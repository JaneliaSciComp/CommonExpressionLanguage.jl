using Test
using CommonExpressionLanguage
const CEL = CommonExpressionLanguage

const CTX = Dict{String,Any}(
    "identity" => Dict{String,Any}("device_id" => "cam-01",
                                   "device_type" => "camera/thermal",
                                   "seat_row" => 1, "seat_col" => 2),
    "labels" => Dict{String,Any}("zone" => "A", "category" => "camera"),
    "status" => Dict{String,Any}("battery" => 72, "temperature" => 36.5,
                                 "online" => true),
    "bindings" => Dict{String,Any}(
        "threshold" => 50,
        "mask" => Any[Any[0, 0, 1], Any[0, 1, 0]],
        "big" => UInt64(18446744073709551615)))

@testset "CommonExpressionLanguage" begin
    @testset "literals" begin
        @test evaluate("true", CTX) === true
        @test evaluate("false", CTX) === false
        @test evaluate("null", CTX) === nothing
        @test evaluate("42", CTX) === Int64(42)
        @test evaluate("-7", CTX) === Int64(-7)
        @test evaluate("3.5", CTX) === 3.5
        @test evaluate("\"hi\"", CTX) == "hi"
        @test evaluate("'hi'", CTX) == "hi"
        @test evaluate("'a\\nb'", CTX) == "a\nb"
        @test evaluate("18446744073709551615", CTX) == UInt64(18446744073709551615)
    end

    @testset "member, index, methods" begin
        @test evaluate("identity.device_id", CTX) == "cam-01"
        @test evaluate("labels[\"zone\"]", CTX) == "A"
        @test evaluate("bindings.mask[identity.seat_row][identity.seat_col]", CTX) == 0
        @test evaluate("bindings.mask[0][2]", CTX) == 1
        @test evaluate_bool("identity.device_type.startsWith(\"camera\")", CTX)
        @test evaluate_bool("identity.device_type.endsWith(\"thermal\")", CTX)
        @test evaluate_bool("identity.device_type.contains(\"/\")", CTX)
        @test !evaluate_bool("labels.zone.contains(\"b\")", CTX)
    end

    @testset "comparisons and connectives" begin
        @test evaluate_bool("status.battery > 50", CTX)
        @test evaluate_bool("bindings.threshold < status.battery", CTX)
        @test evaluate_bool("labels.category == \"camera\" && status.battery > 50", CTX)
        @test evaluate_bool("labels.zone == \"B\" || status.online", CTX)
        @test !evaluate_bool("!status.online || labels.zone == \"B\"", CTX)
        # exact numeric equality across types
        @test evaluate_bool("status.battery == 72.0", CTX)
        @test evaluate_bool("bindings.big == 18446744073709551615", CTX)
        @test !evaluate_bool("bindings.big == 18446744073709551614", CTX)
        # string ordering
        @test evaluate_bool("labels.zone < \"B\"", CTX)
        # bool is not numeric
        @test !evaluate_bool("status.online == 1", CTX)
    end

    @testset "error absorption in && / ||" begin
        # A missing member errors, but the other arm decides.
        @test evaluate_bool("labels.missing == \"x\" || labels.zone == \"A\"", CTX)
        @test !evaluate_bool("labels.missing == \"x\" && labels.zone == \"B\"", CTX)
        # ...and when the other arm does NOT decide, the error propagates.
        @test_throws CELEvalError evaluate_bool(
            "labels.missing == \"x\" || labels.zone == \"B\"", CTX)
        @test_throws CELEvalError evaluate_bool(
            "labels.zone == \"A\" && labels.missing == \"x\"", CTX)
        # error && true: true does not decide '&&', so the error propagates.
        @test_throws CELEvalError evaluate_bool(
            "labels.missing == \"x\" && labels.zone == \"A\"", CTX)
    end

    @testset "fail-closed errors" begin
        @test_throws CELEvalError evaluate("nosuchvar", CTX)
        @test_throws CELEvalError evaluate("identity.nosuchfield", CTX)
        @test_throws CELEvalError evaluate("bindings.mask[9]", CTX)
        @test_throws CELEvalError evaluate("labels.zone[0]", CTX)
        @test_throws CELEvalError evaluate("status.battery.startsWith(\"7\")", CTX)
        @test_throws CELEvalError evaluate_bool("status.battery", CTX)  # non-boolean
        @test_throws CELEvalError evaluate_bool("labels.zone < 5", CTX) # mixed ordering
        @test_throws CELEvalError evaluate_bool("!status.battery", CTX)
    end

    @testset "compile errors" begin
        @test_throws CELParseError CEL.compile("")
        @test_throws CELParseError CEL.compile("1 + 1")            # arithmetic: unsupported
        @test_throws CELParseError CEL.compile("a ?? b")
        @test_throws CELParseError CEL.compile("labels.zone ==")
        @test_throws CELParseError CEL.compile("'unterminated")
        @test_throws CELParseError CEL.compile("s.matches('x')")   # unsupported method
        @test_throws CELParseError CEL.compile("99999999999999999999999999")
        @test_throws CELParseError CEL.compile("(" ^ 100 * "true" * ")" ^ 100)
        @test_throws CELParseError CEL.compile("true false")       # trailing input
        @test_throws CELParseError CEL.compile("a" ^ 3000)         # length cap
    end

    @testset "timeout" begin
        # A generous bound passes...
        @test evaluate_bool("status.battery > 50", CTX; timeout=5.0)
        # ...an already-expired bound fails closed as CELEvalError.
        @test_throws CELEvalError evaluate_bool("status.battery > 50", CTX;
                                                timeout=-1.0)
    end

    @testset "compile-once reuse" begin
        prog = CEL.compile("labels.zone == \"A\"")
        @test evaluate_bool(prog, CTX)
        @test !evaluate_bool(prog,
            Dict{String,Any}("labels" => Dict{String,Any}("zone" => "B")))
    end
end
