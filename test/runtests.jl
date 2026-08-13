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

    @testset "arithmetic" begin
        @test evaluate("1 + 2", CTX) === Int64(3)
        @test evaluate("7 - 10", CTX) === Int64(-3)
        @test evaluate("6 * 7", CTX) === Int64(42)
        @test evaluate("1 + 2 * 3", CTX) === Int64(7)          # precedence
        @test evaluate("(1 + 2) * 3", CTX) === Int64(9)
        @test evaluate("status.battery + bindings.threshold", CTX) == 122
        # integer division truncates toward zero; % keeps the dividend's sign
        @test evaluate("7 / 2", CTX) === Int64(3)
        @test evaluate("-7 / 2", CTX) === Int64(-3)
        @test evaluate("7 % 2", CTX) === Int64(1)
        @test evaluate("-7 % 2", CTX) === Int64(-1)
        @test evaluate("7 % -2", CTX) === Int64(1)
        # uint arithmetic stays uint
        @test evaluate("bindings.big - 18446744073709551615", CTX) === UInt64(0)
        @test evaluate("bindings.big / bindings.big", CTX) === UInt64(1)
        @test evaluate("bindings.big % bindings.big", CTX) === UInt64(0)
        # double arithmetic
        @test evaluate("1.5 + 2.25", CTX) === 3.75
        @test evaluate("1.0 / 4.0", CTX) === 0.25
        @test evaluate("status.temperature * 2.0", CTX) === 73.0
        # doubles follow IEEE 754: division by zero is Inf, not an error
        @test evaluate("1.0 / 0.0", CTX) === Inf
        @test evaluate("-1.0 / 0.0", CTX) === -Inf
        # ...but doubles have no '%' overload
        @test_throws CELEvalError evaluate("1.5 % 2.0", CTX)
        # string and list concatenation
        @test evaluate("'foo' + 'bar'", CTX) == "foobar"
        @test evaluate("labels.zone + '1'", CTX) == "A1"
        @test evaluate("[1, 2] + [3]", CTX) == Any[1, 2, 3]
        @test evaluate("size(bindings.mask[0] + bindings.mask[1])", CTX) == 6
        # integer division/modulo by zero is an error, not a crash
        @test_throws CELEvalError evaluate("1 / 0", CTX)
        @test_throws CELEvalError evaluate("1 % 0", CTX)
        @test_throws CELEvalError evaluate("bindings.big / 0", CTX)
        @test_throws CELEvalError evaluate("bindings.big % 0", CTX)
        # checked arithmetic: Int64/UInt64 overflow is an error
        @test_throws CELEvalError evaluate("9223372036854775807 + 1", CTX)
        @test_throws CELEvalError evaluate("-9223372036854775808 - 1", CTX)
        @test_throws CELEvalError evaluate("9223372036854775807 * 2", CTX)
        @test_throws CELEvalError evaluate("-9223372036854775808 / (0 - 1)", CTX)
        @test_throws CELEvalError evaluate("-9223372036854775808 % (0 - 1)", CTX)
        @test_throws CELEvalError evaluate("bindings.big + bindings.big", CTX)
        @test_throws CELEvalError evaluate(
            "18446744073709551614 - 18446744073709551615", CTX)
        # no implicit numeric promotion (cel-spec), and no bool arithmetic
        @test_throws CELEvalError evaluate("1 + 1.0", CTX)
        @test_throws CELEvalError evaluate("bindings.big + 1", CTX)
        @test_throws CELEvalError evaluate("true + true", CTX)
        @test_throws CELEvalError evaluate("'a' + 1", CTX)
        @test_throws CELEvalError evaluate("[1] + 'a'", CTX)
    end

    @testset "unary minus" begin
        @test evaluate("-(1 + 2)", CTX) === Int64(-3)
        @test evaluate("- -3", CTX) === Int64(3)
        @test evaluate("-status.temperature", CTX) === -36.5
        @test evaluate("-status.battery", CTX) == -72
        @test evaluate("-9223372036854775808", CTX) === typemin(Int64)
        @test_throws CELEvalError evaluate("-(-9223372036854775808)", CTX)
        @test_throws CELEvalError evaluate("-bindings.big", CTX)  # no uint negation
        @test_throws CELEvalError evaluate("-'a'", CTX)
        @test_throws CELEvalError evaluate("-true", CTX)
        # negative magnitudes beyond typemin have no home
        @test_throws CELEvalError evaluate("-18446744073709551615", CTX)
    end

    @testset "in" begin
        @test evaluate_bool("2 in [1, 2, 3]", CTX)
        @test !evaluate_bool("4 in [1, 2, 3]", CTX)
        @test evaluate_bool("2 in [1.0, 2.0]", CTX)      # exact cross-type equality
        @test !evaluate_bool("true in [1]", CTX)         # bool is not numeric
        @test evaluate_bool("'zone' in labels", CTX)     # map: key membership
        @test !evaluate_bool("'nope' in labels", CTX)
        @test evaluate_bool("1 in {1: 'a'}", CTX)
        @test evaluate_bool("1.0 in {1: 'a'}", CTX)
        @test evaluate_bool("[1] in [[1], [2]]", CTX)
        @test !evaluate_bool("2 in []", CTX)
        @test evaluate_bool("1 + 1 in [2]", CTX)         # 'in' binds looser than '+'
        @test_throws CELEvalError evaluate("1 in 5", CTX)
        @test_throws CELEvalError evaluate("'a' in 'abc'", CTX)
        @test_throws CELParseError CEL.compile("in")     # reserved word
    end

    @testset "ternary" begin
        @test evaluate("true ? 1 : 2", CTX) == 1
        @test evaluate("false ? 1 : 2", CTX) == 2
        @test evaluate("status.battery > 50 ? 'ok' : 'low'", CTX) == "ok"
        # lazy: only the taken branch evaluates
        @test evaluate("true ? 1 : nosuchvar", CTX) == 1
        @test evaluate("false ? nosuchvar : 2", CTX) == 2
        # right-associative else branch
        @test evaluate("false ? 1 : true ? 2 : 3", CTX) == 2
        @test evaluate("[10, 20][true ? 0 : 1]", CTX) == 10
        # a non-bool condition is an error
        @test_throws CELEvalError evaluate("1 ? 2 : 3", CTX)
        @test_throws CELEvalError evaluate("nosuchvar ? 2 : 3", CTX)
        @test_throws CELParseError CEL.compile("true ? 1")      # missing ':'
        @test_throws CELParseError CEL.compile("true ? : 1")
    end

    @testset "list and map literals" begin
        @test evaluate("[]", CTX) == Any[]
        @test evaluate("[1, 'a', true][1]", CTX) == "a"
        @test evaluate("[1, 2,]", CTX) == Any[1, 2]              # trailing comma
        @test evaluate("[[1], [2, 3]][1][0]", CTX) == 2
        @test evaluate("size({})", CTX) == 0
        @test evaluate("{'k': 1, 'j': 2}['k']", CTX) == 1
        @test evaluate("{1: 'a', 2: 'b'}[2]", CTX) == "b"
        @test evaluate("{1: 'a'}[1.0]", CTX) == "a"              # exact cross-type key
        @test evaluate("{18446744073709551615: 'x'}[bindings.big]", CTX) == "x"
        @test evaluate("{true: 'y'}[true]", CTX) == "y"
        @test evaluate("{'k': 1,}['k']", CTX) == 1               # trailing comma
        @test evaluate("{'battery': status.battery}['battery']", CTX) == 72
        # keys are string/int/uint/bool only (cel-spec)
        @test_throws CELEvalError evaluate("{1.5: 'x'}", CTX)
        @test_throws CELEvalError evaluate("{null: 'x'}", CTX)
        @test_throws CELEvalError evaluate("{[1]: 'x'}", CTX)
        # duplicate keys (by exact cross-type equality) are an error
        @test_throws CELEvalError evaluate("{1: 'a', 1: 'b'}", CTX)
        @test_throws CELEvalError evaluate("{'missing': nosuchvar}", CTX)
        @test_throws CELEvalError evaluate("{'k': 1}['j']", CTX)
        @test_throws CELParseError CEL.compile("[1 2]")
        @test_throws CELParseError CEL.compile("{1, 2}")
        @test_throws CELParseError CEL.compile("{'k' 1}")
    end

    @testset "size, conversions" begin
        @test evaluate("size('')", CTX) === Int64(0)
        @test evaluate("size('héllo')", CTX) === Int64(5)        # codepoints, not bytes
        @test evaluate("size([1, 2, 3])", CTX) === Int64(3)
        @test evaluate("size(labels)", CTX) === Int64(2)
        @test evaluate_bool("size(bindings.mask) > 0", CTX)
        @test_throws CELEvalError evaluate("size(1)", CTX)
        @test_throws CELEvalError evaluate("size(true)", CTX)
        @test evaluate("string(42)", CTX) == "42"
        @test evaluate("string(-1)", CTX) == "-1"
        @test evaluate("string(bindings.big)", CTX) == "18446744073709551615"
        @test evaluate("string(3.5)", CTX) == "3.5"
        @test evaluate("string(true)", CTX) == "true"
        @test evaluate("string('s')", CTX) == "s"
        @test_throws CELEvalError evaluate("string(null)", CTX)
        @test evaluate("int('42')", CTX) === Int64(42)
        @test evaluate("int(3.9)", CTX) === Int64(3)             # truncation toward zero
        @test evaluate("int(0.0 - 3.9)", CTX) === Int64(-3)
        @test evaluate("int(bindings.big / bindings.big)", CTX) === Int64(1)
        @test_throws CELEvalError evaluate("int(bindings.big)", CTX)   # out of range
        @test_throws CELEvalError evaluate("int(9223372036854775808.0)", CTX)
        @test_throws CELEvalError evaluate("int('abc')", CTX)
        @test_throws CELEvalError evaluate("int(true)", CTX)
        @test evaluate("uint(5)", CTX) === UInt64(5)
        @test evaluate("uint('7')", CTX) === UInt64(7)
        @test evaluate("uint(3.9)", CTX) === UInt64(3)
        @test_throws CELEvalError evaluate("uint(0 - 1)", CTX)
        @test_throws CELEvalError evaluate("uint(18446744073709551616.0)", CTX)
        @test evaluate("double(1)", CTX) === 1.0
        @test evaluate("double('3.5')", CTX) === 3.5
        @test evaluate("double(bindings.big)", CTX) === 1.8446744073709552e19
        @test_throws CELEvalError evaluate("double('x')", CTX)
        # bool(): identity + the cel-spec ten-token string set (conversions).
        @test evaluate("bool(true)", CTX) === true
        for t in ("1", "t", "true", "TRUE", "True")
            @test evaluate("bool('$t')", CTX) === true
        end
        for f in ("0", "f", "false", "FALSE", "False")
            @test evaluate("bool('$f')", CTX) === false
        end
        @test_throws CELEvalError evaluate("bool('TrUe')", CTX)   # mixed case
        @test_throws CELEvalError evaluate("bool('yes')", CTX)
        @test_throws CELEvalError evaluate("bool(1)", CTX)        # only bool/string
        # dyn(): a runtime no-op (identity); accepted so conformant
        # expressions written for a checked environment compile.
        @test evaluate("dyn(5)", CTX) === Int64(5)
        @test evaluate_bool("dyn([1, 2]) == [1, 2]", CTX)
        @test evaluate("dyn('x')", CTX) == "x"
        # arity and unknown functions refuse at compile time
        @test_throws CELParseError CEL.compile("size()")
        @test_throws CELParseError CEL.compile("size(1, 2)")
        @test_throws CELParseError CEL.compile("frobnicate(1)")
        @test_throws CELParseError CEL.compile("type(1)")        # type(): unimplemented
    end

    @testset "has" begin
        @test evaluate_bool("has(identity.device_id)", CTX)
        @test !evaluate_bool("has(identity.nosuchfield)", CTX)   # absent: false, no error
        @test !evaluate_bool("has(labels.missing)", CTX)
        @test evaluate_bool("has(labels.zone) && labels.zone == 'A'", CTX)
        # the base object must still resolve, and must be a map
        @test_throws CELEvalError evaluate("has(nosuchvar.f)", CTX)
        @test_throws CELEvalError evaluate("has(identity.device_id.f)", CTX)
        # has() is a macro: anything but a field selection refuses to compile
        @test_throws CELParseError CEL.compile("has(labels)")
        @test_throws CELParseError CEL.compile("has(1)")
        @test_throws CELParseError CEL.compile("has(labels['zone'])")
        @test_throws CELParseError CEL.compile("has(labels.zone, 1)")
    end

    @testset "matches" begin
        @test evaluate_bool("'hello'.matches('^h.*o\$')", CTX)
        @test evaluate_bool("'hello'.matches('ell')", CTX)       # unanchored
        @test !evaluate_bool("'hello'.matches('^ell')", CTX)
        @test evaluate_bool("matches('hello', 'h[ae]llo')", CTX)
        @test !evaluate_bool("matches('hello', 'world')", CTX)
        @test evaluate_bool("identity.device_type.matches('camera/.+')", CTX)
        @test_throws CELEvalError evaluate("'a'.matches('(')", CTX)   # bad pattern
        @test_throws CELEvalError evaluate("matches(1, 'x')", CTX)
        @test_throws CELEvalError evaluate("'a'.matches(1)", CTX)
        @test_throws CELParseError CEL.compile("matches('a')")   # arity
        # cel-spec pins matches() to the RE2 subset, so a PCRE-only construct
        # is a fail-closed CELEvalError -- NOT a silent match. This matters
        # doubly under the PCRE2-DFA engine, which would otherwise silently
        # MATCH lookaround/atomic/possessive patterns: the compile-time
        # screen must catch them all.
        @test_throws CELEvalError evaluate("'aa'.matches('(a)\\\\1')", CTX)   # backref
        @test_throws CELEvalError evaluate("'ab'.matches('a(?=b)')", CTX)     # lookahead
        @test_throws CELEvalError evaluate("'ab'.matches('a(?!c)')", CTX)     # neg lookahead
        @test_throws CELEvalError evaluate("'ab'.matches('(?<=a)b')", CTX)    # lookbehind
        @test_throws CELEvalError evaluate("'ab'.matches('(?>a)b')", CTX)     # atomic
        @test_throws CELEvalError evaluate("'aa'.matches('a++')", CTX)        # possessive
        @test_throws CELEvalError evaluate("'aa'.matches('a*+')", CTX)
        @test_throws CELEvalError evaluate("'aa'.matches('a{1,2}+')", CTX)
        @test_throws CELEvalError evaluate("'a'.matches('a\\\\Z')", CTX)      # \Z (RE2: only \z)
        @test_throws CELEvalError evaluate("'a'.matches('\\\\1')", CTX)       # lone backref
        @test_throws CELEvalError evaluate("'a'.matches('\\\\8')", CTX)       # bad octal
        @test_throws CELEvalError evaluate("'a'.matches('(?#c)a')", CTX)      # comment
        @test_throws CELEvalError evaluate("'a'.matches('(*FAIL)')", CTX)     # verb
        @test_throws CELEvalError evaluate("'a'.matches('(?(1)a)')", CTX)     # conditional
        @test_throws CELEvalError evaluate("'a'.matches('(?R)')", CTX)        # recursion
        @test_throws CELEvalError evaluate("'a'.matches('\\\\K')", CTX)       # \K
        @test_throws CELEvalError evaluate("'a'.matches('\\\\cA')", CTX)      # control escape
        @test_throws CELEvalError evaluate("'a'.matches('(?x)a b')", CTX)     # x flag
        @test_throws CELEvalError evaluate("'a'.matches('a{1001}')", CTX)     # RE2 repeat cap
        # in-subset RE2 features work
        @test evaluate_bool("'HELLO'.matches('(?i)hello')", CTX)
        @test evaluate_bool("'the grey cat'.matches('gr(a|e)y')", CTX)
        @test evaluate_bool("'ab'.matches('(?P<x>a)b')", CTX)                 # named groups
        @test evaluate_bool("'ab'.matches('(?<x>a)b')", CTX)
        @test evaluate_bool("'x'.matches('\\\\p{L}')", CTX)                   # Unicode property
        @test !evaluate_bool("'1'.matches('\\\\p{L}')", CTX)
        @test evaluate_bool("'q'.matches('[[:alpha:]]')", CTX)                # POSIX class
        @test evaluate_bool("'A'.matches('\\\\x41')", CTX)                    # hex escape
        @test evaluate_bool("'A'.matches('\\\\101')", CTX)                    # octal escape
        @test evaluate_bool("'a+b'.matches('\\\\Qa+b\\\\E')", CTX)            # quoted literal
        # RE2 semantics pins (divergences from PCRE2 defaults, rewritten by
        # the screen and verified against the real C++ RE2 in a fuzz gate):
        @test !evaluate_bool("'a\\n'.matches('a\$')", CTX)     # $ is true end of text
        @test evaluate_bool("'a'.matches('a\$')", CTX)
        @test evaluate_bool("'x\\nab'.matches('(?m)^ab\$')", CTX)
        @test evaluate_bool("'\v'.matches('^\\\\v\$')", CTX)  # \v = VT character
        @test !evaluate_bool("'\v'.matches('^\\\\s\$')", CTX) # RE2 \s has no VT
        @test evaluate_bool("'\v'.matches('^\\\\S\$')", CTX)
        @test evaluate_bool("'\v'.matches('^[\\\\S]\$')", CTX)
        @test !evaluate_bool("'\v'.matches('^[\\\\s]\$')", CTX)
        # a hostile predicate cannot become a denial of service: the
        # non-backtracking DFA bounds what would blow up a backtracker.
        let s = "a"^60 * "c"
            t = @elapsed evaluate_bool("'$s'.matches('(a+)+b')", CTX)
            @test t < 0.5
        end
    end

    @testset "comprehensions" begin
        procs = Dict{String,Any}("procedures" =>
            Any[Dict{String,Any}("name" => "echo", "labels" => Dict{String,Any}())])
        @test evaluate_bool("procedures.exists(p, p.name == \"echo\")", procs)
        @test evaluate_bool("size(procedures) > 0", procs)
        @test !evaluate_bool("procedures.exists(p, p.name == \"nope\")", procs)
        @test evaluate_bool("[1, 2, 3].exists(x, x > 2)", CTX)
        @test !evaluate_bool("[].exists(x, true)", CTX)
        @test evaluate_bool("[1, 2, 3].all(x, x > 0)", CTX)
        @test !evaluate_bool("[1, 2, 3].all(x, x > 1)", CTX)
        @test evaluate_bool("[].all(x, false)", CTX)             # vacuous truth
        @test evaluate_bool("[1, 2, 3].exists_one(x, x == 2)", CTX)
        @test !evaluate_bool("[1, 2, 2].exists_one(x, x == 2)", CTX)
        @test !evaluate_bool("[].exists_one(x, true)", CTX)
        @test evaluate("[1, 2, 3, 4].filter(x, x % 2 == 0)", CTX) == Any[2, 4]
        @test evaluate("[1, 2].map(x, x * 10)", CTX) == Any[10, 20]
        @test evaluate("[].map(x, nosuchvar)", CTX) == Any[]
        # comprehensions over a map iterate its keys
        @test evaluate_bool("labels.exists(k, k == 'zone')", CTX)
        @test evaluate_bool("labels.all(k, size(k) > 3)", CTX)
        @test evaluate("labels.filter(k, k == 'zone')", CTX) == Any["zone"]
        # nesting and shadowing
        @test evaluate_bool("[[1], [2]].exists(x, x.exists(y, y == 2))", CTX)
        @test evaluate("[1].map(x, [10].map(x, x))[0][0]", CTX) == 10
        @test evaluate("[1].map(x, x)[0]", Dict{String,Any}("x" => 99)) == 1
        @test evaluate("[1].map(y, x + y)[0]", Dict{String,Any}("x" => 99)) == 100
        # error absorption (cel-spec): exists absorbs once a true is
        # found, all once a false is found; otherwise the error propagates
        @test evaluate_bool("['a', 1].exists(x, x > 0)", CTX)
        @test !evaluate_bool("['a', 1].all(x, x > 1)", CTX)
        @test_throws CELEvalError evaluate("['a', 1].exists(x, x > 1)", CTX)
        @test_throws CELEvalError evaluate("['a', 2].all(x, x > 1)", CTX)
        # exists_one / filter / map propagate any error
        @test_throws CELEvalError evaluate("['a', 1].exists_one(x, x > 0)", CTX)
        @test_throws CELEvalError evaluate("['a', 1].filter(x, x > 0)", CTX)
        @test_throws CELEvalError evaluate("[1, 'a'].map(x, x * 2)", CTX)
        # a non-bool predicate is an error
        @test_throws CELEvalError evaluate("[1].exists(x, x)", CTX)
        # comprehensions need a list or a map
        @test_throws CELEvalError evaluate("status.battery.exists(x, true)", CTX)
        @test_throws CELEvalError evaluate("'abc'.exists(x, true)", CTX)
        # the loop variable must be a plain identifier
        @test_throws CELParseError CEL.compile("[1].exists(1, true)")
        @test_throws CELParseError CEL.compile("[1].exists(true, true)")
        @test_throws CELParseError CEL.compile("[1].exists(x.y, true)")
        @test_throws CELParseError CEL.compile("[1].exists(x)")
        # timeouts inside comprehensions are never absorbed
        @test_throws CELEvalError evaluate_bool("[1].exists(x, true)", CTX;
                                                timeout=-1.0)
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
        @test_throws CELParseError CEL.compile("1 | 2")            # outside the subset
        @test_throws CELParseError CEL.compile("a ?? b")
        @test_throws CELParseError CEL.compile("labels.zone ==")
        @test_throws CELParseError CEL.compile("1 +")
        @test_throws CELParseError CEL.compile("'unterminated")
        @test_throws CELParseError CEL.compile("s.frobnicate('x')") # unsupported method
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
