# A native-Julia evaluator for a subset of the Common Expression Language
# (CEL, https://cel.dev / github.com/cel-expr/cel-spec).
#
# Scope: the practical predicate subset -- literals, identifiers, field
# selection, indexing, the string methods startsWith/endsWith/contains,
# `!`, comparisons, and CEL's `&&`/`||` (which are COMMUTATIVE OVER
# ERRORS, not merely short-circuiting). Everything outside the subset fails to
# COMPILE with `CELParseError` -- never silently misparses -- so callers
# can route unsupported expressions to a fail-closed policy.
#
# The architecture mirrors the cel-spec pipeline so the rest of the
# language can land incrementally: lexer -> AST -> tree-walking evaluator
# over a variable environment. The obvious extension points:
#   * new binary operators: one entry in the parser's precedence ladder
#     plus an `_eval_bin` branch (`+ - * / %`, `in`, `? :`);
#   * list/map literals: two `parse_primary` productions;
#   * functions and macros (`size`, `has`, `matches`, comprehensions):
#     dispatch alongside the string-method call route in
#     `parse_postfix` / `evaluate_node`;
#   * a type checker: a separate pass over the same `Node` tree.
#
# Semantics follow cel-spec where the subset touches it:
#   * numeric equality/ordering is EXACT across Int64/UInt64/Float64 --
#     Julia's cross-type numeric comparisons are mathematically exact, so
#     distinct 64-bit integers never alias through a double;
#   * bool is NOT numeric (`true != 1`);
#   * a missing variable, member, or key is an evaluation ERROR (CEL's
#     absent-field semantics), not `null`;
#   * `&&`/`||` absorb an errored arm when the other arm alone decides
#     the result (false decides `&&`, true decides `||`); otherwise the
#     error propagates;
#   * evaluation is wall-clock bounded (`timeout`); a timeout is never
#     absorbed by `&&`/`||`;
#   * a non-boolean result from `evaluate_bool` is an error, never a
#     truthiness coercion.
module CommonExpressionLanguage

export compile, evaluate, evaluate_bool, CELParseError, CELEvalError

"An expression failed to compile: empty, over the length or depth caps, or outside the implemented grammar."
struct CELParseError <: Exception
    msg::String
end
Base.showerror(io::IO, e::CELParseError) = print(io, "CELParseError: ", e.msg)

"A compiled expression failed at evaluation: missing variable/member/key, type mismatch, non-boolean where a boolean is required, or the wall-clock bound exceeded."
struct CELEvalError <: Exception
    msg::String
end
Base.showerror(io::IO, e::CELEvalError) = print(io, "CELEvalError: ", e.msg)

const MAX_EXPR_LENGTH = 2048   # compile refuses longer sources
const MAX_PARSE_DEPTH = 64     # nesting cap (stack-overflow guard)

# ---------------------------------------------------------------------------
# Lexer.

@enum TokKind TID TNUM TSTR TOP TEOF

struct Token
    kind::TokKind
    text::String
    value::Any     # TNUM: Int64/UInt64/Float64; TSTR: the decoded string
end

_ident_start(c::Char) = 'A' <= c <= 'Z' || 'a' <= c <= 'z' || c == '_'
_ident_char(c::Char) = _ident_start(c) || '0' <= c <= '9'

function tokenize(src::AbstractString)
    out = Token[]
    cs = collect(src)   # Char vector: simple index arithmetic
    i, n = 1, length(cs)
    while i <= n
        c = cs[i]
        if c in (' ', '\t', '\n', '\r')
            i += 1
        elseif _ident_start(c)
            j = i
            while j <= n && _ident_char(cs[j])
                j += 1
            end
            push!(out, Token(TID, String(cs[i:j-1]), nothing))
            i = j
        elseif isdigit(c) || (c == '-' && i < n && isdigit(cs[i+1]))
            j = i + (c == '-' ? 1 : 0)
            isfloat = false
            while j <= n && isdigit(cs[j])
                j += 1
            end
            if j < n && cs[j] == '.' && isdigit(cs[j+1])
                isfloat = true
                j += 1
                while j <= n && isdigit(cs[j])
                    j += 1
                end
            end
            text = String(cs[i:j-1])
            value = if isfloat
                parse(Float64, text)
            else
                # Negative literals parse as Int64; non-negative at full
                # u64 width (context values carry u64 serials/hashes, and
                # cel-spec integers are exact). Over-range refuses at
                # compile time, never silently clamps.
                v = tryparse(Int64, text)
                if v === nothing
                    u = c == '-' ? nothing : tryparse(UInt64, text)
                    u === nothing &&
                        throw(CELParseError("integer literal out of range"))
                    u
                else
                    v
                end
            end
            push!(out, Token(TNUM, text, value))
            i = j
        elseif c == '"' || c == '\''
            quote_c = c
            buf = IOBuffer()
            j = i + 1
            closed = false
            while j <= n
                d = cs[j]
                if d == '\\' && j < n
                    e = cs[j+1]
                    e == 'n' ? write(buf, '\n') :
                    e == 't' ? write(buf, '\t') :
                    e == 'r' ? write(buf, '\r') :
                    e in ('\\', '\'', '"') ? write(buf, e) :
                        throw(CELParseError("unsupported escape in string literal"))
                    j += 2
                elseif d == quote_c
                    closed = true
                    j += 1
                    break
                else
                    write(buf, d)
                    j += 1
                end
            end
            closed || throw(CELParseError("unterminated string literal"))
            s = String(take!(buf))
            push!(out, Token(TSTR, s, s))
            i = j
        else
            two = i < n ? String(cs[i:i+1]) : ""
            if two in ("&&", "||", "==", "!=", "<=", ">=")
                push!(out, Token(TOP, two, nothing))
                i += 2
            elseif c in ('(', ')', '[', ']', '.', '!', '<', '>', ',')
                push!(out, Token(TOP, string(c), nothing))
                i += 1
            else
                throw(CELParseError("unexpected character '$(c)' in expression"))
            end
        end
    end
    push!(out, Token(TEOF, "", nothing))
    return out
end

# ---------------------------------------------------------------------------
# AST + parser. Recursive descent over the grammar (loosest first):
#
#   or       := and ( '||' and )*
#   and      := rel ( '&&' rel )*
#   rel      := unary ( ('=='|'!='|'<'|'<='|'>'|'>=') unary )?
#   unary    := '!' unary | postfix
#   postfix  := primary ( '.' ident | '.' method '(' or ')' | '[' or ']' )*
#   primary  := literal | ident | '(' or ')'
#   literal  := string | number | 'true' | 'false' | 'null'
#   method   := 'startsWith' | 'endsWith' | 'contains'

abstract type Node end
struct Lit <: Node
    value::Any
end
struct Ident <: Node
    name::String
end
struct Member <: Node
    object::Node
    name::String
end
struct Index <: Node
    object::Node
    index::Node
end
struct MethodCall <: Node
    object::Node
    name::String
    arg::Node
end
struct Not <: Node
    operand::Node
end
struct Bin <: Node
    op::String
    a::Node
    b::Node
end

const STRING_METHODS = ("startsWith", "endsWith", "contains")

mutable struct Parser
    toks::Vector{Token}
    pos::Int
    depth::Int
end
_peek(p::Parser) = p.toks[p.pos]
_next!(p::Parser) = (t = p.toks[p.pos]; p.pos += 1; t)
_isop(t::Token, s::String) = t.kind == TOP && t.text == s
function _expect_op!(p::Parser, s::String)
    t = _next!(p)
    _isop(t, s) || throw(CELParseError("expected '$(s)', got '$(t.text)'"))
    return t
end
function _descend(f, p::Parser)
    p.depth += 1
    p.depth > MAX_PARSE_DEPTH &&
        throw(CELParseError("expression nests deeper than $(MAX_PARSE_DEPTH)"))
    try
        return f()
    finally
        p.depth -= 1
    end
end

parse_or(p::Parser) = _descend(p) do
    node = parse_and(p)
    while _isop(_peek(p), "||")
        _next!(p)
        node = Bin("||", node, parse_and(p))
    end
    node
end

parse_and(p::Parser) = _descend(p) do
    node = parse_rel(p)
    while _isop(_peek(p), "&&")
        _next!(p)
        node = Bin("&&", node, parse_rel(p))
    end
    node
end

parse_rel(p::Parser) = _descend(p) do
    node = parse_unary(p)
    t = _peek(p)
    if t.kind == TOP && t.text in ("==", "!=", "<", "<=", ">", ">=")
        _next!(p)
        node = Bin(t.text, node, parse_unary(p))
    end
    node
end

parse_unary(p::Parser) = _descend(p) do
    if _isop(_peek(p), "!")
        _next!(p)
        return Not(parse_unary(p))
    end
    parse_postfix(p)
end

parse_postfix(p::Parser) = _descend(p) do
    node = parse_primary(p)
    while true
        t = _peek(p)
        if _isop(t, ".")
            _next!(p)
            id = _next!(p)
            id.kind == TID ||
                throw(CELParseError("expected an identifier after '.'"))
            if _isop(_peek(p), "(")
                id.text in STRING_METHODS ||
                    throw(CELParseError("unsupported method '$(id.text)'"))
                _next!(p)
                arg = parse_or(p)
                _expect_op!(p, ")")
                node = MethodCall(node, id.text, arg)
            else
                node = Member(node, id.text)
            end
        elseif _isop(t, "[")
            _next!(p)
            idx = parse_or(p)
            _expect_op!(p, "]")
            node = Index(node, idx)
        else
            return node
        end
    end
end

parse_primary(p::Parser) = _descend(p) do
    t = _next!(p)
    if t.kind == TNUM || t.kind == TSTR
        return Lit(t.value)
    elseif t.kind == TID
        t.text == "true" && return Lit(true)
        t.text == "false" && return Lit(false)
        t.text == "null" && return Lit(nothing)
        return Ident(t.text)
    elseif _isop(t, "(")
        node = parse_or(p)
        _expect_op!(p, ")")
        return node
    end
    throw(CELParseError("unexpected token '$(t.text)'"))
end

"""
    compile(source) -> Node

Parse a CEL expression to its AST. Throws [`CELParseError`](@ref) on
empty input, sources over $(MAX_EXPR_LENGTH) bytes, nesting deeper than
$(MAX_PARSE_DEPTH) levels, or anything outside the implemented grammar.
"""
function compile(source::AbstractString)
    isempty(strip(source)) && throw(CELParseError("empty expression"))
    sizeof(source) > MAX_EXPR_LENGTH &&
        throw(CELParseError("expression exceeds the $(MAX_EXPR_LENGTH)-byte cap"))
    p = Parser(tokenize(source), 1, 0)
    ast = parse_or(p)
    _peek(p).kind == TEOF ||
        throw(CELParseError("trailing input after expression"))
    return ast
end

# ---------------------------------------------------------------------------
# Evaluator.

struct EvalCtx
    vars::AbstractDict
    deadline::Float64
end

# Bool is not numeric in CEL (Julia's Bool <: Number would otherwise make
# `true == 1` hold).
_isnum(v) = v isa Number && !(v isa Bool)

function _check_deadline(ctx::EvalCtx)
    time() > ctx.deadline &&
        throw(CELEvalError("evaluation exceeded the wall-clock bound"))
end

_eval_bool(n::Node, ctx::EvalCtx) = begin
    v = evaluate_node(n, ctx)
    v isa Bool || throw(CELEvalError("sub-expression evaluated to a non-boolean"))
    v
end

# CEL equality: exact cross-type numeric comparison; bool excluded from
# the numeric universe; everything else by natural equality.
function _cel_eq(a, b)
    _isnum(a) && _isnum(b) && return a == b
    (a isa Bool) != (b isa Bool) && return false
    return a == b
end

function evaluate_node(n::Node, ctx::EvalCtx)
    _check_deadline(ctx)
    if n isa Lit
        return n.value
    elseif n isa Ident
        haskey(ctx.vars, n.name) ||
            throw(CELEvalError("unknown variable '$(n.name)'"))
        return ctx.vars[n.name]
    elseif n isa Member
        obj = evaluate_node(n.object, ctx)
        (obj isa AbstractDict && haskey(obj, n.name)) ||
            throw(CELEvalError("missing member '$(n.name)'"))
        return obj[n.name]
    elseif n isa Index
        obj = evaluate_node(n.object, ctx)
        idx = evaluate_node(n.index, ctx)
        if obj isa AbstractDict && idx isa AbstractString
            haskey(obj, idx) || throw(CELEvalError("missing key '$(idx)'"))
            return obj[idx]
        elseif obj isa AbstractVector && _isnum(idx)
            (idx isa Integer || isinteger(idx)) ||
                throw(CELEvalError("index out of range"))
            i = Int(idx)
            0 <= i < length(obj) || throw(CELEvalError("index out of range"))
            return obj[i+1]                # CEL indexes from 0
        end
        throw(CELEvalError("invalid index operation"))
    elseif n isa MethodCall
        obj = evaluate_node(n.object, ctx)
        arg = evaluate_node(n.arg, ctx)
        (obj isa AbstractString && arg isa AbstractString) ||
            throw(CELEvalError("string method on a non-string value"))
        n.name == "startsWith" && return startswith(obj, arg)
        n.name == "endsWith" && return endswith(obj, arg)
        return occursin(arg, obj)          # contains
    elseif n isa Not
        return !_eval_bool(n.operand, ctx)
    elseif n isa Bin
        return _eval_bin(n, ctx)
    end
    throw(CELEvalError("unreachable node kind"))
end

function _eval_bin(n::Bin, ctx::EvalCtx)
    # `&&` / `||`: commutative over errors -- an errored arm is absorbed
    # whenever the other arm alone decides the result (false decides `&&`,
    # true decides `||`). Plain short-circuiting would let operand ORDER
    # decide the verdict on expressions like
    # `labels.optional == "x" || labels.zone == "A"` when the left member
    # is missing. A timeout is never absorbed: the deadline is re-checked
    # before absorbing.
    if n.op == "&&" || n.op == "||"
        decides = n.op == "||"
        a_err, a_val = false, false
        try
            a_val = _eval_bool(n.a, ctx)
        catch e
            e isa CELEvalError || rethrow()
            _check_deadline(ctx)
            a_err = true
        end
        !a_err && a_val == decides && return decides
        b_val = _eval_bool(n.b, ctx)
        b_val == decides && return decides
        a_err && throw(CELEvalError(
            "'$(n.op)' arm errored and the other arm does not decide"))
        return !decides
    end
    l = evaluate_node(n.a, ctx)
    r = evaluate_node(n.b, ctx)
    n.op == "==" && return _cel_eq(l, r)
    n.op == "!=" && return !_cel_eq(l, r)
    # Ordering: numbers with numbers (exact across integer/float types),
    # strings with strings; anything else refuses.
    if _isnum(l) && _isnum(r)
        n.op == "<" && return l < r
        n.op == "<=" && return l <= r
        n.op == ">" && return l > r
        return l >= r
    elseif l isa AbstractString && r isa AbstractString
        c = cmp(l, r)
        n.op == "<" && return c < 0
        n.op == "<=" && return c <= 0
        n.op == ">" && return c > 0
        return c >= 0
    end
    throw(CELEvalError("ordering comparison on mixed types"))
end

"""
    evaluate(compiled_or_source, vars::AbstractDict; timeout=Inf)

Evaluate a compiled expression (or compile a source string first)
against the variable environment `vars`. Returns the resulting value.
Throws [`CELEvalError`](@ref) on missing variables/members/keys, type
mismatches, or exceeding `timeout` (seconds, wall clock);
[`CELParseError`](@ref) when given an uncompilable source string.
"""
evaluate(source::AbstractString, vars::AbstractDict; timeout::Real=Inf) =
    evaluate(compile(source), vars; timeout)
evaluate(ast::Node, vars::AbstractDict; timeout::Real=Inf) =
    evaluate_node(ast, EvalCtx(vars, time() + Float64(timeout)))

"""
    evaluate_bool(compiled_or_source, vars; timeout=Inf) -> Bool

[`evaluate`](@ref), additionally requiring a boolean result -- a
non-boolean throws [`CELEvalError`](@ref) rather than being
truthiness-coerced (an accidental "fire whenever nonzero" is exactly
what predicate callers must not get).
"""
function evaluate_bool(x, vars::AbstractDict; timeout::Real=Inf)
    v = evaluate(x, vars; timeout)
    v isa Bool || throw(CELEvalError("expression evaluated to a non-boolean"))
    return v
end

end # module
