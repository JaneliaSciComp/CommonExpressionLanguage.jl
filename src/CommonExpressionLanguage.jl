# A native-Julia evaluator for a subset of the Common Expression Language
# (CEL, https://cel.dev / github.com/cel-expr/cel-spec).
#
# Scope: the practical predicate subset -- literals (including list and
# map literals), identifiers, field selection, indexing, arithmetic
# (`+ - * / %` and unary `-`), comparisons, `in`, the ternary
# `cond ? a : b`, CEL's `&&`/`||` (which are COMMUTATIVE OVER ERRORS,
# not merely short-circuiting), the string methods
# startsWith/endsWith/contains/matches, the global functions
# size/has/string/int/uint/double/bool/dyn/matches, and the comprehension
# exists/all/exists_one/filter/map. Everything outside the subset fails
# to COMPILE with `CELParseError` -- never silently misparses -- so
# callers can route unsupported expressions to a fail-closed policy.
#
# The architecture mirrors the cel-spec pipeline so the rest of the
# language can land incrementally: lexer -> AST -> tree-walking evaluator
# over a variable environment. Remaining extension points:
#   * bytes/timestamp/duration values and their functions;
#   * `type(x)` and type values (deliberately skipped: honest type
#     values need type literals like `int` as identifiers, and a string
#     stand-in would make `type(x) == "int"` hold where cel-spec says it
#     must not);
#   * a type checker: a separate pass over the same `Node` tree.
#
# Semantics follow cel-spec where the subset touches it:
#   * numeric equality/ordering is EXACT across Int64/UInt64/Float64 --
#     Julia's cross-type numeric comparisons are mathematically exact, so
#     distinct 64-bit integers never alias through a double;
#   * bool is NOT numeric (`true != 1`);
#   * arithmetic is CHECKED: Int64/UInt64 overflow, integer division or
#     modulo by zero, and INT64_MIN / -1 (or % -1) are evaluation
#     ERRORS, never wraparound or a Julia crash; integer division
#     truncates toward zero and `%` keeps the dividend's sign; doubles
#     follow IEEE 754 (`x / 0.0` is +/-Inf, per cel-spec never a
#     division error) and have NO `%` overload; operands must share a
#     numeric type (int/uint/double) -- cel-spec has no implicit
#     numeric promotion (`1 + 1u` errors) even though EQUALITY is exact
#     across types;
#   * `+` also concatenates strings and lists;
#   * map literal keys must be string/int/uint/bool (cel-spec); a
#     duplicate key (by the same exact cross-type equality as `==`) is
#     an evaluation error; map indexing and `in` use that equality too;
#   * a missing variable, member, or key is an evaluation ERROR (CEL's
#     absent-field semantics), not `null`; `has(e.f)` is the presence
#     test, and is a macro -- its argument must be a field selection AT
#     COMPILE TIME;
#   * `matches` runs on libpcre2's non-backtracking DFA matcher (the
#     PCRE2_jll stdlib that ships inside every Julia): cel-spec pins
#     matches() to RE2 syntax and to a polynomial cost bound (part of
#     CEL's terminating guarantee). A compile-time screen enforces the
#     RE2 subset -- an out-of-subset pattern (backreference, lookaround,
#     ...) is a fail-closed CELEvalError exactly as under RE2 -- and the
#     DFA algorithm cannot catastrophically backtrack;
module CommonExpressionLanguage

using PCRE2_jll: libpcre2_8

export compile, evaluate, evaluate_bool, CELParseError, CELEvalError

"An expression failed to compile: empty, over the length or depth caps, or outside the implemented grammar."
struct CELParseError <: Exception
    msg::String
end
Base.showerror(io::IO, e::CELParseError) = print(io, "CELParseError: ", e.msg)

"A compiled expression failed at evaluation: missing variable/member/key, type mismatch, checked-arithmetic overflow, non-boolean where a boolean is required, or the wall-clock bound exceeded."
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
        elseif isdigit(c)
            # Numbers lex non-negatively; `-` is always an operator token
            # and unary minus folds literals in the parser (cel-spec has
            # no negative literals either, so `a-1` is a subtraction).
            j = i
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
                # Literals parse as Int64, falling back to full u64 width
                # (context values carry u64 serials/hashes, and cel-spec
                # integers are exact). Over-range refuses at compile
                # time, never silently clamps.
                v = tryparse(Int64, text)
                if v === nothing
                    u = tryparse(UInt64, text)
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
            elseif c in ('(', ')', '[', ']', '{', '}', '.', ',', '!',
                         '<', '>', '+', '-', '*', '/', '%', '?', ':')
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
# AST + parser. Recursive descent over the grammar (loosest first),
# mirroring cel-spec's precedence ladder:
#
#   expr     := or ( '?' or ':' expr )?
#   or       := and ( '||' and )*
#   and      := rel ( '&&' rel )*
#   rel      := add ( ('=='|'!='|'<'|'<='|'>'|'>='|'in') add )?
#   add      := mul ( ('+'|'-') mul )*
#   mul      := unary ( ('*'|'/'|'%') unary )*
#   unary    := ('!'|'-') unary | postfix
#   postfix  := primary ( '.' ident | '.' method '(' expr ')'
#                       | '.' macro '(' ident ',' expr ')'
#                       | '[' expr ']' )*
#   primary  := literal | ident | func '(' expr (',' expr)* ')'
#             | '(' expr ')' | '[' exprlist? ']' | '{' entrylist? '}'
#   literal  := string | number | 'true' | 'false' | 'null'
#   method   := 'startsWith' | 'endsWith' | 'contains' | 'matches'
#   macro    := 'exists' | 'all' | 'exists_one' | 'filter' | 'map'
#   func     := 'size' | 'has' | 'string' | 'int' | 'uint' | 'double'
#             | 'matches'

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
struct Neg <: Node
    operand::Node
end
struct Bin <: Node
    op::String
    a::Node
    b::Node
end
struct Cond <: Node
    cond::Node
    then::Node
    els::Node
end
struct ListLit <: Node
    items::Vector{Node}
end
struct MapLit <: Node
    entries::Vector{Tuple{Node,Node}}
end
struct Call <: Node        # global function
    name::String
    args::Vector{Node}
end
struct Has <: Node         # has(e.f) -- the macro's compiled form
    object::Node
    field::String
end
struct Compr <: Node       # e.kind(var, body) comprehension macros
    object::Node
    kind::String
    var::String
    body::Node
end

const STRING_METHODS = ("startsWith", "endsWith", "contains", "matches")
const MACRO_METHODS = ("exists", "all", "exists_one", "filter", "map")
const GLOBAL_FUNCTIONS = ("size", "has", "string", "int", "uint", "double",
                          "bool", "dyn", "matches")
const KEYWORDS = ("true", "false", "null", "in")

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

# cel-spec: Expr := ConditionalOr ['?' ConditionalOr ':' Expr] -- the
# else branch recurses, so `a ? b : c ? d : e` groups to the right.
parse_expr(p::Parser) = _descend(p) do
    node = parse_or(p)
    if _isop(_peek(p), "?")
        _next!(p)
        then_ = parse_or(p)
        _expect_op!(p, ":")
        node = Cond(node, then_, parse_expr(p))
    end
    node
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
    node = parse_add(p)
    t = _peek(p)
    if t.kind == TOP && t.text in ("==", "!=", "<", "<=", ">", ">=")
        _next!(p)
        node = Bin(t.text, node, parse_add(p))
    elseif t.kind == TID && t.text == "in"
        _next!(p)
        node = Bin("in", node, parse_add(p))
    end
    node
end

parse_add(p::Parser) = _descend(p) do
    node = parse_mul(p)
    while _peek(p).kind == TOP && _peek(p).text in ("+", "-")
        op = _next!(p).text
        node = Bin(op, node, parse_mul(p))
    end
    node
end

parse_mul(p::Parser) = _descend(p) do
    node = parse_unary(p)
    while _peek(p).kind == TOP && _peek(p).text in ("*", "/", "%")
        op = _next!(p).text
        node = Bin(op, node, parse_unary(p))
    end
    node
end

parse_unary(p::Parser) = _descend(p) do
    if _isop(_peek(p), "!")
        _next!(p)
        return Not(parse_unary(p))
    elseif _isop(_peek(p), "-")
        _next!(p)
        operand = parse_unary(p)
        # Fold negated numeric literals so `-7` stays an exact Int64 and
        # `-9223372036854775808` (whose magnitude only lexes at u64
        # width) reaches typemin(Int64), as cel-spec's parser requires.
        # Anything unfoldable becomes a runtime Neg (checked there).
        if operand isa Lit
            v = operand.value
            v isa Float64 && return Lit(-v)
            v isa Int64 && v != typemin(Int64) && return Lit(-v)
            v isa UInt64 && v == UInt64(1) << 63 && return Lit(typemin(Int64))
        end
        return Neg(operand)
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
                _next!(p)
                if id.text in STRING_METHODS
                    arg = parse_expr(p)
                    _expect_op!(p, ")")
                    node = MethodCall(node, id.text, arg)
                elseif id.text in MACRO_METHODS
                    v = _next!(p)
                    (v.kind == TID && !(v.text in KEYWORDS)) ||
                        throw(CELParseError("comprehension variable must be an identifier"))
                    _expect_op!(p, ",")
                    body = parse_expr(p)
                    _expect_op!(p, ")")
                    node = Compr(node, id.text, v.text, body)
                else
                    throw(CELParseError("unsupported method '$(id.text)'"))
                end
            else
                node = Member(node, id.text)
            end
        elseif _isop(t, "[")
            _next!(p)
            idx = parse_expr(p)
            _expect_op!(p, "]")
            node = Index(node, idx)
        else
            return node
        end
    end
end

function _parse_args!(p::Parser)   # '(' already consumed
    args = Node[]
    if !_isop(_peek(p), ")")
        push!(args, parse_expr(p))
        while _isop(_peek(p), ",")
            _next!(p)
            push!(args, parse_expr(p))
        end
    end
    _expect_op!(p, ")")
    return args
end

parse_primary(p::Parser) = _descend(p) do
    t = _next!(p)
    if t.kind == TNUM || t.kind == TSTR
        return Lit(t.value)
    elseif t.kind == TID
        t.text == "true" && return Lit(true)
        t.text == "false" && return Lit(false)
        t.text == "null" && return Lit(nothing)
        t.text == "in" &&
            throw(CELParseError("'in' is an operator, not an identifier"))
        if _isop(_peek(p), "(")
            _next!(p)
            t.text in GLOBAL_FUNCTIONS ||
                throw(CELParseError("unsupported function '$(t.text)'"))
            args = _parse_args!(p)
            if t.text == "has"
                # has() is a macro: its argument must BE a field
                # selection, checked at compile time (cel-spec).
                (length(args) == 1 && args[1] isa Member) ||
                    throw(CELParseError("has() requires a single field-selection argument"))
                return Has(args[1].object, args[1].name)
            end
            nargs = t.text == "matches" ? 2 : 1
            length(args) == nargs ||
                throw(CELParseError("$(t.text)() takes exactly $(nargs) argument$(nargs == 1 ? "" : "s")"))
            return Call(t.text, args)
        end
        return Ident(t.text)
    elseif _isop(t, "(")
        node = parse_expr(p)
        _expect_op!(p, ")")
        return node
    elseif _isop(t, "[")
        items = Node[]
        while !_isop(_peek(p), "]")
            push!(items, parse_expr(p))
            _isop(_peek(p), ",") || break
            _next!(p)   # cel-spec allows a trailing comma before ']'
        end
        _expect_op!(p, "]")
        return ListLit(items)
    elseif _isop(t, "{")
        entries = Tuple{Node,Node}[]
        while !_isop(_peek(p), "}")
            k = parse_expr(p)
            _expect_op!(p, ":")
            push!(entries, (k, parse_expr(p)))
            _isop(_peek(p), ",") || break
            _next!(p)   # cel-spec allows a trailing comma before '}'
        end
        _expect_op!(p, "}")
        return MapLit(entries)
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
    ast = parse_expr(p)
    _peek(p).kind == TEOF ||
        throw(CELParseError("trailing input after expression"))
    return ast
end

# ---------------------------------------------------------------------------
# Evaluator.

# A comprehension extends the environment with its loop variable.
# Chained scopes give natural shadowing for nested comprehensions; only
# haskey/getindex drive evaluation (iterate exists for display and may
# revisit a shadowed parent key).
struct VarScope <: AbstractDict{String,Any}
    name::String
    value::Any
    parent::AbstractDict
end
Base.haskey(s::VarScope, k) = k == s.name || haskey(s.parent, k)
Base.getindex(s::VarScope, k) = k == s.name ? s.value : s.parent[k]
Base.length(s::VarScope) = 1 + length(s.parent)
function Base.iterate(s::VarScope, state=(true, nothing))
    own, pstate = state
    own && return (s.name => s.value), (false, nothing)
    it = pstate === nothing ? iterate(s.parent) : iterate(s.parent, pstate)
    it === nothing && return nothing
    return it[1], (false, it[2])
end

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

# Map keys are string/int/uint/bool per cel-spec (never double or bool
# aliasing a number: bool keys compare only with bools via _cel_eq).
_valid_map_key(k) = k isa AbstractString || k isa Integer   # Bool <: Integer

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
        if obj isa AbstractDict
            if idx isa AbstractString || idx isa Bool
                haskey(obj, idx) || throw(CELEvalError("missing key '$(idx)'"))
                return obj[idx]
            elseif _isnum(idx)
                # Exact cross-type numeric key equality, same as `==`
                # (modern cel-spec: `{1: 'a'}[1u]` succeeds).
                for (k, v) in obj
                    _cel_eq(k, idx) && return v
                end
                throw(CELEvalError("missing key '$(idx)'"))
            end
            throw(CELEvalError("invalid map key type"))
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
        n.name == "matches" && return _cel_matches(obj, arg)
        return occursin(arg, obj)          # contains
    elseif n isa Not
        return !_eval_bool(n.operand, ctx)
    elseif n isa Neg
        v = evaluate_node(n.operand, ctx)
        if v isa Signed                    # Bool is neither Signed nor Unsigned
            (v isa Int64 && v == typemin(Int64)) &&
                throw(CELEvalError("integer overflow in unary '-'"))
            return -Int64(v)
        elseif v isa AbstractFloat
            return -Float64(v)
        end
        throw(CELEvalError("no matching overload for unary '-'"))  # uint/bool/...
    elseif n isa Cond
        c = evaluate_node(n.cond, ctx)
        c isa Bool ||
            throw(CELEvalError("ternary condition evaluated to a non-boolean"))
        return evaluate_node(c ? n.then : n.els, ctx)   # only the taken branch
    elseif n isa ListLit
        return Any[evaluate_node(x, ctx) for x in n.items]
    elseif n isa MapLit
        out = Dict{Any,Any}()
        ks = Any[]
        for (kn, vn) in n.entries
            k = evaluate_node(kn, ctx)
            _valid_map_key(k) ||
                throw(CELEvalError("map key must be string, int, uint, or bool"))
            any(x -> _cel_eq(x, k), ks) &&
                throw(CELEvalError("duplicate map key"))
            push!(ks, k)
            out[k] = evaluate_node(vn, ctx)
        end
        return out
    elseif n isa Call
        return _eval_call(n, ctx)
    elseif n isa Has
        obj = evaluate_node(n.object, ctx)
        obj isa AbstractDict ||
            throw(CELEvalError("has() on a non-map value"))
        return haskey(obj, n.field)        # absent field: false, not an error
    elseif n isa Compr
        return _eval_compr(n, ctx)
    elseif n isa Bin
        return _eval_bin(n, ctx)
    end
    throw(CELEvalError("unreachable node kind"))
end

# cel-spec pins matches() to RE2 syntax AND to a polynomial cost bound
# (langdef "Performance Limits" -- part of CEL's foundational *terminating*
# guarantee for evaluating untrusted expressions). Both are met by libpcre2's
# ALTERNATIVE matcher, pcre2_dfa_match(): a non-backtracking NFA simulation
# (the same algorithm family as RE2), shipped with every Julia via the
# PCRE2_jll stdlib. PCRE2 alone is not enough, though -- it accepts a
# superset of RE2 syntax, and the DFA matcher silently *matches* lookaround /
# atomic-group / possessive patterns that RE2 must reject at compile time,
# while a few escapes mean different things in the two engines. So every
# pattern first goes through _re2_to_pcre2(): a single pass that rejects
# everything outside the RE2 subset (fail closed, CELEvalError) and rewrites
# the divergent escapes to spellings with the RE2 meaning:
#   * RE2 `\v` is the vertical-tab CHARACTER, PCRE2 `\v` a whitespace class
#     -> rewritten to \x0B;
#   * RE2 `\s` is [\t\n\f\r ] (no VT), PCRE2 `\s` includes VT -> expanded;
#     `\S` is the mirrored complement;
#   * octal escapes are valid RE2 but heuristically read as BACKREFERENCES
#     by PCRE2 -> rewritten to \x{...}; a lone \1..\9 (an RE2 backreference
#     error) is rejected;
#   * `\Z` and `$`-before-trailing-newline are PCRE2-isms: \Z is rejected,
#     and a `$` outside (?m) scope is rewritten to \z (true end-of-text,
#     the RE2 meaning; PCRE2's DOLLAR_ENDONLY option would express this
#     but is unreliable under the DFA matcher with inline (?m)).
# One known, accepted divergence: C++ RE2 runs a byte-level automaton, so
# \b/\B are evaluated between BYTES and \B can match inside a multi-byte
# character (both its bytes being non-word); PCRE2 in UTF mode evaluates
# them between CODEPOINTS and never sees that position. They agree on all
# ASCII text.

_re2_err(msg) = throw(CELEvalError("invalid regular expression: " * msg))

# RE2 \s is [\t\n\f\r ]; PCRE2-\S ∪ {VT} equals RE2-\S.
const _RE2_SPACE_IN_CLASS = "\\t\\n\\f\\r "
const _RE2_NONSPACE_IN_CLASS = "\\S\\x0B"

_re2_ishex(c::Char) = c in '0':'9' || c in 'a':'f' || c in 'A':'F'

# Handles one escape starting at cs[i] == '\\' (cs[i+1] exists). Writes the
# PCRE2 spelling of the RE2 meaning; returns the index just past the escape.
function _re2_escape!(out::IOBuffer, cs::Vector{Char}, i::Int, in_class::Bool)
    n = length(cs)
    c = cs[i+1]
    if c in ('a', 'f', 'n', 'r', 't') || c in ('d', 'D', 'w', 'W')
        write(out, '\\', c)                # identical meaning (ASCII classes)
        return i + 2
    elseif c == 'v'
        write(out, "\\x0B")
        return i + 2
    elseif c == 's'
        in_class ? write(out, _RE2_SPACE_IN_CLASS) :
                   write(out, '[', _RE2_SPACE_IN_CLASS, ']')
        return i + 2
    elseif c == 'S'
        in_class ? write(out, _RE2_NONSPACE_IN_CLASS) :
                   write(out, '[', _RE2_NONSPACE_IN_CLASS, ']')
        return i + 2
    elseif c in ('b', 'B', 'A', 'z', 'C')  # assertions + any-byte \C
        in_class && _re2_err("\\$c is not valid inside a character class")
        write(out, '\\', c)
        return i + 2
    elseif c == 'p' || c == 'P'            # Unicode properties: shared syntax
        i + 2 > n && _re2_err("incomplete \\$c escape")
        if cs[i+2] == '{'
            j = i + 3
            while j <= n && cs[j] != '}'
                j += 1
            end
            j > n && _re2_err("missing } in \\$c{...}")
            foreach(k -> write(out, cs[k]), i:j)
            return j + 1
        end
        write(out, '\\', c, cs[i+2])
        return i + 3
    elseif c == 'x'
        i + 2 > n && _re2_err("incomplete \\x escape")
        if cs[i+2] == '{'
            j = i + 3
            nhex = 0
            while j <= n && cs[j] != '}'
                _re2_ishex(cs[j]) || _re2_err("bad hex digit in \\x{...}")
                nhex += 1
                j += 1
            end
            (j > n || nhex == 0) && _re2_err("malformed \\x{...}")
            foreach(k -> write(out, cs[k]), i:j)
            return j + 1
        end
        (i + 3 <= n && _re2_ishex(cs[i+2]) && _re2_ishex(cs[i+3])) ||
            _re2_err("\\x needs exactly two hex digits or {...}")  # RE2 rule
        write(out, "\\x", cs[i+2], cs[i+3])
        return i + 4
    elseif c == 'Q'                        # \Q...\E literal text: verbatim
        j = i + 2
        while j < n && !(cs[j] == '\\' && cs[j+1] == 'E')
            j += 1
        end
        stop = j < n ? j + 1 : n           # \Q to end-of-pattern is allowed
        foreach(k -> write(out, cs[k]), i:stop)
        return stop + 1
    elseif c == 'E'                        # stray \E: ignored by both engines
        write(out, "\\E")
        return i + 2
    elseif isdigit(c)
        # RE2: \0 starts an octal escape, \1-\7 are octal only when another
        # octal digit follows (a LONE \1 is a backreference: unsupported),
        # \8 \9 are invalid.
        (c == '8' || c == '9') && _re2_err("invalid escape \\$c")
        j = i + 1
        val = 0
        while j <= n && cs[j] in '0':'7' && j - i <= 3
            val = val * 8 + (cs[j] - '0')
            j += 1
        end
        (c != '0' && j == i + 2) && _re2_err("backreferences are not supported")
        write(out, "\\x{", string(val, base = 16), "}")
        return j
    elseif isascii(c) && !(isletter(c) || isdigit(c))
        write(out, '\\', c)   # identity escape: any ASCII non-alnum (RE2 rule)
        return i + 2
    else
        _re2_err("unsupported escape \\$c")
    end
end

# Validates a group opening at cs[i] == '('. RE2 allows plain, (?:, named
# ((?P<name>...) / (?<name>...)), and flag groups over [imsU]; everything
# else PCRE2 understands here (lookaround, atomic groups, conditionals,
# recursion, comments, (*VERB) controls) is outside the RE2 subset.
# `mstack` tracks the multiline flag through group scopes so that `$` can be
# rewritten (see _re2_to_pcre2); its top is the state of the current scope.
function _re2_group!(out::IOBuffer, cs::Vector{Char}, i::Int,
                     mstack::Vector{Bool})
    n = length(cs)
    i + 1 <= n && cs[i+1] == '*' && _re2_err("(*...) verbs are not supported")
    if i + 1 > n || cs[i+1] != '?'
        push!(mstack, mstack[end])
        write(out, '(')
        return i + 1
    end
    i + 2 > n && _re2_err("dangling (?")
    c = cs[i+2]
    if c == ':'
        push!(mstack, mstack[end])
        write(out, "(?:")
        return i + 3
    elseif c == '=' || c == '!'
        _re2_err("lookahead assertions are not supported")
    elseif c == '<' && i + 3 <= n && (cs[i+3] == '=' || cs[i+3] == '!')
        _re2_err("lookbehind assertions are not supported")
    elseif c == '>'
        _re2_err("atomic groups are not supported")
    elseif c == '#'
        _re2_err("(?#...) comments are not supported")
    elseif c == '('
        _re2_err("conditional groups are not supported")
    elseif c == '\''
        _re2_err("(?'name'...) groups are not supported")
    elseif c == 'P' || c == '<'
        j = i + 3
        if c == 'P'                        # (?P= and (?P> land in the error
            (j <= n && cs[j] == '<') ||
                _re2_err("only (?P<name>...) is supported after (?P")
            j += 1
        end
        d = j
        while j <= n && isascii(cs[j]) &&
              (isdigit(cs[j]) || isletter(cs[j]) || cs[j] == '_')
            j += 1
        end
        (j > d && j <= n && cs[j] == '>') ||
            _re2_err("malformed capture group name")
        push!(mstack, mstack[end])
        foreach(k -> write(out, cs[k]), i:j)
        return j + 1
    else                                   # flag group: (?imsU-imsU[:)]
        j = i + 2
        seen_dash = false
        newm = mstack[end]
        while j <= n
            cj = cs[j]
            if cj in ('i', 'm', 's', 'U')
                cj == 'm' && (newm = !seen_dash)
                j += 1
            elseif cj == '-' && !seen_dash
                seen_dash = true
                j += 1
            elseif cj == ':' || cj == ')'
                j == i + 2 && _re2_err("malformed (?...) group")
                if cj == ':'
                    push!(mstack, newm)    # (?flags:...): scoped to the group
                else
                    mstack[end] = newm     # (?flags): to end of enclosing scope
                end
                foreach(k -> write(out, cs[k]), i:j)
                return j + 1
            else
                _re2_err("unsupported (?...) group or flag")
            end
        end
        _re2_err("unterminated (?...) group")
    end
end

function _re2_to_pcre2(pat::String)
    all(isvalid, pat) || _re2_err("pattern is not valid UTF-8")
    cs = collect(pat)
    n = length(cs)
    out = IOBuffer()
    i = 1
    in_class = false
    prev_quant = false     # last token was a quantifier: possessive detection
    mstack = Bool[false]   # multiline-flag scope stack (top = current scope)
    while i <= n
        c = cs[i]
        if c == '\\'
            i == n && _re2_err("trailing backslash")
            i = _re2_escape!(out, cs, i, in_class)
            prev_quant = false
        elseif in_class
            if c == ']'
                in_class = false
                write(out, c)
                i += 1
            elseif c == '[' && i < n && cs[i+1] in (':', '.', '=')
                cs[i+1] == ':' ||
                    _re2_err("collating [$(cs[i+1])...$(cs[i+1])] classes are not supported")
                j = i + 2
                while j < n && !(cs[j] == ':' && cs[j+1] == ']')
                    j += 1
                end
                j >= n && _re2_err("missing closing :] in character class")
                foreach(k -> write(out, cs[k]), i:j+1)
                i = j + 2
            else
                write(out, c)
                i += 1
            end
        elseif c == '('
            i = _re2_group!(out, cs, i, mstack)
            prev_quant = false
        elseif c == ')'
            length(mstack) > 1 && pop!(mstack)  # unbalanced ) errors in PCRE2
            write(out, c)
            i += 1
            prev_quant = false
        elseif c == '$'
            # RE2 `$` without (?m) is true end-of-text (PCRE2 needs \z for
            # that; its DOLLAR_ENDONLY option is unreliable under the DFA
            # matcher when (?m) appears inline, so rewrite instead).
            write(out, mstack[end] ? "\$" : "\\z")
            i += 1
            prev_quant = false
        elseif c == '^' && mstack[end]
            # RE2 `(?m)^` also matches after a newline at the very end of the
            # subject; PCRE2's does not. A length-1 lookbehind (internal
            # only -- user lookbehinds stay rejected) has the RE2 meaning at
            # every position, at O(1) cost per position.
            write(out, "(?:\\A|(?<=\\n))")
            i += 1
            prev_quant = false
        elseif c == '['
            write(out, c)
            i += 1
            if i <= n && cs[i] == '^'
                write(out, '^')
                i += 1
            end
            if i <= n && cs[i] == ']'  # leading ] is literal in RE2 and PCRE2
                write(out, ']')
                i += 1
            end
            in_class = true
            prev_quant = false
        elseif c == '{'
            j = i + 1
            d1 = j
            while j <= n && isdigit(cs[j]) && j - d1 < 8
                j += 1
            end
            lo = j > d1 ? parse(Int, String(cs[d1:j-1])) : -1
            hi = lo
            if lo >= 0 && j <= n && cs[j] == ','
                j += 1
                d2 = j
                while j <= n && isdigit(cs[j]) && j - d2 < 8
                    j += 1
                end
                hi = j > d2 ? parse(Int, String(cs[d2:j-1])) : lo   # {n,}
            end
            if lo >= 0 && j <= n && cs[j] == '}'
                max(lo, hi) > 1000 &&
                    _re2_err("repetition count above the RE2 limit of 1000")
                foreach(k -> write(out, cs[k]), i:j)
                i = j + 1
                prev_quant = true
            else
                write(out, '{')            # not a repeat: literal brace
                i += 1
                prev_quant = false
            end
        elseif c == '*'
            write(out, c)
            i += 1
            prev_quant = true
        elseif c == '+'
            prev_quant && _re2_err("possessive quantifiers are not supported")
            write(out, c)
            i += 1
            prev_quant = true
        elseif c == '?'
            write(out, c)
            i += 1
            prev_quant = !prev_quant       # x*? is the (supported) lazy form
        else
            write(out, c)
            i += 1
            prev_quant = false
        end
    end
    in_class && _re2_err("missing closing ]")
    return String(take!(out))
end

# --- thin ccalls into libpcre2-8 (the PCRE2_jll stdlib) ---

const _PCRE2_UTF = UInt32(0x00080000)
const _PCRE2_DUPNAMES = UInt32(0x00000040)        # RE2 allows duplicate names
const _PCRE2_NEWLINE_LF = UInt32(2)               # RE2 lines end at \n only
const _PCRE2_ERR_NOMATCH = Cint(-1)
const _PCRE2_ERR_DFA_WSSIZE = Cint(-43)

function _pcre2_errmsg(code::Cint)
    buf = Vector{UInt8}(undef, 256)
    r = ccall((:pcre2_get_error_message_8, libpcre2_8), Cint,
              (Cint, Ptr{UInt8}, Csize_t), code, buf, length(buf))
    return r < 0 ? "PCRE2 error $code" : String(buf[1:r])
end

function _pcre2_compile(pat::String)
    cctx = ccall((:pcre2_compile_context_create_8, libpcre2_8), Ptr{Cvoid},
                 (Ptr{Cvoid},), C_NULL)
    cctx == C_NULL && throw(OutOfMemoryError())
    errcode = Ref{Cint}(0)
    erroff = Ref{Csize_t}(0)
    re = try
        ccall((:pcre2_set_newline_8, libpcre2_8), Cint,
              (Ptr{Cvoid}, UInt32), cctx, _PCRE2_NEWLINE_LF)
        ccall((:pcre2_set_parens_nest_limit_8, libpcre2_8), Cint,
              (Ptr{Cvoid}, UInt32), cctx, UInt32(1024))  # RE2 has no 250 cap
        ccall((:pcre2_compile_8, libpcre2_8), Ptr{Cvoid},
              (Ptr{UInt8}, Csize_t, UInt32, Ref{Cint}, Ref{Csize_t}, Ptr{Cvoid}),
              pat, ncodeunits(pat), _PCRE2_UTF | _PCRE2_DUPNAMES,
              errcode, erroff, cctx)
    finally
        ccall((:pcre2_compile_context_free_8, libpcre2_8), Cvoid,
              (Ptr{Cvoid},), cctx)
    end
    re == C_NULL && _re2_err(_pcre2_errmsg(errcode[]))
    return re
end

function _pcre2_dfa_matches(re::Ptr{Cvoid}, s::String)
    md = ccall((:pcre2_match_data_create_8, libpcre2_8), Ptr{Cvoid},
               (UInt32, Ptr{Cvoid}), UInt32(1), C_NULL)
    md == C_NULL && throw(OutOfMemoryError())
    mctx = ccall((:pcre2_match_context_create_8, libpcre2_8), Ptr{Cvoid},
                 (Ptr{Cvoid},), C_NULL)
    if mctx == C_NULL
        ccall((:pcre2_match_data_free_8, libpcre2_8), Cvoid, (Ptr{Cvoid},), md)
        throw(OutOfMemoryError())
    end
    ws = Vector{Cint}(undef, 128)
    local rc::Cint
    try
        # belt-and-braces resource caps on top of the linear-time algorithm
        ccall((:pcre2_set_match_limit_8, libpcre2_8), Cint,
              (Ptr{Cvoid}, UInt32), mctx, UInt32(1) << 24)
        ccall((:pcre2_set_depth_limit_8, libpcre2_8), Cint,
              (Ptr{Cvoid}, UInt32), mctx, UInt32(1) << 20)
        ccall((:pcre2_set_heap_limit_8, libpcre2_8), Cint,
              (Ptr{Cvoid}, UInt32), mctx, UInt32(1) << 16)   # KiB -> 64 MiB
        while true
            rc = ccall((:pcre2_dfa_match_8, libpcre2_8), Cint,
                       (Ptr{Cvoid}, Ptr{UInt8}, Csize_t, Csize_t, UInt32,
                        Ptr{Cvoid}, Ptr{Cvoid}, Ptr{Cint}, Csize_t),
                       re, s, ncodeunits(s), 0, UInt32(0), md, mctx,
                       ws, length(ws))
            rc == _PCRE2_ERR_DFA_WSSIZE && length(ws) < (1 << 22) || break
            resize!(ws, 4 * length(ws))
        end
    finally
        ccall((:pcre2_match_context_free_8, libpcre2_8), Cvoid,
              (Ptr{Cvoid},), mctx)
        ccall((:pcre2_match_data_free_8, libpcre2_8), Cvoid, (Ptr{Cvoid},), md)
    end
    rc >= 0 && return true
    rc == _PCRE2_ERR_NOMATCH && return false
    throw(CELEvalError("regular expression matching failed: " *
                       _pcre2_errmsg(rc)))
end

function _cel_matches(s::AbstractString, pat::AbstractString)
    str = String(s)
    all(isvalid, str) || throw(CELEvalError("matches() on invalid UTF-8"))
    re = _pcre2_compile(_re2_to_pcre2(String(pat)))
    try
        return _pcre2_dfa_matches(re, str)
    finally
        ccall((:pcre2_code_free_8, libpcre2_8), Cvoid, (Ptr{Cvoid},), re)
    end
end

function _eval_call(n::Call, ctx::EvalCtx)
    if n.name == "matches"
        s = evaluate_node(n.args[1], ctx)
        pat = evaluate_node(n.args[2], ctx)
        (s isa AbstractString && pat isa AbstractString) ||
            throw(CELEvalError("matches() requires string arguments"))
        return _cel_matches(s, pat)
    end
    v = evaluate_node(n.args[1], ctx)
    if n.name == "size"
        v isa AbstractString && return Int64(length(v))   # codepoints, not bytes
        (v isa AbstractVector || v isa AbstractDict) && return Int64(length(v))
        throw(CELEvalError("size() on an unsupported type"))
    elseif n.name == "string"
        # Doubles use Julia's shortest-roundtrip formatting, which can
        # differ cosmetically from cel-go's (e.g. "1.0e23" vs "1e+23").
        v isa AbstractString && return String(v)
        v isa Bool && return v ? "true" : "false"
        _isnum(v) && return string(v)
        throw(CELEvalError("string() on an unsupported type"))
    elseif n.name == "int"
        return _to_int(v)
    elseif n.name == "uint"
        return _to_uint(v)
    elseif n.name == "bool"
        return _to_bool(v)
    elseif n.name == "dyn"
        # cel-spec: dyn "does not exist at runtime" -- a type-checker hint.
        # In a dynamically-typed evaluator it is the identity, accepted so
        # conformant expressions written for checked environments compile.
        return v
    end
    return _to_double(v)                   # parser admits no other names
end

# bool(string) accepts EXACTLY the cel-spec ten-token set (pinned by the
# conformance suite's conversions cases): 1/t/true/TRUE/True and their
# false counterparts. Mixed case ("TrUe") is a conversion error.
const _BOOL_TRUE_TOKENS = ("1", "t", "true", "TRUE", "True")
const _BOOL_FALSE_TOKENS = ("0", "f", "false", "FALSE", "False")
function _to_bool(v)
    v isa Bool && return v                 # identity
    if v isa AbstractString
        v in _BOOL_TRUE_TOKENS && return true
        v in _BOOL_FALSE_TOKENS && return false
        throw(CELEvalError("bool() could not parse the string"))
    end
    throw(CELEvalError("bool() on an unsupported type"))
end

function _to_int(v)
    v isa Signed && return Int64(v)
    if v isa Unsigned
        v <= typemax(Int64) || throw(CELEvalError("int() out of range"))
        return Int64(v)
    elseif v isa AbstractFloat
        f = trunc(Float64(v))              # cel-spec: truncation toward zero
        (isnan(f) || f < -9.223372036854775808e18 || f >= 9.223372036854775808e18) &&
            throw(CELEvalError("int() out of range"))
        return Int64(f)
    elseif v isa AbstractString
        x = tryparse(Int64, v)
        x === nothing && throw(CELEvalError("int() could not parse the string"))
        return x
    end
    throw(CELEvalError("int() on an unsupported type"))
end

function _to_uint(v)
    if v isa Bool
        throw(CELEvalError("uint() on an unsupported type"))
    elseif v isa Unsigned
        return UInt64(v)
    elseif v isa Signed
        v >= 0 || throw(CELEvalError("uint() out of range"))
        return UInt64(v)
    elseif v isa AbstractFloat
        f = trunc(Float64(v))
        (isnan(f) || f < 0 || f >= 1.8446744073709552e19) &&
            throw(CELEvalError("uint() out of range"))
        return UInt64(f)
    elseif v isa AbstractString
        x = tryparse(UInt64, v)
        x === nothing && throw(CELEvalError("uint() could not parse the string"))
        return x
    end
    throw(CELEvalError("uint() on an unsupported type"))
end

function _to_double(v)
    v isa Bool && throw(CELEvalError("double() on an unsupported type"))
    v isa Number && return Float64(v)
    if v isa AbstractString
        x = tryparse(Float64, v)
        x === nothing && throw(CELEvalError("double() could not parse the string"))
        return x
    end
    throw(CELEvalError("double() on an unsupported type"))
end

# Arithmetic. cel-spec has no implicit numeric promotion: both operands
# must be ints, both uints, or both doubles (`1 + 1.0` errors even
# though `1 == 1.0` holds). Integer arithmetic is CHECKED (Base.Checked):
# overflow, division/modulo by zero, and INT64_MIN / -1 (or % -1) are
# evaluation errors, never wraparound. Integer `/` truncates toward zero
# and `%` keeps the dividend's sign (Julia's div/rem). Doubles follow
# IEEE 754 -- `x / 0.0` is +/-Inf, never an error -- and cel-spec gives
# `%` no double overload.
function _eval_arith(op::String, l, r)
    if op == "+"
        l isa AbstractString && r isa AbstractString && return l * r
        if l isa AbstractVector && r isa AbstractVector
            out = Any[]
            append!(out, l)
            append!(out, r)
            return out
        end
    end
    if l isa AbstractFloat && r isa AbstractFloat
        a, b = Float64(l), Float64(r)
        op == "+" && return a + b
        op == "-" && return a - b
        op == "*" && return a * b
        op == "/" && return a / b
        throw(CELEvalError("no matching overload for '%' on doubles"))
    elseif l isa Signed && r isa Signed        # Bool is neither Signed nor Unsigned
        a, b = Int64(l), Int64(r)
        try
            op == "+" && return Base.checked_add(a, b)
            op == "-" && return Base.checked_sub(a, b)
            op == "*" && return Base.checked_mul(a, b)
            if op == "/"
                b == 0 && throw(CELEvalError("division by zero"))
                return div(a, b)   # truncates toward zero; typemin/-1 raises DivideError
            end
            b == 0 && throw(CELEvalError("modulo by zero"))
            (a == typemin(Int64) && b == -1) &&
                throw(CELEvalError("integer overflow in '%'"))
            return rem(a, b)
        catch e
            e isa CELEvalError && rethrow()
            (e isa OverflowError || e isa DivideError) &&
                throw(CELEvalError("integer overflow in '$(op)'"))
            rethrow()
        end
    elseif l isa Unsigned && r isa Unsigned
        a, b = UInt64(l), UInt64(r)
        try
            op == "+" && return Base.checked_add(a, b)
            op == "-" && return Base.checked_sub(a, b)
            op == "*" && return Base.checked_mul(a, b)
            b == 0 &&
                throw(CELEvalError(op == "/" ? "division by zero" : "modulo by zero"))
            op == "/" && return div(a, b)
            return rem(a, b)
        catch e
            e isa CELEvalError && rethrow()
            e isa OverflowError &&
                throw(CELEvalError("unsigned integer overflow in '$(op)'"))
            rethrow()
        end
    end
    throw(CELEvalError("no matching overload for '$(op)'"))
end

# `x in list` tests element membership, `x in map` tests KEY membership,
# both by the same exact cross-type equality as `==`.
function _eval_in(x, coll)
    coll isa AbstractVector && return any(e -> _cel_eq(e, x), coll)
    coll isa AbstractDict && return any(k -> _cel_eq(k, x), keys(coll))
    throw(CELEvalError("'in' on a non-list/non-map value"))
end

# Comprehension macros. A map comprehension iterates its KEYS (cel-spec).
# `exists`/`all` mirror `||`/`&&` error absorption: a per-element error
# is absorbed when some element decides the result (a true decides
# `exists`, a false decides `all`); otherwise the FIRST error propagates.
# `exists_one`, `filter`, and `map` propagate any error immediately.
# The wall clock is re-checked every iteration and a timeout is never
# absorbed.
function _eval_compr(n::Compr, ctx::EvalCtx)
    obj = evaluate_node(n.object, ctx)
    items = obj isa AbstractVector ? obj :
            obj isa AbstractDict ? collect(keys(obj)) :
            throw(CELEvalError("comprehension over a non-list/non-map value"))
    body_ctx(item) = EvalCtx(VarScope(n.var, item, ctx.vars), ctx.deadline)
    if n.kind == "exists" || n.kind == "all"
        decides = n.kind == "exists"
        err = nothing
        for item in items
            _check_deadline(ctx)
            try
                _eval_bool(n.body, body_ctx(item)) == decides && return decides
            catch e
                e isa CELEvalError || rethrow()
                _check_deadline(ctx)       # a timeout is never absorbed
                err === nothing && (err = e)
            end
        end
        err === nothing || throw(err)
        return !decides
    elseif n.kind == "exists_one"
        hits = 0
        for item in items
            _check_deadline(ctx)
            _eval_bool(n.body, body_ctx(item)) && (hits += 1)
        end
        return hits == 1
    elseif n.kind == "filter"
        out = Any[]
        for item in items
            _check_deadline(ctx)
            _eval_bool(n.body, body_ctx(item)) && push!(out, item)
        end
        return out
    end
    out = Any[]                            # n.kind == "map"
    for item in items
        _check_deadline(ctx)
        push!(out, evaluate_node(n.body, body_ctx(item)))
    end
    return out
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
    n.op == "in" && return _eval_in(l, r)
    n.op in ("+", "-", "*", "/", "%") && return _eval_arith(n.op, l, r)
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
mismatches, checked-arithmetic overflow, or exceeding `timeout`
(seconds, wall clock); [`CELParseError`](@ref) when given an
uncompilable source string.
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
