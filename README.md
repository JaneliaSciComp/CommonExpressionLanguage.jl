# CommonExpressionLanguage.jl

A native-Julia evaluator for a subset of the
[Common Expression Language](https://cel.dev) (CEL) — no wrapping of
cel-go/cel-cpp/cel-c, and no dependencies beyond the libpcre2 that
ships inside every Julia (the PCRE2_jll stdlib, used by `matches`).

```julia
using CommonExpressionLanguage
const CEL = CommonExpressionLanguage

ctx = Dict{String,Any}(
    "labels" => Dict{String,Any}("zone" => "A"),
    "status" => Dict{String,Any}("battery" => 72))

CEL.evaluate_bool("labels.zone == \"A\" && status.battery > 50", ctx)  # true

prog = CEL.compile("status.battery > 50")   # compile once, reuse
CEL.evaluate_bool(prog, ctx; timeout=0.5)   # wall-clock bounded
```

## Scope

The practical predicate subset — boolean expressions over structured
context data, the common case for policy rules, filters, and
self-election predicates:

```
expr     := or ( '?' or ':' expr )?
or       := and ( '||' and )*
and      := rel ( '&&' rel )*
rel      := add ( ('=='|'!='|'<'|'<='|'>'|'>='|'in') add )?
add      := mul ( ('+'|'-') mul )*
mul      := unary ( ('*'|'/'|'%') unary )*
unary    := ('!'|'-') unary | postfix
postfix  := primary ( '.' ident | '.' method '(' expr ')'
                    | '.' macro '(' ident ',' expr ')' | '[' expr ']' )*
primary  := literal | ident | func '(' expr (',' expr)* ')'
          | '(' expr ')' | '[' exprlist? ']' | '{' entrylist? '}'
literal  := string | number | 'true' | 'false' | 'null'
method   := 'startsWith' | 'endsWith' | 'contains' | 'matches'
macro    := 'exists' | 'all' | 'exists_one' | 'filter' | 'map'
func     := 'size' | 'has' | 'string' | 'int' | 'uint' | 'double'
          | 'bool' | 'dyn' | 'matches'
```

Anything outside the subset **fails to compile** (`CELParseError`), never
silently misparses — so callers can route unsupported expressions to a
fail-closed policy.

## Semantics (following cel-spec where the subset touches it)

- Numeric equality/ordering is **exact** across Int64/UInt64/Float64
  (distinct 64-bit integers never alias through a double).
- `bool` is not numeric: `true != 1`.
- Arithmetic is **checked** (cel-spec): Int64/UInt64 overflow, integer
  division/modulo by zero, and `INT64_MIN / -1` are evaluation errors,
  never wraparound; integer `/` truncates toward zero and `%` keeps the
  dividend's sign; doubles follow IEEE 754 (`x / 0.0` is ±Inf, and `%`
  has no double overload). Operands must share a numeric type — cel-spec
  has no implicit promotion (`1 + 1u` errors) even though *equality* is
  exact across types. `+` also concatenates strings and lists.
- A missing variable, member, or key is an evaluation **error** (CEL's
  absent-field semantics), not `null`; `has(e.f)` is the presence test
  and, being a macro, only compiles on a field selection.
- Map literal keys are string/int/uint/bool; a duplicate key is an
  evaluation error; map indexing and `in` use the same exact cross-type
  equality as `==`.
- Comprehension macros follow cel-spec error absorption: `exists`
  absorbs per-element errors once a `true` is found, `all` once a
  `false` is found; `exists_one`/`filter`/`map` propagate the first
  error. Map comprehensions iterate **keys**.
- The ternary evaluates only the taken branch and requires a `bool`
  condition.
- `matches` runs on libpcre2's **non-backtracking DFA matcher**
  (`pcre2_dfa_match`, the same algorithm family as RE2), via the PCRE2_jll
  stdlib that ships inside every Julia. cel-spec pins `matches()` to RE2
  syntax *and* to a polynomial cost bound (part of CEL's terminating
  guarantee); the DFA meets the cost bound, and a compile-time screen
  enforces the syntax: a PCRE-only construct (backreference, lookaround,
  atomic/possessive group, `\Z`, …) is a fail-closed `CELEvalError`
  exactly as under RE2 — crucial because the DFA matcher would otherwise
  silently *match* lookarounds. The screen also rewrites the escapes whose
  meaning differs (`\v`, `\s`, `\S`, octal, non-multiline `$`, `(?m)^`) to
  spellings with the RE2 meaning, a mapping fuzz-verified against the real
  C++ RE2 (hundreds of thousands of pattern/subject checks, zero
  disagreements; the one accepted divergence is `\b`/`\B` *inside* a
  multi-byte character, where C++ RE2's byte-level automaton can assert
  but a codepoint-level matcher cannot). Matching cannot catastrophically
  backtrack — a hostile pattern or input cannot become a denial of
  service.
- `&&`/`||` are **commutative over errors**: an errored arm is absorbed
  when the other arm alone decides the result (false decides `&&`, true
  decides `||`); otherwise the error propagates.
- Evaluation is wall-clock bounded (`timeout` keyword), re-checked every
  comprehension iteration; a timeout is never absorbed by `&&`/`||` or
  by `exists`/`all`.
- `evaluate_bool` refuses non-boolean results — no truthiness coercion.
- Guards: 2048-byte source cap, 64-level nesting cap (stack-overflow
  proofing for hostile inputs).

## Extending toward full CEL

The architecture mirrors the cel-spec pipeline (lexer → AST →
tree-walking evaluator over a variable environment) so the rest of the
language can land incrementally:

- **bytes/timestamp/duration** values and their functions.
- **`type(x)` and type values**: deliberately skipped so far — honest
  type values need type literals like `int` as identifiers, and a string
  stand-in would make `type(x) == "int"` hold where cel-spec says it
  must not.
- **A type checker**: a separate pass over the same `Node` tree.
- **cel-spec conformance**: the upstream
  [conformance suite](https://github.com/cel-expr/cel-spec) is the
  eventual referee for any of the above.

Contributions welcome.
