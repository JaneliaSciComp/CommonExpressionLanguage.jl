# CommonExpressionLanguage.jl

A native-Julia evaluator for a subset of the
[Common Expression Language](https://cel.dev) (CEL) — no wrapping of
cel-go/cel-cpp/cel-c, no binary dependencies, no deps at all.

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
or       := and ( '||' and )*
and      := rel ( '&&' rel )*
rel      := unary ( ('=='|'!='|'<'|'<='|'>'|'>=') unary )?
unary    := '!' unary | postfix
postfix  := primary ( '.' ident | '.' method '(' or ')' | '[' or ']' )*
primary  := literal | ident | '(' or ')'
literal  := string | number | 'true' | 'false' | 'null'
method   := 'startsWith' | 'endsWith' | 'contains'
```

Anything outside the subset **fails to compile** (`CELParseError`), never
silently misparses — so callers can route unsupported expressions to a
fail-closed policy.

## Semantics (following cel-spec where the subset touches it)

- Numeric equality/ordering is **exact** across Int64/UInt64/Float64
  (distinct 64-bit integers never alias through a double).
- `bool` is not numeric: `true != 1`.
- A missing variable, member, or key is an evaluation **error** (CEL's
  absent-field semantics), not `null`.
- `&&`/`||` are **commutative over errors**: an errored arm is absorbed
  when the other arm alone decides the result (false decides `&&`, true
  decides `||`); otherwise the error propagates.
- Evaluation is wall-clock bounded (`timeout` keyword); a timeout is
  never absorbed by `&&`/`||`.
- `evaluate_bool` refuses non-boolean results — no truthiness coercion.
- Guards: 2048-byte source cap, 64-level nesting cap (stack-overflow
  proofing for hostile inputs).

## Extending toward full CEL

The architecture mirrors the cel-spec pipeline (lexer → AST →
tree-walking evaluator over a variable environment) so the rest of the
language can land incrementally:

- **Operators** (`+ - * / %`, `in`, `? :`): one entry in the parser's
  precedence ladder plus an `_eval_bin` branch.
- **List/map literals**: two `parse_primary` productions.
- **Functions and macros** (`size`, `has`, `matches`, comprehensions):
  dispatch alongside the string-method route in `parse_postfix` /
  `evaluate_node`.
- **A type checker**: a separate pass over the same `Node` tree.
- **cel-spec conformance**: the upstream
  [conformance suite](https://github.com/cel-expr/cel-spec) is the
  eventual referee for any of the above.

Contributions welcome.
