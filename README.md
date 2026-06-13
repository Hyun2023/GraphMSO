# GraphMSO

`GraphMSO` is a Lean 4 scaffold for formalizing monadic second-order logic over
graphs.

The current project is intentionally small and build-oriented:

- `GraphMSO.Basic`: graphs as adjacency predicates, mathlib `Set`-based vertex sets,
  and bridges to/from mathlib `SimpleGraph`.
- `GraphMSO.Syntax`: named-variable MSO syntax over the graph signature.
- `GraphMSO.Semantics`: Tarski semantics by first-order and second-order
  assignments, using `VSet V := Set V` for vertex sets.
- `GraphMSO.Examples`: representative MSO graph formulas such as clique,
  independence, domination, and smoke-test examples.

The project now depends on mathlib. The core graph representation is still the
small relation-based `Graph V`, but vertex sets use mathlib `Set V`, and
`GraphMSO.Basic` provides conversion helpers for mathlib `SimpleGraph`.

## Build

```bash
lake exe cache get
lake build
```

Run `lake exe cache get` before the first build after dependency updates so Lean
uses mathlib's precompiled cache instead of compiling mathlib locally.

## Design Status

The syntax currently uses named numeric variables (`Nat`) for both first-order
and second-order variables. This is simple and readable for early development.
If substitution, alpha-equivalence, or automation becomes central, the project
should migrate to de Bruijn indices or locally nameless syntax.
