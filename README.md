# GraphMSO

`GraphMSO` is a Lean 4 scaffold for formalizing monadic second-order logic (MSO2)
over graphs.

The current project is intentionally small and build-oriented:

- `GraphMSO.Basic`: bipartite incidence graphs with vertices `V` and edges `E` where edges connect 1 or 2 vertices. Adjacency is derived, mathlib `Set`-based vertex/edge sets, and bridges to/from mathlib `SimpleGraph`.
- `GraphMSO.Syntax`: named-variable MSO2 syntax over the graph signature, supporting both vertex and edge variables.
- `GraphMSO.Semantics`: Tarski semantics by first-order and second-order
  assignments, accommodating both vertex sets (`Set V`) and edge sets.
- `GraphMSO.Examples`: representative MSO graph formulas such as clique,
  independence, domination, and smoke-test examples.

The project now depends on mathlib. The core graph representation is a two-sorted
structure `Graph V E` with an explicit incidence relation. Vertex and edge sets
use mathlib `Set V` and `Set E`, and `GraphMSO.Basic` provides conversion helpers
for mathlib `SimpleGraph`.

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
