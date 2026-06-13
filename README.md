# GraphMSO

`GraphMSO` is a Lean 4 scaffold for formalizing monadic second-order logic over
graphs.

The current project is intentionally small and build-oriented:

- `GraphMSO.Basic`: graphs as adjacency predicates and basic graph predicates.
- `GraphMSO.Syntax`: named-variable MSO syntax over the graph signature.
- `GraphMSO.Semantics`: Tarski semantics by first-order and second-order
  assignments, using `VSet V := V -> Prop` for vertex sets.
- `GraphMSO.Examples`: representative MSO graph formulas such as clique,
  independence, domination, and smoke-test examples.

This initial version avoids external dependencies, including mathlib, so it can
serve as a stable base. A later phase can add mathlib and connect this encoding
to `SimpleGraph`, finite graphs, and existing graph-theory results.

## Build

```bash
lake build
```

## Design Status

The syntax currently uses named numeric variables (`Nat`) for both first-order
and second-order variables. This is simple and readable for early development.
If substitution, alpha-equivalence, or automation becomes central, the project
should migrate to de Bruijn indices or locally nameless syntax.
