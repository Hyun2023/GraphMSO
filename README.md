# GraphMSO

`GraphMSO` is a Lean 4 scaffold for formalizing MSO2 over graphs on the way to a
formalization of Courcelle's theorem.

The current project is intentionally small and build-oriented:

- `GraphMSO.Basic`: a monomorphic incidence-graph compatibility layer
  (`IncidenceGraph V E`) plus bridges to/from mathlib `SimpleGraph`.
- `GraphMSO.Syntax`: named-variable MSO2 syntax over the graph signature,
  supporting both vertex and edge variables.
- `GraphMSO.Semantics`: Tarski semantics over mathlib `SimpleGraph V`; edge
  variables range over `G.edgeSet`, while `Assignment V E` remains the reusable
  environment type.
- `GraphMSO.Examples`: representative MSO graph formulas such as clique,
  independence, domination, vertex cover, bipartiteness, and smoke tests.

The theorem-facing graph representation is now mathlib `SimpleGraph V`.
`IncidenceGraph V E` remains available for explicit-incidence experiments and
conversion lemmas.

## Build

```bash
lake exe cache get
lake build
```

Run `lake exe cache get` before the first build after dependency updates so Lean
uses mathlib's precompiled cache instead of compiling mathlib locally.

## Design Status

Free-variable semantics use `Semantics.EvalAt phi G rho`. The graph-property
wrapper `Semantics.Eval phi G` is intended for closed formulas and is currently
implemented as validity under every assignment until assignment independence is
proved.

The syntax currently uses named numeric variables (`Nat`) for first-order and
second-order variables. If substitution, alpha-equivalence, or automation becomes
central, the project should migrate to de Bruijn indices or locally nameless
syntax while keeping named syntax as a user-facing layer.
