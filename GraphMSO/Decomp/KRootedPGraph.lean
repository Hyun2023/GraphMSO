import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The `τ_P`-structure core

A `KRootedPGraph P` is a graph together with a family of unary predicates indexed
by a fixed predicate-symbol type `P`: that is, a relational structure over the
vocabulary `τ_P = {adj} ∪ P`.  It is the shared core on top of which the
Courcelle construction is built:

* the rooted, labelled graphs (`KRooted`) extend this with a root set and a
  partial injective coloring;
* the `Σ_ω`-letters of the encoding are letters over this structure; and
* the coloured incidence structure (`P = {Vert, EdgeObj}`) is one instance.

The ordinary graph case is `P` empty.

Finiteness or decidability of `P` (`[Fintype P]`, `[DecidableEq P]`) is assumed
only in the lemmas that need it, never baked into this structure.
-/

/-- A `τ_P`-structure: a graph `G` on vertices `V` together with a family of unary
predicates `pred p : V → Prop`, one for each predicate symbol `p : P`.  The
adjacency relation is reused from Mathlib's `SimpleGraph`; the unary predicates
are the `P` part of the vocabulary `τ_P = {adj} ∪ P`. -/
structure KRootedPGraph (P : Type*) where
  /-- The vertex type. -/
  V : Type*
  /-- The adjacency relation (`adj`). -/
  G : SimpleGraph V
  /-- The interpretation of each unary predicate symbol `p : P`. -/
  pred : P → V → Prop
