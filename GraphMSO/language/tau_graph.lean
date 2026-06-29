import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# `τ_P`-graphs

The lecture note uses the vocabulary `τ_P = {adj} ∪ P`: one binary adjacency
relation and a family of unary predicates indexed by `P`.  In Lean, the
adjacency symbol is represented by the mandatory `SimpleGraph` field, while
`P` indexes only the unary predicate symbols.
-/

universe u v

/-- Predicate symbols for quick examples.  The main definition is polymorphic in
the predicate-symbol type, so this abbreviation is not built into `τPGraph`. -/
abbrev pred_symbol := ℕ

/-- A `τ_P`-graph: a simple graph together with one unary predicate on vertices
for every predicate symbol `p : P`.

The `adj` symbol from `τ_P` is not an element of `P`; it is interpreted by the
required field `G : SimpleGraph V`.  The ordinary graph case is obtained by
taking `P = Empty`. -/
structure τPGraph (P : Type u) where
  /-- The vertex type. -/
  V : Type v
  /-- The interpretation of the distinguished binary symbol `adj`. -/
  G : SimpleGraph V
  /-- The interpretation of each unary predicate symbol. -/
  pred : P → V → Prop

/-- ASCII alias for `τPGraph`. -/
abbrev TauPGraph (P : Type u) := τPGraph P

namespace τPGraph

variable {P : Type u}

/-- The adjacency relation of a `τ_P`-graph. -/
def Adj (X : τPGraph P) : X.V → X.V → Prop :=
  X.G.Adj

/-- The unary predicate interpretation of a symbol `p : P`. -/
def Pred (X : τPGraph P) (p : P) : X.V → Prop :=
  X.pred p

/-- The underlying simple graph of a `τ_P`-graph. -/
def underlying (X : τPGraph P) : SimpleGraph X.V :=
  X.G

/-- View an ordinary simple graph as a `τ_P`-graph with no unary predicate
symbols. -/
def ofSimpleGraph {V : Type v} (G : SimpleGraph V) : τPGraph Empty where
  V := V
  G := G
  pred := Empty.elim

@[simp]
theorem adj_eq (X : τPGraph P) : X.Adj = X.G.Adj :=
  rfl

@[simp]
theorem pred_eq (X : τPGraph P) (p : P) : X.Pred p = X.pred p :=
  rfl

end τPGraph
