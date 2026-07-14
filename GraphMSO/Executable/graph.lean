import GraphMSO.language.tau_graph

/-!
# Executable finite graph data

The mathematical graph structure used by the semantics stores adjacency and
unary predicates in `Prop`.  This companion structure stores the same
information as Boolean functions, while retaining proofs that adjacency is a
simple graph.  The finite input checker will use these Boolean functions; the
map to `τPGraph` is the refinement boundary used in correctness theorems.
-/

namespace GraphMSO.Executable

universe u v

/-- A Boolean presentation of a simple graph with unary predicates. -/
structure TauPGraph (P : Type u) (V : Type v) where
  /-- Decidable adjacency oracle. -/
  adj : V → V → Bool
  /-- Decidable unary-predicate oracle. -/
  pred : P → V → Bool
  /-- Adjacency is symmetric. -/
  adj_symm : ∀ u v, adj u v = adj v u
  /-- There are no loops. -/
  adj_loopless : ∀ v, adj v v = false

namespace TauPGraph

variable {P : Type u} {V : Type v}

/-- Forget the Boolean presentation and recover the mathematical structure. -/
def toMath (X : TauPGraph P V) : _root_.τPGraph P where
  V := V
  G :=
    { Adj := fun u v => X.adj u v = true
      symm := by
        intro u v h
        rwa [X.adj_symm]
      loopless := by
        intro v h
        rw [X.adj_loopless] at h
        cases h }
  pred := fun p v => X.pred p v = true

@[simp] theorem toMath_adj_iff (X : TauPGraph P V) (u v : V) :
    X.toMath.G.Adj u v ↔ X.adj u v = true :=
  Iff.rfl

@[simp] theorem toMath_pred_iff (X : TauPGraph P V) (p : P) (v : V) :
    X.toMath.pred p v ↔ X.pred p v = true :=
  Iff.rfl

end TauPGraph

end GraphMSO.Executable
