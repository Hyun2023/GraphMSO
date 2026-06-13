namespace GraphMSO

universe u

/-- Vertex sets are represented as predicates.

This local alias keeps the scaffold dependency-free. A later mathlib-backed layer
can bridge this to mathlib Set. -/
abbrev VSet (V : Type u) := V -> Prop

/-- A graph is represented by its adjacency predicate.

The scaffold keeps this intentionally general: directed graphs, loops, and infinite
vertex types are all allowed. Undirected simple graphs can be recovered by adding
the `Simple` predicate below. -/
structure Graph (V : Type u) where
  Adj : V -> V -> Prop

namespace Graph

variable {V : Type u}

/-- No loops. -/
def Irreflexive (G : Graph V) : Prop :=
  forall v : V, Not (G.Adj v v)

/-- Undirected adjacency. -/
def Symmetric (G : Graph V) : Prop :=
  forall u v : V, G.Adj u v -> G.Adj v u

/-- The usual simple-graph side condition for this relation-based encoding. -/
def Simple (G : Graph V) : Prop :=
  Irreflexive G /\ Symmetric G

/-- The empty graph on a vertex type. -/
def empty (V : Type u) : Graph V where
  Adj := fun _ _ => False

/-- The complete loopless graph on a vertex type. -/
def complete (V : Type u) : Graph V where
  Adj := fun u v => Not (u = v)

/-- Restrict a graph to vertices satisfying a predicate. -/
def induced (G : Graph V) (S : VSet V) : Graph {v : V // S v} where
  Adj := fun u v => G.Adj u.1 v.1

/-- A set of vertices is a clique if every two distinct vertices in it are adjacent. -/
def IsClique (G : Graph V) (S : VSet V) : Prop :=
  forall u v : V, S u -> S v -> Not (u = v) -> G.Adj u v

/-- A set of vertices is independent if no two distinct vertices in it are adjacent. -/
def IsIndependent (G : Graph V) (S : VSet V) : Prop :=
  forall u v : V, S u -> S v -> Not (u = v) -> Not (G.Adj u v)

theorem empty_irreflexive (V : Type u) : Irreflexive (empty V) := by
  intro v h
  exact h

theorem complete_irreflexive (V : Type u) : Irreflexive (complete V) := by
  intro v h
  exact h rfl

end Graph

end GraphMSO
