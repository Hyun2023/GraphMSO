import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Basic

namespace GraphMSO

universe u

/-- Vertex sets are mathlib sets. -/
abbrev VSet (V : Type u) := Set V

/-- A graph is represented by its adjacency predicate.

This core representation remains intentionally general: directed graphs, loops, and
infinite vertex types are all allowed. Undirected simple graphs can be recovered by
adding the `Simple` predicate below, or by converting from mathlib `SimpleGraph`. -/
structure Graph (V : Type u) where
  Adj : V -> V -> Prop

namespace Graph

variable {V : Type u}

/-- No loops. -/
def Irreflexive (G : Graph V) : Prop :=
  _root_.Irreflexive G.Adj

/-- Undirected adjacency. -/
def Symmetric (G : Graph V) : Prop :=
  _root_.Symmetric G.Adj

/-- The usual simple-graph side condition for this relation-based encoding. -/
def Simple (G : Graph V) : Prop :=
  Irreflexive G /\ Symmetric G

/-- The empty graph on a vertex type. -/
def empty (V : Type u) : Graph V where
  Adj := fun _ _ => False

/-- The complete loopless graph on a vertex type. -/
def complete (V : Type u) : Graph V where
  Adj := fun u v => Not (u = v)

/-- View a mathlib simple graph as a `GraphMSO.Graph`. -/
def fromSimpleGraph (G : SimpleGraph V) : Graph V where
  Adj := G.Adj

/-- Turn a `GraphMSO.Graph` satisfying `Graph.Simple` into a mathlib simple graph. -/
def toSimpleGraph (G : Graph V) (hG : Simple G) : SimpleGraph V where
  Adj := G.Adj
  symm := by
    intro u v huv
    exact hG.2 huv
  loopless := by
    intro v
    exact hG.1 v

/-- The graph obtained from a mathlib simple graph is simple. -/
theorem fromSimpleGraph_simple (G : SimpleGraph V) : Simple (fromSimpleGraph G) := by
  constructor
  · intro v
    exact G.loopless v
  · intro u v huv
    exact G.symm huv

/-- Restrict a graph to vertices in a mathlib set. -/
def induced (G : Graph V) (S : VSet V) : Graph {v : V // v ∈ S} where
  Adj := fun u v => G.Adj u.1 v.1

/-- A set of vertices is a clique if every two distinct vertices in it are adjacent. -/
def IsClique (G : Graph V) (S : VSet V) : Prop :=
  forall u v : V, u ∈ S -> v ∈ S -> Not (u = v) -> G.Adj u v

/-- A set of vertices is independent if no two distinct vertices in it are adjacent. -/
def IsIndependent (G : Graph V) (S : VSet V) : Prop :=
  forall u v : V, u ∈ S -> v ∈ S -> Not (u = v) -> Not (G.Adj u v)

/-- A set of vertices is dominating if every vertex is in it or has an incoming neighbor in it. -/
def IsDominating (G : Graph V) (S : VSet V) : Prop :=
  forall v : V, v ∈ S \/ Exists (fun u : V => u ∈ S /\ G.Adj u v)

theorem empty_irreflexive (V : Type u) : Irreflexive (empty V) := by
  intro v h
  exact h

theorem complete_irreflexive (V : Type u) : Irreflexive (complete V) := by
  intro v h
  exact h rfl

end Graph

end GraphMSO
