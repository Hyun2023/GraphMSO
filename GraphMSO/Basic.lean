import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Basic

namespace GraphMSO

universe u

/-- Vertex sets are mathlib sets. -/
abbrev VSet (V : Type u) := Set V

/-- Edge sets are mathlib sets. -/
abbrev ESet (E : Type u) := Set E

/-- A bipartite incidence graph representation.

This core representation supports MSO2 by explicitly having an edge type `E`
and an incidence relation. Directed graphs or graphs with loops can be encoded,
but we require each edge to connect at least one and at most two vertices. -/
structure Graph (V E : Type u) where
  inc : V -> E -> Prop
  inc_at_least_one : ∀ e : E, ∃ v : V, inc v e
  inc_at_most_two : ∀ e : E, ∃ v1 v2 : V, ∀ v : V, inc v e → v = v1 ∨ v = v2

namespace Graph

variable {V E : Type u} (G : Graph V E)

/-- An edge is a loop if it is incident to exactly one vertex. -/
def IsLoop (e : E) : Prop :=
  ∃ v : V, G.inc v e ∧ ∀ w : V, G.inc w e → w = v

/-- Derived adjacency relation. If u = v, they are adjacent if there is a loop at u.
If u ≠ v, they are adjacent if they share an edge. -/
def Adj (u v : V) : Prop :=
  (u = v ∧ ∃ e : E, G.IsLoop e ∧ G.inc u e) ∨
  (u ≠ v ∧ ∃ e : E, G.inc u e ∧ G.inc v e)

/-- No loops. -/
def Irreflexive : Prop :=
  _root_.Irreflexive G.Adj

/-- Undirected adjacency. -/
def Symmetric : Prop :=
  _root_.Symmetric G.Adj

/-- The usual simple-graph side condition for this relation-based encoding. -/
def Simple : Prop :=
  G.Irreflexive /\ G.Symmetric

/-- The empty graph on a vertex type. -/
def empty (V : Type u) : Graph V Empty where
  inc := fun _ _ => False
  inc_at_least_one := fun e => Empty.elim e
  inc_at_most_two := fun e => Empty.elim e

/-- View a mathlib simple graph as a `GraphMSO.Graph`. -/
def fromSimpleGraph (G : SimpleGraph V) : Graph V G.edgeSet where
  inc := fun v e => v ∈ e.val
  inc_at_least_one := by
    rintro ⟨e, _⟩
    refine Quotient.inductionOn e ?_
    intro ⟨x, y⟩
    exact ⟨x, by simp⟩
  inc_at_most_two := by
    rintro ⟨e, _⟩
    refine Quotient.inductionOn e ?_
    intro ⟨x, y⟩
    exact ⟨x, y, fun w => by simp⟩

/-- Turn a `GraphMSO.Graph` satisfying `Graph.Simple` into a mathlib simple graph. -/
def toSimpleGraph (hG : G.Simple) : SimpleGraph V where
  Adj := G.Adj
  symm := by
    intro u v h
    rcases h with ⟨heq, ⟨e, hloop, hinc⟩⟩ | ⟨hne, ⟨e, hinc_u, hinc_v⟩⟩
    · left
      exact ⟨heq.symm, ⟨e, hloop, by rwa [heq]⟩⟩
    · right
      exact ⟨hne.symm, ⟨e, hinc_v, hinc_u⟩⟩
  loopless := by
    intro v
    exact hG.1 v

/-- The graph obtained from a mathlib simple graph is simple. -/
theorem fromSimpleGraph_simple (G : SimpleGraph V) : (fromSimpleGraph G).Simple := by
  constructor
  · intro v h
    rcases h with ⟨_, ⟨⟨e, he_edge⟩, ⟨u, _, hu_only⟩⟩, hv_inc⟩ | ⟨hne, _⟩
    · have h_only_v : ∀ w, w ∈ e → w = v := by
        intro w hw
        have hw_u := hu_only w hw
        have hv_u := hu_only v hv_inc
        rw [hw_u, ←hv_u]
      revert he_edge h_only_v
      refine Quotient.inductionOn e ?_
      intro ⟨x, y⟩ he_edge h_only_v
      have hx : x = v := h_only_v x (by simp)
      have hy : y = v := h_only_v y (by simp)
      subst hx hy
      exact G.loopless v he_edge
    · exact hne rfl
  · intro u v h
    rcases h with ⟨heq, ⟨e, hloop, hinc⟩⟩ | ⟨hne, ⟨e, hinc_u, hinc_v⟩⟩
    · left; exact ⟨heq.symm, ⟨e, hloop, by rwa [heq]⟩⟩
    · right; exact ⟨hne.symm, ⟨e, hinc_v, hinc_u⟩⟩

/-- A set of vertices is a clique if every two distinct vertices in it are adjacent. -/
def IsClique (S : VSet V) : Prop :=
  forall u v : V, u ∈ S -> v ∈ S -> Not (u = v) -> G.Adj u v

/-- A set of vertices is independent if no two distinct vertices in it are adjacent. -/
def IsIndependent (S : VSet V) : Prop :=
  forall u v : V, u ∈ S -> v ∈ S -> Not (u = v) -> Not (G.Adj u v)

/-- A set of vertices is dominating if every vertex is in it or has an incoming neighbor in it. -/
def IsDominating (S : VSet V) : Prop :=
  forall v : V, v ∈ S \/ Exists (fun u : V => u ∈ S /\ G.Adj u v)

theorem empty_irreflexive (V : Type u) : (empty V).Irreflexive := by
  intro v h
  rcases h with ⟨_, ⟨e, _⟩⟩ | ⟨_, ⟨e, _⟩⟩
  · exact Empty.elim e
  · exact Empty.elim e

end Graph

end GraphMSO
