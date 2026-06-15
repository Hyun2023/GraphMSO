import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Basic

namespace GraphMSO

/-- Vertex sets are mathlib sets. -/
abbrev VSet (V : Type) := Set V

/-- Edge sets are mathlib sets. -/
abbrev ESet (E : Type) := Set E


/-- A bipartite incidence graph representation.
This core representation supports MSO2 by explicitly having an edge type `E`
and an incidence relation. It represents undirected multigraph-style graphs with
possible loops; directed graphs need a richer signature if orientation matters.
Each edge must connect at least one and at most two vertices. -/
structure IncidenceGraph (V E : Type) where
  inc : V -> E -> Prop
  inc_at_least_one : ∀ e : E, ∃ v : V, inc v e
  inc_at_most_two : ∀ e : E, ∃ v1 v2 : V, ∀ v : V, inc v e → v = v1 ∨ v = v2

-- `IncidenceGraph` is intended to model multigraph-like objects for MSO2.
--

namespace IncidenceGraph

variable {V E : Type} (G : IncidenceGraph V E)

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
def empty (V : Type) : IncidenceGraph V PEmpty where
  inc := fun _ _ => False
  inc_at_least_one := fun e => PEmpty.elim e
  inc_at_most_two := fun e => PEmpty.elim e

/-- View a mathlib simple graph as a `GraphMSO.IncidenceGraph`. -/
def fromSimpleGraph (G : SimpleGraph V) : IncidenceGraph V G.edgeSet where
  inc := fun v e => v ∈ e.val
  inc_at_least_one := by
    rintro ⟨e, _⟩
    change ∃ v : V, v ∈ e
    exact ⟨e.out.1, Sym2.out_fst_mem e⟩
  inc_at_most_two := by
    rintro ⟨e, _⟩
    change ∃ v1 v2 : V, ∀ v : V, v ∈ e → v = v1 ∨ v = v2
    refine Sym2.inductionOn e ?_
    intro x y
    exact ⟨x, y, fun w hw => by simpa using hw⟩

/-- Turn a `GraphMSO.IncidenceGraph` satisfying `IncidenceGraph.Simple` into a mathlib
simple graph. -/
def toSimpleGraph (hG : G.Simple) : SimpleGraph V where
  Adj := G.Adj
  symm := by
    intro u v h
    rcases h with ⟨heq, ⟨e, hloop, hinc⟩⟩ | ⟨hne, ⟨e, hinc_u, hinc_v⟩⟩
    · left
      exact ⟨heq.symm, ⟨e, hloop, by simpa [heq] using hinc⟩⟩
    · right
      exact ⟨hne.symm, ⟨e, hinc_v, hinc_u⟩⟩
  loopless := by
    intro v
    exact hG.1 v

/-- The graph obtained from a mathlib simple graph is simple. -/
theorem fromSimpleGraph_simple (G : SimpleGraph V) : (fromSimpleGraph G).Simple := by
  constructor
  · intro v h
    rcases h with ⟨_, hEdge⟩ | ⟨hne, _⟩
    · rcases hEdge with ⟨⟨e, he_edge⟩, hloop, hv_inc⟩
      rcases hloop with ⟨u, _, hu_only⟩
      have h_only_v : ∀ w, w ∈ e → w = v := by
        intro w hw
        have hw_inc : (fromSimpleGraph G).inc w ⟨e, he_edge⟩ := hw
        have hw_u := hu_only w hw_inc
        have hv_u := hu_only v hv_inc
        rw [hw_u, ←hv_u]
      have hx : e.out.1 = v := h_only_v e.out.1 (Sym2.out_fst_mem e)
      have hy : e.out.2 = v := h_only_v e.out.2 (Sym2.out_snd_mem e)
      have hout : e.out.1 = e.out.2 := hx.trans hy.symm
      have hdiag_mk : (Sym2.mk e.out).IsDiag := (Sym2.isDiag_iff_proj_eq e.out).2 hout
      have hdiag : e.IsDiag := by
        simpa [e.out_eq] using hdiag_mk
      exact G.not_isDiag_of_mem_edgeSet he_edge hdiag
    · exact hne rfl
  · intro u v h
    rcases h with ⟨heq, ⟨e, hloop, hinc⟩⟩ | ⟨hne, ⟨e, hinc_u, hinc_v⟩⟩
    · left; exact ⟨heq.symm, ⟨e, hloop, by simpa [heq] using hinc⟩⟩
    · right; exact ⟨hne.symm, ⟨e, hinc_v, hinc_u⟩⟩

/-- The complete simple graph on a vertex type. -/
def complete (V : Type) : IncidenceGraph V (⊤ : SimpleGraph V).edgeSet :=
  fromSimpleGraph ⊤

/-- Restrict a graph to vertices in a mathlib set and edges incident only to those vertices. -/
def induced (S : VSet V) :
    IncidenceGraph {v : V // v ∈ S} {e : E // ∀ v, G.inc v e → v ∈ S} where
  inc := fun v e => G.inc v.val e.val
  inc_at_least_one := by
    rintro ⟨e, he⟩
    rcases G.inc_at_least_one e with ⟨v, hv⟩
    exact ⟨⟨v, he v hv⟩, hv⟩
  inc_at_most_two := by
    rintro ⟨e, he⟩
    rcases G.inc_at_least_one e with ⟨v0, hv0⟩
    have hv0S : v0 ∈ S := he v0 hv0
    rcases G.inc_at_most_two e with ⟨v1, v2, h_most_two⟩
    classical
    let v1' : {v : V // v ∈ S} :=
      if h : G.inc v1 e then ⟨v1, he v1 h⟩ else ⟨v0, hv0S⟩
    let v2' : {v : V // v ∈ S} :=
      if h : G.inc v2 e then ⟨v2, he v2 h⟩ else ⟨v0, hv0S⟩
    use v1', v2'
    intro ⟨v, hvS⟩ h_inc
    rcases h_most_two v h_inc with (rfl | rfl)
    · left
      apply Subtype.ext
      dsimp [v1']
      rw [dif_pos h_inc]
    · right
      apply Subtype.ext
      dsimp [v2']
      rw [dif_pos h_inc]

/-- A set of vertices is a clique if every two distinct vertices in it are adjacent. -/
def IsClique (S : VSet V) : Prop :=
  forall u v : V, u ∈ S -> v ∈ S -> Not (u = v) -> G.Adj u v

/-- A set of vertices is independent if no two distinct vertices in it are adjacent. -/
def IsIndependent (S : VSet V) : Prop :=
  forall u v : V, u ∈ S -> v ∈ S -> Not (u = v) -> Not (G.Adj u v)

/-- A set of vertices is dominating if every vertex is in it or has an incoming neighbor in it. -/
def IsDominating (S : VSet V) : Prop :=
  forall v : V, v ∈ S \/ Exists (fun u : V => u ∈ S /\ G.Adj u v)

theorem empty_irreflexive (V : Type) : (empty V).Irreflexive := by
  intro v h
  rcases h with ⟨_, ⟨e, _⟩⟩ | ⟨_, ⟨e, _⟩⟩
  · exact PEmpty.elim e
  · exact PEmpty.elim e

end IncidenceGraph

end GraphMSO
