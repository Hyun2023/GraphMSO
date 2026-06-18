import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Matching
import GraphMSO.Semantics

namespace SimpleGraph

variable {V : Type} (G : SimpleGraph V)

/-- A vertex set dominates the graph if every vertex is in it or adjacent to one of it. -/
def IsDominating (S : Set V) : Prop :=
  ∀ v : V, v ∈ S ∨ ∃ u : V, u ∈ S ∧ G.Adj u v

/-- A set covers all edges (`IsVertexCover`) iff, ranging over `G.edgeSet`, every
edge has an endpoint in it. This bridges the adjacency-based mathlib definition and
the incidence view used by MSO2 edge quantifiers. -/
theorem isVertexCover_iff_forall_edge (S : Set V) :
    G.IsVertexCover S ↔ ∀ e : G.edgeSet, ∃ v : V, v ∈ S ∧ v ∈ (e : Sym2 V) := by
  unfold SimpleGraph.IsVertexCover
  constructor
  · rintro h ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
      rcases h (G.mem_edgeSet.mp he) with ha | hb
      · exact ⟨a, ha, Sym2.mem_iff.mpr (Or.inl rfl)⟩
      · exact ⟨b, hb, Sym2.mem_iff.mpr (Or.inr rfl)⟩
  · intro h v w hvw
    obtain ⟨u, huS, hu⟩ := h ⟨s(v, w), G.mem_edgeSet.mpr hvw⟩
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · exact Or.inl huS
    · exact Or.inr huS

/-- A graph is bipartite (`IsBipartite`) iff there is a set `S` of vertices such that,
ranging over `G.edgeSet`, every edge has one endpoint in `S` and one outside it. The
witnessing parts are `S` and its complement. -/
theorem isBipartite_iff_forall_edge :
    G.IsBipartite ↔
      ∃ S : Set V, ∀ e : G.edgeSet, ∃ u v : V,
        u ∈ S ∧ v ∉ S ∧ u ∈ (e : Sym2 V) ∧ v ∈ (e : Sym2 V) := by
  rw [SimpleGraph.isBipartite_iff_exists_isBipartiteWith]
  constructor
  · rintro ⟨s, t, hdisj, hadj⟩
    refine ⟨s, ?_⟩
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
      rcases hadj (G.mem_edgeSet.mp he) with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨a, b, ha, Set.disjoint_right.mp hdisj hb,
          Sym2.mem_iff.mpr (Or.inl rfl), Sym2.mem_iff.mpr (Or.inr rfl)⟩
      · exact ⟨b, a, hb, Set.disjoint_right.mp hdisj ha,
          Sym2.mem_iff.mpr (Or.inr rfl), Sym2.mem_iff.mpr (Or.inl rfl)⟩
  · rintro ⟨S, h⟩
    refine ⟨S, Sᶜ, disjoint_compl_right, ?_⟩
    intro v w hvw
    obtain ⟨u, u', huS, hu'notS, hu, hu'⟩ := h ⟨s(v, w), G.mem_edgeSet.mpr hvw⟩
    rcases Sym2.mem_iff.mp hu with rfl | rfl <;> rcases Sym2.mem_iff.mp hu' with rfl | rfl
    · exact absurd huS hu'notS
    · exact Or.inl ⟨huS, hu'notS⟩
    · exact Or.inr ⟨hu'notS, huS⟩
    · exact absurd huS hu'notS

/-- The spanning subgraph of `G` whose edges are exactly the set `S ⊆ G.edgeSet`:
every vertex is kept, and `v, w` are adjacent precisely when the edge `s(v, w)`
belongs to `S`. -/
def spanningSubgraphOfEdges (S : Set G.edgeSet) : G.Subgraph where
  verts := Set.univ
  Adj v w := s(v, w) ∈ Subtype.val '' S
  adj_sub := by
    rintro v w ⟨e, -, he⟩
    exact G.mem_edgeSet.mp (he ▸ e.2)
  edge_vert := by intro v w _; exact Set.mem_univ v
  symm := by
    intro v w h
    rwa [Sym2.eq_swap]

@[simp]
theorem spanningSubgraphOfEdges_adj (S : Set G.edgeSet) (v w : V) :
    (G.spanningSubgraphOfEdges S).Adj v w ↔ s(v, w) ∈ Subtype.val '' S :=
  Iff.rfl

/-- The spanning subgraph carved out by an edge set `S` is a perfect matching iff,
ranging over `G.edgeSet`, every vertex is incident to exactly one edge of `S`. This
bridges mathlib's subgraph-based `IsPerfectMatching` and the incidence view used by
the MSO2 perfect-matching formula. -/
theorem isPerfectMatching_spanningSubgraphOfEdges_iff (S : Set G.edgeSet) :
    (G.spanningSubgraphOfEdges S).IsPerfectMatching ↔
      ∀ v : V, ∃! e : G.edgeSet, e ∈ S ∧ v ∈ (e : Sym2 V) := by
  rw [Subgraph.isPerfectMatching_iff]
  refine forall_congr' fun v => ?_
  simp only [spanningSubgraphOfEdges_adj]
  constructor
  · rintro ⟨w, hw, huniq⟩
    obtain ⟨e, heS, he⟩ := hw
    have hve : v ∈ (e : Sym2 V) := by rw [he]; exact Sym2.mem_iff.mpr (Or.inl rfl)
    refine ⟨e, ⟨heS, hve⟩, ?_⟩
    rintro e' ⟨he'S, hve'⟩
    have hspec : s(v, Sym2.Mem.other hve') = (e' : Sym2 V) := Sym2.other_spec hve'
    have hwoth : Sym2.Mem.other hve' = w := huniq _ ⟨e', he'S, hspec.symm⟩
    apply Subtype.ext
    rw [← hspec, hwoth, he]
  · rintro ⟨e, ⟨heS, hve⟩, huniq⟩
    have hspec : s(v, Sym2.Mem.other hve) = (e : Sym2 V) := Sym2.other_spec hve
    refine ⟨Sym2.Mem.other hve, ⟨e, heS, hspec.symm⟩, ?_⟩
    rintro w' ⟨e', he'S, he'⟩
    have hve' : v ∈ (e' : Sym2 V) := by rw [he']; exact Sym2.mem_iff.mpr (Or.inl rfl)
    have hee : e' = e := huniq e' ⟨he'S, hve'⟩
    rw [hee] at he'
    exact (Sym2.congr_right.mp (hspec.trans he')).symm

end SimpleGraph

namespace GraphMSO

namespace Examples

open Formula
open Semantics

def x : FOVar := 0
def y : FOVar := 1
def z : FOVar := 2
def X : SOVar := 0
def Y : SOVar := 1
def e0 : EdgeFOVar := 0
def e1 : EdgeFOVar := 1
def E0 : EdgeSOVar := 0

/-- "The set variable `X` is a clique." -/
def clique (X : SOVar) : Formula :=
  forallFOs [x, y]
    (impl
      (conj (inSet x X) (conj (inSet y X) (notEqual x y)))
      (edge x y))

/-- "The set variable `X` is independent." -/
def independent (X : SOVar) : Formula :=
  forallFOs [x, y]
    (impl
      (conj (inSet x X) (conj (inSet y X) (edge x y)))
      (equal x y))

/-- "The set variable `X` is a dominating set." -/
def dominating (X : SOVar) : Formula :=
  forallFO x
    (disj
      (inSet x X)
      (existsFO y (conj (inSet y X) (edge y x))))

/-- "There exists a nonempty clique." -/
def hasNonemptyClique : Formula :=
  existsSO X (conj (existsFO x (inSet x X)) (clique X))

theorem eval_clique_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    EvalAt (clique X) G rho ↔ G.IsClique (rho.so X) := by
  simp [clique, SimpleGraph.IsClique, Set.Pairwise, Formula.forallFOs, Formula.notEqual,
    Semantics.EvalAt, x, y, Assignment.updateFO]
  constructor
  · intro h u hu v hv hne
    exact h u v hu hv hne
  · intro h u v hu hv hne
    exact h hu hv hne

theorem eval_independent_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    EvalAt (independent X) G rho ↔ G.IsIndepSet (rho.so X) := by
  classical
  simp [independent, SimpleGraph.isIndepSet_iff, Set.Pairwise, Formula.forallFOs,
    Semantics.EvalAt, x, y, Assignment.updateFO]
  constructor
  · intro h u hSu v hSv hne hAdj
    exact hne (h u v hSu hSv hAdj)
  · intro h u v hSu hSv hAdj
    by_contra hne
    exact h hSu hSv hne hAdj

theorem eval_dominating_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    EvalAt (dominating X) G rho ↔ G.IsDominating (rho.so X) := by
  simp [dominating, SimpleGraph.IsDominating, Semantics.EvalAt, x, y, Assignment.updateFO]

theorem clique_no_freeFO (X : SOVar) (a : FOVar) :
    Not (Formula.FreeFO (clique X) a) := by
  simp [clique, Formula.forallFOs, Formula.FreeFO, Formula.notEqual, x, y]
  intro h0 h1
  exact ⟨⟨h0, h1, h0, h1⟩, h0, h1⟩

theorem clique_freeSO_iff (X Y : SOVar) :
    Formula.FreeSO (clique X) Y ↔ Y = X := by
  simp [clique, Formula.forallFOs, Formula.FreeSO, Formula.notEqual, x, y]

theorem hasNonemptyClique_closed : Formula.Closed hasNonemptyClique := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    simp [hasNonemptyClique, clique, Formula.forallFOs, Formula.FreeFO, Formula.notEqual, x, y, X]
    intro h0 h1
    exact ⟨⟨h0, h1, h0, h1⟩, h0, h1⟩
  · intro Z
    simp [hasNonemptyClique, clique, Formula.forallFOs, Formula.FreeSO, Formula.notEqual, x, y, X]
  · intro e
    simp [hasNonemptyClique, clique, Formula.forallFOs, Formula.FreeEdgeFO, Formula.notEqual, x, y, X]
  · intro E_var
    simp [hasNonemptyClique, clique, Formula.forallFOs, Formula.FreeEdgeSO, Formula.notEqual, x, y, X]

/-- "The edge `e` is incident to exactly one vertex." In a `SimpleGraph.edgeSet`,
this formula is unsatisfiable, but it remains useful as MSO2 syntax. -/
def isLoop (e : EdgeFOVar) : Formula :=
  existsFO y (conj (inc y e) (forallFO z (impl (inc z e) (equal z y))))

/-- "There is a unique edge in `M` incident to vertex variable `v`." -/
def uniqueIncEdgeIn (v : FOVar) (M : EdgeSOVar) : Formula :=
  existsEdgeFO e0 (conj (inEdgeSet e0 M) (conj (inc v e0)
    (forallEdgeFO e1 (impl (conj (inEdgeSet e1 M) (inc v e1)) (equalEdge e1 e0)))))

/-- "The edge set variable `M` is a perfect matching." -/
def perfectMatching (M : EdgeSOVar) : Formula :=
  conj (forallEdgeFO e0 (impl (inEdgeSet e0 M) (neg (isLoop e0))))
       (forallFO x (uniqueIncEdgeIn x M))

theorem evalAt_isLoop_false {V : Type} (e : EdgeFOVar) (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) : ¬ EvalAt (isLoop e) G rho := by
  simp [isLoop, Semantics.EvalAt, y, z]
  obtain ⟨ed, hed⟩ := rho.efo e
  induction ed using Sym2.ind with
  | _ a b =>
    have hne : a ≠ b := (G.mem_edgeSet.mp hed).ne
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact ⟨b, Sym2.mem_iff.mpr (Or.inr rfl), fun h => hne h.symm⟩
    · exact ⟨a, Sym2.mem_iff.mpr (Or.inl rfl), fun h => hne h⟩

theorem eval_perfectMatching_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (M : EdgeSOVar) :
    EvalAt (perfectMatching M) G rho ↔
      (G.spanningSubgraphOfEdges (rho.eso M)).IsPerfectMatching := by
  rw [SimpleGraph.isPerfectMatching_spanningSubgraphOfEdges_iff]
  simp [perfectMatching, uniqueIncEdgeIn, Semantics.EvalAt, x, e0, e1, evalAt_isLoop_false,
    ExistsUnique, and_assoc, -Subtype.exists]

def vertexCover (X : SOVar) : Formula :=
  forallEdgeFO e0 (existsFO x (conj (inSet x X) (inc x e0)))

theorem eval_vertexCover_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    EvalAt (vertexCover X) G rho ↔ G.IsVertexCover (rho.so X) := by
  rw [G.isVertexCover_iff_forall_edge]
  simp only [vertexCover, Semantics.EvalAt, x, e0, Assignment.updateFO, Assignment.updateEdgeFO,
    if_true]

def bipartite : Formula :=
  existsSO X (forallEdgeFO e0 (existsFO x (existsFO y
    (conj (inSet x X) (conj (neg (inSet y X)) (conj (inc x e0) (inc y e0)))))))

theorem eval_bipartite_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    EvalAt bipartite G rho ↔ G.IsBipartite := by
  rw [G.isBipartite_iff_forall_edge]
  simp [bipartite, Semantics.EvalAt, X, e0, x, y,
    Assignment.updateSO, Assignment.updateFO, Assignment.updateEdgeFO]

/-- A two-vertex type for smoke-test examples. -/
inductive Two where
  | left : Two
  | right : Two
  deriving Repr, DecidableEq

def twoGraph : SimpleGraph Two :=
  ⊤

def twoEdge : twoGraph.edgeSet :=
  ⟨s(Two.left, Two.right), by simp [twoGraph]⟩

def allTrueAssignment : Assignment Two twoGraph.edgeSet where
  fo := fun _ => Two.left
  so := fun _ => Set.univ
  efo := fun _ => twoEdge
  eso := fun _ => Set.univ

example : EvalAt Formula.true_ twoGraph allTrueAssignment := by
  exact evalAt_true twoGraph allTrueAssignment

example : Eval Formula.true_ twoGraph := by
  exact eval_true twoGraph

example : EvalAt (forallFO x (inSet x X)) twoGraph allTrueAssignment := by
  simp [Semantics.EvalAt, allTrueAssignment, x, X]

end Examples

end GraphMSO
