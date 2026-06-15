import Mathlib.Combinatorics.SimpleGraph.Clique
import GraphMSO.Semantics

namespace SimpleGraph

variable {V : Type} (G : SimpleGraph V)

/-- A vertex set is independent if no two distinct vertices in it are adjacent. -/
def IsIndependent (S : Set V) : Prop :=
  ∀ u v : V, u ∈ S -> v ∈ S -> u ≠ v -> ¬ G.Adj u v

/-- A vertex set dominates the graph if every vertex is in it or adjacent to one of it. -/
def IsDominating (S : Set V) : Prop :=
  ∀ v : V, v ∈ S ∨ ∃ u : V, u ∈ S ∧ G.Adj u v

/-- A vertex set covers all edges if every edge has an endpoint in it. -/
def IsVertexCover (S : Set V) : Prop :=
  ∀ e : G.edgeSet, ∃ v : V, v ∈ S ∧ v ∈ (e : Sym2 V)

/-- Edge-based bipartiteness, phrased to match the MSO2 formula directly. -/
def IsBipartiteByEdges : Prop :=
  ∃ S : Set V,
    ∀ e : G.edgeSet, ∃ u v : V,
      u ∈ S ∧ v ∉ S ∧ u ∈ (e : Sym2 V) ∧ v ∈ (e : Sym2 V)

/-- A perfect matching is an edge set incident to each vertex at exactly one edge. -/
def HasPerfectMatching (M : Set G.edgeSet) : Prop :=
  ∀ v : V, ∃! e : G.edgeSet, e ∈ M ∧ v ∈ (e : Sym2 V)

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
    EvalAt (independent X) G rho ↔ G.IsIndependent (rho.so X) := by
  classical
  simp [independent, SimpleGraph.IsIndependent, Formula.forallFOs, Semantics.EvalAt, x, y,
    Assignment.updateFO]
  constructor
  · intro h u v hSu hSv hne hAdj
    exact hne (h u v hSu hSv hAdj)
  · intro h u v hSu hSv hAdj
    by_contra hne
    exact h u v hSu hSv hne hAdj

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

def vertexCover (X : SOVar) : Formula :=
  forallEdgeFO e0 (existsFO x (conj (inSet x X) (inc x e0)))

theorem eval_vertexCover_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    EvalAt (vertexCover X) G rho ↔ G.IsVertexCover (rho.so X) := by
  simp [vertexCover, SimpleGraph.IsVertexCover, Semantics.EvalAt, x, e0,
    Assignment.updateFO, Assignment.updateEdgeFO]

def bipartite : Formula :=
  existsSO X (forallEdgeFO e0 (existsFO x (existsFO y
    (conj (inSet x X) (conj (neg (inSet y X)) (conj (inc x e0) (inc y e0)))))))

theorem eval_bipartite_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    EvalAt bipartite G rho ↔ G.IsBipartiteByEdges := by
  simp [bipartite, SimpleGraph.IsBipartiteByEdges, Semantics.EvalAt, X, e0, x, y,
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
