import GraphMSO.Semantics

namespace GraphMSO

universe u

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

/-- "The set variable `X` is a clique." Intended for simple undirected graphs. -/
def clique (X : SOVar) : Formula :=
  forallFOs [x, y]
    (impl
      (conj (inSet x X) (conj (inSet y X) (notEqual x y)))
      (edge x y))

/-- "The set variable `X` is independent." Intended for simple undirected graphs. -/
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

theorem eval_clique_iff {V E : Type u} (G : Graph V E) (rho : Assignment V E) (X : SOVar) :
    Eval G rho (clique X) ↔ Graph.IsClique G (rho.so X) := by
  simp [clique, Graph.IsClique, Formula.forallFOs, Formula.notEqual, Semantics.Eval, x, y,
    Assignment.updateFO]

theorem eval_independent_iff {V E : Type u} (G : Graph V E) (rho : Assignment V E) (X : SOVar) :
    Eval G rho (independent X) ↔ Graph.IsIndependent G (rho.so X) := by
  classical
  simp [independent, Graph.IsIndependent, Formula.forallFOs, Semantics.Eval, x, y,
    Assignment.updateFO]
  constructor
  · intro h u v hSu hSv hne hAdj
    exact hne (h u v hSu hSv hAdj)
  · intro h u v hSu hSv hAdj
    by_cases hEq : u = v
    · exact hEq
    · exfalso
      exact h u v hSu hSv hEq hAdj

theorem eval_dominating_iff {V E : Type u} (G : Graph V E) (rho : Assignment V E) (X : SOVar) :
    Eval G rho (dominating X) ↔ Graph.IsDominating G (rho.so X) := by
  simp [dominating, Graph.IsDominating, Semantics.Eval, x, y, Assignment.updateFO]

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

/-- "The subset `M` of edges is a perfect matching." -/
def uniqueIncEdgeIn (v : FOVar) (M : EdgeSOVar) : Formula :=
  existsEdgeFO e0 (conj (inEdgeSet e0 M) (conj (inc v e0)
    (forallEdgeFO e1 (impl (conj (inEdgeSet e1 M) (inc v e1)) (equalEdge e1 e0)))))

def perfectMatching (M : EdgeSOVar) : Formula :=
  forallFO x (uniqueIncEdgeIn x M)

def Graph.HasPerfectMatching {V E : Type u} (G : Graph V E) (M : ESet E) : Prop :=
  ∀ v : V, ∃! e : E, e ∈ M ∧ G.inc v e

theorem eval_perfectMatching_iff {V E : Type u} (G : Graph V E) (rho : Assignment V E) (M : EdgeSOVar) :
    Eval G rho (perfectMatching M) ↔ Graph.HasPerfectMatching G (rho.eso M) := by
  simp [perfectMatching, uniqueIncEdgeIn, Graph.HasPerfectMatching, Semantics.Eval, x, e0, e1, ExistsUnique,
    Assignment.updateFO, Assignment.updateEdgeFO]

/-- A one-vertex type for smoke-test examples. -/
inductive One where
  | star : One
  deriving Repr, DecidableEq

def oneEmptyGraph : Graph One Empty :=
  Graph.empty One

def allTrueAssignment : Assignment One Empty where
  fo := fun _ => One.star
  so := fun _ => Set.univ
  efo := fun e => Empty.elim e
  eso := fun _ => Set.univ

example : Eval oneEmptyGraph allTrueAssignment Formula.true_ := by
  exact eval_true oneEmptyGraph allTrueAssignment

example : Eval oneEmptyGraph allTrueAssignment (forallFO x (inSet x X)) := by
  intro v
  exact True.intro

end Examples

end GraphMSO
