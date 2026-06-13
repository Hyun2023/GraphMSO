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

theorem eval_clique_iff {V : Type u} (G : Graph V) (rho : Assignment V) (X : SOVar) :
    Eval G rho (clique X) ↔ Graph.IsClique G (rho.so X) := by
  simp [clique, Graph.IsClique, Formula.forallFOs, Formula.notEqual, Semantics.Eval, x, y,
    Assignment.updateFO]

theorem eval_independent_iff {V : Type u} (G : Graph V) (rho : Assignment V) (X : SOVar) :
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

theorem eval_dominating_iff {V : Type u} (G : Graph V) (rho : Assignment V) (X : SOVar) :
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
  constructor
  · intro a
    simp [hasNonemptyClique, clique, Formula.forallFOs, Formula.FreeFO, Formula.notEqual,
      x, y, X]
    intro h0 h1
    exact ⟨⟨h0, h1, h0, h1⟩, h0, h1⟩
  · intro Z
    simp [hasNonemptyClique, clique, Formula.forallFOs, Formula.FreeSO, Formula.notEqual,
      x, y, X]

/-- A one-vertex type for smoke-test examples. -/
inductive One where
  | star : One
  deriving Repr, DecidableEq

def oneEmptyGraph : Graph One :=
  Graph.empty One

def allTrueAssignment : Assignment One where
  fo := fun _ => One.star
  so := fun _ => Set.univ

example : Eval oneEmptyGraph allTrueAssignment Formula.true_ := by
  exact eval_true oneEmptyGraph allTrueAssignment

example : Eval oneEmptyGraph allTrueAssignment (forallFO x (inSet x X)) := by
  intro v
  exact True.intro

end Examples

end GraphMSO
