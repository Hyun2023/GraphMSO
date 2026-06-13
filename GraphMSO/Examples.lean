import GraphMSO.Semantics

namespace GraphMSO

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

/-- A one-vertex type for smoke-test examples. -/
inductive One where
  | star : One
  deriving Repr, DecidableEq

def oneEmptyGraph : Graph One :=
  Graph.empty One

def allTrueAssignment : Assignment One where
  fo := fun _ => One.star
  so := fun _ => fun _ => True

example : Eval oneEmptyGraph allTrueAssignment Formula.true_ := by
  exact eval_true oneEmptyGraph allTrueAssignment

example : Eval oneEmptyGraph allTrueAssignment (forallFO x (inSet x X)) := by
  intro v
  exact True.intro

end Examples

end GraphMSO
