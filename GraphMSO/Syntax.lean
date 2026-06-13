namespace GraphMSO

/-- First-order variables range over vertices. -/
abbrev FOVar := Nat

/-- Monadic second-order variables range over sets of vertices. -/
abbrev SOVar := Nat

/-- Syntax for monadic second-order logic over the graph signature.

Terms are just first-order variables. The only graph-specific atomic formula is
`edge x y`; `inSet x X` is the monadic second-order membership atom. The syntax
uses named numeric variables, so binders shadow by updating assignments. -/
inductive Formula where
  | false_ : Formula
  | equal : FOVar -> FOVar -> Formula
  | edge : FOVar -> FOVar -> Formula
  | inSet : FOVar -> SOVar -> Formula
  | neg : Formula -> Formula
  | conj : Formula -> Formula -> Formula
  | disj : Formula -> Formula -> Formula
  | impl : Formula -> Formula -> Formula
  | biimpl : Formula -> Formula -> Formula
  | existsFO : FOVar -> Formula -> Formula
  | forallFO : FOVar -> Formula -> Formula
  | existsSO : SOVar -> Formula -> Formula
  | forallSO : SOVar -> Formula -> Formula
  deriving Repr, DecidableEq

namespace Formula

def true_ : Formula :=
  neg false_

def notEqual (x y : FOVar) : Formula :=
  neg (equal x y)

def subset (X Y : SOVar) : Formula :=
  forallFO 0 (impl (inSet 0 X) (inSet 0 Y))

def setEq (X Y : SOVar) : Formula :=
  conj (subset X Y) (subset Y X)

/-- First-order variables occurring free in a formula. -/
def FreeFO : Formula -> FOVar -> Prop
  | false_, _ => False
  | equal y z, x => x = y \/ x = z
  | edge y z, x => x = y \/ x = z
  | inSet y _, x => x = y
  | neg phi, x => FreeFO phi x
  | conj phi psi, x => FreeFO phi x \/ FreeFO psi x
  | disj phi psi, x => FreeFO phi x \/ FreeFO psi x
  | impl phi psi, x => FreeFO phi x \/ FreeFO psi x
  | biimpl phi psi, x => FreeFO phi x \/ FreeFO psi x
  | existsFO y phi, x => x ≠ y /\ FreeFO phi x
  | forallFO y phi, x => x ≠ y /\ FreeFO phi x
  | existsSO _ phi, x => FreeFO phi x
  | forallSO _ phi, x => FreeFO phi x

/-- Second-order variables occurring free in a formula. -/
def FreeSO : Formula -> SOVar -> Prop
  | false_, _ => False
  | equal _ _, _ => False
  | edge _ _, _ => False
  | inSet _ Y, X => X = Y
  | neg phi, X => FreeSO phi X
  | conj phi psi, X => FreeSO phi X \/ FreeSO psi X
  | disj phi psi, X => FreeSO phi X \/ FreeSO psi X
  | impl phi psi, X => FreeSO phi X \/ FreeSO psi X
  | biimpl phi psi, X => FreeSO phi X \/ FreeSO psi X
  | existsFO _ phi, X => FreeSO phi X
  | forallFO _ phi, X => FreeSO phi X
  | existsSO Y phi, X => X ≠ Y /\ FreeSO phi X
  | forallSO Y phi, X => X ≠ Y /\ FreeSO phi X

/-- A closed formula has no free first-order or second-order variables. -/
def Closed (phi : Formula) : Prop :=
  (forall x, Not (FreeFO phi x)) /\ (forall X, Not (FreeSO phi X))

/-- Existential first-order quantification over a list of variables. -/
def existsFOs : List FOVar -> Formula -> Formula
  | [], phi => phi
  | x :: xs, phi => existsFO x (existsFOs xs phi)

/-- Universal first-order quantification over a list of variables. -/
def forallFOs : List FOVar -> Formula -> Formula
  | [], phi => phi
  | x :: xs, phi => forallFO x (forallFOs xs phi)

end Formula

end GraphMSO
