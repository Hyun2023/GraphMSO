namespace GraphMSO

/-- First-order variables range over vertices. -/
abbrev FOVar := Nat

/-- Monadic second-order variables range over sets of vertices. -/
abbrev SOVar := Nat

/-- First-order edge variables range over edges. -/
abbrev EdgeFOVar := Nat

/-- Monadic second-order edge variables range over sets of edges. -/
abbrev EdgeSOVar := Nat

/-- Syntax for monadic second-order logic over the graph signature.

Terms are just first-order variables. The only graph-specific atomic formula is
`edge x y`; `inSet x X` is the monadic second-order membership atom. The syntax
uses named numeric variables, so binders shadow by updating assignments. -/
inductive Formula where
  | false_ : Formula
  | equal : FOVar -> FOVar -> Formula
  | edge : FOVar -> FOVar -> Formula
  | inSet : FOVar -> SOVar -> Formula
  | equalEdge : EdgeFOVar -> EdgeFOVar -> Formula
  | inc : FOVar -> EdgeFOVar -> Formula
  | inEdgeSet : EdgeFOVar -> EdgeSOVar -> Formula
  | neg : Formula -> Formula
  | conj : Formula -> Formula -> Formula
  | disj : Formula -> Formula -> Formula
  | impl : Formula -> Formula -> Formula
  | biimpl : Formula -> Formula -> Formula
  | existsFO : FOVar -> Formula -> Formula
  | forallFO : FOVar -> Formula -> Formula
  | existsSO : SOVar -> Formula -> Formula
  | forallSO : SOVar -> Formula -> Formula
  | existsEdgeFO : EdgeFOVar -> Formula -> Formula
  | forallEdgeFO : EdgeFOVar -> Formula -> Formula
  | existsEdgeSO : EdgeSOVar -> Formula -> Formula
  | forallEdgeSO : EdgeSOVar -> Formula -> Formula
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
  | equalEdge _ _, _ => False
  | inc y _, x => x = y
  | inEdgeSet _ _, _ => False
  | neg phi, x => FreeFO phi x
  | conj phi psi, x => FreeFO phi x \/ FreeFO psi x
  | disj phi psi, x => FreeFO phi x \/ FreeFO psi x
  | impl phi psi, x => FreeFO phi x \/ FreeFO psi x
  | biimpl phi psi, x => FreeFO phi x \/ FreeFO psi x
  | existsFO y phi, x => x ≠ y /\ FreeFO phi x
  | forallFO y phi, x => x ≠ y /\ FreeFO phi x
  | existsSO _ phi, x => FreeFO phi x
  | forallSO _ phi, x => FreeFO phi x
  | existsEdgeFO _ phi, x => FreeFO phi x
  | forallEdgeFO _ phi, x => FreeFO phi x
  | existsEdgeSO _ phi, x => FreeFO phi x
  | forallEdgeSO _ phi, x => FreeFO phi x

/-- Second-order variables occurring free in a formula. -/
def FreeSO : Formula -> SOVar -> Prop
  | false_, _ => False
  | equal _ _, _ => False
  | edge _ _, _ => False
  | inSet _ Y, X => X = Y
  | equalEdge _ _, _ => False
  | inc _ _, _ => False
  | inEdgeSet _ _, _ => False
  | neg phi, X => FreeSO phi X
  | conj phi psi, X => FreeSO phi X \/ FreeSO psi X
  | disj phi psi, X => FreeSO phi X \/ FreeSO psi X
  | impl phi psi, X => FreeSO phi X \/ FreeSO psi X
  | biimpl phi psi, X => FreeSO phi X \/ FreeSO psi X
  | existsFO _ phi, X => FreeSO phi X
  | forallFO _ phi, X => FreeSO phi X
  | existsSO Y phi, X => X ≠ Y /\ FreeSO phi X
  | forallSO Y phi, X => X ≠ Y /\ FreeSO phi X
  | existsEdgeFO _ phi, X => FreeSO phi X
  | forallEdgeFO _ phi, X => FreeSO phi X
  | existsEdgeSO _ phi, X => FreeSO phi X
  | forallEdgeSO _ phi, X => FreeSO phi X

/-- First-order edge variables occurring free in a formula. -/
def FreeEdgeFO : Formula -> EdgeFOVar -> Prop
  | false_, _ => False
  | equal _ _, _ => False
  | edge _ _, _ => False
  | inSet _ _, _ => False
  | equalEdge y z, x => x = y \/ x = z
  | inc _ y, x => x = y
  | inEdgeSet y _, x => x = y
  | neg phi, x => FreeEdgeFO phi x
  | conj phi psi, x => FreeEdgeFO phi x \/ FreeEdgeFO psi x
  | disj phi psi, x => FreeEdgeFO phi x \/ FreeEdgeFO psi x
  | impl phi psi, x => FreeEdgeFO phi x \/ FreeEdgeFO psi x
  | biimpl phi psi, x => FreeEdgeFO phi x \/ FreeEdgeFO psi x
  | existsFO _ phi, x => FreeEdgeFO phi x
  | forallFO _ phi, x => FreeEdgeFO phi x
  | existsSO _ phi, x => FreeEdgeFO phi x
  | forallSO _ phi, x => FreeEdgeFO phi x
  | existsEdgeFO y phi, x => x ≠ y /\ FreeEdgeFO phi x
  | forallEdgeFO y phi, x => x ≠ y /\ FreeEdgeFO phi x
  | existsEdgeSO _ phi, x => FreeEdgeFO phi x
  | forallEdgeSO _ phi, x => FreeEdgeFO phi x

/-- Second-order edge variables occurring free in a formula. -/
def FreeEdgeSO : Formula -> EdgeSOVar -> Prop
  | false_, _ => False
  | equal _ _, _ => False
  | edge _ _, _ => False
  | inSet _ _, _ => False
  | equalEdge _ _, _ => False
  | inc _ _, _ => False
  | inEdgeSet _ Y, X => X = Y
  | neg phi, X => FreeEdgeSO phi X
  | conj phi psi, X => FreeEdgeSO phi X \/ FreeEdgeSO psi X
  | disj phi psi, X => FreeEdgeSO phi X \/ FreeEdgeSO psi X
  | impl phi psi, X => FreeEdgeSO phi X \/ FreeEdgeSO psi X
  | biimpl phi psi, X => FreeEdgeSO phi X \/ FreeEdgeSO psi X
  | existsFO _ phi, X => FreeEdgeSO phi X
  | forallFO _ phi, X => FreeEdgeSO phi X
  | existsSO _ phi, X => FreeEdgeSO phi X
  | forallSO _ phi, X => FreeEdgeSO phi X
  | existsEdgeFO _ phi, X => FreeEdgeSO phi X
  | forallEdgeFO _ phi, X => FreeEdgeSO phi X
  | existsEdgeSO Y phi, X => X ≠ Y /\ FreeEdgeSO phi X
  | forallEdgeSO Y phi, X => X ≠ Y /\ FreeEdgeSO phi X

/-- A closed formula has no free first-order or second-order variables. -/
def Closed (phi : Formula) : Prop :=
  (forall x, Not (FreeFO phi x)) /\ (forall X, Not (FreeSO phi X)) /\
  (forall e, Not (FreeEdgeFO phi e)) /\ (forall E, Not (FreeEdgeSO phi E))

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
