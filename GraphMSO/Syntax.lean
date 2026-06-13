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
