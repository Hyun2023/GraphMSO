import GraphMSO.language.tau_graph

/-!
# MSO syntax over `τ_P`

This file gives a small MSO1 syntax for the vocabulary `τ_P = {adj} ∪ P`.
There are no edge variables here: first-order variables range over vertices,
and second-order variables range over sets of vertices.
-/

namespace GraphMSO.Language

universe u

/-- First-order variables range over vertices. -/
abbrev FOVar := Nat

/-- Monadic second-order variables range over sets of vertices. -/
abbrev SOVar := Nat

/-- MSO formulas over the unary-expanded graph vocabulary `τ_P`.

The graph-specific atoms are `adj x y` and `pred p x`; membership `inSet x X`
is the monadic second-order atom saying that vertex variable `x` belongs to the
set variable `X`. -/
inductive Formula (P : Type u) where
  | false_ : Formula P
  | equal : FOVar → FOVar → Formula P
  | adj : FOVar → FOVar → Formula P
  | pred : P → FOVar → Formula P
  | inSet : FOVar → SOVar → Formula P
  | neg : Formula P → Formula P
  | conj : Formula P → Formula P → Formula P
  | disj : Formula P → Formula P → Formula P
  | impl : Formula P → Formula P → Formula P
  | biimpl : Formula P → Formula P → Formula P
  | existsFO : FOVar → Formula P → Formula P
  | forallFO : FOVar → Formula P → Formula P
  | existsSO : SOVar → Formula P → Formula P
  | forallSO : SOVar → Formula P → Formula P
  deriving Repr, DecidableEq

namespace Formula

variable {P : Type u}

/-- Truth, defined from falsity. -/
def true_ : Formula P :=
  neg false_

/-- Inequality of first-order variables. -/
def notEqual (x y : FOVar) : Formula P :=
  neg (equal x y)

/-- `X ⊆ Y`, expressed in MSO syntax. -/
def subset (X Y : SOVar) : Formula P :=
  forallFO 0 (impl (inSet 0 X) (inSet 0 Y))

/-- Extensional equality of second-order variables. -/
def setEq (X Y : SOVar) : Formula P :=
  conj (subset X Y) (subset Y X)

end Formula

end GraphMSO.Language
