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

/-- The free first-order variables of a formula. -/
def freeFO : Formula P → Set FOVar
  | false_ => ∅
  | equal x y => {x, y}
  | adj x y => {x, y}
  | pred _ x => {x}
  | inSet x _ => {x}
  | neg φ => φ.freeFO
  | conj φ ψ => φ.freeFO ∪ ψ.freeFO
  | disj φ ψ => φ.freeFO ∪ ψ.freeFO
  | impl φ ψ => φ.freeFO ∪ ψ.freeFO
  | biimpl φ ψ => φ.freeFO ∪ ψ.freeFO
  | existsFO x φ => φ.freeFO \ {x}
  | forallFO x φ => φ.freeFO \ {x}
  | existsSO _ φ => φ.freeFO
  | forallSO _ φ => φ.freeFO

/-- The free second-order variables of a formula. -/
def freeSO : Formula P → Set SOVar
  | false_ => ∅
  | equal _ _ => ∅
  | adj _ _ => ∅
  | pred _ _ => ∅
  | inSet _ X => {X}
  | neg φ => φ.freeSO
  | conj φ ψ => φ.freeSO ∪ ψ.freeSO
  | disj φ ψ => φ.freeSO ∪ ψ.freeSO
  | impl φ ψ => φ.freeSO ∪ ψ.freeSO
  | biimpl φ ψ => φ.freeSO ∪ ψ.freeSO
  | existsFO _ φ => φ.freeSO
  | forallFO _ φ => φ.freeSO
  | existsSO X φ => φ.freeSO \ {X}
  | forallSO X φ => φ.freeSO \ {X}

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
