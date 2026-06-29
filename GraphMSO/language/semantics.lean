import GraphMSO.language.syntax

/-!
# MSO semantics over `τ_P`-graphs

This file gives a small Tarski semantics for the MSO1 syntax in
`GraphMSO.language.syntax`.  First-order variables range over vertices, and
second-order variables range over sets of vertices.
-/

namespace GraphMSO.Language

universe u

/-- An assignment for MSO formulas over a fixed `τ_P`-graph.

First-order variables are optional, so the empty assignment is available even
when the graph has no vertices.  Quantifiers assign concrete vertex values
before evaluating their body. -/
structure Assignment {P : Type u} (X : τPGraph P) where
  /-- First-order variables, ranging over vertices. -/
  fo : FOVar → Option X.V
  /-- Monadic second-order variables, ranging over sets of vertices. -/
  so : SOVar → Set X.V

namespace Assignment

variable {P : Type u} {X : τPGraph P}

/-- The empty assignment: no first-order variables are assigned, and every
second-order variable is interpreted as the empty set. -/
def empty (X : τPGraph P) : Assignment X where
  fo := fun _ => none
  so := fun _ => ∅

/-- Update a first-order variable. -/
def updateFO (ρ : Assignment X) (x : FOVar) (v : X.V) : Assignment X where
  fo := fun y => if y = x then some v else ρ.fo y
  so := ρ.so

/-- Update a second-order variable. -/
def updateSO (ρ : Assignment X) (Y : SOVar) (S : Set X.V) : Assignment X where
  fo := ρ.fo
  so := fun Z => if Z = Y then S else ρ.so Z

@[simp]
theorem updateFO_here (ρ : Assignment X) (x : FOVar) (v : X.V) :
    (ρ.updateFO x v).fo x = some v := by
  simp [updateFO]

@[simp]
theorem updateFO_other (ρ : Assignment X) {x y : FOVar} (v : X.V) (h : y ≠ x) :
    (ρ.updateFO x v).fo y = ρ.fo y := by
  simp [updateFO, h]

@[simp]
theorem updateFO_so (ρ : Assignment X) (x : FOVar) (v : X.V) (Y : SOVar) :
    (ρ.updateFO x v).so Y = ρ.so Y :=
  rfl

@[simp]
theorem updateSO_here (ρ : Assignment X) (Y : SOVar) (S : Set X.V) :
    (ρ.updateSO Y S).so Y = S := by
  simp [updateSO]

@[simp]
theorem updateSO_other (ρ : Assignment X) {Y Z : SOVar} (S : Set X.V) (h : Z ≠ Y) :
    (ρ.updateSO Y S).so Z = ρ.so Z := by
  simp [updateSO, h]

@[simp]
theorem updateSO_fo (ρ : Assignment X) (Y : SOVar) (S : Set X.V) (x : FOVar) :
    (ρ.updateSO Y S).fo x = ρ.fo x :=
  rfl

end Assignment

namespace Semantics

open Formula

variable {P : Type u}

/-- Tarski semantics for MSO1 formulas over a `τ_P`-graph and an assignment. -/
def SatisfiesAt (X : τPGraph P) : Formula P → Assignment X → Prop
  | false_, _ => False
  | equal x y, ρ => ∃ v : X.V, ρ.fo x = some v ∧ ρ.fo y = some v
  | adj x y, ρ =>
      ∃ u v : X.V, ρ.fo x = some u ∧ ρ.fo y = some v ∧ X.G.Adj u v
  | pred p x, ρ => ∃ v : X.V, ρ.fo x = some v ∧ X.pred p v
  | inSet x Y, ρ => ∃ v : X.V, ρ.fo x = some v ∧ v ∈ ρ.so Y
  | neg φ, ρ => ¬ SatisfiesAt X φ ρ
  | conj φ ψ, ρ => SatisfiesAt X φ ρ ∧ SatisfiesAt X ψ ρ
  | disj φ ψ, ρ => SatisfiesAt X φ ρ ∨ SatisfiesAt X ψ ρ
  | impl φ ψ, ρ => SatisfiesAt X φ ρ → SatisfiesAt X ψ ρ
  | biimpl φ ψ, ρ => SatisfiesAt X φ ρ ↔ SatisfiesAt X ψ ρ
  | existsFO x φ, ρ => ∃ v : X.V, SatisfiesAt X φ (ρ.updateFO x v)
  | forallFO x φ, ρ => ∀ v : X.V, SatisfiesAt X φ (ρ.updateFO x v)
  | existsSO Y φ, ρ => ∃ S : Set X.V, SatisfiesAt X φ (ρ.updateSO Y S)
  | forallSO Y φ, ρ => ∀ S : Set X.V, SatisfiesAt X φ (ρ.updateSO Y S)

/-- Satisfaction from the empty assignment.  This is intended for sentences. -/
def Satisfies (X : τPGraph P) (φ : Formula P) : Prop :=
  SatisfiesAt X φ (Assignment.empty X)

@[simp]
theorem not_satisfiesAt_false (X : τPGraph P) (ρ : Assignment X) :
    ¬ SatisfiesAt X false_ ρ := by
  intro h
  exact h

theorem satisfiesAt_true (X : τPGraph P) (ρ : Assignment X) :
    SatisfiesAt X (Formula.true_ : Formula P) ρ := by
  intro h
  exact h

@[simp]
theorem satisfiesAt_conj (X : τPGraph P) (ρ : Assignment X) (φ ψ : Formula P) :
    SatisfiesAt X (conj φ ψ) ρ ↔ SatisfiesAt X φ ρ ∧ SatisfiesAt X ψ ρ :=
  Iff.rfl

@[simp]
theorem satisfiesAt_disj (X : τPGraph P) (ρ : Assignment X) (φ ψ : Formula P) :
    SatisfiesAt X (disj φ ψ) ρ ↔ SatisfiesAt X φ ρ ∨ SatisfiesAt X ψ ρ :=
  Iff.rfl

@[simp]
theorem satisfiesAt_impl (X : τPGraph P) (ρ : Assignment X) (φ ψ : Formula P) :
    SatisfiesAt X (impl φ ψ) ρ ↔ (SatisfiesAt X φ ρ → SatisfiesAt X ψ ρ) :=
  Iff.rfl

@[simp]
theorem satisfiesAt_biimpl (X : τPGraph P) (ρ : Assignment X) (φ ψ : Formula P) :
    SatisfiesAt X (biimpl φ ψ) ρ ↔ (SatisfiesAt X φ ρ ↔ SatisfiesAt X ψ ρ) :=
  Iff.rfl

end Semantics

end GraphMSO.Language
