import GraphMSO.Automata.binTree
import GraphMSO.treeLanguage.modelIso

/-!
# Relabeling executable tree models

The executable sigma alphabet is decoded into the proof-facing sigma
alphabet node by node.  This file supplies the general logical bridge for
that operation: pulling a formula back along a label map is equivalent to
evaluating the original formula after relabeling the model.
-/

namespace GraphMSO.TreeLanguage

universe u v w

namespace Formula

/-- Pull every label predicate back along a map of alphabets. -/
def comapLabels {A : Type u} {B : Type v} (f : A → B) :
    Formula B → Formula A
  | .false_ => .false_
  | .equal x y => .equal x y
  | .parent y x => .parent y x
  | .labelMem S x => .labelMem {a | f a ∈ S} x
  | .labelMem₂ R x y => .labelMem₂ {p | (f p.1, f p.2) ∈ R} x y
  | .inSet x X => .inSet x X
  | .neg φ => .neg (comapLabels f φ)
  | .conj φ ψ => .conj (comapLabels f φ) (comapLabels f ψ)
  | .disj φ ψ => .disj (comapLabels f φ) (comapLabels f ψ)
  | .impl φ ψ => .impl (comapLabels f φ) (comapLabels f ψ)
  | .biimpl φ ψ => .biimpl (comapLabels f φ) (comapLabels f ψ)
  | .existsFO x φ => .existsFO x (comapLabels f φ)
  | .forallFO x φ => .forallFO x (comapLabels f φ)
  | .existsSO X φ => .existsSO X (comapLabels f φ)
  | .forallSO X φ => .forallSO X (comapLabels f φ)

end Formula

namespace TreeModel

/-- Relabel a model without changing its node type or parent relation. -/
def mapLabels {A : Type u} {B : Type v} (f : A → B) (M : TreeModel A) :
    TreeModel B where
  Node := M.Node
  parentRel := M.parentRel
  label := fun n => f (M.label n)

end TreeModel

namespace Assignment

variable {A : Type u} {B : Type v} {M : TreeModel A}

/-- Reuse an assignment after changing only the model's label alphabet. -/
def mapLabels (f : A → B) (ρ : Assignment M) : Assignment (M.mapLabels f) where
  fo := ρ.fo
  so := ρ.so

@[simp] theorem mapLabels_updateFO (f : A → B) (ρ : Assignment M)
    (x : FOVar) (n : M.Node) :
    (ρ.updateFO x n).mapLabels f = (ρ.mapLabels f).updateFO x n :=
  rfl

@[simp] theorem mapLabels_updateSO (f : A → B) (ρ : Assignment M)
    (X : SOVar) (S : Set M.Node) :
    (ρ.updateSO X S).mapLabels f = (ρ.mapLabels f).updateSO X S :=
  rfl

end Assignment

namespace Semantics

variable {A : Type u} {B : Type v}

/-- Formula pullback is correct for a model relabeled on the same nodes. -/
theorem satisfiesAt_mapLabels_iff (f : A → B) (M : TreeModel A)
    (φ : Formula B) (ρ : Assignment M) :
    SatisfiesAt (M.mapLabels f) φ (ρ.mapLabels f) ↔
      SatisfiesAt M (φ.comapLabels f) ρ := by
  induction φ generalizing ρ with
  | false_ => rfl
  | equal x y => rfl
  | parent y x => rfl
  | labelMem S x => rfl
  | labelMem₂ R x y => rfl
  | inSet x X => rfl
  | neg φ ih => exact not_congr (ih ρ)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ ρ) (ihψ ρ)
  | disj φ ψ ihφ ihψ => exact or_congr (ihφ ρ) (ihψ ρ)
  | impl φ ψ ihφ ihψ => exact imp_congr (ihφ ρ) (ihψ ρ)
  | biimpl φ ψ ihφ ihψ => exact iff_congr (ihφ ρ) (ihψ ρ)
  | existsFO x φ ih =>
      exact exists_congr fun n => by
        rw [← Assignment.mapLabels_updateFO]
        exact ih (ρ.updateFO x n)
  | forallFO x φ ih =>
      exact forall_congr' fun n => by
        rw [← Assignment.mapLabels_updateFO]
        exact ih (ρ.updateFO x n)
  | existsSO X φ ih =>
      exact exists_congr fun S => by
        rw [← Assignment.mapLabels_updateSO]
        exact ih (ρ.updateSO X S)
  | forallSO X φ ih =>
      exact forall_congr' fun S => by
        rw [← Assignment.mapLabels_updateSO]
        exact ih (ρ.updateSO X S)

/-- Sentence-level form of `satisfiesAt_mapLabels_iff`. -/
theorem satisfies_mapLabels_iff (f : A → B) (M : TreeModel A)
    (φ : Formula B) :
    Satisfies (M.mapLabels f) φ ↔ Satisfies M (φ.comapLabels f) := by
  change
    SatisfiesAt (M.mapLabels f) φ (Assignment.empty (M.mapLabels f)) ↔
      SatisfiesAt M (φ.comapLabels f) (Assignment.empty M)
  have hempty :
      (Assignment.empty M).mapLabels f = Assignment.empty (M.mapLabels f) :=
    rfl
  rw [← hempty]
  exact satisfiesAt_mapLabels_iff f M φ (Assignment.empty M)

end Semantics

end GraphMSO.TreeLanguage

namespace BinTree

universe u v

variable {A : Type u} {B : Type v}

/-- Mapping a binary tree's labels realizes `TreeModel.mapLabels`, up to the
canonical equivalence of recursively defined position types. -/
def mapModelIso (f : A → B) (t : BinTree A) :
    (t.toTreeModel.mapLabels f).Iso (t.map f).toTreeModel where
  toEquiv := posEquivMap f t
  parentRel_iff := by
    intro p q
    change
      ((t.map f).childRel false (posEquivMap f t p) (posEquivMap f t q) ∨
          (t.map f).childRel true (posEquivMap f t p) (posEquivMap f t q)) ↔
        (t.childRel false p q ∨ t.childRel true p q)
    exact or_congr (childRel_map_iff f false t p q)
      (childRel_map_iff f true t p q)
  label_eq := labelAt_map f t

namespace Semantics

open GraphMSO.TreeLanguage

/-- Satisfaction on a relabeled binary tree is satisfaction of the pulled
back formula on the source tree. -/
theorem satisfies_map_iff (f : A → B) (t : BinTree A)
    (φ : Formula B) :
    Semantics.Satisfies (t.map f).toTreeModel φ ↔
      Semantics.Satisfies t.toTreeModel (φ.comapLabels f) := by
  rw [Semantics.satisfies_iff_of_iso (mapModelIso f t)]
  exact Semantics.satisfies_mapLabels_iff f t.toTreeModel φ

end Semantics

end BinTree
