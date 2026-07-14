import GraphMSO.Decomp.sigmaTree
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.DeriveFintype

/-!
# Executable sigma letters

This file gives the finite Boolean-table representation of a sigma letter used
by the executable model checker.  `ExecSigmaLetter.decode` connects it to the
proof-facing `SigmaLetter` representation.
-/

universe u

/-- A sigma letter represented entirely by finite Boolean lookup tables. -/
structure ExecSigmaLetter (P : Type u) (omega : ℕ) where
  present : Fin (omega + 1) → Bool
  root : Fin (omega + 1) → Bool
  adj : Fin (omega + 1) → Fin (omega + 1) → Bool
  tag : P → Fin (omega + 1) → Bool

instance instFintype {P : Type u} {omega : Nat} [Fintype P] [DecidableEq P] :
    Fintype (ExecSigmaLetter P omega) := by
  let Color := Fin (omega + 1)
  letI : Fintype (Color → Bool) := Pi.instFintype
  letI : Fintype (Color → Color → Bool) := Pi.instFintype
  letI : Fintype (P → Color → Bool) := Pi.instFintype
  exact derive_fintype% ExecSigmaLetter P omega

instance instDecidableEq {P : Type u} {omega : Nat} [Fintype P] [DecidableEq P] :
    DecidableEq (ExecSigmaLetter P omega) := by
  intro A B
  cases A with
  | mk presentA rootA adjA tagA =>
      cases B with
      | mk presentB rootB adjB tagB =>
          exact decidable_of_iff
            (presentA = presentB ∧ rootA = rootB ∧ adjA = adjB ∧ tagA = tagB)
            (by simp)

namespace ExecSigmaLetter

variable {P : Type u} {omega : ℕ}

/-- Boolean universal search over a finite set. -/
def finsetAll {A : Type*} [DecidableEq A]
    (s : Finset A) (p : A → Bool) : Bool :=
  s.fold Bool.and true p

theorem finsetAll_eq_true_iff {A : Type*} [DecidableEq A]
    (s : Finset A) (p : A → Bool) :
    finsetAll s p = true ↔ ∀ a ∈ s, p a = true := by
  induction s using Finset.induction_on with
  | empty => simp [finsetAll]
  | @insert a s ha ih =>
      rw [finsetAll, Finset.fold_insert ha, Bool.and_eq_true]
      change (p a = true ∧ finsetAll s p = true) ↔ _
      rw [ih]
      simp

/-- A finite Boolean universal quantifier. -/
def allFintype {A : Type*} [Fintype A] [DecidableEq A] (p : A → Bool) : Bool :=
  finsetAll Finset.univ p

@[simp] theorem allFintype_eq_true {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → Bool) :
    allFintype p = true ↔ ∀ a, p a = true := by
  simp [allFintype, finsetAll_eq_true_iff]

/-- Boolean implication. -/
def boolImp (a b : Bool) : Bool :=
  !a || b

@[simp] theorem boolImp_eq_true (a b : Bool) :
    boolImp a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp [boolImp]

/-- Boolean equivalence. -/
def boolIff (a b : Bool) : Bool :=
  decide (a = b)

@[simp] theorem boolIff_eq_true (a b : Bool) :
    boolIff a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp [boolIff]

/-- Decode a Boolean table into the proof-facing sigma-letter structure.

The stored adjacency table is symmetrized, and diagonal entries are discarded,
so the resulting relation is a simple graph regardless of the input table. -/
def decode (A : ExecSigmaLetter P omega) : SigmaLetter P omega where
  verts := {i | A.present i = true}
  G :=
    { Adj := fun i j =>
        i.1 ≠ j.1 ∧ (A.adj i.1 j.1 || A.adj j.1 i.1) = true
      symm := by
        rintro i j ⟨hij, hadj⟩
        exact ⟨hij.symm, by simpa [Bool.or_comm] using hadj⟩
      loopless := by
        rintro i ⟨hii, -⟩
        exact hii rfl }
  R := {i | A.root i.1 = true}
  tag := fun p i => A.tag p i.1 = true

/-- Whether a color is present in the letter. -/
def hasVertex (A : ExecSigmaLetter P omega) (i : BagColorSet omega) : Bool :=
  A.present i

/-- Whether a present color belongs to the root/boundary. -/
def rootContains (A : ExecSigmaLetter P omega) (i : BagColorSet omega) : Bool :=
  A.present i && A.root i

/-- Whether two present, distinct colors are adjacent. -/
def adjOnColors (A : ExecSigmaLetter P omega)
    (i j : BagColorSet omega) : Bool :=
  A.present i && A.present j && decide (i ≠ j) && (A.adj i j || A.adj j i)

/-- Whether a unary predicate tag holds at a present color. -/
def tagOnColor (A : ExecSigmaLetter P omega)
    (p : P) (i : BagColorSet omega) : Bool :=
  A.present i && A.tag p i

/-- Whether no present color is marked as a root/boundary color. -/
def rootEmpty (A : ExecSigmaLetter P omega) : Bool :=
  allFintype fun i => !(A.present i && A.root i)

/-- Executable compatibility of a child letter with its parent letter. -/
def compatible [Fintype P] [DecidableEq P]
    (child parent : ExecSigmaLetter P omega) : Bool :=
  (allFintype fun i => boolImp (child.rootContains i) (parent.hasVertex i)) &&
    (allFintype fun i => allFintype fun j =>
      boolImp (child.rootContains i)
        (boolImp (child.rootContains j)
          (boolIff (child.adjOnColors i j) (parent.adjOnColors i j)))) &&
    (allFintype fun p => allFintype fun i =>
      boolImp (child.rootContains i)
        (boolIff (child.tagOnColor p i) (parent.tagOnColor p i)))

@[simp] theorem hasVertex_eq_true_iff
    (A : ExecSigmaLetter P omega) (i : BagColorSet omega) :
    A.hasVertex i = true ↔ A.decode.HasVertex i :=
  Iff.rfl

@[simp] theorem rootContains_eq_true_iff
    (A : ExecSigmaLetter P omega) (i : BagColorSet omega) :
    A.rootContains i = true ↔ A.decode.RootContains i := by
  simp [rootContains, decode, SigmaLetter.RootContains]

@[simp] theorem adjOnColors_eq_true_iff
    (A : ExecSigmaLetter P omega) (i j : BagColorSet omega) :
    A.adjOnColors i j = true ↔ A.decode.AdjOnColors i j := by
  simp only [adjOnColors, decode, SigmaLetter.AdjOnColors, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨⟨hi, hj⟩, hne⟩, hadj⟩
    exact ⟨hi, hj, hne, hadj⟩
  · rintro ⟨hi, hj, hne, hadj⟩
    exact ⟨⟨⟨hi, hj⟩, hne⟩, hadj⟩

@[simp] theorem tagOnColor_eq_true_iff
    (A : ExecSigmaLetter P omega) (p : P) (i : BagColorSet omega) :
    A.tagOnColor p i = true ↔ A.decode.TagOnColor p i := by
  simp [tagOnColor, decode, SigmaLetter.TagOnColor]

@[simp] theorem rootEmpty_eq_true_iff (A : ExecSigmaLetter P omega) :
    A.rootEmpty = true ↔ A.decode.RootEmpty := by
  rw [rootEmpty, allFintype_eq_true, SigmaLetter.RootEmpty,
    Set.eq_empty_iff_forall_notMem]
  change
    (∀ i, (!(A.present i && A.root i)) = true) ↔
      ∀ i : {i | A.present i = true}, ¬A.root i.1 = true
  constructor
  · intro h i
    cases hr : A.root i.1 with
    | false => simp
    | true =>
        have hi := h i.1
        rw [i.2, hr] at hi
        simp at hi
  · intro h i
    by_cases hp : A.present i = true
    · have hr : A.root i = false :=
        Bool.eq_false_of_not_eq_true (h ⟨i, hp⟩)
      simp [hp, hr]
    · have hp' : A.present i = false := Bool.eq_false_of_not_eq_true hp
      simp [hp']

@[simp] theorem compatible_eq_true_iff [Fintype P] [DecidableEq P]
    (child parent : ExecSigmaLetter P omega) :
    child.compatible parent = true ↔
      SigmaLetter.Compatible child.decode parent.decode := by
  simp only [compatible, Bool.and_eq_true, allFintype_eq_true,
    boolImp_eq_true, boolIff_eq_true]
  simp only [SigmaLetter.Compatible, rootContains_eq_true_iff,
    hasVertex_eq_true_iff, adjOnColors_eq_true_iff, tagOnColor_eq_true_iff]
  simp only [and_assoc]

end ExecSigmaLetter
