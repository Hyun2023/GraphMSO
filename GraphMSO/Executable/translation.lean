import GraphMSO.Decomp.translation
import GraphMSO.Executable.formula
import GraphMSO.Executable.sigma
import GraphMSO.Executable.relabel

/-!
# Executable Courcelle translation

This file mirrors the proof-facing translation from graph MSO to tree MSO,
using Boolean predicates on `ExecSigmaLetter`.  The refinement theorems at the
end show that decoding the finite letters recovers the existing translation.
-/

namespace GraphMSO.Executable

universe u v

open GraphMSO TreeLanguage

variable {P : Type u} {omega : ℕ}

/-- The executable Courcelle translation from graph MSO to tree MSO. -/
def translate (omega : ℕ) :
    Language.Formula P → ExecFormula (ExecSigmaLetter P omega)
  | .false_ => .false_
  | .equal x y =>
      .eqTuple (fun i a => a.hasVertex i) (fun i a => a.rootContains i)
        (fvBlock omega x) (fvBlock omega y)
  | .adj x y =>
      .adjTuple (fun i a => a.hasVertex i) (fun i a => a.rootContains i)
        (fun i j a => a.adjOnColors i j)
        (fvBlock omega x) (fvBlock omega y)
  | .pred p x =>
      .predTuple (fun i a => a.hasVertex i) (fun i a => a.rootContains i)
        (fun i a => a.tagOnColor p i) (fvBlock omega x)
  | .inSet x X =>
      .contTuple (fun i a => a.hasVertex i) (fun i a => a.rootContains i)
        (fvBlock omega x) (svBlock omega X)
  | .neg φ => .neg (translate omega φ)
  | .conj φ ψ => .conj (translate omega φ) (translate omega ψ)
  | .disj φ ψ => .disj (translate omega φ) (translate omega ψ)
  | .impl φ ψ => .impl (translate omega φ) (translate omega ψ)
  | .biimpl φ ψ => .biimpl (translate omega φ) (translate omega ψ)
  | .existsFO x φ =>
      .existsSOList (blockList (fvBlock omega x))
        (.conj
          (.vtxTuple (fun i a => a.hasVertex i) (fun i a => a.rootContains i)
            (fvBlock omega x))
          (translate omega φ))
  | .forallFO x φ =>
      .forallSOList (blockList (fvBlock omega x))
        (.impl
          (.vtxTuple (fun i a => a.hasVertex i) (fun i a => a.rootContains i)
            (fvBlock omega x))
          (translate omega φ))
  | .existsSO X φ =>
      .existsSOList (blockList (svBlock omega X))
        (.conj
          (.setTuple (fun i a => a.hasVertex i) (fun i a => a.rootContains i)
            (svBlock omega X))
          (translate omega φ))
  | .forallSO X φ =>
      .forallSOList (blockList (svBlock omega X))
        (.impl
          (.setTuple (fun i a => a.hasVertex i) (fun i a => a.rootContains i)
            (svBlock omega X))
          (translate omega φ))

/-- Executable legality formula for finite sigma letters. -/
def legalFormula (P : Type u) (omega : ℕ) [Fintype P] [DecidableEq P] :
    ExecFormula (ExecSigmaLetter P omega) :=
  .legal (fun a => a.rootEmpty) (fun child parent => child.compatible parent)

/-- The executable sentence checked by the model-checking pipeline. -/
def legalTranslate [Fintype P] [DecidableEq P]
    (omega : ℕ) (theta : Language.Formula P) :
    ExecFormula (ExecSigmaLetter P omega) :=
  .conj (legalFormula P omega) (translate omega theta)

/-! ## Refinement to the proof-facing translation -/

private theorem comapLabels_existsSOList {A : Type u} {B : Type v}
    (f : A → B) (xs : List SOVar) (phi : TreeLanguage.Formula B) :
    (TreeLanguage.Formula.existsSOList xs phi).comapLabels f =
      TreeLanguage.Formula.existsSOList xs (phi.comapLabels f) := by
  induction xs with
  | nil => rfl
  | cons X xs ih =>
      simp only [TreeLanguage.Formula.existsSOList,
        TreeLanguage.Formula.comapLabels, ih]

private theorem comapLabels_forallSOList {A : Type u} {B : Type v}
    (f : A → B) (xs : List SOVar) (phi : TreeLanguage.Formula B) :
    (TreeLanguage.Formula.forallSOList xs phi).comapLabels f =
      TreeLanguage.Formula.forallSOList xs (phi.comapLabels f) := by
  induction xs with
  | nil => rfl
  | cons X xs ih =>
      simp only [TreeLanguage.Formula.forallSOList,
        TreeLanguage.Formula.comapLabels, ih]

private theorem comapLabels_conjList {A : Type u} {B : Type v}
    (f : A → B) (formulas : List (TreeLanguage.Formula B)) :
    (TreeLanguage.Formula.conjList formulas).comapLabels f =
      TreeLanguage.Formula.conjList (formulas.map fun phi ↦ phi.comapLabels f) := by
  induction formulas with
  | nil => rfl
  | cons phi formulas ih =>
      simp only [TreeLanguage.Formula.conjList, List.map_cons,
        TreeLanguage.Formula.comapLabels, ih]

private theorem comapLabels_disjList {A : Type u} {B : Type v}
    (f : A → B) (formulas : List (TreeLanguage.Formula B)) :
    (TreeLanguage.Formula.disjList formulas).comapLabels f =
      TreeLanguage.Formula.disjList (formulas.map fun phi ↦ phi.comapLabels f) := by
  induction formulas with
  | nil => rfl
  | cons phi formulas ih =>
      simp only [TreeLanguage.Formula.disjList, List.map_cons,
        TreeLanguage.Formula.comapLabels, ih]

private theorem comapLabels_legal {A : Type u} {B : Type v}
    (f : A → B) (rootLetter : Set B) (compatible : Set (B × B)) :
    (TreeLanguage.Formula.legal rootLetter compatible).comapLabels f =
      TreeLanguage.Formula.legal {a | f a ∈ rootLetter}
        {q | (f q.1, f q.2) ∈ compatible} := by
  rfl

private theorem comapLabels_definingPair {A : Type u} {B : Type v}
    (f : A → B) (hasVertex rootContains : Set B) (Z : SOVar) :
    (TreeLanguage.Formula.definingPair hasVertex rootContains Z).comapLabels f =
      TreeLanguage.Formula.definingPair {a | f a ∈ hasVertex}
        {a | f a ∈ rootContains} Z := by
  rfl

private theorem comapLabels_vtxTuple {A : Type u} {B : Type v} {k : Nat}
    (f : A → B) (hasVertex rootContains : Fin k → Set B) (Zs : Fin k → SOVar) :
    (TreeLanguage.Formula.vtxTuple hasVertex rootContains Zs).comapLabels f =
      TreeLanguage.Formula.vtxTuple (fun i ↦ {a | f a ∈ hasVertex i})
        (fun i ↦ {a | f a ∈ rootContains i}) Zs := by
  simp [TreeLanguage.Formula.vtxTuple, comapLabels_disjList,
    comapLabels_conjList, comapLabels_definingPair,
    TreeLanguage.Formula.empty, TreeLanguage.Formula.comapLabels, Function.comp_def]

private theorem comapLabels_setTuple {A : Type u} {B : Type v} {k : Nat}
    (f : A → B) (hasVertex rootContains : Fin k → Set B) (Zs : Fin k → SOVar) :
    (TreeLanguage.Formula.setTuple hasVertex rootContains Zs).comapLabels f =
      TreeLanguage.Formula.setTuple (fun i ↦ {a | f a ∈ hasVertex i})
        (fun i ↦ {a | f a ∈ rootContains i}) Zs := by
  simp [TreeLanguage.Formula.setTuple, comapLabels_conjList,
    comapLabels_definingPair, TreeLanguage.Formula.subset,
    TreeLanguage.Formula.comapLabels, Function.comp_def]

private theorem comapLabels_adjTuple {A : Type u} {B : Type v} {k : Nat}
    (f : A → B) (hasVertex rootContains : Fin k → Set B)
    (adjacent : Fin k → Fin k → Set B) (Xs Ys : Fin k → SOVar) :
    (TreeLanguage.Formula.adjTuple hasVertex rootContains adjacent Xs Ys).comapLabels f =
      TreeLanguage.Formula.adjTuple (fun i ↦ {a | f a ∈ hasVertex i})
        (fun i ↦ {a | f a ∈ rootContains i})
        (fun i j ↦ {a | f a ∈ adjacent i j}) Xs Ys := by
  simp [TreeLanguage.Formula.adjTuple, comapLabels_disjList,
    comapLabels_vtxTuple, TreeLanguage.Formula.comapLabels, Function.comp_def]

private theorem comapLabels_predTuple {A : Type u} {B : Type v} {k : Nat}
    (f : A → B) (hasVertex rootContains : Fin k → Set B)
    (tagged : Fin k → Set B) (Xs : Fin k → SOVar) :
    (TreeLanguage.Formula.predTuple hasVertex rootContains tagged Xs).comapLabels f =
      TreeLanguage.Formula.predTuple (fun i ↦ {a | f a ∈ hasVertex i})
        (fun i ↦ {a | f a ∈ rootContains i})
        (fun i ↦ {a | f a ∈ tagged i}) Xs := by
  simp [TreeLanguage.Formula.predTuple, comapLabels_disjList,
    comapLabels_vtxTuple, TreeLanguage.Formula.comapLabels, Function.comp_def]

private theorem comapLabels_eqTuple {A : Type u} {B : Type v} {k : Nat}
    (f : A → B) (hasVertex rootContains : Fin k → Set B)
    (Xs Ys : Fin k → SOVar) :
    (TreeLanguage.Formula.eqTuple hasVertex rootContains Xs Ys).comapLabels f =
      TreeLanguage.Formula.eqTuple (fun i ↦ {a | f a ∈ hasVertex i})
        (fun i ↦ {a | f a ∈ rootContains i}) Xs Ys := by
  simp [TreeLanguage.Formula.eqTuple, comapLabels_conjList,
    comapLabels_vtxTuple, TreeLanguage.Formula.setEq, TreeLanguage.Formula.subset,
    TreeLanguage.Formula.comapLabels, Function.comp_def]

private theorem comapLabels_contTuple {A : Type u} {B : Type v} {k : Nat}
    (f : A → B) (hasVertex rootContains : Fin k → Set B)
    (Xs Ys : Fin k → SOVar) :
    (TreeLanguage.Formula.contTuple hasVertex rootContains Xs Ys).comapLabels f =
      TreeLanguage.Formula.contTuple (fun i ↦ {a | f a ∈ hasVertex i})
        (fun i ↦ {a | f a ∈ rootContains i}) Xs Ys := by
  simp [TreeLanguage.Formula.contTuple, comapLabels_disjList,
    comapLabels_vtxTuple, comapLabels_setTuple,
    TreeLanguage.Formula.nonempty, TreeLanguage.Formula.subset,
    TreeLanguage.Formula.comapLabels, Function.comp_def]

theorem toFormula_translate [Fintype P] [DecidableEq P]
    (theta : Language.Formula P) :
    (translate omega theta).toFormula =
      (Language.Formula.translate omega theta).comapLabels ExecSigmaLetter.decode := by
  induction theta <;>
    simp [translate, Language.Formula.translate, TreeLanguage.Formula.comapLabels,
      comapLabels_existsSOList, comapLabels_forallSOList, comapLabels_vtxTuple,
      comapLabels_setTuple, comapLabels_adjTuple, comapLabels_predTuple,
      comapLabels_eqTuple, comapLabels_contTuple, *]

theorem toFormula_legalFormula [Fintype P] [DecidableEq P] :
    (legalFormula P omega).toFormula =
      (SigmaTree.legalFormula P omega).comapLabels ExecSigmaLetter.decode := by
  simp [legalFormula, SigmaTree.legalFormula, comapLabels_legal]

theorem toFormula_legalTranslate [Fintype P] [DecidableEq P]
    (theta : Language.Formula P) :
    (legalTranslate omega theta).toFormula =
      (TreeLanguage.Formula.conj (SigmaTree.legalFormula P omega)
        (Language.Formula.translate omega theta)).comapLabels ExecSigmaLetter.decode := by
  simp [legalTranslate, TreeLanguage.Formula.comapLabels, toFormula_translate,
    toFormula_legalFormula]

end GraphMSO.Executable
