import GraphMSO.Automata.compile
import GraphMSO.Executable.atomic
import GraphMSO.Executable.formula

/-!
# Executable tree-MSO compiler

This module turns executable tree formulas into deterministic bottom-up
automata.  Its proof field connects every computed automaton to the existing
`TrackLanguage` correctness development.
-/

namespace GraphMSO.Executable

open BinTree
open BinTree.Automata
open GraphMSO.TreeLanguage

variable {A : Type} [Finite A] [DecidableEq A]

/-! ## Languages of the executable atomic automata -/

@[simp] theorem language_falseAutomaton :
    (falseAutomaton A).toTreeAutomaton.language = ∅ := by
  ext t
  rw [ExecTreeAutomaton.mem_language_iff_accepts_ofTerm]
  simp

@[simp] theorem language_trackSingletonAutomaton {n : ℕ} (i : Fin n) :
    (trackSingletonAutomaton A i).toTreeAutomaton.language =
      {t | trackCount i (BinTree.ofTerm t) = Count.one} := by
  ext t
  rw [ExecTreeAutomaton.mem_language_iff_accepts_ofTerm]
  exact trackSingletonAutomaton_accepts_eq_true i (BinTree.ofTerm t)

@[simp] theorem language_tracksIntersectAutomaton {n : ℕ} (i j : Fin n) :
    (tracksIntersectAutomaton A i j).toTreeAutomaton.language =
      {t | tracksIntersect i j (BinTree.ofTerm t) = true} := by
  ext t
  rw [ExecTreeAutomaton.mem_language_iff_accepts_ofTerm]
  rw [tracksIntersectAutomaton_accepts]
  rfl

@[simp] theorem language_parentTrackAutomaton {n : ℕ} (parent child : Fin n) :
    (parentTrackAutomaton A parent child).toTreeAutomaton.language =
      {t | (parentTrackSummary parent child (BinTree.ofTerm t)).2 = true} := by
  ext t
  rw [ExecTreeAutomaton.mem_language_iff_accepts_ofTerm]
  rw [parentTrackAutomaton_accepts]
  rfl

@[simp] theorem language_labelMemTrackAutomaton {n : ℕ} (i : Fin n)
    (predicate : A → Bool) :
    (labelMemTrackAutomaton i predicate).toTreeAutomaton.language =
      {t | ∃ a ∈ labelsOnTrack i (BinTree.ofTerm t), predicate a = true} := by
  ext t
  rw [ExecTreeAutomaton.mem_language_iff_accepts_ofTerm]
  exact labelMemTrackAutomaton_accepts_eq_true_iff i predicate (BinTree.ofTerm t)

@[simp] theorem language_labelMem₂TrackAutomaton {n : ℕ} (i j : Fin n)
    (relation : A → A → Bool) :
    (labelMem₂TrackAutomaton i j relation).toTreeAutomaton.language =
      {t |
        let p := labelPairSummary i j (BinTree.ofTerm t)
        ∃ a ∈ p.1, ∃ b ∈ p.2, relation a b = true} := by
  ext t
  rw [ExecTreeAutomaton.mem_language_iff_accepts_ofTerm]
  rw [labelMem₂TrackAutomaton_accepts_eq_true_iff]
  simp only [labelPairSummary_fst, labelPairSummary_snd]
  rfl

/-! ## Certified compilation -/

/-- An executable automaton together with its proof-facing compiler certificate. -/
structure Compiled {n : ℕ} (foTrack : FOVar → Fin n) (soTrack : SOVar → Fin n)
    (phi : ExecFormula A) where
  automaton : ExecTreeAutomaton (A × TrackBits n)
  correct : TrackLanguage foTrack soTrack phi.toFormula
    automaton.toTreeAutomaton.language

/-- Compile an executable tree-MSO formula in an arbitrary track context. -/
def compile : (phi : ExecFormula A) → (n : ℕ) →
    (foTrack : FOVar → Fin n) → (soTrack : SOVar → Fin n) →
      Compiled foTrack soTrack phi
  | .false_, _, _, _ =>
      { automaton := falseAutomaton _
        correct := by simpa using (TrackLanguage.false_ :
          TrackLanguage _ _ TreeLanguage.Formula.false_ ∅) }
  | .equal x y, _, foTrack, _ =>
      { automaton := tracksIntersectAutomaton A (foTrack x) (foTrack y)
        correct := by simpa using TrackLanguage.equal (A := A) x y }
  | .parent parent child, _, foTrack, _ =>
      { automaton := parentTrackAutomaton A (foTrack parent) (foTrack child)
        correct := by simpa using TrackLanguage.parent (A := A) parent child }
  | .labelMem predicate x, _, foTrack, _ =>
      { automaton := labelMemTrackAutomaton (foTrack x) predicate
        correct := by
          simpa using TrackLanguage.labelMem (A := A)
            {a | predicate a = true} x }
  | .labelMem₂ relation x y, _, foTrack, _ =>
      { automaton := labelMem₂TrackAutomaton (foTrack x) (foTrack y) relation
        correct := by
          simpa using TrackLanguage.labelMem₂ (A := A)
            {p | relation p.1 p.2 = true} x y }
  | .inSet x X, _, foTrack, soTrack =>
      { automaton := tracksIntersectAutomaton A (foTrack x) (soTrack X)
        correct := by simpa using TrackLanguage.inSet (A := A) x X }
  | .neg phi, n, foTrack, soTrack =>
      let compiled := compile phi n foTrack soTrack
      { automaton := compiled.automaton.compl
        correct := by simpa using TrackLanguage.neg compiled.correct }
  | .conj phi psi, n, foTrack, soTrack =>
      let left := compile phi n foTrack soTrack
      let right := compile psi n foTrack soTrack
      { automaton := left.automaton.inter right.automaton
        correct := by simpa using TrackLanguage.conj left.correct right.correct }
  | .disj phi psi, n, foTrack, soTrack =>
      let left := compile phi n foTrack soTrack
      let right := compile psi n foTrack soTrack
      { automaton := left.automaton.union right.automaton
        correct := by simpa using TrackLanguage.disj left.correct right.correct }
  | .impl phi psi, n, foTrack, soTrack =>
      let left := compile phi n foTrack soTrack
      let right := compile psi n foTrack soTrack
      { automaton := left.automaton.compl.union right.automaton
        correct := by simpa using TrackLanguage.impl left.correct right.correct }
  | .biimpl phi psi, n, foTrack, soTrack =>
      let left := compile phi n foTrack soTrack
      let right := compile psi n foTrack soTrack
      { automaton := (left.automaton.inter right.automaton).union
          (left.automaton.compl.inter right.automaton.compl)
        correct := by simpa using TrackLanguage.biimpl left.correct right.correct }
  | .existsFO x phi, n, foTrack, soTrack =>
      let keep : Fin n → Fin (n + 1) := Fin.castSucc
      let sourceFO : FOVar → Fin (n + 1) := fun y =>
        if y = x then Fin.last n else keep (foTrack y)
      let sourceSO : SOVar → Fin (n + 1) := fun X => keep (soTrack X)
      let child := compile phi (n + 1) sourceFO sourceSO
      { automaton :=
          (trackSingletonAutomaton A (Fin.last n)).inter child.automaton |>.projectLast
        correct := by
          simpa [ExecTreeAutomaton.language_toTreeAutomaton_projectLast] using
            TrackLanguage.existsFO x keep sourceFO sourceSO (Fin.last n)
              (Fin.castSucc_injective n)
              (by intro y hy; simp [sourceFO, hy])
              (by simp [sourceFO])
              (by intro i; exact (Fin.castSucc_ne_last i).symm)
              (by intro X; simp [sourceSO]) child.correct }
  | .forallFO x phi, n, foTrack, soTrack =>
      let keep : Fin n → Fin (n + 1) := Fin.castSucc
      let sourceFO : FOVar → Fin (n + 1) := fun y =>
        if y = x then Fin.last n else keep (foTrack y)
      let sourceSO : SOVar → Fin (n + 1) := fun X => keep (soTrack X)
      let child := compile phi (n + 1) sourceFO sourceSO
      { automaton :=
          ((trackSingletonAutomaton A (Fin.last n)).inter child.automaton.compl |>
            ExecTreeAutomaton.projectLast).compl
        correct := by
          simpa [ExecTreeAutomaton.language_toTreeAutomaton_projectLast] using
            TrackLanguage.forallFO x keep sourceFO sourceSO (Fin.last n)
              (Fin.castSucc_injective n)
              (by intro y hy; simp [sourceFO, hy])
              (by simp [sourceFO])
              (by intro i; exact (Fin.castSucc_ne_last i).symm)
              (by intro X; simp [sourceSO]) child.correct }
  | .existsSO X phi, n, foTrack, soTrack =>
      let keep : Fin n → Fin (n + 1) := Fin.castSucc
      let sourceFO : FOVar → Fin (n + 1) := fun y => keep (foTrack y)
      let sourceSO : SOVar → Fin (n + 1) := fun Y =>
        if Y = X then Fin.last n else keep (soTrack Y)
      let child := compile phi (n + 1) sourceFO sourceSO
      { automaton := child.automaton.projectLast
        correct := by
          simpa [ExecTreeAutomaton.language_toTreeAutomaton_projectLast] using
            TrackLanguage.existsSO X keep sourceFO sourceSO (Fin.last n)
              (Fin.castSucc_injective n)
              (by intro y; simp [sourceFO])
              (by simp [sourceSO])
              (by intro i; exact (Fin.castSucc_ne_last i).symm)
              (by intro Y hY; simp [sourceSO, hY]) child.correct }
  | .forallSO X phi, n, foTrack, soTrack =>
      let keep : Fin n → Fin (n + 1) := Fin.castSucc
      let sourceFO : FOVar → Fin (n + 1) := fun y => keep (foTrack y)
      let sourceSO : SOVar → Fin (n + 1) := fun Y =>
        if Y = X then Fin.last n else keep (soTrack Y)
      let child := compile phi (n + 1) sourceFO sourceSO
      { automaton := child.automaton.compl.projectLast.compl
        correct := by
          simpa [ExecTreeAutomaton.language_toTreeAutomaton_projectLast] using
            TrackLanguage.forallSO X keep sourceFO sourceSO (Fin.last n)
              (Fin.castSucc_injective n)
              (by intro y; simp [sourceFO])
              (by simp [sourceSO])
              (by intro i; exact (Fin.castSucc_ne_last i).symm)
              (by intro Y hY; simp [sourceSO, hY]) child.correct }

/-! ## Closed-tree checker -/

/-- Add one computationally empty dummy track to every label. -/
def addDummyTrack (t : BinTree A) : BinTree (A × TrackBits 1) :=
  t.map fun a => (a, fun _ => false)

/-- Compile and execute a tree-MSO formula under the empty assignment. -/
def checkTree (phi : ExecFormula A) (t : BinTree A) : Bool :=
  let track : FOVar → Fin 1 := fun _ => 0
  (compile phi 1 track track).automaton.accepts (addDummyTrack t)

theorem checkTree_eq_true_iff (phi : ExecFormula A) (t : BinTree A) :
    checkTree phi t = true ↔
      TreeLanguage.Semantics.Satisfies t.toTreeModel phi.toFormula := by
  let track : FOVar → Fin 1 := fun _ => 0
  let tracks : Fin 1 → Set t.Pos := fun _ => ∅
  let tracked : BinTree (A × TrackBits 1) := withTracks t tracks
  let e := eraseWithTracksEquiv t tracks
  let rho : Assignment tracked.eraseTracks.toTreeModel :=
    (Assignment.empty t.toTreeModel).mapEquiv e
  have hcarry : CarriesAssignment tracked track track rho := by
    simpa [tracked, tracks, rho, e, track] using
      CarriesAssignment.empty_withTracks_empty t track track
  have hiso :
      TreeLanguage.Semantics.SatisfiesAt tracked.eraseTracks.toTreeModel
          phi.toFormula rho ↔
        TreeLanguage.Semantics.SatisfiesAt t.toTreeModel phi.toFormula
          (Assignment.empty t.toTreeModel) := by
    simpa [tracked, tracks, rho, e] using
      TreeLanguage.Semantics.satisfiesAt_mapEquiv_iff
        (eraseWithTracksIso t tracks) phi.toFormula (Assignment.empty t.toTreeModel)
  have hcorrect := (compile phi 1 track track).correct.correct tracked rho hcarry
  have hsentence :
      TreeLanguage.Semantics.Satisfies t.toTreeModel phi.toFormula ↔
        tracked.toTerm ∈
          (compile phi 1 track track).automaton.toTreeAutomaton.language := by
    exact hiso.symm.trans hcorrect
  have haccept := ExecTreeAutomaton.accepts_eq_true_iff_language
    (compile phi 1 track track).automaton tracked
  have hdummy : addDummyTrack t = tracked := by
    simp [addDummyTrack, tracked, tracks, withTracks_empty]
  change (compile phi 1 track track).automaton.accepts (addDummyTrack t) = true ↔ _
  rw [hdummy]
  exact haccept.trans hsentence.symm

end GraphMSO.Executable
