import GraphMSO.Executable.compile
import GraphMSO.Executable.translation
import GraphMSO.Automata.cost

namespace GraphMSO.Executable

open BinTree.Automata

variable {A : Type} [Finite A] [DecidableEq A]

theorem natCard_finset (S : Type) [Finite S] :
    Nat.card (Finset S) = 2 ^ Nat.card S := by
  letI : Fintype S := Fintype.ofFinite S
  rw [Nat.card_eq_fintype_card, Fintype.card_finset,
    Nat.card_eq_fintype_card]

@[simp] theorem natCard_count : Nat.card Count = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[simp] theorem fintypeCard_count : Fintype.card Count = 3 := by
  decide

@[simp] theorem natCard_bool : Nat.card Bool = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[simp] theorem natCard_punit : Nat.card PUnit = 1 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- Exact state-count recurrence for the executable formula compiler. -/
def compilerStateCount (alphabetCard : Nat) : ExecFormula A → Nat
  | .false_ => 1
  | .equal _ _ => 2
  | .parent _ _ => 4
  | .labelMem _ _ => 2 ^ alphabetCard
  | .labelMem₂ _ _ _ => (2 ^ alphabetCard) ^ 2
  | .inSet _ _ => 2
  | .neg phi => compilerStateCount alphabetCard phi
  | .conj phi psi | .disj phi psi | .impl phi psi =>
      compilerStateCount alphabetCard phi * compilerStateCount alphabetCard psi
  | .biimpl phi psi =>
      (compilerStateCount alphabetCard phi * compilerStateCount alphabetCard psi) ^ 2
  | .existsFO _ phi | .forallFO _ phi =>
      2 ^ (3 * compilerStateCount alphabetCard phi)
  | .existsSO _ phi | .forallSO _ phi =>
      2 ^ compilerStateCount alphabetCard phi

theorem compile_state_card (phi : ExecFormula A) (n : Nat)
    (foTrack : GraphMSO.TreeLanguage.FOVar → Fin n)
    (soTrack : GraphMSO.TreeLanguage.SOVar → Fin n) :
    Nat.card (compile phi n foTrack soTrack).automaton.State =
      compilerStateCount (Nat.card A) phi := by
  induction phi generalizing n with
  | false_ => simp [compile, compilerStateCount, falseAutomaton, foldAutomaton]
  | equal => simp [compile, compilerStateCount, tracksIntersectAutomaton,
      foldAutomaton]
  | parent => simp [compile, compilerStateCount, parentTrackAutomaton,
      foldAutomaton]
  | labelMem predicate x =>
      simp [compile, compilerStateCount, labelMemTrackAutomaton,
        labelsOnTrackAutomaton, foldAutomaton, natCard_finset]
  | labelMem₂ relation x y =>
      simp [compile, compilerStateCount, labelMem₂TrackAutomaton,
        foldAutomaton, Nat.card_prod, natCard_finset, pow_two]
  | inSet => simp [compile, compilerStateCount, tracksIntersectAutomaton,
      foldAutomaton]
  | neg phi ih =>
      simp [compile, compilerStateCount, ExecTreeAutomaton.compl, ih]
  | conj phi psi ihPhi ihPsi =>
      simp [compile, compilerStateCount, ExecTreeAutomaton.inter,
        Nat.card_prod, ihPhi, ihPsi]
  | disj phi psi ihPhi ihPsi =>
      simp [compile, compilerStateCount, ExecTreeAutomaton.union,
        Nat.card_prod, ihPhi, ihPsi]
  | impl phi psi ihPhi ihPsi =>
      simp [compile, compilerStateCount, ExecTreeAutomaton.union,
        ExecTreeAutomaton.compl, Nat.card_prod, ihPhi, ihPsi]
  | biimpl phi psi ihPhi ihPsi =>
      simp [compile, compilerStateCount, ExecTreeAutomaton.union,
        ExecTreeAutomaton.inter, ExecTreeAutomaton.compl, Nat.card_prod,
        ihPhi, ihPsi, pow_two]
  | existsFO x phi ih =>
      simp [compile, compilerStateCount, ExecTreeAutomaton.projectLast,
        ExecTreeAutomaton.inter, trackSingletonAutomaton, foldAutomaton,
        Nat.card_prod, natCard_finset, ih]
  | forallFO x phi ih =>
      simp [compile, compilerStateCount, ExecTreeAutomaton.projectLast,
        ExecTreeAutomaton.inter, ExecTreeAutomaton.compl,
        trackSingletonAutomaton, foldAutomaton, Nat.card_prod,
        natCard_finset, ih]
  | existsSO X phi ih =>
      simp [compile, compilerStateCount, ExecTreeAutomaton.projectLast,
        natCard_finset, ih]
  | forallSO X phi ih =>
      simp [compile, compilerStateCount, ExecTreeAutomaton.projectLast,
        ExecTreeAutomaton.compl, natCard_finset, ih]

/-- Number of tower levels needed by the compiler constructors. -/
def compilerTowerHeight : ExecFormula A → Nat
  | .false_ | .equal _ _ | .parent _ _ | .labelMem _ _ |
      .labelMem₂ _ _ _ | .inSet _ _ => 1
  | .neg phi => compilerTowerHeight phi
  | .conj phi psi | .disj phi psi | .impl phi psi =>
      max (compilerTowerHeight phi) (compilerTowerHeight psi) + 1
  | .biimpl phi psi =>
      max (compilerTowerHeight phi) (compilerTowerHeight psi) + 2
  | .existsFO _ phi | .forallFO _ phi => compilerTowerHeight phi + 2
  | .existsSO _ phi | .forallSO _ phi => compilerTowerHeight phi + 1

theorem self_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega

theorem courcelleTower_mono_height (base : Nat) {h k : Nat} (hhk : h ≤ k) :
    courcelleTower h base ≤ courcelleTower k base := by
  obtain ⟨d, hk⟩ := Nat.exists_eq_add_of_le hhk
  subst k
  clear hhk
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, courcelleTower]
      exact ih.trans (self_le_two_pow (courcelleTower (h + d) base))

theorem four_le_courcelleTower {base : Nat} (hbase : 4 ≤ base) (height : Nat) :
    4 ≤ courcelleTower height base := by
  induction height with
  | zero => exact hbase
  | succ height ih =>
      simp only [courcelleTower]
      calc
        4 = 2 ^ 2 := by decide
        _ ≤ 2 ^ courcelleTower height base :=
          Nat.pow_le_pow_right (by decide) (by omega)

theorem sq_le_two_pow {n : Nat} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
      rw [pow_two, pow_succ]
      rw [pow_two] at ih
      nlinarith

theorem four_mul_le_two_pow {n : Nat} (hn : 4 ≤ n) : 4 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
      rw [pow_succ]
      omega

omit [Finite A] [DecidableEq A] in
theorem compilerStateCount_le_tower (phi : ExecFormula A) :
    compilerStateCount (Nat.card A) phi ≤
      courcelleTower (compilerTowerHeight phi) (4 * (Nat.card A + 1)) := by
  let base := 4 * (Nat.card A + 1)
  have hbase : 4 ≤ base := by simp [base]
  have hfour (h : Nat) : 4 ≤ courcelleTower h base :=
    four_le_courcelleTower hbase h
  induction phi with
  | false_ =>
      simp only [compilerStateCount, compilerTowerHeight]
      exact le_trans (by omega) (hfour 1)
  | equal =>
      simp only [compilerStateCount, compilerTowerHeight]
      exact le_trans (by omega) (hfour 1)
  | parent =>
      exact (hfour 1)
  | labelMem predicate x =>
      simp only [compilerStateCount, compilerTowerHeight, courcelleTower]
      apply Nat.pow_le_pow_right (by decide)
      omega
  | labelMem₂ relation x y =>
      simp only [compilerStateCount, compilerTowerHeight, courcelleTower]
      rw [← pow_mul]
      apply Nat.pow_le_pow_right (by decide)
      omega
  | inSet =>
      simp only [compilerStateCount, compilerTowerHeight]
      exact le_trans (by omega) (hfour 1)
  | neg phi ih =>
      simpa [compilerStateCount, compilerTowerHeight] using ih
  | conj phi psi ihPhi ihPsi =>
      simp only [compilerStateCount, compilerTowerHeight, courcelleTower]
      let h := max (compilerTowerHeight phi) (compilerTowerHeight psi)
      let tower := courcelleTower h base
      have hPhi : compilerStateCount (Nat.card A) phi ≤ tower :=
        ihPhi.trans (courcelleTower_mono_height base (Nat.le_max_left _ _))
      have hPsi : compilerStateCount (Nat.card A) psi ≤ tower :=
        ihPsi.trans (courcelleTower_mono_height base (Nat.le_max_right _ _))
      calc
        _ ≤ tower ^ 2 := by
          rw [pow_two]
          exact Nat.mul_le_mul hPhi hPsi
        _ ≤ 2 ^ tower := sq_le_two_pow (hfour h)
  | disj phi psi ihPhi ihPsi =>
      simp only [compilerStateCount, compilerTowerHeight, courcelleTower]
      let h := max (compilerTowerHeight phi) (compilerTowerHeight psi)
      let tower := courcelleTower h base
      have hPhi : compilerStateCount (Nat.card A) phi ≤ tower :=
        ihPhi.trans (courcelleTower_mono_height base (Nat.le_max_left _ _))
      have hPsi : compilerStateCount (Nat.card A) psi ≤ tower :=
        ihPsi.trans (courcelleTower_mono_height base (Nat.le_max_right _ _))
      calc
        _ ≤ tower ^ 2 := by
          rw [pow_two]
          exact Nat.mul_le_mul hPhi hPsi
        _ ≤ 2 ^ tower := sq_le_two_pow (hfour h)
  | impl phi psi ihPhi ihPsi =>
      simp only [compilerStateCount, compilerTowerHeight, courcelleTower]
      let h := max (compilerTowerHeight phi) (compilerTowerHeight psi)
      let tower := courcelleTower h base
      have hPhi : compilerStateCount (Nat.card A) phi ≤ tower :=
        ihPhi.trans (courcelleTower_mono_height base (Nat.le_max_left _ _))
      have hPsi : compilerStateCount (Nat.card A) psi ≤ tower :=
        ihPsi.trans (courcelleTower_mono_height base (Nat.le_max_right _ _))
      calc
        _ ≤ tower ^ 2 := by
          rw [pow_two]
          exact Nat.mul_le_mul hPhi hPsi
        _ ≤ 2 ^ tower := sq_le_two_pow (hfour h)
  | biimpl phi psi ihPhi ihPsi =>
      simp only [compilerStateCount, compilerTowerHeight, courcelleTower]
      let h := max (compilerTowerHeight phi) (compilerTowerHeight psi)
      let tower := courcelleTower h base
      have hPhi : compilerStateCount (Nat.card A) phi ≤ tower :=
        ihPhi.trans (courcelleTower_mono_height base (Nat.le_max_left _ _))
      have hPsi : compilerStateCount (Nat.card A) psi ≤ tower :=
        ihPsi.trans (courcelleTower_mono_height base (Nat.le_max_right _ _))
      have hprod : compilerStateCount (Nat.card A) phi *
          compilerStateCount (Nat.card A) psi ≤ 2 ^ tower := by
        calc
          _ ≤ tower ^ 2 := by
            rw [pow_two]
            exact Nat.mul_le_mul hPhi hPsi
          _ ≤ 2 ^ tower := sq_le_two_pow (hfour h)
      calc
        _ ≤ (2 ^ tower) ^ 2 := Nat.pow_le_pow_left hprod 2
        _ ≤ 2 ^ (2 ^ tower) := sq_le_two_pow (by
          calc 4 = 2 ^ 2 := by decide
               _ ≤ 2 ^ tower := Nat.pow_le_pow_right (by decide) (by
                 have := hfour h
                 omega))
  | existsFO x phi ih =>
      simp only [compilerStateCount, compilerTowerHeight, courcelleTower]
      apply Nat.pow_le_pow_right (by decide)
      calc
        3 * compilerStateCount (Nat.card A) phi ≤
            4 * courcelleTower (compilerTowerHeight phi) base := by
          exact Nat.mul_le_mul (by omega) ih
        _ ≤ 2 ^ courcelleTower (compilerTowerHeight phi) base :=
          four_mul_le_two_pow (hfour _)
  | forallFO x phi ih =>
      simp only [compilerStateCount, compilerTowerHeight, courcelleTower]
      apply Nat.pow_le_pow_right (by decide)
      calc
        3 * compilerStateCount (Nat.card A) phi ≤
            4 * courcelleTower (compilerTowerHeight phi) base := by
          exact Nat.mul_le_mul (by omega) ih
        _ ≤ 2 ^ courcelleTower (compilerTowerHeight phi) base :=
          four_mul_le_two_pow (hfour _)
  | existsSO X phi ih =>
      simp only [compilerStateCount, compilerTowerHeight, courcelleTower]
      exact Nat.pow_le_pow_right (by decide) ih
  | forallSO X phi ih =>
      simp only [compilerStateCount, compilerTowerHeight, courcelleTower]
      exact Nat.pow_le_pow_right (by decide) ih

omit [Finite A] [DecidableEq A] in
theorem compilerTowerHeight_le_twice_size (phi : ExecFormula A) :
    compilerTowerHeight phi ≤ 2 * phi.toFormula.size := by
  induction phi <;>
    simp [compilerTowerHeight, ExecFormula.toFormula,
      GraphMSO.TreeLanguage.Formula.size] at * <;> omega

theorem compile_state_card_le_formula_tower (phi : ExecFormula A) (n : Nat)
    (foTrack : GraphMSO.TreeLanguage.FOVar → Fin n)
    (soTrack : GraphMSO.TreeLanguage.SOVar → Fin n) :
    Nat.card (compile phi n foTrack soTrack).automaton.State ≤
      courcelleTower (2 * phi.toFormula.size) (4 * (Nat.card A + 1)) := by
  rw [compile_state_card]
  exact (compilerStateCount_le_tower phi).trans
    (courcelleTower_mono_height _ (compilerTowerHeight_le_twice_size phi))

theorem courcelleTower_mono_base {a b : Nat} (hab : a ≤ b) (height : Nat) :
    courcelleTower height a ≤ courcelleTower height b := by
  induction height with
  | zero => exact hab
  | succ height ih =>
      simp only [courcelleTower]
      exact Nat.pow_le_pow_right (by decide) ih

/-- A closed-form upper bound on the Boolean sigma alphabet. -/
noncomputable def sigmaAlphabetBound (P : Type) [Finite P] (omega : Nat) : Nat :=
  let colorTables := 2 ^ (omega + 1)
  colorTables *
    (colorTables * (colorTables ^ (omega + 1) * colorTables ^ Nat.card P))

theorem execSigmaLetter_card_le (P : Type) [Fintype P] [DecidableEq P]
    (omega : Nat) :
    Nat.card (ExecSigmaLetter P omega) ≤ sigmaAlphabetBound P omega := by
  let C := Fin (omega + 1)
  let encode : ExecSigmaLetter P omega →
      (C → Bool) × (C → Bool) × (C → C → Bool) × (P → C → Bool) :=
    fun A => (A.present, A.root, A.adj, A.tag)
  have hinj : Function.Injective encode := by
    intro A B h
    cases A
    cases B
    cases h
    rfl
  have hcard := Nat.card_le_card_of_injective encode hinj
  simpa [sigmaAlphabetBound, C, Nat.card_prod, Nat.card_fun,
    Nat.card_fin, natCard_bool] using hcard

theorem compile_legalTranslate_state_le_tower
    {P : Type} [Fintype P] [DecidableEq P] (omega : Nat)
    (theta : GraphMSO.Language.Formula P) (n : Nat)
    (foTrack : GraphMSO.TreeLanguage.FOVar → Fin n)
    (soTrack : GraphMSO.TreeLanguage.SOVar → Fin n) :
    Nat.card (compile (legalTranslate omega theta) n foTrack soTrack).automaton.State ≤
      courcelleTower
        (2 * (legalTranslate omega theta).toFormula.size)
        (4 * (sigmaAlphabetBound P omega + 1)) := by
  exact (compile_state_card_le_formula_tower
    (legalTranslate omega theta) n foTrack soTrack).trans
      (courcelleTower_mono_base (by
        have h := execSigmaLetter_card_le P omega
        omega) _)

end GraphMSO.Executable

