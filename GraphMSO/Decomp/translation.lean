import GraphMSO.Decomp.recognition
import GraphMSO.language.semantics

/-!
# The Courcelle translation `theta_star`

The translation of `tau_P` MSO formulas into tree MSO formulas over the
Σ-letter alphabet, and its correctness over an encoding (the lecture note's
translation-correctness lemma).

Each graph variable is represented by a block of `omega + 1` tree set
variables: graph first-order variable `x` gets the block `fvBlock omega x`,
and graph set variable `X` gets `svBlock omega X`.  The blocks are pairwise
disjoint by the allocation arithmetic below, so quantifying one block leaves
the others untouched.

The correctness statement quantifies over all tree assignments that carry the
defining tuples of the graph assignment on the free-variable blocks; this
form makes the quantifier cases of the induction self-sustaining without a
capture-avoidance or coincidence-lemma apparatus for the tree language.
-/

namespace GraphMSO

/-! ## Variable allocation -/

/-- The tree set variables allocated to the graph first-order variable
`x`. -/
def fvBlock (omega : ℕ) (x : Language.FOVar) :
    Fin (omega + 1) → TreeLanguage.SOVar :=
  fun i => (omega + 1) * (2 * x) + i

/-- The tree set variables allocated to the graph set variable `X`. -/
def svBlock (omega : ℕ) (X : Language.SOVar) :
    Fin (omega + 1) → TreeLanguage.SOVar :=
  fun i => (omega + 1) * (2 * X + 1) + i

/-- The block of a variable enumeration as a list, for block quantifiers. -/
def blockList {k : ℕ} (Zs : Fin k → TreeLanguage.SOVar) :
    List TreeLanguage.SOVar :=
  (List.finRange k).map Zs

theorem mem_blockList_iff {k : ℕ} {Zs : Fin k → TreeLanguage.SOVar}
    {Y : TreeLanguage.SOVar} :
    Y ∈ blockList Zs ↔ ∃ i, Zs i = Y := by
  simp [blockList]

/-- Base-`k` positional decoding: block index and offset are determined. -/
private theorem block_eq_iff {k : ℕ} {a b : ℕ} {i j : Fin k} :
    k * a + i.1 = k * b + j.1 ↔ a = b ∧ i = j := by
  constructor
  · intro h
    have hk : 0 < k := i.pos
    have ha : (k * a + i.1) / k = a := by
      rw [Nat.mul_add_div hk, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
    have hb : (k * b + j.1) / k = b := by
      rw [Nat.mul_add_div hk, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
    have hab : a = b := by rw [← ha, ← hb, h]
    subst hab
    exact ⟨rfl, Fin.ext (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem fvBlock_eq_fvBlock_iff {omega : ℕ} {x y : Language.FOVar}
    {i j : Fin (omega + 1)} :
    fvBlock omega x i = fvBlock omega y j ↔ x = y ∧ i = j := by
  rw [show fvBlock omega x i = (omega + 1) * (2 * x) + i.1 from rfl,
    show fvBlock omega y j = (omega + 1) * (2 * y) + j.1 from rfl,
    block_eq_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨Nat.eq_of_mul_eq_mul_left (by decide) h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem svBlock_eq_svBlock_iff {omega : ℕ} {X Y : Language.SOVar}
    {i j : Fin (omega + 1)} :
    svBlock omega X i = svBlock omega Y j ↔ X = Y ∧ i = j := by
  rw [show svBlock omega X i = (omega + 1) * (2 * X + 1) + i.1 from rfl,
    show svBlock omega Y j = (omega + 1) * (2 * Y + 1) + j.1 from rfl,
    block_eq_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_right_cancel h), rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem fvBlock_ne_svBlock {omega : ℕ} (x : Language.FOVar)
    (X : Language.SOVar) (i j : Fin (omega + 1)) :
    fvBlock omega x i ≠ svBlock omega X j := by
  intro h
  rw [show fvBlock omega x i = (omega + 1) * (2 * x) + i.1 from rfl,
    show svBlock omega X j = (omega + 1) * (2 * X + 1) + j.1 from rfl,
    block_eq_iff] at h
  exact Nat.two_mul_ne_two_mul_add_one h.1

theorem fvBlock_injective (omega : ℕ) (x : Language.FOVar) :
    Function.Injective (fvBlock omega x) :=
  fun _ _ h => (fvBlock_eq_fvBlock_iff.mp h).2

theorem svBlock_injective (omega : ℕ) (X : Language.SOVar) :
    Function.Injective (svBlock omega X) :=
  fun _ _ h => (svBlock_eq_svBlock_iff.mp h).2

theorem fvBlock_ne_fvBlock {omega : ℕ} {x y : Language.FOVar}
    (h : x ≠ y) (i j : Fin (omega + 1)) :
    fvBlock omega x i ≠ fvBlock omega y j :=
  fun he => h (fvBlock_eq_fvBlock_iff.mp he).1

theorem svBlock_ne_svBlock {omega : ℕ} {X Y : Language.SOVar}
    (h : X ≠ Y) (i j : Fin (omega + 1)) :
    svBlock omega X i ≠ svBlock omega Y j :=
  fun he => h (svBlock_eq_svBlock_iff.mp he).1

theorem fvBlock_notMem_blockList_fvBlock {omega : ℕ} {x y : Language.FOVar}
    (h : y ≠ x) (i : Fin (omega + 1)) :
    fvBlock omega y i ∉ blockList (fvBlock omega x) := by
  rw [mem_blockList_iff]
  rintro ⟨j, hj⟩
  exact h ((fvBlock_eq_fvBlock_iff.mp hj).1).symm

theorem svBlock_notMem_blockList_fvBlock {omega : ℕ}
    (Y : Language.SOVar) (x : Language.FOVar) (i : Fin (omega + 1)) :
    svBlock omega Y i ∉ blockList (fvBlock omega x) := by
  rw [mem_blockList_iff]
  rintro ⟨j, hj⟩
  exact fvBlock_ne_svBlock x Y j i hj

theorem fvBlock_notMem_blockList_svBlock {omega : ℕ}
    (y : Language.FOVar) (X : Language.SOVar) (i : Fin (omega + 1)) :
    fvBlock omega y i ∉ blockList (svBlock omega X) := by
  rw [mem_blockList_iff]
  rintro ⟨j, hj⟩
  exact fvBlock_ne_svBlock y X i j hj.symm

theorem svBlock_notMem_blockList_svBlock {omega : ℕ} {Y Z : Language.SOVar}
    (h : Z ≠ Y) (i : Fin (omega + 1)) :
    svBlock omega Z i ∉ blockList (svBlock omega Y) := by
  rw [mem_blockList_iff]
  rintro ⟨j, hj⟩
  exact h ((svBlock_eq_svBlock_iff.mp hj).1).symm

end GraphMSO

namespace GraphMSO.Language.Formula

open GraphMSO GraphMSO.TreeLanguage

variable {P : Type*}

/--
The Courcelle translation `theta_star`: atoms become the atomic tuple
formulas over the allocated blocks, Boolean connectives commute, and graph
quantifiers become blocks of set quantifiers guarded by the vertex- or
set-recognition formulas.
-/
def translate (omega : ℕ) :
    Formula P → TreeLanguage.Formula (SigmaLetter P omega)
  | false_ => .false_
  | equal x y =>
      .eqTuple (fun i => {a | a.HasVertex i}) (fun i => {a | a.RootContains i})
        (fvBlock omega x) (fvBlock omega y)
  | adj x y =>
      .adjTuple (fun i => {a | a.HasVertex i}) (fun i => {a | a.RootContains i})
        (fun i j => {a | a.AdjOnColors i j})
        (fvBlock omega x) (fvBlock omega y)
  | pred p x =>
      .predTuple (fun i => {a | a.HasVertex i}) (fun i => {a | a.RootContains i})
        (fun i => {a | a.TagOnColor p i}) (fvBlock omega x)
  | inSet x X =>
      .contTuple (fun i => {a | a.HasVertex i}) (fun i => {a | a.RootContains i})
        (fvBlock omega x) (svBlock omega X)
  | neg φ => .neg (translate omega φ)
  | conj φ ψ => .conj (translate omega φ) (translate omega ψ)
  | disj φ ψ => .disj (translate omega φ) (translate omega ψ)
  | impl φ ψ => .impl (translate omega φ) (translate omega ψ)
  | biimpl φ ψ => .biimpl (translate omega φ) (translate omega ψ)
  | existsFO x φ =>
      .existsSOList (blockList (fvBlock omega x))
        (.conj
          (.vtxTuple (fun i => {a | a.HasVertex i})
            (fun i => {a | a.RootContains i}) (fvBlock omega x))
          (translate omega φ))
  | forallFO x φ =>
      .forallSOList (blockList (fvBlock omega x))
        (.impl
          (.vtxTuple (fun i => {a | a.HasVertex i})
            (fun i => {a | a.RootContains i}) (fvBlock omega x))
          (translate omega φ))
  | existsSO X φ =>
      .existsSOList (blockList (svBlock omega X))
        (.conj
          (.setTuple (fun i => {a | a.HasVertex i})
            (fun i => {a | a.RootContains i}) (svBlock omega X))
          (translate omega φ))
  | forallSO X φ =>
      .forallSOList (blockList (svBlock omega X))
        (.impl
          (.setTuple (fun i => {a | a.HasVertex i})
            (fun i => {a | a.RootContains i}) (svBlock omega X))
          (translate omega φ))

end GraphMSO.Language.Formula

/-! ## Correctness of the translation -/

namespace RootedTreeDecomposition

open GraphMSO GraphMSO.TreeLanguage GraphMSO.TreeLanguage.Semantics

variable {V : Type*} [Fintype V] {G : SimpleGraph V}
variable {P : Type*} {omega : ℕ}
variable (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color)

/--
The lecture note's translation-correctness lemma, over an encoding: for every
`tau_P` formula and every pair of assignments in which the tree assignment
carries the defining tuples of the graph assignment on all free-variable
blocks, satisfaction of the translation equals graph satisfaction.
-/
theorem satisfiesAt_translate_iff
    (θ : Language.Formula P)
    (α : Language.Assignment (⟨V, G, vpred⟩ : τPGraph P))
    (ρ : TreeLanguage.Assignment (T.encode vpred color hcolor).toTreeModel)
    (hFO : ∀ x ∈ θ.freeFO, ∃ v : V, α.fo x = some v ∧
      ∀ i, ρ.so (fvBlock omega x i) = T.definingTuple color {v} i)
    (hSO : ∀ Y ∈ θ.freeSO, ∀ i,
      ρ.so (svBlock omega Y i) = T.definingTuple color (α.so Y) i) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (θ.translate omega) ρ ↔
      Language.Semantics.SatisfiesAt _ θ α := by
  revert hFO hSO
  induction θ generalizing α ρ with
  | false_ =>
      intro _ _
      exact Iff.rfl
  | equal x y =>
      intro hFO _
      obtain ⟨u, hu, hXs⟩ := hFO x (by simp [Language.Formula.freeFO])
      obtain ⟨w, hw, hYs⟩ := hFO y (by simp [Language.Formula.freeFO])
      rw [show (Language.Formula.equal x y).translate omega =
        TreeLanguage.Formula.eqTuple (fun i => {a | a.HasVertex i})
          (fun i => {a | a.RootContains i})
          (fvBlock omega x) (fvBlock omega y) from rfl,
        satisfiesAt_eqTuple_iff T vpred color hcolor ρ _ _ hXs hYs]
      constructor
      · rintro rfl
        exact ⟨u, hu, hw⟩
      · rintro ⟨v, hv1, hv2⟩
        rw [hu] at hv1
        rw [hw] at hv2
        rw [Option.some.inj hv1, Option.some.inj hv2]
  | adj x y =>
      intro hFO _
      obtain ⟨u, hu, hXs⟩ := hFO x (by simp [Language.Formula.freeFO])
      obtain ⟨w, hw, hYs⟩ := hFO y (by simp [Language.Formula.freeFO])
      rw [show (Language.Formula.adj x y).translate omega =
        TreeLanguage.Formula.adjTuple (fun i => {a | a.HasVertex i})
          (fun i => {a | a.RootContains i})
          (fun i j => {a | a.AdjOnColors i j})
          (fvBlock omega x) (fvBlock omega y) from rfl,
        satisfiesAt_adjTuple_iff T vpred color hcolor ρ _ _ hXs hYs]
      constructor
      · intro hadj
        exact ⟨u, w, hu, hw, hadj⟩
      · rintro ⟨a, b, ha, hb, hab⟩
        rw [hu] at ha
        rw [hw] at hb
        rw [Option.some.inj ha, Option.some.inj hb]
        exact hab
  | pred p x =>
      intro hFO _
      obtain ⟨u, hu, hXs⟩ := hFO x (by simp [Language.Formula.freeFO])
      rw [show (Language.Formula.pred p x).translate omega =
        TreeLanguage.Formula.predTuple (fun i => {a | a.HasVertex i})
          (fun i => {a | a.RootContains i})
          (fun i => {a | a.TagOnColor p i}) (fvBlock omega x) from rfl,
        satisfiesAt_predTuple_iff T vpred color hcolor ρ _ p hXs]
      constructor
      · intro hp
        exact ⟨u, hu, hp⟩
      · rintro ⟨v, hv, hp⟩
        rw [hu] at hv
        rwa [Option.some.inj hv]
  | inSet x Y =>
      intro hFO hSO
      obtain ⟨u, hu, hXs⟩ := hFO x (by simp [Language.Formula.freeFO])
      have hYs := hSO Y (by simp [Language.Formula.freeSO])
      rw [show (Language.Formula.inSet x Y).translate omega =
        TreeLanguage.Formula.contTuple (fun i => {a | a.HasVertex i})
          (fun i => {a | a.RootContains i})
          (fvBlock omega x) (svBlock omega Y) from rfl,
        satisfiesAt_contTuple_iff T vpred color hcolor ρ _ _ hXs hYs]
      constructor
      · intro hmem
        exact ⟨u, hu, hmem⟩
      · rintro ⟨v, hv, hmem⟩
        rw [hu] at hv
        rwa [Option.some.inj hv]
  | neg φ ih =>
      intro hFO hSO
      exact not_congr (ih α ρ hFO hSO)
  | conj φ ψ ihφ ihψ =>
      intro hFO hSO
      exact and_congr
        (ihφ α ρ (fun x hx => hFO x (Or.inl hx)) (fun Y hY => hSO Y (Or.inl hY)))
        (ihψ α ρ (fun x hx => hFO x (Or.inr hx)) (fun Y hY => hSO Y (Or.inr hY)))
  | disj φ ψ ihφ ihψ =>
      intro hFO hSO
      exact or_congr
        (ihφ α ρ (fun x hx => hFO x (Or.inl hx)) (fun Y hY => hSO Y (Or.inl hY)))
        (ihψ α ρ (fun x hx => hFO x (Or.inr hx)) (fun Y hY => hSO Y (Or.inr hY)))
  | impl φ ψ ihφ ihψ =>
      intro hFO hSO
      exact imp_congr
        (ihφ α ρ (fun x hx => hFO x (Or.inl hx)) (fun Y hY => hSO Y (Or.inl hY)))
        (ihψ α ρ (fun x hx => hFO x (Or.inr hx)) (fun Y hY => hSO Y (Or.inr hY)))
  | biimpl φ ψ ihφ ihψ =>
      intro hFO hSO
      exact iff_congr
        (ihφ α ρ (fun x hx => hFO x (Or.inl hx)) (fun Y hY => hSO Y (Or.inl hY)))
        (ihψ α ρ (fun x hx => hFO x (Or.inr hx)) (fun Y hY => hSO Y (Or.inr hY)))
  | existsFO x φ ih =>
      intro hFO hSO
      rw [show (Language.Formula.existsFO x φ).translate omega =
        TreeLanguage.Formula.existsSOList (blockList (fvBlock omega x))
          (TreeLanguage.Formula.conj
            (TreeLanguage.Formula.vtxTuple (fun i => {a | a.HasVertex i})
              (fun i => {a | a.RootContains i}) (fvBlock omega x))
            (φ.translate omega)) from rfl,
        satisfiesAt_existsSOList_iff]
      constructor
      · rintro ⟨ρ', hfo, hoff, hvtx, hφ⟩
        obtain ⟨v, hv⟩ :=
          (satisfiesAt_vtxTuple_iff T vpred color hcolor ρ'
            (fvBlock omega x)).mp hvtx
        refine ⟨v, ?_⟩
        rw [← ih (α.updateFO x v) ρ' ?_ ?_]
        · exact hφ
        · intro y hy
          by_cases hyx : y = x
          · subst hyx
            exact ⟨v, Language.Assignment.updateFO_here α y v, hv⟩
          · obtain ⟨u, hu, hblocks⟩ := hFO y
              ⟨hy, fun hmem => hyx (by simpa using hmem)⟩
            refine ⟨u, ?_, fun i => ?_⟩
            · rw [Language.Assignment.updateFO_other α v hyx]
              exact hu
            · rw [hoff _ (fvBlock_notMem_blockList_fvBlock hyx i)]
              exact hblocks i
        · intro Z hZ i
          rw [hoff _ (svBlock_notMem_blockList_fvBlock Z x i)]
          exact hSO Z hZ i
      · rintro ⟨v, hφ⟩
        refine ⟨ρ.setBlock (fvBlock omega x)
          (fun i => T.definingTuple color {v} i), rfl, ?_, ?_, ?_⟩
        · intro Y hY
          refine Assignment.setBlock_so_of_forall_ne ρ _ _ fun i hi => ?_
          exact hY (mem_blockList_iff.mpr ⟨i, hi⟩)
        · exact (satisfiesAt_vtxTuple_iff T vpred color hcolor _ _).mpr
            ⟨v, fun i =>
              Assignment.setBlock_so_apply ρ (fvBlock_injective omega x) _ i⟩
        · rw [ih (α.updateFO x v) _ ?_ ?_]
          · exact hφ
          · intro y hy
            by_cases hyx : y = x
            · subst hyx
              exact ⟨v, Language.Assignment.updateFO_here α y v, fun i =>
                Assignment.setBlock_so_apply ρ (fvBlock_injective omega y) _ i⟩
            · obtain ⟨u, hu, hblocks⟩ := hFO y
                ⟨hy, fun hmem => hyx (by simpa using hmem)⟩
              refine ⟨u, ?_, fun i => ?_⟩
              · rw [Language.Assignment.updateFO_other α v hyx]
                exact hu
              · rw [Assignment.setBlock_so_of_forall_ne ρ _ _
                  (fun j => fvBlock_ne_fvBlock (Ne.symm hyx) j i)]
                exact hblocks i
          · intro Z hZ i
            rw [Assignment.setBlock_so_of_forall_ne ρ _ _
              (fun j => fvBlock_ne_svBlock x Z j i)]
            exact hSO Z hZ i
  | forallFO x φ ih =>
      intro hFO hSO
      rw [show (Language.Formula.forallFO x φ).translate omega =
        TreeLanguage.Formula.forallSOList (blockList (fvBlock omega x))
          (TreeLanguage.Formula.impl
            (TreeLanguage.Formula.vtxTuple (fun i => {a | a.HasVertex i})
              (fun i => {a | a.RootContains i}) (fvBlock omega x))
            (φ.translate omega)) from rfl,
        satisfiesAt_forallSOList_iff]
      constructor
      · intro h v
        have hoff : ∀ Y : TreeLanguage.SOVar,
            Y ∉ blockList (fvBlock omega x) →
            (ρ.setBlock (fvBlock omega x)
              (fun i => T.definingTuple color {v} i)).so Y = ρ.so Y := by
          intro Y hY
          refine Assignment.setBlock_so_of_forall_ne ρ _ _ fun i hi => ?_
          exact hY (mem_blockList_iff.mpr ⟨i, hi⟩)
        have hφ' := h (ρ.setBlock (fvBlock omega x)
            (fun i => T.definingTuple color {v} i)) rfl hoff
          ((satisfiesAt_vtxTuple_iff T vpred color hcolor _ _).mpr
            ⟨v, fun i =>
              Assignment.setBlock_so_apply ρ (fvBlock_injective omega x) _ i⟩)
        rw [ih (α.updateFO x v) _ ?_ ?_] at hφ'
        · exact hφ'
        · intro y hy
          by_cases hyx : y = x
          · subst hyx
            exact ⟨v, Language.Assignment.updateFO_here α y v, fun i =>
              Assignment.setBlock_so_apply ρ (fvBlock_injective omega y) _ i⟩
          · obtain ⟨u, hu, hblocks⟩ := hFO y
              ⟨hy, fun hmem => hyx (by simpa using hmem)⟩
            refine ⟨u, ?_, fun i => ?_⟩
            · rw [Language.Assignment.updateFO_other α v hyx]
              exact hu
            · rw [Assignment.setBlock_so_of_forall_ne ρ _ _
                (fun j => fvBlock_ne_fvBlock (Ne.symm hyx) j i)]
              exact hblocks i
        · intro Z hZ i
          rw [Assignment.setBlock_so_of_forall_ne ρ _ _
            (fun j hj => fvBlock_ne_svBlock x Z j i hj)]
          exact hSO Z hZ i
      · intro h ρ' hfo hoff hvtx
        obtain ⟨v, hv⟩ :=
          (satisfiesAt_vtxTuple_iff T vpred color hcolor ρ'
            (fvBlock omega x)).mp hvtx
        rw [ih (α.updateFO x v) ρ' ?_ ?_]
        · exact h v
        · intro y hy
          by_cases hyx : y = x
          · subst hyx
            exact ⟨v, Language.Assignment.updateFO_here α y v, hv⟩
          · obtain ⟨u, hu, hblocks⟩ := hFO y
              ⟨hy, fun hmem => hyx (by simpa using hmem)⟩
            refine ⟨u, ?_, fun i => ?_⟩
            · rw [Language.Assignment.updateFO_other α v hyx]
              exact hu
            · rw [hoff _ (fvBlock_notMem_blockList_fvBlock hyx i)]
              exact hblocks i
        · intro Z hZ i
          rw [hoff _ (svBlock_notMem_blockList_fvBlock Z x i)]
          exact hSO Z hZ i
  | existsSO Y φ ih =>
      intro hFO hSO
      rw [show (Language.Formula.existsSO Y φ).translate omega =
        TreeLanguage.Formula.existsSOList (blockList (svBlock omega Y))
          (TreeLanguage.Formula.conj
            (TreeLanguage.Formula.setTuple (fun i => {a | a.HasVertex i})
              (fun i => {a | a.RootContains i}) (svBlock omega Y))
            (φ.translate omega)) from rfl,
        satisfiesAt_existsSOList_iff]
      constructor
      · rintro ⟨ρ', hfo, hoff, hset, hφ⟩
        obtain ⟨S, hS⟩ :=
          (satisfiesAt_setTuple_iff T vpred color hcolor ρ'
            (svBlock omega Y)).mp hset
        refine ⟨S, ?_⟩
        rw [← ih (α.updateSO Y S) ρ' ?_ ?_]
        · exact hφ
        · intro y hy
          obtain ⟨u, hu, hblocks⟩ := hFO y hy
          refine ⟨u, hu, fun i => ?_⟩
          rw [hoff _ (fvBlock_notMem_blockList_svBlock y Y i)]
          exact hblocks i
        · intro Z hZ i
          by_cases hZY : Z = Y
          · subst hZY
            rw [Language.Assignment.updateSO_here]
            exact (congrFun hS i).symm
          · rw [hoff _ (svBlock_notMem_blockList_svBlock hZY i),
              Language.Assignment.updateSO_other α S hZY]
            exact hSO Z ⟨hZ, fun hmem => hZY (by simpa using hmem)⟩ i
      · rintro ⟨S, hφ⟩
        refine ⟨ρ.setBlock (svBlock omega Y)
          (fun i => T.definingTuple color S i), rfl, ?_, ?_, ?_⟩
        · intro Z hZ
          refine Assignment.setBlock_so_of_forall_ne ρ _ _ fun i hi => ?_
          exact hZ (mem_blockList_iff.mpr ⟨i, hi⟩)
        · exact (satisfiesAt_setTuple_iff T vpred color hcolor _ _).mpr
            ⟨S, funext fun i =>
              (Assignment.setBlock_so_apply ρ (svBlock_injective omega Y) _ i).symm⟩
        · rw [ih (α.updateSO Y S) _ ?_ ?_]
          · exact hφ
          · intro y hy
            obtain ⟨u, hu, hblocks⟩ := hFO y hy
            refine ⟨u, hu, fun i => ?_⟩
            rw [Assignment.setBlock_so_of_forall_ne ρ _ _
              (fun j hj => fvBlock_ne_svBlock y Y i j hj.symm)]
            exact hblocks i
          · intro Z hZ i
            by_cases hZY : Z = Y
            · subst hZY
              rw [Language.Assignment.updateSO_here]
              exact Assignment.setBlock_so_apply ρ (svBlock_injective omega Z) _ i
            · rw [Assignment.setBlock_so_of_forall_ne ρ _ _
                (fun j => svBlock_ne_svBlock (Ne.symm hZY) j i),
                Language.Assignment.updateSO_other α S hZY]
              exact hSO Z ⟨hZ, fun hmem => hZY (by simpa using hmem)⟩ i
  | forallSO Y φ ih =>
      intro hFO hSO
      rw [show (Language.Formula.forallSO Y φ).translate omega =
        TreeLanguage.Formula.forallSOList (blockList (svBlock omega Y))
          (TreeLanguage.Formula.impl
            (TreeLanguage.Formula.setTuple (fun i => {a | a.HasVertex i})
              (fun i => {a | a.RootContains i}) (svBlock omega Y))
            (φ.translate omega)) from rfl,
        satisfiesAt_forallSOList_iff]
      constructor
      · intro h S
        have hoff : ∀ Z : TreeLanguage.SOVar,
            Z ∉ blockList (svBlock omega Y) →
            (ρ.setBlock (svBlock omega Y)
              (fun i => T.definingTuple color S i)).so Z = ρ.so Z := by
          intro Z hZ
          refine Assignment.setBlock_so_of_forall_ne ρ _ _ fun i hi => ?_
          exact hZ (mem_blockList_iff.mpr ⟨i, hi⟩)
        have hφ' := h (ρ.setBlock (svBlock omega Y)
            (fun i => T.definingTuple color S i)) rfl hoff
          ((satisfiesAt_setTuple_iff T vpred color hcolor _ _).mpr
            ⟨S, funext fun i =>
              (Assignment.setBlock_so_apply ρ (svBlock_injective omega Y) _ i).symm⟩)
        rw [ih (α.updateSO Y S) _ ?_ ?_] at hφ'
        · exact hφ'
        · intro y hy
          obtain ⟨u, hu, hblocks⟩ := hFO y hy
          refine ⟨u, hu, fun i => ?_⟩
          rw [Assignment.setBlock_so_of_forall_ne ρ _ _
            (fun j hj => fvBlock_ne_svBlock y Y i j hj.symm)]
          exact hblocks i
        · intro Z hZ i
          by_cases hZY : Z = Y
          · subst hZY
            rw [Language.Assignment.updateSO_here]
            exact Assignment.setBlock_so_apply ρ (svBlock_injective omega Z) _ i
          · rw [Assignment.setBlock_so_of_forall_ne ρ _ _
              (fun j => svBlock_ne_svBlock (Ne.symm hZY) j i),
              Language.Assignment.updateSO_other α S hZY]
            exact hSO Z ⟨hZ, fun hmem => hZY (by simpa using hmem)⟩ i
      · intro h ρ' hfo hoff hset
        obtain ⟨S, hS⟩ :=
          (satisfiesAt_setTuple_iff T vpred color hcolor ρ'
            (svBlock omega Y)).mp hset
        rw [ih (α.updateSO Y S) ρ' ?_ ?_]
        · exact h S
        · intro y hy
          obtain ⟨u, hu, hblocks⟩ := hFO y hy
          refine ⟨u, hu, fun i => ?_⟩
          rw [hoff _ (fvBlock_notMem_blockList_svBlock y Y i)]
          exact hblocks i
        · intro Z hZ i
          by_cases hZY : Z = Y
          · subst hZY
            rw [Language.Assignment.updateSO_here]
            exact (congrFun hS i).symm
          · rw [hoff _ (svBlock_notMem_blockList_svBlock hZY i),
              Language.Assignment.updateSO_other α S hZY]
            exact hSO Z ⟨hZ, fun hmem => hZY (by simpa using hmem)⟩ i

/--
The final translation display of the lecture note: for a closed `tau_P`
formula, the graph satisfies it iff the encoding satisfies the legality
sentence conjoined with the translation.
-/
theorem satisfies_legalFormula_conj_translate_iff
    (θ : Language.Formula P) (hFO : θ.freeFO = ∅) (hSO : θ.freeSO = ∅) :
    Satisfies (T.encode vpred color hcolor).toTreeModel
      (TreeLanguage.Formula.conj (SigmaTree.legalFormula P omega)
        (θ.translate omega)) ↔
      Language.Semantics.Satisfies (⟨V, G, vpred⟩ : τPGraph P) θ := by
  show SatisfiesAt _ _ _ ↔ Language.Semantics.SatisfiesAt _ _ _
  rw [satisfiesAt_conj]
  have hlegal := T.encode_satisfiesAt_legalFormula vpred color hcolor
    (Assignment.empty _)
  simp only [hlegal, true_and]
  exact satisfiesAt_translate_iff T vpred color hcolor θ _ _
    (fun x hx => absurd (hFO ▸ hx) (Set.notMem_empty x))
    (fun Y hY => absurd (hSO ▸ hY) (Set.notMem_empty Y))

end RootedTreeDecomposition
