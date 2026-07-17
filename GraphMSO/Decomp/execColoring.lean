import GraphMSO.Decomp.execNormalization

/-!
# Executable greedy bag coloring

`DecompTree.greedyColoring` computes a width-sized bag-injective coloring of
a rose-tree decomposition: the tree is walked root-first, and every vertex
receives, at its topmost bag, the first color not used by the already-colored
members of that bag.  The running-intersection property guarantees that every
already-colored member of the current bag was colored in an ancestor bag or a
previous sibling subtree and therefore lies in the current bag's parent, so
at most `omega` colors are blocked and a fresh one exists.

This replaces the `choose`-based colorings of the proof-facing pipeline with
a computable function; `normalizeCode_greedyColoring_isBagColoring` certifies
it for the code consumed by the executable checker.
-/

universe u

namespace DecompTree

variable {V : Type u} [DecidableEq V] {omega : ℕ}

/-! ## Fresh colors -/

/-- The first color of `Fin (omega + 1)` not occurring in `used`. -/
def freshColor (omega : ℕ) (used : List (Fin (omega + 1))) : Fin (omega + 1) :=
  ((List.finRange (omega + 1)).find? (fun c => decide (c ∉ used))).getD 0

theorem freshColor_notMem {used : List (Fin (omega + 1))}
    (h : used.length ≤ omega) : freshColor omega used ∉ used := by
  have hex : ∃ c : Fin (omega + 1), c ∉ used := by
    by_contra hall
    push_neg at hall
    have huniv : (Finset.univ : Finset (Fin (omega + 1))) ⊆ used.toFinset :=
      fun c _ => List.mem_toFinset.mpr (hall c)
    have hcard := Finset.card_le_card huniv
    have hlen := used.toFinset_card_le
    simp [Finset.card_univ] at hcard
    omega
  obtain ⟨c, hc⟩ := hex
  have hsome :
      ((List.finRange (omega + 1)).find? (fun c => decide (c ∉ used))).isSome := by
    rw [List.find?_isSome]
    exact ⟨c, List.mem_finRange c, by simpa using hc⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
  have hpa := List.find?_some ha
  simp only [decide_eq_true_eq] at hpa
  have hgoal : freshColor omega used = a := by
    simp only [freshColor, ha, Option.getD_some]
  rw [hgoal]
  exact hpa

/-- Colors of the already-assigned members of `bag`. -/
def usedColors (f : V → Fin (omega + 1)) (assigned bag : List V) :
    List (Fin (omega + 1)) :=
  (bag.dedup.filter (fun x => decide (x ∈ assigned))).map f

theorem mem_usedColors {f : V → Fin (omega + 1)} {assigned bag : List V}
    {x : V} (hxbag : x ∈ bag) (hxassigned : x ∈ assigned) :
    f x ∈ usedColors f assigned bag :=
  List.mem_map_of_mem
    (by simp [List.mem_filter, List.mem_dedup, hxbag, hxassigned])

/-- When some member of `bag` is unassigned, at most `omega` colors are
blocked. -/
theorem usedColors_length_le {f : V → Fin (omega + 1)} {assigned bag : List V}
    {v : V} (hv : v ∈ bag) (hvassigned : v ∉ assigned)
    (hw : bag.toFinset.card ≤ omega + 1) :
    (usedColors f assigned bag).length ≤ omega := by
  have hnodup : (bag.dedup.filter (fun x => decide (x ∈ assigned))).Nodup :=
    bag.nodup_dedup.filter _
  have hsub : (bag.dedup.filter (fun x => decide (x ∈ assigned))).toFinset ⊆
      bag.toFinset.erase v := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_filter, List.mem_dedup,
      decide_eq_true_eq] at hx
    refine Finset.mem_erase.mpr ⟨?_, List.mem_toFinset.mpr hx.1⟩
    rintro rfl
    exact hvassigned hx.2
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnodup] at hcard
  have herase : (bag.toFinset.erase v).card = bag.toFinset.card - 1 :=
    Finset.card_erase_of_mem (List.mem_toFinset.mpr hv)
  have hlen : (usedColors f assigned bag).length =
      (bag.dedup.filter (fun x => decide (x ∈ assigned))).length := by
    simp [usedColors]
  rw [hlen]
  omega

/-! ## Coloring one bag -/

/-- One greedy step: assign a fresh color to `v` unless it is already
assigned.  The fresh color avoids all colors of assigned members of `bag`. -/
def assignVertex (bag : List V) (acc : (V → Fin (omega + 1)) × List V)
    (v : V) : (V → Fin (omega + 1)) × List V :=
  if v ∈ acc.2 then acc
  else
    (fun x =>
      if x = v then freshColor omega (usedColors acc.1 acc.2 bag) else acc.1 x,
      v :: acc.2)

theorem assignVertex_fst_eq_of_mem {bag : List V}
    {acc : (V → Fin (omega + 1)) × List V} {v x : V} (hx : x ∈ acc.2) :
    (assignVertex bag acc v).1 x = acc.1 x := by
  unfold assignVertex
  by_cases hv : v ∈ acc.2
  · simp [hv]
  · have hxv : x ≠ v := fun h => hv (h ▸ hx)
    simp [hv, hxv]

theorem assignVertex_snd_mono {bag : List V}
    {acc : (V → Fin (omega + 1)) × List V} {v : V} :
    acc.2 ⊆ (assignVertex bag acc v).2 := by
  unfold assignVertex
  by_cases hv : v ∈ acc.2
  · simp [hv]
  · simp only [if_neg hv]
    exact fun x hx => List.mem_cons_of_mem v hx

theorem mem_assignVertex_snd {bag : List V}
    {acc : (V → Fin (omega + 1)) × List V} {v x : V} :
    x ∈ (assignVertex bag acc v).2 ↔ x = v ∨ x ∈ acc.2 := by
  unfold assignVertex
  by_cases hv : v ∈ acc.2
  · simp only [if_pos hv]
    constructor
    · exact Or.inr
    · rintro (rfl | hx)
      · exact hv
      · exact hx
  · simp [if_neg hv, List.mem_cons]

theorem self_mem_assignVertex_snd {bag : List V}
    {acc : (V → Fin (omega + 1)) × List V} {v : V} :
    v ∈ (assignVertex bag acc v).2 :=
  mem_assignVertex_snd.2 (Or.inl rfl)

/-- The greedy step keeps the coloring injective on the assigned part of the
bag. -/
theorem assignVertex_injOn {bag : List V}
    {acc : (V → Fin (omega + 1)) × List V} {v : V} (hv : v ∈ bag)
    (hw : bag.toFinset.card ≤ omega + 1)
    (hpre : Set.InjOn acc.1 {x | x ∈ bag ∧ x ∈ acc.2}) :
    Set.InjOn (assignVertex bag acc v).1
      {x | x ∈ bag ∧ x ∈ (assignVertex bag acc v).2} := by
  by_cases hvmem : v ∈ acc.2
  · simpa [assignVertex, hvmem] using hpre
  · have hfresh : freshColor omega (usedColors acc.1 acc.2 bag) ∉
        usedColors acc.1 acc.2 bag :=
      freshColor_notMem (usedColors_length_le hv hvmem hw)
    have hself : (assignVertex bag acc v).1 v =
        freshColor omega (usedColors acc.1 acc.2 bag) := by
      simp [assignVertex, hvmem]
    have hother : ∀ x ∈ acc.2, (assignVertex bag acc v).1 x = acc.1 x :=
      fun x hx => assignVertex_fst_eq_of_mem hx
    intro x hx y hy hxy
    rcases mem_assignVertex_snd.1 hx.2 with rfl | hxold
    · rcases mem_assignVertex_snd.1 hy.2 with rfl | hyold
      · rfl
      · exfalso
        rw [hself, hother y hyold] at hxy
        exact hfresh (hxy ▸ mem_usedColors hy.1 hyold)
    · rcases mem_assignVertex_snd.1 hy.2 with rfl | hyold
      · exfalso
        rw [hself, hother x hxold] at hxy
        exact hfresh (hxy.symm ▸ mem_usedColors hx.1 hxold)
      · rw [hother x hxold, hother y hyold] at hxy
        exact hpre ⟨hx.1, hxold⟩ ⟨hy.1, hyold⟩ hxy

/-- Assign fresh colors to every unassigned member of one bag. -/
def colorBag (bag : List V) (acc : (V → Fin (omega + 1)) × List V) :
    (V → Fin (omega + 1)) × List V :=
  bag.dedup.foldl (assignVertex bag) acc

theorem foldl_assignVertex_fst_eq_of_mem (bag xs : List V) :
    ∀ (acc : (V → Fin (omega + 1)) × List V) {x : V}, x ∈ acc.2 →
      (xs.foldl (assignVertex bag) acc).1 x = acc.1 x := by
  induction xs with
  | nil => intro acc x _; rfl
  | cons v rest ih =>
      intro acc x hx
      rw [List.foldl_cons, ih _ (assignVertex_snd_mono hx)]
      exact assignVertex_fst_eq_of_mem hx

theorem foldl_assignVertex_snd_mono (bag xs : List V) :
    ∀ acc : (V → Fin (omega + 1)) × List V,
      acc.2 ⊆ (xs.foldl (assignVertex bag) acc).2 := by
  induction xs with
  | nil => exact fun _ _ h => h
  | cons v rest ih =>
      intro acc
      rw [List.foldl_cons]
      exact fun x hx => ih _ (assignVertex_snd_mono hx)

theorem mem_foldl_assignVertex_snd (bag xs : List V) :
    ∀ (acc : (V → Fin (omega + 1)) × List V) {x : V},
      x ∈ (xs.foldl (assignVertex bag) acc).2 → x ∈ xs ∨ x ∈ acc.2 := by
  induction xs with
  | nil => intro acc x hx; exact Or.inr hx
  | cons v rest ih =>
      intro acc x hx
      rw [List.foldl_cons] at hx
      rcases ih _ hx with hx | hx
      · exact Or.inl (List.mem_cons_of_mem v hx)
      · rcases mem_assignVertex_snd.1 hx with rfl | hx
        · exact Or.inl (by simp)
        · exact Or.inr hx

theorem foldl_assignVertex_mem_snd (bag xs : List V) :
    ∀ (acc : (V → Fin (omega + 1)) × List V) {x : V}, x ∈ xs →
      x ∈ (xs.foldl (assignVertex bag) acc).2 := by
  induction xs with
  | nil => intro acc x hx; simp at hx
  | cons v rest ih =>
      intro acc x hx
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact foldl_assignVertex_snd_mono bag rest _ self_mem_assignVertex_snd
      · exact ih _ hx

theorem foldl_assignVertex_injOn (bag : List V)
    (hw : bag.toFinset.card ≤ omega + 1) (xs : List V) :
    (∀ x ∈ xs, x ∈ bag) →
      ∀ acc : (V → Fin (omega + 1)) × List V,
        Set.InjOn acc.1 {x | x ∈ bag ∧ x ∈ acc.2} →
        Set.InjOn (xs.foldl (assignVertex bag) acc).1
          {x | x ∈ bag ∧ x ∈ (xs.foldl (assignVertex bag) acc).2} := by
  induction xs with
  | nil => intro _ acc h; exact h
  | cons v rest ih =>
      intro hxs acc h
      rw [List.foldl_cons]
      exact ih (fun x hx => hxs x (List.mem_cons_of_mem v hx)) _
        (assignVertex_injOn (hxs v (by simp)) hw h)

theorem colorBag_fst_eq_of_mem {bag : List V}
    {acc : (V → Fin (omega + 1)) × List V} {x : V} (hx : x ∈ acc.2) :
    (colorBag bag acc).1 x = acc.1 x :=
  foldl_assignVertex_fst_eq_of_mem bag bag.dedup acc hx

theorem colorBag_snd_mono {bag : List V}
    {acc : (V → Fin (omega + 1)) × List V} :
    acc.2 ⊆ (colorBag bag acc).2 :=
  foldl_assignVertex_snd_mono bag bag.dedup acc

theorem mem_colorBag_snd {bag : List V}
    {acc : (V → Fin (omega + 1)) × List V} {x : V}
    (hx : x ∈ (colorBag bag acc).2) : x ∈ bag ∨ x ∈ acc.2 := by
  rcases mem_foldl_assignVertex_snd bag bag.dedup acc hx with h | h
  · exact Or.inl (List.mem_dedup.mp h)
  · exact Or.inr h

theorem mem_colorBag_of_mem_bag {bag : List V}
    {acc : (V → Fin (omega + 1)) × List V} {x : V} (hx : x ∈ bag) :
    x ∈ (colorBag bag acc).2 :=
  foldl_assignVertex_mem_snd bag bag.dedup acc (List.mem_dedup.mpr hx)

/-- After `colorBag`, the coloring is injective on the whole bag. -/
theorem colorBag_injOn {bag : List V}
    {acc : (V → Fin (omega + 1)) × List V}
    (hw : bag.toFinset.card ≤ omega + 1)
    (h : Set.InjOn acc.1 {x | x ∈ bag ∧ x ∈ acc.2}) :
    Set.InjOn (colorBag bag acc).1 {x | x ∈ bag} := by
  have h2 := foldl_assignVertex_injOn bag hw bag.dedup
    (fun x hx => List.mem_dedup.mp hx) acc h
  refine h2.mono ?_
  intro x hx
  exact ⟨hx, mem_colorBag_of_mem_bag hx⟩

/-! ## The greedy tree walk -/

/-- The greedy tree walk: color the root bag, then recurse into the child
subtrees left to right, threading the partial coloring. -/
def greedyAux (omega : ℕ) :
    DecompTree V → ((V → Fin (omega + 1)) × List V) →
      ((V → Fin (omega + 1)) × List V)
  | node bag children => fun acc =>
      children.attach.foldl (fun a c => greedyAux omega c.1 a)
        (colorBag bag acc)
decreasing_by
  simp
  have := List.sizeOf_lt_of_mem c.2
  omega

theorem greedyAux_node (omega : ℕ) (bag : List V)
    (children : List (DecompTree V))
    (acc : (V → Fin (omega + 1)) × List V) :
    greedyAux omega (node bag children) acc =
      children.foldl (fun a c => greedyAux omega c a) (colorBag bag acc) := by
  simp only [greedyAux]
  conv_rhs => rw [← List.attach_map_subtype_val children]
  rw [List.foldl_map]

/-- Entry invariant of one `greedyAux` run: assigned vertices occurring in
the subtree lie in its root bag, injectively colored there. -/
private abbrev GreedyPre (t : DecompTree V)
    (acc : (V → Fin (omega + 1)) × List V) : Prop :=
  (∀ v, t.Occurs v → v ∈ acc.2 → v ∈ t.rootBag) ∧
  Set.InjOn acc.1 {x | x ∈ t.rootBag ∧ x ∈ acc.2}

/-- Postconditions of one `greedyAux` run: previously assigned values are
unchanged, exactly the occurring vertices are newly assigned, and the
resulting coloring is injective on every bag of the subtree. -/
private abbrev GreedyPost (t : DecompTree V)
    (acc res : (V → Fin (omega + 1)) × List V) : Prop :=
  (∀ x ∈ acc.2, res.1 x = acc.1 x) ∧
  (∀ x ∈ res.2, x ∈ acc.2 ∨ t.Occurs x) ∧
  (∀ x, t.Occurs x → x ∈ res.2) ∧
  acc.2 ⊆ res.2 ∧
  (∀ ⦃L⦄, t.HasBag L → Set.InjOn res.1 {x | x ∈ L})

private theorem foldl_greedyAux_spec (bag : List V) :
    ∀ cs : List (DecompTree V),
      (∀ c ∈ cs, ∀ acc, GreedyPre c acc →
        GreedyPost c acc (greedyAux omega c acc)) →
      (∀ c ∈ cs, ∀ v ∈ bag, c.Occurs v → v ∈ c.rootBag) →
      cs.Pairwise (fun c₁ c₂ => ∀ v, c₁.Occurs v → c₂.Occurs v → v ∈ bag) →
      ∀ acc : (V → Fin (omega + 1)) × List V,
        bag ⊆ acc.2 → Set.InjOn acc.1 {x | x ∈ bag} →
        (∀ c ∈ cs, ∀ v, c.Occurs v → v ∈ acc.2 → v ∈ bag) →
        (∀ x ∈ acc.2,
          (cs.foldl (fun a c => greedyAux omega c a) acc).1 x = acc.1 x) ∧
        (∀ x ∈ (cs.foldl (fun a c => greedyAux omega c a) acc).2,
          x ∈ acc.2 ∨ ∃ c ∈ cs, c.Occurs x) ∧
        (∀ c ∈ cs, ∀ x, c.Occurs x →
          x ∈ (cs.foldl (fun a c => greedyAux omega c a) acc).2) ∧
        acc.2 ⊆ (cs.foldl (fun a c => greedyAux omega c a) acc).2 ∧
        (∀ c ∈ cs, ∀ ⦃L⦄, c.HasBag L →
          Set.InjOn (cs.foldl (fun a c => greedyAux omega c a) acc).1
            {x | x ∈ L}) := by
  intro cs
  induction cs with
  | nil =>
      intro _ _ _ acc _ _ _
      refine ⟨fun _ _ => rfl, fun x hx => Or.inl hx, ?_, fun _ h => h, ?_⟩
      · intro c hc
        simp at hc
      · intro c hc
        simp at hc
  | cons c cs ihcs =>
      intro hspec hdown hpair acc hbagsub hbaginj hA
      rw [List.foldl_cons]
      rw [List.pairwise_cons] at hpair
      have hpre : GreedyPre c acc := by
        constructor
        · intro v hocc hmem
          exact hdown c (by simp) v (hA c (by simp) v hocc hmem) hocc
        · refine hbaginj.mono ?_
          intro x hx
          exact hA c (by simp) x (occurs_of_mem_rootBag hx.1) hx.2
      obtain ⟨hP1, hP2, hP3, hP4, hP5⟩ := hspec c (by simp) acc hpre
      have hbagsub₂ : bag ⊆ (greedyAux omega c acc).2 :=
        fun x hx => hP4 (hbagsub hx)
      have hbaginj₂ : Set.InjOn (greedyAux omega c acc).1 {x | x ∈ bag} :=
        hbaginj.congr (fun x hx => (hP1 x (hbagsub hx)).symm)
      have hA₂ : ∀ c' ∈ cs, ∀ v, c'.Occurs v →
          v ∈ (greedyAux omega c acc).2 → v ∈ bag := by
        intro c' hc' v hocc hmem
        rcases hP2 v hmem with hmem | hoccc
        · exact hA c' (by simp [hc']) v hocc hmem
        · exact hpair.1 c' hc' v hoccc hocc
      obtain ⟨hQ1, hQ2, hQ3, hQ4, hQ5⟩ := ihcs
        (fun c' hc' => hspec c' (by simp [hc']))
        (fun c' hc' => hdown c' (by simp [hc']))
        hpair.2 _ hbagsub₂ hbaginj₂ hA₂
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rw [hQ1 x (hP4 hx)]
        exact hP1 x hx
      · intro x hx
        rcases hQ2 x hx with hx | ⟨c', hc', hocc⟩
        · rcases hP2 x hx with hx | hocc
          · exact Or.inl hx
          · exact Or.inr ⟨c, by simp, hocc⟩
        · exact Or.inr ⟨c', by simp [hc'], hocc⟩
      · intro c' hc' x hocc
        rcases List.mem_cons.mp hc' with rfl | hc'
        · exact hQ4 (hP3 x hocc)
        · exact hQ3 c' hc' x hocc
      · exact fun x hx => hQ4 (hP4 hx)
      · intro c' hc' L hL
        rcases List.mem_cons.mp hc' with rfl | hc'
        · refine (hP5 hL).congr ?_
          intro x hx
          exact (hQ1 x (hP3 x ⟨L, hL, hx⟩)).symm
        · exact hQ5 c' hc' hL

private theorem greedyAux_spec (t : DecompTree V) :
    t.HasWidth omega → t.RunningIntersection →
      ∀ acc, GreedyPre t acc → GreedyPost t acc (greedyAux omega t acc) := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      rintro hw ⟨hdown, hpair, hchildren⟩ acc ⟨hA, hinj⟩
      rw [greedyAux_node]
      have hwbag : bag.toFinset.card ≤ omega + 1 :=
        hw bag (HasBag.root bag children)
      have hbaginj : Set.InjOn (colorBag bag acc).1 {x | x ∈ bag} :=
        colorBag_injOn hwbag hinj
      have hbagsub : bag ⊆ (colorBag bag acc).2 :=
        fun x hx => mem_colorBag_of_mem_bag hx
      have hAfold : ∀ c ∈ children, ∀ v, c.Occurs v →
          v ∈ (colorBag bag acc).2 → v ∈ bag := by
        intro c hc v hocc hmem
        rcases mem_colorBag_snd hmem with hv | hv
        · exact hv
        · exact hA v (occurs_node_iff.2 (Or.inr ⟨c, hc, hocc⟩)) hv
      obtain ⟨hF1, hF2, hF3, hF4, hF5⟩ := foldl_greedyAux_spec bag children
        (fun c hc => ih c hc (hw.of_mem_children hc) (hchildren c hc))
        hdown hpair _ hbagsub hbaginj hAfold
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rw [hF1 x (colorBag_snd_mono hx)]
        exact colorBag_fst_eq_of_mem hx
      · intro x hx
        rcases hF2 x hx with hx | ⟨c, hc, hocc⟩
        · rcases mem_colorBag_snd hx with hx | hx
          · exact Or.inr (occurs_node_iff.2 (Or.inl hx))
          · exact Or.inl hx
        · exact Or.inr (occurs_node_iff.2 (Or.inr ⟨c, hc, hocc⟩))
      · intro x hocc
        rcases occurs_node_iff.1 hocc with hx | ⟨c, hc, hocc⟩
        · exact hF4 (mem_colorBag_of_mem_bag hx)
        · exact hF3 c hc x hocc
      · exact fun x hx => hF4 (colorBag_snd_mono hx)
      · intro L hL
        rcases hasBag_node_iff.1 hL with rfl | ⟨c, hc, hcL⟩
        · exact hbaginj.congr (fun x hx => (hF1 x (hbagsub hx)).symm)
        · exact hF5 c hc hcL

/-! ## The coloring and its certificate -/

/-- The computable greedy bag coloring of a rose-tree decomposition.
Vertices outside every bag receive the default color `0`. -/
def greedyColoring (t : DecompTree V) (omega : ℕ) : V → Fin (omega + 1) :=
  (greedyAux omega t (fun _ => (0 : Fin (omega + 1)), ([] : List V))).1

/-- The greedy coloring is injective on every bag of a bounded-width rose
tree satisfying the running-intersection property. -/
theorem greedyColoring_isBagColoring (t : DecompTree V) (omega : ℕ)
    (hw : t.HasWidth omega) (hri : t.RunningIntersection) :
    t.IsBagColoring (t.greedyColoring omega) := by
  have hpre : GreedyPre t (fun _ => (0 : Fin (omega + 1)), ([] : List V)) := by
    constructor
    · intro v _ hmem
      simp at hmem
    · intro x hx
      simp at hx
  intro L hL
  exact (greedyAux_spec t hw hri _ hpre).2.2.2.2 hL

/-- The greedy coloring certifies the normalized code: this is exactly the
coloring hypothesis consumed by the verified executable checker. -/
theorem normalizeCode_greedyColoring_isBagColoring (t : DecompTree V)
    (omega : ℕ) (hw : t.HasWidth omega) (hri : t.RunningIntersection) :
    t.normalizeCode.IsBagColoring (t.greedyColoring omega) :=
  normalizeCode_isBagColoring t (greedyColoring_isBagColoring t omega hw hri)

end DecompTree
