import GraphMSO.Decomp.treeModel
import GraphMSO.Decomp.definingPairs

/-!
# Recognition formulas over an encoding

The recognition lemmas of the lecture note, stated over the Σ-tree encoding
of a bag-colored decomposition as recommended by the issues note:

* `SigmaTree.satisfiesAt_legalFormula_iff` — the legality sentence
  characterizes legal Σ-trees (the note's `phi_legal` lemma, proved for
  arbitrary Σ-trees).
* `RootedTreeDecomposition.satisfiesAt_definingPair_iff` — the formula
  `phi_vtx_i` recognizes exactly the defining pairs (the note's Lemma vtx-i,
  in the encoded form of the recognition corollary).
* `RootedTreeDecomposition.satisfiesAt_vtxTuple_iff` and
  `satisfiesAt_setTuple_iff` — the tuple formulas `phi_vtx` and `phi_set`
  recognize the defining tuples of vertices and of vertex sets.

The proofs consume three prepared layers: the formula characterizations of
`GraphMSO.treeLanguage.semantics`, the model bridge of
`GraphMSO.Decomp.treeModel`, and the combinatorial defining-pair lemmas of
`GraphMSO.Decomp.definingPairs`.
-/

open GraphMSO.TreeLanguage GraphMSO.TreeLanguage.Semantics

namespace SigmaTree

variable {P : Type*} {omega : ℕ}

/-- A node with no child-relation parent is the root. -/
theorem forall_not_isChild_iff (S : SigmaTree P omega) (t : S.Node) :
    (∀ p : S.Node, ¬ S.IsChild p t) ↔ t = S.root := by
  constructor
  · intro h
    by_contra hroot
    exact h (S.parent t) ⟨hroot, rfl⟩
  · rintro rfl p hp
    exact hp.1 rfl

/-- The legality sentence over the Σ-letter alphabet: the root letter has an
empty boundary, and every child letter is compatible with its parent's. -/
def legalFormula (P : Type*) (omega : ℕ) : Formula (SigmaLetter P omega) :=
  Formula.legal {a | a.RootEmpty} {q | SigmaLetter.Compatible q.1 q.2}

/-- The lecture note's legality lemma: the legality sentence characterizes
the legal Σ-trees. -/
theorem satisfiesAt_legalFormula_iff (S : SigmaTree P omega)
    (ρ : Assignment S.toTreeModel) :
    SatisfiesAt S.toTreeModel (legalFormula P omega) ρ ↔ S.IsLegal := by
  rw [legalFormula, satisfiesAt_legal_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1 S.root ((S.forall_not_isChild_iff S.root).mpr rfl), ?_⟩
    intro t ht
    rcases h2 t with hp | ⟨p, hpc, hcomp⟩
    · exact absurd ((S.forall_not_isChild_iff t).mp hp) ht
    · exact hpc.2 ▸ hcomp
  · rintro ⟨hroot, hcomp⟩
    constructor
    · intro n hn
      have hn_root := (S.forall_not_isChild_iff n).mp hn
      rw [hn_root]
      exact hroot
    · intro n
      by_cases hn : n = S.root
      · exact Or.inl ((S.forall_not_isChild_iff n).mpr hn)
      · exact Or.inr ⟨S.parent n, ⟨hn, rfl⟩, hcomp n hn⟩

end SigmaTree

namespace RootedTreeDecomposition

open SigmaTree

variable {V : Type*} [Fintype V] {G : SimpleGraph V}
variable {P : Type*} {omega : ℕ}
variable (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color)

/-- Encodings satisfy the legality sentence. -/
theorem encode_satisfiesAt_legalFormula
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (legalFormula P omega) ρ :=
  ((T.encode vpred color hcolor).satisfiesAt_legalFormula_iff ρ).mpr
    (T.encode_isLegal vpred color hcolor)

/-! ## The defining-pair formula -/

private theorem comp_A_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Z : SOVar) (i : BagColorSet omega) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.forallFO 0 (Formula.impl (Formula.inSet 0 Z)
        (Formula.labelMem {a | a.HasVertex i} 0))) ρ ↔
      ∀ t ∈ ρ.so Z, ∃ v ∈ T.bag t, color v = i := by
  rw [satisfiesAt_forallFO]
  refine forall_congr' fun t => ?_
  rw [satisfiesAt_impl,
    satisfiesAt_inSet_iff _ (Assignment.updateFO_here ρ 0 t),
    satisfiesAt_labelMem_iff _ (Assignment.updateFO_here ρ 0 t),
    T.encode_toTreeModel_label vpred color hcolor,
    Set.mem_setOf_eq, encodeLetter_hasVertex_iff, Set.mem_image]
  exact Iff.rfl

private theorem comp_Rnt_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Z : SOVar) (i : BagColorSet omega) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.forallFO 0 (Formula.impl
        (Formula.conj (Formula.inSet 0 Z) (Formula.neg (Formula.top 0 Z)))
        (Formula.labelMem {a | a.RootContains i} 0))) ρ ↔
      ∀ t : T.Node,
        (t ∈ ρ.so Z ∧
          ¬(t ∈ ρ.so Z ∧ (T.T.induce (ρ.so Z)).Connected ∧
            ((∀ p, ¬ T.IsChild p t) ∨ ∃ p, T.IsChild p t ∧ p ∉ ρ.so Z))) ->
        ∃ v ∈ T.adhesion t, color v = i := by
  rw [satisfiesAt_forallFO]
  refine forall_congr' fun t => ?_
  rw [satisfiesAt_impl, satisfiesAt_conj, satisfiesAt_neg,
    satisfiesAt_inSet_iff _ (Assignment.updateFO_here ρ 0 t),
    satisfiesAt_top_iff _ (Assignment.updateFO_here ρ 0 t),
    T.encode_toTreeModel_graph vpred color hcolor,
    satisfiesAt_labelMem_iff _ (Assignment.updateFO_here ρ 0 t),
    T.encode_toTreeModel_label vpred color hcolor,
    Set.mem_setOf_eq, encodeLetter_rootContains_iff, Set.mem_image]
  exact Iff.rfl

private theorem comp_Rtop_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Z : SOVar) (i : BagColorSet omega) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.forallFO 0 (Formula.impl (Formula.top 0 Z)
        (Formula.neg (Formula.labelMem {a | a.RootContains i} 0)))) ρ ↔
      ∀ t : T.Node,
        (t ∈ ρ.so Z ∧ (T.T.induce (ρ.so Z)).Connected ∧
          ((∀ p, ¬ T.IsChild p t) ∨ ∃ p, T.IsChild p t ∧ p ∉ ρ.so Z)) ->
        ¬∃ v ∈ T.adhesion t, color v = i := by
  rw [satisfiesAt_forallFO]
  refine forall_congr' fun t => ?_
  rw [satisfiesAt_impl, satisfiesAt_neg,
    satisfiesAt_top_iff _ (Assignment.updateFO_here ρ 0 t),
    T.encode_toTreeModel_graph vpred color hcolor,
    satisfiesAt_labelMem_iff _ (Assignment.updateFO_here ρ 0 t),
    T.encode_toTreeModel_label vpred color hcolor,
    Set.mem_setOf_eq, encodeLetter_rootContains_iff, Set.mem_image]
  exact Iff.rfl

private theorem comp_Rdang_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Z : SOVar) (i : BagColorSet omega) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.forallFO 0 (Formula.impl (Formula.dangle 0 Z)
        (Formula.neg (Formula.labelMem {a | a.RootContains i} 0)))) ρ ↔
      ∀ t : T.Node,
        (t ∉ ρ.so Z ∧ ∃ p, T.IsChild p t ∧ p ∈ ρ.so Z) ->
        ¬∃ v ∈ T.adhesion t, color v = i := by
  rw [satisfiesAt_forallFO]
  refine forall_congr' fun t => ?_
  rw [satisfiesAt_impl, satisfiesAt_neg,
    satisfiesAt_dangle_iff _ (Assignment.updateFO_here ρ 0 t),
    satisfiesAt_labelMem_iff _ (Assignment.updateFO_here ρ 0 t),
    T.encode_toTreeModel_label vpred color hcolor,
    Set.mem_setOf_eq, encodeLetter_rootContains_iff, Set.mem_image]
  exact Iff.rfl

/-- The note's Lemma vtx-i over an encoding: the defining-pair formula holds
of `Z` iff the assigned set and the color form a defining pair. -/
theorem satisfiesAt_definingPair_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Z : SOVar) (i : BagColorSet omega) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.definingPair {a | a.HasVertex i} {a | a.RootContains i} Z) ρ ↔
      T.IsDefiningPair color (ρ.so Z) i := by
  rw [Formula.definingPair, satisfiesAt_conj, satisfiesAt_conj,
    satisfiesAt_conj, satisfiesAt_conj, satisfiesAt_conn_iff,
    T.encode_toTreeModel_graph vpred color hcolor,
    comp_A_iff T vpred color hcolor ρ Z i,
    comp_Rnt_iff T vpred color hcolor ρ Z i,
    comp_Rtop_iff T vpred color hcolor ρ Z i,
    comp_Rdang_iff T vpred color hcolor ρ Z i]
  constructor
  · rintro ⟨hUconn, hA, hRnt, hRtop, hRdang⟩
    have hUne : (ρ.so Z).Nonempty :=
      Set.nonempty_coe_sort.mp hUconn.nonempty
    have hUpre : (T.T.induce (ρ.so Z)).Preconnected := hUconn.preconnected
    refine ⟨hUne, hUpre, hA, ?_, ?_, ?_⟩
    · intro t ht htroot hparentU
      refine hRnt t ⟨ht, ?_⟩
      rintro ⟨-, -, hcase⟩
      rcases hcase with hnop | ⟨p, hpc, hpU⟩
      · exact htroot ((T.forall_not_isChild_iff t).mp hnop)
      · exact hpU (hpc.2.symm ▸ hparentU)
    · intro t ht hparentU v hv hcv
      by_cases hroot : t = T.root
      · rw [hroot, T.adhesion_root] at hv
        exact hv
      · exact hRtop t
          ⟨ht, hUconn, Or.inr ⟨T.parent t, isChild_parent hroot, hparentU⟩⟩
          ⟨v, hv, hcv⟩
    · intro x hx hparentU v hv hcv
      have hx_ne_root : x ≠ T.root := by
        intro h
        subst h
        rw [T.parent_root] at hparentU
        exact hx hparentU
      exact hRdang x ⟨hx, T.parent x, isChild_parent hx_ne_root, hparentU⟩
        ⟨v, hv, hcv⟩
  · rintro ⟨hUne, hUpre, h3, h4, h5, h6⟩
    have hUconn : (T.T.induce (ρ.so Z)).Connected := by
      haveI : Nonempty ↥(ρ.so Z) := Set.nonempty_coe_sort.mpr hUne
      exact ⟨hUpre⟩
    refine ⟨hUconn, h3, ?_, ?_, ?_⟩
    · rintro t ⟨ht, hnottop⟩
      have htroot : t ≠ T.root := by
        intro h
        exact hnottop ⟨ht, hUconn, Or.inl ((T.forall_not_isChild_iff t).mpr h)⟩
      have hparentU : T.parent t ∈ ρ.so Z := by
        by_contra hpu
        exact hnottop
          ⟨ht, hUconn, Or.inr ⟨T.parent t, isChild_parent htroot, hpu⟩⟩
      exact h4 t ht htroot hparentU
    · rintro t ⟨ht, -, hcase⟩ ⟨v, hv, hcv⟩
      rcases hcase with hnop | ⟨p, hpc, hpU⟩
      · have ht_root := (T.forall_not_isChild_iff t).mp hnop
        rw [ht_root, T.adhesion_root] at hv
        exact hv
      · exact h5 t ht (hpc.2 ▸ hpU) v hv hcv
    · rintro x ⟨hx, p, hpc, hpU⟩ ⟨v, hv, hcv⟩
      exact h6 x hx (hpc.2 ▸ hpU) v hv hcv

/-! ## The tuple formulas -/

/-- The note's Lemma vtx over an encoding: the tuple formula `phi_vtx` holds
iff the assigned tuple is the defining tuple of a (unique) vertex. -/
theorem satisfiesAt_vtxTuple_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Zs : Fin (omega + 1) → SOVar) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.vtxTuple (fun i => {a | a.HasVertex i})
        (fun i => {a | a.RootContains i}) Zs) ρ ↔
      ∃ v : V, ∀ i, ρ.so (Zs i) = T.definingTuple color {v} i := by
  rw [Formula.vtxTuple, satisfiesAt_disjList]
  simp only [List.mem_map, List.mem_finRange, true_and, exists_exists_eq_and,
    satisfiesAt_conj, satisfiesAt_conjList, List.mem_filter,
    decide_eq_true_eq, satisfiesAt_definingPair_iff T vpred color hcolor ρ]
  constructor
  · rintro ⟨i, hpair, hemp⟩
    obtain ⟨v, hvc, hvB⟩ := exists_of_isDefiningPair hcolor hpair
    refine ⟨v, fun j => ?_⟩
    rw [T.definingTuple_singleton v j]
    by_cases hj : j = i
    · subst hj
      rw [if_pos hvc, hvB]
    · rw [if_neg (by rw [hvc]; exact fun h => hj h.symm)]
      have hj' := hemp (Formula.empty (Zs j)) ⟨j, hj, rfl⟩
      rwa [satisfiesAt_empty_iff] at hj'
  · rintro ⟨v, hv⟩
    refine ⟨color v, ?_, ?_⟩
    · have hcv := hv (color v)
      rw [T.definingTuple_singleton v (color v), if_pos rfl] at hcv
      rw [hcv]
      exact isDefiningPair_BAGS hcolor v
    · rintro φ ⟨j, hj, rfl⟩
      rw [satisfiesAt_empty_iff]
      have hcv := hv j
      rwa [T.definingTuple_singleton v j, if_neg (fun h => hj h.symm)] at hcv

/-- The note's Lemma set over an encoding: the tuple formula `phi_set` holds
iff the assigned tuple is the defining tuple of a vertex set. -/
theorem satisfiesAt_setTuple_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Zs : Fin (omega + 1) → SOVar) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.setTuple (fun i => {a | a.HasVertex i})
        (fun i => {a | a.RootContains i}) Zs) ρ ↔
      ∃ S : Set V, T.definingTuple color S = fun i => ρ.so (Zs i) := by
  rw [exists_definingTuple_eq_iff, Formula.setTuple, satisfiesAt_conjList]
  simp only [List.mem_map, List.mem_finRange, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  refine forall_congr' fun i => ?_
  have hne : Zs i ≠ Zs i + 1 := Ne.symm (Nat.succ_ne_self (Zs i))
  rw [satisfiesAt_forallFO]
  constructor
  · intro h x hx
    have hx' := h x
    rw [satisfiesAt_impl,
      satisfiesAt_inSet_iff _ (Assignment.updateFO_here ρ 0 x),
      satisfiesAt_existsSO] at hx'
    obtain ⟨Y, hY⟩ := hx' hx
    rw [satisfiesAt_conj, satisfiesAt_conj, satisfiesAt_subset_iff,
      satisfiesAt_inSet_iff _
        (show ((ρ.updateFO 0 x).updateSO (Zs i + 1) Y).fo 0 = some x from
          Assignment.updateFO_here ρ 0 x),
      satisfiesAt_definingPair_iff T vpred color hcolor] at hY
    simp only [Assignment.updateSO_here, Assignment.updateSO_other,
      Assignment.updateFO_so, ne_eq, hne, not_false_iff] at hY
    obtain ⟨hYsub, hxY, hYpair⟩ := hY
    obtain ⟨v, hvc, hvB⟩ := exists_of_isDefiningPair hcolor hYpair
    exact ⟨Y, hYsub, hxY, v, hvc, hvB⟩
  · intro h x
    rw [satisfiesAt_impl,
      satisfiesAt_inSet_iff _ (Assignment.updateFO_here ρ 0 x),
      satisfiesAt_existsSO]
    intro hx
    obtain ⟨U', hU'sub, hxU', v, hvc, hvB⟩ := h x hx
    refine ⟨U', ?_⟩
    rw [satisfiesAt_conj, satisfiesAt_conj, satisfiesAt_subset_iff,
      satisfiesAt_inSet_iff _
        (show ((ρ.updateFO 0 x).updateSO (Zs i + 1) U').fo 0 = some x from
          Assignment.updateFO_here ρ 0 x),
      satisfiesAt_definingPair_iff T vpred color hcolor]
    simp only [Assignment.updateSO_here, Assignment.updateSO_other,
      Assignment.updateFO_so, ne_eq, hne, not_false_iff]
    refine ⟨hU'sub, hxU', ?_⟩
    rw [isDefiningPair_iff hcolor _ i]
    exact ⟨v, hvc, hvB⟩

/-! ## The atomic formulas -/

private theorem adj_witness_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Xs Ys : Fin (omega + 1) → SOVar) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.disjList ((List.finRange (omega + 1)).map fun i =>
        Formula.disjList ((List.finRange (omega + 1)).map fun j =>
          Formula.existsFO 0 (Formula.conj (Formula.inSet 0 (Xs i))
            (Formula.conj (Formula.inSet 0 (Ys j))
              (Formula.labelMem {a | a.AdjOnColors i j} 0)))))) ρ ↔
      ∃ (i j : Fin (omega + 1)) (t : T.Node),
        t ∈ ρ.so (Xs i) ∧ t ∈ ρ.so (Ys j) ∧
          (T.encodeLetter vpred color hcolor t).AdjOnColors i j := by
  simp only [satisfiesAt_disjList, List.mem_map, List.mem_finRange, true_and,
    exists_exists_eq_and]
  simp only [Semantics.SatisfiesAt, Assignment.updateFO_here,
    Assignment.updateFO_so, Option.some.injEq, exists_eq_left',
    Set.mem_setOf_eq]
  exact Iff.rfl

private theorem pred_witness_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Xs : Fin (omega + 1) → SOVar) (p : P) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.disjList ((List.finRange (omega + 1)).map fun i =>
        Formula.existsFO 0 (Formula.conj (Formula.inSet 0 (Xs i))
          (Formula.labelMem {a | a.TagOnColor p i} 0)))) ρ ↔
      ∃ (i : Fin (omega + 1)) (t : T.Node),
        t ∈ ρ.so (Xs i) ∧
          (T.encodeLetter vpred color hcolor t).TagOnColor p i := by
  simp only [satisfiesAt_disjList, List.mem_map, List.mem_finRange, true_and,
    exists_exists_eq_and]
  simp only [Semantics.SatisfiesAt, Assignment.updateFO_here,
    Assignment.updateFO_so, Option.some.injEq, exists_eq_left',
    Set.mem_setOf_eq]
  exact Iff.rfl

private theorem eq_witness_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Xs Ys : Fin (omega + 1) → SOVar) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.conjList ((List.finRange (omega + 1)).map fun i =>
        Formula.setEq (Xs i) (Ys i))) ρ ↔
      ∀ i : Fin (omega + 1), ρ.so (Xs i) = ρ.so (Ys i) := by
  simp only [satisfiesAt_conjList, List.mem_map, List.mem_finRange, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  exact forall_congr' fun i => satisfiesAt_setEq_iff ρ (Xs i) (Ys i)

private theorem cont_witness_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Xs Ys : Fin (omega + 1) → SOVar) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.disjList ((List.finRange (omega + 1)).map fun i =>
        Formula.conj (Formula.nonempty (Xs i))
          (Formula.subset (Xs i) (Ys i)))) ρ ↔
      ∃ i : Fin (omega + 1),
        (ρ.so (Xs i)).Nonempty ∧ ρ.so (Xs i) ⊆ ρ.so (Ys i) := by
  simp only [satisfiesAt_disjList, List.mem_map, List.mem_finRange, true_and,
    exists_exists_eq_and, satisfiesAt_conj]
  exact exists_congr fun i =>
    and_congr (satisfiesAt_nonempty_iff ρ (Xs i))
      (satisfiesAt_subset_iff ρ (Xs i) (Ys i))

/-- The note's adjacency lemma over an encoding: on defining tuples of `u`
and `w`, the formula `phi_adj` holds iff `u` and `w` are adjacent. -/
theorem satisfiesAt_adjTuple_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Xs Ys : Fin (omega + 1) → SOVar) {u w : V}
    (hX : ∀ i, ρ.so (Xs i) = T.definingTuple color {u} i)
    (hY : ∀ i, ρ.so (Ys i) = T.definingTuple color {w} i) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.adjTuple (fun i => {a | a.HasVertex i})
        (fun i => {a | a.RootContains i})
        (fun i j => {a | a.AdjOnColors i j}) Xs Ys) ρ ↔
      G.Adj u w := by
  rw [Formula.adjTuple, satisfiesAt_conj, satisfiesAt_conj,
    adj_witness_iff T vpred color hcolor ρ Xs Ys]
  have h1 := (satisfiesAt_vtxTuple_iff T vpred color hcolor ρ Xs).mpr ⟨u, hX⟩
  have h2 := (satisfiesAt_vtxTuple_iff T vpred color hcolor ρ Ys).mpr ⟨w, hY⟩
  simp only [h1, h2, true_and]
  constructor
  · rintro ⟨i, j, t, htX, htY, hadj⟩
    rw [hX i, mem_definingTuple_singleton_iff] at htX
    rw [hY j, mem_definingTuple_singleton_iff] at htY
    obtain ⟨rfl, htu⟩ := htX
    obtain ⟨rfl, htw⟩ := htY
    exact (encodeLetter_adjOnColors_iff_adj vpred hcolor htu htw).mp hadj
  · intro hadj
    obtain ⟨t, htu, htw, hadjc⟩ :=
      (adj_iff_exists_mem_BAGS_adjOnColors vpred hcolor u w).mp hadj
    refine ⟨color u, color w, t, ?_, ?_, hadjc⟩
    · rw [hX (color u)]
      exact mem_definingTuple_singleton_iff.mpr ⟨rfl, htu⟩
    · rw [hY (color w)]
      exact mem_definingTuple_singleton_iff.mpr ⟨rfl, htw⟩

/-- The note's unary-predicate lemma over an encoding: on the defining tuple
of `v`, the formula `phi_Q` holds iff the predicate holds of `v`. -/
theorem satisfiesAt_predTuple_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Xs : Fin (omega + 1) → SOVar) (p : P) {v : V}
    (hX : ∀ i, ρ.so (Xs i) = T.definingTuple color {v} i) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.predTuple (fun i => {a | a.HasVertex i})
        (fun i => {a | a.RootContains i})
        (fun i => {a | a.TagOnColor p i}) Xs) ρ ↔
      vpred p v := by
  rw [Formula.predTuple, satisfiesAt_conj,
    pred_witness_iff T vpred color hcolor ρ Xs p]
  have h1 := (satisfiesAt_vtxTuple_iff T vpred color hcolor ρ Xs).mpr ⟨v, hX⟩
  simp only [h1, true_and]
  constructor
  · rintro ⟨i, t, htX, htag⟩
    rw [hX i, mem_definingTuple_singleton_iff] at htX
    obtain ⟨rfl, htv⟩ := htX
    exact (encodeLetter_tagOnColor_iff_vpred vpred hcolor htv p).mp htag
  · intro hp
    obtain ⟨t, htv, htag⟩ :=
      (vpred_iff_exists_mem_BAGS_tagOnColor vpred hcolor p v).mp hp
    refine ⟨color v, t, ?_, htag⟩
    rw [hX (color v)]
    exact mem_definingTuple_singleton_iff.mpr ⟨rfl, htv⟩

/-- The note's equality lemma over an encoding: on defining tuples of `u`
and `w`, the formula `phi_eq` holds iff `u = w`. -/
theorem satisfiesAt_eqTuple_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Xs Ys : Fin (omega + 1) → SOVar) {u w : V}
    (hX : ∀ i, ρ.so (Xs i) = T.definingTuple color {u} i)
    (hY : ∀ i, ρ.so (Ys i) = T.definingTuple color {w} i) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.eqTuple (fun i => {a | a.HasVertex i})
        (fun i => {a | a.RootContains i}) Xs Ys) ρ ↔
      u = w := by
  rw [Formula.eqTuple, satisfiesAt_conj, satisfiesAt_conj,
    eq_witness_iff T vpred color hcolor ρ Xs Ys]
  have h1 := (satisfiesAt_vtxTuple_iff T vpred color hcolor ρ Xs).mpr ⟨u, hX⟩
  have h2 := (satisfiesAt_vtxTuple_iff T vpred color hcolor ρ Ys).mpr ⟨w, hY⟩
  simp only [h1, h2, true_and]
  constructor
  · intro h
    refine eq_of_definingTuple_singleton_eq hcolor fun i => ?_
    rw [← hX i, ← hY i]
    exact h i
  · rintro rfl i
    rw [hX i, hY i]

/-- The note's containment lemma over an encoding: on the defining tuple of
`v` and the defining tuple of a set `S`, the formula `phi_cont` holds iff
`v ∈ S`. -/
theorem satisfiesAt_contTuple_iff
    (ρ : Assignment (T.encode vpred color hcolor).toTreeModel)
    (Xs Ys : Fin (omega + 1) → SOVar) {v : V} {S : Set V}
    (hX : ∀ i, ρ.so (Xs i) = T.definingTuple color {v} i)
    (hY : ∀ i, ρ.so (Ys i) = T.definingTuple color S i) :
    SatisfiesAt (T.encode vpred color hcolor).toTreeModel
      (Formula.contTuple (fun i => {a | a.HasVertex i})
        (fun i => {a | a.RootContains i}) Xs Ys) ρ ↔
      v ∈ S := by
  rw [Formula.contTuple, satisfiesAt_conj, satisfiesAt_conj,
    cont_witness_iff T vpred color hcolor ρ Xs Ys]
  have h1 := (satisfiesAt_vtxTuple_iff T vpred color hcolor ρ Xs).mpr ⟨v, hX⟩
  have h2 := (satisfiesAt_setTuple_iff T vpred color hcolor ρ Ys).mpr
    ⟨S, funext fun i => (hY i).symm⟩
  simp only [h1, h2, true_and]
  constructor
  · rintro ⟨i, hne, hsub⟩
    rw [hX i] at hne hsub
    rw [hY i] at hsub
    obtain ⟨t, ht⟩ := hne
    obtain ⟨hci, -⟩ := mem_definingTuple_singleton_iff.mp ht
    subst hci
    rw [mem_iff_BAGS_subset_definingTuple hcolor]
    intro t' ht'
    exact hsub (mem_definingTuple_singleton_iff.mpr ⟨rfl, ht'⟩)
  · intro hv
    refine ⟨color v, ?_, ?_⟩
    · obtain ⟨t, ht⟩ := T.BAGS_nonempty v
      exact ⟨t, by
        rw [hX (color v)]
        exact mem_definingTuple_singleton_iff.mpr ⟨rfl, ht⟩⟩
    · rw [hX (color v), hY (color v)]
      intro t ht
      obtain ⟨-, htv⟩ := mem_definingTuple_singleton_iff.mp ht
      exact BAGS_subset_definingTuple hv htv

end RootedTreeDecomposition
