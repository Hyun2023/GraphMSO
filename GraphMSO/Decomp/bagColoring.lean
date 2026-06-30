import GraphMSO.Decomp.bags
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.EquivFin

/-!
Bag colorings for tree decompositions.

In the lecture note, a bag-injective coloring is a map
`c : V(G) -> {0, ..., omega}` such that no bag contains two vertices with the
same color.  We represent `{0, ..., omega}` as `Fin (omega + 1)` and the
bag-injectivity condition as Mathlib's `Set.InjOn`.
-/

/-- Courcelle's finite color set `{0, ..., omega}`. -/
abbrev BagColorSet (omega : ℕ) : Type :=
  Fin (omega + 1)

namespace TreeDecomposition

variable {V : Type*} {G : SimpleGraph V}

/-! ## Main definition: BagColoring -/

/-- A coloring is bag-injective if every bag contains at most one vertex of each color. -/
def IsBagColoring (D : TreeDecomposition G) {k : ℕ} (color : V -> Fin k) : Prop :=
  ∀ t : D.Node, Set.InjOn color (D.bag t)

/-- A Courcelle bag-coloring using colors `{0, ..., omega}`. -/
def BagColoring (D : TreeDecomposition G) (omega : ℕ) : Type _ :=
  { color : V -> BagColorSet omega // D.IsBagColoring color }

theorem eq_of_mem_bag_of_color_eq {D : TreeDecomposition G} {k : ℕ}
    {color : V -> Fin k} (hcolor : D.IsBagColoring color)
    {t : D.Node} {u v : V} (hu : u ∈ D.bag t) (hv : v ∈ D.bag t)
    (h : color u = color v) :
    u = v :=
  hcolor t hu hv h

end TreeDecomposition

namespace RootedTreeDecomposition

variable {V : Type*} {G : SimpleGraph V}

/-! ## Main definition: RootedTreeDecomposition.BagColoring -/

/-- Bag-injectivity for a rooted tree decomposition, forwarded to the underlying decomposition. -/
def IsBagColoring (T : RootedTreeDecomposition G) {k : ℕ} (color : V -> Fin k) : Prop :=
  T.decomp.IsBagColoring color

/-- A Courcelle bag-coloring of a rooted tree decomposition. -/
def BagColoring (T : RootedTreeDecomposition G) (omega : ℕ) : Type _ :=
  T.decomp.BagColoring omega

/-! ## The conflict graph viewpoint -/

/--
The conflict graph of a tree decomposition: two graph vertices conflict when
they are distinct and appear together in some bag.
-/
def bagConflictGraph (T : RootedTreeDecomposition G) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ t : T.decomp.Node, u ∈ T.bag t ∧ v ∈ T.bag t
  symm := by
    intro u v h
    exact ⟨h.1.symm, h.2.imp fun t ht => ⟨ht.2, ht.1⟩⟩
  loopless := by
    intro u h
    exact h.1 rfl

theorem bagConflictGraph_adj_iff (T : RootedTreeDecomposition G) (u v : V) :
    (T.bagConflictGraph).Adj u v ↔
      u ≠ v ∧ ∃ t : T.decomp.Node, u ∈ T.bag t ∧ v ∈ T.bag t :=
  Iff.rfl

/--
Bag-injectivity is exactly proper coloring of the conflict graph associated
with the decomposition.
-/
theorem isBagColoring_iff_valid_conflict (T : RootedTreeDecomposition G) {k : ℕ}
    (color : V -> Fin k) :
    T.IsBagColoring color ↔
      ∀ {u v : V}, (T.bagConflictGraph).Adj u v -> color u ≠ color v := by
  constructor
  · intro hcolor u v huv hsame
    rcases huv.2 with ⟨t, hu, hv⟩
    exact huv.1 (hcolor t hu hv hsame)
  · intro hvalid t u hu v hv hsame
    by_contra hne
    exact hvalid ⟨hne, ⟨t, hu, hv⟩⟩ hsame

/-- A proper coloring of the conflict graph is a bag coloring. -/
def bagColoringOfConflictColoring (T : RootedTreeDecomposition G) {omega : ℕ}
    (color : (T.bagConflictGraph).Coloring (BagColorSet omega)) :
    T.BagColoring omega :=
  ⟨color, (T.isBagColoring_iff_valid_conflict color).2 fun huv => color.valid huv⟩

/-! ## Top-node bookkeeping for the finite greedy construction -/

/-- The depth of the top node of `BAGS(v)`. -/
noncomputable def topBAGSDepth (T : RootedTreeDecomposition G) (v : V) : ℕ :=
  T.rootDepth (T.topBAGSNode v)

/-- The top node of `BAGS(v)` carries `v` in its bag. -/
theorem mem_bag_topBAGSNode (T : RootedTreeDecomposition G) (v : V) :
    v ∈ T.bag (T.topBAGSNode v) := by
  simpa using T.topBAGSNode_mem v

/-- Vertices whose `BAGS` top node is exactly `t`. -/
def verticesWithTop (T : RootedTreeDecomposition G) (t : T.decomp.Node) : Set V :=
  {v | T.topBAGSNode v = t}

/-- Every vertex with top node `t` is contained in the bag at `t`. -/
theorem verticesWithTop_subset_bag (T : RootedTreeDecomposition G) (t : T.decomp.Node) :
    T.verticesWithTop t ⊆ T.bag t := by
  intro v hv
  rw [← hv]
  exact T.mem_bag_topBAGSNode v

/-- Under a width bound, each top fiber has size at most `omega + 1`. -/
theorem verticesWithTop_ncard_le_of_hasWidth (T : RootedTreeDecomposition G) (omega : ℕ)
    (hwidth : T.decomp.HasWidth omega) (t : T.decomp.Node) :
    (T.verticesWithTop t).ncard ≤ omega + 1 := by
  exact (Set.ncard_le_ncard (T.verticesWithTop_subset_bag t) (hwidth t).1).trans (hwidth t).2

/-- A single bounded bag admits an injective coloring by the bag color set. -/
theorem exists_injective_coloring_on_bag (T : RootedTreeDecomposition G) (omega : ℕ)
    (hwidth : T.decomp.HasWidth omega) (t : T.decomp.Node) :
    ∃ color : V -> BagColorSet omega, Set.InjOn color (T.bag t) := by
  classical
  letI : Fintype (T.bag t) := (hwidth t).1.fintype
  have hcard : Fintype.card (T.bag t) ≤ Fintype.card (BagColorSet omega) := by
    have hcard_bag : Fintype.card (T.bag t) ≤ omega + 1 := by
      rw [← Set.toFinset_card (T.bag t), ← Set.ncard_eq_toFinset_card' (T.bag t)]
      exact (hwidth t).2
    simpa [BagColorSet, Fintype.card_fin] using hcard_bag
  let emb : T.bag t ↪ BagColorSet omega :=
    (Function.Embedding.nonempty_of_card_le hcard).some
  let color : V -> BagColorSet omega := fun v =>
    if hv : v ∈ T.bag t then emb ⟨v, hv⟩ else 0
  refine ⟨color, ?_⟩
  intro u hu v hv hcolor
  have hu' : color u = emb ⟨u, hu⟩ := by simp [color, hu]
  have hv' : color v = emb ⟨v, hv⟩ := by simp [color, hv]
  have h_emb : emb ⟨u, hu⟩ = emb ⟨v, hv⟩ := by
    simpa [hu', hv'] using hcolor
  exact congrArg Subtype.val (emb.injective h_emb)

/-! ## Finite greedy coloring -/

/-- A coloring that is proper on the finite vertex set `s`. -/
def IsPartialColoring (H : SimpleGraph V) (s : Finset V) {k : ℕ}
    (color : V -> Fin k) : Prop :=
  ∀ u v : V, u ∈ s -> v ∈ s -> H.Adj u v -> color u ≠ color v

/--
Finite greedy coloring: if every nonempty finite set has a vertex with at most
`omega` neighbors inside that set, then the whole finite graph is colorable with
`omega + 1` colors.
-/
theorem exists_coloring_of_forall_exists_neighbor_card_le [Fintype V]
    (H : SimpleGraph V) (omega : ℕ)
    (hchoose : ∀ s : Finset V, s.Nonempty ->
      ∃ v ∈ s, ({u | u ∈ s ∧ H.Adj u v} : Set V).ncard ≤ omega) :
    Nonempty (H.Coloring (BagColorSet omega)) := by
  classical
  have hpartial :
      ∀ s : Finset V, ∃ color : V -> BagColorSet omega, IsPartialColoring H s color := by
    refine Finset.strongInduction ?_
    intro s ih
    by_cases hs : s.Nonempty
    · rcases hchoose s hs with ⟨v, hv, hdeg⟩
      have herase : s.erase v ⊂ s := Finset.erase_ssubset hv
      rcases ih (s.erase v) herase with ⟨color, hcolor⟩
      let neighbors : Finset V := {u ∈ s | H.Adj u v}
      let forbidden : Finset (BagColorSet omega) := neighbors.image color
      have hneighbors_card : neighbors.card ≤ omega := by
        rw [← Set.ncard_coe_finset neighbors]
        simpa [neighbors] using hdeg
      have hforbidden_card : forbidden.card ≤ omega := by
        exact Finset.card_image_le.trans hneighbors_card
      have hlt_univ : forbidden.card < (Finset.univ : Finset (BagColorSet omega)).card := by
        simpa [BagColorSet, Fintype.card_fin] using Nat.lt_succ_of_le hforbidden_card
      rcases Finset.exists_mem_notMem_of_card_lt_card hlt_univ with ⟨c, -, hc⟩
      let color' : V -> BagColorSet omega := fun x => if x = v then c else color x
      refine ⟨color', ?_⟩
      intro a b ha hb hab heq
      by_cases hav : a = v
      · subst a
        by_cases hbv : b = v
        · subst b
          exact H.loopless v hab
        · have hb_neigh : b ∈ neighbors := by
            simp [neighbors, hb, H.symm hab]
          have hb_forbidden : color b ∈ forbidden := by
            exact Finset.mem_image.mpr ⟨b, hb_neigh, rfl⟩
          have hcb : c = color b := by
            simpa [color', hbv] using heq
          exact hc (by
            rw [hcb]
            exact hb_forbidden)
      · by_cases hbv : b = v
        · subst b
          have ha_neigh : a ∈ neighbors := by
            simp [neighbors, ha, hab]
          have ha_forbidden : color a ∈ forbidden := by
            exact Finset.mem_image.mpr ⟨a, ha_neigh, rfl⟩
          have hac : color a = c := by
            simpa [color', hav] using heq
          exact hc (by
            rw [← hac]
            exact ha_forbidden)
        · exact hcolor a b (Finset.mem_erase.mpr ⟨hav, ha⟩)
            (Finset.mem_erase.mpr ⟨hbv, hb⟩) hab (by simpa [color', hav, hbv] using heq)
    · refine ⟨fun _ => 0, ?_⟩
      intro a _ ha _ _ _
      exact (hs ⟨a, ha⟩).elim
  rcases hpartial (Finset.univ : Finset V) with ⟨color, hcolor⟩
  exact ⟨SimpleGraph.Coloring.mk color (by
    intro u v huv
    exact hcolor u v (Finset.mem_univ u) (Finset.mem_univ v) huv)⟩

/--
Greedy bag coloring from the top-node claim: if every conflict edge whose first
endpoint has no larger top depth is witnessed in the second endpoint's top bag,
then a bounded-width rooted decomposition has a bag coloring.
-/
theorem exists_bagColoring_of_hasWidth_of_top_claim [Fintype V]
    (T : RootedTreeDecomposition G) (omega : ℕ)
    (hwidth : T.decomp.HasWidth omega)
    (htop : ∀ {u v : V}, (T.bagConflictGraph).Adj u v ->
      T.topBAGSDepth u ≤ T.topBAGSDepth v -> u ∈ T.bag (T.topBAGSNode v)) :
    Nonempty (T.BagColoring omega) := by
  classical
  have hchoose : ∀ s : Finset V, s.Nonempty ->
      ∃ v ∈ s, ({u | u ∈ s ∧ (T.bagConflictGraph).Adj u v} : Set V).ncard ≤ omega := by
    intro s hs
    rcases Finset.exists_max_image s T.topBAGSDepth hs with ⟨v, hv, hvmax⟩
    refine ⟨v, hv, ?_⟩
    let neighbors : Finset V := {u ∈ s | (T.bagConflictGraph).Adj u v}
    have hsubset :
        (neighbors : Set V) ⊆ T.bag (T.topBAGSNode v) \ {v} := by
      intro u hu
      have hu_fin : u ∈ neighbors := hu
      have hu_parts := Finset.mem_filter.mp hu_fin
      have hu_mem : u ∈ s := hu_parts.1
      have huv : (T.bagConflictGraph).Adj u v := hu_parts.2
      have hdepth : T.topBAGSDepth u ≤ T.topBAGSDepth v := hvmax u hu_mem
      exact ⟨htop huv hdepth, huv.1⟩
    have hneighbors_card :
        neighbors.card ≤ (T.bag (T.topBAGSNode v) \ {v}).ncard := by
      rw [← Set.ncard_coe_finset neighbors]
      exact Set.ncard_le_ncard hsubset ((hwidth (T.topBAGSNode v)).1.diff)
    have hbag_minus :
        (T.bag (T.topBAGSNode v) \ {v}).ncard ≤ omega := by
      have hvbag : v ∈ T.bag (T.topBAGSNode v) := T.mem_bag_topBAGSNode v
      have hdiff :
          (T.bag (T.topBAGSNode v) \ {v}).ncard =
            (T.bag (T.topBAGSNode v)).ncard - 1 := by
        exact Set.ncard_diff_singleton_of_mem hvbag
      have hbag_card : (T.bag (T.topBAGSNode v)).ncard ≤ omega + 1 :=
        (hwidth (T.topBAGSNode v)).2
      rw [hdiff]
      omega
    have hset :
        ({u | u ∈ s ∧ (T.bagConflictGraph).Adj u v} : Set V) =
          (neighbors : Set V) := by
      ext u
      simp [neighbors]
    rw [hset]
    simpa using hneighbors_card.trans hbag_minus
  rcases exists_coloring_of_forall_exists_neighbor_card_le
      (H := T.bagConflictGraph) omega hchoose with ⟨coloring⟩
  exact ⟨T.bagColoringOfConflictColoring coloring⟩

/--
If two vertices occur together in a bag and `u`'s top node is no deeper than
`v`'s top node, then `u`'s top node is an ancestor of `v`'s top node.
-/
theorem topBAGSNode_isAncestor_topBAGSNode_of_conflict_of_depth_le
    (T : RootedTreeDecomposition G) {u v : V}
    (huv : (T.bagConflictGraph).Adj u v)
    (hle : T.topBAGSDepth u ≤ T.topBAGSDepth v) :
    T.IsAncestor (T.topBAGSNode u) (T.topBAGSNode v) := by
  rcases huv.2 with ⟨t, hut, hvt⟩
  have hu_anc_t : T.IsAncestor (T.topBAGSNode u) t :=
    T.topBAGSNode_isAncestor u hut
  have hv_anc_t : T.IsAncestor (T.topBAGSNode v) t :=
    T.topBAGSNode_isAncestor v hvt
  rcases hu_anc_t.comparable_of_common_descendant hv_anc_t with h | h
  · exact h
  · have heq : T.topBAGSNode v = T.topBAGSNode u :=
      h.eq_of_rootDepth_le (by
        simpa [topBAGSDepth] using hle)
    rw [heq]
    exact Relation.ReflTransGen.refl

/--
If two conflicting vertices satisfy `topDepth u ≤ topDepth v`, then `u` is
already present in the top bag of `v`.
-/
theorem mem_bag_topBAGSNode_of_conflict_of_depth_le
    (T : RootedTreeDecomposition G) {u v : V}
    (huv : (T.bagConflictGraph).Adj u v)
    (hle : T.topBAGSDepth u ≤ T.topBAGSDepth v) :
    u ∈ T.bag (T.topBAGSNode v) := by
  rcases huv.2 with ⟨t, hut, hvt⟩
  have htop_uv : T.IsAncestor (T.topBAGSNode u) (T.topBAGSNode v) :=
    T.topBAGSNode_isAncestor_topBAGSNode_of_conflict_of_depth_le huv hle
  have htopv_t : T.IsAncestor (T.topBAGSNode v) t :=
    T.topBAGSNode_isAncestor v hvt
  have htopv_mem_BAGSu : T.topBAGSNode v ∈ T.BAGS u :=
    T.mem_BAGS_of_isAncestor_of_isAncestor u htop_uv htopv_t hut
  simpa using htopv_mem_BAGSu

/--
Bag-injective coloring fact: a rooted tree decomposition of width at most
`omega` admits a coloring by `{0, ..., omega}` that is injective on every bag.
-/
theorem exists_bagColoring_of_hasWidth [Fintype V] (T : RootedTreeDecomposition G) (omega : ℕ)
    (hwidth : T.decomp.HasWidth omega) :
    Nonempty (T.BagColoring omega) := by
  exact T.exists_bagColoring_of_hasWidth_of_top_claim omega hwidth
    (fun huv hle => T.mem_bag_topBAGSNode_of_conflict_of_depth_le huv hle)

theorem eq_of_mem_bag_of_color_eq {T : RootedTreeDecomposition G} {k : ℕ}
    {color : V -> Fin k} (hcolor : T.IsBagColoring color)
    {t : T.decomp.Node} {u v : V} (hu : u ∈ T.bag t) (hv : v ∈ T.bag t)
    (h : color u = color v) :
    u = v :=
  hcolor t hu hv h

end RootedTreeDecomposition
