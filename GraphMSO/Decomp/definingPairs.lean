import GraphMSO.Decomp.encoding

/-!
# Defining pairs and defining tuples

The combinatorial layer of the lecture note's §"Combinatorial properties of
defining tuples", stated directly over a bag-colored decomposition
`(G, c, (T, β))`.  Following the recommendation of
`Courcelle/lecture_note_expanded_lean_issues.tex`, none of these statements
mention the decoding of a legal Σ-tree; they are the facts the MSO
translation will cite over an encoded triple.

* `IsDefiningPair` — the five local conditions of the defining-pair lemma.
  The top node is not mentioned explicitly: for a preconnected set, "being
  the top node" is expressed by "the parent is outside the set", which is
  also the form the tree MSO formulas use.
* `isDefiningPair_iff` — the defining-pair lemma: the conditions hold exactly
  for the pairs `(BAGS v, color v)`.
* Distinctness: distinct vertices of one color have disjoint bag sets and are
  non-adjacent.
* `adj_iff_exists_mem_BAGS_adjOnColors` and
  `vpred_iff_exists_mem_BAGS_tagOnColor` — adjacency and unary predicates are
  read off the encoded letters at common bags.
* `definingTuple` and its characterizations — the tuple representation of
  vertex sets used by the set-variable translation.
-/

namespace RootedTreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-! ## Defining pairs -/

/--
The five defining-pair conditions for a node set `U` and a color `i`:
`U` is nonempty and preconnected, every bag of `U` has a color-`i` vertex,
every non-top member's adhesion has a color-`i` vertex, the top member's
adhesion has none, and no dangling child's adhesion has one.

Here "non-top member" is expressed as a non-root member whose parent stays in
`U`, and "top member" as a member whose parent leaves `U`; for preconnected
`U` these describe exactly the non-top members and the top node.
-/
def IsDefiningPair (T : RootedTreeDecomposition G) {k : ℕ} (color : V -> Fin k)
    (U : Set T.Node) (i : Fin k) : Prop :=
  U.Nonempty ∧
  (T.T.induce U).Preconnected ∧
  (∀ t ∈ U, ∃ v ∈ T.bag t, color v = i) ∧
  (∀ t ∈ U, t ≠ T.root -> T.parent t ∈ U -> ∃ v ∈ T.adhesion t, color v = i) ∧
  (∀ t ∈ U, T.parent t ∉ U -> ∀ v ∈ T.adhesion t, color v ≠ i) ∧
  (∀ x ∉ U, T.parent x ∈ U -> ∀ v ∈ T.adhesion x, color v ≠ i)

variable {T : RootedTreeDecomposition G} {k : ℕ} {color : V -> Fin k}

/-- The forward half of the defining-pair lemma: the bag set and color of any
vertex satisfy the five conditions. -/
theorem isDefiningPair_BAGS (hcolor : T.IsBagColoring color) (v : V) :
    T.IsDefiningPair color (T.BAGS v) (color v) := by
  refine ⟨T.BAGS_nonempty v, T.BAGS_preconnected v, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨v, ht, rfl⟩
  · intro t ht hroot hparent
    refine ⟨v, ?_, rfl⟩
    rw [T.adhesion_eq_inter_parent hroot]
    exact ⟨ht, hparent⟩
  · intro t ht hparent u hu hcu
    by_cases hroot : t = T.root
    · subst hroot
      rw [T.adhesion_root] at hu
      exact hu
    · rw [T.adhesion_eq_inter_parent hroot] at hu
      have huv : u = v := hcolor t hu.1 ht hcu
      subst huv
      exact hparent hu.2
  · intro x hx hparent u hu hcu
    have hx_ne_root : x ≠ T.root := by
      intro hroot
      subst hroot
      rw [T.parent_root] at hparent
      exact hx hparent
    rw [T.adhesion_eq_inter_parent hx_ne_root] at hu
    have huv : u = v := hcolor (T.parent x) hu.2 hparent hcu
    subst huv
    exact hx hu.1

/-- The backward half of the defining-pair lemma: the five conditions force
`(U, i)` to be the bag set and color of a (unique) vertex. -/
theorem exists_of_isDefiningPair (hcolor : T.IsBagColoring color)
    {U : Set T.Node} {i : Fin k} (h : T.IsDefiningPair color U i) :
    ∃ v : V, color v = i ∧ T.BAGS v = U := by
  obtain ⟨hU, hconn, hbag, hadh, htopc, hdangle⟩ := h
  have ht₀_mem : T.topNode U hU ∈ U := T.topNode_mem U hU
  obtain ⟨v, hv_bag, hv_color⟩ := hbag (T.topNode U hU) ht₀_mem
  -- every node of `U` carries `v`, by induction along the ancestor chain
  -- from the top node
  have hU_sub : ∀ t, T.IsAncestor (T.topNode U hU) t -> t ∈ U -> v ∈ T.bag t := by
    intro t hanc
    induction hanc with
    | refl =>
        intro _
        exact hv_bag
    | @tail b c hb hbc ih =>
        intro hc_mem
        have hb_mem : b ∈ U :=
          T.mem_of_isAncestor_of_isAncestor hconn hU hb
            (Relation.ReflTransGen.single hbc) hc_mem
        have hv_b : v ∈ T.bag b := ih hb_mem
        obtain ⟨u, hu_adh, hu_color⟩ :=
          hadh c hc_mem hbc.1 (by rw [← hbc.2]; exact hb_mem)
        rw [T.adhesion_eq_inter_parent hbc.1, ← hbc.2] at hu_adh
        have huv : u = v :=
          hcolor b hu_adh.2 hv_b (hu_color.trans hv_color.symm)
        rw [← huv]
        exact hu_adh.1
  have ht₀_bags : T.topNode U hU ∈ T.BAGS v := hv_bag
  -- the top node of `U` is the top node of `BAGS v`
  have hτ_eq : T.topBAGSNode v = T.topNode U hU := by
    have hτ := T.topBAGSNode_isAncestor v ht₀_bags
    rcases Relation.ReflTransGen.cases_tail hτ with heq | ⟨b, hτb, hbc⟩
    · exact heq.symm
    · exfalso
      have hb_bags : b ∈ T.BAGS v :=
        T.mem_BAGS_of_isAncestor_of_isAncestor v hτb
          (Relation.ReflTransGen.single hbc) ht₀_bags
      have hparent_not_mem : T.parent (T.topNode U hU) ∉ U := by
        intro hmem
        have hmin := T.topNode_minimal hU hmem
        have hstep := T.rootDepth_eq_parent_add_one hbc.1
        omega
      have hv_adh : v ∈ T.adhesion (T.topNode U hU) := by
        rw [T.adhesion_eq_inter_parent hbc.1, ← hbc.2]
        exact ⟨hv_bag, hb_bags⟩
      exact htopc (T.topNode U hU) ht₀_mem hparent_not_mem v hv_adh hv_color
  -- every node of `BAGS v` lies in `U`, again along the ancestor chain
  have hBags_sub : ∀ s, T.IsAncestor (T.topNode U hU) s -> s ∈ T.BAGS v -> s ∈ U := by
    intro s hanc
    induction hanc with
    | refl =>
        intro _
        exact ht₀_mem
    | @tail b c hb hbc ih =>
        intro hc_bags
        have hb_bags : b ∈ T.BAGS v := by
          refine T.mem_BAGS_of_isAncestor_of_isAncestor v ?_
            (Relation.ReflTransGen.single hbc) hc_bags
          rw [hτ_eq]
          exact hb
        have hb_mem : b ∈ U := ih hb_bags
        by_contra hc_not_mem
        have hv_adh : v ∈ T.adhesion c := by
          rw [T.adhesion_eq_inter_parent hbc.1, ← hbc.2]
          exact ⟨hc_bags, hb_bags⟩
        exact hdangle c hc_not_mem (by rw [← hbc.2]; exact hb_mem)
          v hv_adh hv_color
  refine ⟨v, hv_color, Set.Subset.antisymm ?_ ?_⟩
  · intro s hs
    refine hBags_sub s ?_ hs
    rw [← hτ_eq]
    exact T.topBAGSNode_isAncestor v hs
  · intro t ht
    exact hU_sub t (T.topNode_isAncestor hconn hU ht) ht

/-- The defining-pair lemma: `(U, i)` satisfies the five conditions iff it is
the pair `(BAGS v, color v)` of some vertex `v`. -/
theorem isDefiningPair_iff (hcolor : T.IsBagColoring color)
    (U : Set T.Node) (i : Fin k) :
    T.IsDefiningPair color U i ↔ ∃ v : V, color v = i ∧ T.BAGS v = U := by
  constructor
  · exact exists_of_isDefiningPair hcolor
  · rintro ⟨v, rfl, rfl⟩
    exact isDefiningPair_BAGS hcolor v

/-! ## Distinct defining pairs -/

/-- Distinct vertices sharing a color have disjoint bag sets. -/
theorem disjoint_BAGS_of_ne_of_color_eq (hcolor : T.IsBagColoring color)
    {u v : V} (hne : u ≠ v) (hc : color u = color v) :
    Disjoint (T.BAGS u) (T.BAGS v) := by
  rw [Set.disjoint_left]
  intro t hu hv
  exact hne (hcolor t hu hv hc)

/-- Distinct vertices sharing a color are non-adjacent. -/
theorem not_adj_of_ne_of_color_eq (hcolor : T.IsBagColoring color)
    {u v : V} (hne : u ≠ v) (hc : color u = color v) :
    ¬ G.Adj u v := by
  intro hadj
  rcases T.toTreeDecomposition.exists_bag_of_adj hadj with ⟨t, hut, hvt⟩
  exact hne (hcolor t hut hvt hc)

/-- Distinct vertices have distinct defining pairs: a vertex is determined by
its bag set and color. -/
theorem eq_of_BAGS_eq_of_color_eq (hcolor : T.IsBagColoring color)
    {u v : V} (hBAGS : T.BAGS u = T.BAGS v) (hc : color u = color v) :
    u = v := by
  rcases T.BAGS_nonempty u with ⟨t, ht⟩
  have ht' : t ∈ T.BAGS v := hBAGS ▸ ht
  exact hcolor t ht ht' hc

/-! ## Atomic formulas over encoded letters -/

variable {P : Type*} {omega : ℕ}

/-- At a common bag, adjacency of two vertices is adjacency of their colors
in the encoded letter. -/
theorem encodeLetter_adjOnColors_iff_adj (vpred : P → V → Prop)
    {color : V -> BagColorSet omega} (hcolor : T.IsBagColoring color)
    {t : T.Node} {u v : V} (hut : t ∈ T.BAGS u) (hvt : t ∈ T.BAGS v) :
    (T.encodeLetter vpred color hcolor t).AdjOnColors (color u) (color v) ↔
      G.Adj u v := by
  rw [encodeLetter_adjOnColors_iff]
  constructor
  · rintro ⟨u', v', hu', hv', hcu', hcv', hadj'⟩
    have hu_eq : u' = u := hcolor t hu' hut hcu'
    have hv_eq : v' = v := hcolor t hv' hvt hcv'
    rw [← hu_eq, ← hv_eq]
    exact hadj'
  · intro hadj
    exact ⟨u, v, hut, hvt, rfl, rfl, hadj⟩

/-- At any bag containing a vertex, the vertex's unary predicates are the
tags of its color in the encoded letter. -/
theorem encodeLetter_tagOnColor_iff_vpred (vpred : P → V → Prop)
    {color : V -> BagColorSet omega} (hcolor : T.IsBagColoring color)
    {t : T.Node} {v : V} (hvt : t ∈ T.BAGS v) (p : P) :
    (T.encodeLetter vpred color hcolor t).TagOnColor p (color v) ↔
      vpred p v := by
  rw [encodeLetter_tagOnColor_iff]
  constructor
  · rintro ⟨u, hu, hcu, hp⟩
    rwa [hcolor t hu hvt hcu] at hp
  · intro hp
    exact ⟨v, hvt, rfl, hp⟩

/-- Edges from common bags: `u` and `v` are adjacent iff some node carries
both in its bag and its encoded letter records the edge between their
colors. -/
theorem adj_iff_exists_mem_BAGS_adjOnColors (vpred : P → V → Prop)
    {color : V -> BagColorSet omega} (hcolor : T.IsBagColoring color)
    (u v : V) :
    G.Adj u v ↔ ∃ t : T.Node, t ∈ T.BAGS u ∧ t ∈ T.BAGS v ∧
      (T.encodeLetter vpred color hcolor t).AdjOnColors (color u) (color v) := by
  constructor
  · intro hadj
    rcases T.toTreeDecomposition.exists_bag_of_adj hadj with ⟨t, hut, hvt⟩
    exact ⟨t, hut, hvt,
      (encodeLetter_adjOnColors_iff_adj vpred hcolor hut hvt).2 hadj⟩
  · rintro ⟨t, hut, hvt, hadjc⟩
    exact (encodeLetter_adjOnColors_iff_adj vpred hcolor hut hvt).1 hadjc

/-- Unary predicates from bags: `vpred p v` holds iff some node carrying `v`
tags its color with `p`.  By `encodeLetter_tagOnColor_iff_vpred` "some" can be
strengthened to "every". -/
theorem vpred_iff_exists_mem_BAGS_tagOnColor (vpred : P → V → Prop)
    {color : V -> BagColorSet omega} (hcolor : T.IsBagColoring color)
    (p : P) (v : V) :
    vpred p v ↔ ∃ t ∈ T.BAGS v,
      (T.encodeLetter vpred color hcolor t).TagOnColor p (color v) := by
  constructor
  · intro hp
    rcases T.BAGS_nonempty v with ⟨t, ht⟩
    exact ⟨t, ht, (encodeLetter_tagOnColor_iff_vpred vpred hcolor ht p).2 hp⟩
  · rintro ⟨t, ht, htag⟩
    exact (encodeLetter_tagOnColor_iff_vpred vpred hcolor ht p).1 htag

/-! ## Defining tuples -/

/--
The defining tuple of a vertex set `S`: coordinate `i` collects the bag sets
of the color-`i` members of `S`.
-/
def definingTuple (T : RootedTreeDecomposition G) {k : ℕ} (color : V -> Fin k)
    (S : Set V) : Fin k -> Set T.Node :=
  fun i => ⋃ v ∈ {v ∈ S | color v = i}, T.BAGS v

theorem mem_definingTuple_iff {S : Set V} {i : Fin k} {t : T.Node} :
    t ∈ T.definingTuple color S i ↔
      ∃ v ∈ S, color v = i ∧ t ∈ T.BAGS v := by
  simp only [definingTuple, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨v, ⟨hvS, hvc⟩, ht⟩
    exact ⟨v, hvS, hvc, ht⟩
  · rintro ⟨v, hvS, hvc, ht⟩
    exact ⟨v, ⟨hvS, hvc⟩, ht⟩

/-- The defining tuple of a singleton: the bag set at the vertex's color and
empty elsewhere. -/
theorem definingTuple_singleton [DecidableEq (Fin k)] (v : V) (i : Fin k) :
    T.definingTuple color {v} i =
      if color v = i then T.BAGS v else ∅ := by
  ext t
  rw [mem_definingTuple_iff]
  by_cases hc : color v = i
  · simp [hc]
  · simp [hc]

/-- A member of a set contributes its whole bag set to the tuple coordinate
of its color. -/
theorem BAGS_subset_definingTuple {S : Set V} {v : V} (hv : v ∈ S) :
    T.BAGS v ⊆ T.definingTuple color S (color v) := by
  intro t ht
  exact (mem_definingTuple_iff).2 ⟨v, hv, rfl, ht⟩

/-- Membership from tuples: `v ∈ S` iff the bag set of `v` is contained in
the tuple coordinate of its color.  This is the semantic content of the
containment formula of the translation. -/
theorem mem_iff_BAGS_subset_definingTuple (hcolor : T.IsBagColoring color)
    {S : Set V} {v : V} :
    v ∈ S ↔ T.BAGS v ⊆ T.definingTuple color S (color v) := by
  constructor
  · exact BAGS_subset_definingTuple
  · intro hsub
    rcases T.BAGS_nonempty v with ⟨t, ht⟩
    obtain ⟨w, hwS, hwc, htw⟩ := (mem_definingTuple_iff).1 (hsub ht)
    have : v = w := hcolor t ht htw hwc.symm
    rw [this]
    exact hwS

/--
Characterization of defining tuples of vertex sets: a tuple arises from some
vertex set iff every node of every coordinate is covered by a defining pair
contained in that coordinate.  This is the shape of the set-recognition
formula of the translation.
-/
theorem exists_definingTuple_eq_iff (Us : Fin k -> Set T.Node) :
    (∃ S : Set V, T.definingTuple color S = Us) ↔
      ∀ i, ∀ x ∈ Us i, ∃ U' : Set T.Node, U' ⊆ Us i ∧ x ∈ U' ∧
        ∃ v : V, color v = i ∧ T.BAGS v = U' := by
  constructor
  · rintro ⟨S, rfl⟩ i x hx
    obtain ⟨v, hvS, hvc, hxv⟩ := (mem_definingTuple_iff).1 hx
    refine ⟨T.BAGS v, ?_, hxv, v, hvc, rfl⟩
    rw [← hvc]
    exact BAGS_subset_definingTuple hvS
  · intro h
    refine ⟨{v : V | T.BAGS v ⊆ Us (color v)}, ?_⟩
    funext i
    ext x
    rw [mem_definingTuple_iff]
    constructor
    · rintro ⟨v, hvsub, hvc, hxv⟩
      have := hvsub hxv
      rwa [hvc] at this
    · intro hx
      obtain ⟨U', hU'sub, hxU', v, hvc, hvBAGS⟩ := h i x hx
      refine ⟨v, ?_, hvc, ?_⟩
      · show T.BAGS v ⊆ Us (color v)
        rw [hvBAGS, hvc]
        exact hU'sub
      · rw [hvBAGS]
        exact hxU'

end RootedTreeDecomposition
