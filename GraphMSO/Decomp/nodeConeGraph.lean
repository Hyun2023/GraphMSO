import GraphMSO.Decomp.bagColoring
import GraphMSO.Decomp.rootedGraph

/-!
Node graphs and cone graphs associated with a rooted tree decomposition.

The lecture note uses two rooted graphs at a decomposition node `t`.

* The node graph is the graph induced by the current bag `beta(t)`, rooted at
  the adhesion, and labeled by the bag coloring on the whole bag.
* The cone graph is the graph induced by the whole cone below `t`, rooted and
  labeled on the current bag.  The root is still only the adhesion, but the
  temporary bag labels are retained so that the result of gluing a node graph
  with its child cones has the same labelled interface as the cone graph.
-/

namespace RootedTreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The bag of `t` is contained in the cone below `t`. -/
theorem bag_subset_cone (T : RootedTreeDecomposition G) (t : T.Node) :
    T.bag t ⊆ T.cone t := by
  intro v hv
  exact ⟨t, Relation.ReflTransGen.refl, hv⟩

/-- The adhesion of `t` is contained in the bag of `t`. -/
theorem adhesion_subset_bag (T : RootedTreeDecomposition G) (t : T.Node) :
    T.adhesion t ⊆ T.bag t := by
  intro v hv
  by_cases hroot : t = T.root
  · subst t
    simp at hv
  · rw [T.adhesion_eq_inter_parent hroot] at hv
    exact hv.1

/-- The adhesion of `t` is contained in the cone below `t`. -/
theorem adhesion_subset_cone (T : RootedTreeDecomposition G) (t : T.Node) :
    T.adhesion t ⊆ T.cone t :=
  fun _ hv => T.bag_subset_cone t (T.adhesion_subset_bag t hv)

/-! ## Cone structure -/

/-- Descendants of distinct children of the same parent are disjoint. -/
theorem eq_of_isChild_of_isAncestor_of_isAncestor {T : RootedTreeDecomposition G}
    {parent child₁ child₂ x : T.Node}
    (hchild₁ : T.IsChild parent child₁) (hchild₂ : T.IsChild parent child₂)
    (hdesc₁ : T.IsAncestor child₁ x) (hdesc₂ : T.IsAncestor child₂ x) :
    child₁ = child₂ := by
  rcases hdesc₁.comparable_of_common_descendant hdesc₂ with h₁₂ | h₂₁
  · exact h₁₂.eq_of_rootDepth_le (by
      have hdepth₁ := hchild₁.rootDepth_eq_add_one
      have hdepth₂ := hchild₂.rootDepth_eq_add_one
      omega)
  · exact (h₂₁.eq_of_rootDepth_le (by
      have hdepth₁ := hchild₁.rootDepth_eq_add_one
      have hdepth₂ := hchild₂.rootDepth_eq_add_one
      omega)).symm

/--
Lemma 6(i): for a child `child` of `parent`, the vertices that occur both in the
child cone and in the parent bag are exactly the adhesion of the child.
-/
theorem cone_inter_bag_eq_adhesion_of_isChild (T : RootedTreeDecomposition G)
    {parent child : T.Node} (hchild : T.IsChild parent child) :
    T.cone child ∩ T.bag parent = T.adhesion child := by
  ext v
  constructor
  · intro hv
    rcases hv.1 with ⟨x, hdesc, hxbag⟩
    have hxBAGS : x ∈ T.BAGS v := by
      simpa using hxbag
    have hparentBAGS : parent ∈ T.BAGS v := by
      simpa using hv.2
    have htop_x : T.IsAncestor (T.topBAGSNode v) x :=
      T.topBAGSNode_isAncestor v hxBAGS
    have htop_parent : T.IsAncestor (T.topBAGSNode v) parent :=
      T.topBAGSNode_isAncestor v hparentBAGS
    have htop_child : T.IsAncestor (T.topBAGSNode v) child := by
      rcases htop_x.comparable_of_common_descendant hdesc with h | h
      · exact h
      · exfalso
        have hchild_le_top := h.rootDepth_le
        have htop_le_parent := htop_parent.rootDepth_le
        have hstep := hchild.rootDepth_eq_add_one
        omega
    have hchildBAGS : child ∈ T.BAGS v :=
      T.mem_BAGS_of_isAncestor_of_isAncestor v htop_child hdesc hxBAGS
    rw [T.adhesion_eq_inter_of_isChild hchild]
    exact ⟨hchildBAGS, hv.2⟩
  · intro hv
    rw [T.adhesion_eq_inter_of_isChild hchild] at hv
    exact ⟨T.bag_subset_cone child hv.1, hv.2⟩

/--
If a vertex belongs to cones of two distinct children, then it already belongs
to the parent bag.
-/
theorem mem_bag_of_mem_cone_of_mem_cone_of_isChild_ne
    (T : RootedTreeDecomposition G) {parent child₁ child₂ : T.Node}
    (hchild₁ : T.IsChild parent child₁) (hchild₂ : T.IsChild parent child₂)
    (hne : child₁ ≠ child₂) {v : V}
    (hv₁ : v ∈ T.cone child₁) (hv₂ : v ∈ T.cone child₂) :
    v ∈ T.bag parent := by
  rcases hv₁ with ⟨x₁, hdesc₁, hx₁bag⟩
  rcases hv₂ with ⟨x₂, hdesc₂, hx₂bag⟩
  have hx₁BAGS : x₁ ∈ T.BAGS v := by
    simpa using hx₁bag
  have hx₂BAGS : x₂ ∈ T.BAGS v := by
    simpa using hx₂bag
  have htop_x₁ : T.IsAncestor (T.topBAGSNode v) x₁ :=
    T.topBAGSNode_isAncestor v hx₁BAGS
  have htop_x₂ : T.IsAncestor (T.topBAGSNode v) x₂ :=
    T.topBAGSNode_isAncestor v hx₂BAGS
  have hparent_x₁ : T.IsAncestor parent x₁ :=
    (Relation.ReflTransGen.single hchild₁).trans hdesc₁
  have htop_parent : T.IsAncestor (T.topBAGSNode v) parent := by
    rcases htop_x₁.comparable_of_common_descendant hparent_x₁ with h | hparent_top
    · exact h
    · rcases Relation.ReflTransGen.cases_head hparent_top with htop_eq | hstep
      · rw [htop_eq]
        exact Relation.ReflTransGen.refl
      · rcases hstep with ⟨child, hparent_child, hchild_top⟩
        have hchild_x₁ : T.IsAncestor child x₁ := hchild_top.trans htop_x₁
        have hchild_x₂ : T.IsAncestor child x₂ := hchild_top.trans htop_x₂
        have hchild_eq₁ : child = child₁ :=
          eq_of_isChild_of_isAncestor_of_isAncestor hparent_child hchild₁ hchild_x₁ hdesc₁
        have hchild_eq₂ : child = child₂ :=
          eq_of_isChild_of_isAncestor_of_isAncestor hparent_child hchild₂ hchild_x₂ hdesc₂
        exact False.elim (hne (hchild_eq₁.symm.trans hchild_eq₂))
  have hparentBAGS : parent ∈ T.BAGS v :=
    T.mem_BAGS_of_isAncestor_of_isAncestor v htop_parent hparent_x₁ hx₁BAGS
  simpa using hparentBAGS

/--
Lemma 6(ii): cones of distinct children intersect only along the corresponding
adhesions.
-/
theorem cone_inter_cone_subset_adhesion_inter_adhesion_of_isChild_ne
    (T : RootedTreeDecomposition G) {parent child₁ child₂ : T.Node}
    (hchild₁ : T.IsChild parent child₁) (hchild₂ : T.IsChild parent child₂)
    (hne : child₁ ≠ child₂) :
    T.cone child₁ ∩ T.cone child₂ ⊆ T.adhesion child₁ ∩ T.adhesion child₂ := by
  intro v hv
  have hparent_bag : v ∈ T.bag parent :=
    T.mem_bag_of_mem_cone_of_mem_cone_of_isChild_ne hchild₁ hchild₂ hne hv.1 hv.2
  have hadh₁ : v ∈ T.adhesion child₁ := by
    rw [← T.cone_inter_bag_eq_adhesion_of_isChild hchild₁]
    exact ⟨hv.1, hparent_bag⟩
  have hadh₂ : v ∈ T.adhesion child₂ := by
    rw [← T.cone_inter_bag_eq_adhesion_of_isChild hchild₂]
    exact ⟨hv.2, hparent_bag⟩
  exact ⟨hadh₁, hadh₂⟩

/--
Lemma 6(iii), first form: every edge of the graph induced by `cone t` has both
endpoints in a common bag whose node lies in the subtree rooted at `t`.
-/
theorem exists_bag_in_subtree_of_adj_of_mem_cone (T : RootedTreeDecomposition G)
    {t : T.Node} {u v : V} (hadj : G.Adj u v)
    (hu : u ∈ T.cone t) (hv : v ∈ T.cone t) :
    ∃ s : T.Node, T.IsAncestor t s ∧ u ∈ T.bag s ∧ v ∈ T.bag s := by
  classical
  rcases T.toTreeDecomposition.exists_bag_of_adj hadj with ⟨s₀, hu₀, hv₀⟩
  by_cases hdesc₀ : T.IsAncestor t s₀
  · exact ⟨s₀, hdesc₀, hu₀, hv₀⟩
  · rcases hu with ⟨a, hta, hua⟩
    rcases hv with ⟨b, htb, hvb⟩
    have haBAGS : a ∈ T.BAGS u := by
      simpa using hua
    have hs₀BAGSu : s₀ ∈ T.BAGS u := by
      simpa using hu₀
    have htop_a : T.IsAncestor (T.topBAGSNode u) a :=
      T.topBAGSNode_isAncestor u haBAGS
    have htop_s₀ : T.IsAncestor (T.topBAGSNode u) s₀ :=
      T.topBAGSNode_isAncestor u hs₀BAGSu
    have htop_t_u : T.IsAncestor (T.topBAGSNode u) t := by
      rcases htop_a.comparable_of_common_descendant hta with h | ht_top
      · exact h
      · exfalso
        exact hdesc₀ (ht_top.trans htop_s₀)
    have htBAGSu : t ∈ T.BAGS u :=
      T.mem_BAGS_of_isAncestor_of_isAncestor u htop_t_u hta haBAGS
    have hbBAGS : b ∈ T.BAGS v := by
      simpa using hvb
    have hs₀BAGSv : s₀ ∈ T.BAGS v := by
      simpa using hv₀
    have htop_b : T.IsAncestor (T.topBAGSNode v) b :=
      T.topBAGSNode_isAncestor v hbBAGS
    have htop_s₀_v : T.IsAncestor (T.topBAGSNode v) s₀ :=
      T.topBAGSNode_isAncestor v hs₀BAGSv
    have htop_t_v : T.IsAncestor (T.topBAGSNode v) t := by
      rcases htop_b.comparable_of_common_descendant htb with h | ht_top
      · exact h
      · exfalso
        exact hdesc₀ (ht_top.trans htop_s₀_v)
    have htBAGSv : t ∈ T.BAGS v :=
      T.mem_BAGS_of_isAncestor_of_isAncestor v htop_t_v htb hbBAGS
    exact ⟨t, Relation.ReflTransGen.refl, by simpa using htBAGSu, by simpa using htBAGSv⟩

/--
Lemma 6(iii), child-cone form: an edge in `cone t` is either already in the bag
at `t`, or both endpoints lie in the cone of a child of `t`.
-/
theorem adj_in_bag_or_child_cone_of_adj_of_mem_cone (T : RootedTreeDecomposition G)
    {t : T.Node} {u v : V} (hadj : G.Adj u v)
    (hu : u ∈ T.cone t) (hv : v ∈ T.cone t) :
    (u ∈ T.bag t ∧ v ∈ T.bag t) ∨
      ∃ child : T.Node, T.IsChild t child ∧ u ∈ T.cone child ∧ v ∈ T.cone child := by
  rcases T.exists_bag_in_subtree_of_adj_of_mem_cone hadj hu hv with ⟨s, hts, hus, hvs⟩
  rcases Relation.ReflTransGen.cases_head hts with hst | hstep
  · left
    subst s
    exact ⟨hus, hvs⟩
  · right
    rcases hstep with ⟨child, hchild, hchild_s⟩
    exact ⟨child, hchild, ⟨s, hchild_s, hus⟩, ⟨s, hchild_s, hvs⟩⟩

/-- Vertices of the node graph at `t`. -/
abbrev NodeGraphVertex (T : RootedTreeDecomposition G) (t : T.Node) : Type _ :=
  {v : V // v ∈ T.bag t}

/-- Vertices of the cone graph at `t`. -/
abbrev ConeGraphVertex (T : RootedTreeDecomposition G) (t : T.Node) : Type _ :=
  {v : V // v ∈ T.cone t}

/-! ## Main definition: Node Graph -/

/--
The node graph at `t`: the graph induced by the current bag, rooted at the
adhesion, and labeled by the bag coloring on every bag vertex.
-/
def nodeGraph (T : RootedTreeDecomposition G) {omega : ℕ} {P : Type*}
    (vpred : P → V → Prop)
    (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color)
    (t : T.Node) : KRootedGraph P (omega + 1) where
  V := T.NodeGraphVertex t
  G := G.induce (T.bag t)
  pred := fun p x => vpred p x.1
  R := {x | x.1 ∈ T.adhesion t}
  labelDom := Set.univ
  label := fun x => color x.1.1
  root_labeled := by
    intro _ _
    trivial
  label_injective := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact T.eq_of_mem_bag_of_color_eq hcolor x.1.2 y.1.2 hxy

/-! ## Main definition: Cone Graph -/

/--
The cone graph at `t`: the graph induced by all vertices appearing below `t`,
rooted at the adhesion, and labeled on the current bag.

Keeping the whole bag labelled is deliberate.  When the node graph at `t` is
glued with its child cones, gluing inherits the labels of the first operand,
namely the labels on `T.bag t`; the cone graph at `t` must carry exactly those
temporary labels.  Later, when this cone is attached to its parent, only its
root `T.adhesion t` participates in the identification.
-/
def coneGraph (T : RootedTreeDecomposition G) {omega : ℕ} {P : Type*}
    (vpred : P → V → Prop)
    (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color)
    (t : T.Node) : KRootedGraph P (omega + 1) where
  V := T.ConeGraphVertex t
  G := G.induce (T.cone t)
  pred := fun p x => vpred p x.1
  R := {x | x.1 ∈ T.adhesion t}
  labelDom := {x | x.1 ∈ T.bag t}
  label := fun x => color x.1.1
  root_labeled := by
    intro _ hx
    exact T.adhesion_subset_bag t hx
  label_injective := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact T.eq_of_mem_bag_of_color_eq hcolor
      x.2 y.2 hxy

end RootedTreeDecomposition
