import GraphMSO.Decomp.tree_decomp
import Mathlib.Order.WellFounded

/-!
The `BAGS` connected subgraph associated with a graph vertex.

For a vertex `v`, `BAGS(v)` is the set of decomposition nodes whose bags
contain `v`.  The tree-decomposition connectivity axiom says that this set
induces a connected subgraph of the decomposition tree.

The top-node machinery is developed for an arbitrary node set `U` whose
induced subgraph is preconnected: existence and minimality of a top node,
uniqueness, the ancestor property, and convexity along ancestor chains.
`BAGS(v)` is the motivating instance, and the `BAGS` versions used elsewhere
are derived from the general ones.  The general form is what the defining-pair
lemmas of the Courcelle encoding quantify over.
-/

namespace TreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-! ## Main definition: BAGS -/

/-- `BAGS(v)`: decomposition nodes whose bags contain the graph vertex `v`. -/
def BAGS (D : TreeDecomposition G) (v : V) : Set D.Node :=
  D.bagsOf v

@[simp] theorem mem_BAGS (D : TreeDecomposition G) (v : V) (t : D.Node) :
    t ∈ D.BAGS v ↔ v ∈ D.bag t :=
  Iff.rfl

/-! ## Main definition: BAGSGraph -/

/-- The subgraph of the decomposition tree induced by `BAGS(v)`. -/
def BAGSGraph (D : TreeDecomposition G) (v : V) :
    SimpleGraph (D.BAGS v) :=
  D.T.induce (D.BAGS v)

/-- `BAGS(v)` is nonempty because every graph vertex appears in some bag. -/
theorem BAGS_nonempty (D : TreeDecomposition G) (v : V) :
    (D.BAGS v).Nonempty := by
  simpa [BAGS] using D.bagsOf_nonempty v

/-- `BAGS(v)` induces a preconnected graph by the tree-decomposition axiom. -/
theorem BAGS_preconnected (D : TreeDecomposition G) (v : V) :
    (D.BAGSGraph v).Preconnected := by
  simpa [BAGSGraph, BAGS] using D.bagsOf_preconnected v

/-- `BAGS(v)` induces a connected subgraph of the decomposition tree. -/
theorem BAGS_connected (D : TreeDecomposition G) (v : V) :
    (D.BAGSGraph v).Connected := by
  refine { preconnected := D.BAGS_preconnected v, nonempty := ?_ }
  rcases D.BAGS_nonempty v with ⟨t, ht⟩
  exact ⟨⟨t, ht⟩⟩

/-- The subgraph induced by `BAGS(v)` is a tree. -/
theorem BAGSGraph_isTree (D : TreeDecomposition G) (v : V) :
    (D.BAGSGraph v).IsTree := by
  refine ⟨D.BAGS_connected v, ?_⟩
  simpa [BAGSGraph] using D.T_istree.IsAcyclic.induce (D.BAGS v)

end TreeDecomposition

namespace RootedTreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-! ## Top node of a preconnected node set -/

/-- A preconnected nonempty node set induces a subtree of the decomposition
tree. -/
theorem isTree_induce_of_preconnected (T : RootedTreeDecomposition G)
    {U : Set T.Node} (hconn : (T.T.induce U).Preconnected) (hU : U.Nonempty) :
    (T.T.induce U).IsTree := by
  refine ⟨{ preconnected := hconn, nonempty := ?_ }, ?_⟩
  · rcases hU with ⟨t, ht⟩
    exact ⟨⟨t, ht⟩⟩
  · exact T.T_istree.IsAcyclic.induce U

/-- A top node of a node set `U`: a member of minimum root depth. -/
def IsTopNode (T : RootedTreeDecomposition G) (U : Set T.Node) (t : T.Node) :
    Prop :=
  t ∈ U ∧ ∀ u ∈ U, T.rootDepth t ≤ T.rootDepth u

/-- The chosen top node of a nonempty node set: a member of minimum root
depth. -/
noncomputable def topNode (T : RootedTreeDecomposition G) (U : Set T.Node)
    (hU : U.Nonempty) : T.Node :=
  T.rootDepth.argminOn U hU

theorem topNode_mem (T : RootedTreeDecomposition G) (U : Set T.Node)
    (hU : U.Nonempty) :
    T.topNode U hU ∈ U :=
  T.rootDepth.argminOn_mem U hU

theorem topNode_minimal (T : RootedTreeDecomposition G) {U : Set T.Node}
    (hU : U.Nonempty) {t : T.Node} (ht : t ∈ U) :
    T.rootDepth (T.topNode U hU) ≤ T.rootDepth t :=
  T.rootDepth.argminOn_le U ht hU

theorem isTopNode_topNode (T : RootedTreeDecomposition G) (U : Set T.Node)
    (hU : U.Nonempty) :
    T.IsTopNode U (T.topNode U hU) :=
  ⟨T.topNode_mem U hU, fun _ ht => T.topNode_minimal hU ht⟩

/-- The inclusion of an induced subgraph of the decomposition tree into the
tree. -/
private def inclHom (T : RootedTreeDecomposition G) (U : Set T.Node) :
    T.T.induce U →g T.T where
  toFun := fun x => x.1
  map_rel' := by
    intro x y hxy
    simpa using hxy

private theorem inclHom_injective (T : RootedTreeDecomposition G)
    (U : Set T.Node) :
    Function.Injective (T.inclHom U) := by
  intro x y hxy
  exact Subtype.ext hxy

/-- Top nodes of a preconnected node set are unique. -/
theorem IsTopNode.unique {T : RootedTreeDecomposition G} {U : Set T.Node}
    (hconn : (T.T.induce U).Preconnected)
    {t u : T.Node} (ht : T.IsTopNode U t) (hu : T.IsTopNode U u) :
    t = u := by
  have hUtree : (T.T.induce U).IsTree :=
    T.isTree_induce_of_preconnected hconn ⟨t, ht.1⟩
  let t' : U := ⟨t, ht.1⟩
  let u' : U := ⟨u, hu.1⟩
  obtain ⟨p, hp⟩ := (hUtree.isConnected t' u').exists_isPath
  by_cases heq : t' = u'
  · exact congrArg Subtype.val heq
  · have hp_not_nil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne heq
    rcases SimpleGraph.Walk.not_nil_iff.mp hp_not_nil with ⟨x, h, q, hp_eq⟩
    subst p
    have htx : T.T.Adj t x.1 := (T.inclHom U).map_adj h
    have hle_tx : T.rootDepth t ≤ T.rootDepth x.1 := ht.2 x.1 x.2
    have hdepth : T.rootDepth x.1 = T.rootDepth t + 1 := by
      rcases T.rootDepth_eq_add_one_or_eq_add_one htx with hlt | hgt
      · omega
      · exact hgt
    have hp_orig :
        (SimpleGraph.Walk.cons htx (q.map (T.inclHom U))).IsPath := by
      have hp_mapped :=
        SimpleGraph.Walk.map_isPath_of_injective (f := T.inclHom U)
          (T.inclHom_injective U) hp
      change (SimpleGraph.Walk.cons ((T.inclHom U).map_adj h)
        (q.map (T.inclHom U))).IsPath at hp_mapped
      exact hp_mapped
    have hlt_tu : T.rootDepth t < T.rootDepth u :=
      rootDepth_lt_of_cons_isPath_of_rootDepth_eq_add_one
        (T := T) htx hdepth (q.map (T.inclHom U)) hp_orig
    have hle_ut : T.rootDepth u ≤ T.rootDepth t := hu.2 t ht.1
    omega

/-- The top node of a preconnected node set is an ancestor of every member. -/
theorem topNode_isAncestor (T : RootedTreeDecomposition G) {U : Set T.Node}
    (hconn : (T.T.induce U).Preconnected) (hU : U.Nonempty)
    {t : T.Node} (ht : t ∈ U) :
    T.IsAncestor (T.topNode U hU) t := by
  have hUtree : (T.T.induce U).IsTree :=
    T.isTree_induce_of_preconnected hconn hU
  let top' : U := ⟨T.topNode U hU, T.topNode_mem U hU⟩
  let t' : U := ⟨t, ht⟩
  obtain ⟨p, hp⟩ := (hUtree.isConnected top' t').exists_isPath
  by_cases heq : top' = t'
  · have hval : T.topNode U hU = t := congrArg Subtype.val heq
    rw [← hval]
    exact Relation.ReflTransGen.refl
  · have hp_not_nil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne heq
    rcases SimpleGraph.Walk.not_nil_iff.mp hp_not_nil with ⟨x, h, q, hp_eq⟩
    subst p
    have htopx : T.T.Adj (T.topNode U hU) x.1 := (T.inclHom U).map_adj h
    have hle_topx : T.rootDepth (T.topNode U hU) ≤ T.rootDepth x.1 :=
      T.topNode_minimal hU x.2
    have hdepth : T.rootDepth x.1 = T.rootDepth (T.topNode U hU) + 1 := by
      rcases T.rootDepth_eq_add_one_or_eq_add_one htopx with hlt | hgt
      · omega
      · exact hgt
    have hp_orig :
        (SimpleGraph.Walk.cons htopx (q.map (T.inclHom U))).IsPath := by
      have hp_mapped :=
        SimpleGraph.Walk.map_isPath_of_injective (f := T.inclHom U)
          (T.inclHom_injective U) hp
      change (SimpleGraph.Walk.cons ((T.inclHom U).map_adj h)
        (q.map (T.inclHom U))).IsPath at hp_mapped
      exact hp_mapped
    exact isAncestor_of_cons_isPath_of_rootDepth_eq_add_one
      (T := T) htopx hdepth (q.map (T.inclHom U)) hp_orig

/--
If a child lies in a preconnected node set `U` and its parent is below the
top node of `U`, then the parent lies in `U` as well.
-/
theorem parent_mem_of_isChild_of_child_mem {T : RootedTreeDecomposition G}
    {U : Set T.Node} (hconn : (T.T.induce U).Preconnected) (hU : U.Nonempty)
    {parent child : T.Node} (hchild : T.IsChild parent child)
    (htop_parent : T.IsAncestor (T.topNode U hU) parent)
    (hchild_mem : child ∈ U) :
    parent ∈ U := by
  have hUtree : (T.T.induce U).IsTree :=
    T.isTree_induce_of_preconnected hconn hU
  let top' : U := ⟨T.topNode U hU, T.topNode_mem U hU⟩
  let child' : U := ⟨child, hchild_mem⟩
  obtain ⟨q, hq⟩ := (hUtree.isConnected top' child').exists_isPath
  let qOrig : T.T.Walk (T.topNode U hU) child := q.map (T.inclHom U)
  have hqOrig : qOrig.IsPath := by
    dsimp [qOrig]
    exact SimpleGraph.Walk.map_isPath_of_injective (f := T.inclHom U)
      (T.inclHom_injective U) hq
  have hqOrig_support_subset :
      ∀ z : T.Node, z ∈ qOrig.support -> z ∈ U := by
    intro z hz
    dsimp [qOrig] at hz
    rw [SimpleGraph.Walk.support_map] at hz
    rcases List.mem_map.mp hz with ⟨x, hx, hxz⟩
    have hxz' : x.1 = z := by
      simpa [inclHom] using hxz
    rw [← hxz']
    exact x.2
  rcases htop_parent.exists_isPath_and_forall_rootDepth_le with ⟨p, hp, hpdepth⟩
  by_contra hparent_not_mem
  have hparent_not_support : parent ∉ qOrig.support := by
    intro hmem
    exact hparent_not_mem (hqOrig_support_subset parent hmem)
  have hchild_in_p : child ∈ p.support :=
    T.T_istree.IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
      hp hqOrig hchild.adj hparent_not_support
  have hchild_depth_le : T.rootDepth child ≤ T.rootDepth parent :=
    hpdepth child hchild_in_p
  have hstep := hchild.rootDepth_eq_add_one
  omega

/--
A preconnected node set is convex along ancestor chains starting at its top
node: if `x` is between the top node of `U` and a node of `U`, then `x` is
also in `U`.
-/
theorem mem_of_isAncestor_of_isAncestor (T : RootedTreeDecomposition G)
    {U : Set T.Node} (hconn : (T.T.induce U).Preconnected) (hU : U.Nonempty)
    {x t : T.Node}
    (htop_x : T.IsAncestor (T.topNode U hU) x)
    (hxt : T.IsAncestor x t)
    (ht : t ∈ U) :
    x ∈ U := by
  revert htop_x ht
  induction hxt with
  | refl =>
      intro _ ht
      exact ht
  | @tail y z hxy hyz ih =>
      intro htop_x hz_mem
      have htop_y : T.IsAncestor (T.topNode U hU) y :=
        htop_x.trans hxy
      have hy_mem : y ∈ U :=
        parent_mem_of_isChild_of_child_mem hconn hU hyz htop_y hz_mem
      exact ih htop_x hy_mem

/--
A non-top member of a preconnected node set has its parent in the set.
-/
theorem parent_mem_of_mem_of_ne_topNode (T : RootedTreeDecomposition G)
    {U : Set T.Node} (hconn : (T.T.induce U).Preconnected) (hU : U.Nonempty)
    {t : T.Node} (ht : t ∈ U) (hne : t ≠ T.topNode U hU) :
    T.parent t ∈ U := by
  have htop := T.topNode_isAncestor hconn hU ht
  rcases Relation.ReflTransGen.cases_tail htop with heq | ⟨b, htop_b, hb_child⟩
  · exact absurd heq hne
  · obtain rfl : b = T.parent t := hb_child.2
    exact T.mem_of_isAncestor_of_isAncestor hconn hU htop_b
      (Relation.ReflTransGen.single hb_child) ht

/-! ## Top node of `BAGS(v)` -/

/-- The `BAGS(v)` set for a rooted tree decomposition, forwarded to the underlying decomposition. -/
def BAGS (T : RootedTreeDecomposition G) (v : V) : Set T.Node :=
  T.toTreeDecomposition.BAGS v

@[simp] theorem mem_BAGS (T : RootedTreeDecomposition G) (v : V) (t : T.Node) :
    t ∈ T.BAGS v ↔ v ∈ T.bag t :=
  Iff.rfl

/-- `BAGS(v)` is nonempty for a rooted tree decomposition. -/
theorem BAGS_nonempty (T : RootedTreeDecomposition G) (v : V) :
    (T.BAGS v).Nonempty := by
  simpa [BAGS] using T.toTreeDecomposition.BAGS_nonempty v

/-- The subgraph induced by `BAGS(v)` for a rooted tree decomposition. -/
def BAGSGraph (T : RootedTreeDecomposition G) (v : V) :
    SimpleGraph (T.BAGS v) :=
  T.toTreeDecomposition.BAGSGraph v

/-- `BAGS(v)` induces a preconnected subgraph of the decomposition tree. -/
theorem BAGS_preconnected (T : RootedTreeDecomposition G) (v : V) :
    (T.T.induce (T.BAGS v)).Preconnected :=
  T.toTreeDecomposition.BAGS_preconnected v

/-- The subgraph induced by `BAGS(v)` is a tree for a rooted tree decomposition. -/
theorem BAGSGraph_isTree (T : RootedTreeDecomposition G) (v : V) :
    (T.BAGSGraph v).IsTree := by
  simpa [BAGSGraph, BAGS] using T.toTreeDecomposition.BAGSGraph_isTree v

/-- A top node of `BAGS(v)`: a node in `BAGS(v)` with minimum root depth. -/
def IsTopBAGSNode (T : RootedTreeDecomposition G) (v : V) (t : T.Node) : Prop :=
  t ∈ T.BAGS v ∧ ∀ u : T.Node, u ∈ T.BAGS v -> T.rootDepth t ≤ T.rootDepth u

/--
The top node of `BAGS(v)`: a node in `BAGS(v)` whose path from the root has
minimum length among all nodes in `BAGS(v)`.
-/
noncomputable def topBAGSNode (T : RootedTreeDecomposition G) (v : V) : T.Node :=
  T.topNode (T.BAGS v) (T.BAGS_nonempty v)

/-- The chosen top node belongs to `BAGS(v)`. -/
theorem topBAGSNode_mem (T : RootedTreeDecomposition G) (v : V) :
    T.topBAGSNode v ∈ T.BAGS v :=
  T.topNode_mem (T.BAGS v) (T.BAGS_nonempty v)

/-- The chosen top node is at least as close to the root as any other node in `BAGS(v)`. -/
theorem topBAGSNode_minimal (T : RootedTreeDecomposition G) (v : V)
    {t : T.Node} (ht : t ∈ T.BAGS v) :
    T.rootDepth (T.topBAGSNode v) ≤ T.rootDepth t :=
  T.topNode_minimal (T.BAGS_nonempty v) ht

/-- The chosen top node satisfies the top-node specification. -/
theorem topBAGSNode_isTop (T : RootedTreeDecomposition G) (v : V) :
    T.IsTopBAGSNode v (T.topBAGSNode v) :=
  ⟨T.topBAGSNode_mem v, fun _ ht => T.topBAGSNode_minimal v ht⟩

/-- The top node of `BAGS(v)` is unique. -/
theorem IsTopBAGSNode.unique {T : RootedTreeDecomposition G} {v : V}
    {t u : T.Node} (ht : T.IsTopBAGSNode v t) (hu : T.IsTopBAGSNode v u) :
    t = u :=
  IsTopNode.unique (T.BAGS_preconnected v) ⟨ht.1, ht.2⟩ ⟨hu.1, hu.2⟩

/-- Existence and uniqueness of the top node of `BAGS(v)`. -/
theorem existsUnique_topBAGSNode (T : RootedTreeDecomposition G) (v : V) :
    ∃! t : T.Node, T.IsTopBAGSNode v t := by
  refine ⟨T.topBAGSNode v, T.topBAGSNode_isTop v, ?_⟩
  intro t ht
  exact ht.unique (T.topBAGSNode_isTop v)

/-- The top node of `BAGS(v)` is an ancestor of every node in `BAGS(v)`. -/
theorem topBAGSNode_isAncestor (T : RootedTreeDecomposition G) (v : V)
    {t : T.Node} (ht : t ∈ T.BAGS v) :
    T.IsAncestor (T.topBAGSNode v) t :=
  T.topNode_isAncestor (T.BAGS_preconnected v) (T.BAGS_nonempty v) ht

/--
If a child lies in `BAGS(v)` and its parent is below the top node of `BAGS(v)`,
then the parent lies in `BAGS(v)` as well.
-/
theorem IsChild.parent_mem_BAGS_of_child_mem {T : RootedTreeDecomposition G} {v : V}
    {parent child : T.Node} (hchild : T.IsChild parent child)
    (htop_parent : T.IsAncestor (T.topBAGSNode v) parent)
    (hchild_mem : child ∈ T.BAGS v) :
    parent ∈ T.BAGS v :=
  parent_mem_of_isChild_of_child_mem (T.BAGS_preconnected v)
    (T.BAGS_nonempty v) hchild htop_parent hchild_mem

/--
`BAGS(v)` is convex along ancestor chains starting at its top node: if `x` is
between the top node of `BAGS(v)` and a node of `BAGS(v)`, then `x` is also in
`BAGS(v)`.
-/
theorem mem_BAGS_of_isAncestor_of_isAncestor (T : RootedTreeDecomposition G) (v : V)
    {x t : T.Node}
    (htop_x : T.IsAncestor (T.topBAGSNode v) x)
    (hxt : T.IsAncestor x t)
    (ht : t ∈ T.BAGS v) :
    x ∈ T.BAGS v :=
  T.mem_of_isAncestor_of_isAncestor (T.BAGS_preconnected v) (T.BAGS_nonempty v)
    htop_x hxt ht

end RootedTreeDecomposition
