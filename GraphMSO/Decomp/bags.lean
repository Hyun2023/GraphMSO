import GraphMSO.Decomp.tree_decomp
import Mathlib.Order.WellFounded

/-!
The `BAGS` connected subgraph associated with a graph vertex.

For a vertex `v`, `BAGS(v)` is the set of decomposition nodes whose bags
contain `v`.  The tree-decomposition connectivity axiom says that this set
induces a connected subgraph of the decomposition tree.
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
  T.rootDepth.argminOn (T.BAGS v) (T.BAGS_nonempty v)

/-- The chosen top node belongs to `BAGS(v)`. -/
theorem topBAGSNode_mem (T : RootedTreeDecomposition G) (v : V) :
    T.topBAGSNode v ∈ T.BAGS v := by
  exact T.rootDepth.argminOn_mem (T.BAGS v) (T.BAGS_nonempty v)

/-- The chosen top node is at least as close to the root as any other node in `BAGS(v)`. -/
theorem topBAGSNode_minimal (T : RootedTreeDecomposition G) (v : V)
    {t : T.Node} (ht : t ∈ T.BAGS v) :
    T.rootDepth (T.topBAGSNode v) ≤ T.rootDepth t := by
  simpa [topBAGSNode] using
    T.rootDepth.argminOn_le (T.BAGS v) ht (T.BAGS_nonempty v)

/-- The chosen top node satisfies the top-node specification. -/
theorem topBAGSNode_isTop (T : RootedTreeDecomposition G) (v : V) :
    T.IsTopBAGSNode v (T.topBAGSNode v) :=
  ⟨T.topBAGSNode_mem v, fun _ ht => T.topBAGSNode_minimal v ht⟩

/-- The top node of `BAGS(v)` is unique. -/
theorem IsTopBAGSNode.unique {T : RootedTreeDecomposition G} {v : V}
    {t u : T.Node} (ht : T.IsTopBAGSNode v t) (hu : T.IsTopBAGSNode v u) :
    t = u := by
  let t' : T.BAGS v := ⟨t, ht.1⟩
  let u' : T.BAGS v := ⟨u, hu.1⟩
  obtain ⟨p, hp⟩ := ((T.BAGSGraph_isTree v).isConnected t' u').exists_isPath
  let incl : T.BAGSGraph v →g T.T := {
    toFun := fun x => x.1
    map_rel' := by
      intro x y hxy
      simpa [BAGSGraph, BAGS, TreeDecomposition.BAGSGraph] using hxy }
  have hincl : Function.Injective incl := by
    intro x y hxy
    exact Subtype.ext hxy
  by_cases heq : t' = u'
  · exact congrArg Subtype.val heq
  · have hp_not_nil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne heq
    rcases SimpleGraph.Walk.not_nil_iff.mp hp_not_nil with ⟨x, h, q, hp_eq⟩
    subst p
    have htx : T.T.Adj t x.1 := incl.map_adj h
    have hle_tx : T.rootDepth t ≤ T.rootDepth x.1 := ht.2 x x.2
    have hdepth : T.rootDepth x.1 = T.rootDepth t + 1 := by
      rcases T.rootDepth_eq_add_one_or_eq_add_one htx with hlt | hgt
      · omega
      · exact hgt
    have hp_orig :
        (SimpleGraph.Walk.cons htx (q.map incl)).IsPath := by
      have hp_mapped := SimpleGraph.Walk.map_isPath_of_injective (f := incl) hincl hp
      change (SimpleGraph.Walk.cons (incl.map_adj h) (q.map incl)).IsPath at hp_mapped
      exact hp_mapped
    have hlt_tu : T.rootDepth t < T.rootDepth u :=
      rootDepth_lt_of_cons_isPath_of_rootDepth_eq_add_one
        (T := T) htx hdepth (q.map incl) hp_orig
    have hle_ut : T.rootDepth u ≤ T.rootDepth t := hu.2 t ht.1
    omega

/-- Existence and uniqueness of the top node of `BAGS(v)`. -/
theorem existsUnique_topBAGSNode (T : RootedTreeDecomposition G) (v : V) :
    ∃! t : T.Node, T.IsTopBAGSNode v t := by
  refine ⟨T.topBAGSNode v, T.topBAGSNode_isTop v, ?_⟩
  intro t ht
  exact ht.unique (T.topBAGSNode_isTop v)

/-- The top node of `BAGS(v)` is an ancestor of every node in `BAGS(v)`. -/
theorem topBAGSNode_isAncestor (T : RootedTreeDecomposition G) (v : V)
    {t : T.Node} (ht : t ∈ T.BAGS v) :
    T.IsAncestor (T.topBAGSNode v) t := by
  let top' : T.BAGS v := ⟨T.topBAGSNode v, T.topBAGSNode_mem v⟩
  let t' : T.BAGS v := ⟨t, ht⟩
  obtain ⟨p, hp⟩ := ((T.BAGSGraph_isTree v).isConnected top' t').exists_isPath
  let incl : T.BAGSGraph v →g T.T := {
    toFun := fun x => x.1
    map_rel' := by
      intro x y hxy
      simpa [BAGSGraph, BAGS, TreeDecomposition.BAGSGraph] using hxy }
  have hincl : Function.Injective incl := by
    intro x y hxy
    exact Subtype.ext hxy
  by_cases heq : top' = t'
  · have hval : T.topBAGSNode v = t := congrArg Subtype.val heq
    rw [← hval]
    exact Relation.ReflTransGen.refl
  · have hp_not_nil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne heq
    rcases SimpleGraph.Walk.not_nil_iff.mp hp_not_nil with ⟨x, h, q, hp_eq⟩
    subst p
    have htopx : T.T.Adj (T.topBAGSNode v) x.1 := incl.map_adj h
    have hle_topx : T.rootDepth (T.topBAGSNode v) ≤ T.rootDepth x.1 :=
      T.topBAGSNode_minimal v x.2
    have hdepth : T.rootDepth x.1 = T.rootDepth (T.topBAGSNode v) + 1 := by
      rcases T.rootDepth_eq_add_one_or_eq_add_one htopx with hlt | hgt
      · omega
      · exact hgt
    have hp_orig :
        (SimpleGraph.Walk.cons htopx (q.map incl)).IsPath := by
      have hp_mapped := SimpleGraph.Walk.map_isPath_of_injective (f := incl) hincl hp
      change (SimpleGraph.Walk.cons (incl.map_adj h) (q.map incl)).IsPath at hp_mapped
      exact hp_mapped
    exact isAncestor_of_cons_isPath_of_rootDepth_eq_add_one
      (T := T) htopx hdepth (q.map incl) hp_orig

/--
If a child lies in `BAGS(v)` and its parent is below the top node of `BAGS(v)`,
then the parent lies in `BAGS(v)` as well.
-/
theorem IsChild.parent_mem_BAGS_of_child_mem {T : RootedTreeDecomposition G} {v : V}
    {parent child : T.Node} (hchild : T.IsChild parent child)
    (htop_parent : T.IsAncestor (T.topBAGSNode v) parent)
    (hchild_mem : child ∈ T.BAGS v) :
    parent ∈ T.BAGS v := by
  let top' : T.BAGS v := ⟨T.topBAGSNode v, T.topBAGSNode_mem v⟩
  let child' : T.BAGS v := ⟨child, hchild_mem⟩
  obtain ⟨q, hq⟩ := ((T.BAGSGraph_isTree v).isConnected top' child').exists_isPath
  let incl : T.BAGSGraph v →g T.T := {
    toFun := fun x => x.1
    map_rel' := by
      intro x y hxy
      simpa [BAGSGraph, BAGS, TreeDecomposition.BAGSGraph] using hxy }
  have hincl : Function.Injective incl := by
    intro x y hxy
    exact Subtype.ext hxy
  let qOrig : T.T.Walk (T.topBAGSNode v) child := q.map incl
  have hqOrig : qOrig.IsPath := by
    dsimp [qOrig]
    exact SimpleGraph.Walk.map_isPath_of_injective (f := incl) hincl hq
  have hqOrig_support_subset :
      ∀ z : T.Node, z ∈ qOrig.support -> z ∈ T.BAGS v := by
    intro z hz
    dsimp [qOrig] at hz
    rw [SimpleGraph.Walk.support_map] at hz
    rcases List.mem_map.mp hz with ⟨x, hx, hxz⟩
    have hxz' : x.1 = z := by
      simpa [incl] using hxz
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
`BAGS(v)` is convex along ancestor chains starting at its top node: if `x` is
between the top node of `BAGS(v)` and a node of `BAGS(v)`, then `x` is also in
`BAGS(v)`.
-/
theorem mem_BAGS_of_isAncestor_of_isAncestor (T : RootedTreeDecomposition G) (v : V)
    {x t : T.Node}
    (htop_x : T.IsAncestor (T.topBAGSNode v) x)
    (hxt : T.IsAncestor x t)
    (ht : t ∈ T.BAGS v) :
    x ∈ T.BAGS v := by
  revert htop_x ht
  induction hxt with
  | refl =>
      intro _ ht
      exact ht
  | @tail y z hxy hyz ih =>
      intro htop_x hz_mem
      have htop_y : T.IsAncestor (T.topBAGSNode v) y :=
        htop_x.trans hxy
      have hy_mem : y ∈ T.BAGS v :=
        hyz.parent_mem_BAGS_of_child_mem (v := v) htop_y hz_mem
      exact ih htop_x hy_mem

end RootedTreeDecomposition
