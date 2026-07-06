import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Logic.Relation


/--
A finite tree-decomposition of a finite simple graph `G`.

`Node` is the finite type of decomposition-tree nodes, `T` is the tree on those
nodes, and `node2bag` assigns to each tree node the set of graph vertices in
its bag.  The three axioms are the standard tree-decomposition axioms:
every graph vertex appears somewhere, every graph edge is covered by some bag,
and the bags containing a fixed graph vertex induce a connected subgraph of
the decomposition tree.
-/
structure TreeDecomposition {V : Type*} [Fintype V] (G : SimpleGraph V) where
  Node : Type*
  nodeFintype : Fintype Node
  T : SimpleGraph Node
  T_istree : T.IsTree
  node2bag : Node -> Set V
  VertexCoverage : ∀ v : V, ∃ n : Node, v ∈ node2bag n
  EdgeCoverage : ∀ {u v : V}, G.Adj u v -> ∃ n : Node, u ∈ node2bag n ∧ v ∈ node2bag n
  Connectivity : ∀ v : V, (T.induce {n : Node | v ∈ node2bag n}).Preconnected

/--
A tree-decomposition with a distinguished root node.

This extends `TreeDecomposition`, so the node type and decomposition tree are
available directly as `T.Node` and `T.T`.  Use `T.toTreeDecomposition` only
when a theorem explicitly expects the unrooted structure.
-/
structure RootedTreeDecomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    extends TreeDecomposition G where
  root : Node

namespace TreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

instance instFintypeNode (D : TreeDecomposition G) : Fintype D.Node :=
  D.nodeFintype

instance instNonemptyNode (D : TreeDecomposition G) : Nonempty D.Node :=
  D.T_istree.isConnected.nonempty

/-- The bag associated with a tree node. -/
def bag (D : TreeDecomposition G) (t : D.Node) : Set V :=
  D.node2bag t

/-- The set of tree nodes whose bags contain a graph vertex. -/
def bagsOf (D : TreeDecomposition G) (v : V) : Set D.Node :=
  {t | v ∈ D.bag t}

@[simp] theorem mem_bagsOf (D : TreeDecomposition G) (v : V) (t : D.Node) :
    t ∈ D.bagsOf v ↔ v ∈ D.bag t :=
  Iff.rfl

/-- Every graph vertex appears in at least one bag. -/
theorem bagsOf_nonempty (D : TreeDecomposition G) (v : V) :
    (D.bagsOf v).Nonempty := by
  rcases D.VertexCoverage v with ⟨t, ht⟩
  exact ⟨t, ht⟩

/-- Every graph edge appears inside at least one bag. -/
theorem exists_bag_of_adj (D : TreeDecomposition G) {u v : V} (h : G.Adj u v) :
    ∃ t : D.Node, u ∈ D.bag t ∧ v ∈ D.bag t := by
  simpa [bag] using D.EdgeCoverage h

/-- The bags containing a fixed graph vertex form a connected part of the tree. -/
theorem bagsOf_preconnected (D : TreeDecomposition G) (v : V) :
    (D.T.induce (D.bagsOf v)).Preconnected := by
  simpa [bagsOf, bag] using D.Connectivity v

/-- The decomposition has width at most `ω`: every bag has at most `ω + 1` vertices. -/
def HasWidth (D : TreeDecomposition G) (ω : ℕ) : Prop :=
  ∀ t : D.Node, (D.bag t).ncard ≤ ω + 1

end TreeDecomposition

namespace RootedTreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

instance instFintypeNode (T : RootedTreeDecomposition G) : Fintype T.Node :=
  T.nodeFintype

instance instNonemptyNode (T : RootedTreeDecomposition G) : Nonempty T.Node :=
  T.T_istree.isConnected.nonempty

/-- The bag associated with a tree node. -/
def bag (T : RootedTreeDecomposition G) (t : T.Node) : Set V :=
  T.toTreeDecomposition.bag t

/-- The set of tree nodes whose bags contain a graph vertex. -/
def bagsOf (T : RootedTreeDecomposition G) (v : V) : Set T.Node :=
  T.toTreeDecomposition.bagsOf v

@[simp] theorem mem_bagsOf (T : RootedTreeDecomposition G) (v : V) (t : T.Node) :
    t ∈ T.bagsOf v ↔ v ∈ T.bag t :=
  Iff.rfl

/-- The unique path from the root to a tree node. -/
noncomputable def rootPath (T : RootedTreeDecomposition G) (t : T.Node) :
    T.T.Walk T.root t :=
  (T.T_istree.existsUnique_path T.root t).choose

/-- The chosen root path is simple. -/
theorem rootPath_isPath (T : RootedTreeDecomposition G) (t : T.Node) :
    (T.rootPath t).IsPath :=
  (T.T_istree.existsUnique_path T.root t).choose_spec.1

@[simp] theorem rootPath_root (T : RootedTreeDecomposition G) :
    T.rootPath T.root = SimpleGraph.Walk.nil := by
  exact (SimpleGraph.Walk.isPath_iff_eq_nil (T.rootPath T.root)).mp
    (T.rootPath_isPath T.root)

/-- The graph distance from the root in the decomposition tree. -/
noncomputable def rootDepth (T : RootedTreeDecomposition G) (t : T.Node) : ℕ :=
  T.T.dist T.root t

/-- The chosen root path realizes the graph distance from the root. -/
theorem rootPath_length_eq_rootDepth (T : RootedTreeDecomposition G) (t : T.Node) :
    (T.rootPath t).length = T.rootDepth t := by
  obtain ⟨p, hp, hlen⟩ := T.T_istree.isConnected.exists_path_of_dist T.root t
  have hpath :
      (⟨p, hp⟩ : T.T.Path T.root t) =
        ⟨T.rootPath t, T.rootPath_isPath t⟩ :=
    T.T_istree.IsAcyclic.path_unique _ _
  have hwalk : p = T.rootPath t := congrArg Subtype.val hpath
  simpa [rootDepth, hwalk] using hlen

@[simp] theorem rootDepth_root (T : RootedTreeDecomposition G) :
    T.rootDepth T.root = 0 := by
  simpa using (T.rootPath_length_eq_rootDepth T.root).symm

/-- Adjacent decomposition nodes have distinct depths from the root. -/
theorem rootDepth_ne_of_adj (T : RootedTreeDecomposition G) {t u : T.Node}
    (h : T.T.Adj t u) :
    T.rootDepth t ≠ T.rootDepth u := by
  simpa [rootDepth] using T.T_istree.dist_ne_of_adj T.root h

/-- Along an edge, root depths differ by exactly one. -/
theorem rootDepth_eq_add_one_or_eq_add_one (T : RootedTreeDecomposition G)
    {t u : T.Node} (h : T.T.Adj t u) :
    T.rootDepth t = T.rootDepth u + 1 ∨ T.rootDepth u = T.rootDepth t + 1 := by
  simpa [rootDepth] using T.T_istree.dist_eq_dist_add_one_of_adj T.root h

/-- A node has at most one adjacent node of smaller root depth. -/
theorem eq_of_adj_of_rootDepth_lt {T : RootedTreeDecomposition G}
    {x parent₁ parent₂ : T.Node}
    (h₁ : T.T.Adj parent₁ x) (h₂ : T.T.Adj parent₂ x)
    (hd₁ : T.rootDepth parent₁ < T.rootDepth x)
    (hd₂ : T.rootDepth parent₂ < T.rootDepth x) :
    parent₁ = parent₂ := by
  have hstep₁ : T.rootDepth x = T.rootDepth parent₁ + 1 := by
    rcases T.rootDepth_eq_add_one_or_eq_add_one h₁ with h | h
    · omega
    · exact h
  have hstep₂ : T.rootDepth x = T.rootDepth parent₂ + 1 := by
    rcases T.rootDepth_eq_add_one_or_eq_add_one h₂ with h | h
    · omega
    · exact h
  have hpath₁ : T.rootPath x = (T.rootPath parent₁).concat h₁ := by
    let p : T.T.Walk T.root x := (T.rootPath parent₁).concat h₁
    have hp_len : p.length = T.rootDepth x := by
      simp [p, SimpleGraph.Walk.length_concat, T.rootPath_length_eq_rootDepth, hstep₁]
    have hp_path : p.IsPath := by
      apply SimpleGraph.Walk.isPath_of_length_eq_dist
      simpa [rootDepth] using hp_len
    have hpath :
        (⟨T.rootPath x, T.rootPath_isPath x⟩ : T.T.Path T.root x) =
          ⟨p, hp_path⟩ :=
      T.T_istree.IsAcyclic.path_unique _ _
    exact congrArg Subtype.val hpath
  have hpath₂ : T.rootPath x = (T.rootPath parent₂).concat h₂ := by
    let p : T.T.Walk T.root x := (T.rootPath parent₂).concat h₂
    have hp_len : p.length = T.rootDepth x := by
      simp [p, SimpleGraph.Walk.length_concat, T.rootPath_length_eq_rootDepth, hstep₂]
    have hp_path : p.IsPath := by
      apply SimpleGraph.Walk.isPath_of_length_eq_dist
      simpa [rootDepth] using hp_len
    have hpath :
        (⟨T.rootPath x, T.rootPath_isPath x⟩ : T.T.Path T.root x) =
          ⟨p, hp_path⟩ :=
      T.T_istree.IsAcyclic.path_unique _ _
    exact congrArg Subtype.val hpath
  have hpen₁ : (T.rootPath x).penultimate = parent₁ := by
    rw [hpath₁]
    exact SimpleGraph.Walk.penultimate_concat (T.rootPath parent₁) h₁
  have hpen₂ : (T.rootPath x).penultimate = parent₂ := by
    rw [hpath₂]
    exact SimpleGraph.Walk.penultimate_concat (T.rootPath parent₂) h₂
  exact hpen₁.symm.trans hpen₂

/--
If a simple path starts by moving one step away from the root, then its endpoint
is strictly deeper than the starting parent.
-/
theorem rootDepth_lt_of_cons_isPath_of_rootDepth_eq_add_one
    {T : RootedTreeDecomposition G} {parent child y : T.Node}
    (hpc : T.T.Adj parent child)
    (hdepth : T.rootDepth child = T.rootDepth parent + 1)
    (p : T.T.Walk child y) (hp : (SimpleGraph.Walk.cons hpc p).IsPath) :
    T.rootDepth parent < T.rootDepth y := by
  induction p generalizing parent with
  | nil =>
      omega
  | @cons child z y hcz q ih =>
      rw [SimpleGraph.Walk.cons_isPath_iff] at hp
      have hz_not_lt : ¬ T.rootDepth z < T.rootDepth child := by
        intro hzlt
        have hz_eq_parent :
            z = parent :=
          (eq_of_adj_of_rootDepth_lt (T := T) hpc hcz.symm (by omega) hzlt).symm
        have hz_mem : parent ∈ (SimpleGraph.Walk.cons hcz q).support := by
          right
          simpa [hz_eq_parent] using q.start_mem_support
        exact hp.2 hz_mem
      have hzdepth : T.rootDepth z = T.rootDepth child + 1 := by
        rcases T.rootDepth_eq_add_one_or_eq_add_one hcz with h | h
        · exfalso
          exact hz_not_lt (by omega)
        · exact h
      have hchild_lt_y : T.rootDepth child < T.rootDepth y :=
        ih hcz hzdepth hp.1
      omega

/-- The parent of a node, defined as the penultimate vertex on the root path.
For the root itself this returns the root. -/
noncomputable def parent (T : RootedTreeDecomposition G) (t : T.Node) : T.Node :=
  (T.rootPath t).penultimate

@[simp] theorem parent_root (T : RootedTreeDecomposition G) :
    T.parent T.root = T.root := by
  simp [parent]

/-- A non-root node is adjacent to its parent. -/
theorem parent_adj (T : RootedTreeDecomposition G) {t : T.Node}
    (hroot : t ≠ T.root) :
    T.T.Adj (T.parent t) t := by
  exact (T.rootPath t).adj_penultimate (SimpleGraph.Walk.not_nil_of_ne hroot.symm)

/-- The child relation induced by the parent function of the rooted tree. -/
def IsChild (T : RootedTreeDecomposition G) (parent child : T.Node) : Prop :=
  child ≠ T.root ∧ parent = T.parent child

/-- `parent` is the parent of `child` in the rooted tree. -/
def IsParent (T : RootedTreeDecomposition G) (parent child : T.Node) : Prop :=
  T.IsChild parent child

theorem not_isChild_root (T : RootedTreeDecomposition G) (parent : T.Node) :
    ¬ T.IsChild parent T.root := by
  intro h
  exact h.1 rfl

theorem IsChild.adj {T : RootedTreeDecomposition G} {parent child : T.Node}
    (h : T.IsChild parent child) :
    T.T.Adj parent child := by
  rw [h.2]
  exact T.parent_adj h.1

theorem isChild_parent {T : RootedTreeDecomposition G} {t : T.Node}
    (hroot : t ≠ T.root) :
    T.IsChild (T.parent t) t :=
  ⟨hroot, rfl⟩

/-- The parent of a non-root node is exactly one level closer to the root. -/
theorem rootDepth_eq_parent_add_one (T : RootedTreeDecomposition G)
    {t : T.Node} (hroot : t ≠ T.root) :
    T.rootDepth t = T.rootDepth (T.parent t) + 1 := by
  have hadj : T.T.Adj (T.parent t) t := T.parent_adj hroot
  rcases T.rootDepth_eq_add_one_or_eq_add_one hadj with hbad | hgood
  · have hpos : 0 < T.rootDepth t := by
      simpa [rootDepth] using T.T_istree.isConnected.pos_dist_of_ne hroot.symm
    let q : T.T.Walk T.root (T.parent t) := (T.rootPath t).dropLast
    have hq_len : q.length = T.rootDepth t - 1 := by
      simp [q, SimpleGraph.Walk.dropLast, T.rootPath_length_eq_rootDepth]
    have hdist_le : T.rootDepth (T.parent t) ≤ T.rootDepth t - 1 := by
      simpa [rootDepth, q, parent, hq_len] using T.T.dist_le q
    omega
  · exact hgood

theorem IsChild.rootDepth_eq_add_one {T : RootedTreeDecomposition G}
    {parent child : T.Node} (h : T.IsChild parent child) :
    T.rootDepth child = T.rootDepth parent + 1 := by
  rw [h.2]
  exact T.rootDepth_eq_parent_add_one h.1

/-- An edge that increases root depth by one is precisely a child edge. -/
theorem isChild_of_adj_of_rootDepth_eq_add_one {T : RootedTreeDecomposition G}
    {parent child : T.Node}
    (hpc : T.T.Adj parent child)
    (hdepth : T.rootDepth child = T.rootDepth parent + 1) :
    T.IsChild parent child := by
  have hchild_ne_root : child ≠ T.root := by
    intro hroot
    subst child
    simp at hdepth
  have hp_len :
      ((T.rootPath parent).concat hpc).length = T.rootDepth child := by
    simp [SimpleGraph.Walk.length_concat, T.rootPath_length_eq_rootDepth, hdepth]
  have hp_path : ((T.rootPath parent).concat hpc).IsPath := by
    apply SimpleGraph.Walk.isPath_of_length_eq_dist
    simpa [rootDepth] using hp_len
  have hpath :
      (⟨T.rootPath child, T.rootPath_isPath child⟩ :
          T.T.Path T.root child) =
        ⟨(T.rootPath parent).concat hpc, hp_path⟩ :=
    T.T_istree.IsAcyclic.path_unique _ _
  have hwalk : T.rootPath child = (T.rootPath parent).concat hpc :=
    congrArg Subtype.val hpath
  refine ⟨hchild_ne_root, ?_⟩
  change parent = (T.rootPath child).penultimate
  rw [hwalk]
  simp

theorem existsUnique_parent {T : RootedTreeDecomposition G} {t : T.Node}
    (hroot : t ≠ T.root) :
    ∃! parent : T.Node, T.IsChild parent t := by
  refine ⟨T.parent t, isChild_parent hroot, ?_⟩
  intro parent hparent
  exact hparent.2

/-- `child` is the unique child of `t`. -/
def HasUniqueChild (T : RootedTreeDecomposition G) (t child : T.Node) : Prop :=
  T.IsChild t child ∧ ∀ child' : T.Node, T.IsChild t child' -> child' = child

/-- The reflexive descendant relation generated by children. -/
def IsAncestor (T : RootedTreeDecomposition G) (ancestor node : T.Node) : Prop :=
  Relation.ReflTransGen (fun parent child => T.IsChild parent child) ancestor node

/--
If a simple path starts by moving one step away from the root, then its endpoint
is a descendant of the starting parent.
-/
theorem isAncestor_of_cons_isPath_of_rootDepth_eq_add_one
    {T : RootedTreeDecomposition G} {parent child y : T.Node}
    (hpc : T.T.Adj parent child)
    (hdepth : T.rootDepth child = T.rootDepth parent + 1)
    (p : T.T.Walk child y) (hp : (SimpleGraph.Walk.cons hpc p).IsPath) :
    T.IsAncestor parent y := by
  induction p generalizing parent with
  | nil =>
      exact Relation.ReflTransGen.single
        (isChild_of_adj_of_rootDepth_eq_add_one (T := T) hpc hdepth)
  | @cons child z y hcz q ih =>
      rw [SimpleGraph.Walk.cons_isPath_iff] at hp
      have hz_not_lt : ¬ T.rootDepth z < T.rootDepth child := by
        intro hzlt
        have hz_eq_parent :
            z = parent :=
          (eq_of_adj_of_rootDepth_lt (T := T) hpc hcz.symm (by omega) hzlt).symm
        have hz_mem : parent ∈ (SimpleGraph.Walk.cons hcz q).support := by
          right
          simpa [hz_eq_parent] using q.start_mem_support
        exact hp.2 hz_mem
      have hzdepth : T.rootDepth z = T.rootDepth child + 1 := by
        rcases T.rootDepth_eq_add_one_or_eq_add_one hcz with h | h
        · exfalso
          exact hz_not_lt (by omega)
        · exact h
      exact (Relation.ReflTransGen.single
        (isChild_of_adj_of_rootDepth_eq_add_one (T := T) hpc hdepth)).trans
          (ih hcz hzdepth hp.1)

theorem IsAncestor.rootDepth_le {T : RootedTreeDecomposition G}
    {ancestor node : T.Node} (h : T.IsAncestor ancestor node) :
    T.rootDepth ancestor ≤ T.rootDepth node := by
  induction h with
  | refl =>
      rfl
  | tail hprev hchild ih =>
      have hstep := hchild.rootDepth_eq_add_one
      omega

theorem IsAncestor.eq_of_rootDepth_le {T : RootedTreeDecomposition G}
    {ancestor node : T.Node} (h : T.IsAncestor ancestor node)
    (hle : T.rootDepth node ≤ T.rootDepth ancestor) :
    ancestor = node := by
  induction h with
  | refl =>
      rfl
  | tail hprev hchild ih =>
      have hprev_le := IsAncestor.rootDepth_le (T := T) hprev
      have hstep := hchild.rootDepth_eq_add_one
      exfalso
      omega

/-- Two ancestors of a common node are comparable in the rooted tree order. -/
theorem IsAncestor.comparable_of_common_descendant {T : RootedTreeDecomposition G}
    {a b x : T.Node} (ha : T.IsAncestor a x) (hb : T.IsAncestor b x) :
    T.IsAncestor a b ∨ T.IsAncestor b a := by
  let r : T.Node -> T.Node -> Prop := fun parent child => T.IsChild parent child
  have hright : Relator.RightUnique (Function.swap r) := by
    intro child parent₁ parent₂ h₁ h₂
    exact h₁.2.trans h₂.2.symm
  have ha' : Relation.ReflTransGen (Function.swap r) x a := by
    simpa [r, IsAncestor] using Relation.ReflTransGen.swap ha
  have hb' : Relation.ReflTransGen (Function.swap r) x b := by
    simpa [r, IsAncestor] using Relation.ReflTransGen.swap hb
  rcases Relation.ReflTransGen.total_of_right_unique hright ha' hb' with h | h
  · right
    simpa [r, IsAncestor, Relation.reflTransGen_swap] using h
  · left
    simpa [r, IsAncestor, Relation.reflTransGen_swap] using h

/--
An ancestor relation is witnessed by a simple path whose vertices are no deeper
than the endpoint.
-/
theorem IsAncestor.exists_isPath_and_forall_rootDepth_le
    {T : RootedTreeDecomposition G} {ancestor node : T.Node}
    (h : T.IsAncestor ancestor node) :
    ∃ p : T.T.Walk ancestor node,
      p.IsPath ∧ ∀ z : T.Node, z ∈ p.support -> T.rootDepth z ≤ T.rootDepth node := by
  induction h with
  | refl =>
      refine ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, ?_⟩
      intro z hz
      have hz' : z = ancestor := by
        simpa using hz
      subst z
      rfl
  | @tail b c hprev hchild ih =>
      rcases ih with ⟨p, hp, hpdepth⟩
      have hstep := hchild.rootDepth_eq_add_one
      have hnotmem : c ∉ p.support := by
        intro hmem
        have := hpdepth _ hmem
        omega
      refine ⟨p.concat hchild.adj, hp.concat hnotmem hchild.adj, ?_⟩
      intro z hz
      rw [SimpleGraph.Walk.support_concat] at hz
      simp at hz
      rcases hz with hz | rfl
      · have := hpdepth z hz
        omega
      · omega

/-- The node set of the subtree rooted at `t`. -/
def SubtreeNodes (T : RootedTreeDecomposition G) (t : T.Node) : Set T.Node :=
  {x | T.IsAncestor t x}

@[simp] theorem mem_subtreeNodes (T : RootedTreeDecomposition G)
    (t x : T.Node) :
    x ∈ T.SubtreeNodes t ↔ T.IsAncestor t x :=
  Iff.rfl

/-- The graph vertices appearing in bags of the subtree rooted at `t`. -/
def cone (T : RootedTreeDecomposition G) (t : T.Node) : Set V :=
  {v | ∃ x : T.Node, x ∈ T.SubtreeNodes t ∧ v ∈ T.bag x}

@[simp] theorem mem_cone (T : RootedTreeDecomposition G) (t : T.Node) (v : V) :
    v ∈ T.cone t ↔ ∃ x : T.Node, x ∈ T.SubtreeNodes t ∧ v ∈ T.bag x :=
  Iff.rfl

/--
`A` is the adhesion of `t`: the empty set at the root, and otherwise the
intersection of `t`'s bag with its parent's bag.
-/
def IsAdhesion (T : RootedTreeDecomposition G) (t : T.Node) (A : Set V) : Prop :=
  (t = T.root ∧ A = ∅) ∨
    (t ≠ T.root ∧ A = T.bag t ∩ T.bag (T.parent t))


open Classical in
/--
The adhesion of `t`: the empty set at the root, and otherwise the intersection
of `t`'s bag with a parent bag when a parent is available.
-/
noncomputable def adhesion (T : RootedTreeDecomposition G) (t : T.Node) : Set V :=
      if t = T.root then
        ∅
      else
        T.bag t ∩ T.bag (T.parent t)

lemma adhesion_isAdhesion (T : RootedTreeDecomposition G) (t : T.Node) :
  T.IsAdhesion t (adhesion T t) := by
  simp [adhesion,IsAdhesion]
  by_cases h : t= T.root<;>simp [h]

theorem root_isAdhesion_empty (T : RootedTreeDecomposition G) :
    T.IsAdhesion T.root (∅ : Set V) := by
  exact Or.inl ⟨rfl, rfl⟩

@[simp] theorem adhesion_root (T : RootedTreeDecomposition G) :
    T.adhesion T.root = (∅ : Set V) := by
  simp [adhesion]

theorem isAdhesion_of_isChild (T : RootedTreeDecomposition G) {parent t : T.Node}
    (hroot : t ≠ T.root) (hchild : T.IsChild parent t) :
    T.IsAdhesion t (T.bag t ∩ T.bag parent) := by
  exact Or.inr ⟨hroot, by rw [hchild.2]⟩


theorem adhesion_eq_inter_parent (T : RootedTreeDecomposition G)
    {t : T.Node} (hroot : t ≠ T.root) :
    T.adhesion t = T.bag t ∩ T.bag (T.parent t) := by
  simp [adhesion, hroot]

theorem adhesion_eq_inter_of_isChild (T : RootedTreeDecomposition G)
    {parent t : T.Node} (hchild : T.IsChild parent t) :
    T.adhesion t = T.bag t ∩ T.bag parent := by
  rw [adhesion_eq_inter_parent T hchild.1, hchild.2]

end RootedTreeDecomposition
