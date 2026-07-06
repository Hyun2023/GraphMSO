import GraphMSO.Decomp.tree_decomp

namespace RootedTreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (T : RootedTreeDecomposition G)

/--
`t` is a leaf of the rooted decomposition tree.

The child relation is not primitive data: it is induced by the root and the
unique path from the root.  Thus a leaf is a node with no child in this
root-oriented sense.
-/
def IsLeafNode (t : T.Node) : Prop :=
  ∀ child : T.Node, ¬ T.IsChild t child

/--
`t` has at most two children.

This formulation avoids cardinalities.  It says that all children of `t` are
contained in a two-element list of candidates `left, right`; the two candidates
are allowed to coincide, so this also covers zero-child and one-child nodes.
-/
def HasAtMostTwoChildren (t : T.Node) : Prop :=
  ∃ left right : T.Node,
    ∀ child : T.Node, T.IsChild t child -> child = left ∨ child = right

/--
`t` has exactly one child.

The witness is the unique child itself, packaged using `HasUniqueChild` from
`tree_decomp.lean`.
-/
def HasExactlyOneChild (t : T.Node) : Prop :=
  ∃ child : T.Node, T.HasUniqueChild t child

/--
`t` is an introduce node in the top-down convention.

It has a unique child `child`, and the parent bag is obtained from the child
bag by adding exactly one vertex `v`.  The equation is written as
`bag child = bag t \ {v}` because that is often easier to rewrite with
set difference.
-/
def IsIntroduceNode (T : RootedTreeDecomposition G) (t : T.Node) : Prop :=
  ∃ (child : T.Node) (v : V),
    T.HasUniqueChild t child ∧
      v ∈ T.bag t ∧
      T.bag child = T.bag t \ {v}

/--
`t` is a forget node in the top-down convention.

It has a unique child `child`, and the parent bag is obtained from the child
bag by deleting exactly one vertex `v`.
-/
def IsForgetNode (T : RootedTreeDecomposition G) (t : T.Node) : Prop :=
  ∃ (child : T.Node) (v : V),
    T.HasUniqueChild t child ∧
      v ∈ T.bag child ∧
      T.bag t = T.bag child \ {v}

/--
`t` has exactly two children.

The witnesses `left` and `right` are distinct, are both children of `t`, and
every child of `t` is one of them.
-/
def HasExactlyTwoChildren (t : T.Node) : Prop :=
  ∃ left right : T.Node,
    left ≠ right ∧
      T.IsChild t left ∧
      T.IsChild t right ∧
      (∀ child : T.Node, T.IsChild t child -> child = left ∨ child = right)

/--
`t` is a join node.

It has exactly two children, and the parent bag is equal to each child bag.
This is the usual binary join operation in a nice tree-decomposition.
-/
def IsJoinNode (T : RootedTreeDecomposition G) (t : T.Node) : Prop :=
  T.HasExactlyTwoChildren t ∧
    ∀ child : T.Node, T.IsChild t child -> T.bag t = T.bag child

/-- A leaf automatically satisfies the "at most two children" condition. -/
theorem IsLeafNode.hasAtMostTwoChildren {T : RootedTreeDecomposition G}
    {t : T.Node} (h : T.IsLeafNode t) :
    T.HasAtMostTwoChildren t := by
  refine ⟨t, t, ?_⟩
  intro child hchild
  exact False.elim (h child hchild)

/-- A node with a unique child automatically has at most two children. -/
theorem HasUniqueChild.hasAtMostTwoChildren {T : RootedTreeDecomposition G}
    {t child : T.Node} (h : T.HasUniqueChild t child) :
    T.HasAtMostTwoChildren t := by
  refine ⟨child, child, ?_⟩
  intro child' hchild'
  exact Or.inl (h.2 child' hchild')

/-- A node with exactly two children automatically has at most two children. -/
theorem HasExactlyTwoChildren.hasAtMostTwoChildren {T : RootedTreeDecomposition G}
    {t : T.Node} (h : T.HasExactlyTwoChildren t) :
    T.HasAtMostTwoChildren t := by
  rcases h with ⟨left, right, _hne, _hleft, _hright, hchildren⟩
  exact ⟨left, right, hchildren⟩

/-- An introduce node is unary. -/
theorem IsIntroduceNode.hasExactlyOneChild {T : RootedTreeDecomposition G}
    {t : T.Node} (h : T.IsIntroduceNode t) :
    T.HasExactlyOneChild t := by
  rcases h with ⟨child, _v, hchild, _hv, _hbag⟩
  exact ⟨child, hchild⟩

/-- A forget node is unary. -/
theorem IsForgetNode.hasExactlyOneChild {T : RootedTreeDecomposition G}
    {t : T.Node} (h : T.IsForgetNode t) :
    T.HasExactlyOneChild t := by
  rcases h with ⟨child, _v, hchild, _hv, _hbag⟩
  exact ⟨child, hchild⟩

/-- A join node has exactly two children. -/
theorem IsJoinNode.hasExactlyTwoChildren {T : RootedTreeDecomposition G}
    {t : T.Node} (h : T.IsJoinNode t) :
    T.HasExactlyTwoChildren t :=
  h.1

/-- A node with a unique child cannot also have exactly two children. -/
theorem not_hasExactlyTwoChildren_of_hasUniqueChild {T : RootedTreeDecomposition G}
    {t child : T.Node} (h : T.HasUniqueChild t child) :
    ¬ T.HasExactlyTwoChildren t := by
  rintro ⟨left, right, hne, hleft, hright, _hchildren⟩
  exact hne ((h.2 left hleft).trans (h.2 right hright).symm)

/-- A one-child node cannot also be a two-child node. -/
theorem not_hasExactlyTwoChildren_of_hasExactlyOneChild {T : RootedTreeDecomposition G}
    {t : T.Node} (h : T.HasExactlyOneChild t) :
    ¬ T.HasExactlyTwoChildren t := by
  rcases h with ⟨child, hchild⟩
  exact not_hasExactlyTwoChildren_of_hasUniqueChild hchild

/--
If a node has at most two children, is not a leaf, and does not have exactly
one child, then it has exactly two children.

This is the small case split that turns the global "at most two children" nice
condition into the join case when the leaf and unary cases do not apply.
-/
theorem hasExactlyTwoChildren_of_hasAtMostTwoChildren_of_not_isLeafNode_of_not_hasExactlyOneChild
    {T : RootedTreeDecomposition G} {t : T.Node}
    (hatMostTwo : T.HasAtMostTwoChildren t)
    (hleaf : ¬ T.IsLeafNode t)
    (hone : ¬ T.HasExactlyOneChild t) :
    T.HasExactlyTwoChildren t := by
  classical
  rw [IsLeafNode] at hleaf
  rcases not_forall.mp hleaf with ⟨left, hleft_not_not⟩
  have hleft : T.IsChild t left := by
    by_contra hnot
    exact hleft_not_not hnot
  have hnotUniqueLeft :
      ¬ ∀ child : T.Node, T.IsChild t child -> child = left := by
    intro hunique
    exact hone ⟨left, hleft, hunique⟩
  rcases not_forall.mp hnotUniqueLeft with ⟨right, hright_not_imp⟩
  have hright : T.IsChild t right := by
    by_contra hnot
    exact hright_not_imp (fun hchild => False.elim (hnot hchild))
  have hright_ne_left : right ≠ left := by
    intro hright_eq_left
    exact hright_not_imp (fun _ => hright_eq_left)
  have hleft_ne_right : left ≠ right := by
    intro hleft_eq_right
    exact hright_ne_left hleft_eq_right.symm
  rcases hatMostTwo with ⟨a, b, hatMostTwo⟩
  have hleft_ab := hatMostTwo left hleft
  have hright_ab := hatMostTwo right hright
  refine ⟨left, right, hleft_ne_right, hleft, hright, ?_⟩
  intro child hchild
  have hchild_ab := hatMostTwo child hchild
  rcases hleft_ab with hleft_a | hleft_b
  · rcases hright_ab with hright_a | hright_b
    · exact False.elim (hleft_ne_right (hleft_a.trans hright_a.symm))
    · rcases hchild_ab with hchild_a | hchild_b
      · exact Or.inl (hchild_a.trans hleft_a.symm)
      · exact Or.inr (hchild_b.trans hright_b.symm)
  · rcases hright_ab with hright_a | hright_b
    · rcases hchild_ab with hchild_a | hchild_b
      · exact Or.inr (hchild_a.trans hright_a.symm)
      · exact Or.inl (hchild_b.trans hleft_b.symm)
    · exact False.elim (hleft_ne_right (hleft_b.trans hright_b.symm))

/--
Rewrite an introduce node into the more familiar union form.

The definition stores `bag child = bag t \ {v}`.  This theorem recovers
`bag t = bag child ∪ {v}` and the side condition `v ∉ bag child`.
-/
theorem IsIntroduceNode.exists_child_vertex {T : RootedTreeDecomposition G}
    {t : T.Node} (h : T.IsIntroduceNode t) :
    ∃ (child : T.Node) (v : V),
      T.HasUniqueChild t child ∧
        v ∉ T.bag child ∧
        v ∈ T.bag t ∧
        T.bag t = T.bag child ∪ {v} := by
  rcases h with ⟨child, v, hchild, hv_parent, hbag_child⟩
  refine ⟨child, v, hchild, ?_, hv_parent, ?_⟩
  · rw [hbag_child]
    simp
  · ext u
    constructor
    · intro hu
      by_cases huv : u = v
      · right
        simp [huv]
      · left
        rw [hbag_child]
        exact ⟨hu, by simp [huv]⟩
    · intro hu
      rcases hu with hu_child | hu_v
      · rw [hbag_child] at hu_child
        exact hu_child.1
      · subst u
        exact hv_parent

/--
Expose the child, forgotten vertex, and the fact that the forgotten vertex is
not present in the parent bag.
-/
theorem IsForgetNode.exists_child_vertex {T : RootedTreeDecomposition G}
    {t : T.Node} (h : T.IsForgetNode t) :
    ∃ (child : T.Node) (v : V),
      T.HasUniqueChild t child ∧
        v ∈ T.bag child ∧
        v ∉ T.bag t ∧
        T.bag t = T.bag child \ {v} := by
  rcases h with ⟨child, v, hchild, hv_child, hbag⟩
  refine ⟨child, v, hchild, hv_child, ?_, hbag⟩
  simp [hbag]

/--
Expose the two children of a join node and the two bag equalities.
-/
theorem IsJoinNode.exists_children {T : RootedTreeDecomposition G}
    {t : T.Node} (h : T.IsJoinNode t) :
    ∃ left right : T.Node,
      left ≠ right ∧
        T.IsChild t left ∧
        T.IsChild t right ∧
        (∀ child : T.Node, T.IsChild t child -> child = left ∨ child = right) ∧
        T.bag t = T.bag left ∧
        T.bag t = T.bag right := by
  rcases h with ⟨hchildren, hbags⟩
  rcases hchildren with ⟨left, right, hne, hleft, hright, hchildren⟩
  exact ⟨left, right, hne, hleft, hright, hchildren, hbags left hleft, hbags right hright⟩

/--
Predicate-style nice tree-decomposition.

This is the direct formalization of the note's local conditions:
the root and all leaves have empty bags, every node has at most two children,
unary nodes are introduce or forget nodes, and binary nodes are join nodes.
-/
def IsNice {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T : RootedTreeDecomposition G) : Prop :=
  T.bag T.root = ∅ ∧
  (∀ t : T.Node, T.IsLeafNode t -> T.bag t = ∅) ∧
  (∀ t : T.Node, T.HasAtMostTwoChildren t) ∧
  (∀ t : T.Node,
    T.HasExactlyOneChild t -> T.IsIntroduceNode t ∨ T.IsForgetNode t) ∧
  (∀ t : T.Node, T.HasExactlyTwoChildren t -> T.IsJoinNode t)

end RootedTreeDecomposition

/--
A mathematical nice tree-decomposition of `G`.

This extends `RootedTreeDecomposition`, so its root, node type, bags, and tree
are accessed directly, while `nice` records the local nice conditions as a
proposition.
-/
structure NiceTreeDecomposition {V : Type*} [Fintype V] {G : SimpleGraph V}
    extends RootedTreeDecomposition G where
  nice : toRootedTreeDecomposition.IsNice
