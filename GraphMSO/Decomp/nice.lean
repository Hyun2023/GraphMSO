import GraphMSO.Decomp.tree_decomp

namespace RootedTreeDecomposition

variable {V : Type*} {G : SimpleGraph V}

/-- A node with no children. -/
def IsLeafNode (T : RootedTreeDecomposition G) (t : T.decomp.Node) : Prop :=
  ∀ child : T.decomp.Node, ¬ T.IsChild t child

/-- An introduce node has one child and adds one graph vertex to the child's bag. -/
def IsIntroduceNode (T : RootedTreeDecomposition G) (t : T.decomp.Node) : Prop :=
  ∃ (child : T.decomp.Node) (v : V),
    T.HasUniqueChild t child ∧
      v ∉ T.bag child ∧
      T.bag t = T.bag child ∪ {v}

/-- A forget node has one child and removes one graph vertex from the child's bag. -/
def IsForgetNode (T : RootedTreeDecomposition G) (t : T.decomp.Node) : Prop :=
  ∃ (child : T.decomp.Node) (v : V),
    T.HasUniqueChild t child ∧
      v ∈ T.bag child ∧
      T.bag t = T.bag child \ {v}

/-- A join node has two children, and the three bags are equal. -/
def IsJoinNode (T : RootedTreeDecomposition G) (t : T.decomp.Node) : Prop :=
  ∃ left right : T.decomp.Node,
    left ≠ right ∧
      T.IsChild t left ∧
      T.IsChild t right ∧
      (∀ child : T.decomp.Node, T.IsChild t child -> child = left ∨ child = right) ∧
      T.bag t = T.bag left ∧
      T.bag t = T.bag right

theorem IsIntroduceNode.exists_child_vertex {T : RootedTreeDecomposition G}
    {t : T.decomp.Node} (h : T.IsIntroduceNode t) :
    ∃ (child : T.decomp.Node) (v : V),
      T.HasUniqueChild t child ∧
        v ∉ T.bag child ∧
        v ∈ T.bag t ∧
        T.bag t = T.bag child ∪ {v} := by
  rcases h with ⟨child, v, hchild, hv_child, hbag⟩
  refine ⟨child, v, hchild, hv_child, ?_, hbag⟩
  simp [hbag]

theorem IsForgetNode.exists_child_vertex {T : RootedTreeDecomposition G}
    {t : T.decomp.Node} (h : T.IsForgetNode t) :
    ∃ (child : T.decomp.Node) (v : V),
      T.HasUniqueChild t child ∧
        v ∈ T.bag child ∧
        v ∉ T.bag t ∧
        T.bag t = T.bag child \ {v} := by
  rcases h with ⟨child, v, hchild, hv_child, hbag⟩
  refine ⟨child, v, hchild, hv_child, ?_, hbag⟩
  simp [hbag]

theorem IsJoinNode.exists_children {T : RootedTreeDecomposition G}
    {t : T.decomp.Node} (h : T.IsJoinNode t) :
    ∃ left right : T.decomp.Node,
      left ≠ right ∧
        T.IsChild t left ∧
        T.IsChild t right ∧
        (∀ child : T.decomp.Node, T.IsChild t child -> child = left ∨ child = right) ∧
        T.bag t = T.bag left ∧
        T.bag t = T.bag right := by
  exact h

def IsNice {V : Type*} {G : SimpleGraph V}
    (T : RootedTreeDecomposition G) : Prop :=
  ∀ t : T.decomp.Node,
    T.IsLeafNode t ∨ T.IsIntroduceNode t ∨ T.IsForgetNode t ∨ T.IsJoinNode t

end RootedTreeDecomposition

/-- A rooted tree-decomposition is nice if every node is leaf, introduce, forget, or join. -/


structure NiceTreeDecomposition {V : Type*} {G : SimpleGraph V} where
    T : RootedTreeDecomposition G
    nice : T.IsNice
