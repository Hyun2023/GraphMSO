import GraphMSO.Decomp.nice

/-!
# Constructor-style nice tree-decompositions

`GraphMSO.Decomp.nice` contains the predicate-style definition:
`NiceTreeDecomposition` is a rooted tree-decomposition together with a global
`IsNice` proof.

This file contains the algorithm-facing constructor-style version.  It keeps
the same `RootedTreeDecomposition` data, but stores an explicit classification
of every node as a leaf, introduce, forget, or join node.
-/

open scoped Classical

namespace RootedTreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/--
An explicit constructor-style classification of one node of a rooted
tree-decomposition.

Unlike `IsNice`, which is a bundled global predicate, `NiceNodeKind T t` is
data that can be case-split by algorithms.  It keeps the same mathematical
content as the four local nice-node alternatives:

* `leaf`: no children and empty bag,
* `introduce`: one child and one vertex added from child to parent,
* `forget`: one child and one vertex removed from child to parent,
* `join`: two children and all three bags equal.
-/
inductive NiceNodeKind (T : RootedTreeDecomposition G) (t : T.Node) : Prop where
  | leaf (hleaf : T.IsLeafNode t) (hbag : T.bag t = ∅) :
      NiceNodeKind T t
  | introduce (hintro : T.IsIntroduceNode t) :
      NiceNodeKind T t
  | forget (hforget : T.IsForgetNode t) :
      NiceNodeKind T t
  | join (hjoin : T.IsJoinNode t) :
      NiceNodeKind T t

namespace NiceNodeKind

/-- A node classified by `NiceNodeKind` has at most two children. -/
theorem hasAtMostTwoChildren {T : RootedTreeDecomposition G} {t : T.Node}
    (h : T.NiceNodeKind t) :
    T.HasAtMostTwoChildren t := by
  cases h with
  | leaf hleaf hbag =>
      exact hleaf.hasAtMostTwoChildren
  | introduce hintro =>
      rcases hintro.hasExactlyOneChild with ⟨child, hchild⟩
      exact hchild.hasAtMostTwoChildren
  | forget hforget =>
      rcases hforget.hasExactlyOneChild with ⟨child, hchild⟩
      exact hchild.hasAtMostTwoChildren
  | join hjoin =>
      exact hjoin.hasExactlyTwoChildren.hasAtMostTwoChildren

/--
If a classified node is actually a leaf, then its bag is empty.

This is the leaf-bag part of `IsNice`, recovered from constructor-style data.
-/
theorem leaf_bag_empty {T : RootedTreeDecomposition G} {t : T.Node}
    (h : T.NiceNodeKind t) (hleaf : T.IsLeafNode t) :
    T.bag t = ∅ := by
  cases h with
  | leaf _ hbag =>
      exact hbag
  | introduce hintro =>
      rcases hintro.hasExactlyOneChild with ⟨child, hchild⟩
      exact False.elim (hleaf child hchild.1)
  | forget hforget =>
      rcases hforget.hasExactlyOneChild with ⟨child, hchild⟩
      exact False.elim (hleaf child hchild.1)
  | join hjoin =>
      rcases hjoin.hasExactlyTwoChildren with ⟨left, _right, _hne, hleft, _hright, _hchildren⟩
      exact False.elim (hleaf left hleft)

/--
If a classified node has exactly one child, then it is either introduce or
forget.
-/
theorem one_child_intro_or_forget {T : RootedTreeDecomposition G} {t : T.Node}
    (h : T.NiceNodeKind t) (hone : T.HasExactlyOneChild t) :
    T.IsIntroduceNode t ∨ T.IsForgetNode t := by
  cases h with
  | leaf hleaf _hbag =>
      rcases hone with ⟨child, hchild⟩
      exact False.elim (hleaf child hchild.1)
  | introduce hintro =>
      exact Or.inl hintro
  | forget hforget =>
      exact Or.inr hforget
  | join hjoin =>
      exact False.elim
        ((not_hasExactlyTwoChildren_of_hasExactlyOneChild hone)
          hjoin.hasExactlyTwoChildren)

/-- If a classified node has exactly two children, then it is a join node. -/
theorem two_children_join {T : RootedTreeDecomposition G} {t : T.Node}
    (h : T.NiceNodeKind t) (htwo : T.HasExactlyTwoChildren t) :
    T.IsJoinNode t := by
  cases h with
  | leaf hleaf _hbag =>
      rcases htwo with ⟨left, _right, _hne, hleft, _hright, _hchildren⟩
      exact False.elim (hleaf left hleft)
  | introduce hintro =>
      exact False.elim
        ((not_hasExactlyTwoChildren_of_hasExactlyOneChild
          hintro.hasExactlyOneChild) htwo)
  | forget hforget =>
      exact False.elim
        ((not_hasExactlyTwoChildren_of_hasExactlyOneChild
          hforget.hasExactlyOneChild) htwo)
  | join hjoin =>
      exact hjoin

end NiceNodeKind

end RootedTreeDecomposition

/--
Constructor-style nice tree-decomposition of `G`.

This version keeps all mathematical tree-decomposition data by extending
`RootedTreeDecomposition`, but replaces the global `IsNice` predicate by
explicit node-classification data.  Algorithms can inspect `nodeKind t` and
case-split into the leaf, introduce, forget, and join cases without having to
reconstruct the classification from the global predicate each time.
-/
structure InductiveNiceTreeDecomposition {V : Type*} [Fintype V] {G : SimpleGraph V}
    extends RootedTreeDecomposition G where
  /-- The root bag is empty, as in the standard definition of nice decompositions. -/
  root_empty : toRootedTreeDecomposition.bag root = ∅
  /-- Every node is explicitly classified as leaf, introduce, forget, or join. -/
  nodeKind :
    ∀ t : Node, toRootedTreeDecomposition.NiceNodeKind t

namespace InductiveNiceTreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/--
Forget the constructor-style node classification and recover the predicate-style
nice tree-decomposition.
-/
def toNiceTreeDecomposition (T : InductiveNiceTreeDecomposition (G := G)) :
    NiceTreeDecomposition (G := G) :=
  { T.toRootedTreeDecomposition with
    nice := by
      refine ⟨T.root_empty, ?_, ?_, ?_, ?_⟩
      · intro t hleaf
        exact (T.nodeKind t).leaf_bag_empty hleaf
      · intro t
        exact (T.nodeKind t).hasAtMostTwoChildren
      · intro t hone
        exact (T.nodeKind t).one_child_intro_or_forget hone
      · intro t htwo
        exact (T.nodeKind t).two_children_join htwo }

/-- The predicate-style nice proof obtained from an inductive-style decomposition. -/
theorem isNice (T : InductiveNiceTreeDecomposition (G := G)) :
    T.toRootedTreeDecomposition.IsNice :=
  T.toNiceTreeDecomposition.nice

end InductiveNiceTreeDecomposition

namespace NiceTreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/--
Recover constructor-style node data from the predicate-style nice conditions.

For each node, we first check whether it is a leaf.  If not, we check whether it
has exactly one child.  If neither case applies, the global "at most two
children" condition forces the node to have exactly two children, hence it is a
join node.
-/
noncomputable def toInductiveTreeDecomposition
    (T : NiceTreeDecomposition (G := G)) :
    InductiveNiceTreeDecomposition (G := G) :=
  { T.toRootedTreeDecomposition with
    root_empty := T.nice.1
    nodeKind := by
      intro t
      classical
      let R : RootedTreeDecomposition G := T.toRootedTreeDecomposition
      rcases T.nice with ⟨_hroot, hleafBag, hatMostTwo, hunary, hbinary⟩
      by_cases hleaf : R.IsLeafNode t
      · exact RootedTreeDecomposition.NiceNodeKind.leaf hleaf (hleafBag t hleaf)
      · by_cases hone : R.HasExactlyOneChild t
        · rcases hunary t hone with hintro | hforget
          · exact RootedTreeDecomposition.NiceNodeKind.introduce hintro
          · exact RootedTreeDecomposition.NiceNodeKind.forget hforget
        · have htwo : R.HasExactlyTwoChildren t :=
            RootedTreeDecomposition.hasExactlyTwoChildren_of_hasAtMostTwoChildren_of_not_isLeafNode_of_not_hasExactlyOneChild
              (T := R) (hatMostTwo t) hleaf hone
          exact RootedTreeDecomposition.NiceNodeKind.join (hbinary t htwo) }

/--
The predicate-style decomposition recovered from `toInductiveTreeDecomposition`
has the same rooted tree-decomposition data.
-/
@[simp] theorem toInductiveTreeDecomposition_toNiceTreeDecomposition_rooted
    (T : NiceTreeDecomposition (G := G)) :
    T.toInductiveTreeDecomposition.toNiceTreeDecomposition.toRootedTreeDecomposition =
      T.toRootedTreeDecomposition :=
  rfl

/-- Converting to constructor-style and back preserves the global `IsNice` proof. -/
theorem toInductiveTreeDecomposition_isNice
    (T : NiceTreeDecomposition (G := G)) :
    T.toInductiveTreeDecomposition.toRootedTreeDecomposition.IsNice :=
  T.toInductiveTreeDecomposition.isNice

end NiceTreeDecomposition
