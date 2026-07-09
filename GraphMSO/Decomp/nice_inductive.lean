import GraphMSO.Decomp.nice

/-!
# Inductive nice tree-decompositions

`GraphMSO.Decomp.nice` defines a nice tree-decomposition as a rooted
tree-decomposition plus a global predicate `IsNice`.

This file is deliberately different: it introduces a programming-facing tree
code, defined by ordinary inductive constructors, and then relates that code to
a mathematical `RootedTreeDecomposition` by a separate realization proof.

The intended use is that algorithms recurse over `InductiveNiceTree`; the
realization fields say that this recursive tree is exactly the rooted
tree-decomposition already present in the mathematical development.
-/

open scoped Classical

universe u

/--
A constructor-coded nice tree whose type is indexed by its root bag.

The local bag discipline is carried by the constructors themselves:

* a leaf has empty bag,
* an introduce node adds one fresh vertex to its child bag,
* a forget node removes one present vertex from its child bag,
* a join node has two children with the same root bag.

This is the algorithm-facing object: definitions can recurse directly over
`leaf`, `introduce`, `forget`, and `join`.
-/
inductive InductiveNiceTree (V : Type u) : Set V -> Type (u + 1) where
  | leaf : InductiveNiceTree V ∅
  | introduce {bag : Set V} (v : V) (child : InductiveNiceTree V bag)
      (fresh : v ∉ bag) : InductiveNiceTree V (bag ∪ {v})
  | forget {bag : Set V} (v : V) (child : InductiveNiceTree V bag)
      (present : v ∈ bag) : InductiveNiceTree V (bag \ {v})
  | join {bag : Set V} (left right : InductiveNiceTree V bag) :
      InductiveNiceTree V bag


-- 계산구조 <-> 진짜수학구조
--   체킹  <->   성질만족

namespace InductiveNiceTree

variable {V : Type u}

/--
The finite type of positions/nodes inside a coded nice tree.

The root is represented by `PUnit.unit` for a leaf and by `none` for every
non-leaf constructor.  Child positions are embedded recursively.
-/
def Node {bag : Set V} (tree : InductiveNiceTree V bag) : Type (u + 1) :=
  match tree with
  | leaf => PUnit
  | introduce _ child _ => Option (Node child)
  | forget _ child _ => Option (Node child)
  | join left right => Option (Sum (Node left) (Node right))

/-- The root position of a coded nice tree. -/
def root {bag : Set V} (tree : InductiveNiceTree V bag) : Node tree :=
  match tree with
  | leaf => PUnit.unit
  | introduce _ _ _ => none
  | forget _ _ _ => none
  | join _ _ => none

/-- The bag at a coded tree position. -/
def nodeBag {bag : Set V} (tree : InductiveNiceTree V bag) :
    Node tree -> Set V :=
  match tree with
  | leaf => fun _ => ∅
  | introduce v child _ => fun
      | none => nodeBag child (root child) ∪ {v}
      | some n => nodeBag child n
  | forget v child _ => fun
      | none => nodeBag child (root child) \ {v}
      | some n => nodeBag child n
  | join left _right => fun
      | none => nodeBag left (root left)
      | some (Sum.inl n) => nodeBag left n
      | some (Sum.inr n) => nodeBag _right n

/-- The immediate children of a coded tree position, as explicit data. -/
def children {bag : Set V} (tree : InductiveNiceTree V bag) :
    Node tree -> List (Node tree) :=
  match tree with
  | leaf => fun _ => []
  | introduce _ child _ => fun
      | none => [some (root child)]
      | some n => (children child n).map some
  | forget _ child _ => fun
      | none => [some (root child)]
      | some n => (children child n).map some
  | join left right => fun
      | none => [some (Sum.inl (root left)), some (Sum.inr (root right))]
      | some (Sum.inl n) => (children left n).map (fun child => some (Sum.inl child))
      | some (Sum.inr n) => (children right n).map (fun child => some (Sum.inr child))

/-- The parent/child relation induced by the explicit `children` list. -/
def IsChild {bag : Set V} (tree : InductiveNiceTree V bag)
    (parent child : Node tree) : Prop :=
  child ∈ children tree parent

/-- The root bag index is exactly the bag of the root position. -/
@[simp] theorem nodeBag_root {bag : Set V} (tree : InductiveNiceTree V bag) :
    nodeBag tree (root tree) = bag := by
  induction tree with
  | leaf =>
      rfl
  | introduce v child _ ih =>
      simpa [nodeBag, root] using congrArg (fun s : Set V => s ∪ {v}) ih
  | forget v child _ ih =>
      simpa [nodeBag, root] using congrArg (fun s : Set V => s \ {v}) ih
  | join left _right ih_left _ih_right =>
      simpa [nodeBag, root] using ih_left

/-- The root children of an introduce node consist of the unique child root. -/
@[simp] theorem children_root_introduce {bag : Set V} (v : V)
    (child : InductiveNiceTree V bag) (fresh : v ∉ bag) :
    children (introduce v child fresh) (root (introduce v child fresh)) =
      [some (root child)] :=
  rfl

/-- The root children of a forget node consist of the unique child root. -/
@[simp] theorem children_root_forget {bag : Set V} (v : V)
    (child : InductiveNiceTree V bag) (present : v ∈ bag) :
    children (forget v child present) (root (forget v child present)) =
      [some (root child)] :=
  rfl

/-- The root children of a join node are the two child roots. -/
@[simp] theorem children_root_join {bag : Set V}
    (left right : InductiveNiceTree V bag) :
    children (join left right) (root (join left right)) =
      [some (Sum.inl (root left)), some (Sum.inr (root right))] :=
  rfl

/-- A coded nice tree has finitely many positions. -/
def nodeFintype {bag : Set V} (tree : InductiveNiceTree V bag) :
    Fintype (Node tree) :=
  match tree with
  | leaf => by
      change Fintype PUnit
      infer_instance
  | introduce _ child _ => by
      letI := nodeFintype child
      change Fintype (Option (Node child))
      infer_instance
  | forget _ child _ => by
      letI := nodeFintype child
      change Fintype (Option (Node child))
      infer_instance
  | join left right => by
      letI := nodeFintype left
      letI := nodeFintype right
      change Fintype (Option (Sum (Node left) (Node right)))
      infer_instance

instance instFintypeNode {bag : Set V} (tree : InductiveNiceTree V bag) :
    Fintype (Node tree) :=
  nodeFintype tree

namespace Realization

variable [Fintype V] {G : SimpleGraph V} {bag : Set V}

/--
Compatibility between a coded nice tree and a rooted tree-decomposition.

`realize` sends algorithmic positions to mathematical decomposition nodes.  The
remaining fields say that this map is bijective, preserves the root and bags,
and identifies the explicit child relation of the coded tree with the rooted
child relation of the decomposition.
-/
structure Realizes (tree : InductiveNiceTree V bag)
    (T : RootedTreeDecomposition G) where
  realize : Node tree -> T.Node
  realize_bijective : Function.Bijective realize
  root_eq : realize (root tree) = T.root
  bag_eq : ∀ n : Node tree, T.bag (realize n) = nodeBag tree n
  child_iff : ∀ parent child : Node tree,
    T.IsChild (realize parent) (realize child) ↔ tree.IsChild parent child

end Realization

export Realization (Realizes)

namespace Realizes

variable [Fintype V] {G : SimpleGraph V} {bag : Set V}
variable {tree : InductiveNiceTree V bag} {T : RootedTreeDecomposition G}

theorem root_bag_eq (R : Realizes tree T) :
    T.bag T.root = bag := by
  rw [← R.root_eq, R.bag_eq, nodeBag_root]

theorem child_iff_realize (R : Realizes tree T)
    (parent child : Node tree) :
    T.IsChild (R.realize parent) (R.realize child) ↔
      tree.IsChild parent child :=
  R.child_iff parent child

end Realizes

end InductiveNiceTree

/--
An inductive nice tree-decomposition of `G`.

This is a rooted tree-decomposition together with an explicit recursive nice
tree with empty root bag, plus a proof that the recursive tree realizes the
rooted tree-decomposition exactly.
-/
structure InductiveNiceTreeDecomposition {V : Type u} [Fintype V]
    {G : SimpleGraph V} extends RootedTreeDecomposition G where
  tree : InductiveNiceTree V ∅
  realization :
    InductiveNiceTree.Realizes tree toRootedTreeDecomposition


namespace InductiveNiceTreeDecomposition

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- The algorithm-facing node type of an inductive nice tree-decomposition. -/
abbrev CodeNode (T : InductiveNiceTreeDecomposition (G := G)) : Type (u + 1) :=
  InductiveNiceTree.Node T.tree

/-- The root of the algorithm-facing tree. -/
def codeRoot (T : InductiveNiceTreeDecomposition (G := G)) : T.CodeNode :=
  InductiveNiceTree.root T.tree

/-- The bag computed from the algorithm-facing tree at a code node. -/
def codeBag (T : InductiveNiceTreeDecomposition (G := G))
    (n : T.CodeNode) : Set V :=
  InductiveNiceTree.nodeBag T.tree n

/-- The immediate children available to algorithms by structural recursion. -/
def codeChildren (T : InductiveNiceTreeDecomposition (G := G))
    (n : T.CodeNode) : List T.CodeNode :=
  InductiveNiceTree.children T.tree n

/-- Interpret an algorithm-facing node as a node of the rooted decomposition. -/
def realize (T : InductiveNiceTreeDecomposition (G := G))
    (n : T.CodeNode) : T.Node :=
  T.realization.realize n

@[simp] theorem realize_codeRoot
    (T : InductiveNiceTreeDecomposition (G := G)) :
    T.realize T.codeRoot = T.root :=
  T.realization.root_eq

@[simp] theorem bag_realize
    (T : InductiveNiceTreeDecomposition (G := G)) (n : T.CodeNode) :
    T.toRootedTreeDecomposition.bag (T.realize n) = T.codeBag n :=
  T.realization.bag_eq n

/-- The mathematical root bag is empty because the coded tree is indexed by `∅`. -/
theorem root_empty (T : InductiveNiceTreeDecomposition (G := G)) :
    T.toRootedTreeDecomposition.bag T.root = ∅ :=
  InductiveNiceTree.Realizes.root_bag_eq T.realization

/-- Childhood agrees between the coded tree and the rooted decomposition. -/
theorem child_iff (T : InductiveNiceTreeDecomposition (G := G))
    (parent child : T.CodeNode) :
    T.toRootedTreeDecomposition.IsChild (T.realize parent) (T.realize child) ↔
      T.tree.IsChild parent child :=
  T.realization.child_iff parent child

end InductiveNiceTreeDecomposition
