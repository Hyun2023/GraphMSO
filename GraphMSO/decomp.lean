import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic

namespace GraphMSO

universe u

/--
An inductive rooted tree whose nodes carry bags of graph vertices.

A leaf is represented as `node bag 0 ...`, so there is only one constructor and
no duplicate leaf/nonleaf encoding.
-/
inductive DecompositionTree (V : Type u) : Type u where
  | node (bag : Set V) (arity : Nat) (child : Fin arity -> DecompositionTree V) :
      DecompositionTree V

namespace DecompositionTree

variable {V : Type u}

/-- The bag attached to the root. -/
def rootBag : DecompositionTree V -> Set V
  | .node bag _ _ => bag

/-- The number of children of the root. -/
def arity : DecompositionTree V -> Nat
  | .node _ arity _ => arity

/-- The `i`th child subtree. -/
def child : (T : DecompositionTree V) -> Fin (arity T) -> DecompositionTree V
  | .node _ _ child, i => child i

/-- A one-node tree. -/
def leaf (bag : Set V) : DecompositionTree V :=
  .node bag 0 (fun i => Fin.elim0 i)

/-- The tree contains `v` in at least one bag. -/
inductive ContainsVertex : DecompositionTree V -> V -> Prop
  | root (bag : Set V) arity child v (hv : v ∈ bag) :
      ContainsVertex (DecompositionTree.node bag arity child) v
  | child (bag : Set V) arity child v (i : Fin arity)
      (hchild : ContainsVertex (child i) v) :
      ContainsVertex (DecompositionTree.node bag arity child) v

/-- The tree contains `u` and `v` together in at least one bag. -/
inductive ContainsEdge : DecompositionTree V -> V -> V -> Prop
  | root (bag : Set V) arity child u v (hu : u ∈ bag) (hv : v ∈ bag) :
      ContainsEdge (DecompositionTree.node bag arity child) u v
  | child (bag : Set V) arity child u v (i : Fin arity)
      (hchild : ContainsEdge (child i) u v) :
      ContainsEdge (DecompositionTree.node bag arity child) u v

/-- Every bag in the tree satisfies `P`. -/
inductive AllBags (P : Set V -> Prop) : DecompositionTree V -> Prop
  | node (bag : Set V) arity child (hroot : P bag)
      (hchild : forall i : Fin arity, AllBags P (child i)) :
      AllBags P (DecompositionTree.node bag arity child)

/-- Every bag in the tree is finite. -/
def BagsFinite (T : DecompositionTree V) : Prop :=
  T.AllBags Set.Finite

/--
For one graph vertex `v`, the bags containing `v` form a connected rooted subtree.

Inductively, every child satisfies the property; if the root bag contains `v`,
then every child branch containing `v` starts with a child root bag containing
`v`; and if the root bag does not contain `v`, then at most one child branch can
contain `v`.
-/
inductive RunningIntersectionAt : DecompositionTree V -> V -> Prop
  | node (bag : Set V) arity child v
      (hchild : forall i : Fin arity, RunningIntersectionAt (child i) v)
      (hroot : v ∈ bag ->
        forall i : Fin arity, ContainsVertex (child i) v -> v ∈ rootBag (child i))
      (hunique : v ∉ bag ->
        forall i j : Fin arity, ContainsVertex (child i) v -> ContainsVertex (child j) v ->
          i = j) :
      RunningIntersectionAt (DecompositionTree.node bag arity child) v

/-- The running-intersection property for all graph vertices. -/
def RunningIntersection (T : DecompositionTree V) : Prop :=
  forall v : V, T.RunningIntersectionAt v

/--
`T.WidthAtMost k` means that every bag of `T` has at most `k + 1` vertices.
This is the usual `width(T) <= k` condition, phrased without taking a maximum.
-/
def WidthAtMost (T : DecompositionTree V) (k : Nat) : Prop :=
  T.AllBags (fun bag => bag.ncard <= k + 1)

end DecompositionTree

/--
`TreeDecomposition G T` means that the inductive tree `T` is a valid tree
decomposition of the graph `G`.
-/
inductive TreeDecomposition {V : Type u} (G : SimpleGraph V) : DecompositionTree V -> Prop where
  | mk (T : DecompositionTree V)
      (finite_bags : T.BagsFinite)
      (vertex_mem : forall v : V, T.ContainsVertex v)
      (edge_mem : forall {u v : V}, G.Adj u v -> T.ContainsEdge u v)
      (running_intersection : T.RunningIntersection) :
      TreeDecomposition G T

namespace TreeDecomposition

variable {V : Type u} {G : SimpleGraph V}

/-- The graph `G` admits a tree decomposition of width at most `k`. -/
def HasTreewidthAtMost (G : SimpleGraph V) (k : Nat) : Prop :=
  Exists fun T : DecompositionTree V => TreeDecomposition G T ∧ T.WidthAtMost k

/-- A one-node decomposition tree whose only bag contains all vertices of a finite graph. -/
def singleBag (_G : SimpleGraph V) [Fintype V] : DecompositionTree V :=
  DecompositionTree.leaf Set.univ

/-- The one-bag tree is a valid decomposition of any finite graph. -/
theorem singleBag_decomposition (G : SimpleGraph V) [Fintype V] :
    TreeDecomposition G (singleBag G) := by
  exact TreeDecomposition.mk (singleBag G)
    (DecompositionTree.AllBags.node (bag := Set.univ) (arity := 0)
      (child := fun i => Fin.elim0 i) (by simp) (fun i => Fin.elim0 i))
    (by
      intro v
      exact DecompositionTree.ContainsVertex.root Set.univ 0 (fun i => Fin.elim0 i) v
        (by simp))
    (by
      intro u v _
      exact DecompositionTree.ContainsEdge.root Set.univ 0 (fun i => Fin.elim0 i) u v
        (by simp) (by simp))
    (by
      intro v
      exact DecompositionTree.RunningIntersectionAt.node Set.univ 0 (fun i => Fin.elim0 i) v
        (fun i => Fin.elim0 i)
        (by intro _ i; exact Fin.elim0 i)
        (by intro _ i; exact Fin.elim0 i))

theorem singleBag_widthAtMost_card (G : SimpleGraph V) [Fintype V] :
    (singleBag G).WidthAtMost (Fintype.card V) := by
  exact DecompositionTree.AllBags.node (bag := Set.univ) (arity := 0)
    (child := fun i => Fin.elim0 i) (by simp) (fun i => Fin.elim0 i)

theorem hasTreewidthAtMost_card (G : SimpleGraph V) [Fintype V] :
    HasTreewidthAtMost G (Fintype.card V) :=
  Exists.intro (singleBag G) ⟨singleBag_decomposition G, singleBag_widthAtMost_card G⟩

end TreeDecomposition

end GraphMSO
