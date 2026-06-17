import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace GraphMSO

universe u

/--
A tree decomposition of a graph `G`.

The decomposition tree is represented as a `SimpleGraph` on the node type `Node`.
Each node carries a finite bag of vertices of `G`.
-/
structure TreeDecomposition {V : Type u} (G : SimpleGraph V) where
  /-- Nodes of the decomposition tree. -/
  Node : Type u
  /-- The tree structure on decomposition nodes. -/
  tree : SimpleGraph Node
  /-- The decomposition graph is a tree. -/
  isTree : tree.IsTree
  /-- The bag attached to each decomposition node. -/
  bag : Node -> Finset V
  /-- Every graph vertex appears in some bag. -/
  vertex_mem : forall v : V, Exists fun t : Node => Membership.mem (bag t) v
  /-- Every graph edge has both endpoints together in some bag. -/
  edge_mem :
    forall {u v : V}, G.Adj u v ->
      Exists fun t : Node => Membership.mem (bag t) u /\ Membership.mem (bag t) v
  /-- For each graph vertex, the nodes whose bags contain it form a connected subtree. -/
  running_intersection :
    forall v : V, (tree.induce {t : Node | Membership.mem (bag t) v}).Connected

namespace TreeDecomposition

variable {V : Type u} {G : SimpleGraph V}

/-- The decomposition-tree nodes whose bags contain the graph vertex `v`. -/
def bagsContaining (D : TreeDecomposition G) (v : V) : Set D.Node :=
  {t : D.Node | Membership.mem (D.bag t) v}

/-- The induced subtree on the bags containing `v`. -/
def bagsContainingTree (D : TreeDecomposition G) (v : V) : SimpleGraph (D.bagsContaining v) :=
  D.tree.induce (D.bagsContaining v)

theorem bagsContainingTree_connected (D : TreeDecomposition G) (v : V) :
    (D.bagsContainingTree v).Connected := by
  simpa [bagsContainingTree, bagsContaining] using D.running_intersection v

/-- The local width contribution of one bag, namely `|bag| - 1`. -/
def bagWidth (D : TreeDecomposition G) (t : D.Node) : Nat :=
  (D.bag t).card - 1

/--
`D.WidthAtMost k` means that every bag has at most `k + 1` vertices.
This is the usual `width(D) <= k` condition, phrased without taking a maximum.
-/
def WidthAtMost (D : TreeDecomposition G) (k : Nat) : Prop :=
  forall t : D.Node, (D.bag t).card <= k + 1

/-- The graph `G` admits a tree decomposition of width at most `k`. -/
def HasTreewidthAtMost (G : SimpleGraph V) (k : Nat) : Prop :=
  Exists fun D : TreeDecomposition G => D.WidthAtMost k

/-- A one-node decomposition whose only bag contains all vertices of a finite graph. -/
def singleBag (G : SimpleGraph V) [Fintype V] : TreeDecomposition G where
  Node := PUnit
  tree := SimpleGraph.emptyGraph PUnit
  isTree := by
    exact SimpleGraph.IsTree.of_subsingleton
  bag := fun _ => Finset.univ
  vertex_mem := by
    intro v
    exact Exists.intro PUnit.unit (by simp)
  edge_mem := by
    intro u v _
    exact Exists.intro PUnit.unit (by simp)
  running_intersection := by
    intro v
    haveI : Nonempty {t : PUnit | Membership.mem (Finset.univ : Finset V) v} :=
      Nonempty.intro (Subtype.mk PUnit.unit (by simp))
    exact SimpleGraph.Connected.of_subsingleton

theorem singleBag_widthAtMost_card (G : SimpleGraph V) [Fintype V] :
    (singleBag G).WidthAtMost (Fintype.card V) := by
  intro t
  simp [singleBag]

theorem hasTreewidthAtMost_card (G : SimpleGraph V) [Fintype V] :
    HasTreewidthAtMost G (Fintype.card V) :=
  Exists.intro (singleBag G) (singleBag_widthAtMost_card G)

end TreeDecomposition

end GraphMSO
