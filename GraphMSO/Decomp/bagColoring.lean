import GraphMSO.Decomp.tree_decomp

/-!
Bag colorings for tree decompositions.

In the lecture note, a bag-injective coloring is a map
`c : V(G) -> {0, ..., omega}` such that no bag contains two vertices with the
same color.  We represent `{0, ..., omega}` as `Fin (omega + 1)` and the
bag-injectivity condition as Mathlib's `Set.InjOn`.
-/

/-- Courcelle's finite color set `{0, ..., omega}`. -/
abbrev BagColorSet (omega : ℕ) : Type :=
  Fin (omega + 1)

namespace TreeDecomposition

variable {V : Type*} {G : SimpleGraph V}

/-! ## Main definition: BagColoring -/

/-- A coloring is bag-injective if every bag contains at most one vertex of each color. -/
def IsBagColoring (D : TreeDecomposition G) {k : ℕ} (color : V -> Fin k) : Prop :=
  ∀ t : D.Node, Set.InjOn color (D.bag t)

/-- A Courcelle bag-coloring using colors `{0, ..., omega}`. -/
def BagColoring (D : TreeDecomposition G) (omega : ℕ) : Type _ :=
  { color : V -> BagColorSet omega // D.IsBagColoring color }

theorem eq_of_mem_bag_of_color_eq {D : TreeDecomposition G} {k : ℕ}
    {color : V -> Fin k} (hcolor : D.IsBagColoring color)
    {t : D.Node} {u v : V} (hu : u ∈ D.bag t) (hv : v ∈ D.bag t)
    (h : color u = color v) :
    u = v :=
  hcolor t hu hv h

end TreeDecomposition

namespace RootedTreeDecomposition

variable {V : Type*} {G : SimpleGraph V}

/-! ## Main definition: RootedTreeDecomposition.BagColoring -/

/-- Bag-injectivity for a rooted tree decomposition, forwarded to the underlying decomposition. -/
def IsBagColoring (T : RootedTreeDecomposition G) {k : ℕ} (color : V -> Fin k) : Prop :=
  T.decomp.IsBagColoring color

/-- A Courcelle bag-coloring of a rooted tree decomposition. -/
def BagColoring (T : RootedTreeDecomposition G) (omega : ℕ) : Type _ :=
  T.decomp.BagColoring omega

theorem eq_of_mem_bag_of_color_eq {T : RootedTreeDecomposition G} {k : ℕ}
    {color : V -> Fin k} (hcolor : T.IsBagColoring color)
    {t : T.decomp.Node} {u v : V} (hu : u ∈ T.bag t) (hv : v ∈ T.bag t)
    (h : color u = color v) :
    u = v :=
  hcolor t hu hv h

end RootedTreeDecomposition
