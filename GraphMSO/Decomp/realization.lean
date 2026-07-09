import GraphMSO.Decomp.nice_inductive
import GraphMSO.Decomp.bagColoring

/-!
# Transfer of decomposition properties along a realization

`GraphMSO.Decomp.nice_inductive` relates the constructor-coded
`InductiveNiceTree` to the mathematical `RootedTreeDecomposition` through the
`Realizes` structure.  When a statement mixes the two representations, the
properties used on one side must be transported to the other side along the
realization map.

This file provides those transfer lemmas for the properties consumed by the
encoding layer of the Courcelle development:

* width bounds (`HasWidth`), and
* bag-injective colorings (`IsBagColoring`).

Both are stated as `iff`s, so either representation can be taken as the source
of truth.
-/

namespace InductiveNiceTree

universe u

variable {V : Type u}

/--
Width bound for a constructor-coded nice tree: every position bag has at most
`omega + 1` vertices.  This is the coded counterpart of
`TreeDecomposition.HasWidth`.
-/
def HasWidth {bag : Set V} (tree : InductiveNiceTree V bag) (omega : ℕ) : Prop :=
  ∀ n : Node tree, (nodeBag tree n).ncard ≤ omega + 1

/--
Bag-injectivity of a vertex coloring on a constructor-coded nice tree: the
coloring is injective on every position bag.  This is the coded counterpart of
`TreeDecomposition.IsBagColoring`.
-/
def IsBagColoring {bag : Set V} (tree : InductiveNiceTree V bag) {k : ℕ}
    (color : V -> Fin k) : Prop :=
  ∀ n : Node tree, Set.InjOn color (nodeBag tree n)

namespace Realization.Realizes

variable [Fintype V] {G : SimpleGraph V} {bag : Set V}
variable {tree : InductiveNiceTree V bag} {T : RootedTreeDecomposition G}

/-- A realization matches coded position bags with decomposition bags, so the
width bounds on the two sides are equivalent. -/
theorem hasWidth_iff (R : Realizes tree T) (omega : ℕ) :
    T.toTreeDecomposition.HasWidth omega ↔ tree.HasWidth omega := by
  constructor
  · intro h n
    rw [← R.bag_eq n]
    exact h (R.realize n)
  · intro h t
    obtain ⟨n, rfl⟩ := R.realize_bijective.2 t
    have hbag : T.toTreeDecomposition.bag (R.realize n) = nodeBag tree n :=
      R.bag_eq n
    rw [hbag]
    exact h n

/-- A realization matches coded position bags with decomposition bags, so
bag-injectivity of a coloring on the two sides is equivalent. -/
theorem isBagColoring_iff (R : Realizes tree T) {k : ℕ} (color : V -> Fin k) :
    T.IsBagColoring color ↔ tree.IsBagColoring color := by
  constructor
  · intro h n
    rw [← R.bag_eq n]
    exact h (R.realize n)
  · intro h t
    obtain ⟨n, rfl⟩ := R.realize_bijective.2 t
    have hbag : T.toTreeDecomposition.bag (R.realize n) = nodeBag tree n :=
      R.bag_eq n
    show Set.InjOn color (T.toTreeDecomposition.bag (R.realize n))
    rw [hbag]
    exact h n

end Realization.Realizes

end InductiveNiceTree

namespace InductiveNiceTreeDecomposition

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- Width transfer for an inductive nice tree-decomposition: the mathematical
width bound holds iff the coded width bound holds. -/
theorem hasWidth_iff (T : InductiveNiceTreeDecomposition (G := G)) (omega : ℕ) :
    T.toTreeDecomposition.HasWidth omega ↔ T.tree.HasWidth omega :=
  T.realization.hasWidth_iff omega

/-- Bag-coloring transfer for an inductive nice tree-decomposition. -/
theorem isBagColoring_iff (T : InductiveNiceTreeDecomposition (G := G)) {k : ℕ}
    (color : V -> Fin k) :
    T.toRootedTreeDecomposition.IsBagColoring color ↔
      T.tree.IsBagColoring color :=
  T.realization.isBagColoring_iff color

/--
A bag-injective coloring exists from a width bound stated purely on the coded
tree.  The proof crosses the realization: the coded width bound is transported
to the mathematical decomposition, the greedy coloring fact is applied there,
and bag-injectivity is transported back.
-/
theorem exists_bagColoring_of_codeHasWidth
    (T : InductiveNiceTreeDecomposition (G := G)) (omega : ℕ)
    (hwidth : T.tree.HasWidth omega) :
    ∃ color : V -> BagColorSet omega, T.tree.IsBagColoring color := by
  obtain ⟨color, hcolor⟩ :=
    T.toRootedTreeDecomposition.exists_bagColoring_of_hasWidth' omega
      ((T.hasWidth_iff omega).2 hwidth)
  exact ⟨color, (T.isBagColoring_iff color).1 hcolor⟩

end InductiveNiceTreeDecomposition
