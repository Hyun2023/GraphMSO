import GraphMSO.Decomp.bagColoring
import GraphMSO.Decomp.rootedGraph

/-!
Node graphs and cone graphs associated with a rooted tree decomposition.

The lecture note uses two rooted graphs at a decomposition node `t`.

* The node graph is the graph induced by the current bag `beta(t)`, rooted at
  the adhesion, and labeled by the bag coloring on the whole bag.
* The cone graph is the graph induced by the whole cone below `t`, rooted and
  labeled only on the adhesion.  The interior of the cone is intentionally not
  labeled: those labels are local to the subproblem and should not remain as
  the boundary after gluing.
-/

namespace RootedTreeDecomposition

variable {V : Type*} {G : SimpleGraph V}

/-- The bag of `t` is contained in the cone below `t`. -/
theorem bag_subset_cone (T : RootedTreeDecomposition G) (t : T.decomp.Node) :
    T.bag t ⊆ T.cone t := by
  intro v hv
  exact ⟨t, Relation.ReflTransGen.refl, hv⟩

/-- The adhesion of `t` is contained in the bag of `t`. -/
theorem adhesion_subset_bag (T : RootedTreeDecomposition G) (t : T.decomp.Node) :
    T.adhesion t ⊆ T.bag t := by
  intro v hv
  by_cases hroot : t = T.root
  · subst t
    simp at hv
  · rw [T.adhesion_eq_inter_parent hroot] at hv
    exact hv.1

/-- The adhesion of `t` is contained in the cone below `t`. -/
theorem adhesion_subset_cone (T : RootedTreeDecomposition G) (t : T.decomp.Node) :
    T.adhesion t ⊆ T.cone t :=
  fun _ hv => T.bag_subset_cone t (T.adhesion_subset_bag t hv)

/-- Vertices of the node graph at `t`. -/
abbrev NodeGraphVertex (T : RootedTreeDecomposition G) (t : T.decomp.Node) : Type _ :=
  {v : V // v ∈ T.bag t}

/-- Vertices of the cone graph at `t`. -/
abbrev ConeGraphVertex (T : RootedTreeDecomposition G) (t : T.decomp.Node) : Type _ :=
  {v : V // v ∈ T.cone t}

/-! ## Main definition: Node Graph -/

/--
The node graph at `t`: the graph induced by the current bag, rooted at the
adhesion, and labeled by the bag coloring on every bag vertex.
-/
def nodeGraph (T : RootedTreeDecomposition G) {omega : ℕ} {P : Type*}
    (vpred : P → V → Prop)
    (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color)
    (t : T.decomp.Node) : KRootedGraph P (omega + 1) where
  V := T.NodeGraphVertex t
  G := G.induce (T.bag t)
  pred := fun p x => vpred p x.1
  R := {x | x.1 ∈ T.adhesion t}
  labelDom := Set.univ
  label := fun x => color x.1.1
  root_labeled := by
    intro _ _
    trivial
  label_injective := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact T.eq_of_mem_bag_of_color_eq hcolor x.1.2 y.1.2 hxy

/-! ## Main definition: Cone Graph -/

/--
The cone graph at `t`: the graph induced by all vertices appearing below `t`,
rooted at the adhesion, and labeled only on the adhesion.

The restricted label domain is deliberate.  After a cone is glued into its
parent context, only the adhesion remains visible as the boundary.
-/
def coneGraph (T : RootedTreeDecomposition G) {omega : ℕ} {P : Type*}
    (vpred : P → V → Prop)
    (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color)
    (t : T.decomp.Node) : KRootedGraph P (omega + 1) where
  V := T.ConeGraphVertex t
  G := G.induce (T.cone t)
  pred := fun p x => vpred p x.1
  R := {x | x.1 ∈ T.adhesion t}
  labelDom := {x | x.1 ∈ T.adhesion t}
  label := fun x => color x.1.1
  root_labeled := by
    intro _ hx
    exact hx
  label_injective := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact T.eq_of_mem_bag_of_color_eq hcolor
      (T.adhesion_subset_bag t x.2) (T.adhesion_subset_bag t y.2) hxy

end RootedTreeDecomposition
