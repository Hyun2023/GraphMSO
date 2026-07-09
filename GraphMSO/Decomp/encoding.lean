import GraphMSO.Decomp.sigmaTree
import GraphMSO.Decomp.nodeConeGraph
import GraphMSO.Decomp.realization

/-!
# Encoding a colored decomposition as a Σ-tree

This file formalizes the encoding step of the lecture note: a rooted
tree-decomposition of a `τ_P`-graph, together with a bag-injective coloring,
is turned into a `SigmaTree` by relabeling every bag vertex with its color.

* `RootedTreeDecomposition.encodeLetter` is the Σ-letter at one node: its
  vertices are the colors of the bag, its root set is the colors of the
  adhesion, and adjacency/predicate tags are read off the original structure
  through the (bag-unique) vertex of each color.
* `RootedTreeDecomposition.encode` is the Σ-tree with the same underlying tree
  and root, labeled by `encodeLetter`.
* `RootedTreeDecomposition.encode_isLegal` is the forward half of the
  lecture-note lemma "legal iff encoding": every encoding is legal.

The final theorems produce legal encodings from a width bound alone, both for
the mathematical `RootedTreeDecomposition` and, through the realization
transfer lemmas, for the constructor-coded `InductiveNiceTreeDecomposition`.
-/

namespace RootedTreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}
variable {P : Type*} {omega : ℕ}

/-! ## Main definition: encodeLetter -/

/--
The Σ_ω-letter of the encoding at node `t`.

Vertices are the colors occurring in the bag of `t`, the root set records the
colors occurring in the adhesion of `t`, and adjacency and unary-predicate
tags are inherited from the vertices of `G` realizing each color.  Because the
coloring is injective on bags, each color determines a unique bag vertex, so
no information inside a single bag is lost.
-/
def encodeLetter (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color)
    (t : T.Node) : SigmaLetter P omega where
  verts := color '' T.bag t
  G :=
    { Adj := fun i j =>
        ∃ u v : V, u ∈ T.bag t ∧ v ∈ T.bag t ∧
          color u = i.1 ∧ color v = j.1 ∧ G.Adj u v
      symm := by
        rintro i j ⟨u, v, hu, hv, hcu, hcv, hadj⟩
        exact ⟨v, u, hv, hu, hcv, hcu, hadj.symm⟩
      loopless := by
        rintro i ⟨u, v, hu, hv, hcu, hcv, hadj⟩
        have huv : u = v := hcolor t hu hv (hcu.trans hcv.symm)
        subst huv
        exact G.loopless u hadj }
  R := {i | i.1 ∈ color '' T.adhesion t}
  tag := fun p i => ∃ u : V, u ∈ T.bag t ∧ color u = i.1 ∧ vpred p u

section EncodeLetter

variable (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color)

@[simp] theorem encodeLetter_hasVertex_iff (t : T.Node) (i : BagColorSet omega) :
    (T.encodeLetter vpred color hcolor t).HasVertex i ↔ i ∈ color '' T.bag t :=
  Iff.rfl

theorem encodeLetter_rootContains_iff (t : T.Node) (i : BagColorSet omega) :
    (T.encodeLetter vpred color hcolor t).RootContains i ↔
      i ∈ color '' T.adhesion t := by
  constructor
  · rintro ⟨hi, hroot⟩
    exact hroot
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, T.adhesion_subset_bag t hu, rfl⟩, ⟨u, hu, rfl⟩⟩

theorem encodeLetter_adjOnColors_iff (t : T.Node) (i j : BagColorSet omega) :
    (T.encodeLetter vpred color hcolor t).AdjOnColors i j ↔
      ∃ u v : V, u ∈ T.bag t ∧ v ∈ T.bag t ∧
        color u = i ∧ color v = j ∧ G.Adj u v := by
  constructor
  · rintro ⟨hi, hj, hadj⟩
    exact hadj
  · rintro ⟨u, v, hu, hv, hcu, hcv, hadj⟩
    exact ⟨⟨u, hu, hcu⟩, ⟨v, hv, hcv⟩, u, v, hu, hv, hcu, hcv, hadj⟩

theorem encodeLetter_tagOnColor_iff (t : T.Node) (p : P) (i : BagColorSet omega) :
    (T.encodeLetter vpred color hcolor t).TagOnColor p i ↔
      ∃ u : V, u ∈ T.bag t ∧ color u = i ∧ vpred p u := by
  constructor
  · rintro ⟨hi, htag⟩
    exact htag
  · rintro ⟨u, hu, hcu, hp⟩
    exact ⟨⟨u, hu, hcu⟩, u, hu, hcu, hp⟩

@[simp] theorem encodeLetter_rootEmpty_root :
    (T.encodeLetter vpred color hcolor T.root).RootEmpty := by
  ext i
  simp [encodeLetter]

end EncodeLetter

/-! ## Main definition: encode -/

/--
The encoding of `(G, vpred, color, (T, bag))` as a Σ-tree: the same underlying
rooted tree, with each node labeled by its color-renamed bag letter.
-/
def encode (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color) :
    SigmaTree P omega where
  Node := T.Node
  T := T.T
  T_istree := T.T_istree
  root := T.root
  letter := T.encodeLetter vpred color hcolor

section Encode

variable (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color)

@[simp] theorem encode_root :
    (T.encode vpred color hcolor).root = T.root :=
  rfl

@[simp] theorem encode_letter (t : T.Node) :
    (T.encode vpred color hcolor).letter t =
      T.encodeLetter vpred color hcolor t :=
  rfl

/-- The parent function of the encoded Σ-tree is the parent function of the
decomposition; both are the penultimate node of the chosen root path in the
same tree. -/
theorem encode_parent (t : T.Node) :
    (T.encode vpred color hcolor).parent t = T.parent t :=
  rfl

end Encode

/-! ## Legality of the encoding -/

/--
The compatibility step of legality.  If `adh t = bag t ∩ bag s` — as happens
for `s` the parent of a non-root `t` — then the letter at `t` is compatible
with the letter at `s`: root colors of the child occur in the parent, and
adjacency and predicate tags agree on the shared root colors.

The proof is the lecture note's: a root color identifies a unique vertex of
the adhesion, and by bag-injectivity that vertex is also the unique vertex of
its color in either bag, so both letters read their data off the same
vertices of `G`.
-/
theorem encodeLetter_compatible (T : RootedTreeDecomposition G)
    (vpred : P → V → Prop) (color : V -> BagColorSet omega)
    (hcolor : T.IsBagColoring color) {t s : T.Node}
    (hadh : T.adhesion t = T.bag t ∩ T.bag s) :
    SigmaLetter.Compatible (T.encodeLetter vpred color hcolor t)
      (T.encodeLetter vpred color hcolor s) := by
  have hsub_t : T.adhesion t ⊆ T.bag t := T.adhesion_subset_bag t
  have hsub_s : T.adhesion t ⊆ T.bag s := by
    rw [hadh]
    exact Set.inter_subset_right
  refine ⟨?_, ?_, ?_⟩
  · -- root colors of the child occur in the parent letter
    intro i hi
    rw [encodeLetter_rootContains_iff] at hi
    rcases hi with ⟨u, hu, rfl⟩
    exact ⟨u, hsub_s hu, rfl⟩
  · -- adjacency agrees on shared root colors
    intro i j hi hj
    rw [encodeLetter_rootContains_iff] at hi hj
    rcases hi with ⟨u₀, hu₀, hcu₀⟩
    rcases hj with ⟨v₀, hv₀, hcv₀⟩
    rw [encodeLetter_adjOnColors_iff, encodeLetter_adjOnColors_iff]
    constructor
    · rintro ⟨u, v, hu, hv, hcu, hcv, hadj⟩
      have hu_eq : u = u₀ :=
        hcolor t hu (hsub_t hu₀) (hcu.trans hcu₀.symm)
      have hv_eq : v = v₀ :=
        hcolor t hv (hsub_t hv₀) (hcv.trans hcv₀.symm)
      subst hu_eq hv_eq
      exact ⟨u, v, hsub_s hu₀, hsub_s hv₀, hcu, hcv, hadj⟩
    · rintro ⟨u, v, hu, hv, hcu, hcv, hadj⟩
      have hu_eq : u = u₀ :=
        hcolor s hu (hsub_s hu₀) (hcu.trans hcu₀.symm)
      have hv_eq : v = v₀ :=
        hcolor s hv (hsub_s hv₀) (hcv.trans hcv₀.symm)
      subst hu_eq hv_eq
      exact ⟨u, v, hsub_t hu₀, hsub_t hv₀, hcu, hcv, hadj⟩
  · -- unary predicate tags agree on shared root colors
    intro p i hi
    rw [encodeLetter_rootContains_iff] at hi
    rcases hi with ⟨u₀, hu₀, hcu₀⟩
    rw [encodeLetter_tagOnColor_iff, encodeLetter_tagOnColor_iff]
    constructor
    · rintro ⟨u, hu, hcu, hp⟩
      have hu_eq : u = u₀ :=
        hcolor t hu (hsub_t hu₀) (hcu.trans hcu₀.symm)
      subst hu_eq
      exact ⟨u, hsub_s hu₀, hcu, hp⟩
    · rintro ⟨u, hu, hcu, hp⟩
      have hu_eq : u = u₀ :=
        hcolor s hu (hsub_s hu₀) (hcu.trans hcu₀.symm)
      subst hu_eq
      exact ⟨u, hsub_t hu₀, hcu, hp⟩

/-- Every encoding is legal.  This is the forward half of the lecture-note
lemma "a Σ-tree is legal iff it is an encoding". -/
theorem encode_isLegal (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color) :
    (T.encode vpred color hcolor).IsLegal := by
  constructor
  · exact T.encodeLetter_rootEmpty_root vpred color hcolor
  · intro t hroot
    exact T.encodeLetter_compatible vpred color hcolor
      (T.adhesion_eq_inter_parent hroot)

/--
Existence form of the encoding theorem: a rooted tree-decomposition of width
at most `omega` admits a bag-injective coloring whose encoding is a legal
Σ-tree.
-/
theorem exists_encode_isLegal (T : RootedTreeDecomposition G)
    (vpred : P → V → Prop)
    (hwidth : T.toTreeDecomposition.HasWidth omega) :
    ∃ (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color),
      (T.encode vpred color hcolor).IsLegal := by
  obtain ⟨color, hcolor⟩ := T.exists_bagColoring_of_hasWidth' omega hwidth
  exact ⟨color, hcolor, T.encode_isLegal vpred color hcolor⟩

end RootedTreeDecomposition

namespace InductiveNiceTreeDecomposition

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {P : Type*} {omega : ℕ}

/--
The encoding of an inductive nice tree-decomposition, given a coloring that is
bag-injective on the coded tree.  The realization transfer lemma converts the
coded bag-injectivity into the mathematical one required by `encode`.
-/
def encode (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V -> BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) : SigmaTree P omega :=
  T.toRootedTreeDecomposition.encode vpred color
    ((T.isBagColoring_iff color).2 hcolor)

/-- The encoding of an inductive nice tree-decomposition is legal. -/
theorem encode_isLegal (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V -> BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) :
    (T.encode vpred color hcolor).IsLegal :=
  T.toRootedTreeDecomposition.encode_isLegal vpred color _

/--
Existence form over the coded interface: a width bound on the coded tree alone
produces a coloring and a legal encoding.  Both the width bound and the
resulting bag-injectivity cross the realization via the transfer lemmas.
-/
theorem exists_encode_isLegal (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (hwidth : T.tree.HasWidth omega) :
    ∃ (color : V -> BagColorSet omega) (hcolor : T.tree.IsBagColoring color),
      (T.encode vpred color hcolor).IsLegal := by
  obtain ⟨color, hcolor⟩ := T.exists_bagColoring_of_codeHasWidth omega hwidth
  exact ⟨color, hcolor, T.encode_isLegal vpred color hcolor⟩

end InductiveNiceTreeDecomposition
