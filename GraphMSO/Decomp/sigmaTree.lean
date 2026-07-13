import GraphMSO.Decomp.rootedGraph
import GraphMSO.Decomp.bagColoring

/-!
Sigma trees for the tree-automata side of Courcelle's theorem.

For a fixed `omega`, the alphabet letter is a rooted graph whose vertices are
colors from `{0, ..., omega}`.  This is intentionally separate from
`KRootedGraph`: in a sigma letter, vertices are color names themselves, not
vertices of the original graph with labels attached.
-/

/-! ## Main definition: SigmaLetter -/

/-- A letter of `Sigma_omega`: a rooted `τ_P`-structure on a subset of the color
set — a rooted graph together with `tag`, recording for each present color which
unary predicates `p : P` hold of it. -/
structure SigmaLetter (P : Type*) (omega : ℕ) where
  verts : Set (BagColorSet omega)
  G : SimpleGraph verts
  R : Set verts
  tag : P → verts → Prop

namespace SigmaLetter

variable {P : Type*} {omega : ℕ}

instance instFinite [Finite P] : Finite (SigmaLetter P omega) := by
  classical
  let encode :
      SigmaLetter P omega →
        Σ verts : Set (BagColorSet omega),
          SimpleGraph verts × Set verts × (P → verts → Prop) :=
    fun A => ⟨A.verts, A.G, A.R, A.tag⟩
  have henc : Function.Injective encode := by
    intro A B h
    cases A
    cases B
    cases h
    rfl
  exact Finite.of_injective encode henc

/-- The letter contains the color `i` as a vertex. -/
def HasVertex (A : SigmaLetter P omega) (i : BagColorSet omega) : Prop :=
  i ∈ A.verts

/-- The letter contains the color `i` in its root/boundary set. -/
def RootContains (A : SigmaLetter P omega) (i : BagColorSet omega) : Prop :=
  ∃ hi : i ∈ A.verts, (⟨i, hi⟩ : A.verts) ∈ A.R

/-- The root/boundary set of the letter is empty. -/
def RootEmpty (A : SigmaLetter P omega) : Prop :=
  A.R = ∅

/-- Adjacency between two colors inside a sigma letter. -/
def AdjOnColors (A : SigmaLetter P omega) (i j : BagColorSet omega) : Prop :=
  ∃ (hi : i ∈ A.verts) (hj : j ∈ A.verts), A.G.Adj ⟨i, hi⟩ ⟨j, hj⟩

/-- The unary predicate `p` holds of color `i` inside a sigma letter (and `i` is
present in the letter). -/
def TagOnColor (A : SigmaLetter P omega) (p : P) (i : BagColorSet omega) : Prop :=
  ∃ hi : i ∈ A.verts, A.tag p ⟨i, hi⟩

/-! ## Main definition: SigmaLetter.Compatible -/

/--
Compatibility of a child letter with its parent letter.

This formalizes the legality condition from the lecture note: the child's root
colors must occur in the parent letter, the graph induced on those root colors
must agree with the parent graph, and every unary predicate must agree on those
root colors.
-/
def Compatible (child parent : SigmaLetter P omega) : Prop :=
  (∀ i : BagColorSet omega, child.RootContains i -> parent.HasVertex i) ∧
  (∀ i j : BagColorSet omega,
      child.RootContains i -> child.RootContains j ->
        (child.AdjOnColors i j ↔ parent.AdjOnColors i j)) ∧
  (∀ (p : P) (i : BagColorSet omega),
      child.RootContains i -> (child.TagOnColor p i ↔ parent.TagOnColor p i))

/-- A sigma letter as a `KRootedGraph`, with colors used as their own labels. -/
def toKRootedGraph (A : SigmaLetter P omega) : KRootedGraph P (omega + 1) where
  V := A.verts
  G := A.G
  pred := A.tag
  R := A.R
  labelDom := Set.univ
  label := fun x => x.1.1
  root_labeled := by
    intro _ _
    trivial
  label_injective := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy

end SigmaLetter

/-! ## Main definition: SigmaTree -/

/--
A rooted tree whose nodes are labeled by letters of `Sigma_omega`.

The tree is represented using Mathlib's `SimpleGraph.IsTree`, matching the
rooted tree-decomposition representation used elsewhere in this directory.
-/
structure SigmaTree (P : Type*) (omega : ℕ) where
  Node : Type*
  T : SimpleGraph Node
  T_istree : T.IsTree
  root : Node
  letter : Node -> SigmaLetter P omega

namespace SigmaTree

variable {P : Type*} {omega : ℕ}

/-- The unique path from the root to a sigma-tree node. -/
noncomputable def rootPath (S : SigmaTree P omega) (t : S.Node) :
    S.T.Walk S.root t :=
  (S.T_istree.existsUnique_path S.root t).choose

/-- The chosen root path is simple. -/
theorem rootPath_isPath (S : SigmaTree P omega) (t : S.Node) :
    (S.rootPath t).IsPath :=
  (S.T_istree.existsUnique_path S.root t).choose_spec.1

@[simp] theorem rootPath_root (S : SigmaTree P omega) :
    S.rootPath S.root = SimpleGraph.Walk.nil := by
  exact (SimpleGraph.Walk.isPath_iff_eq_nil (S.rootPath S.root)).mp
    (S.rootPath_isPath S.root)

/-- The parent of a node.  The parent of the root is defined to be the root. -/
noncomputable def parent (S : SigmaTree P omega) (t : S.Node) : S.Node :=
  (S.rootPath t).penultimate

@[simp] theorem parent_root (S : SigmaTree P omega) :
    S.parent S.root = S.root := by
  simp [parent]

/-- A non-root node is adjacent to its parent. -/
theorem parent_adj (S : SigmaTree P omega) {t : S.Node} (hroot : t ≠ S.root) :
    S.T.Adj (S.parent t) t := by
  exact (S.rootPath t).adj_penultimate (SimpleGraph.Walk.not_nil_of_ne hroot.symm)

/-- The child relation induced by the rooted tree. -/
def IsChild (S : SigmaTree P omega) (parent child : S.Node) : Prop :=
  child ≠ S.root ∧ parent = S.parent child

/-! ## Main definition: SigmaTree.Legality -/

/--
Legality of a sigma tree.

The root has empty boundary, and every non-root node is compatible with its
parent.  The root condition is included because the whole graph has no outside
context to glue to.
-/
def IsLegal (S : SigmaTree P omega) : Prop :=
  (S.letter S.root).RootEmpty ∧
    ∀ t : S.Node, t ≠ S.root ->
      SigmaLetter.Compatible (S.letter t) (S.letter (S.parent t))

theorem IsLegal.root_empty {S : SigmaTree P omega} (hlegal : S.IsLegal) :
    (S.letter S.root).RootEmpty :=
  hlegal.1

theorem IsLegal.compatible_of_isChild {S : SigmaTree P omega} (hlegal : S.IsLegal)
    {parent child : S.Node} (hchild : S.IsChild parent child) :
    SigmaLetter.Compatible (S.letter child) (S.letter parent) := by
  rw [hchild.2]
  exact hlegal.2 child hchild.1

end SigmaTree
