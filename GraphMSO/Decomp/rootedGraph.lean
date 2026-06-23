import Mathlib
import GraphMSO.Decomp.tree_decomp

/-!
This file keeps the rooted-graph side of the Courcelle construction separate
from tree decompositions.

The gluing operation from the lecture note is partial: two rooted graphs can be
glued only when the second boundary can be matched, by labels, inside the first
graph.  Rather than defining a partial function immediately, we separate the
formalization into three layers.

* `Gluable A B` records the precondition saying that `A ⊕ B` is defined.
* `GluingData A B C` is explicit witness data saying that `C` is obtained by
  gluing `A` and `B`.
* `IsGluing A B C := Nonempty (GluingData A B C)` is the proposition-level
  predicate used in theorem statements.

This keeps theorem statements proof-irrelevant while still allowing later
proofs to unpack the concrete maps into the glued graph when needed.
-/

/-- A `k`-rooted graph: a graph with a root/boundary set and a partial injective
labeling whose domain contains the root. -/
structure KRootedGraph (k : ℕ) where
  V : Type*
  G : SimpleGraph V
  R : Set V
  labelDom : Set V
  label : labelDom -> Fin k
  root_labeled : R ⊆ labelDom
  label_injective : Function.Injective label

namespace KRootedGraph

variable {k : ℕ}

/--
`HasLabel H v i` means that the partial labeling of `H` is defined at `v`
and gives the label `i`.

This wrapper is useful because the labeling function has domain
`H.labelDom`, so using it directly constantly exposes subtype membership
proofs.  Most gluing conditions only care that a vertex has a certain label,
not which proof was used to view the vertex as an element of `labelDom`.
-/
def HasLabel (H : KRootedGraph k) (v : H.V) (i : Fin k) : Prop :=
  ∃ hv : v ∈ H.labelDom, H.label ⟨v, hv⟩ = i

/--
The label of a root vertex.

The definition of a rooted graph requires `R ⊆ labelDom`, so root vertices
have a total labeling even though labels are partial on the ambient vertex set.
This is the label used when matching the boundary of the second graph into the
first graph during gluing.
-/
def rootLabel (H : KRootedGraph k) (v : H.V) (hv : v ∈ H.R) : Fin k :=
  H.label ⟨v, H.root_labeled hv⟩

theorem root_hasLabel (H : KRootedGraph k) {v : H.V} (hv : v ∈ H.R) :
    H.HasLabel v (H.rootLabel v hv) := by
  exact ⟨H.root_labeled hv, rfl⟩

/--
Labels identify at most one vertex.

This is the main reason the injectivity condition is part of `KRootedGraph`
itself rather than an extra hypothesis on gluing: whenever a boundary label of
the second graph occurs in the first graph, the matching vertex in the first
graph is automatically unique.
-/
theorem eq_of_hasLabel_eq {H : KRootedGraph k} {u v : H.V} {i : Fin k}
    (hu : H.HasLabel u i) (hv : H.HasLabel v i) : u = v := by
  rcases hu with ⟨hu_dom, hu_label⟩
  rcases hv with ⟨hv_dom, hv_label⟩
  exact congrArg Subtype.val (H.label_injective (hu_label.trans hv_label.symm))

/--
Compatibility of the rooted part of `B` with the part of `A` selected by the
same labels.

The lecture note requires the labelled graph induced by `B.R` to be
label-preservingly isomorphic to the induced labelled subgraph of `A` on the
matching labels.  Since labels are injective, it is enough here to say that
whenever the matching vertices in `A` exist, adjacency between root vertices of
`B` is exactly adjacency between their matched vertices in `A`.
-/
def LabelCompatibleOnRoots (A B : KRootedGraph k) : Prop :=
  ∀ {u v : B.V} (hu : u ∈ B.R) (hv : v ∈ B.R)
      {uA vA : A.V},
    A.HasLabel uA (B.rootLabel u hu) ->
    A.HasLabel vA (B.rootLabel v hv) ->
    (B.G.Adj u v ↔ A.G.Adj uA vA)

/--
The precondition for the partial gluing operation `A ⊕ B`.

The first conjunct says every boundary vertex of `B` has a same-labelled
partner in `A`.  The second conjunct says that these partners preserve the
induced graph structure on the boundary.  Separating this precondition from
`IsGluing` lets later statements talk either about definedness of gluing or
about a particular glued result.
-/
def Gluable (A B : KRootedGraph k) : Prop :=
  (∀ v : B.V, ∀ hv : v ∈ B.R, ∃ u : A.V, A.HasLabel u (B.rootLabel v hv)) ∧
    A.LabelCompatibleOnRoots B

/--
Concrete witness data that `C` is a gluing result of `A` and `B`.

The maps `left` and `right` represent the quotient maps from the disjoint union
of vertices of `A` and `B` into the glued graph.  We use maps instead of
defining the quotient immediately because the quotient construction and the
resulting simple graph can be added later without changing theorem statements
that only need the predicate `IsGluing`.
-/
structure GluingData (A B C : KRootedGraph k) where
  /-- The left inclusion/quotient map from `A` into the glued graph. -/
  left : A.V -> C.V
  /-- The right inclusion/quotient map from `B` into the glued graph. -/
  right : B.V -> C.V
  /-- Gluing is only meaningful when the boundary of `B` matches inside `A`. -/
  gluable : A.Gluable B
  /-- Vertices from `A` remain distinct in the glued graph. -/
  left_injective : Function.Injective left
  /-- Vertices from `B` remain distinct in the glued graph. -/
  right_injective : Function.Injective right
  /-- Every vertex of the result comes from one of the two input graphs. -/
  vertex_cover : ∀ x : C.V, (∃ u : A.V, left u = x) ∨ (∃ v : B.V, right v = x)
  /--
  The only identifications between the two sides are the intended boundary
  identifications: a vertex of `B` is identified with a vertex of `A` exactly
  when it is in `B.R` and the two vertices have the same label.
  -/
  identified_iff :
    ∀ (u : A.V) (v : B.V),
      left u = right v ↔ ∃ hv : v ∈ B.R, A.HasLabel u (B.rootLabel v hv)
  /--
  The root of the glued graph is inherited from the first graph, as in the
  lecture note.
  -/
  root_eq : C.R = left '' A.R
  /--
  The remaining labels of the glued graph are inherited from the first graph.
  Labels on the right graph are used only to decide boundary identifications.
  -/
  labelDom_eq : C.labelDom = left '' A.labelDom
  /-- The inherited labels agree with the labels of the first graph. -/
  label_left : ∀ u : A.labelDom, C.HasLabel (left u.1) (A.label u)
  /-- Edges from the first graph appear in the glued graph. -/
  left_adj : ∀ {u v : A.V}, A.G.Adj u v -> C.G.Adj (left u) (left v)
  /-- Edges from the second graph appear in the glued graph. -/
  right_adj : ∀ {u v : B.V}, B.G.Adj u v -> C.G.Adj (right u) (right v)
  /--
  Conversely, every edge of the glued graph comes from one of the two input
  graphs.  This prevents `C` from containing extra edges not created by gluing.
  -/
  adj_cases : ∀ {x y : C.V}, C.G.Adj x y ->
    (∃ u v : A.V, A.G.Adj u v ∧ left u = x ∧ left v = y) ∨
      (∃ u v : B.V, B.G.Adj u v ∧ right u = x ∧ right v = y)

/--
Predicate-level gluing relation.

Using `Nonempty` hides the concrete maps in theorem statements while preserving
the option to recover them in proofs.  This is the usual Lean pattern for a
partial construction whose result is better described by a relation first.
-/
def IsGluing (A B C : KRootedGraph k) : Prop :=
  Nonempty (GluingData A B C)

theorem IsGluing.gluable {A B C : KRootedGraph k} (h : IsGluing A B C) :
    A.Gluable B := by
  rcases h with ⟨data⟩
  exact data.gluable

end KRootedGraph
