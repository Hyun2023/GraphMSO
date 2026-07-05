import GraphMSO.Decomp.tree_decomp
import GraphMSO.language.tau_graph

/-!
This file keeps the rooted-graph side of the Courcelle construction separate
from tree decompositions.

The gluing operation from the lecture note is partial: two rooted graphs can be
glued only when the second boundary can be matched, by labels, inside the first
graph.  Rather than defining a partial function immediately, we separate the
formalization into three layers.

* `Gluable A B` records the precondition saying that `A ⊕ B` is defined.
* `GluingData A B C` is explicit witness data saying that `C` is obtained by
  gluing the disjoint sum of `A` and `B` along the labelled root vertices of
  `B`.
* `IsGluing A B C := Nonempty (GluingData A B C)` is the proposition-level
  predicate used in theorem statements.
* `MultiGluingData A B C` is the corresponding witness for gluing a family
  `B : ι -> KRootedGraph P k` onto one distinguished left graph `A`.

This keeps theorem statements proof-irrelevant while still allowing later
proofs to unpack the concrete maps into the glued graph when needed.
-/

/-- A `k`-rooted `τ_P`-graph: a `τ_P`-structure (`KRootedPGraph P`) together with a
root/boundary set and a partial injective labeling whose domain contains the
root. -/
structure KRootedGraph (P : Type*) (k : ℕ) extends τPGraph P where
  R : Set V
  labelDom : Set V
  label : labelDom -> Fin k
  root_labeled : R ⊆ labelDom
  label_injective : Function.Injective label

namespace KRootedGraph

variable {P : Type*} {k : ℕ}

/--
`HasLabel H v i` means that the partial labeling of `H` is defined at `v`
and gives the label `i`.

This wrapper is useful because the labeling function has domain
`H.labelDom`, so using it directly constantly exposes subtype membership
proofs.  Most gluing conditions only care that a vertex has a certain label,
not which proof was used to view the vertex as an element of `labelDom`.
-/
def HasLabel (H : KRootedGraph P k) (v : H.V) (i : Fin k) : Prop :=
  ∃ hv : v ∈ H.labelDom, H.label ⟨v, hv⟩ = i

/--
The label of a root vertex.

The definition of a rooted graph requires `R ⊆ labelDom`, so root vertices
have a total labeling even though labels are partial on the ambient vertex set.
This is the label used when matching the boundary of the second graph into the
first graph during gluing.
-/
def rootLabel (H : KRootedGraph P k) (v : H.V) (hv : v ∈ H.R) : Fin k :=
  H.label ⟨v, H.root_labeled hv⟩

theorem root_hasLabel (H : KRootedGraph P k) {v : H.V} (hv : v ∈ H.R) :
    H.HasLabel v (H.rootLabel v hv) := by
  exact ⟨H.root_labeled hv, rfl⟩

/--
Labels identify at most one vertex.

This is the main reason the injectivity condition is part of `KRootedGraph`
itself rather than an extra hypothesis on gluing: whenever a boundary label of
the second graph occurs in the first graph, the matching vertex in the first
graph is automatically unique.
-/
theorem eq_of_hasLabel_eq {H : KRootedGraph P k} {u v : H.V} {i : Fin k}
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
def LabelCompatibleOnRoots (A B : KRootedGraph P k) : Prop :=
  (∀ {u v : B.V} (hu : u ∈ B.R) (hv : v ∈ B.R)
      {uA vA : A.V},
    A.HasLabel uA (B.rootLabel u hu) ->
    A.HasLabel vA (B.rootLabel v hv) ->
    (B.G.Adj u v ↔ A.G.Adj uA vA)) ∧
  (∀ {u : B.V} (hu : u ∈ B.R) {uA : A.V},
    A.HasLabel uA (B.rootLabel u hu) ->
    ∀ p : P, (B.pred p u ↔ A.pred p uA))

/--
The precondition for the partial gluing operation `A ⊕ B`.

The first conjunct says every boundary vertex of `B` has a same-labelled
partner in `A`.  The second conjunct says that these partners preserve the
induced graph structure on the boundary.  Separating this precondition from
`IsGluing` lets later statements talk either about definedness of gluing or
about a particular glued result.
-/
def Gluable (A B : KRootedGraph P k) : Prop :=
  (∀ v : B.V, ∀ hv : v ∈ B.R, ∃ u : A.V, A.HasLabel u (B.rootLabel v hv)) ∧
    A.LabelCompatibleOnRoots B

/--
The equivalence relation on representatives in the disjoint sum of the input
vertex types.

Left representatives are identified only with themselves, right representatives
are identified only with themselves, and a left representative is identified
with a right representative exactly when the right vertex is in the root of
`B` and has the same label as the left vertex in `A`.
-/
def GluingRel (A B : KRootedGraph P k) :
    A.V ⊕ B.V -> A.V ⊕ B.V -> Prop
  | .inl u, .inl u' => u = u'
  | .inr v, .inr v' => v = v'
  | .inl u, .inr v => ∃ hv : v ∈ B.R, A.HasLabel u (B.rootLabel v hv)
  | .inr v, .inl u => ∃ hv : v ∈ B.R, A.HasLabel u (B.rootLabel v hv)

/--
Concrete witness data that `C` is a gluing result of `A` and `B`.

The map `repr` sends representatives in the disjoint sum of vertices of `A`
and `B` to vertices of the glued graph.  Its fibers are exactly `GluingRel`,
so this records the quotient-style specification without defining a canonical
quotient construction.
-/
structure GluingData (A B C : KRootedGraph P k) where
  /-- The quotient map from disjoint-sum representatives into the glued graph. -/
  repr : A.V ⊕ B.V -> C.V
  /-- Gluing is only meaningful when the boundary of `B` matches inside `A`. -/
  gluable : A.Gluable B
  /-- Every vertex of the result comes from one of the two input graphs. -/
  repr_surjective : Function.Surjective repr
  /--
  The fibers of `repr` are exactly the intended gluing identifications.
  -/
  repr_eq_iff :
    ∀ x y : A.V ⊕ B.V, repr x = repr y ↔ GluingRel A B x y
  /--
  The root of the glued graph is inherited from the first graph, as in the
  lecture note.
  -/
  root_eq : C.R = repr '' (Sum.inl '' A.R)
  /--
  The remaining labels of the glued graph are inherited from the first graph.
  Labels on the right graph are used only to decide boundary identifications.
  -/
  labelDom_eq : C.labelDom = repr '' (Sum.inl '' A.labelDom)
  /-- The inherited labels agree with the labels of the first graph. -/
  label_left : ∀ u : A.labelDom, C.HasLabel (repr (.inl u.1)) (A.label u)
  /-- Edges from the first graph appear in the glued graph. -/
  left_adj : ∀ {u v : A.V}, A.G.Adj u v -> C.G.Adj (repr (.inl u)) (repr (.inl v))
  /-- Edges from the second graph appear in the glued graph. -/
  right_adj : ∀ {u v : B.V}, B.G.Adj u v -> C.G.Adj (repr (.inr u)) (repr (.inr v))
  /--
  Conversely, every edge of the glued graph comes from one of the two input
  graphs.  This prevents `C` from containing extra edges not created by gluing.
  -/
  adj_cases : ∀ {x y : C.V}, C.G.Adj x y ->
    (∃ u v : A.V, A.G.Adj u v ∧ repr (.inl u) = x ∧ repr (.inl v) = y) ∨
      (∃ u v : B.V, B.G.Adj u v ∧ repr (.inr u) = x ∧ repr (.inr v) = y)
  /-- Unary predicates of the first graph are inherited by the glued graph. -/
  left_pred : ∀ (p : P) (u : A.V), C.pred p (repr (.inl u)) ↔ A.pred p u
  /-- Unary predicates of the second graph are inherited by the glued graph. -/
  right_pred : ∀ (p : P) (v : B.V), C.pred p (repr (.inr v)) ↔ B.pred p v

namespace GluingData

variable {A B C : KRootedGraph P k}

/-- The induced map from the left input into the glued graph. -/
def left (data : GluingData A B C) : A.V -> C.V :=
  fun u => data.repr (.inl u)

/-- The induced map from the right input into the glued graph. -/
def right (data : GluingData A B C) : B.V -> C.V :=
  fun v => data.repr (.inr v)

theorem left_injective (data : GluingData A B C) :
    Function.Injective data.left := by
  intro u v huv
  exact (data.repr_eq_iff (.inl u) (.inl v)).mp huv

theorem right_injective (data : GluingData A B C) :
    Function.Injective data.right := by
  intro u v huv
  exact (data.repr_eq_iff (.inr u) (.inr v)).mp huv

theorem vertex_cover (data : GluingData A B C) (x : C.V) :
    (∃ u : A.V, data.left u = x) ∨ (∃ v : B.V, data.right v = x) := by
  rcases data.repr_surjective x with ⟨rep, hrep⟩
  cases rep with
  | inl u =>
      exact Or.inl ⟨u, hrep⟩
  | inr v =>
      exact Or.inr ⟨v, hrep⟩

theorem identified_iff (data : GluingData A B C) (u : A.V) (v : B.V) :
    data.left u = data.right v ↔
      ∃ hv : v ∈ B.R, A.HasLabel u (B.rootLabel v hv) :=
  data.repr_eq_iff (.inl u) (.inr v)

end GluingData

/--
Predicate-level gluing relation.

Using `Nonempty` hides the concrete maps in theorem statements while preserving
the option to recover them in proofs.  This is the usual Lean pattern for a
partial construction whose result is better described by a relation first.
-/
def IsGluing (A B C : KRootedGraph P k) : Prop :=
  Nonempty (GluingData A B C)

theorem IsGluing.gluable {A B C : KRootedGraph P k} (h : IsGluing A B C) :
    A.Gluable B := by
  rcases h with ⟨data⟩
  exact data.gluable

/-! ## Indexed gluing

The cone-gluing lemma in the Courcelle notes glues one node graph with all cone
graphs of its children.  The child set is finite in the intended applications,
often `Fin d`, but the specification below does not need finiteness: it records
the quotient-style result of gluing an arbitrary indexed family of right-hand
pieces onto one distinguished left-hand piece.

Only roots of the right-hand pieces are identified, and every such root must
match a labelled vertex of the left-hand graph.  The root set and all surviving
labels of the result are inherited from the left-hand graph, exactly as in the
binary operation above.
-/

/-- Representatives before gluing a family of right-hand pieces onto `A`. -/
abbrev MultiRep {ι : Type*} (A : KRootedGraph P k) (B : ι -> KRootedGraph P k) :=
  A.V ⊕ (Σ i : ι, (B i).V)

/--
The precondition for gluing every member of the indexed family `B` onto `A`.

Each piece is matched directly against the distinguished left graph.  This is
the shape used by cone gluing: child cones are glued along their adhesions into
the parent node graph, not sequentially into each other.
-/
def MultiGluable {ι : Type*} (A : KRootedGraph P k) (B : ι -> KRootedGraph P k) :
    Prop :=
  ∀ i : ι, A.Gluable (B i)

/--
The intended quotient relation for indexed gluing.

Two left representatives agree exactly when they are the same vertex of `A`.
A left representative is identified with a right representative exactly when the
right representative is in its root and has a matching label in `A`.  Two right
representatives agree either when they are literally the same tagged
representative, or when they are both rooted representatives matched to the same
left vertex.
-/
def MultiGluingRel {ι : Type*} (A : KRootedGraph P k) (B : ι -> KRootedGraph P k) :
    MultiRep A B -> MultiRep A B -> Prop
  | .inl u, .inl u' => u = u'
  | .inl u, .inr x =>
      ∃ hx : x.2 ∈ (B x.1).R, A.HasLabel u ((B x.1).rootLabel x.2 hx)
  | .inr x, .inl u =>
      ∃ hx : x.2 ∈ (B x.1).R, A.HasLabel u ((B x.1).rootLabel x.2 hx)
  | .inr x, .inr y =>
      x = y ∨
        ∃ (hx : x.2 ∈ (B x.1).R) (hy : y.2 ∈ (B y.1).R) (u : A.V),
          A.HasLabel u ((B x.1).rootLabel x.2 hx) ∧
            A.HasLabel u ((B y.1).rootLabel y.2 hy)

/--
Concrete witness data that `C` is obtained by gluing the indexed family `B` onto
the distinguished graph `A`.

This is the multi-piece analogue of `GluingData`.  It remains relational rather
than constructing a canonical quotient, which keeps later cone-gluing statements
free to use the concrete cone graph as the chosen result.
-/
structure MultiGluingData {ι : Type*}
    (A : KRootedGraph P k) (B : ι -> KRootedGraph P k) (C : KRootedGraph P k) where
  /-- The quotient map from all representatives into the glued graph. -/
  repr : MultiRep A B -> C.V
  /-- Every indexed piece is gluable onto the distinguished left graph. -/
  gluable : MultiGluable A B
  /-- Every vertex of the result comes from the left graph or one indexed piece. -/
  repr_surjective : Function.Surjective repr
  /-- The fibers of `repr` are exactly the intended indexed gluing relation. -/
  repr_eq_iff :
    ∀ x y : MultiRep A B, repr x = repr y ↔ MultiGluingRel A B x y
  /-- The root of the glued graph is inherited from the left graph. -/
  root_eq : C.R =
    repr '' ((fun u : A.V => (Sum.inl u : MultiRep A B)) '' A.R)
  /-- The surviving label domain is inherited from the left graph. -/
  labelDom_eq : C.labelDom =
    repr '' ((fun u : A.V => (Sum.inl u : MultiRep A B)) '' A.labelDom)
  /-- The inherited labels agree with the labels of the left graph. -/
  label_left : ∀ u : A.labelDom, C.HasLabel (repr (.inl u.1)) (A.label u)
  /-- Edges from the left graph appear in the glued graph. -/
  left_adj : ∀ {u v : A.V}, A.G.Adj u v -> C.G.Adj (repr (.inl u)) (repr (.inl v))
  /-- Edges from every indexed piece appear in the glued graph. -/
  piece_adj :
    ∀ (i : ι) {u v : (B i).V},
      (B i).G.Adj u v -> C.G.Adj (repr (.inr ⟨i, u⟩)) (repr (.inr ⟨i, v⟩))
  /--
  Conversely, every edge of the glued graph comes from the left graph or one
  indexed piece.
  -/
  adj_cases : ∀ {x y : C.V}, C.G.Adj x y ->
    (∃ u v : A.V, A.G.Adj u v ∧ repr (.inl u) = x ∧ repr (.inl v) = y) ∨
      (∃ i : ι, ∃ u v : (B i).V,
        (B i).G.Adj u v ∧ repr (.inr ⟨i, u⟩) = x ∧ repr (.inr ⟨i, v⟩) = y)
  /-- Unary predicates of the left graph are inherited by the glued graph. -/
  left_pred : ∀ (p : P) (u : A.V), C.pred p (repr (.inl u)) ↔ A.pred p u
  /-- Unary predicates of every indexed piece are inherited by the glued graph. -/
  piece_pred :
    ∀ (p : P) (i : ι) (v : (B i).V),
      C.pred p (repr (.inr ⟨i, v⟩)) ↔ (B i).pred p v

namespace MultiGluingData

variable {ι : Type*} {A : KRootedGraph P k} {B : ι -> KRootedGraph P k}
variable {C : KRootedGraph P k}

/-- The induced map from the distinguished left input into the glued graph. -/
def left (data : MultiGluingData A B C) : A.V -> C.V :=
  fun u => data.repr (.inl u)

/-- The induced map from an indexed right input into the glued graph. -/
def piece (data : MultiGluingData A B C) (i : ι) : (B i).V -> C.V :=
  fun v => data.repr (.inr ⟨i, v⟩)

theorem left_injective (data : MultiGluingData A B C) :
    Function.Injective data.left := by
  intro u v huv
  exact (data.repr_eq_iff (.inl u) (.inl v)).mp huv

theorem vertex_cover (data : MultiGluingData A B C) (x : C.V) :
    (∃ u : A.V, data.left u = x) ∨
      (∃ i : ι, ∃ v : (B i).V, data.piece i v = x) := by
  rcases data.repr_surjective x with ⟨rep, hrep⟩
  cases rep with
  | inl u =>
      exact Or.inl ⟨u, hrep⟩
  | inr y =>
      exact Or.inr ⟨y.1, y.2, hrep⟩

theorem identified_iff (data : MultiGluingData A B C) (u : A.V)
    (i : ι) (v : (B i).V) :
    data.left u = data.piece i v ↔
      ∃ hv : v ∈ (B i).R, A.HasLabel u ((B i).rootLabel v hv) :=
  data.repr_eq_iff (.inl u) (.inr ⟨i, v⟩)

theorem piece_identified_iff (data : MultiGluingData A B C)
    (i j : ι) (u : (B i).V) (v : (B j).V) :
    data.piece i u = data.piece j v ↔
      (⟨i, u⟩ : Σ i : ι, (B i).V) = ⟨j, v⟩ ∨
        ∃ (hu : u ∈ (B i).R) (hv : v ∈ (B j).R) (a : A.V),
          A.HasLabel a ((B i).rootLabel u hu) ∧
            A.HasLabel a ((B j).rootLabel v hv) :=
  data.repr_eq_iff (.inr ⟨i, u⟩) (.inr ⟨j, v⟩)

end MultiGluingData

/-- Predicate-level indexed gluing relation. -/
def IsMultiGluing {ι : Type*}
    (A : KRootedGraph P k) (B : ι -> KRootedGraph P k) (C : KRootedGraph P k) :
    Prop :=
  Nonempty (MultiGluingData A B C)

theorem IsMultiGluing.gluable {ι : Type*} {A : KRootedGraph P k}
    {B : ι -> KRootedGraph P k} {C : KRootedGraph P k}
    (h : IsMultiGluing A B C) :
    MultiGluable A B := by
  rcases h with ⟨data⟩
  exact data.gluable

end KRootedGraph
