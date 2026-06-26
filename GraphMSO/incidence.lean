import Mathlib.Combinatorics.SimpleGraph.Basic
import GraphMSO.Decomp.KRootedPGraph

inductive IncidenceVertex.{u} {V : Type u} (G : SimpleGraph V) : Type u where
  |fromV (v : V)
  |fromEdge (e : G.edgeSet)

def IncidenceGraph.{u} {V : Type u} (G : SimpleGraph V) : SimpleGraph (IncidenceVertex G) where
  Adj := fun u v =>
    match u, v with
    | IncidenceVertex.fromV x, IncidenceVertex.fromEdge e => x ∈ (e : Sym2 V)
    | IncidenceVertex.fromEdge e, IncidenceVertex.fromV x => x ∈ (e : Sym2 V)
    | _, _ => False
  symm := by
    intro u v h
    cases u <;> cases v <;> simp_all
  loopless := by
    intro u h
    cases u <;> simp_all

@[simp]
theorem IncidenceGraph_adj_fromV_fromEdge.{u} {V : Type u} (G : SimpleGraph V)
    (v : V) (e : G.edgeSet) :
    (IncidenceGraph G).Adj (IncidenceVertex.fromV v) (IncidenceVertex.fromEdge e) ↔
      v ∈ (e : Sym2 V) :=
  Iff.rfl

@[simp]
theorem IncidenceGraph_adj_fromEdge_fromV.{u} {V : Type u} (G : SimpleGraph V)
    (e : G.edgeSet) (v : V) :
    (IncidenceGraph G).Adj (IncidenceVertex.fromEdge e) (IncidenceVertex.fromV v) ↔
      v ∈ (e : Sym2 V) :=
  Iff.rfl

@[simp]
theorem IncidenceGraph_not_adj_fromV_fromV.{u} {V : Type u} (G : SimpleGraph V)
    (u v : V) :
    ¬ (IncidenceGraph G).Adj (IncidenceVertex.fromV u) (IncidenceVertex.fromV v) :=
  id

@[simp]
theorem IncidenceGraph_not_adj_fromEdge_fromEdge.{u} {V : Type u} (G : SimpleGraph V)
    (e f : G.edgeSet) :
    ¬ (IncidenceGraph G).Adj (IncidenceVertex.fromEdge e) (IncidenceVertex.fromEdge f) :=
  id

/-!
### The two sorts of the coloured incidence structure

The coloured incidence structure is `IncidenceGraph G` together with the two
unary predicates below, forming the vocabulary `τ_I = {adj, Vert, EdgeObj}`. The
sort of an incidence vertex is read off its constructor, never reconstructed
from adjacency; this is what makes the `MSO₂`-to-incidence reduction
truth-preserving (an isolated original vertex and an edge object are
indistinguishable by adjacency alone).
-/

/-- `Vert` predicate of the coloured incidence structure: holds of the incidence
vertices coming from an original vertex of `G`. -/
def IncidenceVertex.IsVertex.{u} {V : Type u} {G : SimpleGraph V} :
    IncidenceVertex G → Prop
  | .fromV _ => True
  | .fromEdge _ => False

/-- `EdgeObj` predicate of the coloured incidence structure: holds of the incidence
vertices coming from an edge of `G`. -/
def IncidenceVertex.IsEdgeObj.{u} {V : Type u} {G : SimpleGraph V} :
    IncidenceVertex G → Prop
  | .fromV _ => False
  | .fromEdge _ => True

@[simp]
theorem IncidenceVertex.isVertex_fromV.{u} {V : Type u} {G : SimpleGraph V} (v : V) :
    (IncidenceVertex.fromV v : IncidenceVertex G).IsVertex :=
  trivial

@[simp]
theorem IncidenceVertex.not_isVertex_fromEdge.{u} {V : Type u} {G : SimpleGraph V}
    (e : G.edgeSet) :
    ¬ (IncidenceVertex.fromEdge e : IncidenceVertex G).IsVertex :=
  id

@[simp]
theorem IncidenceVertex.isEdgeObj_fromEdge.{u} {V : Type u} {G : SimpleGraph V}
    (e : G.edgeSet) :
    (IncidenceVertex.fromEdge e : IncidenceVertex G).IsEdgeObj :=
  trivial

@[simp]
theorem IncidenceVertex.not_isEdgeObj_fromV.{u} {V : Type u} {G : SimpleGraph V} (v : V) :
    ¬ (IncidenceVertex.fromV v : IncidenceVertex G).IsEdgeObj :=
  id

/-- The two sorts are complementary: every incidence vertex is a `Vert` exactly
when it is not an `EdgeObj`. -/
theorem IncidenceVertex.isVertex_iff_not_isEdgeObj.{u} {V : Type u} {G : SimpleGraph V}
    (x : IncidenceVertex G) : x.IsVertex ↔ ¬ x.IsEdgeObj := by
  cases x <;> simp

/-- The two sorts are exhaustive: every incidence vertex is a `Vert` or an
`EdgeObj`. -/
theorem IncidenceVertex.isVertex_or_isEdgeObj.{u} {V : Type u} {G : SimpleGraph V}
    (x : IncidenceVertex G) : x.IsVertex ∨ x.IsEdgeObj := by
  cases x <;> simp

/-- The vertex sort is decidable: it is read off the constructor. -/
instance IncidenceVertex.instDecidableIsVertex.{u} {V : Type u} {G : SimpleGraph V}
    (x : IncidenceVertex G) : Decidable x.IsVertex :=
  match x with
  | .fromV _ => .isTrue trivial
  | .fromEdge _ => .isFalse id

/-- The edge-object sort is decidable: it is read off the constructor. -/
instance IncidenceVertex.instDecidableIsEdgeObj.{u} {V : Type u} {G : SimpleGraph V}
    (x : IncidenceVertex G) : Decidable x.IsEdgeObj :=
  match x with
  | .fromV _ => .isFalse id
  | .fromEdge _ => .isTrue trivial

/-!
### The coloured incidence structure as a `KRootedPGraph`

The coloured incidence structure `Î(G)` over the vocabulary
`τ_I = {adj, Vert, EdgeObj}` is the instance of `KRootedPGraph` whose adjacency is
the incidence graph and whose two unary predicates are `IsVertex` and `IsEdgeObj`.
-/

/-- The two predicate symbols of the coloured incidence vocabulary `τ_I`. -/
inductive IncSort
  | vert
  | edgeObj
  deriving DecidableEq

/-- The coloured incidence structure of `G` as a `KRootedPGraph` over `IncSort`. -/
def colouredIncidence.{u} {V : Type u} (G : SimpleGraph V) : KRootedPGraph IncSort where
  V := IncidenceVertex G
  G := IncidenceGraph G
  pred := fun
    | .vert => (·.IsVertex)
    | .edgeObj => (·.IsEdgeObj)
