import Mathlib

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
