import GraphMSO.incidence
import GraphMSO.pendant
import GraphMSO.Decomp.edgeBound

/-!
# Tree decompositions of the incidence graph

From a tree-decomposition of `G` of width at most `omega`, this file builds a
tree-decomposition of `IncidenceGraph G` of width at most `max omega 2`, the
construction used by the MSO₂ corollary of the lecture note.

The decomposition tree is the pendant extension of the original tree: every
edge of `G` contributes one new leaf, attached below a node whose bag covers
the edge (`attachNode`).  The old bags keep their vertices (as `fromV`
incidence vertices); the leaf bag of an edge holds the edge object and its
two endpoints.
-/

/-- `fromV` is injective: distinct vertices give distinct incidence
vertices. -/
theorem IncidenceVertex.fromV_injective {V : Type*} {G : SimpleGraph V} :
    Function.Injective (IncidenceVertex.fromV : V → IncidenceVertex G) :=
  fun _ _ h => by injection h

/-- Incidence vertices are the sum of the original vertices and the edge
objects. -/
def IncidenceVertex.sumEquiv {V : Type*} {G : SimpleGraph V} :
    (V ⊕ G.edgeSet) ≃ IncidenceVertex G where
  toFun := fun x =>
    match x with
    | .inl v => .fromV v
    | .inr e => .fromEdge e
  invFun := fun x =>
    match x with
    | .fromV v => .inl v
    | .fromEdge e => .inr e
  left_inv := by rintro (v | e) <;> rfl
  right_inv := by rintro (v | e) <;> rfl

/-- The incidence vertices of a finite graph form a finite type. -/
noncomputable instance IncidenceVertex.instFintype {V : Type*} [Fintype V]
    {G : SimpleGraph V} : Fintype (IncidenceVertex G) := by
  classical
  exact Fintype.ofEquiv (V ⊕ G.edgeSet) IncidenceVertex.sumEquiv

namespace TreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Every edge has a node whose bag contains both endpoints, stated over the
edge as a `Sym2` element. -/
theorem exists_forall_mem_bag (D : TreeDecomposition G) (e : G.edgeSet) :
    ∃ t : D.Node, ∀ v ∈ (e : Sym2 V), v ∈ D.bag t := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨t, hut, hvt⟩ := D.EdgeCoverage he
      refine ⟨t, ?_⟩
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hut
      · exact hvt

/-- A chosen node whose bag covers the edge `e`. -/
noncomputable def attachNode (D : TreeDecomposition G) (e : G.edgeSet) :
    D.Node :=
  (D.exists_forall_mem_bag e).choose

theorem mem_bag_attachNode (D : TreeDecomposition G) (e : G.edgeSet) :
    ∀ v ∈ (e : Sym2 V), v ∈ D.bag (D.attachNode e) :=
  (D.exists_forall_mem_bag e).choose_spec

/-- The bags of the incidence decomposition: old nodes keep their vertices,
and the leaf of an edge holds the edge object and its endpoints. -/
def incidenceBag (D : TreeDecomposition G) :
    D.Node ⊕ G.edgeSet → Set (IncidenceVertex G)
  | .inl t => IncidenceVertex.fromV '' D.bag t
  | .inr e =>
      insert (IncidenceVertex.fromEdge e)
        (IncidenceVertex.fromV '' {v | v ∈ (e : Sym2 V)})

section IncidenceBag

variable (D : TreeDecomposition G)

@[simp] theorem fromV_mem_incidenceBag_inl_iff (t : D.Node) (v : V) :
    IncidenceVertex.fromV v ∈ D.incidenceBag (Sum.inl t) ↔ v ∈ D.bag t := by
  simp [incidenceBag, IncidenceVertex.fromV_injective.eq_iff]

@[simp] theorem fromEdge_not_mem_incidenceBag_inl (t : D.Node) (e : G.edgeSet) :
    IncidenceVertex.fromEdge e ∉ D.incidenceBag (Sum.inl t) := by
  simp [incidenceBag]

@[simp] theorem fromV_mem_incidenceBag_inr_iff (e : G.edgeSet) (v : V) :
    IncidenceVertex.fromV v ∈ D.incidenceBag (Sum.inr e) ↔ v ∈ (e : Sym2 V) := by
  simp [incidenceBag, IncidenceVertex.fromV_injective.eq_iff]

@[simp] theorem fromEdge_mem_incidenceBag_inr_iff (e e' : G.edgeSet) :
    IncidenceVertex.fromEdge e' ∈ D.incidenceBag (Sum.inr e) ↔ e' = e := by
  simp [incidenceBag]

end IncidenceBag

/-- The occurrence set of a vertex incidence-vertex consists of the old
occurrence nodes and the leaves of its incident edges. -/
theorem mem_incidenceBag_fromV_iff (D : TreeDecomposition G) (v : V) :
    ∀ n : D.Node ⊕ G.edgeSet,
      IncidenceVertex.fromV v ∈ D.incidenceBag n ↔
        (∃ t : D.Node, n = Sum.inl t ∧ v ∈ D.bag t) ∨
        (∃ e : G.edgeSet, n = Sum.inr e ∧ v ∈ (e : Sym2 V)) := by
  rintro (t | e)
  · simp
  · simp

/-- The connectivity axiom for the incidence decomposition. -/
theorem incidence_connectivity (D : TreeDecomposition G)
    (x : IncidenceVertex G) :
    ((SimpleGraph.pendantExtension D.T D.attachNode).induce
      {n | x ∈ D.incidenceBag n}).Preconnected := by
  cases x with
  | fromEdge e₀ =>
      -- the occurrence set of an edge object is the singleton of its leaf
      have hocc : ∀ n : D.Node ⊕ G.edgeSet,
          IncidenceVertex.fromEdge e₀ ∈ D.incidenceBag n → n = Sum.inr e₀ := by
        rintro (t | e) hn
        · exact absurd hn (D.fromEdge_not_mem_incidenceBag_inl t e₀)
        · rw [D.fromEdge_mem_incidenceBag_inr_iff] at hn
          rw [hn]
      intro a b
      have hab : a = b := Subtype.ext ((hocc a.1 a.2).trans (hocc b.1 b.2).symm)
      rw [hab]
  | fromV v =>
      -- reduce every occurrence node to an old occurrence node, then use the
      -- connectivity of the original decomposition
      set occ : Set (D.Node ⊕ G.edgeSet) :=
        {n | IncidenceVertex.fromV v ∈ D.incidenceBag n} with hocc_def
      have hmem_inl : ∀ t : D.Node, Sum.inl t ∈ occ ↔ v ∈ D.bag t := by
        intro t
        simp [hocc_def]
      have hmem_inr : ∀ e : G.edgeSet, Sum.inr e ∈ occ ↔ v ∈ (e : Sym2 V) := by
        intro e
        simp [hocc_def]
      -- the inclusion of the original occurrence subtree
      let f : D.T.induce (D.bagsOf v) →g
          (SimpleGraph.pendantExtension D.T D.attachNode).induce occ :=
        { toFun := fun t => ⟨Sum.inl t.1, (hmem_inl t.1).2 t.2⟩
          map_rel' := fun h => h }
      have hreach_inl : ∀ (t s : D.Node) (ht : v ∈ D.bag t) (hs : v ∈ D.bag s),
          ((SimpleGraph.pendantExtension D.T D.attachNode).induce occ).Reachable
            ⟨Sum.inl t, (hmem_inl t).2 ht⟩ ⟨Sum.inl s, (hmem_inl s).2 hs⟩ := by
        intro t s ht hs
        exact (D.Connectivity v ⟨t, ht⟩ ⟨s, hs⟩).map f
      -- every occurrence node reaches an old occurrence node
      have key : ∀ (n : D.Node ⊕ G.edgeSet) (hn : n ∈ occ),
          ∃ (t : D.Node) (ht : v ∈ D.bag t),
            ((SimpleGraph.pendantExtension D.T D.attachNode).induce occ).Reachable
              ⟨n, hn⟩ ⟨Sum.inl t, (hmem_inl t).2 ht⟩ := by
        rintro (t | e) hn
        · exact ⟨t, (hmem_inl t).1 hn, SimpleGraph.Reachable.refl _⟩
        · have hv_e : v ∈ (e : Sym2 V) := (hmem_inr e).1 hn
          have hv_attach : v ∈ D.bag (D.attachNode e) :=
            D.mem_bag_attachNode e v hv_e
          refine ⟨D.attachNode e, hv_attach, SimpleGraph.Adj.reachable ?_⟩
          show (SimpleGraph.pendantExtension D.T D.attachNode).Adj
            (Sum.inr e) (Sum.inl (D.attachNode e))
          simp
      intro a b
      obtain ⟨ta, hta, hra⟩ := key a.1 a.2
      obtain ⟨tb, htb, hrb⟩ := key b.1 b.2
      exact (hra.trans (hreach_inl ta tb hta htb)).trans hrb.symm

/-- The tree-decomposition of the incidence graph induced by a
tree-decomposition of `G`: one pendant leaf per edge, holding the edge object
and its endpoints. -/
noncomputable def incidenceDecomposition (D : TreeDecomposition G) :
    TreeDecomposition (IncidenceGraph G) where
  Node := D.Node ⊕ G.edgeSet
  nodeFintype := by classical exact inferInstance
  T := SimpleGraph.pendantExtension D.T D.attachNode
  T_istree := SimpleGraph.PendantExtension.isTree D.T D.attachNode D.T_istree
  node2bag := D.incidenceBag
  VertexCoverage := by
    rintro (v | e)
    · obtain ⟨t, ht⟩ := D.VertexCoverage v
      exact ⟨Sum.inl t, (D.fromV_mem_incidenceBag_inl_iff t v).2 ht⟩
    · exact ⟨Sum.inr e, (D.fromEdge_mem_incidenceBag_inr_iff e e).2 rfl⟩
  EdgeCoverage := by
    rintro (u | e) (w | f) hadj
    · exact hadj.elim
    · exact ⟨Sum.inr f, (D.fromV_mem_incidenceBag_inr_iff f u).2 hadj,
        (D.fromEdge_mem_incidenceBag_inr_iff f f).2 rfl⟩
    · exact ⟨Sum.inr e, (D.fromEdge_mem_incidenceBag_inr_iff e e).2 rfl,
        (D.fromV_mem_incidenceBag_inr_iff e w).2 hadj⟩
    · exact hadj.elim
  Connectivity := D.incidence_connectivity

@[simp] theorem incidenceDecomposition_bag (D : TreeDecomposition G)
    (n : D.Node ⊕ G.edgeSet) :
    D.incidenceDecomposition.bag n = D.incidenceBag n :=
  rfl

omit [Fintype V] in
/-- The endpoints of an edge form a set of at most two vertices. -/
theorem ncard_setOf_mem_sym2_le (e : G.edgeSet) :
    ({v | v ∈ (e : Sym2 V)} : Set V).ncard ≤ 2 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ u v =>
      have hset : ({w | w ∈ (s(u, v) : Sym2 V)} : Set V) = {u, v} := by
        ext w
        simp [Sym2.mem_iff]
      rw [hset]
      exact (Set.ncard_insert_le u {v}).trans (by simp)

/-- The incidence decomposition has width at most `max omega 2`. -/
theorem incidenceDecomposition_hasWidth (D : TreeDecomposition G) (omega : ℕ)
    (hwidth : D.HasWidth omega) :
    D.incidenceDecomposition.HasWidth (max omega 2) := by
  rintro (t | e)
  · rw [incidenceDecomposition_bag]
    show (IncidenceVertex.fromV '' D.bag t).ncard ≤ max omega 2 + 1
    rw [Set.ncard_image_of_injective _ IncidenceVertex.fromV_injective]
    exact (hwidth t).trans (by omega)
  · rw [incidenceDecomposition_bag]
    show (insert (IncidenceVertex.fromEdge e)
      (IncidenceVertex.fromV '' {v | v ∈ (e : Sym2 V)})).ncard ≤ max omega 2 + 1
    have himg :
        ((IncidenceVertex.fromV '' {v | v ∈ (e : Sym2 V)}) :
          Set (IncidenceVertex G)).ncard ≤ 2 := by
      rw [Set.ncard_image_of_injective _ IncidenceVertex.fromV_injective]
      exact ncard_setOf_mem_sym2_le e
    have hinsert := Set.ncard_insert_le (IncidenceVertex.fromEdge e)
      (IncidenceVertex.fromV '' {v | v ∈ (e : Sym2 V)})
    omega

/-- The size of the incidence structure: original vertices plus edge
objects. -/
theorem card_incidenceVertex (G : SimpleGraph V) :
    Nat.card (IncidenceVertex G) = Fintype.card V + G.edgeSet.ncard := by
  rw [Nat.card_congr IncidenceVertex.sumEquiv.symm, Nat.card_sum,
    Nat.card_eq_fintype_card]
  rfl

/-- The incidence-structure size bound: for a graph of width at most `omega`,
the incidence structure has at most `(omega + 1) * |V|` elements. -/
theorem card_incidenceVertex_le_of_hasWidth (D : TreeDecomposition G)
    (omega : ℕ) (hwidth : D.HasWidth omega) :
    Nat.card (IncidenceVertex G) ≤ (omega + 1) * Fintype.card V := by
  rw [card_incidenceVertex]
  calc Fintype.card V + G.edgeSet.ncard
      ≤ Fintype.card V + omega * Fintype.card V :=
        Nat.add_le_add_left (D.edgeSet_ncard_le_of_hasWidth omega hwidth) _
    _ = (omega + 1) * Fintype.card V := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

end TreeDecomposition
