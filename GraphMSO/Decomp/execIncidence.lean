import Mathlib.Combinatorics.SimpleGraph.Dart
import GraphMSO.incidence
import GraphMSO.Decomp.execDecomp

/-!
# Executable incidence decompositions

`DecompTree.incidenceTree` extends a rose-tree decomposition of `G` to one of
the incidence graph `IncidenceGraph G`: every bag is mapped through
`IncidenceVertex.fromV`, and every edge of `G` receives one pendant leaf
`{fromV u, fromV v, fromEdge e}` attached at the first node (root-first,
left-to-right) whose bag contains both endpoints.

Edges are enumerated as `SimpleGraph.Dart`s built from ordered pairs of the
tree's vertex list, so no choice on `Sym2` or `Finset` is needed; the walk
threads the pending dart list, which guarantees that each edge object occurs
in exactly one pendant leaf.  This is the computable counterpart of
`TreeDecomposition.incidenceDecomposition`.
-/

universe u

namespace DecompTree

variable {V : Type u}

/-! ## Vertex enumeration -/

/-- All bag members of the rose tree, with repetitions. -/
def vertexList : DecompTree V → List V
  | node bag children =>
      bag ++ (children.attach.map fun c => vertexList c.1).flatten
decreasing_by
  have := List.sizeOf_lt_of_mem c.2
  simp
  omega

theorem vertexList_node (bag : List V) (children : List (DecompTree V)) :
    (node bag children).vertexList = bag ++ (children.map vertexList).flatten := by
  simp only [vertexList]
  congr 2
  exact List.attach_map_val (l := children) (f := vertexList)

theorem mem_vertexList_of_occurs (t : DecompTree V) {v : V} :
    t.Occurs v → v ∈ t.vertexList := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      intro h
      rw [vertexList_node]
      rcases occurs_node_iff.1 h with hv | ⟨c, hc, hocc⟩
      · exact List.mem_append_left _ hv
      · refine List.mem_append_right _ ?_
        rw [List.mem_flatten]
        exact ⟨c.vertexList, List.mem_map_of_mem hc, ih c hc hocc⟩

/-! ## Edge enumeration by darts -/

/-- All ordered pairs `(a, b)` with `a` strictly before `b` in the list. -/
def offDiagPairs : List V → List (V × V)
  | [] => []
  | v :: rest => rest.map (Prod.mk v) ++ offDiagPairs rest

theorem mem_of_mem_offDiagPairs {l : List V} {p : V × V}
    (hp : p ∈ offDiagPairs l) : p.1 ∈ l ∧ p.2 ∈ l := by
  induction l with
  | nil => simp [offDiagPairs] at hp
  | cons v rest ih =>
      simp only [offDiagPairs, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
        exact ⟨by simp, by simp [hb]⟩
      · obtain ⟨h1, h2⟩ := ih hp
        exact ⟨by simp [h1], by simp [h2]⟩

theorem exists_mem_offDiagPairs {l : List V} {a b : V}
    (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    (a, b) ∈ offDiagPairs l ∨ (b, a) ∈ offDiagPairs l := by
  induction l with
  | nil => simp at ha
  | cons v rest ih =>
      simp only [offDiagPairs, List.mem_append]
      rcases List.mem_cons.mp ha with ha' | ha'
      · rcases List.mem_cons.mp hb with hb' | hb'
        · exact absurd (ha'.trans hb'.symm) hab
        · subst ha'
          exact Or.inl (Or.inl (List.mem_map_of_mem hb'))
      · rcases List.mem_cons.mp hb with hb' | hb'
        · subst hb'
          exact Or.inr (Or.inl (List.mem_map_of_mem ha'))
        · rcases ih ha' hb' with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inr h)

/-- Distinct positions of `offDiagPairs` of a duplicate-free list carry
distinct unordered pairs. -/
theorem offDiagPairs_pairwise_sym2_ne {l : List V} (h : l.Nodup) :
    (offDiagPairs l).Pairwise (fun p q => s(p.1, p.2) ≠ s(q.1, q.2)) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons v rest ih =>
      rw [List.nodup_cons] at h
      simp only [offDiagPairs]
      rw [List.pairwise_append]
      refine ⟨?_, ih h.2, ?_⟩
      · refine List.Pairwise.map (Prod.mk v) ?_ h.2
        intro a b hab heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨_, h2⟩ | ⟨h1, h2⟩
        · exact hab h2
        · exact hab (h2.trans h1)
      · intro p hp q hq
        obtain ⟨b, _hb, rfl⟩ := List.mem_map.mp hp
        have hq' := mem_of_mem_offDiagPairs hq
        intro heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h.1 ((show v = q.1 from h1) ▸ hq'.1)
        · exact h.1 ((show v = q.2 from h1) ▸ hq'.2)

variable [DecidableEq V] (G : SimpleGraph V)

/-- The darts of `G` between vertices of `l`, one per unordered edge. -/
def dartsOfList [DecidableRel G.Adj] (l : List V) : List G.Dart :=
  (offDiagPairs l.dedup).filterMap fun p =>
    if h : G.Adj p.1 p.2 then some ⟨p, h⟩ else none

theorem exists_dart_of_adj [DecidableRel G.Adj] {l : List V} {u v : V}
    (h : G.Adj u v) (hu : u ∈ l) (hv : v ∈ l) :
    ∃ d ∈ dartsOfList G l, d.edge = s(u, v) := by
  rcases exists_mem_offDiagPairs (List.mem_dedup.mpr hu)
    (List.mem_dedup.mpr hv) h.ne with hp | hp
  · refine ⟨⟨(u, v), h⟩, ?_, rfl⟩
    rw [dartsOfList, List.mem_filterMap]
    exact ⟨(u, v), hp, by simp [h]⟩
  · refine ⟨⟨(v, u), h.symm⟩, ?_, ?_⟩
    · rw [dartsOfList, List.mem_filterMap]
      exact ⟨(v, u), hp, by simp [h.symm]⟩
    · show s(v, u) = s(u, v)
      exact Sym2.eq_swap

omit [DecidableEq V] in
theorem filterMap_dart_pairwise [DecidableRel G.Adj] (ps : List (V × V))
    (hpw : ps.Pairwise fun p q => s(p.1, p.2) ≠ s(q.1, q.2)) :
    (ps.filterMap fun p =>
      if h : G.Adj p.1 p.2 then some (⟨p, h⟩ : G.Dart) else none).Pairwise
      (fun d₁ d₂ => d₁.edge ≠ d₂.edge) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [List.pairwise_cons] at hpw
      rw [List.filterMap_cons]
      by_cases h : G.Adj p.1 p.2
      · simp only [dif_pos h]
        rw [List.pairwise_cons]
        constructor
        · intro d hd
          rw [List.mem_filterMap] at hd
          obtain ⟨q, hq, hdq⟩ := hd
          by_cases hadj : G.Adj q.1 q.2
          · rw [dif_pos hadj, Option.some_inj] at hdq
            subst hdq
            exact hpw.1 q hq
          · rw [dif_neg hadj] at hdq
            exact absurd hdq (by simp)
        · exact ih hpw.2
      · simp only [dif_neg h]
        exact ih hpw.2

/-- Distinct listed darts carry distinct edges. -/
theorem dartsOfList_pairwise_edge_ne [DecidableRel G.Adj] {l : List V} :
    (dartsOfList G l).Pairwise (fun d₁ d₂ => d₁.edge ≠ d₂.edge) :=
  filterMap_dart_pairwise G _ (offDiagPairs_pairwise_sym2_ne l.nodup_dedup)

/-! ## The incidence rose tree -/

/-- Both dart endpoints lie in the bag. -/
def dartMem (bag : List V) (d : G.Dart) : Bool :=
  decide (d.toProd.1 ∈ bag) && decide (d.toProd.2 ∈ bag)

@[simp] theorem dartMem_eq_true_iff {bag : List V} {d : G.Dart} :
    dartMem G bag d = true ↔ d.toProd.1 ∈ bag ∧ d.toProd.2 ∈ bag := by
  simp [dartMem]

/-- The pendant leaf attached for one edge dart. -/
def edgeLeaf (d : G.Dart) : DecompTree (IncidenceVertex G) :=
  node [.fromV d.toProd.1, .fromV d.toProd.2, .fromEdge ⟨d.edge, d.edge_mem⟩] []

omit [DecidableEq V] in
theorem edgeLeaf_occurs_iff {d : G.Dart} {x : IncidenceVertex G} :
    (edgeLeaf G d).Occurs x ↔
      x = .fromV d.toProd.1 ∨ x = .fromV d.toProd.2 ∨
        x = .fromEdge ⟨d.edge, d.edge_mem⟩ := by
  rw [edgeLeaf, occurs_node_nil_iff]
  simp

mutual

/-- Extend one decomposition subtree to the incidence graph: the bag is
mapped through `fromV`, and every pending dart whose endpoints both lie in
the bag is attached here as a pendant leaf; the remaining darts are threaded
through the children left to right. -/
def incidenceAux : DecompTree V → List G.Dart →
    DecompTree (IncidenceVertex G) × List G.Dart
  | node bag children => fun pending =>
      match incidenceForest children (pending.filter fun d => !dartMem G bag d) with
      | (children', pending') =>
          (node (bag.map .fromV)
            (children' ++ (pending.filter (dartMem G bag)).map (edgeLeaf G)),
            pending')

/-- Process a forest left to right, threading the pending darts. -/
def incidenceForest : List (DecompTree V) → List G.Dart →
    List (DecompTree (IncidenceVertex G)) × List G.Dart
  | [], pending => ([], pending)
  | c :: cs, pending =>
      match incidenceAux c pending with
      | (c', pending₁) =>
          match incidenceForest cs pending₁ with
          | (cs', pending₂) => (c' :: cs', pending₂)

end

theorem incidenceAux_node (bag : List V) (children : List (DecompTree V))
    (pending : List G.Dart) :
    incidenceAux G (node bag children) pending =
      (node (bag.map .fromV)
        ((incidenceForest G children
            (pending.filter fun d => !dartMem G bag d)).1 ++
          (pending.filter (dartMem G bag)).map (edgeLeaf G)),
        (incidenceForest G children
          (pending.filter fun d => !dartMem G bag d)).2) := by
  simp only [incidenceAux]

theorem incidenceForest_nil (pending : List G.Dart) :
    incidenceForest G [] pending = ([], pending) := by
  simp only [incidenceForest]

theorem incidenceForest_cons (c : DecompTree V) (cs : List (DecompTree V))
    (pending : List G.Dart) :
    incidenceForest G (c :: cs) pending =
      ((incidenceAux G c pending).1 ::
        (incidenceForest G cs (incidenceAux G c pending).2).1,
        (incidenceForest G cs (incidenceAux G c pending).2).2) := by
  simp only [incidenceForest]

/-! ## Threading facts -/

theorem incidenceForest_sublist (cs : List (DecompTree V)) :
    (∀ c ∈ cs, ∀ p : List G.Dart, ((incidenceAux G c p).2).Sublist p) →
      ∀ p : List G.Dart, ((incidenceForest G cs p).2).Sublist p := by
  induction cs with
  | nil => intro _ p; rw [incidenceForest_nil]
  | cons c cs ih =>
      intro hspec p
      rw [incidenceForest_cons]
      exact (ih (fun c' hc' => hspec c' (by simp [hc'])) _).trans
        (hspec c (by simp) p)

theorem incidenceAux_sublist (t : DecompTree V) :
    ∀ p : List G.Dart, ((incidenceAux G t p).2).Sublist p := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      intro p
      rw [incidenceAux_node]
      exact (incidenceForest_sublist G children ih _).trans List.filter_sublist

/-- The root bag is the mapped input root bag. -/
theorem incidenceAux_rootBag (t : DecompTree V) (p : List G.Dart) :
    (incidenceAux G t p).1.rootBag = t.rootBag.map IncidenceVertex.fromV := by
  cases t with
  | node bag children => rw [incidenceAux_node, rootBag_node, rootBag_node]

/-! ## Vertex occurrences -/

theorem incidenceForest_occurs_fromV (cs : List (DecompTree V)) :
    (∀ c ∈ cs, ∀ (p : List G.Dart) (v : V),
      ((incidenceAux G c p).1.Occurs (.fromV v) ↔ c.Occurs v)) →
      ∀ (p : List G.Dart) (v : V),
        ((∃ c' ∈ (incidenceForest G cs p).1, c'.Occurs (.fromV v)) ↔
          ∃ c ∈ cs, c.Occurs v) := by
  induction cs with
  | nil =>
      intro _ p v
      rw [incidenceForest_nil]
      simp
  | cons c cs ih =>
      intro hspec p v
      rw [incidenceForest_cons]
      constructor
      · rintro ⟨c', hc', hocc⟩
        rcases List.mem_cons.mp hc' with rfl | hc'
        · exact ⟨c, by simp, (hspec c (by simp) p v).1 hocc⟩
        · obtain ⟨c₂, hc₂, h₂⟩ :=
            (ih (fun c₀ hc₀ => hspec c₀ (by simp [hc₀])) _ v).1 ⟨c', hc', hocc⟩
          exact ⟨c₂, by simp [hc₂], h₂⟩
      · rintro ⟨c₂, hc₂, hocc⟩
        rcases List.mem_cons.mp hc₂ with rfl | hc₂
        · exact ⟨_, by simp, (hspec c₂ (by simp) p v).2 hocc⟩
        · obtain ⟨c', hc', h'⟩ :=
            (ih (fun c₀ hc₀ => hspec c₀ (by simp [hc₀]))
              (incidenceAux G c p).2 v).2 ⟨c₂, hc₂, hocc⟩
          exact ⟨c', by simp [hc'], h'⟩

theorem incidenceAux_occurs_fromV (t : DecompTree V) :
    ∀ (p : List G.Dart) (v : V),
      ((incidenceAux G t p).1.Occurs (.fromV v) ↔ t.Occurs v) := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      intro p v
      rw [incidenceAux_node, occurs_node_iff, occurs_node_iff]
      constructor
      · rintro (hv | ⟨x, hx, hocc⟩)
        · obtain ⟨w, hw, heq⟩ := List.mem_map.mp hv
          rw [IncidenceVertex.fromV.injEq] at heq
          exact Or.inl (heq ▸ hw)
        · rcases List.mem_append.mp hx with hx | hx
          · exact Or.inr ((incidenceForest_occurs_fromV G children ih _ v).1
              ⟨x, hx, hocc⟩)
          · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
            rw [edgeLeaf_occurs_iff] at hocc
            have hdm := (List.mem_filter.mp hd).2
            rw [dartMem_eq_true_iff] at hdm
            rcases hocc with h1 | h1 | h1
            · rw [IncidenceVertex.fromV.injEq] at h1
              exact Or.inl (h1 ▸ hdm.1)
            · rw [IncidenceVertex.fromV.injEq] at h1
              exact Or.inl (h1 ▸ hdm.2)
            · exact absurd h1 (by simp)
      · rintro (hv | hocc)
        · exact Or.inl (List.mem_map_of_mem hv)
        · obtain ⟨c', hc', h'⟩ :=
            (incidenceForest_occurs_fromV G children ih _ v).2 hocc
          exact Or.inr ⟨c', List.mem_append_left _ hc', h'⟩

/-- Correspondence between transformed children and input children. -/
theorem incidenceForest_correspondence (cs : List (DecompTree V)) :
    ∀ p : List G.Dart, ∀ c' ∈ (incidenceForest G cs p).1, ∃ c ∈ cs,
      (∀ v, c'.Occurs (.fromV v) → c.Occurs v) ∧
      c'.rootBag = c.rootBag.map IncidenceVertex.fromV := by
  induction cs with
  | nil =>
      intro p
      rw [incidenceForest_nil]
      simp
  | cons c cs ih =>
      intro p c' hc'
      rw [incidenceForest_cons] at hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact ⟨c, by simp,
          fun v h => (incidenceAux_occurs_fromV G c p v).1 h,
          incidenceAux_rootBag G c p⟩
      · obtain ⟨c₂, hc₂, h₂⟩ := ih _ c' hc'
        exact ⟨c₂, by simp [hc₂], h₂⟩

/-! ## Edge-object occurrences -/

theorem incidenceForest_occurs_fromEdge (cs : List (DecompTree V)) :
    (∀ c ∈ cs, ∀ (p : List G.Dart) (e : G.edgeSet),
      (incidenceAux G c p).1.Occurs (.fromEdge e) →
        ∃ d ∈ p, d.edge = (e : Sym2 V) ∧ d ∉ (incidenceAux G c p).2) →
      ∀ (p : List G.Dart) (e : G.edgeSet),
        (∃ c' ∈ (incidenceForest G cs p).1, c'.Occurs (.fromEdge e)) →
          ∃ d ∈ p, d.edge = (e : Sym2 V) ∧ d ∉ (incidenceForest G cs p).2 := by
  induction cs with
  | nil =>
      intro _ p e h
      rw [incidenceForest_nil] at h
      simp at h
  | cons c cs ih =>
      intro hspec p e h
      rw [incidenceForest_cons] at h ⊢
      obtain ⟨c', hc', hocc⟩ := h
      rcases List.mem_cons.mp hc' with rfl | hc'
      · obtain ⟨d, hd, hedge, hout⟩ := hspec c (by simp) p e hocc
        refine ⟨d, hd, hedge, fun hmem => hout ?_⟩
        exact (incidenceForest_sublist G cs
          (fun c₂ _hc₂ p₂ => incidenceAux_sublist G c₂ p₂) _).subset hmem
      · obtain ⟨d, hd, hedge, hout⟩ :=
          ih (fun c₂ hc₂ => hspec c₂ (by simp [hc₂])) _ e ⟨c', hc', hocc⟩
        exact ⟨d, (incidenceAux_sublist G c p).subset hd, hedge, hout⟩

theorem incidenceAux_occurs_fromEdge (t : DecompTree V) :
    ∀ (p : List G.Dart) (e : G.edgeSet),
      (incidenceAux G t p).1.Occurs (.fromEdge e) →
        ∃ d ∈ p, d.edge = (e : Sym2 V) ∧ d ∉ (incidenceAux G t p).2 := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      intro p e hocc
      rw [incidenceAux_node] at hocc ⊢
      rcases occurs_node_iff.1 hocc with hv | ⟨x, hx, hocc'⟩
      · obtain ⟨w, _, heq⟩ := List.mem_map.mp hv
        exact absurd heq (by simp)
      · rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨d, hd, hedge, hout⟩ :=
            incidenceForest_occurs_fromEdge G children ih _ e ⟨x, hx, hocc'⟩
          exact ⟨d, List.filter_sublist.subset hd, hedge, hout⟩
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
          rw [edgeLeaf_occurs_iff] at hocc'
          rcases hocc' with h1 | h1 | h1
          · exact absurd h1 (by simp)
          · exact absurd h1 (by simp)
          · rw [IncidenceVertex.fromEdge.injEq] at h1
            have hd' := List.mem_filter.mp hd
            refine ⟨d, hd'.1, (congrArg Subtype.val h1).symm, ?_⟩
            intro hmem
            have hsub := (incidenceForest_sublist G children
              (fun c _hc p₂ => incidenceAux_sublist G c p₂)
              (p.filter fun d => !dartMem G bag d)).subset hmem
            have hneg := (List.mem_filter.mp hsub).2
            rw [hd'.2] at hneg
            simp at hneg

/-! ## Attachment completeness -/

theorem incidenceForest_consumed (cs : List (DecompTree V)) :
    (∀ c ∈ cs, ∀ (p : List G.Dart) (d : G.Dart), d ∈ p →
      (∃ L, c.HasBag L ∧ d.toProd.1 ∈ L ∧ d.toProd.2 ∈ L) →
        d ∉ (incidenceAux G c p).2) →
      ∀ (p : List G.Dart) (d : G.Dart), d ∈ p →
        (∃ c ∈ cs, ∃ L, c.HasBag L ∧ d.toProd.1 ∈ L ∧ d.toProd.2 ∈ L) →
          d ∉ (incidenceForest G cs p).2 := by
  induction cs with
  | nil =>
      intro _ p d _ h
      simp at h
  | cons c cs ih =>
      rintro hspec p d hd ⟨c₀, hc₀, hbag⟩
      rw [incidenceForest_cons]
      by_cases hd₁ : d ∈ (incidenceAux G c p).2
      · rcases List.mem_cons.mp hc₀ with rfl | hc₀
        · exact absurd hd₁ (hspec c₀ (by simp) p d hd hbag)
        · exact ih (fun c₂ hc₂ => hspec c₂ (by simp [hc₂])) _ d hd₁
            ⟨c₀, hc₀, hbag⟩
      · intro hmem
        exact hd₁ ((incidenceForest_sublist G cs
          (fun c₂ _hc₂ p₂ => incidenceAux_sublist G c₂ p₂) _).subset hmem)

theorem incidenceAux_consumed (t : DecompTree V) :
    ∀ (p : List G.Dart) (d : G.Dart), d ∈ p →
      (∃ L, t.HasBag L ∧ d.toProd.1 ∈ L ∧ d.toProd.2 ∈ L) →
        d ∉ (incidenceAux G t p).2 := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      rintro p d hd ⟨L, hL, h1, h2⟩
      rw [incidenceAux_node]
      by_cases hdm : dartMem G bag d = true
      · intro hmem
        have hsub := (incidenceForest_sublist G children
          (fun c _hc p₂ => incidenceAux_sublist G c p₂)
          (p.filter fun d => !dartMem G bag d)).subset hmem
        have hneg := (List.mem_filter.mp hsub).2
        rw [hdm] at hneg
        simp at hneg
      · rcases hasBag_node_iff.1 hL with rfl | ⟨c, hc, hcL⟩
        · exact absurd ((dartMem_eq_true_iff G).2 ⟨h1, h2⟩) hdm
        · exact incidenceForest_consumed G children ih _ d
            (List.mem_filter.mpr ⟨hd, by simp [hdm]⟩) ⟨c, hc, L, hcL, h1, h2⟩

/-! ## Consumed darts produce pendant leaves -/

theorem incidenceForest_leaf_of_consumed (cs : List (DecompTree V)) :
    (∀ c ∈ cs, ∀ (p : List G.Dart) (d : G.Dart), d ∈ p →
      d ∉ (incidenceAux G c p).2 →
        (incidenceAux G c p).1.HasBag
          [.fromV d.toProd.1, .fromV d.toProd.2,
            .fromEdge ⟨d.edge, d.edge_mem⟩]) →
      ∀ (p : List G.Dart) (d : G.Dart), d ∈ p →
        d ∉ (incidenceForest G cs p).2 →
          ∃ c' ∈ (incidenceForest G cs p).1, c'.HasBag
            [.fromV d.toProd.1, .fromV d.toProd.2,
              .fromEdge ⟨d.edge, d.edge_mem⟩] := by
  induction cs with
  | nil =>
      intro _ p d hd hout
      rw [incidenceForest_nil] at hout
      exact absurd hd hout
  | cons c cs ih =>
      intro hspec p d hd hout
      rw [incidenceForest_cons] at hout ⊢
      by_cases hd₁ : d ∈ (incidenceAux G c p).2
      · obtain ⟨c', hc', hbag⟩ :=
          ih (fun c₂ hc₂ => hspec c₂ (by simp [hc₂])) _ d hd₁ hout
        exact ⟨c', by simp [hc'], hbag⟩
      · exact ⟨_, by simp, hspec c (by simp) p d hd hd₁⟩

theorem incidenceAux_leaf_of_consumed (t : DecompTree V) :
    ∀ (p : List G.Dart) (d : G.Dart), d ∈ p →
      d ∉ (incidenceAux G t p).2 →
        (incidenceAux G t p).1.HasBag
          [.fromV d.toProd.1, .fromV d.toProd.2,
            .fromEdge ⟨d.edge, d.edge_mem⟩] := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      intro p d hd hout
      rw [incidenceAux_node] at hout ⊢
      by_cases hdm : dartMem G bag d = true
      · have hmine : d ∈ p.filter (dartMem G bag) :=
          List.mem_filter.mpr ⟨hd, hdm⟩
        exact HasBag.child _
          (List.mem_append_right _ (List.mem_map_of_mem hmine))
          (HasBag.root _ _)
      · have hrest : d ∈ p.filter fun d => !dartMem G bag d :=
          List.mem_filter.mpr ⟨hd, by simp [hdm]⟩
        obtain ⟨c', hc', hbag⟩ :=
          incidenceForest_leaf_of_consumed G children ih _ d hrest hout
        exact HasBag.child _ (List.mem_append_left _ hc') hbag

/-! ## Width -/

theorem incidenceForest_hasWidth (cs : List (DecompTree V)) (omega : ℕ) :
    (∀ c ∈ cs, ∀ p : List G.Dart, c.HasWidth omega →
      (incidenceAux G c p).1.HasWidth (max omega 2)) →
      (∀ c ∈ cs, c.HasWidth omega) →
      ∀ p : List G.Dart, ∀ c' ∈ (incidenceForest G cs p).1,
        c'.HasWidth (max omega 2) := by
  induction cs with
  | nil =>
      intro _ _ p c' hc'
      rw [incidenceForest_nil] at hc'
      simp at hc'
  | cons c cs ih =>
      intro hspec hw p c' hc'
      rw [incidenceForest_cons] at hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hspec c (by simp) p (hw c (by simp))
      · exact ih (fun c₂ hc₂ => hspec c₂ (by simp [hc₂]))
          (fun c₂ hc₂ => hw c₂ (by simp [hc₂])) _ c' hc'

theorem incidenceAux_hasWidth (t : DecompTree V) (omega : ℕ) :
    ∀ p : List G.Dart, t.HasWidth omega →
      (incidenceAux G t p).1.HasWidth (max omega 2) := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      intro p hw L' hL'
      rw [incidenceAux_node] at hL'
      rcases hasBag_node_iff.1 hL' with rfl | ⟨x, hx, hxL⟩
      · calc (bag.map IncidenceVertex.fromV).toFinset.card
            ≤ bag.toFinset.card := by
              have himg : (bag.map IncidenceVertex.fromV).toFinset =
                  bag.toFinset.image
                    (IncidenceVertex.fromV : V → IncidenceVertex G) := by
                ext x
                simp
              rw [himg]
              exact Finset.card_image_le
          _ ≤ omega + 1 := hw bag (HasBag.root _ _)
          _ ≤ max omega 2 + 1 := by omega
      · rcases List.mem_append.mp hx with hx | hx
        · exact incidenceForest_hasWidth G children omega
            (fun c hc p₂ => ih c hc p₂) (fun c hc => hw.of_mem_children hc)
            _ x hx L' hxL
        · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
          rw [edgeLeaf] at hxL
          rcases hasBag_node_iff.1 hxL with rfl | ⟨c, hc, _⟩
          · have h3 := List.toFinset_card_le
              (l := [IncidenceVertex.fromV d.toProd.1,
                IncidenceVertex.fromV d.toProd.2,
                IncidenceVertex.fromEdge ⟨d.edge, d.edge_mem⟩])
            have hmax : 2 ≤ max omega 2 := Nat.le_max_right omega 2
            simp only [List.length_cons, List.length_nil] at h3
            omega
          · simp at hc

/-! ## Running intersection -/

/-- Pairwise sharing condition for the transformed children. -/
theorem incidenceForest_pairwise (bag : List V) (cs : List (DecompTree V)) :
    ∀ p : List G.Dart,
      p.Pairwise (fun d₁ d₂ => d₁.edge ≠ d₂.edge) →
      cs.Pairwise (fun c₁ c₂ => ∀ v, c₁.Occurs v → c₂.Occurs v → v ∈ bag) →
      (incidenceForest G cs p).1.Pairwise
        (fun a b => ∀ x, a.Occurs x → b.Occurs x →
          x ∈ bag.map IncidenceVertex.fromV) := by
  induction cs with
  | nil =>
      intro p _ _
      rw [incidenceForest_nil]
      exact List.Pairwise.nil
  | cons c cs ih =>
      intro p hpne hpair
      rw [List.pairwise_cons] at hpair
      rw [incidenceForest_cons, List.pairwise_cons]
      constructor
      · intro b hb x hocca hoccb
        cases x with
        | fromV v =>
            have hcv : c.Occurs v := (incidenceAux_occurs_fromV G c p v).1 hocca
            obtain ⟨c₂, hc₂, hcorr, _⟩ :=
              incidenceForest_correspondence G cs _ b hb
            exact List.mem_map_of_mem (hpair.1 c₂ hc₂ v hcv (hcorr v hoccb))
        | fromEdge e =>
            obtain ⟨d₁, hd₁, hedge₁, hout₁⟩ :=
              incidenceAux_occurs_fromEdge G c p e hocca
            obtain ⟨d₂, hd₂, hedge₂, _⟩ :=
              incidenceForest_occurs_fromEdge G cs
                (fun c₂ _hc₂ p₂ e₂ => incidenceAux_occurs_fromEdge G c₂ p₂ e₂)
                _ e ⟨b, hb, hoccb⟩
            have hd₂p : d₂ ∈ p := (incidenceAux_sublist G c p).subset hd₂
            have hne : d₁ ≠ d₂ := by
              rintro rfl
              exact hout₁ hd₂
            have hsym : Symmetric fun d₁ d₂ : G.Dart => d₁.edge ≠ d₂.edge :=
              fun _ _ h heq => h heq.symm
            have hforall := hpne.forall hsym
            exact absurd (hedge₁.trans hedge₂.symm) (hforall hd₁ hd₂p hne)
      · exact ih _ (hpne.sublist (incidenceAux_sublist G c p)) hpair.2

theorem incidenceForest_runningIntersection (cs : List (DecompTree V)) :
    (∀ c ∈ cs, ∀ p : List G.Dart,
      p.Pairwise (fun d₁ d₂ => d₁.edge ≠ d₂.edge) → c.RunningIntersection →
        (incidenceAux G c p).1.RunningIntersection) →
      ∀ p : List G.Dart, p.Pairwise (fun d₁ d₂ => d₁.edge ≠ d₂.edge) →
        (∀ c ∈ cs, c.RunningIntersection) →
        ∀ c' ∈ (incidenceForest G cs p).1, c'.RunningIntersection := by
  induction cs with
  | nil =>
      intro _ p _ _ c' hc'
      rw [incidenceForest_nil] at hc'
      simp at hc'
  | cons c cs ih =>
      intro hspec p hpne hri c' hc'
      rw [incidenceForest_cons] at hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hspec c (by simp) p hpne (hri c (by simp))
      · exact ih (fun c₂ hc₂ => hspec c₂ (by simp [hc₂])) _
          (hpne.sublist (incidenceAux_sublist G c p))
          (fun c₂ hc₂ => hri c₂ (by simp [hc₂])) c' hc'

theorem incidenceAux_runningIntersection (t : DecompTree V) :
    ∀ p : List G.Dart, p.Pairwise (fun d₁ d₂ => d₁.edge ≠ d₂.edge) →
      t.RunningIntersection → (incidenceAux G t p).1.RunningIntersection := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      rintro p hpne ⟨hdown, hpair, hchildren⟩
      rw [incidenceAux_node]
      have hpneRest : (p.filter fun d => !dartMem G bag d).Pairwise
          (fun d₁ d₂ => d₁.edge ≠ d₂.edge) :=
        hpne.sublist List.filter_sublist
      refine RunningIntersection.node ?_ ?_ ?_
      · intro c'' hc'' x hx hocc
        rcases List.mem_append.mp hc'' with hc'' | hc''
        · obtain ⟨c, hc, hcorr, hroot⟩ :=
            incidenceForest_correspondence G children _ c'' hc''
          obtain ⟨v, hvbag, rfl⟩ := List.mem_map.mp hx
          rw [hroot]
          exact List.mem_map_of_mem (hdown c hc v hvbag (hcorr v hocc))
        · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc''
          rw [edgeLeaf_occurs_iff] at hocc
          rw [edgeLeaf, rootBag_node]
          rcases hocc with rfl | rfl | rfl
          · simp
          · simp
          · simp
      · rw [List.pairwise_append]
        refine ⟨incidenceForest_pairwise G bag children _ hpneRest hpair,
          ?_, ?_⟩
        · have hminePairwise : (p.filter (dartMem G bag)).Pairwise
              (fun d₁ d₂ => d₁.edge ≠ d₂.edge ∧
                dartMem G bag d₁ = true ∧ dartMem G bag d₂ = true) :=
            (hpne.sublist List.filter_sublist).imp_of_mem
              (fun ha hb h =>
                ⟨h, (List.mem_filter.mp ha).2, (List.mem_filter.mp hb).2⟩)
          refine hminePairwise.map (edgeLeaf G) ?_
          rintro d₁ d₂ ⟨hne, hm₁, _hm₂⟩ x hocc₁ hocc₂
          rw [edgeLeaf_occurs_iff] at hocc₁ hocc₂
          rw [dartMem_eq_true_iff] at hm₁
          rcases hocc₁ with rfl | rfl | rfl
          · exact List.mem_map_of_mem hm₁.1
          · exact List.mem_map_of_mem hm₁.2
          · rcases hocc₂ with h2 | h2 | h2
            · exact absurd h2 (by simp)
            · exact absurd h2 (by simp)
            · simp only [IncidenceVertex.fromEdge.injEq, Subtype.mk.injEq] at h2
              exact absurd h2 hne
        · intro a ha b hb x hocca hoccb
          obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hb
          have hdmTrue : dartMem G bag d' = true := (List.mem_filter.mp hd').2
          have hdm' := hdmTrue
          rw [dartMem_eq_true_iff] at hdm'
          rw [edgeLeaf_occurs_iff] at hoccb
          rcases hoccb with rfl | rfl | rfl
          · exact List.mem_map_of_mem hdm'.1
          · exact List.mem_map_of_mem hdm'.2
          · obtain ⟨d, hd, hedge, _⟩ :=
              incidenceForest_occurs_fromEdge G children
                (fun c _hc p₂ e₂ => incidenceAux_occurs_fromEdge G c p₂ e₂)
                _ _ ⟨a, ha, hocca⟩
            have hdrest := List.mem_filter.mp hd
            have hdmFalse : dartMem G bag d = false := by
              simpa using hdrest.2
            have hne : d ≠ d' := by
              rintro rfl
              rw [hdmTrue] at hdmFalse
              simp at hdmFalse
            have hsym : Symmetric fun d₁ d₂ : G.Dart => d₁.edge ≠ d₂.edge :=
              fun _ _ h heq => h heq.symm
            have hforall := hpne.forall hsym
            have hd'p : d' ∈ p := List.filter_sublist.subset hd'
            exact absurd hedge (hforall hdrest.1 hd'p hne)
      · intro c'' hc''
        rcases List.mem_append.mp hc'' with hc'' | hc''
        · exact incidenceForest_runningIntersection G children ih _ hpneRest
            hchildren c'' hc''
        · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc''
          rw [edgeLeaf]
          exact runningIntersection_node_nil _

/-! ## Size accounting -/

theorem incidenceForest_size (cs : List (DecompTree V)) :
    (∀ c ∈ cs, ∀ p : List G.Dart,
      (incidenceAux G c p).1.size + (incidenceAux G c p).2.length =
        c.size + p.length) →
      ∀ p : List G.Dart,
        ((incidenceForest G cs p).1.map size).sum +
          (incidenceForest G cs p).2.length =
          (cs.map size).sum + p.length := by
  induction cs with
  | nil =>
      intro _ p
      rw [incidenceForest_nil]
      simp
  | cons c cs ih =>
      intro hspec p
      rw [incidenceForest_cons]
      simp only [List.map_cons, List.sum_cons]
      have h1 := hspec c (by simp) p
      have h2 := ih (fun c₂ hc₂ => hspec c₂ (by simp [hc₂]))
        (incidenceAux G c p).2
      omega

/-- Each consumed dart contributes exactly one pendant leaf: node counts plus
pending lengths are conserved by the walk. -/
theorem incidenceAux_size (t : DecompTree V) :
    ∀ p : List G.Dart,
      (incidenceAux G t p).1.size + (incidenceAux G t p).2.length =
        t.size + p.length := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      intro p
      rw [incidenceAux_node]
      dsimp only
      have hsplit :=
        (List.length_eq_length_filter_add (l := p) (dartMem G bag)).symm
      have hforest := incidenceForest_size G children ih
        (p.filter fun d => !dartMem G bag d)
      have hleaves : ∀ ds : List G.Dart,
          ((ds.map (edgeLeaf G)).map size).sum = ds.length := by
        intro ds
        induction ds with
        | nil => simp
        | cons d ds ihd =>
            simp only [List.map_cons, List.sum_cons, ihd, List.length_cons]
            rw [edgeLeaf, size_node]
            simp only [List.map_nil, List.sum_nil, Nat.add_zero]
            omega
      have hmine := hleaves (p.filter (dartMem G bag))
      rw [size_node, size_node, List.map_append, List.sum_append]
      omega

/-! ## The executable incidence decomposition -/

/-- The executable incidence extension of a rose-tree decomposition. -/
def incidenceTree [DecidableRel G.Adj] (t : DecompTree V) :
    DecompTree (IncidenceVertex G) :=
  (incidenceAux G t (dartsOfList G t.vertexList)).1

theorem incidenceTree_hasWidth [DecidableRel G.Adj] (t : DecompTree V)
    (omega : ℕ) (hw : t.HasWidth omega) :
    (incidenceTree G t).HasWidth (max omega 2) :=
  incidenceAux_hasWidth G t omega _ hw

/-- The incidence extension adds at most one pendant leaf per enumerated
dart. -/
theorem incidenceTree_size_le [DecidableRel G.Adj] (t : DecompTree V) :
    (incidenceTree G t).size ≤
      t.size + (dartsOfList G t.vertexList).length := by
  have h := incidenceAux_size G t (dartsOfList G t.vertexList)
  unfold incidenceTree
  omega

/-- Every graph edge receives a pendant leaf bag in the incidence
extension of a valid decomposition. -/
theorem incidenceTree_exists_leaf [DecidableRel G.Adj] {t : DecompTree V}
    (h : t.IsDecompFor G) (e : G.edgeSet) :
    ∃ d : G.Dart, d.edge = (e : Sym2 V) ∧
      (incidenceTree G t).HasBag
        [.fromV d.toProd.1, .fromV d.toProd.2,
          .fromEdge ⟨d.edge, d.edge_mem⟩] := by
  obtain ⟨eSym, he⟩ := e
  revert he
  induction eSym using Sym2.ind with
  | _ u v =>
      intro he
      have hadj : G.Adj u v := (G.mem_edgeSet).1 he
      obtain ⟨L, hL, hu, hv⟩ := h.edgeCoverage hadj
      have hu' := mem_vertexList_of_occurs t ⟨L, hL, hu⟩
      have hv' := mem_vertexList_of_occurs t ⟨L, hL, hv⟩
      obtain ⟨d, hd, hedge⟩ := exists_dart_of_adj G hadj hu' hv'
      have hbagd : d.toProd.1 ∈ L ∧ d.toProd.2 ∈ L := by
        have heq : s(d.toProd.1, d.toProd.2) = s(u, v) := hedge
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1 ▸ hu, h2 ▸ hv⟩
        · exact ⟨h1 ▸ hv, h2 ▸ hu⟩
      have hcons := incidenceAux_consumed G t _ d hd ⟨L, hL, hbagd.1, hbagd.2⟩
      exact ⟨d, hedge, incidenceAux_leaf_of_consumed G t _ d hd hcons⟩

/-- The incidence extension of a valid rose-tree decomposition of `G` is a
valid rose-tree decomposition of the incidence graph. -/
theorem incidenceTree_isDecompFor [DecidableRel G.Adj] {t : DecompTree V}
    (h : t.IsDecompFor G) :
    (incidenceTree G t).IsDecompFor (IncidenceGraph G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    cases x with
    | fromV v =>
        exact (incidenceAux_occurs_fromV G t _ v).2 (h.vertexCoverage v)
    | fromEdge e =>
        obtain ⟨d, hedge, hbag⟩ := incidenceTree_exists_leaf G h e
        refine ⟨_, hbag, ?_⟩
        have hee : (⟨d.edge, d.edge_mem⟩ : G.edgeSet) = e := Subtype.ext hedge
        simp [hee]
  · intro x y hadj
    cases x with
    | fromV v =>
        cases y with
        | fromV w =>
            exact absurd hadj (IncidenceGraph_not_adj_fromV_fromV G v w)
        | fromEdge e =>
            obtain ⟨d, hedge, hbag⟩ := incidenceTree_exists_leaf G h e
            have hv : v ∈ (e : Sym2 V) := hadj
            rw [← hedge] at hv
            have hv' : v = d.toProd.1 ∨ v = d.toProd.2 :=
              Sym2.mem_iff.1 hv
            have hee : (⟨d.edge, d.edge_mem⟩ : G.edgeSet) = e :=
              Subtype.ext hedge
            refine ⟨_, hbag, ?_, ?_⟩
            · rcases hv' with rfl | rfl
              · simp
              · simp
            · simp [hee]
    | fromEdge e =>
        cases y with
        | fromV v =>
            obtain ⟨d, hedge, hbag⟩ := incidenceTree_exists_leaf G h e
            have hv : v ∈ (e : Sym2 V) := hadj
            rw [← hedge] at hv
            have hv' : v = d.toProd.1 ∨ v = d.toProd.2 :=
              Sym2.mem_iff.1 hv
            have hee : (⟨d.edge, d.edge_mem⟩ : G.edgeSet) = e :=
              Subtype.ext hedge
            refine ⟨_, hbag, ?_, ?_⟩
            · simp [hee]
            · rcases hv' with rfl | rfl
              · simp
              · simp
        | fromEdge f =>
            exact absurd hadj (IncidenceGraph_not_adj_fromEdge_fromEdge G e f)
  · exact incidenceAux_runningIntersection G t _
      (dartsOfList_pairwise_edge_ne G) h.runningIntersection

end DecompTree
