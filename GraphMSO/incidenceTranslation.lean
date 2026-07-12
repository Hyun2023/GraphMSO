import GraphMSO.Semantics
import GraphMSO.language.semantics
import GraphMSO.Decomp.incidenceDecomp

/-!
# MSO₂ over a graph as MSO₁ over its coloured incidence structure

The Phase 4 reduction of the lecture note: an MSO₂ formula over a simple
graph is translated into a one-sorted MSO formula over the vocabulary
`τ_I = {adj, Vert, EdgeObj}`, interpreted in the coloured incidence
structure, and the translation preserves truth.

Variable management: the two-sorted variables of MSO₂ are merged into the
single namespaces of the target language by parity — vertex variables `x`
become `2 * x`, edge variables `e` become `2 * e + 1`, and likewise for set
variables.  Quantifiers are guarded by the sort predicates `Vert` and
`EdgeObj`; set quantifiers use the pointwise sort guards.  The MSO₂ atom
`edge x y` (adjacency of two vertices) is not part of `τ_I` and is expressed
by the existence of a common incident edge object together with `x ≠ y`; its
bound variable `2*x + 2*y + 1` is odd, hence distinct from `2*x` and `2*y`.
-/

namespace GraphMSO

/-- `fromEdge` is injective: distinct edge objects give distinct incidence
vertices. -/
theorem _root_.IncidenceVertex.fromEdge_injective {V : Type*} {G : SimpleGraph V} :
    Function.Injective
      (IncidenceVertex.fromEdge : G.edgeSet → IncidenceVertex G) :=
  fun _ _ h => by injection h

/-- An incidence vertex satisfying `Vert` is an original vertex. -/
theorem _root_.IncidenceVertex.isVertex_iff_exists {V : Type*} {G : SimpleGraph V}
    {z : IncidenceVertex G} :
    z.IsVertex ↔ ∃ v : V, z = .fromV v := by
  cases z <;> simp

/-- An incidence vertex satisfying `EdgeObj` is an edge object. -/
theorem _root_.IncidenceVertex.isEdgeObj_iff_exists {V : Type*} {G : SimpleGraph V}
    {z : IncidenceVertex G} :
    z.IsEdgeObj ↔ ∃ e : G.edgeSet, z = .fromEdge e := by
  cases z <;> simp

/-- The coloured incidence structure of `G` as a `τPGraph` over `IncSort`:
the incidence adjacency together with the two sort predicates. -/
def incidenceTauGraph {V : Type*} (G : SimpleGraph V) : τPGraph IncSort where
  V := IncidenceVertex G
  G := IncidenceGraph G
  pred := fun s =>
    match s with
    | .vert => IncidenceVertex.IsVertex
    | .edgeObj => IncidenceVertex.IsEdgeObj

/-- Two vertices are adjacent iff some edge object is incident to both and
they are distinct. -/
theorem adj_iff_exists_edgeSet {V : Type*} {G : SimpleGraph V} {u w : V} :
    G.Adj u w ↔
      ∃ val : G.edgeSet,
        u ∈ (val : Sym2 V) ∧ w ∈ (val : Sym2 V) ∧ u ≠ w := by
  constructor
  · intro h
    exact ⟨⟨s(u, w), h⟩, by simp, by simp, h.ne⟩
  · rintro ⟨⟨e, he⟩, hu, hw, hne⟩
    induction e using Sym2.ind with
    | _ a b =>
        rw [SimpleGraph.mem_edgeSet] at he
        rcases Sym2.mem_iff.mp hu with rfl | rfl <;>
          rcases Sym2.mem_iff.mp hw with rfl | rfl
        · exact absurd rfl hne
        · exact he
        · exact he.symm
        · exact absurd rfl hne

/-! ## Parity arithmetic for the merged variable namespaces -/

private theorem two_mul_inj {x y : ℕ} (h : 2 * x = 2 * y) : x = y :=
  Nat.eq_of_mul_eq_mul_left (by decide) h

private theorem two_mul_add_one_inj {x y : ℕ} (h : 2 * x + 1 = 2 * y + 1) :
    x = y :=
  two_mul_inj (Nat.add_right_cancel h)

private theorem two_mul_ne_two_mul_add_one' {x y : ℕ} :
    2 * x ≠ 2 * y + 1 :=
  Nat.two_mul_ne_two_mul_add_one

/-! ## The sort guards for set quantifiers -/

/-- Every member of `X` is an original vertex; bound variable `0`. -/
def vertSetGuard (X : Language.SOVar) : Language.Formula IncSort :=
  .forallFO 0 (.impl (.inSet 0 X) (.pred .vert 0))

/-- Every member of `X` is an edge object; bound variable `0`. -/
def edgeSetGuard (X : Language.SOVar) : Language.Formula IncSort :=
  .forallFO 0 (.impl (.inSet 0 X) (.pred .edgeObj 0))

/-! ## Main definition: the translation -/

namespace Formula

/--
The MSO₂-to-MSO₁ translation over the coloured incidence structure.

Atoms about vertices and edge objects become the corresponding one-sorted
atoms on the parity-encoded variables; `edge x y` becomes the existence of a
common incident edge object between distinct vertices; quantifiers are
guarded by the sort predicates.
-/
def toIncidence : Formula → Language.Formula IncSort
  | .false_ => .false_
  | .equal x y => .equal (2 * x) (2 * y)
  | .edge x y =>
      .existsFO (2 * x + 2 * y + 1)
        (.conj (.pred .edgeObj (2 * x + 2 * y + 1))
          (.conj (.adj (2 * x) (2 * x + 2 * y + 1))
            (.conj (.adj (2 * y) (2 * x + 2 * y + 1))
              (.neg (.equal (2 * x) (2 * y))))))
  | .inSet x X => .inSet (2 * x) (2 * X)
  | .equalEdge e f => .equal (2 * e + 1) (2 * f + 1)
  | .inc x e => .adj (2 * x) (2 * e + 1)
  | .inEdgeSet e F => .inSet (2 * e + 1) (2 * F + 1)
  | .neg φ => .neg φ.toIncidence
  | .conj φ ψ => .conj φ.toIncidence ψ.toIncidence
  | .disj φ ψ => .disj φ.toIncidence ψ.toIncidence
  | .impl φ ψ => .impl φ.toIncidence ψ.toIncidence
  | .biimpl φ ψ => .biimpl φ.toIncidence ψ.toIncidence
  | .existsFO x φ =>
      .existsFO (2 * x) (.conj (.pred .vert (2 * x)) φ.toIncidence)
  | .forallFO x φ =>
      .forallFO (2 * x) (.impl (.pred .vert (2 * x)) φ.toIncidence)
  | .existsSO X φ =>
      .existsSO (2 * X) (.conj (vertSetGuard (2 * X)) φ.toIncidence)
  | .forallSO X φ =>
      .forallSO (2 * X) (.impl (vertSetGuard (2 * X)) φ.toIncidence)
  | .existsEdgeFO e φ =>
      .existsFO (2 * e + 1)
        (.conj (.pred .edgeObj (2 * e + 1)) φ.toIncidence)
  | .forallEdgeFO e φ =>
      .forallFO (2 * e + 1)
        (.impl (.pred .edgeObj (2 * e + 1)) φ.toIncidence)
  | .existsEdgeSO F φ =>
      .existsSO (2 * F + 1) (.conj (edgeSetGuard (2 * F + 1)) φ.toIncidence)
  | .forallEdgeSO F φ =>
      .forallSO (2 * F + 1) (.impl (edgeSetGuard (2 * F + 1)) φ.toIncidence)

end Formula

/-! ## Semantics of the guards -/

variable {V : Type} {G : SimpleGraph V}

theorem satisfiesAt_vertSetGuard_iff
    (β : Language.Assignment (incidenceTauGraph G)) (X : Language.SOVar) :
    Language.Semantics.SatisfiesAt (incidenceTauGraph G) (vertSetGuard X) β ↔
      ∀ z ∈ β.so X, IncidenceVertex.IsVertex z := by
  simp [vertSetGuard, Language.Semantics.SatisfiesAt, incidenceTauGraph]

theorem satisfiesAt_edgeSetGuard_iff
    (β : Language.Assignment (incidenceTauGraph G)) (X : Language.SOVar) :
    Language.Semantics.SatisfiesAt (incidenceTauGraph G) (edgeSetGuard X) β ↔
      ∀ z ∈ β.so X, IncidenceVertex.IsEdgeObj z := by
  simp [edgeSetGuard, Language.Semantics.SatisfiesAt, incidenceTauGraph]

/-- A set of incidence vertices all satisfying `Vert` is the `fromV` image of
its vertex preimage. -/
theorem eq_image_fromV_of_forall_isVertex {S : Set (IncidenceVertex G)}
    (h : ∀ z ∈ S, IncidenceVertex.IsVertex z) :
    S = IncidenceVertex.fromV '' {v : V | IncidenceVertex.fromV v ∈ S} := by
  ext z
  constructor
  · intro hz
    obtain ⟨v, rfl⟩ := IncidenceVertex.isVertex_iff_exists.mp (h z hz)
    exact ⟨v, hz, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact hv

/-- A set of incidence vertices all satisfying `EdgeObj` is the `fromEdge`
image of its edge preimage. -/
theorem eq_image_fromEdge_of_forall_isEdgeObj {S : Set (IncidenceVertex G)}
    (h : ∀ z ∈ S, IncidenceVertex.IsEdgeObj z) :
    S = IncidenceVertex.fromEdge ''
      {e : G.edgeSet | IncidenceVertex.fromEdge e ∈ S} := by
  ext z
  constructor
  · intro hz
    obtain ⟨e, rfl⟩ := IncidenceVertex.isEdgeObj_iff_exists.mp (h z hz)
    exact ⟨e, hz, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact he

/-! ## Truth preservation -/

private theorem ne_shift₁ {x y : ℕ} : (2 * x : ℕ) ≠ 2 * x + 2 * y + 1 := by
  omega

private theorem ne_shift₂ {x y : ℕ} : (2 * y : ℕ) ≠ 2 * x + 2 * y + 1 := by
  omega

/--
The translation preserves truth: over the coloured incidence structure, the
translated formula holds under an assignment carrying the images of the
original assignment on the free variables iff the original formula holds in
the graph.
-/
theorem satisfiesAt_toIncidence_iff (phi : Formula)
    (α : Assignment V G.edgeSet)
    (β : Language.Assignment (incidenceTauGraph G))
    (hFO : ∀ x, phi.FreeFO x → ∃ v : V,
      α.fo x = some v ∧ β.fo (2 * x) = some (IncidenceVertex.fromV v))
    (hEFO : ∀ e, phi.FreeEdgeFO e → ∃ val : G.edgeSet,
      α.efo e = some val ∧
        β.fo (2 * e + 1) = some (IncidenceVertex.fromEdge val))
    (hSO : ∀ X, phi.FreeSO X →
      β.so (2 * X) = IncidenceVertex.fromV '' α.so X)
    (hESO : ∀ F, phi.FreeEdgeSO F →
      β.so (2 * F + 1) = IncidenceVertex.fromEdge '' α.eso F) :
    Language.Semantics.SatisfiesAt (incidenceTauGraph G) phi.toIncidence β ↔
      Semantics.SatisfiesAt phi G α := by
  induction phi generalizing α β with
  | false_ => exact Iff.rfl
  | equal x y =>
      obtain ⟨u, hu, hu'⟩ := hFO x (Or.inl rfl)
      obtain ⟨w, hw, hw'⟩ := hFO y (Or.inr rfl)
      show (∃ z : IncidenceVertex G,
          β.fo (2 * x) = some z ∧ β.fo (2 * y) = some z) ↔
        (∃ v : V, α.fo x = some v ∧ α.fo y = some v)
      rw [hu', hw']
      constructor
      · rintro ⟨z, hz1, hz2⟩
        obtain rfl := Option.some.inj hz1
        have hwu : w = u :=
          IncidenceVertex.fromV_injective (Option.some.inj hz2)
        exact ⟨u, hu, by rw [hw, hwu]⟩
      · rintro ⟨v, hv1, hv2⟩
        rw [hu] at hv1
        rw [hw] at hv2
        obtain rfl := Option.some.inj hv1
        obtain rfl := Option.some.inj hv2
        exact ⟨_, rfl, rfl⟩
  | edge x y =>
      obtain ⟨u, hu, hu'⟩ := hFO x (Or.inl rfl)
      obtain ⟨w, hw, hw'⟩ := hFO y (Or.inr rfl)
      show (∃ z : IncidenceVertex G, _) ↔
        (∃ a b : V, α.fo x = some a ∧ α.fo y = some b ∧ G.Adj a b)
      constructor
      · rintro ⟨z, hpred, hadjx, hadjy, hne⟩
        obtain ⟨n, hn, hnE⟩ := hpred
        rw [Language.Assignment.updateFO_here] at hn
        obtain rfl := Option.some.inj hn
        obtain ⟨val, rfl⟩ := IncidenceVertex.isEdgeObj_iff_exists.mp hnE
        obtain ⟨a, c, ha, hc, hac⟩ := hadjx
        rw [Language.Assignment.updateFO_other β _ ne_shift₁, hu'] at ha
        rw [Language.Assignment.updateFO_here] at hc
        obtain rfl := Option.some.inj ha
        obtain rfl := Option.some.inj hc
        obtain ⟨a', c', ha', hc', hac'⟩ := hadjy
        rw [Language.Assignment.updateFO_other β _ ne_shift₂, hw'] at ha'
        rw [Language.Assignment.updateFO_here] at hc'
        obtain rfl := Option.some.inj ha'
        obtain rfl := Option.some.inj hc'
        have hne_uw : u ≠ w := by
          intro h
          refine hne ⟨IncidenceVertex.fromV u, ?_, ?_⟩
          · rw [Language.Assignment.updateFO_other β _ ne_shift₁]
            exact hu'
          · rw [Language.Assignment.updateFO_other β _ ne_shift₂, hw', h]
        exact ⟨u, w, hu, hw,
          adj_iff_exists_edgeSet.mpr ⟨val, hac, hac', hne_uw⟩⟩
      · rintro ⟨a, b, ha, hb, hadj⟩
        rw [hu] at ha
        rw [hw] at hb
        obtain rfl := Option.some.inj ha
        obtain rfl := Option.some.inj hb
        obtain ⟨val, hum, hwm, hneuw⟩ := adj_iff_exists_edgeSet.mp hadj
        refine ⟨IncidenceVertex.fromEdge val,
          ⟨IncidenceVertex.fromEdge val,
            Language.Assignment.updateFO_here _ _ _, trivial⟩,
          ?_, ?_, ?_⟩
        · refine ⟨IncidenceVertex.fromV u, IncidenceVertex.fromEdge val,
            ?_, Language.Assignment.updateFO_here _ _ _, hum⟩
          rw [Language.Assignment.updateFO_other β _ ne_shift₁]
          exact hu'
        · refine ⟨IncidenceVertex.fromV w, IncidenceVertex.fromEdge val,
            ?_, Language.Assignment.updateFO_here _ _ _, hwm⟩
          rw [Language.Assignment.updateFO_other β _ ne_shift₂]
          exact hw'
        · rintro ⟨n, hn1, hn2⟩
          rw [Language.Assignment.updateFO_other β _ ne_shift₁, hu'] at hn1
          rw [Language.Assignment.updateFO_other β _ ne_shift₂, hw'] at hn2
          obtain rfl := Option.some.inj hn1
          exact hneuw
            (IncidenceVertex.fromV_injective (Option.some.inj hn2)).symm
  | inSet x X =>
      obtain ⟨u, hu, hu'⟩ := hFO x rfl
      have hX := hSO X rfl
      show (∃ z : IncidenceVertex G,
          β.fo (2 * x) = some z ∧ z ∈ β.so (2 * X)) ↔
        (∃ v : V, α.fo x = some v ∧ v ∈ α.so X)
      rw [hu', hX]
      constructor
      · rintro ⟨z, hz, hzm⟩
        obtain rfl := Option.some.inj hz
        obtain ⟨v, hv, hveq⟩ := hzm
        exact ⟨u, hu, by
          rwa [← IncidenceVertex.fromV_injective hveq]⟩
      · rintro ⟨v, hv, hvm⟩
        rw [hu] at hv
        obtain rfl := Option.some.inj hv
        exact ⟨_, rfl, ⟨_, hvm, rfl⟩⟩
  | equalEdge e f =>
      obtain ⟨val₁, hv₁, hv₁'⟩ := hEFO e (Or.inl rfl)
      obtain ⟨val₂, hv₂, hv₂'⟩ := hEFO f (Or.inr rfl)
      show (∃ z : IncidenceVertex G,
          β.fo (2 * e + 1) = some z ∧ β.fo (2 * f + 1) = some z) ↔
        (∃ val : G.edgeSet, α.efo e = some val ∧ α.efo f = some val)
      rw [hv₁', hv₂']
      constructor
      · rintro ⟨z, hz1, hz2⟩
        obtain rfl := Option.some.inj hz1
        have h21 : val₂ = val₁ :=
          IncidenceVertex.fromEdge_injective (Option.some.inj hz2)
        exact ⟨val₁, hv₁, by rw [hv₂, h21]⟩
      · rintro ⟨val, h1, h2⟩
        rw [hv₁] at h1
        rw [hv₂] at h2
        obtain rfl := Option.some.inj h1
        obtain rfl := Option.some.inj h2
        exact ⟨_, rfl, rfl⟩
  | inc x e =>
      obtain ⟨u, hu, hu'⟩ := hFO x rfl
      obtain ⟨val, hval, hval'⟩ := hEFO e rfl
      show (∃ a c : IncidenceVertex G,
          β.fo (2 * x) = some a ∧ β.fo (2 * e + 1) = some c ∧
            (IncidenceGraph G).Adj a c) ↔
        (∃ (v : V) (w : G.edgeSet), α.fo x = some v ∧ α.efo e = some w ∧
          v ∈ (w : Sym2 V))
      rw [hu', hval']
      constructor
      · rintro ⟨a, c, ha, hc, hac⟩
        obtain rfl := Option.some.inj ha
        obtain rfl := Option.some.inj hc
        exact ⟨u, val, hu, hval, hac⟩
      · rintro ⟨v, w, hv, hw, hmem⟩
        rw [hu] at hv
        rw [hval] at hw
        obtain rfl := Option.some.inj hv
        obtain rfl := Option.some.inj hw
        exact ⟨_, _, rfl, rfl, hmem⟩
  | inEdgeSet e F =>
      obtain ⟨val, hval, hval'⟩ := hEFO e rfl
      have hF := hESO F rfl
      show (∃ z : IncidenceVertex G,
          β.fo (2 * e + 1) = some z ∧ z ∈ β.so (2 * F + 1)) ↔
        (∃ w : G.edgeSet, α.efo e = some w ∧ w ∈ α.eso F)
      rw [hval', hF]
      constructor
      · rintro ⟨z, hz, hzm⟩
        obtain rfl := Option.some.inj hz
        obtain ⟨w, hw, hweq⟩ := hzm
        exact ⟨val, hval, by
          rwa [← IncidenceVertex.fromEdge_injective hweq]⟩
      · rintro ⟨w, hw, hwm⟩
        rw [hval] at hw
        obtain rfl := Option.some.inj hw
        exact ⟨_, rfl, ⟨_, hwm, rfl⟩⟩
  | neg φ ih =>
      exact not_congr (ih α β hFO hEFO hSO hESO)
  | conj φ ψ ihφ ihψ =>
      exact and_congr
        (ihφ α β (fun x hx => hFO x (Or.inl hx)) (fun e he => hEFO e (Or.inl he))
          (fun X hX => hSO X (Or.inl hX)) (fun F hF => hESO F (Or.inl hF)))
        (ihψ α β (fun x hx => hFO x (Or.inr hx)) (fun e he => hEFO e (Or.inr he))
          (fun X hX => hSO X (Or.inr hX)) (fun F hF => hESO F (Or.inr hF)))
  | disj φ ψ ihφ ihψ =>
      exact or_congr
        (ihφ α β (fun x hx => hFO x (Or.inl hx)) (fun e he => hEFO e (Or.inl he))
          (fun X hX => hSO X (Or.inl hX)) (fun F hF => hESO F (Or.inl hF)))
        (ihψ α β (fun x hx => hFO x (Or.inr hx)) (fun e he => hEFO e (Or.inr he))
          (fun X hX => hSO X (Or.inr hX)) (fun F hF => hESO F (Or.inr hF)))
  | impl φ ψ ihφ ihψ =>
      exact imp_congr
        (ihφ α β (fun x hx => hFO x (Or.inl hx)) (fun e he => hEFO e (Or.inl he))
          (fun X hX => hSO X (Or.inl hX)) (fun F hF => hESO F (Or.inl hF)))
        (ihψ α β (fun x hx => hFO x (Or.inr hx)) (fun e he => hEFO e (Or.inr he))
          (fun X hX => hSO X (Or.inr hX)) (fun F hF => hESO F (Or.inr hF)))
  | biimpl φ ψ ihφ ihψ =>
      exact iff_congr
        (ihφ α β (fun x hx => hFO x (Or.inl hx)) (fun e he => hEFO e (Or.inl he))
          (fun X hX => hSO X (Or.inl hX)) (fun F hF => hESO F (Or.inl hF)))
        (ihψ α β (fun x hx => hFO x (Or.inr hx)) (fun e he => hEFO e (Or.inr he))
          (fun X hX => hSO X (Or.inr hX)) (fun F hF => hESO F (Or.inr hF)))
  | existsFO x φ ih =>
      have hstep : ∀ v : V,
          Language.Semantics.SatisfiesAt (incidenceTauGraph G) φ.toIncidence
            (β.updateFO (2 * x) (.fromV v)) ↔
          Semantics.SatisfiesAt φ G (α.updateFO x v) := by
        intro v
        refine ih _ _ ?_ (fun e he => ?_) (fun X hX => hSO X hX)
          (fun F hF => hESO F hF)
        · intro y hy
          by_cases hyx : y = x
          · subst hyx
            exact ⟨v, by simp, by simp⟩
          · obtain ⟨u, hu, hu'⟩ := hFO y ⟨hyx, hy⟩
            refine ⟨u, ?_, ?_⟩
            · rw [Assignment.updateFO_other α v hyx]
              exact hu
            · rw [Language.Assignment.updateFO_other β _
                (fun h => hyx (two_mul_inj h))]
              exact hu'
        · obtain ⟨val, hval, hval'⟩ := hEFO e he
          refine ⟨val, hval, ?_⟩
          rw [Language.Assignment.updateFO_other β _
            two_mul_ne_two_mul_add_one'.symm]
          exact hval'
      show (∃ z : IncidenceVertex G, _) ↔ (∃ v : V, _)
      constructor
      · rintro ⟨z, hvert, hφ⟩
        obtain ⟨n, hn, hnv⟩ := hvert
        rw [Language.Assignment.updateFO_here] at hn
        obtain rfl := Option.some.inj hn
        obtain ⟨v, rfl⟩ := IncidenceVertex.isVertex_iff_exists.mp hnv
        exact ⟨v, (hstep v).mp hφ⟩
      · rintro ⟨v, hφ⟩
        exact ⟨.fromV v,
          ⟨.fromV v, Language.Assignment.updateFO_here _ _ _, trivial⟩,
          (hstep v).mpr hφ⟩
  | forallFO x φ ih =>
      have hstep : ∀ v : V,
          Language.Semantics.SatisfiesAt (incidenceTauGraph G) φ.toIncidence
            (β.updateFO (2 * x) (.fromV v)) ↔
          Semantics.SatisfiesAt φ G (α.updateFO x v) := by
        intro v
        refine ih _ _ ?_ (fun e he => ?_) (fun X hX => hSO X hX)
          (fun F hF => hESO F hF)
        · intro y hy
          by_cases hyx : y = x
          · subst hyx
            exact ⟨v, by simp, by simp⟩
          · obtain ⟨u, hu, hu'⟩ := hFO y ⟨hyx, hy⟩
            refine ⟨u, ?_, ?_⟩
            · rw [Assignment.updateFO_other α v hyx]
              exact hu
            · rw [Language.Assignment.updateFO_other β _
                (fun h => hyx (two_mul_inj h))]
              exact hu'
        · obtain ⟨val, hval, hval'⟩ := hEFO e he
          refine ⟨val, hval, ?_⟩
          rw [Language.Assignment.updateFO_other β _
            two_mul_ne_two_mul_add_one'.symm]
          exact hval'
      show (∀ z : IncidenceVertex G, _ → _) ↔ (∀ v : V, _)
      constructor
      · intro h v
        exact (hstep v).mp (h (.fromV v)
          ⟨.fromV v, Language.Assignment.updateFO_here _ _ _, trivial⟩)
      · intro h z hvert
        obtain ⟨n, hn, hnv⟩ := hvert
        rw [Language.Assignment.updateFO_here] at hn
        obtain rfl := Option.some.inj hn
        obtain ⟨v, rfl⟩ := IncidenceVertex.isVertex_iff_exists.mp hnv
        exact (hstep v).mpr (h v)
  | existsEdgeFO e φ ih =>
      have hstep : ∀ val : G.edgeSet,
          Language.Semantics.SatisfiesAt (incidenceTauGraph G) φ.toIncidence
            (β.updateFO (2 * e + 1) (.fromEdge val)) ↔
          Semantics.SatisfiesAt φ G (α.updateEdgeFO e val) := by
        intro val
        refine ih _ _ (fun y hy => ?_) (fun f hf => ?_)
          (fun X hX => hSO X hX) (fun F hF => hESO F hF)
        · obtain ⟨u, hu, hu'⟩ := hFO y hy
          refine ⟨u, hu, ?_⟩
          rw [Language.Assignment.updateFO_other β _
            two_mul_ne_two_mul_add_one']
          exact hu'
        · by_cases hfe : f = e
          · subst hfe
            exact ⟨val, by simp, by simp⟩
          · obtain ⟨w, hw, hw'⟩ := hEFO f ⟨hfe, hf⟩
            refine ⟨w, ?_, ?_⟩
            · rw [Assignment.updateEdgeFO_other α val hfe]
              exact hw
            · rw [Language.Assignment.updateFO_other β _
                (fun h => hfe (two_mul_add_one_inj h))]
              exact hw'
      show (∃ z : IncidenceVertex G, _) ↔ (∃ val : G.edgeSet, _)
      constructor
      · rintro ⟨z, hobj, hφ⟩
        obtain ⟨n, hn, hnE⟩ := hobj
        rw [Language.Assignment.updateFO_here] at hn
        obtain rfl := Option.some.inj hn
        obtain ⟨val, rfl⟩ := IncidenceVertex.isEdgeObj_iff_exists.mp hnE
        exact ⟨val, (hstep val).mp hφ⟩
      · rintro ⟨val, hφ⟩
        exact ⟨.fromEdge val,
          ⟨.fromEdge val, Language.Assignment.updateFO_here _ _ _, trivial⟩,
          (hstep val).mpr hφ⟩
  | forallEdgeFO e φ ih =>
      have hstep : ∀ val : G.edgeSet,
          Language.Semantics.SatisfiesAt (incidenceTauGraph G) φ.toIncidence
            (β.updateFO (2 * e + 1) (.fromEdge val)) ↔
          Semantics.SatisfiesAt φ G (α.updateEdgeFO e val) := by
        intro val
        refine ih _ _ (fun y hy => ?_) (fun f hf => ?_)
          (fun X hX => hSO X hX) (fun F hF => hESO F hF)
        · obtain ⟨u, hu, hu'⟩ := hFO y hy
          refine ⟨u, hu, ?_⟩
          rw [Language.Assignment.updateFO_other β _
            two_mul_ne_two_mul_add_one']
          exact hu'
        · by_cases hfe : f = e
          · subst hfe
            exact ⟨val, by simp, by simp⟩
          · obtain ⟨w, hw, hw'⟩ := hEFO f ⟨hfe, hf⟩
            refine ⟨w, ?_, ?_⟩
            · rw [Assignment.updateEdgeFO_other α val hfe]
              exact hw
            · rw [Language.Assignment.updateFO_other β _
                (fun h => hfe (two_mul_add_one_inj h))]
              exact hw'
      show (∀ z : IncidenceVertex G, _ → _) ↔ (∀ val : G.edgeSet, _)
      constructor
      · intro h val
        exact (hstep val).mp (h (.fromEdge val)
          ⟨.fromEdge val, Language.Assignment.updateFO_here _ _ _, trivial⟩)
      · intro h z hobj
        obtain ⟨n, hn, hnE⟩ := hobj
        rw [Language.Assignment.updateFO_here] at hn
        obtain rfl := Option.some.inj hn
        obtain ⟨val, rfl⟩ := IncidenceVertex.isEdgeObj_iff_exists.mp hnE
        exact (hstep val).mpr (h val)
  | existsSO X φ ih =>
      have hstep : ∀ S₀ : Set V,
          Language.Semantics.SatisfiesAt (incidenceTauGraph G) φ.toIncidence
            (β.updateSO (2 * X) (IncidenceVertex.fromV '' S₀)) ↔
          Semantics.SatisfiesAt φ G (α.updateSO X S₀) := by
        intro S₀
        refine ih _ _ (fun y hy => hFO y hy) (fun e he => hEFO e he)
          (fun Y hY => ?_) (fun F hF => ?_)
        · by_cases hYX : Y = X
          · subst hYX
            rw [Language.Assignment.updateSO_here, Assignment.updateSO_here]
          · rw [Language.Assignment.updateSO_other β _
              (fun h => hYX (two_mul_inj h)),
              Assignment.updateSO_other α _ hYX]
            exact hSO Y ⟨hYX, hY⟩
        · rw [Language.Assignment.updateSO_other β _
            two_mul_ne_two_mul_add_one'.symm]
          exact hESO F hF
      show (∃ S : Set (IncidenceVertex G), _) ↔ (∃ S₀ : Set V, _)
      constructor
      · rintro ⟨S, hguard, hφ⟩
        have hS := (satisfiesAt_vertSetGuard_iff _ _).mp hguard
        rw [Language.Assignment.updateSO_here] at hS
        have hSeq := eq_image_fromV_of_forall_isVertex hS
        rw [hSeq] at hφ
        exact ⟨_, (hstep _).mp hφ⟩
      · rintro ⟨S₀, hφ⟩
        refine ⟨IncidenceVertex.fromV '' S₀, ?_, (hstep S₀).mpr hφ⟩
        rw [satisfiesAt_vertSetGuard_iff, Language.Assignment.updateSO_here]
        rintro z ⟨v, hv, rfl⟩
        trivial
  | forallSO X φ ih =>
      have hstep : ∀ S₀ : Set V,
          Language.Semantics.SatisfiesAt (incidenceTauGraph G) φ.toIncidence
            (β.updateSO (2 * X) (IncidenceVertex.fromV '' S₀)) ↔
          Semantics.SatisfiesAt φ G (α.updateSO X S₀) := by
        intro S₀
        refine ih _ _ (fun y hy => hFO y hy) (fun e he => hEFO e he)
          (fun Y hY => ?_) (fun F hF => ?_)
        · by_cases hYX : Y = X
          · subst hYX
            rw [Language.Assignment.updateSO_here, Assignment.updateSO_here]
          · rw [Language.Assignment.updateSO_other β _
              (fun h => hYX (two_mul_inj h)),
              Assignment.updateSO_other α _ hYX]
            exact hSO Y ⟨hYX, hY⟩
        · rw [Language.Assignment.updateSO_other β _
            two_mul_ne_two_mul_add_one'.symm]
          exact hESO F hF
      show (∀ S : Set (IncidenceVertex G), _ → _) ↔ (∀ S₀ : Set V, _)
      constructor
      · intro h S₀
        refine (hstep S₀).mp (h (IncidenceVertex.fromV '' S₀) ?_)
        rw [satisfiesAt_vertSetGuard_iff, Language.Assignment.updateSO_here]
        rintro z ⟨v, hv, rfl⟩
        trivial
      · intro h S hguard
        have hS := (satisfiesAt_vertSetGuard_iff _ _).mp hguard
        rw [Language.Assignment.updateSO_here] at hS
        have hSeq := eq_image_fromV_of_forall_isVertex hS
        rw [hSeq]
        exact (hstep _).mpr (h _)
  | existsEdgeSO F φ ih =>
      have hstep : ∀ S₀ : Set G.edgeSet,
          Language.Semantics.SatisfiesAt (incidenceTauGraph G) φ.toIncidence
            (β.updateSO (2 * F + 1) (IncidenceVertex.fromEdge '' S₀)) ↔
          Semantics.SatisfiesAt φ G (α.updateEdgeSO F S₀) := by
        intro S₀
        refine ih _ _ (fun y hy => hFO y hy) (fun e he => hEFO e he)
          (fun Y hY => ?_) (fun F' hF' => ?_)
        · rw [Language.Assignment.updateSO_other β _
            two_mul_ne_two_mul_add_one']
          exact hSO Y hY
        · by_cases hFF : F' = F
          · subst hFF
            rw [Language.Assignment.updateSO_here, Assignment.updateEdgeSO_here]
          · rw [Language.Assignment.updateSO_other β _
              (fun h => hFF (two_mul_add_one_inj h)),
              Assignment.updateEdgeSO_other α _ hFF]
            exact hESO F' ⟨hFF, hF'⟩
      show (∃ S : Set (IncidenceVertex G), _) ↔ (∃ S₀ : Set G.edgeSet, _)
      constructor
      · rintro ⟨S, hguard, hφ⟩
        have hS := (satisfiesAt_edgeSetGuard_iff _ _).mp hguard
        rw [Language.Assignment.updateSO_here] at hS
        have hSeq := eq_image_fromEdge_of_forall_isEdgeObj hS
        rw [hSeq] at hφ
        exact ⟨_, (hstep _).mp hφ⟩
      · rintro ⟨S₀, hφ⟩
        refine ⟨IncidenceVertex.fromEdge '' S₀, ?_, (hstep S₀).mpr hφ⟩
        rw [satisfiesAt_edgeSetGuard_iff, Language.Assignment.updateSO_here]
        rintro z ⟨e, he, rfl⟩
        trivial
  | forallEdgeSO F φ ih =>
      have hstep : ∀ S₀ : Set G.edgeSet,
          Language.Semantics.SatisfiesAt (incidenceTauGraph G) φ.toIncidence
            (β.updateSO (2 * F + 1) (IncidenceVertex.fromEdge '' S₀)) ↔
          Semantics.SatisfiesAt φ G (α.updateEdgeSO F S₀) := by
        intro S₀
        refine ih _ _ (fun y hy => hFO y hy) (fun e he => hEFO e he)
          (fun Y hY => ?_) (fun F' hF' => ?_)
        · rw [Language.Assignment.updateSO_other β _
            two_mul_ne_two_mul_add_one']
          exact hSO Y hY
        · by_cases hFF : F' = F
          · subst hFF
            rw [Language.Assignment.updateSO_here, Assignment.updateEdgeSO_here]
          · rw [Language.Assignment.updateSO_other β _
              (fun h => hFF (two_mul_add_one_inj h)),
              Assignment.updateEdgeSO_other α _ hFF]
            exact hESO F' ⟨hFF, hF'⟩
      show (∀ S : Set (IncidenceVertex G), _ → _) ↔ (∀ S₀ : Set G.edgeSet, _)
      constructor
      · intro h S₀
        refine (hstep S₀).mp (h (IncidenceVertex.fromEdge '' S₀) ?_)
        rw [satisfiesAt_edgeSetGuard_iff, Language.Assignment.updateSO_here]
        rintro z ⟨e, he, rfl⟩
        trivial
      · intro h S hguard
        have hS := (satisfiesAt_edgeSetGuard_iff _ _).mp hguard
        rw [Language.Assignment.updateSO_here] at hS
        have hSeq := eq_image_fromEdge_of_forall_isEdgeObj hS
        rw [hSeq]
        exact (hstep _).mpr (h _)

/-- The closed-sentence form of Phase 4: an MSO₂ sentence holds in `G` iff
its translation holds in the coloured incidence structure. -/
theorem satisfies_toIncidence_iff (phi : Formula) (hclosed : phi.Closed) :
    Language.Semantics.Satisfies (incidenceTauGraph G) phi.toIncidence ↔
      Semantics.Satisfies G phi := by
  rw [Semantics.satisfies_iff_satisfiesAt_of_closed hclosed]
  exact satisfiesAt_toIncidence_iff phi Assignment.empty
    (Language.Assignment.empty _)
    (fun x hx => absurd hx (hclosed.1 x))
    (fun e he => absurd he (hclosed.2.2.1 e))
    (fun X hX => absurd hX (hclosed.2.1 X))
    (fun F hF => absurd hF (hclosed.2.2.2 F))

/--
Phase 4 combined: from a width-`omega` decomposition of `G`, the coloured
incidence structure carries a decomposition of width at most `max omega 2`,
and MSO₂ model checking on `G` reduces to MSO₁ model checking on it.
-/
theorem incidence_reduction {V : Type} [Fintype V] {G : SimpleGraph V}
    (D : TreeDecomposition G) (omega : ℕ) (hwidth : D.HasWidth omega)
    (phi : Formula) (hclosed : phi.Closed) :
    D.incidenceDecomposition.HasWidth (max omega 2) ∧
      (Semantics.Satisfies G phi ↔
        Language.Semantics.Satisfies (incidenceTauGraph G)
          phi.toIncidence) :=
  ⟨D.incidenceDecomposition_hasWidth omega hwidth,
    (satisfies_toIncidence_iff phi hclosed).symm⟩

end GraphMSO
