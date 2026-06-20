import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import GraphMSO.Semantics

namespace SimpleGraph

variable {V : Type} (G : SimpleGraph V)

/-- A vertex set dominates the graph if every vertex is in it or adjacent to one of it. -/
def IsDominating (S : Set V) : Prop :=
  ∀ v : V, v ∈ S ∨ ∃ u : V, u ∈ S ∧ G.Adj u v

/-- A set covers all edges (`IsVertexCover`) iff, ranging over `G.edgeSet`, every
edge has an endpoint in it. This bridges the adjacency-based mathlib definition and
the incidence view used by MSO2 edge quantifiers. -/
theorem isVertexCover_iff_forall_edge (S : Set V) :
    G.IsVertexCover S ↔ ∀ e : G.edgeSet, ∃ v : V, v ∈ S ∧ v ∈ (e : Sym2 V) := by
  unfold SimpleGraph.IsVertexCover
  constructor
  · rintro h ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
      rcases h (G.mem_edgeSet.mp he) with ha | hb
      · exact ⟨a, ha, Sym2.mem_iff.mpr (Or.inl rfl)⟩
      · exact ⟨b, hb, Sym2.mem_iff.mpr (Or.inr rfl)⟩
  · intro h v w hvw
    obtain ⟨u, huS, hu⟩ := h ⟨s(v, w), G.mem_edgeSet.mpr hvw⟩
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · exact Or.inl huS
    · exact Or.inr huS

/-- A graph is bipartite (`IsBipartite`) iff there is a set `S` of vertices such that,
ranging over `G.edgeSet`, every edge has one endpoint in `S` and one outside it. The
witnessing parts are `S` and its complement. -/
theorem isBipartite_iff_forall_edge :
    G.IsBipartite ↔
      ∃ S : Set V, ∀ e : G.edgeSet, ∃ u v : V,
        u ∈ S ∧ v ∉ S ∧ u ∈ (e : Sym2 V) ∧ v ∈ (e : Sym2 V) := by
  rw [SimpleGraph.isBipartite_iff_exists_isBipartiteWith]
  constructor
  · rintro ⟨s, t, hdisj, hadj⟩
    refine ⟨s, ?_⟩
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
      rcases hadj (G.mem_edgeSet.mp he) with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨a, b, ha, Set.disjoint_right.mp hdisj hb,
          Sym2.mem_iff.mpr (Or.inl rfl), Sym2.mem_iff.mpr (Or.inr rfl)⟩
      · exact ⟨b, a, hb, Set.disjoint_right.mp hdisj ha,
          Sym2.mem_iff.mpr (Or.inr rfl), Sym2.mem_iff.mpr (Or.inl rfl)⟩
  · rintro ⟨S, h⟩
    refine ⟨S, Sᶜ, disjoint_compl_right, ?_⟩
    intro v w hvw
    obtain ⟨u, u', huS, hu'notS, hu, hu'⟩ := h ⟨s(v, w), G.mem_edgeSet.mpr hvw⟩
    rcases Sym2.mem_iff.mp hu with rfl | rfl <;> rcases Sym2.mem_iff.mp hu' with rfl | rfl
    · exact absurd huS hu'notS
    · exact Or.inl ⟨huS, hu'notS⟩
    · exact Or.inr ⟨hu'notS, huS⟩
    · exact absurd huS hu'notS

/-- The spanning subgraph of `G` whose edges are exactly the set `S ⊆ G.edgeSet`:
every vertex is kept, and `v, w` are adjacent precisely when the edge `s(v, w)`
belongs to `S`. -/
def spanningSubgraphOfEdges (S : Set G.edgeSet) : G.Subgraph where
  verts := Set.univ
  Adj v w := s(v, w) ∈ Subtype.val '' S
  adj_sub := by
    rintro v w ⟨e, -, he⟩
    exact G.mem_edgeSet.mp (he ▸ e.2)
  edge_vert := by intro v w _; exact Set.mem_univ v
  symm := by
    intro v w h
    rwa [Sym2.eq_swap]

@[simp]
theorem spanningSubgraphOfEdges_adj (S : Set G.edgeSet) (v w : V) :
    (G.spanningSubgraphOfEdges S).Adj v w ↔ s(v, w) ∈ Subtype.val '' S :=
  Iff.rfl

/-- The spanning subgraph carved out by an edge set `S` is a perfect matching iff,
ranging over `G.edgeSet`, every vertex is incident to exactly one edge of `S`. This
bridges mathlib's subgraph-based `IsPerfectMatching` and the incidence view used by
the MSO2 perfect-matching formula. -/
theorem isPerfectMatching_spanningSubgraphOfEdges_iff (S : Set G.edgeSet) :
    (G.spanningSubgraphOfEdges S).IsPerfectMatching ↔
      ∀ v : V, ∃! e : G.edgeSet, e ∈ S ∧ v ∈ (e : Sym2 V) := by
  rw [Subgraph.isPerfectMatching_iff]
  refine forall_congr' fun v => ?_
  simp only [spanningSubgraphOfEdges_adj]
  constructor
  · rintro ⟨w, hw, huniq⟩
    obtain ⟨e, heS, he⟩ := hw
    have hve : v ∈ (e : Sym2 V) := by rw [he]; exact Sym2.mem_iff.mpr (Or.inl rfl)
    refine ⟨e, ⟨heS, hve⟩, ?_⟩
    rintro e' ⟨he'S, hve'⟩
    have hspec : s(v, Sym2.Mem.other hve') = (e' : Sym2 V) := Sym2.other_spec hve'
    have hwoth : Sym2.Mem.other hve' = w := huniq _ ⟨e', he'S, hspec.symm⟩
    apply Subtype.ext
    rw [← hspec, hwoth, he]
  · rintro ⟨e, ⟨heS, hve⟩, huniq⟩
    have hspec : s(v, Sym2.Mem.other hve) = (e : Sym2 V) := Sym2.other_spec hve
    refine ⟨Sym2.Mem.other hve, ⟨e, heS, hspec.symm⟩, ?_⟩
    rintro w' ⟨e', he'S, he'⟩
    have hve' : v ∈ (e' : Sym2 V) := by rw [he']; exact Sym2.mem_iff.mpr (Or.inl rfl)
    have hee : e' = e := huniq e' ⟨he'S, hve'⟩
    rw [hee] at he'
    exact (Sym2.congr_right.mp (hspec.trans he')).symm

/-- The edge set `F` contains exactly two edges incident to `v`. -/
def HasExactlyTwoIncidentEdgesIn (F : Set G.edgeSet) (v : V) : Prop :=
  ∃ e₀ e₁ : G.edgeSet,
    e₀ ∈ F ∧ e₁ ∈ F ∧
    v ∈ (e₀ : Sym2 V) ∧ v ∈ (e₁ : Sym2 V) ∧ e₀ ≠ e₁ ∧
    ∀ e : G.edgeSet, e ∈ F -> v ∈ (e : Sym2 V) -> e = e₀ ∨ e = e₁

/-- No edge has one endpoint in `S` and the other in `T`. -/
def HasNoEdgesBetween (S T : Set V) : Prop :=
  ∀ u v : V, u ∈ S -> v ∈ T -> ¬ G.Adj u v

/-- `S` and `T` form a nontrivial partition of all vertices. -/
def IsNontrivialPartition (S T : Set V) : Prop :=
  S.Nonempty ∧ T.Nonempty ∧
    (∀ v : V, v ∈ S ∨ v ∈ T) ∧
    (∀ v : V, v ∈ S -> v ∈ T -> False)

/-- The graph is disconnected if its vertices split into two nonempty parts
with no edges between them. -/
def IsDisconnectedByPartition : Prop :=
  ∃ S T : Set V, IsNontrivialPartition S T ∧ G.HasNoEdgesBetween S T

/-- Connectivity, defined as the negation of the partition-based disconnectedness. -/
def IsConnectedByPartition : Prop :=
  ¬ G.IsDisconnectedByPartition

/-- The partition-based disconnectedness coincides with the failure of mathlib's
`Preconnected` (no path between some pair of vertices). The witnessing cut is the set
of vertices reachable from one endpoint and its complement. -/
theorem isDisconnectedByPartition_iff_not_preconnected :
    G.IsDisconnectedByPartition ↔ ¬ G.Preconnected := by
  constructor
  · rintro ⟨S, T, ⟨hSne, hTne, hcover, hdisj⟩, hno⟩ hpre
    obtain ⟨u, huS⟩ := hSne
    obtain ⟨v, hvT⟩ := hTne
    have hclosed : ∀ {a b : V}, a ∈ S → G.Adj a b → b ∈ S := by
      intro a b ha hab
      rcases hcover b with hbS | hbT
      · exact hbS
      · exact absurd hab (hno a b ha hbT)
    have closure : ∀ {a b : V}, G.Walk a b → a ∈ S → b ∈ S := by
      intro a b p
      induction p with
      | nil => exact fun h => h
      | cons hadj _ ih => exact fun h => ih (hclosed h hadj)
    obtain ⟨p⟩ := hpre u v
    exact hdisj v (closure p huS) hvT
  · intro hnpre
    simp only [SimpleGraph.Preconnected, not_forall] at hnpre
    obtain ⟨u, v, huv⟩ := hnpre
    refine ⟨{w | G.Reachable u w}, {w | ¬ G.Reachable u w},
      ⟨⟨u, ?_⟩, ⟨v, ?_⟩, ?_, ?_⟩, ?_⟩
    · exact SimpleGraph.Reachable.refl u
    · exact huv
    · intro w
      by_cases h : G.Reachable u w
      · exact Or.inl h
      · exact Or.inr h
    · intro w hwS hwT
      exact (hwT : ¬ G.Reachable u w) hwS
    · intro a b haS hbT hab
      exact (hbT : ¬ G.Reachable u b) ((haS : G.Reachable u a).trans hab.reachable)

/-- Partition-based connectivity coincides with mathlib's `Preconnected`. (For nonempty
vertex types this is `Connected`; the empty graph is vacuously `Preconnected`.) -/
theorem isConnectedByPartition_iff_preconnected :
    G.IsConnectedByPartition ↔ G.Preconnected := by
  simp only [IsConnectedByPartition, isDisconnectedByPartition_iff_not_preconnected, not_not]

/-- The edge set `F` has an edge crossing from `S` to `T`. -/
def HasCrossingEdgeIn (F : Set G.edgeSet) (S T : Set V) : Prop :=
  ∃ e : G.edgeSet, e ∈ F ∧
    ∃ u v : V, u ∈ S ∧ v ∈ T ∧ u ∈ (e : Sym2 V) ∧ v ∈ (e : Sym2 V)

/-- The spanning subgraph with edge set `F` is connected, phrased by cuts:
every nontrivial partition of the vertices has a selected crossing edge. -/
def EdgeSetConnectedSpanning (F : Set G.edgeSet) : Prop :=
  ∀ S T : Set V, IsNontrivialPartition S T -> G.HasCrossingEdgeIn F S T

/-- A Hamiltonian cycle, represented as a selected edge set: every vertex has
degree exactly two in the selected edges, and those selected edges are connected. -/
def HasHamiltonianCycleByEdges : Prop :=
  ∃ F : Set G.edgeSet,
    (∀ v : V, G.HasExactlyTwoIncidentEdgesIn F v) ∧
    G.EdgeSetConnectedSpanning F

/-- The edge-set (2-factor) characterization of a Hamiltonian cycle coincides with the
existence of a mathlib `Walk.IsHamiltonianCycle`, for a nonempty finite graph. -/
theorem hasHamiltonianCycleByEdges_iff [Fintype V] [DecidableEq V] [Nonempty V] :
    G.HasHamiltonianCycleByEdges ↔ ∃ a, ∃ p : G.Walk a a, p.IsHamiltonianCycle := by
  constructor
  · rintro ⟨F, hdeg, hconn⟩
    classical
    set H : SimpleGraph V := (G.spanningSubgraphOfEdges F).spanningCoe with hH
    have hHadj : ∀ v w, H.Adj v w ↔ s(v, w) ∈ Subtype.val '' F := by
      intro v w
      rw [hH, Subgraph.spanningCoe_adj, spanningSubgraphOfEdges_adj]
    have hcyc : H.IsCycles := by
      intro v _
      obtain ⟨e₀, e₁, he₀F, he₁F, hve₀, hve₁, hne, huniq⟩ := hdeg v
      refine Set.ncard_eq_two.mpr ⟨Sym2.Mem.other hve₀, Sym2.Mem.other hve₁, ?_, ?_⟩
      · intro heq
        exact hne (Subtype.ext (by rw [← Sym2.other_spec hve₀, ← Sym2.other_spec hve₁, heq]))
      · ext w
        simp only [SimpleGraph.mem_neighborSet, hHadj, Set.mem_image, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        constructor
        · rintro ⟨e', he'F, he'eq⟩
          have hve' : v ∈ (e' : Sym2 V) := by rw [he'eq]; exact Sym2.mem_mk_left v w
          rcases huniq e' he'F hve' with rfl | rfl
          · left
            have heq : s(v, Sym2.Mem.other hve₀) = s(v, w) := by
              rw [Sym2.other_spec hve₀]; exact he'eq
            exact (Sym2.congr_right.mp heq).symm
          · right
            have heq : s(v, Sym2.Mem.other hve₁) = s(v, w) := by
              rw [Sym2.other_spec hve₁]; exact he'eq
            exact (Sym2.congr_right.mp heq).symm
        · rintro (rfl | rfl)
          · exact ⟨e₀, he₀F, (Sym2.other_spec hve₀).symm⟩
          · exact ⟨e₁, he₁F, (Sym2.other_spec hve₁).symm⟩
    have hpre : H.Preconnected := by
      rw [← H.isConnectedByPartition_iff_preconnected]
      intro hdisc
      obtain ⟨S, T, hpart, hno⟩ := hdisc
      obtain ⟨e, heF, u, w, huS, hwT, hue, hwe⟩ := hconn S T hpart
      have huw : u ≠ w := fun h => hpart.2.2.2 u huS (h ▸ hwT)
      have hwoth : w = Sym2.Mem.other hue := by
        have hmem : w ∈ s(u, Sym2.Mem.other hue) := by rw [Sym2.other_spec hue]; exact hwe
        rcases Sym2.mem_iff.mp hmem with h | h
        · exact absurd h huw.symm
        · exact h
      have hee : (e : Sym2 V) = s(u, w) := by rw [← Sym2.other_spec hue, hwoth]
      exact hno u w huS hwT ((hHadj u w).mpr ⟨e, heF, hee⟩)
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    have hn : (H.neighborSet v).Nonempty := by
      obtain ⟨e₀, _, he₀F, _, hve₀, _, _, _⟩ := hdeg v
      exact ⟨Sym2.Mem.other hve₀,
        (hHadj v (Sym2.Mem.other hve₀)).mpr ⟨e₀, he₀F, (Sym2.other_spec hve₀).symm⟩⟩
    obtain ⟨q, hqc, hverts⟩ :=
      hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp (c := H.connectedComponentMk v)
        ((ConnectedComponent.mem_supp_iff _ v).mpr rfl) hn
    have hsupp : (H.connectedComponentMk v).supp = Set.univ := by
      ext w
      simp only [Set.mem_univ, iff_true, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
      exact hpre w v
    rw [hsupp] at hverts
    have hle : H ≤ G := (G.spanningSubgraphOfEdges F).spanningCoe_le
    refine ⟨v, q.mapLe hle, ?_⟩
    rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
    refine ⟨hqc.mapLe hle, fun a => ?_⟩
    rw [Walk.support_mapLe_eq_support]
    have hmem : a ∈ q.support.tail := by
      have ha : a ∈ q.support := (q.mem_verts_toSubgraph).mp (by rw [hverts]; exact Set.mem_univ a)
      rw [Walk.support_eq_cons] at ha
      rcases List.mem_cons.mp ha with rfl | h
      · exact Walk.end_mem_tail_support hqc.not_nil
      · exact h
    exact List.count_eq_one_of_mem hqc.support_nodup hmem
  · rintro ⟨a, p, hp⟩
    classical
    refine ⟨{e : G.edgeSet | (e : Sym2 V) ∈ p.edges}, ?_, ?_⟩
    · intro v
      have hvs : v ∈ p.support := hp.mem_support v
      have hmem : ∀ w, p.toSubgraph.Adj v w ↔ s(v, w) ∈ p.edges :=
        fun w => Walk.adj_toSubgraph_iff_mem_edges
      obtain ⟨w₀, w₁, hne, hset⟩ := Set.ncard_eq_two.mp
        (hp.isCycle.ncard_neighborSet_toSubgraph_eq_two hvs)
      have hadj0 : p.toSubgraph.Adj v w₀ := by
        have : w₀ ∈ p.toSubgraph.neighborSet v := by rw [hset]; exact Set.mem_insert _ _
        exact this
      have hadj1 : p.toSubgraph.Adj v w₁ := by
        have : w₁ ∈ p.toSubgraph.neighborSet v := by
          rw [hset]; exact Set.mem_insert_of_mem _ rfl
        exact this
      have hw0 : s(v, w₀) ∈ p.edges := (hmem w₀).mp hadj0
      have hw1 : s(v, w₁) ∈ p.edges := (hmem w₁).mp hadj1
      refine ⟨⟨s(v, w₀), p.edges_subset_edgeSet hw0⟩, ⟨s(v, w₁), p.edges_subset_edgeSet hw1⟩,
        hw0, hw1, Sym2.mem_iff.mpr (Or.inl rfl), Sym2.mem_iff.mpr (Or.inl rfl), ?_, ?_⟩
      · intro h
        exact hne (Sym2.congr_right.mp (congrArg Subtype.val h))
      · rintro ⟨e, he⟩ hmemF hve
        have hother : s(v, Sym2.Mem.other hve) = e := Sym2.other_spec hve
        have hadj : p.toSubgraph.Adj v (Sym2.Mem.other hve) := by
          rw [hmem]; rw [hother]; exact hmemF
        have hin : Sym2.Mem.other hve ∈ p.toSubgraph.neighborSet v := hadj
        rw [hset] at hin
        rcases hin with h | h
        · left
          apply Subtype.ext
          show e = s(v, w₀)
          rw [← hother, h]
        · right
          rw [Set.mem_singleton_iff] at h
          apply Subtype.ext
          show e = s(v, w₁)
          rw [← hother, h]
    · rintro S T ⟨hSne, hTne, hcover, hdisj⟩
      obtain ⟨u, huS⟩ := hSne
      obtain ⟨t, htT⟩ := hTne
      have htnS : t ∉ S := fun h => hdisj t h htT
      by_cases ha : a ∈ S
      · obtain ⟨d, hd, hfst, hsnd⟩ :=
          (p.takeUntil t (hp.mem_support t)).exists_boundary_dart S ha htnS
        have h1 : d ∈ p.darts := Walk.darts_takeUntil_subset _ _ hd
        have hedge : d.edge ∈ p.edges := List.mem_map.mpr ⟨d, h1, rfl⟩
        exact ⟨⟨d.edge, d.edge_mem⟩, hedge, d.fst, d.snd, hfst,
          (hcover d.snd).resolve_left hsnd, Sym2.mem_mk_left d.fst d.snd,
          Sym2.mem_mk_right d.fst d.snd⟩
      · have haT : a ∈ T := (hcover a).resolve_left ha
        obtain ⟨d, hd, hfst, hsnd⟩ :=
          (p.takeUntil u (hp.mem_support u)).exists_boundary_dart T haT (fun h => hdisj u huS h)
        have h1 : d ∈ p.darts := Walk.darts_takeUntil_subset _ _ hd
        have hedge : d.edge ∈ p.edges := List.mem_map.mpr ⟨d, h1, rfl⟩
        exact ⟨⟨d.edge, d.edge_mem⟩, hedge, d.snd, d.fst,
          (hcover d.snd).resolve_right hsnd, hfst, Sym2.mem_mk_right d.fst d.snd,
          Sym2.mem_mk_left d.fst d.snd⟩

/-- A vertex belongs to one of the listed color classes. -/
def IsInSomeColor (v : V) : List (Set V) -> Prop
  | [] => False
  | S :: Ss => v ∈ S ∨ IsInSomeColor v Ss

/-- The listed color classes cover all vertices. -/
def ColorClassesCover (colors : List (Set V)) : Prop :=
  ∀ v : V, IsInSomeColor v colors

/-- Two color classes are disjoint. -/
def ColorClassesDisjoint (S T : Set V) : Prop :=
  ∀ v : V, v ∈ S -> v ∈ T -> False

/-- One color class is disjoint from every class in the list. -/
def ColorClassDisjointFrom (S : Set V) : List (Set V) -> Prop
  | [] => True
  | T :: Ts => ColorClassesDisjoint S T ∧ ColorClassDisjointFrom S Ts

/-- The listed color classes are pairwise disjoint. -/
def ColorClassesPairwiseDisjoint : List (Set V) -> Prop
  | [] => True
  | S :: Ss => ColorClassDisjointFrom S Ss ∧ ColorClassesPairwiseDisjoint Ss

/-- Every listed color class is independent. -/
def ColorClassesIndependent (G : SimpleGraph V) : List (Set V) -> Prop
  | [] => True
  | S :: Ss => G.IsIndepSet S ∧ ColorClassesIndependent G Ss

/-- A coloring is a partition of the vertex set into independent color classes. -/
def IsColoringBySets (colors : List (Set V)) : Prop :=
  ColorClassesCover colors ∧
  ColorClassesPairwiseDisjoint colors ∧
  G.ColorClassesIndependent colors

/-- The graph has a coloring represented by exactly `k` color classes. -/
def HasColoringBySetsOfSize (k : Nat) : Prop :=
  ∃ colors : List (Set V), colors.length = k ∧ G.IsColoringBySets colors

/-- The graph is 3-colorable if it has three color classes forming a coloring. -/
def IsThreeColorableBySets : Prop :=
  ∃ S T U : Set V, G.IsColoringBySets [S, T, U]

/-- The graph has an edge with one endpoint in `S` and one endpoint in `T`. -/
def HasEdgeBetween (S T : Set V) : Prop :=
  ∃ e : G.edgeSet, ∃ u v : V,
    u ∈ S ∧ v ∈ T ∧ u ∈ (e : Sym2 V) ∧ v ∈ (e : Sym2 V)

/-- `A` and `B` form a nontrivial partition of `U`. -/
def IsPartitionOfSet (A B U : Set V) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧
    (∀ v : V, v ∈ A -> v ∈ U) ∧
    (∀ v : V, v ∈ B -> v ∈ U) ∧
    (∀ v : V, v ∈ U -> v ∈ A ∨ v ∈ B) ∧
    (∀ v : V, v ∈ A -> v ∈ B -> False)

/-- The induced subgraph on `U` is connected, phrased by cuts inside `U`. -/
def IsConnectedVertexSet (U : Set V) : Prop :=
  ∀ A B : Set V, IsPartitionOfSet A B U -> G.HasEdgeBetween A B

/-- Every listed branch set is nonempty and connected. -/
def BranchSetsConnected (G : SimpleGraph V) : List (Set V) -> Prop
  | [] => True
  | U :: Us => U.Nonempty ∧ G.IsConnectedVertexSet U ∧ BranchSetsConnected G Us

/-- Every listed pair of branch sets is adjacent by at least one graph edge. -/
def MinorEdgesRealized (G : SimpleGraph V) : List (Set V × Set V) -> Prop
  | [] => True
  | (S, T) :: pairs => G.HasEdgeBetween S T ∧ MinorEdgesRealized G pairs

/-- A minor model represented by branch sets and required adjacencies between them. -/
def IsMinorModelBySets (branchSets : List (Set V)) (edgePairs : List (Set V × Set V)) :
    Prop :=
  ColorClassesPairwiseDisjoint branchSets ∧
  G.BranchSetsConnected branchSets ∧
  G.MinorEdgesRealized edgePairs

/-- The graph has a `K_3` minor, represented by three branch sets. -/
def HasK3MinorBySets : Prop :=
  ∃ S T U : Set V, G.IsMinorModelBySets [S, T, U] [(S, T), (S, U), (T, U)]

theorem isInSomeColor_iff (v : V) (colors : List (Set V)) :
    IsInSomeColor v colors ↔ ∃ S ∈ colors, v ∈ S := by
  induction colors with
  | nil => simp [IsInSomeColor]
  | cons S Ss ih => simp [IsInSomeColor, ih]

theorem colorClassesIndependent_iff (colors : List (Set V)) :
    G.ColorClassesIndependent colors ↔ ∀ S ∈ colors, G.IsIndepSet S := by
  induction colors with
  | nil => simp [ColorClassesIndependent]
  | cons S Ss ih => simp [ColorClassesIndependent, ih]

theorem colorClassDisjointFrom_iff (S : Set V) (colors : List (Set V)) :
    ColorClassDisjointFrom S colors ↔ ∀ T ∈ colors, ColorClassesDisjoint S T := by
  induction colors with
  | nil => simp [ColorClassDisjointFrom]
  | cons T Ts ih => simp [ColorClassDisjointFrom, ih]

theorem colorClassesPairwiseDisjoint_iff (colors : List (Set V)) :
    ColorClassesPairwiseDisjoint colors ↔ colors.Pairwise ColorClassesDisjoint := by
  induction colors with
  | nil => simp [ColorClassesPairwiseDisjoint]
  | cons S Ss ih =>
    simp [ColorClassesPairwiseDisjoint, List.pairwise_cons, colorClassDisjointFrom_iff, ih]

/-- A vertex coloring represented by a list of `k` color classes (covering, pairwise
disjoint, each independent) is exactly mathlib's `Colorable k`. Empty color classes
correspond to unused colors. -/
theorem hasColoringBySetsOfSize_iff_colorable (k : ℕ) :
    G.HasColoringBySetsOfSize k ↔ G.Colorable k := by
  constructor
  · rintro ⟨colors, hlen, hcover, _, hind⟩
    classical
    subst hlen
    have cov : ∀ v, ∃ i : Fin colors.length, v ∈ colors.get i := by
      intro v
      obtain ⟨S, hS, hvS⟩ := (isInSomeColor_iff v colors).mp (hcover v)
      obtain ⟨i, hi⟩ := List.get_of_mem hS
      exact ⟨i, by rw [hi]; exact hvS⟩
    refine ⟨Coloring.mk (fun v => Classical.choose (cov v)) ?_⟩
    intro a b hab heq
    have ha := Classical.choose_spec (cov a)
    have hb := Classical.choose_spec (cov b)
    rw [show Classical.choose (cov a) = Classical.choose (cov b) from heq] at ha
    have hindi : G.IsIndepSet (colors.get (Classical.choose (cov b))) :=
      (colorClassesIndependent_iff G colors).mp hind _ (colors.get_mem _)
    exact (G.isIndepSet_iff.mp hindi) ha hb (G.ne_of_adj hab) hab
  · rintro ⟨C⟩
    refine ⟨(List.finRange k).map (fun i => {v | C v = i}), ?_, ?_, ?_, ?_⟩
    · simp
    · intro v
      rw [isInSomeColor_iff]
      exact ⟨{w | C w = C v}, List.mem_map.mpr ⟨C v, List.mem_finRange _, rfl⟩, rfl⟩
    · rw [colorClassesPairwiseDisjoint_iff, List.pairwise_map]
      refine (List.nodup_finRange k).imp ?_
      intro i j hij v hvi hvj
      have e1 : C v = i := hvi
      have e2 : C v = j := hvj
      exact hij (e1.symm.trans e2)
    · rw [colorClassesIndependent_iff]
      intro S hS
      rw [List.mem_map] at hS
      obtain ⟨i, _, rfl⟩ := hS
      rw [G.isIndepSet_iff]
      intro u hu w hw _ hadj
      exact C.valid hadj ((show C u = i from hu).trans (show C w = i from hw).symm)

/-- Three-colorability by sets coincides with mathlib's `Colorable 3`. -/
theorem isThreeColorableBySets_iff_colorable :
    G.IsThreeColorableBySets ↔ G.Colorable 3 := by
  rw [← hasColoringBySetsOfSize_iff_colorable]
  constructor
  · rintro ⟨S, T, U, h⟩
    exact ⟨[S, T, U], rfl, h⟩
  · rintro ⟨colors, hlen, h⟩
    obtain ⟨S, T, U, rfl⟩ := List.length_eq_three.mp hlen
    exact ⟨S, T, U, h⟩

end SimpleGraph

namespace GraphMSO

namespace Examples

open Formula
open Semantics

def x : FOVar := 0
def y : FOVar := 1
def z : FOVar := 2
def X : SOVar := 0
def Y : SOVar := 1
def Z : SOVar := 2
def P : SOVar := 3
def Q : SOVar := 4
def e0 : EdgeFOVar := 0
def e1 : EdgeFOVar := 1
def e2 : EdgeFOVar := 2
def E0 : EdgeSOVar := 0

/-- "The set variable `X` is nonempty." -/
def nonemptySet (X : SOVar) : Formula :=
  existsFO x (inSet x X)

/-- "The set variable `X` is a clique." -/
def clique (X : SOVar) : Formula :=
  forallFOs [x, y]
    (impl
      (conj (inSet x X) (conj (inSet y X) (notEqual x y)))
      (edge x y))

/-- "The set variable `X` is independent." -/
def independent (X : SOVar) : Formula :=
  forallFOs [x, y]
    (impl
      (conj (inSet x X) (conj (inSet y X) (edge x y)))
      (equal x y))

/-- "The set variable `X` is a dominating set." -/
def dominating (X : SOVar) : Formula :=
  forallFO x
    (disj
      (inSet x X)
      (existsFO y (conj (inSet y X) (edge y x))))

/-- "The set variables `X` and `Y` cover all vertices." -/
def coverAll (X Y : SOVar) : Formula :=
  forallFO x (disj (inSet x X) (inSet x Y))

/-- "The set variables `X` and `Y` are disjoint." -/
def disjointSets (X Y : SOVar) : Formula :=
  forallFO x (impl (inSet x X) (neg (inSet x Y)))

/-- "The set variable `X` is a subset of the set variable `Y`." -/
def subsetSet (X Y : SOVar) : Formula :=
  forallFO x (impl (inSet x X) (inSet x Y))

/-- "The set variables `X` and `Y` form a nontrivial partition of the vertices." -/
def nontrivialPartition (X Y : SOVar) : Formula :=
  conj (nonemptySet X)
    (conj (nonemptySet Y)
      (conj (coverAll X Y) (disjointSets X Y)))

/-- "There are no edges between the set variables `X` and `Y`." -/
def noEdgesBetween (X Y : SOVar) : Formula :=
  forallFOs [x, y] (impl (conj (inSet x X) (inSet y Y)) (neg (edge x y)))

/-- "The set variables `X` and `Y` have an edge between them." -/
def edgeBetween (X Y : SOVar) : Formula :=
  existsEdgeFO e0
    (existsFO x (existsFO y
      (conj (inSet x X)
        (conj (inSet y Y) (conj (inc x e0) (inc y e0))))))

/-- "`A` and `B` form a nontrivial partition of `U`." -/
def partitionOfSet (A B U : SOVar) : Formula :=
  conj (nonemptySet A)
    (conj (nonemptySet B)
      (conj (subsetSet A U)
        (conj (subsetSet B U)
          (conj (forallFO x (impl (inSet x U) (disj (inSet x A) (inSet x B))))
            (disjointSets A B)))))

/-- "The set variable `U` induces a connected subgraph."

The variables `A` and `B` are used as locally-bound partition variables, so callers
should choose them fresh from `U` and the surrounding free set variables. -/
def connectedVertexSetUsing (A B U : SOVar) : Formula :=
  forallSO A (forallSO B (impl (partitionOfSet A B U) (edgeBetween A B)))

/-- "The set variable `U` is a nonempty connected branch set." -/
def branchSetConnectedUsing (A B U : SOVar) : Formula :=
  conj (nonemptySet U) (connectedVertexSetUsing A B U)

/-- "Every listed set variable is a nonempty connected branch set." -/
def branchSetsConnectedUsing (A B : SOVar) : List SOVar -> Formula
  | [] => true_
  | U :: Us => conj (branchSetConnectedUsing A B U) (branchSetsConnectedUsing A B Us)

/-- "Every listed pair of set variables has an edge between the two sets." -/
def minorEdgeConstraints : List (SOVar × SOVar) -> Formula
  | [] => true_
  | (X, Y) :: pairs => conj (edgeBetween X Y) (minorEdgeConstraints pairs)

/-- "The graph is disconnected: there is a nontrivial partition with no crossing edges." -/
def disconnected : Formula :=
  existsSO X (existsSO Y (conj (nontrivialPartition X Y) (noEdgesBetween X Y)))

/-- "The graph is connected." -/
def connected : Formula :=
  neg disconnected

/-- "The vertex variable `v` belongs to one of the listed set variables." -/
def inSomeColor (v : FOVar) : List SOVar -> Formula
  | [] => false_
  | X :: Xs => disj (inSet v X) (inSomeColor v Xs)

/-- "The listed set variables cover all vertices." -/
def colorClassesCover (colors : List SOVar) : Formula :=
  forallFO x (inSomeColor x colors)

/-- "The set variable `X` is disjoint from every set variable in the list." -/
def colorClassDisjointFrom (X : SOVar) : List SOVar -> Formula
  | [] => true_
  | Y :: Ys => conj (disjointSets X Y) (colorClassDisjointFrom X Ys)

/-- "The listed set variables are pairwise disjoint." -/
def colorClassesPairwiseDisjoint : List SOVar -> Formula
  | [] => true_
  | X :: Xs => conj (colorClassDisjointFrom X Xs) (colorClassesPairwiseDisjoint Xs)

/-- "Every listed set variable is independent." -/
def colorClassesIndependent : List SOVar -> Formula
  | [] => true_
  | X :: Xs => conj (independent X) (colorClassesIndependent Xs)

/-- "The listed set variables form color classes: a partition into independent sets." -/
def coloring (colors : List SOVar) : Formula :=
  conj (colorClassesCover colors)
    (conj (colorClassesPairwiseDisjoint colors) (colorClassesIndependent colors))

/-- A finite MSO minor model formula.

`branchVars` are the branch-set variables. `edgePairs` records which pairs of
branch sets must be adjacent, i.e. the edges of the fixed pattern graph `H`.
The variables `A` and `B` are temporary partition variables used inside the
connectedness test, and should be fresh from `branchVars` and `edgePairs`. -/
def minorModelUsing (A B : SOVar) (branchVars : List SOVar)
    (edgePairs : List (SOVar × SOVar)) : Formula :=
  conj (colorClassesPairwiseDisjoint branchVars)
    (conj (branchSetsConnectedUsing A B branchVars) (minorEdgeConstraints edgePairs))

/-- Pair one item with every item in the list. -/
def pairsWith {α : Type} (a : α) : List α -> List (α × α)
  | [] => []
  | b :: bs => (a, b) :: pairsWith a bs

/-- All unordered pairs from a list, keeping the list order. -/
def completePairs {α : Type} : List α -> List (α × α)
  | [] => []
  | a :: as => pairsWith a as ++ completePairs as

/-- The closed MSO2 sentence saying that the graph has a `K_3` minor. -/
def k3Minor : Formula :=
  existsSO X (existsSO Y (existsSO Z
    (minorModelUsing P Q [X, Y, Z] [(X, Y), (X, Z), (Y, Z)])))

/-- A convenient open formula whose first `k` second-order variables are color classes. -/
def kColoring (k : Nat) : Formula :=
  coloring (List.range k)

/-- Existentially quantify a formula over a list of vertex-set variables. -/
def existsSOs : List SOVar -> Formula -> Formula
  | [], phi => phi
  | X :: Xs, phi => existsSO X (existsSOs Xs phi)

/-- Update a list of vertex-set variables by a list of concrete vertex sets. -/
def updateSOsByList {V E : Type} (rho : Assignment V E) : List SOVar -> List (Set V) ->
    Assignment V E
  | X :: Xs, S :: Ss => updateSOsByList (rho.updateSO X S) Xs Ss
  | _, _ => rho

/-- A closed finite-pattern minor sentence from explicit branch variables and
explicit required adjacencies. `A` and `B` must be fresh partition variables. -/
def minorSentenceUsing (A B : SOVar) (branchVars : List SOVar)
    (edgePairs : List (SOVar × SOVar)) : Formula :=
  existsSOs branchVars (minorModelUsing A B branchVars edgePairs)

/-- The open formula saying that the first `t` set variables form a `K_t` minor model. -/
def completeGraphMinorModel (t : Nat) : Formula :=
  minorModelUsing t (t + 1) (List.range t) (completePairs (List.range t))

/-- The closed MSO2 sentence saying that the graph has a `K_t` minor. -/
def completeGraphMinor (t : Nat) : Formula :=
  minorSentenceUsing t (t + 1) (List.range t) (completePairs (List.range t))

/-- A closed sentence saying that there exists a coloring using the first `k`
second-order variables as color classes. For each fixed `k`, this is one finite
MSO formula. -/
def kColorable (k : Nat) : Formula :=
  existsSOs (List.range k) (kColoring k)

/-- The closed sentence saying that the graph is 3-colorable. -/
def threeColorable : Formula :=
  existsSO X (existsSO Y (existsSO Z (coloring [X, Y, Z])))

theorem threeColorable_eq_kColorable_three :
    threeColorable = kColorable 3 := by
  rfl

theorem k3Minor_eq_completeGraphMinor_three :
    k3Minor = completeGraphMinor 3 := by
  rfl

/-- "There exists a nonempty clique." -/
def hasNonemptyClique : Formula :=
  existsSO X (conj (nonemptySet X) (clique X))

theorem satisfiesAt_clique_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    SatisfiesAt (clique X) G rho ↔ G.IsClique (rho.so X) := by
  simp [clique, SimpleGraph.IsClique, Set.Pairwise, Formula.forallFOs, Formula.notEqual,
    Semantics.SatisfiesAt, x, y, Assignment.updateFO, eq_comm]
  constructor
  · intro h u hu v hv hne
    exact h u v hu hv hne
  · intro h u v hu hv hne
    exact h hu hv hne

theorem satisfiesAt_independent_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    SatisfiesAt (independent X) G rho ↔ G.IsIndepSet (rho.so X) := by
  classical
  simp [independent, SimpleGraph.isIndepSet_iff, Set.Pairwise, Formula.forallFOs,
    Semantics.SatisfiesAt, x, y, Assignment.updateFO, eq_comm]
  constructor
  · intro h u hSu v hSv hne hAdj
    exact hne (h u v hSu hSv hAdj)
  · intro h u v hSu hSv hAdj
    by_contra hne
    exact h hSu hSv hne hAdj

theorem satisfiesAt_dominating_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    SatisfiesAt (dominating X) G rho ↔ G.IsDominating (rho.so X) := by
  simp [dominating, SimpleGraph.IsDominating, Semantics.SatisfiesAt, x, y, Assignment.updateFO]

theorem satisfiesAt_disconnected_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    SatisfiesAt disconnected G rho ↔ ¬ G.Preconnected := by
  rw [← G.isDisconnectedByPartition_iff_not_preconnected]
  simp [disconnected, nontrivialPartition, nonemptySet, coverAll, disjointSets, noEdgesBetween,
    SimpleGraph.IsDisconnectedByPartition, SimpleGraph.IsNontrivialPartition,
    SimpleGraph.HasNoEdgesBetween,
    Set.Nonempty, Formula.forallFOs, Semantics.SatisfiesAt, X, Y, x, y, Assignment.updateSO,
    Assignment.updateFO]

theorem satisfiesAt_connected_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    SatisfiesAt connected G rho ↔ G.Preconnected := by
  simpa [connected, Semantics.SatisfiesAt, not_not]
    using not_congr (satisfiesAt_disconnected_iff G rho)

theorem satisfiesAt_inSomeColor_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (v : FOVar) (colors : List SOVar) :
    SatisfiesAt (inSomeColor v colors) G rho ↔
      ∃ vertex : V, rho.fo v = some vertex ∧
        SimpleGraph.IsInSomeColor vertex (colors.map rho.so) := by
  induction colors with
  | nil =>
      simp [inSomeColor, SimpleGraph.IsInSomeColor, Semantics.SatisfiesAt]
  | cons X Xs ih =>
      simp [inSomeColor, SimpleGraph.IsInSomeColor, Semantics.SatisfiesAt, ih]
      constructor
      · rintro (hX | hXs)
        · rcases hX with ⟨vertex, hfo, hmem⟩
          exact ⟨vertex, hfo, Or.inl hmem⟩
        · rcases hXs with ⟨vertex, hfo, hmem⟩
          exact ⟨vertex, hfo, Or.inr hmem⟩
      · rintro ⟨vertex, hfo, hmem | hmem⟩
        · exact Or.inl ⟨vertex, hfo, hmem⟩
        · exact Or.inr ⟨vertex, hfo, hmem⟩

theorem satisfiesAt_colorClassesCover_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (colors : List SOVar) :
    SatisfiesAt (colorClassesCover colors) G rho ↔
      SimpleGraph.ColorClassesCover (colors.map rho.so) := by
  simp [colorClassesCover, SimpleGraph.ColorClassesCover, Semantics.SatisfiesAt,
    satisfiesAt_inSomeColor_iff, x, Assignment.updateFO]

theorem satisfiesAt_disjointSets_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X Y : SOVar) :
    SatisfiesAt (disjointSets X Y) G rho ↔
      SimpleGraph.ColorClassesDisjoint (rho.so X) (rho.so Y) := by
  simp [disjointSets, SimpleGraph.ColorClassesDisjoint, Semantics.SatisfiesAt, x,
    Assignment.updateFO]

theorem satisfiesAt_colorClassDisjointFrom_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) (colors : List SOVar) :
    SatisfiesAt (colorClassDisjointFrom X colors) G rho ↔
      SimpleGraph.ColorClassDisjointFrom (rho.so X) (colors.map rho.so) := by
  induction colors with
  | nil =>
      simp [colorClassDisjointFrom, SimpleGraph.ColorClassDisjointFrom, Formula.true_,
        Semantics.SatisfiesAt]
  | cons Y Ys ih =>
      simp [colorClassDisjointFrom, SimpleGraph.ColorClassDisjointFrom,
        satisfiesAt_disjointSets_iff, ih]

theorem satisfiesAt_colorClassesPairwiseDisjoint_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (colors : List SOVar) :
    SatisfiesAt (colorClassesPairwiseDisjoint colors) G rho ↔
      SimpleGraph.ColorClassesPairwiseDisjoint (colors.map rho.so) := by
  induction colors with
  | nil =>
      simp [colorClassesPairwiseDisjoint, SimpleGraph.ColorClassesPairwiseDisjoint,
        Formula.true_, Semantics.SatisfiesAt]
  | cons X Xs ih =>
      simp [colorClassesPairwiseDisjoint, SimpleGraph.ColorClassesPairwiseDisjoint,
        satisfiesAt_colorClassDisjointFrom_iff, ih]

theorem satisfiesAt_colorClassesIndependent_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (colors : List SOVar) :
    SatisfiesAt (colorClassesIndependent colors) G rho ↔
      G.ColorClassesIndependent (colors.map rho.so) := by
  induction colors with
  | nil =>
      simp [colorClassesIndependent, SimpleGraph.ColorClassesIndependent, Formula.true_,
        Semantics.SatisfiesAt]
  | cons X Xs ih =>
      simp [colorClassesIndependent, SimpleGraph.ColorClassesIndependent,
        satisfiesAt_independent_iff, ih]

theorem satisfiesAt_coloring_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (colors : List SOVar) :
    SatisfiesAt (coloring colors) G rho ↔
      G.IsColoringBySets (colors.map rho.so) := by
  simp [coloring, SimpleGraph.IsColoringBySets, Semantics.SatisfiesAt,
    satisfiesAt_colorClassesCover_iff, satisfiesAt_colorClassesPairwiseDisjoint_iff,
    satisfiesAt_colorClassesIndependent_iff]

theorem satisfiesAt_kColoring_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (k : Nat) :
    SatisfiesAt (kColoring k) G rho ↔
      G.IsColoringBySets ((List.range k).map rho.so) := by
  simp [kColoring, satisfiesAt_coloring_iff]

theorem updateSOsByList_so_of_not_mem {V E : Type} (rho : Assignment V E)
    {X : SOVar} :
    ∀ (vars : List SOVar) (sets : List (Set V)), X ∉ vars ->
      (updateSOsByList rho vars sets).so X = rho.so X := by
  intro vars
  induction vars generalizing rho with
  | nil =>
      intro sets _
      cases sets <;> simp [updateSOsByList]
  | cons Y Ys ih =>
      intro sets hnot
      cases sets with
      | nil =>
          simp [updateSOsByList]
      | cons S Ss =>
          have hXY : X ≠ Y := by
            intro hXY
            exact hnot (by simp [hXY])
          have hnot_tail : X ∉ Ys := by
            intro hmem
            exact hnot (by simp [hmem])
          calc
            (updateSOsByList (rho.updateSO Y S) Ys Ss).so X =
                (rho.updateSO Y S).so X := ih (rho.updateSO Y S) Ss hnot_tail
            _ = rho.so X := by simp [Assignment.updateSO, hXY]

theorem map_updateSOsByList_eq {V E : Type} (rho : Assignment V E) :
    ∀ (vars : List SOVar) (sets : List (Set V)), vars.Nodup ->
      sets.length = vars.length ->
      vars.map (fun X => (updateSOsByList rho vars sets).so X) = sets := by
  intro vars
  induction vars generalizing rho with
  | nil =>
      intro sets _ hlen
      cases sets with
      | nil =>
          simp [updateSOsByList]
      | cons S Ss =>
          simp at hlen
  | cons X Xs ih =>
      intro sets hnodup hlen
      cases hnodup with
      | cons hXnot hXsNodup =>
          cases sets with
          | nil =>
              simp at hlen
          | cons S Ss =>
              have hXnot_mem : X ∉ Xs := by
                intro hmem
                exact hXnot X hmem rfl
              have hlen_tail : Ss.length = Xs.length := by
                simpa using hlen
              have hhead :
                  (updateSOsByList (rho.updateSO X S) Xs Ss).so X = S := by
                rw [updateSOsByList_so_of_not_mem (rho.updateSO X S) Xs Ss hXnot_mem]
                simp
              have htail :
                  Xs.map (fun Y => (updateSOsByList (rho.updateSO X S) Xs Ss).so Y) = Ss :=
                ih (rho.updateSO X S) Ss hXsNodup hlen_tail
              simp [updateSOsByList, hhead, htail]

theorem satisfiesAt_existsSOs_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (vars : List SOVar) (phi : Formula) :
    SatisfiesAt (existsSOs vars phi) G rho ↔
      ∃ sets : List (Set V), sets.length = vars.length ∧
        SatisfiesAt phi G (updateSOsByList rho vars sets) := by
  induction vars generalizing rho with
  | nil =>
      constructor
      · intro h
        exact ⟨[], rfl, by simpa [existsSOs, updateSOsByList] using h⟩
      · rintro ⟨sets, hlen, hEval⟩
        cases sets with
        | nil =>
            simpa [existsSOs, updateSOsByList] using hEval
        | cons S Ss =>
            simp at hlen
  | cons X Xs ih =>
      constructor
      · intro h
        rcases (by
          simpa [existsSOs, Semantics.SatisfiesAt] using h :
            ∃ S : Set V, SatisfiesAt (existsSOs Xs phi) G (rho.updateSO X S)) with
          ⟨S, hS⟩
        rcases (ih (rho.updateSO X S)).mp hS with ⟨Ss, hlen, hEval⟩
        exact ⟨S :: Ss, by simp [hlen], by simpa [updateSOsByList] using hEval⟩
      · rintro ⟨sets, hlen, hEval⟩
        cases sets with
        | nil =>
            simp at hlen
        | cons S Ss =>
            have hlen_tail : Ss.length = Xs.length := by
              simpa using hlen
            simp [existsSOs, Semantics.SatisfiesAt]
            refine ⟨S, ?_⟩
            apply (ih (rho.updateSO X S)).mpr
            exact ⟨Ss, hlen_tail, by simpa [updateSOsByList] using hEval⟩

theorem satisfiesAt_kColorable_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (k : Nat) :
    SatisfiesAt (kColorable k) G rho ↔ G.Colorable k := by
  rw [← G.hasColoringBySetsOfSize_iff_colorable, kColorable, satisfiesAt_existsSOs_iff]
  constructor
  · rintro ⟨sets, hlen, hEval⟩
    have hmap :
        (List.range k).map
            (fun X => (updateSOsByList rho (List.range k) sets).so X) = sets :=
      map_updateSOsByList_eq rho (List.range k) sets List.nodup_range hlen
    have hcolor : G.IsColoringBySets sets := by
      have h := (satisfiesAt_kColoring_iff G (updateSOsByList rho (List.range k) sets) k).mp hEval
      simpa [hmap] using h
    exact ⟨sets, by simpa using hlen, hcolor⟩
  · rintro ⟨sets, hlen, hcolor⟩
    refine ⟨sets, by simpa using hlen, ?_⟩
    have hlen_range : sets.length = (List.range k).length := by
      simpa using hlen
    have hmap :
        (List.range k).map
            (fun X => (updateSOsByList rho (List.range k) sets).so X) = sets :=
      map_updateSOsByList_eq rho (List.range k) sets List.nodup_range hlen_range
    apply (satisfiesAt_kColoring_iff G (updateSOsByList rho (List.range k) sets) k).mpr
    simpa [hmap] using hcolor

theorem satisfiesAt_threeColorable_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    SatisfiesAt threeColorable G rho ↔ G.Colorable 3 := by
  rw [← G.isThreeColorableBySets_iff_colorable]
  simp [threeColorable, SimpleGraph.IsThreeColorableBySets, Semantics.SatisfiesAt,
    satisfiesAt_coloring_iff, X, Y, Z, Assignment.updateSO]

theorem satisfiesAt_kColorable_three_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    SatisfiesAt (kColorable 3) G rho ↔ G.Colorable 3 := by
  simpa [← threeColorable_eq_kColorable_three] using satisfiesAt_threeColorable_iff G rho

theorem satisfiesAt_edgeBetween_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X Y : SOVar) :
    SatisfiesAt (edgeBetween X Y) G rho ↔
      G.HasEdgeBetween (rho.so X) (rho.so Y) := by
  simp [edgeBetween, SimpleGraph.HasEdgeBetween, Semantics.SatisfiesAt, e0, x, y,
    Assignment.updateEdgeFO, Assignment.updateFO]

theorem satisfiesAt_partitionOfSet_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (A B U : SOVar) :
    SatisfiesAt (partitionOfSet A B U) G rho ↔
      SimpleGraph.IsPartitionOfSet (rho.so A) (rho.so B) (rho.so U) := by
  simp [partitionOfSet, nonemptySet, subsetSet, disjointSets,
    SimpleGraph.IsPartitionOfSet, Set.Nonempty, Semantics.SatisfiesAt, x,
    Assignment.updateFO]

theorem satisfiesAt_connectedVertexSetUsing_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (A B U : SOVar)
    (hAB : A ≠ B) (hAU : A ≠ U) (hBU : B ≠ U) :
    SatisfiesAt (connectedVertexSetUsing A B U) G rho ↔
      G.IsConnectedVertexSet (rho.so U) := by
  simp [connectedVertexSetUsing, SimpleGraph.IsConnectedVertexSet, Semantics.SatisfiesAt,
    Assignment.updateSO, hAB, hAU.symm, hBU.symm,
    satisfiesAt_partitionOfSet_iff, satisfiesAt_edgeBetween_iff]

theorem satisfiesAt_branchSetConnectedUsing_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (A B U : SOVar)
    (hAB : A ≠ B) (hAU : A ≠ U) (hBU : B ≠ U) :
    SatisfiesAt (branchSetConnectedUsing A B U) G rho ↔
      (rho.so U).Nonempty ∧ G.IsConnectedVertexSet (rho.so U) := by
  simp [branchSetConnectedUsing, nonemptySet, Semantics.SatisfiesAt, Set.Nonempty,
    satisfiesAt_connectedVertexSetUsing_iff, hAB, hAU, hBU, x, Assignment.updateFO]

theorem satisfiesAt_minorEdgeConstraints_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (edgePairs : List (SOVar × SOVar)) :
    SatisfiesAt (minorEdgeConstraints edgePairs) G rho ↔
      G.MinorEdgesRealized (edgePairs.map (fun p => (rho.so p.1, rho.so p.2))) := by
  induction edgePairs with
  | nil =>
      simp [minorEdgeConstraints, SimpleGraph.MinorEdgesRealized, Formula.true_,
        Semantics.SatisfiesAt]
  | cons p pairs ih =>
      cases p with
      | mk X Y =>
          simp [minorEdgeConstraints, SimpleGraph.MinorEdgesRealized, satisfiesAt_edgeBetween_iff, ih]

theorem satisfiesAt_k3Minor_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    SatisfiesAt k3Minor G rho ↔ G.HasK3MinorBySets := by
  simp [k3Minor, minorModelUsing, branchSetsConnectedUsing,
    SimpleGraph.HasK3MinorBySets, SimpleGraph.IsMinorModelBySets,
    SimpleGraph.BranchSetsConnected, Formula.true_, Semantics.SatisfiesAt, X, Y, Z, P, Q,
    Assignment.updateSO, satisfiesAt_colorClassesPairwiseDisjoint_iff,
    satisfiesAt_branchSetConnectedUsing_iff, satisfiesAt_minorEdgeConstraints_iff]
  constructor
  · rintro ⟨S, T, U, hdisj, ⟨⟨hSnon, hSconn⟩, ⟨hTnon, hTconn⟩, hUnon, hUconn⟩, hedges⟩
    exact ⟨S, T, U, hdisj, ⟨hSnon, hSconn, hTnon, hTconn, hUnon, hUconn⟩, hedges⟩
  · rintro ⟨S, T, U, hdisj, ⟨hSnon, hSconn, hTnon, hTconn, hUnon, hUconn⟩, hedges⟩
    exact ⟨S, T, U, hdisj, ⟨⟨hSnon, hSconn⟩, ⟨hTnon, hTconn⟩, hUnon, hUconn⟩, hedges⟩

theorem satisfiesAt_completeGraphMinor_three_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    SatisfiesAt (completeGraphMinor 3) G rho ↔ G.HasK3MinorBySets := by
  simpa [← k3Minor_eq_completeGraphMinor_three] using satisfiesAt_k3Minor_iff G rho

theorem clique_no_freeFO (X : SOVar) (a : FOVar) :
    Not (Formula.FreeFO (clique X) a) := by
  simp [clique, Formula.forallFOs, Formula.FreeFO, Formula.notEqual, x, y]
  intro h0 h1
  exact ⟨⟨h0, h1, h0, h1⟩, h0, h1⟩

theorem clique_freeSO_iff (X Y : SOVar) :
    Formula.FreeSO (clique X) Y ↔ Y = X := by
  simp [clique, Formula.forallFOs, Formula.FreeSO, Formula.notEqual, x, y]

theorem hasNonemptyClique_closed : Formula.Closed hasNonemptyClique := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    simp [hasNonemptyClique, nonemptySet, clique, Formula.forallFOs, Formula.FreeFO,
      Formula.notEqual, x, y, X]
    intro h0 h1
    exact ⟨⟨h0, h1, h0, h1⟩, h0, h1⟩
  · intro Z
    simp [hasNonemptyClique, nonemptySet, clique, Formula.forallFOs, Formula.FreeSO,
      Formula.notEqual, x, y, X]
  · intro e
    simp [hasNonemptyClique, nonemptySet, clique, Formula.forallFOs, Formula.FreeEdgeFO,
      Formula.notEqual, x, y, X]
  · intro E_var
    simp [hasNonemptyClique, nonemptySet, clique, Formula.forallFOs, Formula.FreeEdgeSO,
      Formula.notEqual, x, y, X]

/-- "The edge `e` is incident to exactly one vertex." In a `SimpleGraph.edgeSet`,
this formula is unsatisfiable, but it remains useful as MSO2 syntax. -/
def isLoop (e : EdgeFOVar) : Formula :=
  existsFO y (conj (inc y e) (forallFO z (impl (inc z e) (equal z y))))

/-- "There is a unique edge in `M` incident to vertex variable `v`." -/
def uniqueIncEdgeIn (v : FOVar) (M : EdgeSOVar) : Formula :=
  existsEdgeFO e0 (conj (inEdgeSet e0 M) (conj (inc v e0)
    (forallEdgeFO e1 (impl (conj (inEdgeSet e1 M) (inc v e1)) (equalEdge e1 e0)))))

/-- "The edge set variable `M` is a perfect matching." -/
def perfectMatching (M : EdgeSOVar) : Formula :=
  conj (forallEdgeFO e0 (impl (inEdgeSet e0 M) (neg (isLoop e0))))
       (forallFO x (uniqueIncEdgeIn x M))

theorem edgeSet_not_singleton_incident {V : Type} (G : SimpleGraph V)
    (edge : G.edgeSet) :
    ¬ ∃ v : V, v ∈ (edge : Sym2 V) ∧
      ∀ w : V, w ∈ (edge : Sym2 V) -> w = v := by
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.ind with
  | _ a b =>
      intro h
      rcases h with ⟨v, _, hall⟩
      have ha : a = v := hall a (by simp)
      have hb : b = v := hall b (by simp)
      have hab : a = b := ha.trans hb.symm
      have hadj : G.Adj a b := by
        simpa using (SimpleGraph.mem_edgeSet (G := G) (v := a) (w := b)).mp hedge
      exact (G.ne_of_adj hadj) hab

theorem satisfiesAt_isLoop_false {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (e : EdgeFOVar) :
    ¬ SatisfiesAt (isLoop e) G rho := by
  cases hedge : rho.efo e with
  | none =>
      simp [isLoop, Semantics.SatisfiesAt, hedge, y, z, Assignment.updateFO]
  | some edge =>
      rw [show SatisfiesAt (isLoop e) G rho ↔
          ∃ v : V, v ∈ (edge : Sym2 V) ∧
            ∀ w : V, w ∈ (edge : Sym2 V) -> v = w by
        simp [isLoop, Semantics.SatisfiesAt, hedge, y, z, Assignment.updateFO]]
      intro h
      apply edgeSet_not_singleton_incident G edge
      rcases h with ⟨v, hv, hall⟩
      exact ⟨v, hv, fun w hw => (hall w hw).symm⟩

theorem satisfiesAt_uniqueIncEdgeIn_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (v : FOVar) (M : EdgeSOVar) {vertex : V}
    (hfo : rho.fo v = some vertex) :
    SatisfiesAt (uniqueIncEdgeIn v M) G rho ↔
      ∃ e : G.edgeSet, e ∈ rho.eso M ∧ vertex ∈ (e : Sym2 V) ∧
        ∀ e' : G.edgeSet, e' ∈ rho.eso M -> vertex ∈ (e' : Sym2 V) -> e = e' := by
  simp [uniqueIncEdgeIn, Semantics.SatisfiesAt, e0, e1, Assignment.updateEdgeFO,
    hfo, Subtype.ext_iff]

theorem satisfiesAt_perfectMatching_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (M : EdgeSOVar) :
    SatisfiesAt (perfectMatching M) G rho ↔
      (G.spanningSubgraphOfEdges (rho.eso M)).IsPerfectMatching := by
  rw [SimpleGraph.isPerfectMatching_spanningSubgraphOfEdges_iff]
  simp [perfectMatching, Semantics.SatisfiesAt,
    satisfiesAt_isLoop_false, x, e0, Assignment.updateFO, Assignment.updateEdgeFO]
  constructor
  · intro h vertex
    rcases (satisfiesAt_uniqueIncEdgeIn_iff G (rho.updateFO x vertex) x M (vertex := vertex) (by simp)).mp (h vertex) with
      ⟨edge, hedge_mem, hvertex_mem, huniq⟩
    exact ⟨edge, ⟨hedge_mem, hvertex_mem⟩,
      fun edge' hedge' => (huniq edge' hedge'.1 hedge'.2).symm⟩
  · intro h vertex
    rcases h vertex with ⟨edge, ⟨hedge_mem, hvertex_mem⟩, huniq⟩
    exact (satisfiesAt_uniqueIncEdgeIn_iff G (rho.updateFO x vertex) x M (vertex := vertex) (by simp)).mpr
      ⟨edge, hedge_mem, hvertex_mem, fun edge' hedge'_mem hvertex'_mem =>
        (huniq edge' ⟨hedge'_mem, hvertex'_mem⟩).symm⟩

/-- "Exactly two edges in `M` are incident to vertex variable `v`." -/
def exactlyTwoIncEdgesIn (v : FOVar) (M : EdgeSOVar) : Formula :=
  existsEdgeFO e0
    (existsEdgeFO e1
      (conj (inEdgeSet e0 M)
        (conj (inEdgeSet e1 M)
          (conj (inc v e0)
            (conj (inc v e1)
              (conj (neg (equalEdge e0 e1))
                (forallEdgeFO e2
                  (impl (conj (inEdgeSet e2 M) (inc v e2))
                    (disj (equalEdge e2 e0) (equalEdge e2 e1))))))))))

/-- "Every vertex has exactly two incident edges in `M`." -/
def everyVertexExactlyTwoIncEdgesIn (M : EdgeSOVar) : Formula :=
  forallFO x (exactlyTwoIncEdgesIn x M)

/-- "Some selected edge in `M` crosses from vertex set `X` to vertex set `Y`." -/
def crossingEdgeIn (M : EdgeSOVar) (X Y : SOVar) : Formula :=
  existsEdgeFO e0
    (conj (inEdgeSet e0 M)
      (existsFO x (existsFO y
        (conj (inSet x X)
          (conj (inSet y Y) (conj (inc x e0) (inc y e0)))))))

/-- "The selected edge set `M` is connected as a spanning subgraph." -/
def edgeSetConnected (M : EdgeSOVar) : Formula :=
  forallSO X (forallSO Y
    (impl (nontrivialPartition X Y) (crossingEdgeIn M X Y)))

/-- "The graph has a Hamiltonian cycle, represented by its selected edge set." -/
def hamiltonian : Formula :=
  existsEdgeSO E0
    (conj (everyVertexExactlyTwoIncEdgesIn E0) (edgeSetConnected E0))

theorem satisfiesAt_exactlyTwoIncEdgesIn_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (v : FOVar) (M : EdgeSOVar) {vertex : V}
    (hfo : rho.fo v = some vertex) :
    SatisfiesAt (exactlyTwoIncEdgesIn v M) G rho ↔
      ∃ e₀ e₁ : G.edgeSet,
        e₀ ∈ rho.eso M ∧ e₁ ∈ rho.eso M ∧
        vertex ∈ (e₀ : Sym2 V) ∧ vertex ∈ (e₁ : Sym2 V) ∧ e₀ ≠ e₁ ∧
        ∀ e : G.edgeSet, e ∈ rho.eso M -> vertex ∈ (e : Sym2 V) -> e₀ = e ∨ e₁ = e := by
  simp [exactlyTwoIncEdgesIn, Semantics.SatisfiesAt, e0, e1, e2,
    Assignment.updateEdgeFO, hfo, Subtype.ext_iff]
  constructor
  · rintro ⟨edge0, hedge0_mem, edge1, hedge1_mem, hvertex0, hvertex1, hne, huniq⟩
    exact ⟨edge0, hedge0_mem, edge1, hedge1_mem, hvertex0, hvertex1,
      fun h => hne h.symm, huniq⟩
  · rintro ⟨edge0, hedge0_mem, edge1, hedge1_mem, hvertex0, hvertex1, hne, huniq⟩
    exact ⟨edge0, hedge0_mem, edge1, hedge1_mem, hvertex0, hvertex1,
      fun h => hne h.symm, huniq⟩

theorem satisfiesAt_everyVertexExactlyTwoIncEdgesIn_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (M : EdgeSOVar) :
    SatisfiesAt (everyVertexExactlyTwoIncEdgesIn M) G rho ↔
      ∀ v : V, G.HasExactlyTwoIncidentEdgesIn (rho.eso M) v := by
  simp [everyVertexExactlyTwoIncEdgesIn, Semantics.SatisfiesAt, x, Assignment.updateFO]
  constructor
  · intro h vertex
    rcases (satisfiesAt_exactlyTwoIncEdgesIn_iff G (rho.updateFO x vertex) x M (vertex := vertex) (by simp)).mp
        (h vertex) with
      ⟨edge0, edge1, hedge0_mem, hedge1_mem, hvertex0, hvertex1, hne, huniq⟩
    exact ⟨edge0, edge1, hedge0_mem, hedge1_mem, hvertex0, hvertex1, hne,
      fun edge hedge_mem hvertex =>
        (huniq edge hedge_mem hvertex).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
  · intro h vertex
    rcases h vertex with ⟨edge0, edge1, hedge0_mem, hedge1_mem, hvertex0, hvertex1, hne, huniq⟩
    exact (satisfiesAt_exactlyTwoIncEdgesIn_iff G (rho.updateFO x vertex) x M (vertex := vertex) (by simp)).mpr
      ⟨edge0, edge1, hedge0_mem, hedge1_mem, hvertex0, hvertex1, hne,
        fun edge hedge_mem hvertex =>
          (huniq edge hedge_mem hvertex).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩

theorem satisfiesAt_crossingEdgeIn_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (M : EdgeSOVar) (X Y : SOVar) :
    SatisfiesAt (crossingEdgeIn M X Y) G rho ↔
      G.HasCrossingEdgeIn (rho.eso M) (rho.so X) (rho.so Y) := by
  simp [crossingEdgeIn, SimpleGraph.HasCrossingEdgeIn, Semantics.SatisfiesAt, e0, x, y,
    Assignment.updateEdgeFO, Assignment.updateFO]

theorem satisfiesAt_edgeSetConnected_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (M : EdgeSOVar) :
    SatisfiesAt (edgeSetConnected M) G rho ↔
      G.EdgeSetConnectedSpanning (rho.eso M) := by
  simp [edgeSetConnected, nontrivialPartition, nonemptySet, coverAll, disjointSets,
    SimpleGraph.EdgeSetConnectedSpanning, SimpleGraph.IsNontrivialPartition, Set.Nonempty,
    Semantics.SatisfiesAt, X, Y, x, Assignment.updateSO, Assignment.updateFO,
    satisfiesAt_crossingEdgeIn_iff]

theorem satisfiesAt_hamiltonian_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    SatisfiesAt hamiltonian G rho ↔ G.HasHamiltonianCycleByEdges := by
  simp [hamiltonian, SimpleGraph.HasHamiltonianCycleByEdges, Semantics.SatisfiesAt, E0,
    Assignment.updateEdgeSO, satisfiesAt_everyVertexExactlyTwoIncEdgesIn_iff,
    satisfiesAt_edgeSetConnected_iff]

/-- For a nonempty finite graph, the MSO2 Hamiltonian-cycle sentence holds exactly when the
graph admits a mathlib `Walk.IsHamiltonianCycle`. -/
theorem satisfiesAt_hamiltonian_iff_isHamiltonianCycle {V : Type} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Nonempty V] (rho : Assignment V G.edgeSet) :
    SatisfiesAt hamiltonian G rho ↔ ∃ a, ∃ p : G.Walk a a, p.IsHamiltonianCycle :=
  (satisfiesAt_hamiltonian_iff G rho).trans G.hasHamiltonianCycleByEdges_iff

def vertexCover (X : SOVar) : Formula :=
  forallEdgeFO e0 (existsFO x (conj (inSet x X) (inc x e0)))

theorem satisfiesAt_vertexCover_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    SatisfiesAt (vertexCover X) G rho ↔ G.IsVertexCover (rho.so X) := by
  rw [G.isVertexCover_iff_forall_edge]
  simp [vertexCover, Semantics.SatisfiesAt, x, e0, Assignment.updateFO, Assignment.updateEdgeFO]

def bipartite : Formula :=
  existsSO X (forallEdgeFO e0 (existsFO x (existsFO y
    (conj (inSet x X) (conj (neg (inSet y X)) (conj (inc x e0) (inc y e0)))))))

theorem satisfiesAt_bipartite_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    SatisfiesAt bipartite G rho ↔ G.IsBipartite := by
  rw [G.isBipartite_iff_forall_edge]
  simp [bipartite, Semantics.SatisfiesAt, X, e0, x, y,
    Assignment.updateSO, Assignment.updateFO, Assignment.updateEdgeFO]

/-- A two-vertex type for smoke-test examples. -/
inductive Two where
  | left : Two
  | right : Two
  deriving Repr, DecidableEq

def twoGraph : SimpleGraph Two :=
  ⊤

def twoEdge : twoGraph.edgeSet :=
  ⟨s(Two.left, Two.right), by simp [twoGraph]⟩

def allTrueAssignment : Assignment Two twoGraph.edgeSet where
  fo := fun _ => some Two.left
  so := fun _ => Set.univ
  efo := fun _ => some twoEdge
  eso := fun _ => Set.univ

example : SatisfiesAt Formula.true_ twoGraph allTrueAssignment := by
  exact satisfiesAt_true twoGraph allTrueAssignment

example : SatisfiesAt (forallFO x (inSet x X)) twoGraph allTrueAssignment := by
  simp [Semantics.SatisfiesAt, allTrueAssignment, x, X]

end Examples

end GraphMSO
