import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Pendant extensions of graphs

`SimpleGraph.pendantExtension G attach` extends a graph `G` on `α` by one new
pendant vertex for every element of an index type `β`, each attached by a
single edge to the vertex chosen by `attach`.  The incidence-graph
tree-decomposition of the Courcelle development attaches one leaf bag per
edge to a decomposition tree, so preservation of treeness under pendant
extension is exactly the tree surgery it needs.

Main results:

* `Walk.induceLift` — a walk whose support stays inside `s` lifts to the
  induced subgraph on `s`; mapping back along the inclusion recovers the
  original walk, so cycles lift to cycles.
* `Walk.IsCycle.not_mem_support_of_forall_adj_eq` — a vertex with at most one
  neighbor lies on no cycle.
* `pendantExtension_isTree` — pendant extensions of trees are trees.
-/

namespace SimpleGraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## Walks into induced subgraphs -/

namespace Walk

variable {G : SimpleGraph α} {s : Set α}

/-- Lift a walk whose support stays inside `s` to the induced subgraph on
`s`. -/
def induceLift :
    ∀ {u v : α} (p : G.Walk u v), (∀ z ∈ p.support, z ∈ s) ->
      ∀ (hu : u ∈ s) (hv : v ∈ s), (G.induce s).Walk ⟨u, hu⟩ ⟨v, hv⟩
  | _, _, .nil, _, _, _ => .nil
  | _, _, @Walk.cons _ _ u m _ h q, hp, hu, hv =>
      Walk.cons
        (show (G.induce s).Adj ⟨u, hu⟩ ⟨m, hp m (by simp)⟩ from h)
        (q.induceLift (fun z hz => hp z (by simp [hz])) (hp m (by simp)) hv)

/-- Mapping a lifted walk back along the inclusion recovers the original
walk. -/
@[simp] theorem induceLift_map_induceHom {u v : α} (p : G.Walk u v)
    (hp : ∀ z ∈ p.support, z ∈ s) (hu : u ∈ s) (hv : v ∈ s) :
    (p.induceLift hp hu hv).map (Embedding.induce s).toHom = p := by
  induction p with
  | nil => rfl
  | cons h q ih =>
      show Walk.cons _ ((q.induceLift _ _ _).map _) = _
      rw [ih]

/-- A closed walk whose support stays inside `s` is a cycle iff its lift to
the induced subgraph is a cycle. -/
theorem isCycle_induceLift_iff {u : α} (c : G.Walk u u)
    (hc : ∀ z ∈ c.support, z ∈ s) (hu : u ∈ s) :
    (c.induceLift hc hu hu).IsCycle ↔ c.IsCycle := by
  have h := Walk.map_isCycle_iff_of_injective
    (p := c.induceLift hc hu hu) (f := (Embedding.induce (G := G) s).toHom)
    (Embedding.induce (G := G) s).injective
  rw [induceLift_map_induceHom] at h
  exact h.symm

/-! ## Vertices with at most one neighbor avoid cycles -/

/-- A vertex with at most one neighbor lies on no cycle: a cycle through it
would use its unique incident edge twice. -/
theorem IsCycle.not_mem_support_of_forall_adj_eq {G : SimpleGraph α} {w : α}
    (hw : ∀ y z : α, G.Adj w y -> G.Adj w z -> y = z)
    {x : α} {c : G.Walk x x} (hc : c.IsCycle) :
    w ∉ c.support := by
  classical
  intro hmem
  have hc' : (c.rotate hmem).IsCycle := hc.rotate hmem
  have hnn : ¬(c.rotate hmem).Nil := by
    intro hnil
    exact hc'.ne_nil (Walk.nil_iff_eq_nil.mp hnil)
  obtain ⟨y, hadj, p, heq⟩ := Walk.not_nil_iff.mp hnn
  rw [heq] at hc'
  have hyw : y ≠ w := by
    intro h
    subst h
    exact G.loopless y hadj
  have hpn : ¬p.Nil := Walk.not_nil_of_ne hyw
  have hlast : s(p.penultimate, w) ∈ p.edges :=
    Walk.mk_penultimate_end_mem_edges hpn
  have hpen : p.penultimate = y :=
    hw p.penultimate y (Walk.adj_penultimate hpn).symm hadj
  have hnotmem : s(w, y) ∉ p.edges := ((Walk.cons_isCycle_iff p hadj).mp hc').2
  rw [hpen, Sym2.eq_swap] at hlast
  exact hnotmem hlast

end Walk

/-! ## Main definition: pendantExtension -/

/--
The pendant extension of `G` by an `β`-indexed family of new leaves: each new
vertex `Sum.inr e` is adjacent exactly to `Sum.inl (attach e)`, and the old
vertices keep the adjacency of `G`.
-/
def pendantExtension (G : SimpleGraph α) (attach : β → α) :
    SimpleGraph (α ⊕ β) where
  Adj x y :=
    match x, y with
    | .inl a, .inl b => G.Adj a b
    | .inl a, .inr e => a = attach e
    | .inr e, .inl a => a = attach e
    | .inr _, .inr _ => False
  symm := by
    rintro (a | e) (b | f) h
    · exact G.symm h
    · exact h
    · exact h
    · exact h.elim
  loopless := by
    rintro (a | e) h
    · exact G.loopless a h
    · exact h.elim

namespace PendantExtension

variable (G : SimpleGraph α) (attach : β → α)

@[simp] theorem adj_inl_inl (a b : α) :
    (pendantExtension G attach).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b :=
  Iff.rfl

@[simp] theorem adj_inl_inr (a : α) (e : β) :
    (pendantExtension G attach).Adj (Sum.inl a) (Sum.inr e) ↔ a = attach e :=
  Iff.rfl

@[simp] theorem adj_inr_inl (e : β) (a : α) :
    (pendantExtension G attach).Adj (Sum.inr e) (Sum.inl a) ↔ a = attach e :=
  Iff.rfl

@[simp] theorem not_adj_inr_inr (e f : β) :
    ¬ (pendantExtension G attach).Adj (Sum.inr e) (Sum.inr f) :=
  id

/-- The unique neighbor of a pendant vertex is its attachment point. -/
theorem eq_of_adj_inr {e : β} {y z : α ⊕ β}
    (hy : (pendantExtension G attach).Adj (Sum.inr e) y)
    (hz : (pendantExtension G attach).Adj (Sum.inr e) z) :
    y = z := by
  cases y with
  | inl a =>
      cases z with
      | inl b =>
          cases hy
          cases hz
          rfl
      | inr f => exact hz.elim
  | inr f => exact hy.elim

/-- The old part of a pendant extension is the original graph. -/
noncomputable def induceRangeInlIso :
    G ≃g (pendantExtension G attach).induce (Set.range (Sum.inl : α → α ⊕ β)) where
  toEquiv := Equiv.ofInjective Sum.inl Sum.inl_injective
  map_rel_iff' := Iff.rfl

/-! ## Preservation of connectivity and acyclicity -/

/-- The inclusion of the original graph into a pendant extension. -/
def inlHom : G →g pendantExtension G attach where
  toFun := Sum.inl
  map_rel' := fun h => h

theorem preconnected (hG : G.Preconnected) :
    (pendantExtension G attach).Preconnected := by
  have hinl : ∀ a b : α,
      (pendantExtension G attach).Reachable (Sum.inl a) (Sum.inl b) :=
    fun a b => (hG a b).map (inlHom G attach)
  have hleaf : ∀ e : β,
      (pendantExtension G attach).Reachable (Sum.inr e) (Sum.inl (attach e)) :=
    fun e => (Adj.reachable (by simp))
  rintro (a | e) (b | f)
  · exact hinl a b
  · exact (hinl a (attach f)).trans (hleaf f).symm
  · exact (hleaf e).trans (hinl (attach e) b)
  · exact (hleaf e).trans ((hinl (attach e) (attach f)).trans (hleaf f).symm)

theorem connected (hG : G.Connected) :
    (pendantExtension G attach).Connected where
  preconnected := preconnected G attach hG.preconnected
  nonempty := ⟨Sum.inl hG.nonempty.some⟩

theorem isAcyclic (hG : G.IsAcyclic) :
    (pendantExtension G attach).IsAcyclic := by
  intro x c hc
  -- the support avoids the pendant leaves, whose unique incident edge cannot
  -- occur twice on a cycle
  have hsup : ∀ z ∈ c.support, z ∈ Set.range (Sum.inl : α → α ⊕ β) := by
    intro z hz
    cases z with
    | inl a => exact ⟨a, rfl⟩
    | inr e =>
        exact absurd hz
          (Walk.IsCycle.not_mem_support_of_forall_adj_eq
            (fun y z hy hz => eq_of_adj_inr G attach hy hz) hc)
  have hx : x ∈ Set.range (Sum.inl : α → α ⊕ β) :=
    hsup x c.start_mem_support
  -- lift the cycle to the old part and transport it to `G`
  have hlift : (c.induceLift hsup hx hx).IsCycle :=
    (Walk.isCycle_induceLift_iff c hsup hx).mpr hc
  have hmap :
      (((c.induceLift hsup hx hx).map
        (induceRangeInlIso G attach).symm.toHom)).IsCycle :=
    (Walk.map_isCycle_iff_of_injective
      (induceRangeInlIso G attach).symm.toEmbedding.injective).mpr hlift
  exact hG _ hmap

/-- Pendant extensions of trees are trees. -/
theorem isTree (hG : G.IsTree) : (pendantExtension G attach).IsTree where
  isConnected := connected G attach hG.isConnected
  IsAcyclic := isAcyclic G attach hG.IsAcyclic

end PendantExtension

end SimpleGraph
