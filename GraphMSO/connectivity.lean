import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Partition characterization of induced connectivity

The tree MSO formula `conn(X)` of the Courcelle translation says that no
proper nonempty subset of `X` is closed under edges: every split of `X` into
a nonempty `Y` and a nonempty rest has a crossing edge.  This file proves
that this second-order condition characterizes preconnectedness (and, with
nonemptiness, connectedness) of the induced subgraph, which is the fact the
translation-correctness proof needs to interpret `conn`.

The characterization holds for arbitrary simple graphs; no finiteness is
required.
-/

namespace SimpleGraph

universe u

variable {α : Type u} (G : SimpleGraph α)

/--
The induced subgraph on `X` is preconnected iff every split of `X` into a
nonempty part `Y` and a nonempty rest `X \ Y` has an edge across it.
-/
theorem induce_preconnected_iff_forall_exists_adj (X : Set α) :
    (G.induce X).Preconnected ↔
      ∀ Y ⊆ X, Y.Nonempty -> (X \ Y).Nonempty ->
        ∃ u ∈ Y, ∃ v ∈ X \ Y, G.Adj u v := by
  constructor
  · -- a walk from `Y` to the rest crosses the split at some edge
    intro hpre Y hYX ⟨y₀, hy₀⟩ ⟨z₀, hz₀⟩
    have key : ∀ (a b : X), (G.induce X).Walk a b -> a.1 ∈ Y -> b.1 ∉ Y ->
        ∃ u ∈ Y, ∃ v ∈ X \ Y, G.Adj u v := by
      intro a b w
      induction w with
      | nil =>
          intro ha hb
          exact absurd ha hb
      | @cons a c b hac p ih =>
          intro ha hb
          by_cases hc : c.1 ∈ Y
          · exact ih hc hb
          · exact ⟨a.1, ha, c.1, ⟨c.2, hc⟩, hac⟩
    obtain ⟨w⟩ := hpre ⟨y₀, hYX hy₀⟩ ⟨z₀, hz₀.1⟩
    exact key _ _ w hy₀ hz₀.2
  · -- the set reachable from a fixed vertex admits no crossing edge, so it
    -- exhausts `X`
    intro hcross u v
    let Y : Set α := {w | ∃ h : w ∈ X, (G.induce X).Reachable u ⟨w, h⟩}
    have hYX : Y ⊆ X := fun w hw => hw.1
    have hY_nonempty : Y.Nonempty := ⟨u.1, u.2, Reachable.refl u⟩
    have hrest : ¬ (X \ Y).Nonempty := by
      rintro hne
      obtain ⟨a, haY, b, hb, hadj⟩ := hcross Y hYX hY_nonempty hne
      rcases haY with ⟨haX, hreach⟩
      have hadj' : (G.induce X).Adj ⟨a, haX⟩ ⟨b, hb.1⟩ := hadj
      exact hb.2 ⟨hb.1, hreach.trans hadj'.reachable⟩
    have hvY : v.1 ∈ Y := by
      by_contra hv
      exact hrest ⟨v.1, v.2, hv⟩
    rcases hvY with ⟨hvX, hreach⟩
    exact hreach

/--
The induced subgraph on `X` is connected iff `X` is nonempty and every split
of `X` into a nonempty part and a nonempty rest has an edge across it.  This
is the semantic content of the `conn(X)` tree formula of the Courcelle
translation.
-/
theorem induce_connected_iff_nonempty_and_forall_exists_adj (X : Set α) :
    (G.induce X).Connected ↔
      X.Nonempty ∧
        ∀ Y ⊆ X, Y.Nonempty -> (X \ Y).Nonempty ->
          ∃ u ∈ Y, ∃ v ∈ X \ Y, G.Adj u v := by
  rw [connected_iff, induce_preconnected_iff_forall_exists_adj]
  constructor
  · rintro ⟨hcross, ⟨x⟩⟩
    exact ⟨⟨x.1, x.2⟩, hcross⟩
  · rintro ⟨⟨x, hx⟩, hcross⟩
    exact ⟨hcross, ⟨⟨x, hx⟩⟩⟩

end SimpleGraph
