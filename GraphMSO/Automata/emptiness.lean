import GraphMSO.Automata.automaton
import Mathlib.Data.Set.Card

/-!
# Replacement and emptiness

The remaining automata facts of Thatcher–Wright §2:

* `RankedAlphabet.Context` and `TreeAutomaton.run_fill_eq_of_run_eq` — the
  replacement lemma (TW Lemma 5): replacing a subterm by one with the same
  run state does not change the run of the whole term.
* `TreeAutomaton.exists_depth_le_of_run_eq` — the bounded-depth witness
  (TW Lemma 6): every reachable state is reached by a term of depth at most
  the number of states.
* `TreeAutomaton.language_nonempty_iff` — the emptiness characterization
  behind TW Theorem 7: the language is nonempty iff it contains a term of
  depth at most the number of states.

The bounded-depth witness is proved by depth-indexed reachability sets rather
than by TW's minimal-counterexample pumping: the sets `reachableAtDepth k`
increase with `k`, each step is generated from the previous one by a single
transition, and a monotone sequence of subsets of a finite type must
stabilize within `Nat.card` steps.  This avoids formalizing root-to-leaf
subterm chains while proving the same bound.

Effective decidability of emptiness — enumerating the finitely many terms of
bounded depth over a finite alphabet — is deliberately postponed to the
executable phase of the project.
-/

universe u

namespace RankedAlphabet

/-- A one-hole context: a term with exactly one missing subterm.  `fill`
plugs a term into the hole.  This packages Thatcher–Wright's "occurrence of a
subterm" for the replacement lemma. -/
inductive Context (S : RankedAlphabet.{u}) : Type u
  | hole : Context S
  | node (f : S.Symb) (i : Fin (S.arity f)) (siblings : Fin (S.arity f) → S.Term)
      (ctx : Context S) : Context S

namespace Context

variable {S : RankedAlphabet.{u}}

/-- Plug a term into the hole of a context. -/
def fill : Context S → S.Term → S.Term
  | hole, t => t
  | node f i siblings ctx, t => .node f (Function.update siblings i (ctx.fill t))

@[simp] theorem fill_hole (t : S.Term) : (hole : Context S).fill t = t :=
  rfl

@[simp] theorem fill_node (f : S.Symb) (i : Fin (S.arity f))
    (siblings : Fin (S.arity f) → S.Term) (ctx : Context S) (t : S.Term) :
    (node f i siblings ctx).fill t =
      .node f (Function.update siblings i (ctx.fill t)) :=
  rfl

end Context

end RankedAlphabet

namespace TreeAutomaton

open RankedAlphabet

variable {S : RankedAlphabet.{u}} (A : TreeAutomaton S)

/-! ## The replacement lemma (TW Lemma 5) -/

/-- TW Lemma 5: replacing an occurrence of a subterm by a term with the same
run state does not change the run of the surrounding term. -/
theorem run_fill_eq_of_run_eq {t₁ t₂ : S.Term} (h : A.run t₁ = A.run t₂) :
    ∀ C : Context S, A.run (C.fill t₁) = A.run (C.fill t₂) := by
  intro C
  induction C with
  | hole =>
      exact h
  | node f i siblings ctx ih =>
      rw [Context.fill_node, Context.fill_node, run_node, run_node]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Function.update_self]
        exact ih
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]

/-! ## Depth-indexed reachability -/

/-- The states reachable by some term of depth at most `k`. -/
def reachableAtDepth (k : ℕ) : Set A.State :=
  {a | ∃ t : S.Term, A.run t = a ∧ t.depth ≤ k}

/-- The states reachable by some term. -/
def reachable : Set A.State :=
  {a | ∃ t : S.Term, A.run t = a}

@[simp] theorem reachableAtDepth_zero : A.reachableAtDepth 0 = ∅ := by
  ext a
  simp only [reachableAtDepth, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_exists, not_and]
  intro t _
  have := t.depth_pos
  omega

theorem reachableAtDepth_mono : Monotone A.reachableAtDepth := by
  intro k l hkl a ⟨t, hrun, hdepth⟩
  exact ⟨t, hrun, hdepth.trans hkl⟩

theorem reachableAtDepth_subset_reachable (k : ℕ) :
    A.reachableAtDepth k ⊆ A.reachable := by
  rintro a ⟨t, hrun, -⟩
  exact ⟨t, hrun⟩

/-- One-step generation: the states reachable at depth `k + 1` are exactly
the results of one transition from states reachable at depth `k`. -/
theorem reachableAtDepth_succ (k : ℕ) :
    A.reachableAtDepth (k + 1) =
      {a | ∃ (f : S.Symb) (qs : Fin (S.arity f) → A.State),
        (∀ i, qs i ∈ A.reachableAtDepth k) ∧ A.step f qs = a} := by
  ext a
  constructor
  · rintro ⟨t, rfl, hdepth⟩
    cases t with
    | node f ts =>
        rw [Term.depth_node_le_succ_iff] at hdepth
        exact ⟨f, fun i => A.run (ts i),
          fun i => ⟨ts i, rfl, hdepth i⟩, rfl⟩
  · rintro ⟨f, qs, hqs, rfl⟩
    choose ts hrun hdepth using hqs
    exact ⟨.node f ts, by rw [run_node]; simp only [hrun],
      (Term.depth_node_le_succ_iff f ts k).2 hdepth⟩

/-- Once two consecutive reachability layers agree, all later layers agree
with them. -/
theorem reachableAtDepth_eq_of_stab {k : ℕ}
    (h : A.reachableAtDepth (k + 1) = A.reachableAtDepth k) :
    ∀ l, k ≤ l → A.reachableAtDepth l = A.reachableAtDepth k := by
  intro l hl
  induction l with
  | zero =>
      obtain rfl : k = 0 := Nat.le_zero.mp hl
      rfl
  | succ l ih =>
      rcases Nat.lt_or_ge k (l + 1) with hlt | hge
      · have hkl : k ≤ l := Nat.lt_succ_iff.mp hlt
        have hprev : A.reachableAtDepth l = A.reachableAtDepth k := ih hkl
        rw [reachableAtDepth_succ, hprev, ← reachableAtDepth_succ, h]
      · obtain rfl : k = l + 1 := Nat.le_antisymm hl hge
        rfl

/-- Some two consecutive layers among the first `Nat.card A.State + 1` agree:
a strictly increasing chain of subsets of a finite type cannot be longer than
the cardinality. -/
theorem exists_reachableAtDepth_stab :
    ∃ k ≤ Nat.card A.State,
      A.reachableAtDepth (k + 1) = A.reachableAtDepth k := by
  by_contra hcon
  push_neg at hcon
  have hssub : ∀ k ≤ Nat.card A.State,
      A.reachableAtDepth k ⊂ A.reachableAtDepth (k + 1) := by
    intro k hk
    exact HasSubset.Subset.ssubset_of_ne
      (A.reachableAtDepth_mono (Nat.le_succ k)) (Ne.symm (hcon k hk))
  have hcard : ∀ k ≤ Nat.card A.State + 1, k ≤ (A.reachableAtDepth k).ncard := by
    intro k hk
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        have hk' : k ≤ Nat.card A.State := Nat.succ_le_succ_iff.mp hk
        have hlt := Set.ncard_lt_ncard (hssub k hk')
          (Set.toFinite (A.reachableAtDepth (k + 1)))
        have := ih (hk'.trans (Nat.le_succ _))
        omega
  have hle : (A.reachableAtDepth (Nat.card A.State + 1)).ncard ≤
      Nat.card A.State := by
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  have := hcard (Nat.card A.State + 1) le_rfl
  omega

/-- Every reachable state is already reachable within depth
`Nat.card A.State`. -/
theorem reachable_eq_reachableAtDepth_card :
    A.reachable = A.reachableAtDepth (Nat.card A.State) := by
  refine Set.Subset.antisymm ?_ (A.reachableAtDepth_subset_reachable _)
  rintro a ⟨t, rfl⟩
  obtain ⟨k, hk, hstab⟩ := A.exists_reachableAtDepth_stab
  have hmem : A.run t ∈ A.reachableAtDepth t.depth := ⟨t, rfl, le_rfl⟩
  rcases Nat.le_total t.depth (Nat.card A.State) with hle | hge
  · exact A.reachableAtDepth_mono hle hmem
  · have hdepth_eq : A.reachableAtDepth t.depth = A.reachableAtDepth k :=
      A.reachableAtDepth_eq_of_stab hstab t.depth (hk.trans hge)
    rw [hdepth_eq] at hmem
    exact A.reachableAtDepth_mono hk hmem

/-! ## Bounded-depth witnesses and emptiness (TW Lemma 6, Theorem 7) -/

/-- TW Lemma 6: every state reached by some term is reached by a term of
depth at most the number of states. -/
theorem exists_depth_le_of_run_eq (t : S.Term) :
    ∃ t' : S.Term, A.run t' = A.run t ∧ t'.depth ≤ Nat.card A.State := by
  have hmem : A.run t ∈ A.reachable := ⟨t, rfl⟩
  rw [A.reachable_eq_reachableAtDepth_card] at hmem
  exact hmem

/-- The emptiness characterization behind TW Theorem 7: the language of a
finite deterministic automaton is nonempty iff it contains a term of depth at
most the number of states.  Over a finite alphabet the right-hand side is a
finite search, which is the decision procedure. -/
theorem language_nonempty_iff :
    A.language.Nonempty ↔
      ∃ t ∈ A.language, t.depth ≤ Nat.card A.State := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨t', hrun, hdepth⟩ := A.exists_depth_le_of_run_eq t
    refine ⟨t', ?_, hdepth⟩
    rw [mem_language, hrun]
    exact ht
  · rintro ⟨t, ht, -⟩
    exact ⟨t, ht⟩

end TreeAutomaton
