import GraphMSO.Automata.automaton

/-!
# Projection and inverse projection

Closure of recognizable term sets under arity-preserving relabelings of the
alphabet, in both directions (TW Theorems 3 and 4):

* `RankedAlphabet.Hom.imageAutomaton` — the nondeterministic automaton for the
  image `Term.map π '' L`: at each node of the projected term it guesses a
  preimage symbol and simulates the original automaton;
* `RankedAlphabet.Hom.comapAutomaton` — the deterministic automaton for the
  preimage `Term.map π ⁻¹' L`: it reuses the transition of the projected
  symbol.

These are the automata constructions behind existential set quantification in
the MSO-to-automata compilation, where a quantified track is erased by a
projection of alphabets.
-/

universe u

namespace RankedAlphabet.Hom

open RankedAlphabet

variable {S T : RankedAlphabet.{u}}

/-! ## Projection (TW Theorem 3) -/

/--
The image automaton of `A : TreeAutomaton S` along `π : S.Hom T`.

A `g`-transition is allowed exactly when it is an `f`-transition of `A` for
some symbol `f` projecting to `g`; the child states are transported along the
arity equality of `π`.
-/
def imageAutomaton (π : S.Hom T) (A : TreeAutomaton S) : NTreeAutomaton T where
  State := A.State
  step g qs q :=
    ∃ (f : S.Symb) (h : π.toFun f = g),
      A.step f
        (fun i => qs (Fin.cast ((π.arity_eq f).symm.trans (congrArg T.arity h)) i)) = q
  accept := A.accept

/-- Every source run survives projection: the run of `A` on `s` is a possible
run of the image automaton on `s.map π`.  This is invariant (P1) of TW
Theorem 3. -/
theorem run_mem_runSet_map (π : S.Hom T) (A : TreeAutomaton S) (s : S.Term) :
    A.run s ∈ (π.imageAutomaton A).runSet (s.map π) := by
  induction s with
  | node f ts ih =>
      rw [Term.map_node, NTreeAutomaton.mem_runSet_node]
      exact ⟨fun i => A.run (ts (Fin.cast (π.arity_eq f) i)),
        fun i => ih (Fin.cast (π.arity_eq f) i), f, rfl, rfl⟩

/-- Every state reached by the image automaton is realized by some source
term: if `a` is a possible run state on `t`, then `t` is the projection of a
source term whose `A`-run is `a`.  This is invariant (P2) of TW Theorem 3. -/
theorem exists_map_eq_of_mem_runSet (π : S.Hom T) (A : TreeAutomaton S)
    (t : T.Term) :
    ∀ a ∈ (π.imageAutomaton A).runSet t,
      ∃ s : S.Term, s.map π = t ∧ A.run s = a := by
  induction t with
  | node g us ih =>
      rintro a ⟨qs, hqs, f, rfl, hstep⟩
      choose ss hmap hrun using fun i => ih i (qs i) (hqs i)
      refine ⟨.node f (fun j => ss (Fin.cast (π.arity_eq f).symm j)), ?_, ?_⟩
      · rw [Term.map_node]
        congr 1
        funext i
        exact hmap i
      · show A.step f
            (fun j => A.run (ss (Fin.cast (π.arity_eq f).symm j))) = a
        have hchild :
            (fun j : Fin (S.arity f) =>
                A.run (ss (Fin.cast (π.arity_eq f).symm j))) =
              fun j => qs (Fin.cast (π.arity_eq f).symm j) := by
          funext j
          exact hrun (Fin.cast (π.arity_eq f).symm j)
        rw [hchild]
        exact hstep

/-- The image automaton recognizes exactly the image of the language of `A`
under the term relabeling. -/
@[simp] theorem language_imageAutomaton (π : S.Hom T) (A : TreeAutomaton S) :
    (π.imageAutomaton A).language = RankedAlphabet.Term.map π '' A.language := by
  ext t
  constructor
  · rintro ⟨q, hq, hmem⟩
    obtain ⟨s, rfl, rfl⟩ := π.exists_map_eq_of_mem_runSet A t q hmem
    exact ⟨s, hq, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨A.run s, hs, π.run_mem_runSet_map A s⟩

/-! ## Inverse projection (TW Theorem 4) -/

/--
The preimage automaton of `A : TreeAutomaton T` along `π : S.Hom T`: the
transition of a symbol is the transition of its projection, with the child
states transported along the arity equality.
-/
def comapAutomaton (π : S.Hom T) (A : TreeAutomaton T) : TreeAutomaton S where
  State := A.State
  step f qs := A.step (π.toFun f) (fun i => qs (Fin.cast (π.arity_eq f) i))
  accept := A.accept

/-- The run of the preimage automaton is the run of `A` on the projected
term. -/
theorem run_comapAutomaton (π : S.Hom T) (A : TreeAutomaton T) (s : S.Term) :
    (π.comapAutomaton A).run s = A.run (s.map π) := by
  induction s with
  | node f ts ih =>
      show A.step (π.toFun f)
          (fun i => (π.comapAutomaton A).run (ts (Fin.cast (π.arity_eq f) i))) = _
      simp only [ih]
      rfl

/-- The preimage automaton recognizes exactly the preimage of the language of
`A` under the term relabeling. -/
@[simp] theorem language_comapAutomaton (π : S.Hom T) (A : TreeAutomaton T) :
    (π.comapAutomaton A).language = RankedAlphabet.Term.map π ⁻¹' A.language := by
  ext s
  rw [TreeAutomaton.mem_language, run_comapAutomaton]
  exact Iff.rfl

end RankedAlphabet.Hom

namespace RankedAlphabet.Recognizable

variable {S T : RankedAlphabet.{u}} {L : Set S.Term} {L' : Set T.Term}

/-- TW Theorem 3: recognizable sets are closed under projection. -/
theorem map (h : S.Recognizable L) (π : S.Hom T) :
    T.Recognizable (RankedAlphabet.Term.map π '' L) := by
  rcases h with ⟨A, rfl⟩
  exact (RankedAlphabet.recognizable_iff_nondet _).2
    ⟨π.imageAutomaton A, π.language_imageAutomaton A⟩

/-- TW Theorem 4: recognizable sets are closed under inverse projection. -/
theorem comap (h : T.Recognizable L') (π : S.Hom T) :
    S.Recognizable (RankedAlphabet.Term.map π ⁻¹' L') := by
  rcases h with ⟨A, rfl⟩
  exact ⟨π.comapAutomaton A, π.language_comapAutomaton A⟩

end RankedAlphabet.Recognizable
