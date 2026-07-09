import GraphMSO.Automata.term
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finite.Prod

/-!
# Bottom-up finite tree automata

Deterministic and nondeterministic bottom-up tree automata over a ranked
alphabet, their run semantics, and the first two closure theorems of
Thatcher–Wright:

* `NTreeAutomaton.determinize` — the subset construction (TW Theorem 1);
* complement, intersection, and union of recognizable term sets
  (TW Theorem 2).

A deterministic automaton is a finite `S`-algebra: `step` interprets every
symbol as an operation on states, and `run` is the unique homomorphism from
the term algebra.  Nondeterministic automata replace the operations by
relations; their run computes the set of reachable states.

State types are taken in `Type` with a bundled `Finite` instance.  Since
states are finite, this loses no generality, and it keeps the powerset and
product constructions in the same universe.
-/

universe u

/-- A deterministic bottom-up tree automaton over `S`: a finite `S`-algebra
together with a set of accepting states. -/
structure TreeAutomaton (S : RankedAlphabet.{u}) where
  /-- The type of states. -/
  State : Type
  /-- States form a finite type. -/
  [stateFinite : Finite State]
  /-- The transition operation interpreting each symbol. -/
  step : (f : S.Symb) → (Fin (S.arity f) → State) → State
  /-- The accepting states. -/
  accept : Set State

attribute [instance] TreeAutomaton.stateFinite

/-- A nondeterministic bottom-up tree automaton over `S`: transitions are
relations between child-state tuples and result states. -/
structure NTreeAutomaton (S : RankedAlphabet.{u}) where
  /-- The type of states. -/
  State : Type
  /-- States form a finite type. -/
  [stateFinite : Finite State]
  /-- The transition relation: `step f qs q` means the automaton may move to
  state `q` at an `f`-node whose children carry the states `qs`. -/
  step : (f : S.Symb) → (Fin (S.arity f) → State) → State → Prop
  /-- The accepting states. -/
  accept : Set State

attribute [instance] NTreeAutomaton.stateFinite

namespace TreeAutomaton

open RankedAlphabet

variable {S : RankedAlphabet.{u}}

/-- The bottom-up run of a deterministic automaton: the unique algebra
homomorphism from the term algebra to the automaton. -/
def run (A : TreeAutomaton S) : S.Term → A.State
  | .node f ts => A.step f fun i => A.run (ts i)

@[simp] theorem run_node (A : TreeAutomaton S) (f : S.Symb)
    (ts : Fin (S.arity f) → S.Term) :
    A.run (.node f ts) = A.step f fun i => A.run (ts i) :=
  rfl

/-- The behaviour of a deterministic automaton: the set of accepted terms. -/
def language (A : TreeAutomaton S) : Set S.Term :=
  {t | A.run t ∈ A.accept}

@[simp] theorem mem_language (A : TreeAutomaton S) (t : S.Term) :
    t ∈ A.language ↔ A.run t ∈ A.accept :=
  Iff.rfl

end TreeAutomaton

/-- A set of terms is recognizable if some finite deterministic bottom-up tree
automaton accepts exactly its members. -/
def RankedAlphabet.Recognizable (S : RankedAlphabet.{u}) (L : Set S.Term) : Prop :=
  ∃ A : TreeAutomaton S, A.language = L

namespace NTreeAutomaton

open RankedAlphabet

variable {S : RankedAlphabet.{u}}

/-- The run of a nondeterministic automaton: the set of states reachable at
the root of a term. -/
def runSet (N : NTreeAutomaton S) : S.Term → Set N.State
  | .node f ts =>
      {q | ∃ qs : Fin (S.arity f) → N.State,
        (∀ i, qs i ∈ N.runSet (ts i)) ∧ N.step f qs q}

theorem mem_runSet_node (N : NTreeAutomaton S) (f : S.Symb)
    (ts : Fin (S.arity f) → S.Term) (q : N.State) :
    q ∈ N.runSet (.node f ts) ↔
      ∃ qs : Fin (S.arity f) → N.State,
        (∀ i, qs i ∈ N.runSet (ts i)) ∧ N.step f qs q :=
  Iff.rfl

/-- The behaviour of a nondeterministic automaton: terms whose run reaches an
accepting state. -/
def language (N : NTreeAutomaton S) : Set S.Term :=
  {t | ∃ q ∈ N.accept, q ∈ N.runSet t}

@[simp] theorem mem_language (N : NTreeAutomaton S) (t : S.Term) :
    t ∈ N.language ↔ ∃ q ∈ N.accept, q ∈ N.runSet t :=
  Iff.rfl

/-! ## The subset construction (TW Theorem 1) -/

/-- The powerset determinization of a nondeterministic automaton. -/
def determinize (N : NTreeAutomaton S) : TreeAutomaton S where
  State := Set N.State
  step f Qs := {q | ∃ qs, (∀ i, qs i ∈ Qs i) ∧ N.step f qs q}
  accept := {Q | ∃ q ∈ N.accept, q ∈ Q}

/-- The deterministic run of the powerset automaton computes exactly the
nondeterministic run set. -/
theorem run_determinize (N : NTreeAutomaton S) (t : S.Term) :
    N.determinize.run t = N.runSet t := by
  induction t with
  | node f ts ih =>
      show N.determinize.step f (fun i => N.determinize.run (ts i)) = _
      simp only [ih]
      rfl

/-- The powerset automaton recognizes the language of the nondeterministic
automaton. -/
@[simp] theorem language_determinize (N : NTreeAutomaton S) :
    N.determinize.language = N.language := by
  ext t
  rw [TreeAutomaton.mem_language, run_determinize]
  rfl

end NTreeAutomaton

namespace TreeAutomaton

open RankedAlphabet

variable {S : RankedAlphabet.{u}}

/-- View a deterministic automaton as a nondeterministic one whose transition
relation is the graph of the transition operation. -/
def toNondet (A : TreeAutomaton S) : NTreeAutomaton S where
  State := A.State
  step f qs q := A.step f qs = q
  accept := A.accept

/-- The nondeterministic run of `toNondet` is the singleton of the
deterministic run. -/
theorem runSet_toNondet (A : TreeAutomaton S) (t : S.Term) :
    A.toNondet.runSet t = {A.run t} := by
  induction t with
  | node f ts ih =>
      ext q
      constructor
      · rintro ⟨qs, hqs, rfl⟩
        have hfun : qs = fun i => A.run (ts i) := by
          funext i
          have := hqs i
          rw [ih i] at this
          exact this
        simp [hfun]
      · rintro rfl
        exact ⟨fun i => A.run (ts i), fun i => by rw [ih i]; rfl, rfl⟩

@[simp] theorem language_toNondet (A : TreeAutomaton S) :
    A.toNondet.language = A.language := by
  ext t
  rw [NTreeAutomaton.mem_language, mem_language]
  constructor
  · rintro ⟨q, hq, hmem⟩
    rw [runSet_toNondet] at hmem
    rwa [hmem] at hq
  · intro h
    exact ⟨A.run t, h, by rw [runSet_toNondet]; rfl⟩

/-- TW Theorem 1: a term set is recognizable by a deterministic automaton iff
it is recognizable by a nondeterministic one. -/
theorem _root_.RankedAlphabet.recognizable_iff_nondet (L : Set S.Term) :
    S.Recognizable L ↔ ∃ N : NTreeAutomaton S, N.language = L := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A.toNondet, A.language_toNondet⟩
  · rintro ⟨N, rfl⟩
    exact ⟨N.determinize, N.language_determinize⟩

/-! ## Boolean closure (TW Theorem 2) -/

/-- Complement automaton: same algebra, complemented accepting set.
Determinism is essential here. -/
def compl (A : TreeAutomaton S) : TreeAutomaton S :=
  { A with accept := A.acceptᶜ }

/-- The complement automaton has the same transition algebra, hence the same
run. -/
theorem run_compl (A : TreeAutomaton S) (t : S.Term) :
    A.compl.run t = A.run t := by
  induction t with
  | node f ts ih =>
      show A.step f (fun i => A.compl.run (ts i)) = _
      simp only [ih]
      rfl

@[simp] theorem language_compl (A : TreeAutomaton S) :
    A.compl.language = A.languageᶜ := by
  ext t
  rw [mem_language, run_compl]
  exact Iff.rfl

/-- The product automaton, computing both runs simultaneously; the accepting
set is a parameter so that intersection and union are two accepting choices
for one construction. -/
def prod (A B : TreeAutomaton S) (acc : Set (A.State × B.State)) :
    TreeAutomaton S where
  State := A.State × B.State
  step f qs := (A.step f fun i => (qs i).1, B.step f fun i => (qs i).2)
  accept := acc

/-- The product automaton computes both original runs at the same time. -/
theorem run_prod (A B : TreeAutomaton S) (acc : Set (A.State × B.State))
    (t : S.Term) :
    (A.prod B acc).run t = (A.run t, B.run t) := by
  induction t with
  | node f ts ih =>
      show (A.prod B acc).step f (fun i => (A.prod B acc).run (ts i)) = _
      simp only [ih]
      rfl

/-- Intersection automaton. -/
def inter (A B : TreeAutomaton S) : TreeAutomaton S :=
  A.prod B {p | p.1 ∈ A.accept ∧ p.2 ∈ B.accept}

@[simp] theorem language_inter (A B : TreeAutomaton S) :
    (A.inter B).language = A.language ∩ B.language := by
  ext t
  rw [mem_language, inter, run_prod]
  exact Iff.rfl

/-- Union automaton. -/
def union (A B : TreeAutomaton S) : TreeAutomaton S :=
  A.prod B {p | p.1 ∈ A.accept ∨ p.2 ∈ B.accept}

@[simp] theorem language_union (A B : TreeAutomaton S) :
    (A.union B).language = A.language ∪ B.language := by
  ext t
  rw [mem_language, union, run_prod]
  exact Iff.rfl

end TreeAutomaton

namespace RankedAlphabet.Recognizable

open RankedAlphabet

variable {S : RankedAlphabet.{u}} {L L' : Set S.Term}

/-- TW Theorem 2: recognizable sets are closed under complement. -/
theorem compl (h : S.Recognizable L) : S.Recognizable Lᶜ := by
  rcases h with ⟨A, rfl⟩
  exact ⟨A.compl, A.language_compl⟩

/-- TW Theorem 2: recognizable sets are closed under intersection. -/
theorem inter (h : S.Recognizable L) (h' : S.Recognizable L') :
    S.Recognizable (L ∩ L') := by
  rcases h with ⟨A, rfl⟩
  rcases h' with ⟨B, rfl⟩
  exact ⟨A.inter B, A.language_inter B⟩

/-- TW Theorem 2: recognizable sets are closed under union. -/
theorem union (h : S.Recognizable L) (h' : S.Recognizable L') :
    S.Recognizable (L ∪ L') := by
  rcases h with ⟨A, rfl⟩
  rcases h' with ⟨B, rfl⟩
  exact ⟨A.union B, A.language_union B⟩

end RankedAlphabet.Recognizable
