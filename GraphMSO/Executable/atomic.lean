import GraphMSO.Executable.automaton
import GraphMSO.Automata.atomic

/-!
# Executable atomic automata

These automata are the computational counterparts of the atomic tracked-tree
languages. Their states are explicit finite data and their accepting tests
are Boolean.
-/

namespace GraphMSO.Executable

universe u

open BinTree
open BinTree.Automata
open ExecTreeAutomaton

variable {A : Type u}

/-- Build an executable automaton from a bottom-up fold. -/
def foldAutomaton {σ : Type} [Finite σ] [DecidableEq σ]
    (nilState : σ) (nodeStep : A → σ → σ → σ) (accept : σ → Bool) :
    ExecTreeAutomaton A where
  State := σ
  nil := nilState
  node := nodeStep
  accept := accept

@[simp] theorem run_foldAutomaton {σ : Type} [Finite σ] [DecidableEq σ]
    (nilState : σ) (nodeStep : A → σ → σ → σ) (accept : σ → Bool)
    (t : BinTree A) :
    (foldAutomaton nilState nodeStep accept).run t =
      t.fold nilState nodeStep := by
  induction t with
  | nil => rfl
  | node a left right ihLeft ihRight =>
      change nodeStep a
        ((foldAutomaton nilState nodeStep accept).run left)
        ((foldAutomaton nilState nodeStep accept).run right) = _
      rw [ihLeft, ihRight]
      rfl

/-- The automaton that rejects every tree. -/
def falseAutomaton (A : Type u) : ExecTreeAutomaton A :=
  foldAutomaton PUnit.unit (fun _ _ _ => PUnit.unit) (fun _ => false)

@[simp] theorem falseAutomaton_accepts (t : BinTree A) :
    (falseAutomaton A).accepts t = false :=
  rfl

/-- A track is marked at exactly one node. -/
def trackSingletonAutomaton (A : Type u) {n : Nat} (i : Fin n) :
    ExecTreeAutomaton (A × TrackBits n) :=
  foldAutomaton Count.zero
    (fun a left right => Count.addMark (a.2 i) (Count.add left right))
    (fun count => decide (count = Count.one))

@[simp] theorem run_trackSingletonAutomaton {n : Nat} (i : Fin n)
    (t : BinTree (A × TrackBits n)) :
    (trackSingletonAutomaton A i).run t = trackCount i t := by
  simp [trackSingletonAutomaton, trackCount]

@[simp] theorem trackSingletonAutomaton_accepts_eq_true {n : Nat}
    (i : Fin n) (t : BinTree (A × TrackBits n)) :
    (trackSingletonAutomaton A i).accepts t = true ↔
      trackCount i t = Count.one := by
  change decide ((trackSingletonAutomaton A i).run t = Count.one) = true ↔ _
  rw [run_trackSingletonAutomaton]
  simp

/-- Two tracks intersect at some node. -/
def tracksIntersectAutomaton (A : Type u) {n : Nat} (i j : Fin n) :
    ExecTreeAutomaton (A × TrackBits n) :=
  foldAutomaton false
    (fun a left right => (a.2 i && a.2 j) || left || right)
    id

@[simp] theorem run_tracksIntersectAutomaton {n : Nat} (i j : Fin n)
    (t : BinTree (A × TrackBits n)) :
    (tracksIntersectAutomaton A i j).run t = tracksIntersect i j t := by
  simp [tracksIntersectAutomaton, tracksIntersect]

@[simp] theorem tracksIntersectAutomaton_accepts {n : Nat} (i j : Fin n)
    (t : BinTree (A × TrackBits n)) :
    (tracksIntersectAutomaton A i j).accepts t = tracksIntersect i j t := by
  change (tracksIntersectAutomaton A i j).run t = tracksIntersect i j t
  exact run_tracksIntersectAutomaton i j t

/-- A parent-track node has a child-track child. -/
def parentTrackAutomaton (A : Type u) {n : Nat} (parent child : Fin n) :
    ExecTreeAutomaton (A × TrackBits n) :=
  foldAutomaton (false, false)
    (fun a left right =>
      let rootChild := a.2 child
      let found := left.2 || right.2 ||
        (a.2 parent && left.1) || (a.2 parent && right.1)
      (rootChild, found))
    (fun summary => summary.2)

@[simp] theorem run_parentTrackAutomaton {n : Nat} (parent child : Fin n)
    (t : BinTree (A × TrackBits n)) :
    (parentTrackAutomaton A parent child).run t =
      parentTrackSummary parent child t := by
  simp [parentTrackAutomaton, parentTrackSummary]

@[simp] theorem parentTrackAutomaton_accepts {n : Nat} (parent child : Fin n)
    (t : BinTree (A × TrackBits n)) :
    (parentTrackAutomaton A parent child).accepts t =
      (parentTrackSummary parent child t).2 := by
  change ((parentTrackAutomaton A parent child).run t).2 = _
  rw [run_parentTrackAutomaton]

/-! ## Decidable label predicates -/

section Labels

variable {B : Type}

/-- Finite set of labels occurring at nodes marked on a track. -/
def labelsOnTrackFinset [DecidableEq B] {n : Nat} (i : Fin n) :
    BinTree (B × TrackBits n) → Finset B
  | .nil => ∅
  | .node a left right =>
      ((if a.2 i = true then {a.1} else ∅) ∪
        labelsOnTrackFinset i left) ∪ labelsOnTrackFinset i right

theorem mem_labelsOnTrackFinset_iff [DecidableEq B] {n : Nat} (i : Fin n)
    (t : BinTree (B × TrackBits n)) (a : B) :
    a ∈ labelsOnTrackFinset i t ↔ a ∈ labelsOnTrack i t := by
  induction t with
  | nil => simp [labelsOnTrackFinset, labelsOnTrack]
  | node label left right ihLeft ihRight =>
      by_cases hlabel : label.2 i = true <;>
        simp [labelsOnTrackFinset, labelsOnTrack, ihLeft, ihRight, hlabel, or_assoc]

/-- Collect the labels marked by one track. -/
def labelsOnTrackAutomaton [Finite B] [DecidableEq B] {n : Nat}
    (i : Fin n) (accept : Finset B → Bool) :
    ExecTreeAutomaton (B × TrackBits n) :=
  foldAutomaton ∅
    (fun a left right =>
      ((if a.2 i = true then {a.1} else ∅) ∪ left) ∪ right)
    accept

@[simp] theorem run_labelsOnTrackAutomaton [Finite B] [DecidableEq B]
    {n : Nat} (i : Fin n) (accept : Finset B → Bool)
    (t : BinTree (B × TrackBits n)) :
    (labelsOnTrackAutomaton i accept).run t = labelsOnTrackFinset i t := by
  unfold labelsOnTrackAutomaton
  rw [run_foldAutomaton]
  induction t with
  | nil => rfl
  | node label left right ihLeft ihRight =>
      rw [BinTree.fold_node, labelsOnTrackFinset]
      rw [ihLeft, ihRight]

/-- Executable unary label predicate at a marked first-order track. -/
def labelMemTrackAutomaton [Finite B] [DecidableEq B] {n : Nat}
    (i : Fin n) (predicate : B → Bool) :
    ExecTreeAutomaton (B × TrackBits n) :=
  labelsOnTrackAutomaton i (fun labels => finsetAny labels predicate)

theorem labelMemTrackAutomaton_accepts_eq_true_iff
    [Finite B] [DecidableEq B] {n : Nat} (i : Fin n)
    (predicate : B → Bool) (t : BinTree (B × TrackBits n)) :
    (labelMemTrackAutomaton i predicate).accepts t = true ↔
      ∃ a ∈ labelsOnTrack i t, predicate a = true := by
  change finsetAny ((labelsOnTrackAutomaton i _).run t) predicate = true ↔ _
  rw [run_labelsOnTrackAutomaton, finsetAny_eq_true_iff]
  constructor
  · rintro ⟨a, ha, hp⟩
    exact ⟨a, (mem_labelsOnTrackFinset_iff i t a).mp ha, hp⟩
  · rintro ⟨a, ha, hp⟩
    exact ⟨a, (mem_labelsOnTrackFinset_iff i t a).mpr ha, hp⟩

/-- Pair of finite label sets marked by two tracks. -/
def labelPairFinset [DecidableEq B] {n : Nat} (i j : Fin n) :
    BinTree (B × TrackBits n) → Finset B × Finset B
  | .nil => (∅, ∅)
  | .node a left right =>
      let first := if a.2 i = true then {a.1} else ∅
      let second := if a.2 j = true then {a.1} else ∅
      let leftState := labelPairFinset i j left
      let rightState := labelPairFinset i j right
      ((first ∪ leftState.1) ∪ rightState.1,
        (second ∪ leftState.2) ∪ rightState.2)

theorem labelPairFinset_fst [DecidableEq B] {n : Nat} (i j : Fin n)
    (t : BinTree (B × TrackBits n)) :
    (labelPairFinset i j t).1 = labelsOnTrackFinset i t := by
  induction t with
  | nil => rfl
  | node label left right ihLeft ihRight =>
      change
        ((if label.2 i = true then {label.1} else ∅) ∪
          (labelPairFinset i j left).1) ∪ (labelPairFinset i j right).1 = _
      rw [ihLeft, ihRight]
      rfl

theorem labelPairFinset_snd [DecidableEq B] {n : Nat} (i j : Fin n)
    (t : BinTree (B × TrackBits n)) :
    (labelPairFinset i j t).2 = labelsOnTrackFinset j t := by
  induction t with
  | nil => rfl
  | node label left right ihLeft ihRight =>
      change
        ((if label.2 j = true then {label.1} else ∅) ∪
          (labelPairFinset i j left).2) ∪ (labelPairFinset i j right).2 = _
      rw [ihLeft, ihRight]
      rfl

/-- Executable binary relation on labels carried by two marked tracks. -/
def labelMem₂TrackAutomaton [Finite B] [DecidableEq B] {n : Nat}
    (i j : Fin n) (relation : B → B → Bool) :
    ExecTreeAutomaton (B × TrackBits n) :=
  foldAutomaton (∅, ∅)
    (fun a left right =>
      let first := if a.2 i = true then {a.1} else ∅
      let second := if a.2 j = true then {a.1} else ∅
      ((first ∪ left.1) ∪ right.1, (second ∪ left.2) ∪ right.2))
    (fun labels =>
      finsetAny labels.1 fun a => finsetAny labels.2 fun b => relation a b)

@[simp] theorem run_labelMem₂TrackAutomaton [Finite B] [DecidableEq B]
    {n : Nat} (i j : Fin n) (relation : B → B → Bool)
    (t : BinTree (B × TrackBits n)) :
    (labelMem₂TrackAutomaton i j relation).run t = labelPairFinset i j t := by
  unfold labelMem₂TrackAutomaton
  rw [run_foldAutomaton]
  induction t with
  | nil => rfl
  | node label left right ihLeft ihRight =>
      rw [BinTree.fold_node, labelPairFinset]
      rw [ihLeft, ihRight]

theorem labelMem₂TrackAutomaton_accepts_eq_true_iff
    [Finite B] [DecidableEq B] {n : Nat} (i j : Fin n)
    (relation : B → B → Bool) (t : BinTree (B × TrackBits n)) :
    (labelMem₂TrackAutomaton i j relation).accepts t = true ↔
      ∃ a ∈ labelsOnTrack i t, ∃ b ∈ labelsOnTrack j t,
        relation a b = true := by
  change
    finsetAny ((labelMem₂TrackAutomaton i j relation).run t).1
      (fun a => finsetAny
        ((labelMem₂TrackAutomaton i j relation).run t).2
        (fun b => relation a b)) = true ↔ _
  rw [run_labelMem₂TrackAutomaton, finsetAny_eq_true_iff]
  simp only [finsetAny_eq_true_iff]
  constructor
  · rintro ⟨a, ha, b, hb, hr⟩
    rw [labelPairFinset_fst] at ha
    rw [labelPairFinset_snd] at hb
    exact ⟨a, (mem_labelsOnTrackFinset_iff i t a).mp ha,
      b, (mem_labelsOnTrackFinset_iff j t b).mp hb, hr⟩
  · rintro ⟨a, ha, b, hb, hr⟩
    refine ⟨a, ?_, b, ?_, hr⟩
    · rw [labelPairFinset_fst]
      exact (mem_labelsOnTrackFinset_iff i t a).mpr ha
    · rw [labelPairFinset_snd]
      exact (mem_labelsOnTrackFinset_iff j t b).mpr hb

end Labels

end GraphMSO.Executable
