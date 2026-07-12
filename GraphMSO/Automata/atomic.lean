import GraphMSO.Automata.automaton
import GraphMSO.Automata.binTree

/-!
# Atomic automata for tracked binary trees

This file starts the MSO-to-automata compilation layer.  A tree with free
monadic variables is represented by Boolean tracks in its labels:
`A × TrackBits n`.  First-order variables are represented by singleton
tracks, and set variables by arbitrary tracks.

The automata here are deliberately small bottom-up summaries over the padded
ranked alphabet.  They recognize the atomic information needed by the tree
language: singleton tracks, membership of a marked node in a marked set,
root/parent relations between marked nodes, and label predicates read at
marked tracks.
-/

universe u v

namespace BinTree

variable {A : Type u}

/-! ## Generic bottom-up summaries over padded terms -/

/-- Fold a binary tree into a finite state summary. -/
def fold {σ : Type v} (nilState : σ) (nodeStep : A → σ → σ → σ) : BinTree A → σ
  | .nil => nilState
  | .node a l r => nodeStep a (l.fold nilState nodeStep) (r.fold nilState nodeStep)

@[simp] theorem fold_nil {σ : Type v} (nilState : σ) (nodeStep : A → σ → σ → σ) :
    (BinTree.nil : BinTree A).fold nilState nodeStep = nilState :=
  rfl

@[simp] theorem fold_node {σ : Type v} (nilState : σ) (nodeStep : A → σ → σ → σ)
    (a : A) (l r : BinTree A) :
    (BinTree.node a l r).fold nilState nodeStep =
      nodeStep a (l.fold nilState nodeStep) (r.fold nilState nodeStep) :=
  rfl

namespace Automata

open RankedAlphabet

/-- A deterministic automaton induced by a bottom-up summary algebra on
binary trees. -/
def foldAutomaton {σ : Type} (nilState : σ) (nodeStep : A → σ → σ → σ)
    (accept : Set σ) [Finite σ] : TreeAutomaton (paddedAlphabet A) where
  State := σ
  step
    | none, _ => nilState
    | some a, qs =>
        nodeStep a
          (qs ⟨0, by simp [paddedAlphabet]⟩)
          (qs ⟨1, by simp [paddedAlphabet]⟩)
  accept := accept

theorem run_foldAutomaton {σ : Type} (nilState : σ) (nodeStep : A → σ → σ → σ)
    (accept : Set σ) [Finite σ] (t : (paddedAlphabet A).Term) :
    (foldAutomaton nilState nodeStep accept).run t =
      (BinTree.ofTerm t).fold nilState nodeStep := by
  induction t with
  | node f ts ih =>
      cases f with
      | none =>
          change nilState = nilState
          rfl
      | some a =>
          change nodeStep a
              ((foldAutomaton nilState nodeStep accept).run
                (ts ⟨0, by simp [paddedAlphabet]⟩))
              ((foldAutomaton nilState nodeStep accept).run
                (ts ⟨1, by simp [paddedAlphabet]⟩)) =
            nodeStep a
              ((BinTree.ofTerm (ts ⟨0, by simp [paddedAlphabet]⟩)).fold
                nilState nodeStep)
              ((BinTree.ofTerm (ts ⟨1, by simp [paddedAlphabet]⟩)).fold
                nilState nodeStep)
          rw [ih ⟨0, by simp [paddedAlphabet]⟩,
            ih ⟨1, by simp [paddedAlphabet]⟩]

@[simp] theorem language_foldAutomaton {σ : Type} (nilState : σ)
    (nodeStep : A → σ → σ → σ) (accept : Set σ) [Finite σ] :
    (foldAutomaton nilState nodeStep accept).language =
      {t | (BinTree.ofTerm t).fold nilState nodeStep ∈ accept} := by
  ext t
  rw [TreeAutomaton.mem_language, run_foldAutomaton]
  rfl

/-! ## Boolean summaries for tracks -/

/-- Saturating counts: enough to express that a first-order track is a
singleton. -/
inductive Count where
  | zero
  | one
  | many
  deriving DecidableEq

instance : Fintype Count where
  elems := {Count.zero, Count.one, Count.many}
  complete := by
    intro x
    cases x <;> simp

instance : Finite Count :=
  by infer_instance

namespace Count

/-- Add two saturating counts. -/
def add : Count → Count → Count
  | zero, c => c
  | c, zero => c
  | _, _ => many

/-- Add one marked node to a saturating count. -/
def addMark (marked : Bool) (c : Count) : Count :=
  if marked = true then add one c else c

@[simp] theorem add_zero_left (c : Count) : add zero c = c := by
  cases c <;> rfl

@[simp] theorem add_zero_right (c : Count) : add c zero = c := by
  cases c <;> rfl

theorem add_eq_zero_iff (a b : Count) :
    add a b = zero ↔ a = zero ∧ b = zero := by
  cases a <;> cases b <;> simp [add]

theorem add_eq_one_iff (a b : Count) :
    add a b = one ↔ (a = one ∧ b = zero) ∨ (a = zero ∧ b = one) := by
  cases a <;> cases b <;> simp [add]

@[simp] theorem addMark_false (c : Count) : addMark false c = c := by
  rfl

@[simp] theorem addMark_true (c : Count) : addMark true c = add one c := by
  rfl

theorem addMark_eq_zero_iff (marked : Bool) (c : Count) :
    addMark marked c = zero ↔ marked = false ∧ c = zero := by
  cases marked <;> cases c <;> simp [addMark, add]

theorem addMark_eq_one_iff (marked : Bool) (c : Count) :
    addMark marked c = one ↔
      (marked = true ∧ c = zero) ∨ (marked = false ∧ c = one) := by
  cases marked <;> cases c <;> simp [addMark, add]

end Count

/-- Count the number of marked nodes on one Boolean track, saturating above
one. -/
def trackCount {n : ℕ} (i : Fin n) : BinTree (A × TrackBits n) → Count :=
  fold Count.zero fun a l r => Count.addMark (a.2 i) (Count.add l r)

theorem trackCount_eq_zero_iff {n : ℕ} (i : Fin n)
    (t : BinTree (A × TrackBits n)) :
    trackCount i t = Count.zero ↔
      ∀ p : t.Pos, (t.labelAt p).2 i = false := by
  induction t with
  | nil =>
      constructor
      · intro _ p
        exact p.elim
      · intro _
        rfl
  | node a l r ihl ihr =>
      change
        Count.addMark (a.2 i) (Count.add (trackCount i l) (trackCount i r)) =
            Count.zero ↔
          ∀ p : Option (l.Pos ⊕ r.Pos),
            ((BinTree.node a l r).labelAt p).2 i = false
      rw [Count.addMark_eq_zero_iff, Count.add_eq_zero_iff, ihl, ihr]
      constructor
      · rintro ⟨hroot, hleft, hright⟩ p
        cases p with
        | none => exact hroot
        | some q =>
            cases q with
            | inl p => exact hleft p
            | inr p => exact hright p
      · intro h
        exact ⟨h none, fun p => h (some (.inl p)), fun p => h (some (.inr p))⟩

theorem trackCount_eq_one_iff_exists_unique {n : ℕ} (i : Fin n)
    (t : BinTree (A × TrackBits n)) :
    trackCount i t = Count.one ↔
      ∃ p : t.Pos, (t.labelAt p).2 i = true ∧
        ∀ q : t.Pos, (t.labelAt q).2 i = true → q = p := by
  induction t with
  | nil =>
      constructor
      · intro h
        simp [trackCount] at h
      · rintro ⟨p, _, _⟩
        exact p.elim
  | node a l r ihl ihr =>
      change
        Count.addMark (a.2 i) (Count.add (trackCount i l) (trackCount i r)) =
            Count.one ↔
          ∃ p : Option (l.Pos ⊕ r.Pos),
            ((BinTree.node a l r).labelAt p).2 i = true ∧
              ∀ q : Option (l.Pos ⊕ r.Pos),
                ((BinTree.node a l r).labelAt q).2 i = true → q = p
      rw [Count.addMark_eq_one_iff]
      constructor
      · rintro (⟨hroot, hchildren⟩ | ⟨hroot, hchildren⟩)
        · rw [Count.add_eq_zero_iff,
            trackCount_eq_zero_iff i l, trackCount_eq_zero_iff i r] at hchildren
          refine ⟨none, hroot, ?_⟩
          intro q hq
          cases q with
          | none => rfl
          | some q' =>
              cases q' with
              | inl p =>
                  have hpfalse := hchildren.1 p
                  have hq' : (l.labelAt p).2 i = true := by simpa using hq
                  rw [hpfalse] at hq'
                  cases hq'
              | inr p =>
                  have hpfalse := hchildren.2 p
                  have hq' : (r.labelAt p).2 i = true := by simpa using hq
                  rw [hpfalse] at hq'
                  cases hq'
        · rw [Count.add_eq_one_iff] at hchildren
          rcases hchildren with ⟨hleftOne, hrightZero⟩ | ⟨hleftZero, hrightOne⟩
          · obtain ⟨p, hp, huniq⟩ := ihl.mp hleftOne
            have hrightNone := (trackCount_eq_zero_iff i r).mp hrightZero
            refine ⟨some (.inl p), hp, ?_⟩
            intro q hq
            cases q with
            | none =>
                have hq' : a.2 i = true := by simpa using hq
                rw [hroot] at hq'
                cases hq'
            | some q' =>
                cases q' with
                | inl q =>
                    have hq' : (l.labelAt q).2 i = true := by simpa using hq
                    rw [huniq q hq']
                | inr q =>
                    have hqfalse := hrightNone q
                    have hq' : (r.labelAt q).2 i = true := by simpa using hq
                    rw [hqfalse] at hq'
                    cases hq'
          · obtain ⟨p, hp, huniq⟩ := ihr.mp hrightOne
            have hleftNone := (trackCount_eq_zero_iff i l).mp hleftZero
            refine ⟨some (.inr p), hp, ?_⟩
            intro q hq
            cases q with
            | none =>
                have hq' : a.2 i = true := by simpa using hq
                rw [hroot] at hq'
                cases hq'
            | some q' =>
                cases q' with
                | inl q =>
                    have hqfalse := hleftNone q
                    have hq' : (l.labelAt q).2 i = true := by simpa using hq
                    rw [hqfalse] at hq'
                    cases hq'
                | inr q =>
                    have hq' : (r.labelAt q).2 i = true := by simpa using hq
                    rw [huniq q hq']
      · rintro ⟨p, hp, huniq⟩
        cases p with
        | none =>
            left
            refine ⟨hp, ?_⟩
            rw [Count.add_eq_zero_iff,
              trackCount_eq_zero_iff i l, trackCount_eq_zero_iff i r]
            constructor
            · intro q
              by_contra hq
              have hqtrue : (l.labelAt q).2 i = true := by
                cases hbit : (l.labelAt q).2 i <;> simp [hbit] at hq ⊢
              have hsome := huniq (some (.inl q)) hqtrue
              cases hsome
            · intro q
              by_contra hq
              have hqtrue : (r.labelAt q).2 i = true := by
                cases hbit : (r.labelAt q).2 i <;> simp [hbit] at hq ⊢
              have hsome := huniq (some (.inr q)) hqtrue
              cases hsome
        | some p' =>
            right
            refine ⟨?_, ?_⟩
            · by_contra hroot
              have hrootTrue : a.2 i = true := by
                cases hbit : a.2 i <;> simp [hbit] at hroot ⊢
              have hnone := huniq none hrootTrue
              cases hnone
            · cases p' with
              | inl p =>
                  rw [Count.add_eq_one_iff]
                  left
                  refine ⟨?_, ?_⟩
                  · have hp' : (l.labelAt p).2 i = true := by simpa using hp
                    refine ihl.mpr ⟨p, hp', ?_⟩
                    intro q hq
                    have hsum : Sum.inl q = Sum.inl p :=
                      Option.some.inj (huniq (some (.inl q)) (by simpa using hq))
                    cases hsum
                    rfl
                  · rw [trackCount_eq_zero_iff]
                    intro q
                    by_contra hq
                    have hqtrue : (r.labelAt q).2 i = true := by
                      cases hbit : (r.labelAt q).2 i <;> simp [hbit] at hq ⊢
                    have hsome := huniq (some (.inr q)) (by simpa using hqtrue)
                    cases hsome
              | inr p =>
                  rw [Count.add_eq_one_iff]
                  right
                  refine ⟨?_, ?_⟩
                  · rw [trackCount_eq_zero_iff]
                    intro q
                    by_contra hq
                    have hqtrue : (l.labelAt q).2 i = true := by
                      cases hbit : (l.labelAt q).2 i <;> simp [hbit] at hq ⊢
                    have hsome := huniq (some (.inl q)) (by simpa using hqtrue)
                    cases hsome
                  · have hp' : (r.labelAt p).2 i = true := by simpa using hp
                    refine ihr.mpr ⟨p, hp', ?_⟩
                    intro q hq
                    have hsum : Sum.inr q = Sum.inr p :=
                      Option.some.inj (huniq (some (.inr q)) (by simpa using hq))
                    cases hsum
                    rfl

/-- Automaton accepting exactly the terms whose `i`-th track marks one node. -/
def trackSingletonAutomaton (A : Type u) {n : ℕ} (i : Fin n) :
    TreeAutomaton (paddedAlphabet (A × TrackBits n)) :=
  foldAutomaton Count.zero
    (fun a l r => Count.addMark (a.2 i) (Count.add l r))
    {c | c = Count.one}

@[simp] theorem language_trackSingletonAutomaton {n : ℕ} (i : Fin n) :
    (trackSingletonAutomaton A i).language =
      {t | trackCount (A := A) i (BinTree.ofTerm t) = Count.one} := by
  simp [trackSingletonAutomaton, trackCount]

theorem recognizable_trackSingleton (A : Type u) {n : ℕ} (i : Fin n) :
    (paddedAlphabet (A × TrackBits n)).Recognizable
      {t | trackCount (A := A) i (BinTree.ofTerm t) = Count.one} :=
  ⟨trackSingletonAutomaton A i, by simp⟩

/-- Does the `i`-th track hold at the root of the tree? -/
def rootTrack {n : ℕ} (i : Fin n) : BinTree (A × TrackBits n) → Bool :=
  fold false fun a _ _ => a.2 i

/-- Automaton accepting terms whose root carries track `i`. -/
def rootTrackAutomaton (A : Type u) {n : ℕ} (i : Fin n) :
    TreeAutomaton (paddedAlphabet (A × TrackBits n)) :=
  foldAutomaton false (fun a _ _ => a.2 i) {b | b = true}

@[simp] theorem language_rootTrackAutomaton {n : ℕ} (i : Fin n) :
    (rootTrackAutomaton A i).language =
      {t | rootTrack (A := A) i (BinTree.ofTerm t) = true} := by
  simp [rootTrackAutomaton, rootTrack]

theorem recognizable_rootTrack (A : Type u) {n : ℕ} (i : Fin n) :
    (paddedAlphabet (A × TrackBits n)).Recognizable
      {t | rootTrack (A := A) i (BinTree.ofTerm t) = true} :=
  ⟨rootTrackAutomaton A i, by simp⟩

theorem rootTrack_eq_true_iff {n : ℕ} (i : Fin n)
    (t : BinTree (A × TrackBits n)) :
    rootTrack i t = true ↔
      ∃ p : t.Pos, t.IsRootPos p ∧ (t.labelAt p).2 i = true := by
  cases t with
  | nil =>
      constructor
      · intro h
        simp [rootTrack] at h
      · rintro ⟨p, _, _⟩
        exact p.elim
  | node a l r =>
      constructor
      · intro h
        exact ⟨none, rfl, h⟩
      · rintro ⟨p, hroot, hbit⟩
        cases p with
        | none => exact hbit
        | some q => cases hroot

/-- Do the two tracks intersect at some node? -/
def tracksIntersect {n : ℕ} (i j : Fin n) :
    BinTree (A × TrackBits n) → Bool :=
  fold false fun a l r => (a.2 i && a.2 j) || l || r

/-- Automaton accepting terms whose `i` and `j` tracks intersect. -/
def tracksIntersectAutomaton (A : Type u) {n : ℕ} (i j : Fin n) :
    TreeAutomaton (paddedAlphabet (A × TrackBits n)) :=
  foldAutomaton false
    (fun a l r => (a.2 i && a.2 j) || l || r)
    {b | b = true}

@[simp] theorem language_tracksIntersectAutomaton {n : ℕ} (i j : Fin n) :
    (tracksIntersectAutomaton A i j).language =
      {t | tracksIntersect (A := A) i j (BinTree.ofTerm t) = true} := by
  simp [tracksIntersectAutomaton, tracksIntersect]

theorem recognizable_tracksIntersect (A : Type u) {n : ℕ} (i j : Fin n) :
    (paddedAlphabet (A × TrackBits n)).Recognizable
      {t | tracksIntersect (A := A) i j (BinTree.ofTerm t) = true} :=
  ⟨tracksIntersectAutomaton A i j, by simp⟩

theorem tracksIntersect_eq_true_iff {n : ℕ} (i j : Fin n)
    (t : BinTree (A × TrackBits n)) :
    tracksIntersect i j t = true ↔
      ∃ p : t.Pos, (t.labelAt p).2 i = true ∧ (t.labelAt p).2 j = true := by
  induction t with
  | nil =>
      constructor
      · intro h
        simp [tracksIntersect] at h
      · rintro ⟨p, _, _⟩
        exact p.elim
  | node a l r ihl ihr =>
      rw [tracksIntersect, fold_node]
      rw [show fold false (fun a l r => (a.2 i && a.2 j) || l || r) l =
          tracksIntersect i j l by rfl,
        show fold false (fun a l r => (a.2 i && a.2 j) || l || r) r =
          tracksIntersect i j r by rfl]
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, ihl, ihr]
      constructor
      · rintro ((⟨hi, hj⟩ | ⟨p, hp⟩) | ⟨p, hp⟩)
        · exact ⟨none, hi, hj⟩
        · exact ⟨some (.inl p), hp⟩
        · exact ⟨some (.inr p), hp⟩
      · rintro ⟨p, hp⟩
        cases p with
        | none =>
            left
            left
            exact hp
        | some q =>
            cases q with
            | inl p =>
                left
                right
                exact ⟨p, hp⟩
            | inr p =>
                right
                exact ⟨p, hp⟩

/-! ## Erasing tracks in position semantics -/

/-- The canonical position equivalence between a tracked tree and the tree
obtained by erasing all tracks. -/
def erasePosEquiv {n : ℕ} (t : BinTree (A × TrackBits n)) :
    t.Pos ≃ t.eraseTracks.Pos :=
  posEquivMap Prod.fst t

/-- A Boolean track read as a set of positions in the track-erased tree. -/
def trackSetErased {n : ℕ} (t : BinTree (A × TrackBits n)) (i : Fin n) :
    Set t.eraseTracks.Pos :=
  erasePosEquiv t '' trackSet t i

theorem mem_trackSetErased_iff {n : ℕ} (t : BinTree (A × TrackBits n))
    (i : Fin n) (p : t.eraseTracks.Pos) :
    p ∈ trackSetErased t i ↔
      ∃ q : t.Pos, (t.labelAt q).2 i = true ∧ erasePosEquiv t q = p :=
  Iff.rfl

theorem trackCount_eq_one_iff_exists_unique_erased {n : ℕ} (i : Fin n)
    (t : BinTree (A × TrackBits n)) :
    trackCount i t = Count.one ↔
      ∃ p : t.eraseTracks.Pos, p ∈ trackSetErased t i ∧
        ∀ q : t.eraseTracks.Pos, q ∈ trackSetErased t i → q = p := by
  constructor
  · intro h
    obtain ⟨p, hp, huniq⟩ := (trackCount_eq_one_iff_exists_unique i t).mp h
    refine ⟨erasePosEquiv t p, ⟨p, hp, rfl⟩, ?_⟩
    intro q hq
    obtain ⟨r, hr, hrq⟩ := (mem_trackSetErased_iff t i q).mp hq
    have hrp : r = p := huniq r hr
    rw [← hrq, hrp]
  · rintro ⟨p, hp, huniq⟩
    obtain ⟨q, hq, hqp⟩ := (mem_trackSetErased_iff t i p).mp hp
    refine (trackCount_eq_one_iff_exists_unique i t).mpr ⟨q, hq, ?_⟩
    intro r hr
    have hmemr : erasePosEquiv t r ∈ trackSetErased t i :=
      ⟨r, hr, rfl⟩
    have heq : erasePosEquiv t r = p := huniq (erasePosEquiv t r) hmemr
    exact (erasePosEquiv t).injective (heq.trans hqp.symm)

theorem tracksIntersect_eq_true_iff_exists_erased {n : ℕ} (i j : Fin n)
    (t : BinTree (A × TrackBits n)) :
    tracksIntersect i j t = true ↔
      ∃ p : t.eraseTracks.Pos, p ∈ trackSetErased t i ∧
        p ∈ trackSetErased t j := by
  constructor
  · intro h
    obtain ⟨q, hi, hj⟩ := (tracksIntersect_eq_true_iff i j t).mp h
    refine ⟨erasePosEquiv t q, ?_, ?_⟩
    · exact ⟨q, hi, rfl⟩
    · exact ⟨q, hj, rfl⟩
  · rintro ⟨p, hi, hj⟩
    obtain ⟨q, hqi, hq⟩ := (mem_trackSetErased_iff t i p).mp hi
    obtain ⟨r, hrj, hr⟩ := (mem_trackSetErased_iff t j p).mp hj
    have hqr : q = r := (erasePosEquiv t).injective (hq.trans hr.symm)
    exact (tracksIntersect_eq_true_iff i j t).mpr
      ⟨q, hqi, by simpa [hqr] using hrj⟩

/-! ## Parent relation between marked tracks -/

/-- Summary for the parent atom: whether the subtree root carries the child
track, and whether a witness edge has already been seen. -/
abbrev ParentSummary := Bool × Bool

/-- Bottom-up summary for the existence of a parent-child edge from track
`parent` to track `child`. -/
def parentTrackSummary {n : ℕ} (parent child : Fin n) :
    BinTree (A × TrackBits n) → ParentSummary :=
  fold (false, false) fun a l r =>
    let rootChild := a.2 child
    let found :=
      l.2 || r.2 || (a.2 parent && l.1) || (a.2 parent && r.1)
    (rootChild, found)

/-- Automaton accepting terms with an edge whose parent node carries
`parent` and whose child node carries `child`. -/
def parentTrackAutomaton (A : Type u) {n : ℕ} (parent child : Fin n) :
    TreeAutomaton (paddedAlphabet (A × TrackBits n)) :=
  foldAutomaton (false, false)
    (fun a l r =>
      let rootChild := a.2 child
      let found :=
        l.2 || r.2 || (a.2 parent && l.1) || (a.2 parent && r.1)
      (rootChild, found))
    {s | s.2 = true}

@[simp] theorem language_parentTrackAutomaton {n : ℕ} (parent child : Fin n) :
    (parentTrackAutomaton A parent child).language =
      {t | (parentTrackSummary (A := A) parent child (BinTree.ofTerm t)).2 = true} := by
  simp [parentTrackAutomaton, parentTrackSummary]

theorem recognizable_parentTrack (A : Type u) {n : ℕ} (parent child : Fin n) :
    (paddedAlphabet (A × TrackBits n)).Recognizable
      {t | (parentTrackSummary (A := A) parent child (BinTree.ofTerm t)).2 = true} :=
  ⟨parentTrackAutomaton A parent child, by simp⟩

theorem parentTrackSummary_root_iff {n : ℕ} (parent child : Fin n)
    (t : BinTree (A × TrackBits n)) :
    (parentTrackSummary parent child t).1 = true ↔
      ∃ p : t.Pos, t.IsRootPos p ∧ (t.labelAt p).2 child = true := by
  cases t with
  | nil =>
      constructor
      · intro h
        simp [parentTrackSummary] at h
      · rintro ⟨p, _, _⟩
        exact p.elim
  | node a l r =>
      constructor
      · intro h
        exact ⟨none, rfl, h⟩
      · rintro ⟨p, hroot, hbit⟩
        cases p with
        | none => exact hbit
        | some q => cases hroot

theorem parentTrackSummary_found_iff {n : ℕ} (parent child : Fin n)
    (t : BinTree (A × TrackBits n)) :
    (parentTrackSummary parent child t).2 = true ↔
      ∃ p q : t.Pos,
        (t.labelAt p).2 parent = true ∧
        (t.labelAt q).2 child = true ∧
        (t.childRel false p q ∨ t.childRel true p q) := by
  induction t with
  | nil =>
      constructor
      · intro h
        simp [parentTrackSummary] at h
      · rintro ⟨p, _, _, _, _⟩
        exact p.elim
  | node a l r ihl ihr =>
      change
        ((parentTrackSummary parent child l).2 ||
            (parentTrackSummary parent child r).2 ||
            (a.2 parent && (parentTrackSummary parent child l).1) ||
            (a.2 parent && (parentTrackSummary parent child r).1)) = true ↔
          ∃ p q : Option (l.Pos ⊕ r.Pos),
            ((BinTree.node a l r).labelAt p).2 parent = true ∧
            ((BinTree.node a l r).labelAt q).2 child = true ∧
            ((BinTree.node a l r).childRel false p q ∨
              (BinTree.node a l r).childRel true p q)
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true,
        Bool.and_eq_true, Bool.and_eq_true, ihl, ihr,
        parentTrackSummary_root_iff parent child l,
        parentTrackSummary_root_iff parent child r]
      constructor
      · rintro (((⟨p, q, hp, hq, hrel⟩ | ⟨p, q, hp, hq, hrel⟩) |
            ⟨hp, q, hqroot, hq⟩) | ⟨hp, q, hqroot, hq⟩)
        · refine ⟨some (.inl p), some (.inl q), hp, hq, ?_⟩
          rcases hrel with hrel | hrel
          · exact Or.inl hrel
          · exact Or.inr hrel
        · refine ⟨some (.inr p), some (.inr q), hp, hq, ?_⟩
          rcases hrel with hrel | hrel
          · exact Or.inl hrel
          · exact Or.inr hrel
        · exact ⟨none, some (.inl q), hp, hq, Or.inl ⟨rfl, hqroot⟩⟩
        · exact ⟨none, some (.inr q), hp, hq, Or.inr ⟨rfl, hqroot⟩⟩
      · rintro ⟨p, q, hp, hq, hrel⟩
        cases p with
        | none =>
            cases q with
            | none =>
                rcases hrel with hrel | hrel <;> cases hrel
            | some q' =>
                cases q' with
                | inl ql =>
                    left
                    right
                    refine ⟨hp, ql, ?_, hq⟩
                    rcases hrel with hrel | hrel
                    · exact hrel.2
                    · cases hrel.1
                | inr qr =>
                    right
                    refine ⟨hp, qr, ?_, hq⟩
                    rcases hrel with hrel | hrel
                    · cases hrel.1
                    · exact hrel.2
        | some p' =>
            cases p' with
            | inl pl =>
                cases q with
                | none =>
                    rcases hrel with hrel | hrel <;> cases hrel
                | some q' =>
                    cases q' with
                    | inl ql =>
                        left
                        left
                        left
                        exact ⟨pl, ql, hp, hq, hrel⟩
                    | inr qr =>
                        rcases hrel with hrel | hrel <;> cases hrel
            | inr pr =>
                cases q with
                | none =>
                    rcases hrel with hrel | hrel <;> cases hrel
                | some q' =>
                    cases q' with
                    | inl ql =>
                        rcases hrel with hrel | hrel <;> cases hrel
                    | inr qr =>
                        left
                        left
                        right
                        exact ⟨pr, qr, hp, hq, hrel⟩

theorem parentTrackSummary_found_iff_exists_erased {n : ℕ}
    (parent child : Fin n) (t : BinTree (A × TrackBits n)) :
    (parentTrackSummary parent child t).2 = true ↔
      ∃ p q : t.eraseTracks.Pos,
        p ∈ trackSetErased t parent ∧
        q ∈ trackSetErased t child ∧
        (t.eraseTracks.childRel false p q ∨
          t.eraseTracks.childRel true p q) := by
  rw [parentTrackSummary_found_iff]
  constructor
  · rintro ⟨p, q, hp, hq, hrel⟩
    refine ⟨erasePosEquiv t p, erasePosEquiv t q,
      ⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩, ?_⟩
    rcases hrel with hrel | hrel
    · left
      exact (childRel_map_iff Prod.fst false t p q).mpr hrel
    · right
      exact (childRel_map_iff Prod.fst true t p q).mpr hrel
  · rintro ⟨p, q, hp, hq, hrel⟩
    obtain ⟨p', hp', hpe⟩ := (mem_trackSetErased_iff t parent p).mp hp
    obtain ⟨q', hq', hqe⟩ := (mem_trackSetErased_iff t child q).mp hq
    refine ⟨p', q', hp', hq', ?_⟩
    rcases hrel with hrel | hrel
    · left
      have hrel' :
          t.eraseTracks.childRel false (erasePosEquiv t p') (erasePosEquiv t q') := by
        rwa [hpe, hqe]
      exact (childRel_map_iff Prod.fst false t p' q').mp hrel'
    · right
      have hrel' :
          t.eraseTracks.childRel true (erasePosEquiv t p') (erasePosEquiv t q') := by
        rwa [hpe, hqe]
      exact (childRel_map_iff Prod.fst true t p' q').mp hrel'

/-! ## Labels seen on tracks -/

/-- The set of base labels occurring at nodes whose `i`-th track is on. -/
def labelsOnTrack {n : ℕ} (i : Fin n) :
    BinTree (A × TrackBits n) → Set A :=
  fold ∅ fun a l r =>
    (if a.2 i = true then {a.1} else ∅) ∪ l ∪ r

theorem mem_labelsOnTrack_iff {n : ℕ} (i : Fin n)
    (t : BinTree (A × TrackBits n)) (a : A) :
    a ∈ labelsOnTrack i t ↔
      ∃ p : t.Pos, (t.labelAt p).2 i = true ∧ (t.labelAt p).1 = a := by
  induction t with
  | nil =>
      constructor
      · intro h
        simp [labelsOnTrack] at h
      · rintro ⟨p, _, _⟩
        exact p.elim
  | node x l r ihl ihr =>
      change
        a ∈ ((if x.2 i = true then {x.1} else ∅) ∪
            labelsOnTrack i l ∪ labelsOnTrack i r) ↔
          ∃ p : Option (l.Pos ⊕ r.Pos),
            ((BinTree.node x l r).labelAt p).2 i = true ∧
              ((BinTree.node x l r).labelAt p).1 = a
      constructor
      · intro h
        rw [Set.mem_union] at h
        rcases h with hrootLeft | hright
        · rw [Set.mem_union] at hrootLeft
          rcases hrootLeft with hroot | hleft
          · by_cases hx : x.2 i = true
            · have ha : a = x.1 := by simpa [hx] using hroot
              exact ⟨none, hx, ha.symm⟩
            · simp [hx] at hroot
          · obtain ⟨p, hp, hpa⟩ := ihl.mp hleft
            exact ⟨some (.inl p), hp, hpa⟩
        · obtain ⟨p, hp, hpa⟩ := ihr.mp hright
          exact ⟨some (.inr p), hp, hpa⟩
      · rintro ⟨p, hp, hpa⟩
        cases p with
        | none =>
            rw [Set.mem_union]
            left
            rw [Set.mem_union]
            left
            by_cases hx : x.2 i = true
            · simpa [hx] using hpa.symm
            · exact False.elim (hx (by simpa using hp))
        | some q =>
            cases q with
            | inl p =>
                rw [Set.mem_union]
                left
                rw [Set.mem_union]
                right
                exact ihl.mpr ⟨p, hp, hpa⟩
            | inr p =>
                rw [Set.mem_union]
                right
                exact ihr.mpr ⟨p, hp, hpa⟩

/-- Automaton computing the set of labels seen on track `i`. -/
def labelsOnTrackAutomaton (A : Type) [Finite A] {n : ℕ} (i : Fin n)
    (accept : Set (Set A)) :
    TreeAutomaton (paddedAlphabet (A × TrackBits n)) :=
  foldAutomaton ∅
    (fun a l r => (if a.2 i = true then {a.1} else ∅) ∪ l ∪ r)
    accept

@[simp] theorem language_labelsOnTrackAutomaton {A : Type} [Finite A] {n : ℕ}
    (i : Fin n) (accept : Set (Set A)) :
    (labelsOnTrackAutomaton A i accept).language =
      {t | labelsOnTrack i (BinTree.ofTerm t) ∈ accept} := by
  simp [labelsOnTrackAutomaton, labelsOnTrack]

/-- Automaton for the atomic label predicate at a marked first-order track. -/
def labelMemTrackAutomaton (A : Type) [Finite A] {n : ℕ}
    (i : Fin n) (S : Set A) :
    TreeAutomaton (paddedAlphabet (A × TrackBits n)) :=
  labelsOnTrackAutomaton A i {U | ∃ a ∈ U, a ∈ S}

@[simp] theorem language_labelMemTrackAutomaton {A : Type} [Finite A] {n : ℕ}
    (i : Fin n) (S : Set A) :
    (labelMemTrackAutomaton A i S).language =
      {t | ∃ a ∈ labelsOnTrack i (BinTree.ofTerm t), a ∈ S} := by
  simp [labelMemTrackAutomaton]

theorem recognizable_labelMemTrack (A : Type) [Finite A] {n : ℕ}
    (i : Fin n) (S : Set A) :
    (paddedAlphabet (A × TrackBits n)).Recognizable
      {t | ∃ a ∈ labelsOnTrack i (BinTree.ofTerm t), a ∈ S} :=
  ⟨labelMemTrackAutomaton A i S, by simp⟩

/-- The pair of label sets seen on two tracks. -/
def labelPairSummary {n : ℕ} (i j : Fin n) :
    BinTree (A × TrackBits n) → Set A × Set A :=
  fold (∅, ∅) fun a l r =>
    let left : Set A := if a.2 i = true then {a.1} else ∅
    let right : Set A := if a.2 j = true then {a.1} else ∅
    (left ∪ l.1 ∪ r.1, right ∪ l.2 ∪ r.2)

theorem labelPairSummary_fst {n : ℕ} (i j : Fin n)
    (t : BinTree (A × TrackBits n)) :
    (labelPairSummary i j t).1 = labelsOnTrack i t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      change
        (if a.2 i = true then {a.1} else ∅) ∪
            (labelPairSummary i j l).1 ∪ (labelPairSummary i j r).1 =
          (if a.2 i = true then {a.1} else ∅) ∪
            labelsOnTrack i l ∪ labelsOnTrack i r
      rw [ihl, ihr]

theorem labelPairSummary_snd {n : ℕ} (i j : Fin n)
    (t : BinTree (A × TrackBits n)) :
    (labelPairSummary i j t).2 = labelsOnTrack j t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      change
        (if a.2 j = true then {a.1} else ∅) ∪
            (labelPairSummary i j l).2 ∪ (labelPairSummary i j r).2 =
          (if a.2 j = true then {a.1} else ∅) ∪
            labelsOnTrack j l ∪ labelsOnTrack j r
      rw [ihl, ihr]

/-- Automaton computing the pair of label sets seen on two tracks. -/
def labelPairAutomaton (A : Type) [Finite A] {n : ℕ}
    (i j : Fin n) (accept : Set (Set A × Set A)) :
    TreeAutomaton (paddedAlphabet (A × TrackBits n)) :=
  foldAutomaton (∅, ∅)
    (fun a l r =>
      let left : Set A := if a.2 i = true then {a.1} else ∅
      let right : Set A := if a.2 j = true then {a.1} else ∅
      (left ∪ l.1 ∪ r.1, right ∪ l.2 ∪ r.2))
    accept

@[simp] theorem language_labelPairAutomaton {A : Type} [Finite A] {n : ℕ}
    (i j : Fin n) (accept : Set (Set A × Set A)) :
    (labelPairAutomaton A i j accept).language =
      {t | labelPairSummary (A := A) i j (BinTree.ofTerm t) ∈ accept} := by
  simp [labelPairAutomaton, labelPairSummary]

/-- Automaton for the binary letter-pair predicate at two marked first-order
tracks. -/
def labelMem₂TrackAutomaton (A : Type) [Finite A] {n : ℕ}
    (i j : Fin n) (R : Set (A × A)) :
    TreeAutomaton (paddedAlphabet (A × TrackBits n)) :=
  labelPairAutomaton A i j {p | ∃ a ∈ p.1, ∃ b ∈ p.2, (a, b) ∈ R}

@[simp] theorem language_labelMem₂TrackAutomaton {A : Type} [Finite A] {n : ℕ}
    (i j : Fin n) (R : Set (A × A)) :
    (labelMem₂TrackAutomaton A i j R).language =
      {t |
        let p := labelPairSummary (A := A) i j (BinTree.ofTerm t)
        ∃ a ∈ p.1, ∃ b ∈ p.2, (a, b) ∈ R} := by
  simp [labelMem₂TrackAutomaton]

theorem recognizable_labelMem₂Track (A : Type) [Finite A] {n : ℕ}
    (i j : Fin n) (R : Set (A × A)) :
    (paddedAlphabet (A × TrackBits n)).Recognizable
      {t |
        let p := labelPairSummary (A := A) i j (BinTree.ofTerm t)
        ∃ a ∈ p.1, ∃ b ∈ p.2, (a, b) ∈ R} :=
  ⟨labelMem₂TrackAutomaton A i j R, by simp⟩

/-! ## Connection to tree-language assignments -/

open GraphMSO.TreeLanguage

/-- A tracked tree carries a tree-language assignment when first-order and
second-order variables are read from the chosen Boolean tracks after erasing
the extra Boolean component from labels. -/
def CarriesAssignment {n : ℕ} (t : BinTree (A × TrackBits n))
    (foTrack : FOVar → Fin n) (soTrack : SOVar → Fin n)
    (ρ : Assignment t.eraseTracks.toTreeModel) : Prop :=
  (∀ x p, ρ.fo x = some p ↔ p ∈ trackSetErased t (foTrack x)) ∧
    (∀ X, ρ.so X = trackSetErased t (soTrack X))

namespace CarriesAssignment

variable {n : ℕ} {t : BinTree (A × TrackBits n)}
  {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
  {ρ : Assignment t.eraseTracks.toTreeModel}

theorem fo_iff (h : CarriesAssignment t foTrack soTrack ρ)
    (x : FOVar) (p : t.eraseTracks.Pos) :
    ρ.fo x = some p ↔ p ∈ trackSetErased t (foTrack x) :=
  h.1 x p

theorem so_eq (h : CarriesAssignment t foTrack soTrack ρ)
    (X : SOVar) :
    ρ.so X = trackSetErased t (soTrack X) :=
  h.2 X

theorem updateFO {oldFO : FOVar → Fin n}
    (h : CarriesAssignment t oldFO soTrack ρ)
    {newFO : FOVar → Fin n} {x : FOVar} {p : t.eraseTracks.Pos}
    (hfo : ∀ y, y ≠ x → newFO y = oldFO y)
    (hmem : p ∈ trackSetErased t (newFO x))
    (huniq : ∀ q : t.eraseTracks.Pos,
      q ∈ trackSetErased t (newFO x) → q = p) :
    CarriesAssignment t newFO soTrack (ρ.updateFO x p) := by
  constructor
  · intro y q
    by_cases hy : y = x
    · subst hy
      constructor
      · intro hq
        rw [Assignment.updateFO_here] at hq
        have hqp : p = q := Option.some.inj hq
        simpa [hqp] using hmem
      · intro hq
        rw [huniq q hq]
        simp [Assignment.updateFO]
    · rw [Assignment.updateFO_other ρ p hy]
      rw [hfo y hy]
      exact h.fo_iff y q
  · intro X
    exact h.so_eq X

theorem updateSO {oldSO : SOVar → Fin n}
    (h : CarriesAssignment t foTrack oldSO ρ)
    {newSO : SOVar → Fin n} {X : SOVar} {S : Set t.eraseTracks.Pos}
    (hso : ∀ Y, Y ≠ X → newSO Y = oldSO Y)
    (hX : S = trackSetErased t (newSO X)) :
    CarriesAssignment t foTrack newSO (ρ.updateSO X S) := by
  constructor
  · intro x p
    exact h.fo_iff x p
  · intro Y
    by_cases hY : Y = X
    · subst hY
      rw [Assignment.updateSO_here, hX]
    · rw [Assignment.updateSO_other ρ S hY, hso Y hY]
      exact h.so_eq Y

end CarriesAssignment

theorem exists_label_on_track_iff_exists_erased {n : ℕ}
    (t : BinTree (A × TrackBits n)) (i : Fin n) (S : Set A) :
    (∃ a ∈ labelsOnTrack i t, a ∈ S) ↔
      ∃ p : t.eraseTracks.Pos, p ∈ trackSetErased t i ∧
        t.eraseTracks.labelAt p ∈ S := by
  constructor
  · rintro ⟨a, ha, hS⟩
    obtain ⟨q, hq, hqa⟩ := (mem_labelsOnTrack_iff i t a).mp ha
    refine ⟨erasePosEquiv t q, ⟨q, hq, rfl⟩, ?_⟩
    have hlabel :
        t.eraseTracks.labelAt (erasePosEquiv t q) = (t.labelAt q).1 := by
      simp [eraseTracks, erasePosEquiv]
    rw [hlabel, hqa]
    exact hS
  · rintro ⟨p, hp, hS⟩
    obtain ⟨q, hq, hpq⟩ := (mem_trackSetErased_iff t i p).mp hp
    refine ⟨(t.labelAt q).1, ?_, ?_⟩
    · exact (mem_labelsOnTrack_iff i t (t.labelAt q).1).mpr ⟨q, hq, rfl⟩
    · have hlabel :
          t.eraseTracks.labelAt (erasePosEquiv t q) = (t.labelAt q).1 := by
        simp [eraseTracks, erasePosEquiv]
      rwa [← hpq, hlabel] at hS

theorem satisfiesAt_equal_iff_tracksIntersect {n : ℕ}
    (t : BinTree (A × TrackBits n)) (foTrack : FOVar → Fin n)
    (soTrack : SOVar → Fin n) (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t foTrack soTrack ρ) (x y : FOVar) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel (Formula.equal x y) ρ ↔
      tracksIntersect (foTrack x) (foTrack y) t = true := by
  rw [Semantics.SatisfiesAt, tracksIntersect_eq_true_iff_exists_erased]
  constructor
  · rintro ⟨p, hx, hy⟩
    exact ⟨p, (hρ.fo_iff x p).mp hx, (hρ.fo_iff y p).mp hy⟩
  · rintro ⟨p, hx, hy⟩
    exact ⟨p, (hρ.fo_iff x p).mpr hx, (hρ.fo_iff y p).mpr hy⟩

theorem satisfiesAt_inSet_iff_tracksIntersect {n : ℕ}
    (t : BinTree (A × TrackBits n)) (foTrack : FOVar → Fin n)
    (soTrack : SOVar → Fin n) (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t foTrack soTrack ρ) (x : FOVar) (X : SOVar) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel (Formula.inSet x X) ρ ↔
      tracksIntersect (foTrack x) (soTrack X) t = true := by
  rw [Semantics.SatisfiesAt, tracksIntersect_eq_true_iff_exists_erased,
    hρ.so_eq X]
  constructor
  · rintro ⟨p, hx, hX⟩
    exact ⟨p, (hρ.fo_iff x p).mp hx, hX⟩
  · rintro ⟨p, hx, hX⟩
    exact ⟨p, (hρ.fo_iff x p).mpr hx, hX⟩

theorem satisfiesAt_parent_iff_parentTrackSummary {n : ℕ}
    (t : BinTree (A × TrackBits n)) (foTrack : FOVar → Fin n)
    (soTrack : SOVar → Fin n) (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t foTrack soTrack ρ) (y x : FOVar) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel (Formula.parent y x) ρ ↔
      (parentTrackSummary (foTrack y) (foTrack x) t).2 = true := by
  rw [Semantics.SatisfiesAt,
    parentTrackSummary_found_iff_exists_erased (foTrack y) (foTrack x) t]
  constructor
  · rintro ⟨p, q, hp, hq, hrel⟩
    exact ⟨p, q, (hρ.fo_iff y p).mp hp, (hρ.fo_iff x q).mp hq, hrel⟩
  · rintro ⟨p, q, hp, hq, hrel⟩
    exact ⟨p, q, (hρ.fo_iff y p).mpr hp, (hρ.fo_iff x q).mpr hq, hrel⟩

theorem satisfiesAt_labelMem_iff_labelsOnTrack {n : ℕ}
    (t : BinTree (A × TrackBits n)) (foTrack : FOVar → Fin n)
    (soTrack : SOVar → Fin n) (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t foTrack soTrack ρ) (S : Set A) (x : FOVar) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel (Formula.labelMem S x) ρ ↔
      ∃ a ∈ labelsOnTrack (foTrack x) t, a ∈ S := by
  rw [Semantics.SatisfiesAt, exists_label_on_track_iff_exists_erased]
  constructor
  · rintro ⟨p, hx, hpS⟩
    exact ⟨p, (hρ.fo_iff x p).mp hx, hpS⟩
  · rintro ⟨p, hp, hpS⟩
    exact ⟨p, (hρ.fo_iff x p).mpr hp, hpS⟩

theorem satisfiesAt_labelMem₂_iff_labelPairSummary {n : ℕ}
    (t : BinTree (A × TrackBits n)) (foTrack : FOVar → Fin n)
    (soTrack : SOVar → Fin n) (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t foTrack soTrack ρ) (R : Set (A × A))
    (x y : FOVar) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel (Formula.labelMem₂ R x y) ρ ↔
      ∃ a ∈ (labelPairSummary (foTrack x) (foTrack y) t).1,
        ∃ b ∈ (labelPairSummary (foTrack x) (foTrack y) t).2, (a, b) ∈ R := by
  rw [Semantics.SatisfiesAt]
  constructor
  · rintro ⟨px, py, hx, hy, hR⟩
    obtain ⟨qx, hqx, hqxeq⟩ :=
      (mem_trackSetErased_iff t (foTrack x) px).mp ((hρ.fo_iff x px).mp hx)
    obtain ⟨qy, hqy, hqyeq⟩ :=
      (mem_trackSetErased_iff t (foTrack y) py).mp ((hρ.fo_iff y py).mp hy)
    refine ⟨(t.labelAt qx).1, ?_, (t.labelAt qy).1, ?_, ?_⟩
    · rw [labelPairSummary_fst]
      exact (mem_labelsOnTrack_iff (foTrack x) t (t.labelAt qx).1).mpr
        ⟨qx, hqx, rfl⟩
    · rw [labelPairSummary_snd]
      exact (mem_labelsOnTrack_iff (foTrack y) t (t.labelAt qy).1).mpr
        ⟨qy, hqy, rfl⟩
    · have hxLabel : t.eraseTracks.labelAt px = (t.labelAt qx).1 := by
        rw [← hqxeq]
        simp [eraseTracks, erasePosEquiv]
      have hyLabel : t.eraseTracks.labelAt py = (t.labelAt qy).1 := by
        rw [← hqyeq]
        simp [eraseTracks, erasePosEquiv]
      simpa [hxLabel, hyLabel] using hR
  · rintro ⟨a, ha, b, hb, hR⟩
    rw [labelPairSummary_fst] at ha
    rw [labelPairSummary_snd] at hb
    obtain ⟨qx, hqx, hqa⟩ := (mem_labelsOnTrack_iff (foTrack x) t a).mp ha
    obtain ⟨qy, hqy, hqb⟩ := (mem_labelsOnTrack_iff (foTrack y) t b).mp hb
    let px : t.eraseTracks.Pos := erasePosEquiv t qx
    let py : t.eraseTracks.Pos := erasePosEquiv t qy
    refine ⟨px, py, ?_, ?_, ?_⟩
    · exact (hρ.fo_iff x px).mpr ⟨qx, hqx, rfl⟩
    · exact (hρ.fo_iff y py).mpr ⟨qy, hqy, rfl⟩
    · have hxLabel : t.eraseTracks.labelAt px = a := by
        change t.eraseTracks.labelAt (erasePosEquiv t qx) = a
        rw [show t.eraseTracks.labelAt (erasePosEquiv t qx) =
            (t.labelAt qx).1 by simp [eraseTracks, erasePosEquiv], hqa]
      have hyLabel : t.eraseTracks.labelAt py = b := by
        change t.eraseTracks.labelAt (erasePosEquiv t qy) = b
        rw [show t.eraseTracks.labelAt (erasePosEquiv t qy) =
            (t.labelAt qy).1 by simp [eraseTracks, erasePosEquiv], hqb]
      simpa [hxLabel, hyLabel] using hR

end Automata

end BinTree
