import GraphMSO.Automata.automaton
import GraphMSO.Automata.binTree
import GraphMSO.treeLanguage.modelIso

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

@[simp] theorem trackSetErased_node_root {n : ℕ}
    (a : A × TrackBits n) (l r : BinTree (A × TrackBits n)) (i : Fin n) :
    (none : (BinTree.node a l r).eraseTracks.Pos) ∈
        trackSetErased (BinTree.node a l r) i ↔
      a.2 i = true := by
  rw [mem_trackSetErased_iff]
  constructor
  · rintro ⟨q, hq, hqp⟩
    cases q with
    | none =>
        simpa using hq
    | some q =>
        cases q with
        | inl q => cases hqp
        | inr q => cases hqp
  · intro h
    exact ⟨none, by simpa using h, rfl⟩

@[simp] theorem trackSetErased_node_left {n : ℕ}
    (a : A × TrackBits n) (l r : BinTree (A × TrackBits n)) (i : Fin n)
    (p : l.eraseTracks.Pos) :
    (some (.inl p) : (BinTree.node a l r).eraseTracks.Pos) ∈
        trackSetErased (BinTree.node a l r) i ↔
      p ∈ trackSetErased l i := by
  rw [mem_trackSetErased_iff]
  constructor
  · rintro ⟨q, hq, hqp⟩
    cases q with
    | none => cases hqp
    | some q =>
        cases q with
        | inl q =>
            refine ⟨q, hq, ?_⟩
            change
              (some (Sum.inl ((erasePosEquiv l) q)) :
                  Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) =
                some (Sum.inl p) at hqp
            exact Sum.inl.inj (Option.some.inj hqp)
        | inr q => cases hqp
  · rintro ⟨q, hq, hqp⟩
    refine ⟨some (.inl q), hq, ?_⟩
    change
      (some (Sum.inl ((erasePosEquiv l) q)) :
          Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) =
        some (Sum.inl p)
    simp [hqp]

@[simp] theorem trackSetErased_node_right {n : ℕ}
    (a : A × TrackBits n) (l r : BinTree (A × TrackBits n)) (i : Fin n)
    (p : r.eraseTracks.Pos) :
    (some (.inr p) : (BinTree.node a l r).eraseTracks.Pos) ∈
        trackSetErased (BinTree.node a l r) i ↔
      p ∈ trackSetErased r i := by
  rw [mem_trackSetErased_iff]
  constructor
  · rintro ⟨q, hq, hqp⟩
    cases q with
    | none => cases hqp
    | some q =>
        cases q with
        | inl q => cases hqp
        | inr q =>
            refine ⟨q, hq, ?_⟩
            change
              (some (Sum.inr ((erasePosEquiv r) q)) :
                  Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) =
                some (Sum.inr p) at hqp
            exact Sum.inr.inj (Option.some.inj hqp)
  · rintro ⟨q, hq, hqp⟩
    refine ⟨some (.inr q), hq, ?_⟩
    change
      (some (Sum.inr ((erasePosEquiv r) q)) :
          Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) =
        some (Sum.inr p)
    simp [hqp]

theorem erasePosEquiv_mem_trackSetErased_iff {n : ℕ}
    (t : BinTree (A × TrackBits n)) (i : Fin n) (p : t.Pos) :
    erasePosEquiv t p ∈ trackSetErased t i ↔ p ∈ trackSet t i := by
  constructor
  · intro h
    obtain ⟨q, hq, heq⟩ := (mem_trackSetErased_iff t i (erasePosEquiv t p)).mp h
    have hqp : q = p := (erasePosEquiv t).injective heq
    simpa [trackSet, hqp] using hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- The erased-position equivalence induced by adding tracks to an untracked
tree. -/
noncomputable def eraseWithTracksEquiv {n : ℕ}
    (t : BinTree A) (tracks : Fin n → Set t.Pos) :
    t.Pos ≃ (withTracks t tracks).eraseTracks.Pos :=
  (posEquivWithTracks t tracks).trans (erasePosEquiv (withTracks t tracks))

@[simp] theorem eraseWithTracksEquiv_mem_trackSetErased_iff {n : ℕ}
    (t : BinTree A) (tracks : Fin n → Set t.Pos) (i : Fin n)
    (p : t.Pos) :
    eraseWithTracksEquiv t tracks p ∈ trackSetErased (withTracks t tracks) i ↔
      p ∈ tracks i := by
  simpa [eraseWithTracksEquiv] using
    (erasePosEquiv_mem_trackSetErased_iff (withTracks t tracks) i
      (posEquivWithTracks t tracks p)).trans
      (trackSet_withTracks_iff t tracks i p)

theorem labelAt_eraseWithTracksEquiv {n : ℕ}
    (t : BinTree A) (tracks : Fin n → Set t.Pos) (p : t.Pos) :
    (withTracks t tracks).eraseTracks.labelAt
      (eraseWithTracksEquiv t tracks p) =
      t.labelAt p := by
  simp [eraseWithTracksEquiv, eraseTracks, erasePosEquiv]

theorem childRel_eraseWithTracksEquiv_iff {n : ℕ}
    (t : BinTree A) (tracks : Fin n → Set t.Pos) (b : Bool)
    (p q : t.Pos) :
    (withTracks t tracks).eraseTracks.childRel b
        (eraseWithTracksEquiv t tracks p)
        (eraseWithTracksEquiv t tracks q) ↔
      t.childRel b p q := by
  rw [show
      (withTracks t tracks).eraseTracks.childRel b
          (eraseWithTracksEquiv t tracks p)
          (eraseWithTracksEquiv t tracks q) ↔
        (withTracks t tracks).childRel b
          (posEquivWithTracks t tracks p)
          (posEquivWithTracks t tracks q) by
      simpa [eraseWithTracksEquiv, eraseTracks, erasePosEquiv] using
        childRel_map_iff Prod.fst b (withTracks t tracks)
          (posEquivWithTracks t tracks p)
          (posEquivWithTracks t tracks q)]
  exact childRel_withTracks_iff t tracks b p q

/-- Adding tracks and then erasing them gives a tree model isomorphic to the
original untracked tree model. -/
noncomputable def eraseWithTracksIso {n : ℕ}
    (t : BinTree A) (tracks : Fin n → Set t.Pos) :
    t.toTreeModel.Iso (withTracks t tracks).eraseTracks.toTreeModel where
  toEquiv := eraseWithTracksEquiv t tracks
  parentRel_iff := by
    intro p q
    simp [toTreeModel, childRel_eraseWithTracksEquiv_iff t tracks]
  label_eq := by
    intro p
    exact labelAt_eraseWithTracksEquiv t tracks p

theorem remapTracks_withTracks_eq_of_tracks {source target : ℕ}
    (keep : Fin target → Fin source)
    (t : BinTree (A × TrackBits target))
    (tracks : Fin source → Set t.eraseTracks.Pos)
    (htracks : ∀ i p, p ∈ tracks (keep i) ↔ p ∈ trackSetErased t i) :
    remapTracks keep (withTracks t.eraseTracks tracks) = t := by
  induction t with
  | nil =>
      rfl
  | node a l r ihl ihr =>
      let leftTracks : Fin source → Set l.eraseTracks.Pos := fun j =>
        {p | (some (.inl p) : Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) ∈
          tracks j}
      let rightTracks : Fin source → Set r.eraseTracks.Pos := fun j =>
        {p | (some (.inr p) : Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) ∈
          tracks j}
      have hleft :
          ∀ i p, p ∈ leftTracks (keep i) ↔ p ∈ trackSetErased l i := by
        intro i p
        change
          (some (.inl p) :
              Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) ∈
              tracks (keep i) ↔
            p ∈ trackSetErased l i
        exact (htracks i
          (some (.inl p) :
            Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos))).trans
          (trackSetErased_node_left a l r i p)
      have hright :
          ∀ i p, p ∈ rightTracks (keep i) ↔ p ∈ trackSetErased r i := by
        intro i p
        change
          (some (.inr p) :
              Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) ∈
              tracks (keep i) ↔
            p ∈ trackSetErased r i
        exact (htracks i
          (some (.inr p) :
            Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos))).trans
          (trackSetErased_node_right a l r i p)
      have hlabel :
          (a.1,
              fun i =>
                haveI : Decidable
                    ((none : Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) ∈
                      tracks (keep i)) :=
                  Classical.propDecidable _
                decide
                  ((none : Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) ∈
                    tracks (keep i))) = a := by
        cases a with
        | mk a bits =>
            classical
            simp only [Prod.mk.injEq, true_and]
            funext i
            have hiff :
                ((none : Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) ∈
                    tracks (keep i)) ↔
                  bits i = true := by
              exact (htracks i
                (none : Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos))).trans
                (trackSetErased_node_root (a, bits) l r i)
            by_cases hmem :
                (none : Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) ∈
                  tracks (keep i)
            · have hbit : bits i = true := hiff.mp hmem
              rw [decide_eq_true hmem, hbit]
            · have hbit : bits i = false := by
                cases h : bits i with
                | false => rfl
                | true =>
                    exact False.elim (hmem (hiff.mpr h))
              rw [decide_eq_false hmem, hbit]
      change
        BinTree.node
            (a.1,
              fun i =>
                haveI : Decidable
                    ((none : Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) ∈
                      tracks (keep i)) :=
                  Classical.propDecidable _
                decide
                  ((none : Option (l.eraseTracks.Pos ⊕ r.eraseTracks.Pos)) ∈
                    tracks (keep i)))
            (remapTracks keep (withTracks l.eraseTracks leftTracks))
            (remapTracks keep (withTracks r.eraseTracks rightTracks)) =
          BinTree.node a l r
      rw [ihl leftTracks hleft, ihr rightTracks hright, hlabel]

/-- Extend a target track context by copying the kept tracks and using one
fresh source track for a chosen set of erased target positions.  All other
source tracks are empty. -/
noncomputable def liftTracksWithFresh {source target : ℕ}
    (keep : Fin target → Fin source) (fresh : Fin source)
    (t : BinTree (A × TrackBits target))
    (freshSet : Set t.eraseTracks.Pos) :
    Fin source → Set t.eraseTracks.Pos :=
  fun j =>
    if h : ∃ i, keep i = j then
      trackSetErased t h.choose
    else if j = fresh then
      freshSet
    else
      ∅

@[simp] theorem liftTracksWithFresh_keep {source target : ℕ}
    (keep : Fin target → Fin source) (fresh : Fin source)
    (t : BinTree (A × TrackBits target))
    (freshSet : Set t.eraseTracks.Pos)
    (hkeep : Function.Injective keep) (i : Fin target) :
    liftTracksWithFresh keep fresh t freshSet (keep i) =
      trackSetErased t i := by
  unfold liftTracksWithFresh
  rw [dif_pos ⟨i, rfl⟩]
  congr 1
  exact hkeep (Classical.choose_spec (p := fun k => keep k = keep i) ⟨i, rfl⟩)

@[simp] theorem liftTracksWithFresh_fresh {source target : ℕ}
    (keep : Fin target → Fin source) (fresh : Fin source)
    (t : BinTree (A × TrackBits target))
    (freshSet : Set t.eraseTracks.Pos)
    (hfresh : ∀ i, fresh ≠ keep i) :
    liftTracksWithFresh keep fresh t freshSet fresh = freshSet := by
  unfold liftTracksWithFresh
  rw [dif_neg]
  · simp
  · rintro ⟨i, hi⟩
    exact hfresh i hi.symm

theorem remapTracks_withTracks_liftTracksWithFresh_eq {source target : ℕ}
    (keep : Fin target → Fin source) (fresh : Fin source)
    (t : BinTree (A × TrackBits target))
    (freshSet : Set t.eraseTracks.Pos)
    (hkeep : Function.Injective keep) :
    remapTracks keep
        (withTracks t.eraseTracks (liftTracksWithFresh keep fresh t freshSet)) =
      t := by
  refine remapTracks_withTracks_eq_of_tracks keep t
    (liftTracksWithFresh keep fresh t freshSet) ?_
  intro i p
  rw [liftTracksWithFresh_keep keep fresh t freshSet hkeep i]

theorem eraseWithTracksEquiv_mem_liftTracksWithFresh_fresh_iff
    {source target : ℕ}
    (keep : Fin target → Fin source) (fresh : Fin source)
    (t : BinTree (A × TrackBits target))
    (freshSet : Set t.eraseTracks.Pos)
    (hfresh : ∀ i, fresh ≠ keep i)
    (p : t.eraseTracks.Pos) :
    eraseWithTracksEquiv t.eraseTracks
        (liftTracksWithFresh keep fresh t freshSet) p ∈
        trackSetErased
          (withTracks t.eraseTracks (liftTracksWithFresh keep fresh t freshSet))
          fresh ↔
      p ∈ freshSet := by
  rw [eraseWithTracksEquiv_mem_trackSetErased_iff,
    liftTracksWithFresh_fresh keep fresh t freshSet hfresh]

theorem eraseWithTracksEquiv_mem_liftTracksWithFresh_keep_iff
    {source target : ℕ}
    (keep : Fin target → Fin source) (fresh : Fin source)
    (t : BinTree (A × TrackBits target))
    (freshSet : Set t.eraseTracks.Pos)
    (hkeep : Function.Injective keep) (i : Fin target)
    (p : t.eraseTracks.Pos) :
    eraseWithTracksEquiv t.eraseTracks
        (liftTracksWithFresh keep fresh t freshSet) p ∈
        trackSetErased
          (withTracks t.eraseTracks (liftTracksWithFresh keep fresh t freshSet))
          (keep i) ↔
      p ∈ trackSetErased t i := by
  rw [eraseWithTracksEquiv_mem_trackSetErased_iff,
    liftTracksWithFresh_keep keep fresh t freshSet hkeep i]

theorem trackCount_liftTracksWithFresh_singleton {source target : ℕ}
    (keep : Fin target → Fin source) (fresh : Fin source)
    (t : BinTree (A × TrackBits target))
    (hfresh : ∀ i, fresh ≠ keep i)
    (p : t.eraseTracks.Pos) :
    trackCount fresh
        (withTracks t.eraseTracks
          (liftTracksWithFresh keep fresh t ({p} : Set t.eraseTracks.Pos))) =
      Count.one := by
  let tracks :=
    liftTracksWithFresh keep fresh t ({p} : Set t.eraseTracks.Pos)
  let e := posEquivWithTracks t.eraseTracks tracks
  refine (trackCount_eq_one_iff_exists_unique fresh
    (withTracks t.eraseTracks tracks)).mpr ?_
  refine ⟨e p, ?_, ?_⟩
  · exact
      (trackSet_withTracks_iff t.eraseTracks tracks fresh p).mpr
        (by
          change p ∈ liftTracksWithFresh keep fresh t
            ({p} : Set t.eraseTracks.Pos) fresh
          rw [liftTracksWithFresh_fresh keep fresh t
            ({p} : Set t.eraseTracks.Pos) hfresh]
          exact rfl)
  · intro q hq
    obtain ⟨q0, rfl⟩ := e.surjective q
    have hq0 : q0 ∈ ({p} : Set t.eraseTracks.Pos) :=
      by
        have hq0tracks : q0 ∈ tracks fresh :=
          (trackSet_withTracks_iff t.eraseTracks tracks fresh q0).mp hq
        simpa [tracks,
          liftTracksWithFresh_fresh keep fresh t
            ({p} : Set t.eraseTracks.Pos) hfresh] using hq0tracks
    rw [Set.mem_singleton_iff.mp hq0]

theorem erasePosEquiv_mem_trackSetErased_remap_iff {source target : ℕ}
    (keep : Fin target → Fin source)
    (s : BinTree (A × TrackBits source)) (i : Fin target) (p : s.Pos) :
    erasePosEquiv (remapTracks keep s)
        (posEquivMap (fun a : A × TrackBits source =>
          (a.1, fun j => a.2 (keep j))) s p) ∈
        trackSetErased (remapTracks keep s) i ↔
      erasePosEquiv s p ∈ trackSetErased s (keep i) := by
  rw [erasePosEquiv_mem_trackSetErased_iff,
    erasePosEquiv_mem_trackSetErased_iff]
  exact trackSet_remapTracks_iff keep s i p

/-- The natural position equivalence between a source tracked tree with
`source` tracks and its `target`-track remapping after erasing tracks. -/
def eraseRemapEquiv {source target : ℕ} (keep : Fin target → Fin source)
    (s : BinTree (A × TrackBits source)) :
    s.eraseTracks.Pos ≃ (remapTracks keep s).eraseTracks.Pos :=
  (erasePosEquiv s).symm.trans
    ((posEquivMap (fun a : A × TrackBits source =>
      (a.1, fun j => a.2 (keep j))) s).trans
        (erasePosEquiv (remapTracks keep s)))

theorem eraseRemapEquiv_mem_trackSetErased_iff {source target : ℕ}
    (keep : Fin target → Fin source)
    (s : BinTree (A × TrackBits source)) (i : Fin target)
    (p : s.eraseTracks.Pos) :
    eraseRemapEquiv keep s p ∈ trackSetErased (remapTracks keep s) i ↔
      p ∈ trackSetErased s (keep i) := by
  simpa [eraseRemapEquiv] using
    erasePosEquiv_mem_trackSetErased_remap_iff keep s i
      ((erasePosEquiv s).symm p)

theorem labelAt_eraseRemapEquiv {source target : ℕ}
    (keep : Fin target → Fin source)
    (s : BinTree (A × TrackBits source)) (p : s.eraseTracks.Pos) :
    (remapTracks keep s).eraseTracks.labelAt (eraseRemapEquiv keep s p) =
      s.eraseTracks.labelAt p := by
  obtain ⟨p, rfl⟩ := (erasePosEquiv s).surjective p
  simp [eraseRemapEquiv, eraseTracks, erasePosEquiv, remapTracks]

theorem childRel_eraseRemapEquiv_iff {source target : ℕ}
    (keep : Fin target → Fin source)
    (s : BinTree (A × TrackBits source)) (b : Bool)
    (p q : s.eraseTracks.Pos) :
    (remapTracks keep s).eraseTracks.childRel b
        (eraseRemapEquiv keep s p) (eraseRemapEquiv keep s q) ↔
      s.eraseTracks.childRel b p q := by
  obtain ⟨p, rfl⟩ := (erasePosEquiv s).surjective p
  obtain ⟨q, rfl⟩ := (erasePosEquiv s).surjective q
  simp only [eraseRemapEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  change
    ((remapTracks keep s).map Prod.fst).childRel b
        (posEquivMap Prod.fst (remapTracks keep s)
          (posEquivMap (fun a : A × TrackBits source =>
            (a.1, fun j => a.2 (keep j))) s p))
        (posEquivMap Prod.fst (remapTracks keep s)
          (posEquivMap (fun a : A × TrackBits source =>
            (a.1, fun j => a.2 (keep j))) s q)) ↔
      (s.map Prod.fst).childRel b
        (posEquivMap Prod.fst s p) (posEquivMap Prod.fst s q)
  rw [childRel_map_iff Prod.fst b (remapTracks keep s)
      (posEquivMap (fun a : A × TrackBits source =>
        (a.1, fun j => a.2 (keep j))) s p)
      (posEquivMap (fun a : A × TrackBits source =>
        (a.1, fun j => a.2 (keep j))) s q)]
  change
    (s.map (fun a : A × TrackBits source =>
      (a.1, fun j => a.2 (keep j)))).childRel b
        (posEquivMap (fun a : A × TrackBits source =>
          (a.1, fun j => a.2 (keep j))) s p)
        (posEquivMap (fun a : A × TrackBits source =>
          (a.1, fun j => a.2 (keep j))) s q) ↔
      (s.map Prod.fst).childRel b
        (posEquivMap Prod.fst s p) (posEquivMap Prod.fst s q)
  rw [childRel_map_iff (fun a : A × TrackBits source =>
      (a.1, fun j => a.2 (keep j))) b s p q,
    childRel_map_iff Prod.fst b s p q]

/-- Erasing tracks before and after a track remapping yields isomorphic tree
models. -/
def eraseRemapIso {source target : ℕ} (keep : Fin target → Fin source)
    (s : BinTree (A × TrackBits source)) :
    s.eraseTracks.toTreeModel.Iso (remapTracks keep s).eraseTracks.toTreeModel where
  toEquiv := eraseRemapEquiv keep s
  parentRel_iff := by
    intro p q
    simp [toTreeModel, childRel_eraseRemapEquiv_iff keep s]
  label_eq := by
    intro p
    exact labelAt_eraseRemapEquiv keep s p

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

theorem of_liftTracksWithFresh_updateFO {source target : ℕ}
    (keep : Fin target → Fin source) (fresh : Fin source)
    (t : BinTree (A × TrackBits target))
    {targetFO : FOVar → Fin target} {targetSO : SOVar → Fin target}
    {sourceFO : FOVar → Fin source} {sourceSO : SOVar → Fin source}
    {ρ : Assignment t.eraseTracks.toTreeModel}
    (hρ : CarriesAssignment t targetFO targetSO ρ)
    (hkeep : Function.Injective keep)
    {x : FOVar} (p : t.eraseTracks.Pos)
    (hfo : ∀ y, y ≠ x → sourceFO y = keep (targetFO y))
    (hx : sourceFO x = fresh)
    (hfresh : ∀ i, fresh ≠ keep i)
    (hso : ∀ X, sourceSO X = keep (targetSO X)) :
    CarriesAssignment
      (withTracks t.eraseTracks
        (liftTracksWithFresh keep fresh t ({p} : Set t.eraseTracks.Pos)))
      sourceFO sourceSO
      ((ρ.updateFO x p).mapEquiv
        (eraseWithTracksEquiv t.eraseTracks
          (liftTracksWithFresh keep fresh t ({p} : Set t.eraseTracks.Pos)))) := by
  let tracks :=
    liftTracksWithFresh keep fresh t ({p} : Set t.eraseTracks.Pos)
  let e := eraseWithTracksEquiv t.eraseTracks tracks
  constructor
  · intro y q
    obtain ⟨q0, rfl⟩ := e.surjective q
    have hmap :
        (((ρ.updateFO x p).fo y).map e = some (e q0)) ↔
          (ρ.updateFO x p).fo y = some q0 := by
      constructor
      · intro h
        obtain ⟨r, hr, hrq⟩ := Option.map_eq_some_iff.mp h
        have hr0 : r = q0 := e.injective hrq
        simpa [hr0] using hr
      · intro h
        rw [h]
        rfl
    by_cases hy : y = x
    · subst hy
      rw [Assignment.updateFO_here] at hmap
      change
        (((ρ.updateFO y p).fo y).map e = some (e q0)) ↔
          e q0 ∈ trackSetErased
            (withTracks t.eraseTracks tracks) (sourceFO y)
      rw [Assignment.updateFO_here, hmap, hx]
      constructor
      · intro hpq
        have hq0 : q0 = p := (Option.some.inj hpq).symm
        rw [hq0]
        exact
          (eraseWithTracksEquiv_mem_liftTracksWithFresh_fresh_iff
            keep fresh t ({p} : Set t.eraseTracks.Pos) hfresh p).mpr rfl
      · intro hq
        have hq0 : q0 ∈ ({p} : Set t.eraseTracks.Pos) :=
          (eraseWithTracksEquiv_mem_liftTracksWithFresh_fresh_iff
            keep fresh t ({p} : Set t.eraseTracks.Pos) hfresh q0).mp hq
        exact congrArg some (Set.mem_singleton_iff.mp hq0).symm
    · rw [Assignment.updateFO_other ρ p hy] at hmap
      change
        (((ρ.updateFO x p).fo y).map e = some (e q0)) ↔
          e q0 ∈ trackSetErased
            (withTracks t.eraseTracks tracks) (sourceFO y)
      rw [Assignment.updateFO_other ρ p hy]
      rw [hmap, hfo y hy]
      exact
        (hρ.fo_iff y q0).trans
          (eraseWithTracksEquiv_mem_liftTracksWithFresh_keep_iff
            keep fresh t ({p} : Set t.eraseTracks.Pos) hkeep (targetFO y) q0).symm
  · intro X
    ext q
    obtain ⟨q0, rfl⟩ := e.surjective q
    constructor
    · rintro ⟨r, hr, hrq⟩
      have hr0 : r = q0 := e.injective hrq
      have htarget : q0 ∈ trackSetErased t (targetSO X) := by
        simpa [hr0, hρ.so_eq X] using hr
      have hsource :
          e q0 ∈ trackSetErased
            (withTracks t.eraseTracks tracks) (keep (targetSO X)) :=
        (eraseWithTracksEquiv_mem_liftTracksWithFresh_keep_iff
          keep fresh t ({p} : Set t.eraseTracks.Pos) hkeep (targetSO X) q0).mpr
          htarget
      simpa [e, tracks, hso X] using hsource
    · intro hq
      have hsource :
          e q0 ∈ trackSetErased
            (withTracks t.eraseTracks tracks) (keep (targetSO X)) := by
        simpa [e, tracks, hso X] using hq
      have htarget : q0 ∈ trackSetErased t (targetSO X) :=
        (eraseWithTracksEquiv_mem_liftTracksWithFresh_keep_iff
          keep fresh t ({p} : Set t.eraseTracks.Pos) hkeep (targetSO X) q0).mp
          hsource
      refine ⟨q0, ?_, rfl⟩
      simpa [hρ.so_eq X] using htarget

theorem of_liftTracksWithFresh_updateSO {source target : ℕ}
    (keep : Fin target → Fin source) (fresh : Fin source)
    (t : BinTree (A × TrackBits target))
    {targetFO : FOVar → Fin target} {targetSO : SOVar → Fin target}
    {sourceFO : FOVar → Fin source} {sourceSO : SOVar → Fin source}
    {ρ : Assignment t.eraseTracks.toTreeModel}
    (hρ : CarriesAssignment t targetFO targetSO ρ)
    (hkeep : Function.Injective keep)
    {X : SOVar} (S : Set t.eraseTracks.Pos)
    (hfo : ∀ y, sourceFO y = keep (targetFO y))
    (hX : sourceSO X = fresh)
    (hfresh : ∀ i, fresh ≠ keep i)
    (hso : ∀ Y, Y ≠ X → sourceSO Y = keep (targetSO Y)) :
    CarriesAssignment
      (withTracks t.eraseTracks
        (liftTracksWithFresh keep fresh t S))
      sourceFO sourceSO
      ((ρ.updateSO X S).mapEquiv
        (eraseWithTracksEquiv t.eraseTracks
          (liftTracksWithFresh keep fresh t S))) := by
  let tracks := liftTracksWithFresh keep fresh t S
  let e := eraseWithTracksEquiv t.eraseTracks tracks
  constructor
  · intro y q
    obtain ⟨q0, rfl⟩ := e.surjective q
    have hmap :
        (((ρ.updateSO X S).fo y).map e = some (e q0)) ↔
          (ρ.updateSO X S).fo y = some q0 := by
      constructor
      · intro h
        obtain ⟨r, hr, hrq⟩ := Option.map_eq_some_iff.mp h
        have hr0 : r = q0 := e.injective hrq
        simpa [hr0] using hr
      · intro h
        rw [h]
        rfl
    change
      (((ρ.updateSO X S).fo y).map e = some (e q0)) ↔
        e q0 ∈ trackSetErased
          (withTracks t.eraseTracks tracks) (sourceFO y)
    rw [hmap, Assignment.updateSO_fo, hfo y]
    exact
      (hρ.fo_iff y q0).trans
        (eraseWithTracksEquiv_mem_liftTracksWithFresh_keep_iff
          keep fresh t S hkeep (targetFO y) q0).symm
  · intro Y
    ext q
    obtain ⟨q0, rfl⟩ := e.surjective q
    by_cases hY : Y = X
    · subst hY
      rw [hX]
      constructor
      · rintro ⟨r, hr, hrq⟩
        have hr0 : r = q0 := e.injective hrq
        have hq0 : q0 ∈ S := by
          simpa [hr0] using hr
        exact
          (eraseWithTracksEquiv_mem_liftTracksWithFresh_fresh_iff
            keep fresh t S hfresh q0).mpr hq0
      · intro hq
        have hq0 : q0 ∈ S :=
          (eraseWithTracksEquiv_mem_liftTracksWithFresh_fresh_iff
            keep fresh t S hfresh q0).mp hq
        exact ⟨q0, by simpa using hq0, rfl⟩
    · constructor
      · rintro ⟨r, hr, hrq⟩
        have hr0 : r = q0 := e.injective hrq
        have htarget : q0 ∈ trackSetErased t (targetSO Y) := by
          simpa [hr0, hρ.so_eq Y, Assignment.updateSO_other ρ S hY] using hr
        have hsource :
            e q0 ∈ trackSetErased
              (withTracks t.eraseTracks tracks) (keep (targetSO Y)) :=
          (eraseWithTracksEquiv_mem_liftTracksWithFresh_keep_iff
            keep fresh t S hkeep (targetSO Y) q0).mpr htarget
        simpa [e, tracks, hso Y hY] using hsource
      · intro hq
        have hsource :
            e q0 ∈ trackSetErased
              (withTracks t.eraseTracks tracks) (keep (targetSO Y)) := by
          simpa [e, tracks, hso Y hY] using hq
        have htarget : q0 ∈ trackSetErased t (targetSO Y) :=
          (eraseWithTracksEquiv_mem_liftTracksWithFresh_keep_iff
            keep fresh t S hkeep (targetSO Y) q0).mp hsource
        refine ⟨q0, ?_, rfl⟩
        simpa [hρ.so_eq Y, Assignment.updateSO_other ρ S hY] using htarget

theorem empty_withTracks_empty {n : ℕ}
    (t : BinTree A)
    (foTrack : FOVar → Fin n) (soTrack : SOVar → Fin n) :
    CarriesAssignment
      (withTracks t (fun _ => (∅ : Set t.Pos)))
      foTrack soTrack
      ((Assignment.empty t.toTreeModel).mapEquiv
        (eraseWithTracksEquiv t (fun _ => (∅ : Set t.Pos)))) := by
  let tracks : Fin n → Set t.Pos := fun _ => ∅
  let e := eraseWithTracksEquiv t tracks
  constructor
  · intro x p
    constructor
    · intro hp
      simp [Assignment.empty, Assignment.mapEquiv] at hp
    · intro hp
      obtain ⟨q, rfl⟩ := e.surjective p
      have hq : q ∈ tracks (foTrack x) :=
        (eraseWithTracksEquiv_mem_trackSetErased_iff t tracks (foTrack x) q).mp hp
      simp [tracks] at hq
  · intro X
    ext p
    constructor
    · intro hp
      rcases hp with ⟨q, hq, rfl⟩
      simp [Assignment.empty] at hq
    · intro hp
      obtain ⟨q, rfl⟩ := e.surjective p
      have hq : q ∈ tracks (soTrack X) :=
        (eraseWithTracksEquiv_mem_trackSetErased_iff t tracks (soTrack X) q).mp hp
      simp [tracks] at hq

theorem of_remapTracks {source target : ℕ}
    (keep : Fin target → Fin source)
    (s : BinTree (A × TrackBits source))
    {targetFO : FOVar → Fin target} {targetSO : SOVar → Fin target}
    {sourceFO : FOVar → Fin source} {sourceSO : SOVar → Fin source}
    {ρ : Assignment (remapTracks keep s).eraseTracks.toTreeModel}
    (hρ : CarriesAssignment (remapTracks keep s) targetFO targetSO ρ)
    (hfo : ∀ x, sourceFO x = keep (targetFO x))
    (hso : ∀ X, sourceSO X = keep (targetSO X)) :
    CarriesAssignment s sourceFO sourceSO
      (ρ.mapEquiv (eraseRemapEquiv keep s).symm) := by
  let e := eraseRemapEquiv keep s
  constructor
  · intro x p
    constructor
    · intro hp
      obtain ⟨q, hq, hqp⟩ := Option.map_eq_some_iff.mp hp
      have hqmem : q ∈ trackSetErased (remapTracks keep s) (targetFO x) :=
        (hρ.fo_iff x q).mp hq
      have hqeq : q = e p := by
        have := congrArg e hqp
        simpa [e] using this
      have hep : e p ∈ trackSetErased (remapTracks keep s) (targetFO x) := by
        simpa [hqeq] using hqmem
      have hsource :=
        (eraseRemapEquiv_mem_trackSetErased_iff keep s (targetFO x) p).mp hep
      simpa [hfo x] using hsource
    · intro hp
      have hep : e p ∈ trackSetErased (remapTracks keep s) (targetFO x) := by
        have hsource : p ∈ trackSetErased s (keep (targetFO x)) := by
          simpa [hfo x] using hp
        exact (eraseRemapEquiv_mem_trackSetErased_iff keep s (targetFO x) p).mpr
          hsource
      have htarget : ρ.fo x = some (e p) :=
        (hρ.fo_iff x (e p)).mpr hep
      rw [Assignment.mapEquiv_fo, htarget]
      simp [e]
  · intro X
    ext p
    constructor
    · rintro ⟨q, hq, hqp⟩
      have hqmem : q ∈ trackSetErased (remapTracks keep s) (targetSO X) := by
        simpa [hρ.so_eq X] using hq
      have hqeq : q = e p := by
        have := congrArg e hqp
        simpa [e] using this
      have hep : e p ∈ trackSetErased (remapTracks keep s) (targetSO X) := by
        simpa [hqeq] using hqmem
      have hsource :=
        (eraseRemapEquiv_mem_trackSetErased_iff keep s (targetSO X) p).mp hep
      simpa [hso X] using hsource
    · intro hp
      refine ⟨e p, ?_, ?_⟩
      · have hsource : p ∈ trackSetErased s (keep (targetSO X)) := by
          simpa [hso X] using hp
        have hep :=
          (eraseRemapEquiv_mem_trackSetErased_iff keep s (targetSO X) p).mpr
            hsource
        simpa [hρ.so_eq X] using hep
      · simp [e]

theorem to_remapTracks {source target : ℕ}
    (keep : Fin target → Fin source)
    (s : BinTree (A × TrackBits source))
    {targetFO : FOVar → Fin target} {targetSO : SOVar → Fin target}
    {sourceFO : FOVar → Fin source} {sourceSO : SOVar → Fin source}
    {ρ : Assignment s.eraseTracks.toTreeModel}
    (hρ : CarriesAssignment s sourceFO sourceSO ρ)
    (hfo : ∀ x, sourceFO x = keep (targetFO x))
    (hso : ∀ X, sourceSO X = keep (targetSO X)) :
    CarriesAssignment (remapTracks keep s) targetFO targetSO
      (ρ.mapEquiv (eraseRemapEquiv keep s)) := by
  let e := eraseRemapEquiv keep s
  constructor
  · intro x q
    constructor
    · intro hq
      obtain ⟨p, hp, hpq⟩ := Option.map_eq_some_iff.mp hq
      have hpmem : p ∈ trackSetErased s (keep (targetFO x)) := by
        have hsource : p ∈ trackSetErased s (sourceFO x) :=
          (hρ.fo_iff x p).mp hp
        simpa [hfo x] using hsource
      have heq : e p = q := hpq
      have hep :=
        (eraseRemapEquiv_mem_trackSetErased_iff keep s (targetFO x) p).mpr
          hpmem
      rw [← heq]
      exact hep
    · intro hq
      let p : s.eraseTracks.Pos := e.symm q
      have hpmem : p ∈ trackSetErased s (keep (targetFO x)) := by
        have hep : e p ∈ trackSetErased (remapTracks keep s) (targetFO x) := by
          simpa [p, e] using hq
        exact (eraseRemapEquiv_mem_trackSetErased_iff keep s (targetFO x) p).mp
          hep
      have hp : ρ.fo x = some p := by
        apply (hρ.fo_iff x p).mpr
        simpa [hfo x] using hpmem
      rw [Assignment.mapEquiv_fo, hp]
      simp [p, e]
  · intro X
    ext q
    constructor
    · rintro ⟨p, hp, hpq⟩
      have hpmem : p ∈ trackSetErased s (keep (targetSO X)) := by
        have hsource : p ∈ trackSetErased s (sourceSO X) := by
          simpa [hρ.so_eq X] using hp
        simpa [hso X] using hsource
      have hep :=
        (eraseRemapEquiv_mem_trackSetErased_iff keep s (targetSO X) p).mpr
          hpmem
      rw [← hpq]
      exact hep
    · intro hq
      let p : s.eraseTracks.Pos := e.symm q
      refine ⟨p, ?_, ?_⟩
      · have hep : e p ∈ trackSetErased (remapTracks keep s) (targetSO X) := by
          simpa [p, e] using hq
        have hpmem :=
          (eraseRemapEquiv_mem_trackSetErased_iff keep s (targetSO X) p).mp
            hep
        have hsource : p ∈ trackSetErased s (sourceSO X) := by
          simpa [hso X] using hpmem
        simpa [hρ.so_eq X] using hsource
      · simp [p, e]

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
