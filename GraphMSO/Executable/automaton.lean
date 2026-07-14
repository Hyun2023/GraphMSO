import GraphMSO.Automata.automaton
import GraphMSO.Automata.binTree
import Mathlib.Data.Bool.AllAny
import Mathlib.Tactic

/-!
# Executable bottom-up automata for binary trees

This file is the computable companion to `TreeAutomaton`.  Its accepting
predicate is Boolean and its state space carries a `Finite` proof together
with executable `DecidableEq`.  The final-track projection uses only the
states actually reached by the two children; it never enumerates the whole
state or alphabet type.
-/

universe u

/-- A deterministic, executable bottom-up automaton on ordered binary trees. -/
structure ExecTreeAutomaton (A : Type u) where
  /-- The finite state type. -/
  State : Type
  /-- A proof that the state type is finite.  Keeping only `Finite` here is
  important computationally: powerset states must not eagerly enumerate the
  entire powerset before a run starts. -/
  [stateFinite : Finite State]
  /-- Decidable state equality, used by finite-set constructions. -/
  [stateDecidableEq : DecidableEq State]
  /-- State assigned to an absent subtree. -/
  nil : State
  /-- Transition at a binary node. -/
  node : A → State → State → State
  /-- Boolean accepting-state test. -/
  accept : State → Bool

attribute [instance] ExecTreeAutomaton.stateFinite
attribute [instance] ExecTreeAutomaton.stateDecidableEq

namespace ExecTreeAutomaton

variable {A : Type u}

open BinTree

/-- Finsets over a finite type are finite, without bundling an eager powerset
enumeration into executable automata. -/
instance instFiniteFinset {S : Type} [Finite S] : Finite (Finset S) :=
  Finite.of_injective ((↑) : Finset S → Set S) Finset.coe_injective

/-- Executable Boolean existential search over a finite set. -/
def finsetAny {S : Type*} [DecidableEq S]
    (states : Finset S) (predicate : S → Bool) : Bool :=
  states.fold Bool.or false predicate

theorem finsetAny_eq_true_iff {S : Type*} [DecidableEq S]
    (states : Finset S) (predicate : S → Bool) :
    finsetAny states predicate = true ↔
      ∃ state ∈ states, predicate state = true := by
  induction states using Finset.induction_on with
  | empty => simp [finsetAny]
  | @insert state states hstate ih =>
      rw [finsetAny, Finset.fold_insert hstate, Bool.or_eq_true]
      change (predicate state = true ∨ finsetAny states predicate = true) ↔ _
      rw [ih]
      simp

/-- Execute an automaton bottom-up on a binary tree. -/
def run (M : ExecTreeAutomaton A) : BinTree A → M.State
  | .nil => M.nil
  | .node a left right => M.node a (M.run left) (M.run right)

@[simp] theorem run_nil (M : ExecTreeAutomaton A) :
    M.run (.nil : BinTree A) = M.nil :=
  rfl

@[simp] theorem run_node (M : ExecTreeAutomaton A) (a : A) (left right : BinTree A) :
    M.run (.node a left right) = M.node a (M.run left) (M.run right) :=
  rfl

/-- Execute the automaton and return its Boolean answer. -/
def accepts (M : ExecTreeAutomaton A) (t : BinTree A) : Bool :=
  M.accept (M.run t)

/-- Forget the executable structure and obtain the existing padded-term automaton. -/
def toTreeAutomaton (M : ExecTreeAutomaton A) : TreeAutomaton (paddedAlphabet A) where
  State := M.State
  step
    | none, _ => M.nil
    | some a, qs =>
        M.node a
          (qs ⟨0, by simp [paddedAlphabet]⟩)
          (qs ⟨1, by simp [paddedAlphabet]⟩)
  accept := {q | M.accept q = true}

/-- The padded-term run of the forgotten automaton is the executable tree run. -/
@[simp] theorem toTreeAutomaton_run_toTerm (M : ExecTreeAutomaton A) (t : BinTree A) :
    M.toTreeAutomaton.run t.toTerm = M.run t := by
  induction t with
  | nil => rfl
  | node a left right ihLeft ihRight =>
      change M.node a
        (M.toTreeAutomaton.run left.toTerm)
        (M.toTreeAutomaton.run right.toTerm) = _
      rw [ihLeft, ihRight]
      rfl

/-- The abstract run on an arbitrary padded term is execution on its decoded tree. -/
@[simp] theorem toTreeAutomaton_run_ofTerm (M : ExecTreeAutomaton A)
    (t : (paddedAlphabet A).Term) :
    M.toTreeAutomaton.run t = M.run (BinTree.ofTerm t) := by
  calc
    M.toTreeAutomaton.run t =
        M.toTreeAutomaton.run (BinTree.ofTerm t).toTerm := by simp
    _ = M.run (BinTree.ofTerm t) := toTreeAutomaton_run_toTerm _ _

/-- Boolean acceptance agrees with membership in the abstract automaton language. -/
@[simp] theorem accepts_eq_true_iff_language (M : ExecTreeAutomaton A) (t : BinTree A) :
    M.accepts t = true ↔ t.toTerm ∈ M.toTreeAutomaton.language := by
  change M.accept (M.run t) = true ↔
    M.accept (M.toTreeAutomaton.run t.toTerm) = true
  rw [toTreeAutomaton_run_toTerm]

/-- Abstract-language membership for an arbitrary padded term can be decided
by decoding it to a binary tree and running the executable automaton. -/
@[simp] theorem mem_language_iff_accepts_ofTerm (M : ExecTreeAutomaton A)
    (t : (paddedAlphabet A).Term) :
    t ∈ M.toTreeAutomaton.language ↔ M.accepts (BinTree.ofTerm t) = true := by
  simpa using (accepts_eq_true_iff_language M (BinTree.ofTerm t)).symm

/-! ## Boolean closure -/

/-- Complement an executable deterministic automaton. -/
def compl (M : ExecTreeAutomaton A) : ExecTreeAutomaton A where
  State := M.State
  nil := M.nil
  node := M.node
  accept q := !(M.accept q)

@[simp] theorem run_compl (M : ExecTreeAutomaton A) (t : BinTree A) :
    M.compl.run t = M.run t := by
  induction t with
  | nil => rfl
  | node a left right ihLeft ihRight =>
      change M.node a (M.compl.run left) (M.compl.run right) = _
      rw [ihLeft, ihRight]
      rfl

@[simp] theorem accepts_compl (M : ExecTreeAutomaton A) (t : BinTree A) :
    M.compl.accepts t = !(M.accepts t) := by
  unfold accepts
  rw [run_compl]
  rfl

/-- Intersection by the usual product construction. -/
def inter (M N : ExecTreeAutomaton A) : ExecTreeAutomaton A where
  State := M.State × N.State
  nil := (M.nil, N.nil)
  node a left right :=
    (M.node a left.1 right.1, N.node a left.2 right.2)
  accept q := M.accept q.1 && N.accept q.2

@[simp] theorem run_inter (M N : ExecTreeAutomaton A) (t : BinTree A) :
    (M.inter N).run t = (M.run t, N.run t) := by
  induction t with
  | nil => rfl
  | node a left right ihLeft ihRight =>
      change
        (M.node a ((M.inter N).run left).1 ((M.inter N).run right).1,
          N.node a ((M.inter N).run left).2 ((M.inter N).run right).2) = _
      rw [ihLeft, ihRight]
      rfl

@[simp] theorem accepts_inter (M N : ExecTreeAutomaton A) (t : BinTree A) :
    (M.inter N).accepts t = (M.accepts t && N.accepts t) := by
  unfold accepts
  rw [run_inter]
  rfl

/-- Union by the usual product construction. -/
def union (M N : ExecTreeAutomaton A) : ExecTreeAutomaton A where
  State := M.State × N.State
  nil := (M.nil, N.nil)
  node a left right :=
    (M.node a left.1 right.1, N.node a left.2 right.2)
  accept q := M.accept q.1 || N.accept q.2

@[simp] theorem run_union (M N : ExecTreeAutomaton A) (t : BinTree A) :
    (M.union N).run t = (M.run t, N.run t) := by
  induction t with
  | nil => rfl
  | node a left right ihLeft ihRight =>
      change
        (M.node a ((M.union N).run left).1 ((M.union N).run right).1,
          N.node a ((M.union N).run left).2 ((M.union N).run right).2) = _
      rw [ihLeft, ihRight]
      rfl

@[simp] theorem accepts_union (M N : ExecTreeAutomaton A) (t : BinTree A) :
    (M.union N).accepts t = (M.accepts t || N.accepts t) := by
  unfold accepts
  rw [run_union]
  rfl

@[simp] theorem language_toTreeAutomaton_compl (M : ExecTreeAutomaton A) :
    M.compl.toTreeAutomaton.language = M.toTreeAutomaton.languageᶜ := by
  ext t
  rw [Set.mem_compl_iff]
  change (Bool.not (M.accept (M.compl.toTreeAutomaton.run t)) = true) ↔
    ¬M.accept (M.toTreeAutomaton.run t) = true
  rw [toTreeAutomaton_run_ofTerm, toTreeAutomaton_run_ofTerm, run_compl]
  cases M.accept (M.run (BinTree.ofTerm t)) <;> decide

@[simp] theorem language_toTreeAutomaton_inter (M N : ExecTreeAutomaton A) :
    (M.inter N).toTreeAutomaton.language =
      M.toTreeAutomaton.language ∩ N.toTreeAutomaton.language := by
  ext t
  rw [Set.mem_inter_iff, mem_language_iff_accepts_ofTerm,
    mem_language_iff_accepts_ofTerm, mem_language_iff_accepts_ofTerm]
  simp

@[simp] theorem language_toTreeAutomaton_union (M N : ExecTreeAutomaton A) :
    (M.union N).toTreeAutomaton.language =
      M.toTreeAutomaton.language ∪ N.toTreeAutomaton.language := by
  ext t
  rw [Set.mem_union, mem_language_iff_accepts_ofTerm,
    mem_language_iff_accepts_ofTerm, mem_language_iff_accepts_ofTerm]
  simp

/-! ## Lazy projection of the final Boolean track -/

/-- Append one final Boolean coordinate to a track vector. -/
def appendLast {n : ℕ} (bits : TrackBits n) (last : Bool) : TrackBits (n + 1) :=
  Fin.lastCases last bits

@[simp] theorem appendLast_castSucc {n : ℕ} (bits : TrackBits n) (last : Bool)
    (i : Fin n) :
    appendLast bits last (Fin.castSucc i) = bits i := by
  simp [appendLast]

@[simp] theorem appendLast_last {n : ℕ} (bits : TrackBits n) (last : Bool) :
    appendLast bits last (Fin.last n) = last := by
  simp [appendLast]

/-- Every track vector is its prefix followed by its final coordinate. -/
theorem appendLast_eta {n : ℕ} (bits : TrackBits (n + 1)) :
    appendLast (fun i => bits (Fin.castSucc i)) (bits (Fin.last n)) = bits := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- A source tree extends a target tree by one freely chosen Boolean track. -/
inductive LastTrackExtension {n : ℕ} :
    BinTree (A × TrackBits n) → BinTree (A × TrackBits (n + 1)) → Prop where
  | nil : LastTrackExtension .nil .nil
  | node (a : A) (bits : TrackBits n) (last : Bool)
      {left right : BinTree (A × TrackBits n)}
      {sourceLeft sourceRight : BinTree (A × TrackBits (n + 1))}
      (hLeft : LastTrackExtension left sourceLeft)
      (hRight : LastTrackExtension right sourceRight) :
      LastTrackExtension
        (.node (a, bits) left right)
        (.node (a, appendLast bits last) sourceLeft sourceRight)

/-- Project away the last Boolean track.

The projected state is the finite set of source states reachable from choices
made below the current node.  Its node transition combines only the states
present in the two child sets and the two possible values of the erased bit.
-/
def projectLast {n : ℕ}
    (M : ExecTreeAutomaton (A × TrackBits (n + 1))) :
    ExecTreeAutomaton (A × TrackBits n) where
  State := Finset M.State
  nil := {M.nil}
  node label left right :=
    let pairs := left.product right
    (pairs.image fun q =>
      M.node (label.1, appendLast label.2 false) q.1 q.2) ∪
    (pairs.image fun q =>
      M.node (label.1, appendLast label.2 true) q.1 q.2)
  accept states := finsetAny states M.accept

/-- The projected run with its concrete finite-set result type exposed. -/
def projectLastRun {n : ℕ}
    (M : ExecTreeAutomaton (A × TrackBits (n + 1)))
    (t : BinTree (A × TrackBits n)) : Finset M.State :=
  M.projectLast.run t

/-- The lazy projected run contains exactly the runs of final-track extensions. -/
theorem mem_run_projectLast_iff {n : ℕ}
    (M : ExecTreeAutomaton (A × TrackBits (n + 1)))
    (t : BinTree (A × TrackBits n)) (q : M.State) :
    q ∈ M.projectLastRun t ↔
      ∃ source : BinTree (A × TrackBits (n + 1)),
        LastTrackExtension t source ∧ M.run source = q := by
  induction t generalizing q with
  | nil =>
      constructor
      · intro h
        change q ∈ ({M.nil} : Finset M.State) at h
        have hq : q = M.nil := Finset.mem_singleton.mp h
        exact ⟨.nil, .nil, by simpa [hq]⟩
      · rintro ⟨source, hsource, hrun⟩
        cases hsource
        change q ∈ ({M.nil} : Finset M.State)
        exact Finset.mem_singleton.mpr hrun.symm
  | node label left right ihLeft ihRight =>
      constructor
      · intro h
        change q ∈
          ((M.projectLastRun left).product (M.projectLastRun right)).image
              (fun p => M.node
                (label.1, appendLast label.2 false) p.1 p.2) ∪
            ((M.projectLastRun left).product (M.projectLastRun right)).image
              (fun p => M.node
                (label.1, appendLast label.2 true) p.1 p.2) at h
        rw [Finset.mem_union] at h
        rcases h with h | h
        · obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp h
          obtain ⟨hpLeft, hpRight⟩ := Finset.mem_product.mp hp
          obtain ⟨sourceLeft, hsourceLeft, hrunLeft⟩ := (ihLeft p.1).mp hpLeft
          obtain ⟨sourceRight, hsourceRight, hrunRight⟩ := (ihRight p.2).mp hpRight
          refine ⟨.node (label.1, appendLast label.2 false) sourceLeft sourceRight,
            .node label.1 label.2 false hsourceLeft hsourceRight, ?_⟩
          simpa [hrunLeft, hrunRight] using hpq
        · obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp h
          obtain ⟨hpLeft, hpRight⟩ := Finset.mem_product.mp hp
          obtain ⟨sourceLeft, hsourceLeft, hrunLeft⟩ := (ihLeft p.1).mp hpLeft
          obtain ⟨sourceRight, hsourceRight, hrunRight⟩ := (ihRight p.2).mp hpRight
          refine ⟨.node (label.1, appendLast label.2 true) sourceLeft sourceRight,
            .node label.1 label.2 true hsourceLeft hsourceRight, ?_⟩
          simpa [hrunLeft, hrunRight] using hpq
      · rintro ⟨source, hsource, hrun⟩
        cases hsource with
        | node a bits last hsourceLeft hsourceRight =>
            rename_i sourceLeft sourceRight
            have hleft : M.run sourceLeft ∈ M.projectLastRun left :=
              (ihLeft (M.run sourceLeft)).mpr ⟨sourceLeft, hsourceLeft, rfl⟩
            have hright : M.run sourceRight ∈ M.projectLastRun right :=
              (ihRight (M.run sourceRight)).mpr ⟨sourceRight, hsourceRight, rfl⟩
            change q ∈
              ((M.projectLastRun left).product (M.projectLastRun right)).image
                  (fun p => M.node
                    (a, appendLast bits false) p.1 p.2) ∪
                ((M.projectLastRun left).product (M.projectLastRun right)).image
                  (fun p => M.node
                    (a, appendLast bits true) p.1 p.2)
            cases last with
            | false =>
                rw [Finset.mem_union]
                left
                apply Finset.mem_image.mpr
                exact ⟨(M.run sourceLeft, M.run sourceRight),
                  Finset.mem_product.mpr ⟨hleft, hright⟩, by simpa using hrun⟩
            | true =>
                rw [Finset.mem_union]
                right
                apply Finset.mem_image.mpr
                exact ⟨(M.run sourceLeft, M.run sourceRight),
                  Finset.mem_product.mpr ⟨hleft, hright⟩, by simpa using hrun⟩

/-- Boolean acceptance of the projection is existential acceptance over extensions. -/
theorem projectLast_accepts_eq_true_iff {n : ℕ}
    (M : ExecTreeAutomaton (A × TrackBits (n + 1)))
    (t : BinTree (A × TrackBits n)) :
    M.projectLast.accepts t = true ↔
      ∃ source : BinTree (A × TrackBits (n + 1)),
        LastTrackExtension t source ∧ M.accepts source = true := by
  change finsetAny (M.projectLastRun t) M.accept = true ↔ _
  rw [finsetAny_eq_true_iff]
  constructor
  · rintro ⟨q, hq, haccept⟩
    obtain ⟨source, hsource, hrun⟩ := (mem_run_projectLast_iff M t q).mp hq
    exact ⟨source, hsource, by simpa [accepts, hrun] using haccept⟩
  · rintro ⟨source, hsource, haccept⟩
    refine ⟨M.run source, ?_, ?_⟩
    · simpa using (mem_run_projectLast_iff M t _).mpr
        ⟨source, hsource, rfl⟩
    simpa [accepts] using haccept

/-- Extending the final track is equivalent to erasing it with `Fin.castSucc`. -/
theorem lastTrackExtension_iff_remapTracks {n : ℕ}
    (target : BinTree (A × TrackBits n))
    (source : BinTree (A × TrackBits (n + 1))) :
    LastTrackExtension target source ↔
      BinTree.remapTracks Fin.castSucc source = target := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | node a bits last hLeft hRight ihLeft ihRight =>
        unfold BinTree.remapTracks at ihLeft ihRight ⊢
        simp only [BinTree.map_node, appendLast_castSucc, ihLeft, ihRight]
  · revert source
    induction target with
    | nil =>
        intro source h
        cases source with
        | nil => exact .nil
        | node label left right => simp [BinTree.remapTracks] at h
    | node label left right ihLeft ihRight =>
        intro source h
        cases source with
        | nil => simp [BinTree.remapTracks] at h
        | node sourceLabel sourceLeft sourceRight =>
            change
              BinTree.node
                  (sourceLabel.1, fun i => sourceLabel.2 (Fin.castSucc i))
                  (BinTree.remapTracks Fin.castSucc sourceLeft)
                  (BinTree.remapTracks Fin.castSucc sourceRight) =
                BinTree.node label left right at h
            injection h with hlabel hleft hright
            have hbase : sourceLabel.1 = label.1 := congrArg Prod.fst hlabel
            have hbits :
                (fun i => sourceLabel.2 (Fin.castSucc i)) = label.2 :=
              congrArg Prod.snd hlabel
            have hsourceBits :
                sourceLabel.2 =
                  appendLast label.2 (sourceLabel.2 (Fin.last n)) := by
              rw [← hbits]
              exact (appendLast_eta sourceLabel.2).symm
            have hslabel :
                sourceLabel =
                  (label.1, appendLast label.2 (sourceLabel.2 (Fin.last n))) := by
              apply Prod.ext
              · exact hbase
              · exact hsourceBits
            rw [hslabel]
            exact .node label.1 label.2 (sourceLabel.2 (Fin.last n))
              (ihLeft _ hleft) (ihRight _ hright)

/-- Run-membership correctness stated using the existing track-remapping operation. -/
theorem mem_run_projectLast_iff_remapTracks {n : ℕ}
    (M : ExecTreeAutomaton (A × TrackBits (n + 1)))
    (t : BinTree (A × TrackBits n)) (q : M.State) :
    q ∈ M.projectLastRun t ↔
      ∃ source : BinTree (A × TrackBits (n + 1)),
        BinTree.remapTracks Fin.castSucc source = t ∧ M.run source = q := by
  rw [mem_run_projectLast_iff]
  apply exists_congr
  intro source
  rw [lastTrackExtension_iff_remapTracks]

/-- The abstract language of lazy projection is the homomorphic image obtained
by erasing the final track. -/
theorem language_toTreeAutomaton_projectLast {n : ℕ}
    (M : ExecTreeAutomaton (A × TrackBits (n + 1))) :
    M.projectLast.toTreeAutomaton.language =
      RankedAlphabet.Term.map (remapTracksHom A Fin.castSucc) ''
        M.toTreeAutomaton.language := by
  ext t
  rw [← BinTree.toTerm_ofTerm t]
  constructor
  · intro h
    have haccept : M.projectLast.accepts (BinTree.ofTerm t) = true :=
      (accepts_eq_true_iff_language _ _).mpr h
    obtain ⟨source, hsource, hsourceAccept⟩ :=
      (projectLast_accepts_eq_true_iff M (BinTree.ofTerm t)).mp haccept
    refine ⟨source.toTerm, (accepts_eq_true_iff_language M source).mp hsourceAccept, ?_⟩
    rw [← BinTree.toTerm_remapTracks]
    congr
    exact (lastTrackExtension_iff_remapTracks _ _).mp hsource
  · rintro ⟨sourceTerm, hsourceAccept, hmap⟩
    let source := BinTree.ofTerm sourceTerm
    have hremap : BinTree.remapTracks Fin.castSucc source = BinTree.ofTerm t := by
      apply BinTree.toTerm_injective
      rw [BinTree.toTerm_remapTracks]
      simpa [source] using hmap
    have hacceptSource : M.accepts source = true := by
      apply (accepts_eq_true_iff_language M source).mpr
      simpa [source] using hsourceAccept
    apply (accepts_eq_true_iff_language M.projectLast (BinTree.ofTerm t)).mp
    apply (projectLast_accepts_eq_true_iff M (BinTree.ofTerm t)).mpr
    exact ⟨source, (lastTrackExtension_iff_remapTracks _ _).mpr hremap,
      hacceptSource⟩

end ExecTreeAutomaton
