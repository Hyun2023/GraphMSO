import GraphMSO.Automata.atomic
import GraphMSO.Automata.projection

/-!
# Formula-to-automata compilation, first layer

This file packages the tracked atomic automata and Boolean closure theorems as
the first MSO-to-automata compilation relation.  The relation currently covers
primitive tree atoms and Boolean connectives over a fixed family of Boolean
tracks.  Quantifiers will extend the same relation by adding a fresh track and
projecting it away with `remapTracksHom`.
-/

namespace BinTree

namespace Automata

open RankedAlphabet
open GraphMSO.TreeLanguage

variable {A : Type}

/-- A compiled tracked language for the quantifier-free/Boolean fragment of
the tree language, relative to fixed first-order and second-order track maps.

The constructors are intentionally relational rather than functional: later
quantifier constructors can choose a larger source track context and project
back to the current one. -/
inductive TrackLanguage :
    {n : ℕ} → (FOVar → Fin n) → (SOVar → Fin n) →
      Formula A → Set (paddedAlphabet (A × TrackBits n)).Term → Prop where
  | false_ {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n} :
      TrackLanguage foTrack soTrack Formula.false_ ∅
  | equal {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      (x y : FOVar) :
      TrackLanguage foTrack soTrack (Formula.equal x y)
        {t | tracksIntersect (foTrack x) (foTrack y) (BinTree.ofTerm t) = true}
  | parent {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      (y x : FOVar) :
      TrackLanguage foTrack soTrack (Formula.parent y x)
        {t |
          (parentTrackSummary (foTrack y) (foTrack x) (BinTree.ofTerm t)).2 =
            true}
  | labelMem {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      (S : Set A) (x : FOVar) :
      TrackLanguage foTrack soTrack (Formula.labelMem S x)
        {t | ∃ a ∈ labelsOnTrack (foTrack x) (BinTree.ofTerm t), a ∈ S}
  | labelMem₂ {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      (R : Set (A × A)) (x y : FOVar) :
      TrackLanguage foTrack soTrack (Formula.labelMem₂ R x y)
        {t |
          let p := labelPairSummary (foTrack x) (foTrack y) (BinTree.ofTerm t)
          ∃ a ∈ p.1, ∃ b ∈ p.2, (a, b) ∈ R}
  | inSet {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      (x : FOVar) (X : SOVar) :
      TrackLanguage foTrack soTrack (Formula.inSet x X)
        {t | tracksIntersect (foTrack x) (soTrack X) (BinTree.ofTerm t) = true}
  | neg {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ : Formula A} {L : Set (paddedAlphabet (A × TrackBits n)).Term}
      (hφ : TrackLanguage foTrack soTrack φ L) :
      TrackLanguage foTrack soTrack (Formula.neg φ) Lᶜ
  | conj {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ ψ : Formula A} {L M : Set (paddedAlphabet (A × TrackBits n)).Term}
      (hφ : TrackLanguage foTrack soTrack φ L)
      (hψ : TrackLanguage foTrack soTrack ψ M) :
      TrackLanguage foTrack soTrack (Formula.conj φ ψ) (L ∩ M)
  | disj {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ ψ : Formula A} {L M : Set (paddedAlphabet (A × TrackBits n)).Term}
      (hφ : TrackLanguage foTrack soTrack φ L)
      (hψ : TrackLanguage foTrack soTrack ψ M) :
      TrackLanguage foTrack soTrack (Formula.disj φ ψ) (L ∪ M)
  | impl {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ ψ : Formula A} {L M : Set (paddedAlphabet (A × TrackBits n)).Term}
      (hφ : TrackLanguage foTrack soTrack φ L)
      (hψ : TrackLanguage foTrack soTrack ψ M) :
      TrackLanguage foTrack soTrack (Formula.impl φ ψ) (Lᶜ ∪ M)
  | biimpl {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ ψ : Formula A}
      {L M : Set (paddedAlphabet (A × TrackBits n)).Term}
      (hφ : TrackLanguage foTrack soTrack φ L)
      (hψ : TrackLanguage foTrack soTrack ψ M) :
      TrackLanguage foTrack soTrack (Formula.biimpl φ ψ)
        ((L ∩ M) ∪ (Lᶜ ∩ Mᶜ))
  | existsFO {n m : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ : Formula A}
      (x : FOVar) (keep : Fin n → Fin m)
      (sourceFO : FOVar → Fin m) (sourceSO : SOVar → Fin m)
      (xTrack : Fin m)
      {L : Set (paddedAlphabet (A × TrackBits m)).Term}
      (hfo : ∀ y, y ≠ x → sourceFO y = keep (foTrack y))
      (hx : sourceFO x = xTrack)
      (hfresh : ∀ i, xTrack ≠ keep i)
      (hso : ∀ X, sourceSO X = keep (soTrack X))
      (hφ : TrackLanguage sourceFO sourceSO φ L) :
      TrackLanguage foTrack soTrack (Formula.existsFO x φ)
        (RankedAlphabet.Term.map (remapTracksHom A keep) ''
          ({t | trackCount xTrack (BinTree.ofTerm t) = Count.one} ∩ L))
  | forallFO {n m : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ : Formula A}
      (x : FOVar) (keep : Fin n → Fin m)
      (sourceFO : FOVar → Fin m) (sourceSO : SOVar → Fin m)
      (xTrack : Fin m)
      {L : Set (paddedAlphabet (A × TrackBits m)).Term}
      (hfo : ∀ y, y ≠ x → sourceFO y = keep (foTrack y))
      (hx : sourceFO x = xTrack)
      (hfresh : ∀ i, xTrack ≠ keep i)
      (hso : ∀ X, sourceSO X = keep (soTrack X))
      (hφ : TrackLanguage sourceFO sourceSO φ L) :
      TrackLanguage foTrack soTrack (Formula.forallFO x φ)
        ((RankedAlphabet.Term.map (remapTracksHom A keep) ''
          ({t | trackCount xTrack (BinTree.ofTerm t) = Count.one} ∩ Lᶜ))ᶜ)
  | existsSO {n m : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ : Formula A}
      (X : SOVar) (keep : Fin n → Fin m)
      (sourceFO : FOVar → Fin m) (sourceSO : SOVar → Fin m)
      (XTrack : Fin m)
      {L : Set (paddedAlphabet (A × TrackBits m)).Term}
      (hfo : ∀ y, sourceFO y = keep (foTrack y))
      (hX : sourceSO X = XTrack)
      (hfresh : ∀ i, XTrack ≠ keep i)
      (hso : ∀ Y, Y ≠ X → sourceSO Y = keep (soTrack Y))
      (hφ : TrackLanguage sourceFO sourceSO φ L) :
      TrackLanguage foTrack soTrack (Formula.existsSO X φ)
        (RankedAlphabet.Term.map (remapTracksHom A keep) '' L)
  | forallSO {n m : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ : Formula A}
      (X : SOVar) (keep : Fin n → Fin m)
      (sourceFO : FOVar → Fin m) (sourceSO : SOVar → Fin m)
      (XTrack : Fin m)
      {L : Set (paddedAlphabet (A × TrackBits m)).Term}
      (hfo : ∀ y, sourceFO y = keep (foTrack y))
      (hX : sourceSO X = XTrack)
      (hfresh : ∀ i, XTrack ≠ keep i)
      (hso : ∀ Y, Y ≠ X → sourceSO Y = keep (soTrack Y))
      (hφ : TrackLanguage sourceFO sourceSO φ L) :
      TrackLanguage foTrack soTrack (Formula.forallSO X φ)
        ((RankedAlphabet.Term.map (remapTracksHom A keep) '' Lᶜ)ᶜ)

namespace TrackLanguage

variable {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
  {φ : Formula A} {L : Set (paddedAlphabet (A × TrackBits n)).Term}

/-- The empty term language is recognizable. -/
theorem recognizable_empty :
    (paddedAlphabet (A × TrackBits n)).Recognizable
      (∅ : Set (paddedAlphabet (A × TrackBits n)).Term) := by
  refine ⟨
    { State := PUnit
      step := fun _ _ => PUnit.unit
      accept := ∅ }, ?_⟩
  ext t
  simp [TreeAutomaton.language]

/-- Track remapping is the projection closure specialized to Boolean-track
alphabets. -/
theorem recognizable_remapTracks {m n : ℕ} (ι : Fin m → Fin n)
    {L : Set (paddedAlphabet (A × TrackBits n)).Term}
    (hL : (paddedAlphabet (A × TrackBits n)).Recognizable L) :
    (paddedAlphabet (A × TrackBits m)).Recognizable
      (RankedAlphabet.Term.map (remapTracksHom A ι) '' L) :=
  hL.map (remapTracksHom A ι)

/-- Every compiled tracked Boolean-fragment language is recognizable. -/
theorem recognizable [Finite A]
    (h : TrackLanguage foTrack soTrack φ L) :
    (paddedAlphabet (A × TrackBits n)).Recognizable L := by
  induction h with
  | false_ =>
      exact recognizable_empty
  | equal x y =>
      exact recognizable_tracksIntersect A _ _
  | parent y x =>
      exact recognizable_parentTrack A _ _
  | labelMem S x =>
      exact recognizable_labelMemTrack A _ S
  | labelMem₂ R x y =>
      exact recognizable_labelMem₂Track A _ _ R
  | inSet x X =>
      exact recognizable_tracksIntersect A _ _
  | neg hφ ihφ =>
      exact ihφ.compl
  | conj hφ hψ ihφ ihψ =>
      exact ihφ.inter ihψ
  | disj hφ hψ ihφ ihψ =>
      exact ihφ.union ihψ
  | impl hφ hψ ihφ ihψ =>
      exact ihφ.compl.union ihψ
  | biimpl hφ hψ ihφ ihψ =>
      exact (ihφ.inter ihψ).union (ihφ.compl.inter ihψ.compl)
  | existsFO x keep sourceFO sourceSO xTrack hfo hx hfresh hso hφ ihφ =>
      exact recognizable_remapTracks keep
        ((recognizable_trackSingleton A xTrack).inter ihφ)
  | forallFO x keep sourceFO sourceSO xTrack hfo hx hfresh hso hφ ihφ =>
      exact (recognizable_remapTracks keep
        ((recognizable_trackSingleton A xTrack).inter ihφ.compl)).compl
  | existsSO X keep sourceFO sourceSO XTrack hfo hX hfresh hso hφ ihφ =>
      exact recognizable_remapTracks keep ihφ
  | forallSO X keep sourceFO sourceSO XTrack hfo hX hfresh hso hφ ihφ =>
      exact (recognizable_remapTracks keep ihφ.compl).compl

end TrackLanguage

/-! ## Quantifier-free correctness

The full compiler relation above already includes projection-shaped
quantifier constructors.  The next theorem proves semantic correctness for
the atom/Boolean fragment; it is the induction base for the later quantified
correctness theorem.
-/

/-- The atom/Boolean fragment of `TrackLanguage`, with no track projections. -/
inductive QFTrackLanguage :
    {n : ℕ} → (FOVar → Fin n) → (SOVar → Fin n) →
      Formula A → Set (paddedAlphabet (A × TrackBits n)).Term → Prop where
  | false_ {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n} :
      QFTrackLanguage foTrack soTrack Formula.false_ ∅
  | equal {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      (x y : FOVar) :
      QFTrackLanguage foTrack soTrack (Formula.equal x y)
        {t | tracksIntersect (foTrack x) (foTrack y) (BinTree.ofTerm t) = true}
  | parent {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      (y x : FOVar) :
      QFTrackLanguage foTrack soTrack (Formula.parent y x)
        {t |
          (parentTrackSummary (foTrack y) (foTrack x) (BinTree.ofTerm t)).2 =
            true}
  | labelMem {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      (S : Set A) (x : FOVar) :
      QFTrackLanguage foTrack soTrack (Formula.labelMem S x)
        {t | ∃ a ∈ labelsOnTrack (foTrack x) (BinTree.ofTerm t), a ∈ S}
  | labelMem₂ {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      (R : Set (A × A)) (x y : FOVar) :
      QFTrackLanguage foTrack soTrack (Formula.labelMem₂ R x y)
        {t |
          let p := labelPairSummary (foTrack x) (foTrack y) (BinTree.ofTerm t)
          ∃ a ∈ p.1, ∃ b ∈ p.2, (a, b) ∈ R}
  | inSet {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      (x : FOVar) (X : SOVar) :
      QFTrackLanguage foTrack soTrack (Formula.inSet x X)
        {t | tracksIntersect (foTrack x) (soTrack X) (BinTree.ofTerm t) = true}
  | neg {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ : Formula A} {L : Set (paddedAlphabet (A × TrackBits n)).Term}
      (hφ : QFTrackLanguage foTrack soTrack φ L) :
      QFTrackLanguage foTrack soTrack (Formula.neg φ) Lᶜ
  | conj {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ ψ : Formula A} {L M : Set (paddedAlphabet (A × TrackBits n)).Term}
      (hφ : QFTrackLanguage foTrack soTrack φ L)
      (hψ : QFTrackLanguage foTrack soTrack ψ M) :
      QFTrackLanguage foTrack soTrack (Formula.conj φ ψ) (L ∩ M)
  | disj {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ ψ : Formula A} {L M : Set (paddedAlphabet (A × TrackBits n)).Term}
      (hφ : QFTrackLanguage foTrack soTrack φ L)
      (hψ : QFTrackLanguage foTrack soTrack ψ M) :
      QFTrackLanguage foTrack soTrack (Formula.disj φ ψ) (L ∪ M)
  | impl {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ ψ : Formula A} {L M : Set (paddedAlphabet (A × TrackBits n)).Term}
      (hφ : QFTrackLanguage foTrack soTrack φ L)
      (hψ : QFTrackLanguage foTrack soTrack ψ M) :
      QFTrackLanguage foTrack soTrack (Formula.impl φ ψ) (Lᶜ ∪ M)
  | biimpl {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
      {φ ψ : Formula A}
      {L M : Set (paddedAlphabet (A × TrackBits n)).Term}
      (hφ : QFTrackLanguage foTrack soTrack φ L)
      (hψ : QFTrackLanguage foTrack soTrack ψ M) :
      QFTrackLanguage foTrack soTrack (Formula.biimpl φ ψ)
        ((L ∩ M) ∪ (Lᶜ ∩ Mᶜ))

namespace QFTrackLanguage

variable {n : ℕ} {foTrack : FOVar → Fin n} {soTrack : SOVar → Fin n}
  {φ : Formula A} {L : Set (paddedAlphabet (A × TrackBits n)).Term}

/-- The quantifier-free fragment embeds in the full tracked compiler
relation. -/
theorem toTrackLanguage (h : QFTrackLanguage foTrack soTrack φ L) :
    TrackLanguage foTrack soTrack φ L := by
  induction h with
  | false_ => exact TrackLanguage.false_
  | equal x y => exact TrackLanguage.equal x y
  | parent y x => exact TrackLanguage.parent y x
  | labelMem S x => exact TrackLanguage.labelMem S x
  | labelMem₂ R x y => exact TrackLanguage.labelMem₂ R x y
  | inSet x X => exact TrackLanguage.inSet x X
  | neg hφ ihφ => exact TrackLanguage.neg ihφ
  | conj hφ hψ ihφ ihψ => exact TrackLanguage.conj ihφ ihψ
  | disj hφ hψ ihφ ihψ => exact TrackLanguage.disj ihφ ihψ
  | impl hφ hψ ihφ ihψ => exact TrackLanguage.impl ihφ ihψ
  | biimpl hφ hψ ihφ ihψ => exact TrackLanguage.biimpl ihφ ihψ

theorem recognizable [Finite A] (h : QFTrackLanguage foTrack soTrack φ L) :
    (paddedAlphabet (A × TrackBits n)).Recognizable L :=
  h.toTrackLanguage.recognizable

/-- Correctness of the atom/Boolean tracked-language compiler. -/
theorem correct (h : QFTrackLanguage foTrack soTrack φ L)
    (t : BinTree (A × TrackBits n))
    (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t foTrack soTrack ρ) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel φ ρ ↔ t.toTerm ∈ L := by
  induction h with
  | false_ =>
      simp [Semantics.SatisfiesAt]
  | equal x y =>
      simpa using satisfiesAt_equal_iff_tracksIntersect t foTrack soTrack ρ hρ x y
  | parent y x =>
      simpa using satisfiesAt_parent_iff_parentTrackSummary t foTrack soTrack ρ hρ y x
  | labelMem S x =>
      simpa using satisfiesAt_labelMem_iff_labelsOnTrack t foTrack soTrack ρ hρ S x
  | labelMem₂ R x y =>
      simpa using
        satisfiesAt_labelMem₂_iff_labelPairSummary t foTrack soTrack ρ hρ R x y
  | inSet x X =>
      simpa using satisfiesAt_inSet_iff_tracksIntersect t foTrack soTrack ρ hρ x X
  | neg hφ ihφ =>
      simpa [Semantics.SatisfiesAt] using not_congr ihφ
  | conj hφ hψ ihφ ihψ =>
      change
        (Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ ∧
          Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ) ↔
          t.toTerm ∈ _ ∩ _
      simpa using and_congr ihφ ihψ
  | disj hφ hψ ihφ ihψ =>
      change
        (Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ ∨
          Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ) ↔
          t.toTerm ∈ _ ∪ _
      simpa using or_congr ihφ ihψ
  | impl hφ hψ ihφ ihψ =>
      change
        (Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ →
          Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ) ↔
          t.toTerm ∈ _ᶜ ∪ _
      rw [Set.mem_union, Set.mem_compl_iff]
      tauto
  | biimpl hφ hψ ihφ ihψ =>
      change
        (Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ ↔
          Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ) ↔
          t.toTerm ∈ (_ ∩ _) ∪ (_ᶜ ∩ _ᶜ)
      rw [Set.mem_union, Set.mem_inter_iff, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_compl_iff]
      tauto

end QFTrackLanguage

end Automata

end BinTree
