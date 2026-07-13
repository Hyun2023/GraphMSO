import GraphMSO.Automata.atomic
import GraphMSO.Automata.projection
import GraphMSO.treeLanguage.modelIso

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
      (hkeep : Function.Injective keep)
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
      (hkeep : Function.Injective keep)
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
      (hkeep : Function.Injective keep)
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
      (hkeep : Function.Injective keep)
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

/-- Equal binary trees give isomorphic tree models. -/
def treeModelIsoOfEq {s t : BinTree A} (h : s = t) :
    s.toTreeModel.Iso t.toTreeModel := by
  subst h
  exact
    { toEquiv := Equiv.refl _
      parentRel_iff := by intro _ _; rfl
      label_eq := by intro _; rfl }

/-- If a source tracked tree remaps to a target tracked tree, then their
track-erased tree models are isomorphic. -/
def remapEraseIso {source target : ℕ} (keep : Fin target → Fin source)
    {s : BinTree (A × TrackBits source)}
    {t : BinTree (A × TrackBits target)}
    (h : remapTracks keep s = t) :
    s.eraseTracks.toTreeModel.Iso t.eraseTracks.toTreeModel :=
  treeModelIsoOfEq (eraseTracks_eq_of_remapTracks_eq keep h)

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

theorem exists_remapTracks_eq_of_toTerm_mem_image {source target : ℕ}
    (keep : Fin target → Fin source)
    {L : Set (paddedAlphabet (A × TrackBits source)).Term}
    {t : BinTree (A × TrackBits target)}
    (h : t.toTerm ∈ RankedAlphabet.Term.map (remapTracksHom A keep) '' L) :
    ∃ s : BinTree (A × TrackBits source),
      s.toTerm ∈ L ∧ remapTracks keep s = t := by
  obtain ⟨u, huL, humap⟩ := h
  refine ⟨BinTree.ofTerm u, ?_, ?_⟩
  · simpa using huL
  · exact remapTracks_eq_of_toTerm_map_eq keep (BinTree.ofTerm u) t
      (by simpa using humap)

theorem existsFO_sound_of_mem_image {source target : ℕ}
    (x : FOVar) (keep : Fin target → Fin source)
    {targetFO : FOVar → Fin target} {targetSO : SOVar → Fin target}
    {sourceFO : FOVar → Fin source} {sourceSO : SOVar → Fin source}
    (xTrack : Fin source) {φ : Formula A}
    {L : Set (paddedAlphabet (A × TrackBits source)).Term}
    (hfo : ∀ y, y ≠ x → sourceFO y = keep (targetFO y))
    (hx : sourceFO x = xTrack)
    (hso : ∀ X, sourceSO X = keep (targetSO X))
    (hφcorr : ∀ (s : BinTree (A × TrackBits source))
      (ρ : Assignment s.eraseTracks.toTreeModel),
        CarriesAssignment s sourceFO sourceSO ρ →
          (Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ ρ ↔
            s.toTerm ∈ L))
    (t : BinTree (A × TrackBits target))
    (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t targetFO targetSO ρ)
    (hmem : t.toTerm ∈ RankedAlphabet.Term.map (remapTracksHom A keep) ''
      ({u | trackCount xTrack (BinTree.ofTerm u) = Count.one} ∩ L)) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel (Formula.existsFO x φ) ρ := by
  obtain ⟨s, hs, hst⟩ :=
    exists_remapTracks_eq_of_toTerm_mem_image (A := A) keep (t := t) hmem
  subst t
  let e := eraseRemapEquiv keep s
  let ρs : Assignment s.eraseTracks.toTreeModel := ρ.mapEquiv e.symm
  have hcount : trackCount xTrack s = Count.one := by
    simpa using hs.1
  have hL : s.toTerm ∈ L := hs.2
  obtain ⟨p, hp, huniq⟩ :=
    (trackCount_eq_one_iff_exists_unique_erased xTrack s).mp hcount
  let oldFO : FOVar → Fin source := fun y => keep (targetFO y)
  let oldSO : SOVar → Fin source := fun X => keep (targetSO X)
  have hbaseOld : CarriesAssignment s oldFO oldSO ρs := by
    exact CarriesAssignment.of_remapTracks keep s hρ (fun _ => rfl) (fun _ => rfl)
  have hbase : CarriesAssignment s oldFO sourceSO ρs := by
    convert hbaseOld using 1
    funext X
    exact hso X
  have hcarry : CarriesAssignment s sourceFO sourceSO (ρs.updateFO x p) := by
    refine CarriesAssignment.updateFO hbase ?_ ?_ ?_
    · intro y hy
      exact hfo y hy
    · simpa [hx] using hp
    · intro q hq
      exact huniq q (by simpa [hx] using hq)
  have hsatSource : Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ
      (ρs.updateFO x p) :=
    (hφcorr s (ρs.updateFO x p) hcarry).mpr hL
  have hsatTarget :
      Semantics.SatisfiesAt (remapTracks keep s).eraseTracks.toTreeModel φ
        ((ρs.updateFO x p).mapEquiv e) :=
    (Semantics.satisfiesAt_mapEquiv_iff (eraseRemapIso keep s) φ
      (ρs.updateFO x p)).mpr hsatSource
  have hassign : (ρs.updateFO x p).mapEquiv e = ρ.updateFO x (e p) := by
    rw [Assignment.mapEquiv_updateFO]
    have hround : ρs.mapEquiv e = ρ := by
      let eM :
          s.eraseTracks.toTreeModel.Node ≃
            (remapTracks keep s).eraseTracks.toTreeModel.Node := e
      change (ρ.mapEquiv eM.symm).mapEquiv eM = ρ
      exact Assignment.mapEquiv_symm_mapEquiv
        (M := s.eraseTracks.toTreeModel)
        (N := (remapTracks keep s).eraseTracks.toTreeModel) eM ρ
    rw [hround]
    rfl
  change ∃ q : (remapTracks keep s).eraseTracks.Pos,
    Semantics.SatisfiesAt (remapTracks keep s).eraseTracks.toTreeModel φ
      (ρ.updateFO x q)
  refine ⟨e p, ?_⟩
  simpa [hassign] using hsatTarget

theorem existsSO_sound_of_mem_image {source target : ℕ}
    (X : SOVar) (keep : Fin target → Fin source)
    {targetFO : FOVar → Fin target} {targetSO : SOVar → Fin target}
    {sourceFO : FOVar → Fin source} {sourceSO : SOVar → Fin source}
    {φ : Formula A}
    {L : Set (paddedAlphabet (A × TrackBits source)).Term}
    (hfo : ∀ y, sourceFO y = keep (targetFO y))
    (hso : ∀ Y, Y ≠ X → sourceSO Y = keep (targetSO Y))
    (hφcorr : ∀ (s : BinTree (A × TrackBits source))
      (ρ : Assignment s.eraseTracks.toTreeModel),
        CarriesAssignment s sourceFO sourceSO ρ →
          (Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ ρ ↔
            s.toTerm ∈ L))
    (t : BinTree (A × TrackBits target))
    (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t targetFO targetSO ρ)
    (hmem : t.toTerm ∈ RankedAlphabet.Term.map (remapTracksHom A keep) '' L) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel (Formula.existsSO X φ) ρ := by
  obtain ⟨s, hL, hst⟩ :=
    exists_remapTracks_eq_of_toTerm_mem_image (A := A) keep (t := t) hmem
  subst t
  let e := eraseRemapEquiv keep s
  let ρs : Assignment s.eraseTracks.toTreeModel := ρ.mapEquiv e.symm
  let oldFO : FOVar → Fin source := fun y => keep (targetFO y)
  let oldSO : SOVar → Fin source := fun Y => keep (targetSO Y)
  have hbaseOld : CarriesAssignment s oldFO oldSO ρs := by
    exact CarriesAssignment.of_remapTracks keep s hρ (fun _ => rfl) (fun _ => rfl)
  have hbase : CarriesAssignment s sourceFO oldSO ρs := by
    convert hbaseOld using 1
    funext y
    exact hfo y
  let S : Set s.eraseTracks.Pos := trackSetErased s (sourceSO X)
  have hcarry : CarriesAssignment s sourceFO sourceSO (ρs.updateSO X S) := by
    refine CarriesAssignment.updateSO hbase ?_ ?_
    · intro Y hY
      exact hso Y hY
    · rfl
  have hsatSource : Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ
      (ρs.updateSO X S) :=
    (hφcorr s (ρs.updateSO X S) hcarry).mpr hL
  have hsatTarget :
      Semantics.SatisfiesAt (remapTracks keep s).eraseTracks.toTreeModel φ
        ((ρs.updateSO X S).mapEquiv e) :=
    (Semantics.satisfiesAt_mapEquiv_iff (eraseRemapIso keep s) φ
      (ρs.updateSO X S)).mpr hsatSource
  have hassign :
      (ρs.updateSO X S).mapEquiv e = ρ.updateSO X (e '' S) := by
    rw [Assignment.mapEquiv_updateSO]
    have hround : ρs.mapEquiv e = ρ := by
      let eM :
          s.eraseTracks.toTreeModel.Node ≃
            (remapTracks keep s).eraseTracks.toTreeModel.Node := e
      change (ρ.mapEquiv eM.symm).mapEquiv eM = ρ
      exact Assignment.mapEquiv_symm_mapEquiv
        (M := s.eraseTracks.toTreeModel)
        (N := (remapTracks keep s).eraseTracks.toTreeModel) eM ρ
    rw [hround]
    rfl
  change ∃ S : Set (remapTracks keep s).eraseTracks.Pos,
    Semantics.SatisfiesAt (remapTracks keep s).eraseTracks.toTreeModel φ
      (ρ.updateSO X S)
  refine ⟨e '' S, ?_⟩
  simpa [hassign] using hsatTarget

theorem existsFO_mem_image_of_satisfies {source target : ℕ}
    (x : FOVar) (keep : Fin target → Fin source)
    {targetFO : FOVar → Fin target} {targetSO : SOVar → Fin target}
    {sourceFO : FOVar → Fin source} {sourceSO : SOVar → Fin source}
    (xTrack : Fin source) {φ : Formula A}
    {L : Set (paddedAlphabet (A × TrackBits source)).Term}
    (hkeep : Function.Injective keep)
    (hfo : ∀ y, y ≠ x → sourceFO y = keep (targetFO y))
    (hx : sourceFO x = xTrack)
    (hfresh : ∀ i, xTrack ≠ keep i)
    (hso : ∀ X, sourceSO X = keep (targetSO X))
    (hφcorr : ∀ (s : BinTree (A × TrackBits source))
      (ρ : Assignment s.eraseTracks.toTreeModel),
        CarriesAssignment s sourceFO sourceSO ρ →
          (Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ ρ ↔
            s.toTerm ∈ L))
    (t : BinTree (A × TrackBits target))
    (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t targetFO targetSO ρ)
    (hsat : Semantics.SatisfiesAt t.eraseTracks.toTreeModel
      (Formula.existsFO x φ) ρ) :
    t.toTerm ∈ RankedAlphabet.Term.map (remapTracksHom A keep) ''
      ({u | trackCount xTrack (BinTree.ofTerm u) = Count.one} ∩ L) := by
  change ∃ p : t.eraseTracks.Pos,
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel φ (ρ.updateFO x p) at hsat
  obtain ⟨p, hp⟩ := hsat
  let tracks :=
    liftTracksWithFresh keep xTrack t ({p} : Set t.eraseTracks.Pos)
  let s : BinTree (A × TrackBits source) := withTracks t.eraseTracks tracks
  let e := eraseWithTracksEquiv t.eraseTracks tracks
  have hcarry : CarriesAssignment s sourceFO sourceSO
      ((ρ.updateFO x p).mapEquiv e) := by
    simpa [s, tracks, e] using
      CarriesAssignment.of_liftTracksWithFresh_updateFO
        keep xTrack t hρ hkeep p hfo hx hfresh hso
  have hsatSource :
      Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ
        ((ρ.updateFO x p).mapEquiv e) := by
    simpa [s, tracks, e] using
      (Semantics.satisfiesAt_mapEquiv_iff
        (eraseWithTracksIso t.eraseTracks tracks) φ
        (ρ.updateFO x p)).mpr hp
  have hL : s.toTerm ∈ L :=
    (hφcorr s ((ρ.updateFO x p).mapEquiv e) hcarry).mp hsatSource
  have hcount : trackCount xTrack s = Count.one := by
    simpa [s, tracks] using
      trackCount_liftTracksWithFresh_singleton keep xTrack t hfresh p
  have hsremap : remapTracks keep s = t := by
    simpa [s, tracks] using
      remapTracks_withTracks_liftTracksWithFresh_eq
        keep xTrack t ({p} : Set t.eraseTracks.Pos) hkeep
  refine ⟨s.toTerm, ?_, ?_⟩
  · constructor
    · simpa using hcount
    · exact hL
  · simpa [toTerm_remapTracks] using congrArg BinTree.toTerm hsremap

theorem existsSO_mem_image_of_satisfies {source target : ℕ}
    (X : SOVar) (keep : Fin target → Fin source)
    {targetFO : FOVar → Fin target} {targetSO : SOVar → Fin target}
    {sourceFO : FOVar → Fin source} {sourceSO : SOVar → Fin source}
    (XTrack : Fin source) {φ : Formula A}
    {L : Set (paddedAlphabet (A × TrackBits source)).Term}
    (hkeep : Function.Injective keep)
    (hfo : ∀ y, sourceFO y = keep (targetFO y))
    (hX : sourceSO X = XTrack)
    (hfresh : ∀ i, XTrack ≠ keep i)
    (hso : ∀ Y, Y ≠ X → sourceSO Y = keep (targetSO Y))
    (hφcorr : ∀ (s : BinTree (A × TrackBits source))
      (ρ : Assignment s.eraseTracks.toTreeModel),
        CarriesAssignment s sourceFO sourceSO ρ →
          (Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ ρ ↔
            s.toTerm ∈ L))
    (t : BinTree (A × TrackBits target))
    (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t targetFO targetSO ρ)
    (hsat : Semantics.SatisfiesAt t.eraseTracks.toTreeModel
      (Formula.existsSO X φ) ρ) :
    t.toTerm ∈ RankedAlphabet.Term.map (remapTracksHom A keep) '' L := by
  change ∃ S : Set t.eraseTracks.Pos,
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel φ (ρ.updateSO X S) at hsat
  obtain ⟨S, hS⟩ := hsat
  let tracks := liftTracksWithFresh keep XTrack t S
  let s : BinTree (A × TrackBits source) := withTracks t.eraseTracks tracks
  let e := eraseWithTracksEquiv t.eraseTracks tracks
  have hcarry : CarriesAssignment s sourceFO sourceSO
      ((ρ.updateSO X S).mapEquiv e) := by
    simpa [s, tracks, e] using
      CarriesAssignment.of_liftTracksWithFresh_updateSO
        keep XTrack t hρ hkeep S hfo hX hfresh hso
  have hsatSource :
      Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ
        ((ρ.updateSO X S).mapEquiv e) := by
    simpa [s, tracks, e] using
      (Semantics.satisfiesAt_mapEquiv_iff
        (eraseWithTracksIso t.eraseTracks tracks) φ
        (ρ.updateSO X S)).mpr hS
  have hL : s.toTerm ∈ L :=
    (hφcorr s ((ρ.updateSO X S).mapEquiv e) hcarry).mp hsatSource
  have hsremap : remapTracks keep s = t := by
    simpa [s, tracks] using
      remapTracks_withTracks_liftTracksWithFresh_eq keep XTrack t S hkeep
  exact ⟨s.toTerm, hL,
    by simpa [toTerm_remapTracks] using congrArg BinTree.toTerm hsremap⟩

theorem existsFO_correct {source target : ℕ}
    (x : FOVar) (keep : Fin target → Fin source)
    {targetFO : FOVar → Fin target} {targetSO : SOVar → Fin target}
    {sourceFO : FOVar → Fin source} {sourceSO : SOVar → Fin source}
    (xTrack : Fin source) {φ : Formula A}
    {L : Set (paddedAlphabet (A × TrackBits source)).Term}
    (hkeep : Function.Injective keep)
    (hfo : ∀ y, y ≠ x → sourceFO y = keep (targetFO y))
    (hx : sourceFO x = xTrack)
    (hfresh : ∀ i, xTrack ≠ keep i)
    (hso : ∀ X, sourceSO X = keep (targetSO X))
    (hφcorr : ∀ (s : BinTree (A × TrackBits source))
      (ρ : Assignment s.eraseTracks.toTreeModel),
        CarriesAssignment s sourceFO sourceSO ρ →
          (Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ ρ ↔
            s.toTerm ∈ L))
    (t : BinTree (A × TrackBits target))
    (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t targetFO targetSO ρ) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel
        (Formula.existsFO x φ) ρ ↔
      t.toTerm ∈ RankedAlphabet.Term.map (remapTracksHom A keep) ''
        ({u | trackCount xTrack (BinTree.ofTerm u) = Count.one} ∩ L) := by
  constructor
  · exact existsFO_mem_image_of_satisfies x keep xTrack hkeep hfo hx hfresh hso
      hφcorr t ρ hρ
  · exact existsFO_sound_of_mem_image x keep xTrack hfo hx hso
      hφcorr t ρ hρ

theorem existsSO_correct {source target : ℕ}
    (X : SOVar) (keep : Fin target → Fin source)
    {targetFO : FOVar → Fin target} {targetSO : SOVar → Fin target}
    {sourceFO : FOVar → Fin source} {sourceSO : SOVar → Fin source}
    (XTrack : Fin source) {φ : Formula A}
    {L : Set (paddedAlphabet (A × TrackBits source)).Term}
    (hkeep : Function.Injective keep)
    (hfo : ∀ y, sourceFO y = keep (targetFO y))
    (hX : sourceSO X = XTrack)
    (hfresh : ∀ i, XTrack ≠ keep i)
    (hso : ∀ Y, Y ≠ X → sourceSO Y = keep (targetSO Y))
    (hφcorr : ∀ (s : BinTree (A × TrackBits source))
      (ρ : Assignment s.eraseTracks.toTreeModel),
        CarriesAssignment s sourceFO sourceSO ρ →
          (Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ ρ ↔
            s.toTerm ∈ L))
    (t : BinTree (A × TrackBits target))
    (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t targetFO targetSO ρ) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel
        (Formula.existsSO X φ) ρ ↔
      t.toTerm ∈ RankedAlphabet.Term.map (remapTracksHom A keep) '' L := by
  constructor
  · exact existsSO_mem_image_of_satisfies X keep XTrack hkeep hfo hX hfresh hso
      hφcorr t ρ hρ
  · exact existsSO_sound_of_mem_image X keep hfo hso hφcorr t ρ hρ

theorem forallFO_correct {source target : ℕ}
    (x : FOVar) (keep : Fin target → Fin source)
    {targetFO : FOVar → Fin target} {targetSO : SOVar → Fin target}
    {sourceFO : FOVar → Fin source} {sourceSO : SOVar → Fin source}
    (xTrack : Fin source) {φ : Formula A}
    {L : Set (paddedAlphabet (A × TrackBits source)).Term}
    (hkeep : Function.Injective keep)
    (hfo : ∀ y, y ≠ x → sourceFO y = keep (targetFO y))
    (hx : sourceFO x = xTrack)
    (hfresh : ∀ i, xTrack ≠ keep i)
    (hso : ∀ X, sourceSO X = keep (targetSO X))
    (hφcorr : ∀ (s : BinTree (A × TrackBits source))
      (ρ : Assignment s.eraseTracks.toTreeModel),
        CarriesAssignment s sourceFO sourceSO ρ →
          (Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ ρ ↔
            s.toTerm ∈ L))
    (t : BinTree (A × TrackBits target))
    (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t targetFO targetSO ρ) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel
        (Formula.forallFO x φ) ρ ↔
      t.toTerm ∈
        (RankedAlphabet.Term.map (remapTracksHom A keep) ''
          ({u | trackCount xTrack (BinTree.ofTerm u) = Count.one} ∩ Lᶜ))ᶜ := by
  classical
  have hnegcorr :
      ∀ (s : BinTree (A × TrackBits source))
        (ρ : Assignment s.eraseTracks.toTreeModel),
        CarriesAssignment s sourceFO sourceSO ρ →
          (Semantics.SatisfiesAt s.eraseTracks.toTreeModel
              (Formula.neg φ) ρ ↔
            s.toTerm ∈ Lᶜ) := by
    intro s ρ hcarry
    change (¬ Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ ρ) ↔
      s.toTerm ∈ Lᶜ
    rw [Set.mem_compl_iff]
    exact not_congr (hφcorr s ρ hcarry)
  have hex := existsFO_correct (A := A) x keep xTrack hkeep hfo hx hfresh hso
    hnegcorr t ρ hρ
  rw [Set.mem_compl_iff]
  constructor
  · intro hall himage
    have hexSat := hex.mpr himage
    change ∃ p : t.eraseTracks.Pos,
      ¬ Semantics.SatisfiesAt t.eraseTracks.toTreeModel φ
        (ρ.updateFO x p) at hexSat
    obtain ⟨p, hp⟩ := hexSat
    exact hp (hall p)
  · intro hnot p
    by_contra hp
    exact hnot (hex.mp ⟨p, hp⟩)

theorem forallSO_correct {source target : ℕ}
    (X : SOVar) (keep : Fin target → Fin source)
    {targetFO : FOVar → Fin target} {targetSO : SOVar → Fin target}
    {sourceFO : FOVar → Fin source} {sourceSO : SOVar → Fin source}
    (XTrack : Fin source) {φ : Formula A}
    {L : Set (paddedAlphabet (A × TrackBits source)).Term}
    (hkeep : Function.Injective keep)
    (hfo : ∀ y, sourceFO y = keep (targetFO y))
    (hX : sourceSO X = XTrack)
    (hfresh : ∀ i, XTrack ≠ keep i)
    (hso : ∀ Y, Y ≠ X → sourceSO Y = keep (targetSO Y))
    (hφcorr : ∀ (s : BinTree (A × TrackBits source))
      (ρ : Assignment s.eraseTracks.toTreeModel),
        CarriesAssignment s sourceFO sourceSO ρ →
          (Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ ρ ↔
            s.toTerm ∈ L))
    (t : BinTree (A × TrackBits target))
    (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t targetFO targetSO ρ) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel
        (Formula.forallSO X φ) ρ ↔
      t.toTerm ∈
        (RankedAlphabet.Term.map (remapTracksHom A keep) '' Lᶜ)ᶜ := by
  classical
  have hnegcorr :
      ∀ (s : BinTree (A × TrackBits source))
        (ρ : Assignment s.eraseTracks.toTreeModel),
        CarriesAssignment s sourceFO sourceSO ρ →
          (Semantics.SatisfiesAt s.eraseTracks.toTreeModel
              (Formula.neg φ) ρ ↔
            s.toTerm ∈ Lᶜ) := by
    intro s ρ hcarry
    change (¬ Semantics.SatisfiesAt s.eraseTracks.toTreeModel φ ρ) ↔
      s.toTerm ∈ Lᶜ
    rw [Set.mem_compl_iff]
    exact not_congr (hφcorr s ρ hcarry)
  have hex := existsSO_correct (A := A) X keep XTrack hkeep hfo hX hfresh hso
    hnegcorr t ρ hρ
  rw [Set.mem_compl_iff]
  constructor
  · intro hall himage
    have hexSat := hex.mpr himage
    change ∃ S : Set t.eraseTracks.Pos,
      ¬ Semantics.SatisfiesAt t.eraseTracks.toTreeModel φ
        (ρ.updateSO X S) at hexSat
    obtain ⟨S, hS⟩ := hexSat
    exact hS (hall S)
  · intro hnot S
    by_contra hS
    exact hnot (hex.mp ⟨S, hS⟩)

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
  | existsFO x keep sourceFO sourceSO xTrack hkeep hfo hx hfresh hso hφ ihφ =>
      exact recognizable_remapTracks keep
        ((recognizable_trackSingleton A xTrack).inter ihφ)
  | forallFO x keep sourceFO sourceSO xTrack hkeep hfo hx hfresh hso hφ ihφ =>
      exact (recognizable_remapTracks keep
        ((recognizable_trackSingleton A xTrack).inter ihφ.compl)).compl
  | existsSO X keep sourceFO sourceSO XTrack hkeep hfo hX hfresh hso hφ ihφ =>
      exact recognizable_remapTracks keep ihφ
  | forallSO X keep sourceFO sourceSO XTrack hkeep hfo hX hfresh hso hφ ihφ =>
      exact (recognizable_remapTracks keep ihφ.compl).compl

/-- Correctness of the full tracked-language compiler relation. -/
theorem correct (h : TrackLanguage foTrack soTrack φ L)
    (t : BinTree (A × TrackBits n))
    (ρ : Assignment t.eraseTracks.toTreeModel)
    (hρ : CarriesAssignment t foTrack soTrack ρ) :
    Semantics.SatisfiesAt t.eraseTracks.toTreeModel φ ρ ↔ t.toTerm ∈ L := by
  induction h with
  | false_ =>
      simp [Semantics.SatisfiesAt]
  | equal x y =>
      simpa using satisfiesAt_equal_iff_tracksIntersect t _ _ ρ hρ x y
  | parent y x =>
      simpa using satisfiesAt_parent_iff_parentTrackSummary t _ _ ρ hρ y x
  | labelMem S x =>
      simpa using satisfiesAt_labelMem_iff_labelsOnTrack t _ _ ρ hρ S x
  | labelMem₂ R x y =>
      simpa using
        satisfiesAt_labelMem₂_iff_labelPairSummary t _ _ ρ hρ R x y
  | inSet x X =>
      simpa using satisfiesAt_inSet_iff_tracksIntersect t _ _ ρ hρ x X
  | neg hφ ihφ =>
      simpa [Semantics.SatisfiesAt] using not_congr (ihφ t ρ hρ)
  | conj hφ hψ ihφ ihψ =>
      change
        (Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ ∧
          Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ) ↔
          t.toTerm ∈ _ ∩ _
      simpa using and_congr (ihφ t ρ hρ) (ihψ t ρ hρ)
  | disj hφ hψ ihφ ihψ =>
      change
        (Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ ∨
          Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ) ↔
          t.toTerm ∈ _ ∪ _
      simpa using or_congr (ihφ t ρ hρ) (ihψ t ρ hρ)
  | impl hφ hψ ihφ ihψ =>
      change
        (Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ →
          Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ) ↔
          t.toTerm ∈ _ᶜ ∪ _
      rw [Set.mem_union, Set.mem_compl_iff]
      have hφiff := ihφ t ρ hρ
      have hψiff := ihψ t ρ hρ
      tauto
  | biimpl hφ hψ ihφ ihψ =>
      change
        (Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ ↔
          Semantics.SatisfiesAt t.eraseTracks.toTreeModel _ ρ) ↔
          t.toTerm ∈ (_ ∩ _) ∪ (_ᶜ ∩ _ᶜ)
      rw [Set.mem_union, Set.mem_inter_iff, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_compl_iff]
      have hφiff := ihφ t ρ hρ
      have hψiff := ihψ t ρ hρ
      tauto
  | existsFO x keep sourceFO sourceSO xTrack hkeep hfo hx hfresh hso hφ ihφ =>
      exact existsFO_correct x keep xTrack hkeep hfo hx hfresh hso ihφ t ρ hρ
  | forallFO x keep sourceFO sourceSO xTrack hkeep hfo hx hfresh hso hφ ihφ =>
      exact forallFO_correct x keep xTrack hkeep hfo hx hfresh hso ihφ t ρ hρ
  | existsSO X keep sourceFO sourceSO XTrack hkeep hfo hX hfresh hso hφ ihφ =>
      exact existsSO_correct X keep XTrack hkeep hfo hX hfresh hso ihφ t ρ hρ
  | forallSO X keep sourceFO sourceSO XTrack hkeep hfo hX hfresh hso hφ ihφ =>
      exact forallSO_correct X keep XTrack hkeep hfo hX hfresh hso ihφ t ρ hρ

/-- Formula induction compiler: starting from any current track context, every
tree formula has a compiled tracked language.  Quantifiers allocate one fresh
track by embedding the old context with `Fin.castSucc` and using `Fin.last`. -/
theorem exists_compile :
    ∀ (φ : Formula A) (n : ℕ)
      (foTrack : FOVar → Fin n) (soTrack : SOVar → Fin n),
      ∃ L : Set (paddedAlphabet (A × TrackBits n)).Term,
        TrackLanguage foTrack soTrack φ L
  | Formula.false_, n, foTrack, soTrack =>
      ⟨∅, TrackLanguage.false_⟩
  | Formula.equal x y, n, foTrack, soTrack =>
      ⟨_, TrackLanguage.equal x y⟩
  | Formula.parent y x, n, foTrack, soTrack =>
      ⟨_, TrackLanguage.parent y x⟩
  | Formula.labelMem S x, n, foTrack, soTrack =>
      ⟨_, TrackLanguage.labelMem S x⟩
  | Formula.labelMem₂ R x y, n, foTrack, soTrack =>
      ⟨_, TrackLanguage.labelMem₂ R x y⟩
  | Formula.inSet x X, n, foTrack, soTrack =>
      ⟨_, TrackLanguage.inSet x X⟩
  | Formula.neg φ, n, foTrack, soTrack =>
      let ⟨L, hL⟩ := exists_compile φ n foTrack soTrack
      ⟨Lᶜ, TrackLanguage.neg hL⟩
  | Formula.conj φ ψ, n, foTrack, soTrack =>
      let ⟨L, hL⟩ := exists_compile φ n foTrack soTrack
      let ⟨M, hM⟩ := exists_compile ψ n foTrack soTrack
      ⟨L ∩ M, TrackLanguage.conj hL hM⟩
  | Formula.disj φ ψ, n, foTrack, soTrack =>
      let ⟨L, hL⟩ := exists_compile φ n foTrack soTrack
      let ⟨M, hM⟩ := exists_compile ψ n foTrack soTrack
      ⟨L ∪ M, TrackLanguage.disj hL hM⟩
  | Formula.impl φ ψ, n, foTrack, soTrack =>
      let ⟨L, hL⟩ := exists_compile φ n foTrack soTrack
      let ⟨M, hM⟩ := exists_compile ψ n foTrack soTrack
      ⟨Lᶜ ∪ M, TrackLanguage.impl hL hM⟩
  | Formula.biimpl φ ψ, n, foTrack, soTrack =>
      let ⟨L, hL⟩ := exists_compile φ n foTrack soTrack
      let ⟨M, hM⟩ := exists_compile ψ n foTrack soTrack
      ⟨(L ∩ M) ∪ (Lᶜ ∩ Mᶜ), TrackLanguage.biimpl hL hM⟩
  | Formula.existsFO x φ, n, foTrack, soTrack =>
      let keep : Fin n → Fin (n + 1) := Fin.castSucc
      let sourceFO : FOVar → Fin (n + 1) := fun y =>
        if y = x then Fin.last n else keep (foTrack y)
      let sourceSO : SOVar → Fin (n + 1) := fun X => keep (soTrack X)
      let ⟨L, hL⟩ := exists_compile φ (n + 1) sourceFO sourceSO
      ⟨_, TrackLanguage.existsFO x keep sourceFO sourceSO (Fin.last n)
        (Fin.castSucc_injective n)
        (by intro y hy; simp [sourceFO, hy])
        (by simp [sourceFO])
        (by intro i; exact (Fin.castSucc_ne_last i).symm)
        (by intro X; simp [sourceSO])
        hL⟩
  | Formula.forallFO x φ, n, foTrack, soTrack =>
      let keep : Fin n → Fin (n + 1) := Fin.castSucc
      let sourceFO : FOVar → Fin (n + 1) := fun y =>
        if y = x then Fin.last n else keep (foTrack y)
      let sourceSO : SOVar → Fin (n + 1) := fun X => keep (soTrack X)
      let ⟨L, hL⟩ := exists_compile φ (n + 1) sourceFO sourceSO
      ⟨_, TrackLanguage.forallFO x keep sourceFO sourceSO (Fin.last n)
        (Fin.castSucc_injective n)
        (by intro y hy; simp [sourceFO, hy])
        (by simp [sourceFO])
        (by intro i; exact (Fin.castSucc_ne_last i).symm)
        (by intro X; simp [sourceSO])
        hL⟩
  | Formula.existsSO X φ, n, foTrack, soTrack =>
      let keep : Fin n → Fin (n + 1) := Fin.castSucc
      let sourceFO : FOVar → Fin (n + 1) := fun y => keep (foTrack y)
      let sourceSO : SOVar → Fin (n + 1) := fun Y =>
        if Y = X then Fin.last n else keep (soTrack Y)
      let ⟨L, hL⟩ := exists_compile φ (n + 1) sourceFO sourceSO
      ⟨_, TrackLanguage.existsSO X keep sourceFO sourceSO (Fin.last n)
        (Fin.castSucc_injective n)
        (by intro y; simp [sourceFO])
        (by simp [sourceSO])
        (by intro i; exact (Fin.castSucc_ne_last i).symm)
        (by intro Y hY; simp [sourceSO, hY])
        hL⟩
  | Formula.forallSO X φ, n, foTrack, soTrack =>
      let keep : Fin n → Fin (n + 1) := Fin.castSucc
      let sourceFO : FOVar → Fin (n + 1) := fun y => keep (foTrack y)
      let sourceSO : SOVar → Fin (n + 1) := fun Y =>
        if Y = X then Fin.last n else keep (soTrack Y)
      let ⟨L, hL⟩ := exists_compile φ (n + 1) sourceFO sourceSO
      ⟨_, TrackLanguage.forallSO X keep sourceFO sourceSO (Fin.last n)
        (Fin.castSucc_injective n)
        (by intro y; simp [sourceFO])
        (by simp [sourceSO])
        (by intro i; exact (Fin.castSucc_ne_last i).symm)
        (by intro Y hY; simp [sourceSO, hY])
        hL⟩

theorem exists_recognizable_compile [Finite A]
    (φ : Formula A) (n : ℕ)
    (foTrack : FOVar → Fin n) (soTrack : SOVar → Fin n) :
    ∃ L : Set (paddedAlphabet (A × TrackBits n)).Term,
      TrackLanguage foTrack soTrack φ L ∧
        (paddedAlphabet (A × TrackBits n)).Recognizable L := by
  obtain ⟨L, hL⟩ := exists_compile φ n foTrack soTrack
  exact ⟨L, hL, hL.recognizable⟩

/-- Add `n` empty Boolean tracks to labels as an alphabet homomorphism. -/
def addEmptyTracksHom (A : Type) (n : ℕ) :
    (paddedAlphabet A).Hom (paddedAlphabet (A × TrackBits n)) :=
  paddedMapHom fun a => (a, fun _ : Fin n => false)

@[simp] theorem toTerm_withTracks_empty {n : ℕ} (t : BinTree A) :
    (withTracks t (fun _ => (∅ : Set t.Pos))).toTerm =
      t.toTerm.map (addEmptyTracksHom A n) := by
  rw [withTracks_empty, toTerm_map]
  rfl

/-- Thatcher-Wright/Courcelle automata theorem for ordered binary tree
sentences: every tree MSO sentence denotes a recognizable language of padded
ordered binary trees. -/
theorem exists_recognizable_sentence_language [Finite A] (φ : Formula A) :
    ∃ L : Set (paddedAlphabet A).Term,
      (paddedAlphabet A).Recognizable L ∧
        ∀ t : BinTree A,
          Semantics.Satisfies t.toTreeModel φ ↔ t.toTerm ∈ L := by
  let track : FOVar → Fin 1 := fun _ => 0
  obtain ⟨L, hL, hrec⟩ := exists_recognizable_compile φ 1 track track
  let π := addEmptyTracksHom A 1
  refine ⟨RankedAlphabet.Term.map π ⁻¹' L, hrec.comap π, ?_⟩
  intro t
  let tracks : Fin 1 → Set t.Pos := fun _ => ∅
  let tracked : BinTree (A × TrackBits 1) := withTracks t tracks
  let e := eraseWithTracksEquiv t tracks
  let ρ : Assignment tracked.eraseTracks.toTreeModel :=
    (Assignment.empty t.toTreeModel).mapEquiv e
  have hcarry : CarriesAssignment tracked track track ρ := by
    simpa [tracked, tracks, ρ, e, track] using
      CarriesAssignment.empty_withTracks_empty t track track
  have hiso :
      Semantics.SatisfiesAt tracked.eraseTracks.toTreeModel φ ρ ↔
        Semantics.SatisfiesAt t.toTreeModel φ (Assignment.empty t.toTreeModel) := by
    simpa [tracked, tracks, ρ, e] using
      Semantics.satisfiesAt_mapEquiv_iff
        (eraseWithTracksIso t tracks) φ (Assignment.empty t.toTreeModel)
  have hcorr := hL.correct tracked ρ hcarry
  have hsentence : Semantics.Satisfies t.toTreeModel φ ↔ tracked.toTerm ∈ L :=
    hiso.symm.trans hcorr
  simpa [Semantics.Satisfies, tracked, tracks, π] using hsentence

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
