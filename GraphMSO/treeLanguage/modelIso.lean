import GraphMSO.treeLanguage.semantics

/-!
# Isomorphisms of tree models

Satisfaction of tree MSO formulas is invariant under isomorphism of models.
This is the glue of the final assembly: translation correctness speaks about
the (unordered) encoded model of a decomposition, while automata run on an
ordered binary tree; an isomorphism of tree models transfers satisfaction
between the two.
-/

namespace GraphMSO.TreeLanguage

universe u v w

variable {A : Type u}

/-- An isomorphism of tree models: a bijection of nodes preserving the
parent relation and the labels. -/
structure TreeModel.Iso (M : TreeModel A) (N : TreeModel A) where
  /-- The underlying bijection of nodes. -/
  toEquiv : M.Node ≃ N.Node
  /-- The bijection transports the parent relation. -/
  parentRel_iff : ∀ p q : M.Node,
    N.parentRel (toEquiv p) (toEquiv q) ↔ M.parentRel p q
  /-- The bijection preserves labels. -/
  label_eq : ∀ p : M.Node, N.label (toEquiv p) = M.label p

namespace Assignment

variable {M N : TreeModel A}

/-- Transport an assignment along a bijection of nodes. -/
def mapEquiv (e : M.Node ≃ N.Node) (ρ : Assignment M) : Assignment N where
  fo := fun x => (ρ.fo x).map e
  so := fun X => e '' ρ.so X

@[simp] theorem mapEquiv_fo (e : M.Node ≃ N.Node) (ρ : Assignment M)
    (x : FOVar) :
    (ρ.mapEquiv e).fo x = (ρ.fo x).map e :=
  rfl

@[simp] theorem mapEquiv_so (e : M.Node ≃ N.Node) (ρ : Assignment M)
    (X : SOVar) :
    (ρ.mapEquiv e).so X = e '' ρ.so X :=
  rfl

theorem mapEquiv_updateFO (e : M.Node ≃ N.Node) (ρ : Assignment M)
    (x : FOVar) (v : M.Node) :
    (ρ.updateFO x v).mapEquiv e = (ρ.mapEquiv e).updateFO x (e v) := by
  refine Assignment.ext ?_ rfl
  funext y
  show ((ρ.updateFO x v).fo y).map e = _
  simp only [updateFO, mapEquiv]
  by_cases h : y = x <;> simp [h]

theorem mapEquiv_updateSO (e : M.Node ≃ N.Node) (ρ : Assignment M)
    (X : SOVar) (S : Set M.Node) :
    (ρ.updateSO X S).mapEquiv e = (ρ.mapEquiv e).updateSO X (e '' S) := by
  refine Assignment.ext rfl ?_
  funext Y
  show e '' (ρ.updateSO X S).so Y = _
  simp only [updateSO, mapEquiv]
  by_cases h : Y = X <;> simp [h]

@[simp] theorem mapEquiv_symm_mapEquiv (e : M.Node ≃ N.Node)
    (ρ : Assignment N) :
    (ρ.mapEquiv e.symm).mapEquiv e = ρ := by
  refine Assignment.ext ?_ ?_
  · funext x
    cases h : ρ.fo x with
    | none => simp [mapEquiv, h]
    | some p => simp [mapEquiv, h]
  · funext X
    ext p
    constructor
    · rintro ⟨q, ⟨r, hr, hrq⟩, hqp⟩
      rw [← hqp, ← hrq]
      simpa using hr
    · intro hp
      exact ⟨e.symm p, ⟨p, hp, rfl⟩, by simp⟩

@[simp] theorem mapEquiv_mapEquiv_symm (e : M.Node ≃ N.Node)
    (ρ : Assignment M) :
    (ρ.mapEquiv e).mapEquiv e.symm = ρ := by
  simpa using mapEquiv_symm_mapEquiv (M := N) (N := M) e.symm ρ

end Assignment

namespace Semantics

open Formula

variable {M N : TreeModel A}

/-- Satisfaction is invariant under isomorphism of tree models. -/
theorem satisfiesAt_mapEquiv_iff (iso : M.Iso N) (φ : Formula A)
    (ρ : Assignment M) :
    SatisfiesAt N φ (ρ.mapEquiv iso.toEquiv) ↔ SatisfiesAt M φ ρ := by
  induction φ generalizing ρ with
  | false_ => exact Iff.rfl
  | equal x y =>
      show (∃ n : N.Node, (ρ.fo x).map _ = some n ∧ (ρ.fo y).map _ = some n) ↔
        (∃ m : M.Node, ρ.fo x = some m ∧ ρ.fo y = some m)
      constructor
      · rintro ⟨n, hx, hy⟩
        obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hx
        obtain ⟨m', hm', hmm⟩ := Option.map_eq_some_iff.mp hy
        exact ⟨m, hm, by rwa [iso.toEquiv.injective hmm] at hm'⟩
      · rintro ⟨m, hx, hy⟩
        exact ⟨iso.toEquiv m, by rw [hx]; rfl, by rw [hy]; rfl⟩
  | parent y x =>
      show (∃ p n : N.Node, (ρ.fo y).map _ = some p ∧ (ρ.fo x).map _ = some n ∧
          N.parentRel p n) ↔
        (∃ p n : M.Node, ρ.fo y = some p ∧ ρ.fo x = some n ∧ M.parentRel p n)
      constructor
      · rintro ⟨p, n, hy, hx, hpn⟩
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hy
        obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hx
        exact ⟨q, m, hq, hm, (iso.parentRel_iff q m).mp hpn⟩
      · rintro ⟨p, n, hy, hx, hpn⟩
        exact ⟨iso.toEquiv p, iso.toEquiv n, by rw [hy]; rfl, by rw [hx]; rfl,
          (iso.parentRel_iff p n).mpr hpn⟩
  | labelMem S x =>
      show (∃ n : N.Node, (ρ.fo x).map _ = some n ∧ N.label n ∈ S) ↔
        (∃ m : M.Node, ρ.fo x = some m ∧ M.label m ∈ S)
      constructor
      · rintro ⟨n, hx, hn⟩
        obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hx
        exact ⟨m, hm, by rwa [iso.label_eq m] at hn⟩
      · rintro ⟨m, hx, hm⟩
        exact ⟨iso.toEquiv m, by rw [hx]; rfl, by rwa [iso.label_eq m]⟩
  | labelMem₂ R x y =>
      show (∃ p n : N.Node, (ρ.fo x).map _ = some p ∧ (ρ.fo y).map _ = some n ∧
          (N.label p, N.label n) ∈ R) ↔ _
      constructor
      · rintro ⟨p, n, hx, hy, hpn⟩
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hx
        obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hy
        exact ⟨q, m, hq, hm, by rwa [iso.label_eq q, iso.label_eq m] at hpn⟩
      · rintro ⟨p, n, hx, hy, hpn⟩
        exact ⟨iso.toEquiv p, iso.toEquiv n, by rw [hx]; rfl, by rw [hy]; rfl,
          by rwa [iso.label_eq p, iso.label_eq n]⟩
  | inSet x X =>
      show (∃ n : N.Node, (ρ.fo x).map _ = some n ∧ n ∈ _ '' ρ.so X) ↔
        (∃ m : M.Node, ρ.fo x = some m ∧ m ∈ ρ.so X)
      constructor
      · rintro ⟨n, hx, hn⟩
        obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hx
        obtain ⟨m', hm', hmm⟩ := hn
        exact ⟨m, hm, by rwa [← iso.toEquiv.injective hmm]⟩
      · rintro ⟨m, hx, hm⟩
        exact ⟨iso.toEquiv m, by rw [hx]; rfl, ⟨m, hm, rfl⟩⟩
  | neg φ ih => exact not_congr (ih ρ)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ ρ) (ihψ ρ)
  | disj φ ψ ihφ ihψ => exact or_congr (ihφ ρ) (ihψ ρ)
  | impl φ ψ ihφ ihψ => exact imp_congr (ihφ ρ) (ihψ ρ)
  | biimpl φ ψ ihφ ihψ => exact iff_congr (ihφ ρ) (ihψ ρ)
  | existsFO x φ ih =>
      show (∃ n : N.Node, SatisfiesAt N φ ((ρ.mapEquiv _).updateFO x n)) ↔
        (∃ v : M.Node, SatisfiesAt M φ (ρ.updateFO x v))
      constructor
      · rintro ⟨n, hn⟩
        refine ⟨iso.toEquiv.symm n, (ih _).mp ?_⟩
        rw [Assignment.mapEquiv_updateFO, Equiv.apply_symm_apply]
        exact hn
      · rintro ⟨v, hv⟩
        refine ⟨iso.toEquiv v, ?_⟩
        rw [← Assignment.mapEquiv_updateFO]
        exact (ih _).mpr hv
  | forallFO x φ ih =>
      show (∀ n : N.Node, SatisfiesAt N φ ((ρ.mapEquiv _).updateFO x n)) ↔
        (∀ v : M.Node, SatisfiesAt M φ (ρ.updateFO x v))
      constructor
      · intro h v
        refine (ih _).mp ?_
        rw [Assignment.mapEquiv_updateFO]
        exact h (iso.toEquiv v)
      · intro h n
        have := (ih (ρ.updateFO x (iso.toEquiv.symm n))).mpr
          (h (iso.toEquiv.symm n))
        rwa [Assignment.mapEquiv_updateFO, Equiv.apply_symm_apply] at this
  | existsSO X φ ih =>
      show (∃ S : Set N.Node, SatisfiesAt N φ ((ρ.mapEquiv _).updateSO X S)) ↔
        (∃ S : Set M.Node, SatisfiesAt M φ (ρ.updateSO X S))
      constructor
      · rintro ⟨S, hS⟩
        refine ⟨iso.toEquiv ⁻¹' S, (ih _).mp ?_⟩
        rw [Assignment.mapEquiv_updateSO,
          Set.image_preimage_eq S iso.toEquiv.surjective]
        exact hS
      · rintro ⟨S, hS⟩
        refine ⟨iso.toEquiv '' S, ?_⟩
        rw [← Assignment.mapEquiv_updateSO]
        exact (ih _).mpr hS
  | forallSO X φ ih =>
      show (∀ S : Set N.Node, SatisfiesAt N φ ((ρ.mapEquiv _).updateSO X S)) ↔
        (∀ S : Set M.Node, SatisfiesAt M φ (ρ.updateSO X S))
      constructor
      · intro h S
        refine (ih _).mp ?_
        rw [Assignment.mapEquiv_updateSO]
        exact h (iso.toEquiv '' S)
      · intro h S
        have := (ih (ρ.updateSO X (iso.toEquiv ⁻¹' S))).mpr
          (h (iso.toEquiv ⁻¹' S))
        rwa [Assignment.mapEquiv_updateSO,
          Set.image_preimage_eq S iso.toEquiv.surjective] at this

/-- Sentence-level transfer: a formula is satisfied from the empty
assignment in isomorphic models simultaneously. -/
theorem satisfies_iff_of_iso (iso : M.Iso N) (φ : Formula A) :
    Satisfies N φ ↔ Satisfies M φ := by
  have hempty : (Assignment.empty M).mapEquiv iso.toEquiv =
      Assignment.empty N := by
    refine Assignment.ext rfl ?_
    funext X
    show iso.toEquiv '' ∅ = ∅
    simp
  rw [Satisfies, Satisfies, ← hempty]
  exact satisfiesAt_mapEquiv_iff iso φ (Assignment.empty M)

end Semantics

end GraphMSO.TreeLanguage
