import GraphMSO.Decomp.execDecomp
import GraphMSO.Decomp.normalization

/-!
# Executable nice-decomposition normalization

`DecompTree.normalizeCode` is the computable counterpart of
`RootedTreeDecomposition.normalizeCode`: it turns a rose-tree presentation of
a tree-decomposition into a constructor-coded nice tree by structural
recursion, connecting every child branch to its parent bag with a one-vertex
introduce/forget path and combining equal-bag branches with binary joins.

The correctness theorems mirror the proof-facing normalization: width bounds,
bag survival, occurrence equivalence, and occurrence connectedness, and they
assemble into `DecompTree.normalize`, a certified
`InductiveNiceTreeDecomposition` for any valid input.
-/

universe u

namespace DecompTree

variable {V : Type u} [DecidableEq V]

/-- Normalize the subtree of a rose-tree decomposition into constructor-coded
nice form.  Computable counterpart of
`RootedTreeDecomposition.normalizeCodeAt`. -/
def normalizeAux : (t : DecompTree V) → InductiveNiceTree V (t.rootBag.toFinset : Set V)
  | node bag [] => InductiveNiceTree.closeToLeafOfList bag
  | node bag (c :: cs) =>
      InductiveNiceTree.joinNonempty
        (InductiveNiceTree.changeRootOfList bag c.rootBag (normalizeAux c))
        (cs.attach.map fun s =>
          InductiveNiceTree.changeRootOfList bag s.1.rootBag (normalizeAux s.1))
decreasing_by
  all_goals simp
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem s.2; omega)

@[simp] theorem normalizeAux_nil (bag : List V) :
    normalizeAux (node bag ([] : List (DecompTree V))) =
      InductiveNiceTree.closeToLeafOfList bag := by
  simp only [normalizeAux]

theorem normalizeAux_cons (bag : List V) (c : DecompTree V)
    (cs : List (DecompTree V)) :
    normalizeAux (node bag (c :: cs)) =
      InductiveNiceTree.joinNonempty
        (InductiveNiceTree.changeRootOfList bag c.rootBag (normalizeAux c))
        (cs.map fun s =>
          InductiveNiceTree.changeRootOfList bag s.rootBag (normalizeAux s)) := by
  simp only [normalizeAux]
  congr 1
  exact List.attach_map_val (l := cs) (f := fun s =>
    InductiveNiceTree.changeRootOfList bag s.rootBag (normalizeAux s))

/-- A vertex occurs in the normalized code exactly when it occurs in the
input rose tree. -/
theorem normalizeAux_occurs_iff (t : DecompTree V) (v : V) :
    (normalizeAux t).Occurs v ↔ t.Occurs v := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      cases children with
      | nil =>
          rw [normalizeAux_nil, InductiveNiceTree.closeToLeafOfList_occurs_iff,
            occurs_node_iff]
          simp
      | cons c cs =>
          rw [normalizeAux_cons, InductiveNiceTree.joinNonempty_occurs_iff,
            occurs_node_iff]
          have hbranch : ∀ s ∈ c :: cs,
              ((InductiveNiceTree.changeRootOfList bag s.rootBag
                (normalizeAux s)).Occurs v ↔
                s.Occurs v ∨ (v ∈ bag ∧ v ∉ s.rootBag)) := by
            intro s hs
            rw [InductiveNiceTree.changeRootOfList_occurs_iff, ih s hs]
          constructor
          · rintro (h | ⟨next, hnext, hocc⟩)
            · rcases (hbranch c (by simp)).1 h with h | ⟨hv, _⟩
              · exact Or.inr ⟨c, by simp, h⟩
              · exact Or.inl hv
            · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hnext
              rcases (hbranch s (by simp [hs])).1 hocc with h | ⟨hv, _⟩
              · exact Or.inr ⟨s, by simp [hs], h⟩
              · exact Or.inl hv
          · rintro (hv | ⟨s, hs, hocc⟩)
            · by_cases hc : v ∈ c.rootBag
              · exact Or.inl
                  ((hbranch c (by simp)).2 (Or.inl (occurs_of_mem_rootBag hc)))
              · exact Or.inl ((hbranch c (by simp)).2 (Or.inr ⟨hv, hc⟩))
            · rcases List.mem_cons.mp hs with rfl | hs'
              · exact Or.inl ((hbranch s (by simp)).2 (Or.inl hocc))
              · refine Or.inr ⟨_, List.mem_map_of_mem hs', ?_⟩
                exact (hbranch s (by simp [hs'])).2 (Or.inl hocc)

/-- Normalization preserves the width bound of the input rose tree. -/
theorem normalizeAux_hasWidth [Finite V] (t : DecompTree V) (omega : ℕ) :
    t.HasWidth omega → (normalizeAux t).HasWidth omega := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      intro h
      cases children with
      | nil =>
          rw [normalizeAux_nil]
          exact InductiveNiceTree.closeToLeafOfList_hasWidth bag omega
            (by simpa using h.rootBag_card)
      | cons c cs =>
          rw [normalizeAux_cons]
          have hbranch : ∀ s ∈ c :: cs,
              (InductiveNiceTree.changeRootOfList bag s.rootBag
                (normalizeAux s)).HasWidth omega := by
            intro s hs
            exact InductiveNiceTree.changeRootOfList_hasWidth _ _ _ omega
              (ih s hs (h.of_mem_children hs))
              (by simpa using h.rootBag_card)
              (h.of_mem_children hs).rootBag_card
          apply InductiveNiceTree.joinNonempty_hasWidth
          · exact hbranch c (by simp)
          · intro next hnext
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hnext
            exact hbranch s (by simp [hs])

/-- Every bag of the input rose tree occurs in the normalized code. -/
theorem normalizeAux_hasBag (t : DecompTree V) {L : List V} :
    t.HasBag L → (normalizeAux t).HasBag (L.toFinset : Set V) := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      intro hL
      cases children with
      | nil =>
          rw [normalizeAux_nil]
          rcases hasBag_node_iff.1 hL with rfl | ⟨c, hc, _⟩
          · exact InductiveNiceTree.hasBag_root _
          · simp at hc
      | cons c cs =>
          rw [normalizeAux_cons]
          rcases hasBag_node_iff.1 hL with rfl | ⟨s, hs, hsL⟩
          · exact InductiveNiceTree.hasBag_root _
          · have hchild := InductiveNiceTree.changeRootOfList_hasBag bag
              s.rootBag (normalizeAux s) _ (ih s hs hsL)
            rcases List.mem_cons.mp hs with rfl | hs'
            · exact InductiveNiceTree.joinNonempty_hasBag_head _ _ hchild
            · exact InductiveNiceTree.joinNonempty_hasBag_of_mem _ _
                (List.mem_map_of_mem hs') hchild

/-- Normalization preserves the running-intersection property: the code
positions containing a fixed graph vertex form a connected subtree. -/
theorem normalizeAux_occPreconnected (t : DecompTree V) :
    t.RunningIntersection → ∀ v, (normalizeAux t).OccPreconnected v := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      rintro ⟨hdown, hpair, hchildren⟩ v
      cases children with
      | nil =>
          rw [normalizeAux_nil]
          exact InductiveNiceTree.closeToLeafOfList_occPreconnected bag v
      | cons c cs =>
          rw [normalizeAux_cons]
          have hbranchConn : ∀ s ∈ c :: cs,
              (InductiveNiceTree.changeRootOfList bag s.rootBag
                (normalizeAux s)).OccPreconnected v := by
            intro s hs
            apply InductiveNiceTree.changeRootOfList_occPreconnected
            · exact ih s hs (hchildren s hs) v
            · intro x hxbag hxnot hocc
              exact hxnot
                (hdown s hs x hxbag ((normalizeAux_occurs_iff s x).1 hocc))
          have hbranchPair :
              ((c :: cs).map fun s => InductiveNiceTree.changeRootOfList bag
                s.rootBag (normalizeAux s)).Pairwise
                (fun l r => l.Occurs v → r.Occurs v →
                  v ∈ (bag.toFinset : Set V)) := by
            apply hpair.map
            intro s₁ s₂ hs₁₂ hl hr
            rcases (InductiveNiceTree.changeRootOfList_occurs_iff _ _ _ v).1 hl
              with hocc₁ | ⟨hv, _⟩
            case inr => simpa using hv
            rcases (InductiveNiceTree.changeRootOfList_occurs_iff _ _ _ v).1 hr
              with hocc₂ | ⟨hv, _⟩
            case inr => simpa using hv
            have hmem := hs₁₂ v ((normalizeAux_occurs_iff s₁ v).1 hocc₁)
              ((normalizeAux_occurs_iff s₂ v).1 hocc₂)
            simpa using hmem
          rw [List.map_cons] at hbranchPair
          exact InductiveNiceTree.joinNonempty_occPreconnected _ _ v
            (hbranchConn c (by simp))
            (fun next hnext => by
              obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hnext
              exact hbranchConn s (by simp [hs]))
            hbranchPair

/-- Normalization preserves bag-injective colorings: a coloring injective on
every input bag is injective on every generated code bag. -/
theorem normalizeAux_isBagColoring (t : DecompTree V) {k : ℕ}
    {color : V → Fin k} :
    t.IsBagColoring color → (normalizeAux t).IsBagColoring color := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      intro h
      cases children with
      | nil =>
          rw [normalizeAux_nil]
          exact InductiveNiceTree.closeToLeafOfList_isBagColoring bag
            (h (HasBag.root _ _))
      | cons c cs =>
          rw [normalizeAux_cons]
          have hbranch : ∀ s ∈ c :: cs,
              (InductiveNiceTree.changeRootOfList bag s.rootBag
                (normalizeAux s)).IsBagColoring color := by
            intro s hs
            exact InductiveNiceTree.changeRootOfList_isBagColoring _ _ _
              (ih s hs (h.of_mem_children hs)) (h (HasBag.root _ _))
          apply InductiveNiceTree.joinNonempty_isBagColoring
          · exact hbranch c (by simp)
          · intro next hnext
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hnext
            exact hbranch s (by simp [hs])

/-- The complete computable normalization: an empty root path is attached
above the normalized rose tree.  Computable counterpart of
`RootedTreeDecomposition.normalizeCode`. -/
def normalizeCode (t : DecompTree V) : InductiveNiceTree V ∅ :=
  InductiveNiceTree.castRoot (by simp)
    (InductiveNiceTree.changeRootOfList [] t.rootBag (normalizeAux t))

theorem normalizeCode_occurs_iff (t : DecompTree V) (v : V) :
    t.normalizeCode.Occurs v ↔ t.Occurs v := by
  unfold normalizeCode
  rw [InductiveNiceTree.occurs_castRoot_iff,
    InductiveNiceTree.changeRootOfList_occurs_iff, normalizeAux_occurs_iff]
  simp

/-- Complete normalization, including the empty root path, preserves
width. -/
theorem normalizeCode_hasWidth [Finite V] (t : DecompTree V) (omega : ℕ)
    (h : t.HasWidth omega) : t.normalizeCode.HasWidth omega := by
  unfold normalizeCode
  apply (InductiveNiceTree.hasWidth_castRoot_iff _ _ _).2
  exact InductiveNiceTree.changeRootOfList_hasWidth _ _ _ omega
    (normalizeAux_hasWidth t omega h) (by simp) h.rootBag_card

/-- Every bag of the input rose tree survives in the complete normalized
code. -/
theorem normalizeCode_hasBag (t : DecompTree V) {L : List V}
    (h : t.HasBag L) : t.normalizeCode.HasBag (L.toFinset : Set V) := by
  unfold normalizeCode
  exact (InductiveNiceTree.hasBag_castRoot_iff _ _).2
    (InductiveNiceTree.changeRootOfList_hasBag _ _ _ _
      (normalizeAux_hasBag t h))

/-- A coloring injective on every input bag is a bag coloring of the complete
normalized code. -/
theorem normalizeCode_isBagColoring (t : DecompTree V) {k : ℕ}
    {color : V → Fin k} (h : t.IsBagColoring color) :
    t.normalizeCode.IsBagColoring color := by
  unfold normalizeCode
  apply (InductiveNiceTree.isBagColoring_castRoot_iff _ _ _).2
  apply InductiveNiceTree.changeRootOfList_isBagColoring _ _ _
    (normalizeAux_isBagColoring t h)
  simp

theorem normalizeCode_occPreconnected (t : DecompTree V)
    (hri : t.RunningIntersection) (v : V) :
    t.normalizeCode.OccPreconnected v := by
  unfold normalizeCode
  apply (InductiveNiceTree.occPreconnected_castRoot_iff _ _ v).2
  apply InductiveNiceTree.changeRootOfList_occPreconnected _ _ _ v
    (normalizeAux_occPreconnected t hri v)
  intro x hx
  simp at hx

section

variable [Fintype V] {G : SimpleGraph V}

/-- The certified inductive nice decomposition obtained by normalizing a
valid rose-tree decomposition of `G`.  The underlying code is the computable
`normalizeCode`; only the certificate layer is noncomputable. -/
noncomputable def normalize (t : DecompTree V) (h : t.IsDecompFor G) :
    InductiveNiceTreeDecomposition (G := G) := by
  apply t.normalizeCode.toInductiveNiceTreeDecomposition
  · intro v
    exact (normalizeCode_occurs_iff t v).2 (h.vertexCoverage v)
  · intro u v huv
    obtain ⟨L, hL, hu, hv⟩ := h.edgeCoverage huv
    obtain ⟨n, hn⟩ := normalizeCode_hasBag t hL
    exact ⟨n, by rw [hn]; simpa using hu, by rw [hn]; simpa using hv⟩
  · intro v
    exact normalizeCode_occPreconnected t h.runningIntersection v

@[simp] theorem normalize_tree (t : DecompTree V) (h : t.IsDecompFor G) :
    (t.normalize h).tree = t.normalizeCode :=
  rfl

/-- The certified normalization preserves any width bound of the input rose
tree. -/
theorem normalize_hasWidth (t : DecompTree V) (h : t.IsDecompFor G)
    (omega : ℕ) (hw : t.HasWidth omega) :
    (t.normalize h).toTreeDecomposition.HasWidth omega := by
  rw [(t.normalize h).hasWidth_iff]
  simpa using normalizeCode_hasWidth t omega hw

end

end DecompTree
