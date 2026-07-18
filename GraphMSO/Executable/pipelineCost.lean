import GraphMSO.Executable.cost
import GraphMSO.Executable.incidence

/-!
# Abstract cost of the complete executable MSO₂ pipeline

`checkMSO2ExecCosted` extends the abstract `Costed` model of
`GraphMSO/Executable/cost.lean` from the core pass to the whole
`checkMSO2Exec` pipeline: vertex enumeration, dart enumeration, the
incidence extension, nice normalization, the greedy bag coloring, and the
core encode/run pass are all charged in one combined counter, and the total
is bounded by a closed form in the input parameters.

Charging policy, extending the conventions of the core cost file:

- vertex enumeration charges one operation per rose-tree node;
- dart enumeration charges one operation per examined ordered vertex pair;
- the incidence walk charges, at every node, one operation plus one per
  pending dart examined there (`DecompTree.incidenceWalkCost`);
- normalization charges one operation per constructed nice-tree node, i.e.
  exactly the output size;
- the greedy coloring charges one operation per node plus one per distinct
  bag member (`DecompTree.greedyWalkCost`), treating one `assignVertex` step
  as a fixed-width primitive exactly as `encodeLetter` is treated in the
  core model;
- the core pass is `checkCodeCosted`, contributing its established
  `3 * n + 2`.

As in the core file, formula translation and compilation remain deliberately
uncharged, and nothing here is a claim about Lean kernel or VM time.
-/

universe u

/-- The two node-count measures on constructor-coded nice trees agree. -/
theorem InductiveNiceTree.nodeCount_eq_size {W : Type u} {bag : Set W}
    (tree : InductiveNiceTree W bag) : tree.nodeCount = tree.size := by
  induction tree with
  | leaf => rfl
  | introduce v child fresh ih =>
      simp [InductiveNiceTree.nodeCount, InductiveNiceTree.size, ih]
  | forget v child present ih =>
      simp [InductiveNiceTree.nodeCount, InductiveNiceTree.size, ih]
  | join left right ihl ihr =>
      simp [InductiveNiceTree.nodeCount, InductiveNiceTree.size, ihl, ihr]

namespace DecompTree

variable {V : Type u} [DecidableEq V]

/-! ## Cost of the greedy coloring walk -/

/-- Abstract cost of the greedy coloring walk: one operation per node plus
one per distinct bag member. -/
def greedyWalkCost : DecompTree V → ℕ
  | node bag children =>
      bag.dedup.length + 1 +
        (children.attach.map fun c => greedyWalkCost c.1).sum
decreasing_by
  have := List.sizeOf_lt_of_mem c.2
  simp
  omega

theorem greedyWalkCost_node (bag : List V) (children : List (DecompTree V)) :
    (node bag children).greedyWalkCost =
      bag.dedup.length + 1 + (children.map greedyWalkCost).sum := by
  simp only [greedyWalkCost]
  congr 2
  exact List.attach_map_val (l := children) (f := greedyWalkCost)

/-- On a width-`omega` rose tree the greedy walk is linear in the node
count. -/
theorem greedyWalkCost_le (t : DecompTree V) (omega : ℕ) :
    t.HasWidth omega → t.greedyWalkCost ≤ (omega + 2) * t.size := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      intro hw
      rw [greedyWalkCost_node, size_node]
      have hbag : bag.dedup.length ≤ omega + 1 := by
        rw [List.dedup_length_eq_card_toFinset]
        exact hw.rootBag_card
      have hsum : (children.map greedyWalkCost).sum ≤
          (omega + 2) * (children.map size).sum := by
        have h1 : (children.map greedyWalkCost).sum ≤
            (children.map fun c => (omega + 2) * c.size).sum :=
          List.sum_le_sum (fun c hc => ih c hc (hw.of_mem_children hc))
        rw [List.sum_map_mul_left] at h1
        exact h1
      have hexpand : (omega + 2) * (1 + (children.map size).sum) =
          (omega + 2) + (omega + 2) * (children.map size).sum := by
        rw [Nat.mul_add, Nat.mul_one]
      omega

/-! ## Cost of the incidence walk -/

variable (G : SimpleGraph V)

mutual

/-- Abstract cost of the incidence walk: one operation per node plus one per
pending dart examined there. -/
def incidenceWalkCost : DecompTree V → List G.Dart → ℕ
  | node bag children, pending =>
      pending.length + 1 +
        incidenceForestCost children (pending.filter fun d => !dartMem G bag d)

/-- Forest version of `incidenceWalkCost`, threading the pending darts. -/
def incidenceForestCost : List (DecompTree V) → List G.Dart → ℕ
  | [], _ => 0
  | c :: cs, pending =>
      incidenceWalkCost c pending +
        incidenceForestCost cs (incidenceAux G c pending).2

end

theorem incidenceWalkCost_node (bag : List V)
    (children : List (DecompTree V)) (pending : List G.Dart) :
    incidenceWalkCost G (node bag children) pending =
      pending.length + 1 +
        incidenceForestCost G children
          (pending.filter fun d => !dartMem G bag d) := by
  unfold incidenceWalkCost
  rfl

theorem incidenceForestCost_nil (pending : List G.Dart) :
    incidenceForestCost G [] pending = 0 := by
  unfold incidenceForestCost
  rfl

theorem incidenceForestCost_cons (c : DecompTree V)
    (cs : List (DecompTree V)) (pending : List G.Dart) :
    incidenceForestCost G (c :: cs) pending =
      incidenceWalkCost G c pending +
        incidenceForestCost G cs (incidenceAux G c pending).2 := by
  cases cs with
  | nil =>
      unfold incidenceForestCost
      rfl
  | cons c₂ cs₂ =>
      unfold incidenceForestCost
      rfl

theorem incidenceForestCost_le (cs : List (DecompTree V)) :
    (∀ c ∈ cs, ∀ p : List G.Dart,
      incidenceWalkCost G c p ≤ c.size * (p.length + 1)) →
      ∀ p : List G.Dart,
        incidenceForestCost G cs p ≤
          (cs.map DecompTree.size).sum * (p.length + 1) := by
  induction cs with
  | nil =>
      intro _ p
      simp [incidenceForestCost_nil]
  | cons c cs ih =>
      intro hspec p
      rw [incidenceForestCost_cons]
      have h1 := hspec c (by simp) p
      have h2 := ih (fun c₂ hc₂ => hspec c₂ (by simp [hc₂]))
        (incidenceAux G c p).2
      have hlen : (incidenceAux G c p).2.length ≤ p.length :=
        (incidenceAux_sublist G c p).length_le
      have h3 : (cs.map DecompTree.size).sum *
            ((incidenceAux G c p).2.length + 1) ≤
          (cs.map DecompTree.size).sum * (p.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hexpand : (c.size + (cs.map DecompTree.size).sum) *
            (p.length + 1) =
          c.size * (p.length + 1) +
            (cs.map DecompTree.size).sum * (p.length + 1) := by
        rw [Nat.add_mul]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The incidence walk touches each pending dart at most once per node. -/
theorem incidenceWalkCost_le (t : DecompTree V) :
    ∀ p : List G.Dart, incidenceWalkCost G t p ≤ t.size * (p.length + 1) := by
  induction t using DecompTree.induction_on with
  | h bag children ih =>
      intro p
      rw [incidenceWalkCost_node]
      have hf := incidenceForestCost_le G children ih
        (p.filter fun d => !dartMem G bag d)
      have hlen : (p.filter fun d => !dartMem G bag d).length ≤ p.length :=
        List.length_filter_le _ _
      have h3 : (children.map DecompTree.size).sum *
            ((p.filter fun d => !dartMem G bag d).length + 1) ≤
          (children.map DecompTree.size).sum * (p.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hexpand : (1 + (children.map DecompTree.size).sum) *
            (p.length + 1) =
          (p.length + 1) +
            (children.map DecompTree.size).sum * (p.length + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [size_node]
      omega

end DecompTree

namespace GraphMSO.Executable

variable {V : Type} [DecidableEq V]

/-- The costed complete pipeline: every stage of `checkMSO2Exec` is charged
under the policy documented in the module header. -/
def checkMSO2ExecCosted (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : DecompTree V) (omega : ℕ) (phi : Formula) : Costed Bool :=
  (Costed.charge t.size t.vertexList).bind fun vs =>
    (Costed.charge (DecompTree.offDiagPairs vs.dedup).length
        (DecompTree.dartsOfList G vs)).bind fun darts =>
      (Costed.charge (DecompTree.incidenceWalkCost G t darts)
          (DecompTree.incidenceAux G t darts).1).bind fun tI =>
        (Costed.charge tI.normalizeCode.size tI.normalizeCode).bind fun code =>
          (Costed.charge tI.greedyWalkCost
              (tI.greedyColoring (max omega 2))).bind fun color =>
            checkCodeCosted (omega := max omega 2) (incidenceTauGraphExec G)
              code color phi.toIncidence

@[simp] theorem checkMSO2ExecCosted_value (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : DecompTree V) (omega : ℕ) (phi : Formula) :
    (checkMSO2ExecCosted G t omega phi).value = checkMSO2Exec G t omega phi := by
  simp [checkMSO2ExecCosted, checkMSO2Exec, DecompTree.incidenceTree]

/-- Exact combined cost: the five stage charges plus the core pass. -/
theorem checkMSO2ExecCosted_cost (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : DecompTree V) (omega : ℕ) (phi : Formula) :
    (checkMSO2ExecCosted G t omega phi).cost =
      t.size + (DecompTree.offDiagPairs t.vertexList.dedup).length +
        DecompTree.incidenceWalkCost G t (DecompTree.dartsOfList G t.vertexList) +
        (DecompTree.incidenceTree G t).normalizeCode.size +
        (DecompTree.incidenceTree G t).greedyWalkCost +
        (3 * (DecompTree.incidenceTree G t).normalizeCode.size + 2) := by
  simp [checkMSO2ExecCosted, DecompTree.incidenceTree,
    InductiveNiceTree.nodeCount_eq_size]
  omega

/-- Combined abstract cost bound for the complete pipeline, in the input
parameters: the rose-tree size `n = t.size`, the number `q` of examined
vertex pairs, the number `m` of enumerated darts, and the width `omega`. -/
theorem checkMSO2ExecCosted_cost_le (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : DecompTree V) (omega : ℕ) (phi : Formula)
    (hw : t.HasWidth omega) :
    (checkMSO2ExecCosted G t omega phi).cost ≤
      t.size + (DecompTree.offDiagPairs t.vertexList.dedup).length +
        t.size * ((DecompTree.dartsOfList G t.vertexList).length + 1) +
        (4 * (3 * max omega 2 + 5) + (max omega 2 + 2)) *
          (t.size + (DecompTree.dartsOfList G t.vertexList).length) + 2 := by
  rw [checkMSO2ExecCosted_cost]
  have hwI := DecompTree.incidenceTree_hasWidth G t omega hw
  have hsizeI : (DecompTree.incidenceTree G t).size ≤
      t.size + (DecompTree.dartsOfList G t.vertexList).length :=
    DecompTree.incidenceTree_size_le G t
  have hwalk := DecompTree.incidenceWalkCost_le G t
    (DecompTree.dartsOfList G t.vertexList)
  have hnorm : (DecompTree.incidenceTree G t).normalizeCode.size ≤
      (3 * max omega 2 + 5) *
        (t.size + (DecompTree.dartsOfList G t.vertexList).length) :=
    (DecompTree.normalizeCode_size_le _ _ hwI).trans
      (Nat.mul_le_mul_left _ hsizeI)
  have hgreedy : (DecompTree.incidenceTree G t).greedyWalkCost ≤
      (max omega 2 + 2) *
        (t.size + (DecompTree.dartsOfList G t.vertexList).length) :=
    (DecompTree.greedyWalkCost_le _ _ hwI).trans
      (Nat.mul_le_mul_left _ hsizeI)
  have hexpand : (4 * (3 * max omega 2 + 5) + (max omega 2 + 2)) *
        (t.size + (DecompTree.dartsOfList G t.vertexList).length) =
      (3 * max omega 2 + 5) *
          (t.size + (DecompTree.dartsOfList G t.vertexList).length) +
        (max omega 2 + 2) *
          (t.size + (DecompTree.dartsOfList G t.vertexList).length) +
        3 * ((3 * max omega 2 + 5) *
          (t.size + (DecompTree.dartsOfList G t.vertexList).length)) := by
    ring
  omega

/-- Semantic correctness of the costed pipeline on closed MSO₂ sentences. -/
theorem checkMSO2ExecCosted_value_eq_true_iff [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : DecompTree V) (omega : ℕ)
    (hvalid : t.IsDecompFor G) (hw : t.HasWidth omega)
    (phi : Formula) (hclosed : phi.Closed) :
    (checkMSO2ExecCosted G t omega phi).value = true ↔
      Semantics.Satisfies G phi := by
  rw [checkMSO2ExecCosted_value,
    checkMSO2Exec_eq_true_iff G t omega hvalid hw phi hclosed]

end GraphMSO.Executable
