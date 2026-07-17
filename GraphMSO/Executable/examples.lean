import GraphMSO.Executable.modelCheck
import GraphMSO.Executable.incidence
import GraphMSO.Decomp.execColoring

/-!
# Executable Phase 7 smoke tests

These examples exercise both the tree-formula compiler and the full
nice-decomposition model-checking pipeline.  The graph examples use width zero,
so every color has type `Fin 1`.  The final section drives rose-tree
decompositions through the computable normalizer `DecompTree.normalizeCode`.
-/

namespace GraphMSO.Executable.Examples

/-! ## Direct tree-formula checks -/

/-- A closed tree formula saying that some node has Boolean label `true`. -/
def hasTrueLabel : ExecFormula Bool :=
  .existsFO 0 (.labelMem (fun label => label) 0)

def trueLabelTree : BinTree Bool :=
  .node true .nil .nil

def falseLabelTree : BinTree Bool :=
  .node false .nil .nil

#guard checkTree hasTrueLabel trueLabelTree

#guard !(checkTree hasTrueLabel falseLabelTree)

/-! ## Full checker on the empty graph -/

def emptyGraph : TauPGraph Unit Empty where
  adj _ _ := false
  pred _ _ := false
  adj_symm _ _ := rfl
  adj_loopless _ := rfl

def emptyCode : InductiveNiceTree Empty ∅ :=
  .leaf

def emptyColor : Empty → Fin 1 :=
  fun vertex => nomatch vertex

def graphTruth : Language.Formula Unit :=
  Language.Formula.true_

def graphFalse : Language.Formula Unit :=
  .false_

#guard checkCode (omega := 0) emptyGraph emptyCode emptyColor graphTruth

#guard !(checkCode (omega := 0) emptyGraph emptyCode emptyColor graphFalse)

/-! ## A one-vertex constructor-coded nice tree -/

def oneVertexGraph : TauPGraph Unit (Fin 1) where
  adj _ _ := false
  pred _ _ := false
  adj_symm _ _ := rfl
  adj_loopless _ := rfl

/-- The introduce node has the singleton bag `{0}`. -/
def oneVertexIntroduced :
    InductiveNiceTree (Fin 1) ({0} : Set (Fin 1)) := by
  simpa using
    (InductiveNiceTree.introduce 0
      (InductiveNiceTree.leaf : InductiveNiceTree (Fin 1) ∅) (by simp))

/-- Forgetting the only vertex makes the root bag empty again. -/
def oneVertexCode : InductiveNiceTree (Fin 1) ∅ := by
  simpa using (InductiveNiceTree.forget 0 oneVertexIntroduced (by simp))

def oneVertexColor : Fin 1 → Fin 1 :=
  fun _ => 0

/-- The closed graph-MSO sentence `∃ x, x = x`. -/
def graphHasVertex : Language.Formula Unit :=
  .existsFO 0 (.equal 0 0)

/-- The closed graph-MSO sentence `∀ x, false`. -/
def graphHasNoVertex : Language.Formula Unit :=
  .forallFO 0 .false_

/- The following end-to-end checks are useful manual stress tests.  Unlike the
empty-graph smoke tests above, the translated vertex-recognition guard has
several nested quantifiers, so they are not run automatically on every build.

Expected outputs are respectively `true` and `false`:

```
#eval checkCode (omega := 0) oneVertexGraph oneVertexCode oneVertexColor graphHasVertex
#eval checkCode (omega := 0) oneVertexGraph oneVertexCode oneVertexColor graphHasNoVertex
```
-/

/-! ## Rose-tree decomposition normalization

`DecompTree.normalizeCode` is the computable normalizer from rose-tree
decompositions to constructor-coded nice trees.  The size guards pin down the
generated introduce/forget chains, and the checker guards run the verified
model checker on a generated code instead of a hand-written one. -/

/-- The one-bag rose-tree decomposition of the empty graph. -/
def emptyDecompTree : DecompTree Empty :=
  .node [] []

#guard emptyDecompTree.normalizeCode.size == 1

#guard checkCode (omega := 0) emptyGraph emptyDecompTree.normalizeCode emptyColor
  graphTruth

#guard !(checkCode (omega := 0) emptyGraph emptyDecompTree.normalizeCode emptyColor
  graphFalse)

/-- `K₂` presented as a single-bag rose tree. -/
def k2Tree : DecompTree (Fin 2) :=
  .node [0, 1] []

/-- A two-bag path decomposition of the path `0 — 1 — 2`. -/
def pathTree : DecompTree (Fin 3) :=
  .node [0, 1] [.node [1, 2] []]

#guard k2Tree.normalizeCode.size == 5

#guard pathTree.normalizeCode.size == 7

/-- The single-bag rose tree is a valid decomposition of `K₂`, so
`DecompTree.normalize` certifies its normalized code. -/
example : k2Tree.IsDecompFor (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    refine ⟨[0, 1], DecompTree.HasBag.root _ _, ?_⟩
    fin_cases v <;> decide
  · intro u v _huv
    refine ⟨[0, 1], DecompTree.HasBag.root _ _, ?_, ?_⟩
    · fin_cases u <;> decide
    · fin_cases v <;> decide
  · exact .node (fun c hc => by simp at hc) List.Pairwise.nil
      (fun c hc => by simp at hc)

example : k2Tree.HasWidth 1 := by
  intro L hL
  rcases DecompTree.hasBag_node_iff.1 hL with rfl | ⟨c, hc, _⟩
  · decide
  · simp at hc

/-! ## Fully computable end-to-end MSO₂ checking

`checkMSO2Exec` composes the executable incidence extension, nice
normalization, and greedy coloring with the verified checker.  The guards
exercise the incidence construction and its coloring; running the full
checker compiles the width-2 incidence automaton, so complete runs are kept
as manual stress tests. -/

/-- `K₂` with decidable adjacency. -/
def k2Graph : SimpleGraph (Fin 2) where
  Adj u v := u ≠ v
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

instance : DecidableRel k2Graph.Adj :=
  fun u v => inferInstanceAs (Decidable ¬(u = v))

#guard (DecompTree.incidenceTree k2Graph k2Tree).normalizeCode.size == 7

#guard ((DecompTree.incidenceTree k2Graph k2Tree).greedyColoring 2)
  (.fromV 1) == 1

/- Expected outputs are respectively `true` and `false` (manual stress
tests; the width-2 incidence alphabet makes the compiled automaton large):

```
#eval checkMSO2Exec k2Graph k2Tree 1 (.neg .false_)
#eval checkMSO2Exec k2Graph k2Tree 1 .false_
```
-/

/-! ## Greedy bag coloring

`DecompTree.greedyColoring` computes width-sized bag-injective colorings; the
guard pins down the colors on the two-bag path decomposition, and the example
certifies the coloring for the normalized `K₂` code, which is exactly the
hypothesis shape consumed by `checkColored_eq_true_iff`. -/

#guard (List.finRange 3).map (pathTree.greedyColoring 1) == [0, 1, 0]

/-- The greedy coloring certifies the normalized `K₂` code. -/
example : k2Tree.normalizeCode.IsBagColoring (k2Tree.greedyColoring 1) := by
  apply DecompTree.normalizeCode_greedyColoring_isBagColoring
  · intro L hL
    rcases DecompTree.hasBag_node_iff.1 hL with rfl | ⟨c, hc, _⟩
    · decide
    · simp at hc
  · exact .node (fun c hc => by simp at hc) List.Pairwise.nil
      (fun c hc => by simp at hc)

end GraphMSO.Executable.Examples
