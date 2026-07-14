import GraphMSO.Executable.modelCheck

/-!
# Executable Phase 7 smoke tests

These examples exercise both the tree-formula compiler and the full
nice-decomposition model-checking pipeline.  The graph examples use width zero,
so every color has type `Fin 1`.
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

end GraphMSO.Executable.Examples
