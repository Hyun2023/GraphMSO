import GraphMSO.Automata.cost
import GraphMSO.Executable.modelCheck
import Mathlib.Tactic

/-!
# Abstract costs for executable tree automata

This file refines the executable bottom-up evaluator to the abstract `Costed`
model.  One unit is charged whenever `ExecTreeAutomaton.run` visits a
`BinTree` constructor, including an absent child, and one further unit is
charged for the final Boolean accepting-state test.

These counters describe only the online encoding and tree traversal.  At an
encoding node, constructing its label with `encodeLetter` (including its bag
searches) and constructing the corresponding binary-tree node are treated as
one fixed-width primitive.  Likewise, an automaton transition (including any
`Finset` work inside a projected automaton) is treated as one primitive.  The
cost of translating and compiling a formula, constructing the dummy-track
relabeling, and Lean kernel or VM reduction steps is not included.  Thus the
results below are fixed-parameter abstract cost statements, not claims that
the complete Lean evaluator runs in this many VM steps.
-/

universe u v

namespace BinTree

variable {A : Type u} {B : Type v}

/-- Relabeling does not change the number of genuine binary-tree nodes. -/
@[simp] theorem nodeCount_map (f : A -> B) (t : BinTree A) :
    (t.map f).nodeCount = t.nodeCount := by
  induction t with
  | nil => rfl
  | node a left right ihLeft ihRight =>
      simp [nodeCount, ihLeft, ihRight]

end BinTree

namespace ExecTreeAutomaton

variable {A : Type u}

/-- Bottom-up execution, charging once for every visited `BinTree` constructor. -/
def runCosted (M : ExecTreeAutomaton A) : BinTree A -> Costed M.State
  | .nil => Costed.tick M.nil
  | .node a left right =>
      (M.runCosted left).bind fun leftState =>
        (M.runCosted right).bind fun rightState =>
          Costed.tick (M.node a leftState rightState)

@[simp] theorem runCosted_value (M : ExecTreeAutomaton A) (t : BinTree A) :
    (M.runCosted t).value = M.run t := by
  induction t with
  | nil => rfl
  | node a left right ihLeft ihRight =>
      simp [runCosted, ihLeft, ihRight]

/-- A binary tree with `n` genuine nodes has exactly `2 * n + 1` constructors
once its absent children are included. -/
@[simp] theorem runCosted_cost (M : ExecTreeAutomaton A) (t : BinTree A) :
    (M.runCosted t).cost = 2 * t.nodeCount + 1 := by
  induction t with
  | nil => rfl
  | node a left right ihLeft ihRight =>
      simp [runCosted, ihLeft, ihRight, BinTree.nodeCount] <;> omega

/-- Run the executable automaton and charge one final Boolean acceptance test. -/
def acceptsCosted (M : ExecTreeAutomaton A) (t : BinTree A) : Costed Bool :=
  (M.runCosted t).bind fun state => Costed.tick (M.accept state)

@[simp] theorem acceptsCosted_value (M : ExecTreeAutomaton A) (t : BinTree A) :
    (M.acceptsCosted t).value = M.accepts t := by
  simp [acceptsCosted, accepts]

@[simp] theorem acceptsCosted_cost (M : ExecTreeAutomaton A) (t : BinTree A) :
    (M.acceptsCosted t).cost = 2 * t.nodeCount + 2 := by
  simp [acceptsCosted] <;> omega

end ExecTreeAutomaton

namespace GraphMSO.Executable

open GraphMSO.TreeLanguage

variable {A : Type} [Finite A] [DecidableEq A]

/-- The abstract online phase of `checkTree` after compilation and dummy-track
relabeling.  Formula compilation and construction of `addDummyTrack t` are
deliberately uncharged; see the module-level cost-model qualification. -/
def checkTreeCosted (phi : ExecFormula A) (t : BinTree A) : Costed Bool :=
  let track : FOVar -> Fin 1 := fun _ => 0
  (compile phi 1 track track).automaton.acceptsCosted (addDummyTrack t)

@[simp] theorem checkTreeCosted_value (phi : ExecFormula A) (t : BinTree A) :
    (checkTreeCosted phi t).value = checkTree phi t := by
  simp [checkTreeCosted, checkTree]

@[simp] theorem checkTreeCosted_cost (phi : ExecFormula A) (t : BinTree A) :
    (checkTreeCosted phi t).cost = 2 * t.nodeCount + 2 := by
  simp [checkTreeCosted, addDummyTrack] <;> omega

@[simp] theorem checkTreeCosted_value_eq_true_iff
    (phi : ExecFormula A) (t : BinTree A) :
    (checkTreeCosted phi t).value = true <->
      TreeLanguage.Semantics.Satisfies t.toTreeModel phi.toFormula := by
  rw [checkTreeCosted_value, checkTree_eq_true_iff]

/-! ## Direct nice-tree encoding costs -/

variable {P : Type} {V : Type v} {omega : Nat}

/-- Directly encode a constructor-coded nice tree, charging one operation at
each nice-tree node.  The one operation includes both `encodeLetter` and the
construction of the corresponding binary-tree node; see the module-level
qualification of this fixed-parameter cost model. -/
def encodeAuxCosted [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1)) :
    {rootBag : Set V} → (tree : InductiveNiceTree V rootBag) →
      Finset V → Finset V → Costed (BinTree (ExecSigmaLetter P omega))
  | _, .leaf, bag, adhesion =>
      Costed.tick (.node (encodeLetter X color bag adhesion) .nil .nil)
  | _, .introduce v child _, bag, adhesion =>
      (encodeAuxCosted X color child (bag.erase v) (bag.erase v)).bind fun encoded =>
        Costed.tick (.node (encodeLetter X color bag adhesion) encoded .nil)
  | _, .forget v child _, bag, adhesion =>
      (encodeAuxCosted X color child (insert v bag) bag).bind fun encoded =>
        Costed.tick (.node (encodeLetter X color bag adhesion) encoded .nil)
  | _, .join left right, bag, adhesion =>
      (encodeAuxCosted X color left bag bag).bind fun leftEncoded =>
        (encodeAuxCosted X color right bag bag).bind fun rightEncoded =>
          Costed.tick
            (.node (encodeLetter X color bag adhesion) leftEncoded rightEncoded)

@[simp] theorem encodeAuxCosted_value [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    {rootBag : Set V} (tree : InductiveNiceTree V rootBag)
    (bag adhesion : Finset V) :
    (encodeAuxCosted X color tree bag adhesion).value =
      encodeAux X color tree bag adhesion := by
  induction tree generalizing bag adhesion with
  | leaf => rfl
  | introduce v child fresh ih =>
      simp [encodeAuxCosted, encodeAux, ih]
  | forget v child present ih =>
      simp [encodeAuxCosted, encodeAux, ih]
  | join left right ihLeft ihRight =>
      simp [encodeAuxCosted, encodeAux, ihLeft, ihRight]

@[simp] theorem encodeAuxCosted_cost [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    {rootBag : Set V} (tree : InductiveNiceTree V rootBag)
    (bag adhesion : Finset V) :
    (encodeAuxCosted X color tree bag adhesion).cost = tree.nodeCount := by
  induction tree generalizing bag adhesion with
  | leaf => rfl
  | introduce v child fresh ih =>
      simp [encodeAuxCosted, InductiveNiceTree.nodeCount, ih]
  | forget v child present ih =>
      simp [encodeAuxCosted, InductiveNiceTree.nodeCount, ih]
  | join left right ihLeft ihRight =>
      simp [encodeAuxCosted, InductiveNiceTree.nodeCount, ihLeft, ihRight]
      omega

/-- Costed direct encoding of an empty-rooted constructor nice tree. -/
def encodeCosted [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    (tree : InductiveNiceTree V ∅) : Costed (BinTree (ExecSigmaLetter P omega)) :=
  encodeAuxCosted X color tree ∅ ∅

@[simp] theorem encodeCosted_value [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    (tree : InductiveNiceTree V ∅) :
    (encodeCosted X color tree).value = encode X color tree := by
  simp [encodeCosted, encode]

@[simp] theorem encodeCosted_cost [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    (tree : InductiveNiceTree V ∅) :
    (encodeCosted X color tree).cost = tree.nodeCount := by
  simp [encodeCosted]

/-- The direct executable encoding has exactly one binary-tree node for each
constructor node of the input nice tree. -/
@[simp] theorem encodeAux_nodeCount [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    {rootBag : Set V} (tree : InductiveNiceTree V rootBag)
    (bag adhesion : Finset V) :
    (encodeAux X color tree bag adhesion).nodeCount = tree.nodeCount := by
  induction tree generalizing bag adhesion with
  | leaf => rfl
  | introduce v child fresh ih =>
      simp [encodeAux, InductiveNiceTree.nodeCount, ih]
      omega
  | forget v child present ih =>
      simp [encodeAux, InductiveNiceTree.nodeCount, ih]
      omega
  | join left right ihLeft ihRight =>
      simp [encodeAux, InductiveNiceTree.nodeCount, ihLeft, ihRight]
      omega

@[simp] theorem encode_nodeCount [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    (tree : InductiveNiceTree V ∅) :
    (encode X color tree).nodeCount = tree.nodeCount := by
  simp [encode]

/-! ## End-to-end code-checking cost -/

/-- Encode a nice-tree code and run the compiled checker.  Formula translation
and compilation are deliberately uncharged; encoding and the online automaton
pass are both represented in the returned abstract counter. -/
def checkCodeCosted [Fintype P] [DecidableEq P] [DecidableEq V]
    (X : TauPGraph P V) (tree : InductiveNiceTree V ∅)
    (color : V → Fin (omega + 1)) (theta : Language.Formula P) : Costed Bool :=
  (encodeCosted X color tree).bind fun code =>
    checkTreeCosted (legalTranslate omega theta) code

@[simp] theorem checkCodeCosted_value
    [Fintype P] [DecidableEq P] [DecidableEq V]
    (X : TauPGraph P V) (tree : InductiveNiceTree V ∅)
    (color : V → Fin (omega + 1)) (theta : Language.Formula P) :
    (checkCodeCosted X tree color theta).value = checkCode X tree color theta := by
  simp [checkCodeCosted, checkCode]

/-- With `n` constructor nodes, direct encoding costs `n`, bottom-up traversal
including absent children costs `2 * n + 1`, and the final Boolean test costs
one.  Hence the complete online cost is `3 * n + 2`. -/
@[simp] theorem checkCodeCosted_cost
    [Fintype P] [DecidableEq P] [DecidableEq V]
    (X : TauPGraph P V) (tree : InductiveNiceTree V ∅)
    (color : V → Fin (omega + 1)) (theta : Language.Formula P) :
    (checkCodeCosted X tree color theta).cost = 3 * tree.nodeCount + 2 := by
  simp [checkCodeCosted]
  omega

/-! ## Certified decomposition wrapper -/

/-- The costed checker on a certified inductive nice tree-decomposition.  The
certificate is used only by the correctness theorem; execution still follows
the constructor-coded tree directly. -/
def checkColoredCosted
    [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]
    (X : TauPGraph P V)
    (T : @InductiveNiceTreeDecomposition V
      (inferInstance : Fintype V) X.toMath.G)
    (color : V → Fin (omega + 1)) (theta : Language.Formula P) : Costed Bool :=
  checkCodeCosted X T.tree color theta

@[simp] theorem checkColoredCosted_value
    [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]
    (X : TauPGraph P V)
    (T : @InductiveNiceTreeDecomposition V
      (inferInstance : Fintype V) X.toMath.G)
    (color : V → Fin (omega + 1)) (theta : Language.Formula P) :
    (checkColoredCosted X T color theta).value = checkColored X T color theta := by
  simp [checkColoredCosted, checkColored]

@[simp] theorem checkColoredCosted_cost
    [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]
    (X : TauPGraph P V)
    (T : @InductiveNiceTreeDecomposition V
      (inferInstance : Fintype V) X.toMath.G)
    (color : V → Fin (omega + 1)) (theta : Language.Formula P) :
    (checkColoredCosted X T color theta).cost = 3 * T.tree.nodeCount + 2 := by
  simp [checkColoredCosted]

/-- Semantic correctness of the costed checker on a closed graph formula. -/
@[simp] theorem checkColoredCosted_value_eq_true_iff
    [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]
    (X : TauPGraph P V)
    (T : @InductiveNiceTreeDecomposition V
      (inferInstance : Fintype V) X.toMath.G)
    (color : V → Fin (omega + 1))
    (hcolor : T.tree.IsBagColoring color)
    (theta : Language.Formula P)
    (hFO : theta.freeFO = ∅) (hSO : theta.freeSO = ∅) :
    (checkColoredCosted X T color theta).value = true ↔
      Language.Semantics.Satisfies X.toMath theta := by
  rw [checkColoredCosted_value,
    checkColored_eq_true_iff X T color hcolor theta hFO hSO]

/-! ## Canonically numbered finite vertices -/

/-- Costed canonical checker for graphs whose vertex type is `Fin n`.  As in
`checkFin`, the globally injective coloring `Fin.castSucc` removes the coloring
argument from the executable interface. -/
def checkFinCosted [Fintype P] [DecidableEq P] {n : Nat}
    (X : TauPGraph P (Fin n))
    (T : @InductiveNiceTreeDecomposition (Fin n)
      (inferInstance : Fintype (Fin n)) X.toMath.G)
    (theta : Language.Formula P) : Costed Bool :=
  checkColoredCosted (omega := n) X T Fin.castSucc theta

@[simp] theorem checkFinCosted_value
    [Fintype P] [DecidableEq P] {n : Nat}
    (X : TauPGraph P (Fin n))
    (T : @InductiveNiceTreeDecomposition (Fin n)
      (inferInstance : Fintype (Fin n)) X.toMath.G)
    (theta : Language.Formula P) :
    (checkFinCosted X T theta).value = checkFin X T theta := by
  simp [checkFinCosted, checkFin]

@[simp] theorem checkFinCosted_cost
    [Fintype P] [DecidableEq P] {n : Nat}
    (X : TauPGraph P (Fin n))
    (T : @InductiveNiceTreeDecomposition (Fin n)
      (inferInstance : Fintype (Fin n)) X.toMath.G)
    (theta : Language.Formula P) :
    (checkFinCosted X T theta).cost = 3 * T.tree.nodeCount + 2 := by
  simp [checkFinCosted]

/-- Semantic correctness of the canonical costed checker on closed formulas. -/
@[simp] theorem checkFinCosted_value_eq_true_iff
    [Fintype P] [DecidableEq P] {n : Nat}
    (X : TauPGraph P (Fin n))
    (T : @InductiveNiceTreeDecomposition (Fin n)
      (inferInstance : Fintype (Fin n)) X.toMath.G)
    (theta : Language.Formula P)
    (hFO : theta.freeFO = ∅) (hSO : theta.freeSO = ∅) :
    (checkFinCosted X T theta).value = true ↔
      Language.Semantics.Satisfies X.toMath theta := by
  rw [checkFinCosted_value, checkFin_eq_true_iff X T theta hFO hSO]

end GraphMSO.Executable
