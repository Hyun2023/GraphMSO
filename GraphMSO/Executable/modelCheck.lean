import GraphMSO.Executable.compile
import GraphMSO.Executable.encodingCorrect
import GraphMSO.Executable.translation

/-!
# Executable decomposition-based model checker

The function in this file is the Phase 7 computational pipeline: it encodes
the constructor-coded nice decomposition, builds the executable Courcelle
tree formula, compiles that formula to a Boolean bottom-up automaton, and runs
the automaton.  The correctness theorem is factored through the encoder
refinement equation, which is proved by the encoding-correctness module.
-/

namespace GraphMSO.Executable

universe v

open GraphMSO

-- The executable compiler currently stores alphabet elements in finite states,
-- so its input alphabet (and hence the predicate-symbol type `P`) lives in
-- `Type`.  This agrees with the proof-facing `orderedEncode` interface.
variable {P : Type} {V : Type v} {omega : Nat}

/-- Run the computational pipeline on an empty-rooted constructor-coded nice
tree.  This is the proof-free entry point suitable for `#eval`; correctness is
obtained below when the code is certified by an
`InductiveNiceTreeDecomposition`. -/
def checkCode [Fintype P] [DecidableEq P] [DecidableEq V]
    (X : TauPGraph P V) (tree : InductiveNiceTree V ∅)
    (color : V → Fin (omega + 1)) (theta : Language.Formula P) : Bool :=
  checkTree (legalTranslate omega theta) (encode X color tree)

/-- Check a graph formula using an explicitly colored nice decomposition. -/
def checkColored [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]
    (X : TauPGraph P V)
    (T : @InductiveNiceTreeDecomposition V
      (inferInstance : Fintype V) X.toMath.G)
    (color : V → Fin (omega + 1)) (theta : Language.Formula P) : Bool :=
  checkCode X T.tree color theta

/-- Correctness of the complete executable pipeline, once the direct encoder
is identified with the existing proof-facing ordered encoding. -/
theorem checkColored_eq_true_iff_of_encode_eq
    [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]
    (X : TauPGraph P V)
    (T : @InductiveNiceTreeDecomposition V
      (inferInstance : Fintype V) X.toMath.G)
    (color : V → Fin (omega + 1))
    (hcolor : T.tree.IsBagColoring color)
    (theta : Language.Formula P)
    (hFO : theta.freeFO = ∅) (hSO : theta.freeSO = ∅)
    (hencode :
      (encode X color T.tree).map ExecSigmaLetter.decode =
        T.orderedEncode X.toMath.pred color hcolor) :
    checkColored X T color theta = true ↔
      Language.Semantics.Satisfies X.toMath theta := by
  rw [checkColored, checkCode, checkTree_eq_true_iff, toFormula_legalTranslate]
  let proofFormula :=
    GraphMSO.TreeLanguage.Formula.conj (SigmaTree.legalFormula P omega)
      (Language.Formula.translate omega theta)
  have hrelabel :=
    BinTree.Semantics.satisfies_map_iff ExecSigmaLetter.decode
      (encode X color T.tree) proofFormula
  rw [← hrelabel, hencode]
  simpa [proofFormula] using
    T.orderedEncode_satisfies_legal_translate_iff
      X.toMath.pred color hcolor theta hFO hSO

/-- Correctness of the complete executable model checker. -/
theorem checkColored_eq_true_iff
    [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]
    (X : TauPGraph P V)
    (T : @InductiveNiceTreeDecomposition V
      (inferInstance : Fintype V) X.toMath.G)
    (color : V → Fin (omega + 1))
    (hcolor : T.tree.IsBagColoring color)
    (theta : Language.Formula P)
    (hFO : theta.freeFO = ∅) (hSO : theta.freeSO = ∅) :
    checkColored X T color theta = true ↔
      Language.Semantics.Satisfies X.toMath theta :=
  checkColored_eq_true_iff_of_encode_eq X T color hcolor theta hFO hSO
    (encode_map_decode X T color hcolor)

/-! ## Canonically numbered finite vertices -/

/-- A convenience checker whose only substantive inputs are a graph on
`Fin n`, its nice decomposition, and a formula.  The globally injective map
`Fin.castSucc : Fin n → Fin (n + 1)` supplies a bag coloring automatically.

This fallback uses `n + 1` colors rather than the decomposition width, so
`checkColored` remains the fixed-width entry point for Courcelle's parameterized
algorithm. -/
def checkFin [Fintype P] [DecidableEq P] {n : Nat}
    (X : TauPGraph P (Fin n))
    (T : @InductiveNiceTreeDecomposition (Fin n)
      (inferInstance : Fintype (Fin n)) X.toMath.G)
    (theta : Language.Formula P) : Bool :=
  checkColored (omega := n) X T Fin.castSucc theta

/-- Correctness of `checkFin`, with its canonical injective coloring. -/
theorem checkFin_eq_true_iff
    [Fintype P] [DecidableEq P] {n : Nat}
    (X : TauPGraph P (Fin n))
    (T : @InductiveNiceTreeDecomposition (Fin n)
      (inferInstance : Fintype (Fin n)) X.toMath.G)
    (theta : Language.Formula P)
    (hFO : theta.freeFO = ∅) (hSO : theta.freeSO = ∅) :
    checkFin X T theta = true ↔
      Language.Semantics.Satisfies X.toMath theta := by
  have hcolor : T.tree.IsBagColoring (Fin.castSucc : Fin n → Fin (n + 1)) := by
    intro node u hu v hv huv
    exact Fin.castSucc_injective n huv
  simpa [checkFin] using
    checkColored_eq_true_iff X T Fin.castSucc hcolor theta hFO hSO

end GraphMSO.Executable
