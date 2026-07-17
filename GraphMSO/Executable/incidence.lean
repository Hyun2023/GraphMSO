import GraphMSO.Executable.modelCheck
import GraphMSO.incidenceTranslation
import GraphMSO.Decomp.normalization
import GraphMSO.Decomp.execIncidence
import GraphMSO.Decomp.execColoring

/-!
# End-to-end executable MSO₂ checking

This module closes the executable Phase 4/Phase 7 pipeline.  An ordinary
width-bounded decomposition of `G` is extended to the incidence graph,
nice-normalized, colored with `max omega 2 + 1` bag colors, and passed to the
verified Boolean MSO₁ checker after the incidence translation.
-/

namespace GraphMSO.Executable

open GraphMSO

/-- Boolean presentation of the two-sorted incidence structure. -/
def incidenceTauGraphExec {V : Type} [DecidableEq V] (G : SimpleGraph V) :
    TauPGraph IncSort (IncidenceVertex G) where
  adj := fun u v =>
    match u, v with
    | .fromV x, .fromEdge e => decide (x ∈ (e : Sym2 V))
    | .fromEdge e, .fromV x => decide (x ∈ (e : Sym2 V))
    | _, _ => false
  pred := fun s z =>
    match s, z with
    | .vert, .fromV _ => true
    | .edgeObj, .fromEdge _ => true
    | _, _ => false
  adj_symm := by intro u v; cases u <;> cases v <;> rfl
  adj_loopless := by intro v; cases v <;> rfl

/-- The Boolean presentation refines the proof-facing incidence structure. -/
@[simp] theorem incidenceTauGraphExec_toMath {V : Type} [DecidableEq V]
    (G : SimpleGraph V) :
    (incidenceTauGraphExec G).toMath = incidenceTauGraph G := by
  have hG : (incidenceTauGraphExec G).toMath.G = IncidenceGraph G := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    cases u <;> cases v <;> simp [incidenceTauGraphExec, IncidenceGraph]
  change (τPGraph.mk (IncidenceVertex G)
    (incidenceTauGraphExec G).toMath.G
    (incidenceTauGraphExec G).toMath.pred) = _
  rw [hG]
  congr
  funext s z
  apply propext
  cases s <;> cases z <;>
    simp [incidenceTauGraphExec, IncidenceVertex.IsVertex,
      IncidenceVertex.IsEdgeObj]

noncomputable instance incidenceTauGraphExecFintype
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    Fintype (incidenceTauGraphExec G).toMath.V := by
  change Fintype (IncidenceVertex G)
  infer_instance

instance incidenceTauGraphExecDecidableEq
    {V : Type} [DecidableEq V] (G : SimpleGraph V) :
    DecidableEq (incidenceTauGraphExec G).toMath.V := by
  change DecidableEq (IncidenceVertex G)
  infer_instance

theorem incidenceTauGraphExec_graph {V : Type} [DecidableEq V]
    (G : SimpleGraph V) :
    IncidenceGraph G = (incidenceTauGraphExec G).toMath.G := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  cases u <;> cases v <;> simp [incidenceTauGraphExec, IncidenceGraph]

namespace TreeDecomposition

/-- Transport a decomposition along equality of its underlying graph. -/
noncomputable def castGraph {V : Type} [Fintype V]
    {G H : SimpleGraph V} (h : G = H) (D : TreeDecomposition G) :
    TreeDecomposition H :=
  h ▸ D

theorem castGraph_hasWidth_iff {V : Type} [Fintype V]
    {G H : SimpleGraph V} (h : G = H) (D : TreeDecomposition G) (omega : Nat) :
    (castGraph h D).HasWidth omega ↔ D.HasWidth omega := by
  subst H
  rfl

end TreeDecomposition

/-- Incidence decomposition, transported to the Boolean presentation's
proof-facing graph. -/
noncomputable def incidenceDecompositionExec
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : TreeDecomposition G) :
    TreeDecomposition (incidenceTauGraphExec G).toMath.G :=
  TreeDecomposition.castGraph (incidenceTauGraphExec_graph G)
    D.incidenceDecomposition

theorem incidenceDecompositionExec_hasWidth
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : TreeDecomposition G) (omega : Nat)
    (hwidth : D.HasWidth omega) :
    (incidenceDecompositionExec D).HasWidth (max omega 2) := by
  apply (TreeDecomposition.castGraph_hasWidth_iff
    (incidenceTauGraphExec_graph G) D.incidenceDecomposition (max omega 2)).2
  exact D.incidenceDecomposition_hasWidth omega hwidth

/-- Certified nice incidence decomposition consumed by `checkColored`. -/
noncomputable def incidenceNiceExec
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : TreeDecomposition G) :
    @InductiveNiceTreeDecomposition (IncidenceVertex G)
      (inferInstance : Fintype (IncidenceVertex G))
      (incidenceTauGraphExec G).toMath.G :=
  (incidenceDecompositionExec D).normalize

theorem incidenceNiceExec_codeHasWidth
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : TreeDecomposition G) (omega : Nat)
    (hwidth : D.HasWidth omega) :
    (incidenceNiceExec D).tree.HasWidth (max omega 2) := by
  rw [← (incidenceNiceExec D).hasWidth_iff]
  exact (incidenceDecompositionExec D).normalize_hasWidth (max omega 2)
    (incidenceDecompositionExec_hasWidth D omega hwidth)

/-- Width-sized bag coloring chosen from the normalized incidence
decomposition. -/
noncomputable def incidenceColor
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : TreeDecomposition G) (omega : Nat)
    (hwidth : D.HasWidth omega) :
    IncidenceVertex G → Fin (max omega 2 + 1) :=
  ((incidenceNiceExec D).exists_bagColoring_of_codeHasWidth
    (max omega 2) (incidenceNiceExec_codeHasWidth D omega hwidth)).choose

theorem incidenceColor_isBagColoring
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : TreeDecomposition G) (omega : Nat)
    (hwidth : D.HasWidth omega) :
    (incidenceNiceExec D).tree.IsBagColoring
      (incidenceColor D omega hwidth) :=
  ((incidenceNiceExec D).exists_bagColoring_of_codeHasWidth
    (max omega 2) (incidenceNiceExec_codeHasWidth D omega hwidth)).choose_spec

/-- End-to-end Boolean model checker for a closed MSO₂ formula.  Closedness
is needed only by the correctness theorem, so the computational function may
also be run on arbitrary syntax. -/
noncomputable def checkMSO2
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : TreeDecomposition G) (omega : Nat)
    (hwidth : D.HasWidth omega) (phi : Formula) : Bool :=
  checkColored (omega := max omega 2) (incidenceTauGraphExec G)
    (incidenceNiceExec D) (incidenceColor D omega hwidth) phi.toIncidence

/-- Fully computable end-to-end MSO₂ checker: a rose-tree decomposition of
`G` in, a Boolean out.  The incidence extension, nice normalization, and
width-sized greedy bag coloring are all executable; correctness is
`checkMSO2Exec_eq_true_iff`. -/
def checkMSO2Exec {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : DecompTree V) (omega : ℕ) (phi : Formula) : Bool :=
  checkCode (omega := max omega 2) (incidenceTauGraphExec G)
    (DecompTree.incidenceTree G t).normalizeCode
    ((DecompTree.incidenceTree G t).greedyColoring (max omega 2))
    phi.toIncidence

/-- Correctness of the fully computable pipeline: for a valid width-`omega`
rose-tree decomposition of `G` and a closed MSO₂ formula, the Boolean answer
agrees with the MSO₂ semantics. -/
theorem checkMSO2Exec_eq_true_iff {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : DecompTree V) (omega : ℕ)
    (hvalid : t.IsDecompFor G) (hw : t.HasWidth omega)
    (phi : Formula) (hclosed : phi.Closed) :
    checkMSO2Exec G t omega phi = true ↔ Semantics.Satisfies G phi := by
  have hI : (DecompTree.incidenceTree G t).IsDecompFor
      (incidenceTauGraphExec G).toMath.G := by
    have h := DecompTree.incidenceTree_isDecompFor G hvalid
    rwa [incidenceTauGraphExec_graph G] at h
  have hwI := DecompTree.incidenceTree_hasWidth G t omega hw
  have hcolor := DecompTree.normalizeCode_greedyColoring_isBagColoring
    (DecompTree.incidenceTree G t) (max omega 2) hwI hI.runningIntersection
  have hfree := toIncidence_free_eq_empty phi hclosed
  have hcheck := checkColored_eq_true_iff (omega := max omega 2)
    (incidenceTauGraphExec G)
    ((DecompTree.incidenceTree G t).normalize hI)
    ((DecompTree.incidenceTree G t).greedyColoring (max omega 2))
    hcolor phi.toIncidence hfree.1 hfree.2
  rw [checkMSO2Exec]
  exact hcheck.trans (by
    rw [incidenceTauGraphExec_toMath]
    exact satisfies_toIncidence_iff phi hclosed)

/-- Correctness of the complete incidence-reduction and executable-checker
pipeline. -/
theorem checkMSO2_eq_true_iff
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : TreeDecomposition G) (omega : Nat)
    (hwidth : D.HasWidth omega) (phi : Formula) (hclosed : phi.Closed) :
    checkMSO2 D omega hwidth phi = true ↔ Semantics.Satisfies G phi := by
  have hfree := toIncidence_free_eq_empty phi hclosed
  have hcheck := checkColored_eq_true_iff
    (omega := max omega 2) (incidenceTauGraphExec G)
    (incidenceNiceExec D) (incidenceColor D omega hwidth)
    (incidenceColor_isBagColoring D omega hwidth)
    phi.toIncidence hfree.1 hfree.2
  rw [checkMSO2]
  exact hcheck.trans (by
    rw [incidenceTauGraphExec_toMath]
    exact satisfies_toIncidence_iff phi hclosed)

end GraphMSO.Executable
