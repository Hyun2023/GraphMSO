import GraphMSO.treeLanguage.syntax
import GraphMSO.connectivity

/-!
# MSO semantics over labeled trees

Tarski semantics for the tree language of `GraphMSO.treeLanguage.syntax`.  A
model is a `TreeModel`: a node type with a parent relation and a labeling.
No tree axioms are baked into the structure; the intended models are the
Σ-tree encodings of decompositions, and every statement that needs a tree
property assumes it explicitly or inherits it from the encoding.

Besides the satisfaction relation and its simp interface, this file proves
the semantic characterizations of the derived formulas.  The characterization
of `conn` reduces to the partition description of induced connectivity from
`GraphMSO.connectivity`, evaluated in the symmetrized parent graph
`TreeModel.graph`.
-/

namespace GraphMSO.TreeLanguage

universe u v

/-- A model of the tree language: nodes, a parent relation, and a labeling
into the alphabet. -/
structure TreeModel (A : Type u) where
  /-- The type of tree nodes. -/
  Node : Type v
  /-- `parentRel p n` means `p` is the parent of `n`. -/
  parentRel : Node → Node → Prop
  /-- The letter carried by each node. -/
  label : Node → A

namespace TreeModel

variable {A : Type u}

/-- The undirected tree adjacency: the parent relation in either
orientation. -/
def graph (M : TreeModel A) : SimpleGraph M.Node :=
  SimpleGraph.fromRel M.parentRel

theorem graph_adj (M : TreeModel A) (u v : M.Node) :
    M.graph.Adj u v ↔ u ≠ v ∧ (M.parentRel u v ∨ M.parentRel v u) :=
  SimpleGraph.fromRel_adj M.parentRel u v

end TreeModel

/-- An assignment for tree formulas over a fixed model.  First-order
variables are optional, so the empty assignment exists even for the empty
model. -/
structure Assignment {A : Type u} (M : TreeModel A) where
  /-- First-order variables, ranging over nodes. -/
  fo : FOVar → Option M.Node
  /-- Monadic second-order variables, ranging over sets of nodes. -/
  so : SOVar → Set M.Node

namespace Assignment

variable {A : Type u} {M : TreeModel A}

/-- The empty assignment. -/
def empty (M : TreeModel A) : Assignment M where
  fo := fun _ => none
  so := fun _ => ∅

/-- Update a first-order variable. -/
def updateFO (ρ : Assignment M) (x : FOVar) (n : M.Node) : Assignment M where
  fo := fun y => if y = x then some n else ρ.fo y
  so := ρ.so

/-- Update a second-order variable. -/
def updateSO (ρ : Assignment M) (X : SOVar) (S : Set M.Node) : Assignment M where
  fo := ρ.fo
  so := fun Y => if Y = X then S else ρ.so Y

@[simp]
theorem updateFO_here (ρ : Assignment M) (x : FOVar) (n : M.Node) :
    (ρ.updateFO x n).fo x = some n := by
  simp [updateFO]

@[simp]
theorem updateFO_other (ρ : Assignment M) {x y : FOVar} (n : M.Node)
    (h : y ≠ x) :
    (ρ.updateFO x n).fo y = ρ.fo y := by
  simp [updateFO, h]

@[simp]
theorem updateFO_so (ρ : Assignment M) (x : FOVar) (n : M.Node) (X : SOVar) :
    (ρ.updateFO x n).so X = ρ.so X :=
  rfl

@[simp]
theorem updateSO_here (ρ : Assignment M) (X : SOVar) (S : Set M.Node) :
    (ρ.updateSO X S).so X = S := by
  simp [updateSO]

@[simp]
theorem updateSO_other (ρ : Assignment M) {X Y : SOVar} (S : Set M.Node)
    (h : Y ≠ X) :
    (ρ.updateSO X S).so Y = ρ.so Y := by
  simp [updateSO, h]

@[simp]
theorem updateSO_fo (ρ : Assignment M) (X : SOVar) (S : Set M.Node) (x : FOVar) :
    (ρ.updateSO X S).fo x = ρ.fo x :=
  rfl

end Assignment

namespace Semantics

open Formula

variable {A : Type u}

/-- Tarski semantics for tree formulas over a model and an assignment. -/
def SatisfiesAt (M : TreeModel A) : Formula A → Assignment M → Prop
  | false_, _ => False
  | equal x y, ρ => ∃ n : M.Node, ρ.fo x = some n ∧ ρ.fo y = some n
  | parent y x, ρ =>
      ∃ p n : M.Node, ρ.fo y = some p ∧ ρ.fo x = some n ∧ M.parentRel p n
  | labelMem S x, ρ => ∃ n : M.Node, ρ.fo x = some n ∧ M.label n ∈ S
  | inSet x X, ρ => ∃ n : M.Node, ρ.fo x = some n ∧ n ∈ ρ.so X
  | neg φ, ρ => ¬ SatisfiesAt M φ ρ
  | conj φ ψ, ρ => SatisfiesAt M φ ρ ∧ SatisfiesAt M ψ ρ
  | disj φ ψ, ρ => SatisfiesAt M φ ρ ∨ SatisfiesAt M ψ ρ
  | impl φ ψ, ρ => SatisfiesAt M φ ρ → SatisfiesAt M ψ ρ
  | biimpl φ ψ, ρ => SatisfiesAt M φ ρ ↔ SatisfiesAt M ψ ρ
  | existsFO x φ, ρ => ∃ n : M.Node, SatisfiesAt M φ (ρ.updateFO x n)
  | forallFO x φ, ρ => ∀ n : M.Node, SatisfiesAt M φ (ρ.updateFO x n)
  | existsSO X φ, ρ => ∃ S : Set M.Node, SatisfiesAt M φ (ρ.updateSO X S)
  | forallSO X φ, ρ => ∀ S : Set M.Node, SatisfiesAt M φ (ρ.updateSO X S)

/-- Satisfaction from the empty assignment, intended for sentences. -/
def Satisfies (M : TreeModel A) (φ : Formula A) : Prop :=
  SatisfiesAt M φ (Assignment.empty M)

variable {M : TreeModel A}

@[simp]
theorem satisfiesAt_conj (ρ : Assignment M) (φ ψ : Formula A) :
    SatisfiesAt M (conj φ ψ) ρ ↔ SatisfiesAt M φ ρ ∧ SatisfiesAt M ψ ρ :=
  Iff.rfl

@[simp]
theorem satisfiesAt_disj (ρ : Assignment M) (φ ψ : Formula A) :
    SatisfiesAt M (disj φ ψ) ρ ↔ SatisfiesAt M φ ρ ∨ SatisfiesAt M ψ ρ :=
  Iff.rfl

@[simp]
theorem satisfiesAt_impl (ρ : Assignment M) (φ ψ : Formula A) :
    SatisfiesAt M (impl φ ψ) ρ ↔ (SatisfiesAt M φ ρ → SatisfiesAt M ψ ρ) :=
  Iff.rfl

@[simp]
theorem satisfiesAt_neg (ρ : Assignment M) (φ : Formula A) :
    SatisfiesAt M (neg φ) ρ ↔ ¬ SatisfiesAt M φ ρ :=
  Iff.rfl

/-! ## Characterizations of the derived formulas -/

theorem satisfiesAt_labelMem_iff (ρ : Assignment M) {x : FOVar} {n : M.Node}
    (hx : ρ.fo x = some n) (S : Set A) :
    SatisfiesAt M (labelMem S x) ρ ↔ M.label n ∈ S := by
  simp [SatisfiesAt, hx]

theorem satisfiesAt_nonempty_iff (ρ : Assignment M) (X : SOVar) :
    SatisfiesAt M (Formula.nonempty X) ρ ↔ (ρ.so X).Nonempty := by
  simp [Formula.nonempty, SatisfiesAt, Set.Nonempty]

theorem satisfiesAt_empty_iff (ρ : Assignment M) (X : SOVar) :
    SatisfiesAt M (Formula.empty X) ρ ↔ ρ.so X = ∅ := by
  simp [Formula.empty, SatisfiesAt, Set.eq_empty_iff_forall_notMem]

theorem satisfiesAt_subset_iff (ρ : Assignment M) (Y X : SOVar) :
    SatisfiesAt M (Formula.subset Y X) ρ ↔ ρ.so Y ⊆ ρ.so X := by
  simp [Formula.subset, SatisfiesAt, Set.subset_def]

theorem satisfiesAt_root_iff (ρ : Assignment M) {x : FOVar} {n : M.Node}
    (hx : ρ.fo x = some n) :
    SatisfiesAt M (Formula.root_ x) ρ ↔ ∀ p : M.Node, ¬ M.parentRel p n := by
  simp [Formula.root_, SatisfiesAt, hx]

theorem satisfiesAt_adjTree_iff (ρ : Assignment M) {x y : FOVar}
    {m n : M.Node} (hx : ρ.fo x = some m) (hy : ρ.fo y = some n) :
    SatisfiesAt M (Formula.adjTree x y) ρ ↔
      M.parentRel m n ∨ M.parentRel n m := by
  simp [Formula.adjTree, SatisfiesAt, hx, hy]

/-- The witness part of the split hypothesis in `conn`: some element of `X`
is outside `Y`. -/
private theorem satisfiesAt_conn_rest_iff (ρ : Assignment M) (X Y : SOVar) :
    SatisfiesAt M
      (existsFO 0 (conj (inSet 0 X) (neg (inSet 0 Y)))) ρ ↔
      ∃ z, z ∈ ρ.so X ∧ z ∉ ρ.so Y := by
  simp [SatisfiesAt]

/-- The crossing-edge conclusion of `conn`. -/
private theorem satisfiesAt_conn_cross_iff (ρ : Assignment M) (X Y : SOVar) :
    SatisfiesAt M
      (existsFO 0 (existsFO 1
        (conj (inSet 0 Y)
          (conj (inSet 1 X)
            (conj (neg (inSet 1 Y)) (Formula.adjTree 0 1)))))) ρ ↔
      ∃ u ∈ ρ.so Y, ∃ v, v ∈ ρ.so X ∧ v ∉ ρ.so Y ∧
        (M.parentRel u v ∨ M.parentRel v u) := by
  simp [SatisfiesAt, Formula.adjTree]

/-- The `conn` formula holds of `X` iff `X` induces a connected subgraph of
the symmetrized parent graph. -/
theorem satisfiesAt_conn_iff (ρ : Assignment M) (X : SOVar) :
    SatisfiesAt M (Formula.conn X) ρ ↔
      (M.graph.induce (ρ.so X)).Connected := by
  have hne : X ≠ X + 1 := Ne.symm (Nat.succ_ne_self X)
  rw [SimpleGraph.induce_connected_iff_nonempty_and_forall_exists_adj,
    Formula.conn, satisfiesAt_conj, satisfiesAt_nonempty_iff]
  refine and_congr_right fun _ => ?_
  show (∀ S : Set M.Node, SatisfiesAt M _ (ρ.updateSO (X + 1) S)) ↔ _
  refine forall_congr' fun Y => ?_
  rw [satisfiesAt_impl, satisfiesAt_conj, satisfiesAt_conj,
    satisfiesAt_subset_iff, satisfiesAt_nonempty_iff,
    satisfiesAt_conn_rest_iff, satisfiesAt_conn_cross_iff]
  simp only [Assignment.updateSO_here, Assignment.updateSO_other, hne, ne_eq,
    not_false_iff]
  constructor
  · intro h hYX hYne hrest
    obtain ⟨z, hz⟩ := hrest
    obtain ⟨u, huY, v, hvX, hvY, hadj⟩ := h ⟨hYX, hYne, z, hz.1, hz.2⟩
    refine ⟨u, huY, v, ⟨hvX, hvY⟩, ?_⟩
    rw [TreeModel.graph_adj]
    exact ⟨fun huv => hvY (huv ▸ huY), hadj⟩
  · rintro h ⟨hYX, hYne, z, hzX, hzY⟩
    obtain ⟨u, huY, v, hv, hadj⟩ := h hYX hYne ⟨z, hzX, hzY⟩
    rw [TreeModel.graph_adj] at hadj
    exact ⟨u, huY, v, hv.1, hv.2, hadj.2⟩

theorem satisfiesAt_inSet_iff (ρ : Assignment M) {x : FOVar} {n : M.Node}
    (hx : ρ.fo x = some n) (X : SOVar) :
    SatisfiesAt M (inSet x X) ρ ↔ n ∈ ρ.so X := by
  simp [SatisfiesAt, hx]

/-- The parent-escape clause of `top`: some parent of `x` lies outside
`X`. -/
private theorem satisfiesAt_parent_notin_iff (ρ : Assignment M) {x : FOVar}
    {n : M.Node} (hx : ρ.fo x = some n) (X : SOVar) :
    SatisfiesAt M
      (existsFO (x + 1) (conj (parent (x + 1) x) (neg (inSet (x + 1) X)))) ρ ↔
      ∃ p, M.parentRel p n ∧ p ∉ ρ.so X := by
  simp [SatisfiesAt, hx]

/-- The `top` formula holds of `x` and `X` iff `x` lies in the connected set
`X` and has no parent inside `X`. -/
theorem satisfiesAt_top_iff (ρ : Assignment M) {x : FOVar} {n : M.Node}
    (hx : ρ.fo x = some n) (X : SOVar) :
    SatisfiesAt M (Formula.top x X) ρ ↔
      n ∈ ρ.so X ∧ (M.graph.induce (ρ.so X)).Connected ∧
        ((∀ p, ¬ M.parentRel p n) ∨ ∃ p, M.parentRel p n ∧ p ∉ ρ.so X) := by
  rw [Formula.top, satisfiesAt_conj, satisfiesAt_conj, satisfiesAt_disj,
    satisfiesAt_conn_iff, satisfiesAt_root_iff ρ hx,
    satisfiesAt_inSet_iff ρ hx, satisfiesAt_parent_notin_iff ρ hx]

/-- The `dangle` formula holds of `x` and `X` iff `x` lies outside `X` but
has a parent inside `X`. -/
theorem satisfiesAt_dangle_iff (ρ : Assignment M) {x : FOVar} {n : M.Node}
    (hx : ρ.fo x = some n) (X : SOVar) :
    SatisfiesAt M (Formula.dangle x X) ρ ↔
      n ∉ ρ.so X ∧ ∃ p, M.parentRel p n ∧ p ∈ ρ.so X := by
  simp [Formula.dangle, SatisfiesAt, hx]

end Semantics

end GraphMSO.TreeLanguage
