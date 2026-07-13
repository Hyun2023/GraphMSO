import GraphMSO.Cost
import GraphMSO.Automata.orderedEncoding
import Mathlib.Tactic

/-!
# Abstract costs for the Courcelle pipeline

This file counts abstract primitive operations.  Each graph vertex, each
deterministic automaton transition, construction of one encoded node,
construction of one padded term symbol, and the final accepting-set test cost
one operation.  These are the fixed-width/fixed-formula primitives of Phase 6;
this is not a claim about Lean kernel or VM reduction steps.
-/

open scoped BigOperators

universe u v

namespace RankedAlphabet.Term

variable {S T : RankedAlphabet.{u}}

/-- Number of symbols in a finite ranked term. -/
def nodeCount : S.Term → ℕ
  | .node _ ts => 1 + ∑ i, (ts i).nodeCount

@[simp] theorem nodeCount_node (f : S.Symb)
    (ts : Fin (S.arity f) → S.Term) :
    (RankedAlphabet.Term.node f ts).nodeCount = 1 + ∑ i, (ts i).nodeCount :=
  rfl

theorem nodeCount_pos (t : S.Term) : 0 < t.nodeCount := by
  cases t
  simp

end RankedAlphabet.Term

namespace TreeAutomaton

open RankedAlphabet

variable {S : RankedAlphabet.{u}}

/-- Bottom-up evaluation, charging one operation for every transition. -/
def runCosted (A : TreeAutomaton S) : S.Term → Costed A.State
  | .node f ts =>
      let children : Costed (Fin (S.arity f) → A.State) :=
        ⟨fun i => (A.runCosted (ts i)).value,
          ∑ i, (A.runCosted (ts i)).cost⟩
      children.bind fun qs => Costed.tick (A.step f qs)

@[simp] theorem runCosted_value (A : TreeAutomaton S) (t : S.Term) :
    (A.runCosted t).value = A.run t := by
  induction t with
  | node f ts ih =>
      simp only [runCosted, Costed.bind_value, Costed.tick_value, run_node]
      congr 1
      funext i
      exact ih i

@[simp] theorem runCosted_cost (A : TreeAutomaton S) (t : S.Term) :
    (A.runCosted t).cost = t.nodeCount := by
  induction t with
  | node f ts ih =>
      simp [runCosted, RankedAlphabet.Term.nodeCount, ih]
      omega

/-- Run the automaton and charge one final accepting-set membership test. -/
def acceptsCosted (A : TreeAutomaton S) (t : S.Term) : Costed Prop :=
  (A.runCosted t).bind fun q => Costed.tick (q ∈ A.accept)

@[simp] theorem acceptsCosted_value_iff (A : TreeAutomaton S) (t : S.Term) :
    (A.acceptsCosted t).value ↔ t ∈ A.language := by
  change (A.runCosted t).value ∈ A.accept ↔ A.run t ∈ A.accept
  rw [runCosted_value]

@[simp] theorem acceptsCosted_cost (A : TreeAutomaton S) (t : S.Term) :
    (A.acceptsCosted t).cost = t.nodeCount + 1 := by
  simp [acceptsCosted]

end TreeAutomaton

namespace BinTree

variable {A : Type u}

/-- Number of genuine labeled nodes, excluding absent children. -/
def nodeCount : BinTree A → ℕ
  | .nil => 0
  | .node _ l r => 1 + l.nodeCount + r.nodeCount

@[simp] theorem nodeCount_nil : (BinTree.nil : BinTree A).nodeCount = 0 :=
  rfl

@[simp] theorem nodeCount_node (a : A) (l r : BinTree A) :
    (BinTree.node a l r).nodeCount = 1 + l.nodeCount + r.nodeCount :=
  rfl

/-- The recursive count agrees with the finite position type. -/
theorem nodeCount_eq_card_pos (t : BinTree A) :
    t.nodeCount = Fintype.card t.Pos := by
  induction t with
  | nil =>
      simp [Pos]
  | node a l r ihl ihr =>
      simp [Pos, ihl, ihr, Fintype.card_option, Fintype.card_sum]
      omega

/-- Padding a binary tree introduces one null symbol for every missing child. -/
@[simp] theorem toTerm_nodeCount (t : BinTree A) :
    t.toTerm.nodeCount = 2 * t.nodeCount + 1 := by
  induction t with
  | nil =>
      rfl
  | node a l r ihl ihr =>
      simp [toTerm, paddedAlphabet, Fin.sum_univ_two, ihl, ihr]
      omega

/-- Construct the padded term, ticking once for every produced symbol. -/
def toTermCosted : BinTree A → Costed (paddedAlphabet A).Term
  | .nil =>
      Costed.tick (.node (none : Option A) (fun i => i.elim0))
  | .node a l r =>
      l.toTermCosted.bind fun lt =>
        r.toTermCosted.bind fun rt =>
          Costed.tick (.node (some a) ![lt, rt])

@[simp] theorem toTermCosted_value (t : BinTree A) :
    t.toTermCosted.value = t.toTerm :=
  by
    induction t with
    | nil => rfl
    | node a l r ihl ihr =>
        simp [toTermCosted, toTerm, ihl, ihr]

@[simp] theorem toTermCosted_cost (t : BinTree A) :
    t.toTermCosted.cost = 2 * t.nodeCount + 1 := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp [toTermCosted, ihl, ihr]
      omega

end BinTree

namespace InductiveNiceTree

variable {V : Type u} {A : Type v}

/-- Number of constructor-coded nice-tree nodes. -/
def nodeCount {bag : Set V} : (tree : InductiveNiceTree V bag) → ℕ
  | .leaf => 1
  | .introduce _ child _ => child.nodeCount + 1
  | .forget _ child _ => child.nodeCount + 1
  | .join left right => left.nodeCount + right.nodeCount + 1

/-- The recursive count agrees with the finite code-node type. -/
theorem nodeCount_eq_card_node {bag : Set V} (tree : InductiveNiceTree V bag) :
    tree.nodeCount = Fintype.card (Node tree) := by
  induction tree with
  | leaf =>
      simp [nodeCount, Node]
  | introduce v child fresh ih =>
      simp [nodeCount, Node, ih, Fintype.card_option]
  | forget v child present ih =>
      simp [nodeCount, Node, ih, Fintype.card_option]
  | join left right ihl ihr =>
      simp [nodeCount, Node, ihl, ihr, Fintype.card_option, Fintype.card_sum]

/-- Read a constructor-coded nice tree as a binary tree, ticking at each node. -/
def toBinTreeCosted {bag : Set V} :
    (tree : InductiveNiceTree V bag) → (Node tree → A) → Costed (BinTree A)
  | .leaf, label =>
      Costed.tick (.node (label PUnit.unit) .nil .nil)
  | .introduce _ child _, label =>
      (toBinTreeCosted child fun n => label (some n)).bind fun encoded =>
        Costed.tick (.node (label none) encoded .nil)
  | .forget _ child _, label =>
      (toBinTreeCosted child fun n => label (some n)).bind fun encoded =>
        Costed.tick (.node (label none) encoded .nil)
  | .join left right, label =>
      (toBinTreeCosted left fun n => label (some (.inl n))).bind fun leftEncoded =>
        (toBinTreeCosted right fun n => label (some (.inr n))).bind fun rightEncoded =>
          Costed.tick (.node (label none) leftEncoded rightEncoded)

@[simp] theorem toBinTreeCosted_value {bag : Set V}
    (tree : InductiveNiceTree V bag) (label : Node tree → A) :
    (tree.toBinTreeCosted label).value = tree.toBinTree label := by
  induction tree with
  | leaf => rfl
  | introduce v child fresh ih =>
      simp [toBinTreeCosted, toBinTree, ih]
  | forget v child present ih =>
      simp [toBinTreeCosted, toBinTree, ih]
  | join left right ihl ihr =>
      simp [toBinTreeCosted, toBinTree, ihl, ihr]

@[simp] theorem toBinTreeCosted_cost {bag : Set V}
    (tree : InductiveNiceTree V bag) (label : Node tree → A) :
    (tree.toBinTreeCosted label).cost = tree.nodeCount := by
  induction tree with
  | leaf => rfl
  | introduce v child fresh ih =>
      simp [toBinTreeCosted, nodeCount, ih]
  | forget v child present ih =>
      simp [toBinTreeCosted, nodeCount, ih]
  | join left right ihl ihr =>
      simp [toBinTreeCosted, nodeCount, ihl, ihr]
      omega

/-- Reading a constructor-coded nice tree as a binary tree preserves nodes. -/
@[simp] theorem toBinTree_nodeCount {bag : Set V}
    (tree : InductiveNiceTree V bag) (label : Node tree → A) :
    (toBinTree tree label).nodeCount = tree.nodeCount := by
  induction tree with
  | leaf =>
      rfl
  | introduce v child fresh ih =>
      simp [toBinTree, nodeCount, BinTree.nodeCount, ih]
      omega
  | forget v child present ih =>
      simp [toBinTree, nodeCount, BinTree.nodeCount, ih]
      omega
  | join left right ihl ihr =>
      simp [toBinTree, nodeCount, ihl, ihr]
      omega

end InductiveNiceTree

namespace SigmaTree

variable {P : Type u} {omega : ℕ}

/-- Size of a finite sigma tree. -/
def nodeCount (S : SigmaTree P omega) [Fintype S.Node] : ℕ :=
  Fintype.card S.Node

end SigmaTree

namespace GraphMSO.Language.Formula

variable {P : Type u}

/-- Syntactic size of a graph-language formula. -/
def size : GraphMSO.Language.Formula P → ℕ
  | .false_ | .equal _ _ | .adj _ _ | .pred _ _ | .inSet _ _ => 1
  | .neg φ | .existsFO _ φ | .forallFO _ φ | .existsSO _ φ | .forallSO _ φ =>
      φ.size + 1
  | .conj φ ψ | .disj φ ψ | .impl φ ψ | .biimpl φ ψ =>
      φ.size + ψ.size + 1

theorem size_pos (φ : GraphMSO.Language.Formula P) : 0 < φ.size := by
  induction φ <;> simp [size, *]

end GraphMSO.Language.Formula

namespace GraphMSO.TreeLanguage.Formula

variable {A : Type u}

/-- Syntactic size of a tree-language formula. -/
def size : GraphMSO.TreeLanguage.Formula A → ℕ
  | .false_ | .equal _ _ | .parent _ _ | .labelMem _ _ | .labelMem₂ _ _ _ |
      .inSet _ _ => 1
  | .neg φ | .existsFO _ φ | .forallFO _ φ | .existsSO _ φ | .forallSO _ φ =>
      φ.size + 1
  | .conj φ ψ | .disj φ ψ | .impl φ ψ | .biimpl φ ψ =>
      φ.size + ψ.size + 1

theorem size_pos (φ : GraphMSO.TreeLanguage.Formula A) : 0 < φ.size := by
  induction φ <;> simp [size, *]

end GraphMSO.TreeLanguage.Formula

/-- A standard height-indexed power tower. -/
def courcelleTower : ℕ → ℕ → ℕ
  | 0, base => base
  | height + 1, base => 2 ^ courcelleTower height base

/--
An explicit, deliberately conservative tower-shaped parameter function.  The
abstract online pass below actually has coefficient eight; this larger
function packages the requested dependence on width and source-formula size.
It is not a bound on automaton construction or on the number of states.
-/
def explicitCourcelleFactor {P : Type u} (omega : ℕ)
    (φ : GraphMSO.Language.Formula P) : ℕ :=
  courcelleTower (φ.size + 1) (omega + 2) + 8

theorem eight_le_explicitCourcelleFactor {P : Type u} (omega : ℕ)
    (φ : GraphMSO.Language.Formula P) :
    8 ≤ explicitCourcelleFactor omega φ := by
  simp [explicitCourcelleFactor]

namespace InductiveNiceTreeDecomposition

open RankedAlphabet

variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {P : Type} {omega : ℕ}

/-- The realization bijection transfers the code-node count to the normal decomposition. -/
theorem codeNodeCount_eq_nodeCount (T : InductiveNiceTreeDecomposition (G := G)) :
    T.tree.nodeCount = Fintype.card T.Node := by
  rw [InductiveNiceTree.nodeCount_eq_card_node]
  exact Fintype.card_congr
    (Equiv.ofBijective T.realize T.realization.realize_bijective)

@[simp] theorem orderedEncode_nodeCount
    (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) :
    (T.orderedEncode vpred color hcolor).nodeCount = T.tree.nodeCount := by
  simp [orderedEncode]

@[simp] theorem orderedEncode_term_nodeCount
    (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) :
    (T.orderedEncode vpred color hcolor).toTerm.nodeCount =
      2 * Fintype.card T.Node + 1 := by
  rw [BinTree.toTerm_nodeCount, orderedEncode_nodeCount,
    codeNodeCount_eq_nodeCount]

/-- Construct the ordered encoding, charging once per decomposition node. -/
noncomputable def orderedEncodeCosted
    (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) :
    Costed (BinTree (SigmaLetter P omega)) :=
  T.tree.toBinTreeCosted fun n =>
    (T.encode vpred color hcolor).letter (T.realize n)

@[simp] theorem orderedEncodeCosted_value
    (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) :
    (T.orderedEncodeCosted vpred color hcolor).value =
      T.orderedEncode vpred color hcolor :=
  by
    simp [orderedEncodeCosted, orderedEncode]

@[simp] theorem orderedEncodeCosted_cost
    (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) :
    (T.orderedEncodeCosted vpred color hcolor).cost = Fintype.card T.Node := by
  simp [orderedEncodeCosted, codeNodeCount_eq_nodeCount]

/--
The complete abstract model-checking pass: tick once per graph vertex,
construct the ordered encoding, construct its padded term, run the automaton,
and test the accepting set.
-/
noncomputable def modelCheckCosted
    (A : TreeAutomaton (paddedAlphabet (SigmaLetter P omega)))
    (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) : Costed Prop :=
  (Costed.ticks (Fintype.card V)).bind fun _ =>
    (T.orderedEncodeCosted vpred color hcolor).bind fun encoded =>
      encoded.toTermCosted.bind fun term =>
        A.acceptsCosted term

@[simp] theorem modelCheckCosted_value_iff_language
    (A : TreeAutomaton (paddedAlphabet (SigmaLetter P omega)))
    (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) :
    (T.modelCheckCosted A vpred color hcolor).value ↔
      (T.orderedEncode vpred color hcolor).toTerm ∈ A.language := by
  simp [modelCheckCosted]

@[simp] theorem modelCheckCosted_cost
    (A : TreeAutomaton (paddedAlphabet (SigmaLetter P omega)))
    (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) :
    (T.modelCheckCosted A vpred color hcolor).cost =
      Fintype.card V + 5 * Fintype.card T.Node + 3 := by
  simp [modelCheckCosted, orderedEncodeCosted, codeNodeCount_eq_nodeCount]
  omega

theorem modelCheckCosted_cost_le
    (A : TreeAutomaton (paddedAlphabet (SigmaLetter P omega)))
    (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) :
    (T.modelCheckCosted A vpred color hcolor).cost ≤
      8 * (Fintype.card V + Fintype.card T.Node) := by
  rw [modelCheckCosted_cost]
  have hnode : 1 ≤ Fintype.card T.Node :=
    Fintype.card_pos_iff.mpr ⟨T.root⟩
  omega

/-- The constant-eight bound implies the explicit tower-shaped bound. -/
theorem modelCheckCosted_cost_le_explicit
    (A : TreeAutomaton (paddedAlphabet (SigmaLetter P omega)))
    (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color)
    (φ : GraphMSO.Language.Formula P) :
    (T.modelCheckCosted A vpred color hcolor).cost ≤
      explicitCourcelleFactor omega φ *
        (Fintype.card V + Fintype.card T.Node) := by
  calc
    (T.modelCheckCosted A vpred color hcolor).cost ≤
        8 * (Fintype.card V + Fintype.card T.Node) :=
      T.modelCheckCosted_cost_le A vpred color hcolor
    _ ≤ explicitCourcelleFactor omega φ *
        (Fintype.card V + Fintype.card T.Node) :=
      Nat.mul_le_mul_right _ (eight_le_explicitCourcelleFactor omega φ)

/--
Phase 6 Courcelle statement in the abstract unit-cost model.  For a closed
graph MSO sentence there is a fixed finite tree automaton whose costed pass is
uniformly correct for all finite input graphs and supplied inductive nice
decompositions, and is bounded by an explicit function of width and formula
size times `|V| + |N(T)|`.
-/
theorem exists_costed_courcelle_automaton
    [Finite P]
    (φ : GraphMSO.Language.Formula P)
    (hFO : φ.freeFO = ∅) (hSO : φ.freeSO = ∅) :
    ∃ A : TreeAutomaton (paddedAlphabet (SigmaLetter P omega)),
      ∀ {W : Type u} [Fintype W] {H : SimpleGraph W}
        (T : InductiveNiceTreeDecomposition (G := H))
        (vpred : P → W → Prop) (color : W → BagColorSet omega)
        (hcolor : T.tree.IsBagColoring color),
        ((T.modelCheckCosted A vpred color hcolor).value ↔
          GraphMSO.Language.Semantics.Satisfies
            (⟨W, H, vpred⟩ : τPGraph P) φ) ∧
        (T.modelCheckCosted A vpred color hcolor).cost ≤
          explicitCourcelleFactor omega φ *
            (Fintype.card W + Fintype.card T.Node) := by
  obtain ⟨L, hrec, hcorr⟩ :=
    exists_recognizable_orderedEncode_language_uniform (omega := omega)
      φ hFO hSO
  obtain ⟨A, hA⟩ := hrec
  refine ⟨A, ?_⟩
  intro W inst H T vpred color hcolor
  constructor
  · rw [modelCheckCosted_value_iff_language, hA]
    exact hcorr T vpred color hcolor
  · exact T.modelCheckCosted_cost_le_explicit A vpred color hcolor φ

/-- Width-only form: the realization transfer and bag-coloring theorem supply
the coloring required by the ordered encoding. -/
theorem exists_costed_courcelle_automaton_of_width
    [Finite P]
    (φ : GraphMSO.Language.Formula P)
    (hFO : φ.freeFO = ∅) (hSO : φ.freeSO = ∅) :
    ∃ A : TreeAutomaton (paddedAlphabet (SigmaLetter P omega)),
      ∀ {W : Type u} [Fintype W] {H : SimpleGraph W}
        (T : InductiveNiceTreeDecomposition (G := H))
        (vpred : P → W → Prop) (_hwidth : T.tree.HasWidth omega),
        ∃ color : W → BagColorSet omega,
          ∃ hcolor : T.tree.IsBagColoring color,
          ((T.modelCheckCosted A vpred color hcolor).value ↔
            GraphMSO.Language.Semantics.Satisfies
              (⟨W, H, vpred⟩ : τPGraph P) φ) ∧
          (T.modelCheckCosted A vpred color hcolor).cost ≤
            explicitCourcelleFactor omega φ *
              (Fintype.card W + Fintype.card T.Node) := by
  obtain ⟨A, hA⟩ :=
    exists_costed_courcelle_automaton (omega := omega) φ hFO hSO
  refine ⟨A, ?_⟩
  intro W inst H T vpred hwidth
  obtain ⟨color, hcolor⟩ :=
    T.exists_bagColoring_of_codeHasWidth omega hwidth
  exact ⟨color, hcolor, hA T vpred color hcolor⟩

end InductiveNiceTreeDecomposition
