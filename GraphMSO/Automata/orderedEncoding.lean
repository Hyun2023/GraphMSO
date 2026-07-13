import GraphMSO.Automata.compile
import GraphMSO.Decomp.encoding
import GraphMSO.Decomp.treeModel
import GraphMSO.Decomp.translation
import GraphMSO.treeLanguage.modelIso

/-!
# Ordered binary encodings of constructor-coded nice trees

The decomposition-side encoding produces a `SigmaTree`, whose underlying tree
is the mathematical rooted decomposition.  Automata run on ordered binary
trees.  This file starts the bridge from the constructor-coded nice tree to the
ordered representation used by `BinTree.toTerm`.
-/

open scoped Classical

universe u v

namespace InductiveNiceTree

variable {V : Type u} {A : Type v}

/-- A constructor-coded nice tree as a tree-language model, with labels
supplied externally. -/
def toTreeModel {bag : Set V} (tree : InductiveNiceTree V bag)
    (label : Node tree → A) : GraphMSO.TreeLanguage.TreeModel A where
  Node := Node tree
  parentRel := tree.IsChild
  label := label

/-- Read a constructor-coded nice tree as an ordered binary tree, using the
left child for unary introduce/forget nodes and the two ordered children for
join nodes. -/
def toBinTree {bag : Set V} :
    (tree : InductiveNiceTree V bag) → (Node tree → A) → BinTree A
  | leaf, label =>
      BinTree.node (label PUnit.unit) .nil .nil
  | introduce _ child _, label =>
      BinTree.node (label none)
        (toBinTree child fun n => label (some n))
        .nil
  | forget _ child _, label =>
      BinTree.node (label none)
        (toBinTree child fun n => label (some n))
        .nil
  | join left right, label =>
      BinTree.node (label none)
        (toBinTree left fun n => label (some (.inl n)))
        (toBinTree right fun n => label (some (.inr n)))

/-- The canonical equivalence between constructor-code nodes and positions of
the ordered binary encoding. -/
def nodeEquivToBinTreePos {bag : Set V} :
    (tree : InductiveNiceTree V bag) → (label : Node tree → A) →
      Node tree ≃ (toBinTree tree label).Pos
  | leaf, _ =>
      { toFun := fun _ => none
        invFun := fun
          | none => PUnit.unit
          | some q => q.elim (fun p => p.elim) (fun p => p.elim)
        left_inv := by
          intro p
          cases p
          rfl
        right_inv := by
          intro p
          cases p with
          | none => rfl
          | some q =>
              cases q with
              | inl p => exact p.elim
              | inr p => exact p.elim }
  | introduce _ child _, label =>
      let e := nodeEquivToBinTreePos child fun n => label (some n)
      { toFun := fun
          | none => none
          | some n => some (.inl (e n))
        invFun := fun
          | none => none
          | some (.inl p) => some (e.symm p)
          | some (.inr p) => p.elim
        left_inv := by
          intro p
          cases p with
          | none => rfl
          | some p => simp
        right_inv := by
          intro p
          cases p with
          | none => rfl
          | some q =>
              cases q with
              | inl p => simp
              | inr p => exact p.elim }
  | forget _ child _, label =>
      let e := nodeEquivToBinTreePos child fun n => label (some n)
      { toFun := fun
          | none => none
          | some n => some (.inl (e n))
        invFun := fun
          | none => none
          | some (.inl p) => some (e.symm p)
          | some (.inr p) => p.elim
        left_inv := by
          intro p
          cases p with
          | none => rfl
          | some p => simp
        right_inv := by
          intro p
          cases p with
          | none => rfl
          | some q =>
              cases q with
              | inl p => simp
              | inr p => exact p.elim }
  | join left right, label =>
      let el := nodeEquivToBinTreePos left fun n => label (some (.inl n))
      let er := nodeEquivToBinTreePos right fun n => label (some (.inr n))
      { toFun := fun
          | none => none
          | some (.inl n) => some (.inl (el n))
          | some (.inr n) => some (.inr (er n))
        invFun := fun
          | none => none
          | some (.inl p) => some (.inl (el.symm p))
          | some (.inr p) => some (.inr (er.symm p))
        left_inv := by
          intro p
          cases p with
          | none => rfl
          | some q =>
              cases q with
              | inl p => simp
              | inr p => simp
        right_inv := by
          intro p
          cases p with
          | none => rfl
          | some q =>
              cases q with
              | inl p => simp
              | inr p => simp }

@[simp] theorem nodeEquivToBinTreePos_leaf_apply
    (label : Node (leaf : InductiveNiceTree V ∅) → A)
    (p : Node (leaf : InductiveNiceTree V ∅)) :
    nodeEquivToBinTreePos (leaf : InductiveNiceTree V ∅) label p = none := by
  cases p
  rfl

@[simp] theorem nodeEquivToBinTreePos_introduce_root {bag : Set V}
    (v : V) (child : InductiveNiceTree V bag) (fresh : v ∉ bag)
    (label : Node (introduce v child fresh) → A) :
    nodeEquivToBinTreePos (introduce v child fresh) label none = none :=
  rfl

@[simp] theorem nodeEquivToBinTreePos_forget_root {bag : Set V}
    (v : V) (child : InductiveNiceTree V bag) (present : v ∈ bag)
    (label : Node (forget v child present) → A) :
    nodeEquivToBinTreePos (forget v child present) label none = none :=
  rfl

@[simp] theorem nodeEquivToBinTreePos_join_root {bag : Set V}
    (left right : InductiveNiceTree V bag)
    (label : Node (join left right) → A) :
    nodeEquivToBinTreePos (join left right) label none = none :=
  rfl

/-- The ordered binary encoding preserves labels at corresponding nodes. -/
@[simp] theorem labelAt_toBinTree_nodeEquiv {bag : Set V}
    (tree : InductiveNiceTree V bag) (label : Node tree → A)
    (n : Node tree) :
    (toBinTree tree label).labelAt
        (nodeEquivToBinTreePos tree label n) =
      label n := by
  induction tree with
  | leaf =>
      cases n
      rfl
  | introduce v child fresh ih =>
      cases n with
      | none => rfl
      | some n =>
          simpa [toBinTree, nodeEquivToBinTreePos] using
            ih (fun n => label (some n)) n
  | forget v child present ih =>
      cases n with
      | none => rfl
      | some n =>
          simpa [toBinTree, nodeEquivToBinTreePos] using
            ih (fun n => label (some n)) n
  | join left right ihl ihr =>
      cases n with
      | none => rfl
      | some n =>
          cases n with
          | inl n =>
              simpa [toBinTree, nodeEquivToBinTreePos] using
                ihl (fun n => label (some (.inl n))) n
          | inr n =>
              simpa [toBinTree, nodeEquivToBinTreePos] using
                ihr (fun n => label (some (.inr n))) n

/-- The root of the coded tree corresponds to the root position of the ordered
binary encoding. -/
@[simp] theorem isRootPos_toBinTree_nodeEquiv_iff {bag : Set V}
    (tree : InductiveNiceTree V bag) (label : Node tree → A)
    (n : Node tree) :
    (toBinTree tree label).IsRootPos
        (nodeEquivToBinTreePos tree label n) ↔
      n = root tree := by
  induction tree with
  | leaf =>
      cases n
      simp [toBinTree, nodeEquivToBinTreePos, root, BinTree.IsRootPos]
  | introduce v child fresh ih =>
      cases n with
      | none =>
          simp [toBinTree, nodeEquivToBinTreePos, root, BinTree.IsRootPos]
      | some n =>
          simp [toBinTree, nodeEquivToBinTreePos, root, BinTree.IsRootPos]
  | forget v child present ih =>
      cases n with
      | none =>
          simp [toBinTree, nodeEquivToBinTreePos, root, BinTree.IsRootPos]
      | some n =>
          simp [toBinTree, nodeEquivToBinTreePos, root, BinTree.IsRootPos]
  | join left right ihl ihr =>
      cases n with
      | none =>
          simp [toBinTree, nodeEquivToBinTreePos, root, BinTree.IsRootPos]
      | some n =>
          cases n with
          | inl n =>
              simp [toBinTree, nodeEquivToBinTreePos, root, BinTree.IsRootPos]
          | inr n =>
              simp [toBinTree, nodeEquivToBinTreePos, root, BinTree.IsRootPos]

/-- Parent/child in the ordered binary model agrees with the child relation of
the constructor-coded nice tree. -/
@[simp] theorem parentRel_toBinTree_nodeEquiv_iff {bag : Set V}
    (tree : InductiveNiceTree V bag) (label : Node tree → A)
    (parent child : Node tree) :
    (toBinTree tree label).toTreeModel.parentRel
        (nodeEquivToBinTreePos tree label parent)
        (nodeEquivToBinTreePos tree label child) ↔
      tree.IsChild parent child := by
  induction tree with
  | leaf =>
      cases parent
      cases child
      simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
        BinTree.childRel, IsChild, children]
  | introduce v childTree fresh ih =>
      cases parent with
      | none =>
          cases child with
          | none =>
              simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                BinTree.childRel, IsChild, children]
          | some child =>
              simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                BinTree.childRel, IsChild, children,
                isRootPos_toBinTree_nodeEquiv_iff]
              constructor
              · intro h
                rw [h]
              · intro h
                exact Option.some.inj h
      | some parent =>
          cases child with
          | none =>
              simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                BinTree.childRel, IsChild, children]
          | some child =>
              have hmem :
                  child ∈ childTree.children parent ↔
                    ∃ a ∈ childTree.children parent, some a = some child := by
                constructor
                · intro h
                  exact ⟨child, h, rfl⟩
                · rintro ⟨a, ha, h⟩
                  simpa [Option.some.inj h] using ha
              have hmem' :
                  childTree.IsChild parent child ↔
                    (introduce v childTree fresh).IsChild (some parent) (some child) := by
                constructor
                · intro h
                  change some child ∈ (childTree.children parent).map some
                  change child ∈ childTree.children parent at h
                  exact List.mem_map.mpr ⟨child, h, rfl⟩
                · intro h
                  change some child ∈ (childTree.children parent).map some at h
                  obtain ⟨a, ha, haeq⟩ := List.mem_map.mp h
                  change child ∈ childTree.children parent
                  simpa [Option.some.inj haeq] using ha
              exact (ih (fun n => label (some n)) parent child).trans hmem'
  | forget v childTree present ih =>
      cases parent with
      | none =>
          cases child with
          | none =>
              simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                BinTree.childRel, IsChild, children]
          | some child =>
              simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                BinTree.childRel, IsChild, children,
                isRootPos_toBinTree_nodeEquiv_iff]
              constructor
              · intro h
                rw [h]
              · intro h
                exact Option.some.inj h
      | some parent =>
          cases child with
          | none =>
              simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                BinTree.childRel, IsChild, children]
          | some child =>
              have hmem :
                  child ∈ childTree.children parent ↔
                    ∃ a ∈ childTree.children parent, some a = some child := by
                constructor
                · intro h
                  exact ⟨child, h, rfl⟩
                · rintro ⟨a, ha, h⟩
                  simpa [Option.some.inj h] using ha
              have hmem' :
                  childTree.IsChild parent child ↔
                    (forget v childTree present).IsChild (some parent) (some child) := by
                constructor
                · intro h
                  change some child ∈ (childTree.children parent).map some
                  change child ∈ childTree.children parent at h
                  exact List.mem_map.mpr ⟨child, h, rfl⟩
                · intro h
                  change some child ∈ (childTree.children parent).map some at h
                  obtain ⟨a, ha, haeq⟩ := List.mem_map.mp h
                  change child ∈ childTree.children parent
                  simpa [Option.some.inj haeq] using ha
              exact (ih (fun n => label (some n)) parent child).trans hmem'
  | join left right ihl ihr =>
      cases parent with
      | none =>
          cases child with
          | none =>
              simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                BinTree.childRel, IsChild, children]
          | some child =>
              cases child with
              | inl child =>
                  simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                    BinTree.childRel, IsChild, children,
                    isRootPos_toBinTree_nodeEquiv_iff]
                  constructor
                  · intro h
                    left
                    rw [h]
                  · intro h
                    cases h with
                    | inl h =>
                        exact Sum.inl.inj (Option.some.inj h)
                    | inr h =>
                        cases Option.some.inj h
              | inr child =>
                  simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                    BinTree.childRel, IsChild, children,
                    isRootPos_toBinTree_nodeEquiv_iff]
                  constructor
                  · intro h
                    right
                    rw [h]
                  · intro h
                    cases h with
                    | inl h =>
                        cases Option.some.inj h
                    | inr h =>
                        exact Sum.inr.inj (Option.some.inj h)
      | some parent =>
          cases parent with
          | inl parent =>
              cases child with
              | none =>
                  simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                    BinTree.childRel, IsChild, children]
              | some child =>
                  cases child with
                  | inl child =>
                      have hmem :
                          child ∈ left.children parent ↔
                            ∃ a ∈ left.children parent,
                              some (Sum.inl a : left.Node ⊕ right.Node) =
                                some (Sum.inl child : left.Node ⊕ right.Node) := by
                        constructor
                        · intro h
                          exact ⟨child, h, rfl⟩
                        · rintro ⟨a, ha, h⟩
                          have haeq : a = child := Sum.inl.inj (Option.some.inj h)
                          simpa [haeq] using ha
                      have hmem' :
                          left.IsChild parent child ↔
                            (left.join right).IsChild
                              (some (Sum.inl parent)) (some (Sum.inl child)) := by
                        constructor
                        · intro h
                          change
                            some (Sum.inl child : left.Node ⊕ right.Node) ∈
                              (left.children parent).map
                                (fun child => some (Sum.inl child))
                          change child ∈ left.children parent at h
                          exact List.mem_map.mpr ⟨child, h, rfl⟩
                        · intro h
                          change
                            some (Sum.inl child : left.Node ⊕ right.Node) ∈
                              (left.children parent).map
                                (fun child => some (Sum.inl child)) at h
                          obtain ⟨a, ha, haeq⟩ := List.mem_map.mp h
                          change child ∈ left.children parent
                          have hachild : a = child :=
                            Sum.inl.inj (Option.some.inj haeq)
                          simpa [hachild] using ha
                      exact (ihl (fun n => label (some (.inl n))) parent child).trans
                        hmem'
                  | inr child =>
                      simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                        BinTree.childRel, IsChild, children, List.mem_map]
                      intro x hx h
                      cases Option.some.inj h
          | inr parent =>
              cases child with
              | none =>
                  simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                    BinTree.childRel, IsChild, children]
              | some child =>
                  cases child with
                  | inl child =>
                      simp [toBinTree, nodeEquivToBinTreePos, BinTree.toTreeModel,
                        BinTree.childRel, IsChild, children, List.mem_map]
                      intro x hx h
                      cases Option.some.inj h
                  | inr child =>
                      have hmem :
                          child ∈ right.children parent ↔
                            ∃ a ∈ right.children parent,
                              some (Sum.inr a : left.Node ⊕ right.Node) =
                                some (Sum.inr child : left.Node ⊕ right.Node) := by
                        constructor
                        · intro h
                          exact ⟨child, h, rfl⟩
                        · rintro ⟨a, ha, h⟩
                          have haeq : a = child := Sum.inr.inj (Option.some.inj h)
                          simpa [haeq] using ha
                      have hmem' :
                          right.IsChild parent child ↔
                            (left.join right).IsChild
                              (some (Sum.inr parent)) (some (Sum.inr child)) := by
                        constructor
                        · intro h
                          change
                            some (Sum.inr child : left.Node ⊕ right.Node) ∈
                              (right.children parent).map
                                (fun child => some (Sum.inr child))
                          change child ∈ right.children parent at h
                          exact List.mem_map.mpr ⟨child, h, rfl⟩
                        · intro h
                          change
                            some (Sum.inr child : left.Node ⊕ right.Node) ∈
                              (right.children parent).map
                                (fun child => some (Sum.inr child)) at h
                          obtain ⟨a, ha, haeq⟩ := List.mem_map.mp h
                          change child ∈ right.children parent
                          have hachild : a = child :=
                            Sum.inr.inj (Option.some.inj haeq)
                          simpa [hachild] using ha
                      exact (ihr (fun n => label (some (.inr n))) parent child).trans
                        hmem'

/-- The constructor-coded tree model is isomorphic to its ordered binary
encoding. -/
noncomputable def toBinTreeModelIso {bag : Set V}
    (tree : InductiveNiceTree V bag) (label : Node tree → A) :
    (tree.toTreeModel label).Iso (toBinTree tree label).toTreeModel where
  toEquiv := nodeEquivToBinTreePos tree label
  parentRel_iff := by
    intro parent child
    exact parentRel_toBinTree_nodeEquiv_iff tree label parent child
  label_eq := by
    intro n
    exact labelAt_toBinTree_nodeEquiv tree label n

end InductiveNiceTree

namespace InductiveNiceTreeDecomposition

variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {P : Type} {omega : ℕ}

/-- Ordered binary version of the Σ-tree encoding of an inductive nice
tree-decomposition. -/
noncomputable def orderedEncode (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) :
    BinTree (SigmaLetter P omega) :=
  T.tree.toBinTree fun n =>
    (T.encode vpred color hcolor).letter (T.realize n)

/-- The ordered encoding and the ordinary Σ-tree encoding present isomorphic
tree-language models. -/
noncomputable def orderedEncodeIso
    (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color) :
    (T.orderedEncode vpred color hcolor).toTreeModel.Iso
      (T.encode vpred color hcolor).toTreeModel where
  toEquiv :=
    (InductiveNiceTree.nodeEquivToBinTreePos T.tree
      (fun n => (T.encode vpred color hcolor).letter (T.realize n))).symm.trans
        (Equiv.ofBijective T.realize T.realization.realize_bijective)
  parentRel_iff := by
    intro p q
    let label : T.CodeNode → SigmaLetter P omega := fun n =>
      (T.encode vpred color hcolor).letter (T.realize n)
    let eCode := InductiveNiceTree.nodeEquivToBinTreePos T.tree label
    let eRealize : T.CodeNode ≃ T.Node :=
      Equiv.ofBijective T.realize T.realization.realize_bijective
    change
      (T.encode vpred color hcolor).toTreeModel.parentRel
          (T.realize (eCode.symm p)) (T.realize (eCode.symm q)) ↔
        (T.orderedEncode vpred color hcolor).toTreeModel.parentRel p q
    unfold InductiveNiceTreeDecomposition.encode
    rw [RootedTreeDecomposition.encode_toTreeModel_parentRel]
    have hchild := T.child_iff (eCode.symm p) (eCode.symm q)
    have hordered :=
      InductiveNiceTree.parentRel_toBinTree_nodeEquiv_iff
        T.tree label (eCode.symm p) (eCode.symm q)
    simpa [label, eCode, orderedEncode] using hchild.trans hordered.symm
  label_eq := by
    intro p
    let label : T.CodeNode → SigmaLetter P omega := fun n =>
      (T.encode vpred color hcolor).letter (T.realize n)
    let eCode := InductiveNiceTree.nodeEquivToBinTreePos T.tree label
    change
      (T.encode vpred color hcolor).toTreeModel.label
          (T.realize (eCode.symm p)) =
        (T.orderedEncode vpred color hcolor).toTreeModel.label p
    rw [SigmaTree.toTreeModel_label]
    have hlabel :=
      InductiveNiceTree.labelAt_toBinTree_nodeEquiv
        T.tree label (eCode.symm p)
    simpa [label, eCode, orderedEncode] using hlabel.symm

/-- Closed graph formulas may be evaluated on the ordered binary encoding by
transporting the already-proved translation theorem across
`orderedEncodeIso`. -/
theorem orderedEncode_satisfies_legal_translate_iff
    (T : InductiveNiceTreeDecomposition (G := G))
    (vpred : P → V → Prop) (color : V → BagColorSet omega)
    (hcolor : T.tree.IsBagColoring color)
    (θ : GraphMSO.Language.Formula P)
    (hFO : θ.freeFO = ∅) (hSO : θ.freeSO = ∅) :
    GraphMSO.TreeLanguage.Semantics.Satisfies
        (T.orderedEncode vpred color hcolor).toTreeModel
        (GraphMSO.TreeLanguage.Formula.conj
          (SigmaTree.legalFormula P omega) (θ.translate omega)) ↔
      GraphMSO.Language.Semantics.Satisfies
        (⟨V, G, vpred⟩ : τPGraph P) θ := by
  let φ :=
    GraphMSO.TreeLanguage.Formula.conj
      (SigmaTree.legalFormula P omega) (θ.translate omega)
  have hiso :=
    GraphMSO.TreeLanguage.Semantics.satisfies_iff_of_iso
      (orderedEncodeIso T vpred color hcolor) φ
  have htranslate :
      GraphMSO.TreeLanguage.Semantics.Satisfies
          (T.encode vpred color hcolor).toTreeModel φ ↔
        GraphMSO.Language.Semantics.Satisfies
          (⟨V, G, vpred⟩ : τPGraph P) θ := by
    simpa [φ, InductiveNiceTreeDecomposition.encode] using
      RootedTreeDecomposition.satisfies_legalFormula_conj_translate_iff
        (T := T.toRootedTreeDecomposition) (vpred := vpred)
        (color := color) (hcolor := (T.isBagColoring_iff color).2 hcolor)
        θ hFO hSO
  exact hiso.symm.trans htranslate

/-- Decomposition-given Courcelle statement for the ordered encoding: for a
closed `τ_P` formula and fixed width, the padded terms of ordered encodings
whose decoded graph satisfies the formula form a recognizable tree language.

The finiteness of the concrete `SigmaLetter` alphabet is kept as an explicit
assumption here; for fixed finite `P` and `omega` it is the expected finite
alphabet of the lecture note. -/
theorem exists_recognizable_orderedEncode_language
    [Finite P]
    (θ : GraphMSO.Language.Formula P)
    (hFO : θ.freeFO = ∅) (hSO : θ.freeSO = ∅) :
    ∃ L : Set (paddedAlphabet (SigmaLetter P omega)).Term,
      (paddedAlphabet (SigmaLetter P omega)).Recognizable L ∧
        ∀ (T : InductiveNiceTreeDecomposition (G := G))
          (vpred : P → V → Prop) (color : V → BagColorSet omega)
          (hcolor : T.tree.IsBagColoring color),
          (T.orderedEncode vpred color hcolor).toTerm ∈ L ↔
            GraphMSO.Language.Semantics.Satisfies
              (⟨V, G, vpred⟩ : τPGraph P) θ := by
  let φ :=
    GraphMSO.TreeLanguage.Formula.conj
      (SigmaTree.legalFormula P omega) (θ.translate omega)
  obtain ⟨L, hrec, hcorr⟩ :=
    BinTree.Automata.TrackLanguage.exists_recognizable_sentence_language
      (A := SigmaLetter P omega) φ
  refine ⟨L, hrec, ?_⟩
  intro T vpred color hcolor
  exact (hcorr (T.orderedEncode vpred color hcolor)).symm.trans
    (orderedEncode_satisfies_legal_translate_iff
      T vpred color hcolor θ hFO hSO)

/-- Uniform form of the decomposition-given Courcelle statement.  The
recognizable language depends only on `P`, `omega`, and the sentence, and is
shared by all finite input graphs and supplied inductive nice decompositions. -/
theorem exists_recognizable_orderedEncode_language_uniform
    [Finite P]
    (θ : GraphMSO.Language.Formula P)
    (hFO : θ.freeFO = ∅) (hSO : θ.freeSO = ∅) :
    ∃ L : Set (paddedAlphabet (SigmaLetter P omega)).Term,
      (paddedAlphabet (SigmaLetter P omega)).Recognizable L ∧
        ∀ {W : Type u} [Fintype W] {H : SimpleGraph W}
          (T : InductiveNiceTreeDecomposition (G := H))
          (vpred : P → W → Prop) (color : W → BagColorSet omega)
          (hcolor : T.tree.IsBagColoring color),
          (T.orderedEncode vpred color hcolor).toTerm ∈ L ↔
            GraphMSO.Language.Semantics.Satisfies
              (⟨W, H, vpred⟩ : τPGraph P) θ := by
  let φ :=
    GraphMSO.TreeLanguage.Formula.conj
      (SigmaTree.legalFormula P omega) (θ.translate omega)
  obtain ⟨L, hrec, hcorr⟩ :=
    BinTree.Automata.TrackLanguage.exists_recognizable_sentence_language
      (A := SigmaLetter P omega) φ
  refine ⟨L, hrec, ?_⟩
  intro W inst H T vpred color hcolor
  exact (hcorr (T.orderedEncode vpred color hcolor)).symm.trans
    (orderedEncode_satisfies_legal_translate_iff
      T vpred color hcolor θ hFO hSO)

end InductiveNiceTreeDecomposition
