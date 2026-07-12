import GraphMSO.Automata.term
import GraphMSO.treeLanguage.semantics
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option

/-!
# Ordered binary labeled trees

The ordered representation of the note's Σ-trees, bridging the logic side
and the automata side of the development:

* `BinTree A` is a finite ordered binary tree with `A`-labeled nodes;
  `nil` represents an absent child.
* `BinTree.toTreeModel` reads a binary tree as a model of the tree language
  (positions, the parent relation, labels), so tree MSO sentences can be
  evaluated on it.
* `BinTree.toTerm` pads a binary tree into a term over the ranked alphabet
  with one nullary symbol `⊥` (= `none`) and one binary symbol per letter,
  the encoding on which tree automata run.  The encoding is injective.

The remaining step of the Thatcher–Wright route — compiling a tree MSO
sentence into an automaton over `paddedAlphabet A` recognizing exactly the
encodings of its models — builds on these two bridges.
-/

universe u

/-- A finite ordered binary tree with `A`-labeled nodes; `nil` is the absent
child. -/
inductive BinTree (A : Type u) : Type u
  | nil : BinTree A
  | node (a : A) (l r : BinTree A) : BinTree A

namespace BinTree

variable {A : Type u}

/-! ## Positions -/

/-- The positions (nodes) of a binary tree.  The root of a nonempty tree is
`none`; child positions are embedded recursively. -/
def Pos : BinTree A → Type
  | .nil => Empty
  | .node _ l r => Option (Pos l ⊕ Pos r)

/-- Positions form a finite type. -/
def posFintype : (t : BinTree A) → Fintype t.Pos
  | .nil => by
      change Fintype Empty
      infer_instance
  | .node _ l r => by
      letI := posFintype l
      letI := posFintype r
      change Fintype (Option (Pos l ⊕ Pos r))
      infer_instance

instance instFintypePos (t : BinTree A) : Fintype t.Pos :=
  posFintype t

/-- The label at a position. -/
def labelAt : (t : BinTree A) → t.Pos → A
  | .nil => fun p => p.elim
  | .node a l r => fun p =>
      match p with
      | none => a
      | some (.inl q) => l.labelAt q
      | some (.inr q) => r.labelAt q

/-- The position is the root of its tree. -/
def IsRootPos : (t : BinTree A) → t.Pos → Prop
  | .nil => fun p => p.elim
  | .node _ _ _ => fun p => p = none

/-- The ordered child relation: `childRel false` is the first-child relation
`child₁`, and `childRel true` is `child₂`. -/
def childRel (b : Bool) : (t : BinTree A) → t.Pos → t.Pos → Prop
  | .nil => fun p _ => p.elim
  | .node _ l r => fun p q =>
      match p, q with
      | none, some (.inl q') => b = false ∧ l.IsRootPos q'
      | none, some (.inr q') => b = true ∧ r.IsRootPos q'
      | some (.inl p'), some (.inl q') => childRel b l p' q'
      | some (.inr p'), some (.inr q') => childRel b r p' q'
      | _, _ => False

/-- A binary tree as a model of the tree language: positions, the parent
relation (a child in either slot), and labels. -/
def toTreeModel (t : BinTree A) : GraphMSO.TreeLanguage.TreeModel A where
  Node := t.Pos
  parentRel := fun p q => t.childRel false p q ∨ t.childRel true p q
  label := t.labelAt

@[simp] theorem toTreeModel_node (t : BinTree A) :
    t.toTreeModel.Node = t.Pos :=
  rfl

@[simp] theorem toTreeModel_label (t : BinTree A) :
    t.toTreeModel.label = t.labelAt :=
  rfl

/-! ## The padded ranked-term encoding -/

/-- The padded ranked alphabet of the note: one nullary symbol `⊥`
(= `none`) for absent subtrees and one binary symbol per letter. -/
def _root_.paddedAlphabet (A : Type u) : RankedAlphabet where
  Symb := Option A
  arity := fun x =>
    match x with
    | none => 0
    | some _ => 2

/-- Pad a binary tree into a term over the padded alphabet. -/
def toTerm : BinTree A → (paddedAlphabet A).Term
  | .nil => .node (none : Option A) (fun i => i.elim0)
  | .node a l r => .node (some a) ![l.toTerm, r.toTerm]

/-- The padding encoding is injective: distinct trees have distinct padded
terms. -/
theorem toTerm_injective :
    Function.Injective (toTerm : BinTree A → (paddedAlphabet A).Term) := by
  intro s
  induction s with
  | nil =>
      intro t h
      cases t with
      | nil => rfl
      | node b l' r' =>
          exact absurd (congrArg
            (fun s => match s with
              | RankedAlphabet.Term.node f _ => f) h) (by simp [toTerm])
  | node a l r ihl ihr =>
      intro t h
      cases t with
      | nil =>
          exact absurd (congrArg
            (fun s => match s with
              | RankedAlphabet.Term.node f _ => f) h) (by simp [toTerm])
      | node b l' r' =>
          rw [toTerm, toTerm] at h
          obtain ⟨hab, hchild⟩ := RankedAlphabet.Term.node.inj h
          obtain rfl : a = b := Option.some.inj hab
          have hchild' :
              ![l.toTerm, r.toTerm] = ![l'.toTerm, r'.toTerm] :=
            eq_of_heq hchild
          have hl : l.toTerm = l'.toTerm := congrFun hchild' 0
          have hr : r.toTerm = r'.toTerm := congrFun hchild' 1
          rw [ihl hl, ihr hr]

end BinTree
