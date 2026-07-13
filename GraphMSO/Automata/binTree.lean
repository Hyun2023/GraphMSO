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

universe u v

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

/-! ## Relabeling -/

/-- Relabel a binary tree without changing its ordered shape. -/
def map {B : Type v} (f : A → B) : BinTree A → BinTree B
  | .nil => .nil
  | .node a l r => .node (f a) (l.map f) (r.map f)

@[simp] theorem map_nil {B : Type v} (f : A → B) :
    (BinTree.nil : BinTree A).map f = .nil :=
  rfl

@[simp] theorem map_node {B : Type v} (f : A → B) (a : A) (l r : BinTree A) :
    (BinTree.node a l r).map f = .node (f a) (l.map f) (r.map f) :=
  rfl

/-- Relabeling preserves the position type, up to the canonical recursive
equivalence. -/
def posEquivMap {B : Type v} (f : A → B) : (t : BinTree A) → t.Pos ≃ (t.map f).Pos
  | .nil =>
      { toFun := fun p => p.elim
        invFun := fun p => p.elim
        left_inv := fun p => p.elim
        right_inv := fun p => p.elim }
  | .node _ l r =>
      let el := posEquivMap f l
      let er := posEquivMap f r
      { toFun := fun
          | none => none
          | some (.inl p) => some (.inl (el p))
          | some (.inr p) => some (.inr (er p))
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

@[simp] theorem posEquivMap_node_root {B : Type v} (f : A → B)
    (a : A) (l r : BinTree A) :
    posEquivMap f (.node a l r) none = none :=
  rfl

@[simp] theorem posEquivMap_node_left {B : Type v} (f : A → B)
    (a : A) (l r : BinTree A) (p : l.Pos) :
    posEquivMap f (.node a l r) (some (.inl p)) =
      some (.inl (posEquivMap f l p)) :=
  rfl

@[simp] theorem posEquivMap_node_right {B : Type v} (f : A → B)
    (a : A) (l r : BinTree A) (p : r.Pos) :
    posEquivMap f (.node a l r) (some (.inr p)) =
      some (.inr (posEquivMap f r p)) :=
  rfl

/-- The label at a position. -/
def labelAt : (t : BinTree A) → t.Pos → A
  | .nil => fun p => p.elim
  | .node a l r => fun p =>
      match p with
      | none => a
      | some (.inl q) => l.labelAt q
      | some (.inr q) => r.labelAt q

@[simp] theorem labelAt_map {B : Type v} (f : A → B)
    (t : BinTree A) (p : t.Pos) :
    (t.map f).labelAt (posEquivMap f t p) = f (t.labelAt p) := by
  induction t with
  | nil => exact p.elim
  | node a l r ihl ihr =>
      cases p with
      | none => rfl
      | some q =>
          cases q with
          | inl p => simpa using ihl p
          | inr p => simpa using ihr p

/-- The position is the root of its tree. -/
def IsRootPos : (t : BinTree A) → t.Pos → Prop
  | .nil => fun p => p.elim
  | .node _ _ _ => fun p => p = none

theorem isRootPos_map_iff {B : Type v} (f : A → B)
    (t : BinTree A) (p : t.Pos) :
    (t.map f).IsRootPos (posEquivMap f t p) ↔ t.IsRootPos p := by
  induction t with
  | nil => exact p.elim
  | node a l r ihl ihr =>
      cases p with
      | none =>
          simp [IsRootPos, posEquivMap]
      | some q =>
          cases q with
          | inl p =>
              simp [IsRootPos, posEquivMap]
          | inr p =>
              simp [IsRootPos, posEquivMap]

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

theorem childRel_map_iff {B : Type v} (f : A → B) (b : Bool)
    (t : BinTree A) (p q : t.Pos) :
    (t.map f).childRel b (posEquivMap f t p) (posEquivMap f t q) ↔
      t.childRel b p q := by
  induction t with
  | nil => exact p.elim
  | node a l r ihl ihr =>
      cases p with
      | none =>
          cases q with
          | none => rfl
          | some q' =>
              cases q' with
              | inl q =>
                  change
                    (b = false ∧ (l.map f).IsRootPos (posEquivMap f l q)) ↔
                      (b = false ∧ l.IsRootPos q)
                  exact and_congr_right fun _ => isRootPos_map_iff f l q
              | inr q =>
                  change
                    (b = true ∧ (r.map f).IsRootPos (posEquivMap f r q)) ↔
                      (b = true ∧ r.IsRootPos q)
                  exact and_congr_right fun _ => isRootPos_map_iff f r q
      | some p' =>
          cases p' with
          | inl p =>
              cases q with
              | none => rfl
              | some q' =>
                  cases q' with
                  | inl q => exact ihl p q
                  | inr q => rfl
          | inr p =>
              cases q with
              | none => rfl
              | some q' =>
                  cases q' with
                  | inl q => rfl
                  | inr q => exact ihr p q

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

/-- A relabeling of binary-tree labels induces an arity-preserving relabeling
of the padded ranked alphabet. -/
def _root_.paddedMapHom {A B : Type u} (f : A → B) :
    (paddedAlphabet A).Hom (paddedAlphabet B) where
  toFun := Option.map f
  arity_eq := by
    intro x
    cases x <;> rfl

@[simp] theorem paddedMapHom_none {B : Type u} (f : A → B) :
    paddedMapHom f (none : Option A) = none :=
  rfl

@[simp] theorem paddedMapHom_some {B : Type u} (f : A → B) (a : A) :
    paddedMapHom f (some a) = some (f a) :=
  rfl

/-- Pad a binary tree into a term over the padded alphabet. -/
def toTerm : BinTree A → (paddedAlphabet A).Term
  | .nil => .node (none : Option A) (fun i => i.elim0)
  | .node a l r => .node (some a) ![l.toTerm, r.toTerm]

/-- Read a padded ranked term back as an ordered binary tree. -/
def ofTerm : (paddedAlphabet A).Term → BinTree A
  | .node none _ => .nil
  | .node (some a) ts =>
      .node a
        (ofTerm (ts ⟨0, by simp [paddedAlphabet]⟩))
        (ofTerm (ts ⟨1, by simp [paddedAlphabet]⟩))

@[simp] theorem ofTerm_toTerm (t : BinTree A) :
    ofTerm t.toTerm = t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      rw [toTerm, ofTerm]
      simp [ihl, ihr]

@[simp] theorem toTerm_ofTerm (t : (paddedAlphabet A).Term) :
    (ofTerm t).toTerm = t := by
  induction t with
  | node f ts ih =>
      cases f with
      | none =>
          rw [ofTerm, toTerm]
          congr
          funext i
          exact i.elim0
      | some a =>
          rw [ofTerm, toTerm]
          congr
          funext i
          cases i using Fin.cases with
          | zero =>
              simpa using ih ⟨0, by simp [paddedAlphabet]⟩
          | succ i =>
              cases i using Fin.cases with
              | zero =>
                  simpa using ih ⟨1, by simp [paddedAlphabet]⟩
              | succ i =>
                  exact i.elim0

@[simp] theorem toTerm_map {B : Type u} (f : A → B) (t : BinTree A) :
    (t.map f).toTerm = t.toTerm.map (paddedMapHom f) := by
  induction t with
  | nil =>
      rw [map_nil, toTerm, toTerm, RankedAlphabet.Term.map_node]
      congr
      funext i
      exact i.elim0
  | node a l r ihl ihr =>
      rw [map_node, toTerm, toTerm, RankedAlphabet.Term.map_node]
      congr
      funext i
      cases i using Fin.cases with
      | zero =>
          simp [ihl]
      | succ i =>
          cases i using Fin.cases with
          | zero =>
              simp [ihr]
          | succ i =>
              exact i.elim0

/-! ## Boolean tracks on positions -/

/-- The Boolean vector carried by a label with `n` monadic tracks. -/
abbrev TrackBits (n : ℕ) := Fin n → Bool

/-- Erase all Boolean tracks from a tracked binary tree. -/
def eraseTracks {n : ℕ} (t : BinTree (A × TrackBits n)) : BinTree A :=
  t.map Prod.fst

/-- The set of positions whose `i`-th Boolean track is on. -/
def trackSet {n : ℕ} (t : BinTree (A × TrackBits n)) (i : Fin n) : Set t.Pos :=
  {p | (t.labelAt p).2 i = true}

/-- Keep, permute, or duplicate Boolean tracks according to an index map. -/
def remapTracks {m n : ℕ} (ι : Fin m → Fin n)
    (t : BinTree (A × TrackBits n)) : BinTree (A × TrackBits m) :=
  t.map fun a => (a.1, fun i => a.2 (ι i))

/-- Remapping tracks does not change the base labeled tree. -/
@[simp] theorem eraseTracks_remapTracks {m n : ℕ} (ι : Fin m → Fin n)
    (t : BinTree (A × TrackBits n)) :
    eraseTracks (remapTracks ι t) = eraseTracks t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      change BinTree.node a.1
          (eraseTracks (remapTracks ι l))
          (eraseTracks (remapTracks ι r)) =
        BinTree.node a.1 (eraseTracks l) (eraseTracks r)
      rw [ihl, ihr]

/-- Track membership after remapping is the membership of the source track. -/
@[simp] theorem trackSet_remapTracks_iff {m n : ℕ} (ι : Fin m → Fin n)
    (t : BinTree (A × TrackBits n)) (i : Fin m) (p : t.Pos) :
    posEquivMap (fun a : A × TrackBits n => (a.1, fun i => a.2 (ι i))) t p ∈
        trackSet (remapTracks ι t) i ↔
      p ∈ trackSet t (ι i) := by
  simp [trackSet, remapTracks]

/-- Add `n` Boolean tracks to a tree from `n` distinguished position sets. -/
noncomputable def withTracks {n : ℕ} :
    (t : BinTree A) → (Fin n → Set t.Pos) → BinTree (A × TrackBits n)
  | .nil, _ => .nil
  | .node a l r, tracks =>
      .node
        (a, fun i =>
          haveI : Decidable
              ((none : Option (l.Pos ⊕ r.Pos)) ∈ tracks i) :=
            Classical.propDecidable _
          decide ((none : Option (l.Pos ⊕ r.Pos)) ∈ tracks i))
        (withTracks l fun i =>
          {p | (some (.inl p) : Option (l.Pos ⊕ r.Pos)) ∈ tracks i})
        (withTracks r fun i =>
          {p | (some (.inr p) : Option (l.Pos ⊕ r.Pos)) ∈ tracks i})

/-- Adding Boolean tracks preserves the position type, up to the canonical
recursive equivalence. -/
noncomputable def posEquivWithTracks {n : ℕ} :
    (t : BinTree A) → (tracks : Fin n → Set t.Pos) →
      t.Pos ≃ (withTracks t tracks).Pos
  | .nil, _ =>
      { toFun := fun p => p.elim
        invFun := fun p => p.elim
        left_inv := fun p => p.elim
        right_inv := fun p => p.elim }
  | .node _ l r, tracks =>
      let el := posEquivWithTracks l fun i =>
        {p | (some (.inl p) : Option (l.Pos ⊕ r.Pos)) ∈ tracks i}
      let er := posEquivWithTracks r fun i =>
        {p | (some (.inr p) : Option (l.Pos ⊕ r.Pos)) ∈ tracks i}
      { toFun := fun
          | none => none
          | some (.inl p) => some (.inl (el p))
          | some (.inr p) => some (.inr (er p))
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

@[simp] theorem posEquivWithTracks_node_root {n : ℕ}
    (a : A) (l r : BinTree A)
    (tracks : Fin n → Set (BinTree.node a l r).Pos) :
    posEquivWithTracks (BinTree.node a l r) tracks none = none :=
  rfl

@[simp] theorem posEquivWithTracks_node_left {n : ℕ}
    (a : A) (l r : BinTree A)
    (tracks : Fin n → Set (BinTree.node a l r).Pos)
    (p : l.Pos) :
    posEquivWithTracks (BinTree.node a l r) tracks (some (.inl p)) =
      some (.inl
        ((posEquivWithTracks l fun i =>
          {p | (some (.inl p) : Option (l.Pos ⊕ r.Pos)) ∈ tracks i}) p)) :=
  rfl

@[simp] theorem posEquivWithTracks_node_right {n : ℕ}
    (a : A) (l r : BinTree A)
    (tracks : Fin n → Set (BinTree.node a l r).Pos)
    (p : r.Pos) :
    posEquivWithTracks (BinTree.node a l r) tracks (some (.inr p)) =
      some (.inr
        ((posEquivWithTracks r fun i =>
          {p | (some (.inr p) : Option (l.Pos ⊕ r.Pos)) ∈ tracks i}) p)) :=
  rfl

theorem isRootPos_withTracks_iff {n : ℕ}
    (t : BinTree A) (tracks : Fin n → Set t.Pos) (p : t.Pos) :
    (withTracks t tracks).IsRootPos (posEquivWithTracks t tracks p) ↔
      t.IsRootPos p := by
  induction t with
  | nil => exact p.elim
  | node a l r ihl ihr =>
      cases p with
      | none =>
          simp [IsRootPos, withTracks, posEquivWithTracks]
      | some q =>
          cases q with
          | inl p =>
              simp [IsRootPos, withTracks, posEquivWithTracks]
          | inr p =>
              simp [IsRootPos, withTracks, posEquivWithTracks]

theorem childRel_withTracks_iff {n : ℕ}
    (t : BinTree A) (tracks : Fin n → Set t.Pos) (b : Bool)
    (p q : t.Pos) :
    (withTracks t tracks).childRel b
        (posEquivWithTracks t tracks p)
        (posEquivWithTracks t tracks q) ↔
      t.childRel b p q := by
  induction t with
  | nil => exact p.elim
  | node a l r ihl ihr =>
      cases p with
      | none =>
          cases q with
          | none => rfl
          | some q' =>
              cases q' with
              | inl q =>
                  change
                    (b = false ∧
                        (withTracks l fun i =>
                          {p | (some (.inl p) : Option (l.Pos ⊕ r.Pos)) ∈
                            tracks i}).IsRootPos
                          ((posEquivWithTracks l fun i =>
                            {p | (some (.inl p) :
                              Option (l.Pos ⊕ r.Pos)) ∈ tracks i}) q)) ↔
                      (b = false ∧ l.IsRootPos q)
                  exact and_congr_right fun _ =>
                    isRootPos_withTracks_iff l (fun i =>
                      {p | (some (.inl p) :
                        Option (l.Pos ⊕ r.Pos)) ∈ tracks i}) q
              | inr q =>
                  change
                    (b = true ∧
                        (withTracks r fun i =>
                          {p | (some (.inr p) : Option (l.Pos ⊕ r.Pos)) ∈
                            tracks i}).IsRootPos
                          ((posEquivWithTracks r fun i =>
                            {p | (some (.inr p) :
                              Option (l.Pos ⊕ r.Pos)) ∈ tracks i}) q)) ↔
                      (b = true ∧ r.IsRootPos q)
                  exact and_congr_right fun _ =>
                    isRootPos_withTracks_iff r (fun i =>
                      {p | (some (.inr p) :
                        Option (l.Pos ⊕ r.Pos)) ∈ tracks i}) q
      | some p' =>
          cases p' with
          | inl p =>
              cases q with
              | none => rfl
              | some q' =>
                  cases q' with
                  | inl q =>
                      exact ihl (fun i =>
                        {p | (some (.inl p) :
                          Option (l.Pos ⊕ r.Pos)) ∈ tracks i}) p q
                  | inr q => rfl
          | inr p =>
              cases q with
              | none => rfl
              | some q' =>
                  cases q' with
                  | inl q => rfl
                  | inr q =>
                      exact ihr (fun i =>
                        {p | (some (.inr p) :
                          Option (l.Pos ⊕ r.Pos)) ∈ tracks i}) p q

@[simp] theorem fst_labelAt_withTracks {n : ℕ}
    (t : BinTree A) (tracks : Fin n → Set t.Pos) (p : t.Pos) :
    ((withTracks t tracks).labelAt (posEquivWithTracks t tracks p)).1 =
      t.labelAt p := by
  induction t with
  | nil => exact p.elim
  | node a l r ihl ihr =>
      cases p with
      | none => rfl
      | some q =>
          cases q with
          | inl p => simpa using ihl (fun i =>
              {p | (some (.inl p) : Option (l.Pos ⊕ r.Pos)) ∈ tracks i}) p
          | inr p => simpa using ihr (fun i =>
              {p | (some (.inr p) : Option (l.Pos ⊕ r.Pos)) ∈ tracks i}) p

@[simp] theorem trackSet_withTracks_iff {n : ℕ}
    (t : BinTree A) (tracks : Fin n → Set t.Pos) (i : Fin n) (p : t.Pos) :
    posEquivWithTracks t tracks p ∈ trackSet (withTracks t tracks) i ↔
      p ∈ tracks i := by
  induction t with
  | nil => exact p.elim
  | node a l r ihl ihr =>
      cases p with
      | none =>
          let P : Prop := (none : Option (l.Pos ⊕ r.Pos)) ∈ tracks i
          change (@decide P (Classical.propDecidable P) = true ↔ P)
          exact Iff.of_eq (@decide_eq_true_eq P (Classical.propDecidable P))
      | some q =>
          cases q with
          | inl p =>
              simpa [trackSet, withTracks] using ihl (fun i =>
                {p | (some (.inl p) : Option (l.Pos ⊕ r.Pos)) ∈ tracks i}) p
          | inr p =>
              simpa [trackSet, withTracks] using ihr (fun i =>
                {p | (some (.inr p) : Option (l.Pos ⊕ r.Pos)) ∈ tracks i}) p

@[simp] theorem eraseTracks_withTracks {n : ℕ}
    (t : BinTree A) (tracks : Fin n → Set t.Pos) :
    eraseTracks (withTracks t tracks) = t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      let leftTracks : Fin n → Set l.Pos := fun i =>
        {p | (some (.inl p) : Option (l.Pos ⊕ r.Pos)) ∈ tracks i}
      let rightTracks : Fin n → Set r.Pos := fun i =>
        {p | (some (.inr p) : Option (l.Pos ⊕ r.Pos)) ∈ tracks i}
      change BinTree.node a
          (eraseTracks (withTracks l leftTracks))
          (eraseTracks (withTracks r rightTracks)) =
        BinTree.node a l r
      simp [ihl leftTracks, ihr rightTracks]

@[simp] theorem withTracks_empty {n : ℕ} (t : BinTree A) :
    withTracks t (fun _ => (∅ : Set t.Pos)) =
      t.map (fun a => (a, fun _ : Fin n => false)) := by
  induction t with
  | nil =>
      rfl
  | node a l r ihl ihr =>
      change
        BinTree.node
            (a,
              fun i =>
                haveI : Decidable
                    ((none : Option (l.Pos ⊕ r.Pos)) ∈
                      (∅ : Set (Option (l.Pos ⊕ r.Pos)))) :=
                  Classical.propDecidable _
                decide
                  ((none : Option (l.Pos ⊕ r.Pos)) ∈
                    (∅ : Set (Option (l.Pos ⊕ r.Pos)))))
            (withTracks l (fun _ => (∅ : Set l.Pos)))
            (withTracks r (fun _ => (∅ : Set r.Pos))) =
          BinTree.node (a, fun _ : Fin n => false)
            (l.map fun a => (a, fun _ : Fin n => false))
            (r.map fun a => (a, fun _ : Fin n => false))
      simp [ihl, ihr]

/-- Erasing Boolean tracks is an arity-preserving homomorphism of padded
ranked alphabets. -/
def eraseTracksHom (A : Type u) (n : ℕ) :
    (paddedAlphabet (A × TrackBits n)).Hom (paddedAlphabet A) :=
  paddedMapHom Prod.fst

/-- Remapping Boolean tracks as an arity-preserving homomorphism of padded
ranked alphabets. -/
def remapTracksHom (A : Type u) {m n : ℕ} (ι : Fin m → Fin n) :
    (paddedAlphabet (A × TrackBits n)).Hom
      (paddedAlphabet (A × TrackBits m)) :=
  paddedMapHom fun a => (a.1, fun i => a.2 (ι i))

@[simp] theorem toTerm_eraseTracks {n : ℕ} (t : BinTree (A × TrackBits n)) :
    t.eraseTracks.toTerm = t.toTerm.map (eraseTracksHom A n) := by
  simp [eraseTracks, eraseTracksHom]

@[simp] theorem toTerm_remapTracks {m n : ℕ} (ι : Fin m → Fin n)
    (t : BinTree (A × TrackBits n)) :
    (remapTracks ι t).toTerm = t.toTerm.map (remapTracksHom A ι) := by
  simp [remapTracks, remapTracksHom]

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

theorem remapTracks_eq_of_toTerm_map_eq {m n : ℕ} (ι : Fin m → Fin n)
    (s : BinTree (A × TrackBits n)) (t : BinTree (A × TrackBits m))
    (h : s.toTerm.map (remapTracksHom A ι) = t.toTerm) :
    remapTracks ι s = t := by
  apply toTerm_injective
  rw [toTerm_remapTracks, h]

theorem eraseTracks_eq_of_remapTracks_eq {m n : ℕ} (ι : Fin m → Fin n)
    {s : BinTree (A × TrackBits n)} {t : BinTree (A × TrackBits m)}
    (h : remapTracks ι s = t) :
    s.eraseTracks = t.eraseTracks := by
  have h' := congrArg eraseTracks h
  rwa [eraseTracks_remapTracks] at h'

end BinTree
