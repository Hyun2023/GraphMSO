import GraphMSO.treeLanguage.syntax

/-!
# Executable tree-MSO formulas

This file gives the executable counterpart of `GraphMSO.TreeLanguage.Formula`.
The logical syntax is unchanged, but unary and binary label predicates return
`Bool` instead of being arbitrary `Set`-valued predicates.  Consequently a
compiler may inspect a label atom without invoking classical decidability.

`ExecFormula.toFormula` forgets this computational presentation and interprets
a Boolean predicate by the set on which it returns `true`.
-/

namespace GraphMSO.Executable

universe u

open GraphMSO.TreeLanguage

/-- Executable MSO syntax over labeled trees.

This mirrors `GraphMSO.TreeLanguage.Formula` constructor for constructor.  Only
the two label atoms differ: their predicates are Boolean-valued functions. -/
inductive ExecFormula (A : Type u) : Type u where
  | false_ : ExecFormula A
  | equal : FOVar -> FOVar -> ExecFormula A
  | parent : FOVar -> FOVar -> ExecFormula A
  | labelMem : (A -> Bool) -> FOVar -> ExecFormula A
  | labelMem₂ : (A -> A -> Bool) -> FOVar -> FOVar -> ExecFormula A
  | inSet : FOVar -> SOVar -> ExecFormula A
  | neg : ExecFormula A -> ExecFormula A
  | conj : ExecFormula A -> ExecFormula A -> ExecFormula A
  | disj : ExecFormula A -> ExecFormula A -> ExecFormula A
  | impl : ExecFormula A -> ExecFormula A -> ExecFormula A
  | biimpl : ExecFormula A -> ExecFormula A -> ExecFormula A
  | existsFO : FOVar -> ExecFormula A -> ExecFormula A
  | forallFO : FOVar -> ExecFormula A -> ExecFormula A
  | existsSO : SOVar -> ExecFormula A -> ExecFormula A
  | forallSO : SOVar -> ExecFormula A -> ExecFormula A

namespace ExecFormula

variable {A : Type u}

/-- Interpret Boolean label predicates as ordinary set predicates. -/
def toFormula : ExecFormula A -> TreeLanguage.Formula A
  | false_ => .false_
  | equal x y => .equal x y
  | parent x y => .parent x y
  | labelMem p x => .labelMem {a | p a = true} x
  | labelMem₂ r x y => .labelMem₂ {q | r q.1 q.2 = true} x y
  | inSet x X => .inSet x X
  | neg φ => .neg φ.toFormula
  | conj φ ψ => .conj φ.toFormula ψ.toFormula
  | disj φ ψ => .disj φ.toFormula ψ.toFormula
  | impl φ ψ => .impl φ.toFormula ψ.toFormula
  | biimpl φ ψ => .biimpl φ.toFormula ψ.toFormula
  | existsFO x φ => .existsFO x φ.toFormula
  | forallFO x φ => .forallFO x φ.toFormula
  | existsSO X φ => .existsSO X φ.toFormula
  | forallSO X φ => .forallSO X φ.toFormula

@[simp] theorem toFormula_false_ : (false_ : ExecFormula A).toFormula = .false_ := rfl

@[simp] theorem toFormula_equal (x y : FOVar) :
    (equal x y : ExecFormula A).toFormula = .equal x y :=
  rfl

@[simp] theorem toFormula_parent (x y : FOVar) :
    (parent x y : ExecFormula A).toFormula = .parent x y :=
  rfl

@[simp] theorem toFormula_labelMem (p : A -> Bool) (x : FOVar) :
    (labelMem p x).toFormula = .labelMem {a | p a = true} x :=
  rfl

@[simp] theorem toFormula_labelMem₂ (r : A -> A -> Bool) (x y : FOVar) :
    (labelMem₂ r x y).toFormula = .labelMem₂ {q | r q.1 q.2 = true} x y :=
  rfl

@[simp] theorem toFormula_inSet (x : FOVar) (X : SOVar) :
    (inSet x X : ExecFormula A).toFormula = .inSet x X :=
  rfl

@[simp] theorem toFormula_neg (φ : ExecFormula A) :
    (neg φ).toFormula = .neg φ.toFormula :=
  rfl

@[simp] theorem toFormula_conj (φ ψ : ExecFormula A) :
    (conj φ ψ).toFormula = .conj φ.toFormula ψ.toFormula :=
  rfl

@[simp] theorem toFormula_disj (φ ψ : ExecFormula A) :
    (disj φ ψ).toFormula = .disj φ.toFormula ψ.toFormula :=
  rfl

@[simp] theorem toFormula_impl (φ ψ : ExecFormula A) :
    (impl φ ψ).toFormula = .impl φ.toFormula ψ.toFormula :=
  rfl

@[simp] theorem toFormula_biimpl (φ ψ : ExecFormula A) :
    (biimpl φ ψ).toFormula = .biimpl φ.toFormula ψ.toFormula :=
  rfl

@[simp] theorem toFormula_existsFO (x : FOVar) (φ : ExecFormula A) :
    (existsFO x φ).toFormula = .existsFO x φ.toFormula :=
  rfl

@[simp] theorem toFormula_forallFO (x : FOVar) (φ : ExecFormula A) :
    (forallFO x φ).toFormula = .forallFO x φ.toFormula :=
  rfl

@[simp] theorem toFormula_existsSO (X : SOVar) (φ : ExecFormula A) :
    (existsSO X φ).toFormula = .existsSO X φ.toFormula :=
  rfl

@[simp] theorem toFormula_forallSO (X : SOVar) (φ : ExecFormula A) :
    (forallSO X φ).toFormula = .forallSO X φ.toFormula :=
  rfl

/-! ## Executable derived formulas -/

/-- Truth, defined from falsity. -/
def true_ : ExecFormula A :=
  neg false_

/-- `x` is the root: it has no parent. -/
def root_ (x : FOVar) : ExecFormula A :=
  neg (existsFO (x + 1) (parent (x + 1) x))

/-- `Y ⊆ X`, with bound first-order variable `0`. -/
def subset (Y X : SOVar) : ExecFormula A :=
  forallFO 0 (impl (inSet 0 Y) (inSet 0 X))

/-- Extensional equality of two set variables. -/
def setEq (X Y : SOVar) : ExecFormula A :=
  conj (subset X Y) (subset Y X)

/-- `X = ∅`. -/
def empty (X : SOVar) : ExecFormula A :=
  forallFO 0 (neg (inSet 0 X))

/-- `X ≠ ∅`. -/
def nonempty (X : SOVar) : ExecFormula A :=
  existsFO 0 (inSet 0 X)

/-- `x` and `y` are joined by a tree edge in either orientation. -/
def adjTree (x y : FOVar) : ExecFormula A :=
  disj (parent x y) (parent y x)

/-- `X` is nonempty and connected in the underlying tree. -/
def conn (X : SOVar) : ExecFormula A :=
  conj (nonempty X)
    (forallSO (X + 1)
      (impl
        (conj (subset (X + 1) X)
          (conj (nonempty (X + 1))
            (existsFO 0 (conj (inSet 0 X) (neg (inSet 0 (X + 1)))))))
        (existsFO 0 (existsFO 1
          (conj (inSet 0 (X + 1))
            (conj (inSet 1 X)
              (conj (neg (inSet 1 (X + 1)))
                (adjTree 0 1))))))))

/-- `x` is the topmost node of the connected set `X`. -/
def top (x : FOVar) (X : SOVar) : ExecFormula A :=
  conj (inSet x X)
    (conj (conn X)
      (disj (root_ x)
        (existsFO (x + 1)
          (conj (parent (x + 1) x) (neg (inSet (x + 1) X))))))

/-- `x` is outside `X` and its parent lies in `X`. -/
def dangle (x : FOVar) (X : SOVar) : ExecFormula A :=
  conj (neg (inSet x X))
    (existsFO (x + 1) (conj (parent (x + 1) x) (inSet (x + 1) X)))

/-- Quantify a list of set variables existentially, in order. -/
def existsSOList : List SOVar -> ExecFormula A -> ExecFormula A
  | [], φ => φ
  | X :: l, φ => existsSO X (existsSOList l φ)

/-- Quantify a list of set variables universally, in order. -/
def forallSOList : List SOVar -> ExecFormula A -> ExecFormula A
  | [], φ => φ
  | X :: l, φ => forallSO X (forallSOList l φ)

/-- Finite conjunction of a list of formulas. -/
def conjList : List (ExecFormula A) -> ExecFormula A
  | [] => true_
  | φ :: l => conj φ (conjList l)

/-- Finite disjunction of a list of formulas. -/
def disjList : List (ExecFormula A) -> ExecFormula A
  | [] => false_
  | φ :: l => disj φ (disjList l)

/-- Executable form of the legality sentence for labeled encodings. -/
def legal (rootLetter : A -> Bool) (compatible : A -> A -> Bool) : ExecFormula A :=
  conj
    (forallFO 0 (impl (root_ 0) (labelMem rootLetter 0)))
    (forallFO 0 (disj (root_ 0)
      (existsFO 1 (conj (parent 1 0) (labelMem₂ compatible 0 1)))))

/-- Executable defining-pair recognition formula. -/
def definingPair (hasVertex rootContains : A -> Bool) (Z : SOVar) : ExecFormula A :=
  conj (conn Z)
    (conj (forallFO 0 (impl (inSet 0 Z) (labelMem hasVertex 0)))
      (conj (forallFO 0 (impl (conj (inSet 0 Z) (neg (top 0 Z)))
          (labelMem rootContains 0)))
        (conj (forallFO 0 (impl (top 0 Z) (neg (labelMem rootContains 0))))
          (forallFO 0 (impl (dangle 0 Z) (neg (labelMem rootContains 0)))))))

/-- Executable vertex-recognition formula for a tuple of color coordinates. -/
def vtxTuple {k : Nat} (hasVertex rootContains : Fin k -> A -> Bool)
    (Zs : Fin k -> SOVar) : ExecFormula A :=
  disjList ((List.finRange k).map fun i =>
    conj (definingPair (hasVertex i) (rootContains i) (Zs i))
      (conjList (((List.finRange k).filter (fun j => j ≠ i)).map fun j =>
        empty (Zs j))))

/-- Executable set-recognition formula for a tuple of color coordinates. -/
def setTuple {k : Nat} (hasVertex rootContains : Fin k -> A -> Bool)
    (Zs : Fin k -> SOVar) : ExecFormula A :=
  conjList ((List.finRange k).map fun i =>
    forallFO 0 (impl (inSet 0 (Zs i))
      (existsSO (Zs i + 1)
        (conj (subset (Zs i + 1) (Zs i))
          (conj (inSet 0 (Zs i + 1))
            (definingPair (hasVertex i) (rootContains i) (Zs i + 1)))))))

/-- Executable adjacency formula for two vertex tuples. -/
def adjTuple {k : Nat} (hasVertex rootContains : Fin k -> A -> Bool)
    (adjacent : Fin k -> Fin k -> A -> Bool) (Xs Ys : Fin k -> SOVar) : ExecFormula A :=
  conj (vtxTuple hasVertex rootContains Xs)
    (conj (vtxTuple hasVertex rootContains Ys)
      (disjList ((List.finRange k).map fun i =>
        disjList ((List.finRange k).map fun j =>
          existsFO 0 (conj (inSet 0 (Xs i))
            (conj (inSet 0 (Ys j)) (labelMem (adjacent i j) 0)))))))

/-- Executable unary-predicate formula for a vertex tuple. -/
def predTuple {k : Nat} (hasVertex rootContains : Fin k -> A -> Bool)
    (tagged : Fin k -> A -> Bool) (Xs : Fin k -> SOVar) : ExecFormula A :=
  conj (vtxTuple hasVertex rootContains Xs)
    (disjList ((List.finRange k).map fun i =>
      existsFO 0 (conj (inSet 0 (Xs i)) (labelMem (tagged i) 0))))

/-- Executable equality formula for two vertex tuples. -/
def eqTuple {k : Nat} (hasVertex rootContains : Fin k -> A -> Bool)
    (Xs Ys : Fin k -> SOVar) : ExecFormula A :=
  conj (vtxTuple hasVertex rootContains Xs)
    (conj (vtxTuple hasVertex rootContains Ys)
      (conjList ((List.finRange k).map fun i => setEq (Xs i) (Ys i))))

/-- Executable containment formula for a vertex tuple and a set tuple. -/
def contTuple {k : Nat} (hasVertex rootContains : Fin k -> A -> Bool)
    (Xs Ys : Fin k -> SOVar) : ExecFormula A :=
  conj (vtxTuple hasVertex rootContains Xs)
    (conj (setTuple hasVertex rootContains Ys)
      (disjList ((List.finRange k).map fun i =>
        conj (nonempty (Xs i)) (subset (Xs i) (Ys i)))))

/-! ## Refinement of derived formulas -/

@[simp] theorem toFormula_true_ : (true_ : ExecFormula A).toFormula =
    TreeLanguage.Formula.true_ :=
  rfl

@[simp] theorem toFormula_root_ (x : FOVar) :
    (root_ x : ExecFormula A).toFormula = TreeLanguage.Formula.root_ x :=
  rfl

@[simp] theorem toFormula_subset (Y X : SOVar) :
    (subset Y X : ExecFormula A).toFormula = TreeLanguage.Formula.subset Y X :=
  rfl

@[simp] theorem toFormula_setEq (X Y : SOVar) :
    (setEq X Y : ExecFormula A).toFormula = TreeLanguage.Formula.setEq X Y :=
  rfl

@[simp] theorem toFormula_empty (X : SOVar) :
    (empty X : ExecFormula A).toFormula = TreeLanguage.Formula.empty X :=
  rfl

@[simp] theorem toFormula_nonempty (X : SOVar) :
    (nonempty X : ExecFormula A).toFormula = TreeLanguage.Formula.nonempty X :=
  rfl

@[simp] theorem toFormula_adjTree (x y : FOVar) :
    (adjTree x y : ExecFormula A).toFormula = TreeLanguage.Formula.adjTree x y :=
  rfl

@[simp] theorem toFormula_conn (X : SOVar) :
    (conn X : ExecFormula A).toFormula = TreeLanguage.Formula.conn X :=
  rfl

@[simp] theorem toFormula_top (x : FOVar) (X : SOVar) :
    (top x X : ExecFormula A).toFormula = TreeLanguage.Formula.top x X :=
  rfl

@[simp] theorem toFormula_dangle (x : FOVar) (X : SOVar) :
    (dangle x X : ExecFormula A).toFormula = TreeLanguage.Formula.dangle x X :=
  rfl

@[simp] theorem toFormula_existsSOList (xs : List SOVar) (φ : ExecFormula A) :
    (existsSOList xs φ).toFormula =
      TreeLanguage.Formula.existsSOList xs φ.toFormula := by
  induction xs with
  | nil => rfl
  | cons X xs ih => simp [existsSOList, TreeLanguage.Formula.existsSOList, ih]

@[simp] theorem toFormula_forallSOList (xs : List SOVar) (φ : ExecFormula A) :
    (forallSOList xs φ).toFormula =
      TreeLanguage.Formula.forallSOList xs φ.toFormula := by
  induction xs with
  | nil => rfl
  | cons X xs ih => simp [forallSOList, TreeLanguage.Formula.forallSOList, ih]

@[simp] theorem toFormula_conjList (formulas : List (ExecFormula A)) :
    (conjList formulas).toFormula =
      TreeLanguage.Formula.conjList (formulas.map toFormula) := by
  induction formulas with
  | nil => rfl
  | cons φ formulas ih => simp [conjList, TreeLanguage.Formula.conjList, ih]

@[simp] theorem toFormula_disjList (formulas : List (ExecFormula A)) :
    (disjList formulas).toFormula =
      TreeLanguage.Formula.disjList (formulas.map toFormula) := by
  induction formulas with
  | nil => rfl
  | cons φ formulas ih => simp [disjList, TreeLanguage.Formula.disjList, ih]

@[simp] theorem toFormula_legal (rootLetter : A -> Bool) (compatible : A -> A -> Bool) :
    (legal rootLetter compatible).toFormula =
      TreeLanguage.Formula.legal {a | rootLetter a = true}
        {q | compatible q.1 q.2 = true} :=
  rfl

@[simp] theorem toFormula_definingPair (hasVertex rootContains : A -> Bool) (Z : SOVar) :
    (definingPair hasVertex rootContains Z).toFormula =
      TreeLanguage.Formula.definingPair {a | hasVertex a = true}
        {a | rootContains a = true} Z :=
  rfl

@[simp] theorem toFormula_vtxTuple {k : Nat}
    (hasVertex rootContains : Fin k -> A -> Bool) (Zs : Fin k -> SOVar) :
    (vtxTuple hasVertex rootContains Zs).toFormula =
      TreeLanguage.Formula.vtxTuple (fun i => {a | hasVertex i a = true})
        (fun i => {a | rootContains i a = true}) Zs := by
  simp [vtxTuple, TreeLanguage.Formula.vtxTuple, Function.comp_def]

@[simp] theorem toFormula_setTuple {k : Nat}
    (hasVertex rootContains : Fin k -> A -> Bool) (Zs : Fin k -> SOVar) :
    (setTuple hasVertex rootContains Zs).toFormula =
      TreeLanguage.Formula.setTuple (fun i => {a | hasVertex i a = true})
        (fun i => {a | rootContains i a = true}) Zs := by
  simp [setTuple, TreeLanguage.Formula.setTuple, Function.comp_def]

@[simp] theorem toFormula_adjTuple {k : Nat}
    (hasVertex rootContains : Fin k -> A -> Bool)
    (adjacent : Fin k -> Fin k -> A -> Bool) (Xs Ys : Fin k -> SOVar) :
    (adjTuple hasVertex rootContains adjacent Xs Ys).toFormula =
      TreeLanguage.Formula.adjTuple (fun i => {a | hasVertex i a = true})
        (fun i => {a | rootContains i a = true})
        (fun i j => {a | adjacent i j a = true}) Xs Ys := by
  simp [adjTuple, TreeLanguage.Formula.adjTuple, Function.comp_def]

@[simp] theorem toFormula_predTuple {k : Nat}
    (hasVertex rootContains : Fin k -> A -> Bool) (tagged : Fin k -> A -> Bool)
    (Xs : Fin k -> SOVar) :
    (predTuple hasVertex rootContains tagged Xs).toFormula =
      TreeLanguage.Formula.predTuple (fun i => {a | hasVertex i a = true})
        (fun i => {a | rootContains i a = true})
        (fun i => {a | tagged i a = true}) Xs := by
  simp [predTuple, TreeLanguage.Formula.predTuple, Function.comp_def]

@[simp] theorem toFormula_eqTuple {k : Nat}
    (hasVertex rootContains : Fin k -> A -> Bool) (Xs Ys : Fin k -> SOVar) :
    (eqTuple hasVertex rootContains Xs Ys).toFormula =
      TreeLanguage.Formula.eqTuple (fun i => {a | hasVertex i a = true})
        (fun i => {a | rootContains i a = true}) Xs Ys := by
  simp [eqTuple, TreeLanguage.Formula.eqTuple, Function.comp_def]

@[simp] theorem toFormula_contTuple {k : Nat}
    (hasVertex rootContains : Fin k -> A -> Bool) (Xs Ys : Fin k -> SOVar) :
    (contTuple hasVertex rootContains Xs Ys).toFormula =
      TreeLanguage.Formula.contTuple (fun i => {a | hasVertex i a = true})
        (fun i => {a | rootContains i a = true}) Xs Ys := by
  simp [contTuple, TreeLanguage.Formula.contTuple, Function.comp_def]

end ExecFormula

end GraphMSO.Executable
