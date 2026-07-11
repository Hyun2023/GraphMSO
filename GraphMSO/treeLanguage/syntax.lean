import Mathlib.Data.Set.Basic

/-!
# MSO syntax over labeled trees

The tree-side language of the Courcelle translation.  Following the lecture
note, formulas speak about a labeled rooted tree through

* the parent relation (`parent y x`: `y` is the parent of `x`), and
* letter-class predicates.

Two simplifications relative to the note's presentation, both
semantics-preserving:

* The note's vocabulary has `child₁, child₂` and uses them only through the
  abbreviation `parent(y,x) = child₁(y,x) ∨ child₂(y,x)`; the translation
  layer takes `parent` as primitive.  The ordered child relations enter only
  when trees are handed to automata, where `parent` is first-order definable.
* The note's per-letter predicates `P_a` occur only in finite disjunctions
  `⋁_{a ∈ S} P_a(x)` over letter classes `S` (the classes `A_i`, `R_i`,
  `E_{ij}`, `Q_i`).  The atom `labelMem S x` asserts `ρ(x) ∈ S` directly, so
  each such disjunction is one atom; `P_a` itself is the singleton instance.

Bound variables of the derived formulas are chosen concretely (just above
the variables of the arguments); each semantic characterization in
`GraphMSO.treeLanguage.semantics` verifies the choice, so no general
capture-avoidance machinery is needed.
-/

namespace GraphMSO.TreeLanguage

universe u

/-- First-order variables range over tree nodes. -/
abbrev FOVar := Nat

/-- Monadic second-order variables range over sets of tree nodes. -/
abbrev SOVar := Nat

/-- MSO formulas over the tree vocabulary: parent, letter-class membership,
equality, and set membership.

`labelMem₂ R x y` constrains the pair of letters at `x` and `y` to lie in
`R`; over a finite alphabet it abbreviates the finite disjunction
`⋁_{(a,b) ∈ R} (P_a(x) ∧ P_b(y))`, which is how the compatibility relation
of the legality sentence appears in the lecture note. -/
inductive Formula (A : Type u) : Type u where
  | false_ : Formula A
  | equal : FOVar → FOVar → Formula A
  | parent : FOVar → FOVar → Formula A
  | labelMem : Set A → FOVar → Formula A
  | labelMem₂ : Set (A × A) → FOVar → FOVar → Formula A
  | inSet : FOVar → SOVar → Formula A
  | neg : Formula A → Formula A
  | conj : Formula A → Formula A → Formula A
  | disj : Formula A → Formula A → Formula A
  | impl : Formula A → Formula A → Formula A
  | biimpl : Formula A → Formula A → Formula A
  | existsFO : FOVar → Formula A → Formula A
  | forallFO : FOVar → Formula A → Formula A
  | existsSO : SOVar → Formula A → Formula A
  | forallSO : SOVar → Formula A → Formula A

namespace Formula

variable {A : Type u}

/-- Truth, defined from falsity. -/
def true_ : Formula A :=
  neg false_

/-- The letter predicate `P_a` of the lecture note: the label is exactly
`a`. -/
def labelIs (a : A) (x : FOVar) : Formula A :=
  labelMem {a} x

/-- `x` is the root: it has no parent.  The bound variable is `x + 1`. -/
def root_ (x : FOVar) : Formula A :=
  neg (existsFO (x + 1) (parent (x + 1) x))

/-- `Y ⊆ X`, with bound first-order variable `0`. -/
def subset (Y X : SOVar) : Formula A :=
  forallFO 0 (impl (inSet 0 Y) (inSet 0 X))

/-- Extensional equality of two set variables, with bound first-order
variable `0`. -/
def setEq (X Y : SOVar) : Formula A :=
  conj (subset X Y) (subset Y X)

/-- `X = ∅`, with bound first-order variable `0`. -/
def empty (X : SOVar) : Formula A :=
  forallFO 0 (neg (inSet 0 X))

/-- `X ≠ ∅`, with bound first-order variable `0`. -/
def nonempty (X : SOVar) : Formula A :=
  existsFO 0 (inSet 0 X)

/-- `x` and `y` are joined by a tree edge, in either orientation. -/
def adjTree (x y : FOVar) : Formula A :=
  disj (parent x y) (parent y x)

/--
`X` is nonempty and connected in the tree: every split of `X` into a nonempty
part `Y` and a nonempty rest has a tree edge across it.  The bound set
variable is `X + 1`; the bound first-order variables are `0` and `1`.
-/
def conn (X : SOVar) : Formula A :=
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

/-- `x` is the topmost node of the connected set `X`: it belongs to `X` and
its parent, if any, does not.  The bound variable is `x + 1`. -/
def top (x : FOVar) (X : SOVar) : Formula A :=
  conj (inSet x X)
    (conj (conn X)
      (disj (root_ x)
        (existsFO (x + 1)
          (conj (parent (x + 1) x) (neg (inSet (x + 1) X))))))

/-- `x` dangles from `X`: it lies outside `X` but its parent lies in `X`.
The bound variable is `x + 1`. -/
def dangle (x : FOVar) (X : SOVar) : Formula A :=
  conj (neg (inSet x X))
    (existsFO (x + 1) (conj (parent (x + 1) x) (inSet (x + 1) X)))

/-- Finite conjunction of a list of formulas. -/
def conjList : List (Formula A) → Formula A
  | [] => true_
  | φ :: l => conj φ (conjList l)

/-- Finite disjunction of a list of formulas. -/
def disjList : List (Formula A) → Formula A
  | [] => false_
  | φ :: l => disj φ (disjList l)

/--
The legality sentence, parameterized by the set `S` of letters allowed at the
root and the compatibility relation `R` on (child, parent) letter pairs: the
root letter lies in `S`, and every non-root node's letter is compatible with
its parent's.  The bound variables are `0` and `1`.
-/
def legal (S : Set A) (R : Set (A × A)) : Formula A :=
  conj
    (forallFO 0 (impl (root_ 0) (labelMem S 0)))
    (forallFO 0 (disj (root_ 0)
      (existsFO 1 (conj (parent 1 0) (labelMem₂ R 0 1)))))

/--
The defining-pair recognition formula `phi_vtx_i` of the lecture note,
parameterized by the letter classes `SA` (letters carrying the color) and
`SR` (letters whose root carries the color): `Z` is connected, all its
letters lie in `SA`, non-top members lie in `SR`, and the top member and all
dangling children do not.  The legality conjunct of the note is omitted: over
an encoding it is ambient, and in the final tree sentence it is conjoined
once at top level.  The bound first-order variables are `0` and `1`.
-/
def definingPair (SA SR : Set A) (Z : SOVar) : Formula A :=
  conj (conn Z)
    (conj (forallFO 0 (impl (inSet 0 Z) (labelMem SA 0)))
      (conj (forallFO 0 (impl (conj (inSet 0 Z) (neg (top 0 Z)))
          (labelMem SR 0)))
        (conj (forallFO 0 (impl (top 0 Z) (neg (labelMem SR 0))))
          (forallFO 0 (impl (dangle 0 Z) (neg (labelMem SR 0)))))))

/--
The vertex-recognition formula `phi_vtx` of the lecture note: some coordinate
of the tuple `Zs` is a defining pair for its color class, and every other
coordinate is empty.
-/
def vtxTuple {k : ℕ} (SA SR : Fin k → Set A) (Zs : Fin k → SOVar) :
    Formula A :=
  disjList ((List.finRange k).map fun i =>
    conj (definingPair (SA i) (SR i) (Zs i))
      (conjList (((List.finRange k).filter (fun j => j ≠ i)).map fun j =>
        Formula.empty (Zs j))))

/--
The set-recognition formula `phi_set` of the lecture note: every node of
every coordinate is covered by a defining pair contained in that coordinate.
The bound set variable of coordinate `i` is `Zs i + 1`; the bound first-order
variable is `0`.
-/
def setTuple {k : ℕ} (SA SR : Fin k → Set A) (Zs : Fin k → SOVar) :
    Formula A :=
  conjList ((List.finRange k).map fun i =>
    forallFO 0 (impl (inSet 0 (Zs i))
      (existsSO (Zs i + 1)
        (conj (subset (Zs i + 1) (Zs i))
          (conj (inSet 0 (Zs i + 1))
            (definingPair (SA i) (SR i) (Zs i + 1)))))))

/--
The adjacency formula `phi_adj` of the lecture note: both tuples define
vertices, and some node lies in an `i`-coordinate of the first and a
`j`-coordinate of the second while its letter records an edge between the
colors `i` and `j` (the class `SE i j`).  The bound first-order variable is
`0`.
-/
def adjTuple {k : ℕ} (SA SR : Fin k → Set A) (SE : Fin k → Fin k → Set A)
    (Xs Ys : Fin k → SOVar) : Formula A :=
  conj (vtxTuple SA SR Xs)
    (conj (vtxTuple SA SR Ys)
      (disjList ((List.finRange k).map fun i =>
        disjList ((List.finRange k).map fun j =>
          existsFO 0 (conj (inSet 0 (Xs i))
            (conj (inSet 0 (Ys j)) (labelMem (SE i j) 0)))))))

/--
The unary-predicate formula `phi_Q` of the lecture note: the tuple defines a
vertex, and some node of some coordinate carries the predicate tag for that
color (the class `SQ i`).  The bound first-order variable is `0`.
-/
def predTuple {k : ℕ} (SA SR : Fin k → Set A) (SQ : Fin k → Set A)
    (Xs : Fin k → SOVar) : Formula A :=
  conj (vtxTuple SA SR Xs)
    (disjList ((List.finRange k).map fun i =>
      existsFO 0 (conj (inSet 0 (Xs i)) (labelMem (SQ i) 0))))

/--
The equality formula `phi_eq` of the lecture note: both tuples define
vertices and agree coordinatewise.
-/
def eqTuple {k : ℕ} (SA SR : Fin k → Set A) (Xs Ys : Fin k → SOVar) :
    Formula A :=
  conj (vtxTuple SA SR Xs)
    (conj (vtxTuple SA SR Ys)
      (conjList ((List.finRange k).map fun i => setEq (Xs i) (Ys i))))

/--
The containment formula `phi_cont` of the lecture note: the first tuple
defines a vertex, the second defines a vertex set, and the vertex's nonempty
coordinate is contained in the corresponding coordinate of the set.
-/
def contTuple {k : ℕ} (SA SR : Fin k → Set A) (Xs Ys : Fin k → SOVar) :
    Formula A :=
  conj (vtxTuple SA SR Xs)
    (conj (setTuple SA SR Ys)
      (disjList ((List.finRange k).map fun i =>
        conj (Formula.nonempty (Xs i)) (subset (Xs i) (Ys i)))))

end Formula

end GraphMSO.TreeLanguage
