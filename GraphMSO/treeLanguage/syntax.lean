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
equality, and set membership. -/
inductive Formula (A : Type u) : Type u where
  | false_ : Formula A
  | equal : FOVar → FOVar → Formula A
  | parent : FOVar → FOVar → Formula A
  | labelMem : Set A → FOVar → Formula A
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

end Formula

end GraphMSO.TreeLanguage
