# Phase 7: Verified Executable MSO Model Checking

This document explains the executable part of the Phase 7 development.  It is
intended as a guide to the code rather than a replacement for the mathematical
proofs in the Lean files.

The implementation takes:

- a finite Boolean presentation of a `tau_P` graph,
- an empty-rooted constructor-coded nice tree decomposition,
- a coloring that is injective inside every bag, and
- a graph-MSO formula,

and computes a `Bool`.  For closed formulas and certified inputs,
`checkColored_eq_true_iff` proves that this Boolean answer is `true` exactly
when the original graph satisfies the formula.

The full project build and the four maintained `#guard` examples were verified
on 2026-07-14.

## 1. Scope

Phase 7 implements MSO1 model checking once a suitable nice decomposition is
already available.  It does not currently:

- convert an arbitrary tree decomposition into a nice one,
- construct a width-sized bag coloring automatically,
- assemble the end-to-end executable MSO2 checker using the existing
  incidence-graph reduction, or
- prove that the actual Lean VM runtime is `3 * n + 2`.

The first omission is deliberate.  Nice normalization will be needed later
when the decomposition of an incidence graph is passed to this checker.

## 2. Thirty-second overview

The computational path is:

```text
Boolean graph X                 graph formula theta
      |                               |
      | encode                        | legalTranslate
      v                               v
BinTree (ExecSigmaLetter P omega)   ExecFormula
                 \                   /
                  \    checkTree    /
                   v               v
                         Bool
```

At the top level, the definition is essentially:

```lean
checkCode X tree color theta =
  checkTree (legalTranslate omega theta) (encode X color tree)
```

There are two parallel refinements behind its correctness:

```text
encode X color T.tree
  -- map ExecSigmaLetter.decode -->
T.orderedEncode X.toMath.pred color hcolor

(legalTranslate omega theta).toFormula
  =
(proof-facing legality and translation).comapLabels
  ExecSigmaLetter.decode
```

The executable automaton compiler is separately certified against the existing
proof-facing `TrackLanguage` development.

## 3. Notation and input contract

| Name | Lean representation | Meaning |
|---|---|---|
| `P` | `[Fintype P] [DecidableEq P]` | Unary predicate symbols of `tau_P` |
| `V` | a vertex type | Vertices of the input graph |
| `omega` | `Nat` | Colors are elements of `Fin (omega + 1)` |
| executable graph | `Executable.TauPGraph P V` | Boolean adjacency and predicate oracles |
| nice code | `InductiveNiceTree V rootBag` | A tree built from leaf, introduce, forget, and join |
| certified decomposition | `InductiveNiceTreeDecomposition` | A nice code plus its realization as a mathematical decomposition |
| bag coloring | `IsBagColoring` | The coloring is injective inside every bag |
| track | `TrackBits n` | An `n`-tuple of Boolean node markers |

The executable interfaces require `[Fintype P] [DecidableEq P]`.  For vertices,
`checkCode` only needs `[DecidableEq V]`, while the certified `checkColored`
interface needs `[Fintype V] [DecidableEq V]`.

The graph-level correctness theorem additionally assumes:

```lean
theta.freeFO = ∅
theta.freeSO = ∅
```

Thus `theta` is a sentence.  The evaluator itself can be run on an open
formula, but `checkColored_eq_true_iff` is intentionally stated for closed
graph formulas.

## 4. The two-layer design

The project already had a proof-facing development using `Prop`, `Set`, and
abstract tree automata.  Phase 7 does not duplicate those mathematical proofs.
Instead, each new executable object has a map back to the old object.

| Executable layer | Proof-facing layer | Refinement map or theorem |
|---|---|---|
| Boolean `TauPGraph` | `_root_.τPGraph` | `TauPGraph.toMath` |
| `ExecSigmaLetter` | `SigmaLetter` | `ExecSigmaLetter.decode` |
| `ExecFormula` | `TreeLanguage.Formula` | `ExecFormula.toFormula` |
| `ExecTreeAutomaton` | `TreeAutomaton` | `ExecTreeAutomaton.toTreeAutomaton` |
| direct `encode` | `orderedEncode` | `encode_map_decode` |
| Boolean tree acceptance | tree semantics | `checkTree_eq_true_iff` |

This is the main architectural idea.  Computation is performed in the left
column, while correctness is inherited from the established theory in the
right column.

## 5. Public entry points

The public functions are in
[`GraphMSO/Executable/modelCheck.lean`](../GraphMSO/Executable/modelCheck.lean).

### 5.1 `checkCode`

```lean
def checkCode [Fintype P] [DecidableEq P] [DecidableEq V]
    (X : TauPGraph P V)
    (tree : InductiveNiceTree V ∅)
    (color : V → Fin (omega + 1))
    (theta : Language.Formula P) : Bool
```

This is the lowest graph-level execution interface.  It follows the raw
constructor tree directly and is convenient for `#eval` and small examples.
It does not require a decomposition realization or a coloring proof.

The `InductiveNiceTree` type already enforces the local leaf, introduce,
forget, and join invariants.  What `checkCode` lacks is a realization proving
that this code is a decomposition of `X.toMath.G`, together with a proof that
`color` is a bag coloring.  Without those links, no graph-level correctness
theorem applies.

### 5.2 `checkColored`

```lean
def checkColored [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]
    (X : TauPGraph P V)
    (T : InductiveNiceTreeDecomposition (G := X.toMath.G))
    (color : V → Fin (omega + 1))
    (theta : Language.Formula P) : Bool
```

This is the main fixed-width interface.  Its runtime definition only extracts
`T.tree` and calls `checkCode`.  Its correctness theorem additionally takes:

```lean
hcolor : T.tree.IsBagColoring color
hFO : theta.freeFO = ∅
hSO : theta.freeSO = ∅
```

and proves:

```lean
checkColored X T color theta = true ↔
  Language.Semantics.Satisfies X.toMath theta
```

### 5.3 `checkFin`

For a graph with vertex type `Fin n`, `checkFin` uses:

```lean
Fin.castSucc : Fin n → Fin (n + 1)
```

as a globally injective coloring.  This removes the coloring argument, but it
uses `n + 1` colors.  It is therefore a convenience interface, not the
treewidth-parameterized interface used in the fixed-width statement.

## 6. Module map

The umbrella module is
[`GraphMSO/Executable.lean`](../GraphMSO/Executable.lean).

| Module | Main role | Important declarations |
|---|---|---|
| [`graph.lean`](../GraphMSO/Executable/graph.lean) | Boolean graph input | `TauPGraph`, `toMath` |
| [`sigma.lean`](../GraphMSO/Executable/sigma.lean) | Boolean sigma letters | `ExecSigmaLetter`, `decode`, `compatible` |
| [`relabel.lean`](../GraphMSO/Executable/relabel.lean) | Semantics under label maps | `comapLabels`, `satisfies_map_iff` |
| [`formula.lean`](../GraphMSO/Executable/formula.lean) | Executable tree-MSO syntax | `ExecFormula`, `toFormula` |
| [`automaton.lean`](../GraphMSO/Executable/automaton.lean) | Executable bottom-up automata | `ExecTreeAutomaton`, `projectLast` |
| [`atomic.lean`](../GraphMSO/Executable/atomic.lean) | Atomic-formula automata | `trackSingletonAutomaton` and related definitions |
| [`compile.lean`](../GraphMSO/Executable/compile.lean) | Certified structural compiler | `Compiled`, `compile`, `checkTree` |
| [`encoding.lean`](../GraphMSO/Executable/encoding.lean) | Direct nice-tree encoding | `encodeLetter`, `encodeAux`, `encode` |
| [`encodingCorrect.lean`](../GraphMSO/Executable/encodingCorrect.lean) | Encoding refinement | `decode_encodeLetter_eq`, `encode_map_decode` |
| [`translation.lean`](../GraphMSO/Executable/translation.lean) | Executable Courcelle translation | `translate`, `legalTranslate` |
| [`modelCheck.lean`](../GraphMSO/Executable/modelCheck.lean) | End-to-end checker | `checkCode`, `checkColored`, `checkFin` |
| [`cost.lean`](../GraphMSO/Executable/cost.lean) | Qualified abstract cost | `checkCodeCosted_cost` |
| [`examples.lean`](../GraphMSO/Executable/examples.lean) | Build-time smoke tests | four `#guard` commands |

## 7. Boolean graph and sigma-letter representations

### 7.1 Graph input

[`graph.lean`](../GraphMSO/Executable/graph.lean) defines:

```lean
structure TauPGraph (P : Type u) (V : Type v) where
  adj : V → V → Bool
  pred : P → V → Bool
  adj_symm : ∀ u v, adj u v = adj v u
  adj_loopless : ∀ v, adj v v = false
```

The graph is not bundled with a vertex enumeration.  The required `Fintype`
or `DecidableEq` instances are supplied by the caller where needed.

`TauPGraph.toMath` interprets the Boolean fields as propositions:

```text
X.toMath.G.Adj u v  iff  X.adj u v = true
X.toMath.pred p v   iff  X.pred p v = true
```

This is the first refinement boundary.

### 7.2 Sigma letters

[`sigma.lean`](../GraphMSO/Executable/sigma.lean) represents the label of one
decomposition node by four finite Boolean tables:

```lean
structure ExecSigmaLetter (P : Type u) (omega : Nat) where
  present : Fin (omega + 1) → Bool
  root : Fin (omega + 1) → Bool
  adj : Fin (omega + 1) → Fin (omega + 1) → Bool
  tag : P → Fin (omega + 1) → Bool
```

- `present i` says that color `i` occurs in the bag.
- `root i` is the raw Boolean boundary bit for color `i`.
- `adj i j` stores adjacency information between colors.
- `tag p i` stores unary predicate `p` at color `i`.

Here the field name `root` refers to adhesion or boundary membership, not to
the root node of the decomposition tree.  The observable test is
`rootContains i = present i && root i`; on labels produced by the encoder, this
means exactly that color `i` occurs in the adhesion.  This distinction matters
because an arbitrary `ExecSigmaLetter` may set `root i` while leaving
`present i` false.

`ExecSigmaLetter.decode` builds the old `SigmaLetter`.  It symmetrizes the
stored adjacency table and removes diagonal edges, so even an arbitrary table
decodes to a simple graph.

The Boolean observations `hasVertex`, `rootContains`, `adjOnColors`,
`tagOnColor`, `rootEmpty`, and `compatible` have corresponding
`*_eq_true_iff` theorems.  These theorems are what allow the executable
legality formula to reuse the old proof-facing legality result.

## 8. Direct encoding of a nice decomposition

The encoder is in
[`encoding.lean`](../GraphMSO/Executable/encoding.lean).  It deliberately
recurses on `InductiveNiceTree` rather than computing paths or parents in an
abstract rooted tree.

### 8.1 One letter

`encodeLetter X color bag adhesion` uses finite Boolean folds:

- search `bag` for `present`,
- search `adhesion` for `root`,
- search pairs of bag vertices for `adj`, and
- search `bag` for each predicate `tag`.

The helper `encodeAny` is `Finset.fold Bool.or false`.

### 8.2 Recursive tree encoding

`encodeAux` carries the current bag and its adhesion as `Finset V` values.
When it descends to a child, it reverses the constructor's bag update:

| Nice-tree constructor | Child bag passed recursively | Child adhesion |
|---|---|---|
| `leaf` | no child | no child |
| `introduce v child` | `bag.erase v` | `bag.erase v` |
| `forget v child` | `insert v bag` | current parent `bag` |
| `join left right` | current `bag` to both children | current `bag` |

Every nice-tree constructor produces exactly one `BinTree.node`.  A leaf is
encoded as a labeled node with two `nil` children.  The public `encode` starts
an empty-rooted code with empty bag and empty adhesion:

```lean
encode X color tree = encodeAux X color tree ∅ ∅
```

### 8.3 Why the encoding is correct

[`encodingCorrect.lean`](../GraphMSO/Executable/encodingCorrect.lean) proves the
refinement in stages:

1. `encodeAny_eq_true_iff` identifies the Boolean fold with finite
   existential quantification.
2. `sigmaLetter_ext_of_observations` reduces equality of sigma letters to the
   four observable predicates.
3. `decode_encodeLetter_eq` proves one computed letter equals the old
   decomposition letter after decoding.
4. `encodeAux_eq_toBinTree` proves that direct recursion has the expected
   ordered binary-tree shape.
5. `encodeLabelAux_decode_eq` follows the realization node by node.
6. `encode_map_decode` proves the final tree equality:

```lean
(encode X color T.tree).map ExecSigmaLetter.decode =
  T.orderedEncode X.toMath.pred color hcolor
```

The bag-coloring hypothesis is essential in the adjacency case: two vertices
with the same color in one bag must be equal.

## 9. Executable formulas and graph-to-tree translation

### 9.1 `ExecFormula`

[`formula.lean`](../GraphMSO/Executable/formula.lean) mirrors all 15
constructors of `TreeLanguage.Formula`.  The only computational change is that
label predicates return `Bool`:

```lean
labelMem  : (A → Bool) → FOVar → ExecFormula A
labelMem₂ : (A → A → Bool) → FOVar → FOVar → ExecFormula A
```

`ExecFormula.toFormula` interprets a Boolean predicate `p` as
`{a | p a = true}`.  The file also gives executable versions of the derived
formulas used by Courcelle's translation:

- `legal` and `definingPair`,
- `vtxTuple` and `setTuple`, and
- `adjTuple`, `predTuple`, `eqTuple`, and `contTuple`.

Each has a `toFormula_*` theorem identifying it with the old definition.

### 9.2 Translation of graph MSO

[`translation.lean`](../GraphMSO/Executable/translation.lean) defines
`translate omega`.

Each graph variable is represented by a block of `omega + 1` tree
second-order variables, one coordinate per color:

- `fvBlock omega x` for a graph first-order variable, and
- `svBlock omega X` for a graph set variable.

The graph atoms become tuple formulas:

| Graph atom | Executable tree formula |
|---|---|
| equality | `eqTuple` |
| adjacency | `adjTuple` |
| unary predicate | `predTuple` |
| set membership | `contTuple` |

A graph first-order quantifier therefore quantifies a whole block of tree set
variables and guards it with `vtxTuple`.  A graph set quantifier similarly uses
`setTuple`.

The checked formula is:

```lean
legalTranslate omega theta =
  (legalFormula P omega).conj (translate omega theta)
```

`legalFormula` requires an empty boundary at the root and compatible
child-parent letters.  The important refinement theorem is:

```lean
toFormula_legalTranslate :
  (legalTranslate omega theta).toFormula =
    (TreeLanguage.Formula.conj (SigmaTree.legalFormula P omega)
      (Language.Formula.translate omega theta)).comapLabels
        ExecSigmaLetter.decode
```

## 10. Executable bottom-up automata

### 10.1 Basic machine

[`automaton.lean`](../GraphMSO/Executable/automaton.lean) defines:

```lean
structure ExecTreeAutomaton (A : Type u) where
  State : Type
  [stateFinite : Finite State]
  [stateDecidableEq : DecidableEq State]
  nil : State
  node : A → State → State → State
  accept : State → Bool
```

`run` performs a deterministic bottom-up fold and `accepts` applies the final
Boolean test.  `toTreeAutomaton` forgets the computational presentation and
connects it to the old padded-term automaton.  In particular:

```lean
accepts_eq_true_iff_language
```

identifies Boolean acceptance with membership in the old automaton language.

Complement keeps the same transitions and flips `accept`.  Intersection and
union use product states.

The state field stores a `Finite` proof, not a bundled `Fintype` enumeration.
This distinction matters for quantified formulas: a powerset state should not
cause the complete powerset to be enumerated before a run begins.

### 10.2 Atomic automata

[`atomic.lean`](../GraphMSO/Executable/atomic.lean) builds the base cases.

| Automaton | What its state summarizes |
|---|---|
| `falseAutomaton` | Always rejects |
| `trackSingletonAutomaton` | Whether a track marks exactly one node |
| `tracksIntersectAutomaton` | Whether two tracks meet at a node |
| `parentTrackAutomaton` | Whether a parent-track node has a child-track child |
| `labelMemTrackAutomaton` | Labels occurring on one marked track |
| `labelMem₂TrackAutomaton` | Two marked label sets for a binary relation |

`tracksIntersectAutomaton` alone only checks intersection.  It represents
first-order equality under `CarriesAssignment`, where a first-order value
`none` is represented by an empty track and `some p` by the singleton track
containing `p`.  A fresh quantified first-order track is separately forced to
contain exactly one node by `trackSingletonAutomaton`.

### 10.3 Lazy projection of one track

Quantifier compilation introduces one fresh final track and then erases it.
`projectLast` performs the required subset construction without eagerly
enumerating the full powerset.

For a source automaton `M`, the projected state is `Finset M.State`:

- `nil` has state `{M.nil}`;
- at a node, take the product of the state sets actually reached by the two
  children;
- run the source transition once with the erased bit `false` and once with it
  `true`; and
- union the resulting finite sets.

The final test accepts if any reached source state is accepted.  The main
proofs are:

- `mem_run_projectLast_iff`,
- `projectLast_accepts_eq_true_iff`,
- `lastTrackExtension_iff_remapTracks`, and
- `language_toTreeAutomaton_projectLast`.

This design avoids eager global enumeration.  It does not remove state
explosion.  Reached state sets and their Cartesian products may still grow very
quickly, and nested quantifiers produce nested `Finset` state types.  No
explicit state-growth bound is proved here.

## 11. The certified structural compiler

[`compile.lean`](../GraphMSO/Executable/compile.lean) defines:

```lean
structure Compiled foTrack soTrack phi where
  automaton : ExecTreeAutomaton (A × TrackBits n)
  correct : TrackLanguage foTrack soTrack phi.toFormula
    automaton.toTreeAutomaton.language
```

Thus `compile` never returns a bare automaton: it returns the automaton together
with its proof-facing language certificate.

The recursive cases use:

| Formula form | Automaton construction |
|---|---|
| atomic formula | the corresponding automaton from `atomic.lean` |
| `neg phi` | complement |
| `conj phi psi` | intersection |
| `disj phi psi` | union |
| `impl phi psi` | `not phi` union `psi` |
| `biimpl phi psi` | both true union both false |

For a quantifier, the old tracks are embedded by `Fin.castSucc` and the new
variable uses `Fin.last n`:

- `existsFO x phi`: intersect with the singleton-track automaton, then
  `projectLast`;
- `forallFO x phi`: search for a singleton counterexample using complement and
  projection, then complement the result;
- `existsSO X phi`: directly `projectLast`, because a set track may mark any
  node set;
- `forallSO X phi`: complement, project, and complement.

The closed-tree wrapper `checkTree` adds one all-false dummy track.  Using
`Fin 1` makes the variable-to-track functions total.  The all-false track
represents `Assignment.empty`, which assigns `none` to every first-order
variable and `∅` to every second-order variable.

Its final tree-level theorem is:

```lean
checkTree_eq_true_iff :
  checkTree phi t = true ↔
    TreeLanguage.Semantics.Satisfies t.toTreeModel phi.toFormula
```

## 12. End-to-end correctness

Assume:

- `T` is a certified empty-rooted inductive nice decomposition of
  `X.toMath.G`,
- `color` is a bag coloring into `Fin (omega + 1)`, and
- `theta` has no free first- or second-order variables.

Then the proof follows this chain:

```text
checkColored X T color theta = true

  iff  the executable encoded tree satisfies
       (legalTranslate omega theta).toFormula
       [checkTree_eq_true_iff]

  iff  the decoded label tree satisfies the old legality-and-translation
       formula
       [toFormula_legalTranslate, BinTree.Semantics.satisfies_map_iff]

  iff  T.orderedEncode X.toMath.pred color hcolor satisfies that formula
       [encode_map_decode]

  iff  X.toMath satisfies theta
       [orderedEncode_satisfies_legal_translate_iff]
```

This composition is first isolated in
`checkColored_eq_true_iff_of_encode_eq`.  Supplying `encode_map_decode` gives
the public theorem `checkColored_eq_true_iff`.

For `Fin n` vertices, `checkFin_eq_true_iff` derives the coloring obligation
from injectivity of `Fin.castSucc`.

## 13. Qualified cost model

[`cost.lean`](../GraphMSO/Executable/cost.lean) uses the existing `Costed`
structure.  Let `n` be the number of constructors of the input nice tree.

| Part | Charged cost |
|---|---:|
| direct encoding | `n` |
| automaton traversal, including absent children | `2 * n + 1` |
| final Boolean acceptance test | `1` |
| total | `3 * n + 2` |

A binary tree with `n` genuine nodes has `n + 1` absent children, which explains
the `2 * n + 1` traversal count.

The exact results include:

```lean
checkCodeCosted_cost
checkColoredCosted_cost
checkFinCosted_cost
```

The equality `3 * n + 2` is an abstract online operation count.  The counter
charges one unit for each whole encoding-node operation, each visited tree
constructor and its whole transition, and the final whole acceptance test.  It
does not separately charge:

- `encodeLetter` or its internal bag searches within a charged encoding node;
- `Finset.product`, `image`, and `union` within a charged projected transition;
  or
- the element-by-element `finsetAny` work within the charged final acceptance
  test.

The following are wholly uncharged:

- graph-to-tree formula translation and formula compilation;
- construction of the dummy-track relabeling;
- Lean kernel and VM reduction costs; and
- construction of the nice decomposition and bag coloring.

Therefore this theorem does not claim that the complete Lean evaluator runs in
`3 * n + 2` machine steps, nor does it bound compiler state growth.

## 14. Examples and verification

[`examples.lean`](../GraphMSO/Executable/examples.lean) contains four
build-time guards:

1. a one-node Boolean-labeled tree satisfying `exists x, label(x)`;
2. a one-node tree that does not satisfy it;
3. the empty graph satisfying graph truth; and
4. the empty graph not satisfying graph falsehood.

The first pair exercises first-order singleton tracks and lazy projection.  The
second pair exercises the full `checkCode` path:

```text
direct encoding -> graph-to-tree translation -> compiler -> automaton run
```

Run just these examples with:

```text
lake build GraphMSO.Executable.examples
```

Run the complete project gate with:

```text
lake build
```

The file also defines a one-vertex introduce-forget code and two graph
sentences.  Their `#eval` commands are intentionally kept in a block comment:
the translated vertex-recognition formula has more nested quantifiers and is a
manual stress test rather than a build-time regression test.
The expected outputs are `true` and `false`, respectively, but neither
computation is executed by `lake build`.

The guards are smoke tests, not the basis of semantic correctness.  Correctness
comes from the refinement theorems and `checkColored_eq_true_iff`.

## 15. Current limitations and next steps

1. **The decomposition must already be nice.**
   The checker consumes an `InductiveNiceTreeDecomposition` with empty root
   bag.  Arbitrary-to-nice normalization is not yet formalized.

2. **The main checker needs a coloring.**
   `checkColored` accepts a color function, and its correctness theorem needs
   `IsBagColoring`.  It does not compute or verify that certificate at runtime.

3. **`checkFin` is not the fixed-width interface.**
   It uses a global `n + 1` coloring.  It is useful for evaluation but does not
   preserve the treewidth parameter.

4. **Graph correctness is stated for sentences.**
   The final theorem requires empty sets of free first- and second-order
   variables.

5. **Lazy projection can still grow quickly.**
   It avoids enumerating an entire powerset before execution, but the reached
   finite state sets may still grow very quickly, potentially exponentially up
   to the source state space.  Nested quantifiers also produce nested `Finset`
   state types, and no explicit state-growth bound is proved here.

6. **The cost theorem is deliberately abstract.**
   It does not bound actual `Finset` work, compiler construction time, or Lean
   VM time.

7. **MSO2 remains future work.**
   The existing incidence decomposition is ordinary rather than constructor
   nice.  Nice normalization must be inserted before the existing incidence
   reduction can be connected to the present executable checker.

## 16. Recommended reading orders

For a quick top-down understanding:

1. [`examples.lean`](../GraphMSO/Executable/examples.lean)
2. [`modelCheck.lean`](../GraphMSO/Executable/modelCheck.lean)
3. [`encoding.lean`](../GraphMSO/Executable/encoding.lean)
4. [`translation.lean`](../GraphMSO/Executable/translation.lean)
5. [`compile.lean`](../GraphMSO/Executable/compile.lean)
6. [`automaton.lean`](../GraphMSO/Executable/automaton.lean)
7. the correctness and cost files

To follow implementation dependencies bottom-up:

1. `graph.lean`
2. `sigma.lean`
3. `formula.lean`
4. `relabel.lean`
5. `automaton.lean`
6. `atomic.lean`
7. `compile.lean`
8. `encoding.lean`
9. `encodingCorrect.lean`
10. `translation.lean`
11. `modelCheck.lean`
12. `cost.lean`
13. `examples.lean`

Useful proof-facing prerequisites are:

- [`GraphMSO/Decomp/nice_inductive.lean`](../GraphMSO/Decomp/nice_inductive.lean),
- [`GraphMSO/Decomp/translation.lean`](../GraphMSO/Decomp/translation.lean), and
- [`GraphMSO/Automata/orderedEncoding.lean`](../GraphMSO/Automata/orderedEncoding.lean).

The broader project status and remaining roadmap are recorded in
[`docs/PLAN.md`](PLAN.md).
