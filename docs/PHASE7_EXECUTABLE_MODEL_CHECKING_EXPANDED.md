# Verified Executable MSO₂ Model Checking: The Complete Pipeline

This document describes the executable development as it stands after the
completion of the rose-tree front end.  It supersedes the scope and
limitation sections of
[`PHASE7_EXECUTABLE_MODEL_CHECKING.md`](PHASE7_EXECUTABLE_MODEL_CHECKING.md);
that document remains the authoritative code guide for the Phase 7 core
(sigma letters, the direct encoder, the certified compiler, and the cost
model, its §§7–13), all of which is unchanged and still accurate.

The headline result: the project now contains a **fully computable,
end-to-end verified MSO₂ model checker**.

```lean
def checkMSO2Exec {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : DecompTree V) (omega : ℕ) (phi : Formula) : Bool
```

It consumes a rose-tree presentation of a tree decomposition of `G` and an
MSO₂ formula, and returns a Boolean.  It is a plain `def`: every stage —
incidence extension, nice normalization, bag coloring, encoding, formula
translation, automaton compilation, and the automaton run — is executable
code with no `choose`, no `Finset.toList`, and no classical instances in
data positions.  Its correctness theorem is

```lean
theorem checkMSO2Exec_eq_true_iff [Fintype V]
    (hvalid : t.IsDecompFor G) (hw : t.HasWidth omega)
    (hclosed : phi.Closed) :
    checkMSO2Exec G t omega phi = true ↔ Semantics.Satisfies G phi
```

Verified on 2026-07-18: the full `lake build` succeeds (3167 jobs), all
twelve maintained `#guard` smoke tests pass during the build, and every
declaration named in this document depends only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## 1. What changed relative to the original Phase 7 document

The original document's §1 listed three omissions.  All three are now
implemented and verified:

| Former omission | Resolved by | File |
|---|---|---|
| arbitrary-to-nice normalization | `DecompTree.normalizeCode` | [`execNormalization.lean`](../GraphMSO/Decomp/execNormalization.lean) |
| automatic width-sized bag coloring | `DecompTree.greedyColoring` | [`execColoring.lean`](../GraphMSO/Decomp/execColoring.lean) |
| end-to-end executable MSO₂ assembly | `checkMSO2Exec` | [`Executable/incidence.lean`](../GraphMSO/Executable/incidence.lean) |

The fourth reservation of the original document — that the abstract cost
theorem is not a claim about Lean VM runtime — still stands, and is now also
practically visible: see §7.

## 2. Thirty-second overview

```text
rose-tree decomposition t of G          MSO₂ formula phi
        |                                     |
        | incidenceTree G                     | toIncidence
        v                                     v
DecompTree (IncidenceVertex G)          MSO₁ formula over tau_I
        |                                     |
        | normalizeCode                       |
        v                                     |
InductiveNiceTree (IncidenceVertex G) ∅       |
        |            \                        |
        |             greedyColoring          |
        v              v                      v
        +---------- checkCode ----------------+
                        |
                        v          (encode -> legalTranslate -> compile -> run,
                       Bool         the unchanged Phase 7 core)
```

Three new executable stages sit in front of the Phase 7 core:

1. **Incidence extension** (`DecompTree.incidenceTree`): turns a
   decomposition of `G` into one of `IncidenceGraph G`, raising the width to
   `max omega 2`.
2. **Nice normalization** (`DecompTree.normalizeCode`): turns the rose tree
   into a constructor-coded nice tree with empty root bag.
3. **Greedy bag coloring** (`DecompTree.greedyColoring`): computes an
   `omega + 1`-color bag-injective coloring.

Each stage carries correctness theorems shaped exactly like the hypotheses
of the next stage, so the final theorem is a composition with no glue
axioms.

## 3. The input contract: rose-tree decompositions

File: [`execDecomp.lean`](../GraphMSO/Decomp/execDecomp.lean).

```lean
inductive DecompTree (V : Type u) : Type u where
  | node (bag : List V) (children : List (DecompTree V))
```

`DecompTree` is the algorithm-facing input format for tree decompositions.
Design points, in order of importance:

- **Rootedness and tree shape are data.**  A rose tree cannot fail to be a
  tree, so no `IsTree` proof, root choice, or child enumeration is needed,
  and every algorithm is a structural recursion (via the
  `DecompTree.induction_on` principle).
- **Bags are raw `List V` values.**  Lists, unlike `Finset`s, admit
  computable enumeration; duplicates are harmless because all consumers
  measure bags through `List.toFinset` and chain constructions dedup
  internally.
- **Validity is a separate predicate.**  Algorithms consume raw data;
  correctness theorems consume:

```lean
structure IsDecompFor (t : DecompTree V) (G : SimpleGraph V) : Prop where
  vertexCoverage : ∀ v, t.Occurs v
  edgeCoverage : ∀ ⦃u v⦄, G.Adj u v → t.OccursPair u v
  runningIntersection : t.RunningIntersection
```

`RunningIntersection` is the rooted, local form of the usual connectivity
axiom: a vertex shared by a node bag and a child subtree lies in the child
root bag (`hdown`), and a vertex occurring below two distinct child branches
lies in the node bag (`hpair`, a `List.Pairwise` over the children).  These
two local conditions are exactly what the normalization and coloring proofs
consume, so no top-node machinery is required on the executable side.

Supporting API: `HasBag` (inductive), `Occurs`, `OccursPair`, `HasWidth`
(`toFinset.card ≤ omega + 1` for every bag), `IsBagColoring`
(`Set.InjOn` on every bag), and membership/iff lemmas
(`hasBag_node_iff`, `occurs_node_iff`, …).

## 4. The three new executable stages

### 4.1 Computable normalization

Files: [`execNormalization.lean`](../GraphMSO/Decomp/execNormalization.lean)
and the list-presented building blocks in
[`normalization.lean`](../GraphMSO/Decomp/normalization.lean).

The proof-facing normalizer (`RootedTreeDecomposition.normalizeCodeAt`) is
noncomputable precisely where it reads data out of the abstract
decomposition: bag-to-`Finset` conversion, child enumeration, and
`WellFounded.fix`.  On a rose tree all three become trivial, so the
executable normalizer is the same algorithm with the choice points replaced
by concrete data:

```lean
def normalizeAux : (t : DecompTree V) →
    InductiveNiceTree V (t.rootBag.toFinset : Set V)
  | node bag []        => closeToLeafOfList bag
  | node bag (c :: cs) =>
      joinNonempty (changeRootOfList bag c.rootBag (normalizeAux c))
        (cs.map fun s => changeRootOfList bag s.rootBag (normalizeAux s))

def normalizeCode (t : DecompTree V) : InductiveNiceTree V ∅
```

`changeRootOfList` and `closeToLeafOfList` are computable counterparts of
`changeRoot`/`closeToLeaf`: the introduce/forget chain between two bags is
built from `List.dedup`/`List.filter` differences, so no `Nodup` certificate
and no `Finset.toList` is needed.  They live in `normalization.lean` next to
their `Finset` siblings and carry the same lemma surface (width, bag
survival, occurrence, occurrence connectedness, bag-injectivity).

Correctness is proved directly by rose-tree induction — deliberately *not*
by comparison with the noncomputable normalizer, whose choice-dependent
child order makes the two outputs differ syntactically:

- `normalizeCode_hasWidth` — width preservation;
- `normalizeCode_hasBag` — every input bag survives as a code bag;
- `normalizeCode_occurs_iff` — occurrence equivalence;
- `normalizeCode_occPreconnected` — running intersection of the code;
- `normalizeCode_isBagColoring` — colorings injective on input bags are
  bag colorings of the code (forget-phase bags shrink toward the parent
  bag and introduce-phase bags grow toward the child bag, so input bags
  dominate every chain bag).

`DecompTree.normalize (t) (h : t.IsDecompFor G)` packages these into a
certified `InductiveNiceTreeDecomposition` with `normalize_tree : … = rfl`,
so the certificate layer is the only noncomputable part and the code
consumed by `checkCode` is `normalizeCode` itself.

### 4.2 Greedy bag coloring

File: [`execColoring.lean`](../GraphMSO/Decomp/execColoring.lean).

```lean
def greedyColoring (t : DecompTree V) (omega : ℕ) : V → Fin (omega + 1)
```

The tree is walked root-first, left-to-right, threading a state
`(V → Fin (omega + 1)) × List V` (the coloring so far and the assigned
vertices).  At each node, `colorBag` gives every unassigned bag member the
first color (`freshColor`) not used by the already-assigned members of that
bag.

Correctness (`greedyColoring_isBagColoring`) rests on one invariant,
maintained through both the bag fold and the sibling fold: *every already
assigned vertex occurring in the current subtree lies in its root bag, where
the partial coloring is injective*.  Running intersection is what preserves
the invariant across siblings (`hpair`) and into children (`hdown`), and the
width bound is what guarantees a fresh color exists (at most `omega` of the
`omega + 1` colors can be blocked when a bag member is unassigned).

The composition
`normalizeCode_greedyColoring_isBagColoring` certifies the greedy coloring
for the *normalized code*, which is exactly the hypothesis shape of
`checkColored_eq_true_iff`.

### 4.3 Executable incidence extension

File: [`execIncidence.lean`](../GraphMSO/Decomp/execIncidence.lean).

`DecompTree.incidenceTree G t` extends a decomposition of `G` to one of
`IncidenceGraph G`, the computable counterpart of
`TreeDecomposition.incidenceDecomposition`:

- Every bag is mapped through `IncidenceVertex.fromV`.
- Every edge of `G` receives one pendant leaf
  `[fromV u, fromV v, fromEdge e]` hung below a node whose bag contains
  both endpoints.

Two representation problems are solved without choice:

1. **Edge enumeration.**  `Sym2` and `Finset` admit no computable element
   extraction, so edges are enumerated as `SimpleGraph.Dart`s built from
   `offDiagPairs` — the ordered pairs `(a, b)` with `a` strictly before `b`
   in the deduplicated `vertexList` of the tree.  Each unordered edge yields
   exactly one dart (`dartsOfList_pairwise_edge_ne`).
2. **Exactly-once attachment.**  The mutual recursion
   `incidenceAux`/`incidenceForest` threads the pending dart list through
   the walk: at each node the darts whose endpoints both lie in the bag are
   attached and removed, and the rest flow into the children left-to-right.
   A dart attached in one subtree is therefore absent from every later
   sibling's pending list, which is precisely what makes the edge-object
   occurrence sets singletons and preserves running intersection.

The spec layer proves threading facts (the returned pending list is a
sublist), occurrence characterizations for `fromV` and `fromEdge` vertices,
attachment completeness (a dart whose endpoints share a bag is consumed),
pendant-leaf production for consumed darts, the `max omega 2` width bound
(mapped bags keep their cardinality; leaf bags have three elements), and
running intersection.  They assemble into:

```lean
theorem incidenceTree_isDecompFor (h : t.IsDecompFor G) :
    (incidenceTree G t).IsDecompFor (IncidenceGraph G)
theorem incidenceTree_hasWidth (hw : t.HasWidth omega) :
    (incidenceTree G t).HasWidth (max omega 2)
```

## 5. End-to-end assembly and correctness

File: [`Executable/incidence.lean`](../GraphMSO/Executable/incidence.lean).

```lean
def checkMSO2Exec G t omega phi :=
  checkCode (omega := max omega 2) (incidenceTauGraphExec G)
    (DecompTree.incidenceTree G t).normalizeCode
    ((DecompTree.incidenceTree G t).greedyColoring (max omega 2))
    phi.toIncidence
```

The correctness proof of `checkMSO2Exec_eq_true_iff` is a short
composition — each arrow is one existing theorem:

```text
checkMSO2Exec G t omega phi = true

  iff  checkColored (incidenceTauGraphExec G)
         ((incidenceTree G t).normalize hI) (greedyColoring …) … = true
       [definitional: checkColored extracts T.tree, and normalize_tree = rfl]

  iff  the incidence structure satisfies phi.toIncidence
       [checkColored_eq_true_iff, with the coloring certificate
        normalizeCode_greedyColoring_isBagColoring and the validity
        certificate incidenceTree_isDecompFor transported along
        incidenceTauGraphExec_graph]

  iff  G satisfies phi
       [incidenceTauGraphExec_toMath, satisfies_toIncidence_iff]
```

The noncomputable `checkMSO2` (which takes a mathematical
`TreeDecomposition` instead of a `DecompTree`) is retained as the
proof-facing variant; the two share the entire correctness infrastructure.

## 6. Updated module map

New modules relative to the original document's §6:

| Module | Main role | Key declarations |
|---|---|---|
| [`Decomp/execDecomp.lean`](../GraphMSO/Decomp/execDecomp.lean) | rose-tree input format | `DecompTree`, `HasBag`, `Occurs`, `HasWidth`, `RunningIntersection`, `IsDecompFor`, `IsBagColoring` |
| [`Decomp/execNormalization.lean`](../GraphMSO/Decomp/execNormalization.lean) | computable nice normalization | `normalizeAux`, `normalizeCode`, `normalize` |
| [`Decomp/execColoring.lean`](../GraphMSO/Decomp/execColoring.lean) | greedy width-sized coloring | `greedyColoring`, `greedyColoring_isBagColoring` |
| [`Decomp/execIncidence.lean`](../GraphMSO/Decomp/execIncidence.lean) | computable incidence extension | `dartsOfList`, `incidenceAux`, `incidenceTree`, `incidenceTree_isDecompFor` |
| [`Executable/incidence.lean`](../GraphMSO/Executable/incidence.lean) | end-to-end assembly | `checkMSO2Exec`, `checkMSO2Exec_eq_true_iff`, `checkMSO2` |

The computable list-presented building blocks (`forgetList`,
`introduceList`, `changeRootOfList`, `closeToLeafOfList`) live in
[`Decomp/normalization.lean`](../GraphMSO/Decomp/normalization.lean)
alongside the proof-facing normalizer.  The Phase 7 core modules
(`graph`, `sigma`, `formula`, `automaton`, `atomic`, `compile`,
`encoding`, `encodingCorrect`, `translation`, `modelCheck`, `cost`) are
unchanged; see the original document.

## 7. Performance reality

`checkMSO2Exec` is executable and its pieces are fast: construction,
normalization, and coloring on small examples run instantly under `#eval`
(they are exercised by build-time guards).  A *complete* run, however,
compiles the automaton of `legalTranslate` at width `max omega 2 = 2` over
the incidence alphabet, whose size and quantifier alternations make even
the `K₂` instance expensive: an interpreted evaluation attempt did not
finish within twenty minutes.  This is the Courcelle fixed-parameter
constant, not an implementation bug; the original document's §10.3 caveat
("lazy projection does not remove state explosion") is where the time goes.
Complete runs are therefore kept as commented manual stress tests, and
practical mitigation paths are catalogued in
[`REMAINING_EXTENSIONS.md`](REMAINING_EXTENSIONS.md).

## 8. Build-time guards

[`Executable/examples.lean`](../GraphMSO/Executable/examples.lean) now
maintains twelve `#guard`s:

1–2. a one-node labeled tree satisfying / violating `∃x, label(x)`;
3–4. the empty graph satisfying truth / violating falsehood via `checkCode`;
5. `emptyDecompTree.normalizeCode.size == 1`;
6–7. `checkCode` on the *generated* (not hand-written) normalized code of
   the empty decomposition;
8–9. normalized-code sizes of the `K₂` and path decompositions (5 and 7),
   pinning the introduce/forget chains;
10. the greedy coloring of the path decomposition (`[0, 1, 0]`);
11. the normalized incidence code size of `K₂` (7), exercising
   `vertexList`/`dartsOfList`/`incidenceAux`/`normalizeCode` end to end;
12. a greedy color on the incidence tree of `K₂`.

The file also contains proved examples: validity (`IsDecompFor`), width,
and the coloring certificate for the normalized `K₂` code.

## 9. Current limitations

1. **Complete runs are slow.**  See §7.  The checker is verified and
   computable; it is not yet practical beyond the smallest widths.
2. **Validity is a proof obligation, not a runtime check.**
   `checkMSO2Exec_eq_true_iff` consumes `t.IsDecompFor G` and
   `t.HasWidth omega` as hypotheses; there is no `Decidable` instance yet
   that would discharge them by `decide` on concrete inputs.
3. **`checkFin` remains the `n + 1`-color fallback** (unchanged).
4. **Graph correctness is stated for sentences** (unchanged).
5. **The cost theorem is abstract** (unchanged): `3 * n + 2` counts charged
   online operations of the core pass, not VM time, and none of the three
   new front stages is cost-instrumented.  In particular the executable
   normalizer has no formal node bound yet (the proof-facing
   `(3 * omega + 5) * |N(T)|` bound has no `DecompTree` counterpart).

## 10. Reading order

Top-down, for the new material:

1. [`Executable/examples.lean`](../GraphMSO/Executable/examples.lean) —
   the rose-tree sections;
2. [`Executable/incidence.lean`](../GraphMSO/Executable/incidence.lean) —
   `checkMSO2Exec` and its theorem;
3. [`Decomp/execDecomp.lean`](../GraphMSO/Decomp/execDecomp.lean);
4. [`Decomp/execNormalization.lean`](../GraphMSO/Decomp/execNormalization.lean);
5. [`Decomp/execColoring.lean`](../GraphMSO/Decomp/execColoring.lean);
6. [`Decomp/execIncidence.lean`](../GraphMSO/Decomp/execIncidence.lean);

then the original document for the Phase 7 core, and
[`docs/PLAN.md`](PLAN.md) for overall project status.
