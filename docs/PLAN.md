# GraphMSO Plan

Last status check: 2026-07-10.

This project formalizes the graph-theoretic and logical infrastructure needed
for Courcelle's theorem in Lean 4.  The main proof route follows
`Courcelle/lecture_note_expanded.tex`: encode a bounded-width colored
tree-decomposition as a finite-alphabet tree, translate graph MSO to tree MSO,
and connect tree MSO to finite tree automata.

The preferred core theorem is for fixed finite unary-expanded graph
vocabularies
\[
  \tau_P = \{\mathrm{adj}\} \cup P.
\]
The ordinary graph case is `P = Empty`.  MSO2 over `SimpleGraph` should be
handled through the colored incidence structure with predicates `Vert` and
`EdgeObj`, not by rebuilding the source semantics around incidence graphs.

## Current Status

Verified on 2026-07-09:

- `lake build` succeeds.
- No real `sorry` or `admit` placeholders were found in `GraphMSO/**/*.lean`.
- The top-level module imports:
  - `GraphMSO.Syntax`
  - `GraphMSO.Semantics`
  - `GraphMSO.Examples`
  - `GraphMSO.incidence`
  - `GraphMSO.Decomp`

The following foundations are complete enough to stop tracking them as active
plan items.

### Done: MSO Semantics on Graphs

Files:

- `GraphMSO/Syntax.lean`
- `GraphMSO/Semantics.lean`
- `GraphMSO/Examples.lean`

Completed:

- MSO2-style syntax over `SimpleGraph`, including vertex variables, vertex-set
  variables, edge variables, and edge-set variables.
- Assignment-based Tarski semantics over `SimpleGraph V` with edge sort
  `G.edgeSet`.
- Closed-sentence wrapper `Semantics.Satisfies`.
- Free-variable support and assignment-independence lemmas.
- A library of graph-property examples and correctness theorems, including
  clique, independent set, dominating set, vertex cover, bipartite,
  connectivity, coloring, perfect matching, Hamiltonian cycle, and `K_3` minor
  examples.

### Done: MSO Semantics on `tau_P` Graphs

Files:

- `GraphMSO/language/tau_graph.lean`
- `GraphMSO/language/syntax.lean`
- `GraphMSO/language/semantics.lean`

Completed:

- `TauPGraph P`: a simple graph together with unary predicates indexed by `P`.
- MSO1 syntax over `tau_P`, with atoms `adj`, unary predicate atoms, equality,
  and set membership.
- Assignment-based semantics and basic simp lemmas.

This is the target language for the direct Courcelle proof over unary-expanded
graphs.

### Done: Tree Decomposition API

Files:

- `GraphMSO/Decomp/tree_decomp.lean`
- `GraphMSO/Decomp/bags.lean`
- `GraphMSO/Decomp/bagColoring.lean`
- `GraphMSO/Decomp/nodeConeGraph.lean`

Completed:

- `TreeDecomposition G` and `RootedTreeDecomposition G`.
- Bag, width, rooted path, parent/child, ancestor, cone, adhesion, and `BAGS(v)`
  APIs.
- Connectedness of `BAGS(v)` from the running-intersection axiom.
- Topmost-node machinery (`topNode`, uniqueness, ancestor property, convexity)
  for arbitrary preconnected node sets, with the `BAGS(v)` versions derived
  from it.
- Bag-injective coloring existence for bounded-width decompositions.
- Structural cone lemmas corresponding to the lecture note.
- The edge bound `|E(G)| ≤ omega * |V(G)|` for width-`omega` decompositions
  (`GraphMSO/Decomp/edgeBound.lean`), proved by charging each edge to the
  endpoint with the deeper `BAGS` top node instead of the note's
  minimal-decomposition induction.
- The partition characterization of induced connectivity
  (`GraphMSO/connectivity.lean`): the semantic content of the `conn(X)` tree
  formula of the translation.

### Done: Nice Decomposition Definitions

Files:

- `GraphMSO/Decomp/nice.lean`
- `GraphMSO/Decomp/nice_inductive.lean`

Completed:

- Predicate-style nice decomposition:
  `RootedTreeDecomposition.IsNice` and `NiceTreeDecomposition`.
- Constructor-style/algorithm-facing nice decomposition:
  `InductiveNiceTreeDecomposition`.
- Conversion from constructor-style nice decompositions to predicate-style nice
  decompositions.
- Recovery of constructor-style node cases from a predicate-style nice
  decomposition.
- Equivalence is now available in the direction needed for algorithms and in
  the direction needed for graph-theoretic use.
- Property transfer along a realization (`GraphMSO/Decomp/realization.lean`):
  width bounds and bag-injective colorings are equivalent on the two sides of
  a `Realizes`, so statements may mix the two nice-decomposition definitions.

The informal algorithmic normalization proof is written in
`Courcelle/nice_tree_decomp.tex`.  It is not yet formalized in Lean.

### Done: Incidence and Sigma-Tree Scaffolding

Files:

- `GraphMSO/incidence.lean`
- `GraphMSO/Decomp/KRootedPGraph.lean`
- `GraphMSO/Decomp/rootedGraph.lean`
- `GraphMSO/Decomp/sigmaTree.lean`
- `GraphMSO/Decomp/nodeConeGraph.lean`

Completed:

- Colored incidence graph vertices and the predicates `Vert` and `EdgeObj`.
- Colored incidence structure as a `KRootedPGraph IncSort`.
- Rooted `tau_P` graph structures and gluing witness data.
- Sigma letters with unary predicate tags.
- Sigma trees and the legality predicate.
- Node and cone graph definitions over unary predicate families.

### Done: Encoding and Legality (Phase 2, first half)

Files:

- `GraphMSO/Decomp/encoding.lean`

Completed:

- `RootedTreeDecomposition.encodeLetter` and `RootedTreeDecomposition.encode`:
  the Σ-tree encoding of a bag-colored rooted decomposition of a `tau_P`
  graph, following the lecture note.
- `encode_isLegal`: every encoding is legal (the forward half of the
  legal-iff-encoding lemma).
- Existence forms from a width bound alone, both for
  `RootedTreeDecomposition` and, through the realization transfer lemmas, for
  `InductiveNiceTreeDecomposition` (`exists_encode_isLegal`).

Not yet done: decoding of a legal tree, the decode/encode inverse lemmas, and
the recognition corollary over an encoding.

### Done: Defining Pairs and Defining Tuples (Phase 3, combinatorial layer)

Files:

- `GraphMSO/Decomp/definingPairs.lean`

Completed, stated directly over a bag-colored decomposition as the issues
note recommends:

- `IsDefiningPair` and `isDefiningPair_iff`: the five-condition
  characterization of the pairs `(BAGS v, color v)`.  The top node is
  expressed as "the parent leaves the set", matching the tree formulas.
- Distinctness: same-colored distinct vertices have disjoint `BAGS` and are
  non-adjacent; a vertex is determined by its defining pair.
- Atomic readings over encoded letters: adjacency
  (`adj_iff_exists_mem_BAGS_adjOnColors`) and unary predicates
  (`vpred_iff_exists_mem_BAGS_tagOnColor`), in both pointwise and
  existential-node forms.
- `definingTuple` for vertex sets, the singleton computation, the membership
  lemma `mem_iff_BAGS_subset_definingTuple`, and the recognition
  characterization `exists_definingTuple_eq_iff` in the exact shape of the
  set-recognition formula.

### Done: Tree Automata Core (Phase 5, TW §2)

Files:

- `GraphMSO/Automata/term.lean`
- `GraphMSO/Automata/automaton.lean`
- `GraphMSO/Automata/projection.lean`
- `GraphMSO/Automata/emptiness.lean`

Completed, following `Courcelle/Thatcher-Wright-expanding.tex`:

- Ranked alphabets (`RankedAlphabet`), finite terms, arity-preserving
  alphabet maps (`RankedAlphabet.Hom`), term relabeling, and depth.
- Deterministic and nondeterministic bottom-up tree automata with run
  semantics and languages; `Recognizable`.
- TW Theorem 1 (subset construction): `NTreeAutomaton.determinize`,
  `recognizable_iff_nondet`.
- TW Theorem 2 (Boolean closure): complement, product, intersection, union.
- TW Theorems 3-4 (projection and inverse projection):
  `Hom.imageAutomaton`, `Hom.comapAutomaton`, `Recognizable.map`,
  `Recognizable.comap`.
- TW Lemma 5 (replacement) via one-hole contexts.
- TW Lemma 6 and the mathematical content of Theorem 7: bounded-depth
  witnesses via depth-indexed reachability, and
  `language_nonempty_iff` (nonemptiness iff a witness of depth at most
  `Nat.card State` exists).

Not yet done: atomic automata for the labelled-tree vocabulary, the
MSO-to-automaton compilation induction, the regularity characterization
(TW §3, optional), and executable decision procedures (Phase 6).

## Remaining Roadmap

The plan is now organized by proof blocks rather than by every individual
lemma.  When a block becomes active, split it into small Lean tasks in the PR or
working notes for that block.

### Phase 1: Finish the Decomposition Infrastructure Used by the Note

Goal: make every decomposition fact cited by `lecture_note_expanded.tex`
available as Lean statements and proofs.

Done:

- `|E(G)| <= omega * |V(G)|` (see the tree-decomposition API section).
- Pendant extensions of graphs (`GraphMSO/pendant.lean`): one new leaf per
  index, with preservation of connectedness, acyclicity, and treeness.  The
  acyclicity proof lifts cycles into the induced old part via
  `Walk.induceLift` and shows pendant leaves lie on no cycle.
- The incidence-decomposition construction
  (`GraphMSO/Decomp/incidenceDecomp.lean`):
  `TreeDecomposition.incidenceDecomposition` builds a decomposition of
  `IncidenceGraph G` on nodes `D.Node ⊕ G.edgeSet` with one pendant leaf per
  edge, `incidenceDecomposition_hasWidth` bounds its width by `max omega 2`,
  and `card_incidenceVertex_le_of_hasWidth` bounds the incidence-structure
  size by `(omega + 1) * |V|`.

Remaining:

- Formalize the algorithmic nice-normalization theorem from
  `Courcelle/nice_tree_decomp.tex`, if the final Courcelle statement needs to
  normalize a supplied decomposition inside Lean.

### Phase 2: Encoding and Decoding Bounded Decompositions

Goal: formalize the lecture-note equivalence between colored bounded-width
decompositions and legal sigma trees.

Main tasks (encoding and its legality are done, see above):

- Define decoding/gluing of a legal sigma tree into a graph, coloring, and
  decomposition.
- Prove encode/decode correctness in both directions, up to the appropriate
  isomorphism/equality notion.
- Prove cone-gluing correctness using the existing rooted-graph gluing API.
- Per `Courcelle/lecture_note_expanded_lean_issues.tex`, prefer stating the
  Phase 3 recognition lemmas directly over an encoded triple, so decoding
  stays off the critical path of the main theorem.

### Phase 3: Translate Graph MSO to Tree MSO

Goal: formalize the logical interpretation used in
`lecture_note_expanded.tex`.

Done:

- The tree language (`GraphMSO/treeLanguage/syntax.lean`,
  `GraphMSO/treeLanguage/semantics.lean`): MSO formulas over `parent` and
  letter-class atoms `labelMem S x` (the note's finite disjunctions `A_i,
  R_i, E_ij, Q_i` are single atoms; `child_1/child_2` enter only at the
  automata boundary, where `parent` is definable).  Models are `TreeModel`s;
  satisfaction is Tarski-style with the assignment interface of the graph
  language.
- Semantic characterizations of the derived formulas: `root_`, `subset`,
  `empty`, `nonempty`, `adjTree`, `inSet`, `labelMem`, and crucially `conn`
  (reduced to the partition characterization in `GraphMSO/connectivity.lean`
  over the symmetrized parent graph `TreeModel.graph`), `top`, and `dangle`.
- The model bridge (`GraphMSO/Decomp/treeModel.lean`):
  `SigmaTree.toTreeModel`, and for an encoding the parent relation is the
  decomposition child relation definitionally while `TreeModel.graph` is the
  decomposition tree (`encode_toTreeModel_graph`).
- Defining pairs and defining tuples (see the earlier section).

Also done — the recognition layer (`GraphMSO/Decomp/recognition.lean`):

- `labelMem₂` binary letter-class atoms, finite `conjList`/`disjList`, and
  the formulas `legal`, `definingPair`, `vtxTuple`, `setTuple` in the tree
  language, with the note's finite alphabet disjunctions absorbed into
  set-parameterized atoms.
- `SigmaTree.satisfiesAt_legalFormula_iff`: the legality sentence
  characterizes legal Σ-trees (the note's `phi_legal` lemma), and encodings
  satisfy it.
- `satisfiesAt_definingPair_iff`: over an encoding, `phi_vtx_i` recognizes
  exactly the defining pairs (the note's Lemma vtx-i / recognition
  corollary part 1).
- `satisfiesAt_vtxTuple_iff` and `satisfiesAt_setTuple_iff`: the tuple
  formulas recognize the defining tuples of vertices and of vertex sets
  (recognition corollary parts 2-3).

Also done — the atomic formulas (recognition corollary part 4, in
`recognition.lean`):

- `Formula.setEq`, `adjTuple`, `predTuple`, `eqTuple`, `contTuple` in the
  tree language, with the note's double color disjunction of `phi_adj`
  realized as nested finite disjunctions.
- On defining tuples over an encoding: `satisfiesAt_adjTuple_iff`
  (adjacency), `satisfiesAt_predTuple_iff` (unary predicates),
  `satisfiesAt_eqTuple_iff` (equality, via injectivity of vertex defining
  tuples `eq_of_definingTuple_singleton_eq`), and
  `satisfiesAt_contTuple_iff` (membership, via
  `mem_iff_BAGS_subset_definingTuple`).

Also done — the translation itself (`GraphMSO/Decomp/translation.lean`):

- Block quantifiers for the tree language
  (`existsSOList`/`forallSOList` with the loose-assignment semantics
  `satisfiesAt_existsSOList_iff`/`forallSOList_iff`, and the simultaneous
  block update `Assignment.setBlock`).
- The variable allocation: graph FO variable `x` gets the tree set variables
  `fvBlock omega x = fun i => (omega+1)*(2*x) + i`, graph SO variable `X`
  gets `svBlock omega X = fun i => (omega+1)*(2*X+1) + i`, with the
  positional-decoding injectivity and disjointness lemmas.
- Free variables `freeFO`/`freeSO` for the graph language.
- `Language.Formula.translate` (`theta_star`): atoms to the atomic tuple
  formulas, connectives commute, quantifiers to guarded block quantifiers
  (universal quantifiers translated directly as guarded universal blocks
  rather than via `¬∃¬`).
- `satisfiesAt_translate_iff` — translation correctness by formula
  induction: over an encoding, satisfaction of `theta_star` equals graph
  satisfaction, for every tree assignment carrying the defining tuples of
  the graph assignment on all free-variable blocks.
- `satisfies_legalFormula_conj_translate_iff` — the note's final display:
  for a closed `tau_P` formula, `G ⊨ phi` iff the encoding satisfies
  `phi_legal ∧ phi_star`.

Phase 3 is complete.

### Phase 4: MSO2 via Colored Incidence — done

Goal: connect the existing MSO2-over-`SimpleGraph` source language to the
`tau_P` theorem through the colored incidence structure.

Done (`GraphMSO/incidenceTranslation.lean`):

- `incidenceTauGraph`: the coloured incidence structure as a `τPGraph` over
  `IncSort`.
- `Formula.toIncidence`: the MSO₂-to-MSO₁ translation.  The two-sorted
  variables are merged by parity (`x ↦ 2x`, edge `e ↦ 2e+1`, and likewise
  for set variables); quantifiers are guarded by `Vert`/`EdgeObj` and the
  pointwise set guards; the `edge x y` atom, absent from `τ_I`, becomes the
  existence of a common incident edge object between distinct vertices
  (`adj_iff_exists_edgeSet`), with the odd bound variable `2x + 2y + 1`.
- `satisfiesAt_toIncidence_iff`: truth preservation for open formulas, with
  the assignment correspondence carried on free variables.
- `satisfies_toIncidence_iff` (closed sentences) and `incidence_reduction`
  (combined with `incidenceDecomposition_hasWidth`): MSO₂ model checking on
  `G` with a width-`omega` decomposition reduces to MSO₁ model checking on
  the incidence structure with a width-`max omega 2` decomposition.

### Phase 5: Tree Automata and Courcelle Statement

Goal: state and then progressively formalize the automata side.

Done beyond the TW §2 core:

- Ordered binary labeled trees (`GraphMSO/Automata/binTree.lean`):
  `BinTree A` with positions, labels, the ordered child relations
  `childRel false/true` (= `child₁/child₂`), the tree-model reading
  `BinTree.toTreeModel`, and the injective padded ranked-term encoding
  `BinTree.toTerm` over `paddedAlphabet A` (nullary `⊥` + binary letters).
- Isomorphism invariance (`GraphMSO/treeLanguage/modelIso.lean`):
  `TreeModel.Iso` and `satisfiesAt_mapEquiv_iff`/`satisfies_iff_of_iso` —
  tree MSO satisfaction transfers along node bijections preserving parent
  and labels.  This is the glue between the unordered encoded model of a
  decomposition and the ordered tree the automaton runs on.

Main remaining tasks (linear-time claims excluded; they stay metatheoretic
until Phase 6 fixes a cost model):

- Track machinery: `BinTree.map`, the position equivalence between a tree
  and its relabelings, and the correspondence between trees over
  `A × Bool^n` and trees over `A` with `n` distinguished position sets.
- Atomic automata over `paddedAlphabet` for the tree vocabulary, and the
  MSO-to-automaton compilation by formula induction using the closure
  theorems (subset construction, Boolean closure, projection).
- The ordered encoding of an `InductiveNiceTreeDecomposition` as a
  `BinTree (SigmaLetter P omega)` and its `TreeModel.Iso` with the encoded
  model, via the realization.
- Combine the translation theorem, the isomorphism transfer, and automaton
  correctness into the decomposition-given Courcelle theorem.

### Phase 6: Toward Really Working Code

Goal: after the proof architecture is stable, make the checker executable on
finite inputs where possible.

Main tasks:

- Separate proof-only structures from computable data structures.
- Add finite, decidable representations of graphs, decompositions, formulas,
  sigma trees, and automata.
- Implement the normalization/encoding/model-checking pipeline.
- Prove the executable pipeline refines the mathematical semantics.
- Maintain small examples that can be evaluated with `#eval` or tests.

This phase should not block the proof formalization.  It becomes realistic once
the mathematical interfaces for decomposition encoding, formula translation,
and automata evaluation are stable.

## Immediate Next Step

Done so far: encoding legality (Phase 2, first half), the tree-automata core
(Phase 5, TW §2), the defining-pair/tuple layer, the tree language with its
formula characterizations and model bridge, and the recognition formulas
`phi_legal`, `phi_vtx_i`, `phi_vtx`, `phi_set` with correctness over an
encoding (Phase 3), plus the incidence decomposition, the edge bound, and
the connectivity characterization (Phase 1).  The best next Lean targets:

1. The MSO₂-to-MSO₁ formula translation over the coloured incidence
   structure (Phase 4); its decomposition input is now available from
   `incidenceDecomposition`.
2. Ranked-term bridge for ordered trees, the atomic automata for the tree
   vocabulary, and the MSO-to-automaton compilation (rest of Phase 5); with
   Phase 3 complete this is the last substantial block before the
   decomposition-given Courcelle statement.
3. Decoding of legal Σ-trees (Phase 2, second half; off the critical path),
   and the nice-normalization theorem only if the final statement needs it.

## Working Rules

- Keep this plan short.  Do not add per-lemma checklists here.
- Put detailed proof checklists in the active PR, issue note, or companion TeX
  file for the current block.
- Every completed Lean block should end with:
  - no new `sorry`;
  - no new custom axioms;
  - `lake build` passing.
- Prefer theorem-level correctness first.  Add executable code only when the
  mathematical interface has settled.
