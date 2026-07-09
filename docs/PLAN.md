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
- Topmost-bag lemmas used by the lecture-note encoding.
- Bag-injective coloring existence for bounded-width decompositions.
- Structural cone lemmas corresponding to the lecture note.

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

Main tasks:

- Formalize the algorithmic nice-normalization theorem from
  `Courcelle/nice_tree_decomp.tex`, if the final Courcelle statement needs to
  normalize a supplied decomposition inside Lean.
- Formalize the incidence-decomposition construction: from a decomposition of
  `G`, build a decomposition of the colored incidence graph with width at most
  `max omega 2`.
- Add the associated size bounds needed for linear-time statements:
  `|E(G)| <= omega * |V(G)|` for bounded treewidth, and the corresponding
  incidence-structure size bound.
- Keep these results independent of the later MSO translation layer.

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

Main tasks:

- Decide whether to introduce a small tree-MSO syntax or a reusable relational
  vocabulary abstraction.
- Define tree formulas for root, parent, connected node sets, top node, and
  dangles.
- Formalize defining pairs and defining tuples for vertices and vertex sets.
- Translate `tau_P` MSO atoms:
  adjacency, equality, set membership, and unary predicate atoms.
- Prove translation correctness:
  graph satisfaction iff the encoded legal sigma tree satisfies the translated
  tree formula.

### Phase 4: MSO2 via Colored Incidence

Goal: connect the existing MSO2-over-`SimpleGraph` source language to the
`tau_P` theorem through the colored incidence structure.

Main tasks:

- Define the formula translation from MSO2 over `SimpleGraph` to MSO1 over
  `tau_I = {adj, Vert, EdgeObj}`.
- Prove truth preservation for the translation.
- Combine this with the incidence treewidth/decomposition theorem from Phase 1.

### Phase 5: Tree Automata and Courcelle Statement

Goal: state and then progressively formalize the automata side.

Main tasks (the automata core of TW §2 is done, see above):

- Connect `SigmaTree` to ranked terms: an ordered/binary tree representation
  and the padding encoding with a nullary `⊥` symbol.  `SigmaTree` itself is
  an unordered mathlib tree, so this step needs the ordered representation
  (for nice decompositions, `InductiveNiceTree` already carries it).
- Define a tree MSO syntax over `child_1, child_2, P_a` and its semantics.
- Build the atomic automata for that vocabulary and the track/product
  alphabets for free variables.
- Prove the MSO-to-automaton compilation by formula induction, using the
  closure theorems already available.
- Combine the translation theorem and automaton correctness into the
  decomposition-given Courcelle theorem.
- Linear-time claims stay metatheoretic until Phase 6 fixes a cost model.

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

Encoding legality (Phase 2, first half) and the tree-automata core (Phase 5,
TW §2) are done.  The best next Lean targets:

1. Defining pairs and defining tuples over an encoded triple
   (lecture note §3), stated directly against `(G, c, (T, beta))` as the
   issues note recommends — this starts Phase 3 without needing decoding.
2. The incidence-decomposition construction and width bound (Phase 1).
3. The ordered-binary-tree bridge from `SigmaTree`/`InductiveNiceTree` to
   ranked terms, plus a tree MSO syntax (rest of Phase 5).
4. The algorithmic nice-normalization theorem
   (`Courcelle/nice_tree_decomp.tex`) only if the final statement needs
   built-in normalization; it is the heaviest standalone block.

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
