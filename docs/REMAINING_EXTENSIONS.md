# Remaining Extensions

Status as of 2026-07-18: the theorem-level Courcelle development and the
fully computable end-to-end pipeline (`checkMSO2Exec` with
`checkMSO2Exec_eq_true_iff`) are both complete; see
[`PLAN.md`](PLAN.md) and
[`PHASE7_EXECUTABLE_MODEL_CHECKING_EXPANDED.md`](PHASE7_EXECUTABLE_MODEL_CHECKING_EXPANDED.md).
Nothing below is a prerequisite for the theorem or the verified checker.
This file catalogues the optional extensions, with concrete plans against
the current codebase, so any of them can be picked up independently.

Effort labels: **S** (small, roughly one working session), **M** (medium,
one to two sessions), **L** (large, an architectural block on the scale of
a project phase).

## 1. Performance: making complete runs practical

**The problem, located.**  `checkMSO2Exec` forces the width to
`max omega 2` through the incidence reduction.  At width 2 the sigma
alphabet (`SigmaLetter IncSort 2`: color presence × boundary bits ×
color-pair adjacency × per-color predicate tags) is large, and the legality
sentence inside `legalTranslate` contains several quantifier alternations.
Each quantifier is a lazy subset construction (`projectLast`), and each
projected transition must consider all track extensions of a letter, so the
per-node cost multiplies through nested quantifiers.  An interpreted
evaluation of `checkMSO2Exec` on `K₂` did not finish within twenty
minutes; this is the expected fixed-parameter constant, and
`stateComplexity.lean` bounds it by a tower.

Mitigations, ordered by value for effort:

### 1.1 An MSO₁ direct path (`checkMSO1Exec`) — **S**

If a formula uses no edge or edge-set variables, the incidence reduction is
unnecessary: feed `DecompTree.normalizeCode` and
`DecompTree.greedyColoring` at the *original* width `omega` straight into
`checkCode` against a Boolean `TauPGraph` presentation of the input
structure.  At `omega = 1` the alphabet is incomparably smaller than the
width-2 incidence alphabet.  All parts exist; this is assembly plus one
correctness theorem in the style of `checkMSO2Exec_eq_true_iff` (using
`normalizeCode_greedyColoring_isBagColoring` and
`checkColored_eq_true_iff` directly, no incidence transport).

### 1.2 A compiled benchmark harness — **S**

Build-time `#guard`s and `#eval` run in the interpreter.  A `lean_exe`
target in the lakefile with an `IO` main would run natively compiled code —
typically a large constant factor faster — and doubles as the benchmark
driver of §4.  No proofs involved.

### 1.3 Letter representation and transition memoization — **M**

`ExecSigmaLetter` stores four Boolean tables as functions; state-set
operations hash and compare them repeatedly.  A packed bitmask encoding
(with a proved equivalence to the current record) plus a transition cache
keyed on (state, letter) would cut the dominant constant.  Requires
refinement lemmas but no new theory.

### 1.4 Automaton minimization between compiler stages — **M/L**

Quotient the reached state space by bisimulation (or prune with antichain
techniques) after each Boolean combination and projection.  This is the
classical remedy for projection blow-up.  It needs a genuine correctness
proof (language preservation of the quotient), so it is the first item on
this list that is a real formalization block.

### 1.5 Nice-tree dynamic-programming transitions — **L**

Replace the generic sigma-tree automaton pipeline with transitions indexed
directly by the nice-tree constructors (introduce/forget/join), the way
practical Courcelle implementations work.  Largest speedup, but it
re-litigates much of Phases 5–7; only worth it if the project turns toward
being a usable tool.

## 2. Usability: discharging the hypotheses by computation

### 2.1 `Decidable` instances for validity — **S**, best value on this list

`checkMSO2Exec_eq_true_iff` consumes `t.IsDecompFor G` and
`t.HasWidth omega` as hypotheses; today users prove them by hand
(see the `K₂` examples).  All three components are finite searches over
the rose tree and (for coverage) over `Fintype V`:

- `HasBag`/`Occurs`/`OccursPair`: structural recursion on `DecompTree`;
- `RunningIntersection`: recursion with `List.Pairwise` and bag-membership
  tests (decidable given `DecidableEq V`);
- `vertexCoverage`: `∀ v` over a `Fintype`;
- `HasWidth`: quantifies over `HasBag`, decidable via a bag-list
  enumeration (`allBags : DecompTree V → List (List V)`).

With these instances, validity on concrete inputs becomes `by decide`, and
together with §2.2 the pipeline needs no manual proofs at all.

### 2.2 A treewidth heuristic front end — **M**

Compute a decomposition instead of requiring one: a min-degree or min-fill
elimination-ordering heuristic producing a `DecompTree`.  The heuristic
itself needs *no* correctness proof under the certified-checking pattern:
run it uncertified, then validate its output with the `Decidable` instance
of §2.1.  The result is a fully automatic verified pipeline — graph and
formula in, Boolean out — at the price of a heuristic (not optimal) width.

### 2.3 Additional graph input formats — **S**

Constructors from edge lists (`List (V × V)` → `SimpleGraph` with
`DecidableRel`), adjacency matrices over `Fin n`, and optionally a
DIMACS-style text parser feeding them.  Mechanical; pairs naturally with
§2.2.

## 3. Theory: Thatcher–Wright §3 regularity — **M**

The pipeline currently proves MSO → recognizable (the compilation
direction).  TW §3 is the converse: every recognizable tree language is
MSO-definable, completing the Büchi–Elgot–Trakhtenbrot-style equivalence
for trees.  Plan: for a deterministic bottom-up automaton, introduce one
second-order variable per state and write, in the existing tree language
(`labelMem`, parent atoms of
[`treeLanguage/syntax.lean`](../GraphMSO/treeLanguage/syntax.lean)), the
sentence "the nodes admit a state-partition that is transition-consistent
and root-accepting"; prove satisfaction ↔ acceptance.  Self-contained,
touches no existing code, purely additive.  Not needed for Courcelle.

## 4. Benchmarks — **S**, gated on §1

Systematic timing over families (paths, cycles, small trees) × formulas
(the [`Examples.lean`](../GraphMSO/Examples.lean) properties:
colorability, dominating set, vertex cover) × widths, comparing:

- `checkFin`'s `n + 1`-color fallback vs `greedyColoring`'s width-sized
  coloring (alphabet impact);
- the MSO₁ direct path (§1.1) vs the incidence route;
- interpreted vs compiled (§1.2) execution.

Without §1 the reachable input sizes stay trivial, so this item is mostly
meaningful after at least §1.1–1.2.

## 5. Smaller formal-hygiene items

- ~~**Node bound for the executable normalizer**~~ — **done**
  (`DecompTree.normalizeCode_size_le` in
  [`execNormalization.lean`](../GraphMSO/Decomp/execNormalization.lean)).
- ~~**Cost instrumentation of the new stages**~~ — **done**
  ([`Executable/pipelineCost.lean`](../GraphMSO/Executable/pipelineCost.lean)):
  `checkMSO2ExecCosted` charges all five pipeline stages under a documented
  policy, with the exact stage sum and a closed-form total bound
  (`checkMSO2ExecCosted_cost_le`).  Note the incidence-walk term is
  `n · (m + 1)` — the pending-dart threading is quadratic, so a linear-time
  claim for the full front end would additionally need a better threading
  data structure.
- **Merging `changeRoot` with `changeRootOfList`** — **S**.  The
  `Finset`-presented `changeRoot` could be redefined as
  `changeRootOfList` on `toList`s, deriving its five lemmas instead of
  duplicating their proofs (~150-line compression in
  [`normalization.lean`](../GraphMSO/Decomp/normalization.lean)).  Pure
  refactor; touches stable proof-facing code, so it should ride on a full
  build gate.

## Recommended sequences

- **"I want to actually run it":** §2.1 → §1.1 → §1.2 → §4, then §1.3.
  Each step is small, independently verifiable, and visibly widens the set
  of inputs that finish.
- **"I want theoretical completeness":** §3 alone; it is the one remaining
  classical theorem adjacent to the development.
- **"I want a usable tool":** the run sequence above, then §2.2/§2.3,
  and only then consider §1.4–1.5.
