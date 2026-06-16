import Mathlib.Combinatorics.SimpleGraph.Clique
import GraphMSO.Semantics

namespace SimpleGraph

variable {V : Type} (G : SimpleGraph V)

/-- A vertex set is independent if no two distinct vertices in it are adjacent. -/
def IsIndependent (S : Set V) : Prop :=
  ∀ u v : V, u ∈ S -> v ∈ S -> u ≠ v -> ¬ G.Adj u v

/-- A vertex set dominates the graph if every vertex is in it or adjacent to one of it. -/
def IsDominating (S : Set V) : Prop :=
  ∀ v : V, v ∈ S ∨ ∃ u : V, u ∈ S ∧ G.Adj u v

/-- A vertex set covers all edges if every edge has an endpoint in it. -/
def IsVertexCover (S : Set V) : Prop :=
  ∀ e : G.edgeSet, ∃ v : V, v ∈ S ∧ v ∈ (e : Sym2 V)

/-- Edge-based bipartiteness, phrased to match the MSO2 formula directly. -/
def IsBipartiteByEdges : Prop :=
  ∃ S : Set V,
    ∀ e : G.edgeSet, ∃ u v : V,
      u ∈ S ∧ v ∉ S ∧ u ∈ (e : Sym2 V) ∧ v ∈ (e : Sym2 V)

/-- A perfect matching is an edge set incident to each vertex at exactly one edge. -/
def HasPerfectMatching (M : Set G.edgeSet) : Prop :=
  ∀ v : V, ∃! e : G.edgeSet, e ∈ M ∧ v ∈ (e : Sym2 V)

/-- The edge set `F` contains exactly two edges incident to `v`. -/
def HasExactlyTwoIncidentEdgesIn (F : Set G.edgeSet) (v : V) : Prop :=
  ∃ e₀ e₁ : G.edgeSet,
    e₀ ∈ F ∧ e₁ ∈ F ∧
    v ∈ (e₀ : Sym2 V) ∧ v ∈ (e₁ : Sym2 V) ∧ e₀ ≠ e₁ ∧
    ∀ e : G.edgeSet, e ∈ F -> v ∈ (e : Sym2 V) -> e = e₀ ∨ e = e₁

/-- No edge has one endpoint in `S` and the other in `T`. -/
def HasNoEdgesBetween (S T : Set V) : Prop :=
  ∀ u v : V, u ∈ S -> v ∈ T -> ¬ G.Adj u v

/-- `S` and `T` form a nontrivial partition of all vertices. -/
def IsNontrivialPartition (S T : Set V) : Prop :=
  S.Nonempty ∧ T.Nonempty ∧
    (∀ v : V, v ∈ S ∨ v ∈ T) ∧
    (∀ v : V, v ∈ S -> v ∈ T -> False)

/-- The graph is disconnected if its vertices split into two nonempty parts
with no edges between them. -/
def IsDisconnectedByPartition : Prop :=
  ∃ S T : Set V, IsNontrivialPartition S T ∧ G.HasNoEdgesBetween S T

/-- Connectivity, defined as the negation of the partition-based disconnectedness. -/
def IsConnectedByPartition : Prop :=
  ¬ G.IsDisconnectedByPartition

/-- The edge set `F` has an edge crossing from `S` to `T`. -/
def HasCrossingEdgeIn (F : Set G.edgeSet) (S T : Set V) : Prop :=
  ∃ e : G.edgeSet, e ∈ F ∧
    ∃ u v : V, u ∈ S ∧ v ∈ T ∧ u ∈ (e : Sym2 V) ∧ v ∈ (e : Sym2 V)

/-- The spanning subgraph with edge set `F` is connected, phrased by cuts:
every nontrivial partition of the vertices has a selected crossing edge. -/
def EdgeSetConnectedSpanning (F : Set G.edgeSet) : Prop :=
  ∀ S T : Set V, IsNontrivialPartition S T -> G.HasCrossingEdgeIn F S T

/-- A Hamiltonian cycle, represented as a selected edge set: every vertex has
degree exactly two in the selected edges, and those selected edges are connected. -/
def HasHamiltonianCycleByEdges : Prop :=
  ∃ F : Set G.edgeSet,
    (∀ v : V, G.HasExactlyTwoIncidentEdgesIn F v) ∧
    G.EdgeSetConnectedSpanning F

/-- A vertex belongs to one of the listed color classes. -/
def IsInSomeColor (v : V) : List (Set V) -> Prop
  | [] => False
  | S :: Ss => v ∈ S ∨ IsInSomeColor v Ss

/-- The listed color classes cover all vertices. -/
def ColorClassesCover (colors : List (Set V)) : Prop :=
  ∀ v : V, IsInSomeColor v colors

/-- Two color classes are disjoint. -/
def ColorClassesDisjoint (S T : Set V) : Prop :=
  ∀ v : V, v ∈ S -> v ∈ T -> False

/-- One color class is disjoint from every class in the list. -/
def ColorClassDisjointFrom (S : Set V) : List (Set V) -> Prop
  | [] => True
  | T :: Ts => ColorClassesDisjoint S T ∧ ColorClassDisjointFrom S Ts

/-- The listed color classes are pairwise disjoint. -/
def ColorClassesPairwiseDisjoint : List (Set V) -> Prop
  | [] => True
  | S :: Ss => ColorClassDisjointFrom S Ss ∧ ColorClassesPairwiseDisjoint Ss

/-- Every listed color class is independent. -/
def ColorClassesIndependent (G : SimpleGraph V) : List (Set V) -> Prop
  | [] => True
  | S :: Ss => G.IsIndependent S ∧ ColorClassesIndependent G Ss

/-- A coloring is a partition of the vertex set into independent color classes. -/
def IsColoringBySets (colors : List (Set V)) : Prop :=
  ColorClassesCover colors ∧
  ColorClassesPairwiseDisjoint colors ∧
  G.ColorClassesIndependent colors

/-- The graph is 3-colorable if it has three color classes forming a coloring. -/
def IsThreeColorableBySets : Prop :=
  ∃ S T U : Set V, G.IsColoringBySets [S, T, U]

end SimpleGraph

namespace GraphMSO

namespace Examples

open Formula
open Semantics

def x : FOVar := 0
def y : FOVar := 1
def z : FOVar := 2
def X : SOVar := 0
def Y : SOVar := 1
def Z : SOVar := 2
def e0 : EdgeFOVar := 0
def e1 : EdgeFOVar := 1
def e2 : EdgeFOVar := 2
def E0 : EdgeSOVar := 0

/-- "The set variable `X` is nonempty." -/
def nonemptySet (X : SOVar) : Formula :=
  existsFO x (inSet x X)

/-- "The set variable `X` is a clique." -/
def clique (X : SOVar) : Formula :=
  forallFOs [x, y]
    (impl
      (conj (inSet x X) (conj (inSet y X) (notEqual x y)))
      (edge x y))

/-- "The set variable `X` is independent." -/
def independent (X : SOVar) : Formula :=
  forallFOs [x, y]
    (impl
      (conj (inSet x X) (conj (inSet y X) (edge x y)))
      (equal x y))

/-- "The set variable `X` is a dominating set." -/
def dominating (X : SOVar) : Formula :=
  forallFO x
    (disj
      (inSet x X)
      (existsFO y (conj (inSet y X) (edge y x))))

/-- "The set variables `X` and `Y` cover all vertices." -/
def coverAll (X Y : SOVar) : Formula :=
  forallFO x (disj (inSet x X) (inSet x Y))

/-- "The set variables `X` and `Y` are disjoint." -/
def disjointSets (X Y : SOVar) : Formula :=
  forallFO x (impl (inSet x X) (neg (inSet x Y)))

/-- "The set variables `X` and `Y` form a nontrivial partition of the vertices." -/
def nontrivialPartition (X Y : SOVar) : Formula :=
  conj (nonemptySet X)
    (conj (nonemptySet Y)
      (conj (coverAll X Y) (disjointSets X Y)))

/-- "There are no edges between the set variables `X` and `Y`." -/
def noEdgesBetween (X Y : SOVar) : Formula :=
  forallFOs [x, y] (impl (conj (inSet x X) (inSet y Y)) (neg (edge x y)))

/-- "The graph is disconnected: there is a nontrivial partition with no crossing edges." -/
def disconnected : Formula :=
  existsSO X (existsSO Y (conj (nontrivialPartition X Y) (noEdgesBetween X Y)))

/-- "The graph is connected." -/
def connected : Formula :=
  neg disconnected

/-- "The vertex variable `v` belongs to one of the listed set variables." -/
def inSomeColor (v : FOVar) : List SOVar -> Formula
  | [] => false_
  | X :: Xs => disj (inSet v X) (inSomeColor v Xs)

/-- "The listed set variables cover all vertices." -/
def colorClassesCover (colors : List SOVar) : Formula :=
  forallFO x (inSomeColor x colors)

/-- "The set variable `X` is disjoint from every set variable in the list." -/
def colorClassDisjointFrom (X : SOVar) : List SOVar -> Formula
  | [] => true_
  | Y :: Ys => conj (disjointSets X Y) (colorClassDisjointFrom X Ys)

/-- "The listed set variables are pairwise disjoint." -/
def colorClassesPairwiseDisjoint : List SOVar -> Formula
  | [] => true_
  | X :: Xs => conj (colorClassDisjointFrom X Xs) (colorClassesPairwiseDisjoint Xs)

/-- "Every listed set variable is independent." -/
def colorClassesIndependent : List SOVar -> Formula
  | [] => true_
  | X :: Xs => conj (independent X) (colorClassesIndependent Xs)

/-- "The listed set variables form color classes: a partition into independent sets." -/
def coloring (colors : List SOVar) : Formula :=
  conj (colorClassesCover colors)
    (conj (colorClassesPairwiseDisjoint colors) (colorClassesIndependent colors))

/-- A convenient open formula whose first `k` second-order variables are color classes. -/
def kColoring (k : Nat) : Formula :=
  coloring (List.range k)

/-- Existentially quantify a formula over a list of vertex-set variables. -/
def existsSOs : List SOVar -> Formula -> Formula
  | [], phi => phi
  | X :: Xs, phi => existsSO X (existsSOs Xs phi)

/-- A closed sentence saying that there exists a coloring using the first `k`
second-order variables as color classes. For each fixed `k`, this is one finite
MSO formula. -/
def kColorable (k : Nat) : Formula :=
  existsSOs (List.range k) (kColoring k)

/-- The closed sentence saying that the graph is 3-colorable. -/
def threeColorable : Formula :=
  existsSO X (existsSO Y (existsSO Z (coloring [X, Y, Z])))

theorem threeColorable_eq_kColorable_three :
    threeColorable = kColorable 3 := by
  rfl

/-- "There exists a nonempty clique." -/
def hasNonemptyClique : Formula :=
  existsSO X (conj (nonemptySet X) (clique X))

theorem eval_clique_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    EvalAt (clique X) G rho ↔ G.IsClique (rho.so X) := by
  simp [clique, SimpleGraph.IsClique, Set.Pairwise, Formula.forallFOs, Formula.notEqual,
    Semantics.EvalAt, x, y, Assignment.updateFO]
  constructor
  · intro h u hu v hv hne
    exact h u v hu hv hne
  · intro h u v hu hv hne
    exact h hu hv hne

theorem eval_independent_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    EvalAt (independent X) G rho ↔ G.IsIndependent (rho.so X) := by
  classical
  simp [independent, SimpleGraph.IsIndependent, Formula.forallFOs, Semantics.EvalAt, x, y,
    Assignment.updateFO]
  constructor
  · intro h u v hSu hSv hne hAdj
    exact hne (h u v hSu hSv hAdj)
  · intro h u v hSu hSv hAdj
    by_contra hne
    exact h u v hSu hSv hne hAdj

theorem eval_dominating_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    EvalAt (dominating X) G rho ↔ G.IsDominating (rho.so X) := by
  simp [dominating, SimpleGraph.IsDominating, Semantics.EvalAt, x, y, Assignment.updateFO]

theorem eval_disconnected_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    EvalAt disconnected G rho ↔ G.IsDisconnectedByPartition := by
  simp [disconnected, nontrivialPartition, nonemptySet, coverAll, disjointSets, noEdgesBetween,
    SimpleGraph.IsDisconnectedByPartition, SimpleGraph.IsNontrivialPartition,
    SimpleGraph.HasNoEdgesBetween,
    Set.Nonempty, Formula.forallFOs, Semantics.EvalAt, X, Y, x, y, Assignment.updateSO,
    Assignment.updateFO]

theorem eval_connected_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    EvalAt connected G rho ↔ G.IsConnectedByPartition := by
  simpa [connected, SimpleGraph.IsConnectedByPartition, Semantics.EvalAt]
    using not_congr (eval_disconnected_iff G rho)

theorem eval_inSomeColor_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (v : FOVar) (colors : List SOVar) :
    EvalAt (inSomeColor v colors) G rho ↔
      SimpleGraph.IsInSomeColor (rho.fo v) (colors.map rho.so) := by
  induction colors with
  | nil =>
      simp [inSomeColor, SimpleGraph.IsInSomeColor, Semantics.EvalAt]
  | cons X Xs ih =>
      simp [inSomeColor, SimpleGraph.IsInSomeColor, Semantics.EvalAt, ih]

theorem eval_colorClassesCover_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (colors : List SOVar) :
    EvalAt (colorClassesCover colors) G rho ↔
      SimpleGraph.ColorClassesCover (colors.map rho.so) := by
  simp [colorClassesCover, SimpleGraph.ColorClassesCover, Semantics.EvalAt,
    eval_inSomeColor_iff, x, Assignment.updateFO]

theorem eval_disjointSets_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X Y : SOVar) :
    EvalAt (disjointSets X Y) G rho ↔
      SimpleGraph.ColorClassesDisjoint (rho.so X) (rho.so Y) := by
  simp [disjointSets, SimpleGraph.ColorClassesDisjoint, Semantics.EvalAt, x,
    Assignment.updateFO]

theorem eval_colorClassDisjointFrom_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) (colors : List SOVar) :
    EvalAt (colorClassDisjointFrom X colors) G rho ↔
      SimpleGraph.ColorClassDisjointFrom (rho.so X) (colors.map rho.so) := by
  induction colors with
  | nil =>
      simp [colorClassDisjointFrom, SimpleGraph.ColorClassDisjointFrom, Formula.true_,
        Semantics.EvalAt]
  | cons Y Ys ih =>
      simp [colorClassDisjointFrom, SimpleGraph.ColorClassDisjointFrom,
        eval_disjointSets_iff, ih]

theorem eval_colorClassesPairwiseDisjoint_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (colors : List SOVar) :
    EvalAt (colorClassesPairwiseDisjoint colors) G rho ↔
      SimpleGraph.ColorClassesPairwiseDisjoint (colors.map rho.so) := by
  induction colors with
  | nil =>
      simp [colorClassesPairwiseDisjoint, SimpleGraph.ColorClassesPairwiseDisjoint,
        Formula.true_, Semantics.EvalAt]
  | cons X Xs ih =>
      simp [colorClassesPairwiseDisjoint, SimpleGraph.ColorClassesPairwiseDisjoint,
        eval_colorClassDisjointFrom_iff, ih]

theorem eval_colorClassesIndependent_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (colors : List SOVar) :
    EvalAt (colorClassesIndependent colors) G rho ↔
      G.ColorClassesIndependent (colors.map rho.so) := by
  induction colors with
  | nil =>
      simp [colorClassesIndependent, SimpleGraph.ColorClassesIndependent, Formula.true_,
        Semantics.EvalAt]
  | cons X Xs ih =>
      simp [colorClassesIndependent, SimpleGraph.ColorClassesIndependent,
        eval_independent_iff, ih]

theorem eval_coloring_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (colors : List SOVar) :
    EvalAt (coloring colors) G rho ↔
      G.IsColoringBySets (colors.map rho.so) := by
  simp [coloring, SimpleGraph.IsColoringBySets, Semantics.EvalAt,
    eval_colorClassesCover_iff, eval_colorClassesPairwiseDisjoint_iff,
    eval_colorClassesIndependent_iff]

theorem eval_kColoring_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (k : Nat) :
    EvalAt (kColoring k) G rho ↔
      G.IsColoringBySets ((List.range k).map rho.so) := by
  simp [kColoring, eval_coloring_iff]

theorem eval_threeColorable_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    EvalAt threeColorable G rho ↔ G.IsThreeColorableBySets := by
  simp [threeColorable, SimpleGraph.IsThreeColorableBySets, Semantics.EvalAt,
    eval_coloring_iff, X, Y, Z, Assignment.updateSO]

theorem eval_kColorable_three_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    EvalAt (kColorable 3) G rho ↔ G.IsThreeColorableBySets := by
  simpa [← threeColorable_eq_kColorable_three] using eval_threeColorable_iff G rho

theorem clique_no_freeFO (X : SOVar) (a : FOVar) :
    Not (Formula.FreeFO (clique X) a) := by
  simp [clique, Formula.forallFOs, Formula.FreeFO, Formula.notEqual, x, y]
  intro h0 h1
  exact ⟨⟨h0, h1, h0, h1⟩, h0, h1⟩

theorem clique_freeSO_iff (X Y : SOVar) :
    Formula.FreeSO (clique X) Y ↔ Y = X := by
  simp [clique, Formula.forallFOs, Formula.FreeSO, Formula.notEqual, x, y]

theorem hasNonemptyClique_closed : Formula.Closed hasNonemptyClique := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    simp [hasNonemptyClique, nonemptySet, clique, Formula.forallFOs, Formula.FreeFO,
      Formula.notEqual, x, y, X]
    intro h0 h1
    exact ⟨⟨h0, h1, h0, h1⟩, h0, h1⟩
  · intro Z
    simp [hasNonemptyClique, nonemptySet, clique, Formula.forallFOs, Formula.FreeSO,
      Formula.notEqual, x, y, X]
  · intro e
    simp [hasNonemptyClique, nonemptySet, clique, Formula.forallFOs, Formula.FreeEdgeFO,
      Formula.notEqual, x, y, X]
  · intro E_var
    simp [hasNonemptyClique, nonemptySet, clique, Formula.forallFOs, Formula.FreeEdgeSO,
      Formula.notEqual, x, y, X]

/-- "The edge `e` is incident to exactly one vertex." In a `SimpleGraph.edgeSet`,
this formula is unsatisfiable, but it remains useful as MSO2 syntax. -/
def isLoop (e : EdgeFOVar) : Formula :=
  existsFO y (conj (inc y e) (forallFO z (impl (inc z e) (equal z y))))

/-- "There is a unique edge in `M` incident to vertex variable `v`." -/
def uniqueIncEdgeIn (v : FOVar) (M : EdgeSOVar) : Formula :=
  existsEdgeFO e0 (conj (inEdgeSet e0 M) (conj (inc v e0)
    (forallEdgeFO e1 (impl (conj (inEdgeSet e1 M) (inc v e1)) (equalEdge e1 e0)))))

/-- "The edge set variable `M` is a perfect matching." -/
def perfectMatching (M : EdgeSOVar) : Formula :=
  conj (forallEdgeFO e0 (impl (inEdgeSet e0 M) (neg (isLoop e0))))
       (forallFO x (uniqueIncEdgeIn x M))

/-- "Exactly two edges in `M` are incident to vertex variable `v`." -/
def exactlyTwoIncEdgesIn (v : FOVar) (M : EdgeSOVar) : Formula :=
  existsEdgeFO e0
    (existsEdgeFO e1
      (conj (inEdgeSet e0 M)
        (conj (inEdgeSet e1 M)
          (conj (inc v e0)
            (conj (inc v e1)
              (conj (neg (equalEdge e0 e1))
                (forallEdgeFO e2
                  (impl (conj (inEdgeSet e2 M) (inc v e2))
                    (disj (equalEdge e2 e0) (equalEdge e2 e1))))))))))

/-- "Every vertex has exactly two incident edges in `M`." -/
def everyVertexExactlyTwoIncEdgesIn (M : EdgeSOVar) : Formula :=
  forallFO x (exactlyTwoIncEdgesIn x M)

/-- "Some selected edge in `M` crosses from vertex set `X` to vertex set `Y`." -/
def crossingEdgeIn (M : EdgeSOVar) (X Y : SOVar) : Formula :=
  existsEdgeFO e0
    (conj (inEdgeSet e0 M)
      (existsFO x (existsFO y
        (conj (inSet x X)
          (conj (inSet y Y) (conj (inc x e0) (inc y e0)))))))

/-- "The selected edge set `M` is connected as a spanning subgraph." -/
def edgeSetConnected (M : EdgeSOVar) : Formula :=
  forallSO X (forallSO Y
    (impl (nontrivialPartition X Y) (crossingEdgeIn M X Y)))

/-- "The graph has a Hamiltonian cycle, represented by its selected edge set." -/
def hamiltonian : Formula :=
  existsEdgeSO E0
    (conj (everyVertexExactlyTwoIncEdgesIn E0) (edgeSetConnected E0))

theorem eval_exactlyTwoIncEdgesIn_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (v : FOVar) (M : EdgeSOVar) :
    EvalAt (exactlyTwoIncEdgesIn v M) G rho ↔
      G.HasExactlyTwoIncidentEdgesIn (rho.eso M) (rho.fo v) := by
  simp [exactlyTwoIncEdgesIn, SimpleGraph.HasExactlyTwoIncidentEdgesIn, Semantics.EvalAt,
    e0, e1, e2, Assignment.updateEdgeFO]

theorem eval_everyVertexExactlyTwoIncEdgesIn_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (M : EdgeSOVar) :
    EvalAt (everyVertexExactlyTwoIncEdgesIn M) G rho ↔
      ∀ v : V, G.HasExactlyTwoIncidentEdgesIn (rho.eso M) v := by
  simp [everyVertexExactlyTwoIncEdgesIn, Semantics.EvalAt, x, Assignment.updateFO,
    eval_exactlyTwoIncEdgesIn_iff]

theorem eval_crossingEdgeIn_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (M : EdgeSOVar) (X Y : SOVar) :
    EvalAt (crossingEdgeIn M X Y) G rho ↔
      G.HasCrossingEdgeIn (rho.eso M) (rho.so X) (rho.so Y) := by
  simp [crossingEdgeIn, SimpleGraph.HasCrossingEdgeIn, Semantics.EvalAt, e0, x, y,
    Assignment.updateEdgeFO, Assignment.updateFO]

theorem eval_edgeSetConnected_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (M : EdgeSOVar) :
    EvalAt (edgeSetConnected M) G rho ↔
      G.EdgeSetConnectedSpanning (rho.eso M) := by
  simp [edgeSetConnected, nontrivialPartition, nonemptySet, coverAll, disjointSets,
    SimpleGraph.EdgeSetConnectedSpanning, SimpleGraph.IsNontrivialPartition, Set.Nonempty,
    Semantics.EvalAt, X, Y, x, Assignment.updateSO, Assignment.updateFO,
    eval_crossingEdgeIn_iff]

theorem eval_hamiltonian_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    EvalAt hamiltonian G rho ↔ G.HasHamiltonianCycleByEdges := by
  simp [hamiltonian, SimpleGraph.HasHamiltonianCycleByEdges, Semantics.EvalAt, E0,
    Assignment.updateEdgeSO, eval_everyVertexExactlyTwoIncEdgesIn_iff,
    eval_edgeSetConnected_iff]

def vertexCover (X : SOVar) : Formula :=
  forallEdgeFO e0 (existsFO x (conj (inSet x X) (inc x e0)))

theorem eval_vertexCover_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) (X : SOVar) :
    EvalAt (vertexCover X) G rho ↔ G.IsVertexCover (rho.so X) := by
  simp [vertexCover, SimpleGraph.IsVertexCover, Semantics.EvalAt, x, e0,
    Assignment.updateFO, Assignment.updateEdgeFO]

def bipartite : Formula :=
  existsSO X (forallEdgeFO e0 (existsFO x (existsFO y
    (conj (inSet x X) (conj (neg (inSet y X)) (conj (inc x e0) (inc y e0)))))))

theorem eval_bipartite_iff {V : Type} (G : SimpleGraph V)
    (rho : Assignment V G.edgeSet) :
    EvalAt bipartite G rho ↔ G.IsBipartiteByEdges := by
  simp [bipartite, SimpleGraph.IsBipartiteByEdges, Semantics.EvalAt, X, e0, x, y,
    Assignment.updateSO, Assignment.updateFO, Assignment.updateEdgeFO]

/-- A two-vertex type for smoke-test examples. -/
inductive Two where
  | left : Two
  | right : Two
  deriving Repr, DecidableEq

def twoGraph : SimpleGraph Two :=
  ⊤

def twoEdge : twoGraph.edgeSet :=
  ⟨s(Two.left, Two.right), by simp [twoGraph]⟩

def allTrueAssignment : Assignment Two twoGraph.edgeSet where
  fo := fun _ => Two.left
  so := fun _ => Set.univ
  efo := fun _ => twoEdge
  eso := fun _ => Set.univ

example : EvalAt Formula.true_ twoGraph allTrueAssignment := by
  exact evalAt_true twoGraph allTrueAssignment

example : Eval Formula.true_ twoGraph := by
  exact eval_true twoGraph

example : EvalAt (forallFO x (inSet x X)) twoGraph allTrueAssignment := by
  simp [Semantics.EvalAt, allTrueAssignment, x, X]

end Examples

end GraphMSO
