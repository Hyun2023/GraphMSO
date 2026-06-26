import GraphMSO.Decomp.nice

/-!
The `BAGS` connected subgraph associated with a graph vertex.

For a vertex `v`, `BAGS(v)` is the set of decomposition nodes whose bags
contain `v`.  The tree-decomposition connectivity axiom says that this set
induces a connected subgraph of the decomposition tree.
-/

namespace NiceTreeDecomposition

variable {V : Type*} {G : SimpleGraph V}

/-! ## Main definition: BAGS -/

/-- `BAGS(v)`: decomposition nodes whose bags contain the graph vertex `v`. -/
def BAGS (N : NiceTreeDecomposition (G := G)) (v : V) : Set N.T.decomp.Node :=
  N.T.bagsOf v

/-! ## Main definition: BAGSGraph -/

/-- The subgraph of the decomposition tree induced by `BAGS(v)`. -/
def BAGSGraph (N : NiceTreeDecomposition (G := G)) (v : V) :
    SimpleGraph (N.BAGS v) :=
  N.T.decomp.T.induce (N.BAGS v)

/-- `BAGS(v)` is nonempty because every graph vertex appears in some bag. -/
theorem BAGS_nonempty (N : NiceTreeDecomposition (G := G)) (v : V) :
    (N.BAGS v).Nonempty := by
  simpa [BAGS, RootedTreeDecomposition.bagsOf] using N.T.decomp.bagsOf_nonempty v

/-- `BAGS(v)` induces a preconnected graph by the tree-decomposition axiom. -/
theorem BAGS_preconnected (N : NiceTreeDecomposition (G := G)) (v : V) :
    (N.BAGSGraph v).Preconnected := by
  simpa [BAGSGraph, BAGS, RootedTreeDecomposition.bagsOf] using
    N.T.decomp.bagsOf_preconnected v

/-- `BAGS(v)` induces a connected subgraph of the decomposition tree. -/
theorem BAGS_connected (N : NiceTreeDecomposition (G := G)) (v : V) :
    (N.BAGSGraph v).Connected := by
  refine { preconnected := N.BAGS_preconnected v, nonempty := ?_ }
  rcases N.BAGS_nonempty v with ⟨t, ht⟩
  exact ⟨⟨t, ht⟩⟩

end NiceTreeDecomposition
