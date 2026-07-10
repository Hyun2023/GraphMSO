import GraphMSO.Decomp.bagColoring
import Mathlib.Data.Set.Card.Arithmetic

/-!
# The edge bound for bounded-width decompositions

A graph admitting a tree-decomposition of width at most `omega` has at most
`omega * |V|` edges.  This is the size lemma of the lecture note used for the
linear-time bookkeeping of the MSO₂ corollary.

The proof differs from the note's minimal-decomposition induction: each edge
is charged to the endpoint whose `BAGS` top node is deeper.  By the
top-node lemmas, the other endpoint then lies in the top bag of the charged
endpoint, a set of size at most `omega` once the charged vertex is removed.
This reuses the existing top-node machinery instead of formalizing
decomposition surgery.
-/

namespace RootedTreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A graph with a rooted tree-decomposition of width at most `omega` has at
most `omega * |V|` edges. -/
theorem edgeSet_ncard_le_of_hasWidth (T : RootedTreeDecomposition G) (omega : ℕ)
    (hwidth : T.toTreeDecomposition.HasWidth omega) :
    G.edgeSet.ncard ≤ omega * Fintype.card V := by
  classical
  set X : Set (V × V) :=
    {p : V × V | p.2 ∈ T.bag (T.topBAGSNode p.1) \ {p.1}} with hX
  -- every edge is the image of a charged pair
  have hsurj : G.edgeSet ⊆ (fun p : V × V => s(p.1, p.2)) '' X := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
        intro he
        rw [SimpleGraph.mem_edgeSet] at he
        have hconf : T.bagConflictGraph.Adj u v := by
          refine ⟨he.ne, ?_⟩
          rcases T.toTreeDecomposition.exists_bag_of_adj he with ⟨t, hut, hvt⟩
          exact ⟨t, hut, hvt⟩
        rcases le_total (T.topBAGSDepth u) (T.topBAGSDepth v) with hle | hle
        · refine ⟨(v, u), ⟨?_, ?_⟩, ?_⟩
          · exact T.mem_bag_topBAGSNode_of_conflict_of_depth_le hconf hle
          · intro hmem
            exact he.ne (by simpa using hmem)
          · exact Sym2.eq_swap
        · refine ⟨(u, v), ⟨?_, ?_⟩, ?_⟩
          · exact T.mem_bag_topBAGSNode_of_conflict_of_depth_le hconf.symm hle
          · intro hmem
            exact he.ne.symm (by simpa using hmem)
          · rfl
  -- the charged pairs live over the top bags
  have hcover : X ⊆ ⋃ v : V, ({v} ×ˢ (T.bag (T.topBAGSNode v) \ {v})) := by
    rintro ⟨v, u⟩ hp
    exact Set.mem_iUnion.2 ⟨v, ⟨rfl, hp⟩⟩
  have hfiber : ∀ v : V, (T.bag (T.topBAGSNode v) \ {v}).ncard ≤ omega := by
    intro v
    have hvbag : v ∈ T.bag (T.topBAGSNode v) := T.mem_bag_topBAGSNode v
    have hdiff : (T.bag (T.topBAGSNode v) \ {v}).ncard =
        (T.bag (T.topBAGSNode v)).ncard - 1 :=
      Set.ncard_diff_singleton_of_mem hvbag
    have hcard : (T.bag (T.topBAGSNode v)).ncard ≤ omega + 1 :=
      hwidth (T.topBAGSNode v)
    omega
  calc G.edgeSet.ncard
      ≤ ((fun p : V × V => s(p.1, p.2)) '' X).ncard :=
        Set.ncard_le_ncard hsurj (Set.toFinite _)
    _ ≤ X.ncard := Set.ncard_image_le (Set.toFinite X)
    _ ≤ (⋃ v : V, ({v} ×ˢ (T.bag (T.topBAGSNode v) \ {v}))).ncard :=
        Set.ncard_le_ncard hcover (Set.toFinite _)
    _ ≤ ∑ v : V, ({v} ×ˢ (T.bag (T.topBAGSNode v) \ {v})).ncard :=
        Set.ncard_iUnion_le_of_fintype _
    _ = ∑ v : V, (T.bag (T.topBAGSNode v) \ {v}).ncard := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Set.singleton_prod,
          Set.ncard_image_of_injective _ (fun x y h => by simpa using h)]
    _ ≤ ∑ _v : V, omega := Finset.sum_le_sum fun v _ => hfiber v
    _ = omega * Fintype.card V := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

end RootedTreeDecomposition

namespace TreeDecomposition

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A graph with a tree-decomposition of width at most `omega` has at most
`omega * |V|` edges. -/
theorem edgeSet_ncard_le_of_hasWidth (D : TreeDecomposition G) (omega : ℕ)
    (hwidth : D.HasWidth omega) :
    G.edgeSet.ncard ≤ omega * Fintype.card V :=
  RootedTreeDecomposition.edgeSet_ncard_le_of_hasWidth
    { D with root := Classical.arbitrary D.Node } omega hwidth

end TreeDecomposition
