import GraphMSO.Decomp.encoding
import GraphMSO.treeLanguage.semantics

/-!
# Σ-trees as models of the tree language

A `SigmaTree` is a model of the tree MSO language over the alphabet of
Σ-letters: its nodes, its child relation, and its letter labeling.  For the
Σ-tree encoding a bag-colored decomposition, this file identifies the model
data with the decomposition data:

* the parent relation of the encoded model is the decomposition's child
  relation (definitionally), and
* the symmetrized parent graph of the encoded model is the decomposition
  tree itself (`encode_toTreeModel_graph`).

Consequently the `conn`/`top`/`dangle` characterizations of
`GraphMSO.treeLanguage.semantics` evaluate, over an encoding, to statements
about connectivity in the decomposition tree — the form consumed by the
defining-pair layer.
-/

namespace SigmaTree

variable {P : Type*} {omega : ℕ}

/-- View a Σ-tree as a model of the tree language over the letter
alphabet. -/
def toTreeModel (S : SigmaTree P omega) :
    GraphMSO.TreeLanguage.TreeModel (SigmaLetter P omega) where
  Node := S.Node
  parentRel := S.IsChild
  label := S.letter

@[simp] theorem toTreeModel_node (S : SigmaTree P omega) :
    S.toTreeModel.Node = S.Node :=
  rfl

@[simp] theorem toTreeModel_parentRel (S : SigmaTree P omega) :
    S.toTreeModel.parentRel = S.IsChild :=
  rfl

@[simp] theorem toTreeModel_label (S : SigmaTree P omega) :
    S.toTreeModel.label = S.letter :=
  rfl

end SigmaTree

namespace RootedTreeDecomposition

open GraphMSO.TreeLanguage

variable {V : Type*} [Fintype V] {G : SimpleGraph V}
variable {P : Type*} {omega : ℕ}

variable (T : RootedTreeDecomposition G) (vpred : P → V → Prop)
    (color : V -> BagColorSet omega) (hcolor : T.IsBagColoring color)

/-- The parent relation of the encoded tree model is the child relation of
the decomposition. -/
theorem encode_toTreeModel_parentRel :
    (T.encode vpred color hcolor).toTreeModel.parentRel =
      fun parent child => T.IsChild parent child :=
  rfl

/-- The letter labeling of the encoded tree model. -/
theorem encode_toTreeModel_label :
    (T.encode vpred color hcolor).toTreeModel.label =
      T.encodeLetter vpred color hcolor :=
  rfl

/-- The symmetrized parent graph of the encoded tree model is the
decomposition tree. -/
theorem encode_toTreeModel_graph :
    (T.encode vpred color hcolor).toTreeModel.graph = T.T := by
  ext a b
  rw [TreeModel.graph_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact IsChild.adj h
    · exact (IsChild.adj h).symm
  · intro hadj
    refine ⟨hadj.ne, ?_⟩
    exact (T.adj_iff_isChild_or_isChild.mp hadj).imp id id

end RootedTreeDecomposition
