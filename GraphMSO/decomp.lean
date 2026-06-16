import Mathlib.Data.Set.Basic

namespace GraphMSO

/-- A rooted binary tree whose nodes are bags of vertices. -/
inductive TreeDecomposition (V : Type) where
  | leaf (bag : Set V) : TreeDecomposition V
  | node (bag : Set V) (left right : TreeDecomposition V) : TreeDecomposition V

namespace TreeDecomposition
