import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Ranked alphabets and finite terms

This file starts the tree-automata development needed for the effective
MSO–tree-automaton correspondence (Thatcher–Wright), following the working
extraction in `Courcelle/Thatcher-Wright-expanding.tex`.

* `RankedAlphabet` is a *species* in Thatcher–Wright's terminology: a type of
  function symbols with an arity for each symbol.
* `RankedAlphabet.Term` is the type of finite terms over a ranked alphabet;
  these are exactly the finite ranked trees that tree automata run on.
* `RankedAlphabet.Hom` is an arity-preserving symbol map (a *projection* in
  Thatcher–Wright), and `RankedAlphabet.Term.map` applies it nodewise to a
  term.

Finiteness of the alphabet is not baked into the structure; theorems assume
`Finite S.Symb` only where they need it.
-/

universe u v

/-- A ranked alphabet — a *species* in Thatcher–Wright: a type of function
symbols together with an arity for each symbol.  Nullary symbols play the role
of constants. -/
structure RankedAlphabet : Type (u + 1) where
  /-- The type of function symbols. -/
  Symb : Type u
  /-- The number of children of each symbol. -/
  arity : Symb → ℕ

namespace RankedAlphabet

/-- Finite terms over a ranked alphabet: a symbol applied to one child term
per arity position.  Terms rooted at nullary symbols are the leaves. -/
inductive Term (S : RankedAlphabet.{u}) : Type u
  | node (f : S.Symb) (children : Fin (S.arity f) → Term S)

/-- An arity-preserving map of ranked alphabets — a *projection* in
Thatcher–Wright's terminology. -/
structure Hom (S T : RankedAlphabet.{u}) : Type u where
  /-- The underlying map on symbols. -/
  toFun : S.Symb → T.Symb
  /-- The map preserves arities. -/
  arity_eq : ∀ f : S.Symb, T.arity (toFun f) = S.arity f

instance (S T : RankedAlphabet.{u}) : CoeFun (S.Hom T) (fun _ => S.Symb → T.Symb) :=
  ⟨Hom.toFun⟩

namespace Term

variable {S T : RankedAlphabet.{u}}

/-- Apply an arity-preserving symbol map to every node of a term. -/
def map (π : S.Hom T) : S.Term → T.Term
  | node f ts => node (π.toFun f) (fun i => (ts (Fin.cast (π.arity_eq f) i)).map π)

@[simp] theorem map_node (π : S.Hom T) (f : S.Symb)
    (ts : Fin (S.arity f) → S.Term) :
    (node f ts).map π =
      node (π.toFun f) (fun i => (ts (Fin.cast (π.arity_eq f) i)).map π) :=
  rfl

/-- The depth of a term: `1` at a leaf, and one more than the deepest child
otherwise. -/
def depth : S.Term → ℕ
  | node _ ts => (Finset.univ.sup fun i => (ts i).depth) + 1

theorem depth_node (f : S.Symb) (ts : Fin (S.arity f) → S.Term) :
    (node f ts).depth = (Finset.univ.sup fun i => (ts i).depth) + 1 :=
  rfl

theorem depth_pos (t : S.Term) : 0 < t.depth := by
  cases t with
  | node f ts => exact Nat.succ_pos _

/-- Children are strictly shallower than their parent. -/
theorem depth_lt_depth_node (f : S.Symb) (ts : Fin (S.arity f) → S.Term)
    (i : Fin (S.arity f)) :
    (ts i).depth < (node f ts).depth := by
  rw [depth_node]
  exact Nat.lt_succ_of_le
    (Finset.le_sup (f := fun i => (ts i).depth) (Finset.mem_univ i))

/-- The depth of a node is at most `k + 1` iff every child has depth at most
`k`. -/
theorem depth_node_le_succ_iff (f : S.Symb) (ts : Fin (S.arity f) → S.Term)
    (k : ℕ) :
    (node f ts).depth ≤ k + 1 ↔ ∀ i, (ts i).depth ≤ k := by
  rw [depth_node, Nat.add_le_add_iff_right, Finset.sup_le_iff]
  simp

end Term

end RankedAlphabet
