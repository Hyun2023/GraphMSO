import GraphMSO.Executable.graph
import GraphMSO.Executable.sigma
import GraphMSO.Decomp.nice_inductive
import GraphMSO.Automata.orderedEncoding

/-!
# Executable encoding of constructor-coded nice trees

The encoder in this file follows the constructor tree directly.  In
particular, it does not compute paths or parents in the proof-facing rooted
tree decomposition.
-/

namespace GraphMSO.Executable

universe u v

variable {P : Type u} {V : Type v} {omega : ℕ}

/-- Executable Boolean existential search over a finite bag. -/
def encodeAny [DecidableEq V] (s : Finset V) (predicate : V → Bool) : Bool :=
  s.fold Bool.or false predicate

/-- Build the executable sigma letter carried by one decomposition node. -/
def encodeLetter [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    (bag adhesion : Finset V) : ExecSigmaLetter P omega where
  present i := encodeAny bag fun x => decide (color x = i)
  root i := encodeAny adhesion fun x => decide (color x = i)
  adj i j := encodeAny bag fun x => encodeAny bag fun y =>
    decide (color x = i) && decide (color y = j) && X.adj x y
  tag p i := encodeAny bag fun x => decide (color x = i) && X.pred p x

@[simp] theorem encodeLetter_present [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    (bag adhesion : Finset V) (i : Fin (omega + 1)) :
    (encodeLetter X color bag adhesion).present i =
      encodeAny bag (fun x => decide (color x = i)) :=
  rfl

@[simp] theorem encodeLetter_root [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    (bag adhesion : Finset V) (i : Fin (omega + 1)) :
    (encodeLetter X color bag adhesion).root i =
      encodeAny adhesion (fun x => decide (color x = i)) :=
  rfl

@[simp] theorem encodeLetter_adj [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    (bag adhesion : Finset V) (i j : Fin (omega + 1)) :
    (encodeLetter X color bag adhesion).adj i j =
      encodeAny bag (fun x => encodeAny bag fun y =>
        decide (color x = i) && decide (color y = j) && X.adj x y) :=
  rfl

@[simp] theorem encodeLetter_tag [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    (bag adhesion : Finset V) (p : P) (i : Fin (omega + 1)) :
    (encodeLetter X color bag adhesion).tag p i =
      encodeAny bag (fun x => decide (color x = i) && X.pred p x) :=
  rfl

/-- Encode a constructor-coded nice tree while carrying the current bag and
its adhesion as explicit finite data.

Going from a node to its child reverses the constructor's bag update: an
`introduce` node erases its introduced vertex, a `forget` node inserts its
forgotten vertex, and a `join` passes the same bag to both children. -/
def encodeAux [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1)) :
    {rootBag : Set V} → InductiveNiceTree V rootBag →
      Finset V → Finset V → BinTree (ExecSigmaLetter P omega)
  | _, .leaf, bag, adhesion =>
      .node (encodeLetter X color bag adhesion) .nil .nil
  | _, .introduce v child _, bag, adhesion =>
      .node (encodeLetter X color bag adhesion)
        (encodeAux X color child (bag.erase v) (bag.erase v)) .nil
  | _, .forget v child _, bag, adhesion =>
      .node (encodeLetter X color bag adhesion)
        (encodeAux X color child (insert v bag) bag) .nil
  | _, .join left right, bag, adhesion =>
      .node (encodeLetter X color bag adhesion)
        (encodeAux X color left bag bag)
        (encodeAux X color right bag bag)

@[simp] theorem encodeAux_leaf [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    (bag adhesion : Finset V) :
    encodeAux X color (.leaf : InductiveNiceTree V ∅) bag adhesion =
      .node (encodeLetter X color bag adhesion) .nil .nil :=
  rfl

@[simp] theorem encodeAux_introduce [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    {childBag : Set V} (v : V) (child : InductiveNiceTree V childBag)
    (fresh : v ∉ childBag) (bag adhesion : Finset V) :
    encodeAux X color (.introduce v child fresh) bag adhesion =
      .node (encodeLetter X color bag adhesion)
        (encodeAux X color child (bag.erase v) (bag.erase v)) .nil :=
  rfl

@[simp] theorem encodeAux_forget [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    {childBag : Set V} (v : V) (child : InductiveNiceTree V childBag)
    (present : v ∈ childBag) (bag adhesion : Finset V) :
    encodeAux X color (.forget v child present) bag adhesion =
      .node (encodeLetter X color bag adhesion)
        (encodeAux X color child (insert v bag) bag) .nil :=
  rfl

@[simp] theorem encodeAux_join [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    {bagSet : Set V} (left right : InductiveNiceTree V bagSet)
    (bag adhesion : Finset V) :
    encodeAux X color (.join left right) bag adhesion =
      .node (encodeLetter X color bag adhesion)
        (encodeAux X color left bag bag)
        (encodeAux X color right bag bag) :=
  rfl

/-- Encode an empty-rooted constructor nice tree. -/
def encode [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    (tree : InductiveNiceTree V ∅) : BinTree (ExecSigmaLetter P omega) :=
  encodeAux X color tree ∅ ∅

@[simp] theorem encode_eq [DecidableEq V]
    (X : TauPGraph P V) (color : V → Fin (omega + 1))
    (tree : InductiveNiceTree V ∅) :
    encode X color tree = encodeAux X color tree ∅ ∅ :=
  rfl

end GraphMSO.Executable
