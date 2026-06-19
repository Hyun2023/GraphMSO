import Mathlib.Combinatorics.SimpleGraph.Basic
import GraphMSO.Syntax

namespace GraphMSO

/-- An environment for evaluating MSO formulas.

First-order vertex and edge variables may be unassigned, which lets closed formulas start from
an empty environment even when the vertex type or edge sort is empty. Monadic variables still
carry ordinary set values, with the empty environment assigning them the empty set. -/
structure Assignment (V E : Type) where
  fo : FOVar -> Option V
  so : SOVar -> Set V
  efo : EdgeFOVar -> Option E
  eso : EdgeSOVar -> Set E

namespace Assignment

variable {V E : Type}

def empty : Assignment V E where
  fo := fun _ => none
  so := fun _ => ∅
  efo := fun _ => none
  eso := fun _ => ∅

def updateFO (rho : Assignment V E) (x : FOVar) (v : V) : Assignment V E where
  fo := fun y => if y = x then some v else rho.fo y
  so := rho.so
  efo := rho.efo
  eso := rho.eso

def updateSO (rho : Assignment V E) (X : SOVar) (S : Set V) : Assignment V E where
  fo := rho.fo
  so := fun Y => if Y = X then S else rho.so Y
  efo := rho.efo
  eso := rho.eso

def updateEdgeFO (rho : Assignment V E) (e : EdgeFOVar) (val : E) : Assignment V E where
  fo := rho.fo
  so := rho.so
  efo := fun e' => if e' = e then some val else rho.efo e'
  eso := rho.eso

def updateEdgeSO (rho : Assignment V E) (E_var : EdgeSOVar) (S : Set E) : Assignment V E where
  fo := rho.fo
  so := rho.so
  efo := rho.efo
  eso := fun E' => if E' = E_var then S else rho.eso E'

@[simp]
theorem updateFO_here (rho : Assignment V E) (x : FOVar) (v : V) :
    (rho.updateFO x v).fo x = some v := by
  simp [updateFO]

@[simp]
theorem updateFO_other (rho : Assignment V E) {x y : FOVar} (v : V) (h : y ≠ x) :
    (rho.updateFO x v).fo y = rho.fo y := by
  simp [updateFO, h]

@[simp]
theorem updateFO_so (rho : Assignment V E) (x : FOVar) (v : V) (X : SOVar) :
    (rho.updateFO x v).so X = rho.so X := by
  rfl

@[simp]
theorem updateFO_efo (rho : Assignment V E) (x : FOVar) (v : V) (e : EdgeFOVar) :
    (rho.updateFO x v).efo e = rho.efo e := by
  rfl

@[simp]
theorem updateFO_eso (rho : Assignment V E) (x : FOVar) (v : V) (E_var : EdgeSOVar) :
    (rho.updateFO x v).eso E_var = rho.eso E_var := by
  rfl

@[simp]
theorem updateSO_here (rho : Assignment V E) (X : SOVar) (S : Set V) :
    (rho.updateSO X S).so X = S := by
  simp [updateSO]

@[simp]
theorem updateSO_other (rho : Assignment V E) {X Y : SOVar} (S : Set V) (h : Y ≠ X) :
    (rho.updateSO X S).so Y = rho.so Y := by
  simp [updateSO, h]

@[simp]
theorem updateSO_fo (rho : Assignment V E) (X : SOVar) (S : Set V) (x : FOVar) :
    (rho.updateSO X S).fo x = rho.fo x := by
  rfl

@[simp]
theorem updateSO_efo (rho : Assignment V E) (X : SOVar) (S : Set V) (e : EdgeFOVar) :
    (rho.updateSO X S).efo e = rho.efo e := by
  rfl

@[simp]
theorem updateSO_eso (rho : Assignment V E) (X : SOVar) (S : Set V) (E_var : EdgeSOVar) :
    (rho.updateSO X S).eso E_var = rho.eso E_var := by
  rfl

@[simp]
theorem updateEdgeFO_here (rho : Assignment V E) (e : EdgeFOVar) (val : E) :
    (rho.updateEdgeFO e val).efo e = some val := by
  simp [updateEdgeFO]

@[simp]
theorem updateEdgeFO_other (rho : Assignment V E) {e e' : EdgeFOVar} (val : E)
    (h : e' ≠ e) :
    (rho.updateEdgeFO e val).efo e' = rho.efo e' := by
  simp [updateEdgeFO, h]

@[simp]
theorem updateEdgeFO_fo (rho : Assignment V E) (e : EdgeFOVar) (val : E) (x : FOVar) :
    (rho.updateEdgeFO e val).fo x = rho.fo x := by
  rfl

@[simp]
theorem updateEdgeFO_so (rho : Assignment V E) (e : EdgeFOVar) (val : E) (X : SOVar) :
    (rho.updateEdgeFO e val).so X = rho.so X := by
  rfl

@[simp]
theorem updateEdgeFO_eso (rho : Assignment V E) (e : EdgeFOVar) (val : E)
    (E_var : EdgeSOVar) :
    (rho.updateEdgeFO e val).eso E_var = rho.eso E_var := by
  rfl

@[simp]
theorem updateEdgeSO_here (rho : Assignment V E) (E_var : EdgeSOVar) (S : Set E) :
    (rho.updateEdgeSO E_var S).eso E_var = S := by
  simp [updateEdgeSO]

@[simp]
theorem updateEdgeSO_other (rho : Assignment V E) {E_var E' : EdgeSOVar} (S : Set E)
    (h : E' ≠ E_var) :
    (rho.updateEdgeSO E_var S).eso E' = rho.eso E' := by
  simp [updateEdgeSO, h]

@[simp]
theorem updateEdgeSO_fo (rho : Assignment V E) (E_var : EdgeSOVar) (S : Set E) (x : FOVar) :
    (rho.updateEdgeSO E_var S).fo x = rho.fo x := by
  rfl

@[simp]
theorem updateEdgeSO_so (rho : Assignment V E) (E_var : EdgeSOVar) (S : Set E) (X : SOVar) :
    (rho.updateEdgeSO E_var S).so X = rho.so X := by
  rfl

@[simp]
theorem updateEdgeSO_efo (rho : Assignment V E) (E_var : EdgeSOVar) (S : Set E)
    (e : EdgeFOVar) :
    (rho.updateEdgeSO E_var S).efo e = rho.efo e := by
  rfl

@[simp]
theorem updateFO_updateSO_comm (rho : Assignment V E) (x : FOVar) (v : V) (X : SOVar)
    (S : Set V) :
    (rho.updateFO x v).updateSO X S = (rho.updateSO X S).updateFO x v := by
  cases rho
  rfl

@[simp]
theorem updateEdgeFO_updateEdgeSO_comm (rho : Assignment V E) (e : EdgeFOVar) (val : E)
    (E_var : EdgeSOVar) (S : Set E) :
    (rho.updateEdgeFO e val).updateEdgeSO E_var S =
      (rho.updateEdgeSO E_var S).updateEdgeFO e val := by
  cases rho
  rfl

/-- Two assignments agree on every free variable of a formula. -/
def AgreeOnFree (rho : Assignment V E) (phi : Formula) (sigma : Assignment V E) : Prop :=
  (∀ x, Formula.FreeFO phi x -> rho.fo x = sigma.fo x) ∧
  (∀ X, Formula.FreeSO phi X -> rho.so X = sigma.so X) ∧
  (∀ e, Formula.FreeEdgeFO phi e -> rho.efo e = sigma.efo e) ∧
  (∀ E_var, Formula.FreeEdgeSO phi E_var -> rho.eso E_var = sigma.eso E_var)

end Assignment

namespace Semantics

open Formula

variable {V : Type}

/-- Tarski semantics for MSO formulas over a simple graph and an assignment.

For `G : SimpleGraph V`, edge variables range over the subtype `G.edgeSet`. First-order
variables that are unassigned make the corresponding atomic formula false; quantifiers install
assignments before recursively evaluating their bodies. -/
def SatisfiesAt : Formula -> (G : SimpleGraph V) -> Assignment V G.edgeSet -> Prop
  | false_, _, _ => False
  | equal x y, _, rho => ∃ v : V, rho.fo x = some v ∧ rho.fo y = some v
  | edge x y, G, rho =>
      ∃ u v : V, rho.fo x = some u ∧ rho.fo y = some v ∧ G.Adj u v
  | inSet x X, _, rho => ∃ v : V, rho.fo x = some v ∧ v ∈ rho.so X
  | equalEdge e1 e2, G, rho =>
      ∃ val : G.edgeSet, rho.efo e1 = some val ∧ rho.efo e2 = some val
  | inc x e, G, rho =>
      ∃ v : V, ∃ val : G.edgeSet,
        rho.fo x = some v ∧ rho.efo e = some val ∧ v ∈ (val : Sym2 V)
  | inEdgeSet e E_var, G, rho =>
      ∃ val : G.edgeSet, rho.efo e = some val ∧ val ∈ rho.eso E_var
  | neg phi, G, rho => Not (SatisfiesAt phi G rho)
  | conj phi psi, G, rho => SatisfiesAt phi G rho ∧ SatisfiesAt psi G rho
  | disj phi psi, G, rho => SatisfiesAt phi G rho ∨ SatisfiesAt psi G rho
  | impl phi psi, G, rho => SatisfiesAt phi G rho -> SatisfiesAt psi G rho
  | biimpl phi psi, G, rho => Iff (SatisfiesAt phi G rho) (SatisfiesAt psi G rho)
  | existsFO x phi, G, rho => ∃ v : V, SatisfiesAt phi G (rho.updateFO x v)
  | forallFO x phi, G, rho => ∀ v : V, SatisfiesAt phi G (rho.updateFO x v)
  | existsSO X phi, G, rho => ∃ S : Set V, SatisfiesAt phi G (rho.updateSO X S)
  | forallSO X phi, G, rho => ∀ S : Set V, SatisfiesAt phi G (rho.updateSO X S)
  | existsEdgeFO e phi, G, rho =>
      ∃ val : G.edgeSet, SatisfiesAt phi G (rho.updateEdgeFO e val)
  | forallEdgeFO e phi, G, rho =>
      ∀ val : G.edgeSet, SatisfiesAt phi G (rho.updateEdgeFO e val)
  | existsEdgeSO E_var phi, G, rho =>
      ∃ S : Set G.edgeSet, SatisfiesAt phi G (rho.updateEdgeSO E_var S)
  | forallEdgeSO E_var phi, G, rho =>
      ∀ S : Set G.edgeSet, SatisfiesAt phi G (rho.updateEdgeSO E_var S)

/-- Satisfaction of a closed formula by a graph. -/
def Satisfies (G : SimpleGraph V) (phi : Formula) : Prop :=
  phi.Closed ∧ SatisfiesAt phi G (Assignment.empty : Assignment V G.edgeSet)

theorem satisfies_closed {G : SimpleGraph V} {phi : Formula} (h : Satisfies G phi) :
    phi.Closed :=
  h.1

theorem satisfies_iff_satisfiesAt_of_closed {G : SimpleGraph V} {phi : Formula}
    (hclosed : phi.Closed) :
    Satisfies G phi ↔ SatisfiesAt phi G (Assignment.empty : Assignment V G.edgeSet) := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hclosed, h⟩

@[simp]
theorem not_satisfies_false (G : SimpleGraph V) : ¬ Satisfies G Formula.false_ := by
  intro h
  exact h.2

theorem satisfiesAt_true (G : SimpleGraph V) (rho : Assignment V G.edgeSet) :
    SatisfiesAt Formula.true_ G rho := by
  intro h
  exact h

theorem satisfies_true (G : SimpleGraph V) : Satisfies G Formula.true_ := by
  constructor
  · simp [Formula.true_, Formula.Closed, Formula.FreeFO, Formula.FreeSO,
      Formula.FreeEdgeFO, Formula.FreeEdgeSO]
  · exact satisfiesAt_true G _

@[simp]
theorem satisfiesAt_conj (G : SimpleGraph V) (rho : Assignment V G.edgeSet) (phi psi : Formula) :
    SatisfiesAt (Formula.conj phi psi) G rho ↔ SatisfiesAt phi G rho ∧ SatisfiesAt psi G rho := by
  rfl

@[simp]
theorem satisfiesAt_disj (G : SimpleGraph V) (rho : Assignment V G.edgeSet) (phi psi : Formula) :
    SatisfiesAt (Formula.disj phi psi) G rho ↔ SatisfiesAt phi G rho ∨ SatisfiesAt psi G rho := by
  rfl

@[simp]
theorem satisfiesAt_impl (G : SimpleGraph V) (rho : Assignment V G.edgeSet) (phi psi : Formula) :
    SatisfiesAt (Formula.impl phi psi) G rho ↔
      (SatisfiesAt phi G rho -> SatisfiesAt psi G rho) := by
  rfl

@[simp]
theorem satisfiesAt_biimpl (G : SimpleGraph V) (rho : Assignment V G.edgeSet)
    (phi psi : Formula) :
    SatisfiesAt (Formula.biimpl phi psi) G rho ↔
      (SatisfiesAt phi G rho ↔ SatisfiesAt psi G rho) := by
  rfl

@[simp]
theorem satisfiesAt_existsFOs_nil (G : SimpleGraph V) (rho : Assignment V G.edgeSet)
    (phi : Formula) :
    SatisfiesAt (Formula.existsFOs [] phi) G rho ↔ SatisfiesAt phi G rho := by
  rfl

@[simp]
theorem satisfiesAt_existsFOs_cons (G : SimpleGraph V) (rho : Assignment V G.edgeSet)
    (x : FOVar) (xs : List FOVar) (phi : Formula) :
    SatisfiesAt (Formula.existsFOs (x :: xs) phi) G rho ↔
      ∃ v : V, SatisfiesAt (Formula.existsFOs xs phi) G (rho.updateFO x v) := by
  rfl

@[simp]
theorem satisfiesAt_forallFOs_nil (G : SimpleGraph V) (rho : Assignment V G.edgeSet)
    (phi : Formula) :
    SatisfiesAt (Formula.forallFOs [] phi) G rho ↔ SatisfiesAt phi G rho := by
  rfl

@[simp]
theorem satisfiesAt_forallFOs_cons (G : SimpleGraph V) (rho : Assignment V G.edgeSet)
    (x : FOVar) (xs : List FOVar) (phi : Formula) :
    SatisfiesAt (Formula.forallFOs (x :: xs) phi) G rho ↔
      ∀ v : V, SatisfiesAt (Formula.forallFOs xs phi) G (rho.updateFO x v) := by
  rfl

end Semantics

end GraphMSO
