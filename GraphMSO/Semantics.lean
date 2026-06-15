import GraphMSO.Basic
import GraphMSO.Syntax

namespace GraphMSO

/-- An environment assigning first-order variables to vertices/edges and monadic
second-order variables to vertex/edge sets. -/
structure Assignment (V E : Type) where
  fo : FOVar -> V
  so : SOVar -> VSet V
  efo : EdgeFOVar -> E
  eso : EdgeSOVar -> ESet E

namespace Assignment

variable {V E : Type}

def updateFO (rho : Assignment V E) (x : FOVar) (v : V) : Assignment V E where
  fo := fun y => if y = x then v else rho.fo y
  so := rho.so
  efo := rho.efo
  eso := rho.eso

def updateSO (rho : Assignment V E) (X : SOVar) (S : VSet V) : Assignment V E where
  fo := rho.fo
  so := fun Y => if Y = X then S else rho.so Y
  efo := rho.efo
  eso := rho.eso

def updateEdgeFO (rho : Assignment V E) (e : EdgeFOVar) (val : E) : Assignment V E where
  fo := rho.fo
  so := rho.so
  efo := fun e' => if e' = e then val else rho.efo e'
  eso := rho.eso

def updateEdgeSO (rho : Assignment V E) (E_var : EdgeSOVar) (S : ESet E) : Assignment V E where
  fo := rho.fo
  so := rho.so
  efo := rho.efo
  eso := fun E' => if E' = E_var then S else rho.eso E'

@[simp]
theorem updateFO_here (rho : Assignment V E) (x : FOVar) (v : V) :
    (rho.updateFO x v).fo x = v := by
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
theorem updateSO_here (rho : Assignment V E) (X : SOVar) (S : VSet V) :
    (rho.updateSO X S).so X = S := by
  simp [updateSO]

@[simp]
theorem updateSO_other (rho : Assignment V E) {X Y : SOVar} (S : VSet V) (h : Y ≠ X) :
    (rho.updateSO X S).so Y = rho.so Y := by
  simp [updateSO, h]

@[simp]
theorem updateSO_fo (rho : Assignment V E) (X : SOVar) (S : VSet V) (x : FOVar) :
    (rho.updateSO X S).fo x = rho.fo x := by
  rfl

@[simp]
theorem updateSO_efo (rho : Assignment V E) (X : SOVar) (S : VSet V) (e : EdgeFOVar) :
    (rho.updateSO X S).efo e = rho.efo e := by
  rfl

@[simp]
theorem updateSO_eso (rho : Assignment V E) (X : SOVar) (S : VSet V) (E_var : EdgeSOVar) :
    (rho.updateSO X S).eso E_var = rho.eso E_var := by
  rfl

@[simp]
theorem updateEdgeFO_here (rho : Assignment V E) (e : EdgeFOVar) (val : E) :
    (rho.updateEdgeFO e val).efo e = val := by
  simp [updateEdgeFO]

@[simp]
theorem updateEdgeFO_other (rho : Assignment V E) {e e' : EdgeFOVar} (val : E) (h : e' ≠ e) :
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
theorem updateEdgeSO_here (rho : Assignment V E) (E_var : EdgeSOVar) (S : ESet E) :
    (rho.updateEdgeSO E_var S).eso E_var = S := by
  simp [updateEdgeSO]

@[simp]
theorem updateEdgeSO_other (rho : Assignment V E) {E_var E' : EdgeSOVar} (S : ESet E) (h : E' ≠ E_var) :
    (rho.updateEdgeSO E_var S).eso E' = rho.eso E' := by
  simp [updateEdgeSO, h]

@[simp]
theorem updateEdgeSO_fo (rho : Assignment V E) (E_var : EdgeSOVar) (S : ESet E) (x : FOVar) :
    (rho.updateEdgeSO E_var S).fo x = rho.fo x := by
  rfl

@[simp]
theorem updateEdgeSO_so (rho : Assignment V E) (E_var : EdgeSOVar) (S : ESet E) (X : SOVar) :
    (rho.updateEdgeSO E_var S).so X = rho.so X := by
  rfl

@[simp]
theorem updateEdgeSO_efo (rho : Assignment V E) (E_var : EdgeSOVar) (S : ESet E)
    (e : EdgeFOVar) :
    (rho.updateEdgeSO E_var S).efo e = rho.efo e := by
  rfl

@[simp]
theorem updateFO_comm (rho : Assignment V E) (x y : FOVar) (vx vy : V) (h : x ≠ y) :
    (rho.updateFO x vx).updateFO y vy = (rho.updateFO y vy).updateFO x vx := by
  cases rho
  dsimp [updateFO]
  congr
  funext z
  by_cases hz_y : z = y
  · subst z
    simp [h.symm]
  · by_cases hz_x : z = x
    · subst z
      simp [h]
    · simp [hz_y, hz_x]

@[simp]
theorem updateSO_comm (rho : Assignment V E) (X Y : SOVar) (SX SY : VSet V) (h : X ≠ Y) :
    (rho.updateSO X SX).updateSO Y SY = (rho.updateSO Y SY).updateSO X SX := by
  cases rho
  dsimp [updateSO]
  congr
  funext Z
  by_cases hZ_Y : Z = Y
  · subst Z
    simp [h.symm]
  · by_cases hZ_X : Z = X
    · subst Z
      simp [h]
    · simp [hZ_Y, hZ_X]

@[simp]
theorem updateFO_updateSO_comm (rho : Assignment V E) (x : FOVar) (v : V) (X : SOVar) (S : VSet V) :
    (rho.updateFO x v).updateSO X S = (rho.updateSO X S).updateFO x v := by
  cases rho
  rfl

@[simp]
theorem updateEdgeFO_updateEdgeSO_comm (rho : Assignment V E) (e : EdgeFOVar) (val : E) (E_var : EdgeSOVar) (S : ESet E) :
    (rho.updateEdgeFO e val).updateEdgeSO E_var S = (rho.updateEdgeSO E_var S).updateEdgeFO e val := by
  cases rho
  rfl

end Assignment

namespace Semantics

open Formula

variable {V : Type}

/-- Tarski semantics for MSO formulas over a simple graph and an assignment.

For `G : SimpleGraph V`, edge variables range over the subtype `G.edgeSet`. -/
def EvalAt : Formula -> (G : SimpleGraph V) -> Assignment V G.edgeSet -> Prop
  | false_, _, _ => False
  | equal x y, _, rho => rho.fo x = rho.fo y
  | edge x y, G, rho => G.Adj (rho.fo x) (rho.fo y)
  | inSet x X, _, rho => rho.fo x ∈ rho.so X
  | equalEdge e1 e2, _, rho => rho.efo e1 = rho.efo e2
  | inc x e, _, rho => rho.fo x ∈ (rho.efo e : Sym2 V)
  | inEdgeSet e E_var, _, rho => rho.efo e ∈ rho.eso E_var
  | neg phi, G, rho => Not (EvalAt phi G rho)
  | conj phi psi, G, rho => EvalAt phi G rho /\ EvalAt psi G rho
  | disj phi psi, G, rho => EvalAt phi G rho \/ EvalAt psi G rho
  | impl phi psi, G, rho => EvalAt phi G rho -> EvalAt psi G rho
  | biimpl phi psi, G, rho => Iff (EvalAt phi G rho) (EvalAt psi G rho)
  | existsFO x phi, G, rho => Exists (fun v : V => EvalAt phi G (rho.updateFO x v))
  | forallFO x phi, G, rho => forall v : V, EvalAt phi G (rho.updateFO x v)
  | existsSO X phi, G, rho => Exists (fun S : VSet V => EvalAt phi G (rho.updateSO X S))
  | forallSO X phi, G, rho => forall S : VSet V, EvalAt phi G (rho.updateSO X S)
  | existsEdgeFO e phi, G, rho =>
      Exists (fun val : G.edgeSet => EvalAt phi G (rho.updateEdgeFO e val))
  | forallEdgeFO e phi, G, rho =>
      forall val : G.edgeSet, EvalAt phi G (rho.updateEdgeFO e val)
  | existsEdgeSO E_var phi, G, rho =>
      Exists (fun S : ESet G.edgeSet => EvalAt phi G (rho.updateEdgeSO E_var S))
  | forallEdgeSO E_var phi, G, rho =>
      forall S : ESet G.edgeSet, EvalAt phi G (rho.updateEdgeSO E_var S)

/-- Evaluate a formula as a property of a simple graph.

This is intended for closed formulas. Until assignment-independence is proved, it is defined as
validity under every assignment. Use `EvalAt` for formulas with free variables. -/
def Eval (phi : Formula) (G : SimpleGraph V) : Prop :=
  forall rho : Assignment V G.edgeSet, EvalAt phi G rho

theorem eval_true (G : SimpleGraph V) : Eval Formula.true_ G := by
  intro rho h
  exact h

theorem evalAt_true (G : SimpleGraph V) (rho : Assignment V G.edgeSet) :
    EvalAt Formula.true_ G rho := by
  intro h
  exact h

@[simp]
theorem evalAt_notEqual (G : SimpleGraph V) (rho : Assignment V G.edgeSet) (x y : FOVar) :
    EvalAt (Formula.notEqual x y) G rho ↔ rho.fo x ≠ rho.fo y := by
  rfl

@[simp]
theorem evalAt_conj (G : SimpleGraph V) (rho : Assignment V G.edgeSet) (phi psi : Formula) :
    EvalAt (Formula.conj phi psi) G rho ↔ EvalAt phi G rho ∧ EvalAt psi G rho := by
  rfl

@[simp]
theorem evalAt_disj (G : SimpleGraph V) (rho : Assignment V G.edgeSet) (phi psi : Formula) :
    EvalAt (Formula.disj phi psi) G rho ↔ EvalAt phi G rho ∨ EvalAt psi G rho := by
  rfl

@[simp]
theorem evalAt_impl (G : SimpleGraph V) (rho : Assignment V G.edgeSet) (phi psi : Formula) :
    EvalAt (Formula.impl phi psi) G rho ↔ (EvalAt phi G rho → EvalAt psi G rho) := by
  rfl

@[simp]
theorem evalAt_biimpl (G : SimpleGraph V) (rho : Assignment V G.edgeSet) (phi psi : Formula) :
    EvalAt (Formula.biimpl phi psi) G rho ↔ (EvalAt phi G rho ↔ EvalAt psi G rho) := by
  rfl

@[simp]
theorem evalAt_existsFOs_nil (G : SimpleGraph V) (rho : Assignment V G.edgeSet) (phi : Formula) :
    EvalAt (Formula.existsFOs [] phi) G rho ↔ EvalAt phi G rho := by
  rfl

@[simp]
theorem evalAt_existsFOs_cons (G : SimpleGraph V) (rho : Assignment V G.edgeSet)
    (x : FOVar) (xs : List FOVar) (phi : Formula) :
    EvalAt (Formula.existsFOs (x :: xs) phi) G rho ↔
      ∃ v : V, EvalAt (Formula.existsFOs xs phi) G (rho.updateFO x v) := by
  rfl

@[simp]
theorem evalAt_forallFOs_nil (G : SimpleGraph V) (rho : Assignment V G.edgeSet) (phi : Formula) :
    EvalAt (Formula.forallFOs [] phi) G rho ↔ EvalAt phi G rho := by
  rfl

@[simp]
theorem evalAt_forallFOs_cons (G : SimpleGraph V) (rho : Assignment V G.edgeSet)
    (x : FOVar) (xs : List FOVar) (phi : Formula) :
    EvalAt (Formula.forallFOs (x :: xs) phi) G rho ↔
      ∀ v : V, EvalAt (Formula.forallFOs xs phi) G (rho.updateFO x v) := by
  rfl

theorem evalAt_equal_self (G : SimpleGraph V) (rho : Assignment V G.edgeSet) (x : FOVar) :
    EvalAt (Formula.equal x x) G rho := by
  rfl

theorem evalAt_not_equal_self_false (G : SimpleGraph V) (rho : Assignment V G.edgeSet) (x : FOVar) :
    Not (EvalAt (Formula.notEqual x x) G rho) := by
  intro h
  exact h rfl

end Semantics

end GraphMSO
