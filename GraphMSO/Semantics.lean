import GraphMSO.Basic
import GraphMSO.Syntax

namespace GraphMSO

universe u

/-- An environment assigning vertices to first-order variables and vertex sets to
monadic second-order variables. -/
structure Assignment (V E : Type u) where
  fo : FOVar -> V
  so : SOVar -> VSet V
  efo : EdgeFOVar -> E
  eso : EdgeSOVar -> ESet E

namespace Assignment

variable {V E : Type u}

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
theorem updateEdgeFO_here (rho : Assignment V E) (e : EdgeFOVar) (val : E) :
    (rho.updateEdgeFO e val).efo e = val := by
  simp [updateEdgeFO]

@[simp]
theorem updateEdgeFO_other (rho : Assignment V E) {e e' : EdgeFOVar} (val : E) (h : e' ≠ e) :
    (rho.updateEdgeFO e val).efo e' = rho.efo e' := by
  simp [updateEdgeFO, h]

@[simp]
theorem updateEdgeSO_here (rho : Assignment V E) (E_var : EdgeSOVar) (S : ESet E) :
    (rho.updateEdgeSO E_var S).eso E_var = S := by
  simp [updateEdgeSO]

@[simp]
theorem updateEdgeSO_other (rho : Assignment V E) {E_var E' : EdgeSOVar} (S : ESet E) (h : E' ≠ E_var) :
    (rho.updateEdgeSO E_var S).eso E' = rho.eso E' := by
  simp [updateEdgeSO, h]

@[simp]
theorem updateFO_comm (rho : Assignment V E) (x y : FOVar) (vx vy : V) (h : x ≠ y) :
    (rho.updateFO x vx).updateFO y vy = (rho.updateFO y vy).updateFO x vx := by
  cases rho
  dsimp [updateFO]
  congr
  funext z
  by_cases hy : z = y
  · subst hy
    have hx : y ≠ x := h.symm
    simp [hx]
  · simp [hy]

@[simp]
theorem updateSO_comm (rho : Assignment V E) (X Y : SOVar) (SX SY : VSet V) (h : X ≠ Y) :
    (rho.updateSO X SX).updateSO Y SY = (rho.updateSO Y SY).updateSO X SX := by
  cases rho
  dsimp [updateSO]
  congr
  funext Z
  by_cases hY : Z = Y
  · subst hY
    have hX : Y ≠ X := h.symm
    simp [hX]
  · simp [hY]

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

variable {V E : Type u}

/-- Tarski semantics for MSO formulas over a graph and an assignment. -/
def Eval (G : Graph V E) (rho : Assignment V E) : Formula -> Prop
  | false_ => False
  | equal x y => rho.fo x = rho.fo y
  | edge x y => G.Adj (rho.fo x) (rho.fo y)
  | inSet x X => rho.fo x ∈ rho.so X
  | equalEdge e1 e2 => rho.efo e1 = rho.efo e2
  | inc x e => G.inc (rho.fo x) (rho.efo e)
  | inEdgeSet e E_var => rho.efo e ∈ rho.eso E_var
  | neg phi => Not (Eval G rho phi)
  | conj phi psi => Eval G rho phi /\ Eval G rho psi
  | disj phi psi => Eval G rho phi \/ Eval G rho psi
  | impl phi psi => Eval G rho phi -> Eval G rho psi
  | biimpl phi psi => Iff (Eval G rho phi) (Eval G rho psi)
  | existsFO x phi => Exists (fun v : V => Eval G (rho.updateFO x v) phi)
  | forallFO x phi => forall v : V, Eval G (rho.updateFO x v) phi
  | existsSO X phi => Exists (fun S : VSet V => Eval G (rho.updateSO X S) phi)
  | forallSO X phi => forall S : VSet V, Eval G (rho.updateSO X S) phi
  | existsEdgeFO e phi => Exists (fun val : E => Eval G (rho.updateEdgeFO e val) phi)
  | forallEdgeFO e phi => forall val : E, Eval G (rho.updateEdgeFO e val) phi
  | existsEdgeSO E_var phi => Exists (fun S : ESet E => Eval G (rho.updateEdgeSO E_var S) phi)
  | forallEdgeSO E_var phi => forall S : ESet E, Eval G (rho.updateEdgeSO E_var S) phi

theorem eval_true (G : Graph V E) (rho : Assignment V E) : Eval G rho Formula.true_ := by
  intro h
  exact h

@[simp]
theorem eval_notEqual (G : Graph V E) (rho : Assignment V E) (x y : FOVar) :
    Eval G rho (Formula.notEqual x y) ↔ rho.fo x ≠ rho.fo y := by
  rfl

@[simp]
theorem eval_conj (G : Graph V E) (rho : Assignment V E) (phi psi : Formula) :
    Eval G rho (Formula.conj phi psi) ↔ Eval G rho phi ∧ Eval G rho psi := by
  rfl

@[simp]
theorem eval_disj (G : Graph V E) (rho : Assignment V E) (phi psi : Formula) :
    Eval G rho (Formula.disj phi psi) ↔ Eval G rho phi ∨ Eval G rho psi := by
  rfl

@[simp]
theorem eval_impl (G : Graph V E) (rho : Assignment V E) (phi psi : Formula) :
    Eval G rho (Formula.impl phi psi) ↔ (Eval G rho phi → Eval G rho psi) := by
  rfl

@[simp]
theorem eval_biimpl (G : Graph V E) (rho : Assignment V E) (phi psi : Formula) :
    Eval G rho (Formula.biimpl phi psi) ↔ (Eval G rho phi ↔ Eval G rho psi) := by
  rfl

@[simp]
theorem eval_existsFOs_nil (G : Graph V E) (rho : Assignment V E) (phi : Formula) :
    Eval G rho (Formula.existsFOs [] phi) ↔ Eval G rho phi := by
  rfl

@[simp]
theorem eval_existsFOs_cons (G : Graph V E) (rho : Assignment V E) (x : FOVar) (xs : List FOVar) (phi : Formula) :
    Eval G rho (Formula.existsFOs (x :: xs) phi) ↔ ∃ v : V, Eval G (rho.updateFO x v) (Formula.existsFOs xs phi) := by
  rfl

@[simp]
theorem eval_forallFOs_nil (G : Graph V E) (rho : Assignment V E) (phi : Formula) :
    Eval G rho (Formula.forallFOs [] phi) ↔ Eval G rho phi := by
  rfl

@[simp]
theorem eval_forallFOs_cons (G : Graph V E) (rho : Assignment V E) (x : FOVar) (xs : List FOVar) (phi : Formula) :
    Eval G rho (Formula.forallFOs (x :: xs) phi) ↔ ∀ v : V, Eval G (rho.updateFO x v) (Formula.forallFOs xs phi) := by
  rfl

theorem eval_equal_self (G : Graph V E) (rho : Assignment V E) (x : FOVar) :
    Eval G rho (Formula.equal x x) := by
  rfl

theorem eval_not_equal_self_false (G : Graph V E) (rho : Assignment V E) (x : FOVar) :
    Not (Eval G rho (Formula.notEqual x x)) := by
  intro h
  exact h rfl

end Semantics

end GraphMSO
