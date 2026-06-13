import GraphMSO.Basic
import GraphMSO.Syntax

namespace GraphMSO

universe u

/-- An environment assigning vertices to first-order variables and vertex sets to
monadic second-order variables. -/
structure Assignment (V : Type u) where
  fo : FOVar -> V
  so : SOVar -> VSet V

namespace Assignment

variable {V : Type u}

def updateFO (rho : Assignment V) (x : FOVar) (v : V) : Assignment V where
  fo := fun y => if y = x then v else rho.fo y
  so := rho.so

def updateSO (rho : Assignment V) (X : SOVar) (S : VSet V) : Assignment V where
  fo := rho.fo
  so := fun Y => if Y = X then S else rho.so Y

@[simp]
theorem updateFO_here (rho : Assignment V) (x : FOVar) (v : V) :
    (rho.updateFO x v).fo x = v := by
  simp [updateFO]

@[simp]
theorem updateSO_here (rho : Assignment V) (X : SOVar) (S : VSet V) :
    (rho.updateSO X S).so X = S := by
  simp [updateSO]

end Assignment

namespace Semantics

open Formula

variable {V : Type u}

/-- Tarski semantics for MSO formulas over a graph and an assignment. -/
def Eval (G : Graph V) (rho : Assignment V) : Formula -> Prop
  | false_ => False
  | equal x y => rho.fo x = rho.fo y
  | edge x y => G.Adj (rho.fo x) (rho.fo y)
  | inSet x X => rho.so X (rho.fo x)
  | neg phi => Not (Eval G rho phi)
  | conj phi psi => Eval G rho phi /\ Eval G rho psi
  | disj phi psi => Eval G rho phi \/ Eval G rho psi
  | impl phi psi => Eval G rho phi -> Eval G rho psi
  | biimpl phi psi => Iff (Eval G rho phi) (Eval G rho psi)
  | existsFO x phi => Exists (fun v : V => Eval G (rho.updateFO x v) phi)
  | forallFO x phi => forall v : V, Eval G (rho.updateFO x v) phi
  | existsSO X phi => Exists (fun S : VSet V => Eval G (rho.updateSO X S) phi)
  | forallSO X phi => forall S : VSet V, Eval G (rho.updateSO X S) phi

theorem eval_true (G : Graph V) (rho : Assignment V) : Eval G rho Formula.true_ := by
  intro h
  exact h

theorem eval_equal_self (G : Graph V) (rho : Assignment V) (x : FOVar) :
    Eval G rho (Formula.equal x x) := by
  rfl

theorem eval_not_equal_self_false (G : Graph V) (rho : Assignment V) (x : FOVar) :
    Not (Eval G rho (Formula.notEqual x x)) := by
  intro h
  exact h rfl

end Semantics

end GraphMSO
