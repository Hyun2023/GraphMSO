import Mathlib.Combinatorics.SimpleGraph.Basic
import GraphMSO.Syntax

namespace GraphMSO

/-- An environment assigning first-order variables to vertices/edges and monadic
second-order variables to vertex/edge sets. -/
structure Assignment (V E : Type) where
  fo : FOVar -> V
  so : SOVar -> Set V
  efo : EdgeFOVar -> E
  eso : EdgeSOVar -> Set E

namespace Assignment

variable {V E : Type}

def updateFO (rho : Assignment V E) (x : FOVar) (v : V) : Assignment V E where
  fo := fun y => if y = x then v else rho.fo y
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
  efo := fun e' => if e' = e then val else rho.efo e'
  eso := rho.eso

def updateEdgeSO (rho : Assignment V E) (E_var : EdgeSOVar) (S : Set E) : Assignment V E where
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
theorem updateSO_comm (rho : Assignment V E) (X Y : SOVar) (SX SY : Set V) (h : X ≠ Y) :
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
  (∀ x, Formula.FreeFO phi x → rho.fo x = sigma.fo x) ∧
  (∀ X, Formula.FreeSO phi X → rho.so X = sigma.so X) ∧
  (∀ e, Formula.FreeEdgeFO phi e → rho.efo e = sigma.efo e) ∧
  (∀ E_var, Formula.FreeEdgeSO phi E_var → rho.eso E_var = sigma.eso E_var)

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
  | existsSO X phi, G, rho => Exists (fun S : Set V => EvalAt phi G (rho.updateSO X S))
  | forallSO X phi, G, rho => forall S : Set V, EvalAt phi G (rho.updateSO X S)
  | existsEdgeFO e phi, G, rho =>
      Exists (fun val : G.edgeSet => EvalAt phi G (rho.updateEdgeFO e val))
  | forallEdgeFO e phi, G, rho =>
      forall val : G.edgeSet, EvalAt phi G (rho.updateEdgeFO e val)
  | existsEdgeSO E_var phi, G, rho =>
      Exists (fun S : Set G.edgeSet => EvalAt phi G (rho.updateEdgeSO E_var S))
  | forallEdgeSO E_var phi, G, rho =>
      forall S : Set G.edgeSet, EvalAt phi G (rho.updateEdgeSO E_var S)

/-- Evaluate a formula as a property of a simple graph.

This is intended for closed formulas. Until assignment-independence is proved, it is defined as
validity under every assignment. Use `EvalAt` for formulas with free variables. -/
def Eval (phi : Formula) (G : SimpleGraph V) : Prop :=
  forall rho : Assignment V G.edgeSet, EvalAt phi G rho

/-- `EvalAt` only depends on the values of variables that occur free in the formula. -/
theorem evalAt_ext_on_free {G : SimpleGraph V} (phi : Formula)
    (rho sigma : Assignment V G.edgeSet) (h : rho.AgreeOnFree phi sigma) :
    EvalAt phi G rho ↔ EvalAt phi G sigma := by
  induction phi generalizing rho sigma with
  | false_ =>
      simp [EvalAt]
  | equal x y =>
      rcases h with ⟨hfo, _, _, _⟩
      have hx : rho.fo x = sigma.fo x := hfo x (Or.inl rfl)
      have hy : rho.fo y = sigma.fo y := hfo y (Or.inr rfl)
      simp [EvalAt, hx, hy]
  | edge x y =>
      rcases h with ⟨hfo, _, _, _⟩
      have hx : rho.fo x = sigma.fo x := hfo x (Or.inl rfl)
      have hy : rho.fo y = sigma.fo y := hfo y (Or.inr rfl)
      simp [EvalAt, hx, hy]
  | inSet x X =>
      rcases h with ⟨hfo, hso, _, _⟩
      have hx : rho.fo x = sigma.fo x := hfo x rfl
      have hX : rho.so X = sigma.so X := hso X rfl
      simp [EvalAt, hx, hX]
  | equalEdge e₁ e₂ =>
      rcases h with ⟨_, _, hefo, _⟩
      have he₁ : rho.efo e₁ = sigma.efo e₁ := hefo e₁ (Or.inl rfl)
      have he₂ : rho.efo e₂ = sigma.efo e₂ := hefo e₂ (Or.inr rfl)
      simp [EvalAt, he₁, he₂]
  | inc x e =>
      rcases h with ⟨hfo, _, hefo, _⟩
      have hx : rho.fo x = sigma.fo x := hfo x rfl
      have he : rho.efo e = sigma.efo e := hefo e rfl
      simp [EvalAt, hx, he]
  | inEdgeSet e E_var =>
      rcases h with ⟨_, _, hefo, heso⟩
      have he : rho.efo e = sigma.efo e := hefo e rfl
      have hE : rho.eso E_var = sigma.eso E_var := heso E_var rfl
      simp [EvalAt, he, hE]
  | neg phi ih =>
      have hphi : rho.AgreeOnFree phi sigma := by
        simpa [Assignment.AgreeOnFree, Formula.FreeFO, Formula.FreeSO,
          Formula.FreeEdgeFO, Formula.FreeEdgeSO] using h
      have hiff := ih rho sigma hphi
      constructor
      · intro hn hs
        exact hn (hiff.mpr hs)
      · intro hn hr
        exact hn (hiff.mp hr)
  | conj phi psi ihPhi ihPsi =>
      have hPhi : rho.AgreeOnFree phi sigma := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        exact ⟨fun x hx => hfo x (Or.inl hx), fun X hX => hso X (Or.inl hX),
          fun e he => hefo e (Or.inl he), fun E_var hE => heso E_var (Or.inl hE)⟩
      have hPsi : rho.AgreeOnFree psi sigma := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        exact ⟨fun x hx => hfo x (Or.inr hx), fun X hX => hso X (Or.inr hX),
          fun e he => hefo e (Or.inr he), fun E_var hE => heso E_var (Or.inr hE)⟩
      have hPhiEval := ihPhi rho sigma hPhi
      have hPsiEval := ihPsi rho sigma hPsi
      constructor
      · intro hp
        exact ⟨hPhiEval.mp hp.1, hPsiEval.mp hp.2⟩
      · intro hp
        exact ⟨hPhiEval.mpr hp.1, hPsiEval.mpr hp.2⟩
  | disj phi psi ihPhi ihPsi =>
      have hPhi : rho.AgreeOnFree phi sigma := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        exact ⟨fun x hx => hfo x (Or.inl hx), fun X hX => hso X (Or.inl hX),
          fun e he => hefo e (Or.inl he), fun E_var hE => heso E_var (Or.inl hE)⟩
      have hPsi : rho.AgreeOnFree psi sigma := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        exact ⟨fun x hx => hfo x (Or.inr hx), fun X hX => hso X (Or.inr hX),
          fun e he => hefo e (Or.inr he), fun E_var hE => heso E_var (Or.inr hE)⟩
      have hPhiEval := ihPhi rho sigma hPhi
      have hPsiEval := ihPsi rho sigma hPsi
      constructor
      · rintro (hp | hp)
        · exact Or.inl (hPhiEval.mp hp)
        · exact Or.inr (hPsiEval.mp hp)
      · rintro (hp | hp)
        · exact Or.inl (hPhiEval.mpr hp)
        · exact Or.inr (hPsiEval.mpr hp)
  | impl phi psi ihPhi ihPsi =>
      have hPhi : rho.AgreeOnFree phi sigma := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        exact ⟨fun x hx => hfo x (Or.inl hx), fun X hX => hso X (Or.inl hX),
          fun e he => hefo e (Or.inl he), fun E_var hE => heso E_var (Or.inl hE)⟩
      have hPsi : rho.AgreeOnFree psi sigma := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        exact ⟨fun x hx => hfo x (Or.inr hx), fun X hX => hso X (Or.inr hX),
          fun e he => hefo e (Or.inr he), fun E_var hE => heso E_var (Or.inr hE)⟩
      have hPhiEval := ihPhi rho sigma hPhi
      have hPsiEval := ihPsi rho sigma hPsi
      constructor
      · intro hp hphi
        exact hPsiEval.mp (hp (hPhiEval.mpr hphi))
      · intro hp hphi
        exact hPsiEval.mpr (hp (hPhiEval.mp hphi))
  | biimpl phi psi ihPhi ihPsi =>
      have hPhi : rho.AgreeOnFree phi sigma := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        exact ⟨fun x hx => hfo x (Or.inl hx), fun X hX => hso X (Or.inl hX),
          fun e he => hefo e (Or.inl he), fun E_var hE => heso E_var (Or.inl hE)⟩
      have hPsi : rho.AgreeOnFree psi sigma := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        exact ⟨fun x hx => hfo x (Or.inr hx), fun X hX => hso X (Or.inr hX),
          fun e he => hefo e (Or.inr he), fun E_var hE => heso E_var (Or.inr hE)⟩
      have hPhiEval := ihPhi rho sigma hPhi
      have hPsiEval := ihPsi rho sigma hPsi
      constructor
      · intro hp
        constructor
        · intro hphi
          exact hPsiEval.mp (hp.mp (hPhiEval.mpr hphi))
        · intro hpsi
          exact hPhiEval.mp (hp.mpr (hPsiEval.mpr hpsi))
      · intro hp
        constructor
        · intro hphi
          exact hPsiEval.mpr (hp.mp (hPhiEval.mp hphi))
        · intro hpsi
          exact hPhiEval.mpr (hp.mpr (hPsiEval.mp hpsi))
  | existsFO x phi ih =>
      have agree (v : V) : (rho.updateFO x v).AgreeOnFree phi (sigma.updateFO x v) := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro y hy
          by_cases hyx : y = x
          · subst y
            simp [Assignment.updateFO]
          · simpa [Assignment.updateFO, hyx] using hfo y ⟨hyx, hy⟩
        · intro Y hY
          exact hso Y hY
        · intro e he
          exact hefo e he
        · intro E_var hE
          exact heso E_var hE
      constructor
      · rintro ⟨v, hv⟩
        exact ⟨v, (ih (rho.updateFO x v) (sigma.updateFO x v) (agree v)).mp hv⟩
      · rintro ⟨v, hv⟩
        exact ⟨v, (ih (rho.updateFO x v) (sigma.updateFO x v) (agree v)).mpr hv⟩
  | forallFO x phi ih =>
      have agree (v : V) : (rho.updateFO x v).AgreeOnFree phi (sigma.updateFO x v) := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro y hy
          by_cases hyx : y = x
          · subst y
            simp [Assignment.updateFO]
          · simpa [Assignment.updateFO, hyx] using hfo y ⟨hyx, hy⟩
        · intro Y hY
          exact hso Y hY
        · intro e he
          exact hefo e he
        · intro E_var hE
          exact heso E_var hE
      constructor
      · intro hp v
        exact (ih (rho.updateFO x v) (sigma.updateFO x v) (agree v)).mp (hp v)
      · intro hp v
        exact (ih (rho.updateFO x v) (sigma.updateFO x v) (agree v)).mpr (hp v)
  | existsSO X phi ih =>
      have agree (S : Set V) : (rho.updateSO X S).AgreeOnFree phi (sigma.updateSO X S) := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro y hy
          exact hfo y hy
        · intro Y hY
          by_cases hYX : Y = X
          · subst Y
            simp [Assignment.updateSO]
          · simpa [Assignment.updateSO, hYX] using hso Y ⟨hYX, hY⟩
        · intro e he
          exact hefo e he
        · intro E_var hE
          exact heso E_var hE
      constructor
      · rintro ⟨S, hS⟩
        exact ⟨S, (ih (rho.updateSO X S) (sigma.updateSO X S) (agree S)).mp hS⟩
      · rintro ⟨S, hS⟩
        exact ⟨S, (ih (rho.updateSO X S) (sigma.updateSO X S) (agree S)).mpr hS⟩
  | forallSO X phi ih =>
      have agree (S : Set V) : (rho.updateSO X S).AgreeOnFree phi (sigma.updateSO X S) := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro y hy
          exact hfo y hy
        · intro Y hY
          by_cases hYX : Y = X
          · subst Y
            simp [Assignment.updateSO]
          · simpa [Assignment.updateSO, hYX] using hso Y ⟨hYX, hY⟩
        · intro e he
          exact hefo e he
        · intro E_var hE
          exact heso E_var hE
      constructor
      · intro hp S
        exact (ih (rho.updateSO X S) (sigma.updateSO X S) (agree S)).mp (hp S)
      · intro hp S
        exact (ih (rho.updateSO X S) (sigma.updateSO X S) (agree S)).mpr (hp S)
  | existsEdgeFO e phi ih =>
      have agree (val : G.edgeSet) :
          (rho.updateEdgeFO e val).AgreeOnFree phi (sigma.updateEdgeFO e val) := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro y hy
          exact hfo y hy
        · intro Y hY
          exact hso Y hY
        · intro e' he'
          by_cases heq : e' = e
          · subst e'
            simp [Assignment.updateEdgeFO]
          · simpa [Assignment.updateEdgeFO, heq] using hefo e' ⟨heq, he'⟩
        · intro E_var hE
          exact heso E_var hE
      constructor
      · rintro ⟨val, hval⟩
        exact ⟨val, (ih (rho.updateEdgeFO e val) (sigma.updateEdgeFO e val)
          (agree val)).mp hval⟩
      · rintro ⟨val, hval⟩
        exact ⟨val, (ih (rho.updateEdgeFO e val) (sigma.updateEdgeFO e val)
          (agree val)).mpr hval⟩
  | forallEdgeFO e phi ih =>
      have agree (val : G.edgeSet) :
          (rho.updateEdgeFO e val).AgreeOnFree phi (sigma.updateEdgeFO e val) := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro y hy
          exact hfo y hy
        · intro Y hY
          exact hso Y hY
        · intro e' he'
          by_cases heq : e' = e
          · subst e'
            simp [Assignment.updateEdgeFO]
          · simpa [Assignment.updateEdgeFO, heq] using hefo e' ⟨heq, he'⟩
        · intro E_var hE
          exact heso E_var hE
      constructor
      · intro hp val
        exact (ih (rho.updateEdgeFO e val) (sigma.updateEdgeFO e val) (agree val)).mp (hp val)
      · intro hp val
        exact (ih (rho.updateEdgeFO e val) (sigma.updateEdgeFO e val) (agree val)).mpr (hp val)
  | existsEdgeSO E_var phi ih =>
      have agree (S : Set G.edgeSet) :
          (rho.updateEdgeSO E_var S).AgreeOnFree phi (sigma.updateEdgeSO E_var S) := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro y hy
          exact hfo y hy
        · intro Y hY
          exact hso Y hY
        · intro e he
          exact hefo e he
        · intro E' hE'
          by_cases hEq : E' = E_var
          · subst E'
            simp [Assignment.updateEdgeSO]
          · simpa [Assignment.updateEdgeSO, hEq] using heso E' ⟨hEq, hE'⟩
      constructor
      · rintro ⟨S, hS⟩
        exact ⟨S, (ih (rho.updateEdgeSO E_var S) (sigma.updateEdgeSO E_var S)
          (agree S)).mp hS⟩
      · rintro ⟨S, hS⟩
        exact ⟨S, (ih (rho.updateEdgeSO E_var S) (sigma.updateEdgeSO E_var S)
          (agree S)).mpr hS⟩
  | forallEdgeSO E_var phi ih =>
      have agree (S : Set G.edgeSet) :
          (rho.updateEdgeSO E_var S).AgreeOnFree phi (sigma.updateEdgeSO E_var S) := by
        rcases h with ⟨hfo, hso, hefo, heso⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro y hy
          exact hfo y hy
        · intro Y hY
          exact hso Y hY
        · intro e he
          exact hefo e he
        · intro E' hE'
          by_cases hEq : E' = E_var
          · subst E'
            simp [Assignment.updateEdgeSO]
          · simpa [Assignment.updateEdgeSO, hEq] using heso E' ⟨hEq, hE'⟩
      constructor
      · intro hp S
        exact (ih (rho.updateEdgeSO E_var S) (sigma.updateEdgeSO E_var S) (agree S)).mp (hp S)
      · intro hp S
        exact (ih (rho.updateEdgeSO E_var S) (sigma.updateEdgeSO E_var S) (agree S)).mpr (hp S)

/-- A closed formula has assignment-independent `EvalAt` semantics. -/
theorem evalAt_closed_independent {G : SimpleGraph V} {phi : Formula} (hclosed : phi.Closed)
    (rho sigma : Assignment V G.edgeSet) :
    EvalAt phi G rho ↔ EvalAt phi G sigma := by
  apply evalAt_ext_on_free phi
  rcases hclosed with ⟨hfo, hso, hefo, heso⟩
  exact ⟨
    (fun x hx => False.elim (hfo x hx)),
    (fun X hX => False.elim (hso X hX)),
    (fun e he => False.elim (hefo e he)),
    (fun E_var hE => False.elim (heso E_var hE))⟩

/-- For a closed formula, `Eval` is equivalent to evaluating at any chosen assignment. -/
theorem eval_iff_evalAt_of_closed {G : SimpleGraph V} {phi : Formula} (hclosed : phi.Closed)
    (rho : Assignment V G.edgeSet) :
    Eval phi G ↔ EvalAt phi G rho := by
  constructor
  · intro h
    exact h rho
  · intro h sigma
    exact (evalAt_closed_independent hclosed rho sigma).mp h

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
