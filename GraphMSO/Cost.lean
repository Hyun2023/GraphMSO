import Mathlib.Data.Nat.Basic

/-!
# A small abstract cost layer

`Costed α` records a mathematical result together with an abstract operation
count.  It is deliberately independent of Lean's evaluator: clients decide
which primitive operations cost one step, and proofs track the resulting
counter compositionally.
-/

universe u v

/-- A value paired with an abstract natural-number operation count. -/
structure Costed (α : Type u) where
  value : α
  cost : ℕ
  deriving Repr

namespace Costed

variable {α : Type u} {β : Type v}

/-- Return a value without performing a charged operation. -/
def pure (a : α) : Costed α :=
  ⟨a, 0⟩

/-- Perform one abstract primitive operation and return its result. -/
def tick (a : α) : Costed α :=
  ⟨a, 1⟩

/-- Add an explicitly specified number of primitive operations. -/
def charge (n : ℕ) (a : α) : Costed α :=
  ⟨a, n⟩

/-- Sequential composition adds the costs of its two computations. -/
def bind (x : Costed α) (f : α → Costed β) : Costed β :=
  let y := f x.value
  ⟨y.value, x.cost + y.cost⟩

/-- Apply a pure function without adding a new charged operation. -/
def map (f : α → β) (x : Costed α) : Costed β :=
  ⟨f x.value, x.cost⟩

/-- Start at zero and perform exactly `n` unit-cost operations. -/
def ticks : ℕ → Costed Unit
  | 0 => pure ()
  | n + 1 => (ticks n).bind fun _ => tick ()

@[simp] theorem pure_value (a : α) : (pure a).value = a :=
  rfl

@[simp] theorem pure_cost (a : α) : (pure a).cost = 0 :=
  rfl

@[simp] theorem tick_value (a : α) : (tick a).value = a :=
  rfl

@[simp] theorem tick_cost (a : α) : (tick a).cost = 1 :=
  rfl

@[simp] theorem charge_value (n : ℕ) (a : α) : (charge n a).value = a :=
  rfl

@[simp] theorem charge_cost (n : ℕ) (a : α) : (charge n a).cost = n :=
  rfl

@[simp] theorem bind_value (x : Costed α) (f : α → Costed β) :
    (x.bind f).value = (f x.value).value := by
  rfl

@[simp] theorem bind_cost (x : Costed α) (f : α → Costed β) :
    (x.bind f).cost = x.cost + (f x.value).cost := by
  rfl

@[simp] theorem map_value (f : α → β) (x : Costed α) :
    (x.map f).value = f x.value :=
  rfl

@[simp] theorem map_cost (f : α → β) (x : Costed α) :
    (x.map f).cost = x.cost :=
  rfl

@[simp] theorem ticks_value (n : ℕ) : (ticks n).value = () := by
  induction n <;> simp [ticks, *]

@[simp] theorem ticks_cost (n : ℕ) : (ticks n).cost = n := by
  induction n <;> simp [ticks, *]

end Costed
