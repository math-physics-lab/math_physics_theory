import MathPhysicsTheory

/-! Tests for `MathPhysicsTheory.BoundaryConditions.Neumann`. -/

open MathPhysicsTheory.BoundaryConditions
open MathPhysicsTheory.BoundaryConditions.Neumann

/-- The Neumann operator is the derivative: `exp'(0) = 1`. -/
example : ({ c := 0 : Operator }).apply (Real.exp) = 1 := by
  simp

/-- It agrees with the Robin operator with `α = 0`, `β = 1`. -/
example (c : ℝ) (y : ℝ → ℝ) :
    ({ c := c : Operator }).apply (y) =
      ({ α := 0, β := 1, c := c : Robin.Operator }).apply (y) :=
  rfl

/-- `cos` satisfies the homogeneous Neumann condition `y'(π) = 0`. -/
example : ({ c := Real.pi : Operator }).Satisfies (0) (Real.cos) := by
  simp [Operator.satisfies_iff]

/-- `sin` does not satisfy `y'(0) = 0`. -/
example : ¬ ({ c := 0 : Operator }).Satisfies (0) (Real.sin) := by
  simp [Operator.satisfies_iff]

/-- `sin + cos` satisfies `y'(0) = 1 + 0`. -/
example : ({ c := 0 : Operator }).Satisfies (fun _ => 1 + 0)
    (fun x => Real.sin (x) + Real.cos (x)) :=
  Operator.satisfies_add (_) (Real.differentiable_sin (_)) (Real.differentiable_cos (_))
    (by simp [Operator.satisfies_iff]) (by simp [Operator.satisfies_iff])
