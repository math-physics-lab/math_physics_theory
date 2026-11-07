import MathPhysicsTheory

/-! Tests for `MathPhysicsTheory.BoundaryConditions.Dirichlet`. -/

open MathPhysicsTheory.BoundaryConditions
open MathPhysicsTheory.BoundaryConditions.Dirichlet

/-- The Dirichlet operator is evaluation: `exp(0) = 1`. -/
example : ({ c := 0 : Operator }).apply (Real.exp) = 1 := by
  simp

/-- It agrees with the Robin operator with `α = 1`, `β = 0`. -/
example (c : ℝ) (y : ℝ → ℝ) :
    ({ c := c : Operator }).apply (y) =
      ({ α := 1, β := 0, c := c : Robin.Operator }).apply (y) :=
  rfl

/-- No differentiability is needed for additivity: `|x| + x` at `0`. -/
example : ({ c := 0 : Operator }).apply (fun x => |x| + x) =
    ({ c := 0 : Operator }).apply (fun x => |x|) + ({ c := 0 : Operator }).apply (fun x => x) :=
  Operator.apply_add (_) (fun x => |x|) (fun x => x)

/-- `sin` satisfies the homogeneous Dirichlet condition `y(π) = 0`. -/
example : ({ c := Real.pi : Operator }).Satisfies (0) (Real.sin) := by
  simp [Operator.satisfies_iff]

/-- `cos` does not satisfy `y(0) = 0`. -/
example : ¬ ({ c := 0 : Operator }).Satisfies (0) (Real.cos) := by
  simp [Operator.satisfies_iff]

/-- `exp` satisfies `y(0) = 1`, so `3 exp` satisfies `y(0) = 3`. -/
example : ({ c := 0 : Operator }).Satisfies (fun _ => 3 * 1) (fun x => 3 * Real.exp (x)) :=
  Operator.satisfies_const_mul (_) (3) (by simp [Operator.satisfies_iff])
