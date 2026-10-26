import MathPhysicsTheory

/-! Tests for `MathPhysicsTheory.BoundaryConditions.Robin`. -/

open MathPhysicsTheory.BoundaryConditions

/-- `2 exp(0) + 3 exp'(0) = 5`. -/
example : robin (2) (3) (0) (Real.exp) = 5 := by
  norm_num [robin]

/-- `exp` is annihilated by `-y(c) + y'(c)` at every point. -/
example (c : ℝ) : robin (-1) (1) (c) (Real.exp) = 0 := by
  simp [robin]

/-- With `β = 0` the operator is evaluation: `sin(π) = 0`. -/
example : robin (1) (0) (Real.pi) (Real.sin) = 0 := by
  simp [robin]

/-- With `α = 0` the operator is the derivative: `cos'(π) = -sin(π) = 0`. -/
example : robin (0) (1) (Real.pi) (Real.cos) = 0 := by
  simp [robin]

/-- `exp` satisfies `2 y(0) + 3 y'(0) = 5`. -/
example : robinCondition (2) (3) (5) (0) (Real.exp) := by
  norm_num [robinCondition, robin]

/-- `sin` satisfies the homogeneous Dirichlet condition `y(π) = 0`. -/
example : robinCondition (1) (0) (0) (Real.pi) (Real.sin) := by
  simp [robinCondition, robin]
