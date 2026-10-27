import MathPhysicsTheory

/-! Tests for `MathPhysicsTheory.BoundaryConditions.Robin`. -/

open MathPhysicsTheory.BoundaryConditions.Robin

/-- `2 exp(0) + 3 exp'(0) = 5`. -/
example : ({ α := 2, β := 3, c := 0 : Operator }).apply (Real.exp) = 5 := by
  norm_num [Operator.apply]

/-- `exp` is annihilated by `-y(c) + y'(c)` at every point. -/
example (c : ℝ) : ({ α := -1, β := 1, c := c : Operator }).apply (Real.exp) = 0 := by
  simp [Operator.apply]

/-- With `β = 0` the operator is evaluation: `sin(π) = 0`. -/
example : ({ α := 1, β := 0, c := Real.pi : Operator }).apply (Real.sin) = 0 := by
  simp [Operator.apply]

/-- With `α = 0` the operator is the derivative: `cos'(π) = -sin(π) = 0`. -/
example : ({ α := 0, β := 1, c := Real.pi : Operator }).apply (Real.cos) = 0 := by
  simp [Operator.apply]

/-- `exp` satisfies `2 y(0) + 3 y'(0) = 5`. -/
example : ({ α := 2, β := 3, c := 0 : Operator }).condition (fun _ => 5) (Real.exp) := by
  norm_num [Operator.condition, Operator.apply]

/-- `sin` satisfies the homogeneous Dirichlet condition `y(π) = 0`. -/
example : ({ α := 1, β := 0, c := Real.pi : Operator }).condition (0) (Real.sin) := by
  simp [Operator.condition, Operator.apply]
