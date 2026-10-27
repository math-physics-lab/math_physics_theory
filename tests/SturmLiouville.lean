import MathPhysicsTheory

/-! Tests for `MathPhysicsTheory.SturmLiouville`. -/

open MathPhysicsTheory.SturmLiouville

/-- With `p = 1` and `q = 0` the operator is the second derivative. -/
example (y : ℝ → ℝ) (x : ℝ) :
    ({ p := 1, q := 0 : Operator }).apply (y) (x) = deriv (deriv (y)) (x) := by
  simp [Operator.apply]

/-- `L sin = -sin` for `p = 1`, `q = 0`. -/
example (x : ℝ) : ({ p := 1, q := 0 : Operator }).apply (Real.sin) (x) = -Real.sin (x) := by
  simp [Operator.apply]

/-- `apply_expanded` as a method: with `p = 1`, `q = 0` it gives `y''`. -/
example (y : ℝ → ℝ) (hy : Differentiable (ℝ) (deriv (y))) :
    ({ p := 1, q := 0 : Operator }).apply (y) = fun x => deriv (deriv (y)) (x) := by
  rw [({ p := 1, q := 0 : Operator }).apply_expanded (differentiable_const (1)) (hy)]
  simp
