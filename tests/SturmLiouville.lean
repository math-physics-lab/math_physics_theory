import MathPhysicsTheory

/-! Tests for `MathPhysicsTheory.SturmLiouville`. -/

open MathPhysicsTheory.SturmLiouville

/-- With `p = 1` and `q = 0` the operator is the second derivative. -/
example (y : ℝ → ℝ) (x : ℝ) : operator (1) (0) (y) (x) = deriv (deriv (y)) (x) := by
  simp [operator]

/-- `L sin = -sin` for `p = 1`, `q = 0`. -/
example (x : ℝ) : operator (1) (0) (Real.sin) (x) = -Real.sin (x) := by
  simp [operator]

/-- The operator `y ↦ y''` is regular on `[0, π]`. -/
example : IsRegular (0) (Real.pi) (1) (0) where
  lt := Real.pi_pos
  contDiffOn_p := contDiffOn_const
  continuousOn_q := continuousOn_const
  pos_p _ _ := one_pos
