import MathPhysicsTheory

/-! Tests for `MathPhysicsTheory.SturmLiouville.Operator`. -/

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

/-- `applyWithin_eq_apply`: on `[0, π]`, the operator with derivatives within `[0, π]` gives
`L sin = -sin`. -/
example {x : ℝ} (hx : x ∈ Set.Icc (0) (Real.pi)) :
    ({ p := 1, q := 0 : Operator }).applyWithin (Set.Icc (0) (Real.pi)) (Real.sin) (x) =
      -Real.sin (x) := by
  rw [Operator.applyWithin_eq_apply (_) (uniqueDiffOn_Icc (Real.pi_pos)) (hx)
    (Real.differentiable_sin) (by simp)]
  simp [Operator.apply]
