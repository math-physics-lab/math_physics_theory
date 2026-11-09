import MathPhysicsTheory

/-! Tests for `MathPhysicsTheory.ODE.SelfAdjoint`. -/

open MathPhysicsTheory.ODE

/-- `sin` solves `y'' + y = 0`, the equation with `p = 1` and `r = 1`. -/
example : SelfAdjoint.IsSolution (0) (Real.pi) (1) (1) (Real.sin) := by
  refine ⟨Real.contDiff_sin.contDiffOn, fun x _ => ?_⟩
  simp

/-- The coefficients `p = 1`, `r = 1` are regular. -/
theorem regular : SelfAdjoint.RegularCoeffs (0) (Real.pi) (1) (1) where
  p_pos := fun _ _ => by simp
  p_contDiffOn := contDiffOn_const
  r_continuousOn := continuousOn_const

/-- A solution with zero Cauchy data at an interior point vanishes: `y'' + y = 0` with
`y (π / 2) = y' (π / 2) = 0` forces `y = 0`. -/
example {y : ℝ → ℝ} (h : SelfAdjoint.IsSolution (0) (Real.pi) (1) (1) (y))
    (h0 : y (Real.pi / 2) = 0) (h1 : deriv (y) (Real.pi / 2) = 0) :
    ∀ x ∈ Set.Icc (0) (Real.pi), y (x) = 0 :=
  h.eq_zero_of_cauchy (regular) ⟨by positivity, by linarith [Real.pi_pos]⟩ (h0) (h1)
