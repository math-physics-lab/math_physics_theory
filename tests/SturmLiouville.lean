import MathPhysicsTheory

/-! Tests for `MathPhysicsTheory.SturmLiouville`. -/

open MathPhysicsTheory.SturmLiouville MathPhysicsTheory.BoundaryConditions

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

/-- `y'' = -μ y` on `[0, π]` with Dirichlet conditions `y(0) = 0`, `y(π) = 0`. -/
noncomputable def dirichlet : Problem where
  a := 0
  b := Real.pi
  a_lt_b := Real.pi_pos
  L := { p := 1, q := 0 }
  w := 1
  p_pos := fun _ _ => by simp
  w_pos := fun _ _ => by simp
  Ba := { α := 1, β := 0, c := 0 }
  Bb := { α := 1, β := 0, c := Real.pi }
  Ba_c := rfl
  Bb_c := rfl

/-- `sin` solves `y'' = -y`, `y(0) = 0`, `y(π) = 0`. -/
example : dirichlet.IsSolution (1) (Real.sin) := by
  simp [dirichlet, Problem.IsSolution, Operator.apply, Robin.Operator.condition,
    Robin.Operator.apply]

/-- `cos` solves `y'' = -y` but not `y(0) = 0`. -/
example : ¬ dirichlet.IsSolution (1) (Real.cos) := by
  simp [dirichlet, Problem.IsSolution, Robin.Operator.condition, Robin.Operator.apply]

/-- `isSolution_trivial` as a method: `y = 0` solves the Dirichlet problem for any `μ`. -/
example (μ : ℝ) : dirichlet.IsSolution (μ) (0) := dirichlet.isSolution_trivial (μ)
