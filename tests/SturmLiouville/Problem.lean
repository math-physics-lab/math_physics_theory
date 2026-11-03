import MathPhysicsTheory

/-! Tests for `MathPhysicsTheory.SturmLiouville.Problem`. -/

open MathPhysicsTheory.SturmLiouville MathPhysicsTheory.BoundaryConditions

/-- `y'' = -λ y` on `[0, π]` with Dirichlet conditions `y(0) = 0`, `y(π) = 0`. -/
noncomputable def dirichlet : Problem where
  a := 0
  b := Real.pi
  a_lt_b := Real.pi_pos
  L := { p := 1, q := 0 }
  w := 1
  Ba := { α := 1, β := 0, c := 0 }
  Bb := { α := 1, β := 0, c := Real.pi }
  assumptions := {
    p_pos := fun _ _ => by simp
    w_pos := fun _ _ => by simp
    p_contDiffOn := contDiffOn_const
    q_continuousOn := continuousOn_const
    w_continuousOn := continuousOn_const
    q_nonpos := fun _ _ => by simp
    Ba_c := rfl
    Bb_c := rfl
    Ba_ne := by simp
    Bb_ne := by simp
    Ba_mul_nonpos := by simp
    Bb_mul_nonneg := by simp }

/-- `sin` solves `y'' = -y`, `y(0) = 0`, `y(π) = 0`. -/
example : dirichlet.IsSolution (1) (Real.sin) := by
  refine ⟨Real.contDiff_sin.contDiffOn, ?_⟩
  simp [dirichlet, Operator.apply, Robin.Operator.condition,
    Robin.Operator.apply]

/-- `cos` solves `y'' = -y` but not `y(0) = 0`. -/
example : ¬ dirichlet.IsSolution (1) (Real.cos) := by
  simp [dirichlet, Problem.IsSolution, Robin.Operator.condition, Robin.Operator.apply]

/-- `isSolution_trivial` as a method: `y = 0` solves the Dirichlet problem for any `λ`. -/
example («λ» : ℝ) : dirichlet.IsSolution («λ») (0) := dirichlet.isSolution_trivial («λ»)
