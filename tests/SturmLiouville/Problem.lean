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
  Ba := Dirichlet.Operator.toRobin ({ c := 0 })
  Bb := Dirichlet.Operator.toRobin ({ c := Real.pi })
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
  refine ⟨⟨Real.contDiff_sin.contDiffOn, fun x hx => ?_⟩, ?_⟩
  · change dirichlet.L.applyOn (Set.Icc (0) (Real.pi)) (Real.sin) (x) =
        -1 * dirichlet.w (x) * Real.sin (x)
    rw [Operator.applyOn_eq_apply_of_differentiable (dirichlet.L) (uniqueDiffOn_Icc (Real.pi_pos))
      (hx) (Real.differentiable_sin) (by simp [dirichlet])]
    simp [dirichlet, Operator.apply]
  · simp [dirichlet, Dirichlet.Operator.satisfies_iff]

/-- `cos` solves `y'' = -y` but not `y(0) = 0`. -/
example : ¬ dirichlet.IsSolution (1) (Real.cos) := by
  simp [dirichlet, Problem.IsSolution, Dirichlet.Operator.satisfies_iff]

/-- `isSolution_zero` as a method: `y = 0` solves the Dirichlet problem for any `λ`. -/
example («λ» : ℝ) : dirichlet.IsSolution («λ») (0) := dirichlet.isSolution_zero («λ»)
