import MathPhysicsTheory
import tests.SturmLiouville.Problem

/-! Tests for `MathPhysicsTheory.SturmLiouville.InverseSpectral`. -/

open MathPhysicsTheory.SturmLiouville MathPhysicsTheory.BoundaryConditions
open MathPhysicsTheory.SturmLiouville.InverseSpectral

/-- `q = 0` is admissible for Dirichlet conditions on `[0, π]`. -/
theorem admissible_zero_dirichlet :
    Admissible (0) (Real.pi) (Dirichlet.Operator.toRobin ({ c := 0 }))
      (Dirichlet.Operator.toRobin ({ c := Real.pi })) (0) :=
  dirichlet.assumptions

/-- `q = 0` is admissible for a Dirichlet condition at `0` and a Neumann condition at `π`. -/
theorem admissible_zero_dirichlet_neumann :
    Admissible (0) (Real.pi) (Dirichlet.Operator.toRobin ({ c := 0 }))
      (Neumann.Operator.toRobin ({ c := Real.pi })) (0) where
  p_pos := fun _ _ => by simp [normalOperator]
  w_pos := fun _ _ => by simp
  p_contDiffOn := contDiffOn_const
  q_continuousOn := continuousOn_const
  w_continuousOn := continuousOn_const
  q_nonpos := fun _ _ => by simp [normalOperator]
  Ba_c := rfl
  Bb_c := rfl
  Ba_ne := by simp [Dirichlet.Operator.toRobin]
  Bb_ne := by simp [Neumann.Operator.toRobin]
  Ba_mul_nonpos := by simp [Dirichlet.Operator.toRobin]
  Bb_mul_nonneg := by simp [Neumann.Operator.toRobin]

/-- Borg's problem for `q = 0` on `[0, π]`: the Dirichlet-Dirichlet and Dirichlet-Neumann
spectra. -/
noncomputable def borgZero : TwoSpectra where
  a := 0
  b := Real.pi
  a_lt_b := Real.pi_pos
  Ba := Dirichlet.Operator.toRobin ({ c := 0 })
  Bb₁ := Dirichlet.Operator.toRobin ({ c := Real.pi })
  Bb₂ := Neumann.Operator.toRobin ({ c := Real.pi })
  Bb_ne := by simp [Dirichlet.Operator.toRobin, Neumann.Operator.toRobin]
  μ₁ := Eigenvalues.eigenvalues (normalProblem (Real.pi_pos) (admissible_zero_dirichlet))
  μ₂ := Eigenvalues.eigenvalues (normalProblem (Real.pi_pos) (admissible_zero_dirichlet_neumann))
  exists_potential :=
    ⟨0, ⟨admissible_zero_dirichlet, rfl⟩, ⟨admissible_zero_dirichlet_neumann, rfl⟩⟩

/-- `q = 0` solves it. -/
example : borgZero.IsSolution (0) :=
  ⟨⟨admissible_zero_dirichlet, rfl⟩, ⟨admissible_zero_dirichlet_neumann, rfl⟩⟩
