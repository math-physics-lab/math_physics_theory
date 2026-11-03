import MathPhysicsTheory
import tests.SturmLiouville.Problem

/-! Tests for `MathPhysicsTheory.SturmLiouville.EigenValues`. -/

open MathPhysicsTheory.SturmLiouville MathPhysicsTheory.BoundaryConditions
open MathPhysicsTheory.SturmLiouville.EigenValues

/-- `sin` is an eigenfunction of the Dirichlet problem for `λ = 1`: it is nonzero at `π / 2`. -/
example : eigen_function (dirichlet) (1) (Real.sin) :=
  ⟨⟨Real.contDiff_sin.contDiffOn, by simp [dirichlet, Operator.apply, Robin.Operator.condition,
    Robin.Operator.apply]⟩, Real.pi / 2, ⟨by positivity, half_le_self (Real.pi_pos.le)⟩, by simp⟩

/-- `eigen_value_of_eigen_function`: `1` is an eigenvalue of the Dirichlet problem. -/
example (h : eigen_function (dirichlet) (1) (Real.sin)) : 1 ∈ eigen_values_set (dirichlet) :=
  eigen_value_of_eigen_function (h)

/-- `eigen_values_countable`: the eigenvalues of the Dirichlet problem form a countable set. -/
example : (eigen_values_set (dirichlet)).Countable :=
  eigen_values_countable (dirichlet)

/-- `eigen_values_infinite`: the Dirichlet problem has infinitely many eigenvalues. -/
example : (eigen_values_set (dirichlet)).Infinite :=
  eigen_values_infinite (dirichlet)

/-- `eigen_values_nonneg`: the eigenvalue `1` of the Dirichlet problem is nonnegative. -/
example (h₁ : 1 ∈ eigen_values_set (dirichlet)) : (0 : ℝ) ≤ 1 :=
  eigen_values_nonneg (h₁)

/-- `eigen_functions_orthogonal`: eigenfunctions of the Dirichlet problem for different eigenvalues
are orthogonal on `[0, π]`. -/
example {X₁ X₂ : ℝ → ℝ} (h₁ : eigen_function (dirichlet) (1) (X₁))
    (h₂ : eigen_function (dirichlet) (4) (X₂)) :
    ∫ x in (dirichlet.a)..(dirichlet.b), X₁ (x) * X₂ (x) * dirichlet.w (x) = 0 :=
  eigen_functions_orthogonal (dirichlet) (h₁) (h₂) (by norm_num)
