import MathPhysicsTheory
import tests.SturmLiouville.Problem

/-! Tests for `MathPhysicsTheory.SturmLiouville.Eigenvalues`. -/

open MathPhysicsTheory.SturmLiouville MathPhysicsTheory.BoundaryConditions
open MathPhysicsTheory.SturmLiouville.Eigenvalues

/-- `sin` is an eigenfunction of the Dirichlet problem for `λ = 1`: it is nonzero at `π / 2`. -/
example : IsEigenfunction (dirichlet) (1) (Real.sin) :=
  ⟨⟨Real.contDiff_sin.contDiffOn, by simp [dirichlet, Operator.apply, Robin.Operator.Satisfies,
    Robin.Operator.apply]⟩, Real.pi / 2, ⟨by positivity, half_le_self (Real.pi_pos.le)⟩, by simp⟩

/-- `isEigenvalue_of_isEigenfunction`: `1` is an eigenvalue of the Dirichlet problem. -/
example (h : IsEigenfunction (dirichlet) (1) (Real.sin)) : 1 ∈ eigenvalueSet (dirichlet) :=
  isEigenvalue_of_isEigenfunction (h)

/-- `eigenvalueSet_countable`: the eigenvalues of the Dirichlet problem form a countable set. -/
example : (eigenvalueSet (dirichlet)).Countable :=
  eigenvalueSet_countable (dirichlet)

/-- `eigenvalueSet_infinite`: the Dirichlet problem has infinitely many eigenvalues. -/
example : (eigenvalueSet (dirichlet)).Infinite :=
  eigenvalueSet_infinite (dirichlet)

/-- `nonneg_of_mem_eigenvalueSet`: the eigenvalue `1` of the Dirichlet problem is nonnegative. -/
example (h₁ : 1 ∈ eigenvalueSet (dirichlet)) : (0 : ℝ) ≤ 1 :=
  nonneg_of_mem_eigenvalueSet (h₁)

/-- `isEigenfunction_orthogonal`: eigenfunctions of the Dirichlet problem for different eigenvalues
are orthogonal on `[0, π]`. -/
example {X₁ X₂ : ℝ → ℝ} (h₁ : IsEigenfunction (dirichlet) (1) (X₁))
    (h₂ : IsEigenfunction (dirichlet) (4) (X₂)) :
    ∫ x in (dirichlet.a)..(dirichlet.b), X₁ (x) * X₂ (x) * dirichlet.w (x) = 0 :=
  isEigenfunction_orthogonal (dirichlet) (h₁) (h₂) (by norm_num)
