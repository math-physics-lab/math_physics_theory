import MathPhysicsTheory
import tests.SturmLiouville.Problem

/-! Tests for `MathPhysicsTheory.SturmLiouville.EigenValues`. -/

open MathPhysicsTheory.SturmLiouville MathPhysicsTheory.BoundaryConditions
open MathPhysicsTheory.SturmLiouville.EigenValues

/-- `sin` is an eigenfunction of the Dirichlet problem for `λ = 1`: it is nonzero at `π / 2`. -/
example : IsEigenfunction (dirichlet) (1) (Real.sin) :=
  ⟨by simp [dirichlet, Problem.IsSolution, Operator.apply, Robin.Operator.condition,
    Robin.Operator.apply], Real.pi / 2, ⟨by positivity, half_le_self (Real.pi_pos.le)⟩, by simp⟩

/-- `IsEigenfunction.isEigenvalue` as a method: `1` is an eigenvalue of the Dirichlet problem. -/
example (h : IsEigenfunction (dirichlet) (1) (Real.sin)) : 1 ∈ EigenvaluesSet (dirichlet) :=
  h.isEigenvalue

/-- `eigenvalues_countable`: the eigenvalues of the Dirichlet problem form a countable set. -/
example : (EigenvaluesSet (dirichlet)).Countable :=
  eigenvalues_countable (dirichlet)

/-- `eigenvalues_infinite`: the Dirichlet problem has infinitely many eigenvalues. -/
example : (EigenvaluesSet (dirichlet)).Infinite :=
  eigenvalues_infinite (dirichlet)

/-- `eigenvalues_nonneg`: the eigenvalue `1` of the Dirichlet problem is nonnegative. -/
example (h₁ : 1 ∈ EigenvaluesSet (dirichlet)) : (0 : ℝ) ≤ 1 :=
  eigenvalues_nonneg (h₁)
