import MathPhysicsTheory
import tests.SturmLiouville.Problem

/-! Tests for `MathPhysicsTheory.SturmLiouville.InverseProblem`. -/

open MathPhysicsTheory.SturmLiouville MathPhysicsTheory.BoundaryConditions
open MathPhysicsTheory.SturmLiouville.EigenValues

/-- The inverse problem derived from the Dirichlet problem: its data are the interval, the boundary
operators and the eigenpairs `(λₙ, Xₙ)` of `dirichlet`, given a family `X` of eigenfunctions for the
ordered eigenvalues. -/
noncomputable def dirichletInverse (X : ℕ → ℝ → ℝ)
    (hX : ∀ n, eigen_function (dirichlet) (eigen_values (dirichlet) (n)) (X (n))) :
    InverseProblem where
  a := dirichlet.a
  b := dirichlet.b
  a_lt_b := dirichlet.a_lt_b
  Ba := dirichlet.Ba
  Bb := dirichlet.Bb
  «λₙ» := eigen_values (dirichlet)
  Xₙ := X
  assumptions := ⟨dirichlet, rfl, rfl, rfl, rfl, rfl, hX⟩

/-- The original coefficients `p = 1`, `q = 0`, `w = 1` solve the inverse problem derived from the
Dirichlet problem. -/
example (X : ℕ → ℝ → ℝ)
    (hX : ∀ n, eigen_function (dirichlet) (eigen_values (dirichlet) (n)) (X (n))) :
    (dirichletInverse (X) (hX)).IsSolution ({ p := 1, q := 0 }) (1) := by
  refine ⟨dirichlet.assumptions, fun n x hx => ?_⟩
  have h := (hX (n)).1.2.1 (x) (hx)
  change dirichlet.L.apply (X (n)) (x) +
    eigen_values (dirichlet) (n) * dirichlet.w (x) * X (n) (x) = 0
  linarith
