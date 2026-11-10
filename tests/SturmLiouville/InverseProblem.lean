import MathPhysicsTheory
import tests.SturmLiouville.Problem

/-! Tests for `MathPhysicsTheory.SturmLiouville.InverseProblem`. -/

open MathPhysicsTheory.SturmLiouville MathPhysicsTheory.BoundaryConditions
open MathPhysicsTheory.SturmLiouville.Eigenvalues

/-- The inverse problem derived from the Dirichlet problem: its data are the interval, the boundary
operators and the eigenpairs `(λₙ, Xₙ)` of `dirichlet`, given a family `X` of eigenfunctions for the
ordered eigenvalues. -/
noncomputable def dirichletInverse (X : ℕ → ℝ → ℝ)
    (hX : ∀ n, IsEigenfunction (dirichlet) (eigenvalues (dirichlet) (n)) (X (n))) :
    InverseProblem where
  a := dirichlet.a
  b := dirichlet.b
  a_lt_b := dirichlet.a_lt_b
  Ba := dirichlet.Ba
  Bb := dirichlet.Bb
  «λₙ» := eigenvalues (dirichlet)
  Xₙ := X
  assumptions := ⟨dirichlet, rfl, rfl, rfl, rfl, rfl, hX⟩

/-- The original coefficients `p = 1`, `q = 0`, `w = 1` solve the inverse problem derived from the
Dirichlet problem. -/
example (X : ℕ → ℝ → ℝ)
    (hX : ∀ n, IsEigenfunction (dirichlet) (eigenvalues (dirichlet) (n)) (X (n))) :
    (dirichletInverse (X) (hX)).IsSolution ({ p := 1, q := 0 }) (1) := by
  refine ⟨dirichlet.assumptions, fun n x hx => ?_⟩
  have h := (hX (n)).1.1.2 (x) (hx)
  change dirichlet.L.apply (X (n)) (x) +
    eigenvalues (dirichlet) (n) * dirichlet.w (x) * X (n) (x) = 0
  linarith

/-- For `p = 1`, `q = 0`, `w = 1` the reconstruction formulas return `p' / p = 0`, `q / p = 0` and
`w / p = 1` at every interior point where `fluxDet ≠ 0`. -/
example (X : ℕ → ℝ → ℝ)
    (hX : ∀ n, IsEigenfunction (dirichlet) (eigenvalues (dirichlet) (n)) (X (n)))
    (hsol : (dirichletInverse (X) (hX)).IsSolution ({ p := 1, q := 0 }) (1)) {x : ℝ}
    (hx : x ∈ Set.Ioo (dirichlet.a) (dirichlet.b))
    (hD : InverseProblem.fluxDet (eigenvalues (dirichlet)) (X) (x) ≠ 0) :
    InverseProblem.alphaNum (eigenvalues (dirichlet)) (X) (x) /
        InverseProblem.fluxDet (eigenvalues (dirichlet)) (X) (x) = 0 ∧
      InverseProblem.betaNum (eigenvalues (dirichlet)) (X) (x) /
        InverseProblem.fluxDet (eigenvalues (dirichlet)) (X) (x) = 0 ∧
      InverseProblem.gammaNum (X) (x) /
        InverseProblem.fluxDet (eigenvalues (dirichlet)) (X) (x) = 1 := by
  obtain ⟨h₁, h₂, h₃⟩ := hsol.reconstruction_formulas (hx) (hD)
  have e₁ : deriv (fun _ : ℝ => (1 : ℝ)) (x) / 1 =
      InverseProblem.alphaNum (eigenvalues (dirichlet)) (X) (x) /
        InverseProblem.fluxDet (eigenvalues (dirichlet)) (X) (x) := h₁
  have e₂ : (0 : ℝ) / 1 = InverseProblem.betaNum (eigenvalues (dirichlet)) (X) (x) /
      InverseProblem.fluxDet (eigenvalues (dirichlet)) (X) (x) := h₂
  have e₃ : (1 : ℝ) / 1 = InverseProblem.gammaNum (X) (x) /
      InverseProblem.fluxDet (eigenvalues (dirichlet)) (X) (x) := h₃
  refine ⟨?_, ?_, ?_⟩
  · simpa using e₁.symm
  · simpa using e₂.symm
  · simpa using e₃.symm
