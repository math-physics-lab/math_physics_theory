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
  change dirichlet.L.applyOn (Set.Icc (dirichlet.a) (dirichlet.b)) (X (n)) (x) +
    eigenvalues (dirichlet) (n) * dirichlet.w (x) * X (n) (x) = 0
  linarith

/-- The reduction of `dirichletInverse` to its eigenpairs `0, 1, 2` is solved by `p = 1`, `q = 0`,
`w = 1`, by `InverseProblem.isSolution_iff_reduce`. -/
example (X : ℕ → ℝ → ℝ)
    (hX : ∀ n, IsEigenfunction (dirichlet) (eigenvalues (dirichlet) (n)) (X (n))) :
    ((dirichletInverse (X) (hX)).reduce (e := ![0, 1, 2]) (by decide)).IsSolution
      ({ p := 1, q := 0 }) (1) := by
  rw [← InverseProblem.isSolution_iff_reduce]
  refine ⟨dirichlet.assumptions, fun n x hx => ?_⟩
  have h := (hX (n)).1.1.2 (x) (hx)
  change dirichlet.L.applyOn (Set.Icc (dirichlet.a) (dirichlet.b)) (X (n)) (x) +
    eigenvalues (dirichlet) (n) * dirichlet.w (x) * X (n) (x) = 0
  linarith

/-- A reduced inverse problem from any three eigenpairs of `dirichlet`, in increasing order. -/
noncomputable def dirichletReduced («λ» : Fin (3) → ℝ) (X : Fin (3) → ℝ → ℝ)
    (hlam : StrictMono («λ»)) (hX : ∀ i, IsEigenfunction (dirichlet) («λ» (i)) (X (i))) :
    ReducedInverseProblem where
  a := dirichlet.a
  b := dirichlet.b
  a_lt_b := dirichlet.a_lt_b
  Ba := dirichlet.Ba
  Bb := dirichlet.Bb
  «λ» := «λ»
  X := X
  assumptions := ⟨hlam, dirichlet, rfl, rfl, rfl, rfl, hX⟩

/-- Every solution of the reduced Dirichlet problem is `c (1, 0, 1)` with `c > 0`. -/
example («λ» : Fin (3) → ℝ) (X : Fin (3) → ℝ → ℝ) (hlam : StrictMono («λ»))
    (hX : ∀ i, IsEigenfunction (dirichlet) («λ» (i)) (X (i))) {p q w : ℝ → ℝ}
    (h : (dirichletReduced («λ») (X) (hlam) (hX)).IsSolution ({ p := p, q := q }) (w)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Set.Icc (0) (Real.pi), p (x) = c ∧ q (x) = 0 ∧ w (x) = c := by
  have h₀ : (dirichletReduced («λ») (X) (hlam) (hX)).IsSolution ({ p := 1, q := 0 }) (1) := by
    refine ⟨dirichlet.assumptions, fun i x hx => ?_⟩
    have := (hX (i)).1.1.2 (x) (hx)
    change dirichlet.L.applyOn (Set.Icc (dirichlet.a) (dirichlet.b)) (X (i)) (x) +
      «λ» (i) * dirichlet.w (x) * X (i) (x) = 0
    linarith
  obtain ⟨c, hc, hx⟩ := ReducedInverseProblem.solution_unique (_) (h₀) (h)
  exact ⟨c, hc, fun x hx' => by simpa using hx (x) (hx')⟩
