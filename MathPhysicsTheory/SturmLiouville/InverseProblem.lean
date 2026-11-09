module

public import Mathlib
public import MathPhysicsTheory.BoundaryConditions.Robin
public import MathPhysicsTheory.SturmLiouville.Eigenvalues
public import MathPhysicsTheory.SturmLiouville.Operator
public import MathPhysicsTheory.SturmLiouville.Problem
public import MathPhysicsTheory.SturmLiouville.Uniqueness

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# The inverse Sturm-Liouville problem

In the Sturm-Liouville problem the coefficients `p`, `q` and the weight `w` are given, and one
looks for the eigenvalues `λₙ` and eigenfunctions `Xₙ`. In the inverse problem the roles are
swapped: the interval `[a, b]`, the boundary conditions and the eigenpairs `(λₙ, Xₙ)` are given,
and one looks for `p`, `q` and `w` such that

* `(p Xₙ')' + q Xₙ = -λₙ w Xₙ` on `[a, b]` for every `n`,

where `p`, `q` and `w` satisfy the same `Assumptions` as in the direct problem. These say which
functions are allowed on `[a, b]`:

* `p` is continuously differentiable and strictly positive (`p > 0`);
* `w` is continuous and strictly positive (`w > 0`);
* `q` is continuous and nonpositive (`q ≤ 0`), so `q = 0` is allowed.

The remaining clauses of `Assumptions` concern only the boundary operators, which are part of the
given data.

The given eigenpairs must come from a Sturm-Liouville problem. This is recorded in
`InverseProblem.Assumptions`: there is a `Problem` on `[a, b]` with the same boundary operators
whose ordered eigenvalues are the `λₙ` and which has `Xₙ` as the eigenfunction for each `λₙ`. The
properties of eigenpairs (`0 ≤ λ₀ < λ₁ < ⋯`, `λₙ → +∞`, the boundary conditions on `Xₙ`, `n` zeros
of `Xₙ`) then follow from the theorems in `MathPhysicsTheory.SturmLiouville.Eigenvalues`.

## References

* R. L. Herman, *Introduction to Partial Differential Equations*, §4.1
  "Sturm-Liouville Operators".
-/

@[expose] public section

namespace MathPhysicsTheory.SturmLiouville

/-- The assumptions on the data of an inverse Sturm-Liouville problem on `[a, b]` with Robin
boundary operators `Ba`, `Bb`, eigenvalues `λₙ` and eigenfunctions `Xₙ`: the data are the
eigenpairs of some Sturm-Liouville problem `P` on the same interval with the same boundary
operators. The `λₙ` are the eigenvalues of `P` in increasing order and `Xₙ` is an eigenfunction for
`λₙ`, for every `n`. -/
structure InverseProblem.Assumptions (a b : ℝ) (Ba Bb : BoundaryConditions.Robin.Operator)
    («λₙ» : ℕ → ℝ) (Xₙ : ℕ → ℝ → ℝ) : Prop where
  /-- Some Sturm-Liouville problem has these eigenpairs. -/
  exists_problem : ∃ P : Problem, P.a = a ∧ P.b = b ∧ P.Ba = Ba ∧ P.Bb = Bb ∧
    «λₙ» = Eigenvalues.eigenvalues (P) ∧ ∀ n, Eigenvalues.IsEigenfunction (P) («λₙ» (n)) (Xₙ (n))

/-- An inverse Sturm-Liouville problem: an interval `[a, b]`, Robin boundary operators `Ba` at `a`
and `Bb` at `b`, and the known eigenvalues `λₙ` with eigenfunctions `Xₙ`. The operator `L` and the
weight `w` are the unknowns. -/
structure InverseProblem where
  /-- The left endpoint of the interval. -/
  a : ℝ
  /-- The right endpoint of the interval. -/
  b : ℝ
  /-- The interval is nondegenerate. -/
  a_lt_b : a < b
  /-- The Robin boundary operator at `a`. -/
  Ba : BoundaryConditions.Robin.Operator
  /-- The Robin boundary operator at `b`. -/
  Bb : BoundaryConditions.Robin.Operator
  /-- The known eigenvalues. -/
  «λₙ» : ℕ → ℝ
  /-- The known eigenfunctions. -/
  Xₙ : ℕ → ℝ → ℝ
  /-- The assumptions on the eigenvalues and eigenfunctions. -/
  assumptions : InverseProblem.Assumptions (a) (b) (Ba) (Bb) («λₙ») (Xₙ)

namespace InverseProblem

/-- `(L, w)` solves the inverse problem: it satisfies the `Assumptions` and, for every `n`,
`L Xₙ + λₙ w Xₙ = 0` on `[a, b]`.

The `Assumptions` fix the allowed types of the unknowns: `p` is `C¹` and positive, `w` is
continuous and positive, and `q` is continuous with `q ≤ 0` (so `q` may be zero, but `p` and `w`
may not). -/
def IsSolution (I : InverseProblem) (L : Operator) (w : ℝ → ℝ) : Prop :=
  SturmLiouville.Assumptions (I.a) (I.b) (L) (w) (I.Ba) (I.Bb) ∧
    ∀ n, ∀ x ∈ Set.Icc (I.a) (I.b),
      L.apply (I.Xₙ (n)) (x) + I.«λₙ» (n) * w (x) * I.Xₙ (n) (x) = 0

/-- Existence: an inverse problem has a solution, namely the operator `P.L` and the weight `P.w` of
a Sturm-Liouville problem `P` whose eigenpairs are the given data. -/
theorem exists_solution (I : InverseProblem) :
    ∃ (L : Operator) (w : ℝ → ℝ), I.IsSolution (L) (w) := by
  obtain ⟨P, ha, hb, hBa, hBb, -, hP⟩ := I.assumptions.exists_problem
  refine ⟨P.L, P.w, ?_, ?_⟩
  · have hA := P.assumptions
    rw [ha, hb, hBa, hBb] at hA
    exact hA
  · intro n x hx
    have hx' : x ∈ Set.Icc (P.a) (P.b) := by rwa [ha, hb]
    have := (hP (n)).1.2.1 (x) (hx')
    linarith

/-- Uniqueness up to a constant factor: two solutions `(p₁, q₁, w₁)` and `(p₂, q₂, w₂)` of the same
inverse problem differ by a positive constant `c`, that is `p₂ = c p₁`, `q₂ = c q₁` and
`w₂ = c w₁` on `[a, b]`.

The factor cannot be removed: the equation `(p Xₙ')' + q Xₙ + λₙ w Xₙ = 0` is linear in
`(p, q, w)`, so `(c p, c q, c w)` is a solution whenever `(p, q, w)` is, and `c > 0` keeps `p` and
`w` positive. Fixing the scale, for example `p (a)`, makes the solution unique. -/
theorem solution_unique (I : InverseProblem) {p₁ q₁ p₂ q₂ w₁ w₂ : ℝ → ℝ}
    (h₁ : I.IsSolution ({ p := p₁, q := q₁ }) (w₁))
    (h₂ : I.IsSolution ({ p := p₂, q := q₂ }) (w₂)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Set.Icc (I.a) (I.b),
      p₂ (x) = c * p₁ (x) ∧ q₂ (x) = c * q₁ (x) ∧ w₂ (x) = c * w₁ (x) := by
  obtain ⟨P, ha, hb, hBa, hBb, hev, hP⟩ := I.assumptions.exists_problem
  have hlam : StrictMono (I.«λₙ») := by
    rw [hev]
    exact (Classical.choose_spec (Eigenvalues.exists_eigenvalue_seq (P))).1
  have hX : ∀ n, ContDiffOn (ℝ) (2) (I.Xₙ (n)) (Set.Icc (I.a) (I.b)) := fun n => by
    have := (hP (n)).1.1
    rwa [ha, hb] at this
  have hne : ∀ n, ∃ x ∈ Set.Icc (I.a) (I.b), I.Xₙ (n) (x) ≠ 0 := fun n => by
    have := (hP (n)).2
    rwa [ha, hb] at this
  have hc : ∀ {p q w : ℝ → ℝ}, I.IsSolution ({ p := p, q := q }) (w) →
      RegularCoeffs (I.a) (I.b) (p) (q) (w) := fun h =>
    { p_pos := h.1.p_pos
      w_pos := h.1.w_pos
      p_contDiffOn := h.1.p_contDiffOn
      q_continuousOn := h.1.q_continuousOn
      w_continuousOn := h.1.w_continuousOn }
  have hs : ∀ {p q w : ℝ → ℝ}, I.IsSolution ({ p := p, q := q }) (w) →
      ∀ n, ODESolution (I.a) (I.b) (p) (q) (w) (I.«λₙ» (n)) (I.Xₙ (n)) := fun h n =>
    ⟨hX (n), fun x hx => h.2 (n) (x) (hx)⟩
  exact proportional_of_eigenpairs (I.a_lt_b) (hc (h₁)) (hc (h₂)) (hlam) (hs (h₁)) (hs (h₂)) (hne)

end InverseProblem

end MathPhysicsTheory.SturmLiouville

end
