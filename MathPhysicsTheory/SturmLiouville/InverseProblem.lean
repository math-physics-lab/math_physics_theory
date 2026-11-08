module

public import Mathlib
public import MathPhysicsTheory.BoundaryConditions.Robin
public import MathPhysicsTheory.SturmLiouville.Eigenvalues
public import MathPhysicsTheory.SturmLiouville.Operator
public import MathPhysicsTheory.SturmLiouville.Problem

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

## References

* R. L. Herman, *Introduction to Partial Differential Equations*, §4.1
  "Sturm-Liouville Operators".
-/

@[expose] public section

namespace MathPhysicsTheory.SturmLiouville

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

namespace InverseProblem

/-- `(L, w)` solves the inverse problem: it satisfies the `Assumptions` and, for every `n`,
`L Xₙ + λₙ w Xₙ = 0` on `[a, b]`.

The `Assumptions` fix the allowed types of the unknowns: `p` is `C¹` and positive, `w` is
continuous and positive, and `q` is continuous with `q ≤ 0` (so `q` may be zero, but `p` and `w`
may not). -/
def IsSolution (I : InverseProblem) (L : Operator) (w : ℝ → ℝ) : Prop :=
  Assumptions (I.a) (I.b) (L) (w) (I.Ba) (I.Bb) ∧
    ∀ n, ∀ x ∈ Set.Icc (I.a) (I.b),
      L.apply (I.Xₙ (n)) (x) + I.«λₙ» (n) * w (x) * I.Xₙ (n) (x) = 0

/-- Existence: if the data `(λₙ, Xₙ)` is the full sequence of eigenpairs (indexed by all `n : ℕ`)
of some Sturm-Liouville problem `P` on the same interval with the same boundary operators, then the
inverse problem has a solution, namely the operator `P.L` and the weight `P.w` of `P`. -/
theorem exists_solution (I : InverseProblem)
    (h : ∃ P : Problem, P.a = I.a ∧ P.b = I.b ∧ P.Ba = I.Ba ∧ P.Bb = I.Bb ∧
      ∀ n, Eigenvalues.IsEigenfunction (P) (I.«λₙ» (n)) (I.Xₙ (n))) :
    ∃ (L : Operator) (w : ℝ → ℝ), I.IsSolution (L) (w) := by
  obtain ⟨P, ha, hb, hBa, hBb, hP⟩ := h
  refine ⟨P.L, P.w, ?_, ?_⟩
  · have hA := P.assumptions
    rw [ha, hb, hBa, hBb] at hA
    exact hA
  · intro n x hx
    have hx' : x ∈ Set.Icc (P.a) (P.b) := by rwa [ha, hb]
    have := (hP (n)).1.2.1 (x) (hx')
    linarith

end InverseProblem

end MathPhysicsTheory.SturmLiouville

end
