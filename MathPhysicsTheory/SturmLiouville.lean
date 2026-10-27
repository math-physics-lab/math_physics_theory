module

public import Mathlib

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Sturm-Liouville operators

The Sturm-Liouville operator with coefficients `p` and `q` acts on a function `y` by
`L y = (p y')' + q y`, i.e. `L = d/dx (p(x) d/dx) + q(x)`.

## References

* R. L. Herman, *Introduction to Partial Differential Equations*, §4.1
  "Sturm-Liouville Operators".
-/

@[expose] public section

namespace MathPhysicsTheory.SturmLiouville

/-- A Sturm-Liouville operator, given by its coefficients `p` and `q` in
`L y = d/dx (p(x) y'(x)) + q(x) y(x)`. -/
structure Operator where
  /-- The coefficient inside the derivative. -/
  p : ℝ → ℝ
  /-- The potential. -/
  q : ℝ → ℝ

namespace Operator

/-- The Sturm-Liouville differential expression `L y = d/dx (p(x) y'(x)) + q(x) y(x)`. -/
noncomputable def apply (L : Operator) (y : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv (fun t => L.p (t) * deriv (y) (t)) (x) + L.q (x) * y (x)

/-- Expanded form of the Sturm-Liouville operator: `L y = p y'' + p' y' + q y`. -/
theorem apply_expanded (L : Operator) {y : ℝ → ℝ} (hp : Differentiable (ℝ) (L.p))
    (hy : Differentiable (ℝ) (deriv (y))) :
    L.apply (y) =
      fun x => L.p (x) * deriv (deriv (y)) (x) + deriv (L.p) (x) * deriv (y) (x) +
        L.q (x) * y (x) := by
  funext x
  have h : HasDerivAt (fun t => L.p (t) * deriv (y) (t))
      (deriv (L.p) (x) * deriv (y) (x) + L.p (x) * deriv (deriv (y)) (x)) (x) :=
    (hp (x)).hasDerivAt.mul ((hy (x)).hasDerivAt)
  rw [apply, h.deriv]
  ring

end Operator

end MathPhysicsTheory.SturmLiouville

end
