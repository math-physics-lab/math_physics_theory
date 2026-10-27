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

/-- The Sturm-Liouville differential expression with coefficients `p` and `q`:
`L y = d/dx (p(x) y'(x)) + q(x) y(x)`. -/
noncomputable def operator (p q : ℝ → ℝ) (y : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv (fun t => p (t) * deriv (y) (t)) (x) + q (x) * y (x)

/-- Expanded form of the Sturm-Liouville operator: `L y = p y'' + p' y' + q y`. -/
theorem operator_expanded {p q y : ℝ → ℝ} (hp : Differentiable (ℝ) (p))
    (hy : Differentiable (ℝ) (deriv (y))) :
    operator (p) (q) (y) =
      fun x => p (x) * deriv (deriv (y)) (x) + deriv (p) (x) * deriv (y) (x) + q (x) * y (x) := by
  funext x
  have h : HasDerivAt (fun t => p (t) * deriv (y) (t))
      (deriv (p) (x) * deriv (y) (x) + p (x) * deriv (deriv (y)) (x)) (x) :=
    (hp (x)).hasDerivAt.mul ((hy (x)).hasDerivAt)
  rw [operator, h.deriv]
  ring

end MathPhysicsTheory.SturmLiouville

end
