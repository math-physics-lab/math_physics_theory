module

public import Mathlib

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Sturm-Liouville operators

The Sturm-Liouville operator with coefficients `p` and `q` acts on a function `y` by
`L y = (p y')' + q y`.

`applyWithin` takes the derivatives within a set `s`; on an interval they are one-sided at the
endpoints. Sturm-Liouville problems use it on `[a, b]`.

## Example

With `p = 1` and `q = 0` the operator is the second derivative, so `L sin = -sin`.

```lean
example (x : ℝ) : ({ p := 1, q := 0 : Operator }).apply (Real.sin) (x) = -Real.sin (x) := by
  simp [Operator.apply]
```

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
  fun x => deriv (fun x => L.p (x) * deriv (y) (x)) (x) + L.q (x) * y (x)

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

/-- The Sturm-Liouville differential expression `L y = (p y')' + q y` with the derivatives taken
within a set `s`. On an interval `s` the derivatives at the endpoints are one-sided. -/
noncomputable def applyWithin (L : Operator) (s : Set (ℝ)) (y : ℝ → ℝ) : ℝ → ℝ :=
  fun x => derivWithin (fun x => L.p (x) * derivWithin (y) (s) (x)) (s) (x) + L.q (x) * y (x)

/-- For `y` and `p y'` differentiable, the derivatives within `s` are the usual derivatives. -/
theorem applyWithin_eq_apply (L : Operator) {s : Set (ℝ)} {y : ℝ → ℝ} {x : ℝ}
    (hs : UniqueDiffOn (ℝ) (s)) (hx : x ∈ s) (hy : Differentiable (ℝ) (y))
    (hpy : DifferentiableAt (ℝ) (fun x => L.p (x) * deriv (y) (x)) (x)) :
    L.applyWithin (s) (y) (x) = L.apply (y) (x) := by
  have h : Set.EqOn (fun x => L.p (x) * derivWithin (y) (s) (x))
      (fun x => L.p (x) * deriv (y) (x)) (s) := fun z hz => by
    simp only [(hy (z)).derivWithin (hs (z) (hz))]
  simp only [applyWithin, apply]
  rw [derivWithin_congr (h) (h (hx)), hpy.derivWithin (hs (x) (hx))]

end Operator

end MathPhysicsTheory.SturmLiouville

end
