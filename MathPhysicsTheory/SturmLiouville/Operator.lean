module

public import Mathlib

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Sturm-Liouville operators

The Sturm-Liouville operator with coefficients `p` and `q` acts on a function `y` by
`L y = (p y')' + q y`.

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

/-- The Sturm-Liouville differential expression on a set `s`, with derivatives taken within `s`:
`L y = d/dx (p(x) y'(x)) + q(x) y(x)`. On `s = [a, b]` this uses only the values of `p`, `q`, `y`
on `[a, b]`, with one-sided derivatives at the endpoints, as for a function that is `C²` on
`[a, b]`. -/
noncomputable def applyOn (L : Operator) (s : Set (ℝ)) (y : ℝ → ℝ) : ℝ → ℝ :=
  fun x => derivWithin (fun x => L.p (x) * derivWithin (y) (s) (x)) (s) (x) + L.q (x) * y (x)

/-- At a point of the interior of `s`, `applyOn` agrees with `apply`. -/
theorem applyOn_eq_apply_of_mem_interior (L : Operator) {s : Set (ℝ)} {y : ℝ → ℝ} {x : ℝ}
    (hx : s ∈ nhds (x)) : L.applyOn (s) (y) (x) = L.apply (y) (x) := by
  have hev : (fun t => L.p (t) * derivWithin (y) (s) (t)) =ᶠ[nhds (x)]
      fun t => L.p (t) * deriv (y) (t) := by
    filter_upwards [eventually_mem_nhds_iff.2 (hx)] with t ht
    rw [derivWithin_of_mem_nhds (ht)]
  rw [applyOn, apply, derivWithin_of_mem_nhds (hx), hev.deriv_eq]

/-- If `y` and the flux `p y'` are differentiable on all of `ℝ`, `applyOn` agrees with `apply` on
any set `s` with unique derivatives, endpoints included. -/
theorem applyOn_eq_apply_of_differentiable (L : Operator) {s : Set (ℝ)} {y : ℝ → ℝ} {x : ℝ}
    (hs : UniqueDiffOn (ℝ) (s)) (hx : x ∈ s) (hy : Differentiable (ℝ) (y))
    (hf : Differentiable (ℝ) (fun t => L.p (t) * deriv (y) (t))) :
    L.applyOn (s) (y) (x) = L.apply (y) (x) := by
  have heq : Set.EqOn (fun t => L.p (t) * derivWithin (y) (s) (t))
      (fun t => L.p (t) * deriv (y) (t)) (s) := fun t ht => by
    dsimp only
    rw [(hy (t)).derivWithin (hs (t) (ht))]
  rw [applyOn, apply, derivWithin_congr (heq) (heq (hx)), (hf (x)).derivWithin (hs (x) (hx))]

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
