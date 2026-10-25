module

public import Mathlib

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Sturm-Liouville operators

The Sturm-Liouville operator with coefficients `p` and `q` acts on a function `y` by
`L y = (p y')' + q y`, i.e. `L = d/dx (p(x) d/dx) + q(x)`.

The operator is called *regular* on a finite interval `[a, b]` when `p`, `p'` and `q`
are continuous on `[a, b]` and `p > 0` there.

## Main definitions

* `MathPhysicsTheory.SturmLiouville.operator`: the Sturm-Liouville differential expression
  `y ↦ (p y')' + q y` for arbitrary coefficients `p q : ℝ → ℝ`.
* `MathPhysicsTheory.SturmLiouville.IsRegular`: the coefficients `p` and `q` define a regular
  Sturm-Liouville operator on `[a, b]`.

## Main statements

* `MathPhysicsTheory.SturmLiouville.operator_eq`: for differentiable `p` and twice
  differentiable `y`, `L y = p y'' + p' y' + q y`.

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

theorem operator_apply (p q y : ℝ → ℝ) (x : ℝ) :
    operator (p) (q) (y) (x) = deriv (fun t => p (t) * deriv (y) (t)) (x) + q (x) * y (x) :=
  rfl

/-- Expanded form of the Sturm-Liouville operator: `L y = p y'' + p' y' + q y`. -/
theorem operator_eq {p q y : ℝ → ℝ} {x : ℝ} (hp : DifferentiableAt (ℝ) (p) (x))
    (hy : DifferentiableAt (ℝ) (deriv (y)) (x)) :
    operator (p) (q) (y) (x) =
      p (x) * deriv (deriv (y)) (x) + deriv (p) (x) * deriv (y) (x) + q (x) * y (x) := by
  have h : HasDerivAt (fun t => p (t) * deriv (y) (t))
      (deriv (p) (x) * deriv (y) (x) + p (x) * deriv (deriv (y)) (x)) (x) :=
    hp.hasDerivAt.mul (hy.hasDerivAt)
  rw [operator_apply, h.deriv]
  ring

/-- The coefficients `p` and `q` define a *regular* Sturm-Liouville operator on the finite
interval `[a, b]`: `p` is continuously differentiable and positive on `[a, b]`, and `q` is
continuous on `[a, b]`. -/
structure IsRegular (a b : ℝ) (p q : ℝ → ℝ) : Prop where
  /-- The interval is nondegenerate. -/
  lt : a < b
  /-- `p` and `p'` are continuous on `[a, b]`. -/
  contDiffOn_p : ContDiffOn (ℝ) (1) (p) (Set.Icc (a) (b))
  /-- `q` is continuous on `[a, b]`. -/
  continuousOn_q : ContinuousOn (q) (Set.Icc (a) (b))
  /-- `p` is positive on `[a, b]`. -/
  pos_p : ∀ x ∈ Set.Icc (a) (b), 0 < p (x)

end MathPhysicsTheory.SturmLiouville

end
