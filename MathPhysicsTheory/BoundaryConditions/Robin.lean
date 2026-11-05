module

public import Mathlib

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Robin boundary conditions

The Robin boundary operator at a point `c` with coefficients `α` and `β` acts on a function `y`
by `B y = α y(c) + β y'(c)`. A Robin boundary condition prescribes the value of `B y`:
`α y(c) + β y'(c) = g(c)` for a given function `g`. It is homogeneous when `g = 0`, as in a
Sturm-Liouville problem.

`β = 0` gives the Dirichlet operator `y(c)`, and `α = 0` the Neumann operator `y'(c)`.

`applyWithin` and `SatisfiesWithin` take the derivative within a set `s`; at an endpoint `c` of an
interval `s` it is one-sided. Sturm-Liouville problems use them on `[a, b]`.

## References

* R. L. Herman, *Introduction to Partial Differential Equations*, §4.1
  "Sturm-Liouville Operators".
-/

@[expose] public section

namespace MathPhysicsTheory.BoundaryConditions.Robin

/-- A Robin boundary operator: the point `c` and the coefficients `α` and `β` of
`B y = α y(c) + β y'(c)`. -/
structure Operator where
  /-- The coefficient of `y(c)`. -/
  α : ℝ
  /-- The coefficient of `y'(c)`. -/
  β : ℝ
  /-- The point the condition is imposed at. -/
  c : ℝ

namespace Operator

/-- The Robin boundary operator `B y = α y(c) + β y'(c)`. -/
noncomputable def apply (B : Operator) (y : ℝ → ℝ) : ℝ :=
  B.α * y (B.c) + B.β * deriv (y) (B.c)

/-- The Robin operator is additive on functions differentiable at `c`. -/
theorem apply_add (B : Operator) {y z : ℝ → ℝ} (hy : DifferentiableAt (ℝ) (y) (B.c))
    (hz : DifferentiableAt (ℝ) (z) (B.c)) :
    B.apply (fun x => y (x) + z (x)) = B.apply (y) + B.apply (z) := by
  have h : deriv (fun x => y (x) + z (x)) (B.c) = deriv (y) (B.c) + deriv (z) (B.c) :=
    (hy.hasDerivAt.add (hz.hasDerivAt)).deriv
  simp only [apply, h]
  ring

/-- The Robin operator commutes with scalar multiplication. -/
theorem apply_const_mul (B : Operator) (k : ℝ) (y : ℝ → ℝ) :
    B.apply (fun x => k * y (x)) = k * B.apply (y) := by
  simp only [apply, deriv_const_mul_field]
  ring

/-- `y` satisfies the Robin boundary condition with right-hand side `g`:
`α y(c) + β y'(c) = g(c)`. -/
def Satisfies (B : Operator) (g : ℝ → ℝ) (y : ℝ → ℝ) : Prop :=
  B.apply (y) = g (B.c)

/-- If `y` and `z` satisfy Robin conditions with right-hand sides `g₁` and `g₂`, then `y + z`
satisfies the one with right-hand side `g₁ + g₂`. -/
theorem satisfies_add (B : Operator) {g₁ g₂ : ℝ → ℝ} {y z : ℝ → ℝ}
    (hy : DifferentiableAt (ℝ) (y) (B.c)) (hz : DifferentiableAt (ℝ) (z) (B.c))
    (h₁ : B.Satisfies (g₁) (y)) (h₂ : B.Satisfies (g₂) (z)) :
    B.Satisfies (fun x => g₁ (x) + g₂ (x)) (fun x => y (x) + z (x)) := by
  unfold Satisfies at h₁ h₂ ⊢
  rw [B.apply_add (hy) (hz), h₁, h₂]

/-- If `y` satisfies the Robin condition with right-hand side `g`, then `k y` satisfies the one
with right-hand side `k g`. -/
theorem satisfies_const_mul (B : Operator) {g : ℝ → ℝ} {y : ℝ → ℝ} (k : ℝ)
    (h : B.Satisfies (g) (y)) :
    B.Satisfies (fun x => k * g (x)) (fun x => k * y (x)) := by
  unfold Satisfies at h ⊢
  rw [apply_const_mul, h]

/-- The Robin boundary operator `B y = α y(c) + β y'(c)` with the derivative `y'(c)` taken within
a set `s`. At an endpoint of an interval `s` this is the one-sided derivative. -/
noncomputable def applyWithin (B : Operator) (s : Set (ℝ)) (y : ℝ → ℝ) : ℝ :=
  B.α * y (B.c) + B.β * derivWithin (y) (s) (B.c)

/-- `y` satisfies the Robin boundary condition with right-hand side `g`, with the derivative
taken within `s`: `α y(c) + β y'(c) = g(c)`. -/
def SatisfiesWithin (B : Operator) (s : Set (ℝ)) (g : ℝ → ℝ) (y : ℝ → ℝ) : Prop :=
  B.applyWithin (s) (y) = g (B.c)

/-- For `y` differentiable at `c`, the derivative within `s` is the usual derivative. -/
theorem applyWithin_eq_apply (B : Operator) {s : Set (ℝ)} {y : ℝ → ℝ}
    (hs : UniqueDiffWithinAt (ℝ) (s) (B.c)) (hy : DifferentiableAt (ℝ) (y) (B.c)) :
    B.applyWithin (s) (y) = B.apply (y) := by
  rw [applyWithin, apply, hy.derivWithin (hs)]

end Operator

end MathPhysicsTheory.BoundaryConditions.Robin

end
