module

public import Mathlib

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Robin boundary conditions

The Robin boundary operator at a point `c` with coefficients `α` and `β` acts on a function `y`
by `B y = α y(c) + β y'(c)`. A Robin boundary condition prescribes the value of `B y`:
`α y(c) + β y'(c) = γ`. It is homogeneous when `γ = 0`, as in a Sturm-Liouville problem.

`β = 0` gives the Dirichlet operator `y(c)`, and `α = 0` the Neumann operator `y'(c)`.

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

/-- The Robin boundary condition with right-hand side `γ`: `α y(c) + β y'(c) = γ`. -/
def condition (B : Operator) (γ : ℝ) (y : ℝ → ℝ) : Prop :=
  B.apply (y) = γ

/-- If `y` and `z` satisfy Robin conditions with right-hand sides `γ₁` and `γ₂`, then `y + z`
satisfies the one with right-hand side `γ₁ + γ₂`. -/
theorem condition_add (B : Operator) {γ₁ γ₂ : ℝ} {y z : ℝ → ℝ}
    (hy : DifferentiableAt (ℝ) (y) (B.c)) (hz : DifferentiableAt (ℝ) (z) (B.c))
    (h₁ : B.condition (γ₁) (y)) (h₂ : B.condition (γ₂) (z)) :
    B.condition (γ₁ + γ₂) (fun x => y (x) + z (x)) := by
  unfold condition at h₁ h₂ ⊢
  rw [B.apply_add (hy) (hz), h₁, h₂]

/-- If `y` satisfies the Robin condition with right-hand side `γ`, then `k y` satisfies the one
with right-hand side `k γ`. -/
theorem condition_const_mul (B : Operator) {γ : ℝ} {y : ℝ → ℝ} (k : ℝ)
    (h : B.condition (γ) (y)) :
    B.condition (k * γ) (fun x => k * y (x)) := by
  unfold condition at h ⊢
  rw [apply_const_mul, h]

end Operator

end MathPhysicsTheory.BoundaryConditions.Robin

end
