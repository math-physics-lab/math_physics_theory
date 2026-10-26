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

namespace MathPhysicsTheory.BoundaryConditions

/-- The Robin boundary operator at `c` with coefficients `α` and `β`:
`B y = α y(c) + β y'(c)`. -/
noncomputable def robin (α β c : ℝ) (y : ℝ → ℝ) : ℝ :=
  α * y (c) + β * deriv (y) (c)

/-- The Robin operator is additive on functions differentiable at `c`. -/
theorem robin_add {α β c : ℝ} {y z : ℝ → ℝ} (hy : DifferentiableAt (ℝ) (y) (c))
    (hz : DifferentiableAt (ℝ) (z) (c)) :
    robin (α) (β) (c) (fun x => y (x) + z (x)) = robin (α) (β) (c) (y) + robin (α) (β) (c) (z) := by
  have h : deriv (fun x => y (x) + z (x)) (c) = deriv (y) (c) + deriv (z) (c) :=
    (hy.hasDerivAt.add (hz.hasDerivAt)).deriv
  simp only [robin, h]
  ring

/-- The Robin operator commutes with scalar multiplication. -/
theorem robin_const_mul (α β c k : ℝ) (y : ℝ → ℝ) :
    robin (α) (β) (c) (fun x => k * y (x)) = k * robin (α) (β) (c) (y) := by
  simp only [robin, deriv_const_mul_field]
  ring

/-- The Robin boundary condition at `c` with right-hand side `γ`: `α y(c) + β y'(c) = γ`. -/
def robinCondition (α β γ c : ℝ) (y : ℝ → ℝ) : Prop :=
  robin (α) (β) (c) (y) = γ

/-- If `y` and `z` satisfy Robin conditions with right-hand sides `γ₁` and `γ₂`, then `y + z`
satisfies the one with right-hand side `γ₁ + γ₂`. -/
theorem robinCondition_add {α β γ₁ γ₂ c : ℝ} {y z : ℝ → ℝ} (hy : DifferentiableAt (ℝ) (y) (c))
    (hz : DifferentiableAt (ℝ) (z) (c)) (h₁ : robinCondition (α) (β) (γ₁) (c) (y))
    (h₂ : robinCondition (α) (β) (γ₂) (c) (z)) :
    robinCondition (α) (β) (γ₁ + γ₂) (c) (fun x => y (x) + z (x)) := by
  unfold robinCondition at h₁ h₂ ⊢
  rw [robin_add (hy) (hz), h₁, h₂]

/-- If `y` satisfies the Robin condition with right-hand side `γ`, then `k y` satisfies the one
with right-hand side `k γ`. -/
theorem robinCondition_const_mul {α β γ c : ℝ} {y : ℝ → ℝ} (k : ℝ)
    (h : robinCondition (α) (β) (γ) (c) (y)) :
    robinCondition (α) (β) (k * γ) (c) (fun x => k * y (x)) := by
  unfold robinCondition at h ⊢
  rw [robin_const_mul, h]

end MathPhysicsTheory.BoundaryConditions

end
