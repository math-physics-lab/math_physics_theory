module

public import Mathlib
public import MathPhysicsTheory.BoundaryConditions.Robin

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Neumann boundary conditions

The Neumann boundary operator at a point `c` acts on a function `y` by `B y = y'(c)`. A Neumann
boundary condition prescribes the derivative of `y` at `c`: `y'(c) = g(c)` for a given function
`g`. It is homogeneous when `g = 0`.

The Neumann operator is the Robin operator `α y(c) + β y'(c)` with `α = 0` and `β = 1`
(`Operator.toRobin`), and `apply` and `Satisfies` are defined through it.

## References

* R. L. Herman, *Introduction to Partial Differential Equations*, §4.1
  "Sturm-Liouville Operators".
-/

@[expose] public section

namespace MathPhysicsTheory.BoundaryConditions.Neumann

/-- A Neumann boundary operator: the point `c` of `B y = y'(c)`. -/
structure Operator where
  /-- The point the condition is imposed at. -/
  c : ℝ

namespace Operator

/-- The Neumann operator as the Robin operator with `α = 0` and `β = 1`. -/
def toRobin (B : Operator) : Robin.Operator :=
  { α := 0, β := 1, c := B.c }

@[simp]
theorem toRobin_α (B : Operator) : B.toRobin.α = 0 := rfl

@[simp]
theorem toRobin_β (B : Operator) : B.toRobin.β = 1 := rfl

@[simp]
theorem toRobin_c (B : Operator) : B.toRobin.c = B.c := rfl

/-- The Neumann boundary operator `B y = y'(c)`, the Robin operator `0 * y(c) + 1 * y'(c)`. -/
noncomputable def apply (B : Operator) (y : ℝ → ℝ) : ℝ :=
  B.toRobin.apply (y)

/-- The Neumann operator differentiates at `c`: `B y = y'(c)`. -/
@[simp]
theorem apply_eq (B : Operator) (y : ℝ → ℝ) : B.apply (y) = deriv (y) (B.c) := by
  simp [apply, Robin.Operator.apply]

/-- The Robin operator `B.toRobin` acts as `B`. -/
@[simp]
theorem toRobin_apply (B : Operator) (y : ℝ → ℝ) : B.toRobin.apply (y) = B.apply (y) := rfl

/-- The Neumann operator is additive on functions differentiable at `c`. -/
theorem apply_add (B : Operator) {y z : ℝ → ℝ} (hy : DifferentiableAt (ℝ) (y) (B.c))
    (hz : DifferentiableAt (ℝ) (z) (B.c)) :
    B.apply (fun x => y (x) + z (x)) = B.apply (y) + B.apply (z) :=
  Robin.Operator.apply_add (B.toRobin) (hy) (hz)

/-- The Neumann operator commutes with scalar multiplication. -/
theorem apply_const_mul (B : Operator) (k : ℝ) (y : ℝ → ℝ) :
    B.apply (fun x => k * y (x)) = k * B.apply (y) :=
  Robin.Operator.apply_const_mul (B.toRobin) (k) (y)

/-- `y` satisfies the Neumann boundary condition with right-hand side `g`: `y'(c) = g(c)`. It is
the Robin condition of `B.toRobin`. -/
def Satisfies (B : Operator) (g : ℝ → ℝ) (y : ℝ → ℝ) : Prop :=
  B.toRobin.Satisfies (g) (y)

/-- The Robin condition of `B.toRobin` is the Neumann condition of `B`. -/
@[simp]
theorem toRobin_satisfies_iff (B : Operator) (g : ℝ → ℝ) (y : ℝ → ℝ) :
    B.toRobin.Satisfies (g) (y) ↔ B.Satisfies (g) (y) := Iff.rfl

/-- `y` satisfies the Neumann condition with right-hand side `g` iff `y'(c) = g(c)`. -/
theorem satisfies_iff (B : Operator) (g : ℝ → ℝ) (y : ℝ → ℝ) :
    B.Satisfies (g) (y) ↔ deriv (y) (B.c) = g (B.c) := by
  show B.apply (y) = g (B.c) ↔ _
  rw [apply_eq]

/-- If `y` and `z` satisfy Neumann conditions with right-hand sides `g₁` and `g₂`, then `y + z`
satisfies the one with right-hand side `g₁ + g₂`. -/
theorem satisfies_add (B : Operator) {g₁ g₂ : ℝ → ℝ} {y z : ℝ → ℝ}
    (hy : DifferentiableAt (ℝ) (y) (B.c)) (hz : DifferentiableAt (ℝ) (z) (B.c))
    (h₁ : B.Satisfies (g₁) (y)) (h₂ : B.Satisfies (g₂) (z)) :
    B.Satisfies (fun x => g₁ (x) + g₂ (x)) (fun x => y (x) + z (x)) :=
  Robin.Operator.satisfies_add (B.toRobin) (hy) (hz) (h₁) (h₂)

/-- If `y` satisfies the Neumann condition with right-hand side `g`, then `k y` satisfies the one
with right-hand side `k g`. -/
theorem satisfies_const_mul (B : Operator) {g : ℝ → ℝ} {y : ℝ → ℝ} (k : ℝ)
    (h : B.Satisfies (g) (y)) :
    B.Satisfies (fun x => k * g (x)) (fun x => k * y (x)) :=
  Robin.Operator.satisfies_const_mul (B.toRobin) (k) (h)

end Operator

end MathPhysicsTheory.BoundaryConditions.Neumann

end
