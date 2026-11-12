module

public import Mathlib
public import MathPhysicsTheory.BoundaryConditions.Robin

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Dirichlet boundary conditions

The Dirichlet boundary operator at a point `c` acts on a function `y` by `B y = y(c)`. A Dirichlet
boundary condition prescribes the value of `y` at `c`: `y(c) = g(c)` for a given function `g`. It
is homogeneous when `g = 0`.

The Dirichlet operator is the Robin operator `α y(c) + β y'(c)` with `α = 1` and `β = 0`
(`Operator.toRobin`), and `apply` and `Satisfies` are defined through it. Unlike the Robin
operator, it needs no differentiability to be additive.

## References

* R. L. Herman, *Introduction to Partial Differential Equations*, §4.1
  "Sturm-Liouville Operators".
-/

@[expose] public section

namespace MathPhysicsTheory.BoundaryConditions.Dirichlet

/-- A Dirichlet boundary operator: the point `c` of `B y = y(c)`. -/
structure Operator where
  /-- The point the condition is imposed at. -/
  c : ℝ

namespace Operator

/-- The Dirichlet operator as the Robin operator with `α = 1` and `β = 0`. -/
def toRobin (B : Operator) : Robin.Operator :=
  { α := 1, β := 0, c := B.c }

@[simp]
theorem toRobin_α (B : Operator) : B.toRobin.α = 1 := rfl

@[simp]
theorem toRobin_β (B : Operator) : B.toRobin.β = 0 := rfl

@[simp]
theorem toRobin_c (B : Operator) : B.toRobin.c = B.c := rfl

/-- The Dirichlet boundary operator `B y = y(c)`, the Robin operator `1 * y(c) + 0 * y'(c)`. -/
noncomputable def apply (B : Operator) (y : ℝ → ℝ) : ℝ :=
  B.toRobin.apply (y)

/-- The Dirichlet operator evaluates at `c`: `B y = y(c)`. -/
@[simp]
theorem apply_eq (B : Operator) (y : ℝ → ℝ) : B.apply (y) = y (B.c) := by
  simp [apply, Robin.Operator.apply]

/-- The Robin operator `B.toRobin` acts as `B`. -/
@[simp]
theorem toRobin_apply (B : Operator) (y : ℝ → ℝ) : B.toRobin.apply (y) = B.apply (y) := rfl

/-- The Dirichlet operator is additive. -/
theorem apply_add (B : Operator) (y z : ℝ → ℝ) :
    B.apply (fun x => y (x) + z (x)) = B.apply (y) + B.apply (z) := by
  simp

/-- The Dirichlet operator commutes with scalar multiplication. -/
theorem apply_const_mul (B : Operator) (k : ℝ) (y : ℝ → ℝ) :
    B.apply (fun x => k * y (x)) = k * B.apply (y) :=
  Robin.Operator.apply_const_mul (B.toRobin) (k) (y)

/-- `y` satisfies the Dirichlet boundary condition with right-hand side `g`: `y(c) = g(c)`. It is
the Robin condition of `B.toRobin`. -/
def Satisfies (B : Operator) (g : ℝ → ℝ) (y : ℝ → ℝ) : Prop :=
  B.toRobin.Satisfies (g) (y)

/-- The Robin condition of `B.toRobin` is the Dirichlet condition of `B`. -/
@[simp]
theorem toRobin_satisfies_iff (B : Operator) (g : ℝ → ℝ) (y : ℝ → ℝ) :
    B.toRobin.Satisfies (g) (y) ↔ B.Satisfies (g) (y) := Iff.rfl

/-- `y` satisfies the Dirichlet condition with right-hand side `g` iff `y(c) = g(c)`. -/
theorem satisfies_iff (B : Operator) (g : ℝ → ℝ) (y : ℝ → ℝ) :
    B.Satisfies (g) (y) ↔ y (B.c) = g (B.c) := by
  change B.apply (y) = g (B.c) ↔ _
  rw [apply_eq]

/-- If `y` and `z` satisfy Dirichlet conditions with right-hand sides `g₁` and `g₂`, then
`y + z` satisfies the one with right-hand side `g₁ + g₂`. -/
theorem satisfies_add (B : Operator) {g₁ g₂ : ℝ → ℝ} {y z : ℝ → ℝ}
    (h₁ : B.Satisfies (g₁) (y)) (h₂ : B.Satisfies (g₂) (z)) :
    B.Satisfies (fun x => g₁ (x) + g₂ (x)) (fun x => y (x) + z (x)) := by
  rw [satisfies_iff] at h₁ h₂ ⊢
  simp only [h₁, h₂]

/-- If `y` satisfies the Dirichlet condition with right-hand side `g`, then `k y` satisfies the
one with right-hand side `k g`. -/
theorem satisfies_const_mul (B : Operator) {g : ℝ → ℝ} {y : ℝ → ℝ} (k : ℝ)
    (h : B.Satisfies (g) (y)) :
    B.Satisfies (fun x => k * g (x)) (fun x => k * y (x)) :=
  Robin.Operator.satisfies_const_mul (B.toRobin) (k) (h)

end Operator

end MathPhysicsTheory.BoundaryConditions.Dirichlet

end
