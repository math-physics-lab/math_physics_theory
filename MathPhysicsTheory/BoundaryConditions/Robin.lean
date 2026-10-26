module

public import Mathlib

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Robin boundary conditions

A Robin boundary condition at a point `c` prescribes a linear combination of the value and the
derivative of `y` there:
`α y(c) + β y'(c) = 0`, with `α` and `β` not both zero.

`β = 0` gives the Dirichlet condition `y(c) = 0`, and `α = 0` the Neumann condition `y'(c) = 0`.

On an interval `[a, b]` a Robin boundary condition is a pair of such conditions, one at each
endpoint. These are the separated boundary conditions of a regular Sturm-Liouville problem.

## Main definitions

* `Robin`: the coefficients of a Robin condition at one point.
* `Robin.operator`: the boundary operator `y ↦ α y(c) + β y'(c)`.
* `RobinBC`: Robin conditions at both endpoints of an interval.
* `RobinBC.operator`: the boundary operator `y ↦ (B_a y, B_b y)`.

## Main statements

* `Robin.Holds.add`, `Robin.Holds.const_mul`, `RobinBC.Holds.add`, `RobinBC.Holds.const_mul`:
  the functions satisfying a Robin condition are closed under sums and scalar multiples.

## References

* R. L. Herman, *Introduction to Partial Differential Equations*, §4.1
  "Sturm-Liouville Operators".
-/

@[expose] public section

namespace MathPhysicsTheory.BoundaryConditions

/-- The coefficients of a Robin boundary condition `α y(c) + β y'(c) = 0`, not both zero. -/
structure Robin where
  /-- The coefficient of the value `y(c)`. -/
  α : ℝ
  /-- The coefficient of the derivative `y'(c)`. -/
  β : ℝ
  /-- The condition is not trivially satisfied. -/
  nontrivial : α ≠ 0 ∨ β ≠ 0

namespace Robin

/-- The Robin boundary operator at `c`: `B y = α y(c) + β y'(c)`. -/
noncomputable def operator (r : Robin) (c : ℝ) (y : ℝ → ℝ) : ℝ :=
  r.α * y (c) + r.β * deriv (y) (c)

/-- `y` satisfies the Robin condition `r` at `c`: `α y(c) + β y'(c) = 0`. -/
def Holds (r : Robin) (c : ℝ) (y : ℝ → ℝ) : Prop :=
  r.operator (c) (y) = 0

/-- The Robin operator is additive on functions differentiable at `c`. -/
theorem operator_add {r : Robin} {c : ℝ} {y z : ℝ → ℝ} (hy : DifferentiableAt (ℝ) (y) (c))
    (hz : DifferentiableAt (ℝ) (z) (c)) :
    r.operator (c) (fun x => y (x) + z (x)) = r.operator (c) (y) + r.operator (c) (z) := by
  simp only [operator, deriv_add (hy) (hz)]
  ring

/-- The Robin operator commutes with scalar multiplication. -/
theorem operator_const_mul (r : Robin) (c k : ℝ) (y : ℝ → ℝ) :
    r.operator (c) (fun x => k * y (x)) = k * r.operator (c) (y) := by
  simp only [operator, deriv_const_mul_field]
  ring

/-- The sum of two functions satisfying a Robin condition satisfies it too. -/
theorem Holds.add {r : Robin} {c : ℝ} {y z : ℝ → ℝ} (hy : DifferentiableAt (ℝ) (y) (c))
    (hz : DifferentiableAt (ℝ) (z) (c)) (h₁ : r.Holds (c) (y)) (h₂ : r.Holds (c) (z)) :
    r.Holds (c) (fun x => y (x) + z (x)) := by
  unfold Holds at h₁ h₂ ⊢
  rw [operator_add (hy) (hz), h₁, h₂, add_zero]

/-- A scalar multiple of a function satisfying a Robin condition satisfies it too. -/
theorem Holds.const_mul {r : Robin} {c : ℝ} {y : ℝ → ℝ} (k : ℝ) (h : r.Holds (c) (y)) :
    r.Holds (c) (fun x => k * y (x)) := by
  unfold Holds at h ⊢
  rw [operator_const_mul, h, mul_zero]

end Robin

/-- Robin boundary conditions on an interval `[a, b]`:
`α₁ y(a) + β₁ y'(a) = 0` at the left endpoint and `α₂ y(b) + β₂ y'(b) = 0` at the right. -/
structure RobinBC where
  /-- The condition at the left endpoint `a`. -/
  left : Robin
  /-- The condition at the right endpoint `b`. -/
  right : Robin

namespace RobinBC

/-- The boundary operator on `[a, b]`: `B y = (α₁ y(a) + β₁ y'(a), α₂ y(b) + β₂ y'(b))`. -/
noncomputable def operator (bc : RobinBC) (a b : ℝ) (y : ℝ → ℝ) : ℝ × ℝ :=
  (bc.left.operator (a) (y), bc.right.operator (b) (y))

/-- `y` satisfies the Robin conditions `bc` at both endpoints of `[a, b]`. -/
def Holds (bc : RobinBC) (a b : ℝ) (y : ℝ → ℝ) : Prop :=
  bc.left.Holds (a) (y) ∧ bc.right.Holds (b) (y)

/-- `y` satisfies the boundary conditions exactly when the boundary operator vanishes on it. -/
theorem holds_iff_operator_eq_zero {bc : RobinBC} {a b : ℝ} {y : ℝ → ℝ} :
    bc.Holds (a) (b) (y) ↔ bc.operator (a) (b) (y) = 0 := by
  simp [Holds, Robin.Holds, operator, Prod.ext_iff]

/-- The sum of two functions satisfying Robin boundary conditions satisfies them too. -/
theorem Holds.add {bc : RobinBC} {a b : ℝ} {y z : ℝ → ℝ} (hya : DifferentiableAt (ℝ) (y) (a))
    (hza : DifferentiableAt (ℝ) (z) (a)) (hyb : DifferentiableAt (ℝ) (y) (b))
    (hzb : DifferentiableAt (ℝ) (z) (b)) (h₁ : bc.Holds (a) (b) (y)) (h₂ : bc.Holds (a) (b) (z)) :
    bc.Holds (a) (b) (fun x => y (x) + z (x)) :=
  ⟨Robin.Holds.add (hya) (hza) (h₁.1) (h₂.1), Robin.Holds.add (hyb) (hzb) (h₁.2) (h₂.2)⟩

/-- A scalar multiple of a function satisfying Robin boundary conditions satisfies them too. -/
theorem Holds.const_mul {bc : RobinBC} {a b : ℝ} {y : ℝ → ℝ} (k : ℝ) (h : bc.Holds (a) (b) (y)) :
    bc.Holds (a) (b) (fun x => k * y (x)) :=
  ⟨Robin.Holds.const_mul (k) (h.1), Robin.Holds.const_mul (k) (h.2)⟩

end RobinBC

end MathPhysicsTheory.BoundaryConditions

end
