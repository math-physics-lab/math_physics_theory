import MathPhysicsTheory

/-! Tests for `MathPhysicsTheory.distance`. -/

open MathPhysicsTheory

/-- A 3-4-5 right triangle. -/
example : distance (0) (0) (3) (4) = 5 := by
  rw [distance, show (3  - 0) ^ 2 + (4 - 0) ^ 2 = 5 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- A point is at distance zero from itself. -/
example (x y : ℝ) : distance (x) (y) (x) (y) = 0 := by
  simp [distance]

/-- Distance is symmetric. -/
example (x₁ y₁ x₂ y₂ : ℝ) : distance (x₁) (y₁) (x₂) (y₂) = distance (x₂) (y₂) (x₁) (y₁) := by
  simp only [distance]
  ring_nf
