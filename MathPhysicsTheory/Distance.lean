module

public import Mathlib

/-!
# Euclidean distance in the plane
-/

@[expose] public section

namespace MathPhysicsTheory

/-- The Euclidean distance between the points `(x₁, y₁)` and `(x₂, y₂)`. -/
noncomputable def distance (x₁ y₁ x₂ y₂ : ℝ) : ℝ :=
  Real.sqrt ((x₂ - x₁) ^ 2 + (y₂ - y₁) ^ 2)

end MathPhysicsTheory

end
