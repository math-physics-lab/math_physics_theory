import MathPhysicsTheory

/-! Tests for `MathPhysicsTheory.BoundaryConditions.Robin`. -/

open MathPhysicsTheory.BoundaryConditions

/-- `exp` satisfies `-y(c) + y'(c) = 0` at every point. -/
example (c : ℝ) : (⟨-1, 1, by simp⟩ : Robin).Holds (c) (Real.exp) := by
  simp [Robin.Holds, Robin.operator]

/-- `sin` satisfies the Dirichlet case `y(0) = y(π) = 0` on `[0, π]`. -/
example : (⟨⟨1, 0, by simp⟩, ⟨1, 0, by simp⟩⟩ : RobinBC).Holds (0) (Real.pi) (Real.sin) := by
  simp [RobinBC.Holds, Robin.Holds, Robin.operator]

/-- `cos` satisfies the Neumann case `y'(0) = y'(π) = 0` on `[0, π]`. -/
example : (⟨⟨0, 1, by simp⟩, ⟨0, 1, by simp⟩⟩ : RobinBC).Holds (0) (Real.pi) (Real.cos) := by
  simp [RobinBC.Holds, Robin.Holds, Robin.operator]
