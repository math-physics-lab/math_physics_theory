module

public import Mathlib
public import MathPhysicsTheory.SturmLiouville.Problem

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Eigenvalues of Sturm-Liouville problems

A number `λ` is an eigenvalue of a Sturm-Liouville problem if the problem has a solution `y` that
is not identically zero on `[a, b]`, and such a `y` is an eigenfunction for `λ`.

The eigenvalues form a countable set of real numbers
`0 ≤ λ₀ < λ₁ < ⋯` with `λₙ → +∞` (`eigenvalue_sequence`).

## Example

For the Dirichlet problem `y'' = -λ y` on `[0, π]` with `y(0) = 0`, `y(π) = 0` (`dirichlet` from
`MathPhysicsTheory.SturmLiouville.Problem`), `sin` is an eigenfunction for `λ = 1`: it solves the
problem and is nonzero at `π / 2`.

```lean
example : EigenValues.IsEigenvalue (dirichlet) (1) :=
  ⟨Real.sin, ⟨by simp [dirichlet, Problem.IsSolution, Operator.apply, Robin.Operator.condition,
    Robin.Operator.apply], Real.pi / 2, ⟨by positivity, half_le_self (Real.pi_pos.le)⟩, by simp⟩⟩
```

## References

* R. L. Herman, *Introduction to Partial Differential Equations*, §4.1
  "Sturm-Liouville Operators".
-/

@[expose] public section

namespace MathPhysicsTheory.SturmLiouville.EigenValues

/-- `y` is an eigenfunction of `P` for `λ`: a solution with parameter `λ` that is not identically
zero on `[a, b]`. -/
def IsEigenfunction (P : Problem) («λ» : ℝ) (y : ℝ → ℝ) : Prop :=
  P.IsSolution («λ») (y) ∧ ∃ x ∈ Set.Icc (P.a) (P.b), y (x) ≠ 0

/-- `λ` is an eigenvalue of `P`: the problem has an eigenfunction for `λ`. -/
def IsEigenvalue (P : Problem) («λ» : ℝ) : Prop :=
  ∃ y, IsEigenfunction (P) («λ») (y)

/-- The set of eigenvalues of `P`. -/
def EigenvaluesSet (P : Problem) : Set (ℝ) :=
  {«λ» | IsEigenvalue (P) («λ»)}

/-- An eigenfunction for `λ` makes `λ` an eigenvalue. -/
theorem IsEigenfunction.isEigenvalue {P : Problem} {«λ» : ℝ} {y : ℝ → ℝ}
    (h : IsEigenfunction (P) («λ») (y)) : IsEigenvalue (P) («λ») :=
  ⟨y, h⟩

/-- The eigenvalues of `P` form a sequence `0 ≤ λ₀ < λ₁ < ⋯` with `λₙ → +∞`. -/
theorem eigenvalue_sequence (P : Problem) :
    ∃ «λ» : ℕ → ℝ, StrictMono («λ») ∧ 0 ≤ «λ» (0) ∧
      Filter.Tendsto («λ») (Filter.atTop) (Filter.atTop) ∧
      Set.range («λ») = EigenvaluesSet (P) := by
  -- TODO: prove.
  sorry

/-- The set of eigenvalues is countable. -/
theorem eigenvalues_countable (P : Problem) : (EigenvaluesSet (P)).Countable := by
  obtain ⟨«λ», -, -, -, hrange⟩ := eigenvalue_sequence (P)
  exact hrange ▸ Set.countable_range («λ»)

/-- The set of eigenvalues is infinite. -/
theorem eigenvalues_infinite (P : Problem) : (EigenvaluesSet (P)).Infinite := by
  obtain ⟨«λ», hmono, -, -, hrange⟩ := eigenvalue_sequence (P)
  exact hrange ▸ Set.infinite_range_of_injective (hmono.injective)

/-- Every eigenvalue is nonnegative. -/
theorem eigenvalues_nonneg {P : Problem} {μ : ℝ} (hμ : μ ∈ EigenvaluesSet (P)) : 0 ≤ μ := by
  obtain ⟨«λ», hmono, h0, -, hrange⟩ := eigenvalue_sequence (P)
  obtain ⟨n, rfl⟩ := hrange ▸ hμ
  exact h0.trans (hmono.monotone (Nat.zero_le (n)))

end MathPhysicsTheory.SturmLiouville.EigenValues

end
