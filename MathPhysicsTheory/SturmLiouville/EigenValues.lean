module

public import Mathlib
public import MathPhysicsTheory.SturmLiouville.Problem

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Eigenvalues of Sturm-Liouville problems

A number `λ` is an eigenvalue of a Sturm-Liouville problem if the problem has a solution `X` that
is not identically zero on `[a, b]`, and such an `X` is an eigenfunction for `λ`.

- the eigenvalues form a countable set of real numbers
  `0 ≤ λ₀ < λ₁ < ⋯` with `λₙ → +∞` (`eigen_values_sequence`).
- eigenfunctions for different eigenvalues are orthogonal on `[a, b]` with weight `w`
  (`eigen_functions_orthogonal`).
- each eigenvalue corresponds to a single eigenfunction, up to a constant factor
  (`eigen_functions_correspondence`).

## Example

For the Dirichlet problem `y'' = -λ y` on `[0, π]` with `y(0) = 0`, `y(π) = 0` (`dirichlet` from
`MathPhysicsTheory.SturmLiouville.Problem`), `sin` is an eigenfunction for `λ = 1`: it solves the
problem and is nonzero at `π / 2`.

```lean
example : EigenValues.eigen_value (dirichlet) (1) :=
  ⟨Real.sin, ⟨⟨Real.contDiff_sin.contDiffOn, by simp [dirichlet, Operator.apply,
    Robin.Operator.condition, Robin.Operator.apply]⟩, Real.pi / 2,
    ⟨by positivity, half_le_self (Real.pi_pos.le)⟩, by simp⟩⟩
```

## References

* R. L. Herman, *Introduction to Partial Differential Equations*, §4.1
  "Sturm-Liouville Operators".
-/

@[expose] public section

namespace MathPhysicsTheory.SturmLiouville.EigenValues

/-- `X` is an eigenfunction of `P` for `λ`: a solution with parameter `λ` that is not identically
zero on `[a, b]`. -/
def eigen_function (P : Problem) («λ» : ℝ) (X : ℝ → ℝ) : Prop :=
  P.IsSolution («λ») (X) ∧ ∃ x ∈ Set.Icc (P.a) (P.b), X (x) ≠ 0

/-- `λ` is an eigenvalue of `P`: the problem has an eigenfunction for `λ`. -/
def eigen_value (P : Problem) («λ» : ℝ) : Prop :=
  ∃ X, eigen_function (P) («λ») (X)

/-- The set of eigenvalues of `P`. -/
def eigen_values_set (P : Problem) : Set (ℝ) :=
  {«λ» | eigen_value (P) («λ»)}

/-- An eigenfunction for `λ` makes `λ` an eigenvalue. -/
theorem eigen_value_of_eigen_function {P : Problem} {«λ» : ℝ} {X : ℝ → ℝ}
    (h : eigen_function (P) («λ») (X)) : eigen_value (P) («λ») :=
  ⟨X, h⟩

/-- The eigenvalues of `P` form a sequence `0 ≤ λ₀ < λ₁ < ⋯` with `λₙ → +∞`. -/
theorem eigen_values_sequence (P : Problem) :
    ∃ «λ» : ℕ → ℝ, StrictMono («λ») ∧ 0 ≤ «λ» (0) ∧
      Filter.Tendsto («λ») (Filter.atTop) (Filter.atTop) ∧
      Set.range («λ») = eigen_values_set (P) := by
  -- TODO: prove.
  sorry

/-- The set of eigenvalues is countable. -/
theorem eigen_values_countable (P : Problem) : (eigen_values_set (P)).Countable := by
  obtain ⟨«λ», -, -, -, hrange⟩ := eigen_values_sequence (P)
  exact hrange ▸ Set.countable_range («λ»)

/-- The set of eigenvalues is infinite. -/
theorem eigen_values_infinite (P : Problem) : (eigen_values_set (P)).Infinite := by
  obtain ⟨«λ», hmono, -, -, hrange⟩ := eigen_values_sequence (P)
  exact hrange ▸ Set.infinite_range_of_injective (hmono.injective)

/-- Every eigenvalue is nonnegative. -/
theorem eigen_values_nonneg {P : Problem} {«λₙ» : ℝ} (hₙ : «λₙ» ∈ eigen_values_set (P)) :
    0 ≤ «λₙ» := by
  obtain ⟨«λ», hmono, h0, -, hrange⟩ := eigen_values_sequence (P)
  obtain ⟨n, rfl⟩ := hrange ▸ hₙ
  exact h0.trans (hmono.monotone (Nat.zero_le (n)))

/-- Eigenfunctions `Xₙ`, `Xₘ` for different eigenvalues `λₙ ≠ λₘ` are orthogonal on `[a, b]`
with weight `w`: `∫ₐᵇ Xₙ(x) Xₘ(x) w(x) dx = 0`. -/
theorem eigen_functions_orthogonal (P : Problem) {«λₙ» «λₘ» : ℝ} {Xₙ Xₘ : ℝ → ℝ}
    (hₙ : eigen_function (P) («λₙ») (Xₙ)) (hₘ : eigen_function (P) («λₘ») (Xₘ))
    (hne : «λₙ» ≠ «λₘ») :
    ∫ x in (P.a)..(P.b), Xₙ (x) * Xₘ (x) * P.w (x) = 0 := by
  -- TODO: prove.
  sorry

/-- Each eigenvalue `λₙ` corresponds to a single eigenfunction, up to a constant factor: two
eigenfunctions `Xₙ`, `Yₙ` for `λₙ` are proportional on `[a, b]`. -/
theorem eigen_functions_correspondence (P : Problem) {«λₙ» : ℝ} {Xₙ Yₙ : ℝ → ℝ}
    (hX : eigen_function (P) («λₙ») (Xₙ)) (hY : eigen_function (P) («λₙ») (Yₙ)) :
    ∃ c : ℝ, ∀ x ∈ Set.Icc (P.a) (P.b), Yₙ (x) = c * Xₙ (x) := by
  -- TODO: prove.
  sorry

end MathPhysicsTheory.SturmLiouville.EigenValues

end
