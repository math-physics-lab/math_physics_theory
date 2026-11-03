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
- an eigenfunction for the `n`-th eigenvalue `λₙ` has exactly `n` zeros in `(a, b)`
  (`eigen_functions_oscillation`).
- Steklov's theorem: a twice continuously differentiable function satisfying the boundary
  conditions is the sum of its Fourier series in the eigenfunctions, which converges absolutely
  and uniformly on `[a, b]` (`steklov_expansion`).

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
def eigen_function (P : Problem) («λₙ» : ℝ) (Xₙ : ℝ → ℝ) : Prop :=
  P.IsSolution («λₙ») (Xₙ) ∧ ∃ x ∈ Set.Icc (P.a) (P.b), Xₙ (x) ≠ 0

/-- `λ` is an eigenvalue of `P`: the problem has an eigenfunction for `λ`. -/
def eigen_value (P : Problem) («λₙ» : ℝ) : Prop :=
  ∃ Xₙ, eigen_function (P) («λₙ») (Xₙ)

/-- The set of eigenvalues of `P`. -/
def eigen_values_set (P : Problem) : Set (ℝ) :=
  {«λₙ» | eigen_value (P) («λₙ»)}

/-- An eigenfunction for `λ` makes `λ` an eigenvalue. -/
theorem eigen_value_of_eigen_function {P : Problem} {«λₙ» : ℝ} {Xₙ : ℝ → ℝ}
    (h : eigen_function (P) («λₙ») (Xₙ)) : eigen_value (P) («λₙ») :=
  ⟨Xₙ, h⟩

/-- The eigenvalues of `P` form a sequence `0 ≤ λ₀ < λ₁ < ⋯` with `λₙ → +∞`. -/
theorem eigen_values_sequence (P : Problem) :
    ∃ «λₙ» : ℕ → ℝ, StrictMono («λₙ») ∧ 0 ≤ «λₙ» (0) ∧
      Filter.Tendsto («λₙ») (Filter.atTop) (Filter.atTop) ∧
      Set.range («λₙ») = eigen_values_set (P) := by
  -- TODO: prove.
  sorry

/-- The eigenvalues of `P` in increasing order, `λ₀ < λ₁ < ⋯`. -/
noncomputable def eigen_values (P : Problem) : ℕ → ℝ :=
  Classical.choose (eigen_values_sequence (P))

/-- The eigenvalues are strictly increasing: `λ₀ < λ₁ < ⋯`. -/
lemma eigen_values_strictMono (P : Problem) : StrictMono (eigen_values (P)) :=
  (Classical.choose_spec (eigen_values_sequence (P))).1

/-- The smallest eigenvalue is nonnegative: `0 ≤ λ₀`. -/
lemma eigen_values_zero_nonneg (P : Problem) : 0 ≤ eigen_values (P) (0) :=
  (Classical.choose_spec (eigen_values_sequence (P))).2.1

/-- The eigenvalues tend to infinity: `λₙ → +∞`. -/
lemma eigen_values_tendsto (P : Problem) :
    Filter.Tendsto (eigen_values (P)) (Filter.atTop) (Filter.atTop) :=
  (Classical.choose_spec (eigen_values_sequence (P))).2.2.1

/-- The sequence `λ₀ < λ₁ < ⋯` lists every eigenvalue. -/
lemma eigen_values_range (P : Problem) : Set.range (eigen_values (P)) = eigen_values_set (P) :=
  (Classical.choose_spec (eigen_values_sequence (P))).2.2.2

/-- The set of eigenvalues is countable. -/
theorem eigen_values_countable (P : Problem) : (eigen_values_set (P)).Countable :=
  eigen_values_range (P) ▸ Set.countable_range (eigen_values (P))

/-- The set of eigenvalues is infinite. -/
theorem eigen_values_infinite (P : Problem) : (eigen_values_set (P)).Infinite :=
  eigen_values_range (P) ▸ Set.infinite_range_of_injective ((eigen_values_strictMono (P)).injective)

/-- Every eigenvalue is nonnegative. -/
theorem eigen_values_nonneg {P : Problem} {«λₙ» : ℝ} (hₙ : «λₙ» ∈ eigen_values_set (P)) :
    0 ≤ «λₙ» := by
  obtain ⟨n, rfl⟩ := eigen_values_range (P) ▸ hₙ
  exact (eigen_values_zero_nonneg (P)).trans
    ((eigen_values_strictMono (P)).monotone (Nat.zero_le (n)))

/-- Each eigenvalue `λₙ` corresponds to a single eigenfunction, up to a constant factor: two
eigenfunctions `Xₙ`, `Yₙ` for `λₙ` are proportional on `[a, b]`. -/
theorem eigen_functions_correspondence (P : Problem) {«λₙ» : ℝ} {Xₙ Yₙ : ℝ → ℝ}
    (hX : eigen_function (P) («λₙ») (Xₙ)) (hY : eigen_function (P) («λₙ») (Yₙ)) :
    ∃ c : ℝ, ∀ x ∈ Set.Icc (P.a) (P.b), Yₙ (x) = c * Xₙ (x) := by
  -- TODO: prove.
  sorry

/-- Oscillation theorem: if `λ₀ < λ₁ < ⋯` are the eigenvalues of `P` in increasing order, then an
eigenfunction `Xₙ` for `λₙ` has exactly `n` zeros in `(a, b)`. -/
theorem eigen_functions_oscillation (P : Problem) {n : ℕ} {Xₙ : ℝ → ℝ}
    (hₙ : eigen_function (P) (eigen_values (P) (n)) (Xₙ)) :
    {x | x ∈ Set.Ioo (P.a) (P.b) ∧ Xₙ (x) = 0}.encard = n := by
  -- TODO: prove.
  sorry

/-- Eigenfunctions `Xₙ`, `Xₘ` for different eigenvalues `λₙ ≠ λₘ` are orthogonal on `[a, b]`
with weight `w`: `∫ₐᵇ Xₙ(x) Xₘ(x) w(x) dx = 0`. -/
theorem eigen_functions_orthogonal (P : Problem) {«λₙ» «λₘ» : ℝ} {Xₙ Xₘ : ℝ → ℝ}
    (hₙ : eigen_function (P) («λₙ») (Xₙ)) (hₘ : eigen_function (P) («λₘ») (Xₘ))
    (hne : «λₙ» ≠ «λₘ») :
    ∫ x in (P.a)..(P.b), Xₙ (x) * Xₘ (x) * P.w (x) = 0 := by
  -- TODO: prove.
  sorry

/-- The Fourier coefficient of `f` with respect to `Xₙ`:
`cₙ = ∫ₐᵇ f(x) Xₙ(x) w(x) dx / ∫ₐᵇ Xₙ(x)² w(x) dx`. -/
noncomputable def fourier_coefficient (P : Problem) (Xₙ : ℝ → ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in (P.a)..(P.b), f (x) * Xₙ (x) * P.w (x)) / ∫ x in (P.a)..(P.b), Xₙ (x) ^ 2 * P.w (x)

/-- Steklov's theorem: let `λ₀ < λ₁ < ⋯` be the eigenvalues of `P` in increasing order and `Xₙ`
an eigenfunction for `λₙ`. If `f` is twice continuously differentiable on `[a, b]` and satisfies
the boundary conditions, then its Fourier series `∑ₙ cₙ Xₙ` converges to `f` absolutely and
uniformly on `[a, b]`. -/
theorem steklov_expansion (P : Problem) {Xₙ : ℕ → ℝ → ℝ}
    (hₙ : ∀ n, eigen_function (P) (eigen_values (P) (n)) (Xₙ (n))) {f : ℝ → ℝ}
    (hf : ContDiffOn (ℝ) (2) (f) (Set.Icc (P.a) (P.b)))
    (hBa : P.Ba.condition (0) (f)) (hBb : P.Bb.condition (0) (f)) :
    (∀ x ∈ Set.Icc (P.a) (P.b),
      Summable (fun n => |fourier_coefficient (P) (Xₙ (n)) (f) * Xₙ (n) (x)|)) ∧
    TendstoUniformlyOn
      (fun N x => ∑ n ∈ Finset.range (N), fourier_coefficient (P) (Xₙ (n)) (f) * Xₙ (n) (x))
      (f) (Filter.atTop) (Set.Icc (P.a) (P.b)) := by
  -- TODO: prove.
  sorry

end MathPhysicsTheory.SturmLiouville.EigenValues

end
