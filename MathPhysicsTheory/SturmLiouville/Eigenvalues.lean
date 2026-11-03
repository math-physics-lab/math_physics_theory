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
  `0 ≤ λ₀ < λ₁ < ⋯` with `λₙ → +∞` (`exists_eigenvalue_seq`). This follows from three facts:
  every eigenvalue is nonnegative (`nonneg_of_mem_eigenvalueSet`), there are infinitely many
  (`eigenvalueSet_infinite`), and only finitely many lie below any bound
  (`eigenvalueSet_inter_Iic_finite`).
- eigenfunctions for different eigenvalues are orthogonal on `[a, b]` with weight `w`
  (`isEigenfunction_orthogonal`).
- each eigenvalue corresponds to a single eigenfunction, up to a constant factor
  (`isEigenfunction_proportional`).
- an eigenfunction for the `n`-th eigenvalue `λₙ` has exactly `n` zeros in `(a, b)`
  (`isEigenfunction_zeros_encard`).
- Steklov's theorem: a twice continuously differentiable function satisfying the boundary
  conditions is the sum of its Fourier series in the eigenfunctions, which converges absolutely
  and uniformly on `[a, b]` (`steklov_expansion`).

## Example

For the Dirichlet problem `y'' = -λ y` on `[0, π]` with `y(0) = 0`, `y(π) = 0` (`dirichlet` from
`MathPhysicsTheory.SturmLiouville.Problem`), `sin` is an eigenfunction for `λ = 1`: it solves the
problem and is nonzero at `π / 2`.

```lean
example : Eigenvalues.IsEigenvalue (dirichlet) (1) :=
  ⟨Real.sin, ⟨⟨Real.contDiff_sin.contDiffOn, by simp [dirichlet, Operator.apply,
    Robin.Operator.Satisfies, Robin.Operator.apply]⟩, Real.pi / 2,
    ⟨by positivity, half_le_self (Real.pi_pos.le)⟩, by simp⟩⟩
```

## References

* R. L. Herman, *Introduction to Partial Differential Equations*, §4.1
  "Sturm-Liouville Operators".
-/

@[expose] public section

namespace MathPhysicsTheory.SturmLiouville.Eigenvalues

/-- `X` is an eigenfunction of `P` for `λ`: a solution with parameter `λ` that is not identically
zero on `[a, b]`. -/
def IsEigenfunction (P : Problem) («λₙ» : ℝ) (Xₙ : ℝ → ℝ) : Prop :=
  P.IsSolution («λₙ») (Xₙ) ∧ ∃ x ∈ Set.Icc (P.a) (P.b), Xₙ (x) ≠ 0

/-- `λ` is an eigenvalue of `P`: the problem has an eigenfunction for `λ`. -/
def IsEigenvalue (P : Problem) («λₙ» : ℝ) : Prop :=
  ∃ Xₙ, IsEigenfunction (P) («λₙ») (Xₙ)

/-- The set of eigenvalues of `P`. -/
def eigenvalueSet (P : Problem) : Set (ℝ) :=
  {«λₙ» | IsEigenvalue (P) («λₙ»)}

/-- An eigenfunction for `λ` makes `λ` an eigenvalue. -/
theorem isEigenvalue_of_isEigenfunction {P : Problem} {«λₙ» : ℝ} {Xₙ : ℝ → ℝ}
    (h : IsEigenfunction (P) («λₙ») (Xₙ)) : IsEigenvalue (P) («λₙ») :=
  ⟨Xₙ, h⟩

/-- An infinite set `S` in a linear order with only finitely many elements below every bound is
the range of a strictly increasing sequence tending to `+∞`. -/
theorem exists_strictMono_tendsto_range_eq {α : Type*} [LinearOrder (α)] {S : Set (α)}
    (hS : S.Infinite) (hfin : ∀ c, (S ∩ Set.Iic (c)).Finite) :
    ∃ f : ℕ → α, StrictMono (f) ∧ Filter.Tendsto (f) (Filter.atTop) (Filter.atTop) ∧
      Set.range (f) = S := by
  -- The rank of `s ∈ S`: the number of elements of `S` below `s`.
  let g : S → ℕ := fun s => (S ∩ Set.Iio (s : α)).ncard
  have hg : StrictMono (g) := by
    intro s t hst
    refine Set.ncard_lt_ncard (?_) ((hfin (t)).subset
      (Set.inter_subset_inter_right (S) (Set.Iio_subset_Iic_self)))
    refine ⟨Set.inter_subset_inter_right (S) (Set.Iio_subset_Iio (hst.le)), fun h => ?_⟩
    exact lt_irrefl (_) ((h ⟨s.2, hst⟩).2)
  have : Infinite (S) := hS.to_subtype
  have : Infinite (Set.range (g)) := (Set.infinite_range_of_injective (hg.injective)).to_subtype
  let e : ℕ ≃o S := (Nat.Subtype.orderIsoOfNat (Set.range (g))).trans
    ((StrictMono.orderIso (g) (hg)).symm)
  let f : ℕ → α := fun n => (e (n) : α)
  have hf : StrictMono (f) := fun m n h => e.strictMono (h)
  refine ⟨f, hf, ?_, ?_⟩
  · refine Filter.tendsto_atTop_atTop.2 (fun c => ?_)
    obtain ⟨n, hn⟩ := ((hfin (c)).preimage (hf.injective.injOn)).exists_notMem
    refine ⟨n, fun m hm => ?_⟩
    have hlt : c < f (n) := lt_of_not_ge (fun h => hn ⟨(e (n)).2, h⟩)
    exact hlt.le.trans (hf.monotone (hm))
  · refine Set.Subset.antisymm (?_) (fun s hs => ?_)
    · rintro _ ⟨n, rfl⟩
      exact (e (n)).2
    · exact ⟨e.symm ⟨s, hs⟩, by simp [f]⟩

/-- Every eigenvalue is nonnegative. -/
theorem nonneg_of_mem_eigenvalueSet {P : Problem} {«λₙ» : ℝ} (hₙ : «λₙ» ∈ eigenvalueSet (P)) :
    0 ≤ «λₙ» := by
  -- TODO: prove, by multiplying `L X = -λ w X` by `X` and integrating by parts over `[a, b]`.
  sorry

/-- The set of eigenvalues is infinite. -/
theorem eigenvalueSet_infinite (P : Problem) : (eigenvalueSet (P)).Infinite := by
  -- TODO: prove.
  sorry

/-- There are only finitely many eigenvalues below any bound `c`. -/
theorem eigenvalueSet_inter_Iic_finite (P : Problem) (c : ℝ) :
    (eigenvalueSet (P) ∩ Set.Iic (c)).Finite := by
  -- TODO: prove.
  sorry

/-- The eigenvalues of `P` form a sequence `0 ≤ λ₀ < λ₁ < ⋯` with `λₙ → +∞`. -/
theorem exists_eigenvalue_seq (P : Problem) :
    ∃ «λₙ» : ℕ → ℝ, StrictMono («λₙ») ∧ 0 ≤ «λₙ» (0) ∧
      Filter.Tendsto («λₙ») (Filter.atTop) (Filter.atTop) ∧
      Set.range («λₙ») = eigenvalueSet (P) := by
  obtain ⟨f, hf, ht, hr⟩ := exists_strictMono_tendsto_range_eq (eigenvalueSet_infinite (P))
    (eigenvalueSet_inter_Iic_finite (P))
  exact ⟨f, hf, nonneg_of_mem_eigenvalueSet (hr.subset (Set.mem_range_self (0))), ht, hr⟩

/-- The eigenvalues of `P` in increasing order, `λ₀ < λ₁ < ⋯`. -/
noncomputable def eigenvalues (P : Problem) : ℕ → ℝ :=
  Classical.choose (exists_eigenvalue_seq (P))

/-- The eigenvalues are strictly increasing: `λ₀ < λ₁ < ⋯`. -/
lemma eigenvalues_strictMono (P : Problem) : StrictMono (eigenvalues (P)) :=
  (Classical.choose_spec (exists_eigenvalue_seq (P))).1

/-- The smallest eigenvalue is nonnegative: `0 ≤ λ₀`. -/
lemma eigenvalues_zero_nonneg (P : Problem) : 0 ≤ eigenvalues (P) (0) :=
  (Classical.choose_spec (exists_eigenvalue_seq (P))).2.1

/-- The eigenvalues tend to infinity: `λₙ → +∞`. -/
lemma eigenvalues_tendsto_atTop (P : Problem) :
    Filter.Tendsto (eigenvalues (P)) (Filter.atTop) (Filter.atTop) :=
  (Classical.choose_spec (exists_eigenvalue_seq (P))).2.2.1

/-- The sequence `λ₀ < λ₁ < ⋯` lists every eigenvalue. -/
lemma range_eigenvalues (P : Problem) : Set.range (eigenvalues (P)) = eigenvalueSet (P) :=
  (Classical.choose_spec (exists_eigenvalue_seq (P))).2.2.2

/-- The set of eigenvalues is countable. -/
theorem eigenvalueSet_countable (P : Problem) : (eigenvalueSet (P)).Countable :=
  range_eigenvalues (P) ▸ Set.countable_range (eigenvalues (P))

/-- Each eigenvalue `λₙ` corresponds to a single eigenfunction, up to a constant factor: two
eigenfunctions `Xₙ`, `Yₙ` for `λₙ` are proportional on `[a, b]`. -/
theorem isEigenfunction_proportional (P : Problem) {«λₙ» : ℝ} {Xₙ Yₙ : ℝ → ℝ}
    (hX : IsEigenfunction (P) («λₙ») (Xₙ)) (hY : IsEigenfunction (P) («λₙ») (Yₙ)) :
    ∃ c : ℝ, ∀ x ∈ Set.Icc (P.a) (P.b), Yₙ (x) = c * Xₙ (x) := by
  -- TODO: prove.
  sorry

/-- Oscillation theorem: if `λ₀ < λ₁ < ⋯` are the eigenvalues of `P` in increasing order, then an
eigenfunction `Xₙ` for `λₙ` has exactly `n` zeros in `(a, b)`. -/
theorem isEigenfunction_zeros_encard (P : Problem) {n : ℕ} {Xₙ : ℝ → ℝ}
    (hₙ : IsEigenfunction (P) (eigenvalues (P) (n)) (Xₙ)) :
    {x | x ∈ Set.Ioo (P.a) (P.b) ∧ Xₙ (x) = 0}.encard = n := by
  -- TODO: prove.
  sorry

/-- Eigenfunctions `Xₙ`, `Xₘ` for different eigenvalues `λₙ ≠ λₘ` are orthogonal on `[a, b]`
with weight `w`: `∫ₐᵇ Xₙ(x) Xₘ(x) w(x) dx = 0`. -/
theorem isEigenfunction_orthogonal (P : Problem) {«λₙ» «λₘ» : ℝ} {Xₙ Xₘ : ℝ → ℝ}
    (hₙ : IsEigenfunction (P) («λₙ») (Xₙ)) (hₘ : IsEigenfunction (P) («λₘ») (Xₘ))
    (hne : «λₙ» ≠ «λₘ») :
    ∫ x in (P.a)..(P.b), Xₙ (x) * Xₘ (x) * P.w (x) = 0 := by
  -- TODO: prove.
  sorry

/-- The Fourier coefficient of `f` with respect to `Xₙ`:
`cₙ = ∫ₐᵇ f(x) Xₙ(x) w(x) dx / ∫ₐᵇ Xₙ(x)² w(x) dx`. -/
noncomputable def fourierCoeff (P : Problem) (Xₙ : ℝ → ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in (P.a)..(P.b), f (x) * Xₙ (x) * P.w (x)) / ∫ x in (P.a)..(P.b), Xₙ (x) ^ 2 * P.w (x)

/-- Steklov's theorem: let `λ₀ < λ₁ < ⋯` be the eigenvalues of `P` in increasing order and `Xₙ`
an eigenfunction for `λₙ`. If `f` is twice continuously differentiable on `[a, b]` and satisfies
the boundary conditions, then its Fourier series `∑ₙ cₙ Xₙ` converges to `f` absolutely and
uniformly on `[a, b]`. -/
theorem steklov_expansion (P : Problem) {Xₙ : ℕ → ℝ → ℝ}
    (hₙ : ∀ n, IsEigenfunction (P) (eigenvalues (P) (n)) (Xₙ (n))) {f : ℝ → ℝ}
    (hf : ContDiffOn (ℝ) (2) (f) (Set.Icc (P.a) (P.b)))
    (hBa : P.Ba.Satisfies (0) (f)) (hBb : P.Bb.Satisfies (0) (f)) :
    (∀ x ∈ Set.Icc (P.a) (P.b),
      Summable (fun n => |fourierCoeff (P) (Xₙ (n)) (f) * Xₙ (n) (x)|)) ∧
    TendstoUniformlyOn
      (fun N x => ∑ n ∈ Finset.range (N), fourierCoeff (P) (Xₙ (n)) (f) * Xₙ (n) (x))
      (f) (Filter.atTop) (Set.Icc (P.a) (P.b)) := by
  -- TODO: prove.
  sorry

end MathPhysicsTheory.SturmLiouville.Eigenvalues

end
