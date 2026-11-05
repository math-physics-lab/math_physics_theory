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
  `0 ≤ λ₀ < λ₁ < ⋯` with `λₙ → +∞` (`exists_eigenvalue_seq`).
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
* G. Birkhoff, G.-C. Rota, *Ordinary Differential Equations*, Ch. 10 "The Sturm-Liouville
  Systems".
* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Ch. 8.
* G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, §5.5 "Oscillation theory".
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

/-- The eigenvalues of `P` form a sequence `0 ≤ λ₀ < λ₁ < ⋯` with `λₙ → +∞`. -/
theorem exists_eigenvalue_seq (P : Problem) :
    ∃ «λₙ» : ℕ → ℝ, StrictMono («λₙ») ∧ 0 ≤ «λₙ» (0) ∧
      Filter.Tendsto («λₙ») (Filter.atTop) (Filter.atTop) ∧
      Set.range («λₙ») = eigenvalueSet (P) := by
  -- The eigenvalues are nonnegative: multiply the equation by an eigenfunction `Y` and integrate
  -- by parts (the Rayleigh quotient). The boundary terms are nonnegative because `α₁ β₁ ≤ 0` and
  -- `α₂ β₂ ≥ 0`, and `∫ (p Y'² - q Y²)` is nonnegative because `p > 0` and `q ≤ 0`. See the module
  -- note for the endpoint cases that come from `deriv` being two-sided.
  have hnonneg : eigenvalueSet (P) ⊆ Set.Ici (0) := by
    -- TODO: prove.
    sorry
  -- Only finitely many eigenvalues lie below each bound: they lie in the union of the spectra of
  -- four separated problems (each endpoint carries its own Robin condition or a Dirichlet one),
  -- together with at most two exceptional values, and by Prüfer's transformation each of these
  -- spectra is a sequence tending to `+∞`. See the module note.
  have hfin : ∀ M : ℝ, (eigenvalueSet (P) ∩ Set.Iic (M)).Finite := by
    -- TODO: prove.
    sorry
  -- There are infinitely many eigenvalues: every eigenvalue of the Dirichlet problem with the same
  -- `p`, `q` and `w` is one (extend the eigenfunction by a jump outside `[a, b]`, which makes
  -- `deriv` vanish at the endpoints), and by Prüfer's transformation the Dirichlet problem has
  -- infinitely many eigenvalues. See the module note.
  have hinf : (eigenvalueSet (P)).Infinite := by
    -- TODO: prove.
    sorry
  -- An infinite set with finitely many elements below each bound is order-isomorphic to `ℕ`; its
  -- enumeration is the required sequence.
  set S := eigenvalueSet (P)
  have hIcc : ∀ a b : S, (Set.Icc (a) (b)).Finite := fun a b =>
    ((hfin (b)).preimage (Subtype.val_injective.injOn)).subset (fun x hx => ⟨x.2, hx.2⟩)
  let _ : LocallyFiniteOrder (S) := LocallyFiniteOrder.ofFiniteIcc (hIcc)
  let _ : SuccOrder (S) := LinearLocallyFiniteOrder.succOrder (S)
  let _ : PredOrder (S) := LinearLocallyFiniteOrder.predOrder (S)
  have : NoMaxOrder (S) := ⟨fun s => by
    by_contra h
    push Not at h
    exact hinf ((hfin (s)).subset (fun x hx => ⟨hx, h ⟨x, hx⟩⟩))⟩
  obtain ⟨s₀, hs₀⟩ := hinf.nonempty
  obtain ⟨m, hm, hmin⟩ := (hfin (s₀)).exists_minimal ⟨s₀, hs₀, Set.mem_Iic.2 (le_rfl)⟩
  have hm_le : ∀ x ∈ S, m ≤ x := fun x hx => by
    by_contra hlt
    push Not at hlt
    exact absurd (hmin ⟨hx, hlt.le.trans (hm.2)⟩ (hlt.le)) (not_le.2 (hlt))
  let _ : OrderBot (S) := { bot := ⟨m, hm.1⟩, bot_le := fun x => hm_le (x) (x.2) }
  let e : S ≃o ℕ := orderIsoNatOfLinearSuccPredArch
  refine ⟨fun n => (e.symm (n) : ℝ), fun i j hij => e.symm.strictMono (hij),
    hnonneg ((e.symm (0)).2), ?_, ?_⟩
  · refine Filter.tendsto_atTop.2 (fun M => ?_)
    have hf : {n : ℕ | (e.symm (n) : ℝ) ≤ M}.Finite :=
      ((hfin (M)).preimage ((Subtype.val_injective.comp (e.symm.injective)).injOn)).subset
        (fun n hn => ⟨(e.symm (n)).2, hn⟩)
    rw [← Nat.cofinite_eq_atTop]
    filter_upwards [hf.eventually_cofinite_notMem] with n hn
    exact le_of_lt (lt_of_not_ge (hn))
  · ext x
    exact ⟨fun ⟨n, hn⟩ => hn ▸ (e.symm (n)).2, fun hx => ⟨e ⟨x, hx⟩, by simp⟩⟩

/-- The eigenvalues of `P` in increasing order, `λ₀ < λ₁ < ⋯`. -/
noncomputable def eigenvalues (P : Problem) : ℕ → ℝ :=
  Classical.choose (exists_eigenvalue_seq (P))

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
