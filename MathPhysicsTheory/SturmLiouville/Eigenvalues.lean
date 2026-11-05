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

section ExistsEigenvalueSeq

/-! ### Endpoint analysis, Green's identity and the Rayleigh quotient -/

open Set Filter Topology MeasureTheory

/-- `Y` solves `(p Y')' + q Y = -μ w Y` on `[a, b]`, with `Y'` its derivative within `[a, b]`. -/
private def Honest (P : Problem) (μ : ℝ) (Y Y' : ℝ → ℝ) : Prop :=
  (∀ x ∈ Icc (P.a) (P.b), HasDerivWithinAt (Y) (Y' (x)) (Icc (P.a) (P.b)) (x)) ∧
    ContinuousOn (Y') (Icc (P.a) (P.b)) ∧
    ∀ x ∈ Icc (P.a) (P.b), HasDerivWithinAt (fun y => P.L.p (y) * Y' (y))
      (-(μ * P.w (x) + P.L.q (x)) * Y (x)) (Icc (P.a) (P.b)) (x)

private lemma Honest.continuousOn {P : Problem} {μ : ℝ} {Y Y' : ℝ → ℝ}
    (h : Honest (P) (μ) (Y) (Y')) :
    ContinuousOn (Y) (Icc (P.a) (P.b)) :=
  fun x hx => (h.1 (x) (hx)).continuousWithinAt

private lemma Honest.const_mul {P : Problem} {μ : ℝ} {Y Y' : ℝ → ℝ} (h : Honest (P) (μ) (Y) (Y'))
    (c : ℝ) : Honest (P) (μ) (fun x => c * Y (x)) (fun x => c * Y' (x)) := by
  refine ⟨fun x hx => (h.1 (x) (hx)).const_mul (c), continuousOn_const.mul (h.2.1),
    fun x hx => ?_⟩
  have := (h.2.2 (x) (hx)).const_mul (c)
  convert this using 1
  · funext y
    ring
  · ring

/-- A continuous function on `[a, b]` is interval integrable. -/
private lemma intervalIntegrable_of_continuousOn {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn (f) (Icc (a) (b))) : IntervalIntegrable (f) (volume) (a) (b) :=
  ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le (hab)])

/-- Two functions continuous within `[a, b]` at `c ∈ [a, b]` that agree on `(a, b)` agree at `c`. -/
private lemma eq_of_eqOn_Ioo {a b c : ℝ} (hab : a < b) (hc : c ∈ Icc (a) (b)) {f g : ℝ → ℝ}
    (hf : ContinuousWithinAt (f) (Icc (a) (b)) (c)) (hg : ContinuousWithinAt (g) (Icc (a) (b)) (c))
    (h : EqOn (f) (g) (Ioo (a) (b))) : f (c) = g (c) := by
  have hne : (𝓝[Ioo (a) (b)] c).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rwa [closure_Ioo (hab.ne)])
  have hf' := hf.tendsto.mono_left (nhdsWithin_mono (c) (Ioo_subset_Icc_self))
  have hg' := hg.tendsto.mono_left (nhdsWithin_mono (c) (Ioo_subset_Icc_self))
  exact tendsto_nhds_unique (hf'.congr' (eventually_nhdsWithin_of_forall (h))) (hg')

/-- An eigenfunction solves the equation on `[a, b]` with one-sided derivatives at the endpoints. -/
private lemma honest_of_isSolution {P : Problem} {μ : ℝ} {X : ℝ → ℝ}
    (hX : P.IsSolution (μ) (X)) : Honest (P) (μ) (X) (derivWithin (X) (Icc (P.a) (P.b))) := by
  have hab := P.a_lt_b
  have hU : UniqueDiffOn (ℝ) (Icc (P.a) (P.b)) := uniqueDiffOn_Icc (hab)
  obtain ⟨hC2, hode, -, -⟩ := hX
  have hdiff : DifferentiableOn (ℝ) (X) (Icc (P.a) (P.b)) := hC2.differentiableOn (by norm_num)
  have hC1 : ContDiffOn (ℝ) (1) (derivWithin (X) (Icc (P.a) (P.b))) (Icc (P.a) (P.b)) :=
    hC2.derivWithin (hU) (by norm_num)
  have hg : ContDiffOn (ℝ) (1) (fun y => P.L.p (y) * derivWithin (X) (Icc (P.a) (P.b)) (y))
      (Icc (P.a) (P.b)) := P.assumptions.p_contDiffOn.mul (hC1)
  have hgd := hg.differentiableOn (by norm_num)
  have hg' : ContinuousOn (derivWithin (fun y => P.L.p (y) * derivWithin (X) (Icc (P.a) (P.b))
      (y)) (Icc (P.a) (P.b))) (Icc (P.a) (P.b)) :=
    (hg.derivWithin (hU) (m := 0) (by norm_num)).continuousOn
  have hrhs : ContinuousOn (fun x => -(μ * P.w (x) + P.L.q (x)) * X (x)) (Icc (P.a) (P.b)) :=
    ((continuousOn_const.mul (P.assumptions.w_continuousOn)).add
      (P.assumptions.q_continuousOn)).neg.mul (hdiff.continuousOn)
  have hin : EqOn (derivWithin (fun y => P.L.p (y) * derivWithin (X) (Icc (P.a) (P.b)) (y))
      (Icc (P.a) (P.b))) (fun x => -(μ * P.w (x) + P.L.q (x)) * X (x)) (Ioo (P.a) (P.b)) := by
    intro x hx
    have heq : (fun y => P.L.p (y) * deriv (X) (y)) =ᶠ[𝓝 (x)]
        fun y => P.L.p (y) * derivWithin (X) (Icc (P.a) (P.b)) (y) := by
      filter_upwards [Ioo_mem_nhds (hx.1) (hx.2)] with y hy
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds (hy.1) (hy.2))]
    have h := hode (x) (Ioo_subset_Icc_self (hx))
    simp only [Operator.apply] at h
    simp only
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds (hx.1) (hx.2)), ← heq.deriv_eq]
    linarith
  refine ⟨fun x hx => (hdiff (x) (hx)).hasDerivWithinAt, hC1.continuousOn, fun x hx => ?_⟩
  have hx' : derivWithin (fun y => P.L.p (y) * derivWithin (X) (Icc (P.a) (P.b)) (y))
      (Icc (P.a) (P.b)) (x) = -(μ * P.w (x) + P.L.q (x)) * X (x) :=
    eq_of_eqOn_Ioo (hab) (hx) (hg' (x) (hx)) (hrhs (x) (hx)) (hin)
  rw [← hx']
  exact (hgd (x) (hx)).hasDerivWithinAt

/-- The boundary condition at an endpoint `c` of an eigenfunction, in terms of the derivative
within `[a, b]`: the Robin condition holds, or `X(c) = 0`, or `q(c) + μ w(c) = 0`. -/
private lemma endpoint {P : Problem} {μ : ℝ} {X : ℝ → ℝ} (hX : P.IsSolution (μ) (X)) {c α β : ℝ}
    (hc : c ∈ Icc (P.a) (P.b)) (hBC : α * X (c) + β * deriv (X) (c) = 0) :
    α * X (c) + β * derivWithin (X) (Icc (P.a) (P.b)) (c) = 0 ∨ X (c) = 0 ∨
      P.L.q (c) + μ * P.w (c) = 0 := by
  have hab := P.a_lt_b
  have hH := honest_of_isSolution (hX)
  by_cases hd : DifferentiableAt (ℝ) (X) (c)
  · left
    rwa [hd.derivWithin (uniqueDiffOn_Icc (hab) (c) (hc))]
  rw [deriv_zero_of_not_differentiableAt (hd), mul_zero, add_zero] at hBC
  by_cases hα : α = 0
  swap
  · exact Or.inr (Or.inl ((mul_eq_zero.1 (hBC)).resolve_left (hα)))
  subst hα
  have hode := hX.2.1 (c) (hc)
  simp only [Operator.apply] at hode
  by_cases hh : DifferentiableAt (ℝ) (fun y => P.L.p (y) * deriv (X) (y)) (c)
  · left
    have hcont : ContinuousWithinAt (fun y => P.L.p (y) * deriv (X) (y)) (Icc (P.a) (P.b)) (c) :=
      hh.continuousAt.continuousWithinAt
    have h0 := eq_of_eqOn_Ioo (hab) (hc) (hcont) ((hH.2.2 (c) (hc)).continuousWithinAt)
      (fun y hy => by
        rw [derivWithin_of_mem_nhds (Icc_mem_nhds (hy.1) (hy.2))])
    simp only [deriv_zero_of_not_differentiableAt (hd), mul_zero] at h0
    have hpc := P.assumptions.p_pos (c) (hc)
    have : derivWithin (X) (Icc (P.a) (P.b)) (c) = 0 :=
      (mul_eq_zero.1 (h0.symm)).resolve_left (hpc.ne')
    simp [this]
  · right
    rw [deriv_zero_of_not_differentiableAt (hh)] at hode
    have : (P.L.q (c) + μ * P.w (c)) * X (c) = 0 := by linarith
    rcases mul_eq_zero.1 (this) with h1 | h1
    · exact Or.inr (h1)
    · exact Or.inl (h1)

/-- The data of an eigenfunction: it solves the equation on `[a, b]`, satisfies at each endpoint
the Robin condition, a Dirichlet condition, or `q + μ w = 0`, and is nonzero somewhere. -/
private lemma eigenfunction_data {P : Problem} {μ : ℝ} {X : ℝ → ℝ}
    (hX : IsEigenfunction (P) (μ) (X)) :
    Honest (P) (μ) (X) (derivWithin (X) (Icc (P.a) (P.b))) ∧
      (P.Ba.α * X (P.a) + P.Ba.β * derivWithin (X) (Icc (P.a) (P.b)) (P.a) = 0 ∨ X (P.a) = 0 ∨
        P.L.q (P.a) + μ * P.w (P.a) = 0) ∧
      (P.Bb.α * X (P.b) + P.Bb.β * derivWithin (X) (Icc (P.a) (P.b)) (P.b) = 0 ∨ X (P.b) = 0 ∨
        P.L.q (P.b) + μ * P.w (P.b) = 0) ∧
      ∃ x ∈ Icc (P.a) (P.b), X (x) ≠ 0 := by
  obtain ⟨hS, hne⟩ := hX
  have hab := P.a_lt_b
  have hBa := hS.2.2.1
  have hBb := hS.2.2.2
  simp only [BoundaryConditions.Robin.Operator.Satisfies, BoundaryConditions.Robin.Operator.apply,
    Pi.zero_apply, P.assumptions.Ba_c, P.assumptions.Bb_c] at hBa hBb
  exact ⟨honest_of_isSolution (hS), endpoint (hS) (left_mem_Icc.2 (hab.le)) (hBa),
    endpoint (hS) (right_mem_Icc.2 (hab.le)) (hBb), hne⟩

/-- Green's identity: `∫ₐᵇ ((p Y')' Z + p Y' Z') = [p Y' Z]ₐᵇ`. -/
private lemma green {P : Problem} {μ : ℝ} {Y Y' Z Z' : ℝ → ℝ} (hY : Honest (P) (μ) (Y) (Y'))
    (hZ : ∀ x ∈ Icc (P.a) (P.b), HasDerivWithinAt (Z) (Z' (x)) (Icc (P.a) (P.b)) (x))
    (hZ' : ContinuousOn (Z') (Icc (P.a) (P.b))) :
    ∫ x in (P.a)..(P.b),
        (-(μ * P.w (x) + P.L.q (x)) * Y (x) * Z (x) + P.L.p (x) * Y' (x) * Z' (x)) =
      P.L.p (P.b) * Y' (P.b) * Z (P.b) - P.L.p (P.a) * Y' (P.a) * Z (P.a) := by
  have hab := P.a_lt_b.le
  have hu : uIcc (P.a) (P.b) = Icc (P.a) (P.b) := uIcc_of_le (hab)
  have hYc := hY.continuousOn
  have h1 : ContinuousOn (fun x => -(μ * P.w (x) + P.L.q (x)) * Y (x)) (Icc (P.a) (P.b)) :=
    ((continuousOn_const.mul (P.assumptions.w_continuousOn)).add
      (P.assumptions.q_continuousOn)).neg.mul (hYc)
  have := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (u := fun y => P.L.p (y) * Y' (y)) (v := Z)
    (u' := fun x => -(μ * P.w (x) + P.L.q (x)) * Y (x)) (v' := Z')
    (by rw [hu]; exact hY.2.2) (by rw [hu]; exact hZ)
    (intervalIntegrable_of_continuousOn (hab) (h1)) (intervalIntegrable_of_continuousOn (hab) (hZ'))
  simpa only using this

/-- At `a`, the Robin condition with `α β ≤ 0`, or a Dirichlet condition, gives `y' y ≥ 0`. -/
private lemma boundary_nonneg {α β y y' : ℝ} (hne : α ≠ 0 ∨ β ≠ 0) (hαβ : α * β ≤ 0)
    (h : α * y + β * y' = 0 ∨ y = 0) : 0 ≤ y' * y := by
  rcases h with h | h
  · by_cases hβ : β = 0
    · have hα : α ≠ 0 := hne.resolve_right (not_not.2 (hβ))
      subst hβ
      have : y = 0 := by
        have : α * y = 0 := by linarith
        exact (mul_eq_zero.1 (this)).resolve_left (hα)
      simp [this]
    · have key : β ^ 2 * (y' * y) = -(α * β) * y ^ 2 := by
        have hb : β * y' = -(α * y) := by linarith
        calc β ^ 2 * (y' * y) = (β * y') * (β * y) := by ring
          _ = -(α * y) * (β * y) := by rw [hb]
          _ = -(α * β) * y ^ 2 := by ring
      have hb : 0 < β ^ 2 := by positivity
      have : 0 ≤ β ^ 2 * (y' * y) := by
        rw [key]
        exact mul_nonneg (by linarith) (sq_nonneg (y))
      exact (mul_nonneg_iff_of_pos_left (hb)).1 (this)
  · simp [h]

/-- The Wronskian `y' z - y z'` vanishes when `y` and `z` satisfy the same Robin condition. -/
private lemma wronskian_eq_zero {α β y y' z z' : ℝ} (hne : α ≠ 0 ∨ β ≠ 0)
    (hy : α * y + β * y' = 0) (hz : α * z + β * z' = 0) : y' * z - y * z' = 0 := by
  rcases hne with hα | hβ
  · have : α * (y' * z - y * z') = 0 := by linear_combination y' * hz - z' * hy
    exact (mul_eq_zero.1 (this)).resolve_left (hα)
  · have : β * (y' * z - y * z') = 0 := by linear_combination z * hy - y * hz
    exact (mul_eq_zero.1 (this)).resolve_left (hβ)

/-- The Rayleigh quotient: `∫ p Y'² ≤ μ ∫ w Y²` when `Y` satisfies, at each endpoint, the Robin
condition or a Dirichlet condition. -/
private lemma rayleigh {P : Problem} {μ : ℝ} {Y Y' : ℝ → ℝ} (hY : Honest (P) (μ) (Y) (Y'))
    (ha : P.Ba.α * Y (P.a) + P.Ba.β * Y' (P.a) = 0 ∨ Y (P.a) = 0)
    (hb : P.Bb.α * Y (P.b) + P.Bb.β * Y' (P.b) = 0 ∨ Y (P.b) = 0) :
    ∫ x in (P.a)..(P.b), P.L.p (x) * Y' (x) ^ 2 ≤ μ * ∫ x in (P.a)..(P.b), P.w (x) * Y (x) ^ 2 := by
  have hab := P.a_lt_b.le
  have hYc := hY.continuousOn
  have hY'c := hY.2.1
  have hG := green (hY) (hY.1) (hY'c)
  have hpa := P.assumptions.p_pos (P.a) (left_mem_Icc.2 (hab))
  have hpb := P.assumptions.p_pos (P.b) (right_mem_Icc.2 (hab))
  have hA : 0 ≤ Y' (P.a) * Y (P.a) :=
    boundary_nonneg (P.assumptions.Ba_ne) (P.assumptions.Ba_mul_nonpos) (ha)
  have hB : Y' (P.b) * Y (P.b) ≤ 0 := by
    have := boundary_nonneg (α := P.Bb.α) (β := -P.Bb.β) (y := Y (P.b)) (y' := -Y' (P.b))
      (by rcases P.assumptions.Bb_ne with h | h
          · exact Or.inl (h)
          · exact Or.inr (neg_ne_zero.2 (h)))
      (by nlinarith [P.assumptions.Bb_mul_nonneg])
      (by rcases hb with h | h
          · exact Or.inl (by linarith)
          · exact Or.inr (h))
    linarith
  have hw := P.assumptions.w_continuousOn
  have hq := P.assumptions.q_continuousOn
  have hp : ContinuousOn (P.L.p) (Icc (P.a) (P.b)) := P.assumptions.p_contDiffOn.continuousOn
  have i1 : IntervalIntegrable (fun x => -(μ * P.w (x) + P.L.q (x)) * Y (x) * Y (x) +
      P.L.p (x) * Y' (x) * Y' (x)) (volume) (P.a) (P.b) :=
    intervalIntegrable_of_continuousOn (hab) (((((continuousOn_const.mul (hw)).add (hq)).neg.mul
      (hYc)).mul (hYc)).add (((hp.mul (hY'c)).mul (hY'c))))
  have i2 : IntervalIntegrable (fun x => μ * (P.w (x) * Y (x) ^ 2)) (volume) (P.a) (P.b) :=
    intervalIntegrable_of_continuousOn (hab) (continuousOn_const.mul ((hw.mul ((hYc.pow (2))))))
  have i3 : IntervalIntegrable (fun x => P.L.q (x) * Y (x) ^ 2) (volume) (P.a) (P.b) :=
    intervalIntegrable_of_continuousOn (hab) (hq.mul (hYc.pow (2)))
  have e : (fun x => P.L.p (x) * Y' (x) ^ 2) = fun x =>
      (-(μ * P.w (x) + P.L.q (x)) * Y (x) * Y (x) + P.L.p (x) * Y' (x) * Y' (x)) +
        μ * (P.w (x) * Y (x) ^ 2) + P.L.q (x) * Y (x) ^ 2 := by
    funext x
    ring
  rw [e, intervalIntegral.integral_add ((i1.add (i2))) (i3),
    intervalIntegral.integral_add (i1) (i2), hG, intervalIntegral.integral_const_mul]
  have hq0 : ∫ x in (P.a)..(P.b), P.L.q (x) * Y (x) ^ 2 ≤ 0 := by
    have := intervalIntegral.integral_nonneg (hab) (μ := volume)
      (f := fun x => -(P.L.q (x) * Y (x) ^ 2))
      (fun x hx => by
        have := P.assumptions.q_nonpos (x) (hx)
        nlinarith [sq_nonneg (Y (x))])
    rw [intervalIntegral.integral_neg] at this
    linarith
  nlinarith

/-- The integral of a continuous nonnegative function on `[a, b]` that is nonzero at some point is
positive. -/
private lemma integral_pos_of_ne_zero {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn (f) (Icc (a) (b))) (h0 : ∀ x ∈ Icc (a) (b), 0 ≤ f (x)) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc (a) (b)) (hne : f (x₀) ≠ 0) : 0 < ∫ x in (a)..(b), f (x) := by
  -- a point of `(a, b)` where `f ≠ 0`
  have hev : ∀ᶠ x in 𝓝[Icc (a) (b)] x₀, f (x) ≠ 0 :=
    (hf (x₀) (hx₀)).eventually (isOpen_ne.mem_nhds (hne))
  have hNe : (𝓝[Ioo (a) (b)] x₀).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rwa [closure_Ioo (hab.ne)])
  obtain ⟨x₁, hx₁f, hx₁⟩ :=
    ((hev.filter_mono (nhdsWithin_mono (x₀) (Ioo_subset_Icc_self))).and
      (self_mem_nhdsWithin)).exists
  have hU : IsOpen (Ioo (a) (b) ∩ f ⁻¹' {0}ᶜ) :=
    (hf.mono (Ioo_subset_Icc_self)).isOpen_inter_preimage (isOpen_Ioo) (isOpen_compl_singleton)
  have hfi := intervalIntegrable_of_continuousOn (hab.le) (hf)
  have hnn : 0 ≤ᵐ[volume.restrict (uIoc (a) (b))] f := by
    rw [uIoc_of_le (hab.le)]
    exact (ae_restrict_mem (measurableSet_Ioc)).mono
      (fun x hx => h0 (x) (Ioc_subset_Icc_self (hx)))
  refine (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' (hnn) (hfi)).2 ⟨hab, ?_⟩
  refine lt_of_lt_of_le (hU.measure_pos (volume) ⟨x₁, hx₁, hx₁f⟩) (measure_mono (?_))
  intro x hx
  exact ⟨hx.2, Ioo_subset_Ioc_self (hx.1)⟩

/-- The eigenvalues of `P` are nonnegative. -/
private lemma eigenvalue_nonneg {P : Problem} {μ : ℝ} (hμ : IsEigenvalue (P) (μ)) : 0 ≤ μ := by
  obtain ⟨X, hX⟩ := hμ
  obtain ⟨hH, ha, hb, x₀, hx₀, hne⟩ := eigenfunction_data (hX)
  have hab := P.a_lt_b
  -- the exceptional cases `q(c) + μ w(c) = 0`
  have hexc : ∀ c ∈ Icc (P.a) (P.b), P.L.q (c) + μ * P.w (c) = 0 → 0 ≤ μ := fun c hc h => by
    have hw := P.assumptions.w_pos (c) (hc)
    have hq := P.assumptions.q_nonpos (c) (hc)
    nlinarith
  rcases or_assoc.2 (ha) with ha | ha
  swap
  · exact hexc (P.a) (left_mem_Icc.2 (hab.le)) (ha)
  rcases or_assoc.2 (hb) with hb | hb
  swap
  · exact hexc (P.b) (right_mem_Icc.2 (hab.le)) (hb)
  have hR := rayleigh (hH) (ha) (hb)
  have hpos : 0 < ∫ x in (P.a)..(P.b), P.w (x) * X (x) ^ 2 :=
    integral_pos_of_ne_zero (hab) (P.assumptions.w_continuousOn.mul (hH.continuousOn.pow (2)))
      (fun x hx => mul_nonneg ((P.assumptions.w_pos (x) (hx)).le) (sq_nonneg (_))) (hx₀)
      (mul_ne_zero ((P.assumptions.w_pos (x₀) (hx₀)).ne') (pow_ne_zero (2) (hne)))
  have hp0 : 0 ≤ ∫ x in (P.a)..(P.b), P.L.p (x) * derivWithin (X) (Icc (P.a) (P.b)) (x) ^ 2 :=
    intervalIntegral.integral_nonneg (hab.le)
      (fun x hx => mul_nonneg ((P.assumptions.p_pos (x) (hx)).le) (sq_nonneg (_)))
  by_contra hneg
  push Not at hneg
  nlinarith

/-! ### Finitely many eigenvalues below each bound -/

/-- Eigenfunctions for different eigenvalues, with vanishing Wronskians at the endpoints, are
orthogonal with weight `w`. -/
private lemma orthogonal {P : Problem} {μ ν : ℝ} {Y Y' Z Z' : ℝ → ℝ} (hY : Honest (P) (μ) (Y) (Y'))
    (hZ : Honest (P) (ν) (Z) (Z')) (hne : μ ≠ ν)
    (ha : Y' (P.a) * Z (P.a) - Y (P.a) * Z' (P.a) = 0)
    (hb : Y' (P.b) * Z (P.b) - Y (P.b) * Z' (P.b) = 0) :
    ∫ x in (P.a)..(P.b), P.w (x) * (Y (x) * Z (x)) = 0 := by
  have hab := P.a_lt_b.le
  have h1 := green (hY) (hZ.1) (hZ.2.1)
  have h2 := green (hZ) (hY.1) (hY.2.1)
  have hw := P.assumptions.w_continuousOn
  have hq := P.assumptions.q_continuousOn
  have hp : ContinuousOn (P.L.p) (Icc (P.a) (P.b)) := P.assumptions.p_contDiffOn.continuousOn
  have hYc := hY.continuousOn
  have hZc := hZ.continuousOn
  have i1 : IntervalIntegrable (fun x => -(μ * P.w (x) + P.L.q (x)) * Y (x) * Z (x) +
      P.L.p (x) * Y' (x) * Z' (x)) (volume) (P.a) (P.b) :=
    intervalIntegrable_of_continuousOn (hab) (((((continuousOn_const.mul (hw)).add (hq)).neg.mul
      (hYc)).mul (hZc)).add (((hp.mul (hY.2.1)).mul (hZ.2.1))))
  have i2 : IntervalIntegrable (fun x => -(ν * P.w (x) + P.L.q (x)) * Z (x) * Y (x) +
      P.L.p (x) * Z' (x) * Y' (x)) (volume) (P.a) (P.b) :=
    intervalIntegrable_of_continuousOn (hab) (((((continuousOn_const.mul (hw)).add (hq)).neg.mul
      (hZc)).mul (hYc)).add (((hp.mul (hZ.2.1)).mul (hY.2.1))))
  have hsub := intervalIntegral.integral_sub (i1) (i2)
  rw [h1, h2] at hsub
  have e : (fun x => (-(μ * P.w (x) + P.L.q (x)) * Y (x) * Z (x) + P.L.p (x) * Y' (x) * Z' (x)) -
      (-(ν * P.w (x) + P.L.q (x)) * Z (x) * Y (x) + P.L.p (x) * Z' (x) * Y' (x))) =
      fun x => (ν - μ) * (P.w (x) * (Y (x) * Z (x))) := by
    funext x
    ring
  rw [e, intervalIntegral.integral_const_mul] at hsub
  have hzero : (ν - μ) * ∫ x in (P.a)..(P.b), P.w (x) * (Y (x) * Z (x)) = 0 := by
    rw [hsub]
    linear_combination P.L.p (P.b) * hb - P.L.p (P.a) * ha
  exact (mul_eq_zero.1 (hzero)).resolve_left (sub_ne_zero.2 (hne.symm))

/-- A Hölder-type estimate: `|Z x - Z y| ≤ t |x - y| / 2 + (∫ Z'²) / (2 t)`. -/
private lemma abs_sub_le_of_integral_sq {a b : ℝ} (hab : a < b) {Z Z' : ℝ → ℝ}
    (hZ : ∀ x ∈ Icc (a) (b), HasDerivWithinAt (Z) (Z' (x)) (Icc (a) (b)) (x))
    (hZ' : ContinuousOn (Z') (Icc (a) (b))) {C : ℝ} (hC : ∫ x in (a)..(b), Z' (x) ^ 2 ≤ C)
    {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ Icc (a) (b), ∀ y ∈ Icc (a) (b), |Z (x) - Z (y)| ≤ t * |x - y| / 2 + C / (2 * t) := by
  have key : ∀ x ∈ Icc (a) (b), ∀ y ∈ Icc (a) (b), y ≤ x →
      |Z (x) - Z (y)| ≤ t * |x - y| / 2 + C / (2 * t) := by
    intro x hx y hy hyx
    have hsub : Icc (y) (x) ⊆ Icc (a) (b) := Icc_subset_Icc (hy.1) (hx.2)
    have hZc : ContinuousOn (Z) (Icc (a) (b)) := fun x hx => (hZ (x) (hx)).continuousWithinAt
    have hint : IntervalIntegrable (Z') (volume) (y) (x) :=
      intervalIntegrable_of_continuousOn (hyx) (hZ'.mono (hsub))
    have hftc : ∫ s in (y)..(x), Z' (s) = Z (x) - Z (y) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (hyx) (hZc.mono (hsub))
        (fun s hs => (hZ (s) (hsub (Ioo_subset_Icc_self (hs)))).hasDerivAt
          (Icc_mem_nhds (lt_of_le_of_lt (hy.1) (hs.1)) (lt_of_lt_of_le (hs.2) (hx.2)))) (hint)
    have hsq : IntervalIntegrable (fun s => Z' (s) ^ 2) (volume) (y) (x) :=
      intervalIntegrable_of_continuousOn (hyx) ((hZ'.pow (2)).mono (hsub))
    have h1 : |∫ s in (y)..(x), Z' (s)| ≤ ∫ s in (y)..(x), |Z' (s)| :=
      intervalIntegral.abs_integral_le_integral_abs (hyx)
    have h2 : ∫ s in (y)..(x), |Z' (s)| ≤ ∫ s in (y)..(x), (t / 2 + Z' (s) ^ 2 / (2 * t)) := by
      refine intervalIntegral.integral_mono_on (hyx) (hint.abs) ((intervalIntegrable_const).add
        (hsq.div_const (_))) (fun s _ => ?_)
      have : 2 * t * |Z' (s)| ≤ t ^ 2 + Z' (s) ^ 2 := by
        nlinarith [sq_nonneg (|Z' (s)| - t), sq_abs (Z' (s))]
      rw [div_add_div (_) (_) (two_ne_zero) (mul_ne_zero (two_ne_zero) (ht.ne')),
        le_div_iff₀ (by positivity)]
      nlinarith
    have h3 : ∫ s in (y)..(x), (t / 2 + Z' (s) ^ 2 / (2 * t)) =
        (x - y) * (t / 2) + (∫ s in (y)..(x), Z' (s) ^ 2) / (2 * t) := by
      rw [intervalIntegral.integral_add (intervalIntegrable_const) (hsq.div_const (_)),
        intervalIntegral.integral_const, intervalIntegral.integral_div, smul_eq_mul]
    have h4 : ∫ s in (y)..(x), Z' (s) ^ 2 ≤ C := by
      refine le_trans (intervalIntegral.integral_mono_interval (hy.1) (hyx) (hx.2) (?_)
        (intervalIntegrable_of_continuousOn (hab.le) (hZ'.pow (2)))) (hC)
      exact Eventually.of_forall (fun s => sq_nonneg (Z' (s)))
    rw [← hftc, abs_of_nonneg (sub_nonneg.2 (hyx))]
    have : (∫ s in (y)..(x), Z' (s) ^ 2) / (2 * t) ≤ C / (2 * t) :=
      div_le_div_of_nonneg_right (h4) (by positivity)
    nlinarith
  intro x hx y hy
  rcases le_total (y) (x) with h | h
  · exact key (x) (hx) (y) (hy) (h)
  · rw [abs_sub_comm, abs_sub_comm (x)]
    exact key (y) (hy) (x) (hx) (h)

/-- Positive lower and upper bounds of a continuous positive function on `[a, b]`. -/
private lemma exists_pos_bounds {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn (f) (Icc (a) (b))) (hpos : ∀ x ∈ Icc (a) (b), 0 < f (x)) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ Icc (a) (b), m ≤ f (x) ∧ f (x) ≤ M := by
  obtain ⟨x₁, hx₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (hab)) (hf)
  obtain ⟨x₂, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (hab)) (hf)
  exact ⟨f (x₁), f (x₂), hpos (x₁) (hx₁), fun x hx => ⟨hmin (hx), hmax (hx)⟩⟩

/-- Only finitely many eigenvalues of `P` lie below each bound. -/
private lemma eigenvalueSet_inter_Iic_finite (P : Problem) (M : ℝ) :
    (eigenvalueSet (P) ∩ Iic (M)).Finite := by
  have hab := P.a_lt_b
  by_contra hinf
  set T := (eigenvalueSet (P) ∩ Iic (M)) \ {-P.L.q (P.a) / P.w (P.a), -P.L.q (P.b) / P.w (P.b)}
    with hT_def
  have hT : T.Infinite := Set.Infinite.sdiff (hinf) (toFinite (_))
  have hwa := P.assumptions.w_pos (P.a) (left_mem_Icc.2 (hab.le))
  have hwb := P.assumptions.w_pos (P.b) (right_mem_Icc.2 (hab.le))
  -- normalised eigenfunctions with a chosen type of boundary condition at each endpoint
  have hdata : ∀ μ, ∃ Z Z' : ℝ → ℝ, ∃ τ : Bool × Bool, μ ∈ T →
      Honest (P) (μ) (Z) (Z') ∧ ∫ x in (P.a)..(P.b), P.w (x) * Z (x) ^ 2 = 1 ∧
      (if τ.1 then P.Ba.α * Z (P.a) + P.Ba.β * Z' (P.a) = 0 else Z (P.a) = 0) ∧
      (if τ.2 then P.Bb.α * Z (P.b) + P.Bb.β * Z' (P.b) = 0 else Z (P.b) = 0) := by
    intro μ
    by_cases hμ : μ ∈ T
    swap
    · exact ⟨0, 0, (true, true), fun h => absurd (h) (hμ)⟩
    obtain ⟨⟨⟨X, hX⟩, -⟩, hμ'⟩ := hμ
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hμ'
    obtain ⟨hH, ha, hb, x₀, hx₀, hne⟩ := eigenfunction_data (hX)
    have ha' : P.Ba.α * X (P.a) + P.Ba.β * derivWithin (X) (Icc (P.a) (P.b)) (P.a) = 0 ∨
        X (P.a) = 0 := by
      rcases ha with h | h | h
      · exact Or.inl (h)
      · exact Or.inr (h)
      · exact absurd (by field_simp; linarith) (hμ'.1)
    have hb' : P.Bb.α * X (P.b) + P.Bb.β * derivWithin (X) (Icc (P.a) (P.b)) (P.b) = 0 ∨
        X (P.b) = 0 := by
      rcases hb with h | h | h
      · exact Or.inl (h)
      · exact Or.inr (h)
      · exact absurd (by field_simp; linarith) (hμ'.2)
    set s := ∫ x in (P.a)..(P.b), P.w (x) * X (x) ^ 2
    have hs : 0 < s :=
      integral_pos_of_ne_zero (hab) (P.assumptions.w_continuousOn.mul (hH.continuousOn.pow (2)))
        (fun x hx => mul_nonneg ((P.assumptions.w_pos (x) (hx)).le) (sq_nonneg (_))) (hx₀)
        (mul_ne_zero ((P.assumptions.w_pos (x₀) (hx₀)).ne') (pow_ne_zero (2) (hne)))
    set c := 1 / Real.sqrt (s)
    have hc2 : c ^ 2 * s = 1 := by
      simp only [c, div_pow, one_pow, Real.sq_sqrt (hs.le)]
      field_simp
    refine ⟨fun x => c * X (x), fun x => c * derivWithin (X) (Icc (P.a) (P.b)) (x),
      (decide (P.Ba.α * X (P.a) + P.Ba.β * derivWithin (X) (Icc (P.a) (P.b)) (P.a) = 0),
        decide (P.Bb.α * X (P.b) + P.Bb.β * derivWithin (X) (Icc (P.a) (P.b)) (P.b) = 0)),
      fun _ => ⟨hH.const_mul (c), ?_, ?_, ?_⟩⟩
    · have e : (fun x => P.w (x) * (c * X (x)) ^ 2) = fun x => c ^ 2 * (P.w (x) * X (x) ^ 2) := by
        funext x
        ring
      rw [e, intervalIntegral.integral_const_mul, hc2]
    · by_cases h : P.Ba.α * X (P.a) + P.Ba.β * derivWithin (X) (Icc (P.a) (P.b)) (P.a) = 0
      · simp only [h, decide_true, ite_true]
        linear_combination c * h
      · simp only [h, decide_false]
        simp [ha'.resolve_left (h)]
    · by_cases h : P.Bb.α * X (P.b) + P.Bb.β * derivWithin (X) (Icc (P.a) (P.b)) (P.b) = 0
      · simp only [h, decide_true, ite_true]
        linear_combination c * h
      · simp only [h, decide_false]
        simp [hb'.resolve_left (h)]
  choose Z Z' τ hZ using hdata
  -- an infinite set of eigenvalues sharing the type of boundary conditions
  have : Infinite (T) := hT.to_subtype
  obtain ⟨τ₀, hτ₀⟩ := Finite.exists_infinite_fiber (fun μ : T => τ (μ))
  set S := {μ | μ ∈ T ∧ τ (μ) = τ₀}
  have hS : S.Infinite := by
    have := (Set.infinite_coe_iff.1 (hτ₀)).image (Subtype.val_injective.injOn)
    refine this.mono (?_)
    rintro _ ⟨μ, hμ, rfl⟩
    exact ⟨μ.2, hμ⟩
  have hST : S ⊆ T := fun μ hμ => hμ.1
  -- orthogonality
  have horth : ∀ μ ∈ S, ∀ ν ∈ S, μ ≠ ν →
      ∫ x in (P.a)..(P.b), P.w (x) * (Z (μ) (x) * Z (ν) (x)) = 0 := by
    intro μ hμ ν hν hne
    obtain ⟨hHμ, -, haμ, hbμ⟩ := hZ (μ) (hST (hμ))
    obtain ⟨hHν, -, haν, hbν⟩ := hZ (ν) (hST (hν))
    rw [hμ.2] at haμ hbμ
    rw [hν.2] at haν hbν
    refine orthogonal (hHμ) (hHν) (hne) (?_) (?_)
    · by_cases h : τ₀.1
      · simp only [h, ite_true] at haμ haν
        exact wronskian_eq_zero (P.assumptions.Ba_ne) (haμ) (haν)
      · simp only [h] at haμ haν
        rw [haμ, haν]
        ring
    · by_cases h : τ₀.2
      · simp only [h, ite_true] at hbμ hbν
        exact wronskian_eq_zero (P.assumptions.Bb_ne) (hbμ) (hbν)
      · simp only [h] at hbμ hbν
        rw [hbμ, hbν]
        ring
  -- uniform bounds
  obtain ⟨pm, pM, hpm, hp⟩ := exists_pos_bounds (hab.le)
    (P.assumptions.p_contDiffOn.continuousOn) (P.assumptions.p_pos)
  obtain ⟨wm, wM, -, hw⟩ := exists_pos_bounds (hab.le) (P.assumptions.w_continuousOn)
    (P.assumptions.w_pos)
  set W := ∫ x in (P.a)..(P.b), P.w (x)
  have hW : 0 < W := integral_pos_of_ne_zero (hab) (P.assumptions.w_continuousOn)
    (fun x hx => (P.assumptions.w_pos (x) (hx)).le) (left_mem_Icc.2 (hab.le))
    ((P.assumptions.w_pos (P.a) (left_mem_Icc.2 (hab.le))).ne')
  set C := max (M / pm) (0)
  have henergy : ∀ μ ∈ S, ∫ x in (P.a)..(P.b), Z' (μ) (x) ^ 2 ≤ C := by
    intro μ hμ
    obtain ⟨hH, hn, ha, hb⟩ := hZ (μ) (hST (hμ))
    have hR := rayleigh (hH) (by
        split_ifs at ha
        · exact Or.inl (ha)
        · exact Or.inr (ha))
      (by
        split_ifs at hb
        · exact Or.inl (hb)
        · exact Or.inr (hb))
    rw [hn, mul_one] at hR
    have hμM : μ ≤ M := (hST (hμ)).1.2
    have hle : ∫ x in (P.a)..(P.b), Z' (μ) (x) ^ 2 ≤
        ∫ x in (P.a)..(P.b), P.L.p (x) * Z' (μ) (x) ^ 2 / pm := by
      refine intervalIntegral.integral_mono_on (hab.le)
        (intervalIntegrable_of_continuousOn (hab.le) (hH.2.1.pow (2)))
        (intervalIntegrable_of_continuousOn (hab.le)
          (((P.assumptions.p_contDiffOn.continuousOn).mul (hH.2.1.pow (2))).div_const (_)))
        (fun x hx => ?_)
      rw [le_div_iff₀ (hpm)]
      nlinarith [(hp (x) (hx)).1, sq_nonneg (Z' (μ) (x))]
    rw [intervalIntegral.integral_div] at hle
    calc _ ≤ _ := hle
      _ ≤ M / pm := div_le_div_of_nonneg_right (hR.trans (hμM)) (hpm.le)
      _ ≤ C := le_max_left (_) (_)
  have hC0 : 0 ≤ C := le_max_right (_) (_)
  -- a uniform bound on the values
  have hval : ∀ μ ∈ S, ∀ x ∈ Icc (P.a) (P.b),
      |Z (μ) (x)| ≤ 1 + 2 / W + (P.b - P.a) / 2 + C / 2 := by
    intro μ hμ x hx
    obtain ⟨hH, hn, -, -⟩ := hZ (μ) (hST (hμ))
    obtain ⟨x₀, hx₀, hsmall⟩ : ∃ x₀ ∈ Icc (P.a) (P.b), Z (μ) (x₀) ^ 2 ≤ 2 / W := by
      by_contra hcon
      push Not at hcon
      have : ∫ x in (P.a)..(P.b), P.w (x) * (2 / W) ≤
          ∫ x in (P.a)..(P.b), P.w (x) * Z (μ) (x) ^ 2 :=
        intervalIntegral.integral_mono_on (hab.le)
          (intervalIntegrable_of_continuousOn (hab.le)
            ((P.assumptions.w_continuousOn).mul (continuousOn_const)))
          (intervalIntegrable_of_continuousOn (hab.le)
            ((P.assumptions.w_continuousOn).mul (hH.continuousOn.pow (2))))
          (fun x hx => mul_le_mul_of_nonneg_left ((hcon (x) (hx)).le)
            ((P.assumptions.w_pos (x) (hx)).le))
      rw [intervalIntegral.integral_mul_const, hn] at this
      have : W * (2 / W) = 2 := by field_simp
      linarith
    have h1 := abs_sub_le_of_integral_sq (hab) (hH.1) (hH.2.1) (henergy (μ) (hμ)) (one_pos)
      (x) (hx) (x₀) (hx₀)
    have h2 : |x - x₀| ≤ P.b - P.a := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hx₀.1, hx₀.2]
    have h3 : |Z (μ) (x₀)| ≤ 1 + 2 / W := by
      have : |Z (μ) (x₀)| ≤ 1 + Z (μ) (x₀) ^ 2 := by
        nlinarith [sq_abs (Z (μ) (x₀)), sq_nonneg (|Z (μ) (x₀)| - 1)]
      linarith
    calc |Z (μ) (x)| = |(Z (μ) (x) - Z (μ) (x₀)) + Z (μ) (x₀)| := by ring_nf
      _ ≤ |Z (μ) (x) - Z (μ) (x₀)| + |Z (μ) (x₀)| := abs_add_le (_) (_)
      _ ≤ _ := by
        have : 1 * |x - x₀| / 2 ≤ (P.b - P.a) / 2 := by linarith
        linarith
  set B := 1 + 2 / W + (P.b - P.a) / 2 + C / 2
  -- the eigenfunctions as bounded continuous functions on `[a, b]`
  have : Infinite (S) := hS.to_subtype
  let e : ℕ ↪ S := Infinite.natEmbedding (S)
  have hcont : ∀ n, ContinuousOn (Z (e (n))) (Icc (P.a) (P.b)) :=
    fun n => (hZ (e (n)) (hST ((e (n)).2))).1.continuousOn
  let f : ℕ → BoundedContinuousFunction (Icc (P.a) (P.b)) (ℝ) := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨(Icc (P.a) (P.b)).domRestrict (Z (e (n))),
      (hcont (n)).domRestrict⟩
  have hf : ∀ n (x : Icc (P.a) (P.b)), f (n) (x) = Z (e (n)) (x) := fun n x => rfl
  have hcpt : IsCompact (closure (range (f))) := by
    refine BoundedContinuousFunction.arzela_ascoli (Icc (-B) (B)) (isCompact_Icc) (range (f))
      (?_) (?_)
    · rintro _ x ⟨n, rfl⟩
      rw [hf]
      exact abs_le.1 (hval (e (n)) ((e (n)).2) (x) (x.2))
    · refine UniformEquicontinuous.equicontinuous (Metric.uniformEquicontinuous_iff.2 (?_))
      intro ε hε
      set t := C / ε + 1
      have ht : 0 < t := by positivity
      refine ⟨ε / t, by positivity, fun x y hxy g => ?_⟩
      obtain ⟨_, ⟨n, rfl⟩⟩ := g
      simp only [Real.dist_eq, hf]
      have := abs_sub_le_of_integral_sq (hab) ((hZ (e (n)) (hST ((e (n)).2))).1.1)
        ((hZ (e (n)) (hST ((e (n)).2))).1.2.1) (henergy (e (n)) ((e (n)).2)) (ht) (x) (x.2) (y)
        (y.2)
      have hxy' : |(x : ℝ) - y| < ε / t := by
        rw [← Real.dist_eq]
        exact hxy
      have h1 : t * |(x : ℝ) - y| / 2 < ε / 2 := by
        have := mul_lt_mul_of_pos_left (hxy') (ht)
        rw [mul_div_cancel₀ (_) (ht.ne')] at this
        linarith
      have h2 : C / (2 * t) < ε / 2 := by
        rw [div_lt_div_iff₀ (by positivity) (two_pos)]
        have : C < ε * t := by
          simp only [t]
          rw [mul_add, mul_div_cancel₀ (_) (hε.ne'), mul_one]
          linarith
        nlinarith
      linarith
  obtain ⟨g, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  set δ := min (1) (1 / W)
  have hδ : 0 < δ := lt_min (one_pos) (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 (hlim.cauchySeq) (δ) (hδ)
  have hdist := hN (N + 1) (Nat.le_succ (N))
  set μ := (e (φ (N + 1)) : ℝ)
  set ν := (e (φ (N)) : ℝ)
  have hμν : μ ≠ ν := fun h =>
    (hφ (Nat.lt_succ_self (N))).ne' (e.injective (Subtype.val_injective (h)))
  have hμS : μ ∈ S := (e (φ (N + 1))).2
  have hνS : ν ∈ S := (e (φ (N))).2
  have hclose : ∀ x ∈ Icc (P.a) (P.b), |Z (μ) (x) - Z (ν) (x)| ≤ δ := fun x hx => by
    have := BoundedContinuousFunction.dist_coe_le_dist (f := f (φ (N + 1))) (g := f (φ (N)))
      ⟨x, hx⟩
    rw [hf, hf, Real.dist_eq] at this
    exact this.trans (hdist.le)
  obtain ⟨hHμ, hnμ, -, -⟩ := hZ (μ) (hST (hμS))
  obtain ⟨hHν, hnν, -, -⟩ := hZ (ν) (hST (hνS))
  have hw' := P.assumptions.w_continuousOn
  have i1 : IntervalIntegrable (fun x => P.w (x) * Z (μ) (x) ^ 2) (volume) (P.a) (P.b) :=
    intervalIntegrable_of_continuousOn (hab.le) (hw'.mul (hHμ.continuousOn.pow (2)))
  have i2 : IntervalIntegrable (fun x => P.w (x) * Z (ν) (x) ^ 2) (volume) (P.a) (P.b) :=
    intervalIntegrable_of_continuousOn (hab.le) (hw'.mul (hHν.continuousOn.pow (2)))
  have i3 : IntervalIntegrable (fun x => 2 * (P.w (x) * (Z (μ) (x) * Z (ν) (x)))) (volume) (P.a)
      (P.b) :=
    intervalIntegrable_of_continuousOn (hab.le)
      (continuousOn_const.mul (hw'.mul (hHμ.continuousOn.mul (hHν.continuousOn))))
  have htwo : ∫ x in (P.a)..(P.b), P.w (x) * (Z (μ) (x) - Z (ν) (x)) ^ 2 = 2 := by
    have e : (fun x => P.w (x) * (Z (μ) (x) - Z (ν) (x)) ^ 2) = fun x =>
        P.w (x) * Z (μ) (x) ^ 2 + P.w (x) * Z (ν) (x) ^ 2 -
          2 * (P.w (x) * (Z (μ) (x) * Z (ν) (x))) := by
      funext x
      ring
    rw [e, intervalIntegral.integral_sub ((i1.add (i2))) (i3),
      intervalIntegral.integral_add (i1) (i2),
      intervalIntegral.integral_const_mul, hnμ, hnν, horth (μ) (hμS) (ν) (hνS) (hμν)]
    ring
  have hsmall : ∫ x in (P.a)..(P.b), P.w (x) * (Z (μ) (x) - Z (ν) (x)) ^ 2 ≤
      ∫ x in (P.a)..(P.b), P.w (x) * δ ^ 2 :=
    intervalIntegral.integral_mono_on (hab.le)
      (intervalIntegrable_of_continuousOn (hab.le)
        (hw'.mul ((hHμ.continuousOn.sub (hHν.continuousOn)).pow (2))))
      (intervalIntegrable_of_continuousOn (hab.le) (hw'.mul (continuousOn_const)))
      (fun x hx => mul_le_mul_of_nonneg_left (by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg (_)) (hclose (x) (hx)) (2))
        ((P.assumptions.w_pos (x) (hx)).le))
  rw [htwo, intervalIntegral.integral_mul_const] at hsmall
  have h1 : δ ≤ 1 := min_le_left (_) (_)
  have h2 : δ * W ≤ 1 := by
    have := mul_le_mul_of_nonneg_right (min_le_right (1) (1 / W)) (hW.le)
    rwa [one_div_mul_cancel (hW.ne')] at this
  have : W * δ ^ 2 ≤ 1 := by nlinarith
  linarith

/-! ### Infinitely many eigenvalues: a scaled Prüfer transformation -/

/-- The extension of a function on `[a, b]` to `ℝ` that is constant outside `[a, b]`. -/
private noncomputable def extIcc (P : Problem) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => f (projIcc (P.a) (P.b) (P.a_lt_b.le) (x))

private lemma extIcc_eq {P : Problem} {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc (P.a) (P.b)) :
    extIcc (P) (f) (x) = f (x) := by
  simp [extIcc, projIcc_of_mem (_) (hx)]

private lemma continuous_extIcc {P : Problem} {f : ℝ → ℝ}
    (hf : ContinuousOn (f) (Icc (P.a) (P.b))) :
    Continuous (extIcc (P) (f)) :=
  hf.comp_continuous (continuous_subtype_val.comp (continuous_projIcc))
    (fun x => (projIcc (P.a) (P.b) (P.a_lt_b.le) (x)).2)

/-- Bounds on the coefficients of `P`, extended to `ℝ`. -/
private lemma coeff_bounds (P : Problem) :
    ∃ pm pM wm wM Q : ℝ, 0 < pm ∧ 0 < wm ∧ 0 ≤ Q ∧ ∀ x, pm ≤ extIcc (P) (P.L.p) (x) ∧
      extIcc (P) (P.L.p) (x) ≤ pM ∧ wm ≤ extIcc (P) (P.w) (x) ∧ extIcc (P) (P.w) (x) ≤ wM ∧
      |extIcc (P) (P.L.q) (x)| ≤ Q := by
  have hab := P.a_lt_b.le
  obtain ⟨pm, pM, hpm, hp⟩ := exists_pos_bounds (hab) (P.assumptions.p_contDiffOn.continuousOn)
    (P.assumptions.p_pos)
  obtain ⟨wm, wM, hwm, hw⟩ := exists_pos_bounds (hab) (P.assumptions.w_continuousOn)
    (P.assumptions.w_pos)
  obtain ⟨x₂, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (hab))
    (P.assumptions.q_continuousOn.abs)
  refine ⟨pm, pM, wm, wM, |P.L.q (x₂)|, hpm, hwm, abs_nonneg (_), fun x => ?_⟩
  have hy := (projIcc (P.a) (P.b) (hab) (x)).2
  exact ⟨(hp (_) (hy)).1, (hp (_) (hy)).2, (hw (_) (hy)).1, (hw (_) (hy)).2, hmax (hy)⟩

/-- The right-hand side of the scaled Prüfer equation
`θ' = k cos² θ / p + (q / k + k w) sin² θ`. -/
private noncomputable def prF (P : Problem) (k x θ : ℝ) : ℝ :=
  k * Real.cos (θ) ^ 2 / extIcc (P) (P.L.p) (x) +
    (extIcc (P) (P.L.q) (x) / k + k * extIcc (P) (P.w) (x)) * Real.sin (θ) ^ 2

private lemma continuous_prF (P : Problem) (k θ : ℝ) :
    Continuous (fun x => prF (P) (k) (x) (θ)) := by
  obtain ⟨pm, pM, wm, wM, Q, hpm, hwm, hQ, hb⟩ := coeff_bounds (P)
  have hp := continuous_extIcc (P := P) (P.assumptions.p_contDiffOn.continuousOn)
  have hq := continuous_extIcc (P := P) (P.assumptions.q_continuousOn)
  have hw := continuous_extIcc (P := P) (P.assumptions.w_continuousOn)
  exact (continuous_const.div (hp) (fun x => ((hpm.trans_le ((hb (x)).1))).ne')).add
    (((hq.div_const (_)).add (continuous_const.mul (hw))).mul (continuous_const))

private lemma prF_lipschitz (P : Problem) {k : ℝ} (hk : 0 < k) :
    ∃ K : NNReal, ∀ x, LipschitzWith (K) (prF (P) (k) (x)) := by
  obtain ⟨pm, pM, wm, wM, Q, hpm, hwm, hQ, hb⟩ := coeff_bounds (P)
  set Bm := Q / k + k * wM + k / pm
  have hwM : 0 ≤ wM := (hwm.le.trans ((hb (0)).2.2.1)).trans ((hb (0)).2.2.2.1)
  have hBm : 0 ≤ Bm := by positivity
  refine ⟨(2 * Bm).toNNReal, fun x => LipschitzWith.of_dist_le_mul (fun θ φ => ?_)⟩
  rw [Real.coe_toNNReal (_) (by positivity), Real.dist_eq, Real.dist_eq]
  obtain ⟨h1, -, h3, h4, h5⟩ := hb (x)
  set B := extIcc (P) (P.L.q) (x) / k + k * extIcc (P) (P.w) (x) - k / extIcc (P) (P.L.p) (x)
  have hp0 : 0 < extIcc (P) (P.L.p) (x) := hpm.trans_le (h1)
  have hB : |B| ≤ Bm := by
    have e1 : |extIcc (P) (P.L.q) (x) / k| ≤ Q / k := by
      rw [abs_div, abs_of_pos (hk)]
      exact div_le_div_of_nonneg_right (h5) (hk.le)
    have e2 : |k * extIcc (P) (P.w) (x)| ≤ k * wM := by
      rw [abs_mul, abs_of_pos (hk), abs_of_pos (hwm.trans_le (h3))]
      exact mul_le_mul_of_nonneg_left (h4) (hk.le)
    have e3 : |k / extIcc (P) (P.L.p) (x)| ≤ k / pm := by
      rw [abs_div, abs_of_pos (hk), abs_of_pos (hp0)]
      exact div_le_div_of_nonneg_left (hk.le) (hpm) (h1)
    calc |B| ≤ |extIcc (P) (P.L.q) (x) / k + k * extIcc (P) (P.w) (x)| +
          |k / extIcc (P) (P.L.p) (x)| :=
          abs_sub (_) (_)
      _ ≤ |extIcc (P) (P.L.q) (x) / k| + |k * extIcc (P) (P.w) (x)| +
          |k / extIcc (P) (P.L.p) (x)| := by
          gcongr
          exact abs_add_le (_) (_)
      _ ≤ Bm := by linarith
  have hdiff : prF (P) (k) (x) (θ) - prF (P) (k) (x) (φ) =
      B * (Real.sin (θ) ^ 2 - Real.sin (φ) ^ 2) := by
    simp only [prF, B, Real.cos_sq']
    ring
  have hsin : |Real.sin (θ) ^ 2 - Real.sin (φ) ^ 2| ≤ 2 * |θ - φ| := by
    have : Real.sin (θ) ^ 2 - Real.sin (φ) ^ 2 =
        (Real.sin (θ) - Real.sin (φ)) * (Real.sin (θ) + Real.sin (φ)) := by ring
    rw [this, abs_mul]
    have h1 := Real.abs_sin_sub_sin_le (θ) (φ)
    have h2 : |Real.sin (θ) + Real.sin (φ)| ≤ 2 := by
      have := abs_add_le (Real.sin (θ)) (Real.sin (φ))
      linarith [Real.abs_sin_le_one (θ), Real.abs_sin_le_one (φ)]
    calc _ ≤ |θ - φ| * 2 := mul_le_mul (h1) (h2) (abs_nonneg (_)) (abs_nonneg (_))
      _ = _ := by ring
  rw [hdiff, abs_mul]
  calc |B| * |Real.sin (θ) ^ 2 - Real.sin (φ) ^ 2| ≤ Bm * (2 * |θ - φ|) :=
        mul_le_mul (hB) (hsin) (abs_nonneg (_)) (hBm)
    _ = 2 * Bm * |θ - φ| := by ring

private lemma prF_abs_le (P : Problem) {k : ℝ} (hk : 0 < k) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x θ, |prF (P) (k) (x) (θ)| ≤ L := by
  obtain ⟨pm, pM, wm, wM, Q, hpm, hwm, hQ, hb⟩ := coeff_bounds (P)
  have hwM : 0 ≤ wM := (hwm.le.trans ((hb (0)).2.2.1)).trans ((hb (0)).2.2.2.1)
  refine ⟨k / pm + (Q / k + k * wM), by positivity, fun x θ => ?_⟩
  obtain ⟨h1, -, h3, h4, h5⟩ := hb (x)
  have hp0 : 0 < extIcc (P) (P.L.p) (x) := hpm.trans_le (h1)
  have hc := Real.cos_sq_le_one (θ)
  have hs := Real.sin_sq_le_one (θ)
  have hc0 := sq_nonneg (Real.cos (θ))
  have hs0 := sq_nonneg (Real.sin (θ))
  have t1 : |k * Real.cos (θ) ^ 2 / extIcc (P) (P.L.p) (x)| ≤ k / pm := by
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (hp0) (hpm)]
    have e1 := mul_le_mul_of_nonneg_left (hc) (mul_nonneg (hk.le) (hpm.le))
    have e2 := mul_le_mul_of_nonneg_left (h1) (hk.le)
    nlinarith
  have t2 : |(extIcc (P) (P.L.q) (x) / k + k * extIcc (P) (P.w) (x)) * Real.sin (θ) ^ 2| ≤
      Q / k + k * wM := by
    rw [abs_mul, abs_of_nonneg (hs0)]
    have : |extIcc (P) (P.L.q) (x) / k + k * extIcc (P) (P.w) (x)| ≤ Q / k + k * wM := by
      refine (abs_add_le (_) (_)).trans (add_le_add (?_) (?_))
      · rw [abs_div, abs_of_pos (hk)]
        exact div_le_div_of_nonneg_right (h5) (hk.le)
      · rw [abs_mul, abs_of_pos (hk), abs_of_pos (hwm.trans_le (h3))]
        exact mul_le_mul_of_nonneg_left (h4) (hk.le)
    calc _ ≤ (Q / k + k * wM) * 1 :=
          mul_le_mul (this) (hs) (hs0) (by positivity)
      _ = _ := mul_one (_)
  exact (abs_add_le (_) (_)).trans (add_le_add (t1) (t2))

/-- Existence of the scaled Prüfer angle: `θ(a) = 0` and `θ' = prF k x θ` on `[a, b]`. -/
private lemma prufer_exists (P : Problem) {k : ℝ} (hk : 0 < k) :
    ∃ θ : ℝ → ℝ, θ (P.a) = 0 ∧ ∀ x ∈ Icc (P.a) (P.b),
      HasDerivWithinAt (θ) (prF (P) (k) (x) (θ (x))) (Icc (P.a) (P.b)) (x) := by
  obtain ⟨K, hK⟩ := prF_lipschitz (P) (hk)
  obtain ⟨L, hL0, hL⟩ := prF_abs_le (P) (hk)
  have hab := P.a_lt_b
  let t₀ : Icc (P.a) (P.b) := ⟨P.a, left_mem_Icc.2 (hab.le)⟩
  have hPL : IsPicardLindelof (fun t θ => prF (P) (k) (t) (θ)) (t₀) (0)
      (L.toNNReal * (P.b - P.a).toNNReal) (0) (L.toNNReal) (K) :=
    { lipschitzOnWith := fun t _ => (hK (t)).lipschitzOnWith
      continuousOn := fun θ _ => (continuous_prF (P) (k) (θ)).continuousOn
      norm_le := fun t _ θ _ => by
        rw [Real.norm_eq_abs, Real.coe_toNNReal (_) (hL0)]
        exact hL (t) (θ)
      mul_max_le := by
        simp only [t₀, sub_self, NNReal.coe_mul, Real.coe_toNNReal (_) (hL0),
          Real.coe_toNNReal (_) (sub_nonneg.2 (hab.le)), NNReal.coe_zero, sub_zero]
        rw [max_eq_left (sub_nonneg.2 (hab.le))] }
  obtain ⟨θ, hθ0, hθ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨θ, hθ0, hθ⟩

/-- For large `k`, the right-hand side of the Prüfer equation is at least `c k`. -/
private lemma prF_lower (P : Problem) :
    ∃ k₀ > 0, ∃ c > 0, ∀ k ≥ k₀, ∀ x θ, k * c ≤ prF (P) (k) (x) (θ) := by
  obtain ⟨pm, pM, wm, wM, Q, hpm, hwm, hQ, hb⟩ := coeff_bounds (P)
  have hpM : 0 < pM := hpm.trans_le (((hb (0)).1).trans ((hb (0)).2.1))
  refine ⟨1 + 2 * Q / wm, by positivity, min (1 / pM) (wm / 2), lt_min (by positivity)
    (by positivity), fun k hk x θ => ?_⟩
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) (hk)
  have hk1 : 1 ≤ k := le_trans (le_add_of_nonneg_right (by positivity)) (hk)
  obtain ⟨h1, h2, h3, -, h5⟩ := hb (x)
  have hp0 : 0 < extIcc (P) (P.L.p) (x) := hpm.trans_le (h1)
  set c := min (1 / pM) (wm / 2)
  have hc1 : c ≤ 1 / extIcc (P) (P.L.p) (x) :=
    (min_le_left (_) (_)).trans (one_div_le_one_div_of_le (hp0) (h2))
  have hc2 : c ≤ wm / 2 := min_le_right (_) (_)
  -- `Q / k ≤ k wm / 2`
  have hQk : Q / k ≤ k * wm / 2 := by
    rw [div_le_iff₀ (hk0)]
    have : 2 * Q / wm ≤ k := by linarith
    rw [div_le_iff₀ (hwm)] at this
    nlinarith
  have hq : -(Q / k) ≤ extIcc (P) (P.L.q) (x) / k := by
    rw [neg_div', div_le_div_iff_of_pos_right (hk0)]
    linarith [(abs_le.1 (h5)).1]
  have hr : k * c ≤ extIcc (P) (P.L.q) (x) / k + k * extIcc (P) (P.w) (x) := by
    have : k * c ≤ k * (wm / 2) := mul_le_mul_of_nonneg_left (hc2) (hk0.le)
    nlinarith
  have hcos : k * c * Real.cos (θ) ^ 2 ≤ k * Real.cos (θ) ^ 2 / extIcc (P) (P.L.p) (x) := by
    have := mul_le_mul_of_nonneg_left (hc1) (mul_nonneg (hk0.le) (sq_nonneg (Real.cos (θ))))
    calc k * c * Real.cos (θ) ^ 2 = k * Real.cos (θ) ^ 2 * c := by ring
      _ ≤ k * Real.cos (θ) ^ 2 * (1 / extIcc (P) (P.L.p) (x)) := this
      _ = _ := by ring
  have hsin : k * c * Real.sin (θ) ^ 2 ≤
      (extIcc (P) (P.L.q) (x) / k + k * extIcc (P) (P.w) (x)) * Real.sin (θ) ^ 2 :=
    mul_le_mul_of_nonneg_right (hr) (sq_nonneg (_))
  have hsc := Real.sin_sq_add_cos_sq (θ)
  have hkc : k * c = k * c * Real.sin (θ) ^ 2 + k * c * Real.cos (θ) ^ 2 := by
    linear_combination (-(k * c)) * hsc
  simp only [prF]
  linarith

/-- The scaled Prüfer angle for `k > 0` (and `0` otherwise). -/
private noncomputable def pruferAngle (P : Problem) (k : ℝ) : ℝ → ℝ :=
  if hk : 0 < k then Classical.choose (prufer_exists (P) (hk)) else 0

private lemma pruferAngle_spec (P : Problem) {k : ℝ} (hk : 0 < k) :
    pruferAngle (P) (k) (P.a) = 0 ∧ ∀ x ∈ Icc (P.a) (P.b), HasDerivWithinAt (pruferAngle (P) (k))
      (prF (P) (k) (x) (pruferAngle (P) (k) (x))) (Icc (P.a) (P.b)) (x) := by
  simp only [pruferAngle, hk, ↓reduceDIte]
  exact Classical.choose_spec (prufer_exists (P) (hk))

/-- The derivative within `[a, b]`, at a point of `[a, b)`, gives the right derivative. -/
private lemma hasDerivWithinAt_Ici {a b : ℝ} {f : ℝ → ℝ} {f' t : ℝ}
    (h : HasDerivWithinAt (f) (f') (Icc (a) (b)) (t)) (ht : t ∈ Ico (a) (b)) :
    HasDerivWithinAt (f) (f') (Ici (t)) (t) :=
  h.mono_of_mem_nhdsWithin (mem_of_superset (Icc_mem_nhdsGE (ht.2))
    (Icc_subset_Icc_left (ht.1)))

/-- The Prüfer angle at `b` depends continuously on `k > 0`. -/
private lemma continuousOn_pruferAngle (P : Problem) :
    ContinuousOn (fun k => pruferAngle (P) (k) (P.b)) (Ioi (0)) := by
  intro k₀ hk₀
  have hk₀' : 0 < k₀ := hk₀
  have hab := P.a_lt_b
  obtain ⟨K, hK⟩ := prF_lipschitz (P) (hk₀')
  obtain ⟨pm, pM, wm, wM, Q, hpm, hwm, hQ, hb⟩ := coeff_bounds (P)
  have hwM : 0 ≤ wM := (hwm.le.trans ((hb (0)).2.2.1)).trans ((hb (0)).2.2.2.1)
  set e : ℝ → ℝ := fun j => |j - k₀| / pm + Q * |1 / j - 1 / k₀| + wM * |j - k₀|
  have hbound : ∀ j > 0, dist (pruferAngle (P) (j) (P.b)) (pruferAngle (P) (k₀) (P.b)) ≤
      gronwallBound (0) (K) (e (j) + 0) (P.b - P.a) := by
    intro j hj
    obtain ⟨hja, hjd⟩ := pruferAngle_spec (P) (hj)
    obtain ⟨hka, hkd⟩ := pruferAngle_spec (P) (hk₀')
    refine dist_le_of_approx_trajectories_ODE (v := fun t θ => prF (P) (k₀) (t) (θ)) (hK)
      (fun x hx => (hjd (x) (hx)).continuousWithinAt)
      (fun t ht => hasDerivWithinAt_Ici (hjd (t) (Ico_subset_Icc_self (ht))) (ht))
      (fun t _ => ?_)
      (fun x hx => (hkd (x) (hx)).continuousWithinAt)
      (fun t ht => hasDerivWithinAt_Ici (hkd (t) (Ico_subset_Icc_self (ht))) (ht))
      (fun t _ => by simp) (by rw [hja, hka, dist_self]) (P.b) (right_mem_Icc.2 (hab.le))
    -- `|prF j - prF k₀| ≤ e j`
    set θ := pruferAngle (P) (j) (t)
    obtain ⟨h1, -, h3, h4, h5⟩ := hb (t)
    have hp0 : 0 < extIcc (P) (P.L.p) (t) := hpm.trans_le (h1)
    have hdiff : prF (P) (j) (t) (θ) - prF (P) (k₀) (t) (θ) =
        (j - k₀) * (Real.cos (θ) ^ 2 / extIcc (P) (P.L.p) (t)) +
          extIcc (P) (P.L.q) (t) * (1 / j - 1 / k₀) * Real.sin (θ) ^ 2 +
          (j - k₀) * extIcc (P) (P.w) (t) * Real.sin (θ) ^ 2 := by
      simp only [prF]
      ring
    rw [Real.dist_eq, hdiff]
    have hc : Real.cos (θ) ^ 2 / extIcc (P) (P.L.p) (t) ≤ 1 / pm := by
      rw [div_le_div_iff₀ (hp0) (hpm)]
      nlinarith [Real.cos_sq_le_one (θ), sq_nonneg (Real.cos (θ))]
    have hs := Real.sin_sq_le_one (θ)
    have hs0 := sq_nonneg (Real.sin (θ))
    have hc0 : 0 ≤ Real.cos (θ) ^ 2 / extIcc (P) (P.L.p) (t) := by positivity
    have hw0 : 0 ≤ extIcc (P) (P.w) (t) := by linarith
    calc _ ≤ |(j - k₀) * (Real.cos (θ) ^ 2 / extIcc (P) (P.L.p) (t))| +
          |extIcc (P) (P.L.q) (t) * (1 / j - 1 / k₀) * Real.sin (θ) ^ 2| +
          |(j - k₀) * extIcc (P) (P.w) (t) * Real.sin (θ) ^ 2| := abs_add_three (_) (_) (_)
      _ ≤ |j - k₀| * (1 / pm) + Q * |1 / j - 1 / k₀| * 1 + |j - k₀| * wM * 1 := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hc0),
            abs_of_nonneg (hs0), abs_of_nonneg (hw0)]
          gcongr
      _ = e (j) := by
          simp only [e]
          ring
  -- the bound tends to `0`
  have he : ContinuousAt (e) (k₀) := by
    simp only [e]
    have : ContinuousAt (fun j : ℝ => 1 / j) (k₀) :=
      continuousAt_const.div (continuousAt_id) (hk₀'.ne')
    fun_prop
  have he0 : e (k₀) = 0 := by simp [e]
  have hlim : Tendsto (fun j => gronwallBound (0) (K) (e (j) + 0) (P.b - P.a)) (𝓝 (k₀))
      (𝓝 (0)) := by
    have h1 : Tendsto (fun j => e (j) + 0) (𝓝 (k₀)) (𝓝 (0)) := by
      have := he.tendsto
      rw [he0] at this
      simpa only [add_zero] using this
    have := ((gronwallBound_continuous_ε (0) (K) (P.b - P.a)).tendsto (0)).comp (h1)
    rwa [gronwallBound_ε0_δ0] at this
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall
    (fun _ => dist_nonneg)) (eventually_nhdsWithin_of_forall (fun j hj => hbound (j) (hj)))
    (hlim.mono_left (nhdsWithin_le_nhds)))

/-- A lower bound for the Prüfer angle at `b`: `θ(b) ≥ c k (b - a)`. -/
private lemma pruferAngle_ge (P : Problem) {k c : ℝ} (hk : 0 < k)
    (hc : ∀ x θ, k * c ≤ prF (P) (k) (x) (θ)) :
    k * c * (P.b - P.a) ≤ pruferAngle (P) (k) (P.b) := by
  have hab := P.a_lt_b
  obtain ⟨ha, hd⟩ := pruferAngle_spec (P) (hk)
  have hmono : MonotoneOn (fun x => pruferAngle (P) (k) (x) - k * c * x) (Icc (P.a) (P.b)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => prF (P) (k) (x)
      (pruferAngle (P) (k) (x)) - k * c) (convex_Icc (_) (_))
      (fun x hx => ((hd (x) (hx)).continuousWithinAt.sub (continuousWithinAt_const.mul
        (continuousWithinAt_id)))) (fun x hx => ?_) (fun x _ => sub_nonneg.2 (hc (x) (_)))
    rw [interior_Icc] at hx ⊢
    have := (hd (x) (Ioo_subset_Icc_self (hx))).mono (Ioo_subset_Icc_self)
    exact this.sub ((hasDerivWithinAt_id (x) (_)).const_mul (k * c) |>.congr_deriv (by ring))
  have := hmono (left_mem_Icc.2 (hab.le)) (right_mem_Icc.2 (hab.le)) (hab.le)
  simp only [ha] at this
  linarith

/-- From a Prüfer angle with `θ(a) = 0` and `θ(b) = m π`, `m ≥ 1`, an eigenfunction of `P` for
`k²`: `u = ρ sin θ` on `[a, b]`, with a jump outside `[a, b]`. -/
private lemma isEigenvalue_of_prufer {P : Problem} {k : ℝ} (hk : 0 < k) {θ : ℝ → ℝ}
    (hθa : θ (P.a) = 0)
    (hθ : ∀ x ∈ Icc (P.a) (P.b),
      HasDerivWithinAt (θ) (prF (P) (k) (x) (θ (x))) (Icc (P.a) (P.b)) (x))
    {m : ℕ} (hθb : θ (P.b) = m * Real.pi) (hm : 1 ≤ m) : IsEigenvalue (P) (k ^ 2) := by
  have hab := P.a_lt_b
  have hU : UniqueDiffOn (ℝ) (Icc (P.a) (P.b)) := uniqueDiffOn_Icc (hab)
  have hθc : ContinuousOn (θ) (Icc (P.a) (P.b)) := fun x hx => (hθ (x) (hx)).continuousWithinAt
  obtain ⟨pm, pM, wm, wM, Q, hpm, hwm, hQ, hb⟩ := coeff_bounds (P)
  have hp0 : ∀ x, 0 < extIcc (P) (P.L.p) (x) := fun x => hpm.trans_le ((hb (x)).1)
  have hpc := continuous_extIcc (P := P) (P.assumptions.p_contDiffOn.continuousOn)
  have hqc := continuous_extIcc (P := P) (P.assumptions.q_continuousOn)
  have hwc := continuous_extIcc (P := P) (P.assumptions.w_continuousOn)
  have hθ'c := continuous_extIcc (P := P) (hθc)
  set θ' := extIcc (P) (θ)
  set p' := extIcc (P) (P.L.p)
  set q' := extIcc (P) (P.L.q)
  set w' := extIcc (P) (P.w)
  set G : ℝ → ℝ := fun t => (k / p' (t) - (q' (t) / k + k * w' (t))) * Real.sin (θ' (t)) *
    Real.cos (θ' (t))
  have hGc : Continuous (G) :=
    (((continuous_const.div (hpc) (fun x => (hp0 (x)).ne')).sub ((hqc.div_const (_)).add
      (continuous_const.mul (hwc)))).mul (Real.continuous_sin.comp (hθ'c))).mul
      (Real.continuous_cos.comp (hθ'c))
  set ρ : ℝ → ℝ := fun x => Real.exp (∫ t in (P.a)..(x), G (t))
  have hρ : ∀ x, HasDerivAt (ρ) (G (x) * ρ (x)) (x) := fun x => by
    have := ((hGc.integral_hasStrictDerivAt (P.a) (x)).hasDerivAt).exp
    convert this using 1
    ring
  have hρc : Continuous (ρ) := continuous_iff_continuousAt.2 (fun x => (hρ (x)).continuousAt)
  have hρ0 : ∀ x, 0 < ρ (x) := fun x => Real.exp_pos (_)
  -- the derivative of `θ'` within `[a, b]`
  have hθ' : ∀ x ∈ Icc (P.a) (P.b), HasDerivWithinAt (θ') (prF (P) (k) (x) (θ (x)))
      (Icc (P.a) (P.b)) (x) := fun x hx =>
    (hθ (x) (hx)).congr (fun y hy => extIcc_eq (hy)) (extIcc_eq (hx))
  set u : ℝ → ℝ := fun x => ρ (x) * Real.sin (θ' (x))
  set v : ℝ → ℝ := fun x => k * ρ (x) * Real.cos (θ' (x)) / p' (x)
  set g : ℝ → ℝ := fun x => k * ρ (x) * Real.cos (θ' (x))
  have hu : ∀ x ∈ Icc (P.a) (P.b), HasDerivWithinAt (u) (v (x)) (Icc (P.a) (P.b)) (x) := by
    intro x hx
    have h := ((hρ (x)).hasDerivWithinAt).mul ((hθ' (x) (hx)).sin)
    convert h using 1
    have hx' : θ' (x) = θ (x) := extIcc_eq (hx)
    simp only [v, G, prF, hx']
    have hsc := Real.sin_sq_add_cos_sq (θ (x))
    linear_combination (-(k * ρ (x) * Real.cos (θ (x)) / p' (x))) * hsc
  have hg : ∀ x ∈ Icc (P.a) (P.b), HasDerivWithinAt (g)
      (-(P.L.q (x) + k ^ 2 * P.w (x)) * u (x)) (Icc (P.a) (P.b)) (x) := by
    intro x hx
    have h := (((hρ (x)).hasDerivWithinAt).const_mul (k)).mul ((hθ' (x) (hx)).cos)
    convert h using 1
    have hx' : θ' (x) = θ (x) := extIcc_eq (hx)
    simp only [u, G, prF, hx', ← extIcc_eq (f := P.L.q) (hx), ← extIcc_eq (f := P.w) (hx)]
    have hsc := Real.sin_sq_add_cos_sq (θ (x))
    have hkr : k * (q' (x) / k) = q' (x) := mul_div_cancel₀ (_) (hk.ne')
    linear_combination (ρ (x) * Real.sin (θ (x)) * (Real.sin (θ (x)) ^ 2 + Real.cos (θ (x)) ^ 2)) *
      hkr + (ρ (x) * Real.sin (θ (x)) * (q' (x) + k ^ 2 * w' (x))) * hsc
  have hpg : ∀ x ∈ Icc (P.a) (P.b), P.L.p (x) * v (x) = g (x) := fun x hx => by
    simp only [v, g, ← extIcc_eq (f := P.L.p) (hx)]
    field_simp [(hp0 (x)).ne']
    ring
  -- the eigenfunction
  set X : ℝ → ℝ := fun x => if x ∈ Icc (P.a) (P.b) then u (x) else u (x) + 1
  have hXu : EqOn (X) (u) (Icc (P.a) (P.b)) := fun x hx => by simp only [X, hx, ↓reduceIte]
  have huc : Continuous (u) := hρc.mul (Real.continuous_sin.comp (hθ'c))
  have hgc : Continuous (g) := (continuous_const.mul (hρc)).mul (Real.continuous_cos.comp (hθ'c))
  -- interior points
  have hderivX : ∀ y ∈ Ioo (P.a) (P.b), deriv (X) (y) = v (y) := fun y hy => by
    have hn : Icc (P.a) (P.b) ∈ 𝓝 (y) := Icc_mem_nhds (hy.1) (hy.2)
    have heq : X =ᶠ[𝓝 (y)] u := Filter.eventually_of_mem (hn) (hXu)
    rw [heq.deriv_eq]
    exact ((hu (y) (Ioo_subset_Icc_self (hy))).hasDerivAt (hn)).deriv
  -- endpoints
  have hend : ∀ c ∈ Icc (P.a) (P.b), c ∉ Ioo (P.a) (P.b) → Real.sin (θ (c)) = 0 →
      X (c) = 0 ∧ deriv (X) (c) = 0 ∧ deriv (fun y => P.L.p (y) * deriv (X) (y)) (c) = 0 := by
    intro c hc hcI hsin
    have hθc' : θ' (c) = θ (c) := extIcc_eq (hc)
    have hXc : X (c) = 0 := by
      rw [hXu (hc)]
      simp only [u, hθc', hsin, mul_zero]
    -- `X` jumps at `c`
    have hside : c = P.a ∨ c = P.b := by
      by_contra h
      push Not at h
      exact hcI ⟨lt_of_le_of_ne (hc.1) (h.1.symm), lt_of_le_of_ne (hc.2) (h.2)⟩
    have hjump : ¬ ContinuousAt (X) (c) := by
      intro hcont
      obtain ⟨F, hF, hout⟩ : ∃ F : Filter (ℝ), F.NeBot ∧ F ≤ 𝓝 (c) ∧
          ∀ᶠ y in F, y ∉ Icc (P.a) (P.b) := by
        rcases hside with rfl | rfl
        · exact ⟨𝓝[<] P.a, inferInstance, nhdsWithin_le_nhds,
            eventually_nhdsWithin_of_forall (fun y hy hy' => (not_le.2 (hy)) (hy'.1))⟩
        · exact ⟨𝓝[>] P.b, inferInstance, nhdsWithin_le_nhds,
            eventually_nhdsWithin_of_forall (fun y hy hy' => (not_le.2 (hy)) (hy'.2))⟩
      have t1 : Tendsto (X) (F) (𝓝 (X (c))) := hcont.tendsto.mono_left (hout.1)
      have t2 : Tendsto (X) (F) (𝓝 (u (c) + 1)) := by
        refine ((huc.tendsto (c)).add (tendsto_const_nhds)).mono_left (hout.1) |>.congr' ?_
        filter_upwards [hout.2] with y hy
        simp only [X, hy, ↓reduceIte]
      have := tendsto_nhds_unique (t1) (t2)
      have hu0 : u (c) = 0 := (hXu (hc)).symm.trans (hXc)
      rw [hXc, hu0] at this
      norm_num at this
    have hdX : deriv (X) (c) = 0 :=
      deriv_zero_of_not_differentiableAt (fun h => hjump (h.continuousAt))
    refine ⟨hXc, hdX, deriv_zero_of_not_differentiableAt (fun h => ?_)⟩
    -- `p X'` jumps at `c`
    have hcos : Real.cos (θ (c)) ≠ 0 := by
      intro h0
      have := Real.sin_sq_add_cos_sq (θ (c))
      rw [hsin, h0] at this
      norm_num at this
    have hgc0 : g (c) ≠ 0 := by
      simp only [g, hθc']
      exact mul_ne_zero (mul_ne_zero (hk.ne') ((hρ0 (c)).ne')) (hcos)
    have := eq_of_eqOn_Ioo (hab) (hc) (h.continuousAt.continuousWithinAt)
      (hgc.continuousAt.continuousWithinAt) (fun y hy => by
        rw [hderivX (y) (hy), hpg (y) (Ioo_subset_Icc_self (hy))])
    simp only [hdX, mul_zero] at this
    exact hgc0 (this.symm)
  have hθbsin : Real.sin (θ (P.b)) = 0 := by
    rw [hθb]
    exact Real.sin_nat_mul_pi (m)
  have hθasin : Real.sin (θ (P.a)) = 0 := by
    rw [hθa, Real.sin_zero]
  have hea := hend (P.a) (left_mem_Icc.2 (hab.le)) (fun h => lt_irrefl (_) (h.1)) (hθasin)
  have heb := hend (P.b) (right_mem_Icc.2 (hab.le)) (fun h => lt_irrefl (_) (h.2)) (hθbsin)
  refine ⟨X, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- `X` is `C²` on `[a, b]`
    have hρ1 : ContDiffOn (ℝ) (1) (ρ) (Icc (P.a) (P.b)) := by
      have : ContDiff (ℝ) (1) (ρ) := by
        rw [contDiff_one_iff_deriv]
        refine ⟨fun x => (hρ (x)).differentiableAt, ?_⟩
        have : deriv (ρ) = fun x => G (x) * ρ (x) := funext (fun x => (hρ (x)).deriv)
        rw [this]
        exact hGc.mul (hρc)
      exact this.contDiffOn
    have hθ'1 : ContDiffOn (ℝ) (1) (θ') (Icc (P.a) (P.b)) := by
      have hcont : ContinuousOn (fun x => prF (P) (k) (x) (θ (x))) (Icc (P.a) (P.b)) := by
        have : ContinuousOn (fun x => prF (P) (k) (x) (θ' (x))) (Icc (P.a) (P.b)) := by
          simp only [prF]
          exact (((continuous_const.mul ((Real.continuous_cos.comp (hθ'c)).pow (2))).div (hpc)
            (fun x => (hp0 (x)).ne')).add (((hqc.div_const (_)).add (continuous_const.mul
            (hwc))).mul ((Real.continuous_sin.comp (hθ'c)).pow (2)))).continuousOn
        exact this.congr (fun x hx => by simp only [extIcc_eq (f := θ) (hx), θ'])
      have := (contDiffOn_succ_iff_derivWithin (n := 0) (hU)).2 ⟨fun x hx =>
        (hθ' (x) (hx)).differentiableWithinAt, by simp, contDiffOn_zero.2 (hcont.congr
          (fun x hx => (hθ' (x) (hx)).derivWithin (hU (x) (hx))))⟩
      simpa using this
    have hp'1 : ContDiffOn (ℝ) (1) (p') (Icc (P.a) (P.b)) :=
      P.assumptions.p_contDiffOn.congr (fun x hx => extIcc_eq (hx))
    have hv1 : ContDiffOn (ℝ) (1) (v) (Icc (P.a) (P.b)) :=
      ((contDiffOn_const.mul (hρ1)).mul (hθ'1.cos)).div (hp'1) (fun x _ => (hp0 (x)).ne')
    have hu2 : ContDiffOn (ℝ) (2) (u) (Icc (P.a) (P.b)) := by
      have := (contDiffOn_succ_iff_derivWithin (n := 1) (hU)).2 ⟨fun x hx =>
        (hu (x) (hx)).differentiableWithinAt, by simp, hv1.congr
          (fun x hx => (hu (x) (hx)).derivWithin (hU (x) (hx)))⟩
      exact this
    exact hu2.congr (hXu)
  · -- the equation
    intro x hx
    simp only [Operator.apply]
    by_cases hxI : x ∈ Ioo (P.a) (P.b)
    · have hn : Ioo (P.a) (P.b) ∈ 𝓝 (x) := Ioo_mem_nhds (hxI.1) (hxI.2)
      have heq : (fun y => P.L.p (y) * deriv (X) (y)) =ᶠ[𝓝 (x)] g := by
        filter_upwards [hn] with y hy
        rw [hderivX (y) (hy), hpg (y) (Ioo_subset_Icc_self (hy))]
      rw [heq.deriv_eq, ((hg (x) (hx)).hasDerivAt (Icc_mem_nhds (hxI.1) (hxI.2))).deriv,
        hXu (hx)]
      ring
    · have hs : Real.sin (θ (x)) = 0 := by
        rcases eq_or_lt_of_le (hx.1) with h | h
        · rw [← h]
          exact hθasin
        · rcases eq_or_lt_of_le (hx.2) with h' | h'
          · rw [h']
            exact hθbsin
          · exact absurd ⟨h, h'⟩ (hxI)
      obtain ⟨h1, -, h3⟩ := hend (x) (hx) (hxI) (hs)
      rw [h3, h1]
      ring
  · simp only [BoundaryConditions.Robin.Operator.Satisfies, BoundaryConditions.Robin.Operator.apply,
      P.assumptions.Ba_c, hea.1, hea.2.1, Pi.zero_apply]
    ring
  · simp only [BoundaryConditions.Robin.Operator.Satisfies, BoundaryConditions.Robin.Operator.apply,
      P.assumptions.Bb_c, heb.1, heb.2.1, Pi.zero_apply]
    ring
  · -- `X ≠ 0` where `θ = π / 2`
    have hmem : Real.pi / 2 ∈ Icc (θ (P.a)) (θ (P.b)) := by
      rw [hθa, hθb]
      constructor
      · positivity
      · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        nlinarith [Real.pi_pos]
    obtain ⟨x, hx, hθx⟩ := intermediate_value_Icc (hab.le) (hθc) (hmem)
    refine ⟨x, hx, ?_⟩
    rw [hXu (hx)]
    simp only [u, extIcc_eq (f := θ) (hx), θ', hθx, Real.sin_pi_div_two, mul_one]
    exact (hρ0 (x)).ne'

/-- `P` has infinitely many eigenvalues. -/
private lemma eigenvalueSet_infinite (P : Problem) : (eigenvalueSet (P)).Infinite := by
  have hab := P.a_lt_b
  obtain ⟨k₀, hk₀, c, hc, hlow⟩ := prF_lower (P)
  set H := fun k => pruferAngle (P) (k) (P.b)
  have hH := continuousOn_pruferAngle (P)
  set N₀ := ⌈H (k₀) / Real.pi⌉₊ + 1
  have hcb : 0 < c * (P.b - P.a) := mul_pos (hc) (sub_pos.2 (hab))
  -- for each `n`, a `k ≥ k₀` with `θ_k(b) = (N₀ + n) π`
  have hex : ∀ n : ℕ, ∃ k ∈ Icc (k₀) (max (k₀) ((N₀ + n) * Real.pi / (c * (P.b - P.a)))),
      H (k) = (N₀ + n : ℕ) * Real.pi := by
    intro n
    set K := max (k₀) ((N₀ + n) * Real.pi / (c * (P.b - P.a)))
    have hK : k₀ ≤ K := le_max_left (_) (_)
    have hcont : ContinuousOn (H) (Icc (k₀) (K)) :=
      hH.mono (fun k hk => lt_of_lt_of_le (hk₀) (hk.1))
    have h1 : H (k₀) ≤ (N₀ + n : ℕ) * Real.pi := by
      have : H (k₀) / Real.pi ≤ N₀ := by
        have := Nat.le_ceil (H (k₀) / Real.pi)
        simp only [N₀]
        push_cast
        linarith
      rw [div_le_iff₀ (Real.pi_pos)] at this
      push_cast
      nlinarith [Real.pi_pos]
    have h2 : (N₀ + n : ℕ) * Real.pi ≤ H (K) := by
      have hKpos : 0 < K := lt_of_lt_of_le (hk₀) (hK)
      have := pruferAngle_ge (P) (hKpos) (hlow (K) (hK))
      have h3 : (N₀ + n) * Real.pi / (c * (P.b - P.a)) ≤ K := le_max_right (_) (_)
      rw [div_le_iff₀ (hcb)] at h3
      push_cast
      nlinarith
    exact intermediate_value_Icc (hK) (hcont) ⟨h1, h2⟩
  choose k hk hkH using hex
  have hkpos : ∀ n, 0 < k (n) := fun n => lt_of_lt_of_le (hk₀) ((hk (n)).1)
  refine Set.infinite_of_injective_forall_mem (f := fun n => k (n) ^ 2) (fun n m h => ?_)
    (fun n => ?_)
  · have : k (n) = k (m) := by
      exact (sq_eq_sq₀ ((hkpos (n)).le) ((hkpos (m)).le)).1 (h)
    have h' := hkH (n)
    rw [this, hkH (m)] at h'
    have := mul_right_cancel₀ (Real.pi_pos.ne') (h')
    exact_mod_cast (Nat.add_left_cancel (Nat.cast_injective (this.symm)))
  · obtain ⟨ha, hd⟩ := pruferAngle_spec (P) (hkpos (n))
    exact isEigenvalue_of_prufer (hkpos (n)) (ha) (hd) (hkH (n)) (by omega)

end ExistsEigenvalueSeq

/-- The eigenvalues of `P` form a sequence `0 ≤ λ₀ < λ₁ < ⋯` with `λₙ → +∞`. -/
theorem exists_eigenvalue_seq (P : Problem) :
    ∃ «λₙ» : ℕ → ℝ, StrictMono («λₙ») ∧ 0 ≤ «λₙ» (0) ∧
      Filter.Tendsto («λₙ») (Filter.atTop) (Filter.atTop) ∧
      Set.range («λₙ») = eigenvalueSet (P) := by
  have hnonneg : eigenvalueSet (P) ⊆ Set.Ici (0) := fun μ hμ => eigenvalue_nonneg (hμ)
  have hfin : ∀ M : ℝ, (eigenvalueSet (P) ∩ Set.Iic (M)).Finite :=
    eigenvalueSet_inter_Iic_finite (P)
  have hinf : (eigenvalueSet (P)).Infinite := eigenvalueSet_infinite (P)
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
