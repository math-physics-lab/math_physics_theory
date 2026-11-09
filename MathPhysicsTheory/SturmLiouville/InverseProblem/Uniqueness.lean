module

public import Mathlib
public import MathPhysicsTheory.ODE.SelfAdjoint
public import MathPhysicsTheory.SturmLiouville.InverseProblem.Basic

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Uniqueness of the inverse Sturm-Liouville problem

A solution `(p, q, w)` of an inverse problem is unique up to a positive constant factor
(`InverseProblem.solution_unique`).

The proof compares two solutions `(p₁, q₁, w₁)` and `(p₂, q₂, w₂)` that have the same eigenpairs.
With `c = p₂ / p₁`, eliminating `Xₙ''` from the two equations gives, for every `n`,

* `c' (p₁ Xₙ') + ((q₂ - c q₁) + λₙ (w₂ - c w₁)) Xₙ = 0`.

Where `c' ≠ 0`, the ratios `mₙ = p₁ Xₙ' / Xₙ` are therefore affine in `λₙ`. Together with the
Riccati equation `mₙ' = -(q₁ + λₙ w₁) - mₙ² / p₁`, this forces `w₁ = 0` (`deriv_ratio_eq_zero`),
which is excluded. So `c` is constant, and the relation above then gives `q₂ = c q₁` and
`w₂ = c w₁` (`proportional_of_eigenpairs`). The ODE facts used (Cauchy uniqueness for the
eigenfunctions, the Riccati equation) are in `MathPhysicsTheory.ODE.SelfAdjoint`.
-/

@[expose] public section

open Set MathPhysicsTheory.ODE

namespace MathPhysicsTheory.SturmLiouville.InverseProblem

/-- The algebraic core of the uniqueness argument: if the ratios `uₙ` satisfy the Riccati equation
for three distinct eigenvalues `l₀ < l₁ < l₂` and are affine in `λ`, then `u₁ = u₀`. -/
private theorem ratio_algebra {P q w l₀ l₁ l₂ u₀ u₁ u₂ : ℝ} (hP : 0 < P) (h₀₁ : l₀ < l₁)
    (h₁₂ : l₁ < l₂)
    (H : (l₁ - l₀) * (u₂ - u₀) = (l₂ - l₀) * (u₁ - u₀))
    (E : (l₁ - l₀) * ((-(q + l₂ * w) - u₂ ^ 2 / P) - (-(q + l₀ * w) - u₀ ^ 2 / P)) =
      (l₂ - l₀) * ((-(q + l₁ * w) - u₁ ^ 2 / P) - (-(q + l₀ * w) - u₀ ^ 2 / P))) :
    u₁ = u₀ := by
  have hP' : P ≠ 0 := hP.ne'
  have E' : (l₁ - l₀) * (u₂ ^ 2 - u₀ ^ 2) = (l₂ - l₀) * (u₁ ^ 2 - u₀ ^ 2) := by
    field_simp at E
    linarith
  have hA : 0 < l₁ - l₀ := by linarith
  have hB : 0 < l₂ - l₀ := by linarith
  have hBA : 0 < (l₂ - l₀) - (l₁ - l₀) := by linarith
  have key : (l₂ - l₀) * ((l₂ - l₀) - (l₁ - l₀)) * (u₁ - u₀) ^ 2 = 0 := by
    linear_combination (l₁ - l₀) * E' -
      ((l₂ - l₀) * (u₁ - u₀) + (l₁ - l₀) * (2 * u₀ + (u₂ - u₀))) * H
  have : (u₁ - u₀) ^ 2 = 0 := by
    rcases mul_eq_zero.mp (key) with h | h
    · exact absurd (h) ((mul_pos (hB) (hBA)).ne')
    · exact h
  have := pow_eq_zero_iff (two_ne_zero) |>.mp this
  linarith

/-- Core of the uniqueness proof: if two sets of coefficients `(p₁, q₁, w₁)` and `(p₂, q₂, w₂)` have
the same three eigenpairs (with distinct eigenvalues), then `p₂ / p₁` has zero derivative on
`(a, b)`. -/
theorem deriv_ratio_eq_zero {a b : ℝ} {p₁ q₁ w₁ p₂ q₂ w₂ : ℝ → ℝ}
    {Ba Bb : BoundaryConditions.Robin.Operator} {lam : ℕ → ℝ} {X : ℕ → ℝ → ℝ}
    (hA₁ : SturmLiouville.Assumptions (a) (b) ({ p := p₁, q := q₁ }) (w₁) (Ba) (Bb))
    (hA₂ : SturmLiouville.Assumptions (a) (b) ({ p := p₂, q := q₂ }) (w₂) (Ba) (Bb))
    (hlam : StrictMono (lam))
    (h₁ : ∀ n, SelfAdjoint.IsSolution (a) (b) (p₁) (fun x => q₁ (x) + lam (n) * w₁ (x)) (X (n)))
    (h₂ : ∀ n, SelfAdjoint.IsSolution (a) (b) (p₂) (fun x => q₂ (x) + lam (n) * w₂ (x)) (X (n)))
    (hne : ∀ n, ∃ x ∈ Icc (a) (b), X (n) (x) ≠ 0) :
    ∀ x ∈ Ioo (a) (b), deriv (fun t => p₂ (t) / p₁ (t)) (x) = 0 := by
  have hc₁ : ∀ l, SelfAdjoint.RegularCoeffs (a) (b) (p₁) (fun x => q₁ (x) + l * w₁ (x)) :=
    fun l => hA₁.regularCoeffs (l)
  have hc₂ : ∀ l, SelfAdjoint.RegularCoeffs (a) (b) (p₂) (fun x => q₂ (x) + l * w₂ (x)) :=
    fun l => hA₂.regularCoeffs (l)
  have hpd₁ : ContDiffOn (ℝ) (1) (p₁) (Icc (a) (b)) := hA₁.p_contDiffOn
  have hpd₂ : ContDiffOn (ℝ) (1) (p₂) (Icc (a) (b)) := hA₂.p_contDiffOn
  have hpp₁ : ∀ x ∈ Icc (a) (b), 0 < p₁ (x) := hA₁.p_pos
  have hwp₁ : ∀ x ∈ Icc (a) (b), 0 < w₁ (x) := hA₁.w_pos
  set c : ℝ → ℝ := fun t => p₂ (t) / p₁ (t) with hcdef
  have hcd : ContDiffOn (ℝ) (1) (c) (Ioo (a) (b)) :=
    (hpd₂.mono (Ioo_subset_Icc_self)).div (hpd₁.mono (Ioo_subset_Icc_self))
      (fun t ht => (hpp₁ (t) (Ioo_subset_Icc_self (ht))).ne')
  have hcont : ContinuousOn (deriv (c)) (Ioo (a) (b)) :=
    hcd.continuousOn_deriv_of_isOpen (isOpen_Ioo) (le_rfl)
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀, hne0⟩ := hcon
  have hp : ∀ x ∈ Ioo (a) (b), 0 < p₁ (x) := fun x hx => hpp₁ (x) (Ioo_subset_Icc_self (hx))
  have hXne : ∀ n, ∀ x ∈ Ioo (a) (b), deriv (c) (x) ≠ 0 → X (n) (x) ≠ 0 := by
    intro n x hx hcx hXx
    have R := SelfAdjoint.IsSolution.relation (hc₁ (lam (n))) (hc₂ (lam (n))) (h₁ (n))
      (h₂ (n)) (hx)
    rw [hXx, mul_zero, add_zero] at R
    have hd : deriv (X (n)) (x) = 0 := by
      rcases mul_eq_zero.mp (R) with h | h
      · exact absurd (h) (hcx)
      · exact (mul_eq_zero.mp (h)).resolve_left ((hp (x) (hx)).ne')
    obtain ⟨z, hz, hzne⟩ := hne (n)
    exact hzne (SelfAdjoint.IsSolution.eq_zero_of_cauchy (hc₁ (lam (n))) (h₁ (n)) (hx) (hXx) (hd)
      (z) (hz))
  set U : Set (ℝ) := Ioo (a) (b) ∩ deriv (c) ⁻¹' {0}ᶜ with hU
  have hUopen : IsOpen (U) := hcont.isOpen_inter_preimage (isOpen_Ioo) (isOpen_compl_singleton)
  have hx₀U : x₀ ∈ U := ⟨hx₀, hne0⟩
  set m : ℕ → ℝ → ℝ := fun n t => p₁ (t) * deriv (X (n)) (t) / X (n) (t) with hm
  have hmd : ∀ n, ∀ x ∈ U, HasDerivAt (m (n))
      (-(q₁ (x) + lam (n) * w₁ (x)) - (m (n) (x)) ^ 2 / p₁ (x)) (x) := fun n x hx =>
    SelfAdjoint.IsSolution.hasDerivAt_ratio (hc₁ (lam (n))) (h₁ (n)) (hx.1)
      (hXne (n) (x) (hx.1) (hx.2))
  have hrel : ∀ n, ∀ x ∈ U, deriv (c) (x) * m (n) (x) =
      -((q₂ (x) - c (x) * q₁ (x)) + lam (n) * (w₂ (x) - c (x) * w₁ (x))) := by
    intro n x hx
    have R := SelfAdjoint.IsSolution.relation (hc₁ (lam (n))) (hc₂ (lam (n))) (h₁ (n)) (h₂ (n))
      (hx.1)
    have hX := hXne (n) (x) (hx.1) (hx.2)
    simp only [hm]
    field_simp
    linear_combination R
  have hprop : ∀ x ∈ U, (lam (1) - lam (0)) * (m (2) (x) - m (0) (x)) =
      (lam (2) - lam (0)) * (m (1) (x) - m (0) (x)) := by
    intro x hx
    apply mul_left_cancel₀ (hx.2)
    linear_combination (lam (1) - lam (0)) * (hrel (2) (x) (hx) - hrel (0) (x) (hx)) -
      (lam (2) - lam (0)) * (hrel (1) (x) (hx) - hrel (0) (x) (hx))
  have hd1 : ∀ x ∈ U, m (1) (x) = m (0) (x) := by
    intro x hx
    have H1 : HasDerivAt (fun t => (lam (1) - lam (0)) * (m (2) (t) - m (0) (t)))
        ((lam (1) - lam (0)) * ((-(q₁ (x) + lam (2) * w₁ (x)) - (m (2) (x)) ^ 2 / p₁ (x)) -
          (-(q₁ (x) + lam (0) * w₁ (x)) - (m (0) (x)) ^ 2 / p₁ (x)))) (x) :=
      ((hmd (2) (x) (hx)).sub (hmd (0) (x) (hx))).const_mul (_)
    have H2 : HasDerivAt (fun t => (lam (2) - lam (0)) * (m (1) (t) - m (0) (t)))
        ((lam (2) - lam (0)) * ((-(q₁ (x) + lam (1) * w₁ (x)) - (m (1) (x)) ^ 2 / p₁ (x)) -
          (-(q₁ (x) + lam (0) * w₁ (x)) - (m (0) (x)) ^ 2 / p₁ (x)))) (x) :=
      ((hmd (1) (x) (hx)).sub (hmd (0) (x) (hx))).const_mul (_)
    have hev : (fun t => (lam (1) - lam (0)) * (m (2) (t) - m (0) (t))) =ᶠ[nhds (x)]
        (fun t => (lam (2) - lam (0)) * (m (1) (t) - m (0) (t))) := by
      filter_upwards [hUopen.mem_nhds (hx)] with t ht using hprop (t) (ht)
    have E := H1.unique (H2.congr_of_eventuallyEq (hev))
    exact ratio_algebra (hp (x) (hx.1)) (hlam (by norm_num)) (hlam (by norm_num))
      (hprop (x) (hx)) (E)
  -- Contradiction at `x₀`: `m 1 - m 0` vanishes near `x₀`, so its derivative vanishes, but the
  -- Riccati equation gives `-(λ₁ - λ₀) w`.
  have H3 : HasDerivAt (fun t => m (1) (t) - m (0) (t))
      ((-(q₁ (x₀) + lam (1) * w₁ (x₀)) - (m (1) (x₀)) ^ 2 / p₁ (x₀)) -
        (-(q₁ (x₀) + lam (0) * w₁ (x₀)) - (m (0) (x₀)) ^ 2 / p₁ (x₀))) (x₀) :=
    (hmd (1) (x₀) (hx₀U)).sub (hmd (0) (x₀) (hx₀U))
  have hev0 : (fun t => m (1) (t) - m (0) (t)) =ᶠ[nhds (x₀)] fun _ => 0 := by
    filter_upwards [hUopen.mem_nhds (hx₀U)] with t ht
    simp [hd1 (t) (ht)]
  have H4 := H3.unique ((hasDerivAt_const (x₀) (0 : ℝ)).congr_of_eventuallyEq (hev0))
  rw [hd1 (x₀) (hx₀U)] at H4
  have hw := (hwp₁ (x₀) (Ioo_subset_Icc_self (hx₀))).ne'
  have hl : lam (1) - lam (0) ≠ 0 := (sub_pos.mpr (hlam (by norm_num))).ne'
  have : (lam (1) - lam (0)) * w₁ (x₀) = 0 := by linarith
  exact (mul_ne_zero (hl) (hw)) (this)

/-- Two sets of coefficients with the same three eigenpairs (distinct eigenvalues) are proportional
on `[a, b]` by a positive constant. -/
theorem proportional_of_eigenpairs {a b : ℝ} (hab : a < b) {p₁ q₁ w₁ p₂ q₂ w₂ : ℝ → ℝ}
    {Ba Bb : BoundaryConditions.Robin.Operator} {lam : ℕ → ℝ} {X : ℕ → ℝ → ℝ}
    (hA₁ : SturmLiouville.Assumptions (a) (b) ({ p := p₁, q := q₁ }) (w₁) (Ba) (Bb))
    (hA₂ : SturmLiouville.Assumptions (a) (b) ({ p := p₂, q := q₂ }) (w₂) (Ba) (Bb))
    (hlam : StrictMono (lam))
    (h₁ : ∀ n, SelfAdjoint.IsSolution (a) (b) (p₁) (fun x => q₁ (x) + lam (n) * w₁ (x)) (X (n)))
    (h₂ : ∀ n, SelfAdjoint.IsSolution (a) (b) (p₂) (fun x => q₂ (x) + lam (n) * w₂ (x)) (X (n)))
    (hne : ∀ n, ∃ x ∈ Icc (a) (b), X (n) (x) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc (a) (b),
      p₂ (x) = c * p₁ (x) ∧ q₂ (x) = c * q₁ (x) ∧ w₂ (x) = c * w₁ (x) := by
  have hc₁ : ∀ l, SelfAdjoint.RegularCoeffs (a) (b) (p₁) (fun x => q₁ (x) + l * w₁ (x)) :=
    fun l => hA₁.regularCoeffs (l)
  have hc₂ : ∀ l, SelfAdjoint.RegularCoeffs (a) (b) (p₂) (fun x => q₂ (x) + l * w₂ (x)) :=
    fun l => hA₂.regularCoeffs (l)
  have hpd₁ : ContDiffOn (ℝ) (1) (p₁) (Icc (a) (b)) := hA₁.p_contDiffOn
  have hpd₂ : ContDiffOn (ℝ) (1) (p₂) (Icc (a) (b)) := hA₂.p_contDiffOn
  have hpp₁ : ∀ x ∈ Icc (a) (b), 0 < p₁ (x) := hA₁.p_pos
  have hpp₂ : ∀ x ∈ Icc (a) (b), 0 < p₂ (x) := hA₂.p_pos
  have hq₁ : ContinuousOn (q₁) (Icc (a) (b)) := hA₁.q_continuousOn
  have hq₂ : ContinuousOn (q₂) (Icc (a) (b)) := hA₂.q_continuousOn
  have hw₁ : ContinuousOn (w₁) (Icc (a) (b)) := hA₁.w_continuousOn
  have hw₂ : ContinuousOn (w₂) (Icc (a) (b)) := hA₂.w_continuousOn
  have hmem : (a + b) / 2 ∈ Ioo (a) (b) := ⟨by linarith, by linarith⟩
  have hp₁ : ∀ x ∈ Ioo (a) (b), p₁ (x) ≠ 0 := fun x hx =>
    (hpp₁ (x) (Ioo_subset_Icc_self (hx))).ne'
  have hcd : ContDiffOn (ℝ) (1) (fun t => p₂ (t) / p₁ (t)) (Ioo (a) (b)) :=
    (hpd₂.mono (Ioo_subset_Icc_self)).div (hpd₁.mono (Ioo_subset_Icc_self))
      (hp₁)
  have hconst : ∀ x ∈ Ioo (a) (b), ∀ y ∈ Ioo (a) (b), p₂ (x) / p₁ (x) = p₂ (y) / p₁ (y) :=
    fun x hx y hy => isOpen_Ioo.is_const_of_deriv_eq_zero (isPreconnected_Ioo)
      (hcd.differentiableOn (by norm_num))
      (fun x hx => deriv_ratio_eq_zero (hA₁) (hA₂) (hlam) (h₁) (h₂) (hne) (x) (hx)) (hx) (hy)
  set k : ℝ := p₂ ((a + b) / 2) / p₁ ((a + b) / 2) with hk
  have hkpos : 0 < k :=
    div_pos (hpp₂ (_) (Ioo_subset_Icc_self (hmem)))
      (hpp₁ (_) (Ioo_subset_Icc_self (hmem)))
  have hpk : ∀ x ∈ Ioo (a) (b), p₂ (x) = k * p₁ (x) := by
    intro x hx
    have := hconst (x) (hx) (_) (hmem)
    have h' : p₂ (x) / p₁ (x) = k := this
    field_simp [hp₁ (x) (hx)] at h'
    linarith
  -- the combination `(q₂ - k q₁) + λₙ (w₂ - k w₁)` vanishes on `(a, b)` for `n = 0, 1`
  have hg : ∀ n, ∀ x ∈ Ioo (a) (b),
      ((q₂ (x) - k * q₁ (x)) + lam (n) * (w₂ (x) - k * w₁ (x))) = 0 := by
    intro n
    refine SelfAdjoint.IsSolution.eq_zero_of_mul_eq_zero (hc₁ (lam (n))) (h₁ (n)) (hne (n))
      (g := fun x => (q₂ (x) - k * q₁ (x)) + lam (n) * (w₂ (x) - k * w₁ (x))) (?_) (?_)
    · exact ((hq₂.sub (continuousOn_const.mul (hq₁))).add
        (continuousOn_const.mul (hw₂.sub
          (continuousOn_const.mul (hw₁))))).mono (Ioo_subset_Icc_self)
    · intro x hx
      have R := SelfAdjoint.IsSolution.relation (hc₁ (lam (n))) (hc₂ (lam (n))) (h₁ (n))
        (h₂ (n)) (hx)
      have hc0 : deriv (fun t => p₂ (t) / p₁ (t)) (x) = 0 :=
        deriv_ratio_eq_zero (hA₁) (hA₂) (hlam) (h₁) (h₂) (hne) (x) (hx)
      have hcx : p₂ (x) / p₁ (x) = k := hconst (x) (hx) (_) (hmem)
      rw [hc0, hcx] at R
      linarith
  have hw : ∀ x ∈ Ioo (a) (b), w₂ (x) = k * w₁ (x) := by
    intro x hx
    have h0 := hg (0) (x) (hx)
    have h1 := hg (1) (x) (hx)
    have hl : lam (1) - lam (0) ≠ 0 := (sub_pos.mpr (hlam (by norm_num))).ne'
    have : (lam (1) - lam (0)) * (w₂ (x) - k * w₁ (x)) = 0 := by linarith
    have := (mul_eq_zero.mp (this)).resolve_left (hl)
    linarith
  have hq : ∀ x ∈ Ioo (a) (b), q₂ (x) = k * q₁ (x) := by
    intro x hx
    have h0 := hg (0) (x) (hx)
    have := hw (x) (hx)
    rw [this] at h0
    nlinarith
  -- extend from `(a, b)` to `[a, b]` by continuity
  have hext : ∀ {u v : ℝ → ℝ}, ContinuousOn (u) (Icc (a) (b)) → ContinuousOn (v) (Icc (a) (b)) →
      (∀ x ∈ Ioo (a) (b), u (x) = k * v (x)) → ∀ x ∈ Icc (a) (b), u (x) = k * v (x) := by
    intro u v hu hv huv x hx
    have : EqOn (u) (fun t => k * v (t)) (Ioo (a) (b)) := huv
    exact (this.of_subset_closure (hu) (continuousOn_const.mul (hv)) (Ioo_subset_Icc_self)
      (by rw [closure_Ioo (hab.ne)])) (hx)
  have hpc : ContinuousOn (p₁) (Icc (a) (b)) := hpd₁.continuousOn
  have hpc₂ : ContinuousOn (p₂) (Icc (a) (b)) := hpd₂.continuousOn
  exact ⟨k, hkpos, fun x hx => ⟨hext (hpc₂) (hpc) (hpk) (x) (hx), hext (hq₂)
    (hq₁) (hq) (x) (hx),
    hext (hw₂) (hw₁) (hw) (x) (hx)⟩⟩

/-- Uniqueness up to a constant factor: two solutions `(p₁, q₁, w₁)` and `(p₂, q₂, w₂)` of the same
inverse problem differ by a positive constant `c`, that is `p₂ = c p₁`, `q₂ = c q₁` and
`w₂ = c w₁` on `[a, b]`.

The factor cannot be removed: the equation `(p Xₙ')' + q Xₙ + λₙ w Xₙ = 0` is linear in
`(p, q, w)`, so `(c p, c q, c w)` is a solution whenever `(p, q, w)` is, and `c > 0` keeps `p` and
`w` positive. Fixing the scale, for example `p (a)`, makes the solution unique. -/
theorem solution_unique (I : InverseProblem) {p₁ q₁ p₂ q₂ w₁ w₂ : ℝ → ℝ}
    (h₁ : I.IsSolution ({ p := p₁, q := q₁ }) (w₁))
    (h₂ : I.IsSolution ({ p := p₂, q := q₂ }) (w₂)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Set.Icc (I.a) (I.b),
      p₂ (x) = c * p₁ (x) ∧ q₂ (x) = c * q₁ (x) ∧ w₂ (x) = c * w₁ (x) := by
  obtain ⟨P, ha, hb, hBa, hBb, hev, hP⟩ := I.assumptions.exists_problem
  have hlam : StrictMono (I.«λₙ») := by
    rw [hev]
    exact (Classical.choose_spec (Eigenvalues.exists_eigenvalue_seq (P))).1
  have hX : ∀ n, ContDiffOn (ℝ) (2) (I.Xₙ (n)) (Set.Icc (I.a) (I.b)) := fun n => by
    have := (hP (n)).1.contDiffOn
    rwa [ha, hb] at this
  have hne : ∀ n, ∃ x ∈ Set.Icc (I.a) (I.b), I.Xₙ (n) (x) ≠ 0 := fun n => by
    have := (hP (n)).2
    rwa [ha, hb] at this
  have hs : ∀ {p q w : ℝ → ℝ}, I.IsSolution ({ p := p, q := q }) (w) → ∀ n,
      SelfAdjoint.IsSolution (I.a) (I.b) (p) (fun x => q (x) + I.«λₙ» (n) * w (x))
        (I.Xₙ (n)) := fun h n =>
    ⟨hX (n), fun x hx => by
      have := h.2 (n) (x) (hx)
      simp only [Operator.apply] at this
      linear_combination this⟩
  exact proportional_of_eigenpairs (I.a_lt_b) (h₁.1) (h₂.1) (hlam) (hs (h₁)) (hs (h₂)) (hne)

end InverseProblem

end MathPhysicsTheory.SturmLiouville

end
