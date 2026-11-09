module

public import Mathlib

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Auxiliary results for the uniqueness of the inverse Sturm-Liouville problem

* `ODESolution`: `y` is `C²` on `[a, b]` and solves `(p y')' + q y + λ w y = 0` there.
* `eq_zero_of_cauchy`: a solution with `y (x₁) = y' (x₁) = 0` at an interior point vanishes.
-/

@[expose] public section

open Set

namespace MathPhysicsTheory.SturmLiouville

/-- The regularity of the coefficients of a Sturm-Liouville equation on `[a, b]`. -/
structure RegularCoeffs (a b : ℝ) (p q w : ℝ → ℝ) : Prop where
  /-- `p` is positive. -/
  p_pos : ∀ x ∈ Icc (a) (b), 0 < p (x)
  /-- `w` is positive. -/
  w_pos : ∀ x ∈ Icc (a) (b), 0 < w (x)
  /-- `p` is `C¹`. -/
  p_contDiffOn : ContDiffOn (ℝ) (1) (p) (Icc (a) (b))
  /-- `q` is continuous. -/
  q_continuousOn : ContinuousOn (q) (Icc (a) (b))
  /-- `w` is continuous. -/
  w_continuousOn : ContinuousOn (w) (Icc (a) (b))

/-- `y` solves `(p y')' + q y + λ w y = 0` on `[a, b]` and is `C²` there. -/
def ODESolution (a b : ℝ) (p q w : ℝ → ℝ) («λ» : ℝ) (y : ℝ → ℝ) : Prop :=
  ContDiffOn (ℝ) (2) (y) (Icc (a) (b)) ∧ ∀ x ∈ Icc (a) (b),
    deriv (fun t => p (t) * deriv (y) (t)) (x) + q (x) * y (x) + «λ» * w (x) * y (x) = 0

namespace ODESolution

variable {a b : ℝ} {p q w : ℝ → ℝ} {l : ℝ} {y : ℝ → ℝ}

/-- At an interior point, `y` is differentiable. -/
theorem hasDerivAt (h : ODESolution (a) (b) (p) (q) (w) (l) (y)) {x : ℝ} (hx : x ∈ Ioo (a) (b)) :
    HasDerivAt (y) (deriv (y) (x)) (x) := by
  have : ContDiffAt (ℝ) (2) (y) (x) := h.1.contDiffAt (Icc_mem_nhds (hx.1) (hx.2))
  exact (this.differentiableAt (by norm_num)).hasDerivAt

/-- At an interior point, `deriv y` is differentiable. -/
theorem hasDerivAt_deriv (h : ODESolution (a) (b) (p) (q) (w) (l) (y)) {x : ℝ}
    (hx : x ∈ Ioo (a) (b)) : DifferentiableAt (ℝ) (deriv (y)) (x) := by
  have h1 : ContDiffOn (ℝ) (2) (y) (Ioo (a) (b)) := h.1.mono (Ioo_subset_Icc_self)
  have h2 : ContDiffOn (ℝ) (1) (deriv (y)) (Ioo (a) (b)) :=
    h1.deriv_of_isOpen (isOpen_Ioo) (by norm_num)
  exact (h2.contDiffAt (isOpen_Ioo.mem_nhds (hx))).differentiableAt (by norm_num)

/-- The flux `p y'` has derivative `-(q + λ w) y` at an interior point. -/
theorem hasDerivAt_flux (hc : RegularCoeffs (a) (b) (p) (q) (w))
    (h : ODESolution (a) (b) (p) (q) (w) (l) (y)) {x : ℝ} (hx : x ∈ Ioo (a) (b)) :
    HasDerivAt (fun t => p (t) * deriv (y) (t)) (-(q (x) + l * w (x)) * y (x)) (x) := by
  have hp : DifferentiableAt (ℝ) (p) (x) :=
    ((hc.p_contDiffOn.contDiffAt (Icc_mem_nhds (hx.1) (hx.2))).differentiableAt (by norm_num))
  have hd : DifferentiableAt (ℝ) (fun t => p (t) * deriv (y) (t)) (x) :=
    hp.mul (h.hasDerivAt_deriv (hx))
  have := h.2 (x) (Ioo_subset_Icc_self (hx))
  have e : deriv (fun t => p (t) * deriv (y) (t)) (x) = -(q (x) + l * w (x)) * y (x) := by
    linarith
  rw [← e]
  exact hd.hasDerivAt

/-- Uniqueness for the Cauchy problem: a solution with `y (x₁) = 0` and `y' (x₁) = 0` at an interior
point `x₁` vanishes on all of `[a, b]`. -/
theorem eq_zero_of_cauchy (hc : RegularCoeffs (a) (b) (p) (q) (w))
    (h : ODESolution (a) (b) (p) (q) (w) (l) (y)) {x₁ : ℝ} (hx₁ : x₁ ∈ Ioo (a) (b))
    (h0 : y (x₁) = 0) (h1 : deriv (y) (x₁) = 0) : ∀ x ∈ Icc (a) (b), y (x) = 0 := by
  have hab : a < b := hx₁.1.trans (hx₁.2)
  have hpc : ContinuousOn (p) (Icc (a) (b)) := hc.p_contDiffOn.continuousOn
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun x => (p (x))⁻¹) (hpc.inv₀ (fun x hx => (hc.p_pos (x) (hx)).ne'))
  obtain ⟨M₂, hM₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun x => q (x) + l * w (x))
    (hc.q_continuousOn.add (continuousOn_const.mul (hc.w_continuousOn)))
  set M : ℝ := max (max (M₁) (M₂)) (0) with hM
  have hM0 : 0 ≤ M := le_max_right (_) (_)
  have hM1 : ∀ x ∈ Icc (a) (b), |(p (x))⁻¹| ≤ M := fun x hx => by
    have := hM₁ (x) (hx)
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left (_) (_)).trans (le_max_left (_) (_)))
  have hM2 : ∀ x ∈ Icc (a) (b), |q (x) + l * w (x)| ≤ M := fun x hx => by
    have := hM₂ (x) (hx)
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_right (_) (_)).trans (le_max_left (_) (_)))
  let v : ℝ → ℝ × ℝ → ℝ × ℝ := fun t u => (u.2 / p (t), -(q (t) + l * w (t)) * u.1)
  have hv : ∀ t ∈ Ioo (a) (b), LipschitzOnWith (Real.toNNReal (M)) (v (t)) (univ) := by
    intro t ht
    have ht' : t ∈ Icc (a) (b) := Ioo_subset_Icc_self (ht)
    refine (LipschitzWith.of_dist_le_mul (fun u u' => ?_)).lipschitzOnWith
    rw [Real.coe_toNNReal (_) (hM0), Prod.dist_eq, Prod.dist_eq]
    simp only [v, Real.dist_eq]
    refine max_le (?_) (?_)
    · have : |u.2 / p (t) - u'.2 / p (t)| = |(p (t))⁻¹| * |u.2 - u'.2| := by
        rw [← abs_mul]; congr 1; field_simp
      rw [this]
      calc |(p (t))⁻¹| * |u.2 - u'.2| ≤ M * |u.2 - u'.2| :=
            mul_le_mul_of_nonneg_right (hM1 (t) (ht')) (abs_nonneg (_))
        _ ≤ M * max (|u.1 - u'.1|) (|u.2 - u'.2|) :=
            mul_le_mul_of_nonneg_left (le_max_right (_) (_)) (hM0)
    · have : |-(q (t) + l * w (t)) * u.1 - -(q (t) + l * w (t)) * u'.1| =
          |q (t) + l * w (t)| * |u.1 - u'.1| := by
        rw [← abs_mul, ← abs_neg]; congr 1; ring
      rw [this]
      calc |q (t) + l * w (t)| * |u.1 - u'.1| ≤ M * |u.1 - u'.1| :=
            mul_le_mul_of_nonneg_right (hM2 (t) (ht')) (abs_nonneg (_))
        _ ≤ M * max (|u.1 - u'.1|) (|u.2 - u'.2|) :=
            mul_le_mul_of_nonneg_left (le_max_left (_) (_)) (hM0)
  let f : ℝ → ℝ × ℝ := fun t => (y (t), p (t) * deriv (y) (t))
  let g : ℝ → ℝ × ℝ := fun _ => (0, 0)
  have hf : ∀ t ∈ Ioo (a) (b),
      HasDerivAt (f) (v (t) (f (t))) (t) ∧ f (t) ∈ (univ : Set (ℝ × ℝ)) := by
    intro t ht
    refine ⟨?_, trivial⟩
    have := (h.hasDerivAt (ht)).prodMk (h.hasDerivAt_flux (hc) (ht))
    convert this using 1
    have hp := (hc.p_pos (t) (Ioo_subset_Icc_self (ht))).ne'
    simp only [v, f]
    ext
    · field_simp
    · rfl
  have hg : ∀ t ∈ Ioo (a) (b),
      HasDerivAt (g) (v (t) (g (t))) (t) ∧ g (t) ∈ (univ : Set (ℝ × ℝ)) := by
    intro t ht
    refine ⟨?_, trivial⟩
    have := hasDerivAt_const (t) ((0 : ℝ), (0 : ℝ))
    convert this using 1
    simp [v, g]
  have heq : f (x₁) = g (x₁) := by simp [f, g, h0, h1]
  have key := ODE_solution_unique_of_mem_Ioo (hv) (hx₁) (hf) (hg) (heq)
  have hyc : ContinuousOn (y) (Icc (a) (b)) := h.1.continuousOn
  have hI : EqOn (y) (fun _ => 0) (Ioo (a) (b)) := fun t ht => by
    have := congrArg (Prod.fst) (key (ht))
    simpa [f, g] using this
  exact fun x hx => (hI.of_subset_closure (hyc) (continuousOn_const) (Ioo_subset_Icc_self)
    (by rw [closure_Ioo (hab.ne)])) (hx)

end ODESolution

/-- `p` is differentiable at interior points. -/
theorem RegularCoeffs.differentiableAt_p {a b : ℝ} {p q w : ℝ → ℝ}
    (hc : RegularCoeffs (a) (b) (p) (q) (w)) {x : ℝ} (hx : x ∈ Ioo (a) (b)) :
    DifferentiableAt (ℝ) (p) (x) :=
  (hc.p_contDiffOn.contDiffAt (Icc_mem_nhds (hx.1) (hx.2))).differentiableAt (by norm_num)

namespace ODESolution

variable {a b : ℝ} {p q w : ℝ → ℝ} {l : ℝ} {y : ℝ → ℝ}

/-- Elimination of `y''`: if `y` solves the equation for the coefficients `(p₁, q₁, w₁)` and for
`(p₂, q₂, w₂)`, then with `c = p₂ / p₁` we get
`c' (p₁ y') + ((q₂ - c q₁) + λ (w₂ - c w₁)) y = 0` at interior points. -/
theorem relation {p₁ q₁ w₁ p₂ q₂ w₂ : ℝ → ℝ} (hc₁ : RegularCoeffs (a) (b) (p₁) (q₁) (w₁))
    (hc₂ : RegularCoeffs (a) (b) (p₂) (q₂) (w₂))
    (h₁ : ODESolution (a) (b) (p₁) (q₁) (w₁) (l) (y))
    (h₂ : ODESolution (a) (b) (p₂) (q₂) (w₂) (l) (y)) {x : ℝ} (hx : x ∈ Ioo (a) (b)) :
    deriv (fun t => p₂ (t) / p₁ (t)) (x) * (p₁ (x) * deriv (y) (x)) +
      ((q₂ (x) - p₂ (x) / p₁ (x) * q₁ (x)) + l * (w₂ (x) - p₂ (x) / p₁ (x) * w₁ (x))) * y (x) =
      0 := by
  have hp₁ : ∀ t ∈ Ioo (a) (b), p₁ (t) ≠ 0 := fun t ht =>
    (hc₁.p_pos (t) (Ioo_subset_Icc_self (ht))).ne'
  have hcd : HasDerivAt (fun t => p₂ (t) / p₁ (t)) (deriv (fun t => p₂ (t) / p₁ (t)) (x)) (x) :=
    ((hc₂.differentiableAt_p (hx)).div (hc₁.differentiableAt_p (hx)) (hp₁ (x) (hx))).hasDerivAt
  have H3 := hcd.mul (h₁.hasDerivAt_flux (hc₁) (hx))
  have hev : (fun t => p₂ (t) * deriv (y) (t)) =ᶠ[nhds (x)]
      (fun t => p₂ (t) / p₁ (t) * (p₁ (t) * deriv (y) (t))) := by
    filter_upwards [isOpen_Ioo.mem_nhds (hx)] with t ht
    have := hp₁ (t) (ht)
    field_simp
  have H4 := H3.congr_of_eventuallyEq (hev)
  have E := (h₂.hasDerivAt_flux (hc₂) (hx)).unique (H4)
  have hp := hp₁ (x) (hx)
  linear_combination -E

/-- The logarithmic flux `m = p y' / y` satisfies the Riccati equation
`m' = -(q + λ w) - m² / p` where `y ≠ 0`. -/
theorem hasDerivAt_ratio (hc : RegularCoeffs (a) (b) (p) (q) (w))
    (h : ODESolution (a) (b) (p) (q) (w) (l) (y)) {x : ℝ} (hx : x ∈ Ioo (a) (b))
    (hy : y (x) ≠ 0) :
    HasDerivAt (fun t => p (t) * deriv (y) (t) / y (t))
      (-(q (x) + l * w (x)) - (p (x) * deriv (y) (x) / y (x)) ^ 2 / p (x)) (x) := by
  have hp := (hc.p_pos (x) (Ioo_subset_Icc_self (hx))).ne'
  have H := (h.hasDerivAt_flux (hc) (hx)).div (h.hasDerivAt (hx)) (hy)
  convert H using 1
  field_simp

/-- If `h` is continuous on `(a, b)` and `h y = 0` on `(a, b)`, then `y` is not an eigenfunction
unless `h` vanishes on `(a, b)`. -/
theorem eq_zero_of_mul_eq_zero (hc : RegularCoeffs (a) (b) (p) (q) (w))
    (h : ODESolution (a) (b) (p) (q) (w) (l) (y)) (hne : ∃ x ∈ Icc (a) (b), y (x) ≠ 0)
    {g : ℝ → ℝ} (hg : ContinuousOn (g) (Ioo (a) (b)))
    (hgy : ∀ x ∈ Ioo (a) (b), g (x) * y (x) = 0) : ∀ x ∈ Ioo (a) (b), g (x) = 0 := by
  intro x₀ hx₀
  by_contra hne0
  obtain ⟨z, hz, hzne⟩ := hne
  have hev : ∀ᶠ t in nhds (x₀), g (t) ≠ 0 :=
    (hg.continuousAt (isOpen_Ioo.mem_nhds (hx₀))).eventually_ne (hne0)
  have hy0 : y =ᶠ[nhds (x₀)] fun _ => 0 := by
    filter_upwards [hev, isOpen_Ioo.mem_nhds (hx₀)] with t ht1 ht2
    exact (mul_eq_zero.mp (hgy (t) (ht2))).resolve_left (ht1)
  have h0 : y (x₀) = 0 := hy0.eq_of_nhds
  have h1 : deriv (y) (x₀) = 0 := by rw [hy0.deriv_eq]; simp
  exact hzne (eq_zero_of_cauchy (hc) (h) (hx₀) (h0) (h1) (z) (hz))

end ODESolution

/-- The algebraic core of the uniqueness argument: if the ratios `uₙ` satisfy the Riccati equation
for three distinct eigenvalues `l₀ < l₁ < l₂` and are affine in `λ`, then `u₁ = u₀`. -/
theorem ratio_algebra {P q w l₀ l₁ l₂ u₀ u₁ u₂ : ℝ} (hP : 0 < P) (h₀₁ : l₀ < l₁) (h₁₂ : l₁ < l₂)
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
theorem deriv_ratio_eq_zero {a b : ℝ} {p₁ q₁ w₁ p₂ q₂ w₂ : ℝ → ℝ} {lam : ℕ → ℝ} {X : ℕ → ℝ → ℝ}
    (hc₁ : RegularCoeffs (a) (b) (p₁) (q₁) (w₁)) (hc₂ : RegularCoeffs (a) (b) (p₂) (q₂) (w₂))
    (hlam : StrictMono (lam))
    (h₁ : ∀ n, ODESolution (a) (b) (p₁) (q₁) (w₁) (lam (n)) (X (n)))
    (h₂ : ∀ n, ODESolution (a) (b) (p₂) (q₂) (w₂) (lam (n)) (X (n)))
    (hne : ∀ n, ∃ x ∈ Icc (a) (b), X (n) (x) ≠ 0) :
    ∀ x ∈ Ioo (a) (b), deriv (fun t => p₂ (t) / p₁ (t)) (x) = 0 := by
  set c : ℝ → ℝ := fun t => p₂ (t) / p₁ (t) with hcdef
  have hcd : ContDiffOn (ℝ) (1) (c) (Ioo (a) (b)) :=
    (hc₂.p_contDiffOn.mono (Ioo_subset_Icc_self)).div (hc₁.p_contDiffOn.mono (Ioo_subset_Icc_self))
      (fun t ht => (hc₁.p_pos (t) (Ioo_subset_Icc_self (ht))).ne')
  have hcont : ContinuousOn (deriv (c)) (Ioo (a) (b)) :=
    hcd.continuousOn_deriv_of_isOpen (isOpen_Ioo) (le_rfl)
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀, hne0⟩ := hcon
  have hp : ∀ x ∈ Ioo (a) (b), 0 < p₁ (x) := fun x hx => hc₁.p_pos (x) (Ioo_subset_Icc_self (hx))
  have hXne : ∀ n, ∀ x ∈ Ioo (a) (b), deriv (c) (x) ≠ 0 → X (n) (x) ≠ 0 := by
    intro n x hx hcx hXx
    have R := ODESolution.relation (hc₁) (hc₂) (h₁ (n)) (h₂ (n)) (hx)
    rw [hXx, mul_zero, add_zero] at R
    have hd : deriv (X (n)) (x) = 0 := by
      rcases mul_eq_zero.mp (R) with h | h
      · exact absurd (h) (hcx)
      · exact (mul_eq_zero.mp (h)).resolve_left ((hp (x) (hx)).ne')
    obtain ⟨z, hz, hzne⟩ := hne (n)
    exact hzne (ODESolution.eq_zero_of_cauchy (hc₁) (h₁ (n)) (hx) (hXx) (hd) (z) (hz))
  set U : Set (ℝ) := Ioo (a) (b) ∩ deriv (c) ⁻¹' {0}ᶜ with hU
  have hUopen : IsOpen (U) := hcont.isOpen_inter_preimage (isOpen_Ioo) (isOpen_compl_singleton)
  have hx₀U : x₀ ∈ U := ⟨hx₀, hne0⟩
  set m : ℕ → ℝ → ℝ := fun n t => p₁ (t) * deriv (X (n)) (t) / X (n) (t) with hm
  have hmd : ∀ n, ∀ x ∈ U, HasDerivAt (m (n))
      (-(q₁ (x) + lam (n) * w₁ (x)) - (m (n) (x)) ^ 2 / p₁ (x)) (x) := fun n x hx =>
    ODESolution.hasDerivAt_ratio (hc₁) (h₁ (n)) (hx.1) (hXne (n) (x) (hx.1) (hx.2))
  have hrel : ∀ n, ∀ x ∈ U, deriv (c) (x) * m (n) (x) =
      -((q₂ (x) - c (x) * q₁ (x)) + lam (n) * (w₂ (x) - c (x) * w₁ (x))) := by
    intro n x hx
    have R := ODESolution.relation (hc₁) (hc₂) (h₁ (n)) (h₂ (n)) (hx.1)
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
  have hw := (hc₁.w_pos (x₀) (Ioo_subset_Icc_self (hx₀))).ne'
  have hl : lam (1) - lam (0) ≠ 0 := (sub_pos.mpr (hlam (by norm_num))).ne'
  have : (lam (1) - lam (0)) * w₁ (x₀) = 0 := by linarith
  exact (mul_ne_zero (hl) (hw)) (this)

/-- Two sets of coefficients with the same three eigenpairs (distinct eigenvalues) are proportional
on `[a, b]` by a positive constant. -/
theorem proportional_of_eigenpairs {a b : ℝ} (hab : a < b) {p₁ q₁ w₁ p₂ q₂ w₂ : ℝ → ℝ}
    {lam : ℕ → ℝ} {X : ℕ → ℝ → ℝ}
    (hc₁ : RegularCoeffs (a) (b) (p₁) (q₁) (w₁)) (hc₂ : RegularCoeffs (a) (b) (p₂) (q₂) (w₂))
    (hlam : StrictMono (lam))
    (h₁ : ∀ n, ODESolution (a) (b) (p₁) (q₁) (w₁) (lam (n)) (X (n)))
    (h₂ : ∀ n, ODESolution (a) (b) (p₂) (q₂) (w₂) (lam (n)) (X (n)))
    (hne : ∀ n, ∃ x ∈ Icc (a) (b), X (n) (x) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc (a) (b),
      p₂ (x) = c * p₁ (x) ∧ q₂ (x) = c * q₁ (x) ∧ w₂ (x) = c * w₁ (x) := by
  have hmem : (a + b) / 2 ∈ Ioo (a) (b) := ⟨by linarith, by linarith⟩
  have hp₁ : ∀ x ∈ Ioo (a) (b), p₁ (x) ≠ 0 := fun x hx =>
    (hc₁.p_pos (x) (Ioo_subset_Icc_self (hx))).ne'
  have hcd : ContDiffOn (ℝ) (1) (fun t => p₂ (t) / p₁ (t)) (Ioo (a) (b)) :=
    (hc₂.p_contDiffOn.mono (Ioo_subset_Icc_self)).div (hc₁.p_contDiffOn.mono (Ioo_subset_Icc_self))
      (hp₁)
  have hconst : ∀ x ∈ Ioo (a) (b), ∀ y ∈ Ioo (a) (b), p₂ (x) / p₁ (x) = p₂ (y) / p₁ (y) :=
    fun x hx y hy => isOpen_Ioo.is_const_of_deriv_eq_zero (isPreconnected_Ioo)
      (hcd.differentiableOn (by norm_num))
      (fun x hx => deriv_ratio_eq_zero (hc₁) (hc₂) (hlam) (h₁) (h₂) (hne) (x) (hx)) (hx) (hy)
  set k : ℝ := p₂ ((a + b) / 2) / p₁ ((a + b) / 2) with hk
  have hkpos : 0 < k :=
    div_pos (hc₂.p_pos (_) (Ioo_subset_Icc_self (hmem)))
      (hc₁.p_pos (_) (Ioo_subset_Icc_self (hmem)))
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
    refine ODESolution.eq_zero_of_mul_eq_zero (hc₁) (h₁ (n)) (hne (n)) (g := fun x =>
      (q₂ (x) - k * q₁ (x)) + lam (n) * (w₂ (x) - k * w₁ (x))) (?_) (?_)
    · exact ((hc₂.q_continuousOn.sub (continuousOn_const.mul (hc₁.q_continuousOn))).add
        (continuousOn_const.mul (hc₂.w_continuousOn.sub
          (continuousOn_const.mul (hc₁.w_continuousOn))))).mono (Ioo_subset_Icc_self)
    · intro x hx
      have R := ODESolution.relation (hc₁) (hc₂) (h₁ (n)) (h₂ (n)) (hx)
      have hc0 : deriv (fun t => p₂ (t) / p₁ (t)) (x) = 0 :=
        deriv_ratio_eq_zero (hc₁) (hc₂) (hlam) (h₁) (h₂) (hne) (x) (hx)
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
  have hpc : ContinuousOn (p₁) (Icc (a) (b)) := hc₁.p_contDiffOn.continuousOn
  have hpc₂ : ContinuousOn (p₂) (Icc (a) (b)) := hc₂.p_contDiffOn.continuousOn
  exact ⟨k, hkpos, fun x hx => ⟨hext (hpc₂) (hpc) (hpk) (x) (hx), hext (hc₂.q_continuousOn)
    (hc₁.q_continuousOn) (hq) (x) (hx),
    hext (hc₂.w_continuousOn) (hc₁.w_continuousOn) (hw) (x) (hx)⟩⟩

end MathPhysicsTheory.SturmLiouville

end
