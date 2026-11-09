module

public import Mathlib

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# The self-adjoint second-order linear ODE

On an interval `[a, b]`, with coefficients `p` and `r`, the self-adjoint equation is

* `(p y')' + r y = 0`,

where `p` is continuously differentiable and positive and `r` is continuous. A Sturm-Liouville
equation `(p y')' + q y = -λ w y` is the case `r = q + λ w`.

* `SelfAdjoint.IsSolution`: `y` is twice continuously differentiable on `[a, b]` and solves the
  equation there.
* `SelfAdjoint.IsSolution.eq_zero_of_cauchy`: a solution with `y (x₁) = y' (x₁) = 0` at an interior
  point vanishes on `[a, b]`.
* `SelfAdjoint.IsSolution.eq_zero_of_mul_eq_zero`: a nonzero solution does not vanish on any open
  subinterval, so it cannot satisfy `g y = 0` for a continuous `g` that is nonzero somewhere.
* `SelfAdjoint.IsSolution.hasDerivAt_ratio`: the Riccati equation for `p y' / y`.
* `SelfAdjoint.IsSolution.relation`: the relation between solutions of two equations with the same
  solution `y`, obtained by eliminating `y''`.
-/

@[expose] public section

open Set

namespace MathPhysicsTheory.ODE.SelfAdjoint

/-- The regularity of the coefficients of `(p y')' + r y = 0` on `[a, b]`: `p` is positive and
`C¹`, and `r` is continuous. -/
structure RegularCoeffs (a b : ℝ) (p r : ℝ → ℝ) : Prop where
  /-- `p` is positive. -/
  p_pos : ∀ x ∈ Icc (a) (b), 0 < p (x)
  /-- `p` is `C¹`. -/
  p_contDiffOn : ContDiffOn (ℝ) (1) (p) (Icc (a) (b))
  /-- `r` is continuous. -/
  r_continuousOn : ContinuousOn (r) (Icc (a) (b))

/-- `p` is differentiable at interior points. -/
theorem RegularCoeffs.differentiableAt_p {a b : ℝ} {p r : ℝ → ℝ}
    (hc : RegularCoeffs (a) (b) (p) (r)) {x : ℝ} (hx : x ∈ Ioo (a) (b)) :
    DifferentiableAt (ℝ) (p) (x) :=
  (hc.p_contDiffOn.contDiffAt (Icc_mem_nhds (hx.1) (hx.2))).differentiableAt (by norm_num)

/-- `y` solves `(p y')' + r y = 0` on `[a, b]` and is `C²` there. -/
def IsSolution (a b : ℝ) (p r : ℝ → ℝ) (y : ℝ → ℝ) : Prop :=
  ContDiffOn (ℝ) (2) (y) (Icc (a) (b)) ∧
    ∀ x ∈ Icc (a) (b), deriv (fun t => p (t) * deriv (y) (t)) (x) + r (x) * y (x) = 0

namespace IsSolution

variable {a b : ℝ} {p r : ℝ → ℝ} {y : ℝ → ℝ}

/-- At an interior point, `y` is differentiable. -/
theorem hasDerivAt (h : IsSolution (a) (b) (p) (r) (y)) {x : ℝ} (hx : x ∈ Ioo (a) (b)) :
    HasDerivAt (y) (deriv (y) (x)) (x) := by
  have : ContDiffAt (ℝ) (2) (y) (x) := h.1.contDiffAt (Icc_mem_nhds (hx.1) (hx.2))
  exact (this.differentiableAt (by norm_num)).hasDerivAt

/-- At an interior point, `deriv y` is differentiable. -/
theorem differentiableAt_deriv (h : IsSolution (a) (b) (p) (r) (y)) {x : ℝ}
    (hx : x ∈ Ioo (a) (b)) : DifferentiableAt (ℝ) (deriv (y)) (x) := by
  have h1 : ContDiffOn (ℝ) (2) (y) (Ioo (a) (b)) := h.1.mono (Ioo_subset_Icc_self)
  have h2 : ContDiffOn (ℝ) (1) (deriv (y)) (Ioo (a) (b)) :=
    h1.deriv_of_isOpen (isOpen_Ioo) (by norm_num)
  exact (h2.contDiffAt (isOpen_Ioo.mem_nhds (hx))).differentiableAt (by norm_num)

/-- The flux `p y'` has derivative `-r y` at an interior point. -/
theorem hasDerivAt_flux (hc : RegularCoeffs (a) (b) (p) (r))
    (h : IsSolution (a) (b) (p) (r) (y)) {x : ℝ} (hx : x ∈ Ioo (a) (b)) :
    HasDerivAt (fun t => p (t) * deriv (y) (t)) (-r (x) * y (x)) (x) := by
  have hd : DifferentiableAt (ℝ) (fun t => p (t) * deriv (y) (t)) (x) :=
    (hc.differentiableAt_p (hx)).mul (h.differentiableAt_deriv (hx))
  have := h.2 (x) (Ioo_subset_Icc_self (hx))
  have e : deriv (fun t => p (t) * deriv (y) (t)) (x) = -r (x) * y (x) := by
    linarith
  rw [← e]
  exact hd.hasDerivAt

/-- Uniqueness for the Cauchy problem: a solution with `y (x₁) = 0` and `y' (x₁) = 0` at an interior
point `x₁` vanishes on all of `[a, b]`. -/
theorem eq_zero_of_cauchy (hc : RegularCoeffs (a) (b) (p) (r))
    (h : IsSolution (a) (b) (p) (r) (y)) {x₁ : ℝ} (hx₁ : x₁ ∈ Ioo (a) (b))
    (h0 : y (x₁) = 0) (h1 : deriv (y) (x₁) = 0) : ∀ x ∈ Icc (a) (b), y (x) = 0 := by
  have hab : a < b := hx₁.1.trans (hx₁.2)
  have hpc : ContinuousOn (p) (Icc (a) (b)) := hc.p_contDiffOn.continuousOn
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun x => (p (x))⁻¹) (hpc.inv₀ (fun x hx => (hc.p_pos (x) (hx)).ne'))
  obtain ⟨M₂, hM₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := r) (hc.r_continuousOn)
  set M : ℝ := max (max (M₁) (M₂)) (0) with hM
  have hM0 : 0 ≤ M := le_max_right (_) (_)
  have hM1 : ∀ x ∈ Icc (a) (b), |(p (x))⁻¹| ≤ M := fun x hx => by
    have := hM₁ (x) (hx)
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left (_) (_)).trans (le_max_left (_) (_)))
  have hM2 : ∀ x ∈ Icc (a) (b), |r (x)| ≤ M := fun x hx => by
    have := hM₂ (x) (hx)
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_right (_) (_)).trans (le_max_left (_) (_)))
  let v : ℝ → ℝ × ℝ → ℝ × ℝ := fun t u => (u.2 / p (t), -r (t) * u.1)
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
    · have : |-r (t) * u.1 - -r (t) * u'.1| = |r (t)| * |u.1 - u'.1| := by
        rw [← abs_mul, ← abs_neg]; congr 1; ring
      rw [this]
      calc |r (t)| * |u.1 - u'.1| ≤ M * |u.1 - u'.1| :=
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

/-- Elimination of `y''`: if `y` solves the equation for the coefficients `(p₁, r₁)` and for
`(p₂, r₂)`, then with `c = p₂ / p₁` we get `c' (p₁ y') + (r₂ - c r₁) y = 0` at interior points. -/
theorem relation {p₁ r₁ p₂ r₂ : ℝ → ℝ} (hc₁ : RegularCoeffs (a) (b) (p₁) (r₁))
    (hc₂ : RegularCoeffs (a) (b) (p₂) (r₂))
    (h₁ : IsSolution (a) (b) (p₁) (r₁) (y)) (h₂ : IsSolution (a) (b) (p₂) (r₂) (y))
    {x : ℝ} (hx : x ∈ Ioo (a) (b)) :
    deriv (fun t => p₂ (t) / p₁ (t)) (x) * (p₁ (x) * deriv (y) (x)) +
      (r₂ (x) - p₂ (x) / p₁ (x) * r₁ (x)) * y (x) = 0 := by
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

/-- The ratio `m = p y' / y` satisfies the Riccati equation `m' = -r - m² / p` where `y ≠ 0`. -/
theorem hasDerivAt_ratio (hc : RegularCoeffs (a) (b) (p) (r))
    (h : IsSolution (a) (b) (p) (r) (y)) {x : ℝ} (hx : x ∈ Ioo (a) (b)) (hy : y (x) ≠ 0) :
    HasDerivAt (fun t => p (t) * deriv (y) (t) / y (t))
      (-r (x) - (p (x) * deriv (y) (x) / y (x)) ^ 2 / p (x)) (x) := by
  have hp := (hc.p_pos (x) (Ioo_subset_Icc_self (hx))).ne'
  have H := (h.hasDerivAt_flux (hc) (hx)).div (h.hasDerivAt (hx)) (hy)
  convert H using 1
  field_simp

/-- A nonzero solution does not vanish on an open subinterval: if `g` is continuous on `(a, b)`
and `g y = 0` there, then `g = 0` on `(a, b)`. -/
theorem eq_zero_of_mul_eq_zero (hc : RegularCoeffs (a) (b) (p) (r))
    (h : IsSolution (a) (b) (p) (r) (y)) (hne : ∃ x ∈ Icc (a) (b), y (x) ≠ 0)
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

end IsSolution

end MathPhysicsTheory.ODE.SelfAdjoint

end
