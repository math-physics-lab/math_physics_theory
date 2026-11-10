module

public import Mathlib
public import MathPhysicsTheory.SturmLiouville.InverseProblem.Basic
public import MathPhysicsTheory.SturmLiouville.InverseProblem.Uniqueness

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Reconstruction of `p`, `q` and `w` from three eigenpairs

A method to solve the inverse Sturm-Liouville problem explicitly. Dividing the equation
`(p Xₙ')' + q Xₙ + λₙ w Xₙ = 0` by `p` gives, with `α = p' / p`, `β = q / p` and `γ = w / p`,

* `Xₙ'' + α Xₙ' + β Xₙ + λₙ γ Xₙ = 0`.

This is a *linear* equation in the three unknown functions `(α, β, γ)` at every point `x`. Three
eigenpairs `n = 0, 1, 2` give a `3 × 3` linear system with matrix rows `(Xₙ', Xₙ, λₙ Xₙ)` and
right-hand side `-Xₙ''`, which Cramer's rule solves: `α = A / D`, `β = B / D`, `γ = G / D`
(`reconstruction_formulas`), wherever the determinant `D = fluxDet` is nonzero.

`D` cannot vanish on an interval (`exists_fluxDet_ne_zero`): on such an interval the ratios
`Xₙ' / Xₙ` would be affine in `λₙ`, and the Riccati equation then forces `w = 0`. So `α`, `β` and
`γ` are the continuous extensions of `A / D`, `B / D` and `G / D` from the dense set `{D ≠ 0}`.

Finally `p` is recovered from `α = p' / p` by one integration (`eq_mul_exp_integral`),
`p (x) = p (a) exp (∫ₐˣ α)`, and then `q = p β`, `w = p γ`. The constant `p (a)` is the free
scale of `solution_unique`.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral

namespace MathPhysicsTheory.SturmLiouville.InverseProblem

section Cramer

/-- The determinant of the `3 × 3` matrix whose row `n` is `(f n, g n, h n)`, `n = 0, 1, 2`. -/
def det₃ (f g h : ℕ → ℝ) : ℝ :=
  f (0) * (g (1) * h (2) - g (2) * h (1)) - g (0) * (f (1) * h (2) - f (2) * h (1)) +
    h (0) * (f (1) * g (2) - f (2) * g (1))

/-- Cramer's rule for the system `f n * α + g n * β + h n * γ = r n`, `n = 0, 1, 2`. -/
theorem det₃_cramer {f g h r : ℕ → ℝ} {α β γ : ℝ}
    (e : ∀ n, n < 3 → f (n) * α + g (n) * β + h (n) * γ = r (n)) :
    det₃ (f) (g) (h) * α = det₃ (r) (g) (h) ∧ det₃ (f) (g) (h) * β = det₃ (f) (r) (h) ∧
      det₃ (f) (g) (h) * γ = det₃ (f) (g) (r) := by
  have e0 := e (0) (by norm_num)
  have e1 := e (1) (by norm_num)
  have e2 := e (2) (by norm_num)
  refine ⟨?_, ?_, ?_⟩ <;> simp only [det₃]
  · linear_combination (g (1) * h (2) - g (2) * h (1)) * e0 - (g (0) * h (2) - g (2) * h (0)) * e1 +
      (g (0) * h (1) - g (1) * h (0)) * e2
  · linear_combination -(f (1) * h (2) - f (2) * h (1)) * e0 +
      (f (0) * h (2) - f (2) * h (0)) * e1 - (f (0) * h (1) - f (1) * h (0)) * e2
  · linear_combination (f (1) * g (2) - f (2) * g (1)) * e0 - (f (0) * g (2) - f (2) * g (0)) * e1 +
      (f (0) * g (1) - f (1) * g (0)) * e2

end Cramer

/-- The determinant of the system for `(p' / p, q / p, w / p)` at `x`: rows `(Xₙ', Xₙ, λₙ Xₙ)`
for `n = 0, 1, 2`. -/
noncomputable def fluxDet (lam : ℕ → ℝ) (X : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  det₃ (fun n => deriv (X (n)) (x)) (fun n => X (n) (x)) (fun n => lam (n) * X (n) (x))

/-- The numerator of `p' / p`: `fluxDet` with the column `Xₙ'` replaced by `-Xₙ''`. -/
noncomputable def alphaNum (lam : ℕ → ℝ) (X : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  det₃ (fun n => -deriv (deriv (X (n))) (x)) (fun n => X (n) (x)) (fun n => lam (n) * X (n) (x))

/-- The numerator of `q / p`: `fluxDet` with the column `Xₙ` replaced by `-Xₙ''`. -/
noncomputable def betaNum (lam : ℕ → ℝ) (X : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  det₃ (fun n => deriv (X (n)) (x)) (fun n => -deriv (deriv (X (n))) (x))
    (fun n => lam (n) * X (n) (x))

/-- The numerator of `w / p`: `fluxDet` with the column `λₙ Xₙ` replaced by `-Xₙ''`. -/
noncomputable def gammaNum (X : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  det₃ (fun n => deriv (X (n)) (x)) (fun n => X (n) (x)) (fun n => -deriv (deriv (X (n))) (x))

section Pointwise

variable {a b : ℝ} {L : Operator} {w : ℝ → ℝ} {l : ℝ} {y : ℝ → ℝ}
  {Ba Bb : BoundaryConditions.Robin.Operator}

/-- The expanded equation at an interior point: `p y'' + p' y' + (q + λ w) y = 0`. -/
theorem second_order (hA : SturmLiouville.Assumptions (a) (b) (L) (w) (Ba) (Bb))
    (h : L.IsSolution (a) (b) (w) (l) (y)) {x : ℝ} (hx : x ∈ Ioo (a) (b)) :
    L.p (x) * deriv (deriv (y)) (x) + deriv (L.p) (x) * deriv (y) (x) +
      (L.q (x) + l * w (x)) * y (x) = 0 := by
  have h2 : ContDiffOn (ℝ) (2) (y) (Ioo (a) (b)) := h.1.mono (Ioo_subset_Icc_self)
  have h3 : ContDiffOn (ℝ) (1) (deriv (y)) (Ioo (a) (b)) :=
    h2.deriv_of_isOpen (isOpen_Ioo) (by norm_num)
  have hy' : DifferentiableAt (ℝ) (deriv (y)) (x) :=
    (h3.contDiffAt (isOpen_Ioo.mem_nhds (hx))).differentiableAt (by norm_num)
  have H := ((differentiableAt_p (hA) (hx)).hasDerivAt).mul (hy'.hasDerivAt)
  have E := (solution_hasDerivAt (hA) (h) (hx)).2.unique (H)
  linarith

/-- **Reconstruction formulas.** If `(L, w)` has the eigenpairs `(λₙ, Xₙ)`, `n = 0, 1, 2`, and
`fluxDet ≠ 0` at an interior point `x`, then `p' / p`, `q / p` and `w / p` at `x` are the ratios of
the determinants `alphaNum`, `betaNum`, `gammaNum` to `fluxDet`. They are computed from the data
`λₙ, Xₙ` alone. -/
theorem reconstruction_formulas {lam : ℕ → ℝ} {X : ℕ → ℝ → ℝ}
    (hA : SturmLiouville.Assumptions (a) (b) (L) (w) (Ba) (Bb))
    (h : ∀ n, L.IsSolution (a) (b) (w) (lam (n)) (X (n))) {x : ℝ} (hx : x ∈ Ioo (a) (b))
    (hD : fluxDet (lam) (X) (x) ≠ 0) :
    deriv (L.p) (x) / L.p (x) = alphaNum (lam) (X) (x) / fluxDet (lam) (X) (x) ∧
      L.q (x) / L.p (x) = betaNum (lam) (X) (x) / fluxDet (lam) (X) (x) ∧
      w (x) / L.p (x) = gammaNum (X) (x) / fluxDet (lam) (X) (x) := by
  have hp : L.p (x) ≠ 0 := (hA.p_pos (x) (Ioo_subset_Icc_self (hx))).ne'
  have hα : L.p (x) * (deriv (L.p) (x) / L.p (x)) = deriv (L.p) (x) := by field_simp
  have hβ : L.p (x) * (L.q (x) / L.p (x)) = L.q (x) := by field_simp
  have hγ : L.p (x) * (w (x) / L.p (x)) = w (x) := by field_simp
  have e : ∀ n, n < 3 → deriv (X (n)) (x) * (deriv (L.p) (x) / L.p (x)) +
      X (n) (x) * (L.q (x) / L.p (x)) + lam (n) * X (n) (x) * (w (x) / L.p (x)) =
      -deriv (deriv (X (n))) (x) := by
    intro n _
    have h2 := second_order (hA) (h (n)) (hx)
    apply mul_left_cancel₀ (hp)
    linear_combination deriv (X (n)) (x) * hα + X (n) (x) * hβ + lam (n) * X (n) (x) * hγ + h2
  obtain ⟨c₁, c₂, c₃⟩ := det₃_cramer (e := e)
  refine ⟨?_, ?_, ?_⟩
  · exact eq_div_of_mul_eq (hD) (by rw [mul_comm]; exact c₁)
  · exact eq_div_of_mul_eq (hD) (by rw [mul_comm]; exact c₂)
  · exact eq_div_of_mul_eq (hD) (by rw [mul_comm]; exact c₃)

/-- A nonzero solution does not vanish identically on any subinterval `(u, v) ⊆ [a, b]`: otherwise
`y (x₁) = y' (x₁) = 0` at the midpoint and Cauchy uniqueness gives `y = 0`. -/
theorem exists_ne_zero_of_Ioo (hA : SturmLiouville.Assumptions (a) (b) (L) (w) (Ba) (Bb))
    (h : L.IsSolution (a) (b) (w) (l) (y)) (hne : ∃ x ∈ Icc (a) (b), y (x) ≠ 0) {u v : ℝ}
    (huv : u < v) (hu : a ≤ u) (hv : v ≤ b) : ∃ x ∈ Ioo (u) (v), y (x) ≠ 0 := by
  by_contra H
  have H' : ∀ x ∈ Ioo (u) (v), y (x) = 0 := fun x hx => by_contra (fun hx0 => H ⟨x, hx, hx0⟩)
  have hm : (u + v) / 2 ∈ Ioo (u) (v) := ⟨by linarith, by linarith⟩
  have hmab : (u + v) / 2 ∈ Ioo (a) (b) := ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have hy0 : y =ᶠ[nhds ((u + v) / 2)] fun _ => 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (hm)] with t ht using H' (t) (ht)
  obtain ⟨z, hz, hzne⟩ := hne
  exact hzne (eq_zero_of_cauchy (hA) (h) (hmab) (hy0.eq_of_nhds)
    (by rw [hy0.deriv_eq]; simp) (z) (hz))

/-- Inside a nonempty open set `J ⊆ (a, b)` there is a nonempty open subset on which the nonzero
solution `y` has no zeros. -/
theorem exists_open_ne_zero (hA : SturmLiouville.Assumptions (a) (b) (L) (w) (Ba) (Bb))
    (h : L.IsSolution (a) (b) (w) (l) (y)) (hne : ∃ x ∈ Icc (a) (b), y (x) ≠ 0) {J : Set (ℝ)}
    (hJo : IsOpen (J)) (hJI : J ⊆ Ioo (a) (b)) (hJne : J.Nonempty) :
    ∃ J' : Set (ℝ), IsOpen (J') ∧ J' ⊆ J ∧ J'.Nonempty ∧ ∀ x ∈ J', y (x) ≠ 0 := by
  obtain ⟨x₁, hx₁⟩ := hJne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hJo) (x₁) (hx₁)
  have hsub : Ioo (x₁ - ε / 2) (x₁ + ε / 2) ⊆ J := fun t ht =>
    hball (by rw [Real.ball_eq_Ioo]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hl : x₁ - ε / 2 ∈ Ioo (a) (b) := hJI (hball (by
    rw [Real.ball_eq_Ioo]; exact ⟨by linarith, by linarith⟩))
  have hr : x₁ + ε / 2 ∈ Ioo (a) (b) := hJI (hball (by
    rw [Real.ball_eq_Ioo]; exact ⟨by linarith, by linarith⟩))
  obtain ⟨x, hx, hxne⟩ := exists_ne_zero_of_Ioo (hA) (h) (hne) (u := x₁ - ε / 2) (v := x₁ + ε / 2)
    (by linarith) (hl.1.le) (hr.2.le)
  refine ⟨J ∩ y ⁻¹' {0}ᶜ, ?_, inter_subset_left, ⟨x, hsub (hx), hxne⟩, fun t ht => ht.2⟩
  exact (h.1.continuousOn.mono (hJI.trans (Ioo_subset_Icc_self))).isOpen_inter_preimage (hJo)
    (isOpen_compl_singleton)

/-- **The reconstruction determinant is not identically zero on any interval.** If `(L, w)` has
the eigenpairs `(λₙ, Xₙ)`, `n = 0, 1, 2`, with `λ₀ < λ₁ < λ₂` and each `Xₙ ≢ 0`, then `fluxDet`
has a nonzero value in every subinterval `(u, v) ⊆ [a, b]`. Hence `{fluxDet ≠ 0}` is dense in
`(a, b)` and the formulas of `reconstruction_formulas` determine `p' / p`, `q / p`, `w / p` by
continuity. -/
theorem exists_fluxDet_ne_zero {lam : ℕ → ℝ} {X : ℕ → ℝ → ℝ}
    (hA : SturmLiouville.Assumptions (a) (b) (L) (w) (Ba) (Bb)) (hlam : StrictMono (lam))
    (h : ∀ n, L.IsSolution (a) (b) (w) (lam (n)) (X (n)))
    (hne : ∀ n, ∃ x ∈ Icc (a) (b), X (n) (x) ≠ 0) {u v : ℝ} (huv : u < v) (hu : a ≤ u)
    (hv : v ≤ b) : ∃ x ∈ Ioo (u) (v), fluxDet (lam) (X) (x) ≠ 0 := by
  by_contra H
  have H' : ∀ x ∈ Ioo (u) (v), fluxDet (lam) (X) (x) = 0 := fun x hx =>
    by_contra (fun h0 => H ⟨x, hx, h0⟩)
  have hJ0 : Ioo (u) (v) ⊆ Ioo (a) (b) := Ioo_subset_Ioo (hu) (hv)
  obtain ⟨J₁, ho₁, hs₁, hn₁, hX₁⟩ := exists_open_ne_zero (hA) (h (0)) (hne (0)) (isOpen_Ioo)
    (hJ0) (nonempty_Ioo.2 (huv))
  obtain ⟨J₂, ho₂, hs₂, hn₂, hX₂⟩ := exists_open_ne_zero (hA) (h (1)) (hne (1)) (ho₁)
    (hs₁.trans (hJ0)) (hn₁)
  obtain ⟨U, hUo, hs₃, hUne, hX₃⟩ := exists_open_ne_zero (hA) (h (2)) (hne (2)) (ho₂)
    (hs₂.trans (hs₁.trans (hJ0))) (hn₂)
  have hUI : U ⊆ Ioo (a) (b) := hs₃.trans (hs₂.trans (hs₁.trans (hJ0)))
  have hXne : ∀ n, n < 3 → ∀ x ∈ U, X (n) (x) ≠ 0 := by
    intro n hn x hx
    interval_cases n
    · exact hX₁ (x) (hs₂ (hs₃ (hx)))
    · exact hX₂ (x) (hs₃ (hx))
    · exact hX₃ (x) (hx)
  set m : ℕ → ℝ → ℝ := fun n t => L.p (t) * deriv (X (n)) (t) / X (n) (t) with hm
  have hmd : ∀ n, n < 3 → ∀ x ∈ U, HasDerivAt (m (n))
      (-(L.q (x) + lam (n) * w (x)) - (m (n) (x)) ^ 2 / L.p (x)) (x) := fun n hn x hx =>
    hasDerivAt_ratio (hA) (h (n)) (hUI (hx)) (hXne (n) (hn) (x) (hx))
  have hprop : ∀ x ∈ U, (lam (1) - lam (0)) * (m (2) (x) - m (0) (x)) =
      (lam (2) - lam (0)) * (m (1) (x) - m (0) (x)) := by
    intro x hx
    have h0 := H' (x) (hs₃.trans (hs₂.trans (hs₁)) (hx))
    have x0 := hXne (0) (by norm_num) (x) (hx)
    have x1 := hXne (1) (by norm_num) (x) (hx)
    have x2 := hXne (2) (by norm_num) (x) (hx)
    have key : (lam (1) - lam (0)) * (m (2) (x) - m (0) (x)) -
        (lam (2) - lam (0)) * (m (1) (x) - m (0) (x)) =
        L.p (x) * fluxDet (lam) (X) (x) / (X (0) (x) * X (1) (x) * X (2) (x)) := by
      simp only [hm, fluxDet, det₃]
      field_simp
      ring
    rw [h0, mul_zero, zero_div] at key
    linarith
  exact false_of_collinear (hA) (hlam) (hUo) (hUI) (hUne) (m) (hmd) (hprop)

end Pointwise

section Integration

variable {a b : ℝ} {L : Operator} {w : ℝ → ℝ} {Ba Bb : BoundaryConditions.Robin.Operator}

/-- **Recovering `p` from `α = p' / p`.** For `p > 0` of class `C¹` on `[a, b]`,
`p (x) = p (a) exp (∫ₐˣ p' / p)`. Together with `q = p (q / p)` and `w = p (w / p)` this finishes
the reconstruction; the free constant `p (a)` is the scale of `solution_unique`. -/
theorem eq_mul_exp_integral (hA : SturmLiouville.Assumptions (a) (b) (L) (w) (Ba) (Bb))
    (hab : a < b) {x : ℝ} (hx : x ∈ Icc (a) (b)) :
    L.p (x) = L.p (a) * Real.exp (∫ t in a..x, deriv (L.p) (t) / L.p (t)) := by
  rcases hx.1.eq_or_lt with rfl | hax
  · simp
  have hpd : ContDiffOn (ℝ) (1) (L.p) (Icc (a) (b)) := hA.p_contDiffOn
  have hpos : ∀ t ∈ Icc (a) (b), 0 < L.p (t) := hA.p_pos
  have hxb : Icc (a) (x) ⊆ Icc (a) (b) := Icc_subset_Icc_right (hx.2)
  set g : ℝ → ℝ := fun t => derivWithin (L.p) (Icc (a) (b)) (t) / L.p (t) with hg
  have hgc : ContinuousOn (g) (Icc (a) (b)) :=
    (hpd.continuousOn_derivWithin (uniqueDiffOn_Icc (hab)) (le_rfl)).div (hpd.continuousOn)
      (fun t ht => (hpos (t) (ht)).ne')
  have hint : ∫ t in a..x, deriv (L.p) (t) / L.p (t) = ∫ t in a..x, g (t) := by
    rw [intervalIntegral.integral_of_le (hax.le), intervalIntegral.integral_of_le (hax.le),
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun (measurableSet_Ioo) (fun t ht => ?_)
    have htab : t ∈ Ioo (a) (b) := ⟨ht.1, ht.2.trans_le (hx.2)⟩
    simp only [hg]
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds (htab.1) (htab.2))]
  have hftc : ∫ t in a..x, g (t) = Real.log (L.p (x)) - Real.log (L.p (a)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun t => Real.log (L.p (t)))
      (hax.le) (?_) (?_) (?_)
    · exact ContinuousOn.log (hpd.continuousOn.mono (hxb))
        (fun t ht => (hpos (t) (hxb (ht))).ne')
    · intro t ht
      have htab : t ∈ Ioo (a) (b) := ⟨ht.1, ht.2.trans_le (hx.2)⟩
      have hpt : L.p (t) ≠ 0 := (hpos (t) (Ioo_subset_Icc_self (htab))).ne'
      have := (differentiableAt_p (hA) (htab)).hasDerivAt.log (hpt)
      simpa [hg, derivWithin_of_mem_nhds (Icc_mem_nhds (htab.1) (htab.2))] using this
    · exact (hgc.mono (hxb)).intervalIntegrable_of_Icc (hax.le)
  have hpa : 0 < L.p (a) := hpos (a) ⟨le_rfl, hab.le⟩
  rw [hint, hftc, Real.exp_sub, Real.exp_log (hpos (x) (hx)), Real.exp_log (hpa)]
  field_simp

end Integration

section Problem

variable (I : InverseProblem)

/-- The data of an inverse problem: `λₙ` is strictly increasing. -/
theorem strictMono_lam : StrictMono (I.«λₙ») := by
  obtain ⟨P, -, -, -, -, hev, -⟩ := I.assumptions.exists_problem
  rw [hev]
  exact (Classical.choose_spec (Eigenvalues.exists_eigenvalue_seq (P))).1

/-- Every solution of the inverse problem solves the equation for each given eigenpair. -/
theorem IsSolution.isSolution_eigenpair {L : Operator} {w : ℝ → ℝ} (h : I.IsSolution (L) (w))
    (n : ℕ) : L.IsSolution (I.a) (I.b) (w) (I.«λₙ» (n)) (I.Xₙ (n)) := by
  obtain ⟨P, ha, hb, -, -, -, hP⟩ := I.assumptions.exists_problem
  refine ⟨?_, fun x hx => ?_⟩
  · have := (hP (n)).1.1.1
    rwa [ha, hb] at this
  · have := h.2 (n) (x) (hx)
    linear_combination this

/-- Each given eigenfunction is nonzero somewhere on `[a, b]`. -/
theorem Xₙ_ne_zero (n : ℕ) : ∃ x ∈ Icc (I.a) (I.b), I.Xₙ (n) (x) ≠ 0 := by
  obtain ⟨P, ha, hb, -, -, -, hP⟩ := I.assumptions.exists_problem
  have := (hP (n)).2
  rwa [ha, hb] at this

variable {I}

/-- **The reconstruction formulas for an inverse problem.** A solution `(p, q, w)` is given at
every interior point where `fluxDet ≠ 0` by the three eigenpairs `n = 0, 1, 2` alone:
`p' / p = alphaNum / fluxDet`, `q / p = betaNum / fluxDet`, `w / p = gammaNum / fluxDet`. -/
theorem IsSolution.reconstruction_formulas {L : Operator} {w : ℝ → ℝ} (h : I.IsSolution (L) (w))
    {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) (hD : fluxDet (I.«λₙ») (I.Xₙ) (x) ≠ 0) :
    deriv (L.p) (x) / L.p (x) = alphaNum (I.«λₙ») (I.Xₙ) (x) / fluxDet (I.«λₙ») (I.Xₙ) (x) ∧
      L.q (x) / L.p (x) = betaNum (I.«λₙ») (I.Xₙ) (x) / fluxDet (I.«λₙ») (I.Xₙ) (x) ∧
      w (x) / L.p (x) = gammaNum (I.Xₙ) (x) / fluxDet (I.«λₙ») (I.Xₙ) (x) :=
  InverseProblem.reconstruction_formulas (h.1) (h.isSolution_eigenpair) (hx) (hD)

/-- `fluxDet` of an inverse problem has a nonzero value in every subinterval of `[a, b]`, so
`{fluxDet ≠ 0}` is dense in `(a, b)`. -/
theorem IsSolution.exists_fluxDet_ne_zero {L : Operator} {w : ℝ → ℝ} (h : I.IsSolution (L) (w))
    {u v : ℝ} (huv : u < v) (hu : I.a ≤ u) (hv : v ≤ I.b) :
    ∃ x ∈ Ioo (u) (v), fluxDet (I.«λₙ») (I.Xₙ) (x) ≠ 0 :=
  InverseProblem.exists_fluxDet_ne_zero (h.1) (strictMono_lam (I)) (h.isSolution_eigenpair)
    (Xₙ_ne_zero (I)) (huv) (hu) (hv)

end Problem

end MathPhysicsTheory.SturmLiouville.InverseProblem

end
