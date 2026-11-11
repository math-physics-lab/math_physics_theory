module

public import Mathlib
public import MathPhysicsTheory.SturmLiouville.InverseProblem.Basic

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# A solution method for the inverse Sturm-Liouville problem

Statements and proofs for the solution method described in `InverseProblem/Basic/NOTE.md`.
Steps 1 to 6 are proved. Every `sorry` below (steps 7 to 9) is a lemma still to be proved.

Given the eigenpairs `(λₙ, Xₙ)` of an inverse problem `I`, the method finds `(p, q, w)` using only
three of them, `n = e 0 < e 1 < e 2`. They need not be the first three: `e : Fin 3 → ℕ` is any
strictly increasing choice of indices (`StrictMono (e)`), and the first three are `e = id`.
Any three distinct indices can be reduced to this case by reordering the rows of `M`, which
changes `D` only by a sign. For a solution `(L, w)` write `α = p'/p`, `β = q/p`, `γ = w/p`.

* **Step 1** (`expand`): `p Xₙ'' + p' Xₙ' + q Xₙ + λₙ w Xₙ = 0`.
* **Step 2** (`linear_equation`): `Xₙ'' + α Xₙ' + β Xₙ + λₙ γ Xₙ = 0`, linear in `(α, β, γ)`.
* **Step 3** (`coeffMatrix_mulVec`): `M(x) (α, β, γ)ᵀ = r(x)` for `n = e 0, e 1, e 2`.
* **Step 4** (`α_eq_cramer`, `β_eq_cramer`, `γ_eq_cramer`): `(α, β, γ) = (A, B, G) / D`
  where `D = det M ≠ 0`.
* **Step 5** (`closure_regularSet`, `ratioLimit_zero_eq`, `ratioLimit_one_eq`,
  `ratioLimit_two_eq`): `{D ≠ 0}` is dense in `(a, b)`, and
  `(α, β, γ)` is the limit of `(A, B, G) / D` along it.
* **Step 6** (`pRec_eq`): `p = p(a) exp ∫ₐˣ α`.
* **Step 7** (`qRec_eq`, `wRec_eq`): `q = p β`, `w = p γ`.
* **Step 8** (`check_eigenpair`): every further eigenpair satisfies the linear equation with the
  recovered `(α, β, γ)`.
* **Step 9** (`recSolution_isSolution`, `eq_recSolution`): the recovered triple, normalised by
  `p(a) = 1`, is a solution, and it is the unique normalised one.

The recovered functions `pRec`, `qRec`, `wRec` are defined from the data `(λₙ, Xₙ)` alone.
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace MathPhysicsTheory.SturmLiouville.InverseProblem

namespace SolutionMethod

variable (I : InverseProblem) (e : Fin (3) → ℕ)

/-! ### Definitions: the data of the method -/

/-- The matrix `M (x)` of step 3: row `i` is `(Xₙ' (x), Xₙ (x), λₙ Xₙ (x))` for `n = e i`, where
`e : Fin 3 → ℕ` selects the three eigenpairs used. -/
noncomputable def coeffMatrix (x : ℝ) : Matrix (Fin (3)) (Fin (3)) (ℝ) :=
  Matrix.of (fun i =>
    ![deriv (I.Xₙ (e (i))) (x), I.Xₙ (e (i)) (x), I.«λₙ» (e (i)) * I.Xₙ (e (i)) (x)])

/-- The right-hand side `r (x)` of step 3: row `i` is `-Xₙ'' (x)` for `n = e i`. -/
noncomputable def rhs (x : ℝ) : Fin (3) → (ℝ) :=
  fun i => -deriv (deriv (I.Xₙ (e (i)))) (x)

/-- The determinant `D (x) = det M (x)`. -/
noncomputable def D (x : ℝ) : ℝ :=
  (coeffMatrix (I) (e) (x)).det

/-- The numerators of Cramer's rule: `cramerNum 0 = A`, `cramerNum 1 = B`, `cramerNum 2 = G`, that
is `D` with the `k`-th column replaced by `r`. -/
noncomputable def cramerNum (k : Fin (3)) (x : ℝ) : ℝ :=
  Matrix.cramer (coeffMatrix (I) (e) (x)) (rhs (I) (e) (x)) (k)

/-- The points of `(a, b)` where `D ≠ 0`. -/
def regularSet : Set (ℝ) :=
  {x | x ∈ Ioo (I.a) (I.b) ∧ D (I) (e) (x) ≠ 0}

/-- The value at `x` of the limit of `cramerNum k / D` along the points where `D ≠ 0` (step 5).
It is `α` for `k = 0`, `β` for `k = 1` and `γ` for `k = 2`. -/
noncomputable def ratioLimit (k : Fin (3)) (x : ℝ) : ℝ :=
  limUnder (𝓝[regularSet (I) (e)] (x)) (fun y => cramerNum (I) (e) (k) (y) / D (I) (e) (y))

/-- The recovered `p`, normalised by `p (a) = 1` (step 6): `p = exp ∫ₐˣ α`. -/
noncomputable def pRec (x : ℝ) : ℝ :=
  Real.exp (∫ t in I.a..x, ratioLimit (I) (e) (0) (t))

/-- The recovered `q = p β` (step 7). -/
noncomputable def qRec (x : ℝ) : ℝ :=
  pRec (I) (e) (x) * ratioLimit (I) (e) (1) (x)

/-- The recovered weight `w = p γ` (step 7). -/
noncomputable def wRec (x : ℝ) : ℝ :=
  pRec (I) (e) (x) * ratioLimit (I) (e) (2) (x)

/-- The recovered operator `L y = (pRec y')' + qRec y`. -/
noncomputable def recOperator : Operator :=
  { p := pRec (I) (e), q := qRec (I) (e) }

/-- `α = p'/p` (step 2). -/
noncomputable def α (L : Operator) (x : ℝ) : ℝ :=
  deriv (L.p) (x) / L.p (x)

/-- `β = q/p` (step 2). -/
noncomputable def β (L : Operator) (x : ℝ) : ℝ :=
  L.q (x) / L.p (x)

/-- `γ = w/p` (step 2). -/
noncomputable def γ (L : Operator) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  w (x) / L.p (x)

variable {I} {e}
variable {L : Operator} {w : ℝ → ℝ}

/-! ### Step 1: expand the operator -/

/-- Step 1. At interior points `(p Xₙ')' = p Xₙ'' + p' Xₙ'`, so
`p Xₙ'' + p' Xₙ' + q Xₙ + λₙ w Xₙ = 0`. -/
lemma expand (hS : I.IsSolution (L) (w)) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) :
    L.p (x) * deriv (deriv (I.Xₙ (n))) (x) + deriv (L.p) (x) * deriv (I.Xₙ (n)) (x) +
      L.q (x) * I.Xₙ (n) (x) + I.«λₙ» (n) * w (x) * I.Xₙ (n) (x) = 0 := by
  have hp : DifferentiableAt (ℝ) (L.p) (x) := differentiableAt_p (hS.1) (hx)
  -- The given eigenfunctions are `C²` on `[a, b]`.
  have hC : ContDiffOn (ℝ) (2) (I.Xₙ (n)) (Icc (I.a) (I.b)) := by
    obtain ⟨P, ha, hb, -, -, -, hP⟩ := I.assumptions.exists_problem
    have := (hP (n)).1.1.1
    rwa [ha, hb] at this
  -- The derivative of an eigenfunction is differentiable at interior points.
  have hd : DifferentiableAt (ℝ) (deriv (I.Xₙ (n))) (x) := by
    have h2 : ContDiffOn (ℝ) (2) (I.Xₙ (n)) (Ioo (I.a) (I.b)) :=
      hC.mono (Ioo_subset_Icc_self)
    have h3 : ContDiffOn (ℝ) (1) (deriv (I.Xₙ (n))) (Ioo (I.a) (I.b)) :=
      h2.deriv_of_isOpen (isOpen_Ioo) (by norm_num)
    exact (h3.contDiffAt (isOpen_Ioo.mem_nhds (hx))).differentiableAt (by norm_num)
  have h : HasDerivAt (fun t => L.p (t) * deriv (I.Xₙ (n)) (t))
      (deriv (L.p) (x) * deriv (I.Xₙ (n)) (x) + L.p (x) * deriv (deriv (I.Xₙ (n))) (x)) (x) :=
    hp.hasDerivAt.mul hd.hasDerivAt
  have := hS.2 (n) (x) (Ioo_subset_Icc_self (hx))
  simp only [Operator.apply, h.deriv] at this
  linear_combination this

/-! ### Step 2: divide by `p` and rename the unknowns -/

/-- Step 2. With `α = p'/p`, `β = q/p`, `γ = w/p`, for every `n` and interior `x`:
`Xₙ'' + α Xₙ' + β Xₙ + λₙ γ Xₙ = 0`. For fixed `x` this is linear in `(α, β, γ)`. -/
lemma linear_equation (hS : I.IsSolution (L) (w)) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) :
    deriv (deriv (I.Xₙ (n))) (x) + α (L) (x) * deriv (I.Xₙ (n)) (x) +
      β (L) (x) * I.Xₙ (n) (x) + I.«λₙ» (n) * γ (L) (w) (x) * I.Xₙ (n) (x) = 0 := by
  have hp : L.p (x) ≠ 0 := (hS.1.p_pos (x) (Ioo_subset_Icc_self (hx))).ne'
  have h := expand (hS) (n) (hx)
  simp only [α, β, γ]
  field_simp
  linear_combination h

/-! ### Step 3: three eigenpairs give a linear system -/

/-- Step 3. For `n = e 0, e 1, e 2` the equations of step 2 form the system
`M (x) (α, β, γ)ᵀ = r (x)`. -/
lemma coeffMatrix_mulVec (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) :
    (coeffMatrix (I) (e) (x)).mulVec ![α (L) (x), β (L) (x), γ (L) (w) (x)] =
      rhs (I) (e) (x) := by
  ext i
  have h := linear_equation (hS) (e (i)) (hx)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, coeffMatrix, rhs]
  linear_combination h

/-! ### Step 4: Cramer's rule -/

/-- If `A x = b`, then the `k`-th Cramer numerator `det (A with column k replaced by b)` equals
`det A * x k`. -/
lemma cramer_eq_det_mul {A : Matrix (Fin (3)) (Fin (3)) (ℝ)} {x b : Fin (3) → (ℝ)}
    (h : A.mulVec (x) = b) (k : Fin (3)) : Matrix.cramer (A) (b) (k) = A.det * x (k) := by
  rw [Matrix.cramer_eq_adjugate_mulVec, ← h, Matrix.mulVec_mulVec, Matrix.adjugate_mul]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

/-- Step 4. Wherever `D (x) ≠ 0`, `(α, β, γ) = (A, B, G) / D`. This is a necessary condition on
every solution. -/
lemma α_eq_cramer (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b))
    (hD : D (I) (e) (x) ≠ 0) : α (L) (x) = cramerNum (I) (e) (0) (x) / D (I) (e) (x) := by
  have h := cramer_eq_det_mul (coeffMatrix_mulVec (e := e) (hS) (hx)) (0)
  rw [eq_div_iff (hD)]
  simp only [cramerNum, D, h]
  simp
  ring

/-- Step 4, for `β`. -/
lemma β_eq_cramer (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b))
    (hD : D (I) (e) (x) ≠ 0) : β (L) (x) = cramerNum (I) (e) (1) (x) / D (I) (e) (x) := by
  have h := cramer_eq_det_mul (coeffMatrix_mulVec (e := e) (hS) (hx)) (1)
  rw [eq_div_iff (hD)]
  simp only [cramerNum, D, h]
  simp
  ring

/-- Step 4, for `γ`. -/
lemma γ_eq_cramer (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b))
    (hD : D (I) (e) (x) ≠ 0) : γ (L) (w) (x) = cramerNum (I) (e) (2) (x) / D (I) (e) (x) := by
  have h := cramer_eq_det_mul (coeffMatrix_mulVec (e := e) (hS) (hx)) (2)
  rw [eq_div_iff (hD)]
  simp only [cramerNum, D, h]
  simp
  ring

/-! ### Step 5: `D ≠ 0` on a dense set -/

/-- Step 5 (the key lemma). `D` does not vanish on any subinterval of `(a, b)`. -/
lemma exists_D_ne_zero (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {c d : ℝ} (hcd : c < d)
    (hsub : Ioo (c) (d) ⊆ Ioo (I.a) (I.b)) : ∃ x ∈ Ioo (c) (d), D (I) (e) (x) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  -- the given eigenvalues are strictly increasing
  have hl : StrictMono (I.«λₙ») := by
    obtain ⟨P, -, -, -, -, hev, -⟩ := I.assumptions.exists_problem
    rw [hev]
    exact (Classical.choose_spec (Eigenvalues.exists_eigenvalue_seq (P))).1
  have hsubI : ∀ n, ContinuousOn (I.Xₙ (n)) (Ioo (I.a) (I.b)) := fun n =>
    ((contDiffOn_Xₙ (I) (n)).continuousOn).mono (Ioo_subset_Icc_self)
  -- `Xₙ` solves the equation `L y = -λₙ w y` for the operator of a solution
  have hsol : ∀ n, L.IsSolution (I.a) (I.b) (w) (I.«λₙ» (n)) (I.Xₙ (n)) := fun n =>
    ⟨contDiffOn_Xₙ (I) (n), fun x hx => by
      have := hS.2 (n) (x) (hx)
      linear_combination this⟩
  -- shrink to an open set on which a given eigenfunction does not vanish
  have step : ∀ (n : ℕ) (U : Set (ℝ)), IsOpen (U) → U ⊆ Ioo (I.a) (I.b) → U.Nonempty →
      ∃ U' ⊆ U, IsOpen (U') ∧ U'.Nonempty ∧ ∀ x ∈ U', I.Xₙ (n) (x) ≠ 0 := by
    intro n U hU hUsub hne
    -- an eigenfunction cannot vanish on a nonempty open subset of `(a, b)` (Cauchy uniqueness)
    have hex : ∃ x ∈ U, I.Xₙ (n) (x) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨x₀, hx₀⟩ := hne
      have hev : I.Xₙ (n) =ᶠ[𝓝 (x₀)] fun _ => 0 := by
        filter_upwards [hU.mem_nhds (hx₀)] with t ht using hcon (t) (ht)
      have h1 : deriv (I.Xₙ (n)) (x₀) = 0 := by rw [hev.deriv_eq]; simp
      -- every given eigenfunction is nonzero somewhere on `[a, b]`
      obtain ⟨z, hz, hzne⟩ : ∃ z ∈ Icc (I.a) (I.b), I.Xₙ (n) (z) ≠ 0 := by
        obtain ⟨P, ha, hb, -, -, -, hP⟩ := I.assumptions.exists_problem
        have := (hP (n)).2
        rwa [ha, hb] at this
      exact hzne (eq_zero_of_cauchy (hS.1) (hsol (n)) (hUsub (hx₀)) (hev.eq_of_nhds) (h1) (z)
        (hz))
    obtain ⟨x, hxU, hxne⟩ := hex
    refine ⟨U ∩ I.Xₙ (n) ⁻¹' {0}ᶜ, inter_subset_left, ?_, ⟨x, hxU, hxne⟩, fun t ht => ht.2⟩
    exact ((hsubI (n)).mono (hUsub)).isOpen_inter_preimage (hU) (isOpen_compl_singleton)
  have h0 : Ioo (c) (d) ⊆ Ioo (I.a) (I.b) := hsub
  obtain ⟨U1, hU1, hU1o, hU1n, hU1ne⟩ :=
    step (e (0)) (Ioo (c) (d)) (isOpen_Ioo) (h0) (nonempty_Ioo.mpr (hcd))
  obtain ⟨U2, hU2, hU2o, hU2n, hU2ne⟩ :=
    step (e (1)) (U1) (hU1o) (hU1.trans (h0)) (hU1n)
  obtain ⟨W, hW, hWo, hWn, hWne⟩ :=
    step (e (2)) (U2) (hU2o) ((hU2.trans (hU1)).trans (h0)) (hU2n)
  have hW1 : W ⊆ U1 := hW.trans (hU2)
  have hWcd : W ⊆ Ioo (c) (d) := hW1.trans (hU1)
  have hWab : W ⊆ Ioo (I.a) (I.b) := hWcd.trans (h0)
  have hY : ∀ x ∈ W, ∀ i : Fin (3), I.Xₙ (e (i)) (x) ≠ 0 := by
    intro x hx i
    fin_cases i
    · exact hU1ne (x) (hW1 (hx))
    · exact hU2ne (x) (hW (hx))
    · exact hWne (x) (hx)
  set l : Fin (3) → ℝ := fun i => I.«λₙ» (e (i)) with hldef
  have hl01 : l (0) < l (1) := hl (he (by decide))
  have hl12 : l (1) < l (2) := hl (he (by decide))
  set m : Fin (3) → ℝ → ℝ := fun i t => L.p (t) * deriv (I.Xₙ (e (i))) (t) / I.Xₙ (e (i)) (t)
    with hm
  have hp : ∀ x ∈ W, 0 < L.p (x) := fun x hx =>
    hS.1.p_pos (x) (Ioo_subset_Icc_self (hWab (hx)))
  have hmd : ∀ i, ∀ x ∈ W, HasDerivAt (m (i))
      (-(L.q (x) + l (i) * w (x)) - (m (i) (x)) ^ 2 / L.p (x)) (x) := fun i x hx =>
    hasDerivAt_ratio (hS.1) (hsol (e (i))) (hWab (hx)) (hY (x) (hx) (i))
  have hprop : ∀ x ∈ W,
      (l (1) - l (0)) * (m (2) (x) - m (0) (x)) = (l (2) - l (0)) * (m (1) (x) - m (0) (x)) := by
    intro x hx
    have hZ : ∀ i, deriv (I.Xₙ (e (i))) (x) = m (i) (x) * I.Xₙ (e (i)) (x) / L.p (x) := by
      intro i
      have := hY (x) (hx) (i)
      have := (hp (x) (hx)).ne'
      simp only [hm]
      field_simp
    have hDx : D (I) (e) (x) =
        I.Xₙ (e (0)) (x) * I.Xₙ (e (1)) (x) * I.Xₙ (e (2)) (x) / L.p (x) *
        ((l (1) - l (0)) * (m (2) (x) - m (0) (x)) -
          (l (2) - l (0)) * (m (1) (x) - m (0) (x))) := by
      have := (hp (x) (hx)).ne'
      simp only [D, coeffMatrix, Matrix.det_fin_three, hldef]
      simp [hZ]
      field_simp
      ring
    have hD0 : D (I) (e) (x) = 0 := hcon (x) (hWcd (hx))
    rw [hDx] at hD0
    have h1 := hY (x) (hx) (0)
    have h2 := hY (x) (hx) (1)
    have h3 := hY (x) (hx) (2)
    have h4 := (hp (x) (hx)).ne'
    have : (l (1) - l (0)) * (m (2) (x) - m (0) (x)) -
        (l (2) - l (0)) * (m (1) (x) - m (0) (x)) = 0 := by
      rcases mul_eq_zero.mp (hD0) with h | h
      · simp [h1, h2, h3, h4] at h
      · exact h
    linarith
  have hd1 : ∀ x ∈ W, m (1) (x) = m (0) (x) := by
    intro x hx
    have H1 : HasDerivAt (fun t => (l (1) - l (0)) * (m (2) (t) - m (0) (t)))
        ((l (1) - l (0)) * ((-(L.q (x) + l (2) * w (x)) - (m (2) (x)) ^ 2 / L.p (x)) -
          (-(L.q (x) + l (0) * w (x)) - (m (0) (x)) ^ 2 / L.p (x)))) (x) :=
      ((hmd (2) (x) (hx)).sub (hmd (0) (x) (hx))).const_mul (_)
    have H2 : HasDerivAt (fun t => (l (2) - l (0)) * (m (1) (t) - m (0) (t)))
        ((l (2) - l (0)) * ((-(L.q (x) + l (1) * w (x)) - (m (1) (x)) ^ 2 / L.p (x)) -
          (-(L.q (x) + l (0) * w (x)) - (m (0) (x)) ^ 2 / L.p (x)))) (x) :=
      ((hmd (1) (x) (hx)).sub (hmd (0) (x) (hx))).const_mul (_)
    have hev : (fun t => (l (1) - l (0)) * (m (2) (t) - m (0) (t))) =ᶠ[𝓝 (x)]
        (fun t => (l (2) - l (0)) * (m (1) (t) - m (0) (t))) := by
      filter_upwards [hWo.mem_nhds (hx)] with t ht using hprop (t) (ht)
    have E := H1.unique (H2.congr_of_eventuallyEq (hev))
    exact ratio_algebra (hp (x) (hx)) (hl01) (hl12) (hprop (x) (hx)) (E)
  obtain ⟨x₀, hx₀⟩ := hWn
  have H3 : HasDerivAt (fun t => m (1) (t) - m (0) (t))
      ((-(L.q (x₀) + l (1) * w (x₀)) - (m (1) (x₀)) ^ 2 / L.p (x₀)) -
        (-(L.q (x₀) + l (0) * w (x₀)) - (m (0) (x₀)) ^ 2 / L.p (x₀))) (x₀) :=
    (hmd (1) (x₀) (hx₀)).sub (hmd (0) (x₀) (hx₀))
  have hev0 : (fun t => m (1) (t) - m (0) (t)) =ᶠ[𝓝 (x₀)] fun _ => 0 := by
    filter_upwards [hWo.mem_nhds (hx₀)] with t ht
    simp [hd1 (t) (ht)]
  have H4 := H3.unique ((hasDerivAt_const (x₀) (0 : ℝ)).congr_of_eventuallyEq (hev0))
  rw [hd1 (x₀) (hx₀)] at H4
  have hw := (hS.1.w_pos (x₀) (Ioo_subset_Icc_self (hWab (hx₀)))).ne'
  have hl' : l (1) - l (0) ≠ 0 := (sub_pos.mpr (hl01)).ne'
  have : (l (1) - l (0)) * w (x₀) = 0 := by linarith
  exact (mul_ne_zero (hl') (hw)) (this)

/-- Step 5. The set `{D ≠ 0}` is dense in `(a, b)`. -/
lemma closure_regularSet (he : StrictMono (e)) :
    Ioo (I.a) (I.b) ⊆ closure (regularSet (I) (e)) := by
  obtain ⟨L, w, hS⟩ := I.exists_solution
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hcd : max (x - ε) (I.a) < min (x + ε) (I.b) := by
    simp only [max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hx.1, hx.2]
  obtain ⟨y, hy, hDy⟩ := exists_D_ne_zero (hS) (he) (hcd) (fun t ht =>
    ⟨(le_max_right (x - ε) (I.a)).trans_lt (ht.1),
      (ht.2).trans_le (min_le_right (x + ε) (I.b))⟩)
  refine ⟨y, ⟨⟨(le_max_right (x - ε) (I.a)).trans_lt (hy.1),
    (hy.2).trans_le (min_le_right (x + ε) (I.b))⟩, hDy⟩, ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [(hy.2).trans_le (min_le_left (x + ε) (I.b))]
  · linarith [(le_max_left (x - ε) (I.a)).trans_lt (hy.1)]

/-- The closure of the regular set contains the closed interval `[a, b]`. -/
lemma Icc_subset_closure_regularSet (he : StrictMono (e)) :
    Icc (I.a) (I.b) ⊆ closure (regularSet (I) (e)) := by
  rw [← closure_Ioo (I.a_lt_b.ne)]
  calc closure (Ioo (I.a) (I.b)) ⊆ closure (closure (regularSet (I) (e))) :=
        closure_mono (closure_regularSet (he))
    _ = closure (regularSet (I) (e)) := closure_closure

/-- If `g` agrees with `A / D` on the regular set and is continuous within `[a, b]` at `x`, then
`A / D → g x` along the regular set. -/
lemma tendsto_of_eq_cramer (k : Fin (3)) {g : ℝ → ℝ}
    (hg : ∀ y ∈ regularSet (I) (e), g (y) = cramerNum (I) (e) (k) (y) / D (I) (e) (y)) {x : ℝ}
    (hc : ContinuousWithinAt (g) (Icc (I.a) (I.b)) (x)) :
    Tendsto (fun y => cramerNum (I) (e) (k) (y) / D (I) (e) (y))
      (𝓝[regularSet (I) (e)] (x)) (𝓝 (g (x))) := by
  -- `regularSet` lies in `[a, b]`
  have hsub : regularSet (I) (e) ⊆ Icc (I.a) (I.b) := fun _ hx => Ioo_subset_Icc_self (hx.1)
  have h : Tendsto (g) (𝓝[regularSet (I) (e)] (x)) (𝓝 (g (x))) :=
    (hc.mono (hsub)).tendsto
  refine h.congr' (?_)
  filter_upwards [self_mem_nhdsWithin] with y hy using hg (y) (hy)

/-- Step 5. At every interior point, `α` is the limit of `A / D` along the points where
`D ≠ 0`. -/
lemma tendsto_α (hS : I.IsSolution (L) (w)) {x : ℝ}
    (hx : x ∈ Ioo (I.a) (I.b)) :
    Tendsto (fun y => cramerNum (I) (e) (0) (y) / D (I) (e) (y))
      (𝓝[regularSet (I) (e)] (x)) (𝓝 (α (L) (x))) := by
  -- `α = p'/p` is continuous at interior points
  have hc : ContinuousWithinAt (α (L)) (Icc (I.a) (I.b)) (x) := by
    have hcd : ContDiffOn (ℝ) (1) (L.p) (Ioo (I.a) (I.b)) :=
      hS.1.p_contDiffOn.mono (Ioo_subset_Icc_self)
    have h1 : ContinuousOn (deriv (L.p)) (Ioo (I.a) (I.b)) :=
      hcd.continuousOn_deriv_of_isOpen (isOpen_Ioo) (le_rfl)
    have h2 : ContinuousAt (L.p) (x) := (differentiableAt_p (hS.1) (hx)).continuousAt
    exact ((h1.continuousAt (isOpen_Ioo.mem_nhds (hx))).div (h2)
      ((hS.1.p_pos (x) (Ioo_subset_Icc_self (hx))).ne')).continuousWithinAt
  exact tendsto_of_eq_cramer (0) (fun y hy => α_eq_cramer (hS) (hy.1) (hy.2)) (hc)

/-- Step 5, for `β` and `B / D`. -/
lemma tendsto_β (hS : I.IsSolution (L) (w)) {x : ℝ}
    (hx : x ∈ Ioo (I.a) (I.b)) :
    Tendsto (fun y => cramerNum (I) (e) (1) (y) / D (I) (e) (y))
      (𝓝[regularSet (I) (e)] (x)) (𝓝 (β (L) (x))) := by
  -- `β = q/p` is continuous on `[a, b]`
  have hc : ContinuousOn (β (L)) (Icc (I.a) (I.b)) :=
    hS.1.q_continuousOn.div (hS.1.p_contDiffOn.continuousOn)
      (fun x hx => (hS.1.p_pos (x) (hx)).ne')
  exact tendsto_of_eq_cramer (1) (fun y hy => β_eq_cramer (hS) (hy.1) (hy.2))
    (hc (x) (Ioo_subset_Icc_self (hx)))

/-- Step 5, for `γ` and `G / D`. -/
lemma tendsto_γ (hS : I.IsSolution (L) (w)) {x : ℝ}
    (hx : x ∈ Ioo (I.a) (I.b)) :
    Tendsto (fun y => cramerNum (I) (e) (2) (y) / D (I) (e) (y))
      (𝓝[regularSet (I) (e)] (x)) (𝓝 (γ (L) (w) (x))) := by
  -- `γ = w/p` is continuous on `[a, b]`
  have hc : ContinuousOn (γ (L) (w)) (Icc (I.a) (I.b)) :=
    hS.1.w_continuousOn.div (hS.1.p_contDiffOn.continuousOn)
      (fun x hx => (hS.1.p_pos (x) (hx)).ne')
  exact tendsto_of_eq_cramer (2) (fun y hy => γ_eq_cramer (hS) (hy.1) (hy.2))
    (hc (x) (Ioo_subset_Icc_self (hx)))

/-- Step 5. Hence `ratioLimit 0` recovers `α` at interior points. -/
lemma ratioLimit_zero_eq (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Ioo (I.a) (I.b)) : ratioLimit (I) (e) (0) (x) = α (L) (x) := by
  have hne : NeBot (𝓝[regularSet (I) (e)] (x)) :=
    mem_closure_iff_nhdsWithin_neBot.mp (closure_regularSet (he) (hx))
  exact (tendsto_α (hS) (hx)).limUnder_eq

/-- Step 5. Hence `ratioLimit 1` recovers `β`, also at the endpoints: `β = q/p` is continuous
on all of `[a, b]`. -/
lemma ratioLimit_one_eq (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Icc (I.a) (I.b)) : ratioLimit (I) (e) (1) (x) = β (L) (x) := by
  have hne : NeBot (𝓝[regularSet (I) (e)] (x)) :=
    mem_closure_iff_nhdsWithin_neBot.mp (Icc_subset_closure_regularSet (he) (hx))
  -- `β = q/p` is continuous on `[a, b]`
  have hc : ContinuousOn (β (L)) (Icc (I.a) (I.b)) :=
    hS.1.q_continuousOn.div (hS.1.p_contDiffOn.continuousOn)
      (fun x hx => (hS.1.p_pos (x) (hx)).ne')
  exact (tendsto_of_eq_cramer (1) (fun y hy => β_eq_cramer (hS) (hy.1) (hy.2))
    (hc (x) (hx))).limUnder_eq

/-- Step 5. Hence `ratioLimit 2` recovers `γ`, also at the endpoints: `γ = w/p` is continuous
on all of `[a, b]`. -/
lemma ratioLimit_two_eq (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Icc (I.a) (I.b)) : ratioLimit (I) (e) (2) (x) = γ (L) (w) (x) := by
  have hne : NeBot (𝓝[regularSet (I) (e)] (x)) :=
    mem_closure_iff_nhdsWithin_neBot.mp (Icc_subset_closure_regularSet (he) (hx))
  -- `γ = w/p` is continuous on `[a, b]`
  have hc : ContinuousOn (γ (L) (w)) (Icc (I.a) (I.b)) :=
    hS.1.w_continuousOn.div (hS.1.p_contDiffOn.continuousOn)
      (fun x hx => (hS.1.p_pos (x) (hx)).ne')
  exact (tendsto_of_eq_cramer (2) (fun y hy => γ_eq_cramer (hS) (hy.1) (hy.2))
    (hc (x) (hx))).limUnder_eq

/-! ### Step 6: recover `p` by one integration -/

/-- Step 6. `p (x) = p (a) exp ∫ₐˣ α`. With the normalisation `p (a) = 1` this says
`pRec = p / p (a)`. -/
lemma pRec_eq (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Icc (I.a) (I.b)) : pRec (I) (e) (x) = L.p (x) / L.p (I.a) := by
  have hpa : 0 < L.p (I.a) := hS.1.p_pos (I.a) (left_mem_Icc.mpr (I.a_lt_b.le))
  have hpx : 0 < L.p (x) := hS.1.p_pos (x) (hx)
  have hpc : ContinuousOn (L.p) (Icc (I.a) (I.b)) := hS.1.p_contDiffOn.continuousOn
  rcases hx.1.eq_or_lt with h | h
  · subst h
    simp [pRec, hpa.ne']
  -- `ratioLimit 0` equals the continuous function `p' / p` on `(a, x)`, hence is integrable
  have hsub : Icc (I.a) (x) ⊆ Icc (I.a) (I.b) := Icc_subset_Icc_right (hx.2)
  have hint : IntervalIntegrable (ratioLimit (I) (e) (0)) (volume) (I.a) (x) := by
    set g : ℝ → ℝ := fun t => derivWithin (L.p) (Icc (I.a) (I.b)) (t) / L.p (t) with hg
    have hgc : ContinuousOn (g) (Icc (I.a) (I.b)) :=
      (hS.1.p_contDiffOn.continuousOn_derivWithin (uniqueDiffOn_Icc (I.a_lt_b)) (le_rfl)).div
        (hpc) (fun t ht => (hS.1.p_pos (t) (ht)).ne')
    have hgi : IntervalIntegrable (g) (volume) (I.a) (x) :=
      (hgc.mono (by rwa [uIcc_of_le (h.le)])).intervalIntegrable
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (h.le)] at hgi ⊢
    refine hgi.congr_fun (fun t ht => ?_) (measurableSet_Ioo)
    have ht' : t ∈ Ioo (I.a) (I.b) := ⟨ht.1, ht.2.trans_le (hx.2)⟩
    rw [ratioLimit_zero_eq (hS) (he) (ht'), hg]
    simp only [α]
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds (ht'.1) (ht'.2))]
  have hFTC : ∫ t in I.a..x, ratioLimit (I) (e) (0) (t) =
      Real.log (L.p (x)) - Real.log (L.p (I.a)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun t => Real.log (L.p (t)))
      (h.le) (?_) (fun t ht => ?_) (hint)
    · exact (hpc.mono (hsub)).log (fun t ht => (hS.1.p_pos (t) (hsub (ht))).ne')
    · have ht' : t ∈ Ioo (I.a) (I.b) := ⟨ht.1, ht.2.trans_le (hx.2)⟩
      rw [ratioLimit_zero_eq (hS) (he) (ht')]
      exact (differentiableAt_p (hS.1) (ht')).hasDerivAt.log
        ((hS.1.p_pos (t) (Ioo_subset_Icc_self (ht'))).ne')
  rw [pRec, hFTC, Real.exp_sub, Real.exp_log (hpx), Real.exp_log (hpa)]

/-! ### Step 7: recover `q` and `w` -/

/-- Step 7. `q = p β`: `qRec = q / p (a)`. -/
lemma qRec_eq (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Icc (I.a) (I.b)) : qRec (I) (e) (x) = L.q (x) / L.p (I.a) := by
  have hpx : 0 < L.p (x) := hS.1.p_pos (x) (hx)
  have hpa : 0 < L.p (I.a) := hS.1.p_pos (I.a) (left_mem_Icc.2 (I.a_lt_b.le))
  rw [qRec, pRec_eq (hS) (he) (hx), ratioLimit_one_eq (hS) (he) (hx), β]
  field_simp

/-- Step 7. `w = p γ`: `wRec = w / p (a)`. -/
lemma wRec_eq (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Icc (I.a) (I.b)) : wRec (I) (e) (x) = w (x) / L.p (I.a) := by
  have hpx : 0 < L.p (x) := hS.1.p_pos (x) (hx)
  have hpa : 0 < L.p (I.a) := hS.1.p_pos (I.a) (left_mem_Icc.2 (I.a_lt_b.le))
  rw [wRec, pRec_eq (hS) (he) (hx), ratioLimit_two_eq (hS) (he) (hx), γ]
  field_simp

/-! ### Step 8: check with the remaining eigenpairs -/

/-- Step 8. The recovered `(α, β, γ)` satisfy the linear equation of step 2 for *every* eigenpair,
not only for the three chosen indices `e i`. -/
lemma check_eigenpair (he : StrictMono (e)) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) :
    deriv (deriv (I.Xₙ (n))) (x) + ratioLimit (I) (e) (0) (x) * deriv (I.Xₙ (n)) (x) +
      ratioLimit (I) (e) (1) (x) * I.Xₙ (n) (x) +
      I.«λₙ» (n) * ratioLimit (I) (e) (2) (x) * I.Xₙ (n) (x) = 0 := by
  obtain ⟨L, w, hS⟩ := I.exists_solution
  rw [ratioLimit_zero_eq (hS) (he) (hx), ratioLimit_one_eq (hS) (he) (Ioo_subset_Icc_self (hx)),
    ratioLimit_two_eq (hS) (he) (Ioo_subset_Icc_self (hx))]
  exact linear_equation (hS) (n) (hx)

/-! ### Step 9: the recovered triple solves the inverse problem -/

/-- The method finds a solution: `(recOperator, wRec)` solves the inverse problem, and it is
normalised by `p (a) = 1`. -/
lemma recSolution_isSolution (he : StrictMono (e)) :
    I.IsSolution (recOperator (I) (e)) (wRec (I) (e)) := by
  sorry

/-- The recovered `p` is normalised: `p (a) = 1`. -/
lemma pRec_left : pRec (I) (e) (I.a) = 1 := by
  simp [pRec]

/-- The method finds *the* solution: every solution `(L, w)` is the recovered one multiplied by
`p (a)`. Together with `pRec_left` this says that the recovered triple is the unique solution
normalised by `p (a) = 1`. -/
lemma eq_recSolution (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Icc (I.a) (I.b)) :
    L.p (x) = L.p (I.a) * pRec (I) (e) (x) ∧ L.q (x) = L.p (I.a) * qRec (I) (e) (x) ∧
      w (x) = L.p (I.a) * wRec (I) (e) (x) := by
  sorry

end SolutionMethod

end MathPhysicsTheory.SturmLiouville.InverseProblem

end
