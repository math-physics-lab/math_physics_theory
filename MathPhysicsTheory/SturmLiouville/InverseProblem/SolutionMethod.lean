module

public import Mathlib
public import MathPhysicsTheory.SturmLiouville.InverseProblem.Basic

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# A solution method for the inverse Sturm-Liouville problem

Statements and proofs for the solution method described in `InverseProblem/Basic/NOTE.md`.
Steps 1 to 4 are proved. Every `sorry` below (steps 5 to 9) is a lemma still to be proved.

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

/-- The given eigenfunctions are `C²` on `[a, b]`. -/
lemma contDiffOn_Xₙ (I : InverseProblem) (n : ℕ) :
    ContDiffOn (ℝ) (2) (I.Xₙ (n)) (Icc (I.a) (I.b)) := by
  obtain ⟨P, ha, hb, -, -, -, hP⟩ := I.assumptions.exists_problem
  have := (hP (n)).1.1.1
  rwa [ha, hb] at this

/-- The derivative of an eigenfunction is differentiable at interior points. -/
lemma differentiableAt_deriv_Xₙ (I : InverseProblem) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (I.a) (I.b)) : DifferentiableAt (ℝ) (deriv (I.Xₙ (n))) (x) := by
  have h2 : ContDiffOn (ℝ) (2) (I.Xₙ (n)) (Ioo (I.a) (I.b)) :=
    (contDiffOn_Xₙ (I) (n)).mono (Ioo_subset_Icc_self)
  have h3 : ContDiffOn (ℝ) (1) (deriv (I.Xₙ (n))) (Ioo (I.a) (I.b)) :=
    h2.deriv_of_isOpen (isOpen_Ioo) (by norm_num)
  exact (h3.contDiffAt (isOpen_Ioo.mem_nhds (hx))).differentiableAt (by norm_num)

/-! ### Step 1: expand the operator -/

/-- Step 1. At interior points `(p Xₙ')' = p Xₙ'' + p' Xₙ'`, so
`p Xₙ'' + p' Xₙ' + q Xₙ + λₙ w Xₙ = 0`. -/
lemma expand (hS : I.IsSolution (L) (w)) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) :
    L.p (x) * deriv (deriv (I.Xₙ (n))) (x) + deriv (L.p) (x) * deriv (I.Xₙ (n)) (x) +
      L.q (x) * I.Xₙ (n) (x) + I.«λₙ» (n) * w (x) * I.Xₙ (n) (x) = 0 := by
  have hp : DifferentiableAt (ℝ) (L.p) (x) := differentiableAt_p (hS.1) (hx)
  have h : HasDerivAt (fun t => L.p (t) * deriv (I.Xₙ (n)) (t))
      (deriv (L.p) (x) * deriv (I.Xₙ (n)) (x) + L.p (x) * deriv (deriv (I.Xₙ (n))) (x)) (x) :=
    hp.hasDerivAt.mul ((differentiableAt_deriv_Xₙ (I) (n) (hx)).hasDerivAt)
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
  sorry

/-- Step 5. The set `{D ≠ 0}` is dense in `(a, b)`. -/
lemma closure_regularSet (he : StrictMono (e)) :
    Ioo (I.a) (I.b) ⊆ closure (regularSet (I) (e)) := by
  sorry

/-- Step 5. At every interior point, `α` is the limit of `A / D` along the points where
`D ≠ 0`. -/
lemma tendsto_α (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Ioo (I.a) (I.b)) :
    Tendsto (fun y => cramerNum (I) (e) (0) (y) / D (I) (e) (y))
      (𝓝[regularSet (I) (e)] (x)) (𝓝 (α (L) (x))) := by
  sorry

/-- Step 5, for `β` and `B / D`. -/
lemma tendsto_β (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Ioo (I.a) (I.b)) :
    Tendsto (fun y => cramerNum (I) (e) (1) (y) / D (I) (e) (y))
      (𝓝[regularSet (I) (e)] (x)) (𝓝 (β (L) (x))) := by
  sorry

/-- Step 5, for `γ` and `G / D`. -/
lemma tendsto_γ (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Ioo (I.a) (I.b)) :
    Tendsto (fun y => cramerNum (I) (e) (2) (y) / D (I) (e) (y))
      (𝓝[regularSet (I) (e)] (x)) (𝓝 (γ (L) (w) (x))) := by
  sorry

/-- Step 5. Hence `ratioLimit 0` recovers `α` at interior points. -/
lemma ratioLimit_zero_eq (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Ioo (I.a) (I.b)) : ratioLimit (I) (e) (0) (x) = α (L) (x) := by
  sorry

/-- Step 5. Hence `ratioLimit 1` recovers `β`, also at the endpoints: `β = q/p` is continuous
on all of `[a, b]`. -/
lemma ratioLimit_one_eq (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Icc (I.a) (I.b)) : ratioLimit (I) (e) (1) (x) = β (L) (x) := by
  sorry

/-- Step 5. Hence `ratioLimit 2` recovers `γ`, also at the endpoints: `γ = w/p` is continuous
on all of `[a, b]`. -/
lemma ratioLimit_two_eq (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Icc (I.a) (I.b)) : ratioLimit (I) (e) (2) (x) = γ (L) (w) (x) := by
  sorry

/-! ### Step 6: recover `p` by one integration -/

/-- Step 6. `p (x) = p (a) exp ∫ₐˣ α`. With the normalisation `p (a) = 1` this says
`pRec = p / p (a)`. -/
lemma pRec_eq (hS : I.IsSolution (L) (w)) (he : StrictMono (e)) {x : ℝ}
    (hx : x ∈ Icc (I.a) (I.b)) : pRec (I) (e) (x) = L.p (x) / L.p (I.a) := by
  sorry

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
  sorry

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
