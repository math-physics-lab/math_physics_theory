module

public import Mathlib
public import MathPhysicsTheory.SturmLiouville.InverseProblem.Basic

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# A solution method for the inverse Sturm-Liouville problem

Statements (no proofs yet) for the solution method described in
`InverseProblem/Basic/NOTE.md`. Every `sorry` below is a theorem still to be proved.

Given the eigenpairs `(λₙ, Xₙ)` of an inverse problem `I`, the method finds `(p, q, w)` using only
`n = 0, 1, 2`. For a solution `(L, w)` write `α = p'/p`, `β = q/p`, `γ = w/p`.

* **Step 1** (`expand`): `p Xₙ'' + p' Xₙ' + q Xₙ + λₙ w Xₙ = 0`.
* **Step 2** (`linear_equation`): `Xₙ'' + α Xₙ' + β Xₙ + λₙ γ Xₙ = 0`, linear in `(α, β, γ)`.
* **Step 3** (`coeffMatrix_mulVec`): `M(x) (α, β, γ)ᵀ = r(x)` for `n = 0, 1, 2`.
* **Step 4** (`alpha_eq_cramer`, `beta_eq_cramer`, `gamma_eq_cramer`): `(α, β, γ) = (A, B, G) / D`
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

variable (I : InverseProblem)

/-! ### Definitions: the data of the method -/

/-- The matrix `M (x)` of step 3: row `n` is `(Xₙ' (x), Xₙ (x), λₙ Xₙ (x))`, `n = 0, 1, 2`. -/
noncomputable def coeffMatrix (x : ℝ) : Matrix (Fin (3)) (Fin (3)) (ℝ) :=
  Matrix.of (fun i => ![deriv (I.Xₙ (i)) (x), I.Xₙ (i) (x), I.«λₙ» (i) * I.Xₙ (i) (x)])

/-- The right-hand side `r (x) = (-X₀'' (x), -X₁'' (x), -X₂'' (x))` of step 3. -/
noncomputable def rhs (x : ℝ) : Fin (3) → (ℝ) :=
  fun i => -deriv (deriv (I.Xₙ (i))) (x)

/-- The determinant `D (x) = det M (x)`. -/
noncomputable def D (x : ℝ) : ℝ :=
  (coeffMatrix (I) (x)).det

/-- The numerators of Cramer's rule: `cramerNum 0 = A`, `cramerNum 1 = B`, `cramerNum 2 = G`, that
is `D` with the `k`-th column replaced by `r`. -/
noncomputable def cramerNum (k : Fin (3)) (x : ℝ) : ℝ :=
  Matrix.cramer (coeffMatrix (I) (x)) (rhs (I) (x)) (k)

/-- The points of `(a, b)` where `D ≠ 0`. -/
def regularSet : Set (ℝ) :=
  {x | x ∈ Ioo (I.a) (I.b) ∧ D (I) (x) ≠ 0}

/-- The value at `x` of the limit of `cramerNum k / D` along the points where `D ≠ 0` (step 5).
It is `α` for `k = 0`, `β` for `k = 1` and `γ` for `k = 2`. -/
noncomputable def ratioLimit (k : Fin (3)) (x : ℝ) : ℝ :=
  limUnder (𝓝[regularSet (I)] (x)) (fun y => cramerNum (I) (k) (y) / D (I) (y))

/-- The recovered `p`, normalised by `p (a) = 1` (step 6): `p = exp ∫ₐˣ α`. -/
noncomputable def pRec (x : ℝ) : ℝ :=
  Real.exp (∫ t in I.a..x, ratioLimit (I) (0) (t))

/-- The recovered `q = p β` (step 7). -/
noncomputable def qRec (x : ℝ) : ℝ :=
  pRec (I) (x) * ratioLimit (I) (1) (x)

/-- The recovered weight `w = p γ` (step 7). -/
noncomputable def wRec (x : ℝ) : ℝ :=
  pRec (I) (x) * ratioLimit (I) (2) (x)

/-- The recovered operator `L y = (pRec y')' + qRec y`. -/
noncomputable def recOperator : Operator :=
  { p := pRec (I), q := qRec (I) }

/-- `α = p'/p` (step 2). -/
noncomputable def alpha (L : Operator) (x : ℝ) : ℝ :=
  deriv (L.p) (x) / L.p (x)

/-- `β = q/p` (step 2). -/
noncomputable def beta (L : Operator) (x : ℝ) : ℝ :=
  L.q (x) / L.p (x)

/-- `γ = w/p` (step 2). -/
noncomputable def gamma (L : Operator) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  w (x) / L.p (x)

variable {I}
variable {L : Operator} {w : ℝ → ℝ}

/-! ### Step 1: expand the operator -/

/-- Step 1. At interior points `(p Xₙ')' = p Xₙ'' + p' Xₙ'`, so
`p Xₙ'' + p' Xₙ' + q Xₙ + λₙ w Xₙ = 0`. -/
theorem expand (hS : I.IsSolution (L) (w)) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) :
    L.p (x) * deriv (deriv (I.Xₙ (n))) (x) + deriv (L.p) (x) * deriv (I.Xₙ (n)) (x) +
      L.q (x) * I.Xₙ (n) (x) + I.«λₙ» (n) * w (x) * I.Xₙ (n) (x) = 0 := by
  sorry

/-! ### Step 2: divide by `p` and rename the unknowns -/

/-- Step 2. With `α = p'/p`, `β = q/p`, `γ = w/p`, for every `n` and interior `x`:
`Xₙ'' + α Xₙ' + β Xₙ + λₙ γ Xₙ = 0`. For fixed `x` this is linear in `(α, β, γ)`. -/
theorem linear_equation (hS : I.IsSolution (L) (w)) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (I.a) (I.b)) :
    deriv (deriv (I.Xₙ (n))) (x) + alpha (L) (x) * deriv (I.Xₙ (n)) (x) +
      beta (L) (x) * I.Xₙ (n) (x) + I.«λₙ» (n) * gamma (L) (w) (x) * I.Xₙ (n) (x) = 0 := by
  sorry

/-! ### Step 3: three eigenpairs give a linear system -/

/-- Step 3. For `n = 0, 1, 2` the equations of step 2 form the system
`M (x) (α, β, γ)ᵀ = r (x)`. -/
theorem coeffMatrix_mulVec (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) :
    (coeffMatrix (I) (x)).mulVec ![alpha (L) (x), beta (L) (x), gamma (L) (w) (x)] =
      rhs (I) (x) := by
  sorry

/-! ### Step 4: Cramer's rule -/

/-- Step 4. Wherever `D (x) ≠ 0`, `(α, β, γ) = (A, B, G) / D`. This is a necessary condition on
every solution. -/
theorem alpha_eq_cramer (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b))
    (hD : D (I) (x) ≠ 0) : alpha (L) (x) = cramerNum (I) (0) (x) / D (I) (x) := by
  sorry

/-- Step 4, for `β`. -/
theorem beta_eq_cramer (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b))
    (hD : D (I) (x) ≠ 0) : beta (L) (x) = cramerNum (I) (1) (x) / D (I) (x) := by
  sorry

/-- Step 4, for `γ`. -/
theorem gamma_eq_cramer (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b))
    (hD : D (I) (x) ≠ 0) : gamma (L) (w) (x) = cramerNum (I) (2) (x) / D (I) (x) := by
  sorry

/-! ### Step 5: `D ≠ 0` on a dense set -/

/-- Step 5 (the key lemma). `D` does not vanish on any subinterval of `(a, b)`. -/
theorem exists_D_ne_zero (hS : I.IsSolution (L) (w)) {c d : ℝ} (hcd : c < d)
    (hsub : Ioo (c) (d) ⊆ Ioo (I.a) (I.b)) : ∃ x ∈ Ioo (c) (d), D (I) (x) ≠ 0 := by
  sorry

/-- Step 5. The set `{D ≠ 0}` is dense in `(a, b)`. -/
theorem closure_regularSet : Ioo (I.a) (I.b) ⊆ closure (regularSet (I)) := by
  sorry

/-- Step 5. At every interior point, `α` is the limit of `A / D` along the points where
`D ≠ 0`. -/
theorem tendsto_alpha (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) :
    Tendsto (fun y => cramerNum (I) (0) (y) / D (I) (y)) (𝓝[regularSet (I)] (x))
      (𝓝 (alpha (L) (x))) := by
  sorry

/-- Step 5, for `β` and `B / D`. -/
theorem tendsto_beta (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) :
    Tendsto (fun y => cramerNum (I) (1) (y) / D (I) (y)) (𝓝[regularSet (I)] (x))
      (𝓝 (beta (L) (x))) := by
  sorry

/-- Step 5, for `γ` and `G / D`. -/
theorem tendsto_gamma (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) :
    Tendsto (fun y => cramerNum (I) (2) (y) / D (I) (y)) (𝓝[regularSet (I)] (x))
      (𝓝 (gamma (L) (w) (x))) := by
  sorry

/-- Step 5. Hence `ratioLimit 0` recovers `α` at interior points. -/
theorem ratioLimit_zero_eq (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) :
    ratioLimit (I) (0) (x) = alpha (L) (x) := by
  sorry

/-- Step 5. Hence `ratioLimit 1` recovers `β`, also at the endpoints: `β = q/p` is continuous
on all of `[a, b]`. -/
theorem ratioLimit_one_eq (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Icc (I.a) (I.b)) :
    ratioLimit (I) (1) (x) = beta (L) (x) := by
  sorry

/-- Step 5. Hence `ratioLimit 2` recovers `γ`, also at the endpoints: `γ = w/p` is continuous
on all of `[a, b]`. -/
theorem ratioLimit_two_eq (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Icc (I.a) (I.b)) :
    ratioLimit (I) (2) (x) = gamma (L) (w) (x) := by
  sorry

/-! ### Step 6: recover `p` by one integration -/

/-- Step 6. `p (x) = p (a) exp ∫ₐˣ α`. With the normalisation `p (a) = 1` this says
`pRec = p / p (a)`. -/
theorem pRec_eq (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Icc (I.a) (I.b)) :
    pRec (I) (x) = L.p (x) / L.p (I.a) := by
  sorry

/-! ### Step 7: recover `q` and `w` -/

/-- Step 7. `q = p β`: `qRec = q / p (a)`. -/
theorem qRec_eq (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Icc (I.a) (I.b)) :
    qRec (I) (x) = L.q (x) / L.p (I.a) := by
  sorry

/-- Step 7. `w = p γ`: `wRec = w / p (a)`. -/
theorem wRec_eq (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Icc (I.a) (I.b)) :
    wRec (I) (x) = w (x) / L.p (I.a) := by
  sorry

/-! ### Step 8: check with the remaining eigenpairs -/

/-- Step 8. The recovered `(α, β, γ)` satisfy the linear equation of step 2 for *every* eigenpair,
not only for `n = 0, 1, 2`. -/
theorem check_eigenpair (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (I.a) (I.b)) :
    deriv (deriv (I.Xₙ (n))) (x) + ratioLimit (I) (0) (x) * deriv (I.Xₙ (n)) (x) +
      ratioLimit (I) (1) (x) * I.Xₙ (n) (x) +
      I.«λₙ» (n) * ratioLimit (I) (2) (x) * I.Xₙ (n) (x) = 0 := by
  sorry

/-! ### Step 9: the recovered triple solves the inverse problem -/

/-- The method finds a solution: `(recOperator, wRec)` solves the inverse problem, and it is
normalised by `p (a) = 1`. -/
theorem recSolution_isSolution : I.IsSolution (recOperator (I)) (wRec (I)) := by
  sorry

/-- The recovered `p` is normalised: `p (a) = 1`. -/
theorem pRec_left : pRec (I) (I.a) = 1 := by
  simp [pRec]

/-- The method finds *the* solution: every solution `(L, w)` is the recovered one multiplied by
`p (a)`. Together with `pRec_left` this says that the recovered triple is the unique solution
normalised by `p (a) = 1`. -/
theorem eq_recSolution (hS : I.IsSolution (L) (w)) {x : ℝ} (hx : x ∈ Icc (I.a) (I.b)) :
    L.p (x) = L.p (I.a) * pRec (I) (x) ∧ L.q (x) = L.p (I.a) * qRec (I) (x) ∧
      w (x) = L.p (I.a) * wRec (I) (x) := by
  sorry

end SolutionMethod

end MathPhysicsTheory.SturmLiouville.InverseProblem

end
