module

public import Mathlib
public import MathPhysicsTheory.SturmLiouville.Eigenvalues
public import MathPhysicsTheory.SturmLiouville.InverseProblem.Basic
public import MathPhysicsTheory.SturmLiouville.InverseProblem.Uniqueness

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# The inverse Sturm-Liouville problem from three eigenpairs

The data of `InverseProblem` are *all* the eigenpairs `(λₙ, Xₙ)`, `n = 0, 1, 2, …`, and its
assumptions require the `λₙ` to be the whole ordered spectrum of some problem. This module shows
that three eigenpairs carry the same information:

* `ReducedInverseProblem`: the data are three eigenpairs `(λᵢ, Xᵢ)`, `i : Fin 3`, with
  `λ₀ < λ₁ < λ₂`, of some Sturm-Liouville problem. Their position in the spectrum is not part of
  the data. Existence (`ReducedInverseProblem.exists_solution`) and uniqueness up to a positive
  factor (`ReducedInverseProblem.solution_unique`) hold, and their proofs do not depend on any
  `sorry`.
* `InverseProblem.isSolution_iff_reduce`: the reduction loses nothing. For any three indices
  `n₀ < n₁ < n₂`, `(L, w)` solves the full inverse problem iff it solves the reduced problem made
  of the eigenpairs `n₀, n₁, n₂`.
* Three eigenpairs determine the whole spectral data. If two problems on `[a, b]` with the same
  boundary conditions share three eigenpairs, then they have the same eigenfunctions
  (`Problem.isEigenfunction_iff_of_three`), the same ordered eigenvalues
  (`Problem.eigenvalues_eq_of_three`), and the same Fourier coefficients, so the same Steklov
  expansion of every function (`Problem.fourierCoeff_eq_of_three`, see
  `Eigenvalues.steklov_expansion`).

Three cannot be lowered to two; see the note.
-/

@[expose] public section

open Set

namespace MathPhysicsTheory.SturmLiouville

/-! ### Proportional coefficients -/

/-- Scaling `p` and `q` by `c` on `s` scales `applyOn s` by `c` on `s`. -/
theorem Operator.applyOn_eq_const_mul {L₁ L₂ : Operator} {s : Set (ℝ)} {c : ℝ}
    (hp : ∀ x ∈ s, L₂.p (x) = c * L₁.p (x)) (hq : ∀ x ∈ s, L₂.q (x) = c * L₁.q (x))
    (y : ℝ → ℝ) {x : ℝ} (hx : x ∈ s) :
    L₂.applyOn (s) (y) (x) = c * L₁.applyOn (s) (y) (x) := by
  have h : EqOn (fun t => L₂.p (t) * derivWithin (y) (s) (t))
      (fun t => c * (L₁.p (t) * derivWithin (y) (s) (t))) (s) := fun t ht => by
    simp only [hp (t) (ht)]
    ring
  simp only [Operator.applyOn]
  rw [derivWithin_congr (h) (h (hx)), derivWithin_const_mul_field, hq (x) (hx)]
  ring

/-- If `(p₂, q₂, w₂) = c (p₁, q₁, w₁)` on `[a, b]`, every solution of `L₁ y = -λ w₁ y` solves
`L₂ y = -λ w₂ y`. -/
theorem Operator.IsSolution.of_proportional {a b : ℝ} {L₁ L₂ : Operator} {w₁ w₂ : ℝ → ℝ}
    {c «λ» : ℝ} {y : ℝ → ℝ}
    (hp : ∀ x ∈ Icc (a) (b), L₂.p (x) = c * L₁.p (x))
    (hq : ∀ x ∈ Icc (a) (b), L₂.q (x) = c * L₁.q (x))
    (hw : ∀ x ∈ Icc (a) (b), w₂ (x) = c * w₁ (x))
    (h : L₁.IsSolution (a) (b) (w₁) («λ») (y)) : L₂.IsSolution (a) (b) (w₂) («λ») (y) := by
  refine ⟨h.1, fun x hx => ?_⟩
  rw [Operator.applyOn_eq_const_mul (hp) (hq) (y) (hx), h.2 (x) (hx), hw (x) (hx)]
  ring

namespace Problem

/-- Two problems `P₁`, `P₂` with the same interval and boundary operators, whose coefficients are
proportional on `[a, b]`: `(p₂, q₂, w₂) = c (p₁, q₁, w₁)` with `c > 0`. -/
structure Proportional (P₁ P₂ : Problem) : Prop where
  a_eq : P₂.a = P₁.a
  b_eq : P₂.b = P₁.b
  Ba_eq : P₂.Ba = P₁.Ba
  Bb_eq : P₂.Bb = P₁.Bb
  exists_const : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc (P₁.a) (P₁.b),
    P₂.L.p (x) = c * P₁.L.p (x) ∧ P₂.L.q (x) = c * P₁.L.q (x) ∧ P₂.w (x) = c * P₁.w (x)

namespace Proportional

variable {P₁ P₂ : Problem}

/-- Proportionality is symmetric, with the factor `c⁻¹`. -/
theorem symm (h : Proportional (P₁) (P₂)) : Proportional (P₂) (P₁) := by
  obtain ⟨ha, hb, hBa, hBb, c, hc, hx⟩ := h
  refine ⟨ha.symm, hb.symm, hBa.symm, hBb.symm, c⁻¹, inv_pos.mpr (hc), fun x hx' => ?_⟩
  rw [ha, hb] at hx'
  obtain ⟨h1, h2, h3⟩ := hx (x) (hx')
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> linarith

/-- Proportional problems have the same solutions. -/
theorem isSolution (h : Proportional (P₁) (P₂)) {«λ» : ℝ} {y : ℝ → ℝ}
    (hy : P₁.IsSolution («λ») (y)) : P₂.IsSolution («λ») (y) := by
  obtain ⟨ha, hb, hBa, hBb, c, -, hc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [ha, hb]
    exact hy.1.of_proportional (fun x hx => (hc (x) (hx)).1) (fun x hx => (hc (x) (hx)).2.1)
      (fun x hx => (hc (x) (hx)).2.2)
  · rw [hBa]
    exact hy.2.1
  · rw [hBb]
    exact hy.2.2

/-- Proportional problems have the same eigenfunctions. -/
theorem isEigenfunction_iff (h : Proportional (P₁) (P₂)) {«λ» : ℝ} {y : ℝ → ℝ} :
    Eigenvalues.IsEigenfunction (P₁) («λ») (y) ↔ Eigenvalues.IsEigenfunction (P₂) («λ») (y) := by
  have key : ∀ {Q₁ Q₂ : Problem}, Proportional (Q₁) (Q₂) →
      Eigenvalues.IsEigenfunction (Q₁) («λ») (y) → Eigenvalues.IsEigenfunction (Q₂) («λ») (y) :=
    fun hQ hy => ⟨hQ.isSolution (hy.1), by rw [hQ.a_eq, hQ.b_eq]; exact hy.2⟩
  exact ⟨key (h), key (h.symm)⟩

/-- Proportional problems have the same eigenvalues. -/
theorem eigenvalueSet_eq (h : Proportional (P₁) (P₂)) :
    Eigenvalues.eigenvalueSet (P₁) = Eigenvalues.eigenvalueSet (P₂) := by
  ext «λ»
  exact ⟨fun ⟨y, hy⟩ => ⟨y, h.isEigenfunction_iff.mp (hy)⟩,
    fun ⟨y, hy⟩ => ⟨y, h.isEigenfunction_iff.mpr (hy)⟩⟩

/-- Proportional problems have the same ordered eigenvalues `λ₀ < λ₁ < ⋯`. -/
theorem eigenvalues_eq (h : Proportional (P₁) (P₂)) :
    Eigenvalues.eigenvalues (P₁) = Eigenvalues.eigenvalues (P₂) := by
  have h₁ := Classical.choose_spec (Eigenvalues.exists_eigenvalue_seq (P₁))
  have h₂ := Classical.choose_spec (Eigenvalues.exists_eigenvalue_seq (P₂))
  refine h₁.1.eq_of_range_eq (h₂.1) (?_)
  change Set.range (Eigenvalues.eigenvalues (P₁)) = Set.range (Eigenvalues.eigenvalues (P₂))
  rw [show Set.range (Eigenvalues.eigenvalues (P₁)) = _ from h₁.2.2.2,
    show Set.range (Eigenvalues.eigenvalues (P₂)) = _ from h₂.2.2.2, h.eigenvalueSet_eq]

/-- Proportional problems have the same Fourier coefficients: the factor `c` cancels in
`∫ f Xₙ w / ∫ Xₙ² w`. -/
theorem fourierCoeff_eq (h : Proportional (P₁) (P₂)) (Xₙ f : ℝ → ℝ) :
    Eigenvalues.fourierCoeff (P₁) (Xₙ) (f) = Eigenvalues.fourierCoeff (P₂) (Xₙ) (f) := by
  obtain ⟨ha, hb, -, -, c, hc, hx⟩ := h
  have hab : P₁.a ≤ P₁.b := P₁.a_lt_b.le
  have hcongr : ∀ g : ℝ → ℝ, ∫ x in (P₂.a)..(P₂.b), g (x) * P₂.w (x) =
      c * ∫ x in (P₁.a)..(P₁.b), g (x) * P₁.w (x) := fun g => by
    rw [ha, hb, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x hx' => ?_)
    rw [uIcc_of_le (hab)] at hx'
    simp only [(hx (x) (hx')).2.2]
    ring
  simp only [Eigenvalues.fourierCoeff]
  rw [hcongr (fun x => f (x) * Xₙ (x)), hcongr (fun x => Xₙ (x) ^ 2),
    mul_div_mul_left (_) (_) (hc.ne')]

end Proportional

/-- Uniqueness for problems: two problems with the same interval and boundary operators that
share three eigenpairs `(λᵢ, Xᵢ)` with `λ₀ < λ₁ < λ₂` are proportional. -/
theorem proportional_of_three {P₁ P₂ : Problem} (ha : P₂.a = P₁.a) (hb : P₂.b = P₁.b)
    (hBa : P₂.Ba = P₁.Ba) (hBb : P₂.Bb = P₁.Bb) {«λ» : Fin (3) → ℝ} {X : Fin (3) → ℝ → ℝ}
    (hlam : StrictMono («λ»))
    (h₁ : ∀ i, Eigenvalues.IsEigenfunction (P₁) («λ» (i)) (X (i)))
    (h₂ : ∀ i, Eigenvalues.IsEigenfunction (P₂) («λ» (i)) (X (i))) :
    Proportional (P₁) (P₂) := by
  refine ⟨ha, hb, hBa, hBb, ?_⟩
  have hA₂ := P₂.assumptions
  rw [ha, hb, hBa, hBb] at hA₂
  have hs₂ : ∀ i, P₂.L.IsSolution (P₁.a) (P₁.b) (P₂.w) («λ» (i)) (X (i)) := fun i => by
    have := (h₂ (i)).1.1
    rwa [ha, hb] at this
  exact InverseProblem.proportional_of_eigenpairs (P₁.a_lt_b) (P₁.assumptions) (hA₂) (hlam)
    (fun i => (h₁ (i)).1.1) (hs₂) (fun i => (h₁ (i)).2)

/-- Three eigenpairs determine all eigenfunctions: two problems with the same interval and
boundary operators sharing three eigenpairs (`λ₀ < λ₁ < λ₂`) have the same eigenpairs. -/
theorem isEigenfunction_iff_of_three {P₁ P₂ : Problem} (ha : P₂.a = P₁.a) (hb : P₂.b = P₁.b)
    (hBa : P₂.Ba = P₁.Ba) (hBb : P₂.Bb = P₁.Bb) {«λ» : Fin (3) → ℝ} {X : Fin (3) → ℝ → ℝ}
    (hlam : StrictMono («λ»))
    (h₁ : ∀ i, Eigenvalues.IsEigenfunction (P₁) («λ» (i)) (X (i)))
    (h₂ : ∀ i, Eigenvalues.IsEigenfunction (P₂) («λ» (i)) (X (i))) {μ : ℝ} {y : ℝ → ℝ} :
    Eigenvalues.IsEigenfunction (P₁) (μ) (y) ↔ Eigenvalues.IsEigenfunction (P₂) (μ) (y) :=
  (proportional_of_three (ha) (hb) (hBa) (hBb) (hlam) (h₁) (h₂)).isEigenfunction_iff

/-- Three eigenpairs determine the whole ordered spectrum `λ₀ < λ₁ < ⋯`. -/
theorem eigenvalues_eq_of_three {P₁ P₂ : Problem} (ha : P₂.a = P₁.a) (hb : P₂.b = P₁.b)
    (hBa : P₂.Ba = P₁.Ba) (hBb : P₂.Bb = P₁.Bb) {«λ» : Fin (3) → ℝ} {X : Fin (3) → ℝ → ℝ}
    (hlam : StrictMono («λ»))
    (h₁ : ∀ i, Eigenvalues.IsEigenfunction (P₁) («λ» (i)) (X (i)))
    (h₂ : ∀ i, Eigenvalues.IsEigenfunction (P₂) («λ» (i)) (X (i))) :
    Eigenvalues.eigenvalues (P₁) = Eigenvalues.eigenvalues (P₂) :=
  (proportional_of_three (ha) (hb) (hBa) (hBb) (hlam) (h₁) (h₂)).eigenvalues_eq

/-- Three eigenpairs determine the Steklov expansion: the Fourier coefficients
`cₙ = ∫ f Xₙ w / ∫ Xₙ² w` of every `f` are the same for every problem with these three eigenpairs,
even though `w` itself is only determined up to a constant factor. With
`Eigenvalues.steklov_expansion`, `f = ∑ₙ cₙ Xₙ` is therefore computable from three eigenpairs. -/
theorem fourierCoeff_eq_of_three {P₁ P₂ : Problem} (ha : P₂.a = P₁.a) (hb : P₂.b = P₁.b)
    (hBa : P₂.Ba = P₁.Ba) (hBb : P₂.Bb = P₁.Bb) {«λ» : Fin (3) → ℝ} {X : Fin (3) → ℝ → ℝ}
    (hlam : StrictMono («λ»))
    (h₁ : ∀ i, Eigenvalues.IsEigenfunction (P₁) («λ» (i)) (X (i)))
    (h₂ : ∀ i, Eigenvalues.IsEigenfunction (P₂) («λ» (i)) (X (i))) (Xₙ f : ℝ → ℝ) :
    Eigenvalues.fourierCoeff (P₁) (Xₙ) (f) = Eigenvalues.fourierCoeff (P₂) (Xₙ) (f) :=
  (proportional_of_three (ha) (hb) (hBa) (hBb) (hlam) (h₁) (h₂)).fourierCoeff_eq (Xₙ) (f)

end Problem

/-! ### The reduced inverse problem -/

/-- The assumptions on the data of a reduced inverse problem: the three eigenvalues are listed in
increasing order, and the three pairs are eigenpairs of some Sturm-Liouville problem on `[a, b]`
with boundary operators `Ba`, `Bb`. Which eigenvalues of that problem they are is not assumed. -/
structure ReducedInverseProblem.Assumptions (a b : ℝ) (Ba Bb : BoundaryConditions.Robin.Operator)
    («λ» : Fin (3) → ℝ) (X : Fin (3) → ℝ → ℝ) : Prop where
  /-- `λ₀ < λ₁ < λ₂`. Three distinct eigenvalues can always be listed this way. -/
  strictMono : StrictMono («λ»)
  /-- Some Sturm-Liouville problem has these three eigenpairs. -/
  exists_problem : ∃ P : Problem, P.a = a ∧ P.b = b ∧ P.Ba = Ba ∧ P.Bb = Bb ∧
    ∀ i, Eigenvalues.IsEigenfunction (P) («λ» (i)) (X (i))

/-- The inverse Sturm-Liouville problem with reduced data: an interval `[a, b]`, Robin boundary
operators `Ba`, `Bb`, and three eigenpairs `(λᵢ, Xᵢ)`, `i : Fin 3`. The operator `L` and the weight
`w` are the unknowns. -/
structure ReducedInverseProblem where
  /-- The left endpoint of the interval. -/
  a : ℝ
  /-- The right endpoint of the interval. -/
  b : ℝ
  /-- The interval is nondegenerate. -/
  a_lt_b : a < b
  /-- The Robin boundary operator at `a`. -/
  Ba : BoundaryConditions.Robin.Operator
  /-- The Robin boundary operator at `b`. -/
  Bb : BoundaryConditions.Robin.Operator
  /-- The three known eigenvalues. -/
  «λ» : Fin (3) → ℝ
  /-- The three known eigenfunctions. -/
  X : Fin (3) → ℝ → ℝ
  /-- The assumptions on the eigenpairs. -/
  assumptions : ReducedInverseProblem.Assumptions (a) (b) (Ba) (Bb) («λ») (X)

namespace ReducedInverseProblem

/-- `(L, w)` solves the reduced inverse problem: it satisfies the `Assumptions` of a
Sturm-Liouville problem and `L Xᵢ + λᵢ w Xᵢ = 0` on `[a, b]` for `i = 0, 1, 2`. -/
def IsSolution (R : ReducedInverseProblem) (L : Operator) (w : ℝ → ℝ) : Prop :=
  SturmLiouville.Assumptions (R.a) (R.b) (L) (w) (R.Ba) (R.Bb) ∧
    ∀ i, ∀ x ∈ Icc (R.a) (R.b),
      L.applyOn (Icc (R.a) (R.b)) (R.X (i)) (x) + R.«λ» (i) * w (x) * R.X (i) (x) = 0

/-- The Sturm-Liouville problem with the data of `R` and the coefficients of a solution. -/
def toProblem (R : ReducedInverseProblem) {L : Operator} {w : ℝ → ℝ} (h : R.IsSolution (L) (w)) :
    Problem :=
  ⟨R.a, R.b, R.a_lt_b, L, w, R.Ba, R.Bb, h.1⟩

/-- The data `Xᵢ` are eigenfunctions of the problem built from any solution. -/
theorem isEigenfunction_toProblem (R : ReducedInverseProblem) {L : Operator} {w : ℝ → ℝ}
    (h : R.IsSolution (L) (w)) (i : Fin (3)) :
    Eigenvalues.IsEigenfunction (R.toProblem (h)) (R.«λ» (i)) (R.X (i)) := by
  obtain ⟨-, P, ha, hb, hBa, hBb, hP⟩ := R.assumptions
  refine ⟨⟨⟨?_, fun x hx => ?_⟩, ?_, ?_⟩, ?_⟩
  · have := (hP (i)).1.1.1
    rwa [ha, hb] at this
  · have := h.2 (i) (x) (hx)
    change L.applyOn (Icc (R.a) (R.b)) (R.X (i)) (x) = -R.«λ» (i) * w (x) * R.X (i) (x)
    linarith
  · have := (hP (i)).1.2.1
    rwa [hBa] at this
  · have := (hP (i)).1.2.2
    rwa [hBb] at this
  · have := (hP (i)).2
    rwa [ha, hb] at this

/-- Existence: the coefficients of a problem with the given eigenpairs solve the reduced problem. -/
theorem exists_solution (R : ReducedInverseProblem) :
    ∃ (L : Operator) (w : ℝ → ℝ), R.IsSolution (L) (w) := by
  obtain ⟨-, P, ha, hb, hBa, hBb, hP⟩ := R.assumptions
  refine ⟨P.L, P.w, ?_, fun i x hx => ?_⟩
  · have hA := P.assumptions
    rw [ha, hb, hBa, hBb] at hA
    exact hA
  · have hx' : x ∈ Icc (P.a) (P.b) := by rwa [ha, hb]
    have := (hP (i)).1.1.2 (x) (hx')
    rw [ha, hb] at this
    linarith

/-- Uniqueness up to a positive constant factor, from three eigenpairs. Unlike
`InverseProblem.solution_unique`, the proof does not use `Eigenvalues.exists_eigenvalue_seq`: the
order `λ₀ < λ₁ < λ₂` is part of the data. -/
theorem solution_unique (R : ReducedInverseProblem) {p₁ q₁ p₂ q₂ w₁ w₂ : ℝ → ℝ}
    (h₁ : R.IsSolution ({ p := p₁, q := q₁ }) (w₁))
    (h₂ : R.IsSolution ({ p := p₂, q := q₂ }) (w₂)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc (R.a) (R.b),
      p₂ (x) = c * p₁ (x) ∧ q₂ (x) = c * q₁ (x) ∧ w₂ (x) = c * w₁ (x) :=
  (Problem.proportional_of_three (P₁ := R.toProblem (h₁)) (P₂ := R.toProblem (h₂)) (rfl) (rfl)
    (rfl) (rfl) (R.assumptions.strictMono) (R.isEigenfunction_toProblem (h₁))
    (R.isEigenfunction_toProblem (h₂))).exists_const

end ReducedInverseProblem

/-! ### The reduction loses no information -/

namespace InverseProblem

/-- The reduced inverse problem made of the eigenpairs with indices `e 0 < e 1 < e 2`. -/
noncomputable def reduce (I : InverseProblem) {e : Fin (3) → ℕ} (he : StrictMono (e)) :
    ReducedInverseProblem where
  a := I.a
  b := I.b
  a_lt_b := I.a_lt_b
  Ba := I.Ba
  Bb := I.Bb
  «λ» := fun i => I.«λₙ» (e (i))
  X := fun i => I.Xₙ (e (i))
  assumptions := by
    obtain ⟨P, ha, hb, hBa, hBb, hev, hP⟩ := I.assumptions.exists_problem
    refine ⟨?_, P, ha, hb, hBa, hBb, fun i => hP (e (i))⟩
    rw [hev]
    exact (Classical.choose_spec (Eigenvalues.exists_eigenvalue_seq (P))).1.comp (he)

/-- The reduction to three eigenpairs loses no information: for any indices `n₀ < n₁ < n₂`,
`(L, w)` solves the full inverse problem iff it solves the problem made of the three eigenpairs
`n₀, n₁, n₂`. All the other eigenpairs are redundant. -/
theorem isSolution_iff_reduce (I : InverseProblem) {e : Fin (3) → ℕ} (he : StrictMono (e))
    {L : Operator} {w : ℝ → ℝ} : I.IsSolution (L) (w) ↔ (I.reduce (he)).IsSolution (L) (w) := by
  refine ⟨fun h => ⟨h.1, fun i => h.2 (e (i))⟩, fun h => ⟨h.1, fun n x hx => ?_⟩⟩
  obtain ⟨P, ha, hb, hBa, hBb, -, hP⟩ := I.assumptions.exists_problem
  set R := I.reduce (he)
  -- `P` and the problem built from `(L, w)` share the three eigenpairs, so they are proportional.
  have hprop : Problem.Proportional (P) (R.toProblem (h)) :=
    Problem.proportional_of_three (ha.symm) (hb.symm) (hBa.symm) (hBb.symm)
      (R.assumptions.strictMono) (fun i => hP (e (i))) (R.isEigenfunction_toProblem (h))
  have hn := (hprop.isSolution ((hP (n)).1)).1.2 (x) (hx)
  change L.applyOn (Icc (I.a) (I.b)) (I.Xₙ (n)) (x) = -I.«λₙ» (n) * w (x) * I.Xₙ (n) (x) at hn
  linarith

end InverseProblem

end MathPhysicsTheory.SturmLiouville

end
