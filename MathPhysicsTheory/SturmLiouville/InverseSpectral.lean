module

public import Mathlib
public import MathPhysicsTheory.BoundaryConditions.Robin
public import MathPhysicsTheory.SturmLiouville.Eigenvalues
public import MathPhysicsTheory.SturmLiouville.Problem

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Inverse spectral problems

In `InverseProblem` the data are the eigen*functions* `Xₙ`. Here the data are *numbers* only: one
or two spectra, possibly with norming constants. Numbers can determine at most one unknown
function (see the note), so the coefficients are put in Liouville normal form, `p = 1` and `w = 1`,
and the only unknown is the potential `q`:

* `y'' + q y = -λ y` on `[a, b]`, `α₁ y(a) + β₁ y'(a) = 0`, `α₂ y(b) + β₂ y'(b) = 0`.

The interval and the boundary conditions are known. The problems, each with its classical
uniqueness theorem:

* `TwoSpectra` (Borg): the spectra for two different boundary conditions at `b`.
* `SpectralData` (Gelfand–Levitan, Marchenko): one spectrum and the norming constants.
* `SymmetricSpectrum` (Borg): one spectrum, for a potential symmetric about the midpoint.
* `HalfKnownSpectrum` (Hochstadt–Lieberman): one spectrum, with `q` known on half of the interval.
* `ambarzumian` (Ambarzumian): for Neumann conditions, `λ₀ = 0` forces `q = 0`.

Existence holds by assumption: the data come from some admissible potential. The uniqueness
theorems are stated and not proved yet.

## References

* G. Borg, *Eine Umkehrung der Sturm-Liouvilleschen Eigenwertaufgabe*, Acta Math. 78 (1946).
* I. M. Gelfand, B. M. Levitan, *On the determination of a differential equation from its
  spectral function*, Izv. Akad. Nauk SSSR 15 (1951).
* V. A. Marchenko, *Sturm-Liouville Operators and Applications*, Birkhäuser (1986).
* H. Hochstadt, B. Lieberman, *An inverse Sturm-Liouville problem with mixed given data*,
  SIAM J. Appl. Math. 34 (1978).
* V. A. Ambarzumian, *Über eine Frage der Eigenwerttheorie*, Z. Phys. 53 (1929).
-/

@[expose] public section

open Set

namespace MathPhysicsTheory.SturmLiouville.InverseSpectral

open BoundaryConditions

/-! ### The direct problem in Liouville normal form -/

/-- The operator in Liouville normal form, `L y = y'' + q y`. -/
def normalOperator (q : ℝ → ℝ) : Operator :=
  { p := 1, q := q }

/-- `q` is an admissible potential on `[a, b]` for the boundary operators `Ba`, `Bb`: the
`Assumptions` of a Sturm-Liouville problem hold with `p = 1` and `w = 1`. They say that `q` is
continuous with `q ≤ 0`, and that `Ba`, `Bb` are nondegenerate boundary operators at `a` and `b`
with the usual signs. -/
def Admissible (a b : ℝ) (Ba Bb : Robin.Operator) (q : ℝ → ℝ) : Prop :=
  SturmLiouville.Assumptions (a) (b) (normalOperator (q)) (1) (Ba) (Bb)

/-- The Sturm-Liouville problem `y'' + q y = -λ y` on `[a, b]` with boundary operators `Ba`, `Bb`,
for an admissible potential `q`. -/
def normalProblem {a b : ℝ} (hab : a < b) {Ba Bb : Robin.Operator} {q : ℝ → ℝ}
    (hq : Admissible (a) (b) (Ba) (Bb) (q)) : Problem :=
  ⟨a, b, hab, normalOperator (q), 1, Ba, Bb, hq⟩

/-- `μ` is the spectrum of the potential `q`: `q` is admissible and `μ₀ < μ₁ < ⋯` are the
eigenvalues of `y'' + q y = -λ y` with the boundary operators `Ba`, `Bb`, in increasing order. -/
def HasSpectrum {a b : ℝ} (hab : a < b) (Ba Bb : Robin.Operator) (q : ℝ → ℝ) (μ : ℕ → ℝ) :
    Prop :=
  ∃ hq : Admissible (a) (b) (Ba) (Bb) (q), Eigenvalues.eigenvalues (normalProblem (hab) (hq)) = μ

/-- `X` is the eigenfunction of `P` for `λ` normalised at `a` by the Cauchy data
`X(a) = β₁`, `X'(a) = -α₁` of the boundary operator `Ba y = α₁ y(a) + β₁ y'(a)`. For a Robin
condition `y'(a) = h y(a)` this is `X(a) = 1`, `X'(a) = h`, and for a Dirichlet condition it is
`X(a) = 0`, `X'(a) = -1`. -/
def IsNormalizedEigenfunction (P : Problem) («λ» : ℝ) (X : ℝ → ℝ) : Prop :=
  Eigenvalues.IsEigenfunction (P) («λ») (X) ∧ X (P.a) = P.Ba.β ∧ deriv (X) (P.a) = -P.Ba.α

/-- `ρ` is the norming constant of `P` for the eigenvalue `λ`: `ρ = ∫ₐᵇ X² w` for the normalised
eigenfunction `X` (see `IsNormalizedEigenfunction`). -/
def IsNormingConstant (P : Problem) («λ» ρ : ℝ) : Prop :=
  ∃ X, IsNormalizedEigenfunction (P) («λ») (X) ∧ ∫ x in (P.a)..(P.b), X (x) ^ 2 * P.w (x) = ρ

/-- `(μ, ρ)` are the spectral data of the potential `q`: `μ` is its spectrum and `ρₙ` the norming
constant for `μₙ`. -/
def HasSpectralData {a b : ℝ} (hab : a < b) (Ba Bb : Robin.Operator) (q : ℝ → ℝ)
    (μ ρ : ℕ → ℝ) : Prop :=
  ∃ hq : Admissible (a) (b) (Ba) (Bb) (q),
    Eigenvalues.eigenvalues (normalProblem (hab) (hq)) = μ ∧
      ∀ n, IsNormingConstant (normalProblem (hab) (hq)) (μ (n)) (ρ (n))

/-- The boundary operator at `b` that mirrors `Ba` under `x ↦ a + b - x`: if `y` satisfies
`α y(a) + β y'(a) = 0`, then `x ↦ y (a + b - x)` satisfies `α y(b) - β y'(b) = 0`. -/
def mirror (Ba : Robin.Operator) (b : ℝ) : Robin.Operator :=
  ⟨Ba.α, -Ba.β, b⟩

/-! ### Borg: two spectra -/

/-- Borg's inverse problem: recover `q` from two spectra, for the same boundary condition `Ba` at
`a` and two different boundary conditions `Bb₁`, `Bb₂` at `b`. -/
structure TwoSpectra where
  /-- The left endpoint of the interval. -/
  a : ℝ
  /-- The right endpoint of the interval. -/
  b : ℝ
  /-- The interval is nondegenerate. -/
  a_lt_b : a < b
  /-- The boundary operator at `a`, shared by both problems. -/
  Ba : Robin.Operator
  /-- The first boundary operator at `b`. -/
  Bb₁ : Robin.Operator
  /-- The second boundary operator at `b`. -/
  Bb₂ : Robin.Operator
  /-- The two conditions at `b` are different: `(α, β)` are not proportional. -/
  Bb_ne : Bb₁.α * Bb₂.β - Bb₁.β * Bb₂.α ≠ 0
  /-- The spectrum for `Bb₁`. -/
  μ₁ : ℕ → ℝ
  /-- The spectrum for `Bb₂`. -/
  μ₂ : ℕ → ℝ
  /-- The two spectra come from one admissible potential. -/
  exists_potential : ∃ q, HasSpectrum (a_lt_b) (Ba) (Bb₁) (q) (μ₁) ∧
    HasSpectrum (a_lt_b) (Ba) (Bb₂) (q) (μ₂)

namespace TwoSpectra

/-- `q` solves Borg's problem: it has both spectra. -/
def IsSolution (I : TwoSpectra) (q : ℝ → ℝ) : Prop :=
  HasSpectrum (I.a_lt_b) (I.Ba) (I.Bb₁) (q) (I.μ₁) ∧
    HasSpectrum (I.a_lt_b) (I.Ba) (I.Bb₂) (q) (I.μ₂)

/-- Existence: the data come from some potential. -/
theorem exists_solution (I : TwoSpectra) : ∃ q, I.IsSolution (q) :=
  I.exists_potential

/-- Borg's theorem: two spectra determine the potential on `[a, b]`. -/
theorem solution_unique (I : TwoSpectra) {q₁ q₂ : ℝ → ℝ} (h₁ : I.IsSolution (q₁))
    (h₂ : I.IsSolution (q₂)) : ∀ x ∈ Icc (I.a) (I.b), q₁ (x) = q₂ (x) := by
  -- TODO: prove.
  sorry

end TwoSpectra

/-! ### Gelfand–Levitan, Marchenko: one spectrum and the norming constants -/

/-- The Gelfand–Levitan–Marchenko inverse problem: recover `q` from its spectrum `μ` and its
norming constants `ρ`. -/
structure SpectralData where
  /-- The left endpoint of the interval. -/
  a : ℝ
  /-- The right endpoint of the interval. -/
  b : ℝ
  /-- The interval is nondegenerate. -/
  a_lt_b : a < b
  /-- The boundary operator at `a`. -/
  Ba : Robin.Operator
  /-- The boundary operator at `b`. -/
  Bb : Robin.Operator
  /-- The spectrum. -/
  μ : ℕ → ℝ
  /-- The norming constants. -/
  ρ : ℕ → ℝ
  /-- The data come from one admissible potential. -/
  exists_potential : ∃ q, HasSpectralData (a_lt_b) (Ba) (Bb) (q) (μ) (ρ)

namespace SpectralData

/-- `q` solves the problem: it has the spectral data `(μ, ρ)`. -/
def IsSolution (I : SpectralData) (q : ℝ → ℝ) : Prop :=
  HasSpectralData (I.a_lt_b) (I.Ba) (I.Bb) (q) (I.μ) (I.ρ)

/-- Existence: the data come from some potential. -/
theorem exists_solution (I : SpectralData) : ∃ q, I.IsSolution (q) :=
  I.exists_potential

/-- Marchenko's theorem: the spectrum and the norming constants determine the potential on
`[a, b]`. The Gelfand–Levitan integral equation reconstructs it. -/
theorem solution_unique (I : SpectralData) {q₁ q₂ : ℝ → ℝ} (h₁ : I.IsSolution (q₁))
    (h₂ : I.IsSolution (q₂)) : ∀ x ∈ Icc (I.a) (I.b), q₁ (x) = q₂ (x) := by
  -- TODO: prove.
  sorry

end SpectralData

/-! ### Borg: one spectrum, symmetric potential -/

/-- Recover a symmetric potential, `q (a + b - x) = q (x)`, from one spectrum. The boundary
conditions are symmetric too: the one at `b` is the mirror of the one at `a`. -/
structure SymmetricSpectrum where
  /-- The left endpoint of the interval. -/
  a : ℝ
  /-- The right endpoint of the interval. -/
  b : ℝ
  /-- The interval is nondegenerate. -/
  a_lt_b : a < b
  /-- The boundary operator at `a`; the one at `b` is `mirror Ba b`. -/
  Ba : Robin.Operator
  /-- The spectrum. -/
  μ : ℕ → ℝ
  /-- The spectrum comes from a symmetric admissible potential. -/
  exists_potential : ∃ q, (∀ x, q (a + b - x) = q (x)) ∧
    HasSpectrum (a_lt_b) (Ba) (mirror (Ba) (b)) (q) (μ)

namespace SymmetricSpectrum

/-- `q` solves the problem: it is symmetric and has the spectrum `μ`. -/
def IsSolution (I : SymmetricSpectrum) (q : ℝ → ℝ) : Prop :=
  (∀ x, q (I.a + I.b - x) = q (x)) ∧
    HasSpectrum (I.a_lt_b) (I.Ba) (mirror (I.Ba) (I.b)) (q) (I.μ)

/-- Existence: the data come from some symmetric potential. -/
theorem exists_solution (I : SymmetricSpectrum) : ∃ q, I.IsSolution (q) :=
  I.exists_potential

/-- Borg's theorem for symmetric potentials: one spectrum determines a symmetric potential on
`[a, b]`. -/
theorem solution_unique (I : SymmetricSpectrum) {q₁ q₂ : ℝ → ℝ} (h₁ : I.IsSolution (q₁))
    (h₂ : I.IsSolution (q₂)) : ∀ x ∈ Icc (I.a) (I.b), q₁ (x) = q₂ (x) := by
  -- TODO: prove.
  sorry

end SymmetricSpectrum

/-! ### Hochstadt–Lieberman: one spectrum, half of the potential known -/

/-- Recover `q` from one spectrum when `q` is already known, equal to `q₀`, on the right half
`[(a + b) / 2, b]` of the interval. -/
structure HalfKnownSpectrum where
  /-- The left endpoint of the interval. -/
  a : ℝ
  /-- The right endpoint of the interval. -/
  b : ℝ
  /-- The interval is nondegenerate. -/
  a_lt_b : a < b
  /-- The boundary operator at `a`. -/
  Ba : Robin.Operator
  /-- The boundary operator at `b`. -/
  Bb : Robin.Operator
  /-- The potential on the right half of the interval. -/
  q₀ : ℝ → ℝ
  /-- The spectrum. -/
  μ : ℕ → ℝ
  /-- The data come from an admissible potential equal to `q₀` on the right half. -/
  exists_potential : ∃ q, (∀ x ∈ Icc ((a + b) / 2) (b), q (x) = q₀ (x)) ∧
    HasSpectrum (a_lt_b) (Ba) (Bb) (q) (μ)

namespace HalfKnownSpectrum

/-- `q` solves the problem: it equals `q₀` on the right half and has the spectrum `μ`. -/
def IsSolution (I : HalfKnownSpectrum) (q : ℝ → ℝ) : Prop :=
  (∀ x ∈ Icc ((I.a + I.b) / 2) (I.b), q (x) = I.q₀ (x)) ∧
    HasSpectrum (I.a_lt_b) (I.Ba) (I.Bb) (q) (I.μ)

/-- Existence: the data come from some potential. -/
theorem exists_solution (I : HalfKnownSpectrum) : ∃ q, I.IsSolution (q) :=
  I.exists_potential

/-- The Hochstadt–Lieberman theorem: one spectrum and the potential on half of the interval
determine the potential on all of `[a, b]`. -/
theorem solution_unique (I : HalfKnownSpectrum) {q₁ q₂ : ℝ → ℝ} (h₁ : I.IsSolution (q₁))
    (h₂ : I.IsSolution (q₂)) : ∀ x ∈ Icc (I.a) (I.b), q₁ (x) = q₂ (x) := by
  -- TODO: prove.
  sorry

end HalfKnownSpectrum

/-! ### Ambarzumian: a single eigenvalue -/

/-- Ambarzumian's theorem, in the sign convention `q ≤ 0` of `Assumptions`: for Neumann
conditions at both ends, if the lowest eigenvalue is `0` then `q = 0` on `[a, b]`. A single number
determines the potential, because `0` is the lowest eigenvalue `q = 0` can have. -/
theorem ambarzumian {a b : ℝ} (hab : a < b) {q : ℝ → ℝ} {μ : ℕ → ℝ}
    (h : HasSpectrum (hab) (⟨0, 1, a⟩) (⟨0, 1, b⟩) (q) (μ)) (h₀ : μ (0) = 0) :
    ∀ x ∈ Icc (a) (b), q (x) = 0 := by
  -- TODO: prove.
  sorry

end MathPhysicsTheory.SturmLiouville.InverseSpectral

end
