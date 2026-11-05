module

public import Mathlib
public import MathPhysicsTheory.BoundaryConditions.Robin
public import MathPhysicsTheory.SturmLiouville.Operator

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Sturm-Liouville problems

A Sturm-Liouville problem on an interval `[a, b]`, with coefficients `p`, `q` and a weight `w`,
asks for the functions `y` and numbers `λ` with

* `(p y')' + q y = -λ w y` on `[a, b]`,
* `α₁ y(a) + β₁ y'(a) = 0` and `α₂ y(b) + β₂ y'(b) = 0`.

Derivatives are taken within `[a, b]`, so they are one-sided at the endpoints and do not depend on
the values of `y` or `p` outside `[a, b]`.

The coefficients satisfy, on `[a, b]`:

* `p` is continuously differentiable, `q` and `w` are continuous;
* `p > 0`, `w > 0` and `q ≤ 0`;
* `α₁² + β₁² ≠ 0`, `α₂² + β₂² ≠ 0`, `α₁ β₁ ≤ 0` and `α₂ β₂ ≥ 0`.

`y = 0` is always a solution.

## Example

`y'' = -λ y` on `[0, π]` with `y(0) = 0`, `y(π) = 0`: `sin` is a solution for `λ = 1`, `cos` is
not.

```lean
noncomputable def dirichlet : Problem where
  a := 0
  b := Real.pi
  a_lt_b := Real.pi_pos
  L := { p := 1, q := 0 }
  w := 1
  Ba := { α := 1, β := 0, c := 0 }
  Bb := { α := 1, β := 0, c := Real.pi }
  assumptions := {
    p_pos := fun _ _ => by simp
    w_pos := fun _ _ => by simp
    p_contDiffOn := contDiffOn_const
    q_continuousOn := continuousOn_const
    w_continuousOn := continuousOn_const
    q_nonpos := fun _ _ => by simp
    Ba_c := rfl
    Bb_c := rfl
    Ba_ne := by simp
    Bb_ne := by simp
    Ba_mul_nonpos := by simp
    Bb_mul_nonneg := by simp }

example : dirichlet.IsSolution (1) (Real.sin) := by
  refine ⟨Real.contDiff_sin.contDiffOn, fun x hx => ?_, ?_, ?_⟩
  · rw [Operator.applyWithin_eq_apply (_) (uniqueDiffOn_Icc (dirichlet.a_lt_b)) (hx)
      (Real.differentiable_sin) (by simp [dirichlet])]
    simp [dirichlet, Operator.apply]
  all_goals simp [dirichlet, Robin.Operator.SatisfiesWithin, Robin.Operator.applyWithin]

example : ¬ dirichlet.IsSolution (1) (Real.cos) := by
  simp [dirichlet, Problem.IsSolution, Robin.Operator.SatisfiesWithin,
    Robin.Operator.applyWithin]
```

## References

* R. L. Herman, *Introduction to Partial Differential Equations*, §4.1
  "Sturm-Liouville Operators".
-/

@[expose] public section

namespace MathPhysicsTheory.SturmLiouville

/-- The assumptions on the data of a Sturm-Liouville problem on `[a, b]` with operator `L`, weight
`w` and Robin boundary operators `Ba`, `Bb`. -/
structure Assumptions (a b : ℝ) (L : Operator) (w : ℝ → ℝ)
    (Ba Bb : BoundaryConditions.Robin.Operator) : Prop where
  /-- `p` is positive on `[a, b]`. -/
  p_pos : ∀ x ∈ Set.Icc (a) (b), 0 < L.p (x)
  /-- `w` is positive on `[a, b]`. -/
  w_pos : ∀ x ∈ Set.Icc (a) (b), 0 < w (x)
  /-- `p` is continuously differentiable on `[a, b]`. -/
  p_contDiffOn : ContDiffOn (ℝ) (1) (L.p) (Set.Icc (a) (b))
  /-- `q` is continuous on `[a, b]`. -/
  q_continuousOn : ContinuousOn (L.q) (Set.Icc (a) (b))
  /-- `w` is continuous on `[a, b]`. -/
  w_continuousOn : ContinuousOn (w) (Set.Icc (a) (b))
  /-- `q ≤ 0` on `[a, b]`. -/
  q_nonpos : ∀ x ∈ Set.Icc (a) (b), L.q (x) ≤ 0
  /-- `Ba` is imposed at `a`. -/
  Ba_c : Ba.c = a
  /-- `Bb` is imposed at `b`. -/
  Bb_c : Bb.c = b
  /-- `Ba` is nondegenerate: `α` and `β` are not both zero. -/
  Ba_ne : Ba.α ≠ 0 ∨ Ba.β ≠ 0
  /-- `Bb` is nondegenerate: `α` and `β` are not both zero. -/
  Bb_ne : Bb.α ≠ 0 ∨ Bb.β ≠ 0
  /-- `α₁ β₁ ≤ 0` at `a`. -/
  Ba_mul_nonpos : Ba.α * Ba.β ≤ 0
  /-- `α₂ β₂ ≥ 0` at `b`. -/
  Bb_mul_nonneg : 0 ≤ Bb.α * Bb.β

/-- A Sturm-Liouville problem: an interval `[a, b]`, an operator `L`, a weight `w` and Robin
boundary operators `Ba` at `a` and `Bb` at `b`, satisfying the `Assumptions`. -/
structure Problem where
  /-- The left endpoint of the interval. -/
  a : ℝ
  /-- The right endpoint of the interval. -/
  b : ℝ
  /-- The interval is nondegenerate. -/
  a_lt_b : a < b
  /-- The Sturm-Liouville operator. -/
  L : Operator
  /-- The weight (density) function. -/
  w : ℝ → ℝ
  /-- The Robin boundary operator at `a`. -/
  Ba : BoundaryConditions.Robin.Operator
  /-- The Robin boundary operator at `b`. -/
  Bb : BoundaryConditions.Robin.Operator
  /-- The assumptions on the coefficients and boundary operators. -/
  assumptions : Assumptions (a) (b) (L) (w) (Ba) (Bb)

namespace Problem

/-- `y` solves the problem with parameter `λ`: `y` is twice continuously differentiable on
`[a, b]`, `L y = -λ w y` on `[a, b]`, `Ba y = 0` and `Bb y = 0`, with all derivatives taken
within `[a, b]`. -/
def IsSolution (P : Problem) («λ» : ℝ) (y : ℝ → ℝ) : Prop :=
  ContDiffOn (ℝ) (2) (y) (Set.Icc (P.a) (P.b)) ∧
  (∀ x ∈ Set.Icc (P.a) (P.b),
    P.L.applyWithin (Set.Icc (P.a) (P.b)) (y) (x) = -«λ» * P.w (x) * y (x)) ∧
    P.Ba.SatisfiesWithin (Set.Icc (P.a) (P.b)) (0) (y) ∧
    P.Bb.SatisfiesWithin (Set.Icc (P.a) (P.b)) (0) (y)

/-- The trivial solution: `y = 0` solves every Sturm-Liouville problem, for every `λ`. -/
theorem isSolution_zero (P : Problem) : ∀ «λ» : ℝ, P.IsSolution («λ») (0) := by
  intro «λ»
  refine ⟨contDiffOn_const, ?_⟩
  simp [Operator.applyWithin, BoundaryConditions.Robin.Operator.SatisfiesWithin,
    BoundaryConditions.Robin.Operator.applyWithin]

end Problem

end MathPhysicsTheory.SturmLiouville

end
