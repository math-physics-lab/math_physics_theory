module

public import Mathlib
public import MathPhysicsTheory.BoundaryConditions.Robin

-- Linter: requires function arguments to be written in parentheses, `f (x)`.
import MathPhysicsTheory.Linter.ArgParens

/-!
# Sturm-Liouville problems

A Sturm-Liouville problem on an interval `[a, b]`, with coefficients `p`, `q`, a weight `w` and
`p > 0`, `w > 0` on `[a, b]`, asks for the functions `y` and numbers `λ` with

* `(p y')' + q y = -λ w y` on `[a, b]`,
* `α₁ y(a) + β₁ y'(a) = 0` and `α₂ y(b) + β₂ y'(b) = 0`.

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
  p_pos := fun _ _ => by simp
  w_pos := fun _ _ => by simp
  Ba := { α := 1, β := 0, c := 0 }
  Bb := { α := 1, β := 0, c := Real.pi }
  Ba_c := rfl
  Bb_c := rfl

example : dirichlet.IsSolution (1) (Real.sin) := by
  simp [dirichlet, Problem.IsSolution, Operator.apply, Robin.Operator.condition,
    Robin.Operator.apply]

example : ¬ dirichlet.IsSolution (1) (Real.cos) := by
  simp [dirichlet, Problem.IsSolution, Robin.Operator.condition, Robin.Operator.apply]
```

## References

* R. L. Herman, *Introduction to Partial Differential Equations*, §4.1
  "Sturm-Liouville Operators".
-/

@[expose] public section

namespace MathPhysicsTheory.SturmLiouville

/-- A Sturm-Liouville operator, given by its coefficients `p` and `q` in
`L y = d/dx (p(x) y'(x)) + q(x) y(x)`. -/
structure Operator where
  /-- The coefficient inside the derivative. -/
  p : ℝ → ℝ
  /-- The potential. -/
  q : ℝ → ℝ

namespace Operator

/-- The Sturm-Liouville differential expression `L y = d/dx (p(x) y'(x)) + q(x) y(x)`. -/
noncomputable def apply (L : Operator) (y : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv (fun x => L.p (x) * deriv (y) (x)) (x) + L.q (x) * y (x)

/-- Expanded form of the Sturm-Liouville operator: `L y = p y'' + p' y' + q y`. -/
theorem apply_expanded (L : Operator) {y : ℝ → ℝ} (hp : Differentiable (ℝ) (L.p))
    (hy : Differentiable (ℝ) (deriv (y))) :
    L.apply (y) =
      fun x => L.p (x) * deriv (deriv (y)) (x) + deriv (L.p) (x) * deriv (y) (x) +
        L.q (x) * y (x) := by
  funext x
  have h : HasDerivAt (fun t => L.p (t) * deriv (y) (t))
      (deriv (L.p) (x) * deriv (y) (x) + L.p (x) * deriv (deriv (y)) (x)) (x) :=
    (hp (x)).hasDerivAt.mul ((hy (x)).hasDerivAt)
  rw [apply, h.deriv]
  ring

end Operator

/-- A Sturm-Liouville problem: an interval `[a, b]`, an operator `L`, a weight `w` and Robin
boundary operators `Ba` at `a` and `Bb` at `b`, with `p > 0` and `w > 0` on `[a, b]`. -/
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
  /-- `p` is positive on `[a, b]`. -/
  p_pos : ∀ x ∈ Set.Icc (a) (b), 0 < L.p (x)
  /-- `w` is positive on `[a, b]`. -/
  w_pos : ∀ x ∈ Set.Icc (a) (b), 0 < w (x)
  /-- The Robin boundary operator at `a`. -/
  Ba : BoundaryConditions.Robin.Operator
  /-- The Robin boundary operator at `b`. -/
  Bb : BoundaryConditions.Robin.Operator
  /-- `Ba` is imposed at `a`. -/
  Ba_c : Ba.c = a
  /-- `Bb` is imposed at `b`. -/
  Bb_c : Bb.c = b

namespace Problem

/-- `y` solves the problem with parameter `λ`: `L y = -λ w y` on `[a, b]`, `Ba y = 0` and
`Bb y = 0`. -/
def IsSolution (P : Problem) («λ» : ℝ) (y : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc (P.a) (P.b), P.L.apply (y) (x) = -«λ» * P.w (x) * y (x)) ∧
    P.Ba.condition (0) (y) ∧ P.Bb.condition (0) (y)

/-- The trivial solution: `y = 0` solves every Sturm-Liouville problem, for every `λ`. -/
theorem isSolution_trivial (P : Problem) : ∀ «λ» : ℝ, P.IsSolution («λ») (0) := by
  intro «λ»
  simp [IsSolution, Operator.apply, BoundaryConditions.Robin.Operator.condition,
    BoundaryConditions.Robin.Operator.apply]

end Problem

end MathPhysicsTheory.SturmLiouville

end
