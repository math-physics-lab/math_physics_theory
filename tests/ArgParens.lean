import MathPhysicsTheory

/-! Tests for the `argParens` linter. -/

/--
warning: Function arguments should be written in parentheses: `(x)`.

Note: This linter can be disabled with `set_option linter.argParens false`
-/
#guard_msgs in
example (f : ℝ → ℝ) (x : ℝ) : ℝ := f x

/--
warning: Function arguments should be written in parentheses: `(a)`.

Note: This linter can be disabled with `set_option linter.argParens false`
---
warning: Function arguments should be written in parentheses: `(b)`.

Note: This linter can be disabled with `set_option linter.argParens false`
-/
#guard_msgs in
example (a b : ℕ) : Set (ℕ) := Set.Icc a b

/--
warning: Function arguments should be written in parentheses: `(n)`.

Note: This linter can be disabled with `set_option linter.argParens false`
-/
#guard_msgs in
example (g : ℕ → ℕ) (n : ℕ) : ℕ := g (g n)

-- Bracketed arguments are accepted.
#guard_msgs in
noncomputable example (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x) + deriv (f) (x) + Real.sin (x + 1)

-- Type ascriptions, tuples, anonymous constructors and lists count as bracketed.
#guard_msgs in
example (g : ℕ × ℕ → ℕ) (h : List (ℕ) → ℕ) (n : ℕ) : ℕ :=
  g ((n, n)) + g ⟨n, n⟩ + h [n] + g (⟨n, n⟩ : ℕ × ℕ)
