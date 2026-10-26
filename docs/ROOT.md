# MathPhysicsTheory

A [Lean 4](https://lean-lang.org) library of definitions and theorems from
mathematical physics, built on [Mathlib](https://github.com/leanprover-community/mathlib4).
The aim is to state the objects physicists work with, such as distances,
differential operators and boundary value problems, precisely enough for Lean
to check the mathematics behind them.

## Using the library

Add it to your Lake project's `lakefile.toml`:

```toml
[[require]]
name = "MathPhysicsTheory"
git = "https://github.com/math-physics-lab/math_physics_theory"
rev = "main"
```

and import it with `import MathPhysicsTheory`. The library pins its Lean and
Mathlib versions, so use the same Lean toolchain as the library.

