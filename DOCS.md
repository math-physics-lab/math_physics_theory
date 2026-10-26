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

## Reading these docs

The documentation is generated from the library's source on every change.

- [**Modules**](MathPhysicsTheory/) lists the library's modules. Each module
  page shows the module's description, then its declarations grouped by kind:
  structures, classes, definitions, theorems, and so on.
- Every declaration shows its full signature, its docstring and a link to its
  source on GitHub. Names in signatures link to their documentation, here or in
  the [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/) for
  names from Mathlib and Lean core.
- Some modules come with notes: derivations, analysis and background that
  don't fit in a docstring.
- Search (press <kbd>/</kbd>) finds declarations and modules by name.

Mathematics is written in LaTeX, for example the Sturm-Liouville operator

$$
L y = \frac{d}{dx}\left(p(x) \frac{dy}{dx}\right) + q(x) y.
$$

## Contributing

The source, build instructions and contribution notes are in the
[repository](https://github.com/math-physics-lab/math_physics_theory). This
page is `DOCS.md` at the root of the repository.
