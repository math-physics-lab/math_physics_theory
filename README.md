# Mathematical Physics Theory

A Lean library of definitions and theorems from mathematical physics.

## Building

Install Lean via [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get   # download prebuilt Mathlib
lake build --wfail   # build, failing on any warning or linter finding
```

## Tests

Tests live in `tests/` as the package's test driver library. Each file
imports the library.
Run with:

```sh
lake test --wfail
```

## Documentation

API docs are generated with [doc-gen4](https://github.com/leanprover/doc-gen4)
and published to GitHub Pages on every push to `main`
(see `.github/workflows/docs.yml`). To build them locally:

```sh
lake exe cache get
python3 docbuild/build_docs.py
python3 -m http.server -d docbuild/.lake/build/doc
```

`docbuild/` is a separate Lake project so the main package doesn't depend on
doc-gen4. Only `MathPhysicsTheory` (and Lean core) is documented, not Mathlib.
When bumping the Lean/Mathlib version, update `rev` in
`docbuild/lakefile.toml` and `docbuild/lean-toolchain` to match, then run
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4` in `docbuild/`.
