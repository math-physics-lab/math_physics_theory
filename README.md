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
