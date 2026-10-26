# Mathematical Physics Theory

A Lean library of definitions and theorems from mathematical physics.

## Building

Install Lean via [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get   # download prebuilt Mathlib
lake build --wfail   # build, failing on any warning or linter finding
```

## Tests

Tests live in `tests/`:

```sh
lake test --wfail
```

## Documentation

API docs are an [Astro](https://astro.build) site in `docs/site/`, deployed to
GitHub Pages from `main` (`.github/workflows/docs.yml`). `docbuild/` (a separate
Lake project) runs [doc-gen4](https://github.com/leanprover/doc-gen4) and exports
`docs.json`; the site renders it with the module notes. The front page is
`docs/ROOT.md`.

Build locally (Node.js version in `docs/site/.node-version`):

```sh
lake exe cache get
python3 docbuild/build_docs.py
cd docs/site && npm ci
npm run dev       # live reload at http://localhost:4321; or `npm run build`
```

When bumping Lean/Mathlib, match `rev` in `docbuild/lakefile.toml` and
`docbuild/lean-toolchain`, run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4`
in `docbuild/`, and check the docs still render.

### Notes

Notes for module `A.B` go in `A/B/NOTE.md`, next to `A/B.lean`. They're shown
after the module docstring and support `$...$`/`$$...$$` math, `` `name` `` links
to declarations, and Lean code blocks. A `NOTE.md` without a matching module
fails the build.
