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

The API docs are a static [Astro](https://astro.build) site in `docs/site/`,
published to GitHub Pages on every push to `main` and built (not deployed) on
pull requests (see `.github/workflows/docs.yml`). They are built in two steps:

1. `docbuild/build_docs.py` runs [doc-gen4](https://github.com/leanprover/doc-gen4)
   on the library's modules to fill its database, then `docbuild/ExportDocs.lean`
   exports that database to `docbuild/.lake/build/docs.json`.
2. The site renders `docs.json`, plus the notes in `docs/notes/`.

To build them locally (needs Node.js, version in `docs/site/.node-version`):

```sh
lake exe cache get
python3 docbuild/build_docs.py
cd docs/site
npm ci
npm run dev       # serve with live reload at http://localhost:4321
npm run build     # or build the site into docs/site/dist
```

`docbuild/` is a separate Lake project so the main package doesn't depend on
doc-gen4. Only `MathPhysicsTheory` is documented (without its linters), not
Mathlib or Lean core; names from those link to the Mathlib docs.
When bumping the Lean/Mathlib version, update `rev` in
`docbuild/lakefile.toml` and `docbuild/lean-toolchain` to match, then run
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4` in `docbuild/`.
doc-gen4's database format is internal, so also check that
`docbuild/ExportDocs.lean` still builds and the docs still render.

### Notes

A module's page can be extended with notes: descriptions, analysis,
derivations and so on. Write them in Markdown at the path mirroring the
module, e.g. `docs/notes/MathPhysicsTheory/SturmLiouville.md` for
`MathPhysicsTheory.SturmLiouville`. They're shown after the module docstring.
Notes, like docstrings, support:

- LaTeX math: `$...$` inline and `$$...$$` for display
- names of declarations in backticks, such as `` `operator_expanded` ``,
  which link to their docs (resolved in the module's namespace)
- code blocks, highlighted as Lean unless another language is given

The build fails on a notes file that doesn't match any documented module.
