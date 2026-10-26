#!/usr/bin/env python3
"""Generate the API docs for the `MathPhysicsTheory` library.

doc-gen4's `MathPhysicsTheory:docs` Lake facet documents a library together
with everything it imports, plus Lean core. The library imports all of
Mathlib, so that would mean documenting Mathlib and Lean as well. Instead,
this script drives the doc-gen4 executable directly: it fills the doc
database with our own modules only (skipping the linters in `EXCLUDED`) and
renders HTML from it. Names from Lean core and Mathlib are shown without
links, and import links to their modules point to the Mathlib docs, which
also cover Lean core.

Output: docbuild/.lake/build/doc (serve it over HTTP, e.g.
`python3 -m http.server -d docbuild/.lake/build/doc`).
"""

import os
import re
import shutil
import subprocess
from pathlib import Path

DOCBUILD = Path(__file__).resolve().parent
ROOT = DOCBUILD.parent
DOCGEN = ROOT / ".lake/packages/doc-gen4/.lake/build/bin/doc-gen4"
BUILD_DIR = Path(".lake/build")  # relative to DOCBUILD
DB = "api-docs.db"  # relative to BUILD_DIR
LIBRARY = "MathPhysicsTheory"
# Module prefixes left out of the docs.
EXCLUDED = ["MathPhysicsTheory.Linter"]
MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs/"


def run(*args: str) -> None:
    subprocess.run(args, cwd=DOCBUILD, check=True)


def docgen(*args: str) -> list[str]:
    return ["lake", "env", str(DOCGEN), *args]


def is_documented(module: str) -> bool:
    return module.split(".")[0] == LIBRARY and not any(
        module == prefix or module.startswith(prefix + ".") for prefix in EXCLUDED
    )


def source_url() -> str:
    """Source links point at this commit on GitHub."""
    server = os.environ.get("GITHUB_SERVER_URL", "https://github.com")
    repo = os.environ.get("GITHUB_REPOSITORY", "math-physics-lab/math_physics_theory")
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout.strip()
    return f"{server}/{repo}/blob/{commit}"


def library_modules() -> list[tuple[str, str]]:
    """The documented modules, as (module name, path relative to ROOT)."""
    files = [ROOT / f"{LIBRARY}.lean", *(ROOT / LIBRARY).rglob("*.lean")]
    modules = []
    for file in sorted(f.relative_to(ROOT).as_posix() for f in files):
        module = file.removesuffix(".lean").replace("/", ".")
        if is_documented(module):
            modules.append((module, file))
    return modules


IMPORTS = re.compile(r"(<summary>Imports</summary><ul>)(.*?)(</ul>)", re.S)
IMPORT = re.compile(r'<li><a href="(?:\.\./)*\./([^"]*)\.html">([^<]*)</a></li>')


def fix_imports(html: str) -> str:
    """Drop imports of excluded modules and send other packages to the Mathlib docs."""

    def fix_import(m: re.Match[str]) -> str:
        path, module = m.groups()
        if module.split(".")[0] == LIBRARY:
            return m.group(0) if is_documented(module) else ""
        return f'<li><a href="{MATHLIB_DOCS}{path}.html">{module}</a></li>'

    return IMPORTS.sub(lambda m: m[1] + IMPORT.sub(fix_import, m[2]) + m[3], html)


def main() -> None:
    run("lake", "build", LIBRARY, "doc-gen4")

    build_dir = DOCBUILD / BUILD_DIR
    for path in ["doc", "doc-data"]:
        shutil.rmtree(build_dir / path, ignore_errors=True)
    for path in build_dir.glob(DB + "*"):
        path.unlink()
    # doc-gen4 doesn't create the directory it puts its database in.
    build_dir.mkdir(parents=True, exist_ok=True)

    run(*docgen("bibPrepass", "--build", str(BUILD_DIR), "--none"))

    src_url = source_url()
    for module, file in library_modules():
        print(f"Documenting {module}", flush=True)
        run(*docgen("single", "--build", str(BUILD_DIR), module, DB, f"{src_url}/{file}"))

    # No module roots: render every module in the database.
    run(*docgen("fromDb", "--build", str(BUILD_DIR), str(BUILD_DIR / DB)))

    doc = build_dir / "doc"
    for page in [doc / f"{LIBRARY}.html", *(doc / LIBRARY).rglob("*.html")]:
        page.write_text(fix_imports(page.read_text(encoding="utf-8")), encoding="utf-8")


if __name__ == "__main__":
    main()
