#!/usr/bin/env python3
"""Export the API docs data for the `MathPhysicsTheory` library to JSON.

doc-gen4's `MathPhysicsTheory:docs` Lake facet documents a library together
with everything it imports, plus Lean core. The library imports all of
Mathlib, so that would mean documenting Mathlib and Lean as well. Instead,
this script drives the doc-gen4 executable directly: it fills the doc
database with our own modules only (skipping the linters in `EXCLUDED`), then
`export-docs` (`ExportDocs.lean`) writes that database to JSON for the Astro
site in `docs/site` to render.

Output: docbuild/.lake/build/docs.json
"""

import os
import subprocess
from pathlib import Path

DOCBUILD = Path(__file__).resolve().parent
ROOT = DOCBUILD.parent
DOCGEN = ROOT / ".lake/packages/doc-gen4/.lake/build/bin/doc-gen4"
BUILD_DIR = Path(".lake/build")  # relative to DOCBUILD
DB = "api-docs.db"  # relative to BUILD_DIR
OUTPUT = "docs.json"  # relative to BUILD_DIR
LIBRARY = "MathPhysicsTheory"
# Module prefixes left out of the docs.
EXCLUDED = ["MathPhysicsTheory.Linter"]


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


def main() -> None:
    run("lake", "build", LIBRARY, "doc-gen4", "export-docs")

    build_dir = DOCBUILD / BUILD_DIR
    for path in [*build_dir.glob(DB + "*"), build_dir / OUTPUT]:
        path.unlink(missing_ok=True)
    # doc-gen4 doesn't create the directory it puts its database in.
    build_dir.mkdir(parents=True, exist_ok=True)

    run(*docgen("bibPrepass", "--build", str(BUILD_DIR), "--none"))

    src_url = source_url()
    for module, file in library_modules():
        print(f"Documenting {module}", flush=True)
        run(*docgen("single", "--build", str(BUILD_DIR), module, DB, f"{src_url}/{file}"))

    run("lake", "exe", "export-docs", str(BUILD_DIR / DB), LIBRARY, str(BUILD_DIR / OUTPUT))


if __name__ == "__main__":
    main()
