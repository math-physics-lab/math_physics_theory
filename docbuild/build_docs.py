#!/usr/bin/env python3
"""Generate the API docs for the `MathPhysicsTheory` library.

doc-gen4's `MathPhysicsTheory:docs` Lake facet documents a library together
with everything it imports. The library imports all of Mathlib, so that would
mean documenting Mathlib as well. Instead, this script drives the doc-gen4
executable directly: it fills the doc database with Lean core (so `Nat`,
`List`, ... links resolve) and our own modules, then renders HTML from it.
Names from Mathlib are shown without links.

The Lean core part takes several minutes but depends only on the toolchain
and the doc-gen4 version, so it is kept in `.lake/build/core-docs.db` and
reused (CI caches it). Delete that file to regenerate it.

Output: docbuild/.lake/build/doc (serve it over HTTP, e.g.
`python3 -m http.server -d docbuild/.lake/build/doc`).
"""

import os
import re
import shutil
import sqlite3
import subprocess
from pathlib import Path

DOCBUILD = Path(__file__).resolve().parent
ROOT = DOCBUILD.parent
DOCGEN = ROOT / ".lake/packages/doc-gen4/.lake/build/bin/doc-gen4"
BUILD_DIR = Path(".lake/build")  # relative to DOCBUILD
# Database paths passed to doc-gen4 are relative to BUILD_DIR.
CORE_DB = "core-docs.db"
DB = "api-docs.db"
CORE_MODULES = ["Init", "Std", "Lake", "Lean"]
MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs/"


def run(*args: str) -> None:
    subprocess.run(args, cwd=DOCBUILD, check=True)


def docgen(*args: str) -> list[str]:
    return ["lake", "env", str(DOCGEN), *args]


def copy_db(src: Path, dst: Path) -> None:
    """Copy an SQLite database, including any pending write-ahead log."""
    with sqlite3.connect(src) as s, sqlite3.connect(dst) as d:
        s.backup(d)


def remove(pattern: str) -> None:
    for path in (DOCBUILD / BUILD_DIR).glob(pattern):
        if path.is_dir():
            shutil.rmtree(path)
        else:
            path.unlink()


def build_core_db() -> None:
    print("Documenting Lean core", flush=True)
    tmp = CORE_DB + ".tmp"
    remove(tmp + "*")
    procs = [
        subprocess.Popen(docgen("genCore", "--build", str(BUILD_DIR), module, tmp), cwd=DOCBUILD)
        for module in CORE_MODULES
    ]
    for proc in procs:
        if proc.wait() != 0:
            raise subprocess.CalledProcessError(proc.returncode, proc.args)
    copy_db(DOCBUILD / BUILD_DIR / tmp, DOCBUILD / BUILD_DIR / CORE_DB)
    remove(tmp + "*")


def source_url() -> str:
    """Source links point at this commit on GitHub."""
    server = os.environ.get("GITHUB_SERVER_URL", "https://github.com")
    repo = os.environ.get("GITHUB_REPOSITORY", "math-physics-lab/math_physics_theory")
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout.strip()
    return f"{server}/{repo}/blob/{commit}"


def library_files() -> list[str]:
    files = [ROOT / "MathPhysicsTheory.lean", *(ROOT / "MathPhysicsTheory").rglob("*.lean")]
    return sorted(f.relative_to(ROOT).as_posix() for f in files)


def link_mathlib_imports() -> None:
    """Mathlib modules have no local pages; send import links to the Mathlib docs."""
    pattern = re.compile(r'href="(?:\.\./)*\./Mathlib([./])')
    doc = DOCBUILD / BUILD_DIR / "doc"
    for page in [doc / "MathPhysicsTheory.html", *(doc / "MathPhysicsTheory").rglob("*.html")]:
        html = page.read_text(encoding="utf-8")
        page.write_text(pattern.sub(rf'href="{MATHLIB_DOCS}Mathlib\1', html), encoding="utf-8")


def main() -> None:
    run("lake", "build", "MathPhysicsTheory", "doc-gen4")
    # doc-gen4 doesn't create the directory it puts its database in.
    (DOCBUILD / BUILD_DIR).mkdir(parents=True, exist_ok=True)

    if not (DOCBUILD / BUILD_DIR / CORE_DB).exists():
        build_core_db()

    remove("doc")
    remove("doc-data")
    remove(DB + "*")
    copy_db(DOCBUILD / BUILD_DIR / CORE_DB, DOCBUILD / BUILD_DIR / DB)

    run(*docgen("bibPrepass", "--build", str(BUILD_DIR), "--none"))

    src_url = source_url()
    for file in library_files():
        module = file.removesuffix(".lean").replace("/", ".")
        print(f"Documenting {module}", flush=True)
        run(*docgen("single", "--build", str(BUILD_DIR), module, DB, f"{src_url}/{file}"))

    # No module roots: render every module in the database.
    run(*docgen("fromDb", "--build", str(BUILD_DIR), str(BUILD_DIR / DB)))

    link_mathlib_imports()


if __name__ == "__main__":
    main()
