"""Read-only import-graph reconciliation for the Lean project.

Usage: D:\\miniconda3\\python.exe experiments/lean_import_graph.py
Prints: module count, direct facade imports, modules with no importer (LEAF),
and modules whose file is missing (dangling imports).
"""
import os
import re
import sys

PROJ = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                    "..", "theory", "jin_wishart_formalization")
MODDIR = os.path.join(PROJ, "JinWishartFormalization")
FACADE = os.path.join(PROJ, "JinWishartFormalization.lean")


def main() -> int:
    files = sorted(f[:-5] for f in os.listdir(MODDIR) if f.endswith(".lean"))
    imports = {}
    for name in files:
        with open(os.path.join(MODDIR, name + ".lean"), encoding="utf-8") as fh:
            imports[name] = set(re.findall(r"import JinWishartFormalization\.(\w+)", fh.read()))
    with open(FACADE, encoding="utf-8") as fh:
        facade = set(re.findall(r"import JinWishartFormalization\.(\w+)", fh.read()))
    # The facade counts as an importer too, otherwise its 84 imports look like leaves.
    imports["<facade>"] = facade

    print("modules on disk      :", len(files))
    print("facade direct imports:", len(facade))
    dangling = sorted(facade - set(files))
    print("import without file  :", ", ".join(dangling) if dangling else "(none)")
    leaves = sorted(n for n in files
                    if not any(n in imps for f, imps in imports.items() if f != n))
    print("leaf (no importers)  :", ", ".join(leaves) if leaves else "(none)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
