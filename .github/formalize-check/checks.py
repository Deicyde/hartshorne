"""Source inventory, exact contract, and all-public unused-hypothesis checks."""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from autoform_cli.lean import bind_project_sources
from autoform_cli import skeleton as sk
from autoform_cli import unused_hypotheses as uh

MODULE = "src/Hartshorne/Scheme/ModuleSheafHom.lean"
FROZEN = {
    MODULE: "709c2b4a95e6d17039c6300037e81f811e1fa834f031ffc0502a55324069e44d",
    "src/Hartshorne.lean": "351bc03697a839df42f090408e593e01b8f2bb352dcaee421b24c02533464db7",
    "blueprint/roadmap/schemes/modules-and-quasicoherent/module-sheaf-hom.md":
        "3bf7850e67dde2c6e60ecbd9353559b2d2af883c5d8c4d56722b8a2b9d122a8e",
    "lakefile.toml": "b6d19119e408264abfa097303402b430851c2a8ee6ee6d081055f2dcbb3458b9",
    "lake-manifest.json": "9c57ac5bbc6130385b19572b003bbe91161040f432cb0cb9f99a903bd6ccbd31",
    "lean-toolchain": "3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71",
    ".github/autoform_audit.py": "5ca1e1ea1c8a94a9faaf18e75206188060e381d38974e3986b11c07734b42ab3",
}
CONTRACT = """import Hartshorne.Scheme.ModuleSheafHom
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe u
namespace Hartshorne
noncomputable example (X : Scheme.{u}) : ModuleSheafHomData X := moduleSheafHomData X
example (X : Scheme.{u}) (d : ModuleSheafHomData X) (F G : X.Modules)
    (σ : Γ(d.obj F G, ⊤)) (V : X.Opens) (x : Γ(F, V)) :
    (d.globalSections F G σ).val.app (op V) x =
      (d.overSections F G ⊤ σ).val.app
        (op (Over.mk (homOfLE (show V ≤ ⊤ from le_top)))) x :=
  d.global_app F G σ V x
#check moduleSheafHom
#check moduleSheafHomSectionsAddEquiv
#check moduleSheafHomGlobalSectionsLinearEquiv
#check module_sheaf_hom_sections_smul_app
#check module_sheaf_hom_sections_restrict
#check module_sheaf_hom_global_map
#print axioms moduleSheafHomData
#print axioms moduleSheafHom
#print axioms module_sheaf_hom_sections_restrict
#print axioms module_sheaf_hom_global_map
end Hartshorne
"""


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def frozen():
    for path, expected in FROZEN.items():
        require(hashlib.sha256(Path(path).read_bytes()).hexdigest() == expected,
                f"candidate source changed: {path}")


def main():
    root = Path.cwd().resolve(strict=True)
    mode, destination = sys.argv[1], Path(sys.argv[2])
    require(destination.is_absolute() and not destination.exists(), "require a fresh absolute output path")
    frozen()
    with bind_project_sources(root) as bound:
        capture = bound.capture()
        if mode == "inventory":
            libraries = sk.lean_libraries(root)
            modules = []
            mathlib = set()
            imports = {}
            for path, content in capture.source_files:
                module = sk.module_of(root / path, libraries)
                if module is None:
                    continue
                modules.append(module)
                imports[module] = []
                for line in content.decode("utf-8").splitlines():
                    if not line.lstrip().startswith("import "):
                        continue
                    match = re.fullmatch(r"\s*import\s+([A-Za-z0-9_'.]+)\s*(?:--.*)?", line)
                    require(match is not None, f"unsupported import syntax in {path}")
                    imports[module].append(match[1])
                    if match[1] == "Mathlib" or match[1].startswith("Mathlib."):
                        mathlib.add(match[1])
            require(modules and mathlib and len(modules) == len(set(modules)), "invalid source import inventory")
            local = set(modules)
            ordered = []
            visiting = set()
            visited = set()

            def visit(module):
                require(module not in visiting, "local module import cycle")
                if module in visited:
                    return
                visiting.add(module)
                for dependency in imports[module]:
                    if dependency in local:
                        visit(dependency)
                visiting.remove(module)
                visited.add(module)
                ordered.append(module)

            for module in sorted(local):
                visit(module)
            require(set(ordered) == local and len(ordered) == len(local), "incomplete module build order")
            destination.write_text(json.dumps({
                "schema": "hartshorne-source-inventory/v1", "source_revision": capture.revision,
                "generation": capture.generation_revision, "local_modules": sorted(modules),
                "mathlib_imports": sorted(mathlib), "frozen": FROZEN,
                "local_build_order": ordered,
            }, indent=2) + "\n")
        elif mode == "contract":
            destination.write_text(CONTRACT)
        elif mode == "seed":
            seed = Path(os.environ["HARTSHORNE_SOURCE_SEED"])
            archive = seed / "root-build-seed.tgz"
            digest = hashlib.sha256()
            with archive.open("rb") as saved:
                for block in iter(lambda: saved.read(1024 * 1024), b""):
                    digest.update(block)
            expected = "a59dd76dde397d3b20186c36524c003b195b7198da1e30fac9a581c46a90cf2e"
            require(digest.hexdigest() == expected, "saved root seed hash differs")
            inventory = json.loads((seed / "source-inventory.json").read_text())
            require(inventory["source_revision"] == capture.revision, "saved seed source differs")
            # Markdown assertions are checked by frozen() on the current
            # candidate; they are not inputs to these compiled Lean artifacts.
            compiled = {key: value for key, value in FROZEN.items() if not key.endswith(".md")}
            saved_compiled = {key: value for key, value in inventory["frozen"].items() if not key.endswith(".md")}
            require(saved_compiled == compiled, "saved seed compiled project controls differ")
            destination.write_text(json.dumps({"schema": "hartshorne-build-seed/v1", "sha256": expected,
                                               "source_revision": capture.revision, "acceptance": None}) + "\n")
        elif mode == "controls":
            forbidden = "skip" + "KernelTC"
            result = subprocess.run(["git", "grep", "-n", "-I", forbidden, "--", "."],
                                    cwd=root, capture_output=True, text=True, timeout=30)
            require(result.returncode == 1, "tracked kernel-check bypass found or tracked scan failed")
            destination.write_text(json.dumps({"schema": "hartshorne-tracked-controls/v1", "status": "PASS"}) + "\n")
        elif mode == "packages":
            manifest = json.loads(Path("lake-manifest.json").read_text())
            rows = []
            for package in manifest["packages"]:
                directory = root / manifest["packagesDir"] / package["name"]
                require(directory.is_dir() and not directory.is_symlink(), "package is missing or symlinked")
                result = subprocess.run(["git", "--no-replace-objects", "rev-parse", "HEAD"],
                                        cwd=directory, capture_output=True, text=True, check=True, timeout=30)
                require(result.stdout.strip() == package["rev"], f"package pin changed: {package['name']}")
                clean = subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=directory, timeout=30)
                require(clean.returncode == 0, f"tracked package source differs: {package['name']}")
                rows.append({"name": package["name"], "revision": package["rev"]})
            destination.write_text(json.dumps({"schema": "hartshorne-package-pins/v1", "packages": rows}, indent=2) + "\n")
        elif mode == "pack-scope":
            spec = importlib.util.spec_from_file_location("hartshorne_tracked_audit", root / ".github/autoform_audit.py")
            audit = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(audit)
            modules = audit.modules_from_archive(destination.parent / "root-build.tgz", "Hartshorne")
            inventory = json.loads((destination.parent / "source-inventory.json").read_text())
            require(set(modules) == set(inventory["local_modules"]), "root pack omitted or added source modules")
            require(inventory["source_revision"] == capture.revision, "source inventory became stale")
            destination.write_text(json.dumps({"schema": "hartshorne-root-pack-scope/v1", "module_count": len(modules),
                                               "modules": list(modules)}, indent=2) + "\n")
        elif mode == "unused":
            files = {path: content.decode("utf-8").splitlines() for path, content in capture.source_files}
            chosen = {Path(MODULE), Path("src/Hartshorne/Scheme/AbelianSheafHom.lean")}
            names = tuple(sorted(declaration.name for declaration in capture.index.declarations.values()
                                 if declaration.path in chosen and declaration.keyword in ("theorem", "lemma")
                                 and not files[declaration.path][declaration.line - 1].lstrip().startswith("private ")))
            require(names, "no public theorem declarations found")
            roots = (*names, "Hartshorne.moduleSheafHomData")
            output = sk.run_probe(uh.render_probe(imports=("Hartshorne.Scheme.ModuleSheafHom",), roots=roots),
                                  root, timeout=600, label="all-public unused-hypotheses probe")
            records = uh.parse_probe_output(output, expected_roots=roots)
            require(all(row["found"] for row in records.values()), "an all-public declaration was unresolved")
            require(all(records[name]["proof"] == "proved" for name in names), "a public theorem proof was not read")
            findings = [{"declaration": name, "hypothesis": hypothesis.as_dict()}
                        for name, row in records.items()
                        for hypothesis in uh._hypotheses(row.get("hypotheses", []), root=name) if not hypothesis.used]
            destination.write_text(json.dumps({
                "schema": "hartshorne-all-public-unused/v1", "source_revision": capture.revision,
                "requests": list(roots), "records": records, "findings": findings,
            }, indent=2) + "\n")
            require(not findings, "unused public hypotheses require review")
        else:
            raise ValueError("unknown check mode")
        after = bound.capture()
        require((capture.revision, capture.generation_revision) == (after.revision, after.generation_revision),
                "source generation changed during check")
        bound.verify()
    frozen()


if __name__ == "__main__":
    main()
