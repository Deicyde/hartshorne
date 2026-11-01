"""Fresh original Autoform extraction with approved limits and complete artifact binding."""

import functools
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys

from autoform_cli import __main__ as entrypoint
from autoform_cli import skeleton as sk
from autoform_cli.graph import load_graph
from autoform_cli.lean import bind_project_sources
from checks import frozen

NODE = "schemes/modules-and-quasicoherent/module-sheaf-hom"
ORIGINAL_DECODER = "4fd33f54f4863e4c342b5fea942f7a18c5199323f069ff40215913ff868021ff"
OUTPUT_LIMIT = 256 * 1024**2


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def hash_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def generation(metadata):
    return (metadata.st_dev, metadata.st_ino, metadata.st_size,
            metadata.st_mtime_ns, metadata.st_ctime_ns)


def fingerprint(path, required):
    parent = path.parent.resolve(strict=True)
    parent_stat = parent.stat()
    try:
        before = path.lstat()
    except FileNotFoundError:
        require(not required, f"missing required artifact {path}")
        final_parent = path.parent.resolve(strict=True)
        final_parent_stat = final_parent.stat()
        require(final_parent == parent and (final_parent_stat.st_dev, final_parent_stat.st_ino) ==
                (parent_stat.st_dev, parent_stat.st_ino), "optional artifact parent changed")
        try:
            path.lstat()
        except FileNotFoundError:
            pass
        else:
            raise RuntimeError("optional artifact appeared during absent capture")
        return {"path": str(path), "status": "optional-absent", "parent": str(parent),
                "parent_identity": [parent_stat.st_dev, parent_stat.st_ino]}
    require(stat.S_ISREG(before.st_mode), f"artifact is not a non-symlink regular file {path}")
    canonical = path.resolve(strict=True)
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC)
    try:
        require(generation(os.fstat(descriptor)) == generation(before), "artifact changed on open")
        digest = hashlib.sha256()
        size = 0
        while True:
            block = os.read(descriptor, 1024 * 1024)
            if not block:
                break
            size += len(block)
            digest.update(block)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    final_parent = path.parent.resolve(strict=True)
    final_parent_stat = final_parent.stat()
    require(generation(before) == generation(after) == generation(path.lstat()), "artifact changed while hashing")
    require(size == before.st_size and path.resolve(strict=True) == canonical, "artifact read or canonical target changed")
    require(final_parent == parent and (final_parent_stat.st_dev, final_parent_stat.st_ino) ==
            (parent_stat.st_dev, parent_stat.st_ino), "artifact parent identity changed")
    return {"path": str(path), "canonical": str(canonical), "status": "present", "bytes": size,
            "sha256": digest.hexdigest(), "generation": list(generation(before)),
            "parent": str(parent), "parent_identity": [parent_stat.st_dev, parent_stat.st_ino]}


def main():
    require(hash_file(Path(sk.__file__)) == ORIGINAL_DECODER, "original extraction decoder bytes differ")
    frozen()
    root = Path.cwd().resolve(strict=True)
    output = Path(sys.argv[1])
    require(output.is_absolute() and not output.exists(), "output must be a fresh absolute directory")
    require(root not in output.parents and output not in root.parents, "output must be outside the Lean source root")
    output.mkdir(parents=True)
    original_runner = sk.run_probe
    original_command = sk._run_bounded_command
    original_parser = sk.parse_probe_output
    sk.DEFAULT_PROBE_OUTPUT_LIMIT = OUTPUT_LIMIT
    sk._PROBE_MATERIAL_LIMIT = 1024**3
    native_bytes = 0

    @functools.wraps(original_command)
    def bounded(command, **options):
        nonlocal native_bytes
        remaining = OUTPUT_LIMIT - native_bytes
        require(remaining > 0, "cumulative native output budget exhausted")
        options.setdefault("output_limit", remaining)
        result = original_command(command, **options)
        emitted = len(result.stdout.encode("utf-8")) + len(result.stderr.encode("utf-8"))
        records_path = (options.get("env") or {}).get(sk.PROBE_OUTPUT_ENV)
        if records_path is not None:
            try:
                emitted += Path(records_path).stat().st_size
            except FileNotFoundError:
                pass
        native_bytes += emitted
        require(native_bytes <= OUTPUT_LIMIT, "cumulative native console and records output exceeded 256 MiB")
        return result

    sk._run_bounded_command = bounded
    artifacts = []
    native_paths = set()
    captures = []
    metadata_program = """
import Lean.Util.Path
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in env.header.moduleNames do
    let original ← findOLean name
    let canonical ← IO.FS.realPath original
    rows := rows.push <| Json.mkObj [("module", Json.str name.toString),
      ("original_olean", Json.str original.toString), ("olean", Json.str canonical.toString)]
  IO.println ("ARTIFACT_MODULES " ++ (Json.arr rows).compress)
"""

    def current_artifacts():
        return [fingerprint(Path(row["path"]), row["kind"] == "olean") for row in captures]

    def fresh(probe, lean_root, **options):
        require(lean_root.resolve(strict=True) == root, "native run root changed")
        project_imports = sk._probe_modules(probe)
        leading = "\n".join(f"import {name}" for name in project_imports)
        support = "\n".join(line for line in probe.splitlines()
                            if line.startswith("import ") and line.removeprefix("import ").strip() not in project_imports)
        # Stock freshness checks exactly the leading project imports, while
        # metadata loads all of the actual probe's toolchain support modules.
        meta = original_runner(leading + "\n-- Metadata support modules\n" + support +
                               "\n" + metadata_program, lean_root, **options)
        matches = re.findall(r"^ARTIFACT_MODULES (.+)$", meta, re.M)
        require(len(matches) == 1 and "error:" not in meta, "invalid native module metadata")
        rows = json.loads(matches[0])
        require(isinstance(rows, list) and rows, "empty native module closure")
        names = set()
        canonicals = set()
        for row in rows:
            require(isinstance(row, dict) and set(row) == {"module", "original_olean", "olean"}, "invalid module row")
            name = row["module"]
            require(isinstance(name, str) and name and name not in names, "duplicate or invalid module")
            names.add(name)
            native = Path(row["original_olean"])
            if not native.is_absolute():
                native = root / native
            require(native.suffix == ".olean" and native.resolve(strict=True) == Path(row["olean"]), "native module target mismatch")
            canonical = str(native.resolve(strict=True))
            require(canonical not in canonicals, "duplicate native artifact")
            canonicals.add(canonical)
            for kind, path in (("olean", native), ("olean.server", Path(str(native) + ".server")),
                               ("olean.private", Path(str(native) + ".private"))):
                captures.append({"module": name, "kind": kind, "path": str(path)})
                native_paths.add((name, kind, str(path.resolve(strict=False))))
        before = current_artifacts()
        raw = original_runner(probe, lean_root, **options)
        require(current_artifacts() == before, "native artifacts changed during extraction")
        artifacts.extend(before)
        (output / "native-modules.json").write_text(json.dumps(rows, indent=2))
        (output / "fresh-native.records").write_text(raw)
        return raw

    @functools.wraps(original_parser)
    def parse(raw, **options):
        records = original_parser(raw, **options)
        for record in records.values():
            if not record.get("found"):
                continue
            for name, kind, raw_path in sk._module_file_entries(record.get("boundary_modules"), context="full extraction"):
                path = (root / raw_path).resolve(strict=True)
                require((name, kind, str(path)) in native_paths, "native boundary escaped the captured module closure")
        return records

    sk.run_probe = entrypoint.run_probe = fresh
    sk.parse_probe_output = parse
    graph = load_graph(root / "blueprint")
    controls = sk.snapshot_inputs(graph, root)
    with bind_project_sources(root) as bound:
        source = bound.capture()
        result = entrypoint.main([
            "skeleton", "blueprint", "--lean-root", str(root), "--node", NODE,
            "--timeout", "600", "--output", str(output / "report.json"),
            "--packets", str(output / "packets"), "--passages", str(output / "passages"),
        ])
        require(result == 0 and artifacts, "full original extraction was incomplete")
        require(current_artifacts() == artifacts, "artifacts changed during strict parse or publication")
        recapture = bound.capture()
        require((source.revision, source.generation_revision) ==
                (recapture.revision, recapture.generation_revision), "source generation changed")
        sk.check_inputs_unchanged(graph, root, source.index, controls, activity="full Linux extraction")
        bound.verify()
    frozen()
    require((output / "packets/manifest.json").is_file() and
            (output / "passages/manifest.json").is_file(), "complete managed manifests missing")
    (output / "binding.json").write_text(json.dumps({
        "schema": "hartshorne-full-extraction-binding/v1", "status": "PASS", "final_verdict": None,
        "decoder_sha256": ORIGINAL_DECODER, "source_revision": source.revision,
        "source_generation": source.generation_revision,
        "report_sha256": hash_file(output / "report.json"), "artifacts": artifacts,
        "cumulative_native_output_bytes": native_bytes,
    }, indent=2) + "\n")


if __name__ == "__main__":
    main()
