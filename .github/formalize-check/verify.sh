#!/usr/bin/env bash
set -euo pipefail

controls="$PWD/.github/formalize-check"
evidence="${RUNNER_TEMP:?}/hartshorne-formalize-evidence"
mkdir "$evidence"
mkdir "$evidence/stages"
stage() {
  name=$1
  shift
  python "$controls/guard_linux.py" "$evidence/stages/$name.json" -- "$@"
}

stage guard-calibration python -c 'import time; payload=bytearray(16*1024*1024); time.sleep(0.5); print(len(payload))'
stage source-inventory python "$controls/checks.py" inventory "$evidence/source-inventory.json"
stage tracked-controls python "$controls/checks.py" controls "$evidence/tracked-controls.json"
mapfile -t mathlib_targets < <(python -c 'import json,sys; print("\n".join(json.load(open(sys.argv[1]))["mathlib_imports"]))' "$evidence/source-inventory.json")
test "${#mathlib_targets[@]}" -gt 0
stage prebuilt-cache lake exe cache get
stage pinned-packages python "$controls/checks.py" packages "$evidence/package-pins.json"
stage cached-theory-freshness lake --rehash --no-build build "${mathlib_targets[@]}"
stage focused-build lake build Hartshorne.Scheme.ModuleSheafHom
stage default-build lake build
stage final-default-freshness lake --rehash --no-build build
stage final-pinned-packages python "$controls/checks.py" packages "$evidence/final-package-pins.json"

stage exact-contract-source python "$controls/checks.py" contract "$evidence/Contract.lean"
stage exact-contract lake env lean "$evidence/Contract.lean"
stage all-public-unused python "$controls/checks.py" unused "$evidence/all-public-unused.json"
stage full-extraction python "$controls/extract_full.py" "$evidence/full-extraction"

stage evaluate-config lake translate-config toml "$evidence/lake-config.toml"
stage root-package python .github/autoform_audit.py --root-package "$evidence/lake-config.toml"
root_package=$(cat "$evidence/stages/root-package.stdout")
test "$root_package" = Hartshorne
stage actual-root-pack lake pack "$evidence/root-build.tgz"
stage exact-root-pack-scope python "$controls/checks.py" pack-scope "$evidence/root-pack-scope.json"
stage prepare-root-audit python .github/autoform_audit.py "$root_package" "$evidence/root-build.tgz" "$evidence/WholeRoot.lean"
stage whole-root-safety-axioms lake env lean "$evidence/WholeRoot.lean"
stage blueprint-check autoform check blueprint --lean-root .
stage blueprint-audit autoform audit blueprint --lean-root .

stage immutable-blueprint-check env -u PYTHONPATH uvx --from git+https://github.com/facebookresearch/autoform-bot.git@1cf2ca825fec5e6d3303e24374e218bf3e8ab5c1 autoform check blueprint --lean-root .
stage immutable-blueprint-audit env -u PYTHONPATH uvx --from git+https://github.com/facebookresearch/autoform-bot.git@1cf2ca825fec5e6d3303e24374e218bf3e8ab5c1 autoform audit blueprint --lean-root .

python - "$evidence" <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1])
entries = []
for path in sorted(root.rglob("*")):
    if path.is_symlink():
        raise RuntimeError("evidence contains a symlink")
    if path.is_file():
        digest = hashlib.sha256()
        with path.open("rb") as source:
            for block in iter(lambda: source.read(1024 * 1024), b""):
                digest.update(block)
        entries.append({"path": path.relative_to(root).as_posix(), "bytes": path.stat().st_size, "sha256": digest.hexdigest()})
(root / "evidence-manifest.json").write_text(json.dumps({"schema": "hartshorne-verification-evidence/v1", "execution_status": "PASS", "mathematical_verdict": None, "entries": entries}, indent=2) + "\n")
PY
echo 'Verification execution passed; independent mathematical review remains required.'
