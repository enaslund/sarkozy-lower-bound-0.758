#!/usr/bin/env bash
set -euo pipefail

# Judge Solution against Challenge with the comparator bundled in the pinned
# Lean toolchain, as Palomar's verifier does since Lean v4.35.0-rc2: Lean's
# kernel plus the bundled NanoDa and con-ron kernels must all accept both
# selected theorems, using only the permitted axioms.
#
# `lake comparator` builds and exports the project inside a bubblewrap
# sandbox, so `bwrap` must be installed and able to create user namespaces.
# Palomar additionally replaces the Challenge with its canonical, protected
# copy; that step exists only in the hosted verifier.

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_command in bwrap lake python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run the comparator" >&2
    exit 1
  fi
done

config=$(mktemp "${TMPDIR:-/tmp}/sarkozy-comparator.XXXXXX.json")
trap 'rm -f "$config"' EXIT

# Same modules, theorems and axioms as comparator.json; the kernels are those
# Palomar registers (con-ron with two jobs).
python3 - comparator.json "$config" <<'PY'
import json
import sys

source, destination = sys.argv[1:]
config = json.load(open(source, encoding="utf-8"))
if config.get("enable_nanoda") is not True:
    raise SystemExit(f"error: {source}: enable_nanoda must be exactly true")
protected = {key: config[key] for key in (
    "challenge_module", "solution_module", "theorem_names", "permitted_axioms")}
protected["definition_names"] = config.get("definition_names", [])
protected["external_kernels"] = {"nanoda": ["nanoda_bin"], "con-ron": ["con-ron", "--jobs=2"]}
json.dump(protected, open(destination, "w", encoding="utf-8"), indent=2)
PY

lake comparator --config "$config"
