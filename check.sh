#!/usr/bin/env bash
# Verify tactus-computability-theory under the Lean backend, importing the
# group-theory export (verus_group_theory.vir/.rlib from ../tactus-group-theory).
#
#   ./check.sh                  # whole crate
#   ./check.sh --verify-module M   # one module
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERUS="$HERE/../tactus/source/target-verus/release/verus"
GT="$HERE/../tactus-group-theory/export"

if [[ ! -f "$GT/verus_group_theory.vir" || ! -f "$GT/libverus_group_theory.rlib" ]]; then
  echo "building group-theory export first..." >&2
  "$HERE/../tactus-group-theory/build-export.sh" >/dev/null
fi

exec "$VERUS" --lean-backend --crate-type=lib \
  --import verus_group_theory="$GT/verus_group_theory.vir" \
  --extern verus_group_theory="$GT/libverus_group_theory.rlib" \
  "$HERE/src/lib.rs" "$@"
