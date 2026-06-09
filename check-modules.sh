#!/usr/bin/env bash
# Per-module verification of tactus-computability-theory (so one failure/panic
# doesn't mask the rest). Imports the group-theory export. --verify-module still
# loads the whole crate's context, so cross-module reasoning is unchanged.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERUS="$HERE/../tactus/source/target-verus/release/verus"
GT="$HERE/../tactus-group-theory/export"
if [[ ! -f "$GT/verus_group_theory.vir" ]]; then
  "$HERE/../tactus-group-theory/build-export.sh" >/dev/null
fi
mods=$(grep -oE 'pub mod [a-z_]+' "$HERE/src/lib.rs" | awk '{print $3}')
tot_v=0; tot_e=0; fail=0
for m in $mods; do
  out=$("$VERUS" --lean-backend --crate-type=lib \
    --import verus_group_theory="$GT/verus_group_theory.vir" \
    --extern verus_group_theory="$GT/libverus_group_theory.rlib" \
    "$HERE/src/lib.rs" --verify-module "$m" 2>&1)
  if echo "$out" | grep -q 'tuple_field_accessor\|panicked'; then
    printf "  %-26s PANIC\n" "$m"; fail=1
  else
    res=$(echo "$out" | grep -oE '[0-9]+ verified, [0-9]+ errors' | head -1)
    v=$(echo "$res" | grep -oE '^[0-9]+'); e=$(echo "$res" | grep -oE '[0-9]+ errors' | grep -oE '^[0-9]+')
    tot_v=$((tot_v + ${v:-0})); tot_e=$((tot_e + ${e:-0}))
    [[ "${e:-0}" != "0" ]] && fail=1
    [[ -z "$res" ]] && { res="(no result: $(echo "$out" | grep -oE 'error.*' | head -1 | cut -c1-60))"; fail=1; }
    printf "  %-26s %s\n" "$m" "$res"
  fi
done
echo "  ----"; printf "  TOTAL: %d verified, %d errors\n" "$tot_v" "$tot_e"
exit $fail
