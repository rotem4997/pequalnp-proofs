#!/usr/bin/env bash
# Run: bash notes/data/lrat-link/test_genrow_utf8.sh
# genrow.py writes its Lean file in UTF-8 with LF whatever the machine's default: the same inputs (one segment and two,
# LF and CRLF inputs, a function with non-ASCII text) give byte-identical output under UTF-8, under LC_ALL=C, and under
# LC_ALL=en_US.ISO8859-1 (a real legacy default: python's open() then uses ISO-8859-1, as a Windows python uses its code
# page), with the python3 on PATH and with the stock /usr/bin/python3 when there is one.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"; t="$(mktemp -d)"; trap 'rm -rf "$t"' EXIT
locale -a 2>/dev/null | grep -x 'en_US.ISO8859-1' >/dev/null || { echo "SKIPPED: no en_US.ISO8859-1 locale here to stand for a legacy code page"; exit 1; }
printf 'p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n' > "$t/f.cnf"; printf '5 1 0 1 2 0\n6 0 5 3 4 0\n' > "$t/p.lrat"
sed 's/$/\r/' "$t/f.cnf" > "$t/crlf.cnf"; sed 's/$/\r/' "$t/p.lrat" > "$t/crlf.lrat"
FX='x ⟨0, by decide⟩ && !x ⟨1, by decide⟩'
pys="python3"; [ -x /usr/bin/python3 ] && pys="$pys /usr/bin/python3"
n=0
for py in $pys; do for L in en_US.UTF-8 C en_US.ISO8859-1; do for c in one two crlf; do
  case $c in one) a=("$t/f.cnf" "$t/p.lrat"); s=();; two) a=("$t/f.cnf" "$t/p.lrat"); s=(--seg 1);; crlf) a=("$t/crlf.cnf" "$t/crlf.lrat"); s=(--seg 1);; esac
  o="$t/$c.$n.lean"; LC_ALL=$L "$py" "$here/genrow.py" "${a[@]}" "$o" NS 2 3 0,1,2,3 "$FX" "${s[@]+"${s[@]}"}" >/dev/null 2>"$t/err" || { echo "FAIL: $py $L $c"; cat "$t/err"; exit 1; }
  [ -e "$t/$c.lean" ] || cp "$o" "$t/$c.lean"
  cmp -s "$t/$c.lean" "$o" || { echo "FAIL: $c differs under $py $L"; exit 1; }
done; n=$((n+1)); done; done
for c in one two crlf; do
  ! grep -q $'\r' "$t/$c.lean" || { echo "FAIL: $c holds CR"; exit 1; }
  grep -qF "def fn (x : Fin 2 → Bool) : Bool := $FX" "$t/$c.lean" || { echo "FAIL: $c lacks the function in UTF-8"; exit 1; }
done
grep -q '^theorem seg1 ' "$t/two.lean" && ! grep -q '^theorem seg1 ' "$t/one.lean" || { echo "FAIL: the segment case"; exit 1; }
cmp -s "$t/two.lean" "$t/crlf.lean" || { echo "FAIL: CRLF inputs give another file"; exit 1; }
echo "genrow utf8: pass ($n runs of 3 cases, byte-identical)"
