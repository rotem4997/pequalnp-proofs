#!/usr/bin/env bash
# Run: bash tools/test_pnp_check_guard.sh
# check runs the public guard's file rules (.github/scripts/outside-guard.mjs) before lake: one file per rule, breaking
# only that rule, is refused with the guard's sentence, its line and the one fix, and lake is never called; a clean file
# goes on to the build; submit refuses such a file too. PARITY: every file text the guard's own test file feeds it, and
# a seeded batch of mixed lines, is judged by the guard itself (node) and by check's copy, after check's comment removal,
# and the two must give the same verdict and the same sentences. Offline: lake and gh are stubs, the desk is a loopback
# address nothing listens on, and git's insteadOf with GIT_ALLOW_PROTOCOL=file keeps the stop check off every real host.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"; guard="$here/../.github/scripts/outside-guard.mjs"; t="$(mktemp -d)"; trap 'rm -rf "$t"' EXIT
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t GIT_ALLOW_PROTOCOL=file
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0="url.$t/no-host.git.insteadOf" GIT_CONFIG_VALUE_0="https://github.com/open-goat/pequalnp-proofs.git"
mkdir -p "$t/bin"; printf '#!/bin/sh\necho tester\n' > "$t/bin/gh"; printf '#!/bin/sh\necho "$2" >> "$LAKED"\n' > "$t/bin/lake"; chmod +x "$t/bin/gh" "$t/bin/lake"; export LAKED="$t/laked"
R="$t/repo"; mkdir -p "$R/tools" "$R/lean/PEqualNP/Outside" "$R/.pnp"; git -C "$R" init -q; cp "$here/pnp.sh" "$R/tools/"; printf '.pnp/\ntools/\n' >> "$R/.git/info/exclude"
F=lean/PEqualNP/Outside/L_x_1.lean; M=PEqualNP.Outside.L_x_1
state() { python3 -c 'import json,sys; print(json.dumps({"gap":{"id":"L-x-1","file":sys.argv[1],"module":sys.argv[2],"imports":["PEqualNP.Defs"]},"lease":{"id":"abc"}}))' "$1" "$2" > "$R/.pnp/L-x-1.json"; }
pnp() { set +e; (cd "$R" && PATH="$t/bin:$PATH" PNP_DESK="http://127.0.0.1:9" /bin/bash tools/pnp.sh "$@") >"$t/out" 2>"$t/err"; rc=$?; set -e; }
H=$'import Mathlib\nimport PEqualNP.Defs\n\n'; T="theorem $M : True := trivial"$'\n'
# refused <body> <the guard's words> <line or -> <fix words>: check refuses before lake with the three things
n=0; refused() { printf '%s' "$1" > "$R/$F"; judge "$2" "$3" "$4"; }
judge() { rm -f "$LAKED"; pnp check L-x-1; n=$((n+1)); set -- "" "$@"
  [ "$rc" = 1 ] && [ ! -e "$LAKED" ] && [ ! -e "$R/.pnp/L-x-1.checked" ] || { echo "FAIL $n: not refused before lake (exit $rc)"; cat "$t/err"; exit 1; }
  grep -qF -- "$2" "$t/err" || { echo "FAIL $n: no sentence: $2"; cat "$t/err"; exit 1; }
  [ "$3" = - ] || grep -qF "REFUSED: line $3: " "$t/err" || { echo "FAIL $n: no line $3"; cat "$t/err"; exit 1; }
  grep -qF -- "$4" "$t/err" || { echo "FAIL $n: no fix: $4"; cat "$t/err"; exit 1; }; }
state "$F" "$M"
refused "$H$T  sorry"$'\n' '"sorry" is not allowed in a proof file' 5 'fix: take that word out of the line'
refused "$H$T  exact x"$'\n'"#eval 1"$'\n' '"#eval" is not allowed in a proof file' 6 'fix: take that word out of the line'
refused "${H}set_option maxHeartbeats 400000"$'\n'"$T" '"set_option" is not allowed' 4 'write it as set_option <option> <value> in'
refused "$H$T  bv_decide"$'\n' '"bv_decide" is not allowed' 5 'so use tactics the kernel checks alone'
refused "${H}import Evil.Module"$'\n'"$T" 'line 4: import Evil.Module is not allowed (only Mathlib and the modules the gap lists)' 4 'fix: delete this import line'
refused "$H$T  exact x import y"$'\n' 'line 5: the word "import" after the import lines' 5 'fix: take the word import out of this line'
refused "${H}def f : Nat := 1"$'\n' 'the file holds no theorem' - "fix: keep the theorem $M in the file"
refused "${H}def f : Nat := 1"$'\n'"$T" "line 4: a declaration or command outside the file's own namespace" 4 "put every helper inside \`namespace $M\`"
refused "${H}namespace PEqualNP.Library"$'\n'"end PEqualNP.Library"$'\n'"$T" '`namespace PEqualNP.Library` at the top level' 4 "put every helper inside"
refused "${H}namespace $M"$'\n'"  namespace In"$'\n'"  end In"$'\n'"end $M"$'\n'"$T" '`namespace`, `section`, `end` and `mutual` must stand alone' 5 "put every helper inside"
refused "${H}namespace $M"$'\n'"end"$'\n'"$T" '`end` does not name what it closes' 5 "write \`end $M\`"
refused "${H}open Nat in def f : Nat := 1"$'\n'"$T" 'an `open ... in` line must end with `in`' 4 "put every helper inside"
refused "$H$T"$'\n'"theorem other : True := trivial"$'\n' '"theorem" after the theorem' 6 "nothing but its proof may follow it"
refused "$H$T  trivial"$'\x07\n' 'the file holds control characters' - 'fix: delete the control characters'
refused "$H$T"$'\xe2\x80\xae'"x"$'\n' 'the file holds invisible or direction-changing characters' - 'fix: delete the invisible characters'
{ printf '%s' "$H$T"; printf '\000\n'; } > "$R/$F"; judge 'the file holds a NUL byte' - 'fix: delete the NUL byte'
state lean/PEqualNP/Outside/L_Bad.lean PEqualNP.Outside.L_Bad; F0=$F; F=lean/PEqualNP/Outside/L_Bad.lean
refused "${H}theorem PEqualNP.Outside.L_Bad : True := trivial"$'\n' 'the one file must be lean/PEqualNP/Outside/L_<gap>.lean' - 'L_<gap>.lean'
F=$F0; state "$F" "$M"
# every problem at once, in file order, as the guard gives them
printf '%s' "${H}import Evil.M"$'\n'"private def f : Nat := sorry"$'\n' > "$R/$F"; rm -f "$LAKED"; pnp check L-x-1
[ "$rc" = 1 ] && [ ! -e "$LAKED" ] && [ "$(grep -c '^REFUSED: ' "$t/err")" = 5 ] || { echo "FAIL: all problems at once"; cat "$t/err"; exit 1; }
# a clean file, with a comment that holds a refused word (check removes comments first): built and recorded
printf '%s' "${H}namespace $M"$'\n'"/-- a helper, no sorry here -/"$'\n'"private def f : ℕ := 1"$'\n'"end $M"$'\n'"open $M in"$'\n'"$T" > "$R/$F"; rm -f "$LAKED"; pnp check L-x-1
[ "$rc" = 0 ] && grep -qx "$M" "$LAKED" && [ -s "$R/.pnp/L-x-1.checked" ] && ! grep -q REFUSED "$t/err" || { echo "FAIL: a clean file did not reach the build"; cat "$t/out" "$t/err"; exit 1; }
# check --allow-sorry: only the sorry rule is skipped, the file reaches the build, nothing is recorded, submit refuses it
SR="${H}theorem $M : True := by"$'\n'"  sorry"$'\n'; printf '%s' "$SR" > "$R/$F"; rm -f "$LAKED"; pnp check L-x-1 --allow-sorry
[ "$rc" = 0 ] && grep -qx "$M" "$LAKED" && [ ! -e "$R/.pnp/L-x-1.checked" ] && grep -qF 'this file cannot be submitted while it holds sorry' "$t/err" && ! grep -q REFUSED "$t/err" || { echo "FAIL: --allow-sorry"; cat "$t/out" "$t/err"; exit 1; }
pnp submit L-x-1; [ "$rc" = 1 ] && grep -qF 'is not the file that was checked' "$t/err" || { echo "FAIL: submit took an --allow-sorry check"; cat "$t/err"; exit 1; }
printf '%s' "$SR  #eval 1"$'\n' > "$R/$F"; rm -f "$LAKED"; pnp check L-x-1 --allow-sorry
[ "$rc" = 1 ] && [ ! -e "$LAKED" ] && grep -qF 'REFUSED: line 6: "#eval" is not allowed' "$t/err" && ! grep -q '"sorry"' "$t/err" || { echo "FAIL: --allow-sorry skipped more than sorry"; cat "$t/err"; exit 1; }
printf '%s' "$SR" > "$R/$F"; pnp check L-x-1 --allow-sorrys; [ "$rc" = 1 ] && grep -q '^unknown: --allow-sorrys' "$t/err" || { echo "FAIL: an unknown option"; cat "$t/err"; exit 1; }
pnp check L-x-1; [ "$rc" = 1 ] && grep -qF 'REFUSED: line 5: "sorry" is not allowed' "$t/err" || { echo "FAIL: sorry without the flag"; cat "$t/err"; exit 1; }
# a file that is not UTF-8: one refusal, the guard's sentence and the fix, no traceback, no build
{ printf '%s' "$H$T"; printf '\377\n'; } > "$R/$F"; rm -f "$LAKED"; pnp check L-x-1
[ "$rc" = 1 ] && [ ! -e "$LAKED" ] && [ "$(cat "$t/err")" = "REFUSED: the file is not UTF-8 text"$'\n'"  fix: save the file as UTF-8 text" ] || { echo "FAIL: not UTF-8"; cat "$t/err"; exit 1; }
# submit refuses a file the guard refuses, even when it carries a record of check (a check made before this rule)
printf '%s' "$H$T  sorry"$'\n' > "$R/$F"; printf '%s %s\n' "$(python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$R/$F")" "$F" > "$R/.pnp/L-x-1.checked"
pnp submit L-x-1; [ "$rc" = 1 ] && grep -qF 'REFUSED: line 5: "sorry" is not allowed' "$t/err" && ! grep -q 'still contains sorry' "$t/err" || { echo "FAIL: submit did not refuse"; cat "$t/err"; exit 1; }
git -C "$R" rev-parse -q --verify HEAD >/dev/null && { echo "FAIL: submit committed"; exit 1; }
echo "rules: $n refusals, all problems at once, a clean file built, --allow-sorry, not UTF-8, submit refuses: pass"

# PARITY. The guard's own test inputs are recorded by running its test file against a recording copy of the guard.
command -v node >/dev/null || { echo "SKIPPED parity: node is not installed, so the guard cannot be run here"; exit 1; }
G="$t/g"; mkdir -p "$G" "$t/c"; cp "$guard" "$G/outside-guard.mjs"
sed -e "s#'./outside-guard.mjs'#'./shim.mjs'#g" -e "s#'node:test'#'./nt.mjs'#" "$here/../.github/scripts/outside-guard.test.mjs" > "$G/t.mjs"
echo 'export const test = (name, fn) => { try { fn(); } catch {} };' > "$G/nt.mjs"
cat > "$G/shim.mjs" <<'JS'
import * as G from './outside-guard.mjs';
export * from './outside-guard.mjs';
export const REC = [];
const b64 = (x) => Buffer.from(typeof x === 'string' ? new TextEncoder().encode(x) : x).toString('base64');
const rec = (x, allowed, module) => { if (Array.isArray(allowed)) REC.push({ b: b64(x), allowed, module: module || 'PEqualNP.Outside.L_x_1' }); };
export const checkImports = (b, a) => { rec(b, a); return G.checkImports(b, a); };
export const checkProofFile = (b, a, m) => { rec(b, a, m); return G.checkProofFile(b, a, m); };
export const checkPlain = (s) => { rec(s, []); return G.checkPlain(s); };
export const checkOwnNamespace = (s, m) => { rec(s, ['PEqualNP.Defs'], m); return G.checkOwnNamespace(s, m); };
JS
# a seeded batch of mixed lines: comments, strings, scope lines, other letters and spaces, the guard's edge characters
cat > "$G/cases.mjs" <<'JS'
import { writeFileSync } from 'node:fs';
await import('./t.mjs'); const { REC } = await import('./shim.mjs');
const M = 'PEqualNP.Outside.L_x_1';
const parts = ['import Mathlib', 'import PEqualNP.Defs', 'import Evil.X', '', '  ', `namespace ${M}`, `end ${M}`, 'end', 'section', 'noncomputable section S', 'end S', 'mutual',
  `  namespace ${M}`, 'namespace Δέλτα.x₁', 'end Δέλτα.x₁', `namespace ${M}_aux.ℕ₂`, `end ${M}_aux.ℕ₂`, `open ${M} in`, 'open Nat in def g := 1', 'open scoped BigOperators',
  `theorem ${M} : True := trivial`, `theorem ${M}.a : True := trivial`, `theorem ${M}x : True := trivial`, 'private def f : ℕ := 1', '@[simp] theorem s : True := trivial',
  '  sorry', '  exact add_comm', 'add_x', '\u00a0add_x', '\u0085add_x', '\u2028end', '-- sorry', '-- end X', '/- end X -/ def h := 1', '/-- doc -/', '/-', '-/', '"s -- x"',
  "  have : '-' = '-' := rfl", "  exact h'--", 'set_option maxHeartbeats 1 in', 'set_option maxHeartbeats 1', 'set_option maxHeartbeats 1 in def k := 1', '  n%2 = xy% 1',
  '𝔽ab end 𝔽', '  exact λ x ↦ x', 'λend', 'x\r', '#check Nat', '\ufeffdef a := 1', 'deriving DecidableEq', '  def inner := 1', 'where', '  aux (n : ℕ) : n = n := rfl', 'import'];
let s = 0x2545; const rnd = (n) => { s = (s * 1103515245 + 12345) % 2147483648; return s % n; };
const mixed = Array.from({ length: 400 }, () => Array.from({ length: 1 + rnd(9) }, () => parts[rnd(parts.length)]).join(rnd(7) ? '\n' : '\r\n') + (rnd(3) ? '\n' : ''));
const inner = ['private def f (n : ℕ) : ℕ := n', 'theorem a : True := trivial', '/-- doc -/', '-- a note', 'section', 'end', 'namespace Helpers', 'end Helpers', 'variable {n : ℕ}', '  deriving DecidableEq', 'open Finset'];
const proofLines = ['  trivial', '  simp [Nat.add_comm, add_zero]', '  exact h\'', '  omega -- why', '  /- step -/ rfl', '  n%2 = 1', '  exact λ x ↦ x', 'where', '  aux (n : ℕ) : n = n := rfl'];
const pick = (a) => a[rnd(a.length)];
const nearly = Array.from({ length: 300 }, () => ['import Mathlib', ...(rnd(2) ? ['import PEqualNP.Defs'] : []), '',
  ...(rnd(2) ? [`namespace ${M}`, ...Array.from({ length: rnd(5) }, () => pick(inner)), `end ${M}`] : []), ...(rnd(3) ? [] : ['set_option maxHeartbeats 400000 in']),
  ...(rnd(4) ? [] : [pick(parts)]), `theorem ${M} : True := by`, ...Array.from({ length: rnd(4) }, () => pick(proofLines))].join('\n') + '\n');
const extra = ['\ufeffimport Mathlib\ntheorem ' + M + ' : True := trivial\n', 'import Mathlib\n\u0085\ntheorem ' + M + ' : True := trivial\n', 'import Mathlib\nimport 𝔽' + 'x'.repeat(70) + '\n', `import Mathlib\nnamespace ${'𝔽'.repeat(40)}\nend ${'𝔽'.repeat(40)}x\ntheorem ${M} : True := trivial\n`];
const all = [...REC, ...[...mixed, ...nearly, ...extra].map((x) => ({ b: Buffer.from(x).toString('base64'), allowed: ['PEqualNP.Defs'], module: M }))];
all.forEach((c, k) => {
  writeFileSync(`${process.argv[2]}/${k}.lean`, Buffer.from(c.b, 'base64'));
  writeFileSync(`${process.argv[2]}/${k}.json`, JSON.stringify({ gap: { imports: c.allowed } }));
  writeFileSync(`${process.argv[2]}/${k}.rel`, `lean/${c.module.split('.').join('/')}.lean`);
});
console.log(REC.length, all.length);
JS
cat > "$G/verdict.mjs" <<'JS'
import { readFileSync, writeFileSync } from 'node:fs';
import { checkFileKind, checkProofFile } from './outside-guard.mjs';
const [dir, count] = process.argv.slice(2);
for (let k = 0; k < Number(count); k += 1) {
  const rel = readFileSync(`${dir}/${k}.rel`, 'utf8'); let say = '';
  try { checkFileKind(rel, rel.includes('/R_') ? 'reduce' : 'check'); checkProofFile(readFileSync(`${dir}/${k}.lean`), JSON.parse(readFileSync(`${dir}/${k}.json`, 'utf8')).gap.imports, rel.slice(5, -5).split('/').join('.')); }
  catch (e) { say = e.message.split('\n').map((l) => `REFUSED: ${l}\n`).join(''); }
  writeFileSync(`${dir}/${k}.guard`, say);
}
JS
read -r recorded count < <(node "$G/cases.mjs" "$t/c")
[ "$recorded" -ge 100 ] || { echo "FAIL: only $recorded inputs recorded from the guard's test file"; exit 1; }
# check's comment removal first (what is sent is what check built), then the guard and check's copy on the same bytes
eval "$(sed -n -e '/^tidy() {/,/^}/p' -e '/^format_py() {/,/^}/p' "$here/pnp.sh")"
k=0; while [ "$k" -lt "$count" ]; do tidy "$t/c/$k.lean" >/dev/null 2>&1 || true; k=$((k+1)); done
node "$G/verdict.mjs" "$t/c" "$count"
src="$(format_py)"; same=0; refusedn=0; k=0
while [ "$k" -lt "$count" ]; do
  python3 -I -c "$src" "$t/c/$k.lean" "$(cat "$t/c/$k.rel")" "$t/c/$k.json" 2>"$t/c/$k.err" && : || :
  grep '^REFUSED: ' "$t/c/$k.err" > "$t/c/$k.local" || true
  cmp -s "$t/c/$k.local" "$t/c/$k.guard" || { echo "FAIL parity on case $k ($(cat "$t/c/$k.rel")):"; cat -v "$t/c/$k.lean" | head -20; echo "--- guard"; cat "$t/c/$k.guard"; echo "--- check"; cat "$t/c/$k.err"; exit 1; }
  [ -s "$t/c/$k.guard" ] && refusedn=$((refusedn+1)); same=$((same+1)); k=$((k+1))
done
echo "parity: $same files ($recorded from the guard's test file), $refusedn refused and $((same-refusedn)) accepted by both, sentence for sentence: pass"
echo "pnp check guard: pass"
