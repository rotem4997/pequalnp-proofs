#!/usr/bin/env bash
# Run: bash tools/test_pnp_utf8.sh
# Every file tools/pnp.sh reads or writes is UTF-8 with LF line ends whatever the machine's default: a step with
# non-ASCII text goes through next, value, check and submit under three environments, and the skeletons, the checked
# record and the bytes sent are the same in all three. The first is UTF-8; the second is LC_ALL=C with
# PYTHONIOENCODING=cp1252 (python3 -I ignores PYTHON* variables, and C turns on its UTF-8 mode, so this one shows that
# nothing breaks); the third, LC_ALL=en_US.ISO8859-1, is a real legacy default: python's open() and print() then use
# ISO-8859-1, as a Windows python uses its code page. A CRLF file goes through check in all three as well.
# Offline: gh, lake and git's network verbs are stubs, the desk is loopback, the stop check reads a missing local path.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"; t="$(mktemp -d)"; srv=; trap 'kill $srv 2>/dev/null || true; wait $srv 2>/dev/null || true; rm -rf "$t"' EXIT
locale -a 2>/dev/null | grep -x 'en_US.ISO8859-1' >/dev/null || { echo "SKIPPED: no en_US.ISO8859-1 locale here to stand for a legacy code page"; exit 1; }
mkdir -p "$t/bin" "$t/www"; printf '#!/bin/sh\necho tester\n' > "$t/bin/gh"; printf '#!/bin/sh\ntrue\n' > "$t/bin/lake"
port=$((20000 + RANDOM % 20000)); (cd "$t/www" && exec python3 -m http.server "$port" --bind 127.0.0.1 >/dev/null 2>&1) & srv=$!
for _ in $(seq 50); do curl -s "http://127.0.0.1:$port/" >/dev/null && break; sleep 0.1; done
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t GIT_ALLOW_PROTOCOL=file
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0="url.$t/no-host.git.insteadOf" GIT_CONFIG_VALUE_0="https://github.com/open-goat/pequalnp-proofs.git"
mkdir -p "$t/up"; git -C "$t/up" init -q -b main; echo r > "$t/up/README"; mkdir -p "$t/up/lean/PEqualNP/Outside"; echo x > "$t/up/lean/PEqualNP/Outside/L_x_9.lean"; git -C "$t/up" add -A; git -C "$t/up" commit -qm base
real="$(command -v git)"
cat > "$t/bin/git" <<STUB
#!/bin/bash
if [ "\$1" = push ]; then echo "\$*" >> "\$PUSHED"; exit 0; fi
if [ "\$1" = fetch ]; then exec "$real" fetch -q "$t/up" main; fi
exec "$real" "\$@"
STUB
chmod +x "$t/bin/gh" "$t/bin/lake" "$t/bin/git"
# the desk speaks UTF-8 JSON, characters written out (not \u escapes), as a JavaScript server does
python3 - "$t/www" <<'PY'
import json, sys
g = {"id": "L-x-1", "title": "Größe ≤ ∀", "statement": "∀ n : ℕ, n + 0 = n ∧ (fun x : Fin 2 → Bool => x) = id", "file": "lean/PEqualNP/Outside/L_x_1.lean",
     "module": "PEqualNP.Outside.L_x_1", "imports": [], "unlocks": "the λ-calculus, ⟨a, b⟩ «names»", "context": "€ ‰ ∑ 𝔽 ﬁ"}
v = {"id": "L-x-2", "kind": "value", "title": "Wert", "template": "∀ t : ℕ, @@VALUE@@ ≤ t + @@VALUE@@", "value_holes": 2, "value_max": 9,
     "file_form": "lean/PEqualNP/Outside/V_x_2__k<k>.lean", "imports": [], "size_in_words": "AND ∧, OR ∨", "value_max_why": "≤ 9"}
for name, gap in (("next1", g), ("next2", v)):
    open(sys.argv[1] + "/" + name, "w", encoding="utf-8").write(json.dumps({"gap": gap, "lease": {"id": "abc", "expires_at": "2026-11-25T12:00:00Z"}}, ensure_ascii=False))
PY
F1=lean/PEqualNP/Outside/L_x_1.lean; F2=lean/PEqualNP/Outside/V_x_2__k3.lean
# rw <from> <to> <text for the sorry line> <line end>: the proof put in, written as bytes
rw() { python3 -c 'import sys; a,b,new,end=sys.argv[1:]; d=open(a,"rb").read().decode().replace("  sorry\n", new.replace("\\n","\n")); open(b,"wb").write(d.replace("\n", end.replace("\\r","\r").replace("\\n","\n")).encode())' "$@"; }
# run <name> <env...>: a fresh clone, next and value, a proof in place of sorry, check, submit; keep what came out
run() { local n="$1"; shift; local R="$t/$n"; git clone -q "$t/up" "$R"; mkdir -p "$R/tools"; cp "$here/pnp.sh" "$R/tools/"; printf '.pnp/\ntools/\n' >> "$R/.git/info/exclude"
  p() { (cd "$R" && env "$@" PATH="$t/bin:$PATH" PNP_DESK="http://127.0.0.1:$port" PUSHED="$t/$n.pushed" /bin/bash tools/pnp.sh "${ARGS[@]}") >"$t/$n.out" 2>"$t/$n.err" || { echo "FAIL $n: ${ARGS[*]}"; cat "$t/$n.out" "$t/$n.err"; exit 1; }; }
  cp "$t/www/next1" "$t/www/next"; ARGS=(next); p "$@"; grep -q 'Größe ≤ ∀' "$t/$n.out" && grep -q '⟨a, b⟩ «names»' "$t/$n.out" || { echo "FAIL $n: next printed"; cat "$t/$n.out"; exit 1; }
  cp "$R/$F1" "$t/$n.skel1"; cp "$t/www/next2" "$t/www/next"; ARGS=(next); p "$@"; grep -q 'AND ∧, OR ∨' "$t/$n.out" || { echo "FAIL $n: next (value) printed"; cat "$t/$n.out"; exit 1; }
  ARGS=(value L-x-2 3); p "$@"; cp "$R/$F2" "$t/$n.skel2"
  # a proof with a comment (check rewrites the file) and one in CRLF with no comment (check keeps its bytes)
  rw "$t/$n.skel1" "$R/$F1" '  -- ∀ by hand\n  intro n; simp\n' '\n'; ARGS=(check L-x-1); p "$@"; cp "$R/$F1" "$t/$n.tidy1"; cp "$R/.pnp/L-x-1.checked" "$t/$n.checked1"
  rw "$t/$n.skel2" "$R/$F2" '  omega\n' '\r\n'; ARGS=(check L-x-2); p "$@"; cp "$R/$F2" "$t/$n.crlf2"; cp "$R/.pnp/L-x-2.checked" "$t/$n.checked2"; rm "$R/$F2"
  (cd "$R" && env "$@" PATH="$t/bin:$PATH" PNP_DESK="http://127.0.0.1:$port" PUSHED="$t/$n.pushed" /bin/bash tools/pnp.sh submit L-x-1) >"$t/$n.out" 2>"$t/$n.err" || true; git -C "$R" cat-file blob "L-x-1:$F1" > "$t/$n.sent1"; grep -q 'push -q -u origin L-x-1' "$t/$n.pushed" || { echo "FAIL $n: not sent"; cat "$t/$n.err"; exit 1; }; }
run utf8 LC_ALL=en_US.UTF-8
run c LC_ALL=C PYTHONIOENCODING=cp1252
run legacy LC_ALL=en_US.ISO8859-1
# the skeleton is the desk's statement in UTF-8 with LF, byte for byte
printf 'import Mathlib\n\ntheorem PEqualNP.Outside.L_x_1 : (∀ n : ℕ, n + 0 = n ∧ (fun x : Fin 2 → Bool => x) = id) := by\n  sorry\n' > "$t/want1"
cmp "$t/want1" "$t/utf8.skel1" || { echo "FAIL: the UTF-8 skeleton is not the desk's statement"; exit 1; }
printf 'import Mathlib\n\ntheorem PEqualNP.Outside.V_x_2__k3 : (∀ t : ℕ, 3 ≤ t + 3) := by\n  sorry\n' > "$t/want2"
cmp "$t/want2" "$t/utf8.skel2" || { echo "FAIL: the UTF-8 value skeleton"; exit 1; }
! grep -q $'\r' "$t/utf8.tidy1" && grep -q $'\r' "$t/utf8.crlf2" || { echo "FAIL: line ends"; exit 1; }
for n in c legacy; do for f in skel1 skel2 tidy1 crlf2 checked1 checked2 sent1; do
  cmp -s "$t/utf8.$f" "$t/$n.$f" || { echo "FAIL: $f differs under $n"; od -c "$t/$n.$f" | head -8; exit 1; }
done; done
cut -d' ' -f1 "$t/utf8.checked1" | grep -qx "$(python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$t/utf8.sent1")" || { echo "FAIL: the record is not the hash of the bytes sent"; exit 1; }
echo "pnp utf8: pass (3 environments, 7 artifacts each, identical)"
