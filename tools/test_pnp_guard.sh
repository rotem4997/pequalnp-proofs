#!/usr/bin/env bash
# Run: bash tools/test_pnp_guard.sh [gaps.json]
# The statement guard of tools/pnp.sh next: a statement carrying Lean code is refused with nothing written; a plain
# statement is written wrapped in parentheses; and, given a gaps.json, every statement in it passes.
set -euo pipefail
# The stop notice check of pnp.sh fetches the code host: this test never waits on a real host (git's own rewrite, this test's environment only).
export GIT_ALLOW_PROTOCOL=file GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=url./nonexistent-host-for-test.insteadOf GIT_CONFIG_VALUE_0=https://github.com/
here="$(cd "$(dirname "$0")" && pwd)"; t="$(mktemp -d)"; trap 'kill $srv 2>/dev/null || true; wait $srv 2>/dev/null || true; rm -rf "$t"' EXIT
mkdir -p "$t/repo" "$t/bin" "$t/www"; git -C "$t/repo" init -q; mkdir -p "$t/repo/tools"; cp "$here/pnp.sh" "$t/repo/tools/"
printf '#!/bin/sh\necho tester\n' > "$t/bin/gh"; chmod +x "$t/bin/gh"
port=$((20000 + RANDOM % 20000)); (cd "$t/www" && exec python3 -m http.server "$port" --bind 127.0.0.1 >/dev/null 2>&1) & srv=$!
for _ in $(seq 50); do curl -s "http://127.0.0.1:$port/" >/dev/null && break; sleep 0.1; done
serve() { python3 -c 'import json,sys; print(json.dumps({"gap":{"id":"L-t-1","title":"t","statement":sys.argv[1],"file":"lean/PEqualNP/Outside/L_t_1.lean","module":"PEqualNP.Outside.L_t_1","imports":["PEqualNP.Defs"]},"lease":{"id":"abc","expires_at":"2026-11-25T12:00:00Z"}}))' "$1" > "$t/www/next"; rm -f "$t/repo/lean/PEqualNP/Outside/L_t_1.lean"; }
run() { (cd "$t/repo" && PATH="$t/bin:$PATH" PNP_DESK="http://127.0.0.1:$port" bash tools/pnp.sh next) >"$t/out" 2>&1; }
f="$t/repo/lean/PEqualNP/Outside/L_t_1.lean"
for bad in $'True := trivial\n#eval IO.println "pwned"' $'True) := trivial\nrun_cmd pure ()\nexample : (True' '(by run_tac pure ()) = ()' 'Lean.reduceBool x = true'; do
  serve "$bad"; if run; then echo "FAIL: accepted: $bad"; exit 1; fi
  grep -q REFUSED "$t/out" || { echo "FAIL: no reason printed"; cat "$t/out"; exit 1; }; [ ! -e "$f" ] || { echo "FAIL: file written for: $bad"; exit 1; }
done
serve '∀ n : ℕ, n + 0 = n'; run || { cat "$t/out"; echo "FAIL: plain statement refused"; exit 1; }
grep -q 'theorem PEqualNP.Outside.L_t_1 : (∀ n : ℕ, n + 0 = n) := by' "$f" || { echo "FAIL: skeleton"; cat "$f"; exit 1; }
if [ -n "${1:-}" ]; then
  n=0; while IFS= read -r -d '' s; do serve "$s"; run || { echo "FAIL: live statement refused: $(head -c 200 <<<"$s")"; cat "$t/out"; exit 1; }; n=$((n+1)); done \
    < <(python3 -c 'import json,sys; [sys.stdout.write(g["statement"]+"\0") for g in json.load(open(sys.argv[1]))["gaps"] if isinstance(g.get("statement"), str)]' "$1")
  echo "live: $n statements, none refused"
fi
echo "pnp guard: pass"
