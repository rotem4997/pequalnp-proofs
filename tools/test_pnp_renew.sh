#!/usr/bin/env bash
# Run: bash tools/test_pnp_renew.sh
# submit renews the lease right before the pull request. A 410 that says withdrawn stops it; a 200 goes on in silence; a
# 409 with a reason (or an expired lease) shows the desk's reason and goes on; a timeout, a 503, an HTML page or an empty
# body is NOT a withdrawal: one line says the desk could not be reached, the renew is tried 3 more times, then the
# finished proof is sent with a line that the lease could not be confirmed. Offline: a loopback desk that answers as
# told, gh, lake and git's network verbs stubbed, the stop check reading a local path.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"; t="$(mktemp -d)"; srv=; trap 'kill $srv 2>/dev/null || true; wait $srv 2>/dev/null || true; rm -rf "$t"' EXIT
mkdir -p "$t/bin"; export LOG="$t/log" MODE="$t/mode"
port=$((20000 + RANDOM % 20000))
python3 - "$port" <<'PY' & srv=$!
import json, os, sys, time
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
class H(BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def send(self, code, body, kind="application/json"):
        self.send_response(code); self.send_header("Content-Type", kind); self.send_header("Content-Length", str(len(body))); self.end_headers(); self.wfile.write(body)
    def do_GET(self):
        self.send(200, json.dumps({"gap": {"id": "L-x-1", "title": "t", "statement": "1 = 1", "file": "lean/PEqualNP/Outside/L_x_1.lean", "module": "PEqualNP.Outside.L_x_1", "imports": []},
                                   "lease": {"id": "abc", "expires_at": "2026-11-25T12:00:00Z"}}).encode())
    def do_POST(self):
        open(os.environ["LOG"], "a").write(self.path.split("?")[0] + "\n")
        if not self.path.startswith("/beat"): return self.send(200, b"{}")
        m = open(os.environ["MODE"]).read().strip()
        if m == "timeout": time.sleep(11); return self.send(200, b'{"lease":{"id":"abc"}}')
        if m == "html": return self.send(502, b"<html><body>Bad gateway</body></html>", "text/html")
        if m == "empty": return self.send(200, b"")
        if m == "503": return self.send(503, b'{"error":"busy"}')
        if m == "410": return self.send(410, b'{"withdrawn":true,"error":"proved by another agent"}')
        if m == "409": return self.send(409, b'{"error":"the lease is held by another agent"}')
        if m == "expired": return self.send(410, b'{"withdrawn":false,"error":"the lease expired"}')
        if m == "flaky": open(os.environ["MODE"], "w").write("200"); return self.send(503, b"")
        return self.send(200, b'{"lease":{"id":"abc","expires_at":"2026-11-25T12:05:00Z"}}')
ThreadingHTTPServer(("127.0.0.1", int(sys.argv[1])), H).serve_forever()
PY
for _ in $(seq 50); do curl -s "http://127.0.0.1:$port/" >/dev/null && break; sleep 0.1; done
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t GIT_ALLOW_PROTOCOL=file
mkdir -p "$t/up/lean/PEqualNP/Outside"; git -C "$t/up" init -q -b main; echo x > "$t/up/lean/PEqualNP/Outside/L_x_9.lean"; git -C "$t/up" add -A; git -C "$t/up" commit -qm base
real="$(command -v git)"
printf '#!/bin/bash\nif [ "$1" = push ]; then exit 0; fi\nif [ "$1" = fetch ]; then exec "%s" fetch -q "%s" main; fi\nexec "%s" "$@"\n' "$real" "$t/up" "$real" > "$t/bin/git"
printf '#!/bin/sh\n[ "$1" = pr ] && echo "pr create" >> "$LOG"\necho tester\n' > "$t/bin/gh"; printf '#!/bin/sh\ntrue\n' > "$t/bin/lake"; chmod +x "$t/bin/git" "$t/bin/gh" "$t/bin/lake"
R="$t/repo"; git clone -q "$t/up" "$R"; mkdir -p "$R/tools"; cp "$here/pnp.sh" "$R/tools/"; printf '.pnp/\ntools/\n' >> "$R/.git/info/exclude"
pnp() { set +e; (cd "$R" && PATH="$t/bin:$PATH" PNP_DESK="http://127.0.0.1:$port" /bin/bash tools/pnp.sh "$@") >"$t/out" 2>"$t/err"; rc=$?; set -e; }
pnp next; printf 'import Mathlib\n\ntheorem PEqualNP.Outside.L_x_1 : (1 = 1) := rfl\n' > "$R/lean/PEqualNP/Outside/L_x_1.lean"; pnp check L-x-1; [ "$rc" = 0 ] || { cat "$t/err"; exit 1; }
UNREACH='the desk could not be reached to renew the lease; trying again, 3 times, 3 s apart'
UNCONF='the lease could not be confirmed (the desk did not answer); sending the finished, checked proof anyway'
# case <mode> <exit> <beats> <pr: yes|no> <lines expected on stderr, each a fixed string>...
case_() { local m="$1" want="$2" beats="$3" pr="$4"; shift 4; echo "$m" > "$MODE"; : > "$LOG"; pnp submit L-x-1
  [ "$rc" = "$want" ] || { echo "FAIL $m: exit $rc, not $want"; cat "$t/err"; exit 1; }
  [ "$(grep -c '^/beat$' "$LOG")" = "$beats" ] || { echo "FAIL $m: $(grep -c '^/beat$' "$LOG") renew calls, not $beats"; exit 1; }
  if [ "$pr" = yes ]; then grep -qx 'pr create' "$LOG" || { echo "FAIL $m: no pull request"; cat "$t/err"; exit 1; }
  else ! grep -q 'pr create' "$LOG" || { echo "FAIL $m: a pull request was opened"; exit 1; }; fi
  for l in "$@"; do grep -qxF -- "$l" "$t/err" || { echo "FAIL $m: no line: $l"; cat "$t/err"; exit 1; }; done
  ! grep -qi 'traceback' "$t/err" || { echo "FAIL $m: a traceback"; exit 1; }; echo "ok $m"; }
case_ 200 0 1 yes
! grep -q 'renew the lease\|could not be confirmed' "$t/err" || { echo "FAIL 200: not silent"; cat "$t/err"; exit 1; }
case_ 410 3 1 no 'STOP: not submitted. proved by another agent'
case_ 409 0 1 yes 'the desk did not renew the lease (409): the lease is held by another agent; sending the finished, checked proof anyway'
case_ expired 0 1 yes 'the desk did not renew the lease (410): the lease expired; sending the finished, checked proof anyway'
case_ 503 0 4 yes "$UNREACH" "$UNCONF"
case_ html 0 4 yes "$UNREACH" "$UNCONF"
case_ empty 0 4 yes "$UNREACH" "$UNCONF"
case_ flaky 0 2 yes "$UNREACH"
! grep -qF "$UNCONF" "$t/err" || { echo "FAIL flaky: said unconfirmed after a renew went through"; exit 1; }
s=$SECONDS; case_ timeout 0 4 yes "$UNREACH" "$UNCONF"; [ $((SECONDS - s)) -le 60 ] || { echo "FAIL timeout: took $((SECONDS - s)) s"; exit 1; }
echo "pnp renew: pass"
