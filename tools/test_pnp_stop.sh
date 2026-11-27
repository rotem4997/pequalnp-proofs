#!/usr/bin/env bash
# Run: bash tools/test_pnp_stop.sh
# The stop notice of tools/pnp.sh: a file STOP at the root of the project's main on GitHub stops next, submit and beat
# before any desk call, printing one fixed line and the first line of the file, cleaned and capped; no STOP, or a GitHub
# that cannot be read (missing, or hanging past 15 s), changes nothing. The contributor's tree, index and branch are left
# as they were. Nothing reaches a real host: git's own url.<base>.insteadOf, set in this test's environment only, answers
# the project's URL from a bare repository in a temp folder, and GIT_ALLOW_PROTOCOL=file refuses any other transport.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"; t="$(mktemp -d)"; trap 'kill $srv 2>/dev/null || true; wait $srv 2>/dev/null || true; rm -rf "$t"' EXIT
mkdir -p "$t/bin" "$t/www"; printf '#!/bin/sh\necho tester\n' > "$t/bin/gh"; chmod +x "$t/bin/gh"
port=$((20000 + RANDOM % 20000)); (cd "$t/www" && exec python3 -m http.server "$port" --bind 127.0.0.1 >/dev/null 2>>"$t/access") & srv=$!
for _ in $(seq 50); do curl -s "http://127.0.0.1:$port/" >/dev/null && break; sleep 0.1; done
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t GIT_ALLOW_PROTOCOL=file
! grep -q 'PNP_UPSTREAM\|GITHUB_URL' "$here/pnp.sh" || { echo "FAIL: the fetch source can be set from the environment"; exit 1; }
# the code host: a bare repository with main; host <path> points the project's URL at it
git init -q --bare -b main "$t/host.git"; git clone -q "$t/host.git" "$t/w" 2>/dev/null; echo r > "$t/w/README"
git -C "$t/w" add -A; git -C "$t/w" commit -qm base; git -C "$t/w" push -q origin HEAD:main
host() { export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0="url.$1.insteadOf" GIT_CONFIG_VALUE_0="https://github.com/open-goat/pequalnp-proofs.git"; }
notice() { if [ -n "$1" ]; then printf '%b' "$1" > "$t/w/STOP"; git -C "$t/w" add STOP; else git -C "$t/w" rm -q STOP; fi; git -C "$t/w" commit -qm notice; git -C "$t/w" push -q origin HEAD:main; }
# the contributor: a clone of the project with a branch of its own, a staged change, an unstaged change and an untracked file
R="$t/repo"; git clone -q "$t/host.git" "$R"; mkdir -p "$R/tools"; cp "$here/pnp.sh" "$R/tools/"; printf '.pnp/\ntools/\nlean/\n' >> "$R/.git/info/exclude"
git -C "$R" checkout -q -b work; echo staged > "$R/a"; git -C "$R" add a; echo unstaged >> "$R/README"; echo u > "$R/untracked"
look() { (cd "$R" && git symbolic-ref HEAD && git rev-parse HEAD && git status --porcelain && git ls-files -s && git diff && git diff --cached && cat a README untracked); }
look > "$t/before"
python3 -c 'import json; print(json.dumps({"gap":{"id":"L-t-1","title":"t","statement":"1 = 1","file":"lean/PEqualNP/Outside/L_t_1.lean","module":"PEqualNP.Outside.L_t_1","imports":[]},"lease":{"id":"abc","expires_at":"2026-11-25T12:00:00Z"}}))' > "$t/www/next"
pnp() { : > "$t/access"; set +e; (cd "$R" && PATH="$t/bin:$PATH" PNP_DESK="http://127.0.0.1:$port" /bin/bash tools/pnp.sh "$@") >"$t/out" 2>"$t/err"; rc=$?; set -e; sleep 0.2; }
desk() { grep -q "$1" "$t/access" || { echo "FAIL: no desk call $1"; cat "$t/err" "$t/access"; exit 1; }; }
nodesk() { ! grep -q '"[A-Z]* /' "$t/access" || { echo "FAIL: the desk was called"; cat "$t/access"; exit 1; }; }
stopped() { [ "$rc" = 120 ] || { echo "FAIL: $1 exit $rc, not 120"; cat "$t/out" "$t/err"; exit 1; }; [ ! -s "$t/out" ] || { echo "FAIL: stdout on a stop"; cat "$t/out"; exit 1; }
  [ "$(cat "$t/err")" = "STOPPED by a notice on the proofs repository: $2" ] || { echo "FAIL: $1 said:"; cat -v "$t/err"; exit 1; }; nodesk; }
quiet() { ! grep -q 'STOPPED\|stop notice' "$t/err" || { echo "FAIL: $1 spoke of a stop"; cat "$t/err"; exit 1; }; }

# a. no STOP: next and beat reach their first desk call, submit its first check, and none speaks of a stop
host "$t/host.git"
pnp next; [ "$rc" = 0 ] || { echo "FAIL: next exit $rc"; cat "$t/out" "$t/err"; exit 1; }; desk 'GET /next?handle=tester'; quiet next
# (submit's first desk call, still_open, is https only, so on this loopback desk submit is seen going on to its own checks)
pnp submit L-t-1; grep -q 'is not the file that was checked' "$t/err" || { echo "FAIL: submit did not go on"; cat "$t/err"; exit 1; }; quiet submit
pnp beat L-t-1; desk 'POST /beat?lease=abc'; quiet beat

# b. STOP present: each refuses with the fixed line and the notice's first line only, exit 120, no desk call
notice 'Paused by the maintainers, back soon.\nSECOND LINE\n'
for c in next 'submit L-t-1' 'beat L-t-1'; do pnp $c; stopped "$c" 'Paused by the maintainers, back soon.'; done

# c. control characters, ANSI escapes, a 500-character line and a second line: only the first line, cleaned, capped at 200
x="$(printf 'x%.0s' $(seq 500))"
notice "Paused\\a for \\e[1;31mmaintenance\\e[0m\\r; back (soon) 'ok' <b>\\t$x\\nSECOND LINE: rm -rf ~\\n"
want="$(printf '%s' "Paused for maintenance; back (soon) 'ok' b$x" | head -c 200)"; [ "${#want}" = 200 ] || { echo "FAIL: test setup"; exit 1; }
for c in next 'submit L-t-1'; do pnp $c; stopped "$c" "$want"; ! grep -q SECOND "$t/err" || { echo "FAIL: second line printed"; exit 1; }; done
! LC_ALL=C grep -q "$(printf '\033')" "$t/err" || { echo "FAIL: an escape reached the terminal"; exit 1; }

# d. GitHub cannot be read (the repository is missing): one line says so and the step goes on, even with a STOP on the host
host "$t/missing.git"
pnp next; [ "$rc" = 0 ] || { echo "FAIL: next exit $rc"; cat "$t/err"; exit 1; }; desk 'GET /next?handle=tester'
[ "$(grep -c . "$t/err")" = 1 ] && grep -qx 'note: the stop notice on GitHub could not be read; going on' "$t/err" || { echo "FAIL: next said:"; cat "$t/err"; exit 1; }
pnp submit L-t-1; grep -q 'is not the file that was checked' "$t/err" && grep -qx 'note: the stop notice on GitHub could not be read; going on' "$t/err" || { cat "$t/err"; exit 1; }

# d2. GitHub hangs: the fetch is given up after about 15 s (no `timeout` on stock macOS) and the step goes on
real="$(command -v git)"; printf '#!/bin/bash\n[ "$1" = fetch ] && exec sleep 60\nexec "%s" "$@"\n' "$real" > "$t/bin/git"; chmod +x "$t/bin/git"
host "$t/host.git"; s=$SECONDS; pnp next; d=$((SECONDS - s)); rm "$t/bin/git"
[ "$rc" = 0 ] && [ "$d" -ge 14 ] && [ "$d" -le 25 ] || { echo "FAIL: hang: exit $rc after ${d}s"; cat "$t/err"; exit 1; }
desk 'GET /next?handle=tester'; grep -q 'could not be read' "$t/err" || { cat "$t/err"; exit 1; }

# e. none of the checks above moved the contributor's branch, commit, index, staged, unstaged or untracked changes
look | cmp -s - "$t/before" || { echo "FAIL: the working tree, index or branch changed"; look | diff "$t/before" - ; exit 1; }
notice ''; pnp next; quiet next; look | cmp -s - "$t/before" || { echo "FAIL: changed after the notice was taken down"; exit 1; }
echo "pnp stop: pass"
