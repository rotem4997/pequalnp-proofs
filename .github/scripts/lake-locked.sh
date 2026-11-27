#!/bin/sh
# The `lake` the authoritative workflow hands to the checker (through PEQUALNP_REAL_LAKE, the
# place tools/bin/lake reads the real lake from). The checker itself is not changed.
#
# `lake build` is the one command that compiles the proof file, and a Lean file can run code
# while it compiles. So every build runs as the account `outsider`: no network, an empty
# environment, no way to gain privileges, and write access to nothing but the output
# directories of its own module. Every other lake command (the verifier's run) is the plain
# pinned lake, run by the workflow's own account, which that compile cannot touch.
# The system's own tools only, whatever a build left on the runner's PATH (red team, second wall).
PATH=/usr/bin:/bin; export PATH
set -eu
: "${PNP_TC_BIN:?the toolchain bin directory}" "${PNP_GITCONFIG:?the git config file}"
: "${PNP_RW_DIRS:?the output directories of the build, colon-separated}"
here=$(cd "$(dirname "$0")" && pwd)
case "${1:-}" in
  build)
    code=0
    # The whole output of the build is kept (the checker passes on only its last lines), then
    # handed to the caller unchanged, stream by stream. The directory and the two files are
    # created by THIS account, closed to every other (0700): the locked build holds only the
    # two open descriptors, as it held the caller's pipes before. It can write text into them
    # and nothing else, so their content is as untrusted as any build output.
    log=$(mktemp -d "${PNP_BUILD_LOGS:-${TMPDIR:-/tmp}}/build.XXXXXX")
    # Its own namespaces: no network; its own process tree, whose first process is the build, so
    # when the build ends the kernel ends everything it started; its own IPC objects; its own mounts,
    # where everything is read-only but the places it must write (locked-ns.sh, which says why).
    : > "$log/ns"
    # The ready file is opened (as root, descriptor 4) BEFORE the namespace is made, and inherited.
    sudo -n /bin/sh -c 'exec 4>>"$1"; shift; exec /usr/bin/unshare --net --ipc --mount --pid --fork -- /bin/sh "$@"' pnp-ready \
        "$log/ns" "$here/locked-ns.sh" "$log/ns" "$PNP_TC_BIN" "${PNP_LEAN_THREADS:-${LEAN_NUM_THREADS:-3}}" "$PNP_GITCONFIG" "$PNP_RW_DIRS" "$PNP_TC_BIN/lake" "$@" \
      > "$log/out" 2> "$log/err" || code=$?
    # Nothing a build started may outlive it: the compiled result is read only once it is still.
    sudo -n /usr/bin/pkill -KILL -u outsider || true
    # A namespace that did not say it was ready: the build never ran as it should. That is OUR fault,
    # never the proof's: the marker file tells the workflow, which reports a FAULT, never a verdict.
    if ! grep -qx 'namespace ready' "$log/ns" 2>/dev/null; then
      echo "the locked build's namespace was not ready (exit $code)" > "$log/nsfail"; code=97
    fi
    printf '%s\n' "lake $* (exit $code)" > "$log/cmd"
    cat "$log/out"; cat "$log/err" >&2
    exit "$code" ;;
  probe)
    # The same namespace with a command that does nothing, run by the workflow BEFORE any outside file
    # is placed: a runner on which the namespace cannot be made ready stops there, with no file judged.
    log=$(mktemp -d "${PNP_BUILD_LOGS:-${TMPDIR:-/tmp}}/probe.XXXXXX"); : > "$log/ns"; code=0
    sudo -n /bin/sh -c 'exec 4>>"$1"; shift; exec /usr/bin/unshare --net --ipc --mount --pid --fork -- /bin/sh "$@"' pnp-ready \
        "$log/ns" "$here/locked-ns.sh" "$log/ns" "$PNP_TC_BIN" 1 "$PNP_GITCONFIG" "$PNP_RW_DIRS" /bin/true 2> "$log/err" || code=$?
    if grep -qx 'namespace ready' "$log/ns" 2>/dev/null && [ "$code" = 0 ]; then echo "the namespace of the locked build: ready; $(grep -m 1 '^mounts: ' "$log/ns")"; exit 0; fi
    why=`tr -cd 'A-Za-z0-9_./:, \n-' < "$log/err" | head -n 5 | tr '\n' ' '`
    echo "the namespace of the locked build could not be made ready (exit $code): $why"
    exit 1 ;;
  *)
    exec "$PNP_TC_BIN/lake" "$@" ;;
esac
