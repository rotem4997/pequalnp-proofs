#!/bin/sh
# The pinned Lean toolchain, installed by a PINNED elan (red team ruling, 2026-11-25).
#
#   install-elan.sh <elan version, like v4.4.0> <sha256 of that release's linux x86_64 asset> <ELAN_HOME> <toolchain>
#
# WHY: the step used to pipe https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh into sh,
# and that script fetches the elan of releases/latest: code nobody pinned, run before the judged step. Now
# the one asset of one named release is downloaded into an empty temporary folder, its sha256 is compared
# with the pinned one BEFORE anything is extracted or run, and any other bytes stop the run with one fixed
# FAULT line (fail closed). The version and the hash are the workflow's ELAN_VERSION and ELAN_SHA256.
# WHY THE RETRIES (2026-11-24/25: about one run in ten failed on this download, curl (56) and HTTP 503,
# for twelve minutes): five tries, waits growing to a minute. Only a failed download is tried again; bytes
# that do not match the hash are never retried, they are a FAULT at once.
set -eu
ver=$1; want=$2; home=$3; toolchain=$4
waits="10 20 30 60"
fault() { echo "FAULT: $1"; exit 1; }
printf '%s' "$ver" | grep -Eqx 'v[0-9]+\.[0-9]+\.[0-9]+' || fault "the pinned elan version is not of the form v1.2.3"
printf '%s' "$want" | grep -Eqx '[0-9a-f]{64}' || fault "the pinned elan sha256 is not 64 hex digits"
arch=$(uname -m)
[ "$arch" = x86_64 ] || fault "this runner is not x86_64; the pinned elan asset is the x86_64 one"
url="https://github.com/leanprover/elan/releases/download/$ver/elan-x86_64-unknown-linux-gnu.tar.gz"
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
# Five tries of the download; the waits between them grow.
try() {
  for w in $waits ''; do
    "$@" && return 0
    [ -n "$w" ] || return 1
    echo "elan install: a download failed; trying again in $w s"
    sleep "$w"
  done
}
fetch() { rm -f "$tmp/elan.tar.gz"; curl -sSfL --proto '=https' --proto-redir '=https' --connect-timeout 20 --max-time 300 \
            --max-filesize 100000000 -o "$tmp/elan.tar.gz" "$url"; }
try fetch || fault "the pinned elan installer could not be downloaded (5 tries)"
got=$(sha256sum "$tmp/elan.tar.gz" | cut -d' ' -f1)
[ "$got" = "$want" ] || fault "the elan installer's sha256 is not the pinned one; nothing was extracted or run"
echo "elan $ver: sha256 $got (the pinned one)"
mkdir "$tmp/x"
tar -xzf "$tmp/elan.tar.gz" -C "$tmp/x" elan-init
[ -f "$tmp/x/elan-init" ] && [ ! -L "$tmp/x/elan-init" ] || fault "the elan archive holds no plain elan-init"
ELAN_HOME="$home" "$tmp/x/elan-init" -y --no-modify-path --default-toolchain none
# The toolchain download itself fails the same way, so it gets the same tries.
try env ELAN_HOME="$home" "$home/bin/elan" toolchain install "$toolchain" || fault "the pinned Lean toolchain could not be downloaded (5 tries)"
