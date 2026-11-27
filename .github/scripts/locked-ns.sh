#!/bin/sh
# The first process of the locked build's own namespaces (started by lake-locked.sh as root, through
# sudo unshare). It makes the namespace safe, says so in the ready file, then becomes the build account
# and runs the build. Fixed text; every value reaches it as a positional parameter.
#
# WHY (red team, rehearsal 1 of the batch patch, 2026-11-24): on a stock hosted runner the build
# account can WRITE about 473,000 existing paths by their file modes (/usr/local, the tool cache,
# /usr/share, /opt ...), and our own steps read and run from some of them after the build. File modes
# of an image we do not own cannot be fixed by listing them. So inside this namespace EVERY mount is
# made read-only (and nodev, nosuid), then exactly the places the build needs are mounted writable:
# fresh small tmpfs over the temp directories and its home, and a bind of its own output directories.
# That is a property of the namespace, whatever the image's file modes are, and it costs a second.
# Then the namespace's own mount table is read: any other writable mount, or a mount that allows
# device files other than /dev itself, and the build does not start.
#
#   locked-ns.sh <ready file> <toolchain bin> <threads> <git config> <writable dirs, colon-separated> <command...>
# The ready file (the caller's, in a directory only the caller's account can enter) gets one line,
# "namespace ready", only after the check below passed; the caller treats anything else as our fault.
# It arrives OPEN on descriptor 4, opened by the caller BEFORE the namespace was made (rehearsal 1: a
# file opened for writing inside it, on the root mount, keeps / from turning read-only: "mount point is
# busy"); it is closed before the build account starts. The first argument names it, for the record.
# The system's own tools only (red team, second wall): sudo hands this root process its secure path,
# which lists /usr/local/bin ahead of /usr/bin.
PATH=/usr/bin:/bin; export PATH
set -eu
tc=$2; threads=$3; gitcfg=$4; rwdirs=$5; shift 5
mount --make-rprivate /
# 0. Our own /proc for our own process namespace, mounted by THIS script (red team, 2026-11-24: a proc
#    mounted on top of the inherited one would leave the covered one writable and in the table). The
#    inherited /proc and everything under it are detached first.
#    The new proc is mounted at a spare directory first and moved into place, so the mount tool never
#    runs without a /proc (red team note, 15:37Z).
mkdir -p /tmp/.pnp-proc
mount -n -t proc -o nosuid,nodev,noexec proc /tmp/.pnp-proc
umount -n -l /proc
mount -n --move /tmp/.pnp-proc /proc
# 1. every mount read-only, no set-user-id, no device files (except /dev and /dev/pts, which hold the
#    standard device nodes; the world-writable odd ones there are closed by the workflow beforehand).
#    Mount points are read from this namespace's own table; octal escapes (\040) decoded. A remount by
#    path reaches the TOP mount at that path; a mount covered by another is judged below as covered.
#    Every remount is made with -n (no bookkeeping written): rehearsal 1 saw the snap images' remount
#    succeed and the mount tool then fail writing its own table under /run, by then read-only (red team).
#    A mount that still cannot be remounted is DETACHED from this private namespace instead (the runner
#    keeps it; the build needs none of them). Whatever is left, the judge below reads the final table:
#    a mount still writable, or allowing set-user-id or device files, stops the build. So a failure here
#    can only ever stop a build, never open one.
n0=$(wc -l < /proc/self/mountinfo)
# Snap images mounted at this moment (red team, a permanent line: rehearsal 1 saw them stop 3 runs of 15).
snaps=$(awk '$5 ~ "^/snap/" { n++ } END { print n + 0 }' /proc/self/mountinfo)
awk '{print $5}' /proc/self/mountinfo | while IFS= read -r m; do
  m=$(printf '%b' "$m")
  case "$m" in
    (/dev|/dev/pts) o=remount,bind,ro,nosuid ;;
    (*) o=remount,bind,ro,nosuid,nodev ;;
  esac
  mount -n -o "$o" "$m" 2>/dev/null || umount -n -l "$m" 2>/dev/null || true
done
detached=$(( n0 - $(wc -l < /proc/self/mountinfo) ))
# 2. the places the build may write, each recorded by its MOUNT ID the moment it is made, so the judge
#    allows exactly these mounts and not whatever sits at their paths. Mode 1777 makes the tmpfs places
#    world-writable INSIDE this namespace only, where the build account is the one account that runs.
ours=" "
top_id() { awk -v m="$1" '$5 == m { id = $1 } END { print id }' /proc/self/mountinfo; }
TMPS="/tmp /var/tmp /dev/shm /run /var/crash /home/outsider"
for d in $TMPS; do
  if [ -d "$d" ]; then
    mount -n -t tmpfs -o size=256m,nosuid,nodev,mode=1777 pnp-tmp "$d"
    ours="$ours$(top_id "$d") "
  fi
done
chown outsider:outsider /home/outsider; chmod 0700 /home/outsider
#    and its own output directories, each bound onto itself and made writable again.
IFS=:
for d in $rwdirs; do
  [ -d "$d" ] && [ ! -L "$d" ] || { echo "not a directory: an output directory of the build" >&2; exit 98; }
  mount -n --bind "$d" "$d" && mount -n -o remount,bind,rw,nosuid,nodev "$d"
  ours="$ours$(top_id "$d") "
done
unset IFS
# 3. THE CHECK, from this namespace's own mount table (field 1 mount id, 2 parent id, 5 mount point,
#    6 the mount's own flags). Every mount has nosuid, and nodev unless it is /dev or /dev/pts. A
#    writable mount passes only if its id is one of ours, OR it is COVERED: another mount whose parent
#    is it sits at the same path (that covering mount is judged on its own line).
judge() {
  awk -v ours="$ours" '
    { id[NR] = $1; par[NR] = $2; mp[NR] = $5; fl[NR] = "," $6 ","; covered[$2 " " $5] = 1 }
    END {
      for (i = 1; i <= NR; i++) {
        # A covered mount is reached by no path, so its own flags do not matter (red team note).
        if ((id[i] " " mp[i]) in covered) continue
        if (fl[i] !~ /,nosuid,/) print "set-user-id allowed: " mp[i]
        if (mp[i] != "/dev" && mp[i] != "/dev/pts" && fl[i] !~ /,nodev,/) print "device files allowed: " mp[i]
        if (fl[i] ~ /,rw,/ && index(ours, " " id[i] " ") == 0) print "writable: " mp[i]
      }
    }' /proc/self/mountinfo
}
bad=$(judge)
if [ -n "$bad" ]; then
  printf '%s\n' "$bad" | tr -cd 'A-Za-z0-9_./:, \n-' | head -n 5 >&2
  exit 98
fi
# One line for the log: how many mounts are read-only, and which are writable (our own places only).
awk '{print $5, $6}' /proc/self/mountinfo | awk -v d="$detached" -v sn="$snaps" '{ split($2, f, ","); if (f[1] == "ro") r++; else w = w " " $1 } END { print "mounts: " r " read-only; detached: " d "; snap images at the probe: " sn "; writable:" w }' \
  | tr -cd 'A-Za-z0-9_./:;, \n-' >&4
echo "namespace ready" >&4
exec 4>&-
exec setpriv --reuid=outsider --regid=outsider --init-groups --no-new-privs \
  env -i HOME=/home/outsider LANG=C.UTF-8 PATH="$tc:/usr/bin:/bin" \
    LAKE_ARTIFACT_CACHE=false LEAN_NUM_THREADS="$threads" \
    GIT_CONFIG_GLOBAL="$gitcfg" GIT_CONFIG_NOSYSTEM=1 \
  "$@"
