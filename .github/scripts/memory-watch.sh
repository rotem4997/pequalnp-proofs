#!/bin/sh
# THE MEMORY WATCH and THE NO-PROGRESS WATCHDOG of the checker step (authoritative.yml says why each exists).
# Moved here from the workflow's inline shell so its logic can be tested (memory-watch.test.mjs); the
# behaviour is the same as inline, apart from W1 and W2 below (red team ruling, 2026-11-25).
#
#   memory-watch.sh <sampler dir> <checker scope's cgroup dir> <scope unit> <t0> <checker cap, kB> <markers file> <checker.err>
#
# It ends when <sampler dir>/done appears, or after it ended the checker scope.
# W1 (2026-11-25: the watch ended two honest checks with 7 GB of 16 available and pressure full at 42 to
#   46 percent): pressure full over 40 percent ends a check only when available memory is ALSO under 15
#   percent of the machine's total for two samples in a row. Available memory under 5 percent for two
#   samples in a row ends it alone, as before. Either ending is a FAULT and a re-run, never a verdict.
# W2: before any ending by this watch, the checker scope's memory.stat (anon, file, shmem), its
#   memory.events and the swap in use are printed, read-only; a missing file prints n/a.
PATH=/usr/bin:/bin; export PATH
set -u
S=$1; cg=$2; unit=$3; t0=$4; cap=$5; MARK=$6; ERR=$7
PROC=/proc
INTERVAL=15
kill_scope() { sudo /usr/bin/systemctl kill --signal=KILL "$unit.scope" 2>/dev/null || true; }
# The checker's last stage, printed ONLY as one of our own fixed stage names (red team: once
# Lean runs on the file, stderr can carry the author's text; nothing of it is printed).
stage_now() {
  last=$(grep -a '^checker stage: ' "$ERR" 2>/dev/null | tail -n 1 | sed 's/^checker stage: //; s/ t=[0-9]*s$//')
  case "$last" in
    'started'|'build lock taken'|'building the verifier'|'building the file and the definitions root'|'verifier reading the built file') echo "stage: $last" ;;
    '') echo "stage: none yet" ;;
    *) echo "stage: (unrecognised line, not printed)" ;;
  esac
}
# W2: digits only from each kernel file, so nothing but our own fixed words and numbers is printed.
num() { v=$(printf '%s' "$1" | tr -cd '0-9'); [ -n "$v" ] && echo "$v" || echo n/a; }
scope_state() {
  for k in anon file shmem; do
    v=n/a; [ -r "$cg/memory.stat" ] && v=$(num "$(awk -v k="$k" '$1 == k { print $2 }' "$cg/memory.stat" 2>/dev/null)")
    echo "memory watch, the checker scope: memory.stat $k $v"
  done
  ev=n/a
  if [ -r "$cg/memory.events" ]; then
    ev=$(awk '{ printf "%s%s %s", (NR > 1 ? ", " : ""), $1, $2 }' "$cg/memory.events" 2>/dev/null | tr -cd 'a-z_0-9, ')
    [ -n "$ev" ] || ev=n/a
  fi
  echo "memory watch, the checker scope: memory.events $ev"
  sw=$(cat "$cg/memory.swap.current" 2>/dev/null)
  if printf '%s' "$sw" | grep -Eqx '[0-9]+'; then echo "memory watch, the checker scope: swap in use $((sw / 1048576)) MB (memory.swap.current)"
  else
    sw=$(awk '/^SwapTotal:/{t=$2} /^SwapFree:/{f=$2} END{ if (t != "") print t-f }' "$PROC/meminfo" 2>/dev/null)
    if printf '%s' "$sw" | grep -Eqx '[0-9]+'; then echo "memory watch, the machine: swap in use $((sw / 1024)) MB (/proc/meminfo; memory.swap.current n/a)"
    else echo "memory watch, the machine: swap in use n/a"; fi
  fi
}
low=0; low15=0; tick=0; cpu0=0; still=0; dog=on; beat=$(date +%s); maxgap=0
while sleep "$INTERVAL"; do
  [ -e "$S/done" ] && break
  tick=$((tick + 1))
  # The watch's own beat (red team M1): the largest gap between two samples, for the rehearsal.
  nb=$(date +%s); [ $((nb - beat)) -gt "$maxgap" ] && maxgap=$((nb - beat)) && echo "$maxgap" > "$S/maxgap"; beat=$nb
  cpu=""; while read -r ck cv; do [ "$ck" = usage_usec ] && cpu=$cv; done 2>/dev/null < "$cg/cpu.stat"
  if [ "$dog" = on ] && ! printf '%s' "$cpu" | grep -Eqx '[0-9]+'; then dog=off; echo "no-progress watchdog: OFF for this run (the checker scope's cpu.stat cannot be read)"; fi
  if [ "$dog" = on ]; then
    if [ "$cpu" -ge $((cpu0 + 2000000)) ]; then cpu0=$cpu; still=0; else still=$((still + 1)); fi
    echo "$still" > "$S/still"
  fi
  if [ "$dog" = on ] && [ "$still" -ge 32 ]; then
    scope_state | tee -a "$ERR"
    echo "no progress: the check made no progress for 8 minutes (CPU time $((cpu / 1000000)) s; last: $(stage_now)); ending the whole checker scope" | tee -a "$ERR" "$MARK"
    kill_scope
    break
  fi
  total=$(awk '/^MemTotal:/{print $2}' "$PROC/meminfo"); avail=$(awk '/^MemAvailable:/{print $2}' "$PROC/meminfo")
  swap=$(awk '/^SwapTotal:/{t=$2} /^SwapFree:/{f=$2} END{print t-f}' "$PROC/meminfo")
  now=$(cat "$cg/memory.current" 2>/dev/null || echo 0); peak=$(cat "$cg/memory.peak" 2>/dev/null || echo 0)
  printf '%s' "$peak" | grep -Eqx '[0-9]+' && echo "$peak" > "$S/peak"
  full=$(awk '/^full/{for(i=1;i<=NF;i++) if($i ~ /^avg60=/){sub("avg60=","",$i); print int($i)}}' "$PROC/pressure/memory" 2>/dev/null || echo 0)
  [ $((tick % 4)) -eq 0 ] || [ "$avail" -lt $((total / 10)) ] && echo "memory watch t=$(( $(date +%s) - t0 ))s: available $((avail / 1024)) MB of $((total / 1024)), swap used $((swap / 1024)) MB, checker now $((now / 1048576)) MB, peak $((peak / 1048576)) MB of $((cap / 1024)), pressure full $full%, $(stage_now)"
  if [ "$avail" -lt $((total / 20)) ]; then low=$((low + 1)); else low=0; fi
  # W1: samples in a row under 15 percent available; the pressure trigger needs two of them.
  if [ "$avail" -lt $((total * 3 / 20)) ]; then low15=$((low15 + 1)); else low15=0; fi
  if [ "$low" -ge 2 ] || { [ "${full:-0}" -gt 40 ] && [ "$low15" -ge 2 ]; }; then
    scope_state | tee -a "$ERR"
    echo "memory watch: the MACHINE is running short (available $((avail / 1024)) MB, pressure full $full%): ending the checker before the runner is lost" | tee -a "$ERR" "$MARK"
    kill_scope
    break
  fi
done
