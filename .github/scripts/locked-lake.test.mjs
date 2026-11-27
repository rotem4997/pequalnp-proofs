// node --test .github/scripts/locked-lake.test.mjs
// THE LOCKED BUILD stays locked: every build of an outside file on this runner goes through
// .github/scripts/lake-locked.sh (the locked account, no credential of this run). The checker
// wrapper must never choose its own lake, and the workflow must hand it the locked one.
// (Operator's rehearsal, 2026-11-24: a fleet wrapper that set PEQUALNP_REAL_LAKE itself was copied
// here by mistake and would have built outside Lean as the workflow's account.)
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, mkdtempSync, rmSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
const root = new URL('../../', import.meta.url);
const wrapper = readFileSync(new URL('tools/check-lean.mjs', root), 'utf8');
const workflow = readFileSync(new URL('.github/workflows/authoritative.yml', root), 'utf8');
test('the checker wrapper never sets the lake it builds with', () => {
  assert.doesNotMatch(wrapper, /PEQUALNP_REAL_LAKE\s*=|\[\s*['"]PEQUALNP_REAL_LAKE['"]\s*\]\s*=/, 'tools/check-lean.mjs assigns PEQUALNP_REAL_LAKE');
  assert.doesNotMatch(wrapper, /\bREAL_LAKE\b/, 'tools/check-lean.mjs names a REAL_LAKE of its own');
});
test('the workflow runs the checker with the locked lake', () => {
  assert.match(workflow, /PEQUALNP_REAL_LAKE="\$W\/base\/\.github\/scripts\/lake-locked\.sh"[^\n]*\\\n(?:[^\n]*\\\n)*[^\n]*"\$node_bin\/node" "\$W\/base\/tools\/check-lean\.mjs"/, 'the check-lean.mjs call is not given lake-locked.sh as its lake');
});
// All-cores, GATED (red team, 22:00Z): every core only on our dispatch with cores=all; empty keeps today's pin
// (cores 0 and 1, three threads); a reduction keeps it whatever the input; any other value is refused first.
test('all-cores is gated: empty keeps the two-core pin, a reduction keeps it, other values refused', () => {
  const wf = readFileSync(new URL('../workflows/authoritative.yml', import.meta.url), 'utf8');
  assert.match(wf, /case "\$CORES" in ''\|all\) ;; \*\) echo "REFUSED: cores must be empty or all"; exit 1 ;; esac/);
  assert.match(wf, /if \[ "\$\{CORES:-\}" != all \]; then ncpu=2; nthr=3; fi/);
  assert.match(wf, /if \[ "\$\(cat "\$W\/in\/gap.kind"\)" = reduce \]; then ncpu=2; nthr=3; fi/);
  assert.match(wf, /taskset -c "0-\$\(\(ncpu - 1\)\)"/);
  assert.match(wf, /PNP_LEAN_THREADS="\$nthr"/);
});
const locked = readFileSync(new URL('.github/scripts/lake-locked.sh', root), 'utf8');
const ns = readFileSync(new URL('.github/scripts/locked-ns.sh', root), 'utf8');
test('the locked build always runs inside locked-ns.sh, never setpriv directly (red team, 2026-11-24)', () => {
  assert.doesNotMatch(locked, /setpriv/, 'lake-locked.sh starts the build account itself');
  assert.match(locked, /exec 4>>"\$1"; shift; exec \/usr\/bin\/unshare --net --ipc --mount --pid --fork -- \/bin\/sh "\$@"' pnp-ready \\\n\s+"\$log\/ns" "\$here\/locked-ns\.sh"/, 'the ready file is not opened before the namespace, or locked-ns.sh is not what runs in it');
  assert.doesNotMatch(ns, /exec 4>>/, 'locked-ns.sh opens the ready file inside the namespace (it keeps / from turning read-only)');
  assert.doesNotMatch(locked, /--mount-proc/, "a proc mounted on top of the inherited one leaves the covered one writable");
  assert.match(locked, /grep -qx 'namespace ready'/, 'lake-locked.sh does not read the ready file');
});
test('locked-ns.sh: every mount read-only, then the writable places, then the check, then the account', () => {
  const at = (re) => { const m = ns.search(re); assert.ok(m >= 0, `missing ${re}`); return m; };
  const ro = at(/remount,bind,ro,nosuid,nodev/), tmp = at(/mount -n -t tmpfs/), bind = at(/remount,bind,rw/);
  const judge = at(/^bad=\$\(judge\)/m), ready = at(/echo "namespace ready" >&4/), drop = at(/^exec setpriv/m);
  assert.ok(ro < tmp && tmp < bind && bind < judge && judge < ready && ready < drop, 'the order of the steps changed');
  assert.match(ns, /exec 4>&-\n/, 'the ready file stays open for the build account');
});
test('after the build: the system PATH only, and the checker on the node copied before it (second wall)', () => {
  assert.match(workflow, /export PATH=\/usr\/bin:\/bin\n\s+echo "the checker step runs with PATH=\$PATH"\n\s+node_bin="\$RUNNER_TEMP\/node"/, 'the run step does not pin PATH and the node copy');
  assert.match(workflow, /install -m 0700 "\$src" "\$RUNNER_TEMP\/node\/node"/, 'no node copy is taken before the build');
  assert.ok((workflow.match(/export PATH=\/usr\/bin:\/bin/g) || []).length >= 2, 'the verdict step does not pin PATH');
});
test('second wall: both namespace scripts pin PATH first, and every sudo after the lock step names its program by full path', () => {
  for (const [name, text] of [['lake-locked.sh', locked], ['locked-ns.sh', ns]]) {
    const pin = text.search(/^PATH=\/usr\/bin:\/bin; export PATH$/m), first = text.search(/^(set |exec |case |[a-z_]+=)/m);
    assert.ok(pin >= 0 && pin <= first, `${name} does not pin PATH before anything runs`);
  }
  assert.doesNotMatch(locked, /sudo -n (?!\/)/, 'lake-locked.sh hands sudo a bare name');
  const run = workflow.slice(workflow.indexOf('- name: Run the BASE checker'), workflow.indexOf("- name: Print the checker's last line"));
  assert.doesNotMatch(run, /sudo (?!\/usr\/bin\/)/, 'the run step hands sudo a bare name');
});
test('the launch line RUNS: locked-ns.sh gets the ready file first, then the toolchain, and writes through descriptor 4', () => {
  // The fixed program of lake-locked.sh's build launch, with the namespace tool replaced by plain env:
  // what reaches the script, in what order, and the inherited descriptor (a dropped shift once broke it).
  const prog = locked.match(/sudo -n \/bin\/sh -c '([^']*)' pnp-ready/)[1].replace(/\/usr\/bin\/unshare --net --ipc --mount --pid --fork --/, '/usr/bin/env');
  const d = mkdtempSync(join(tmpdir(), 'pnp-launch-'));
  try {
    const ready = join(d, 'ready'), stub = join(d, 'ns.sh'); writeFileSync(ready, '');
    writeFileSync(stub, 'printf "%s|" "$@"; echo "namespace ready" >&4\n');
    const out = execFileSync('/bin/sh', ['-c', prog, 'pnp-ready', ready, stub, ready, 'TC', '3', 'CFG', 'RW', 'lake', 'build', 'X'], { encoding: 'utf8' });
    assert.equal(out, `${ready}|TC|3|CFG|RW|lake|build|X|`, 'the script got its arguments in the wrong order');
    assert.equal(readFileSync(ready, 'utf8'), 'namespace ready\n', 'the ready line did not arrive through descriptor 4');
  } finally { rmSync(d, { recursive: true, force: true }); }
});
// Two permanent lines asked before the merge (red team, rehearsal 2): the snap images mounted at the moment of the
// probe, counted inside the namespace before the remount loop, on the mounts line; and the checker step's PATH.
test('the mounts line names the snap images at the probe; the checker step prints its PATH', () => {
  const ns = readFileSync(new URL('./locked-ns.sh', import.meta.url), 'utf8');
  assert.match(ns, /n0=\$\(wc -l < \/proc\/self\/mountinfo\)\n(#[^\n]*\n)*snaps=\$\(awk '\$5 ~ "\^\/snap\/"/, 'the snap count is not taken before the remount loop');
  assert.match(ns, /snap images at the probe: " sn/, 'the mounts line does not carry the snap count');
  const wf = readFileSync(new URL('../workflows/authoritative.yml', import.meta.url), 'utf8');
  assert.match(wf, /echo "the checker step runs with PATH=\$PATH"/);
});
