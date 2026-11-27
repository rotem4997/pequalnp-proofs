// node --test .github/scripts/memory-watch.test.mjs     (PNP_WATCH_REAL=1 adds a run at the real 15 s interval)
// THE MEMORY WATCH, W1 and W2 (red team ruling, 2026-11-25). The watch (memory-watch.sh) runs here on stubbed
// /proc/meminfo, /proc/pressure/memory and cgroup files, as a fast run and a slow run. Only the test's copy is
// changed: the /proc root, the interval, the kill (it records instead of ending a scope), and two test lines
// at the top of the loop (the sample's meminfo for this tick; a stop after the last tick).
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, mkdtempSync, mkdirSync, rmSync, existsSync, copyFileSync } from 'node:fs';
import { spawn } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const script = readFileSync(new URL('./memory-watch.sh', import.meta.url), 'utf8');
const workflow = readFileSync(new URL('../workflows/authoritative.yml', import.meta.url), 'utf8');
const TOTAL = 16000000; // kB, a 16 GB runner
const meminfo = (pct) => `MemTotal:       ${TOTAL} kB\nMemFree:        1000 kB\nMemAvailable:   ${Math.floor(TOTAL * pct / 100)} kB\nSwapTotal:      8000000 kB\nSwapFree:       6000000 kB\n`;
const pressure = (full) => `some avg10=50.00 avg60=${full}.00 avg300=5.00 total=1\nfull avg10=50.00 avg60=${full}.37 avg300=5.00 total=1\n`;

function testCopy(dir, interval, maxTick) {
  const swap = (s, a, b) => { assert.ok(s.includes(a), `memory-watch.sh no longer has: ${a}`); return s.replace(a, b); };
  let s = script;
  s = swap(s, 'PROC=/proc\n', `PROC='${dir}/proc'\n`);
  s = swap(s, 'INTERVAL=15\n', `INTERVAL=${interval}\n`);
  s = swap(s, 'kill_scope() { sudo /usr/bin/systemctl kill --signal=KILL "$unit.scope" 2>/dev/null || true; }',
              `kill_scope() { echo "killed $unit.scope" >> '${dir}/killed'; }`);
  s = swap(s, '  tick=$((tick + 1))\n',
              `  tick=$((tick + 1))\n  [ "$tick" -gt ${maxTick} ] && { echo "TEST: stopped after ${maxTick} samples"; break; }\n  [ -f "$PROC/meminfo.$tick" ] && cp "$PROC/meminfo.$tick" "$PROC/meminfo"\n`);
  const f = join(dir, 'watch.sh'); writeFileSync(f, s); return f;
}

// samples: the available percent at each tick; full: pressure full avg60; cgFiles: whether the scope's files exist.
function runCase({ samples, full, cgFiles, maxTick }, interval) {
  const dir = mkdtempSync(join(tmpdir(), 'pnp-watch-'));
  mkdirSync(join(dir, 'proc', 'pressure'), { recursive: true });
  mkdirSync(join(dir, 'sampler')); mkdirSync(join(dir, 'cg'));
  samples.forEach((p, i) => writeFileSync(join(dir, 'proc', `meminfo.${i + 1}`), meminfo(p)));
  copyFileSync(join(dir, 'proc', 'meminfo.1'), join(dir, 'proc', 'meminfo'));
  writeFileSync(join(dir, 'proc', 'pressure', 'memory'), pressure(full));
  writeFileSync(join(dir, 'cg', 'cpu.stat'), 'usage_usec 5000000\nuser_usec 1\n');
  if (cgFiles) {
    writeFileSync(join(dir, 'cg', 'memory.current'), String(9 * 1048576 * 1024));
    writeFileSync(join(dir, 'cg', 'memory.peak'), String(10 * 1048576 * 1024));
    writeFileSync(join(dir, 'cg', 'memory.stat'), 'anon 7340032000\nfile 1048576000\nkernel 1\nshmem 2097152\nfile_mapped 3\n');
    writeFileSync(join(dir, 'cg', 'memory.events'), 'low 0\nhigh 0\nmax 12\noom 0\noom_kill 0\noom_group_kill 0\n');
    writeFileSync(join(dir, 'cg', 'memory.swap.current'), String(3 * 1048576 * 1024));
  }
  const err = join(dir, 'checker.err'), mark = join(dir, 'markers');
  writeFileSync(err, 'checker stage: building the verifier t=3s\n'); writeFileSync(mark, '');
  const f = testCopy(dir, interval, maxTick);
  return new Promise((resolve, reject) => {
    const p = spawn('/bin/sh', [f, join(dir, 'sampler'), join(dir, 'cg'), 'pnp-check-1', String(Math.floor(Date.now() / 1000)), '12700000', mark, err]);
    let out = ''; p.stdout.on('data', (d) => { out += d; }); p.stderr.on('data', (d) => { out += d; });
    const guard = setTimeout(() => { p.kill('SIGKILL'); reject(new Error('the watch did not end')); }, (maxTick + 4) * interval * 1000 + 10000);
    p.on('close', (code) => {
      clearTimeout(guard);
      const r = { code, out, err: readFileSync(err, 'utf8'), mark: readFileSync(mark, 'utf8'),
                  killed: existsSync(join(dir, 'killed')) ? readFileSync(join(dir, 'killed'), 'utf8') : '' };
      rmSync(dir, { recursive: true, force: true }); resolve(r);
    });
  });
}

const ENDED = /^memory watch: the MACHINE is running short \(available \d+ MB, pressure full \d+%\): ending the checker before the runner is lost$/m;
const cases = {
  a: { samples: [45, 45, 45, 45], full: 45, cgFiles: true, maxTick: 4 },  // pressure high, 45% available
  b: { samples: [12, 45, 45, 45], full: 45, cgFiles: true, maxTick: 4 },  // 12% for one sample only
  c: { samples: [12, 12, 45, 45], full: 45, cgFiles: true, maxTick: 4 },  // 12% for two samples
  d: { samples: [4, 4, 45, 45], full: 0, cgFiles: false, maxTick: 4 },    // under 5% alone (W2 files missing)
  d1: { samples: [4, 45, 4, 45], full: 0, cgFiles: false, maxTick: 4 },   // under 5% never twice in a row
  e: { samples: [12, 12, 12, 12], full: 40, cgFiles: true, maxTick: 4 },  // pressure exactly 40: not over it
};

function judge(name, r) {
  const ended = ENDED.test(r.mark);
  switch (name) {
    case 'a': case 'b': case 'd1': case 'e':
      assert.equal(ended, false, `${name}: ended\n${r.out}`); assert.equal(r.killed, '', `${name}: the scope was killed`);
      assert.match(r.out, /TEST: stopped after 4 samples/, `${name}: did not run its four samples`);
      assert.doesNotMatch(r.out, /memory watch, the checker scope/, `${name}: printed W2 lines without an ending`);
      break;
    case 'c': {
      assert.ok(ended, `c: not ended\n${r.out}`); assert.equal(r.killed, 'killed pnp-check-1.scope\n');
      assert.doesNotMatch(r.out, /TEST: stopped/, 'c: ran past its ending');
      assert.match(r.mark, /available 1875 MB, pressure full 45%/, 'c: not ended on the second 12% sample');
      const w2 = ['memory.stat anon 7340032000', 'memory.stat file 1048576000', 'memory.stat shmem 2097152',
                  'memory.events low 0, high 0, max 12, oom 0, oom_kill 0, oom_group_kill 0', 'swap in use 3072 MB (memory.swap.current)'];
      for (const s of w2) { assert.ok(r.out.includes(`memory watch, the checker scope: ${s}`), `c: no W2 line "${s}" on the live log\n${r.out}`);
                            assert.ok(r.err.includes(`memory watch, the checker scope: ${s}`), `c: no W2 line "${s}" in checker.err`); }
      // W2 comes FIRST, then the ending line.
      assert.ok(r.err.indexOf('memory.stat anon') < r.err.search(ENDED), 'c: the W2 lines came after the ending line');
      break; }
    case 'd': {
      assert.ok(ended, `d: not ended\n${r.out}`); assert.equal(r.killed, 'killed pnp-check-1.scope\n');
      assert.match(r.mark, /available 625 MB, pressure full 0%/);
      for (const s of ['memory.stat anon n/a', 'memory.stat file n/a', 'memory.stat shmem n/a', 'memory.events n/a'])
        assert.ok(r.out.includes(`memory watch, the checker scope: ${s}`), `d: missing "${s}"\n${r.out}`);
      assert.ok(r.out.includes('memory watch, the machine: swap in use 1953 MB (/proc/meminfo; memory.swap.current n/a)'), `d: swap from /proc/meminfo\n${r.out}`);
      assert.equal(r.code, 0, 'd: a missing file failed the watch');
      break; }
  }
}

for (const [label, interval, on] of [['fast', 0.05, true], ['slow', 2, true], ['real 15 s', 15, process.env.PNP_WATCH_REAL === '1']]) {
  test(`the memory watch, W1 and W2: the ${label} run`, { skip: !on && 'set PNP_WATCH_REAL=1' }, async () => {
    const names = Object.keys(cases);
    const rs = await Promise.all(names.map((n) => runCase(cases[n], interval)));
    names.forEach((n, i) => judge(n, rs[i]));
  });
}

test('the workflow runs the watch from its script, and the inline loop is gone', () => {
  assert.match(workflow, /sh "\$W\/base\/\.github\/scripts\/memory-watch\.sh" "\$RUNNER_TEMP\/sampler" "\$cg" "\$unit" "\$t0" "\$cap" "\$MARK" "\$RUNNER_TEMP\/checker\.err" &\n\s+watch=\$!/);
  assert.doesNotMatch(workflow, /low=0; tick=0/, 'an inline copy of the watch is still in the workflow');
  assert.equal((workflow.match(/base\/\.github\/scripts\/lake-locked\.sh base\/\.github\/scripts\/memory-watch\.sh \$\(cat in\/outside-sources\.txt\)/g) || []).length, 2,
    'memory-watch.sh is not hashed before and after the hostile step');
});

test('the 5 percent rule is the one it was, alone; the pressure rule needs two samples under 15 percent', () => {
  assert.match(script, /if \[ "\$avail" -lt \$\(\(total \/ 20\)\) \]; then low=\$\(\(low \+ 1\)\); else low=0; fi/);
  assert.match(script, /if \[ "\$avail" -lt \$\(\(total \* 3 \/ 20\)\) \]; then low15=\$\(\(low15 \+ 1\)\); else low15=0; fi/);
  assert.match(script, /if \[ "\$low" -ge 2 \] \|\| \{ \[ "\$\{full:-0\}" -gt 40 \] && \[ "\$low15" -ge 2 \]; \}; then/);
  assert.match(script, /^PATH=\/usr\/bin:\/bin; export PATH$/m, 'memory-watch.sh does not pin PATH');
});
