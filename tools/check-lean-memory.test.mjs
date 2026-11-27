// node --test tools/check-lean-memory.test.mjs : the memory-death test check-lean uses before it calls a failed build a fault.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { counterRose, diedOfMemory, oomKills } from './check-lean-memory.mjs';

const cg = (kills) => {
  const d = mkdtempSync(join(tmpdir(), 'cg-'));
  mkdirSync(join(d, 'root/system.slice/pnp-check.scope'), { recursive: true });
  writeFileSync(join(d, 'proc'), '0::/system.slice/pnp-check.scope\n');
  writeFileSync(join(d, 'root/system.slice/pnp-check.scope/memory.events'), `low 0\nhigh 0\nmax 41\noom 1\noom_kill ${kills}\n`);
  return d;
};
const PANIC = 'INTERNAL PANIC: out of memory';

test('the counter rising is a memory death, whatever was printed', () => {
  const d = cg(1); const after = oomKills(join(d, 'proc'), join(d, 'root')); rmSync(d, { recursive: true });
  assert.equal(after, 1);
  assert.equal(diedOfMemory({ output: 'error: build failed', killsBefore: 0, killsAfter: after }), true);
  assert.equal(counterRose(0, after), true);
});
test('T2 (b): counter readable and UNCHANGED, the phrase printed by the build: NOT memory (stays exit 3)', () => {
  assert.equal(diedOfMemory({ output: `${PANIC}\nerror: build failed`, killsBefore: 3, killsAfter: 3 }), false);
});
test('T1 (a): a project-file error whose message carries the phrase, counter unchanged: counterRose is false, so check-lean keeps does-not-compile', () => {
  assert.equal(counterRose(3, 3), false);
  assert.equal(counterRose(null, null), false);
});
test("without a cgroup only the runtime's own line at the start of a line counts", () => {
  assert.equal(diedOfMemory({ output: `${PANIC}\nerror: build failed` }), true);
  assert.equal(diedOfMemory({ output: "terminate called after throwing an instance of 'std::bad_alloc'\n" }), true);
  assert.equal(diedOfMemory({ output: `error: ./PEqualNP/X.lean:3:2: unknown identifier '${PANIC}'` }), false);
  assert.equal(diedOfMemory({ output: 'the build ran out of memory, maybe\nCannot allocate memory' }), false);
});
test('an ordinary non-project failure is not a memory death', () => {
  assert.equal(diedOfMemory({ output: "error: unknown target 'X'\nerror: build failed", killsBefore: 2, killsAfter: 2 }), false);
  assert.equal(oomKills('/nonexistent/proc', '/nonexistent'), null);
  assert.equal(diedOfMemory({ output: 'error: lake: something else' }), false);
});
