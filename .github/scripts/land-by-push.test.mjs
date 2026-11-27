// Tests of land-by-push.mjs on local repositories: the red team's rehearsal list (2026-11-24 19:56 UTC), each case
// in its own pull request ref of a local bare "remote". node --test .github/scripts/land-by-push.test.mjs
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, writeFileSync, mkdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { run, parseList, checkCommitText, reserved, LeftOut, MAX_ENTRIES, pushStatus, MAX_TRIES, pushKind, remoteRejected, RETRY_REMOTE_REJECTED_IF_MAIN_MOVED, MAX_REMOTE_RETRIES } from './land-by-push.mjs';

process.env.LAND_TEST_FILE_TRANSPORT = '1';
const ENV = { PATH: '/usr/bin:/bin', GIT_CONFIG_NOSYSTEM: '1', GIT_CONFIG_GLOBAL: '/dev/null', LC_ALL: 'C' };
const ID = (name = 'Some One', email = 'someone@users.noreply.example') => ({ GIT_AUTHOR_NAME: name, GIT_AUTHOR_EMAIL: email, GIT_COMMITTER_NAME: name, GIT_COMMITTER_EMAIL: email, GIT_AUTHOR_DATE: '1700000000 +0000', GIT_COMMITTER_DATE: '1700000000 +0000' });
const g = (dir, args, env = {}) => execFileSync('git', ['-C', dir, ...args], { env: { ...ENV, ...ID(), ...env }, encoding: 'utf8' }).replace(/\n$/, '');
const P = (n) => `lean/PEqualNP/Outside/L_meta_${n}.lean`;

// A work repository with main, and a bare remote it pushes to.
function world() {
  const root = mkdtempSync(join(tmpdir(), 'lbp-'));
  const work = join(root, 'work'), remote = join(root, 'remote.git');
  mkdirSync(work);
  g(root, ['init', '-q', '--bare', '-b', 'main', remote]);
  g(root, ['--git-dir', remote, 'config', 'uploadpack.allowAnySHA1InWant', 'true']);  // as the service allows a fetch by hash
  g(work, ['init', '-q', '-b', 'main']);
  mkdirSync(join(work, 'lean/PEqualNP/Outside'), { recursive: true });
  writeFileSync(join(work, 'README'), 'base\n');
  writeFileSync(join(work, P(1)), 'theorem a : True := trivial\n');
  g(work, ['add', '-A']); g(work, ['commit', '-q', '-m', 'base']);
  g(work, ['remote', 'add', 'origin', remote]); g(work, ['push', '-q', 'origin', 'main']);
  return { root, work, remote, n: 100 };
}
// A pull request ref built by `make(work)` on a branch off main; returns an entry for the list.
function pr(w, make, { path, step = 'L-meta-9' } = {}) {
  const n = String(++w.n);
  g(w.work, ['checkout', '-q', '-B', `b${n}`, 'main']);
  const file = make(w.work, n);
  const head = g(w.work, ['rev-parse', 'HEAD']);
  const p = path ?? file;
  const blob = g(w.work, ['rev-parse', `HEAD:${p}`]);
  g(w.work, ['push', '-q', 'origin', `HEAD:refs/pull/${n}/head`]);
  g(w.work, ['checkout', '-q', 'main']);
  return { pr: n, head, step, path: p, blob, login: 'someone' };
}
const add = (msg = 'Prove a step', env = {}) => (work, n) => {
  writeFileSync(join(work, P(n)), `theorem t${n} : True := trivial\n`);
  g(work, ['add', P(n)]); g(work, ['commit', '-q', '-m', msg], env); return P(n);
};
function land(w, list, extra, opts = {}) {
  const lines = [];
  const dir = mkdtempSync(join(w.root, 'store-'));
  const parentsOf = (sha) => g(w.root, ['--git-dir', w.remote, 'rev-list', '--parents', '-n', '1', sha]).split(' ').slice(1);
  const res = run({ dir, remote: w.remote, listJson: JSON.stringify(list), extraNames: extra, parentsOf, log: (s) => lines.push(s), waitMs: () => 0, ...opts });
  return { res, dir, text: lines.join('\n'), main: g(w.root, ['--git-dir', w.remote, 'rev-parse', 'main']) };
}
const why = (res, n) => res.find((r) => r.pr === n)?.why ?? 'landed';

test('a good single-commit head lands, and main contains it with our merge message', () => {
  const w = world(); const e = pr(w, add());
  const { res, main } = land(w, [e]);
  assert.equal(why(res, e.pr), 'landed');
  assert.ok(g(w.root, ['--git-dir', w.remote, 'merge-base', '--is-ancestor', e.head, main]) === '');
  assert.equal(g(w.root, ['--git-dir', w.remote, 'log', '-1', '--format=%s|%an', main]), `Land L-meta-9 (#${e.pr}) by someone|pequalnp`);
});

test('three good heads land in one push, in the list order', () => {
  const w = world(); const a = pr(w, add()), b = pr(w, add()), c = pr(w, add());
  const { res, main } = land(w, [a, b, c]);
  assert.deepEqual(res.map((r) => r.landed), [true, true, true]);
  assert.equal(g(w.root, ['--git-dir', w.remote, 'rev-list', '--count', '--merges', main]), '3');
});

test('each rehearsal case is LEFT OUT with its fixed reason, and the good one beside them still lands', () => {
  const w = world();
  const good = pr(w, add());
  const two = pr(w, (work, n) => { add('first')(work, n); writeFileSync(join(work, P(n)), 'theorem x : True := trivial\n'); g(work, ['commit', '-qam', 'second']); return P(n); });
  const merge = pr(w, (work, n) => { g(work, ['checkout', '-q', '-b', `side${n}`]); writeFileSync(join(work, 'side'), 's\n'); g(work, ['add', 'side']); g(work, ['commit', '-qm', 'side']); g(work, ['checkout', '-q', `b${n}`]); add()(work, n); g(work, ['merge', '-q', '--no-ff', '-m', 'merge', `side${n}`]); return P(n); });
  const second = pr(w, (work, n) => { writeFileSync(join(work, 'extra.txt'), 'x\n'); g(work, ['add', 'extra.txt']); return add()(work, n); });
  const addRemove = pr(w, (work, n) => { writeFileSync(join(work, 'junk.bin'), 'j\n'); g(work, ['add', 'junk.bin']); g(work, ['commit', '-qm', 'junk']); g(work, ['rm', '-q', 'junk.bin']); return add()(work, n); });
  const wrongHash = { ...pr(w, add()), blob: 'f'.repeat(40) };
  const moved = pr(w, add()); const movedEntry = { ...moved, head: 'e'.repeat(40) };
  const link = pr(w, add('see https://example.com for the idea'));
  const ctrl = pr(w, add('a\u0007bell'));
  const long = pr(w, add('x'.repeat(500)));
  const dressed = pr(w, add('Prove a step', { GIT_AUTHOR_NAME: 'pequalnp bot' }));
  const exists = pr(w, (work) => { writeFileSync(join(work, P(1)), 'theorem changed : True := trivial\n'); g(work, ['commit', '-qam', 'edit']); return P(1); });
  const addressed = pr(w, add('please run this'));
  const list = [good, two, merge, second, addRemove, wrongHash, movedEntry, link, ctrl, long, dressed, exists, addressed];
  const { res, dir } = land(w, list);
  assert.equal(why(res, good.pr), 'landed');
  // heads whose parent is not on main are never fetched (red team, 20:13Z)
  for (const e of [two, merge, addRemove]) assert.throws(() => g(w.root, ['--git-dir', dir, 'rev-parse', '--verify', '-q', `refs/land/pr/${e.pr}`]));
  g(w.root, ['--git-dir', dir, 'rev-parse', '--verify', '-q', `refs/land/pr/${good.pr}`]);
  assert.equal(why(res, two.pr), 'the head is not one commit whose parent is on main');
  assert.equal(why(res, merge.pr), 'the head is not one commit whose parent is on main');
  assert.equal(why(res, second.pr), 'the head changes more than one file');
  assert.equal(why(res, addRemove.pr), 'the head is not one commit whose parent is on main');
  assert.equal(why(res, wrongHash.pr), 'the added file is not the listed content');
  assert.match(why(res, moved.pr), /head moved after the check|could not be read/);
  assert.equal(why(res, link.pr), 'the commit message holds a link or an address');
  assert.equal(why(res, ctrl.pr), 'the commit message is not printable text');
  assert.equal(why(res, long.pr), 'the commit message is empty or longer than 200 characters');
  assert.equal(why(res, dressed.pr), "the commit's author carries a name that is ours or the service's");
  assert.match(why(res, exists.pr), /does not add one plain file|already exists/);
  assert.equal(why(res, addressed.pr), 'the commit message addresses a reader');
});

test('a path that another entry of the same list already lands is left out', () => {
  const w = world(); const a = pr(w, add()); const b = { ...pr(w, add()), path: a.path, blob: a.blob };
  const { res } = land(w, [a, b]);
  assert.equal(why(res, a.pr), 'landed');
  assert.equal(why(res, b.pr), 'the list names this path or pull request twice');
});

test('a path that main gained after the pull request branched is left out, and the job goes on', () => {
  const w = world(); const e = pr(w, add()); const good = pr(w, add());
  writeFileSync(join(w.work, e.path), 'theorem other : True := trivial\n'); g(w.work, ['add', e.path]); g(w.work, ['commit', '-qm', 'same path by another route']); g(w.work, ['push', '-q', 'origin', 'main']);
  const { res } = land(w, [e, good]);
  assert.equal(why(res, e.pr), 'the path already exists on main');
  assert.equal(why(res, good.pr), 'landed');
});

test('a refusal of another kind (a hook): the line of each entry is printed, one attempt, nothing lands, the job faults at once', () => {
  const w = world(); const e = pr(w, add()); const bad = { ...pr(w, add()), blob: 'f'.repeat(40) };
  const before = g(w.root, ['--git-dir', w.remote, 'rev-parse', 'main']);
  writeFileSync(join(w.remote, 'hooks', 'pre-receive'), '#!/bin/sh\nexit 1\n', { mode: 0o755 });
  const lines = []; const dir = mkdtempSync(join(w.root, 'store-'));
  const parentsOf = (sha) => g(w.root, ['--git-dir', w.remote, 'rev-list', '--parents', '-n', '1', sha]).split(' ').slice(1);
  assert.throws(() => run({ dir, remote: w.remote, listJson: JSON.stringify([e, bad]), parentsOf, log: (s) => lines.push(s), waitMs: () => 0 }), /refused, not as a fast-forward/);
  const text = lines.join('\n');
  assert.match(text, new RegExp(`in the chain #${e.pr}\nleft out #${bad.pr}: the added file is not the listed content\nattempt 1: tip [0-9a-f]{10}: refused, another kind`));
  assert.equal((text.match(/^attempt \d+: tip /gm) || []).length, 1);   // one attempt (its kind line is data beside it)
  assert.doesNotMatch(text, /landed #/);
  assert.equal(g(w.root, ['--git-dir', w.remote, 'rev-parse', 'main']), before);
});

test('nothing landable: nothing is pushed, main unchanged', () => {
  const w = world(); const before = g(w.root, ['--git-dir', w.remote, 'rev-parse', 'main']);
  const e = { ...pr(w, add()), blob: 'f'.repeat(40) };
  const { main } = land(w, [e]);
  assert.equal(main, before);
});

// A second writer of main (the squash path), driven between our build and our push: main moves, our push is refused by
// git as not a fast-forward ("fetch first"), which is the one refusal that is retried.
const mover = (w, until, also = () => {}) => (attempt) => { if (attempt <= until) { also(attempt); g(w.work, ['checkout', '-q', 'main']); g(w.work, ['pull', '-q', '--ff-only', 'origin', 'main']); writeFileSync(join(w.work, 'README'), `moved ${attempt}\n`); g(w.work, ['commit', '-qam', `moved ${attempt}`]); g(w.work, ['push', '-q', 'origin', 'main']); } };

test('main moved three times under the push: three fast-forward refusals, then it lands; one line per attempt; landed once', () => {
  const w = world(); const e = pr(w, add());
  const { res, text, main } = land(w, [e], undefined, { beforePush: mover(w, 3) });
  assert.equal(why(res, e.pr), 'landed');
  assert.deepEqual(text.match(/^attempt \d+: tip [0-9a-f]{10}: .*$/gm).map((l) => l.replace(/tip [0-9a-f]{10}/, 'tip T')),
    ['attempt 1: tip T: refused, not a fast-forward', 'attempt 2: tip T: refused, not a fast-forward', 'attempt 3: tip T: refused, not a fast-forward', 'attempt 4: tip T: pushed']);
  assert.equal((text.match(/^landed #/gm) || []).length, 1);
  assert.ok(g(w.root, ['--git-dir', w.remote, 'merge-base', '--is-ancestor', e.head, main]) === '');
  assert.equal(g(w.root, ['--git-dir', w.remote, 'log', '-1', '--format=%s', main]), `Land L-meta-9 (#${e.pr}) by someone`);
});

test('main moving at every try: at most MAX_TRIES attempts, then a FAULT; nothing landed, nothing forced', () => {
  const w = world(); const e = pr(w, add()); let tips = [];
  assert.throws(() => land(w, [e], undefined, { beforePush: mover(w, 99, () => tips.push(g(w.root, ['--git-dir', w.remote, 'rev-parse', 'main']))) }), new RegExp(`not a fast-forward ${MAX_TRIES} times`));
  assert.equal(tips.length, MAX_TRIES);
  assert.throws(() => g(w.root, ['--git-dir', w.remote, 'merge-base', '--is-ancestor', e.head, 'main']));   // the head is not on main
});

test('the time bound stops the retries early', () => {
  const w = world(); const e = pr(w, add());
  assert.throws(() => land(w, [e], undefined, { beforePush: mover(w, 99), totalMs: 0 }), /not a fast-forward 1 times/);
});

test('a path that appears on main between tries is left out on the retry and goes back; the other head lands', () => {
  const w = world(); const e = pr(w, add()); const good = pr(w, add());
  const samePath = () => { g(w.work, ['checkout', '-q', 'main']); g(w.work, ['pull', '-q', '--ff-only', 'origin', 'main']); writeFileSync(join(w.work, e.path), 'theorem other : True := trivial\n'); g(w.work, ['add', e.path]); g(w.work, ['commit', '-qm', 'same path by the squash path']); g(w.work, ['push', '-q', 'origin', 'main']); };
  const { res, text, main } = land(w, [e, good], undefined, { beforePush: (a) => { if (a === 1) samePath(); } });
  assert.equal(why(res, e.pr), 'the path already exists on main');
  assert.equal(why(res, good.pr), 'landed');
  assert.match(text, /attempt 1: tip [0-9a-f]{10}: refused, not a fast-forward\n[\s\S]*left out #\d+: the path already exists on main[\s\S]*attempt 2: tip [0-9a-f]{10}: pushed/);
  assert.notEqual(g(w.root, ['--git-dir', w.remote, 'show', `${main}:${e.path}`]), 'theorem t' + e.pr + ' : True := trivial');
});

// A remote that refuses with a hook: once while main moves under it (another writer), or always with main still.
const hookOnce = (w) => writeFileSync(join(w.remote, 'hooks', 'pre-receive'), `#!/bin/sh\nf="${w.root}/once"\nif [ ! -e "$f" ]; then : > "$f"; unset $(env | sed -n 's/^\\(GIT_[A-Z_]*\\)=.*/\\1/p'); cd "${w.work}" && git checkout -q main && echo moved >> README && git commit -qam moved && git push -q "${w.remote}" main; exit 1; fi\nexit 0\n`, { mode: 0o755 });
const hookAlways = (w) => writeFileSync(join(w.remote, 'hooks', 'pre-receive'), '#!/bin/sh\nexit 1\n', { mode: 0o755 });

test('another kind of refusal: its kind is printed as filtered data, and it is a FAULT (the switch is off)', () => {
  assert.equal(RETRY_REMOTE_REJECTED_IF_MAIN_MOVED, false);
  const w = world(); const e = pr(w, add()); hookOnce(w);
  let text = ''; assert.throws(() => { try { land(w, [e]); } catch (x) { throw x; } }, /refused, not as a fast-forward/);
  const lines = []; const w2 = world(); const e2 = pr(w2, add()); hookOnce(w2);
  const dir = mkdtempSync(join(w2.root, 'store-')); const parentsOf = (sha) => g(w2.root, ['--git-dir', w2.remote, 'rev-list', '--parents', '-n', '1', sha]).split(' ').slice(1);
  assert.throws(() => run({ dir, remote: w2.remote, listJson: JSON.stringify([e2]), parentsOf, log: (s) => lines.push(s), waitMs: () => 0 }));
  text = lines.join('\n');
  assert.match(text, /attempt 1: tip [0-9a-f]{10}: refused, another kind\nattempt 1: the refusal's kind \(data, not acted on\): flag refused, summary \[remote rejected\] \(pre-receive hook declined\)/);
  assert.doesNotMatch(text, /landed #/);
});

test('the kind filter keeps only plain characters and at most 120 of them', () => {
  const k = pushKind('!\tx:refs/heads/main\t[remote rejected] (bad <b>`ref`</b> $(rm -rf) ' + 'x'.repeat(200) + ')');
  assert.ok(k.length <= 120 && /^[A-Za-z0-9 ()[\].,:-]*$/.test(k) && k.startsWith('flag refused, summary [remote rejected] (bad brefb (rm -rf) xxx'), k);
  assert.equal(pushKind('To x\nDone'), 'no status line for main');
  assert.equal(remoteRejected('!\tx:refs/heads/main\t[remote rejected] (cannot lock ref)'), true);
  assert.equal(remoteRejected('!\tx:refs/heads/main\t[rejected] (fetch first)'), false);
  assert.equal(remoteRejected('remote: [remote rejected] refs/heads/main'), false);
});

test('switch ON: a remote rejection while main moved is retried and lands; with main still it is a FAULT at once', () => {
  const w = world(); const e = pr(w, add()); hookOnce(w);
  const { res, text } = land(w, [e], undefined, { retryRemoteRejected: true });
  assert.equal(why(res, e.pr), 'landed');
  assert.match(text, /attempt 1: [\s\S]*\[remote rejected\][\s\S]*attempt 1: main moved since this attempt's tip[\s\S]*attempt 2: tip [0-9a-f]{10}: pushed/);
  const w2 = world(); const e2 = pr(w2, add()); hookAlways(w2);
  assert.throws(() => land(w2, [e2], undefined, { retryRemoteRejected: true }), /refused by the remote and main did not move/);
});

// A remote whose hook moves main and refuses on EVERY push: each refusal is a remote rejection while main moved.
const hookEvery = (w) => writeFileSync(join(w.remote, 'hooks', 'pre-receive'), `#!/bin/sh\nm="${w.root}/inhook"\nif [ -e "$m" ]; then exit 0; fi\n: > "$m"; unset $(env | sed -n 's/^\\(GIT_[A-Z_]*\\)=.*/\\1/p'); cd "${w.work}" && git checkout -q main && git pull -q --ff-only "${w.remote}" main 2>/dev/null; echo moved >> README && git commit -qam moved && git push -q "${w.remote}" main; rm -f "$m"; exit 1\n`, { mode: 0o755 });

test('switch ON: at most three retries of a remote rejection, then a FAULT; the kind line on EVERY such refusal', () => {
  assert.equal(MAX_REMOTE_RETRIES, 3);
  const w = world(); const e = pr(w, add()); hookEvery(w);
  const lines = []; const dir = mkdtempSync(join(w.root, 'store-')); const parentsOf = (sha) => g(w.root, ['--git-dir', w.remote, 'rev-list', '--parents', '-n', '1', sha]).split(' ').slice(1);
  assert.throws(() => run({ dir, remote: w.remote, listJson: JSON.stringify([e]), parentsOf, log: (s) => lines.push(s), waitMs: () => 0, retryRemoteRejected: true }), /refused by the remote 4 times while main moved/);
  const text = lines.join('\n');
  assert.equal((text.match(/^attempt \d+: tip [0-9a-f]{10}: refused, another kind$/gm) || []).length, 4);
  assert.equal((text.match(/^attempt \d+: the refusal's kind \(data, not acted on\): flag refused, summary \[remote rejected\]/gm) || []).length, 4);
  assert.doesNotMatch(text, /landed #/);
});

test('switch OFF: the kind line is printed on the one such refusal before the FAULT', () => {
  const w = world(); const e = pr(w, add()); hookEvery(w);
  const lines = []; const dir = mkdtempSync(join(w.root, 'store-')); const parentsOf = (sha) => g(w.root, ['--git-dir', w.remote, 'rev-list', '--parents', '-n', '1', sha]).split(' ').slice(1);
  assert.throws(() => run({ dir, remote: w.remote, listJson: JSON.stringify([e]), parentsOf, log: (s) => lines.push(s), waitMs: () => 0 }), /refused, not as a fast-forward/);
  assert.equal((lines.join('\n').match(/the refusal's kind \(data, not acted on\)/g) || []).length, 1);
});

test('the status is read from git porcelain only', () => {
  assert.equal(pushStatus('To x\n=\tabc:refs/heads/main\t[up to date]\nDone'), 'pushed');
  assert.equal(pushStatus('To x\n \tabc:refs/heads/main\t1111..2222\nDone'), 'pushed');
  assert.equal(pushStatus('To x\n!\tabc:refs/heads/main\t[rejected] (fetch first)\nDone'), 'fast-forward');
  assert.equal(pushStatus('To x\n!\tabc:refs/heads/main\t[rejected] (non-fast-forward)\nDone'), 'fast-forward');
  assert.equal(pushStatus('To x\n!\tabc:refs/heads/main\t[remote rejected] (pre-receive hook declined)\nDone'), 'other');
  assert.equal(pushStatus('remote: [rejected] (fetch first) refs/heads/main'), 'other');   // server text is never read as status
  assert.equal(pushStatus(''), 'other');
});

test('a signature block or an extra header is left out; names from the variable are ours too', () => {
  const names = reserved('Founder One');
  const base = 'tree ' + 'a'.repeat(40) + '\nparent ' + 'b'.repeat(40) + '\nauthor A <a@x.y> 1 +0000\ncommitter A <a@x.y> 1 +0000\n';
  assert.throws(() => checkCommitText(base.replace('\nauthor', '\ngpgsig -----BEGIN PGP SIGNATURE-----\nauthor') + '\nmsg\n', names), /signature block/);
  assert.throws(() => checkCommitText(base + 'encoding ISO-8859-1\n\nmsg\n', names), /header other than/);
  assert.throws(() => checkCommitText(base.replace(/A <a@x.y> 1 \+0000\ncommitter/, 'Founder One <f@x.y> 1 +0000\ncommitter') + '\nmsg\n', names), /ours or the service's/);
  checkCommitText(base + '\nProve L-meta-9 by induction on the gate count\n', names);
  assert.throws(() => checkCommitText(base + '\ntwo\nlines\n', names), /more than one line/);
  assert.ok(new LeftOut('x') instanceof Error);
});

test('the service private no-reply address lands; its bare no-reply address and its name are left out', () => {
  const w = world();
  const priv = pr(w, add('Prove a step', { GIT_AUTHOR_EMAIL: '1234567+someone@users.noreply.github.com', GIT_COMMITTER_EMAIL: '1234567+someone@users.noreply.github.com' }));
  const bare = pr(w, add('Prove a step', { GIT_COMMITTER_EMAIL: 'noreply@github.com' }));
  const named = pr(w, add('Prove a step', { GIT_COMMITTER_NAME: 'GitHub' }));
  const look = pr(w, add('Prove a step', { GIT_AUTHOR_EMAIL: 'pequalnp+1@users.noreply.github.com' }));
  const { res } = land(w, [priv, bare, named, look]);
  assert.equal(why(res, priv.pr), 'landed');
  assert.equal(why(res, bare.pr), "the commit's committer carries a name that is ours or the service's");
  assert.equal(why(res, named.pr), "the commit's committer carries a name that is ours or the service's");
  assert.equal(why(res, look.pr), "the commit's author carries a name that is ours or the service's");
});

test('a head that moved after the check (one new commit, same parent) is left out as moved', () => {
  const w = world(); const e = pr(w, add());
  g(w.work, ['checkout', '-q', `b${e.pr}`]); g(w.work, ['commit', '-q', '--amend', '-m', 'Prove a step again']);
  g(w.work, ['push', '-q', '-f', 'origin', `HEAD:refs/pull/${e.pr}/head`]); g(w.work, ['checkout', '-q', 'main']);
  const { res } = land(w, [e]);
  assert.equal(why(res, e.pr), 'the pull request head moved after the check');
  assert.throws(() => g(w.root, ['--git-dir', land(w, [e]).dir, 'rev-parse', '--verify', '-q', `refs/land/pr/${e.pr}`]));
});

test('the file transport is refused without the suite flag', () => {
  const w = world(); const e = pr(w, add());
  process.env.LAND_TEST_FILE_TRANSPORT = '0';
  try { assert.throws(() => land(w, [e])); } finally { process.env.LAND_TEST_FILE_TRANSPORT = '1'; }
});

test('the list itself: shape refused whole', () => {
  const ok = { pr: '5', head: 'a'.repeat(40), step: 'L-meta-9', path: P(5), blob: 'b'.repeat(40), login: 'someone' };
  parseList(JSON.stringify([ok]));
  assert.throws(() => parseList('[]'), /1 to/);
  assert.throws(() => parseList(JSON.stringify(Array(MAX_ENTRIES + 1).fill(ok))), /1 to/);
  assert.throws(() => parseList(JSON.stringify([{ ...ok, extra: 1 }])), /other fields/);
  assert.throws(() => parseList(JSON.stringify([{ ...ok, path: 'README' }])), /allowed outside file/);
  assert.throws(() => parseList(JSON.stringify([{ ...ok, head: 'A'.repeat(40) }])), /40-hex/);
  assert.throws(() => parseList(JSON.stringify([{ ...ok, login: 'x[bot]' }])), /plain account/);
  assert.throws(() => parseList(JSON.stringify([{ ...ok, step: 'L-meta-9; rm' }])), /step id/);
});

// RUN AS A SCRIPT, BY REAL PATH (2026-11-26): through a symlink the script runs (here it stops as a FAULT for want of
// its settings, which shows it ran), and a file of the same name that only imports it is a FAULT, never a silent 0.
{
  const { spawnSync } = await import('node:child_process');
  const { mkdtempSync, symlinkSync, writeFileSync, mkdirSync } = await import('node:fs');
  const { tmpdir } = await import('node:os'); const { join } = await import('node:path');
  const LBP = new URL('./land-by-push.mjs', import.meta.url).pathname;
  const env = { PATH: process.env.PATH, HOME: process.env.HOME };
  test('land-by-push: called through a symlink it runs (a FAULT without its settings, not a silent 0)', () => {
    const d = mkdtempSync(join(tmpdir(), 'lbp-link-')); symlinkSync(LBP, join(d, 'l.mjs'));
    const r = spawnSync(process.execPath, [join(d, 'l.mjs')], { encoding: 'utf8', env });
    assert.equal(r.status, 3, r.stdout + r.stderr); assert.match(r.stdout, /^FAULT: /); assert.doesNotMatch(r.stdout, /LAND OK/);
  });
  test('land-by-push: a file of its name that does not reach main is a FAULT, exit 3', () => {
    const d = mkdtempSync(join(tmpdir(), 'lbp-skip-')); mkdirSync(join(d, 'w'));
    writeFileSync(join(d, 'w', 'land-by-push.mjs'), `import ${JSON.stringify(LBP)};\n`);
    const r = spawnSync(process.execPath, [join(d, 'w', 'land-by-push.mjs')], { encoding: 'utf8', env });
    assert.equal(r.status, 3); assert.match(r.stdout, /^FAULT: land-by-push was started but did not run/);
  });
}
