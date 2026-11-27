// LAND BY PUSH (red team ruling, 2026-11-24 19:56 UTC: YES with conditions, on a runner, one-commit heads only).
// GitHub marks a pull request merged by itself when main comes to contain its head commit, so one push of a chain
// of merge commits lands many accepted proofs with no write call per pull request. This script runs ONLY in
// .github/workflows/land-by-push.yml, on a runner, never on a machine of ours.
//
// Plumbing only: the named commits are fetched into a bare store with object checking on, hooks off, no
// checkout, no build, no submodules, no filters. Nothing fetched is run or opened as a program.
//
// A head is landed only if ALL hold, checked here (a head that fails is LEFT OUT with a fixed reason, and the
// intake lands it by today's squash path; it is never a refusal of the proof):
//  (a) the pull request's head, read now, is the commit the checker accepted;
//  (b) the head is ONE commit whose single parent is an ancestor of main: nothing else rides into history;
//  (c) its tree against its parent is exactly one added plain file, at the listed path, with the listed blob;
//      the merge commit's tree against main is that same one file and nothing else;
//  (d) the commit's own text: no header but tree, parent, author, committer (no signature block); the message
//      one line, at most 200 characters, printable ASCII, no link, none of the reader's addressing words;
//      author and committer names and addresses printable ASCII, at most 100 characters, none of ours.
// The merge commits carry OUR fixed message and the project identity. Before the push the new tip's tree against
// the old tip is exactly the landed files; the push never forces; a rejected push is rebuilt once on the new tip.
import { execFileSync } from 'node:child_process';
import { realpathSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { FILE_RE, MAX_BYTES } from './outside-guard.mjs';

export const MAX_ENTRIES = 50;
const SHA_RE = /^[0-9a-f]{40}$/;
const PR_RE = /^[1-9][0-9]{0,6}$/;
const STEP_RE = /^[LR]-[a-z0-9]+(-[a-z0-9]+)*$/;
const LOGIN_RE = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/;
// The reader's link and addressing tripwires, applied to the commit message (tools/outside-read.py, 2026-11-24).
const LINK_RE = /:\/\/|\bwww\.|\bhttps?\b|[A-Za-z0-9._%+-]+@[A-Za-z0-9-]+\.[a-z]{2,}|\b[a-z0-9-]+\.(com|org|net|io|dev|ai|sh|xyz|me|gg|ly)\b|\b\d{1,3}(\.\d{1,3}){3}\b/i;
const ADDRESS_RE = /\b(you|your|yours|please|instruction|instructions|prompt|assistant|agent|agents|llm|reviewer|maintainer|curl|wget|download|install|execute|password|credential|credentials|secret|token|click|visit|contact|email|sudo|bash|pip|npm|ssh|chatgpt|gpt|claude)\b/i;
// Names that are ours or the service's: a commit dressed as us in main's history is left out. More names (the
// founders') come from the repository variable LAND_RESERVED_NAMES, comma-separated, never from the list.
const RESERVED = ['pequalnp', 'open-goat', 'anthropic', 'claude', 'github', 'noreply@github.com', '[bot]', 'dependabot', 'actions'];
const PRINTABLE = /^[\x20-\x7e]*$/;

export class LeftOut extends Error {}
const out = (why) => { throw new LeftOut(why); };

// One entry of the intake's list, shape only. Throws a plain Error (the whole list is refused) on a bad shape.
export function checkEntry(e) {
  if (!e || typeof e !== 'object') throw new Error('an entry is not an object');
  const keys = Object.keys(e).sort().join(',');
  if (keys !== 'blob,head,login,path,pr,step') throw new Error('an entry has other fields than pr, head, step, path, blob, login');
  if (!PR_RE.test(String(e.pr))) throw new Error('an entry has no plain pull request number');
  if (!SHA_RE.test(e.head) || !SHA_RE.test(e.blob)) throw new Error('an entry has no plain 40-hex head or blob');
  if (!STEP_RE.test(e.step)) throw new Error('an entry has no plain step id');
  if (typeof e.path !== 'string' || !FILE_RE.test(e.path)) throw new Error('an entry path is not an allowed outside file');
  if (!LOGIN_RE.test(e.login)) throw new Error('an entry login is not a plain account name');
  return { pr: String(e.pr), head: e.head, step: e.step, path: e.path, blob: e.blob, login: e.login };
}

export function parseList(json) {
  const v = JSON.parse(json);
  if (!Array.isArray(v) || v.length === 0 || v.length > MAX_ENTRIES) throw new Error(`the list must hold 1 to ${MAX_ENTRIES} entries`);
  return v.map(checkEntry);
}

export function reserved(extra) {
  return RESERVED.concat(String(extra || '').split(',').map((s) => s.trim().toLowerCase()).filter((s) => s.length >= 3));
}

// (d) the raw commit object, as git stores it.
export function checkCommitText(raw, names) {
  const cut = raw.indexOf('\n\n');
  if (cut < 0) out('the commit has no message');
  const head = raw.slice(0, cut).split('\n');
  let msg = raw.slice(cut + 2);
  const kinds = head.map((l) => l.split(' ')[0]);
  for (const k of kinds) if (!['tree', 'parent', 'author', 'committer'].includes(k)) out(k === 'gpgsig' || k === 'gpgsig-sha256' ? 'the commit carries a signature block' : 'the commit carries a header other than tree, parent, author, committer');
  if (kinds.filter((k) => k === 'parent').length !== 1) out('the head is not one commit with one parent');
  for (const who of ['author', 'committer']) {
    const line = head.find((l) => l.startsWith(who + ' '));
    const m = line && /^(author|committer) (.*) <(.*)> [0-9]+ [+-][0-9]{4}$/.exec(line);
    if (!m) out(`the commit's ${who} line is not of the plain shape`);
    // The service's standard private address (digits plus login at its users no-reply domain) is how most
    // contributors' commits are addressed: that exact suffix is removed before the reserved test (red team, 20:13Z).
    // The service's bare no-reply address and every name test stay.
    const addr = m[3].length <= 100 && /^[0-9]+\+[A-Za-z0-9-]{1,39}@users\.noreply\.github\.com$/.test(m[3]) ? m[3].replace(/@users\.noreply\.github\.com$/, '') : m[3];
    if (m[3].length > 100 || !PRINTABLE.test(m[3])) out(`the commit's ${who} is not printable text of at most 100 characters`);
    for (const part of [m[2], addr]) {
      if (part.length > 100 || !PRINTABLE.test(part)) out(`the commit's ${who} is not printable text of at most 100 characters`);
      const low = part.toLowerCase();
      if (names.some((n) => low.includes(n))) out(`the commit's ${who} carries a name that is ours or the service's`);
    }
  }
  if (msg.endsWith('\n')) msg = msg.slice(0, -1);
  if (msg.includes('\n')) out('the commit message is more than one line');
  if (msg.length === 0 || msg.length > 200) out('the commit message is empty or longer than 200 characters');
  if (!PRINTABLE.test(msg)) out('the commit message is not printable text');
  if (LINK_RE.test(msg)) out('the commit message holds a link or an address');
  if (ADDRESS_RE.test(msg)) out('the commit message addresses a reader');
}

// git in the bare store: fixed configuration, no hooks, no system or global configuration, object checking on.
export function gitIn(dir, auth) {
  const env = { PATH: '/usr/bin:/bin', HOME: dir, GIT_CONFIG_NOSYSTEM: '1', GIT_CONFIG_GLOBAL: '/dev/null', GIT_TERMINAL_PROMPT: '0', LC_ALL: 'C' };
  // The token reaches git as an environment-only header, never on a command line, in a remote URL or in a file.
  if (auth) Object.assign(env, { GIT_CONFIG_COUNT: '1', GIT_CONFIG_KEY_0: 'http.https://github.com/.extraheader', GIT_CONFIG_VALUE_0: `AUTHORIZATION: basic ${Buffer.from(`x-access-token:${auth}`).toString('base64')}` });
  const base = ['-c', 'core.hooksPath=/dev/null', '-c', 'fetch.fsckObjects=true', '-c', 'transfer.fsckObjects=true', '-c', 'protocol.allow=never', '-c', 'protocol.https.allow=always', '-c', `protocol.file.allow=${process.env.LAND_TEST_FILE_TRANSPORT === '1' ? 'always' : 'never'}`, '-C', dir];
  const git = (args, opts = {}) => execFileSync('git', base.concat(args), { env: { ...env, ...(opts.env || {}) }, encoding: 'utf8', maxBuffer: 8 << 20, stdio: ['ignore', 'pipe', 'pipe'], timeout: opts.timeout ?? 120000 }).replace(/\n$/, '');
  git.ok = (args, opts) => { try { git(args, opts); return true; } catch { return false; } };
  // A call whose output is read whether or not it succeeds (git push --porcelain prints its status lines on a refusal too).
  git.out = (args, opts = {}) => { try { return { ok: true, out: git(args, opts) }; } catch (e) { return { ok: false, out: String(e.stdout ?? '') }; } };
  return git;
}

// (a), (b), (c) and (d) for one fetched head, against the tip it would be merged onto. Returns the merge tree.
export function checkHead(git, e, fetched, tip, names) {
  if (fetched === 'not one commit on main') out("the head is not one commit whose parent is on main");
  if (fetched === 'too large or too slow') out('the head was too large or too slow to fetch');
  if (fetched === 'too many objects') out('the head brings more objects than one commit and one file');
  if (fetched === 'unreadable') out('the head could not be read');
  if (fetched !== e.head) out('the pull request head moved after the check');
  checkCommitText(git(['cat-file', 'commit', e.head]), names);
  const parent = git(['rev-parse', `${e.head}^1`]);
  if (!git.ok(['merge-base', '--is-ancestor', parent, tip])) out("the head's parent is not on main");
  const diff = git(['diff-tree', '-r', '--no-renames', '--no-commit-id', '--raw', '--full-index', parent, e.head]).split('\n').filter(Boolean);
  if (diff.length !== 1) out('the head changes more than one file');
  const m = /^:000000 100644 0{40} ([0-9a-f]{40}) A\t(.+)$/.exec(diff[0]);
  if (!m) out('the head does not add one plain file');
  if (m[2] !== e.path) out('the added file is not the listed path');
  if (m[1] !== e.blob) out('the added file is not the listed content');
  if (Number(git(['cat-file', '-s', e.blob])) > MAX_BYTES) out('the added file is larger than the limit');
  if (git.ok(['cat-file', '-e', `${tip}:${e.path}`])) out('the path already exists on main');
  let tree;
  try { tree = git(['merge-tree', '--write-tree', '--no-messages', tip, e.head]).split('\n')[0]; }
  catch { out('the merge with main does not go through cleanly'); }
  if (!SHA_RE.test(tree)) out('the merge did not give one tree');
  const md = git(['diff-tree', '-r', '--no-renames', '--raw', '--full-index', `${tip}^{tree}`, tree]).split('\n').filter(Boolean);
  if (md.length !== 1 || md[0] !== `:000000 100644 ${'0'.repeat(40)} ${e.blob} A\t${e.path}`) out('the merge with main is not that one file');
  return tree;
}

const IDENT = { GIT_AUTHOR_NAME: 'pequalnp', GIT_AUTHOR_EMAIL: 'noreply@pequalnp.com', GIT_COMMITTER_NAME: 'pequalnp', GIT_COMMITTER_EMAIL: 'noreply@pequalnp.com' };

// The chain of merge commits on `tip`, in the list's order. Returns { tip, results }.
export function buildChain(git, list, heads, tip0, names) {
  let tip = tip0;
  const results = [];
  const landed = [];
  for (const e of list) {
    try {
      if (landed.some((x) => x.path === e.path || x.pr === e.pr)) out('the list names this path or pull request twice');
      const tree = checkHead(git, e, heads[e.pr], tip, names);
      tip = git(['commit-tree', tree, '-p', tip, '-p', e.head, '-m', `Land ${e.step} (#${e.pr}) by ${e.login}`], { env: IDENT });
      landed.push(e);
      results.push({ pr: e.pr, landed: true });
    } catch (err) {
      if (!(err instanceof LeftOut)) throw err;
      results.push({ pr: e.pr, landed: false, why: err.message });
    }
  }
  // Before any push: the new tip's tree against the old tip is exactly the landed files, each as listed.
  const want = landed.map((e) => `:000000 100644 ${'0'.repeat(40)} ${e.blob} A\t${e.path}`).sort();
  const got = landed.length ? git(['diff-tree', '-r', '--no-renames', '--raw', '--full-index', `${tip0}^{tree}`, `${tip}^{tree}`]).split('\n').filter(Boolean).sort() : [];
  if (JSON.stringify(want) !== JSON.stringify(got)) throw new Error('the new main differs from the old by more than the landed files: nothing is pushed');
  return { tip, results };
}

// Before the push a head is only 'in the chain'; 'landed' is said only after the push went through (red team, 20:46Z).
export function report(results, pushed = false) {
  return results.map((r) => (r.landed ? `${pushed ? 'landed' : 'in the chain'} #${r.pr}` : `left out #${r.pr}: ${r.why}`)).join('\n');
}

// The job: fetch, build, push (never forced), rebuild once on a moved main.
export function apiParents(repo, auth) {
  // The head's parents, read through the API with the job's own token (a read; no write).
  if (!SHA_RE.test('0'.repeat(40)) || !/^[A-Za-z0-9-]+\/[A-Za-z0-9._-]+$/.test(String(repo))) throw new Error('no plain repository name');
  return (sha) => {
    if (!SHA_RE.test(sha)) throw new Error('no plain sha');
    // The token goes to curl on its standard input (-H @-), never on its command line.
    const outp = execFileSync('curl', ['-sS', '--fail', '--max-time', '20', '-H', 'Accept: application/vnd.github+json', '-H', '@-', `https://api.github.com/repos/${repo}/commits/${sha}`], { input: `Authorization: Bearer ${auth}\n`, encoding: 'utf8', env: { PATH: '/usr/bin:/bin' }, maxBuffer: 4 << 20 });
    return JSON.parse(outp).parents.map((p) => p.sha);
  };
}

// THE PUSH, RETRIED ON A FAST-FORWARD REFUSAL ONLY (red team, both seats, 25 Nov): main moves every few seconds while the
// squash path merges, so a chain built on one tip is often refused as not a fast-forward. The refusal is read from git's
// own machine status (`git push --porcelain`: flag "!", "[rejected]" with "fetch first" or "non-fast-forward"), never from
// a server's text; any other refusal is a FAULT at once. Each retry fetches main fresh, reads every head again and reruns
// EVERY check from the start against the new tip, so a head whose path a squash landing put on main meanwhile is LEFT OUT
// (back to the squash path), never pushed over. At most MAX_TRIES tries, a short random wait between, a total time bound
// well inside the job's twenty minutes; never a force. One line per attempt; "landed" only after the push that went through.
export const MAX_TRIES = 10, TOTAL_MS = 5 * 60 * 1000;
export function pushStatus(out) {
  // 'pushed' | 'fast-forward' | 'other', from the porcelain status line of refs/heads/main.
  const line = String(out || '').split('\n').find((l) => l.split('\t')[1]?.endsWith(':refs/heads/main'));
  if (!line) return 'other';
  const [flag, , summary = ''] = line.split('\t');
  if ([' ', '+', '*', '='].includes(flag)) return 'pushed';
  if (flag === '!' && /^\[rejected\] \((fetch first|non-fast-forward)\)$/.test(summary.trim())) return 'fast-forward';
  return 'other';
}
// THE KIND OF ANOTHER REFUSAL, AS DATA (operator, 25 Nov, after run 45708355672): the porcelain flag and summary of the
// line for refs/heads/main, through a strict filter (letters, digits, space and ( ) [ ] . , : -, at most 120 characters).
// It is printed so the kind can be seen; nothing in this file decides anything from it.
export function pushKind(out) {
  const line = String(out || '').split('\n').find((l) => l.split('\t')[1]?.endsWith(':refs/heads/main'));
  if (!line) return 'no status line for main';
  const [flag, , summary = ''] = line.split('\t');
  // git's one-character flag is named (the filter keeps no "!"); the summary passes the filter.
  const name = { ' ': 'ok', '+': 'forced', '*': 'new', '=': 'up to date', '-': 'deleted', '!': 'refused' }[flag] ?? 'unknown';
  return `flag ${name}, summary ${summary}`.replace(/[^A-Za-z0-9 ()[\].,:-]/g, '').slice(0, 120);
}
// A REMOTE REJECTION RETRIED ONLY IF MAIN MOVED, PREPARED AND OFF (operator, 25 Nov; for the red team): git's own status
// word "[remote rejected]" (flag "!"; the reason in brackets after it is the server's and is never read), and then OUR
// fact, read from git: after a fresh fetch, main's tip is not the tip this attempt was built on. Main did not move: a
// FAULT at once. OFF until the red team rules on the kind.
export const RETRY_REMOTE_REJECTED_IF_MAIN_MOVED = false, MAX_REMOTE_RETRIES = 3;   // the red team's term (2): at most three in a run
export function remoteRejected(out) {
  const line = String(out || '').split('\n').find((l) => l.split('\t')[1]?.endsWith(':refs/heads/main'));
  if (!line) return false;
  const [flag, , summary = ''] = line.split('\t');
  return flag === '!' && summary.trim().startsWith('[remote rejected]');
}
const pause = (ms) => Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);
export function run({ dir, remote, listJson, extraNames, auth, parentsOf, log = console.log, beforePush = () => {}, maxTries = MAX_TRIES, totalMs = TOTAL_MS, waitMs = () => 500 + Math.floor(Math.random() * 2500), retryRemoteRejected = RETRY_REMOTE_REJECTED_IF_MAIN_MOVED }) {
  const list = parseList(listJson);
  const names = reserved(extraNames);
  const git = gitIn(dir, auth);
  git(['init', '-q', '--bare', '.']);
  git(['remote', 'add', 'origin', remote]);
  const fetchMain = () => { git(['fetch', '-q', '--no-tags', '--no-recurse-submodules', 'origin', '+refs/heads/main:refs/land/main']); return git(['rev-parse', 'refs/land/main']); };
  let tip0 = fetchMain();
  const began = Date.now(); let remoteRetries = 0;
  // A head is fetched only after its parent, read through the API, is shown to be on main: such a head brings one
  // commit, its trees and one file. A fetch that fails or takes over 30 seconds leaves that entry out (red team, 20:13Z).
  const readHeads = () => {
  const heads = {};
  for (const e of list) {
    let parents;
    try { parents = parentsOf(e.head); } catch { parents = null; }
    if (!Array.isArray(parents)) { heads[e.pr] = 'unreadable'; continue; }
    if (parents.length !== 1 || !SHA_RE.test(parents[0]) || !git.ok(['merge-base', '--is-ancestor', parents[0], tip0])) { heads[e.pr] = 'not one commit on main'; continue; }
    // The pull request's CURRENT head is read without fetching anything (ls-remote); only the LISTED commit, whose
    // parents were just read, is fetched, by its hash (red team note, 20:22Z): a head that moved is never fetched.
    let current = '';
    try { current = (git(['ls-remote', 'origin', `refs/pull/${e.pr}/head`], { timeout: 30000 }).split('\t')[0] || '').trim(); } catch { current = ''; }
    if (!SHA_RE.test(current)) { heads[e.pr] = 'unreadable'; continue; }
    if (current !== e.head) { heads[e.pr] = current; continue; }
    if (git.ok(['fetch', '-q', '--no-tags', '--no-recurse-submodules', 'origin', `+${e.head}:refs/land/pr/${e.pr}`], { timeout: 30000 })) heads[e.pr] = git(['rev-parse', `refs/land/pr/${e.pr}`]);
    else { heads[e.pr] = 'too large or too slow'; continue; }
    if (heads[e.pr] === e.head && git.ok(['rev-parse', `${e.head}^1`])) {
      const n = git(['rev-list', '--objects', `${e.head}^1..${e.head}`]).split('\n').filter(Boolean).length;
      if (n > 16) heads[e.pr] = 'too many objects';
    }
  }
  return heads;
  };
  for (let attempt = 1; ; attempt++) {
    if (attempt > 1) tip0 = fetchMain();   // a fresh main, then every head and every check again, from the start
    const heads = readHeads();
    const { tip, results } = buildChain(git, list, heads, tip0, names);
    // Each entry's line is printed BEFORE the push, so a refused push still shows what was judged (rehearsal 1).
    log(report(results));
    if (!results.some((r) => r.landed)) { log(`attempt ${attempt}: tip ${tip0.slice(0, 10)}: nothing in the chain`); log('nothing to land: no push'); return results; }
    beforePush(attempt);
    const { out } = git.out(['push', '--porcelain', 'origin', `${tip}:refs/heads/main`]);
    const st = pushStatus(out);
    log(`attempt ${attempt}: tip ${tip0.slice(0, 10)}: ${st === 'pushed' ? 'pushed' : st === 'fast-forward' ? 'refused, not a fast-forward' : 'refused, another kind'}`);
    if (st === 'pushed') { log('pushed: these heads are on main'); log(results.filter((r) => r.landed).map((r) => `landed #${r.pr}`).join('\n')); return results; }
    if (st === 'other') log(`attempt ${attempt}: the refusal's kind (data, not acted on): ${pushKind(out)}`);
    if (st === 'other' && retryRemoteRejected && remoteRejected(out)) {
      const now = fetchMain();
      log(`attempt ${attempt}: main ${now === tip0 ? 'did not move' : 'moved'} since this attempt's tip`);
      if (now === tip0) throw new Error('the push was refused by the remote and main did not move: nothing landed, nothing forced');
      if (++remoteRetries > MAX_REMOTE_RETRIES) throw new Error(`the push was refused by the remote ${remoteRetries} times while main moved: nothing landed, nothing forced`);
    } else if (st !== 'fast-forward') throw new Error('the push was refused, not as a fast-forward: nothing landed, nothing forced');
    if (attempt >= maxTries || Date.now() - began >= totalMs) throw new Error(`the push was refused as not a fast-forward${retryRemoteRejected ? ' or by the remote while main moved' : ''} ${attempt} times: nothing landed, nothing forced`);
    pause(waitMs());
  }
}

// Run as a script, by REAL path (2026-11-26): the text comparison skipped run() silently when called through a
// symlinked path; now both sides are resolved, and a call naming this file that still is not main is a FAULT.
const ranAsScript = (url, argv1) => { if (!argv1) return false; try { return realpathSync(fileURLToPath(url)) === realpathSync(argv1); } catch { return false; } };
if (!ranAsScript(import.meta.url, process.argv[1]) && /(^|[\/\\])land-by-push\.mjs$/.test(process.argv[1] ?? '')) {
  console.log('FAULT: land-by-push was started but did not run (its own path and the called path differ); nothing landed');
  process.exit(3);
}
if (ranAsScript(import.meta.url, process.argv[1])) {
  try {
    run({ dir: process.env.LAND_DIR, remote: process.env.LAND_REMOTE, listJson: process.env.LAND_LIST, extraNames: process.env.LAND_RESERVED_NAMES, auth: process.env.LAND_TOKEN, parentsOf: apiParents(process.env.GITHUB_REPOSITORY, process.env.LAND_TOKEN) });
    console.log('LAND OK');   // the fixed last line the workflow requires (2026-11-26): silence is never a pass
  } catch (err) {
    console.log(`FAULT: ${String(err.message).replace(/[^A-Za-z0-9 .,:;'()#_-]/g, '?').slice(0, 300)}`);
    process.exit(3);
  }
}
