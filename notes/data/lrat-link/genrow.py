#!/usr/bin/env python3
"""ROW FILE generator for the Monotone2 link (adapted from notes/data/lrat-kernel/genlean.py).
The formula handed to the checker is `enc n s (rowFun n f) rows` itself (Link.lean); the CNF file
is only used to read the certificate's hints and must be genmono.py's output for the same
(n, s, edges, rows).  Usage:
  genrow.py f.cnf p.lrat out.lean NAMESPACE n s ROWS FEXPR [--seg HINTS] [--enc2]
--enc2: the formula is `enc2` (Link2.lean, with the lexicographic order; CNF from genmono.py
with 'rows,lex') and the final theorem goes through `lower_of_unsat2`.
ROWS: comma list; FEXPR: Lean Bool expression in `x : Fin n → Bool`.

Original doc: Write a Lean file that proves a DIMACS formula unsatisfiable from an LRAT certificate (text
form, RUP only) with PEqualNP.Library.LRAT.Checker and `decide +kernel`.

Usage: genlean.py f.cnf p.lrat out.lean NAME [--trim] [--seg HINTS] [--packF] [--chunk N]
  --trim     keep only the additions the empty clause depends on (deletions are always dropped)
  --seg H    cut the certificate into segments of about H hints, one theorem each (checkpoints:
             the live clauses at each cut are stated as a packed list)
  --packF    state the formula as decodeF of packed words (else a list literal)
  --chunk N  words per Lean definition (default 2000)
Literal encoding: DIMACS v -> 2v, -v -> 2v+1. Keys: clauses ranked by number of uses (most used
at key 0, the trie root); unused formula clauses are not loaded.
Prints: clauses, steps, hints, tokens, field width, segments.
"""
import sys
from collections import Counter

args = sys.argv[1:]
flags = {a for a in args if a.startswith('--')}


def opt(name, dflt):
    if name in args:
        i = args.index(name)
        v = args[i + 1]
        del args[i:i + 2]
        return int(v)
    return dflt


chunk = opt('--chunk', 2000)
CUBE = opt('--cube', -1)  # piece k of the cube split: F = enc2 ... ++ enc2Cube N S k (implies --enc2)
NOTG = '--not' in args  # NOT gates: LinkN2's enc2 (CNF from gennot.py), theorem for HasCircuitSize
assert not (NOTG and CUBE >= 0), '--not has no cube mode'
if CUBE >= 0 or NOTG:
    flags.add('--enc2')
seg = opt('--seg', 0)
pos = [a for a in args if not a.startswith('--')]
cnf, lrat, out, ns, N, S, ROWS, FEXPR = pos
name = 'c'
flags.add('--trim')


def lit(x):
    x = int(x)
    return 2 * x if x > 0 else 2 * (-x) + 1


clauses = []
with open(cnf, encoding='utf-8') as fh:
    for line in fh:
        t = line.split()
        if not t or t[0] in ('c', 'p'):
            continue
        assert t[-1] == '0'
        clauses.append([lit(x) for x in t[:-1]])
m = len(clauses)

steps = []  # (id, lits, hints)
with open(lrat, encoding='utf-8') as fh:
    for line in fh:
        t = line.split()
        if not t or t[1] == 'd':
            continue
        i = int(t[0])
        z = t.index('0', 1)
        hints = [int(h) for h in t[z + 1:-1]]
        assert all(h > 0 for h in hints), 'RAT hint: not supported'
        steps.append((i, [lit(x) for x in t[1:z]], hints))
        if z == 1:
            break
assert not steps[-1][1], 'no empty clause'

if '--trim' in flags:
    adds = {s[0]: s for s in steps}
    need = {steps[-1][0]}
    stack = [steps[-1][0]]
    while stack:
        for h in adds[stack.pop()][2]:
            if h > m and h not in need:
                need.add(h)
                stack.append(h)
    steps = [s for s in steps if s[0] in need]

# Unit literal after each hint (the checker cannot afford Nat.log2); cut at the first conflict.
neg = lambda l: l ^ 1
cl = {i + 1: c for i, c in enumerate(clauses)}
new = []
for i, lits, hints in steps:
    F = set(lits)
    hout = []
    ok = False
    for h in hints:
        U = set(cl[h]) - F
        if not U:
            hout.append(h)
            ok = True
            break
        assert len(U) == 1, f'hint {h} of step {i} leaves {len(U)} literals'
        u = next(iter(U))
        hout += [h, u]
        F.add(neg(u))
    assert ok, f'step {i}: no conflict'
    cl[i] = lits
    new.append((i, lits, hout))
steps = new

uses = Counter(h for _, _, hs in steps for h in hs[0::2])
if '--rank' in flags:  # keys by use rank
    key = {h: r for r, (h, _) in enumerate(uses.most_common())}
else:  # keys in creation order (used formula clauses first): insertions walk one edge of the trie
    key = {}
    for h in sorted(h for h in uses if h <= m):
        key[h] = len(key)
    for i, _, _ in steps:
        key[i] = len(key)
nxt = len(key)
for i, _, _ in steps:
    if i not in key:  # never used (the empty clause)
        key[i] = nxt
        nxt += 1
fk = [key[i + 1] + 1 if i + 1 in key else 0 for i in range(m)]


def steptoks(s):
    i, lits, hs = s
    return [key[i]] + lits + [0] + [key[x] if j % 2 == 0 else x for j, x in enumerate(hs)]


# segments
segs = [[]]
cnt = 0
for s in steps:
    segs[-1].append(s)
    cnt += (len(s[2]) + 1) // 2
    if seg and cnt >= seg:
        segs.append([])
        cnt = 0
if not segs[-1]:
    segs.pop()
last = {}
for j, s in enumerate(steps):
    for h in s[2][0::2]:
        last[h] = j
created = {s[0]: j for j, s in enumerate(steps)}
# live clauses at each cut: formula or created before the cut, last used at or after it
bounds = []
j0 = 0
for sg in segs[:-1]:
    j0 += len(sg)
    live = [h for h, lj in last.items() if lj >= j0 and (h <= m or created[h] < j0)]
    bounds.append(sorted(live, key=lambda h: key[h]))

alltoks = [t for s in steps for t in steptoks(s)]
ftoks = [x for c in clauses for x in c + [0]]
btoks = [[x for h in b for x in [key[h] + 1] + cl[h] + [0]] for b in bounds]
W = max([max(alltoks), max(ftoks), max(fk)] + [max(b) for b in btoks if b]).bit_length()
K = 1024 // W


def pack(ts):
    words = []
    for k in range(0, len(ts), K):
        w = 1
        for t in reversed(ts[k:k + K]):
            w = (w << W) | t
        words.append(w)
    return words


def L(xs):
    return '[' + ','.join(map(str, xs)) + ']'


def wordsdef(o, nm, ws):
    parts = []
    for k in range(0, len(ws), chunk):
        o.write(f'def {nm}_{k // chunk} : List Nat := [\n' + ',\n'.join(map(str, ws[k:k + chunk])) + ']\n\n')
        parts.append(f'{nm}_{k // chunk}')
    o.write(f'def {nm} : List Nat := ' + (' ++ '.join(parts) or '[]') + '\n\n')


rowsL = '[' + ROWS + ']'
E2 = '--enc2' in flags
ENC = 'enc2' if E2 else 'enc'
with open(out, 'w', encoding='utf-8', newline='\n') as o:  # UTF-8 and LF on every machine
    o.write('import PEqualNP.Library.LRAT.Cube\n\n' if CUBE >= 0 else
            'import PEqualNP.Library.LRAT.LinkN2\n\n' if NOTG else
            'import PEqualNP.Library.LRAT.Link2\n\n' if E2 else 'import PEqualNP.Library.LRAT.Link\n\n')
    o.write(f'/-!\n# Generated row file (genrow.py): no {"FanInTwo" if NOTG else "Monotone2"} circuit with {S} gates for one function\n\n'
            f'The formula handed to the checker is `{ENC} {N} {S} (rowFun {N} fn) rows` itself. Certificate:\n'
            f'CaDiCaL LRAT, trimmed; {len(steps)} steps, {sum((len(s[2]) + 1) // 2 for s in steps)} hints, '
            f'{len(segs)} segment(s).\n-/\n\n')
    o.write(f'namespace {ns}\nopen PEqualNP.Library.LRAT PEqualNP.Library.LRAT.{"LinkN" if NOTG else "Link"}\n\n')
    o.write('set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n')
    o.write(f'/-- The function. -/\ndef fn (x : Fin {N} → Bool) : Bool := {FEXPR}\n\n')
    o.write(f'/-- The rows. -/\ndef rows : List ℕ := {rowsL}\n\n')
    if CUBE >= 0:
        o.write(f'/-- The formula: piece {CUBE} of the cube split, `enc2 ++ enc2Cube` itself. -/\n'
                f'def F : List (List ℕ) := enc2 {N} {S} (rowFun {N} fn) rows ++ '
                f'PEqualNP.Defs.LratEncoding.enc2Cube {N} {S} {CUBE}\n\n')
    else:
        o.write(f'/-- The formula: `{ENC}` itself. -/\ndef F : List (List ℕ) := {ENC} {N} {S} (rowFun {N} fn) rows\n\n')
    wordsdef(o, f'{name}_Kw', pack(fk))
    o.write(f'noncomputable def {name}_K : List Nat := unpack {W} {name}_Kw\n\n')
    if len(segs) == 1:
        wordsdef(o, f'{name}_P', pack(alltoks))
        o.write(f'theorem unsat : ¬ FormulaSat F :=\n'
                f'  checkW_sound F {name}_K {W} {name}_P (by decide +kernel)\n\n')
    else:
        for b, bt in enumerate(btoks):
            wordsdef(o, f'{name}_B{b + 1}w', pack(bt))
            o.write(f'noncomputable def {name}_B{b + 1} : List (List Nat) := '
                    f'decodeF (unpack {W} {name}_B{b + 1}w)\n\n')
        n = len(segs)
        for k, sg in enumerate(segs):
            wordsdef(o, f'{name}_S{k}', pack([t for s in sg for t in steptoks(s)]))
            if k == 0:
                o.write(f'theorem seg0 : ∀ a, (∀ c ∈ F, ClauseSat a c) → EntriesSat a {name}_B1 :=\n'
                        f'  checkFirst_sound F {name}_K {W} {name}_S0 {name}_B1 (by decide +kernel)\n\n')
            elif k < n - 1:
                o.write(f'theorem seg{k} : ∀ a, EntriesSat a {name}_B{k} → EntriesSat a {name}_B{k + 1} :=\n'
                        f'  checkSeg_sound {name}_B{k} {W} {name}_S{k} {name}_B{k + 1} (by decide +kernel)\n\n')
            else:
                o.write(f'theorem seg{k} : ∀ a, EntriesSat a {name}_B{k} → False :=\n'
                        f'  checkLast_sound {name}_B{k} {W} {name}_S{k} (by decide +kernel)\n\n')
        expr = 'seg0 a ha'
        for k in range(1, n):
            expr = f'seg{k} a ({expr})'
        o.write(f'theorem unsat : ¬ FormulaSat F := fun ⟨a, ha⟩ =>\n  {expr}\n\n')
    if CUBE >= 0:
        R = 'PEqualNP.Defs.LratEncoding'
        o.write(f'/-- Piece {CUBE} of the cube split of the formula saying that a circuit of AND and OR gates\n'
                f'of fan-in two with {S} gate slots computes the function on the rows is unsatisfiable. -/\n'
                f'theorem piece : ¬ {R}.FormulaSat ({R}.enc2 {N} {S} ({R}.rowFun {N} fun x => {FEXPR})\n'
                f'    {rowsL} ++ {R}.enc2Cube {N} {S} {CUBE}) :=\n  unsat\n\n')
    elif NOTG:
        o.write(f'/-- Every circuit of AND, OR and NOT gates of fan-in at most two computing the function on {N}\n'
                f'inputs has at least {int(S) + 1} gates. -/\n'
                f'theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize {N} (fun x : Fin {N} → Bool => {FEXPR}) t →\n'
                f'    {int(S) + 1} ≤ t :=\n  size_of_unsat2 {N} {S} fn rows (by decide) unsat\n\n')
    else:
        o.write(f'/-- Every circuit of AND and OR gates of fan-in at most two computing the function on {N}\n'
                f'inputs has at least {int(S) + 1} gates. -/\n'
                f'theorem lower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →\n'
                f'    (∀ x : Fin {N} → Bool, C.eval (List.ofFn x) = ({FEXPR})) → {int(S) + 1} ≤ C.size :=\n'
                f'  {"lower_of_unsat2" if E2 else "lower_of_unsat"} {N} {S} fn rows (by decide) unsat\n\n')
    o.write(f'end {ns}\n')

print(f'clauses={m} steps={len(steps)} hints={sum((len(s[2]) + 1) // 2 for s in steps)} W={W} segments={len(segs)} live_at_cuts={[len(b) for b in bounds]}')
