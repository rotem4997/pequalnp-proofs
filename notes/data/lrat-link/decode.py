#!/usr/bin/env python3
"""Decode a cadical model of genmono.py into a circuit and evaluate it with the root semantics
(AND/OR over listed wires, missing wire reads false).  Usage: decode.py n s EDGES model.out"""
import sys
n, s = int(sys.argv[1]), int(sys.argv[2])
edges = [(int(e[0]), int(e[1])) for e in sys.argv[3].split(',')]
R = 1 << n; A = R + n + s + 1
val = set()
for line in open(sys.argv[4]):
    if line.startswith('v'):
        val |= {int(x) for x in line.split()[1:] if int(x) > 0}
def T(kd, j, a): return ((kd * (s + 1) + j) * A + a + 1) in val
gates = []
for j in range(s):
    op = [t for t in range(3) if T(0, j, t)]
    s1 = [k for k in range(n + j + 1) if T(1, j, k)]
    s2 = [k for k in range(n + j + 1) if T(2, j, k)]
    assert op and s1 and s2  # no at-most-one clauses: any chosen value is consistent; take the least
    gates.append(('AND', []) if op[0] == 2 else (['AND', 'OR'][op[0]], [s1[0], s2[0]]))
so = [k for k in range(n + s + 1) if T(6, 0, k)]; assert so
ok = True
for r in range(R):
    w = [(r >> i) & 1 == 1 for i in range(n)]
    for op, ins in gates:
        v = [w[i] if i < len(w) else False for i in ins]
        w.append(all(v) if op == 'AND' else any(v))
    out = w[so[0]] if so[0] < len(w) else False
    want = any((r >> u) & 1 and (r >> v) & 1 for u, v in edges)
    ok &= out == want
for j, gt in enumerate(gates): print(f'w{n+j} = {gt}')
print('out', so[0], 'correct on all rows:', ok)
