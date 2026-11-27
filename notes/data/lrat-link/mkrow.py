#!/usr/bin/env python3
"""One command: (graph, s) -> a ready row file proving `s + 1 <= C.size` for every Monotone2
circuit computing the graph's edge function, via Link.lower_of_unsat.
Usage: mkrow.py n s EDGES out.lean NAMESPACE [--seg H] [--seed K] [--work DIR]
EDGES like 01,12,23 (vertices are single digits).  Runs genmono.py (rows = minimal true and
maximal false inputs), CaDiCaL (--unsat, LRAT), genrow.py.  The solver run is one process; a
run expected over a minute needs a solver slot first (box rules)."""
import os, subprocess, sys
a = sys.argv[1:]
def opt(nm, d):
    if nm in a:
        i = a.index(nm); v = a[i + 1]; del a[i:i + 2]; return v
    return d
seg = opt('--seg', '60000'); seed = opt('--seed', '2'); work = opt('--work', '.cache/lrat-link')
n, s, edges, out, ns = a
here = os.path.dirname(os.path.abspath(__file__))
os.makedirs(work, exist_ok=True)
cnf = os.path.join(work, f'row_{n}_{s}.cnf'); lrat = os.path.join(work, f'row_{n}_{s}.lrat')
r = subprocess.run([sys.executable, os.path.join(here, 'genmono.py'), n, s, edges, cnf, 'rows'],
                   capture_output=True, text=True, check=True)
rows = r.stderr.split('rows [')[1].split(']')[0].replace(' ', '')
res = subprocess.run(['cadical', '-q', '--unsat', f'--seed={seed}', '--lrat', '--no-binary', cnf, lrat],
                     capture_output=True, text=True)
if res.returncode != 20:
    sys.exit(f'not UNSAT (cadical exit {res.returncode}): no row')
fx = ' || '.join(f'(x {e[0]} && x {e[1]})' for e in edges.split(','))
subprocess.run([sys.executable, os.path.join(here, 'genrow.py'), cnf, lrat, out, ns, n, s, rows, fx,
                '--seg', seg], check=True)
