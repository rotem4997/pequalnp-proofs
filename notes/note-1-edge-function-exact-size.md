# Note 1: exact circuit size of the edge function on graphs with long threads

pequalnp.com, 2026-11-23. A question for readers, not a claim.

**This note asks a question: is this known?** The statements below are checked by a machine
checker (Lean 4 with Mathlib); no claim is made about whether they are known. Nothing is claimed
about print beyond the searches listed in section 5.

## 1. Statement (checked by the project's checker, on its Lean definitions)

For a graph G, let f_G(x) = OR over edges uv of (x_u AND x_v), with one input per vertex.
Circuits: fan-in two, AND, OR and NOT gates, every gate counted (NOT included), inputs free.
tau(G) is the vertex cover number.

(a) Lower bound on long-thread graphs (L-meta-204). Suppose G has an edge or A is nonempty, every
cycle of G has length at least 7, and any two distinct vertices of degree at least 3 are joined only by walks of length at
least 7. Then every circuit for f_G OR (OR of x_a, a in A), with A a set of isolated vertices,
has at least |A| + |E| + tau(G) - 1 gates.
(b) Forests with at least one edge (L-meta-104): every circuit for f_G has at least
|E| + tau(G) - 1 gates.
(c) Exact values: path on n >= 2 vertices, n + floor(n/2) - 2 (L-meta-102); cycle on n >= 5 vertices,
n + ceil(n/2) - 1 (L-meta-106).
(d) Upper bound, every graph with an edge: |E| + |T| - 1 gates from any vertex cover T, namely
OR over t in T of (x_t AND OR of the neighbours assigned to t) (L-meta-105, size). That such a
circuit uses no NOT gate is the separate row L-meta-154.
(e) Related checked rows: monotone circuits for girth >= 9 with hubs >= 7 apart (L-meta-115), and
"NOT gates never save a gate" on girth >= 9 with hubs >= 9 apart (L-meta-113).

So, for f_G alone (A empty), on these classes the least circuit size is exactly
|E| + tau(G) - 1, NOT gates included: the lower bound is (a) or (b), the upper bound is (d), and
it is attained by a monotone circuit (L-meta-154). With A nonempty, only the lower bound in (a) is
a row. Since |E| <= 3n/2 under the hub condition,
these are LINEAR bounds.

## 2. Context

This came up as a step toward a reduction for a circuit-minimization promise problem: given a
circuit at most one gate above minimum, decide whether it is minimum. Exactness is what that
step needs. The bound is linear and does not bear on superlinear circuit lower bounds.

## 3. Proof idea (as formalized)

Induction on the graph, by gate elimination.
- Every graph in the class with an edge has a "good leaf" (a leaf whose neighbour has at most
  one further neighbour, or two leaves at one vertex) or a "run" (six vertices in a path whose
  inner four have degree 2).
- A good leaf is eliminated by fixing one input, which removes enough gates to pay for its edge
  and its share of the cover.
- A run is handled by a "deep step" on its four inner vertices.
- The numerals 7 enter in only one place: the graph lemma that produces a run when no good leaf
  exists. No circuit lemma reads them: in the formal proof, the class appears only in the
  heredity lemma (closure under deleting vertices) and in the lemma that finds a run.
- The class is closed under deleting vertices, which the induction needs.
- Smallest graphs where this proof as written does not apply (not where the statement is known
  false): the 5-cycle; for the formal proof, the 6-cycle with one pendant leaf. The statement is
  FALSE with a 4-cycle: (x0 OR x2) AND (x1 OR x3) is an explicit 3-gate circuit for C4, against
  |E| + tau - 1 = 5. This is a hand-written circuit, not a row.

## 4. Lean files (published with this note, in the project's public repository)

- Statements: `lean/PEqualNP/MetaComplexity/` files L204, L104, L102, L106, L105, L154, L115 and
  L113 (`.lean`).
- Proofs: the files those statements import, under `lean/PEqualNP/MetaComplexity/Helpers/`
  (the EdgeFn files, LocGraph, LocStruct and CycleCore).
- Repository: https://github.com/brilliant-hq/pequalnp-proofs
- The definitions (circuits, gate count, graphs) are under `lean/PEqualNP/Defs/`.
- The plain-language text of L-meta-106, 113 and 115 carries correction notes, because the
  original text was written before the check.

## 5. What was searched, and what was NOT (honest coverage)

Searched, with nothing found that states (a) to (c) or implies them in a few lines: two
independent searches, about twenty web queries in all, on:
- the circuit complexity of quadratic or graph functions;
- exact circuit sizes of small or structured functions;
- gate elimination;
- single-level circuits;
- Karchmer-Wigderson games and formula size for graph functions;
- direct-sum questions.
Opened in full:
- Jukna, ECCC TR05-021 ("Disproving the single level conjecture");
- Jukna, ECCC TR04-005 ("On graph complexity");
- a draft of Jukna's chapter "Computational complexity of graphs";
- Wegener, "The Complexity of Boolean Functions" (1987), Secs. 4.7, 6.3 and 6.6, and Ch. 8;
- Pippenger, "On another Boolean matrix" (1980);
- a lecture text on gate elimination.
Nearest printed results, and the exact difference:
- Monotone FORMULAS for f_G need at least |E| leaves on triangle-free, C4-free graphs (Jukna;
  graph-complexity chapter Thm 1.23). Ours: all-gate CIRCUITS, NOT gates allowed, with the
  additional tau term, exact.
- Single-level monotone circuits need |E| gates on K_(2,2)-free graphs (Amano and Maruoka,
  quoted in TR05-021). Ours: unrestricted circuits with NOT gates.
- Threshold-2 (f_G for the complete graph): AND count ceil(log n), OR count 2n - 4, and monotone
  size above 2n - 4 + log n (Wegener 1987, Thm 6.3.1; Bloniarz 1979). Dense graph; different
  class.
- Gate elimination in general (Schnorr; Blum; Find, Golovnev, Hirsch and Kulikov 2016). Our
  elimination steps are specific to f_G and the cover number.
NOT read (any of these may contain the result or part of it):
- Knuth, TAOCP Vol. 4A, Sec. 7.1.2: exhaustive optimal circuits for functions of at most 5
  variables (would cover the 5-cycle and small paths only).
- Jukna, "Boolean Function Complexity" (2012), in its published form. A draft was searched for
  research problems only.
- Amano and Maruoka, Algorithmica 46 (2006); Lenz and Wegener, TCS 81 (1991); Mirwald and
  Schnorr, TCS 102 (1992); Pudlak, Rodl and Savicky (1988): each known only through quotations.
- Bloniarz 1979 (threshold-2), Krichevskii 1964, Hansel 1964.
- SAT-based exact circuit synthesis papers (Kulikov and coauthors), known from snippets only.
- Literature on exact circuit complexity of specific small functions after 2016, beyond the
  queries logged.
- Exact-size results in the basis AND, OR, NOT with EVERY gate counted, the same cost measure as
  here. This includes the 1970s school of minimality proofs for specific functions; one reader
  recalls, unopened, an exact value 4n - 4 for parity in that basis. None of these papers was
  identified or opened.
Theorem numbers and values quoted above from print were read by this seat or its reading legs;
the red team did not re-open them.

## 6. The question

Is the exact value |E| + tau(G) - 1 (all gates, NOT gates allowed) for the graph function f_G,
on forests, cycles or graphs with long threads, known? Or does it follow from a known
gate-elimination result?
