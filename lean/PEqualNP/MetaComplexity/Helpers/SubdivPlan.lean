import Mathlib
import PEqualNP.MetaComplexity.Helpers.SubdivDefs
import PEqualNP.MetaComplexity.Helpers.SubdivBridge
import PEqualNP.MetaComplexity.Helpers.RootOnlyBridge

/-!
# Plan of the subdivision link (chain links L5 and L9, gaps G3 and G5)

Pieces in the order of SUBDIVISION-FOR-BUILDER.md section 5 (S1 to S8), on the definitions of
`SubdivDefs.lean`, plus the hub-distance half of the class (`StmtHub`, the half of L-meta-204's
class not covered by a filed row) and the class itself (S9).

THE PIECES ARE THE FILED ROWS. `RowL280` .. `RowL291` are the statements of L-meta-280, 281,
285, 286, 288, 289, 290, 291, verbatim (scratch-sub/filed-rows/); `stmtSn_of_L...` turns each into
the plan piece through `SubdivBridge` (`graph_eq`, `pos_eq`). `rowL280_proof` PROVES L-meta-280.
`RowHubDist` is the PROPOSED missing row (hub distance, same inline graph).

Proved here: `stmtS1` = `rowL280_proof`, `pdeg`, `stmtS7_of`, `stmtHub_of` (hub distance from S2
and Theorem P (ii)), `stmtS9_of` (class from S3 and `StmtHub`), the assembly `subdivTarget_of`,
and `subdivTarget_of_filed`: `SubdivTarget` from the filed rows 285, 286, 288, 289, 291 and
`RowHubDist`. Open, one builder each: S2, S3, S4, S5 with S8, S6, Theorem P (ii) or `RowHubDist`.
-/

namespace PEqualNP.MetaComplexity.Subdiv

open SimpleGraph

/-- The labelling hypotheses (GRAPH-FOR-BUILDER section 3, LB-SUB clauses 1 and 2): no edge joins
two vertices of label `0`; a vertex of nonzero label `p` has `p ≤ 2k` and exactly two neighbours,
one of label `p - 1` and one of label `(p + 1) mod (2k + 1)`. -/
def Lab {N : ℕ} (k : ℕ) (G : SimpleGraph (Fin N)) (pos : Fin N → ℕ) : Prop :=
  (∀ u v : Fin N, G.Adj u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧
  ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N,
    (∀ w : Fin N, G.Adj v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧
      pos b = (pos v + 1) % (2 * k + 1)

/-! ## The pieces -/

/-- S1 (sheet 1.3): thread indices decode uniquely. PROVED (`stmtS1`). -/
def StmtS1 : Prop :=
  ∀ (m k : ℕ) (u v u' v' : Fin m) (i i' : ℕ), i < 2 * k → i' < 2 * k →
    m + 2 * k * (u.val * m + v.val) + i = m + 2 * k * (u'.val * m + v'.val) + i' →
      u = u' ∧ v = v' ∧ i = i'

theorem stmtS1 : StmtS1 := fun _ _ _ _ _ _ _ _ hi hi' h => thr_inj hi hi' h

/-- S2 (sheet 1.5 L1, L2; GRAPH-FOR-BUILDER 3 `Lab`): the thread label satisfies `Lab`. -/
def StmtS2 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], 1 ≤ k → Lab k (subdiv k H) (pos k H)

/-- S3 (sheet 1.5 L3): every cycle has length at least `6k + 3` (only for the LB-SUB row; the
class S9 needs `2k + 1` only). -/
def StmtS3 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ (L : ℕ) (c : ℕ → Fin (nS m k)), 3 ≤ L →
    (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) →
    (∀ i : ℕ, i < L → (subdiv k H).Adj (c i) (c ((i + 1) % L))) → 6 * k + 3 ≤ L

/-- S4 (sheet 4, RECORD-k 2.1): `|E(S)| = (2k + 1)|E(H)|`. -/
def StmtS4 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k →
    (subdiv k H).edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard

/-- S5 (sheet 2.1 to 2.3, RECORD-k 1.2): the forward cover is a cover with `|T| + k|E(H)|`
vertices. -/
def StmtS5 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (T : Finset (Fin m)), 1 ≤ k →
    (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) →
    (∀ x y : Fin (nS m k), (subdiv k H).Adj x y → x ∈ fwd k H T ∨ y ∈ fwd k H T) ∧
      (fwd k H T).card = T.card + k * H.edgeSet.ncard

/-- S6 (sheet 2.4 to 2.6, RECORD-k 1.3): the back map gives a cover of `H` with at most
`|U| - k|E(H)|` vertices. -/
def StmtS6 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (U : Finset (Fin (nS m k))), 1 ≤ k →
    (∀ x y : Fin (nS m k), (subdiv k H).Adj x y → x ∈ U ∨ y ∈ U) →
    (∀ u v : Fin m, H.Adj u v → u ∈ back k H U ∨ v ∈ back k H U) ∧
      (back k H U).card + k * H.edgeSet.ncard ≤ U.card

/-- S7 (sheet 2.7, the form L-meta-204 consumes). PROVED from S6 (`stmtS7_of`). -/
def StmtS7 : Prop :=
  ∀ (k m c : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k →
    (∀ T : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → c ≤ T.card) →
    ∀ U : Finset (Fin (nS m k)), (∀ x y : Fin (nS m k), (subdiv k H).Adj x y → x ∈ U ∨ y ∈ U) →
      c + k * H.edgeSet.ncard ≤ U.card

/-- S8 (sheet 3.1, RECORD-k 1.5): the forward cover of an inclusion-minimal cover has a private
edge at every member. -/
def StmtS8 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (T : Finset (Fin m)), 1 ≤ k →
    (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → (∀ t ∈ T, ∃ w : Fin m, H.Adj t w ∧ w ∉ T) →
    ∀ x ∈ fwd k H T, ∃ y : Fin (nS m k), (subdiv k H).Adj x y ∧ y ∉ fwd k H T

/-- S9 (RECORD-k 1.7 (c), (d); GRAPH-FOR-BUILDER Theorem P): for `k ≥ 3` the subdivision has
the two class hypotheses of L-meta-204. PROVED from S3 and `StmtHub` (`stmtS9_of`). -/
def StmtS9 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 3 ≤ k →
    (∀ (v : Fin (nS m k)) (c : (subdiv k H).Walk v v), c.IsCycle → 7 ≤ c.length) ∧
    ∀ u v : Fin (nS m k), u ≠ v → 3 ≤ ((subdiv k H).neighborSet u).ncard →
      3 ≤ ((subdiv k H).neighborSet v).ncard → ∀ p : (subdiv k H).Walk u v, 7 ≤ p.length

/-- Theorem P (ii) (GRAPH-FOR-BUILDER 3, F1 to F7): under `Lab`, a walk between two distinct
vertices of label `0` has length at least `2k + 1`. -/
def StmtPDist : Prop :=
  ∀ (N k : ℕ) (G : SimpleGraph (Fin N)) (pos : Fin N → ℕ), 1 ≤ k → Lab k G pos →
    ∀ u v : Fin N, pos u = 0 → pos v = 0 → u ≠ v → ∀ p : G.Walk u v, 2 * k + 1 ≤ p.length

/-- The hub-distance half of the class: two distinct vertices of the subdivision with at least three
neighbours each are joined by no walk shorter than `2k + 1` (RECORD-k 1.7 (c)). -/
def StmtHub : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k →
    ∀ u v : Fin (nS m k), u ≠ v → 3 ≤ ((subdiv k H).neighborSet u).ncard →
      3 ≤ ((subdiv k H).neighborSet v).ncard → ∀ p : (subdiv k H).Walk u v, 2 * k + 1 ≤ p.length

/-! ## What is proved here -/

/-- Theorem P (iii): a vertex with at least three neighbours has label `0`. -/
theorem pdeg {N k : ℕ} {G : SimpleGraph (Fin N)} {pos : Fin N → ℕ} (h : Lab k G pos) (v : Fin N)
    (h3 : 3 ≤ (G.neighborSet v).ncard) : pos v = 0 := by
  by_contra hv
  obtain ⟨-, a, b, hab, -, -⟩ := h.2 v hv
  have hset : G.neighborSet v = insert a {b} := by
    ext w
    simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hab w
  have := Set.ncard_insert_le a ({b} : Set (Fin N))
  rw [Set.ncard_singleton, ← hset] at this
  omega

theorem stmtS7_of (h6 : StmtS6) : StmtS7 := by
  intro k m c H hk hc U hU
  classical
  obtain ⟨hcov, hcard⟩ := h6 k m H U hk hU
  have := hc _ hcov
  omega

theorem stmtHub_of (h2 : StmtS2) (hd : StmtPDist) : StmtHub := by
  intro k m H hk u v huv hu hv p
  classical
  have hl := h2 k m H hk
  exact hd _ k _ _ hk hl u v (pdeg hl u hu) (pdeg hl v hv) huv p

theorem stmtS9_of (h3 : StmtS3) (hh : StmtHub) : StmtS9 := by
  intro k m H hk
  refine ⟨fun v c hcyc => ?_, fun u v huv hu hv p => ?_⟩
  · have := (PEqualNP.MetaComplexity.RootOnly.cycleHyp_iff (G := subdiv k H) (6 * k + 3)).mp
      (h3 k m H (by omega)) v c hcyc
    omega
  · have := hh k m H (by omega) u v huv hu hv p
    omega

/-- The assembly the chain consumes: for `H` on `Fin m`, `k ≥ 3` and a cover `T` of `H`, the
subdivision is in the class of L-meta-204, has `(2k + 1)|E(H)|` edges, the forward cover is a
cover with `|T| + k|E(H)|` vertices, the cover bounds shift by exactly `k|E(H)|` (both ways), and
an inclusion-minimal `T` gives a forward cover with a private edge at every member. -/
def SubdivTarget : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (T : Finset (Fin m)), 3 ≤ k →
    (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) →
    ((∀ (v : Fin (nS m k)) (c : (subdiv k H).Walk v v), c.IsCycle → 7 ≤ c.length) ∧
      ∀ u v : Fin (nS m k), u ≠ v → 3 ≤ ((subdiv k H).neighborSet u).ncard →
        3 ≤ ((subdiv k H).neighborSet v).ncard → ∀ p : (subdiv k H).Walk u v, 7 ≤ p.length) ∧
    (subdiv k H).edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard ∧
    (∀ x y : Fin (nS m k), (subdiv k H).Adj x y → x ∈ fwd k H T ∨ y ∈ fwd k H T) ∧
    (fwd k H T).card = T.card + k * H.edgeSet.ncard ∧
    (∀ j : ℕ, (∀ S : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ S ∨ v ∈ S) → j ≤ S.card) ↔
      (∀ S : Finset (Fin (nS m k)), (∀ x y : Fin (nS m k), (subdiv k H).Adj x y → x ∈ S ∨ y ∈ S) →
        j + k * H.edgeSet.ncard ≤ S.card)) ∧
    ((∀ t ∈ T, ∃ w : Fin m, H.Adj t w ∧ w ∉ T) →
      ∀ x ∈ fwd k H T, ∃ y : Fin (nS m k), (subdiv k H).Adj x y ∧ y ∉ fwd k H T)

theorem subdivTarget_of (h3 : StmtS3) (hh : StmtHub) (h4 : StmtS4) (h5 : StmtS5)
    (h6 : StmtS6) (h8 : StmtS8) : SubdivTarget := by
  intro k m H _ T hk hT
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hF, hFc⟩ := h5 k m H T hk1 hT
  refine ⟨stmtS9_of h3 hh k m H hk, h4 k m H hk1, hF, hFc, fun j => ⟨?_, ?_⟩,
    h8 k m H T hk1 hT⟩
  · intro hj S hS
    exact stmtS7_of h6 k m j H hk1 hj S hS
  · intro hj S hS
    obtain ⟨hF', hFc'⟩ := h5 k m H S hk1 hS
    have := hj _ hF'
    omega

theorem fwd_char {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (T : Finset (Fin m))
    (j : Fin (nS m k)) :
    j ∈ fwd k H T ↔ (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k),
      u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
        (i.val % 2 = 1 ↔ u ∈ T) := by
  simp only [fwd, Finset.mem_filter, Finset.mem_univ, true_and]

theorem back_char {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (U : Finset (Fin (nS m k))) (u : Fin m) :
    u ∈ back k H U ↔ (∃ x ∈ U, x.val = u.val) ∨ ∃ v : Fin m, u < v ∧ H.Adj u v ∧
      (∀ x ∈ U, x.val ≠ u.val) ∧ (∀ x ∈ U, x.val ≠ v.val) := by
  simp only [back, Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## The filed rows, verbatim, and the bridge to the plan pieces -/

/-- L-meta-280 as filed: thread indices decode uniquely. -/
def RowL280 : Prop :=
  ∀ (m k : ℕ) (u v u' v' : Fin m) (i i' : ℕ), i < 2 * k → i' < 2 * k → m + 2 * k * (u.val * m + v.val) + i = m + 2 * k * (u'.val * m + v'.val) + i' → u = u' ∧ v = v' ∧ i = i'

/-- L-meta-281 as filed: the thread labelling satisfies the labelling hypotheses. -/
def RowL281 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ pos : Fin (m + 2 * k * m * m) → ℕ, (∀ j : Fin (m + 2 * k * m * m), pos j = ∑ u : Fin m, ∑ v : Fin m, ∑ i : Fin (2 * k), if u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val then i.val + 1 else 0) → (∀ u v : Fin (m + 2 * k * m * m), S.Adj u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin (m + 2 * k * m * m), pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin (m + 2 * k * m * m), (∀ w : Fin (m + 2 * k * m * m), S.Adj v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)

/-- L-meta-285 as filed: every cycle has length at least 6k + 3. -/
def RowL285 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ (L : ℕ) (c : ℕ → Fin (m + 2 * k * m * m)), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) → (∀ i : ℕ, i < L → S.Adj (c i) (c ((i + 1) % L))) → 6 * k + 3 ≤ L

/-- L-meta-286 as filed: edge count (2k + 1)|E(H)|. -/
def RowL286 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → S.edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard

/-- L-meta-288 as filed: forward cover map. -/
def RowL288 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)), 1 ≤ k → (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ F : Finset (Fin (m + 2 * k * m * m)), (∀ j : Fin (m + 2 * k * m * m), j ∈ F ↔ (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T)) → (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ F ∨ y ∈ F) ∧ F.card = T.card + k * H.edgeSet.ncard

/-- L-meta-289 as filed: backward cover map. -/
def RowL289 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ U : Finset (Fin (m + 2 * k * m * m)), (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) → ∀ R : Finset (Fin m), (∀ u : Fin m, u ∈ R ↔ (∃ x ∈ U, x.val = u.val) ∨ ∃ v : Fin m, u < v ∧ H.Adj u v ∧ (∀ x ∈ U, x.val ≠ u.val) ∧ (∀ x ∈ U, x.val ≠ v.val)) → (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) ∧ R.card + k * H.edgeSet.ncard ≤ U.card

/-- L-meta-290 as filed: cover shift. -/
def RowL290 : Prop :=
  ∀ (k m c : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → (∀ T : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → c ≤ T.card) → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ U : Finset (Fin (m + 2 * k * m * m)), (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) → c + k * H.edgeSet.ncard ≤ U.card

/-- L-meta-291 as filed: forward cover of a minimal cover has private edges. -/
def RowL291 : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)), 1 ≤ k → (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → (∀ t ∈ T, ∃ w : Fin m, H.Adj t w ∧ w ∉ T) → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ F : Finset (Fin (m + 2 * k * m * m)), (∀ j : Fin (m + 2 * k * m * m), j ∈ F ↔ (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T)) → ∀ x ∈ F, ∃ y : Fin (m + 2 * k * m * m), S.Adj x y ∧ y ∉ F

/-- PROPOSED row (not filed): hub distance in the subdivision, same inline graph as the filed rows. -/
def RowHubDist : Prop :=
  ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ u v : Fin (m + 2 * k * m * m), u ≠ v → 3 ≤ (S.neighborSet u).ncard → 3 ≤ (S.neighborSet v).ncard → ∀ p : S.Walk u v, 2 * k + 1 ≤ p.length

theorem rowL280_proof : RowL280 := stmtS1

theorem stmtS2_of_L281 (h : RowL281) : StmtS2 := fun k m H _ hk =>
  h k m H hk (subdiv k H) (Bridge.graph_eq H hk).symm (pos k H) (fun j => (Bridge.pos_eq H j).symm)

theorem stmtS3_of_L285 (h : RowL285) : StmtS3 := fun k m H hk =>
  h k m H hk (subdiv k H) (Bridge.graph_eq H hk).symm

theorem stmtS4_of_L286 (h : RowL286) : StmtS4 := fun k m H hk =>
  h k m H hk (subdiv k H) (Bridge.graph_eq H hk).symm

theorem stmtS5_of_L288 (h : RowL288) : StmtS5 := fun k m H _ T hk hT =>
  h k m H T hk hT (subdiv k H) (Bridge.graph_eq H hk).symm (fwd k H T) (fwd_char H T)

theorem stmtS6_of_L289 (h : RowL289) : StmtS6 := fun k m H _ U hk hU =>
  h k m H hk (subdiv k H) (Bridge.graph_eq H hk).symm U hU (back k H U) (back_char H U)

theorem stmtS7_of_L290 (h : RowL290) : StmtS7 := fun k m c H hk hc U hU =>
  h k m c H hk hc (subdiv k H) (Bridge.graph_eq H hk).symm U hU

theorem stmtS8_of_L291 (h : RowL291) : StmtS8 := fun k m H _ T hk hT hmin =>
  h k m H T hk hT hmin (subdiv k H) (Bridge.graph_eq H hk).symm (fwd k H T) (fwd_char H T)

theorem stmtHub_of_row (h : RowHubDist) : StmtHub := fun k m H hk =>
  h k m H hk (subdiv k H) (Bridge.graph_eq H hk).symm

/-- The assembly from the filed rows and the proposed hub-distance row. -/
theorem subdivTarget_of_filed (h285 : RowL285) (h286 : RowL286) (h288 : RowL288)
    (h289 : RowL289) (h291 : RowL291) (hhub : RowHubDist) : SubdivTarget :=
  subdivTarget_of (stmtS3_of_L285 h285) (stmtHub_of_row hhub) (stmtS4_of_L286 h286)
    (stmtS5_of_L288 h288) (stmtS6_of_L289 h289) (stmtS8_of_L291 h291)

/-- The same with the hub distance from L-meta-281 and Theorem P (ii). -/
theorem subdivTarget_of_filed' (h281 : RowL281) (h285 : RowL285) (h286 : RowL286)
    (h288 : RowL288) (h289 : RowL289) (h291 : RowL291) (hd : StmtPDist) : SubdivTarget :=
  subdivTarget_of (stmtS3_of_L285 h285) (stmtHub_of (stmtS2_of_L281 h281) hd)
    (stmtS4_of_L286 h286) (stmtS5_of_L288 h288) (stmtS6_of_L289 h289) (stmtS8_of_L291 h291)

end PEqualNP.MetaComplexity.Subdiv
