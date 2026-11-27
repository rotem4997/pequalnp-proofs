import PEqualNP.MetaComplexity.Helpers.RunPQ2g
import PEqualNP.MetaComplexity.Helpers.RunPQ2e
import PEqualNP.MetaComplexity.Helpers.RunAsm6

/-!
# The q2 side, item D and the final assembly: `AsmPQ2` from one named remainder

Conjecture until the checker accepts.

`pq2h_main_of_beta` proves `AsmPQ2` from `Pq2hBeta`, the single statement left: the reader `o2`
of `x_q2` in `C` is an OR gate `OR(x_q2, W2)` (the only reader of `x_q2`), and `o2` is NOT read
by exactly one AND gate (that case, the state Q2-AND, is `pq2e_qd`). The assembly done here:

* two distinct readers of `x_q2`: (q-a)/(q-b) by `pq2_two_readers`;
* case Q1 (the reader comes from `A_k` with a partner `w_k = x_q2`): (q-a) by `pq2g_ap_q2`;
* case R, a single reader `o2`, an OR gate (the chain of item A has only OR gates, and the
  operation is kept by `pq2g_back`), with the two operands `x_q2` and `W2`;
* `o2` read by exactly one AND gate `M`: the third disjunct by `pq2e_qd`, its six no-repeat
  facts from `pq2f_ne_*`;
* otherwise `Pq2hBeta` (fates (a) to (g) of the paper, not proved here).
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.EdgeFn

/-- The remainder of `AsmPQ2` (case R, not Q2-AND): `o2 = OR(x_q2, W2)` is the only reader of
`x_q2`, and it is not the case that exactly one AND gate reads `o2`. Then `Drop q2 true 4` or
the double restriction `x_q2 := 1`, `x_q1 := 0` saves five gates. (Paper: the q2-side argument Lemma Q2
(1), (2), fates (a) to (g).) -/
def Pq2hBeta : Prop :=
  asmChain → ∀ (N : ℕ) (G : SimpleGraph (Fin (N + 2))) (q0 q1 q2 q3 q4 q5 : Fin (N + 2))
    (gs : List Gate) (o p1 p2 : ℕ) (g1 g2 : Gate) (u1 u2 : ℕ),
    r4Run G q0 q1 q2 q3 q4 q5 → Least (N + 2) (F G ∅) gs o →
    gs[p1]? = some g1 → g1.op = GateOp.or → (g1.inputs = [(q1 : ℕ), u1] ∨ g1.inputs = [u1, q1]) →
    gs[p2]? = some g2 → g2.op = GateOp.or → (g2.inputs = [(q1 : ℕ), u2] ∨ g2.inputs = [u2, q1]) →
    p1 ≠ p2 → (∀ t, Reads gs t q1 → t = p1 ∨ t = p2) →
    AsmShapeI (N + 2) gs p1 p2 u1 u2 → ¬ Drop (F G ∅) q1 true 5 gs.length →
    ∀ (o2 : ℕ) (go2 : Gate) (W2 : ℕ), gs[o2]? = some go2 → go2.op = GateOp.or →
      (go2.inputs = [(q2 : ℕ), W2] ∨ go2.inputs = [W2, q2]) →
      (∀ t, Reads gs t q2 → t = o2) →
      ¬ (∃ (jM : ℕ) (gM : Gate) (z : ℕ), gs[jM]? = some gM ∧ gM.op = GateOp.and ∧
          (gM.inputs = [N + 2 + o2, z] ∨ gM.inputs = [z, N + 2 + o2]) ∧
          ∀ t, Reads gs t (N + 2 + o2) → t = jM) →
      Drop (F G ∅) q2 true 4 gs.length ∨
        ∃ s', s' + 5 ≤ gs.length ∧ HasCircuitSize (N + 2)
          (fun x => F G ∅ (Function.update (Function.update x q2 true) q1 false)) s'

/-- `AsmPQ2` from `Pq2hBeta`. -/
theorem pq2h_main_of_beta (hB : Pq2hBeta) : AsmPQ2 := by
  intro hch n G q0 q1 q2 q3 q4 q5 gs o p1 p2 g1 g2 u1 u2 r L hg1 ho1 hu1 hg2 ho2 hu2 h12 hall hS h5
  -- the arity is at least two
  rcases n with _ | N
  · exfalso
    have h12 : q1 ≠ q2 := by
      have := r.nd
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true] at this
      exact this.1.1
    exact h12 (Fin.ext (by have := q1.isLt; have := q2.isLt; omega))
  obtain ⟨hD, -⟩ := r4_stmtG3 (N + 1) G ∅ q0 q1 q2 q3 q4 q5
    (fun i _ _ h => Finset.notMem_empty i h) r
  have hnc2 := hD.nc q2 (by simp)
  have hnc : ∃ x y : Fin (N + 2) → Bool, F G ∅ x ≠ F G ∅ y := by
    obtain ⟨x, y, h⟩ := hnc2 true
    exact ⟨_, _, h⟩
  obtain ⟨a1, a2, ga1, ga2, w1, w2, h12', hpa1, hpa2, hga1, hao1, hai1, hga2, hao2, hai2,
    hrd1, hrd2, hu1r, hu2r⟩ := hS
  obtain ⟨j, q, hjq, hLeast, hlen, hch1, hrd⟩ := pq2g_back hch N G q0 q1 q2 q3 q4 q5 r gs o L
    p1 p2 g1 g2 u1 u2 hg1 ho1 hu1 hg2 ho2 hu2 h12 a1 a2 ga1 ga2 w1 w2 h12' hga1 hao1 hai1
    hga2 hao2 hai2 h5
  -- the reader `c 0` of `j` in the chain
  obtain ⟨k, c, hmono, hlast, hout, hops, hc0, hcs, hsole, hsolei, hcone, hw0, hws⟩ := hch1
  obtain ⟨g', hg', hj'⟩ := hc0
  obtain ⟨p, g, hp, hp1, hp2, hpa1', hpa2', hE, hop, hst, hcase⟩ := hrd _ g' hg' hj'
  -- case Q1: a partner is `x_q2`
  rcases hcase with hR | ⟨-, hw⟩
  swap
  · left
    rcases hw with hw | hw
    · exact pq2g_ap_q2 G q0 q1 q2 q3 q4 q5 r L p1 a1 ga1 hga1 hao1
        (by rcases hai1 with h | h
            · exact Or.inl (by rw [h, hw])
            · exact Or.inr (by rw [h, hw])) hrd1
    · exact pq2g_ap_q2 G q0 q1 q2 q3 q4 q5 r L p2 a2 ga2 hga2 hao2
        (by rcases hai2 with h | h
            · exact Or.inl (by rw [h, hw])
            · exact Or.inr (by rw [h, hw])) hrd2
  -- case R: `p` reads `x_q2`; it is the only reader, else (q-a) or (q-b)
  by_cases hrq2 : ∀ t, Reads gs t q2 → t = p
  swap
  · push_neg at hrq2
    obtain ⟨t, ht, hne⟩ := hrq2
    rcases pq2_two_readers (N + 1) G q0 q1 q2 q3 q4 q5 gs o r L t p hne ht ⟨g, hp, hR⟩ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  -- `p` is an OR gate with the operands `x_q2` and `W2`
  have hgor : g.op = GateOp.or := by
    obtain ⟨g'', hg'', hor, -⟩ := hops 0
    rw [hg'] at hg''
    cases hg''
    rw [← hop]; exact hor
  obtain ⟨W2, hoin2⟩ : ∃ W2, g.inputs = [(q2 : ℕ), W2] ∨ g.inputs = [W2, (q2 : ℕ)] := by
    rcases L.hcl p g hp with ⟨h1, -⟩ | ⟨-, j1, k1, -, -, hin⟩
    · rw [hgor] at h1; cases h1
    · rw [hin] at hR ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with h | h
      · exact ⟨k1, Or.inl (by rw [← h])⟩
      · exact ⟨j1, Or.inr (by rw [← h])⟩
  have hne_W2 : W2 ≠ (q2 : ℕ) := pq2f_ne_W2 L hnc hp hgor hoin2
  by_cases hM : ∃ (jM : ℕ) (gM : Gate) (z : ℕ), gs[jM]? = some gM ∧ gM.op = GateOp.and ∧
      (gM.inputs = [N + 2 + p, z] ∨ gM.inputs = [z, N + 2 + p]) ∧
      ∀ t, Reads gs t (N + 2 + p) → t = jM
  · obtain ⟨jM, gM, z, hgM, hMop, hMin, hrM⟩ := hM
    right; right
    have hread : Reads gs jM (N + 2 + p) :=
      ⟨gM, hgM, by rcases hMin with h | h <;> rw [h] <;> simp⟩
    have hoM : p < jM := by
      have := reads_lt L.hcl hread
      omega
    exact pq2e_qd hch (N + 1) G q0 q1 q2 q3 q4 q5 r gs o L p1 p2 a1 a2 p jM g1 g2 ga1 ga2 g gM
      u1 u2 w1 w2 W2 z hg1 ho1 hu1 hg2 ho2 hu2 h12 hall h12' hpa1 hpa2 hga1 hao1 hai1 hga2 hao2
      hai2 hrd1 hrd2 hu1r hu2r (pq2f_ne_u1 L hnc hg1 ho1 hu1) (pq2f_ne_u1 L hnc hg2 ho2 hu2)
      (pq2f_ne_w1 L hnc hga1 hao1 hai1) (pq2f_ne_w1 L hnc hga2 hao2 hai2) hp hgor hoin2 hne_W2
      hrq2 hp1 hp2 hgM hMop hMin (pq2f_ne_z L hnc hgM hMop hMin) hoM hrM
  · rcases hB hch N G q0 q1 q2 q3 q4 q5 gs o p1 p2 g1 g2 u1 u2 r L hg1 ho1 hu1 hg2 ho2 hu2 h12
      hall ⟨a1, a2, ga1, ga2, w1, w2, h12', hpa1, hpa2, hga1, hao1, hai1, hga2, hao2, hai2, hrd1,
        hrd2, hu1r, hu2r⟩ h5 p g W2 hp hgor hoin2 hrq2 hM with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end PEqualNP.MetaComplexity.Helpers.RunAsm
