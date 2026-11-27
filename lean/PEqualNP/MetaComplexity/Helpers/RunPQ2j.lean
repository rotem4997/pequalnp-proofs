import PEqualNP.MetaComplexity.Helpers.RunPQ2i

/-!
# The q2 side, stage I (part 2): the fates at `x_q2 := 1`

Conjecture until the checker accepts. With no drop of four at `x_q2 := 1`, at most three
positions of the least list read a constant there. The three gates `o2`, `r1`, `r2` are
named; the fates of the two OR gates of shape (i) (paper the q2-side argument (2), (a) to (g)) are
settled by counting positions that read a constant at `x_q2 := 1` or, once emitted, read the
input `x_q1` in the cleaned list.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.EdgeFn

/-- Four distinct positions that read a constant contradict the bound of three. -/
theorem pq2j_no4 (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool)
    (hall3 : ∀ S : Finset ℕ, (∀ p ∈ S, RC n gs i b p) → S.card ≤ 3)
    (a b' c d : ℕ) (hab : a ≠ b') (hac : a ≠ c) (had : a ≠ d) (hbc : b' ≠ c) (hbd : b' ≠ d)
    (hcd : c ≠ d) (ha : RC n gs i b a) (hb : RC n gs i b b') (hc : RC n gs i b c)
    (hd : RC n gs i b d) : False := by
  have h := hall3 {a, b', c, d} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({a, b', c, d} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  omega

/-- The finish with named gates `o2`, `r1`, `r2` and two saved gates of the emitted list. -/
theorem pq2j_fin (N : ℕ) (G : SimpleGraph (Fin (N + 2))) (q0 q1 q2 q3 q4 q5 : Fin (N + 2))
    (r : r4Run G q0 q1 q2 q3 q4 q5) (gs : List Gate) (o : ℕ) (L : Least (N + 2) (F G ∅) gs o)
    (hnc1 : ∃ x y : Fin (N + 2) → Bool,
      F G ∅ (Function.update x q2 true) ≠ F G ∅ (Function.update y q2 true))
    (j : Fin (N + 1)) (hj : q2.succAbove j = q1)
    (o2 r1 r2 : ℕ) (ho : RC (N + 1) gs q2 true o2) (hr1 : RC (N + 1) gs q2 true r1)
    (hr2 : RC (N + 1) gs q2 true r2) (h1 : o2 ≠ r1) (h2 : o2 ≠ r2) (h12 : r1 ≠ r2)
    (e1 e2 : ℕ) (hee : e1 ≠ e2) (he1 : RC N (passG (N + 1) gs q2 true) j false e1)
    (he2 : RC N (passG (N + 1) gs q2 true) j false e2) :
    ∃ s', s' + 5 ≤ gs.length ∧ HasCircuitSize (N + 2)
      (fun x => F G ∅ (Function.update (Function.update x q2 true) q1 false)) s' := by
  refine pq2i_finish N G q0 q1 q2 q3 q4 q5 r gs o L hnc1 j hj {o2, r1, r2} {e1, e2} ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption
  · rw [Finset.card_eq_three.2 ⟨o2, r1, r2, h1, h2, h12, rfl⟩]
  · rw [Finset.card_pair hee]


/-- The status of the input `q1` at `x_q2 := 1` is the wire `j`. -/
theorem pq2j_hq1 (N : ℕ) (gs : List Gate) (q1 q2 : Fin (N + 2)) (j : Fin (N + 1))
    (hj : q2.succAbove j = q1) : stF (N + 1) gs q2 true (q1 : ℕ) = Stat.wire (j : ℕ) := by
  have := pq2i_st_succAbove (N + 1) gs q2 true j
  rwa [hj] at this

/-- Fate of a gate `g_k = OR(x_q1, u_k)` that reads a constant at `x_q2 := 1`, with the other
OR gate `g_l` of shape (i): at most three gates read a constant there, so the finish follows or
the case is empty. -/
theorem pq2j_rc_case (N : ℕ) (G : SimpleGraph (Fin (N + 2))) (q0 q1 q2 q3 q4 q5 : Fin (N + 2))
    (r : r4Run G q0 q1 q2 q3 q4 q5) (gs : List Gate) (o : ℕ) (L : Least (N + 2) (F G ∅) gs o)
    (hnc1 : ∃ x y : Fin (N + 2) → Bool,
      F G ∅ (Function.update x q2 true) ≠ F G ∅ (Function.update y q2 true))
    (hall3 : ∀ S : Finset ℕ, (∀ p ∈ S, RC (N + 1) gs q2 true p) → S.card ≤ 3)
    (j : Fin (N + 1)) (hj : q2.succAbove j = q1)
    (o2 : ℕ) (go2 : Gate) (hgo2 : gs[o2]? = some go2) (hoo2 : go2.op = GateOp.or)
    (h2in : (q2 : ℕ) ∈ go2.inputs) (hrq2 : ∀ t, Reads gs t q2 → t = o2)
    (hstO2 : stF (N + 1) gs q2 true (N + 2 + o2) = Stat.const true)
    (r1 r2 : ℕ) (hr1 : RC (N + 1) gs q2 true r1) (hr2 : RC (N + 1) gs q2 true r2)
    (ho1 : o2 ≠ r1) (ho2' : o2 ≠ r2) (h12 : r1 ≠ r2)
    (p : ℕ) (g : Gate) (u : ℕ) (hg : gs[p]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [(q1 : ℕ), u] ∨ g.inputs = [u, q1])
    (a : ℕ) (ga : Gate) (w : ℕ) (hpa : p < a) (hga : gs[a]? = some ga) (hao : ga.op = GateOp.and)
    (hai : ga.inputs = [N + 2 + p, w] ∨ ga.inputs = [w, N + 2 + p])
    (p' : ℕ) (g' : Gate) (u' : ℕ) (hg' : gs[p']? = some g') (hop' : g'.op = GateOp.or)
    (hin' : g'.inputs = [(q1 : ℕ), u'] ∨ g'.inputs = [u', q1])
    (hpp' : p ≠ p') (hop2 : o2 ≠ p) (hop2' : o2 ≠ p')
    (hrc : RC (N + 1) gs q2 true p) :
    ∃ s', s' + 5 ≤ gs.length ∧ HasCircuitSize (N + 2)
      (fun x => F G ∅ (Function.update (Function.update x q2 true) q1 false)) s' := by
  have hq1 := pq2j_hq1 N gs q1 q2 j hj
  have hoa : o2 ≠ a := by
    rintro rfl
    rw [hgo2] at hga; cases hga; rw [hoo2] at hao; cases hao
  have hRo2 : RC (N + 1) gs q2 true o2 := rc_input true ⟨go2, hgo2, h2in⟩
  have hplen : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hq1mem : (q1 : ℕ) ∈ g.inputs := by rcases hin with h | h <;> rw [h] <;> simp
  have humem : ∀ u0 : ℕ, (g.inputs = [(q1 : ℕ), u0] ∨ g.inputs = [u0, q1]) → u0 ∈ g.inputs := by
    intro u0 h; rcases h with h | h <;> rw [h] <;> simp
  -- the operand `u` has constant status
  obtain ⟨c, hc⟩ : ∃ c, stF (N + 1) gs q2 true u = Stat.const c := by
    obtain ⟨g0, hg0, a0, ha0, c, hc⟩ := hrc
    rw [hg] at hg0; cases hg0
    have h0 : a0 = q1 ∨ a0 = u := by
      rcases hin with h | h <;> rw [h] at ha0 <;> simp at ha0 <;> tauto
    rcases h0 with h0 | h0
    · rw [h0, hq1] at hc; cases hc
    · rw [h0] at hc; exact ⟨c, hc⟩
  have hult : u < N + 2 + p := (L.hcl p g hg).lt u (humem u hin)
  by_cases hu2 : u < N + 2
  · exfalso
    have he := pq2i_input_const (N + 1) gs q2 true u hu2 c hc
    exact hop2 (hrq2 p ⟨g, hg, by rw [← he]; exact humem u hin⟩).symm
  obtain ⟨t', rfl⟩ : ∃ t', u = N + 2 + t' := ⟨u - (N + 2), by omega⟩
  have ht'p : t' < p := by omega
  obtain ⟨gt', hgt'⟩ : ∃ gt', gs[t']? = some gt' :=
    ⟨gs[t'], List.getElem?_eq_getElem (by omega)⟩
  have hrct' : RC (N + 1) gs q2 true t' :=
    pq2i_rc_of_const (N + 1) gs L.hcl q2 true t' gt' hgt' c hc
  have hRa : Reads gs a (N + 2 + p) := ⟨ga, hga, by rcases hai with h | h <;> rw [h] <;> simp⟩
  cases c with
  | true =>
    have hgs : stF (N + 1) gs q2 true (N + 2 + p) = Stat.const true :=
      pq2i_st_or_true (N + 1) gs L.hcl q2 true p g hg hop (N + 2 + t') (humem _ hin) hc
    have hgc : IsC (N + 1) gs q2 true (N + 2 + p) := ⟨true, hgs⟩
    have hRCa : RC (N + 1) gs q2 true a := rc_of_reads hRa hgc
    have hte : o2 = t' := by
      by_contra hne
      exact pq2j_no4 (N + 1) gs q2 true hall3 o2 t' p a hne hop2 hoa (by omega) (by omega)
        (by omega) hRo2 hrct' hrc hRCa
    subst hte
    have hrd : ∀ t, Reads gs t (N + 2 + o2) → t = p := by
      intro t ht
      have hrct : RC (N + 1) gs q2 true t := rc_of_reads ht ⟨true, hstO2⟩
      have hlt : o2 < t := by have := reads_lt L.hcl ht; omega
      by_contra htp
      by_cases hta : t = a
      · subst hta
        obtain ⟨gt, hgt, hmem⟩ := ht
        rw [hga] at hgt; cases hgt
        have hw : w = N + 2 + o2 := by
          rcases hai with h | h <;> rw [h] at hmem <;> simp at hmem <;> omega
        have hac : IsC (N + 1) gs q2 true (N + 2 + t) := by
          rcases hai with h | h
          · exact pq2i_st_const2 (N + 1) gs L.hcl q2 true t ga hga (Or.inl hao) _ _ h true true
              hgs (by rw [hw]; exact hstO2)
          · exact pq2i_st_const2 (N + 1) gs L.hcl q2 true t ga hga (Or.inl hao) _ _ h true true
              (by rw [hw]; exact hstO2) hgs
        obtain ⟨q, haq, -, hqrc⟩ := L.next q2 true hnc1 t (List.getElem?_eq_some_iff.1 hga).1 hac
        exact pq2j_no4 (N + 1) gs q2 true hall3 o2 p t q hop2 hoa (by omega) (by omega)
          (by omega) (by omega) hRo2 hrc hrct hqrc
      · exact pq2j_no4 (N + 1) gs q2 true hall3 o2 p a t hop2 hoa (by omega) (by omega)
          (by omega) (by omega) hRo2 hrc hRCa hrct
    exact (pq2i_M2 N G q0 q1 q2 q3 q4 q5 r gs o L hnc1 o2 go2 hgo2 hoo2 h2in hrq2 p g hg hop
      hq1mem (humem _ hin) hrd).elim
  | false =>
    have hgal : stF (N + 1) gs q2 true (N + 2 + p) = stF (N + 1) gs q2 true q1 :=
      pq2i_st_or_false (N + 1) gs L.hcl q2 true p g hg hop (N + 2 + t') q1
        (by rcases hin with h | h
            · exact Or.inr h
            · exact Or.inl h) hc
    have hstp : stF (N + 1) gs q2 true (N + 2 + p) = Stat.wire (j : ℕ) := by rw [hgal, hq1]
    have hot : o2 ≠ t' := by
      intro e
      rw [← e, hstO2] at hc
      cases hc
    have hnRa : ¬ RC (N + 1) gs q2 true a := fun h =>
      pq2j_no4 (N + 1) gs q2 true hall3 o2 t' p a hot hop2 hoa (by omega) (by omega) (by omega)
        hRo2 hrct' hrc h
    have hnRp' : ¬ RC (N + 1) gs q2 true p' := by
      intro h
      have hpt : p' ≠ t' := by
        intro e
        have := pq2i_st_or_wire (N + 1) gs L.hcl q2 true p' g' hg' hop' q1
          (by rcases hin' with h | h <;> rw [h] <;> simp) j hq1
        rw [e] at this
        exact this hc
      exact pq2j_no4 (N + 1) gs q2 true hall3 o2 t' p p' hot hop2 hop2' (by omega) hpt.symm
        hpp' hRo2 hrct' hrc h
    have hap' : a ≠ p' := by
      rintro rfl
      rw [hg'] at hga; cases hga; rw [hop'] at hao; cases hao
    refine pq2j_fin N G q0 q1 q2 q3 q4 q5 r gs o L hnc1 j hj o2 r1 r2 hRo2 hr1 hr2 ho1 ho2' h12
      (pq2E (N + 1) gs q2 true a) (pq2E (N + 1) gs q2 true p') ?_ ?_ ?_
    · exact pq2i_E_ne (N + 1) gs L.hcl q2 true a p' ga g' hga hg' hnRa hnRp' (Or.inl hao)
        (Or.inr hop') hap'
    · rcases hai with h | h
      · exact pq2i_rc_pass N gs L.hcl q2 true a ga hga hnRa (Or.inl hao) _ _ h j (Or.inl hstp) false
      · exact pq2i_rc_pass N gs L.hcl q2 true a ga hga hnRa (Or.inl hao) _ _ h j (Or.inr hstp) false
    · rcases hin' with h | h
      · exact pq2i_rc_pass N gs L.hcl q2 true p' g' hg' hnRp' (Or.inr hop') _ _ h j (Or.inl hq1) false
      · exact pq2i_rc_pass N gs L.hcl q2 true p' g' hg' hnRp' (Or.inr hop') _ _ h j (Or.inr hq1) false


/-- The remainder `Pq2hBeta` of `AsmPQ2`: the fates of the OR gates of shape (i) at `x_q2 := 1`. -/
theorem pq2i_beta : Pq2hBeta := by
  intro hch N G q0 q1 q2 q3 q4 q5 gs o p1 p2 g1 g2 u1 u2 r L hg1 ho1 hu1 hg2 ho2 hu2 h12 hall hS h5
    o2 go2 W2 hgo2 hoo2 hoin2 hrq2 hM
  by_cases hD4 : Drop (F G ∅) q2 true 4 gs.length
  · exact Or.inl hD4
  right
  obtain ⟨hD, -⟩ := r4_stmtG3 (N + 1) G ∅ q0 q1 q2 q3 q4 q5
    (fun i _ _ h => Finset.notMem_empty i h) r
  have hnc1 : ∃ x y : Fin (N + 2) → Bool,
      F G ∅ (Function.update x q2 true) ≠ F G ∅ (Function.update y q2 true) := by
    obtain ⟨x, y, h⟩ := hD.nc q2 (by simp) true
    exact ⟨x, y, h⟩
  have hq12 : q1 ≠ q2 := by
    have := r.nd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at this
    exact this.1.1
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hq12
  have hall3 : ∀ S : Finset ℕ, (∀ p ∈ S, RC (N + 1) gs q2 true p) → S.card ≤ 3 := by
    intro S hS'
    by_contra h
    exact hD4 ((L.save q2 true hnc1 S hS').mono (by omega) le_rfl)
  have hq1 := pq2j_hq1 N gs q1 q2 j hj
  obtain ⟨a1, a2, ga1, ga2, w1, w2, h12', hpa1, hpa2, hga1, hao1, hai1, hga2, hao2, hai2,
    hrd1, hrd2, hu1r, hu2r⟩ := hS
  have h2in : (q2 : ℕ) ∈ go2.inputs := by
    rcases hoin2 with h | h <;> rw [h] <;> simp
  have hstO2 : stF (N + 1) gs q2 true (N + 2 + o2) = Stat.const true :=
    pq2i_st_or_true (N + 1) gs L.hcl q2 true o2 go2 hgo2 hoo2 (q2 : ℕ) h2in (stF_self _ _ _ _)
  have hRo2 : RC (N + 1) gs q2 true o2 := rc_input true ⟨go2, hgo2, h2in⟩
  have hlo2 : o2 < gs.length := (List.getElem?_eq_some_iff.1 hgo2).1
  -- the readers of `o2`
  obtain ⟨r1, hlt1, hread1, hrc1⟩ := L.next q2 true hnc1 o2 hlo2 ⟨true, hstO2⟩
  obtain ⟨r2, hrc2, hr12, hlt2⟩ : ∃ r2, RC (N + 1) gs q2 true r2 ∧ r1 ≠ r2 ∧ o2 < r2 := by
    by_cases hrr : ∃ t, t ≠ r1 ∧ Reads gs t (N + 2 + o2)
    · obtain ⟨t, hne, ht⟩ := hrr
      exact ⟨t, rc_of_reads ht ⟨true, hstO2⟩, hne.symm, by have := reads_lt L.hcl ht; omega⟩
    · push_neg at hrr
      have hrr' : ∀ t, Reads gs t (N + 2 + o2) → t = r1 := by
        intro t ht
        by_contra hne
        exact hrr t hne ht
      obtain ⟨gr1, hgr1, hmem⟩ := hread1
      have hisC : IsC (N + 1) gs q2 true (N + 2 + r1) := by
        rcases L.hcl r1 gr1 hgr1 with ⟨hnot, a0, -, hin⟩ | ⟨hbin, j', l, -, -, hin⟩
        · rw [hin] at hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          exact pq2i_st_not (N + 1) gs L.hcl q2 true r1 gr1 hgr1 hnot a0 hin true (by rw [← hmem]; exact hstO2)
        · rcases hbin with hand | hor
          · exfalso
            apply hM
            rw [hin] at hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with h | h
            · exact ⟨r1, gr1, l, hgr1, hand, Or.inl (by rw [hin, ← h]), hrr'⟩
            · exact ⟨r1, gr1, j', hgr1, hand, Or.inr (by rw [hin, ← h]), hrr'⟩
          · exact ⟨true, pq2i_st_or_true (N + 1) gs L.hcl q2 true r1 gr1 hgr1 hor (N + 2 + o2) hmem hstO2⟩
      obtain ⟨r2, hlt, -, hrc⟩ := L.next q2 true hnc1 r1 (List.getElem?_eq_some_iff.1 hgr1).1 hisC
      exact ⟨r2, hrc, by omega, by omega⟩
  have hor1 : o2 ≠ r1 := by omega
  have hor2 : o2 ≠ r2 := by omega
  -- the gate `o2` is not a gate of shape (i)
  have hM1 : ∀ (p : ℕ) (g : Gate), gs[p]? = some g → (q1 : ℕ) ∈ g.inputs → o2 ≠ p := by
    intro p g hg hq e
    subst e
    rw [hgo2] at hg; cases hg
    exact pq2i_M1 N G q0 q1 q2 q3 q4 q5 r gs o L hnc1 o2 go2 hgo2 hoo2 hq h2in hrq2
  have hq1mem1 : (q1 : ℕ) ∈ g1.inputs := by rcases hu1 with h | h <;> rw [h] <;> simp
  have hq1mem2 : (q1 : ℕ) ∈ g2.inputs := by rcases hu2 with h | h <;> rw [h] <;> simp
  have hop21 := hM1 p1 g1 hg1 hq1mem1
  have hop22 := hM1 p2 g2 hg2 hq1mem2
  by_cases hR1 : RC (N + 1) gs q2 true p1
  · exact pq2j_rc_case N G q0 q1 q2 q3 q4 q5 r gs o L hnc1 hall3 j hj o2 go2 hgo2 hoo2 h2in hrq2
      hstO2 r1 r2 hrc1 hrc2 hor1 hor2 hr12 p1 g1 u1 hg1 ho1 hu1 a1 ga1 w1 hpa1 hga1 hao1 hai1
      p2 g2 u2 hg2 ho2 hu2 h12 hop21 hop22 hR1
  by_cases hR2 : RC (N + 1) gs q2 true p2
  · exact pq2j_rc_case N G q0 q1 q2 q3 q4 q5 r gs o L hnc1 hall3 j hj o2 go2 hgo2 hoo2 h2in hrq2
      hstO2 r1 r2 hrc1 hrc2 hor1 hor2 hr12 p2 g2 u2 hg2 ho2 hu2 a2 ga2 w2 hpa2 hga2 hao2 hai2
      p1 g1 u1 hg1 ho1 hu1 h12.symm hop22 hop21 hR2
  refine pq2j_fin N G q0 q1 q2 q3 q4 q5 r gs o L hnc1 j hj o2 r1 r2 hRo2 hrc1 hrc2 hor1 hor2 hr12
    (pq2E (N + 1) gs q2 true p1) (pq2E (N + 1) gs q2 true p2) ?_ ?_ ?_
  · exact pq2i_E_ne (N + 1) gs L.hcl q2 true p1 p2 g1 g2 hg1 hg2 hR1 hR2 (Or.inr ho1) (Or.inr ho2) h12
  · rcases hu1 with h | h
    · exact pq2i_rc_pass N gs L.hcl q2 true p1 g1 hg1 hR1 (Or.inr ho1) _ _ h j (Or.inl hq1) false
    · exact pq2i_rc_pass N gs L.hcl q2 true p1 g1 hg1 hR1 (Or.inr ho1) _ _ h j (Or.inr hq1) false
  · rcases hu2 with h | h
    · exact pq2i_rc_pass N gs L.hcl q2 true p2 g2 hg2 hR2 (Or.inr ho2) _ _ h j (Or.inl hq1) false
    · exact pq2i_rc_pass N gs L.hcl q2 true p2 g2 hg2 hR2 (Or.inr ho2) _ _ h j (Or.inr hq1) false

/-- `AsmPQ2`: the last piece of the run-of-four assembly, from `Pq2hBeta` proved above. -/
theorem pq2_main : AsmPQ2 := pq2h_main_of_beta pq2i_beta

end PEqualNP.MetaComplexity.Helpers.RunAsm
