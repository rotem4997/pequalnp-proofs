import PEqualNP.MetaComplexity.Helpers.RunQASqueeze

/-!
# Theorem QA, step C3 (started): bricks for the cases

* `qa_or_chain_ge`: along a chain of OR gates, each listing the previous one (the first listing
  a wire `w`), every chain gate is true wherever `w` is true. Case A of the paper: a literal
  chain from `x_q3` to the output makes the output at least `x_q3`.
* `qa_L_gate`: every gate of `qaL` is a kept gate of `C` with its listed wires normalized and
  mapped by `qaRho`, at the position `cnt S q`.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunFour2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Loc.Removal

theorem qa_or_chain_ge (N : ℕ) (C : Circuit) (k : ℕ) (p : Fin (k + 1) → Fin C.gates.length)
    (w : ℕ) (x : Fin N → Bool)
    (hop : ∀ i, (C.gates.get (p i)).op = GateOp.or)
    (h0 : w ∈ (C.gates.get (p 0)).inputs) (hw : w < N + (p 0).val)
    (hstep : ∀ i : Fin k, N + (p i.castSucc).val ∈ (C.gates.get (p i.succ)).inputs ∧
      p i.castSucc < p i.succ)
    (hwx : (wiresFrom C.gates (List.ofFn x)).getD w false = true) :
    ∀ i, (wiresFrom C.gates (List.ofFn x)).getD (N + (p i).val) false = true := by
  intro i
  induction i using Fin.induction with
  | zero =>
    rw [qa_val_fin N C x (p 0)]
    exact qa_or_true _ _ (hop 0) w h0 (by rw [if_pos hw]; exact hwx)
  | succ i ih =>
    rw [qa_val_fin N C x (p i.succ)]
    obtain ⟨hm, hlt⟩ := hstep i
    have hlt' : N + (p i.castSucc).val < N + (p i.succ).val := by
      have : (p i.castSucc).val < (p i.succ).val := hlt
      omega
    exact qa_or_true _ _ (hop i.succ) _ hm (by rw [if_pos hlt']; exact ih)

theorem qa_L_gate (N : ℕ) (C : Circuit) (g1 g2 o2 jM u1 u2 z : ℕ) (k : ℕ) (g : Gate)
    (hk : (qaL N C g1 g2 o2 jM u1 u2 z).gates[k]? = some g) :
    ∃ q, q < C.gates.length ∧ q ∉ qaS g1 g2 o2 jM ∧ cnt (qaS g1 g2 o2 jM) q = k ∧
      g = ⟨(C.gates.getD q g0).op, (C.gates.getD q g0).inputs.map fun i =>
        qaRho N (qaS g1 g2 o2 jM) (qaTgt g1 g2 jM u1 u2 z)
          (N + cnt (qaS g1 g2 o2 jM) C.gates.length)
          (if i < N + q then i else N + C.gates.length)⟩ := by
  obtain ⟨q, hq, hqS, hc, rfl⟩ := mem_build _ _ _ _ k g hk
  refine ⟨q, hq, hqS, hc, ?_⟩
  rw [qaNorm_getD _ _ q hq]
  simp [rg]

/-- Kept gates are ordered as their new positions. -/
theorem qa_cnt_lt {S : Finset ℕ} {q r : ℕ} (hq : q ∉ S) (h : cnt S q < cnt S r) : q < r := by
  by_contra h'
  push_neg at h'
  have := cnt_mono S h'
  omega

theorem qa_cnt_inj {S : Finset ℕ} {q r : ℕ} (hq : q ∉ S) (hr : r ∉ S) (h : cnt S q = cnt S r) :
    q = r := by
  rcases lt_trichotomy q r with h1 | h1 | h1
  · have := cnt_mono S (show q + 1 ≤ r by omega); rw [cnt_succ_keep S hq] at this; omega
  · exact h1
  · have := cnt_mono S (show r + 1 ≤ q by omega); rw [cnt_succ_keep S hr] at this; omega

/-- Case A of the paper: if the FP chain of `qaL` does not pass through the image of `M`, the
chain lifts to a literal OR chain of `C` from `x_q3` to the output, and `F(1_q3) = 1`:
contradiction. -/
theorem qa_caseA (n : ℕ) (C : Circuit) (F : (Fin (n + 1) → Bool) → Bool) (e : Fin (n + 1))
    (g1 g2 a1 a2 o2 jM : Fin C.gates.length) (u1 u2 z : ℕ)
    (ho1 : o2 ≠ g1) (ho2 : o2 ≠ g2) (hoM : o2 ≠ jM)
    (hCF : ∀ x, circuitFun (n + 1) C x = F x)
    (hp0 : F (fun i : Fin (n + 1) => decide (i = Fin.last n)) = false)
    (hpe : F (fun i : Fin (n + 1) => decide (i = e)) = false)
    (hg1 : (C.gates.get g1).op = GateOp.or ∧ e.val ∈ (C.gates.get g1).inputs)
    (hg2 : (C.gates.get g2).op = GateOp.or ∧ e.val ∈ (C.gates.get g2).inputs)
    (ha1 : (C.gates.get a1).op = GateOp.and) (ha2 : (C.gates.get a2).op = GateOp.and)
    (hr1 : ∀ j : Fin C.gates.length, g1 < j → qaReads (C.gates.get j) (n + 1 + g1.val) → j = a1)
    (hr2 : ∀ j : Fin C.gates.length, g2 < j → qaReads (C.gates.get j) (n + 1 + g2.val) → j = a2)
    (k : ℕ) (c : Fin (k + 1) → Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length)
    (hc : StrictMono c)
    (hout : (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).output = n + 1 + (c (Fin.last k)).val)
    (hcop : ∀ i, ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get (c i)).op = GateOp.or)
    (hc0 : n ∈ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get (c 0)).inputs)
    (hcs : ∀ i : Fin k, n + 1 + (c i.castSucc).val ∈
      ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get (c i.succ)).inputs)
    (hA : ∀ v, (v = n ∨ ∃ i, v = n + 1 + (c i).val) →
      qaRho (n + 1) (qaS g1 g2 o2 jM) (qaTgt g1 g2 jM u1 u2 z)
        (n + 1 + cnt (qaS g1 g2 o2 jM) C.gates.length) (n + 1 + jM.val) ≠ v) :
    False := by
  set S := qaS g1.val g2.val o2.val jM.val with hS
  set tgt := qaTgt g1.val g2.val jM.val u1 u2 z with htgt
  set d := n + 1 + cnt S C.gates.length with hd
  have hvne : ∀ a b : Fin C.gates.length, a ≠ b → a.val ≠ b.val := fun a b h h' => h (Fin.ext h')
  have hmemS : ∀ p, p ∈ S ↔ p = g1.val ∨ p = g2.val ∨ p = o2.val ∨ p = jM.val := by
    intro p; simp [hS, qaS]
  have hLlen : (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length = cnt S C.gates.length := len_build _ _ _ _
  have hto : tgt o2.val = none := by
    simp [htgt, qaTgt, hvne _ _ ho1, hvne _ _ ho2, hvne _ _ hoM]
  -- lift every chain gate
  have hlift : ∀ i, ∃ q, q < C.gates.length ∧ q ∉ S ∧ cnt S q = (c i).val ∧
      (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get (c i) = ⟨(C.gates.getD q g0).op, (C.gates.getD q g0).inputs.map fun a =>
        qaRho (n + 1) S tgt d (if a < n + 1 + q then a else n + 1 + C.gates.length)⟩ := by
    intro i
    exact qa_L_gate (n + 1) C g1 g2 o2 jM u1 u2 z (c i) _
      (by rw [List.getElem?_eq_getElem (c i).isLt]; rfl)
  choose q hq hqS hqc hqg using hlift
  have hqop : ∀ i, (C.gates.getD (q i) g0).op = GateOp.or := by
    intro i; have := hcop i; rw [hqg i] at this; exact this
  have hget : ∀ i, C.gates.getD (q i) g0 = C.gates.get ⟨q i, hq i⟩ := by
    intro i; simp [List.getD_eq_getElem?_getD, hq i]
  -- the image of the fallback is past every chain wire
  have hdT : ∀ v, (v = n ∨ ∃ i, v = n + 1 + (c i).val) → v < d := by
    rintro v (rfl | ⟨i, rfl⟩)
    · omega
    · have := (c i).isLt; have h2 := hLlen; omega
  -- operand classification
  have hcls : ∀ i v, (v = n ∨ ∃ j, v = n + 1 + (c j).val) →
      v ∈ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get (c i)).inputs →
      ∃ a ∈ (C.gates.get ⟨q i, hq i⟩).inputs, a < n + 1 + q i ∧
        ((v = n ∧ a = n) ∨ ∃ j, v = n + 1 + (c j).val ∧ a = n + 1 + q j) := by
    intro i v hv hmem
    rw [hqg i] at hmem
    obtain ⟨a, ha, hav⟩ := List.mem_map.1 hmem
    rw [hget i] at ha
    refine ⟨a, ha, ?_⟩
    have hvd := hdT v hv
    have hbig : qaRho (n + 1) S tgt d (n + 1 + C.gates.length) = d := by
      have : C.gates.length ∉ S := by
        intro h; rw [hmemS] at h
        rcases h with h | h | h | h <;> omega
      rw [qaRho_keep (n + 1) S tgt d this]
    by_cases hlt : a < n + 1 + q i
    · rw [if_pos hlt] at hav
      refine ⟨hlt, ?_⟩
      by_cases ha1' : a < n + 1
      · rw [qaRho_lt (n + 1) S tgt d ha1'] at hav
        subst hav
        rcases hv with h | ⟨j, h⟩
        · exact Or.inl ⟨h, h⟩
        · omega
      obtain ⟨r, rfl⟩ : ∃ r, a = n + 1 + r := ⟨a - (n + 1), by omega⟩
      have hrl : r < C.gates.length := by have := hq i; omega
      by_cases hrS : r ∈ S
      · exfalso
        rcases (hmemS r).1 hrS with h | h | h | h
        · -- r = g1: gate q i reads g1, so it is a1, an AND
          have hgt : g1 < (⟨q i, hq i⟩ : Fin C.gates.length) := by
            show g1.val < q i; omega
          have hrd := hr1 ⟨q i, hq i⟩ hgt
            (Or.inr ⟨by rw [← hget i, hqop i]; exact fun hh => GateOp.noConfusion hh,
              by rw [← h]; exact ha⟩)
          have := hqop i; rw [hget i, hrd, ha1] at this; cases this
        · have hgt : g2 < (⟨q i, hq i⟩ : Fin C.gates.length) := by
            show g2.val < q i; omega
          have hrd := hr2 ⟨q i, hq i⟩ hgt
            (Or.inr ⟨by rw [← hget i, hqop i]; exact fun hh => GateOp.noConfusion hh,
              by rw [← h]; exact ha⟩)
          have := hqop i; rw [hget i, hrd, ha2] at this; cases this
        · subst h
          rw [qaRho_none (n + 1) S tgt d hrS hto] at hav; omega
        · subst h
          exact hA v hv hav
      · rw [qaRho_keep (n + 1) S tgt d hrS] at hav
        rcases hv with h | ⟨j, h⟩
        · omega
        · right
          refine ⟨j, h, ?_⟩
          have hcj : cnt S r = cnt S (q j) := by rw [hqc j]; omega
          rw [qa_cnt_inj hrS (hqS j) hcj]
    · rw [if_neg hlt, hbig] at hav; omega
  -- the chain in C
  have hPop : ∀ i, (C.gates.get ⟨q i, hq i⟩).op = GateOp.or := fun i => by
    rw [← hget i]; exact hqop i
  have hP0 : n ∈ (C.gates.get ⟨q 0, hq 0⟩).inputs ∧ n < n + 1 + q 0 := by
    obtain ⟨a, ha, hlt, hcase⟩ := hcls 0 n (Or.inl rfl) hc0
    rcases hcase with ⟨_, rfl⟩ | ⟨j, hj, _⟩
    · exact ⟨ha, by omega⟩
    · omega
  have hPs : ∀ i : Fin k, n + 1 + q i.castSucc ∈ (C.gates.get ⟨q i.succ, hq i.succ⟩).inputs ∧
      (⟨q i.castSucc, hq i.castSucc⟩ : Fin C.gates.length) < ⟨q i.succ, hq i.succ⟩ := by
    intro i
    obtain ⟨a, ha, _, hcase⟩ := hcls i.succ (n + 1 + (c i.castSucc).val)
      (Or.inr ⟨_, rfl⟩) (hcs i)
    rcases hcase with ⟨h, _⟩ | ⟨j, hj, rfl⟩
    · omega
    · have hcj : c j = c i.castSucc := Fin.ext (by omega)
      have hji : j = i.castSucc := hc.injective hcj
      subst hji
      refine ⟨ha, ?_⟩
      show q i.castSucc < q i.succ
      apply qa_cnt_lt (hqS _)
      rw [hqc, hqc]
      exact hc (Fin.castSucc_lt_succ (i := i))
  -- the output of C is the top of the chain
  have hO : qaRho (n + 1) S tgt d C.output = n + 1 + (c (Fin.last k)).val := hout
  have hclt : (c (Fin.last k)).val < cnt S C.gates.length := by
    have := (c (Fin.last k)).isLt; have h2 := hLlen; omega
  have hOq : C.output = n + 1 + q (Fin.last k) := by
    by_cases h1 : C.output < n + 1
    · rw [qaRho_lt (n + 1) S tgt d h1] at hO; omega
    obtain ⟨r, hr⟩ : ∃ r, C.output = n + 1 + r := ⟨C.output - (n + 1), by omega⟩
    rw [hr] at hO ⊢
    by_cases hrS : r ∈ S
    · exfalso
      have hrl : r < C.gates.length := by
        rcases (hmemS r).1 hrS with h | h | h | h <;> rw [h] <;> exact Fin.isLt _
      have hor : ∀ g : Fin C.gates.length, r = g.val → (C.gates.get g).op = GateOp.or →
          e.val ∈ (C.gates.get g).inputs → False := by
        intro g hg hop he
        have h1e := hCF (fun i : Fin (n + 1) => decide (i = e))
        rw [hpe] at h1e
        revert h1e
        show (C.wires _).getD C.output false = false → False
        rw [wires_eq, hr, hg, qa_val_fin (n + 1) C _ g,
          qa_or_true _ _ hop e.val he (by
            rw [if_pos (by have := e.isLt; omega),
              getD_wiresFrom _ _ _ (by rw [List.length_ofFn]; exact e.isLt),
              qa_ofFn_getD _ _ e.isLt]
            simp)]
        simp
      rcases (hmemS r).1 hrS with h | h | h | h
      · exact hor g1 h hg1.1 hg1.2
      · exact hor g2 h hg2.1 hg2.2
      · rw [h, qaRho_none (n + 1) S tgt d (h ▸ hrS) hto] at hO; omega
      · rw [h] at hO; exact hA _ (Or.inr ⟨_, rfl⟩) hO
    · rw [qaRho_keep (n + 1) S tgt d hrS] at hO
      by_cases hrl : r < C.gates.length
      · have := qa_cnt_inj hrS (hqS (Fin.last k)) (by rw [hqc]; omega)
        rw [this]
      · have := cnt_mono S (show C.gates.length ≤ r by omega); omega
  -- F at 1_q3 is true: contradiction
  have hchain := qa_or_chain_ge (n + 1) C k (fun i => ⟨q i, hq i⟩) n
    (fun i : Fin (n + 1) => decide (i = Fin.last n)) hPop hP0.1 hP0.2 hPs
    (by
      rw [getD_wiresFrom _ _ _ (by rw [List.length_ofFn]; omega),
        qa_ofFn_getD _ _ (by omega)]
      simp [Fin.ext_iff]) (Fin.last k)
  have h1q := hCF (fun i : Fin (n + 1) => decide (i = Fin.last n))
  rw [hp0] at h1q
  revert h1q
  show (C.wires _).getD C.output false = false → False
  rw [wires_eq, hOq]
  simp only at hchain
  rw [hchain]
  simp

/-- The fifth gate, cases B1 and B2 (OPEN): under every hypothesis of the row, with `qaL`
minimal and its FP chain `c`, the image of `M` is `x_q3` or a chain wire. Then: False. -/
def qaGapB : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (H : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (e q2 q4 : Fin (n + 1)) (g1 g2 a1 a2 o2 jM : Fin C.gates.length) (u1 u2 w1 w2 W2 z : ℕ), (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w)) → (e ≠ q2 ∧ e ≠ q4 ∧ q2 ≠ q4 ∧ e ≠ (Fin.last n) ∧ q2 ≠ (Fin.last n) ∧ q4 ≠ (Fin.last n)) → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, F (Function.update (Function.update x q2 true) e false) = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → F (fun i : Fin (n + 1) => decide (i = (Fin.last n))) = false → F (fun i : Fin (n + 1) => decide (i = (Fin.last n) ∨ i = q2)) = true → F (fun i : Fin (n + 1) => decide (i = e)) = false → F (fun i : Fin (n + 1) => decide (i = e ∨ i = q2)) = true → F (fun i : Fin (n + 1) => decide (i = e ∨ i = q4)) = false → F (fun i : Fin (n + 1) => decide (i = e ∨ i = q4 ∨ i = q2)) = true → F (fun i : Fin (n + 1) => decide (i = e ∨ i = q4 ∨ i = (Fin.last n))) = true → PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = F x) → (g1 ≠ g2 ∧ a1 ≠ a2 ∧ g1 < a1 ∧ g2 < a2) → ((C.gates.get g1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get g1).inputs.length = 2 ∧ (e.val) ∈ (C.gates.get g1).inputs ∧ (u1) ∈ (C.gates.get g1).inputs ∧ (e.val) ≠ (u1)) → ((C.gates.get g2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get g2).inputs.length = 2 ∧ (e.val) ∈ (C.gates.get g2).inputs ∧ (u2) ∈ (C.gates.get g2).inputs ∧ (e.val) ≠ (u2)) → (∀ j : Fin C.gates.length, True → (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (e.val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (e.val) ∈ (C.gates.get j).inputs)) → j = g1 ∨ j = g2) → ((C.gates.get a1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (C.gates.get a1).inputs.length = 2 ∧ (n + 1 + g1.val) ∈ (C.gates.get a1).inputs ∧ (w1) ∈ (C.gates.get a1).inputs ∧ (n + 1 + g1.val) ≠ (w1)) → ((C.gates.get a2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (C.gates.get a2).inputs.length = 2 ∧ (n + 1 + g2.val) ∈ (C.gates.get a2).inputs ∧ (w2) ∈ (C.gates.get a2).inputs ∧ (n + 1 + g2.val) ≠ (w2)) → (∀ j : Fin C.gates.length, g1 < j → (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + g1.val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + g1.val) ∈ (C.gates.get j).inputs)) → j = a1) → (∀ j : Fin C.gates.length, g2 < j → (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + g2.val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + g2.val) ∈ (C.gates.get j).inputs)) → j = a2) → (u1 < n + 1 ∨ ∃ j : Fin C.gates.length, j ≠ g1 ∧ u1 < n + 1 + j.val ∧ (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (u1) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (u1) ∈ (C.gates.get j).inputs))) → (u2 < n + 1 ∨ ∃ j : Fin C.gates.length, j ≠ g2 ∧ u2 < n + 1 + j.val ∧ (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (u2) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (u2) ∈ (C.gates.get j).inputs))) → o2 < jM → (o2 ≠ g1 ∧ o2 ≠ g2) → ((C.gates.get o2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get o2).inputs.length = 2 ∧ (q2.val) ∈ (C.gates.get o2).inputs ∧ (W2) ∈ (C.gates.get o2).inputs ∧ (q2.val) ≠ (W2)) → (∀ j : Fin C.gates.length, True → (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (q2.val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (q2.val) ∈ (C.gates.get j).inputs)) → j = o2) → ((C.gates.get jM).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (C.gates.get jM).inputs.length = 2 ∧ (n + 1 + o2.val) ∈ (C.gates.get jM).inputs ∧ (z) ∈ (C.gates.get jM).inputs ∧ (n + 1 + o2.val) ≠ (z)) → (∀ j : Fin C.gates.length, o2 < j → (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + o2.val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + o2.val) ∈ (C.gates.get j).inputs)) → j = jM) → PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) (qaL (n + 1) C g1 g2 o2 jM u1 u2 z) → ∀ (k : ℕ) (c : Fin (k + 1) → Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length), (StrictMono c ∧ (c (Fin.last k)).val + 1 = (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length ∧ (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get (c i)).inputs.length = 2) ∧ n ∈ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get (c i.succ)).inputs) ∧ (∀ j : Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length, (((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).inputs.head? = some n ∨ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length), (((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length, b = n + 1 + j.val ∧ (((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).inputs.head? = some a ∨ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length, b = n + 1 + j.val ∧ (((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).inputs.head? = some a ∨ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin (qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.length, b = n + 1 + j.val ∧ (((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).inputs.head? = some a ∨ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ ((qaL (n + 1) C g1 g2 o2 jM u1 u2 z).gates.get j).inputs)) n w)) → (∃ v : ℕ, (v = n ∨ ∃ i : Fin (k + 1), v = n + 1 + (c i).val) ∧ qaRho (n + 1) (qaS g1 g2 o2 jM) (qaTgt g1 g2 jM u1 u2 z) (n + 1 + cnt (qaS g1 g2 o2 jM) C.gates.length) (n + 1 + jM.val) = v) → False

/-- Case A closes the rest: the fifth-gate step follows from the B cases. -/
theorem qa_gapC3_of_gapB (hB : qaGapB) : qaGapC3 := by
  intro n F H C e q2 q4 g1 g2 a1 a2 o2 jM u1 u2 w1 w2 W2 z hFP hdist hH hF p1 p2 p3 p4 p5 p6 p7
    hmin hCF hga hg1 hg2 hre ha1 ha2 hr1 hr2 hu1 hu2 hoM hog ho hrq hM hro hLmin
  set G := fun x : Fin (n + 1) → Bool => x (Fin.last n) || H (fun i : Fin n => x i.castSucc)
    with hGdef
  have hG : ∀ x, circuitFun (n + 1) C (Function.update (Function.update x q2 true) e false) =
      G x := fun x => by rw [hCF]; exact hF x
  have hnc : ∃ y y' : Fin (n + 1) → Bool, G y ≠ G y' := by
    obtain ⟨y, y', h⟩ := hH
    refine ⟨Fin.snoc y false, Fin.snoc y' false, ?_⟩
    simpa [hGdef] using h
  obtain ⟨_, _, hLe⟩ := qa_remove n C hmin.1 e q2 g1 g2 o2 jM u1 u2 z hdist.1 hga.1 hog.1
    hog.2 hoM hg1 hg2 (fun j hj => hre j trivial hj) ⟨ho.1, ho.2.2.1⟩
    (fun j hj => hrq j trivial hj) hM hro G hG hnc
  obtain ⟨k, c, hchain⟩ := hFP n (qaL (n + 1) C g1 g2 o2 jM u1 u2 z) H hLmin hH
    (fun x => hLe x)
  by_cases hT : ∃ v : ℕ, (v = n ∨ ∃ i : Fin (k + 1), v = n + 1 + (c i).val) ∧
      qaRho (n + 1) (qaS g1 g2 o2 jM) (qaTgt g1 g2 jM u1 u2 z)
        (n + 1 + cnt (qaS g1 g2 o2 jM) C.gates.length) (n + 1 + jM.val) = v
  · exact hB n F H C e q2 q4 g1 g2 a1 a2 o2 jM u1 u2 w1 w2 W2 z hFP hdist hH hF p1 p2 p3 p4 p5
      p6 p7 hmin hCF hga hg1 hg2 hre ha1 ha2 hr1 hr2 hu1 hu2 hoM hog ho hrq hM hro hLmin k c
      hchain hT
  · obtain ⟨hcm, _, hcout, hcop, hc0, hcs, _⟩ := hchain
    exact qa_caseA n C F e g1 g2 a1 a2 o2 jM u1 u2 z hog.1 hog.2 (ne_of_lt hoM) hCF p1 p3
      ⟨hg1.1, hg1.2.2.1⟩ ⟨hg2.1, hg2.2.2.1⟩ ha1.1 ha2.1 hr1 hr2 k c hcm hcout
      (fun i => (hcop i).1) hc0 hcs (fun v hv hv' => hT ⟨v, hv, hv'⟩)

/-- A brick for the B cases (paper: "z is not x_q3", tool W on M): wire `z` is true at `1_e`,
so it is not the input `x_q3`. -/
theorem qa_z_at_e (n : ℕ) (C : Circuit) (F : (Fin (n + 1) → Bool) → Bool) (e q2 : Fin (n + 1))
    (o2 jM : Fin C.gates.length) (z : ℕ) (heq : e ≠ q2) (helast : e ≠ Fin.last n)
    (hoM : o2 < jM)
    (hCF : ∀ x, circuitFun (n + 1) C x = F x)
    (hp3 : F (fun i : Fin (n + 1) => decide (i = e)) = false)
    (hp4 : F (fun i : Fin (n + 1) => decide (i = e ∨ i = q2)) = true)
    (hrq : ∀ j : Fin C.gates.length, qaReads (C.gates.get j) q2.val → j = o2)
    (hM : (C.gates.get jM).op = GateOp.and ∧ n + 1 + o2.val ∈ (C.gates.get jM).inputs ∧
      z ∈ (C.gates.get jM).inputs ∧ n + 1 + o2.val ≠ z)
    (hzlt : z < n + 1 + jM.val)
    (hro : ∀ j : Fin C.gates.length, o2 < j → qaReads (C.gates.get j) (n + 1 + o2.val) →
      j = jM)
    (hout : C.output ≠ q2.val) (hout' : C.output ≠ n + 1 + o2.val) :
    (wiresFrom C.gates (List.ofFn (fun i : Fin (n + 1) => decide (i = e)))).getD z false = true ∧
      z ≠ n := by
  have hz := qa_toolW_or_and (n + 1) C q2 o2 jM z hoM hM.1 hM.2.1 hM.2.2.1
    (Ne.symm hM.2.2.2) hzlt hrq hro hout hout' (fun i : Fin (n + 1) => decide (i = e)) (by
      have hup : Function.update (fun i : Fin (n + 1) => decide (i = e)) q2
          (!decide (q2 = e)) = fun i : Fin (n + 1) => decide (i = e ∨ i = q2) := by
        funext i
        by_cases hi : i = q2
        · subst hi; simp [Ne.symm heq]
        · simp [Function.update_of_ne hi, hi]
      rw [hup, hCF, hCF, hp3, hp4]; simp)
  refine ⟨hz, ?_⟩
  intro hzn
  rw [hzn, wires_eq, getD_wiresFrom _ _ _ (by rw [List.length_ofFn]; omega),
    qa_ofFn_getD _ _ (by omega)] at hz
  have he : (⟨n, by omega⟩ : Fin (n + 1)) ≠ e := by
    intro h; apply helast; rw [← h]; rfl
  simp [he] at hz

end PEqualNP.MetaComplexity.Helpers.RunFour2
