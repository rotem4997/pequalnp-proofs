import PEqualNP.MetaComplexity.Helpers.RunNL2

/-!
# Theorem NL, part 3: the removed list computes the restriction

`nlState` collects the NOT state at input `ev` (gates `pn`, `pm`, `pS`), `nlRSpec` the removal set.
At every input list `X'` with `x_ev = 1`, the NOT gate and the AND gate are `false` and the OR
gate `pS` equals its other operand (or `false`). A kept gate of the new list has the value of its
old gate at `X'`, read on any input list `X` agreeing with `X'` off `ev`.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunNL

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The NOT state at input `ev`. -/
structure nlState (n : ℕ) (gs : List Gate) (ev pn pm pS : ℕ) : Prop where
  fan : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2
  ev_lt : ev < n + 1
  pn_lt : pn < gs.length
  pm_lt : pm < gs.length
  pS_lt : pS < gs.length
  n_op : (gs.getD pn nlG0).op = GateOp.not
  n_hd : (gs.getD pn nlG0).inputs.head? = some ev
  m_op : (gs.getD pm nlG0).op = GateOp.and
  m_in : n + 1 + pn ∈ (gs.getD pm nlG0).inputs
  S_op : (gs.getD pS nlG0).op = GateOp.or
  S_in : n + 1 + pm ∈ (gs.getD pS nlG0).inputs
  rd_e : ∀ j, j < gs.length → nlRel (gs.getD j nlG0) ev → j = pn
  rd_n : ∀ j, j < gs.length → nlRel (gs.getD j nlG0) (n + 1 + pn) → j = pm
  rd_m : ∀ j, j < gs.length → nlRel (gs.getD j nlG0) (n + 1 + pm) → j = pS

/-- The removal set: gates of the list, each `pn`, `pm`, `pS` or a gate read only by `pm`. -/
def nlRSpec (n : ℕ) (gs : List Gate) (pn pm pS : ℕ) (R : Finset ℕ) : Prop :=
  ∀ j ∈ R, j < gs.length ∧ (j = pn ∨ j = pm ∨ j = pS ∨
    ∀ q, q < gs.length → nlRel (gs.getD q nlG0) (n + 1 + j) → q = pm)

section
variable {n : ℕ} {gs : List Gate} {ev pn pm pS : ℕ}

theorem nlState.len_le (hN : nlState n gs ev pn pm pS) (p : ℕ) :
    (gs.getD p nlG0).inputs.length ≤ 2 := by
  by_cases hp : p < gs.length
  · rw [nl_getD hp]; exact (hN.fan _ (List.getElem_mem hp)).2
  · rw [List.getD_eq_default _ _ (by omega)]; simp [nlG0]

theorem nlState.nm (hN : nlState n gs ev pn pm pS) : pn ≠ pm := by
  intro h; have := hN.n_op; rw [h, hN.m_op] at this; cases this

theorem nlState.mS (hN : nlState n gs ev pn pm pS) : pm ≠ pS := by
  intro h; have := hN.m_op; rw [h, hN.S_op] at this; cases this

theorem nlState.nS (hN : nlState n gs ev pn pm pS) : pn ≠ pS := by
  intro h; have := hN.n_op; rw [h, hN.S_op] at this; cases this

theorem nlState.rS (hN : nlState n gs ev pn pm pS) (a : ℕ)
    (ha : a ∈ (gs.getD pS nlG0).inputs) : nlRel (gs.getD pS nlG0) a :=
  Or.inr ⟨by rw [hN.S_op]; simp, ha⟩

/-- The other operand `s` of the OR gate is an input other than `ev` or a kept gate. -/
theorem nlState.s_facts (hN : nlState n gs ev pn pm pS) {R : Finset ℕ}
    (hR : nlRSpec n gs pn pm pS R) {s : ℕ} (hs : nlSo n gs pm pS = some s) :
    s ≠ ev ∧ s < n + 1 + pS ∧ (n + 1 ≤ s → s - (n + 1) ∉ R) := by
  obtain ⟨h1, h2, h3⟩ := nlSo_spec n gs pm pS s hs
  refine ⟨?_, h3, ?_⟩
  · intro he; subst he
    exact hN.nS (hN.rd_e pS hN.pS_lt (hN.rS _ h1)).symm
  · intro hle hR'
    obtain ⟨_, hj⟩ := hR _ hR'
    have hs' : s = n + 1 + (s - (n + 1)) := by omega
    rcases hj with hj | hj | hj | hj
    · rw [hj] at hs'
      have := hN.rd_n pS hN.pS_lt (hs' ▸ hN.rS _ h1)
      exact hN.mS this.symm
    · rw [hj] at hs'; exact h2 hs'
    · omega
    · have := hj pS hN.pS_lt (hs' ▸ hN.rS _ h1)
      exact hN.mS this.symm

/-! ## Values at a point with `x_ev = 1` -/

theorem nlState.vn (hN : nlState n gs ev pn pm pS) (X : List Bool) (hX : X.length = n + 1)
    (he : X.getD ev false = true) : nlV gs X (n + 1 + pn) = false := by
  have h := nl_not_val gs X pn hN.pn_lt (by rw [← nl_getD hN.pn_lt]; exact hN.n_op) ev
    (by rw [← nl_getD hN.pn_lt]; exact hN.n_hd) (by have := hN.ev_lt; omega)
  rw [hX] at h
  rw [h, nlV_input _ _ _ (by rw [hX]; exact hN.ev_lt), he]; rfl

theorem nlState.vm (hN : nlState n gs ev pn pm pS) (X : List Bool) (hX : X.length = n + 1)
    (he : X.getD ev false = true) : nlV gs X (n + 1 + pm) = false := by
  have h := nl_and_false gs X pm hN.pm_lt (by rw [← nl_getD hN.pm_lt]; exact hN.m_op)
    (n + 1 + pn) (by rw [← nl_getD hN.pm_lt]; exact hN.m_in) (fun _ => hN.vn X hX he)
  rw [hX] at h; exact h

/-- The OR gate `pS` equals its other operand when its read of `pm` is `false`. -/
theorem nlState.vS (hN : nlState n gs ev pn pm pS) (X : List Bool) (hX : X.length = n + 1)
    (hrm : nlRd gs X pS (n + 1 + pm) = false) :
    nlV gs X (n + 1 + pS) = (match nlSo n gs pm pS with
      | some s => nlV gs X s
      | none => false) := by
  have hg := nlV_gate' gs X pS hN.pS_lt
  rw [hX, ← nl_getD hN.pS_lt, hN.S_op] at hg
  rw [hg]
  simp only [GateOp.eval]
  have hl := hN.len_le pS
  cases hso : nlSo n gs pm pS with
  | none =>
    simp only
    rw [Bool.eq_false_iff]
    intro hany
    rw [List.any_eq_true] at hany
    obtain ⟨b, hb, hbt⟩ := hany
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    by_cases ham : a = n + 1 + pm
    · subst ham; rw [hrm] at hbt; cases hbt
    · unfold nlRd at hbt
      rw [hX] at hbt
      by_cases hal : a < n + 1 + pS
      · rw [nlSo_of n gs pm pS hl hN.S_in a ha ham hal] at hso; cases hso
      · simp [hal] at hbt
  | some s =>
    simp only
    obtain ⟨k1, k2, k3⟩ := nlSo_spec n gs pm pS s hso
    cases hv : nlV gs X s with
    | true =>
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.2 ⟨s, k1, by unfold nlRd; rw [hX, if_pos k3, hv]⟩, rfl⟩
    | false =>
      rw [Bool.eq_false_iff]
      intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨b, hb, hbt⟩ := hany
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
      by_cases ham : a = n + 1 + pm
      · subst ham; rw [hrm] at hbt; cases hbt
      · unfold nlRd at hbt
        rw [hX] at hbt
        by_cases hal : a < n + 1 + pS
        · have := nlSo_of n gs pm pS hl hN.S_in a ha ham hal
          rw [hso] at this
          cases this
          simp [hal, hv] at hbt
        · simp [hal] at hbt

theorem nlState.vS1 (hN : nlState n gs ev pn pm pS) (X : List Bool) (hX : X.length = n + 1)
    (he : X.getD ev false = true) :
    nlV gs X (n + 1 + pS) = (match nlSo n gs pm pS with
      | some s => nlV gs X s
      | none => false) := by
  apply hN.vS X hX
  unfold nlRd
  rw [hX]
  split_ifs
  · exact hN.vm X hX he
  · rfl

end

/-! ## The new list computes the restriction -/

section Values
variable {n : ℕ} {gs : List Gate} {ev pn pm pS : ℕ} {R : Finset ℕ} (o : ℕ)
  (hN : nlState n gs ev pn pm pS) (hR : nlRSpec n gs pn pm pS R)
  (X X' : List Bool) (hX : X.length = n + 1) (hX' : X'.length = n + 1)
  (he : X'.getD ev false = true)
  (hag : ∀ i, i < n + 1 → i ≠ ev → X.getD i false = X'.getD i false)
include hN hR hX hX' he hag

theorem nl_readEq (p : ℕ) (hp : p ≤ gs.length)
    (hIH : ∀ q, q < p → q ∉ R →
      nlV (nlL n gs R pm pS o).gates X (n + 1 + nlCnt R q) = nlV gs X' (n + 1 + q))
    (a : ℕ) (hae : a ≠ ev)
    (haR : n + 1 ≤ a → a < n + 1 + p → a - (n + 1) ∈ R →
      a = n + 1 + pS ∨ a = n + 1 + pn ∨ a = n + 1 + pm) :
    (if nlRho n gs R pm pS p a < n + 1 + nlCnt R p then
        nlV (nlL n gs R pm pS o).gates X (nlRho n gs R pm pS p a) else false) =
      (if a < n + 1 + p then nlV gs X' a else false) := by
  have hiota : ∀ b, b < n + 1 + p → (n + 1 ≤ b → b - (n + 1) ∉ R) → b ≠ ev →
      nlIota n R b < n + 1 + nlCnt R p ∧
      nlV (nlL n gs R pm pS o).gates X (nlIota n R b) = nlV gs X' b := by
    intro b hb hbR hbe
    unfold nlIota
    by_cases hbn : b < n + 1
    · rw [if_pos hbn]
      refine ⟨by omega, ?_⟩
      rw [nlV_input _ _ _ (by omega), nlV_input _ _ _ (by omega)]
      exact hag b hbn hbe
    · rw [if_neg hbn]
      have hk := hbR (by omega)
      refine ⟨by have := nlCnt_lt R hk (show b - (n + 1) < p by omega); omega, ?_⟩
      rw [hIH _ (by omega) hk, show n + 1 + (b - (n + 1)) = b by omega]
  cases hso : nlSo n gs pm pS with
  | none =>
    unfold nlRho
    rw [hso]
    simp only
    by_cases h1 : a < n + 1
    · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]
      exact (hiota a (by omega) (by omega) hae).2.symm ▸ by
        unfold nlIota; rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : a < n + 1 + p
      · rw [if_pos h2, if_pos h2]
        by_cases h3 : a - (n + 1) ∈ R
        · rw [if_pos h3]
          have hv : nlV gs X' a = false := by
            rcases haR (by omega) h2 h3 with h | h | h
            · rw [h, hN.vS1 X' hX' he, hso]
            · rw [h]; exact hN.vn X' hX' he
            · rw [h]; exact hN.vm X' hX' he
          rw [hv]
          split_ifs <;> first | rfl | (exfalso; omega)
        · rw [if_neg h3]
          have := hiota a h2 (fun _ => h3) hae
          unfold nlIota at this
          rw [if_neg h1] at this
          rw [if_pos this.1, this.2]
      · rw [if_neg h2, if_neg h2]
        simp
  | some s =>
    obtain ⟨s1, s2, s3⟩ := hN.s_facts hR hso
    unfold nlRho
    rw [hso]
    simp only
    by_cases h1 : a < n + 1
    · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]
      rw [nlV_input _ _ _ (by omega), nlV_input _ _ _ (by omega)]
      exact hag a h1 hae
    · rw [if_neg h1]
      by_cases h2 : a < n + 1 + p
      · rw [if_pos h2, if_pos h2]
        by_cases h3 : a - (n + 1) ∈ R
        · rw [if_pos h3]
          rcases haR (by omega) h2 h3 with h | h | h
          · rw [if_pos h]
            have := hiota s (by omega) s3 s1
            rw [if_pos this.1, this.2, h, hN.vS1 X' hX' he, hso]
          · have := hN.nS; rw [if_neg (show a ≠ n + 1 + pS by omega), h, hN.vn X' hX' he]; split_ifs <;> first | rfl | (exfalso; omega)
          · have := hN.mS; rw [if_neg (show a ≠ n + 1 + pS by omega), h, hN.vm X' hX' he]; split_ifs <;> first | rfl | (exfalso; omega)
        · rw [if_neg h3]
          have := hiota a h2 (fun _ => h3) hae
          unfold nlIota at this
          rw [if_neg h1] at this
          rw [if_pos this.1, this.2]
      · rw [if_neg h2, if_neg h2]
        simp

theorem nl_gateEq (hRin : pn ∈ R ∧ pm ∈ R ∧ pS ∈ R) : ∀ p, p < gs.length → p ∉ R →
    nlV (nlL n gs R pm pS o).gates X (n + 1 + nlCnt R p) = nlV gs X' (n + 1 + p) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp hpR
    have hget : (nlL n gs R pm pS o).gates[nlCnt R p]? = some (nlMk n gs R pm pS p) :=
      nlB_get R _ hpR hp
    have hlt : nlCnt R p < (nlL n gs R pm pS o).gates.length := by
      exact (List.getElem?_eq_some_iff.1 hget).1
    have hL := nlV_gate' (nlL n gs R pm pS o).gates X (nlCnt R p) hlt
    have hC := nlV_gate' gs X' p hp
    rw [hX] at hL
    rw [hX'] at hC
    rw [hL, hC]
    have hg : (nlL n gs R pm pS o).gates[nlCnt R p] = nlMk n gs R pm pS p := by
      rw [List.getElem?_eq_some_iff] at hget; exact hget.2
    rw [hg]
    simp only [nlMk, List.map_map]
    rw [← nl_getD hp]
    apply nl_eval_congr
    intro a ha
    simp only [Function.comp, nlRd]
    rw [hX, hX']
    apply nl_readEq o hN hR X X' hX hX' he hag p (le_of_lt hp) (fun q hq hqR => ih q hq (by omega) hqR) a
    · intro hae; subst hae
      exact hpR (hN.rd_e p hp ha ▸ hRin.1)
    · intro h1 h2 h3
      have hj : a = n + 1 + (a - (n + 1)) := by omega
      rcases (hR _ h3).2 with h | h | h | h
      · rw [h] at hj; rw [hj] at ha
        exact absurd (hN.rd_n p hp ha ▸ hRin.2.1) hpR
      · rw [h] at hj; rw [hj] at ha
        exact absurd (hN.rd_m p hp ha ▸ hRin.2.2) hpR
      · exact Or.inl (by rw [hj, h])
      · rw [hj] at ha
        exact absurd (h p hp ha ▸ hRin.2.1) hpR

theorem nl_outEq (hRin : pn ∈ R ∧ pm ∈ R ∧ pS ∈ R) (hoe : o ≠ ev)
    (hoR : n + 1 ≤ o → o < n + 1 + gs.length → o - (n + 1) ∈ R →
      o = n + 1 + pS ∨ o = n + 1 + pn ∨ o = n + 1 + pm) :
    nlV (nlL n gs R pm pS o).gates X (nlL n gs R pm pS o).output = nlV gs X' o := by
  have h := nl_readEq o hN hR X X' hX hX' he hag gs.length le_rfl
    (fun q _ hqR => nl_gateEq o hN hR X X' hX hX' he hag hRin q (by omega) hqR) o hoe hoR
  have hlen : (nlL n gs R pm pS o).gates.length = nlCnt R gs.length := nlB_len R _ _
  show nlV (nlL n gs R pm pS o).gates X (nlRho n gs R pm pS gs.length o) = _
  have e1 : nlV (nlL n gs R pm pS o).gates X (nlRho n gs R pm pS gs.length o) =
      (if nlRho n gs R pm pS gs.length o < n + 1 + nlCnt R gs.length then
        nlV (nlL n gs R pm pS o).gates X (nlRho n gs R pm pS gs.length o) else false) := by
    split_ifs with h1
    · rfl
    · exact nlV_past _ _ _ (by rw [hX, hlen]; omega)
  have e2 : nlV gs X' o = (if o < n + 1 + gs.length then nlV gs X' o else false) := by
    split_ifs with h1
    · rfl
    · exact nlV_past _ _ _ (by rw [hX']; omega)
  rw [e1, e2]; exact h

end Values

end PEqualNP.MetaComplexity.Helpers.RunNL
