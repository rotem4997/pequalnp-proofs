import PEqualNP.MetaComplexity.Helpers.RunNL5

/-!
# Theorem NL, part 6: the chain of the new list lifts, and the two points contradict it

`nlChain` is the conclusion of the free-input-chain statement on the new list, indexed by
naturals. Each chain gate is a kept gate `γ i` of the old list. Case A: the other operand `s` of
the OR gate is no chain predecessor; then the chain is literal in the old list and the output is
`true` at the point `X0` (only `x_q` set). Case B: `s` is a chain predecessor; then a chain gate
that is `true` at `X1` (`x_q`, `x_e` set) is `true` at `X0`. Both contradict the two points.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunNL

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The free-input chain of `L` at input `n`, indexed by naturals. -/
structure nlChain (n : ℕ) (L : Circuit) (k : ℕ) (cn : ℕ → ℕ) : Prop where
  lt : ∀ i, i ≤ k → cn i < L.gates.length
  mono : ∀ i j, i < j → j ≤ k → cn i < cn j
  op : ∀ i, i ≤ k → (L.gates.getD (cn i) nlG0).op = GateOp.or ∧
    (L.gates.getD (cn i) nlG0).inputs.length = 2
  pred : ∀ i, i ≤ k → (if i = 0 then n else n + 1 + cn (i - 1)) ∈ (L.gates.getD (cn i) nlG0).inputs
  side : ∀ i, i ≤ k → ∃ w ∈ (L.gates.getD (cn i) nlG0).inputs,
    w ≠ (if i = 0 then n else n + 1 + cn (i - 1)) ∧ w ≠ n ∧
      ¬ Relation.TransGen (nlFR n L) n w
  above : ∀ i, i ≤ k → Relation.TransGen (nlFR n L) n (n + 1 + cn i)
  out : L.output = n + 1 + cn k

section
variable {n : ℕ} {gs : List Gate}

theorem nl_orT (X : List Bool) (hX : X.length = n + 1) (p : ℕ) (hp : p < gs.length)
    (hop : (gs.getD p nlG0).op = GateOp.or) (a : ℕ) (ha : a ∈ (gs.getD p nlG0).inputs)
    (hal : a < n + 1 + p) (hv : nlV gs X a = true) : nlV gs X (n + 1 + p) = true := by
  rw [nl_getD hp] at hop ha
  have := nl_or_true gs X p hp hop a ha (by rw [hX]; exact hal) hv
  rw [hX] at this; exact this

theorem nl_orS (X : List Bool) (hX : X.length = n + 1) (p : ℕ) (hp : p < gs.length)
    (hop : (gs.getD p nlG0).op = GateOp.or) (hv : nlV gs X (n + 1 + p) = true) :
    ∃ a ∈ (gs.getD p nlG0).inputs, a < n + 1 + p ∧ nlV gs X a = true := by
  rw [nl_getD hp] at hop ⊢
  have := nl_or_some gs X p hp hop (by rw [hX]; exact hv)
  rw [hX] at this; exact this

end

section
variable {n : ℕ} {gs : List Gate} {ev pn pm pS : ℕ} {R : Finset ℕ} (o : ℕ)
  (hN : nlState n gs ev pn pm pS) (hR : nlRSpec n gs pn pm pS R)
  (hRin : pn ∈ R ∧ pm ∈ R ∧ pS ∈ R) (hRle : ∀ j ∈ R, j ≤ pS)
  (X0 X1 : List Bool) (hX0 : X0.length = n + 1) (hX1 : X1.length = n + 1)
  (he1 : X1.getD ev false = true) (hq0 : X0.getD n false = true)
  (hag : ∀ i, i < n + 1 → i ≠ ev → X0.getD i false = X1.getD i false)
  (hF0 : nlV gs X0 o = false) (hF1 : nlV gs X1 o = true) (hoe : o ≠ ev)
include hN hR hRin hRle hX0 hX1 he1 hq0 hag hF0 hF1 hoe

theorem nl_lift (k : ℕ) (cn : ℕ → ℕ) (hC : nlChain n (nlL n gs R pm pS o) k cn) : False := by
  set L := nlL n gs R pm pS o with hL
  have hγ : ∀ i, ∃ p, i ≤ k → p < gs.length ∧ p ∉ R ∧ nlCnt R p = cn i ∧
      L.gates.getD (cn i) nlG0 = nlMk n gs R pm pS p := by
    intro i
    by_cases hi : i ≤ k
    · have hlt := hC.lt i hi
      have h1 : L.gates[cn i]? = some (L.gates.getD (cn i) nlG0) := by
        rw [nl_getD hlt]; exact List.getElem?_eq_getElem hlt
      obtain ⟨q, hq, hqR, hc, hg⟩ := nlB_mem R _ gs.length (cn i) _ h1
      exact ⟨q, fun _ => ⟨hq, hqR, hc, hg⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose γ hγ using hγ
  have hop : ∀ i, i ≤ k → (gs.getD (γ i) nlG0).op = GateOp.or ∧
      (gs.getD (γ i) nlG0).inputs.length = 2 := by
    intro i hi
    have := hC.op i hi
    rw [(hγ i hi).2.2.2] at this
    simpa [nlMk] using this
  have hins : ∀ i, i ≤ k → (L.gates.getD (cn i) nlG0).inputs =
      (gs.getD (γ i) nlG0).inputs.map (nlRho n gs R pm pS (γ i)) := by
    intro i hi
    rw [(hγ i hi).2.2.2]; rfl
  have hγmono : ∀ i j, i < j → j ≤ k → γ i < γ j := by
    intro i j hij hj
    by_contra hcon
    have h1 := nlCnt_mono R (show γ j ≤ γ i by omega)
    rw [(hγ i (by omega)).2.2.1, (hγ j hj).2.2.1] at h1
    have := hC.mono i j hij hj
    omega
  -- the chain predecessors in the old list
  let PC : ℕ → ℕ := fun i => if i = 0 then n else n + 1 + γ (i - 1)
  have hPC : ∀ i, i ≤ k → nlIota n R (PC i) = (if i = 0 then n else n + 1 + cn (i - 1)) ∧
      PC i < n + 1 + γ i ∧ (n + 1 ≤ PC i → PC i - (n + 1) ∉ R) := by
    intro i hi
    by_cases h0 : i = 0
    · simp only [PC, h0, if_true]
      refine ⟨by unfold nlIota; rw [if_pos (by omega)], by omega, fun h => by omega⟩
    · simp only [PC, h0, if_false]
      have hk := hγ (i - 1) (by omega)
      refine ⟨?_, ?_, ?_⟩
      · unfold nlIota; rw [if_neg (by omega)]; simp [hk.2.2.1]
      · have := hγmono (i - 1) i (by omega) hi; omega
      · intro _; simpa using hk.2.1
  have hpredC : ∀ i, i ≤ k → ∃ a ∈ (gs.getD (γ i) nlG0).inputs,
      a = PC i ∨ (a = n + 1 + pS ∧ pS < γ i ∧ nlSo n gs pm pS = some (PC i)) := by
    intro i hi
    have h := hC.pred i hi
    rw [hins i hi] at h
    obtain ⟨a, ha, hra⟩ := List.mem_map.1 h
    obtain ⟨p1, p2, p3⟩ := hPC i hi
    rw [← p1] at hra
    exact ⟨a, ha, nl_pre hN hR (γ i) a (PC i) p2 p3 hra⟩
  -- the output
  have hout : o = n + 1 + γ k ∨ (o = n + 1 + pS ∧ nlSo n gs pm pS = some (n + 1 + γ k)) := by
    have h := hC.out
    have hk := hγ k le_rfl
    have hb : nlIota n R (n + 1 + γ k) = n + 1 + cn k := by
      unfold nlIota; rw [if_neg (by omega)]; simp [hk.2.2.1]
    rw [← hb] at h
    rcases nl_pre hN hR gs.length o (n + 1 + γ k) (by omega) (fun _ => by simpa using hk.2.1) h
      with h1 | ⟨h1, _, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, h3⟩
  by_cases hB : ∃ j, j ≤ k ∧ nlSo n gs pm pS = some (PC j)
  · -- Case B
    obtain ⟨j, hj, hso⟩ := hB
    have hsA : nlIota n R (PC j) = n ∨
        Relation.TransGen (nlFR n L) n (nlIota n R (PC j)) := by
      rw [(hPC j hj).1]
      by_cases h0 : j = 0
      · left; simp [h0]
      · right; simp only [h0, if_false]; exact hC.above (j - 1) (by omega)
    have hoγ : o = n + 1 + γ k := by
      rcases hout with h | ⟨_, h⟩
      · exact h
      · rw [hso] at h
        injection h with h
        simp only [PC] at h
        by_cases h0 : j = 0
        · simp [h0] at h; omega
        · simp only [h0, if_false] at h
          have := hγmono (j - 1) k (by omega) le_rfl
          omega
    have claim : ∀ i, i ≤ k → nlV gs X1 (n + 1 + γ i) = true →
        nlV gs X0 (n + 1 + γ i) = true := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
      intro hi h1
      have hk := hγ i hi
      obtain ⟨a, ha, hal, hv⟩ := nl_orS X1 hX1 (γ i) hk.1 (hop i hi).1 h1
      suffices hv0 : nlV gs X0 a = true from
        nl_orT X0 hX0 (γ i) hk.1 (hop i hi).1 a ha hal hv0
      have hsf := hN.s_free hso
      by_cases haS : a = n + 1 + pS
      · subst haS
        have e1 := hN.vS1 X1 hX1 he1
        rw [hso] at e1
        simp only at e1
        rw [e1, ← nl_free_rch X0 X1 hX0 hX1 hag _ hsf] at hv
        obtain ⟨k1, _, k3⟩ := nlSo_spec n gs pm pS _ hso
        exact nl_orT X0 hX0 pS hN.pS_lt hN.S_op _ k1 k3 hv
      by_cases hrch : nlRch gs (n + 1) ev a
      swap
      · rw [nl_free_rch X0 X1 hX0 hX1 hag a hrch]; exact hv
      have hrel : nlRel (gs.getD (γ i) nlG0) a := Or.inr ⟨by rw [(hop i hi).1]; simp, ha⟩
      rcases hrch with hae | hrch
      · subst hae; exact absurd (hN.rd_e _ hk.1 hrel ▸ hRin.1) hk.2.1
      rcases hN.reach hrch with h' | h' | h' | h'
      · rw [h'] at hrel; exact absurd (hN.rd_n _ hk.1 hrel ▸ hRin.2.1) hk.2.1
      · rw [h'] at hrel; exact absurd (hN.rd_m _ hk.1 hrel ▸ hRin.2.2) hk.2.1
      · exact absurd h' haS
      obtain ⟨q1, q2, q3, q4⟩ := nl_path hN hR o hRin.2.2 hRle hso h'
      have hρ := nlRho_iota n gs R pm pS (γ i) a hal (fun _ => q3)
      have hmem : nlIota n R a ∈ (L.gates.getD (cn i) nlG0).inputs := by
        rw [hins i hi, ← hρ]; exact List.mem_map_of_mem ha
      obtain ⟨w, hw, hw1, _, hw3⟩ := hC.side i hi
      have hlen : (L.gates.getD (cn i) nlG0).inputs.length ≤ 2 := by rw [(hC.op i hi).2]
      rcases nl_two' _ hlen _ w _ (hC.pred i hi) hw (fun h => hw1 h.symm) hmem with h2 | h2
      · rw [← (hPC i hi).1] at h2
        have := nlIota_inj n R a (PC i) (fun _ => q3) (hPC i hi).2.2 h2
        by_cases h0 : i = 0
        · simp [PC, h0] at this; omega
        · simp only [PC, h0, if_false] at this
          rw [this] at hv ⊢
          exact ih (i - 1) (by omega) (by omega) hv
      · exfalso; apply hw3
        rw [← h2]
        rcases hsA with h3 | h3
        · rw [h3] at q4; exact q4
        · exact Relation.TransGen.trans h3 q4
    have := claim k le_rfl (by rw [← hoγ]; exact hF1)
    rw [← hoγ, hF0] at this
    cases this
  · -- Case A
    have claim : ∀ i, i ≤ k → nlV gs X0 (n + 1 + γ i) = true := by
      intro i
      induction i with
      | zero =>
        intro hi
        obtain ⟨a, ha, h | ⟨_, _, h⟩⟩ := hpredC 0 hi
        · have hk := hγ 0 hi
          refine nl_orT X0 hX0 (γ 0) hk.1 (hop 0 hi).1 a ha (by rw [h]; exact (hPC 0 hi).2.1) ?_
          rw [h]; simp only [PC, if_true]
          rw [nlV_input _ _ _ (by omega)]; exact hq0
        · exact absurd ⟨0, hi, h⟩ hB
      | succ i ih =>
        intro hi
        obtain ⟨a, ha, h | ⟨_, _, h⟩⟩ := hpredC (i + 1) hi
        · have hk := hγ (i + 1) hi
          refine nl_orT X0 hX0 (γ (i + 1)) hk.1 (hop (i + 1) hi).1 a ha
            (by rw [h]; exact (hPC (i + 1) hi).2.1) ?_
          rw [h]; simp only [PC]; simpa using ih (by omega)
        · exact absurd ⟨i + 1, hi, h⟩ hB
    rcases hout with h | ⟨h1, h2⟩
    · rw [h, claim k le_rfl] at hF0; cases hF0
    · obtain ⟨k1, _, k3⟩ := nlSo_spec n gs pm pS _ h2
      have := nl_orT X0 hX0 pS hN.pS_lt hN.S_op _ k1 k3 (claim k le_rfl)
      rw [h1, this] at hF0; cases hF0

end

end PEqualNP.MetaComplexity.Helpers.RunNL
