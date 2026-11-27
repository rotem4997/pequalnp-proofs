import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.PermInputs

/-- From the read-2 bound `N q <= 100 s` for projective-plane incidence functions, the bound
`N (q + 1) <= 112 s`: the function depends on all `2 N` inputs, so `2 N <= s + 1`. -/
theorem PEqualNP.MetaComplexity.L2506 : (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size) → ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * (q + 1) ≤ 112 * C.size := by
  intro H q N I _ C hq hN hcard hline hAO hfun hread
  have h1 := H q N I C hq hN hcard hline hAO hfun hread
  have hN7 : 7 ≤ N := by subst hN; nlinarith
  have hFan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    rcases hAO.1 g hg with h | h
    · exact ⟨by simp [h], by rw [hAO.2.2 g hg]⟩
    · exact ⟨by simp [h], by rw [hAO.2.2 g hg]⟩
  have hHas : PEqualNP.MetaComplexity.HasCircuitSize (N + N)
      (PEqualNP.MetaComplexity.circuitFun (N + N) C) C.size :=
    ⟨C, hFan, le_refl _, fun x => rfl⟩
  -- the indicator of a single input wire is false
  have hone : ∀ a : Fin (N + N),
      PEqualNP.MetaComplexity.circuitFun (N + N) C (fun j => decide (j = a)) = false := by
    intro a
    rw [hfun]
    simp only [decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
    intro p l _ hp hl
    have h := hp.trans hl.symm
    have := congrArg Fin.val h
    simp [Fin.coe_castAdd, Fin.coe_natAdd] at this
    omega
  have hpair : ∀ p l : Fin N, I p l →
      (∀ x : Fin (N + N) → Bool, x (Fin.castAdd N p) = true → x (Fin.natAdd N l) = true →
        PEqualNP.MetaComplexity.circuitFun (N + N) C x = true) := by
    intro p l hpl x hx1 hx2
    rw [hfun]
    simp only [decide_eq_true_eq]
    exact ⟨p, l, hpl, hx1, hx2⟩
  have hne : ∀ a b : Fin N, Fin.castAdd N a ≠ Fin.natAdd N b := by
    intro a b h
    have := congrArg Fin.val h
    simp [Fin.coe_castAdd, Fin.coe_natAdd] at this
    omega
  have hdep : ∀ i ∈ (Finset.univ : Finset (Fin (N + N))), ∃ x : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C (Function.update x i (!x i)) ≠
        PEqualNP.MetaComplexity.circuitFun (N + N) C x := by
    intro i _
    refine Fin.addCases (motive := fun i => ∃ x : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C (Function.update x i (!x i)) ≠
        PEqualNP.MetaComplexity.circuitFun (N + N) C x) ?_ ?_ i
    · intro p
      -- a line through p
      have hp0 : 0 < N := by omega
      obtain ⟨p', hp'⟩ : ∃ p' : Fin N, p' ≠ p := by
        by_cases h : p = ⟨0, hp0⟩
        · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
        · exact ⟨⟨0, hp0⟩, fun e => h e.symm⟩
      obtain ⟨l, ⟨hpl, _⟩, _⟩ := hline p p' (Ne.symm hp')
      refine ⟨fun j => decide (j = Fin.natAdd N l), ?_⟩
      rw [hone]
      have hv : (fun j => decide (j = Fin.natAdd N l)) (Fin.castAdd N p) = false := by
        simpa using hne p l
      rw [hv]
      rw [hpair p l hpl]
      · simp
      · simp
      · rw [Function.update_of_ne (Ne.symm (hne p l))]; simp
    · intro l
      have hc := hcard l
      obtain ⟨p, hp⟩ : (Finset.univ.filter (fun p => I p l)).Nonempty := by
        rw [← Finset.card_pos, hc]; omega
      have hpl : I p l := (Finset.mem_filter.1 hp).2
      refine ⟨fun j => decide (j = Fin.castAdd N p), ?_⟩
      rw [hone]
      have hv : (fun j => decide (j = Fin.castAdd N p)) (Fin.natAdd N l) = false := by
        simpa using (hne p l).symm
      rw [hv]
      rw [hpair p l hpl]
      · simp
      · rw [Function.update_of_ne (hne p l)]; simp
      · simp
  have h2 := PEqualNP.MetaComplexity.Helpers.PermInputs.dep_lower_set (N + N)
    (PEqualNP.MetaComplexity.circuitFun (N + N) C) Finset.univ hdep C.size hHas
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : N ≤ C.size := by omega
  nlinarith
