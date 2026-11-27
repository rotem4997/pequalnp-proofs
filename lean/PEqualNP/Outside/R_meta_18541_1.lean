import PEqualNP.Defs

-- The 36 two-input edges and the 12 auxiliary singleton hits give the positive tests.
-- A subset of the nine retained points determines a dominating negative test: allow
-- every discarded point and every line that is not adjacent to the selected points.
-- The auxiliary outputs depend only on lines, so all point inputs are enabled there.
theorem PEqualNP.Outside.R_meta_18541_1 :
    (∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (n w : ℕ), PEqualNP.TopForm.IsAO2 n C →
      Monotone (fun x : Fin n → Bool => PEqualNP.BlindGate.wireValue C n x w)) →
    (let B := PEqualNP.HeptadCover.singerLines3 0
     let E := fun (q p l : Fin 13) => l ≠ 0 ∧ p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
       (if q ∈ B then p = q else p ∉ B)
     ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (W : Fin 13 → ℕ), C.size ≤ 50 ∧ PEqualNP.TopForm.IsAO2 26 C ∧
       (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.output < 26 + C.size ∧
       (∀ p ∈ B, W p < 26 + C.size ∧ W p ≠ p.val) ∧
       ∀ q, let o := if q ∈ B then W q else C.output
            (∀ p l, E q p l →
              PEqualNP.BlindGate.wireValue C 26 (fun i => decide (i = Fin.natAdd 13 l ∨
                (q ∉ B ∧ i = Fin.castAdd 13 p))) o = true) ∧
            (∀ P : Finset (Fin 13), (∀ p ∈ P, p ∉ B) → (q ∈ B → P = Bᶜ) →
              PEqualNP.BlindGate.wireValue C 26 (fun i => @Fin.addCases 13 13 (fun _ => Bool)
                (fun p => decide (p ∈ P ∨ p ∈ B))
                (fun l => decide (¬ ∃ p, E q p l ∧ (p ∈ P ∨ q ∈ B))) i) o = false)) →
(∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (13 : ℕ) → ℕ), x1.size ≤ (50 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x3 ∈ x1.gates, x3.inputs.Nodup) ∧ x1.output < (26 : ℕ) + x1.size ∧ (∀ x3 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x2 x3 < (26 : ℕ) + x1.size ∧ x2 x3 ≠ ↑x3) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 ∉ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 ∈ PEqualNP.HeptadCover.singerLines3 x5 ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) ∧ ∀ x4 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x3 (x2 x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)), x6 ≠ (0 : Fin (13 : ℕ)) ∧ x4 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧ x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true) := by

  intro mono tests
  classical
  let B := PEqualNP.HeptadCover.singerLines3 0
  let E := fun (q p l : Fin 13) => l ≠ 0 ∧ p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
    (if q ∈ B then p = q else p ∉ B)
  obtain ⟨C, W, hsize, hao, hnodup, hout, hW, htests⟩ := tests
  refine ⟨C, W, hsize, hao, hnodup, hout, hW, ?_⟩
  intro x
  have verify (q : Fin 13) :
      PEqualNP.BlindGate.wireValue C 26 x (if q ∈ B then W q else C.output) = true ↔
      ∃ p l, E q p l ∧ x (Fin.natAdd 13 l) = true ∧
        (q ∉ B → x (Fin.castAdd 13 p) = true) := by
    let o := if q ∈ B then W q else C.output
    obtain ⟨positive, negative⟩ := htests q
    constructor
    · intro h
      by_contra absent
      let P : Finset (Fin 13) := if q ∈ B then Bᶜ else
        Finset.univ.filter (fun p => x (Fin.castAdd 13 p) = true ∧ p ∉ B)
      have valid : ∀ p ∈ P, p ∉ B := by
        intro p hp
        by_cases hq : q ∈ B
        · simpa [P, hq] using hp
        · have hm : x (Fin.castAdd 13 p) = true ∧ p ∉ B := by simpa [P, hq] using hp
          exact hm.2
      have maximal : q ∈ B → P = Bᶜ := fun hq => by simp [P, hq]
      have up : x ≤ @Fin.addCases 13 13 (fun _ => Bool)
          (fun p : Fin 13 => decide (p ∈ P ∨ p ∈ B))
          (fun l : Fin 13 => decide (¬∃ p, E q p l ∧ (p ∈ P ∨ q ∈ B))) := by
        intro i
        induction i using @Fin.addCases 13 13 with
        | left p =>
          simp only [Fin.addCases_left]
          cases hx : x (Fin.castAdd 13 p) with
          | false => simp
          | true =>
            by_cases hb : p ∈ B
            · simp [hb]
            · by_cases hq : q ∈ B <;> simp [P, hq, hx, hb]
        | right l =>
          simp only [Fin.addCases_right]
          cases hx : x (Fin.natAdd 13 l) with
          | false => simp
          | true =>
            have no : ¬∃ p, E q p l ∧ (p ∈ P ∨ q ∈ B) := by
              rintro ⟨p, he, hP | hq⟩
              · exact absent ⟨p, l, he, hx, fun hq => by
                  have hm : x (Fin.castAdd 13 p) = true ∧ p ∉ B := by simpa [P, hq] using hP
                  exact hm.1⟩
              · exact absent ⟨p, l, he, hx, fun hn => False.elim (hn hq)⟩
            simp [no]
      have rise := mono C 26 o hao up
      change PEqualNP.BlindGate.wireValue C 26 x o = true at h
      have impossible : true ≤ false := calc
        true = _ := h.symm
        _ ≤ _ := rise
        _ = false := negative P valid maximal
      exact (by decide : ¬ true ≤ false) impossible
    · rintro ⟨p, l, he, hl, hp⟩
      have low : (fun i => decide (i = Fin.natAdd 13 l ∨
          (q ∉ B ∧ i = Fin.castAdd 13 p))) ≤ x := by
        intro i
        by_cases hi : i = Fin.natAdd 13 l ∨ (q ∉ B ∧ i = Fin.castAdd 13 p)
        · rcases hi with rfl | ⟨hq, rfl⟩
          · rw [hl]; exact Bool.le_true _
          · rw [hp hq]; exact Bool.le_true _
        · change decide _ ≤ x i
          rw [decide_eq_false hi]; exact Bool.false_le _
      have rise := mono C 26 o hao low
      apply Bool.eq_true_of_true_le
      calc
        true = _ := (positive p l he).symm
        _ ≤ _ := rise
  constructor
  · have outside : (2 : Fin 13) ∉ B := by decide
    have h := verify 2
    simp only [outside, ite_false] at h
    change PEqualNP.BlindGate.wireValue C 26 x C.output = true ↔ _
    rw [h]
    constructor
    · rintro ⟨p, l, he, hl, hp⟩
      exact ⟨p, l, by simpa [E, outside] using he.2.2, he.1, he.2.1, hp (by simp), hl⟩
    · rintro ⟨p, l, hB, h0, he, hp, hl⟩
      exact ⟨p, l, ⟨h0, he, by simpa [outside] using hB⟩, hl, fun _ => hp⟩
  · intro q hq
    change q ∈ B at hq
    have h := verify q
    simp only [hq, ite_true] at h
    rw [h]
    constructor
    · rintro ⟨p, l, he, hl, _⟩
      have eq : p = q := by simpa [hq] using he.2.2
      exact ⟨l, he.1, eq ▸ he.2.1, hl⟩
    · rintro ⟨l, hl, he, hx⟩
      exact ⟨q, l, ⟨hl, he, by simp [hq]⟩, hx, fun hn => False.elim (hn True.intro)⟩
