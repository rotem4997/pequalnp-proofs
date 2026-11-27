import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1681_2 :
    (let D : Finset (Fin 13) := {0, 1, 3, 9}
     ∀ a b c k : Fin 13, a ≠ b → a ≠ c → b ≠ c →
       a - k ∈ D → b - k ∈ D → c - k ∈ D →
       ∃ z : Fin 13, ∀ w : Fin 13,
         a - w ∉ D → b - w ∉ D → c - w ∉ D → z - w ∈ D) →
    (let D : Finset (Fin 13) := {0, 1, 3, 9}
     ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
       PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧
       (∀ p w : Fin 13, p - w ∈ D →
         PEqualNP.MetaComplexity.circuitFun (13 + 13) C
           (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w)) = true) ∧
       (∀ P W : Finset (Fin 13),
         (∀ p ∈ P, ∀ w ∈ W, p - w ∉ D) →
         (∀ w : Fin 13, (P.filter fun p => p - w ∈ D).card ≤ 2) →
         (∀ p : Fin 13, (W.filter fun w => p - w ∈ D).card ≤ 2) →
         PEqualNP.MetaComplexity.circuitFun (13 + 13) C
           (fun i => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨
             (∃ w ∈ W, i = Fin.natAdd 13 w))) = false)) →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  intro triple synthesis
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  have inc (p w : Fin 13) :
      (∃ d ∈ D, p = w + d) ↔ p - w ∈ D := by
    constructor
    · rintro ⟨d, hd, he⟩
      have hs : p - w = d := sub_eq_iff_eq_add.2 (he.trans (add_comm _ _))
      rwa [hs]
    · intro h
      exact ⟨p - w, h, (sub_add_cancel p w).symm.trans (add_comm _ _)⟩
  have dual (p w : Fin 13) : (-w) - (-p) = p - w := by
    simp [sub_eq_add_neg, add_comm]
  obtain ⟨C, hmono, hsize, haccept, hreject⟩ := synthesis
  refine ⟨C, hmono, hsize, ?_, ?_⟩
  · intro p w hpw
    exact haccept p w ((inc p w).1 hpw)
  intro P _ hgeneric
  let W : Finset (Fin 13) := Finset.univ.filter (fun w => ∀ p ∈ P, p - w ∉ D)
  have memW (w : Fin 13) : w ∈ W ↔ ∀ p ∈ P, p - w ∉ D := by
    simp [W]
  have hnon (p : Fin 13) (hp : p ∈ P) (w : Fin 13) (hw : w ∈ W) :
      p - w ∉ D := (memW w).1 hw p hp
  have hP (k : Fin 13) : (P.filter fun p => p - k ∈ D).card ≤ 2 := by
    by_contra! hcard
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hcard
    obtain ⟨haP, hak⟩ := Finset.mem_filter.1 ha
    obtain ⟨hbP, hbk⟩ := Finset.mem_filter.1 hb
    obtain ⟨hcP, hck⟩ := Finset.mem_filter.1 hc
    obtain ⟨z, hz⟩ := triple a b c k hab hac hbc hak hbk hck
    apply hgeneric.2
    refine ⟨z, fun w hw => (inc z w).2 (hz w (hw a haP ∘ (inc a w).2)
      (hw b hbP ∘ (inc b w).2) (hw c hcP ∘ (inc c w).2))⟩
  have hW (k : Fin 13) : (W.filter fun w => k - w ∈ D).card ≤ 2 := by
    by_contra! hcard
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hcard
    obtain ⟨haW, hak⟩ := Finset.mem_filter.1 ha
    obtain ⟨hbW, hbk⟩ := Finset.mem_filter.1 hb
    obtain ⟨hcW, hck⟩ := Finset.mem_filter.1 hc
    obtain ⟨z, hz⟩ := triple (-a) (-b) (-c) (-k)
      (fun e => hab (neg_injective e)) (fun e => hac (neg_injective e))
      (fun e => hbc (neg_injective e))
      (by rwa [dual]) (by rwa [dual]) (by rwa [dual])
    apply hgeneric.1
    refine ⟨-z, fun p hp => (inc p (-z)).2 ?_⟩
    have hh := hz (-p) (by rw [dual]; exact hnon p hp a haW)
      (by rw [dual]; exact hnon p hp b hbW)
      (by rw [dual]; exact hnon p hp c hcW)
    simpa only [sub_neg_eq_add, add_comm] using hh
  have hinput :
      (fun i : Fin (13 + 13) => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨
        (∃ w ∈ W, i = Fin.natAdd 13 w))) =
      (fun i : Fin (13 + 13) => decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨
        (∃ w : Fin 13, i = Fin.natAdd 13 w ∧ (∀ p ∈ P, ¬ ∃ d ∈ D, p = w + d)))) := by
    funext i
    apply decide_eq_decide.mpr
    simp only [memW]
    constructor
    · rintro (h | ⟨w, hw, hi⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, hi, fun p hp hiw => hw p hp ((inc p w).1 hiw)⟩
    · rintro (h | ⟨w, hi, hw⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, fun p hp hiw => hw p hp ((inc p w).2 hiw), hi⟩
  rw [← hinput]
  exact hreject P W hnon hP hW
