import PEqualNP.MetaComplexity.Helpers.LowMergeLabels

/-!
# One wire: a low wire's alive set carries one label, or it is a low merge and carries two

The case analysis of the paper's facts F1 to F3 on the kinds of wire.
-/

namespace PEqualNP.MetaComplexity.LowMergeProof

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

variable {P L : ℕ} (inc : Fin P → Fin L → Bool) (C : Circuit) (w : Fin L)

theorem labs_of_dead (t : ℕ) (h : ∀ p : Fin P, V C w t (ind p) = false) :
    (labs inc C w t).card ≤ 1 := by
  have : aliveSet P L C t w = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp; rw [alive_mem, h p] at hp; exact Bool.false_ne_true hp
  unfold labs; rw [this]; simp

theorem labs_of_sub (t a : ℕ) (hat : a < t) (hlow : IsLow P L inc C a w)
    (hsub : ∀ p : Fin P, V C w t (ind p) = true → V C w a (ind p) = true) :
    (labs inc C w t).card ≤ 1 := by
  apply card_image_le_one inc C w t _ (aliveSet P L C a w)
  · intro p hp; rw [alive_mem] at hp ⊢; exact hsub p hp
  · exact const_later inc C w a t hat hlow

theorem labs_of_copy (t b : ℕ) (hlow : IsLow P L inc C t w)
    (hv : ∀ pts : Fin P → Bool, V C w t pts = R C w t b pts) : (labs inc C w t).card ≤ 1 := by
  by_cases hb : b < t
  · have e : ∀ pts : Fin P → Bool, V C w t pts = V C w b pts := by
      intro pts; rw [hv]; unfold R; rw [if_pos hb]
    apply labs_of_sub inc C w t b hb
    · intro pts h; exact hlow pts (((e pts).trans h : V C w t pts = true))
    · intro p h; rwa [← e]
  · apply labs_of_dead
    intro p; rw [hv]; unfold R; rw [if_neg hb]

theorem not_low_elim {g : ℕ} (h : ¬ IsLow P L inc C g w) :
    ∃ pts : Fin P → Bool, V C w g pts = true ∧ ∀ p, inc p w = true → pts p = false := by
  rw [isLow_iff] at h
  simp only [not_forall] at h
  obtain ⟨pts, h1, h2⟩ := h
  refine ⟨pts, h1, fun p hp => ?_⟩
  by_contra hc
  apply h2
  unfold lineSum
  simp only [decide_eq_true_eq]
  exact ⟨p, hp, by simpa using hc⟩

theorem and_low (hC : IsMonotoneCircuit C) (t a b : ℕ) (hlow : IsLow P L inc C t w)
    (hv : ∀ pts : Fin P → Bool, V C w t pts = (V C w a pts && V C w b pts)) :
    IsLow P L inc C a w ∨ IsLow P L inc C b w := by
  by_contra hn
  simp only [not_or] at hn
  obtain ⟨p1, h1, e1⟩ := not_low_elim inc C w hn.1
  obtain ⟨p2, h2, e2⟩ := not_low_elim inc C w hn.2
  let pts : Fin P → Bool := fun p => p1 p || p2 p
  have ha : V C w a pts = true := V_mono C hC w a p1 pts (fun p h => by simp [pts, h]) h1
  have hb : V C w b pts = true := V_mono C hC w b p2 pts (fun p h => by simp [pts, h]) h2
  have ht : V C w t pts = true := by rw [hv, ha, hb]; rfl
  have := hlow pts ht
  unfold lineSum at this
  simp only [decide_eq_true_eq] at this
  obtain ⟨p, hp, hpt⟩ := this
  simp [pts, e1 p hp, e2 p hp] at hpt

/-- The per-wire bound. -/
theorem labs_bound (hC : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (t : ℕ) (hlow : IsLow P L inc C t w) :
    (labs inc C w t).card ≤ 1 ∨ (IsLowMerge P L inc C t w ∧ (labs inc C w t).card ≤ 2) := by
  by_cases hin : t < P + L
  · left
    by_cases hP : t < P
    · apply card_image_le_one inc C w t _ {⟨t, hP⟩}
      · intro p hp
        rw [alive_mem, V_input_lt C w t _ hP] at hp
        unfold ind at hp
        simp only [decide_eq_true_eq] at hp
        simp [← hp]
      · intro p hp q hq
        rw [Finset.mem_singleton] at hp hq; rw [hp, hq]
    · apply labs_of_dead
      intro p
      rw [V_input_ge C w t (ind p) (fun _ => false) (by omega) hin]
      by_contra hc
      have := hlow (fun _ => false) (by simpa using hc : V C w t (fun _ => false) = true)
      rw [lineSum_false] at this; exact Bool.false_ne_true this
  by_cases hbig : P + L + C.gates.length ≤ t
  · left; apply labs_of_dead; intro p; exact V_big C w t _ hbig
  obtain ⟨j, rfl⟩ : ∃ j, t = P + L + j := ⟨t - (P + L), by omega⟩
  have hj : j < C.gates.length := by omega
  have hop := hC _ (List.getElem_mem hj)
  have hf := hfan _ (List.getElem_mem hj)
  have hv := V_gate (P := P) C w j hj
  have hgate : C.gates[P + L + j - (P + L)]? = some C.gates[j] := by
    rw [show P + L + j - (P + L) = j by omega]; exact List.getElem?_eq_getElem hj
  generalize C.gates[j] = G at hop hf hv hgate
  obtain ⟨op, ins⟩ := G
  simp only at hop hf hv hgate
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · -- no inputs
    left
    rcases hop with rfl | rfl
    · exfalso
      have := hlow (fun _ => false) ((hv _).trans rfl : V C w (P + L + j) (fun _ => false) = true)
      rw [lineSum_false] at this; exact Bool.false_ne_true this
    · apply labs_of_dead; intro p; rw [hv]; rfl
  · -- one input
    left
    apply labs_of_copy inc C w _ a hlow
    intro pts; rw [hv pts]
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  · -- two inputs
    rcases hop with rfl | rfl
    · left
      have hv2 : ∀ pts : Fin P → Bool, V C w (P + L + j) pts = (R C w (P + L + j) a pts && R C w (P + L + j) b pts) := by
        intro pts; rw [hv pts]; simp [GateOp.eval]
      by_cases ha : a < P + L + j
      · by_cases hb : b < P + L + j
        · have hv3 : ∀ pts : Fin P → Bool, V C w (P + L + j) pts = (V C w a pts && V C w b pts) := by
            intro pts; rw [hv2]; unfold R; rw [if_pos ha, if_pos hb]
          rcases and_low inc C w hC _ a b hlow hv3 with hla | hlb
          · apply labs_of_sub inc C w _ a ha hla
            intro p h; rw [hv3] at h; simp only [Bool.and_eq_true] at h; exact h.1
          · apply labs_of_sub inc C w _ b hb hlb
            intro p h; rw [hv3] at h; simp only [Bool.and_eq_true] at h; exact h.2
        · apply labs_of_dead; intro p; rw [hv2]; unfold R; rw [if_neg hb]; simp
      · apply labs_of_dead; intro p; rw [hv2]; unfold R; rw [if_neg ha]; simp
    · have hv2 : ∀ pts : Fin P → Bool, V C w (P + L + j) pts = (R C w (P + L + j) a pts || R C w (P + L + j) b pts) := by
        intro pts; rw [hv pts]; simp [GateOp.eval]
      by_cases ha : a < P + L + j
      · by_cases hb : b < P + L + j
        · have hv3 : ∀ pts : Fin P → Bool, V C w (P + L + j) pts = (V C w a pts || V C w b pts) := by
            intro pts; rw [hv2]; unfold R; rw [if_pos ha, if_pos hb]
          have hla : IsLow P L inc C a w := by
            intro pts h; apply hlow pts
            show V C w (P + L + j) pts = true
            rw [hv3]; simp [show V C w _ pts = true from h]
          have hlb : IsLow P L inc C b w := by
            intro pts h; apply hlow pts
            show V C w (P + L + j) pts = true
            rw [hv3]; simp [show V C w _ pts = true from h]
          by_cases hab : aliveSet P L C a w ⊆ aliveSet P L C b w
          · left
            apply labs_of_sub inc C w _ b hb hlb
            intro p h; rw [hv3] at h; simp only [Bool.or_eq_true] at h
            rcases h with h | h
            · have := hab ((alive_mem C w a p).mpr h); rwa [alive_mem] at this
            · exact h
          by_cases hba : aliveSet P L C b w ⊆ aliveSet P L C a w
          · left
            apply labs_of_sub inc C w _ a ha hla
            intro p h; rw [hv3] at h; simp only [Bool.or_eq_true] at h
            rcases h with h | h
            · exact h
            · have := hba ((alive_mem C w b p).mpr h); rwa [alive_mem] at this
          right
          refine ⟨⟨by omega, a, ha, b, hb, hgate, hlow, hab, hba⟩, ?_⟩
          have hsub : aliveSet P L C (P + L + j) w ⊆ aliveSet P L C a w ∪ aliveSet P L C b w := by
            intro p hp
            rw [alive_mem, hv3] at hp
            simp only [Bool.or_eq_true] at hp
            rw [Finset.mem_union, alive_mem, alive_mem]; exact hp
          have c1 := card_image_le_one inc C w (P + L + j) (aliveSet P L C a w)
            (aliveSet P L C a w) (subset_refl _) (const_later inc C w a _ ha hla)
          have c2 := card_image_le_one inc C w (P + L + j) (aliveSet P L C b w)
            (aliveSet P L C b w) (subset_refl _) (const_later inc C w b _ hb hlb)
          unfold labs
          calc ((aliveSet P L C (P + L + j) w).image (lab inc C w (P + L + j))).card
              ≤ ((aliveSet P L C a w ∪ aliveSet P L C b w).image (lab inc C w (P + L + j))).card :=
                Finset.card_le_card (Finset.image_subset_image hsub)
            _ ≤ _ := by
                rw [Finset.image_union]
                exact (Finset.card_union_le _ _).trans (by omega)
        · left
          apply labs_of_copy inc C w _ a hlow
          intro pts; rw [hv2]; unfold R; rw [if_neg hb]; simp
      · left
        apply labs_of_copy inc C w _ b hlow
        intro pts; rw [hv2]; unfold R; rw [if_neg ha]; simp
  · exfalso; simp at hf

end PEqualNP.MetaComplexity.LowMergeProof
