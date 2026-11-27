import PEqualNP.MetaComplexity.Helpers.LowMergeCases

/-!
# The low-merge inequality

The number of labels on the points of the line starts at the number of points and drops by
at most one at each low merge; at the end the line is the alive set of the output, so it has one
label.
-/

namespace PEqualNP.MetaComplexity.LowMergeProof

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

variable {P L : ℕ} (inc : Fin P → Fin L → Bool) (C : Circuit) (w : Fin L)

theorem lineLabs_succ (hC : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (t : ℕ) : (lineLabs inc C w t).card ≤
      (lineLabs inc C w (t + 1)).card + (if IsLowMerge P L inc C t w then 1 else 0) := by
  by_cases hlow : IsLow P L inc C t w
  · have h1 := lineLabs_step inc C w t hlow
    have h2 := labs_bound inc C w hC hfan t hlow
    split_ifs with hm
    · omega
    · rcases h2 with h2 | h2
      · omega
      · exact absurd h2.1 hm
  · have : lineLabs inc C w (t + 1) = lineLabs inc C w t := by
      unfold lineLabs; rw [lab_succ_of_not_low inc C w t hlow]
    rw [this]; omega

theorem lineLabs_total (hC : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (t : ℕ) : (lineLabs inc C w 0).card ≤ (lineLabs inc C w t).card +
      ((Finset.range t).filter (fun g => IsLowMerge P L inc C g w)).card := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := lineLabs_succ inc C w hC hfan t
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs at h ⊢ with hm
    · rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · omega

theorem main (hC : IsMonotoneCircuit C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hout : ∀ pts : Fin P → Bool, V C w C.output pts = lineSum P L inc w pts) :
    (Finset.univ.filter (fun p : Fin P => inc p w = true)).card ≤
      ((Finset.range (P + L + C.gates.length)).filter
        (fun g => IsLowMerge P L inc C g w)).card + 1 := by
  set S := Finset.univ.filter (fun p : Fin P => inc p w = true) with hS
  rcases S.eq_empty_or_nonempty with hE | ⟨p0, hp0⟩
  · rw [hE]; simp
  have hp0w : inc p0 w = true := by simpa [hS] using hp0
  have hlow : IsLow P L inc C C.output w := fun pts h => by rw [← hout]; exact h
  have hlt : C.output < P + L + C.gates.length := by
    by_contra hc
    have h1 := hout (ind p0)
    rw [V_big C w _ _ (by omega), lineSum_ind, hp0w] at h1
    exact Bool.false_ne_true h1
  have hSA : S ⊆ aliveSet P L C C.output w := by
    intro p hp
    rw [alive_mem, hout, lineSum_ind]
    simpa [hS] using hp
  have hend : (lineLabs inc C w (P + L + C.gates.length)).card ≤ 1 :=
    card_image_le_one inc C w _ S _ hSA (const_later inc C w _ _ hlt hlow)
  have h0 : (lineLabs inc C w 0).card = S.card := by
    unfold lineLabs
    exact Finset.card_image_of_injective _ Fin.val_injective
  have := lineLabs_total inc C w hC hfan (P + L + C.gates.length)
  omega

theorem main' (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (hC : IsMonotoneCircuit C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcomp : ∀ (x : Fin P → Bool) (y : Fin L → Bool), C.eval (List.ofFn x ++ List.ofFn y) =
      decide (∃ (p : Fin P) (w : Fin L), inc p w = true ∧ x p = true ∧ y w = true))
    (w : Fin L) :
    (Finset.univ.filter (fun p : Fin P => inc p w = true)).card ≤
      ((Finset.range (P + L + C.gates.length)).filter
        (fun g => IsLowMerge P L inc C g w)).card + 1 := by
  apply main inc C w hC hfan
  intro pts
  have h := hcomp pts (fun v : Fin L => decide (v = w))
  change V C w C.output pts = _ at h
  rw [h]
  unfold lineSum
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨p, v, h1, h2, h3⟩
    simp only [decide_eq_true_eq] at h3
    subst h3; exact ⟨p, h1, h2⟩
  · rintro ⟨p, h1, h2⟩
    exact ⟨p, w, h1, h2, by simp⟩

end PEqualNP.MetaComplexity.LowMergeProof
