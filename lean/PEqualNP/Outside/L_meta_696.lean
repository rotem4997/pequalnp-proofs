import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L663

namespace PEqualNP.Outside.L_meta_696

-- Pairs counted line by line.
theorem card_pairs {α : Type} [DecidableEq α] (L : ℕ) (A : Finset α) (R : α → Fin L → Prop)
    [∀ a w, Decidable (R a w)] :
    ((A ×ˢ (Finset.univ : Finset (Fin L))).filter (fun e : α × Fin L => R e.1 e.2)).card
      = ∑ w : Fin L, (A.filter (fun a => R a w)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at he ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := he
    rw [h3] at h2
    exact ⟨h1, h2⟩
  · intro e he e' he' h
    simp only [Finset.mem_filter] at he he'
    exact Prod.ext h (he.2.trans he'.2.symm)
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact ⟨(a, w), by simp [ha.1, ha.2], rfl⟩

end PEqualNP.Outside.L_meta_696

theorem PEqualNP.Outside.L_meta_696 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → (∀ g ∈ C.gates, g.inputs.length ≤ 2) → (∀ (x : Fin P → Bool) (y : Fin L → Bool), C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ (p : Fin P) (w : Fin L), inc p w = true ∧ x p = true ∧ y w = true)) → (Finset.univ.filter (fun e : Fin P × Fin L => inc e.1 e.2 = true)).card ≤ ((Finset.range (P + L + C.gates.length) ×ˢ (Finset.univ : Finset (Fin L))).filter (fun e : ℕ × Fin L => PEqualNP.LowMerge.IsLowMerge P L inc C e.1 e.2)).card + L := by
  intro P L inc C hC hfan hcomp
  have h1 := PEqualNP.Outside.L_meta_696.card_pairs L (Finset.univ : Finset (Fin P))
    (fun p w => inc p w = true)
  rw [Finset.univ_product_univ] at h1
  have h2 := PEqualNP.Outside.L_meta_696.card_pairs L (Finset.range (P + L + C.gates.length))
    (fun g w => PEqualNP.LowMerge.IsLowMerge P L inc C g w)
  rw [h1, h2]
  have h3 : ∑ w : Fin L, (Finset.univ.filter (fun p : Fin P => inc p w = true)).card
      ≤ ∑ w : Fin L, (((Finset.range (P + L + C.gates.length)).filter
          (fun g => PEqualNP.LowMerge.IsLowMerge P L inc C g w)).card + 1) :=
    Finset.sum_le_sum (fun w _ => PEqualNP.MetaComplexity.L663 P L inc C hC hfan hcomp w)
  rw [Finset.sum_add_distrib] at h3
  simpa using h3
