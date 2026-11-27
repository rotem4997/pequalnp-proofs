import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7505
open PEqualNP.CircuitLowerBounds



theorem below {n : ℕ} (F : Finset (Finset (Fin n))) : ∀ k (S : Finset (Fin n)), S.card = k →
    S ∈ F → ∃ M ∈ F.filter (fun S => ∀ T ∈ F, T ⊆ S → S ⊆ T), M ⊆ S := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S hk hS
    by_cases hmin : ∀ T ∈ F, T ⊆ S → S ⊆ T
    · exact ⟨S, Finset.mem_filter.2 ⟨hS, hmin⟩, Finset.Subset.refl _⟩
    · push_neg at hmin
      obtain ⟨T, hT, hTS, hnot⟩ := hmin
      have hlt : T.card < S.card := Finset.card_lt_card ⟨hTS, hnot⟩
      obtain ⟨M, hM, hMT⟩ := ih T.card (hk ▸ hlt) T rfl hT
      exact ⟨M, hM, hMT.trans hTS⟩

end PEqualNP.Outside.L_meta_7505

open PEqualNP.Outside.L_meta_7505 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7505 : ∀ (x1 : ℕ) (x2 : Finset (Finset (Fin (x1 + x1)))) (x3 : Bool) (x4 : Fin x1 → Bool),   have x5 : Bool → List Bool := fun (x5 : Bool) => if x3 = Bool.true then List.ofFn x4 ++ List.replicate x1 x5 else List.replicate x1 x5 ++ List.ofFn x4;   have x6 : Bool → Prop := fun (x6 : Bool) => ∀ x7 ∈ x2, ∃ x9 ∈ x7, (x5 x6).getD (↑x9) Bool.false = Bool.true;   ¬(x6 Bool.false ↔ x6 Bool.true) → ∃ x8 ∈ x2, (∀ x9 ∈ x2, x9 ⊆ x8 → x9 = x8) ∧ ∃ x9 ∈ x8, if x3 = Bool.true then x1 ≤ ↑x9 else ↑x9 < x1 := by
  intro n F s y X P hne
  have agree : ∀ i : Fin (n + n), ¬(if s = true then n ≤ (i : ℕ) else (i : ℕ) < n) →
      ∀ b b' : Bool, (X b).getD (i : ℕ) false = (X b').getD (i : ℕ) false := by
    intro i hi b b'
    cases s
    · have h1 : n ≤ (i : ℕ) := by simpa using hi
      simp [X, List.getD_eq_getElem?_getD, List.getElem?_append_right, h1]
    · have h1 : (i : ℕ) < n := by simpa using hi
      simp [X, List.getD_eq_getElem?_getD, List.getElem?_append_left, h1]
  have main : ∀ b b' : Bool, P b → ¬ P b' →
      ∃ x8 ∈ F, (∀ x9 ∈ F, x9 ⊆ x8 → x9 = x8) ∧
        ∃ x9 ∈ x8, if s = true then n ≤ (x9 : ℕ) else (x9 : ℕ) < n := by
    intro b b' hb hb'
    have hb2 : ∃ T0 ∈ F, ∀ i ∈ T0, ¬ (X b').getD (i : ℕ) false = true := by
      by_contra hc
      apply hb'
      intro T hT
      by_contra hc2
      exact hc ⟨T, hT, fun i hi hv => hc2 ⟨i, hi, hv⟩⟩
    obtain ⟨T0, hT0, hall⟩ := hb2
    obtain ⟨M, hM, hMT⟩ := below F _ T0 rfl hT0
    obtain ⟨hMF, hMmin⟩ := Finset.mem_filter.1 hM
    obtain ⟨i, hi, hv⟩ := hb M hMF
    refine ⟨M, hMF, fun T hT hTM => Finset.Subset.antisymm hTM (hMmin T hT hTM), i, hi, ?_⟩
    by_contra hside
    have h5 := agree i hside b b'
    rw [h5] at hv
    exact hall i (hMT hi) hv
  by_cases hf : P false
  · by_cases ht : P true
    · exact absurd ⟨fun _ => ht, fun _ => hf⟩ hne
    · exact main false true hf ht
  · by_cases ht : P true
    · exact main true false ht hf
    · exact absurd ⟨fun h => absurd h hf, fun h => absurd h ht⟩ hne
