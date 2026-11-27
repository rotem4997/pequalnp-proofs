import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4777 : ∀ (x1 : List (ℕ × ℕ)) (x2 : (Fin (14 : ℕ) → Bool) → Bool), (x1.all fun (x3 : ℕ × ℕ) => Decidable.decide (x3.1 < x3.2)) = Bool.true → (∀ (x4 x5 : Fin (14 : ℕ) → Bool), (∀ (x6 : Fin (14 : ℕ)), x4 x6 = Bool.true → x5 x6 = Bool.true) → x2 x4 = Bool.true → x2 x5 = Bool.true) → (∀ (x5 : Fin (14 : ℕ) → Bool), ((∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ x1 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) ∧ ∀ (x6 : Fin (14 : ℕ)), x5 x6 = Bool.true → ¬∃ (x8 : Fin (14 : ℕ)) (x9 : Fin (14 : ℕ)), (↑x8, ↑x9) ∈ x1 ∧ Function.update x5 x6 Bool.false x8 = Bool.true ∧ Function.update x5 x6 Bool.false x9 = Bool.true) → x5 (0 : Fin (14 : ℕ)) = Bool.false ∨ x5 (7 : Fin (14 : ℕ)) = Bool.false → (x2 x5 = Bool.true ↔ ∃ (x8 : Fin (14 : ℕ)) (x9 : Fin (14 : ℕ)), (↑x8, ↑x9) ∈ x1 ∧ x5 x8 = Bool.true ∧ x5 x9 = Bool.true)) → ∀ (x6 : Fin (14 : ℕ) → Bool), (∃ (x7 : Fin (14 : ℕ)) (x8 : Fin (14 : ℕ)), (↑x7, ↑x8) ∈ x1 ∧ (x7 ≠ (0 : Fin (14 : ℕ)) ∨ x8 ≠ (7 : Fin (14 : ℕ))) ∧ x6 x7 = Bool.true ∧ x6 x8 = Bool.true) → x2 x6 = Bool.true := by
  intro E f hlt hmono hmin x hx
  obtain ⟨a, b, hab, hne07, ha, hb⟩ := hx
  have hall := List.all_eq_true.1 hlt
  have hlt' : ∀ (u v : Fin 14), (u.1, v.1) ∈ E → u.1 < v.1 := fun u v h => of_decide_eq_true (hall _ h)
  have habne : a ≠ b := fun e => by have := hlt' a b hab; rw [e] at this; omega
  obtain ⟨e, he⟩ : ∃ e : Fin 14 → Bool, e = fun i => decide (i = a ∨ i = b) := ⟨_, rfl⟩
  have hea : e a = true := by rw [he]; exact decide_eq_true (Or.inl rfl)
  have heb : e b = true := by rw [he]; exact decide_eq_true (Or.inr rfl)
  have hfe : f e = true := by
    apply (hmin e ⟨⟨a, b, hab, hea, heb⟩, ?_⟩ ?_).2 ⟨a, b, hab, hea, heb⟩
    · intro t ht
      rintro ⟨u, v, huv, hu, hv⟩
      have huv' := hlt' u v huv
      have hu1 : u ≠ t := by
        intro h1; rw [h1, Function.update_self] at hu; exact absurd hu (by decide)
      have hv1 : v ≠ t := by
        intro h1; rw [h1, Function.update_self] at hv; exact absurd hv (by decide)
      rw [Function.update_of_ne hu1] at hu
      rw [Function.update_of_ne hv1] at hv
      rw [he] at hu hv ht
      have hu2 := of_decide_eq_true hu
      have hv2 := of_decide_eq_true hv
      have ht2 := of_decide_eq_true ht
      have huv2 : u ≠ v := fun h1 => by rw [h1] at huv'; omega
      rcases hu2 with h1 | h1 <;> rcases hv2 with h2 | h2 <;> rcases ht2 with h3 | h3 <;>
        first
          | exact huv2 (h1.trans h2.symm)
          | exact hu1 (h1.trans h3.symm)
          | exact hv1 (h2.trans h3.symm)
    · by_contra hboth
      rw [not_or] at hboth
      have h0 : e 0 = true := by
        cases h : e 0 with
        | true => rfl
        | false => exact absurd h hboth.1
      have h7 : e 7 = true := by
        cases h : e 7 with
        | true => rfl
        | false => exact absurd h hboth.2
      rw [he] at h0 h7
      have h0' := of_decide_eq_true h0
      have h7' := of_decide_eq_true h7
      have hab' := hlt' a b hab
      rcases h0' with h1 | h1 <;> rcases h7' with h2 | h2
      · rw [← h1] at h2; exact absurd h2 (by decide)
      · rcases hne07 with h3 | h3
        · exact h3 h1.symm
        · exact h3 h2.symm
      · rw [← h1, ← h2] at hab'; exact absurd hab' (by decide)
      · rw [← h1] at h2; exact absurd h2 (by decide)
  apply hmono e x ?_ hfe
  intro t ht
  rw [he] at ht
  rcases of_decide_eq_true ht with h1 | h1
  · rw [h1]; exact ha
  · rw [h1]; exact hb
