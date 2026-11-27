import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7511 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set ((Fin x1 → Bool) × (Fin x1 → Bool))),   let x5 : Type := (Fin x1 → Bool) × (Fin x1 → Bool);   have x6 : Fin x1 → Fin x1 → Bool := fun (x6 x7 : Fin x1) => Decidable.decide (x7 = x6);   x3 < x1 + x1 + x2 → (∀ (x8 : Fin x1), x4 ↑x8 = {x9 : x5 | x9.1 x8 = Bool.true} ∧ x4 (x1 + ↑x8) = {x9 : x5 | x9.2 x8 = Bool.true}) → (∀ x9 < x2, ∃ x11 < x1 + x1 + x9, ∃ x12 < x1 + x1 + x9, x4 (x1 + x1 + x9) = x4 x11 ∪ x4 x12 ∨ x4 (x1 + x1 + x9) = x4 x11 ∩ x4 x12) → (∀ (x10 : Fin x1), (x6 x10, fun (x11 : Fin x1) => Bool.false) ∉ x4 x3 ∧ (fun (x11 : Fin x1) => Bool.false, x6 x10) ∉ x4 x3) → ∃ (x11 : Finset ℕ), (∀ x12 ∈ x11, x12 < x2 ∧ ∃ x14 < x1 + x1 + x12, ∃ x15 < x1 + x1 + x12, x4 (x1 + x1 + x12) = x4 x14 ∩ x4 x15) ∧ ∀ (x12 : x5), x12 ∈ x4 x3 ↔ ∃ x13 ∈ x11, x12 ∈ x4 (x1 + x1 + x13) := by
  intro n m w0 W X e hw0 hin hg hH
  classical
  have key : ∀ w, w < n + n + m →
      (∀ i : Fin n, (e i, fun _ => false) ∉ W w ∧ ((fun _ => false), e i) ∉ W w) →
      ∃ J : Finset ℕ, (∀ j ∈ J, j < m ∧ ∃ a < n + n + j, ∃ b < n + n + j,
          W (n + n + j) = W a ∩ W b) ∧
        ∀ p : X, p ∈ W w ↔ ∃ j ∈ J, p ∈ W (n + n + j) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hHw
      by_cases h1 : w < n
      · exfalso
        have h3 := (hin ⟨w, h1⟩).1
        refine (hHw ⟨w, h1⟩).1 ?_
        show (e ⟨w, h1⟩, fun _ => false) ∈ W w
        rw [h3]
        exact decide_eq_true rfl
      · by_cases h2 : w < n + n
        · exfalso
          obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hk : k < n := by omega
          have h3 := (hin ⟨k, hk⟩).2
          refine (hHw ⟨k, hk⟩).2 ?_
          show ((fun _ => false), e ⟨k, hk⟩) ∈ W (n + k)
          rw [h3]
          exact decide_eq_true rfl
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + n + j := ⟨w - (n + n), by omega⟩
          obtain ⟨a, ha, b, hb, h | h⟩ := hg j (by omega)
          · have Ha : ∀ i : Fin n, (e i, fun _ => false) ∉ W a ∧ ((fun _ => false), e i) ∉ W a :=
              fun i => ⟨fun hc => (hHw i).1 (by rw [h]; exact Or.inl hc),
                fun hc => (hHw i).2 (by rw [h]; exact Or.inl hc)⟩
            have Hb : ∀ i : Fin n, (e i, fun _ => false) ∉ W b ∧ ((fun _ => false), e i) ∉ W b :=
              fun i => ⟨fun hc => (hHw i).1 (by rw [h]; exact Or.inr hc),
                fun hc => (hHw i).2 (by rw [h]; exact Or.inr hc)⟩
            obtain ⟨Ja, hJa, hpa⟩ := ih a ha (by omega) Ha
            obtain ⟨Jb, hJb, hpb⟩ := ih b hb (by omega) Hb
            refine ⟨Ja ∪ Jb, fun j' hj' => (Finset.mem_union.1 hj').elim (hJa j') (hJb j'),
              fun p => ?_⟩
            rw [h]
            constructor
            · rintro (hp | hp)
              · obtain ⟨j', hj', hp'⟩ := (hpa p).1 hp
                exact ⟨j', Finset.mem_union_left _ hj', hp'⟩
              · obtain ⟨j', hj', hp'⟩ := (hpb p).1 hp
                exact ⟨j', Finset.mem_union_right _ hj', hp'⟩
            · rintro ⟨j', hj', hp'⟩
              rcases Finset.mem_union.1 hj' with h3 | h3
              · exact Or.inl ((hpa p).2 ⟨j', h3, hp'⟩)
              · exact Or.inr ((hpb p).2 ⟨j', h3, hp'⟩)
          · refine ⟨{j}, fun j' hj' => ?_, fun p => by simp⟩
            rw [Finset.mem_singleton.1 hj']
            exact ⟨by omega, a, ha, b, hb, h⟩
  exact key w0 hw0 hH
