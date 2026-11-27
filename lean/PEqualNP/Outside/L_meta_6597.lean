import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6597 : ∀ (x1 x2 x3 x4 : ℕ) (x5 : Finset (Fin x1 × Fin x1)) (x6 : ℕ → Set ((Fin x1 × Fin x1) × Finset (Fin x1))),   have x7 : ℕ → Fin x1 × Fin x1 → Prop := fun (x7 : ℕ) (x8 : Fin x1 × Fin x1) => (x8, ∅) ∈ x6 x7 ∧ (x8, {x8.2}) ∈ x6 x7;   x4 < x2 + x3 → (∀ x9 ∈ x5, x7 x4 x9) → (∀ x10 < x2, ∀ x12 ∈ x5, ¬x7 x10 x12) → (24 : ℕ) * x3 < x5.card → ∃ x12 < x3, ∃ x13 ⊆ x5, (24 : ℕ) < x13.card ∧ ∀ x14 ∈ x13, x7 (x2 + x12) x14 ∧ ∀ x16 < x2 + x12, ¬x7 x16 x14 := by
  intro N n m w0 E S P hw0 hall hlow hcard
  classical
  have hf : ∀ e ∈ E, (∃ w, P w e) := fun e he => ⟨w0, hall e he⟩
  have hfind : ∀ e (he : e ∈ E), n ≤ Nat.find (hf e he) ∧ Nat.find (hf e he) ≤ w0 := by
    intro e he
    refine ⟨?_, Nat.find_min' _ (hall e he)⟩
    by_contra hc
    push_neg at hc
    exact hlow _ hc e he (Nat.find_spec (hf e he))
  have hmaps : ∀ e ∈ E, (if h : ∃ w, P w e then Nat.find h - n else 0) ∈ Finset.range m := by
    intro e he
    have h1 := hfind e he
    rw [dif_pos (hf e he), Finset.mem_range]
    omega
  obtain ⟨j, hj, hbig⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (n := 24) hmaps
    (by rw [Finset.card_range]; omega)
  refine ⟨j, Finset.mem_range.1 hj,
    E.filter (fun e => (if h : ∃ w, P w e then Nat.find h - n else 0) = j),
    Finset.filter_subset _ _, hbig, ?_⟩
  intro e he
  obtain ⟨heE, hfe⟩ := Finset.mem_filter.1 he
  have hb := hfind e heE
  rw [dif_pos (hf e heE)] at hfe
  have hw : Nat.find (hf e heE) = n + j := by omega
  have hs := Nat.find_spec (hf e heE)
  rw [hw] at hs
  refine ⟨hs, fun w hwlt => ?_⟩
  exact Nat.find_min (hf e heE) (by omega)
