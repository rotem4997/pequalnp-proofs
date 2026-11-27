import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7047 : ∀ (x1 x2 : ℕ) (x3 : List ℕ) (x4 : ℕ → ℕ), x3.length = x1 → x1 + x2 ≤ (64 : ℕ) → (∀ x7 < x1, x3.getD x7 (0 : ℕ) = x4 x7) → (∀ x8 < x2, ∃ (x10 : ℕ) (x11 : ℕ) (x12 : Bool), x10 < x1 + x8 ∧ x11 < x1 + x8 ∧ x4 (x1 + x8) = if x12 = Bool.true then x4 x10 ||| x4 x11 else x4 x10 &&& x4 x11) → ∃ (x9 : List (Fin (8192 : ℕ))), x9.length = x2 ∧ ∀ x10 < x1 + x2, (List.foldl (fun (x12 : List ℕ) (x13 : Fin (8192 : ℕ)) => x12 ++ [if ↑x13 < (4096 : ℕ) then x12.getD (↑x13 % (64 : ℕ)) (0 : ℕ) &&& x12.getD (↑x13 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ) else x12.getD (↑x13 % (64 : ℕ)) (0 : ℕ) ||| x12.getD (↑x13 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ)]) x3 x9).getD x10 (0 : ℕ) = x4 x10 := by
  intro n m L v hlen hnm hL hg
  classical
  have hc : ∀ j, ∃ c : Fin 8192, j < m → ∃ (a : ℕ) (b : ℕ) (o : Bool), a < n + j ∧ b < n + j ∧
      (v (n + j) = if o = true then v a ||| v b else v a &&& v b) ∧
      (c : ℕ) = a + 64 * b + (if o = true then 4096 else 0) := by
    intro j
    by_cases hj : j < m
    · obtain ⟨a, b, o, ha, hb, hv⟩ := hg j hj
      exact ⟨⟨a + 64 * b + (if o = true then 4096 else 0), by split <;> omega⟩,
        fun _ => ⟨a, b, o, ha, hb, hv, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose c hc using hc
  have hL0 : L = (List.range n).map v := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    have h3 := hL i (by rw [← hlen]; exact h1)
    rw [List.getD_eq_getElem _ _ h1] at h3
    exact h3
  have gA : ∀ t i, i < t → ((List.range t).map v).getD i 0 = v i := by
    intro t i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  have key : ∀ k, k ≤ m → List.foldl (fun (S : List ℕ) (z : Fin 8192) =>
      S ++ [if (z : ℕ) < 4096 then S.getD ((z : ℕ) % 64) 0 &&& S.getD ((z : ℕ) / 64 % 64) 0
        else S.getD ((z : ℕ) % 64) 0 ||| S.getD ((z : ℕ) / 64 % 64) 0]) L ((List.range k).map c)
      = (List.range (n + k)).map v := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa using hL0
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
      obtain ⟨a, b, o, ha, hb, hv, hcode⟩ := hc k (by omega)
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [show n + (k + 1) = n + k + 1 from rfl, List.range_succ, List.map_append]
      congr 1
      simp only [List.map_cons, List.map_nil]
      congr 1
      have e1 : (c k : ℕ) % 64 = a := by rw [hcode]; split <;> omega
      have e2 : (c k : ℕ) / 64 % 64 = b := by rw [hcode]; split <;> omega
      rw [e1, e2, gA _ a ha, gA _ b hb, hv]
      cases o
      · have h4 : (c k : ℕ) < 4096 := by rw [hcode]; simp; omega
        simp [h4]
      · have h4 : ¬ (c k : ℕ) < 4096 := by rw [hcode]; simp
        simp [h4]
  refine ⟨(List.range m).map c, by simp, fun i hi => ?_⟩
  rw [key m le_rfl]
  exact gA _ i hi
