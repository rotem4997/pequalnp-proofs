import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3511_401
    (normalize : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (C : Circuit),
      0 < s → (∀ r ∈ rows, r < 2^n) → Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = g r) →
      ∃ k < enc2CubeCount n s, FormulaSat (enc2 n s g rows ++ enc2Cube n s k))
    (certificates : ∀ (v : Fin 9) (k : ℕ), k < enc2CubeCount 11 13 →
      let rows : List ℕ := [3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402]
      let pos : List ℕ := [3,6,12,17,24,33,66,132,160,264,288,320]
      let pack := fun (m : ℕ) =>
        let uv := m.testBit 0 || m.testBit 4
        m + 512 * uv.toNat + 1024 * (uv || m.testBit v.val).toNat
      ¬ FormulaSat (enc2 11 13 (fun m => pos.contains (m % 512)) (rows.map pack) ++
        enc2Cube 11 13 k)) :
    ∀ (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     (∀ x4 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x6 : Fin (9 : ℕ) → Bool := fun (x6 : Fin (9 : ℕ)) => x4.testBit ↑x6;         x2.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x1]) = Decidable.decide (x4 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (14 : ℕ) ≤ x2.size := by
  intro v C hC test
  by_contra! small
  let rows : List ℕ := [3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402]
  let pos : List ℕ := [3,6,12,17,24,33,66,132,160,264,288,320]
  let pack (m : ℕ) :=
    let uv := m.testBit 0 || m.testBit 4
    m + 512 * uv.toNat + 1024 * (uv || m.testBit v.val).toNat
  let assignment (m : ℕ) :=
    let x := fun i : Fin 9 => m.testBit i.val
    List.ofFn x ++ [x 0 || x 4, x 0 || x 4 || x v]
  have data : ∀ m ∈ rows, pack m < 2^11 ∧ pack m % 512 = m ∧
      (List.ofFn fun i : Fin 11 => (pack m).testBit i.val) = assignment m := by
    have checked : rows.all (fun m => decide
        (pack m < 2^11 ∧ pack m % 512 = m ∧
        (List.ofFn fun i : Fin 11 => (pack m).testBit i.val) = assignment m)) = true := by
      dsimp only [pack, assignment, rows]
      clear * - v
      revert v
      decide +kernel
    exact fun m hm => of_decide_eq_true (List.all_eq_true.mp checked m hm)
  have valid : ∀ r ∈ rows.map pack, r < 2^11 := by
    intro r hr
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hr
    exact (data m hm).1
  obtain ⟨k, hk, sat⟩ := normalize 11 13 (fun m => pos.contains (m % 512))
    (rows.map pack) C (by decide) valid hC (by omega) (by
      intro r hr
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hr
      rw [(data m hm).2.1, (data m hm).2.2]
      simpa [assignment, pos, List.contains_iff_mem] using test m hm)
  exact certificates v k hk sat
