import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2436_684
    (reads : ∀ (j : Fin 42) (a b : Fin 43) (C : Circuit), (j = 1 ∨ j = 21 ∨ j = 22) → a < b → (a,b) ≠ (0,j.castSucc) →
      (b = Fin.last 42 → a ≠ 0 ∧ a ≠ j.castSucc) →
      (∀ x : Fin 42 → Bool,
        let y : Fin 43 → Bool := Fin.lastCases (x 0 || x j) x
        C.eval (List.ofFn (Fin.lastCases (y a || y b) y)) = true ↔
        ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧
          x u = true ∧ x v = true) → ∀ i : Fin 42, ([0,j.val,a.val,b.val] : List ℕ).count i.val = 1 →
        ∃ g ∈ C.gates, i.val ∈ g.inputs)
    (found : ∃ (j : Fin 42) (a b : Fin 43) (C : Circuit),
      (j = 1 ∨ j = 21 ∨ j = 22) ∧ (let row : List ℕ := if j = 1 then [81788948,0,4398145077304,0,4398077984768,4398059094016,4398256226304,4406653222912] else if j = 21 then [71303174,4398126202900,4398067482760] else [10485770,4398258323484,0,4402383429648]
      (row.getD (([0,1,2,3,4,21,22,23] : List ℕ).idxOf a.val) 0).testBit b.val = true) ∧
      Monotone2 C ∧ ReadsBack 44 C ∧ C.size ≤ 122 ∧ ∀ x : Fin 42 → Bool,
        let y : Fin 43 → Bool := Fin.lastCases (x 0 || x j) x
        C.eval (List.ofFn (Fin.lastCases (y a || y b) y)) = true ↔
        ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧
          x u = true ∧ x v = true) :
    ∃ (x1 : Fin (42 : ℕ)) (x2 : Fin (43 : ℕ)) (x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ))) ∧     x2 < x3 ∧       (x2, x3) ≠ ((0 : Fin (43 : ℕ)), x1.castSucc) ∧         (x3 = Fin.last (42 : ℕ) → x2 ≠ (0 : Fin (43 : ℕ)) ∧ x2 ≠ x1.castSucc) ∧           (∀ (x5 : Fin (42 : ℕ)), List.count ↑x5 [(0 : ℕ), ↑x1, ↑x2, ↑x3] = (1 : ℕ) → ∃ x7 ∈ x4.gates, ↑x5 ∈ x7.inputs) ∧             PEqualNP.MetaComplexity.Monotone2 x4 ∧               PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 ∧                 x4.size ≤ (122 : ℕ) ∧                   ∀ (x5 : Fin (42 : ℕ) → Bool),                     have x6 : Fin (43 : ℕ) → Bool := fun (x6 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x5 (0 : Fin (42 : ℕ)) || x5 x1) x5 x6;                     x4.eval (List.ofFn fun (x7 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 x2 || x6 x3) x6 x7) = Bool.true ↔ ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true := by
  obtain ⟨j,a,b,C,hj,hrep,hm,hback,hs,he⟩ := found
  have valid : ∀ (j : Fin 42) (a b : Fin 43), (j = 1 ∨ j = 21 ∨ j = 22) →
      (let row : List ℕ := if j = 1 then [81788948,0,4398145077304,0,4398077984768,4398059094016,4398256226304,4406653222912] else if j = 21 then [71303174,4398126202900,4398067482760] else [10485770,4398258323484,0,4402383429648]
      (row.getD (([0,1,2,3,4,21,22,23] : List ℕ).idxOf a.val) 0).testBit b.val = true) → a < b ∧ (a,b) ≠ (0,j.castSucc) ∧
        (b = Fin.last 42 → a ≠ 0 ∧ a ≠ j.castSucc) := by
    intro j a b hj
    rcases hj with rfl | rfl | rfl <;> revert a b <;> decide +kernel
  obtain ⟨hlt,hd,hb⟩ := valid j a b hj hrep
  exact ⟨j,a,b,C,hj,hlt,hd,hb,reads j a b C hj hlt hd hb he,hm,hback,hs,he⟩
