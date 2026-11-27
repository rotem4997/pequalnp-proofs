import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3511_714
    (encode : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : List (BitVec 24)),
      PEqualNP.MetaComplexity.Monotone2 C →
      ∃ s : List (Bool × ℕ × ℕ), s.length = C.size ∧ ∀ i : Fin 24,
        ((s.foldl (fun (w : List (BitVec 24)) (g : Bool × ℕ × ℕ) =>
      w ++ [if g.1 then w.getD g.2.1 0 ||| w.getD g.2.2 0
        else w.getD g.2.1 0 &&& w.getD g.2.2 0])
          (0 :: BitVec.allOnes 24 :: w)).getD (C.output + 2) 0).getLsbD i =
            C.eval (w.map fun b => b.getLsbD i))
    (wordBound : ∀ (v : Fin 9) (s : List (Bool × ℕ × ℕ)) (out : ℕ),
      let raw : List (BitVec 24) := [0x428229, 0x8021c3, 0x0a1a06, 0x04a454, 0x890898, 0x104ce0, 0x218f00, 0xc1f000, 0xfe0000]
      let a := raw.getD 0 0 ||| raw.getD 4 0
      let w := raw ++ [a, a ||| raw.getD v.val 0]
      (s.foldl (fun (w : List (BitVec 24)) (g : Bool × ℕ × ℕ) =>
      w ++ [if g.1 then w.getD g.2.1 0 ||| w.getD g.2.2 0
        else w.getD g.2.1 0 &&& w.getD g.2.2 0])
        (0 :: BitVec.allOnes 24 :: w)).getD out 0 = 0x34513f → 14 ≤ s.length) :
    ∀ (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     (∀ x4 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x6 : Fin (9 : ℕ) → Bool := fun (x6 : Fin (9 : ℕ)) => x4.testBit ↑x6;         x2.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x1]) = Decidable.decide (x4 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (14 : ℕ) ≤ x2.size := by
  intro v C hm hc
  let rows : List ℕ := [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402]
  let positive : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
  let raw : List (BitVec 24) := [0x428229, 0x8021c3, 0x0a1a06, 0x04a454, 0x890898, 0x104ce0, 0x218f00, 0xc1f000, 0xfe0000]
  let a := raw.getD 0 0 ||| raw.getD 4 0
  let words (z : Fin 9) := raw ++ [a, a ||| raw.getD z.val 0]
  have inputEq : ∀ (z : Fin 9) (i : Fin 24),
      (words z).map (fun b => b.getLsbD i) =
        (let bits : Fin 9 → Bool := fun j => (rows.getD i.val 0).testBit j.val
         List.ofFn bits ++ [bits 0 || bits 4, bits 0 || bits 4 || bits z]) := by
    decide +kernel
  have targetEq : ∀ i : Fin 24,
      (0x34513f : BitVec 24).getLsbD i = decide (rows.getD i.val 0 ∈ positive) := by
    decide +kernel
  obtain ⟨s, hlen, heval⟩ := encode C (words v) hm
  rw [← hlen]
  apply wordBound v s (C.output + 2)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin 24 := ⟨i, hi⟩
  have outputBit := heval j
  rw [inputEq] at outputBit
  have rowMem : rows.getD j.val 0 ∈ rows := by
    have lengthBound : j.val < rows.length := by simpa [rows] using j.isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lengthBound]
    exact List.getElem_mem _
  exact outputBit.trans ((hc (rows.getD j.val 0) rowMem).trans (targetEq j).symm)
