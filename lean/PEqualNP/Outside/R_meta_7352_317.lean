import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 500000 in
theorem PEqualNP.Outside.R_meta_7352_317 :
    (have x1 : List (ℕ × ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (ℕ × ℕ) := fun (x1 : List (ℕ × ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) =>   have x3 : ℕ × ℕ := x1.getD (x2.inputs.getD (0 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   have x4 : ℕ × ℕ := x1.getD (x2.inputs.getD (1 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   x1 ++ [(if x2.op.eval [Bool.false, Bool.true] = Bool.true then x3.1 ||| x4.1 else x3.1 &&& x4.1, x3.2 + x4.2)]; have x2 : List (ℕ × ℕ) := List.map (fun (x2 : ℕ) => (x2, (1 : ℕ))) [(288247147372494849 : ℕ), (15270196031913994 : ℕ), (58150374867024 : ℕ), (94946423956570756 : ℕ), (54820275478336544 : ℕ), (3870282840318208 : ℕ), (133410654208 : ℕ), (759033086762549255 : ℕ), (218716039641301048 : ℕ), (189725234880840128 : ℕ), (156548607028235776 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)]; have x3 : ℕ × ℕ → Prop := fun (x3 : ℕ × ℕ) => (∑ x4 : Fin (39 : ℕ), if x3.1.testBit ((21 : ℕ) + ↑x4) = Bool.true then (0 : ℕ) else [(99679525959508064 : ℕ), (144982790311510564 : ℕ), (41076143140 : ℕ)].getD (↑x4 / (15 : ℕ)) (0 : ℕ) >>> ((4 : ℕ) * (↑x4 % (15 : ℕ))) % (16 : ℕ)) ≤ (4 : ℕ) * x3.2; ∃ (x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) (x6 : ℕ),   x4.length ≤ (26 : ℕ) ∧     (∀ i : Fin x4.length, let g := x4.getD i.val ⟨.or, []⟩; (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14 + i.val ∧ b < 14 + i.val) ∧         x5 < x6 ∧           x6 < (14 : ℕ) + x4.length ∧             have x7 : List (ℕ × ℕ) := List.foldl x1 x2 x4;             have x8 : ℕ × ℕ := x7.getD x5 ((0 : ℕ), (0 : ℕ));             have x9 : ℕ × ℕ := x7.getD x6 ((0 : ℕ), (0 : ℕ));             x8.1 &&& x9.1 = (2097151 : ℕ) ∧ x8.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x9.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x3 x8 ∧ x3 x9) →
    (∀ (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ i : Fin gs.length, let g := gs.getD i.val ⟨.or, []⟩; (g.op = .and ∨ g.op = .or) ∧
        ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < n + i.val ∧ b < n + i.val) →
      PEqualNP.TopForm.IsAO2 n ⟨gs,0⟩ ∧ ∀ g ∈ gs, g.inputs.Nodup) →
    (have x1 : List (ℕ × ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (ℕ × ℕ) := fun (x1 : List (ℕ × ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) =>   have x3 : ℕ × ℕ := x1.getD (x2.inputs.getD (0 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   have x4 : ℕ × ℕ := x1.getD (x2.inputs.getD (1 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   x1 ++ [(if x2.op.eval [Bool.false, Bool.true] = Bool.true then x3.1 ||| x4.1 else x3.1 &&& x4.1, x3.2 + x4.2)]; have x2 : List (ℕ × ℕ) := List.map (fun (x2 : ℕ) => (x2, (1 : ℕ))) [(288247147372494849 : ℕ), (15270196031913994 : ℕ), (58150374867024 : ℕ), (94946423956570756 : ℕ), (54820275478336544 : ℕ), (3870282840318208 : ℕ), (133410654208 : ℕ), (759033086762549255 : ℕ), (218716039641301048 : ℕ), (189725234880840128 : ℕ), (156548607028235776 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)]; have x3 : ℕ × ℕ → Prop := fun (x3 : ℕ × ℕ) => (∑ x4 : Fin (39 : ℕ), if x3.1.testBit ((21 : ℕ) + ↑x4) = Bool.true then (0 : ℕ) else [(99679525959508064 : ℕ), (144982790311510564 : ℕ), (41076143140 : ℕ)].getD (↑x4 / (15 : ℕ)) (0 : ℕ) >>> ((4 : ℕ) * (↑x4 % (15 : ℕ))) % (16 : ℕ)) ≤ (4 : ℕ) * x3.2; ∃ (x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) (x6 : ℕ),   x4.length ≤ (26 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) { gates := x4, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧       (∀ x7 ∈ x4, x7.inputs.Nodup) ∧         x5 < x6 ∧           x6 < (14 : ℕ) + x4.length ∧             have x7 : List (ℕ × ℕ) := List.foldl x1 x2 x4;             have x8 : ℕ × ℕ := x7.getD x5 ((0 : ℕ), (0 : ℕ));             have x9 : ℕ × ℕ := x7.getD x6 ((0 : ℕ), (0 : ℕ));             x8.1 &&& x9.1 = (2097151 : ℕ) ∧ x8.1 >>> (58 : ℕ) = (0 : ℕ) ∧ x9.1 >>> (58 : ℕ) = (0 : ℕ) ∧ (31 : ℕ) ≤ x8.2 + x9.2 ∧ x3 x8 ∧ x3 x9) := by
  intro search shape
  dsimp only at search ⊢
  obtain ⟨gs, u, v, len, localShape, order, bound, join, ua, va, wu, wv⟩ := search
  obtain ⟨ao, distinct⟩ := shape 14 gs localShape
  refine ⟨gs, u, v, len, ao, distinct, order, bound, join, ua, va, ?_, wu, wv⟩
  let w (j : Fin 39) : ℕ :=
    [99679525959508064,144982790311510564,41076143140].getD (j.val / 15) 0 >>>
      (4 * (j.val % 15)) % 16
  have leafBound (a b : ℕ × ℕ)
      (join : a.1 &&& b.1 = 2097151) (ua : a.1 >>> 58 = 0) (va : b.1 >>> 58 = 0)
      (wu : (∑ j : Fin 39, if a.1.testBit (21+j.val) then 0 else w j) ≤ 4*a.2)
      (wv : (∑ j : Fin 39, if b.1.testBit (21+j.val) then 0 else w j) ≤ 4*b.2) :
      31 ≤ a.2+b.2 := by
    have upperBits (m k : ℕ) (hz : m >>> 58 = 0) (hk : 58 ≤ k) :
        m.testBit k = false := by
      have hh := congrArg (fun n : ℕ => n.testBit (k-58)) hz
      simpa [Nat.testBit_shiftRight, Nat.add_sub_of_le hk, Nat.add_comm] using hh
    have zeroBit (j : Fin 39) : (2097151 : ℕ).testBit (21+j.val) = false := by
      rw [← Nat.testBit_shiftRight]
      change (0 : ℕ).testBit j.val = false
      simp
    have row (j : Fin 39) :
        w j + (if 37 ≤ j.val then w j else 0) ≤
          (if a.1.testBit (21+j.val) then 0 else w j) +
          (if b.1.testBit (21+j.val) then 0 else w j) := by
      by_cases late : 37 ≤ j.val
      · have k : 58 ≤ 21+j.val := by omega
        simp [late, upperBits _ _ ua k, upperBits _ _ va k]
      · have same := congrArg (fun n : ℕ => n.testBit (21+j.val)) join
        change (a.1 &&& b.1).testBit (21+j.val) = _ at same
        rw [Nat.testBit_and, zeroBit] at same
        simp only [if_neg late, Nat.add_zero]
        cases hu : a.1.testBit (21+j.val) <;>
          cases hv : b.1.testBit (21+j.val) <;>
          simp [hu, hv] at same ⊢
    have combined := Finset.sum_le_sum (s := Finset.univ) (fun j _ => row j)
    have sumCert : (∑ j : Fin 39, (w j + (if 37 ≤ j.val then w j else 0))) = 121 := by
      dsimp [w]
      decide +kernel
    rw [sumCert, Finset.sum_add_distrib] at combined
    omega
  exact leafBound _ _ join ua va wu wv
