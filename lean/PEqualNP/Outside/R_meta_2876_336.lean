import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2876_336
    (search : let P := fun x : Fin 14 → Bool => ∃ u v : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true
      ∃ (C : Circuit) (o : GateOp) (a b : ℕ), Monotone2 C ∧ C.size ≤ 25 ∧
      14 ≤ a ∧ a < b ∧ b < 14 + C.size ∧
      let w := fun i (z : Fin 14 → Bool) => (C.wires (List.ofFn z)).getD i false
      (∀ z, o.eval [w a z, w b z] = true ↔ P z) ∧
      ∃ X Y, ((o = .or ∧ Minimal P X ∧ Minimal P Y) ∨
        (o = .and ∧ Maximal (fun z => ¬ P z) X ∧ Maximal (fun z => ¬ P z) Y)) ∧
        w a X ≠ w b X ∧ w a X = w b Y ∧ w b X = w a Y)
    (points : (let P := fun x : Fin 14 → Bool => ∃ u v : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true
      ∀ x y, Minimal P x → Minimal P y → x ≠ y →
      ∃ (s : Equiv.Perm (Fin 14)) (m : ℕ × ℕ), m ∈ ([(129, 130), (129, 260), (129, 544)] : List (ℕ × ℕ)) ∧
        (∀ z, P (z ∘ s) ↔ P z) ∧
        ((x = (fun i => m.1.testBit (s i).val) ∧ y = (fun i => m.2.testBit (s i).val)) ∨
         (y = (fun i => m.1.testBit (s i).val) ∧ x = (fun i => m.2.testBit (s i).val)))))
    (independentSets : (let P := fun x : Fin 14 → Bool => ∃ u v : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true
      ∀ x y, Maximal (fun z => ¬ P z) x → Maximal (fun z => ¬ P z) y → x ≠ y →
      ∃ (s : Equiv.Perm (Fin 14)) (m : ℕ × ℕ), m ∈ ([(127, 244), (127, 432), (127, 3716), (127, 16256), (244, 314), (244, 432), (244, 792), (244, 1290), (244, 3716), (244, 7426), (432, 660), (432, 1220), (432, 1548)] : List (ℕ × ℕ)) ∧
        (∀ z, P (z ∘ s) ↔ P z) ∧
        ((x = (fun i => m.1.testBit (s i).val) ∧ y = (fun i => m.2.testBit (s i).val)) ∨
         (y = (fun i => m.1.testBit (s i).val) ∧ x = (fun i => m.2.testBit (s i).val)))))
    (relabel : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ s : Equiv.Perm (Fin n),
      ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧ ∀ i (x : Fin n → Bool), n ≤ i →
        (D.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn (x ∘ s))).getD i false) :

let P := fun x : Fin 14 → Bool => ∃ u v : Fin 14, (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List ℕ).getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true
      ∃ (D : Circuit) (op : GateOp) (a b : ℕ) (m : ℕ × ℕ),
        Monotone2 D ∧ D.size ≤ 25 ∧
        14 ≤ a ∧ a < b ∧ b < 14 + D.size ∧
        ((op = .or ∧ m ∈ ([(129,130),(129,260),(129,544)] : List (ℕ × ℕ)))
          ∨ (op = .and ∧ m ∈ ([(127,244),(127,432),(127,3716),(127,16256),(244,314),(244,432),
            (244,792),(244,1290),(244,3716),(244,7426),(432,660),(432,1220),(432,1548)]
          : List (ℕ × ℕ)))) ∧
        let read := fun (w : ℕ) (x : Fin 14 → Bool) => (D.wires (List.ofFn x)).getD w false
        let X := fun i : Fin 14 => m.1.testBit i.val
        let Y := fun i : Fin 14 => m.2.testBit i.val
        let F := fun x => op.eval [read a x, read b x]
        read a X ≠ read b X ∧ read a X = read b Y ∧ read b X = read a Y ∧
        (∀ x, Minimal P x → (op = .or ∧ (x = X ∨ x = Y)) ∨ F x = true) ∧
        (∀ x, Maximal (fun z => ¬ P z) x → (op = .and ∧ (x = X ∨ x = Y)) ∨ F x = false) := by
  let P := fun x : Fin 14 → Bool => ∃ u v : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u.val 0).testBit v.val = true ∧ x u = true ∧ x v = true
  obtain ⟨C, o, a, b, hC, size, ha, hab, hb, full, X, Y, kind, hdiff, hcross, hswap⟩ := search
  have hxy : X ≠ Y := by
    intro e
    subst Y
    exact hdiff hcross
  have hn : ∃ (s : Equiv.Perm (Fin 14)) (m : ℕ × ℕ),
      ((o = .or ∧ m ∈ ([(129, 130), (129, 260), (129, 544)] : List (ℕ × ℕ))) ∨ (o = .and ∧ m ∈ ([(127, 244), (127, 432), (127, 3716), (127, 16256), (244, 314), (244, 432), (244, 792), (244, 1290), (244, 3716), (244, 7426), (432, 660), (432, 1220), (432, 1548)] : List (ℕ × ℕ)))) ∧
      (∀ z, P (z ∘ s) ↔ P z) ∧
      ((X = (fun i => m.1.testBit (s i).val) ∧ Y = (fun i => m.2.testBit (s i).val)) ∨
       (Y = (fun i => m.1.testBit (s i).val) ∧ X = (fun i => m.2.testBit (s i).val))) := by
    rcases kind with ⟨ho,hx,hy⟩ | ⟨ho,hx,hy⟩
    · obtain ⟨s,m,hm,hp,hr⟩ := points X Y hx hy hxy
      exact ⟨s,m,Or.inl ⟨ho,hm⟩,hp,hr⟩
    · obtain ⟨s,m,hm,hp,hr⟩ := independentSets X Y hx hy hxy
      exact ⟨s,m,Or.inr ⟨ho,hm⟩,hp,hr⟩
  obtain ⟨s,m,hm,hp,hr⟩ := hn
  obtain ⟨D,hD,hsize,hw⟩ := relabel 14 C hC s
  refine ⟨D,o,a,b,m,hD,hsize.trans_le size,ha,hab,by simpa [hsize] using hb,hm,?_⟩
  let A : Fin 14 → Bool := fun i => m.1.testBit i.val
  let B : Fin 14 → Bool := fun i => m.2.testBit i.val
  let w := fun i (z : Fin 14 → Bool) => (D.wires (List.ofFn z)).getD i false
  have wb := fun z => hw b z (Nat.le_trans ha (Nat.le_of_lt hab))
  have wa := fun z => hw a z ha
  have pair : w a A ≠ w b A ∧ w a A = w b B ∧ w b A = w a B := by
    dsimp only [w]
    rw [wa A, wb A, wa B, wb B]
    change (X = A ∘ s ∧ Y = B ∘ s) ∨ (Y = A ∘ s ∧ X = B ∘ s) at hr
    rcases hr with ⟨hx,hy⟩ | ⟨hy,hx⟩
    · rw [← hx, ← hy]
      exact ⟨hdiff,hcross,hswap⟩
    · rw [← hy, ← hx]
      exact ⟨by intro e; exact hdiff (hcross.trans (e.symm.trans hswap.symm)), hswap.symm, hcross.symm⟩
  have correct (z : Fin 14 → Bool) : o.eval [w a z, w b z] = true ↔ P z := by
    dsimp only [w]
    rw [wa z, wb z]
    exact (full (z ∘ s)).trans (hp z)
  refine ⟨pair.1,pair.2.1,pair.2.2,?_,?_⟩
  · intro x hx
    exact Or.inr ((correct x).2 hx.1)
  · intro x hx
    exact Or.inr (Bool.eq_false_iff.mpr (fun e => hx.1 ((correct x).1 e)))

