import Mathlib
import PEqualNP.Defs

-- After 22 intermediate gates, a binary tree with three further gates suffices.
-- Test the balanced tree and the chain using the row masks of their leaves.
theorem PEqualNP.Outside.R_meta_3326_416
    (decode : ∀ (W : List ℕ) (t : ℕ),
      let mix := fun (P Q : ℕ → Prop) (z : ℕ) =>
        ∃ a, P a ∧ ∃ b, Q b ∧ (z = a &&& b ∨ z = a ||| b)
      let gen := fun (ws : List ℕ) => mix (fun a => a ∈ ws) (fun b => b ∈ ws)
      (let R := fun a => a ∈ W
      let B := mix R R
      mix B B t ∨ mix R (mix R B) t) →
      ∃ L : List ℕ, L.length ≤ 2 ∧ (∀ i : Fin L.length, gen (W ++ L.take i.val) (L.get i)) ∧
        gen (W ++ L) t)
    (search : let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      let mix := fun (P Q : ℕ → Prop) (z : ℕ) =>
        ∃ a, P a ∧ ∃ b, Q b ∧ (z = a &&& b ∨ z = a ||| b)
      let gen := fun (ws : List ℕ) => mix (fun a => a ∈ ws) (fun b => b ∈ ws)
      ∃ g ∈ ([17871361015808, 95274182876594239, 1, 284526031944024591, 72622777407897600, 241600541374316567] : List ℕ), ∃ P : List ℕ, P.length ≤ 22 ∧
        (∀ i : Fin P.length, gen ((g :: A) ++ P.take i.val) (P.get i)) ∧
        let W := (g :: A) ++ P
        let R := fun a => a ∈ W
        let B := mix R R
        mix B B 2097151 ∨ mix R (mix R B) 2097151) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; have x2 : List ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 : ℕ) => ∃ x4 ∈ x2, ∃ x5 ∈ x2, x3 = x4 &&& x5 ∨ x3 = x4 ||| x5; ∃ x3 ∈ [(17871361015808 : ℕ), (95274182876594239 : ℕ), (1 : ℕ), (284526031944024591 : ℕ), (72622777407897600 : ℕ), (241600541374316567 : ℕ)], ∃ (x4 : List ℕ), x4.length ≤ (24 : ℕ) ∧ (∀ (x5 : Fin x4.length), x2 (x3 :: x1 ++ List.take (↑x5) x4) (x4.get x5)) ∧ x2 (x3 :: x1 ++ x4) (2097151 : ℕ) := by
  let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let step (ws : List ℕ) (z : ℕ) := ∃ a ∈ ws, ∃ b ∈ ws, z = a &&& b ∨ z = a ||| b
  obtain ⟨g,hg,P,hp,legal,hit⟩ := search
  obtain ⟨L,hl,extra,finish⟩ := decode ((g :: A) ++ P) 2097151 hit
  refine ⟨g,hg,P ++ L,by simp; omega,?_,?_⟩
  · intro i
    change step ((g :: A) ++ (P ++ L).take i.val) ((P ++ L).get i)
    by_cases hi : i.val < P.length
    · have h := legal ⟨i.val,hi⟩
      change step ((g :: A) ++ P.take i.val) (P[i.val]) at h
      simpa only [List.get_eq_getElem,List.getElem_append_left hi,List.take_append_of_le_length hi.le] using h
    · have hj : i.val - P.length < L.length := by have := i.isLt; simp at this; omega
      have h := extra ⟨i.val-P.length,hj⟩
      change step (((g :: A) ++ P) ++ L.take (i.val-P.length)) (L[i.val-P.length]) at h
      simpa only [List.get_eq_getElem,List.getElem_append_right (Nat.le_of_not_gt hi),
        List.take_append,List.take_of_length_le (Nat.le_of_not_gt hi),List.append_assoc] using h
  · change step ((g :: A) ++ (P ++ L)) 2097151
    change step (((g :: A) ++ P) ++ L) 2097151 at finish
    simpa only [List.append_assoc] using finish
