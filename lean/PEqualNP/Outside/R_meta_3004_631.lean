import Mathlib
import PEqualNP.Defs

-- Point and line duality and incidence-preserving relabelings give three pair representatives.
-- The middle program may repeat values. Its last two available operands must cover the target
-- by an OR or intersect at the target by an AND.
set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_3004_631
    (search :
      let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      let step := fun (ws : List ℕ) (z : ℕ) =>
        ∃ a ∈ ws, ∃ b ∈ ws, z = a &&& b ∨ z = a ||| b
      ∃ g ∈ ([17871361015808, 95274182876594239, 1, 284526031944024591, 72622777407897600, 241600541374316567] : List ℕ), ∃ M : List ℕ,
        M.length ≤ 24 ∧ (∀ i : Fin M.length, step ((g :: A) ++ M.take i.val) (M.get i)) ∧
          step ((g :: A) ++ M) 2097151)
    (compact :
      let step := fun (ws : List ℕ) (z : ℕ) =>
        ∃ a ∈ ws, ∃ b ∈ ws, z = a &&& b ∨ z = a ||| b
      let valid := fun (A S : List ℕ) =>
        ∀ i : Fin S.length, step (A ++ S.take i.val) (S.get i)
      ∀ (A : List ℕ) (g t : ℕ) (M : List ℕ), t ∉ A →
        step A g → valid (g :: A) M → step ((g :: A) ++ M) t →
        ∃ S : List ℕ, S.length ≤ M.length + 2 ∧ S.Nodup ∧
          (∀ z ∈ S, z ∉ A) ∧ t ∈ S ∧ valid A S) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x2 : List ℕ), x2.length ≤ (26 : ℕ) ∧ x2.Nodup ∧ (∀ x3 ∈ x2, x3 ∉ x1) ∧ (2097151 : ℕ) ∈ x2 ∧ ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5 := by
  let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let step := fun (ws : List ℕ) (z : ℕ) =>
    ∃ a ∈ ws, ∃ b ∈ ws, z = a &&& b ∨ z = a ||| b
  have first : ∀ g ∈ ([17871361015808, 95274182876594239, 1, 284526031944024591, 72622777407897600, 241600541374316567] : List ℕ), step A g := by decide +kernel
  have fresh : 2097151 ∉ A := by decide +kernel
  obtain ⟨g, hg, M, hm, legal, finish⟩ := search
  obtain ⟨S, bound, nd, outside, seen, steps⟩ :=
    compact A g 2097151 M fresh (first g hg) legal finish
  exact ⟨S, by omega, nd, outside, seen, steps⟩
