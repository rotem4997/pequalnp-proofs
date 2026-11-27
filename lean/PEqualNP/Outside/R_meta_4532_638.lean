import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4532_638
    (frontier :
      let builds := fun (s l : List ℕ) => ∀ i : Fin l.length,
        ∃ a ∈ s ++ l.take i.val, ∃ b ∈ s ++ l.take i.val,
          l.get i = a &&& b ∨ l.get i = a ||| b
      ∀ (s l : List ℕ) (m k z : ℕ), l.length ≤ m + k → builds s l → z ∈ s ++ l →
        ∃ p : List ℕ, p.length ≤ m ∧ builds s p ∧
          ∃ w t : List ℕ, w.length ≤ k + 1 ∧ (∀ v ∈ w, v ∈ s ++ p) ∧
            t.length ≤ k ∧ builds w t ∧ z ∈ w ++ t)
    (search :
      let s : List ℕ := [63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 191866593364673099, 193001360500003407]
      ∃ l : List ℕ, l.length ≤ 22 ∧
        (∀ i : Fin l.length,
          ∃ a ∈ s ++ l.take i.val, ∃ b ∈ s ++ l.take i.val,
            l.get i = a &&& b ∨ l.get i = a ||| b) ∧
        ∃ z ∈ s ++ l, z ||| 7 = 2097151) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)] ++ [(191866593364673099 : ℕ), (193001360500003407 : ℕ), (7 : ℕ)]; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), ∃ x5 ∈ x2 ++ List.take (↑x4) x3, ∃ x6 ∈ x2 ++ List.take (↑x4) x3, x3.get x4 = x5 &&& x6 ∨ x3.get x4 = x5 ||| x6; ∃ (x3 : List ℕ), x3.length ≤ (15 : ℕ) ∧ x2 x1 x3 ∧ ∃ (x4 : List ℕ) (x5 : List ℕ), x4.length ≤ (8 : ℕ) ∧ (∀ x6 ∈ x4, x6 ∈ x1 ++ x3) ∧ x5.length ≤ (7 : ℕ) ∧ x2 x4 x5 ∧ ∃ x6 ∈ x4 ++ x5, x6 ||| (7 : ℕ) = (2097151 : ℕ) := by
  intro full builds
  let s : List ℕ := [63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 191866593364673099, 193001360500003407]
  have hs : s ⊆ full := by decide +kernel
  have included (l : List ℕ) : s ++ l ⊆ full ++ l := by
    intro z hz
    exact List.mem_append.mpr ((List.mem_append.mp hz).imp (fun h => hs h) id)
  obtain ⟨l, hlen, hl, z, hz, target⟩ := search
  have valid : builds full l := by
    intro i
    obtain ⟨a, ha, b, hb, hout⟩ := hl i
    exact ⟨a, included _ ha, b, included _ hb, hout⟩
  obtain ⟨p, hp, buildP, w, t, hw, transfer, ht, buildT, out⟩ :=
    frontier full l 15 7 z hlen valid (included _ hz)
  exact ⟨p, hp, buildP, w, t, hw, transfer, ht, buildT, z, out, target⟩
