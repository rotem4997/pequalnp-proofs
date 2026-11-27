import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5839

def L1 : List ℕ := [917681471495, 14877982776, 31886295695808, 257731333632, 42884715540480, 82789891276800, 248671168364609, 198670308900872, 158476001153026, 238332533547520, 176488259388544, 212188564308240, 280375465084964, 271282175770697, 280357743665737]

def L2 : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 191866593364673099, 193001360500003407, 7]

def sig : List ℕ := [0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 32, 33, 34, 35, 36, 37, 37, 38, 39, 39, 40, 41, 42, 44, 43, 44, 45, 45, 46, 46, 47, 47]

def P (y z : ℕ) : Prop :=
  z < 2 ^ 58 ∧ (∀ j, 3 ≤ j → j < 21 → y.testBit (sig.getD j 0) = true → z.testBit j = true) ∧
    (∀ j, 21 ≤ j → j < 58 → z.testBit j = true → y.testBit (sig.getD j 0) = true)

theorem P_and {y1 z1 y2 z2 : ℕ} (h1 : P y1 z1) (h2 : P y2 z2) : P (y1 &&& y2) (z1 &&& z2) := by
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  refine ⟨Nat.and_lt_two_pow _ a2, ?_, ?_⟩
  · intro j hj1 hj2 h
    simp only [Nat.testBit_and, Bool.and_eq_true] at h ⊢
    exact ⟨b1 j hj1 hj2 h.1, b2 j hj1 hj2 h.2⟩
  · intro j hj1 hj2 h
    simp only [Nat.testBit_and, Bool.and_eq_true] at h ⊢
    exact ⟨c1 j hj1 hj2 h.1, c2 j hj1 hj2 h.2⟩

theorem P_or {y1 z1 y2 z2 : ℕ} (h1 : P y1 z1) (h2 : P y2 z2) : P (y1 ||| y2) (z1 ||| z2) := by
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  refine ⟨Nat.or_lt_two_pow a1 a2, ?_, ?_⟩
  · intro j hj1 hj2 h
    simp only [Nat.testBit_or, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (b1 j hj1 hj2 h)
    · exact Or.inr (b2 j hj1 hj2 h)
  · intro j hj1 hj2 h
    simp only [Nat.testBit_or, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (c1 j hj1 hj2 h)
    · exact Or.inr (c2 j hj1 hj2 h)

def chk (y z : ℕ) : Bool :=
  decide (z < 2 ^ 58) && (List.range 58).all (fun j =>
    if j < 3 then true
    else if j < 21 then (!y.testBit (sig.getD j 0) || z.testBit j)
    else (!z.testBit j || y.testBit (sig.getD j 0)))

theorem chk_P {y z : ℕ} (h : chk y z = true) : P y z := by
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨h0, h1⟩ := h
  refine ⟨h0, ?_, ?_⟩
  · intro j hj1 hj2 hy
    have := h1 j (by omega)
    rw [if_neg (by omega), if_pos hj2, hy] at this
    simpa using this
  · intro j hj1 hj2 hz
    have := h1 j hj2
    rw [if_neg (by omega), if_neg (by omega), hz] at this
    simpa using this

theorem base_chk : ∀ k < 15, chk (L1.getD k 0) (L2.getD (k + 1) 0) = true := by
  decide +kernel

theorem L1_len : L1.length = 15 := by decide

theorem L2_len : L2.length = 17 := by decide

theorem base (u : ℕ) (hu : u ∈ L1) : ∃ v ∈ L2, P u v := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hu
  have hk1 : k < 15 := by rw [L1_len] at hk; exact hk
  have h := chk_P (base_chk k hk1)
  rw [List.getD_eq_getElem _ _ hk] at h
  have hk2 : k + 1 < L2.length := by rw [L2_len]; omega
  rw [List.getD_eq_getElem _ _ hk2] at h
  exact ⟨_, List.getElem_mem hk2, h⟩

theorem pow_ge {n j : ℕ} (h : n ≤ j) : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h

theorem final (z : ℕ) (h : P 262143 z) : z ||| 7 = 2097151 := by
  obtain ⟨h0, h1, h2⟩ := h
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or]
  by_cases hj : j < 3
  · have h7 : (7 : ℕ).testBit j = true := by interval_cases j <;> decide
    have h' : (2097151 : ℕ).testBit j = true := by interval_cases j <;> decide
    rw [h7, h', Bool.or_true]
  by_cases hj2 : j < 21
  · have hs : (262143 : ℕ).testBit (sig.getD j 0) = true := by
      interval_cases j <;> decide
    have hz := h1 j (by omega) hj2 hs
    have h' : (2097151 : ℕ).testBit j = true := by interval_cases j <;> decide
    rw [hz, h', Bool.true_or]
  have h7 : (7 : ℕ).testBit j = false := by
    apply Nat.testBit_eq_false_of_lt
    calc (7 : ℕ) < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := pow_ge (by omega)
  have h' : (2097151 : ℕ).testBit j = false := by
    apply Nat.testBit_eq_false_of_lt
    calc (2097151 : ℕ) < 2 ^ 21 := by norm_num
      _ ≤ 2 ^ j := pow_ge (by omega)
  by_cases hj3 : j < 58
  · have hs : (262143 : ℕ).testBit (sig.getD j 0) = false := by
      interval_cases j <;> decide
    have hz : z.testBit j = false := by
      cases hb : z.testBit j
      · rfl
      · have := h2 j (by omega) hj3 hb
        rw [hs] at this
        exact absurd this Bool.false_ne_true
    rw [hz, h7, h']; rfl
  · have hz : z.testBit j = false := by
      apply Nat.testBit_eq_false_of_lt
      calc z < 2 ^ 58 := h0
        _ ≤ 2 ^ j := pow_ge (by omega)
    rw [hz, h7, h']; rfl

def Gen (B l : List ℕ) : Prop :=
  ∀ (i : Fin l.length), ∃ a ∈ B ++ List.take (↑i) l, ∃ b ∈ B ++ List.take (↑i) l,
    l.get i = a &&& b ∨ l.get i = a ||| b

theorem key (l : List ℕ) (hl : Gen L1 l) : ∃ m : List ℕ, m.length = l.length ∧ Gen L2 m ∧
    ∀ (i : ℕ) (h1 : i < l.length) (h2 : i < m.length), P l[i] m[i] := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], rfl, fun i => i.elim0, fun i h1 => absurd h1 (by simp)⟩
  | append_singleton l a ih =>
    have hl' : Gen L1 l := by
      intro i
      obtain ⟨u, hu, v, hv, h⟩ := hl ⟨i.1, by simp only [List.length_append, List.length_singleton]; omega⟩
      have ht : List.take i.1 (l ++ [a]) = List.take i.1 l :=
        List.take_append_of_le_length (by omega)
      rw [ht] at hu hv
      refine ⟨u, hu, v, hv, ?_⟩
      have hg : (l ++ [a]).get ⟨i.1, by simp only [List.length_append, List.length_singleton]; omega⟩ = l.get i := by
        simp [List.getElem_append_left i.2]
      rw [hg] at h
      exact h
    obtain ⟨m, hml, hmg, hmP⟩ := ih hl'
    have partner : ∀ u ∈ L1 ++ l, ∃ u' ∈ L2 ++ m, P u u' := by
      intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · obtain ⟨v, hv, hP⟩ := base u hu
        exact ⟨v, List.mem_append_left _ hv, hP⟩
      · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hu
        exact ⟨m[k]'(by omega), List.mem_append_right _ (List.getElem_mem _),
          hmP k hk (by omega)⟩
    obtain ⟨u, hu, v, hv, h⟩ := hl ⟨l.length, by simp⟩
    have ht : List.take l.length (l ++ [a]) = l := by simp
    have hg : (l ++ [a]).get ⟨l.length, by simp⟩ = a := by simp
    rw [ht] at hu hv
    rw [hg] at h
    obtain ⟨u', hu', hPu⟩ := partner u hu
    obtain ⟨v', hv', hPv⟩ := partner v hv
    have hc : ∃ c, (c = u' &&& v' ∨ c = u' ||| v') ∧ P a c := by
      rcases h with h | h
      · exact ⟨_, Or.inl rfl, h ▸ P_and hPu hPv⟩
      · exact ⟨_, Or.inr rfl, h ▸ P_or hPu hPv⟩
    obtain ⟨c, hc1, hc2⟩ := hc
    refine ⟨m ++ [c], by simp [hml], ?_, ?_⟩
    · intro i
      by_cases hi : i.1 < m.length
      · obtain ⟨p, hp, q, hq, h⟩ := hmg ⟨i.1, hi⟩
        have ht2 : List.take i.1 (m ++ [c]) = List.take i.1 m :=
          List.take_append_of_le_length (by omega)
        rw [ht2]
        refine ⟨p, hp, q, hq, ?_⟩
        have hg2 : (m ++ [c]).get i = m.get ⟨i.1, hi⟩ := by
          simp [List.getElem_append_left hi]
        rw [hg2]
        exact h
      · have hi2 : i.1 = m.length := by
          have := i.2
          simp at this
          omega
        have ht2 : List.take i.1 (m ++ [c]) = m := by rw [hi2]; simp
        rw [ht2]
        refine ⟨u', hu', v', hv', ?_⟩
        have hg2 : (m ++ [c]).get i = c := by
          simp [hi2]
        rw [hg2]
        exact hc1
    · intro i h1 h2
      by_cases hi : i < l.length
      · rw [List.getElem_append_left hi, List.getElem_append_left (by omega)]
        exact hmP i hi (by omega)
      · have hi2 : i = l.length := by simp at h1; omega
        subst hi2
        rw [List.getElem_append_right (Nat.le_refl _), List.getElem_append_right (by omega)]
        simpa [hml] using hc2

theorem main : ∀ (x3 : List ℕ), Gen L1 x3 → ∃ (x5 : List ℕ), x5.length = x3.length ∧ Gen L2 x5 ∧
    ((262143 : ℕ) ∈ x3 → ∃ x7 ∈ x5, x7 ||| (7 : ℕ) = (2097151 : ℕ)) := by
  intro x3 h
  obtain ⟨m, hml, hmg, hmP⟩ := key x3 h
  refine ⟨m, hml, hmg, ?_⟩
  intro hmem
  obtain ⟨k, hk, hx⟩ := List.mem_iff_getElem.1 hmem
  have hP := hmP k hk (by omega)
  rw [hx] at hP
  exact ⟨m[k], List.getElem_mem _, final _ hP⟩

end PEqualNP.Outside.L_meta_5839

open PEqualNP.Outside.L_meta_5839 in
theorem PEqualNP.Outside.L_meta_5839 : have x1 : List ℕ := [(917681471495 : ℕ), (14877982776 : ℕ), (31886295695808 : ℕ), (257731333632 : ℕ), (42884715540480 : ℕ), (82789891276800 : ℕ), (248671168364609 : ℕ), (198670308900872 : ℕ), (158476001153026 : ℕ), (238332533547520 : ℕ), (176488259388544 : ℕ), (212188564308240 : ℕ), (280375465084964 : ℕ), (271282175770697 : ℕ), (280357743665737 : ℕ)]; have x2 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ), (191866593364673099 : ℕ), (193001360500003407 : ℕ), (7 : ℕ)]; ∀ (x3 : List ℕ), (∀ (x4 : Fin x3.length), ∃ x5 ∈ x1 ++ List.take (↑x4) x3, ∃ x6 ∈ x1 ++ List.take (↑x4) x3, x3.get x4 = x5 &&& x6 ∨ x3.get x4 = x5 ||| x6) → ∃ (x5 : List ℕ), x5.length = x3.length ∧ (∀ (x6 : Fin x5.length), ∃ x7 ∈ x2 ++ List.take (↑x6) x5, ∃ x8 ∈ x2 ++ List.take (↑x6) x5, x5.get x6 = x7 &&& x8 ∨ x5.get x6 = x7 ||| x8) ∧ ((262143 : ℕ) ∈ x3 → ∃ x7 ∈ x5, x7 ||| (7 : ℕ) = (2097151 : ℕ))
 := by
  exact main
