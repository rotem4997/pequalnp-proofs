import Mathlib
import PEqualNP.Defs

-- Twelve edges at points 2, 4, 5 and 6 are the mask 2093504. The other nine edges are 3647.
-- An 11-gate star circuit builds 3647. A 14-gate circuit for 2093504 finishes the witness.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4614_1
    (block4 :
      let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      ∃ M : List ℕ, M.length ≤ 14 ∧
        (∀ i : Fin M.length, ∃ a ∈ A ++ M.take i.val, ∃ b ∈ A ++ M.take i.val,
          M.get i = a &&& b ∨ M.get i = a ||| b) ∧
        (2093504 : ℕ) ∈ A ++ M)
    (block3 :
      let A0 : List ℕ := [95229015649943559, 63038587666488, 4292497062759936, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      ∃ N : List ℕ, N.length ≤ 11 ∧
        (∀ i : Fin N.length, ∃ a ∈ A0 ++ N.take i.val, ∃ b ∈ A0 ++ N.take i.val,
          N.get i = a &&& b ∨ N.get i = a ||| b) ∧
        (3647 : ℕ) ∈ A0 ++ N) :
  have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List ℕ → ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 x4 : ℕ) => ∀ (x5 : ℕ), ∃ (x6 : ℕ), x3.testBit x6 = Bool.true ∧ x4.testBit x6 = x4.testBit x5 ∧ ∀ x7 ∈ x2, if x4.testBit x5 = Bool.true then x7.testBit x6 = Bool.true → x7.testBit x5 = Bool.true else x7.testBit x5 = Bool.true → x7.testBit x6 = Bool.true; have x3 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x4 : List ℕ) (x5 : List ℕ) (x6 : ℕ) (x7 : List ℕ), x4.length ≤ (14 : ℕ) ∧ x5.length ≤ (13 : ℕ) ∧ x7.length ≤ (12 : ℕ) ∧ x1 x3 x4 ∧ (∀ x8 ∈ x5, x8 ∈ x3 ++ x4) ∧ x2 x5 x6 (2097151 : ℕ) ∧ x1 (List.map (fun (x8 : ℕ) => x8 &&& x6) x5) x7 ∧ (2097151 : ℕ) &&& x6 ∈ List.map (fun (x8 : ℕ) => x8 &&& x6) x5 ++ x7 := by
  dsimp only at block4 block3
  obtain ⟨M, hMlen, hMleg, hMtgt⟩ := block4
  obtain ⟨N, hNlen, hNleg, hNtgt⟩ := block3
  let ports : List ℕ := [95229015649943559, 63038587666488, 4292497062759936, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let full : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let K : List ℕ := [2093504] ++ ports
  let q : ℕ := 2 ^ 58 - 1
  let U : List ℕ := N ++ [2097151]
  have hports : ports ⊆ full := by decide
  have hor : (2093504 : ℕ) ||| 3647 = 2097151 := by decide
  have hq58 : ∀ j : Fin 58, q.testBit j.val = Bool.true := by decide
  have hKlt : ∀ a ∈ K, a < 2 ^ 58 := by decide
  have hmap : K.map (fun x => x &&& q) = K := by decide
  have htq : (2097151 : ℕ) &&& q = 2097151 := by decide
  have h21 : (2097151 : ℕ).testBit 21 = Bool.false := by decide
  have hq21 : q.testBit 21 = Bool.true := by decide
  refine ⟨M, K, q, U, hMlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [K, ports]
  · simp [U]; omega
  · simpa [full] using hMleg
  · intro x hx
    rw [show K = [2093504] ++ ports from rfl] at hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_singleton] at hx
      subst hx
      simpa [full] using hMtgt
    · exact List.mem_append_left _ (hports hx)
  · intro i
    by_cases hi : i < 58
    · refine ⟨i, hq58 ⟨i, hi⟩, rfl, ?_⟩
      intro a ha
      split
      · exact fun h => h
      · exact fun h => h
    · have hi58 : 58 ≤ i := by omega
      have hti : (2097151 : ℕ).testBit i = Bool.false :=
        Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le (by decide : (2097151 : ℕ) < 2 ^ 21)
            (Nat.pow_le_pow_right (by decide) (le_trans (by decide : (21 : ℕ) ≤ 58) hi58)))
      refine ⟨21, hq21, ?_, ?_⟩
      · rw [h21, hti]
      · intro a ha
        have hf : a.testBit i = Bool.false :=
          Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le (hKlt a ha) (Nat.pow_le_pow_right (by decide) hi58))
        rw [hti]
        intro hbit
        simp [hf] at hbit
  · rw [hmap]
    intro i
    by_cases hi : i.val < N.length
    · let j : Fin N.length := ⟨i.val, hi⟩
      obtain ⟨a, ha, b, hb, hab⟩ := hNleg j
      have htake : (N ++ [2097151]).take i.val = N.take i.val :=
        List.take_append_of_le_length (le_of_lt hi)
      have hgetElem : (N ++ [2097151])[i.val]'(by simp; omega) = N[i.val] :=
        List.getElem_append_left hi
      have hget : U.get i = N.get j := by
        rw [List.get_eq_getElem, List.get_eq_getElem]
        simpa [U, j] using hgetElem
      have hin : ∀ {x : ℕ}, x ∈ ports ++ N.take i.val → x ∈ K ++ U.take i.val := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ hx)
        · exact List.mem_append_right _ (by simpa [U, htake] using hx)
      rcases hab with hab | hab
      · exact ⟨a, hin ha, b, hin hb, Or.inl (hget.trans hab)⟩
      · exact ⟨a, hin ha, b, hin hb, Or.inr (hget.trans hab)⟩
    · have hi0 : N.length ≤ i.val := by omega
      have hi1 : i.val = N.length := by
        have hlt : i.val < N.length + 1 := by simpa [U, List.length_append] using i.isLt
        omega
      have hget : U.get i = 2097151 := by
        rw [List.get_eq_getElem]
        have hidx : i.val - N.length = 0 := by omega
        have hge : (N ++ [2097151])[i.val]'(by simp; omega) = 2097151 := by
          simpa [hidx] using List.getElem_append_right (as := N) (bs := [2097151]) hi0
        simpa [U] using hge
      have htake : U.take i.val = N := by
        simp [U, hi1]
      refine ⟨2093504, ?_, 3647, ?_, Or.inr ?_⟩
      · exact List.mem_append_left _ (by simp [K])
      · rcases List.mem_append.mp hNtgt with hm | hm
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ hm)
        · exact List.mem_append_right _ (by simpa [htake] using hm)
      · rw [hget]; exact hor.symm
  · rw [hmap, htq]
    exact List.mem_append_right _ (by simp [U])
