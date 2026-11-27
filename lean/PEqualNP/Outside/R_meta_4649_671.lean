import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.EquivFin

-- Normalize witnesses to 27 gates with distinct ordered operands and fixed output.
-- The output cannot read a primary input in either of its two operation cases.

set_option maxHeartbeats 950000 in
theorem PEqualNP.Outside.R_meta_4649_671
    (lastOr : ∀ (a b : Fin 27 → ℕ) (op : Fin 27 → Bool) (W : ℕ → Fin 62 → Bool),
      op 0 = false → op 26 = false → 14 ≤ a 26 → 14 ≤ b 26 →
      (∀ j : Fin 27, a j < b j ∧ b j < 14 + j.val) →
      (∀ j : Fin 14, W j.val = fun t => ([2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List ℕ).getD j.val 0 |>.testBit t.val) →
      (∀ (j : Fin 27) (t : Fin 62),
        W (14 + j.val) t = if op j then
          if t = 60 then (W (a j) 58 && W (b j) 60) || (W (a j) 60 && W (b j) 58)
          else if t = 61 then (W (a j) 59 && W (b j) 61) || (W (a j) 61 && W (b j) 59)
          else W (a j) t && W (b j) t
        else W (a j) t || W (b j) t) →
      W 40 ≠ fun t => decide (t.val < 21))
    (lastAnd : ∀ (a b : Fin 27 → ℕ) (op : Fin 27 → Bool) (W : ℕ → Fin 62 → Bool),
      op 0 = false → op 26 = true → 14 ≤ a 26 → 14 ≤ b 26 →
      (∀ j : Fin 27, a j < b j ∧ b j < 14 + j.val) →
      (∀ j : Fin 14, W j.val = fun t => ([2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List ℕ).getD j.val 0 |>.testBit t.val) →
      (∀ (j : Fin 27) (t : Fin 62),
        W (14 + j.val) t = if op j then
          if t = 60 then (W (a j) 58 && W (b j) 60) || (W (a j) 60 && W (b j) 58)
          else if t = 61 then (W (a j) 59 && W (b j) 61) || (W (a j) 61 && W (b j) 59)
          else W (a j) t && W (b j) t
        else W (a j) t || W (b j) t) →
      W 40 ≠ fun t => decide (t.val < 21)) :
    have x1 : List (Fin (62 : ℕ) → Bool) := List.map (fun (x1 : ℕ) (x2 : Fin (62 : ℕ)) => x1.testBit ↑x2) [(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)]; ¬∃ (x2 : List (Fin (62 : ℕ) → Bool)),     x2.length ≤ (27 : ℕ) ∧       (fun (x3 : Fin (62 : ℕ)) => Decidable.decide (↑x3 < (21 : ℕ))) ∈ x2 ∧         ∀ x3 < x2.length,           ∃ (x5 : ℕ) (x6 : ℕ),             x5 ≠ x6 ∧               x5 < (14 : ℕ) + x3 ∧                 x6 < (14 : ℕ) + x3 ∧                   have x7 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x5 fun (x7 : Fin (62 : ℕ)) => Bool.false;                   have x8 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x6 fun (x8 : Fin (62 : ℕ)) => Bool.false;                   ((x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => x7 x9 || x8 x9) ∨ (0 : ℕ) < x3 ∧ (x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => if x9 = (60 : Fin (62 : ℕ)) then x7 (58 : Fin (62 : ℕ)) && x8 (60 : Fin (62 : ℕ)) || x7 (60 : Fin (62 : ℕ)) && x8 (58 : Fin (62 : ℕ)) else if x9 = (61 : Fin (62 : ℕ)) then x7 (59 : Fin (62 : ℕ)) && x8 (61 : Fin (62 : ℕ)) || x7 (61 : Fin (62 : ℕ)) && x8 (59 : Fin (62 : ℕ)) else x7 x9 && x8 x9 := by
  classical
  dsimp only
  rintro ⟨s, small, member, valid⟩
  let z : Fin 62 → Bool := fun _ => false
  let goal : Fin 62 → Bool := fun t => decide (t.val < 21)
  let seed : List (Fin 62 → Bool) := ([2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List ℕ).map
    (fun v t => v.testBit t.val)
  let orVal (A B : Fin 62 → Bool) (t : Fin 62) := A t || B t
  let andVal (A B : Fin 62 → Bool) (t : Fin 62) :=
    if t = 60 then (A 58 && B 60) || (A 60 && B 58)
    else if t = 61 then (A 59 && B 61) || (A 61 && B 59)
    else A t && B t
  let old (i : ℕ) := (seed ++ s).getD i z
  have seedLen : seed.length = 14 := rfl
  have andSwap (A B : Fin 62 → Bool) : andVal A B = andVal B A := by
    funext t
    simp only [andVal]
    split <;> rename_i h₁
    · simp only [Bool.and_comm (A 58), Bool.and_comm (A 60), Bool.or_comm]
    · split
      · simp only [Bool.and_comm (A 59), Bool.and_comm (A 61), Bool.or_comm]
      · exact Bool.and_comm _ _
  have orSwap (A B : Fin 62 → Bool) : orVal A B = orVal B A := by
    funext t
    exact Bool.or_comm _ _
  have gate (j : ℕ) (hj : j < s.length) : ∃ a b : ℕ, ∃ op : Bool,
      a < b ∧ b < 14+j ∧ (j=0 → op=false) ∧
      s.getD j z = if op then andVal (old a) (old b) else orVal (old a) (old b) := by
    obtain ⟨a,b,ne,ha,hb,hop⟩ := valid j hj
    change s.getD j z = orVal (old a) (old b) ∨
      0 < j ∧ s.getD j z = andVal (old a) (old b) at hop
    by_cases h : a < b
    · rcases hop with ho | ⟨pos,hand⟩
      · exact ⟨a,b,false,h,hb,fun _ => rfl,ho⟩
      · exact ⟨a,b,true,h,hb,by omega,hand⟩
    · have strict : b < a := by omega
      rcases hop with ho | ⟨pos,hand⟩
      · exact ⟨b,a,false,strict,ha,fun _ => rfl,ho.trans (orSwap ..)⟩
      · exact ⟨b,a,true,strict,ha,by omega,hand.trans (andSwap ..)⟩
  obtain ⟨k, hk, atK⟩ := List.mem_iff_getElem.mp member
  have kBound : k < 27 := by omega
  have atK' : s.getD k z = goal := by simpa [List.getD_eq_getElem?_getD, hk] using atK
  let initial := s.take (k+1)
  let padded := initial ++ List.replicate (27-(k+1)) goal
  let W (i : ℕ) := (seed ++ padded).getD i z
  have preLen : initial.length = k+1 := by simp [initial, Nat.min_eq_left (by omega : k+1 ≤ s.length)]
  have preEq (i : ℕ) (hi : i < k+1) : initial.getD i z = s.getD i z := by
    simp [List.getD_eq_getElem?_getD, initial, hi]
  have padEq (i : ℕ) (hi : i < k+1) : padded.getD i z = s.getD i z := by
    rw [List.getD_append _ _ _ _ (by rwa [preLen])]
    exact preEq i hi
  have oldEq (i : ℕ) (hi : i < 14+(k+1)) : W i = old i := by
    by_cases h : i < 14
    · simp only [W, old, List.getD_append _ _ _ _ (by rwa [seedLen] : i < seed.length)]
    · have hi' : i - 14 < k+1 := by omega
      simp only [W, old, List.getD_eq_getElem?_getD, List.getElem?_append_right
        (by rw [seedLen]; omega : seed.length ≤ i), seedLen]
      simpa only [List.getD_eq_getElem?_getD] using padEq (i-14) hi'
  have tailEq (i : ℕ) (hi : k+1 ≤ i) (hi27 : i < 27) : padded.getD i z = goal := by
    unfold padded
    rw [List.getD_append_right _ _ _ _ (by rwa [preLen]), preLen]
    exact List.getD_replicate goal (by omega)
  have hit (i : ℕ) (hi : i < 27) : W (14+i) = padded.getD i z := by
    simp [W, List.getD_eq_getElem?_getD, List.getElem?_append_right
      (by rw [seedLen]; omega : seed.length ≤ 14+i), seedLen]
  have out : W 40 = goal := by
    rw [show 40 = 14+26 by rfl, hit 26 (by decide)]
    by_cases h : 26 < k+1
    · have e : k=26 := by omega
      rw [padEq 26 h, ← e, atK']
    · exact tailEq 26 (by omega) (by decide)
  have inputEq (j : Fin 14) : W j.val = fun t =>
      ([2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List ℕ).getD j.val 0 |>.testBit t.val := by
    have zero : z = (fun t : Fin 62 => (0 : ℕ).testBit t.val) := by funext t; simp [z]
    unfold W
    rw [List.getD_append _ _ _ _ (by rw [seedLen]; exact j.isLt), zero]
    unfold seed
    exact List.getD_map _ (0 : ℕ) _
  have normalized (j : Fin 27) : ∃ a b : ℕ, ∃ op : Bool,
      a < b ∧ b < 14+j.val ∧ (j=0 → op=false) ∧
      W (14+j.val) = if op then andVal (W a) (W b) else orVal (W a) (W b) := by
    let t := min j.val k
    have th : t < s.length := lt_of_le_of_lt (Nat.min_le_right ..) hk
    obtain ⟨a,b,op,hab,hb,hzero,hval⟩ := gate t th
    have tLeK : t ≤ k := Nat.min_le_right ..
    have tLeJ : t ≤ j.val := Nat.min_le_left ..
    refine ⟨a,b,op,hab,by omega,fun h => hzero (by subst j; simp [t]),?_⟩
    rw [oldEq a (by omega), oldEq b (by omega), ← hval, hit j.val j.isLt]
    by_cases h : j.val < k+1
    · have ht : t=j.val := Nat.min_eq_left (by omega)
      rw [ht, padEq j.val h]
    · have ht : t=k := Nat.min_eq_right (by omega)
      rw [ht, atK', tailEq j.val (by omega) j.isLt]
  choose a b op horder hbound hzero hlaw using normalized
  have laws (j : Fin 27) (t : Fin 62) := congrFun (hlaw j) t
  have law (j : Fin 27) (t : Fin 62) : W (14+j.val) t =
      if op j then
        if t=60 then (W (a j) 58 && W (b j) 60) || (W (a j) 60 && W (b j) 58)
        else if t=61 then (W (a j) 59 && W (b j) 61) || (W (a j) 61 && W (b j) 59)
        else W (a j) t && W (b j) t
      else W (a j) t || W (b j) t := by
    cases e : op j <;> simpa [e, andVal, orVal] using laws j t
  let bit (i : Fin 14) (t : Fin 62) := ([2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List ℕ).getD i.val 0 |>.testBit t.val
  have positiveOff : ∀ i : Fin 14, ∃ t : Fin 62, t.val < 21 ∧ bit i t = false := by
    decide +kernel
  have negativeOn : ∀ i : Fin 14, ∃ t : Fin 62, 21 ≤ t.val ∧ bit i t = true := by
    decide +kernel
  have outputSrc (w : ℕ) (src : w = a 26 ∨ w = b 26) : 14 ≤ w := by
    by_contra! bound
    let i : Fin 14 := ⟨w,bound⟩
    have raw (t : Fin 62) : W w t = bit i t := congrFun (inputEq i) t
    cases final : op 26
    · obtain ⟨t,ht,on⟩ := negativeOn i
      have eval := law 26 t
      change W 40 t = _ at eval
      have expected := congrFun out t
      change W 40 t = decide (t.val < 21) at expected
      rw [expected, ite_eq_right (by simpa using final)] at eval
      have off : ¬ t.val < 21 := by omega
      rcases src with h | h
      · rw [← h, raw t, on] at eval
        simp [off] at eval
      · rw [← h, raw t, on] at eval
        simp [off] at eval
    · obtain ⟨t,ht,off⟩ := positiveOff i
      have h60 : t ≠ 60 := fun e => by subst t; contradiction
      have h61 : t ≠ 61 := fun e => by subst t; contradiction
      have eval := law 26 t
      change W 40 t = _ at eval
      have expected := congrFun out t
      change W 40 t = decide (t.val < 21) at expected
      rw [expected, ite_eq_left final, ite_eq_right h60, ite_eq_right h61] at eval
      rcases src with h | h
      · rw [← h, raw t, off] at eval
        simp [ht] at eval
      · rw [← h, raw t, off] at eval
        simp [ht] at eval
  have za : 14 ≤ a 26 := outputSrc _ (Or.inl rfl)
  have zb : 14 ≤ b 26 := outputSrc _ (Or.inr rfl)
  cases final : op 26
  · exact lastOr a b op W (hzero 0 rfl) final za zb (fun j => ⟨horder j, hbound j⟩) inputEq law out
  · exact lastAnd a b op W (hzero 0 rfl) final za zb (fun j => ⟨horder j, hbound j⟩) inputEq law out
