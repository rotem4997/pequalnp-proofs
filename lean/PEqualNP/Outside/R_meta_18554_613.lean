import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_18554_613 :
  (∃ t : Fin 39 → BitVec 58,
    (∀ i : Fin 14, (t (Fin.ofNat 39 i.val)).toNat = ([189297016294346753, 155696362464247818, 218994303132237904, 183565875465421444, 229736628136977440, 270286071508582656, 288160007408715776, 95229015649943559, 55389823206162488, 14003410187583936, 8521481457152, 4292497062785024, 256463044608, 63038589501440] : List ℕ).getD i.val 0) ∧
    (∀ j : Fin 25, ∃ a b : Fin (14 + j.val),
      t (Fin.ofNat 39 (14 + j.val)) = t (Fin.ofNat 39 a.val) ||| t (Fin.ofNat 39 b.val) ∨ t (Fin.ofNat 39 (14 + j.val)) = t (Fin.ofNat 39 a.val) &&& t (Fin.ofNat 39 b.val)) ∧
    ∃ a b : Fin 39, t a ||| t b = 2097151 ∨ t a &&& t b = 2097151) →
  (∀ (W : List ℕ) (m : ℕ) (t : ℕ → ℕ),
    (∀ i < W.length, t i = W.getD i 0) →
    (∀ j < m, ∃ a < W.length + j, ∃ b < W.length + j,
      t (W.length + j) = t a ||| t b ∨ t (W.length + j) = t a &&& t b) →
    ∀ o < W.length + m, ∃ C : Circuit, C.size ≤ m ∧ IsAO2 W.length C ∧
      (C.gates.foldl (fun u g => u ++ [if g.op.eval [false, true] = true then
        (u.getD (g.inputs.getD 0 0) 0) ||| (u.getD (g.inputs.getD 1 0) 0) else
        (u.getD (g.inputs.getD 0 0) 0) &&& (u.getD (g.inputs.getD 1 0) 0)]) W).getD C.output 0 = t o) →
  (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (26 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧       (List.foldl               (fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>                 have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                 have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                 x2 ++ [if x3.op.eval [Bool.false, Bool.true] = Bool.true then x4 ||| x5 else x4 &&& x5])               [(189297016294346753 : ℕ), (155696362464247818 : ℕ), (218994303132237904 : ℕ), (183565875465421444 : ℕ), (229736628136977440 : ℕ), (270286071508582656 : ℕ), (288160007408715776 : ℕ), (95229015649943559 : ℕ), (55389823206162488 : ℕ), (14003410187583936 : ℕ), (8521481457152 : ℕ), (4292497062785024 : ℕ), (256463044608 : ℕ), (63038589501440 : ℕ)] x1.gates).getD           x1.output (0 : ℕ) =         (2097151 : ℕ)) := by
  rintro ⟨t, inp, step, a, b, last⟩ compile
  let W : List ℕ := [189297016294346753, 155696362464247818, 218994303132237904, 183565875465421444, 229736628136977440, 270286071508582656, 288160007408715776, 95229015649943559, 55389823206162488, 14003410187583936, 8521481457152, 4292497062785024, 256463044608, 63038589501440]
  have len : W.length = 14 := rfl
  let u (i : ℕ) := if i < 39 then (t (Fin.ofNat 39 i)).toNat else 2097151
  have hl : ∀ i < 39, u i = (t (Fin.ofNat 39 i)).toNat := fun i hi => by simp [u, hi]
  have input_ok : ∀ i < W.length, u i = W.getD i 0 := by
    intro i hi
    rw [len] at hi
    rw [hl i (by omega)]
    exact inp ⟨i, hi⟩
  have step_ok : ∀ j < 26, ∃ x < W.length + j, ∃ y < W.length + j,
      u (W.length + j) = u x ||| u y ∨ u (W.length + j) = u x &&& u y := by
    intro j hj
    rw [len]
    by_cases small : j < 25
    · obtain ⟨x, y, hor⟩ := step ⟨j, small⟩
      refine ⟨x.val, x.isLt, y.val, y.isLt, ?_⟩
      have hx : x.val < 14 + j := x.isLt
      have hy : y.val < 14 + j := y.isLt
      rw [hl _ (by omega), hl _ (by omega), hl _ (by omega)]
      rcases hor with hh | hh
      · exact Or.inl (by simpa only [BitVec.toNat_or] using congrArg BitVec.toNat hh)
      · exact Or.inr (by simpa only [BitVec.toNat_and] using congrArg BitVec.toNat hh)
    · have hj25 : j = 25 := by omega
      subst j
      refine ⟨a.val, a.isLt, b.val, b.isLt, ?_⟩
      rw [hl _ a.isLt, hl _ b.isLt]
      have ha : (Fin.ofNat 39 a.val) = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
      have hb : (Fin.ofNat 39 b.val) = b := Fin.ext (Nat.mod_eq_of_lt b.isLt)
      rw [ha, hb]
      have target : u (14 + 25) = (2097151 : BitVec 58).toNat := by change (if 39 < 39 then _ else 2097151) = _; rw [if_neg (by decide : ¬ 39 < 39)]; decide
      rw [target]
      rcases last with hh | hh
      · exact Or.inl (by simpa only [BitVec.toNat_or] using congrArg BitVec.toNat hh.symm)
      · exact Or.inr (by simpa only [BitVec.toNat_and] using congrArg BitVec.toNat hh.symm)
  obtain ⟨C, hs, hf, he⟩ := compile W 26 u input_ok step_ok 39 (by rw [len]; decide)
  exact ⟨C, hs, hf, he⟩
