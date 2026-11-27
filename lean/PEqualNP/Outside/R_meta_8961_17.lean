import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_8961_17
    (preserve : ∀ (seed : List ℕ) (gs : List (Bool × Fin 32 × Fin 32))
        (value : List ℕ → (Bool × Fin 32 × Fin 32) → ℕ) (i : Fin seed.length),
      (gs.foldl (fun ws g => ws ++ [value ws g]) seed).getD i.val 0 = seed.getD i.val 0)
    (remaining : ∃ (gs : List (Bool × Fin 32 × Fin 32)) (terms : List (Fin 32 × Fin 32)),
      let ws := gs.foldl (fun (w : List ℕ) g => w ++ [if g.1 = true then
          w.getD g.2.1.val 0 &&& w.getD g.2.2.val 0 else
          w.getD g.2.1.val 0 ||| w.getD g.2.2.val 0])
        [2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128,
         26322415680, 344922804352, 414195942664, 581968119809, 1065151898146, 371245215936,
         582520731713, 1066477318818, 549755842560, 728266404032]
      let out := fun (p : Fin 32 × Fin 32) => ws.getD p.1.val 0 &&& ws.getD p.2.val 0
      gs.length + 2 * terms.length ≤ 15 ∧
        (∀ i : Fin gs.length, (gs.get i).2.1.val < 16 + i.val ∧ (gs.get i).2.2.val < 16 + i.val) ∧
        (gs.filter (·.1)).length = 1 ∧
        (∀ i : Fin gs.length, (gs.get i).1 = true →
          ws.getD (16 + i.val) 0 &&& 1099511562240 ≠ 0) ∧
        (∀ p ∈ terms, p.1.val < 16 + gs.length ∧ p.2.val < 16 + gs.length ∧
          out p &&& 1099511562240 = 0) ∧
        terms.foldl (fun n p => n ||| out p) 28864 = 65535) :
∃ (x1 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x2 : List (Fin (32 : ℕ) × Fin (32 : ℕ))),   have x3 : List ℕ := List.foldl (fun (x3 : List ℕ) (x4 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x3 ++ [if x4.1 = Bool.true then x3.getD ↑x4.2.1 (0 : ℕ) &&& x3.getD ↑x4.2.2 (0 : ℕ) else x3.getD ↑x4.2.1 (0 : ℕ) ||| x3.getD ↑x4.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)] x1;   have x4 : Fin (32 : ℕ) × Fin (32 : ℕ) → ℕ := fun (x4 : Fin (32 : ℕ) × Fin (32 : ℕ)) => x3.getD ↑x4.1 (0 : ℕ) &&& x3.getD ↑x4.2 (0 : ℕ);   x1.length + (2 : ℕ) * x2.length ≤ (22 : ℕ) ∧ x2 ≠ [] ∧ (∀ (x5 : Fin x1.length), ↑(x1.get x5).2.1 < (11 : ℕ) + ↑x5 ∧ ↑(x1.get x5).2.2 < (11 : ℕ) + ↑x5) ∧ (List.filter (fun (x5 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x5.1) x1).length = (2 : ℕ) ∧ (∀ (x5 : Fin x1.length), (x1.get x5).1 = Bool.true → x3.getD ((11 : ℕ) + ↑x5) (0 : ℕ) &&& (1099511562240 : ℕ) ≠ (0 : ℕ)) ∧ (∀ x5 ∈ x2, ↑x5.1 < (11 : ℕ) + x1.length ∧ ↑x5.2 < (11 : ℕ) + x1.length ∧ x4 x5 &&& (1099511562240 : ℕ) = (0 : ℕ)) ∧ List.foldl (fun (x5 : ℕ) (x6 : Fin (32 : ℕ) × Fin (32 : ℕ)) => x5 ||| x4 x6) (0 : ℕ) x2 = (65535 : ℕ) := by
  let roots : List ℕ := [2147418115, 663661903884, 34144976944, 728266375360, 21653750532,
     103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146]
  let head : List (Bool × Fin 32 × Fin 32) :=
    [(false, 6, 7), (false, 6, 9), (false, 7, 10), (true, 12, 13), (false, 3, 14)]
  let value := fun (w : List ℕ) (g : Bool × Fin 32 × Fin 32) =>
    if g.1 = true then w.getD g.2.1.val 0 &&& w.getD g.2.2.val 0
    else w.getD g.2.1.val 0 ||| w.getD g.2.2.val 0
  let step := fun (w : List ℕ) (g : Bool × Fin 32 × Fin 32) => w ++ [value w g]
  let seed : List ℕ := [2147418115, 663661903884, 34144976944, 728266375360, 21653750532,
     103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146,
     371245215936, 582520731713, 1066477318818, 549755842560, 728266404032]
  have seedEq : head.foldl step roots = seed := by decide +kernel
  let emit := fun (w : List ℕ) (p : Fin 32 × Fin 32) => w.getD p.1.val 0 &&& w.getD p.2.val 0
  let first : Fin 32 × Fin 32 := (11, 15)
  obtain ⟨gs, ts, h⟩ := remaining
  let bank := gs.foldl step seed
  change gs.length + 2 * ts.length ≤ 15 ∧
    (∀ i : Fin gs.length, (gs.get i).2.1.val < 16 + i.val ∧ (gs.get i).2.2.val < 16 + i.val) ∧
    (gs.filter (·.1)).length = 1 ∧
    (∀ i : Fin gs.length, (gs.get i).1 = true → bank.getD (16+i.val) 0 &&& 1099511562240 ≠ 0) ∧
    (∀ p ∈ ts, p.1.val < 16+gs.length ∧ p.2.val < 16+gs.length ∧ emit bank p &&& 1099511562240 = 0) ∧
    ts.foldl (fun n p => n ||| emit bank p) 28864 = 65535 at h
  obtain ⟨budget, inputs, dirtyCount, dirty, clean, covers⟩ := h
  have same : (head ++ gs).foldl step roots = bank := by
    rw [List.foldl_append, seedEq]
  have keep (i : ℕ) (hi : i < 16) : bank.getD i 0 = seed.getD i 0 :=
    preserve seed gs value ⟨i,hi⟩
  have fixed : emit bank first = 28864 := by
    change bank.getD 11 0 &&& bank.getD 15 0 = 28864
    rw [keep 11 (by decide), keep 15 (by decide)]
    decide +kernel
  have countHead : (head.filter (·.1)).length = 1 := rfl
  have headInputs : ∀ j : Fin head.length,
      (head.get j).2.1.val < 11 + j.val ∧ (head.get j).2.2.val < 11+j.val := by decide
  have headDirty : ∀ j : Fin head.length, (head.get j).1 = true →
      seed.getD (11+j.val) 0 &&& 1099511562240 ≠ 0 := by decide
  have hlen : head.length = 5 := rfl
  have glen : (head ++ gs).length = 5 + gs.length := by rw [List.length_append, hlen]
  have getHead (i : Fin (head ++ gs).length) (hi : i.val < 5) :
      (head ++ gs).get i = head.get ⟨i.val,hi⟩ := by
    exact List.getElem_append_left (as := head) (bs := gs) hi
  have getRest (i : Fin (head ++ gs).length) (hi : 5 ≤ i.val) :
      (head ++ gs).get i = gs.get ⟨i.val-5,by have := i.isLt; omega⟩ := by
    exact List.getElem_append_right (as := head) (bs := gs) hi
  refine ⟨head ++ gs, first :: ts, ?_⟩
  change (head ++ gs).length + 2 * (first :: ts).length ≤ 22 ∧ first :: ts ≠ [] ∧
    (∀ i : Fin (head ++ gs).length, ((head ++ gs).get i).2.1.val < 11+i.val ∧
      ((head ++ gs).get i).2.2.val < 11+i.val) ∧
    ((head ++ gs).filter (·.1)).length = 2 ∧
    (∀ i : Fin (head ++ gs).length, ((head ++ gs).get i).1 = true →
      ((head ++ gs).foldl step roots).getD (11+i.val) 0 &&& 1099511562240 ≠ 0) ∧
    (∀ p ∈ first :: ts, p.1.val < 11+(head++gs).length ∧ p.2.val < 11+(head++gs).length ∧
      emit ((head ++ gs).foldl step roots) p &&& 1099511562240 = 0) ∧
    (first :: ts).foldl (fun n p => n ||| emit ((head ++ gs).foldl step roots) p) 0 = 65535
  rw [same]
  refine ⟨?_, List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [glen, List.length_cons]
    omega
  · intro i
    by_cases hi : i.val < 5
    · rw [getHead i hi]
      exact headInputs ⟨i.val,hi⟩
    · have hj : i.val-5 < gs.length := by have := i.isLt; omega
      rw [getRest i (by omega)]
      simpa only [show 11+i.val = 16+(i.val-5) by omega] using inputs ⟨i.val-5,hj⟩
  · rw [List.filter_append, List.length_append, countHead, dirtyCount]
  · intro i
    by_cases hi : i.val < 5
    · rw [getHead i hi, keep (11+i.val) (by omega)]
      exact headDirty ⟨i.val,hi⟩
    · have hj : i.val-5 < gs.length := by have := i.isLt; omega
      rw [getRest i (by omega), show 11+i.val = 16+(i.val-5) by omega]
      exact dirty ⟨i.val-5,hj⟩
  · intro p hp
    rw [List.mem_cons] at hp
    rw [glen, show 11 + (5 + gs.length) = 16 + gs.length by omega]
    rcases hp with rfl | hp
    · refine ⟨?_, ?_, ?_⟩
      · change 11 < 16+gs.length
        omega
      · change 15 < 16+gs.length
        omega
      · rw [fixed]
        decide
    · exact clean p hp
  · simpa only [List.foldl_cons, fixed, Nat.zero_or] using covers
