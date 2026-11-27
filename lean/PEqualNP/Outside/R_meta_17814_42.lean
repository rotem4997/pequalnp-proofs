import PEqualNP.Defs
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_17814_42
 (cert : let cols : List Nat := [579928113, 419987523, 608501894, 169476364, 23364120, 201770016, 3616832, 28839040, 834691328, 1040194048]
    let init := fun a b : Nat => 0 :: 1073741823 :: (cols ++ [cols.getD a 0 ||| cols.getD b 0])
    ∀ a b : Fin 11, ∃ c : Bool, ∃ t : Fin 13 → Fin 13, ∃ s : Fin 30 → Fin 30,
      (∀ k, (s k).val < 15 ↔ k.val < 15) ∧
      ∀ j k, ((init a b).getD j.val 0).testBit (s k).val =
        ((init 0 (if c then 1 else 2)).getD (t j).val 0).testBit k.val)
 (res : let cols : List Nat := [579928113, 419987523, 608501894, 169476364, 23364120, 201770016, 3616832, 28839040, 834691328, 1040194048]
    let init := fun a b : Nat => 0 :: 1073741823 :: (cols ++ [cols.getD a 0 ||| cols.getD b 0])
    ∀ (c : Bool) (gs : List (Bool × Nat × Nat)) (o : Nat), gs.length ≤ 18 → o < 13 + gs.length →
      (∀ i g, gs[i]? = some g → g.2.1 < 13 + i ∧ g.2.2 < 13 + i) →
      (gs.foldl (fun (w : List Nat) (g : Bool × Nat × Nat) =>
       let a := w.getD g.2.1 0
       let b := w.getD g.2.2 0
       w ++ [if g.1 = true then a &&& b else a ||| b]) (init 0 (if c then 1 else 2))).getD o 0 &&& 1073741823 ≠ 32767) :
have x1 : List ℕ := [(579928113 : ℕ), (419987523 : ℕ), (608501894 : ℕ), (169476364 : ℕ), (23364120 : ℕ), (201770016 : ℕ), (3616832 : ℕ), (28839040 : ℕ), (834691328 : ℕ), (1040194048 : ℕ)]; ∀ (x2 x3 : Fin (11 : ℕ)) (x4 : List (Bool × ℕ × ℕ)) (x5 : ℕ),   x4.length ≤ (18 : ℕ) →     x5 < (13 : ℕ) + x4.length →       (∀ (x8 : ℕ) (x9 : Bool × ℕ × ℕ), x4[x8]? = Option.some x9 → x9.2.1 < (13 : ℕ) + x8 ∧ x9.2.2 < (13 : ℕ) + x8) →         have x9 : List ℕ := (0 : ℕ) :: (1073741823 : ℕ) :: (x1 ++ [x1.getD ↑x2 (0 : ℕ) ||| x1.getD ↑x3 (0 : ℕ)]);         have x10 : List ℕ :=           List.foldl             (fun (x10 : List ℕ) (x11 : Bool × ℕ × ℕ) =>               have x12 : ℕ := x10.getD x11.2.1 (0 : ℕ);               have x13 : ℕ := x10.getD x11.2.2 (0 : ℕ);               x10 ++ [if x11.1 = Bool.true then x12 &&& x13 else x12 ||| x13])             x9 x4;         x10.getD x5 (0 : ℕ) &&& (1073741823 : ℕ) ≠ (32767 : ℕ) := by
  let cols : List Nat := [579928113, 419987523, 608501894, 169476364, 23364120, 201770016, 3616832, 28839040, 834691328, 1040194048]
  let ini := fun a b : Nat => 0 :: 1073741823 :: (cols ++ [cols.getD a 0 ||| cols.getD b 0])
  let step := fun (w : List Nat) (g : Bool × Nat × Nat) =>
       let a := w.getD g.2.1 0
       let b := w.getD g.2.2 0
       w ++ [if g.1 = true then a &&& b else a ||| b]
  dsimp only
  intro a b gs o len outLegal gateLegal hit
  obtain ⟨c,t,s,labels,entries⟩ := cert a b
  let tr (i : Nat) : Nat := if h : i < 13 then (t ⟨i,h⟩).val else i
  let ren (g : Bool × Nat × Nat) : Bool × Nat × Nat := (g.1,tr g.2.1,tr g.2.2)
  let R (u v : List Nat) : Prop := 13 ≤ u.length ∧ u.length = v.length ∧
    ∀ i (k : Fin 30), (u.getD i 0).testBit (s k).val = (v.getD (tr i) 0).testBit k.val
  have iniLen (x y : Nat) : (ini x y).length = 13 := by simp [ini,cols]
  have initR : R (ini a b) (ini 0 (if c then 1 else 2)) := by
    refine ⟨(iniLen _ _).symm ▸ Nat.le_refl 13, (iniLen _ _).trans (iniLen _ _).symm, ?_⟩
    intro i k
    by_cases hi : i < 13
    · simpa only [tr, dite_eq_left hi] using entries ⟨i,hi⟩ k
    · have lsrc : (ini a b).length ≤ i := by rw [iniLen]; omega
      have ldst : (ini 0 (if c then 1 else 2)).length ≤ i := by rw [iniLen]; omega
      simp [tr,hi,List.getD_eq_getElem?_getD,List.getElem?_eq_none lsrc,List.getElem?_eq_none ldst]
  have run (p : List (Bool × Nat × Nat)) (u v : List Nat) (h : R u v) :
      R (p.foldl step u) ((p.map ren).foldl step v) := by
    induction p generalizing u v with
    | nil => exact h
    | cons g gs ih =>
      apply ih
      rcases h with ⟨bound,lens,h⟩
      let one (w : List Nat) (g : Bool × Nat × Nat) :=
        if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0
      change R (u ++ [one u g]) (v ++ [one v (ren g)])
      refine ⟨by simpa using Nat.le_trans bound (Nat.le_succ _),by simp [lens],?_⟩
      intro i k
      have hb : (one u g).testBit (s k).val = (one v (ren g)).testBit k.val := by
        by_cases gt : g.1 = true
        · simp only [one,ren,ite_eq_left gt,Nat.testBit_and,h]
        · simp only [one,ren,ite_eq_right gt,Nat.testBit_or,h]
      by_cases hi : i < u.length
      · have hj : tr i < v.length := by
          by_cases h13 : i < 13
          · have hr := (t ⟨i,h13⟩).isLt
            simp only [tr,dite_eq_left h13]; omega
          · simp only [tr,dite_eq_right h13]; omega
        simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left hi,List.getElem?_append_left hj] using h i k
      · have h13 : ¬i < 13 := by omega
        have le : u.length ≤ i := by omega
        have le' : v.length ≤ i := by omega
        simp only [tr,dite_eq_right h13,List.getD_eq_getElem?_getD,List.getElem?_append_right le,List.getElem?_append_right le',lens,List.getElem?_singleton]
        split
        · exact hb
        · simp
  have H := (run gs _ _ initR).2.2 o
  have trlt (i n : Nat) (hn : 13 ≤ n) (hi : i < n) : tr i < n := by
    by_cases h13 : i < 13
    · have hb := (t ⟨i,h13⟩).isLt
      simp only [tr,dite_eq_left h13]; omega
    · simpa only [tr,dite_eq_right h13] using hi
  apply res c (gs.map ren) (tr o) (by simpa using len) (by simpa only [List.length_map] using trlt o (13+gs.length) (by omega) outLegal)
  · intro i g hg
    rw [List.getElem?_map,Option.map_eq_some_iff] at hg
    obtain ⟨g', hg',rfl⟩ := hg
    exact ⟨trlt _ _ (by omega) (gateLegal i g' hg').1, trlt _ _ (by omega) (gateLegal i g' hg').2⟩
  change ((gs.map ren).foldl step (ini 0 (if c then 1 else 2))).getD (tr o) 0 &&& 1073741823 = 32767
  apply Nat.eq_of_testBit_eq
  intro k
  have mask (i : Nat) : (1073741823 : Nat).testBit i = decide (i < 30) := Nat.testBit_two_pow_sub_one 30 i
  have target (i : Nat) : (32767 : Nat).testBit i = decide (i < 15) := Nat.testBit_two_pow_sub_one 15 i
  rw [Nat.testBit_and, mask, target]
  by_cases hk : k < 30
  · let k' : Fin 30 := ⟨k,hk⟩
    have hh := congrArg (fun n : Nat => n.testBit (s k').val) hit
    have hsk := (s k').isLt
    change (((gs.foldl step (ini a b)).getD o 0 &&& 1073741823).testBit (s k').val) = _ at hh
    rw [Nat.testBit_and,mask,target] at hh
    simpa only [decide_eq_true hk,Bool.and_true] using (show (((gs.map ren).foldl step (ini 0 (if c then 1 else 2))).getD (tr o) 0).testBit k = decide (k < 15) from by
      rw [← H k']
      simpa only [decide_eq_true hsk,Bool.and_true,labels k'] using hh)
  · have hk' : ¬k < 15 := by omega
    simp [hk,hk']
