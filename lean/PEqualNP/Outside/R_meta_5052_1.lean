import Mathlib
import PEqualNP.Defs

open PEqualNP.Defs.LratEncoding

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_5052_1
  (andCubes :
    let positive : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
    let negative : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
    ∀ j : ℕ, 19 ≤ j → j < 38 →
      ¬ FormulaSat (enc2 14 26 (fun r => decide (r ∈ positive)) (positive ++ negative) ++
        enc2Cube 14 26 (j)))
  (orCubes :
    let positive : List ℕ := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
    let negative : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]
    ∀ j : ℕ, 14 ≤ j → j < 38 →
      ¬ FormulaSat (enc2 14 26 (fun r => decide (r ∈ positive)) (positive ++ negative) ++
        enc2Cube 14 26 (40 + j)))
  : have x1 : List ℕ := [(129 : ℕ), (257 : ℕ), (1025 : ℕ), (130 : ℕ), (514 : ℕ), (8194 : ℕ), (260 : ℕ), (4100 : ℕ), (8196 : ℕ), (136 : ℕ), (2056 : ℕ), (4104 : ℕ), (1040 : ℕ), (2064 : ℕ), (8208 : ℕ), (544 : ℕ), (1056 : ℕ), (4128 : ℕ), (320 : ℕ), (576 : ℕ), (2112 : ℕ)]; have x2 : List ℕ :=   have x2 : List ℕ :=     have x2 : List ℕ :=       have x2 : List ℕ := [(10656 : ℕ), (12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ)];       (8488 : ℕ) :: (8713 : ℕ) :: (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: x2;     have x3 : List ℕ := (5186 : ℕ) :: (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: x2;     (4304 : ℕ) :: (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: x3;   have x3 : List ℕ :=     have x3 : List ℕ := (2338 : ℕ) :: (2565 : ℕ) :: (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: x2;     (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: x3;   have x4 : List ℕ := (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: (1220 : ℕ) :: x3;   (127 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: (432 : ℕ) :: x4; ∀ x3 < PEqualNP.Defs.LratEncoding.enc2CubeCount (14 : ℕ) (26 : ℕ), ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 (14 : ℕ) (26 : ℕ) (fun (x5 : ℕ) => Decidable.decide (x5 ∈ x1)) (x1 ++ x2) ++ PEqualNP.Defs.LratEncoding.enc2Cube (14 : ℕ) (26 : ℕ) x3) := by
  have noLastPad (g : Nat → Bool) (rows : List Nat) (a : Nat → Bool)
      (hSat : ∀ c ∈ enc2 14 26 g rows, ClauseSat a c)
      (pos : ∃ r ∈ rows, g r = true)
      (neg : ∃ r ∈ rows, g r = false)
      (raw : ∀ j < 14, ∃ r ∈ rows, r.testBit j ≠ g r) :
      a (ix 14 26 7 25 0 + 1) = false ∧ a (ix 14 26 0 25 2 + 1) = false := by
    clear andCubes orCubes
    have use (c : List Nat)
        (hm : c ∈ fPre 14 26 ∨ c ∈ fPad 14 26 ∨ c ∈ fGate 14 26 rows ∨
          c ∈ fOutAlo 14 26 ∨ c ∈ fOutEq 14 26 g rows) : ClauseSat a c := by
      apply hSat
      change c ∈ fOp 14 26 ++ fSrcAlo 14 26 ++ fSrcEq 14 26 rows ++
        fGate 14 26 rows ++ fOutAlo 14 26 ++ fOutEq 14 26 g rows ++ fOut 14 26 ++
        fPad 14 26 ++ fPre 14 26 ++ fPadRd 14 26 ++ fOrd 14 26 ++ fUsed 14 26 ++ fLex 14 26
      simp only [List.mem_append]
      rcases hm with hm | hm | hm | hm | hm
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm)))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm))))))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm)))))))

    have litP (v : Nat) : litVal a (P v) = true ↔ a (v+1) = true := by
      change (a ((2*v+2)/2) == ((2*v+2)%2 == 0)) = true ↔ a (v+1) = true
      have d : (2*v+2)/2 = v+1 := by omega
      have m : (2*v+2)%2 = 0 := by omega
      rw [d,m]
      cases a (v+1) <;> decide

    have litQ (v : Nat) : litVal a (Q v) = true ↔ a (v+1) = false := by
      change (a ((2*v+3)/2) == ((2*v+3)%2 == 0)) = true ↔ a (v+1) = false
      have d : (2*v+3)/2 = v+1 := by omega
      have m : (2*v+3)%2 = 1 := by omega
      rw [d,m]
      cases a (v+1) <;> decide

    have unit (l : Nat) (hs : ClauseSat a [l]) : litVal a l = true := by
      obtain ⟨k,hk,hv⟩ := hs
      exact (List.mem_singleton.mp hk) ▸ hv

    have pair (l k : Nat) (hs : ClauseSat a [l,k]) :
        litVal a l = true ∨ litVal a k = true := by
      obtain ⟨i,hi,hv⟩ := hs
      rcases List.mem_cons.mp hi with rfl | hi
      · exact Or.inl hv
      · exact Or.inr ((List.mem_singleton.mp hi) ▸ hv)

    have padTrue (j : Nat) (hj : j < 26)
        (hp : a (ix 14 26 7 j 0 + 1) = true) :
        a (ix 14 26 0 j 2 + 1) = true := by
      have hc : [Q (ix 14 26 7 j 0), P (ix 14 26 0 j 2)] ∈ fPad 14 26 := by
        change [Q (ix 14 26 7 j 0), P (ix 14 26 0 j 2)] ∈ (List.range 26).flatMap _
        exact List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,List.mem_cons_self⟩
      rcases pair _ _ (use _ (Or.inr (Or.inl hc))) with h | h
      · have z := (litQ _).mp h
        rw [hp] at z
        cases z
      · exact (litP _).mp h

    have backwardPad (j : Nat) (hj : j < 25)
        (hp : a (ix 14 26 7 (j+1) 0 + 1) = true) :
        a (ix 14 26 7 j 0 + 1) = true := by
      have hc : [Q (ix 14 26 7 (j+1) 0), P (ix 14 26 7 j 0)] ∈ fPre 14 26 := by
        change [Q (ix 14 26 7 (j+1) 0), P (ix 14 26 7 j 0)] ∈ (List.range 25).map _
        exact List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
      rcases pair _ _ (use _ (Or.inl hc)) with h | h
      · have z := (litQ _).mp h
        rw [hp] at z
        cases z
      · exact (litP _).mp h

    have valueTrue (j : Nat) (hj : j < 26) (r : Nat) (hr : r ∈ rows)
        (hop : a (ix 14 26 0 j 2 + 1) = true) :
        a (ix 14 26 3 j r + 1) = true := by
      have hc : [Q (ix 14 26 0 j 2), P (ix 14 26 3 j r)] ∈ fGate 14 26 rows := by
        change [Q (ix 14 26 0 j 2), P (ix 14 26 3 j r)] ∈ (List.range 26).flatMap _
        refine List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj, List.mem_flatMap.mpr ⟨r,hr,?_⟩⟩
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            List.mem_cons_self)))))
      rcases pair _ _ (use _ (Or.inr (Or.inr (Or.inl hc)))) with h | h
      · have z := (litQ _).mp h
        rw [hop] at z
        cases z
      · exact (litP _).mp h

    have fromRow (r : Nat) (hr : r ∈ rows) (k : Nat) (hk : k < 41) (c : List Nat)
        (hc : c ∈ outEq 14 26 g k r) : ClauseSat a c := by
      have hm : c ∈ fOutEq 14 26 g rows := by
        change c ∈ rows.flatMap (fun t => (List.range 41).flatMap (fun i => outEq 14 26 g i t))
        exact List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr ⟨k,List.mem_range.mpr hk,hc⟩⟩
      exact use _ (Or.inr (Or.inr (Or.inr (Or.inr hm))))

    have outEqDef (k r : Nat) : outEq 14 26 g k r =
        if k < 14 then (if r.testBit k = g r then [] else [[Q (ix 14 26 6 0 k)]])
        else if k < 40 then [[Q (ix 14 26 6 0 k), L (ix 14 26 3 (k-14) r) (g r)]]
        else if g r = true then [[Q (ix 14 26 6 0 k)]] else [] := rfl

    have padOff : a (ix 14 26 7 25 0 + 1) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hLast
      have goingDown (d : Nat) (hd : d ≤ 25) : a (ix 14 26 7 (25-d) 0 + 1) = true := by
        induction d with
        | zero => exact hLast
        | succ d ih =>
          have hs : 25 - (d + 1) < 25 := by omega
          have he : 25 - (d + 1) + 1 = 25 - d := by omega
          apply backwardPad _ hs
          rw [he]
          exact ih (by omega)
      have allPad (j : Nat) (hj : j < 26) : a (ix 14 26 7 j 0 + 1) = true := by
        have h := goingDown (25-j) (by omega)
        have e : 25 - (25-j) = j := by omega
        simpa only [e] using h
      let out := (List.range 41).map fun k => P (ix 14 26 6 0 k)
      have hAlo : out ∈ fOutAlo 14 26 := List.mem_cons_self
      obtain ⟨l,hl,hv⟩ := use out (Or.inr (Or.inr (Or.inr (Or.inl hAlo))))
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
      have hl41 : k < 41 := List.mem_range.mp hk
      have hOn : a (ix 14 26 6 0 k + 1) = true := (litP _).mp hv
      by_cases hRaw : k < 14
      · obtain ⟨r,hr,hdiff⟩ := raw k hRaw
        have gc : [Q (ix 14 26 6 0 k)] ∈ outEq 14 26 g k r := by
          rw [outEqDef,ite_eq_left hRaw,ite_eq_right hdiff]
          exact List.mem_cons_self
        have off := (litQ _).mp (unit _ (fromRow r hr k hl41 _ gc))
        rw [hOn] at off
        cases off
      · by_cases hGate : k < 40
        · obtain ⟨r,hr,hneg⟩ := neg
          have hj : k - 14 < 26 := by omega
          have gc : [Q (ix 14 26 6 0 k), Q (ix 14 26 3 (k-14) r)] ∈ outEq 14 26 g k r := by
            rw [outEqDef,ite_eq_right hRaw,ite_eq_left hGate,hneg]
            exact List.mem_cons_self
          rcases pair _ _ (fromRow r hr k hl41 _ gc) with h | h
          · have off := (litQ _).mp h
            rw [hOn] at off
            cases off
          · have off := (litQ _).mp h
            rw [valueTrue _ hj r hr (padTrue _ hj (allPad _ hj))] at off
            cases off
        · obtain ⟨r,hr,hpos⟩ := pos
          have gc : [Q (ix 14 26 6 0 k)] ∈ outEq 14 26 g k r := by
            rw [outEqDef,ite_eq_right hRaw,ite_eq_right hGate,ite_eq_left hpos]
            exact List.mem_cons_self
          have off := (litQ _).mp (unit _ (fromRow r hr k hl41 _ gc))
          rw [hOn] at off
          cases off

    have hc : [P (ix 14 26 7 25 0), Q (ix 14 26 0 25 2)] ∈ fPad 14 26 := by
      change [P (ix 14 26 7 25 0), Q (ix 14 26 0 25 2)] ∈ (List.range 26).flatMap _
      refine List.mem_flatMap.mpr ⟨25,by decide,?_⟩
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))
    refine ⟨padOff, ?_⟩
    rcases pair _ _ (use _ (Or.inr (Or.inl hc))) with h | h
    · have padOn := (litP _).mp h
      rw [padOff] at padOn
      cases padOn
    · exact (litQ _).mp h
  have lastFirstSourceBounds (g : ℕ → Bool) (rows : List ℕ) (a : ℕ → Bool)
      (op k : ℕ) (sat : ∀ c ∈ enc2 14 26 g rows, ClauseSat a c)
      (pad : a (ix 14 26 7 25 0 + 1) = false) (hop : op = 0 ∨ op = 1)
      (hopSel : a (ix 14 26 0 25 op + 1) = true)
      (hfirst : a (ix 14 26 1 25 k + 1) = true) (hk : k < 40)
      (hpos : ∀ j < 14, ∃ r ∈ rows, g r = true ∧ r.testBit j = false)
      (hneg : ∀ j < 14, ∃ r ∈ rows, g r = false ∧ r.testBit j = true) :
      14 ≤ k ∧ k < 38 := by
    clear andCubes orCubes noLastPad
    have pos (v : ℕ) : litVal a (P v) = true ↔ a (v + 1) = true := by
      change (a ((2 * v + 2) / 2) == ((2 * v + 2) % 2 == 0)) = true ↔ _
      rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
      cases a (v + 1) <;> decide
    have neg (v : ℕ) : litVal a (Q v) = true ↔ a (v + 1) = false := by
      change (a ((2 * v + 3) / 2) == ((2 * v + 3) % 2 == 0)) = true ↔ _
      rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
      cases a (v + 1) <;> decide
    have signed (v : ℕ) (b : Bool) : litVal a (L v b) = true ↔ a (v + 1) = b := by
      cases b
      · exact neg v
      · exact pos v
    have posDead (v : ℕ) (hv : a (v + 1) = false) : litVal a (P v) ≠ true := by
      intro h
      have e := (pos v).mp h
      rw [hv] at e
      cases e
    have negDead (v : ℕ) (hv : a (v + 1) = true) : litVal a (Q v) ≠ true := by
      intro h
      have e := (neg v).mp h
      rw [hv] at e
      cases e
    have pair (u v : ℕ) (h : ClauseSat a [u, v]) : litVal a u = true ∨ litVal a v = true := by
      obtain ⟨l, hl, hv⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact Or.inl hv
      · exact Or.inr hv
    have triple (u v w : ℕ) (h : ClauseSat a [u, v, w]) :
        litVal a u = true ∨ litVal a v = true ∨ litVal a w = true := by
      obtain ⟨l, hl, hv⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact Or.inl hv
      · exact Or.inr (Or.inl hv)
      · exact Or.inr (Or.inr hv)
    have fromParts (c : List ℕ) (hc :
        c ∈ fSrcAlo 14 26 ∨ c ∈ fSrcEq 14 26 rows ∨ c ∈ fGate 14 26 rows ∨
        c ∈ fOutEq 14 26 g rows ∨ c ∈ fOut 14 26 ∨ c ∈ fPad 14 26 ∨ c ∈ fOrd 14 26) :
        ClauseSat a c := by
      apply sat
      change c ∈ ((fOp 14 26 ++ fSrcAlo 14 26 ++ fSrcEq 14 26 rows ++ fGate 14 26 rows ++
        fOutAlo 14 26 ++ fOutEq 14 26 g rows ++ fOut 14 26 ++ fPad 14 26 ++
        fPre 14 26 ++ fPadRd 14 26 ++ fOrd 14 26 ++ fUsed 14 26) ++ fLex 14 26)
      simp only [List.append_assoc]
      simp only [List.mem_append]
      right
      rcases hc with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
    have upper : k < 38 := by
      let c := (List.range 40).map (fun l => P (ix 14 26 2 25 l))
      have hmem : c ∈ fSrcAlo 14 26 := by
        apply List.mem_flatMap.mpr
        exact ⟨2, by decide, List.mem_map.mpr ⟨25, by decide, rfl⟩⟩
      obtain ⟨lit, hlit, hlTrue⟩ := fromParts c (Or.inl hmem)
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hlit
      have hsecond : a (ix 14 26 2 25 l + 1) = true := (pos _).mp hlTrue
      have hlt : l < 40 := List.mem_range.mp hl
      have hne : l ≠ 39 := by
        intro e
        subst l
        let cp := [P (ix 14 26 7 25 0), Q (ix 14 26 2 25 39)]
        have hc : cp ∈ fPad 14 26 := by
          apply List.mem_flatMap.mpr
          refine ⟨25, by decide, ?_⟩
          decide
        have hcp : ClauseSat a cp := fromParts _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))))
        rcases pair _ _ hcp with h | h
        · exact posDead _ pad h
        · exact negDead _ hsecond h
      have hkl : k < l := by
        by_contra hb
        have hle : l ≤ k := Nat.le_of_not_gt hb
        let co := [Q (ix 14 26 1 25 k), Q (ix 14 26 2 25 l), P (ix 14 26 7 25 0)]
        have hc : co ∈ fOrd 14 26 := by
          apply List.mem_flatMap.mpr
          refine ⟨25, by decide, ?_⟩
          exact List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
            List.mem_map.mpr ⟨l, List.mem_range.mpr (by omega), rfl⟩⟩
        have hco : ClauseSat a co := fromParts _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))))
        rcases triple _ _ _ hco with h | h | h
        · exact negDead _ hfirst h
        · exact negDead _ hsecond h
        · exact posDead _ pad h
      omega
    refine ⟨?_, upper⟩
    by_contra hh
    have hkraw : k < 14 := Nat.lt_of_not_ge hh
    have out : a (ix 14 26 6 0 39 + 1) = true := by
      let c := [P (ix 14 26 6 0 39), P (ix 14 26 7 25 0)]
      have hc : c ∈ fOut 14 26 := List.mem_cons_self
      have hs : ClauseSat a c := fromParts _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))
      exact (pos _).mp ((pair _ _ hs).resolve_right (posDead _ pad))
    have outValue (r : ℕ) (hr : r ∈ rows) : a (ix 14 26 3 25 r + 1) = g r := by
      let c := [Q (ix 14 26 6 0 39), L (ix 14 26 3 25 r) (g r)]
      have hc : c ∈ fOutEq 14 26 g rows := by
        apply List.mem_flatMap.mpr
        refine ⟨r, hr, ?_⟩
        exact List.mem_flatMap.mpr ⟨39, by decide, List.mem_cons_self⟩
      have hs : ClauseSat a c := fromParts _ (Or.inr (Or.inr (Or.inr (Or.inl hc))))
      exact (signed _ _).mp ((pair _ _ hs).resolve_left (negDead _ out))
    have rawValue (r : ℕ) (hr : r ∈ rows) : a (ix 14 26 4 25 r + 1) = r.testBit k := by
      let c := [Q (ix 14 26 1 25 k), L (ix 14 26 4 25 r) (r.testBit k)]
      have hc : c ∈ fSrcEq 14 26 rows := by
        apply List.mem_flatMap.mpr
        refine ⟨1, by decide, ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨25, by decide, ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨r, hr, ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨k, List.mem_range.mpr (by omega), ?_⟩
        delta srcEq
        rw [ite_eq_left hkraw]
        exact List.mem_cons_self
      have hs : ClauseSat a c := fromParts _ (Or.inr (Or.inl hc))
      exact (signed _ _).mp ((pair _ _ hs).resolve_left (negDead _ hfirst))
    have gateClause (r : ℕ) (hr : r ∈ rows) (c : List ℕ) (hc : c ∈ gateCl 14 26 25 r) :
        ClauseSat a c := by
      have h : c ∈ fGate 14 26 rows :=
        List.mem_flatMap.mpr ⟨25, by decide, List.mem_flatMap.mpr ⟨r, hr, hc⟩⟩
      exact fromParts _ (Or.inr (Or.inr (Or.inl h)))
    rcases hop with rfl | rfl
    · obtain ⟨r, hr, hg, hb⟩ := hpos k hkraw
      let c := [Q (ix 14 26 0 25 0), Q (ix 14 26 3 25 r), P (ix 14 26 4 25 r)]
      have hc : c ∈ gateCl 14 26 25 r := List.mem_cons_self
      rcases triple _ _ _ (gateClause r hr c hc) with h | h | h
      · exact negDead _ hopSel h
      · exact negDead _ ((outValue r hr).trans hg) h
      · exact posDead _ ((rawValue r hr).trans hb) h
    · obtain ⟨r, hr, hg, hb⟩ := hneg k hkraw
      let c := [Q (ix 14 26 0 25 1), P (ix 14 26 3 25 r), Q (ix 14 26 4 25 r)]
      have hc : c ∈ gateCl 14 26 25 r :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      rcases triple _ _ _ (gateClause r hr c hc) with h | h | h
      · exact negDead _ hopSel h
      · exact posDead _ ((outValue r hr).trans hg) h
      · exact negDead _ ((rawValue r hr).trans hb) h
  have noFullSupport (initial extra : List (Finset (Fin 7)))
      (hInit : ∀ S ∈ initial, S.card ≤ 1)
      (hExtra : ∀ i < extra.length, extra.getD i ∅ = ∅ ∨
        ∃ A ∈ initial ++ extra.take i, ∃ B ∈ initial ++ extra.take i,
          extra.getD i ∅ ⊆ A ∪ B)
      (hLen : extra.length ≤ 5) : Finset.univ ∉ extra := by
    clear andCubes orCubes noLastPad lastFirstSourceBounds
    let supported := fun (color : Fin 7 → Fin 7) (history : List (Finset (Fin 7))) =>
      ∀ S ∈ history, ∃ label : Fin 7, ∀ v ∈ S, color v = label
    let palette := fun (color : Fin 7 → Fin 7) => (Finset.univ.image color).card
    let steps := fun (history next : List (Finset (Fin 7))) =>
      ∀ i < next.length, next.getD i ∅ = ∅ ∨
        ∃ A ∈ history ++ next.take i, ∃ B ∈ history ++ next.take i,
          next.getD i ∅ ⊆ A ∪ B

    have add (history : List (Finset (Fin 7))) (S : Finset (Fin 7)) (c : Fin 7 → Fin 7)
        (inv : supported c history)
        (step : S = ∅ ∨ ∃ A ∈ history, ∃ B ∈ history, S ⊆ A ∪ B) :
        ∃ c' : Fin 7 → Fin 7, supported c' (history ++ [S]) ∧ palette c ≤ palette c' + 1 := by
      rcases step with hEmpty | ⟨A,hA,B,hB,hUnion⟩
      · subst S
        refine ⟨c, ?_, Nat.le_succ _⟩
        intro T hT
        rcases List.mem_append.mp hT with hOld | hNew
        · exact inv T hOld
        · have eq := List.mem_singleton.mp hNew
          subst T
          exact ⟨0,fun _ hv => (Finset.notMem_empty _ hv).elim⟩
      · obtain ⟨a,ha⟩ := inv A hA
        obtain ⟨b,hb⟩ := inv B hB
        let c' := fun v : Fin 7 => if c v = b then a else c v
        refine ⟨c', ?_, ?_⟩
        · intro T hT
          rcases List.mem_append.mp hT with hOld | hNew
          · obtain ⟨l,hl⟩ := inv T hOld
            refine ⟨if l = b then a else l,?_⟩
            intro v hv
            change (if c v = b then a else c v) = _
            rw [hl v hv]
          · have eq := List.mem_singleton.mp hNew
            subst T
            refine ⟨a, ?_⟩
            intro v hv
            change (if c v = b then a else c v) = a
            rcases Finset.mem_union.mp (hUnion hv) with hvA | hvB
            · rw [ha v hvA]
              split <;> rfl
            · rw [hb v hvB, ite_eq_left rfl]
        · have inc : Finset.univ.image c ⊆ insert b (Finset.univ.image c') := by
            intro l hl
            obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
            apply Finset.mem_insert.mpr
            by_cases h : c v = b
            · exact Or.inl h
            · exact Or.inr (Finset.mem_image.mpr ⟨v,hv,ite_eq_right h⟩)
          exact (Finset.card_le_card inc).trans (Finset.card_insert_le b _)

    have propagate (next : List (Finset (Fin 7))) (history : List (Finset (Fin 7)))
        (c : Fin 7 → Fin 7) (inv : supported c history) (good : steps history next) :
        ∃ c' : Fin 7 → Fin 7, supported c' (history ++ next) ∧
          palette c ≤ palette c' + next.length := by
      induction next generalizing history c with
      | nil =>
        exact ⟨c, by simpa only [List.append_nil] using inv, by simp⟩
      | cons S tail ih =>
        have first : S = ∅ ∨ ∃ A ∈ history, ∃ B ∈ history, S ⊆ A ∪ B := by
          have h := good 0 (by simp)
          change S = ∅ ∨ ∃ A ∈ history ++ [], ∃ B ∈ history ++ [], S ⊆ A ∪ B at h
          simpa only [List.append_nil] using h
        obtain ⟨c₁,inv₁,spend⟩ := add history S c inv first
        have more : steps (history ++ [S]) tail := by
          intro i hi
          have h := good (i+1) (by simp only [List.length_cons]; omega)
          change tail.getD i ∅ = ∅ ∨
            ∃ A ∈ history ++ S :: tail.take i, ∃ B ∈ history ++ S :: tail.take i,
              tail.getD i ∅ ⊆ A ∪ B at h
          simpa only [List.append_assoc,List.singleton_append] using h
        obtain ⟨c₂,inv₂,bound⟩ := ih (history ++ [S]) c₁ inv₁ more
        refine ⟨c₂, ?_, ?_⟩
        · simpa only [List.append_assoc,List.singleton_append] using inv₂
        · simp only [List.length_cons]
          omega

    have start : supported (fun v => v) initial := by
      intro S hS
      by_cases hn : S.Nonempty
      · obtain ⟨v,hv⟩ := hn
        exact ⟨v,fun w hw => (Finset.card_le_one.mp (hInit S hS)) w hw v hv⟩
      · exact ⟨0,fun v hv => (hn ⟨v,hv⟩).elim⟩
    obtain ⟨c,inv,lb⟩ := propagate extra initial (fun v => v) start hExtra
    have full : palette (fun v => v) = 7 := by decide +kernel
    rw [full] at lb
    intro present
    obtain ⟨k,hk⟩ := inv Finset.univ (List.mem_append.mpr (Or.inr present))
    have cap : palette c ≤ 1 := by
      have inc : Finset.univ.image c ⊆ {k} := by
        intro l hl
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
        exact Finset.mem_singleton.mpr (hk v hv)
      simpa only [Finset.card_singleton] using Finset.card_le_card inc
    omega
  have noEarlyCover (a : ℕ → Bool) (sample : Fin 7 → ℕ)
      (hCount : ∀ initial extra : List (Finset (Fin 7)),
        (∀ S ∈ initial, S.card ≤ 1) →
        (∀ i < extra.length, extra.getD i ∅ = ∅ ∨
          ∃ A ∈ initial ++ extra.take i, ∃ B ∈ initial ++ extra.take i, extra.getD i ∅ ⊆ A ∪ B) →
        extra.length ≤ 5 → Finset.univ ∉ extra)
      (oneHot : ∀ w : Fin 14, (Finset.univ.filter fun c : Fin 7 => (sample c).testBit w.val = true).card ≤ 1)
      (hPred :
        let live := fun w : ℕ => w < 14 ∨ a (ix 14 26 7 (w-14) 0 + 1) = false
        let val := fun w r : ℕ => if w < 14 then r.testBit w else a (ix 14 26 3 (w-14) r + 1)
        ∀ i < 5, a (ix 14 26 7 i 0 + 1) = false →
          ∃ u v, u < 14 + i ∧ v < 14 + i ∧ live u ∧ live v ∧
            ∀ c : Fin 7, a (ix 14 26 3 i (sample c) + 1) = true →
              val u (sample c) = true ∨ val v (sample c) = true)
      (j : ℕ) (hj : j < 5)
      (liveJ : a (ix 14 26 7 j 0 + 1) = false)
      (covers : ∀ c : Fin 7, a (ix 14 26 3 j (sample c) + 1) = true) : False := by
    clear andCubes orCubes noLastPad lastFirstSourceBounds noFullSupport
    let live := fun w : ℕ => w < 14 ∨ a (ix 14 26 7 (w-14) 0 + 1) = false
    let val := fun w r : ℕ => if w < 14 then r.testBit w else a (ix 14 26 3 (w-14) r + 1)
    let support (w : ℕ) := Finset.univ.filter fun c : Fin 7 => live w ∧ val w (sample c) = true
    let initial := (List.range 14).map support
    let extra := (List.range 5).map fun i => support (14 + i)
    have listed (w : ℕ) (hw : w < 14) : support w ∈ initial :=
      List.mem_map.mpr ⟨w,List.mem_range.mpr hw,rfl⟩
    have prefixMem (w i : ℕ) (hi : i ≤ 5) (hw : w < 14 + i) :
        support w ∈ initial ++ extra.take i := by
      apply List.mem_append.mpr
      by_cases raw : w < 14
      · exact Or.inl (listed w raw)
      · right
        have h : w - 14 < i := by omega
        change support w ∈ (((List.range 5).map fun j => support (14 + j)).take i)
        rw [← List.map_take, List.take_range, Nat.min_eq_left hi]
        exact List.mem_map.mpr ⟨w-14,List.mem_range.mpr h,by congr 1; omega⟩
    have initCard : ∀ S ∈ initial, S.card ≤ 1 := by
      intro S h
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h
      have lt := List.mem_range.mp hw
      have eq : support w = Finset.univ.filter (fun c : Fin 7 => (sample c).testBit w = true) := by
        ext c
        simp [support, live, val, lt]
      rw [eq]
      exact oneHot ⟨w,lt⟩
    have len : extra.length = 5 := by simp [extra]
    have getExtra (i : ℕ) (hi : i < extra.length) : extra.getD i ∅ = support (14 + i) := by
      rw [List.getD_eq_getElem _ _ hi]
      change (((List.range 5).map fun i => support (14 + i))[i]) = _
      rw [List.getElem_map, List.getElem_range]
    have branch (i : ℕ) : live (14 + i) ↔ a (ix 14 26 7 i 0 + 1) = false := by
      dsimp only [live]
      rw [show 14+i-14=i by omega]
      simp only [show ¬ 14+i < 14 by omega, false_or]
    have gate (i : ℕ) (c : Fin 7) :
        val (14 + i) (sample c) = a (ix 14 26 3 i (sample c) + 1) := by
      dsimp only [val]
      rw [ite_eq_right (show ¬ 14+i < 14 by omega), show 14+i-14=i by omega]
    have step (i : ℕ) (hi : i < extra.length) :
        extra.getD i ∅ = ∅ ∨
          ∃ A ∈ initial ++ extra.take i, ∃ B ∈ initial ++ extra.take i, extra.getD i ∅ ⊆ A ∪ B := by
      rw [getExtra i hi]
      have small : i < 5 := len ▸ hi
      by_cases active : live (14+i)
      · obtain ⟨u,v,hu,hv,lu,lv,allows⟩ := hPred i small ((branch i).mp active)
        refine Or.inr ⟨support u,prefixMem u i (by omega) hu,support v,prefixMem v i (by omega) hv,?_⟩
        intro row hr
        have hh : val (14+i) (sample row) = true := (Finset.mem_filter.mp hr).2.2
        rw [gate] at hh
        rcases allows row hh with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lu,h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lv,h⟩)
      · left
        ext row
        simp [support,active]
    have hTop : support (14+j) = Finset.univ := by
      ext row
      simp only [support,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
      exact ⟨(branch j).mpr liveJ,(gate j row).trans (covers row)⟩
    have mem : support (14+j) ∈ extra :=
      List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
    rw [hTop] at mem
    exact hCount initial extra initCard step (by omega) mem
  have predecessors (g : ℕ → Bool) (rows : List ℕ) (a : ℕ → Bool)
      (sat : ∀ c ∈ enc2 14 26 g rows, ClauseSat a c) :
      let wireVal := fun k r : ℕ =>
        if k < 14 then r.testBit k else a (ix 14 26 3 (k - 14) r + 1)
      (∀ j : ℕ, j < 26 → a (ix 14 26 7 j 0 + 1) = false →
        ∃ u v : ℕ, u < 14 + j ∧ v < 14 + j ∧
          (u < 14 ∨ a (ix 14 26 7 (u - 14) 0 + 1) = false) ∧
          (v < 14 ∨ a (ix 14 26 7 (v - 14) 0 + 1) = false) ∧
          ∀ r ∈ rows, a (ix 14 26 3 j r + 1) = true → wireVal u r = true ∨ wireVal v r = true) ∧
      (∀ k : ℕ, 14 ≤ k → k < 39 → a (ix 14 26 7 25 0 + 1) = false →
        a (ix 14 26 0 25 0 + 1) = true → a (ix 14 26 1 25 k + 1) = true →
        a (ix 14 26 7 (k - 14) 0 + 1) = false ∧
          ∀ r ∈ rows, g r = true → a (ix 14 26 3 (k - 14) r + 1) = true) := by
    clear andCubes orCubes noLastPad lastFirstSourceBounds noFullSupport noEarlyCover
    intro wireVal
    have pos (v : ℕ) : litVal a (P v) = true ↔ a (v + 1) = true := by
      change (a ((2 * v + 2) / 2) == ((2 * v + 2) % 2 == 0)) = true ↔ _
      rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
      cases a (v + 1) <;> decide
    have neg (v : ℕ) : litVal a (Q v) = true ↔ a (v + 1) = false := by
      change (a ((2 * v + 3) / 2) == ((2 * v + 3) % 2 == 0)) = true ↔ _
      rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
      cases a (v + 1) <;> decide
    have signed (v : ℕ) (b : Bool) : litVal a (L v b) = true ↔ a (v + 1) = b := by
      cases b
      · exact neg v
      · exact pos v
    have posDead (v : ℕ) (hv : a (v + 1) = false) : litVal a (P v) ≠ true := by
      intro h
      have e := (pos v).mp h
      rw [hv] at e
      cases e
    have negDead (v : ℕ) (hv : a (v + 1) = true) : litVal a (Q v) ≠ true := by
      intro h
      have e := (neg v).mp h
      rw [hv] at e
      cases e
    have pair (u v : ℕ) (h : ClauseSat a [u, v]) : litVal a u = true ∨ litVal a v = true := by
      obtain ⟨l, hl, hv⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact Or.inl hv
      · exact Or.inr hv
    have triple (u v w : ℕ) (h : ClauseSat a [u, v, w]) :
        litVal a u = true ∨ litVal a v = true ∨ litVal a w = true := by
      obtain ⟨l, hl, hv⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact Or.inl hv
      · exact Or.inr (Or.inl hv)
      · exact Or.inr (Or.inr hv)
    have fromParts (c : List ℕ) (hc :
        c ∈ fOp 14 26 ∨
        c ∈ fSrcAlo 14 26 ∨
        c ∈ fSrcEq 14 26 rows ∨
        c ∈ fGate 14 26 rows ∨
        c ∈ fOutEq 14 26 g rows ∨
        c ∈ fOut 14 26 ∨
        c ∈ fPad 14 26 ∨
        c ∈ fPadRd 14 26) : ClauseSat a c := by
      apply sat
      change c ∈ ((fOp 14 26 ++ fSrcAlo 14 26 ++ fSrcEq 14 26 rows ++ fGate 14 26 rows ++
        fOutAlo 14 26 ++ fOutEq 14 26 g rows ++ fOut 14 26 ++ fPad 14 26 ++
        fPre 14 26 ++ fPadRd 14 26 ++ fOrd 14 26 ++ fUsed 14 26) ++ fLex 14 26)
      simp only [List.append_assoc]
      simp only [List.mem_append]
      rcases hc with h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
    have satOp (c : List ℕ) (h : c ∈ fOp 14 26) : ClauseSat a c :=
      fromParts c (Or.inl h)
    have satAlo (c : List ℕ) (h : c ∈ fSrcAlo 14 26) : ClauseSat a c :=
      fromParts c (Or.inr (Or.inl h))
    have satSrcEq (c : List ℕ) (h : c ∈ fSrcEq 14 26 rows) : ClauseSat a c :=
      fromParts c (Or.inr (Or.inr (Or.inl h)))
    have satGate (c : List ℕ) (h : c ∈ fGate 14 26 rows) : ClauseSat a c :=
      fromParts c (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have satOutEq (c : List ℕ) (h : c ∈ fOutEq 14 26 g rows) : ClauseSat a c :=
      fromParts c (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    have satOut (c : List ℕ) (h : c ∈ fOut 14 26) : ClauseSat a c :=
      fromParts c (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    have satPad (c : List ℕ) (h : c ∈ fPad 14 26) : ClauseSat a c :=
      fromParts c (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    have satPadRd (c : List ℕ) (h : c ∈ fPadRd 14 26) : ClauseSat a c :=
      fromParts c (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    have quad (u v w z : ℕ) (h : ClauseSat a [u, v, w, z]) :
        litVal a u = true ∨ litVal a v = true ∨ litVal a w = true ∨ litVal a z = true := by
      obtain ⟨l, hl, hv⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · exact Or.inl hv
      · exact Or.inr (Or.inl hv)
      · exact Or.inr (Or.inr (Or.inl hv))
      · exact Or.inr (Or.inr (Or.inr hv))
    have side (e : ℕ) (he : e = 1 ∨ e = 2) : e ∈ ([1, 2] : List ℕ) := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using he
    have padTail (j : ℕ) (hj : j < 26) :
        ClauseSat a [P (ix 14 26 7 j 0), Q (ix 14 26 0 j 2)] ∧
        ClauseSat a [P (ix 14 26 7 j 0), Q (ix 14 26 1 j (14 + j))] ∧
        ClauseSat a [P (ix 14 26 7 j 0), Q (ix 14 26 2 j (14 + j))] := by
      refine ⟨?_, ?_, ?_⟩
      all_goals
        apply satPad
        apply List.mem_flatMap.mpr
        refine ⟨j, List.mem_range.mpr hj, ?_⟩
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      · exact List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      · exact List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self))))
    have operation (j : ℕ) (hj : j < 26) (hp : a (ix 14 26 7 j 0 + 1) = false) :
        a (ix 14 26 0 j 0 + 1) = true ∨ a (ix 14 26 0 j 1 + 1) = true := by
      have c : ClauseSat a [P (ix 14 26 0 j 0), P (ix 14 26 0 j 1), P (ix 14 26 0 j 2)] :=
        satOp _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
      have off : a (ix 14 26 0 j 2 + 1) = false :=
        (neg _).mp ((pair _ _ (padTail j hj).1).resolve_left (posDead _ hp))
      rcases triple _ _ _ c with h | h | h
      · exact Or.inl ((pos _).mp h)
      · exact Or.inr ((pos _).mp h)
      · exact (posDead _ off h).elim
    have source (j e : ℕ) (hj : j < 26) (he : e = 1 ∨ e = 2)
        (hp : a (ix 14 26 7 j 0 + 1) = false) :
        ∃ k < 14 + j, a (ix 14 26 e j k + 1) = true := by
      let c := (List.range (14 + j + 1)).map (fun k => P (ix 14 26 e j k))
      have hc : c ∈ fSrcAlo 14 26 :=
        List.mem_flatMap.mpr ⟨e, side e he, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩
      obtain ⟨v, hv, ht⟩ := satAlo c hc
      obtain ⟨k, hkr, rfl⟩ := List.mem_map.mp hv
      have hsel : a (ix 14 26 e j k + 1) = true := (pos _).mp ht
      have hlt := List.mem_range.mp hkr
      have hno : k ≠ 14 + j := by
        intro eq
        subst k
        have hcl : ClauseSat a [P (ix 14 26 7 j 0), Q (ix 14 26 e j (14 + j))] := by
          rcases he with rfl | rfl
          · exact (padTail j hj).2.1
          · exact (padTail j hj).2.2
        exact (negDead _ hsel) ((pair _ _ hcl).resolve_left (posDead _ hp))
      exact ⟨k, by omega, hsel⟩
    have liveSource (j e k : ℕ) (hj : j < 26) (he : e = 1 ∨ e = 2)
        (hk : k < 14 + j) (hsel : a (ix 14 26 e j k + 1) = true) :
        k < 14 ∨ a (ix 14 26 7 (k - 14) 0 + 1) = false := by
      by_cases hraw : k < 14
      · exact Or.inl hraw
      right
      let i := k - 14
      have hi : i < j := by dsimp [i]; omega
      have hki : 14 + i = k := by dsimp [i]; omega
      have hc : [Q (ix 14 26 7 i 0), Q (ix 14 26 e j k)] ∈ fPadRd 14 26 := by
        apply List.mem_flatMap.mpr
        refine ⟨j, List.mem_range.mpr hj, ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨i, List.mem_range.mpr hi, ?_⟩
        rw [← hki]
        rcases he with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
      exact (neg _).mp ((pair _ _ (satPadRd _ hc)).resolve_right (negDead _ hsel))
    have sourceTrue (j e k r : ℕ) (hj : j < 26) (he : e = 1 ∨ e = 2)
        (hk : k < 14 + j) (hr : r ∈ rows) (hsel : a (ix 14 26 e j k + 1) = true)
        (hval : a (ix 14 26 (e + 3) j r + 1) = true) : wireVal k r = true := by
      have eqClause (c : List ℕ) (hc : c ∈ srcEq 14 26 e j k r) : ClauseSat a c :=
        satSrcEq c (List.mem_flatMap.mpr ⟨e, side e he, List.mem_flatMap.mpr
          ⟨j, List.mem_range.mpr hj, List.mem_flatMap.mpr
            ⟨r, hr, List.mem_flatMap.mpr ⟨k, List.mem_range.mpr (by omega), hc⟩⟩⟩⟩)
      change (if k < 14 then r.testBit k else a (ix 14 26 3 (k - 14) r + 1)) = true
      by_cases hraw : k < 14
      · let c := [Q (ix 14 26 e j k), L (ix 14 26 (e + 3) j r) (r.testBit k)]
        have hc : c ∈ srcEq 14 26 e j k r := by
          delta srcEq
          rw [ite_eq_left hraw]
          exact List.mem_cons_self
        have h := (signed _ _).mp ((pair _ _ (eqClause c hc)).resolve_left (negDead _ hsel))
        rw [ite_eq_left hraw, ← h]
        exact hval
      · let c := [Q (ix 14 26 e j k), Q (ix 14 26 (e + 3) j r), P (ix 14 26 3 (k - 14) r)]
        have hc : c ∈ srcEq 14 26 e j k r := by
          delta srcEq
          rw [ite_eq_right hraw, ite_eq_left hk]
          exact List.mem_cons_self
        rw [ite_eq_right hraw]
        rcases triple _ _ _ (eqClause c hc) with h | h | h
        · exact (negDead _ hsel h).elim
        · exact (negDead _ hval h).elim
        · exact (pos _).mp h
    have gateClause (j r : ℕ) (hj : j < 26) (hr : r ∈ rows)
        (c : List ℕ) (hc : c ∈ gateCl 14 26 j r) : ClauseSat a c :=
      satGate c (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_flatMap.mpr ⟨r, hr, hc⟩⟩)
    have andFirst (j r : ℕ) (hj : j < 26) (hr : r ∈ rows)
        (hop : a (ix 14 26 0 j 0 + 1) = true) (hval : a (ix 14 26 3 j r + 1) = true) :
        a (ix 14 26 4 j r + 1) = true := by
      let c := [Q (ix 14 26 0 j 0), Q (ix 14 26 3 j r), P (ix 14 26 4 j r)]
      have hc : c ∈ gateCl 14 26 j r := List.mem_cons_self
      rcases triple _ _ _ (gateClause j r hj hr c hc) with h | h | h
      · exact (negDead _ hop h).elim
      · exact (negDead _ hval h).elim
      · exact (pos _).mp h
    have orInputs (j r : ℕ) (hj : j < 26) (hr : r ∈ rows)
        (hop : a (ix 14 26 0 j 1 + 1) = true) (hval : a (ix 14 26 3 j r + 1) = true) :
        a (ix 14 26 4 j r + 1) = true ∨ a (ix 14 26 5 j r + 1) = true := by
      let c := [Q (ix 14 26 0 j 1), Q (ix 14 26 3 j r), P (ix 14 26 4 j r), P (ix 14 26 5 j r)]
      have hc : c ∈ gateCl 14 26 j r :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
      rcases quad _ _ _ _ (gateClause j r hj hr c hc) with h | h | h | h
      · exact (negDead _ hop h).elim
      · exact (negDead _ hval h).elim
      · exact Or.inl ((pos _).mp h)
      · exact Or.inr ((pos _).mp h)
    constructor
    · intro j hj hp
      obtain ⟨u, hu, hs₁⟩ := source j 1 hj (Or.inl rfl) hp
      obtain ⟨v, hv, hs₂⟩ := source j 2 hj (Or.inr rfl) hp
      refine ⟨u, v, hu, hv, liveSource j 1 u hj (Or.inl rfl) hu hs₁,
        liveSource j 2 v hj (Or.inr rfl) hv hs₂, ?_⟩
      intro r hr hrtrue
      have h₁ := sourceTrue j 1 u r hj (Or.inl rfl) hu hr hs₁
      have h₂ := sourceTrue j 2 v r hj (Or.inr rfl) hv hr hs₂
      rcases operation j hj hp with ha | ho
      · exact Or.inl (h₁ (andFirst j r hj hr ha hrtrue))
      · exact (orInputs j r hj hr ho hrtrue).elim (fun h => Or.inl (h₁ h)) (fun h => Or.inr (h₂ h))
    · intro k klo khi pad hop hfirst
      have hj : 25 < 26 := by decide
      refine ⟨(liveSource 25 1 k hj (Or.inl rfl) khi hfirst).resolve_left (Nat.not_lt_of_ge klo), ?_⟩
      have out : a (ix 14 26 6 0 39 + 1) = true := by
        let c := [P (ix 14 26 6 0 39), P (ix 14 26 7 25 0)]
        have hc : c ∈ fOut 14 26 := List.mem_cons_self
        exact (pos _).mp ((pair _ _ (satOut c hc)).resolve_right (posDead _ pad))
      intro r hr hgr
      have gv : a (ix 14 26 3 25 r + 1) = true := by
        let c := [Q (ix 14 26 6 0 39), L (ix 14 26 3 25 r) (g r)]
        have hc : c ∈ fOutEq 14 26 g rows :=
          List.mem_flatMap.mpr ⟨r, hr, List.mem_flatMap.mpr ⟨39, by decide, List.mem_cons_self⟩⟩
        exact ((signed _ _).mp ((pair _ _ (satOutEq c hc)).resolve_left (negDead _ out))).trans hgr
      have h := sourceTrue 25 1 k r hj (Or.inl rfl) khi hr hfirst
        (andFirst 25 r hj hr hop gv)
      change (if k < 14 then r.testBit k else a (ix 14 26 3 (k - 14) r + 1)) = true at h
      rwa [ite_eq_right (Nat.not_lt_of_ge klo)] at h
  intro positive negative k hk hsat
  let rows := positive ++ negative
  let label := fun r : ℕ => decide (r ∈ positive)
  obtain ⟨a,allClauses⟩ := hsat
  have base (c : List ℕ) (hc : c ∈ enc2 14 26 label rows) : ClauseSat a c :=
    allClauses c (List.mem_append.mpr (Or.inl hc))
  have unit (v : ℕ) (h : ClauseSat a [P v]) : a (v + 1) = true := by
    obtain ⟨l,hl,h⟩ := h
    have e := List.mem_singleton.mp hl
    subst l
    change (a ((2*v+2)/2) == ((2*v+2)%2 == 0)) = true at h
    rw [show (2*v+2)/2 = v+1 by omega, show (2*v+2)%2 = 0 by omega] at h
    simpa using h
  have selectedFirst : a (ix 14 26 1 25 (k % 40) + 1) = true := by
    apply unit
    apply allClauses
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have selectedOp : a (ix 14 26 0 25 (k / 40) + 1) = true := by
    apply unit
    apply allClauses
    exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ List.mem_cons_self))
  have samples : (∃ r ∈ rows, label r = true) ∧ (∃ r ∈ rows, label r = false) ∧
      ∀ j : Fin 14,
        (∃ r ∈ rows, label r = true ∧ r.testBit j.val = false) ∧
        (∃ r ∈ rows, label r = false ∧ r.testBit j.val = true) := by decide +kernel
  have pos (j : ℕ) (hj : j < 14) :
      ∃ r ∈ rows, label r = true ∧ r.testBit j = false := (samples.2.2 ⟨j,hj⟩).1
  have neg (j : ℕ) (hj : j < 14) :
      ∃ r ∈ rows, label r = false ∧ r.testBit j = true := (samples.2.2 ⟨j,hj⟩).2
  have mismatch (j : ℕ) (hj : j < 14) : ∃ r ∈ rows, r.testBit j ≠ label r := by
    obtain ⟨r,hr,hl,ht⟩ := pos j hj
    exact ⟨r,hr,by rw [ht,hl]; decide⟩
  obtain ⟨pad,notTrue⟩ := noLastPad label rows a base samples.1 samples.2.1 mismatch
  change k < 120 at hk
  have operation : k / 40 = 0 ∨ k / 40 = 1 := by
    have possible : k / 40 = 0 ∨ k / 40 = 1 ∨ k / 40 = 2 := by omega
    rcases possible with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h,notTrue] at selectedOp
      contradiction
  have firstLt : k % 40 < 40 := Nat.mod_lt _ (by decide)
  obtain ⟨low,high⟩ := lastFirstSourceBounds label rows a (k / 40) (k % 40)
    base pad operation selectedOp selectedFirst firstLt pos neg
  rcases operation with h | h
  · have strictly : 19 ≤ k % 40 := by
      by_contra! short
      let matching : Fin 7 → ℕ := ![129,514,260,4104,8208,1056,2112]
      have matchRows : ∀ c : Fin 7, matching c ∈ rows ∧ label (matching c) = true := by
        decide +kernel
      have oneHot : ∀ w : Fin 14,
          (Finset.univ.filter fun c : Fin 7 => (matching c).testBit w.val = true).card ≤ 1 := by
        decide +kernel
      have jSmall : k % 40 - 14 < 5 := by omega
      have andSelected : a (ix 14 26 0 25 0 + 1) = true := by
        simpa only [h] using selectedOp
      have transfers := predecessors label rows a base
      obtain ⟨notPad,hitAll⟩ := transfers.2 (k % 40) low (by omega) pad andSelected selectedFirst
      refine noEarlyCover a matching noFullSupport oneHot ?_ (k % 40 - 14) jSmall notPad ?_
      · intro live val i hi active
        obtain ⟨u,v,hu,hv,lu,lv,cover⟩ := transfers.1 i (by omega) active
        exact ⟨u,v,hu,hv,lu,lv,fun c hc => cover (matching c) (matchRows c).1 hc⟩
      · intro c
        exact hitAll (matching c) (matchRows c).1 (matchRows c).2
    exact andCubes k (by omega) (by omega) ⟨a,allClauses⟩
  · apply orCubes (k % 40) low high
    rw [show 40 + k % 40 = k by omega]
    exact ⟨a,allClauses⟩
