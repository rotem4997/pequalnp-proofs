import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_17121_448
    (h0 : let run := fun (w : List (BitVec 32)) (a : Fin 32 × Fin 32 × Bool) =>
        let u := w.getD a.1.val 0
        let v := w.getD a.2.1.val 0
        let z := if a.2.2 then u ||| v else u &&& v
        if w.any (fun t => (t ^^^ 16383) &&& (z ^^^ 16383) == t ^^^ 16383) then w else w ++ [z]
      ∀ p : Fin 18 → Fin 32 × Fin 32 × Bool, (16383 : BitVec 32) ∉ (List.ofFn p).foldl run ([0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752] : List (BitVec 32)))
    (h1 : let run := fun (w : List (BitVec 32)) (a : Fin 32 × Fin 32 × Bool) =>
        let u := w.getD a.1.val 0
        let v := w.getD a.2.1.val 0
        let z := if a.2.2 then u ||| v else u &&& v
        if w.any (fun t => (t ^^^ 16383) &&& (z ^^^ 16383) == t ^^^ 16383) then w else w ++ [z]
      ∀ p : Fin 18 → Fin 32 × Fin 32 × Bool, (16383 : BitVec 32) ∉ (List.ofFn p).foldl run ([8372227, 0, 32849932, 714129456, 26198208, 101352196, 19074064, 340530208, 410001728, 562049537, 1040189578] : List (BitVec 32)))
    (h2 : let run := fun (w : List (BitVec 32)) (a : Fin 32 × Fin 32 × Bool) =>
        let u := w.getD a.1.val 0
        let v := w.getD a.2.1.val 0
        let z := if a.2.2 then u ||| v else u &&& v
        if w.any (fun t => (t ^^^ 16383) &&& (z ^^^ 16383) == t ^^^ 16383) then w else w ++ [z]
      ∀ p : Fin 18 → Fin 32 × Fin 32 × Bool, (16383 : BitVec 32) ∉ (List.ofFn p).foldl run ([8372227, 1292189708, 0, 1418772528, 42631364, 202359552, 52628496, 676074528, 812654920, 1132474881, 2080376962] : List (BitVec 32)))
    (h3 : let run := fun (w : List (BitVec 32)) (a : Fin 32 × Fin 32 × Bool) =>
        let u := w.getD a.1.val 0
        let v := w.getD a.2.1.val 0
        let z := if a.2.2 then u ||| v else u &&& v
        if w.any (fun t => (t ^^^ 16383) &&& (z ^^^ 16383) == t ^^^ 16383) then w else w ++ [z]
      ∀ p : Fin 18 → Fin 32 × Fin 32 × Bool, (16383 : BitVec 32) ∉ (List.ofFn p).foldl run ([16760835, 353714188, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 318779905, 469764258] : List (BitVec 32)))
    : (∀ x1 ∈ [[(0 : BitVec (32 : ℕ)), (2592243715 : BitVec (32 : ℕ)), (133562380 : BitVec (32 : ℕ)), (2844803120 : BitVec (32 : ℕ)), (84754625 : BitVec (32 : ℕ)), (403292932 : BitVec (32 : ℕ)), (102861840 : BitVec (32 : ℕ)), (1347294240 : BitVec (32 : ℕ)), (1617961282 : BitVec (32 : ℕ)), (2273325568 : BitVec (32 : ℕ)), (4160751752 : BitVec (32 : ℕ))], [(8372227 : BitVec (32 : ℕ)), (0 : BitVec (32 : ℕ)), (32849932 : BitVec (32 : ℕ)), (714129456 : BitVec (32 : ℕ)), (26198208 : BitVec (32 : ℕ)), (101352196 : BitVec (32 : ℕ)), (19074064 : BitVec (32 : ℕ)), (340530208 : BitVec (32 : ℕ)), (410001728 : BitVec (32 : ℕ)), (562049537 : BitVec (32 : ℕ)), (1040189578 : BitVec (32 : ℕ))], [(8372227 : BitVec (32 : ℕ)), (1292189708 : BitVec (32 : ℕ)), (0 : BitVec (32 : ℕ)), (1418772528 : BitVec (32 : ℕ)), (42631364 : BitVec (32 : ℕ)), (202359552 : BitVec (32 : ℕ)), (52628496 : BitVec (32 : ℕ)), (676074528 : BitVec (32 : ℕ)), (812654920 : BitVec (32 : ℕ)), (1132474881 : BitVec (32 : ℕ)), (2080376962 : BitVec (32 : ℕ))], [(16760835 : BitVec (32 : ℕ)), (353714188 : BitVec (32 : ℕ)), (63750192 : BitVec (32 : ℕ)), (0 : BitVec (32 : ℕ)), (36339908 : BitVec (32 : ℕ)), (70451984 : BitVec (32 : ℕ)), (54774784 : BitVec (32 : ℕ)), (213652480 : BitVec (32 : ℕ)), (146809160 : BitVec (32 : ℕ)), (318779905 : BitVec (32 : ℕ)), (469764258 : BitVec (32 : ℕ))]],   ∀ (x3 : List (BitVec (32 : ℕ))),     x3.length ≤ (18 : ℕ) →       (∀ (x5 : Fin x3.length),           have x6 : List (BitVec (32 : ℕ)) := x1 ++ List.take (↑x5) x3;           (∃ x7 ∈ x6, ∃ x8 ∈ x6, x3.get x5 = x7 &&& x8 ∨ x3.get x5 = x7 ||| x8) ∧ ∀ x7 ∈ x6, (x7 ^^^ (16383 : BitVec (32 : ℕ))) &&& (x3.get x5 ^^^ (16383 : BitVec (32 : ℕ))) ≠ x7 ^^^ (16383 : BitVec (32 : ℕ))) →         (16383 : BitVec (32 : ℕ)) ∉ x1 ++ x3) := by
  let run := fun (w : List (BitVec 32)) (a : Fin 32 × Fin 32 × Bool) =>
        let u := w.getD a.1.val 0
        let v := w.getD a.2.1.val 0
        let z := if a.2.2 then u ||| v else u &&& v
        if w.any (fun t => (t ^^^ 16383) &&& (z ^^^ 16383) == t ^^^ 16383) then w else w ++ [z]
  let ok (w : List (BitVec 32)) (s : List (BitVec 32)) :=
    ∀ j : Fin s.length, let a := w ++ s.take j.val
      (∃ u ∈ a, ∃ v ∈ a, s.get j = u &&& v ∨ s.get j = u ||| v) ∧
      ∀ t ∈ a, (t ^^^ 16383) &&& (s.get j ^^^ 16383) ≠ t ^^^ 16383
  have encode (w s : List (BitVec 32)) (bound : w.length + s.length ≤ 32) (valid : ok w s) :
      ∃ p : List (Fin 32 × Fin 32 × Bool), p.length = s.length ∧ p.foldl run w = w ++ s := by
    induction s using List.reverseRecOn with
    | nil => exact ⟨[],rfl,by simp⟩
    | append_singleton s z ih =>
      have bound' : w.length + s.length ≤ 32 := by simpa using (show w.length + s.length ≤ 32 by simp at bound; omega)
      have old : ok w s := by
        intro j
        let i : Fin (s ++ [z]).length := ⟨j.val,by simp⟩
        have h := valid i
        have ht : (s ++ [z]).take j.val = s.take j.val := by
          rw [List.take_append_of_le_length]; omega
        have atj : (s ++ [z]).get i = s.get j := by
          simp [List.get_eq_getElem,i,List.getElem_append_left,j.isLt]
        simpa only [i, ht, atj] using h
      obtain ⟨pre,len,eq⟩ := ih bound' old
      let j : Fin (s ++ [z]).length := ⟨s.length, by simp⟩
      have last := valid j
      have gz : (s ++ [z]).get j = z := by simp [List.get_eq_getElem,j]
      have take : (s ++ [z]).take s.length = s := by simp
      change (∃ u ∈ w ++ (s ++ [z]).take s.length, ∃ v ∈ w ++ (s ++ [z]).take s.length,
          (s ++ [z]).get j = u &&& v ∨ (s ++ [z]).get j = u ||| v) ∧ _ at last
      simp only [gz,take] at last
      obtain ⟨⟨u,hu,v,hv,op⟩,dom⟩ := last
      obtain ⟨a,ha,au⟩ := List.getElem_of_mem hu
      obtain ⟨b,hb,bv⟩ := List.getElem_of_mem hv
      let ai : Fin 32 := ⟨a, by simp at ha; omega⟩
      let bi : Fin 32 := ⟨b, by simp at hb; omega⟩
      have getU : (w ++ s).getD ai.val 0 = u := by change ((w ++ s)[a]?).getD 0 = u; rw [getElem?_pos (w ++ s) a ha]; exact au
      have getV : (w ++ s).getD bi.val 0 = v := by change ((w ++ s)[b]?).getD 0 = v; rw [getElem?_pos (w ++ s) b hb]; exact bv
      have skip : (w ++ s).any (fun t => (t ^^^ 16383) &&& (z ^^^ 16383) == t ^^^ 16383) = false := by
        apply List.any_eq_false.mpr
        intro t ht
        simpa only [beq_iff_eq] using dom t (by simpa [j,take] using ht)
      rcases op with h | h
      · refine ⟨pre ++ [(ai,bi,false)], by simp [len], ?_⟩
        rw [List.foldl_append,eq,← List.append_assoc]
        change run (w ++ s) _ = w ++ s ++ [z]
        simp only [run,getU,getV,Bool.false_eq_true,↓reduceIte,← h,skip]
      · refine ⟨pre ++ [(ai,bi,true)], by simp [len], ?_⟩
        rw [List.foldl_append,eq,← List.append_assoc]
        change run (w ++ s) _ = w ++ s ++ [z]
        simp only [run,getU,getV,Bool.false_eq_true,↓reduceIte,← h,skip]
  have extend (w : List (BitVec 32)) (hw : w ≠ []) :
      run w (0,0,false) = w := by
    obtain ⟨v,t,rfl⟩ := List.exists_cons_of_ne_nil hw
    simp [run,List.getD]
  have pad (w : List (BitVec 32)) (hw : w ≠ []) (k : Nat) :
      (List.replicate k ((0,0,false) : Fin 32 × Fin 32 × Bool)).foldl run w = w := by
    induction k with
    | zero => rfl
    | succ k ih => simpa [List.replicate_succ,extend w hw] using ih
  have faithful (a s : List (BitVec 32)) (la : a.length = 11) (ls : s.length ≤ 18)
      (valid : ok a s)
      (nohit : ∀ p : Fin 18 → Fin 32 × Fin 32 × Bool, (16383 : BitVec 32) ∉ (List.ofFn p).foldl run a) :
      (16383 : BitVec 32) ∉ a ++ s := by
    obtain ⟨pre,len,eq⟩ := encode a s (by omega) valid
    let p := pre ++ List.replicate (18-pre.length) ((0,0,false) : Fin 32 × Fin 32 × Bool)
    have plen : p.length = 18 := by simp [p]; omega
    let program (j : Fin 18) := p[j.val]'(by rw [plen]; exact j.isLt)
    have same : List.ofFn program = p := by
      apply List.ext_getElem
      · simp only [List.length_ofFn,plen]
      · intro i h₁ h₂
        rw [List.getElem_ofFn]
    have h := nohit program
    rw [same] at h
    have nonempty : a ++ s ≠ [] := by intro contra; have z := congrArg List.length contra; simp only [List.length_append,la,List.length_nil] at z; omega
    simpa [p,List.foldl_append,eq,pad _ nonempty] using h
  intro a ha s ls valid
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact faithful _ s rfl ls valid h0
  · exact faithful _ s rfl ls valid h1
  · exact faithful _ s rfl ls valid h2
  · exact faithful _ s rfl ls valid h3
