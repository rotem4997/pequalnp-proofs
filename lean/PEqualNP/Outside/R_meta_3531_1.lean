import Mathlib
import PEqualNP.Defs

-- Three points on line seven form the first part. The other four points and six lines
-- form the vertex-edge incidence graph of the complete graph on four vertices.
-- The three shared disjunctions encode the three pairs of opposite edges.
-- A witness for the three-point branch, with the seven inputs in their stated order, is
-- [(true,3,4),(false,0,7),(true,3,5),(false,1,9),(true,3,6),(false,2,11),(true,8,10),(true,13,12)]
theorem PEqualNP.Outside.R_meta_3531_1
    (three : ∃ gs : List (Bool × ℕ × ℕ), 1 ≤ gs.length ∧ gs.length ≤ 8 ∧
      (gs.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) => w ++ [if g.1 = true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0])
        ([95229015649944073,63038587928642,4292497062825988,189297016294080519,192860064594267704,288166778660192704,283797140973809664] : List ℕ)).getD (7+gs.length-1) 0 = 332367)
    (four : ∃ gs : List (Bool × ℕ × ℕ), 1 ≤ gs.length ∧ gs.length ≤ 14 ∧
      (gs.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) => w ++ [if g.1 = true then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0])
        ([256463372304,8521482511360,14003410187716736,55389823206179104,155696362464215096,218994303131713984,183565875465424384,229736628136996864,270286071508729856,288160007409369088,192860064594267704,288166778660192704,283797140973809664] : List ℕ)).getD (13+gs.length-1) 0 = 1764784) : ∃ (x1 : List (Bool × ℕ × ℕ)) (x2 : ℕ) (x3 : ℕ) (x4 : Fin (16 : ℕ)),   x1.length ≤ (25 : ℕ) ∧     (14 : ℕ) ≤ x2 ∧       x2 < x3 ∧         x3 < (14 : ℕ) + x1.length ∧           have x5 : ℕ := [(64 : ℕ), (256 : ℕ), (448 : ℕ), (1429 : ℕ), (1557 : ℕ), (2389 : ℕ), (3669 : ℕ), (1494 : ℕ), (1558 : ℕ), (1750 : ℕ), (1942 : ℕ), (2390 : ℕ), (2902 : ℕ), (1688 : ℕ), (1880 : ℕ), (2008 : ℕ)].getD ↑x4 (0 : ℕ);           have x6 : ℕ := x5 % (64 : ℕ);           have x7 : ℕ := x5 / (64 : ℕ);           have x8 : List ℕ := List.foldl (fun (x8 : List ℕ) (x9 : Bool × ℕ × ℕ) => x8 ++ [(fun (x10 : List ℕ) (x11 : Bool × ℕ × ℕ) => if x11.1 = Bool.true then x10.getD x11.2.1 (0 : ℕ) ||| x10.getD x11.2.2 (0 : ℕ) else x10.getD x11.2.1 (0 : ℕ) &&& x10.getD x11.2.2 (0 : ℕ)) x8 x9]) [(95229015649944073 : ℕ), (63038587928642 : ℕ), (256463372304 : ℕ), (4292497062825988 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (189297016294080519 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)] x1;           have x9 : ℕ := x8.getD x2 (0 : ℕ);           have x10 : ℕ := x8.getD x3 (0 : ℕ);           (if x6 < (21 : ℕ) then x9 ||| x10 else x9 &&& x10) = (2097151 : ℕ) ∧ x9.testBit x6 ≠ x10.testBit x6 ∧ x9.testBit x6 = x10.testBit x7 ∧ x10.testBit x6 = x9.testBit x7 := by
  let op (w : List ℕ) (g : Bool × ℕ × ℕ) := if g.1 = true then
    w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0
  let step (w : List ℕ) (g : Bool × ℕ × ℕ) := w ++ [op w g]
  have extendsWires (gs : List (Bool × ℕ × ℕ)) (w : List ℕ) :
      ∃ t, gs.foldl step w = w++t ∧ t.length=gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp,rfl⟩
    | cons g gs ih =>
      obtain ⟨t,eq,len⟩ := ih (step w g)
      refine ⟨op w g :: t,?_,by simp [len]⟩
      simpa only [List.foldl_cons,step,List.append_assoc,List.singleton_append] using eq
  have appendRead (w : List ℕ) (v i : ℕ) :
      (w++[v]).getD i 0 = if i=w.length then v else w.getD i 0 := by
    by_cases hi : i < w.length
    · rw [List.getD_append _ _ _ _ hi,ite_eq_right (Nat.ne_of_lt hi)]
    · by_cases he : i=w.length
      · subst i; simp
      · have large : (w++[v]).length ≤ i := by simp;omega
        rw [List.getD_eq_default _ _ large,ite_eq_right he,List.getD_eq_default _ _ (by omega)]
  have simulate (gs : List (Bool × ℕ × ℕ)) (f : ℕ → ℕ) (u v : List ℕ)
      (same : ∀ i, u.getD i 0 = v.getD (f i) 0)
      (align : ∀ i k, f i=v.length+k ↔ i=u.length+k) :
      ∀ i, (gs.foldl step u).getD i 0 =
        ((gs.map (fun g => (g.1,f g.2.1,f g.2.2))).foldl step v).getD (f i) 0 := by
    induction gs generalizing u v with
    | nil => exact same
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      apply ih
      · intro i
        simp only [step,appendRead]
        have h := align i 0
        simp only [Nat.add_zero] at h
        by_cases eq : i=u.length
        · simp only [ite_eq_left eq,ite_eq_left (h.mpr eq),op,same]
        · simp only [ite_eq_right eq,ite_eq_right (fun he => eq (h.mp he)),same]
      · intro i k
        simpa only [step,List.length_append,List.length_singleton,Nat.add_assoc] using align i (1+k)
  have compile (I W : List ℕ) (gs : List (Bool × ℕ × ℕ)) (mask : ℕ)
      (safe : ∀ i ∈ I, i<W.length) (pos : 1 ≤ gs.length)
      (value : (gs.foldl step (I.map (fun j => W.getD j 0))).getD (I.length+gs.length-1) 0=mask) :
      ∃ ts : List (Bool × ℕ × ℕ), ∃ t : List ℕ, ts.length=gs.length ∧ t.length=gs.length ∧
        ts.foldl step W=W++t ∧ (W++t).getD (W.length+gs.length-1) 0=mask := by
    let f (i : ℕ) := if i<I.length then I.getD i 0 else W.length+(i-I.length)
    let ts := gs.map (fun g => (g.1,f g.2.1,f g.2.2))
    obtain ⟨t,ev,len⟩ := extendsWires ts W
    have sz : ts.length=gs.length := by simp [ts]
    refine ⟨ts,t,sz,len.trans sz,ev,?_⟩
    have rel (i) : (I.map (fun j => W.getD j 0)).getD i 0 = W.getD (f i) 0 := by
      by_cases hi : i<I.length
      · simp [f,hi,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hi]
      · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp [f,hi])]
    have align (i k : ℕ) : f i=W.length+k ↔ i=(I.map (fun j => W.getD j 0)).length+k := by
      simp only [List.length_map]
      by_cases hi : i<I.length
      · have valid : I[i] ∈ I := List.getElem_mem hi
        have rd : I.getD i 0 = I[i] := by simp [List.getD_eq_getElem?_getD,hi]
        have small : I.getD i 0 < W.length := rd ▸ safe _ valid
        simp only [f,ite_eq_left hi]; omega
      · simp only [f,ite_eq_right hi]; omega
    have final := simulate gs f _ W rel align (I.length+gs.length-1)
    change _ = (ts.foldl step W).getD _ 0 at final
    rw [ev] at final
    have idx : f (I.length+gs.length-1) = W.length+gs.length-1 := by
      have off : ¬ I.length+gs.length-1<I.length := by omega
      simp only [f,ite_eq_right off];omega
    rw [idx] at final
    exact final.symm.trans value
  let initial : List ℕ := [95229015649944073,63038587928642,256463372304,4292497062825988,8521482511360,14003410187716736,55389823206179104,189297016294080519,155696362464215096,218994303131713984,183565875465424384,229736628136996864,270286071508729856,288160007409369088]
  let pre : List (Bool × ℕ × ℕ) := [(true,8,10),(true,9,13),(true,11,12)]
  let W : List ℕ := [95229015649944073,63038587928642,256463372304,4292497062825988,8521482511360,14003410187716736,55389823206179104,189297016294080519,155696362464215096,218994303131713984,183565875465424384,229736628136996864,270286071508729856,288160007409369088,192860064594267704,288166778660192704,283797140973809664]
  have start : pre.foldl step initial=W := by decide +kernel
  let A : List ℕ := [0,1,3,7,14,15,16]
  let B : List ℕ := [2,4,5,6,8,9,10,11,12,13,14,15,16]
  obtain ⟨gs,apos,asz,av⟩ := three
  obtain ⟨hs,bpos,bsz,bv⟩ := four
  obtain ⟨ta,x,la,lx,ea,va⟩ := compile A W gs 332367 (by decide +kernel) apos av
  have validB : ∀ i∈B, i<(W++x).length := by
    have hi : ∀ i∈B, i<W.length := by decide +kernel
    intro i h; have := hi i h; simp only [List.length_append];omega
  have valuesB : B.map (fun j => (W++x).getD j 0) = B.map (fun j => W.getD j 0) := by
    apply List.map_congr_left
    have hi : ∀ i∈B, i<W.length := by decide +kernel
    intro i h; exact List.getD_append _ _ _ _ (hi i h)
  obtain ⟨tb,y,lb,ly,eb,vb⟩ := compile B (W++x) hs 1764784 validB bpos (by rw [valuesB];exact bv)
  let a := W.length+gs.length-1
  let b := (W++x).length+hs.length-1
  refine ⟨pre++ta++tb,a,b,1,?_,?_,?_,?_,?_⟩
  · simp only [List.length_append,la,lb]; change 3+gs.length+hs.length ≤ 25;omega
  · dsimp only [a]; change 14 ≤ 17+gs.length-1;omega
  · dsimp only [a,b]; simp only [List.length_append,lx];omega
  · dsimp only [b]; simp only [List.length_append,lx,la,lb]
    change 17+gs.length+hs.length-1 < 14+(3+gs.length+hs.length);omega
  · let final := (pre++ta++tb).foldl step initial
    have run : final=W++x++y := by simp only [final,List.foldl_append,start,ea,eb]
    have hA : final.getD a 0=332367 := by
      rw [run,List.getD_append _ _ _ _ (by dsimp only [a]; simp only [List.length_append,lx];omega)]
      exact va
    have hB : final.getD b 0=1764784 := by rw [run];exact vb
    change (final.getD a 0 ||| final.getD b 0)=2097151 ∧
      (final.getD a 0).testBit 0 ≠ (final.getD b 0).testBit 0 ∧
      (final.getD a 0).testBit 0 = (final.getD b 0).testBit 4 ∧
      (final.getD b 0).testBit 0 = (final.getD a 0).testBit 4
    rw [hA,hB]
    decide +kernel
