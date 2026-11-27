import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_8610_17
    (left : ∃ (op : Fin 14 → Bool) (a b : Fin 14 → Fin 33)
        (s : ℕ → ℕ) (d : Fin 2 → Fin 14) (q : Fin 2 → Fin 24),
      (∀ i : Fin 11, s i.val = ([2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] : List ℕ).getD i.val 0) ∧
      (∀ i, (a i).val ∈ ([0, 1, 2, 4, 5, 8, 9, 10] : List ℕ) ∨ 11 ≤ (a i).val) ∧
      (∀ i, (b i).val ∈ ([0, 1, 2, 4, 5, 8, 9, 10] : List ℕ) ∨ 11 ≤ (b i).val) ∧
      (∀ i, (a i).val < 11+i.val ∧ (b i).val < 11+i.val ∧
        s (11+i.val) = if op i = true then s (a i).val &&& s (b i).val else s (a i).val ||| s (b i).val) ∧
      s 24 = 36671 ∧ Function.Injective d ∧
      ∀ i, op (d i) = true ∧ (s (11+(d i).val)).testBit (16+(q i).val) = true)
    (right : ∃ (op : Fin 6 → Bool) (a b : Fin 6 → Fin 33)
        (s : ℕ → ℕ) (d : Fin 1 → Fin 6) (q : Fin 1 → Fin 24),
      (∀ i : Fin 11, s i.val = ([2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] : List ℕ).getD i.val 0) ∧
      (∀ i, (a i).val ∈ ([3, 6, 7, 9, 10] : List ℕ) ∨ 25 ≤ (a i).val) ∧
      (∀ i, (b i).val ∈ ([3, 6, 7, 9, 10] : List ℕ) ∨ 25 ≤ (b i).val) ∧
      (∀ i, (a i).val < 25+i.val ∧ (b i).val < 25+i.val ∧
        s (25+i.val) = if op i = true then s (a i).val &&& s (b i).val else s (a i).val ||| s (b i).val) ∧
      s 30 = 28864 ∧ Function.Injective d ∧
      ∀ i, op (d i) = true ∧ (s (25+(d i).val)).testBit (16+(q i).val) = true) :
    ∃ (x1 : Fin (22 : ℕ)) (x2 : Fin ↑x1 → Bool) (x3 : Fin ↑x1 → Fin (33 : ℕ)) (x4 : Fin ↑x1 → Fin (33 : ℕ)) (x5 : Fin (33 : ℕ)) (x6 : ℕ → ℕ) (x7 : Fin (3 : ℕ) → Fin ↑x1) (x8 : Fin (3 : ℕ) → Fin (24 : ℕ)), ↑x5 < (11 : ℕ) + ↑x1 ∧ x6 ↑x5 = (65535 : ℕ) ∧ (∀ (x9 : Fin (11 : ℕ)), x6 ↑x9 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x9 (0 : ℕ)) ∧ (∀ (x9 : Fin ↑x1), ↑(x3 x9) < (11 : ℕ) + ↑x9 ∧ ↑(x4 x9) < (11 : ℕ) + ↑x9 ∧ x6 ((11 : ℕ) + ↑x9) = if x2 x9 = Bool.true then x6 ↑(x3 x9) &&& x6 ↑(x4 x9) else x6 ↑(x3 x9) ||| x6 ↑(x4 x9)) ∧ Function.Injective x7 ∧ ∀ (x9 : Fin (3 : ℕ)), x2 (x7 x9) = Bool.true ∧ (x6 ((11 : ℕ) + ↑(x7 x9))).testBit ((16 : ℕ) + ↑(x8 x9)) = Bool.true := by
  obtain ⟨fo,fa,fb,F,fd,fq,fi,_,_,fr,fout,finj,fdirt⟩ := left
  obtain ⟨go,ga,gb,G,gd,gq,gi,gla,glb,gr,gout,ginj,gdirt⟩ := right
  let pack {α : Type} (f : Fin 14 → α) (g : Fin 6 → α) (z : α) (i : Fin 21) : α :=
    if h : i.val < 14 then f ⟨i.val,h⟩ else if hh : i.val < 20 then g ⟨i.val-14,by omega⟩ else z
  let S (w : ℕ) := if w < 25 then F w else if w < 31 then G w else 65535
  let d (i : Fin 3) : Fin 21 :=
    if h : i.val < 2 then ⟨(fd ⟨i.val,h⟩).val,by omega⟩ else ⟨14+(gd 0).val,by omega⟩
  let q (i : Fin 3) : Fin 24 := if h : i.val < 2 then fq ⟨i,h⟩ else gq 0
  refine ⟨21,pack fo go false,pack fa ga 24,pack fb gb 30,31,S,d,q,by decide,rfl,?_,?_,?_,?_⟩
  · intro i
    simpa only [S, ite_eq_left (show i.val < 25 by omega)] using fi i
  · intro i
    by_cases h : i.val < 14
    · let j : Fin 14 := ⟨i.val,h⟩
      obtain ⟨ha,hb,hr⟩ := fr j
      have aa : (fa j).val < 25 := by have := j.isLt; omega
      have bb : (fb j).val < 25 := by have := j.isLt; omega
      simpa only [pack, dite_eq_left h, S, ite_eq_left aa, ite_eq_left bb, ite_eq_left (show 11+i.val < 25 by omega),
        j] using And.intro ha (And.intro hb hr)
    · by_cases hh : i.val < 20
      · let j : Fin 6 := ⟨i.val-14,by omega⟩
        obtain ⟨ha,hb,hr⟩ := gr j
        have eq : 11+i.val = 25+j.val := by dsimp [j]; omega
        have ge : ∀ v : Fin 33, v.val ∈ ([3,6,7,9,10] : List ℕ) ∨ 25 ≤ v.val →
            v.val < 25+j.val → S v.val = G v.val := by
          intro v hx hv
          rcases hx with raw | later
          · have hv' : v.val < 11 := by
              have ht : ∀ n ∈ ([3,6,7,9,10] : List ℕ), n < 11 := by decide
              exact ht _ raw
            let z : Fin 11 := ⟨v.val,hv'⟩
            exact (show S v.val = F v.val by simp [S,show v.val < 25 by omega]).trans
              ((fi z).trans (gi z).symm)
          · simp [S, show ¬v.val < 25 by omega, show v.val < 31 by omega]
        have ax := ge (ga j) (gla j) ha
        have bx := ge (gb j) (glb j) hb
        simp only [pack, dite_eq_right h, dite_eq_left hh]
        change (ga j).val < 11+i.val ∧ (gb j).val < 11+i.val ∧ _
        rw [eq]
        refine ⟨ha,hb,?_⟩
        change S (25+j.val) = if go j = true then S (ga j).val &&& S (gb j).val else S (ga j).val ||| S (gb j).val
        rw [ax,bx]
        simpa only [S, ite_eq_right (show ¬ 25+j.val < 25 by omega), ite_eq_left (show 25+j.val < 31 by omega)] using hr
      · have hi : i.val = 20 := by omega
        have ei : i = (20 : Fin 21) := Fin.ext hi
        subst i
        change 24 < 11+20 ∧ 30 < 11+20 ∧ S 31 = S 24 ||| S 30
        exact ⟨by decide, by decide, by simp [S,fout,gout]⟩
  · intro i j eq
    apply Fin.ext
    by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2
    · have ex := congrArg Fin.val eq
      simp only [d, dite_eq_left hi, dite_eq_left hj] at ex
      exact congrArg (fun j : Fin 2 => j.val) (finj (Fin.ext ex))
    · have ex := congrArg Fin.val eq
      simp only [d, dite_eq_left hi, dite_eq_right hj] at ex
      omega
    · have ex := congrArg Fin.val eq
      simp only [d, dite_eq_right hi, dite_eq_left hj] at ex
      omega
    · omega
  · intro i
    by_cases h : i.val < 2
    · let j : Fin 2 := ⟨i,h⟩
      have b : (fd j).val < 14 := (fd j).isLt
      simpa only [d,q,dite_eq_left h,pack,dite_eq_left b,S,ite_eq_left (show 11+(fd j).val < 25 by omega),j] using fdirt j
    · let z := gd 0
      have ha : ¬ 14+z.val < 14 := by omega
      have hb : 14+z.val < 20 := by omega
      have hi : (⟨14+z.val-14,by omega⟩ : Fin 6) = z := Fin.ext (by simp)
      have hs : 11+(14+z.val) = 25+z.val := by omega
      simpa only [d,q,dite_eq_right h,pack,dite_eq_right ha,dite_eq_left hb,hi,hs,S,
        ite_eq_right (show ¬25+z.val < 25 by omega),ite_eq_left (show 25+z.val<31 by omega),z] using gdirt 0
