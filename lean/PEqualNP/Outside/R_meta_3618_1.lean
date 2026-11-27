import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.R_meta_3618_1
    (degreeThree : ∀ (w : ℕ → (Fin 8 → Bool) → Bool) (paid : Finset ℕ), paid.card ≤ 11 →
      (∀ i < 23, (∃ c : Bool, ∀ x, w i x = c) ∨
        (∃ k : Fin 8, ∃ p : Bool, ∀ x, w i x = (x k ^^ p)) ∨
        (∃ j < i, ∃ p : Bool, ∀ x, w i x = (w j x ^^ p)) ∨
        (i ∈ paid ∧ ∃ j < i, ∃ k < i, ∃ p q d : Bool, ∀ x,
          w i x = (if d then (w j x ^^ p) && (w k x ^^ q) else (w j x ^^ p) || (w k x ^^ q)))) →
      ∀ o < 23, ∃ x : Fin 8 → Bool, w o x ≠
        ([1,12,23,5,16,27,46,57,47] : List ℕ).any (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10))))
    (degreeTwo : ∀ (w : ℕ → (Fin 8 → Bool) → Bool) (paid : Finset ℕ), paid.card ≤ 11 →
      (∀ i < 23, (∃ c : Bool, ∀ x, w i x = c) ∨
        (∃ k : Fin 8, ∃ p : Bool, ∀ x, w i x = (x k ^^ p)) ∨
        (∃ j < i, ∃ p : Bool, ∀ x, w i x = (w j x ^^ p)) ∨
        (i ∈ paid ∧ ∃ j < i, ∃ k < i, ∃ p q d : Bool, ∀ x,
          w i x = (if d then (w j x ^^ p) && (w k x ^^ q) else (w j x ^^ p) || (w k x ^^ q)))) →
      ∀ o < 23, ∃ x : Fin 8 → Bool, w o x ≠
        ([1,12,23,4,15,26,37,46,57,47] : List ℕ).any (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10)))) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (∀ (x7 : Fin x1), (x3 x7).1 < (10 : ℕ) + ↑x7 ∧ (x4 x7).1 < (10 : ℕ) + ↑x7) →     x5.1 < (10 : ℕ) + x1 →       x5.2 = Bool.false →         ∀ (x10 : Finset ℕ),           x10.Nonempty →             x10.card ≤ (3 : ℕ) →               x1 + x10.card ≤ (14 : ℕ) →                 (have x14 : ℕ × Bool → Prop := fun (x14 : ℕ × Bool) => x14.2 = Bool.true → x14.1 = (0 : ℕ) ∨ x14.1 = (9 : ℕ) ∨ x14.1 ∈ x10;                   x14 x5 ∧ ∀ (x15 : Fin x1), x14 (x3 x15) ∧ x14 (x4 x15)) →                   (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ)), x6 x15 ↑x16 = x15 x16) →                     (∀ (x16 : Fin (9 : ℕ) → Bool), x6 x16 (9 : ℕ) = Bool.false) →                       (∀ (x17 : Fin (9 : ℕ) → Bool) (x18 : Fin x1),                           have x19 : ℕ × Bool → Bool := fun (x19 : ℕ × Bool) => x6 x17 x19.1 ^^ x19.2;                           x6 x17 ((10 : ℕ) + ↑x18) = if x2 x18 = Bool.true then x19 (x3 x18) && x19 (x4 x18) else x19 (x3 x18) || x19 (x4 x18)) →                         (∀ (x18 : Fin (9 : ℕ) → Bool), (x6 x18 x5.1 ^^ x5.2) = (x18 (0 : Fin (9 : ℕ)) && x18 (1 : Fin (9 : ℕ)) || x18 (1 : Fin (9 : ℕ)) && x18 (2 : Fin (9 : ℕ)) || x18 (2 : Fin (9 : ℕ)) && x18 (3 : Fin (9 : ℕ)) || x18 (3 : Fin (9 : ℕ)) && x18 (4 : Fin (9 : ℕ)) || x18 (4 : Fin (9 : ℕ)) && x18 (0 : Fin (9 : ℕ)) || x18 (0 : Fin (9 : ℕ)) && x18 (5 : Fin (9 : ℕ)) || x18 (1 : Fin (9 : ℕ)) && x18 (6 : Fin (9 : ℕ)) || x18 (2 : Fin (9 : ℕ)) && x18 (7 : Fin (9 : ℕ)) || x18 (3 : Fin (9 : ℕ)) && x18 (8 : Fin (9 : ℕ)) || x18 (5 : Fin (9 : ℕ)) && x18 (7 : Fin (9 : ℕ)) || x18 (6 : Fin (9 : ℕ)) && x18 (8 : Fin (9 : ℕ)) || x18 (8 : Fin (9 : ℕ)) && x18 (5 : Fin (9 : ℕ)))) → False := by
  classical
  intro n op l r out val back outBound outPhase S nonempty _ budget _ raw zero step correct
  let F (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) ||
    (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have size : n ≤ 13 := by have := Finset.card_pos.mpr nonempty; omega
  have output (x) : val x out.1 = F x := by simpa [outPhase,F] using correct x
  have high : 10 ≤ out.1 := by
    by_contra! h
    by_cases low : out.1 < 9
    · let k : Fin 9 := ⟨out.1,low⟩
      let x (i : Fin 9) := decide (i=k)
      have single : ∀ z : Fin 9, F (fun i => decide (i=z)) = false := by decide +kernel
      have a := raw x k
      have b := output x
      change val x out.1 = x k at a
      rw [single k] at b
      simp [a,x] at b
    · have ix : out.1 = 9 := by omega
      have a := output (fun _ => true)
      rw [ix,zero] at a
      contradiction
  have pos : 0 < n := by omega
  let first : Fin n := ⟨0,pos⟩
  let A : Fin 10 := ⟨(l first).1,by simpa [first] using (back first).1⟩
  let B : Fin 10 := ⟨(r first).1,by simpa [first] using (back first).2⟩
  let pin (x : Fin 9 → Bool) (a : Fin 10) := if h : a.val < 9 then x ⟨a.val,h⟩ else false
  have pinOk (x) (a : Fin 10) : val x a.val = pin x a := by
    unfold pin
    split
    next h => exact raw x ⟨a.val,h⟩
    next h => rw [show a.val=9 by omega,zero]
  -- Each entry encodes a pivot and a pair of assignments differing at that pivot.
  -- They change the target while giving the same value at the first gate.
  let code (a b : Fin 10) (c : Bool) :=
    ([10,10,144,18,18,180,18,90,18,144,18,288,18,720,18,1170,18,2322,18,10,37,10,18,18,10,37,10,82,10,181,10,325,10,577,10,1162,10,2314,18,18,20,83,74,20,18,18,20,74,20,164,20,308,20,650,20,1154,20,2324,18,18,39,48,39,165,147,39,18,18,39,147,39,327,39,615,39,1299,39,2307,18,18,76,13,13,94,13,49,13,76,18,18,13,364,13,589,13,1165,13,2317,18,18,1157,14,14,1175,14,50,14,86,14,1301,18,18,14,590,14,1157,14,2309,18,18,24,2319,2310,24,24,2346,24,96,24,168,24,312,18,18,24,1176,24,2310,18,18,43,52,43,313,295,43,43,367,43,187,43,295,43,619,18,18,43,2347,18,18,80,89,80,98,80,332,296,80,80,440,80,296,80,584,80,1232,18,18,18,18,10,10,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18,18] : List ℕ).getD ((10*a.val+b.val)*2+c.toNat) 0
  let pivot (a b : Fin 10) (c : Bool) : Fin 9 := Fin.ofNat 9 (code a b c)
  let off (a b : Fin 10) (c : Bool) (k : Fin 9) := (code a b c / 9).testBit k.val
  let on (a b : Fin 10) (c : Bool) (k : Fin 9) := off a b c k || decide (k=pivot a b c)
  have table : ∀ (a b : Fin 10) (c : Bool),
      let v := pivot a b c
      let x := off a b c
      let y := on a b c
      (a.val = 9 ∨ b.val = 9 ∨ a=b ∨ a.val=v.val ∨ b.val=v.val) ∧
      F x ≠ F y ∧ ((pin x a = pin y a ∧ pin x b = pin y b) ∨ (pin x b=c ∧ pin y b=c)) := by
    decide +kernel
  let c := (!op first) ^^ (r first).2
  let v := pivot A B c
  let x := off A B c
  let y := on A B c
  obtain ⟨g0,diff,mask⟩ := table A B c
  change F x ≠ F y at diff
  have sameRaw (k : Fin 9) (hk : k.val ≠ v.val) : x k = y k := by
    have ne : k ≠ v := fun e => hk (congrArg Fin.val e)
    change x k = (x k || decide (k=v))
    simp [ne]
  have masked : val x 10 = val y 10 := by
    have hx := step x first
    have hy := step y first
    change val x 10 = (if op first then (val x A.val ^^ (l first).2) && (val x B.val ^^ (r first).2)
       else (val x A.val ^^ (l first).2) || (val x B.val ^^ (r first).2)) at hx
    change val y 10 = (if op first then (val y A.val ^^ (l first).2) && (val y B.val ^^ (r first).2)
       else (val y A.val ^^ (l first).2) || (val y B.val ^^ (r first).2)) at hy
    rw [hx,hy,pinOk,pinOk,pinOk,pinOk]
    rcases mask with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · change pin x A = pin y A at ha
      change pin x B = pin y B at hb
      rw [ha,hb]
    · change pin x B = c at ha
      change pin y B = c at hb
      rw [ha,hb]
      dsimp only [c]
      cases op first <;> cases (r first).2 <;> simp
  -- A second gate must read the pivot because its change reaches the output.
  have other : ∃ j : Fin n, j ≠ first ∧ ((l j).1 = v.val ∨ (r j).1 = v.val) := by
    by_contra miss
    have invariant (i : ℕ) : i < 10+n → i ≠ v.val → val x i = val y i := by
      induction i using Nat.strong_induction_on with
      | ind i ih =>
        intro hi ne
        by_cases small : i < 9
        · exact (raw x ⟨i,small⟩).trans ((sameRaw ⟨i,small⟩ ne).trans (raw y ⟨i,small⟩).symm)
        by_cases z : i=9
        · subst i; rw [zero,zero]
        by_cases f : i=10
        · subst i; exact masked
        let j : Fin n := ⟨i-10,by omega⟩
        have ij : i=10+j.val := by dsimp [j]; omega
        have jf : j≠first := by intro e; have eq := congrArg Fin.val e; dsimp [first,j] at eq; omega
        have nl : (l j).1 ≠ v.val := fun h => miss ⟨j,jf,Or.inl h⟩
        have nr : (r j).1 ≠ v.val := fun h => miss ⟨j,jf,Or.inr h⟩
        have bl : (l j).1 < i := ij ▸ (back j).1
        have br : (r j).1 < i := ij ▸ (back j).2
        have eqL := ih _ bl (bl.trans hi) nl
        have eqR := ih _ br (br.trans hi) nr
        rw [ij,step,step]
        dsimp only
        rw [eqL,eqR]
    exact diff ((output x).symm.trans ((invariant out.1 outBound (by have := v.isLt; omega)).trans (output y)))
  -- After setting the pivot to false, these gates become constants or signed copies.
  let cheap (j : Fin n) := (l j).1=9 ∨ (r j).1=9 ∨ (l j).1=(r j).1 ∨
     (l j).1=v.val ∨ (r j).1=v.val
  have c0 : cheap first := by
    rcases g0 with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (congrArg Fin.val h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨second,hne,hread⟩ := other
  have c1 : cheap second := Or.inr (Or.inr (Or.inr hread))
  let active := Finset.univ.filter (fun j : Fin n => ¬ cheap j)
  have count : active.card ≤ 11 := by
    have htwo : ({first,second} : Finset (Fin n)) ⊆ Finset.univ.filter cheap := by
      intro j hj
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> simp [c0,c1]
    have hcard := Finset.card_le_card htwo
    have eq := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) cheap
    simp [Ne.symm hne] at hcard
    simp only [Finset.card_univ,Fintype.card_fin] at eq
    change (Finset.univ.filter (fun j : Fin n => ¬ cheap j)).card ≤ 11
    omega
  -- Renumber the two vertex-deletion graphs onto eight inputs.
  let rename : Fin 9 → Fin 9 → Fin 8 := ![![0,0,1,2,3,4,5,6,7],
    ![0,0,4,7,5,1,3,6,2],
    ![1,0,0,4,6,2,5,3,7],
    ![2,1,0,0,3,7,6,5,4],
    ![0,1,2,3,0,4,5,6,7],
    ![0,1,2,7,5,0,6,3,4],
    ![1,0,4,7,5,2,0,6,3],
    ![1,2,3,7,5,0,6,0,4],
    ![1,2,7,4,6,0,3,5,0]]
  let embed (k : Fin 9) (z : Fin 8 → Bool) (i : Fin 9) := if i=k then false else z (rename k i)
  let smallClass (k : Fin 9) := decide (k=4 ∨ k=6 ∨ k=7)
  let edgesA : List ℕ := [1,12,23,5,16,27,46,57,47]
  let edgesB : List ℕ := [1,12,23,4,15,26,37,46,57,47]
  let funOf (es : List ℕ) (z : Fin 8 → Bool) :=
    es.any (fun e => z (Fin.ofNat 8 (e / 10)) && z (Fin.ofNat 8 (e % 10)))
  have cofactor : ∀ (k : Fin 9) (z : Fin 8 → Bool),
      F (embed k z) = (if smallClass k then funOf edgesB z else funOf edgesA z) := by
    decide +kernel
  let w (i : ℕ) (z : Fin 8 → Bool) := if i<10+n then val (embed v z) i else false
  let paid := active.image (fun j : Fin n => 10+j.val)
  have budget' : paid.card ≤ 11 := Finset.card_image_le.trans count
  have under (i : ℕ) (hi : i<10+n) (z) : w i z = val (embed v z) i := if_pos hi
  have atZero (z) : w 9 z = false := (under 9 (by omega) z).trans (zero _)
  have atV (z) : w v.val z = false := by
    rw [under _ (by have := v.isLt; omega),raw _ v]
    simp [embed]
  let mix (j : Fin n) (a b : Bool) :=
    if op j then (a ^^ (l j).2) && (b ^^ (r j).2) else (a ^^ (l j).2) || (b ^^ (r j).2)
  have wire (j : Fin n) (z) : w (10+j.val) z = mix j (w (l j).1 z) (w (r j).1 z) := by
    have lim : 10+j.val < 10+n := by omega
    rw [under _ lim,under _ ((back j).1.trans lim),under _ ((back j).2.trans lim)]
    exact step _ j
  have unary (i j : ℕ) (f : Bool → Bool) (h : ∀ z, w i z = f (w j z)) :
      (∃ c : Bool, ∀ z, w i z = c) ∨ (∃ p : Bool, ∀ z, w i z = (w j z ^^ p)) := by
    cases a : f false <;> cases b : f true
    · exact Or.inl ⟨false, fun z => by rw [h]; cases w j z <;> assumption⟩
    · exact Or.inr ⟨false, fun z => by rw [h]; cases w j z <;> simp [a,b]⟩
    · exact Or.inr ⟨true, fun z => by rw [h]; cases w j z <;> simp [a,b]⟩
    · exact Or.inl ⟨true, fun z => by rw [h]; cases w j z <;> assumption⟩
  have trace : ∀ i < 23, (∃ c : Bool, ∀ z, w i z = c) ∨
      (∃ k : Fin 8, ∃ p : Bool, ∀ z, w i z = (z k ^^ p)) ∨
      (∃ j < i, ∃ p : Bool, ∀ z, w i z = (w j z ^^ p)) ∨
      (i ∈ paid ∧ ∃ j < i, ∃ k < i, ∃ p q d : Bool, ∀ z,
        w i z = (if d then (w j z ^^ p) && (w k z ^^ q) else (w j z ^^ p) || (w k z ^^ q))) := by
    intro i _
    by_cases before : i < 10+n
    · by_cases small : i < 9
      · let k : Fin 9 := ⟨i,small⟩
        by_cases same : k=v
        · left; exact ⟨false,fun z => by change w k.val z=false; rw [same,atV]⟩
        · right; left
          exact ⟨rename v k,false,fun z => by
            rw [under i before]
            change val (embed v z) k.val = _
            rw [raw]; simp [embed,same]⟩
      by_cases hz : i=9
      · exact Or.inl ⟨false,by subst i; exact atZero⟩
      let g : Fin n := ⟨i-10,by omega⟩
      have ix : i = 10+g.val := by dsimp [g]; omega
      rw [ix]
      by_cases hc : cheap g
      · have red : ∃ j < 10+g.val, ∃ f : Bool → Bool, ∀ z, w (10+g.val) z=f (w j z) := by
          rcases hc with h | h | h | h | h
          · exact ⟨(r g).1,(back g).2,mix g false,fun z => by rw [wire,h,atZero]⟩
          · exact ⟨(l g).1,(back g).1,(fun a => mix g a false),fun z => by rw [wire,h,atZero]⟩
          · exact ⟨(r g).1,(back g).2,(fun a => mix g a a),fun z => by rw [wire,h]⟩
          · exact ⟨(r g).1,(back g).2,mix g false,fun z => by rw [wire,h,atV]⟩
          · exact ⟨(l g).1,(back g).1,(fun a => mix g a false),fun z => by rw [wire,h,atV]⟩
        obtain ⟨j,hj,f,hu⟩ := red
        rcases unary _ j f hu with h | ⟨p,h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl ⟨j,hj,p,h⟩))
      · right; right; right
        exact ⟨Finset.mem_image_of_mem _ (by simpa [active] using hc),
          (l g).1,(back g).1,(r g).1,(back g).2,(l g).2,(r g).2,op g,wire g⟩
    · exact Or.inl ⟨false,fun _ => if_neg before⟩
  have out23 : out.1 < 23 := by omega
  have value (z) : w out.1 z = F (embed v z) := (under _ outBound z).trans (output _)
  by_cases hc : smallClass v = true
  · obtain ⟨z,bad⟩ := degreeTwo w paid budget' trace _ out23
    have eq := cofactor v z
    rw [if_pos hc] at eq
    exact bad ((value z).trans eq)
  · obtain ⟨z,bad⟩ := degreeThree w paid budget' trace _ out23
    have eq := cofactor v z
    rw [if_neg hc] at eq
    exact bad ((value z).trans eq)
