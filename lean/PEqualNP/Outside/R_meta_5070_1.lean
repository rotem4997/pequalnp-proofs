import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_5070_1
  (simpleCount : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
    let U := Fin n → Bool
    let one (p : Fin n) : U := fun x => decide (x = p)
    let off : U := fun _ => false
    let safe (S : Set (U × U)) :=
      ∀ y : U, Fintype.card {l : Fin n // y l = true} ≤ q →
        (fun p => decide (¬∃ l, I p l ∧ y l = true), y) ∉ S
    2 ≤ q → (∀ p, Fintype.card {l : Fin n // I p l} = q+1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
    ∀ (g : ℕ) (W : ℕ → Set (U × U)) (a b : Fin g → ℕ),
      (∀ p : Fin n, W p.val = {x | x.1 p = true} ∧ W (n+p.val) = {x | x.2 p = true}) →
      (∀ i : Fin g, max (a i) (b i) < n+n+i.val ∧
        W (n+n+i.val) ∈ [W (a i) ∪ W (b i), W (a i), ∅, W (a i) ∩ W (b i)]) →
      let joins (e : Fin n × Fin n) (i : Fin g) :=
        W (n+n+i.val) = W (a i) ∩ W (b i) ∧
          (((one e.1, off) ∈ W (a i) ∧ (off, one e.2) ∈ W (b i)) ∨
            ((one e.1, off) ∈ W (b i) ∧ (off, one e.2) ∈ W (a i)))
      {e | I e.1 e.2 ∧ ∃ i : Fin g, safe (W (n+n+i.val)) ∧ joins e i}.ncard ≤ 4*g)
  (hardCount : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
    let U := Fin n → Bool
    let one (p : Fin n) : U := fun x => decide (x = p)
    let off : U := fun _ => false
    let safe (S : Set (U × U)) :=
      ∀ y : U, Fintype.card {l : Fin n // y l = true} ≤ q →
        (fun p => decide (¬∃ l, I p l ∧ y l = true), y) ∉ S
    200 ≤ q → n = q^2+q+1 →
    (∀ l, Fintype.card {p : Fin n // I p l} = q+1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
    ∀ (g o : ℕ) (W : ℕ → Set (U × U)) (a b : Fin g → ℕ) (T : Set (Fin n × Fin n)),
      o < n+n+g → n+n ≤ g+1 →
      (∀ p : Fin n, W p.val = {x | x.1 p = true} ∧ W (n+p.val) = {x | x.2 p = true}) →
      (∀ i : Fin g, max (a i) (b i) < n+n+i.val ∧
        W (n+n+i.val) ∈ [W (a i) ∪ W (b i), W (a i), ∅, W (a i) ∩ W (b i)]) →
      (∀ p l, I p l → (one p, one l) ∈ W o) → safe (W o) →
      92*g+n < T.ncard → 23*(n*q)+25*n < 25*T.ncard →
      (∀ e ∈ T, I e.1 e.2 ∧
        (∃ i : Fin g, ¬safe (W (n+n+i.val)) ∧ W (n+n+i.val) = W (a i) ∩ W (b i) ∧
          (one e.1,one e.2) ∈ W (n+n+i.val)) ∧
        ∀ (i : Fin g) x y, max x y < n+n+i.val →
        W (n+n+i.val) = W x ∩ W y →
        ((W (n+n+i.val) ⊆ W o ∧
            ∃ P L : Set U, W x = P ×ˢ Set.univ ∧ W y = Set.univ ×ˢ L) ∨
          (((x,y) = (a i,b i) ∨ (x,y) = (b i,a i)) ∧ safe (W (n+n+i.val)) ∧
            (one e.1,off) ∈ W x ∧ (off,one e.2) ∈ W y)) →
        (one e.1, one e.2) ∉ W (n+n+i.val)) →
      False)
  : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3],
   let x5 : Type := Fin x2 → Bool;
   have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);
   have x7 : ℕ := x2 + x2;
   (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x10 : Fin x2), Fintype.card { x11 : Fin x2 // x3 x11 x10 } = x1 + (1 : ℕ)) → (∀ (x11 x12 : Fin x2), x11 ≠ x12 → ∃! x14 : Fin x2, x3 x11 x14 ∧ x3 x12 x14) → ∀ (x12 x13 : ℕ) (x14 : ℕ → Set (x5 × x5)) (x15 : Set (Fin x2 × Fin x2)), x13 < x7 + x12 → x7 ≤ x12 + (1 : ℕ) → (∀ (x18 : Fin x2), x14 ↑x18 = {x19 : x5 × x5 | x19.1 x18 = Bool.true} ∧ x14 (x2 + ↑x18) = {x19 : x5 × x5 | x19.2 x18 = Bool.true}) → (∀ x19 < x12, ∃ (x21 : ℕ) (x22 : ℕ), Max.max x21 x22 < x7 + x19 ∧ x14 (x7 + x19) ∈ [x14 x21 ∪ x14 x22, x14 x21, ∅, x14 x21 ∩ x14 x22]) → (∀ (x20 x21 : Fin x2), x3 x20 x21 → (x6 x20, x6 x21) ∈ x14 x13) → (∀ (x21 : x5), Fintype.card { x22 : Fin x2 // x21 x22 = Bool.true } ≤ x1 → (fun (x23 : Fin x2) => Decidable.decide ¬∃ (x24 : Fin x2), x3 x23 x24 ∧ x21 x24 = Bool.true, x21) ∉ x14 x13) → x15 ⊆ {x22 : Fin x2 × Fin x2 | x3 x22.1 x22.2} → (96 : ℕ) * x12 + x2 < x15.ncard → (24 : ℕ) * (x2 * x1) + (25 : ℕ) * x2 < (25 : ℕ) * x15.ncard → (∀ x25 < x12, x14 (x7 + x25) ⊆ x14 x13 → ∀ (x28 x29 : ℕ), Max.max x28 x29 < x7 + x25 → x14 (x7 + x25) = x14 x28 ∩ x14 x29 → ∀ (x32 x33 : Set x5), x14 x28 = x32 ×ˢ Set.univ → x14 x29 = Set.univ ×ˢ x33 → ∀ x36 ∈ x15, (x6 x36.1, x6 x36.2) ∉ x14 (x7 + x25)) → False := by
  have geometry (q n : ℕ) (qPos : 1 ≤ q) (size : n = q^2 + q + 1)
      (I : Fin n → Fin n → Prop) [DecidableRel I]
      (lineSize : ∀ l : Fin n, Fintype.card {p : Fin n // I p l} = q+1)
      (uniqueJoin : ∀ a b : Fin n, a ≠ b → ∃! l : Fin n, I a l ∧ I b l) :
      (∀ z : Fin n, Fintype.card {l : Fin n // I z l} = q+1) := by
    let on (l : Fin n) := Finset.univ.filter fun p : Fin n => I p l
    let through (z : Fin n) := Finset.univ.filter fun l : Fin n => I z l
    let other (z l : Fin n) := (on l).erase z
    have onMem (p l : Fin n) : p ∈ on l ↔ I p l := by
      simp only [on,Finset.mem_filter,Finset.mem_univ,true_and]
    have throughMem (z l : Fin n) : l ∈ through z ↔ I z l := by
      simp only [through,Finset.mem_filter,Finset.mem_univ,true_and]
    have otherMem (z l p : Fin n) : p ∈ other z l ↔ p ≠ z ∧ I p l := by
      simp only [other,Finset.mem_erase,onMem]
    have onCard (l : Fin n) : (on l).card = q+1 :=
      (Fintype.card_subtype (fun p : Fin n => I p l)).symm.trans (lineSize l)
    have otherCard (z l : Fin n) (inc : I z l) : (other z l).card = q := by
      have card := Finset.card_erase_add_one ((onMem z l).mpr inc)
      change (other z l).card+1 = (on l).card at card
      rw [onCard] at card
      omega
    have totalOther (z : Fin n) :
        ((Finset.univ : Finset (Fin n)).erase z).card = (q+1)*q := by
      have card := Finset.card_erase_add_one (Finset.mem_univ z)
      rw [Finset.card_univ,Fintype.card_fin] at card
      have cardSize := card.trans size
      have square : q^2+q = (q+1)*q := by ring
      omega
    have throughCard (z : Fin n) : (through z).card = q+1 := by
      have covers : (through z).biUnion (other z) = (Finset.univ : Finset (Fin n)).erase z := by
        ext p
        rw [Finset.mem_biUnion,Finset.mem_erase]
        constructor
        · rintro ⟨l,_,hp⟩
          exact ⟨((otherMem z l p).mp hp).1,Finset.mem_univ _⟩
        · rintro ⟨hp,_⟩
          obtain ⟨l,inc,_⟩ := uniqueJoin z p hp.symm
          exact ⟨l,(throughMem z l).mpr inc.1,(otherMem z l p).mpr ⟨hp,inc.2⟩⟩
      have disjoint : ((through z : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (other z) := by
        intro l hl m hm ne
        apply Finset.disjoint_left.mpr
        intro p hp hq
        have pl := (otherMem z l p).mp hp
        have pm := (otherMem z m p).mp hq
        obtain ⟨a,_,unq⟩ := uniqueJoin z p pl.1.symm
        have el : l = a := unq l ⟨(throughMem z l).mp hl,pl.2⟩
        have em : m = a := unq m ⟨(throughMem z m).mp hm,pm.2⟩
        exact ne (el.trans em.symm)
      have count := Finset.card_biUnion disjoint
      rw [covers] at count
      have sub :
          ∑ l ∈ through z, (other z l).card = ∑ _l ∈ through z, q := by
        apply Finset.sum_congr rfl
        intro l hl
        exact otherCard z l ((throughMem z l).mp hl)
      rw [sub,Finset.sum_const,nsmul_eq_mul,totalOther] at count
      exact Nat.mul_right_cancel (by omega : 0 < q) count.symm
    intro z
    exact (Fintype.card_subtype (fun l : Fin n => I z l)).trans (throughCard z)
  intro q n I inst U one base hq hn hline hjoin g o W T ho hg hinput hstep hpos hneg hflags hmass hdensity hPure
  classical
  have stepChoices (i : Fin g) : ∃ a b : ℕ, max a b < base+i.val ∧
      W (base+i.val) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b] :=
    hstep i.val i.isLt
  choose a b chosen using stepChoices
  let off : U := fun _ => false
  let safe (S : Set (U × U)) :=
    ∀ y : U, Fintype.card {l : Fin n // y l = true} ≤ q →
      (fun p => decide (¬∃ l, I p l ∧ y l = true), y) ∉ S
  let D : Set (Fin n × Fin n) :=
    {e | I e.1 e.2 ∧ ∃ i : Fin g, safe (W (base+i.val)) ∧
      W (base+i.val) = W (a i) ∩ W (b i) ∧
        (((one e.1, off) ∈ W (a i) ∧ (off, one e.2) ∈ W (b i)) ∨
          ((one e.1, off) ∈ W (b i) ∧ (off, one e.2) ∈ W (a i)))}
  have hpoint : ∀ p, Fintype.card {l : Fin n // I p l} = q+1 :=
    geometry q n (by omega) hn I hline hjoin
  have count : D.ncard ≤ 4*g := simpleCount q n I (by omega) hpoint hjoin g W a b hinput chosen
  let R := T \ D
  have part : R.ncard + (T ∩ D).ncard = T.ncard := by
    have eq : R = T \ (T ∩ D) := by
      ext e
      simp only [R, Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    rw [eq]
    exact Set.ncard_sdiff_add_ncard_of_subset Set.inter_subset_left
  have kept : 92*g+n < R.ncard := by
    have bound : (T ∩ D).ncard ≤ D.ncard := Set.ncard_le_ncard Set.inter_subset_right
    omega
  have dense : 23*(n*q)+25*n < 25*R.ncard := by
    have bound : (T ∩ D).ncard ≤ D.ncard := Set.ncard_le_ncard Set.inter_subset_right
    have share : 23*T.ncard+n < 24*R.ncard := by omega
    omega
  -- Monotonicity of the chosen history lets us compare any input with the designated negative row.
  let rises (x y : U × U) :=
    (∀ p, x.1 p = true → y.1 p = true) ∧ (∀ l, x.2 l = true → y.2 l = true)
  have mono (k : ℕ) (hk : k < base+g) (x y : U × U) (hxy : rises x y) :
      x ∈ W k → y ∈ W k := by
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hin
      by_cases hp : k < n
      · let p : Fin n := ⟨k,hp⟩
        change x ∈ W p.val at hin
        change y ∈ W p.val
        rw [(hinput p).1] at hin ⊢
        exact hxy.1 p hin
      by_cases hl : k < base
      · let l : Fin n := ⟨k-n,by dsimp [base] at hl; omega⟩
        have eq : n + l.val = k := by dsimp [l]; omega
        rw [← eq, (hinput l).2] at hin ⊢
        exact hxy.2 l hin
      let i : Fin g := ⟨k-base,by omega⟩
      have eq : base+i.val = k := by dsimp [i]; omega
      have bound := (chosen i).1
      change max (a i) (b i) < base+i.val at bound
      rw [eq] at bound
      have ha := (max_lt_iff.mp bound).1
      have hb := (max_lt_iff.mp bound).2
      have op := (chosen i).2
      rw [eq] at op
      simp only [List.mem_cons, List.not_mem_nil, or_false] at op
      rcases op with u | c | e | m
      · rw [u] at hin ⊢
        exact hin.elim (fun h => Or.inl (ih _ ha (ha.trans hk) h)) (fun h => Or.inr (ih _ hb (hb.trans hk) h))
      · rw [c] at hin ⊢
        exact ih _ ha (ha.trans hk) hin
      · rw [e] at hin
        exact hin.elim
      · rw [m] at hin ⊢
        exact ⟨ih _ ha (ha.trans hk) hin.1, ih _ hb (hb.trans hk) hin.2⟩
  have offCard : Fintype.card {l : Fin n // off l = true} = 0 := by
    let _ : IsEmpty {l : Fin n // off l = true} := ⟨fun l => by cases l.property⟩
    exact Fintype.card_of_isEmpty
  have oneCard (l : Fin n) : Fintype.card {u : Fin n // one l u = true} ≤ 1 := by
    have le := Fintype.card_le_of_injective (f := fun _ : {u : Fin n // one l u = true} => ())
      (fun x y _ => Subtype.ext ((of_decide_eq_true x.property).trans (of_decide_eq_true y.property).symm))
    exact le
  have noPoint (p : Fin n) : (one p,off) ∉ W o := by
    let X : U := fun r => decide (¬∃ l, I r l ∧ off l = true)
    apply mt (mono o ho (one p,off) (X,off) ?_) (hneg off (offCard ▸ Nat.zero_le q))
    refine ⟨?_, fun _ h => h⟩
    intro r _
    exact decide_eq_true (by simp [off])
  have noLine (l : Fin n) : (off,one l) ∉ W o := by
    let X : U := fun p => decide (¬∃ u, I p u ∧ one l u = true)
    apply mt (mono o ho (off,one l) (X,one l) ?_) (hneg (one l) ((oneCard l).trans (by omega)))
    exact ⟨(fun _ h => by cases h), fun _ h => h⟩
  let joins (e : Fin n × Fin n) (i : Fin g) :=
    W (base+i.val) = W (a i) ∩ W (b i) ∧
      (((one e.1, off) ∈ W (a i) ∧ (off, one e.2) ∈ W (b i)) ∨
        ((one e.1, off) ∈ W (b i) ∧ (off, one e.2) ∈ W (a i)))
  have jointSource (p l : Fin n) (edge : I p l): ∃ i : Fin g, joins (p,l) i ∧ (one p,one l) ∈ W (base+i.val) := by
    let joint (k : ℕ) := (one p,one l) ∈ W k ∧ (one p,off) ∉ W k ∧ (off,one l) ∉ W k
    let candidate (k : ℕ) := k < base+g ∧ joint k
    have existsC : ∃ k, candidate k := ⟨o, ho, hpos p l edge, noPoint p, noLine l⟩
    let k := Nat.find existsC
    have current : candidate k := Nat.find_spec existsC
    have earlier (h : ℕ) (hr : h < k) : ¬ joint h :=
      fun v => (Nat.not_lt_of_ge (Nat.find_min' existsC (show candidate h from ⟨hr.trans current.1,v⟩))) hr
    have nraw : base ≤ k := by
      by_contra! hr
      by_cases hp : k < n
      · let u : Fin n := ⟨k,hp⟩
        have first := current.2.1
        have never := current.2.2.1
        change (one p,one l) ∈ W u.val at first
        change (one p,off) ∉ W u.val at never
        rw [(hinput u).1] at first never
        exact never first
      · let u : Fin n := ⟨k-n,by dsimp [base] at hr; omega⟩
        have eq : n+u.val = k := by dsimp [u]; omega
        have first := current.2.1
        have never := current.2.2.2
        rw [← eq, (hinput u).2] at first never
        exact never first
    let i : Fin g := ⟨k-base,by have := current.1; omega⟩
    have eq : base+i.val = k := by dsimp [i]; omega
    have bound := (chosen i).1
    change max (a i) (b i) < base+i.val at bound
    rw [eq] at bound
    have ha := (max_lt_iff.mp bound).1
    have hb := (max_lt_iff.mp bound).2
    have op := (chosen i).2
    rw [eq] at op
    simp only [List.mem_cons, List.not_mem_nil, or_false] at op
    obtain ⟨positive, notP, notL⟩ := current.2
    rcases op with union | copy | empty | merge
    · rw [union] at positive notP notL
      rcases positive with left | right
      · exact (earlier _ ha ⟨left,fun h => notP (Or.inl h),fun h => notL (Or.inl h)⟩).elim
      · exact (earlier _ hb ⟨right,fun h => notP (Or.inr h),fun h => notL (Or.inr h)⟩).elim
    · rw [copy] at positive notP notL
      exact (earlier _ ha ⟨positive,notP,notL⟩).elim
    · rw [empty] at positive
      exact positive.elim
    · rw [merge] at positive notP notL
      refine ⟨i, ⟨?_, ?_⟩, ?_⟩
      · simpa only [eq] using merge
      · have single (h : ℕ) (hr : h < k) (hp : (one p,one l) ∈ W h) :
            (one p,off) ∈ W h ∨ (off,one l) ∈ W h := by
          by_contra! no
          exact earlier h hr ⟨hp,no.1,no.2⟩
        rcases single (a i) ha positive.1 with haP | haL
        · rcases single (b i) hb positive.2 with hbP | hbL
          · exact (notP ⟨haP,hbP⟩).elim
          · exact Or.inl ⟨haP,hbL⟩
        · rcases single (b i) hb positive.2 with hbP | hbL
          · exact Or.inr ⟨hbP,haL⟩
          · exact (notL ⟨haL,hbL⟩).elim
      · rw [eq,merge]
        exact positive
  apply hardCount q n I hq hn hline hjoin g o W a b R ho hg hinput chosen hpos hneg kept dense
  intro e he
  have incident : I e.1 e.2 := hflags he.1
  obtain ⟨j, hj, hpair⟩ := jointSource e.1 e.2 incident
  have joint : joins e j := by simpa only [Prod.mk.eta] using hj
  have failsSafety : ¬safe (W (base+j.val)) := fun hs => he.2 ⟨incident,j,hs,joint⟩
  refine ⟨incident, ⟨j,failsSafety,joint.1,hpair⟩, fun i x y prior merge h => ?_⟩
  rcases h with ⟨below,P,L,hP,hL⟩ | ⟨order,hsafe,hP,hL⟩
  · exact hPure i.val i.isLt below x y prior merge P L hP hL e he.1
  · exact False.elim (he.2 (by
      rcases order with ordered | reversed
      · rcases Prod.mk.inj ordered with ⟨hx,hy⟩
        rw [hx,hy] at merge
        rw [hx] at hP
        rw [hy] at hL
        exact ⟨incident, i, hsafe, merge, Or.inl ⟨hP,hL⟩⟩
      · rcases Prod.mk.inj reversed with ⟨hx,hy⟩
        rw [hx,hy] at merge
        rw [hx] at hP
        rw [hy] at hL
        exact ⟨incident, i, hsafe, merge.trans (Set.inter_comm _ _), Or.inr ⟨hP,hL⟩⟩))
