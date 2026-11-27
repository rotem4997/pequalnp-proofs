import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_4982_414
    (compress : ∀ (n : ℕ) (U : Finset ℕ) (C : Circuit),
      (∀ u ∈ U, u < n) → Monotone2 C → ∃ D : Circuit, Monotone2 D ∧
      D.size + (C.gates.filter (fun g => g.inputs.any (fun i => decide (i ∈ U)))).length = C.size ∧
      ∀ x : List Bool, x.length = n → (∀ i ∈ U, x.getD i false = false) → D.eval x = C.eval x)
    (core : ∀ (q m : ℕ) (P : Fin (q*q) ↪ Fin m) (L : (Fin (q+1) × Fin q) ↪ Fin m)
      (F : Fin (q+1) → Fin (q*q) → Fin q), 300 ≤ q →
      (∀ d d', d ≠ d' → Function.Bijective fun u => (F d u,F d' u)) →
      ∀ (A : Finset (Fin (q*q))) (B : Finset (Fin (q+1) × Fin q)) (C : Circuit),
      let E := (A ×ˢ B).filter fun t => F t.2.1 t.1 = t.2.2
      let run := fun (X : Finset (Fin (q*q))) (Y : Finset (Fin (q+1) × Fin q)) => C.eval (incidenceInput (X.map P) (Y.map L))
      let readers := fun (i : ℕ) => (C.gates.filter fun g => decide (i ∈ g.inputs)).length
      Monotone2 C → (∀ e ∈ E, run {e.1} {e.2} = true) →
      (∀ X ⊆ A, ∀ Y ⊆ B, Y.card ≤ q → Disjoint (X ×ˢ Y) E → run X Y = false) →
      (∀ u ∈ A, 0 < readers (P u).val ∧ 99*readers (P u).val < (E.filter fun e => e.1 = u).card) →
      (∀ l ∈ B, 0 < readers (m+(L l).val) ∧ 99*readers (m+(L l).val) < (E.filter fun e => e.2 = l).card) → E.card ≤ 99*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin (x1 * x1) ↪ Fin x2) (x4 : Fin (x1 + (1 : ℕ)) × Fin x1 ↪ Fin x2) (x5 : Fin (x1 + (1 : ℕ)) → Fin (x1 * x1) → Fin x1) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → (∀ (x8 x9 : Fin (x1 + (1 : ℕ))), x8 ≠ x9 → Function.Bijective fun (x11 : Fin (x1 * x1)) => (x5 x8 x11, x5 x9 x11)) → PEqualNP.MetaComplexity.Monotone2 x6 → (∀ (x10 : Fin (x1 * x1)) (x11 : Fin (x1 + (1 : ℕ))), x6.eval (PEqualNP.GenericRejection.incidenceInput {x3 x10} {x4 (x11, x5 x11 x10)}) = Bool.true) → (∀ (x11 : Finset (Fin (x1 * x1))) (x12 : Finset (Fin (x1 + (1 : ℕ)) × Fin x1)), x12.card ≤ x1 → (∀ x14 ∈ x11, ∀ (x16 : Fin (x1 + (1 : ℕ))), (x16, x5 x16 x14) ∉ x12) → x6.eval (PEqualNP.GenericRejection.incidenceInput (Finset.map x3 x11) (Finset.map x4 x12)) = Bool.false) → x1 ^ (2 : ℕ) * (x1 + (1 : ℕ)) ≤ (99 : ℕ) * x6.size := by
  classical
  intro q m P L F original qmin net hm accept reject
  let AType := Fin (q*q)
  let BType := Fin (q+1) × Fin q
  let edges (A : Finset AType) (B : Finset BType) := (A ×ˢ B).filter (fun t => F t.2.1 t.1 = t.2.2)
  let input (X : Finset AType) (Y : Finset BType) := incidenceInput (X.map P) (Y.map L)
  let valid (A : Finset AType) (B : Finset BType) (C : Circuit) := Monotone2 C ∧
    (∀ e ∈ edges A B, C.eval (input {e.1} {e.2}) = true) ∧
    ∀ X ⊆ A, ∀ Y ⊆ B, Y.card ≤ q → Disjoint (X ×ˢ Y) (edges A B) → C.eval (input X Y) = false
  have eMem {A : Finset AType} {B : Finset BType} {e : AType × BType} :
      e ∈ edges A B ↔ (e.1 ∈ A ∧ e.2 ∈ B) ∧ F e.2.1 e.1 = e.2.2 := by simp [edges]
  have eCard : (edges Finset.univ Finset.univ).card = q^2*(q+1) := by
    let pointDir := (Finset.univ : Finset (AType × Fin (q+1)))
    have rep : (edges Finset.univ Finset.univ).card = pointDir.card := by
      apply Finset.card_bij (fun e _ => (e.1,e.2.1)) (by simp [pointDir])
      · rintro ⟨p,d,b⟩ h ⟨p',d',b'⟩ h' eq
        have hb := (eMem.mp h).2
        have hb' := (eMem.mp h').2
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
        simp_all
      · rintro ⟨p,d⟩ _
        exact ⟨(p,d,F d p),eMem.mpr ⟨⟨Finset.mem_univ _,Finset.mem_univ _⟩,rfl⟩,rfl⟩
    rw [rep]
    simp [pointDir,AType,pow_two]
  have start : valid Finset.univ Finset.univ original := by
    refine ⟨hm,?_,?_⟩
    · rintro ⟨p,d,v⟩ edge
      obtain rfl : F d p = v := (eMem.mp edge).2
      simpa [input] using accept p d
    · intro X _ Y _ cap dis
      apply reject X Y cap
      intro p hp d on
      exact Finset.disjoint_left.mp dis (Finset.mem_product.mpr ⟨hp,on⟩)
        ((eMem (e := (p,(d,F d p)))).mpr ⟨⟨Finset.mem_univ _,Finset.mem_univ _⟩,rfl⟩)
  by_contra! failed
  let bad (k : ℕ) := ∃ (A : Finset AType) (B : Finset BType) (C : Circuit),
    A.card+B.card=k ∧ valid A B C ∧ 99*C.size < (edges A B).card
  have fails : ∃ k, bad k := ⟨_,Finset.univ,Finset.univ,original,rfl,start,eCard ▸ failed⟩
  obtain ⟨A,B,C,count,live,small⟩ := Nat.find_spec fails
  have smaller (A' : Finset AType) (B' : Finset BType) (D : Circuit) (ok : valid A' B' D)
      (lt : A'.card+B'.card < A.card+B.card) : (edges A' B').card ≤ 99*D.size := by
    by_contra! more
    exact Nat.find_min fails (lt.trans_le count.le) ⟨A',B',D,rfl,ok,more⟩
  let readers (i : ℕ) := (C.gates.filter fun g => decide (i ∈ g.inputs)).length
  have one (i : ℕ) (hi : i < m+m) : ∃ D : Circuit, Monotone2 D ∧ D.size + readers i = C.size ∧
      ∀ x : List Bool, x.length = m+m → x.getD i false = false → D.eval x = C.eval x := by
    obtain ⟨D,hD,sz,equal⟩ := compress (m+m) {i} C (by simpa using hi) live.1
    have hit (g : Gate) : (g.inputs.any fun t => decide (t ∈ ({i}:Finset ℕ))) = decide (i ∈ g.inputs) := by
      apply Bool.eq_iff_iff.mpr
      simp
    refine ⟨D,hD,?_,?_⟩
    · simpa only [readers,hit] using sz
    · intro x len zero; exact equal x len (by simpa using zero)
  have length (X : Finset AType) (Y : Finset BType) : (input X Y).length = m+m := by unfold input incidenceInput; simp
  have leftOff (p : AType) (X : Finset AType) (Y : Finset BType) (off : p ∉ X) :
      (input X Y).getD (P p).val false = false := by
    unfold input incidenceInput
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD,(P p).isLt,off]
  have rightOff (l : BType) (X : Finset AType) (Y : Finset BType) (off : l ∉ Y) :
      (input X Y).getD (m+(L l).val) false = false := by
    unfold input incidenceInput
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD,(L l).isLt]
    rintro a b h rfl
    exact off h
  have transfer (A' : Finset AType) (B' : Finset BType) (D : Circuit) (hD : Monotone2 D)
      (sa : A' ⊆ A) (sb : B' ⊆ B)
      (agrees : ∀ X ⊆ A', ∀ Y ⊆ B', D.eval (input X Y) = C.eval (input X Y)) : valid A' B' D := by
    refine ⟨hD,?_,?_⟩
    · intro e he
      obtain ⟨⟨hp,hl⟩,inc⟩ := eMem.mp he
      rw [agrees _ (by simpa using hp) _ (by simpa using hl)]
      exact live.2.1 e (eMem.mpr ⟨⟨sa hp,sb hl⟩,inc⟩)
    · intro X sx Y sy cap dis
      rw [agrees X sx Y sy]
      apply live.2.2 X (sx.trans sa) Y (sy.trans sb) cap
      apply Finset.disjoint_left.mpr
      intro e mem edge
      exact Finset.disjoint_left.mp dis mem (eMem.mpr ⟨⟨sx (Finset.mem_product.mp mem).1,sy (Finset.mem_product.mp mem).2⟩,(eMem.mp edge).2⟩)
  let step (z : List Bool) (g : Gate) := z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]
  have untouched (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
      (gs.foldl step x).getD i false = x.getD i false := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (step x g) (by simp [step];omega)]
      exact List.getD_append _ _ _ _ hi
  have far {α : Type} (z : List α) (v d : α) (j : ℕ) (hne : j ≠ z.length) :
      (z ++ [v]).getD j d = z.getD j d := by
    by_cases h : j < z.length
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
  have simulate (i : ℕ) (gs : List Gate) (noRead : ∀ g ∈ gs, i ∉ g.inputs) (x y : List Bool)
      (len : x.length = y.length) (same : ∀ j, j ≠ i → x.getD j false = y.getD j false) :
      ∀ j, j ≠ i → (gs.foldl step x).getD j false = (gs.foldl step y).getD j false := by
    induction gs generalizing x y with
    | nil => exact same
    | cons g gs ih =>
      rw [List.foldl_cons,List.foldl_cons]
      refine ih (fun a ha => noRead a (List.mem_cons_of_mem _ ha)) _ _ (by simp [step,len]) ?_
      have ins : (g.inputs.map fun v => x.getD v false) = g.inputs.map fun v => y.getD v false := by
        apply List.map_congr_left; intro v hv
        apply same v; rintro rfl; exact noRead g (by simp) hv
      intro j ne
      by_cases atEnd : j = x.length
      · subst j
        simp only [step,ins]
        have last (z : List Bool) (v : Bool) : (z++[v]).getD z.length false = v := by simp
        rw [last,len,last]
      · exact (far _ _ _ _ atEnd).trans ((same j ne).trans (far _ _ _ _ (by omega)).symm)
  have inputBit (X : Finset AType) (Y : Finset BType) (j : ℕ) : (input X Y).getD j false = true ↔
      (∃ p ∈ X, (P p).val = j) ∨ (∃ l ∈ Y, m+(L l).val = j) := by
    unfold input incidenceInput
    by_cases h : j < m
    · rw [List.getD_append _ _ _ _ (by simpa using h)]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,h,dite_true,Option.getD_some,decide_eq_true_eq,Finset.mem_map]
      constructor
      · rintro ⟨p,hp,eq⟩; exact Or.inl ⟨p,hp,congrArg Fin.val eq⟩
      · rintro (⟨p,hp,eq⟩|⟨l,hl,eq⟩)
        · exact ⟨p,hp,Fin.ext eq⟩
        · omega
    · rw [List.getD_append_right _ _ _ _ (by simp;omega)]
      simp only [List.length_ofFn,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
      by_cases h2 : j-m < m
      · simp only [h2,dite_true,Option.getD_some,decide_eq_true_eq,Finset.mem_map]
        constructor
        · rintro ⟨l,hl,eq⟩; exact Or.inr ⟨l,hl,by have t := congrArg Fin.val eq; dsimp at t; omega⟩
        · rintro (⟨p,hp,eq⟩|⟨l,hl,eq⟩)
          · have := (P p).isLt; omega
          · exact ⟨l,hl,Fin.ext (by change (L l).val = j-m; omega)⟩
      · simp only [h2,dite_false,Option.getD_none,Bool.false_eq_true,false_iff,not_or]
        constructor
        · rintro ⟨p,hp,eq⟩; have := (P p).isLt; omega
        · rintro ⟨l,hl,eq⟩; have := (L l).isLt; omega
  have activeReads (p : AType) (l : BType) (incl : (p,l) ∈ edges A B) :
      0 < readers (P p).val ∧ 0 < readers (m+(L l).val) := by
    have acc := live.2.1 (p,l) incl
    have hp := (eMem.mp incl).1.1
    have hl := (eMem.mp incl).1.2
    have rejP : C.eval (input {p} ∅) = false := live.2.2 _ (by simpa using hp) _ (by simp) (by simp) (by simp)
    have rejL : C.eval (input ∅ {l}) = false := live.2.2 _ (by simp) _ (by simpa using hl) (by simp;omega) (by simp)
    have test (i : ℕ) (linear solo : List Bool) (len : linear.length = m+m) (lenS : solo.length = m+m)
        (rejectLin : C.eval linear = false) (rejectSolo : C.eval solo = false) (lt : i < m+m)
        (atI : solo.getD i false = true)
        (offI : ∀ j, j ≠ i → (input {p} {l}).getD j false = linear.getD j false) : 0 < readers i := by
      by_contra! zero
      have empty : (C.gates.filter fun g => decide (i ∈ g.inputs)) = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero zero)
      have noRead (g) (hg : g ∈ C.gates) : i ∉ g.inputs := by
        intro h
        have mem : g ∈ C.gates.filter (fun a => decide (i ∈ a.inputs)) := List.mem_filter.mpr ⟨hg,decide_eq_true h⟩
        rw [empty] at mem; simp at mem
      by_cases out : C.output = i
      · have eq := untouched C.gates solo i (by omega)
        change (C.gates.foldl step solo).getD C.output false = false at rejectSolo
        rw [out,eq,atI] at rejectSolo
        contradiction
      · have eq := simulate i C.gates noRead (input {p} {l}) linear ((length _ _).trans len.symm) offI C.output out
        change C.eval (input {p} {l}) = C.eval linear at eq
        rw [acc,rejectLin] at eq; contradiction
    constructor
    · apply test (P p).val (input ∅ {l}) (input {p} ∅) (length _ _) (length _ _) rejL rejP (by have := (P p).isLt;omega)
      · rw [inputBit]; simp
      · intro j ne; apply Bool.eq_iff_iff.mpr
        simp only [inputBit,Finset.mem_singleton,exists_eq_left,Finset.notMem_empty,false_and,exists_false,false_or]
        simp [Ne.symm ne]
    · apply test (m+(L l).val) (input {p} ∅) (input ∅ {l}) (length _ _) (length _ _) rejP rejL (by have := (L l).isLt;omega)
      · rw [inputBit]; simp
      · intro j ne; apply Bool.eq_iff_iff.mpr
        simp only [inputBit,Finset.mem_singleton,exists_eq_left,Finset.notMem_empty,false_and,exists_false,or_false]
        simp [Ne.symm ne]
  have leftDense (p) (inA : p ∈ A) : 99*readers (P p).val < ((edges A B).filter fun e => e.1 = p).card := by
    obtain ⟨D,hD,sz,eq⟩ := one (P p).val (by have := (P p).isLt; omega)
    have ok : valid (A.erase p) B D := transfer _ _ D hD (Finset.erase_subset _ _) Finset.Subset.rfl (by
      intro X sx Y sy
      exact eq _ (length X Y) (leftOff p X Y (fun hx => Finset.notMem_erase _ _ (sx hx))))
    have below := smaller _ _ _ ok (by have := Finset.card_erase_lt_of_mem inA; omega)
    have erased : edges (A.erase p) B = (edges A B).filter fun e => e.1 ≠ p := by
      ext e; simp only [eMem,Finset.mem_erase,Finset.mem_filter]; tauto
    have partition := Finset.card_filter_add_card_filter_not (s := edges A B) (p := fun e => e.1 = p)
    rw [←erased] at partition
    omega
  have rightDense (l) (inB : l ∈ B) : 99*readers (m+(L l).val) < ((edges A B).filter fun e => e.2 = l).card := by
    obtain ⟨D,hD,sz,eq⟩ := one (m+(L l).val) (by have := (L l).isLt; omega)
    have ok : valid A (B.erase l) D := transfer _ _ D hD Finset.Subset.rfl (Finset.erase_subset _ _) (by
      intro X sx Y sy
      exact eq _ (length X Y) (rightOff l X Y (fun hx => Finset.notMem_erase _ _ (sy hx))))
    have below := smaller _ _ _ ok (by have := Finset.card_erase_lt_of_mem inB; omega)
    have erased : edges A (B.erase l) = (edges A B).filter fun e => e.2 ≠ l := by
      ext e; simp only [eMem,Finset.mem_erase,Finset.mem_filter]; tauto
    have partition := Finset.card_filter_add_card_filter_not (s := edges A B) (p := fun e => e.2 = l)
    rw [←erased] at partition
    omega
  refine small.not_ge (core q m P L F qmin net A B C live.1 live.2.1 live.2.2 ?_ ?_)
  · intro u hu
    have lt := leftDense u hu
    obtain ⟨e,he⟩ := Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) lt)
    obtain ⟨mem,eq⟩ := Finset.mem_filter.mp he
    exact ⟨eq ▸ (activeReads e.1 e.2 mem).1,lt⟩
  · intro l hl
    have lt := rightDense l hl
    obtain ⟨e,he⟩ := Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) lt)
    obtain ⟨mem,eq⟩ := Finset.mem_filter.mp he
    exact ⟨eq ▸ (activeReads e.1 e.2 mem).2,lt⟩
