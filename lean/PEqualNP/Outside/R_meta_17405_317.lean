import PEqualNP.Defs
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.R_meta_17405_317
    (front : ∃ f : ℕ → Set (Fin 26 → Bool), (∀ i : Fin 26, f i.val = {x | x i = true}) ∧
      (∀ j : Fin 6, f (26+j.val) = f j.val ∪ f (j.val+1) ∧ f (32+j.val) = f (j.val+3) ∪ f ((j.val+9)%13) ∧ f (38+j.val) = f (26+j.val) ∪ f (32+j.val)) ∧
      f 54 = {x : Fin 26 → Bool | ∃ p l : Fin 13, l.val < 6 ∧ p-l ∈ ([0,1,3,9] : List (Fin 13)) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true} ∧ ∀ j : Fin 29, ∃ a b : Fin (26+j.val), (f (26+j.val) = f a.val ∩ f b.val ∨ f (26+j.val) = f a.val ∪ f b.val))
    (back : ∃ f : ℕ → Set (Fin 26 → Bool), (∀ i : Fin 26, f i.val = {x | x i = true}) ∧
      (∀ j : Fin 6, f (26+j.val) = f j.val ∪ f (j.val+1) ∧ f (32+j.val) = f (j.val+3) ∪ f ((j.val+9)%13) ∧ f (38+j.val) = f (26+j.val) ∪ f (32+j.val)) ∧
      f 54 = {x : Fin 26 → Bool | ∃ p l : Fin 13, l.val < 6 ∧ p-l ∈ ([0,1,3,9] : List (Fin 13)) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true} ∧ f 88 = {x : Fin 26 → Bool | ∃ p l : Fin 13, p-l ∈ ([0,1,3,9] : List (Fin 13)) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true} ∧ ∀ j : Fin 34, ∃ a b : Fin (55+j.val), (a.val < 44 ∨ 54 ≤ a.val) ∧ (b.val < 44 ∨ 54 ≤ b.val) ∧ (f (55+j.val) = f a.val ∩ f b.val ∨ f (55+j.val) = f a.val ∪ f b.val)) : (have x1 : Finset (Fin (13 : ℕ)) := Finset.univ; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) => Fin.append (fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x3)) fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (63 : ℕ) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 (x3 {x5} {x6}) = Bool.true) ∧ (∀ (x5 : Finset (Fin (13 : ℕ))), x5.card ≤ (3 : ℕ) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 (x3 x5 ({x7 ∈ x1 | ∀ x8 ∈ x5, ¬x2 x8 x7})) = Bool.false) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x5.card ≤ (3 : ℕ) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 (x3 ({x7 ∈ x1 | ∀ x8 ∈ x5, ¬x2 x7 x8}) x5) = Bool.false) := by
  classical
  let D : List (Fin 13) := [0,1,3,9]
  let I (p l : Fin 13) := p-l ∈ D
  let input (P L : Finset (Fin 13)) := Fin.append (fun p : Fin 13 => decide (p ∈ P)) (fun l : Fin 13 => decide (l ∈ L))
  have left (P L : Finset (Fin 13)) (p : Fin 13) : input P L (Fin.castAdd 13 p) = decide (p ∈ P) := Fin.append_left _ _ _
  have right (P L : Finset (Fin 13)) (l : Fin 13) : input P L (Fin.natAdd 13 l) = decide (l ∈ L) := Fin.append_right _ _ _
  let col (i : Fin 26) : Set (Fin 26 → Bool) := {x | x i = true}
  let mask : Set (Fin 26 → Bool) := {x : Fin 26 → Bool | ∃ p l : Fin 13, p-l ∈ ([0,1,3,9] : List (Fin 13)) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true}
  obtain ⟨f, fbase, fshare, fout, fstep⟩ := front
  obtain ⟨b, bbase, bshare, bin, bout, bstep⟩ := back
  let w (i : ℕ) := if i < 55 then f i else b i
  have frontWire (i : ℕ) (h : i < 55) : w i = f i := ite_eq_left h
  have backWire (i : ℕ) (h : i < 44 ∨ 54 ≤ i) : w i = b i := by
    by_cases hi : i < 55
    · rw [frontWire i hi]
      rcases h with hl | hl
      · by_cases low : i < 26
        · exact (fbase ⟨i,low⟩).trans (bbase ⟨i,low⟩).symm
        · have same (u : ℕ) (hu : u < 26) : f u = b u :=
            (fbase ⟨u,hu⟩).trans (bbase ⟨u,hu⟩).symm
          have s1 (j : Fin 6) : f (26+j.val) = b (26+j.val) := by
            rw [(fshare j).1,(bshare j).1,same j.val (by omega),same (j.val+1) (by omega)]
          have s2 (j : Fin 6) : f (32+j.val) = b (32+j.val) := by
            rw [(fshare j).2.1,(bshare j).2.1,same (j.val+3) (by omega),same ((j.val+9)%13) (by omega)]
          by_cases hi1 : i < 32
          · let j : Fin 6 := ⟨i-26,by omega⟩
            have eq : 26+j.val = i := by dsimp [j]; omega
            exact eq ▸ s1 j
          by_cases hi2 : i < 38
          · let j : Fin 6 := ⟨i-32,by omega⟩
            have eq : 32+j.val = i := by dsimp [j]; omega
            exact eq ▸ s2 j
          · let j : Fin 6 := ⟨i-38,by omega⟩
            have eq : 38+j.val = i := by dsimp [j]; omega
            rw [← eq,(fshare j).2.2,(bshare j).2.2,s1 j,s2 j]
      · have : i = 54 := by omega
        subst i
        exact fout.trans bin.symm
    · exact ite_eq_right hi
  have base (i : Fin 26) : w i.val = col i := (frontWire _ (by omega)).trans (fbase i)
  have output : w 88 = mask := (backWire _ (by decide)).trans bout
  have steps (j : Fin 63) : ∃ a b : Fin (26+j.val),
      w (26+j.val) = w a.val ∩ w b.val ∨ w (26+j.val) = w a.val ∪ w b.val := by
    by_cases h : j.val < 29
    · obtain ⟨a,b,r⟩ := fstep ⟨j.val,h⟩
      refine ⟨a,b,?_⟩
      rw [frontWire _ (by omega), frontWire a.val (by have := a.isLt; change a.val < 26+j.val at this; omega),
        frontWire b.val (by have := b.isLt; change b.val < 26+j.val at this; omega)]
      exact r
    · let k : Fin 34 := ⟨j.val-29,by omega⟩
      have hk : 55+k.val = 26+j.val := by dsimp [k]; omega
      obtain ⟨a,b,ha,hb,rule⟩ := bstep k
      refine ⟨⟨a.val, hk ▸ a.isLt⟩, ⟨b.val, hk ▸ b.isLt⟩, ?_⟩
      change w (26+j.val) = w a.val ∩ w b.val ∨ w (26+j.val) = w a.val ∪ w b.val
      rw [backWire _ (by omega), backWire _ ha, backWire _ hb, ← hk]
      exact rule

  have make (j : Fin 63) : ∃ g : Gate,
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧
      (∀ i ∈ g.inputs, i < 26+j.val) ∧
      ∀ x : Fin 26 → Bool, g.op.eval (g.inputs.map fun i => decide (x ∈ w i)) = decide (x ∈ w (26+j.val)) := by
    obtain ⟨a,b,h | h⟩ := steps j
    · refine ⟨⟨.and,[a.val,b.val]⟩,Or.inl rfl,rfl,?_,?_⟩
      · intro i hi
        rcases (show i = a.val ∨ i = b.val by simpa using hi) with rfl | rfl
        exact a.isLt
        exact b.isLt
      · intro x
        change (decide (x ∈ w a.val) && (decide (x ∈ w b.val) && true)) = _
        rw [h,Bool.and_true]
        by_cases ha : x ∈ w a.val <;> by_cases hb : x ∈ w b.val <;> simp [ha,hb]
    · refine ⟨⟨.or,[a.val,b.val]⟩,Or.inr rfl,rfl,?_,?_⟩
      · intro i hi
        rcases (show i = a.val ∨ i = b.val by simpa using hi) with rfl | rfl
        exact a.isLt
        exact b.isLt
      · intro x
        change (decide (x ∈ w a.val) || (decide (x ∈ w b.val) || false)) = _
        rw [h,Bool.or_false]
        by_cases ha : x ∈ w a.val <;> by_cases hb : x ∈ w b.val <;> simp [ha,hb]
  let g (j : Fin 63) : Gate := (make j).choose
  have spec (j : Fin 63) := (make j).choose_spec
  let C : Circuit := ⟨List.ofFn g,88⟩
  have gateEq (j : ℕ) (hj : j < C.gates.length) :
      C.gates[j] = g ⟨j,by simpa [C] using hj⟩ := List.getElem_ofFn hj
  have field (q : Gate) (hq : q ∈ C.gates) : (q.op = .and ∨ q.op = .or) ∧ q.inputs.length = 2 := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨(spec j).1,(spec j).2.1⟩
  have mono : Monotone2 C := by
    intro q hq
    exact ⟨(field q hq).1, (field q hq).2.le⟩
  let ev (xs : List Bool) (q : Gate) := xs ++ [q.op.eval (q.inputs.map fun i => xs.getD i false)]
  have run (gs : List Gate) (m : ℕ) (v : ℕ → Bool)
      (h : ∀ j (hj : j < gs.length), (∀ i ∈ gs[j].inputs, i < m+j) ∧
        gs[j].op.eval (gs[j].inputs.map v) = v (m+j)) :
      gs.foldl ev ((List.range m).map v) = (List.range (m+gs.length)).map v := by
    induction gs generalizing m with
    | nil => simp
    | cons q gs ih =>
      have head := h 0 (by simp)
      change (∀ i ∈ q.inputs, i < m+0) ∧ q.op.eval (q.inputs.map v) = v (m+0) at head
      simp only [Nat.add_zero] at head
      have vals : q.inputs.map (fun i => ((List.range m).map v).getD i false) = q.inputs.map v := by
        refine List.map_congr_left fun i hi => ?_
        have bound := head.1 i hi
        rw [List.getD_eq_getElem _ _ (by simpa using bound)]
        simp
      have eq : ev ((List.range m).map v) q = (List.range (m+1)).map v := by
        simp only [ev, vals, head.2, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [List.foldl_cons,eq,ih (m+1)]
      · congr 2; simp; omega
      · intro j hj
        have a := h (j+1) (by simp [hj])
        simpa [Nat.add_assoc, Nat.add_comm 1] using a
  have replay (x : Fin 26 → Bool) : circuitFun 26 C x = decide (x ∈ mask) := by
    let v (i : ℕ) := decide (x ∈ w i)
    have init : List.ofFn x = (List.range 26).map v := by
      apply List.ext_getElem
      · simp
      · intro i hi _
        rw [List.getElem_ofFn]
        simp only [List.getElem_map,List.getElem_range]
        change x _ = decide (x ∈ w i)
        rw [base ⟨i,by simpa using hi⟩]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        rfl
    have rules (j : ℕ) (hj : j < C.gates.length) :
        (∀ i ∈ C.gates[j].inputs, i < 26+j) ∧ C.gates[j].op.eval (C.gates[j].inputs.map v) = v (26+j) := by
      rw [gateEq]
      exact ⟨(spec _).2.2.1,(spec _).2.2.2 x⟩
    change (C.gates.foldl ev (List.ofFn x)).getD 88 false = _
    rw [init,run _ _ _ rules,List.getD_eq_getElem _ _ (by simp [C])]
    simpa [v] using congrArg (fun S : Set (Fin 26 → Bool) => decide (x ∈ S)) output
  let rel (p l : Fin 13) := ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d
  have eqv : ∀ p l : Fin 13, rel p l ↔ I p l := by decide +kernel
  refine ⟨C,mono,?_,?_,?_,?_⟩
  · change (List.ofFn g).length ≤ 63
    simp
  · intro p l h
    rw [replay,decide_eq_true_eq]
    refine ⟨p,l,(eqv _ _).mp h,?_,?_⟩
    · exact (left {p} {l} p).trans (by simp)
    · exact (right {p} {l} l).trans (by simp)
  · intro P _
    rw [replay,decide_eq_false_iff_not]
    rintro ⟨p,l,h,px,ly⟩
    have hp : p ∈ P := by simpa only [Fin.append_left,decide_eq_true_eq] using px
    have ht := (right _ _ l).symm.trans ly
    have hl : ∀ z ∈ P, ¬rel z l := by simpa only [decide_eq_true_eq,Finset.mem_filter,Finset.mem_univ,true_and] using ht
    exact hl p hp ((eqv _ _).mpr h)
  · intro L _
    rw [replay,decide_eq_false_iff_not]
    rintro ⟨p,l,h,px,ly⟩
    have hl : l ∈ L := by simpa only [Fin.append_right,decide_eq_true_eq] using ly
    have ht := (left _ _ p).symm.trans px
    have hp : ∀ z ∈ L, ¬rel p z := by simpa only [decide_eq_true_eq,Finset.mem_filter,Finset.mem_univ,true_and] using ht
    exact hp l hl ((eqv _ _).mpr h)
