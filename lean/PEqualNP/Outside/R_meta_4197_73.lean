import PEqualNP.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A maximal independent input is determined by its closed point support.
-- Every closed support is reached by adjoining points one at a time and closing.
-- The first hypothesis asks for 357 finite transitions among 17 representatives.
-- The second asks for a circuit on the eighty flags outside the pencil through zero.
-- We explicitly restore the five omitted lines using thirty binary gates.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4197_73
    (hTransitions :
      let E (p l : Fin 21) := p=l ∨ p=l+1 ∨ p=l+4 ∨ p=l+14 ∨ p=l+16
      let close (s : Finset (Fin 21)) := Finset.univ.filter (fun p => ∀ l, (∀ i ∈ s, ¬ E i l) → ¬ E p l)
      let decode (r : Nat) := Finset.univ.filter (fun p : Fin 21 => r.testBit p.val)
      let reps : List Nat := [0,1,3,19,7,389,23,15,31,95,1369,1371,6799,5501,54781,503803,2097151]
      ∀ r ∈ reps, ∀ p : Fin 21, ∃ u ∈ reps, ∃ e f : Equiv.Perm (Fin 21),
        (∀ i l, E (e i) (f l) ↔ E i l) ∧ close (insert p (decode r)) = (decode u).map e.toEmbedding)
    (hAffine :
      let E (p l : Fin 21) := p=l ∨ p=l+1 ∨ p=l+4 ∨ p=l+14 ∨ p=l+16
      let Z (y : Fin 21 → Bool) (l : Fin 21) := !(y l || y (l+1) || y (l+4) || y (l+14) || y (l+16))
      let reps : List Nat := [0,1,3,19,7,389,23,15,31,95,1369,1371,6799,5501,54781,503803,2097151]
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 94 ∧
        (∀ p l, E p l → ¬E 0 l → C.eval (List.ofFn (fun k : Fin (21+21) => Fin.addCases (motive := fun _ => Bool)
            (fun i : Fin 21 => decide (i=p)) (fun i : Fin 21 => decide (i=l)) k)) = true) ∧
        ∀ r ∈ reps, ∀ e : Equiv.Perm (Fin 21), (∀ l, ∃ j, ∀ p, E (e p) j ↔ E p l) →
          let y : Fin 21 → Bool := fun p => Nat.testBit r (e.symm p).val
          C.eval (List.ofFn (fun k : Fin (21+21) => Fin.addCases (motive := fun _ => Bool) y (Z y) k)) = false) :
  have x1 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x1 x2 : Fin (21 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (21 : ℕ)) ∨ x1 = x2 + (4 : Fin (21 : ℕ)) ∨ x1 = x2 + (14 : Fin (21 : ℕ)) ∨ x1 = x2 + (16 : Fin (21 : ℕ)); have x2 : (Fin (21 : ℕ) → Bool) → Fin (21 : ℕ) → Bool := fun (x2 : Fin (21 : ℕ) → Bool) (x3 : Fin (21 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (21 : ℕ))) || x2 (x3 + (4 : Fin (21 : ℕ))) || x2 (x3 + (14 : Fin (21 : ℕ))) || x2 (x3 + (16 : Fin (21 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ (124 : ℕ) ∧ (∀ (x4 x5 : Fin (21 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((21 : ℕ) + (21 : ℕ))) => Fin.addCases (fun (x8 : Fin (21 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (21 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧ ∀ (x4 : Fin (21 : ℕ) → Bool), (∀ (x5 : Fin (21 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (21 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((21 : ℕ) + (21 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false := by
  have hOrbit :
      let E (p l : Fin 21) := p=l ∨ p=l+1 ∨ p=l+4 ∨ p=l+14 ∨ p=l+16
      let Z (y : Fin 21 → Bool) (l : Fin 21) := !(y l || y (l+1) || y (l+4) || y (l+14) || y (l+16))
      let reps : List Nat := [0,1,3,19,7,389,23,15,31,95,1369,1371,6799,5501,54781,503803,2097151]
      ∀ y : Fin 21 → Bool, (∀ p, y p=false → ∃ l, E p l ∧ Z y l=true) →
        ∃ r ∈ reps, ∃ e : Equiv.Perm (Fin 21), (∀ l, ∃ j, ∀ p, E (e p) j ↔ E p l) ∧
          ∀ p, y (e p) = Nat.testBit r p.val := by
    clear hAffine
    let I (p l : (Fin 21)) : Prop := p = l ∨ p = l+1 ∨ p = l+4 ∨ p = l+14 ∨ p = l+16

    let Clear (s : Finset (Fin 21)) (l : (Fin 21)) : Prop := ∀ p ∈ s, ¬ I p l

    let cl (s : Finset (Fin 21)) : Finset (Fin 21) :=
      Finset.univ.filter (fun p => ∀ l, Clear s l → ¬ I p l)

    have mem_cl {s : Finset (Fin 21)} {p : (Fin 21)} : p ∈ cl s ↔ ∀ l, Clear s l → ¬ I p l := by
      simp only [cl,Finset.mem_filter,Finset.mem_univ,true_and]

    have subset_cl (s : Finset (Fin 21)) : s ⊆ cl s :=
      fun p hp => mem_cl.mpr (fun _ hl => hl p hp)

    have clear_cl (s : Finset (Fin 21)) (l : (Fin 21)) : Clear (cl s) l ↔ Clear s l :=
      ⟨fun h p hp => h p (subset_cl s hp), fun h _ hp => mem_cl.mp hp l h⟩

    have clear_ins (s : Finset (Fin 21)) (p l : (Fin 21)) :
        Clear (insert p s) l ↔ ¬I p l ∧ Clear s l := by
      simp only [Clear, Finset.mem_insert, forall_eq_or_imp]

    have cl_insert (s : Finset (Fin 21)) (p : (Fin 21)) :
        cl (insert p (cl s)) = cl (insert p s) := by
      ext x
      simp only [mem_cl,clear_ins,clear_cl]

    let Aut (e f : Equiv.Perm (Fin 21)) : Prop := ∀ p l, I (e p) (f l) ↔ I p l

    have aut_id : Aut (Equiv.refl (Fin 21)) (Equiv.refl (Fin 21)) := fun _ _ => Iff.rfl

    have aut_trans {e f e' f' : Equiv.Perm (Fin 21)} (a : Aut e f) (b : Aut e' f') :
        Aut (e.trans e') (f.trans f') := fun p l => (b (e p) (f l)).trans (a p l)

    have clear_map {e f : Equiv.Perm (Fin 21)} (a : Aut e f) (s : Finset (Fin 21)) (l : (Fin 21)) :
        Clear (s.map e.toEmbedding) (f l) ↔ Clear s l := by
      constructor
      · intro h p hp ip
        exact h (e p) (Finset.mem_map.mpr ⟨p,hp,rfl⟩) ((a p l).mpr ip)
      · intro h q hq iq
        obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hq
        exact h _ hp ((a p l).mp iq)

    have cl_map {e f : Equiv.Perm (Fin 21)} (a : Aut e f) (s : Finset (Fin 21)) :
        cl (s.map e.toEmbedding) = (cl s).map e.toEmbedding := by
      ext q
      obtain ⟨p,rfl⟩ := e.surjective q
      rw [mem_cl]
      have hm : e p ∈ (cl s).map e.toEmbedding ↔ p ∈ cl s := by
        constructor
        · intro h
          obtain ⟨p',hp,eq⟩ := Finset.mem_map.mp h
          exact (e.injective eq) ▸ hp
        · intro h
          exact Finset.mem_map.mpr ⟨p,h,rfl⟩
      rw [hm,mem_cl]
      constructor
      · intro h l hl ip
        exact h (f l) ((clear_map a s l).mpr hl) ((a p l).mpr ip)
      · intro h l hl ip
        obtain ⟨j,rfl⟩ := f.surjective l
        exact h j ((clear_map a s j).mp hl) ((a p j).mp ip)

    let Orb (s t : Finset (Fin 21)) : Prop :=
      ∃ e f : Equiv.Perm (Fin 21), Aut e f ∧ t = s.map e.toEmbedding

    have orb_refl (s : Finset (Fin 21)) : Orb s s := by
      refine ⟨Equiv.refl _,Equiv.refl _,aut_id,?_⟩
      simp

    have orb_trans {a b c : Finset (Fin 21)} (h₁ : Orb a b) (h₂ : Orb b c) : Orb a c := by
      obtain ⟨e,f,he,rfl⟩ := h₁
      obtain ⟨g,h,hg,rfl⟩ := h₂
      exact ⟨e.trans g,f.trans h,aut_trans he hg,Finset.map_map _ _ _⟩

    let decode (r : Nat) : Finset (Fin 21) := Finset.univ.filter (fun p => r.testBit p.val)

    let seeds : List Nat := [0,1,3,19,7,389,23,15,31,95,1369,1371,6799,5501,54781,503803,2097151]

    have generate
        (start : Orb (decode 0) (cl ∅))
        (step : ∀ r ∈ seeds, ∀ p : (Fin 21), ∃ r' ∈ seeds, Orb (decode r') (cl (insert p (decode r)))) :
        ∀ s : Finset (Fin 21), ∃ r ∈ seeds, Orb (decode r) (cl s) := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨0,by decide,start⟩
      | @insert p s _ ih =>
        obtain ⟨r,hr,e,f,he,hs⟩ := ih
        obtain ⟨j,hj,hstep⟩ := step r hr (e.symm p)
        refine ⟨j,hj,orb_trans hstep ⟨e,f,he,?_⟩⟩
        rw [←cl_map he, Finset.map_insert, ←hs, ←cl_insert s p]
        simp

    have orbit_generation (s : Finset (Fin 21)) : ∃ r ∈ seeds, Orb (decode r) (cl s) := by
      refine generate ?_ hTransitions s
      have eq : cl ∅ = decode 0 := by decide +kernel
      rw [eq]
      exact orb_refl _

    let safeLines (y : (Fin 21) → Bool) (l : (Fin 21)) : Bool :=
      !(y l || y (l+1) || y (l+4) || y (l+14) || y (l+16))

    let support (y : (Fin 21) → Bool) : Finset (Fin 21) := Finset.univ.filter fun p => y p = true

    have mem_support {y : (Fin 21) → Bool} {p : (Fin 21)} : p ∈ support y ↔ y p = true := by
      simp [support]

    have safe_iff (y : (Fin 21) → Bool) (l : (Fin 21)) : safeLines y l = true ↔ Clear (support y) l := by
      simp only [safeLines,Bool.not_eq_true',Bool.or_eq_false_iff]
      constructor
      · rintro ⟨⟨⟨⟨h₀,h₁⟩,h₄⟩,h₁₄⟩,h₁₆⟩ p hp hi
        have hy := mem_support.mp hp
        rcases hi with rfl | rfl | rfl | rfl | rfl
        · exact (by decide : (true : Bool) ≠ false) (hy.symm.trans h₀)
        · exact (by decide : (true : Bool) ≠ false) (hy.symm.trans h₁)
        · exact (by decide : (true : Bool) ≠ false) (hy.symm.trans h₄)
        · exact (by decide : (true : Bool) ≠ false) (hy.symm.trans h₁₄)
        · exact (by decide : (true : Bool) ≠ false) (hy.symm.trans h₁₆)
      · intro h
        have at_point (p : (Fin 21)) (ip : I p l) : y p = false := by
          apply Bool.eq_false_iff.mpr
          exact fun hy => h p (mem_support.mpr hy) ip
        exact ⟨⟨⟨⟨at_point l (Or.inl rfl),at_point _ (Or.inr (Or.inl rfl))⟩,
          at_point _ (Or.inr (Or.inr (Or.inl rfl)))⟩,at_point _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩,
          at_point _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩

    have support_closed (y : (Fin 21) → Bool)
        (maximal : ∀ p, y p = false → ∃ l, I p l ∧ safeLines y l = true) :
        cl (support y) = support y := by
      apply Finset.Subset.antisymm _ (subset_cl _)
      intro p hp
      by_contra absent
      have hy : y p = false := Bool.eq_false_iff.mpr fun h => absent (mem_support.mpr h)
      obtain ⟨l,ip,empty⟩ := maximal p hy
      exact mem_cl.mp hp l ((safe_iff y l).mp empty) ip

    have classifies (y : (Fin 21) → Bool)
        (maximal : ∀ p, y p = false → ∃ l, I p l ∧ safeLines y l = true) :
        ∃ r ∈ seeds, ∃ e : Equiv.Perm (Fin 21),
          (∀ l, ∃ j, ∀ p, I (e p) j ↔ I p l) ∧ ∀ p, y (e p) = r.testBit p.val := by
      obtain ⟨r,hr,e,f,h,eq⟩ := orbit_generation (support y)
      rw [support_closed y maximal] at eq
      refine ⟨r,hr,e,fun l => ⟨f l,fun p => h p l⟩,?_⟩
      intro p
      have ff : e p ∈ support y ↔ p ∈ decode r := by
        rw [eq]
        constructor
        · intro hp
          obtain ⟨q,hq,he⟩ := Finset.mem_map.mp hp
          exact (e.injective he) ▸ hq
        · intro hp
          exact Finset.mem_map.mpr ⟨p,hp,rfl⟩
      have b : y (e p) = true ↔ r.testBit p.val = true := by simpa [mem_support,decode] using ff
      exact Bool.eq_iff_iff.mpr b
    exact classifies

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map (fun k => w.getD k false))]

  have wireTail (gs : List Gate) (w : List Bool) :
      ∃ t : List Bool, gs.foldl step w = w++t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp,by simp⟩
    | cons g gs ih =>
      obtain ⟨t,ht,hn⟩ := ih (step w g)
      exact ⟨_,by simpa [step,List.append_assoc] using ht,by simpa using hn⟩

  have sizeW (C : Circuit) (w : List Bool) : (C.wires w).length = w.length + C.size := by
    obtain ⟨t,h,ht⟩ := wireTail C.gates w
    change (C.gates.foldl step w).length=w.length+C.gates.length
    simp [h,ht]

  have raw (C : Circuit) (w : List Bool) (i : Nat) (h : i<w.length) :
      (C.wires w).getD i false = w.getD i false := by
    obtain ⟨t,eq,_⟩ := wireTail C.gates w
    change (C.gates.foldl step w).getD _ _=_
    rw [eq,List.getD_append _ _ _ _ h]

  have catRead (w a : List Bool) (i : Nat) :
      (w++a).getD i false = if i<w.length then w.getD i false else a.getD (i-w.length) false := by
    split
    next h => exact List.getD_append _ _ _ _ h
    next h => simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_of_not_gt h)]

  let pair (op : GateOp) (i j : Nat) : Gate := ⟨op,[i,j]⟩

  let ops (n last : Nat) (l : (Fin 21)) : List Gate :=
    [pair .or l.val (l+1).val, pair .or n (l+4).val, pair .or (n+1) (l+14).val,
      pair .or (n+2) (l+16).val, pair .and (n+3) (21+l.val), pair .or last (n+4)]

  let bump (C : Circuit) (l : (Fin 21)) : Circuit :=
    ⟨C.gates ++ ops (42+C.size) C.output l,42+C.size+5⟩

  have bump_size (C : Circuit) (l : (Fin 21)) : (bump C l).size = C.size+6 := by
    change (C.gates ++ ops (42+C.size) C.output l).length = C.gates.length+6
    simp [ops]

  have bump_out (C : Circuit) (l : (Fin 21)) : (bump C l).output < 42+(bump C l).size := by
    rw [bump_size]
    change 42+C.size+5 < 42+(C.size+6)
    omega

  have bump_mon (C : Circuit) (l : (Fin 21)) (h : Monotone2 C) : Monotone2 (bump C l) := by
    intro g hg
    change g ∈ C.gates ++ ops _ _ _ at hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact h g hg
    · simp only [ops,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pair]

  let term (w : List Bool) (l : (Fin 21)) : Bool :=
    (w.getD l.val false || w.getD (l+1).val false || w.getD (l+4).val false ||
     w.getD (l+14).val false || w.getD (l+16).val false) && w.getD (21+l.val) false

  have row_eval (w : List Bool) (last : Nat) (l : (Fin 21)) (big : 42≤w.length) (valid : last<w.length) :
      ((ops w.length last l).foldl step w).getD (w.length+5) false =
        (w.getD last false || term w l) := by
    have pt (i : (Fin 21)) : i.val < w.length := by have hi := i.isLt; omega
    have ln : 21+l.val < w.length := by have hi := l.isLt; omega
    have or_eval (a b : Bool) : GateOp.eval .or [a,b] = (a || b) := by
      change (a || (b || false)) = (a || b)
      simp
    have and_eval (a b : Bool) : GateOp.eval .and [a,b] = (a && b) := by
      change (a && (b && true)) = (a && b)
      simp
    simp only [ops,List.foldl_cons,List.foldl_nil,step,pair,List.map_cons,List.map_nil,
      or_eval,and_eval,
      List.append_assoc,List.cons_append,List.nil_append,term]
    have never (j : Nat) : ¬w.length+j < w.length := by omega
    simp only [catRead,pt,ln,valid,ite_true,Nat.lt_irrefl,ite_false,never,
      Nat.add_sub_cancel_left,Nat.sub_self]
    rfl

  have bump_eval (C : Circuit) (l : (Fin 21)) (xs : List Bool) (hlen : xs.length=42)
      (valid : C.output<42+C.size) :
      (bump C l).eval xs = (C.eval xs || term xs l) := by
    have len : (C.wires xs).length = 42+C.size := by rw [sizeW,hlen]
    have hv : C.output < (C.wires xs).length := by omega
    have h := row_eval (C.wires xs) C.output l (by omega) hv
    rw [len] at h
    change ((C.gates ++ ops (42+C.size) C.output l).foldl step xs).getD (42+C.size+5) false=_
    rw [List.foldl_append]
    change ((ops (42+C.size) C.output l).foldl step (C.wires xs)).getD (42+C.size+5) false=_
    rw [h]
    have r (i : (Fin 21)) : (C.wires xs).getD i.val false = xs.getD i.val false := raw C xs _ (by rw [hlen]; have hi := i.isLt; omega)
    have t : (C.wires xs).getD (21+l.val) false = xs.getD (21+l.val) false := raw C xs _ (by rw [hlen]; have hi := l.isLt; omega)
    change ((C.wires xs).getD C.output false || term (C.wires xs) l) =
      ((C.wires xs).getD C.output false || term xs l)
    simp only [term,r,t]

  let input (x y : (Fin 21) → Bool) : List Bool :=
    List.ofFn (Fin.addCases (motive := fun _ => Bool) x y)

  have input_len (x y : (Fin 21) → Bool) : (input x y).length=42 := by simp [input]

  have baseRead {n : Nat} (f : Fin n → Bool) (i : Fin n) :
      (List.ofFn f).getD i.val false = f i := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),List.getElem_ofFn]

  have input_point (x y : (Fin 21) → Bool) (i : (Fin 21)) : (input x y).getD i.val false = x i := by
    have h := baseRead (Fin.addCases (motive := fun _ => Bool) x y) (Fin.castAdd 21 i)
    exact h.trans (Fin.addCases_left i)

  have input_line (x y : (Fin 21) → Bool) (i : (Fin 21)) : (input x y).getD (21+i.val) false = y i := by
    have h := baseRead (Fin.addCases (motive := fun _ => Bool) x y) (Fin.natAdd 21 i)
    exact h.trans (Fin.addCases_right i)

  have term_input (x y : (Fin 21) → Bool) (l : (Fin 21)) :
      term (input x y) l = ((x l || x (l+1) || x (l+4) || x (l+14) || x (l+16)) && y l) := by
    simp only [term,input_point,input_line]

  have fold_size (ls : List (Fin 21)) (C : Circuit) :
      (ls.foldl bump C).size=C.size+6*ls.length := by
    induction ls generalizing C with
    | nil => simp
    | cons l ls ih =>
      simp only [List.foldl_cons,ih,bump_size,List.length_cons]
      omega

  have fold_valid (ls : List (Fin 21)) (C : Circuit) (h : Monotone2 C) :
      Monotone2 (ls.foldl bump C) := by
    induction ls generalizing C with
    | nil => exact h
    | cons l ls ih => exact ih _ (bump_mon _ _ h)

  have fold_value (ls : List (Fin 21)) (C : Circuit) (valid : C.output<42+C.size)
      (w : List Bool) (len : w.length=42) :
      (ls.foldl bump C).eval w = (C.eval w || ls.any (term w)) := by
    induction ls generalizing C with
    | nil => simp
    | cons l ls ih =>
      rw [List.foldl_cons,ih _ (bump_out _ _),bump_eval _ _ _ len valid]
      simp only [List.any_cons,Bool.or_assoc]

  let pencil : List (Fin 21) := [0,5,7,17,20]

  let incidence (p l : (Fin 21)) : Prop := p=l ∨ p=l+1 ∨ p=l+4 ∨ p=l+14 ∨ p=l+16

  have inPencil : ∀ l : (Fin 21), incidence 0 l ↔ l ∈ pencil := by decide +kernel

  have term_hit (p l : (Fin 21)) (e : incidence p l) :
      term (input (fun i => decide (i=p)) (fun i => decide (i=l))) l = true := by
    rw [term_input]
    rcases e with rfl | rfl | rfl | rfl | rfl <;> simp

  have term_miss (y : (Fin 21) → Bool) (l : (Fin 21)) :
      term (input y (fun k => !(y k || y (k+1) || y (k+4) || y (k+14) || y (k+16)))) l = false := by
    rw [term_input]
    exact Bool.and_not_self _

  obtain ⟨C,hmon,hsize,yes,no⟩ := hAffine
  have valid : C.output < 42+C.size := by
    let unit : Fin 21 → Bool := fun p => decide (p=1)
    have accepted : C.eval (input unit unit) = true := yes 1 1 (Or.inl rfl) (by decide)
    by_contra! bad
    have past : (C.wires (input unit unit)).length ≤ C.output := by
      rw [sizeW,input_len]
      exact bad
    have absent : C.eval (input unit unit)=false := List.getD_eq_default _ _ past
    simp [absent] at accepted
  refine ⟨pencil.foldl bump C,fold_valid _ _ hmon,?_,?_,?_⟩
  · rw [fold_size]
    change C.size+6*5 ≤ 124
    omega
  · intro p l edge
    let x : Fin 21 → Bool := fun i => decide (i=p)
    let y : Fin 21 → Bool := fun i => decide (i=l)
    change (pencil.foldl bump C).eval (input x y) = true
    rw [fold_value _ _ valid _ (input_len x y)]
    simp only [Bool.or_eq_true]
    by_cases center : incidence 0 l
    · exact Or.inr (List.any_eq_true.mpr ⟨l,(inPencil l).mp center,term_hit p l edge⟩)
    · exact Or.inl (yes p l edge center)
  · intro y closed
    let z : Fin 21 → Bool := fun l => !(y l || y (l+1) || y (l+4) || y (l+14) || y (l+16))
    obtain ⟨r,hr,e,he,values⟩ := hOrbit y closed
    have same : (fun p : Fin 21 => Nat.testBit r (e.symm p).val) = y := by
      funext p
      simpa using (values (e.symm p)).symm
    have clear : C.eval (input y z) = false := by
      change C.eval (input y (fun l => !(y l || y (l+1) || y (l+4) || y (l+14) || y (l+16)))) = false
      rw [←same]
      exact no r hr e he
    have all : pencil.any (term (input y z))=false := by
      apply List.any_eq_false.mpr
      intro l _
      exact Bool.eq_false_iff.mp (term_miss y l)
    change (pencil.foldl bump C).eval (input y z) = false
    rw [fold_value _ _ valid _ (input_len y z),clear,all]
    rfl
