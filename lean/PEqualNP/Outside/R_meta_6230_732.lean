import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8500000 in
theorem PEqualNP.Outside.R_meta_6230_732
    (packBit : ∀ (xs : List Bool) (i : ℕ), (xs.foldr Nat.bit 0).testBit i = xs.getD i false)
    (simulate : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 : List ℕ) (x5 : ℕ),       have x6 : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x6 : List ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) =>         have x8 : ℕ := x6.getD (x7.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);         have x9 : ℕ := x6.getD (x7.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);         x6 ++ [if x7.op.eval [Bool.true, Bool.false] = Bool.true then x8 ||| x9 else x8 &&& x9];       ((List.foldl x6 x4 x2.gates).getD x2.output (0 : ℕ)).testBit x5 = x2.eval (List.map (fun (x7 : ℕ) => x7.testBit x5) x4))
    (tailBound :
      let V := List.range 13
      let adj := fun p l : ℕ => ([0,1,3,9] : List ℕ).contains ((p+13-l)%13)
      let mask := fun s : List ℕ => s.foldr (fun i w => 2^i ||| w) 0
      let row := fun a b : List ℕ => mask a ||| (mask b <<< 13)
      let positive := V.flatMap fun l => (V.filter fun p => adj p l).map fun p => row [p] [l]
      let negative := (List.range 4).flatMap fun k => (V.sublistsLen k).flatMap fun s =>
        [row s (V.filter fun l => s.all fun p => !adj p l),
          row (V.filter fun p => s.all fun l => !adj p l) s]
      let rows := positive.map (fun r => (r,true)) ++ negative.map (fun r => (r,false))
      let pack := fun (f : ℕ × Bool → Bool) => (rows.map f).foldr Nat.bit 0
      let bank := List.ofFn (fun v : Fin 26 => pack (fun r => r.1.testBit v.val))
      let step := fun (b : List ℕ) (g : Bool × ℕ × ℕ) =>
        let a := b.getD g.2.1 0
        let c := b.getD g.2.2 0
        b ++ [if g.1 then a ||| c else a &&& c]
      ∀ (h : Bool × ℕ × ℕ) (gs : List (Bool × ℕ × ℕ)),
        h ∈ ([(false,0,13),(true,0,1),(true,0,13),(true,0,14)] : List (Bool × ℕ × ℕ)) → gs.length ≤ 61 →
        (∀ i : Fin gs.length, let g := gs.getD i.val (false,0,0); g.2.1 ≠ g.2.2 ∧ max g.2.1 g.2.2 < 27+i.val) →
        (∀ a b : Fin 26, a ≠ b → ∃ g ∈ h :: gs,
          (g.2.1 = a.val ∨ g.2.2 = a.val) ∧ g.2.1 ≠ b.val ∧ g.2.2 ≠ b.val) →
        pack Prod.snd ∉ gs.foldl step (step bank h)) :
    have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ x1 x4; have x4 : PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (13 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∨ ∃ x5 ∈ [(1 : ℕ), (13 : ℕ), (14 : ℕ)], x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), x5] : PEqualNP.CircuitLowerBounds.Gate }; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → x3 x5 → (∀ (x8 : PEqualNP.CircuitLowerBounds.Gate), x5.gates.head? = Option.some x8 → x4 x8) → (∀ (x9 x10 : Fin (26 : ℕ)), x9 ≠ x10 → ∃ x12 ∈ x5.gates, ↑x9 ∈ x12.inputs ∧ ↑x10 ∉ x12.inputs) → (63 : ℕ) ≤ x5.size := by
  intro target valid computes first C synt semantic initial separates
  by_contra! small
  let V := List.range 13
  let adj := fun p l : ℕ => ([0,1,3,9] : List ℕ).contains ((p+13-l)%13)
  let mask := fun s : List ℕ => s.foldr (fun i w => 2^i ||| w) 0
  let row := fun a b : List ℕ => mask a ||| (mask b <<< 13)
  let positive := V.flatMap fun l => (V.filter fun p => adj p l).map fun p => row [p] [l]
  let negative := (List.range 4).flatMap fun k => (V.sublistsLen k).flatMap fun s =>
    [row s (V.filter fun l => s.all fun p => !adj p l),
      row (V.filter fun p => s.all fun l => !adj p l) s]
  let rows := positive.map (fun r => (r,true)) ++ negative.map (fun r => (r,false))
  let pack := fun (f : ℕ × Bool → Bool) => (rows.map f).foldr Nat.bit 0
  let bank := List.ofFn (fun v : Fin 26 => pack (fun r => r.1.testBit v.val))
  let step := fun (b : List ℕ) (g : Bool × ℕ × ℕ) =>
    let a := b.getD g.2.1 0
    let c := b.getD g.2.2 0
    b ++ [if g.1 then a ||| c else a &&& c]
  let encode (g : Gate) := (g.op.eval [true,false],g.inputs.getD 0 0,g.inputs.getD 1 0)
  have gateRep (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨.or,[]⟩ = C.gates[j]
    exact List.getD_eq_getElem _ _ hj
  have shape (j : ℕ) (hj : j < C.gates.length) :=
    synt j C.gates[j] (List.getElem?_eq_getElem hj)
  have model : IsAO2 26 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
      exact (shape j hj).1
    · intro j hj w hw
      obtain ⟨a,b,ins,_,ha,hb⟩ := (shape j hj).2
      rw [gateRep j hj,ins] at hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      exact hw.elim (· ▸ ha) (· ▸ hb)
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨a,b,ins,_,_,_⟩ := (shape j hj).2
      simp only [ins,List.length_cons,List.length_nil]
  have nonempty : C.gates ≠ [] := by
    obtain ⟨g,hg,_,_⟩ := separates (0 : Fin 26) 1 (by decide)
    intro zero
    rw [zero] at hg
    exact List.not_mem_nil hg
  let input (r : ℕ) (v : Fin 26) := r.testBit v.val
  have posOK : positive.all (fun r => decide (target (input r))) = true := by decide +kernel
  have maskBit (s : List ℕ) (j : ℕ) : (mask s).testBit j = true ↔ j ∈ s := by
    induction s with
    | nil => simp [mask]
    | cons a s ih =>
      change ((2^a) ||| (mask s)).testBit j = true ↔ j ∈ a :: s
      rw [Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,List.mem_cons,ih]
      exact or_congr eq_comm Iff.rfl
  have inc (p l : Fin 13) : adj p.val l.val = true ↔
      (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) := by
    have h : ∀ p l : Fin 13, adj p.val l.val = true ↔
      (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) := by decide +kernel
    exact h p l
  have badRow (a b : List ℕ) (al : ∀ p ∈ a, p < 13)
      (no : ∀ p ∈ a, ∀ l ∈ b, adj p l = false) : ¬target (input (row a b)) := by
    rintro ⟨p,l,hex,hp,hl⟩
    change (mask a ||| (mask b <<< 13)).testBit p.val = true at hp
    change (mask a ||| (mask b <<< 13)).testBit (13+l.val) = true at hl
    have below : decide (p.val ≥ 13) = false := decide_eq_false (Nat.not_le_of_gt p.isLt)
    have above : decide (13+l.val ≥ 13) = true := decide_eq_true (by omega)
    have clear : (mask a).testBit (13+l.val) = false := by
      apply Bool.eq_false_iff.mpr
      intro yes
      have z := al _ ((maskBit a _).1 yes)
      omega
    rw [Nat.testBit_or,Nat.testBit_shiftLeft,below,Bool.false_and,Bool.or_false] at hp
    rw [Nat.testBit_or,Nat.testBit_shiftLeft,clear,above,Bool.true_and,Bool.false_or,
      show 13+l.val-13 = l.val by omega] at hl
    exact Bool.false_ne_true ((no p.val ((maskBit a _).1 hp) l.val ((maskBit b _).1 hl)).symm.trans
      ((inc p l).2 hex))
  have negOK (m : ℕ) (hm : m ∈ negative) : ¬target (input m) := by
    obtain ⟨k,_,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨s,hs,hm⟩ := List.mem_flatMap.mp hm
    have subset : List.Sublist s V := (List.mem_sublistsLen.mp hs).1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · apply badRow _ _ (fun p hp => List.mem_range.mp (subset.subset hp))
      intro p hp l hl
      have h := List.all_eq_true.mp (List.mem_filter.mp hl).2 p hp
      cases e : adj p l <;> simp [e] at h ⊢
    · apply badRow _ _ (fun p hp => List.mem_range.mp (List.mem_filter.mp hp).1)
      intro p hp l hl
      have h := List.all_eq_true.mp (List.mem_filter.mp hp).2 l hl
      cases e : adj p l <;> simp [e] at h ⊢
  have allRows (r : ℕ × Bool) (member : r ∈ rows) : C.eval (List.ofFn (input r.1)) = r.2 := by
    change r ∈ positive.map (fun m => (m,true)) ++ negative.map (fun m => (m,false)) at member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨m,hm,rfl⟩ := List.mem_map.mp member
      exact (semantic _).2 (of_decide_eq_true (List.all_eq_true.mp posOK m hm))
    · obtain ⟨m,hm,rfl⟩ := List.mem_map.mp member
      apply Bool.eq_false_iff.mpr
      exact fun yes => (negOK m hm) ((semantic _).1 yes)
  have outOfRange : C.eval (List.ofFn (input 0)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨p,l,_,hp,_⟩ := (semantic _).1 h
    change Nat.testBit 0 _ = true at hp
    rw [Nat.zero_testBit] at hp
    contradiction
  have bankBits (i : ℕ) : bank.map (fun col => col.testBit i) =
      List.ofFn (input (rows.getD i (0,false)).1) := by
    change (List.ofFn fun v : Fin 26 => pack (fun r => input r.1 v)).map (fun c => c.testBit i) = _
    rw [List.map_ofFn]
    congr 1
    funext v
    change ((rows.map (fun r => input r.1 v)).foldr Nat.bit 0).testBit i =
      input (rows.getD i (0,false)).1 v
    rw [packBit]
    simpa [input] using List.getD_map (n := i) rows (0,false) (fun r => input r.1 v)
  have correctOutput :
      ((C.gates.map encode).foldl step bank).getD C.output 0 = pack Prod.snd := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [List.foldl_map]
    have sim := simulate 26 C model bank i
    change ((C.gates.foldl (fun b g => step b (encode g)) bank).getD C.output 0).testBit i =
      C.eval (bank.map fun c => c.testBit i) at sim
    rw [sim,bankBits]
    change C.eval (List.ofFn (input (rows.getD i (0,false)).1)) =
      ((rows.map Prod.snd).foldr Nat.bit 0).testBit i
    rw [packBit]
    have getLabel := List.getD_map (n := i) rows (0,false) (Prod.snd : ℕ × Bool → Bool)
    change (rows.map Prod.snd).getD i false = (rows.getD i (0,false)).2 at getLabel
    rw [getLabel]
    by_cases hi : i < rows.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact allRows _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      exact outOfRange
  have maskNonzero : pack Prod.snd ≠ 0 := by decide +kernel
  have packedMember : pack Prod.snd ∈ (C.gates.map encode).foldl step bank := by
    let values := (C.gates.map encode).foldl step bank
    change values.getD C.output 0 = pack Prod.snd at correctOutput
    by_cases validOutput : C.output < values.length
    · rw [List.getD_eq_getElem _ _ validOutput] at correctOutput
      rw [← correctOutput]
      exact List.getElem_mem validOutput
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt validOutput)] at correctOutput
      exact (maskNonzero correctOutput.symm).elim
  cases data : C.gates with
  | nil => exact (nonempty data).elim
  | cons g tail =>
    have hFirst : first g := initial g (by rw [data]; rfl)
    have initialMask : encode g ∈ ([(false,0,13),(true,0,1),(true,0,13),(true,0,14)] : List (Bool × ℕ × ℕ)) := by
      change g = ⟨.and,[0,13]⟩ ∨ ∃ j ∈ ([1,13,14] : List ℕ), g = ⟨.or,[0,j]⟩ at hFirst
      rcases hFirst with rfl | ⟨j,hj,rfl⟩
      · decide
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        rcases hj with rfl | rfl | rfl <;> decide
    have sizeTail : (tail.map encode).length ≤ 61 := by
      change C.gates.length < 63 at small
      rw [data,List.length_cons] at small
      rw [List.length_map]
      omega
    have syntaxEncoded (i : Fin (tail.map encode).length) :
        let w := (tail.map encode).getD i.val (false,0,0); w.2.1 ≠ w.2.2 ∧ max w.2.1 w.2.2 < 27+i.val := by
      rw [List.getD_eq_getElem _ _ i.isLt]
      have inTail : i.val < tail.length := by simpa using i.isLt
      have inC : i.val+1 < C.gates.length := by rw [data,List.length_cons]; omega
      have getMapped : C.gates[i.val+1] = tail[i.val] := by
        have h : C.gates[i.val+1]? = some tail[i.val] := by
          rw [data,List.getElem?_cons_succ,List.getElem?_eq_getElem inTail]
        rw [List.getElem?_eq_getElem inC] at h
        exact Option.some.inj h
      obtain ⟨a,b,ins,distinct,ha,hb⟩ := (shape (i.val+1) inC).2
      rw [getMapped] at ins
      simp only [List.getElem_map]
      change (tail[i.val].inputs.getD 0 0) ≠ (tail[i.val].inputs.getD 1 0) ∧
        max (tail[i.val].inputs.getD 0 0) (tail[i.val].inputs.getD 1 0) < 27+i.val
      rw [ins]
      change a ≠ b ∧ max a b < 27+i.val
      exact ⟨distinct,max_lt_iff.mpr ⟨by omega,by omega⟩⟩
    have separatesEncoded (a b : Fin 26) (hab : a ≠ b) :
        ∃ w ∈ encode g :: tail.map encode,
          (w.2.1 = a.val ∨ w.2.2 = a.val) ∧ w.2.1 ≠ b.val ∧ w.2.2 ≠ b.val := by
      obtain ⟨u,hu,ua,ub⟩ := separates a b hab
      obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hu
      have uForm := (shape j hj).2
      rw [eq] at uForm
      obtain ⟨m,n,ins,_,_,_⟩ := uForm
      have mapped : encode u ∈ C.gates.map encode := List.mem_map.mpr ⟨u,hu,rfl⟩
      rw [data,List.map_cons] at mapped
      refine ⟨encode u,mapped,?_⟩
      simp only [ins,List.mem_cons,List.not_mem_nil,or_false,not_or] at ua ub
      change ((u.inputs.getD 0 0) = a.val ∨ (u.inputs.getD 1 0) = a.val) ∧
        (u.inputs.getD 0 0) ≠ b.val ∧ (u.inputs.getD 1 0) ≠ b.val
      rw [ins]
      exact ⟨ua.imp Eq.symm Eq.symm,Ne.symm ub.1,Ne.symm ub.2⟩
    rw [data,List.map_cons,List.foldl_cons] at packedMember
    exact (tailBound (encode g) (tail.map encode) initialMask sizeTail syntaxEncoded separatesEncoded) packedMember
