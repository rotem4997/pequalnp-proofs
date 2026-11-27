import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxRecDepth 16000 in
set_option maxHeartbeats 7000000 in
theorem PEqualNP.Outside.R_meta_17136_731
    (packBit : ∀ (xs : List Bool) (i : ℕ), (xs.foldr Nat.bit 0).testBit i = xs.getD i false)
    (simulate : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 : List ℕ) (x5 : ℕ),       have x6 : List ℕ → PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x6 : List ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) =>         have x8 : ℕ := x6.getD (x7.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);         have x9 : ℕ := x6.getD (x7.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);         x6 ++ [if x7.op.eval [Bool.true, Bool.false] = Bool.true then x8 ||| x9 else x8 &&& x9];       ((List.foldl x6 x4 x2.gates).getD x2.output (0 : ℕ)).testBit x5 = x2.eval (List.map (fun (x7 : ℕ) => x7.testBit x5) x4))
    (rejection :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ v : Fin 11, v.val < 4 →
        let rows := (List.range 2048).filter fun r => !r.testBit v.val
        let pack := fun f : ℕ → Bool => (rows.map f).foldr Nat.bit 0
        let bank := List.ofFn fun i : Fin 11 => pack (fun r => r.testBit i.val)
        let target := pack fun r => graphFun G ∅ (fun i => r.testBit i.val)
        let mask := 2^rows.length-1
        let meet := fun (bank part : List ℕ) =>
          part.foldr (fun i a => (0::bank).getD i 0 &&& a) mask
        let merge := fun (bank : List ℕ) (pair : List ℕ × List ℕ) =>
          bank ++ [meet bank pair.1 ||| meet bank pair.2]
        ∀ (merges : List (List ℕ × List ℕ)) (last : List ℕ),
          merges.length ≤ 12 → meet (merges.foldl merge bank) last ≠ target) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (13 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x3.gates := by
  intro G v C hv ao agree
  -- An old wire is the intersection of input columns and earlier OR values.
  -- The zero slot gives a fixed representative for a missing wire.
  have compress :
      ∀ (mask : ℕ) (bank : List ℕ) (gates : List (Bool × ℕ × ℕ)) (out : ℕ),
        let step := fun (b : List ℕ) (g : Bool × ℕ × ℕ) =>
    let a := b.getD g.2.1 0
    let c := b.getD g.2.2 0
    b ++ [if g.1 then a ||| c else a &&& c]
        let meet := fun (bank part : List ℕ) =>
          part.foldr (fun i a => (0::bank).getD i 0 &&& a) mask
        let merge := fun (bank : List ℕ) (pair : List ℕ × List ℕ) =>
          bank ++ [meet bank pair.1 ||| meet bank pair.2]
        (∀ c ∈ bank, c &&& mask = c) →
        ∃ (merges : List (List ℕ × List ℕ)) (last : List ℕ),
          merges.length ≤ gates.countP Prod.fst ∧
          meet (merges.foldl merge bank) last = (gates.foldl step bank).getD out 0 := by
    intro mask bank gates out step meet merge initMask
    have ground (w : List ℕ) : meet w [0] = 0 := Nat.zero_and _
    have bounded (w part : List ℕ) : meet w part &&& mask = meet w part := by
      induction part with
      | nil => exact Nat.and_self _
      | cons a tail ih =>
        change ((0::w).getD a 0 &&& meet w tail) &&& mask = _
        rw [Nat.and_assoc,ih]
        rfl
    have combine (w a b : List ℕ) : meet w (a++b) = meet w a &&& meet w b := by
      induction a with
      | nil =>
        change meet w b = mask &&& meet w b
        rw [Nat.and_comm,bounded]
      | cons i next ih =>
        change (0::w).getD i 0 &&& meet w (next ++ b) =
          ((0::w).getD i 0 &&& meet w next) &&& meet w b
        rw [ih,Nat.and_assoc]
    have stable (w s : List ℕ) (new : ℕ) (h : ∀ j ∈ s, j ≤ w.length) :
        meet (w ++ [new]) s = meet w s := by
      induction s with
      | nil => rfl
      | cons i tail ih =>
        have ok : i < (0::w).length := by
          have := h i (by simp)
          simp only [List.length_cons]
          omega
        change ((0::w) ++ [new]).getD i 0 &&& meet (w ++ [new]) tail =
          (0::w).getD i 0 &&& meet w tail
        rw [List.getD_append _ _ _ _ ok]
        rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    have getPart (reps : List (List ℕ)) (w : List ℕ) (j : ℕ)
        (well : ∀ s ∈ reps, ∀ t ∈ s, t ≤ w.length) :
        ∀ t ∈ reps.getD j [0], t ≤ w.length := by
      by_cases inRange : j < reps.length
      · rw [List.getD_eq_getElem _ _ inRange]
        exact well _ (List.getElem_mem inRange)
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt inRange)]
        intro t ht
        simpa using (show t = 0 from by simpa using ht) ▸ Nat.zero_le w.length
    have getSound (reps : List (List ℕ)) (w : List ℕ) (j : ℕ) :
        meet w (reps.getD j [0]) = (reps.map (meet w)).getD j 0 := by
      have h := List.getD_map (n := j) reps [0] (meet w)
      rw [ground] at h
      exact h.symm
    have synth (gs : List (Bool × ℕ × ℕ)) :
        ∃ (ops : List (List ℕ × List ℕ)) (reps : List (List ℕ)),
          let w := ops.foldl merge bank
          ops.length ≤ gs.countP Prod.fst ∧
          reps.map (meet w) = gs.foldl step bank ∧
          (∀ s ∈ reps, ∀ i ∈ s, i ≤ w.length) ∧
          ∀ c ∈ w, c &&& mask = c := by
      induction gs using List.reverseRecOn with
      | nil =>
        let reps := List.ofFn fun i : Fin bank.length => [i.val + 1]
        refine ⟨[],reps,by simp,?_,?_,initMask⟩
        · change (List.ofFn fun i : Fin bank.length => [i.val+1]).map (meet bank) = bank
          rw [List.map_ofFn]
          apply Eq.trans _ (List.ofFn_getElem (xs := bank))
          apply congrArg List.ofFn
          funext i
          have h : (0::bank).getD (i.val+1) 0 = bank[i.val] := by
            rw [List.getD_cons_succ,List.getD_eq_getElem _ _ i.isLt]
          change ((0::bank).getD (i.val+1) 0) &&& mask = bank[i.val]
          rw [h,initMask _ (List.getElem_mem i.isLt)]
        · intro s hs t ht
          obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs
          have ht' : t = i.val + 1 := by simpa using ht
          change t ≤ bank.length
          omega
      | append_singleton gs g ih =>
        obtain ⟨ops,reps,count,hrep,well,values⟩ := ih
        let w := ops.foldl merge bank
        let left := reps.getD g.2.1 [0]
        let right := reps.getD g.2.2 [0]
        have hleft : meet w left = (gs.foldl step bank).getD g.2.1 0 := by
          rw [← hrep]
          exact getSound reps w g.2.1
        have hright : meet w right = (gs.foldl step bank).getD g.2.2 0 := by
          rw [← hrep]
          exact getSound reps w g.2.2
        have gl : ∀ i ∈ left, i ≤ w.length := getPart _ _ _ well
        have gr : ∀ i ∈ right, i ≤ w.length := getPart _ _ _ well
        cases hg : g.1
        · refine ⟨ops,reps++[left++right],?_,?_,?_,values⟩
          · rw [List.countP_append,List.countP_singleton,hg]
            exact count
          · change (reps++[left++right]).map (meet w) = (gs++[g]).foldl step bank
            rw [List.map_append,List.map_singleton,combine,hrep,List.foldl_append,List.foldl_cons,
              List.foldl_nil]
            change _ = (gs.foldl step bank) ++ [if g.1 then
              (gs.foldl step bank).getD g.2.1 0 ||| (gs.foldl step bank).getD g.2.2 0 else
              (gs.foldl step bank).getD g.2.1 0 &&& (gs.foldl step bank).getD g.2.2 0]
            rw [hg,hleft,hright]
            rfl
          · intro s hs i hi
            rcases List.mem_append.mp hs with hs' | hs'
            · exact well s hs' i hi
            · have e : s = left++right := List.mem_singleton.mp hs'
              rw [e] at hi
              exact (List.mem_append.mp hi).elim (gl i) (gr i)
        · let result := meet w left ||| meet w right
          let next := w ++ [result]
          have kept : (ops ++ [(left,right)]).foldl merge bank = next := by
            rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
          have resultMask : result &&& mask = result := by
            change (meet w left ||| meet w right) &&& mask = _
            rw [Nat.and_or_distrib_right,bounded,bounded]
          refine ⟨ops++[(left,right)],reps++[[w.length+1]],?_,?_,?_,?_⟩
          · rw [List.length_append,List.length_singleton,List.countP_append,List.countP_singleton,hg]
            exact Nat.add_le_add_right count 1
          · rw [kept,List.map_append,List.map_singleton]
            have same : reps.map (meet next) = reps.map (meet w) := by
              apply List.map_congr_left
              intro s hs
              exact stable w s result (well s hs)
            have atEnd : meet next [w.length+1] = result := by
              change (((0::w) ++ [result]).getD (w.length+1) 0) &&& mask = result
              rw [List.getD_append_right _ _ _ _ (by simp),List.length_cons,Nat.sub_self]
              change result &&& mask = result
              exact resultMask
            rw [same,hrep,atEnd,List.foldl_append,List.foldl_cons,List.foldl_nil]
            change (gs.foldl step bank) ++ [result] = (gs.foldl step bank) ++ [if g.1 then
              (gs.foldl step bank).getD g.2.1 0 ||| (gs.foldl step bank).getD g.2.2 0 else
              (gs.foldl step bank).getD g.2.1 0 &&& (gs.foldl step bank).getD g.2.2 0]
            rw [hg,← hleft,← hright]
            rfl
          · intro s hs i hi
            rw [kept]
            have len : next.length = w.length+1 := by simp [next]
            rcases List.mem_append.mp hs with old | new
            · rw [len]
              exact (well s old i hi).trans (Nat.le_succ _)
            · have ea : s = [w.length+1] := List.mem_singleton.mp new
              rw [ea] at hi
              exact (List.mem_singleton.mp hi).trans len.symm |>.le
          · intro c hc
            rw [kept] at hc
            exact (List.mem_append.mp hc).elim (values c) (fun h => List.mem_singleton.mp h ▸ resultMask)
    obtain ⟨ops,reps,count,hrep,_,_⟩ := synth gates
    refine ⟨ops,reps.getD out [0],count,?_⟩
    rw [← hrep]
    exact getSound reps _ out
  by_contra! few
  let input (r : ℕ) (i : Fin 11) := r.testBit i.val
  let rows := (List.range 2048).filter fun r => !r.testBit v.val
  let pack := fun f : ℕ → Bool => (rows.map f).foldr Nat.bit 0
  let bank := List.ofFn fun i : Fin 11 => pack (fun r => r.testBit i.val)
  let target := pack fun r => graphFun G ∅ (input r)
  let mask := 2^rows.length-1
  let step := fun (b : List ℕ) (g : Bool × ℕ × ℕ) =>
    let a := b.getD g.2.1 0
    let c := b.getD g.2.2 0
    b ++ [if g.1 then a ||| c else a &&& c]
  let meet := fun (bank part : List ℕ) =>
    part.foldr (fun i a => (0::bank).getD i 0 &&& a) mask
  let merge := fun (bank : List ℕ) (pair : List ℕ × List ℕ) =>
    bank ++ [meet bank pair.1 ||| meet bank pair.2]
  let encode (g : Gate) := (g.op.eval [true,false],g.inputs.getD 0 0,g.inputs.getD 1 0)
  let isOr (g : Gate) : Bool := GateOp.rec false true false (fun _ => false) false g.op
  have orCount : (C.gates.map encode).countP Prod.fst = C.gates.countP isOr := by
    rw [List.countP_map]
    apply List.countP_congr
    intro g hg
    rcases ao.1 g hg with h | h
    · change (g.op.eval [true,false] = true ↔ (GateOp.rec false true false (fun _ => false) false g.op : Bool) = true)
      rw [h]
      rfl
    · change (g.op.eval [true,false] = true ↔ (GateOp.rec false true false (fun _ => false) false g.op : Bool) = true)
      rw [h]
      rfl
  have masked : ∀ c ∈ bank, c &&& mask = c := by
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    change (_ && (2^rows.length-1).testBit j) = _
    rw [Nat.testBit_two_pow_sub_one]
    by_cases ok : j < rows.length
    · rw [decide_eq_true ok,Bool.and_true]
    · rw [decide_eq_false ok,Bool.and_false]
      change false = ((rows.map (fun r => r.testBit i.val)).foldr Nat.bit 0).testBit j
      rw [packBit,List.getD_eq_default]
      simpa using Nat.le_of_not_lt ok
  have inputOK (r : ℕ) (hr : r ∈ rows) : input r v = false := by
    have h := (List.mem_filter.mp hr).2
    change (!input r v) = true at h
    cases he : input r v <;> simp [he] at h ⊢
  have bankBits (j : ℕ) : bank.map (fun b => b.testBit j) =
      List.ofFn (input (rows.getD j 0)) := by
    change (List.ofFn fun i : Fin 11 => pack (fun r => input r i)).map (fun b => b.testBit j) = _
    rw [List.map_ofFn]
    congr 1
    funext i
    change ((rows.map (fun r => input r i)).foldr Nat.bit 0).testBit j = input (rows.getD j 0) i
    rw [packBit]
    simpa [input] using List.getD_map (n := j) rows 0 (fun r => input r i)
  have produce :
      ((C.gates.map encode).foldl step bank).getD C.output 0 = target := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [List.foldl_map]
    have h := simulate 11 C ao bank j
    change ((C.gates.foldl (fun b g => step b (encode g)) bank).getD C.output 0).testBit j =
      C.eval (bank.map fun b => b.testBit j) at h
    rw [h,bankBits]
    let label := fun r => graphFun G ∅ (input r)
    change circuitFun 11 C (input (rows.getD j 0)) = ((rows.map label).foldr Nat.bit 0).testBit j
    rw [packBit]
    by_cases valid : j < rows.length
    · have within : j < (rows.map label).length := by simpa using valid
      rw [List.getD_eq_getElem _ _ valid,List.getD_eq_getElem _ _ within,List.getElem_map]
      exact agree _ (inputOK _ (List.getElem_mem valid))
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt valid),List.getD_eq_default]
      · have zero : graphFun G ∅ (input 0) = false := by
          change (decide (∃ a ∈ (∅ : Finset (Fin 11)), input 0 a = true) ||
            decide (∃ u w, G.Adj u w ∧ input 0 u = true ∧ input 0 w = true)) = false
          simp [input]
        rw [agree _ (by simp [input]),zero]
      · simpa using Nat.le_of_not_lt valid
  obtain ⟨merges,last,count,same⟩ := compress mask bank (C.gates.map encode) C.output masked
  have count' : merges.length ≤ 12 := by
    rw [orCount] at count
    change C.gates.countP isOr < 13 at few
    omega
  change meet (merges.foldl merge bank) last = _ at same
  exact (rejection v hv merges last count') (same.trans produce)
