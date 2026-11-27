import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Insert the masked input after its companion. A least counterexample uses the full budget.
set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3614_2
    (lower :
      let F := (fun (x : Fin 9 → Bool) =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
      ∀ D : Circuit, FanInTwo D → circuitFun 9 D = F → 15 ≤ D.size)
    (remaining :
      let F := (fun (x : Fin 9 → Bool) =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
      let R := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 6]
      let W := fun (C : Circuit) k x => (C.wires (R x)).getD k false
      ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (b : Bool), v ≠ 0 → v ≠ 6 →
        FanInTwo C → C.size = 13 → C.output = 22 → 10 ≤ k → k < 22 →
        (b = false → k = 10 → v = 1 ∨ v = 4 ∨ v = 7) →
        (∀ g ∈ C.gates.take (k+1-10), v.val ∉ g.inputs) →
        (∀ x y, (∀ u, u ≠ v → x u = y u) → F x ≠ F y → W C k x = !b) →
        (∃ g ∈ C.gates, 9 ∈ g.inputs) → (∃ x, x v = !b ∧ W C k x = b ∧ C.eval (R x) ≠ F x) →
        ∃ x, C.eval ((R x).set v.val (if b then x v || W C k x else x v && W C k x)) ≠ F x) : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : Bool),   x3 ≠ (0 : Fin (9 : ℕ)) →     x3 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < (10 : ℕ) + x4.size →               (∀ x13 ∈ List.take (x5 + (1 : ℕ) - (10 : ℕ)) x4.gates, ↑x3 ∉ x13.inputs) →                 (∀ (x14 x15 : Fin (9 : ℕ) → Bool), (∀ (x16 : Fin (9 : ℕ)), x16 ≠ x3 → x14 x16 = x15 x16) → x1 x14 ≠ x1 x15 → (x4.wires (x2 x14)).getD x5 Bool.false = !x6) →                   ∃ (x15 : Fin (9 : ℕ) → Bool),                     have x16 : Bool := (x4.wires (x2 x15)).getD x5 Bool.false;                     x4.eval ((x2 x15).set (↑x3) (if x6 = Bool.true then x15 x3 || x16 else x15 x3 && x16)) ≠ x1 x15 := by
  let target (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))

  let row (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 6]

  let emit (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let maskBit (x h disj : Bool) := if disj then x || h else x && h

  let redirect (v k i : ℕ) : ℕ := if i = v then k else if i < k then i else i+1

  let rename (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

  have fold_size (gs : List Gate) (w : List Bool) : (gs.foldl emit w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [emit]; omega

  have fold_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl emit w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (emit w g) (by simp [emit]; omega)]
      exact List.getD_append _ _ _ _ hi

  have set_emit_avoid (g : Gate) (w : List Bool) (v : ℕ) (val : Bool)
      (hv : v < w.length) (avoid : v ∉ g.inputs) :
      emit (w.set v val) g = (emit w g).set v val := by
    have reads : ∀ i ∈ g.inputs, (w.set v val).getD i false = w.getD i false := by
      intro i hi
      have ne : v ≠ i := by intro eq; apply avoid; exact eq ▸ hi
      by_cases valid : i < w.length
      · rw [List.getD_eq_getElem _ _ (by simpa using valid),List.getD_eq_getElem _ _ valid,
          List.getElem_set_ne ne]
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt valid),
          List.getD_eq_default _ _ (Nat.le_of_not_gt valid)]
    unfold emit
    rw [List.map_congr_left reads,List.set_append_left v val hv]

  have fold_set_avoid (gs : List Gate) (w : List Bool) (v : ℕ) (val : Bool)
      (hv : v < w.length) (avoid : ∀ g ∈ gs, v ∉ g.inputs) :
      gs.foldl emit (w.set v val) = (gs.foldl emit w).set v val := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [set_emit_avoid g w v val hv (avoid g (by simp))]
      exact ih (emit w g) (by simp [emit]; omega) (fun a ha => avoid a (by simp [ha]))

  have append_other (w : List Bool) (b : Bool) (i : ℕ) (ne : i ≠ w.length) :
      (w++[b]).getD i false = w.getD i false := by
    by_cases small : i < w.length
    · exact List.getD_append _ _ _ _ small
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

  have suffix_shift (gs : List Gate) (v k : ℕ) (w y : List Bool)
      (hv : v < k) (hk : k ≤ w.length) (len : y.length = w.length + 1)
      (rel : ∀ i, y.getD (redirect v k i) false = w.getD i false) :
      ∀ i, ((gs.map (rename (redirect v k))).foldl emit y).getD (redirect v k i) false =
        (gs.foldl emit w).getD i false := by
    induction gs generalizing w y with
    | nil => exact rel
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      let value := g.op.eval (g.inputs.map fun i => w.getD i false)
      have emitY : emit y (rename (redirect v k) g) = y ++ [value] := by
        change y ++ [g.op.eval ((g.inputs.map (redirect v k)).map fun i => y.getD i false)] = _
        simp only [List.map_map,Function.comp_def]
        rw [List.map_congr_left (fun i _ => rel i)]
      rw [emitY]
      apply ih (w++[value]) (y++[value])
      · simp; omega
      · simp [len]
      intro i
      have sameWire : redirect v k i = y.length ↔ i = w.length := by
        by_cases eq : i = v
        · simp only [redirect]
          rw [ite_eq_left eq]
          omega
        · simp only [redirect]
          rw [ite_eq_right eq]
          split <;> omega
      by_cases hi : i = w.length
      · rw [sameWire.mpr hi,hi]
        simp
      · rw [append_other _ _ _ (fun a => hi (sameWire.mp a)),append_other _ _ _ hi]
        exact rel i

  have append_with_mask (v : ℕ) (old : List Bool) (hv : v < old.length) (bit : Bool) :
      ∀ i, (old ++ [bit]).getD (redirect v old.length i) false = (old.set v bit).getD i false := by
    intro i
    by_cases piv : i = v
    · subst i
      simp only [redirect, ite_true]
      rw [List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self,List.getD_cons_zero,
        List.getD_eq_getElem _ _ (by simp; exact hv)]
      simp
    simp only [redirect]
    rw [ite_eq_right piv]
    by_cases valid : i < old.length
    · rw [ite_eq_left valid,List.getD_append _ _ _ _ valid,List.getD_eq_getElem _ _ valid,
        List.getD_eq_getElem _ _ (by simpa using valid),List.getElem_set_ne (Ne.symm piv)]
    · rw [ite_eq_right valid,List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

  have seed_correct (x : Fin 9 → Bool) : emit (List.ofFn x) ⟨.or,[0,6]⟩ = row x := by
    change List.ofFn x ++ [x 0 || (x 6 || false)] = row x
    simp [row]

  have row_pivot (x : Fin 9 → Bool) (v : Fin 9) : (row x).getD v.val false = x v := by
    unfold row
    rw [List.getD_append _ _ _ _ (by simpa using v.isLt),
      List.getD_eq_getElem _ _ (by simpa using v.isLt),List.getElem_ofFn]

  have mask_value (x : Fin 9 → Bool) (v : Fin 9) (k : ℕ) (disj : Bool) (old : List Bool)
      (hv : v.val < old.length) (oldv : old.getD v.val false = x v) :
      emit old ⟨if disj then .or else .and,[v.val,k]⟩ =
        old ++ [maskBit (x v) (old.getD k false) disj] := by
    unfold emit maskBit
    cases disj
    · change old ++ [(old.getD v.val false && (old.getD k false && true))] =
        old ++ [x v && old.getD k false]
      rw [Bool.and_true,oldv]
    · change old ++ [(old.getD v.val false || (old.getD k false || false))] =
        old ++ [x v || old.getD k false]
      rw [Bool.or_false,oldv]

  have insert_mask (C : Circuit) (v : Fin 9) (k : ℕ) (disj : Bool)
      (fan : FanInTwo C) (lo : 10 ≤ k) (hi : k < 10+C.size)
      (avoid : ∀ g ∈ C.gates.take (k+1-10), v.val ∉ g.inputs) :
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size+2 ∧
        D.output = redirect v.val (k+1) C.output ∧
        ((∀ g ∈ C.gates, 9 ∉ g.inputs) → (∀ g ∈ D.gates.drop 1, 9 ∉ g.inputs)) ∧
        ∀ x : Fin 9 → Bool, circuitFun 9 D x = C.eval
          ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj)) := by
    let pre := C.gates.take (k+1-10)
    let suf := C.gates.drop (k+1-10)
    let seed : Gate := ⟨.or,[0,6]⟩
    let mask : Gate := ⟨if disj then .or else .and,[v.val,k]⟩
    let shift := rename (redirect v.val (k+1))
    let D : Circuit := ⟨seed :: (pre ++ mask :: suf.map shift),redirect v.val (k+1) C.output⟩
    have split : pre ++ suf = C.gates := List.take_append_drop _ _
    have seedLegal : seed.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ seed.inputs.length ≤ 2 := by
      simp [seed]
    have maskLegal : mask.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ mask.inputs.length ≤ 2 := by
      cases disj <;> simp [mask]
    have legal : FanInTwo D := by
      intro g hg
      change g ∈ seed :: (pre ++ mask :: suf.map shift) at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact seedLegal
      rcases List.mem_append.mp hg with hg | hg
      · exact fan g (by rw [← split]; exact List.mem_append_left _ hg)
      rcases List.mem_cons.mp hg with rfl | hg
      · exact maskLegal
      obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
      obtain ⟨op,arity⟩ := fan g' (by rw [← split]; exact List.mem_append_right _ hg')
      exact ⟨op,by simpa [shift,rename] using arity⟩
    have hsize : D.size = C.size+2 := by
      have len := congrArg List.length split
      change (seed :: (pre ++ mask :: suf.map shift)).length = C.gates.length+2
      simp only [List.length_cons,List.length_append,List.length_map] at len ⊢
      omega
    have preserveNoSeed (avoidSeed : ∀ g ∈ C.gates, 9 ∉ g.inputs) :
        ∀ g ∈ D.gates.drop 1, 9 ∉ g.inputs := by
      intro g hg
      change g ∈ pre ++ mask :: suf.map shift at hg
      rcases List.mem_append.mp hg with hp | hs
      · exact avoidSeed g (by rw [← split]; exact List.mem_append_left _ hp)
      rcases List.mem_cons.mp hs with rfl | hm
      · simp only [mask,List.mem_cons,List.mem_nil_iff,or_false]
        have vlt := v.isLt
        omega
      obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hm
      intro bad
      have ban := avoidSeed h (by rw [← split]; exact List.mem_append_right _ hh)
      change 9 ∈ h.inputs.map (redirect v.val (k+1)) at bad
      obtain ⟨i,used,eq⟩ := List.mem_map.mp bad
      have vlt := v.isLt
      have same : i = 9 := by
        unfold redirect at eq
        split at eq
        · omega
        split at eq <;> omega
      exact ban (same ▸ used)
    refine ⟨D,legal,hsize,rfl,preserveNoSeed,?_⟩
    intro x
    let old := pre.foldl emit (row x)
    have kBound : k+1-10 ≤ C.gates.length := by change k < 10+C.gates.length at hi; omega
    have length : old.length = k+1 := by
      rw [show old = pre.foldl emit (row x) by rfl,fold_size]
      simp [pre,row,Nat.min_eq_left kBound]
      omega
    have vBound : v.val < old.length := by rw [length]; have := v.isLt; omega
    have saved : (C.wires (row x)).getD k false = old.getD k false := by
      change (C.gates.foldl emit (row x)).getD k false = _
      rw [← split,List.foldl_append]
      exact fold_preserves suf old k (by omega)
    have savedV : old.getD v.val false = x v := by
      rw [fold_preserves pre (row x) _ (by simp [row]; have := v.isLt; omega),row_pivot]
    let bit := maskBit (x v) (old.getD k false) disj
    have oldSet : pre.foldl emit ((row x).set v.val bit) = old.set v.val bit :=
      fold_set_avoid pre (row x) v.val bit (by simp [row]; have := v.isLt; omega) avoid
    have law (i : ℕ) : (old ++ [bit]).getD (redirect v.val (k+1) i) false =
        (old.set v.val bit).getD i false := by rw [← length]; exact append_with_mask v.val old vBound bit i
    have simulated := suffix_shift suf v.val (k+1) (old.set v.val bit) (old++[bit])
      (by have := v.isLt; omega) (by simp [length]) (by simp) law C.output
    unfold circuitFun
    change ((pre ++ mask :: suf.map shift).foldl emit (emit (List.ofFn x) seed)).getD
        (redirect v.val (k+1) C.output) false =
      (C.gates.foldl emit ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj))).getD C.output false
    rw [seed_correct, List.foldl_append, List.foldl_cons,mask_value x v k disj old vBound savedV,
      saved,← split,List.foldl_append,oldSet]
    exact simulated

  have take_output (D : Circuit) (n k : ℕ) (bound : D.output < n + min k D.size)
      (fan : FanInTwo D) :
      ∃ E : Circuit, FanInTwo E ∧ E.size ≤ k ∧ circuitFun n E = circuitFun n D := by
    let E : Circuit := ⟨D.gates.take k,D.output⟩
    have legal : FanInTwo E := fun g h => fan g (List.mem_of_mem_take h)
    refine ⟨E,legal,by change (D.gates.take k).length ≤ k; simp,?_⟩
    funext x
    let pre := D.gates.take k
    let tail := D.gates.drop k
    have split : pre ++ tail = D.gates := List.take_append_drop _ _
    change (pre.foldl emit (List.ofFn x)).getD D.output false =
      (D.gates.foldl emit (List.ofFn x)).getD D.output false
    rw [← split,List.foldl_append]
    symm
    apply fold_preserves
    rw [fold_size]
    change D.output < n + min k D.gates.length at bound
    simpa [pre] using bound

  -- Dropping a first gate that no later gate reads preserves the circuit value.
  have drop_first (D : Circuit) (seed : Gate) (gs : List Gate) (shape : D.gates = seed :: gs)
      (fan : FanInTwo D) (out : D.output ≠ 9) (avoid : ∀ g ∈ gs, 9 ∉ g.inputs) :
      ∃ E : Circuit, FanInTwo E ∧ E.size + 1 = D.size ∧ circuitFun 9 E = circuitFun 9 D := by
    let shift (i : ℕ) : ℕ := if i < 9 then i else i-1
    let E : Circuit := ⟨gs.map (rename shift),shift D.output⟩
    have legal : FanInTwo E := by
      intro g hg
      obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
      obtain ⟨op,arity⟩ := fan g' (by rw [shape]; exact List.mem_cons_of_mem _ hg')
      exact ⟨op,by simpa [rename] using arity⟩
    have size : E.size+1 = D.size := by
      change (gs.map (rename shift)).length + 1 = D.gates.length
      rw [shape,List.length_map,List.length_cons]
    refine ⟨E,legal,size,?_⟩
    let Rel (old new : List Bool) := 9 ≤ new.length ∧ old.length = new.length+1 ∧
      ∀ i, i ≠ 9 → new.getD (shift i) false = old.getD i false
    have preserve (g : Gate) (old new : List Bool) (rel : Rel old new) (clean : 9 ∉ g.inputs) :
        Rel (emit old g) (emit new (rename shift g)) := by
      obtain ⟨room,len,same⟩ := rel
      let val := g.op.eval (g.inputs.map fun i => old.getD i false)
      have equalInputs : (g.inputs.map fun i => new.getD (shift i) false) =
          (g.inputs.map fun i => old.getD i false) :=
        List.map_congr_left fun i hi => same i (fun h => clean (h ▸ hi))
      have newStep : emit new (rename shift g) = new ++ [val] := by
        change new ++ [g.op.eval ((g.inputs.map shift).map fun i => new.getD i false)] = _
        rw [List.map_map]
        exact congrArg (fun xs => new ++ [g.op.eval xs]) equalInputs
      rw [newStep]
      change Rel (old++[val]) (new++[val])
      refine ⟨by simp; omega,by simp [len],?_⟩
      intro i ne
      have fresh : shift i = new.length ↔ i = old.length := by
        unfold shift
        split <;> omega
      by_cases h : i = old.length
      · rw [fresh.mpr h,h]
        simp
      · rw [append_other _ _ _ (fun eq => h (fresh.mp eq)),append_other _ _ _ h]
        exact same i ne
    have fold (as : List Gate) (old new : List Bool) (rel : Rel old new)
        (clean : ∀ g ∈ as, 9 ∉ g.inputs) :
        Rel (as.foldl emit old) ((as.map (rename shift)).foldl emit new) := by
      induction as generalizing old new with
      | nil => exact rel
      | cons g rest ih =>
        simp only [List.foldl_cons,List.map_cons]
        exact ih _ _ (preserve g old new rel (clean g (by simp))) (fun a h => clean a (by simp [h]))
    funext x
    let raw := List.ofFn x
    have rawLen : raw.length = 9 := List.length_ofFn
    have start : Rel (emit raw seed) raw := by
      refine ⟨by omega,by simp [emit],?_⟩
      intro i ne
      by_cases small : i < 9
      · simp only [shift,ite_eq_left small]
        exact (List.getD_append _ _ _ _ (by omega)).symm
      · simp only [shift,ite_eq_right small]
        rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp [emit]; omega)]
    have agree := (fold gs (emit raw seed) raw start avoid).2.2 D.output out
    change ((gs.map (rename shift)).foldl emit raw).getD (shift D.output) false =
      (D.gates.foldl emit raw).getD D.output false
    rw [shape,List.foldl_cons]
    exact agree

  have seeded_bound (C : Circuit) (fan : FanInTwo C) :
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size+1 ∧
        ∀ x : Fin 9 → Bool, circuitFun 9 D x = C.eval (row x) := by
    let seed : Gate := ⟨.or,[0,6]⟩
    let D : Circuit := ⟨seed::C.gates,C.output⟩
    have legal : FanInTwo D := by
      intro g h
      rcases List.mem_cons.mp h with rfl | h
      · simp [seed]
      · exact fan _ h
    refine ⟨D,legal,rfl,?_⟩
    intro x
    change (C.gates.foldl emit (emit (List.ofFn x) seed)).getD C.output false =
      (C.gates.foldl emit (row x)).getD C.output false
    rw [seed_correct]

  have set_neighbor (x : Fin 9 → Bool) (v : Fin 9) (v0 : v ≠ 0) (v6 : v ≠ 6) (b : Bool) :
      row (Function.update x v b) = (row x).set v.val b := by
    have upd (i : Fin 9) : Function.update x v b i = if i = v then b else x i := by
      by_cases z : i = v
      · subst i; simp
      · exact (Function.update_of_ne z _ _).trans (by simp [z])
    unfold row
    rw [List.set_append_left v.val b (by simpa using v.isLt)]
    congr 1
    · apply List.ext_getElem (by simp)
      intro i hi hj
      rw [List.getElem_ofFn,upd]
      by_cases eq : i = v.val
      · subst i; simp
      · rw [List.getElem_set_ne (Ne.symm eq),List.getElem_ofFn]
        simp [show (⟨i,by simpa using hi⟩ : Fin 9) ≠ v from fun h => eq (congrArg Fin.val h)]
    · simp [Function.update_of_ne (Ne.symm v0),Function.update_of_ne (Ne.symm v6)]

  have passive_output (C : Circuit) (v : Fin 9) (avoid : ∀ g ∈ C.gates, v.val ∉ g.inputs)
      (out : C.output ≠ v.val) (x : Fin 9 → Bool) (b : Bool) :
      C.eval ((row x).set v.val b) = C.eval (row x) := by
    change (C.gates.foldl emit ((row x).set v.val b)).getD C.output false =
      (C.gates.foldl emit (row x)).getD C.output false
    rw [fold_set_avoid _ _ _ _ (by simp [row]; have := v.isLt; omega) avoid]
    let w := C.gates.foldl emit (row x)
    change (w.set v.val b).getD C.output false = w.getD C.output false
    by_cases lim : C.output < w.length
    · rw [List.getD_eq_getElem _ _ (by simpa using lim),List.getD_eq_getElem _ _ lim,
          List.getElem_set_ne (Ne.symm out)]
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

  have some_sensitive (v : Fin 9) : ∃ x : Fin 9 → Bool,
      target x ≠ target (Function.update x v true) := by
    let sample : Fin 9 → Fin 9 := ![1,0,1,2,3,0,1,2,3]
    have witnesses : ∀ w : Fin 9, let x : Fin 9 → Bool := fun j => decide (j = sample w)
        target x ≠ target (Function.update x w true) := by decide +kernel
    exact ⟨fun j => decide (j = sample v),witnesses v⟩

  have set_pivot_self (x : Fin 9 → Bool) (v : Fin 9) : (row x).set v.val (x v) = row x := by
    have room : v.val < (row x).length := by simp [row]; have := v.isLt; omega
    have read : (row x)[v.val] = x v := by
      rw [← List.getD_eq_getElem _ false room,row_pivot]
    rw [← read,List.set_getElem_self room]

  have mask_changes (x h disj : Bool) (different : maskBit x h disj ≠ x) : x = !disj ∧ h = disj := by
    cases x <;> cases h <;> cases disj <;> first | exact False.elim (different rfl) | exact ⟨rfl,rfl⟩

  have normalized_bounds
      (lower : ∀ D : Circuit, FanInTwo D → circuitFun 9 D = target → 15 ≤ D.size)
      (C : Circuit) (v : Fin 9) (k : ℕ) (disj : Bool)
      (v0 : v ≠ 0) (v6 : v ≠ 6) (fan : FanInTwo C) (size : C.size ≤ 13)
      (lo : 10 ≤ k) (hi : k < 10+C.size)
      (avoid : ∀ g ∈ C.gates.take (k+1-10), v.val ∉ g.inputs)
      (correct : ∀ x : Fin 9 → Bool, C.eval
          ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj)) = target x) :
      C.size = 13 ∧ C.output = 22 ∧ k < 22 ∧
        (∃ g ∈ C.gates, 9 ∈ g.inputs) ∧
        ∃ x : Fin 9 → Bool, x v = !disj ∧ (C.wires (row x)).getD k false = disj ∧
          C.eval (row x) ≠ target x := by
    obtain ⟨D,dfan,dsize,dout,noSeed,deval⟩ := insert_mask C v k disj fan lo hi avoid
    have dtarget : circuitFun 9 D = target := funext fun x => (deval x).trans (correct x)
    have large := lower D dfan dtarget
    have exactSize : C.size = 13 := by omega
    have outLimit : C.output < 23 := by
      by_contra! out
      let x : Fin 9 → Bool := fun _ => true
      let a := (row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj)
      have width : (C.wires a).length = 23 := by
        change (C.gates.foldl emit a).length = 23
        rw [fold_size]
        simp [a,row,show C.gates.length = 13 from exactSize]
      have gone : C.eval a = false := List.getD_eq_default _ _ (by omega)
      have yes : target x = true := by rfl
      exact Bool.false_ne_true (gone.symm.trans ((correct x).trans yes))
    have notRaw : C.output ≠ v.val := by
      intro eq
      have outputRaw (x : Fin 9 → Bool) :
          C.eval ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj)) =
            maskBit (x v) ((C.wires (row x)).getD k false) disj := by
        let b := maskBit (x v) ((C.wires (row x)).getD k false) disj
        change (C.gates.foldl emit ((row x).set v.val b)).getD C.output false = b
        have inRange : v.val < ((row x).set v.val b).length := by
          simp [row]; have := v.isLt; omega
        rw [eq,fold_preserves _ _ _ inRange,List.getD_eq_getElem _ _ inRange]
        simp
      have graphOff : ∀ w : Fin 9, target (fun i => decide (i = w)) = false := by decide +kernel
      have graphOn : ∀ w : Fin 9, target (fun i => decide (i ≠ w)) = true := by decide +kernel
      cases disj
      · have claim := (outputRaw (fun i => decide (i ≠ v))).symm.trans (correct _)
        rw [graphOn] at claim
        simpa [maskBit] using claim
      · have claim := (outputRaw (fun i => decide (i = v))).symm.trans (correct _)
        rw [graphOff] at claim
        simpa [maskBit] using claim
    have outExact : C.output = 22 := by
      by_contra ne
      have outBelow : D.output < 23 := by
        rw [dout]
        simp only [redirect]
        rw [ite_eq_right notRaw]
        split <;> omega
      have width : D.size = 15 := by omega
      obtain ⟨E,efan,esize,eval⟩ := take_output D 9 14 (by simpa [width] using outBelow) dfan
      have big := lower E efan (eval.trans dtarget)
      omega
    have cutEarly : k < 22 := by
      by_contra! later
      have equal : k = 22 := by omega
      have none : ∀ g ∈ C.gates, v.val ∉ g.inputs := by
        have take : C.gates.take (k+1-10) = C.gates := by
          apply List.take_of_length_le
          change C.size ≤ _
          omega
        simpa only [take] using avoid
      have noRead : C.output ≠ v.val := by rw [outExact]; have := v.isLt; omega
      obtain ⟨x,sensitive⟩ := some_sensitive v
      have unmask (z : Fin 9 → Bool) : C.eval (row z) = target z := by
        rw [← correct z]
        exact (passive_output C v none noRead z _).symm
      have same : C.eval (row (Function.update x v true)) = C.eval (row x) := by
        rw [set_neighbor x v v0 v6]
        exact passive_output C v none noRead x true
      rw [unmask,unmask] at same
      exact sensitive same.symm
    have usesSeed : ∃ g ∈ C.gates, 9 ∈ g.inputs := by
      by_contra! absent
      have outputNotSeed : D.output ≠ 9 := by
        rw [dout,outExact]
        have vlt := v.isLt
        unfold redirect
        split
        · omega
        split <;> omega
      have many : 0 < D.gates.length := by change 0 < D.size; omega
      obtain ⟨first,rest,shape⟩ := List.exists_cons_of_length_pos many
      have clean : ∀ g ∈ rest, 9 ∉ g.inputs := by
        have avoid := noSeed absent
        rw [shape] at avoid
        exact avoid
      obtain ⟨E,efan,esize,eval⟩ := drop_first D first rest shape dfan outputNotSeed clean
      have big := lower E efan (eval.trans dtarget)
      omega
    have nontrivial : ∃ x : Fin 9 → Bool, C.eval (row x) ≠ target x := by
      by_contra! all
      obtain ⟨E,fanE,sizeE,evalE⟩ := seeded_bound C fan
      have big := lower E fanE (funext fun x => (evalE x).trans (all x))
      omega
    obtain ⟨x,bad⟩ := nontrivial
    have changed : maskBit (x v) ((C.wires (row x)).getD k false) disj ≠ x v := by
      intro same
      have works := correct x
      rw [same,set_pivot_self] at works
      exact bad works
    obtain ⟨pivot,companion⟩ := mask_changes _ _ _ changed
    exact ⟨exactSize,outExact,cutEarly,usesSeed,x,pivot,companion,bad⟩


  let pivots : Fin 4 → Fin 9 := ![2,3,5,8]
  let samples : Fin 4 → List ℕ := ![[2,201,400,40],[4,112,386,5],[128,69,274,9],[8,116,193,34]]
  let sampleRow (m : ℕ) (x : Fin 9) : Bool := m.testBit x.val
  let ops : Fin 3 → GateOp := ![.and,.or,.not]
  let args (t : Fin 3) (a b : Fin 11) : List (Fin 11) :=
    if t = 0 then [] else if t = 1 then [a] else [a,b]
  let localEval (op t : Fin 3) (a b : Fin 11) (x : Fin 9 → Bool) : Bool :=
    (ops op).eval ((args t a b).map fun i => (row x).getD i.val false)

  have probes : ∀ p : Fin 4, ∀ r ∈ samples p,
      target (sampleRow r) ≠ target (Function.update (sampleRow r) (pivots p) true) := by
    intro p
    fin_cases p <;> decide +kernel

  have table : ∀ (p : Fin 4) (op t : Fin 3) (a b : Fin 11),
      (∀ i ∈ args t a b, i.val ≠ (pivots p).val) →
      (∀ r ∈ samples p, localEval op t a b (sampleRow r) = true) →
      (op = 0 ∧ t = 0) ∨ (op = 2 ∧ (t = 0 ∨ a = 10)) := by
    -- Quantify over the finite lists as Boolean tests before running the table.
    have h : ∀ (p : Fin 4) (op t : Fin 3) (a b : Fin 11),
        (args t a b).all (fun i => decide (i.val ≠ (pivots p).val)) = true →
        (samples p).all (fun r => localEval op t a b (sampleRow r)) = true →
        (op = 0 ∧ t = 0) ∨ (op = 2 ∧ (t = 0 ∨ a = 10)) := by
      decide +kernel
    intro p op t a b avoid good
    exact h p op t a b (List.all_eq_true.mpr (fun i hi => decide_eq_true (avoid i hi)))
      (List.all_eq_true.mpr good)

  let slot (i : ℕ) : Fin 11 := if h : i < 10 then ⟨i,by omega⟩ else 10

  have normalize_read (x : Fin 9 → Bool) (i : ℕ) :
      (row x).getD (slot i).val false = (row x).getD i false := by
    by_cases h : i < 10
    · simp [slot,h]
    · rw [List.getD_eq_default _ _ (by simp [slot,h,row]),List.getD_eq_default _ _ (by simp [row]; omega)]

  have constant_true (op t : Fin 3) (a b : Fin 11)
      (h : (op = 0 ∧ t = 0) ∨ (op = 2 ∧ (t = 0 ∨ a = 10))) (x : Fin 9 → Bool) :
      localEval op t a b x = true := by
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩
    · rfl
    · rfl
    · have falseVal : (row x).getD 10 false = false := List.getD_eq_default _ _ (by simp [row])
      fin_cases t
      · rfl
      · change (!(row x).getD 10 false) = true
        rw [falseVal]
        rfl
      · change (!(row x).getD 10 false) = true
        rw [falseVal]
        rfl

  have first_gate_constant (C : Circuit) (p : Fin 4)
      (fan : FanInTwo C) (used : 0 < C.size)
      (avoid : ∀ g ∈ C.gates.take 1, (pivots p).val ∉ g.inputs)
      (neutral : ∀ x y : Fin 9 → Bool, (∀ u, u ≠ pivots p → x u = y u) → target x ≠ target y →
        (C.wires (row x)).getD 10 false = true) :
      ∀ x : Fin 9 → Bool, (C.wires (row x)).getD 10 false = true := by
    change 0 < C.gates.length at used
    obtain ⟨g,gs,shape⟩ := List.exists_cons_of_length_pos used
    obtain ⟨opOK,len⟩ := fan g (by rw [shape]; simp)
    have unused : (pivots p).val ∉ g.inputs := avoid g (by rw [shape]; simp)
    have opShape : ∃ op : Fin 3, ops op = g.op := by
      rcases (by simpa using opOK : g.op = .and ∨ g.op = .or ∨ g.op = .not) with h|h|h
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
      · exact ⟨2,h.symm⟩
    obtain ⟨op,hop⟩ := opShape
    have argsShape : ∃ (t : Fin 3) (a b : Fin 11), g.inputs.map slot = args t a b := by
      cases data : g.inputs with
      | nil => exact ⟨0,0,0,rfl⟩
      | cons a rest =>
        cases rest with
        | nil => exact ⟨1,slot a,0,rfl⟩
        | cons b tail =>
          have empty : tail = [] := List.length_eq_zero_iff.mp (by rw [data] at len; simp only [List.length_cons] at len; omega)
          subst tail
          exact ⟨2,slot a,slot b,rfl⟩
    obtain ⟨t,a,b,ht⟩ := argsShape
    have avoidSlot : ∀ i ∈ args t a b, i.val ≠ (pivots p).val := by
      rw [← ht]
      intro i hi eq
      obtain ⟨j,used,eq'⟩ := List.mem_map.mp hi
      subst i
      by_cases h : j < 10
      · simp [slot,h] at eq
        exact unused (eq ▸ used)
      · simp [slot,h] at eq
        have room := (pivots p).isLt
        omega
    have eval (x : Fin 9 → Bool) : (C.wires (row x)).getD 10 false = localEval op t a b x := by
      change (C.gates.foldl emit (row x)).getD 10 false = _
      rw [shape,List.foldl_cons,fold_preserves gs _ _ (by simp [emit,row])]
      have newStep : (emit (row x) g).getD 10 false = g.op.eval (g.inputs.map fun i => (row x).getD i false) := by
        change ((row x) ++ [_]).getD 10 false = _
        have len : (row x).length = 10 := by simp [row]
        conv_lhs => rw [(show 10 = (row x).length from len.symm)]
        simp
      rw [newStep]
      unfold localEval
      rw [hop,← ht,List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => (normalize_read x i).symm
    have holds : ∀ r ∈ samples p, localEval op t a b (sampleRow r) = true := by
      intro r hr
      rw [← eval]
      exact neutral _ _ (fun u hu => (Function.update_of_ne hu _ _).symm) (probes p r hr)
    intro x
    rw [eval]
    exact constant_true op t a b (table p op t a b avoidSlot holds) x

  change ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (b : Bool), v ≠ 0 → v ≠ 6 →
    FanInTwo C → C.size ≤ 13 → 10 ≤ k → k < 10+C.size →
    (∀ g ∈ C.gates.take (k+1-10), v.val ∉ g.inputs) →
    (∀ x y, (∀ u, u ≠ v → x u = y u) → target x ≠ target y →
      (C.wires (row x)).getD k false = !b) →
    ∃ x, C.eval ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) b)) ≠ target x
  intro v C k b v0 v6 fan size lo hi avoid sensitive
  change ∃ x, C.eval ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) b)) ≠ target x
  by_contra! correct
  obtain ⟨exactSize,last,early,usesSeed,nontrivial⟩ :=
    normalized_bounds lower C v k b v0 v6 fan size lo hi avoid correct
  have earlyMask : b = false → k = 10 → v = 1 ∨ v = 4 ∨ v = 7 := by
    intro hb hk
    by_contra! bad
    have covers : ∀ j : Fin 9, j ≠ 0 → j ≠ 6 → j ≠ 1 → j ≠ 4 → j ≠ 7 →
        ∃ p : Fin 4, pivots p = j := by decide +kernel
    obtain ⟨p,rfl⟩ := covers v v0 v6 bad.1 bad.2.1 bad.2.2
    subst b
    subst k
    have constant := first_gate_constant C p fan (by omega) (by simpa using avoid)
      (by simpa using sensitive)
    obtain ⟨x,_,flip,_⟩ := nontrivial
    rw [constant x] at flip
    cases flip
  obtain ⟨x,hx⟩ := remaining v C k b v0 v6 fan exactSize last lo early earlyMask avoid sensitive usesSeed nontrivial
  exact hx (correct x)
