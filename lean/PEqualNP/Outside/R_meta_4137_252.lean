import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fix the edge with endpoints zero and one as an unordered pair.
-- Its eight symmetries leave three vertex representatives and ten unordered pair representatives.
-- Except for the promised pair, the tail must still use each operand as an output or a gate input.
-- Wire 27 represents all out-of-range reads, giving the residual search a finite set of indices.
-- Remove the first gate and supply its output as one extra wire to a circuit with sixteen gates.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_4137_252
    (unary : ∀ (i : Fin 10) (f : Bool → Bool), i.val ∈ ([0,2,3] : List ℕ) →
      ∀ D : Circuit, FanInTwo D → D.size ≤ 16 →
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 27) → D.output ≤ 27 → ∃ x : Fin 10 → Bool,
      (x 0 && x 1) = false ∧ D.eval (List.ofFn x ++ [f (x i)]) ≠ (fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true)) x)
    (binary : ∀ (a b : Fin 10) (isOr : Bool), 10 * a.val + b.val ∈ ([1,2,3,4,23,24,26,28,37,38] : List ℕ) →
      (isOr = true ∨ 10 * a.val + b.val ≠ 1) →
      ∀ D : Circuit, FanInTwo D → D.size ≤ 16 →
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 27) → D.output ≤ 27 →
      (a.val + b.val ≠ 1 →
        (D.output = a.val ∨ ∃ g ∈ D.gates, a.val ∈ g.inputs) ∧
        (D.output = b.val ∨ ∃ g ∈ D.gates, b.val ∈ g.inputs)) →
      (10 * a.val + b.val = 1 →
        (D.output = a.val ∨ ∃ g ∈ D.gates, a.val ∈ g.inputs) ∨
        (D.output = b.val ∨ ∃ g ∈ D.gates, b.val ∈ g.inputs)) →
      ∃ x : Fin 10 → Bool,
      (x 0 && x 1) = false ∧ D.eval (List.ofFn x ++ [if isOr then x a || x b else x a && x b]) ≠ (fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ))) = Bool.false ∧ x1.eval (List.ofFn x4) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C fan budget
  let target : (Fin 10 → Bool) → Bool := (fun x : Fin 10 → Bool => decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true))
  let promise (x : Fin 10 → Bool) : Prop := (x 0 && x 1) = false
  let wrong (D : Circuit) (seed : (Fin 10 → Bool) → Bool) : Prop :=
    ∃ x, promise x ∧ D.eval (List.ofFn x ++ [seed x]) ≠ target x
  let perm (s : Fin 8) (i : Fin 10) : Fin 10 :=
    (([[0,1,2,3,4,5,6,7,8,9], [0,1,2,7,5,4,6,3,9,8],
       [0,1,6,8,5,4,2,9,3,7], [0,1,6,9,4,5,2,8,7,3],
       [1,0,4,3,2,6,5,9,8,7], [1,0,4,9,6,2,5,3,7,8],
       [1,0,5,7,2,6,4,8,9,3], [1,0,5,8,6,2,4,7,3,9]] :
       List (List (Fin 10))).getD s.val []).getD i.val 0
  let adj (i j : Fin 10) :=
    (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val
  have keepsEdge : ∀ (s : Fin 8) (i j : Fin 10), adj (perm s i) (perm s j) = adj i j := by decide +kernel
  have onto : ∀ (s : Fin 8) (i : Fin 10), ∃ k : Fin 10, perm s k = i := by decide +kernel
  have fixesPair : ∀ s : Fin 8, (perm s 0 = 0 ∧ perm s 1 = 1) ∨
      (perm s 0 = 1 ∧ perm s 1 = 0) := by decide +kernel
  have promiseMove (s : Fin 8) (x : Fin 10 → Bool) (h : promise x) : promise (x ∘ perm s) := by
    rcases fixesPair s with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;>
      simpa only [promise, Function.comp_apply, h0, h1, Bool.and_comm] using h
  have targetMove (s : Fin 8) (x : Fin 10 → Bool) : target (x ∘ perm s) = target x := by
    apply Bool.decide_congr
    constructor
    · rintro ⟨i,j,hi,hj,he⟩
      exact ⟨perm s i,perm s j,hi,hj,(keepsEdge s i j).trans he⟩
    · rintro ⟨i,j,hi,hj,he⟩
      obtain ⟨a,rfl⟩ := onto s i
      obtain ⟨b,rfl⟩ := onto s j
      exact ⟨a,b,hi,hj,(keepsEdge s a b).symm.trans he⟩
  let pairRep (i j : Fin 10) : Prop := 10 * i.val + j.val ∈ ([1,2,3,4,23,24,26,28,37,38] : List ℕ)
  have oneOrbit : ∀ i : Fin 10, ∃ s : Fin 8, (perm s i).val ∈ ([0,2,3] : List ℕ) := by decide +kernel
  have twoOrbit : ∀ i j : Fin 10, i ≠ j → ∃ s : Fin 8,
      10 * (perm s i).val + (perm s j).val ∈ ([1,2,3,4,23,24,26,28,37,38] : List ℕ) ∨
      10 * (perm s j).val + (perm s i).val ∈ ([1,2,3,4,23,24,26,28,37,38] : List ℕ) := by decide +kernel
  -- Adapted from Outside/R_meta_1795_2.lean.
  have transport (D : Circuit) (ρ : Fin 10 → Fin 10) (hf : FanInTwo D) :
      ∃ E : Circuit, FanInTwo E ∧ E.size = D.size ∧
        ∀ (x : Fin 10 → Bool) (b : Bool),
          E.eval (List.ofFn x ++ [b]) = D.eval (List.ofFn (x ∘ ρ) ++ [b]) := by
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let run (gs : List Gate) (w : List Bool) := gs.foldl step w
    let extendIndex (ρ : Fin 10 → Fin 10) (i : ℕ) : ℕ :=
      if h : i < 10 then (ρ ⟨i,h⟩).val else i
    have moveOld (ρ : Fin 10 → Fin 10) (i : ℕ) (h : ¬i<10) :
        extendIndex ρ i = i := dite_eq_right h
    let renameGate (ρ : Fin 10 → Fin 10) (g : Gate) : Gate :=
      ⟨g.op,g.inputs.map (extendIndex ρ)⟩
    let rename (ρ : Fin 10 → Fin 10) (D : Circuit) : Circuit :=
      ⟨D.gates.map (renameGate ρ),extendIndex ρ D.output⟩
    have renamedFan (ρ : Fin 10 → Fin 10) (D : Circuit) (h : FanInTwo D) :
        FanInTwo (rename ρ D) := by
      intro g hg
      obtain ⟨g0,hm,rfl⟩ := List.mem_map.mp hg
      exact ⟨(h g0 hm).1, by simpa [renameGate] using (h g0 hm).2⟩
    let related (ρ : Fin 10 → Fin 10) (w v : List Bool) :=
      w.length = v.length ∧ 10 ≤ w.length ∧ ∀ i, w.getD i false = v.getD (extendIndex ρ i) false
    have preserved (ρ : Fin 10 → Fin 10) (w v : List Bool) (b : Bool)
        (h : related ρ w v) : related ρ (w++[b]) (v++[b]) := by
      obtain ⟨eq,hl,read⟩ := h
      refine ⟨by simp [eq], by simp; omega, fun i => ?_⟩
      by_cases small : i < 10
      · have bound : extendIndex ρ i < 10 := by simp [extendIndex,small]
        rw [List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)]
        exact read i
      · rw [moveOld ρ i small]
        by_cases inPrefix : i < w.length
        · rw [List.getD_append _ _ _ _ inPrefix,List.getD_append _ _ _ _ (by omega)]
          simpa only [moveOld ρ i small] using read i
        · rw [List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega),eq]
    have runRelated (ρ : Fin 10 → Fin 10) (gs : List Gate) (w v : List Bool) (h : related ρ w v) :
        related ρ (run gs w) (run (gs.map (renameGate ρ)) v) := by
      induction gs generalizing w v with
      | nil => exact h
      | cons g gs ih =>
        change related ρ (run gs (step w g)) (run (gs.map (renameGate ρ)) (step v (renameGate ρ g)))
        apply ih
        have inputsEq : (g.inputs.map fun i => w.getD i false) =
            ((renameGate ρ g).inputs.map fun i => v.getD i false) := by
          change _ = (g.inputs.map (extendIndex ρ)).map (fun i => v.getD i false)
          rw [List.map_map]
          exact List.map_congr_left (fun i _ => h.2.2 i)
        unfold step
        rw [inputsEq]
        exact preserved ρ w v _ h
    have inputRelated (ρ : Fin 10 → Fin 10) (x : Fin 10 → Bool) (e : List Bool) :
        related ρ (List.ofFn (x ∘ ρ) ++ e) (List.ofFn x ++ e) := by
      refine ⟨by simp, by simp, fun i => ?_⟩
      by_cases hi : i < 10
      · let t : Fin 10 := ⟨i,hi⟩
        have bound : extendIndex ρ i < 10 := by simp [extendIndex,hi]
        rw [List.getD_append _ _ _ _ (by simpa using hi),
          List.getD_append _ _ _ _ (by simpa using bound)]
        have get (y : Fin 10 → Bool) (k : Fin 10) : (List.ofFn y).getD k.val false = y k := by
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        change (List.ofFn (x ∘ ρ)).getD t.val false = (List.ofFn x).getD (extendIndex ρ i) false
        rw [get]
        simp only [extendIndex,dite_eq_left hi]
        exact (get x (ρ t)).symm
      · rw [moveOld ρ i hi, List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
        simp only [List.length_ofFn]
    refine ⟨rename ρ D, renamedFan ρ D hf, ?_, ?_⟩
    · change (D.gates.map (renameGate ρ)).length = D.gates.length
      simp only [List.length_map]
    · intro x b
      exact ((runRelated ρ D.gates _ _ (inputRelated ρ x [b])).2.2 D.output).symm

  -- Adapted from Outside/R_meta_1795_2.lean.
  have bounded (D : Circuit) (hf : FanInTwo D) (hs : D.size ≤ 16) :
      ∃ E : Circuit, FanInTwo E ∧ E.size ≤ 16 ∧
        (∀ g ∈ E.gates, ∀ i ∈ g.inputs, i ≤ 27) ∧ E.output ≤ 27 ∧
        ∀ (x : Fin 10 → Bool) (b : Bool),
          E.eval (List.ofFn x ++ [b]) = D.eval (List.ofFn x ++ [b]) := by
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let run (gs : List Gate) (w : List Bool) := gs.foldl step w
    have lengthRun (gs : List Gate) (w : List Bool) :
        (run gs w).length = w.length+gs.length := by
      induction gs generalizing w with
      | nil => simp [run]
      | cons g gs ih =>
        change (run gs (step w g)).length = _
        rw [ih]
        simp [step]
        omega
    let clip (i : ℕ) := min i 27
    let clipGate (g : Gate) : Gate := ⟨g.op,g.inputs.map clip⟩
    let clipped (D : Circuit) : Circuit := ⟨D.gates.map clipGate,clip D.output⟩
    have clipRead (w : List Bool) (hw : w.length ≤ 27) (i : ℕ) :
        w.getD (clip i) false = w.getD i false := by
      change w.getD (min i 27) false = _
      by_cases h : i ≤ 27
      · rw [min_eq_left h]
      · rw [min_eq_right (by omega : 27 ≤ i),List.getD_eq_default _ false hw,
          List.getD_eq_default _ false (by omega : w.length ≤ i)]
    have clipRun (gs : List Gate) (w : List Bool) (hw : w.length+gs.length ≤ 27) :
        run (gs.map clipGate) w = run gs w := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change run (gs.map clipGate) (step w (clipGate g)) = run gs (step w g)
        have same : step w (clipGate g) = step w g := by
          simp only [step,clipGate,List.map_map,Function.comp_def,clipRead w (by omega)]
        rw [same]
        apply ih
        simp only [List.length_cons] at hw
        simp [step]
        omega
    have clipEval (D : Circuit) (w : List Bool) (h : D.size ≤ 16) (hw : w.length = 11) :
        (clipped D).eval w = D.eval w := by
      change D.gates.length ≤ 16 at h
      change (run (D.gates.map clipGate) w).getD (clip D.output) false =
        (run D.gates w).getD D.output false
      rw [clipRun _ _ (by omega),clipRead _ (by rw [lengthRun]; omega)]
    have clippedFan (D : Circuit) (h : FanInTwo D) : FanInTwo (clipped D) := by
      intro g hg
      obtain ⟨g0,hm,rfl⟩ := List.mem_map.mp hg
      exact ⟨(h g0 hm).1, by simpa [clipGate] using (h g0 hm).2⟩
    have clippedSize (D : Circuit) (h : D.size ≤ 16) : (clipped D).size ≤ 16 := by
      change (D.gates.map clipGate).length ≤ 16
      rwa [List.length_map]
    have clippedInputs (D : Circuit) : ∀ g ∈ (clipped D).gates, ∀ i ∈ g.inputs, i ≤ 27 := by
      intro g hg i hi
      obtain ⟨g0,hm,rfl⟩ := List.mem_map.mp hg
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
      exact min_le_right a 27
    have clippedOut (D : Circuit) : (clipped D).output ≤ 27 := min_le_right _ 27
    refine ⟨clipped D, clippedFan D hf, clippedSize D hs,
      clippedInputs D, clippedOut D, ?_⟩
    intro x b
    exact clipEval D _ hs (by simp)


  have unaryCase (i : Fin 10) (f : Bool → Bool) (rep : i.val ∈ ([0,2,3] : List ℕ))
      (D : Circuit) (hf : FanInTwo D) (hs : D.size ≤ 16) : wrong D (fun x => f (x i)) := by
    obtain ⟨E,fanE,sizeE,pins,out,evalE⟩ := bounded D hf hs
    obtain ⟨x,hx,bad⟩ := unary i f rep E fanE sizeE pins out
    exact ⟨x,hx,fun eq => bad ((evalE x (f (x i))).trans eq)⟩
  have pull (D : Circuit) (fanD : FanInTwo D) (sizeD : D.size ≤ 16) (s : Fin 8)
      (seed repSeed : (Fin 10 → Bool) → Bool) (same : ∀ x, seed (x ∘ perm s) = repSeed x)
      (cert : ∀ E : Circuit, FanInTwo E → E.size ≤ 16 → wrong E repSeed) : wrong D seed := by
    obtain ⟨E, fanE, sizeE, evalE⟩ := transport D (perm s) fanD
    obtain ⟨x, hx, bad⟩ := cert E fanE (sizeE.trans_le sizeD)
    refine ⟨x ∘ perm s, promiseMove s x hx, ?_⟩
    rw [same x, targetMove s x, ← evalE x (repSeed x)]
    exact bad
  have allUnary (D : Circuit) (hf : FanInTwo D) (hs : D.size ≤ 16) (i : Fin 10)
      (f : Bool → Bool) : wrong D (fun x => f (x i)) := by
    obtain ⟨s, rep⟩ := oneOrbit i
    exact pull D hf hs s _ (fun x => f (x (perm s i))) (fun _ => rfl) (unaryCase (perm s i) f rep)
  let join (isOr u v : Bool) := if isOr then u || v else u && v
  have depends (D : Circuit) (i : Fin 10) (x y : Fin 10 → Bool) (b : Bool)
      (same : ∀ k : Fin 10, k ≠ i → x k = y k)
      (different : D.eval (List.ofFn x ++ [b]) ≠ D.eval (List.ofFn y ++ [b])) :
      D.output = i.val ∨ ∃ g ∈ D.gates, i.val ∈ g.inputs := by
    classical
    by_contra h
    have hout : D.output ≠ i.val := by
      intro eq
      exact h (Or.inl eq)
    have hread : ∀ g ∈ D.gates, i.val ∉ g.inputs := by
      intro g hg hi
      exact h (Or.inr ⟨g, hg, hi⟩)
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
    let run (gs : List Gate) (w : List Bool) := gs.foldl step w
    let related (w v : List Bool) :=
      w.length = v.length ∧ i.val < w.length ∧
        ∀ j, j ≠ i.val → w.getD j false = v.getD j false
    have preserved (w v : List Bool) (c : Bool) (h : related w v) :
        related (w ++ [c]) (v ++ [c]) := by
      obtain ⟨heq, hlen, hsame⟩ := h
      refine ⟨by simp [heq], by simp; omega, fun j hj => ?_⟩
      by_cases hjw : j < w.length
      · rw [List.getD_append _ _ _ _ hjw, List.getD_append _ _ _ _ (by omega)]
        exact hsame j hj
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), heq]
    have runRelated (gs : List Gate) (w v : List Bool)
        (h : related w v) (hr : ∀ g ∈ gs, i.val ∉ g.inputs) :
        related (run gs w) (run gs v) := by
      induction gs generalizing w v with
      | nil => exact h
      | cons g gs ih =>
        change related (run gs (step w g)) (run gs (step v g))
        apply ih
        · have inputsEq : (g.inputs.map fun j => w.getD j false) =
              (g.inputs.map fun j => v.getD j false) := by
            apply List.map_congr_left
            intro j hj
            apply h.2.2
            intro eq
            apply hr g (by simp)
            simpa [eq] using hj
          unfold step
          rw [inputsEq]
          exact preserved w v _ h
        · intro g' hg'
          exact hr g' (by simp [hg'])
    have inputRelated : related (List.ofFn x ++ [b]) (List.ofFn y ++ [b]) := by
      refine ⟨by simp, by simp; omega, fun j hj => ?_⟩
      by_cases small : j < 10
      · rw [List.getD_append _ _ _ _ (by simpa using small),
          List.getD_append _ _ _ _ (by simpa using small)]
        have get (z : Fin 10 → Bool) (k : Fin 10) :
            (List.ofFn z).getD k.val false = z k := by
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        let k : Fin 10 := ⟨j, small⟩
        change (List.ofFn x).getD k.val false = (List.ofFn y).getD k.val false
        rw [get, get]
        apply same
        intro eq
        apply hj
        exact congrArg Fin.val eq
      · rw [List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
        simp only [List.length_ofFn]
    exact different ((runRelated D.gates _ _ inputRelated hread).2.2 D.output hout)

  have sensitive (a b : Fin 10) (op : Bool) (hab : a ≠ b)
      (ordinary : a.val + b.val ≠ 1) :
      ∃ x y : Fin 10 → Bool, promise x ∧ promise y ∧ target x ≠ target y ∧
        (∀ k : Fin 10, k ≠ a → x k = y k) ∧ x b = op ∧ y b = op := by
    let third (a b : Fin 10) (op : Bool) : Nat :=
      (((if op then
        [[10,10,4,5,2,2,4,4,4,5],
         [10,10,2,6,2,2,2,6,2,2],
         [3,1,10,0,1,1,3,0,1,1],
         [2,4,0,10,1,2,2,4,0,2],
         [0,3,0,0,10,3,0,0,0,0],
         [0,7,0,0,7,10,0,0,0,0],
         [8,1,8,1,1,1,10,1,0,0],
         [2,5,0,5,2,1,2,10,2,0],
         [3,3,5,0,5,1,0,3,10,3],
         [6,4,4,6,1,4,0,0,4,10]]
       else
        [[10,10,4,4,5,4,4,4,4,4],
         [10,10,6,2,2,2,2,2,2,2],
         [1,3,10,1,1,1,1,1,1,1],
         [2,2,4,10,2,2,2,2,2,2],
         [3,0,0,0,10,0,0,0,0,0],
         [7,0,0,0,0,10,0,0,0,0],
         [1,8,1,1,1,1,10,1,1,1],
         [2,2,5,2,2,2,2,10,2,2],
         [3,3,3,5,3,3,3,3,10,3],
         [4,4,4,4,6,4,4,4,4,10]]
       ) : List (List Nat)).getD a.val []).getD b.val 10
    let before (a b : Fin 10) (op : Bool) (i : Fin 10) : Bool :=
      decide (i.val = third a b op ∨ (op = true ∧ i = b))
    let after (a b : Fin 10) (op : Bool) (i : Fin 10) : Bool :=
      decide (i = a ∨ i.val = third a b op ∨ (op = true ∧ i = b))
    have checked : ∀ (a b : Fin 10) (op : Bool), a ≠ b → a.val + b.val ≠ 1 →
        promise (before a b op) ∧ promise (after a b op) ∧
          target (before a b op) ≠ target (after a b op) ∧
          before a b op b = op ∧ after a b op b = op := by
      decide +kernel
    obtain ⟨hx,hy,ht,hb,hb'⟩ := checked a b op hab ordinary
    refine ⟨before a b op, after a b op, hx, hy, ht, ?_, hb, hb'⟩
    intro k hk
    simp [before, after, hk]

  have selectorRead (D : Circuit)
      (correct : ∀ x, promise x → D.eval (List.ofFn x ++ [x 0 || x 1]) = target x) :
      (D.output = 0 ∨ ∃ g ∈ D.gates, 0 ∈ g.inputs) ∨
        (D.output = 1 ∨ ∃ g ∈ D.gates, 1 ∈ g.inputs) := by
    let x : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 4)
    let z : Fin 10 → Bool := fun i => decide (i = 4)
    let y : Fin 10 → Bool := fun i => decide (i = 1 ∨ i = 4)
    have px : promise x := by decide +kernel
    have py : promise y := by decide +kernel
    have sx : (x 0 || x 1) = true := by decide +kernel
    have sy : (y 0 || y 1) = true := by decide +kernel
    have targets : target x ≠ target y := by decide +kernel
    have different : D.eval (List.ofFn x ++ [true]) ≠ D.eval (List.ofFn y ++ [true]) := by
      have ex := correct x px
      have ey := correct y py
      rw [sx] at ex
      rw [sy] at ey
      rw [ex, ey]
      exact targets
    have same0 : ∀ k : Fin 10, k ≠ 0 → x k = z k := by decide +kernel
    have same1 : ∀ k : Fin 10, k ≠ 1 → z k = y k := by decide +kernel
    by_cases hxz : D.eval (List.ofFn x ++ [true]) ≠ D.eval (List.ofFn z ++ [true])
    · exact Or.inl (depends D 0 x z true same0 hxz)
    · apply Or.inr
      apply depends D 1 z y true same1
      intro hzy
      apply different
      exact (not_not.mp hxz).trans hzy

  have mustRead (D : Circuit) (a b : Fin 10) (op : Bool) (distinct : a ≠ b)
      (ordinary : a.val + b.val ≠ 1) (seed : (Fin 10 → Bool) → Bool)
      (masked : ∀ x, x b = op → seed x = op)
      (correct : ∀ x, promise x → D.eval (List.ofFn x ++ [seed x]) = target x) :
      D.output = a.val ∨ ∃ g ∈ D.gates, a.val ∈ g.inputs := by
    obtain ⟨x,y,px,py,diff,same,bx,by'⟩ := sensitive a b op distinct ordinary
    have ex := correct x px
    have ey := correct y py
    rw [masked x bx] at ex
    rw [masked y by'] at ey
    exact depends D a x y op same (fun he => diff (ex.symm.trans (he.trans ey)))
  have pairDistinct : ∀ a b : Fin 10, 10 * a.val + b.val ∈
      ([1,2,3,4,23,24,26,28,37,38] : List ℕ) → a ≠ b := by decide +kernel
  have constrained (a b : Fin 10) (rep : pairRep a b) (op : Bool)
      (allowed : op = true ∨ 10 * a.val + b.val ≠ 1)
      (E : Circuit) (hf : FanInTwo E) (hs : E.size ≤ 16) :
      wrong E (fun x => join op (x a) (x b)) := by
    obtain ⟨F,fanF,sizeF,pins,out,evalF⟩ := bounded E hf hs
    suffices failed : wrong F (fun x => join op (x a) (x b)) by
      obtain ⟨x,hx,bad⟩ := failed
      exact ⟨x,hx,fun eq => bad ((evalF x (join op (x a) (x b))).trans eq)⟩
    by_contra no
    have correct (x : Fin 10 → Bool) (hx : promise x) :
        F.eval (List.ofFn x ++ [join op (x a) (x b)]) = target x := by
      by_contra bad
      exact no ⟨x,hx,bad⟩
    apply no
    apply binary a b op rep allowed F fanF sizeF pins out
    · intro ordinary
      have ne := pairDistinct a b rep
      constructor
      · apply mustRead F a b op ne ordinary (fun x => join op (x a) (x b)) _ correct
        intro x h
        rw [h]
        cases op <;> simp [join]
      · apply mustRead F b a op ne.symm (by omega) (fun x => join op (x a) (x b)) _ correct
        intro x h
        rw [h]
        cases op <;> simp [join]
    · intro code
      have ha : a = 0 := Fin.ext (by change a.val = 0; omega)
      have hb : b = 1 := Fin.ext (by change b.val = 1; omega)
      have ho : op = true := allowed.resolve_right (fun h => h code)
      subst a
      subst b
      subst op
      exact selectorRead F correct
  have canonicalPair (a b : Fin 10) (rep : pairRep a b) (op : Bool)
      (E : Circuit) (hf : FanInTwo E) (hs : E.size ≤ 16) : wrong E (fun x => join op (x a) (x b)) := by
    cases op with
    | true => exact constrained a b rep true (Or.inl rfl) E hf hs
    | false =>
      by_cases edge01 : 10 * a.val + b.val = 1
      · have ha : a = 0 := Fin.ext (by change a.val = 0; omega)
        have hb : b = 1 := Fin.ext (by change b.val = 1; omega)
        obtain ⟨x,hx,bad⟩ := unaryCase 0 (fun _ => false) (by decide) E hf hs
        refine ⟨x,hx,?_⟩
        change E.eval (List.ofFn x ++ [x a && x b]) ≠ target x
        rw [ha,hb,hx]
        exact bad
      · exact constrained a b rep false (Or.inr edge01) E hf hs
  have allBinary (D : Circuit) (hf : FanInTwo D) (hs : D.size ≤ 16)
      (a b : Fin 10) (h : a ≠ b) (op : Bool) : wrong D (fun x => join op (x a) (x b)) := by
    obtain ⟨s,ordered | reversed⟩ := twoOrbit a b h
    · exact pull D hf hs s _ _ (fun _ => rfl) (canonicalPair (perm s a) (perm s b) ordered op)
    · apply pull D hf hs s _ _ _ (canonicalPair (perm s b) (perm s a) reversed op)
      intro x
      change join op (x (perm s a)) (x (perm s b)) = join op (x (perm s b)) (x (perm s a))
      cases op <;> simp [join, Bool.or_comm, Bool.and_comm]
  have classify (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      (∃ (i : Fin 10) (f : Bool → Bool), ∀ x : Fin 10 → Bool,
        g.op.eval (g.inputs.map fun k => (List.ofFn x).getD k false) = f (x i)) ∨
      (∃ (i j : Fin 10) (op : Bool), i ≠ j ∧ ∀ x : Fin 10 → Bool,
        g.op.eval (g.inputs.map fun k => (List.ofFn x).getD k false) =
          (if op then x i || x j else x i && x j)) := by
    have andTwo (u v : Bool) : GateOp.and.eval [u,v] = (u && v) := by
      cases u <;> cases v <;> rfl
    have orTwo (u v : Bool) : GateOp.or.eval [u,v] = (u || v) := by
      cases u <;> cases v <;> rfl
    have valid (k : Nat) (h : k < 10) (x : Fin 10 → Bool) :
        (List.ofFn x).getD k false = x ⟨k, h⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [h]
    have invalid (k : Nat) (h : ¬ k < 10) (x : Fin 10 → Bool) :
        (List.ofFn x).getD k false = false := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [h]
    rcases g with ⟨o, l⟩
    simp only at hg ⊢
    cases l with
    | nil =>
      left
      exact ⟨0, fun _ => o.eval [], by intro x; rfl⟩
    | cons a tail =>
      cases tail with
      | nil =>
        by_cases ha : a < 10
        · left
          refine ⟨⟨a, ha⟩, fun b => o.eval [b], ?_⟩
          intro x
          simp only [List.map_cons, List.map_nil, valid a ha x]
        · left
          refine ⟨0, fun _ => o.eval [false], ?_⟩
          intro x
          simp only [List.map_cons, List.map_nil, invalid a ha x]
      | cons b tail =>
        cases tail with
        | cons c tail => simp at hg
        | nil =>
          by_cases ha : a < 10
          · by_cases hb : b < 10
            · by_cases hab : a = b
              · subst b
                left
                refine ⟨⟨a, ha⟩, fun z => o.eval [z, z], ?_⟩
                intro x
                simp only [List.map_cons, List.map_nil, valid a ha x]
              · cases o with
                | and =>
                  right
                  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, false, ?_, ?_⟩
                  · intro he
                    exact hab (congrArg Fin.val he)
                  · intro x
                    simp only [List.map_cons, List.map_nil, valid a ha x, valid b hb x]
                    exact andTwo _ _
                | or =>
                  right
                  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, true, ?_, ?_⟩
                  · intro he
                    exact hab (congrArg Fin.val he)
                  · intro x
                    simp only [List.map_cons, List.map_nil, valid a ha x, valid b hb x]
                    exact orTwo _ _
                | not =>
                  left
                  refine ⟨⟨a, ha⟩, fun z => !z, ?_⟩
                  intro x
                  simp only [List.map_cons, List.map_nil, valid a ha x]
                  rfl
                | mod m => simp at hg
                | maj => simp at hg
            · left
              refine ⟨⟨a, ha⟩, fun z => o.eval [z, false], ?_⟩
              intro x
              simp only [List.map_cons, List.map_nil, valid a ha x, invalid b hb x]
          · by_cases hb : b < 10
            · left
              refine ⟨⟨b, hb⟩, fun z => o.eval [false, z], ?_⟩
              intro x
              simp only [List.map_cons, List.map_nil, invalid a ha x, valid b hb x]
            · left
              refine ⟨0, fun _ => o.eval [false, false], ?_⟩
              intro x
              simp only [List.map_cons, List.map_nil, invalid a ha x, invalid b hb x]


  have allSeeds (D : Circuit) (hfan : FanInTwo D) (hs : D.size ≤ 16) (g : Gate)
      (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      wrong D (fun x => g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)) := by
    rcases classify g hg with ⟨i,f,shape⟩ | ⟨i,j,op,ne,shape⟩
    · obtain ⟨x,hx,err⟩ := allUnary D hfan hs i f
      refine ⟨x,hx,?_⟩
      change D.eval (List.ofFn x ++ [g.op.eval (g.inputs.map fun k => (List.ofFn x).getD k false)]) ≠ target x
      rw [shape x]
      exact err
    · obtain ⟨x,hx,err⟩ := allBinary D hfan hs i j ne op
      refine ⟨x,hx,?_⟩
      change D.eval (List.ofFn x ++ [g.op.eval (g.inputs.map fun k => (List.ofFn x).getD k false)]) ≠ target x
      rw [shape x]
      exact err
  have failure : ∃ x, promise x ∧ C.eval (List.ofFn x) ≠ target x := by
    rcases C with ⟨gs, out⟩
    cases gs with
    | nil =>
      let x (i : Fin 10) := decide (i.val = 2 ∨ i.val = 3)
      let y (i : Fin 10) := decide (i.val = 6 ∨ i.val = 8)
      have px : promise x := by decide
      have py : promise y := by decide
      have tx : target x = true := by decide
      have ty : target y = true := by decide
      have disjoint : ∀ i : Fin 10, x i = false ∨ y i = false := by decide
      by_cases ho : out < 10
      · have read (z : Fin 10 → Bool) : (Circuit.mk [] out).eval (List.ofFn z) = z ⟨out,ho⟩ := by
          change (List.ofFn z).getD out false = _
          rw [List.getD_eq_getElem _ _ (by simpa using ho), List.getElem_ofFn]
        rcases disjoint ⟨out,ho⟩ with hx | hy
        · exact ⟨x,px,by rw [read,hx,tx]; decide⟩
        · exact ⟨y,py,by rw [read,hy,ty]; decide⟩
      · refine ⟨x,px,?_⟩
        change (List.ofFn x).getD out false ≠ target x
        rw [List.getD_eq_default _ _ (by simp; omega),tx]
        decide
    | cons g gs =>
      let D : Circuit := ⟨gs, out⟩
      have fanD : FanInTwo D := by
        intro z hz
        exact fan z (by simp [D] at hz ⊢; exact Or.inr hz)
      have sizeD : D.size ≤ 16 := by
        change gs.length + 1 ≤ 17 at budget
        change gs.length ≤ 16
        omega
      have hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
        fan g (by simp)
      obtain ⟨x, hx, hw⟩ := allSeeds D fanD sizeD g hg
      refine ⟨x, hx, ?_⟩
      exact hw


  have same : ∀ x : Fin 10 → Bool, target x = (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x := by decide +kernel
  obtain ⟨x,hx,bad⟩ := failure
  exact ⟨x,hx,fun eq => bad (eq.trans (same x).symm)⟩
