import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Keep one representative from each orbit of the fixed-edge symmetry.
-- Indices above twenty-three can be clipped to twenty-four in the remaining circuit.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_1795_2 :
  (∀ (usesFirst : Bool) (C : Circuit), FanInTwo C → C.size ≤ 13 →
    (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) → C.output ≤ 24 →
    ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 && x 1, if usesFirst then !(x 0 && x 1) else true]) ≠
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  (∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
    (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) → C.output ≤ 24 →
    ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 && x 1, !(x 0)]) ≠
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  (∀ (k : Fin 9), k = 2 ∨ k = 3 → ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
    (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) → C.output ≤ 24 →
    ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 && x 1, !(x k)]) ≠
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  (∀ (k : Fin 9), k = 4 ∨ k = 7 → ∀ (C : Circuit), FanInTwo C → C.size ≤ 13 →
    (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ≤ 24) → C.output ≤ 24 →
    ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 && x 1, !(x k)]) ≠
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
  ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro derived endpoint moreDegreeThree degreeTwo pins _ C fan size
  classical
  let target (x : Fin 9 → Bool) :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let pin (x : Fin 9 → Bool) := x 0 && x 1
  let input (x : Fin 9 → Bool) (b : Bool) := List.ofFn x ++ [pin x,b]
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
  let π : Fin 9 → Fin 9 := ![1,0,5,8,6,2,4,7,3]
  have sameTarget : ∀ x : Fin 9 → Bool, target (x ∘ π) = target x := by
    decide +kernel
  have pinFixed (x : Fin 9 → Bool) : pin (x ∘ π) = pin x := by
    change (x 1 && x 0) = (x 0 && x 1)
    exact Bool.and_comm _ _
  let representative (k : Fin 9) : Prop := k=0 ∨ (k=2 ∨ k=3) ∨ k=4 ∨ k=7
  have orbits : ∀ k, representative k ∨ representative (π k) := by decide
  let extendIndex (ρ : Fin 9 → Fin 9) (i : ℕ) : ℕ :=
    if h : i < 9 then (ρ ⟨i,h⟩).val else i
  have moveOld (ρ : Fin 9 → Fin 9) (i : ℕ) (h : ¬i<9) :
      extendIndex ρ i = i := dite_eq_right h
  let renameGate (ρ : Fin 9 → Fin 9) (g : Gate) : Gate :=
    ⟨g.op,g.inputs.map (extendIndex ρ)⟩
  let rename (ρ : Fin 9 → Fin 9) (D : Circuit) : Circuit :=
    ⟨D.gates.map (renameGate ρ),extendIndex ρ D.output⟩
  have renamedFan (ρ : Fin 9 → Fin 9) (D : Circuit) (h : FanInTwo D) :
      FanInTwo (rename ρ D) := by
    intro g hg
    obtain ⟨g0,hm,rfl⟩ := List.mem_map.mp hg
    exact ⟨(h g0 hm).1, by simpa [renameGate] using (h g0 hm).2⟩
  have renamedSize (ρ : Fin 9 → Fin 9) (D : Circuit) (h : D.size ≤ 13) :
      (rename ρ D).size ≤ 13 := by
    change (D.gates.map (renameGate ρ)).length ≤ 13
    rwa [List.length_map]
  let related (ρ : Fin 9 → Fin 9) (w v : List Bool) :=
    w.length = v.length ∧ 9 ≤ w.length ∧ ∀ i, w.getD i false = v.getD (extendIndex ρ i) false
  have preserved (ρ : Fin 9 → Fin 9) (w v : List Bool) (b : Bool)
      (h : related ρ w v) : related ρ (w++[b]) (v++[b]) := by
    obtain ⟨eq,hl,read⟩ := h
    refine ⟨by simp [eq], by simp; omega, fun i => ?_⟩
    by_cases small : i < 9
    · have bound : extendIndex ρ i < 9 := by simp [extendIndex,small]
      rw [List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)]
      exact read i
    · rw [moveOld ρ i small]
      by_cases inPrefix : i < w.length
      · rw [List.getD_append _ _ _ _ inPrefix,List.getD_append _ _ _ _ (by omega)]
        simpa only [moveOld ρ i small] using read i
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega),eq]
  have runRelated (ρ : Fin 9 → Fin 9) (gs : List Gate) (w v : List Bool) (h : related ρ w v) :
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
  have inputRelated (ρ : Fin 9 → Fin 9) (x : Fin 9 → Bool) (e : List Bool) :
      related ρ (List.ofFn (x ∘ ρ) ++ e) (List.ofFn x ++ e) := by
    refine ⟨by simp, by simp, fun i => ?_⟩
    by_cases hi : i < 9
    · let t : Fin 9 := ⟨i,hi⟩
      have bound : extendIndex ρ i < 9 := by simp [extendIndex,hi]
      rw [List.getD_append _ _ _ _ (by simpa using hi),
        List.getD_append _ _ _ _ (by simpa using bound)]
      have get (y : Fin 9 → Bool) (k : Fin 9) : (List.ofFn y).getD k.val false = y k := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      change (List.ofFn (x ∘ ρ)).getD t.val false = (List.ofFn x).getD (extendIndex ρ i) false
      rw [get]
      simp only [extendIndex,dite_eq_left hi]
      exact (get x (ρ t)).symm
    · rw [moveOld ρ i hi, List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn]
  have moved (D : Circuit) (x : Fin 9 → Bool) (e : List Bool) :
      D.eval (List.ofFn (x ∘ π) ++ e) = (rename π D).eval (List.ofFn x ++ e) := by
    exact (runRelated π D.gates _ _ (inputRelated π x e)).2.2 D.output
  let clip (i : ℕ) := min i 24
  let clipGate (g : Gate) : Gate := ⟨g.op,g.inputs.map clip⟩
  let clipped (D : Circuit) : Circuit := ⟨D.gates.map clipGate,clip D.output⟩
  have clipRead (w : List Bool) (hw : w.length ≤ 24) (i : ℕ) :
      w.getD (clip i) false = w.getD i false := by
    change w.getD (min i 24) false = _
    by_cases h : i ≤ 24
    · rw [min_eq_left h]
    · rw [min_eq_right (by omega : 24 ≤ i),List.getD_eq_default _ false hw,
        List.getD_eq_default _ false (by omega : w.length ≤ i)]
  have clipRun (gs : List Gate) (w : List Bool) (hw : w.length+gs.length ≤ 24) :
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
  have clipEval (D : Circuit) (w : List Bool) (h : D.size ≤ 13) (hw : w.length = 11) :
      (clipped D).eval w = D.eval w := by
    change D.gates.length ≤ 13 at h
    change (run (D.gates.map clipGate) w).getD (clip D.output) false =
      (run D.gates w).getD D.output false
    rw [clipRun _ _ (by omega),clipRead _ (by rw [lengthRun]; omega)]
  have clippedFan (D : Circuit) (h : FanInTwo D) : FanInTwo (clipped D) := by
    intro g hg
    obtain ⟨g0,hm,rfl⟩ := List.mem_map.mp hg
    exact ⟨(h g0 hm).1, by simpa [clipGate] using (h g0 hm).2⟩
  have clippedSize (D : Circuit) (h : D.size ≤ 13) : (clipped D).size ≤ 13 := by
    change (D.gates.map clipGate).length ≤ 13
    rwa [List.length_map]
  have clippedInputs (D : Circuit) : ∀ g ∈ (clipped D).gates, ∀ i ∈ g.inputs, i ≤ 24 := by
    intro g hg i hi
    obtain ⟨g0,hm,rfl⟩ := List.mem_map.mp hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    exact min_le_right a 24
  have clippedOut (D : Circuit) : (clipped D).output ≤ 24 := min_le_right _ 24
  have derivedCase (u : Bool) :
      ∃ x, C.eval (input x (if u then !(pin x) else true)) ≠ target x := by
    obtain ⟨x, bad⟩ := derived u (clipped C) (clippedFan C fan) (clippedSize C size)
      (clippedInputs C) (clippedOut C)
    refine ⟨x, ?_⟩
    change (clipped C).eval (input x (if u then !(pin x) else true)) ≠ target x at bad
    rwa [clipEval C _ size (by simp [input])] at bad
  have representatives (k : Fin 9) (rep : representative k) (D : Circuit)
      (hf : FanInTwo D) (hs : D.size ≤ 13) :
      ∃ x, D.eval (input x (!(x k))) ≠ target x := by
    have h : ∃ x, (clipped D).eval (input x (!(x k))) ≠ target x := by
      rcases rep with rfl | h3 | h2
      · exact endpoint _ (clippedFan D hf) (clippedSize D hs) (clippedInputs D) (clippedOut D)
      · exact moreDegreeThree k h3 _ (clippedFan D hf) (clippedSize D hs)
          (clippedInputs D) (clippedOut D)
      · exact degreeTwo k h2 _ (clippedFan D hf) (clippedSize D hs)
          (clippedInputs D) (clippedOut D)
    obtain ⟨x,h⟩ := h
    refine ⟨x,?_⟩
    rwa [clipEval D _ hs (by simp [input])] at h
  have original (k : Fin 9) : ∃ x, C.eval (input x (!(x k))) ≠ target x := by
    rcases orbits k with direct | mirror
    · exact representatives k direct C fan size
    · obtain ⟨x,h⟩ := representatives (π k) mirror (rename π C)
        (renamedFan π C fan) (renamedSize π C size)
      refine ⟨x ∘ π,?_⟩
      rw [sameTarget,show input (x ∘ π) (!( (x ∘ π) k)) =
        List.ofFn (x ∘ π) ++ [pin x,!(x (π k))] by simp only [input,pinFixed,Function.comp_apply],moved]
      exact h
  cases pins with
  | nil =>
    obtain ⟨x,h⟩ := derivedCase false
    refine ⟨x,?_⟩
    change C.eval ((List.ofFn x ++ [pin x]) ++ [true]) ≠ target x
    rwa [List.append_assoc]
  | cons a rest =>
    let w (x : Fin 9 → Bool) := List.ofFn x ++ [pin x]
    have use (seed : (Fin 9 → Bool) → Bool) (hx : ∀ x, (!((w x).getD a false)) = seed x)
        (h : ∃ x, C.eval (input x (seed x)) ≠ target x) :
        ∃ x : Fin 9 → Bool, C.eval (w x ++ [!((w x).getD a false)]) ≠ target x := by
      obtain ⟨x,err⟩ := h
      refine ⟨x,?_⟩
      rw [hx,show w x ++ [seed x] = input x (seed x) by simp [w,input]]
      exact err
    by_cases ha : a < 9
    · let k : Fin 9 := ⟨a,ha⟩
      apply use (fun x => !(x k)) _ (original k)
      intro x
      have he : (w x).getD a false = x k := by
        simp only [w]
        rw [List.getD_append _ _ _ _ (by simpa using ha),
          List.getD_eq_getElem _ _ (by simpa using ha),List.getElem_ofFn]
      rw [he]
    · by_cases ha9 : a = 9
      · apply use (fun x => !(pin x)) _ (derivedCase true)
        intro x
        change (!((List.ofFn x ++ [pin x]).getD a false)) = _
        rw [ha9,List.getD_append_right _ _ _ _ (by simp),List.length_ofFn,Nat.sub_self]
        rfl
      · apply use (fun _ => true) _ (derivedCase false)
        intro x
        rw [List.getD_eq_default _ _ (by simp [w]; omega)]
        rfl
