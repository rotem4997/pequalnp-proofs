import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_7101_642
    (ha :
      let V := Fin 26
      let es : List (V × V) := [(0,18), (1,18), (4,18), (13,18), (14,18), (2,19), (3,19), (6,19), (14,19), (16,19), (3,20), (4,20), (7,20), (15,20), (17,20), (0,21), (5,21), (6,21), (9,21), (17,21), (0,22), (2,22), (7,22), (8,22), (11,22), (1,23), (3,23), (8,23), (9,23), (12,23), (3,24), (5,24), (10,24), (11,24), (13,24), (0,25), (10,25), (12,25), (15,25), (16,25)]
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 46 ∧
        ∀ x : V → Bool, C.eval (List.ofFn x) = es.any (fun e => x e.1 && x e.2))
    (hb :
      let V := Fin 26
      let es : List (V × V) := [(0,18), (1,18), (3,18), (13,18), (15,18), (1,19), (2,19), (7,19), (8,19), (11,19), (2,20), (4,20), (9,20), (10,20), (13,20), (3,21), (5,21), (10,21), (11,21), (14,21), (4,22), (6,22), (11,22), (12,22), (15,22), (5,23), (7,23), (12,23), (13,23), (16,23), (6,24), (8,24), (13,24), (14,24), (17,24), (0,25), (9,25), (11,25), (16,25), (17,25)]
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 47 ∧
        ∀ x : V → Bool, C.eval (List.ofFn x) = es.any (fun e => x e.1 && x e.2)) :
  have x1 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x1 x2 : Fin (21 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (21 : ℕ)) ∨ x1 = x2 + (4 : Fin (21 : ℕ)) ∨ x1 = x2 + (14 : Fin (21 : ℕ)) ∨ x1 = x2 + (16 : Fin (21 : ℕ)); have x2 : (Fin (21 : ℕ) → Bool) → Fin (21 : ℕ) → Bool := fun (x2 : Fin (21 : ℕ) → Bool) (x3 : Fin (21 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (21 : ℕ))) || x2 (x3 + (4 : Fin (21 : ℕ))) || x2 (x3 + (14 : Fin (21 : ℕ))) || x2 (x3 + (16 : Fin (21 : ℕ)))); have x3 : List ℕ := [(0 : ℕ), (1 : ℕ), (3 : ℕ), (19 : ℕ), (7 : ℕ), (389 : ℕ), (23 : ℕ), (15 : ℕ), (31 : ℕ), (95 : ℕ), (1369 : ℕ), (1371 : ℕ), (6799 : ℕ), (5501 : ℕ), (54781 : ℕ), (503803 : ℕ), (2097151 : ℕ)]; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x4 ∧     x4.size ≤ (94 : ℕ) ∧       (∀ (x5 x6 : Fin (21 : ℕ)), x1 x5 x6 → ¬x1 (0 : Fin (21 : ℕ)) x6 → x4.eval (List.ofFn fun (x9 : Fin ((21 : ℕ) + (21 : ℕ))) => Fin.addCases (fun (x10 : Fin (21 : ℕ)) => Decidable.decide (x10 = x5)) (fun (x10 : Fin (21 : ℕ)) => Decidable.decide (x10 = x6)) x9) = Bool.true) ∧         ∀ x5 ∈ x3,           ∀ (x7 : Equiv.Perm (Fin (21 : ℕ))),             (∀ (x8 : Fin (21 : ℕ)), ∃ (x9 : Fin (21 : ℕ)), ∀ (x10 : Fin (21 : ℕ)), x1 (x7 x10) x9 ↔ x1 x10 x8) →               have x9 : Fin (21 : ℕ) → Bool := fun (x9 : Fin (21 : ℕ)) => x5.testBit ↑((Equiv.symm x7) x9);               x4.eval (List.ofFn fun (x10 : Fin ((21 : ℕ) + (21 : ℕ))) => Fin.addCases x9 (x2 x9) x10) = Bool.false := by
  let F : Fin 26 → Fin 42 := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 20, 22, 24, 25, 27, 29, 30, 32, 39]
  let G : Fin 26 → Fin 42 := ![2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 23, 31, 33, 34, 35, 36, 37, 40]
  let fa : List (Fin 26 × Fin 26) := [(0,18), (1,18), (4,18), (13,18), (14,18), (2,19), (3,19), (6,19), (14,19), (16,19), (3,20), (4,20), (7,20), (15,20), (17,20), (0,21), (5,21), (6,21), (9,21), (17,21), (0,22), (2,22), (7,22), (8,22), (11,22), (1,23), (3,23), (8,23), (9,23), (12,23), (3,24), (5,24), (10,24), (11,24), (13,24), (0,25), (10,25), (12,25), (15,25), (16,25)]
  let fb : List (Fin 26 × Fin 26) := [(0,18), (1,18), (3,18), (13,18), (15,18), (1,19), (2,19), (7,19), (8,19), (11,19), (2,20), (4,20), (9,20), (10,20), (13,20), (3,21), (5,21), (10,21), (11,21), (14,21), (4,22), (6,22), (11,22), (12,22), (15,22), (5,23), (7,23), (12,23), (13,23), (16,23), (6,24), (8,24), (13,24), (14,24), (17,24), (0,25), (9,25), (11,25), (16,25), (17,25)]
  let incident (p l : Fin 21) : Prop := p = l ∨ p = l+1 ∨ p = l+4 ∨ p = l+14 ∨ p = l+16
  let isFlag (p l : Fin 21) : Bool := decide (p = l ∨ p = l+1 ∨ p = l+4 ∨ p = l+14 ∨ p = l+16)
  have flagEq (p l : Fin 21) : isFlag p l = true ↔ incident p l := by
    simp only [isFlag,incident,decide_eq_true_iff]
  let lf (p : Fin 21) : Fin 42 := Fin.castAdd 21 p
  let rt (p : Fin 21) : Fin 42 := Fin.natAdd 21 p
  let raw (es : List (Fin 26 × Fin 26)) (f : Fin 26 → Fin 42) :=
    es.map (fun e => (f e.1, f e.2))
  let fA := raw fa F
  let fB := raw fb G
  let full : List (Fin 42 × Fin 42) := [(1,22), (2,22), (5,22), (15,22), (17,22), (3,24), (4,24), (7,24), (17,24), (19,24), (4,25), (5,25), (8,25), (18,25), (20,25), (1,27), (6,27), (7,27), (10,27), (20,27), (1,29), (3,29), (8,29), (9,29), (12,29), (2,30), (4,30), (9,30), (10,30), (13,30), (4,32), (6,32), (11,32), (12,32), (15,32), (1,39), (11,39), (13,39), (18,39), (19,39), (2,23), (3,23), (6,23), (16,23), (18,23), (3,31), (5,31), (10,31), (11,31), (14,31), (5,33), (7,33), (12,33), (13,33), (16,33), (6,34), (8,34), (13,34), (14,34), (17,34), (7,35), (9,35), (14,35), (15,35), (18,35), (8,36), (10,36), (15,36), (16,36), (19,36), (9,37), (11,37), (16,37), (17,37), (20,37), (2,40), (12,40), (14,40), (19,40), (20,40)]
  let comp (x : Fin 42 → Bool) (es : List (Fin 42 × Fin 42)) :=
    es.any (fun e => x e.1 && x e.2)
  have part : fA ++ fB = full := by rfl
  have covered : ∀ p l : Fin 21, isFlag p l = true → isFlag 0 l = false →
      (lf p,rt l) ∈ full := by decide +kernel
  have hflags : ∀ p l : Fin 21, incident p l → ¬ incident 0 l → (lf p,rt l) ∈ full := by
    intro p l hp hl
    apply covered p l ((flagEq p l).mpr hp)
    rw [← Bool.not_eq_true,flagEq]
    exact hl
  have sound : ∀ z : Fin 42 × Fin 42, z ∈ full →
      ∃ p l : Fin 21, incident p l ∧ z = (lf p,rt l) := by
    have base : ∀ p l : Fin 21, (lf p,rt l) ∈ full → isFlag p l = true := by decide +kernel
    intro z hz
    have shape : ∀ z : Fin 42 × Fin 42, z ∈ full → z.1.val < 21 ∧ 21 ≤ z.2.val := by decide +kernel
    have hshape := shape z hz
    have b := hshape.2
    let p : Fin 21 := ⟨z.1.val,hshape.1⟩
    let l : Fin 21 := ⟨z.2.val-21,by have := z.2.isLt; omega⟩
    have eq : z = (lf p,rt l) := by
      apply Prod.ext
      · exact Fin.ext rfl
      · apply Fin.ext
        simp only [rt,Fin.val_natAdd,l]
        omega
    exact ⟨p,l,(flagEq p l).mp (base p l (eq ▸ hz)),eq⟩
  obtain ⟨A,hA,nA,evA⟩ := ha
  obtain ⟨B,hB,nB,evB⟩ := hb
  change ∀ x : Fin 26 → Bool, A.eval (List.ofFn x) = fa.any (fun z => x z.1 && x z.2) at evA
  change ∀ x : Fin 26 → Bool, B.eval (List.ofFn x) = fb.any (fun z => x z.1 && x z.2) at evB
  let rho (f : Fin 26 → Fin 42) (m i : Nat) : Nat :=
    if h : i < 26 then (f ⟨i,h⟩).val else 42+m+(i-26)
  let move (f : Fin 26 → Fin 42) (m : Nat) (g : Gate) : Gate :=
    ⟨g.op,g.inputs.map (rho f m)⟩
  let wstep (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have shapeFold (gs : List Gate) (w : List Bool) :
      ∃ t, gs.foldl wstep w = w ++ t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp,by simp⟩
    | cons g gs ih =>
      obtain ⟨t,ht,hl⟩ := ih (wstep w g)
      refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, ?_⟩
      · simpa [wstep,List.append_assoc] using ht
      · simp [hl]
  have snocRead (w : List Bool) (b : Bool) (i : Nat) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    by_cases h : i < w.length
    · rw [List.getD_append _ _ _ _ h,ite_eq_right (by omega)]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases h' : i = w.length
    · simp [h']
    · rw [ite_eq_right h',List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]
  have imageBoundary (f : Fin 26 → Fin 42) (m i n : Nat) :
      rho f m i = 42+m+n ↔ i = 26+n := by
    by_cases hi : i < 26
    · have hr := (f ⟨i,hi⟩).isLt
      simp only [rho,hi,↓reduceDIte]
      omega
    · simp only [rho,hi,↓reduceDIte]
      omega
  have simulate (f : Fin 26 → Fin 42) (m : Nat) (gs : List Gate)
      (n : Nat) (w w' : List Bool) (hw : w.length = 26+n) (hw' : w'.length = 42+m+n)
      (equiv : ∀ i, w'.getD (rho f m i) false = w.getD i false) :
      ∀ i, ((gs.map (move f m)).foldl wstep w').getD (rho f m i) false =
        (gs.foldl wstep w).getD i false := by
    induction gs generalizing n w w' with
    | nil => exact equiv
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      apply ih (n+1)
      · simp [wstep,hw,Nat.add_assoc]
      · simp [wstep,hw',Nat.add_assoc]
      · intro i
        simp only [wstep,move,List.map_map,Function.comp_def]
        have same : g.inputs.map (fun j => w'.getD (rho f m j) false) =
            g.inputs.map (fun j => w.getD j false) := List.map_congr_left fun j _ => equiv j
        rw [same,snocRead,snocRead,hw,hw']
        by_cases hit : i = 26+n
        · rw [ite_eq_left ((imageBoundary f m i n).mpr hit),ite_eq_left hit]
        · rw [ite_eq_right (mt (imageBoundary f m i n).mp hit),ite_eq_right hit,equiv]
  have embedEval (f : Fin 26 → Fin 42) (m : Nat) (C : Circuit) (x : Fin 42 → Bool)
      (prior : List Bool) (hl : prior.length = m) :
      ((C.gates.map (move f m)).foldl wstep (List.ofFn x ++ prior)).getD (rho f m C.output) false =
        C.eval (List.ofFn (x ∘ f)) := by
    apply simulate f m C.gates 0
    · rw [List.length_ofFn]
    · rw [List.length_append,List.length_ofFn,hl]; omega
    intro i
    by_cases hi : i < 26
    · have hj := (f ⟨i,hi⟩).isLt
      simp only [rho,hi,↓reduceDIte]
      rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using hj)]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hj),
        List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
        List.getElem_ofFn,List.getElem_ofFn]
      rfl
    · have h1 : (List.ofFn x ++ prior).length ≤ rho f m i := by
        rw [List.length_append,List.length_ofFn,hl]
        simp only [rho,hi,↓reduceDIte]
        omega
      have h2 : (List.ofFn (x ∘ f)).length ≤ i := by rw [List.length_ofFn]; omega
      rw [List.getD_eq_default _ _ h1,List.getD_eq_default _ _ h2]
  let ga := A.gates.map (move F 0)
  let gb := B.gates.map (move G A.size)
  let output := 42+A.size+B.size
  let outA := if A.output < 26+A.size then rho F 0 A.output else output
  let last : Gate := ⟨.or,[outA,rho G A.size B.output]⟩
  let C : Circuit := ⟨(ga ++ gb) ++ [last],output⟩
  have movedMono (D : Circuit) (hD : Monotone2 D) (f : Fin 26 → Fin 42) (m : Nat)
      (g : Gate) (hg : g ∈ D.gates.map (move f m)) :
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop,hLen⟩ := hD s hs
    exact ⟨hop,by simpa [move] using hLen⟩
  have mono : Monotone2 C := by
    intro g hg
    simp only [C,List.mem_append,List.mem_singleton] at hg
    rcases hg with (h | h) | rfl
    · exact movedMono A hA F 0 g h
    · exact movedMono B hB G A.size g h
    · simp [last]
  have budget : C.size ≤ 94 := by
    change ((ga ++ gb) ++ [last]).length ≤ 94
    simp only [ga,gb,List.length_append,List.length_map,List.length_singleton]
    change A.gates.length ≤ 46 at nA
    change B.gates.length ≤ 47 at nB
    omega
  have circuitsEval (x : Fin 42 → Bool) :
      C.eval (List.ofFn x) = comp x full := by
    let ws := ga.foldl wstep (List.ofFn x)
    let wt := gb.foldl wstep ws
    obtain ⟨ta,ha',hla⟩ := shapeFold ga (List.ofFn x)
    change ws = _ at ha'
    have lenA : ta.length = A.size := by
      change ta.length = A.gates.length
      simpa only [ga,List.length_map] using hla
    obtain ⟨tb,hb',hlb⟩ := shapeFold gb ws
    change wt = _ at hb'
    have lenB : tb.length = B.size := by
      change tb.length = B.gates.length
      simpa only [gb,List.length_map] using hlb
    have lenWs : ws.length = 42+A.size := by
      rw [ha',List.length_append,List.length_ofFn,lenA]
    have lenWt : wt.length = output := by simp [hb',lenWs,lenB,output]
    have evalASaved : wt.getD outA false = A.eval (List.ofFn (x ∘ F)) := by
      by_cases h : A.output < 26+A.size
      · have hs : rho F 0 A.output < ws.length := by
          rw [lenWs]
          by_cases hi : A.output < 26
          · have edge := (F ⟨A.output,hi⟩).isLt
            simp only [rho,hi,↓reduceDIte]
            omega
          · simp only [rho,hi,↓reduceDIte]
            omega
        simp only [outA,h,ite_true]
        rw [hb',List.getD_append _ _ _ _ hs]
        simpa [ws,ga] using embedEval F 0 A x [] rfl
      · have len : (A.wires (List.ofFn (x ∘ F))).length = 26+A.size := by
          obtain ⟨z,hz,hl⟩ := shapeFold A.gates (List.ofFn (x ∘ F))
          change (A.gates.foldl wstep (List.ofFn (x ∘ F))).length = _
          rw [hz,List.length_append,List.length_ofFn,hl]
          rfl
        change wt.getD outA false = (A.wires (List.ofFn (x ∘ F))).getD A.output false
        simp only [outA,h,ite_false]
        rw [List.getD_eq_default _ _ (by omega)]
        exact (List.getD_eq_default _ _ (by omega : (A.wires (List.ofFn (x ∘ F))).length ≤ A.output)).symm
    have evalB : wt.getD (rho G A.size B.output) false = B.eval (List.ofFn (x ∘ G)) := by
      simpa [wt,gb,ha'] using embedEval G A.size B x ta lenA
    change ((((ga ++ gb) ++ [last]).foldl wstep (List.ofFn x)).getD output false) = _
    rw [List.foldl_append,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (wt ++ [last.op.eval (last.inputs.map fun i => wt.getD i false)]).getD output false = _
    rw [snocRead,lenWt,ite_eq_left rfl]
    change GateOp.or.eval [wt.getD outA false,wt.getD (rho G A.size B.output) false] = _
    rw [evalASaved,evalB,evA,evB,← part]
    change ((fa.any (fun e => (x ∘ F) e.1 && (x ∘ F) e.2)) ||
      ((fb.any (fun e => (x ∘ G) e.1 && (x ∘ G) e.2)) || false)) = comp x (fA ++ fB)
    simp only [Bool.or_false,comp,List.any_append,fA,fB,raw,List.any_map,Function.comp_def]
  refine ⟨C,mono,budget,?_,?_⟩
  · intro p l hp hl
    rw [circuitsEval]
    apply List.any_eq_true.mpr
    refine ⟨(lf p,rt l),hflags p l hp hl,?_⟩
    simp only [lf,rt,Fin.addCases_left,Fin.addCases_right]
    simp
  · intro m hm e he
    dsimp only
    rw [circuitsEval,← Bool.not_eq_true]
    intro bad
    obtain ⟨z,hz,hz'⟩ := List.any_eq_true.mp bad
    obtain ⟨p,l,inc,rfl⟩ := sound z hz
    simp only [lf,rt,Fin.addCases_left,Fin.addCases_right,Bool.and_eq_true] at hz'
    rcases inc with rfl | rfl | rfl | rfl | rfl
    all_goals simp [hz'.1] at hz'
