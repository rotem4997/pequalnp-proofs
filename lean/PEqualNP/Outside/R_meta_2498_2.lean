import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.R_meta_2498_2
    (hSize : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → 15 ≤ C.size)
    (hClean : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
      (∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) →
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) →
      ∀ j g, C.gates[j]? = some g → (∀ i ∈ g.inputs, i < n + j) ∧ g.inputs.Nodup ∧
        (g.op = GateOp.not → g.inputs.length = 1) ∧ (g.op ≠ GateOp.not → g.inputs.length = 2))
    (hBinary : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →
      13 ≤ C.gates.countP (fun g => g.op.eval [true]))
    (hRemaining : ∀ C : Circuit, IsMinimalCircuit 9 C → C.size = 15 →
      (C.gates[0]? = some ⟨GateOp.or,[0,1]⟩ ∨ C.gates[0]? = some ⟨GateOp.or,[1,0]⟩) →
      (∀ j g, C.gates[j]? = some g → (∀ i ∈ g.inputs, i < 9+j) ∧ g.inputs.Nodup ∧
        (g.op = GateOp.not → g.inputs.length = 1) ∧ (g.op ≠ GateOp.not → g.inputs.length = 2)) →
      C.gates.countP (fun g => g.op.eval [false]) ≤ 2 →
      (∀ v ∈ ([0,1,2,3,5,8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧ (v.val ∈ (gateAt C j).inputs ∨
          ∃ i < j, v.val ∈ (gateAt C i).inputs ∧ ((gateAt C i).op = GateOp.and ∨
            (gateAt C i).op = GateOp.not) ∧ 9+i ∈ (gateAt C j).inputs)) → S.card ≤ 3) →
      circuitFun 9 C ≠ (fun x : Fin 9 → Bool => decide
        (∃ u w : Fin 9, (([34,68,136,272,1,128,256,0,32] : List ℕ).getD u.val 0).testBit w.val =
          true ∧ x u = true ∧ x w = true))) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x1.size ∧ ((∃ (x10 : Bool), ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = x10) ∨ ∃ x10 < (9 : ℕ) + x8, ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = (x1.wires (List.ofFn x11)).getD x10 Bool.false)) → x7.card ≤ (3 : ℕ)) → (16 : ℕ) ≤ x1.size := by
  intro C hFan hFirst hListed hCollapse
  have hFun : circuitFun 9 C = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) := by
    rw [hListed]
    funext x
    simp [List.any,Bool.or_assoc]
  by_contra hSmall
  have hSizeC := hSize C hFan hFun
  have hLenC : C.gates.length = 15 := by
    change ¬16 ≤ C.gates.length at hSmall
    change 15 ≤ C.gates.length at hSizeC
    omega
  have andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have notEval (xs : List Bool) : GateOp.not.eval xs = !xs.headD false := rfl
  let trim (g : Gate) : Gate := if g.op.eval [false] then ⟨g.op, g.inputs.take 1⟩ else g
  let D : Circuit := ⟨C.gates.map trim, C.output⟩
  have trimOp (g : Gate) : (trim g).op = g.op := by
    dsimp only [trim]
    split <;> rfl
  have trimEval (g : Gate) (hg : g ∈ C.gates) (f : ℕ → Bool) :
      (trim g).op.eval ((trim g).inputs.map f) = g.op.eval (g.inputs.map f) := by
    have ho := (hFan g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with ho | ho | ho
    · simp [trim, ho, andEval]
    · simp [trim, ho, orEval]
    · cases h : g.inputs <;> simp [trim, ho, notEval, h]
  have hFanD : FanInTwo D := by
    intro g hg
    change g ∈ C.gates.map trim at hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    refine ⟨by rw [trimOp]; exact (hFan a ha).1, ?_⟩
    dsimp only [trim]
    split
    · simp
    · exact (hFan a ha).2
  have hUnary : ∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1 := by
    intro g hg hn
    change g ∈ C.gates.map trim at hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    rw [trimOp] at hn
    simp [trim, hn, notEval]
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hFold (ls : List Gate) (hls : ∀ g ∈ ls, g ∈ C.gates) :
      ∀ w : List Bool, (ls.map trim).foldl step w = ls.foldl step w := by
    induction ls with
    | nil => intro w; rfl
    | cons g ls ih =>
      intro w
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hstep : step w (trim g) = step w g := by
        dsimp only [step]
        rw [trimEval g (hls g List.mem_cons_self)]
      rw [hstep]
      exact ih (fun a ha => hls a (List.mem_cons_of_mem _ ha)) _
  have hWires (x : List Bool) : D.wires x = C.wires x :=
    hFold C.gates (fun _ h => h) x
  have hFunD : circuitFun 9 D = circuitFun 9 C := by
    funext x
    change (D.wires (List.ofFn x)).getD C.output false = (C.wires (List.ofFn x)).getD C.output false
    rw [hWires]
  have hLenD : D.gates.length = 15 := by simp [D, hLenC]
  have hMin : IsMinimalCircuit 9 D := ⟨hFanD, fun E hE hEq => by
    have hh := hSize E hE (hEq.trans (hFunD.trans hFun))
    change D.gates.length ≤ E.size
    simpa only [hLenD] using hh⟩
  have hNonconst : ∃ x y : Fin 9 → Bool, circuitFun 9 D x ≠ circuitFun 9 D y := by
    rw [hFunD, hFun]
    refine ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), ?_⟩
    decide +kernel
  have hCleanD := hClean 9 D hMin hNonconst hUnary
  have hStable (ls : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
      (ls.foldl step w).getD i false = w.getD i false := by
    induction ls with
    | nil => intro w i hi; rfl
    | cons g ls ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have hZeroLt : 0 < D.gates.length := by omega
  let first := D.gates[0]
  have hFirstGet : D.gates[0]? = some first := List.getElem?_eq_getElem hZeroLt
  have hFirstMem : first ∈ D.gates := List.getElem_mem hZeroLt
  obtain ⟨hRead0, _, hArityNot, hArityBin⟩ := hCleanD 0 first hFirstGet
  have hSplit : D.gates = first :: D.gates.drop 1 := by
    simpa only [List.drop_zero, first] using List.drop_eq_getElem_cons hZeroLt
  have hEvalFirst (x : Fin 9 → Bool) :
      first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 1) := by
    have hOld : (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 1) := by
      rw [hWires]
      exact hFirst x
    change (D.gates.foldl step (List.ofFn x)).getD 9 false = _ at hOld
    rw [hSplit, List.foldl_cons, hStable _ _ _ (by simp [step])] at hOld
    change ((List.ofFn x) ++ [first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false)]).getD 9 false = _ at hOld
    rwa [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn,
      Nat.sub_self, List.getD_cons_zero] at hOld
  have hGet (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) : (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  have hOp0 := (hFanD first hFirstMem).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hOp0
  have hNot0 : first.op ≠ .not := by
    intro hn
    obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp (hArityNot hn)
    have hkr : k < 9 := hRead0 k (by simp [hk])
    have he := hEvalFirst (fun _ => false)
    rw [hn, hk] at he
    simp only [List.map_cons, List.map_nil] at he
    rw [hGet (fun _ => false) k hkr] at he
    change true = false at he
    exact Bool.noConfusion he
  obtain ⟨u, v, huv⟩ := List.length_eq_two.mp (hArityBin hNot0)
  have hu : u < 9 := hRead0 u (by simp [huv])
  have hv : v < 9 := hRead0 v (by simp [huv])
  let e0 : Fin 9 → Bool := fun i => decide (i.val = 0)
  let e1 : Fin 9 → Bool := fun i => decide (i.val = 1)
  have h0 : first.op.eval [decide (u = 0), decide (v = 0)] = true := by
    have he := hEvalFirst e0
    rw [huv] at he
    simp only [List.map_cons, List.map_nil] at he
    rw [hGet e0 u hu, hGet e0 v hv] at he
    exact he
  have h1 : first.op.eval [decide (u = 1), decide (v = 1)] = true := by
    have he := hEvalFirst e1
    rw [huv] at he
    simp only [List.map_cons, List.map_nil] at he
    rw [hGet e1 u hu, hGet e1 v hv] at he
    exact he
  have hFirstOR : first.op = .or := by
    rcases hOp0 with ho | ho | ho
    · exfalso
      have ha : u = 0 ∧ v = 0 := by
        simpa [ho, andEval] using h0
      have hb : u = 1 ∧ v = 1 := by
        simpa [ho, andEval] using h1
      omega
    · exact ho
    · exact False.elim (hNot0 ho)
  have hFirstList : first.inputs = [0,1] ∨ first.inputs = [1,0] := by
    have ha : u = 0 ∨ v = 0 := by
      simpa [hFirstOR, orEval] using h0
    have hb : u = 1 ∨ v = 1 := by
      simpa [hFirstOR, orEval] using h1
    rw [huv]
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · omega
    · exact Or.inl (by rw [ha, hb])
    · exact Or.inr (by rw [ha, hb])
    · omega
  have hFirstShape : D.gates[0]? = some ⟨GateOp.or, [0,1]⟩ ∨
      D.gates[0]? = some ⟨GateOp.or, [1,0]⟩ := by
    rw [hFirstGet]
    rcases hFirstList with h | h
    · left
      apply congrArg some
      calc
        first = ⟨first.op, first.inputs⟩ := rfl
        _ = ⟨GateOp.or, [0,1]⟩ := by rw [hFirstOR, h]
    · right
      apply congrArg some
      calc
        first = ⟨first.op, first.inputs⟩ := rfl
        _ = ⟨GateOp.or, [1,0]⟩ := by rw [hFirstOR, h]
  have hCount (ls : List Gate) (hls : ∀ g ∈ ls, g ∈ D.gates) :
      ls.countP (fun g => g.op.eval [true]) + ls.countP (fun g => g.op.eval [false]) = ls.length := by
    induction ls with
    | nil => rfl
    | cons g ls ih =>
      have ht := ih (fun a ha => hls a (List.mem_cons_of_mem _ ha))
      have ho := (hFanD g (hls g List.mem_cons_self)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
      rcases ho with ho | ho | ho <;> simp [ho, andEval, orEval, notEval] <;> omega
  have hBin := hBinary D hFanD (hFunD.trans hFun)
  have hSum := hCount D.gates (fun _ h => h)
  have hFew : D.gates.countP (fun g => g.op.eval [false]) ≤ 2 := by omega
  have hSizeD : D.size = 15 := hLenD
  let V (x : Fin 9 → Bool) (i : ℕ) := (D.wires (List.ofFn x)).getD i false
  have hvInput (x : Fin 9 → Bool) (v : Fin 9) : V x v.val = x v := by
    change (D.gates.foldl step (List.ofFn x)).getD v.val false = x v
    rw [hStable _ _ _ (by simp),hGet _ _ v.isLt]
  have hRunLength (ls : List Gate) (w : List Bool) :
      (ls.foldl step w).length = w.length + ls.length := by
    induction ls generalizing w with
    | nil => simp
    | cons g ls ih =>
      rw [List.foldl_cons,ih]
      simp [step]
      omega
  have hAt (j : ℕ) (hj : j < D.size) : D.gates[j]? = some (gateAt D j) := by
    change D.gates[j]? = some (D.gates.getD j _)
    rw [List.getD_eq_getElem _ _ hj, List.getElem?_eq_getElem hj]
  have hEval (x : Fin 9 → Bool) (j : ℕ) (hj : j < D.size) :
      V x (9+j) = (gateAt D j).op.eval ((gateAt D j).inputs.map (V x)) := by
    let g := gateAt D j
    let pre := D.gates.take j
    let post := D.gates.drop (j+1)
    let w := pre.foldl step (List.ofFn x)
    have hg : D.gates[j] = g := by
      change _ = D.gates.getD j _
      rw [List.getD_eq_getElem _ _ hj]
    have hsplit : D.gates = pre ++ g :: post := by
      change D.gates = D.gates.take j ++ g :: D.gates.drop (j+1)
      rw [← hg, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
    have hWLen : w.length = 9+j := by
      have hjlen : j ≤ D.gates.length := Nat.le_of_lt hj
      simp [w,pre,hRunLength,hjlen]
    have hV : D.wires (List.ofFn x) = post.foldl step (step w g) := by
      change D.gates.foldl step _ = _
      rw [hsplit,List.foldl_append,List.foldl_cons]
    have hWStep : (step w g).length = 9+j+1 := by simp [step,hWLen]
    have hPrior (i : ℕ) (hi : i < 9+j) : w.getD i false = V x i := by
      have hw : i < w.length := by omega
      change _ = (D.wires (List.ofFn x)).getD _ _
      rw [hV,hStable post (step w g) i (by omega)]
      exact (List.getD_append _ _ _ _ hw).symm
    change (D.wires (List.ofFn x)).getD (9+j) false = g.op.eval (g.inputs.map (V x))
    rw [hV,hStable post (step w g) (9+j) (by omega)]
    change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD (9+j) false = _
    rw [List.getD_append_right _ _ _ _ (by omega), hWLen, Nat.sub_self, List.getD_cons_zero]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hPrior i ((hCleanD j g (hAt j hj)).1 i hi)
  have hAnd2 (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by
    cases a <;> cases b <;> rfl
  have hOr2 (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by
    cases a <;> cases b <;> rfl
  have hNot1 (a : Bool) : GateOp.not.eval [a] = !a := rfl
  have hGateOp (j : ℕ) (hj : j < D.size) :
      (gateAt D j).op = .and ∨ (gateAt D j).op = .or ∨ (gateAt D j).op = .not := by
    have hg := (hFanD _ (List.mem_of_getElem? (hAt j hj))).1
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hg
  let Loses (v : Fin 9) (j : ℕ) :=
    (∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false → V x (9+j) = b) ∨
    (∃ i < 9+j, ∀ x : Fin 9 → Bool, x v = false → V x (9+j) = V x i)
  have hOnConst (v : Fin 9) (j w : ℕ) (hj : j < D.size)
      (hw : w ∈ (gateAt D j).inputs) (b : Bool)
      (hW : ∀ x : Fin 9 → Bool, x v = false → V x w = b) : Loses v j := by
    let g := gateAt D j
    change w ∈ g.inputs at hw
    have hg := hCleanD j g (hAt j hj)
    have hUnary (ho : g.op = .not) : Loses v j := by
      obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp (hg.2.2.1 ho)
      have he : w = a := by simpa [ha] using hw
      refine Or.inl ⟨!b,?_⟩
      intro x hx
      rw [hEval x j hj]
      change g.op.eval (g.inputs.map (V x)) = _
      rw [ho,ha,List.map_cons,List.map_nil,hNot1,← he,hW x hx]
    by_cases ho : g.op = .not
    · exact hUnary ho
    · obtain ⟨a,c,hac⟩ := List.length_eq_two.mp (hg.2.2.2 ho)
      have hChoice : w = a ∨ w = c := by simpa [hac] using hw
      have hOp : g.op = .and ∨ g.op = .or := by
        rcases hGateOp j hj with ha | hb | hc
        · exact Or.inl ha
        · exact Or.inr hb
        · exact False.elim (ho hc)
      obtain ⟨u,hu,hU⟩ : ∃ u < 9+j, ∀ x : Fin 9 → Bool, x v = false →
          V x (9+j) = g.op.eval [b,V x u] := by
        rcases hChoice with h | h
        · refine ⟨c,hg.1 c (by simp [hac]),?_⟩
          intro x hx
          rw [hEval x j hj]
          change g.op.eval (g.inputs.map (V x)) = _
          rw [hac,List.map_cons,List.map_cons,List.map_nil,← h,hW x hx]
        · refine ⟨a,hg.1 a (by simp [hac]),?_⟩
          intro x hx
          rw [hEval x j hj]
          change g.op.eval (g.inputs.map (V x)) = _
          rw [hac,List.map_cons,List.map_cons,List.map_nil,← h,hW x hx]
          rcases hOp with hOp | hOp
          · simpa only [hOp,hAnd2] using Bool.and_comm (V x a) b
          · simpa only [hOp,hOr2] using Bool.or_comm (V x a) b
      rcases hOp with hOp | hOp <;> cases b
      · exact Or.inl ⟨false,fun x hx => by rw [hU x hx,hOp,hAnd2]; rfl⟩
      · exact Or.inr ⟨u,hu,fun x hx => by rw [hU x hx,hOp,hAnd2]; rfl⟩
      · exact Or.inr ⟨u,hu,fun x hx => by rw [hU x hx,hOp,hOr2]; rfl⟩
      · exact Or.inl ⟨true,fun x hx => by rw [hU x hx,hOp,hOr2]; rfl⟩
  have hProducer (v : Fin 9) (i : ℕ) (hi : i < D.size) (hv : v.val ∈ (gateAt D i).inputs)
      (hop : (gateAt D i).op = .and ∨ (gateAt D i).op = .not) :
      ∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false → V x (9+i) = b := by
    let g := gateAt D i
    change v.val ∈ g.inputs at hv
    rcases hop with ha | hn
    · refine ⟨false,?_⟩
      intro x hx
      rw [hEval x i hi,ha,andEval]
      have hm : false ∈ (gateAt D i).inputs.map (V x) := List.mem_map.mpr
        ⟨v.val,hv,(hvInput x v).trans hx⟩
      cases h : ((gateAt D i).inputs.map (V x)).all id
      · rfl
      · exact False.elim (Bool.false_ne_true (List.all_eq_true.mp h false hm))
    · obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp ((hCleanD i g (hAt i hi)).2.2.1 hn)
      have hv' : v.val = a := by simpa [ha] using hv
      refine ⟨true,?_⟩
      intro x hx
      rw [hEval x i hi]
      change g.op.eval (g.inputs.map (V x)) = _
      rw [hn,ha,List.map_cons,List.map_nil,hNot1,← hv',hvInput,hx]
      rfl
  have hDirect : ∀ v ∈ ([0,1,2,3,5,8] : List (Fin 9)), ∀ S : Finset ℕ,
      (∀ j ∈ S, j < D.size ∧ (v.val ∈ (gateAt D j).inputs ∨
        ∃ i < j, v.val ∈ (gateAt D i).inputs ∧ ((gateAt D i).op = GateOp.and ∨
          (gateAt D i).op = GateOp.not) ∧ 9+i ∈ (gateAt D j).inputs)) → S.card ≤ 3 := by
    intro v hv S hS
    apply hCollapse v hv S
    intro j hj
    obtain ⟨hD,hjShape⟩ := hS j hj
    have hLoss : Loses v j := by
      rcases hjShape with h | ⟨i,hi,hvi,hop,hij⟩
      · exact hOnConst v j v.val hD h false (fun x hx => (hvInput x v).trans hx)
      · obtain ⟨b,hb⟩ := hProducer v i (by omega) hvi hop
        exact hOnConst v j (9+i) hD hij b hb
    have hc : j < C.size := by
      change j < C.gates.length
      rw [hLenC]
      omega
    have hVC (x : Fin 9 → Bool) (i : ℕ) :
        V x i = (C.wires (List.ofFn x)).getD i false := by
      change (D.wires (List.ofFn x)).getD i false = _
      rw [hWires]
    refine ⟨hc,?_⟩
    rcases hLoss with ⟨b,hb⟩ | ⟨i,hi,h⟩
    · exact Or.inl ⟨b,fun x hx => (hVC x _).symm.trans (hb x hx)⟩
    · exact Or.inr ⟨i,hi,fun x hx => (hVC x _).symm.trans ((h x hx).trans (hVC x _))⟩
  let masked (x : Fin 9 → Bool) := decide
    (∃ u w : Fin 9, (([34,68,136,272,1,128,256,0,32] : List ℕ).getD u.val 0).testBit w.val =
      true ∧ x u = true ∧ x w = true)
  have hEdge : ∀ u w : Fin 9,
      (([34,68,136,272,1,128,256,0,32] : List ℕ).getD u.val 0).testBit w.val = true ↔
      (u,w) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),
        (5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)) := by decide +kernel
  have hMasked : circuitFun 9 D = masked := by
    rw [hFunD,hListed]
    funext x
    change List.any ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),
      (5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)) (fun e => x e.1 && x e.2) = masked x
    rw [Bool.eq_iff_iff,List.any_eq_true]
    simp only [masked,decide_eq_true_eq,hEdge,Bool.and_eq_true]
    constructor
    · rintro ⟨⟨a,b⟩,hab,ht,hz⟩
      exact ⟨a,b,hab,ht,hz⟩
    · rintro ⟨a,b,hab,ht,hz⟩
      exact ⟨(a,b),hab,ht,hz⟩
  exact hRemaining D hMin hSizeD hFirstShape hCleanD hFew hDirect hMasked
