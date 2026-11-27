import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Moving a gate that reads two input bits to the front preserves all later values.
-- The six first-gate cases are the checked files L_meta_1667 through L_meta_1672.
-- Invalid forward references still read false after the gate indices change.
set_option maxHeartbeats 450000 in
theorem PEqualNP.Outside.R_meta_2159_521
    (andFirst : ∀ (a b : Fin 9), (a.val, b.val) ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (ℕ × ℕ)) →
      ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x a && x b)) →
      circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ D.size)
    (remaining : ∀ C : Circuit, Monotone2 C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      (∀ a b : Fin 9, a ≠ b → (⟨.and, [a.val, b.val]⟩ : Gate) ∉ C.gates) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan noNot first correct
  let f := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨op, len⟩ := fan g hg
    exact ⟨by simpa [noNot g hg] using op, len⟩
  by_cases found : ∃ (a b : Fin 9), a ≠ b ∧ (⟨.and, [a.val, b.val]⟩ : Gate) ∈ C.gates
  · obtain ⟨a, b, ab, mem⟩ := found
    let pivot : Gate := ⟨.and, [a.val, b.val]⟩
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem (show pivot ∈ C.gates from mem)
    let n := 9 + pre.length
    let up (i : ℕ) := if i < 9 then i else i + 1
    let move (i : ℕ) := if i < 9 then i else if i < n then i+1 else if i = n then 9 else i
    let liftG (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let D : Circuit := ⟨pivot :: (pre.map (liftG up) ++ post.map (liftG move)), move C.output⟩
    have sizeD : D.size = C.size := by
      change (pivot :: (pre.map (liftG up) ++ post.map (liftG move))).length = C.gates.length
      simp [hsplit]
      omega
    have fanD : FanInTwo D := by
      intro g hg
      change g ∈ pivot :: (pre.map (liftG up) ++ post.map (liftG move)) at hg
      simp only [List.mem_cons, List.mem_append, List.mem_map] at hg
      rcases hg with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · simp [pivot]
      · simpa [liftG] using fan q (by simp [hsplit, hq])
      · simpa [liftG] using fan q (by simp [hsplit, hq])
    have atBase (xs : List Bool) (lx : xs.length = 9) (ys : List Bool) (k : Fin 9) :
        (xs ++ ys).getD k.val false = xs.getD k.val false :=
      List.getD_append _ _ _ _ (by omega)
    have upRead (xs : List Bool) (lx : xs.length = 9) (bit : Bool) (ys : List Bool) (i : ℕ) :
        (xs ++ bit :: ys).getD (up i) false = (xs ++ ys).getD i false := by
      by_cases hi : i < 9
      · simp only [up, ite_eq_left hi]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      · simp only [up, ite_eq_right hi]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        rw [show i + 1 - xs.length = (i - xs.length) + 1 by omega]
        rfl
    have movedRead (xs : List Bool) (lx : xs.length = 9) (bit : Bool) (ys zs : List Bool)
        (ly : ys.length = pre.length) (i : ℕ) :
        (xs ++ bit :: (ys ++ zs)).getD (move i) false =
        (xs ++ (ys ++ bit :: zs)).getD i false := by
      by_cases hi : i < 9
      · simp only [move, ite_eq_left hi]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      · have hx : xs.length ≤ i := by omega
        by_cases hj : i < n
        · simp only [move, ite_eq_right hi, ite_eq_left hj]
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ hx]
          rw [show i+1-xs.length = (i-xs.length)+1 by omega]
          change (ys ++ zs).getD (i-xs.length) false = _
          rw [List.getD_append _ _ _ _ (by dsimp [n] at hj; omega),
              List.getD_append _ _ _ _ (by dsimp [n] at hj; omega)]
        · by_cases he : i = n
          · subst i
            rw [show move n = 9 by simp [move, hi]]
            rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ hx]
            rw [show 9-xs.length=0 by omega, show n-xs.length=ys.length by dsimp [n]; omega]
            simp
          · simp only [move, ite_eq_right hi, ite_eq_right hj, ite_eq_right he]
            rw [List.getD_append_right _ _ _ _ hx, List.getD_append_right _ _ _ _ hx]
            have hlt : ys.length < i-xs.length := by dsimp [n] at hj he; omega
            rw [show i-xs.length=(i-xs.length-1)+1 by omega]
            change (ys ++ zs).getD (i-xs.length-1) false =
              (ys ++ bit :: zs).getD ((i-xs.length-1)+1) false
            rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
            rw [show i-xs.length-1+1-ys.length=(i-xs.length-1-ys.length)+1 by omega]
            rfl
    have applyMap (r : ℕ → ℕ) (s t : List Bool)
        (eqv : ∀ i, t.getD (r i) false = s.getD i false) (g : Gate) :
        (liftG r g).op.eval ((liftG r g).inputs.map fun i => t.getD i false) =
        g.op.eval (g.inputs.map fun i => s.getD i false) := by
      simp only [liftG, List.map_map, Function.comp_def, eqv]
    have runPrefix (xs : List Bool) (lx : xs.length = 9) (bit : Bool)
        (gs : List Gate) (ys : List Bool) :
        ∃ out : List Bool, out.length = ys.length + gs.length ∧
          gs.foldl step (xs ++ ys) = xs ++ out ∧
          (gs.map (liftG up)).foldl step (xs ++ bit :: ys) = xs ++ bit :: out := by
      induction gs generalizing ys with
      | nil => exact ⟨ys, by simp, rfl, rfl⟩
      | cons g gs ih =>
        let v := g.op.eval (g.inputs.map fun i => (xs ++ ys).getD i false)
        obtain ⟨out, hlen, A, B⟩ := ih (ys ++ [v])
        refine ⟨out, by simp at hlen ⊢; omega, ?_, ?_⟩
        · simpa only [List.foldl_cons, step, List.append_assoc] using A
        · simp only [List.map_cons, List.foldl_cons, step, applyMap up _ _ (upRead xs lx bit ys) g,
            List.append_assoc, List.cons_append]
          exact B
    have runSuffix (xs : List Bool) (lx : xs.length = 9) (bit : Bool) (ys : List Bool)
        (ly : ys.length = pre.length) (gs : List Gate) (zs : List Bool) :
        ∃ out : List Bool,
          gs.foldl step (xs ++ (ys ++ bit :: zs)) = xs ++ (ys ++ bit :: out) ∧
          (gs.map (liftG move)).foldl step (xs ++ bit :: (ys ++ zs)) = xs ++ bit :: (ys ++ out) := by
      induction gs generalizing zs with
      | nil => exact ⟨zs, rfl, rfl⟩
      | cons g gs ih =>
        let v := g.op.eval (g.inputs.map fun i => (xs ++ (ys ++ bit :: zs)).getD i false)
        obtain ⟨out, A, B⟩ := ih (zs ++ [v])
        refine ⟨out, ?_, ?_⟩
        · simpa only [List.foldl_cons, step, List.append_assoc, List.cons_append] using A
        · simp only [List.map_cons, List.foldl_cons, step, applyMap move _ _ (movedRead xs lx bit ys zs ly) g,
            List.append_assoc, List.cons_append]
          exact B
    have sim (x : Fin 9 → Bool) : ∃ ys zs : List Bool, ys.length = pre.length ∧
        C.wires (List.ofFn x) = List.ofFn x ++ (ys ++ (x a && x b) :: zs) ∧
        D.wires (List.ofFn x) = List.ofFn x ++ (x a && x b) :: (ys ++ zs) := by
      let xs := List.ofFn x
      have lx : xs.length = 9 := by simp [xs]
      let bit := x a && x b
      have raw (i : Fin 9) : xs.getD i.val false = x i := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp only [xs, List.getElem_ofFn]
      obtain ⟨ys, ly, P, Q⟩ := runPrefix xs lx bit pre []
      simp only [List.length_nil, Nat.zero_add, List.append_nil] at ly P
      have andValues (v w : Bool) : GateOp.and.eval [v,w] = (v && w) := by
        cases v <;> cases w <;> rfl
      have H (ys : List Bool) : step (xs ++ ys) pivot = xs ++ (ys ++ [bit]) := by
        simp only [step, pivot, List.map_cons, List.map_nil, andValues, atBase xs lx ys, raw, bit, List.append_assoc]
      obtain ⟨zs, A, B⟩ := runSuffix xs lx bit ys ly post []
      refine ⟨ys, zs, ly, ?_, ?_⟩
      · change C.gates.foldl step xs = _
        rw [hsplit, List.foldl_append, P, List.foldl_cons, H]
        exact A
      · change (pivot :: (pre.map (liftG up) ++ post.map (liftG move))).foldl step xs = _
        have H0 := H []
        simp only [List.append_nil, List.nil_append] at H0
        rw [List.foldl_cons, H0, List.foldl_append, Q]
        simpa only [List.append_nil] using B
    have firstD (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x a && x b) := by
      obtain ⟨ys,zs,_,_,hd⟩ := sim x
      rw [hd, List.getD_append_right _ _ _ _ (by simp)]
      simp
    have correctD : circuitFun 9 D = f := by
      funext x
      obtain ⟨ys,zs,ly,hc,hd⟩ := sim x
      have e := movedRead (List.ofFn x) (by simp) (x a && x b) ys zs ly C.output
      change (D.wires (List.ofFn x)).getD (move C.output) false = _
      rw [hd, e, ← hc]
      exact congrFun correct x
    let maps : Fin 12 → Fin 9 → Fin 9 :=
      ![![0,1,2,3,4,5,6,7,8],
        ![1,2,3,8,6,0,7,4,5],
        ![2,3,8,5,7,1,4,6,0],
        ![3,2,1,0,4,8,7,6,5],
        ![2,1,0,5,7,3,6,4,8],
        ![3,8,5,0,4,2,6,7,1],
        ![1,0,5,8,6,2,4,7,3],
        ![8,3,2,1,6,5,4,7,0],
        ![0,5,8,3,4,1,7,6,2],
        ![5,0,1,2,7,8,4,6,3],
        ![5,8,3,2,7,0,6,4,1],
        ![8,5,0,1,6,3,7,4,2]]
    have graphSym (k : Fin 12) (x : Fin 9 → Bool) : f (fun j => x (maps k j)) = f x := by
      fin_cases k <;> dsimp [maps, f] <;> ac_rfl
    have coverPairs : ∀ a b : Fin 9, a ≠ b → ∃ k : Fin 12,
        (min (maps k a).val (maps k b).val, max (maps k a).val (maps k b).val) ∈
          ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (ℕ × ℕ)) := by decide +kernel
    obtain ⟨k, rep⟩ := coverPairs a b ab
    let σ := maps k
    let pin (i : ℕ) := if h : i < 9 then (σ ⟨i,h⟩).val else i
    let E : Circuit := ⟨D.gates.map (liftG pin), pin D.output⟩
    have efan : FanInTwo E := by
      intro g hg
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (show g ∈ D.gates.map (liftG pin) from hg)
      simpa [liftG] using fanD q hq
    have ewire (x : Fin 9 → Bool) (i : ℕ) :
        (E.wires (List.ofFn x)).getD (pin i) false = (D.wires (List.ofFn (fun j => x (σ j)))).getD i false := by
      let xs := List.ofFn x
      let ys := List.ofFn (fun j => x (σ j))
      have xlen : xs.length = 9 := List.length_ofFn
      have ylen : ys.length = 9 := List.length_ofFn
      have lookup (ws : List Bool) (j : ℕ) :
          (xs ++ ws).getD (pin j) false = (ys ++ ws).getD j false := by
        by_cases hj : j < 9
        · rw [show pin j = (σ ⟨j,hj⟩).val by simp [pin,hj]]
          rw [List.getD_append _ _ _ _ (by rw [xlen]; exact (σ ⟨j,hj⟩).isLt),
            List.getD_append _ _ _ _ (by omega)]
          rw [List.getD_eq_getElem _ _ (by rw [xlen]; exact (σ ⟨j,hj⟩).isLt),
            List.getD_eq_getElem _ _ (by omega)]
          simp only [xs,ys,List.getElem_ofFn]
        · rw [show pin j = j by simp [pin,hj]]
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),xlen,ylen]
      have run (gs : List Gate) (ws : List Bool) :
          ∃ zs, gs.foldl step (ys ++ ws) = ys ++ zs ∧
            (gs.map (liftG pin)).foldl step (xs ++ ws) = xs ++ zs := by
        induction gs generalizing ws with
        | nil => exact ⟨ws,rfl,rfl⟩
        | cons g gs ih =>
          let val := g.op.eval (g.inputs.map fun j => (ys ++ ws).getD j false)
          obtain ⟨zs,A,B⟩ := ih (ws ++ [val])
          refine ⟨zs, ?_, ?_⟩
          · simpa only [List.foldl_cons, step, List.append_assoc] using A
          · simp only [List.map_cons, List.foldl_cons, step, applyMap pin _ _ (lookup ws) g, List.append_assoc]
            exact B
      obtain ⟨zs,A,B⟩ := run D.gates []
      simp only [List.append_nil] at A B
      change ((D.gates.map (liftG pin)).foldl step xs).getD (pin i) false = (D.gates.foldl step ys).getD i false
      rw [A,B]
      exact lookup zs i
    have firstE (x : Fin 9 → Bool) : (E.wires (List.ofFn x)).getD 9 false =
        (x (min (σ a) (σ b)) && x (max (σ a) (σ b))) := by
      have ev := ewire x 9
      have fixed : pin 9 = 9 := by simp [pin]
      rw [fixed,firstD] at ev
      by_cases le : σ a ≤ σ b
      · simpa only [min_eq_left le,max_eq_right le] using ev
      · have rev : σ b ≤ σ a := le_of_not_ge le
        simpa only [min_eq_right rev,max_eq_left rev,Bool.and_comm] using ev
    have calcE : circuitFun 9 E = f := by
      funext x
      exact (ewire x D.output).trans ((congrFun correctD (fun j => x (σ j))).trans (graphSym k x))
    have eSize : E.size = D.size := by
      change (D.gates.map (liftG pin)).length = D.gates.length
      exact List.length_map _
    have h := andFirst (min (σ a) (σ b)) (max (σ a) (σ b)) rep E efan firstE calcE
    simpa only [eSize,sizeD] using h
  · exact remaining C mono first (by
      intro a b ab mem
      exact found ⟨a,b,ab,mem⟩) correct
