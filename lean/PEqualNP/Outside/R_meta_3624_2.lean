import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The graph relabelling follows R_meta_1936_1.
-- The split at an inversion adapts the argument in R_meta_1676_2.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3624_2
    (positive : ∀ ab ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)),
        ∀ C : Circuit, FanInTwo C →
          (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x ab.1 && x ab.2)) →
          (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → 16 ≤ C.size)
    (negative : ∀ k : Fin 9, k ∈ ([1,2,3,4,6] : List (Fin 9)) →
        ∀ P Q : Circuit, Monotone2 P → Monotone2 Q → P.size + Q.size = 12 →
          ∃ x : Fin 9 → Bool,
            let seed := (List.ofFn x ++ [!x 0]) ++ [(!x 0) && x k]
            let w := P.wires seed
            Q.eval (w ++ [!(w.getD P.output false)]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size = (13 : ℕ) →           List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => !x6.op.eval [Bool.true]) x3.gates = (1 : ℕ) →             (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x7 ≠ x8 ∧ x1 = [↑x7, ↑x8] ∧ ¬(↑x7 = (0 : ℕ) ∧ ↑x8 = (9 : ℕ)) ∧ ¬(↑x7 = (9 : ℕ) ∧ ↑x8 = (0 : ℕ))) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x3.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  have evAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have evOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have evNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl
  have evSize (D : Circuit) : D.size = D.gates.length := rfl
  let target (x : Fin 9 → Bool) := ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  have splitInv (C : Circuit) (hfan : FanInTwo C) (hsize : C.size = 13)
    (hnot : C.gates.countP (fun g => !g.op.eval [true]) = 1) :
    ∃ P Q : Circuit, Monotone2 P ∧ Monotone2 Q ∧ P.size + Q.size = 12 ∧
      ∀ seed : List Bool, seed.length = 11 →
        C.eval seed = Q.eval (P.wires seed ++ [!((P.wires seed).getD P.output false)]) := by
    let inv := fun g : Gate => !g.op.eval [true]
    change C.gates.countP inv = 1 at hnot
    obtain ⟨N, hm, hN⟩ := List.countP_pos_iff.mp (show 0 < C.gates.countP inv by omega)
    obtain ⟨pre, post, hgs⟩ := List.append_of_mem hm
    have allowed := (hfan N hm).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at allowed
    have opN : N.op = GateOp.not := by
      rcases allowed with h | h | h
      · simp [inv, h, evAnd] at hN
      · simp [inv, h, evOr] at hN
      · exact h
    have counts := hnot
    rw [hgs, List.countP_append, List.countP_cons_of_pos hN] at counts
    have mono (gs : List Gate) (out : ℕ) (sub : ∀ v ∈ gs, v ∈ C.gates)
        (hn : gs.countP inv = 0) : Monotone2 ⟨gs,out⟩ := by
      intro v hv
      obtain ⟨ops, length⟩ := hfan v (sub v hv)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops ⊢
      refine ⟨?_, length⟩
      rcases ops with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have contra := List.countP_eq_zero.mp hn v hv
        simp [inv, h, evNot] at contra
    let P : Circuit := ⟨pre, N.inputs.headD (11 + pre.length)⟩
    let Q : Circuit := ⟨post, C.output⟩
    refine ⟨P, Q, mono pre _ (by intro v hv; simp [hgs, hv]) (by omega),
      mono post _ (by intro v hv; simp [hgs, hv]) (by omega), ?_, ?_⟩
    · change C.gates.length = 13 at hsize
      simp [hgs] at hsize
      change pre.length + post.length = 12
      omega
    · intro seed hseed
      let step := fun (w : List Bool) (g : Gate) =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have lengthOf (gs : List Gate) (w : List Bool) :
          (gs.foldl step w).length = w.length + gs.length := by
        induction gs generalizing w with
        | nil => simp
        | cons g gs ih =>
          rw [List.foldl_cons, ih]
          simp [step]
          omega
      let w := pre.foldl step seed
      have hl : w.length = 11 + pre.length := by simp [w, lengthOf, hseed]
      have hv : N.op.eval (N.inputs.map fun i => w.getD i false) = !(w.getD P.output false) := by
        rw [opN]
        change (!((N.inputs.map fun i => w.getD i false).headD false)) =
          !(w.getD (N.inputs.headD (11 + pre.length)) false)
        cases hi : N.inputs with
        | nil => simp [← hl, List.getD_eq_getElem?_getD]
        | cons i is => rfl
      change (C.gates.foldl step seed).getD C.output false =
        (post.foldl step (w ++ [!(w.getD P.output false)])).getD C.output false
      rw [hgs, List.foldl_append, List.foldl_cons]
      change (post.foldl step (w ++ [N.op.eval (N.inputs.map fun i => w.getD i false)])).getD C.output false = _
      rw [hv]
  have swap (i j : Fin 9) (C : Circuit) (hfan : FanInTwo C)
    (target : (Fin 9 → Bool) → Bool)
    (agree : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [!x 0, x i && x j]) = target x) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size + 2 ∧
      (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x i && x j)) ∧
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = target x := by
    let swap (n : ℕ) := if n = 9 then 10 else if n = 10 then 9 else n
    let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map swap⟩
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun n => w.getD n false)]
    let D : Circuit := ⟨⟨.and, [i.val, j.val]⟩ :: ⟨.not, [0]⟩ :: C.gates.map rename, swap C.output⟩
    refine ⟨D, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [D, List.mem_cons, List.mem_map] at hg
      rcases hg with rfl | rfl | ⟨u, hu, rfl⟩
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by decide⟩
      · simpa [rename] using hfan u hu
    · simp [D, evSize, Nat.add_assoc]
    · intro x
      have keep (gs : List Gate) (w : List Bool) (n : ℕ) (hn : n < w.length) :
          (gs.foldl step w).getD n false = w.getD n false := by
        induction gs generalizing w with
        | nil => rfl
        | cons g gs ih =>
          rw [List.foldl_cons, ih]
          · exact List.getD_append _ _ _ _ hn
          · simp [step]; omega
      have get (k : Fin 9) : (List.ofFn x).getD k.val false = x k := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      change (((_ :: _).foldl step (List.ofFn x)).getD 9 false) = (x i && x j)
      rw [List.foldl_cons, keep]
      · have last (b : Bool) : (List.ofFn x ++ [b]).getD 9 false = b := by
          rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]; rfl
        simp only [step, last, List.map_cons, List.map_nil, evAnd, List.all_cons,
          List.all_nil, id_eq, Bool.and_true, get]
      · simp [step]
    · intro x
      let pos := x i && x j
      let neg := !x 0
      have get (k : Fin 9) : (List.ofFn x).getD k.val false = x k := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      have first : step (List.ofFn x) ⟨.and, [i.val, j.val]⟩ = List.ofFn x ++ [pos] := by
        simp only [step, pos, List.map_cons, List.map_nil, evAnd, List.all_cons,
          List.all_nil, id_eq, Bool.and_true, get]
      have second : step (List.ofFn x ++ [pos]) ⟨.not, [0]⟩ = List.ofFn x ++ [pos, neg] := by
        simp [step, evNot, List.getD_eq_getElem?_getD, neg]
      have base (n : ℕ) : (List.ofFn x ++ [neg, pos]).getD n false =
          (List.ofFn x ++ [pos, neg]).getD (swap n) false := by
        by_cases h : n < 9
        · have hs : swap n = n := by simp [swap, show n ≠ 9 by omega, show n ≠ 10 by omega]
          rw [hs, List.getD_append _ _ _ _ (by simpa), List.getD_append _ _ _ _ (by simpa)]
        rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
          List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn,swap]; split_ifs <;> omega),
          List.length_ofFn]
        by_cases h9 : n = 9
        · subst n; rfl
        by_cases h10 : n = 10
        · subst n; rfl
        have hk : 2 ≤ n - 9 := by omega
        simp [swap, h9, h10, List.getD_eq_getElem?_getD, List.getElem?_eq_none
          (show [neg,pos].length ≤ n - 9 by simpa), List.getElem?_eq_none
          (show [pos,neg].length ≤ n - 9 by simpa)]
      have lift (gs : List Gate) (W V : List Bool) (hlen : W.length = V.length)
          (big : 11 ≤ W.length) (same : ∀ n, W.getD n false = V.getD (swap n) false) :
          ∀ n, (gs.foldl step W).getD n false = ((gs.map rename).foldl step V).getD (swap n) false := by
        induction gs generalizing W V with
        | nil => exact same
        | cons g gs ih =>
          have val : g.op.eval (g.inputs.map fun n => W.getD n false) =
              (rename g).op.eval ((rename g).inputs.map fun n => V.getD n false) := by
            apply congrArg g.op.eval
            simp only [rename, List.map_map, Function.comp_def]
            exact List.map_congr_left (fun k _ => same k)
          apply ih (step W g) (step V (rename g))
          · simp [step, hlen]
          · simp [step]; omega
          · intro n
            dsimp only [step]
            rw [val]
            by_cases h : n < W.length
            · have hs : swap n < V.length := by dsimp [swap]; split_ifs <;> omega
              rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ hs, same]
            have hs : swap n = n := by simp [swap, show n ≠ 9 by omega, show n ≠ 10 by omega]
            rw [hs, List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), hlen]
      have eqn := lift C.gates (List.ofFn x ++ [neg,pos]) (List.ofFn x ++ [pos,neg])
        (by simp) (by simp) base C.output
      change (((_ :: _ :: _).foldl step (List.ofFn x)).getD (swap C.output) false) = _
      rw [List.foldl_cons, first, List.foldl_cons, second, ← eqn]
      exact agree x
  have orbit (target : (Fin 9 → Bool) → Bool)
    (htarget : ∀ x, target x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (positive : ∀ ab ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)),
      ∀ C : Circuit, FanInTwo C →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x ab.1 && x ab.2)) →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x) → 16 ≤ C.size)
    (i j : Fin 9) (hne : i ≠ j) (C : Circuit) (hf : FanInTwo C)
    (hfirst : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x i && x j))
    (hcomp : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x) : 16 ≤ C.size := by
    let maps : Fin 12 → Fin 9 → Fin 9 := ![![0,1,2,3,4,5,6,7,8],
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
    let pair (k : Fin 12) (a b : Fin 9) := (min (maps k a) (maps k b), max (maps k a) (maps k b))
    have cert : ∀ a b : Fin 9, a ≠ b → ∃ k : Fin 12,
        pair k a b ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List _) := by
      dsimp only [pair,maps]
      decide +kernel
    have graph : ∀ k (x : Fin 9 → Bool), target (x ∘ maps k) = target x := by
      intro k x
      rw [htarget, htarget]
      fin_cases k
      · rfl
      · change ((x 1 && x 2) || (x 2 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 2 && x 7) || (x 3 && x 4) || (x 8 && x 5) || (x 0 && x 4) || (x 7 && x 5) || (x 5 && x 0)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
      · change ((x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 1) || (x 3 && x 4) || (x 8 && x 6) || (x 5 && x 0) || (x 1 && x 6) || (x 4 && x 0) || (x 0 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
      · change ((x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 0 && x 5) || (x 8 && x 6) || (x 7 && x 5) || (x 5 && x 8)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
      · change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 1 && x 6) || (x 0 && x 4) || (x 5 && x 8) || (x 3 && x 4) || (x 6 && x 8) || (x 8 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
      · change ((x 3 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 8 && x 6) || (x 5 && x 7) || (x 0 && x 1) || (x 2 && x 7) || (x 6 && x 1) || (x 1 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
      · change ((x 1 && x 0) || (x 0 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 5 && x 7) || (x 8 && x 3) || (x 2 && x 7) || (x 4 && x 3) || (x 3 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
      · change ((x 8 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 3 && x 4) || (x 2 && x 7) || (x 1 && x 0) || (x 5 && x 7) || (x 4 && x 0) || (x 0 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
      · change ((x 0 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 5 && x 7) || (x 8 && x 6) || (x 3 && x 2) || (x 1 && x 6) || (x 7 && x 2) || (x 2 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
      · change ((x 5 && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 8 && x 6) || (x 4 && x 3) || (x 3 && x 8)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
      · change ((x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 8 && x 6) || (x 3 && x 4) || (x 2 && x 1) || (x 0 && x 4) || (x 6 && x 1) || (x 1 && x 0)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
      · change ((x 8 && x 5) || (x 5 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 3) || (x 5 && x 7) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 7 && x 2) || (x 2 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
        ac_rfl
    obtain ⟨k, hk⟩ := cert i j hne
    let f (a : ℕ) := if h : a < 9 then (maps k ⟨a,h⟩).val else a
    let rename (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
    let E : Circuit := ⟨C.gates.map rename,f C.output⟩
    have hEFan : FanInTwo E := by
      intro g hg
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hg
      simpa [rename] using hf z hz
    have lift (gs : List Gate) (W V : List Bool) (lengths : W.length = V.length)
        (big : 9 ≤ W.length) (agreement : ∀ a, W.getD a false = V.getD (f a) false) :
        ∀ a, ((Circuit.mk gs 0).wires W).getD a false =
          ((Circuit.mk (gs.map rename) 0).wires V).getD (f a) false := by
      induction gs generalizing W V with
      | nil => exact agreement
      | cons g gs ih =>
        let v := g.op.eval (g.inputs.map fun a => W.getD a false)
        have eqv : (rename g).op.eval ((rename g).inputs.map fun a => V.getD a false) = v := by
          apply congrArg g.op.eval
          simp only [rename,List.map_map,Function.comp_def]
          exact List.map_congr_left (fun a _ => (agreement a).symm)
        change ∀ a, ((Circuit.mk gs 0).wires (W ++ [v])).getD a false =
          ((Circuit.mk (gs.map rename) 0).wires (V ++ [_])).getD (f a) false
        rw [eqv]
        apply ih
        · simp [lengths]
        · simp; omega
        · intro a
          by_cases h : a < W.length
          · have h' : f a < V.length := by
              dsimp only [f]
              split <;> rename_i e
              · have lt := (maps k ⟨a,e⟩).isLt
                omega
              · omega
            simpa only [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ h'] using agreement a
          · rw [show f a = a by simp [f,show ¬a < 9 by omega],
                List.getD_append_right _ _ false a (by omega),
                List.getD_append_right _ _ false a (by omega),lengths]
    have same (x : Fin 9 → Bool) (a : ℕ) :
        (C.wires (List.ofFn (x ∘ maps k))).getD a false = (E.wires (List.ofFn x)).getD (f a) false := by
      apply lift C.gates _ _ (by simp) (by simp)
      intro b
      by_cases hb : b < 9
      · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,f,dite_eq_left hb,
            dite_eq_left (maps k ⟨b,hb⟩).isLt,Option.getD_some,Function.comp_apply]
      · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,f,dite_eq_right hb]
    have hpos := positive (pair k i j) hk E hEFan (by
      intro x
      refine (same x 9).symm.trans ((hfirst (x ∘ maps k)).trans ?_)
      change (x (maps k i) && x (maps k j)) =
        (x (min (maps k i) (maps k j)) && x (max (maps k i) (maps k j)))
      rcases le_total (maps k i) (maps k j) with h | h
      · simp [min_eq_left h,max_eq_right h]
      · simp [min_eq_right h,max_eq_left h,Bool.and_comm]) (by
      intro x
      exact (same x C.output).symm.trans ((hcomp (x ∘ maps k)).trans (graph k x)))
    simpa [evSize,E] using hpos
  have positiveAll := orbit target (fun _ => rfl) positive
  have negOrbit (target : (Fin 9 → Bool) → Bool)
    (htarget : ∀ x, target x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (negative : ∀ k : Fin 9, k ∈ ([1,2,3,4,6] : List (Fin 9)) →
        ∀ P Q : Circuit, Monotone2 P → Monotone2 Q → P.size + Q.size = 12 →
          ∃ x : Fin 9 → Bool,
            let seed := (List.ofFn x ++ [!x 0]) ++ [(!x 0) && x k]
            let w := P.wires seed
            Q.eval (w ++ [!(w.getD P.output false)]) ≠ target x)
    (k : Fin 9) (hk : k ≠ 0) (P Q : Circuit) (hP : Monotone2 P) (hQ : Monotone2 Q)
    (cost : P.size + Q.size = 12) :
      ∃ x : Fin 9 → Bool,
        let seed := (List.ofFn x ++ [!x 0]) ++ [(!x 0) && x k]
        let w := P.wires seed
        Q.eval (w ++ [!(w.getD P.output false)]) ≠ target x := by
    by_cases member : k ∈ ([1,2,3,4,6] : List (Fin 9))
    · exact negative k member P Q hP hQ cost
    let perm : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
    have cert : ∀ i : Fin 9, i ≠ 0 → i ∉ ([1,2,3,4,6] : List (Fin 9)) →
        perm i ∈ ([1,2,3,4,6] : List (Fin 9)) := by
      dsimp only [perm]
      decide +kernel
    have graph (x : Fin 9 → Bool) : target (x ∘ perm) = target x := by
      rw [htarget,htarget]
      change ((x 0 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 5 && x 7) || (x 8 && x 6) || (x 3 && x 2) || (x 1 && x 6) || (x 7 && x 2) || (x 2 && x 1)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    let f (a : ℕ) := if h : a < 9 then (perm ⟨a,h⟩).val else a
    let ren (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
    let transport (D : Circuit) : Circuit := ⟨D.gates.map ren, f D.output⟩
    have mono (D : Circuit) (hD : Monotone2 D) : Monotone2 (transport D) := by
      intro g hg
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hg
      simpa only [ren,List.length_map] using hD z hz
    have len (D : Circuit) : (transport D).size = D.size := List.length_map ren
    obtain ⟨x,bad⟩ := negative (perm k) (cert k hk member) (transport P) (transport Q)
      (mono P hP) (mono Q hQ) (by simpa only [len] using cost)
    let y := x ∘ perm
    let A := (List.ofFn y ++ [!y 0]) ++ [(!y 0) && y k]
    let B := (List.ofFn x ++ [!x 0]) ++ [(!x 0) && x (perm k)]
    have base (a : ℕ) : (List.ofFn y).getD a false = (List.ofFn x).getD (f a) false := by
      by_cases ha : a < 9
      · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,f,dite_eq_left ha,
          dite_eq_left (perm ⟨a,ha⟩).isLt,Option.getD_some,y,Function.comp_apply]
      · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,f,dite_eq_right ha]
    have extend (W V : List Bool) (lengths : W.length = V.length) (big : 9 ≤ W.length)
        (ok : ∀ i, W.getD i false = V.getD (f i) false) (v : Bool) (i : ℕ) :
        (W ++ [v]).getD i false = (V ++ [v]).getD (f i) false := by
      by_cases h : i < W.length
      · have hi : f i < V.length := by
          dsimp only [f]
          split
          · rename_i e
            have lt := (perm ⟨i,e⟩).isLt
            omega
          · omega
        simpa only [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ hi] using ok i
      · rw [show f i = i by simp [f,show ¬i < 9 by omega],
            List.getD_append_right _ _ false i (by omega),
            List.getD_append_right _ _ false i (by omega),lengths]
    have ab : ∀ i, A.getD i false = B.getD (f i) false := by
      apply extend _ _ (by simp) (by simp)
      apply extend _ _ (by simp) (by simp)
      exact base
    have lift (gs : List Gate) (W V : List Bool) (lengths : W.length = V.length)
        (big : 9 ≤ W.length) (same : ∀ i, W.getD i false = V.getD (f i) false) :
        ∀ i, ((Circuit.mk gs 0).wires W).getD i false =
          ((Circuit.mk (gs.map ren) 0).wires V).getD (f i) false := by
      induction gs generalizing W V with
      | nil => exact same
      | cons g gs ih =>
        let v := g.op.eval (g.inputs.map fun a => W.getD a false)
        have eqv : (ren g).op.eval ((ren g).inputs.map fun a => V.getD a false) = v := by
          apply congrArg g.op.eval
          simp only [ren,List.map_map,Function.comp_def]
          exact List.map_congr_left (fun a _ => (same a).symm)
        change ∀ i, ((Circuit.mk gs 0).wires (W ++ [v])).getD i false =
          ((Circuit.mk (gs.map ren) 0).wires (V ++ [_])).getD (f i) false
        rw [eqv]
        exact ih _ _ (by simp [lengths]) (by simp; omega) (extend W V lengths big same v)
    have wlen (gs : List Gate) (W : List Bool) :
        ((Circuit.mk gs 0).wires W).length = W.length + gs.length := by
      induction gs generalizing W with
      | nil => exact (Nat.add_zero _).symm
      | cons g gs ih =>
        change ((Circuit.mk gs 0).wires (W ++ [_])).length = _
        rw [ih]
        simp
        omega
    let W := P.wires A
    let V := (transport P).wires B
    have sw : ∀ i, W.getD i false = V.getD (f i) false :=
      lift P.gates A B (by simp [A,B]) (by simp [A]) ab
    have wl : W.length = A.length + P.gates.length := wlen P.gates A
    have vl : V.length = B.length + (P.gates.map ren).length := wlen (P.gates.map ren) B
    have tw := extend W V (by simp [wl,vl,A,B]) (by simp [wl,A]; omega) sw (!(W.getD P.output false))
    have tw' : ∀ n, (W ++ [!W.getD P.output false]).getD n false =
        (V ++ [!V.getD (f P.output) false]).getD (f n) false := by
      intro n
      rw [← sw P.output]
      exact tw n
    have final := lift Q.gates _ _ (by simp [wl,vl,A,B]) (by simp [wl,A]; omega) tw' Q.output
    refine ⟨y,?_⟩
    exact fun good => bad (final.symm.trans (good.trans (graph x)))
  have negativeAll := negOrbit target (fun _ => rfl) negative
  intro pins _ C hfan hsize hnot hpins
  obtain ⟨a,b,hne,rfl,hab,hba⟩ := hpins
  let raw (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  by_contra noWitness
  have agrees (x : Fin 9 → Bool) :
      C.eval (raw x ++ [(raw x).getD a.val false && (raw x).getD b.val false]) = target x := by
    apply Classical.not_not.mp
    intro differs
    apply noWitness
    refine ⟨x, ?_⟩
    simpa only [raw, target, evAnd, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true] using differs
  have readOrdinary (x : Fin 9 → Bool) (v : Fin 10) (h : v.val < 9) :
      (raw x).getD v.val false = x ⟨v.val,h⟩ := by
    simp only [raw, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show v.val < (List.ofFn x).length by simpa using h),
      List.getElem?_ofFn, dite_eq_left h, Option.getD_some]
  have readLast (x : Fin 9 → Bool) : (raw x).getD 9 false = !x 0 := by
    simp [raw, List.getD_eq_getElem?_getD]
  have mixed (k : Fin 9) (hk : k ≠ 0)
      (hag : ∀ x : Fin 9 → Bool, C.eval (raw x ++ [(!x 0) && x k]) = target x) : False := by
    obtain ⟨P,Q,hP,hQ,hcost,heval⟩ := splitInv C hfan hsize hnot
    obtain ⟨x,dx⟩ := negativeAll k hk P Q hP hQ hcost
    let seed := raw x ++ [(!x 0) && x k]
    exact dx ((heval seed (by simp [seed, raw])).symm.trans (hag x))
  by_cases ha : a.val < 9
  · by_cases hb : b.val < 9
    · let i : Fin 9 := ⟨a.val,ha⟩
      let j : Fin 9 := ⟨b.val,hb⟩
      have diff : i ≠ j := fun eq => hne (Fin.ext (congrArg (fun z : Fin 9 => z.val) eq))
      obtain ⟨D,hD,sD,firstD,evalD⟩ := swap i j C hfan target (by
        intro x
        simpa only [readOrdinary x a ha, readOrdinary x b hb, raw,
          List.append_assoc, List.cons_append, List.nil_append, i, j] using agrees x)
      have lower := positiveAll i j diff D hD firstD evalD
      omega
    · have hb' : b.val = 9 := by omega
      let i : Fin 9 := ⟨a.val,ha⟩
      have hi : i ≠ 0 := fun eq => hab ⟨congrArg Fin.val eq, hb'⟩
      apply mixed i hi
      intro x
      simpa only [readOrdinary x a ha, hb', readLast x, Bool.and_comm (x i) (!x 0), i] using agrees x
  · have ha' : a.val = 9 := by omega
    have hb : b.val < 9 := by
      by_contra! h
      exact hne (Fin.ext (by omega))
    let j : Fin 9 := ⟨b.val,hb⟩
    have hj : j ≠ 0 := fun eq => hba ⟨ha', congrArg Fin.val eq⟩
    apply mixed j hj
    intro x
    simpa only [ha', readLast x, readOrdinary x b hb, j] using agrees x
