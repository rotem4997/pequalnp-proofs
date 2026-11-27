import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The row permutation exchanges graph vertices 0 and 2, 3 and 5, and 4 and 7.
-- Bit positions 12 through 23 are the positive rows.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_3188_31
    (firstEdgeBound : ∀ C : Circuit, FanInTwo C →
      (∃ q ∈ ([1,4] : List ℕ), ∀ y : Fin 9 → Bool,
        (C.wires (List.ofFn y)).getD 9 false = (y 0 && (List.ofFn y).getD q false)) →
      circuitFun 9 C = (fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) → 16 ≤ C.size)
    (sharedAnd : ∀ b ∈ ([12288] : List (BitVec 24)), ∀ xs : List (BitVec 24),
      let seed : List (BitVec 24) := [202052, 276515, 549652, 1097833, 101010, 10616859, 4456668, 2624736, 13635328, 751444] ++ [b]
      (16773120 : BitVec 24) ∈ seed ++ xs →
      (∀ i : Fin xs.length, let old := seed ++ xs.take i.val
        ∃ a ∈ old, ∃ c ∈ old, xs.get i = a &&& c ∨ xs.get i = a ||| c) →
      14 ≤ xs.length)
    (orCases : ∀ b ∈ ([375475, 474471, 650134, 786390, 1015671, 1166075, 1299821, 1374315, 1631101, 1832829, 2723570, 3722473, 4471039, 4557534, 4658652, 5208028, 5554429, 11714683, 13684585, 13733778, 13836100, 13897692, 13909795, 14384980] : List (BitVec 24)), ∀ xs : List (BitVec 24),
      let seed : List (BitVec 24) := [202052, 276515, 549652, 1097833, 101010, 10616859, 4456668, 2624736, 13635328, 751444] ++ [b]
      (16773120 : BitVec 24) ∈ seed ++ xs →
      (∀ i : Fin xs.length, let old := seed ++ xs.take i.val
        ∃ a ∈ old, ∃ c ∈ old, xs.get i = a &&& c ∨ xs.get i = a ||| c) →
      14 ≤ xs.length) :
  have x1 : Fin (9 : ℕ) → BitVec (24 : ℕ) := fun (x1 : Fin (9 : ℕ)) =>   have x2 : ℕ × ℕ := [((49 : ℕ), (1348 : ℕ)), ((67 : ℕ), (2083 : ℕ)), ((134 : ℕ), (788 : ℕ)), ((268 : ℕ), (105 : ℕ)), ((24 : ℕ), (2706 : ℕ)), ((2592 : ℕ), (27 : ℕ)), ((1088 : ℕ), (220 : ℕ)), ((640 : ℕ), (3296 : ℕ)), ((3328 : ℕ), (3840 : ℕ))].getD ↑x1 ((0 : ℕ), (0 : ℕ));   BitVec.ofNat (24 : ℕ) ((4096 : ℕ) * x2.1 + x2.2); have x2 : List (BitVec (24 : ℕ)) := List.ofFn x1 ++ [x1 (0 : Fin (9 : ℕ)) ||| x1 (2 : Fin (9 : ℕ))]; ∀ (x3 : List (BitVec (24 : ℕ))),   BitVec.ofNat (24 : ℕ) ((4095 : ℕ) * (4096 : ℕ)) ∈ x2 ++ x3 →     (∀ (x5 : Fin x3.length),         have x6 : List (BitVec (24 : ℕ)) := x2 ++ List.take (↑x5) x3;         x3.get x5 ∉ x6 ∧ x3.get x5 ≠ (0 : BitVec (24 : ℕ)) ∧ x3.get x5 ≠ (-1 : BitVec (24 : ℕ)) ∧ ∃ x7 ∈ x6, ∃ x8 ∈ x6, x3.get x5 = x7 &&& x8 ∨ x3.get x5 = x7 ||| x8) →       (15 : ℕ) ≤ x3.length := by

  have evalAnd (s : List Bool) : GateOp.and.eval s = s.all id := rfl
  have evalOr (s : List Bool) : GateOp.or.eval s = s.any id := rfl
  -- Each of the six tags is one graph edge. The rows of phys list the input columns
  -- after relabeling its endpoints to 0 and either 1 or 4.
  let seeds : List (BitVec 24) := [202052, 276515, 549652, 1097833, 101010, 10616859, 4456668, 2624736, 13635328, 751444]
  let tags : List (BitVec 24) := [16384, 32768, 65536, 262144, 1048576, 4194304]
  let phys (k : Fin 6) : List (BitVec 24) := ([[549652, 1097833, 13635328, 10616859, 2624736, 276515, 101010, 4456668, 202052], [1097833, 13635328, 10616859, 202052, 101010, 549652, 4456668, 2624736, 276515], [202052, 276515, 549652, 1097833, 101010, 10616859, 4456668, 2624736, 13635328], [276515, 202052, 10616859, 13635328, 4456668, 549652, 101010, 2624736, 1097833], [1097833, 13635328, 10616859, 202052, 101010, 549652, 4456668, 2624736, 276515], [13635328, 1097833, 549652, 276515, 4456668, 10616859, 101010, 2624736, 202052]] : List (List (BitVec 24))).getD k.val []
  let other (k : Fin 6) : ℕ := ([1, 4, 4, 4, 1, 4] : List ℕ).getD k.val 0
  let oa (k : Fin 6) : ℕ := ([8, 3, 0, 1, 3, 8] : List ℕ).getD k.val 0
  let ob (k : Fin 6) : ℕ := ([0, 5, 2, 5, 5, 2] : List ℕ).getD k.val 0
  let firstTwo (k : Fin 6) : List Gate := [⟨.and,[0, other k]⟩, ⟨.or,[oa k, ob k]⟩]
  let physicalSeed (k : Fin 6) := phys k ++ [tags.getD k.val 0, (751444 : (BitVec 24))]
  let target : (BitVec 24) := 16773120
  let mask (i : Fin 24) : BitVec 9 := ([42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402, 3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288] : List (BitVec 9)).getD i.val 0
  let bits (x : BitVec 9) (i : Fin 9) := x.getLsbD i.val
  let edge (x : Fin 9 → Bool) : Bool := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let val (r : ℕ) (s : (BitVec 24)) := s.getLsbD r
  let shape (g : Gate) : Prop := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

  -- The extraction induction follows the 24-row circuit construction in project PR 6186.
  have extract (xs ys : List (BitVec 24))
      (h : ∀ j : Fin ys.length, ∃ a ∈ xs ++ ys.take j.val, ∃ b ∈ xs ++ ys.take j.val,
        ys.get j = a &&& b ∨ ys.get j = a ||| b) :
      ∃ gs : List Gate, gs.length = ys.length ∧ (∀ g ∈ gs, shape g) ∧
        ∀ r : ℕ, gs.foldl step (xs.map (val r)) = (xs ++ ys).map (val r) := by
    induction ys generalizing xs with
    | nil => exact ⟨[], rfl, by simp, by simp⟩
    | cons y ys ih =>
      have hhead : ∃ a ∈ xs, ∃ b ∈ xs, y = a &&& b ∨ y = a ||| b := by
        simpa using h ⟨0, by simp⟩
      obtain ⟨a, ha, b, hb, hgate⟩ := hhead
      obtain ⟨i, hi, ea⟩ := List.mem_iff_getElem.mp ha
      obtain ⟨j, hj, eb⟩ := List.mem_iff_getElem.mp hb
      have sub (r k : ℕ) (hk : k < xs.length) :
          (xs.map (val r)).getD k false = val r xs[k] := by
        rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_map]
      have one : ∃ g : Gate, shape g ∧
          ∀ r, step (xs.map (val r)) g = (xs ++ [y]).map (val r) := by
        rcases hgate with eq | eq
        · refine ⟨⟨.and,[i,j]⟩, by simp [shape], fun r => ?_⟩
          simp only [step, evalAnd, evalOr, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true, List.map_append]
          rw [sub r i hi, sub r j hj, ea, eb]
          simp [val, eq]
        · refine ⟨⟨.or,[i,j]⟩, by simp [shape], fun r => ?_⟩
          simp only [step, evalAnd, evalOr, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, id_eq, Bool.or_false, List.map_append]
          rw [sub r i hi, sub r j hj, ea, eb]
          simp [val, eq]
      obtain ⟨g, hg, same⟩ := one
      have tail : ∀ k : Fin ys.length, ∃ a ∈ (xs ++ [y]) ++ ys.take k.val,
          ∃ b ∈ (xs ++ [y]) ++ ys.take k.val,
            ys.get k = a &&& b ∨ ys.get k = a ||| b := by
        intro k
        simpa [List.append_assoc] using h k.succ
      obtain ⟨gs, hs, hgs, run⟩ := ih (xs ++ [y]) tail
      refine ⟨g :: gs, by simp [hs], ?_, fun r => ?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hg
        · exact hgs _ hu
      · rw [List.foldl_cons, same, run]
        simp [List.append_assoc]

  have retained (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ h

  -- Monotonicity follows the fold argument in the project LowMergeWires module.
  let LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

  have eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
      (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
      op.eval (l.map f) = true → op.eval (l.map f') = true := by
    rcases hop with rfl | rfl
    · simp only [evalAnd, evalOr, List.all_eq_true, List.mem_map, id]
      intro H x hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact h i (H (f i) ⟨i, hi, rfl⟩)
    · simp only [evalAnd, evalOr, List.any_eq_true, List.mem_map, id]
      rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
      exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

  have fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ a b : List Bool, a.length = b.length → LeL a b →
        LeL (gs.foldl step a) (gs.foldl step b) := by
    induction gs with
    | nil => intro a b _ h; exact h
    | cons g gs ih =>
      intro a b hl h
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      · simp [step, hl]
      · intro i hi
        simp only [step] at hi ⊢
        by_cases hia : i < a.length
        · rw [List.getD_append _ _ _ _ hia] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact h i hi
        · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
          rw [List.getD_append_right _ _ _ _ (by omega)]
          rw [← hl]
          by_cases he : i - a.length = 0
          · rw [he] at hi ⊢
            simp only [List.getD_cons_zero] at hi ⊢
            exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
          · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
            rw [hm] at hi; simp at hi

  -- Every true input contains a positive boundary row, and every false input is
  -- contained in a negative boundary row. This transfers the 24 tests to the full function.
  have extend (C : Circuit) (mono : Monotone2 C)
      (hits : ∀ i, C.eval (List.ofFn (bits (mask i))) = target.getLsbD i.val) :
      circuitFun 9 C = edge := by
    have cover : ∀ r : BitVec 9, ∃ i : Fin 24,
        target.getLsbD i.val = edge (bits r) ∧
        (if edge (bits r) then mask i &&& r = mask i else mask i &&& r = r) := by decide +kernel
    funext y
    let r : BitVec 9 := (BitVec.ofBoolListLE (List.ofFn y)).cast (by simp)
    have packed : bits r = y := by
      funext i
      simp only [bits, r, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    obtain ⟨i, lab, sub⟩ := cover r
    have gateMono : PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C := by
      intro g hg
      simpa using (mono g hg).1
    have cmp (a b : BitVec 9) (le : ∀ i : Fin 9, bits a i = true → bits b i = true) :
        C.eval (List.ofFn (bits a)) = true → C.eval (List.ofFn (bits b)) = true := by
      apply fold_mono C.gates gateMono _ _ (by simp)
      intro j hj
      by_cases h : j < 9
      · rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_ofFn] at hj ⊢
        exact le ⟨j,h⟩ hj
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h)] at hj
        contradiction
    change C.eval (List.ofFn y) = edge y
    rw [← packed]
    have hit := (hits i).trans lab
    cases e : edge (bits r)
    · simp only [e, Bool.false_eq_true, ite_false] at sub
      cases h : C.eval (List.ofFn (bits r)) with
      | false => rfl
      | true =>
        have rel (j : Fin 9) : bits r j = true → bits (mask i) j = true := by
          have eq := congrArg (fun v : BitVec 9 => v.getLsbD j.val) sub
          change ((mask i &&& r).getLsbD j.val) = r.getLsbD j.val at eq
          rw [BitVec.getLsbD_and] at eq
          simp only [bits]
          intro hr
          simpa [hr] using eq
        have h' := cmp _ _ rel h
        rw [hit, e] at h'
        contradiction
    · simp only [e, ite_true] at sub
      apply cmp (mask i) r _ (hit.trans e)
      intro j hj
      have eq := congrArg (fun v : BitVec 9 => v.getLsbD j.val) sub
      change ((mask i &&& r).getLsbD j.val) = (mask i).getLsbD j.val at eq
      rw [BitVec.getLsbD_and] at eq
      change (mask i).getLsbD j.val = true at hj
      change r.getLsbD j.val = true
      simpa [hj] using eq

  -- Put the raw edge AND first, the supplied OR second, then replay the suffix.
  -- The resulting ordinary circuit has two more gates than the suffix.
  have byFirst
      (known : ∀ C : Circuit, FanInTwo C →
        (∃ q ∈ ([1,4] : List ℕ), ∀ y : Fin 9 → Bool,
          (C.wires (List.ofFn y)).getD 9 false = (y 0 && (List.ofFn y).getD q false)) →
        circuitFun 9 C = edge → 16 ≤ C.size) :
      ∀ b ∈ tags, ∀ xs : List (BitVec 24), let seed := seeds ++ [b]
        target ∈ seed ++ xs →
        (∀ i : Fin xs.length, let old := seed ++ xs.take i.val
          ∃ a ∈ old, ∃ c ∈ old, xs.get i = a &&& c ∨ xs.get i = a ||| c) → 14 ≤ xs.length := by
    intro b hb xs seed out ops
    dsimp only [seed] at out ops
    obtain ⟨j, hj, eq⟩ := List.mem_iff_getElem.mp hb
    let k : Fin 6 := ⟨j, hj⟩
    have beq : tags.getD k.val 0 = b := by rw [List.getD_eq_getElem _ _ hj, eq]
    have same : ∀ w, w ∈ seeds ++ [b] ↔ w ∈ physicalSeed k := by
      rw [← beq]
      have e : ∀ k : Fin 6, (seeds ++ [tags.getD k.val 0]).toFinset = (physicalSeed k).toFinset := by decide +kernel
      intro w
      simpa only [List.mem_toFinset] using (Finset.ext_iff.mp (e k) w)
    obtain ⟨gs, len, wf, run⟩ := extract (physicalSeed k) xs (by
      intro i
      obtain ⟨a, ha, c, hc, h⟩ := ops i
      have lift (z : (BitVec 24)) (hz : z ∈ (seeds ++ [b]) ++ xs.take i.val) : z ∈ physicalSeed k ++ xs.take i.val :=
        List.mem_append.mpr ((List.mem_append.mp hz).imp (same z).mp id)
      exact ⟨a, lift a ha, c, lift c hc, h⟩)
    have mem : target ∈ physicalSeed k ++ xs := by
      rw [List.mem_append] at out ⊢
      exact out.imp (same target).mp id
    obtain ⟨o, ho, hout⟩ := List.mem_iff_getElem.mp mem
    let C : Circuit := ⟨firstTwo k ++ gs, o⟩
    have mono : Monotone2 C := by
      intro g hg
      change g ∈ firstTwo k ++ gs at hg
      rcases List.mem_append.mp hg with hg | hg
      · simp [firstTwo] at hg
        rcases hg with rfl | rfl <;> simp
      · exact wf g hg
    have fan : FanInTwo C := by
      intro g hg
      obtain ⟨op, ar⟩ := mono g hg
      exact ⟨by simpa using (show g.op = .and ∨ g.op = .or ∨ g.op = .not from
        (show g.op = .and ∨ g.op = .or from by simpa using op).imp_right Or.inl), ar⟩
    have hits (i : Fin 24) : C.eval (List.ofFn (bits (mask i))) = target.getLsbD i.val := by
      have table : ∀ (k : Fin 6) (i : Fin 24), ∃ r : Fin 24,
          (firstTwo k).foldl step (List.ofFn (bits (mask i))) = (physicalSeed k).map (val r.val) ∧
          target.getLsbD r.val = target.getLsbD i.val := by decide +kernel
      obtain ⟨r, agree, label⟩ := table k i
      change (((firstTwo k ++ gs).foldl step _).getD o false) = _
      rw [List.foldl_append, agree, run, List.getD_eq_getElem _ _ (by simpa using ho), List.getElem_map, hout]
      exact label
    have qmem : ∀ k : Fin 6, other k ∈ ([1,4] : List ℕ) := by decide +kernel
    have first (y : Fin 9 → Bool) : (C.wires (List.ofFn y)).getD 9 false =
        (y 0 && (List.ofFn y).getD (other k) false) := by
      change (((firstTwo k ++ gs).foldl step (List.ofFn y)).getD 9 false) = _
      rw [List.foldl_append, retained gs _ 9 (by simp [firstTwo, step])]
      simp [firstTwo, step, evalAnd, evalOr, List.getD_eq_getElem?_getD]
    have bound := known C fan ⟨_, qmem k, first⟩ (extend C mono hits)
    change 16 ≤ (firstTwo k ++ gs).length at bound
    simp [firstTwo, len] at bound
    omega

  let base := seeds
  let goal : BitVec 24 := 16773120
  let left : List (BitVec 24) := [12288, 16384, 32768, 65536, 262144, 1048576, 4194304]
  let right : List (BitVec 24) := [375475, 474471, 650134, 786390, 1015671, 1166075, 1299821, 1374315, 1631101, 1832829, 2723570, 3722473, 4471039, 4557534, 4658652, 5208028, 5554429, 11714683, 13684585, 13733778, 13836100, 13897692, 13909795, 14384980]
  let choices := left ++ right
  let axis (flip : Bool) (i : Fin 24) : ℕ :=
    if flip then ([0, 5, 2, 3, 6, 1, 4, 7, 8, 10, 9, 11, 13, 12, 17, 21, 19, 14, 18, 16, 23, 15, 22, 20] : List ℕ).getD i.val i.val else i.val
  -- On positive rows a replacement may add ones; on negative rows it may remove ones.
  let better (flip : Bool) (x y : BitVec 24) : Prop := ∀ i : Fin 24,
    if goal.getLsbD i.val then x.getLsbD (axis flip i) ≤ y.getLsbD i.val
    else y.getLsbD i.val ≤ x.getLsbD (axis flip i)
  have bitAnd : ∀ a b c d : Bool, a ≤ b → c ≤ d → (a && c) ≤ (b && d) := by decide +kernel
  have bitOr : ∀ a b c d : Bool, a ≤ b → c ≤ d → (a || c) ≤ (b || d) := by decide +kernel
  have combine (f : Bool) (a b c d : BitVec 24) (h : better f a b) (k : better f c d) :
      better f (a &&& c) (b &&& d) ∧ better f (a ||| c) (b ||| d) := by
    constructor
    · intro i
      have ha := h i
      have hc := k i
      cases e : goal.getLsbD i.val <;>
        simp only [e, Bool.false_eq_true, ite_false, ite_true, BitVec.getLsbD_and] at ha hc ⊢ <;>
        exact bitAnd _ _ _ _ ha hc
    · intro i
      have ha := h i
      have hc := k i
      cases e : goal.getLsbD i.val <;>
        simp only [e, Bool.false_eq_true, ite_false, ite_true, BitVec.getLsbD_or] at ha hc ⊢ <;>
        exact bitOr _ _ _ _ ha hc
  have fixed : ∀ f i, goal.getLsbD (axis f i) = goal.getLsbD i.val := by decide +kernel
  have finish (f : Bool) (y : BitVec 24) (h : better f goal y) : y = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    let i : Fin 24 := ⟨n, hn⟩
    specialize h i
    rw [fixed f i] at h
    change y.getLsbD i.val = goal.getLsbD i.val
    cases hg : goal.getLsbD i.val <;> cases hy : y.getLsbD i.val <;> try rfl
    all_goals
      simp only [hg, hy, Bool.false_eq_true, ite_true, ite_false] at h
      exact ((by decide : ¬ (true ≤ false)) h).elim
  have raw : ∀ f x, x ∈ base → ∃ y ∈ base, better f x y := by
    intro f
    have ok : base.all (fun x => base.any (fun y => decide (better f x y))) = true := by
      cases f <;> decide +kernel
    simpa only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] using ok
  let gate (old : List (BitVec 24)) (v : BitVec 24) : Prop :=
    ∃ a ∈ old, ∃ b ∈ old, v = a &&& b ∨ v = a ||| b
  let trace (seed xs : List (BitVec 24)) : Prop :=
    ∀ i : Fin xs.length, gate (seed ++ xs.take i.val) xs[i]
  have replay (f : Bool) (s s' xs : List (BitVec 24))
      (hs : ∀ x ∈ s, ∃ y ∈ s', better f x y) (hx : trace s xs) :
      ∃ ys : List (BitVec 24), ys.length = xs.length ∧ trace s' ys ∧
        ∀ x ∈ s ++ xs, ∃ y ∈ s' ++ ys, better f x y := by
    induction xs generalizing s s' with
    | nil => exact ⟨[], rfl, fun i => Fin.elim0 i, by simpa using hs⟩
    | cons x xs ih =>
      have first : gate s x := by simpa using hx 0
      obtain ⟨a, ha, b, hb, op⟩ := first
      obtain ⟨a', ha', hab⟩ := hs a ha
      obtain ⟨b', hb', hbb⟩ := hs b hb
      obtain ⟨y, hy, hxy⟩ : ∃ y, gate s' y ∧ better f x y := by
        rcases op with h | h
        · exact ⟨_, ⟨a', ha', b', hb', Or.inl rfl⟩, h.symm ▸ (combine _ _ _ _ _ hab hbb).1⟩
        · exact ⟨_, ⟨a', ha', b', hb', Or.inr rfl⟩, h.symm ▸ (combine _ _ _ _ _ hab hbb).2⟩
      have old : ∀ w ∈ s ++ [x], ∃ z ∈ s' ++ [y], better f w z := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · obtain ⟨z, hz, hi⟩ := hs w hw
          exact ⟨z, List.mem_append_left _ hz, hi⟩
        · obtain rfl := List.mem_singleton.mp hw
          exact ⟨y, by simp, hxy⟩
      have tail : trace (s ++ [x]) xs := by
        intro i
        simpa [List.append_assoc] using hx i.succ
      obtain ⟨ys, len, valid, rest⟩ := ih (s ++ [x]) (s' ++ [y]) old tail
      refine ⟨y :: ys, by simp [len], ?_, by simpa [List.append_assoc] using rest⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hy
      · simpa [List.append_assoc] using valid j
  -- The finite table checks the first gate only. The replay above applies to every later gate.
  -- Each triple gives a first signature, its replacement, and whether to permute the rows.
  let certs : List (BitVec 24 × BitVec 24 × Bool) := [
    (3, 12288, false), (9, 12288, false), (16, 12288, false),
    (18, 12288, false), (20, 12288, false), (24, 12288, false),
    (33, 12288, false), (64, 12288, false), (68, 12288, false),
    (72, 12288, false), (84, 12288, false), (96, 12288, false),
    (144, 12288, false), (192, 12288, false), (260, 12288, false),
    (528, 12288, false), (768, 12288, false), (1088, 12288, false),
    (1280, 12288, false), (1792, 12288, false), (2048, 12288, false),
    (2050, 12288, false), (2080, 12288, false), (2176, 12288, false),
    (2560, 12288, false), (3072, 12288, false), (4096, 12288, false),
    (8192, 12288, false), (12288, 12288, false), (16384, 16384, false),
    (16448, 16384, false), (32768, 32768, false), (65536, 65536, false),
    (66064, 65536, false), (131072, 16384, true), (131088, 16384, true),
    (237526, 786390, false), (262144, 262144, false), (375475, 375475, false),
    (474471, 474471, false), (524288, 65536, true), (525376, 65536, true),
    (650134, 650134, false), (786390, 786390, false), (817975, 474471, true),
    (1015671, 1015671, false), (1048576, 1048576, false), (1166075, 1166075, false),
    (1299821, 1299821, false), (1374315, 1374315, false), (1631101, 1631101, false),
    (1832829, 1832829, false), (2097152, 32768, true), (2650100, 786390, true),
    (2723570, 2723570, false), (2825700, 650134, true), (2850804, 786390, true),
    (2899171, 375475, true), (3722473, 3722473, false), (4194304, 4194304, false),
    (4471039, 4471039, false), (4557534, 4557534, false), (4658652, 4658652, false),
    (5006300, 4658652, true), (5208028, 5208028, false), (5554429, 5554429, false),
    (7081212, 4557534, true), (8388608, 1048576, true), (10687839, 1631101, true),
    (10717851, 3722473, true), (10893371, 1374315, true), (11144443, 1166075, true),
    (11166495, 1299821, true), (11237215, 1832829, true), (11714683, 11714683, false),
    (13684585, 13684585, false), (13733778, 13733778, false), (13836100, 13836100, false),
    (13897692, 13897692, false), (13909795, 13909795, false), (14184212, 13836100, true),
    (14384980, 14384980, false), (15073503, 5554429, true), (15863579, 13684585, true),
    (16256992, 13733778, true)]
  have existsRow : ∀ a ∈ base, ∀ b ∈ base, ∀ v ∈ [a &&& b, a ||| b],
      v ∉ base → v ≠ 0 → v ≠ -1 → ∃ q ∈ certs, q.1 = v := by
    have ok : base.all (fun a => base.all (fun b => [a &&& b, a ||| b].all (fun v =>
      decide (v ∈ base ∨ v = 0 ∨ v = -1) || certs.any (fun q => q.1 == v)))) = true := by
      decide +kernel
    intro a ha b hb v hv hn hz hm
    have r := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp ok a ha) b hb) v hv
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at r
    exact r.resolve_left (fun h => h.elim hn (fun k => k.elim hz hm))
  have checks : ∀ q ∈ certs, q.2.1 ∈ choices ∧ better q.2.2 q.1 q.2.1 := by
    have ok : certs.all (fun q => choices.contains q.2.1 && decide (better q.2.2 q.1 q.2.1)) = true := by
      decide +kernel
    simpa only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] using ok
  have covered : ∀ a ∈ base, ∀ b ∈ base, ∀ v ∈ [a &&& b, a ||| b],
      v ∉ base → v ≠ 0 → v ≠ -1 → ∃ c ∈ choices, ∃ f : Bool, better f v c := by
    intro a ha b hb v hv nov nz no
    obtain ⟨q, hq, rfl⟩ := existsRow a ha b hb v hv nov nz no
    exact ⟨_, (checks q hq).1, _, (checks q hq).2⟩

  change ∀ fs : List (BitVec 24), goal ∈ base ++ fs →
    (∀ i : Fin fs.length, let old := base ++ fs.take i.val
      fs[i] ∉ old ∧ fs[i] ≠ 0 ∧ fs[i] ≠ -1 ∧ gate old fs[i]) → 15 ≤ fs.length
  intro fs out valid
  cases fs with
  | nil =>
    have hz : goal ∉ base := by decide +kernel
    exact (hz (by simpa using out)).elim
  | cons x xs =>
    have fst : x ∉ base ∧ x ≠ 0 ∧ x ≠ -1 ∧ gate base x := by simpa using valid 0
    obtain ⟨a, ha, b, hb, hop⟩ := fst.2.2.2
    obtain ⟨c, hc, f, hc'⟩ := covered a ha b hb x (by simpa using hop) fst.1 fst.2.1 fst.2.2.1
    have start : ∀ w ∈ base ++ [x], ∃ z ∈ base ++ [c], better f w z := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨z, hz, h⟩ := raw f w hw
        exact ⟨z, List.mem_append_left _ hz, h⟩
      · obtain rfl := List.mem_singleton.mp hw
        exact ⟨c, by simp, hc'⟩
    have tail : trace (base ++ [x]) xs := by
      intro i
      simpa [List.append_assoc] using (valid i.succ).2.2.2
    obtain ⟨ys, hlen, hyv, endp⟩ := replay f _ _ _ start tail
    obtain ⟨z, hz, hgoal⟩ := endp goal (by simpa [List.append_assoc] using out)
    have hit : goal ∈ (base ++ [c]) ++ ys := finish f z hgoal ▸ hz
    have n : 14 ≤ ys.length := by
      rcases List.mem_append.mp hc with h | h
      · change c ∈ (12288 : BitVec 24) :: tags at h
        rcases List.mem_cons.mp h with h | h
        · exact sharedAnd c (by simp [h]) ys hit hyv
        · exact byFirst firstEdgeBound c h ys hit hyv
      · exact orCases c h ys hit hyv
    simp only [List.length_cons]
    omega
