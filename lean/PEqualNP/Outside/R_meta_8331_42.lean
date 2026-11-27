import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_8331_42
 (synth : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 26 ∧ PEqualNP.TopForm.IsAO2 14 C ∧
  (C.gates.foldl (fun (w : List Nat) (g : PEqualNP.CircuitLowerBounds.Gate) =>
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [if g.op.eval [false, true] then a ||| b else a &&& b]) ([189297016294346753, 155696362464247818, 218994303132237904, 183565875465421444, 229736628136977440, 270286071508582656, 288160007408715776, 95229015649943559, 55389823206162488, 14003410187583936, 8521481457152, 4292497062785024, 256463044608, 63038589501440] : List Nat)).getD C.output 0 = 2097151)
 (boundary : ∀ f : (Fin 14 → Bool) → Bool,
  (∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true) → (∀ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) →
     f (fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) = true) → (∀ n ∈ ([16256, 5889, 11778, 1539, 7300, 5125, 3078, 14600, 4361, 10250, 6156, 12944, 4625, 8722, 4244, 12312, 4125, 9632, 1313, 9250, 1188, 1063, 8488, 8368, 8250, 3008, 833, 2626, 2244, 2376, 2126, 720, 595, 480, 361, 244, 127] : List Nat),
     f (fun i => n.testBit i.val) = false) → ∀ x, f x = true ↔ ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
       x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) :
have x1 : Finset (Fin (7 : ℕ) × Fin (7 : ℕ)) := {x1 : Fin (7 : ℕ) × Fin (7 : ℕ) | x1.1 = x1.2 ∨ x1.1 = x1.2 + (1 : Fin (7 : ℕ)) ∨ x1.1 = x1.2 + (3 : Fin (7 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (26 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x2 x3 = Decidable.decide (∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4, x5) ∈ x1 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true) := by
  have cmono : ∀ (C : Circuit), IsAO2 14 C → ∀ x y : Fin 14 → Bool, (∀ i, x i = true → y i = true) → circuitFun 14 C x = true → circuitFun 14 C y = true := by
    intro C kind x y hxy
    let R (u v : List Bool) := u.length = v.length ∧ ∀ i, u.getD i false = true → v.getD i false = true
    have extend {u v : List Bool} (h : R u v) {b c : Bool} (hb : b = true → c = true) : R (u++[b]) (v++[c]) := by
      refine ⟨by simp [h.1], ?_⟩
      intro i
      by_cases lt : i < u.length
      · have lt' : i < v.length := h.1 ▸ lt
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left lt, List.getElem?_append_left lt']
        exact h.2 i
      · have le := Nat.le_of_not_gt lt
        have le' : v.length ≤ i := h.1 ▸ le
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le, List.getElem?_append_right le', h.1, List.getElem?_singleton]
        split
        · exact hb
        · intro h; exact h
    have ini : R (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp,?_⟩
      intro i
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      split
      · exact hxy _
      · simp
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have run (gs : List Gate) (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (x y : List Bool) (h : R x y) :
        R (gs.foldl step x) (gs.foldl step y) := by
      induction gs generalizing x y with
      | nil => exact h
      | cons g gs ih =>
        apply ih (fun k hk => ok k (List.mem_cons_of_mem g hk))
        apply extend h
        rcases ok g (by simp) with hand | hor
        · rw [hand]
          change (g.inputs.map (fun i => x.getD i false)).all id = true →
            (g.inputs.map (fun i => y.getD i false)).all id = true
          simp only [List.all_eq_true, List.mem_map, id_eq]
          intro hx b hb
          obtain ⟨r,hr,rfl⟩ := hb
          exact h.2 r (hx _ ⟨r,hr,rfl⟩)
        · rw [hor]
          change (g.inputs.map (fun i => x.getD i false)).any id = true →
            (g.inputs.map (fun i => y.getD i false)).any id = true
          simp only [List.any_eq_true, List.mem_map, id_eq]
          rintro ⟨b,⟨r,hr,rfl⟩,hb⟩
          exact ⟨_,⟨r,hr,rfl⟩,h.2 r hb⟩
    exact (run C.gates kind.1 _ _ ini).2 C.output
  obtain ⟨C,sz,model,packed⟩ := synth
  let cols : List Nat := [189297016294346753, 155696362464247818, 218994303132237904, 183565875465421444, 229736628136977440, 270286071508582656, 288160007408715776, 95229015649943559, 55389823206162488, 14003410187583936, 8521481457152, 4292497062785024, 256463044608, 63038589501440]
  let ps := fun (w : List Nat) (g : PEqualNP.CircuitLowerBounds.Gate) =>
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [if g.op.eval [false, true] then a ||| b else a &&& b]
  let bs := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have read (k : Nat) (w : List Nat) (i : Nat) :
      (w.map (fun n => n.testBit k)).getD i false = (w.getD i 0).testBit k := by
    induction w generalizing i with
    | nil => simp
    | cons a w ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i
  have sound (k : Nat) (gs : List Gate) (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (w : List Nat) :
      (gs.foldl ps w).map (fun n => n.testBit k) = gs.foldl bs (w.map fun n => n.testBit k) := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change ((gs.foldl ps (ps w g)).map _) = gs.foldl bs (bs (w.map _) g)
      rw [ih (fun t ht => ok t (List.mem_cons_of_mem g ht))]
      apply congrArg (gs.foldl bs)
      obtain ⟨op,len⟩ := ok g (by simp)
      have two : ∃ a b, g.inputs = [a,b] := by
        cases h : g.inputs with
        | nil => simp [h] at len
        | cons a xs =>
          cases xs with
          | nil => simp [h] at len
          | cons b xs =>
            cases xs with
            | nil => exact ⟨a,b,rfl⟩
            | cons t ts => simp [h] at len
      obtain ⟨a,b,gab⟩ := two
      rcases op with op|op
      · simp only [ps, bs, gab, op, List.getD_cons_zero, List.getD_cons_succ,
          List.map_append, List.map_cons, List.map_nil, read]
        change w.map (fun n => n.testBit k) ++ [((w.getD a 0) &&& (w.getD b 0)).testBit k] =
          w.map (fun n => n.testBit k) ++ [[(w.getD a 0).testBit k, (w.getD b 0).testBit k].all id]
        simp [List.all_cons, List.all_nil, Nat.testBit_and]
      · simp only [ps, bs, gab, op, List.getD_cons_zero, List.getD_cons_succ,
          List.map_append, List.map_cons, List.map_nil, read]
        change w.map (fun n => n.testBit k) ++ [((w.getD a 0) ||| (w.getD b 0)).testBit k] =
          w.map (fun n => n.testBit k) ++ [[(w.getD a 0).testBit k, (w.getD b 0).testBit k].any id]
        simp [List.any_cons, List.any_nil, Nat.testBit_or]
  have sem (k : Fin 58) : circuitFun 14 C (fun i => (cols.getD i.val 0).testBit k.val) = (2097151 : Nat).testBit k.val := by
    have row : List.ofFn (fun i : Fin 14 => (cols.getD i.val 0).testBit k.val) = cols.map (fun m => m.testBit k.val) := by rfl
    change (C.gates.foldl bs (List.ofFn _)).getD C.output false = _
    rw [row, ← sound k.val C.gates (fun g hg => ⟨model.1 g hg,model.2.2 g hg⟩) cols, read]
    change ((C.gates.foldl ps cols).getD C.output 0).testBit k.val = _
    exact congrArg (fun n : Nat => n.testBit k.val) packed
  have pc : ∀ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) → ∃ j : Fin 58, (2097151 : Nat).testBit j.val = true ∧
       ∀ i : Fin 14, (cols.getD i.val 0).testBit j.val = decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l) := by decide +kernel
  have nc : ∀ m ∈ ([16256, 5889, 11778, 1539, 7300, 5125, 3078, 14600, 4361, 10250, 6156, 12944, 4625, 8722, 4244, 12312, 4125, 9632, 1313, 9250, 1188, 1063, 8488, 8368, 8250, 3008, 833, 2626, 2244, 2376, 2126, 720, 595, 480, 361, 244, 127] : List Nat), ∃ j : Fin 58, (2097151 : Nat).testBit j.val = false ∧
       ∀ i : Fin 14, (cols.getD i.val 0).testBit j.val = m.testBit i.val := by decide +kernel
  have hpos : ∀ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) →
     circuitFun 14 C (fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) = true := by
    intro p l h
    obtain ⟨j,y,e⟩ := pc p l h
    rw [← funext e]
    exact (sem j).trans y
  have hneg : ∀ n ∈ ([16256, 5889, 11778, 1539, 7300, 5125, 3078, 14600, 4361, 10250, 6156, 12944, 4625, 8722, 4244, 12312, 4125, 9632, 1313, 9250, 1188, 1063, 8488, 8368, 8250, 3008, 833, 2626, 2244, 2376, 2126, 720, 595, 480, 361, 244, 127] : List Nat),
     circuitFun 14 C (fun i => n.testBit i.val) = false := by
    intro m hm
    obtain ⟨j,y,e⟩ := nc m hm
    rw [← funext e]
    exact (sem j).trans y
  refine ⟨C,sz,model,?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  have h := boundary (circuitFun 14 C) (cmono C model) hpos hneg x
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] using h
