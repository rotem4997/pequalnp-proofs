import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3360_373
    (skipOr :
      let f := fun (x : Fin 9 → Bool) =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), gs.length = 7 →
      (∀ j (h : j < gs.length), (gs[j].op = .and ∨ gs[j].op = .or) ∧
        gs[j].inputs.length ≤ 2 ∧ ∀ i ∈ gs[j].inputs, i < 10 + j ∨ i = 17) →
      let P : PEqualNP.CircuitLowerBounds.Circuit := ⟨⟨.or, [0,2]⟩ :: gs, 0⟩
      ∀ U ⊆ (Finset.range 17).erase 9, U.card ≤ 6 → (∃ k ∈ U, 10 ≤ k) →
        ∃ x y : Fin 9 → Bool, f x ≠ f y ∧
          (∀ k ∈ U, (P.wires (List.ofFn x)).getD k false =
            (P.wires (List.ofFn y)).getD k false))
    (readOr :
      let f := fun (x : Fin 9 → Bool) =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), gs.length = 7 →
      (∀ j (h : j < gs.length), (gs[j].op = .and ∨ gs[j].op = .or) ∧
        gs[j].inputs.length ≤ 2 ∧ ∀ i ∈ gs[j].inputs, i < 10 + j ∨ i = 17) →
      let P : PEqualNP.CircuitLowerBounds.Circuit := ⟨⟨.or, [0,2]⟩ :: gs, 0⟩
      ∀ U ⊆ (Finset.range 17).erase 9, U.card ≤ 5 → (∃ k ∈ U, 10 ≤ k) →
        ∃ x y : Fin 9 → Bool, f x ≠ f y ∧
          (x 0 || x 2) = (y 0 || y 2) ∧
          (∀ k ∈ U, (P.wires (List.ofFn x)).getD k false =
            (P.wires (List.ofFn y)).getD k false)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (8 : ℕ) → (∀ x5 ∈ x2.gates, x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x6 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x6)).getD (9 : ℕ) Bool.false = (x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)))) → ∀ x7 ⊆ Finset.range (17 : ℕ), x7.card ≤ (6 : ℕ) → ∃ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ) → Bool), x1 x10 ≠ x1 x11 ∧ ∀ x12 ∈ x7, (x2.wires (List.ofFn x10)).getD x12 Bool.false = (x2.wires (List.ofFn x11)).getD x12 Bool.false := by
  intro f C fan size monotone first U inside small
  classical
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
      (i : ℕ) (hi : i < w.length) : (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g)]
      · exact List.getD_append _ _ _ _ hi
      · simp only [step, List.length_append, List.length_singleton]
        omega
  have readInput (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  by_cases tail : ∃ k ∈ U, 10 ≤ k
  swap
  · let candidates := ((Finset.range 9).erase 0).erase 2
    have candidateCount : candidates.card = 7 := by decide
    have notContained : ¬candidates ⊆ U := by
      intro sub
      have count := Finset.card_le_card sub
      omega
    obtain ⟨i, hi, unused⟩ := Finset.not_subset.mp notContained
    have irange : i < 9 := Finset.mem_range.mp ((Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2)
    have notTwo := (Finset.mem_erase.mp hi).1
    have notZero := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    let bit : Fin 9 := ⟨i, irange⟩
    let neighbor : Fin 9 → Fin 9 := ![1, 0, 1, 2, 0, 0, 1, 2, 3]
    have changes : ∀ b : Fin 9,
        f (fun k => decide (k = b ∨ k = neighbor b)) ≠
        f (fun k => decide (k = neighbor b)) := by
      dsimp only [f, neighbor]
      decide
    let x : Fin 9 → Bool := fun k => decide (k = bit ∨ k = neighbor bit)
    let y : Fin 9 → Bool := fun k => decide (k = neighbor bit)
    have eqBit (k : Fin 9) (h : k ≠ bit) : x k = y k := by simp [x, y, h]
    refine ⟨x, y, changes bit, ?_⟩
    intro k hk
    have klt : k < 10 := by
      by_contra! large
      exact tail ⟨k, hk, large⟩
    by_cases last : k = 9
    · have eqZero : x 0 = y 0 := eqBit 0 (fun e => notZero (congrArg Fin.val e).symm)
      have eqTwo : x 2 = y 2 := eqBit 2 (fun e => notTwo (congrArg Fin.val e).symm)
      rw [last, first, first, eqZero, eqTwo]
    · have lt : k < 9 := by omega
      change (C.gates.foldl step (List.ofFn x)).getD k false =
        (C.gates.foldl step (List.ofFn y)).getD k false
      rw [keep _ _ _ (by simpa using lt), keep _ _ _ (by simpa using lt)]
      let index : Fin 9 := ⟨k, lt⟩
      have differs : index ≠ bit := by
        intro e
        have same : k = i := congrArg Fin.val e
        exact unused (same ▸ hk)
      exact (readInput x index).trans ((eqBit index differs).trans (readInput y index).symm)
  change C.gates.length = 8 at size
  cases eq : C.gates with
  | nil =>
    rw [eq] at size
    have impossible : (0 : ℕ) = 8 := size
    exact ((by decide : (0 : ℕ) ≠ 8) impossible).elim
  | cons g gs =>
    have count : gs.length = 7 := by
      rw [eq, List.length_cons] at size
      omega
    let fixed : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, [0, 2]⟩
    let normalize (j : ℕ) (q : PEqualNP.CircuitLowerBounds.Gate) :
        PEqualNP.CircuitLowerBounds.Gate :=
      ⟨q.op, q.inputs.map fun i => if i < 10 + j then i else 17⟩
    let ns := gs.mapIdx normalize
    let N : PEqualNP.CircuitLowerBounds.Circuit := ⟨fixed :: ns, 0⟩
    have nlen : ns.length = 7 := by simp [ns, count]
    have legal : ∀ j (h : j < ns.length), (ns[j].op = .and ∨ ns[j].op = .or) ∧
        ns[j].inputs.length ≤ 2 ∧ ∀ i ∈ ns[j].inputs, i < 10 + j ∨ i = 17 := by
      intro j hj
      have jlt : j < gs.length := by simpa [ns] using hj
      have mem : gs[j] ∈ C.gates := by rw [eq]; exact List.mem_cons_of_mem _ (List.getElem_mem jlt)
      have ok := fan _ mem
      have op : gs[j].op = .and ∨ gs[j].op = .or := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff, monotone _ mem] using ok.1
      simp only [ns, List.getElem_mapIdx, normalize]
      refine ⟨op, by simpa using ok.2, ?_⟩
      intro i hi
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hi
      split_ifs with h
      · exact Or.inl h
      · exact Or.inr rfl
    have fold (ts : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
        (j : ℕ) (len : w.length = 10 + j) (bound : j + ts.length ≤ 7) :
        (ts.mapIdx (fun k q => normalize (j + k) q)).foldl step w = ts.foldl step w := by
      induction ts generalizing w j with
      | nil => rfl
      | cons q ts ih =>
        rw [List.mapIdx_cons, List.foldl_cons, List.foldl_cons]
        have same : step w (normalize j q) = step w q := by
          simp only [step, normalize, List.map_map]
          congr 3
          apply List.map_congr_left
          intro k _
          change w.getD (if k < 10 + j then k else 17) false = w.getD k false
          split_ifs with h
          · rfl
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        simp only [Nat.add_zero, same]
        rw [show (fun k q => normalize (j + (k + 1)) q) =
          (fun k q => normalize (j + 1 + k) q) by
            funext k q
            rw [show j + (k + 1) = j + 1 + k by omega]]
        apply ih
        · simp only [step, List.length_append, List.length_singleton, len, Nat.add_assoc]
        · simp only [List.length_cons] at bound
          omega
    have base (x : Fin 9 → Bool) : step (List.ofFn x) g = step (List.ofFn x) fixed := by
      let w := List.ofFn x
      have len : w.length = 9 := List.length_ofFn
      have hlen : (step w g).length = 10 := by simp [step, len]
      have h := first x
      change (C.gates.foldl step w).getD 9 false = (x 0 || x 2) at h
      rw [eq, List.foldl_cons] at h
      rw [keep gs (step w g) 9 (by omega)] at h
      have val : (step w g).getD 9 false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [← len]
        simp only [step, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
        rfl
      rw [val] at h
      have fixedValue : fixed.op.eval (fixed.inputs.map fun i => w.getD i false) = (x 0 || x 2) := by
        change (w.getD 0 false || (w.getD 2 false || false)) = (x 0 || x 2)
        rw [Bool.or_false]
        exact congrArg₂ (· || ·) (readInput x 0) (readInput x 2)
      change w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] =
        w ++ [fixed.op.eval (fixed.inputs.map fun i => w.getD i false)]
      rw [h, fixedValue]
    have wires (x : Fin 9 → Bool) : N.wires (List.ofFn x) = C.wires (List.ofFn x) := by
      change (fixed :: ns).foldl step (List.ofFn x) = C.gates.foldl step (List.ofFn x)
      rw [eq, List.foldl_cons, List.foldl_cons]
      rw [base]
      simpa only [ns, Nat.zero_add] using fold gs (step (List.ofFn x) fixed) 0
        (by simp [step]) (by omega)
    by_cases use : 9 ∈ U
    · have inset : U.erase 9 ⊆ (Finset.range 17).erase 9 := by
        intro i hi
        obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hi
        exact Finset.mem_erase.mpr ⟨ne, inside mem⟩
      have card : (U.erase 9).card ≤ 5 := by
        rw [Finset.card_erase_of_mem use]
        omega
      obtain ⟨j, hj, jbig⟩ := tail
      have tailKept : ∃ k ∈ U.erase 9, 10 ≤ k :=
        ⟨j, Finset.mem_erase.mpr ⟨by omega, hj⟩, jbig⟩
      obtain ⟨x, y, diff, agreeOr, agree⟩ := readOr ns nlen legal (U.erase 9) inset card tailKept
      change ∀ k ∈ U.erase 9, (N.wires (List.ofFn x)).getD k false =
        (N.wires (List.ofFn y)).getD k false at agree
      refine ⟨x, y, diff, ?_⟩
      intro k hk
      by_cases eqK : k = 9
      · rw [eqK, first, first, agreeOr]
      · simpa only [wires] using agree k (Finset.mem_erase.mpr ⟨eqK, hk⟩)
    · have inset : U ⊆ (Finset.range 17).erase 9 := by
        intro i hi
        exact Finset.mem_erase.mpr ⟨fun e => use (e ▸ hi), inside hi⟩
      obtain ⟨x, y, diff, agree⟩ := skipOr ns nlen legal U inset small tail
      change ∀ k ∈ U, (N.wires (List.ofFn x)).getD k false =
        (N.wires (List.ofFn y)).getD k false at agree
      exact ⟨x, y, diff, fun k hk => by simpa only [wires] using agree k hk⟩
