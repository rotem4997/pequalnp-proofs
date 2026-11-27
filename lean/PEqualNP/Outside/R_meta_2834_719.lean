import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The row encoding follows the trace argument for L-meta-3202.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2834_719
    (pinsRead : ∀ (a b : Fin 9) (C : Circuit), a ≠ 0 → a ≠ 4 → b ≠ 0 → b ≠ 4 → a ≠ b →
        FanInTwo C →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
           x 6 && x 8 || x 8 && x 5)) →
        ∀ i : Fin 9, ∃ g ∈ C.gates,
          i.val ∈ (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs))
    (near :
      let raw : List (BitVec 59) :=
        [360930119642124586, 432486920269079116, 293578547141297264,
          289365901620316032, 439119665042618368, 297239789478805504,
          306275578149863424, 540467122476679168, 576425567931334656]
      let step := fun (ws : List (BitVec 59)) (g : Fin 3 × List (Fin 25)) =>
        let args := g.2.map fun i => ws.getD i.val 0
        ws ++ [if g.1 = 0 then args.foldr (· &&& ·) (~~~0)
          else if g.1 = 1 then args.foldr (· ||| ·) 0 else ~~~(args.headD 0)]
      ∀ (a b : Fin 9) (gs : List (Fin 3 × List (Fin 25))) (out : Fin 25),
        10 * min a.val b.val + max a.val b.val ∈ ([12,16,23,27,38,57,58,68] : List ℕ) →
        gs.length ≤ 13 → (∀ g ∈ gs, g.2.length ≤ 2) →
        (∀ i : Fin 25, i.val < 9 → ∃ g ∈ gs,
          i ∈ (if g.1 = 2 then g.2.take 1 else g.2)) →
        let initial := raw ++ [raw.getD 0 0 ||| raw.getD 4 0, raw.getD a.val 0 ||| raw.getD b.val 0]
        let final := gs.foldl step initial
        final.getD out.val 0 ≠ 316380210352264264)
    (far :
      let raw : List (BitVec 59) :=
        [360930119642124586, 432486920269079116, 293578547141297264,
          289365901620316032, 439119665042618368, 297239789478805504,
          306275578149863424, 540467122476679168, 576425567931334656]
      let step := fun (ws : List (BitVec 59)) (g : Fin 3 × List (Fin 25)) =>
        let args := g.2.map fun i => ws.getD i.val 0
        ws ++ [if g.1 = 0 then args.foldr (· &&& ·) (~~~0)
          else if g.1 = 1 then args.foldr (· ||| ·) 0 else ~~~(args.headD 0)]
      ∀ (a b : Fin 9) (gs : List (Fin 3 × List (Fin 25))) (out : Fin 25),
        10 * min a.val b.val + max a.val b.val ∈ ([13,15,17,18,25,26,28,35,36,37,56,67,78] : List ℕ) →
        gs.length ≤ 13 → (∀ g ∈ gs, g.2.length ≤ 2) →
        (∀ i : Fin 25, i.val < 9 → ∃ g ∈ gs,
          i ∈ (if g.1 = 2 then g.2.take 1 else g.2)) →
        let initial := raw ++ [raw.getD 0 0 ||| raw.getD 4 0, raw.getD a.val 0 ||| raw.getD b.val 0]
        let final := gs.foldl step initial
        final.getD out.val 0 ≠ 316380210352264264) :
    ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x11 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)), x11 x1 || x11 x2]) = (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)))) → False := by
  intro a b C ha0 ha4 hb0 hb4 hab fan hsize result
  have hSize : C.gates.length ≤ 13 := hsize
  let target (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let bank (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4, x a || x b]
  change ∀ x, C.eval (bank x) = target x at result
  let rawWords : List (BitVec 59) :=
    [360930119642124586, 432486920269079116, 293578547141297264,
      289365901620316032, 439119665042618368, 297239789478805504,
      306275578149863424, 540467122476679168, 576425567931334656]
  let initial := rawWords ++
    [rawWords.getD 0 0 ||| rawWords.getD 4 0, rawWords.getD a.val 0 ||| rawWords.getD b.val 0]
  let rows : List ℕ :=
    [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36,
      40, 42, 48, 50, 64, 65, 66, 68, 69, 72, 80, 96, 104, 116, 128, 129, 130,
      132, 136, 138, 144, 160, 192, 201, 208, 256, 257, 258, 260, 261, 264, 272,
      276, 288, 320, 384, 385, 402, 511]
  let row (r : Fin 59) (i : Fin 9) : Bool := (rows.getD r.val 0).testBit i.val
  have bits (r : Fin 59) (as : List (BitVec 59)) :
      let bs := as.map fun v => v.getLsbD r.val
      (as.foldr (· &&& ·) (~~~0)).getLsbD r.val = bs.all id ∧
      (as.foldr (· ||| ·) 0).getLsbD r.val = bs.any id ∧
      (~~~(as.headD 0)).getLsbD r.val = !(bs.headD false) := by
    have rb := r.isLt
    induction as with
    | nil =>
      have hz : (0 : BitVec 59).getLsbD r.val = false := BitVec.getLsbD_zero
      have ho : (~~~(0 : BitVec 59)).getLsbD r.val = true := by
        rw [BitVec.getLsbD_not, hz]
        simp [rb]
      exact ⟨ho, hz, ho⟩
    | cons v rest ih =>
      obtain ⟨qa, qo, _⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · change (v &&& rest.foldr (· &&& ·) (~~~0)).getLsbD r.val =
          (v.getLsbD r.val && (rest.map fun w => w.getLsbD r.val).all id)
        rw [BitVec.getLsbD_and, qa]
      · change (v ||| rest.foldr (· ||| ·) 0).getLsbD r.val =
          (v.getLsbD r.val || (rest.map fun w => w.getLsbD r.val).any id)
        rw [BitVec.getLsbD_or, qo]
      · change (~~~v).getLsbD r.val = !(v.getLsbD r.val)
        rw [BitVec.getLsbD_not]
        simp [rb]
  let _ : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let word (g : Gate) : Fin 3 :=
    if g.op = GateOp.and then 0 else if g.op = GateOp.or then 1 else 2
  let cap (j : ℕ) : Fin 25 := ⟨min j 24, lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)⟩
  let enc (g : Gate) : Fin 3 × List (Fin 25) := (word g, g.inputs.map cap)
  let step := fun (ws : List (BitVec 59)) (g : Fin 3 × List (Fin 25)) =>
    let args := g.2.map fun i => ws.getD i.val 0
    ws ++ [if g.1 = 0 then args.foldr (· &&& ·) (~~~0)
      else if g.1 = 1 then args.foldr (· ||| ·) 0 else ~~~(args.headD 0)]
  let scalar (bs : List Bool) (g : Gate) :=
    bs ++ [g.op.eval (g.inputs.map (fun j => bs.getD j false))]
  have knownOp (g : Gate) (hg : g ∈ C.gates) :
      g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (fan g hg).1
  have clamp {bs : List Bool} (hLen : bs.length ≤ 24) (j : ℕ) :
      bs.getD (cap j).val false = bs.getD j false := by
    by_cases h : j ≤ 24
    · simp [cap, Nat.min_eq_left h]
    · have ha : bs.length ≤ min j 24 := by omega
      have hb : bs.length ≤ j := by omega
      change bs.getD (min j 24) false = bs.getD j false
      rw [List.getD_eq_default _ _ ha, List.getD_eq_default _ _ hb]
  have bitAppend (ws : List (BitVec 59)) (a : BitVec 59) (r : Fin 59) :
      (ws ++ [a]).map (fun u => u.getLsbD r.val) =
        ws.map (fun u => u.getLsbD r.val) ++ [a.getLsbD r.val] := by simp
  have indexed (ws : List (BitVec 59)) (r : Fin 59) (j : ℕ) :
      ((ws.map fun u => u.getLsbD r.val).getD j false) = (ws.getD j 0).getLsbD r.val := by
    induction ws generalizing j with
    | nil => exact BitVec.getLsbD_zero.symm
    | cons a ws ih =>
      cases j with
      | zero => rfl
      | succ j => simpa only [List.map_cons, List.getD_cons_succ] using ih j
  have stepBits (ws : List (BitVec 59)) (r : Fin 59) (hLen : ws.length ≤ 24)
      (g : Gate) (hg : g ∈ C.gates) :
      (step ws (enc g)).map (fun u => u.getLsbD r.val) =
        scalar (ws.map fun u => u.getLsbD r.val) g := by
    let bs := ws.map fun u => u.getLsbD r.val
    let args := (g.inputs.map cap).map (fun i => ws.getD i.val 0)
    have translate :
        args.map (fun u => u.getLsbD r.val) = g.inputs.map (fun j => bs.getD j false) := by
      simp only [args, List.map_map]
      apply List.map_congr_left
      intro j _
      change (ws.getD (cap j).val 0).getLsbD r.val = bs.getD j false
      rw [← indexed, clamp (by simpa [bs] using hLen)]
    change (ws ++ [_]).map (fun u : BitVec 59 => u.getLsbD r.val) = bs ++ [_]
    rw [bitAppend]
    congr 2
    change (if word g = 0 then args.foldr (· &&& ·) (~~~0)
      else if word g = 1 then args.foldr (· ||| ·) 0 else ~~~(args.headD 0)).getLsbD r.val =
      g.op.eval (g.inputs.map (fun j => bs.getD j false))
    rcases knownOp g hg with h | h | h
    · rw [show word g = 0 by simp [word, h], ite_eq_left rfl, (bits r args).1, translate, h]
      rfl
    · rw [show word g = 1 by simp [word, h], ite_eq_right (by decide), ite_eq_left rfl,
        (bits r args).2.1, translate, h]
      rfl
    · rw [show word g = 2 by simp [word, h], ite_eq_right (by decide), ite_eq_right (by decide),
        (bits r args).2.2, translate, h]
      rfl
  have runBits (gs : List Gate) (hmem : ∀ g ∈ gs, g ∈ C.gates)
      (ws : List (BitVec 59)) (hb : ws.length + gs.length ≤ 24) (r : Fin 59) :
      ((gs.map enc).foldl step ws).map (fun u => u.getLsbD r.val) =
        gs.foldl scalar (ws.map fun u => u.getLsbD r.val) := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g rest ih =>
      change ((rest.map enc).foldl step (step ws (enc g))).map (fun u => u.getLsbD r.val) =
        rest.foldl scalar (scalar (ws.map fun u => u.getLsbD r.val) g)
      rw [ih (fun j hj => hmem j (List.mem_cons_of_mem _ hj))]
      · rw [stepBits ws r (by simp at hb; omega) g (hmem g (by simp))]
      · simp [step] at hb ⊢
        omega
  have rawBits (r : Fin 59) : rawWords.map (fun u => u.getLsbD r.val) = List.ofFn (row r) := by
    revert r
    decide
  have rawBit (r : Fin 59) (j : Fin 9) :
      (rawWords.getD j.val 0).getLsbD r.val = row r j := by
    rw [← indexed, rawBits]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have initialBits (r : Fin 59) :
      initial.map (fun u => u.getLsbD r.val) = bank (row r) := by
    have h0 : (rawWords.getD 0 0).getLsbD r.val = row r 0 := rawBit r 0
    have h4 : (rawWords.getD 4 0).getLsbD r.val = row r 4 := rawBit r 4
    simp only [initial, List.map_append, List.map_cons, List.map_nil, BitVec.getLsbD_or,
      h0, h4, rawBit, rawBits, bank]
  have targetBits (r : Fin 59) :
      (316380210352264264 : BitVec 59).getLsbD r.val = target (row r) := by
    revert r
    decide
  let gs := C.gates.map enc
  let final := gs.foldl step initial
  have resulting (r : Fin 59) :
      final.map (fun u => u.getLsbD r.val) = C.wires (bank (row r)) := by
    change ((C.gates.map enc).foldl step initial).map (fun u => u.getLsbD r.val) = _
    rw [runBits C.gates (fun _ h => h) initial (by change 11 + C.gates.length ≤ 24; omega), initialBits]
    rfl
  have wireLength (l : List Gate) (v : List Bool) :
      (l.foldl scalar v).length = v.length + l.length := by
    induction l generalizing v with
    | nil => simp
    | cons g rest ih =>
      change (rest.foldl scalar (scalar v g)).length = v.length + (g :: rest).length
      rw [ih]
      simp [scalar]
      omega
  have outLen (r : Fin 59) : (C.wires (bank (row r))).length ≤ 24 := by
    change (C.gates.foldl scalar (bank (row r))).length ≤ 24
    rw [wireLength]
    simp [bank]
    omega
  have size : gs.length ≤ 13 := by simpa [gs] using hSize
  have arity : ∀ g ∈ gs, g.2.length ≤ 2 := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨orig, horig, rfl⟩
    simpa [enc] using (fan orig horig).2
  have pinned : ∀ i : Fin 25, i.val < 9 → ∃ g ∈ gs,
      i ∈ (if g.1 = 2 then g.2.take 1 else g.2) := by
    intro i hi
    obtain ⟨g, hg, reads⟩ := pinsRead a b C ha0 ha4 hb0 hb4 hab fan result ⟨i.val, hi⟩
    have opSem : g.op.eval [false, false] = decide (word g = 2) := by
      rcases knownOp g hg with h | h | h
      · have hc : word g = 0 := by simp [word, h]
        rw [h, hc]; rfl
      · have hc : word g = 1 := by simp [word, h]
        rw [h, hc]; rfl
      · have hc : word g = 2 := by simp [word, h]
        rw [h, hc]; rfl
    have hraw : i.val ∈ (if word g = 2 then g.inputs.take 1 else g.inputs) := by
      rw [opSem] at reads
      simpa only [decide_eq_true_eq] using reads
    refine ⟨enc g, List.mem_map.mpr ⟨g, hg, rfl⟩, ?_⟩
    have hcap : cap i.val = i := by
      apply Fin.ext
      change min i.val 24 = i.val
      exact Nat.min_eq_left (by omega)
    change i ∈ (if word g = 2 then (g.inputs.map cap).take 1 else g.inputs.map cap)
    by_cases op : word g = 2
    · have raw : i.val ∈ g.inputs.take 1 := by simpa only [op, ite_true] using hraw
      rw [ite_eq_left op, ← List.map_take]
      exact List.mem_map.mpr ⟨i.val, raw, hcap⟩
    · have raw : i.val ∈ g.inputs := by simpa only [op, ite_false] using hraw
      rw [ite_eq_right op]
      exact List.mem_map.mpr ⟨i.val, raw, hcap⟩
  have cover : ∀ u v : Fin 9, u ≠ 0 → u ≠ 4 → v ≠ 0 → v ≠ 4 → u ≠ v →
      10 * min u.val v.val + max u.val v.val ∈ ([12,16,23,27,38,57,58,68] : List ℕ) ∨
      10 * min u.val v.val + max u.val v.val ∈ ([13,15,17,18,25,26,28,35,36,37,56,67,78] : List ℕ) := by
    decide
  have trace : final.getD (cap C.output).val 0 = 316380210352264264 := by
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    let r : Fin 59 := ⟨n, hn⟩
    change (final.getD (cap C.output).val 0).getLsbD r.val = _
    rw [← indexed, resulting, clamp (outLen r), targetBits r]
    exact result (row r)
  rcases cover a b ha0 ha4 hb0 hb4 hab with hn | hf
  · exact near a b gs (cap C.output) hn size arity pinned trace
  · exact far a b gs (cap C.output) hf size arity pinned trace
