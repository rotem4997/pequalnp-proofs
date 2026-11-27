import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_4727_214
    (atEdge : ∀ (g : Gate) (D : Circuit), FanInTwo ⟨[g], 0⟩ →
      (∀ i ∈ g.inputs, i = 0 ∨ i = 1 ∨ i = 10) →
      FanInTwo D → D.size ≤ 18 →
      1 ≤ notCount ⟨[g], 0⟩ + notCount D → notCount ⟨[g], 0⟩ + notCount D ≤ 4 →
      ¬ ∀ x : Fin 10 → Bool,
        D.eval (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)]) =
        ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))))
    (awayFromEdge : ∀ (g : Gate) (D : Circuit), FanInTwo ⟨[g], 0⟩ →
      2 ∈ g.inputs → (∀ i ∈ g.inputs, i = 0 ∨ i = 2 ∨ i = 10) →
      FanInTwo D → D.size ≤ 18 →
      1 ≤ notCount ⟨[g], 0⟩ + notCount D → notCount ⟨[g], 0⟩ + notCount D ≤ 4 →
      ¬ ∀ x : Fin 10 → Bool,
        D.eval (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)]) =
        ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (19 : ℕ) → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x2 → PEqualNP.NotBracket.notCount x2 ≤ (4 : ℕ) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7 := by
  intro f C legal budget minNeg maxNeg correct
  let edges : List (Fin 10 × Fin 10) :=
    [(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
  let edgeFun (x : Fin 10 → Bool) := edges.any fun e => x e.1 && x e.2
  have posted (x : Fin 10 → Bool) : f x = edgeFun x := by
    dsimp only [f, edgeFun, edges, List.any_cons, List.any_nil]
    simp only [Bool.or_false]
    ac_rfl
  have encoded (x : Fin 10 → Bool) : ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))) = edgeFun x := by
    rw [← posted x]
    dsimp only [f, List.any_cons, List.any_nil]
    simp only [Bool.or_false, Bool.or_assoc]
    rfl
  let codes : List ℕ :=
    [9876543210,815643279,8035461279,8253761049,3182640579,1302468579,1520768349,9374268501,
     9547068321,5987604321,9267143850,2937416850,251743869,2031475869,2813675049,954716832,
     9064175832,9846375012,3528740169,5308472169,5180672349,9364872105,9146072385,1926704385,
     6598710432,5608179432,5480379612,2631879405,2413079685,4293701685,3782549610,3628149750,
     6398412750,715249683,651849723,7095421683,7659821043,6091485723,6719285043,354812796,
     3024185796,3742985016,9176240583,9567840123,1906427583,1560827943,5907486123,5170286943,
     3984627501,3548027961,5378204961,3924786105,3142086975,1362804975,2537810496,5207183496,
     5470983216,6291783405,6419083275,4639801275]
  let perm (s : Fin 60) (i : Fin 10) := Fin.ofNat 10 (codes.getD s.val 0 / 10 ^ i.val)
  let ordered (a b : Fin 10) := (min a b, max a b)
  have orbit : ∀ i j : Fin 10, ∃ s : Fin 60, perm s i = 0 ∧
      (perm s j = 0 ∨ perm s j = 1 ∨ perm s j = 2) := by
    dsimp only [perm, codes]
    decide +kernel
  have preserves : ∀ s : Fin 60,
      (edges.map (fun e => ordered (perm s e.1) (perm s e.2))).toFinset = edges.toFinset := by
    dsimp only [edges, ordered, perm, codes]
    decide +kernel
  have invariant (s : Fin 60) (x : Fin 10 → Bool) :
      edgeFun (fun i => x (perm s i)) = edgeFun x := by
    let moved := edges.map (fun e => ordered (perm s e.1) (perm s e.2))
    have member (e : Fin 10 × Fin 10) : e ∈ moved ↔ e ∈ edges := by
      simpa only [List.mem_toFinset] using Finset.ext_iff.mp (preserves s) e
    have obs (a b : Fin 10) : (x (ordered a b).1 && x (ordered a b).2) = (x a && x b) := by
      rcases le_total a b with h | h
      · simp [ordered, min_eq_left h, max_eq_right h]
      · simp [ordered, min_eq_right h, max_eq_left h, Bool.and_comm]
    have equal : (moved.any (fun e => x e.1 && x e.2)) = edgeFun x := by
      rw [Bool.eq_iff_iff]
      simp only [edgeFun, List.any_eq_true, member]
    simpa only [moved, List.any_map, Function.comp_def, obs, edgeFun] using equal
  obtain ⟨g, tail, gates⟩ : ∃ g t, C.gates = g :: t := by
    cases h : C.gates with
    | nil =>
      change 1 ≤ (C.gates.filter _).length at minNeg
      simp [h] at minNeg
    | cons g t => exact ⟨g, t, rfl⟩
  have firstLegal := legal g (gates ▸ List.mem_cons_self ..)
  have operand (i : ℕ) (hi : i ∈ g.inputs) :
      i = g.inputs.getD 0 0 ∨ i = g.inputs.getD 1 0 := by
    have hlen := firstLegal.2
    generalize hin : g.inputs = ins at hlen hi ⊢
    cases ins with
    | nil => simp at hi
    | cons a rest =>
      cases rest with
      | nil => exact Or.inl (by simpa using hi)
      | cons b rest =>
        cases rest with
        | nil => simpa using hi
        | cons c rest => simp at hlen
  obtain ⟨s, hfirst, hsecond⟩ := orbit (Fin.ofNat 10 (g.inputs.getD 0 0))
    (Fin.ofNat 10 (g.inputs.getD 1 0))
  let wire (i : ℕ) := if h : i < 10 then (perm s ⟨i, h⟩).val else i
  let headWire (i : ℕ) := if h : i < 10 then (perm s ⟨i, h⟩).val else 10
  let q : Gate := ⟨g.op, g.inputs.map headWire⟩
  let rename (a : Gate) : Gate := ⟨a.op, a.inputs.map wire⟩
  let D : Circuit := ⟨tail.map rename, wire C.output⟩
  let second := (perm s (Fin.ofNat 10 (g.inputs.getD 1 0))).val
  have support (i) (hi : i ∈ q.inputs) : i = 0 ∨ i = second ∨ i = 10 := by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    by_cases h : j < 10
    · have fin : (⟨j, h⟩ : Fin 10) = Fin.ofNat 10 j := by
        apply Fin.ext
        exact (Nat.mod_eq_of_lt h).symm
      simp only [headWire, dite_eq_left h, fin]
      rcases operand j hj with left | right
      · rw [left, hfirst]
        exact Or.inl rfl
      · exact Or.inr (Or.inl (by rw [right]))
    · simp [headWire, h]
  have qLegal : FanInTwo ⟨[q], 0⟩ := by
    intro a ha
    have eq : a = q := List.mem_singleton.mp ha
    subst a
    exact ⟨firstLegal.1, by simpa [q] using firstLegal.2⟩
  have dLegal : FanInTwo D := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have good := legal b (gates ▸ List.mem_cons_of_mem _ hb)
    exact ⟨good.1, by simpa [rename] using good.2⟩
  have small : D.size ≤ 18 := by
    change C.gates.length ≤ 19 at budget
    rw [gates, List.length_cons] at budget
    change (tail.map rename).length ≤ 18
    rw [List.length_map]
    omega
  have counts : notCount ⟨[q], 0⟩ + notCount D = notCount C := by
    let neg (a : Gate) := @decide (a.op = GateOp.not) (lineDegreeGateOpDecEq a.op GateOp.not)
    change ([q].filter neg).length + ((tail.map rename).filter neg).length = (C.gates.filter neg).length
    simp only [gates, q, neg, List.filter_map, Function.comp_def, List.length_map,
      rename, List.filter_cons, List.filter_nil]
    split <;> simp [Nat.add_comm]
  have runs (x : Fin 10 → Bool) :
      D.eval (List.ofFn x ++ [q.op.eval (q.inputs.map fun i => (List.ofFn x).getD i false)]) =
      C.eval (List.ofFn (fun j => x (perm s j))) := by
    let old := List.ofFn (fun j => x (perm s j))
    let newInputs := List.ofFn x
    have lookup (w : List Bool) (i : ℕ) :
        (newInputs ++ w).getD (wire i) false = (old ++ w).getD i false := by
      by_cases hi : i < 10
      · have hw : wire i < newInputs.length := by simp [wire, hi, newInputs]
        have ho : i < old.length := by simpa [old] using hi
        rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ ho,
          List.getD_eq_getElem _ _ hw, List.getD_eq_getElem _ _ ho]
        simp only [newInputs, old, wire, dite_eq_left hi, List.getElem_ofFn]
      · have hn : newInputs.length ≤ i := by simpa [newInputs] using Nat.le_of_not_gt hi
        have ho : old.length ≤ i := by simpa [old] using Nat.le_of_not_gt hi
        rw [show wire i = i by simp [wire, hi], List.getD_append_right _ _ _ _ hn,
          List.getD_append_right _ _ _ _ ho]
        simp [old, newInputs]
    have raw (i : ℕ) : newInputs.getD (headWire i) false = old.getD i false := by
      by_cases hi : i < 10
      · simpa [headWire, wire, hi] using lookup [] i
      · rw [show headWire i = 10 by simp [headWire, hi]]
        rw [List.getD_eq_default _ _ (by simp [newInputs]),
          List.getD_eq_default _ _ (by simpa [old] using Nat.le_of_not_gt hi)]
    let firstValue := g.op.eval (g.inputs.map fun i => old.getD i false)
    have firstEq : q.op.eval (q.inputs.map fun i => newInputs.getD i false) = firstValue := by
      simp only [q, firstValue, List.map_map, Function.comp_def, raw]
    let step := fun (w : List Bool) (a : Gate) =>
      w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]
    have replay (t : List Gate) (w : List Bool) :
        ((t.map rename).foldl step (newInputs ++ w)).getD (wire C.output) false =
        (t.foldl step (old ++ w)).getD C.output false := by
      induction t generalizing w with
      | nil => exact lookup w C.output
      | cons a rest ih =>
        simp only [List.map_cons, List.foldl_cons]
        have go : (rename a).op.eval ((rename a).inputs.map fun i => (newInputs ++ w).getD i false) =
            a.op.eval (a.inputs.map fun i => (old ++ w).getD i false) := by
          simp only [rename, List.map_map, Function.comp_def, lookup]
        simpa only [step, go, List.append_assoc] using
          ih (w ++ [a.op.eval (a.inputs.map fun i => (old ++ w).getD i false)])
    change ((tail.map rename).foldl step (newInputs ++ [_])).getD (wire C.output) false =
      (C.gates.foldl step old).getD C.output false
    rw [firstEq, gates, List.foldl_cons]
    exact replay tail [firstValue]
  have allRows (x : Fin 10 → Bool) :
      D.eval (List.ofFn x ++ [q.op.eval (q.inputs.map fun i => (List.ofFn x).getD i false)]) =
      ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))) :=
    (runs x).trans ((correct (fun j => x (perm s j))).trans
      ((posted (fun j => x (perm s j))).trans ((invariant s x).trans (encoded x).symm)))
  have secondCases : second = 0 ∨ second = 1 ∨ second = 2 := by
    rcases hsecond with h | h | h
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (Or.inl (congrArg Fin.val h))
    · exact Or.inr (Or.inr (congrArg Fin.val h))
  by_cases used : 2 ∈ q.inputs
  · have hs := support 2 used
    have hs2 : second = 2 := by omega
    exact awayFromEdge q D qLegal used (fun i hi => hs2 ▸ support i hi)
      dLegal small (counts ▸ minNeg) (counts ▸ maxNeg) allRows
  · apply atEdge q D qLegal _ dLegal small (counts ▸ minNeg) (counts ▸ maxNeg) allRows
    intro i hi
    have h := support i hi
    have ne : i ≠ 2 := by intro e; exact used (e ▸ hi)
    omega
