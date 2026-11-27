import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Normalize the two OR operands by absorption and by the four Petersen
-- automorphisms preserving the unordered pair of inputs zero and two.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_4815_31
  (finite : let z : Fin 1024 → Bool := fun _ => false
    let bit := fun (a i : ℕ) => a.testBit i
    let t := fun (i : ℕ) (r : Fin 1024) =>
      if i < 10 then bit r.val i else if i = 10 then bit r.val 0 && bit r.val 2 else false
    let goal := fun r : Fin 1024 =>
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any fun e => bit r.val (e / 10) && bit r.val (e % 10)
    ∀ c ∈ ([0, 1, 2, 3, 4, 6, 8, 13, 15, 18, 20, 22, 39, 40, 41, 42, 43, 44, 45, 46, 78, 80, 82, 104, 105, 106, 130, 143] : List ℕ),
      let s := List.ofFn (fun i : Fin 10 => t i.val) ++ [t 10, fun r => t (c / 12) r || t (c % 12) r]
      ∀ (d : List (Fin 1024 → Bool)), d.length ≤ 17 →
        (∀ j < d.length, ∃ a b : Fin 1024 → Bool,
          let l := s ++ d.take j
          (a ∈ l ∨ a = z) ∧ (b ∈ l ∨ b = z) ∧
          let v := d.getD j z
          (v = fun r => a r && b r) ∨ (v = fun r => a r || b r) ∨ (v = fun r => !(a r))) →
        goal ∉ s ++ d)
  (compile : ∀ (n : ℕ) (s : List (Fin n → Bool)) (C : Circuit), FanInTwo C →
    ∃ d : List (Fin n → Bool), d.length = C.size ∧
      (∀ j < d.length, ∃ a b : ℕ,
        let A := (s ++ d.take j).getD a (fun _ => false)
        let B := (s ++ d.take j).getD b (fun _ => false)
        let v := d.getD j (fun _ => false)
        (v = fun r => A r && B r) ∨ (v = fun r => A r || B r) ∨ (v = fun r => !(A r))) ∧
      ∀ r, C.eval (s.map (fun v => v r)) = ((s ++ d).getD C.output (fun _ => false)) r) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (12 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ (x6 : Fin (10 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))];           x1.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : Fin (12 : ℕ)) => x7.getD (↑x8) Bool.false) x2)]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x6 := by
  intro C pins fan budget arity
  let pre (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 && x 2]
  let target (x : Fin 10 → Bool) :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
    (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let sample (r : Fin 1024) (i : Fin 10) := r.val.testBit i.val
  let t (i : ℕ) (r : Fin 1024) :=
    if i < 10 then r.val.testBit i else if i = 10 then r.val.testBit 0 && r.val.testBit 2 else false
  let goal (r : Fin 1024) :=
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any fun e => r.val.testBit (e / 10) && r.val.testBit (e % 10)
  let z : Fin 1024 → Bool := fun _ => false
  let perms : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    [0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
    [2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
    [2, 1, 0, 5, 7, 3, 6, 4, 8, 9]]
  let σ (p : Fin 4) (i : Fin 10) : Fin 10 := Fin.ofNat 10 ((perms.getD p.val []).getD i.val 0)
  let bend (p : Fin 4) (i : Fin 12) : ℕ :=
    if h : i.val < 10 then (σ p ⟨i.val, h⟩).val else i.val
  let code (a b : ℕ) :=
    if a = 11 then b * 12 + b
    else if b = 11 then a * 12 + a
    else if b = 10 ∧ (a = 0 ∨ a = 2) then a * 12 + a
    else if a = 10 ∧ (b = 0 ∨ b = 2) then b * 12 + b
    else min a b * 12 + max a b
  let codes : List ℕ := [0, 1, 2, 3, 4, 6, 8, 13, 15, 18, 20, 22, 39, 40, 41, 42, 43, 44, 45, 46, 78, 80, 82, 104, 105, 106, 130, 143]
  have pick : ∀ a b : Fin 12, ∃ p : Fin 4, code (bend p a) (bend p b) ∈ codes := by
    decide +kernel
  have either (p : Fin 4) :
      (σ p 0 = 0 ∧ σ p 2 = 2) ∨ (σ p 0 = 2 ∧ σ p 2 = 0) := by
    revert p
    decide +kernel
  have invariant : ∀ (p : Fin 4) (r : Fin 1024), target (sample r ∘ σ p) = goal r := by
    decide +kernel
  have width (p : Fin 4) (i : Fin 12) : bend p i < 12 := by
    by_cases h : i.val < 10
    · have b := (σ p ⟨i.val, h⟩).isLt
      simpa only [bend, h, dite_eq_left] using b.trans (show 10 < 12 by decide)
    · have q : bend p i = i.val := dite_eq_right h
      rw [q]
      exact i.isLt
  have encode (a b : ℕ) (hb : b < 12) (r : Fin 1024) :
      (t ((a * 12 + b) / 12) r || t ((a * 12 + b) % 12) r) = (t a r || t b r) := by
    rw [show (a * 12 + b) / 12 = a by omega, show (a * 12 + b) % 12 = b by omega]
  have absorb (a : ℕ) (ha : a = 0 ∨ a = 2) (r : Fin 1024) :
      (t a r || t 10 r) = t a r := by
    rcases ha with rfl | rfl
    · change (r.val.testBit 0 || (r.val.testBit 0 && r.val.testBit 2)) = r.val.testBit 0
      cases r.val.testBit 0 <;> rfl
    · change (r.val.testBit 2 || (r.val.testBit 0 && r.val.testBit 2)) = r.val.testBit 2
      cases r.val.testBit 2 <;> cases r.val.testBit 0 <;> rfl
  have normal (a b : ℕ) (ha : a < 12) (hb : b < 12) (r : Fin 1024) :
      (t (code a b / 12) r || t (code a b % 12) r) = (t a r || t b r) := by
    by_cases hA : a = 11
    · subst a
      dsimp only [code]
      rw [ite_eq_left rfl, encode b b hb r]
      change (t b r || t b r) = (false || t b r)
      simp
    by_cases hB : b = 11
    · subst b
      dsimp only [code]
      rw [ite_eq_right hA, ite_eq_left rfl, encode a a ha r]
      change (t a r || t a r) = (t a r || false)
      simp
    by_cases h : b = 10 ∧ (a = 0 ∨ a = 2)
    · dsimp only [code]
      rw [ite_eq_right hA, ite_eq_right hB, ite_eq_left h, encode a a ha r]
      rw [h.1, absorb a h.2 r]
      simp
    by_cases k : a = 10 ∧ (b = 0 ∨ b = 2)
    · dsimp only [code]
      rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right h, ite_eq_left k, encode b b hb r]
      rw [k.1, Bool.or_comm (t 10 r), absorb b k.2 r]
      simp
    · dsimp only [code]
      rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right h, ite_eq_right k]
      by_cases hab : a ≤ b
      · rw [min_eq_left hab, max_eq_right hab, encode a b hb r]
      · have hba : b ≤ a := by omega
        rw [min_eq_right hba, max_eq_left hba, encode b a ha r, Bool.or_comm]
  have preEval (p : Fin 4) (i : Fin 12) (r : Fin 1024) :
      (pre (sample r ∘ σ p)).getD i.val false = t (bend p i) r := by
    by_cases hi : i.val < 10
    · have h : i.val < (List.ofFn (sample r ∘ σ p)).length := by
        simpa only [List.length_ofFn] using hi
      change ((List.ofFn (sample r ∘ σ p)) ++ [_]).getD i.val false = _
      rw [List.getD_append _ _ _ _ h, List.getD_eq_getElem _ _ h, List.getElem_ofFn]
      have hσ := (σ p ⟨i.val, hi⟩).isLt
      simp only [sample, Function.comp_apply, bend, hi, dite_eq_left, t, hσ, ite_true]
    · have cases : i.val = 10 ∨ i.val = 11 := by omega
      rcases cases with h | h
      · have e : i = 10 := Fin.ext h
        subst i
        change (sample r (σ p 0) && sample r (σ p 2)) = (sample r 0 && sample r 2)
        rcases either p with ⟨h0, h2⟩ | ⟨h0, h2⟩ <;> simp [h0, h2, Bool.and_comm]
      · have e : i = 11 := Fin.ext h
        subst i
        rfl
  have twoPins (qs : List (Fin 12)) (h : qs.length ≤ 2) :
      ∃ a b : Fin 12, ∀ x : Fin 10 → Bool,
        GateOp.or.eval (qs.map (fun i => (pre x).getD i.val false)) =
          ((pre x).getD a.val false || (pre x).getD b.val false) := by
    have missing (x : Fin 10 → Bool) : (pre x).getD 11 false = false := by
      apply List.getD_eq_default
      simp [pre]
    rcases qs with _ | ⟨a, _ | ⟨b, tail⟩⟩
    · exact ⟨11, 11, fun x => by
        change false = ((pre x).getD 11 false || (pre x).getD 11 false)
        rw [missing]
        rfl⟩
    · exact ⟨a, 11, fun x => by
        change ((pre x).getD a.val false || false) =
          ((pre x).getD a.val false || (pre x).getD 11 false)
        rw [missing]⟩
    · have e : tail = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons] at h
        omega
      subst tail
      exact ⟨a, b, fun x => by
        change ((pre x).getD a.val false || ((pre x).getD b.val false || false)) = _
        rw [Bool.or_false]⟩
  obtain ⟨a, b, pair⟩ := twoPins pins arity
  obtain ⟨p, belongs⟩ := pick a b
  let k := code (bend p a) (bend p b)
  let roots := List.ofFn (fun i : Fin 10 => t i.val) ++ [t 10, fun r => t (k / 12) r || t (k % 12) r]
  let x (r : Fin 1024) := sample r ∘ σ p
  let seed := List.ofFn (fun i : Fin 10 => fun r => x r i) ++
    [fun r => x r 0 && x r 2, fun r => GateOp.or.eval (pins.map (fun i => (pre (x r)).getD i.val false))]
  have first : (fun r => x r 0 && x r 2) = t 10 := by
    funext r
    change (sample r (σ p 0) && sample r (σ p 2)) = (sample r 0 && sample r 2)
    rcases either p with ⟨h0, h2⟩ | ⟨h0, h2⟩ <;> simp [h0, h2, Bool.and_comm]
  have second : (fun r => GateOp.or.eval (pins.map (fun i => (pre (x r)).getD i.val false))) =
      fun r => t (k / 12) r || t (k % 12) r := by
    funext r
    rw [pair]
    change ((pre (sample r ∘ σ p)).getD a.val false ||
      (pre (sample r ∘ σ p)).getD b.val false) = _
    rw [preEval, preEval]
    exact (normal _ _ (width p a) (width p b) r).symm
  have included : seed ⊆ roots := by
    intro f hf
    change f ∈ _ ++ _ at hf
    change f ∈ _ ++ _
    rw [List.mem_append] at hf ⊢
    rcases hf with raw | f
    · left
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp raw
      apply List.mem_ofFn.mpr
      refine ⟨σ p i, ?_⟩
      funext r
      simp only [t, (σ p i).isLt, ite_true, x, sample, Function.comp_apply]
    · right
      rw [first, second] at f
      exact f
  have contains (s : List (Fin 1024 → Bool)) (i : ℕ) : s.getD i z ∈ s ∨ s.getD i z = z := by
    by_cases hi : i < s.length
    · exact Or.inl (List.getD_eq_getElem s z hi ▸ List.getElem_mem hi)
    · exact Or.inr (List.getD_eq_default _ _ (Nat.le_of_not_gt hi))
  have carry (tail : List (Fin 1024 → Bool)) {f : Fin 1024 → Bool}
      (h : f ∈ seed ++ tail ∨ f = z) : f ∈ roots ++ tail ∨ f = z := by
    rcases h with h | hz
    · apply Or.inl
      rw [List.mem_append] at h ⊢
      exact h.imp (fun h => included h) id
    · exact Or.inr hz
  have seedEval (r : Fin 1024) : seed.map (fun f => f r) =
      pre (x r) ++ [GateOp.or.eval (pins.map (fun i => (pre (x r)).getD i.val false))] := by
    simp only [seed, pre, List.map_append, List.map_ofFn, Function.comp_def, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append]
  obtain ⟨d, size, trace, ev⟩ := compile 1024 seed C fan
  have legal (j : ℕ) (hj : j < d.length) :
      ∃ a b : Fin 1024 → Bool, (a ∈ roots ++ d.take j ∨ a = z) ∧
        (b ∈ roots ++ d.take j ∨ b = z) ∧
          (d.getD j z = (fun r => a r && b r) ∨
           d.getD j z = (fun r => a r || b r) ∨ d.getD j z = (fun r => !(a r))) := by
    obtain ⟨a, b, step⟩ := trace j hj
    exact ⟨_, _, carry _ (contains _ a), carry _ (contains _ b), step⟩
  have notReach := finite k belongs d (size.trans_le budget) legal
  by_contra missing
  have reached : (seed ++ d).getD C.output z = goal := by
    funext r
    have h := ev r
    rw [seedEval r] at h
    have computes : C.eval (pre (x r) ++ [GateOp.or.eval (pins.map fun i => (pre (x r)).getD i.val false)]) =
        target (x r) := by
      by_contra ne
      exact missing ⟨x r, ne⟩
    exact h.symm.trans (computes.trans (invariant p r))
  have h := carry d (contains (seed ++ d) C.output)
  rw [reached] at h
  rcases h with member | impossible
  · exact notReach member
  · have diff : goal (3 : Fin 1024) ≠ z (3 : Fin 1024) := by decide +kernel
    exact diff (congrFun impossible 3)
