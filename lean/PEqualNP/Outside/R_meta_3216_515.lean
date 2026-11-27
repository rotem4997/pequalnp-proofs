import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3216_515
    (h1 : ∀ (a m t : List Gate) (g h : Gate) (o : Nat),
  let C : Circuit := ⟨a ++ g :: (m ++ h :: t),o⟩
  FanInTwo C →
  (∀ k ∈ C.gates, k.op = .not → k.inputs.length ≤ 1) →
  (∀ k ∈ a ++ m ++ t, 0 ∉ k.inputs ∧ 9 ∉ k.inputs) →
  (∀ k ∈ [g,h], 0 ∈ k.inputs ∨ 9 ∈ k.inputs) →
  (∀ d b z : Bool, C.eval [b,d,false,!d,z,false,false,false,false,!b] =
      (if d then b else z)) →
  ∃ k ∈ a ++ m ++ t, 4 ∈ k.inputs)
    (h2 : ∀ C : Circuit, FanInTwo C →
  (∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) →
  (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) =
    ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any
      (fun e => x (Fin.ofNat 9 (e/9)) && x (Fin.ofNat 9 (e % 9)))) →
  15 ≤ (C.gates.foldl (fun w g => w ++ [1 + (g.inputs.map fun j => w.getD j 0).sum])
      (List.replicate 10 0)).getD C.output 0)
    (h3 : ∀ (a m t : List Gate) (g h : Gate) (o : Nat),
  let C : Circuit := ⟨a ++ g :: (m ++ h :: t),o⟩
  FanInTwo C → a.length + m.length + t.length = 12 → o < 24 →
  (∀ k ∈ C.gates, (k.op = .not → k.inputs.length ≤ 1) ∧ ∀ j ∈ k.inputs, j ≤ 24) →
  (∀ k ∈ a ++ m ++ t, 0 ∉ k.inputs ∧ 9 ∉ k.inputs) →
  ((a ++ m ++ t).filter fun k => k.inputs.contains 4).length = 1 →
  (∀ k ∈ [g,h], 0 ∈ k.inputs ∨ 9 ∈ k.inputs) →
  15 ≤ (C.gates.foldl (fun w g => w ++ [1 + (g.inputs.map fun j => w.getD j 0).sum])
      (List.replicate 10 0)).getD C.output 0 →
  (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) =
    ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any
      (fun e => x (Fin.ofNat 9 (e/9)) && x (Fin.ofNat 9 (e % 9)))) → False) :
    ∀ (x1 x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → x1.length + x2.length + x3.length = (12 : ℕ) → x6 < (24 : ℕ) → (∀ x11 ∈ x7.gates, (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not → x11.inputs.length ≤ (1 : ℕ)) ∧ ∀ x13 ∈ x11.inputs, x13 ≤ (24 : ℕ)) → (∀ x12 ∈ x1 ++ x2 ++ x3, (0 : ℕ) ∉ x12.inputs ∧ (9 : ℕ) ∉ x12.inputs) → (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.inputs.contains (4 : ℕ)) (x1 ++ x2 ++ x3)).length ≤ (1 : ℕ) → (∀ x14 ∈ [x4, x5], (0 : ℕ) ∈ x14.inputs ∨ (9 : ℕ) ∈ x14.inputs) → (∀ (x15 : Fin (8 : ℕ) → Bool), x7.eval (Bool.false :: List.ofFn x15 ++ [Bool.true]) = [(1 : ℕ), (10 : ℕ), (19 : ℕ), (5 : ℕ), (14 : ℕ), (23 : ℕ), (38 : ℕ), (47 : ℕ), (60 : ℕ)].any fun (x16 : ℕ) => x15 (Fin.ofNat (8 : ℕ) (x16 / (8 : ℕ))) && x15 (Fin.ofNat (8 : ℕ) (x16 % (8 : ℕ)))) → ∃ (x16 : Fin (8 : ℕ) → Bool), x7.eval (Bool.true :: List.ofFn x16 ++ [Bool.false]) ≠ (x16 (0 : Fin (8 : ℕ)) || x16 (3 : Fin (8 : ℕ)) || x16 (4 : Fin (8 : ℕ)) || x16 (1 : Fin (8 : ℕ)) && x16 (2 : Fin (8 : ℕ)) || x16 (1 : Fin (8 : ℕ)) && x16 (6 : Fin (8 : ℕ)) || x16 (2 : Fin (8 : ℕ)) && x16 (7 : Fin (8 : ℕ)) || x16 (5 : Fin (8 : ℕ)) && x16 (7 : Fin (8 : ℕ))) := by
  intro a m t g h o C model len out bounds avoids sparse control lo
  by_contra! hi
  let bits (d z : Bool) (k : Fin 8) :=
    if k = 0 then d else if k = 2 then !d else if k = 3 then z else false
  have mux (d b z : Bool) :
      C.eval [b,d,false,!d,z,false,false,false,false,!b] = (if d then b else z) := by
    cases b with
    | false =>
      change C.eval (false :: List.ofFn (bits d z) ++ [true]) = _
      rw [lo]
      cases d <;> cases z <;> rfl
    | true =>
      change C.eval (true :: List.ofFn (bits d z) ++ [false]) = _
      rw [hi]
      cases d <;> cases z <;> rfl
  obtain ⟨g₀,hg₀,read⟩ := h1 a m t g h o model (fun k hk => (bounds k hk).1) avoids control mux
  have mem : g₀ ∈ ((a ++ m ++ t).filter fun k => k.inputs.contains 4) :=
    List.mem_filter.mpr ⟨hg₀,by simpa using read⟩
  have pos := List.length_pos_of_mem mem
  have eq1 : ((a ++ m ++ t).filter fun k => k.inputs.contains 4).length = 1 := by omega
  have full : (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) =
    ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any
      (fun e => x (Fin.ofNat 9 (e/9)) && x (Fin.ofNat 9 (e % 9)))) := by
    intro q
    let u (i : Fin 8) := q i.succ
    have row : List.ofFn q ++ [!q 0] = q 0 :: List.ofFn u ++ [!q 0] := by rfl
    rw [row]
    cases e : q 0
    · change C.eval (false :: List.ofFn u ++ [true]) = _
      rw [lo u]
      change ((q 1 && q 2) || ((q 2 && q 3) || ((q 3 && q 4) || ((q 1 && q 6) ||
        ((q 2 && q 7) || ((q 3 && q 8) || ((q 5 && q 7) || ((q 6 && q 8) || ((q 8 && q 5) || false))))))))) =
        ((q 0 && q 1) || ((q 1 && q 2) || ((q 2 && q 3) || ((q 3 && q 4) ||
        ((q 4 && q 0) || ((q 0 && q 5) || ((q 1 && q 6) || ((q 2 && q 7) ||
        ((q 3 && q 8) || ((q 5 && q 7) || ((q 6 && q 8) || ((q 8 && q 5) || false))))))))))))
      simp [e]
    · change C.eval (true :: List.ofFn u ++ [false]) = _
      rw [hi u]
      change (q 1 || q 4 || q 5 || q 2 && q 3 || q 2 && q 7 || q 3 && q 8 || q 6 && q 8) =
        ((q 0 && q 1) || ((q 1 && q 2) || ((q 2 && q 3) || ((q 3 && q 4) ||
        ((q 4 && q 0) || ((q 0 && q 5) || ((q 1 && q 6) || ((q 2 && q 7) ||
        ((q 3 && q 8) || ((q 5 && q 7) || ((q 6 && q 8) || ((q 8 && q 5) || false))))))))))))
      grind
  exact h3 a m t g h o model len out bounds avoids eq1 control
    (h2 C model (fun k hk => (bounds k hk).1) full) full
