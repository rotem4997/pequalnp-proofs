import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem PEqualNP.Outside.R_meta_18019_641
    (hleft :
      let inc (p l : Fin 13) := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let row (p l : Fin 13) : Fin 26 → Bool := fun i =>
        decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
      let input (x : Fin 26 → Bool) := List.ofFn x ++ [x 0 || x 1]
      ∃ D : Circuit, D.size ≤ 28 ∧ 27 ≤ D.output ∧ D.output < 27 + D.size ∧
        IsAO2 27 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        (∀ p l : Fin 13, l ∈ ([12,1,4,5,10,11] : List (Fin 13)) → inc p l →
          D.eval (input (row p l)) = true) ∧
        ∀ x : Fin 26 → Bool, D.eval (input x) = true →
          ∃ p l : Fin 13, inc p l ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
    (hright :
      let inc (p l : Fin 13) := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let row (p l : Fin 13) : Fin 26 → Bool := fun i =>
        decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
      let input (x : Fin 26 → Bool) := List.ofFn x ++ [x 0 || x 1]
      ∃ D : Circuit, D.size ≤ 29 ∧ 27 ≤ D.output ∧ D.output < 27 + D.size ∧
        IsAO2 27 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        (∀ p l : Fin 13, l ∈ ([2,3,6,7,8,9] : List (Fin 13)) → inc p l →
          D.eval (input (row p l)) = true) ∧
        ∀ x : Fin 26 → Bool, D.eval (input x) = true →
          ∃ p l : Fin 13, inc p l ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) :
  (have x1 : List (ℕ × ℕ) := [((1 : ℕ), (1 : ℕ)), ((2 : ℕ), (1 : ℕ)), ((0 : ℕ), (8191 : ℕ)), ((1 : ℕ), (3054 : ℕ)), ((3 : ℕ), (972 : ℕ)), ((5 : ℕ), (2984 : ℕ)), ((7 : ℕ), (904 : ℕ)), ((11 : ℕ), (832 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((29 : ℕ), (2592 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((39 : ℕ), (392 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((71 : ℕ), (896 : ℕ)), ((83 : ℕ), (644 : ℕ)), ((85 : ℕ), (2688 : ℕ)), ((101 : ℕ), (2432 : ℕ)), ((133 : ℕ), (808 : ℕ)), ((135 : ℕ), (776 : ℕ)), ((141 : ℕ), (800 : ℕ)), ((161 : ℕ), (266 : ℕ)), ((207 : ℕ), (768 : ℕ)), ((349 : ℕ), (2560 : ℕ)), ((1917 : ℕ), (2048 : ℕ)), ((8191 : ℕ), (0 : ℕ))]; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : ℕ) (x5 : ℕ),   x2.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 ∧       (∀ x6 ∈ x2.gates, x6.inputs.Nodup) ∧         x2.output = (26 : ℕ) + x3 ∧           x2.gates[x3]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } ∧             ∀ (x6 : Fin (28 : ℕ)) (x7 : Fin (3 : ℕ)) (x8 : Fin (13 : ℕ)),               have x9 : ℕ × ℕ := x1.getD ↑x6 ((0 : ℕ), (0 : ℕ));               have x10 : ℕ → Fin (13 : ℕ) → Bool := fun (x10 : ℕ) (x11 : Fin (13 : ℕ)) => x10.testBit ↑((if x7 = (0 : Fin (3 : ℕ)) then (1 : Fin (13 : ℕ)) else if x7 = (1 : Fin (3 : ℕ)) then (3 : Fin (13 : ℕ)) else (9 : Fin (13 : ℕ))) * x11 + x8);               have x11 : ℕ → Bool := PEqualNP.BlindGate.wireValue x2 (26 : ℕ) (Fin.append (x10 x9.1) (x10 x9.2));               if ↑x6 < (2 : ℕ) then x11 x4 = Bool.true ∧ x11 x5 = Bool.true else x11 (if x10 x9.2 (0 : Fin (13 : ℕ)) = Bool.true then x4 else x5) = Bool.false) := by
  classical
  let legal (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) :=
    ∀ i (hi : i < gs.length), let g := gs[i]
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup ∧
        ∀ u ∈ g.inputs, u < n + i
  have legal_iff (C : PEqualNP.CircuitLowerBounds.Circuit) (n : ℕ) :
      legal n C.gates ↔ PEqualNP.TopForm.IsAO2 n C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) := by
    have atG (i : ℕ) (hi : i < C.gates.length) :
        PEqualNP.MetaComplexity.NestedCover.gateAt C i = C.gates[i] :=
      List.getD_eq_getElem _ _ hi
    constructor
    · intro h
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · intro g hg
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
        exact (h i hi).1
      · intro i hi u hu
        rw [atG i hi] at hu
        exact (h i hi).2.2.2 u hu
      · intro g hg
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
        exact (h i hi).2.1
      · intro g hg
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
        exact (h i hi).2.2.1
    · rintro ⟨h, nd⟩ i hi
      have m := List.getElem_mem hi
      exact ⟨h.1 _ m, h.2.2 _ m, nd _ m, fun u hu => h.2.1 i hi u (by rwa [atG i hi])⟩
  have appendLegal {n : ℕ} {p q : List PEqualNP.CircuitLowerBounds.Gate}
      (hp : legal n p) (hq : legal (n + p.length) q) : legal n (p ++ q) := by
    intro i hi
    by_cases hl : i < p.length
    · simpa only [List.getElem_append_left hl] using hp i hl
    · have hr : i - p.length < q.length := by simp only [List.length_append] at hi; omega
      have add : n + p.length + (i - p.length) = n + i := by omega
      simpa only [List.getElem_append_right (by omega : p.length ≤ i), add]
        using hq (i - p.length) hr

  let inc (p l : Fin 13) := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let row (p l : Fin 13) : Fin 26 → Bool := fun i =>
    decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
  let input (x : Fin 26 → Bool) := List.ofFn x ++ [x 0 || x 1]
  have splitLines : ∀ l : Fin 13, l ≠ 0 ↔ l ∈ ([12,1,4,5,10,11] : List (Fin 13)) ∨
       l ∈ ([2,3,6,7,8,9] : List (Fin 13)) := by decide +kernel
  have pair : ∃ D : Circuit, D.size ≤ 58 ∧ 27 ≤ D.output ∧ D.output < 27 + D.size ∧
      IsAO2 27 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
      (∀ p l : Fin 13, l ≠ 0 → inc p l → D.eval (input (row p l)) = true) ∧
      ∀ x : Fin 26 → Bool, D.eval (input x) = true →
        ∃ p l : Fin 13, inc p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    obtain ⟨A, As, Alo, Ahi, Aa, An, Apos, Asound⟩ := hleft
    obtain ⟨B, Bs, Blo, Bhi, Ba, Bn, Bpos, Bsound⟩ := hright
    change A.gates.length ≤ 28 at As
    change B.gates.length ≤ 29 at Bs
    change A.output < 27 + A.gates.length at Ahi
    change B.output < 27 + B.gates.length at Bhi
    let offset := A.gates.length
    let shift (i : ℕ) := if i < 27 then i else i + offset
    let move (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨g.op, g.inputs.map shift⟩
    have inj : Function.Injective shift := by
      intro i j h
      dsimp only [shift] at h
      split at h <;> split at h <;> omega
    have moved : legal (27 + A.gates.length) (B.gates.map move) := by
      intro i hi
      have h : i < B.gates.length := by simpa using hi
      have q := ((legal_iff B 27).mpr ⟨Ba, Bn⟩) i h
      simp only [List.getElem_map, move, List.length_map, List.mem_map]
      refine ⟨q.1, q.2.1, List.Nodup.map inj q.2.2.1, ?_⟩
      rintro _ ⟨j, hj, rfl⟩
      have bound := q.2.2.2 j hj
      dsimp only [shift, offset]
      split <;> omega
    have bout : shift B.output = B.output + offset := ite_eq_right (by omega)
    have distinct : A.output ≠ shift B.output := by rw [bout]; dsimp [offset]; omega
    let baseGates := A.gates ++ B.gates.map move
    let root : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, [A.output, shift B.output]⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨baseGates ++ [root], 27 + baseGates.length⟩
    have pn : baseGates.length = A.gates.length + B.gates.length := by simp [baseGates]
    have rootLegal : legal (27 + baseGates.length) [root] := by
      intro i hi
      have eq : i = 0 := by simpa using hi
      subst i
      refine ⟨Or.inr rfl, rfl, by simp [root, distinct], ?_⟩
      intro u hu
      change u ∈ [A.output, shift B.output] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · rw [pn]; omega
      · rw [pn, bout]; dsimp [offset]; omega
    have dl : PEqualNP.TopForm.IsAO2 27 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) :=
      (legal_iff D 27).mp (appendLegal (appendLegal ((legal_iff A 27).mpr ⟨Aa, An⟩) moved) rootLegal)
    refine ⟨D, ?_, ?_, ?_, dl.1, dl.2, ?_⟩
    · change (baseGates ++ [root]).length ≤ 58
      simp only [List.length_append, List.length_cons, List.length_nil, pn]
      omega
    · change 27 ≤ 27 + baseGates.length
      omega
    · change 27 + baseGates.length < 27 + (baseGates ++ [root]).length
      simp
    have evalD (x : Fin 26 → Bool) : D.eval (input x) = (A.eval (input x) || B.eval (input x)) := by
      let u := List.ofFn x ++ [x 0 || x 1]
      have ul : u.length = 27 := by simp [u]
      let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have trace (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
          ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
        induction gs generalizing w with
        | nil => exact ⟨[], by simp, rfl⟩
        | cons g gs ih =>
          obtain ⟨t, ht, hn⟩ := ih (step w g)
          exact ⟨_ :: t, by simpa only [List.foldl_cons, step, List.append_assoc,
            List.cons_append, List.nil_append] using ht, by simp [hn]⟩
      obtain ⟨mid, hm, ml⟩ := trace A.gates u
      have rd (t : List Bool) (i : ℕ) :
          (u ++ t).getD i false = ((u ++ mid) ++ t).getD (shift i) false := by
        by_cases hi : i < 27
        · simp only [shift, ite_eq_left hi]
          have hu : i < u.length := by omega
          have hum : i < (u ++ mid).length := by simp only [List.length_append]; omega
          calc
            (u ++ t).getD i false = u.getD i false := List.getD_append u t false i hu
            _ = (u ++ mid).getD i false := (List.getD_append u mid false i hu).symm
            _ = ((u ++ mid) ++ t).getD i false := (List.getD_append (u ++ mid) t false i hum).symm
        · simp only [shift, ite_eq_right hi]
          rw [List.getD_append_right _ _ _ _ (by omega : u.length ≤ i),
            List.getD_append_right _ _ _ _ (by simp only [List.length_append, ul, ml, offset]; omega)]
          simp only [List.length_append, ul, ml, offset]
          congr 1
          omega
      have simulate (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool) :
          ∃ t : List Bool, gs.foldl step (u ++ acc) = u ++ t ∧
            (gs.map move).foldl step ((u ++ mid) ++ acc) = (u ++ mid) ++ t ∧
            t.length = acc.length + gs.length := by
        induction gs generalizing acc with
        | nil => exact ⟨acc, rfl, rfl, by simp⟩
        | cons g gs ih =>
          let bit := g.op.eval (g.inputs.map fun i => (u ++ acc).getD i false)
          have bitEq : (move g).op.eval ((move g).inputs.map fun i => ((u ++ mid) ++ acc).getD i false) = bit := by
            simp only [move, List.map_map, bit]
            congr 1
            apply List.map_congr_left
            intro i _
            exact (rd acc i).symm
          obtain ⟨t, hs, hp, ht⟩ := ih (acc ++ [bit])
          refine ⟨t, ?_, ?_, ?_⟩
          · simpa only [List.foldl_cons, step, List.append_assoc, bit] using hs
          · change (gs.map move).foldl step (((u ++ mid) ++ acc) ++ [_]) = _
            rw [bitEq, List.append_assoc]
            exact hp
          · simp only [List.length_append, List.length_cons, List.length_nil] at ht ⊢
            omega
      obtain ⟨tail, hs, hp, tl⟩ := simulate B.gates []
      simp only [List.append_nil, List.length_nil, Nat.zero_add] at hs hp tl
      have pEval : baseGates.foldl step u = (u ++ mid) ++ tail := by
        simpa only [baseGates, List.foldl_append, hm] using hp
      have pLen : ((u ++ mid) ++ tail).length = 27 + baseGates.length :=
        by simp [ul, ml, tl, pn]
      have Aval : ((u ++ mid) ++ tail).getD A.output false = A.eval u := by
        change ((u ++ mid) ++ tail).getD A.output false = (A.gates.foldl step u).getD A.output false
        rw [hm, List.getD_append _ _ _ _ (by simp only [List.length_append, ul, ml]; exact Ahi)]
      have Bval : ((u ++ mid) ++ tail).getD (shift B.output) false = B.eval u := by
        change ((u ++ mid) ++ tail).getD (shift B.output) false =
          (B.gates.foldl step u).getD B.output false
        rw [hs, rd]
      have Deval : D.eval u = (A.eval u || B.eval u) := by
        change ((baseGates ++ [root]).foldl step u).getD (27 + baseGates.length) false = _
        rw [List.foldl_append, pEval]
        change (((u ++ mid) ++ tail) ++ [((u ++ mid) ++ tail).getD A.output false ||
          (((u ++ mid) ++ tail).getD (shift B.output) false || false)]).getD (27 + baseGates.length) false = _
        rw [List.getD_append_right _ _ _ _ (by omega), pLen, Nat.sub_self]
        rw [Aval, Bval]
        simp
      exact Deval
    refine ⟨?_, ?_⟩
    · intro p l hl hinc
      rw [evalD, Bool.or_eq_true]
      rcases (splitLines l).mp hl with hA | hB
      · exact Or.inl (Apos p l hA hinc)
      · exact Or.inr (Bpos p l hB hinc)
    · intro x hx
      rw [evalD, Bool.or_eq_true] at hx
      rcases hx with hA | hB
      · exact Asound x hA
      · exact Bsound x hB

  obtain ⟨D, hsz, hlo, hhi, hAO, hnd, positive, sound⟩ := pair
  change D.gates.length ≤ 58 at hsz
  change D.output < 27 + D.gates.length at hhi
  let seed : Gate := ⟨.or, [0,1]⟩
  let gs := seed :: D.gates
  let b := 26 + gs.length
  have hb : b = 27 + D.gates.length := by simp [b, gs]; omega
  let tail : List Gate := [⟨.or,[D.output,13]⟩, ⟨.or,[26,3]⟩, ⟨.or,[b+1,9]⟩,
    ⟨.or,[D.output,b+2]⟩, ⟨.and,[b+3,b]⟩]
  let C : Circuit := ⟨gs ++ tail, b + 4⟩
  have seedLegal : legal 26 [seed] := by
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst i
    change (seed.op = .and ∨ seed.op = .or) ∧ seed.inputs.length = 2 ∧
      seed.inputs.Nodup ∧ ∀ u ∈ seed.inputs, u < 26 + 0
    simp [seed]
  have gsLegal : legal 26 gs :=
    (appendLegal seedLegal ((legal_iff D 27).mpr ⟨hAO,hnd⟩))
  have tailLegal : legal b tail := by
    intro i hi
    have ht : i < 5 := hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · have hne : D.output ≠ 13 := by omega
      have hout : D.output < b := by omega
      have h13 : 13 < b := by omega
      simp [tail, hne, hout, h13]
    · have h26 : 26 < b + 1 := by omega
      have h3 : 3 < b + 1 := by omega
      simpa [tail] using And.intro h26 h3
    · have h9 : 9 < b + 2 := by omega
      have hne : b + 1 ≠ 9 := by omega
      simp [tail, h9, hne]
    · have hne : D.output ≠ b + 2 := by omega
      have hout : D.output < b + 3 := by omega
      simp [tail, hne, hout]
    · simp [tail]
  have finalLegal : IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) :=
    (legal_iff C 26).mp (appendLegal gsLegal tailLegal)
  have Csize : C.size ≤ 64 := by
    change (gs ++ tail).length ≤ 64
    simp only [List.length_append, gs, tail, List.length_cons, List.length_nil]
    omega
  have Cgate : C.gates[gs.length + 4]? = some ⟨.and,[b+3,b]⟩ := by
    change (gs ++ tail)[gs.length+4]? = _
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    rfl
  have Coutput : C.output = 26 + (gs.length+4) := by simp [C,b,Nat.add_assoc]
  let pts (x : Fin 26 → Bool) := (((x 0 || x 1) || x 3) || x 9)
  have vals (x : Fin 26 → Bool) :
      wireValue C 26 x (b+3) = (D.eval (input x) || pts x) ∧
      wireValue C 26 x b = (D.eval (input x) || x 13) := by
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
    let w := D.wires (input x)
    have keep (ys : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
        (ys.foldl step xs).getD i false = xs.getD i false := by
      induction ys generalizing xs with
      | nil => rfl
      | cons g ys ih =>
        change (ys.foldl step (step xs g)).getD i false = _
        have hlt : i < (step xs g).length := by simp [step]; omega
        exact (ih _ hlt).trans (List.getD_append _ _ _ _ hi)
    have lengthEq (ys : List Gate) (xs : List Bool) :
        (ys.foldl step xs).length = xs.length + ys.length := by
      induction ys generalizing xs with
      | nil => simp
      | cons g ys ih =>
        rw [List.foldl_cons, ih]
        simp [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have raw (i : Fin 26) : (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]
    have sow : step (List.ofFn x) seed = input x := by
      change (List.ofFn x) ++
        [(List.ofFn x).getD 0 false || ((List.ofFn x).getD 1 false || false)] = input x
      have e0 : (List.ofFn x).getD 0 false = x 0 := raw 0
      have e1 : (List.ofFn x).getD 1 false = x 1 := raw 1
      rw [e0, e1]
      simp [input]
    have seedVal : gs.foldl step (List.ofFn x) = w := by
      change D.gates.foldl step (step (List.ofFn x) seed) = _
      rw [sow]
      rfl
    have wlen : w.length = b := by
      change (D.gates.foldl step (input x)).length = b
      rw [lengthEq, hb]
      simp [input]
    have oldVal : w.getD D.output false = D.eval (input x) := rfl
    have xval (i : Fin 26) : w.getD i.val false = x i := by
      change (D.gates.foldl step (input x)).getD i.val false = _
      have hlt : i.val < (input x).length := by simp [input]; omega
      rw [keep _ _ _ hlt]
      change ((List.ofFn x) ++ [x 0 || x 1]).getD i.val false = _
      rw [List.getD_append _ _ _ _ (by simpa using i.isLt), raw]
    have zval : w.getD 26 false = (x 0 || x 1) := by
      change (D.gates.foldl step (input x)).getD 26 false = _
      have hlt : 26 < (input x).length := by simp [input]
      rw [keep _ _ _ hlt]
      change ((List.ofFn x) ++ [x 0 || x 1]).getD 26 false = _
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    let t0 := D.eval (input x) || x 13
    let t1 := (x 0 || x 1) || x 3
    let t2 := t1 || x 9
    let t3 := D.eval (input x) || t2
    have headStep : step w ⟨.or,[D.output,13]⟩ = w ++ [t0] := by
      change w ++ [w.getD D.output false || (w.getD 13 false || false)] = _
      have h13 : w.getD 13 false = x 13 := xval 13
      rw [oldVal, h13]
      simp [t0]
    have keep1 (i : ℕ) (hi : i < b) : (w ++ [t0]).getD i false = w.getD i false :=
      List.getD_append _ _ _ _ (wlen.symm ▸ hi)
    have step1 : step (w ++ [t0]) ⟨.or,[26,3]⟩ = w ++ [t0,t1] := by
      change (w ++ [t0]) ++ [(w ++ [t0]).getD 26 false ||
        ((w ++ [t0]).getD 3 false || false)] = _
      have h3 : w.getD 3 false = x 3 := xval 3
      rw [keep1 26 (by omega), keep1 3 (by omega), zval, h3]
      simp [t1,List.append_assoc]
    have at1 : (w ++ [t0,t1]).getD (b+1) false = t1 := by
      rw [List.getD_append_right _ _ _ _ (by omega), wlen]
      simp
    have keep2 (i : ℕ) (hi : i < b) : (w ++ [t0,t1]).getD i false = w.getD i false :=
      List.getD_append _ _ _ _ (wlen.symm ▸ hi)
    have step2 : step (w ++ [t0,t1]) ⟨.or,[b+1,9]⟩ = w ++ [t0,t1,t2] := by
      change (w ++ [t0,t1]) ++ [(w ++ [t0,t1]).getD (b+1) false ||
        ((w ++ [t0,t1]).getD 9 false || false)] = _
      have h9 : w.getD 9 false = x 9 := xval 9
      rw [at1, keep2 9 (by omega), h9]
      simp [t2,List.append_assoc]
    have at2 : (w ++ [t0,t1,t2]).getD (b+2) false = t2 := by
      rw [List.getD_append_right _ _ _ _ (by omega), wlen]
      simp
    have keep3 (i : ℕ) (hi : i < b) : (w ++ [t0,t1,t2]).getD i false = w.getD i false :=
      List.getD_append _ _ _ _ (wlen.symm ▸ hi)
    have step3 : step (w ++ [t0,t1,t2]) ⟨.or,[D.output,b+2]⟩ = w ++ [t0,t1,t2,t3] := by
      change (w ++ [t0,t1,t2]) ++ [(w ++ [t0,t1,t2]).getD D.output false ||
        ((w ++ [t0,t1,t2]).getD (b+2) false || false)] = _
      rw [at2, keep3 _ (by omega : D.output < b), oldVal]
      simp [t3,List.append_assoc]
    have run : (gs ++ tail).foldl step (List.ofFn x) =
        step (w ++ [t0,t1,t2,t3]) ⟨.and,[b+3,b]⟩ := by
      rw [List.foldl_append, seedVal]
      simp only [tail, List.foldl_cons, List.foldl_nil, headStep, step1, step2, step3]
    have keptOut (i : ℕ) (hi : i < b+4) : wireValue C 26 x i =
        (w ++ [t0,t1,t2,t3]).getD i false := by
      change ((gs ++ tail).foldl step (List.ofFn x)).getD i false = _
      rw [run]
      exact List.getD_append _ _ _ _ (by simp [wlen]; omega)
    constructor
    · rw [keptOut (b+3) (by omega), List.getD_append_right _ _ _ _ (by omega), wlen]
      simp [t3,t2,t1,pts]
    · rw [keptOut b (by omega), List.getD_append_right _ _ _ _ (by omega), wlen]
      simp [t0]
  intro rows
  refine ⟨C, gs.length + 4, b+3, b, Csize, finalLegal.1, finalLegal.2, Coutput, Cgate, ?_⟩
  let read (k : Fin 3) (c : Fin 13) (m : ℕ) (i : Fin 13) :=
    m.testBit (((if k = 0 then (1 : Fin 13) else if k = 1 then 3 else 9) * i + c).val)
  let probe (r : Fin 28) (k : Fin 3) (c : Fin 13) : Fin 26 → Bool :=
    Fin.append (read k c (rows.getD r.val (0,0)).1) (read k c (rows.getD r.val (0,0)).2)
  let invert (k : Fin 3) : Fin 13 := if k = 0 then 1 else if k = 1 then 9 else 3
  have edgePositive : ∀ (r : Fin 28) (k : Fin 3) (c : Fin 13), r.val < 2 →
      ∃ p l : Fin 13, inc p l ∧ ∀ i : Fin 26, probe r k c i = row p l i := by
    have cert : ∀ (r : Fin 28) (k : Fin 3) (c : Fin 13), r.val < 2 →
        let p := invert k * (Fin.ofNat 13 r.val - c)
        let l := invert k * (0 - c)
        inc p l ∧ ∀ i : Fin 26, probe r k c i = row p l i := by
      dsimp only [probe, rows, read, inc, row, invert]
      decide +kernel
    intro r k c hr
    exact ⟨_, _, cert r k c hr⟩
  have rowsOff : ∀ (r : Fin 28) (k : Fin 3) (c l : Fin 13), 2 ≤ r.val →
      let p := read k c (rows.getD r.val (0,0)).1
      read k c (rows.getD r.val (0,0)).2 l = true →
        (p l || p (l+1) || p (l+3) || p (l+9)) = false := by
    dsimp only [rows, read]
    decide +kernel
  have rowNegative (r : Fin 28) (k : Fin 3) (c : Fin 13) (hr : 2 ≤ r.val) :
      ¬ ∃ p l : Fin 13, inc p l ∧
          probe r k c (Fin.castAdd 13 p) = true ∧ probe r k c (Fin.natAdd 13 l) = true := by
    rintro ⟨p,l,hi,hp,hl⟩
    simp only [probe, Fin.append_left] at hp
    simp only [probe, Fin.append_right] at hl
    have off := rowsOff r k c l hr hl
    dsimp only [inc] at hi
    simp only [Bool.or_eq_false_iff] at off
    rcases hi with rfl | rfl | rfl | rfl
    · exact Bool.noConfusion (off.1.1.1.symm.trans hp)
    · exact Bool.noConfusion (off.1.1.2.symm.trans hp)
    · exact Bool.noConfusion (off.1.2.symm.trans hp)
    · exact Bool.noConfusion (off.2.symm.trans hp)
  have lineZero : ∀ p : Fin 13, inc p 0 ↔ p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9 := by
    dsimp only [inc]
    decide +kernel
  have liftPoint : ∀ p : Fin 13, inc p 0 → ∀ x : Fin 26 → Bool,
      x (Fin.castAdd 13 p) = true → pts x = true := by
    intro p hp x hx
    rcases (lineZero p).mp hp with rfl | rfl | rfl | rfl
    · change x 0 = true at hx
      simp [pts, hx]
    · change x 1 = true at hx
      simp [pts, hx]
    · change x 3 = true at hx
      simp [pts, hx]
    · change x 9 = true at hx
      simp [pts, hx]
  intro r k c
  let x := probe r k c
  change (if r.val < 2 then wireValue C 26 x (b+3) = true ∧ wireValue C 26 x b = true
    else wireValue C 26 x (if x 13 = true then b+3 else b) = false)
  have v := vals x
  by_cases hr : r.val < 2
  · rw [ite_eq_left hr, v.1, v.2]
    obtain ⟨p,l,hi,hr⟩ := edgePositive r k c hr
    have hx : x = row p l := funext hr
    by_cases hl : l = 0
    · subst l
      have hp : x (Fin.castAdd 13 p) = true := by simp [hx,row]
      have hz : x 13 = true := by simp [hx,row]
      simp [liftPoint p hi x hp, hz]
    · have hD : D.eval (input x) = true := (congrArg (fun y => D.eval (input y)) hx).trans (positive p l hl hi)
      simp [hD]
  · rw [ite_eq_right hr]
    have hn := rowNegative r k c (by omega)
    have hd : D.eval (input x) = false := by
      cases h : D.eval (input x)
      · rfl
      · exact (hn (sound x h)).elim
    by_cases hz : x 13 = true
    · rw [ite_eq_left hz, v.1, hd, Bool.false_or]
      have hpts : pts x = false := by
        cases h : pts x
        · rfl
        · have h0 : x (Fin.natAdd 13 (0 : Fin 13)) = true := hz
          simp only [pts, Bool.or_eq_true] at h
          rcases h with ((h | h) | h) | h
          · exact (hn ⟨0,0,by decide,h,h0⟩).elim
          · exact (hn ⟨1,0,by decide,h,h0⟩).elim
          · exact (hn ⟨3,0,by decide,h,h0⟩).elim
          · exact (hn ⟨9,0,by decide,h,h0⟩).elim
      exact hpts
    · rw [ite_eq_right hz, v.2, hd, Bool.false_or]
      cases h : x 13 <;> simp_all
