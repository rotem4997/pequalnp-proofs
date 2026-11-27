import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Peel the output ORs into a shared set of terminal AND wires.
-- Count them among the gates before the output, testing canonical sparse negatives.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3600_584
    (peel : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ReadsBack n C →
      n ≤ C.output → C.output < n + C.size → (gateAt C (C.output - n)).op = .or →
      ∃ F : Finset ℕ,
        (∀ w ∈ F, w < C.output ∧ (w < n ∨ (gateAt C (w - n)).op = .and)) ∧
        ∀ x : Fin n → Bool, circuitFun n C x = true ↔
          ∃ w ∈ F, wireValue C (List.ofFn x) w = true)
    (count : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (D : Circuit) (F : Finset ℕ),
      let v (x : Fin (N + N) → Bool) (w : ℕ) := wireValue D (List.ofFn x) w
      let pair (p l : Fin N) (i : Fin (N + N)) :=
        decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
      let neg (Y : Finset (Fin N)) := Fin.addCases
        (fun p => decide (∀ l ∈ Y, ¬ I p l)) (fun l => decide (l ∈ Y))
      300 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) →
      Monotone2 D →
      (∀ (i : ℕ) (g : Gate), D.gates[i]? = some g →
        ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i) →
      (∀ w ∈ F, N + N ≤ w ∧ w < N + N + D.size ∧
        (gateAt D (w - (N + N))).op = .and ∧ ∃ p l, I p l ∧ v (pair p l) w = true) →
      (∀ p l, I p l → ∃ w ∈ F, v (pair p l) w = true) →
      (∀ (Y : Finset (Fin N)), Y.card ≤ q → ∀ w ∈ F, v (neg Y) w = false) →
      N * q ≤ 100 * (D.size + 1)) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) → (∀ (x15 x16 : Fin x2), x3 x15 x16 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16)) = Bool.true) → (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x16 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I _ C hq hn degree joins mono outGe outLt outOr shape pos neg
  let k := C.output - (N + N)
  have hk : k < C.gates.length := by
    change C.output < N + N + C.gates.length at outLt
    dsimp [k]
    omega
  have hout : N + N + k = C.output := by dsimp [k]; omega
  have gateAt_eq (A : Circuit) (j : ℕ) (hj : j < A.gates.length) :
      gateAt A j = A.gates[j] := by
    change A.gates.getD j ⟨.or, []⟩ = A.gates[j]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have outOp : (gateAt C k).op = .or := by
    obtain ⟨g, hg, ho⟩ := outOr
    change C.gates[k]? = some g at hg
    rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hg
    rw [gateAt_eq _ _ hk, hg, ho]
  have back : ReadsBack (N + N) C := by
    intro j hj i hi
    rw [gateAt_eq _ _ hj] at hi
    obtain ⟨a, b, h, hab, hb⟩ := shape j C.gates[j] (List.getElem?_eq_getElem hj)
    rw [h] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  obtain ⟨F, front, eval⟩ := peel (N + N) C mono back outGe outLt outOp
  let appendGate := fun (xs : List Bool) (g : Gate) =>
    xs ++ [g.op.eval (g.inputs.map fun w => xs.getD w false)]
  let wires := fun (gs : List Gate) (xs : List Bool) => gs.foldl appendGate xs
  have keeps : ∀ (gs : List Gate) (xs : List Bool) (w : ℕ), w < xs.length →
      (wires gs xs).getD w false = xs.getD w false := by
    intro gs
    induction gs with
    | nil => intro xs w _; rfl
    | cons g rest ih =>
      intro xs w hw
      change (wires rest (appendGate xs g)).getD w false = xs.getD w false
      rw [ih _ _ (by simp [appendGate]; omega)]
      exact List.getD_append _ _ _ _ hw
  have wiresLength : ∀ (gs : List Gate) (xs : List Bool),
      (wires gs xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp [wires]
    | cons g rest ih =>
      intro xs
      change (wires rest (appendGate xs g)).length = xs.length + (g :: rest).length
      rw [ih]
      simp [appendGate]
      omega
  have noInput (w : ℕ) (hF : w ∈ F) : N + N ≤ w := by
    by_contra! hw
    let i : Fin (N + N) := ⟨w, hw⟩
    let x (j : Fin (N + N)) : Bool := decide (j = i)
    have yes : wireValue C (List.ofFn x) w = true := by
      change (wires C.gates (List.ofFn x)).getD w false = true
      rw [keeps _ _ _ (by simpa using hw)]
      simp [List.getD_eq_getElem?_getD, hw, x, i]
    have rejected : circuitFun (N + N) C x = false := by
      apply neg
      · have h : Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ 1 := by
          apply Fintype.card_le_one_iff.mpr
          intro a b
          have ha : Fin.natAdd N a.val = i := of_decide_eq_true a.property
          have hb : Fin.natAdd N b.val = i := of_decide_eq_true b.property
          exact Subtype.ext (Fin.natAdd_injective N N (ha.trans hb.symm))
        omega
      · rintro ⟨p, l, _, hp, hl⟩
        have a : Fin.castAdd N p = i := of_decide_eq_true hp
        have b : Fin.natAdd N l = i := of_decide_eq_true hl
        have e := congrArg Fin.val (a.trans b.symm)
        simp only [Fin.val_castAdd, Fin.val_natAdd] at e
        have := p.isLt
        omega
    have yesOut := (eval x).2 ⟨w, hF, yes⟩
    rw [rejected] at yesOut
    contradiction
  let D : Circuit := ⟨C.gates.take k, 0⟩
  have dSize : D.size = k := by
    change (C.gates.take k).length = k
    rw [List.length_take, Nat.min_eq_left hk.le]
  have getDGate (j : ℕ) (hj : j < k) : D.gates[j]? = C.gates[j]? :=
    List.getElem?_take_of_lt hj
  have dShape (j : ℕ) (g : Gate) (h : D.gates[j]? = some g) :
      ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + j := by
    have hi : j < D.gates.length := by
      by_contra! hnot
      rw [List.getElem?_eq_none hnot] at h
      contradiction
    change j < D.size at hi
    rw [dSize] at hi
    exact shape j g ((getDGate j hi).symm.trans h)
  have dMono : Monotone2 D := by
    intro g hg
    apply mono g
    exact List.Sublist.mem hg (List.take_sublist _ _)
  have takeValue (x : Fin (N + N) → Bool) (w : ℕ) (hw : w < C.output) :
      wireValue D (List.ofFn x) w = wireValue C (List.ofFn x) w := by
    let xs := List.ofFn x
    have hsplit : wires C.gates xs = wires (C.gates.drop k) (wires (C.gates.take k) xs) := by
      have h := congrArg (fun gs => wires gs xs) (List.take_append_drop k C.gates)
      simpa only [wires, List.foldl_append] using h.symm
    change (wires (C.gates.take k) xs).getD w false = (wires C.gates xs).getD w false
    rw [hsplit]
    symm
    apply keeps
    rw [wiresLength, List.length_ofFn, List.length_take, Nat.min_eq_left hk.le, hout]
    exact hw
  let pair (p l : Fin N) (i : Fin (N + N)) :=
    decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
  let T := F.filter (fun w => ∃ p l, I p l ∧ wireValue C (List.ofFn (pair p l)) w = true)
  have Tfront (w : ℕ) (hw : w ∈ T) : w ∈ F := (Finset.mem_filter.mp hw).1
  have Tbounds (w : ℕ) (hw : w ∈ T) :
      N + N ≤ w ∧ w < N + N + D.size ∧
        (gateAt D (w - (N + N))).op = .and ∧
        ∃ p l, I p l ∧ wireValue D (List.ofFn (pair p l)) w = true := by
    have hF := Tfront w hw
    have hlow := noInput w hF
    have hupper := (front w hF).1
    have hop := (front w hF).2.resolve_left (not_lt_of_ge hlow)
    have idx : w - (N + N) < k := by omega
    have same : gateAt D (w - (N + N)) = gateAt C (w - (N + N)) := by
      change D.gates.getD (w - (N + N)) ⟨.or, []⟩ =
        C.gates.getD (w - (N + N)) ⟨.or, []⟩
      simp only [List.getD_eq_getElem?_getD, getDGate _ idx]
    obtain ⟨p, l, hI, hp⟩ := (Finset.mem_filter.mp hw).2
    refine ⟨hlow, by rwa [dSize, hout], same ▸ hop, p, l, hI, ?_⟩
    rwa [takeValue _ _ hupper]
  have Tpos (p l : Fin N) (hI : I p l) :
      ∃ w ∈ T, wireValue D (List.ofFn (pair p l)) w = true := by
    obtain ⟨w, hw, he⟩ := (eval (pair p l)).1 (pos p l hI)
    refine ⟨w, Finset.mem_filter.mpr ⟨hw, p, l, hI, he⟩, ?_⟩
    rwa [takeValue _ _ (front w hw).1]
  have Tneg (Y : Finset (Fin N)) (hY : Y.card ≤ q) (w : ℕ) (hw : w ∈ T) :
      wireValue D (List.ofFn (Fin.addCases
        (fun p => decide (∀ l ∈ Y, ¬ I p l)) (fun l => decide (l ∈ Y)))) w = false := by
    let x : Fin (N + N) → Bool := Fin.addCases
      (fun p => decide (∀ l ∈ Y, ¬ I p l)) (fun l => decide (l ∈ Y))
    have hF := Tfront w hw
    change wireValue D (List.ofFn x) w = false
    rw [takeValue _ _ (front w hF).1]
    have no : circuitFun (N + N) C x = false := by
      apply neg
      · let e : {l : Fin N // x (Fin.natAdd N l) = true} ≃ ↥Y :=
          { toFun := fun l => ⟨l.val, by simpa only [x, Fin.addCases_right, decide_eq_true_eq] using l.property⟩
            invFun := fun l => ⟨l.val, by simpa only [x, Fin.addCases_right, decide_eq_true_eq] using l.property⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [Fintype.card_congr e, Fintype.card_coe]
        exact hY
      · rintro ⟨p, l, hi, hp, hl⟩
        have a : ∀ l ∈ Y, ¬ I p l := by simpa only [x, Fin.addCases_left, decide_eq_true_eq] using hp
        have b : l ∈ Y := by simpa only [x, Fin.addCases_right, decide_eq_true_eq] using hl
        exact a l b hi
    cases val : wireValue C (List.ofFn x) w
    · rfl
    · have yes := (eval x).2 ⟨w, hF, val⟩
      rw [no] at yes
      contradiction
  have bound := count q N I D T hq hn degree joins dMono dShape Tbounds Tpos Tneg
  have hs : D.size + 1 ≤ C.size := by rw [dSize]; change k + 1 ≤ C.gates.length; omega
  exact bound.trans (Nat.mul_le_mul_left _ hs)
