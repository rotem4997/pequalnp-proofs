import PEqualNP.Defs

-- Only the first sixty columns require ordinary gate evaluation.
-- The remaining two marks follow paths from input seven or input zero.
-- At an AND gate the opposite operand must be on in the corresponding singleton column.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_4649_517
  (paths : ∀ (n k src : ℕ) (a b : ℕ → ℕ) (L R v : ℕ → Bool),
    src < n → (∀ i < k, a i < n+i ∧ b i < n+i) →
    (∀ x < n, v x = decide (x = src)) →
    (∀ i < k, v (n+i) = ((v (a i) && L i) || (v (b i) && R i))) →
    let edge := fun x y : ℕ => ∃ i < k, y = n+i ∧
      ((x = a i ∧ L i = true) ∨ (x = b i ∧ R i = true))
    ∀ y < n+k, v y = true ↔ Relation.ReflTransGen edge src y)
  (fano : ∀ (k : ℕ) (op : ℕ → Bool) (a b : ℕ → ℕ) (w : ℕ → BitVec 60),
    k ≤ 27 →
    (∀ i < 14, w i = BitVec.ofNat 60 (([2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List ℕ).getD i 0)) →
    (∀ i < k, a i ≠ b i ∧ a i < 14+i ∧ b i < 14+i ∧ (op i = false → 0 < i) ∧
      w (14+i) = if op i then w (a i) ||| w (b i) else w (a i) &&& w (b i)) →
    ∀ j < k, w (14+j) = 2097151 →
    ∃ s : Bool, let t : ℕ := if s then 58 else 59
      Relation.ReflTransGen (fun x y : ℕ => ∃ i < k, y = 14+i ∧
        ((x = a i ∧ (op i || (w (b i)).getLsbD t) = true) ∨
          (x = b i ∧ (op i || (w (a i)).getLsbD t) = true)))
        (if s then 7 else 0) (14+j)) :
  have x1 : List (Fin (62 : ℕ) → Bool) := List.map (fun (x1 : ℕ) (x2 : Fin (62 : ℕ)) => x1.testBit ↑x2) [(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)]; ¬∃ (x2 : List (Fin (62 : ℕ) → Bool)),     x2.length ≤ (27 : ℕ) ∧       (fun (x3 : Fin (62 : ℕ)) => Decidable.decide (↑x3 < (21 : ℕ))) ∈ x2 ∧         ∀ x3 < x2.length,           ∃ (x5 : ℕ) (x6 : ℕ),             x5 ≠ x6 ∧               x5 < (14 : ℕ) + x3 ∧                 x6 < (14 : ℕ) + x3 ∧                   have x7 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x5 fun (x7 : Fin (62 : ℕ)) => Bool.false;                   have x8 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x6 fun (x8 : Fin (62 : ℕ)) => Bool.false;                   ((x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => x7 x9 || x8 x9) ∨ (0 : ℕ) < x3 ∧ (x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => if x9 = (60 : Fin (62 : ℕ)) then x7 (58 : Fin (62 : ℕ)) && x8 (60 : Fin (62 : ℕ)) || x7 (60 : Fin (62 : ℕ)) && x8 (58 : Fin (62 : ℕ)) else if x9 = (61 : Fin (62 : ℕ)) then x7 (59 : Fin (62 : ℕ)) && x8 (61 : Fin (62 : ℕ)) || x7 (61 : Fin (62 : ℕ)) && x8 (59 : Fin (62 : ℕ)) else x7 x9 && x8 x9 := by
  let raw : List ℕ := [2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916]
  let seed := raw.map (fun n => fun t : Fin 62 => n.testBit t.val)
  let zero := fun _ : Fin 62 => false
  let target := fun t : Fin 62 => decide (t.val < 21)
  change ¬ ∃ s : List (Fin 62 → Bool), s.length ≤ 27 ∧ target ∈ s ∧ _
  rintro ⟨s, cap, mem, gates⟩
  let wire (i : ℕ) := (seed ++ s).getD i zero
  have nseed : seed.length = 14 := by rfl
  have input (i : ℕ) (hi : i < 14) (t : Fin 62) : wire i t = (raw.getD i 0).testBit t.val := by
    have hi' : i < seed.length := nseed ▸ hi
    change ((seed ++ s).getD i zero) t = _
    rw [List.getD_append _ _ _ _ hi']
    change ((raw.map (fun n => fun u : Fin 62 => n.testBit u.val)).getD i zero) t = _
    have hz : zero = (fun n : ℕ => fun u : Fin 62 => n.testBit u.val) 0 := by
      funext u
      exact (Nat.zero_testBit _).symm
    rw [hz, List.getD_map]
  have gate (i : ℕ) : wire (14+i) = s.getD i zero := by
    dsimp only [wire]
    rw [List.getD_append_right _ _ _ _ (by rw [nseed]; omega), nseed, Nat.add_sub_cancel_left]
  have rules (i : ℕ) : ∃ (a b : ℕ) (o : Bool), i < s.length →
      a ≠ b ∧ a < 14+i ∧ b < 14+i ∧ (o = false → 0 < i) ∧
      ∀ t : Fin 62, wire (14+i) t =
        if o then wire a t || wire b t else
          if t = 60 then (wire a 58 && wire b 60) || (wire a 60 && wire b 58)
          else if t = 61 then (wire a 59 && wire b 61) || (wire a 61 && wire b 59)
          else wire a t && wire b t := by
    by_cases hi : i < s.length
    · obtain ⟨a, b, ne, ha, hb, alt⟩ := gates i hi
      rcases alt with h | ⟨pos, h⟩
      · exact ⟨a, b, true, fun _ => ⟨ne, ha, hb, by simp, fun t => (gate i ▸ congrFun h t)⟩⟩
      · exact ⟨a, b, false, fun _ => ⟨ne, ha, hb, fun _ => pos, fun t => (gate i ▸ congrFun h t)⟩⟩
    · exact ⟨0, 0, false, fun h => False.elim (hi h)⟩
  choose a b op rule using rules
  let w (i : ℕ) : BitVec 60 := (BitVec.ofBoolListLE (List.ofFn fun t : Fin 60 =>
    wire i (Fin.ofNat 62 t.val))).setWidth 60
  have bit (i t : ℕ) (ht : t < 60) : (w i).getLsbD t = wire i (Fin.ofNat 62 t) := by
    simp only [w, BitVec.getLsbD_setWidth, ht, decide_true, Bool.true_and,
      BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_ofFn]
  have base (i : ℕ) (hi : i < 14) : w i = BitVec.ofNat 60 (raw.getD i 0) := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro t ht
    rw [bit i t ht, input i hi, BitVec.getLsbD_ofNat]
    simp [ht, Fin.ofNat, Nat.mod_eq_of_lt (show t < 62 by omega)]
  have spec (i : ℕ) (hi : i < s.length) : a i ≠ b i ∧ a i < 14+i ∧ b i < 14+i ∧
      (op i = false → 0 < i) ∧ w (14+i) = if op i then w (a i) ||| w (b i) else w (a i) &&& w (b i) := by
    obtain ⟨ne, ha, hb, pos, eval⟩ := rule i hi
    refine ⟨ne, ha, hb, pos, BitVec.eq_of_getLsbD_eq_iff.mpr ?_⟩
    intro t ht
    have hv : (Fin.ofNat 62 t).val = t := Nat.mod_eq_of_lt (by omega)
    have h60 : Fin.ofNat 62 t ≠ 60 := by intro h; have := congrArg Fin.val h; change _ = 60 at this; omega
    have h61 : Fin.ofNat 62 t ≠ 61 := by intro h; have := congrArg Fin.val h; change _ = 61 at this; omega
    cases hop : op i <;> simp only [hop, Bool.false_eq_true, ite_false, ite_true,
      BitVec.getLsbD_and, BitVec.getLsbD_or, bit _ _ ht, eval, h60, h61]
  obtain ⟨j, hj, hout⟩ := List.mem_iff_getElem.mp mem
  have out : wire (14+j) = target := by
    rw [gate, List.getD_eq_getElem _ _ hj, hout]
  have targetBits : ∀ t : Fin 60, (2097151 : BitVec 60).getLsbD t.val = decide (t.val < 21) := by decide
  have outWord : w (14+j) = 2097151 := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro t ht
    rw [bit _ _ ht, out, targetBits ⟨t, ht⟩]
    dsimp [target, Fin.ofNat]
    simp only [Nat.mod_eq_of_lt (show t < 62 by omega)]
  obtain ⟨side, route⟩ := fano s.length op a b w cap base spec j hj outWord
  let t : ℕ := if side then 58 else 59
  let m : Fin 62 := if side then 60 else 61
  let src : ℕ := if side then 7 else 0
  let L (i : ℕ) := op i || (w (b i)).getLsbD t
  let R (i : ℕ) := op i || (w (a i)).getLsbD t
  have initial : ∀ i < 14, wire i m = decide (i = src) := by
    intro i hi
    rw [input i hi]
    have vals : ∀ u : Fin 14, ∀ d : Bool,
        (raw.getD u.val 0).testBit (if d then 60 else 61) = decide (u.val = if d then 7 else 0) := by decide
    dsimp only [m, src]
    cases side
    · exact vals ⟨i,hi⟩ false
    · exact vals ⟨i,hi⟩ true
  have step (i : ℕ) (hi : i < s.length) :
      wire (14+i) m = ((wire (a i) m && L i) || (wire (b i) m && R i)) := by
    rw [(rule i hi).2.2.2.2 m]
    dsimp only [L, R, t, m]
    cases side <;> cases h : op i <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, Bool.false_or, Bool.true_or,
        Bool.and_true, bit _ 58 (by decide), bit _ 59 (by decide)] <;>
      simp [Bool.and_comm, Bool.or_comm]
  have reachable := paths 14 s.length src a b L R (fun i => wire i m)
    (by cases side <;> decide) (fun i hi => ⟨(rule i hi).2.1, (rule i hi).2.2.1⟩) initial step
  have lit := (reachable (14+j) (by omega)).mpr route
  rw [out] at lit
  cases side <;> contradiction
