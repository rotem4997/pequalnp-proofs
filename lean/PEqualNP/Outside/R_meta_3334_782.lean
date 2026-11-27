import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 15000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3334_782
  (pairs : ∀ i j : Fin 9, ∃ x : Fin 9 → Bool,
    let t := fun y : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
      (fun e => y (Fin.ofNat 9 (e / 10)) && y (Fin.ofNat 9 (e % 10)))
    t x = false ∧ t (fun k => decide (k = i) || x k) = true ∧
      t (fun k => decide (k = j) || x k) = true)
  (packed : ∀ (n : Fin 14) (o : Fin (n.val + 1) → Bool)
    (a : Fin (n.val + 1) → Bool → Fin 24 × Bool) (neg : Bool)
    (s : Finset (Fin 24)) (w : Fin 24 → BitVec 512),
    let enc := fun f : Fin 512 → Bool => BitVec.setWidth 512 (BitVec.ofBoolListLE (List.ofFn f))
    let v := fun e : Fin 24 × Bool => if e.2 then ~~~(w e.1) else w e.1
    let u := fun i : Fin (n.val + 1) => Fin.ofNat 24 (10 + i.val)
    let k := Fin.last n.val
    let p := fun e : Fin 24 × Bool =>
      let z := v (e.1, e.2 ^^ neg)
      ∀ i : Fin 9, ∃ m : Nat, z.getLsbD m < z.getLsbD ((Nat.pow (2 : Nat) i.val) ||| m)
    ¬ (s.card ≤ min 3 (13 - n.val) ∧
    (∀ i j, (a i j).1.val < 10 + i.val) ∧
    (let c := fun e : Fin 24 × Bool => e.2 = true → e.1 = 0 ∨ e.1 = 9 ∨ e.1 ∈ s;
      c (u k, neg) ∧ ∀ i j, c (a i j)) ∧
    (∀ i : Fin 9, w (Fin.ofNat 24 i.val) = enc (fun m => (BitVec.ofNat 9 m.val).getLsbD i.val)) ∧ w 9 = 0 ∧
    (∀ i, w (u i) = if o i then v (a i false) &&& v (a i true) else v (a i false) ||| v (a i true)) ∧
    (o k ≠ neg → p (a k false) ∨ p (a k true)) ∧
    v (u k, neg) = enc (fun m =>
      ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any
        (fun e => e &&& m.val == e)))) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => List.foldl (fun (x2 : Bool) (x3 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x2 || x1 x3.1 && x1 x3.2) Bool.false [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))]; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ)) → Bool) (x4 x5 : Fin (x2 + (1 : ℕ)) → ℕ × Bool) (x6 : Bool) (x7 : Finset ℕ) (x8 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x7.card ≤ (3 : ℕ) →     x2 + (1 : ℕ) + x7.card ≤ (14 : ℕ) →       (∀ (x11 : Fin (x2 + (1 : ℕ))), (x4 x11).1 < (10 : ℕ) + ↑x11 ∧ (x5 x11).1 < (10 : ℕ) + ↑x11) →         (have x12 : ℕ × Bool → Prop := fun (x12 : ℕ × Bool) => x12.2 = Bool.true → x12.1 = (0 : ℕ) ∨ x12.1 = (9 : ℕ) ∨ x12.1 ∈ x7;           x12 ((10 : ℕ) + x2, x6) ∧ ∀ (x13 : Fin (x2 + (1 : ℕ))), x12 (x4 x13) ∧ x12 (x5 x13)) →           (∀ (x13 : Fin (9 : ℕ) → Bool) (x14 : Fin (9 : ℕ)), x8 x13 ↑x14 = x13 x14) →             (∀ (x14 : Fin (9 : ℕ) → Bool), x8 x14 (9 : ℕ) = Bool.false) →               (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (x2 + (1 : ℕ))),                   have x17 : ℕ × Bool → Bool := fun (x17 : ℕ × Bool) => x8 x15 x17.1 ^^ x17.2;                   x8 x15 ((10 : ℕ) + ↑x16) = if x3 x16 = Bool.true then x17 (x4 x16) && x17 (x5 x16) else x17 (x4 x16) || x17 (x5 x16)) →                 (9 : ℕ) ≤ (x4 (Fin.last x2)).1 → (9 : ℕ) ≤ (x5 (Fin.last x2)).1 → ¬∀ (x18 : Fin (9 : ℕ) → Bool), (x8 x18 ((10 : ℕ) + x2) ^^ x6) = x1 x18 := by
  intro posted n o a b neg paid wire hcard hcost hback hneg hraw hfalse hgate hleft hright correct
  classical
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have targetEq (x : Fin 9 → Bool) : posted x = f x := by
    simp [posted, f, List.foldl, List.any, Bool.or_assoc]
    rfl
  have correct' (x : Fin 9 → Bool) : (wire x (10+n) ^^ neg) = f x :=
    (correct x).trans (targetEq x)
  let limit : Fin 14 := ⟨n, by omega⟩
  let ix : Nat → Fin 24 := Fin.ofNat 24
  have ix_val (j : Nat) (hj : j < 24) : (ix j).val = j := Nat.mod_eq_of_lt hj
  have leftBound (i : Fin (n+1)) : (a i).1 < 24 := by
    have hi := i.isLt
    have ha := (hback i).1
    omega
  have rightBound (i : Fin (n+1)) : (b i).1 < 24 := by
    have hi := i.isLt
    have hb := (hback i).2
    omega
  have gateBound (i : Fin (n+1)) : 10 + i.val < 24 := by
    have hi := i.isLt
    omega
  let left := fun i => (ix (a i).1, (a i).2)
  let right := fun i => (ix (b i).1, (b i).2)
  let ref := fun (i : Fin (n+1)) (side : Bool) => if side then right i else left i
  let mask := Finset.univ.filter (fun i : Fin 24 => i.val ∈ paid)
  have maskCard : mask.card ≤ paid.card := by
    let emb : Fin 24 ↪ Nat := ⟨Fin.val, Fin.val_injective⟩
    rw [← Finset.card_map emb]
    apply Finset.card_le_card
    intro j hj
    obtain ⟨i, hi, hj⟩ := Finset.mem_map.mp hj
    have hm := (Finset.mem_filter.mp hi).2
    exact hj ▸ hm
  let enc : {r : Nat} → (Fin r → Bool) → BitVec r :=
    fun f => BitVec.setWidth _ (BitVec.ofBoolListLE (List.ofFn f))
  have enc_bit {r : Nat} (f : Fin r → Bool) (j : Nat) (hj : j < r) :
      (enc f).getLsbD j = f ⟨j, hj⟩ := by
    unfold enc
    rw [BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, BitVec.getLsbD_ofBoolListLE]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hj, Option.getD_some]
  let row := fun (m : Fin 512) (i : Fin 9) => m.val.testBit i.val
  let trace := fun i : Fin 24 => enc (fun m => wire (row m) i.val)
  let vlit := fun e : Fin 24 × Bool => if e.2 then ~~~(trace e.1) else trace e.1
  have bit (e : Fin 24 × Bool) (m : Fin 512) :
      (vlit e).getLsbD m.val = (wire (row m) e.1.val ^^ e.2) := by
    rcases e with ⟨i, phase⟩
    cases phase
    · change (trace i).getLsbD m.val = (wire (row m) i.val ^^ false)
      rw [Bool.xor_false]
      exact enc_bit _ _ m.isLt
    · change (~~~trace i).getLsbD m.val = (wire (row m) i.val ^^ true)
      rw [BitVec.getLsbD_not, decide_eq_true m.isLt, show (trace i).getLsbD m.val = _ from enc_bit _ _ m.isLt]
      cases wire (row m) i.val <;> rfl
  have spell (x : Fin 9 → Bool) : ∃ m : Fin 512, row m = x := by
    refine ⟨(enc x).toFin, ?_⟩
    funext j
    exact enc_bit x j.val j.isLt
  have rewriteRoot (op phase t u : Bool) :
      op ≠ phase → ((if op then t && u else t || u) ^^ phase) =
      ((t ^^ phase) && (u ^^ phase)) := by cases op <;> cases phase <;> cases t <;> cases u <;> decide
  let last := Fin.last n
  have root (h : o last ≠ neg) (x : Fin 9 → Bool) :
      f x = ((wire x (a last).1 ^^ ((a last).2 ^^ neg)) &&
        (wire x (b last).1 ^^ ((b last).2 ^^ neg))) := by
    rw [← correct' x]
    change (wire x (10+last.val) ^^ neg) = _
    rw [hgate x last, rewriteRoot _ _ _ _ h]
    simp only [Bool.xor_assoc]
  have pivot (h : o last ≠ neg) :
      (∀ i : Fin 9, ∃ x : Fin 9 → Bool,
        (wire x (a last).1 ^^ ((a last).2 ^^ neg)) = false ∧
        (wire (fun j => decide (j=i) || x j) (a last).1 ^^ ((a last).2 ^^ neg)) = true) ∨
      (∀ i : Fin 9, ∃ x : Fin 9 → Bool,
        (wire x (b last).1 ^^ ((b last).2 ^^ neg)) = false ∧
        (wire (fun j => decide (j=i) || x j) (b last).1 ^^ ((b last).2 ^^ neg)) = true) := by
    by_contra neither
    push Not at neither
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := neither
    obtain ⟨x, hz, hl, hr⟩ := pairs i j
    change f x = false at hz
    change f (fun k => decide (k=i) || x k) = true at hl
    change f (fun k => decide (k=j) || x k) = true at hr
    simp only [root h, Bool.and_eq_true] at hl hr
    have lTrue : (wire x (a last).1 ^^ ((a last).2 ^^ neg)) = true := by
      cases eq : (wire x (a last).1 ^^ ((a last).2 ^^ neg))
      · exact False.elim (hi x eq hl.1)
      · rfl
    have rTrue : (wire x (b last).1 ^^ ((b last).2 ^^ neg)) = true := by
      cases eq : (wire x (b last).1 ^^ ((b last).2 ^^ neg))
      · exact False.elim (hj x eq hr.2)
      · rfl
    simp [root h, lTrue, rTrue] at hz
  apply packed limit o ref neg mask trace
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply le_min
    · omega
    · change mask.card ≤ 13 - n
      omega
  · intro i side
    cases side
    · change (ix (a i).1).val < 10 + i.val
      rw [ix_val _ (leftBound i)]
      exact (hback i).1
    · change (ix (b i).1).val < 10 + i.val
      rw [ix_val _ (rightBound i)]
      exact (hback i).2
  · have allow (e : Nat × Bool) (bound : e.1 < 24)
         (he : e.2 = true → e.1 = 0 ∨ e.1 = 9 ∨ e.1 ∈ paid) :
         e.2 = true → ix e.1 = 0 ∨ ix e.1 = 9 ∨ ix e.1 ∈ mask := by
      intro hp
      rcases he hp with h | h | h
      · left
        rw [h]
        rfl
      · right
        left
        rw [h]
        rfl
      · right
        right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [ix_val _ bound] using h⟩
    refine ⟨allow (10+n, neg) (gateBound last) hneg.1, ?_⟩
    intro i side
    cases side
    · exact allow (a i) (leftBound i) (hneg.2 i).1
    · exact allow (b i) (rightBound i) (hneg.2 i).2
  · intro i
    apply BitVec.eq_of_getLsbD_eq
    intro m hm
    have hb : i.val < 24 := by have h := i.isLt; omega
    change (enc (fun m => wire (row m) (ix i.val).val)).getLsbD m =
      (enc (fun m => (BitVec.ofNat 9 m.val).getLsbD i.val)).getLsbD m
    rw [enc_bit _ _ hm, enc_bit _ _ hm, ix_val _ hb, BitVec.getLsbD_ofNat, decide_eq_true i.isLt, Bool.true_and]
    exact hraw _ i
  · apply BitVec.eq_of_getLsbD_eq
    intro m hm
    change (enc (fun m => wire (row m) 9)).getLsbD m = (0 : BitVec 512).getLsbD m
    rw [enc_bit _ _ hm]
    exact (hfalse _).trans (BitVec.getLsbD_zero (w := 512) (i := m)).symm
  · intro i
    apply BitVec.eq_of_getLsbD_eq
    intro m hm
    let j : Fin 512 := ⟨m, hm⟩
    change (trace (ix (10+i.val))).getLsbD m =
      (if o i then vlit (left i) &&& vlit (right i) else vlit (left i) ||| vlit (right i)).getLsbD m
    cases e : o i <;>
      simpa [trace, left, right, ix_val _ (leftBound i), ix_val _ (rightBound i),
        ix_val _ (gateBound i), bit _ j, enc_bit _ _ hm, j, e] using hgate (row j) i
  · intro h
    have lift (e : Nat × Bool) (bound : e.1 < 24)
        (hs : ∀ i : Fin 9, ∃ x : Fin 9 → Bool, (wire x e.1 ^^ (e.2 ^^ neg)) = false ∧
          (wire (fun j => decide (j=i) || x j) e.1 ^^ (e.2 ^^ neg)) = true) :
        ∀ i : Fin 9, ∃ m : Nat,
          (vlit (ix e.1, e.2 ^^ neg)).getLsbD m <
            (vlit (ix e.1, e.2 ^^ neg)).getLsbD ((Nat.pow (2 : Nat) i.val) ||| m) := by
      intro i
      obtain ⟨x, hx, hy⟩ := hs i
      obtain ⟨m, hm⟩ := spell x
      let t : Fin 512 := ⟨2 ^ i.val ||| m.val,
        Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by decide) i.isLt) m.isLt⟩
      have updateRow : row t = fun k => decide (k=i) || x k := by
        funext k
        change (2 ^ i.val ||| m.val).testBit k.val = (decide (k=i) || x k)
        rw [Nat.testBit_or, Nat.testBit_two_pow]
        have ht : m.val.testBit k.val = x k := congrFun hm k
        rw [ht]
        have swap : i.val = k.val ↔ k = i :=
          ⟨fun e => (Fin.ext e).symm, fun e => congrArg Fin.val e.symm⟩
        simp only [swap]
      refine ⟨m.val, ?_⟩
      change (vlit (ix e.1, e.2 ^^ neg)).getLsbD m.val <
        (vlit (ix e.1, e.2 ^^ neg)).getLsbD t.val
      rw [bit _ m, bit _ t, ix_val _ bound, hm, updateRow, hx, hy]
      decide
    rcases pivot h with hl | hr
    · exact Or.inl (lift (a last) (leftBound last) hl)
    · exact Or.inr (lift (b last) (rightBound last) hr)
  · let targetRow (m : Fin 512) : Bool :=
      ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any
        (fun e => e &&& m.val == e)
    have vectors : ∀ m : Fin 512, f (row m) = targetRow m := by decide +kernel
    apply BitVec.eq_of_getLsbD_eq
    intro m hm
    let j : Fin 512 := ⟨m, hm⟩
    change (vlit (ix (10+n), neg)).getLsbD m = (enc targetRow).getLsbD m
    rw [bit _ j, enc_bit targetRow _ hm, ← vectors j]
    have outBound : 10+n < 24 := by omega
    rw [ix_val _ outBound]
    exact correct' (row j)
