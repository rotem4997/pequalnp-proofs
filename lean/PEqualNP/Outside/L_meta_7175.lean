import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7175

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


/-- points on line `l` as a mask -/
def ln : List ℕ := [523, 4357, 6274, 3137, 5664, 2832, 1416, 708, 354, 177, 4184, 2092, 1046]

/-- the lines meeting no point of `X` (as a mask), recursively over the lines -/
def ms (X : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | b, a :: l => match Nat.beq (Nat.land X a) 0 with
    | true => Nat.add b (ms X (Nat.add b b) l)
    | false => ms X (Nat.add b b) l

def clo (X : ℕ) : Bool := Nat.beq (ms (ms X 1 ln) 1 ln) X

def cl : List ℕ := (List.range 8192).filter clo

theorem cl_len : cl.length ≤ 704 := by decide +kernel

theorem ms_bit (X : ℕ) : ∀ (L : List ℕ) (k i : ℕ), (ms X (2 ^ k) L).testBit (k + i) = (decide (i < L.length) && Nat.beq (Nat.land X (L.getD i 0)) 0) ∧ 2 ^ k ∣ ms X (2 ^ k) L := by
  intro L
  induction L with
  | nil => intro k i; simp [ms]
  | cons a L ih =>
    intro k i
    have e : Nat.add (2 ^ k) (2 ^ k) = 2 ^ (k + 1) := by
      show 2 ^ k + 2 ^ k = 2 ^ (k + 1); ring
    obtain ⟨c, hc⟩ := (ih (k + 1) 0).2
    have dv : 2 ^ k ∣ ms X (2 ^ (k + 1)) L := (pow_dvd_pow 2 (Nat.le_succ k)).trans (ih (k + 1) 0).2
    rw [ms, e]
    have key : ∀ j, (ms X (2 ^ (k + 1)) L).testBit (k + (j + 1)) = (decide (j < L.length) && Nat.beq (Nat.land X (L.getD j 0)) 0) := by
      intro j
      rw [← (ih (k + 1) j).1]; congr 1; omega
    have low : (ms X (2 ^ (k + 1)) L).testBit k = false := by
      rw [hc, Nat.testBit_two_pow_mul]; simp
    have shape : ms X (2 ^ (k + 1)) L = 2 ^ k * (2 * c) := by rw [hc]; ring
    cases hb : Nat.beq (Nat.land X a) 0 with
    | true =>
      have e2 : Nat.add (2 ^ k) (ms X (2 ^ (k + 1)) L) = 2 ^ k * (2 * c + 1) := by
        show 2 ^ k + _ = _; rw [shape]; ring
      refine ⟨?_, by rw [e2]; exact Dvd.intro _ rfl⟩
      rw [e2, Nat.testBit_two_pow_mul]
      rcases i with _ | j
      · have hb' := hb
        simp at hb'
        simp [hb']
      · have := key j
        rw [shape, Nat.testBit_two_pow_mul] at this
        simp only [show k ≤ k + (j + 1) by omega, decide_true, Bool.true_and, Nat.add_sub_cancel_left] at this ⊢
        rw [Nat.testBit_succ] at this ⊢
        rw [show (2 * c + 1) / 2 = c by omega]
        rw [show 2 * c / 2 = c by omega] at this
        rw [this]
        simp
    | false =>
      refine ⟨?_, dv⟩
      rcases i with _ | j
      · show (ms X (2 ^ (k + 1)) L).testBit k = (decide (0 < (a :: L).length) && Nat.beq (Nat.land X a) 0)
        rw [hb, Bool.and_false]; exact low
      · rw [key j]; simp

theorem ms_spec (X l : ℕ) (hl : l < 13) : (ms X 1 ln).testBit l = Nat.beq (Nat.land X (ln.getD l 0)) 0 := by
  have := (ms_bit X ln 0 l).1
  rw [pow_zero, Nat.zero_add] at this
  rw [this]
  have : ln.length = 13 := rfl
  simp [this, hl]

theorem ms_hi (X : ℕ) : ms X 1 ln < 2 ^ 13 := by
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  have := (ms_bit X ln 0 i).1
  rw [pow_zero, Nat.zero_add] at this
  rw [this]
  have h2 : ln.length = 13 := rfl
  simp [h2]; intro h; omega

def mk (x : Fin 13 → Bool) : ℕ := ∑ i : Fin 13, if x i then 2 ^ (i : ℕ) else 0

theorem ln_bit : ∀ l : Fin 13, ∀ p : Fin 13, (ln.getD l 0).testBit p = decide (((p : ℕ) + (l : ℕ)) % 13 ∈ [0, 1, 3, 9]) := by decide

theorem ln_lt : ∀ l : Fin 13, ln.getD l 0 < 2 ^ 13 := by decide

theorem meet (X : ℕ) (l : Fin 13) : Nat.beq (Nat.land X (ln.getD l 0)) 0 = true ↔ ∀ p : Fin 13, ((p : ℕ) + (l : ℕ)) % 13 ∈ [0, 1, 3, 9] → X.testBit p = false := by
  rw [Nat.beq_eq]
  constructor
  · intro h p hp
    have e : (Nat.land X (ln.getD l 0)).testBit p = (X.testBit p && (ln.getD l 0).testBit p) := Nat.testBit_and _ _ _
    rw [h, Nat.zero_testBit, ln_bit, decide_eq_true hp, Bool.and_true] at e
    exact e.symm
  · intro h
    refine Nat.eq_of_testBit_eq fun i => ?_
    have e : (Nat.land X (ln.getD l 0)).testBit i = (X.testBit i && (ln.getD l 0).testBit i) := Nat.testBit_and _ _ _
    rw [e, Nat.zero_testBit]
    by_cases hi : i < 13
    · have := ln_bit l ⟨i, hi⟩
      simp only at this
      rw [this]
      by_cases hd : (i + (l : ℕ)) % 13 ∈ [0, 1, 3, 9]
      · rw [h ⟨i, hi⟩ hd]; rfl
      · rw [decide_eq_false hd, Bool.and_false]
    · rw [Nat.testBit_lt_two_pow (x := ln.getD l 0) (lt_of_lt_of_le (ln_lt l) (Nat.pow_le_pow_right (by omega) (by omega))), Bool.and_false]

theorem ofb (x : Fin 13 → Bool) : ∃ X < 8192, ∀ i : Fin 13, X.testBit i = x i := by
  refine ⟨(BitVec.ofFnLE x).toNat, by simpa using (BitVec.ofFnLE x).isLt, fun i => ?_⟩
  have := BitVec.getLsbD_ofFnLE x i
  simpa [BitVec.getLsbD] using this

theorem ext8 {X Y : ℕ} (hX : X < 8192) (hY : Y < 8192) (h : ∀ i : Fin 13, X.testBit i = Y.testBit i) : X = Y := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < 13
  · exact h ⟨i, hi⟩
  · have e : 8192 ≤ 2 ^ i := (by norm_num : 8192 ≤ 2 ^ 13).trans (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7175

theorem PEqualNP.Outside.L_meta_7175 : have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∃ (x2 : Fin (756 : ℕ) → Fin (26 : ℕ) → Bool), ∀ (x3 : Fin (26 : ℕ) → Bool), Minimal x1 x3 ∨ Maximal (fun (x4 : Fin (26 : ℕ) → Bool) => ¬x1 x4) x3 → ∃ (x5 : Fin (756 : ℕ)), x2 x5 = x3 := by
  intro R
  classical
  let In : Fin 13 → Fin 13 → Prop := fun p l => ((p : ℕ) + (l : ℕ)) % 13 ∈ [0, 1, 3, 9]
  have sy : ∀ p l, In p l → In l p := by intro p l h; simp only [In] at h ⊢; rwa [add_comm]
  -- the 52 pairs
  have inc : ((Finset.univ : Finset (Fin 13 × Fin 13)).filter fun p => ((p.1 : ℕ) + (p.2 : ℕ)) % 13 ∈ [0, 1, 3, 9]).card ≤ 52 := by decide +kernel
  let mn : Fin 13 × Fin 13 → Fin 26 → Bool := fun p => fun i => decide (i = Fin.castAdd 13 p.1 ∨ i = Fin.natAdd 13 p.2)
  let mx : ℕ → Fin 26 → Bool := fun X => Fin.append (n := 13) (fun i : Fin 13 => X.testBit i) (fun l : Fin 13 => (PEqualNP.Outside.L_meta_7175.ms X 1 PEqualNP.Outside.L_meta_7175.ln).testBit l)
  let Z : Finset (Fin 26 → Bool) := (((Finset.univ : Finset (Fin 13 × Fin 13)).filter fun p => ((p.1 : ℕ) + (p.2 : ℕ)) % 13 ∈ [0, 1, 3, 9]).image mn) ∪ (PEqualNP.Outside.L_meta_7175.cl.toFinset.image mx)
  have hZ : Z.card ≤ 756 := by
    refine (Finset.card_union_le _ _).trans ?_
    have a1 := (Finset.card_image_le (s := (Finset.univ : Finset (Fin 13 × Fin 13)).filter fun p => ((p.1 : ℕ) + (p.2 : ℕ)) % 13 ∈ [0, 1, 3, 9]) (f := mn)).trans inc
    have a2 := (Finset.card_image_le (s := PEqualNP.Outside.L_meta_7175.cl.toFinset) (f := mx)).trans ((List.toFinset_card_le _).trans PEqualNP.Outside.L_meta_7175.cl_len)
    omega
  have sub : ∀ x : Fin 26 → Bool, Minimal R x ∨ Maximal (fun x => ¬R x) x → x ∈ Z := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨p, l, hpl, h1, h2⟩ := hx.prop
      refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨(p, l), by simpa using hpl, ?_⟩)
      have hR : R (mn (p, l)) := ⟨p, l, hpl, by simp [mn], by simp [mn]⟩
      have hle : mn (p, l) ≤ x := by
        intro i
        simp only [mn]
        by_cases hi : i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l
        · rcases hi with rfl | rfl
          · rw [h1]; exact le_top
          · rw [h2]; exact le_top
        · rw [decide_eq_false hi]; exact bot_le
      exact le_antisymm hle (hx.le_of_le hR hle)
    · refine Finset.mem_union_right _ ?_
      obtain ⟨X, hX, hXb⟩ := PEqualNP.Outside.L_meta_7175.ofb fun i => x (Fin.castAdd 13 i)
      obtain ⟨Y, hY, hYb⟩ := PEqualNP.Outside.L_meta_7175.ofb fun i => x (Fin.natAdd 13 i)
      have hn : ∀ p l : Fin 13, In p l → x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 l) = true → False := fun p l h h1 h2 => hx.prop ⟨p, l, h, h1, h2⟩
      -- adding a coordinate that keeps the input false is not possible
      have up : ∀ i : Fin 26, ¬R (Function.update x i true) → x i = true := by
        intro i h
        have hle : x ≤ Function.update x i true := by
          intro k
          by_cases hk : k = i
          · subst hk; rw [Function.update_self]; exact le_top
          · rw [Function.update_of_ne hk]
        have := hx.le_of_ge h hle i
        rw [Function.update_self] at this
        exact top_le_iff.1 this
      have ne1 : ∀ p l : Fin 13, (Fin.castAdd 13 p : Fin (13 + 13)) ≠ Fin.natAdd 13 l := by
        intro p l h
        have := congrArg Fin.val h
        simp at this; omega
      have Ybit : ∀ l : Fin 13, x (Fin.natAdd 13 l) = true ↔ ∀ p : Fin 13, In p l → X.testBit p = false := by
        intro l
        constructor
        · intro h p hp
          rw [hXb]
          by_contra hc
          exact hn p l hp (by simpa using hc) h
        · intro h
          refine up _ ?_
          rintro ⟨p, l', hpl, h1, h2⟩
          rw [Function.update_of_ne (ne1 p l)] at h1
          by_cases e : l' = l
          · subst e
            have := h p hpl
            rw [hXb, h1] at this; cases this
          · rw [Function.update_of_ne (by intro hh; exact e (Fin.natAdd_injective 13 13 hh))] at h2
            exact hn p l' hpl h1 h2
      have Xbit : ∀ p : Fin 13, x (Fin.castAdd 13 p) = true ↔ ∀ l : Fin 13, In p l → Y.testBit l = false := by
        intro p
        constructor
        · intro h l hl
          rw [hYb]
          by_contra hc
          exact hn p l hl h (by simpa using hc)
        · intro h
          refine up _ ?_
          rintro ⟨p', l, hpl, h1, h2⟩
          rw [Function.update_of_ne (ne1 p l).symm] at h2
          by_cases e : p' = p
          · subst e
            have := h l hpl
            rw [hYb, h2] at this; cases this
          · rw [Function.update_of_ne (by intro hh; exact e (Fin.castAdd_injective 13 13 hh))] at h1
            exact hn p' l hpl h1 h2
      have eY : PEqualNP.Outside.L_meta_7175.ms X 1 PEqualNP.Outside.L_meta_7175.ln = Y := by
        refine PEqualNP.Outside.L_meta_7175.ext8 (by simpa using PEqualNP.Outside.L_meta_7175.ms_hi X) hY fun l => ?_
        rw [PEqualNP.Outside.L_meta_7175.ms_spec _ _ l.isLt, hYb, Bool.eq_iff_iff, PEqualNP.Outside.L_meta_7175.meet, Ybit]
      have eX : PEqualNP.Outside.L_meta_7175.ms Y 1 PEqualNP.Outside.L_meta_7175.ln = X := by
        refine PEqualNP.Outside.L_meta_7175.ext8 (by simpa using PEqualNP.Outside.L_meta_7175.ms_hi Y) hX fun p => ?_
        rw [PEqualNP.Outside.L_meta_7175.ms_spec _ _ p.isLt, hXb, Bool.eq_iff_iff, PEqualNP.Outside.L_meta_7175.meet, Xbit]
        constructor
        · intro h l hl; exact h l (sy _ _ hl)
        · intro h l hl; exact h l (sy _ _ hl)
      refine Finset.mem_image.2 ⟨X, ?_, ?_⟩
      · rw [List.mem_toFinset, PEqualNP.Outside.L_meta_7175.cl, List.mem_filter, List.mem_range]
        refine ⟨hX, ?_⟩
        rw [PEqualNP.Outside.L_meta_7175.clo, eY, eX, Nat.beq_eq]
      · funext i
        refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
        · simp only [mx]
          rw [Fin.append_left, hXb]
        · simp only [mx]
          rw [Fin.append_right, eY, hYb]
  obtain ⟨e⟩ : Nonempty (Z ≃ Fin Z.card) := ⟨Z.equivFin⟩
  refine ⟨fun k => if h : (k : ℕ) < Z.card then (e.symm ⟨k, h⟩ : Fin 26 → Bool) else fun _ => false, fun x hx => ?_⟩
  have hm := sub x hx
  refine ⟨⟨(e ⟨x, hm⟩ : ℕ), lt_of_lt_of_le (e ⟨x, hm⟩).isLt hZ⟩, ?_⟩
  simp only [Fin.is_lt, dif_pos, Fin.eta, Equiv.symm_apply_apply]
