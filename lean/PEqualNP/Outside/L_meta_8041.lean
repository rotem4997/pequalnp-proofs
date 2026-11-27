import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8041

abbrev Inc (p w : Fin 13) : Prop := p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9

def pt (w d : ℕ) : ℕ := (w + d) % 13

def onB (p w : ℕ) : Bool := (523 : ℕ).testBit ((p + 13 - w) % 13)

def missB (a w : ℕ) : Bool :=
  !a.testBit (pt w 0) && !a.testBit (pt w 1) && !a.testBit (pt w 3) && !a.testBit (pt w 9)

def Lst : List ℕ := [7, 13, 19, 21, 25, 29, 35, 37, 39, 41, 67, 69, 71, 73, 77, 81, 83, 85,
  97, 101, 105, 131, 133, 135, 137, 141, 195, 201, 265, 273, 275, 281, 297, 329, 337, 549]

def closedB (a : ℕ) : Bool :=
  (List.range 13).all fun p => a.testBit p || (List.range 13).any fun w => missB a w && onB p w

def noLineB (a : ℕ) : Bool :=
  (List.range 13).all fun w => (List.range 13).any fun p => a.testBit p && !onB p w

def noPenB (a : ℕ) : Bool :=
  (List.range 13).all fun p => (List.range 13).any fun w => missB a w && !onB p w

def matchB (a : ℕ) : Bool :=
  Lst.any fun x => (List.range 13).any fun s => (List.range 13).all fun p =>
    a.testBit p == x.testBit ((p + 13 - s) % 13)

def chk (a : ℕ) : Bool := !closedB a || !noLineB a || !noPenB a || matchB a

theorem chk_0 : ∀ k < 8, ∀ j < 128, chk (1024 * 0 + 128 * k + j) = true := by decide +kernel

theorem chk_1 : ∀ k < 8, ∀ j < 128, chk (1024 * 1 + 128 * k + j) = true := by decide +kernel

theorem chk_2 : ∀ k < 8, ∀ j < 128, chk (1024 * 2 + 128 * k + j) = true := by decide +kernel

theorem chk_3 : ∀ k < 8, ∀ j < 128, chk (1024 * 3 + 128 * k + j) = true := by decide +kernel

theorem chk_4 : ∀ k < 8, ∀ j < 128, chk (1024 * 4 + 128 * k + j) = true := by decide +kernel

theorem chk_5 : ∀ k < 8, ∀ j < 128, chk (1024 * 5 + 128 * k + j) = true := by decide +kernel

theorem chk_6 : ∀ k < 8, ∀ j < 128, chk (1024 * 6 + 128 * k + j) = true := by decide +kernel

theorem chk_7 : ∀ k < 8, ∀ j < 128, chk (1024 * 7 + 128 * k + j) = true := by decide +kernel

theorem chk_at (b : ℕ) (h : b < 8192) : chk b = true := by
  have hd : b = 1024 * (b / 1024) + 128 * ((b % 1024) / 128) + (b % 1024) % 128 := by omega
  have hk : (b % 1024) / 128 < 8 := by omega
  have hj : (b % 1024) % 128 < 128 := by omega
  have hm : b / 1024 < 8 := by omega
  rw [hd]
  generalize b / 1024 = m at hm ⊢
  generalize (b % 1024) / 128 = k at hk ⊢
  generalize (b % 1024) % 128 = j at hj ⊢
  interval_cases m
  · exact chk_0 k hk j hj
  · exact chk_1 k hk j hj
  · exact chk_2 k hk j hj
  · exact chk_3 k hk j hj
  · exact chk_4 k hk j hj
  · exact chk_5 k hk j hj
  · exact chk_6 k hk j hj
  · exact chk_7 k hk j hj

theorem inc_onB : ∀ p w : Fin 13, Inc p w ↔ onB p.val w.val = true := by decide +kernel

theorem sub_val : ∀ q s : Fin 13, (q - s).val = (q.val + 13 - s.val) % 13 := by decide +kernel

theorem pt_lt : ∀ w < 13, pt w 0 < 13 ∧ pt w 1 < 13 ∧ pt w 3 < 13 ∧ pt w 9 < 13 := by
  decide +kernel

theorem pt_on : ∀ w < 13, onB (pt w 0) w = true ∧ onB (pt w 1) w = true ∧
    onB (pt w 3) w = true ∧ onB (pt w 9) w = true := by
  decide +kernel

theorem pt_cov : ∀ w < 13, ∀ p < 13, onB p w = true →
    (p = pt w 0 ∨ p = pt w 1 ∨ p = pt w 3 ∨ p = pt w 9) := by
  decide +kernel

theorem bfalse (b : Bool) (h : b = true → False) : b = false := by
  cases b
  · rfl
  · exact (h rfl).elim

theorem missB_sound (a w p : ℕ) (hw : w < 13) (hp : p < 13) (h : missB a w = true)
    (ho : onB p w = true) : a.testBit p = false := by
  simp only [missB, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h0, h1⟩, h3⟩, h9⟩ := h
  rcases pt_cov w hw p hp ho with e | e | e | e <;> rw [e] <;> assumption

theorem missB_complete (a w : ℕ) (hw : w < 13)
    (h : ∀ p < 13, onB p w = true → a.testBit p = false) : missB a w = true := by
  have hlt := pt_lt w hw
  have hon := pt_on w hw
  simp only [missB, Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨⟨⟨h _ hlt.1 hon.1, h _ hlt.2.1 hon.2.1⟩, h _ hlt.2.2.1 hon.2.2.1⟩,
    h _ hlt.2.2.2 hon.2.2.2⟩

def msk (f : Fin 13 → Bool) : ℕ := Nat.ofBits f

theorem msk_bit (f : Fin 13 → Bool) (i : ℕ) (h : i < 13) : (msk f).testBit i = f ⟨i, h⟩ :=
  Nat.testBit_ofBits_lt f i h

theorem msk_lt (f : Fin 13 → Bool) : msk f < 8192 :=
  lt_of_lt_of_eq (Nat.ofBits_lt_two_pow f) (by norm_num)

theorem core (X Y : Finset (Fin 13))
    (missing : ∀ l : Fin 13, l ∈ Y ↔ ∀ p ∈ X, ¬Inc p l)
    (closed : ∀ p : Fin 13, p ∉ X → ∃ l ∈ Y, Inc p l)
    (noLine : ∀ l : Fin 13, ∃ p ∈ X, ¬Inc p l)
    (noPen : ∀ p : Fin 13, ∃ l ∈ Y, ¬Inc p l) :
    ∃ x ∈ Lst, ∃ s : Fin 13, ∀ q : Fin 13, q ∈ X ↔ x.testBit (q - s).val = true := by
  set a := msk (fun p => decide (p ∈ X)) with ha
  have fX : ∀ p : Fin 13, a.testBit p.val = true ↔ p ∈ X := by
    intro p
    rw [ha, msk_bit _ p.val p.isLt]
    simp
  have missA : ∀ l : Fin 13, missB a l.val = true ↔ l ∈ Y := by
    intro l
    rw [missing l]
    constructor
    · intro hm p hp hi
      have hq := missB_sound a l.val p.val l.isLt p.isLt hm ((inc_onB p l).mp hi)
      rw [(fX p).mpr hp] at hq
      exact Bool.noConfusion hq
    · intro h
      exact missB_complete a l.val l.isLt (fun p hp ho => bfalse _ (fun hq =>
        h ⟨p, hp⟩ ((fX ⟨p, hp⟩).mp hq) ((inc_onB ⟨p, hp⟩ l).mpr ho)))
  have c1 : closedB a = true := by
    unfold closedB
    rw [List.all_eq_true]
    intro p hp
    have hpl : p < 13 := List.mem_range.mp hp
    rw [Bool.or_eq_true]
    by_cases hb : a.testBit p = true
    · exact Or.inl hb
    · right
      have hnx : (⟨p, hpl⟩ : Fin 13) ∉ X := fun hx => hb ((fX ⟨p, hpl⟩).mpr hx)
      obtain ⟨l, hl, hi⟩ := closed _ hnx
      rw [List.any_eq_true]
      exact ⟨l.val, List.mem_range.mpr l.isLt, by
        rw [Bool.and_eq_true]
        exact ⟨(missA l).mpr hl, (inc_onB _ l).mp hi⟩⟩
  have c2 : noLineB a = true := by
    unfold noLineB
    rw [List.all_eq_true]
    intro w hw
    have hwl : w < 13 := List.mem_range.mp hw
    obtain ⟨p, hp, hi⟩ := noLine ⟨w, hwl⟩
    rw [List.any_eq_true]
    refine ⟨p.val, List.mem_range.mpr p.isLt, ?_⟩
    rw [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨(fX p).mpr hp, bfalse _ (fun ho => hi ((inc_onB p ⟨w, hwl⟩).mpr ho))⟩
  have c3 : noPenB a = true := by
    unfold noPenB
    rw [List.all_eq_true]
    intro p hp
    have hpl : p < 13 := List.mem_range.mp hp
    obtain ⟨l, hl, hi⟩ := noPen ⟨p, hpl⟩
    rw [List.any_eq_true]
    refine ⟨l.val, List.mem_range.mpr l.isLt, ?_⟩
    rw [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨(missA l).mpr hl, bfalse _ (fun ho => hi ((inc_onB ⟨p, hpl⟩ l).mpr ho))⟩
  have hc := chk_at a (msk_lt _)
  simp only [chk, c1, c2, c3, Bool.not_true, Bool.false_or] at hc
  unfold matchB at hc
  rw [List.any_eq_true] at hc
  obtain ⟨x, hx, hs⟩ := hc
  rw [List.any_eq_true] at hs
  obtain ⟨s, hsr, hall⟩ := hs
  have hsl : s < 13 := List.mem_range.mp hsr
  rw [List.all_eq_true] at hall
  refine ⟨x, hx, ⟨s, hsl⟩, fun q => ?_⟩
  have e := hall q.val (List.mem_range.mpr q.isLt)
  rw [beq_iff_eq] at e
  rw [← fX q, e, sub_val]

end PEqualNP.Outside.L_meta_8041

set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.L_meta_8041 : ∀ (x1 x2 : Finset (Fin (13 : ℕ))),   PEqualNP.GenericRejection.IsMaximalFalse (fun (x3 : Fin (13 : ℕ)) => {x3, x3 + (1 : Fin (13 : ℕ)), x3 + (3 : Fin (13 : ℕ)), x3 + (9 : Fin (13 : ℕ))}) x1 x2 →     PEqualNP.GenericRejection.IsGeneric (fun (x4 : Fin (13 : ℕ)) => {x4, x4 + (1 : Fin (13 : ℕ)), x4 + (3 : Fin (13 : ℕ)), x4 + (9 : Fin (13 : ℕ))}) (3 : ℕ) x1 x2 →       ∃         x5 ∈           have x6 : List ℕ :=             have x6 : List ℕ :=               have x6 : List ℕ := [(281 : ℕ), (297 : ℕ), (329 : ℕ), (337 : ℕ), (549 : ℕ)];               (201 : ℕ) :: (265 : ℕ) :: (273 : ℕ) :: (275 : ℕ) :: x6;             have x7 : List ℕ := (133 : ℕ) :: (135 : ℕ) :: (137 : ℕ) :: (141 : ℕ) :: (195 : ℕ) :: x6;             (97 : ℕ) :: (101 : ℕ) :: (105 : ℕ) :: (131 : ℕ) :: x7;           have x7 : List ℕ :=             have x7 : List ℕ := (73 : ℕ) :: (77 : ℕ) :: (81 : ℕ) :: (83 : ℕ) :: (85 : ℕ) :: x6;             (41 : ℕ) :: (67 : ℕ) :: (69 : ℕ) :: (71 : ℕ) :: x7;           have x8 : List ℕ := (25 : ℕ) :: (29 : ℕ) :: (35 : ℕ) :: (37 : ℕ) :: (39 : ℕ) :: x7;           (7 : ℕ) :: (13 : ℕ) :: (19 : ℕ) :: (21 : ℕ) :: x8,         ∃ (x6 : Fin (13 : ℕ)), (∀ (x7 : Fin (13 : ℕ)), x7 ∈ x1 ↔ x5.testBit ↑(x7 - x6) = Bool.true) ∧ ∀ (x7 : Fin (13 : ℕ)), x7 ∈ x2 ↔ ∀ x8 ∈ x1, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ))) := by
  intro X Y hmax hgen
  have inc : ∀ p l : Fin 13,
      p ∈ (fun x3 : Fin 13 => ({x3, x3 + 1, x3 + 3, x3 + 9} : Finset (Fin 13))) l ↔
        PEqualNP.Outside.L_meta_8041.Inc p l := by
    decide +kernel
  have disj : ∀ l ∈ Y, ∀ p ∈ X, ¬PEqualNP.Outside.L_meta_8041.Inc p l :=
    fun l hl p hp hin => Finset.disjoint_left.mp (hmax.1 l hl) ((inc p l).mpr hin) hp
  have missing (l : Fin 13) : l ∈ Y ↔ ∀ p ∈ X, ¬PEqualNP.Outside.L_meta_8041.Inc p l := by
    constructor
    · intro hl p hp h
      exact disj l hl p hp h
    · intro h
      by_contra hn
      apply hmax.2.2 l hn
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Finset.disjoint_left.mpr fun p hp hx => h p hx ((inc p _).mp hp)
      · exact hmax.1 j hj
  have closed (p : Fin 13) (hp : p ∉ X) : ∃ l ∈ Y, PEqualNP.Outside.L_meta_8041.Inc p l := by
    by_contra hno
    apply hmax.2.1 p hp
    intro l hl
    apply Finset.disjoint_left.mpr
    intro a ha hm
    rcases Finset.mem_insert.mp hm with e | hm
    · subst e
      exact hno ⟨l, hl, (inc _ l).mp ha⟩
    · exact disj l hl a hm ((inc a l).mp ha)
  have noLine (l : Fin 13) : ∃ p ∈ X, ¬PEqualNP.Outside.L_meta_8041.Inc p l := by
    by_contra! h
    exact hgen.2.2.1 l (fun p hp => (inc p l).mpr (h p hp))
  have noPen (p : Fin 13) : ∃ l ∈ Y, ¬PEqualNP.Outside.L_meta_8041.Inc p l := by
    by_contra! h
    exact hgen.2.2.2 p (fun l hl => (inc p l).mpr (h l hl))
  obtain ⟨x, hx, s, hs⟩ := PEqualNP.Outside.L_meta_8041.core X Y missing closed noLine noPen
  exact ⟨x, hx, s, hs, missing⟩
