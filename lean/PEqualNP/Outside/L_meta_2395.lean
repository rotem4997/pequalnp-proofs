import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2395

abbrev Inc (p w : Fin 13) : Prop := p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9

def pt (w d : ℕ) : ℕ := (w + d) % 13

def onB (p w : ℕ) : Bool := (523 : ℕ).testBit ((p + 13 - w) % 13)

def missB (a w : ℕ) : Bool :=
  !a.testBit (pt w 0) && !a.testBit (pt w 1) && !a.testBit (pt w 3) && !a.testBit (pt w 9)

def offB (c p : ℕ) : Bool :=
  !c.testBit (pt p 0) && !c.testBit (pt p 4) && !c.testBit (pt p 10) && !c.testBit (pt p 12)

def no3 (x y z : Bool) : Bool := !(x && y && z)

def arcB (a : ℕ) : Bool :=
  (List.range 13).all fun w =>
    no3 (a.testBit (pt w 0)) (a.testBit (pt w 1)) (a.testBit (pt w 3)) &&
    no3 (a.testBit (pt w 0)) (a.testBit (pt w 1)) (a.testBit (pt w 9)) &&
    no3 (a.testBit (pt w 0)) (a.testBit (pt w 3)) (a.testBit (pt w 9)) &&
    no3 (a.testBit (pt w 1)) (a.testBit (pt w 3)) (a.testBit (pt w 9))

def darcB (b : ℕ) : Bool :=
  (List.range 13).all fun p =>
    no3 (b.testBit (pt p 0)) (b.testBit (pt p 4)) (b.testBit (pt p 10)) &&
    no3 (b.testBit (pt p 0)) (b.testBit (pt p 4)) (b.testBit (pt p 12)) &&
    no3 (b.testBit (pt p 0)) (b.testBit (pt p 10)) (b.testBit (pt p 12)) &&
    no3 (b.testBit (pt p 4)) (b.testBit (pt p 10)) (b.testBit (pt p 12))

def nonconcB (c : ℕ) : Bool :=
  (List.range 13).all fun p => (List.range 13).any fun l => c.testBit l && !onB p l

def nlB (c : ℕ) : Bool :=
  (List.range 13).all fun l => (List.range 13).any fun p => offB c p && !onB p l

def genB (c : ℕ) : Bool := nonconcB c && nlB c

def smallB (b : ℕ) : Bool :=
  b == 0 || (List.range 13).any fun l => (List.range 13).any fun m =>
    decide (l ≤ m) && b == ((2 ^ l) ||| (2 ^ m))

def chk1 (b : ℕ) : Bool := !darcB b || genB b || smallB b

def lm (w : ℕ) : ℕ := 2 ^ pt w 0 + 2 ^ pt w 1 + 2 ^ pt w 3 + 2 ^ pt w 9

def ncB (l m n : ℕ) : Bool := (lm l &&& lm m &&& lm n) == 0

def subB (a l m : ℕ) : Bool := !(missB a l && missB a m) ||
  (List.range 13).any fun n1 => missB a n1 && (List.range 13).any fun n2 =>
    missB a n2 && (m == l || m == n1 || m == n2) && ncB l n1 n2

def chk2 (a : ℕ) : Bool :=
  !arcB a || ((List.range 13).any (fun l => missB a l) &&
    (List.range 13).all fun l => (List.range 13).all fun m => decide (m < l) || subB a l m)

theorem chk1_all : ∀ k < 64, ∀ j < 128, chk1 (128 * k + j) = true := by decide +kernel

theorem chk2_all : ∀ k < 64, ∀ j < 128, chk2 (128 * k + j) = true := by decide +kernel

theorem tri_gen : ∀ l < 13, ∀ m < 13, ∀ n < 13, ncB l m n = true →
    genB (((2 ^ l) ||| (2 ^ m)) ||| (2 ^ n)) = true := by decide +kernel

theorem chk1_at (b : ℕ) (h : b < 8192) : chk1 b = true := by
  have := chk1_all (b / 128) (by omega) (b % 128) (by omega)
  rwa [Nat.div_add_mod] at this

theorem chk2_at (a : ℕ) (h : a < 8192) : chk2 a = true := by
  have := chk2_all (a / 128) (by omega) (a % 128) (by omega)
  rwa [Nat.div_add_mod] at this

theorem inc_onB : ∀ p w : Fin 13, Inc p w ↔ onB p.val w.val = true := by decide +kernel

theorem pt_lt : ∀ w < 13, pt w 0 < 13 ∧ pt w 1 < 13 ∧ pt w 3 < 13 ∧ pt w 9 < 13 := by
  decide +kernel

theorem pt_ne : ∀ w < 13, pt w 0 ≠ pt w 1 ∧ pt w 0 ≠ pt w 3 ∧ pt w 0 ≠ pt w 9 ∧
    pt w 1 ≠ pt w 3 ∧ pt w 1 ≠ pt w 9 ∧ pt w 3 ≠ pt w 9 := by
  decide +kernel

theorem pt_on : ∀ w < 13, onB (pt w 0) w = true ∧ onB (pt w 1) w = true ∧
    onB (pt w 3) w = true ∧ onB (pt w 9) w = true := by
  decide +kernel

theorem pt_cov : ∀ w < 13, ∀ p < 13, onB p w = true →
    (p = pt w 0 ∨ p = pt w 1 ∨ p = pt w 3 ∨ p = pt w 9) := by
  decide +kernel

theorem pt_facts (w : ℕ) (hw : w < 13) :
    (pt w 0 < 13 ∧ pt w 1 < 13 ∧ pt w 3 < 13 ∧ pt w 9 < 13) ∧
    (pt w 0 ≠ pt w 1 ∧ pt w 0 ≠ pt w 3 ∧ pt w 0 ≠ pt w 9 ∧ pt w 1 ≠ pt w 3 ∧
      pt w 1 ≠ pt w 9 ∧ pt w 3 ≠ pt w 9) ∧
    (onB (pt w 0) w = true ∧ onB (pt w 1) w = true ∧ onB (pt w 3) w = true ∧
      onB (pt w 9) w = true) ∧
    ∀ p < 13, onB p w = true → (p = pt w 0 ∨ p = pt w 1 ∨ p = pt w 3 ∨ p = pt w 9) :=
  ⟨pt_lt w hw, pt_ne w hw, pt_on w hw, pt_cov w hw⟩

theorem dpt_lt : ∀ p < 13, pt p 0 < 13 ∧ pt p 4 < 13 ∧ pt p 10 < 13 ∧ pt p 12 < 13 := by
  decide +kernel

theorem dpt_ne : ∀ p < 13, pt p 0 ≠ pt p 4 ∧ pt p 0 ≠ pt p 10 ∧ pt p 0 ≠ pt p 12 ∧
    pt p 4 ≠ pt p 10 ∧ pt p 4 ≠ pt p 12 ∧ pt p 10 ≠ pt p 12 := by
  decide +kernel

theorem dpt_on : ∀ p < 13, onB p (pt p 0) = true ∧ onB p (pt p 4) = true ∧
    onB p (pt p 10) = true ∧ onB p (pt p 12) = true := by
  decide +kernel

theorem dpt_cov : ∀ p < 13, ∀ l < 13, onB p l = true →
    (l = pt p 0 ∨ l = pt p 4 ∨ l = pt p 10 ∨ l = pt p 12) := by
  decide +kernel

theorem dpt_facts (p : ℕ) (hp : p < 13) :
    (pt p 0 < 13 ∧ pt p 4 < 13 ∧ pt p 10 < 13 ∧ pt p 12 < 13) ∧
    (pt p 0 ≠ pt p 4 ∧ pt p 0 ≠ pt p 10 ∧ pt p 0 ≠ pt p 12 ∧ pt p 4 ≠ pt p 10 ∧
      pt p 4 ≠ pt p 12 ∧ pt p 10 ≠ pt p 12) ∧
    (onB p (pt p 0) = true ∧ onB p (pt p 4) = true ∧ onB p (pt p 10) = true ∧
      onB p (pt p 12) = true) ∧
    ∀ l < 13, onB p l = true → (l = pt p 0 ∨ l = pt p 4 ∨ l = pt p 10 ∨ l = pt p 12) :=
  ⟨dpt_lt p hp, dpt_ne p hp, dpt_on p hp, dpt_cov p hp⟩

theorem bfalse (b : Bool) (h : b = true → False) : b = false := by
  cases b
  · rfl
  · exact (h rfl).elim

theorem missB_sound (a w p : ℕ) (hw : w < 13) (hp : p < 13) (h : missB a w = true)
    (ho : onB p w = true) : a.testBit p = false := by
  simp only [missB, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h0, h1⟩, h3⟩, h9⟩ := h
  rcases (pt_facts w hw).2.2.2 p hp ho with e | e | e | e <;> rw [e] <;> assumption

theorem missB_complete (a w : ℕ) (hw : w < 13)
    (h : ∀ p < 13, onB p w = true → a.testBit p = false) : missB a w = true := by
  obtain ⟨hlt, -, hon, -⟩ := pt_facts w hw
  simp only [missB, Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨⟨⟨h _ hlt.1 hon.1, h _ hlt.2.1 hon.2.1⟩, h _ hlt.2.2.1 hon.2.2.1⟩,
    h _ hlt.2.2.2 hon.2.2.2⟩

theorem offB_sound (c p l : ℕ) (hp : p < 13) (hl : l < 13) (h : offB c p = true)
    (ho : onB p l = true) : c.testBit l = false := by
  simp only [offB, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h0, h1⟩, h3⟩, h9⟩ := h
  rcases (dpt_facts p hp).2.2.2 l hl ho with e | e | e | e <;> rw [e] <;> assumption

theorem offB_complete (c p : ℕ) (hp : p < 13)
    (h : ∀ l < 13, onB p l = true → c.testBit l = false) : offB c p = true := by
  obtain ⟨hlt, -, hon, -⟩ := dpt_facts p hp
  simp only [offB, Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨⟨⟨h _ hlt.1 hon.1, h _ hlt.2.1 hon.2.1⟩, h _ hlt.2.2.1 hon.2.2.1⟩,
    h _ hlt.2.2.2 hon.2.2.2⟩

def msk (f : Fin 13 → Bool) : ℕ := Nat.ofBits f

theorem msk_bit (f : Fin 13 → Bool) (i : ℕ) (h : i < 13) : (msk f).testBit i = f ⟨i, h⟩ :=
  Nat.testBit_ofBits_lt f i h

theorem msk_lt (f : Fin 13 → Bool) : msk f < 8192 :=
  lt_of_lt_of_eq (Nat.ofBits_lt_two_pow f) (by norm_num)

theorem n3 (f : Fin 13 → Bool) (R : Fin 13 → Prop)
    (h : ∀ u v w : Fin 13, f u = true → f v = true → f w = true → u ≠ v → u ≠ w → v ≠ w →
      R u → R v → R w → False)
    (i j k : ℕ) (hi : i < 13) (hj : j < 13) (hk : k < 13) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (ri : R ⟨i, hi⟩) (rj : R ⟨j, hj⟩) (rk : R ⟨k, hk⟩) :
    no3 ((msk f).testBit i) ((msk f).testBit j) ((msk f).testBit k) = true := by
  rw [msk_bit f i hi, msk_bit f j hj, msk_bit f k hk]
  by_cases hb : f ⟨i, hi⟩ = true ∧ f ⟨j, hj⟩ = true ∧ f ⟨k, hk⟩ = true
  · exact (h _ _ _ hb.1 hb.2.1 hb.2.2 (fun e => hij (congrArg Fin.val e))
      (fun e => hik (congrArg Fin.val e)) (fun e => hjk (congrArg Fin.val e)) ri rj rk).elim
  · revert hb
    generalize f ⟨i, hi⟩ = u1
    generalize f ⟨j, hj⟩ = u2
    generalize f ⟨k, hk⟩ = u3
    revert u1 u2 u3
    decide

theorem arc_of (f : Fin 13 → Bool)
    (h : ∀ l u v w : Fin 13, f u = true → f v = true → f w = true → u ≠ v → u ≠ w → v ≠ w →
      Inc u l → Inc v l → Inc w l → False) : arcB (msk f) = true := by
  unfold arcB
  rw [List.all_eq_true]
  intro w hw
  have hwlt : w < 13 := List.mem_range.mp hw
  obtain ⟨⟨l0, l1, l3, l9⟩, ⟨d01, d03, d09, d13, d19, d39⟩, ⟨o0, o1, o3, o9⟩, -⟩ :=
    pt_facts w hwlt
  have r : ∀ (i : ℕ) (hi : i < 13), onB i w = true → Inc ⟨i, hi⟩ ⟨w, hwlt⟩ :=
    fun i hi ho => (inc_onB ⟨i, hi⟩ ⟨w, hwlt⟩).mpr ho
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨n3 f (fun u => Inc u ⟨w, hwlt⟩) (h ⟨w, hwlt⟩) _ _ _ l0 l1 l3 d01 d03 d13
        (r _ l0 o0) (r _ l1 o1) (r _ l3 o3),
      n3 f (fun u => Inc u ⟨w, hwlt⟩) (h ⟨w, hwlt⟩) _ _ _ l0 l1 l9 d01 d09 d19
        (r _ l0 o0) (r _ l1 o1) (r _ l9 o9)⟩,
    n3 f (fun u => Inc u ⟨w, hwlt⟩) (h ⟨w, hwlt⟩) _ _ _ l0 l3 l9 d03 d09 d39
      (r _ l0 o0) (r _ l3 o3) (r _ l9 o9)⟩,
    n3 f (fun u => Inc u ⟨w, hwlt⟩) (h ⟨w, hwlt⟩) _ _ _ l1 l3 l9 d13 d19 d39
      (r _ l1 o1) (r _ l3 o3) (r _ l9 o9)⟩

theorem darc_of (g : Fin 13 → Bool)
    (h : ∀ p u v w : Fin 13, g u = true → g v = true → g w = true → u ≠ v → u ≠ w → v ≠ w →
      Inc p u → Inc p v → Inc p w → False) : darcB (msk g) = true := by
  unfold darcB
  rw [List.all_eq_true]
  intro p hp
  have hplt : p < 13 := List.mem_range.mp hp
  obtain ⟨⟨l0, l1, l3, l9⟩, ⟨d01, d03, d09, d13, d19, d39⟩, ⟨o0, o1, o3, o9⟩, -⟩ :=
    dpt_facts p hplt
  have r : ∀ (i : ℕ) (hi : i < 13), onB p i = true → Inc ⟨p, hplt⟩ ⟨i, hi⟩ :=
    fun i hi ho => (inc_onB ⟨p, hplt⟩ ⟨i, hi⟩).mpr ho
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨n3 g (fun u => Inc ⟨p, hplt⟩ u) (h ⟨p, hplt⟩) _ _ _ l0 l1 l3 d01 d03 d13
        (r _ l0 o0) (r _ l1 o1) (r _ l3 o3),
      n3 g (fun u => Inc ⟨p, hplt⟩ u) (h ⟨p, hplt⟩) _ _ _ l0 l1 l9 d01 d09 d19
        (r _ l0 o0) (r _ l1 o1) (r _ l9 o9)⟩,
    n3 g (fun u => Inc ⟨p, hplt⟩ u) (h ⟨p, hplt⟩) _ _ _ l0 l3 l9 d03 d09 d39
      (r _ l0 o0) (r _ l3 o3) (r _ l9 o9)⟩,
    n3 g (fun u => Inc ⟨p, hplt⟩ u) (h ⟨p, hplt⟩) _ _ _ l1 l3 l9 d13 d19 d39
      (r _ l1 o1) (r _ l3 o3) (r _ l9 o9)⟩

theorem wit_spec (X Y : Finset (Fin 13)) (c : ℕ)
    (hY : ∀ l ∈ Y, c.testBit l.val = true)
    (hX : ∀ l : Fin 13, c.testBit l.val = true → ∀ p ∈ X, ¬Inc p l)
    (hnc : nonconcB c = true) (hnl : nlB c = true) :
    ∃ Z : Finset (Fin 13), X ⊆ Z ∧ (∀ l ∈ Y, ∀ p ∈ Z, ¬Inc p l) ∧
      (∀ p ∉ Z, ∃ l : Fin 13, (∀ q ∈ Z, ¬Inc q l) ∧ Inc p l) ∧
      (¬∃ l : Fin 13, ∀ p ∈ Z, Inc p l) ∧
      ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ Z, ¬Inc q l) → Inc p l := by
  have mem : ∀ p : Fin 13,
      p ∈ Finset.univ.filter (fun p : Fin 13 => offB c p.val = true) ↔ offB c p.val = true := by
    intro p
    simp
  have lmiss : ∀ l : Fin 13, c.testBit l.val = true →
      ∀ q ∈ Finset.univ.filter (fun p : Fin 13 => offB c p.val = true), ¬Inc q l := by
    intro l hc q hq hi
    have h := offB_sound c q.val l.val q.isLt l.isLt ((mem q).mp hq) ((inc_onB q l).mp hi)
    rw [hc] at h
    exact Bool.noConfusion h
  simp only [nonconcB, List.all_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    Bool.not_eq_true'] at hnc
  simp only [nlB, List.all_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    Bool.not_eq_true'] at hnl
  refine ⟨Finset.univ.filter (fun p : Fin 13 => offB c p.val = true), ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [mem]
    exact offB_complete c p.val p.isLt (fun l hl ho => bfalse _ (fun hq =>
      hX ⟨l, hl⟩ hq p hp ((inc_onB p ⟨l, hl⟩).mpr ho)))
  · intro l hl p hp
    exact lmiss l (hY l hl) p hp
  · intro p hp
    rw [mem] at hp
    by_contra hcon
    apply hp
    exact offB_complete c p.val p.isLt (fun l hl ho => bfalse _ (fun hq =>
      hcon ⟨⟨l, hl⟩, lmiss ⟨l, hl⟩ hq, (inc_onB p ⟨l, hl⟩).mpr ho⟩))
  · rintro ⟨l, h⟩
    obtain ⟨p, hp, ho, hn⟩ := hnl l.val l.isLt
    have hi := h ⟨p, hp⟩ ((mem ⟨p, hp⟩).mpr ho)
    have hq := (inc_onB ⟨p, hp⟩ l).mp hi
    rw [hn] at hq
    exact Bool.noConfusion hq
  · rintro ⟨p, h⟩
    obtain ⟨l, hl, hc, hn⟩ := hnc p.val p.isLt
    have hi := h ⟨l, hl⟩ (lmiss ⟨l, hl⟩ hc)
    have hq := (inc_onB p ⟨l, hl⟩).mp hi
    rw [hn] at hq
    exact Bool.noConfusion hq

theorem c_bits (l m1 n1 k : ℕ)
    (h : (((2 ^ l) ||| (2 ^ m1)) ||| (2 ^ n1)).testBit k = true) :
    k = l ∨ k = m1 ∨ k = n1 := by
  simp only [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at h
  omega

theorem core2 (X Y : Finset (Fin 13)) (a b : ℕ) (ha : a < 8192) (hb : b < 8192)
    (fX : ∀ p : Fin 13, a.testBit p.val = true ↔ p ∈ X)
    (fY : ∀ l : Fin 13, b.testBit l.val = true ↔ l ∈ Y)
    (hA : arcB a = true) (hB : darcB b = true)
    (h1 : ∀ p ∈ X, ∀ l ∈ Y, ¬Inc p l) :
    ∃ Z : Finset (Fin 13), X ⊆ Z ∧ (∀ l ∈ Y, ∀ p ∈ Z, ¬Inc p l) ∧
      (∀ p ∉ Z, ∃ l : Fin 13, (∀ q ∈ Z, ¬Inc q l) ∧ Inc p l) ∧
      (¬∃ l : Fin 13, ∀ p ∈ Z, Inc p l) ∧
      ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ Z, ¬Inc q l) → Inc p l := by
  have F4 : ∀ l : Fin 13, missB a l.val = true → ∀ p ∈ X, ¬Inc p l := by
    intro l hm p hp hi
    have hq := missB_sound a l.val p.val l.isLt p.isLt hm ((inc_onB p l).mp hi)
    rw [(fX p).mpr hp] at hq
    exact Bool.noConfusion hq
  have F5 : ∀ l ∈ Y, missB a l.val = true := by
    intro l hl
    exact missB_complete a l.val l.isLt (fun p hp ho => bfalse _ (fun hq =>
      h1 ⟨p, hp⟩ ((fX ⟨p, hp⟩).mp hq) l hl ((inc_onB ⟨p, hp⟩ l).mpr ho)))
  have c1 := chk1_at b hb
  have c2 := chk2_at a ha
  simp only [chk1, hB, Bool.not_true, Bool.false_or, Bool.or_eq_true] at c1
  simp only [chk2, hA, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.any_eq_true,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at c2
  obtain ⟨⟨l0, hl0, hm0⟩, c2⟩ := c2
  have done2 : ∀ l m : ℕ, l < 13 → m < 13 → l ≤ m → missB a l = true → missB a m = true →
      (∀ k ∈ Y, ((2 ^ l) ||| (2 ^ m)).testBit k.val = true) →
      ∃ Z : Finset (Fin 13), X ⊆ Z ∧ (∀ l ∈ Y, ∀ p ∈ Z, ¬Inc p l) ∧
        (∀ p ∉ Z, ∃ l : Fin 13, (∀ q ∈ Z, ¬Inc q l) ∧ Inc p l) ∧
        (¬∃ l : Fin 13, ∀ p ∈ Z, Inc p l) ∧
        ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ Z, ¬Inc q l) → Inc p l := by
    intro l m hl hm hlm ml mm hk
    rcases c2 l hl m hm with hlt | hs
    · omega
    · simp only [subB, ml, mm, Bool.and_true, Bool.not_true, Bool.false_or,
        List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
      obtain ⟨m1, hm1, mm1, n1, hn1, ⟨mn1, hmem⟩, hncB⟩ := hs
      have hg := tri_gen l hl m1 hm1 n1 hn1 hncB
      simp only [genB, Bool.and_eq_true] at hg
      refine wit_spec X Y _ ?_ ?_ hg.1 hg.2
      · intro k hkY
        have hq := hk k hkY
        simp only [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true,
          decide_eq_true_eq] at hq ⊢
        omega
      · intro k hc p hp
        rcases c_bits l m1 n1 k.val hc with e | e | e
        · exact F4 k (by rw [e]; exact ml) p hp
        · exact F4 k (by rw [e]; exact mm1) p hp
        · exact F4 k (by rw [e]; exact mn1) p hp
  rcases c1 with hg | hs
  · simp only [genB, Bool.and_eq_true] at hg
    exact wit_spec X Y b (fun l hl => (fY l).mpr hl)
      (fun l hc p hp => h1 p hp l ((fY l).mp hc)) hg.1 hg.2
  · simp only [smallB, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq] at hs
    rcases hs with h0 | ⟨l, hl, m, hm, hlm, e⟩
    · refine done2 l0 l0 hl0 hl0 (le_refl _) hm0 hm0 (fun k hkY => ?_)
      have hq := (fY k).mpr hkY
      rw [h0, Nat.zero_testBit] at hq
      exact Bool.noConfusion hq
    · have bl : b.testBit l = true := by
        rw [e]
        simp [Nat.testBit_two_pow]
      have bm : b.testBit m = true := by
        rw [e]
        simp [Nat.testBit_two_pow]
      refine done2 l m hl hm hlm (F5 ⟨l, hl⟩ ((fY ⟨l, hl⟩).mp bl))
        (F5 ⟨m, hm⟩ ((fY ⟨m, hm⟩).mp bm)) (fun k hkY => ?_)
      rw [← e]
      exact (fY k).mpr hkY

theorem core (X Y : Finset (Fin 13))
    (h1 : ∀ p ∈ X, ∀ l ∈ Y, ¬Inc p l)
    (h2 : ∀ l u v w : Fin 13, u ∈ X → v ∈ X → w ∈ X → u ≠ v → u ≠ w → v ≠ w →
      Inc u l → Inc v l → Inc w l → False)
    (h3 : ∀ p u v w : Fin 13, u ∈ Y → v ∈ Y → w ∈ Y → u ≠ v → u ≠ w → v ≠ w →
      Inc p u → Inc p v → Inc p w → False) :
    ∃ Z : Finset (Fin 13), X ⊆ Z ∧ (∀ l ∈ Y, ∀ p ∈ Z, ¬Inc p l) ∧
      (∀ p ∉ Z, ∃ l : Fin 13, (∀ q ∈ Z, ¬Inc q l) ∧ Inc p l) ∧
      (¬∃ l : Fin 13, ∀ p ∈ Z, Inc p l) ∧
      ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ Z, ¬Inc q l) → Inc p l := by
  refine core2 X Y (msk (fun p => decide (p ∈ X))) (msk (fun l => decide (l ∈ Y)))
    (msk_lt _) (msk_lt _) ?_ ?_ ?_ ?_ h1
  · intro p
    rw [msk_bit _ p.val p.isLt]
    simp
  · intro l
    rw [msk_bit _ l.val l.isLt]
    simp
  · exact arc_of _ (fun l u v w hu hv hw =>
      h2 l u v w (of_decide_eq_true hu) (of_decide_eq_true hv) (of_decide_eq_true hw))
  · exact darc_of _ (fun p u v w hu hv hw =>
      h3 p u v w (of_decide_eq_true hu) (of_decide_eq_true hv) (of_decide_eq_true hw))

theorem card3 (s : Finset (Fin 13)) (P : Fin 13 → Prop) (inst : DecidablePred P)
    (h : (@Finset.filter _ P inst s).card ≤ 2) (u v w : Fin 13)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s)
    (pu : P u) (pv : P v) (pw : P w) : False := by
  have hsub : ({u, v, w} : Finset (Fin 13)) ⊆ @Finset.filter _ P inst s := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rw [Finset.mem_filter]
    rcases hq with rfl | rfl | rfl
    · exact ⟨hu, pu⟩
    · exact ⟨hv, pv⟩
    · exact ⟨hw, pw⟩
  have hc : ({u, v, w} : Finset (Fin 13)).card = 3 :=
    Finset.card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩
  have hle := Finset.card_le_card hsub
  omega

end PEqualNP.Outside.L_meta_2395

theorem PEqualNP.Outside.L_meta_2395 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, ¬x1 x4 x6) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x2 | x1 x6 x5}.card ≤ (2 : ℕ)) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x1 x6 x7}.card ≤ (2 : ℕ)) → ∃ (x7 : Finset (Fin (13 : ℕ))), x2 ⊆ x7 ∧ (∀ x8 ∈ x3, ∀ x10 ∈ x7, ¬x1 x10 x8) ∧ (∀ x8 ∉ x7, ∃ (x10 : Fin (13 : ℕ)), (∀ x11 ∈ x7, ¬x1 x11 x10) ∧ x1 x8 x10) ∧ (¬∃ (x8 : Fin (13 : ℕ)), ∀ x9 ∈ x7, x1 x9 x8) ∧ ¬∃ (x8 : Fin (13 : ℕ)), ∀ (x9 : Fin (13 : ℕ)), (∀ x10 ∈ x7, ¬x1 x10 x9) → x1 x8 x9 := by
  intro x1 x2 x3 h1 h2 h3
  exact PEqualNP.Outside.L_meta_2395.core x2 x3 h1
    (fun l u v w hu hv hw huv huw hvw pu pv pw =>
      PEqualNP.Outside.L_meta_2395.card3 x2 _ _ (h2 l) u v w huv huw hvw hu hv hw pu pv pw)
    (fun p u v w hu hv hw huv huw hvw pu pv pw =>
      PEqualNP.Outside.L_meta_2395.card3 x3 _ _ (h3 p) u v w huv huw hvw hu hv hw pu pv pw)
