import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6182

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- A wire is the 16 bit number of its values: bit 4u+v is its value with left u and right v on.
-- A live set holds the wire values still needed. `Reach T k S`: from the live set S exactly k
-- gates, each with two distinct live operands and a new value, lead to {T}.
def Reach (T : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => S = {T}
  | k + 1, S => ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∃ c, (c = a &&& b ∨ c = a ||| b) ∧ c ∉ S ∧
      ∃ R, (∀ x ∈ S, x ≠ a → x ≠ b → x ∈ R) ∧ R ⊆ S ∧ Reach T k (insert c R)

theorem reach_card (T : ℕ) : ∀ (k : ℕ) (S : Finset ℕ), Reach T k S → S.card ≤ k + 1 := by
  intro k
  induction k with
  | zero => intro S h; have h : S = {T} := h; simp [h]
  | succ k ih =>
    rintro S ⟨a, ha, b, hb, hab, c, hc, hcS, R, hR, hRS, h⟩
    have h1 := ih _ h
    rw [Finset.card_insert_of_notMem fun hm => hcS (hRS hm)] at h1
    have h2 : S ⊆ insert a (insert b R) := by
      intro x hx
      by_cases xa : x = a
      · simp [xa]
      · by_cases xb : x = b
        · simp [xb]
        · simp [hR x hx xa xb]
    have h3 := (Finset.card_le_card h2).trans (Finset.card_insert_le _ _)
    have h4 := Finset.card_insert_le b R
    omega

theorem reach_sep (T p q : ℕ) (hp : T.testBit p = true) (hq : T.testBit q = false) :
    ∀ (k : ℕ) (S : Finset ℕ), Reach T k S → ∃ w ∈ S, w.testBit p = true ∧ w.testBit q = false := by
  intro k
  induction k with
  | zero => intro S h; have h : S = {T} := h; exact ⟨T, by simp [h], hp, hq⟩
  | succ k ih =>
    rintro S ⟨a, ha, b, hb, hab, c, hc, hcS, R, hR, hRS, h⟩
    obtain ⟨w, hw, h1, h2⟩ := ih _ h
    rcases Finset.mem_insert.1 hw with rfl | hw
    · rcases hc with rfl | rfl
      · rw [Nat.testBit_and] at h1 h2
        rw [Bool.and_eq_true] at h1
        rw [Bool.and_eq_false_iff] at h2
        rcases h2 with h2 | h2
        · exact ⟨a, ha, h1.1, h2⟩
        · exact ⟨b, hb, h1.2, h2⟩
      · rw [Nat.testBit_or] at h1 h2
        rw [Bool.or_eq_true] at h1
        rw [Bool.or_eq_false_iff] at h2
        rcases h1 with h1 | h1
        · exact ⟨a, ha, h1, h2.1⟩
        · exact ⟨b, hb, h1, h2.2⟩
    · exact ⟨w, hRS hw, h1, h2⟩

-- `m` is a power of two, the mask of one row.
def meet (m : ℕ) (l : List ℕ) : ℕ :=
  l.foldl (fun x w => cond (Nat.beq (Nat.land w m) 0) x (Nat.land x w)) 65535

theorem mask_zero (w p : ℕ) : Nat.beq (Nat.land w (2 ^ p)) 0 = !(w.testBit p) := by
  have h : Nat.land w (2 ^ p) = (w.testBit p).toNat * 2 ^ p := Nat.and_two_pow w p
  rw [h]
  cases w.testBit p
  · rw [Bool.toNat_false, Nat.zero_mul]; rfl
  · rw [Bool.toNat_true, Nat.one_mul, Bool.not_true, ← Bool.not_eq_true, Nat.beq_eq]
    exact Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos p)

theorem meet_aux (p q : ℕ) (l : List ℕ) : ∀ x0 : ℕ,
    (l.foldl (fun x w => cond (Nat.beq (Nat.land w (2 ^ p)) 0) x (Nat.land x w)) x0).testBit q = true ↔
      x0.testBit q = true ∧ ∀ w ∈ l, w.testBit p = true → w.testBit q = true := by
  induction l with
  | nil => intro x0; simp
  | cons w l ih =>
    intro x0
    rw [List.foldl_cons, ih, mask_zero]
    cases hw : w.testBit p
    · simp [hw]
    · have e : Nat.land x0 w = x0 &&& w := rfl
      simp [hw, e, Nat.testBit_and, and_assoc]

def masks : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768]

def sepB (T : ℕ) (l : List ℕ) : Bool :=
  masks.all fun m => Nat.beq (Nat.land T m) 0 || Nat.beq (Nat.lor (meet m l) T) T

def memB (x : ℕ) (l : List ℕ) : Bool := l.any fun y => Nat.beq y x

theorem memB_iff (x : ℕ) (l : List ℕ) : memB x l = true ↔ x ∈ l := by
  unfold memB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [← Nat.eq_of_beq_eq_true h]; exact hy
  · intro h; exact ⟨x, h, Nat.beq_refl x⟩

theorem reach_sepB (T k : ℕ) (l : List ℕ) (h : Reach T k l.toFinset) : sepB T l = true := by
  unfold sepB
  rw [List.all_eq_true]
  intro m hm
  obtain ⟨p, rfl⟩ : ∃ p, m = 2 ^ p := by
    simp only [masks, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩
    · exact ⟨6, h⟩
    · exact ⟨7, h⟩
    · exact ⟨8, h⟩
    · exact ⟨9, h⟩
    · exact ⟨10, h⟩
    · exact ⟨11, h⟩
    · exact ⟨12, h⟩
    · exact ⟨13, h⟩
    · exact ⟨14, h⟩
    · exact ⟨15, h⟩
  rw [mask_zero]
  cases hp : T.testBit p
  · rfl
  · rw [Bool.not_true, Bool.false_or, Nat.beq_eq]
    apply Nat.eq_of_testBit_eq
    intro q
    show (meet (2 ^ p) l ||| T).testBit q = T.testBit q
    rw [Nat.testBit_or]
    cases hq : T.testBit q
    · rw [Bool.or_false, ← Bool.not_eq_true]
      intro hm
      obtain ⟨w, hw, h1, h2⟩ := reach_sep T p q hp hq k _ h
      have := ((meet_aux p q l 65535).1 hm).2 w (List.mem_toFinset.1 hw) h1
      rw [this] at h2
      exact absurd h2 (by decide)
    · rw [Bool.or_true]

def del (a b : ℕ) (l : List ℕ) : List ℕ := l.filter fun x => !(Nat.beq x a || Nat.beq x b)

theorem mem_del (a b x : ℕ) (l : List ℕ) : x ∈ del a b l ↔ x ∈ l ∧ x ≠ a ∧ x ≠ b := by
  unfold del
  rw [List.mem_filter, Bool.not_eq_true', Bool.or_eq_false_iff, ← Bool.not_eq_true, ← Bool.not_eq_true,
    Nat.beq_eq, Nat.beq_eq]

-- A table of states (a hash and a live set) already shown dead at one level.
def hash (l : List ℕ) : ℕ := l.foldl (fun h x => Nat.add h (Nat.mul x (Nat.mul x x))) 0

def sameB (a b : List ℕ) : Bool := (a.all fun x => memB x b) && (b.all fun x => memB x a)

theorem sameB_eq (a b : List ℕ) (h : sameB a b = true) : a.toFinset = b.toFinset := by
  unfold sameB at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  ext x
  rw [List.mem_toFinset, List.mem_toFinset]
  exact ⟨fun hx => (memB_iff x b).1 (h.1 x hx), fun hx => (memB_iff x a).1 (h.2 x hx)⟩

def look (h : ℕ) (l : List ℕ) (D : List (ℕ × List ℕ)) : Bool :=
  D.any fun e => Nat.beq e.1 h && sameB e.2 l

def child (T k : ℕ) (D : List (ℕ × List ℕ)) (l : List ℕ) : Bool :=
  Nat.blt (k + 1) l.length || (!(sepB T l) || look (hash l) l D)

def Dead (T k : ℕ) (D : List (ℕ × List ℕ)) : Prop := ∀ e ∈ D, ¬ Reach T k e.2.toFinset

theorem child_sound (T k : ℕ) (D : List (ℕ × List ℕ)) (hD : Dead T k D) (l : List ℕ) (hn : l.Nodup)
    (h : child T k D l = true) : ¬ Reach T k l.toFinset := by
  intro hr
  unfold child at h
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with h | h | h
  · have h1 := reach_card T _ _ hr
    rw [List.toFinset_card_of_nodup hn] at h1
    rw [Nat.blt_eq] at h
    omega
  · rw [reach_sepB T k l hr] at h
    exact absurd h (by decide)
  · unfold look at h
    rw [List.any_eq_true] at h
    obtain ⟨e, he, h⟩ := h
    rw [Bool.and_eq_true] at h
    exact hD e he (by rw [sameB_eq _ _ h.2]; exact hr)

def okS (T k : ℕ) (D : List (ℕ × List ℕ)) (l : List ℕ) : Bool :=
  l.all fun a => l.all fun b => Nat.ble b a ||
    [Nat.land a b, Nat.lor a b].all fun c => memB c l ||
      (child T k D (c :: del a b l) && (child T k D (c :: a :: del a b l) &&
        (child T k D (c :: b :: del a b l) && child T k D (c :: a :: b :: del a b l))))

theorem okS_sound (T k : ℕ) (D : List (ℕ × List ℕ)) (hD : Dead T k D) (l : List ℕ) (hn : l.Nodup)
    (hall : okS T k D l = true) : ¬ Reach T (k + 1) l.toFinset := by
    intro h
    unfold okS at hall
    rw [List.all_eq_true] at hall
    obtain ⟨a0, ha0, b0, hb0, hab0, c, hc0, hcS, R, hR0, hRS, hr⟩ := h
    obtain ⟨a, b, ha, hb', hlt, hc, hR⟩ : ∃ a b, a ∈ l ∧ b ∈ l ∧ a < b ∧ (c = a &&& b ∨ c = a ||| b) ∧
        (∀ x ∈ l.toFinset, x ≠ a → x ≠ b → x ∈ R) := by
      rcases Nat.lt_or_gt_of_ne hab0 with h | h
      · exact ⟨a0, b0, List.mem_toFinset.1 ha0, List.mem_toFinset.1 hb0, h, hc0, hR0⟩
      · refine ⟨b0, a0, List.mem_toFinset.1 hb0, List.mem_toFinset.1 ha0, h, ?_,
          fun x hx h1 h2 => hR0 x hx h2 h1⟩
        rw [Nat.and_comm, Nat.or_comm]; exact hc0
    have h1 := hall a ha
    rw [List.all_eq_true] at h1
    have h2 := h1 b hb'
    have hble : Nat.ble b a = false := by
      rw [← Bool.not_eq_true, Nat.ble_eq]; omega
    rw [hble, Bool.false_or, List.all_eq_true] at h2
    have h3 := h2 c (by
      rcases hc with h | h
      · exact h ▸ List.mem_cons_self
      · exact h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
    have hcl : c ∉ l := fun hm => hcS (List.mem_toFinset.2 hm)
    have hmc : memB c l = false := by rw [← Bool.not_eq_true, memB_iff]; exact hcl
    rw [hmc, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h3
    obtain ⟨d0, da, db, dab⟩ := h3
    have hnd : (del a b l).Nodup := hn.filter _
    have hca : c ≠ a := fun e => hcl (e ▸ ha)
    have hcb : c ≠ b := fun e => hcl (e ▸ hb')
    have hab : a ≠ b := Nat.ne_of_lt hlt
    have hcd : c ∉ del a b l := fun hm => hcl ((mem_del a b c l).1 hm).1
    have had : a ∉ del a b l := fun hm => ((mem_del a b a l).1 hm).2.1 rfl
    have hbd : b ∉ del a b l := fun hm => ((mem_del a b b l).1 hm).2.2 rfl
    have key : ∀ m : List ℕ, m.Nodup → child T k D m = true → insert c R = m.toFinset → False := by
      intro m hm hdm e
      rw [e] at hr
      exact child_sound T k D hD m hm hdm hr
    have mR : ∀ x, x ∈ R → x ∈ l := fun x hx => List.mem_toFinset.1 (hRS hx)
    by_cases aR : a ∈ R <;> by_cases bR : b ∈ R
    · refine key (c :: a :: b :: del a b l) ?_ dab ?_
      · simp [hca, hcb, hab, hcd, had, hbd, hnd]
      · ext x
        simp only [Finset.mem_insert, List.mem_toFinset, List.mem_cons, mem_del]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · by_cases xa : x = a
            · exact Or.inr (Or.inl xa)
            · by_cases xb : x = b
              · exact Or.inr (Or.inr (Or.inl xb))
              · exact Or.inr (Or.inr (Or.inr ⟨mR x h, xa, xb⟩))
        · rintro (h | h | h | h)
          · exact Or.inl h
          · exact Or.inr (h ▸ aR)
          · exact Or.inr (h ▸ bR)
          · exact Or.inr (hR x (List.mem_toFinset.2 h.1) h.2.1 h.2.2)
    · refine key (c :: a :: del a b l) ?_ da ?_
      · simp [hca, hcd, had, hnd]
      · ext x
        simp only [Finset.mem_insert, List.mem_toFinset, List.mem_cons, mem_del]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · by_cases xa : x = a
            · exact Or.inr (Or.inl xa)
            · exact Or.inr (Or.inr ⟨mR x h, xa, fun e => bR (e ▸ h)⟩)
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inr (h ▸ aR)
          · exact Or.inr (hR x (List.mem_toFinset.2 h.1) h.2.1 h.2.2)
    · refine key (c :: b :: del a b l) ?_ db ?_
      · simp [hcb, hcd, hbd, hnd]
      · ext x
        simp only [Finset.mem_insert, List.mem_toFinset, List.mem_cons, mem_del]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · by_cases xb : x = b
            · exact Or.inr (Or.inl xb)
            · exact Or.inr (Or.inr ⟨mR x h, fun e => aR (e ▸ h), xb⟩)
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inr (h ▸ bR)
          · exact Or.inr (hR x (List.mem_toFinset.2 h.1) h.2.1 h.2.2)
    · refine key (c :: del a b l) ?_ d0 ?_
      · simp [hcd, hnd]
      · ext x
        simp only [Finset.mem_insert, List.mem_toFinset, List.mem_cons, mem_del]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨mR x h, fun e => aR (e ▸ h), fun e => bR (e ▸ h)⟩
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (hR x (List.mem_toFinset.2 h.1) h.2.1 h.2.2)

def nodupB : List ℕ → Bool
  | [] => true
  | a :: t => !(memB a t) && nodupB t

theorem nodupB_sound : ∀ l : List ℕ, nodupB l = true → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a t ih =>
    intro h
    rw [nodupB, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, memB_iff] at h
    exact List.nodup_cons.2 ⟨h.1, ih h.2⟩

def okL (T k : ℕ) (D E : List (ℕ × List ℕ)) : Bool := E.all fun e => nodupB e.2 && okS T k D e.2

theorem okL_sound (T k : ℕ) (D E : List (ℕ × List ℕ)) (hD : Dead T k D) (h : okL T k D E = true) :
    Dead T (k + 1) E := by
  intro e he
  unfold okL at h
  rw [List.all_eq_true] at h
  have := h e he
  rw [Bool.and_eq_true] at this
  exact okS_sound T k D hD e.2 (nodupB_sound _ this.1) this.2

theorem dead_append (T k : ℕ) (D E : List (ℕ × List ℕ)) (h1 : Dead T k D) (h2 : Dead T k E) :
    Dead T k (D ++ E) := by
  intro e he
  rcases List.mem_append.1 he with h | h
  · exact h1 e h
  · exact h2 e h

theorem dead_nil (T k : ℕ) : Dead T k [] := by intro e he; simp at he

-- Circuits. The pool holds the values of the wires so far.
def gv (pool : List ℕ) (g : Gate) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun i => pool.getD i 0).foldr (fun a b => a &&& b) 65535
  | _ => (g.inputs.map fun i => pool.getD i 0).foldr (fun a b => a ||| b) 0

def exec (gs : List Gate) (pool : List ℕ) : List ℕ := gs.foldl (fun p g => p ++ [gv p g]) pool

def ok (g : Gate) : Prop := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Av (pool : List ℕ) (x : ℕ) : Prop := x ∈ pool ∨ x = 0 ∨ x = 65535

def Small (pool : List ℕ) : Prop := ∀ x ∈ pool, x < 2 ^ 16

theorem getD_av (pool : List ℕ) (i : ℕ) : Av pool (pool.getD i 0) := by
  by_cases h : i < pool.length
  · rw [List.getD_eq_getElem _ _ h]; exact Or.inl (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inr (Or.inl rfl)

theorem av_small (pool : List ℕ) (hp : Small pool) (x : ℕ) (h : Av pool x) : x < 2 ^ 16 := by
  rcases h with h | h | h
  · exact hp x h
  · rw [h]; decide
  · rw [h]; decide

theorem and_full (x : ℕ) (h : x < 2 ^ 16) : x &&& 65535 = x := by
  have := Nat.and_two_pow_sub_one_eq_mod x 16
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, this, Nat.mod_eq_of_lt h]

theorem gv_cases (pool : List ℕ) (hp : Small pool) (g : Gate) (hg : ok g) :
    Av pool (gv pool g) ∨ ∃ a b, Av pool a ∧ Av pool b ∧ (gv pool g = a &&& b ∨ gv pool g = a ||| b) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  have hl : ins.length ≤ 2 := hl
  have hop : op = GateOp.and ∨ op = GateOp.or := hop
  match ins, hl with
  | [], _ =>
    left
    rcases hop with rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  | [i], _ =>
    left
    rcases hop with rfl | rfl
    · show Av pool (pool.getD i 0 &&& 65535)
      rw [and_full _ (av_small pool hp _ (getD_av pool i))]; exact getD_av pool i
    · show Av pool (pool.getD i 0 ||| 0)
      rw [Nat.or_zero]; exact getD_av pool i
  | [i, j], _ =>
    right
    refine ⟨pool.getD i 0, pool.getD j 0, getD_av pool i, getD_av pool j, ?_⟩
    rcases hop with rfl | rfl
    · left
      show pool.getD i 0 &&& (pool.getD j 0 &&& 65535) = _
      rw [and_full _ (av_small pool hp _ (getD_av pool j))]
    · right
      show pool.getD i 0 ||| (pool.getD j 0 ||| 0) = _
      rw [Nat.or_zero]

theorem gv_small (pool : List ℕ) (hp : Small pool) (g : Gate) (hg : ok g) : gv pool g < 2 ^ 16 := by
  rcases gv_cases pool hp g hg with h | ⟨a, b, ha, hb, h | h⟩
  · exact av_small pool hp _ h
  · rw [h]; exact Nat.and_lt_two_pow _ (av_small pool hp b hb)
  · rw [h]; exact Nat.or_lt_two_pow (av_small pool hp a ha) (av_small pool hp b hb)

theorem small_snoc (pool : List ℕ) (hp : Small pool) (g : Gate) (hg : ok g) :
    Small (pool ++ [gv pool g]) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact hp x h
  · rw [List.mem_singleton.1 h]; exact gv_small pool hp g hg

theorem av_snoc (pool : List ℕ) (v x : ℕ) (h : Av (pool ++ [v]) x) : x = v ∨ Av pool x := by
  rcases h with h | h | h
  · rcases List.mem_append.1 h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl (List.mem_singleton.1 h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem pull (T : ℕ) (pool : List ℕ) (hp : Small pool) (g : Gate) (hg : ok g) (j : ℕ) (S : Finset ℕ)
    (hr : Reach T j S) (hS : ∀ x ∈ S, Av (pool ++ [gv pool g]) x) :
    ∃ i ≤ j + 1, ∃ S', Reach T i S' ∧ ∀ x ∈ S', Av pool x := by
  by_cases hv : Av pool (gv pool g)
  · refine ⟨j, by omega, S, hr, fun x hx => ?_⟩
    rcases av_snoc _ _ _ (hS x hx) with rfl | h
    · exact hv
    · exact h
  · by_cases hm : gv pool g ∈ S
    · rcases gv_cases pool hp g hg with h | ⟨a, b, ha, hb, hc⟩
      · exact absurd h hv
      · have hva : gv pool g ≠ a := fun e => hv (e ▸ ha)
        have hvb : gv pool g ≠ b := fun e => hv (e ▸ hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hc with h | h
          · exact hva (h.trans (Nat.and_self a))
          · exact hva (h.trans (Nat.or_self a))
        refine ⟨j + 1, le_rfl, insert a (insert b (S.erase (gv pool g))), ?_, ?_⟩
        · refine ⟨a, by simp, b, by simp, hab, gv pool g, hc, by simp [hva, hvb], S.erase (gv pool g), ?_, ?_, ?_⟩
          · intro x hx xa xb
            simp only [Finset.mem_insert] at hx
            rcases hx with h | h | h
            · exact absurd h xa
            · exact absurd h xb
            · exact h
          · intro x hx; simp only [Finset.mem_insert]; exact Or.inr (Or.inr hx)
          · rw [Finset.insert_erase hm]; exact hr
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_erase] at hx
          rcases hx with rfl | rfl | ⟨hne, hx⟩
          · exact ha
          · exact hb
          · rcases av_snoc _ _ _ (hS x hx) with h | h
            · exact absurd h hne
            · exact h
    · refine ⟨j, by omega, S, hr, fun x hx => ?_⟩
      rcases av_snoc _ _ _ (hS x hx) with rfl | h
      · exact absurd hx hm
      · exact h

theorem extract (T : ℕ) (gs : List Gate) : ∀ pool : List ℕ, Small pool → (∀ g ∈ gs, ok g) →
    ∀ (j : ℕ) (S : Finset ℕ), Reach T j S → (∀ x ∈ S, Av (exec gs pool) x) →
    ∃ i ≤ j + gs.length, ∃ S', Reach T i S' ∧ ∀ x ∈ S', Av pool x := by
  induction gs with
  | nil => intro pool _ _ j S hr hS; exact ⟨j, by simp, S, hr, hS⟩
  | cons g gs ih =>
    intro pool hp hg j S hr hS
    have hg0 := hg g (by simp)
    obtain ⟨i, hi, S1, h1, h2⟩ := ih (pool ++ [gv pool g]) (small_snoc pool hp g hg0)
      (fun x hx => hg x (by simp [hx])) j S hr hS
    obtain ⟨i', hi', S2, h3, h4⟩ := pull T pool hp g hg0 i S1 h1 h2
    exact ⟨i', by simp only [List.length_cons]; omega, S2, h3, h4⟩

def Inv (p : ℕ) (pool : List ℕ) (w : List Bool) : Prop :=
  pool.length = w.length ∧ ∀ i, (pool.getD i 0).testBit p = w.getD i false

theorem fold_and (p : ℕ) (hp : p < 16) (f : ℕ → ℕ) (h : ℕ → Bool) (hf : ∀ i, (f i).testBit p = h i) (l : List ℕ) :
    ((l.map f).foldr (fun a b => a &&& b) 65535).testBit p = (l.map h).all id := by
  induction l with
  | nil =>
    show (65535 : ℕ).testBit p = true
    interval_cases p <;> decide
  | cons i l ih =>
    simp only [List.map_cons, List.foldr_cons, Nat.testBit_and, ih, hf, List.all_cons, id]

theorem fold_or (p : ℕ) (f : ℕ → ℕ) (h : ℕ → Bool) (hf : ∀ i, (f i).testBit p = h i) (l : List ℕ) :
    ((l.map f).foldr (fun a b => a ||| b) 0).testBit p = (l.map h).any id := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.foldr_cons, Nat.testBit_or, ih, hf, List.any_cons, id]

theorem gv_bit (p : ℕ) (hp : p < 16) (pool : List ℕ) (w : List Bool) (h : Inv p pool w) (g : Gate) (hg : ok g) :
    (gv pool g).testBit p = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  have hop : op = GateOp.and ∨ op = GateOp.or := hg.1
  rcases hop with rfl | rfl
  · exact fold_and p hp _ _ h.2 ins
  · exact fold_or p _ _ h.2 ins

theorem inv_snoc (p : ℕ) (pool : List ℕ) (w : List Bool) (h : Inv p pool w) (a : ℕ) (b : Bool)
    (hab : a.testBit p = b) : Inv p (pool ++ [a]) (w ++ [b]) := by
  refine ⟨by simp [h.1], fun i => ?_⟩
  rcases Nat.lt_trichotomy i pool.length with hi | hi | hi
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (h.1 ▸ hi)]; exact h.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by have := h.1; omega)]
    rw [hi, ← h.1, Nat.sub_self]; exact hab
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by have := h.1; simp; omega)]
    exact Nat.zero_testBit p

theorem inv_exec (p : ℕ) (hp : p < 16) (gs : List Gate) : ∀ (pool : List ℕ) (w : List Bool),
    (∀ g ∈ gs, ok g) → Inv p pool w →
    Inv p (exec gs pool) (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) := by
  induction gs with
  | nil => intro pool w _ h; exact h
  | cons g gs ih =>
    intro pool w hg h
    exact ih _ _ (fun x hx => hg x (by simp [hx]))
      (inv_snoc p pool w h _ _ (gv_bit p hp pool w h g (hg g (by simp))))

theorem small_exec (gs : List Gate) : ∀ pool : List ℕ, Small pool → (∀ g ∈ gs, ok g) → Small (exec gs pool) := by
  induction gs with
  | nil => intro pool h _; exact h
  | cons g gs ih =>
    intro pool h hg
    exact ih _ (small_snoc pool h g (hg g (by simp))) (fun x hx => hg x (by simp [hx]))

def pool0 : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]

theorem small0 : Small pool0 := by unfold Small pool0; decide

theorem inv0 : ∀ u v : Fin 4, Inv (4 * u.val + v.val) pool0 (oneEach u v) := by
  intro u v
  refine ⟨by simp [pool0, oneEach], fun i => ?_⟩
  by_cases hi : i < 8
  · interval_cases i <;> revert u v <;> decide
  · rw [List.getD_eq_default _ _ (by simp [pool0]; omega), List.getD_eq_default _ _ (by simp [oneEach]; omega)]
    exact Nat.zero_testBit _

def leaves : List ℕ := pool0 ++ [0, 65535]

def subs : List ℕ → List (List ℕ)
  | [] => [[]]
  | a :: t => subs t ++ (subs t).map (fun s => a :: s)

theorem filter_subs (f : ℕ → Bool) (l : List ℕ) : l.filter f ∈ subs l := by
  induction l with
  | nil => simp [subs]
  | cons a t ih =>
    rw [subs, List.mem_append]
    cases h : f a
    · rw [List.filter_cons_of_neg (by simp [h])]; exact Or.inl ih
    · rw [List.filter_cons_of_pos h]; exact Or.inr (List.mem_map.2 ⟨_, ih, rfl⟩)

def start (T k : ℕ) (D : List (ℕ × List ℕ)) : Bool := (subs leaves).all fun l => child T k D l

theorem lower (T K : ℕ) (hT : T < 2 ^ 16) (hd : ∀ k ≤ K, ∃ D, Dead T k D ∧ start T k D = true) :
    ¬ RepSizeAtMost (fun u v : Fin 4 => T.testBit (4 * u.val + v.val)) K := by
  rintro ⟨C, hC, hs, hr⟩
  have hg : ∀ g ∈ C.gates, ok g := hC
  have hsm := small_exec C.gates pool0 small0 hg
  have out : (exec C.gates pool0).getD C.output 0 = T := by
    apply Nat.eq_of_testBit_eq
    intro q
    by_cases hq : q < 16
    · obtain ⟨u, v, rfl⟩ : ∃ u v : Fin 4, 4 * u.val + v.val = q :=
        ⟨⟨q / 4, by omega⟩, ⟨q % 4, by omega⟩, by simp only; omega⟩
      rw [(inv_exec _ hq C.gates pool0 (oneEach u v) hg (inv0 u v)).2 C.output]
      exact hr u v
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (av_small _ hsm _ (getD_av _ _)) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hT (Nat.pow_le_pow_right (by decide) (by omega)))]
  obtain ⟨i, hi, S, h1, h2⟩ := extract T C.gates pool0 small0 hg 0 {T} rfl (by
    intro x hx
    rw [Finset.mem_singleton.1 hx, ← out]
    exact getD_av _ _)
  have hsz : C.gates.length ≤ K := hs
  obtain ⟨D, hD, hk⟩ := hd i (by omega)
  unfold start at hk
  rw [List.all_eq_true] at hk
  have hmem := filter_subs (fun x => decide (x ∈ S)) leaves
  have hnd : leaves.Nodup := by decide
  refine child_sound T i D hD _ (hnd.filter _) (hk _ hmem) ?_
  have : (leaves.filter fun x => decide (x ∈ S)).toFinset = S := by
    ext x
    rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      unfold leaves
      rcases h2 x h with h | h | h
      · exact List.mem_append.2 (Or.inl h)
      · simp [h]
      · simp [h]
  rw [this]
  exact h1

def D0 : List (ℕ × List ℕ) := []

theorem t0 : Dead 893 0 D0 := dead_nil _ _

def D1_0 : List (ℕ × List ℕ) :=
  []

theorem o1_0 : okL 893 0 D0 D1_0 = true := by decide +kernel

def D1 : List (ℕ × List ℕ) := D1_0

theorem t1 : Dead 893 1 D1 :=
  okL_sound _ _ _ _ t0 o1_0

def D2_0 : List (ℕ × List ℕ) :=
  [(23332138933140, [240, 4893, 28527]),
    (10624564119060, [240, 13119, 20301]),
    (10613443139496, [249, 13119, 20292]),
    (23298821718336, [764, 4369, 28527]),
    (11095722286972, [1016, 8751, 21845]),
    (151711027669568, [4369, 8815, 53244]),
    (9207528527856, [4369, 8959, 20332]),
    (9160330845096, [4409, 8959, 20292]),
    (151699935390272, [4433, 8751, 53244]),
    (50821393380220, [4437, 8751, 36856]),
    (57100532965244, [8751, 21845, 35832])]

theorem o2_0 : okL 893 1 D1 D2_0 = true := by decide +kernel

def D2 : List (ℕ × List ℕ) := D2_0

theorem t2 : Dead 893 2 D2 :=
  okL_sound _ _ _ _ t1 o2_0

def D3_0 : List (ℕ × List ℕ) :=
  [(10613441525976, [9, 240, 13119, 20292]),
    (10607251299328, [13, 240, 13107, 20292]),
    (10618373894319, [15, 240, 13107, 20301]),
    (10607252914755, [15, 249, 13107, 20292]),
    (66580087092760, [15, 816, 17476, 39417]),
    (53535695610140, [15, 816, 21845, 35064]),
    (151708001675176, [15, 4369, 8802, 53244]),
    (151696953208168, [15, 4433, 8738, 53244]),
    (50818411198116, [15, 4437, 8738, 36856]),
    (57097550783140, [15, 8738, 21845, 35832]),
    (58682078115911, [15, 13107, 21845, 35832]),
    (9158019294576, [40, 4369, 8959, 20292]),
    (151696216777088, [64, 4369, 8751, 53244]),
    (50817438788608, [68, 4369, 8751, 36856]),
    (151693234822504, [79, 4369, 8738, 53244]),
    (23298533476416, [240, 524, 4369, 28527]),
    (11095154627452, [240, 776, 8751, 21845]),
    (7660129451284, [240, 3840, 13119, 17485]),
    (7652278183384, [240, 3849, 13119, 17476]),
    (6833950807168, [240, 4369, 8751, 18252]),
    (9118988588160, [240, 4369, 8751, 20300]),
    (9120224919061, [240, 4369, 8751, 20301]),
    (9158611622528, [240, 4369, 8751, 20332]),
    (150204333118592, [240, 4369, 8751, 53068]),
    (151303180416320, [240, 4369, 8815, 53196]),
    (9109561280472, [240, 4377, 8751, 20292]),
    (9119447543384, [240, 4377, 8751, 20300]),
    (9109791388180, [240, 4381, 8751, 20292]),
    (9118047008060, [240, 4383, 8738, 20301]),
    (9111413939768, [240, 4409, 8751, 20292]),
    (151292088137024, [240, 4433, 8751, 53196]),
    (50366382212988, [240, 4437, 8751, 36744]),
    (9142564597208, [240, 4889, 8751, 20292]),
    (9142851659796, [240, 4893, 8751, 20292]),
    (60276557973464, [240, 8751, 20292, 37145]),
    (56670492586876, [240, 8751, 21845, 35720]),
    (60764103792252, [240, 9007, 21845, 36744]),
    (57965274186876, [240, 9007, 24405, 34952]),
    (57208172207960, [240, 13119, 17476, 36745]),
    (57205038017276, [240, 13119, 17477, 36744]),
    (53315948366424, [240, 13119, 20292, 34953]),
    (53313518691324, [240, 13119, 20293, 34952]),
    (57204121906640, [241, 13119, 17476, 36744]),
    (53312283508176, [241, 13119, 20292, 34952]),
    (9109103754240, [248, 4369, 8751, 20292]),
    (9118990017152, [248, 4369, 8751, 20300]),
    (9109562709464, [248, 4377, 8751, 20292]),
    (7651880732584, [249, 3840, 13119, 17476]),
    (9109103939497, [249, 4369, 8751, 20292]),
    (9106926028496, [249, 4383, 8738, 20292]),
    (9109104504256, [252, 4369, 8751, 20292]),
    (60703661257596, [496, 8751, 21845, 36744]),
    (57904831652220, [496, 8751, 24405, 34952]),
    (9109527477248, [760, 4369, 8751, 20292]),
    (9109534444992, [764, 4369, 8751, 20292]),
    (54205756841852, [768, 8751, 21845, 35064]),
    (53794539516796, [1008, 8751, 21845, 34952]),
    (6091951762432, [1016, 4369, 8751, 17476]),
    (145329747728960, [3840, 4369, 8815, 52476]),
    (6233190041584, [3840, 4369, 8959, 17516]),
    (6198768438184, [3840, 4409, 8959, 17476]),
    (145318655449664, [3840, 4433, 8751, 52476]),
    (43924756116348, [3840, 4437, 8751, 35064]),
    (55213081386876, [3840, 8751, 21845, 35320]),
    (54322477695612, [3840, 9007, 21845, 35064]),
    (50766184193960, [3840, 13119, 17476, 35065]),
    (50763411920636, [3840, 13119, 17477, 35064]),
    (50762539884800, [3841, 13119, 17476, 35064]),
    (6198244791664, [3880, 4369, 8959, 17476]),
    (144944867337536, [4080, 4369, 8815, 52428]),
    (144933775058240, [4080, 4433, 8751, 52428]),
    (43524261791612, [4080, 4437, 8751, 34952]),
    (72404779351589, [4080, 8751, 21845, 39417]),
    (52096762440704, [4369, 8751, 17476, 35832]),
    (49936575577088, [4369, 8751, 18244, 35064]),
    (45098385849344, [4369, 8751, 20292, 33016]),
    (56169604854976, [4369, 8815, 17476, 36856]),
    (55877466109376, [4369, 8815, 17652, 36744]),
    (52234529998016, [4369, 8815, 20292, 35064]),
    (52042044671424, [4369, 8815, 20468, 34952]),
    (56158512575680, [4433, 8751, 17476, 36856]),
    (55866373830080, [4433, 8751, 17652, 36744]),
    (52223437718720, [4433, 8751, 20292, 35064]),
    (52030952392128, [4433, 8751, 20468, 34952]),
    (51841206772128, [4593, 8751, 20308, 34952]),
    (61255456540749, [4593, 8751, 21845, 36856]),
    (51825109016016, [4593, 8767, 20292, 34952]),
    (122400752749605, [8751, 21845, 36856, 39417])]

theorem o3_0 : okL 893 2 D2 D3_0 = true := by decide +kernel

def D3 : List (ℕ × List ℕ) := D3_0

theorem t3 : Dead 893 3 D3 :=
  okL_sound _ _ _ _ t2 o3_0

def D4_0 : List (ℕ × List ℕ) :=
  [(9118988588160, [0, 240, 4369, 8751, 20300]),
    (9109561280472, [0, 240, 4377, 8751, 20292]),
    (9109103754240, [0, 248, 4369, 8751, 20292]),
    (57204121733120, [1, 240, 13119, 17476, 36744]),
    (53312283334656, [1, 240, 13119, 20292, 34952]),
    (50762495636480, [1, 3840, 13119, 17476, 35064]),
    (9109102325760, [8, 240, 4369, 8751, 20292]),
    (9118988588672, [8, 240, 4369, 8751, 20300]),
    (9109561280984, [8, 240, 4377, 8751, 20292]),
    (9109103754752, [8, 248, 4369, 8751, 20292]),
    (10607251301235, [9, 15, 240, 13107, 20292]),
    (7651879119064, [9, 240, 3840, 13119, 17476]),
    (9109102325977, [9, 240, 4369, 8751, 20292]),
    (9106924414976, [9, 240, 4383, 8738, 20292]),
    (9109102326976, [12, 240, 4369, 8751, 20292]),
    (7645688892416, [13, 240, 3840, 13107, 17476]),
    (12732855592365, [13, 240, 3840, 13107, 21845]),
    (9106120141966, [13, 240, 4369, 8738, 20292]),
    (151693234594984, [15, 64, 4369, 8738, 53244]),
    (50814456606504, [15, 68, 4369, 8738, 36856]),
    (66133724265208, [15, 240, 816, 17476, 39321]),
    (53123920901404, [15, 240, 816, 21845, 34952]),
    (7653939226543, [15, 240, 3840, 13107, 17485]),
    (12744312684895, [15, 240, 3840, 13107, 21853]),
    (12748438244727, [15, 240, 3840, 13115, 21853]),
    (12733210225735, [15, 240, 3848, 13107, 21845]),
    (7646087958643, [15, 240, 3849, 13107, 17476]),
    (9116006406056, [15, 240, 4369, 8738, 20300]),
    (9117242736957, [15, 240, 4369, 8738, 20301]),
    (150201350936488, [15, 240, 4369, 8738, 53068]),
    (9117840547720, [15, 240, 4369, 8746, 20300]),
    (9118988591535, [15, 240, 4369, 8751, 20300]),
    (151300154421928, [15, 240, 4369, 8802, 53196]),
    (10700533738827, [15, 240, 4369, 13107, 20300]),
    (9106579098368, [15, 240, 4377, 8738, 20292]),
    (9116465361280, [15, 240, 4377, 8738, 20300]),
    (9108413240032, [15, 240, 4377, 8746, 20292]),
    (9109561283847, [15, 240, 4377, 8751, 20292]),
    (10691106431139, [15, 240, 4377, 13107, 20292]),
    (10695231990971, [15, 240, 4377, 13115, 20292]),
    (9106809206076, [15, 240, 4381, 8738, 20292]),
    (151289105954920, [15, 240, 4433, 8738, 53196]),
    (50363400030884, [15, 240, 4437, 8738, 36744]),
    (55064822648832, [15, 240, 4913, 17476, 36744]),
    (55519847640064, [15, 240, 4913, 17476, 36856]),
    (51172984250368, [15, 240, 4913, 20292, 34952]),
    (60273575791360, [15, 240, 8738, 20292, 37145]),
    (56667510404772, [15, 240, 8738, 21845, 35720]),
    (60760944444068, [15, 240, 8994, 21845, 36744]),
    (57962114838692, [15, 240, 8994, 24405, 34952]),
    (57201981983219, [15, 240, 13107, 17476, 36745]),
    (57198847792535, [15, 240, 13107, 17477, 36744]),
    (69119919907363, [15, 240, 13107, 18244, 39321]),
    (53309758141683, [15, 240, 13107, 20292, 34953]),
    (71403063173667, [15, 240, 13107, 20292, 39321]),
    (71849439825219, [15, 240, 13107, 20292, 39417]),
    (78809614603299, [15, 240, 13107, 20292, 40857]),
    (193828648674079, [15, 240, 13107, 20292, 56797]),
    (198828431055135, [15, 240, 13107, 20292, 57309]),
    (271487623135779, [15, 240, 13107, 20292, 63897]),
    (53307328466583, [15, 240, 13107, 20293, 34952]),
    (58252037737543, [15, 240, 13107, 21845, 35720]),
    (62285098208327, [15, 240, 13107, 21845, 36744]),
    (62740123199559, [15, 240, 13107, 21845, 36856]),
    (163211040163079, [15, 240, 13107, 21845, 53196]),
    (66396292512327, [15, 240, 13107, 24405, 36744]),
    (167322234467079, [15, 240, 13107, 24405, 53196]),
    (299592890592327, [15, 240, 13107, 36744, 62805]),
    (71409253401783, [15, 240, 13119, 20292, 39321]),
    (62291288436443, [15, 240, 13119, 21845, 36744]),
    (57197931681899, [15, 241, 13107, 17476, 36744]),
    (53306093283435, [15, 241, 13107, 20292, 34952]),
    (12732857022535, [15, 248, 3840, 13107, 21845]),
    (9106121572136, [15, 248, 4369, 8738, 20292]),
    (9116007835048, [15, 248, 4369, 8738, 20300]),
    (9107955713800, [15, 248, 4369, 8746, 20292]),
    (9109103757615, [15, 248, 4369, 8751, 20292]),
    (10690648904907, [15, 248, 4369, 13107, 20292]),
    (9106580527360, [15, 248, 4377, 8738, 20292]),
    (7645690507843, [15, 249, 3840, 13107, 17476]),
    (9106121757393, [15, 249, 4369, 8738, 20292]),
    (9106122322152, [15, 252, 4369, 8738, 20292]),
    (60700679075492, [15, 496, 8738, 21845, 36744]),
    (57901849470116, [15, 496, 8738, 24405, 34952]),
    (54202774659748, [15, 768, 8738, 21845, 35064]),
    (55787301992519, [15, 768, 13107, 21845, 35064]),
    (48531925085600, [15, 816, 4369, 17476, 35064]),
    (48133632693312, [15, 816, 4593, 17476, 34952]),
    (53791557334692, [15, 1008, 8738, 21845, 34952]),
    (68385888031267, [15, 1008, 13107, 17476, 39321]),
    (55376084667463, [15, 1008, 13107, 21845, 34952]),
    (145326721734568, [15, 3840, 4369, 8802, 52476]),
    (145315673267560, [15, 3840, 4433, 8738, 52476]),
    (43921773934244, [15, 3840, 4437, 8738, 35064]),
    (48623196552192, [15, 3840, 4913, 17476, 35064]),
    (55210099204772, [15, 3840, 8738, 21845, 35320]),
    (54319318347428, [15, 3840, 8994, 21845, 35064]),
    (50759993969219, [15, 3840, 13107, 17476, 35065]),
    (50757221695895, [15, 3840, 13107, 17477, 35064]),
    (55843472111687, [15, 3840, 13107, 21845, 35064]),
    (55849662339803, [15, 3840, 13119, 21845, 35064]),
    (50756349660059, [15, 3841, 13107, 17476, 35064]),
    (144941841343144, [15, 4080, 4369, 8802, 52428]),
    (144930792876136, [15, 4080, 4433, 8738, 52428]),
    (43521279609508, [15, 4080, 4437, 8738, 34952]),
    (48634490760192, [15, 4080, 4913, 17476, 35064]),
    (72401797169485, [15, 4080, 8738, 21845, 39417]),
    (68899157802307, [15, 4080, 13107, 17476, 39417]),
    (55854766319687, [15, 4080, 13107, 21845, 35064]),
    (52093780258600, [15, 4369, 8738, 17476, 35832]),
    (49933593394984, [15, 4369, 8738, 18244, 35064]),
    (45095403667240, [15, 4369, 8738, 20292, 33016]),
    (56166578860584, [15, 4369, 8802, 17476, 36856]),
    (55874440114984, [15, 4369, 8802, 17652, 36744]),
    (52231504003624, [15, 4369, 8802, 20292, 35064]),
    (52039018677032, [15, 4369, 8802, 20468, 34952]),
    (51893327134952, [15, 4369, 8946, 20324, 34952]),
    (53678307591371, [15, 4369, 13107, 17476, 35832]),
    (51518120727755, [15, 4369, 13107, 18244, 35064]),
    (51855581217608, [15, 4401, 8946, 20292, 34952]),
    (56155530393576, [15, 4433, 8738, 17476, 36856]),
    (55863391647976, [15, 4433, 8738, 17652, 36744]),
    (52220455536616, [15, 4433, 8738, 20292, 35064]),
    (52027970210024, [15, 4433, 8738, 20468, 34952]),
    (51838224590024, [15, 4593, 8738, 20308, 34952]),
    (61252474358645, [15, 4593, 8738, 21845, 36856]),
    (51822115910792, [15, 4593, 8754, 20292, 34952]),
    (57749834991467, [15, 4593, 13107, 17476, 36856]),
    (53814760134507, [15, 4593, 13107, 20292, 35064]),
    (98630464158208, [15, 4913, 17476, 35064, 36856]),
    (122397770567501, [15, 8738, 21845, 36856, 39417]),
    (118895131200323, [15, 13107, 17476, 36856, 39417]),
    (64142389744775, [15, 13107, 20292, 21845, 35064]),
    (105395714726471, [15, 13107, 21845, 35064, 36744]),
    (105850739717703, [15, 13107, 21845, 35064, 36856]),
    (51821426455200, [16, 4593, 8751, 20292, 34952]),
    (51818444295416, [31, 4593, 8738, 20292, 34952]),
    (9109102389248, [40, 240, 4369, 8751, 20292]),
    (6196456887664, [40, 3840, 4369, 8959, 17476]),
    (151288369523840, [64, 240, 4369, 8751, 53196]),
    (145314936836480, [64, 3840, 4369, 8751, 52476]),
    (144930056445056, [64, 4080, 4369, 8751, 52428]),
    (56154793962496, [64, 4369, 8751, 17476, 36856]),
    (55862655216896, [64, 4369, 8751, 17652, 36744]),
    (52219719105536, [64, 4369, 8751, 20292, 35064]),
    (52027233778944, [64, 4369, 8751, 20468, 34952]),
    (50362427621376, [68, 240, 4369, 8751, 36744]),
    (43920801524736, [68, 3840, 4369, 8751, 35064]),
    (43520307200000, [68, 4080, 4369, 8751, 34952]),
    (151285387569256, [79, 240, 4369, 8738, 53196]),
    (145311954881896, [79, 3840, 4369, 8738, 52476]),
    (144927074490472, [79, 4080, 4369, 8738, 52428]),
    (56151812007912, [79, 4369, 8738, 17476, 36856]),
    (55859673262312, [79, 4369, 8738, 17652, 36744]),
    (52216737150952, [79, 4369, 8738, 20292, 35064]),
    (52024251824360, [79, 4369, 8738, 20468, 34952]),
    (9109104840704, [136, 240, 4369, 8751, 20292])]

theorem o4_0 : okL 893 3 D3 D4_0 = true := by decide +kernel

def D4_1 : List (ℕ × List ℕ) :=
  [(9109117578240, [240, 248, 4369, 8751, 20292]),
    (9116022984056, [240, 255, 4369, 8738, 20300]),
    (9106595676368, [240, 255, 4377, 8738, 20292]),
    (60703569834876, [240, 256, 8751, 21845, 36744]),
    (57904740229500, [240, 256, 8751, 24405, 34952]),
    (60700590774692, [240, 271, 8738, 21845, 36744]),
    (57901761169316, [240, 271, 8738, 24405, 34952]),
    (9109242933248, [240, 520, 4369, 8751, 20292]),
    (9109246203072, [240, 524, 4369, 8751, 20292]),
    (55029805621248, [240, 559, 4369, 17476, 36744]),
    (55484830612480, [240, 559, 4369, 17476, 36856]),
    (51137967222784, [240, 559, 4369, 20292, 34952]),
    (53793982133116, [240, 768, 8751, 21845, 34952]),
    (6091384102912, [240, 776, 4369, 8751, 17476]),
    (9117793316864, [240, 2056, 4369, 8751, 20292]),
    (6154873128064, [240, 3840, 4369, 8751, 17484]),
    (6155790251285, [240, 3840, 4369, 8751, 17485]),
    (6184273136256, [240, 3840, 4369, 8751, 17516]),
    (6638297556096, [240, 3840, 4369, 8751, 17996]),
    (8261623628928, [240, 3840, 4369, 8751, 19532]),
    (9175611692160, [240, 3840, 4369, 8751, 20300]),
    (11246163709637, [240, 3840, 4369, 8751, 21853]),
    (127709726295168, [240, 3840, 4369, 8751, 50252]),
    (144933586953536, [240, 3840, 4369, 8815, 52428]),
    (6147998873560, [240, 3840, 4377, 8751, 17476]),
    (6155332083288, [240, 3840, 4377, 8751, 17484]),
    (9166184384472, [240, 3840, 4377, 8751, 20292]),
    (11235165573509, [240, 3840, 4377, 8751, 21845]),
    (11246622664861, [240, 3840, 4377, 8751, 21853]),
    (6155331689916, [240, 3840, 4381, 8738, 17487]),
    (6148228981268, [240, 3840, 4381, 8751, 17476]),
    (6153612340284, [240, 3840, 4383, 8738, 17485]),
    (6149851532856, [240, 3840, 4409, 8751, 17476]),
    (144922494674240, [240, 3840, 4433, 8751, 52428]),
    (43512981407612, [240, 3840, 4437, 8751, 34952]),
    (6181002190296, [240, 3840, 4889, 8751, 17476]),
    (57314995566552, [240, 3840, 8751, 17476, 37145]),
    (54795262161788, [240, 3840, 8751, 21845, 35208]),
    (71947122316037, [240, 3840, 8751, 21845, 39321]),
    (72393498967589, [240, 3840, 8751, 21845, 39417]),
    (53910702986876, [240, 3840, 9007, 21845, 34952]),
    (50354385959512, [240, 3840, 13119, 17476, 34953]),
    (50351637211900, [240, 3840, 13119, 17477, 34952]),
    (50350765176064, [240, 3841, 13119, 17476, 34952]),
    (6147894550528, [240, 3848, 4369, 8751, 17476]),
    (6155227760256, [240, 3848, 4369, 8751, 17484]),
    (9166080061440, [240, 3848, 4369, 8751, 20292]),
    (9175966324352, [240, 3848, 4369, 8751, 20300]),
    (11235061250477, [240, 3848, 4369, 8751, 21845]),
    (6148353505752, [240, 3848, 4377, 8751, 17476]),
    (6147938983385, [240, 3849, 4369, 8751, 17476]),
    (6145761072384, [240, 3849, 4383, 8738, 17476]),
    (6148072420544, [240, 3852, 4369, 8751, 17476]),
    (6149327886336, [240, 3880, 4369, 8751, 17476]),
    (144921654402176, [240, 3904, 4369, 8751, 52428]),
    (43512088186880, [240, 3908, 4369, 8751, 34952]),
    (6153771712512, [240, 3976, 4369, 8751, 17476]),
    (6166167336064, [240, 4080, 4369, 8751, 17484]),
    (6159293081560, [240, 4080, 4377, 8751, 17476]),
    (71958416524037, [240, 4080, 8751, 21845, 39321]),
    (6159234423808, [240, 4088, 4369, 8751, 17476]),
    (9192957455881, [240, 4369, 4377, 8751, 20292]),
    (9786157991432, [240, 4369, 8738, 8751, 20300]),
    (14456343814336, [240, 4369, 8751, 17476, 20300]),
    (51666722062336, [240, 4369, 8751, 17476, 35720]),
    (55183139807232, [240, 4369, 8751, 17476, 36616]),
    (55699782533120, [240, 4369, 8751, 17476, 36744]),
    (55703833007961, [240, 4369, 8751, 17476, 36745]),
    (55715985755328, [240, 4369, 8751, 17476, 36748]),
    (55764616590336, [240, 4369, 8751, 17476, 36760]),
    (55829507110912, [240, 4369, 8751, 17476, 36776]),
    (55959457640448, [240, 4369, 8751, 17476, 36808]),
    (56154807524352, [240, 4369, 8751, 17476, 36856]),
    (156049179967488, [240, 4369, 8751, 17476, 53128]),
    (156625724487872, [240, 4369, 8751, 17476, 53196]),
    (157033585565120, [240, 4369, 8751, 17476, 53244]),
    (55700698817277, [240, 4369, 8751, 17477, 36744]),
    (14453790761152, [240, 4369, 8751, 17484, 20292]),
    (14463677024064, [240, 4369, 8751, 17484, 20300]),
    (55707115742848, [240, 4369, 8751, 17484, 36744]),
    (156635809381999, [240, 4369, 8751, 17487, 53196]),
    (55714455666432, [240, 4369, 8751, 17492, 36744]),
    (55729155667456, [240, 4369, 8751, 17508, 36744]),
    (55937790554112, [240, 4369, 8751, 17732, 36744]),
    (56182771081216, [240, 4369, 8751, 17988, 36744]),
    (56190540170880, [240, 4369, 8751, 17996, 36744]),
    (49524800868352, [240, 4369, 8751, 18244, 34952]),
    (57804714016768, [240, 4369, 8751, 19524, 36744]),
    (17474529325248, [240, 4369, 8751, 20292, 20300]),
    (44319250509824, [240, 4369, 8751, 20292, 32776]),
    (51807944134656, [240, 4369, 8751, 20292, 34952]),
    (51811609166425, [240, 4369, 8751, 20292, 34953]),
    (51822605520064, [240, 4369, 8751, 20292, 34956]),
    (51866609812480, [240, 4369, 8751, 20292, 34968]),
    (51925329201152, [240, 4369, 8751, 20292, 34984]),
    (52042929209344, [240, 4369, 8751, 20292, 35016]),
    (52219732667392, [240, 4369, 8751, 20292, 35064]),
    (52753054044160, [240, 4369, 8751, 20292, 35208]),
    (53712008302592, [240, 4369, 8751, 20292, 35464]),
    (53727102348480, [240, 4369, 8751, 20292, 35468]),
    (55671852519424, [240, 4369, 8751, 20292, 35976]),
    (58717968044032, [240, 4369, 8751, 20292, 36744]),
    (59172993035264, [240, 4369, 8751, 20292, 36856]),
    (68647396003840, [240, 4369, 8751, 20292, 39048]),
    (69904914198409, [240, 4369, 8751, 20292, 39321]),
    (70351290849961, [240, 4369, 8751, 20292, 39417]),
    (77311465628041, [240, 4369, 8751, 20292, 40857]),
    (144399221346304, [240, 4369, 8751, 20292, 51336]),
    (153217693432000, [240, 4369, 8751, 20292, 52428]),
    (153613868031424, [240, 4369, 8751, 20292, 52476]),
    (159643909998784, [240, 4369, 8751, 20292, 53196]),
    (160051771076032, [240, 4369, 8751, 20292, 53244]),
    (192330499698821, [240, 4369, 8751, 20292, 56797]),
    (197330282079877, [240, 4369, 8751, 20292, 57309]),
    (51809179491325, [240, 4369, 8751, 20293, 34952]),
    (9118988588160, [240, 4369, 8751, 20300]),
    (51817830397568, [240, 4369, 8751, 20300, 34952]),
    (241047222572160, [240, 4369, 8751, 20300, 61440]),
    (290581080593535, [240, 4369, 8751, 20300, 65535]),
    (159657505619823, [240, 4369, 8751, 20303, 53196]),
    (51827724455680, [240, 4369, 8751, 20308, 34952]),
    (51847535969792, [240, 4369, 8751, 20324, 34952]),
    (60400983048192, [240, 4369, 8751, 21572, 36744]),
    (60786949233069, [240, 4369, 8751, 21845, 36744]),
    (61241974224301, [240, 4369, 8751, 21845, 36856]),
    (161712891187821, [240, 4369, 8751, 21845, 53196]),
    (64898143537069, [240, 4369, 8751, 24405, 36744]),
    (165824085491821, [240, 4369, 8751, 24405, 53196]),
    (169301943150040, [240, 4369, 8751, 26214, 53196]),
    (169320503213263, [240, 4369, 8751, 26223, 53196]),
    (174481383469528, [240, 4369, 8751, 28518, 53196]),
    (174503348860879, [240, 4369, 8751, 28527, 53196]),
    (192835596013568, [240, 4369, 8751, 34952, 53060]),
    (177201372233728, [240, 4369, 8751, 36744, 50244]),
    (395804186294464, [240, 4369, 8751, 53196, 62532]),
    (430347926685888, [240, 4369, 8751, 53196, 65348]),
    (55703465098032, [240, 4369, 8767, 17476, 36744]),
    (51811626699568, [240, 4369, 8767, 20292, 34952]),
    (55714593687744, [240, 4369, 8815, 17476, 36744]),
    (51822755289280, [240, 4369, 8815, 20292, 34952]),
    (55760333267712, [240, 4369, 9007, 17476, 36744]),
    (51868494869248, [240, 4369, 9007, 20292, 34952]),
    (55700011800828, [240, 4373, 8751, 17476, 36744]),
    (51808173402364, [240, 4373, 8751, 20292, 34952]),
    (9776730683744, [240, 4377, 8738, 8751, 20292]),
    (14446916506648, [240, 4377, 8751, 17476, 20292]),
    (55700241488344, [240, 4377, 8751, 17476, 36744]),
    (9109561280472, [240, 4377, 8751, 20292]),
    (51808403089880, [240, 4377, 8751, 20292, 34952]),
    (241037795264472, [240, 4377, 8751, 20292, 61440]),
    (290571653285847, [240, 4377, 8751, 20292, 65535]),
    (55701655096960, [240, 4383, 8738, 17476, 36745]),
    (55698520906276, [240, 4383, 8738, 17477, 36744]),
    (51809431255424, [240, 4383, 8738, 20292, 34953]),
    (51807001580324, [240, 4383, 8738, 20293, 34952])]

theorem o4_1 : okL 893 3 D3 D4_1 = true := by decide +kernel

def D4_2 : List (ℕ × List ℕ) :=
  [(69905718472887, [240, 4383, 8751, 20292, 39321]),
    (60787753507547, [240, 4383, 8751, 21845, 36744]),
    (55701628450912, [240, 4401, 8751, 17476, 36744]),
    (51809790052448, [240, 4401, 8751, 20292, 34952]),
    (55703501408448, [240, 4433, 8751, 17476, 36744]),
    (51811663009984, [240, 4433, 8751, 20292, 34952]),
    (60800445373517, [240, 4593, 8751, 21845, 36744]),
    (55732672087552, [240, 4881, 8751, 17476, 36744]),
    (51840833689088, [240, 4881, 8751, 20292, 34952]),
    (51841119813372, [240, 4885, 8751, 20292, 34952]),
    (55733244805080, [240, 4889, 8751, 17476, 36744]),
    (49269942095104, [240, 7953, 9007, 17476, 34952]),
    (72073214759043, [240, 8751, 13107, 20292, 39321]),
    (62955249793703, [240, 8751, 13107, 21845, 36744]),
    (72079404987159, [240, 8751, 13119, 20292, 39321]),
    (62961440021819, [240, 8751, 13119, 21845, 36744]),
    (64554433855488, [240, 8751, 17476, 20753, 36744]),
    (80246039949125, [240, 8751, 20292, 21845, 39321]),
    (102942292889600, [240, 8751, 20292, 34952, 37137]),
    (304855131017097, [240, 8751, 20292, 39321, 61713]),
    (121499364930821, [240, 8751, 21845, 36744, 39321]),
    (295737166051757, [240, 8751, 21845, 36744, 61713]),
    (50350721101264, [241, 3840, 13119, 17476, 34952]),
    (55699782706641, [241, 4369, 8751, 17476, 36744]),
    (51807944308177, [241, 4369, 8751, 20292, 34952]),
    (55697604795640, [241, 4383, 8738, 17476, 36744]),
    (51805766397176, [241, 4383, 8738, 20292, 34952]),
    (55699783235904, [244, 4369, 8751, 17476, 36744]),
    (51807944837440, [244, 4369, 8751, 20292, 34952]),
    (6147541347328, [248, 3840, 4369, 8751, 17476]),
    (6154874557056, [248, 3840, 4369, 8751, 17484]),
    (9165726858240, [248, 3840, 4369, 8751, 20292]),
    (11234708047277, [248, 3840, 4369, 8751, 21845]),
    (6148000302552, [248, 3840, 4377, 8751, 17476]),
    (6147895979520, [248, 3848, 4369, 8751, 17476]),
    (6158835555328, [248, 4080, 4369, 8751, 17476]),
    (6159235852800, [248, 4088, 4369, 8751, 17476]),
    (9776273157512, [248, 4369, 8738, 8751, 20292]),
    (14446458980416, [248, 4369, 8751, 17476, 20292]),
    (55699783962112, [248, 4369, 8751, 17476, 36744]),
    (9109103754240, [248, 4369, 8751, 20292]),
    (51807945563648, [248, 4369, 8751, 20292, 34952]),
    (241037337738240, [248, 4369, 8751, 20292, 61440]),
    (290571195759615, [248, 4369, 8751, 20292, 65535]),
    (6147541532585, [249, 3840, 4369, 8751, 17476]),
    (6145363621584, [249, 3840, 4383, 8738, 17476]),
    (6154644805992, [252, 3840, 4369, 8738, 17487]),
    (6147542097344, [252, 3840, 4369, 8751, 17476]),
    (6163187907960, [255, 4080, 4369, 8738, 17484]),
    (6156313653456, [255, 4080, 4377, 8738, 17476]),
    (56154810281727, [255, 4369, 8751, 17476, 36856]),
    (52219735424767, [255, 4369, 8751, 20292, 35064]),
    (54261943738236, [256, 3840, 8751, 21845, 35064]),
    (54258964678052, [271, 3840, 8738, 21845, 35064]),
    (53850260452220, [496, 3840, 8751, 21845, 34952]),
    (55699890733056, [496, 4369, 8751, 17476, 36744]),
    (51808052334592, [496, 4369, 8751, 20292, 34952]),
    (49209499560448, [496, 7953, 8751, 17476, 34952]),
    (48588179524608, [559, 3840, 4369, 17476, 35064]),
    (48599473732608, [559, 4080, 4369, 17476, 35064]),
    (98595447130624, [559, 4369, 17476, 35064, 36856]),
    (55700193968128, [752, 4369, 8751, 17476, 36744]),
    (51808355569664, [752, 4369, 8751, 20292, 34952]),
    (51808362391872, [756, 4369, 8751, 20292, 34952]),
    (6147965070336, [760, 3840, 4369, 8751, 17476]),
    (55700207685120, [760, 4369, 8751, 17476, 36744]),
    (49201986317312, [768, 4369, 8751, 17476, 35064]),
    (48790768992256, [1008, 4369, 8751, 17476, 34952]),
    (55711746260992, [2288, 4369, 8751, 17476, 36744]),
    (6159629724672, [2296, 3840, 4369, 8751, 17476]),
    (49280014637416, [3840, 4369, 8738, 17487, 35068]),
    (42136823442432, [3840, 4369, 8751, 17476, 33016]),
    (49258156436480, [3840, 4369, 8751, 17476, 35064]),
    (49261844993961, [3840, 4369, 8751, 17476, 35065]),
    (49272911928768, [3840, 4369, 8751, 17476, 35068]),
    (50209310862336, [3840, 4369, 8751, 17476, 35320]),
    (51174353677312, [3840, 4369, 8751, 17476, 35576]),
    (49259072720637, [3840, 4369, 8751, 17477, 35064]),
    (49265489646208, [3840, 4369, 8751, 17484, 35064]),
    (49272829569792, [3840, 4369, 8751, 17492, 35064]),
    (49287529570816, [3840, 4369, 8751, 17508, 35064]),
    (49294889654400, [3840, 4369, 8751, 17516, 35064]),
    (49496164457472, [3840, 4369, 8751, 17732, 35064]),
    (49741144984576, [3840, 4369, 8751, 17988, 35064]),
    (53959356951552, [3840, 4369, 8751, 21572, 35064]),
    (54345323136429, [3840, 4369, 8751, 21845, 35064]),
    (49261839001392, [3840, 4369, 8767, 17476, 35064]),
    (49272967591104, [3840, 4369, 8815, 17476, 35064]),
    (49024065304000, [3840, 4369, 8815, 17652, 34952]),
    (49318707171072, [3840, 4369, 9007, 17476, 35064]),
    (49265488412836, [3840, 4373, 8738, 17487, 35064]),
    (49258385704188, [3840, 4373, 8751, 17476, 35064]),
    (49258615391704, [3840, 4377, 8751, 17476, 35064]),
    (49259667082960, [3840, 4383, 8738, 17476, 35065]),
    (49256894809636, [3840, 4383, 8738, 17477, 35064]),
    (54346127410907, [3840, 4383, 8751, 21845, 35064]),
    (49260002354272, [3840, 4401, 8751, 17476, 35064]),
    (49260468051000, [3840, 4409, 8751, 17476, 35064]),
    (49261875311808, [3840, 4433, 8751, 17476, 35064]),
    (49012973024704, [3840, 4433, 8751, 17652, 34952]),
    (48874537177504, [3840, 4593, 8751, 17492, 34952]),
    (54358819276877, [3840, 4593, 8751, 21845, 35064]),
    (48863546609104, [3840, 4593, 8767, 17476, 34952]),
    (49291045990912, [3840, 4881, 8751, 17476, 35064]),
    (56513623697063, [3840, 8751, 13107, 21845, 35064]),
    (56519813925179, [3840, 8751, 13119, 21845, 35064]),
    (58112807758848, [3840, 8751, 17476, 20753, 35064]),
    (115057738834181, [3840, 8751, 21845, 35064, 39321]),
    (115504115485733, [3840, 8751, 21845, 35064, 39417]),
    (289295539955117, [3840, 8751, 21845, 35064, 61713]),
    (49258200684801, [3841, 4369, 8751, 17476, 35064]),
    (49256022773800, [3841, 4383, 8738, 17476, 35064]),
    (49258333568064, [3844, 4369, 8751, 17476, 35064]),
    (49258511068672, [3848, 4369, 8751, 17476, 35064]),
    (49258867178496, [3856, 4369, 8751, 17476, 35064]),
    (48860574786208, [3856, 4593, 8751, 17476, 34952]),
    (49259583843328, [3872, 4369, 8751, 17476, 35064]),
    (49259944404480, [3880, 4369, 8751, 17476, 35064]),
    (49261035039744, [3904, 4369, 8751, 17476, 35064]),
    (49264009587712, [3968, 4369, 8751, 17476, 35064]),
    (49092647186432, [4080, 4369, 8751, 17476, 35016]),
    (49269450644480, [4080, 4369, 8751, 17476, 35064]),
    (67401008827049, [4080, 4369, 8751, 17476, 39417]),
    (54356617344429, [4080, 4369, 8751, 21845, 35064]),
    (48872473266368, [4080, 4369, 8815, 17476, 34952]),
    (48861380987072, [4080, 4433, 8751, 17476, 34952]),
    (53958324952141, [4080, 4593, 8751, 21845, 34952]),
    (56251686016209, [4369, 4593, 8751, 17476, 36856]),
    (52316611159249, [4369, 4593, 8751, 20292, 35064]),
    (56870750274888, [4369, 8751, 8946, 17476, 36856]),
    (52935675417928, [4369, 8751, 8946, 20292, 35064]),
    (56873876018431, [4369, 8751, 8959, 17476, 36856]),
    (52938801161471, [4369, 8751, 8959, 20292, 35064]),
    (57473355131904, [4369, 8751, 17476, 20224, 35064]),
    (57557074069568, [4369, 8751, 17476, 20292, 35064]),
    (57776377275712, [4369, 8751, 17476, 20468, 35064]),
    (91662911045632, [4369, 8751, 17476, 33008, 36744]),
    (98261585800192, [4369, 8751, 17476, 35064, 36608]),
    (98810399051264, [4369, 8751, 17476, 35064, 36744]),
    (99265424042496, [4369, 8751, 17476, 35064, 36856]),
    (199736341006016, [4369, 8751, 17476, 35064, 53196]),
    (200144202083264, [4369, 8751, 17476, 35064, 53244]),
    (99291248363263, [4369, 8751, 17476, 35071, 36856]),
    (117396982225065, [4369, 8751, 17476, 36856, 39417]),
    (140009924333352, [4369, 8751, 17476, 36856, 43770]),
    (140038664809727, [4369, 8751, 17476, 36856, 43775]),
    (290811567332352, [4369, 8751, 17476, 36856, 61680]),
    (315068124932608, [4369, 8751, 17476, 36856, 63736]),
    (57567158963695, [4369, 8751, 17487, 20292, 35064]),
    (57719960315200, [4369, 8751, 17652, 20292, 35064]),
    (62644240769517, [4369, 8751, 20292, 21845, 35064]),
    (70233292731736, [4369, 8751, 20292, 26214, 35064]),
    (70251852794959, [4369, 8751, 20292, 26223, 35064])]

theorem o4_2 : okL 893 3 D3 D4_2 = true := by decide +kernel

def D4_3 : List (ℕ × List ℕ) :=
  [(87771072647168, [4369, 8751, 20292, 33008, 34952]),
    (286876492475392, [4369, 8751, 20292, 35064, 61680]),
    (296735535876160, [4369, 8751, 20292, 35064, 62532]),
    (103897565751213, [4369, 8751, 21845, 35064, 36744]),
    (104352590742445, [4369, 8751, 21845, 35064, 36856])]

theorem o4_3 : okL 893 3 D3 D4_3 = true := by decide +kernel

def D4 : List (ℕ × List ℕ) := D4_0 ++ D4_1 ++ D4_2 ++ D4_3

theorem t4 : Dead 893 4 D4 :=
  dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (okL_sound _ _ _ _ t3 o4_0) (okL_sound _ _ _ _ t3 o4_1)) (okL_sound _ _ _ _ t3 o4_2)) (okL_sound _ _ _ _ t3 o4_3)

def D5_0 : List (ℕ × List ℕ) :=
  [(9109102325760, [0, 8, 240, 4369, 8751, 20292]),
    (9116006406056, [0, 15, 240, 4369, 8738, 20300]),
    (9106579098368, [0, 15, 240, 4377, 8738, 20292]),
    (71403063173667, [0, 15, 240, 13107, 20292, 39321]),
    (62285098208327, [0, 15, 240, 13107, 21845, 36744]),
    (9106121572136, [0, 15, 248, 4369, 8738, 20292]),
    (55843472111687, [0, 15, 3840, 13107, 21845, 35064]),
    (6154873128064, [0, 240, 3840, 4369, 8751, 17484]),
    (6147998873560, [0, 240, 3840, 4377, 8751, 17476]),
    (71947122316037, [0, 240, 3840, 8751, 21845, 39321]),
    (6147894550528, [0, 240, 3848, 4369, 8751, 17476]),
    (55699782533120, [0, 240, 4369, 8751, 17476, 36744]),
    (56154807524352, [0, 240, 4369, 8751, 17476, 36856]),
    (156625724487872, [0, 240, 4369, 8751, 17476, 53196]),
    (51807944134656, [0, 240, 4369, 8751, 20292, 34952]),
    (52219732667392, [0, 240, 4369, 8751, 20292, 35064]),
    (58717968044032, [0, 240, 4369, 8751, 20292, 36744]),
    (69904914198409, [0, 240, 4369, 8751, 20292, 39321]),
    (153217693432000, [0, 240, 4369, 8751, 20292, 52428]),
    (159643909998784, [0, 240, 4369, 8751, 20292, 53196]),
    (60786949233069, [0, 240, 4369, 8751, 21845, 36744]),
    (6147541347328, [0, 248, 3840, 4369, 8751, 17476]),
    (49258156436480, [0, 3840, 4369, 8751, 17476, 35064]),
    (54345323136429, [0, 3840, 4369, 8751, 21845, 35064]),
    (49269450644480, [0, 4080, 4369, 8751, 17476, 35064]),
    (57557074069568, [0, 4369, 8751, 17476, 20292, 35064]),
    (98810399051264, [0, 4369, 8751, 17476, 35064, 36744]),
    (99265424042496, [0, 4369, 8751, 17476, 35064, 36856]),
    (57197931508379, [1, 15, 240, 13107, 17476, 36744]),
    (53306093109915, [1, 15, 240, 13107, 20292, 34952]),
    (50756305411739, [1, 15, 3840, 13107, 17476, 35064]),
    (50350720927744, [1, 240, 3840, 13119, 17476, 34952]),
    (55699782533121, [1, 240, 4369, 8751, 17476, 36744]),
    (51807944134657, [1, 240, 4369, 8751, 20292, 34952]),
    (55697604622120, [1, 240, 4383, 8738, 17476, 36744]),
    (51805766223656, [1, 240, 4383, 8738, 20292, 34952]),
    (49258156436481, [1, 3840, 4369, 8751, 17476, 35064]),
    (49255978525480, [1, 3840, 4383, 8738, 17476, 35064]),
    (55699782533128, [2, 240, 4369, 8751, 17476, 36744]),
    (51807944134664, [2, 240, 4369, 8751, 20292, 34952]),
    (49258156436488, [2, 3840, 4369, 8751, 17476, 35064]),
    (55699782533184, [4, 240, 4369, 8751, 17476, 36744]),
    (51807944134720, [4, 240, 4369, 8751, 20292, 34952]),
    (49265259145192, [4, 3840, 4369, 8738, 17487, 35064]),
    (49258156436544, [4, 3840, 4369, 8751, 17476, 35064]),
    (12732855594055, [8, 15, 240, 3840, 13107, 21845]),
    (9106120143656, [8, 15, 240, 4369, 8738, 20292]),
    (9116006406568, [8, 15, 240, 4369, 8738, 20300]),
    (9107954285320, [8, 15, 240, 4369, 8746, 20292]),
    (9109102329135, [8, 15, 240, 4369, 8751, 20292]),
    (10690647476427, [8, 15, 240, 4369, 13107, 20292]),
    (9106579098880, [8, 15, 240, 4377, 8738, 20292]),
    (9106121572648, [8, 15, 248, 4369, 8738, 20292]),
    (9106136721656, [8, 240, 255, 4369, 8738, 20292]),
    (6147539918848, [8, 240, 3840, 4369, 8751, 17476]),
    (6154873128576, [8, 240, 3840, 4369, 8751, 17484]),
    (9165725429760, [8, 240, 3840, 4369, 8751, 20292]),
    (11234706618797, [8, 240, 3840, 4369, 8751, 21845]),
    (6147998874072, [8, 240, 3840, 4377, 8751, 17476]),
    (6147894551040, [8, 240, 3848, 4369, 8751, 17476]),
    (6158834126848, [8, 240, 4080, 4369, 8751, 17476]),
    (9776271729032, [8, 240, 4369, 8738, 8751, 20292]),
    (14446457551936, [8, 240, 4369, 8751, 17476, 20292]),
    (55699782533632, [8, 240, 4369, 8751, 17476, 36744]),
    (9109102325760, [8, 240, 4369, 8751, 20292]),
    (51807944135168, [8, 240, 4369, 8751, 20292, 34952]),
    (241037336309760, [8, 240, 4369, 8751, 20292, 61440]),
    (290571194331135, [8, 240, 4369, 8751, 20292, 65535]),
    (6147541347840, [8, 248, 3840, 4369, 8751, 17476]),
    (6155854698744, [8, 255, 4080, 4369, 8738, 17476]),
    (49258156436992, [8, 3840, 4369, 8751, 17476, 35064]),
    (7645688894323, [9, 15, 240, 3840, 13107, 17476]),
    (9106120143873, [9, 15, 240, 4369, 8738, 20292]),
    (6147539919065, [9, 240, 3840, 4369, 8751, 17476]),
    (6145362008064, [9, 240, 3840, 4383, 8738, 17476]),
    (9106120144872, [12, 15, 240, 4369, 8738, 20292]),
    (6154642628712, [12, 240, 3840, 4369, 8738, 17487]),
    (6147539920064, [12, 240, 3840, 4369, 8751, 17476]),
    (6144557735054, [13, 240, 3840, 4369, 8738, 17476]),
    (11231724435003, [13, 240, 3840, 4369, 8738, 21845]),
    (51818444273096, [15, 16, 4593, 8738, 20292, 34952]),
    (51853735332584, [15, 32, 4369, 8946, 20292, 34952]),
    (151285387341736, [15, 64, 240, 4369, 8738, 53196]),
    (145311954654376, [15, 64, 3840, 4369, 8738, 52476]),
    (144927074262952, [15, 64, 4080, 4369, 8738, 52428]),
    (56151811780392, [15, 64, 4369, 8738, 17476, 36856]),
    (55859673034792, [15, 64, 4369, 8738, 17652, 36744]),
    (52216736923432, [15, 64, 4369, 8738, 20292, 35064]),
    (52024251596840, [15, 64, 4369, 8738, 20468, 34952]),
    (50359445439272, [15, 68, 240, 4369, 8738, 36744]),
    (43917819342632, [15, 68, 3840, 4369, 8738, 35064]),
    (43517325017896, [15, 68, 4080, 4369, 8738, 34952]),
    (9106122658600, [15, 136, 240, 4369, 8738, 20292]),
    (9106135396136, [15, 240, 248, 4369, 8738, 20292]),
    (60700587652772, [15, 240, 256, 8738, 21845, 36744]),
    (57901758047396, [15, 240, 256, 8738, 24405, 34952]),
    (55029791936928, [15, 240, 544, 4369, 17476, 36744]),
    (55484816928160, [15, 240, 544, 4369, 17476, 36856]),
    (51137953538464, [15, 240, 544, 4369, 20292, 34952]),
    (53790999951012, [15, 240, 768, 8738, 21845, 34952]),
    (68385330647587, [15, 240, 768, 13107, 17476, 39321]),
    (55375527283783, [15, 240, 768, 13107, 21845, 34952]),
    (48120150376864, [15, 240, 816, 4369, 17476, 34952]),
    (9114811134760, [15, 240, 2056, 4369, 8738, 20292]),
    (6151890945960, [15, 240, 3840, 4369, 8738, 17484]),
    (6152808069181, [15, 240, 3840, 4369, 8738, 17485]),
    (8258641446824, [15, 240, 3840, 4369, 8738, 19532]),
    (9172629510056, [15, 240, 3840, 4369, 8738, 20300]),
    (11243181527533, [15, 240, 3840, 4369, 8738, 21853]),
    (127706744113064, [15, 240, 3840, 4369, 8738, 50252]),
    (245416877574056, [15, 240, 3840, 4369, 8738, 62540]),
    (6153725087624, [15, 240, 3840, 4369, 8746, 17484]),
    (6154873131439, [15, 240, 3840, 4369, 8751, 17484]),
    (144930560959144, [15, 240, 3840, 4369, 8802, 52428]),
    (7736418278731, [15, 240, 3840, 4369, 13107, 17484]),
    (243651309995944, [15, 240, 3840, 4369, 17484, 61986]),
    (6145016691456, [15, 240, 3840, 4377, 8738, 17476]),
    (6152349901184, [15, 240, 3840, 4377, 8738, 17484])]

theorem o5_0 : okL 893 4 D4 D5_0 = true := by decide +kernel

def D5_1 : List (ℕ × List ℕ) :=
  [(9163202202368, [15, 240, 3840, 4377, 8738, 20292]),
    (11232183391405, [15, 240, 3840, 4377, 8738, 21845]),
    (11243640482757, [15, 240, 3840, 4377, 8738, 21853]),
    (245323478498048, [15, 240, 3840, 4377, 8738, 62532]),
    (6146850833120, [15, 240, 3840, 4377, 8746, 17476]),
    (6147998876935, [15, 240, 3840, 4377, 8751, 17476]),
    (7729544024227, [15, 240, 3840, 4377, 13107, 17476]),
    (7733669584059, [15, 240, 3840, 4377, 13115, 17476]),
    (243644435741440, [15, 240, 3840, 4377, 17476, 61986]),
    (6145246799164, [15, 240, 3840, 4381, 8738, 17476]),
    (144919512492136, [15, 240, 3840, 4433, 8738, 52428]),
    (43509999225508, [15, 240, 3840, 4437, 8738, 34952]),
    (48211421843456, [15, 240, 3840, 4913, 17476, 34952]),
    (57312013384448, [15, 240, 3840, 8738, 17476, 37145]),
    (241186190269184, [15, 240, 3840, 8738, 17476, 61721]),
    (241102107764648, [15, 240, 3840, 8738, 17484, 61713]),
    (54792279979684, [15, 240, 3840, 8738, 21845, 35208]),
    (71944140133933, [15, 240, 3840, 8738, 21845, 39321]),
    (72390516785485, [15, 240, 3840, 8738, 21845, 39417]),
    (272028700096045, [15, 240, 3840, 8738, 21845, 63897]),
    (309251932517933, [15, 240, 3840, 8738, 39321, 62805]),
    (509336492480045, [15, 240, 3840, 8738, 62805, 63897]),
    (71947122319412, [15, 240, 3840, 8751, 21845, 39321]),
    (53907543638692, [15, 240, 3840, 8994, 21845, 34952]),
    (50348195734771, [15, 240, 3840, 13107, 17476, 34953]),
    (68441500766755, [15, 240, 3840, 13107, 17476, 39321]),
    (68887877418307, [15, 240, 3840, 13107, 17476, 39417]),
    (75848052196387, [15, 240, 3840, 13107, 17476, 40857]),
    (190867086267167, [15, 240, 3840, 13107, 17476, 56797]),
    (268526060728867, [15, 240, 3840, 13107, 17476, 63897]),
    (50345446987159, [15, 240, 3840, 13107, 17477, 34952]),
    (71459686277667, [15, 240, 3840, 13107, 20292, 39321]),
    (55431697402951, [15, 240, 3840, 13107, 21845, 34952]),
    (55843485935687, [15, 240, 3840, 13107, 21845, 35064]),
    (62341721312327, [15, 240, 3840, 13107, 21845, 36744]),
    (73528667466704, [15, 240, 3840, 13107, 21845, 39321]),
    (156841446700295, [15, 240, 3840, 13107, 21845, 52428]),
    (195954252967116, [15, 240, 3840, 13107, 21845, 56797]),
    (270283658628167, [15, 240, 3840, 13107, 21845, 63624]),
    (59542891706951, [15, 240, 3840, 13107, 24405, 34952]),
    (292739489786951, [15, 240, 3840, 13107, 34952, 62805]),
    (307619962573347, [15, 240, 3840, 13107, 39321, 62532]),
    (68447690994871, [15, 240, 3840, 13119, 17476, 39321]),
    (55437887631067, [15, 240, 3840, 13119, 21845, 34952]),
    (307517086470691, [15, 240, 3840, 17476, 39321, 62259]),
    (507601646432803, [15, 240, 3840, 17476, 62259, 63897]),
    (294507283106887, [15, 240, 3840, 21845, 34952, 62259]),
    (309443559183917, [15, 240, 3840, 21845, 39321, 61986]),
    (531815075490887, [15, 240, 3840, 34952, 62259, 62805]),
    (50344574951323, [15, 240, 3841, 13107, 17476, 34952]),
    (6144912368424, [15, 240, 3848, 4369, 8738, 17476]),
    (6152245578152, [15, 240, 3848, 4369, 8738, 17484]),
    (9163097879336, [15, 240, 3848, 4369, 8738, 20292]),
    (9172984142248, [15, 240, 3848, 4369, 8738, 20300]),
    (11232079068373, [15, 240, 3848, 4369, 8738, 21845]),
    (245323374175016, [15, 240, 3848, 4369, 8738, 62532]),
    (6146746510088, [15, 240, 3848, 4369, 8746, 17476]),
    (6147894553903, [15, 240, 3848, 4369, 8751, 17476]),
    (7729439701195, [15, 240, 3848, 4369, 13107, 17476]),
    (243644331418408, [15, 240, 3848, 4369, 17476, 61986]),
    (6145371323648, [15, 240, 3848, 4377, 8738, 17476]),
    (241095129187112, [15, 240, 3848, 8738, 17476, 61713]),
    (6144956801281, [15, 240, 3849, 4369, 8738, 17476]),
    (6145090238440, [15, 240, 3852, 4369, 8738, 17476]),
    (144918672220072, [15, 240, 3904, 4369, 8738, 52428]),
    (43509106004776, [15, 240, 3908, 4369, 8738, 34952]),
    (6150789530408, [15, 240, 3976, 4369, 8738, 17476]),
    (6163185153960, [15, 240, 4080, 4369, 8738, 17484]),
    (6156310899456, [15, 240, 4080, 4377, 8738, 17476]),
    (48222716051456, [15, 240, 4080, 4913, 17476, 34952]),
    (71955434341933, [15, 240, 4080, 8738, 21845, 39321]),
    (68452794974755, [15, 240, 4080, 13107, 17476, 39321]),
    (55442991610951, [15, 240, 4080, 13107, 21845, 34952]),
    (6156252241704, [15, 240, 4088, 4369, 8738, 17476]),
    (9189975273777, [15, 240, 4369, 4377, 8738, 20292]),
    (14453361632232, [15, 240, 4369, 8738, 17476, 20300]),
    (51663739880232, [15, 240, 4369, 8738, 17476, 35720]),
    (55180157625128, [15, 240, 4369, 8738, 17476, 36616]),
    (55696800351016, [15, 240, 4369, 8738, 17476, 36744]),
    (55700850825857, [15, 240, 4369, 8738, 17476, 36745]),
    (55713003573224, [15, 240, 4369, 8738, 17476, 36748]),
    (55761634408232, [15, 240, 4369, 8738, 17476, 36760]),
    (55826524928808, [15, 240, 4369, 8738, 17476, 36776]),
    (55956475458344, [15, 240, 4369, 8738, 17476, 36808]),
    (56151825342248, [15, 240, 4369, 8738, 17476, 36856]),
    (156046197785384, [15, 240, 4369, 8738, 17476, 53128]),
    (156622742305768, [15, 240, 4369, 8738, 17476, 53196]),
    (157030603383016, [15, 240, 4369, 8738, 17476, 53244]),
    (55697716635173, [15, 240, 4369, 8738, 17477, 36744]),
    (14450808579048, [15, 240, 4369, 8738, 17484, 20292]),
    (14460694841960, [15, 240, 4369, 8738, 17484, 20300]),
    (55704133560744, [15, 240, 4369, 8738, 17484, 36744]),
    (156632827199895, [15, 240, 4369, 8738, 17487, 53196]),
    (55711473484328, [15, 240, 4369, 8738, 17492, 36744]),
    (55726173485352, [15, 240, 4369, 8738, 17508, 36744]),
    (55934808372008, [15, 240, 4369, 8738, 17732, 36744]),
    (56179788899112, [15, 240, 4369, 8738, 17988, 36744]),
    (49521818686248, [15, 240, 4369, 8738, 18244, 34952]),
    (57801731834664, [15, 240, 4369, 8738, 19524, 36744]),
    (17471547143144, [15, 240, 4369, 8738, 20292, 20300]),
    (44316268327720, [15, 240, 4369, 8738, 20292, 32776]),
    (51804961952552, [15, 240, 4369, 8738, 20292, 34952]),
    (51808626984321, [15, 240, 4369, 8738, 20292, 34953])]

theorem o5_1 : okL 893 4 D4 D5_1 = true := by decide +kernel

def D5_2 : List (ℕ × List ℕ) :=
  [(51819623337960, [15, 240, 4369, 8738, 20292, 34956]),
    (51863627630376, [15, 240, 4369, 8738, 20292, 34968]),
    (51922347019048, [15, 240, 4369, 8738, 20292, 34984]),
    (52039947027240, [15, 240, 4369, 8738, 20292, 35016]),
    (52216750485288, [15, 240, 4369, 8738, 20292, 35064]),
    (52750071862056, [15, 240, 4369, 8738, 20292, 35208]),
    (53709026120488, [15, 240, 4369, 8738, 20292, 35464]),
    (55668870337320, [15, 240, 4369, 8738, 20292, 35976]),
    (58714985861928, [15, 240, 4369, 8738, 20292, 36744]),
    (59170010853160, [15, 240, 4369, 8738, 20292, 36856]),
    (68644413821736, [15, 240, 4369, 8738, 20292, 39048]),
    (69901932016305, [15, 240, 4369, 8738, 20292, 39321]),
    (70348308667857, [15, 240, 4369, 8738, 20292, 39417]),
    (77308483445937, [15, 240, 4369, 8738, 20292, 40857]),
    (89414566073128, [15, 240, 4369, 8738, 20292, 43144]),
    (144396239164200, [15, 240, 4369, 8738, 20292, 51336]),
    (153214711249896, [15, 240, 4369, 8738, 20292, 52428]),
    (153610885849320, [15, 240, 4369, 8738, 20292, 52476]),
    (159640927816680, [15, 240, 4369, 8738, 20292, 53196]),
    (160048788893928, [15, 240, 4369, 8738, 20292, 53244]),
    (192327517516717, [15, 240, 4369, 8738, 20292, 56797]),
    (197327299897773, [15, 240, 4369, 8738, 20292, 57309]),
    (241124962890536, [15, 240, 4369, 8738, 20292, 61448]),
    (266656923177768, [15, 240, 4369, 8738, 20292, 63624]),
    (268019451375400, [15, 240, 4369, 8738, 20292, 63736]),
    (269986491978417, [15, 240, 4369, 8738, 20292, 63897]),
    (280147125156840, [15, 240, 4369, 8738, 20292, 64716]),
    (289037738054440, [15, 240, 4369, 8738, 20292, 65416]),
    (289911613443048, [15, 240, 4369, 8738, 20292, 65484]),
    (51806197309221, [15, 240, 4369, 8738, 20293, 34952]),
    (9116006406056, [15, 240, 4369, 8738, 20300]),
    (51814848215464, [15, 240, 4369, 8738, 20300, 34952]),
    (241044240390056, [15, 240, 4369, 8738, 20300, 61440]),
    (290578098411431, [15, 240, 4369, 8738, 20300, 65535]),
    (159654523437719, [15, 240, 4369, 8738, 20303, 53196]),
    (51824742273576, [15, 240, 4369, 8738, 20308, 34952]),
    (51844553787688, [15, 240, 4369, 8738, 20324, 34952]),
    (60398000866088, [15, 240, 4369, 8738, 21572, 36744]),
    (60783967050965, [15, 240, 4369, 8738, 21845, 36744]),
    (61238992042197, [15, 240, 4369, 8738, 21845, 36856]),
    (161709909005717, [15, 240, 4369, 8738, 21845, 53196]),
    (64895161354965, [15, 240, 4369, 8738, 24405, 36744]),
    (165821103309717, [15, 240, 4369, 8738, 24405, 53196]),
    (67270710002472, [15, 240, 4369, 8738, 25668, 36744]),
    (169298960967936, [15, 240, 4369, 8738, 26214, 53196]),
    (174478401287424, [15, 240, 4369, 8738, 28518, 53196]),
    (192832613831464, [15, 240, 4369, 8738, 34952, 53060]),
    (177198390051624, [15, 240, 4369, 8738, 36744, 50244]),
    (294875262157608, [15, 240, 4369, 8738, 36744, 62532]),
    (298091759434965, [15, 240, 4369, 8738, 36744, 62805]),
    (329419002549032, [15, 240, 4369, 8738, 36744, 65348]),
    (295330287148840, [15, 240, 4369, 8738, 36856, 62532]),
    (395801204112360, [15, 240, 4369, 8738, 53196, 62532]),
    (430344944503784, [15, 240, 4369, 8738, 53196, 65348]),
    (55697029435163, [15, 240, 4369, 8739, 17476, 36744]),
    (51805191036699, [15, 240, 4369, 8739, 20292, 34952]),
    (55697717002232, [15, 240, 4369, 8742, 17476, 36744]),
    (51805878603768, [15, 240, 4369, 8742, 20292, 34952]),
    (55698634492680, [15, 240, 4369, 8746, 17476, 36744]),
    (51806796094216, [15, 240, 4369, 8746, 20292, 34952]),
    (55699782536495, [15, 240, 4369, 8751, 17476, 36744]),
    (56154807527727, [15, 240, 4369, 8751, 17476, 36856]),
    (156625724491247, [15, 240, 4369, 8751, 17476, 53196]),
    (51807944138031, [15, 240, 4369, 8751, 20292, 34952]),
    (52219732670767, [15, 240, 4369, 8751, 20292, 35064]),
    (58717968047407, [15, 240, 4369, 8751, 20292, 36744]),
    (69904914201784, [15, 240, 4369, 8751, 20292, 39321]),
    (153217693435375, [15, 240, 4369, 8751, 20292, 52428]),
    (159643910002159, [15, 240, 4369, 8751, 20292, 53196]),
    (266659905363247, [15, 240, 4369, 8751, 20292, 63624]),
    (60786949236444, [15, 240, 4369, 8751, 21845, 36744]),
    (294878244343087, [15, 240, 4369, 8751, 36744, 62532]),
    (55700471992808, [15, 240, 4369, 8754, 17476, 36744]),
    (51808633594344, [15, 240, 4369, 8754, 20292, 34952]),
    (55711567693352, [15, 240, 4369, 8802, 17476, 36744]),
    (51819729294888, [15, 240, 4369, 8802, 20292, 34952]),
    (55757173919528, [15, 240, 4369, 8994, 17476, 36744]),
    (51865335521064, [15, 240, 4369, 8994, 20292, 34952]),
    (57143539057448, [15, 240, 4369, 12834, 17476, 36744]),
    (53251700658984, [15, 240, 4369, 12834, 20292, 34952]),
    (53248267213003, [15, 240, 4369, 13107, 17476, 35720]),
    (57281327683787, [15, 240, 4369, 13107, 17476, 36744]),
    (57736352675019, [15, 240, 4369, 13107, 17476, 36856]),
    (158207269638539, [15, 240, 4369, 13107, 17476, 53196]),
    (51106346019019, [15, 240, 4369, 13107, 18244, 34952]),
    (53389489285323, [15, 240, 4369, 13107, 20292, 34952]),
    (53801277818059, [15, 240, 4369, 13107, 20292, 35064]),
    (60299513194699, [15, 240, 4369, 13107, 20292, 36744]),
    (71486459349076, [15, 240, 4369, 13107, 20292, 39321]),
    (154799238582667, [15, 240, 4369, 13107, 20292, 52428]),
    (161225455149451, [15, 240, 4369, 13107, 20292, 53196]),
    (268241450510539, [15, 240, 4369, 13107, 20292, 63624]),
    (62368494383736, [15, 240, 4369, 13107, 21845, 36744]),
    (296459789490379, [15, 240, 4369, 13107, 36744, 62532]),
    (57287517911903, [15, 240, 4369, 13119, 17476, 36744]),
    (53395679513439, [15, 240, 4369, 13119, 20292, 34952]),
    (70884499063592, [15, 240, 4369, 17476, 25122, 36744]),
    (122642172531496, [15, 240, 4369, 20292, 34952, 41506]),
    (296214404911912, [15, 240, 4369, 20292, 36744, 61986]),
    (55697029618724, [15, 240, 4373, 8738, 17476, 36744]),
    (51805191220260, [15, 240, 4373, 8738, 20292, 34952]),
    (14443934324544, [15, 240, 4377, 8738, 17476, 20292]),
    (55697259306240, [15, 240, 4377, 8738, 17476, 36744]),
    (9106579098368, [15, 240, 4377, 8738, 20292])]

theorem o5_2 : okL 893 4 D4 D5_2 = true := by decide +kernel

def D5_3 : List (ℕ × List ℕ) :=
  [(51805420907776, [15, 240, 4377, 8738, 20292, 34952]),
    (241034813082368, [15, 240, 4377, 8738, 20292, 61440]),
    (290568671103743, [15, 240, 4377, 8738, 20292, 65535]),
    (69902736290783, [15, 240, 4383, 8738, 20292, 39321]),
    (60784771325443, [15, 240, 4383, 8738, 21845, 36744]),
    (55698646268808, [15, 240, 4401, 8738, 17476, 36744]),
    (51806807870344, [15, 240, 4401, 8738, 20292, 34952]),
    (55700519226344, [15, 240, 4433, 8738, 17476, 36744]),
    (51808680827880, [15, 240, 4433, 8738, 20292, 34952]),
    (60797463191413, [15, 240, 4593, 8738, 21845, 36744]),
    (57294823824235, [15, 240, 4593, 13107, 17476, 36744]),
    (53402985425771, [15, 240, 4593, 13107, 20292, 34952]),
    (55729689905448, [15, 240, 4881, 8738, 17476, 36744]),
    (51837851506984, [15, 240, 4881, 8738, 20292, 34952]),
    (49909165696296, [15, 240, 4881, 12066, 17476, 34952]),
    (49266782746920, [15, 240, 7953, 8994, 17476, 34952]),
    (57700960420555, [15, 240, 7953, 13107, 17476, 36744]),
    (53809122022091, [15, 240, 7953, 13107, 20292, 34952]),
    (57595262690088, [15, 240, 8738, 12561, 17476, 36744]),
    (53703424291624, [15, 240, 8738, 12561, 20292, 34952]),
    (72070232576939, [15, 240, 8738, 13107, 20292, 39321]),
    (62952267611599, [15, 240, 8738, 13107, 21845, 36744]),
    (64551451673384, [15, 240, 8738, 17476, 20753, 36744]),
    (80243057767021, [15, 240, 8738, 20292, 21845, 39321]),
    (102939310707496, [15, 240, 8738, 20292, 34952, 37137]),
    (293665202680616, [15, 240, 8738, 20292, 36744, 61713]),
    (304852148834993, [15, 240, 8738, 20292, 39321, 61713]),
    (121496382748717, [15, 240, 8738, 21845, 36744, 39321]),
    (295734183869653, [15, 240, 8738, 21845, 36744, 61713]),
    (76740418399843, [15, 240, 13107, 17476, 20292, 39321]),
    (67622453434503, [15, 240, 13107, 17476, 21845, 36744]),
    (117993743381539, [15, 240, 13107, 17476, 36744, 39321]),
    (125400294811171, [15, 240, 13107, 17476, 36744, 40857]),
    (292231544502475, [15, 240, 13107, 17476, 36744, 61713]),
    (63730615036039, [15, 240, 13107, 20292, 21845, 34952]),
    (67841809340039, [15, 240, 13107, 20292, 24405, 34952]),
    (114101904983075, [15, 240, 13107, 20292, 34952, 39321]),
    (288339706104011, [15, 240, 13107, 20292, 34952, 61713]),
    (71403063173667, [15, 240, 13107, 20292, 39321]),
    (303331297157667, [15, 240, 13107, 20292, 39321, 61440]),
    (352865155179042, [15, 240, 13107, 20292, 39321, 65535]),
    (104983940017735, [15, 240, 13107, 21845, 34952, 36744]),
    (62285098208327, [15, 240, 13107, 21845, 36744]),
    (294213332192327, [15, 240, 13107, 21845, 36744, 61440]),
    (343747190213702, [15, 240, 13107, 21845, 36744, 65535]),
    (50344530876523, [15, 241, 3840, 13107, 17476, 34952]),
    (55696800524537, [15, 241, 4369, 8738, 17476, 36744]),
    (51804962126073, [15, 241, 4369, 8738, 20292, 34952]),
    (55696801053800, [15, 244, 4369, 8738, 17476, 36744]),
    (51804962655336, [15, 244, 4369, 8738, 20292, 34952]),
    (6144559165224, [15, 248, 3840, 4369, 8738, 17476]),
    (6151892374952, [15, 248, 3840, 4369, 8738, 17484]),
    (9162744676136, [15, 248, 3840, 4369, 8738, 20292]),
    (11231725865173, [15, 248, 3840, 4369, 8738, 21845]),
    (245323020971816, [15, 248, 3840, 4369, 8738, 62532]),
    (6146393306888, [15, 248, 3840, 4369, 8746, 17476]),
    (6147541350703, [15, 248, 3840, 4369, 8751, 17476]),
    (7729086497995, [15, 248, 3840, 4369, 13107, 17476]),
    (243643978215208, [15, 248, 3840, 4369, 17476, 61986]),
    (6145018120448, [15, 248, 3840, 4377, 8738, 17476]),
    (241094775983912, [15, 248, 3840, 8738, 17476, 61713]),
    (6144913797416, [15, 248, 3848, 4369, 8738, 17476]),
    (6155853373224, [15, 248, 4080, 4369, 8738, 17476]),
    (6156253670696, [15, 248, 4088, 4369, 8738, 17476]),
    (14443476798312, [15, 248, 4369, 8738, 17476, 20292]),
    (55696801780008, [15, 248, 4369, 8738, 17476, 36744]),
    (9106121572136, [15, 248, 4369, 8738, 20292]),
    (51804963381544, [15, 248, 4369, 8738, 20292, 34952]),
    (241034355556136, [15, 248, 4369, 8738, 20292, 61440]),
    (290568213577511, [15, 248, 4369, 8738, 20292, 65535]),
    (6144559350481, [15, 249, 3840, 4369, 8738, 17476]),
    (6144559915240, [15, 252, 3840, 4369, 8738, 17476]),
    (56151828099623, [15, 255, 4369, 8738, 17476, 36856]),
    (52216753242663, [15, 255, 4369, 8738, 20292, 35064]),
    (54258961556132, [15, 256, 3840, 8738, 21845, 35064]),
    (53847278270116, [15, 496, 3840, 8738, 21845, 34952]),
    (55696908550952, [15, 496, 4369, 8738, 17476, 36744]),
    (51805070152488, [15, 496, 4369, 8738, 20292, 34952]),
    (49206517378344, [15, 496, 7953, 8738, 17476, 34952]),
    (48588165840288, [15, 544, 3840, 4369, 17476, 35064]),
    (48599460048288, [15, 544, 4080, 4369, 17476, 35064]),
    (98595433446304, [15, 544, 4369, 17476, 35064, 36856]),
    (55697211786024, [15, 752, 4369, 8738, 17476, 36744]),
    (51805373387560, [15, 752, 4369, 8738, 20292, 34952]),
    (49876687576872, [15, 752, 4369, 12066, 17476, 34952]),
    (49199004135208, [15, 768, 4369, 8738, 17476, 35064]),
    (50783531467979, [15, 768, 4369, 13107, 17476, 35064]),
    (48787786810152, [15, 1008, 4369, 8738, 17476, 34952]),
    (50372314142923, [15, 1008, 4369, 13107, 17476, 34952]),
    (55708764078888, [15, 2288, 4369, 8738, 17476, 36744]),
    (6156647542568, [15, 2296, 3840, 4369, 8738, 17476]),
    (42133841260328, [15, 3840, 4369, 8738, 17476, 33016]),
    (49255174254376, [15, 3840, 4369, 8738, 17476, 35064]),
    (49258862811857, [15, 3840, 4369, 8738, 17476, 35065]),
    (49269929746664, [15, 3840, 4369, 8738, 17476, 35068]),
    (50206328680232, [15, 3840, 4369, 8738, 17476, 35320]),
    (51171371495208, [15, 3840, 4369, 8738, 17476, 35576]),
    (49256090538533, [15, 3840, 4369, 8738, 17477, 35064]),
    (49262507464104, [15, 3840, 4369, 8738, 17484, 35064]),
    (49269847387688, [15, 3840, 4369, 8738, 17492, 35064]),
    (49284547388712, [15, 3840, 4369, 8738, 17508, 35064])]

theorem o5_3 : okL 893 4 D4 D5_3 = true := by decide +kernel

def D5_4 : List (ℕ × List ℕ) :=
  [(49493182275368, [15, 3840, 4369, 8738, 17732, 35064]),
    (49738162802472, [15, 3840, 4369, 8738, 17988, 35064]),
    (53956374769448, [15, 3840, 4369, 8738, 21572, 35064]),
    (54342340954325, [15, 3840, 4369, 8738, 21845, 35064]),
    (60829083905832, [15, 3840, 4369, 8738, 25668, 35064]),
    (49255403338523, [15, 3840, 4369, 8739, 17476, 35064]),
    (49256090905592, [15, 3840, 4369, 8742, 17476, 35064]),
    (49257008396040, [15, 3840, 4369, 8746, 17476, 35064]),
    (49258156439855, [15, 3840, 4369, 8751, 17476, 35064]),
    (54345323139804, [15, 3840, 4369, 8751, 21845, 35064]),
    (49258845896168, [15, 3840, 4369, 8754, 17476, 35064]),
    (49269941596712, [15, 3840, 4369, 8802, 17476, 35064]),
    (49021039309608, [15, 3840, 4369, 8802, 17652, 34952]),
    (48921546027240, [15, 3840, 4369, 8946, 17508, 34952]),
    (49315547822888, [15, 3840, 4369, 8994, 17476, 35064]),
    (50701912960808, [15, 3840, 4369, 12834, 17476, 35064]),
    (50839701587147, [15, 3840, 4369, 13107, 17476, 35064]),
    (55926868287096, [15, 3840, 4369, 13107, 21845, 35064]),
    (50845891815263, [15, 3840, 4369, 13119, 17476, 35064]),
    (64442872966952, [15, 3840, 4369, 17476, 25122, 35064]),
    (49255403522084, [15, 3840, 4373, 8738, 17476, 35064]),
    (49255633209600, [15, 3840, 4377, 8738, 17476, 35064]),
    (54343145228803, [15, 3840, 4383, 8738, 21845, 35064]),
    (49257020172168, [15, 3840, 4401, 8738, 17476, 35064]),
    (48894018810696, [15, 3840, 4401, 8946, 17476, 34952]),
    (49258893129704, [15, 3840, 4433, 8738, 17476, 35064]),
    (49009990842600, [15, 3840, 4433, 8738, 17652, 34952]),
    (48871554995400, [15, 3840, 4593, 8738, 17492, 34952]),
    (54355837094773, [15, 3840, 4593, 8738, 21845, 35064]),
    (48860553503880, [15, 3840, 4593, 8754, 17476, 34952]),
    (50853197727595, [15, 3840, 4593, 13107, 17476, 35064]),
    (49288063808808, [15, 3840, 4881, 8738, 17476, 35064]),
    (51259334323915, [15, 3840, 7953, 13107, 17476, 35064]),
    (51153636593448, [15, 3840, 8738, 12561, 17476, 35064]),
    (56510641514959, [15, 3840, 8738, 13107, 21845, 35064]),
    (58109825576744, [15, 3840, 8738, 17476, 20753, 35064]),
    (115054756652077, [15, 3840, 8738, 21845, 35064, 39321]),
    (115501133303629, [15, 3840, 8738, 21845, 35064, 39417]),
    (289292557773013, [15, 3840, 8738, 21845, 35064, 61713]),
    (61180827337863, [15, 3840, 13107, 17476, 21845, 35064]),
    (111552117284899, [15, 3840, 13107, 17476, 35064, 39321]),
    (111998493936451, [15, 3840, 13107, 17476, 35064, 39417]),
    (285789918405835, [15, 3840, 13107, 17476, 35064, 61713]),
    (98542313921095, [15, 3840, 13107, 21845, 34952, 35064]),
    (55843472111687, [15, 3840, 13107, 21845, 35064]),
    (287771706095687, [15, 3840, 13107, 21845, 35064, 61440]),
    (337305564117062, [15, 3840, 13107, 21845, 35064, 65535]),
    (49255218502697, [15, 3841, 4369, 8738, 17476, 35064]),
    (49255351385960, [15, 3844, 4369, 8738, 17476, 35064]),
    (49255528886568, [15, 3848, 4369, 8738, 17476, 35064]),
    (49255884996392, [15, 3856, 4369, 8738, 17476, 35064]),
    (48857592604104, [15, 3856, 4593, 8738, 17476, 34952]),
    (49256601661224, [15, 3872, 4369, 8738, 17476, 35064]),
    (48893600299752, [15, 3872, 4369, 8946, 17476, 34952]),
    (49258052857640, [15, 3904, 4369, 8738, 17476, 35064]),
    (49261027405608, [15, 3968, 4369, 8738, 17476, 35064]),
    (49089665004328, [15, 4080, 4369, 8738, 17476, 35016]),
    (49266468462376, [15, 4080, 4369, 8738, 17476, 35064]),
    (67398026644945, [15, 4080, 4369, 8738, 17476, 39417]),
    (265069169352488, [15, 4080, 4369, 8738, 17476, 63736]),
    (54353635162325, [15, 4080, 4369, 8738, 21845, 35064]),
    (288444930268968, [15, 4080, 4369, 8738, 35064, 62532]),
    (49269450647855, [15, 4080, 4369, 8751, 17476, 35064]),
    (48869447271976, [15, 4080, 4369, 8802, 17476, 34952]),
    (50850995795147, [15, 4080, 4369, 13107, 17476, 35064]),
    (286765887512360, [15, 4080, 4369, 17476, 35064, 61986]),
    (48858398804968, [15, 4080, 4433, 8738, 17476, 34952]),
    (53955342770037, [15, 4080, 4593, 8738, 21845, 34952]),
    (50452703402859, [15, 4080, 4593, 13107, 17476, 34952]),
    (284216685281064, [15, 4080, 8738, 17476, 35064, 61713]),
    (56248703834105, [15, 4369, 4593, 8738, 17476, 36856]),
    (52313628977145, [15, 4369, 4593, 8738, 20292, 35064]),
    (56867768092784, [15, 4369, 8738, 8946, 17476, 36856]),
    (52932693235824, [15, 4369, 8738, 8946, 20292, 35064]),
    (57470372949800, [15, 4369, 8738, 17476, 20224, 35064]),
    (57554091887464, [15, 4369, 8738, 17476, 20292, 35064]),
    (57773395093608, [15, 4369, 8738, 17476, 20468, 35064]),
    (91659928863528, [15, 4369, 8738, 17476, 33008, 36744]),
    (98258603618088, [15, 4369, 8738, 17476, 35064, 36608]),
    (98807416869160, [15, 4369, 8738, 17476, 35064, 36744]),
    (99262441860392, [15, 4369, 8738, 17476, 35064, 36856]),
    (199733358823912, [15, 4369, 8738, 17476, 35064, 53196]),
    (200141219901160, [15, 4369, 8738, 17476, 35064, 53244]),
    (99288266181159, [15, 4369, 8738, 17476, 35071, 36856]),
    (117394000042961, [15, 4369, 8738, 17476, 36856, 39417]),
    (140006942151248, [15, 4369, 8738, 17476, 36856, 43770]),
    (290808585150248, [15, 4369, 8738, 17476, 36856, 61680]),
    (315065142750504, [15, 4369, 8738, 17476, 36856, 63736]),
    (57564176781591, [15, 4369, 8738, 17487, 20292, 35064]),
    (57716978133096, [15, 4369, 8738, 17652, 20292, 35064]),
    (62641258587413, [15, 4369, 8738, 20292, 21845, 35064]),
    (70230310549632, [15, 4369, 8738, 20292, 26214, 35064]),
    (87768090465064, [15, 4369, 8738, 20292, 33008, 34952]),
    (286873510293288, [15, 4369, 8738, 20292, 35064, 61680]),
    (296732553694056, [15, 4369, 8738, 20292, 35064, 62532]),
    (103894583569109, [15, 4369, 8738, 21845, 35064, 36744]),
    (104349608560341, [15, 4369, 8738, 21845, 35064, 36856]),
    (57557074072943, [15, 4369, 8751, 17476, 20292, 35064]),
    (98810399054639, [15, 4369, 8751, 17476, 35064, 36744]),
    (99265424045871, [15, 4369, 8751, 17476, 35064, 36856]),
    (59138619220235, [15, 4369, 13107, 17476, 20292, 35064]),
    (100391944201931, [15, 4369, 13107, 17476, 35064, 36744]),
    (100846969193163, [15, 4369, 13107, 17476, 35064, 36856])]

theorem o5_4 : okL 893 4 D4 D5_4 = true := by decide +kernel

def D5_5 : List (ℕ × List ℕ) :=
  [(55699782537216, [16, 240, 4369, 8751, 17476, 36744]),
    (51807944138752, [16, 240, 4369, 8751, 20292, 34952]),
    (49258156440576, [16, 3840, 4369, 8751, 17476, 35064]),
    (48859864048288, [16, 3840, 4593, 8751, 17476, 34952]),
    (55696800377432, [31, 240, 4369, 8738, 17476, 36744]),
    (51804961978968, [31, 240, 4369, 8738, 20292, 34952]),
    (49255174280792, [31, 3840, 4369, 8738, 17476, 35064]),
    (48856881888504, [31, 3840, 4593, 8738, 17476, 34952]),
    (55699782565888, [32, 240, 4369, 8751, 17476, 36744]),
    (51807944167424, [32, 240, 4369, 8751, 20292, 34952]),
    (49258156469248, [32, 3840, 4369, 8751, 17476, 35064]),
    (6147539982336, [40, 240, 3840, 4369, 8751, 17476]),
    (49258156500480, [40, 3840, 4369, 8751, 17476, 35064]),
    (55696800451464, [47, 240, 4369, 8738, 17476, 36744]),
    (51804962053000, [47, 240, 4369, 8738, 20292, 34952]),
    (49255174354824, [47, 3840, 4369, 8738, 17476, 35064]),
    (144918776061056, [64, 240, 3840, 4369, 8751, 52428]),
    (55699782795264, [64, 240, 4369, 8751, 17476, 36744]),
    (51807944396800, [64, 240, 4369, 8751, 20292, 34952]),
    (49258156698624, [64, 3840, 4369, 8751, 17476, 35064]),
    (49009254411520, [64, 3840, 4369, 8751, 17652, 34952]),
    (48857662373888, [64, 4080, 4369, 8751, 17476, 34952]),
    (43509026816000, [68, 240, 3840, 4369, 8751, 34952]),
    (144915794106472, [79, 240, 3840, 4369, 8738, 52428]),
    (55696800840680, [79, 240, 4369, 8738, 17476, 36744]),
    (51804962442216, [79, 240, 4369, 8738, 20292, 34952]),
    (49255174744040, [79, 3840, 4369, 8738, 17476, 35064]),
    (49006272456936, [79, 3840, 4369, 8738, 17652, 34952]),
    (48854680419304, [79, 4080, 4369, 8738, 17476, 34952]),
    (55699784630272, [128, 240, 4369, 8751, 17476, 36744]),
    (51807946231808, [128, 240, 4369, 8751, 20292, 34952]),
    (49258158533632, [128, 3840, 4369, 8751, 17476, 35064]),
    (6147542433792, [136, 240, 3840, 4369, 8751, 17476]),
    (6147555171328, [240, 248, 3840, 4369, 8751, 17476]),
    (6151907523960, [240, 255, 3840, 4369, 8738, 17484]),
    (6145033269456, [240, 255, 3840, 4377, 8738, 17476]),
    (6144928946424, [240, 255, 3848, 4369, 8738, 17476]),
    (55699799114495, [240, 255, 4369, 8751, 17476, 36744]),
    (51807960716031, [240, 255, 4369, 8751, 20292, 34952]),
    (53850169029500, [240, 256, 3840, 8751, 21845, 34952]),
    (55699799310336, [240, 256, 4369, 8751, 17476, 36744]),
    (51807960911872, [240, 256, 4369, 8751, 20292, 34952]),
    (49209408137728, [240, 256, 7953, 8751, 17476, 34952]),
    (53847189969316, [240, 271, 3840, 8738, 21845, 34952]),
    (55696820250152, [240, 271, 4369, 8738, 17476, 36744]),
    (51804981851688, [240, 271, 4369, 8738, 20292, 34952]),
    (49206429077544, [240, 271, 7953, 8738, 17476, 34952]),
    (55699916750848, [240, 512, 4369, 8751, 17476, 36744]),
    (51808078352384, [240, 512, 4369, 8751, 20292, 34952]),
    (51808081522752, [240, 516, 4369, 8751, 20292, 34952]),
    (6147680526336, [240, 520, 3840, 4369, 8751, 17476]),
    (55699923141120, [240, 520, 4369, 8751, 17476, 36744]),
    (55696946710824, [240, 527, 4369, 8738, 17476, 36744]),
    (51805108312360, [240, 527, 4369, 8738, 20292, 34952]),
    (48176404815872, [240, 559, 3840, 4369, 17476, 34952]),
    (48187699023872, [240, 559, 4080, 4369, 17476, 34952]),
    (48790211608576, [240, 768, 4369, 8751, 17476, 34952]),
    (55700856274944, [240, 1024, 4369, 8751, 17476, 36744]),
    (51809017876480, [240, 1024, 4369, 8751, 20292, 34952]),
    (55708372467712, [240, 2048, 4369, 8751, 17476, 36744]),
    (51816534069248, [240, 2048, 4369, 8751, 20292, 34952]),
    (6156230909952, [240, 2056, 3840, 4369, 8751, 17476]),
    (6204517654528, [240, 3840, 3848, 4369, 8751, 17476]),
    (6231395048969, [240, 3840, 4369, 4377, 8751, 17476]),
    (6822042531336, [240, 3840, 4369, 8738, 8751, 17484]),
    (48876392378664, [240, 3840, 4369, 8738, 17484, 34959]),
    (48868145821800, [240, 3840, 4369, 8738, 17487, 34956]),
    (11492228354240, [240, 3840, 4369, 8751, 17476, 17484]),
    (41357688102912, [240, 3840, 4369, 8751, 17476, 32776]),
    (48846381727744, [240, 3840, 4369, 8751, 17476, 34952]),
    (48850046759513, [240, 3840, 4369, 8751, 17476, 34953]),
    (48861043113152, [240, 3840, 4369, 8751, 17476, 34956]),
    (48905047405568, [240, 3840, 4369, 8751, 17476, 34968]),
    (48963766794240, [240, 3840, 4369, 8751, 17476, 34984]),
    (49081366802432, [240, 3840, 4369, 8751, 17476, 35016]),
    (49258170260480, [240, 3840, 4369, 8751, 17476, 35064]),
    (49791491637248, [240, 3840, 4369, 8751, 17476, 35208]),
    (50750445895680, [240, 3840, 4369, 8751, 17476, 35464]),
    (52710290112512, [240, 3840, 4369, 8751, 17476, 35976]),
    (55756405637120, [240, 3840, 4369, 8751, 17476, 36744]),
    (56211430628352, [240, 3840, 4369, 8751, 17476, 36856]),
    (65685833596928, [240, 3840, 4369, 8751, 17476, 39048]),
    (66943351791497, [240, 3840, 4369, 8751, 17476, 39321]),
    (67389728443049, [240, 3840, 4369, 8751, 17476, 39417]),
    (74349903221129, [240, 3840, 4369, 8751, 17476, 40857]),
    (141437658939392, [240, 3840, 4369, 8751, 17476, 51336]),
    (150256131025088, [240, 3840, 4369, 8751, 17476, 52428]),
    (150652305624512, [240, 3840, 4369, 8751, 17476, 52476]),
    (156682347591872, [240, 3840, 4369, 8751, 17476, 53196]),
    (189368937291909, [240, 3840, 4369, 8751, 17476, 56797]),
    (48847298011901, [240, 3840, 4369, 8751, 17477, 34952]),
    (6154873128064, [240, 3840, 4369, 8751, 17484]),
    (48853714937472, [240, 3840, 4369, 8751, 17484, 34952]),
    (238083107112064, [240, 3840, 4369, 8751, 17484, 61440]),
    (287616965133439, [240, 3840, 4369, 8751, 17484, 65535]),
    (150266215919215, [240, 3840, 4369, 8751, 17487, 52428]),
    (48861054861056, [240, 3840, 4369, 8751, 17492, 34952]),
    (48875754862080, [240, 3840, 4369, 8751, 17508, 34952]),
    (49084389748736, [240, 3840, 4369, 8751, 17732, 34952]),
    (49329370275840, [240, 3840, 4369, 8751, 17988, 34952]),
    (50951313211392, [240, 3840, 4369, 8751, 19524, 34952]),
    (51864567238656, [240, 3840, 4369, 8751, 20292, 34952]),
    (52276355771392, [240, 3840, 4369, 8751, 20292, 35064]),
    (58774591148032, [240, 3840, 4369, 8751, 20292, 36744]),
    (69961537302409, [240, 3840, 4369, 8751, 20292, 39321]),
    (153274316536000, [240, 3840, 4369, 8751, 20292, 52428])]

theorem o5_5 : okL 893 4 D4 D5_5 = true := by decide +kernel

def D5_6 : List (ℕ × List ℕ) :=
  [(159700533102784, [240, 3840, 4369, 8751, 20292, 53196]),
    (53547582242816, [240, 3840, 4369, 8751, 21572, 34952]),
    (53933548427693, [240, 3840, 4369, 8751, 21845, 34952]),
    (54345336960429, [240, 3840, 4369, 8751, 21845, 35064]),
    (60843572337069, [240, 3840, 4369, 8751, 21845, 36744]),
    (72030518491446, [240, 3840, 4369, 8751, 21845, 39321]),
    (155343297725037, [240, 3840, 4369, 8751, 21845, 52428]),
    (194456103991858, [240, 3840, 4369, 8751, 21845, 56797]),
    (58044742731693, [240, 3840, 4369, 8751, 24405, 34952]),
    (162932349687256, [240, 3840, 4369, 8751, 26214, 52428]),
    (162950909750479, [240, 3840, 4369, 8751, 26223, 52428]),
    (170347971428352, [240, 3840, 4369, 8751, 34952, 50244]),
    (389434592831680, [240, 3840, 4369, 8751, 52428, 62532]),
    (48850064292656, [240, 3840, 4369, 8767, 17476, 34952]),
    (48861192882368, [240, 3840, 4369, 8815, 17476, 34952]),
    (48906932462336, [240, 3840, 4369, 9007, 17476, 34952]),
    (48853713704100, [240, 3840, 4373, 8738, 17487, 34952]),
    (48846610995452, [240, 3840, 4373, 8751, 17476, 34952]),
    (6815168276832, [240, 3840, 4377, 8738, 8751, 17476]),
    (48869518124160, [240, 3840, 4377, 8738, 17476, 34959]),
    (6147998873560, [240, 3840, 4377, 8751, 17476]),
    (48846840682968, [240, 3840, 4377, 8751, 17476, 34952]),
    (238076232857560, [240, 3840, 4377, 8751, 17476, 61440]),
    (287610090878935, [240, 3840, 4377, 8751, 17476, 65535]),
    (48847868848512, [240, 3840, 4383, 8738, 17476, 34953]),
    (48845120100900, [240, 3840, 4383, 8738, 17477, 34952]),
    (66944156065975, [240, 3840, 4383, 8751, 17476, 39321]),
    (53934352702171, [240, 3840, 4383, 8751, 21845, 34952]),
    (48848227645536, [240, 3840, 4401, 8751, 17476, 34952]),
    (48850100603072, [240, 3840, 4433, 8751, 17476, 34952]),
    (53947044568141, [240, 3840, 4593, 8751, 21845, 34952]),
    (48879271282176, [240, 3840, 4881, 8751, 17476, 34952]),
    (72614291719309, [240, 3840, 8738, 8751, 21845, 39321]),
    (69111652352131, [240, 3840, 8751, 13107, 17476, 39321]),
    (56101848988327, [240, 3840, 8751, 13107, 21845, 34952]),
    (69117842580247, [240, 3840, 8751, 13119, 17476, 39321]),
    (56108039216443, [240, 3840, 8751, 13119, 21845, 34952]),
    (57701033050112, [240, 3840, 8751, 17476, 20753, 34952]),
    (77284477542213, [240, 3840, 8751, 17476, 21845, 39321]),
    (99980730482688, [240, 3840, 8751, 17476, 34952, 37137]),
    (301893568610185, [240, 3840, 8751, 17476, 39321, 61713]),
    (114645964125445, [240, 3840, 8751, 21845, 34952, 39321]),
    (288883765246381, [240, 3840, 8751, 21845, 34952, 61713]),
    (71947122316037, [240, 3840, 8751, 21845, 39321]),
    (303875356300037, [240, 3840, 8751, 21845, 39321, 61440]),
    (353409214321412, [240, 3840, 8751, 21845, 39321, 65535]),
    (48846425976065, [240, 3841, 4369, 8751, 17476, 34952]),
    (48844248065064, [240, 3841, 4383, 8738, 17476, 34952]),
    (48846558859328, [240, 3844, 4369, 8751, 17476, 34952]),
    (6815063953800, [240, 3848, 4369, 8738, 8751, 17476]),
    (6147894550528, [240, 3848, 4369, 8751, 17476]),
    (48846736359936, [240, 3848, 4369, 8751, 17476, 34952]),
    (238076128534528, [240, 3848, 4369, 8751, 17476, 61440]),
    (287609986555903, [240, 3848, 4369, 8751, 17476, 65535]),
    (55757071784495, [240, 3855, 4369, 8751, 17476, 36744]),
    (51865233386031, [240, 3855, 4369, 8751, 20292, 34952]),
    (48847092469760, [240, 3856, 4369, 8751, 17476, 34952]),
    (48847809134592, [240, 3872, 4369, 8751, 17476, 34952]),
    (48849260331008, [240, 3904, 4369, 8751, 17476, 34952]),
    (48852234878976, [240, 3968, 4369, 8751, 17476, 34952]),
    (48857675935744, [240, 4080, 4369, 8751, 17476, 34952]),
    (49269464468480, [240, 4080, 4369, 8751, 17476, 35064]),
    (55767699845120, [240, 4080, 4369, 8751, 17476, 36744]),
    (56222724836352, [240, 4080, 4369, 8751, 17476, 36856]),
    (66954645999497, [240, 4080, 4369, 8751, 17476, 39321]),
    (150267425233088, [240, 4080, 4369, 8751, 17476, 52428]),
    (51875861446656, [240, 4080, 4369, 8751, 20292, 34952]),
    (53944842635693, [240, 4080, 4369, 8751, 21845, 34952]),
    (55768502009856, [240, 4096, 4369, 8751, 17476, 36744]),
    (51876663611392, [240, 4096, 4369, 8751, 20292, 34952]),
    (55783982983007, [240, 4369, 4383, 8751, 17476, 36744]),
    (51892144584543, [240, 4369, 4383, 8751, 20292, 34952]),
    (55796674848977, [240, 4369, 4593, 8751, 17476, 36744]),
    (51904836450513, [240, 4369, 4593, 8751, 20292, 34952]),
    (56202811445297, [240, 4369, 7953, 8751, 17476, 36744]),
    (52310973046833, [240, 4369, 7953, 8751, 20292, 34952]),
    (56249538347008, [240, 4369, 8192, 8751, 17476, 36744]),
    (52357699948544, [240, 4369, 8192, 8751, 20292, 34952]),
    (56249581593384, [240, 4369, 8207, 8738, 17476, 36744]),
    (52357743194920, [240, 4369, 8207, 8738, 20292, 34952]),
    (56366951936392, [240, 4369, 8738, 8751, 17476, 36744]),
    (56821976927624, [240, 4369, 8738, 8751, 17476, 36856]),
    (157292893891144, [240, 4369, 8738, 8751, 17476, 53196]),
    (52475113537928, [240, 4369, 8738, 8751, 20292, 34952]),
    (52886902070664, [240, 4369, 8738, 8751, 20292, 35064]),
    (59385137447304, [240, 4369, 8738, 8751, 20292, 36744]),
    (70572083601681, [240, 4369, 8738, 8751, 20292, 39321]),
    (153884862835272, [240, 4369, 8738, 8751, 20292, 52428]),
    (160311079402056, [240, 4369, 8738, 8751, 20292, 53196]),
    (61454118636341, [240, 4369, 8738, 8751, 21845, 36744]),
    (56415739107656, [240, 4369, 8751, 8946, 17476, 36744]),
    (52523900709192, [240, 4369, 8751, 8946, 20292, 34952]),
    (56418864851199, [240, 4369, 8751, 8959, 17476, 36744]),
    (52527026452735, [240, 4369, 8751, 8959, 20292, 34952]),
    (57456451636616, [240, 4369, 8751, 12066, 17476, 36744]),
    (53564613238152, [240, 4369, 8751, 12066, 20292, 34952]),
    (57462135702159, [240, 4369, 8751, 12079, 17476, 36744]),
    (53570297303695, [240, 4369, 8751, 12079, 20292, 34952]),
    (57951479269163, [240, 4369, 8751, 13107, 17476, 36744]),
    (54059640870699, [240, 4369, 8751, 13107, 20292, 34952]),
    (57957669497279, [240, 4369, 8751, 13119, 17476, 36744]),
    (54065831098815, [240, 4369, 8751, 13119, 20292, 34952]),
    (60097829044224, [240, 4369, 8751, 16384, 17476, 36744]),
    (56205990645760, [240, 4369, 8751, 16384, 20292, 34952])]

theorem o5_6 : okL 893 4 D4 D5_6 = true := by decide +kernel

def D5_7 : List (ℕ × List ℕ) :=
  [(61047222653423, [240, 4369, 8751, 17476, 17487, 36744]),
    (61200024004928, [240, 4369, 8751, 17476, 17652, 36744]),
    (57061580423168, [240, 4369, 8751, 17476, 20224, 34952]),
    (57145299360832, [240, 4369, 8751, 17476, 20292, 34952]),
    (57557087893568, [240, 4369, 8751, 17476, 20292, 35064]),
    (64055323270208, [240, 4369, 8751, 17476, 20292, 36744]),
    (75242269424585, [240, 4369, 8751, 17476, 20292, 39321]),
    (158555048658176, [240, 4369, 8751, 17476, 20292, 52428]),
    (164981265224960, [240, 4369, 8751, 17476, 20292, 53196]),
    (57364602566976, [240, 4369, 8751, 17476, 20468, 34952]),
    (66124304459245, [240, 4369, 8751, 17476, 21845, 36744]),
    (73713356421464, [240, 4369, 8751, 17476, 26214, 36744]),
    (73731916484687, [240, 4369, 8751, 17476, 26223, 36744]),
    (90884154621952, [240, 4369, 8751, 17476, 32768, 36744]),
    (97849811091456, [240, 4369, 8751, 17476, 34952, 36608]),
    (98398624342528, [240, 4369, 8751, 17476, 34952, 36744]),
    (98853649333760, [240, 4369, 8751, 17476, 34952, 36856]),
    (199324566297280, [240, 4369, 8751, 17476, 34952, 53196]),
    (98424283969199, [240, 4369, 8751, 17476, 34959, 36744]),
    (98810412875264, [240, 4369, 8751, 17476, 35064, 36744]),
    (99265437866496, [240, 4369, 8751, 17476, 35064, 36856]),
    (55699782533120, [240, 4369, 8751, 17476, 36744]),
    (105337006205871, [240, 4369, 8751, 17476, 36744, 36751]),
    (105763673243136, [240, 4369, 8751, 17476, 36744, 36856]),
    (116495594406281, [240, 4369, 8751, 17476, 36744, 39321]),
    (123902145835913, [240, 4369, 8751, 17476, 36744, 40857]),
    (139095957942120, [240, 4369, 8751, 17476, 36744, 43690]),
    (139124593460495, [240, 4369, 8751, 17476, 36744, 43695]),
    (146642654006120, [240, 4369, 8751, 17476, 36744, 44970]),
    (146672991892495, [240, 4369, 8751, 17476, 36744, 44975]),
    (199808373639872, [240, 4369, 8751, 17476, 36744, 52428]),
    (206234590206656, [240, 4369, 8751, 17476, 36744, 53196]),
    (287628016517120, [240, 4369, 8751, 17476, 36744, 61440]),
    (287797927304495, [240, 4369, 8751, 17476, 36744, 61455]),
    (290356556165120, [240, 4369, 8751, 17476, 36744, 61680]),
    (290733395527217, [240, 4369, 8751, 17476, 36744, 61713]),
    (293866370986376, [240, 4369, 8751, 17476, 36744, 61986]),
    (294016250719119, [240, 4369, 8751, 17476, 36744, 61999]),
    (300215599565888, [240, 4369, 8751, 17476, 36744, 62532]),
    (313250585567744, [240, 4369, 8751, 17476, 36744, 63624]),
    (333889092485120, [240, 4369, 8751, 17476, 36744, 65280]),
    (335631400444416, [240, 4369, 8751, 17476, 36744, 65416]),
    (337161874538495, [240, 4369, 8751, 17476, 36744, 65535]),
    (56154807524352, [240, 4369, 8751, 17476, 36856]),
    (288083041508352, [240, 4369, 8751, 17476, 36856, 61440]),
    (337616899529727, [240, 4369, 8751, 17476, 36856, 65535]),
    (300734315594624, [240, 4369, 8751, 17476, 52428, 53196]),
    (156625724487872, [240, 4369, 8751, 17476, 53196]),
    (388553958471872, [240, 4369, 8751, 17476, 53196, 61440]),
    (438087816493247, [240, 4369, 8751, 17476, 53196, 65535]),
    (57155384254959, [240, 4369, 8751, 17487, 20292, 34952]),
    (57308185606464, [240, 4369, 8751, 17652, 20292, 34952]),
    (60177080492783, [240, 4369, 8751, 20292, 20303, 34952]),
    (60382788077888, [240, 4369, 8751, 20292, 20468, 34952]),
    (62232466060781, [240, 4369, 8751, 20292, 21845, 34952]),
    (66343660364781, [240, 4369, 8751, 20292, 24405, 34952]),
    (69821518023000, [240, 4369, 8751, 20292, 26214, 34952]),
    (69840078086223, [240, 4369, 8751, 20292, 26223, 34952]),
    (75000958342488, [240, 4369, 8751, 20292, 28518, 34952]),
    (75022923733839, [240, 4369, 8751, 20292, 28527, 34952]),
    (86992316223488, [240, 4369, 8751, 20292, 32768, 34952]),
    (51807944134656, [240, 4369, 8751, 20292, 34952]),
    (94532445570735, [240, 4369, 8751, 20292, 34952, 34959]),
    (94918574476800, [240, 4369, 8751, 20292, 34952, 35064]),
    (101416809853440, [240, 4369, 8751, 20292, 34952, 36744]),
    (112603756007817, [240, 4369, 8751, 20292, 34952, 39321]),
    (135204119543656, [240, 4369, 8751, 20292, 34952, 43690]),
    (135232755062031, [240, 4369, 8751, 20292, 34952, 43695]),
    (195916535241408, [240, 4369, 8751, 20292, 34952, 52428]),
    (202342751808192, [240, 4369, 8751, 20292, 34952, 53196]),
    (283736178118656, [240, 4369, 8751, 20292, 34952, 61440]),
    (283906088906031, [240, 4369, 8751, 20292, 34952, 61455]),
    (286464717766656, [240, 4369, 8751, 20292, 34952, 61680]),
    (286841557128753, [240, 4369, 8751, 20292, 34952, 61713]),
    (289974532587912, [240, 4369, 8751, 20292, 34952, 61986]),
    (290124412320655, [240, 4369, 8751, 20292, 34952, 61999]),
    (296323761167424, [240, 4369, 8751, 20292, 34952, 62532]),
    (309358747169280, [240, 4369, 8751, 20292, 34952, 63624]),
    (329997254086656, [240, 4369, 8751, 20292, 34952, 65280]),
    (330867501558848, [240, 4369, 8751, 20292, 34952, 65348]),
    (333270036140031, [240, 4369, 8751, 20292, 34952, 65535]),
    (52219732667392, [240, 4369, 8751, 20292, 35064]),
    (284147966651392, [240, 4369, 8751, 20292, 35064, 61440]),
    (333681824672767, [240, 4369, 8751, 20292, 35064, 65535]),
    (58717968044032, [240, 4369, 8751, 20292, 36744]),
    (290646202028032, [240, 4369, 8751, 20292, 36744, 61440]),
    (340180060049407, [240, 4369, 8751, 20292, 36744, 65535]),
    (69904914198409, [240, 4369, 8751, 20292, 39321]),
    (301833148182409, [240, 4369, 8751, 20292, 39321, 61440]),
    (351367006203784, [240, 4369, 8751, 20292, 39321, 65535]),
    (153217693432000, [240, 4369, 8751, 20292, 52428]),
    (385145927416000, [240, 4369, 8751, 20292, 52428, 61440]),
    (434679785437375, [240, 4369, 8751, 20292, 52428, 65535]),
    (159643909998784, [240, 4369, 8751, 20292, 53196]),
    (391572143982784, [240, 4369, 8751, 20292, 53196, 61440]),
    (441106002004159, [240, 4369, 8751, 20292, 53196, 65535]),
    (103485791042477, [240, 4369, 8751, 21845, 34952, 36744]),
    (60786949233069, [240, 4369, 8751, 21845, 36744]),
    (292715183217069, [240, 4369, 8751, 21845, 36744, 61440]),
    (342249041238444, [240, 4369, 8751, 21845, 36744, 65535]),
    (48846381901265, [241, 3840, 4369, 8751, 17476, 34952]),
    (48844203990264, [241, 3840, 4383, 8738, 17476, 34952])]

theorem o5_7 : okL 893 4 D4 D5_7 = true := by decide +kernel

def D5_8 : List (ℕ × List ℕ) :=
  [(48853485139176, [244, 3840, 4369, 8738, 17487, 34952]),
    (48846382430528, [244, 3840, 4369, 8751, 17476, 34952]),
    (6814710750600, [248, 3840, 4369, 8738, 8751, 17476]),
    (6147541347328, [248, 3840, 4369, 8751, 17476]),
    (48846383156736, [248, 3840, 4369, 8751, 17476, 34952]),
    (238075775331328, [248, 3840, 4369, 8751, 17476, 61440]),
    (287609633352703, [248, 3840, 4369, 8751, 17476, 65535]),
    (49258173017855, [255, 3840, 4369, 8751, 17476, 35064]),
    (48857678693119, [255, 4080, 4369, 8751, 17476, 34952]),
    (49258173213696, [256, 3840, 4369, 8751, 17476, 35064]),
    (49255194153512, [271, 3840, 4369, 8738, 17476, 35064]),
    (48846489927680, [496, 3840, 4369, 8751, 17476, 34952]),
    (49258290654208, [512, 3840, 4369, 8751, 17476, 35064]),
    (49255320614184, [527, 3840, 4369, 8738, 17476, 35064]),
    (48846793162752, [752, 3840, 4369, 8751, 17476, 34952]),
    (49259230178304, [1024, 3840, 4369, 8751, 17476, 35064]),
    (49266746371072, [2048, 3840, 4369, 8751, 17476, 35064]),
    (48858345455616, [2288, 3840, 4369, 8751, 17476, 34952]),
    (49315445687855, [3840, 3855, 4369, 8751, 17476, 35064]),
    (49326073748480, [3840, 4080, 4369, 8751, 17476, 35064]),
    (49326875913216, [3840, 4096, 4369, 8751, 17476, 35064]),
    (49342356886367, [3840, 4369, 4383, 8751, 17476, 35064]),
    (49355048752337, [3840, 4369, 4593, 8751, 17476, 35064]),
    (49761185348657, [3840, 4369, 7953, 8751, 17476, 35064]),
    (49807912250368, [3840, 4369, 8192, 8751, 17476, 35064]),
    (49807955496744, [3840, 4369, 8207, 8738, 17476, 35064]),
    (49925325839752, [3840, 4369, 8738, 8751, 17476, 35064]),
    (55012492539701, [3840, 4369, 8738, 8751, 21845, 35064]),
    (49974113011016, [3840, 4369, 8751, 8946, 17476, 35064]),
    (49977238754559, [3840, 4369, 8751, 8959, 17476, 35064]),
    (51014825539976, [3840, 4369, 8751, 12066, 17476, 35064]),
    (51020509605519, [3840, 4369, 8751, 12079, 17476, 35064]),
    (51509853172523, [3840, 4369, 8751, 13107, 17476, 35064]),
    (51516043400639, [3840, 4369, 8751, 13119, 17476, 35064]),
    (53656202947584, [3840, 4369, 8751, 16384, 17476, 35064]),
    (54605596556783, [3840, 4369, 8751, 17476, 17487, 35064]),
    (54758397908288, [3840, 4369, 8751, 17476, 17652, 35064]),
    (57613697173568, [3840, 4369, 8751, 17476, 20292, 35064]),
    (59682678362605, [3840, 4369, 8751, 17476, 21845, 35064]),
    (67271730324824, [3840, 4369, 8751, 17476, 26214, 35064]),
    (67290290388047, [3840, 4369, 8751, 17476, 26223, 35064]),
    (84442528525312, [3840, 4369, 8751, 17476, 32768, 35064]),
    (84809510240256, [3840, 4369, 8751, 17476, 33008, 34952]),
    (91956998245888, [3840, 4369, 8751, 17476, 34952, 35064]),
    (91982657872559, [3840, 4369, 8751, 17476, 34959, 35064]),
    (49258156436480, [3840, 4369, 8751, 17476, 35064]),
    (92394611099391, [3840, 4369, 8751, 17476, 35064, 35071]),
    (98867022155264, [3840, 4369, 8751, 17476, 35064, 36744]),
    (99322047146496, [3840, 4369, 8751, 17476, 35064, 36856]),
    (110053968309641, [3840, 4369, 8751, 17476, 35064, 39321]),
    (110500344961193, [3840, 4369, 8751, 17476, 35064, 39417]),
    (132654331845480, [3840, 4369, 8751, 17476, 35064, 43690]),
    (132682967363855, [3840, 4369, 8751, 17476, 35064, 43695]),
    (133113287069480, [3840, 4369, 8751, 17476, 35064, 43770]),
    (133142027545855, [3840, 4369, 8751, 17476, 35064, 43775]),
    (193366747543232, [3840, 4369, 8751, 17476, 35064, 52428]),
    (193762922142656, [3840, 4369, 8751, 17476, 35064, 52476]),
    (281186390420480, [3840, 4369, 8751, 17476, 35064, 61440]),
    (281356301207855, [3840, 4369, 8751, 17476, 35064, 61455]),
    (283914930068480, [3840, 4369, 8751, 17476, 35064, 61680]),
    (284291769430577, [3840, 4369, 8751, 17476, 35064, 61713]),
    (287424744889736, [3840, 4369, 8751, 17476, 35064, 61986]),
    (287574624622479, [3840, 4369, 8751, 17476, 35064, 61999]),
    (293773973469248, [3840, 4369, 8751, 17476, 35064, 62532]),
    (306808959471104, [3840, 4369, 8751, 17476, 35064, 63624]),
    (308171487668736, [3840, 4369, 8751, 17476, 35064, 63736]),
    (327447466388480, [3840, 4369, 8751, 17476, 35064, 65280]),
    (330720248441855, [3840, 4369, 8751, 17476, 35064, 65535]),
    (97044164945837, [3840, 4369, 8751, 21845, 34952, 35064]),
    (54345323136429, [3840, 4369, 8751, 21845, 35064]),
    (286273557120429, [3840, 4369, 8751, 21845, 35064, 61440]),
    (335807415141804, [3840, 4369, 8751, 21845, 35064, 65535]),
    (48954554427601, [4080, 4369, 4593, 8751, 17476, 34952]),
    (49936620047752, [4080, 4369, 8738, 8751, 17476, 35064]),
    (49573618686280, [4080, 4369, 8751, 8946, 17476, 34952]),
    (49576744429823, [4080, 4369, 8751, 8959, 17476, 34952]),
    (91968292453888, [4080, 4369, 8751, 17476, 34952, 35064]),
    (283514435743744, [4080, 4369, 8751, 17476, 34952, 61680]),
    (49269450644480, [4080, 4369, 8751, 17476, 35064]),
    (281197684628480, [4080, 4369, 8751, 17476, 35064, 61440]),
    (330731542649855, [4080, 4369, 8751, 17476, 35064, 65535]),
    (58224243472840, [4369, 8738, 8751, 17476, 20292, 35064]),
    (99477568454536, [4369, 8738, 8751, 17476, 35064, 36744]),
    (99932593445768, [4369, 8738, 8751, 17476, 35064, 36856]),
    (100255915878976, [4369, 8751, 17476, 20292, 34952, 35064]),
    (57557074069568, [4369, 8751, 17476, 20292, 35064]),
    (289485308053568, [4369, 8751, 17476, 20292, 35064, 61440]),
    (339019166074943, [4369, 8751, 17476, 20292, 35064, 65535]),
    (141509240860672, [4369, 8751, 17476, 34952, 35064, 36744]),
    (141964265851904, [4369, 8751, 17476, 34952, 35064, 36856]),
    (98810399051264, [4369, 8751, 17476, 35064, 36744]),
    (330738633035264, [4369, 8751, 17476, 35064, 36744, 61440]),
    (380272491056639, [4369, 8751, 17476, 35064, 36744, 65535]),
    (99265424042496, [4369, 8751, 17476, 35064, 36856]),
    (331193658026496, [4369, 8751, 17476, 35064, 36856, 61440]),
    (380727516047871, [4369, 8751, 17476, 35064, 36856, 65535])]

theorem o5_8 : okL 893 4 D4 D5_8 = true := by decide +kernel

def D5 : List (ℕ × List ℕ) := D5_0 ++ D5_1 ++ D5_2 ++ D5_3 ++ D5_4 ++ D5_5 ++ D5_6 ++ D5_7 ++ D5_8

theorem t5 : Dead 893 5 D5 :=
  dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (okL_sound _ _ _ _ t4 o5_0) (okL_sound _ _ _ _ t4 o5_1)) (okL_sound _ _ _ _ t4 o5_2)) (okL_sound _ _ _ _ t4 o5_3)) (okL_sound _ _ _ _ t4 o5_4)) (okL_sound _ _ _ _ t4 o5_5)) (okL_sound _ _ _ _ t4 o5_6)) (okL_sound _ _ _ _ t4 o5_7)) (okL_sound _ _ _ _ t4 o5_8)

def D6_0 : List (ℕ × List ℕ) :=
  [(9106120143656, [0, 8, 15, 240, 4369, 8738, 20292]),
    (6147539918848, [0, 8, 240, 3840, 4369, 8751, 17476]),
    (6151890945960, [0, 15, 240, 3840, 4369, 8738, 17484]),
    (6145016691456, [0, 15, 240, 3840, 4377, 8738, 17476]),
    (71944140133933, [0, 15, 240, 3840, 8738, 21845, 39321]),
    (68441500766755, [0, 15, 240, 3840, 13107, 17476, 39321]),
    (55431697402951, [0, 15, 240, 3840, 13107, 21845, 34952]),
    (6144912368424, [0, 15, 240, 3848, 4369, 8738, 17476]),
    (55696800351016, [0, 15, 240, 4369, 8738, 17476, 36744]),
    (56151825342248, [0, 15, 240, 4369, 8738, 17476, 36856]),
    (156622742305768, [0, 15, 240, 4369, 8738, 17476, 53196]),
    (51804961952552, [0, 15, 240, 4369, 8738, 20292, 34952]),
    (52216750485288, [0, 15, 240, 4369, 8738, 20292, 35064]),
    (58714985861928, [0, 15, 240, 4369, 8738, 20292, 36744]),
    (69901932016305, [0, 15, 240, 4369, 8738, 20292, 39321]),
    (153214711249896, [0, 15, 240, 4369, 8738, 20292, 52428]),
    (159640927816680, [0, 15, 240, 4369, 8738, 20292, 53196]),
    (266656923177768, [0, 15, 240, 4369, 8738, 20292, 63624]),
    (60783967050965, [0, 15, 240, 4369, 8738, 21845, 36744]),
    (294875262157608, [0, 15, 240, 4369, 8738, 36744, 62532]),
    (55699782536495, [0, 15, 240, 4369, 8751, 17476, 36744]),
    (51807944138031, [0, 15, 240, 4369, 8751, 20292, 34952]),
    (57281327683787, [0, 15, 240, 4369, 13107, 17476, 36744]),
    (53389489285323, [0, 15, 240, 4369, 13107, 20292, 34952]),
    (6144559165224, [0, 15, 248, 3840, 4369, 8738, 17476]),
    (49255174254376, [0, 15, 3840, 4369, 8738, 17476, 35064]),
    (54342340954325, [0, 15, 3840, 4369, 8738, 21845, 35064]),
    (49258156439855, [0, 15, 3840, 4369, 8751, 17476, 35064]),
    (50839701587147, [0, 15, 3840, 4369, 13107, 17476, 35064]),
    (49266468462376, [0, 15, 4080, 4369, 8738, 17476, 35064]),
    (57554091887464, [0, 15, 4369, 8738, 17476, 20292, 35064]),
    (98807416869160, [0, 15, 4369, 8738, 17476, 35064, 36744]),
    (99262441860392, [0, 15, 4369, 8738, 17476, 35064, 36856]),
    (48846381727744, [0, 240, 3840, 4369, 8751, 17476, 34952]),
    (49258170260480, [0, 240, 3840, 4369, 8751, 17476, 35064]),
    (55756405637120, [0, 240, 3840, 4369, 8751, 17476, 36744]),
    (66943351791497, [0, 240, 3840, 4369, 8751, 17476, 39321]),
    (150256131025088, [0, 240, 3840, 4369, 8751, 17476, 52428]),
    (51864567238656, [0, 240, 3840, 4369, 8751, 20292, 34952]),
    (53933548427693, [0, 240, 3840, 4369, 8751, 21845, 34952]),
    (48857675935744, [0, 240, 4080, 4369, 8751, 17476, 34952]),
    (56366951936392, [0, 240, 4369, 8738, 8751, 17476, 36744]),
    (52475113537928, [0, 240, 4369, 8738, 8751, 20292, 34952]),
    (57145299360832, [0, 240, 4369, 8751, 17476, 20292, 34952]),
    (98398624342528, [0, 240, 4369, 8751, 17476, 34952, 36744]),
    (55699782533120, [0, 240, 4369, 8751, 17476, 36744]),
    (287628016517120, [0, 240, 4369, 8751, 17476, 36744, 61440]),
    (337161874538495, [0, 240, 4369, 8751, 17476, 36744, 65535]),
    (51807944134656, [0, 240, 4369, 8751, 20292, 34952]),
    (283736178118656, [0, 240, 4369, 8751, 20292, 34952, 61440]),
    (333270036140031, [0, 240, 4369, 8751, 20292, 34952, 65535]),
    (49925325839752, [0, 3840, 4369, 8738, 8751, 17476, 35064]),
    (91956998245888, [0, 3840, 4369, 8751, 17476, 34952, 35064]),
    (49258156436480, [0, 3840, 4369, 8751, 17476, 35064]),
    (281186390420480, [0, 3840, 4369, 8751, 17476, 35064, 61440]),
    (330720248441855, [0, 3840, 4369, 8751, 17476, 35064, 65535]),
    (50344530703003, [1, 15, 240, 3840, 13107, 17476, 34952]),
    (55696800351017, [1, 15, 240, 4369, 8738, 17476, 36744]),
    (51804961952553, [1, 15, 240, 4369, 8738, 20292, 34952]),
    (49255174254377, [1, 15, 3840, 4369, 8738, 17476, 35064]),
    (48846381727745, [1, 240, 3840, 4369, 8751, 17476, 34952]),
    (48844203816744, [1, 240, 3840, 4383, 8738, 17476, 34952]),
    (55696800351024, [2, 15, 240, 4369, 8738, 17476, 36744]),
    (51804961952560, [2, 15, 240, 4369, 8738, 20292, 34952]),
    (49255174254384, [2, 15, 3840, 4369, 8738, 17476, 35064]),
    (48846381727752, [2, 240, 3840, 4369, 8751, 17476, 34952]),
    (55696800351080, [4, 15, 240, 4369, 8738, 17476, 36744]),
    (51804961952616, [4, 15, 240, 4369, 8738, 20292, 34952]),
    (49255174254440, [4, 15, 3840, 4369, 8738, 17476, 35064]),
    (48853484436456, [4, 240, 3840, 4369, 8738, 17487, 34952]),
    (48846381727808, [4, 240, 3840, 4369, 8751, 17476, 34952]),
    (6144557736744, [8, 15, 240, 3840, 4369, 8738, 17476]),
    (6151890946472, [8, 15, 240, 3840, 4369, 8738, 17484]),
    (9162743247656, [8, 15, 240, 3840, 4369, 8738, 20292]),
    (11231724436693, [8, 15, 240, 3840, 4369, 8738, 21845]),
    (245323019543336, [8, 15, 240, 3840, 4369, 8738, 62532]),
    (6146391878408, [8, 15, 240, 3840, 4369, 8746, 17476]),
    (6147539922223, [8, 15, 240, 3840, 4369, 8751, 17476]),
    (7729085069515, [8, 15, 240, 3840, 4369, 13107, 17476]),
    (243643976786728, [8, 15, 240, 3840, 4369, 17476, 61986]),
    (6145016691968, [8, 15, 240, 3840, 4377, 8738, 17476]),
    (241094774555432, [8, 15, 240, 3840, 8738, 17476, 61713]),
    (6144912368936, [8, 15, 240, 3848, 4369, 8738, 17476]),
    (6155851944744, [8, 15, 240, 4080, 4369, 8738, 17476]),
    (14443475369832, [8, 15, 240, 4369, 8738, 17476, 20292]),
    (55696800351528, [8, 15, 240, 4369, 8738, 17476, 36744]),
    (9106120143656, [8, 15, 240, 4369, 8738, 20292]),
    (51804961953064, [8, 15, 240, 4369, 8738, 20292, 34952]),
    (241034354127656, [8, 15, 240, 4369, 8738, 20292, 61440]),
    (290568212149031, [8, 15, 240, 4369, 8738, 20292, 65535]),
    (6144559165736, [8, 15, 248, 3840, 4369, 8738, 17476]),
    (49255174254888, [8, 15, 3840, 4369, 8738, 17476, 35064]),
    (6144574314744, [8, 240, 255, 3840, 4369, 8738, 17476]),
    (6814709322120, [8, 240, 3840, 4369, 8738, 8751, 17476]),
    (48869059169448, [8, 240, 3840, 4369, 8738, 17476, 34959])]

theorem o6_0 : okL 893 5 D5 D6_0 = true := by decide +kernel

def D6_1 : List (ℕ × List ℕ) :=
  [(6147539918848, [8, 240, 3840, 4369, 8751, 17476]),
    (48846381728256, [8, 240, 3840, 4369, 8751, 17476, 34952]),
    (238075773902848, [8, 240, 3840, 4369, 8751, 17476, 61440]),
    (287609631924223, [8, 240, 3840, 4369, 8751, 17476, 65535]),
    (6144557736961, [9, 15, 240, 3840, 4369, 8738, 17476]),
    (6144557737960, [12, 15, 240, 3840, 4369, 8738, 17476]),
    (55696800355112, [15, 16, 240, 4369, 8738, 17476, 36744]),
    (51804961956648, [15, 16, 240, 4369, 8738, 20292, 34952]),
    (49255174258472, [15, 16, 3840, 4369, 8738, 17476, 35064]),
    (48856881866184, [15, 16, 3840, 4593, 8738, 17476, 34952]),
    (55696800383784, [15, 32, 240, 4369, 8738, 17476, 36744]),
    (51804961985320, [15, 32, 240, 4369, 8738, 20292, 34952]),
    (49255174287144, [15, 32, 3840, 4369, 8738, 17476, 35064]),
    (48892172925672, [15, 32, 3840, 4369, 8946, 17476, 34952]),
    (144915793878952, [15, 64, 240, 3840, 4369, 8738, 52428]),
    (55696800613160, [15, 64, 240, 4369, 8738, 17476, 36744]),
    (51804962214696, [15, 64, 240, 4369, 8738, 20292, 34952]),
    (49255174516520, [15, 64, 3840, 4369, 8738, 17476, 35064]),
    (49006272229416, [15, 64, 3840, 4369, 8738, 17652, 34952]),
    (48854680191784, [15, 64, 4080, 4369, 8738, 17476, 34952]),
    (43506044633896, [15, 68, 240, 3840, 4369, 8738, 34952]),
    (55696802448168, [15, 128, 240, 4369, 8738, 17476, 36744]),
    (51804964049704, [15, 128, 240, 4369, 8738, 20292, 34952]),
    (49255176351528, [15, 128, 3840, 4369, 8738, 17476, 35064]),
    (6144560251688, [15, 136, 240, 3840, 4369, 8738, 17476]),
    (6144572989224, [15, 240, 248, 3840, 4369, 8738, 17476]),
    (55696816932391, [15, 240, 255, 4369, 8738, 17476, 36744]),
    (51804978533927, [15, 240, 255, 4369, 8738, 20292, 34952]),
    (53847186847396, [15, 240, 256, 3840, 8738, 21845, 34952]),
    (55696817128232, [15, 240, 256, 4369, 8738, 17476, 36744]),
    (51804978729768, [15, 240, 256, 4369, 8738, 20292, 34952]),
    (49206425955624, [15, 240, 256, 7953, 8738, 17476, 34952]),
    (55696934568744, [15, 240, 512, 4369, 8738, 17476, 36744]),
    (51805096170280, [15, 240, 512, 4369, 8738, 20292, 34952]),
    (49876410359592, [15, 240, 512, 4369, 12066, 17476, 34952]),
    (48176391131552, [15, 240, 544, 3840, 4369, 17476, 34952]),
    (48187685339552, [15, 240, 544, 4080, 4369, 17476, 34952]),
    (48787229426472, [15, 240, 768, 4369, 8738, 17476, 34952]),
    (50371756759243, [15, 240, 768, 4369, 13107, 17476, 34952]),
    (55697874092840, [15, 240, 1024, 4369, 8738, 17476, 36744]),
    (51806035694376, [15, 240, 1024, 4369, 8738, 20292, 34952]),
    (55705390285608, [15, 240, 2048, 4369, 8738, 17476, 36744]),
    (51813551887144, [15, 240, 2048, 4369, 8738, 20292, 34952]),
    (6153248727848, [15, 240, 2056, 3840, 4369, 8738, 17476]),
    (6201535472424, [15, 240, 3840, 3848, 4369, 8738, 17476]),
    (6228412866865, [15, 240, 3840, 4369, 4377, 8738, 17476]),
    (11489246172136, [15, 240, 3840, 4369, 8738, 17476, 17484]),
    (41354705920808, [15, 240, 3840, 4369, 8738, 17476, 32776]),
    (48843399545640, [15, 240, 3840, 4369, 8738, 17476, 34952]),
    (48847064577409, [15, 240, 3840, 4369, 8738, 17476, 34953]),
    (48858060931048, [15, 240, 3840, 4369, 8738, 17476, 34956]),
    (48902065223464, [15, 240, 3840, 4369, 8738, 17476, 34968]),
    (48960784612136, [15, 240, 3840, 4369, 8738, 17476, 34984]),
    (49078384620328, [15, 240, 3840, 4369, 8738, 17476, 35016]),
    (49255188078376, [15, 240, 3840, 4369, 8738, 17476, 35064]),
    (49788509455144, [15, 240, 3840, 4369, 8738, 17476, 35208]),
    (50747463713576, [15, 240, 3840, 4369, 8738, 17476, 35464]),
    (52707307930408, [15, 240, 3840, 4369, 8738, 17476, 35976]),
    (55753423455016, [15, 240, 3840, 4369, 8738, 17476, 36744]),
    (56208448446248, [15, 240, 3840, 4369, 8738, 17476, 36856]),
    (65682851414824, [15, 240, 3840, 4369, 8738, 17476, 39048]),
    (66940369609393, [15, 240, 3840, 4369, 8738, 17476, 39321]),
    (67386746260945, [15, 240, 3840, 4369, 8738, 17476, 39417]),
    (74346921039025, [15, 240, 3840, 4369, 8738, 17476, 40857]),
    (86453003666216, [15, 240, 3840, 4369, 8738, 17476, 43144]),
    (141434676757288, [15, 240, 3840, 4369, 8738, 17476, 51336]),
    (150253148842984, [15, 240, 3840, 4369, 8738, 17476, 52428]),
    (150649323442408, [15, 240, 3840, 4369, 8738, 17476, 52476]),
    (156679365409768, [15, 240, 3840, 4369, 8738, 17476, 53196]),
    (189365955109805, [15, 240, 3840, 4369, 8738, 17476, 56797]),
    (238163400483624, [15, 240, 3840, 4369, 8738, 17476, 61448]),
    (263695360770856, [15, 240, 3840, 4369, 8738, 17476, 63624]),
    (265057888968488, [15, 240, 3840, 4369, 8738, 17476, 63736]),
    (267024929571505, [15, 240, 3840, 4369, 8738, 17476, 63897]),
    (277185562749928, [15, 240, 3840, 4369, 8738, 17476, 64716]),
    (286076175647528, [15, 240, 3840, 4369, 8738, 17476, 65416])]

theorem o6_1 : okL 893 5 D5 D6_1 = true := by decide +kernel

def D6_2 : List (ℕ × List ℕ) :=
  [(48844315829797, [15, 240, 3840, 4369, 8738, 17477, 34952]),
    (6151890945960, [15, 240, 3840, 4369, 8738, 17484]),
    (48850732755368, [15, 240, 3840, 4369, 8738, 17484, 34952]),
    (238080124929960, [15, 240, 3840, 4369, 8738, 17484, 61440]),
    (287613982951335, [15, 240, 3840, 4369, 8738, 17484, 65535]),
    (150263233737111, [15, 240, 3840, 4369, 8738, 17487, 52428]),
    (48858072678952, [15, 240, 3840, 4369, 8738, 17492, 34952]),
    (48872772679976, [15, 240, 3840, 4369, 8738, 17508, 34952]),
    (49081407566632, [15, 240, 3840, 4369, 8738, 17732, 34952]),
    (49326388093736, [15, 240, 3840, 4369, 8738, 17988, 34952]),
    (50948331029288, [15, 240, 3840, 4369, 8738, 19524, 34952]),
    (51861585056552, [15, 240, 3840, 4369, 8738, 20292, 34952]),
    (52273373589288, [15, 240, 3840, 4369, 8738, 20292, 35064]),
    (58771608965928, [15, 240, 3840, 4369, 8738, 20292, 36744]),
    (69958555120305, [15, 240, 3840, 4369, 8738, 20292, 39321]),
    (153271334353896, [15, 240, 3840, 4369, 8738, 20292, 52428]),
    (159697550920680, [15, 240, 3840, 4369, 8738, 20292, 53196]),
    (266713546281768, [15, 240, 3840, 4369, 8738, 20292, 63624]),
    (53544600060712, [15, 240, 3840, 4369, 8738, 21572, 34952]),
    (53930566245589, [15, 240, 3840, 4369, 8738, 21845, 34952]),
    (54342354778325, [15, 240, 3840, 4369, 8738, 21845, 35064]),
    (60840590154965, [15, 240, 3840, 4369, 8738, 21845, 36744]),
    (72027536309342, [15, 240, 3840, 4369, 8738, 21845, 39321]),
    (155340315542933, [15, 240, 3840, 4369, 8738, 21845, 52428]),
    (194453121809754, [15, 240, 3840, 4369, 8738, 21845, 56797]),
    (268782527470805, [15, 240, 3840, 4369, 8738, 21845, 63624]),
    (58041760549589, [15, 240, 3840, 4369, 8738, 24405, 34952]),
    (60417309197096, [15, 240, 3840, 4369, 8738, 25668, 34952]),
    (162929367505152, [15, 240, 3840, 4369, 8738, 26214, 52428]),
    (170344989246248, [15, 240, 3840, 4369, 8738, 34952, 50244]),
    (288021861352232, [15, 240, 3840, 4369, 8738, 34952, 62532]),
    (291238358629589, [15, 240, 3840, 4369, 8738, 34952, 62805]),
    (322565601743656, [15, 240, 3840, 4369, 8738, 34952, 65348]),
    (288433649884968, [15, 240, 3840, 4369, 8738, 35064, 62532]),
    (294931885261608, [15, 240, 3840, 4369, 8738, 36744, 62532]),
    (306118831415985, [15, 240, 3840, 4369, 8738, 39321, 62532]),
    (389431610649576, [15, 240, 3840, 4369, 8738, 52428, 62532]),
    (502873822577448, [15, 240, 3840, 4369, 8738, 62532, 63624]),
    (516364024556520, [15, 240, 3840, 4369, 8738, 62532, 64716]),
    (48843628629787, [15, 240, 3840, 4369, 8739, 17476, 34952]),
    (48844316196856, [15, 240, 3840, 4369, 8742, 17476, 34952]),
    (48845233687304, [15, 240, 3840, 4369, 8746, 17476, 34952]),
    (48846381731119, [15, 240, 3840, 4369, 8751, 17476, 34952]),
    (49258170263855, [15, 240, 3840, 4369, 8751, 17476, 35064]),
    (55756405640495, [15, 240, 3840, 4369, 8751, 17476, 36744]),
    (66943351794872, [15, 240, 3840, 4369, 8751, 17476, 39321]),
    (150256131028463, [15, 240, 3840, 4369, 8751, 17476, 52428]),
    (263698342956335, [15, 240, 3840, 4369, 8751, 17476, 63624]),
    (51864567242031, [15, 240, 3840, 4369, 8751, 20292, 34952]),
    (53933548431068, [15, 240, 3840, 4369, 8751, 21845, 34952]),
    (288024843537711, [15, 240, 3840, 4369, 8751, 34952, 62532]),
    (48847071187432, [15, 240, 3840, 4369, 8754, 17476, 34952]),
    (48858166887976, [15, 240, 3840, 4369, 8802, 17476, 34952]),
    (48903773114152, [15, 240, 3840, 4369, 8994, 17476, 34952]),
    (50290138252072, [15, 240, 3840, 4369, 12834, 17476, 34952]),
    (50427926878411, [15, 240, 3840, 4369, 13107, 17476, 34952]),
    (50839715411147, [15, 240, 3840, 4369, 13107, 17476, 35064]),
    (57337950787787, [15, 240, 3840, 4369, 13107, 17476, 36744]),
    (68524896942164, [15, 240, 3840, 4369, 13107, 17476, 39321]),
    (151837676175755, [15, 240, 3840, 4369, 13107, 17476, 52428]),
    (265279888103627, [15, 240, 3840, 4369, 13107, 17476, 63624]),
    (53446112389323, [15, 240, 3840, 4369, 13107, 20292, 34952]),
    (55515093578360, [15, 240, 3840, 4369, 13107, 21845, 34952]),
    (289606388685003, [15, 240, 3840, 4369, 13107, 34952, 62532]),
    (50434117106527, [15, 240, 3840, 4369, 13119, 17476, 34952]),
    (64031098258216, [15, 240, 3840, 4369, 17476, 25122, 34952]),
    (119680610124584, [15, 240, 3840, 4369, 17476, 34952, 41506]),
    (286342818595624, [15, 240, 3840, 4369, 17476, 34952, 61986]),
    (286492698328367, [15, 240, 3840, 4369, 17476, 34952, 61999]),
    (289503512582347, [15, 240, 3840, 4369, 17476, 34952, 62259]),
    (286754607128360, [15, 240, 3840, 4369, 17476, 35064, 61986]),
    (293252842505000, [15, 240, 3840, 4369, 17476, 36744, 61986]),
    (304439788659377, [15, 240, 3840, 4369, 17476, 39321, 61986]),
    (387752567892968, [15, 240, 3840, 4369, 17476, 52428, 61986]),
    (501194779820840, [15, 240, 3840, 4369, 17476, 61986, 63624])]

theorem o6_2 : okL 893 5 D5 D6_2 = true := by decide +kernel

def D6_3 : List (ℕ × List ℕ) :=
  [(289361004106536, [15, 240, 3840, 4369, 20292, 34952, 61986]),
    (291429985295573, [15, 240, 3840, 4369, 21845, 34952, 61986]),
    (525521280402216, [15, 240, 3840, 4369, 34952, 61986, 62532]),
    (48843628813348, [15, 240, 3840, 4373, 8738, 17476, 34952]),
    (6145016691456, [15, 240, 3840, 4377, 8738, 17476]),
    (48843858500864, [15, 240, 3840, 4377, 8738, 17476, 34952]),
    (238073250675456, [15, 240, 3840, 4377, 8738, 17476, 61440]),
    (287607108696831, [15, 240, 3840, 4377, 8738, 17476, 65535]),
    (66941173883871, [15, 240, 3840, 4383, 8738, 17476, 39321]),
    (53931370520067, [15, 240, 3840, 4383, 8738, 21845, 34952]),
    (48845245463432, [15, 240, 3840, 4401, 8738, 17476, 34952]),
    (48847118420968, [15, 240, 3840, 4433, 8738, 17476, 34952]),
    (53944062386037, [15, 240, 3840, 4593, 8738, 21845, 34952]),
    (50441423018859, [15, 240, 3840, 4593, 13107, 17476, 34952]),
    (48876289100072, [15, 240, 3840, 4881, 8738, 17476, 34952]),
    (50847559615179, [15, 240, 3840, 7953, 13107, 17476, 34952]),
    (50741861884712, [15, 240, 3840, 8738, 12561, 17476, 34952]),
    (69108670170027, [15, 240, 3840, 8738, 13107, 17476, 39321]),
    (56098866806223, [15, 240, 3840, 8738, 13107, 21845, 34952]),
    (57698050868008, [15, 240, 3840, 8738, 17476, 20753, 34952]),
    (77281495360109, [15, 240, 3840, 8738, 17476, 21845, 39321]),
    (99977748300584, [15, 240, 3840, 8738, 17476, 34952, 37137]),
    (283793616364328, [15, 240, 3840, 8738, 17476, 34952, 61713]),
    (284205404897064, [15, 240, 3840, 8738, 17476, 35064, 61713]),
    (290703640273704, [15, 240, 3840, 8738, 17476, 36744, 61713]),
    (301890586428081, [15, 240, 3840, 8738, 17476, 39321, 61713]),
    (385203365661672, [15, 240, 3840, 8738, 17476, 52428, 61713]),
    (498645577589544, [15, 240, 3840, 8738, 17476, 61713, 63624]),
    (501975146390193, [15, 240, 3840, 8738, 17476, 61713, 63897]),
    (286811801875240, [15, 240, 3840, 8738, 20292, 34952, 61713]),
    (114642981943341, [15, 240, 3840, 8738, 21845, 34952, 39321]),
    (288880783064277, [15, 240, 3840, 8738, 21845, 34952, 61713]),
    (71944140133933, [15, 240, 3840, 8738, 21845, 39321]),
    (303872374117933, [15, 240, 3840, 8738, 21845, 39321, 61440]),
    (353406232139308, [15, 240, 3840, 8738, 21845, 39321, 65535]),
    (522972078170920, [15, 240, 3840, 8738, 34952, 61713, 62532]),
    (526188575448277, [15, 240, 3840, 8738, 34952, 61713, 62805]),
    (283796598549807, [15, 240, 3840, 8751, 17476, 34952, 61713]),
    (60769052629127, [15, 240, 3840, 13107, 17476, 21845, 34952]),
    (111140342576163, [15, 240, 3840, 13107, 17476, 34952, 39321]),
    (285378143697099, [15, 240, 3840, 13107, 17476, 34952, 61713]),
    (68441500766755, [15, 240, 3840, 13107, 17476, 39321]),
    (300369734750755, [15, 240, 3840, 13107, 17476, 39321, 61440]),
    (349903592772130, [15, 240, 3840, 13107, 17476, 39321, 65535]),
    (55431697402951, [15, 240, 3840, 13107, 21845, 34952]),
    (287359931386951, [15, 240, 3840, 13107, 21845, 34952, 61440]),
    (336893789408326, [15, 240, 3840, 13107, 21845, 34952, 65535]),
    (521293035414312, [15, 240, 3840, 17476, 34952, 61713, 61986]),
    (524453729401035, [15, 240, 3840, 17476, 34952, 61713, 62259]),
    (48843443793961, [15, 240, 3841, 4369, 8738, 17476, 34952]),
    (48843576677224, [15, 240, 3844, 4369, 8738, 17476, 34952]),
    (6144912368424, [15, 240, 3848, 4369, 8738, 17476]),
    (48843754177832, [15, 240, 3848, 4369, 8738, 17476, 34952]),
    (238073146352424, [15, 240, 3848, 4369, 8738, 17476, 61440]),
    (287607004373799, [15, 240, 3848, 4369, 8738, 17476, 65535]),
    (55754089602391, [15, 240, 3855, 4369, 8738, 17476, 36744]),
    (51862251203927, [15, 240, 3855, 4369, 8738, 20292, 34952]),
    (48844110287656, [15, 240, 3856, 4369, 8738, 17476, 34952]),
    (48844826952488, [15, 240, 3872, 4369, 8738, 17476, 34952]),
    (48846278148904, [15, 240, 3904, 4369, 8738, 17476, 34952]),
    (48849252696872, [15, 240, 3968, 4369, 8738, 17476, 34952]),
    (48854693753640, [15, 240, 4080, 4369, 8738, 17476, 34952]),
    (49266482286376, [15, 240, 4080, 4369, 8738, 17476, 35064]),
    (55764717663016, [15, 240, 4080, 4369, 8738, 17476, 36744]),
    (56219742654248, [15, 240, 4080, 4369, 8738, 17476, 36856]),
    (66951663817393, [15, 240, 4080, 4369, 8738, 17476, 39321]),
    (150264443050984, [15, 240, 4080, 4369, 8738, 17476, 52428]),
    (263706654978856, [15, 240, 4080, 4369, 8738, 17476, 63624]),
    (51872879264552, [15, 240, 4080, 4369, 8738, 20292, 34952])]

theorem o6_3 : okL 893 5 D5 D6_3 = true := by decide +kernel

def D6_4 : List (ℕ × List ℕ) :=
  [(53941860453589, [15, 240, 4080, 4369, 8738, 21845, 34952]),
    (288033155560232, [15, 240, 4080, 4369, 8738, 34952, 62532]),
    (48857675939119, [15, 240, 4080, 4369, 8751, 17476, 34952]),
    (50439221086411, [15, 240, 4080, 4369, 13107, 17476, 34952]),
    (286354112803624, [15, 240, 4080, 4369, 17476, 34952, 61986]),
    (283804910572328, [15, 240, 4080, 8738, 17476, 34952, 61713]),
    (55765519827752, [15, 240, 4096, 4369, 8738, 17476, 36744]),
    (51873681429288, [15, 240, 4096, 4369, 8738, 20292, 34952]),
    (55781000800903, [15, 240, 4369, 4383, 8738, 17476, 36744]),
    (51889162402439, [15, 240, 4369, 4383, 8738, 20292, 34952]),
    (55793692666873, [15, 240, 4369, 4593, 8738, 17476, 36744]),
    (51901854268409, [15, 240, 4369, 4593, 8738, 20292, 34952]),
    (56199829263193, [15, 240, 4369, 7953, 8738, 17476, 36744]),
    (52307990864729, [15, 240, 4369, 7953, 8738, 20292, 34952]),
    (56246556164904, [15, 240, 4369, 8192, 8738, 17476, 36744]),
    (52354717766440, [15, 240, 4369, 8192, 8738, 20292, 34952]),
    (56366951939767, [15, 240, 4369, 8738, 8751, 17476, 36744]),
    (52475113541303, [15, 240, 4369, 8738, 8751, 20292, 34952]),
    (56412756925552, [15, 240, 4369, 8738, 8946, 17476, 36744]),
    (52520918527088, [15, 240, 4369, 8738, 8946, 20292, 34952]),
    (57453469454512, [15, 240, 4369, 8738, 12066, 17476, 36744]),
    (53561631056048, [15, 240, 4369, 8738, 12066, 20292, 34952]),
    (57948497087059, [15, 240, 4369, 8738, 13107, 17476, 36744]),
    (54056658688595, [15, 240, 4369, 8738, 13107, 20292, 34952]),
    (60094846862120, [15, 240, 4369, 8738, 16384, 17476, 36744]),
    (56203008463656, [15, 240, 4369, 8738, 16384, 20292, 34952]),
    (61044240471319, [15, 240, 4369, 8738, 17476, 17487, 36744]),
    (61197041822824, [15, 240, 4369, 8738, 17476, 17652, 36744]),
    (57058598241064, [15, 240, 4369, 8738, 17476, 20224, 34952]),
    (57142317178728, [15, 240, 4369, 8738, 17476, 20292, 34952]),
    (57554105711464, [15, 240, 4369, 8738, 17476, 20292, 35064]),
    (64052341088104, [15, 240, 4369, 8738, 17476, 20292, 36744]),
    (75239287242481, [15, 240, 4369, 8738, 17476, 20292, 39321]),
    (158552066476072, [15, 240, 4369, 8738, 17476, 20292, 52428]),
    (164978283042856, [15, 240, 4369, 8738, 17476, 20292, 53196]),
    (271994278403944, [15, 240, 4369, 8738, 17476, 20292, 63624]),
    (57361620384872, [15, 240, 4369, 8738, 17476, 20468, 34952]),
    (66121322277141, [15, 240, 4369, 8738, 17476, 21845, 36744]),
    (73710374239360, [15, 240, 4369, 8738, 17476, 26214, 36744]),
    (90881172439848, [15, 240, 4369, 8738, 17476, 32768, 36744]),
    (97846828909352, [15, 240, 4369, 8738, 17476, 34952, 36608]),
    (98395642160424, [15, 240, 4369, 8738, 17476, 34952, 36744]),
    (98850667151656, [15, 240, 4369, 8738, 17476, 34952, 36856]),
    (199321584115176, [15, 240, 4369, 8738, 17476, 34952, 53196]),
    (98421301787095, [15, 240, 4369, 8738, 17476, 34959, 36744]),
    (98807430693160, [15, 240, 4369, 8738, 17476, 35064, 36744]),
    (99262455684392, [15, 240, 4369, 8738, 17476, 35064, 36856]),
    (55696800351016, [15, 240, 4369, 8738, 17476, 36744]),
    (105334024023767, [15, 240, 4369, 8738, 17476, 36744, 36751]),
    (105760691061032, [15, 240, 4369, 8738, 17476, 36744, 36856]),
    (116492612224177, [15, 240, 4369, 8738, 17476, 36744, 39321]),
    (123899163653809, [15, 240, 4369, 8738, 17476, 36744, 40857]),
    (139092975760016, [15, 240, 4369, 8738, 17476, 36744, 43690]),
    (146639671824016, [15, 240, 4369, 8738, 17476, 36744, 44970]),
    (199805391457768, [15, 240, 4369, 8738, 17476, 36744, 52428]),
    (206231608024552, [15, 240, 4369, 8738, 17476, 36744, 53196]),
    (287625034335016, [15, 240, 4369, 8738, 17476, 36744, 61440]),
    (287794945122391, [15, 240, 4369, 8738, 17476, 36744, 61455]),
    (290353573983016, [15, 240, 4369, 8738, 17476, 36744, 61680]),
    (290730413345113, [15, 240, 4369, 8738, 17476, 36744, 61713]),
    (293863388804272, [15, 240, 4369, 8738, 17476, 36744, 61986]),
    (300212617383784, [15, 240, 4369, 8738, 17476, 36744, 62532]),
    (313247603385640, [15, 240, 4369, 8738, 17476, 36744, 63624]),
    (333886110303016, [15, 240, 4369, 8738, 17476, 36744, 65280]),
    (335628418262312, [15, 240, 4369, 8738, 17476, 36744, 65416]),
    (337158892356391, [15, 240, 4369, 8738, 17476, 36744, 65535]),
    (56151825342248, [15, 240, 4369, 8738, 17476, 36856]),
    (288080059326248, [15, 240, 4369, 8738, 17476, 36856, 61440]),
    (337613917347623, [15, 240, 4369, 8738, 17476, 36856, 65535]),
    (300731333412520, [15, 240, 4369, 8738, 17476, 52428, 53196]),
    (156622742305768, [15, 240, 4369, 8738, 17476, 53196]),
    (388550976289768, [15, 240, 4369, 8738, 17476, 53196, 61440]),
    (438084834311143, [15, 240, 4369, 8738, 17476, 53196, 65535]),
    (57152402072855, [15, 240, 4369, 8738, 17487, 20292, 34952]),
    (57305203424360, [15, 240, 4369, 8738, 17652, 20292, 34952])]

theorem o6_4 : okL 893 5 D5 D6_4 = true := by decide +kernel

def D6_5 : List (ℕ × List ℕ) :=
  [(60174098310679, [15, 240, 4369, 8738, 20292, 20303, 34952]),
    (60379805895784, [15, 240, 4369, 8738, 20292, 20468, 34952]),
    (62229483878677, [15, 240, 4369, 8738, 20292, 21845, 34952]),
    (66340678182677, [15, 240, 4369, 8738, 20292, 24405, 34952]),
    (69818535840896, [15, 240, 4369, 8738, 20292, 26214, 34952]),
    (74997976160384, [15, 240, 4369, 8738, 20292, 28518, 34952]),
    (86989334041384, [15, 240, 4369, 8738, 20292, 32768, 34952]),
    (51804961952552, [15, 240, 4369, 8738, 20292, 34952]),
    (94529463388631, [15, 240, 4369, 8738, 20292, 34952, 34959]),
    (94915592294696, [15, 240, 4369, 8738, 20292, 34952, 35064]),
    (101413827671336, [15, 240, 4369, 8738, 20292, 34952, 36744]),
    (112600773825713, [15, 240, 4369, 8738, 20292, 34952, 39321]),
    (135201137361552, [15, 240, 4369, 8738, 20292, 34952, 43690]),
    (195913553059304, [15, 240, 4369, 8738, 20292, 34952, 52428]),
    (202339769626088, [15, 240, 4369, 8738, 20292, 34952, 53196]),
    (283733195936552, [15, 240, 4369, 8738, 20292, 34952, 61440]),
    (283903106723927, [15, 240, 4369, 8738, 20292, 34952, 61455]),
    (286461735584552, [15, 240, 4369, 8738, 20292, 34952, 61680]),
    (286838574946649, [15, 240, 4369, 8738, 20292, 34952, 61713]),
    (289971550405808, [15, 240, 4369, 8738, 20292, 34952, 61986]),
    (296320778985320, [15, 240, 4369, 8738, 20292, 34952, 62532]),
    (309355764987176, [15, 240, 4369, 8738, 20292, 34952, 63624]),
    (329994271904552, [15, 240, 4369, 8738, 20292, 34952, 65280]),
    (330864519376744, [15, 240, 4369, 8738, 20292, 34952, 65348]),
    (333267053957927, [15, 240, 4369, 8738, 20292, 34952, 65535]),
    (52216750485288, [15, 240, 4369, 8738, 20292, 35064]),
    (284144984469288, [15, 240, 4369, 8738, 20292, 35064, 61440]),
    (333678842490663, [15, 240, 4369, 8738, 20292, 35064, 65535]),
    (58714985861928, [15, 240, 4369, 8738, 20292, 36744]),
    (290643219845928, [15, 240, 4369, 8738, 20292, 36744, 61440]),
    (340177077867303, [15, 240, 4369, 8738, 20292, 36744, 65535]),
    (69901932016305, [15, 240, 4369, 8738, 20292, 39321]),
    (301830166000305, [15, 240, 4369, 8738, 20292, 39321, 61440]),
    (351364024021680, [15, 240, 4369, 8738, 20292, 39321, 65535]),
    (153214711249896, [15, 240, 4369, 8738, 20292, 52428]),
    (385142945233896, [15, 240, 4369, 8738, 20292, 52428, 61440]),
    (434676803255271, [15, 240, 4369, 8738, 20292, 52428, 65535]),
    (159640927816680, [15, 240, 4369, 8738, 20292, 53196]),
    (391569161800680, [15, 240, 4369, 8738, 20292, 53196, 61440]),
    (441103019822055, [15, 240, 4369, 8738, 20292, 53196, 65535]),
    (498585157161768, [15, 240, 4369, 8738, 20292, 61440, 63624]),
    (266656923177768, [15, 240, 4369, 8738, 20292, 63624]),
    (548119015183143, [15, 240, 4369, 8738, 20292, 63624, 65535]),
    (103482808860373, [15, 240, 4369, 8738, 21845, 34952, 36744]),
    (60783967050965, [15, 240, 4369, 8738, 21845, 36744]),
    (292712201034965, [15, 240, 4369, 8738, 21845, 36744, 61440]),
    (342246059056340, [15, 240, 4369, 8738, 21845, 36744, 65535]),
    (337574103967016, [15, 240, 4369, 8738, 34952, 36744, 62532]),
    (526803496141608, [15, 240, 4369, 8738, 36744, 61440, 62532]),
    (294875262157608, [15, 240, 4369, 8738, 36744, 62532]),
    (576337354162983, [15, 240, 4369, 8738, 36744, 62532, 65535]),
    (57145299364207, [15, 240, 4369, 8751, 17476, 20292, 34952]),
    (98398624345903, [15, 240, 4369, 8751, 17476, 34952, 36744]),
    (55699782536495, [15, 240, 4369, 8751, 17476, 36744]),
    (287628016520495, [15, 240, 4369, 8751, 17476, 36744, 61440]),
    (337161874541870, [15, 240, 4369, 8751, 17476, 36744, 65535]),
    (51807944138031, [15, 240, 4369, 8751, 20292, 34952]),
    (283736178122031, [15, 240, 4369, 8751, 20292, 34952, 61440]),
    (333270036143406, [15, 240, 4369, 8751, 20292, 34952, 65535]),
    (58726844511499, [15, 240, 4369, 13107, 17476, 20292, 34952]),
    (99980169493195, [15, 240, 4369, 13107, 17476, 34952, 36744]),
    (57281327683787, [15, 240, 4369, 13107, 17476, 36744]),
    (289209561667787, [15, 240, 4369, 13107, 17476, 36744, 61440]),
    (338743419689162, [15, 240, 4369, 13107, 17476, 36744, 65535]),
    (53389489285323, [15, 240, 4369, 13107, 20292, 34952])]

theorem o6_5 : okL 893 5 D5 D6_5 = true := by decide +kernel

def D6_6 : List (ℕ × List ℕ) :=
  [(285317723269323, [15, 240, 4369, 13107, 20292, 34952, 61440]),
    (334851581290698, [15, 240, 4369, 13107, 20292, 34952, 65535]),
    (48843399719161, [15, 241, 3840, 4369, 8738, 17476, 34952]),
    (48843400248424, [15, 244, 3840, 4369, 8738, 17476, 34952]),
    (6144559165224, [15, 248, 3840, 4369, 8738, 17476]),
    (48843400974632, [15, 248, 3840, 4369, 8738, 17476, 34952]),
    (238072793149224, [15, 248, 3840, 4369, 8738, 17476, 61440]),
    (287606651170599, [15, 248, 3840, 4369, 8738, 17476, 65535]),
    (49255190835751, [15, 255, 3840, 4369, 8738, 17476, 35064]),
    (48854696511015, [15, 255, 4080, 4369, 8738, 17476, 34952]),
    (49255191031592, [15, 256, 3840, 4369, 8738, 17476, 35064]),
    (48843507745576, [15, 496, 3840, 4369, 8738, 17476, 34952]),
    (49255308472104, [15, 512, 3840, 4369, 8738, 17476, 35064]),
    (48843810980648, [15, 752, 3840, 4369, 8738, 17476, 34952]),
    (49256247996200, [15, 1024, 3840, 4369, 8738, 17476, 35064]),
    (49263764188968, [15, 2048, 3840, 4369, 8738, 17476, 35064]),
    (48855363273512, [15, 2288, 3840, 4369, 8738, 17476, 34952]),
    (49312463505751, [15, 3840, 3855, 4369, 8738, 17476, 35064]),
    (49323091566376, [15, 3840, 4080, 4369, 8738, 17476, 35064]),
    (49323893731112, [15, 3840, 4096, 4369, 8738, 17476, 35064]),
    (49339374704263, [15, 3840, 4369, 4383, 8738, 17476, 35064]),
    (49352066570233, [15, 3840, 4369, 4593, 8738, 17476, 35064]),
    (49758203166553, [15, 3840, 4369, 7953, 8738, 17476, 35064]),
    (49804930068264, [15, 3840, 4369, 8192, 8738, 17476, 35064]),
    (49925325843127, [15, 3840, 4369, 8738, 8751, 17476, 35064]),
    (49971130828912, [15, 3840, 4369, 8738, 8946, 17476, 35064]),
    (51011843357872, [15, 3840, 4369, 8738, 12066, 17476, 35064]),
    (51506870990419, [15, 3840, 4369, 8738, 13107, 17476, 35064]),
    (53653220765480, [15, 3840, 4369, 8738, 16384, 17476, 35064]),
    (54602614374679, [15, 3840, 4369, 8738, 17476, 17487, 35064]),
    (54755415726184, [15, 3840, 4369, 8738, 17476, 17652, 35064]),
    (57610714991464, [15, 3840, 4369, 8738, 17476, 20292, 35064]),
    (59679696180501, [15, 3840, 4369, 8738, 17476, 21845, 35064]),
    (67268748142720, [15, 3840, 4369, 8738, 17476, 26214, 35064]),
    (84439546343208, [15, 3840, 4369, 8738, 17476, 32768, 35064]),
    (84806528058152, [15, 3840, 4369, 8738, 17476, 33008, 34952]),
    (91954016063784, [15, 3840, 4369, 8738, 17476, 34952, 35064]),
    (91979675690455, [15, 3840, 4369, 8738, 17476, 34959, 35064]),
    (49255174254376, [15, 3840, 4369, 8738, 17476, 35064]),
    (92391628917287, [15, 3840, 4369, 8738, 17476, 35064, 35071]),
    (98864039973160, [15, 3840, 4369, 8738, 17476, 35064, 36744]),
    (99319064964392, [15, 3840, 4369, 8738, 17476, 35064, 36856]),
    (110050986127537, [15, 3840, 4369, 8738, 17476, 35064, 39321]),
    (110497362779089, [15, 3840, 4369, 8738, 17476, 35064, 39417]),
    (132651349663376, [15, 3840, 4369, 8738, 17476, 35064, 43690]),
    (133110304887376, [15, 3840, 4369, 8738, 17476, 35064, 43770]),
    (193363765361128, [15, 3840, 4369, 8738, 17476, 35064, 52428]),
    (193759939960552, [15, 3840, 4369, 8738, 17476, 35064, 52476]),
    (281183408238376, [15, 3840, 4369, 8738, 17476, 35064, 61440]),
    (281353319025751, [15, 3840, 4369, 8738, 17476, 35064, 61455]),
    (283911947886376, [15, 3840, 4369, 8738, 17476, 35064, 61680]),
    (284288787248473, [15, 3840, 4369, 8738, 17476, 35064, 61713]),
    (287421762707632, [15, 3840, 4369, 8738, 17476, 35064, 61986]),
    (293770991287144, [15, 3840, 4369, 8738, 17476, 35064, 62532]),
    (306805977289000, [15, 3840, 4369, 8738, 17476, 35064, 63624]),
    (308168505486632, [15, 3840, 4369, 8738, 17476, 35064, 63736]),
    (327444484206376, [15, 3840, 4369, 8738, 17476, 35064, 65280]),
    (330717266259751, [15, 3840, 4369, 8738, 17476, 35064, 65535]),
    (97041182763733, [15, 3840, 4369, 8738, 21845, 34952, 35064]),
    (54342340954325, [15, 3840, 4369, 8738, 21845, 35064]),
    (286270574938325, [15, 3840, 4369, 8738, 21845, 35064, 61440]),
    (335804432959700, [15, 3840, 4369, 8738, 21845, 35064, 65535]),
    (91956998249263, [15, 3840, 4369, 8751, 17476, 34952, 35064]),
    (49258156439855, [15, 3840, 4369, 8751, 17476, 35064]),
    (281186390423855, [15, 3840, 4369, 8751, 17476, 35064, 61440]),
    (330720248445230, [15, 3840, 4369, 8751, 17476, 35064, 65535]),
    (93538543396555, [15, 3840, 4369, 13107, 17476, 34952, 35064]),
    (50839701587147, [15, 3840, 4369, 13107, 17476, 35064]),
    (282767935571147, [15, 3840, 4369, 13107, 17476, 35064, 61440]),
    (332301793592522, [15, 3840, 4369, 13107, 17476, 35064, 65535]),
    (48951572245497, [15, 4080, 4369, 4593, 8738, 17476, 34952]),
    (49570636504176, [15, 4080, 4369, 8738, 8946, 17476, 34952])]

theorem o6_6 : okL 893 5 D5 D6_6 = true := by decide +kernel

def D6_7 : List (ℕ × List ℕ) :=
  [(91965310271784, [15, 4080, 4369, 8738, 17476, 34952, 35064]),
    (283511453561640, [15, 4080, 4369, 8738, 17476, 34952, 61680]),
    (49266468462376, [15, 4080, 4369, 8738, 17476, 35064]),
    (281194702446376, [15, 4080, 4369, 8738, 17476, 35064, 61440]),
    (330728560467751, [15, 4080, 4369, 8738, 17476, 35064, 65535]),
    (100252933696872, [15, 4369, 8738, 17476, 20292, 34952, 35064]),
    (57554091887464, [15, 4369, 8738, 17476, 20292, 35064]),
    (289482325871464, [15, 4369, 8738, 17476, 20292, 35064, 61440]),
    (339016183892839, [15, 4369, 8738, 17476, 20292, 35064, 65535]),
    (141506258678568, [15, 4369, 8738, 17476, 34952, 35064, 36744]),
    (141961283669800, [15, 4369, 8738, 17476, 34952, 35064, 36856]),
    (98807416869160, [15, 4369, 8738, 17476, 35064, 36744]),
    (330735650853160, [15, 4369, 8738, 17476, 35064, 36744, 61440]),
    (380269508874535, [15, 4369, 8738, 17476, 35064, 36744, 65535]),
    (99262441860392, [15, 4369, 8738, 17476, 35064, 36856]),
    (331190675844392, [15, 4369, 8738, 17476, 35064, 36856, 61440]),
    (380724533865767, [15, 4369, 8738, 17476, 35064, 36856, 65535]),
    (48846381731840, [16, 240, 3840, 4369, 8751, 17476, 34952]),
    (48843399572056, [31, 240, 3840, 4369, 8738, 17476, 34952]),
    (48846381760512, [32, 240, 3840, 4369, 8751, 17476, 34952]),
    (48843399646088, [47, 240, 3840, 4369, 8738, 17476, 34952]),
    (48846381989888, [64, 240, 3840, 4369, 8751, 17476, 34952]),
    (48843400035304, [79, 240, 3840, 4369, 8738, 17476, 34952]),
    (48846383824896, [128, 240, 3840, 4369, 8751, 17476, 34952]),
    (48846398309119, [240, 255, 3840, 4369, 8751, 17476, 34952]),
    (48846398504960, [240, 256, 3840, 4369, 8751, 17476, 34952]),
    (48843419444776, [240, 271, 3840, 4369, 8738, 17476, 34952]),
    (48846515945472, [240, 512, 3840, 4369, 8751, 17476, 34952]),
    (48843545905448, [240, 527, 3840, 4369, 8738, 17476, 34952]),
    (48847455469568, [240, 1024, 3840, 4369, 8751, 17476, 34952]),
    (48854971662336, [240, 2048, 3840, 4369, 8751, 17476, 34952]),
    (48903670979119, [240, 3840, 3855, 4369, 8751, 17476, 34952]),
    (48914299039744, [240, 3840, 4080, 4369, 8751, 17476, 34952]),
    (48915101204480, [240, 3840, 4096, 4369, 8751, 17476, 34952]),
    (48930582177631, [240, 3840, 4369, 4383, 8751, 17476, 34952]),
    (48943274043601, [240, 3840, 4369, 4593, 8751, 17476, 34952]),
    (49349410639921, [240, 3840, 4369, 7953, 8751, 17476, 34952]),
    (49396137541632, [240, 3840, 4369, 8192, 8751, 17476, 34952]),
    (49396180788008, [240, 3840, 4369, 8207, 8738, 17476, 34952]),
    (49513551131016, [240, 3840, 4369, 8738, 8751, 17476, 34952]),
    (49925339663752, [240, 3840, 4369, 8738, 8751, 17476, 35064]),
    (56423575040392, [240, 3840, 4369, 8738, 8751, 17476, 36744]),
    (67610521194769, [240, 3840, 4369, 8738, 8751, 17476, 39321]),
    (150923300428360, [240, 3840, 4369, 8738, 8751, 17476, 52428]),
    (52531736641928, [240, 3840, 4369, 8738, 8751, 20292, 34952]),
    (54600717830965, [240, 3840, 4369, 8738, 8751, 21845, 34952]),
    (49562338302280, [240, 3840, 4369, 8751, 8946, 17476, 34952]),
    (49565464045823, [240, 3840, 4369, 8751, 8959, 17476, 34952]),
    (50603050831240, [240, 3840, 4369, 8751, 12066, 17476, 34952]),
    (50608734896783, [240, 3840, 4369, 8751, 12079, 17476, 34952]),
    (51098078463787, [240, 3840, 4369, 8751, 13107, 17476, 34952]),
    (51104268691903, [240, 3840, 4369, 8751, 13119, 17476, 34952]),
    (53244428238848, [240, 3840, 4369, 8751, 16384, 17476, 34952]),
    (54193821848047, [240, 3840, 4369, 8751, 17476, 17487, 34952]),
    (54346623199552, [240, 3840, 4369, 8751, 17476, 17652, 34952]),
    (57201922464832, [240, 3840, 4369, 8751, 17476, 20292, 34952]),
    (59270903653869, [240, 3840, 4369, 8751, 17476, 21845, 34952]),
    (66859955616088, [240, 3840, 4369, 8751, 17476, 26214, 34952]),
    (66878515679311, [240, 3840, 4369, 8751, 17476, 26223, 34952]),
    (84030753816576, [240, 3840, 4369, 8751, 17476, 32768, 34952]),
    (48846381727744, [240, 3840, 4369, 8751, 17476, 34952]),
    (91570883163823, [240, 3840, 4369, 8751, 17476, 34952, 34959]),
    (91957012069888, [240, 3840, 4369, 8751, 17476, 34952, 35064]),
    (98455247446528, [240, 3840, 4369, 8751, 17476, 34952, 36744]),
    (109642193600905, [240, 3840, 4369, 8751, 17476, 34952, 39321]),
    (132242557136744, [240, 3840, 4369, 8751, 17476, 34952, 43690]),
    (132271192655119, [240, 3840, 4369, 8751, 17476, 34952, 43695]),
    (192954972834496, [240, 3840, 4369, 8751, 17476, 34952, 52428]),
    (280774615711744, [240, 3840, 4369, 8751, 17476, 34952, 61440]),
    (280944526499119, [240, 3840, 4369, 8751, 17476, 34952, 61455]),
    (283503155359744, [240, 3840, 4369, 8751, 17476, 34952, 61680]),
    (283879994721841, [240, 3840, 4369, 8751, 17476, 34952, 61713])]

theorem o6_7 : okL 893 5 D5 D6_7 = true := by decide +kernel

def D6_8 : List (ℕ × List ℕ) :=
  [(287012970181000, [240, 3840, 4369, 8751, 17476, 34952, 61986]),
    (287162849913743, [240, 3840, 4369, 8751, 17476, 34952, 61999]),
    (293362198760512, [240, 3840, 4369, 8751, 17476, 34952, 62532]),
    (306397184762368, [240, 3840, 4369, 8751, 17476, 34952, 63624]),
    (327035691679744, [240, 3840, 4369, 8751, 17476, 34952, 65280]),
    (330308473733119, [240, 3840, 4369, 8751, 17476, 34952, 65535]),
    (49258170260480, [240, 3840, 4369, 8751, 17476, 35064]),
    (281186404244480, [240, 3840, 4369, 8751, 17476, 35064, 61440]),
    (330720262265855, [240, 3840, 4369, 8751, 17476, 35064, 65535]),
    (55756405637120, [240, 3840, 4369, 8751, 17476, 36744]),
    (287684639621120, [240, 3840, 4369, 8751, 17476, 36744, 61440]),
    (337218497642495, [240, 3840, 4369, 8751, 17476, 36744, 65535]),
    (66943351791497, [240, 3840, 4369, 8751, 17476, 39321]),
    (298871585775497, [240, 3840, 4369, 8751, 17476, 39321, 61440]),
    (348405443796872, [240, 3840, 4369, 8751, 17476, 39321, 65535]),
    (150256131025088, [240, 3840, 4369, 8751, 17476, 52428]),
    (382184365009088, [240, 3840, 4369, 8751, 17476, 52428, 61440]),
    (431718223030463, [240, 3840, 4369, 8751, 17476, 52428, 65535]),
    (51864567238656, [240, 3840, 4369, 8751, 20292, 34952]),
    (283792801222656, [240, 3840, 4369, 8751, 20292, 34952, 61440]),
    (333326659244031, [240, 3840, 4369, 8751, 20292, 34952, 65535]),
    (53933548427693, [240, 3840, 4369, 8751, 21845, 34952]),
    (285861782411693, [240, 3840, 4369, 8751, 21845, 34952, 61440]),
    (335395640433068, [240, 3840, 4369, 8751, 21845, 34952, 65535]),
    (49524845339016, [240, 4080, 4369, 8738, 8751, 17476, 34952]),
    (48857675935744, [240, 4080, 4369, 8751, 17476, 34952]),
    (280785909919744, [240, 4080, 4369, 8751, 17476, 34952, 61440]),
    (330319767941119, [240, 4080, 4369, 8751, 17476, 34952, 65535]),
    (57812468764104, [240, 4369, 8738, 8751, 17476, 20292, 34952]),
    (99065793745800, [240, 4369, 8738, 8751, 17476, 34952, 36744]),
    (56366951936392, [240, 4369, 8738, 8751, 17476, 36744]),
    (288295185920392, [240, 4369, 8738, 8751, 17476, 36744, 61440]),
    (337829043941767, [240, 4369, 8738, 8751, 17476, 36744, 65535]),
    (52475113537928, [240, 4369, 8738, 8751, 20292, 34952]),
    (284403347521928, [240, 4369, 8738, 8751, 20292, 34952, 61440]),
    (333937205543303, [240, 4369, 8738, 8751, 20292, 34952, 65535]),
    (57145299360832, [240, 4369, 8751, 17476, 20292, 34952]),
    (289073533344832, [240, 4369, 8751, 17476, 20292, 34952, 61440]),
    (338607391366207, [240, 4369, 8751, 17476, 20292, 34952, 65535]),
    (98398624342528, [240, 4369, 8751, 17476, 34952, 36744]),
    (330326858326528, [240, 4369, 8751, 17476, 34952, 36744, 61440]),
    (379860716347903, [240, 4369, 8751, 17476, 34952, 36744, 65535]),
    (55699782533120, [240, 4369, 8751, 17476, 36744]),
    (287628016517120, [240, 4369, 8751, 17476, 36744, 61440]),
    (569090108522495, [240, 4369, 8751, 17476, 36744, 61440, 65535]),
    (337161874538495, [240, 4369, 8751, 17476, 36744, 65535]),
    (51807944134656, [240, 4369, 8751, 20292, 34952]),
    (283736178118656, [240, 4369, 8751, 20292, 34952, 61440]),
    (565198270124031, [240, 4369, 8751, 20292, 34952, 61440, 65535]),
    (333270036140031, [240, 4369, 8751, 20292, 34952, 65535]),
    (92624167649160, [3840, 4369, 8738, 8751, 17476, 34952, 35064]),
    (49925325839752, [3840, 4369, 8738, 8751, 17476, 35064]),
    (281853559823752, [3840, 4369, 8738, 8751, 17476, 35064, 61440]),
    (331387417845127, [3840, 4369, 8738, 8751, 17476, 35064, 65535]),
    (91956998245888, [3840, 4369, 8751, 17476, 34952, 35064]),
    (323885232229888, [3840, 4369, 8751, 17476, 34952, 35064, 61440]),
    (373419090251263, [3840, 4369, 8751, 17476, 34952, 35064, 65535]),
    (49258156436480, [3840, 4369, 8751, 17476, 35064]),
    (281186390420480, [3840, 4369, 8751, 17476, 35064, 61440])]

theorem o6_8 : okL 893 5 D5 D6_8 = true := by decide +kernel

def D6_9 : List (ℕ × List ℕ) :=
  [(562648482425855, [3840, 4369, 8751, 17476, 35064, 61440, 65535]),
    (330720248441855, [3840, 4369, 8751, 17476, 35064, 65535])]

theorem o6_9 : okL 893 5 D5 D6_9 = true := by decide +kernel

def D6 : List (ℕ × List ℕ) := D6_0 ++ D6_1 ++ D6_2 ++ D6_3 ++ D6_4 ++ D6_5 ++ D6_6 ++ D6_7 ++ D6_8 ++ D6_9

theorem t6 : Dead 893 6 D6 :=
  dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (dead_append _ _ _ _ (okL_sound _ _ _ _ t5 o6_0) (okL_sound _ _ _ _ t5 o6_1)) (okL_sound _ _ _ _ t5 o6_2)) (okL_sound _ _ _ _ t5 o6_3)) (okL_sound _ _ _ _ t5 o6_4)) (okL_sound _ _ _ _ t5 o6_5)) (okL_sound _ _ _ _ t5 o6_6)) (okL_sound _ _ _ _ t5 o6_7)) (okL_sound _ _ _ _ t5 o6_8)) (okL_sound _ _ _ _ t5 o6_9)

def D7_0 : List (ℕ × List ℕ) :=
  [(6144557736744, [0, 8, 15, 240, 3840, 4369, 8738, 17476]),
    (48843399545640, [0, 15, 240, 3840, 4369, 8738, 17476, 34952]),
    (49255188078376, [0, 15, 240, 3840, 4369, 8738, 17476, 35064]),
    (55753423455016, [0, 15, 240, 3840, 4369, 8738, 17476, 36744]),
    (66940369609393, [0, 15, 240, 3840, 4369, 8738, 17476, 39321]),
    (150253148842984, [0, 15, 240, 3840, 4369, 8738, 17476, 52428]),
    (263695360770856, [0, 15, 240, 3840, 4369, 8738, 17476, 63624]),
    (51861585056552, [0, 15, 240, 3840, 4369, 8738, 20292, 34952]),
    (53930566245589, [0, 15, 240, 3840, 4369, 8738, 21845, 34952]),
    (288021861352232, [0, 15, 240, 3840, 4369, 8738, 34952, 62532]),
    (48846381731119, [0, 15, 240, 3840, 4369, 8751, 17476, 34952]),
    (50427926878411, [0, 15, 240, 3840, 4369, 13107, 17476, 34952]),
    (286342818595624, [0, 15, 240, 3840, 4369, 17476, 34952, 61986]),
    (283793616364328, [0, 15, 240, 3840, 8738, 17476, 34952, 61713]),
    (48854693753640, [0, 15, 240, 4080, 4369, 8738, 17476, 34952]),
    (57142317178728, [0, 15, 240, 4369, 8738, 17476, 20292, 34952]),
    (98395642160424, [0, 15, 240, 4369, 8738, 17476, 34952, 36744]),
    (55696800351016, [0, 15, 240, 4369, 8738, 17476, 36744]),
    (287625034335016, [0, 15, 240, 4369, 8738, 17476, 36744, 61440]),
    (337158892356391, [0, 15, 240, 4369, 8738, 17476, 36744, 65535]),
    (51804961952552, [0, 15, 240, 4369, 8738, 20292, 34952]),
    (283733195936552, [0, 15, 240, 4369, 8738, 20292, 34952, 61440]),
    (333267053957927, [0, 15, 240, 4369, 8738, 20292, 34952, 65535]),
    (91954016063784, [0, 15, 3840, 4369, 8738, 17476, 34952, 35064]),
    (49255174254376, [0, 15, 3840, 4369, 8738, 17476, 35064]),
    (281183408238376, [0, 15, 3840, 4369, 8738, 17476, 35064, 61440]),
    (330717266259751, [0, 15, 3840, 4369, 8738, 17476, 35064, 65535]),
    (49513551131016, [0, 240, 3840, 4369, 8738, 8751, 17476, 34952]),
    (48846381727744, [0, 240, 3840, 4369, 8751, 17476, 34952]),
    (280774615711744, [0, 240, 3840, 4369, 8751, 17476, 34952, 61440]),
    (330308473733119, [0, 240, 3840, 4369, 8751, 17476, 34952, 65535]),
    (48843399545641, [1, 15, 240, 3840, 4369, 8738, 17476, 34952]),
    (48843399545648, [2, 15, 240, 3840, 4369, 8738, 17476, 34952]),
    (48843399545704, [4, 15, 240, 3840, 4369, 8738, 17476, 34952]),
    (6144557736744, [8, 15, 240, 3840, 4369, 8738, 17476]),
    (48843399546152, [8, 15, 240, 3840, 4369, 8738, 17476, 34952]),
    (238072791720744, [8, 15, 240, 3840, 4369, 8738, 17476, 61440]),
    (287606649742119, [8, 15, 240, 3840, 4369, 8738, 17476, 65535]),
    (48843399549736, [15, 16, 240, 3840, 4369, 8738, 17476, 34952]),
    (48843399578408, [15, 32, 240, 3840, 4369, 8738, 17476, 34952]),
    (48843399807784, [15, 64, 240, 3840, 4369, 8738, 17476, 34952]),
    (48843401642792, [15, 128, 240, 3840, 4369, 8738, 17476, 34952]),
    (48843416127015, [15, 240, 255, 3840, 4369, 8738, 17476, 34952]),
    (48843416322856, [15, 240, 256, 3840, 4369, 8738, 17476, 34952]),
    (48843533763368, [15, 240, 512, 3840, 4369, 8738, 17476, 34952]),
    (48844473287464, [15, 240, 1024, 3840, 4369, 8738, 17476, 34952]),
    (48851989480232, [15, 240, 2048, 3840, 4369, 8738, 17476, 34952]),
    (48900688797015, [15, 240, 3840, 3855, 4369, 8738, 17476, 34952]),
    (48911316857640, [15, 240, 3840, 4080, 4369, 8738, 17476, 34952]),
    (48912119022376, [15, 240, 3840, 4096, 4369, 8738, 17476, 34952]),
    (48927599995527, [15, 240, 3840, 4369, 4383, 8738, 17476, 34952]),
    (48940291861497, [15, 240, 3840, 4369, 4593, 8738, 17476, 34952]),
    (49346428457817, [15, 240, 3840, 4369, 7953, 8738, 17476, 34952]),
    (49393155359528, [15, 240, 3840, 4369, 8192, 8738, 17476, 34952]),
    (49513551134391, [15, 240, 3840, 4369, 8738, 8751, 17476, 34952]),
    (49559356120176, [15, 240, 3840, 4369, 8738, 8946, 17476, 34952]),
    (50600068649136, [15, 240, 3840, 4369, 8738, 12066, 17476, 34952]),
    (51095096281683, [15, 240, 3840, 4369, 8738, 13107, 17476, 34952]),
    (53241446056744, [15, 240, 3840, 4369, 8738, 16384, 17476, 34952]),
    (54190839665943, [15, 240, 3840, 4369, 8738, 17476, 17487, 34952]),
    (54343641017448, [15, 240, 3840, 4369, 8738, 17476, 17652, 34952]),
    (57198940282728, [15, 240, 3840, 4369, 8738, 17476, 20292, 34952]),
    (59267921471765, [15, 240, 3840, 4369, 8738, 17476, 21845, 34952]),
    (66856973433984, [15, 240, 3840, 4369, 8738, 17476, 26214, 34952]),
    (84027771634472, [15, 240, 3840, 4369, 8738, 17476, 32768, 34952])]

theorem o7_0 : okL 893 6 D6 D7_0 = true := by decide +kernel

def D7_1 : List (ℕ × List ℕ) :=
  [(48843399545640, [15, 240, 3840, 4369, 8738, 17476, 34952]),
    (91567900981719, [15, 240, 3840, 4369, 8738, 17476, 34952, 34959]),
    (91954029887784, [15, 240, 3840, 4369, 8738, 17476, 34952, 35064]),
    (98452265264424, [15, 240, 3840, 4369, 8738, 17476, 34952, 36744]),
    (109639211418801, [15, 240, 3840, 4369, 8738, 17476, 34952, 39321]),
    (132239574954640, [15, 240, 3840, 4369, 8738, 17476, 34952, 43690]),
    (192951990652392, [15, 240, 3840, 4369, 8738, 17476, 34952, 52428]),
    (280771633529640, [15, 240, 3840, 4369, 8738, 17476, 34952, 61440]),
    (280941544317015, [15, 240, 3840, 4369, 8738, 17476, 34952, 61455]),
    (283500173177640, [15, 240, 3840, 4369, 8738, 17476, 34952, 61680]),
    (283877012539737, [15, 240, 3840, 4369, 8738, 17476, 34952, 61713]),
    (287009987998896, [15, 240, 3840, 4369, 8738, 17476, 34952, 61986]),
    (293359216578408, [15, 240, 3840, 4369, 8738, 17476, 34952, 62532]),
    (306394202580264, [15, 240, 3840, 4369, 8738, 17476, 34952, 63624]),
    (327032709497640, [15, 240, 3840, 4369, 8738, 17476, 34952, 65280]),
    (330305491551015, [15, 240, 3840, 4369, 8738, 17476, 34952, 65535]),
    (49255188078376, [15, 240, 3840, 4369, 8738, 17476, 35064]),
    (281183422062376, [15, 240, 3840, 4369, 8738, 17476, 35064, 61440]),
    (330717280083751, [15, 240, 3840, 4369, 8738, 17476, 35064, 65535]),
    (55753423455016, [15, 240, 3840, 4369, 8738, 17476, 36744]),
    (287681657439016, [15, 240, 3840, 4369, 8738, 17476, 36744, 61440]),
    (337215515460391, [15, 240, 3840, 4369, 8738, 17476, 36744, 65535]),
    (66940369609393, [15, 240, 3840, 4369, 8738, 17476, 39321]),
    (298868603593393, [15, 240, 3840, 4369, 8738, 17476, 39321, 61440]),
    (348402461614768, [15, 240, 3840, 4369, 8738, 17476, 39321, 65535]),
    (150253148842984, [15, 240, 3840, 4369, 8738, 17476, 52428]),
    (382181382826984, [15, 240, 3840, 4369, 8738, 17476, 52428, 61440]),
    (431715240848359, [15, 240, 3840, 4369, 8738, 17476, 52428, 65535]),
    (495623594754856, [15, 240, 3840, 4369, 8738, 17476, 61440, 63624]),
    (263695360770856, [15, 240, 3840, 4369, 8738, 17476, 63624]),
    (545157452776231, [15, 240, 3840, 4369, 8738, 17476, 63624, 65535]),
    (51861585056552, [15, 240, 3840, 4369, 8738, 20292, 34952]),
    (283789819040552, [15, 240, 3840, 4369, 8738, 20292, 34952, 61440]),
    (333323677061927, [15, 240, 3840, 4369, 8738, 20292, 34952, 65535]),
    (53930566245589, [15, 240, 3840, 4369, 8738, 21845, 34952]),
    (285858800229589, [15, 240, 3840, 4369, 8738, 21845, 34952, 61440]),
    (335392658250964, [15, 240, 3840, 4369, 8738, 21845, 34952, 65535]),
    (519950095336232, [15, 240, 3840, 4369, 8738, 34952, 61440, 62532]),
    (288021861352232, [15, 240, 3840, 4369, 8738, 34952, 62532]),
    (569483953357607, [15, 240, 3840, 4369, 8738, 34952, 62532, 65535]),
    (48846381731119, [15, 240, 3840, 4369, 8751, 17476, 34952]),
    (280774615715119, [15, 240, 3840, 4369, 8751, 17476, 34952, 61440]),
    (330308473736494, [15, 240, 3840, 4369, 8751, 17476, 34952, 65535]),
    (50427926878411, [15, 240, 3840, 4369, 13107, 17476, 34952]),
    (282356160862411, [15, 240, 3840, 4369, 13107, 17476, 34952, 61440])]

theorem o7_1 : okL 893 6 D6 D7_1 = true := by decide +kernel

def D7_2 : List (ℕ × List ℕ) :=
  [(331890018883786, [15, 240, 3840, 4369, 13107, 17476, 34952, 65535]),
    (518271052579624, [15, 240, 3840, 4369, 17476, 34952, 61440, 61986]),
    (286342818595624, [15, 240, 3840, 4369, 17476, 34952, 61986]),
    (567804910600999, [15, 240, 3840, 4369, 17476, 34952, 61986, 65535]),
    (515721850348328, [15, 240, 3840, 8738, 17476, 34952, 61440, 61713]),
    (283793616364328, [15, 240, 3840, 8738, 17476, 34952, 61713]),
    (565255708369703, [15, 240, 3840, 8738, 17476, 34952, 61713, 65535]),
    (48854693753640, [15, 240, 4080, 4369, 8738, 17476, 34952]),
    (280782927737640, [15, 240, 4080, 4369, 8738, 17476, 34952, 61440]),
    (330316785759015, [15, 240, 4080, 4369, 8738, 17476, 34952, 65535]),
    (57142317178728, [15, 240, 4369, 8738, 17476, 20292, 34952]),
    (289070551162728, [15, 240, 4369, 8738, 17476, 20292, 34952, 61440]),
    (338604409184103, [15, 240, 4369, 8738, 17476, 20292, 34952, 65535]),
    (98395642160424, [15, 240, 4369, 8738, 17476, 34952, 36744]),
    (330323876144424, [15, 240, 4369, 8738, 17476, 34952, 36744, 61440]),
    (379857734165799, [15, 240, 4369, 8738, 17476, 34952, 36744, 65535]),
    (55696800351016, [15, 240, 4369, 8738, 17476, 36744]),
    (287625034335016, [15, 240, 4369, 8738, 17476, 36744, 61440]),
    (569087126340391, [15, 240, 4369, 8738, 17476, 36744, 61440, 65535]),
    (337158892356391, [15, 240, 4369, 8738, 17476, 36744, 65535]),
    (51804961952552, [15, 240, 4369, 8738, 20292, 34952]),
    (283733195936552, [15, 240, 4369, 8738, 20292, 34952, 61440]),
    (565195287941927, [15, 240, 4369, 8738, 20292, 34952, 61440, 65535]),
    (333267053957927, [15, 240, 4369, 8738, 20292, 34952, 65535]),
    (91954016063784, [15, 3840, 4369, 8738, 17476, 34952, 35064]),
    (323882250047784, [15, 3840, 4369, 8738, 17476, 34952, 35064, 61440]),
    (373416108069159, [15, 3840, 4369, 8738, 17476, 34952, 35064, 65535]),
    (49255174254376, [15, 3840, 4369, 8738, 17476, 35064]),
    (281183408238376, [15, 3840, 4369, 8738, 17476, 35064, 61440]),
    (562645500243751, [15, 3840, 4369, 8738, 17476, 35064, 61440, 65535]),
    (330717266259751, [15, 3840, 4369, 8738, 17476, 35064, 65535]),
    (49513551131016, [240, 3840, 4369, 8738, 8751, 17476, 34952]),
    (281441785115016, [240, 3840, 4369, 8738, 8751, 17476, 34952, 61440]),
    (330975643136391, [240, 3840, 4369, 8738, 8751, 17476, 34952, 65535]),
    (48846381727744, [240, 3840, 4369, 8751, 17476, 34952]),
    (280774615711744, [240, 3840, 4369, 8751, 17476, 34952, 61440]),
    (562236707717119, [240, 3840, 4369, 8751, 17476, 34952, 61440, 65535]),
    (330308473733119, [240, 3840, 4369, 8751, 17476, 34952, 65535])]

theorem o7_2 : okL 893 6 D6 D7_2 = true := by decide +kernel

def D7 : List (ℕ × List ℕ) := D7_0 ++ D7_1 ++ D7_2

theorem t7 : Dead 893 7 D7 :=
  dead_append _ _ _ _ (dead_append _ _ _ _ (okL_sound _ _ _ _ t6 o7_0) (okL_sound _ _ _ _ t6 o7_1)) (okL_sound _ _ _ _ t6 o7_2)

def D8_0 : List (ℕ × List ℕ) :=
  [(48843399545640, [0, 15, 240, 3840, 4369, 8738, 17476, 34952]),
    (280771633529640, [0, 15, 240, 3840, 4369, 8738, 17476, 34952, 61440]),
    (330305491551015, [0, 15, 240, 3840, 4369, 8738, 17476, 34952, 65535]),
    (48843399545640, [15, 240, 3840, 4369, 8738, 17476, 34952]),
    (280771633529640, [15, 240, 3840, 4369, 8738, 17476, 34952, 61440]),
    (562233725535015, [15, 240, 3840, 4369, 8738, 17476, 34952, 61440, 65535]),
    (330305491551015, [15, 240, 3840, 4369, 8738, 17476, 34952, 65535])]

theorem o8_0 : okL 893 7 D7 D8_0 = true := by decide +kernel

def D8 : List (ℕ × List ℕ) := D8_0

theorem t8 : Dead 893 8 D8 :=
  okL_sound _ _ _ _ t7 o8_0

theorem s0 : start 893 0 D0 = true := by decide +kernel

theorem s1 : start 893 1 D1 = true := by decide +kernel

theorem s2 : start 893 2 D2 = true := by decide +kernel

theorem s3 : start 893 3 D3 = true := by decide +kernel

theorem s4 : start 893 4 D4 = true := by decide +kernel

theorem s5 : start 893 5 D5 = true := by decide +kernel

theorem s6 : start 893 6 D6 = true := by decide +kernel

theorem s7 : start 893 7 D7 = true := by decide +kernel

theorem s8 : start 893 8 D8 = true := by decide +kernel

theorem up : RepSizeAtMost (fun u v : Fin 4 => (893 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [8, 6]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.or, [10, 5]⟩, ⟨GateOp.or, [10, 7]⟩, ⟨GateOp.and, [12, 0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [14, 11]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_6182

theorem PEqualNP.Outside.L_meta_6182 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (893 : ℕ).testBit (4 * u.val + v.val)) 9 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (893 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  refine ⟨PEqualNP.Outside.L_meta_6182.up, PEqualNP.Outside.L_meta_6182.lower 893 8 (by decide) ?_⟩
  intro k hk
  interval_cases k
  · exact ⟨_, PEqualNP.Outside.L_meta_6182.t0, PEqualNP.Outside.L_meta_6182.s0⟩
  · exact ⟨_, PEqualNP.Outside.L_meta_6182.t1, PEqualNP.Outside.L_meta_6182.s1⟩
  · exact ⟨_, PEqualNP.Outside.L_meta_6182.t2, PEqualNP.Outside.L_meta_6182.s2⟩
  · exact ⟨_, PEqualNP.Outside.L_meta_6182.t3, PEqualNP.Outside.L_meta_6182.s3⟩
  · exact ⟨_, PEqualNP.Outside.L_meta_6182.t4, PEqualNP.Outside.L_meta_6182.s4⟩
  · exact ⟨_, PEqualNP.Outside.L_meta_6182.t5, PEqualNP.Outside.L_meta_6182.s5⟩
  · exact ⟨_, PEqualNP.Outside.L_meta_6182.t6, PEqualNP.Outside.L_meta_6182.s6⟩
  · exact ⟨_, PEqualNP.Outside.L_meta_6182.t7, PEqualNP.Outside.L_meta_6182.s7⟩
  · exact ⟨_, PEqualNP.Outside.L_meta_6182.t8, PEqualNP.Outside.L_meta_6182.s8⟩
