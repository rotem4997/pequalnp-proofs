import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- The checker of live-state certificates with cofactor cuts (the generic part, up to the data) is the one of the checked
-- V_meta_9945__k9 (same repository, Apache-2.0); the certificates below are new.

namespace PEqualNP.Outside.L_meta_13143_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def mask256 : Nat := 2 ^ 256 - 1

def negD (d w : Nat) : Nat := (w ^^^ mask256) &&& d
def andD (d a b : Nat) : Nat := (a &&& b) &&& d
def orD (d a b : Nat) : Nat := (a ||| b) &&& d
def binD (d : Nat) (isOr : Bool) (a b : Nat) : Nat := if isOr then orD d a b else andD d a b

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunD (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool),
      negD d a ≠ 0 → negD d a ≠ d → negD d a ∉ (a :: r) →
      P s (negD d a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (if c then andD d a b else orD d a b) ≠ 0 →
      (if c then andD d a b else orD d a b) ≠ d →
      (if c then andD d a b else orD d a b) ∉ (a :: b :: r) →
      P s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {d y : Nat}

theorem Run.done : RunD d y 0 [y] := fun _ dn _ _ _ => dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD d y s xs) :
    RunD d y s zs := fun P dn q u b => q p (h P dn q u b)
theorem Run.one {s a r} (save : Bool)
    (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
    (h : RunD d y s (negD d a :: kept save a r)) :
    RunD d y (s + 1) (a :: r) := fun P dn q u b => u save h0 hd hm (h P dn q u b)
theorem Run.two {s a b r} (c ka kb : Bool)
    (h0 : (if c then andD d a b else orD d a b) ≠ 0)
    (hd : (if c then andD d a b else orD d a b) ≠ d)
    (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
    (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))) :
    RunD d y (s + 1) (a :: b :: r) := fun P dn q u v => v c ka kb h0 hd hm (h P dn q u v)

theorem Run.fold {P : ∀ t ws, RunD d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
      (h : RunD d y s (negD d a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h0 hd hm h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h0 : (if c then andD d a b else orD d a b) ≠ 0)
      (hd : (if c then andD d a b else orD d a b) ≠ d)
      (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
      (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h0 hd hm h))
    {t ws} (h : RunD d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunD d y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k h0 hd hm ⟨h', ih⟩ => ⟨Run.one k h0 hd hm h', one k h0 hd hm h' ih⟩)
    (fun c a b h0 hd hm ⟨h', ih⟩ => ⟨Run.two c a b h0 hd hm h', two c a b h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

theorem run_len {d y s xs} (h : RunD d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ _ _ _ ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

theorem zero_done {d y t ws} (h : RunD d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

def IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def isConstB (d w : Nat) : Bool := (w &&& d == 0) || (w &&& d == d)

theorem isConstB_iff (d w : Nat) : isConstB d w = true ↔ IsConst d w := by
  simp [isConstB, IsConst]

def Avail (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  IsConst d w ∨ ∃ v ∈ bank, (v &&& d) = (w &&& d)

def availB (d : Nat) (bank : List Nat) (w : Nat) : Bool :=
  let m := w &&& d
  m == 0 || m == d || bank.any (fun v => (v &&& d) == m)

theorem availB_iff (d : Nat) (bank : List Nat) (w : Nat) :
    availB d bank w = true ↔ Avail d bank w := by
  simp [availB, Avail, IsConst, or_assoc]

def NatReach (d : Nat) (roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
    (∃ b a, bank = negD d a :: b ∧ NatReach d roots p b ∧ Avail d b a) ∨
    (∃ b a c op, bank = binD d op a c :: b ∧ NatReach d roots p b ∧ Avail d b a ∧ Avail d b c)

def Lower (d : Nat) (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, NatReach d roots p bank → Avail d bank T → L ≤ p

theorem mask256_bit (i : Nat) : mask256.testBit i = decide (i < 256) := by
  rw [mask256, Nat.testBit_two_pow_sub_one]

theorem negD_and_sub {d d1 : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d) (a : Nat) :
    negD d1 a &&& d = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [negD, Nat.testBit_and, Nat.testBit_xor] at *
  cases hi : d.testBit i <;> simp_all

theorem andD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    andD d1 a b &&& d = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [andD, Nat.testBit_and] at *
  cases hi : d.testBit i <;> simp_all

theorem orD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    orD d1 a b &&& d = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [orD, Nat.testBit_and, Nat.testBit_or] at *
  cases hi : d.testBit i <;> simp_all

theorem negD_const {d : Nat} (hd : d &&& mask256 = d) {a : Nat} (hc : IsConst d a) :
    IsConst d (negD d a) := by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i := congrArg (fun v => v.testBit i) h0
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i := congrArg (fun v => v.testBit i) h1
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_const_left {d : Nat} {a b : Nat} (op : Bool) (hc : IsConst d a) :
    (binD d op a b &&& d = 0) ∨ (binD d op a b &&& d = d) ∨ (binD d op a b &&& d = b &&& d) := by
  rcases hc with h0 | h1
  · cases op
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, andD, Nat.testBit_and, Nat.zero_testBit, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · cases op
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, andD, Nat.testBit_and, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_comm (d : Nat) (op : Bool) (a b : Nat) : binD d op a b = binD d op b a := by
  cases op <;> simp [binD, andD, orD, Nat.and_comm, Nat.or_comm]

theorem avail_cons {d : Nat} {bank : List Nat} (z w : Nat) (h : Avail d bank w) :
    Avail d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem avail_of_eq {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Avail d bank v) : Avail d bank w := by
  rcases h with (h0 | h1) | ⟨u, hu, hue⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr ⟨u, hu, hue.trans he⟩

theorem countP_kept_ge {α : Type} (p : α → Bool) (b : Bool) (a : α) (xs : List α) :
    xs.countP p ≤ (kept b a xs).countP p := by
  cases b <;> simp [kept, List.countP_cons] <;> split <;> omega

theorem contraction {d d1 T : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD d1 T s ws) {roots p bank}
    (hp : NatReach d roots p bank) (hs : ∀ w ∈ ws, Avail d bank w) :
    ∃ q next, NatReach d roots q next ∧ Avail d next T ∧
      q + ws.countP (isConstB d) ≤ p + s := by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false := by
      cases hc : isConstB d T with
      | false => rfl
      | true => exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p, bank, hp, hs T (by simp), by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q, next, hq, ht, hle⟩ := ih hp (fun w hw => hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q, next, hq, ht, hle⟩
  | @one s a r save _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    by_cases hca : IsConst d a
    · have hc_neg : IsConst d (negD d1 a) := by
        have e := negD_and_sub hd hsub a
        rcases negD_const hd hca with h0 | h1
        · exact Or.inl (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h0))
        · exact Or.inr (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h1))
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact Or.inl hc_neg
        · exact hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw])
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have h1 : isConstB d (negD d1 a) = true := (isConstB_iff _ _).2 hc_neg
      have h2 : isConstB d a = true := (isConstB_iff _ _).2 hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h1, h2, ite_true] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hreach' : NatReach d roots (p + 1) (negD d a :: bank) := Or.inl ⟨bank, a, rfl, hp, ha⟩
      have hneg_av : Avail d (negD d a :: bank) (negD d1 a) :=
        Or.inr ⟨negD d a, List.mem_cons_self, by rw [negD_and_sub hd hsub a]; simp [negD, Nat.and_assoc, Nat.and_self]⟩
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d (negD d a :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hneg_av
        · exact avail_cons _ _ (hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw]))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have h2 : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd ((isConstB_iff _ _).1 h) hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h2, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
  | @two s a b r conj ka kb _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    have hb := hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1 := if conj then andD d1 a b else orD d1 a b
    set z0 := binD d (!conj) a b
    have hz_eq : z1 &&& d = z0 &&& d := by
      cases conj
      · simp only [z1, z0, Bool.false_eq_true, ite_false, Bool.not_false, binD, ite_true]
        rw [orD_and_sub hsub]; simp [orD, Nat.and_assoc, Nat.and_self]
      · simp only [z1, z0, ite_true, Bool.not_true, Bool.false_eq_true, binD, ite_false]
        rw [andD_and_sub hsub]; simp [andD, Nat.and_assoc, Nat.and_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail d bank z1 := by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases binD_const_left (!conj) hca with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
        · dsimp only [z0]; rw [binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0) := by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true := (isConstB_iff _ _).2 hca
          rcases binD_const_left (!conj) hca with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1, hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b := by
              simp only [isConstB, hz_eq.trans he]
            simp [ha1, hzb]
        · have hb1 : isConstB d b = true := (isConstB_iff _ _).2 hcb
          have hz_eq' : z1 &&& d = binD d (!conj) b a &&& d := by rw [hz_eq, binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1, hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a := by
              simp only [isConstB, hz_eq'.trans he]
            simp [hb1, hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hna : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false := by
        cases h : isConstB d b with | false => rfl | true => exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach' : NatReach d roots (p + 1) (z0 :: bank) := Or.inr ⟨bank, a, b, !conj, rfl, hp, ha, hb⟩
      have hz_av : Avail d (z0 :: bank) z1 := Or.inr ⟨z0, List.mem_cons_self, hz_eq.symm⟩
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d (z0 :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons, hna, hnb, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩

-- Backward extraction: NatReach d roots p bank + Avail d bank T -> RunD d (T &&& d) s ws!
theorem mask_idemp (d w : Nat) : (w &&& d) &&& d = w &&& d := by
  simp [Nat.and_assoc, Nat.and_self]

theorem negD_mask (d a : Nat) : negD d (a &&& d) = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD, Nat.testBit_and, Nat.testBit_xor]
  cases d.testBit i <;> simp

theorem andD_mask (d a b : Nat) : andD d (a &&& d) (b &&& d) = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD, Nat.testBit_and]
  cases d.testBit i <;> simp

theorem orD_mask (d a b : Nat) : orD d (a &&& d) (b &&& d) = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD, Nat.testBit_and, Nat.testBit_or]
  cases d.testBit i <;> simp

theorem pull_one {d Y k ws} (hd : d &&& mask256 = d) (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a : Nat} (ha : Avail d b a) (hsub : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := negD d a
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hc
        rcases negD_const hd hc with h0 | h1
        · exact hzp.1 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h0)
        · exact hzp.2 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h1)
      obtain ⟨v, hv, hve⟩ := ha.resolve_left ha_nc
      set a' := a &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨v, hv, hve⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : negD d a' = z := negD_mask d a
      have h1 : RunD d Y k (negD d a' :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      have hne0 : negD d a' ≠ 0 := ez.symm ▸ hzp.1
      have hned : negD d a' ≠ d := ez.symm ▸ hzp.2
      by_cases ham : a' ∈ rest
      · have hp2 : rest.Perm (a' :: rest.erase a') := List.perm_cons_erase ham
        have h2 : RunD d Y k (negD d a' :: kept true a' (rest.erase a')) :=
          Run.perm (hp2.cons _) h1
        have hnm : negD d a' ∉ (a' :: rest.erase a') := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase (List.mem_of_mem_erase hm)
        refine ⟨k + 1, rest, le_rfl, hrest_nd, hrest_prop, hrest_sub, ?_⟩
        exact Run.perm hp2.symm (Run.one true hne0 hned hnm h2)
      · have h2 : RunD d Y k (negD d a' :: kept false a' rest) := h1
        have hnm : negD d a' ∉ (a' :: rest) := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase hm
        refine ⟨k + 1, a' :: rest, le_rfl, List.nodup_cons.2 ⟨ham, hrest_nd⟩, ?_, ?_, Run.one false hne0 hned hnm h2⟩
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_prop
          · exact hrest_prop w hw
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_mem
          · exact hrest_sub w hw
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem pull_two {d Y k ws} (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a c : Nat} (op : Bool) (ha : Avail d b a) (hc : Avail d b c)
    (hsub : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := binD d op a c
  have hz_mask : z &&& d = z := by cases op <;> simp [z, binD, andD, orD, Nat.and_assoc, Nat.and_self]
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hca
        rcases binD_const_left op hca with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans h0)
        · exact hzp.2 (hz_mask.symm.trans h1)
        · rcases hc with hcc | ⟨v, hv, hve⟩
          · rcases hcc with h0 | h1
            · exact hzp.1 (hz_mask.symm.trans (he.trans h0))
            · exact hzp.2 (hz_mask.symm.trans (he.trans h1))
          · exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he.symm.trans hz_mask)⟩)
      have hc_nc : ¬ IsConst d c := by
        intro hcc
        have hz' : z = binD d op c a := binD_comm d op a c
        rcases binD_const_left op hcc with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans (by rw [hz']; exact h0))
        · exact hzp.2 (hz_mask.symm.trans (by rw [hz']; exact h1))
        · rcases ha with hca | ⟨v, hv, hve⟩
          · exact absurd hca ha_nc
          · have he' : z &&& d = a &&& d := hz'.symm ▸ he
            exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he'.symm.trans hz_mask)⟩)
      obtain ⟨va, hva, hvae⟩ := ha.resolve_left ha_nc
      obtain ⟨vc, hvc, hvce⟩ := hc.resolve_left hc_nc
      set a' := a &&& d
      set c' := c &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨va, hva, hvae⟩
      have hc'_mem : c' ∈ b.map (· &&& d) := List.mem_map.2 ⟨vc, hvc, hvce⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d := ⟨fun e => hc_nc (Or.inl e), fun e => hc_nc (Or.inr e)⟩
      have hne_ac : a' ≠ c' := by
        intro heq
        dsimp only [a', c'] at heq
        have hz_eq : z = a' := by
          cases op
          · simp only [z, binD, Bool.false_eq_true, ite_false]; rw [← andD_mask, ← heq]; simp [andD, a', Nat.and_assoc, Nat.and_self]
          · simp only [z, binD, ite_true]; rw [← orD_mask, ← heq]; simp [orD, a', Nat.and_assoc, Nat.and_self]
        exact hzb (hz_eq ▸ ha'_mem)
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : (if !op then andD d a' c' else orD d a' c') = z := by
        cases op
        · simp [z, binD, a', c', andD_mask]
        · simp [z, binD, a', c', orD_mask]
      have h1 : RunD d Y k ((if !op then andD d a' c' else orD d a' c') :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      set ka := decide (a' ∈ rest)
      set kb := decide (c' ∈ rest)
      set tail := (rest.erase a').erase c'
      have htail_nd : tail.Nodup := (hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail := by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail := (hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail := by
        rw [mem_kept]; rintro (⟨_, h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)) := by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept, mem_kept, (hrest_nd.erase a').mem_erase_iff, hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka, kb]
      have h2 := Run.perm (hrest_perm.cons _) h1
      have hne0 : (if !op then andD d a' c' else orD d a' c') ≠ 0 := ez.symm ▸ hzp.1
      have hned : (if !op then andD d a' c' else orD d a' c') ≠ d := ez.symm ▸ hzp.2
      have hnm : (if !op then andD d a' c' else orD d a' c') ∉ (a' :: c' :: tail) := by
        rw [ez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (e ▸ ha'_mem)
        · exact hzb (e ▸ hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD d Y (k + 1) (a' :: c' :: tail) := Run.two (!op) ka kb hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac, hna_tail], List.nodup_cons.2 ⟨hnc_tail, htail_nd⟩⟩
      refine ⟨k + 1, a' :: c' :: tail, le_rfl, hnd3, ?_, ?_, h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem reach_to_run_aux {d : Nat} {roots : List Nat} {p bank} (hd : d &&& mask256 = d)
    (hr : NatReach d roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (· &&& d)) → RunD d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ roots.map (· &&& d)) ∧ RunD d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · have hsub' : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw; simp only [List.map_cons, negD, Nat.and_assoc, Nat.and_self] at this; exact this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_one hd hnd hprop hrun ha hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩
    · have hsub' : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw
        have ez : binD d op a c &&& d = binD d op a c := by cases op <;> simp [binD, andD, orD, Nat.and_assoc, Nat.and_self]
        simpa [List.map_cons, ez] using this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_two hnd hprop hrun op ha hc hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem reach_to_run {d : Nat} {roots : List Nat} {T : Nat} {p bank} (hd : d &&& mask256 = d)
    (hnc : ¬ IsConst d T) (hr : NatReach d roots p bank) (ha : Avail d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ roots.map (· &&& d)) ∧ RunD d (T &&& d) s ws := by
  obtain ⟨v, hv, hve⟩ := ha.resolve_left hnc
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (· &&& d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact List.mem_map.2 ⟨v, hv, hve⟩
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := reach_to_run_aux hd hr (List.nodup_singleton _) hprop hsub Run.done
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

-- Essential variable lemma + lower_slice + lower_base + lower_iso!
theorem runD_bits {d y s ws} (hd : d &&& mask256 = d) (h : RunD d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : mask256.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self
    intro w hm; cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
    · rcases hm with rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hm with rfl | rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; cases conj <;> cases ka <;> cases kb <;>
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm <;>
      rcases hm with rfl | hr <;>
      first | simp [andD, orD, ha, hb, hi, hj] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem runD_bits_le {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (hp.length_eq.trans hl) (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at hm
    rcases hm with rfl | hr
    · cases conj <;> simp only [andD, orD, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true] <;> grind
    · exact hw _ (by simp [hr])

theorem lower_base {d : Nat} {roots : List Nat} {T : Nat} (h : availB d roots T = false) :
    Lower d roots T 1 := by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht := (availB_iff d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p => omega

-- moveBits & lower_iso!
def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_zero (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) : moveBits tag d 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp

def applyMoves (ms : List (Nat × Nat)) (w : Nat) : Nat :=
  ms.foldl (fun acc p => moveBits p.1 p.2 acc) w

def moveOK256 (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) && (moveBits p.1 p.2 mask256 == mask256)

theorem applyMoves_hom (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b, applyMoves ms (a &&& b) = applyMoves ms a &&& applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ||| b) = applyMoves ms a ||| applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ^^^ b) = applyMoves ms a ^^^ applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256 := by
  induction ms with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    obtain ⟨⟨hz, hm⟩, hps⟩ := hok
    obtain ⟨hand, hor, hxor, h0, h256⟩ := ih hps
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves, List.foldl_cons, move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves, List.foldl_cons, hm]; exact h256

theorem move_invol (tag d w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1, ite_true, moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false := by
      have htd := congrArg (fun v : Nat => v.testBit (d + i)) h
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit] at htd
      have hge : d ≤ d + i := Nat.le_add_right d i
      have hsub : d + i - d = i := Nat.add_sub_cancel_left d i
      simp [hge, hsub, h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true := by
      simp [Nat.testBit_shiftLeft, Nat.le_add_right, Nat.add_sub_cancel_left, h1]
    simp [h2, h3, Nat.add_sub_cancel_left]
  · simp only [h1, ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2, ite_true, moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      simp [h2.2, Nat.add_sub_of_le h2.1]
    · simp [h1, h2, moved tag d i w h]

theorem applyMoves_inj (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms) := by
  induction ms with
  | nil => intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves, List.foldl_cons] at h
    have h1 := ih hok.2 h
    have := congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1, move_invol p.1 p.2 b hok.1.1] at this

theorem applyMoves_runD {d Y s} (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD d Y s ws) :
    RunD d Y s (ws.map (applyMoves ms)) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hinj := applyMoves_inj ms hok
  have hneg : ∀ a, applyMoves ms (negD d a) = negD d (applyMoves ms a) := fun a => by
    simp only [negD, hand, hxor, h256, hd]
  have hand' : ∀ a b, applyMoves ms (andD d a b) = andD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [andD, hand, hd]
  have hor' : ∀ a b, applyMoves ms (orD d a b) = orD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [orD, hand, hor, hd]
  rw [← hY]
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map _) ih
  | @one s a r save hne0 hned hnm _ ih =>
    have e1 : (negD d a :: kept save a r).map (applyMoves ms) =
        negD d (applyMoves ms a) :: kept save (applyMoves ms a) (r.map (applyMoves ms)) := by
      simp [kept_map, hneg]
    rw [e1] at ih
    refine Run.one save ?_ ?_ ?_ ih
    · intro e; rw [← hneg] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← hneg] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← hneg, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)
  | @two s a b r conj ka kb hne0 hned hnm _ ih =>
    have eop : applyMoves ms (if conj then andD d a b else orD d a b) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) := by
      cases conj <;> simp [hand', hor']
    have e1 : ((if conj then andD d a b else orD d a b) :: kept ka a (kept kb b r)).map (applyMoves ms) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))) := by
      simp [kept_map, eop]
    rw [e1] at ih
    refine Run.two conj ka kb ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop, ← List.map_cons, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)

theorem reach_map_moves (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2 : Nat} (hd : applyMoves ms d2 = d1)
    {roots1 roots2 : List Nat} (hroots : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r)) :
    ∀ {p bank}, NatReach d2 roots2 p bank →
      ∃ bank', NatReach d1 roots1 p bank' ∧ ∀ v ∈ bank, Avail d1 bank' (applyMoves ms v) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hav : ∀ {b b' w}, (∀ v ∈ b, Avail d1 b' (applyMoves ms v)) →
      Avail d2 b w → Avail d1 b' (applyMoves ms w) := by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v, hv, he⟩
    · exact Or.inl (Or.inl (by rw [← hd, ← hand, hz, h0]))
    · exact Or.inl (Or.inr (by rw [← hd, ← hand, h1]))
    · have hve : applyMoves ms v &&& d1 = applyMoves ms w &&& d1 := by rw [← hd, ← hand, ← hand, he]
      exact avail_of_eq hve (hbb v hv)
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1, rfl, hroots⟩
  | succ p ih =>
    intro bank hr
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha
      refine ⟨negD d1 (applyMoves ms a) :: b', Or.inl ⟨b', applyMoves ms a, rfl, hrb', ha'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨negD d1 (applyMoves ms a), List.mem_cons_self, by simp only [negD, hand, hxor, h256, hd]⟩
      · exact avail_cons _ _ (hbb v hv)
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha; have hc' := hav hbb hc
      refine ⟨binD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
        Or.inr ⟨b', applyMoves ms a, applyMoves ms c, op, rfl, hrb', ha', hc'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨binD d1 op (applyMoves ms a) (applyMoves ms c), List.mem_cons_self, by
          cases op <;> simp only [binD, andD, orD, hand, hor, hd, ite_true, ite_false, Bool.false_eq_true]⟩
      · exact avail_cons _ _ (hbb v hv)

theorem lower_iso {d1 d2 T1 T2 L : Nat} {roots1 roots2 : List Nat}
    (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r => availB d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower d1 roots1 T1 L) : Lower d2 roots2 T2 L := by
  obtain ⟨hand, _, _, h0, _⟩ := applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r) := fun r hr =>
    (availB_iff _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank', hrb', hbb⟩ := reach_map_moves ms hok hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v, hv, he⟩
  · exact Or.inl (Or.inl (by rw [← hT, ← hd, ← hand, hz, h0]))
  · exact Or.inl (Or.inr (by rw [← hT, ← hd, ← hand, ho]))
  · have hve : applyMoves ms v &&& d1 = T1 &&& d1 := by rw [← hT, ← hd, ← hand, ← hand, he]
    exact avail_of_eq hve (hbb v hv)

-- lower_slice!
def pairOK (d T : Nat) (p : Nat × Nat) : Bool :=
  d.testBit p.1 && d.testBit p.2 && (T.testBit p.1 != T.testBit p.2)

def essOK (d T : Nat) (roots : List Nat) (a : Nat) (p : Nat × Nat) : Bool :=
  pairOK d T p && roots.all (fun v => (v == a) || (v.testBit p.1 == v.testBit p.2))

theorem countP_ge_sublist (p : Nat → Bool) {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs, a ∈ ys) (hall : ∀ a ∈ xs, p a = true) :
    xs.length ≤ ys.countP p := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ⟨hna, hnd'⟩ := List.nodup_cons.1 hnd
    have ham : a ∈ ys := hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a) := List.perm_cons_erase ham
    rw [hperm.countP_eq, List.countP_cons, hall a List.mem_cons_self]
    have ih' := ih hnd' (fun x hx => by
      have hne : x ≠ a := fun e => hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true, List.length_cons]
    omega

theorem lower_slice {d dSub T TSub L : Nat} {roots rootsSub : List Nat}
    (hd : d &&& mask256 = d) (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB dSub rootsSub) = true)
    (singles : List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e => isConstB dSub e.1 && essOK d (T &&& d) (roots.map (· &&& d)) e.1 e.2) = true)
    (hprior : Lower dSub rootsSub TSub L) :
    Lower d roots T (L + singles.length) := by
  have hnc' : ¬ IsConst d T := fun h => by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T &&& d) := by
    intro h
    have e : (T &&& d) &&& dSub = TSub &&& dSub := by
      rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run hd hnc' hr ha
  have hws_av : ∀ w ∈ ws, Avail dSub rootsSub w := by
    intro w hw
    obtain ⟨r, hr_m, rfl⟩ := List.mem_map.1 (hws_sub w hw)
    have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub]) hav
  obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hncSub' hrun (p := 0) (bank := rootsSub) rfl hws_av
  have hTSub_av : Avail dSub next TSub := avail_of_eq (by
    rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht
  have hL : L ≤ q := hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst, a ∈ ws := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok (a', r1, r2) hm
    simp only [Bool.and_eq_true, essOK, pairOK, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
    obtain ⟨_, ⟨⟨hr1, hr2⟩, hdiff⟩, hiso⟩ := hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst, isConstB dSub a = true := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt := countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega

-- poolCut (compact 52-bit hint!) + covers + eval6 + bar!
def runChoices (d : Nat) (pool : List Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some pool
  | p + 1, bits =>
    let code := bits &&& 1023
    let op := code &&& 3
    let ia := (code >>> 2) &&& 15
    let ib := (code >>> 6) &&& 15
    if ia < pool.length && (op == 2 || ib < pool.length) then
      let a := pool.getD ia 0
      let b := pool.getD ib 0
      let w := if op == 2 then negD d a else binD d (op == 1) a b
      runChoices d (pool ++ [w]) p (bits >>> 10)
    else none

theorem getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem runChoices_sound {d : Nat} {roots : List Nat} :
    ∀ (p bits q : Nat) (bank pool result : List Nat),
      NatReach d roots q bank →
      (∀ v ∈ pool, Avail d bank v) →
      runChoices d pool p bits = some result →
      ∃ bank', NatReach d roots (q + p) bank' ∧ ∀ v ∈ result, Avail d bank' v
  | 0, _, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices, Option.some.injEq] at hok; subst hok; exact ⟨bank, hr, hsup⟩
  | p + 1, bits, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices] at hok
    split at hok
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hcond
      obtain ⟨hia, hopb⟩ := hcond
      set code := bits &&& 1023
      set op := code &&& 3
      set ia := (code >>> 2) &&& 15
      set ib := (code >>> 6) &&& 15
      set a := pool.getD ia 0
      set b := pool.getD ib 0
      set w := if op == 2 then negD d a else binD d (op == 1) a b
      have ha : Avail d bank a := hsup a (getD_mem hia)
      have hr1 : NatReach d roots (q + 1) (w :: bank) := by
        by_cases h2 : op = 2
        · simp only [w, h2, beq_self_eq_true, ite_true]
          exact Or.inl ⟨bank, a, rfl, hr, ha⟩
        · have hib : ib < pool.length := hopb.resolve_left h2
          have hb : Avail d bank b := hsup b (getD_mem hib)
          simp only [w, h2, beq_iff_eq, ite_false]
          exact Or.inr ⟨bank, a, b, (op == 1), rfl, hr, ha, hb⟩
      have hsup1 : ∀ v ∈ pool ++ [w], Avail d (w :: bank) v := by
        intro v hv; rcases List.mem_append.1 hv with hv | hv
        · exact avail_cons _ _ (hsup v hv)
        · rw [List.mem_singleton.1 hv]; exact Or.inr ⟨w, List.mem_cons_self, rfl⟩
      obtain ⟨bank', hrb', hsb'⟩ := runChoices_sound p (bits >>> 10) (q + 1) (w :: bank) (pool ++ [w]) result hr1 hsup1 hok
      exact ⟨bank', by simpa [Nat.add_assoc, Nat.add_comm 1] using hrb', hsb'⟩
    · contradiction

def checkCutEntry (dSub : Nat) (rootsSub : List Nat) (LSub s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  let p := (hint >>> 8) &&& 15
  decide (s + p < LSub + ws.countP (isConstB dSub)) &&
  match runChoices dSub rootsSub p (hint >>> 12) with
  | none => false
  | some pool => ws.all (availB dSub pool)

theorem checkCutEntry_sound {d dSub T TSub LSub s : Nat} {rootsSub ws : List Nat}
    (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower dSub rootsSub TSub LSub) (hint : Nat)
    (hchk : checkCutEntry dSub rootsSub LSub s ws hint = true) :
    ¬ RunD d (T &&& d) s ws := by
  intro hrun
  simp only [checkCutEntry, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hineq, hmatch⟩ := hchk
  cases hrc : runChoices dSub rootsSub ((hint >>> 8) &&& 15) (hint >>> 12) with
  | none => rw [hrc] at hmatch; contradiction
  | some pool =>
    rw [hrc] at hmatch
    have hsup0 : ∀ v ∈ rootsSub, Avail dSub rootsSub v := fun v hv => Or.inr ⟨v, hv, rfl⟩
    obtain ⟨bank, hrb, hsb⟩ := runChoices_sound _ _ 0 rootsSub rootsSub pool rfl hsup0 hrc
    simp only [Nat.zero_add] at hrb
    have hws_av : ∀ w ∈ ws, Avail dSub bank w := by
      intro w hw
      have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hmatch w hw)
      rcases hav with hc | ⟨v, hv, he⟩
      · exact Or.inl hc
      · exact avail_of_eq he (hsb v hv)
    have hnc' : ¬ IsConst dSub (T &&& d) := by
      intro h; have e : (T &&& d) &&& dSub = TSub &&& dSub := by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
      rcases h with h0 | h1
      · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
      · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
    obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hnc' hrun hrb hws_av
    have hL := hprior q next hq (avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht)
    omega

-- covers, eval6, hw256, hk, bsr, bar, bar_all!
def coversP (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then
    pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem coversP_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : coversP pairs s ws = true := by
  unfold coversP
  by_cases hl : ws.length = s + 1
  · simp only [hl, beq_self_eq_true, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := runD_bits_le h hl v u hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u <;> cases hv : w.testBit v <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  · simp only [hl, beq_iff_eq, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def unorientedCov (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem unorientedCov_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : unorientedCov pairs ws = true := by
  simp only [unorientedCov, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro ⟨u, v⟩ hm
  have hp := List.all_eq_true.1 hpairs (u, v) hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  by_contra! hall
  have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2, hp.2] at heq; contradiction

-- Fast bitmask-decorated covers (150x faster than per-pair testBit!)
def maskP (m : Nat) : Nat := 2 ^ m - 1

def projBit (rs : List Nat) (w : Nat) : Nat :=
  rs.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0

theorem projBit_testBit (rs : List Nat) (w : Nat) (i : Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false := by
  induction rs generalizing i with
  | nil => simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one, decide_false, Bool.false_and, Bool.false_or,
        List.length_cons, Nat.zero_lt_succ, dite_true, List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i), decide_true, Bool.true_and, Nat.add_sub_cancel,
        List.length_cons, Nat.succ_lt_succ_iff, List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false := by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1, Bool.or_false]; exact ih i

theorem projBit_negD {dm : Nat} (hd : dm &&& mask256 = dm) {rs : List Nat}
    (hrs : ∀ r ∈ rs, dm.testBit r = true) (w : Nat) :
    projBit rs (negD dm w) = projBit rs w ^^^ maskP rs.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_xor, projBit_testBit, maskP, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < rs.length
  · have hdr := hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true := by
      have := congrArg (fun v => v.testBit rs[i]) hd; simp [Nat.testBit_and, hdr] at this; exact this
    simp [hi, negD, hdr, hmr]
  · simp [hi]

theorem projBit_andD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (andD dm a b) = projBit rs a &&& projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_and, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, andD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem projBit_orD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (orD dm a b) = projBit rs a ||| projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_or, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, orD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs : List α) (acc i : Nat) :
    (xs.foldl (fun a x => a ||| g x) acc).testBit i = (acc.testBit i || xs.any (fun x => (g x).testBit i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.any_cons, Bool.or_assoc]

def coversD (mp s : Nat) (dws : List (Nat × Nat × Nat)) : Bool :=
  if dws.length == s + 1 then
    dws.foldl (fun acc d => acc ||| ((d.2.1 ^^^ mp) &&& d.2.2)) 0 == mp
  else
    dws.foldl (fun acc d => acc ||| (d.2.1 ^^^ d.2.2)) 0 == mp

theorem coversD_eq (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) :
    coversD (maskP pairs.length) s (ws.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) =
      coversP pairs s ws := by
  set r1s := pairs.map Prod.fst
  set r2s := pairs.map Prod.snd
  set mp := maskP pairs.length
  have hr1 : r1s.length = pairs.length := List.length_map _
  have hr2 : r2s.length = pairs.length := List.length_map _
  unfold coversD coversP
  simp only [List.length_map]
  split
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
        Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
            Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true, r1s, r2s, List.getElem_map]
          exact hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Nat.testBit_two_pow_sub_one, decide_false, Bool.xor_false, Bool.and_false, not_false_eq_true, Bool.false_eq_true]
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s, bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true, r1s, r2s, List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Bool.xor_false, Bool.false_eq_true, not_false_eq_true]

theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs : List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x == f a) = false := beq_false_of_ne (fun e => h (hinj e))
      have hx : (x == a) = false := beq_false_of_ne h
      simp [hf, hx, ih]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b, v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {dm y s ws} (h : RunD dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, andD, Nat.testBit_and, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, orD, Nat.testBit_and, Nat.testBit_or, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil => simp [sumBelow]
  | cons w ws ih => rw [sumBelow, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons, List.sum_cons]; omega

def scoreCheck (dm y s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  let a := code &&& 255
  let b := (code >>> 8) &&& 255
  let c := (code >>> 16) &&& 255
  let d := (code >>> 24) &&& 255
  let e := (code >>> 32) &&& 255
  let f := (code >>> 40) &&& 255
  dm.testBit a && dm.testBit b && dm.testBit c && dm.testBit d && dm.testBit e && dm.testBit f &&
    ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)

theorem scoreCheck_no {dm y s ws} (h : RunD dm y s ws) (code : Nat) :
    scoreCheck dm y s ws code = false := by
  unfold scoreCheck
  by_cases hok : dm.testBit (code &&& 255) = true ∧ dm.testBit ((code >>> 8) &&& 255) = true ∧
      dm.testBit ((code >>> 16) &&& 255) = true ∧ dm.testBit ((code >>> 24) &&& 255) = true ∧
      dm.testBit ((code >>> 32) &&& 255) = true ∧ dm.testBit ((code >>> 40) &&& 255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha, hb, hc, hd, he, hf, hl⟩ := hok
    simp only [ha, hb, hc, hd, he, hf, hl, beq_self_eq_true, Bool.true_and]
    by_contra hbad
    have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht := Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1, ht.1.1.1.1.1.1.2, ht.1.1.1.1.1.2, ht.1.1.1.1.2, ht.1.1.1.2, ht.1.1.2, ht.1.2⟩

def scr (dm y s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck dm y s zs)

theorem scr_no {dm y s : Nat} (pool : List Nat) {zs : List Nat}
    (h : RunD dm y s zs) : scr dm y s pool zs = false := by
  unfold scr; rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
  intro x _; rw [scoreCheck_no h x]; simp

def nextD (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(ws.contains w) &&
         (f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem nextD_one {dm y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h0 : negD dm a ≠ 0) (hd : negD dm a ≠ dm) (hnm : negD dm a ∉ (a :: rest))
    (h : RunD dm y s (negD dm a :: kept save a rest))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  have hnc : ws.contains (negD dm a) = false := by
    cases h : ws.contains (negD dm a) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (negD dm a != 0) = true := bne_iff_ne.2 h0
  have hdb : (negD dm a != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true => simp [kept] at ht hh; simp [ht, show 2 ≤ s + 2 - ws.length by omega]

theorem nextD_two_sorted {dm y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (if conj then andD dm a b else orD dm a b) = false := by
    cases h : ws.contains (if conj then andD dm a b else orD dm a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : ((if conj then andD dm a b else orD dm a b) != 0) = true := bne_iff_ne.2 h0
  have hdb : ((if conj then andD dm a b else orD dm a b) != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right; apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem nextD_two {dm y a b rest} {conj ka kb : Bool} {s ws} (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hab p h0 hd hnm h f hf
  · have he : (if conj then andD dm a b else orD dm a b) = (if conj then andD dm b a else orD dm b a) := by
      cases conj <;> simp [andD, orD, Nat.and_comm, Nat.or_comm]
    have hnm' : (if conj then andD dm b a else orD dm b a) ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _

theorem nextD_complete {dm y t ws} (h : RunD dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, RunD dm y s ys → f ys = true) →
      nextD dm (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_one p h0 hd hnm h f hf
  | two conj ka kb h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_two p h0 hd hnm h f hf

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i) (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi

def fld (T w i : Nat) : Nat :=
  (T >>> (w * i)) &&& (if w == 32 then 4294967295 else if w == 52 then 4503599627370495 else if w == 256 then mask256 else 2 ^ w - 1)

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw256 (seed w : Nat) : Nat :=
  let x := (((w % 170141183460469231731687303715884105727) ^^^ seed) * 0x9e3779b97f4a7c15f39cc0605cedc835) &&& 0xffffffffffffffffffffffffffffffff
  let y := ((x ^^^ (x >>> 61)) * 0xc2b2ae3d27d4eb4f165667b19e3779f9) &&& 0xffffffffffffffffffffffffffffffff
  y >>> 96

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw256 seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := hz seed zs &&& 4294967295

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def foundH (S : Nat → Nat → List Nat) (N : Nat → Nat) (htAt : Nat → Nat → Nat)
    (idxH : Nat → Nat → Nat) (s h : Nat) (zs : List Nat) : Bool :=
  let i := idxH s h
  decide (i < N s) && (htAt s i == h) && zs.isPerm (S s i)

def nextD_decor (dm mp : Nat) (slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  dws.any fun da =>
    let a := da.1
    let ra := dws.erase da
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
         let dw := (w, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
         (f (dw :: ra) || (slack ≥ 2 && f (dw :: da :: ra))))) ||
    ra.any fun db =>
      let b := db.1
      a ≤ b && (let r := ra.erase db
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
            let dw := if conj then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                      else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
            (f (dw :: r) || (slack ≥ 1 && (f (dw :: da :: r) || f (dw :: db :: r))) ||
              (slack ≥ 2 && f (dw :: da :: db :: r))))

theorem nextD_decor_gen (dm mp : Nat) (dec : Nat → Nat × Nat × Nat)
    (hfst : ∀ w, (dec w).1 = w)
    (hneg : ∀ a, (negD dm a, (dec a).2.1 ^^^ mp, (dec a).2.2 ^^^ mp) = dec (negD dm a))
    (hbin : ∀ (c : Bool) a b,
      (if c then (if c then andD dm a b else orD dm a b, (dec a).2.1 &&& (dec b).2.1, (dec a).2.2 &&& (dec b).2.2)
       else (if c then andD dm a b else orD dm a b, (dec a).2.1 ||| (dec b).2.1, (dec a).2.2 ||| (dec b).2.2)) =
      dec (if c then andD dm a b else orD dm a b))
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    nextD_decor dm mp slack (ws.map dec) g = nextD dm slack ws (fun zs => g (zs.map dec)) := by
  have hinj : Function.Injective dec := fun x y h => by rw [← hfst x, ← hfst y, h]
  have herase : ∀ (l : List Nat) x, (l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x => erase_map_inj dec hinj l x
  have hcont : ∀ (l : List Nat) w, (l.map dec).any (fun x => x.1 == w) = l.contains w := by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map, Function.comp_def, hfst, herase, hcont, hneg, hbin, List.map_cons]

theorem nextD_decor_eq {dm : Nat} (hd : dm &&& mask256 = dm)
    (pairs : List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true)
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    let dec := fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)
    nextD_decor dm (maskP pairs.length) slack (ws.map dec) g =
      nextD dm slack ws (fun zs => g (zs.map dec)) := by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro a
    simp only [dec, projBit_negD hd hr1, projBit_negD hd hr2, List.length_map]
  · intro c a b
    cases c <;> simp only [dec, ↓reduceIte, Bool.false_eq_true, projBit_andD hr1, projBit_andD hr2,
      projBit_orD hr1, projBit_orD hr2]

def colB (mp : Nat) (d : Bool) (p : Nat × Nat) : Nat :=
  if d then (p.1 ^^^ mp) &&& p.2 else p.1 ^^^ p.2

def addC (x : Nat) (c : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (c.1 ||| x, c.2.1 ||| (c.1 &&& x), c.2.2 ||| (c.2.1 &&& x))

def cov3 (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) : Nat × Nat × Nat :=
  dws.foldl (fun c dw => addC (colB mp d dw.2) c) (0, 0, 0)

def takeOne (c : Nat × Nat × Nat) (x : Nat) : Nat := (c.1 ^^^ x) ||| c.2.1
def takeTwo (c : Nat × Nat × Nat) (x y : Nat) : Nat :=
  (c.1 ^^^ (x ||| y)) ||| (c.2.1 &&& (x ^^^ y)) ||| c.2.2

theorem cov3_bit (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) (i : Nat) :
    let k := dws.countP (fun dw => (colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k) := by
  have hgen : ∀ (xs : List (Nat × Nat × Nat)) (c : Nat × Nat × Nat) (k0 : Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k := k0 + xs.countP (fun dw => (colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k) := by
    intro xs
    induction xs with
    | nil => intro c k0 ⟨h1, h2, h3⟩; simp [h1, h2, h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1, h2, h3⟩
      simp only [List.foldl_cons, List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) := by
        simp only [addC, Nat.testBit_or, Nat.testBit_and, h1, h2, h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb, Nat.le_add_left]
      have ih' := ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc, Nat.add_comm 1] using ih'
  simpa only [cov3, Nat.zero_testBit, Nat.zero_add] using hgen dws (0, 0, 0) 0 (by simp)

theorem cov3_perm (mp : Nat) (d : Bool) {xs ys : List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys := by
  have heq : ∀ i, (cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i := by
    intro i
    obtain ⟨a1, a2, a3⟩ := cov3_bit mp d xs i
    obtain ⟨b1, b2, b3⟩ := cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i => (heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.2)

theorem takeOne_eq (mp : Nat) (d : Bool) (a : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, _⟩ := cov3_bit mp d (a :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeOne, Nat.testBit_or, Nat.testBit_xor, h1, h2, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, decide_true, Bool.xor_false, Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 1 ≤ k + 3 by omega,
      decide_true, Bool.xor_true, Bool.or_true, Bool.or_false]

theorem takeTwo_eq (mp : Nat) (d : Bool) (a b : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, h3⟩ := cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeTwo, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, h1, h2, h3, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega, show 2 ≤ k + 3 + 1 + 1 by omega, show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true, Bool.xor_true, Bool.xor_false, Bool.or_true, Bool.or_false, Bool.and_true, Bool.and_false])

theorem cov3_coversD (mp s : Nat) (dw : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    let d := (dw :: rest).length == s + 1
    ((cov3 mp d rest).1 ||| colB mp d dw.2 == mp) = coversD mp s (dw :: rest) := by
  intro d
  have e : ∀ b : Bool, ((cov3 mp b rest).1 ||| colB mp b dw.2) =
      (dw :: rest).foldl (fun acc x => acc ||| colB mp b x.2) 0 := by
    intro b; apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1, _, _⟩ := cov3_bit mp b rest i
    rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, Nat.testBit_or, h1, List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw => (colB mp b dw.2).testBit i)) =
        rest.any (fun x => (colB mp b x.2).testBit i) := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.succ_le_iff, List.countP_pos_iff, List.any_eq_true]
    rw [hp, Bool.or_comm]
  have hf : ∀ b : Bool, (cov3 mp b rest).1 ||| colB mp b dw.2 =
      (dw :: rest).foldl (fun acc x => acc ||| (if b then (x.2.1 ^^^ mp) &&& x.2.2 else x.2.1 ^^^ x.2.2)) 0 := by
    intro b; simpa only [colB] using e b
  unfold coversD
  dsimp only [d]
  cases (dw :: rest).length == s + 1
  · simpa only [Bool.false_eq_true, ↓reduceIte] using congrArg (· == mp) (hf false)
  · simpa only [↓reduceIte] using congrArg (· == mp) (hf true)

def nextD_cov (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  let len := dws.length
  let covF := cov3 mp false dws
  let covT := cov3 mp true dws
  let du0 := len == s + 1
  let du1 := len + 1 == s + 1
  let db0 := len - 1 == s + 1
  let db1 := len == s + 1
  let db2 := len + 1 == s + 1
  dws.any fun da =>
    let a := da.1
    (slack ≥ 1 &&
      (let pneg := (da.2.1 ^^^ mp, da.2.2 ^^^ mp)
       let uok0 := (takeOne (if du0 then covT else covF) (colB mp du0 da.2) ||| colB mp du0 pneg) == mp
       let uok1 := slack ≥ 2 && (((if du1 then covT.1 else covF.1) ||| colB mp du1 pneg) == mp)
       (uok0 || uok1) &&
       (let w := negD dm a
        w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
          let dw := (w, pneg)
          let ra := dws.erase da
          ((uok0 && f (dw :: ra)) || (uok1 && f (dw :: da :: ra)))))) ||
    (dws.erase da).any fun db =>
      let b := db.1
      a ≤ b &&
        [false, true].any fun conj =>
          let pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                    else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
          let ok0 := (takeTwo (if db0 then covT else covF) (colB mp db0 da.2) (colB mp db0 db.2) ||| colB mp db0 pz) == mp
          let ok1a := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 db.2) ||| colB mp db1 pz) == mp)
          let ok1b := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 da.2) ||| colB mp db1 pz) == mp)
          let ok2 := slack ≥ 2 && (((if db2 then covT.1 else covF.1) ||| colB mp db2 pz) == mp)
          (ok0 || ok1a || ok1b || ok2) &&
          (let w := if conj then andD dm a b else orD dm a b
           w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
             let dw := (w, pz)
             let r := (dws.erase da).erase db
             ((ok0 && f (dw :: r)) || (ok1a && f (dw :: da :: r)) || (ok1b && f (dw :: db :: r)) || (ok2 && f (dw :: da :: db :: r))))

theorem nextD_cov_eq (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (g : List (Nat × Nat × Nat) → Bool) :
    nextD_cov dm mp s slack dws g =
      nextD_decor dm mp slack dws (fun dzs => coversD mp s dzs && g dzs) := by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      refine ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra
        rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 :
          (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra)
        rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hu0, hf0⟩ | ⟨⟨hsl2, hu1⟩, hf1⟩
      · left; exact ⟨hcov0 ▸ hu0, hf0⟩
      · right; exact ⟨hsl2, hcov1 ▸ hu1, hf1⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw]
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r
      rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r)
      rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r)
      rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r)
      rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with ((⟨hu0, hf0⟩ | ⟨⟨hsl1, hu1a⟩, hf1a⟩) | ⟨⟨hsl1, hu1b⟩, hf1b⟩) | ⟨⟨hsl2, hu2⟩, hf2⟩
      · left; left; exact ⟨hcov0' ▸ hu0, hf0⟩
      · left; right; exact ⟨hsl1, Or.inl ⟨hcov1a' ▸ hu1a, hf1a⟩⟩
      · left; right; exact ⟨hsl1, Or.inr ⟨hcov1b' ▸ hu1b, hf1b⟩⟩
      · right; exact ⟨hsl2, hcov2' ▸ hu2, hf2⟩
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra; rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra); rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hc0, hg0⟩ | ⟨hsl2, hc1, hg1⟩
      · have hu0 : ((takeOne _ _ ||| _) == mp) = true := hcov0.symm ▸ hc0
        exact ⟨hsl, Or.inl hu0, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl ⟨hu0, hg0⟩⟩
      · have hu1 : ((_ ||| _) == mp) = true := hcov1.symm ▸ hc1
        exact ⟨hsl, Or.inr ⟨hsl2, hu1⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, hu1⟩, hg1⟩⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw] at hfx
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r; rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r); rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r); rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r); rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with (⟨hc0, hg0⟩ | ⟨hsl1, ⟨hc1a, hg1a⟩ | ⟨hc1b, hg1b⟩⟩) | ⟨hsl2, hc2', hg2⟩
      · have u0 : ((takeTwo _ _ _ ||| _) == mp) = true := hcov0'.symm ▸ hc0
        exact ⟨Or.inl (Or.inl (Or.inl u0)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inl ⟨u0, hg0⟩))⟩
      · have u1a : ((takeOne _ _ ||| _) == mp) = true := hcov1a'.symm ▸ hc1a
        exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1, u1a⟩)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inr ⟨⟨hsl1, u1a⟩, hg1a⟩))⟩
      · have u1b : ((takeOne _ _ ||| _) == mp) = true := hcov1b'.symm ▸ hc1b
        exact ⟨Or.inl (Or.inr ⟨hsl1, u1b⟩), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inr ⟨⟨hsl1, u1b⟩, hg1b⟩)⟩
      · have u2 : ((_ ||| _) == mp) = true := hcov2'.symm ▸ hc2'
        exact ⟨Or.inr ⟨hsl2, u2⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, u2⟩, hg2⟩⟩

def bar (dm Y : Nat) (pairs : List (Nat × Nat)) (r1s r2s : List Nat) (mp : Nat)
    (SD : Nat → Nat → List (Nat × Nat × Nat)) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (htAt idxH : Nat → Nat → Nat)
    (ori : List Nat → List Nat) (seed : Nat) (pool : List Nat) (cutHitH : Nat → Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Y])
  | s + 1, i =>
    let dws := SD (s + 1) i
    !(nextD_cov dm mp s (s + 2 - dws.length) dws fun dzs =>
        let zs := dzs.map Prod.fst
        !(scr dm Y s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))

theorem bar_all {dm T : Nat} {pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH cap}
    (hd : dm &&& mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j, SD s j = (S s j).map (fun w => (w, projBit r1s w, projBit r2s w)))
    (hpairs : pairs.all (fun p => dm.testBit p.1 && dm.testBit p.2 && !(T &&& dm).testBit p.1 && (T &&& dm).testBit p.2) = true)
    (hr : ∀ {u ys}, RunD dm (T &&& dm) u ys → RunD dm (T &&& dm) u (ori ys))
    (hcut : ∀ {u ys}, cutHitH u (hk seed ys) ys = true → ¬ RunD dm (T &&& dm) u ys)
    (hc : ∀ s ≤ cap, ∀ i < N s, bar dm (T &&& dm) pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RunD dm (T &&& dm) s (S s i) := by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb := hc s hs i hi
    cases s with
    | zero => simp [bar, zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (zs : List Nat) :=
        coversP pairs s zs && !(scr dm (T &&& dm) s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, Bool.not_false, Bool.true_and, foundH]
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        rintro ⟨hj, _⟩
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN := nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD, List.length_map, nextD_cov_eq, nextD_decor_eq hd pairs hr1 hr2] at hb
      have hFeq : (fun zs => coversD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) &&
          (let zs' := (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr dm (T &&& dm) s pool zs') &&
           (let cz := ori zs'
            let h := hk seed cz
            !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction

def pickMin (seed : Nat) (orig : List Nat) : List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [], best, _ => best
  | ms :: rest, best, bestH =>
    let img := orig.map (applyMoves ms)
    let h := hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH

theorem pickMin_runD {dm Y u} (seed : Nat) (orig : List Nat) (h0 : RunD dm Y u orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all moveOK256 && (applyMoves ms dm == dm) && (applyMoves ms Y == Y)) = true →
      RunD dm Y u best →
      RunD dm Y u (pickMin seed orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb

-- Bridge: HasCircuitSize 8 fG s -> Lower mask256 xs256 (enc256 fG) lb -> lb <= s!
def gvN (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => andD mask256 (w.getD i 0) acc) mask256
  | .or  => g.inputs.foldr (fun i acc => orD mask256 (w.getD i 0) acc) 0
  | .not => match g.inputs with | [] => mask256 | i :: _ => negD mask256 (w.getD i 0)
  | _ => 0

def execN (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [gvN l g]) w

theorem gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i => (w.map (·.testBit r)).getD i false) := by
  have hm : mask256.testBit r = true := by simp [mask256_bit, hr]
  have hgd : ∀ i, (w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r := by
    intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? with | none => simp | some v => rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.all_cons, id_eq, andD, Nat.testBit_and, Nat.testBit_and, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.any_cons, id_eq, orD, Nat.testBit_and, Nat.testBit_or, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    cases g.inputs with
    | nil => simp [hm]
    | cons i l => simp only [List.map_cons, List.headD_cons, negD, Nat.testBit_and, Nat.testBit_xor, hm, Bool.and_true, Bool.xor_true, hgd]

theorem execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (·.testBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [execN, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]

theorem execN_reach (gs : List Gate) (roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (p : Nat) (w bank : List Nat), NatReach mask256 roots p bank →
      (∀ v ∈ w, Avail mask256 bank v) →
      ∃ p' bank', p' ≤ p + gs.length ∧ NatReach mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w, Avail mask256 bank' v := by
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by omega, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, Avail mask256 bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    -- Use gvN_step directly on roots=roots:
    have hstep : ∃ p1 bank1, p1 ≤ p + 1 ∧ NatReach mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g], Avail mask256 bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, andD mask256 a mask256 &&& mask256 = a &&& mask256 := fun a => by
        simp [andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, orD mask256 a 0 &&& mask256 = a &&& mask256 := fun a => by
        simp [orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, Avail mask256 (z :: bank) v) := fun z v hv => avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 false (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, false, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by simp [binD, andD, Nat.and_assoc, Nat.and_self]⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 true (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, true, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [binD, orD]; cases mask256.testBit r <;> simp⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, l⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · refine ⟨p + 1, negD mask256 (w.getD i 0) :: bank, le_rfl,
            Or.inl ⟨bank, _, rfl, hr, hav_gd i⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi]; exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    exact ⟨p2, bank2, by simp; omega, hr2, hsup2⟩

def xs256 : List Nat :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]

def pt8 (r : Nat) : Fin 8 → Bool := fun i => r.testBit i.val

theorem xs256_bits : ∀ r : Fin 256, xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val) := by
  decide +kernel

theorem lower_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 256, T.testBit r.val = f (pt8 r.val))
    (hlow : Lower mask256 xs256 T lb) :
    ∀ t : ℕ, HasCircuitSize 8 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ xs256, Avail mask256 xs256 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates xs256 hfan 0 xs256 xs256 rfl hsup0
  have hout : (execN C.gates xs256).getD C.output 0 &&& mask256 = T &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit C.gates xs256 r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r) := hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hav_out : Avail mask256 bank ((execN C.gates xs256).getD C.output 0) := by
    by_cases hi : C.output < (execN C.gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := hlow p bank hr (avail_of_eq hout hav_out)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def dom_0 : Nat := 0x555500000000
def goal_0 : Nat := 0x544000000000
def roots_0 : List Nat := [0x444400000000, 0x505000000000, 0x550000000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(34, 38), (34, 42), (36, 38), (36, 44), (40, 42), (40, 44)]
def r1sG : List Nat := [34, 34, 36, 36, 40, 40]
def r2sG : List Nat := [38, 42, 38, 44, 42, 44]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x95ad01e5
  | 3, 0 => 0x95ad01e5
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55000000000000005050000000000000444400000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x243
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 10
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x30303
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ab57
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 6 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 6 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 3 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_0 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_0 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_0 == dom_0) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_0 goalM u ys) : RunD dom_0 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_0 roots_0 goal_0 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_0 goal_0 := by
    have h0 : isConstB dom_0 goal_0 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_0

theorem low_0 : Lower dom_0 roots_0 goal_0 4 := S_0.noCircuit

def dom_1 : Nat := 0x555500005555
def goal_1 : Nat := 0x544000005040
def roots_1 : List Nat := [0x444400004444, 0x505000005050, 0x550000005500, 0x555500000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x555500000000, 10, 42)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0x333300003333
def goal_2 : Nat := 0x322000003200
def roots_2 : List Nat := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xffff00000000
def goal_3 : Nat := 0xfee000000000
def roots_3 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa00000000, 36, 37)] (by decide +kernel) (by decide +kernel) low_0

def dom_4 : Nat := 0xffff
def goal_4 : Nat := 0xfac0
def roots_4 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

namespace S_4
def pairsG : List (Nat × Nat) := [(1, 9), (2, 6), (3, 7), (3, 11), (4, 6), (4, 12), (5, 7), (5, 13), (8, 9), (8, 12), (10, 11), (10, 14)]
def r1sG : List Nat := [1, 2, 3, 3, 4, 4, 5, 5, 8, 8, 10, 10]
def r2sG : List Nat := [9, 6, 7, 11, 6, 12, 7, 13, 9, 12, 11, 14]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_4.map (· &&& dom_4)
def goalM : Nat := goal_4 &&& dom_4
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xa8d11512
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000f0f0000000000000cccc000000000000aaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf000f0c0e0cd
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfa9af6c5e5cd
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_4 == dom_4) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_4 goalM u ys) : RunD dom_4 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_4 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_4 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_4 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_4 roots_4 goal_4 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_4 goal_4 := by
    have h0 : isConstB dom_4 goal_4 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_4

theorem low_4 : Lower dom_4 roots_4 goal_4 4 := S_4.noCircuit

def dom_5 : Nat := 0xffff0000ffff
def goal_5 : Nat := 0xfee00000fac0
def roots_5 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

namespace S_5
def pairsG : List (Nat × Nat) := [(1, 9), (2, 6), (3, 7), (3, 11), (4, 6), (4, 12), (5, 7), (5, 13), (5, 37), (8, 9), (8, 12), (10, 11), (10, 14), (10, 42), (33, 37), (33, 41), (34, 38), (34, 42), (35, 39), (35, 43), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [1, 2, 3, 3, 4, 4, 5, 5, 5, 8, 8, 10, 10, 10, 33, 33, 34, 34, 35, 35, 36, 36, 36, 40, 40, 40]
def r2sG : List Nat := [9, 6, 7, 11, 6, 12, 7, 13, 37, 9, 12, 11, 14, 42, 37, 41, 38, 42, 39, 43, 37, 38, 44, 41, 42, 44]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_5.map (· &&& dom_5)
def goalM : Nat := goal_5 &&& dom_5
def NN : Nat → Nat
  | 3 => 4
  | 4 => 20
  | 5 => 43
  | 6 => 11
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x9a89e25d67395bb063052a2f163c700e
  | 4, 0 => 0xd50be63bc8cf0947b426338faab22998a74353429b4a1bc57bc61f6560b42ebd54a0aba752a27816506c7a264fada6a44364d45a3ac91e4836f864f02700a59f1be3c7c314d1a68c1209bd7c0fdea189
  | 5, 0 => 0xeea8376dd4c9adb2c76e9974bec67373bc534931b47f2618b24cbc00a60109aca39e46b6947e0d9e88e2183d772c77946fa9a6b36ee798d96d61a0dd6d1e8b116949f7d6692d6f5c686e9bda685c28de6713f9e666e3b08e5ba073fa51aa8be74fada6a447cd236842c1d77f42829c104279b1823d9dc136372650b9358018f52bcc03e12acab2b22a48ff9525a509331ce122ff1b2929df1ae8b27a125878620fdea1890da784ce040f1dd3
  | 6, 0 => 0xa7da18faa1c0b4b8a12a17a37445a6b56949f7d6686e9bda5ba073fa5b61388b160058940f1fce070da784ce
  | 7, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfff00000fff00000f0f00000f0f0000030300000303000000ff000000ff000000f0000000f000000033000000330000000f0000000f000000000000ffff
  | 0, 1 => 0xcccc0000cccc0000ccc00000ccc00000aaff0000aaff0000aaaa0000aaaa0000aaa00000aaa0000055550000555500003333000033330000111100001111
  | 0, 2 => 0xf0c00000f0c00000f0a00000f0a00000f0000000f0000000eeee0000eeee0000eeee000000000000ee000000ee000000ccff0000ccff0000cccf0000cccf
  | 0, 3 => 0xfcfc000000000000fccc0000fccc0000fc000000fc000000fafa0000fafa0000faea0000faea0000faaa0000faaa0000fa000000fa000000f0f00000f0f0
  | 0, 4 => 0xffaa0000ffaa0000ffaa0000aaaa0000ffaa000000000000ff0f0000ff0f0000ff000000ff000000ff00000000000000fe000000fe000000fcfc0000fcfc
  | 0, 5 => 0xffff000000000000fffa0000fffa0000fff00000fff00000fff00000ff000000fff0000000000000ffee0000ffee0000ffcc0000ffcc0000ffcc0000cccc
  | 0, 6 => 0xffff0000f000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xbd538b4c2d68f4bed79a495960f4
  | 4, 0, 0 => 0xbe160f316fa5848c5be379a616b8d83cb5c2d54f316fb5e60c5bed795316fb553cc5be3817316f8db60f5a63613316f8d840c5bed54f2d708de60c5bed64f316f8de60c5
  | 4, 0, 1 => 0xb6b54f316fa5d60c5be360e2d658dc60f5
  | 5, 0, 0 => 0x2f60f2845bec8d83cc6be36113cc6bea8d83cc6bed8d83cb6beda583cc6be36583cc60236133cc5be68d83cc6bee8d83cc602360c2405be78dc60f6be48d83cc602f8de60c5be360f30460258d83cc5
  | 5, 0, 1 => 0xbe88d83cc602f60c2445be360f3076c236153cc6be36983cc6bed8d83cc6be379854c6be36153cc6be360f3036bed8d53cc68e07d83cc602f8cf3065be360f305602fb553cc5be371850f602f3cc1845
  | 5, 0, 2 => 0xb6b8d83cc602f8d82895be360f34c6be360f30868d85133cc6be360f3016be36163cc6be36123cc6be360f302602b8d83cc50183cc1005
  | 6, 0, 0 => 0xbe37183cc602360f3005be36143cc6be78d83cc6bed8d83cc6be36153cc602f8cf306502f8d83ca5be38983cc602f8d83cc5be360f3046
  | 7, 0, 0 => 0x2f8d83cc5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 28
  | 4 => 34
  | 5 => 40
  | 6 => 40
  | 7 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfffffff8ffe0fe0318047fc1ff1c007c070c1f103f003c003fff
  | 0, 1 => 0x3ce0380038001ff07fc0cc1cd0000703f33e32fc31fc7f00630
  | 0, 2 => 0x1c000000000ff9cf03f00000038001ffe7fc0ff80f
  | 0, 3 => 0x1fc00000f380e000e0007cc1fd03307340cc1cd00000007001f0
  | 0, 4 => 0xe33ff378cc1cde3300038ffe0fe00f803800000000e0007f39fe
  | 0, 5 => 0xfff0003fcfffdfc0ffc3f03e00fc000038fffcfe3cf83b8f380e
  | 0, 6 => 0x3ffc000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x6ffad7d8aaa0920208043541560d505581041000000000001eff
  | 0, 1 => 0x4bce1792f385e2f72f7c9ccbcd2732f37633432b431e86400420
  | 0, 2 => 0x99453da5455e49005281bffbdf6ff84018aba894fde5792f385e
  | 0, 3 => 0xdfd84036f3cfed28f2a2fddfffbf77ffedcdfedb227aa67555f6
  | 0, 4 => 0xf7bffb7deebcdf7b8403cabea9f2afaa7caa000f2afaa77f7dfe
  | 0, 5 => 0xfff8403fffffffffffffffffa9fff8403fffffffbefbffefb85e
  | 0, 6 => 0x3fff5a0
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 49 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 49 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 49 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 49 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 6 0) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 6 0) :: stateWiresS n (ids >>> 6)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 27
  | 5 => 55
  | 6 => 8
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xdb55ef26c5f6c2bdc4b84e53b961b83fa2620da29a779d7598c851bd947e0d9e8d1d3c5c773e3a2d6f201b346240228950b5378c4ece10be4d93d8014d5d579a482e67d43130cfe9290acf4c1d0589b2188b6e561412d30a0f1fce070a238d7e06167cc605f59e8c040f1dd3
  | 5, 0 => 0xf0f748ecdb55ef26bcebd86cbcb2dc0bb5290c62a9d70da4a7da18faa1c0b4b8a12a17a39f39fa529e1dee0996c902e47ea52a9a7445a6b572657d5c71f40ace71628380711921746eaeba026c7e6f8d6b7180a367ae8f756594bfe25b61388b598d301e580158be5400e09b53d6c8e351635f9050d47de64d7877b948143a50469eff263f2d04c034e7896733011e373042d04d2fef2b282f733ea92e1b67d12c9d5086270b03de2261f78e21c0242c1b171b191782a15e160058941412d30a0f1fce070f01d2a50c4743590afba44c085ae9b3072d757703b0c7d7
  | 6, 0 => 0x9f39fa527ea52a9a72657d5c6b7180a36594bfe24d7877b92fef2b28270b03de
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x800000300404000033104040000000000cc010000000cc410100000800003000008000003004000000300000400000310404000000000080000000000c00002000000c8100
  | 5, 0 => 0x20000080000200000c000010000080000000000000003000000000010000000000100000800003000008000000000000000000000c000020000040000200000800000000008c41010000000000100000c00002
  | 5, 1 => 0x20000000000300000c00001014408000000000080000000000000001000004000020000000000100000000003000004000010000080000100000400001
  | 6, 0 => 0x2000004000010000040000000000800002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 3 => checkCutEntry dom_4 roots_4 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_5 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_5 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_5 == dom_5) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_5 goalM u ys) : RunD dom_5 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_5 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 4 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 4 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 4 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_8 : ∀ i, 8 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_16 : ∀ i, 16 ≤ i → i < 20 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 16 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 20 → Z 4 i = true := range_split z4_0 (range_split z4_8 (z4_16))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_16 : ∀ i, 16 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_24 : ∀ i, 24 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_32 : ∀ i, 32 ≤ i → i < 40 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_40 : ∀ i, 40 ≤ i → i < 43 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 40 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 43 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (z5_40)))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_8 : ∀ i, 8 ≤ i → i < 11 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 8 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 11 → Z 6 i = true := range_split z6_0 (z6_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := z7_0
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_5 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_5 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_5 roots_5 goal_5 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_5 goal_5 := by
    have h0 : isConstB dom_5 goal_5 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_5

theorem low_5 : Lower dom_5 roots_5 goal_5 8 := S_5.noCircuit

def dom_6 : Nat := 0x55555555
def goal_6 : Nat := 0x54445040
def roots_6 : List Nat := [0x44444444, 0x50505050, 0x55005500, 0x55550000]

theorem low_6 : Lower dom_6 roots_6 goal_6 4 :=
  lower_iso [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_7 : Nat := 0xf0f0f0f
def goal_7 : Nat := 0xe0e0a00
def roots_7 : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]

theorem low_7 : Lower dom_7 roots_7 goal_7 4 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_8 : Nat := 0xff00ff
def goal_8 : Nat := 0xee00c0
def roots_8 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

theorem low_8 : Lower dom_8 roots_8 goal_8 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_9 : Nat := 0xffffffff
def goal_9 : Nat := 0xfeeefac0
def roots_9 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_9
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (2, 6), (2, 18), (3, 7), (3, 11), (3, 19), (4, 6), (4, 12), (5, 7), (5, 13), (5, 21), (8, 9), (8, 12), (10, 11), (10, 14), (10, 26), (16, 17), (16, 18), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 8, 8, 10, 10, 10, 16, 16, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [9, 17, 6, 18, 7, 11, 19, 6, 12, 7, 13, 21, 9, 12, 11, 14, 26, 17, 18, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_9.map (· &&& dom_9)
def goalM : Nat := goal_9 &&& dom_9
def NN : Nat → Nat
  | 5 => 4
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xac05225e3a6b8d41276bea43206585ea
  | 6, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffaaaa00000000ffff000000000000ff00ff0000000000fafafafa00000000f0f0f0f000000000cccccccc00000000aaaaaaaa0000000055555555
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x1ab4546ad05fab45b58d16
  | 6, 0, 0 => 0x6ad15
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xff0739ff8000383e000380ff31c07c000701f0001ce7fff18c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xffaf3dffc212bc3ea437afff79c57ca2570bf094bce7b5a18c
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 25 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 25 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 8 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 4
  | 5 => 3
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xac05225e5e1d4aa82637312d25e0cf66
  | 5, 0 => 0x25303d371b8a7ef10241d3e1
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x100000000002
  | 5, 0 => 0x100000c00001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 3 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_6 roots_6 4 s ws hint
  | 1 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 2 => checkCutEntry dom_8 roots_8 4 s ws hint
  | 3 => checkCutEntry dom_4 roots_4 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_9 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_9 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_9 == dom_9) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_9 goalM u ys) : RunD dom_9 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_9 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_9 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_9 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_9 roots_9 goal_9 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_9 goal_9 := by
    have h0 : isConstB dom_9 goal_9 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_9

theorem low_9 : Lower dom_9 roots_9 goal_9 7 := S_9.noCircuit

def dom_10 : Nat := 0x5555555555555555
def goal_10 : Nat := 0x5444544054445040
def roots_10 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000055550000, 2, 18)] (by decide +kernel) (by decide +kernel) low_1

def dom_11 : Nat := 0x3333333333333333
def goal_11 : Nat := 0x3222322032223200
def roots_11 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10

def dom_12 : Nat := 0x5555555500000000
def goal_12 : Nat := 0x5444544000000000
def roots_12 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 34, 50)] (by decide +kernel) (by decide +kernel) low_0

def dom_13 : Nat := 0xffffffff00000000
def goal_13 : Nat := 0xfeeefee000000000
def roots_13 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000, 36, 37)] (by decide +kernel) (by decide +kernel) low_12

def dom_14 : Nat := 0xf0f0f0f0f0f0f0f
def goal_14 : Nat := 0xe0e0e000e0e0a00
def roots_14 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f00000000, 10, 42)] (by decide +kernel) (by decide +kernel) low_7

def dom_15 : Nat := 0xff00ff00ff00ff
def goal_15 : Nat := 0xee00e000ee00c0
def roots_15 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14

def dom_16 : Nat := 0xffffffffffffffff
def goal_16 : Nat := 0xfeeefee0feeefac0
def roots_16 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_16
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (2, 6), (2, 18), (3, 7), (3, 11), (3, 19), (4, 6), (4, 12), (5, 7), (5, 13), (5, 21), (5, 37), (8, 9), (8, 12), (10, 11), (10, 14), (10, 26), (10, 42), (16, 17), (16, 18), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (33, 37), (33, 41), (33, 49), (34, 38), (34, 42), (34, 50), (35, 39), (35, 43), (35, 51), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 5, 8, 8, 10, 10, 10, 10, 16, 16, 20, 20, 20, 24, 24, 24, 33, 33, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 40, 40, 40, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [9, 17, 6, 18, 7, 11, 19, 6, 12, 7, 13, 21, 37, 9, 12, 11, 14, 26, 42, 17, 18, 21, 22, 28, 25, 26, 28, 37, 41, 49, 38, 42, 50, 39, 43, 51, 37, 38, 44, 41, 42, 44, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_16.map (· &&& dom_16)
def goalM : Nat := goal_16 &&& dom_16
def NN : Nat → Nat
  | 3 => 3
  | 4 => 37
  | 5 => 166
  | 6 => 383
  | 7 => 207
  | 8 => 15
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x8bbd762b02281a3500b52c48
  | 4, 0 => 0xffa5d67efafed319dd30c3a2cd8ba78acb3360deb076ed74b059818aadfee09fa43828c79fcffa108a4d096a87bd66e4875cfd03835e68fb70a3385969d6131a630a008d5793a209543af2ce532825c34b023df74a2fe179445e4f5d444e40333c52dc5d37b1a169371934b33664178b3482d6892f19b73c2c4049351f85c2ff1951c30017f63f72130fcb340d35fb120bc30d25
  | 5, 0 => 0x3825fdfd3766628736e5c0b136d9bd26355135a83471896c34226368340c5c7732d92021317afe763159d03230f8a633302a63012ea7115b2c7ddac72c22e3092a0200d02884fdf8279ba41d26f1ef972593a424246e25642404b6a121e740f2219263b820c56933206d0bcf1f9c98751ed15b311d403d8d1d3dffd51c00ccfa18a76ccb180f1ac21752ee8516e279ed16b34c3615dac5e9159efd22154b9c0314f6ad4b11a50175119dfe10117d2bb9115fbfcf108b31051059d3860fce77530d7822550bb0d3750a70ebbf0a6c0c6909f4089109db321509d0c57e08ea0cab0897ff120804cae0049945ec048a94710375b19803331cf003039dae0112dc7c
  | 5, 1 => 0x9d128a3f9b6d4ee992e4a2cd8f7414698d0d68078b9810018b8bf21b8b2d19748ad3bad78808a6cc82403e67823553477af5220a79d654e879d50c7d778ca8267749ca3b767c5d427603df56751113a074e3f3f7735bf0b37227450771a7a88971a3faaf6ff542016fefc60e6efa94c66b09813368e2e4636788ce6a657914db605a4942600d69015f8385085e9446d15e2d8aab5e2c2c165c3303a15967c8f7577d0024576b7dfe5745f8dc55a7f767554b4938553537e854ea989351579aa950c073eb4fd6e4de4f7c60744c2bffcc48ac4e2c47b4abff4520b41040c1743d3ebcf13e3d7b8c223d57b0d53b932d743a37a9e63a21d651399b360d388623e6
  | 5, 2 => 0xff722e16fd2d0a86fa0fc86bf89a03efed09a4b6e7729a84e254d007e0942cb0dff65054da065308d1941c87d0dc8135cf3b86f7c9611fb6c545de6ac45bc38ac3ad3a5abce01efabc7e122fbb9f8c8abb676267b79b4f15b711e289b53ee764af527550ae3211d5ac8e73deab05838baa4f3836a9fed158a90a6299a8ecf6afa8c71cf8a6db69e1a43f6bafa3f74373a1e92ad59e4c5e2f
  | 6, 0 => 0x18bf975f1835a708181c0a6c17ce2ba217497f4a172c136016cdba33155ed0bb1432396c1422b86f1368b3e21347065013346ed112bbd30812baa6771232479711a579d6118eca211161181a1144e41f104ef3610ff651070fec104b0fcb33c20f8899180f3dab0c0edf18670e737a980df70cce0c269c8b0ba8521d0b88cc090b09f3650b05d34b0ae653d70a7677f509b1e68209a7f2140905f9ab0715437d067e992906612d3f060f596e05b10e6b0585bda20559e5f5053cd7d1053c7a0b04b4455c04963a7b048dacd70460bf69042d77d50341d11b03087e0402dea06a02d6a72e0249a99b0225f9ec01e3cad00185b851012a584001195bd500f94cd0
  | 6, 1 => 0x30e1709b30b9d1dd309c65f32f643cf62f2d39052f29cd722ec68d272ec5e3cd2ebd3d6c2df23de92de6358a2d52d1502c91587f2c5afc882c42325c2b9c405e2b27b74c2b25f1c52af8e8dd2ad9fd9b2aa964312a974f9129d10a322912a74928e1d56328bda13e28b131852886920f2750b4f6273a8680272cb27626dab0602602ca6f25e030e425c5c2a223e6582623bb3be32360951f22758e692259989721ce3725219634db215ab77120d5617920257d1e2014c6441e3844ef1de886c51dbe4d991da04c391d75a3ee1d2ae6bd1c35b2841c18469a1b9386ad1b59902d1a888b681a1f1cf019ff9c8019e5257c19ba301a191407ae190d1e2c18eed24c
  | 6, 2 => 0x4b6de5b24b2e44754b11aa524b0d87ba4abd1d0b4a932f4e4a3ff25049dd0e9149335a0b487b713e481026c54734005046f1b31146af8fd8466dcded462000d2458c33fc457ae3f04546c2da452fb72e44ab1cba44978530446729e643e3db9743415cc54214c55a412c1b383f7f6a493e247c763de700fe3d8a3cae3d64e4c33d4e5b033cc696da3c0ce04f3b754d643b0a44b33a5085363a4fc2063a4d6a9539b1034538c105703885fcd2386890e8380d7bfe375583a9373817bf36c9ea4736b5383e36093879357ada31350fe1ad34fdbc0734c8f0c7347c735e341c017333df688432b54b7632845a4131e5f16a31968b41315c50af31472fc2313ee4c5
  | 6, 3 => 0x74481341730cc97a7301de5f725e95e77236e265720d6fa071ff99de71f003b6719e752171905291706f245a70345b606ec7a3626e97547b6df7e42c6d7b510a6b50e1d96a95be0b676fce6066816af8641019b863939f3362f9b0eb629d9733628e69ce627050f961b6a79260fe5bb260f47f6c5ff943825fa001255f35ba935ed6a3f15da6006b5ccd4b075c97debb5aea31985a9c6dcb58f528b758d5e295588df5d95865c80957a4871956ba13a056488c3a5618ad1555f9c36e556a900e5488605d5465171a53dbb72c53b9049f534b32e9533a10a7533669d95318541d52c657935257aedf522c1d2d51c3864f50d485a14ebf453b4c4c79c44ba1260e
  | 6, 4 => 0xa8f0d2eda8e78fc4a748d152a71f7ceda70f3f44a61bfe94a4428e5ba2cd8bc3a0dcb925a0bf0646a0b30c9da053c87f9f307a4a9e93ebe99d459b779be41d5a9b138b039aca79e39a0d459599ce129a98f6084098825709985e9e2897c0eda197a00225974b40d79551aacc94ad81c7923130828ff7d9d28f74f0a98f15bfe78f09a0718e3f8c778cc6a3578c5b2b6f8c51c7138aa3b04f89ca38de8985697b8905ec5388b00c95876365058756c63885af18308494fa888320fd1b7f3dc0ab7e41f46b7e2488817da51d3c7acbd94679be6a98792b8cc8791c125477d135d07776a25c769b1dfd766e04be75ace69a753360a075079f9674cf39e47481ccfa
  | 6, 5 => 0xfa574c46f89a03eff31deba9f19580b8eec40f0cee5455feebefca4beba28a2aeafba6c3ea326695e9e8d9b8e82d725ee8027d18e5eea4cee4d154f8e2f6af66e247b55edff3a4ccdecd4938daa10b17d9fc9702d88d7dfad85d0165d7f9e631d79dcf25d697b081d5e44738d445852fd2def3e9d26d319fd1979f1acfaaeb5dcdf92910c9f87d99c9db535dc91a9764c8e9878fc7337313c69fce5ec63e6ab8c5460474c0e08b57c0d8bcdabf82112cbf662c09bf0a554ebdee9ca0bd9159b9bc545819b7a1fd24b7784d34b72f93ffb3fad78cb3874f18b22053d7af616e2bacf5e8eface9658bacd35171ac5aad7aab225dd6aa5561f1a97aa236
  | 7, 0 => 0x2d90db782cb7e2692ba0a43a2a6cf0712964176b28a4a83e2838c79a2705880d26beaf6f26396ad4261c309d2429651523afce9220292edb2014c6441fb72b911eb3facb1e3d0e221d989e101d81c57f1d094b741ca0b1831c53b96d1bea35011bde45011b8548e61a4058c319b1d448196672e11922d7aa17d6fff416e8db1816b50ee915ff8a47141a4f1c14121a0c12baa6771234695d123247971198114411761aa810d1aa960faa77070f8b2a5f0e7dd0190e783ebe0d9cbe430d9a92370d52c9a60d4d98860cea20e10cabde0a0c22507d0c167f100b989d4409ee1b6f06b07a0306291d8305869eb1033a727c02e9d44b01a603fb0086a50c00649915
  | 7, 1 => 0x651506a464cf00c56401590263353df46292bf2261aa33685dc82fa15aa8a6b956403068556f069554c1de10531915d1530ec13f52943af5523dc21151e81d51516924ff50c4b4ed500139404fb2394c4f943bc44f0fba7a4e2ce2974e1db72a4e0e9fc94dc27b5b4cd8ba054c4c79c44c1e35cd4b0c2c394b02825d4a3f78dc499b08ca48f889f843cee64d43b4257143a9f848430588364214fad141d9fb7841a4b5d64079af633dc32c533d6d0b963d57f2ca3c9d75a23c3d49423c21f90f3a8b9b213a8b1a653a47663438ad846e379a61823732d33a36c744ae359aee6d3518dab134746a9f33d93c6b339be83032ba82ac302ca7772f7655c82de85b92
  | 7, 2 => 0xc8d8951dc52f7576bf8705ebbf4172fabe107ab6bc545819b7a1fd24b55b444cb3feb3cab253eee6b080f6ebada32de2abbe6e52a98c5b5da909e4c1a8e78fc4a494c22fa35f8a0f9e58572e9d3508f49b71391a9aec1f2b9a36658d996c23f497ec88bb97012b8496a4b77d956125c6944ede0094331b6592b08ece9117715e8fa2db658e7679718df2ab598d3d413a8b7e195e8a81f0ca877910e2850f030e827639727fe35f827e8559377dbaea3c7cfde4937ab59725798a90b2785a178977d135d0727daf3d7260e48f71be65bd70cdf074706753916f69601f6d9b14bb6be1bd3a6bcb63fb6b46b4d16ababa2c6a4fc62d6a0139de69c0add4679d352a
  | 7, 3 => 0xfd058035fce2758bfc3e0176f9acd0faf646c3bfec164c1eeabec0cde8b03ee3e3d420a8e1c2a466d958a3e4d697c1d4cd5fbf4fcc0b8b0bcae6d7d7
  | 8, 0 => 0xf2854adfc2afde018a7994f87cea112d764e5f6161ca40085cde0cce4aee73793e277fff34064f6c2efbd9641b78d4bc1561a43a0e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x330033003300330011001100110011000f000f000f000f0003000300030003000055ff000055ff00003f3f00003f3f00000fff00000fff00000000ffffffff
  | 0, 1 => 0xfc00fc00fc00fc00f000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa0077007700770077005f005f005f005f0055005500550055003f003f003f003f
  | 0, 2 => 0x555055505550555050f050f050f050f0333033303330333030303030303030300ff00ff00ff00ff00ff00ff00f000f000ff00ff00cc00cc00ff00ff00aa00aa
  | 0, 3 => 0x11111111111111110fff0fff0fff0fff0ff00ff00ff00ff00f0f0f0f0f0f0f0f0f0c0f0c0f0c0f0c0e0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a
  | 0, 4 => 0x33333333303030303333333322222222332233223322332233003300330033003030303030303030151515151515151513131313131313131133113311331133
  | 0, 5 => 0x55555555555555555550555055505550554455445544554455005500550055005050505050505050444444444444444433333333333333333333333333003300
  | 0, 6 => 0xaaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00aa00aa00aa00a888a888a888a888a5a5a5a5a5a5a5a5a0a0a0a0a0a0a0a099999999999999998888888888888888
  | 0, 7 => 0xbabababababababaafafafafafafafafababababababababaaffaaffaaffaaffaafaaafaaafaaafaaaafaaafaaafaaafaaaaaaaaaaaaaaaaaaaaa000aaaaa000
  | 0, 8 => 0xcc00cc00cc00cc00c8c8c8c8c8c8c8c8c8c0c8c0c8c0c8c0c888c888c888c888c3c3c3c3c3c3c3c3c0ffc0ffc0ffc0ffc0c0c0c0c0c0c0c0bbaabbaabbaabbaa
  | 0, 9 => 0xccffccffccffccffccfcccfcccfcccfcccccccccccccccccccccc000ccccc000cccc8800cccc8800ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc33cc33cc33cc33
  | 0, 10 => 0xeaeaeaeaeaeaeaeaeac0eac0eac0eac0ea00ea00ea00ea00e0e0e0e0e0e0e0e0e0c0e0c0e0c0e0c0cfcfcfcfcfcfcfcfcececececececececdcdcdcdcdcdcdcd
  | 0, 11 => 0xeeeee000eeeee000eee0eee0eee0eee0eecceecceecceecceeaaeeaaeeaaeeaaee00ee00ee00ee00ecececececececececececec00000000eca0eca0eca0eca0
  | 0, 12 => 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeec0c0eeeeeeeeee00ee00eeeeeeeee000e000eeeeeeeec0c0c0c0eeeeeeee88888888eeeeeeee00000000eeeeeccceeeeeccc
  | 0, 13 => 0xf0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0a000f0f0a000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f00ff00ff00ff00ff000f000f000f000
  | 0, 14 => 0xf8f8f8f8f8f8f8f8f888f888f888f888f3f0f3f0f3f0f3f0f0fff0fff0fff0fff0f5f0f5f0f5f0f5f0f3f0f3f0f3f0f3f0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c0
  | 0, 15 => 0xfc00fc00fc00fc00fafafafafafafafafafafafaeaeaeaeafaf0faf0faf0faf0faeafaeafaeafaeafac8fac8fac8fac8faaafaaafaaafaaafa00fa00fa00fa00
  | 1, 0 => 0xfcfcfcfca800a800fcfcfcfc00000000fcfcf8f0fcfcf8f0fcf0fcf0fcf0fcf0fcf0fcf000000000fcccfcccfcccfcccfcc0fcc0fcc0fcc0fca8fca8fca8fca8
  | 1, 1 => 0xfefcfefcfefcfefcfef0fef0fef0fef0feeefeeefeeefeeefeccfeccfeccfeccfeaafeaafeaafeaafe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfca8a8a8a8
  | 1, 2 => 0xff01ff01ff01ff01ff00ff00ff00ff00ff00ff00f000f000ff00ff00cc00cc00ff00ff00aa00aa00ff00c000ff00c000fefefefefefefefefefefefe00000000
  | 1, 3 => 0xffaaffaaf0a0f0a0ffaaffaaeeaaeeaaffaaffaa00000000ffa0ffa0ffa0ffa0ffa0ffa000000000ff30ff30ff30ff30ff11ff11ff11ff11ff0fff0fff0fff0f
  | 1, 4 => 0xffe0ffe0ffe0ffe0ffccffccffccffccffccffccfcccfcccffccffccf0c0f0c0ffccffccaa88aa88ffc0ffc0ffc0ffc0ffaaffaaffaaffaaffaaffaafaaafaaa
  | 1, 5 => 0xfff0fff0f000f000fff0fff0ccc0ccc0fff0fff088808880fff0fff000000000ffeeffeeffeeffeeffeeffee00000000ffecffecffecffecffeaffeaffeaffea
  | 1, 6 => 0xfffefffefffefffefffcfffcfffcfffcfffafffafffafffafffafffa00000000fff8fff8fff8fff8fff0fff0fff0fff0fff0fff0ffc0ffc0fff0fff0ffa0ffa0
  | 1, 7 => 0xffffc8c0ffffc8c0ffffc0c0ffffc0c0ffffaa00ffffaa00ffff5050ffff5050ffff3300ffff3300ffff1111ffff1111ffff0011ffff0011ffff0000ffff0000
  | 1, 8 => 0xfffff0f0fffff000fffff0f0ffffc0c0fffff0c0fffff0c0fffff000fffff000ffffeeccffffeeccffffeaeaffffeaeaffffeac0ffffeac0ffffe0c0ffffe0c0
  | 1, 9 => 0xffffffc0ffffffc0ffffffa0ffff0000ffffff00ffffaa00fffffcf0ffff0000fffffcccfffffcccfffffaf0fffffaf0fffffaaafffffaaafffffa00fffffa00
  | 1, 10 => 0xffffffff00ff00ffffffffff00cc00ccffffffff00550055ffffffff000f000fffffffff00000000fffffff0fffff000fffffff0ffff8880fffffff0ffff0000
  | 1, 11 => 0xffffffffaaaaa000ffffffffaaaa8080ffffffffaa00aa00ffffffff88888888ffffffff50505050ffffffff11111111ffffffff0a0a0a0affffffff03030303
  | 1, 12 => 0xffffffffeecceeccffffffffea00ea00ffffffffccccccccffffffffc8c8c8c8ffffffffc8c0c8c0ffffffffc888c888ffffffffc0c0c0c0ffffffffaaaaaaaa
  | 1, 13 => 0xfffffffffaf0faf0fffffffffaaafaaafffffffffa00fa00fffffffff0f0f0f0fffffffff0f0a000fffffffff0c0f0c0fffffffff000f000ffffffffeeeeeeee
  | 1, 14 => 0xffffffffffff3300ffffffffffff1111fffffffffff0fff0ffffffffffccffccffffffffffaaffaaffffffffff00ff00fffffffffcfcfcfcfffffffffafafafa
  | 1, 15 => 0xfffffffffffff0c0fffffffffffff000ffffffffffffc0c0ffffffffffffaa00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xd19671674d2b2794d4d0b282794
  | 4, 0, 0 => 0xd3b8a67e5e5cca68471395d0b28271395ddbe9671675d0b2784d395d3b8a189565d3c5a684395b8b2af82395d0a2714d395d3b8a6847b5dcb88a71675d3b8b276675e1b8967c675d3c19671675d2b2684d395d0b28268395
  | 4, 0, 1 => 0xb8b2ac82795c4b2ac794d5d196714d395e2b8968d715edb89c7e4d5d3bda271675d3b8b27a675be967166395dcb8968d715e3b8967c675fac4b2794d5dcb89691545dcc49671675dcb8b268675dcba9671675d3c6967e675
  | 4, 0, 2 => 0xb8ad9671675d3bf967c675d3b8a27c675d3b8a67e585d0a6714a395
  | 5, 0, 0 => 0xd3b8968f45396e4b8967e71676b89d966c4d396b8908a714d396d3b8969146326d0b271684d396b8966c614d396dab8967167306debe96714d396d3c4967160396e5d3bd9671676d3be96715d396dcb8969171676d5b8a1714d356fbc596714d39600e9b8b282395
  | 5, 0, 1 => 0xd3b8a6a17c4d6ddb8a69671676f2d3b89c7e4d6dcb89671671f6b89687714d396d3b88a544d396d3c096715d396d3b8a68e71396d3c4967167306ddb89671574d6d3b8b26867306d3b8b28279396d3c4b2794d396d3ba967167306d3cda6714d396d3b8ab7149356
  | 5, 0, 2 => 0xd3b8b2a6794d6d3b8b5684d376e9b8967167306d3b8a2716735600dcb896711f5ddb8967167416e9b8b2794d396b8ad96714d396b8a6848371396d3b8a68171396d3b8969154306ddb896894139600d3b8964d335d3bf967c4d396dcb8967168676d3b8968d71446
  | 5, 0, 3 => 0xd0b696714d396d3b8a16c4d356d4b8b2684d396b8ab9d714d356d3c196714d396dcb89679714d6f9cf96714d396d3bd96854d396fac49679714d6ecd3b8a289396b896716763396d3bda69671676d096714d39376b8b2ac6b4d39600dcb87167135d3b8a67158396
  | 5, 0, 4 => 0xd3b8967a71676eab8a67147396d3b8967167316d3c89671674d6dcb89671675b6d3b8a18941356d3b8a67047396d3b8968d71306d3b8a39671676e9d3b8b282396d3bd967167416d3b8b2764d396e1b8967c4d396b8b2ac96794d6d3b8a2715d396d3bd968941396
  | 5, 0, 5 => 0xd3b996714d396d3b8968c7e326d3b8b28c7e396ddbe96714d39600d3b89671315d3b8a171564d6b8a2898671396d3b897714d396e5d3b8967c676bd967167614d6d3b8a69c7e4d6d3b8b28c71396e2b89679714d6d3b8b2a67e676d3c996714d38600d0b2684d395
  | 5, 0, 6 => 0xd3c5a69689396dcb8b2684d396b8b2ac79684d6d3b8a67e47326fac4b2684d396b8a6867f71396b8ac967c4d396d3b8b67f4139600d3b89643395d3b8a67148396dcb89671671c6b89d9679714d6d3b8966c67306d3b8b278674d6d3b8a69371676e4b8967e4d326
  | 5, 0, 7 => 0xdfc496714d396d3c5a67147396e3b8967c4d396f9be96716739600b8967167625e6b89671574d6d3b8a66c47396d3c2be9671676d396715f4d39600d3b8694d395d3cf92714d396d3b89c7e784d6b8aca6714a396d3b8ab967c4d6dcc496714d396d3b8a27e71676
  | 5, 0, 8 => 0xd3b8968f53396ecd3b8b282396ba9671614d396d3b8968943396d3bda2714d39600d3b84d391d5b8967c67614d6d3b8b27a4d39600d3b8b28279500d3c4b2794d5d3b8a6715e396daba96714d396b8967e61544d6d096714d39056d3cd9671674d6d3c8a1714d396
  | 5, 0, 9 => 0xd3b8967671676ce9c96714d396d3b8685e4d396d3b8968f41396d3b8b5784d326dcb8b29671676f6ba96714d396d3b8967167566d0b2a6714d396f7bb96714d396d3b8967c67456ebbd96714d396b89689866b396d3b8b2694d396c4b2ac684d396d3b896715d576
  | 5, 0, 10 => 0xd3b8a27c4d396b89671644d396b8b2af684d396d3ba96714d396d3c396714b396d3c696894d396
  | 6, 0, 0 => 0xd3bc96714d396d3b89676714d397d3b8a696896b39700dbb896714d2f6d3b896714d390a7d3b8b2684d39057e9d3b8b2684d397b8a696898671397b8967161544d397d3b896714d39067d3cbc496714d397e0d3b8b2684d397d3b88a89714d397d3b8b696894139700b8b2ac684d396e9b89671674d397
  | 6, 0, 1 => 0xd3b8b096714d397d3b8b2a2714d397d3b896714d392d700b896716730006d3c3bd96714d397d3cabd96714d397d3b8b2967e674d7d3b8a1714d35097e9d3b8968271397e9d3c496714d397d3b89671675b307d3b8a096714d397b89686714d39147e0d3b896827139700b89671574d006e0d3c496714d397
  | 6, 0, 2 => 0xd3b89e96714d397d3b89996714d39700b896716761306d3b8968c714d397d3b896714d390f7d3b8b5966a4d397d3b8967e4d3213700d3b8714739076d3b896896f4d397b89689867141397d3b896714d39287d3b8b2966a4d397d3b8a696715c397e5d3b8968271397d3b8a2714d392f7d3b8a6714739367
  | 6, 0, 3 => 0xd3b8b2a1684d397d8b89689714d397d3b89672714d397d3b8967e71574d700d3b89682391c600d3c4964d391c600f8bd96714d396d3b8967e4d32297d3b8ab967e714d7d3be96714d39357d3be96714d39027f2d3bd96714d39700b896894139006d3b8a6968471397d3b896714d39077d3b896714d39147
  | 6, 0, 4 => 0xd3b896714d3f39700d3b8a27167396e0d3b896715c4d7d3b8968279714d7d3b8a1968271397d3c4a196714d39700d3b8a178714d6d3b8969371674d700b8967c4d39006d3b8968d714d397d3b8b696714a397b8abaa96714d39700d3b839291c13600ddb8964d391c600d3cd96714d396d3b8b6a67147397
  | 6, 0, 5 => 0xecd3b896715d397d3b8968b714d397d3b896897e41397d3b89680714d397d3b896714d391b700d3b8714d42396f2d3b8a1714d357d3b896714d3b397b8b5b496714d397d3b8ab715b4d39700d3b8a1967c4d6d3b89671504d397d3b8a596714d397d3b89679714d397d3b8a6967e71677d3b8968f7c4d397
  | 6, 0, 6 => 0xd3b8918a714d397d3b8a67f714d39700b8a6714739006d3b896714d3d39700d3c4967139296d3b8967e716741700e9b8964d391c6d3b896714d39047d3b8967e4d47327d3b89671574d137d3b8a6716b47397d3b8968c7e7139700d3b8b2683929600d3b8b26b4d396b896867f714d397e5d3bd96714d397
  | 6, 0, 7 => 0xd3b896714d39127d3b8b2968271397d3c4b296714d397d3b89682713915700d3b89689412f6b8b59d96714d397d3b8b5b2684d397b8ac96714d4a397e9b8a196714d397e4b8967e714d397d3b8b2684d392f7d3b8967167301c700ddb896713929600e1b8964d391c6d3b896714d392e7d3b8a671675b397
  | 6, 0, 8 => 0xd3b896894139137e5d3b8a1714d357b89d96714d49397d3b8b2a6684d39700d3bb96713929600d3b8967e6a4d6d3b8a896714d39700d3b8715d39136d3b8b2684d3930700d3b8b296794d6ddb8b296714d397d3b8967871674d700d3be714d39136d3b8968271392f7e1b8a196714d397d3c496714d392f7
  | 6, 0, 9 => 0xe9b8967139296d3b896714d39277d3b896714d39267d3b896714d39177d3b89f96714d397ddb8a696714d39700b89639291c00600d3b8a6715b396d3b896898271397ecd3b89679714d7d3b8a6968271397d3c4a696714d397f2d3b8967e4d327d3b896827139307d3c496714d39307d3b8b2a1967e4d7
  | 6, 0, 10 => 0xd3b89691714139700d3bd967139296e7d3b896715d397b8b2ac96684d397b8967e7167614d700d3b8b24d391e6d3b8966c674d397e9b896714d392f7e9b8b296714d397d3b8b295714d39700d3b8a14d351c6dcb89671684d397d3b896714e4d397fac49671684d397d3b8a67e7147397d3b8967c4d391c7
  | 6, 0, 11 => 0xd3bdb296714d397d3b8a6714739077ecd3b896844d397e9b8a696714d397d3b896714d39207d3b8ab967149397d3b8b196714d397e9b896714d39307d3b8a2714d39357d3b8967151391c7d3b8a696704d397d3b8a89671574d700d3b8a671472f6ddb896714d41397e1b896714d392f7d3b896714d391a7
  | 6, 0, 12 => 0xd3b896897f41397d3bd9689714d397d3b8a1967e6a4d7b8ac96714d3905700d396714d39036d3bda696714d397f8d3bd96714d39700d3b8966c4d396eab8a696714d397d3b89688714d39700be96714d39006d3b89671674d3c7d3c496714d4c39700dcb8714d39136d3b896714d39057e5d3b8967e4d327
  | 6, 0, 13 => 0xf2d3b8968941397e0d3b89671574d7d3c496714d39017d3b896715e4d39700d3b8744d390e6d3b8b2a1714d35700d3c796714d39600d3b8967b714d6ecd3b8a2714d39700e1b8967167396d3b89671654d39700b89689864139600d3b8962f291c6f2d3b8967167307d3b8967e544d397eed3b89679714d7
  | 6, 0, 14 => 0xd3b8b2966b4d397dab896714d391f700b89679714d006d3bd96716d4d397e0d3b8a69671677d3b8a189714d35700d3c596714d396d3b8b2a66b4d397d3c49682714d397d3b8a1714d49357d3b8a2967167397d3b8a396714d397f1d3b896894139700d3b89c967e4d6b8969171614d397d3b8b282684d397
  | 6, 0, 15 => 0xd3b896896b4d397b89671614d391f7d3b8967a714d39700d6b8714d39136d3ba96714d391f700d3b8968279716d3b8967d714d39700d3c49679714d6b8ab9d96714d397d3bd96714d4b397e0d3b8967167417d3b8b2967e4d327d3b8a1714d4135700d3b8b279684d6d3b896714d390b7d3b8a2714d39087
  | 6, 1, 0 => 0xecd3b8968271397ecd3c496714d397d3b896715d39297ecd3b8b2684d397e5d3b8967c4d397d3b896897e4d327d3b8a796714d397d3b8b596714d397d3b8b2a67e4d397f2d3b8a67147397d3b89a96714d397d3be96714d39137e9b89682714d397b8b2aca6714d39700d3b89667301c6d3b8a19671574d7
  | 6, 1, 1 => 0xd3b8968d79714d7d3b8b2967167307d3b896714d3916700d3b8827139136d3b896847e4d397e8d3b8967167307d3b8a693714d397d4b896714d39057d3b8b29671574d7d3b8b2964d392b7b89671676141397d3b88a7e714d397d3c8967e714d39700e9b89679714d600d3b896714d226b8b5ac96714d397
  | 6, 1, 2 => 0xb89c9b96714d397d3b8b296774d397d3b8b578714d397d3b8a27e714d397ecd3bd96714d397d9b896714d391c700d3b8967c39296d3b8b282714d397d3b8968941392f7d3b896714d4039700d3b8a647391c600d3b8714d39086dcb896714d391c700d3b89651391c6d3b8b2684d39377d3b89675714d397
  | 6, 1, 3 => 0xd3b8967971674d7d3b89691714d397d3b896897c4d397d3b8b2a6714a39700d3bd714d39136d3b896714d3a397d3b8967157554d7d3b896917e4d327d3b8967e4d390e7d3b89682713934700d3bd9671674d6f2d3b896715d39700d3b8714d3c0c6d3b8aba1714d3570000dcb8967167500b84d391c13006
  | 6, 1, 4 => 0xd3b896714d39117d3b896714d391f700d3b89679714d6d3b8967e7167467f4d3b8a6714739700d3c4b2684d396d4b8b296714d397d3b89673714d39700b871392913006d3b8a2968971397d3b896715d3920700c496714d3900600d396714d39016d8b896714d39147b896715a594d39700b8b2684d39006
  | 6, 1, 5 => 0xd3b8684d3905600d0b296714d39600e9c496714d39600d3b8967139156d3b8a1715b4d39700d3b89682712f6d3b89671574d35700e9b8b2684d396d3b8b796714d397efd3b8967c4d397d3b896714d39217d3b896917167307d3b896827e71397d3b8ae96714d39700d3b8965d391c600fac496714d396
  | 6, 1, 6 => 0xd3b89671301f6dab89671674d397d3b89671584d397d3b8a496714d397d3b896716867307d3b89671674135700d3b8714f390d6d3b8b396714d397d3b896714d39107d3b8967e715c4d7d3be96714d392f7d3b896827139297d3b8967167301f7f2d3b8a2714d397d3b896917146397ddb896714d391c7
  | 6, 1, 7 => 0xfad3c496714d39700d3ba96714d396dcb8b296714d39700d3b8a24d391c6d3b8a996714d397d3c49671674d39700b896712f29006d3b89671564d397d3b8b268674d397d3b896714d39257d3ba9671674d397f5d3b8b2684d39700d3b8714d35096d3b8967c4d45397d3b8967e6e4d397
  | 7, 0, 0 => 0xd3b8a6714d39137e0d3b8967e714d39800d7d3b8714d391370000b8964d391c00600d3b8714d3930137d3b8b296714d39378ecd3b896714d4139800f2d3b896714d2f7d3b89671674d391c800d3b8714d392f13700d3b8b2714d3913700d3b89674714d39700d3b89694714d397d3b896714d47391c8f2d3b8967e714d398ecd3b89689714d398
  | 7, 0, 1 => 0xe0d3b896714d2f7d3b896714d391c198e5d3b8967e714d398d3b8b6b296714d39800d3b896714d390770000e1b896714d39600d3b896714d3914700b8a196714d39007f2d3b896714d39138f2d3b896714d391c80000e9b896714d39600d3b8a696897139700d3b889714d39137d3b8a696714d3936800d3b896714d392b700d3b896714d391e7
  | 7, 0, 2 => 0xf3d3b8a196714d398e0d3b896714d39138e0d3b896714d391c800e5d3b896714d2f7d3b8b69689714d39800d3b89671524d397ecd3b896714d3932800d3b896897141397d3b8b6a696714d39800d3b8a296714d39700d3b896714d392c700d3b8714d413913700d3b89671392924700b8a19d96714d3970000d3bd96714d396f2d3b896714d39298
  | 7, 0, 3 => 0xd3b8a196714d2f700b896714d3930007d3b8a696716b4d39800d3b8714d393213700d3b898964d391c70000d3b8964d2f1c6d3b8968271684d3980000d3b8a1714d35600b896714d392f00700d3b8714d39130e700b8b296714d39007d3b8a1967e714d398e0d3b896714d392980000b89671392900600d3b89679714d39700d3b89677714d397
  | 7, 0, 4 => 0xd3b8a196714d3929800d3b8964d391c18700b896714d4139007d3b8b2967e714d39800d3b8967971684d7e0d3b896714d4739800d3b896524d391c7ecd3b896714d39358d3b8a196714d39138d3b8a196714d391c800d3b8967f714d39700d3b896714d3e39700d3b8967e713929700d3b8964d391c137f2d3b89671674d39800b8a696714d39007
  | 7, 0, 5 => 0xd3b896714d392f1c8d3b8b296714d391c8ecd3b89671684d39800d3b8714d393513700d3b89671392913700d3b8967139291c700d3b8b296714d2f7d3b8a196714d39098d3b896897e714d398d3b8a6967e714d39800d3b8b296684d397d3b8967167544d39800d3b89671674d3570000d3b8967e4d326e0d3b89671674d3980000d3b896712f296
  | 7, 0, 6 => 0xd3b8a696714d39138d3b8a696714d391c800d3b896715d4d397d3b896714d392f298d3b896714d39301c8d3b8b296714d3929800d3b896674d391c7d3b8a696714d39078d3b8a196714d4739800d3b8964d3e391c7d3b8967e714d4139800d3b896714d3905700d3b89671544d39700d3b89689714d2f700b896714d3932007d3b896714d392f138
  | 7, 0, 7 => 0xe0d3b8964d391c7f5d3b8b296714d398e8d3b89671674d398d3b896714d47392f8d3b8b296714d4739800d3b896716739297d3b896714d41391380000d3b896716730600d3b896714d412f70000d3b89671574d600d3b8714d39130c7d3b8a19671674d39800ecd3b8714d3913700d3b89695714d39700d3b896714d2f2a700d3b871684d39137
  | 7, 0, 8 => 0xd3b8b596714d39700b89671684d39007f2d3b896714d392f8f2d3b8b296714d398e5d3b8a196714d398d3b896897f714d398d3b8a69671674d39800d3b8b2a6714d39700e5d3b8964d391c700f2d3b8967139297d3b896917e714d3980000d3b8967c4d396d3b896714d39130e8e0d3b8a196714d39800d3b896715a4d397d3b8b29671674d398
  | 7, 0, 9 => 0xe9b89671684d39700d3b89671684d2f700d3b8967e71674d7d3b896714d393529800d3b896716f4d3970000d3b89639291c6d3b896714d4739328d3b8967e71684d39800d3b89684714d397d3b8b296714d39058e0d3b8b296714d39800b8b2ac96714d39700d3c49671684d397f2d3b89689714d398f2d3b8a696714d398f2d3b896714d39308
  | 7, 0, 10 => 0xd3b89671392f297d3b896714d39130d8d3b8a19689714d398d3b8a196714d49398d3b89671684d3929800d3b896713929237d3b8969171674d39800d3b896894d391c700e5d3b896716739700d3b896714d390e7f2d3b896714d39328d3b8b2a196714d39800d3b87e714d39137f0d3b8967e714d398e0d3b896714d4139800d3b8964d392f1c7
  | 7, 0, 11 => 0xd3b89671393229700b896714d391c0070000dcb896714d39600d3b8a6967147397d3b8b296714d4139800d3b896714d391f70000d3b89679714d600d3b8964d39321c7d3b8967168674d398d3b8a696714d392f8d3b8b296714d39308d3b89671674d391f800d3b8a6967139297d3b8a196714d4139800d3b89678714d39700d3b89691714d397
  | 7, 0, 12 => 0xd3c496714d396d3b89671684d39308d3b896714d41393580000d3b8b2684d396d3b8b29671684d3980000d3b84d391c13600b8967167614d397d3b896714d391c13800b89671674d39007d3b8a19671684d398d3b8aba196714d398d3b8a696714d3932800f2d3b8714d39137e9d3b89671684d398e0d3b89671684d398
  | 8, 0, 0 => 0xb896714d39006d3b89671684d397d3b896714d41397d3b896714d39307d3b8b296714d397d3b8a196714d39700d3b8964d391c6e0d3b896714d397f2d3b896714d397d3b89671674d397d3b896714d47397d3b896714d39297d3b896714d391c700d3b896714d2f6d3b8967e714d397
  | 9, 0, 0 => 0xd3b896714d396
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 36
  | 4 => 44
  | 5 => 52
  | 6 => 60
  | 7 => 68
  | 8 => 60
  | 9 => 52
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1f1c0e3e07e0c7c7000f801800303fe06001fc0c003818000300fffe01ffffc03fff807ffff00fffe01ffffc000007ffffff
  | 0, 1 => 0x1c1ff03807ff0707000e01f800003f000001f0000e38001e731f1c7e3e07e3c7c7ff8f801ff1f1c703e006307c7ff8f81fff
  | 0, 2 => 0xfffc71fff86338f8fff1fe07ffffc0ffe1fe0f8f803f1860031f1ffe3e07ffc7c7ff8e01f801f1ffe00001f07c7ff8001e73
  | 0, 3 => 0xfffc01fe18603fffffffffffffcfc01f9ffe038f8fff1fe07fe0e3f1c1f81f0000ff807807f0003f001e01f0000e38000073
  | 0, 4 => 0xfffc0e3807e03fff038001e03e0e00fc01f80f8380070060001c1c003807e03fff1c7ffe18cfffc0ffe1860ffff03ff87f83
  | 0, 5 => 0xfffc71fff8633f3f007e7e180e0e071c1f803383800707e0001c1c0038006000001c007800cfffc0ffe1fe0ffff03f006000
  | 0, 6 => 0x7800000e000000700000000000000000e00000070e3e071c7ff830000000001e00ffff81fe187c0000e00000070
  | 0, 7 => 0x1c1f8e3807fcf8f8fff1ffe7fe3e38fc61f9cc7c7ff8f81fff1c1f8e3807fcc0c0ff8181e7f00038e00079cc000000000000
  | 0, 8 => 0x1e0000000e000000700000000000000000e00000070e3e00fc61800c7c7ff8f81fff0000000000003838e3f007e73
  | 0, 9 => 0x1f1ffe3fe7ffc707fc0e79ffc0003f001e01f0000000000000000000000000000000007800000038001e01c07c7038ff9f83
  | 0, 10 => 0x38e00079cc0000000000000000000000000000000001e0000000000000038f8fff1fe07f0003fe01e01ff8f8fc71fe07c
  | 0, 11 => 0x79e000003f001e01f0000e38079e7300000001e0000000fc0079e7c0003f00000000000000079e00
  | 0, 12 => 0x3fe01e79fc000ff80000000003fe01e0000000ff80000000003fe0000000000ff80000700003fe0000000000fc007807c
  | 0, 13 => 0x1c1c000000000707000001e001c00003800000000000001e000000000000000000000001e000303fe06001fc000000000000
  | 0, 14 => 0x1c1f803807fc0000e00000070fcfc01f81fe007c7ff8f81fff1f1c703e07e307c7038f81f831c1c003807e00707000000000
  | 0, 15 => 0x1e0000707e38e01ff31c1f8e00079cc707000e01f8000038e00079cc000e0000007000038e00079cc000000000000
  | 1, 0 => 0x1c1ff00000000707fc00000001c1c003807e00707000e79f801c1c000000000000fc007807c00000001e0000000e00079e70
  | 1, 1 => 0x1c1ff039e7ff0707000e79f800003fe01e79fc000fc007807c00038e01e79cc0000000780001c1ff039e7ff0707fc0001e70
  | 1, 2 => 0xe3e001c7f800383800707e000e0e0000000003838000078000e0e00000000038000070000001c1ffe39e7ffc707ff8000000
  | 1, 3 => 0xe0e38e0007803838e38079e73e0e38e000000383800707fe00e0e0000000003f3f007e7ff80fffc01fff86038f8fff1fe07f
  | 1, 4 => 0xe0e001c1ff803838fc707e07ce0e3f001e01f3838fc0000000e0e3f000001c383800707e000e0e38fc1ff9cf838e38001e73
  | 1, 5 => 0xfcfc000000003f3f000078000fcfc000000003f3f000000000e0e3ffc1ff9ff838ff8000000e0e3f1c1ff9f3838e3f07fe73
  | 1, 6 => 0xfcfffff9ffffff3ffc7e7fffcfcff8ff9fffcff3fe38000000fcff81f9fffc3f3f007e7ff80fcfc01c1f8003f3f00707fe00
  | 1, 7 => 0xff0001fe00003fc0007f80000ff0001fe00003fc7007f80180ffe001fe18003fff007f86180ff1c01fe00603fc0007f80000
  | 1, 8 => 0xff1c01fe00003fc7007f80000ff0001fe00003fc0007f80000ff03f1ffe01f3fc0e3ff81e73ff0001fe00003fc0007f80000
  | 1, 9 => 0xffe001fff8003ff8007f80000ffe001fe00003fc7007f80000ff03f1ffe01f3fc7007f81f80ff038ffe079cffc0007f80000
  | 1, 10 => 0xfffffe3e07ffffffff800007cfffffe3e00633fffff818007ffffffe0000003fff007f80000fffc01fe00003fff007f80000
  | 1, 11 => 0xfffffe0000003fffff8000000fffffe0000003fffff8000070fffffe3800603fffffff86180fffffe00001cfffffff186003
  | 1, 12 => 0xfffffe01e01f3fffff8000000fffffe01e01f3fffff8000070fffffe0000003fffff8000070fffffe0000003fffff8001e73
  | 1, 13 => 0xfffffe3807e03fffff8001e73fffffe0000003fffff8e01f80fffffe3800003fffff8000000fffffe0000003fffff8079e7f
  | 1, 14 => 0xfffffffe18003fffffff86180fffffff9ffe03ffffff07e07cffffffc1ff9cfffffff07e000fffffe39e7ff3fffff8e01ff3
  | 1, 15 => 0xfffffffe00003fffffff80000fffffffe00003fffffff80000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x5040a0a06008000000000000030248060012804002008000200dcb20154e5003d49804f521006db6012cad4000007fbefff
  | 0, 1 => 0xe0ed21c06b70303248601a940a0ad01400b70141a28281a520f0c5a1e062382c29605800ce0a085014002301c192838184a
  | 0, 2 => 0x4a487095802310d09a21e004a25240e4a0e00c8480310820030f0eda1e06b783c3b68601a940f0eda1404b703c3b68281a52
  | 0, 3 => 0x9090012010401bdbffb7ebaff6c6db6d9aead58d8db31ea06b626364c5a81a58d8db31ea06b42436085a01a0848c3108a063
  | 0, 4 => 0xb5b40f2817402d6d039283c03b5b40f6a1f40ec2c01580650194940328174034b4186964108b1b00d621840e56502ca85902
  | 0, 5 => 0xdad871b5d06336360c6c74184dad871b5d063343408687410098981130506112921c257008cb5b40f6a1f40ed6d03d807501
  | 0, 6 => 0x242586482f8c4808e1100a6712021044029084000e000086704644e28d87860101208201e109093812030dc0000e00008270
  | 0, 7 => 0xb5b78f6a3fdcd9d9fbb3ebe7b25278e4a2f9ccbcbf7978beff2d2f9e5a2fbdc9c9f3938be7b25278e4a2f9cc940821280c42
  | 0, 8 => 0x40412081e0080202e404182f40809901060ad0000e0001827029289c5248a5c3c3b68791ade0808901040a52d6de3da8ff73
  | 0, 9 => 0x4f4ffa9fe6bf9393fca779afc4a4bf095e0bf12809025300484a034094a01a12126c24782b44043a081e09c11514aa2f9822
  | 0, 10 => 0x2d2f9e5a6fbdca0a65141a6b52021044069084303248611e940808901041a51adaff35fa2ff6b6bfcd7e8bfd292fc25782fc
  | 0, 11 => 0x6f0248dec3129b1b6db67beb56a6bf4d5e9bf5959ebb2fbe73606124c1e9085393fca779efc4e4ff2010400111168a279e30
  | 0, 12 => 0x6f6ffedfefbfdbdbffb7f1ade6f6ffec1ed085bdbff80514006f6ffe1144a51bdbff80492706f6ffe0104001bd2fe37f8efe
  | 0, 13 => 0x9c9c921044a52727248201e109c0001380300272724ce15f949898913051e5252520ca15f10939249265152a424004814500
  | 0, 14 => 0x9c9f933877fd2424e0481c770bcbc97785fe567e7b6cf95fde9e9cd33c57e7276726ce95f969c9c933857e5272724cc15794
  | 0, 15 => 0xd0d121a1f1482f6fe7de9fff7bdbf9e5a6fbdef2f65de1ffb5bdbf9f7a7ffdee2ee55c1e7f5b5b78f6a7fdcec2c41581e521
  | 1, 0 => 0xdedff201250837b7fc8041000de9fd3bcf7ff37376cee7dfb4dcddb201040036b6fc6d7c7fcd8d9b1b1f1ed3535e8ea7df70
  | 1, 1 => 0xfefff7fdffff7f3f6dfe7ffb5fffffffffffffebefd7d7e7fdf5f7afebffdcfc3c49787e521dedff3bdf7ff37b7fc8249e70
  | 1, 2 => 0xf0f125e1f9487c3c49787e521f0f1252151403c3c492078020f0f1244129087c00007830000ffffffffffffffffff8041000
  | 1, 3 => 0xf5f7af2957c43d7debb2fbe73f5f7ae0104003d3d69fa7ff31f4f5a60104003d3d49fa7fd21f0f125e1f9487cfcdb79fe56b
  | 1, 4 => 0xfcfdb7f9ffed7ebefd7d7e7fdfafbf5b5f1ff3ebefd4c54794fafbf441299c7e3e6d7c7e7b5f5f7afebffdcfd7debdadff73
  | 1, 5 => 0xfcfdb72155403f3f6da4792b4fcfdb601248c3f3f6d8041000ffffffffffffffffff8041000fefff7fdffff7f7feffeffff7
  | 1, 6 => 0xffffffffffffffbffdff7fffdfdffbffbfffdff7fef8041000fcffb7f9fffd7f3f6dfe7ffb5fcfdb7f1fded7f3f6dfa7ff31
  | 1, 7 => 0xff0bd9fee2bfbfc2b67fb0adeff234dfeab1affe6967fb49ceffb24dfe9b52ffe4927fa494aff0249fe8212bfc0927fa084a
  | 1, 8 => 0xff9edbfed752bfe7b6ffb1adeff9ad9fed3f7bfe4927fb4d4aff6bfdffebbfffcbf7ffbbeffff2bddfeebbfffc2b67fb0ede
  | 1, 9 => 0xfffbfdfffbfffffdfbffe184afff36dffab1afff7feffe184affdbf9fff3ffbfeff7ffbffffffb7cffeffdeffecd37fbed6b
  | 1, 10 => 0xfffffe1f06b7bfffff85412dcfffffe1504233fffff81c104afffffe0104003ffffffff5d4affffffffa69ebfffffffe184a
  | 1, 11 => 0xfffffe4b0710bfffff92c1a52fffffe412d087fffff8049270ffffff3154613fffffc845100fffffe432c18ffffff90c3003
  | 1, 12 => 0xfffffed5edbf7fffff905b421fffffe95e4bf3fffff84592f4fffffe1164ad3fffff8059270fffffe1144a53fffff92cbe73
  | 1, 13 => 0xffffff797fed7fffffdadff73ffffff617d487fffffce55f94ffffff3907003fffffcc55794ffffff2155403fffffb7fbeff
  | 1, 14 => 0xffffffff9f52ffffffffe594afffffff9ffed7ffffffd7f7fdffffffebffdcfffffff87f521ffffffbdf7ff3fffffdedfff7
  | 1, 15 => 0xffffffffd7f7bffffffff5d4affffffffc6b7bfffffffebc6b
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 50 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 50 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 252 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 252 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 252 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 252 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 8 0) :: stateWiresD n (ids >>> 8)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 8 0) :: stateWiresS n (ids >>> 8)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 10 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 3 => 1
  | 4 => 24
  | 5 => 344
  | 6 => 923
  | 7 => 460
  | 8 => 13
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0x166aeb2b
  | 4, 0 => 0xfabc8b51bc83c90fb6257f57b145d7fdaf880c88ae5f1047a18967f99d459b77880ce0a473029d4346936c642ff197262d81ae482178cc081899631f1329bd310e50780a0def5aac0cf4fa860c21ff2108d811960611d83705f46c4d036ce48d
  | 5, 0 => 0x19de4522194fe8a0194ec749194e3edd18f325e618ae189c187d0f6b17d6fff417c6219b17b9de51176346e0169f119e15790fcb151183d714677765143f084314219c5913fab94a13cb6ed212bcb56d1234695d11b7c981114298b6111fb91411024d2a0faa77070ef08abd0e55716a0d83c6990cc79e370cad16120c69bfd00c645dec0c2777f60c1a655c0bd5dce90b2a75ff0abe50760a55a4560a4c849609e160f00993677c0990730608d29aa7088521e206fe0c7c06f6939e06616038063d048b05cad53c05c2ee4704b4455c04a0f63a048f76fa04720b10045412d00416c3180414a35503f10e490376cb1900e45e9700c10392005d357c00272583
  | 5, 1 => 0x35791e33356b27a53547ad91350af91a34f0851b34d3193134c8f0c732b54b7632844103321ad228317a69f63091e27e30599af930545a882ff0ebad2fcd421b2fc512132fb0263c2f734f292f3664fa2ef31c182e7212e82d22afae2c6e279a2bd9a5b22b23a65c2b009eae2adce7bc2902c6f728e55b0d28e38c4e285e9f6f2848d5bd273a86802723e9ab2705880d263b036f25e924dd25ae4f0124c372e7243c172c240f87f823dd073c23a743fc22c4e84a217c18ce215ab7711f438acf1ef254801ee50e861e64a3c31e02d8001db4a4271da04c391d289b541d0b2f6a1cfdf5c51caede251c4c210a1bf6a8921b9386ad1ae1c6821a58fe181a10f6e5
  | 5, 2 => 0x5263178f51ef299251a40ee9510fedab5105b6dd509ac928504a9df2500d4be74f8098334f2cf3354e1eb31a4d99d2864c7acf5f4af443bc4aa59fc74a899ff94a24047e49aaec22477cbdc8477c31a44705cf5646f6267046d68f1446b110c04645a3f54643b5a545eb196445ce0d59452937d5440a007d4396c736431a711442f1fa8b42ce706c42b779a34235772a40f6666f408a682f3f2686f63f037a0c3efbc18d3ef02b013d0e4d583c9d75a23c78af4e3b8a51df3b0081d23a8367283a792f6a3a4d6a953a388a3738e1164638c28e57389a23f9388f8f2537d860a0377ab9dd36a8c23836812025360aefae35ee51be35e7ff7635dbbbb0359826f8
  | 5, 3 => 0x817ddf5980edd4f0802e890e7ff2b2087ff0695a7f6313a77d0f0ac67c8831a27c745e417c306b6d79e6d45179c0a36378cda554788b198f778ad8597680fac475311537732cec1272ac283571c4c2dd711ac2337012ccdf6f8edb406f7ca6206e99b4d86e97547b6e5a6e856c8b22b96bd11c156bcf90f36ababa2c6936bd0f678c34f863f3e9a16308ebc862bd28d8628c1e656215319461f5a73b618dfa0560635c9b5ff943825f76041a5f74d2f65e3fd68c5e20d1735e0e30375de239445cdb91705ae7ae295aa8a6b95a6112825953a34858d5e2955865c80957a5936e57160f94556f0695553d3ac154f15b3b53b991c6531a12905318541d52be2f94
  | 5, 4 => 0xc5d82c72c194ef38c036486abf9ac3febf8705ebbdee9ca0bc8249c2bc03177bbbb787aaba95ed65ba48e8d1b99673e8b8b408b6b7c8876db7a1fd24b771ea1eb5e2cbdab5ac93d1b45e17d7b3fad78cb3bdf196b37da600b2f8b09db105689cb06d7fccb065425badcb99c7aaf5732faad69f3ea82d1a2fa81e7370a7ce168da6f17d16a6432819a5296cc5a48f4794a3a9d24fa32e582aa01d11f79f1ccba59f118daa9dd669619d108db69c2c002d9b34369197bea2389708ff3f96d86ce296a6d4ff96a47b2f964b0e81961a44a1952cd52a92879af98d92204d8d8fa01a8d65f46e897431fe882be4e186a4d00a8672c166855c86f08211e0e081d6d650
  | 5, 5 => 0xfd058035f9acd0faf96feb04f0f8df95f0159b22ebafba7be907f834e7cfc807ddd3ac13d9bf0dd2d8512116d68fe03ed4de3103d3874271d29944e0d1e468bbcde65e1acd4d3577cd40a50dcbf4f15bcbc0dee7c73fff91c69fce5ec65db2c7
  | 6, 0 => 0x925d5bd091999780913c1b1090dfc8408de99ae08cdebfc08c12dc408b51a45084aafc707a72649078c60020787d7a5074eba940749214007246e5906e5daf306dc984206ad70f90681af190665520c065bfc790617f3be0608061805fd0f1105f2ecc205bbae7e05b8649705a123ff05687e8905169eb00512d18904bca65904b12ffb048d5ee60479bbe10472ece0041db66f041b5fb5040d80d603f1b95203a0960e03833f26037f6899033a727c030d3b3002c16857029bda2f02734c9f02470b1b024365d60240cfa301f5db9e01d78abd01d18b1e01c9b31e01a6e4da0185f46d01652a320146c416011eaa2f00f5a3d20096f2260082d9db00296567
  | 6, 1 => 0x13728f561349e7ce133c08ef130a5a8912dbba7612d1fe40129e663b1277791b1234695d1233466a121558d811ce639111b4bd5b11a18517119b91ab1187183a115b67ca108ef5b9107fcacf104ad074101f34a210105d9b0faa77070fa2a5570f47a0390f37de040f31b5270ee2d2210ee271f80ea800b80e7e15130e67dc250df124ef0da46fb90d9cbe430d9a92370d95c7350d6e8d170d6e7ee10cfc43180cedf22c0cd896110cd4b54f0c8f5e1d0c83298b0c18c4240c04ca010bc7415d0bc252a20bbb8e270ba9c0d30b8ad6cc0b2c8ce60b28f6400b1a7d630ac4d5b90ab8b2690ab629b709f7ca3e09ede5f809bd51ef097c0ec409598a57093e7356
  | 6, 2 => 0x1b933b9e1b8548e61b78d4bc1b6a04111b6624961b62a5db1b55df541b40c0441b3ea0591b24771a1ac6cf551a7bac721a4058c31a2639791a04d97919468cb71921f28d18ef4baf18eabeb418ac994f188e19d01882b169186366e3185955ec18545dd6181a048118103f8818043d6917e170dd176346e0175a929b17563868173643a8172decb91712096e170e9bbf16bcc03716b01e5416a82ea1169cdf8d168bc85d164f38e016424e12161b95e21611817415f71c1b15f3a94215ea9fee15e9498b15776f951561a43a156020141517feab14adee101499cfe5148428011436a47013fd04b313ea83c213e0e2a713d6d81d13967e2f139302bf138cad00
  | 6, 3 => 0x252f3bbb250aba5724dc2681241d3313240f87f823fa873323d675a923aa74da2325c90b231bcad9230229b922e55f9722d25b5c229eb02f229998fb228802542256b04f21d8db47213bddeb20e249a720cfb40b2064873a205b0a2a204b60b6200df9ca1fd652f71fc76cfb1fb72b911fa432931f8738591f75faad1f6fbf471f3a85a51f3387171f3108e21f09477c1ee50e861ee07af31ec0fa371ea60e4c1e003ae81df468421db574801db432881d826c881d5319ea1d4c60a11d07cbc61d0122a41cce2f151cc5aa5e1ca3d9531ca0b1831c96ea491c7f55261c5a70d51c397d011c32bad41bf0c1dd1bdb5b301bbe42c21bb1776b1b9ff3ad1b9d622f
  | 6, 4 => 0x317af60a31381b07312ae6df30d5282030b973d6306f6ccb2fec250b2fc6445a2fbf5da52fbf35272f7a8db12f3c81e32f03b74b2efbd9642eba05a82ea1c1f32e3061ae2e2eb6002dfdbfd52dec4b6b2da6f7032d7d41f82d618f3b2d2230702d06d0c22cf8cd042cf6f6a82cadc4612c7dc05e2c2fc9bd2be8c6dd2baefdce2b79d3f12b4ef7cf2b20b3d82afe09d52a86ebca2a14d0f72a121f8d29f0b1cd29c478db29af2b64297c99f8296af49a296669a2294399dc293f76f029342757291d2a9e291385ac28d3f68428c73e9828367c31282426c92819312c281910472759c577275958f22751de46271aebe72713cf0026b368532668cbab259a3137
  | 6, 5 => 0x3c66947b3c38e0113b9031bd3b72da473b5624293b34c0e23acf9b4b3abe07193a4cde683a388a373a2d6c6239ff1f0a39ab24c4394f142039200c0d390153ab38eec90038c8629238a4a5e2389a23f93891e84737d8b58137b0b971379a618237962c633769570f36e9c65936cb597836a8e1d9369e286b3668643f36648703364ef29f3610c82c35974020357321f835239d6d34fe1fe134d2fbb734a771a73492603134886bc33481847a347184a0344f47aa34064f6c33da662c33d93c6b33ce1343339be8303398d185338e027c33864f1f335d819533359bf43326d9133316827432e38d4f3294f0e0326bf53f32483a4f31f5eab331f21e333196b900
  | 6, 6 => 0x4a1e617149f0e1f749eb066449d9a14a49d72e8749bd383749b6983f498effba497253c148c32bdf47ee69e847d7f35a46ee463d46df279b46bddc5e46b9685546769a764617f588459774c245940ada4526b4084523bdd944d46f7844c79b8a4408d56743aea1a4439c172043555fb042b779a34291ffc94270b5be425327d741d22c9a41b3665641ae33e241ada2b441a58777416eec4f414a8c1f4119dfa1410ee2ea40a60e3740936de14071490e40455b7a403b69b73fd84d593fca2bf63f732d3d3f2cd2183f086e6d3ef9b7083e896cb83e7b57fa3e79bb8a3e55bbba3e38a55b3e277fff3e0954d53d820b7b3d57f2ca3d44b5c43d2c7c353d256209
  | 6, 7 => 0x55bf057b55a0239d5582b7b3556f06955567a850555d1ca25530a86c54f251df54c9884054b25c705459014c542510755416d04b53ee2a9c53cd1deb53cb5340535b8ef053447d0452f2e65052a599fd528866f75281620b525afe54522a08785209977e5184da3a5160844351501bab5137e9295124950150659ad7504ce257504a74d8503182d9500139404fc71f074fc559f74f9d2f8d4f7141a24f19bfb24f08c8964ed752244eb37e644ea4fa1c4dd3ad484dc9c7c04d977a104d43334a4d2f3d364c9d92c64c4ab93a4c1e35cd4c1326ad4c1064844b75ea1e4b40518f4b226b904b21fba14aee73794acdf8d54ac64d7b4a8b09ee4a8a40314a3f5f3c
  | 6, 8 => 0x642e54a063bad2eb63aed3aa63a6a9d362dfa08f62da87e162bd28d8628c37a3624ac82b61f5a73b61ca400861818f6f6178b77d615ba5fb613f4bb660ca36e160c1af3f60a44355607f3e8c5fa9e2065f4ce3e85f27f51b5ee4680f5e5e95475e13ada65d5624535d4b941a5cde0cce5c5ce06b5c098ff55bf13ab45bdd230c5bc0ce6c5bb03c075ba3354b5b00c4075aecd9575ab003015a9f5dfd5a8723c85a353b1759f684b259a0c2fc59254669591e47e6583019b9582969ea581a3e365808a35357ab48c1576f03e7576c925c576aac01576751eb576611cb574c638e56f13b0e56d3b3db56b4469856aaafbf567c7f51563580cb5615047155f67480
  | 6, 9 => 0x73ea5b6e73da4b1a73be3a8b739a2d4a7388972f736f42c173493a277317072172f1b40272b28339727718da727253ef7221207371ca317b718aa31d7179360f716e00617129e8b070da344670aa5d9370543772701fd2906f4ebd9a6ee7589d6dd08b0e6cfdbf986cf529646c9bdae26c7e6ef86c64d2026c4b6e046bd3e8686ababa2c6ab1a0db6a8097696a44543e69cd7e5369c0add469846ed56936cae36909bb4668d3280d6896eaea682c83d86827ae8568149ab1680dfb0f6786b847678524796776f0786742e730673f974f671ea51e66d1c7a966c97e4e66700a1a661f8dfe655b3353653364ff6502386064e6ab0264b23f0e6472b701644a97a9
  | 6, 10 => 0x83c0be098398fa6c834c2dc0833df90382de7117828515b88276397281e62af881b76e8e819b470f81086da0806266ad7ff0695a7f8776eb7f685e077ee5d8e17ebbf6017e6cc6297e63c5ee7e4dc0ce7de29e817db1e1917d304f3a7cfde4937cea112d7c69c65e7bab0f147ba3c0797b6ec17b7a8ef3507a0875a379e5550479d3e13a79c2eecc79bb6d1e797abaaa79684f627955da0f7951d57878e65c2c78d82dee78d1319678b8fe8c7877b05377abf4137753784a7710f44076ef06c676d063dd764e5f61761e2a877614107e7613d46a7603a98f75d32c7d759b9aea75404ca07522e0b67508aada750876887495e96f74789e6474068ac973fa28f2
  | 6, 11 => 0x97ebea0897012b8496d7a39896a47b2f9515305d94ce77af94b8834e94933acd943ad53594062d5193f0934d93e24993935ddd6e935371a9931f23ef92d1d6d892cd311e91fd1dbb91e61fd3917fb21d912821e490f68a7190edb58d90e225fa90db4d0e8fe77d2d8fa2db658fa19e1f8f6057d08f1f96978e88272c8d8d08b08d88441d8d6a7b858d395ff68c3f36198b4da15b8af097cd8ae257588a7994f88a4c27bb8a4b2c5689b52b50899b6c728974814d88e36b158890c621884052b7882be4e1880c62cc87f2d3ba87ea0dcf87be0786879add678798e1248742e1478625e7dd85f6241e85d48fa38527bd3a84f50771845f90f784569c0883eaa2da
  | 6, 12 => 0xb93206deb8767b00b729f7fab70ac2a9b64ecbd7b44d8ebab285abbdb1b8a042b192c005b0d5dbb4b0d3c397b08080b4b064ed4daddfe763ad7309f1ad58a5d0aca9b064ac41a9b3abe10579ab676f4fab671e17ab30f7eaaa1f6e87a909e4c1a828f69ba7e9f7b1a7853e24a7470e27a72fdc37a6fdec6ba6dfcc07a6a209e6a5fa6e2ba4dee153a4b188daa41794aaa3d87e06a3913837a34731dba195b11ca1558ee5a1521c33a027e35e9fdc65479fa7e8e29f843b4a9f6676b19ef41ebc9ed6de7b9ec9ae489ebfb44d9e5fc6b79e43f1059db392919daae7359d6c560b9ca89a239bca9a899b56d6249ab91a0099bed3f9986d00ac9848610498386cf6
  | 6, 13 => 0xdec1b6bdde99cc50de86f571dd9de376dc8a5345dac25fdada8d8f9bda362501da1bab7ed9cbfa25d9ae4b1dd9840b17d8af4f05d7adc8ffd7783301d7482c02d670e039d568b144d4e47617d2aeea40d23c0f2cd1ffa714d0022fedcfafaaccce5c094bcdf98342cc56fb91cc1a159bcbae6cbdcb18ca29cac50cf0caa28a59ca1c68dcc9f4ae78c7e898c9c7bdffc1c70560b5c6d0b208c6c817b7c60a9cf9c59d6c30c4949487c48fe98ec453a13bc4356e0fc41ed601c41dc00bc337f1aac330a8d4c30d6fe3c2afde01c1ebf1e0c1698805c104a00bc05fc100c01d1494bfb4dd66beea5a39bec0a575bc95da00bc591900bb13142ebaa8c339b9f84562
  | 6, 14 => 0xff98826cfb4809cbfad8dc57f9b99d75f7a45692f58f108cf2854adff205d3fef0f8df95eebe9aeaee365bcfee02495bec9d1042ebc7f551eb408a7fe93c0117e5e351dce56c6f69e2e5bc00e2b58d36e277b2dee254a19ee23cf087e0800c8ddf7dc165def4681fdec9dac1
  | 7, 0 => 0x17d07b00175a929b170db67f16a82ea11581f8c81561a43a1528ba3c1415063f13b5da6d136d10ac131bfefa1317dd2b1308cd7712b8ab4112b8884a12ae5da3129997eb124e263511ed84b711eb7ccf11d748061187183a1134c9340fc22fb60f8898390f3badb20edd17080e8414b20dfe576f0dfb96ef0d61f2fb0cf91d9f0cc7aa850c867e660bd753a90bb2ffb10b41c7720acf09dd0ab7b9ae0ab0afbb0a71f9560a172c4909f5ca2f0878675807d82e3c07bd347d07af559e06ecbabd065223ce064612c705c61dd605ad2f3405a3eb0a059e8b1703e36454036df1500296f5790291d00a024a740d023f103c0198251c0188fb4b0129b75500273479
  | 7, 1 => 0x29f0f18429e942c429c478db291abe562889888f2882e2b2284db2db2775450f2774c460275958f22727707326d2458e26aa53c326a4b5bf264ea12126488ebe262d41fb2609324125bece64258a6ea4255ffecb2485a93423a7fde62310763b23038dd422daf26b22d85c9a22543c1c223682592219ec0a21e9d24d21a5f96820df43cc2081cc612064873a204aaf2d2046aaad203cd04e1f608b651f3108e21ebb13731e8eec381e1aa3ae1e08e1531d89743f1d73f5661d29fe0a1c1ffead1b78d4bc1b70b1901b61a0cd1b52f3321b325a461b2d157f1a45ab1d1a2bfa9c1a0dc40d19f08aad19e360491979f4171900f42918e3fb0a183e8305181aa941
  | 7, 2 => 0x41d622d341a8390640db2d8b40ccbe13405c8f3d40455b7a3f49363a3f086e6d3ee6de3d3dff89d03d8620523d0124c93cedcf813c9dc2fe3c39fd5e3be08ad93b5624293b23954e3acd3e823a861c99396f572d395003403899ed18387c221637dd7e8037a1ed1c378f31e8375fd1e83724f45b36e4026d36b6da9236ad51603678c0eb363c57f436224d1b361b1af4360aefae35d89aaa355e29ce354bc4fd3481847a326a06213264f194315024ba31381b073129ad3f30ccd1eb3055c0a62fc976f62fa1c82a2f1d68d52eedfa852ea0b9112e9e70832d6df75a2ca821632c9946a22bdd94e82b81626d2b0f56702acd7a982a7c85282a60bc7d2a5e00e1
  | 7, 3 => 0x5923c1c65905159658a5f17758905d135806ebe257c3519856abec62568ff7f156240dff55f35c3e55ab6c46558b87505550dd6c54ed1c7554b47b9853b7a8b55342fdb75316929452f2fea452acbe7d528ca242520a3fab515c2919514f645451099cc651007c3a4f9b055d4f717d1d4f5ddbaa4e7327324e00c0ea4de27c5e4dd111674d2b306b4d0476064ca60af44c173de94c1326ad4bff26be4bb8974e4bb13b214b7591cb4b62f61f4b40518f4ac0774d4a6707154a24047e49148db048fa38cc48f0bd7d48ebd2aa48b0ac9d472e33c146e1bded465e79d54609964845f6b584457c5ed144d9dfff44cd758b43555fb0433f660a42b779a34223bdb9
  | 7, 4 => 0x7341d2fd73227b8e72b2833970c4152b7005f1236fa6c90d6f6c29a26e9f1e276e38e6f66e1ad9ba6db8095f6cd622c66c4b6e046bcf90f36b89f08a6a510b3869f5d2f969c031bf697c1303692e70ee6920920f68ff5c7d688d1b5567f1c0d3668c47706659a12a6635754264ffcc4e64789948645092fc6347643b633af011633635116284e04361f427ee6129ea296001a2b65f5d13a95ec6f1c75ec2fe405ebcebc25e90082e5e1657ce5e06e6065d9647d45d93d62e5d6275f45d23bf8f5d1e66bc5d1d08615c9fbd605c91de815bff541c5bec8f385bdfea355b2acd595a73054d5a437adf59f684b259f223e559e5330159d66aa059d395c75992adb0
  | 7, 5 => 0x94b8834e936159ab9351acbb91b98d12906d26119011f582900c696690061e318e35cdb08e2374cd8dbfa66d8d92f6958d7f04bb8d6fdaea8ce77a638c1a6ee88b8fda438b3e939c8a8bfac789beef4c899b6c72897643b6886bb2a587ec230287080352868cb424862851b985210b0383f048fb83c5bc52833df90383233d80830766bf82ddd8a582d3eb9982739f208241b059806266ad804281917fc0036d7f97da8d7ecd8d627ebbf6017db1e1917d356db97d303bbe7bc86ac17ae97d0f7ab2c9087aa157477a85129f79e15a2879a4d76c791d9b417900675a78493a7f7770373f7733bc5376db0b2e76b015da74f2245d745a681c73a4532b73a1eeb7
  | 7, 6 => 0xe2f02cffdfb32b5bdf7fbf91de1b0bb2d988b69cd8f62b1fd6890d25d5d7c256d3b34341d355d4ffd0e5095fceecb93fceeb1ad8ce6b8b90cbfcbae9c707ac1ec61b5c10c59d6c30c4ac2c82c21dcfbbc16463c6c150c440bf46884bbf01fb40bef1afedbcc8e334bc18011aba2399e2b85c2f59b59a84ddb559ed2fb22e7c90b0ec7e1fb0480e0db031ca64aee65ee3abe5308aaa21bb6da96c2da6a77ce252a661d0dfa62fa927a5e4c2a9a302d5f5a1b25c0ca0c045e2a07b39919eab30d29e6bbe4b9da1794d9d61744b9c36144f9bfcd7929a81c9ca99ed5e87997d4564992721c298553ede984899db97a5128c965f3458965531e6963c456d955a0898
  | 7, 7 => 0xfbefb591f9b99d75f96feb04f4642245f32a1730f11d8484f05fc8f2ef0e3eb4e7a75556e7199440e5d4dd4ce33582db
  | 8, 0 => 0xdd9de376a6563cc35fbac6fd5e22a75455df5df85059633d4f8c57c242b779a32eedfa8521b9f7ae1e7359ed1729918f1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x454c9504c8400
  | 4, 0 => 0x4110400005454043006704145440400000000004110432515504c840000118324c83006704145440400000414544030032545504c8400001155148c3000011430041300751193004140000115504c830000115324c830032515504c84000000000000002000000004110400000104402010000042405204450d921005400000000004110432545504c8400000c9504c83000000000041104
  | 5, 0 => 0x500000001001030000000000005000000000000200000454c0201000000000000600000254c02010000000109104000000008c101000005148c20100000000000050000000000006000000000000500000000411040000000041104000000010810200148234c53000000000000001000000000000600000250022000000000000003000005148c20100000454c820100000000000010000000000005000000000000600181250c5300000000000000600041454403000000000000003000c1254c030000000000c8100
  | 5, 1 => 0x109104000d431405300000000004110400000450c120000000000000010000045005200000000000000100000000c0100000000000000600000214842010000000000004000942044130000000520c52010000000000001000d921005300000005148c201000004548c2010008535484300000983048130000041454403000000045484200000c9504c830000185350813000008d5148c30000000324c8200000004548c200000003508120100000000000060000000000005000005048420100000000000040000035081201
  | 5, 2 => 0x51040000000000005000000000000600000304c0200000005148c200000004548c20100000000000040000000109104000005148c20100158304813000000000000003000c9454c830000000324c82000000000000003000000000000200000454c020100000000000060000000000004000000004110400000000000010000000000005000000000000300145504c830000000504c820000000000000040009930041300000003508120100000000000050000000000006000d82544130000000304c02010011905841300
  | 5, 3 => 0x60000000000002000005048c201000000000510400000514c820100000454c8201000000000000500000000000060000000000006000983540530000000324c820100000000000040000000000005000000000000500000204802010011921005300000000000000400115504c83000000000000001000000010910400000454c020100000304c0201000000000000500000210052000011430041300000d8214c530000000450c92000000000000005000000000000500000000000050000000000003000002540c201
  | 5, 4 => 0x4110400000000000020000000000000000414544030000000254c0201000000010810200000250c52010000000000006000813548030000000454c02010014c3248130000000204802000000000000003000000000000500000000000030000000000005001181044030000000000000060000000000001000000000000100000454c8200001192500230000000454c820000181250c530000000000000060000000000001000000000000600000000000010000000000000000000000000300000000c810000148214c5300
  | 5, 5 => 0x324c82010000000000006000000000000200145504c830000000454c0201000000010d102000000000000600000104402010000000041104001192100530000000304c0201000c9504c8300000000000000600000000000010000050484201000000000000600000000000010008d5148c300000000000000500118324c83000000000000001000000000000100118304c03000000000000001000000004110400000304c02000000000000002000000000000100000000000060000020480201000000000000600000000c8101
  | 5, 6 => 0x100102000000000000600118104403000015830481300000005148c200000001044020100000000000000000000000005000000000000600000000000020000000000002000004548c201000000000000100118324c830000000254c0201000000000510400000504842010000021484201000001044020000000000841000000000000005000000000000500000000000030000000000006000004548420000000504842000000000000006000000000000600000204802010000020480201000000000000500000504c8200
  | 5, 7 => 0x119210053000000000000005000001044020100000000000050000000000004000000000000600000000411040000050484201001142044130000098354053000000001404200000c5254c4300000000000000100115504c8300000004540c2010000000000001001155148c300000000000000100000314c4201000000140420100000454c8200000d825441300000003208d201000000000000500000000c0101000c9504c830000000504c820100000504842010004145440300000000000000000000254c02000000000000005
  | 5, 8 => 0x500000354842010000000000001000414544030000000324c8201000000000000600000104402010000045448201000c9504c8300000000000000500000030c1201000000000000600000214842010008d5148c300000000010410300000000000030000000000006001583048130000000454c8201000000000000600000324c820100000204802000000000000001000000000000200000000000050000000000001000000000000100000304c0201000000010d10400000000c0100000002048020100000254c0201
  | 5, 9 => 0x2001183540530000000000411040000050484201000004540420000000454c8200000414544030000000324c82010000010440200000c9454c83000004145440300000000000000500000000000010000000000004000005048c20000000454c02010000000000006000000000000400000454c820100000324c820000000454c8201000000010810200000314c420100000324c8201000414544030000000324c820100000504c8201000005048c201000000000000300148214c530000000001091040000000000005
  | 5, 10 => 0x8c100000002348c200000000000000100000000000040000000000006000000004110400000000000060000000000005000000000000000000454c0201000000000000500000454c820100000000000040000000000004000993004130000000450c92000011810440300000000010d1030000000041104000414544030000000000000020000000100102000c9454c83000004145440300
  | 6, 0 => 0x100000000000050000000000003000000000000400000514c0200000000000000600000454c0201000000000000100000454c820000000000000030000000000005000002540e200000000000000400000304c0200000000000000600000000000010000000000001000005148c20000000254c020000000000000040000000104103000000000210100000058c12000000000000001000000000000400000000c1101000000000000100000350812010000000000001000000000000300000000000020000000000000
  | 6, 1 => 0x2000000380a20000000000000010000000000006000005148c201000000004110400000454c8201000000000a1010000000000005000000280220000000000000020000045404200000002348c2000000000000003000000000000200000254c020100000000000040000000000004000002348c20000000000000050000000000005000000000000500000304c020000000000841000000050484200000000000e101000000000000200000254c020100000324c8201000000008110000000000000030000000000006
  | 6, 2 => 0x400000000000040000025002200000000000000500000000000010000000000003000000000000400000454c82000000000005101000000000000000000324c820000000454c020000000000811010000000000003000000010910300000000c110100000454c0200000005148c20100000000000010000000000001000000140420000000204802000000000000004000005148c20000000000000020000000000006000005148c200000000008c101000000000e1010000000000004000000000e1010000000000003
  | 6, 3 => 0x600000304c0201000000000000200000530852000000000000003000000540a20000000000000020000000000003000000000000300000454c020000000000c91010000000000003000000000000300000000000040000000000002000003540a20000000214842000000000000005000005148c2000000000000005000000000000400000000000040000000000002000000000000500000324c8200000005310120000000000000040000000000001000000000000300000000021000000000000003
  | 6, 4 => 0x35005200000001044020000000000000040000000000001000000000000300000324c820000000514c020000000504c820000000000021010000000000006000000000000300000450c120000000314c420100000000c810000000350052000000000002101000000008d1010000035081200000000000a100000000540a20000000324c8200000005148c20000000058c920000000000c8101000000000a1010000000000003000002148420000000000000020000045041200000000000a10100000000000050000000000006
  | 6, 5 => 0x8110100000000000030000000006100000002044120000000000c81010000000000002000000000000200000504c820000000254c0200000000180220000000304c020100000454842010000035002200000005148c20000000000000020000000000002000000000000200000254c520000000514c02000000045041200000005148c20000000000c110100000250062000000020480200000000000000200000354842000000000000004000000000000200000000000040000000000004000000000000300000314c4201
  | 6, 6 => 0x100000000000010000035484200000004548420000000000000040000000085101000004544020000000000000030000000000002000000000000600000000c51010000045085200000005148020000000454c0201000004548c200000000000000200000514c0201000000000a101000002348c200000000000000600000000000050000003806200000004548c20000000300412000000000000003000000008110100000454c0200000005148c2000000000000003000000000000000000204802000000000012100
  | 6, 7 => 0x400000000000040000000000006000000000000600000504c8200000005048420000000000000030000000000002000004544020000000000000030000000000002000000000610100000454c82000000000000005000000480e20000000450412000000000000005000002148420100000304c0200000000000000400000504c82000000000000002000002148420000000000c910100000000000020000045484200000000000000100000000000020000000000002000000000000400000000000020000035484200
  | 6, 8 => 0x58c920000000250412000000035480200000000000c1010000000000002000000000000300000000000000000000000002000000480a20000000058c5200000000004110100000000000060000000000004000000000000400000104402000000000000001000000000000400000204802010000000000002000005148c2000000030481200000000000000500000000c810000000000051010000000000003000000000000200000000000050000000006101000003540520000000000000030000000002101
  | 6, 9 => 0x1000000008d10100000504842000000010440201000003140520000000314c42000000000000005000000000000500000504c820100000000000000000000000001000000000000200000514c020000000000c410000000000000000000000000003000000000000300000000811000000000000004000000000000200000000c910100000000000040000000000004000000000e10100000000c91010000000000005000000000000600000454c8200000000000a1010000000081101000000000000100000314c4200
  | 6, 10 => 0x404412000000000000005000000000210100000000c51010000000000000000004544020000000000c510100000304c020000000514c020000000254c0200000000000000300000504842000000000000002000000004110000000304c02000000000000006000000000000300000000000050000000085101000004544020000000000000050000000000003000000000e100000000000000200000000000010000000000003000000000610100000000000020000000041101000000000000300000214842000000053109200
  | 6, 11 => 0x45041200000000000000100000000000040000000041101000000000c1010000000000002000000008010100000454c820000000454c0200000000000000100000304c0200000000000000400000104402000000000000001000000000000200000000000010000000000006000000000000200000000c9101000000000000400000000c81010000021484201000000000510100000504c820000000000021000000000000005000000000000200000000000000000035484200000000008510100000000c41010000010440200
  | 6, 12 => 0x84101000000000000300000454c0200000002348c200000005048420100000000000050000000000002000000000000100000514c020100000000000040000000000004000000000000500000000851010000000000002000000000000300000514c0201000000000000100000254c020100000000000020000000000002000004548420100000520c1200000000000a10000000000000040000000000004000000010d100000000000000600000324c82010000000000002000004548420100000048062000000020480200
  | 6, 13 => 0x304c0200000000000000500000000000060000000000003000000000c10100000254c020000000314c42000000035405200000002048020000000514802000000000000002000005148c20000000454c020000000104402010000000000003000000000000200000254c020000000000c4101000000000000300000000000010000000000001000005148c2000000000000002000000000000500000304c02000000000000004000000000000500000000000030000000000000000000000610100000304c02000000000000001
  | 6, 14 => 0x6000000000a10100000000000020000000000002000002048020000000314c42010000000000003000005210d2000000000000002000000000000500000000000040000000005101000000000e101000001044020100000000000030000045005200000000000a10100000234c520000000250062000000000000005000000008c10100000000000020000035484200000000000000100000000051010000000000003000000010110000000000000010000000000000000000008110100000000000040000020480200
  | 6, 15 => 0x300000000000050000000000005000000000000300000514c0200000000000000200000000000030000010440200000000000000400000000000000000020480201000003508120000000000c0101000000000000500000504c82010000000000005000005148c20000000000051000000000000005000000000000500000504c820100000314c42000000000000001000000000000500000000000020000000000004000001044020000000000000010000000000006000000000000600000000c01000000000000004
  | 6, 16 => 0x60000000000002000000000000100000000811000000000000000000000004110400000000000020000000000001000004548420000000454842000000020480200000000180220000000250c52000000035006200000000000000300000000000000000020480200000004548c20000000000000010000000000005000000000000200000000000050000050484200000000000000400000254c0201000003548120000000324c8200000004548420000000314c4200000000000510100000000c41010000000000005
  | 6, 17 => 0x4000000000510400000000061010000000000002000000000000200000324c820000000504c820000000454c0200000000008c101000000000000000000000c1100000000000000300000254c4200000000000000200000000000050000000000004000005148c20000000000c81000000050484200000000000000600000000000020000004802200000000000000400000000000020000000000005000000000000100000324c8200000000000a100000005148c200000000000000200000000000020000000084100
  | 6, 18 => 0x200000000000050000052105200000000000210100000000000010000000000002000000280620000000000c11010000000000003000000000000600000504842000000000000002000000000000500000504c820000000000000050000035404200000000000000500000000000060000000000002000000010d10000000000000030000030481200000000000000000000300412000000000000000000000000000200000000000040000000000004000000000000100000000000010000000000003000000000a101
  | 6, 19 => 0x1000000000000300000324c82000000000000001000000000000300000514c020000000454c820000000520c120000000000000020000000041101000000000000200000504842000000000000005000002348c201000000000e101000003548020000000000c5101000005148c20000000504842000000000000002000000000000200000058c82000000000000000000000000000600000104402000000000000002000002044120000000000000050000000000005000000000000400000000000020000000041101
  | 6, 20 => 0x10010200000000000030000000000002000000004110100000000c810100000514c0201000005048420100000000c110100000454c82000000000000002000000000000300000000000050000010440200000000000000200000000c01000000041405200000004548420100000000c9100000000000000300000058c82000000010440200000002500e200000004548420000000000c5101000005148c201000004548c20100000000000020000000000005000005210120000000504c42000000000101100000000000a101
  | 6, 21 => 0x1044020000000454c8200000000000000100000050062000000000000005000000000000500000000000030000000000002000000000000200000450c120000000000c110000000000000030000000000004000000000000600000454c8200000000000000600000000c510100000000000040000000000006000000000000600000254c0200000004540e200000000000a10100000000c810000000000041000000000000002000003540a20000000000000020000000000002000000000000100000000c81010000010440200
  | 6, 22 => 0x5000000008d101000000000000300000000000060000000000002000000000000600000000c11000000000084100000000000000500000324c8200000000000000200000000c0100000000000000200000000c110100000058812000000000000004000000000000100000350812000000035484200000002544120000000254c020000000000000040000000000005000005148c20000000254c0200000000000a10000000454c82010000000000003000000000000500000000000050000000040101000005210d200
  | 6, 23 => 0x454c8201000002500e200000003004120000000504c820000000000411000000000005104000000000000200000324c8201000000000000500000000041010000000000003000000000000100000504c8200000000000000400000000000020000000041104000000000000000000000000030000000084101000000000000100000000000060000000000004000000000000500000000000050000000000004000000000000000000454c82000000000000003000000588520000000000000020000000080101000000540a200
  | 6, 24 => 0x3548420000000000000010000000081101000000000000600000504c820100000000081010000000000003000000008410100000000000000000025006200000000000000300000300412000000000000003000000000000200000000c91000000000000002000000000000300000000000030000000000003000004504120000000314c420000000000000020000025440200000000000000600000000000000000045441200000000584120000000304812000000000000001000000000000600000000000030000000000004
  | 6, 25 => 0x21484200000000000000200000000000010000020441200000000000000300000254c020100000514c020000000514c0200000000008410100000000000020000000000002000004140520000000000000060000000000000000000000000400000000000030000000000002000000000000000000354842010000021484200000002500e200000000000000000000324c820000000000000060000000006101000000540e200000000280620000000000000060000000000002000000000000600000000000050000000000000
  | 6, 26 => 0xc810100000254c02000000000000005000000000000200000214842000000045440200000000540e2000000000000001000000000810100000000000010000000000005000000000000300000450c9200000000000000600000450c9200000000000000200000304c0201000000000000300000000c810000000304c020100000000c1101000004140520000000314c420100000454c820000000000000010000000000003000000000000400000000000050000000000004000003140520000000450852000000052101200
  | 6, 27 => 0x254c0200000000000000200000000000010000000000001000004544020000000450c9200000000000000500000000000020000035404200000000008c1010000000041104000003540520000000324c8200000000000000300000000000020000000000006000000000000100000324c8200000000000000100000454402000000000000006000002544120000000000000030000000000005000000000000200000000000040000000000005000000000a101000005148c200000000380a200000003500620000000234c5200
  | 6, 28 => 0x104402000000000005104000002500220000000454402000000000000000000001044020100000000121000000000000005000000000000400000058412000000045440200000000000000200000058c820000000000c8100000000004810100000454c820100000324c82010000005841200000000000000000000504c820000000000000040000000000005000002540e20000000000000040000035484200000005308520000000314c4200
  | 7, 0 => 0x30000000006101000000010910000000000000000000000006101000000000000200000000c4100000000008c100000000000000500000000000040000000000004000000004110100000000000040000000000003000000000610100000000c910000000000c410000000000000050000000000003000000001210000000000000030000000081100000000008510000000000c41010000000084101000000004110000000000000060000000105100000000000a101000000000000100000000000010000000012100
  | 7, 1 => 0x401010000000000003000000000000200000000000020000000000004000000000a1000000000000004000000000210000000000c01000000000000000000000000210100000000000020000000041100000000000000100000000811000000000000003000000000000100000000c1100000000000000400000000811000000000002101000000000000200000000c9101000000004110000000000121000000000080100000000010d100000000000000300000000c410000000000c0100000000000a1000000000000002
  | 7, 2 => 0x610000000000811000000000000002000000000000300000001051000000000041101000000000000100000000000030000000000001000000000e101000000000000200000000c510000000000000040000000000000000000010d1000000000002100000000000610000000000851010000000000000000000000210000000000c4101000000000000500000000c5101000000008510100000000c4100000000000e100000000010d100000000010110000000000c51010000000000001000000008110000000000c0100
  | 7, 3 => 0x101100000000000210000000000000020000000006100000000000a10000000000c010000000000061000000000109100000000000210000000000000030000000041101000000008d1000000000101100000000008410100000000c81000000000000003000000000000100000000000030000000000003000000000610000000000841010000000000004000000000e1000000000109100000000000a100000000000e10000000000000030000000000001000000000a100000000008110000000000c81000000000002100
  | 7, 4 => 0x100000000c110100000000000020000000080101000000000000100000000000010000000109100000000000000200000000000030000000000002000000000a100000000000a1010000000000004000000000e100000000000a10000000000c110000000000851000000000000002000000008c1000000000012100000000000610000000000c51000000000004100000000000000400000000c010100000000c8100000000000210000000000000040000000041100000000000000300000000851000000000000001
  | 7, 5 => 0x20000000005100000000000510000000000c110000000000061010000000000004000000000000200000000000020000000006100000000000000300000000c1100000000000000000000000c110000000000c41000000000085100000000000a10000000000000040000000000003000000008c101000000001210000000000401000000000000002000000000a100000000000610000000001091000000000084100000000000000000000000801010000000000001000000000610000000000c81000000000006100
  | 7, 6 => 0x85100000000000000100000000c410100000000c51000000000006100000000000000400000000c41000000000080100000000000000200000000401000000000002101000000000000100000000c910100000000c41000000000000001000000000a1010000000012100000000000a100000000008410100000000000020000000041100000000000000100000000000010000000000003000000000e100000000000210000000000c9100000000000610100000000000030000000000000000000000000000000000c4100
  | 7, 7 => 0x3000000008410000000000401000000000101100000000000000300000001011000000000000004000000010110000000000121000000000002100000000000000300000000c110100000000c9100000000008110000000000000020000000085101000000004110000000000401010000000000004000000000210000000000c510100000000c91000000000040101000000010d10000000000411000000000000006000000000210000000000411000000000006100000000000000100000000c11010000000000001
  | 7, 8 => 0x200000000c9101000000000000000000000021010000000000001000000010510000000001011000000000000000000000000000100000001051000000000101100000000000e10000000000c81010000000000002000000000a1000000000000005000000004110000000000c510000000000000030000000006101000000000000300000000401000000000000001000000010d1000000000000001000000000000100000000000030000000000001000000000000500000000c51000000000000001000000010d100
  | 7, 9 => 0x200000000c810000000000000040000000101100000000000a100000000008010100000000c110000000000c11000000000000002000000000e1010000000002100000000000e10100000000000020000000000000000000000000300000000c510100000000000030000000080100000000008410000000000000030000000040101000000000a1000000000000000000000010110000000000121000000000101100000000008410000000000c01000000000000002000000008110000000000000030000000000003
  | 7, 10 => 0xc01000000000000004000000000e100000000000e10000000000000020000000000003000000000000200000000c0100000000001210000000000c11000000000000004000000000000400000000c1100000000000610000000000000030000000000004000000000610000000000000030000000000001000000000a100000000000e1000000000081100000000000a100000000000a100000000000000400000000401000000000000002000000008410100000000c1100000000010910000000000000010000000040100
  | 7, 11 => 0x2000000001210000000000c910000000000c9100000000000a10000000000401000000000080100000000000000300000000c4100000000000e10100000000000040000000000005000000000a1010000000000001000000008510000000000851000000000006100000000008110100000000041000000000004100000000000000200000000c910000000000000010000000000001000000000a1010000000000001000000010d1000000000000002000000008d10000000000021000000000000002000000008d100
  | 7, 12 => 0xe101000000000a101000000008110000000000c81010000000000000000000000000300000000000010000000084100000000000e101000000010d100000000008410000000000c410000000000c81000000000000006000000000e100000000000000200000000c81000000000084100000000010d1000000000000006000000000000200000000000040000000040100000000000000300000000000020000000040100000000000000100000000411000000000000003000000000a10000000000000010000000000005
  | 7, 13 => 0x210100000000c810000000000c410000000000c810000000000811010000000041100000000000000600000000c8100000000000000400000000c9100000000000a1000000000041101000000000000200000000c81010000000006100000000000000300000000c51000000000000004000000000000300000000c0100000000000000400000000c01000000000000001000000000210000000000021000000000000000000000000a10000000000c9101000000000610000000000811000000000105100000000010d100
  | 7, 14 => 0x400000000000020000000000001000000000a10000000000c8100000000000a10000000000c910000000000021010000000041100000000000000100000000000010000000080100
  | 8, 0 => 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000010000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_5 roots_5 8 s ws hint
  | 1 => checkCutEntry dom_9 roots_9 7 s ws hint
  | 2 => checkCutEntry dom_10 roots_10 6 s ws hint
  | 3 => checkCutEntry dom_11 roots_11 6 s ws hint
  | 4 => checkCutEntry dom_13 roots_13 6 s ws hint
  | 5 => checkCutEntry dom_14 roots_14 5 s ws hint
  | 6 => checkCutEntry dom_15 roots_15 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_16 == dom_16) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_16 goalM u ys) : RunD dom_16 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_16 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_8 : ∀ i, 8 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_16 : ∀ i, 16 ≤ i → i < 24 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_24 : ∀ i, 24 ≤ i → i < 32 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_32 : ∀ i, 32 ≤ i → i < 37 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 32 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 37 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (z4_32))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_16 : ∀ i, 16 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_24 : ∀ i, 24 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_32 : ∀ i, 32 ≤ i → i < 40 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_40 : ∀ i, 40 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_48 : ∀ i, 48 ≤ i → i < 56 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_56 : ∀ i, 56 ≤ i → i < 64 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_64 : ∀ i, 64 ≤ i → i < 72 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_72 : ∀ i, 72 ≤ i → i < 80 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_80 : ∀ i, 80 ≤ i → i < 88 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_88 : ∀ i, 88 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_96 : ∀ i, 96 ≤ i → i < 104 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_104 : ∀ i, 104 ≤ i → i < 112 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_112 : ∀ i, 112 ≤ i → i < 120 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_120 : ∀ i, 120 ≤ i → i < 128 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_128 : ∀ i, 128 ≤ i → i < 136 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_136 : ∀ i, 136 ≤ i → i < 144 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_144 : ∀ i, 144 ≤ i → i < 152 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_152 : ∀ i, 152 ≤ i → i < 160 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_160 : ∀ i, 160 ≤ i → i < 166 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 160 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 166 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (z5_160))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_8 : ∀ i, 8 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_16 : ∀ i, 16 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_24 : ∀ i, 24 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_32 : ∀ i, 32 ≤ i → i < 40 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_40 : ∀ i, 40 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_48 : ∀ i, 48 ≤ i → i < 56 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_56 : ∀ i, 56 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_64 : ∀ i, 64 ≤ i → i < 72 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_72 : ∀ i, 72 ≤ i → i < 80 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_80 : ∀ i, 80 ≤ i → i < 88 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_88 : ∀ i, 88 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_96 : ∀ i, 96 ≤ i → i < 104 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_104 : ∀ i, 104 ≤ i → i < 112 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_112 : ∀ i, 112 ≤ i → i < 120 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_120 : ∀ i, 120 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_128 : ∀ i, 128 ≤ i → i < 136 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_136 : ∀ i, 136 ≤ i → i < 144 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_144 : ∀ i, 144 ≤ i → i < 152 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_152 : ∀ i, 152 ≤ i → i < 160 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_160 : ∀ i, 160 ≤ i → i < 168 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_168 : ∀ i, 168 ≤ i → i < 176 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_176 : ∀ i, 176 ≤ i → i < 184 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_184 : ∀ i, 184 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_192 : ∀ i, 192 ≤ i → i < 200 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_200 : ∀ i, 200 ≤ i → i < 208 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_208 : ∀ i, 208 ≤ i → i < 216 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_216 : ∀ i, 216 ≤ i → i < 224 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_224 : ∀ i, 224 ≤ i → i < 232 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_232 : ∀ i, 232 ≤ i → i < 240 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_240 : ∀ i, 240 ≤ i → i < 248 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_248 : ∀ i, 248 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_256 : ∀ i, 256 ≤ i → i < 264 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_264 : ∀ i, 264 ≤ i → i < 272 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_272 : ∀ i, 272 ≤ i → i < 280 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_280 : ∀ i, 280 ≤ i → i < 288 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_288 : ∀ i, 288 ≤ i → i < 296 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_296 : ∀ i, 296 ≤ i → i < 304 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_304 : ∀ i, 304 ≤ i → i < 312 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_312 : ∀ i, 312 ≤ i → i < 320 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_320 : ∀ i, 320 ≤ i → i < 328 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_328 : ∀ i, 328 ≤ i → i < 336 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_336 : ∀ i, 336 ≤ i → i < 344 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_344 : ∀ i, 344 ≤ i → i < 352 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_352 : ∀ i, 352 ≤ i → i < 360 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_360 : ∀ i, 360 ≤ i → i < 368 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_368 : ∀ i, 368 ≤ i → i < 376 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_376 : ∀ i, 376 ≤ i → i < 383 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 376 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 383 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (z6_376)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_8 : ∀ i, 8 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_16 : ∀ i, 16 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_24 : ∀ i, 24 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_32 : ∀ i, 32 ≤ i → i < 40 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_40 : ∀ i, 40 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_48 : ∀ i, 48 ≤ i → i < 56 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_56 : ∀ i, 56 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_64 : ∀ i, 64 ≤ i → i < 72 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_72 : ∀ i, 72 ≤ i → i < 80 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_80 : ∀ i, 80 ≤ i → i < 88 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_88 : ∀ i, 88 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_96 : ∀ i, 96 ≤ i → i < 104 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_104 : ∀ i, 104 ≤ i → i < 112 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_112 : ∀ i, 112 ≤ i → i < 120 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_120 : ∀ i, 120 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_128 : ∀ i, 128 ≤ i → i < 136 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_136 : ∀ i, 136 ≤ i → i < 144 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_144 : ∀ i, 144 ≤ i → i < 152 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_152 : ∀ i, 152 ≤ i → i < 160 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_160 : ∀ i, 160 ≤ i → i < 168 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_168 : ∀ i, 168 ≤ i → i < 176 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_176 : ∀ i, 176 ≤ i → i < 184 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_184 : ∀ i, 184 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_192 : ∀ i, 192 ≤ i → i < 200 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_200 : ∀ i, 200 ≤ i → i < 207 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 200 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 207 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (z7_200)))))))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 15 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 7 8 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 15 → Z 8 i = true := range_split z8_0 (z8_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_0 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := z9_0
theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_16 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_16 roots_16 goal_16 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_16 goal_16 := by
    have h0 : isConstB dom_16 goal_16 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_16

theorem low_16 : Lower dom_16 roots_16 goal_16 10 := S_16.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_16_bits : ∀ r : Fin 64, roots_16.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_16_lt : ∀ r : Fin 64, dom_16.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_16 T)
    (hlow : Lower dom_16 roots_16 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_16, Avail mask256 roots_16 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_16 hfan 0 roots_16 roots_16 rfl hsup0
  set out := (execN C.gates roots_16).getD C.output 0
  have hout : out &&& dom_16 = T &&& dom_16 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_16_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_16 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_16_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_16).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_16)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_16.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_16 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_16).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_16 &&& mask256 = dom_16 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_16 = T &&& dom_16 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_16, hd63, hout]
  have hnc_m : ¬ IsConst dom_16 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_16 roots_16 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_16, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_16 roots_16 0 roots_16 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4277074624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_16.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_16 10 hT6 (by unfold IsConst; decide) low_16

def wit : Circuit := ⟨[⟨GateOp.or, [1, 0]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [8, 2]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.and, [9, 7]⟩, ⟨GateOp.and, [10, 5]⟩, ⟨GateOp.or, [12, 4]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [14, 11]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_13143_aux

theorem PEqualNP.Outside.L_meta_13143 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4277074624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4277074624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_13143_aux.wit, PEqualNP.Outside.L_meta_13143_aux.wmono, le_trans PEqualNP.Outside.L_meta_13143_aux.wsize (PEqualNP.Outside.L_meta_13143_aux.lower s hs), PEqualNP.Outside.L_meta_13143_aux.weval⟩
