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

namespace PEqualNP.Outside.L_meta_15461_aux

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

def dom_0 : Nat := 0x2222222222222222
def goal_0 : Nat := 0x2220202020202000
def roots_0 : List Nat := [0x2020202020202020, 0x2200220022002200, 0x2222000022220000, 0x2222222200000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(5, 13), (5, 21), (5, 37), (9, 13), (17, 21), (25, 29), (25, 57), (33, 37), (41, 45), (41, 57), (49, 53), (49, 57)]
def r1sG : List Nat := [5, 5, 5, 9, 17, 25, 25, 33, 41, 41, 49, 49]
def r2sG : List Nat := [13, 21, 37, 13, 21, 29, 57, 37, 45, 57, 53, 57]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 3 => 5
  | 4 => 9
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe73e8db2638a94b747bbc86110fd39b60dad1aef
  | 4, 0 => 0xe73e8db2ae419c824c886097245168591f72f38f1d5845a5121141a01053b6540e4a9211
  | 5, 0 => 0xe73e8db2
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x22002200220022002200220020002000220000002200000020202020202020202020000020200000200020002000200002020202020202020000000022222222
  | 0, 1 => 0x222222222222000022222222000000002222220022222200222200002222000022202220222022202220220022202200
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xca744cb544ca924ca644ca844
  | 4, 0, 0 => 0xca7440ca714ca7545ca74050a7404ca7415ca9745ca7435dca745
  | 5, 0, 0 => 0xca744
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x368300060007000000ff807f
  | 0, 1 => 0xff0f80f78c7036f368
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xb69b69a605bf432129a4003b
  | 0, 1 => 0xff6fc4f7be72ffff7b
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 14 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 14 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 14 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 14 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 4 0) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 4 0) :: stateWiresS n (ids >>> 4)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
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

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_0 == dom_0) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_0 goalM u ys) : RunD dom_0 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_8 : ∀ i, 8 ≤ i → i < 9 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 8 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 9 → Z 4 i = true := range_split z4_0 (z4_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_0 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_0 roots_0 goal_0 6 := by
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

theorem low_0 : Lower dom_0 roots_0 goal_0 6 := S_0.noCircuit

def dom_1 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_1 : Nat := 0xaaa8a8a8a8a8a888
def roots_1 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888888888888888, 1, 3)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0x3333333333333333
def goal_2 : Nat := 0x2220202020202000
def roots_2 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x2222222222222222, 12, 13)] (by decide +kernel) (by decide +kernel) low_0

def dom_3 : Nat := 0xff0000
def goal_3 : Nat := 0xe80000
def roots_3 : List Nat := [0xaa0000, 0xcc0000, 0xf00000]

namespace S_3
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (18, 19), (18, 22), (20, 21), (20, 22)]
def r1sG : List Nat := [17, 17, 18, 18, 20, 20]
def r2sG : List Nat := [19, 21, 19, 22, 21, 22]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_3.map (· &&& dom_3)
def goalM : Nat := goal_3 &&& dom_3
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x25ebdbb0
  | 3, 0 => 0x25ebdbb0
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000cc00000000000000aa0000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_3 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_3 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_3 == dom_3) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_3 goalM u ys) : RunD dom_3 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_3 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_3 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_3 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_3 roots_3 goal_3 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_3 goal_3 := by
    have h0 : isConstB dom_3 goal_3 = false := by decide +kernel
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

end S_3

theorem low_3 : Lower dom_3 roots_3 goal_3 4 := S_3.noCircuit

def dom_4 : Nat := 0xff00ff00ff00ff
def goal_4 : Nat := 0xe800e800e800c8
def roots_4 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff0000, 5, 21), (0xff00ff00000000, 5, 37)] (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0xff00
def goal_5 : Nat := 0xe800
def roots_5 : List Nat := [0xaa00, 0xcc00, 0xf000]

theorem low_5 : Lower dom_5 roots_5 goal_5 4 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3

def dom_6 : Nat := 0xff00ff00ff00ff00
def goal_6 : Nat := 0xea00e800e800e800
def roots_6 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff000000, 41, 57), (0xff00ff0000000000, 25, 57)] (by decide +kernel) (by decide +kernel) low_5

def dom_7 : Nat := 0xffff0000ffff
def goal_7 : Nat := 0xe8e80000e8c8
def roots_7 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 6 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_8 : Nat := 0xffff0000ffff0000
def goal_8 : Nat := 0xeae80000e8e80000
def roots_8 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 6 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_9 : Nat := 0xffffffff
def goal_9 : Nat := 0xe8e8e8c8
def roots_9 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_9 : Lower dom_9 roots_9 goal_9 6 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

def dom_10 : Nat := 0xffffffff00000000
def goal_10 : Nat := 0xeae8e8e800000000
def roots_10 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 6 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_11 : Nat := 0xffffffffffffffff
def goal_11 : Nat := 0xeae8e8e8e8e8e8c8
def roots_11 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_11
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (2, 6), (4, 6), (5, 7), (5, 13), (5, 21), (5, 37), (9, 11), (9, 13), (10, 11), (10, 14), (12, 13), (12, 14), (17, 19), (17, 21), (18, 19), (18, 22), (20, 21), (20, 22), (25, 27), (25, 29), (25, 57), (26, 27), (26, 30), (28, 29), (28, 30), (33, 35), (33, 37), (34, 35), (34, 38), (36, 37), (36, 38), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (44, 45), (44, 46), (49, 51), (49, 53), (49, 57), (50, 51), (50, 54), (52, 53), (52, 54), (56, 57), (58, 59), (58, 62), (60, 61), (60, 62)]
def r1sG : List Nat := [1, 2, 2, 4, 5, 5, 5, 5, 9, 9, 10, 10, 12, 12, 17, 17, 18, 18, 20, 20, 25, 25, 25, 26, 26, 28, 28, 33, 33, 34, 34, 36, 36, 41, 41, 41, 42, 42, 44, 44, 49, 49, 49, 50, 50, 52, 52, 56, 58, 58, 60, 60]
def r2sG : List Nat := [3, 3, 6, 6, 7, 13, 21, 37, 11, 13, 11, 14, 13, 14, 19, 21, 19, 22, 21, 22, 27, 29, 57, 27, 30, 29, 30, 35, 37, 35, 38, 37, 38, 43, 45, 57, 43, 46, 45, 46, 51, 53, 57, 51, 54, 53, 54, 57, 59, 62, 61, 62]
def mpG : Nat := 0xfffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_11.map (· &&& dom_11)
def goalM : Nat := goal_11 &&& dom_11
def NN : Nat → Nat
  | 3 => 2
  | 4 => 36
  | 5 => 145
  | 6 => 285
  | 7 => 168
  | 8 => 17
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x4cf3f97a3ac8fc47
  | 4, 0 => 0x91f18ff38d9f87b38788178775d72d41757f40146cb2ebc0664c23c3528095db49f1d29440a60f4f3f48a59a3ed2ca3a3a5ef419399d17f4391e90d92fbf506c2e9be19f2bd2dd26266cbeb72638b64725974ba723e367cd21e07d072129e9f31cae022c1681685a1541c4cf13496dde10f7300a094a6d410836a81106125fd405cbc147058fd73f04dea55f04d2bc49
  | 5, 0 => 0x21e56358218ce75e21813fcc1e18fe4d1dac19601d5993091bac50e01a3a21ba18242fd117360e58169529fa1653d66c156a0b1f15570e0914fe3dd714c5fb361495ea21143b03b9135768c2133df03812efcbd71280e809126fff4c1251ccbc12297d311211aa3111aa9e71114fce0c112d9c6c103434be0dffbf820cbeb5ac0bf8df8d0afbb7420ad205690ab93c020a8fbfde0a1e048409a5915a0956336f08325dec080ff47d07eb6e43075cb82506fa4a3206fa2f6506d016b306aa51230660f867063c23d304d33b8704d09f6503e8731903a2c054032d177202afa47002a23b730244eba00180ea5101785d350121137c00e06cdf00dfe1f90068e3f0
  | 5, 1 => 0x675a114664adb8aa60af956a5f01c1c15ee1c5a75dcf42275989f6925871d44e57cc11fb57c8fb505788450f56a6fd5351d1d2954eb7448b4e6b9b0d4e26b9b74b7209a94a2a375649bbfcf64944662a479e587246d0beac444565ad422d017a41a197fd4008bea93f95fab93e30959e3d9987653d9419de3be26ac33ab727d73aa565e83a8cdbf23a6af2083a113c6839bdd10b380e2dab37c55aeb3549a38d350c4104330408f432ba6ebe32042f7630dbf5832f1210452ef233822ea1fcdc2d140d3d2bd177e02abae92f291274ee2901a36f282c4e16281a6a432607d64325d8613a252800c2251d985825015809241eab4223ee00192289663521ee920b
  | 5, 2 => 0xe0118264be306bb3b12aab189d6e98e59531b4d091e5380c90393f17901dfbd38e98fe81838c0b9e781914dc7782db55766bbd5f6e203e3b6a31021d680858ac67704f3d
  | 6, 0 => 0x10eacc26107fcacf1078127f106ef598101ddafe1004efa20fe0ec5e0fdfcf7d0f8898390f6217b30f47c4600f1fea6e0ef737100edffd230eaffc3a0e6d238f0e44a8da0ce59a120cd4b54f0cabde0a0c7bcab90c70ad7a0c64c7b30c61e8210c0930a10ba1262a0a3d884a09ce0e40099de7ef099089cb09695d4009607ef40954f70e092a933f091999780901e5b308d01fc908645660085765f207e14e4d07cc8029075ae4430732583706f72c6106d54d9306c75a4706a6c1b20680ba44067d884b0489886d03f8e99a03c4e71303939ebd0389d21f037319a0035313420332635f02c7a62002c70bb80286553e01c45ed6019c9fad00499bad003e83f9
  | 6, 1 => 0x22d25b5c22ce17c7226d1f4f226c911121a5c3f121997fae212c87fc21112e3520facdaf20eebdc420b6484d1ff15d981f87b1c01f2183b71f12c23c1effafed1eb6c6781e7f351d1e7a56a21e50103c1e4aed731e07e5491deba4ac1deb26041d7945dc1d0c1c131cce2f151c96ea491b9c44331b8557b31b6f0bf11b55df541b3c1cc21b27d2611a2594481a0e68fd19ba301a19a0f17618af851c17b13c94172c136016c68eac16b01e5415ea9fee15da08fc15aab6251517feab1461a257140b2e6e13f0814f13ee26c413cc3d601354ccae1351e37612a294ae12a023a411eac26e11df47d111bd8f3811bcb75211af78a8118c0c2c1145229c112a2399
  | 6, 2 => 0x3c7acf473b9743c83ae826bb39d3956d389a48a7385c254e37fdfb7837cf3b4d3748575a3597402034ff522234e85a3334cde67634c3e57634781e8033d662733398d18532eb626b32b9632332aa2b2b31a2e6e73186b60930b888bd306876802fab84b42ea523322e44164f2e2327552e1b49d22cadc4612c7dc05e2c3593cc2b812cf62b6d71132b4013f32b29f3792ad14a022aad75692aa964312a91b15229e53c8529b2af1b28ee2b4128c93b9c28c08b7228a472c7285f16652842fbd32802e9c927560b982750b4f62727c9a626a8a4502611711225fb323b259a31372568133f24ef32072400515d23f91d5823bb3be323a34d132393576123876383
  | 6, 3 => 0x795acc8c7915ad7b78d1319676d6e321759d11627150e8666f370f4d6ecddf7f6e14cd2f6cfb7a1c6c4e05d26b585d106a610cd966e762fa66168b326264afc161a8fd496169ffad6155056160205a025fdd5a815f69545a5efaed315eee6ac05eadb47f5e42f7405cbb87cc5c929b395b5dd2095aaffdcf5a9bc22259e15071599d3738597e76b45925466958d0b50157ff050756b1dcbc56488c3a56286fe352ee940e52c16aed52a599fd4d84259f4c0fdeae4b12b1194abd1d0b4a4ec2a84901a2e248d4885848040ac6478778614758974645a7f59843b8c62c41f0f93141405ed84123c05f3ff1e5963fe058bc3e1ce6143d8f565c3d36a95e3cba3bb2
  | 6, 4 => 0xe3cc7821cc452051c71b0c31c0e08b57be269a7bba6c51c3ae11518cad5ae4eca56b8c1ea53d5025a23cfc39a21df06a9ec0d7899b0ef3d8997632ef996ff0bf96a2e0f99533359e93d8715792e04bde913e377d89cd0684876bd56a82673617825d4aed81b76e8e81b726b37f0941107aaaaa1d
  | 7, 0 => 0x24cb7b292438a25923ba1ce723a7fde623038dd422c1b3a322543c1c21a5f96820e970f520df43cc2064873a20335c0420292edb1ca0b1831c53b96d1c1ffead1b70b1901b2d157f1a2bfa9c19d9673c1900f429181aa941174ef90f170db67f1623f29c15c00f471561a43a123247971134c93410d1aa961004221f0faa77070f8898390e7ddf9c0e7dd0190e7646e90e57c7a70de2aecb0d61f2fb0cb3009d0cae59940cabde0a0c867e660beadde70bd753a90b4bf49b0b41c7720a029d7e09ee1b6f088faf9b0864c5e506d43a8406cd9ad405caca6d05ad2f3403f1b95203e3645403bd1a64023f103c023c952e0198251c01013f360064991500273479
  | 7, 1 => 0x6284e0435fbac6fd5e191a245d9647d45d6275f45cde0cce5c9c0baa5ba915895b2acd5959d66aa0567ee6cd556f5cae53b7a8b552e996fb52942b7251efbb6050ec62bd4ec05ebd4bb8974e4b0c2c3948f889f848e9602744cd758b43a9f848430fb55f4305883643008b8e4214fad14211f6603f8b9abe3eaa21d63c39fd5e3c38e0113c21f90f3a8b1a653a861c993899ed18375fd1e836c744ae36b6da9235f0ac8c342cdee9326a06213264f194317141fd315024ba3122199e302ca7772fc976f62f790d942b81626d2b698d6c2a6cf0712a5175e429c478db2964176b28c04ce028a4a83e2775450f26bb2fef263aafdf261c309d25d7fbe1259eb530
  | 7, 2 => 0xf30eb1d1ef4adc1ae1283faad7c2c847c8d8951dc23de552b55b444cb22e7c90aee65ee3abc89b7ba8d9852aa8d69abba6910249a3f2435d996c23f4992721c2955a0898933451c19074f28c8efed2b28e7679718b44c8168a8c1df38a81f0ca872610b88708035283f048fb8241b0597a2bf43676eecc3f745a681c6e834bca6ddedbb86dcfb1e76cd622c66c4b6e046a7ff66869d0a4b069c0add468ff5c7d
  | 8, 0 => 0x9b34b1217f4590c9764e5f6170658ac8705b5d9f5fbac6fd5cde0cce5059633d42b779a33e277fff1e7359ed1729918f1606144c1561a43a15527a691142fa410e7e1513
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33003333333333000f000f0f0f0f0f0000ffff0000ffff0000aaaa0000aaaa000033330000333300000000ffffffff00000000aaaaaaaa0000000033333333
  | 0, 1 => 0xf000f000f000f000a0a0a0a0a0a0a0a05050f0f05050f0f050505050f0f0f0f03033333030333330303030303030303020202020202020200ff00ff00ff00ff
  | 0, 2 => 0xf0f0f0f3f3f3f3f0f0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f000000000f0f0c0c0f0f0c0c0f0f00000f0f00000f0c0f0c0f0c0f0c
  | 0, 3 => 0x555555555555ffff5555555555555555333333333333333333333333111111111313131313131313113311331133113311111111333333330f0f3f3f0f0f3f3f
  | 0, 4 => 0x77777777555555555f5f5f5f5f5f5f5f575757575757575755775577557755775555ffff5555ffff555577775555777755555555ffffffff555555555f5f5f5f
  | 0, 5 => 0xa0a0a0a0a0a00000a0a0a0a080808080a0a08080a0a08080a0a00000a0a00000a080a080a080a080a000a000a000a0008a8a8a8a8a8a8a8a88aa88aa88aa88aa
  | 0, 6 => 0xaa88aa88aa88aa88aa88aa8888888888aa88aa8800000000aa00aa00aa00aa00aa00a000aa00a000a8a8a8a8a8a8a8a8a8a88888a8a88888a0a0a0a0a0a0a0a0
  | 0, 7 => 0xaaa0aaa0aa80aa80aaa0aaa0aa00aa00aaa0aaa0a0a0a0a0aaa0aaa088808880aaa0aaa000000000aaa0aa00aaa0aa00aaa0a0a0aaa0a0a0aaa0a000aaa0a000
  | 0, 8 => 0xaaaa8888aaaa8888aaaa888888888888aaaa888800000000aaaa0000aaaa0000aaa8aaa8aaa8aaa8aaa8aaa8a8a8a8a8aaa8a8a8aaa8a8a8aaa0aaa0aaa0aaa0
  | 0, 9 => 0xaaaaaaaa00000000aaaaaa00aaaaaa00aaaaa8a8aaaaa8a8aaaaa8a888888888aaaaa0a0aaaaa0a0aaaaa0a0aaaa0000aaaaa0a000000000aaaaa000aaaaa000
  | 0, 10 => 0xafafafaf0f0f0f0faf0faf0faf0faf0faaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaa8a8a8a8aaaaaaaaa000a000aaaaaaaa88888888
  | 0, 11 => 0xdfdfdfdfdfdfdfdfcfcfcfcfcfcfcfcfcececececececececcffccffccffccffcceecceecceecceeccccffffccccffffccccccccffffffffcccccccccccccccc
  | 0, 12 => 0xecececececececececececececccecccececececccccccccececccccececcccceccceccceccceccce0e0e0e0c0c0c0c0e0e0c0c0e0e0c0c0e0c0e0c0e0c0e0c0
  | 0, 13 => 0xeeeeeeeecccccccceeeeeecceeeeeecceeeeeccceeeeeccceeeee0e0ccccc0c0eeeecccceeeecccceeeecccc00000000eecceecceecceeccee00cc00ee00cc00
  | 0, 14 => 0xf0f0c0c0f0f0c0c0f0f0a0a0f0f00000f0f00000f0f00000f0c0f0c0f0c0f0c0f0c0c0c0f0c0c0c0f000f000f000f000eeeeeeeeeeeecccceeeeeeeeecececec
  | 0, 15 => 0xfa00fa00f000f000fa00f000fa00f000f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0c0c0c0c0f0f0f0f000000000f0f0f000f0f0f000
  | 1, 0 => 0xfaf0faf0aa00aa00faf0faf000000000faf0c8c0faf0c8c0faf0aa00faf0aa00faf00000faf00000faeafaeaf0c0f0c0faaafaaaf888f888fa00fa00f800f800
  | 1, 1 => 0xfafac8c8f0f0c0c0fafac0c0fafac0c0fafaaaaaf0f00000fafa0000f0f00000faf8faf8faf8faf8faf0faf0faf0faf0faf0faf0faf0aa00faf0faf0eac0eac0
  | 1, 2 => 0xfafafafaf0f0f0f0fafafafaf000f000fafafaf0fafafaf0fafafaaaf0f0f000fafaf8f8fafaf8f8fafaf0f0fafaf0f0fafaf0f0faaaf000fafaf0f0aaaa0000
  | 1, 3 => 0xfcfcfcfcfcccfcccfcfcfcfcccccccccfcfcfcfc00000000fcfcfc00fcfcfc00fcfcccccfcfcccccfcfc0000fcfc0000fcccfcccfcccfcccfafafafaf8f8f8f8
  | 1, 4 => 0xff000000ff000000fefefefefcfcfcfcfefcfefcfefcfefcfefcfefceecceeccfeccfcccfeccfcccfe00fe00fc00fc00fcfcfcfcfcfcfcfcfcfcfcfcfcfc0000
  | 1, 5 => 0xff00ff00ff00ff00ff00ff00fc00fc00ff00ff00f000f000ff00ff00cc00cc00ff00ff0000000000ff00f000ff00f000ff00f000f000f000ff00cc00ff00cc00
  | 1, 6 => 0xffcc0000ffcc0000ffaaff00aaaa0000ffa0ffa0ffa0ffa0ffa0ffa0ff80ff80ffa0a0a0ffa0a0a0ffa00000ffa00000ff0fff0fff0fff0fff0f0f0fff0f0f0f
  | 1, 7 => 0xfff00000fff00000fff00000f0f00000ffccffccffccffccffccffccfcccfcccffccffccccccccccffccfcccffccfcccffccf0c0ffccf0c0ffccccccffcccccc
  | 1, 8 => 0xfff0ff00fff0ff00fff0f0f0fff0f0f0fff0f0f0ff000000fff0f0f0ccc0c0c0fff0f0f000000000fff0f000fff0f000fff0ccc0fff0ccc0fff0ccc0f0f0c0c0
  | 1, 9 => 0xfff0fff0fff0ff00fff0fff0ffc0ffc0fff0fff0ff00ff00fff0fff0f0f0f0f0fff0fff0f000f000fff0fff0ccc0ccc0fff0fff000000000fff0ffc0fff0ffc0
  | 1, 10 => 0xfffcfffcfcfcfcfcfffcfffcfc00fc00fffcfffcf0f0f0f0fffcfffcccccccccfffcfcccfffcfcccfffcccccfffcccccfffc0000fffc0000fff0fff0fff0fff0
  | 1, 11 => 0xffffa0a000000000ffff0f0fffff0f0fffff0000ffff0000ffff0000f0f00000ffff0000a0a00000ffff000000000000fffcfffcfffcfffcfffcfffcffccffcc
  | 1, 12 => 0xffffcccc00000000ffffc0c0f0f0c0c0ffffaaaaffff0000ffffaa00ffffaa00ffffaa00aa00aa00ffffa0a0ffff0000ffffa0a0a0a0a0a0ffffa0a0a0a00000
  | 1, 13 => 0xfffff0f000000000fffff0c0fffff0c0fffff000fffff000fffff000f000f000ffffccccffffccccffffccccff00cc00ffffccccf0f0c0c0ffffcccccccccccc
  | 1, 14 => 0xfffff0f0ffffc0c0fffff0f0ffff0000fffff0f0ff00f000fffff0f0fcfcf0f0fffff0f0f0f0f0f0fffff0f0f0f00000fffff0f0f000f000fffff0f0ccccc0c0
  | 1, 15 => 0xfffffcfcfffffcfcfffffcfcffffccccfffffcfcffff0000fffffcfcfcfcfcfcfffffcfcccccccccfffffc00fffffc00fffff0f0fffff0f0fffff0f0fffff000
  | 2, 0 => 0xffffffffaa88aa88ffffffffaa00aa00ffffffffa0a0a0a0ffffffffa000a000ffffffff00000000ffffff00ffffff00ffffff00f0f0f000ffffff00cccccc00
  | 2, 1 => 0xfffffffff0f0c0c0fffffffff0f00000fffffffff0c0f0c0fffffffff000f000ffffffffeeeeccccffffffffe0c0e0c0ffffffffccccccccffffffffaaaa8888
  | 2, 2 => 0xffffffffffff0000ffffffffff00ff00fffffffffcfcfcfcfffffffffcccfcccfffffffffc00fc00fffffffff0f0f0f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x63250b0554621e0b0554
  | 4, 0, 0 => 0x569f4b055252c09707d379555a8af3e9acaaadb579f4ca5556e9f4b0501d2bad967d2c1555f0cb3e960aab14601f4b0555702bcfa582aab75ac7d2c1555ecbc3e960aaaeb661ecb0555822c8fa582aabc9527d2c1555567d2c14c8eaf8661ecb0555
  | 4, 0, 1 => 0x611f4b05527ac0d5e933391d58c782c1549eb036eaf51667581b751469192c0d5e61220c9607023e96082b03699f4b05557eabcfa58292bf55c7d2c1555b8873e960aab03579acc23256eaacfa662aabc18e7d2c155606dd4598caab033e960aa385
  | 4, 0, 2 => 0x81abcc25826ac0d5e773391d58cc33c160aaada449f4b0555
  | 5, 0, 0 => 0x72b74fe7d2c155a06fa6c9f4b055681b755e7d3391d9ba803e960aa506649f4e4582a911a06af3e990aa47681abd0a7d2c155a06af3e9b4b055664abcfa582a91da06af509f4d63264320cfa582a8d194e7d3c160aa4f685abcfa6a2c155a12dd3e960aa3f6652bcfa582a911a06eb439f4b0556
  | 5, 0, 1 => 0x75aacfa7b2c155a06e6579f4b055684b74fa582a8f99f0ab3e9ecb055681b74fa58258dd9eadd559f4b055681b75426930155a20dd551e4b0556003755e7d339415baa23e9bcb055681b75487d2c155a12dd441f4b055681b755e922c0c9a12f9639f4b055687374fa582a8dd9e6af3e9f0b0556
  | 5, 0, 2 => 0x6eb115e7d2c1559f6af3e960aa4466eb24fa692c1559baaf411f4b055681b755e7d33155a06f93a960aa37681b75aa742c155a28ab3e960aa4766eaecfa582a94d9baaf4e9f4b052681b755e7d2c1099baae4e9f4b05568a375ae7d2c1559baaf3e9b0b055681b40fa582a9219f2af469f4b0556
  | 5, 0, 3 => 0x79bc95e7d2c1559baaf4b1f4b055684b755e7a33955a06dd52980b0556883d8fa582a8d1a2af33e960aa346782bcfa582a911a06f957984b055681bf9b07d2c155a12dd579f4ce5068a3317c7d2c15595e8c3e9bcb05567babcfa582a941a06dd4f1f4d255675abcfa582a94597a8c3e960aa4f6
  | 5, 0, 4 => 0x81c08fa582a8e5a06c6579f0b05566eabcfa582a89d9baaf3e960aa4c657a3cfa582a93d9bacd3e960aa506884094e792c155a06dd579f4de3266eabd027d2c1559beaf3e960aa2c66e2f4fa792c155a1edd641f4b0556883b55e792c155a28eb661f4b05566d2bcfa582a8bd801036e9f4d2325
  | 5, 0, 5 => 0x3d95a7d2c1555babc3e9e4b055681a30fe7d2c155a06e7641f4b055681abcfa6b220c9a06c13e9c8b055681b755e8b2c0c1a06dd3e9a4b04368a2ecfa582a911a20dd3c9a4b055684aa8fa582a911a06a73e9b8b055681b195e772c155a06dd5ea2cb030686bb97a7d2c1559ba7d2c15492336
  | 5, 0, 6 => 0x81b7514602c155a12d039160aa4466ead0fa582a941a06af499608e30681abd26582a8b5a06eb421f4b055681abd4292359559baaf4c1e4b05566eae8fa582a93d9baaf3e960aa3c681b7514782c155a06dd57a84c25566eabd2e762c155a06dd579dcce55677abd367d2c155a14dd3e9a4b0556
  | 5, 0, 7 => 0x78b755e7d2c1559baab4f9f4b05566eabcfa67280c1a2aaf3e960aa46681c09667d2c155800f2579f4b055581b7514581a0c9a06a74e1f4b05566eabd2e7a2c1559bac73e9bcb05565fabcfa6f2c155a12ce3e960aa4466eaecfa7b2c155a06ed3e960aa40683b74fa582a8d5800f3579f0b0555
  | 5, 0, 8 => 0x8abb15e7d2c155a06dd459d0b055681abd1c7d2c155a12a73e960aa4e68129cfa6f2c1559e4af3e9f0b055682b755e7d32955a06af489f4b055682b895e7d2c1559baaf3e960aa1c681ba1ba7d349559d6c73e960aa4f681b7542602a8d1a06af3b9608e30681a8cfa582a9119bacc3e960aa536
  | 5, 0, 9 => 0x206dd3e960a8376
  | 6, 0, 0 => 0x81b74fa7b2c15468f0681b74fa692c155e06dd579f4b05505bc0decaf3e960aa3070040dd6582a85410d036eabcfa582a81de06dd63a84fa582abc0d247e3e960aa44781afd5ea13e960aaf037cabd42752c155dbaaf3e960aa401db80206bf3e9c8b055677b75a0af3e960aaf037caf55e752c155e06af50a48b055223c0dbaaf459f4b0557
  | 6, 0, 1 => 0x6eabcfa762c1549ef0375abcfa582a849c01032c1542a0802b44206eb3e960aa347823755e7d2c15460e0081abcaa440e855a0cdd6d1f4b0551a3b755e7d2c154a005781bb97a7d3a160aaf1481b74fa692c155dbad0579f4de582ab80218dd5e9f4b0556002f4fa582a81404c006e9f4b0551a001801036e9f4b0550d340e04da3e960aa347
  | 6, 0, 2 => 0x84b91ba7d2c15468f036eaacfa582a939e06dd681c8b05502b801baaf2c1542a02681b755e7d2c15444e008a375987d2c155800eb57960aa4f0ab00206d2579f4b055684c0ddaaf3e960aaf126eabd327d2c155e06dd579f4c4582abc0dd6c1579f4b05578a3adceaf3e960aaeef6eaf55e7d2c155e06dd579f4e2582abc0d5e7d3d160aa447
  | 6, 0, 3 => 0x81b74fa582b15468f03772bcfa742c155c01036e970b0550ab40dbaaf3e960600e78840dba7d2c1546ef0981c094e7d2c155c01036eaa8fa550eb40dbab73e960aa377002bcfa582a81404d03662bcfa582a911dbaaf561f4f4582abc0dbaa13e9a4aa34781b74fa722c1546ee006eabcb055280558010d6eaf4fa582ab40dbabd3e99caa307
  | 6, 0, 4 => 0x81be55e9b3e960aaf036e9f4d2582a869e1103579f4b05523bc0e04e8579f4b05570040cfa5c2c1540ad037cabcfa6b2c155e06dd5e9f4b05515bb95baaf4b9f4b0557002bcb055278540ac0081b74fa582a891a06af499f4b05523b8015e7d2c154a005681b756a7d2c15454f096e9f4ea582a8d1c0109579f4b05502300206eb681c8b0556
  | 6, 0, 5 => 0x40dbcaf2c15422c0081c094e582a855a06dd579dcb055183b757aa73e960aa4f70040dba550e85410d106eaf4fa792c155dbac9579f4ea582abc0dbabd3e960aa0e70040ddaaf2c1542acf9579f4ea582a93dc0103681c8b05502b001bac9579f4b01e681bad5e923e960aaf096e9f4b0551a055e2b036eb40e4582abc0dba7d39160aa407
  | 6, 0, 6 => 0x81be55e752c15460e0081abcfa582a921800eb579f4b05510b001b4af3e9f0b055681bcdd6af3e960aaf036eaf4fa582a92de06dd3e9d0b0551a3c2604dd559f4b0557002bd187d2c1549ed037b2bcfa582a8d1dbac9579f4b0550ab802067d2a874100566eabd4e7d37960aaf037caf4fa582a911e06eb57a5cfa582abc0dbaaf3e960aa2b7
  | 6, 0, 7 => 0x863755e7d2c1540ae0081af4fa580f015801093e960aa44043002067d2c1541003681b755a7d2c1540af036eabd407d2c155e06dd579f4b050183c0dbabd3e960aa2670040d5e582a88c2ad036eabcfa5d2c155e06dd57a40fa582ab80206dd5e9603c15681b755e7d2c15428f035fabcfa582a8c1e06dd3e9a4b05502bb755e7d2c154a02e7
  | 6, 0, 8 => 0x439f2af3e960aad1581b74fa692c155c01036eb40e4550eb00218eb579f4b055681b755e7d39960aae0081b74d2582a8558010375ab4fa582ab00228dd559f4b01e6002bcfa55278740ad036ea78fa582a8d1c00af3e960aa2102b40dd6af3e960aa22781b755e7d2c15420f1581abd247d2c155e06dd529f4b0551a3c25ba8a3e960aa347
  | 6, 0, 9 => 0x40d5a7d2c1540ac006e9f4b05504005a06f6579f4e4582abc0dbaab3e960aa3776eb695e7d3d160aaf036eabcfa582a8f5c010376abcfa550eb00206af481f4b055681b74fa792c1546eeeb579f4ee582a93dc01033e9a4b05502b40df8dd579f4b055784bd1baaf3e960aae0081b755a582a855a28dd559f4ea582abc0e02dd579f4b0557
  | 6, 0, 10 => 0x89b755e9d3e960aaf036eabcfa582a835e06dd579f4b0550fbc0d5e7d3b960aa47781bad5e772c15460e0081b74fa581a0c9a06dd3e9a4c0582abb755e8a431f4b055781abcfa7235960aae0081c094e7d2a875a12dd579f4f0582abc45baaf509f4b055784abcfa792c15488e00862bcfa582a815a28dd559f4b0550abc0da2af509f4b0557
  | 6, 0, 11 => 0x883755e792c1542af036eb3cfa7c2c155e2ada682bcfa582ab801baaf3e964b01e681b755e7d2c1546cf106eabcf2752c155e06f9579d4b0551a3c0d5e7d359a0b055781b755ea13e9acaae00883755e792c079801156d1f4b0551a340dbaaf3e960ae55781abcfa582a91c8af03592bcfa582a8c1c0103579f4aa230eb40dc6dd579f4b0557
  | 6, 0, 12 => 0x81b755e9f3e960aaf036eb34fa582a855e21036eb1cfa582ab802067d2d160aa3468840df2af3a960aae0081abcb01e0a815a1302579f4b05522380206dd669f4b01e681b695e7d3c160aae0081abd427d359559dedd579f4b0551a3c0dba7d2c154680a70040e04b83e960aad038129d427d2c155c007d2c15468050133755ea73e960aa507
  | 6, 0, 13 => 0x40dba7d2c15450d038129cfa582a8c1c0103579f43c1d02b00206af2c1542a0466eabd4c7d37960aaf03579f4f6582a911c01036eabc3c1d0ab425ba7d2c154680576eaf56e7d2c1549ef036eb155e7d2c155e06dd589f4b05507b801ba7d2c07810026003bd5e7d2c15488d096eabcfa582a85de06dd579f4b0550d3c0dba7d2f160aa347
  | 6, 0, 14 => 0x81b74fa582a8dc2af036eabcfa582a859dbac661abcfa582abc0dbaaf3e97cb05576eae15e7d2c1549ef1481b758c7d2c155c0103579f4b01e01b001bac73e960aa4f6002fd5e7d2c1549ec007cabcea582a93da06dd579f4b055103c0dbaaf3e960aa06785c0d5e7d35960aaf036ea1cfa582a8d1e06dd57a84fa5826bc0d6caf3e960aa447
  | 6, 0, 15 => 0x81b755e7d2c1545ef156d2bcfa582a8d1e06dd579f4b05504b80228ab3e960aa05681b755e7d2c0d064e008a3ad567d2c1559baaf3e960aa4f063c25baaf4c1f4b055781b75427d2c0d064f146eaacfa582a815c0103579f4aa1d02340d5e923e9acb055781b755e7d2c15430edd579f4b05527865c01036eae4fa582ab40df2af559d4b0557
  | 6, 1, 0 => 0x81b85baaf3e960aaf036eabcfa702c155c01036e9f4b6582ab40dd4dd579f4b055781b74fa602c15468f09803755e7d2c155e06dd57a54fa582ab80212dd579f4ce55681b7560af3e960aaf096eabcfa582a939e06dd57a8524582abc0d5e7d35960aa15781b755e7d2c15452f0374b755e7d2c155c01036e9f4b037183425bac6579f4b0557
  | 6, 1, 1 => 0x40dbaaf3e960aa25781badbaaf3e99caaf036eabd4c7d2c155e06dd579f4b0550dbc0dbaaf3e960aa31781b757a7d2c0dc60f036eabd427d2f155c010357960aa1501b001b4af3e960aa546813755e7d2c154a0f036e9f4b0551b891e06dd579f4ca55183800fa582a8200a026
  | 7, 0, 0 => 0x45206dd579f4b01e70040dbabd3e9d4b055700001baaf3e9549e1d60000206af3e960aa2360040de6dd579f4b05570000206dd5e9f4b01e6003755e7d2c1540a0270040dbaaf4b9f4b055781bfdbaaf509f4b055800425baaf3e960aa50784c0e04dd579f4b055881b755e7d2c1541002881b755e7d2c1542a028000020702539f4b05568840dbaaf509f4b0558003adbaaf3e960aa027
  | 7, 0, 1 => 0x15e7d2c1540a0260000206dd569f4b05560040dbaa13e960aa0870040dbabd3e960aa4f700375a0af3e960aa4f70040dd6af541f4b05570040e04dd57960aa1578a40dbaaf3e9d4b05580040dbabd3e960aa15700001baaf2c1542a0260040dbaaf559f4aa1d70000206dd3e9a4b05568840dbaaf539f4b05580040dba7d3c960aa3470040dbaaf3e9e4aa1d700001d6af3e960aa026
  | 7, 0, 2 => 0x81b755eab509f4b055881b755e7d39160aa30881b755ea13e9e4b05580000206af3e968b055681b757aaf3e9e4b055881be5baaf3e960aa348003755ea13e960aa4f781b756aaf3e960aa308003757aaf3e960aa4f70040dbada5e9f4b05570040dbaaf3e960aa1570040dbaaf3e960aa0a781b75a0af3e9e4b05588a40dbaaf3e960aa1580040dbaaf3e9bcb05570000218dd579f4b0556
  | 7, 0, 3 => 0x81badbaaf3e960aa4f80040df2af3e960aa4470040d5e7d35960aa44781badbaaf3e960aa08881badbaaf3e960aa158003755ea73e960aa4f700441baaf3e9e4b05570040dbaaf3e9603c0570040e04dd3e960aa3470040e04dd579f4aa1d70040dbaaf3e960aa0e700001ba7d2c1546802600001baaf3e9543a0260040dbaaf3e978b05578840dbaaf3e960aa3080040dd6dd579f4b01e7
  | 7, 0, 4 => 0x81c09baaf509f4b05580000212dd57960aa1560000206af3e9603c0560040dbaaf3a960aa1570040dba7d2c1546008781b755e7d2c1549e0580040dbaaf3e960aa2670040dbab157960aa1570040dd6af3e9d4b05570000206dd579603c1568840df2dd579f4b05580040dbaaf3e960aa4b70040dbabd3e960aa02700375a0af3e960aa02700395baaf3e960aa4f781b755ea73e9e4b0558
  | 7, 0, 5 => 0x40dbabb579f4b05570000206dd579f43c1d60040dbaaf2c1542a0e7003755ea73e960aa0270040dbada57960aa15781b755eab3e960aa3080040dbaaf2f160aa15781b755e7d39160aa4480040dd6da579f4b05570040d5e7d2c1549e05781b755e7d2c154602a80040d5e7d2c1542a0578ac0dbaaf3e960aa0880040dbaaf2c1549e1570040dbaaf3e960aa5070040dbaaf2c1542a087
  | 7, 0, 6 => 0x40dba8a3e960aa34781b755ea13e960aa0a881c09baaf3e960aa3080040dbaaf509f4b01e781b75a0af3e960aa15800425bad0579f4b05570040dbaaf3e9549e1d70040dbaaf3e9543a0870040dba7d2c154681570040dbaaf3e9543a1570000212dd3e960aa3460040dbad0579f4b01e70045206dd539f4b055781b755e7d2c1542a1380000206af3e960aa04681b755ea14d1f4b0558
  | 7, 0, 7 => 0x81b75a0af3e960aa0280000206af3e960aa05600425baaf3e9e8b055781b755e7d3c9c8b055881b755ea73e960aa1580000206dd57960aa1560040dba7d2c154680270040dbaaf3e9e0b05570045206af3e960aa05781b75b4bd579f4b05580040dbaaf539f4b01e70045606dd5e9f4b055781b755ea13e960aa4f881b755eab3e960aa44881b755ea13e960aa08881b755ea13e960aa158
  | 7, 0, 8 => 0x81b755e7d2c154681580040dbaaf2c1542a13781badbad0579f4b055881b755e7d2c154602680040dbaaf3e9dcb055781b755ea73e960aa0288840e04dd579f4b055881b755e7d2c1546008881b755e7d2c1546015800425baaf3e960aa3070040dba7d3c960aa0870040dbaaf3e960aa3270040dd6dd57960aa1570000220dd579e4b05560040dbaaf3e99cb055781b79baaf3e960aa158
  | 7, 0, 9 => 0x81b755e7d39160aa0280040dbabd3e960aa34781b755ea13e960aa32881badbaaf3e960aa3080040dbaaf4d9f4b05570040dbad0579f4aa1d70040dbaaf50960aa1570040dbaaf3e960aa53781b755e7d39160aa1580000206af3e960aa0360040dbad057960aa1570000206dd3e960aa3760040dbaaf3e9c8b01e700409baaf3e960aa4f70000206dd2c154681560000206dd579543a156
  | 7, 0, 10 => 0x81b755e7d2c1542a0e881b755e7d2f160aa1580040dbaaf3e9603c15781b755ea13e960aa3080040dbaaf3e954601d781b755e7d33960aa3080040dbaaf2c154601578a40dbaaf3e960aa448
  | 8, 0, 0 => 0x81b755ea13e960aaf036eb415e7d2c155c01036e9f4b0551a300206dd579f4aa1d60040d5e7d2c1540ac0081b755e582a855a06eb6eabcfa582ab80206dd579f4b05568a40dbaaf3e960aaf036eb695e7d2c155e06dd579f4b05527bc0dbaaf3e960aa08781b755e7d2c1542ae0084b755e7d2c155a06dd579f4ea582ab80206dd579f4b01e6
  | 8, 0, 1 => 0x40dbaaf3e960aa307
  | 9, 0, 0 => 0x206dd579f4b0556
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 40
  | 4 => 49
  | 5 => 58
  | 6 => 67
  | 7 => 76
  | 8 => 67
  | 9 => 58
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x67019e7cf3f901f0079f3cf07000fff8003fff0000e180003f1000cf980033f90000007ffffff000000070c3f100000067cf3f9
  | 0, 1 => 0x3803e01f00f000070e1870c3013983e79830f073983061f3cf07087cf9870f3f90870e1870c3010070e1870c30107f01f80fc0ff
  | 0, 2 => 0x39f3e7fffffff39f3e79f3ffff39f3e79f3cf0739f3e79f3c00039f3e7800000039f3061f3cc0639f0001f3c0003983e61f30f06
  | 0, 3 => 0xff8f1e78f3fffff8f1e78f3c0ece7cf9e7cf3f9ce7cf9e0c3008ce7cf9e7cf309ce7c19e0cf0f9ce0c1867cf3f939ffff9f3ffff
  | 0, 4 => 0xfffffff8f3c0efffffffffff0ffffffffffff0fffff1ff8ffcffff8ffff8f3fffff8ffff8f3fffff8f1e7ffffffff8f1e7ffff0f
  | 0, 5 => 0x70e1870c301007001800c0f1
  | 0, 6 => 0xe007003000000e000000000000e000000000000e00700300000000070000000000000000f0000000000000000000000000f0
  | 0, 7 => 0xe007003000000e007003000000e000000f00000e000000000000e000000000000e0070030000000007000f00000000700000
  | 0, 8 => 0x7000070c00000700000000000070000000000007000070c0000000e007003f00000e000000f000000007000f00000e007003f0
  | 0, 9 => 0x70e180000000070e0070c300007000070c0f00070000000000007000070c0f0007000070c0000070000000000007000070c000
  | 0, 10 => 0x39f3e79f3cf0739f3e79f3cf070070e1870c3f10070e1870c0000070e187003000070e180000f00070e180000000070e18000000
  | 0, 11 => 0xfffffffffff0f39f3e79f3cf0731f3e79f3cf0737f31f98fccff31f307983ccf7318fff9833fff3183067ffffff3183061830c06
  | 0, 12 => 0x3183061830cf63183061830c063183061830c063183061830c063183061830c06000000000000000000000000000000000000000
  | 0, 13 => 0x31f3e79830c0631f3e61f3cf0631f3061f3cc0631f000183000031f3061f3cc0631f30600000003183e61f30f063003001f00c00
  | 0, 14 => 0xc6000060c0000c6000060c0000c6000060c0000c00c006003000c000006000000c00c00600300031f3e79f3cc0631f3e79830cf6
  | 0, 15 => 0xc00ce06003000c00c006703000c60c1860c30f8c60c1860c0000c60c186003000c60c180000000c60c180000000c60c0060c3000
  | 1, 0 => 0xc60cf80700300c60cf80000000c6000067c0000c600e067c0300c6000067c0000c07ce1e003000c07ce1e003000c00ce06003000
  | 1, 1 => 0xc6700060c0000c6700067cc000c670e1e0c0000c6700060c0000c60cf867c33f8c60cf867c33f8c60cf867c0300c60cf80700300
  | 1, 2 => 0xc67cf9e0c30f8c67cf9e003000c67cf867cf3f8c67ce1e0c3000c67c1867cf0f8c67c1867cf0f8c67c18670f000c67c18070c000
  | 1, 3 => 0xf78f1e7833c06f78f1e1830c06f78f1e0000000f78f0078f3c00f7830678f0c06f7800078f0000f18f067833c06c67cf9e0c30f8
  | 1, 4 => 0xf800007f00000f7fffff8f3cfef78ffe7ff3ffef78ffe1f30f06f18f067f33c06f00fe07803c00f78f1e78f3cfef78f1e78f0000
  | 1, 5 => 0xf80fe07f03f00f80fe07803c00f80fe06003000f80fe01800c00f80fe00000000f80c007f03000f80c006003000f803007f00c00
  | 1, 6 => 0xf980007f30000f87fe0070c000f80fe07f03ff0f80fe07f03f00f800007f000f0f800007f00000f9ffe7ff3ff07f9f3e7ff3cf07
  | 1, 7 => 0xfe00007fc0000fe000060c0000f98fe67f33f06f98fe67833c06f98fe61830c06f98f067f33c06f98c007f33000f983067f30c06
  | 1, 8 => 0xfe0fe07fc3f00fe0c187fc30f8fe0c187f00000fe0c181800000fe0c180000000fe0c007fc3000fe03007fc0c00fe030060c0000
  | 1, 9 => 0xfe0ff87fc3f00fe0ff87f03f00fe0ff87f03f00fe0ff860c30f8fe0ff86003000fe0ff81800c00fe0ff80000000fe0fe07fc3f00
  | 1, 10 => 0xff8ffe78f3cfeff8ffe7803c00ff8ffe60c30f8ff8ffe1830c06ff8f067ff3c06ff83067ff0c06ff80007ff0000fe0ff87fc3ff8
  | 1, 11 => 0xfff0000000000fff3e7fffcf07fff0007ffc000fff00060c0000fff0000000000fff0000000000ff8ffe7ff3ffeff8ffe7f33f06
  | 1, 12 => 0xfff3060000000fff00060c0000fff0e1fffc000fff0e07ffc300fff0e00700300fff0007ffc000fff00000000f0fff0000000000
  | 1, 13 => 0xfffc180000000fffc007fff000fffc007fff000fffc006003000fff3067ffcc06fff3067f00c00fff30660c0000fff3061830c06
  | 1, 14 => 0xfffc187ffc000fffc187ffc000fffc187f03000fffc1878f30f8fffc1860c30f8fffc1860c0000fffc186003000fffc181830000
  | 1, 15 => 0xffff1e7fffcfeffff1e7ffcc06ffff1e7ffc000ffff1e78f3cfeffff1e1830c06ffff007fffc00fffc187fff0f8fffc187fff000
  | 2, 0 => 0xffffff8700300ffffff8700300ffffff80000f0ffffff8000000ffffff8000000ffffe07ffff00ffffe060c3000ffffe01830c00
  | 2, 1 => 0xffffffe0c0000ffffffe0c0000ffffffe003000ffffffe003000ffffff9f3cc06ffffff8000000ffffff9830c06ffffff870c000
  | 2, 2 => 0xfffffffffc000ffffffff03f00fffffff8f3cfefffffff833c06fffffff803c00ffffffe0c30f8
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2200922492e00090028914503000f7f8003fbf00056b80017b300044900012a00000007bfff7f0000002b5d7730000002249260
  | 0, 1 => 0x1841a00d0050018d1a28d14503000122800050300000009145030844c904012a00840800400000084080040000007b01f80fc0df
  | 0, 2 => 0x18d1a2af5d76318d1a28d17f3f18d1a28d1450318d1a28d1400018d1a2840000018d1a28d1450318d0800d1400018d1a28d14503
  | 0, 3 => 0xa50a1450a3f3fa50a1450a280c4a64c926492e04a64c90400080084080040000002200900480c0000000224926018d5eb8d157a3
  | 0, 4 => 0xef6edd54a288cbddbb6ddb6d0fad4a9454a280ca72a1d50ea8cca50f7fd0a3fbfa50e5d50a3aaca50a147bfff7fa50a1459b6d0f
  | 0, 5 => 0x42244922480c04224490000090422000224805042200022480404004402201230400440220122018d1a28d1451312b12b895c5d3
  | 0, 6 => 0x58d5e2af1573358d5e28d1451358d5e284000005845e02f017205844c02f0122052b56bab5d7f352b122ab5c55342244922492f0
  | 0, 7 => 0x5a65e92f017b05a65e92f017a05a65e926492f05a65e90d005905a65e904000805a65e02f497605a64c92f492f05a64c02f49260
  | 0, 8 => 0x5af1a2af5c5535af1a28d145135af1a284000005af0802f5c0405af5ebaf5d7f35af5ebaf5d7f35af5ebaf5d7f35a65e92f497f0
  | 0, 9 => 0x5af5eb84000805af5e02f5d7605af5ebaf5d7f35af5eb8d145935af4c92f5d2f05af4c92f5c0c05af4c904000805af4c02f5d260
  | 0, 10 => 0x5af5eb8d1458358d5e2af157235af5ebaf5d7f35af5ebaf5c0c05af5ebaf017a05af5ebaf5d7f35af5eba6012a05af5eb8d14593
  | 0, 11 => 0xbddbb6ddb6d1fbddbb6ddb6d1fbddbb6ddb6d1fb7bb3fd9feddfb7bb3fd9feddfb59f7fd9b7fbfb59b36fbfff7fb59b36d9b6d1f
  | 0, 12 => 0xf7bf7ffbffffff7bf7ffbb7fbff7bf7fd9b6d9ff7bb36fbfed5ff59f76fbb7f3fe72e5d50a289ce72a1472ea85ce50e5472a3a3c
  | 0, 13 => 0xffffffddb6d9ffffff6fffff7ffffff6fffff7ffffedd5db689cfffbb6fffed5ffffbb68400000fddff6ffb7f3ff84ba07f02d00
  | 0, 14 => 0xe72a1472ea85ce7244972e80c0e7200072e8040e50e5472a3a3ce50a1472a281ce00e407203a20fffffffffeddffffffffffffff
  | 0, 15 => 0xf84fe07603a20f84ec07f03a20e72e5d72ebafce72e5d72e80c0e72e5d7203aa0e72e5d50a289ce72e5d0000080e72e4072eba60
  | 1, 0 => 0xff6ffd2f017a0ff6ffd0400080ff6bb47fead5cff65e07fe9760ff60807fe8040fffffff6a3abcfaffebff17fb3f84fe07f03f20
  | 1, 1 => 0xfffbb6f6ea85cfffa947ffe85cfff5ebf6e80c0fff08076e8040fffffffffffffff6ffd7febffcff6ffd7fe97e0ff6ffd7fa3fbc
  | 1, 2 => 0xfffffff6ebafcfffffff603aa0fffffd7fffffcffffebf6ebae0ffffffffffffffffedd7fffafcfffedd7f5fae0fffedd2f5c0c0
  | 1, 3 => 0xf7bf7ffbb7fbff7bf7fd9b6d9ff7bf7f8000080f7bf607bfff60f7bb36fbfed5ff7b0007bfc040f59f76fbb7f3ffffffffffffff
  | 1, 4 => 0xf840807f00000ffffffffffffffffffffffffffffffffffb7fbffddff6ffb7f3ff84fe07f03f20f7bf7ffbffffff7bf7ffbfc0c0
  | 1, 5 => 0xf84fe07f03f20f84fe07f03f20f84fe07603a20f84fe05d02d00f84fe00400000f84ec07f03a20f84ec07603a20f84ba07f02d00
  | 1, 6 => 0xfdd0807fb4000faffe02f5c040fa6fe97f4bff0fa6fe97f03fb0fa64c97f492f0fa60807f48040f8dfe2ff17f23f8d1a2ff14503
  | 1, 7 => 0xff60807fe8040ff608076e8040fddff6ffb7f3ffddff6ffb7f3ffddff6ddb6d1ffddff6ffb7f3ffdded47fb7a3cfddbb6ffb6d1f
  | 1, 8 => 0xff6fe07febf60ff6edd7febafcff6edd7f00080ff6edd5da289cff6edd0400080ff6ec07feba60ff6bb47fead5cff6bb476ea85c
  | 1, 9 => 0xff6ffd7febfe0ff6ffd7fa3fbcff6ffd7f03fa0ff6ffd76ebafcff6ffd7603aa0ff6ffd5da2d9cff6ffd0400080ff6ff47febf7c
  | 1, 10 => 0xfffffffffffffffffffff03fa0fffffff6ebafcffffffddb6d9ffffff6fffff7ffffbb6fffed5ffff0807ffc040ff6ffd7febffc
  | 1, 11 => 0xfff4c90400080fff1a2fffc543fff0807ffc040fff08076e8040fff0802648040fff0800400000fffffffffffffffffffffb7fbf
  | 1, 12 => 0xfffbb68400000fffa9476ea85cfff5ebfffc0c0fff5e07ffd760fff5e02f01720fff4c97ffc0c0fff4c926492f0fff4c926480c0
  | 1, 13 => 0xfffedd0400080fffed47fffa7cfffec07fffa60fffec07603a20fffbb6fffed5ffffbb6ff02d00fffbb6f6ea85cfffbb6ddb6d1f
  | 1, 14 => 0xfffedd7ffe8dcfffedd7ffc0c0fffedd7f03aa0fffedd7fffafcfffedd76ebafcfffedd76e80c0fffedd7603aa0fffedd5db689c
  | 1, 15 => 0xffffffffffffffffffffffeddffffffffffc0c0fffffffffffffffffffddb6d9fffffe07ffff60fffedd7fffafcfffedd7fffae0
  | 2, 0 => 0xffffffaf157b3ffffffaf017a0ffffffa6492f0ffffffa6012a0ffffff8400080ffffe07ffff60ffffe076eba60ffffe05db6d00
  | 2, 1 => 0xfffffff6ea8dcfffffff6e80c0fffffff6a3abcfffffff603aa0fffffffffeddffffffff6a3abcffffffddb6d9fffffffaf5c5d3
  | 2, 2 => 0xfffffffffc0c0ffffffff03fa0fffffffffffffffffffffb7fbfffffffff03fa0fffffff6ebafc
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 52 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 52 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 278 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 278 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 278 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 278 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 9 0) :: stateWiresD n (ids >>> 9)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 9 0) :: stateWiresS n (ids >>> 9)
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
  | 3 => 4
  | 4 => 31
  | 5 => 380
  | 6 => 915
  | 7 => 364
  | 8 => 8
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0x843ecb3b50d4df36012ad670010ce8e8
  | 4, 0 => 0xd1f78426c8fe8d62ad9fb9eba6b2a73b9b57b5e574a13e7f7245c9866274e8a7591582aa55c5e2c54f906b594e26b9b73faf79973865746432c078173186c0542d6659a029ebca10273e5632270ae1fb23365f242313ae2a22cc93431d02666815eeb18915c3d9d415098be1138911dd0e6fd2900e1b411f01261437
  | 5, 0 => 0xb7002330b27822e0b12a5570b101bce0b0a20b60afa05f60aea8fc60aca710b0a73b8a20a2eb7d50a1aa28209ffa6bd09907306098d4fc7092d46d80922163208a8b3b60863db9b085fc2c507839f18073b498e06d310cf06a11716066a9dd3062efed5062996f705ad592405338f46052cb60404fdb04604c630e504bd21ab049e8978047120420469edb8044f84c20421b6cf03fe0cc003e9563303ce9a7b03ccd4dd03ae9d7b03403ad7031ab4ea0308ef0f02ec2c5402d24c3d02bb4b6e028df3cc0256d610022a5b2001f5615a01e8185d01d155a701a05d36016b6199015437cd01373cfc01013f3600e3021600dca58f006e8d9d000eebc7000c121a
  | 5, 1 => 0x184a715f17b9de5117b72a7917b0da98178b4c4e1770781f176c5124176268d61727410116438d3716075f8215a7c2d515a30bd6158cbdee1525469b14eab55c14de23b614c050cb144fd28c144c565b13b019cc13a75ce41358dcdc12ef4d9312720752126f65b31260ae4e124434211234695d1205e96f112a2afa110cbd8c10f98e6310b7e6da10886e18106bad281056a0981004bc5e0ff0198b0fdc47fe0faa77070f989ed60f49c1030f3563ed0f2fe0b40f2c93650f2959340ee0d70d0eaffc3a0e7ddf9c0e60a3ca0e47c4f90e33c6070db18d640d9e5bf10d97fb330d85391a0d7282800ca8f48b0c61e8210c44ca190c405bc60beadde70bcfb3fa
  | 5, 2 => 0x23faa22723e6bb0b23c1fe3a2363a3bd2312fd3621b063282164c0a6214c00a121436c63210aa26620ffa4f720f52bf020d005fc2075da6420227861201886541febb65d1fb5cfd51f3a85a51f2147301f194ecc1f02a0361f0252a61ecaac371ea26ad91e7f351d1e747f001e739d4c1e5faeb21e4008941e3f0bd31e0daafc1dfda2651db4a4271d7945dc1d73fc671d6cd5d61d4df85b1d2c49ee1d09498c1d0218971cefcbde1ce800591c3bb9b21b7afc541b7069dc1b4dbd411b3de3861b3845571b0b1d041a49f8f61a3fc2e51a0aa15e1a055bd019c7adeb19c345e01956d04519446e25192081a418f325e618a92f1218a25c1c1896ae74188194e6
  | 5, 3 => 0x3e0cb8133d5518c53d0ec8b73c9d75a23c91d8ce3c487d5b3c3614e83acf17f03abe6baa3a67b4373983ee0e38ced83238b831db38b18bf837812f4b374f8ff2372f8b5f36f4c4b635b74057358afd9b357ee788354ee2f734d319313494773a3476123c33e5e4b832e50a8432b59d2032a6fbfe31d591ee317a69f63156fc5330b70034303aa5a32f75386c2f115a972eeb83062edae5ed2ec68a382eb30b6a2e299d9a2df068002c5ac2c52c50cf7a2c3262cf2b71f0412ac1eb922aaf70c82a91b1522a8dfdd22a886da12a237312278bb56827457d312727c9a6262d4ed9260a193325fb323b25a977402576a98825564e78248d4cfb2469ad78240bbb77
  | 5, 4 => 0x5b09819759be1e2e58ee0c77583fc2775602d08b5592d465556f069554f38e565496f450545efe305456a5535330728c5318541d5235d9fb521a4bae51ef299251a441d65198959c50bb5f6550b7ed5550b4b1a64fe19e8b4e774ff24d953dc34d4947874d1acf0f4cf40f144ce957c54cdbf6234b4ec9ae4b435be74b3af1ce4aff4e004acd3e544a99e66e4a969f554a65097749a0b8ec49261eb348ae027248a3dda9477c6595466f99b745a5853f456f4619455eebbd451158054477344c444e1e2943d1a4874386b4eb434ac03243008b8e42b779a341caee744171d35b4170b9d8411c887340499a11401ae3ef3fc4defb3f6fe4b33ed81c443ebcceee
  | 5, 5 => 0xe1c4fe42d89dce04c7a846e1c4070a2dbb1c657cb85d9858ae077dd1a98670d0a84563c7a51d3ba4a4c36fdda2ead7c09e5f0cb99be530079b19c51e9ad2de7799c4506e939a9e61932db84b8efed2b28b24337c8ad0619388dea2ab882be4e18683f3ba831d17ba7fc339537c217196793a6fd8789aaca976a362bc74a13e7f7245c986716d992470d44b9770c6ceb66f0f2f736e85ad376e2636f56dade4d26cfeec096c3d1b7e6bcf90f36b28433d6ac5d57a6a0fa98169d0a4b06991e7686733942566ff6694667feca46619345f66168b3265d47924638397f463669d955eee6ac05eadb47f5e2d907e5cee0527
  | 6, 0 => 0x3dd9ddf03d31bcd03bd1a6403b5fb4003a02aa2036caa6e0341d11b033af53b0332e636030b3eb50308bf7003087e040305cf4302ffb50b02eaaf3d02e9d44b02d4683902c16857029bda2f02898f5e0285a1030266dda8025b539202588a4e024ad8f90248132d0240dc1802300506022c1d3e0225f9ec02075cec01f5db9e01e3cad001e2de1801ca161a01c1f3ad0196da2a018e4817016fd4b30168ae6a015e807f015437cd014f52d80149839e0141e4f4013f5675012a584001195bd501179a04010d9d940103e62400f94cd000d6e3c300c33f3000c03e3b009787b3006eefee006c2684005528aa00430b2a00244f8c001e67b1000db97300003de8
  | 6, 1 => 0x848694b083057d40815b7f9080a8eb707db41c507d4d70907c2594907bae626078f1e5307839f1807805cdf0779ffd40769b997075d24660750d779074e3d6e074ab391073d28ef073b4e520703840006dc984206da899306cd9ad406c4413d06bd2d1e06b1897a06ad0f6306a693b5068d368e068a399a0681af1906691b5e0665520c064bf28e0646fbd306432260063d52240636e8f6062daa77062996f70617f3be05e60e0005ce889805a47d0105687e89056618dd055fb09b05484c49053c7a0b0537bcc1052f642505169eb004f94c7d04f23d8004ead86d04e7479104dea11c04d32ad8049dce2a047222a1046f19ba0454d64a03f1b95203def96a
  | 6, 2 => 0xdb51cee0db432850da962390d9cbe430d9a92370d896bb80d8540fb0d7f4d7e0cfc43180ce138480cd88bf40cc46ad20cae59940c9e5fad0c83298b0c80b0f20c60dcf80c425b440c402ecd0c36bc970bfc119c0beadde70ba77e000b80283d0b608b620b5240800b2972550b28f6400b1a7d630b18fee80b0a20b60afb5dd30ae34fac0aca8e640ac01d010abbeb7f0aa03d900a9628be0a8235f60a7d079a0a70bd460a3325db0a2a32ae0a075bd10a029d7e09fd209709f9c03209bd51ef09a252ac097efcf10938390c092d46d809272dac09142b2408fadadf08f0123c08ef1b3208c00bc908b7fc7e08a530c6088bad52088b78fe086e838908586f94
  | 6, 3 => 0x114bb2f911491d611142fa411120d6461110c79410c88b7f10705cfe1063cc11105e2d1910532c1f104ef361103c0109102d648a102d4a7a1029899f102497a9101f34a21007ae721004221f100074f20fec104b0fda9e160fc153340faa77070f9c258f0f88d0470f8899180f799f850f79216c0f5dcc450f47a0390f3d84400f3876680f1c66040efe832c0eed14a20ee672b50ee271f80ed3e0d70ecb2c040ec726fe0ebe73810ebcf9d50ea51df30e9bae690e8097270e7e15130e7ddf9c0e6ebfe90e66678e0e60a3ca0e5d94ed0e4ffb2c0e3834050e33c6070e2945730e255d760e1213a10dfbaa4f0dfb96ef0df124ef0de1cc4b0dced1f30dce0a03
  | 6, 4 => 0x16e8a4df16bd508a16b4d972169fae74167fda5b164f2637162e4ad2161181741610dca816100cbf1606144c15f0607615e9498b15d3ee2015cb0ab315c392b515bb49d715b8b2ab15b3c68f1561a43a155cba4e155bdbff1555667b15527a69153cd95614f6524714e3911a14de23b614acf726147d342b1476241e1474a73714696ac214649f8f145917c7144884391437977c1421d7bd141eab0313ed66dd13ec8e4a13ea83c213e874e813da313013ba4514139ddcd7139b02df137dbbb1133c08ef133acad513346ed11327faa1125d0b7e1234695d11ec178611dd99c311c7fa7911c6cff81187183a116b4724116a87581166de16115b67ca1150faed
  | 6, 5 => 0x1cdaf3161cd584061ca0b1831c7f55261c5d3d531c51125d1c38bc051c32bad41bf710b81bebd45a1bc5498a1bc1e6a71bbaa2fd1bb1776b1b98b9f91b96d7631b8548e61b7aa30b1b5d8dce1b52bdbb1b37350b1b06d2411af872791a87fcc01a78e0031a624c741a1f1cf019f2db1c19d9673c19d0561919cfb29819c2b1f0199ecf5e197cabad19064dea18ef4baf18daecab18c91a2e18bfbc0618a709f4189d69961876cc481870ade6185955ec18460f4f1839cef01835b7a618178b9318103f8817dadf5b17d98ca617b8d5e517b29b5517b0da9817aa73131772a37a17617b9e175aeeb01753fa8b1729918f172088df1710ef8e170ecd2617098758
  | 6, 6 => 0x241b265d240dfe2e240707cf23f579f923f5635023ba1ce723aa74da23683086236510162359c6d022e55f97225d4df4224b00c921ded61c21bfea642183f1d221778cd421625102211fa54b20f72cf120e249a720bb659020b2182b20a84c142089ff202064873a205b0a2a20335c0420292edb200d023a1ff58b481fec45ad1fe218841fb72b911f8738591f4eac261f47d9851f3387171f1fd9b81f0858b81efda3231ee77a8a1eb295fc1e961c6a1e7359ed1e5a4bef1e4008941e3a97551e2780c41e1d7d5d1e1a72c21e06b5881df06f441ddb52551da019151d8de2ec1d85cfcc1d826c881d825b1b1d729f271d5e20161d481d0c1d267b371d0a8400
  | 6, 7 => 0x2d0e06132d0700722cd2b91a2cc28d5d2caadf282c2fc9bd2c131a362c0ac7822bfc7bed2be8c6dd2bdc0c9c2bd66a662b81626d2b79d3f12b5f449a2b4d72162b3dd2d02b08f8cc2afe09d52af8e8dd2ad9fd9b2ad6ae8e2ad607842a892cd02a5335872a52a34929e9715529e90d4d29c79620291385ac28f2ce8828a4a83e28a20861288e1a33286ecef828580f392842e2622823a05e280a5d7427a6502e2738adc8272ec81d26f6561a26c9f55a26c5c2ee26c0fdea26bb2fef26bad6df263aafdf262a32f42610a0ef25f82efd25f3998825f20eed2572406825471fea2506be5724d3a654249f7e6f248854b5247367df243971d5242bac33241bb9ec
  | 6, 8 => 0x3668643f365a85603610c82c35d89aaa35c589f8353aa3c634ffbf2734ecd7be34d32b6734ad09f134a771a7349260313470a2a9344f615734417d0f34064f6c33d93c6b33a8219a339be83033508cbb32e16b8932c4afd5329cbbfb3294f0e0326bf53f324765313241f60e32054f5f31f21e3331cc3c3831ae084531a1f0bc31752de7316b2b893157e4933147811e313ee4c531381b0731308a083122199e30f9966730f5732730e916da309e976130010ce22fb10f502fae5bcd2f9e20512f790d942f44eb4f2f2d39052eec01822ee8e9622e8fba352e8e6a142e5e9a2c2e2fd76d2df877932de6358a2db09fc22da1453b2d59f75d2d4f458b2d3d61e6
  | 6, 9 => 0x430fb55f42b779a34291ffc9425327d74228e6a741e3469341d71fb14170b9d8413f306a412c1b3840455b7a403615813f7c70ed3f591dff3f227ddf3ee66eca3edf91b23ed6ab913ec840c33eadce583eaa21d63e82daac3e55bbba3e38828e3e277fff3e0e2b9b3e0ad2fb3db6e42c3db233443d820b7b3d7dc3333d727f8e3d23d8903ccb90303c7b854d3c5bae9a3c3225d73b93b1123b72da473b33d6c03a7547493a51e41939fad63539b6fb3b396f572d38eb527838d122c3388982ce388012b13868b8b7386890e8380d7bfe37d8b58137b2c32b379218e3379210d4378f31e837596ec337139a0e36cb597836bdaf0a36b5383e369d2c57366fa272
  | 6, 10 => 0x5021995a50002b294fe19e8b4f8511f34f050fd04eebb8da4e64a4314e12985f4de1baa04dd542384db7b5514d43a2314d36a1764d2f3d364d1acf0f4cdbf6234c4c79c44c1e35cd4c0fb2d04bb8d2fa4b3785644b226b904ad762854a95df414a6c36964a4249ab4a3ff2504a3f5f3c4a25f49949984626498bdef9498a2f5c4926e5e148e193ac48c35a8b4854372b483ef58e47bc775947608682474dee9a46f1b31146dd66d846b9893046b55adf469cb09745b657d145a865c2459ecff7456daacd4554acc544ed2426449a9aa4449785304486b9414485ef87447cb9f843ee98d04361a4a443555fb0434ac032433f660a4335a681432e5dba432891ef
  | 6, 11 => 0x630c3af36260dea362356cc061b46091619bd762615a00e86149f9556066b2c6604acd205fbac6fd5f3a91285f205a9d5ed473b85e6bb93f5e5d99e45e55ee465e374d3e5e191a245dc382f45d8128125d1cf1905d1495be5cde0cce5c9c0baa5bf13ab45ba915895b5d16395b1f7a795afe18b25afb09185ac56e225ab7f2675a9f5dfd5a7dde2d5a6fa4e45a19e2e159a0c2fc58ca2eae586233b257cf343957728a0056d7ea5656b3de6b5652b963564a529555dc8b8955739b7c5565cf7e5557fdbd55076a1754a96c09547e776853ee3c7453ebafa153b7436653860d06533df00e52e8c50e515df7bf50ec62bd50b9a388506fc4c8506c7ad05059633d
  | 6, 12 => 0x7d8399fc7d5aa3917cea112d7b79bbc67a2bf43679dd3b90792b8cc8792208aa783d68e477d1de1e77ab3f8876d69d90765d4b3f764e5f617626fba57447c1c273f090f6739c3b75731a9a37722120737212456371ff99de710370d570658ac8705b5d9f70345b606ed8da0b6e81dc4c6e38b80a6db7d3e86d483b2f6d18b8176d0b6a236cfeec096ce170276c5bdf7d6c4b6e046c0db62e6bcf90f36b0ca3d16a9833f36a41599e6a08bb0569f4783269d00a3469c0add46909685e67c02dcb6761988367339425670aa40466fd841f66eea10d66a873e666596eea663e596f65cf5287658f322f654b5501651c6741640ad29363a6a9d363939f336390794c
  | 6, 13 => 0xbbe3d513baa3d292b99d8907b751909cb6c163afad965e55acc83166abb5d1f0ab559622a94093e3a8d62ca7a8a73885a6910249a65ef21ea3c1ab4ba3bc67f7a32032e7a116b2f8a101f61fa02ef21b9f8d18969f295df39e56566f9cd8b9f79b34b1219a9046349953af4a98386cf697fd332d96fd83539551aacc952f3430939a9e6192d649fa9268f280919ac8ae91592acd9114aeba90c78886900537138f74f0a98efed2b28ebf00228cfa91f68a8c1df38a81f0ca8a7994f889b52b50892e5a31892cfdea88a4fc2188747b6f8710bff086419ece840e75af82de711781fbf38a81a7996e818c305a814662f380c2fc1b804da87b7fb866157f4590c9
  | 6, 14 => 0xfb89f1edf8ff31bdf8d5ce41f6535463f5277aadf12be4b6f052953bedd0785cec17d5dfe22f5cdfe064565cdbf348d3d94898b0d0c08da1d0347204cb2d3d5cc637c9f1c3ad09c1bfd1f35b
  | 7, 0 => 0xea68d810e8414b20e7e15130e783ebe0e589c450dfb96ef0df078900db675560d9a92370d91ebc20cf91d9f0cea20e10c9f2fc30c2cfbb60c22507d0bb2ffb10b989d440afb5dd30acf09dd0ab8b26f0ab0afbb0aa9dacf0a9628be0a71f9560a172c490a075bd1089ab0f308786758086ef30e085bfa8e07af559e079adfc80754ea1506ecbabd06c7654b06b07a0306a150320663442506556796064612c706291d83061ab2860590310f05869eb105169eb0040745c603f3df97036df1500360127103476202033b05b5033a727c02e9d44b02d5abde0291d00a024a740d0233af1501a603fb0196da2a0188fb4b0129b75500dd496a0086a50c00103def
  | 7, 1 => 0x1e739d441e7359ed1e3d0e221e17d8601e08e1531d989e101d89743f1d73f5661c93f14f1bea35011bde45011b78d4bc1b52f3321b325a461ac4a36f1a5d39541a45ab1d19f08aad19e3604919deb3e219b1d4481979f417196672e1191716b7191531f418e3fb0a18787ffd183e830517d7cb9517d07b0017a820261729918f16e8db181606144c15ff8a4715f86a80155596ad15527a691528ba3c14f3797314121a0c13b5da6d136d10ac135211a2131bfefa130748e512e05c4012c58a1612baa67712b8884a129997eb12798028124e263511d7480611b4128d119811441142fa411110c7940ffdfe370fd4c3f50fc22fb60f3d84400efa46790edd1708
  | 7, 2 => 0x3518dab134ceb8d134744a7f346540ce34064f6c33d93c6b33ab0d08339be83032e7627a32c4afd532ba82ac329cbbfb325e4bb731cc3c3831381b0730f26f092fa1c82a2f7655c82efbd9642ee51d392e46479b2daad2e42da80a642d6df75a2d014b912cf3c0ef2cae27f22ca821632baacaed2ba0a43a2ba064522b48380c2a73350a291abe562882e2b22838c79a2774c460275958f22705880d26e36c2426d2458e26aa53c326a4b5bf26488ebe26396ad4262d41fb260932412485a934246ade96231857ea2310763b22f464032219ec0a21a1d2672179389d203e530f2014c6441fd3d3851f3d31db1f1fd9b81ee4e3db1ee472391ebb13731e8eec38
  | 7, 3 => 0x52f2fea452de426a523dc21151e0918f51d2062b515c291951099cc650a706e85059633d5038abd64f943bc44f8511f34f0fba7a4e2ce2974dc27b5b4d17706a4c4c79c44b62f61f4aee73794a6707154a3f78dc4a0d1974499cfa0a499b08ca498bdef94926e5e149226c8f4879fd8347f69d264696c818454d83ff43b9f0a343b425714365b3a943555fb0432891ef42f65e6542b779a341a8390641a4b5d6413f306a40455b7a3ffca0873e277fff3df1aaf13dc32c533d8620523d18fbc93cedcf813c9f3cdf3c9dc2fe3c9d75a23c52b0633c2c26383bf3e2703afd7b253acd3e8239fad63539de879e38b73fba38ad846e387c2216378f31e8359f67e7
  | 7, 4 => 0x8ce77a638c8386ea8a8bfac78a7994f889211e6a877c8a9f850f030e8492c7cd81b633a5804281917f4590c97dfd47397d356db97cea112d7b2b17a17aa157477a2bfc5d7892577577d135d076f0de3376db0b2e764e5f6175a74bbc73f60c3a72e03d9b72b283397263b2ee71fb25a270946692707cee8d70658ac8705b5d9f6d9b14bb6ce170276cbe1d396b89f08a6b1be3666aa2ab606a4fc62d679d352a66fb4c91651506a4647899486379a67663669d9561b4609160c016455f5d13a95eebace45ebcebc25dc82fa15d93d62e5d7bf2db5d2e415c5d23bf8f5d1495be5b4388f859f223e558905d135806ebe256abec62564030685592bd7c54b47b98
  | 7, 5 => 0xf5210d0eee22ff53e8f19d4fe73f702ce606f433e575a6eae2f6cc76dd4db3aad96359b3d7c0c947d56748abcf6e15b1cdd2d617c707ac1ebef4bb49bcf5d0c6b9782853b37ef559b1b17014b0ed6350b0e1dcffb080f6ebae064aa9ace974c5aabfa2cbaa87c3f1a8e78fc4a5103ec2a4a02823a494c22fa36baaf7a275c8f59b71391a9b34b1219aec1f2b981b7e929710a45897012b8492a6c2019117715e8f46f2108ebf00228d92f6958d3d413a
  | 8, 0 => 0x8a7994f87cea112d76f0de334aee737934064f6c2efbd9641b78d4bc05169eb0
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x810148000030405200000410248000010100201
  | 4, 0 => 0x5150c205600c5310c04000010c1030000043040c001040d2000000032440c00001081020014843481000404052000000040440000000c01010000042041000101002010000043040c000010d10641415410c0000000c110000000200404005250c205000d5420808000010d10400000320418005010d2040000000000c00000000060000043441000540c9205000c10148000000109105000410448000000101100
  | 5, 0 => 0x1c00000000030000030041800000000040004020080400000801010000020440000304052000000031440800350852010000042040800000000040000000001c00520c52010011531080000000000050000032441400000c51060000032040800000c510200000000014000008c10600000000018000010010200000424414004350c200000c932080000000000010000030040c00000000040000030041800000c0103
  | 5, 1 => 0x1000000c01070000000001800000c010100000340414000010810400081014800004350c2010014c42480c00001051060000000000400000000030011521080000000000050000000000c00001001070000031440800521052000000032441c00000d110200000000018002040520000114314804000010d1060000040440000000000030011531080400000c01010000000001c0035109205000003004040000000007
  | 5, 2 => 0x4030080400324c82010000030040c00001091050014c21480400000c01060000041440800204052000011521080000214842000000030040c00001001020000031440800000000070000000000400001081020000042440c00251052000000000001c00200402010000040040c000010d1020009414480000500c5201000003004080000000007000000000100035085201000004144180042508201000000244000000100101
  | 5, 3 => 0x30040c00415042010000000000c00415042010000000001400000811000000043440800001051040000041441000000c81020000040040c00100802010000040040c00000c51040000040041c00000c01040000000000800534842000000042441400000c91030000000001400001001050000030041400001051060000030040800000c1100000003144080045484201000000000040025504201000d442481400000c9103
  | 5, 4 => 0x31441000354842010000040041000001081020000041440c00000000000014c42481400001091030000041441000000000010000020440000000000060000043041c00001091030000034041c00104092000000030040400000000070000031441400000000040009431480000324c820000000320408000008c1020000040041c00001051070011421480000000000060000000000c000008c1020000031440c00000c5107
  | 5, 5 => 0x40041c00351052010000041440c00000000020000000000400324c820100000314414000010510500000000018000000000500000414410004504d2000000030040800000c9103000003204080041504201000d441480000001011000000000000c000000000300000000014000008c1020000030440000000c01020000002440000534842000011521080400001011000004030080400314c4200000004044000000000005
  | 5, 6 => 0x30041c00000000060000032441400355082020000020440000314c42000000031441800000000020004103480000000000070000024041000000c01010000000001800000c51050000024041000001001030000040041800000c81020000040040800000000060000034440800000000050000031440800454842010000032440c00000c51020000043440800000c81020000000001c00001091070009441480000000c9103
  | 5, 7 => 0x31440c000000000200000000014000000000000000314410005250c2030000043041400000c91030000030440000001001010000020040400324c8200000d542080800250c52010000030040800000c9107000000000140035504200000003204080000000005000000000140000109105000d521080000001001020000040041000000c9103000d54108040042508200001010148000000105102000852108000000000001
  | 5, 8 => 0x4103480000000000050000041441c00001051030000020440000000000060000032440c00001081020000041441000000c91070000041440c00454c82040000020040400000c01070000030041c000010d1040000030040c00000000010001541080000000000010000040440000000000000000032040800250512000000000000c00000000020000000000000425082000010d43080400000c51070000040440000500c5201
  | 5, 9 => 0xc00100802010011421480400535042000000010440000000c01070000000000000000c01050000041440800000c01040000000000000000d01070000000000000100802010000024041000000000020008010080400000000020000042041000001051050000034440800001081020010d43080400200402010010942080000000000000000032440c00000000040000032040800000000020000032440c000010c103
  | 5, 10 => 0x424414004150420100000300404000010c1050000043441800000801010004030080400000000040000000001000000000070000030040800304052000000000001800000000000000000000000254c42000000043041400000c010700105410800000010910500000000004004350c2000009531080400454c42000000031441400314c42010000000000800000000010000040040c0000100103000d44148040000000002
  | 5, 11 => 0x3004080000000005000003204080000000001000004004040000000003000000000080000000000000000000100000081100000000000140000000000000c932080400504c42000010101480000000000040000000000c0000000000000000000080000081100001010148000000000003001054108000000000000000000000000000000000000004204080000101100
  | 6, 0 => 0x8521080000000c51060000001440000000000010000000000400001001010000003840000001051050000000001400000000070000004840400000111000000040040400001001010000021440400000000030009531080400001091000000000000c0045484200000d421480400000091000000040041c00000000040000031440800314c420100000000008000010510300000300404000000a101000000000080000080101
  | 6, 1 => 0x1840000001051030000040440000000000020000034040c00000c11000000000000c000008010100000414408000010c1030000020040400000000020000020440000000000020000000001000001081010000000000c000010c1000000000000800000000040000041440800450c52000000040040400001001050011531080400000000030000000001c00000000030000040040400000000050000000000c0000000007
  | 6, 2 => 0x10040400000121000000020440000000000070000000001000001011000000012440000000000030000000000800001001060000040041800001001030000000000800001001050000040440000000c5105000d521080000001051040000032040400000000000000040440000001051070000000001800000000020000031441c000000000600000000000000010c103000004004180000041100000004144000000091100
  | 6, 3 => 0x310404000000d1000000000001800000c01010000031440800000111000000000001000000841010000030040400000000050009541080000000c51040000041441400000000010000040040400000000030000003840400000000010000000001400000411000000000001c00001051000000000001000000000050000004840400001001050000030040800000000040000020440000000000030008521080400000c5104
  | 6, 4 => 0xc00001001040000000000800000000000000000001400000000050000000000c000000000600000038400000000000500000414410000000a10100000048404000010010600000414418000000a100000004144100000006101000c932080000000000030000023440000000c010300000320404000004010100000314408000004d1000000000000c00000000050000034040400000c5104000000184000000000004
  | 6, 5 => 0x1c00000411000000040041400000000000000000000800000000030000030040800001001070000000001c00000811000000000000000000091000000001840400000c11000011421480000000c0105000c932080400000000030000020440000001001010000041440800000811000000000000c00001081060000031441c00000c01010000001440000000c41000000000000800000c5102000000000180000000003
  | 6, 6 => 0x404400000000000400000400404000000d1000000000001400000000020000042040400000000060000040440000001041010000000840400000c81020000040040400000000020000000000000000000020000041441c00350852010000000001c00000000050000040041000000d1102000000000180000000003000000000080000100103000c5310804000008d1000000000001c0000000002000000284040000011100
  | 6, 7 => 0x1400000d11060000031040000000000070000000001800000c01070000000000000000811000000041440800001091050000000000c000000000300000000014000000000400000400404000000000700000000000000000e100000004044000000080101000000284000000000000000003444080000000002000000000040000101100000004104040000100103000000000040000105104000000184000000000003
  | 6, 8 => 0x100404000000000400000000018000004d1000000000001400000091000000040041800000061010000031441400000c91010009541080400001051030000000001400001001040000000000800000000050000004840000000811000000004840400000000030000000000800000000010000040041c00000c51060000032040800000000060000000000000000000030000030040400001051020000000000c00000c1100
  | 6, 9 => 0x31441400425082000009441480000000000020000000000c00001051020000042041000001041010000030440000314c42000000002840000000000010000021440400000000020000030041c00001051040000040040800000091000000031040400000061000000000001000000d01030000000000000001011000000000001800000c01020000030040c00000000020000043041c0000000004000000000100000108104
  | 6, 10 => 0x314410000000a1000000004840400000000030000030040c000000000600000200404000000000100000000014000010510500000000014000010c1000000000001400000c91030000000001c00001051050000000001c000008110000000000008000000000300000414408000000000700000000008000010110000000204400000000210000000000010000000000000000204400000000a101000000000100000109100
  | 6, 11 => 0x41440c00000000040000001840400454842010000000000c00000000070000013440000425082000000030040c00000021000000000001000000801010000000000c000000000300000028400000000e1000000000000400000000040000040040400251052010000000000c00000c01010000031441c00000000020000043441000001081040000000000000000000030000003840400000d11020000040040400454c4200
  | 6, 12 => 0x40040400000411000000000000800000000050000000001c00000000060000002840000000c11000000000001c00001051030000000000800000000060000043040000000000060000000001000000000040000000001000000811000000001840400000000040000000000000001051030000000000800000801010000000001c0000000005000003144000000108102000004204100000002101000000000100000000004
  | 6, 13 => 0x1c00000c51020000000000c000010810400000028404000000d100000000184000000080101000d5410804000000000200114214804000010010100000000014000008510000000100404000000000200000034400000010010500000000014000000e1010000000001c00001001070000000000400000000040000000001400000061000000031040400000121000000004840400000c41010000000001800000c1100
  | 6, 14 => 0x30040c00001051060000040040400001001060010541080400000000050000034440400000000070000000000000000c41000000000001000000000000000001840400000000060000013440000000c51030000004840400000000020000041440800000000060000040040400000000040000003840000000000050000031440c00000000020000030041c00000c0104000000000100000000001000000184040000100106
  | 6, 15 => 0x1800000c01030000030440000000000030000031441400415042000000000001c000004d1000000000001000000000060000000001000001051060000003840000000000040000034041400000061000000002840000000c91000000000000c00000121010000000000000000c910700000104400000000000300000320404000010c105000003144100000000007000003004080000000003000004044000000006100
  | 6, 16 => 0x31040000001011000010d4308000000100101000d521080000000000030000024440000000111000000043440800000801010000000000000000000010000000000800000000050000000000000000000020000001840400000801010000000840400001011000000000001400000000040000000000800001001050000040041800000000010008521080000000801010000040040400000c010400000000000000010c101
  | 6, 17 => 0x11421480400000000060000001840400000000000000000001400324c820000000000014000000d1000000030040c00000c51060000030440000000000050000000001800001011000000000001000000000000000021040400000000070000000000000001051050000001840400000000000000000001000425082010000021440000000000020000031440800000c5102000003104040000000005000000284000000080101
  | 6, 18 => 0x30040400000000020000040040400000401010000020040400000c91070011421480000324c82010000031441000000000060000000000000000000060000030440000000911000000040040400255042000000041440000000c81020000000000800001091000000040040400000c110000000304400000010510100000310400000008410000000000004000000000400000000014000000a101000003144080000000000
  | 6, 19 => 0x1840000000000000010541080400000000010000000000c00000d01010000000001400000000030000000000c00000061000000041440400000851010000000001800001011000000043040400000401010000040041c00000000010000003440000000000020000003840000000c11000000000001c00000000050000042440000000121010000000001000001011000000004440000000000030000000000c0050504200
  | 6, 20 => 0x84000000105104000c932080400000000030000030041800000000070000020440000000091000000000840400000000030000000001800314c42000000032040800000000040000000001000000811000000000000800000c11000000000000c00001011000000000000800000000020000000001000000c01020000040040800000000070000000000400000c11000000000000000000c4101000000000080000000004
  | 6, 21 => 0x1400000c01040000000001800001011000000000000c00255042010000000001000000061000000010040400000061010000020040400000000030000040440000000061000000000000000000000040000000000c00000000000000000001400001001010000040440000425082000000000001400000000050000040440000000411000000000000c00000c11000000000000400000801010000040440000000c0103
  | 6, 22 => 0x400000801010000030440000351052000000003840000000000070000000000800000841000000001840000000000050000000001c00000061000000000000800000000030000000000000001041010000042041000000801010000000840000000000010000043040c00000000020000020040400000d11000000020440000000000060000020440000000491000000043040400000c81000000010040400000c1100
  | 6, 23 => 0x300414000000000600000000008000000000000000434404000010510500000000000000008510100000300410000000e1000000000000800000000020000000001400000c01070000030040c000000d100000000000180000104101000000000140000100104000000184040000000001000000184000000012100000002044000000000003000003444100041504200000000000140000104101000002044000050105201
  | 6, 24 => 0x1800000000060000000001800000000020000001440000000c51000000000000000000000040000030041c00000021000000010440000000000040000000840000000411000000000000c0000080101000000484040000041100000003004080000000001000000000180042508201000000000080000000002000000384040000000006000000000180000040101000002044000000005100000001044000000105107
  | 6, 25 => 0x10510300000000000000000d10000000310404000000000200000104400000000a1000000000000400000000030000040440000000000050000000000800000851000000010440000000c01020000040041c00000051000000000000c00000061010000003440000000000000000020040400000000000000000840000000851000010d4308040000000006000003144180025105200000000000040000000002
  | 6, 26 => 0xc91010000020440000000000010000000000800000801010000010440000001001010000000000c00000091000000031440000000401010000001840000000061010000000000400000811000000041040000000000070000031440000000c01010000020040400450852010000000001000000000000000000000800000c5102000000000180000000002000002004040000081100000c53108040000041100
  | 6, 27 => 0x10040400000051000000001840400000091000000000000c00000000000000021040400000061010000000000800000061000000001840000000000070000031040400000401010000010440000000c81000000000000800000021010000003440000000000010000021040400000000060000013440000000000020000000000000000000060000040440000000000070000030041400000851010000001840400000c5102
  | 6, 28 => 0x401010000010040400000051000000001840400000411000000000000c0000006100000000000040000000000000004004040000040101000002004040000100103000000000040000000007000000184000000041100000000144000000000006
  | 7, 0 => 0x2840000000000030000000001800000061000000040440000000000040000000000800000061000000002840000000000040000031440000000000030000000000000000000050000000000400001001010000000001800000000010000000000000000000020000000000800000c810100000310400000000a10100000000018000000610100000000004000000000700000000004000000000500000424400000008d101
  | 7, 1 => 0x1400000000010000000000000000000030000000001000000000050000000001c00000000020000000000800000000070000000000000000000020000000000400000000030000002840400000000020000041440400000000030000000000000000000050000000000800000000060000000001800000841010000000001c00000000030000000001000000000000000000000000000c0101000000484040000000002
  | 7, 2 => 0x42440400000000020000001840400000000000000000000c00000000010000000001c00000000000000000000c00000000000000000001000000401010000042040000000121000000000001c00000000010000000000c00000c1100000000000180000000002000003244000000104100000000000100000012100000000000100000000006000000000100000000002000004304000000000003000000000000000000003
  | 7, 3 => 0x31440400000000040000002840000000c41010000000000c00000061000000040440000000000030000030440000000000010000000000c00000000010000000840400000121010000000000800000000040000000000800000000020000000001800000000040000002840400000c41000000000000400000000000000042040400000000010000000000c000000e100000000000180000104101000000000140000000000
  | 7, 4 => 0x10040400000000010000000000000000000020000032440000000000010000000000000000000020000000000c00000d01000000042040400000000010000000000c000000000600000000004000000000700000000010000000e10100000414400000000000100000038400000010410000000424404000000e100000000000000000000000000000184000000000002000000000100000000004000000000040000000002
  | 7, 5 => 0x2840000000000050000000000800001011000000000000000000000020000000001000000000000000000001000000000000000000840000000000040000000000000000000050000000000c00000000020000020040400001091000000000000400000000060000000001000000000020000000000c00000c910100000000010000000e10100000000010000000000300000000014000000000300000000010000010c101
  | 7, 6 => 0x800000000060000000000400000000040000000000400000000000000030440000000411000000000000c00000000070000032040400000000030000000001800000000020000043040000000000040000000000000000000050000000000400000000000000000001800000000000000041440400000c91010000021040400000000000000000001000000c010100000214400000000e101000000000100000006101
  | 7, 7 => 0x414400000010010100000000000000000000100000000014000000000000000038400000000000200000000004000000a1010000001840400000000010000021440400000061000000001840000000c81000000000000c000000000000000000000000010d10100000028400000000a10100000000008000000610000000404400000008010100000018404000010c100000000000100000000007000004044000000000006
  | 7, 8 => 0xc00000000060000000000000000000010000000000000000121010000000000800000851000000000000000000061000000000000400000c81010000000000400000000000000000000400000000010000040040400000000060000002840400000000000000001840400000000010000001840400000000010000000000c0000101100000003044000000000001000004144040000002101000000000080000000000
  | 7, 9 => 0x400000000000000000000400000000010000010440000000411000000021040000000c11000000040440000000000000000000000400000000010000043440000000000000000000000400000000010000000000c00000021000000000000000000000000000000000000000000030000000001800000401010000000000c000000000000000000010000010d1000000010440000000c4100000000000000000000001
  | 7, 10 => 0x400000000010000003840000000401010000000000400000411000000000000c00001001010000000000400000851010000000840000000000010000000000c0000085100000000000000000000000000000184040000002100000000000000000000000000002104040000000000000000000040000000001000000184040000000003000002104040000006100000004004040000000005000000000080000080101
  | 7, 11 => 0x6101000000000080000002101000000000000000041100000001004040000000000000000000000000006100000000000000000000000
  | 8, 0 => 0x40000000001000000000000000000000000000000000000000001000000000040000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 7 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 7 s ws hint
  | 2 => checkCutEntry dom_4 roots_4 6 s ws hint
  | 3 => checkCutEntry dom_6 roots_6 6 s ws hint
  | 4 => checkCutEntry dom_7 roots_7 6 s ws hint
  | 5 => checkCutEntry dom_8 roots_8 6 s ws hint
  | 6 => checkCutEntry dom_9 roots_9 6 s ws hint
  | 7 => checkCutEntry dom_10 roots_10 6 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_11 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_11 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_11 == dom_11) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_11 goalM u ys) : RunD dom_11 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_11 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := z3_0
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
theorem z4_32 : ∀ i, 32 ≤ i → i < 36 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 32 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 36 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (z4_32))))
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
theorem z5_144 : ∀ i, 144 ≤ i → i < 145 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 144 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 145 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (z5_144))))))))))))))))))
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
theorem z6_280 : ∀ i, 280 ≤ i → i < 285 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 280 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 285 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (z6_280)))))))))))))))))))))))))))))))))))
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
theorem z7 : ∀ i, 0 ≤ i → i < 168 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (z7_160))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 17 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 16 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 17 → Z 8 i = true := range_split z8_0 (range_split z8_8 (z8_16))
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
  scr dom_11 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_11 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_11 roots_11 goal_11 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_11 goal_11 := by
    have h0 : isConstB dom_11 goal_11 = false := by decide +kernel
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

end S_11

theorem low_11 : Lower dom_11 roots_11 goal_11 10 := S_11.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_11_bits : ∀ r : Fin 64, roots_11.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_11_lt : ∀ r : Fin 64, dom_11.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_11 T)
    (hlow : Lower dom_11 roots_11 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_11, Avail mask256 roots_11 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_11 hfan 0 roots_11 roots_11 rfl hsup0
  set out := (execN C.gates roots_11).getD C.output 0
  have hout : out &&& dom_11 = T &&& dom_11 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_11_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_11 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_11_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_11).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_11)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_11.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_11 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_11).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_11 &&& mask256 = dom_11 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_11 = T &&& dom_11 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_11, hd63, hout]
  have hnc_m : ¬ IsConst dom_11 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_11 roots_11 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_11, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_11 roots_11 0 roots_11 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (3941132520 * 2 ^ 32 + 3907578056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_11.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_11 10 hT6 (by unfold IsConst; decide) low_11

def wit : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [12, 3]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [14, 7]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_15461_aux

theorem PEqualNP.Outside.L_meta_15461 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132520 * 2 ^ 32 + 3907578056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132520 * 2 ^ 32 + 3907578056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_15461_aux.wit, PEqualNP.Outside.L_meta_15461_aux.wmono, le_trans PEqualNP.Outside.L_meta_15461_aux.wsize (PEqualNP.Outside.L_meta_15461_aux.lower s hs), PEqualNP.Outside.L_meta_15461_aux.weval⟩
