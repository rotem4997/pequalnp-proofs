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

namespace PEqualNP.Outside.L_meta_12062_aux

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

def dom_0 : Nat := 0x4400440044004400
def goal_0 : Nat := 0x4400400040000000
def roots_0 : List Nat := [0x4000400040004000, 0x4400000044000000, 0x4400440000000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(14, 30), (14, 46), (26, 30), (26, 58), (42, 46), (42, 58)]
def r1sG : List Nat := [14, 14, 26, 26, 42, 42]
def r2sG : List Nat := [30, 46, 30, 58, 46, 58]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xd656288
  | 3, 0 => 0xd656288
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x440044000000000044000000440000004000400040004000
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

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
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

def dom_1 : Nat := 0x5000500050005000
def goal_1 : Nat := 0x5000400040000000
def roots_1 : List Nat := [0x4000400040004000, 0x5000000050000000, 0x5000500000000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0x5500000055000000
def goal_2 : Nat := 0x5400000040000000
def roots_2 : List Nat := [0x4400000044000000, 0x5000000050000000, 0x5500000000000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 4 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0x5500550000000000
def goal_3 : Nat := 0x5400400000000000
def roots_3 : List Nat := [0x4400440000000000, 0x5000500000000000, 0x5500000000000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 4 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0x5500550055005500
def goal_4 : Nat := 0x5400400040000000
def roots_4 : List Nat := [0x4400440044004400, 0x5000500050005000, 0x5500000055000000, 0x5500550000000000]

namespace S_4
def pairsG : List (Nat × Nat) := [(14, 30), (14, 46), (26, 30), (26, 58), (28, 30), (28, 60), (42, 46), (42, 58), (44, 46), (44, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [14, 14, 26, 26, 28, 28, 42, 42, 44, 44, 56, 56]
def r2sG : List Nat := [30, 46, 30, 58, 30, 60, 46, 58, 46, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_4.map (· &&& dom_4)
def goalM : Nat := goal_4 &&& dom_4
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x32b2d801
  | 4, 0 => 0x5425fa662b50f93a1399e7cd09a3adb0
  | 5, 0 => 0xdd58bfc5767bee795474b636
  | 6, 0 => 0xdd58bfc5
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x50005000000000004400440044004400440044000000000040004000400040004000000040000000110055001100550011001100110011000000000055005500
  | 0, 1 => 0x5500550000000000550000005500000055000000000000005000500050005000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa7544
  | 4, 0, 0 => 0xba8635ba86250a8104a98765
  | 5, 0, 0 => 0xba864ba86550a8604
  | 6, 0, 0 => 0xba864
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3000cf0c0003000ff3f3003f
  | 0, 1 => 0xfc0c3cc00333
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xb625df5ca157015b62a20015
  | 0, 1 => 0xfeaebdea8b77
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 12 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 2 => 1
  | 3 => 4
  | 4 => 8
  | 5 => 2
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0x1171040b
  | 3, 0 => 0xdd58bfc51c07b17c02dca2790037e405
  | 4, 0 => 0xdd58bfc59f5dec7b767bee795474b636508eb14e452b88b2149b0c5b046332fe
  | 5, 0 => 0x9f5dec7b452b88b2
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x2
  | 3, 0 => 0x800000
  | 4, 0 => 0x30000000000100000400001
  | 5, 0 => 0x1
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 4 s ws hint
  | 1 => checkCutEntry dom_1 roots_1 4 s ws hint
  | 2 => checkCutEntry dom_2 roots_2 4 s ws hint
  | 3 => checkCutEntry dom_3 roots_3 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := z5_0
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
  scr dom_4 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_4 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_4 roots_4 goal_4 7 := by
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

theorem low_4 : Lower dom_4 roots_4 goal_4 7 := S_4.noCircuit

def dom_5 : Nat := 0x3300330033003300
def goal_5 : Nat := 0x3200200020000000
def roots_5 : List Nat := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 7 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_6 : Nat := 0xf000f000f000f00
def goal_6 : Nat := 0xe00080008000000
def roots_6 : List Nat := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 7 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_7 : Nat := 0x3300000033000000
def goal_7 : Nat := 0x3200000020000000
def roots_7 : List Nat := [0x2200000022000000, 0x3000000030000000, 0x3300000000000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_8 : Nat := 0xff000000
def goal_8 : Nat := 0xe8000000
def roots_8 : List Nat := [0xaa000000, 0xcc000000, 0xf0000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 4 :=
  lower_iso [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

def dom_9 : Nat := 0xff000000ff000000
def goal_9 : Nat := 0xfe000000e8000000
def roots_9 : List Nat := [0xaa000000aa000000, 0xcc000000cc000000, 0xf0000000f0000000, 0xff00000000000000]

namespace S_9
def pairsG : List (Nat × Nat) := [(25, 27), (25, 29), (25, 57), (26, 27), (26, 30), (26, 58), (28, 29), (28, 30), (28, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [25, 25, 25, 26, 26, 26, 28, 28, 28, 56, 56, 56]
def r2sG : List Nat := [27, 29, 57, 27, 30, 58, 29, 30, 60, 57, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_9.map (· &&& dom_9)
def goalM : Nat := goal_9 &&& dom_9
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x2d4c796
  | 4, 0 => 0x5e5c638619a63e0414994c05054ac424
  | 5, 0 => 0x8da7b5cb212a3a6c11fc6114
  | 6, 0 => 0x8da7b5cb
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0000000f0000000ee000000ee000000cc000000cc000000aa000000aa00000055000000550000003300000033000000110000001100000000000000ff000000
  | 0, 1 => 0xff000000cc000000ff000000aa000000ff00000000000000fe000000fe000000fc000000fc000000fa000000fa000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xb9864
  | 4, 0, 0 => 0x74204b75415cb7655ba7545
  | 5, 0, 0 => 0xb75440b7534db7545
  | 6, 0, 0 => 0xb7544
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1c003f038007ff8fc7fc01ff
  | 0, 1 => 0xe38e07e001ff1f81c7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x9d26ff4b924fdb0b469000db
  | 0, 1 => 0xfbdf6ff24fffdfbbdf
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 2 => 1
  | 3 => 4
  | 4 => 8
  | 5 => 2
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0x6a19ae0
  | 3, 0 => 0x8da7b5cb3988a82122dd62e9025585ab
  | 4, 0 => 0x9fdcf7af8da7b5cb248d14b52435adc521cecb33212a3a6c11fc6114031c2493
  | 5, 0 => 0x9fdcf7af21cecb33
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x1
  | 3, 0 => 0x800002
  | 4, 0 => 0x800000000000000010000040000000000400001
  | 5, 0 => 0x800001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_2 roots_2 4 s ws hint
  | 1 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 2 => checkCutEntry dom_8 roots_8 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_9 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := z5_0
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
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_9 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
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

def dom_10 : Nat := 0xff00ff0000000000
def goal_10 : Nat := 0xfe00e80000000000
def roots_10 : List Nat := [0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 7 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9

def dom_11 : Nat := 0x2200220022002200
def goal_11 : Nat := 0x2200200020000000
def roots_11 : List Nat := [0x2000200020002000, 0x2200000022000000, 0x2200220000000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_12 : Nat := 0xaa00aa00aa00aa00
def goal_12 : Nat := 0xaa00a800a8000000
def roots_12 : List Nat := [0x8800880088008800, 0xa000a000a000a000, 0xaa000000aa000000, 0xaa00aa0000000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8800880088008800, 25, 27)] (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xcc00cc00cc00cc00
def goal_13 : Nat := 0xcc00c800c8000000
def roots_13 : List Nat := [0x8800880088008800, 0xc000c000c000c000, 0xcc000000cc000000, 0xcc00cc0000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_14 : Nat := 0xf000f000f000f000
def goal_14 : Nat := 0xf000e000e0000000
def roots_14 : List Nat := [0xa000a000a000a000, 0xc000c000c000c000, 0xf0000000f0000000, 0xf000f00000000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13

def dom_15 : Nat := 0xff0000000000
def goal_15 : Nat := 0xe80000000000
def roots_15 : List Nat := [0xaa0000000000, 0xcc0000000000, 0xf00000000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 4 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_16 : Nat := 0xff000000ff00
def goal_16 : Nat := 0xe80000000000
def roots_16 : List Nat := [0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff0000000000, 11, 43)] (by decide +kernel) (by decide +kernel) low_15

def dom_17 : Nat := 0xff00ff00
def goal_17 : Nat := 0xe8000000
def roots_17 : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 5 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16

def dom_18 : Nat := 0xff00ff00ff00ff00
def goal_18 : Nat := 0xfe00e800e8000000
def roots_18 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

namespace S_18
def pairsG : List (Nat × Nat) := [(11, 27), (11, 43), (13, 29), (13, 45), (14, 30), (14, 46), (15, 31), (15, 47), (25, 27), (25, 29), (25, 57), (26, 27), (26, 30), (26, 58), (28, 29), (28, 30), (28, 60), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [11, 11, 13, 13, 14, 14, 15, 15, 25, 25, 25, 26, 26, 26, 28, 28, 28, 41, 41, 41, 42, 42, 42, 44, 44, 44, 56, 56, 56]
def r2sG : List Nat := [27, 43, 29, 45, 30, 46, 31, 47, 27, 29, 57, 27, 30, 58, 29, 30, 60, 43, 45, 57, 43, 46, 58, 45, 46, 60, 57, 58, 60]
def mpG : Nat := 0x1fffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_18.map (· &&& dom_18)
def goalM : Nat := goal_18 &&& dom_18
def NN : Nat → Nat
  | 5 => 11
  | 6 => 30
  | 7 => 15
  | 8 => 5
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xa46faa409f3825638d40f6c88016b4f573ce60f96476c9275ac3dc30467beb2a2bb6f2c00e10b9260112cd06
  | 6, 0 => 0xec3e57f9e706d31ccdf62fe58b5e5aa87cd5e6065dbd9cfb528b97dc4b59aa1b40b4f8463eab379e3c12672e3be04b9f3ae5b9b53a42d5f136dee36834f04c332ebdc9ab2d4b34d22cb409032bc717e1284ba7562215c8621a5326ba15babcc6152cc44a13c886310c5d846b085bf81f06c3703e068aac6e
  | 7, 0 => 0xaf6851a890fef5958883a5ff821183aa6221d4735502b33349c3f6ed3739194137252ae62f77a27825c5281a252dfc4b1913588813cdf97f0f5d26a8
  | 8, 0 => 0xc22d231e7a5e7565686746ca287f8e3c27f195c0
  | 9, 0 => 0xc22d231e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x500ff000500ff00050005000500050003000300030003000000ff00ff00ff000000ff000000ff000000ee00ee00ee0000000f000f000f0000000000ff00ff00
  | 0, 1 => 0xf000f000f000f000ee00ee00ee00ee00ee00e000e000e000cc00cc00cc00cc00aa00aa00aa00aa00550055005500550033003300330033000f000f000f000f00
  | 0, 2 => 0xfe00aa00aa00aa00fc00fc00fc00fc00fc00fc0000000000fc000000fc000000fc00000000000000fa00fa00fa00fa00fa00fa0000000000fa000000fa000000
  | 0, 3 => 0xff00cc00cc00cc00ff00aa00aa00aa00ff00050005000500ff000000ff000000ff00000000000000fe00fe00fe00fe00fe00fe0000000000fe00cc00fe00cc00
  | 0, 4 => 0xff00ff0000000000ff00fa00fa00fa00ff00f000f000f000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x1c289200501c592380589c6d648e689c3cd30b66d550f30b689c3cc2c260193cc2c358a07dc58b689c5d63cc600b2480c0589d70f30b6
  | 6, 0, 0 => 0x89c6123cc2de26d650f30b789c6da3cc2dc070e30b200602271b2c921a279c6d23cc789c6cf30b15e27164cf30b701c48f38c01a27123cc2c4702270f30a11808a070f30a68a171b3cc2de271b48f38c789c48f30b1dc000f2c90c05
  | 6, 0, 1 => 0x89c289214002271648e589c6cf30b05c001c64f30b58a079c3cc2dc08953cc2c3602270f2c9198089c50f30a601c68f30b018001c2c9200589f7123cc2de271140f30b70163cc2c3018070f30b1406
  | 7, 0, 0 => 0x89c3cc2c4602279c3cc2d8089c68f30b602270f30b158089c48f38c689c4913cc2dc000f30b0c0589e71b3cc2dc001c3cb240500089c30a214070f38c2c0602271b3cb258089c58f30a689c6cf38c2dc089c40f30b6
  | 8, 0, 0 => 0x2270f30b501c3cc2c0589c6cf30b689c48f30b602270f30a5
  | 9, 0, 0 => 0x2270f30b5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 40
  | 6 => 46
  | 7 => 46
  | 8 => 40
  | 9 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfff1c7ff1c0e00381c0e003ffffff1ff007f81f8fffc0fc7e06001ffff
  | 0, 1 => 0x1c0e07e01f8fffc00001f807038f300703e7ffc7e0c3f1f8e19c7e3f03
  | 0, 2 => 0x703e78fc7e3fc7e00000001f80000000000e3f1ffc71c0000001c700
  | 0, 3 => 0xe381c79f0381f3f8e07001c01ff00e0000000ffffffc7fc0000071fff3
  | 0, 4 => 0x7ff80003f1f8ffff81c0fc
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x4fb10552100800081008001b6dbff0db005506db6ffc0241206000db55
  | 0, 1 => 0x9d2e97e37fbfffdbd9edf8972b9f324f27e7ed86c0c2d1a8c18c5a2d03
  | 0, 2 => 0xf6fb7e7efdfefff7ee4155a41fb55d2090005eff7ffef7e0955609df55
  | 0, 3 => 0xfbddef9fb7dbf3fc924801e49ff55f2492007fffffffffe4955f7bfff7
  | 0, 4 => 0x7ffc92abffffffffedf6fc
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 29 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 29 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 35 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 35 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 35 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 35 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 20
  | 5 => 90
  | 6 => 240
  | 7 => 62
  | 8 => 6
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xe706d31cc22d231e9571754a8b5e5aa87d3632c07ab8711773aad30849f7451e497e74213a952ff8399188d23671272236308c4d2f27a1cd24aaa59f1b71195a18992ada09fcb80f06a1fc3f04fbb39e
  | 5, 0 => 0x500650a84fed3be94e8adda84b90162d4a129c9849c3f6ed48251029462bd2cb457662124416abca3f68e54a3d6b695b3d3a57f93b63462a37252ae636c50d5d35da5ae234fecab033d3be2a31987e5430f4059a2f77a2782d5a8aa12d3f30872c4f26b62ba1e7b92b55f01a29b629e1248fd35024213d0f1eb305a31cfb58161ca944fb1bbc53d91987f9931840e34e157a4faf144764a912dccbbe1247bf6c11ee90a511752c480fd7fc5f0f5d26a80bd417860b8fb9b30aa84f510aa2e8070a6ee77708de701208a0987e06843cb106632aaa05220042048a3a3c044e8c6d0445aa6b04443451043a76c7040d90fb02af742b01ac210f00cdad6f002eb4e9
  | 5, 1 => 0xfd9cf3e8dcb5813ac22d231ebdeb6bddbb280195afd21f30af6851a8ad5d55fda6eb33a890fef59589704da48883a5ff821183aa7687dc0e72b8f05f6ccb21fe662360bf651272e16221d4735afd16a4590e5ec358427ecb5777d7d5576d90ad544c273b51433eb3
  | 6, 0 => 0x12413abe11f32cff11a0084511725c0c10eac4641030d80d100217150eae0a060e4e96f30da7e4e30d0804a50cd5ef420cb8e4b70caef3300c6901150c450c370c24d79e0bc2af8c0bb0c0ea0b5a95ee0b37e0a60b2ce9b50b1c73d80ac18aa009a68dda098ff4c0097dfd7c089d9c4d081a7c7b07acd6f107ab58f4078438f10733d89a0720e811071fa9a806ee40c506afbf9a0673b205067249b50621c9050621c71e04f0713004d4558c048bd74d042bb4e503fb64d303c4c4b603c3357703a98808039dd41b0398d0f1030f61b502d23d3302a9f72b028c22310260869d0209bbfe01dce67b01922bc8012cf73200b14228007ee9700026b4580020b0f4
  | 6, 1 => 0x2955912c2929f598287f8e3c287857542873e04b2846edae281ea5c927f195c027bf120b27bc0c3927897b6f272e553926d571c6269111e925aef1d524270129239736e021703504214cd60d209965402073e5722058c9f91fd6ab491f2d71f91ee889f41ea0155e1e23d25c1e0fa2e41dcbd2261d2f6f0a1ca4b3161c7c9ccd1c1529531bed02651bbbd9161b30ddcc1b2815ea1a1dbb6e1a101f841a09ac3119e47b1e19badaed199fc7d818e0d4d31896088f187d66ab185654121766299d1731ca7616dad17916a2300e1623154115d68c8915cfb6fc1585203a1523384314567ead143e936713f421c513c2dce213a369071392fcaa1313d21c1309f21d
  | 6, 2 => 0x54ae9e545445ddf151b4dd894fe05f7a4e3c7bff4d803f1a4d49a3b64bb38a564b0937854972c4e4495a6cca493047dc474ccf7746896dba465fae33454a5b80450f9f5b449368fc42e23de442619b8841ed60fd407a1b9c405320d53eedb2f73ed8392b3e9c312f3dc7fb293d7389c43ce3ef5c3ca0f2b63c3188883b88ae673b3d667f394c41653914be4f376af55d3755d8d43739194136ff257736e6c2be364302ec35bf663335ae2039358284a5355b415a34f5333634923f1f33ea58b43367639f32579d9730f4059a30eb0f492ffcfc1b2f9902892d78365f2d702f3f2cfa375b2b7a27142b6cab0d2b5ada052b1b25882a8e33b12a88fc6c29c4a5fd
  | 6, 3 => 0xd72e2946c90dadabc22d231ebf08803abcc3ff4bb648dc35a2e1f97e9fe9f9419f5d8da09977d6ec963753c39286b19191c4c8a7910e4c9d8ad7c506896dde9985fe8aa78405a73c83898021831a822c7fb8aeb67e3a241f7ccd78697a5e75657a090568798827b573f6883d70ef17956df7cf656ad144646a7e2003686746ca6799a3ef662360bf661048ac6520240e63163431627949ec6012002d5f6eb0fc5e02c4775d4274795ca4d4785af2d38658cb3f9a5632b22355a275545502b333
  | 7, 0 => 0xc22d231ea6ea808ea05d547c964e519791c4c8a78c93b7498c1ba7e68ad7c5068345c9e67fcd9a0c7a5e75656b65e499686746ca645d9b7f585c82c255a275545315071849ab943446882ade41b5044c3d5305273c887543385e2aca33ea58b433ad434f31c634ad2fa2ca8f2f9902892e5deb172e0c57ee2b5ada052acb3f9d2a5a8b54287f8e3c27f195c0209899111f68b6df1e0fa2e41dab9bf41c7c9ccd1c15295319a15104170905c71689962c16292d9f1232e92111f32cff11725c0c0cb886af0c997fdf0c1b785407ab58f40715da67069c72f6067249b504c92ad3043ca2d4034d65880314efc70241cab901dce67b00086d5c
  | 8, 0 => 0x964e519749ab94343d5305272b5ada051689962c11f32cff
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x104400000000000032080300c00003404120021441204c0c00000c810051490300c0144404c83010000010440c000000000500000000000c931485303000003204000000000005000000144140000000009000000384000000081103000003204000000005107
  | 5, 0 => 0xa01880c0030481203000003204080004885203000843108040034485203000d0104808000280e2000000020440c0000000002000901048040000084100000003204080000041104000d0104800000280620000000014418000000a1000000521480c0034041200000000000100003802203000c831080000000811040000000002400048c82010010121080485104813040000000000c0024041202000000000180024041201
  | 5, 1 => 0x500000320404000180220135105204c0c000280e200000d0104804d4414813040000032040400048c02000009010480800000c81020000000001885104813040000e0088000034041200000001044040003802201000d01048000000000009000d021480c00000061000000032040000000000080000000000800000851030000000001400000000030000000000000000000010010520480c00240c0200
  | 5, 2 => 0x2000000000080000000000000048c920321441204c0c00000000060001232080000000411000000001441800000c81000000010441800000411000001210480000414c82000000000001400324c12030010532080000000000080000000000000240412020000000000c000000000800000000018000000e1010000001441400000c8101
  | 6, 0 => 0xe00881000000000080000000002000000000070000020440c000000000100000018404000000e1000000000840c00340852040000000002400000c01000000001440000000061000000003840c00000411030000010440000000841010000a00880c0000006100000003004000000085104000d010481000000c910400000310408000000e102000d010480c00000c8101000001044080000080102000000000140003802200
  | 6, 1 => 0x32040400000c81010000001840000000000050000010440800038022000000031440c000008c100000901048000000000000000d01048040000002103000000000200000081103000003204000000006100000121048080000041101000000384080000041101000000000140034041200000001044000000006101000d010480000000c41000000031440c000008c10200000038404000008c101
  | 6, 2 => 0x32040400000000020010532080400000c810000000210400000000e1030000000001000000c010000000000014000280e201000d010480000000411000001232080800404c82020001232080800000411010000032040800038062010000032040800000c41000000031040800000411010001210480400000061030000032040800028062000000020040000000000000000000840c0000000007000000084000000000000
  | 6, 3 => 0x20040000414c82000000000000000000411010000000000c000000e1010000002841000000000000000000000000000000070000000002400000c11030000000001000000061000000000840800000000050000003840400000000030000a03880000000021020010520480c000000a1010000000840800000000070000010440400000411040000021440c000000e1020000001840400000c8100000002104000000084101
  | 6, 4 => 0x1840000028062000000600881000000061010000001840400000c81000000003840c00048c82020004120480c00000061010009010480800000c8102000d021481000000000050000021441000000411000000003840c00000061000000000002000000c81000000000001400000021000000001840400048852030000001840000214052030000031040400000841010000000000800048c82000000000002000404c8201
  | 6, 5 => 0x1800000811030000000001400000811030000000001800018022010000023040800038022040001210480400048812030000001841000000c11040000000841000000851040000001840400000411010000001440000000c81000000003840000000851040000000000400000000080009010480800414c82020000001840400000000060000010440400000c810200000320408000000e10000000104404000000e103
  | 6, 6 => 0x3840c00000000000000003840c000000000500000008400000000000800000008404000000e10000000000004001048120300000000010000000e1000000000001c00000000050000001440000000c81000000003840c00000000050000003840c00000c11030000003840c003408520300000038404000280e2000000600880000000411010010520480c00000000010000010440000048852030000003840c00000c4100
  | 6, 7 => 0x20000000000300000000000000280620300000000014000000e1030000000001400414812030000003840c00048852030000010440400000c81010000003840c00340412000000010440000000c8101
  | 7, 0 => 0x8000000000200000000004000000000000000000000000000000400000000008000000a1040000032040400000000020000000000c00000000020000000000400000000040000000840000000000000000000000000000c81010000002840000000811040000000000800000851040000000000c000000000200000018408000000000000000000000000000000100000214410000000a103000000384080000000000
  | 7, 1 => 0x30000000000c00000000030000003840c00000000040000010440800000411000000000000400000000030000000001000000000010000000000c00000c81000000000000c00000000080000001840c000000000200000104404000004110300000000000000000000300000320404000000000500000008408000000a10000000038404000000000500000000010000000e103
  | 8, 0 => 0xc0000000002000000000000000000002000000000100000000004
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_4 roots_4 7 s ws hint
  | 1 => checkCutEntry dom_5 roots_5 7 s ws hint
  | 2 => checkCutEntry dom_6 roots_6 7 s ws hint
  | 3 => checkCutEntry dom_9 roots_9 7 s ws hint
  | 4 => checkCutEntry dom_10 roots_10 7 s ws hint
  | 5 => checkCutEntry dom_12 roots_12 5 s ws hint
  | 6 => checkCutEntry dom_13 roots_13 5 s ws hint
  | 7 => checkCutEntry dom_14 roots_14 5 s ws hint
  | 8 => checkCutEntry dom_16 roots_16 5 s ws hint
  | 9 => checkCutEntry dom_17 roots_17 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_18 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_18 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_18 == dom_18) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_18 goalM u ys) : RunD dom_18 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_18 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 11 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 8 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := range_split z5_0 (z5_8)
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
theorem z6_24 : ∀ i, 24 ≤ i → i < 30 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 24 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 30 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (z6_24)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_8 : ∀ i, 8 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 8 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := range_split z7_0 (z7_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 5 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 5 0 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 5 → Z 8 i = true := z8_0
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
  scr dom_18 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_18 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_18 roots_18 goal_18 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_18 goal_18 := by
    have h0 : isConstB dom_18 goal_18 = false := by decide +kernel
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

end S_18

theorem low_18 : Lower dom_18 roots_18 goal_18 10 := S_18.noCircuit

def dom_19 : Nat := 0xaaaaaaaa00000000
def goal_19 : Nat := 0xaa80a80000000000
def roots_19 : List Nat := [0x8888888800000000, 0xa0a0a0a000000000, 0xaa00aa0000000000, 0xaaaa000000000000]

namespace S_19
def pairsG : List (Nat × Nat) := [(35, 43), (37, 45), (39, 47), (39, 55), (41, 43), (41, 45), (41, 57), (49, 57), (51, 55), (51, 59), (53, 55), (53, 61)]
def r1sG : List Nat := [35, 37, 39, 39, 41, 41, 41, 49, 51, 51, 53, 53]
def r2sG : List Nat := [43, 45, 47, 55, 43, 45, 57, 57, 55, 59, 55, 61]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_19.map (· &&& dom_19)
def goalM : Nat := goal_19 &&& dom_19
def NN : Nat → Nat
  | 3 => 5
  | 4 => 9
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x98a78fe39183c68347c4d4682ff0f51a005fc01b
  | 4, 0 => 0xf7c2c40ed04ff6e2a36dba1c92991ea89183c6836d06e43539300fb52e47c2e00ec20aee
  | 5, 0 => 0x9183c683
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa8a8a8a800000000a0a0a0a000000000a0a000000000000088888888000000008800880000000000808080800000000000aa00aa000000000000aaaa00000000
  | 0, 1 => 0xaaaaaa0000000000aaaaa0a000000000aaaa000000000000aaa0a0a000000000aaa0000000000000aa88aa8800000000aa00aa0000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc9634c8644c8724cb844a8644
  | 4, 0, 0 => 0xc864150c6414ec86450864040c8644c86545c86435dc8645c86405
  | 5, 0, 0 => 0xc8644
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf0fc0ec0030d00000cf8f07f
  | 0, 1 => 0xff0f8ef80c0ec0037d070
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf3fd2ed0871d21550c508037
  | 0, 1 => 0xffffeefc8feefc8fffaf7
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 15 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 15 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 15 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 15 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_19 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_19 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_19 == dom_19) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_19 goalM u ys) : RunD dom_19 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_19 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_19 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_19 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_19 roots_19 goal_19 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_19 goal_19 := by
    have h0 : isConstB dom_19 goal_19 = false := by decide +kernel
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

end S_19

theorem low_19 : Lower dom_19 roots_19 goal_19 6 := S_19.noCircuit

def dom_20 : Nat := 0x2222222222222222
def goal_20 : Nat := 0x2200200020000000
def roots_20 : List Nat := [0x2020202020202020, 0x2200220022002200, 0x2222000022220000, 0x2222222200000000]

theorem low_20 : Lower dom_20 roots_20 goal_20 5 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16

def dom_21 : Nat := 0xa0a0a0a0a0a0a0a
def goal_21 : Nat := 0xa00080008000000
def roots_21 : List Nat := [0x808080808080808, 0xa000a000a000a00, 0xa0a00000a0a0000, 0xa0a0a0a00000000]

theorem low_21 : Lower dom_21 roots_21 goal_21 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20

def dom_22 : Nat := 0xaaaa0000
def goal_22 : Nat := 0xa8800000
def roots_22 : List Nat := [0x88880000, 0xa0a00000, 0xaa000000]

theorem low_22 : Lower dom_22 roots_22 goal_22 4 :=
  lower_iso [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_23 : Nat := 0xaaaa0000aaaa0000
def goal_23 : Nat := 0xaa800000a8800000
def roots_23 : List Nat := [0x8888000088880000, 0xa0a00000a0a00000, 0xaa000000aa000000, 0xaaaa000000000000]

theorem low_23 : Lower dom_23 roots_23 goal_23 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 25, 57)] (by decide +kernel) (by decide +kernel) low_22

def dom_24 : Nat := 0xaaaaaaaa
def goal_24 : Nat := 0xa8800000
def roots_24 : List Nat := [0x88888888, 0xa0a0a0a0, 0xaa00aa00, 0xaaaa0000]

theorem low_24 : Lower dom_24 roots_24 goal_24 5 :=
  lower_iso [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21

def dom_25 : Nat := 0x8888888888888888
def goal_25 : Nat := 0x8880880088800000
def roots_25 : List Nat := [0x8080808080808080, 0x8800880088008800, 0x8888000088880000, 0x8888888800000000]

namespace S_25
def pairsG : List (Nat × Nat) := [(7, 23), (11, 27), (11, 43), (15, 31), (15, 47), (19, 23), (19, 27), (35, 43), (39, 47), (39, 55), (51, 55), (51, 59)]
def r1sG : List Nat := [7, 11, 11, 15, 15, 19, 19, 35, 39, 39, 51, 51]
def r2sG : List Nat := [23, 27, 43, 31, 47, 23, 27, 43, 47, 55, 55, 59]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_25.map (· &&& dom_25)
def goalM : Nat := goal_25 &&& dom_25
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x6d5d2e3b
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x8888888800000000888800008888000088008800880088008080808080808080
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf80c6001e319
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf94e6b9de739
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_25 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_25 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_25 == dom_25) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_25 goalM u ys) : RunD dom_25 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_25 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_25 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_25 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_25 roots_25 goal_25 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_25 goal_25 := by
    have h0 : isConstB dom_25 goal_25 = false := by decide +kernel
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

end S_25

theorem low_25 : Lower dom_25 roots_25 goal_25 4 := S_25.noCircuit

def dom_26 : Nat := 0xa0a0a0a0a0a0a0a0
def goal_26 : Nat := 0xa080a000a0800000
def roots_26 : List Nat := [0x8080808080808080, 0xa000a000a000a000, 0xa0a00000a0a00000, 0xa0a0a0a000000000]

theorem low_26 : Lower dom_26 roots_26 goal_26 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25

def dom_27 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_27 : Nat := 0xaa80a800a8800000
def roots_27 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]

namespace S_27
def pairsG : List (Nat × Nat) := [(7, 23), (11, 27), (11, 43), (13, 29), (13, 45), (15, 31), (15, 47), (19, 23), (19, 27), (21, 23), (21, 29), (25, 27), (25, 29), (25, 57), (35, 43), (37, 45), (39, 47), (39, 55), (41, 43), (41, 45), (41, 57), (49, 57), (51, 55), (51, 59), (53, 55), (53, 61)]
def r1sG : List Nat := [7, 11, 11, 13, 13, 15, 15, 19, 19, 21, 21, 25, 25, 25, 35, 37, 39, 39, 41, 41, 41, 49, 51, 51, 53, 53]
def r2sG : List Nat := [23, 27, 43, 29, 45, 31, 47, 23, 27, 23, 29, 27, 29, 57, 43, 45, 47, 55, 43, 45, 57, 57, 55, 59, 55, 61]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_27.map (· &&& dom_27)
def goalM : Nat := goal_27 &&& dom_27
def NN : Nat → Nat
  | 3 => 20
  | 4 => 77
  | 5 => 235
  | 6 => 177
  | 7 => 20
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xd528b96ad33dd8b9d25a0d67cf11c4169f4188889c9024b698354c2c827a6f0c803d237953c7435c523e85644c3885de4ae410ca40fe329c40a0127f2de299032acbb83828aca3a12263769b208911af
  | 4, 0 => 0xbb531a7db5546085b18ec1e2afca63d1aa5c05b1a59a6f0da13e264aa02e9df59ea251f29c457b0697e71b549463327893bb87b2938c42ca8d6c93138d47eee882f5811f7e23476878bbd0c9701169866dcb85676be0086e6b2d9e196afc3d1c6a1dcfb167b3f3cb608ea1705dcca24a5d6ff5805b82b3f35adc0d0159f4885c5331717d4ff3deaf4e47db9f4d2de8b5490c976a46d809d545cf96e8430a70ae426e2b2441272dd93e02dab73c55293a36844f3635ebeb5a3572367631b5870a31071d7130dfc9ef2ff4cbdf2cdc9b5126892a102622aed623cc575c1bf3c94b18df532e162a4aa913f6507a13ccb3bb12b8fd6b0ab3c3a808de4b7a01633898
  | 4, 1 => 0xfdc3574ff1f89c6be9850eedd9de3f1ed064b254cf89b084cf2e1ef3cd472071cd3a4ab6c6bedd5dc626fedec0588e37bff11a8c
  | 5, 0 => 0x305b1dd52fa0a35f2f710bec2f42d9852f0c007f2d5b8b242d05622d2b71c3322a8a25092a7b15ec2a6aadfd29777ae6293522ff28b0401a28a2ceb228a185cb27d3ed07276e376727669e1c25f4576925c34052254d4295251ddb5c24522fb622f0fdf521ebfc2d21742c1920b91334205bde171fb1d9831dfe47e01b9902011b5d261b1b29fce01a26a0891a254d9718e63e7818d888ea16db6e2816a8613416a04da0164a67c41401a504121ce6a61218589311a1b8930fba94c90f9501c90e65e09a0b8379a00a410aad09e08566095787e0091484d808b3993b08756cac0848c62b066db51c0551e1db04de4d4e04b3b0b501c4aa4c00f9fec300537cf7
  | 5, 1 => 0x6c9458616b8d2e4f6b38be94696eb6326906e2096812394767e8392c67d04ea866e3181866bf8fad65dc7a6b65239731645b303c644ef07863ab17dd613b21585f98725b5ee098e35e4beea65d5b708b5c30dd765ac1dcf15a73be505a0028ba58fabdec58aded9d58934a41575cf4fa5681508f5548067453a2497553543237502d68b94fa3812d4e3416e84dacdb264cc4aee04c67f2734aaa5a5b48c21ebb4697a445452b685e44e6661443f4a1d5438a1f6a43355e4a42900e9a4084cfce4070c4ad3e7cd5663c15cace3a7197953a2e747737cf025b37ab9e33362b93fb35b715303467153d32ba07b8327fbee631f7318331a9b885317cb4a930dfc9ef
  | 5, 2 => 0xb94f1a5bb8f8c1f5b3f92011b27f3ef0b22df25cb01cc75fac264b55ab9f27a9aa3c7614a785de62a6da9abda4bd0855a2a4366da1519ab19fc564209e91219a9e2d1cb89d7f9b199d065c5e9be11c459aa0ea3e99e55dcc99985985965b9d1b93542c698ee230b68dce28138b54c94f8a26f003894ef61f887384778864ba1e863dc07985d5a21d85a0fa1183a2d79e833d0adc81fb2dd581bb81477fe3d59a7f79d80b7f5258ae7f4af5d07dded7b47c9059887c54f4ec78d8cf6378b83f9a7863496a785296f477f5da8777cb227a77abf00275dd779975cba6dd75356170739b694b724b00dc6f93971e6f699cce6f13022a6ee084106def818a6dee3246
  | 5, 3 => 0xfacfebe3f7bdbd95f7a9d42ff7408678f7251ed3f2474058f0cf7315f0952a2aebfcd718e9ba4705e97ec691e03bee62df1b1a99deb4d1cadd6854addc0b4b3fda97d824d8710df2d822fd7ed753f331d607bd36d4fbe315d46a6c8ed41817c3d2f2d8c7d2e59637d2601ac4d241428cce8e1b0fce5ea4e3ce2e83a1ce2996adcbcabc64ca725a1bca69bf1dc981f9a4c7a94606c71ff54fc706e4dbc69c1e8bc617db16c3f7e7a8bc836f88
  | 6, 0 => 0x47267ee64697a445462374a945587707443c1e524436811d3f7cca723d5ba33d3c0eb36e3bf0653f3bbbc96f3ba8163937f5943e37a9f5b63744ee253556f83934e34bc934278a09341dafbf3022bf822da461bb2ade227429e7715826f68eb026c149bc251ddb5c24e408c024a92463233bef122302eb1f21663c201f6f587c1dfe47e01cb19cc81c92e1de1c3cbde71b13e74c19523c6417f189af179fcee415e8d6111531109814b587b312dbc52b12a3a57c11df2ac61045f4800f932a530c9dd6920c991d890b95722f0b8412000b4b7bbf0ac08e56099cbba9071d87b605929501051dd0ae0339582201e405c9019cc41b00c6df010078df0b00537cf7
  | 6, 1 => 0x95332c6b94c5bd8893f918ae92c572f39211c2579205447191583da29133c4fa910eb81a8d3b39228c71e27a8a652bb089fc75d2898781e687e40109878efd0386967d2e856dd5ce830707f6807afade7fcd9ff47fbc28477f3e813a7e6243107d9b12da7d3624d57cd52c3a7ab405057937758e768144647284e78d717785af6b20dcfa6afcc3836982ba486937d57468e98b516898839267e545cb66775c5d644ef078627ada8460c5aed65f48870c5dfb08a25b5b47085973f0b1566f557154ef4b39534137d952d2c0e7520d2ac6502d68b9501247d04fa3812d4ee81f3d4e90d3334e4612624dcfb7bd4d4308254be861664818f01e47a034fe47653d09
  | 6, 2 => 0xf9536981f7251ed3f4918701f2aa30aaf2705fccf18094c5ecbeb245ead75beee89a9f65e0c7caa9dc0b4b3fda23f4e8d920eaabd8710df2d75d25ebd6124694d59206d8d222bcb0cf624399cb9736bfcafd92a0c981f9a4c4972d65c1d6b44ec1af24e8bfd54ae5be058831bdedf48ebd046dcdbceaea51ba4f266aba2a713ab8e1f119b3cc2c95b0fbbde2ac79e26ca6aa695ba5ebf687a236c803a12a14079fee05439ebf54459e0ead0e9df411909cb3b89b99fe3f8396b991c596213cd4959cb0bc
  | 7, 0 => 0xdd4b046bcfbf7520cafd92a0c9163c49c813320cbf06ab049fee05437681446474601d2f6eae6fa85dfb08a2534137d94ced500341c508483f048f3130f1064f2a9a5d9a2319d16a15e8d6110e619fdd
  | 8, 0 => 0x4ced5003
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaa0000aaaa0000aa22aa00aa22aa00aa00aaaaaaaaaa00aa00aa00aa00aa0022aaaa0022aaaa00220022222222220000aaaa0000aaaa00000000aaaaaaaa
  | 0, 1 => 0xa080a080a080a080a000a000a000a00080808080808080802aa02aa02aa02aa020a020a020a020a0202aaaa0202aaaa020202020202020200aaaaaa00aaaaaa
  | 0, 2 => 0x808080808080808022222222222222222222220022222200222200002222000022002200220022000a0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a0000
  | 0, 3 => 0x88800000888000008800aaaa8800aaaa8800aa008800aa0088008800880088008800000088000000828282828282828280aa80aa80aa80aa8080aaaa8080aaaa
  | 0, 4 => 0x8888aaaa8888aaaa8888aaaa0000aaaa888888888888888888888888000000008888880088888800888888008888000088880000888800008880888088808880
  | 0, 5 => 0xa0a0a0a000000000a0a0a000a0a0a000a0a0a000a0a00000a0a00000a0a00000a0800000a0800000a000a000a000a000a0000000a000000088aa88aa00aa00aa
  | 0, 6 => 0xa800a800a800a800a800a800a000a000a8008800a8008800a8000000a8000000a0aaa0aaa0aaa0aaa0aa00aaa0aa00aaa0aa0000a0aa0000a0a0a0a0a0a0a0a0
  | 0, 7 => 0xa8a0a8a000000000a8a0a0a0a8a0a0a0a8a08800a8a08800a8a00000a8a00000a888a888a888a888a888a888a000a000a8888888a8888888a8880000a8880000
  | 0, 8 => 0xa8a8a8a800000000a8a8a800a8a8a800a8a8a0a0a8a8a0a0a8a8a0a088880000a8a88888a8a88888a8a80000a8a80000a8a8000088880000a8a0a8a0a8a0a8a0
  | 0, 9 => 0xaa00aa0000000000aa00a000aa00a000aa008800aa008800aa00880088008800aa000000aa000000aa00000000000000a8a8a8a8a8a8a8a8a8a8a8a8a0a0a0a0
  | 0, 10 => 0xaa80aa8080808080aa808080aa808080aa00aaaaaa00aaaaaa00aaaa0000aaaaaa00aaaa00000000aa00aa00aa00aa00aa00aa00aa000000aa00aa00a8000000
  | 0, 11 => 0xaa88aa8888888888aa88aa8800000000aa88aa0088880000aa88a080aa88a080aa888888aa888888aa88888888888888aa880000aa880000aa88000088880000
  | 0, 12 => 0xaaa0a0a0aaa0a0a0aaa0a0a0aa000000aaa0a0a0a0a0a0a0aaa08880aaa08880aaa00000aaa00000aaa00000a0a00000aaa0000000000000aa88aa88aa88aa88
  | 0, 13 => 0xaaa8aaa088880000aaa8aa00a8a80000aaa8a0a0aaa8a0a0aaa80000a8a80000aaa0aaa0aaa0aaa0aaa0aaa0a0a0a0a0aaa0aaa000000000aaa0aa00a0a00000
  | 0, 14 => 0xaaaa888888888888aaaa880088008800aaaa808080808080aaaa00aaaaaa00aaaaaa00aa00aa00aaaaaa0000aaaa0000aaaa000000000000aaa8aaa8a8a8a8a8
  | 0, 15 => 0xaaaaaaaa00aa00aaaaaaaaaa00000000aaaaaa00aaaaaa00aaaaaa00aaaa0000aaaaaa0000000000aaaaa0a0aaaaa0a0aaaaa0a0a0a0a0a0aaaa8888aaaa8888
  | 1, 0 => 0xaaaaaaaaa8a80000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x7e642a21468524e25468674b254725b4f4047e7257374624f4e254684f4e25472564f4945d4b493046867522547e4b461747e633721400684e2537e59372b4725b4f3e47e5d4d304
  | 3, 0, 1 => 0x6e4b3025472574f3747e7256374725d37304
  | 4, 0, 0 => 0x7e5952492c5724f37302557e5d4b302557e7252402757e5c522c255004f4e2c254725b4f301c57e7d4b3e2557e7257524956c524f30255724f4b39305726f5230255724f3b301c5724f40372557e7d5b301b57858524f305
  | 4, 0, 1 => 0x7e72642a2557e72603d3057e4e2c251c57e785d523054f4b492c255524f4b302257e726a523b57b7252491757e4f4d302157e725b523e57e6352491f567524f2c2554f4b42302557e724b37175725f524f40572524f37175
  | 4, 0, 2 => 0x5d4f4b302557e7d5a4b30500785d523047e725937305007e63372547257524f495007e72521a47e7256524957e6d522b255725d5249305724f4b3b305725b4f301b57e725246175005d4b302547e7d4b49175724f3530255
  | 4, 0, 3 => 0x7c6a4b3025572564f302557e4b4630255724f4b491757e786b2a215624f4b302557e725b52405785d524f3057c62523025572504230255524f4e2c2557e724f37175724f3430255674f4b2c255004f4b2d254726a4f4e255
  | 4, 0, 4 => 0x7e3025074726e5230255724f4937175786952302157e7260372c5725d4b302557e4b372c2555d524b30255724f372c2557e4b30250757e725249185726a4f3725500724f37174
  | 5, 0, 0 => 0x7e7252231257e6352302524678725f524f3067e6d5952302560072524f3b30500785230210057e725952493067e715242302567e72524937176007e6352492557e724f37302567e725230251e67e76725230256007e5230250357258524f302567e72524230256
  | 5, 0, 1 => 0x72524f4330256007e726b372557e72524430256007e7252250f5724f4b30251767e725240250167e725241302567e5b524b30216007e7249170457e7d674b302567267524f302567e72522e25246007e72521709500522512010057e72523730216007b725225125
  | 5, 0, 2 => 0x724f30250857e63523025016007e7d4b251257e724e30251c600723016040057e785230211260072524f2512500524f30160157e7252482c25600724f4d302557e71595230256724f4b49302567e63615230256726952302516600524f30250157e7252402c256
  | 5, 0, 3 => 0x7e726652302567e635230252167e7a522c252467e72523025186004f3025040157e725230282567e72524f491760072524f16125007e60301c015007e5952251257e5952302b2567e725240372567e725230272467e725230251967e727160301c6724f4b3029256
  | 5, 0, 4 => 0x7e777252302167e7252402f256007e52302001500725230160557e72715230206007e724025045724f4b302516600724f25120457e72523b38306007e523b300157e72524b393067e7271523b3067e7252332c256007e72601c1257e72523b301c600724f3730255
  | 5, 0, 5 => 0x7e5225120157e725237302567e72524f40256007e5b52302157e725d52302567e4f4b302c25600725230230057e72523a302567e725230250860072302505045007e524e2c255807252423025672524f3b30256007e7252201257e725b52301c6724f302a251c6
  | 5, 0, 6 => 0x7e7a522c1657e725233251767e78726b2a2567e7267522c256007e7252250b500725e5225125724f4937302567e72523026256726a524f49256007e7830210450072524f491757e7d4b30251b6007e5216120157e524b4230256005e52302501572524f4230256
  | 5, 0, 7 => 0x7c524f4b302567e72523d3025672674f4b302567e7265524b2567e726052492c67b725230251267e777252301767e524b492c2567e72523023126005952302500572524f492c2567e725249471760072695225125007e723016045007d4b3025005007e251204015
  | 5, 0, 8 => 0x7e7d4b302524600725d5230255004f4b302c2550072523b300057e7d7252491767e635230251667e72523025036004f4b30250157e726a522a256724f4b30251c672524f4e302567e726252302567e78524f302167e72524c3025672524f3025026007260301c005
  | 5, 0, 9 => 0x7e726452302567e726b2a252467e75725230256007e5249170157e725230250667e725752302567e727152491767e7d4b302512600725230200057e72524b3b30600554f302501572524f30251067e725b52301b600724f4b25125007f7230160457e72523530256
  | 5, 0, 10 => 0x7e7d4b4a302560030250401005007e7252301557e7d4b30250860078524f30215007252161200572524f30250867e725232302567e725230250c67e72523130256787269523025600724b30250557e7260301c1267e7a5952302567e725243302167e72524917046
  | 5, 0, 11 => 0x7e72523c302567e725249421767b725249302567e7252343025600523025050157e725230200167b72523025176007e5952301650072524f2d2557e7252403f2567e724b37302567e7254523025672524f37302567e7260302c1c6725d524f302567e7260301c016
  | 5, 0, 12 => 0x7e724f4e302567e72524b491767e725246302567e725230271c67e595230250367e7d4b49302567e78523021046725e52302c25672524f4930256725e5230250167e737252302560072524917005726a524f2a2567e725230251d67e7d4b302517672524f30250e6
  | 5, 0, 13 => 0x72524f3027256726a4f4b30256007e7252371757e786b5230216007e30250401572514f4b30256007e7252161257c726a52302567270524f3025672524f30250967257524f302567e7a522c251c67e725652302567e7252492c216007e7d30250857e72523630256
  | 5, 0, 14 => 0x7c4f4b302557254524f302567e72524917016005352302501500724f4b302557e725230250a6724f4b3025086007f302504015724f4b302c256524f4b302c256007e721612045
  | 6, 0, 0 => 0x7e78723025046007e725225121167e72524f302a257007e52302516016007e523027250167e72524b302c2577e72715230251677e7a7252302524700007e725249175007e79725230256007252302c25006007e78725230166007e725b52302567e7252302524127007252302501006007e72524230256
  | 6, 0, 1 => 0x524f30250157e7252302512017007e72524e30256007e72524b301660072524f30251c6007e725952302567e7252302c25247007c72524f30256007e72524b302567e7252302524017000072523016005007e7252492c256007e725225161267e72524b4a302577e72523025160477e72524b3025087
  | 6, 0, 2 => 0x7e726a5230256007e723025240460000725230250550072523025170067e72524b302f257007e725230251067e7252494230257007e724b302504600007e725240255000072524f251257e72523025211277e7252302a251677e726b5230251677e7872524f30257007e74723025046000072302504005
  | 6, 0, 3 => 0x7e71523025016007e72523025086007e5230251c016007e725230160167e72715230251c7007e7d7252251267e72524b49302577e72524f4b302577e7252302c2521700007e72522e255007e72524530256007e723025120460072524930250067e72524b3025177007e7a72523016600007e635230255
  | 6, 0, 4 => 0x7e7252251204600007e725230165007e72302c250467e72524f302512700007e522512015007e72302504016007e72523730256007252302516006007872524f30256007e72715225126007e52302504016007e7252251c1267e7271523025047007e7252302c16600007e7852302157e72524b3029257
  | 6, 0, 5 => 0x7e7252302516127007e7252302f166007e725230250e67e72524f302c2570072524f4b302567e7252493025017007e726b52251267e72524f302501700007e723016045007e726052251267e72523025170177e7252302a251c700007e723025045007e605230250167e72716052302577e72524b3025167
  | 6, 0, 6 => 0x7e72524830256007e724f3025046007e72523025096007d72523025006007e72523016146007e72302517046007e725240302567e78725230250470072524f3025126007e725225120d6007e72524930166007e72524f301667e7252493730257007e7252493025600007f7230250457e7a72523025167
  | 6, 0, 7 => 0x7e7d725230252470072524f302c256007e524b30250167e787252302a2577e7271524b302570072524f30250167e78726b52302570072523025040067e72524b30251c7007e7252302725600005230250100500007b7252302557e7267524b3025700725230251c00600726a524f30256007e72493025046
  | 6, 0, 8 => 0x7e726b52492560000724f302504500007e7260301c5007e723330250467e725230252404700007e7d4b30255007e52302524016000072524f30255007260523025006007e555230250167e72524f49302577e7d72523025127007e72523016136007e524b302c2567e72524f3025177007e72523330256
  | 6, 0, 9 => 0x7e726052302c2577e7260523025017007e724f4b3025600007e5230250150072524f49302567e7252302c250477e72523025040170072524f3025176007e52302c2501600007e7252302057e727152302c2570078725230250067e7252302c251c77e7252302a252477e725230251c0177e726b523025247
  | 6, 0, 10 => 0x724f4b30255007e524930250167e7271524930257007e524f30250167e7252302517047007e523025170167e72715230251777e7d725249302577e7d7252302517700007e302504015007e72713025046007e7230251c04600007e7252161250072524b30250067e72524947302570000725e5230255
  | 6, 0, 11 => 0x7e7252493025047
  | 7, 0, 0 => 0x7e725230251c67e7d7252302560072524f302557e725249302567e72524f302567e72523025176007e723025045007e725230165007e7252302557e7252302c2567e725230250167e7a7252302567e725230251267e725230252467e72524b302560072523025005
  | 7, 0, 1 => 0x7e726052302567e72523025046007e5230250157e72715230256
  | 8, 0, 0 => 0x7e725230255
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 36
  | 4 => 44
  | 5 => 52
  | 6 => 60
  | 7 => 52
  | 8 => 44
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xff01ffbffc799f8fffffe3c781cff19ff20be1807f01fc003fff
  | 0, 1 => 0x371e6181c3806301061bffff813f1e6003ff87f0f0e003ffc7ff
  | 0, 2 => 0xc01873cbe18cf0f863203e00070e060fc79863f10000e03980
  | 0, 3 => 0x1fc07f07001f800006600000003f3861f8f1f841fc07f
  | 0, 4 => 0x37f07fcdfc07f30d079cc340003000798c001803000600030067
  | 0, 5 => 0xc0e0003000678c00180300060000000000000780000003e3c781
  | 0, 6 => 0x1f80000780000198000000f8f1fe7e3c781f801e03038679
  | 0, 7 => 0xc0e0003038679c00199b00060030d07fcc3407830d079cc00180
  | 0, 8 => 0xf0f0003c007fef0e1fe7c38180f0d1f9fc00780f00060303867f
  | 0, 9 => 0x700000003878000e198000066000e000000000f0f1fffc3c679
  | 0, 10 => 0x7c018403386107fe1fc1fc07f07f00001c387e070e0001c0000
  | 0, 11 => 0x37d079cdf40003700600c339f930de79cc341e7300e600c00180
  | 0, 12 => 0xc0ef9e703b800c0e19e7033e67c00f803000600c000000df79ff
  | 0, 13 => 0xf7e0603dc0780f0effe7c00780c7ef9ff1f8679c7e00031c0600
  | 0, 14 => 0xf8d079fe00066f8c0187e3ff81f8f1e07e03f80f800003dfc7ff
  | 0, 15 => 0xfff1e07ffc000ff0fffbfc3f80ff00003e3bff9f8e19e7e37fe7
  | 1, 0 => 0x3ffc780
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x53f0b554a82915087ead42028103701500014080370150001fab
  | 0, 1 => 0x2d1a418b4690621124197222810c080003de0540c080014fc2d5
  | 0, 2 => 0x50c0b8638b4188e2d0623034088e2d060b469062d18010b02902
  | 0, 3 => 0x7082e8c8dc97623725d885496620024897322e150c0b854fc2f5
  | 0, 4 => 0x73f2fddcfc05471d2f9dc7404471d2f9dc74be77082e8dc74be7
  | 0, 5 => 0xd2e01434b96f9d2e5be74216a9d085aa609947880050a1c742c5
  | 0, 6 => 0xa3775fa8dd47ca1575ba801d2ad2e5be74216a9d085aa74b96f9
  | 0, 7 => 0xf3f0153cb9ffbf1d7fbfc21fabf3f7fffcfd47cf1d7fbfc21fab
  | 0, 8 => 0xf3f0153cfdffff2e7fefcb8bf3f1d7fbfc21fabf082e8fcfdfff
  | 0, 9 => 0xaf78152b9bd7aad5f5bab56966ac0f4aab02000f3f7fffcfd6fd
  | 0, 10 => 0xfff8bd7f33febaf7f5fabde054af78152bdfd7eaf7f5fabdfd7e
  | 0, 11 => 0xfffafdfffe054fffafdffbbffbfddffbff76be7fc8feaff22ba3
  | 0, 12 => 0xfeeffeffbbd7afeedbe7f77feffc8feaff236a9fc88003ffffff
  | 0, 13 => 0xfffafdffffffffeeffeff23fabffffffffff6fdfff8153fff6fd
  | 0, 14 => 0xfddaf9ff76966fcc8b87f23fabfc88a07f23fabfc88003ffffff
  | 0, 15 => 0xfff8b57ffe054ffffffffffffffff8153fbbffbfeedbe7f77fef
  | 1, 0 => 0x3ffffff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 129 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 129 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 129 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 129 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 2 => 6
  | 3 => 47
  | 4 => 232
  | 5 => 716
  | 6 => 359
  | 7 => 4
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0x8f1f12744e9fad494a9f93f62acbb8382628eac408fd8aeb
  | 3, 0 => 0xef5f7392ea82c853e8df4e12ddf9ee75d5de66aed4f9eec0c3df1ec3c3a5051cbff11a8ca10879c29c75fe72989ed5248d6c931386ed54ba7baea6a678bbd0c973dbd1ea721965927167151b6dcb8567697feecc5e28af5c5b82b3f35b1022755812848c554b5e7d54d0e36f521ab2454defc1ad497aca9f489932ea44eca2023bdd38153353d70a2d995d3327c14229272a014b268cca312622aed625362d0e251733c31fa3707d1d092f9719e1265f0ecf6e84082562b702378513
  | 4, 0 => 0x28f053d128d9cf68277867bd26c149bc259e615624f545b821ebfc2d21cf164e1f05add81db8d15e1cdae6e71b29fce01a1c73ec1a0b5a7119f9d90b198d26f71961b745186e520a17959328167e084d1631a7021615720815f5d5b3144c80d113f69a5712b2bd041284b5ca119c521611976697116bad2711063d710f4634e10f36fc710f109b1d0e71c8140e01c8b50dde2b460da14baf0c43e7f80ba04aa00a2665220a245469099b6e14096b80a5095787e0091ddfce0804900207ccfa2907c344ac06c95cf4066db51c05929501051e5cb4048f117d03f6ea780393a516037c5955035d84f402a9d5f601b7fa180179f7b001738fa4016d5ea0013ab333
  | 4, 1 => 0x659b92a263482e48632547a661772eee615087175f26cb7c5e6d3a9d5e566f575e28af5c5d1eeffa5c98d1fa5c4734d15c2a13e95ba1879b59df99de596e6a5c58aea20b58934a41588bb81e585bf13d582939ef579bdeef573bc0d4569c08be55cc5f1955993281539ea2fa537ac9df5347347052b153674f830ea34f7a44914e3e65f24ced50034ca57ebe4aaafef44a69403449ac78c54933b9df48da116b4837844647a034fe46a2701144e6661443f9e44c3e15c9673d3e85e23cdf1ccd3bf0653f3bcce6d53b9f8a6b3a84631a3a4739a839d912983854c98a36b109603556f83934ddc0e0342044b6330ed253329ac7482e2619a72d5b3b112a9b81fe
  | 4, 2 => 0xad680700ac79e26cab970e87ab3ad8ccaa3c7614a4754e1ca3bd37bba25d4f1ca236c8039fee05439de696779c6e0dd09a725de49a38443d9a29ab6799af330798b06496950a416694d4622b938378b8929f892892656f8190dd1cd0908e74e190467f4b902acc598c42350e8a652bb08978b6138857ad79870d8dea86e91f0b8214e98f8163e5448137bf387f4c25df7e9fe6547c3eab067bda84a87b2d4513793043db7920e24e785296f4781c59dc77f5da87740f15bb73f1c7897394e45973949aad73057bef72d2e41071fcb88271e6166470de698370a44fdc706ed20d6e2ab2206dced9736d57d8f76b0293246ad7a7836abfa4ae69be81aa683e81dd
  | 4, 3 => 0xfec1f412facfebe3f7a78259f7251ed3f5377d43f2c7e59cee3a4a60ed152544ea82c853e89ed52be6790a91e61fd99fe268bc5adeb4d1cad6e879f3d658266dd59206d8d5159ecfd21f80b0cf96206bcf53736cccb6cc68cba83a27cb986e2dc6b07012c4bc970ac03207a7bfcc3100bf1e46fdbef4e03fbe058831bdd85cc3ba42f11bb945e173b6adf809b60dda43b56e322baf13f981ae794270add3224e
  | 5, 0 => 0xacd0f9a0ac500080a9ba0730a57f0f809f7497309d4b4e609c916fd0990b12d0951716f09467f9108e92fc908bf4e8408b1a63508756e4d082a79c5082a0d6007b1621107464d1e070d15f206fe158d06cce1d506ae4a8e069e274f068e17f605fa08ac05990cab05929501059191cf058b0db905740e3a055ef6c704ffb19604ebeb4d04e3a01704d7d23c04cdb69a04c27743049b29af046e5753045bec8a0446328b03c2a1f503738f43034a85ef031e26ac03160a4402ce909402b9ad9202a9d5f602a983810216f55102137cfa01ab6f88019cc41b013ab333011ba5c301061cc000ec79c800d9737c00cfb30c00cc5bba00c6c707009ccf9b0067426a
  | 5, 1 => 0x18c1407c18b21a0b188999fe1842c28317cfae35179fcee417649ad4172d4de817258f9c163dc49416188638160a504d15e8d611153baf2f152be9b714ed128b14b587b3147530501462f1df14466b1d13fb348113facbad13ed7a8e13bfb53b1364bfbc1355c83f131973db130405d012dbc52b12ab9fac121d8d8712076044119c5216116bad27115a08c311063d71109bbb0c106e21ec105883811029b94a1019fcde0f2079ff0f04ae660ee5422b0ee0aa7d0ea7e6cf0e889b3a0e619fdd0e57eb050e4fd1d70e01c8b50ddcb7b40d94fd960d3750cd0cc67abf0c4279a60c3634c30c26620f0c19c57d0c082f9e0bd8dc820ba67cb90b3ab0500b2fd943
  | 5, 2 => 0x28e80ba728ac9c1b28706db528702da1281d64f02810bae627ac9c8926f4376a26c149bc2613d41f258bb5b4250a511224e464c323c1983423ac042e238d9d83233bc2302319d16a22f5531222db2e8922ce1dde22c02a602290e596221b473d21ee3fb5216b0cb0210af4e220c158e420926bc920868d35207121dc206b5f811ffe6a711fd2847d1f977a661f6f587c1f1c72471efe2a301ebc8bfb1e8f21ed1e878db91e5fb4491d5caa0c1d2c49ae1ce7d0611cbf76401c92e1de1c85bdea1c539aee1bd633341bce95e41b13e74c1b08d8851aeecc4a1ac2e0181a46e73f19f6acaf19ee1ccb199d72d61993a321195aae8519523c641912a35318e76954
  | 5, 3 => 0x39ad2f36392b6a3a3928f7bd3907f9a0383400c038256e83381d2fc937f235e137a3b05537a2d421376ff3cb36c9bc0c367800d3366eae6a363a106536319a46361b0c29360ef66735a8f43b358a0e8c3556f839351e99413511e16634c7a837349bd35f347ed0dc341dafbf333c0ed432c5b8b432b5493331cca6b731bf9409311a709130f1064f30c81d8430600954304bb9ab301ee3323008318e2fcd45562fae6d2c2f49a9df2f1d2e082efa58e32eb77ad82e07a46d2dd4525b2dc247322d1531922d10cb432c9d048d2c74e1292c5e61a62b9e425c2b7ea3102b079f362ade22742acf02bf2ab208fc2a9a5d9a2a712eb02a5b053a2a2eb07e28ea1c60
  | 5, 4 => 0x4b42eeaf4b30593d4aeacf024a78bd824a2aadc74a0c18a449ec6d23495b8f7a492f8d6848e3a4b848d8d2fa488269614834603f47af2a8047ab61d9479a4e75478ebc2746f5bcab46b4870846ad90ca4664b0d8460a36b545d4d15a44beb5dd44bdf141448a88824476a01844685c454457f99a436f91dd435d627042fe38f242ccd9a742bb83534268b8df42604a3241d1ab7841c5084840e5835040d7ad4e4096950f407688744021954a4004549a3fc52c8b3f5594d63f243c853f1022e93f048f313e4b71323d9deb913d65c92d3cf533d93cb201a03c82eb253c8094d33c77ed433bbbc96f3bac4cf43ba851413b57effe3b31a7993b135f823aef4e56
  | 5, 5 => 0x5db184e45cc9c5655c023d205bf1ec0a5be3c0435ba2d40b5b907ceb5af3f06e5ac7cf815a84b6b95a513c2c5a4586e359fab3eb59aeffce59a0bd635989603558642bf5585e79ed581e85ee57fdf23c574b2e31571817de566500cb564ee7335514323a5489fe9f5437ed855435268d543440c154262b9e541c5b03540fd16f53ebeff753cda7e053abf0e9539ea2fa538e6e1c5360b1be53453add534137d952b15367523ba04351cbc4cd51baf31e516b6a4f50b7e8e150553e1d4fda65554fda4a0c4fd324ba4f622e594e90d3334e316b9a4e1536a04d94c6f24d8c27a04d5962ca4d1283e34cfe1dde4ced50034ca3e64d4c3d3a664c1ef24f4c1d88f8
  | 5, 6 => 0x72ff1fb172b748bb72a28515729c421a7284e78d723e811d71caf1cd713f042a70df1f5370aa985d701175cb6ffe25d36fdc4b726fb0a3756f97d75e6ee40e116ed6e8746eae6fa86e46c5e16e3cc9176d39c0cd6d01f4166ca856216c52f1a46b5a26876b5990676b1a481c6ad7a7836a6ad2826a0bee8069d6c3376982ba48693e79d468e98b5168e33a5968dcff5467cb16c46747c91c66fbe9c166cd0955663adcf765ff5b3e65efbb40658459a0656d11f765008ccd64d5345d6474ad8963d7767663b694ff6363326b62464e7b61b36b2d61a00f6361772eee6091ad175faf5fc85f432ee65f04ae155eedd8685eeaec9a5ed0b8a55ec25e125dfb08a2
  | 5, 7 => 0x8ac0f17d8a272f528a0cecf0895300dc894e1bb7891f50d588a24e2e8857ad79881060f787e40109879722e48782d33b87780edf87010e3f8692aa83868585e184533df1844e1e738434d4c883bf5f938360be948340173783384e93830707f681386adc80f0048c805c81917f6beea57f3e813a7f3ce3f57d9b12da7cec669a7c7c6ade7c006ce17bb14c267b97a2937b7122f57ade295c7a13337d79f743f079b0f4357970f92978c8b30e78a226407843e1c3781c59dc77f3d63477c98559778b010376b0801276a3e4b076814464765f962d760278a57575687a755fc29f75488ae3753439d674f91cf0746bc1f074601d2f740f15bb734e0b197307665d
  | 5, 8 => 0x9f33aac59ea5e9339e8d8ce69e13c0b19e0fdd1d9d8ea5939d639d929be459f89b78fcc79b72e44f9b408df49ae48fb39ae00cb29a5a88ec9a1516ef976423c79733b3bf970e804896e3167e96b991c5965e17b095feee3295ed19b095a9532c959cb0bc95679bee94d008f394c5bd88944d8609943334759432099893e193f192c5e1cb9287517292600d5e9217aca79205447191880dd99166d3a69139dd3f91293f3590e4eebc90b64a7c90a167fe908e74e18f41463d8f1c45148ef538518ef3a2ca8ef11a7f8e25f2268dba560d8db81d188d59ca2d8d3b39228d0b86998cee695e8c98c7288c71e27a8c2119148bed44ee8bc6a0588b692f778b0b234f
  | 5, 9 => 0xc72155e9c5630f78c4bd6242c3c92144c2988c9ec1af24e8c0cf70f9bf180dd3bf06ab04beb50d28be9b9cd6be80b5fdbe058831bd76f3c7bd6b87c2bd4eb3ffbcf4c5bbbc03f926baaa0f08ba226942b9944f4fb84f3357b740556db557db8ab54882a7b4b0acd1b4ae14f4b420bb9cb3cc2c95b2dd4076b2c7967bb23722e8b1d7f8dcb18e2429b0fbbde2b0aa97a5b08d8a84afedb10faecdff4baec462a0ae679f07ae2d3545ae1b257dae09c040ac7e5233abbe883fabaede28ab8d9f4daabb8bcdaa041ec4a7cf36a3a65a6089a5c7ecc3a50a3f0da4cc7a0da33aff9da28acb5ba236c803a15be61ca08cdce0a07d1b949fee05439fad72869f8f2708
  | 5, 10 => 0xed20e00aec2c8e7eec23566dea5c256be9f47e99e93c5e01e89d65fce826034ae69fbf77e60e6a02e578555de4a76394e4861e09e46788e6e449540be3b83bb4e3b6ffbce3a3ec65e37a9266e19c4540dfc6a7d6dfaea3b0df87718bdf21ce54deca08e4debedec9dda01b34dd869cc4dd4b046bdc53b61cdb474c3bda669169d905e112d803fd50d5accb1fd59206d8d571af47d436ddabd3f3822ad3ecaf98d37ddb0ad2e798edd0d96051d08eca1dd04712afd0157adfcfdbb1fecfbf7520cf4203cfcf1340d0cea66725ce95a26cce125e4acd91b689cd48d628cce08f6dcc11aff3cb9736bfcafd92a0ca805506c9cef99fc9a9952fc9163c49c813320c
  | 5, 11 => 0xff7f0773fc7e86b1fba37df0f9e8b2eaf5377d43f515f352f351f261f31b7388f2981293f1a69e73ee59d7a9ed2d5a69
  | 6, 0 => 0x1c0c66611a5524231904fd95186ed5d9185dd0761839c10b178081741642c4f5163dc494160ce25b16001f7a159f0bfb1576532313fb3481129f919d126b5d471215a99f1207604411847165113e3cfa111d1b07105883810fa5a56c0f56e6a30f1c6f950e9e13e60e94b88a0e619fdd0e53dc660db699640d90a6580cc6b0ab0c67ac2a0bdd9e460abbdf0c0a4684f508fc717f0899b16c088fc7ab088b300b0852d32a082658340800153f0773e6eb06def8cc06ae4a8e0686f7be0672c8d505e3c4a805a33fba0547555e04bdd1970494d76e04768f570453760c03d72e4402dfc1ef02ad0a7c02137cfa011ba5c301035c7400bc73fb0096982a003b3f26
  | 6, 1 => 0x3f2614793f048f313eeb2a3e3d16eda13d1259793b57effe3b2f974a3ad55d143a61d32c3a2c8d0d3a22a09e3605749535fe72ab35e946da35d46d0935b11cdf35a8f43b35a19b24352853d1344aa75733dc477633baac8a30f1064f304bb9ab302fa8433006bd36300294d72de596012d6f2f2c2b3ab1752b18b9492a9a5d9a2a634f5d296db94028f61a0c288cce3b28706db52833e87a262f1d3f261d2b8725c8be94258bb5b4255b3deb25241254240c59ec238baec5235a37292319d16a2308457d22c02a60216d3abf216b0cb01ffe6a711f85e4681f7215df1f5ba64a1e82da2b1e3e4eea1e2e547f1dd183cb1d637c901d513d981d4825fa1c16f189
  | 6, 2 => 0x6516550764ebe45f64bf5897638627ed62cabd2a61772eee6146831960e3fa66601d29885efca40f5eedd8685ed7439c5df999d25ddb51bb5db4b7995d2f83a55d190fa35c6f645b5c5618f55b907ceb5b1a703d5b17beeb59737e15590b58d0588cea0d5870e674566500cb552c7e8654ed12ca542e51fb53cda7e053137ba8526c4e8951ffc61251cbc4cd50dcbbab4f645f6c4d8c27a04d8ae2ff4ced50034cadc5cb4c65a89d4c5b7d3f4ae557294aa4293b4a8c9e9648e3a4b848ac91f9483bd70b479a4e75472fc7df46f9483546f6ff7945585ff644daf10f42fe38f24258da234255e94441d8d02141cf53b341c50848402bf95f3fc52c8b3f59186c
  | 6, 3 => 0x93785a1c9375af69932aa89e918568c9917685b99166d3a691633b0b90b64a7c8e58a53e8e25f2268e003f6a8bedd25b8bed44ee8a8a8c238944edf28802311287bebf2a868585e1849940e484830b72829bb51b81d42c9781d2cc888198aade8146bcf4810a05b9807d25ca7f5278507cdb8fe279a0609079897989788c23d677b90a397731b0a976b5fffc761a86aa7502577e74cc1cc274601d2f73416f4073316c317313241a72d25ba172625a3870db07f4705671e46fbf7b3e6f1c93316eae6fa86e208c756da978f46c587e306b58fca96b3122a769a230d0699a528569527b1c68dcff5468d915e968038de267b1ea3066cc1f9065efbb4065a5dce6
  | 6, 4 => 0xcacfc54eca2b946ec9163c49c8cb3a6fc813320cc51e17c7c50c90fec4bc970ac49f19a4c48ba401c43a062dc25cdd32c06708d8bf06ab04bf064230be241afbbcf535bcbc42d39cbc03f926bba7318fbb2d7b77bafac807ba4a3eddb925accfb9003930b8bb6bf7b7a8ffddb51596c5b46ab0c1b3de6349b37785d2b346886eb32c4d8eb11dea32ae299d2fae09c040ad668d2aac9afc57ac7e5233abcf3dd7aa041ec4a675548da6468a79a35cf8229f42bdb09ea5e9339e3fb3739c0d73ae9be459f89981e233992eaef698bafb2e98974c89984264099834b06796e3167e96d07d3d968d3c97964271019574375095679bee95254e0a946d9cbd942379dd
  | 6, 5 => 0xfc7e86b1f8a3307cf88a0803f732424cf65dad62f5b4a1cff3e17068f0890975ef2d2818ee58bd0aed20e00aec11e6d0e9f47e99e6797830e449540be2d3b7c9df93d43fdf381f38debedec9dd4b046bdd077c4edae6cc74d7ab700ed78d27f7d69d2caad5b35c53d4eaf6f7d3fe0bdbd3f3822ad0f09e9dd01463a3cfbf7520cf6e4ee3cf1ebb7ccd91b689cd414f61ccf0ec83ccad09fecc11aff3
  | 7, 0 => 0xe2d3b7c9a35cf8223b57effe0672c8d5
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x210402010004110321040202310842023108420131084201
  | 3, 0 => 0xc410131040201310842010000510300005103414c8204000c41013108420100084102404c8204310842020004110300041103310842023104020100005103000841013108420231040202310842020008410121040201000411033108420231040201414c8200310842023108420100041103414c8204414c820400005103
  | 3, 1 => 0x41103000c410100000000310402010004110300041103000411030004110331040201310842013108420134085200310842023108420200041103
  | 4, 0 => 0x314c42000000510300000004000401010004110300041103000c410100005103000c81043108420100041103000c4102000c41020008410100000003000c410200000001000000060000510310440200000c8104000841010000000000005103000c810434484200000c410200000000000c8104000c81040000000000000003
  | 4, 1 => 0x3108420200000005214842001448020000000006414c8204000c8104340852003408120000000007404c8200000051031044020000000005000000030004010131084201310402020000000000000006000841010000000600000004000c410114480200414c8200314c420000000000000c8105000c4102000c410131084201
  | 4, 2 => 0x414c8200000c8105000c4102414c8200104402000000000400084101304c02000000510300084102000401010000000310440200000c8104410c92000008410100000000000c410100000007000c41010000000600041103340852000000000400084101000c81050004110304484200000c410200000005
  | 4, 3 => 0x21484200000000060448420000000000000c410100000006144802000000000100041103000000060000510300041103304c020000000001000051030000510300084102000c41010000000000000006324c82000000000300000002000000003108420100000001000c41010000000300000006000000020000000334081200
  | 4, 4 => 0x1324c820000000006304c0200310842020000000600000005000000060000000300000004000c4101000c81043108420200084102000c41010000000100041103000c41013408520000000003000000000004110300041103000000060000510300041103000000071448020000000001000c41020000000200040101
  | 4, 5 => 0x5103204802001044020040085200000c410200000000000c410200041103324c82000000000000000007000000070004110300041103000c8104204802000000000000000007000000050008410200040101000401010008410100000000000000030000510300005103000c9100000c4102000000033108420100000007
  | 4, 6 => 0x4110300000000404c8204000c81000004110300040101000411033408120000081100000c41010008510031040201000c8104000000060000000700000003000c4101000000000000000300084101000000010004110340085200000c4101400c9200000c41013108420200000004000000000000000700000004000c8100
  | 4, 7 => 0x6000c8104324c8200000c810000000003104402000000000000000000
  | 5, 0 => 0x3000000060000000300000006000c410200000003000000070000000140085200000000020000000200000005000c81000000000504484200000c4102000000030000e10000000004000000010000000400000006000000030000000200000001000c410200000000000000040000a10000000004000c8105000c4102
  | 5, 1 => 0xc410100000007000000000000000500005103000000030000610000000003410c92000004110300000001000000070000000600000004000000030000a100000c4101000000040000000000000002000051030000000100000003000000040000000700000000000000010000000000000003314c42000000000400000001
  | 5, 2 => 0x50000000200000003000000040000000200000003000c4102000c110000000001000c410200000005000c8105000c8104000000010000000000081100000000010000000300000002000401010000000304484200000000020000e10000000000000000030000000300000000000000050000000400000004
  | 5, 3 => 0x300000003000841010000000100006100000c810400000003000000000000000000000003000c4101000c4101000c81000000000514480200000000020000210040085200000000040000000400000003000841010000a100000000010000000500006100000000010008410200000002000401010008410200000003
  | 5, 4 => 0x300000003000c81040000a100400c9200000000030000000100000000000000060000000400000003000c810400000004000000050000000400041100000c11000000000400084100000c41010000000700000006000000030000000200085100000c4101000000020000000400000007000000030000000200040101
  | 5, 5 => 0x8410100000002000c410000005103000000030000000300000005000c41010000000100000001000000020004110300005103340852000000000100000007000000010000000000000006324c820000000005000000030000000300000003000c810400000002000000010000000300000000000000040008410100000003
  | 5, 6 => 0x2000c510000000002000000000000000300000003000c410100000001000000050000000500000006000c4100000000070000000400005103000000020000000100000004000c110000000001000000030000000300000003000000010000000200000003000000060000610000041103410c92000008410200000004
  | 5, 7 => 0xc41010000000100005103000000040000000200084101324c82000000000500000000000021000000000400000003000000020000000100000004000c4101000000030000000300000003000000010000000300000003000c410200000002000000040000000200000005000c110000000004000000070000000500000003
  | 5, 8 => 0xe100400c9200000000072048020000084102000c410000000000000000030000000700002100000c810400000003000000010000000100006100000c81040000e10000000003000c4101000c8100000c41020000000500000000000000030000000400000001000000060000000600000000340812000000000300000006
  | 5, 9 => 0x20000a10000000005000000050000000110440200000061000000000600000000000c8100000c41050000000100040101314c420000000003000c41010000a100000c810000041103000000010000000300005103000411000000000500000007000c4101324c82000000000500000004000000030000000500000001
  | 5, 10 => 0x400852000000000300000002000000030000e10000000003000000020000210000000002000c8104000021000000000500000000000c41010000000100000001000000030000000200000001000c81040000000100000006000c8100000000020000000300084102000000030000000000000001044842000000000200000000
  | 5, 11 => 0x2000000031044020000084100000401000000000400000005000000030000000300085100000000030000000300000006000c8104000000040000000300000003000000020000000500000006000000010008410200084100000c4100000c41014108120000000001000000050000000400000001000c410234081200
  | 5, 12 => 0x30000000300000001000000020000210000000001000000030000000100000001204802000000000300000002000c1100000000000000000000000003000000020004110000000003000061000000000100000001000000000000000500000002000c410200000005000000040000000734081200000000040000a100
  | 5, 13 => 0x30000000300000007000c41010000a10000000003104402000000000300000001000000020000e1000000000004484200000000060000000100000001000c81040004010000000003000000060000000414480200000000010000000300000003000c8100000000050000000100000004000000070000000500000002
  | 5, 14 => 0x4000000050000000634085200000c410200000001000000030000000300000002000c41002148420000000003000c01000000000500000006000c8100400852000000e1000000000300005100000000030000000200000003000c41010000000000000002000c9100000000030000000000000003000c810500000003
  | 5, 15 => 0x2000000050000000100000004000c81040000000100000000000000030000000200000005000c810000000003000000000000000300000007000c11000000000600002100000000060000000500000000000000000004010000000006000000040000e10000000002000000000000000100000004000c410200041103
  | 5, 16 => 0xc410100000001410c920000000007000c8104000000040000000000000003000000040000000300000004324c82000000000000000005000000010000000200000002000000030000000000000004000c81000000000100000004000c810000005103000000010000e1000000000100000002340852000000000400041100
  | 5, 17 => 0xa100000000010000000321484200304c020000002100000841020000000510440200000000030000000300000005000000040000000200084100000000060000000400000004000000030008410200000005000c41010000000200000005000000030000000300000000000c4102000000050000000100000001304c0200
  | 5, 18 => 0x30000000600000003000c8100000000070000000100000000414c82000000000100041100000c81040000000300041100000c4101000000020000000000000002000811000000000400040100000c8104000000010000000500040101000000010000000320480200000c410200000003000000000000000100000005
  | 5, 19 => 0x5000000030000000100000004000c4101000c41010000000710440200000c91000000000100000000000021000000000100000002000c8104000000020000a100000000010000000100041100000c4100000000010000000600000005000801000000000100000007000000030000510300040102000c810500000006
  | 5, 20 => 0x30000a100000000030000000300084102000000060000000100000003000c41020000000300000000000c81040000000000000006000c41010000a100000c81050000000300000001000000020000000200000000000000000004010200000003000c81000000e1000008110000000005000000030000000000080100
  | 5, 21 => 0x400000003000c81040000000300000002000c8104000000030000000000000003000000000000000300000004000c4101000000000000a10000000002000c810400000000000000010000000400000001000000030000e100000c4101000811000000000300000000304c020000081100000c81040000000300000004
  | 5, 22 => 0x500000003000000010000000100000003000c8100000c8104000c810500000000000c41010004010100000006
  | 6, 0 => 0x411000000000100000005000000000000000300000001000000050000000200000006000000020000000400000001000000060000000400000003000000000000000200000001000c9100000000030004010000000002000c8100000000020000000000000000000000010000000200000002000c01000000000400081100
  | 6, 1 => 0x500006100000061000000000300006100000000030000a1000000000200000004000000000000a10000000002000c91000000000300000000000000050000000400000003000000000000e100000000020000000400000002000000000000000400000002000000000000000000080100000000020000000400002100
  | 6, 2 => 0x8410000000001000851000000610000000002000401000000a10000000000000000020000000200000000000000060000000000081100000021000000000000000004000000030000e10000000003000000030000000000000002000c51000008010000000003000000000000000100000001000000010000000200000005
  | 6, 3 => 0x300000004000000030000000400000000000000000000000400000000000000030000000300000000000000010000000300000000000000000000000300000003000c0100000000040000000100000004000811000000000400000003000c41000004110000000005000000000000e100000000040000000300000002
  | 6, 4 => 0xc1100000000050000000100000003000000020000000100000000000000010000a10000000002000000030000e100000000000000000500000002000000040000000500000002000021000000a1000000000300000001000000010000000200000002000000030000000000000002000000020000000100000004
  | 6, 5 => 0x20004110000000001000000020000000000000000000c91000000e1000000000300000000000000040000000500080100000000030000000200000003000401000000000300000005000000050000000400000004000000000000000000000000000000010000000200000000000c9100000000020000000300000000
  | 6, 6 => 0x4000c51000000000100000005000000010000000500000000000000020008110000000003000061000000000300006100000000050000000100000003000000010000000200000004000c810000000002000000040000000100000002000000020000000200000003000061000000000100000002000000030000a100
  | 6, 7 => 0xc0100000000040000000300000001000c11000000000000000001000000040000000000000000000000030000000600000002000000000000a100000000030000000200000005000000000000e1000000000000000001000000010008010000000005000061000000000200000004000000010000000400000000000c9100
  | 6, 8 => 0x3000000040000000000000003000000020000000600000005000c81000000000500000003000000030000000000000000000000010000000100000000000000050000210000000000000000030000000400000001000c41000000000300081100000c8100000000050000e10000000003000000000000000200000001
  | 6, 9 => 0x400000000000000020000000100040100000000050000000000000004000000040000000300000001000000010000000300000001000000010008010000000004000000020000000400000004000411000000000600000000000000000000a10000000000000c11000000a100000000040000000100000001
  | 6, 10 => 0x3000000040000000500000002000000030000000300000000000000040000000400000003000000030000000100040100000c4100000000020000e100000000020000e100000c110000000001000000030000000300000003000c8100000000040000000000000001000411000000000100000003
  | 6, 11 => 0x3000000030000e1000000000300000000000000010000a100
  | 7, 0 => 0x0
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_19 roots_19 6 s ws hint
  | 1 => checkCutEntry dom_20 roots_20 5 s ws hint
  | 2 => checkCutEntry dom_21 roots_21 5 s ws hint
  | 3 => checkCutEntry dom_12 roots_12 5 s ws hint
  | 4 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 5 => checkCutEntry dom_24 roots_24 5 s ws hint
  | 6 => checkCutEntry dom_25 roots_25 4 s ws hint
  | 7 => checkCutEntry dom_26 roots_26 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_27 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_26 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_27 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_27 == dom_27) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_27 goalM u ys) : RunD dom_27 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_27 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 8 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_8 : ∀ i, 8 ≤ i → i < 16 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_16 : ∀ i, 16 ≤ i → i < 20 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 4 16 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 20 → Z 3 i = true := range_split z3_0 (range_split z3_8 (z3_16))
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
theorem z4_32 : ∀ i, 32 ≤ i → i < 40 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_40 : ∀ i, 40 ≤ i → i < 48 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_48 : ∀ i, 48 ≤ i → i < 56 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_56 : ∀ i, 56 ≤ i → i < 64 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_64 : ∀ i, 64 ≤ i → i < 72 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_72 : ∀ i, 72 ≤ i → i < 77 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 72 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 77 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (range_split z4_48 (range_split z4_56 (range_split z4_64 (z4_72)))))))))
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
theorem z5_160 : ∀ i, 160 ≤ i → i < 168 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_168 : ∀ i, 168 ≤ i → i < 176 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_176 : ∀ i, 176 ≤ i → i < 184 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_184 : ∀ i, 184 ≤ i → i < 192 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_192 : ∀ i, 192 ≤ i → i < 200 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_200 : ∀ i, 200 ≤ i → i < 208 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_208 : ∀ i, 208 ≤ i → i < 216 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_216 : ∀ i, 216 ≤ i → i < 224 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_224 : ∀ i, 224 ≤ i → i < 232 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_232 : ∀ i, 232 ≤ i → i < 235 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 232 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 235 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (range_split z5_200 (range_split z5_208 (range_split z5_216 (range_split z5_224 (z5_232)))))))))))))))))))))))))))))
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
theorem z6_176 : ∀ i, 176 ≤ i → i < 177 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 176 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 177 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (z6_176))))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_8 : ∀ i, 8 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_16 : ∀ i, 16 ≤ i → i < 20 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 16 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 20 → Z 7 i = true := range_split z7_0 (range_split z7_8 (z7_16))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := z8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
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
def RootG (s : Nat) : Bool :=
  scr dom_27 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_27 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_27 roots_27 goal_27 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_27 goal_27 := by
    have h0 : isConstB dom_27 goal_27 = false := by decide +kernel
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

end S_27

theorem low_27 : Lower dom_27 roots_27 goal_27 9 := S_27.noCircuit

def dom_28 : Nat := 0xcccccccccccccccc
def goal_28 : Nat := 0xcc80c800c8800000
def roots_28 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

theorem low_28 : Lower dom_28 roots_28 goal_28 9 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27

def dom_29 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_29 : Nat := 0xf080e000e0800000
def roots_29 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

theorem low_29 : Lower dom_29 roots_29 goal_29 9 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_28

def dom_30 : Nat := 0xffff0000
def goal_30 : Nat := 0xe8800000
def roots_30 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]

theorem low_30 : Lower dom_30 roots_30 goal_30 7 :=
  lower_iso [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_31 : Nat := 0xffff000000000000
def goal_31 : Nat := 0xfe80000000000000
def roots_31 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]

theorem low_31 : Lower dom_31 roots_31 goal_31 6 :=
  lower_iso [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19

def dom_32 : Nat := 0x5555000055550000
def goal_32 : Nat := 0x5400000040000000
def roots_32 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]

theorem low_32 : Lower dom_32 roots_32 goal_32 5 :=
  lower_iso [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20

def dom_33 : Nat := 0x3333000033330000
def goal_33 : Nat := 0x3200000020000000
def roots_33 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]

theorem low_33 : Lower dom_33 roots_33 goal_33 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16

def dom_34 : Nat := 0xcccc0000cccc0000
def goal_34 : Nat := 0xcc800000c8800000
def roots_34 : List Nat := [0x8888000088880000, 0xc0c00000c0c00000, 0xcc000000cc000000, 0xcccc000000000000]

theorem low_34 : Lower dom_34 roots_34 goal_34 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23

def dom_35 : Nat := 0xf0f00000f0f0000
def goal_35 : Nat := 0xe00000008000000
def roots_35 : List Nat := [0xa0a00000a0a0000, 0xc0c00000c0c0000, 0xf0000000f000000, 0xf0f000000000000]

theorem low_35 : Lower dom_35 roots_35 goal_35 5 :=
  lower_iso [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16

def dom_36 : Nat := 0xf0f00000f0f00000
def goal_36 : Nat := 0xf0800000e0800000
def roots_36 : List Nat := [0xa0a00000a0a00000, 0xc0c00000c0c00000, 0xf0000000f0000000, 0xf0f0000000000000]

theorem low_36 : Lower dom_36 roots_36 goal_36 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34

def dom_37 : Nat := 0xffff0000ffff0000
def goal_37 : Nat := 0xfe800000e8800000
def roots_37 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

namespace S_37
def pairsG : List (Nat × Nat) := [(19, 23), (19, 27), (21, 23), (21, 29), (22, 23), (22, 30), (25, 27), (25, 29), (25, 57), (26, 27), (26, 30), (26, 58), (28, 29), (28, 30), (28, 60), (49, 57), (50, 58), (51, 55), (51, 59), (52, 60), (53, 55), (53, 61), (54, 55), (54, 62), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [19, 19, 21, 21, 22, 22, 25, 25, 25, 26, 26, 26, 28, 28, 28, 49, 50, 51, 51, 52, 53, 53, 54, 54, 56, 56, 56]
def r2sG : List Nat := [23, 27, 23, 29, 23, 30, 27, 29, 57, 27, 30, 58, 29, 30, 60, 57, 58, 55, 59, 60, 55, 61, 55, 62, 57, 58, 60]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_37.map (· &&& dom_37)
def goalM : Nat := goal_37 &&& dom_37
def NN : Nat → Nat
  | 5 => 3
  | 6 => 8
  | 7 => 4
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xe525037666839de73f5da556
  | 6, 0 => 0x3ccad0901d2ad69c1c062c9f1055f87d0b56512e08c2a11101e0734e00fd4581
  | 7, 0 => 0x301879e728531e57204c65761b7e4038
  | 8, 0 => 0x73240d52
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccc0000cccc0000c0c00000c0c00000aaaa0000aaaa0000a0a00000a0a000008888000088880000555500005555000033330000333300000f0f00000f0f0000
  | 0, 1 => 0xffff000000000000ff000000ff000000fcfc0000fcfc0000fafa0000fafa0000f0f00000f0f00000eeee0000eeee0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xdc21050dcb625dc98306
  | 6, 0, 0 => 0xdc7205dc9754170dca95160dc954160dc97206dcb9752700dcb655dc975217
  | 7, 0, 0 => 0xdcb9756dc97516dc976560dc9515
  | 8, 0, 0 => 0xdc9755
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 28
  | 6 => 32
  | 7 => 28
  | 8 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x18e1c6630000c01b40e7830000c00c0007f25f8c39c78e67078fc3
  | 0, 1 => 0x3ffc0007007fc01fefc7e3fbc7fc7c381e0f78fff
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x5ae5cee34890d4bb49ef872109d0ac04afa25b0829468c43058b42
  | 0, 1 => 0x3ffe4807adffeadfefdff7fbdffe7d3a5ebf7bfff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 27 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 27 (i % 8)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 2
  | 5 => 45
  | 6 => 120
  | 7 => 12
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x73240d5201e0734e
  | 5, 0 => 0xd2960a57cc5eb6b0b783de33ab693e8aa81a96fa9c3935f4976c2eba949c1d5788e6a575881df7ef7cf5b0347c9980f174fc42fa73240d5268541b14630203ff5c1c033e5a36a82259aebbbb5855613b576d9bc756adb5b5558e505e4def2fa0375c57e6301879e728531e5727b61500254887a9213150a6204c65761debf7eb1b7e403816d667e51318383012dd14da0c3fa45f0b9fece809ef4726074913f203d77e8403b571ca0174528100adb09200944e46
  | 6, 0 => 0x3abaee83396ed09e38b15ca03818513f3789c4d5348256ef327a08f930a0664e304aef6a2e3c25d82bac9c7629736cbe28f04ee3285b394e28531e57283d5d722794236026bfc75d22b20da2229cc97d2293e56f224370ac216c343820d451dd20d2612a20c4902620bd7dc21d401ac11c83cb851bef588419e61d65164c77de15c7eb5e15241dbb152101c61510e91714d3c203144bd59c13da3c1613524faf1341b86813254e1a0fe0dd7c0eb5516d0e89a7e30e47c4720e3abfa30e35e9430db35b390d19c9400c72252e0ad4f5aa08f5169407831912074b22ba0667a3c2030f9a1a02e6424c02d7d8a2029dfbe0011289a600ce10f000944e4600296281
  | 6, 1 => 0xfa2a3f79d82eea3bbf32c9a4b283b3aea87ccef4a752979da2457b4d9eb1d9259b05731992d1d3e98fdab7658d21f1ff8906cb8e868d67d484074a347f1810627ec80c447e015b977c2736397a6db96f76c15363751b188873240d5272f56e27706e26236dded0c46a82e1f46a38ff166883b1fe64c2abd85f2699575c1c033e5ae7ec205665ae6453f0243153808e425280458e52390f884ea72b044db731474ced4a414c6abc37480aa853478fcca2474d988c437ee34942b8415a4251030441555cde4153e1ea40f4eed23e49de4f3e3a58463e2a3d1b3ca77fc73c57ea13
  | 7, 0 => 0xeddd1af5c998fb3f8f2f91ef7395259e73240d524de0891543d9a45b3da250b42868627c195e30fe18dba2f405dfb75b
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x21484200
  | 5, 0 => 0x214842001044020100000003000000040000000421484201204802000000610200000004000000060000000300085100000061002148420121484200104402000008410021484200000061000000000610440201008062001044020110440201214842000080a200000000050000a102204802012048020000000006
  | 5, 1 => 0x21484200214842000080a20100000003214842000000000300000004214842000000000500000003000000032148420110440200
  | 6, 0 => 0x500000007000411010000a1000008110100081101000811000000000000005100000041010000a1000000000500041101000000040000a1010008010000080101000411010004110000085100000021000000000700084100000811000000610000006101000000000000810000002100000851000000000600040100
  | 6, 1 => 0x60000a1000008010000005101000061000000210100080100000000080000000000002101000000010000a101000811000008410000006100000000070000a10000000004000041000000000500040100000000050000a10100000007000000030000a100000481010008010000002100000061010008110000002100
  | 6, 2 => 0x610000040101000021000000a101000000030008410100041100000000030000a101000000030000210100085100000021010000a10000000001000061010000a1000000a1010000000600000005000000040008010100080100000061000000a10000006101000021000000000500000003000811000008110000084100
  | 6, 3 => 0x30000a10100000004000021000000210000000005000021000000000200084101000411010000610100006100000000050008510100080100000811010000610100002100000000060004010100084101000000040000000000000001
  | 7, 0 => 0x10000000100000000000000010000000000000000000000000000000000000000000000000000000100000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 8 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_9 roots_9 7 s ws hint
  | 1 => checkCutEntry dom_30 roots_30 7 s ws hint
  | 2 => checkCutEntry dom_31 roots_31 6 s ws hint
  | 3 => checkCutEntry dom_32 roots_32 5 s ws hint
  | 4 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 5 => checkCutEntry dom_33 roots_33 5 s ws hint
  | 6 => checkCutEntry dom_34 roots_34 5 s ws hint
  | 7 => checkCutEntry dom_35 roots_35 5 s ws hint
  | 8 => checkCutEntry dom_36 roots_36 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_37 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_33 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_35 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_36 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_37 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_37 == dom_37) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_37 goalM u ys) : RunD dom_37 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_37 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := z6_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := z7_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := z8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
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
def RootG (s : Nat) : Bool :=
  scr dom_37 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_37 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_37 roots_37 goal_37 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_37 goal_37 := by
    have h0 : isConstB dom_37 goal_37 = false := by decide +kernel
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

end S_37

theorem low_37 : Lower dom_37 roots_37 goal_37 9 := S_37.noCircuit

def dom_38 : Nat := 0xcccccccc00000000
def goal_38 : Nat := 0xcc80c80000000000
def roots_38 : List Nat := [0x8888888800000000, 0xc0c0c0c000000000, 0xcc00cc0000000000, 0xcccc000000000000]

theorem low_38 : Lower dom_38 roots_38 goal_38 6 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31

def dom_39 : Nat := 0xf0f0f0f000000000
def goal_39 : Nat := 0xf080e00000000000
def roots_39 : List Nat := [0xa0a0a0a000000000, 0xc0c0c0c000000000, 0xf000f00000000000, 0xf0f0000000000000]

theorem low_39 : Lower dom_39 roots_39 goal_39 6 :=
  lower_iso [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31

def dom_40 : Nat := 0x5555555500000000
def goal_40 : Nat := 0x5400400000000000
def roots_40 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_40 : Lower dom_40 roots_40 goal_40 5 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_32

def dom_41 : Nat := 0x3333333300000000
def goal_41 : Nat := 0x3200200000000000
def roots_41 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]

theorem low_41 : Lower dom_41 roots_41 goal_41 5 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_33

def dom_42 : Nat := 0xffffffff00000000
def goal_42 : Nat := 0xfe80e80000000000
def roots_42 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

namespace S_42
def pairsG : List (Nat × Nat) := [(35, 43), (37, 45), (38, 46), (39, 47), (39, 55), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (49, 57), (50, 58), (51, 55), (51, 59), (52, 60), (53, 55), (53, 61), (54, 55), (54, 62), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [35, 37, 38, 39, 39, 41, 41, 41, 42, 42, 42, 44, 44, 44, 49, 50, 51, 51, 52, 53, 53, 54, 54, 56, 56, 56]
def r2sG : List Nat := [43, 45, 46, 47, 55, 43, 45, 57, 43, 46, 58, 45, 46, 60, 57, 58, 55, 59, 60, 55, 61, 55, 62, 57, 58, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_42.map (· &&& dom_42)
def goalM : Nat := goal_42 &&& dom_42
def NN : Nat → Nat
  | 5 => 2
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x60ce17dc058ff9a4
  | 6, 0 => 0x35fa7d041ef7b69b0467640c
  | 7, 0 => 0x608578e91dcf2103
  | 8, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000cccccccc00000000c0c0c0c000000000aaaaaaaa00000000888888880000000055555555000000000f0f0f0f000000000000ffff00000000
  | 0, 1 => 0xffff000000000000ff00ff0000000000f8f8888800000000f0f0f0f000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xba986460a62105
  | 6, 0, 0 => 0xba8764370a86540600ba6215
  | 7, 0, 0 => 0xa86405ba86546
  | 8, 0, 0 => 0xba8645
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 28
  | 6 => 32
  | 7 => 28
  | 8 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1f0000063871d18000701b40fb00c0067e4bf04e0f1f84003fff
  | 0, 1 => 0xfff0003803fe01fc00647c381e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x9f480416b973d1a44870bb49fb0ac04e744b60460b1684001b6f
  | 0, 1 => 0xfff9243d6ffef9fc84e67d3a5e
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 12 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 1
  | 5 => 8
  | 6 => 38
  | 7 => 7
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x5f5ce351
  | 5, 0 => 0x608578e95f5ce3515735041f24c7012b1dcf21030c5846380b4eb19008ee31b8
  | 6, 0 => 0x690e50d55f5ce3513ae001033a877c60349c41e6334233843086aa872f5e14ef2a4c3eff291c676f28ce4bfb27acaab82657f8ef24d6aca224aba37a239e6b932297e2ba2178948620d1fe5e1e40394f1d5292a719eda9ec11f8cee70e30e5fa0ca90ca40c1925be0b41f5480ab9b6e00a92351109f2619b08dd3df107092c83065bfbac05afc61b058a965604f034f102f89cc302ef34af
  | 7, 0 => 0xcbba9a7667e5bb3d5f5ce351531e2a992f5e14ef273b926c059706fd
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0xe10000000000000401010180e20000084100000000050000000400006103
  | 6, 0 => 0xe102000061000008c100000000030000000100000003000841000000610000002101000061000000000300000005000c01020000000300080100000000000000e100000000020000a100000c4100000c0102000c41000008410000000006000021000004010000000003000c01030000000200002101000c010000000006
  | 6, 1 => 0xe100000000000000000500000002000c4100000c4100
  | 7, 0 => 0x20000000300000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_10 roots_10 7 s ws hint
  | 1 => checkCutEntry dom_19 roots_19 6 s ws hint
  | 2 => checkCutEntry dom_38 roots_38 6 s ws hint
  | 3 => checkCutEntry dom_39 roots_39 6 s ws hint
  | 4 => checkCutEntry dom_31 roots_31 6 s ws hint
  | 5 => checkCutEntry dom_40 roots_40 5 s ws hint
  | 6 => checkCutEntry dom_41 roots_41 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_42 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_38 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_41 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_42 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_42 == dom_42) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_42 goalM u ys) : RunD dom_42 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_42 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := z6_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := z7_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := z8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
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
def RootG (s : Nat) : Bool :=
  scr dom_42 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_42 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_42 roots_42 goal_42 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_42 goal_42 := by
    have h0 : isConstB dom_42 goal_42 = false := by decide +kernel
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

end S_42

theorem low_42 : Lower dom_42 roots_42 goal_42 9 := S_42.noCircuit

def dom_43 : Nat := 0x5555555555555555
def goal_43 : Nat := 0x5400400040000000
def roots_43 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_43 : Lower dom_43 roots_43 goal_43 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5500550055005500, 22, 30)] (by decide +kernel) (by decide +kernel) low_4

def dom_44 : Nat := 0x3333333333333333
def goal_44 : Nat := 0x3200200020000000
def roots_44 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_44 : Lower dom_44 roots_44 goal_44 8 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43

def dom_45 : Nat := 0xf0f0f0f0f0f0f0f
def goal_45 : Nat := 0xe00080008000000
def roots_45 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_45 : Lower dom_45 roots_45 goal_45 8 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_44

def dom_46 : Nat := 0xffffffff
def goal_46 : Nat := 0xe8800000
def roots_46 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_46 : Lower dom_46 roots_46 goal_46 8 :=
  lower_iso [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xe80000000000
def roots_47 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_47 : Lower dom_47 roots_47 goal_47 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff00, 35, 43)] (by decide +kernel) (by decide +kernel) low_16

def dom_48 : Nat := 0xffffffffffffffff
def goal_48 : Nat := 0xfe80e800e8800000
def roots_48 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_48
def pairsG : List (Nat × Nat) := [(7, 23), (11, 27), (11, 43), (13, 29), (13, 45), (14, 30), (14, 46), (15, 31), (15, 47), (19, 23), (19, 27), (21, 23), (21, 29), (22, 23), (22, 30), (25, 27), (25, 29), (25, 57), (26, 27), (26, 30), (26, 58), (28, 29), (28, 30), (28, 60), (35, 43), (37, 45), (38, 46), (39, 47), (39, 55), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (49, 57), (50, 58), (51, 55), (51, 59), (52, 60), (53, 55), (53, 61), (54, 55), (54, 62), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [7, 11, 11, 13, 13, 14, 14, 15, 15, 19, 19, 21, 21, 22, 22, 25, 25, 25, 26, 26, 26, 28, 28, 28, 35, 37, 38, 39, 39, 41, 41, 41, 42, 42, 42, 44, 44, 44, 49, 50, 51, 51, 52, 53, 53, 54, 54, 56, 56, 56]
def r2sG : List Nat := [23, 27, 43, 29, 45, 30, 46, 31, 47, 23, 27, 23, 29, 23, 30, 27, 29, 57, 27, 30, 58, 29, 30, 60, 43, 45, 46, 47, 55, 43, 45, 57, 43, 46, 58, 45, 46, 60, 57, 58, 55, 59, 60, 55, 61, 55, 62, 57, 58, 60]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_48.map (· &&& dom_48)
def goalM : Nat := goal_48 &&& dom_48
def NN : Nat → Nat
  | 6 => 1
  | 7 => 23
  | 8 => 20
  | 9 => 16
  | 10 => 7
  | 11 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0x2319aad0
  | 7, 0 => 0xae56be977f5c71ba7d4487457bf75610734bd99468f32a9c5c1ed0593c43db2332046c8431bb9c8c2d9e553823114efe1c95caf3167f551b126f631c0aabb46709511d2908f317a508b46f7106ba665e06a75e0e06165d76038dd524
  | 8, 0 => 0x73437dc26cc7f9b75ef408b657d7607c56488c3a49bb2fc346a8c7ac45a7f5983a4fc20631fc10b230555efc29af2b64284514cc1980bc2914b84f321358f629115cdc520aad79ad060e01a404608888
  | 9, 0 => 0x99ed5e87668c477058a5f177564030684b7591cb3899ed18342cdee92cb7e2692b81626d28a4a83e23fe6fae1b52f332135211a20f8898390cabde0a0b41c772
  | 10, 0 => 0xf2854adf7cea112d5fbac6fd1e7359ed1729918f1142fa410e7e1513
  | 11, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x15153f3f15153f3f151515153f3f3f3f131313135f5f5f5f0f0f0f0f0f0f0f0f030333330f0fffff0000ffff0000ffff00003f3f3f3f3f3f00000000ffffffff
  | 0, 1 => 0xaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaa808080808080aaaa0000aaaa0000a0a0a0a0a0a0a0a0888888888888888855555555555555553333333333333333
  | 0, 2 => 0xeaeaeaeac0c0c0c0eaeac0c0eaeac0c0eaeac0c000000000cccccccccccccccccccccccc00000000cccc0000cccc0000c8c88888c0c00000c0c0c0c0c0c0c0c0
  | 0, 3 => 0xfcfcccccf0f00000fafaaaaaf0f00000f8f8f8f888888888f8f8000088880000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f00000f0f00000eeeeccccaaaa0000
  | 0, 4 => 0xffffffff00000000ffffc0c0c0c0c0c0ffff0000ffff0000ffff000000000000ff00ff00ff00ff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x8092040806
  | 7, 0, 0 => 0x92281b5d43c680248a1809204702481d6d43c2792281b5943c780206d4409080702281b5943c0792281e6d444f80248e281b50979238a06d43c180248a079b3c8700081b248080692281f6d43c380248a06d43c170248a06d43c370008a024810060248a06d43c77
  | 7, 0, 1 => 0x2280f30810079238a06d43cd892281b59550f802480f3881027000920248102692281d71b50f80248a06d43c57
  | 8, 0, 0 => 0x92280920460206d43ca08070248e281b50f700092050910260008a03c810069228606d440989206d44cf2c280008143c4080602481b68f202702281448f10070248a075b50f792281b64f38880248a06d850f70248a06d9248702281b51024070248a18142447
  | 8, 0, 1 => 0x2481b51024270248a06d650f70248a03ce20478a06d448f2c08
  | 9, 0, 0 => 0x2481b50f282702281b50f30079228606d43ca80248a06d4409792281b6543ca80248a18143c4702481b50f382702281b50f28070009206d42426000922814244692281b5123ce80248a06d4489792281b5133cb800081b50f08060008a050f10060248a06da3c87
  | 10, 0, 0 => 0x8a06d43c0692281b50f29c09206d43c269228606d43de48a06d43ce792281b6543dc092281b5096
  | 11, 0, 0 => 0x92281b50f6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 40
  | 7 => 52
  | 8 => 52
  | 9 => 52
  | 10 => 46
  | 11 => 40
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe12ff8ff0007b84bf00ff9e1ee11e383ff999b83c7e11f8606e01e3887e1ffc003fff0001ff000ff8ffe7878000000ffffff
  | 0, 1 => 0x6d03ec0e7e7c1b40fb00000006d00600006041b4000039e000600068006664030019000787f92fc13f181839c78e2e39818
  | 0, 2 => 0x1ed03fc0187847b401c03ffe11ed007000000063871d1c67e718e1c740000006380001c660018c006401800060001c0061e1
  | 0, 3 => 0x1fe1c7781e0007f40fbe078001fce07c001e1c7f00000006001f0e07b81e7e47c381e0000001f0000381e0007bc71d039e00
  | 0, 4 => 0x3ffffff000000fff0070018787ffc000fffe00fff0000000003803fe0ff81fe
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xc12b58e40005304a400b5940aa1182033b108982c5a116840620123081a1048001b6f000154000258c9650780000006dfeab
  | 0, 1 => 0x2ed27ec9efe7cbb49fb0201142ed026008ae04bb409027be8b0e4216884ee642b013904af87d12d8136101829468c2a31018
  | 0, 2 => 0x3ed6ffd29afd4fb529c6fffeb3ed4a700805016b973d5cefe75ae5cf44005116b84105ceea31ac04e521ae9469121c486be1
  | 0, 3 => 0xdfedcf7e5efb6ff69fbeb7bbd9fcedfe12bf5e7f201084ae839f4e97ba5efe67d3a5e8001509f48043a5eaa5fbd7bd37bfcf
  | 0, 4 => 0x3ffffff920154fffda7369af87ffe490fffeabfff9242480003d6ffefffd5fe
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 50 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 50 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 37 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 37 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 37 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 37 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 1
  | 6 => 66
  | 7 => 472
  | 8 => 817
  | 9 => 226
  | 10 => 17
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0x42b779a3
  | 6, 0 => 0xc375181cc2fd9798bbe1417aa96c4fd49641ed22954e9cc684ae062482a620f8803e71767684b2746e4b8ccf6e3c4fa26cc7f9b7667cd77f6669cf2f635046455dc2a2ea5d9bb90059822a7856488c3a53e4482852b5b82251a7331b510a33e24d6ebfe3472bf16d46a8c7ac45a7f59843c24f8242b779a33f4e216c3e293de83a4fc20637dd4b7e371278343603fb65350d0fa4329c50032fb10f502da27f692d3ea43129af2b6428bb3ee023546a5b222d47871f72254f1d7876211cf9a55a1ae253941649475514b84f32139985b8120104ac11f46327115cdc520e9d2e700da1f86209cc5295077fcd3e05827516040b5776028418e4026a857402678903
  | 6, 1 => 0xd6592383d30e4ab5
  | 7, 0 => 0x9ca8ffa096e94380949cbc50907ecb908f31a7e08db42a408d7695b08823c9f07dea5a907da90b907ae638a07a3d82307923f59075c38fb0752abcf074c40f10747af45073f257c07362e13072446ef0723b01306f5893006d5cca306cd9ad406cc726706aadd100642876806292576060724fb05f89cb505f2790c05f0e4fd056f32720523d98204e7ea7004b41dcb04a8420e0465dd3f044f31b00442bd8603d84ab903d402d8039863440363bb940361340f02abb21b027bbd1202796fc10270867d02305bab022c2378019dffce0194f39b016603570152a31000fcaef300f748a900f5a3d200eed01400bbc0690085f539008479e000381a40000275a2
  | 7, 1 => 0x13ba2914138c619413669e45135211a2132c545912ee7a2c12ed828f12e0ef8a12c74bc212c46f3912a5110412925de612758e8e126213e9122e0035119e9421111d5cf5107b16de10449d861028558e0ff6fb5a0feb19eb0fe69dbd0fd3d9d00f8898390f442f330f441eeb0f15f0690ee619670ec1d9f20e75a33d0e74347b0e56e4950e0a82d30dc879c40d9e5caf0d995fd20d1a412b0cfaa80e0cecc92f0cd360560ccce2ae0cabde0a0c47ad120c0192bd0bb7fcd30bb7a3730b7b853d0b779d3f0b76dfb80b62a4e10b41c7720b1e24e60b16ce990b01dafd0ae9194f0abee8dd0a9cef640a8092520a414e520a3d884a0a22c95c0a1d8aeb09fb8673
  | 7, 2 => 0x1e6910661e31ba711df4e6651d9ff71b1d5d66371d4bdfe41d4b6d441cfcff2d1c3361321c2dfc241bc66a921bbebb881b8c3ab51b68fbf21b52f3321b02e8091ad9f7c21a8ab1011a2813601a1ff8021a1a0d841a0f2ada19f7625519b64fa119a7dd5b19946dbc197c44521949aaa21921237f18f690411889ea96181325af17fd343117dd4acf17d74ee717b7e34f176eb59d175f8bcc171049e016808bd7162b36ed160ba2501608592015f38b2515f022ce15dfd0b71583c1441581cb33155248bd1509b50f14e084dd14db2920149982cb148a341b148897d21467363d14644cac145d1d56143cb18d142ee0661427c8201413d60813d662d313d58a2d
  | 7, 3 => 0x2cceec882cb7e2692cb4f4d02c885ff32c19ccdd2be5e1212bcdfc582b81626d2b1d10a12ac038642abaa4262a47332829a71f3e299726e32926780728d1223928a4a83e28926bd427f64d9027e0338727b7972b27b06da727a618d627799d3627275d6d26bad94f26a8efc22649bdd82604c45e25f2df5f25c35a2e25ab45b7253a196d24fa58e124d40cd82493fff9240a8b0923fe6fae23ae0ae7236f54822367e26422ce96d722942b46228c6b7a227d83b02264a7f6225a38cc2203254121ec31b52163d5e220d91fca20b256c820806b5020734b3420608cbe1fead8e71fd3c25f1fb72b911f912d781efec5ec1ed7a4461ebf80801ea8dfff1e6950b1
  | 7, 4 => 0x40cb095940986ba64092c1a0401b334b40169460400a44cb3fc3812b3fb7ecf73f72244e3f2f70223e771e883d558b723d01f4f83c3d6e133bcc8c933b6faa4e3b6c7b743ab84ab43a14aa3c396f572d395192c3390153ab3899ed18388e952737809ff0373d0ffc373a149f36bd7d7436ac65283691cc6a361360cf35f55dab342cdee9342a70ab3427e57933cfaaf9339d2ebf3346b69a32df488e32d7023e32b744f7326191d231de767a31abecc53149b7de3108eac730fe0ec830bc147630237ce330091cc92ffa480f2faba6b72f7065272f271ec42ee767672edee25d2e8e1cd92e5831e72e53ab1b2e41d80f2e2bae332dd16b5a2da536eb2d8b266c
  | 7, 5 => 0x5cd73cc75beb4d855ba59d8b5b1fd1e859ebc25759d0ac0158fe7a9958a5f17757d2e8a55640306854aba60453fc7867537d76d851b9e85451b8929651836e8f5146665850e499dd50844bf45065281a500ddb8f4f8e8d6b4f8aafda4f2c76214f2b90654edfc1824e9d19034d77a65b4cf6d8fc4cb596f64c30865f4b92da054b7591cb4adcc5144ad4903c4aa90b0e4a88cd634a0125c04931ec3848f1b3c24883da01484f34f046f4bb0f46ad44e045404f1f44ae84d9446f139f4428ae2e4410545243c92a8d43c1fcc943b05eeb43839b9e437525d54313159c430a7fee42b779a3427f0d1c4218ce08416350044117fbf441157ea6410d769640e5429a
  | 7, 6 => 0x9719b59296f2550d96ad3b8995d7577e9398c7d89277b5869272d0f48dc12cab8d2055058bdac01c8b619d978b1f0e0e8b1c96828aae7a4289cb471188f65fa78833276887d1c013873b6b62860ca4e785fbcd998281f3fa82177bf4810b064b7fefde0c7a69e3517a350f14798b7d067943d46277000c187464d37d73d04ef171e15d5871b3b9eb71646ae6706c5be46fe7c8a46f0124aa6ebf04ed6e8926966e33f3d06be82ea96bda4ad56a8772f96a22b4f86970708f6838001367aab8ca66e682006693df09668c4770658509286422f9a963ac1506633b241c62f0399662dd8f1e6213f55d60c8b4dd5ff0ea905f036dfa5e4b5e7c5d6e18e55d0e48da
  | 7, 7 => 0xf273ad01e580cb8ad8f36f13cc8a6ad8b60afd5bb4c8cb71b48a150cb1e121efb12d9c7aaef0f6f6aeefd66fade4e126a7e3d1f7a6fa9141a452dfc3a1d961dfa05edf759e495df49de686b09c7430f59bc710819ad6c5fc99ed5e8797fdf8da
  | 8, 0 => 0x49fcd0d049ebf63049954c004914d2f04824cd4047422a2045ce2170442bd8604427d3b043130cb0415ff010414dac1040d1ac20406fbe203f0435403d7459b03ce94ee037520950368888c034deea10318307a0301ae1502d82aa602bc4a2f02b85f87029f514b028de01e0286b7c202609609022e4d3f022a715e0228c63402147fe0020b934d01f5eb2d01f0143401bc3326019fd7670186014c017987650176d77b0173637d0172b143016603570165d8db0165a78a015fcb3e014ecf6801464eee0146034a014268c701203fde011bdf1500f76a5900ef69e800ea38dd00e89b5e00d76e02007aaac7006c268400481fea0038331a002d875e00067d12
  | 8, 1 => 0x91f50c90919997809119d3708f39c6608df973908d510d608d2e6d2088a86920873c2b30865d84f0829c9e708194bd307fad7cb07f70b8707d234e707cc006107ba7de007b114e7079d31ce079752f30790b29f07897414077ca621077b799207662bcc0743838c073f5373073d42b70736c9aa072c9a98072ac26d07073daf06dc60a306d7098006c4169506b78b5f06b1cdce0693d9f2068bc39d0684017d06838227065cde5f065bab2f064cb809062e87460628d0bb0607b53a05de0bb405ad2f3405a5230e0590ddec058bff2805805925057c0b7a05793d820523d982051ff7b5051e6def0509fa1f0508581c0507be6904c7d89204adcdb904a0e76b
  | 8, 2 => 0x10c69771109bbfbb105e7e021034f0900fb1a7760f91284e0f808c130f7093b80f6f93110f2e04d90efd32510ef31bbc0eef2d5f0ec217fe0eb97e200e998a170e88588a0e7e15130e7db3450e79ef230e7662f60e25e66b0e19c3470dfe95740dd4b6d80dcc48780d8441f50d7f85ab0d61a76a0d570f570d4a1cc10d27df590d0c05040d0342060cfc12980c6f98ee0c481a120c232aad0c0149d40be887c10bb2dfbe0bb1cb050b926abc0b8ca5670b6f0d3c0b62a4e10b556fa80b395c9a0b17a0e90a97b6ff0a8e01bd0a7f630e0a7677f50a5960500a3e4a3409ede54309dc26a709b79457098587fa095f147d0958bf200934d1df0929d7a40926f007
  | 8, 3 => 0x17102d9d16fd750116d77b9d16c91dcd16c2f98e16573f001646faaf1635c15b161648bc160c7aef15d3b4e415ba6e6315b3f79d1587c11a157f8e8215734321156d3e8b153fc09e152b37771513409014e907ff14e01b9c14db292014cea72914c0d43c14b26e1a14663ea414466a8414446e3c1420fefd1404051413bf6c0813b975fb135dcd66135a7b70134b1232133b3831131a772b1315357712edbfd612ed063c12a8595d128324f812820d5312368661123578e612245a68122261f8120abf081207841211f1344711de2d6511d7480611a875de1198adad115b48311149b8ae1142fa4111381e7b111154cb1107a54710eec24b10d966d710d130c9
  | 8, 4 => 0x1fd3c25f1f7bce301f6e760a1ef740171ec42c741e8f156e1e817e9e1e7359ed1e6cef631e69abc71e481ad41e460f421e3a97551e2d04af1e1fbc621dd0db1b1db4fd5a1d9357ee1d86a59c1d7215931d5dea961d2d9f431cfc3f091cbc12a81ca3b5001c6dfcfc1c5d76581c186f871b890b781b83dee31b2036761b0c66d31b0516841b02e8091aa2be871aa066151a4dc7a41a4050e71a39c2a21a36d11a19ebbf3a19cdfbbe19ba301a19a917ce19a89bc6198e7f10194bf7eb19414ed018fc422a18f302eb18e5db1918989a12185955ec1841934c181c7acd1816a59117b7e34f179c6b23179aa9db1785b96a175d9d67173c2d3b1729918f171f64aa
  | 8, 5 => 0x26eeeb7b26beaf6f26ad119126acf523267d79e52679f5f7267644162671d87b2648e3a826441e1725a301e1258b7b892572649a2533899e24f59d0824e8d99024de4cd924d06dfa24aca9b424a7b2f424a5591f2482c1a2246c8ce72436ece42414ae9a2402910b23c3dd7623b38efa238c288f236fbff3233ffc36232434d9230f30ef22c6965b22c1441e22a738642264a7f62255c20e22432953223682592235fc3c223493472231842a220d473a21e6cbde21a5f96821a213322181df672177d4282149b0a42145e84920f3fb3c20edbe5d20cd9f4c2091837c20713eaa2063e54f20635fcb204abfc92041b12e203060a52026efc11fecb1011fe7a9b7
  | 8, 6 => 0x2f8c06aa2f7e6ae62f4b96e32f2d39052f1d2f5b2f0fc1672f0dffab2eea57922ee290e42ebd3f532e9b5e9e2e7ad7872e4d19592e1ac6682dd864322dd37e3b2db5e3e72daa42342d78a4cd2cfe0cfa2c3569842c11710b2c009a592bf48c202bbea46f2b99aa392b963bfd2b501c0e2b10322c2aec88042ab9f7142ab248542a8387322a7552d52a58f94d2a56a39e2a548dd72a5175e42a4b96732a3e82642a12695129f164c5298ecb11295ce3442936bda92934275729259dd728f4dccc28eb6c7d28ea5aff28cefb7d289bea9e289b063e2891119d287f2f70287543b92812896927d2573727b7972b27afdc82279dbd042731721527018d8f26f168c9
  | 8, 7 => 0x39dae219394fb67838facf2638eab13438e1a69e38b3291337ef3e4037d8b58137c170f837b97c2737ac12ad37a86f8237a858aa379a989f37914cec3746e21e3741ce9037265403371f5bc136be20e336addf82369956fa366946d0364691d8362ee59736187f4e35bf14c335a5a365359f67e7359740203517c80e3513314734db18ef34c0f5e03435619b341103d93409f3743405470d33be968233938d8e333bc51f330a8e35330419e632d537fb32d045d13264f1943264d807323ac717323a478d3234dcea3217774731fe5ec031ee0ac731e8cc4631a059483195d77b3173b86c31674c90312404d430a77a803016b5f92fb1aafd2fa3aeb12f9ce545
  | 8, 8 => 0x48f6d72e48d2e75b488b33cf480a3b3f48011d50471dd813471a541a46e5982746c7c63546816343463bd6b2461ed1b245bf3cf1457c8e1e4577834e44ea513844dc725944baecd44486548a4434b007440fd5ef43c1fcc942e7b5af42b779a34276b14a422d6f5541ab34c64183d88741092fdb4100325e40e5429a40d0e6ee408111a240793c5e404d4a10403af74d403479923fdfc6be3fd3ef6d3fa77a2d3f57f6893f5789763f3ee4403e8cd15e3e444aad3de93fc83dc4a85b3cba78eb3c7dc04f3c63d8bf3bcc8c933bc2d8a43bbe60cd3b5dab7f3b5c4edf3b50a6093b1df1083b0ea8af3b05d6f73acf9b4b3abd39b13aa78d2e3a5b45d33a59cc03
  | 8, 9 => 0x5bb301c65b63ffb55b52e35c5a7e123d5a70ea9959fcbebe59a0c2fc597bfa89595a2c99591709c358a46bf7588d756d58637a7557ff801957ea2a68578e67bf5727b7f456a74fda565d379154de0ffe5415f7d353ca92085395ea5852acbe7d529125325273af1d5215f853520ebc75520a2f2451fa5aa351b036c451a43ef25105402250b5b7bb5079064b505ccc4850490acd4fbdd0064f943bc44f5dcf014e8fb6294e79020e4e235b2b4d84a92c4d84259f4d4db2914d2ff4d14cc34f264c8856354bf147df4bcaa8ce4bc1d16d4bbe87aa4b6760be4b5e75fd4aa90b0e4aa595d049fc667e49f79d6949acb5e149abea55492cd7e549148db04910933d
  | 8, 10 => 0x70baf60f70a579f87044fe07701d07ab6fae64e16f71e1b36f1873fa6ef1af446ecfcc7c6e6d5a4c6e6c6f186e5e503d6dab2ce86d3bf9306ccf53856c97891e6bce3cbb6bcdd5cc6bc32d296b76748c6b69eddb6ae5c9b86ad14c446a26c34b696814bd6920920f6909578d6866437968006e646795eeda674bba8d6747e36c672edba1671066ce66f72a0f66a68d8e6647db116602318b65ef200465b3f9f7659c24f6645abe8e6407b8f163e50b4763dfdc5f6334f12c62f0399662d73fc861a0cf3760dceb4d60a89073601d48af5fbac6fd5f5cd0ad5f18482b5e79be265dfe16575dd272ae5dba85d55d53729c5d4de46a5c79de655c4c83945c0a8559
  | 8, 11 => 0x94ddd495942a4f2093baf614932511749253e7a1919a80f8907419099011f5828feddb818f8c45778f168e788b43d38e8b3b49c589d716268954afad88fc08f688a5bebc8867195f885f7a21881513e887b2ceb487a5f8ba874f926986d3f20a86b55a34866516248623df698570f86d85483ba784927b05832cd056817be6a2814d04b78114557780cc1f0c7f0df4cc7dec882d7dd765af7d251eea7cea112d7a99952e7a9723887a67111c797234ad7851225b77efff8477b8b7dc77ae8a657746c83977384af176d1d46976b7ced3768547ed75a93ed17516320074b8b4237479fdbe74111f2874034845732042cd731482c372be915172aeb9a071ab5e19
  | 8, 12 => 0xff6dda91f2854adfe5499e93e2d732e2e28853e8e1af79dcdd3bc896d5632629d00c244bc9bdabcac98dd445c68fa8b7c2a41594c29e4a2fc18229f3c0185e2ebe953f5fbc0c7999bbfae1e1bbf021b9bbae7e2cbad16276b9ca7217b90024ecb8686298b62fb8d8b48a150cb3ca64ddb2eddaceb153b1c9afac9269af7d3269acc6a2bba56effffa51eac12a31a5e96a28a50f2a0a6c331a0680ccc9fada3039ec0d7899abddb8a9a4c5f4b9a07c69999993bf69946ed2997c8df5e97a4a4a1955d64e3
  | 9, 0 => 0x1ee472391ebb13731e1aa3ae1e17d8601d81c57f1c8c41261c1ffead1b8548e61a974b451a5d39541a0ece7019e3604919deb3e21979f417196672e1191531f41900f42917d7cb95170db67f1680e75515f86a8015f022ce1561a43a1413d60812ae5da3129997eb11d7480611b4128d119811441134c9340fc22fb60f3badb20e589c450d61f2fb0cb3009d0c867e660c22507d0bb2ffb10b989d440afb5dd30acf09dd0ab7b9ae0aa9dacf0a71f95609ee1b6f089ab0f308786758075140fd06cd9ad4061ab28605c61dd605ad2f3405a3eb0a04d0acec036df1500360127102d5abde0296f5790291d00a0129b75501283a1700f5a3d20027347900103def
  | 9, 1 => 0x405c8f3d3f49363a3e9c5ebb3d8620523c9f3cdf3c9d75a23c52b0633bc2d8a43b76a7473a8b1a653a861c9939de879e396f572d37a1ed1c378f31e836c744ae36b6da92359f67e7357bcd573528ce78330961a632ba82ac329cbbfb3294bf40326a06213264f194319b3e423055c0a6302ca7772fbf18df2f1362052eedfa852ee51d392e46479b2d6df75a2cf3c0ef2cae27f22c1543872bcf9a012b698d6c2b48380c2a5175e429e942c429c478db2882e2b2284db2db26beaf6f26aa53c3262d41fb258a6ea424a7e76c246ade9622daf26b225c733222543c1c22521a04223682592219ec0a21a5f96821a1d267203e530f1fd3d3851fb72b911f608b65
  | 9, 2 => 0x8b8fda438b308e208a8bfac7886bb2a5877910e281bd8a2f7f97da8d7ecd8d627e35cb0e7c439fcf7aa15747785a178977211a3f73a1eeb76e4086346b58c0516aa2ab6069d0a4b06920920f67f1c0d366742ba7647899486449b75d62542af85e90082e5d9647d45d93d62e5b2acd595aab3d0b5a437adf5943cbfb56fffaeb567ee6cd55df5df855bb43f755ab6c4653b7a8b552e996fb52acbe7d51ee61ea5038abd64f943bc44e9d19034e7327324de27c5e4bff26be4bf147df4b62f61f4a0d197449226c8f49148db048fa38cc48ebd2aa48b0ac9d46e1bded45f6b58444d9dfff43b9f0a3432891ef42b779a34214fad1413ca696410d769640db2d8b
  | 9, 3 => 0xfd75d7f8fbe5e7c4f1c1f496eef3064de8f19d4fe2f02cffdcac824ed8e7dfa1cef7401ace412b29c5d3e588c4eae2e7c4ad7d99c4ac2c82bf7d381ebf74ae55ba9e7ab4b7610a65adab993dad85a160ac8a86eba98c5b5da8d69abba309310c9eab30d29db654639bfcd7929b308e9f98553ede9690ba6e92b08ece90b340669011f5828e2374cd
  | 10, 0 => 0xf33b5fd0dee29a6ad1efb8f3a279eac48ab84b5d61ca40085e22a75455df5df85059633d4aee737942b779a33e277fff2efbd9642eedfa851606144c1561a43a05169eb0
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x0
  | 6, 0 => 0x120280630000000000000010001203802301000000000000300000000000020000000000003000000000000400000000000020000000000005000120380a300000000000000800000000000000001a454843040001a514c03020000000000001000000000000100006028023040000005484205001954204030007959420c44000000050508205000000000000400159410c030000159400c43010001a35504301000000000000500195420403040000000000000000000000000403806028024000001a515003020019540084305
  | 6, 1 => 0x5079954108040007995410804000000000000009000000000000304806028024000480e0280240000195430403010000e01802303000000000000a079954308440004806028024000019530084300079954308440007959410c8400079953008440000000000000020480e028024000001a454403010000602802300000000000000407995300844000001201802302000000000000100000000000000001a3544030200195430843000000e02802300000000000000000000000000000001a544c03010000000000002
  | 6, 2 => 0x60380602802400
  | 7, 0 => 0x159400c430000159420c4300000000380620000000038022020000001802202000000180220000000038022000000e01802300000004544020100000000121050001203806302000000480a2040000e4100230000000355002010000e21002300000000180220700012038063020000e0180230000000514c0201001954204030500000038022010000a01802300000000480e2070019542004300000000000a10500000000000010000025440205000000180220400159410c0301001040280230000000018022030000003806203
  | 7, 1 => 0x4806202000000480e201000000480e203001954300430100195300843000000004806203000000180220700000000000070001220006300000c00280630000000514c0203000001000a2050000000000000000000480e203000003550420200000515002010000e0280630000000028062000000004802206000000480220200159400c430100000048062060001202806300000005150c20200006028023000000001802206000003544020200195320403000000050504201000000000000000000000000030000035504202
  | 7, 2 => 0x155082040000004806203000120380630100012028063000000051500202000000480620200159420c03000000052500205001954308030000159410c0300000000480a20000012310023000000004802203000000480620400000048c420200000300062030000001802202000001550820400195410803000000042006200000000380220300000544c420300000048062010000043002202000005150c202000000000610400000048402050000035500203000000000000200000544c42020000041002203000000000a104
  | 7, 3 => 0x1550820400195400483000000003802201000004108020000000454802050000e0180230200012038063000000002802204000000480e20300195420403000000004806201000000390420100000544c420300159400c43000000e0280230000000048062050000050504205000120380630000000048062050019542040300000000480e202000123000a30000000544c420100000504c4201000000480e20000000504c420300159400c8300000005150c201000120380230000000028062050000000000004000005050c202
  | 7, 4 => 0x35504203000120380230200000544c02020001203802300000003550420300000544c420200159400c83000000004802202000004544020200000028062050000003806201000120380a300000003550020100000544c42010000035440203000000480e2010000015508204000005050c20100000504c42010001202802300000000380220800000355002030000000002105001954304030000000505042030019532040300000005050c2010000045440201000000380620200000544c02020000e1000a3000001202802300
  | 7, 5 => 0x120180230100000544c0202000004548020400159400c830000195310803000019530084300000000380220700012310023000019543004300000005050c203000000480a204000000180220300000028062040000e028023000000031002200001954304030000000210022040001203806303000004544020100195420403000000003806201000000480220100195430843000000000000001000000480e201000000480a20400000038062020000e0280630000000000000010000e02802300000000280220900159410c8300
  | 7, 6 => 0x1802208000000000e10300000018022030000e20006300000000380220100000400c420000159400c8300000003550020300000048062030000602802300000000000e1030000002802204001954108030000195430843000000050504202000000000000200159420c4300000000280220400159410c030100000028062040000025504204000120280230000000544c02020000004840203000120380a30000000000000030000e0180230200000544c02020000041002203000120384830000000048062010000e01802302
  | 7, 7 => 0x12028023000000004840200000000380620100159410c0301000000480620200159420c430000000200062040000003802200000000380220300000000401080000001802201001954308030000000028022040000602802300000000380220200195430403000000002802200000005050c202001954008430000195420403040019540084300000003100220200000018022010001232002300000005150820500159400c4300000000180220100000018022020000050504205000003550420200000018022020000045484204
  | 7, 8 => 0x390020000000544c42010000043006203000120280230000000544c4203000123100230000000454842050000e410023000000003904202000000000610100012028023050000000000001000000480e20600159410c830000000048062020010c0280630000195420403040019530084300001040280230000012038023000019541080300000003540420100000028022050000045440203000000000210100159410c03020000000000005000000000000200000505042030000a0080630000000048022020000005508204
  | 7, 9 => 0x195430403030001202802300001954304030000012020063000019530084300000005050c2010000035440203001954008430000000514c0203000004544020100000000000080000001802201001954108030000000420062050000e0280230000159400c830000000028022050000e120023000019543080300000003544020300000048402040000000000003000004300a200000003544020100000048022020000e4200230000195430803000000e028063000001203802300000000480e20200159400c4301000005050c203
  | 7, 10 => 0x320402000000045480205000000480220400159400c43000000000002107000004544020400000544c020200000505042010000005484204001954204030000159400c8300001040280230000000028062040000000000001001954304030300000000000090000045440202001954108030000012038023000000e02806300000003550020200012038023000000015480205000000000610200000000000000000602802305001954308430000000420062040000e02802300000120380a3000000000000001000120080a300
  | 7, 11 => 0x1203806300001953008430000159400c8300000004544020100000514c0201000004548420400195400843050000043040200000000384020200000210022000000e018023020000045440201000c0028063000019540084300000060280230000000515002010000050504202000003544020100000514c0201000c002806300000000380620600012018023030000003806203000000001210100195430403000019543040301000004544020100012028063040000001802202000000001210200000038022020019543080300
  | 7, 12 => 0x480e2010000602802304000003544020300000355042020000004802200000001548020500000354402010001201802301000122100230000012018023000000000012104000120380230000000355002020000602802304001953008430000012028023000000035440202001954108030000000048c020000012028023040010c0280230000000454842040000001802203001953204030000000000000040000045484204001954304030000012028023000019541080304000c002806300000005150c2010000e02802300
  | 7, 13 => 0x4802200000000000000a000000180220500000454402030010c0280230000000028022000000000000000000c00280630000000038402030019530084300000000480e200000004548420400000354402030001203840300000000548420400012028023000000005484204000121000a30000000048c020200000048022050019530084300000000480220100000000000000000e02802300000000548420400000514c0202000004544020400000000121060000000012101000000380620200000505042010019543040302
  | 7, 14 => 0x6028023000000602802300000120384030000195300843000000602802300001953008430000195300843000001203840300000120380a30000000048402010000045440201001954304030000000454802040000035440201000000000e106000000180220200195300483000000602802300000000480220800000454842040000035440202000000180220400000038402000000001802202
  | 8, 0 => 0x104104000000001210100000000c010100000001041020000004848200000000001210400000410c0203000000390020200000000c010200000039002020000000100105000000180220200000001001040000000006104000000380a2000000000006101000000010c102000003100220100000038022000000000100104000000010c1030000000000005000004300220200000000000010000000040108000000480e2010000000108104000000004010300000000021070000000100105000000080a2000000004840200
  | 8, 1 => 0x10c102000004000a20000000000c41030000004840203000000001210100000000c0103000000010c1020000003802202000000480220100000001001070000000000002000004200420000000300062000000000040105000000000000600000320402000000000084104000003000620000000000021070000000100101000004300a200000000000e103000000390420100000000401070000000100104000000000610200000018022020000000084105000004308420000000000c410800000410c020000000420c0200
  | 8, 2 => 0x104104000000390020300000210022000000000040101000004200620000000410022000000000006104000000010c103000000000210100000039082000000032006200000000480220000000410c020200000430802000000040006203000003100a200000000480e2000000000002104000000000000300000000c0101000000010c106000000000e10200000000121020000000104107000004300a200000000000610100000000061030000000100101000000008010000000400c820000000420402050000000100101
  | 8, 3 => 0x104101000000380a20000000048c820000000001001070000003802203000001000a20000000000121030000000104103000000004010500000000021040000000100106000004200220400000000000040000000000003000003008420000000310802000000041002203000000010410100000000c010200000310022000000020006200000004100220500000000061060000003900200000000008410000000000c0101000000388420000000000021040000000084100000000000210100000320062000000000002101
  | 8, 4 => 0xa105000000000210300000000121020000043084200000003000a200000000000210200000000c4101000004300a20000000000061080000003840200000000008010500000000401040000003904200000000004010700000000c0102000004000620200000000061010000000104104000000004010200000001041030000000012101000000000e1060000004884200000000390020000000400c4201000000484020300000420c4200000000000210100000410c8200000004000620100000430402000000042002200
  | 8, 5 => 0xc41030000000002101000004100a2000000000104105000000000610100000000401070000000002104000000180220000000400842000000000006102000000000610100000000c01020000000002108000004108020000000000841050000000108105000004204020400000000021000000003806203000000000a100000004300220100000430802000000000002103000000010410200000000c4101000000010410500000000c010200000000021010000000012101000000380620000000000c010300000400c8200
  | 8, 6 => 0x32040200000000008410400000000401020000000080104000000390420000000000401040000004884200000000010410300000048c8200000000480220000000430062020000000012104000001000a2000000032006200000000000e101000003100a200000000000e102000000390820000000000c410600000000401050000042002200000000008410400000000401030000043006202000000010010500000000c810000000000401010000000100104000004304020000000000c010200000200062000000000012101
  | 8, 7 => 0x48c0200000004200620000000000121020000000012101000003100220000000000c0103000000010c1030000000104104000000000a105000000380a2000000041002200000000000e101000000010410200000001041020000000000001000000000000400000048c8200000000000a10000000000000040000003840200000000280220000000200062040000002802205000000010010200000000021050000000002107000000000e1020000000012106000000000e102000000008410400000001041010000000108104
  | 8, 8 => 0x10c101000000010c106000000000610400000420c0200000000480620200000000c01030000042002200000003100a20000000000841040000031080200000000280620000000048022000000000104107000000001210200000400c8200000000388420000000048042000000000012105000003000a20000000410c8200000000010c1010000000040108000000000e10000000001041020000004802205000000000a10400000001081050000000012104000000010c10100000000c410100000001001000000000006106
  | 8, 9 => 0x480a204000000000e10300000400c4200000003100a2000000032040200000001000a2000000000006108000000010c10000000048c4200000004200620400000000c010100000001041040000000000006000000000e1070000000040103000004300220000000120022000000030084200000000000a105000000000210700000000841050000000100101000004100a2000000043040203000004108020000000048c82000000000012104000000010c1020000000100101000000008410400000410c02000000003840203
  | 8, 10 => 0x50000041002200000003000a20000000038402010000000084109000000004010200000400c4202000003100a2000000000104106000000000610100000048c02030000000002101000000000e103000000380220000000000c41060000000002105000000000a1040000000006108000000000210500000000401020000042002200000000001210600000000c010000000039002000000000000003000000001210500000048c4201000000004010100000000c01030000000040102000000000610100000000c4101
  | 8, 11 => 0x480e2000000004802200000000280620000000420062040000000104107000004108020400000001041020000004802200000001000a200000000000e101000000010010100000410c820000000001041020000000002102000000080a2000000000002101000004300a200000000000a10500000000c01060000000084105000000010410200000000c0103000000010c10100000000c4102000000280220000000410c8200000000484020200000001001060000042040200000000484020400000000c41010000043040200
  | 8, 12 => 0x210300000000c41020000000000005000000000210200000420062000000003900200000000010c10300000048c820000000000c410200000000000050000021002200000004200220000000048c820000000000c4101000000384020000000000021020000000012101000000000210300000048c4202000000000e10300000200062000000000040106000000000a109000000004010300000000021010000003802200000000010010700000000401050000000040101000000004010400000000121060000003802200
  | 8, 13 => 0x104101000000010010100000410c82000000000002102000000001210200000000c01060000021002200000000004010100000400842000000041080204000000480e2000000000002104000000010410400000410022050000000040108000000001210300000400c820000000430482000000000104103000000001210200000000c0101000000001210700000000061030000043040200000000480a20000000420c4200000000484020100000430402030000000040108000004200620000000000401010000000040101
  | 8, 14 => 0xe106000000010c10300000400062010000003880200000004300a2000000030006202000000000610800000048c0201000001000a2000000000006106000000004010300000048c82000000000002102000000380a20000000410802000000043002200000004008420000000001041020000030048200000000000610600000001001030000000000001000000010010200000001001030000000000002000000010c1020000000040105000003000a200000000000a104000000388420000000001041060000003900200
  | 8, 15 => 0x48c0200000000010c10100000000000050000000040101000000000610200000000401010000000040102000000010010200000001041000000040084200000004204020500000000401040000001802202000000390420000000400c820000000048802000000031080200000000010010400000410022000000000002104000000010410000000000c0106000000000210500000018022020000000080105000000384020000000000000030000043040203000000180a200000000000210300000000121040000000040102
  | 8, 16 => 0x48c4200000000004010100000000c41010000000012103000000010c1060000004840204000000480620000000300842000000000006108000000000e10300000310802000000000012104000000480220000000420c02000000000000006000000000e10300000000c0102000000000e101000000280220400000048c4200000000000e102000000001210200000001041020000000100101000000488020500000000c01020000002806200000000004010200000048c4200000000008410500000000401020000000012102
  | 8, 17 => 0x2102000000000e1080000000040109000000000210700000300062030000031002201000000000a1040000032040200000000000e1060000030084200000004300620200000000000030000000040104000000010c10200000400c8200000004300420000000000401050000000040106000000001210600000310802000000002802204000000480e20100000038022000000000000000000002100220500000000401040000003904200000000004010400000048c8200000000004010300000048062010000043006201
  | 8, 18 => 0x10410400000001001070000031080200000003008420000000048c82000000003802201000001000a20000000000401040000000000003000000001210600000000121040000000100101000000480220000000000c4107000000380a200000000000a1090000000006109000000480e2000000004840200000000000a10400000200062050000042040200000000480220400000000c010600000000121010000043002200000000000610300000410c0201000000010010200000000c4102000000480a20000000000c4101
  | 8, 19 => 0x48c820000000000121060000041080200000000010c107000000000e1010000000006102000000000e101000000000e1030000004884200000000004010900000048402020000031080200000003000a200000000010c1070000000100106000000000e10300000000061060000000080104000000010c102000000001210100000430402000000003806202000000000a10400000430022000000021002200000000010c106000000010810400000400c820000000410802000000000104105000002100220000000410c8200
  | 8, 20 => 0x1210100000039042000000043002200000000010c103000000010c1020000000040108000000000e107000000000e101000000004010300000300062000000002802200000000480e200000000010010600000430802000000000040108000000000610100000000c0102000000010c10100000410c0202000003000a200000000000e10000000000021020000003802200000000010810400000000121030000000108105000000004010100000000121010000031080200000004100a200000000000e1010000000104103
  | 8, 21 => 0x3900202000000280220000000300842000000000040103000000384020000000000121000000000080105000000384820000000048022000000000080104000004304020100000000121000000004840200000000384020000000000401090000003840203000000001210300000000401040000000108105000000390820000000000c0102000000480e2000000000084105000000010c107000002100220400000048402000000000002105000000000e10100000038402010000000040101000000010c10200000000c0106
  | 8, 22 => 0x480e2000000004840200000000010c101000000001210400000000401040000000002102000004108020000000000401000000003908200000000000e101000000010c1060000043002200000000000210000000000021030000043040200000000480e200000000480e2020000000040102000000004010400000000000060000042040204000000004010400000001001060000004840200000000001210200000000401040000003904200000003100220100000410802000000000012105000000000e1020000021002204
  | 8, 23 => 0x4840200000000480a200000000001210300000000401010000000000001000000480220000000430022000000003840200000000010410200000000c010000000000c010600000038022000000000002100000001200220000000048c820000000001041030000042040200000000280220000000000061010000004840200000000000210200000000121050000000000006000000000e1030000030084200000004300220000000048402050000000080104000004308420000000430402020000000040105000000000e106
  | 8, 24 => 0x400000000121020000004840200000000000e1060000041080205000000484020400000038402000000043040200000000000000400000000c01070000000040105000000000610400000038402000000000100106000004108020000000000121060000000012105000000000e10200000048c020200000410802000000043040200000000010c1020000000012107000000480e2000000043002200000000010c10000000000021050000043040200000000000e1070000042040200000000000e1020000003840200
  | 8, 25 => 0x121040000000012100000000480e200000000480e2000000004802201000000000e10200000048402000000043040200000000480e2010000000000006000000000e1000000003884200000000010010500000000121010000000000006000004300a2000000000104105
  | 9, 0 => 0x9000000000a10000000000c81000000000006100000000004010000000000c0100000000000000300000000000000000000002100000000010c10000000000000050000000048100000000000210000000000c0100000000000000100000000000040000000000003000000000000800000000000010000000012104000000004010100000000c4100000000010010000000000000050000000104100000000000000200000000c4101000000000000700000000c41000000000000001000000001210200000000c4100
  | 9, 1 => 0x90000000000002000000008010500000000000040000000002102000000000000700000000021020000000000000000000010410000000000c01030000000100101000000010c10000000000c010200000000c41010000000006100000000004010000000001081000000000000006000000008010000000000c010000000000000010000000000004000000000a1000000000000005000000008410000000001001000000000104101000000000000800000000121000000000108100000000010c1010000000000001
  | 9, 2 => 0x60000000000004000000004010000000000000040000000000004000000010c10200000000000080000000000003000000000000400000001001040000000002104000000000000600000000c010000000000000020000000012101000000010c101000000010010200000000000020000000104100000000000000400000000c410000000000000070000000000003000000000000800000000c4103000000000e10100000000021040000000104101000000000e101000000000000100000000000030000000000001
  | 9, 3 => 0x200000000000010000000100100000000010c10000000000000040000000000001000000010810400000001041050000000000004000000000000300000000121000000000000004000000000000400000000000070000000000006000000000610200000000c01000000000006102000000000e100000000010c102000000000e1000000000002101000000000000900000001001040000000080100000000000e103000000000000400000000c8100000000000a100000000000000700000000121020000000012100
  | 9, 4 => 0x2100000000000e10000000000000050000000000002000000010010200000000c0100000000010c101000000004810000000000401000000000040103000000000000500000001081000000000012100000000000e100000000001210500000000000010000000104100000000000a100000000000a105000000000000500000000000070000000000001000000001210000000000c010000000000c810000000000000040000000000008000000000000000000000021000000000000003000000000000100000000c0101
  | 9, 5 => 0x2000000000000100000000000020000000000005000000008010000000000121000000000012104000000000e100000000010c100000000000000700000000000020000000040100000000000e100000000004010400000000021000000000104100000000000000500000000000030000000040105000000000e101000000010c100000000000000600000000121000000000104105000000000000200000001081000000000000001000000000e1000000000012100000000001210200000000c81000000000104100
  | 9, 6 => 0x10c100000000000e100000000010c100000000000000100000000401000000000000004000000010c100000000000000500000000121000000000040100000000010c1000000000000002000000000e1000000000000000000000010c1000000000000001000000010c10000000000000010000000000000000000008410000000000401020000000012100000000000000600000000021000000000040100000000010c10000000000401040000000000005000000004010100000000c410000000000401040000000104100
  | 9, 7 => 0x4000000000e100
  | 10, 0 => 0x40000000000004000000000000200000000000010000000000000000000000000000000000000000000000000005000000000000000000000000030000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_18 roots_18 10 s ws hint
  | 1 => checkCutEntry dom_27 roots_27 9 s ws hint
  | 2 => checkCutEntry dom_28 roots_28 9 s ws hint
  | 3 => checkCutEntry dom_29 roots_29 9 s ws hint
  | 4 => checkCutEntry dom_37 roots_37 9 s ws hint
  | 5 => checkCutEntry dom_42 roots_42 9 s ws hint
  | 6 => checkCutEntry dom_43 roots_43 8 s ws hint
  | 7 => checkCutEntry dom_44 roots_44 8 s ws hint
  | 8 => checkCutEntry dom_45 roots_45 8 s ws hint
  | 9 => checkCutEntry dom_46 roots_46 8 s ws hint
  | 10 => checkCutEntry dom_47 roots_47 6 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_48 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_28 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_37 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_42 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_44 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_46 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_48 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_48 == dom_48) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_48 goalM u ys) : RunD dom_48 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_48 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_8 : ∀ i, 8 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_16 : ∀ i, 16 ≤ i → i < 23 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 16 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 23 → Z 7 i = true := range_split z7_0 (range_split z7_8 (z7_16))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 20 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 16 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 20 → Z 8 i = true := range_split z8_0 (range_split z8_8 (z8_16))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_0 : ∀ i, 0 ≤ i → i < 8 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_8 : ∀ i, 8 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 8 = true)
theorem z9 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := range_split z9_0 (z9_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z10_0 : ∀ i, 0 ≤ i → i < 7 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 7 0 = true)
theorem z10 : ∀ i, 0 ≤ i → i < 7 → Z 10 i = true := z10_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z11_0 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := z11_0
theorem checked (s : Nat) (hs : s ≤ 11) : ∀ i < NN s, Z s i = true := by
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
  · exact fun i hi => z10 i (Nat.zero_le i) hi
  · exact fun i hi => z11 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_48 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 7 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : RunD dom_48 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_48 roots_48 goal_48 12 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_48 goal_48 := by
    have h0 : isConstB dom_48 goal_48 = false := by decide +kernel
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

end S_48

theorem low_48 : Lower dom_48 roots_48 goal_48 12 := S_48.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_48_bits : ∀ r : Fin 64, roots_48.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_48_lt : ∀ r : Fin 64, dom_48.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_48 T)
    (hlow : Lower dom_48 roots_48 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_48, Avail mask256 roots_48 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_48 hfan 0 roots_48 roots_48 rfl hsup0
  set out := (execN C.gates roots_48).getD C.output 0
  have hout : out &&& dom_48 = T &&& dom_48 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_48_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_48 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_48_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_48).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_48)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_48.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_48 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_48).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_48 &&& mask256 = dom_48 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_48 = T &&& dom_48 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_48, hd63, hout]
  have hnc_m : ¬ IsConst dom_48 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_48 roots_48 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_48, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_48 roots_48 0 roots_48 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 3900702720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_48.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 12 ≤ t :=
  lower_to_circuit6 fG goal_48 12 hT6 (by unfold IsConst; decide) low_48

def wit : Circuit := ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [7, 3]⟩, ⟨GateOp.and, [8, 1]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.and, [10, 4]⟩, ⟨GateOp.or, [10, 4]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [12, 15]⟩, ⟨GateOp.and, [14, 16]⟩], 17⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 12 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_12062_aux

theorem PEqualNP.Outside.L_meta_12062 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 3900702720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 3900702720) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_12062_aux.wit, PEqualNP.Outside.L_meta_12062_aux.wmono, le_trans PEqualNP.Outside.L_meta_12062_aux.wsize (PEqualNP.Outside.L_meta_12062_aux.lower s hs), PEqualNP.Outside.L_meta_12062_aux.weval⟩
