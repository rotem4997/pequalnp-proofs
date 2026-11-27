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

namespace PEqualNP.Outside.L_meta_16725_aux

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

def dom_0 : Nat := 0xaaaa
def goal_0 : Nat := 0xa880
def roots_0 : List Nat := [0x8888, 0xa0a0, 0xaa00]

namespace S_0
def pairsG : List (Nat × Nat) := [(3, 7), (3, 11), (5, 7), (5, 13), (9, 11), (9, 13)]
def r1sG : List Nat := [3, 3, 5, 5, 9, 9]
def r2sG : List Nat := [7, 11, 7, 13, 11, 13]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x9c0bd08d
  | 3, 0 => 0x9c0bd08d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaa00000000000000a0a00000000000008888
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

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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

def dom_1 : Nat := 0xaaaaaaaa
def goal_1 : Nat := 0xa8a0a880
def roots_1 : List Nat := [0x88888888, 0xa0a0a0a0, 0xaa00aa00, 0xaaaa0000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000, 5, 21)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0x30303030
def goal_2 : Nat := 0x30202000
def roots_2 : List Nat := [0x20202020, 0x30003000, 0x30300000]

theorem low_2 : Lower dom_2 roots_2 goal_2 4 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_3 : Nat := 0x33333333
def goal_3 : Nat := 0x30202000
def roots_3 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30303030, 9, 13)] (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0x55550000
def goal_4 : Nat := 0x54400000
def roots_4 : List Nat := [0x44440000, 0x50500000, 0x55000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_5 : Nat := 0x55555555
def goal_5 : Nat := 0x54404440
def roots_5 : List Nat := [0x44444444, 0x50505050, 0x55005500, 0x55550000]

theorem low_5 : Lower dom_5 roots_5 goal_5 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x55550000, 12, 28)] (by decide +kernel) (by decide +kernel) low_4

def dom_6 : Nat := 0xf0f0f0f0
def goal_6 : Nat := 0xf0e0e0c0
def roots_6 : List Nat := [0xa0a0a0a0, 0xc0c0c0c0, 0xf000f000, 0xf0f00000]

theorem low_6 : Lower dom_6 roots_6 goal_6 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0, 4, 6)] (by decide +kernel) (by decide +kernel) low_2

def dom_7 : Nat := 0xffff0000
def goal_7 : Nat := 0xfce00000
def roots_7 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 5 :=
  lower_iso [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_8 : Nat := 0xffff
def goal_8 : Nat := 0xecc0
def roots_8 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

theorem low_8 : Lower dom_8 roots_8 goal_8 5 :=
  lower_iso [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_9 : Nat := 0xffffffff
def goal_9 : Nat := 0xfce0ecc0
def roots_9 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_9
def pairsG : List (Nat × Nat) := [(2, 6), (2, 10), (3, 7), (3, 11), (4, 6), (5, 7), (5, 13), (5, 21), (8, 10), (9, 11), (9, 13), (12, 13), (12, 14), (12, 28), (17, 21), (18, 22), (18, 26), (19, 23), (19, 27), (20, 21), (20, 22), (20, 28), (24, 26), (24, 28), (25, 27), (25, 29)]
def r1sG : List Nat := [2, 2, 3, 3, 4, 5, 5, 5, 8, 9, 9, 12, 12, 12, 17, 18, 18, 19, 19, 20, 20, 20, 24, 24, 25, 25]
def r2sG : List Nat := [6, 10, 7, 11, 6, 7, 13, 21, 10, 11, 13, 13, 14, 28, 21, 22, 26, 23, 27, 21, 22, 28, 26, 28, 27, 29]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_9.map (· &&& dom_9)
def goalM : Nat := goal_9 &&& dom_9
def NN : Nat → Nat
  | 5 => 15
  | 6 => 10
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xe0bddffab9bdbc07acac4a339e9c03b2914cfc7b8c616cec6baa5813589810f157e8265a536b80584ca624073cf0896d32f633fb2d5135c81ac7d7cf
  | 6, 0 => 0xe0bddffabe3fb924ac05225e8c616cec5c943edf5299e96d3a6b8d4130706e4225303d371eb2c2bc
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x555555550000000033333333000000000fff0fff000000000f0f0f0f0000000000ff00ff0000000000f000f00000000000330033000000000000ffff
  | 0, 1 => 0xff00ff0000000000f0f0f0f000000000f000f00000000000eeeeeeee00000000ccffccff00000000cccccccc00000000aaaaaaaa00000000a0a0a0a0
  | 0, 2 => 0xffffcccc00000000ffff000000000000ffccffcc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x22f7292368bdca485a2f729226045c930d62f729036045ca48d40f5248058bdcb5258127292358bdcc50d8117b8e65045ca40d4115248358bdca495811728e35
  | 6, 0, 0 => 0x8bdca48d8117b9265045ee525411729235045ee5214117a9245045ee51d6307b94968bdcd5258117b98a5
  | 7, 0, 0 => 0x117b9495
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3e6e44ff87ff0fff1fffc7c70f0ff03fc3800f00e103c0003fff
  | 0, 1 => 0xf00fc003838f0000e00307c6ef0ff03fc07800fc191bb00000e0
  | 0, 2 => 0x3ffc00ffff0003c7bf0f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c6c44ea86cc057f0efd45030a06b02d41ac0b50210200001f7f
  | 0, 1 => 0xf94fd2abafcf5a80f1035fdfff57f4efd57933fc393bb20a4ce4
  | 0, 2 => 0x3fff3bffff8203f7bf7f
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 19 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 19 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 19 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 19 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 5 0) :: stateWiresD n (ids >>> 5)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 5 0) :: stateWiresS n (ids >>> 5)
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
  | 4 => 3
  | 5 => 106
  | 6 => 15
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xac05225e5c943edf1eb2c2bc
  | 5, 0 => 0x6ec980c36b065e596790bd296687970064d4803362b9685c5e1d4aa85c943edf5c5c027556b9b479554c825e537bfbe75299e96d4e9167214a565af1445013a34279fe8d40ae6a173fcb2d5a3b3581ad3a6b8d413a3350d73903b3463739cd8230ed598230e804a030de30f430706e42303831d82f5ebe042db842822d24e2362b675315289b62ea2791e22a276bea43255ebca725303d3724f800cd24d3906d211b38e2206585ea202d49801fee0db01eb2c2bc1e7a86521e20a2db1b8a7ef11b4fee2b1695ced6141aecf112e5db13126b25b71232e94d114008550e01c6b20ad7cab808dabbe6081bde80066e9780063aed7105f246af032905ee0241d3e1
  | 5, 1 => 0xfd575aabebec3f58ea397c2ae40c141be3ea3188d83a9daad6f33033d646893ccc199b72c447f238c1ee8a2dbe3fb924be3a6442bb95578cb4992a82b2d0f062b279bdb6ade6772cac05225ea58d7a63a31e0ea0a0508cfd9812ced297dddd95949b309c93c0f7228e381f4f88c9ba2b8518c61582ddb4f581ea162e7ecfa1837e8fe63a7dd26df17d856b167702c5a975affeaf74ef743f744473ec73a0d5137004fb096eced5a5
  | 6, 0 => 0xfd575aabe40c141bbe3a6442b4992a82a0508cfd93c0f7227ecfa1837702c5a9744473ec554c825e276bea43206585ea1b8a7ef1126b25b70241d3e1
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x400002200410000001304000000300000c4010100001c00000130400000050000000000600001c000040000000000021440c000010000044c1010000000000000000000003000000000011304080000800000c00003
  | 5, 1 => 0x200414401010000080000000001c0000700000c0000200000c411030000000000600000c0d1020000040000300000400001000004000020000000000600001c84101000004411050000100000100001c4010100000c00001
  | 5, 2 => 0x1c00001000010000010000000000300000c000030000004c101000004000000000100000700000c000011044100000200000400002000004000012004100000200000000004034400411050000040000310440c00007
  | 5, 3 => 0xc0d100000004000030000100000200000c0000120041000002
  | 6, 0 => 0x300000c000050000000000100000c0000100001000001000008000000000000000400000400005
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 8 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 1 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 2 => checkCutEntry dom_5 roots_5 5 s ws hint
  | 3 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 4 => checkCutEntry dom_7 roots_7 5 s ws hint
  | 5 => checkCutEntry dom_8 roots_8 5 s ws hint
  | 6 => checkCutEntry dom_0 roots_0 4 s ws hint
  | 7 => checkCutEntry dom_2 roots_2 4 s ws hint
  | 8 => checkCutEntry dom_4 roots_4 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_9 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
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
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 8 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := range_split z5_0 (z5_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_8 : ∀ i, 8 ≤ i → i < 10 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 8 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 10 → Z 6 i = true := range_split z6_0 (z6_8)
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
  scr dom_9 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_9 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_9 roots_9 goal_9 8 := by
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

theorem low_9 : Lower dom_9 roots_9 goal_9 8 := S_9.noCircuit

def dom_10 : Nat := 0x3030303030303030
def goal_10 : Nat := 0x3020202030202000
def roots_10 : List Nat := [0x2020202020202020, 0x3000300030003000, 0x3030000030300000, 0x3030303000000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 5 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_11 : Nat := 0x3300330033003300
def goal_11 : Nat := 0x3200220030002000
def roots_11 : List Nat := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]

namespace S_11
def pairsG : List (Nat × Nat) := [(9, 13), (9, 41), (12, 13), (12, 28), (24, 28), (25, 29), (25, 57), (40, 41), (44, 45), (44, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [9, 9, 12, 12, 24, 25, 25, 40, 44, 44, 56, 56]
def r2sG : List Nat := [13, 41, 13, 28, 28, 29, 57, 41, 45, 60, 57, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_11.map (· &&& dom_11)
def goalM : Nat := goal_11 &&& dom_11
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x634eda5
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3300330000000000330000003300000030003000300030002200220022002200
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf80c7030c063
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc2e78b3d5e7
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_11 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_11 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_11 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_11 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_11 roots_11 goal_11 4 := by
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

theorem low_11 : Lower dom_11 roots_11 goal_11 4 := S_11.noCircuit

def dom_12 : Nat := 0x3333000033330000
def goal_12 : Nat := 0x3222000030200000
def roots_12 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 4 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0x3333333333333333
def goal_13 : Nat := 0x3222222230202000
def roots_13 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

namespace S_13
def pairsG : List (Nat × Nat) := [(1, 33), (5, 13), (5, 21), (5, 37), (9, 13), (9, 41), (12, 13), (12, 28), (17, 21), (17, 49), (20, 21), (20, 28), (24, 28), (25, 29), (25, 57), (32, 33), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 5, 5, 5, 9, 9, 12, 12, 17, 17, 20, 20, 24, 25, 25, 32, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [33, 13, 21, 37, 13, 41, 13, 28, 21, 49, 21, 28, 28, 29, 57, 33, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_13.map (· &&& dom_13)
def goalM : Nat := goal_13 &&& dom_13
def NN : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x3b1bb212
  | 5, 0 => 0xd268f7e7c5df00ecb3507d7e2ac4f6e512ef7747
  | 6, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000333300003300330033003300330000003300000030303030303030302222222222222222222200002222000011111111111111110000333300003333
  | 0, 1 => 0x33333333111111113333333300000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x976435
  | 5, 0, 0 => 0x8764158764326876543608643058764316
  | 6, 0, 0 => 0x876435
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf83f80639c3c300e0006d0cce00319f8018c03ff39800f80ff
  | 0, 1 => 0x3ff3981ff8000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc3fc2739e3cb90f1016d3dde5bf3bfac19c1290310007807b
  | 0, 1 => 0x3ffb553ffc229
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 25 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 25 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 10 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 10 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 10 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 10 then wireAt i else 0
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
  | 4 => 4
  | 5 => 20
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x995298d181e5788c7694e7890f92b19f
  | 5, 0 => 0xce2fdbfdc5e9dcc8bad12923a7d4fdd59e310d9b9c1be658995298d19361b60892a7ff7d6c1d17f66955c5a568cd66c551db27f540cd85c33e3ca5393810c1db36e9258f1dce88e910bacbc3086941f4
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x300000800003
  | 5, 0 => 0x400000000008000000000040000100000000000000004000010000080000000000400002000000000010000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_10 roots_10 5 s ws hint
  | 1 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 2 => checkCutEntry dom_11 roots_11 4 s ws hint
  | 3 => checkCutEntry dom_12 roots_12 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_13 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_13 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_13 == dom_13) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_13 goalM u ys) : RunD dom_13 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_13 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := z5_0
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
  scr dom_13 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_13 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_13 roots_13 goal_13 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_13 goal_13 := by
    have h0 : isConstB dom_13 goal_13 = false := by decide +kernel
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

end S_13

theorem low_13 : Lower dom_13 roots_13 goal_13 7 := S_13.noCircuit

def dom_14 : Nat := 0x5555000000000000
def goal_14 : Nat := 0x5440000000000000
def roots_14 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]

namespace S_14
def pairsG : List (Nat × Nat) := [(50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [54, 58, 54, 60, 58, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_14.map (· &&& dom_14)
def goalM : Nat := goal_14 &&& dom_14
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xf882f5e9
  | 3, 0 => 0xf882f5e9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x550000000000000050500000000000004444000000000000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_14 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_14 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_14 == dom_14) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_14 goalM u ys) : RunD dom_14 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_14 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_14 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_14 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_14 roots_14 goal_14 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_14 goal_14 := by
    have h0 : isConstB dom_14 goal_14 = false := by decide +kernel
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

end S_14

theorem low_14 : Lower dom_14 roots_14 goal_14 4 := S_14.noCircuit

def dom_15 : Nat := 0xffff000000000000
def goal_15 : Nat := 0xfeea000000000000
def roots_15 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_14

def dom_16 : Nat := 0xff000000ff0000
def goal_16 : Nat := 0xea000000e00000
def roots_16 : List Nat := [0xaa000000aa0000, 0xcc000000cc0000, 0xf0000000f00000, 0xff000000000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 4 :=
  lower_iso [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_17 : Nat := 0xffff0000ffff0000
def goal_17 : Nat := 0xfeea0000fce00000
def roots_17 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

namespace S_17
def pairsG : List (Nat × Nat) := [(17, 21), (17, 49), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (20, 21), (20, 22), (20, 28), (24, 26), (24, 28), (25, 27), (25, 29), (25, 57), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [17, 17, 18, 18, 19, 19, 19, 20, 20, 20, 24, 24, 25, 25, 25, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [21, 49, 22, 26, 23, 27, 51, 21, 22, 28, 26, 28, 27, 29, 57, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_17.map (· &&& dom_17)
def goalM : Nat := goal_17 &&& dom_17
def NN : Nat → Nat
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xf4050a1dd827a5f7a6b32695301879e705dfb75b
  | 6, 0 => 0x73240d52
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffcc0000ffcc0000ff000000ff000000fcfc0000fcfc0000f0f00000f0f00000cccc0000cccc0000aaaa0000aaaa00000f0f00000f0f000000ff000000ff0000
  | 0, 1 => 0xffff000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x87643260863215864321686543260843205
  | 6, 0, 0 => 0x864325
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe3be3e701f0007e07f838038003803e001c1cf8ff8fe3f83ff
  | 0, 1 => 0x1ff8000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfbbfbe791f8a37e7ffb3a2b954b8abe127c3cd8ba8d41b81d7
  | 0, 1 => 0x1ffc042
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 25 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 25 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 9 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 9 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 9 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 9 then wireAt i else 0
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
  | 4 => 5
  | 5 => 20
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x73240d525aee05895473af6e4e8b4ff301e0734e
  | 5, 0 => 0xf5e4537bef4cf998eddd1af5d7c737ebc998fb3f98f9af048f2f91ef73abf9b97395259e73240d5267fbc5974bce347c3c1f93602868627c28531e57204c65761a287331195e30fe18dba2f41391194e
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x40000300000c00004
  | 5, 0 => 0x20000000000000000800002000000000000000080000200000800003000010000040000000000000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 1 => checkCutEntry dom_7 roots_7 5 s ws hint
  | 2 => checkCutEntry dom_14 roots_14 4 s ws hint
  | 3 => checkCutEntry dom_16 roots_16 4 s ws hint
  | 4 => checkCutEntry dom_12 roots_12 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_17 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_17 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_17 == dom_17) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_17 goalM u ys) : RunD dom_17 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_17 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := z5_0
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
  scr dom_17 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_17 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_17 roots_17 goal_17 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_17 goal_17 := by
    have h0 : isConstB dom_17 goal_17 = false := by decide +kernel
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

end S_17

theorem low_17 : Lower dom_17 roots_17 goal_17 7 := S_17.noCircuit

def dom_18 : Nat := 0xaaaa0000aaaa
def goal_18 : Nat := 0xaaaa0000a880
def roots_18 : List Nat := [0x888800008888, 0xa0a00000a0a0, 0xaa000000aa00, 0xaaaa00000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_19 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_19 : Nat := 0xaaaaaaaaa8a0a880
def roots_19 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa0000, 5, 21)] (by decide +kernel) (by decide +kernel) low_18

def dom_20 : Nat := 0x5555555500000000
def goal_20 : Nat := 0x5440444000000000
def roots_20 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_20 : Lower dom_20 roots_20 goal_20 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 44, 60)] (by decide +kernel) (by decide +kernel) low_14

def dom_21 : Nat := 0xffffffff00000000
def goal_21 : Nat := 0xfeeaeeea00000000
def roots_21 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_21 : Lower dom_21 roots_21 goal_21 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_20

def dom_22 : Nat := 0xffff0000ffff
def goal_22 : Nat := 0xeeea0000ecc0
def roots_22 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_22 : Lower dom_22 roots_22 goal_22 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa, 12, 13)] (by decide +kernel) (by decide +kernel) low_18

def dom_23 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_23 : Nat := 0xf0e0e0e0f0e0e0c0
def roots_23 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

theorem low_23 : Lower dom_23 roots_23 goal_23 6 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19

def dom_24 : Nat := 0xff00ff00ff00ff
def goal_24 : Nat := 0xea00ea00e000c0
def roots_24 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_24 : Lower dom_24 roots_24 goal_24 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff0000, 5, 21)] (by decide +kernel) (by decide +kernel) low_16

def dom_25 : Nat := 0xff00ff00ff00ff00
def goal_25 : Nat := 0xfe00ee00fc00ec00
def roots_25 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

theorem low_25 : Lower dom_25 roots_25 goal_25 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc00, 8, 10)] (by decide +kernel) (by decide +kernel) low_11

def dom_26 : Nat := 0xffffffffffffffff
def goal_26 : Nat := 0xfeeaeeeafce0ecc0
def roots_26 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_26
def pairsG : List (Nat × Nat) := [(1, 33), (2, 6), (2, 10), (3, 7), (3, 11), (3, 35), (4, 6), (5, 7), (5, 13), (5, 21), (5, 37), (8, 10), (9, 11), (9, 13), (9, 41), (12, 13), (12, 14), (12, 28), (17, 21), (17, 49), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (20, 21), (20, 22), (20, 28), (24, 26), (24, 28), (25, 27), (25, 29), (25, 57), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 2, 2, 3, 3, 3, 4, 5, 5, 5, 5, 8, 9, 9, 9, 12, 12, 12, 17, 17, 18, 18, 19, 19, 19, 20, 20, 20, 24, 24, 25, 25, 25, 32, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [33, 6, 10, 7, 11, 35, 6, 7, 13, 21, 37, 10, 11, 13, 41, 13, 14, 28, 21, 49, 22, 26, 23, 27, 51, 21, 22, 28, 26, 28, 27, 29, 57, 33, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_26.map (· &&& dom_26)
def goalM : Nat := goal_26 &&& dom_26
def NN : Nat → Nat
  | 3 => 3
  | 4 => 22
  | 5 => 52
  | 6 => 172
  | 7 => 162
  | 8 => 22
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xa6a193c960e49fa5424b7ded
  | 4, 0 => 0xfbd9e944f0674f5cd6414b98cefd43e6aeade5e7a96861b29905ba8a88ac0c28830bcd147e7eff807bd80d927222baaa7199079b6fa4a0d06b1c81e863e8c2665465787a3c762d4e2e53c292213de8b8158470d50bf2a9a0
  | 5, 0 => 0xff95acedfa5176a9f0760da4ea40f5bfe4ccb2fbdf6648c5d72efe15d4434fb2c8dcf747c4df8dbbb88348e5b62ff35cb476428fb3a5b92faf8b401cab05838ba89b6280a7c5a7a3a43577489547afe5944e6e9590a76c17901f15588ebd5e448da484dc87f229bf876876b085ef384b83ba94f474b450cd726b6eb97245bdeb65c3fb4f4f48fc124e0610dd48d912c14898bef64252611640722d163e30959e3c7ccdeb3c4790dc35b4875c30a973ca2404b6a1217ffa8e1c2c7872177a46bf15a9ceb41298b3ce0990af62024944bd
  | 6, 0 => 0x54a96c0952c657934fcdf8ab4b83f6714b7c2a2d4b0d87ba4abd1d0b49c0fcf4498f6d6646dd66d84654163445a7f5984497853041730f93412c1b3840b204e44021fadd3fa4aa9e3d4e5b033b4891dc3a81220237d59bc63748575a36d69bdf33fffa6731ae08452de6358a2bdb8c2629d10a3228851290286822e3283daf4f26a8a45023fc45a223e658262230d7cc2227e697206969b81f44507b1c96ea4919ba301a16b01e5414a03ebe1488e2b2139302bf133f9c8b133d44ab12e80ba512cec45012123e381020e5be0fec104b0f3d85820ed5a7770dd4529f0cc62e6c0a4613430919997806457cb90453118103f8e99a03939ebd010b91e1003b07ed
  | 6, 1 => 0xbb897c82bb65c259bab9a1bdb7dce78eb533a702afaab267ad163a72abb0f071aadd7ee5a9fdc82ea959581ca911a68ca7853e24a52c7e6ba31a23a09f307a4a9ee2b6579ea0779e9d465cb998bf8e8d96f768a49662477396424b419520bde993370a88903733998dd7584d89cd0684861dc98683bb05f782c4fa7081f114c77f2038cf7d794f967d45306b7c3306be78b04f7e761d3e06753360a074f8ca7a743c75de71addb456f6815276db3cd8b6934a6d86809c50867852479663e41f065e76cd565438d0163c9dda363939f33600139515d4e2d7e5bd7e0585aea31985ad883ea59d1670559449244592546695755f7e456a791e356488c3a55dc8b89
  | 6, 2 => 0xfc30abd5fa728806fa06476af9afb2a4f7d6a695f5ebce57f4a631d0f0d5c0b0ee71c1e8ed07c3a8ec01ec82eb21901ae9d230c7e896cba3e82ca1a0e81160aae6017bdae33cbb01e266464ee171d949dd36d6a1dcd5e9e6dc5fd33ddc530e5fdaaefcd0d970540cd7fa8692d70a1d9bd4af50cfd4535b46d2eb9853d019acf1ce52b7facc389808cbd5b4f2cb5a385fc69fce5ec5736c6ac53a4d5dc4e960c4c47d35c1c0e08b57c0938b43bc9c5c20
  | 7, 0 => 0x6e834bca6b1be36669c0add4689e67455d6275f4581fb8f6568173f954c1de1052942b7251e81d51500139404e2ce2974dc27b5b4d1acf0f4ca60af44c1e35cd4b0c2c394a3f78dc49e125c6499b08ca48c2474245f6b58443b4257143a9f8484214fad13ee6de3d3dc32c533c9d75a23c21f90f3a67daad36b6da923544f67134746a9f33d93c6b330961a63264f194302ca7772d8366eb2c2d83092ba0a43a2b81626d2b698d6c2a6cf0712964176b28a4a83e2838c79a2705880d26396ad425fb67b21b2d157f19f08aad19d9673c12baa6770faa77070f3d84400e7dd0190e783ebe0d9a92370d52c9a60afb5dd309874f3d0754ea1506291d8305869eb1
  | 7, 1 => 0xd697c1d4d0e5095fcea2794cc9a019fdc8d8951dc7d3f23bc7466283c6a44c39c61b5c10c33e8ebcbfa41077be907f01be4f311bba88bda4ba572e16b85c2f59b55b444cb3feb3cab37ef559b253eee6b06c6b4eacac34b6aa87c3f1aa56a296a909e4c1a840633ca6910249a5d7b751a4dede88a499e38aa494c22fa275c8f5a07b3991a00d2aa29e58572e9db654639c48de239b1dd7b09b16c7a498411d8197012b84944ede0093602c469351acbb92efa7479272b1cc913b5e9f9117715e8fa2db658f6e24048e7679718d5eaaf98ce2cfc48a81f0ca8a0d10dd8968a0cb872610b884075d3b7ef7ebec7bf0d33379e15a28794792a7745b5f6d739b9ac4
  | 7, 2 => 0xff939ceffefb8721fe12eeb4f9acd0faf6e94291f34c8d5af22186e7f109fd47f1027f58f053c1fdf03d9387efdef6d4efc2e112eef3064dee6cfdefee1e2c58ec164c1eea555bf2e96d0b92e8b03ee3e812cbdfe6e4feb6e49194eae4625a30e3624776e21fca1de1ccafbce1c2a466e1283faadfb32b5bdcd6712cda2d30a0d8653959d6af2d85
  | 8, 0 => 0xd1efb8f3c2afde01b6be7634b47be6219b34b1218ab84b5d7f4590c97e1a8a5676f0de33764e5f61705b5d9f61ca40085fbac6fd5cde0cce5a34cc4234064f6c1b1e63461606144c1561a43a1142fa410e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff000000ff000000fc00fc00fc00fc00f000f000f000f000aa00aa00aa00aa00333333003333330033003300330033000f00ff000f00ff0000ffff0000ffff
  | 0, 1 => 0xf3f0f3f0f3f0f3f0f0fffff0f0fffff0f0f3f3f0f0f3f3f0f0f0f0f0f0f0f0f03ff03ff03ff03ff0333033303330333030333330303333300ff00ff00ff00ff
  | 0, 2 => 0x33333333333333331f1f1f1f1f1f1f1f1313131313131313113311331133113311113333111133330fff0fff0fff0fff0ff00ff00ff00ff00f5f0f5f0f5f0f5f
  | 0, 3 => 0xaaaaaaaaa800a800aaaaaaaaa000a000aaaa0000aaaa0000aa88aa88aa88aa88aa00aa00aa00aa00a8a88888a8a88888a0a0a0a0a0a0a0a05555555555555555
  | 0, 4 => 0xccccffffccccffffccccccccccccccccc0c0f0f0c0c0f0f0afafafafafafafafafaf0f0fafaf0f0faf0faf0faf0faf0faaffaaffaaffaaffaaaaaaaaaaaaaaaa
  | 0, 5 => 0xeeeecccceeeecccceecceecceecceeccee00ee00ee00ee00ecececececececece0e0e0e0e0e0e0e0e0e0c0c0e0e0c0c0e0c0e0c0e0c0e0c0ccffccffccffccff
  | 0, 6 => 0xf0c0f0c0f0c0f0c0f0c0c0c0f0c0c0c0f0a0f0a0f0a0f0a0f0a0f000f0a0f000f0a0c080f0a0c080f000f000f000f000f000c000f000c000eeeeeeeeeeeeeeee
  | 0, 7 => 0xfa00fa00fa00fa00f0fff0fff0fff0fff0ff00fff0ff00fff0ff0000f0ff0000f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0f0f00000f0f00000f0e0c0c0f0e0c0c0
  | 0, 8 => 0xfafafafafafafafafafaeaeafafaeaeafafa0000fafa0000faf0aa00faf0aa00faaafaaafaaafaaafaaaf000faaaf000faaaeaaafaaaeaaafaaa0000faaa0000
  | 0, 9 => 0xfcfcccccfcfcccccfcfc0000fcfc0000fcecfcecfcecfcecfcccfcccfcccfcccfcccccccfcccccccfca8fca8fca8fca8fc00fc00fc00fc00fc00cc00fc00cc00
  | 0, 10 => 0xff0f0f0fff0f0f0fff00ff00ff00ff00ff000000ff000000fefceeccfefceeccfeeeccccfeeeccccfeaafeaafeaafeaafeaa0000feaa0000fcfcfcfcfcfcfcfc
  | 0, 11 => 0xffcc0000ffcc0000ffaf0f0fffaf0f0fffaaffaaffaaffaaffaaff00ffaaff00ffaacc88ffaacc88ffaa0000ffaa0000ffa0ffa0ffa0ffa0ff0fff0fff0fff0f
  | 0, 12 => 0xfffcffccfffcffccfff0fff0fff0fff0fff0ffc0fff0ffc0fff0ff00fff0ff00fff00000fff00000ffeeccccffeeccccffccffccffccffccffccccccffcccccc
  | 0, 13 => 0xfffffffff0f00000fffffffff0c0f0c0fffffffff000f000ffffffff55555555ffffffff00000000ffffccccffffccccffff0f0fffff0f0fffff0000ffff0000
  | 0, 14 => 0xfffffffffc00fc00fffffffffc00cc00fffffffff0f0c0c0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xcd0131e4d725c204df21ba04
  | 4, 0, 0 => 0xd721cb740bbf0c8768175e598e902ebc93dba05d7965bb40bbeb4f6e8175d69ea502d680ed31e5e15a63a40bc2b4b768175e582ed32f0ad05da65d73e43740bb73404c8175d69ae902eba725da05
  | 4, 0, 1 => 0x34527698faebad41c205d78a4bb40bbab4f6e8175e892a902e8cd0d31e5
  | 5, 0, 0 => 0xd795d324c81b5d676cd3206d7a2b505281b5e8ad415206df5a43b4c81b5d6a8ed3206d786b4f6e81b85674c93206dba33434c81b5e576c53206d759d354c81b5d676e13206d76a4bb4c81b5d69eed7206e159db14c81b5d192ed3206
  | 5, 0, 1 => 0xd791cb74c81b968a4ed3206e15a33b4c81b5d682edd266d9a33324c81b7d672dd3206d759ca94c81806bad31d205d9a24bb4c81b5e19f21da06d15a1bb4c79b449769901f6d78ab507681b5e790ed3206d7a2b4c5681b5e490ed3206
  | 5, 0, 2 => 0xdd59cb74c81b5e190edca06e35a7bb4c81b5e680c93206d75a7b96e81b5e4c33dda06df86b4f7681b5d696edd206d1999264079b5e8acdd6206dfa2b374c81806bd0990115d77ab3b4c81b5e892ed7a06d7aab4d7681b7d67aed3206
  | 5, 0, 3 => 0xd7a2b506c81806bad3dba05d7a2b4f6e81b6d680ed3206
  | 6, 0, 0 => 0xd759db9509903ecd186b3b4c81c06bace5ba640daf4568e98c887d786b4f76e503ebd1764bb4c81c06baced32012c035c976990006d9a335676990380d69900c1001b5e8ace5ba640e03668aced0176d7a2b3b4c804b80d7a93201821806bace531818c035d676992a06
  | 6, 0, 1 => 0xd7a2b3b6c9903ebd125da64061f5e8ad29da640faeb4f769901b701bddb94c80436bad15da64021f5e476e592640e035bb405c400601af4202e304300d7999264001806bd55a63b40c035d676e4c176d7a2b3256990380d6edd264021b668ad41da640fbeb3b72c93207
  | 6, 0, 2 => 0x1af5564c606300d73dda64021806dd159da02edaed56769900c7dfa2b3b649903ebd15a6bb4c81f5e8ad41daf40faf461ad3dda0701aeb274c806300d9a1da63021b5e8ccc932030faeb4f769901a701b74564c80636bad3e43b4c81f5d676e572640e037d69eed3206
  | 6, 0, 3 => 0x1af45d766cbb6ed186b3b4c81c06bacedd2630daf0d672dd320701aeb3a6499036dd186b3b4c81f5e8aced32028e037e87699008601af4a64030436bd191db24c81c06bac9900e18c035d64c60600601af4664c809300d6f1da64021806bd17531b18c035e1ad3dda06
  | 6, 0, 4 => 0x1b343b4c80436bd159daa4c81f5e892ed3203afaf45da0ed31b701af43b4c805b00d76eb3b4c81b5d676e98a640e035e87c990056d7a2b3b4c809b80d759da02e39b5e8c15a83b40e035d67660b806d759dba4c8043ecd159db24c81c06bd158c1718c035e376990086
  | 6, 0, 5 => 0xd79eb4f769903e8aced9264079c06bad11da640c035d69eed3186d792b4f76990380d6edca63021b6e8ad31da640faf456769900a701aeb3b4c806b6bad3dda64025f5d676e53200afaf466649901d701c2b3b7499036dacedcb24c81f5e8aced4a640fbeb3b72990087
  | 6, 0, 6 => 0x1b743b4c804300e5a24bb4c81b5d680ed92640e035ce76990086d766b3b729903ebacedca64005c06bb559da02edaf456769900f7d75a43b729903ebd159ba64065f7e8aced32010faf457aced320701af4d64c60636bad3dda64021c06bb55932018daf45676990037
  | 6, 0, 7 => 0x1af4497698c300d6ed3201c21806b7698c0800c035e84c60608601af53b4c60436bd159da64059c06face532018daeb3b749900d7d7aab3b6a9903ecd159da64021f668aced32018e035bb4e99008601aeb202e30036bb55a83b4c81f5ddacedd2640e035e876990846
  | 6, 0, 8 => 0x1bf4564c806300d78ab3b4c81b5e8a525da640e03668acecc176df86b3b72990380d7a1da64019806bd11d31910c035e87660b88601b746664990300d7a33324c61b5e5acedd2640fbb45676dd320701adca64030436bd159da64055c06facedca02ec03668ac98c0c6
  | 6, 0, 9 => 0xd79eb3b729903ebb559db24c81c06fd159da02ec036d676e53206d759db94c8093ebd159da64481f5d68cedd2640faf456a0ed7207d7a2b42769903ebad39da64021f5d676e532012e035c576990086d7930bb729903ebd159db44c81c06b76e501710daf46686c93207
  | 6, 0, 10 => 0xd7a2b3b4c8d03ebd165db24c81f5e8c359dac40faf45d7698d8c701aed3b4c80436fd186b3b4c81f5e8aced32020e03668ac9900c6d7a2b4c76c103edd15a1bb4c81f5d67aedca640faeb3b72990027
  | 7, 0, 0 => 0x35eaaced3186d7a2b3b6499019801af4557699008700035d6769d320601af4567699002700036e8aced320601af458aced320701af45076990087d7a30d6769901c801af4567699012701af4617699008701af464aced320700035d69ced3206d7a2b3b6099008801af43b4c80c08701af46676990087
  | 7, 0, 1 => 0xd7a2ed6769900c801af45692ed320701aeb3b4c80400701aeb3b4c80600701af4564c80608701af5567699008700035d6769900e6d7a30d676dd320800035d67698c00601af456729900c701af43b4c80c88701af458ac9900c700035e8ac98c0c6d7a2b4c76c9320800035e8baed31b601af43b4c804057
  | 7, 0, 2 => 0x1af456a0ed3187d7a2b3b4c80c08801af461aced3187d7a2b3b4c80c0c800035d676e5017601af43b4c80e88701af43b4c80d88701af4567680b88701af466aced318701af45676e5017701af466acc9320700035e8ad1d319600035e8acecc17601af45676a13207d7a2b3b649901d800035d6729900c6
  | 7, 0, 3 => 0xd7a2b3b4c80c88801af45daced31b701af45676b1320700035daaced3206d7a2b55769900c801af43b4c85008701af0d676e5320701af43b4c804047d7a2b507699008801af43b6499008701af45676b9320701af456609900c701af4564c9100c700035d68aed3206d7a30d676e5320801af45676ad3207
  | 7, 0, 4 => 0x1b745676c9320701af45daced017701af45676c9318700035d67680b80601aeb3b729901b700035e8ac80b8c6d7a2b3b4c80e888d7a2b3b4c80e8c8d7a2b3b4c80d8c800035d676e9320601aeb4f76e5320701af45dac9900c700035d64c80600601af55daced320700035eaac9900c601aeb3b72990197
  | 7, 0, 5 => 0x1af43b72990087d7a2b4376c93208d7a2ed6a0ed320800035e87698c08601aeb507699000701af0d67699000701aeb3b72c9320701af461ac9900c701af4567699005701af4477699008701af45676d5320701af3567699000700037d676e5320601af43e76990087d7a2b3b72c9320801af4564c80c0c7
  | 7, 0, 6 => 0x1af4564c80c8c7d7a2b3b64c13208d7a2b5076990188d7a30d67699018800035d69eed320601af43b4c804077d7a33567699018800035bb7299008601af4567eed320701af45698ed320701af4569eed320701af45676bd320701af456aa9900c701af43b4c80608701af4567680c1770003668aced3186
  | 7, 0, 7 => 0xd7a30d67699019801af4564c80e8c701af4564c80d8c701af43b5099008701af4567680c97701af460aced3207d7a2b55a0ed320800035e3aced3206d7a30d6aaed320801af43b6099008701af45caced320701af459aced3207d7a3356aaed320800037e8aced320600035e9ac9900c601af456aaed0177
  | 7, 0, 8 => 0x35ea76990086d7a2b3b4c806088d7a3356769901b800035d676e53186d7a2b3b7299008801af4567680e97701af25676e5320701af4567680d97701af4567698c087d7a2ed676c9320801af4567698c0c701aeb3b6499000701af456649900c701af55676c93207d7a2b47769900880003668aced3206
  | 7, 0, 9 => 0xd7a30d676c9320800035e8ccc93206d7a2b3b64990188d7a2b50769901d8d7a30d6769901d8d7a2b50769901b801af45d7699008701af45676c9017701af45676dd3207d7a30d6769901b800035e892ed320600035bb4c80400601aeb3b7299008701af45676b5320700035e84c806086d7a3356769901d8
  | 7, 0, 10 => 0x35e87680b886d7a30dfaced3208
  | 8, 0, 0 => 0xd7a2b50769903ebd186b3b4c81f5e8aced32030faf466aced320701af4567680bb6bd176b3b4c81c06baced32000c035e8ac9900c601af5567699036bd159db04c81c06bacedca640daf45676990087d7a2b3b4c8063ebd159db94c81c06bd159da630daf4568eed3207
  | 8, 0, 1 => 0x6bd0ed32010daf45676c93207d7a2b3b4c80ebebd159da6406df5e8aced32032faf456aaed3207
  | 9, 0, 0 => 0x35e8aced3206
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 32
  | 4 => 39
  | 5 => 46
  | 6 => 53
  | 7 => 60
  | 8 => 53
  | 9 => 46
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1fc0003ff000007e07c0ff007fe1c018038001f000000001cc07b91c7f88383fff04710620e0c07c103c1f807f01ffc00ffe0003ffff
  | 0, 1 => 0xffc7fffff1ffff8fffff1ffffffe3ffffc7ffffff8f19ff1fc783fffc7fffff1fffff11e3fe0c7fc1e07f8fc03fff047f07e0ffc07ff
  | 0, 2 => 0xfc7f8ff83fff07ffffffffff87ffc7f8ff83fe107f1fe23e0f8fc1fc7f88f80fff07ff1fffffc7ffffc0787f801ff03ff1fffffc787f
  | 0, 3 => 0x70730000000001c1c070380000070001c0000000001c0003800000000001e03ffffe3e338846
  | 0, 4 => 0x3bff807cffffc0e01c01f0003e003980000e1f038f19ff1fc7fbfe3c67fc7f1e0ff8f19ff1fc783f1fc1ff3ff1dffc00001c1cc77b9
  | 0, 5 => 0x3807707f000f80e01dc1f0703e0000070001c0000e01c01f007be00000000001e000000000000000000000000000007f07e0ffc07ff
  | 0, 6 => 0x3800000e00000000000000000003800000e1e0000e00000380000000000000000000e0000038000000000000000000e01dc1fc77bf
  | 0, 7 => 0x3807000fc0007fe7e0fff87ff1fc1f83ff01ffc7f0000ffc00001c3980380e1f00700000e0000001c0000380000000000000000000
  | 0, 8 => 0x1c39873f3fdfe470001cfcc77b91c00073f30000070001ce007000003807073fdee400e01c1cf80000000070731dee400001c1cc0000
  | 0, 9 => 0x1f80703fc000f87e0000ff0000003b87007ce1ef80ee1c01f3803e03807007c000f800e0001c387b8003800000e00000000000000000
  | 0, 10 => 0xe3c67fc7f1e0ff80f81f003f800e00007c00000007e01dcff0703e03807707f000f800e01c1cff7b9000007073000007ee7c0ff387fe
  | 0, 11 => 0xe38007c7c000038f19ff1fc783fe03e07c73ffee780f81f1cff800e00007c73000e380001f1cc0000e03e07c00ffe038ff9ff1fff83f
  | 0, 12 => 0xffbe77ffcfe0fbf0fe1fe03ffc0fc3e07f80fe003f0f81fe03f800fc0007f80000038e01df1fc003ee3be77c7cfe0fb8e01df1f0003e
  | 0, 13 => 0xfffff838000003ffffe00038000fffff8000e0003ffffe3e338846fffff800000003ff01dfffc003effc67ffff1e0ffff001fffc0000
  | 0, 14 => 0x3ffffe00038000fffff800000003ffffe0e000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xdc0001d7008003606c075406ea0d01a019501b2813026034c06a9044a8808339c0411022020c060100c1b8042013ac007fe0001fdff
  | 0, 1 => 0x66c6dd4eb178d58b7ff51a9fdff62cedd46a3f4d58b19751a858352dc3bc1d711bac910a3020c4601204a8c002394043706e075c06eb
  | 0, 2 => 0xb46a8ea83b9c07cb99779aa5835b0620ca0290006518222a0e0601902a88a00b9405bf1ff57fc5eff6f07e55bd17b79af1df55b85877
  | 0, 3 => 0x24ca9f0623d4c4932a78108e52124c0070f30080082285c1c0f1b8200a070203c44012004c3c412b804088209129e236cd583c330846
  | 0, 4 => 0x4b9ff957c7f7fd2e55c55f118fe0919a0114697299b3b7d3ecffbd66c65f4fb168d58b397d1a8f9352dcbbf1f73dfec932a7c3ccf7b9
  | 0, 5 => 0x6fd5775ff46bf9ae7ddd5f1f9fe621e474287e4513e77cd7f5bffe0d19a219569f2834448865502ca091922114687293f57e57fd1eff
  | 0, 6 => 0x993922b14e872a64c48ac5300ca943882a91e9e2250e00aa47a300943002a91c0a2240e00a803a100903002a00c0001bf7ffd7fdffff
  | 0, 7 => 0xb03a07a20fc44277e6eaf5fa7eb9de1babd781bae77800af5e02009d39a2b95e9f2a74c48ae5702ca9d2002b958080274c48ae5702ca
  | 0, 8 => 0xbdfbbfbf7fdfeef7eefefdff7fbbde007bf780802f4a81eed6f310b4fa9faf3fdee6d3e01ebcfa300b4fa9faf3fdee6d3801ebce0200
  | 0, 9 => 0xdfb573ffdc6bfb7e800fff60200dfbdf3ffdefffb6ef5cfdf3b9fedbb573f7cc63fb5af34fbe7bfbcd23c43e28ee45348d10f8a31814
  | 0, 10 => 0xf2e65fe6a960d7c8f91f8a3f914f22007e2880003fefddfff7fbfefff577fffc6bfbdbfb7fbefffbdf6e007efb808037ef7cfff7bffe
  | 0, 11 => 0xfba007f7c80003db997fbee5a35f6fedfefbffef7dbf91fbeffb14f6f457efbc6af3db801fbee0200f63ec7eb9ffe73cbf97f9abf935
  | 0, 12 => 0xffbf77ffdfeffbfcff9fef7ffdeff3f67fbdfef7bfcf91fef7fb14ff2007fbd80803ffd5dffff1afefbbf77f7cfe7fbeed5dfdf318fe
  | 0, 13 => 0xfffffebd791887fffffad5be5ebfffffea42f9487fffff3d3b4c67fffffc04211087ffd5dffff1afeffe65ffff968d7ff801fffe0200
  | 0, 14 => 0x3ffffff9abfd35ffffffe6ad70d7fffffaf5f46eb
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 54 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 54 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 115 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 115 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 115 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 115 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 7 0) :: stateWiresD n (ids >>> 7)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 7 0) :: stateWiresS n (ids >>> 7)
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
  | 3 => 4
  | 4 => 29
  | 5 => 213
  | 6 => 1328
  | 7 => 954
  | 8 => 24
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xb62e9dec9a93b2bf72d0ffe06e2ea4ac
  | 4, 0 => 0xf68cbccae33c5855e1dd4046dfa4c212d9d8f7e7cd7cb311cbfe0d01c7a5ec4ac4613193b9318e1baf1557e8ac9bcd67a2baef81925adeef8f08ea938502b70a83d6d1ee7d9cb0036c977d7a65bf39b84a05301740ea370632fa9fba3159b7c22bf20d7b220748001df8a09102e901a00295647e
  | 5, 0 => 0x4a8ca0f449e4fe9e48f5f2b9489483bc481e150547b4abff476d210c454523744329a1e542b779a341e0f60d3e7840563e72cfb73c9d75a23b5ff4dd3b451bd639ee226637ff5ca337a793b1367f996d359164a934284ecd33e52db031d017b8310caf6830328f492f992e5d2d91dd90299ce69027a2ea662705880d25dba001257976aa256eb4e1251bbf862436efae221d15441f93be9c1e08610e1d4df85b1bf6a8921ab7faed19ed1d40186f2791157a43ea154e98b114a7d881106d4705103395b70faa77070f22cb830e42ea650d31730909bd0a8a099a21b209874f3d092e46ea088521e2080764f206ff5f2205e79ca90420c92303560a0400243690
  | 5, 1 => 0x939121e592efa74792a869f4928f624e8fb38d108d47c0e48c9555dd8c5d62638c06bea88b3fb09c8afc3ea3894d8b3787454981862ff0fc85d4451d847ea9558437c5ee84075d3b8229ac84818042627ec1279a7d5f68b27cdd580d7c0d3d9579019a1d774fe493770761417548594f74e00fc47243edeb7183c393717e14fb7049eaf46fa9caa86f7ca6206e6f0dfb6e5661bc6d024fde6c5cc38c689e674568556ba566211dbd657fa7266473437b646c71d464476fd56324aefc62b91acf5fd49f2c5a9c001b585cec0758419b775806cd2b556f06955318541d51ef299251de84bd5147ce624fd6e4de4d46f9674d1acf0f4baa88554b9d31b74b24895f
  | 5, 2 => 0xe4434a21e4299312e38650b8e3859273e295016fe1933c22df863131de1d20fdddd96ad2d8bb6d2ad76eed8dd6af2d85d6a59d29d5e7d4dbd4df72d9d4535b46d213ba9dcc917b3bcb634545c9c1e28dc6a44c39c671380cc4e25387c4122956c1f9ee0fc1aba62dc18a15cebfcdd2bfbedeae70bd8bc56dbd4828fbbcb5de76bc907cb5bbe784f2ba88bda4b984f7b6b8d97b0ab84eea26b61dca3db372b4a2b2d50e15b23ad043b06c6b4eafd520e7aca9a704ac305399ac1abacaaaa79269a82a4e04a71b78b4a56eedc6a4d859a8a25e4bf1a2598ba9a0309aeb9f06b8019e71869c9d7f031f9cb6ee409b3d4dac9876c3339742e1059599b4eb94ba79b8
  | 5, 3 => 0xfc7a83edfbe653bdfbd8a13cfa5cc4c9f9acd0faf8cf82a7f863ef6af7a48a32f75e5177f5e365a6f55795c4f3aa2e95f2fc5ba2f2a4d852efced257efc2e112edd55da7ed3f2692e907f834e6f74567e62a3a27
  | 6, 0 => 0xb1a7d630ae892150ae653d70ac4d5b90ab8b2690ab629b709e9743d09bdf0a009874f3d08fadadf08e9a2cc08c00bc908b081660879a30408586f940848694b0815b7f90811dcf507bae626078f1e53078c6002074eba94074033b10715437d06dc984206a136850681af190665520c062e60fa059b7ef705687e890526658705169eb004f7559904c9880c04b413c50479bbe1042d77d503ffc1990384d1180341d11b033a727c0332635f030d3b3003087e0402eac56702da1ead02c1685702898f5e02734c9f024ad8f90248132d022b627e02239f5002075cec01e3cad001ca161a01c1f3ad019c9fad0195ffdc0185f46d00f94cd000d6e3c300a7cf8b
  | 6, 1 => 0x155ed0bb15423b41153eaa181517feab15045f451437977c1436a470140eaf93140b2e6e13bd0dcc139b02df13967e2f136b732c1349e7ce133c08ef132af56d1305f52212d1fe401223d25011f5076911eac26e11be49131190c3f1118d63e411804b36116b4724115b67ca1150faed1144e41f1142fa4111408e9a112a239910e1c50f104ef361101f34a20ff61b8b0fcb33c20fa65f9a0fa2a5570f79f41c0f3d84400f1c66040eed14a20ee5d4340ee271f80ed68c150ea887730ea51df30e7e15130e737a980e66678e0e2559e90d9a92370cfc43180cd4b54f0c64f8630c64c7b30c61e8210c40260e0ba5030a0b88cc090b7421250b2e0ec30b23fcd6
  | 6, 2 => 0x22c73513229eb02f228b59102278b07222758e6922747b08226c911122599897218ce6fb213bddeb210e8bd120a84c1420327e022014c6441fcf12471fc4f9a61fa432931f8738591f3387171f2183b71eedc70e1eafff3f1e7148da1e2780c41d826c881d73f5661d66c50e1d4c60a11c7f55261c10c5811bb1776b1baefe391ba64fad1ba367651b9c90241b8548e61b55df541b27d2611b1e63461b0bab3e1ace0a291ac6cf551ab7c51b1a1f1cf019c2b1f0199a22351921f28d18e16a7f18c13d3918bf975f188affa9186c3881185955ec181c0a6c176346e017353650171e87051710ef8e17015432165c2d5c162a15f61606144c15f3a9421561a43a
  | 6, 3 => 0x2cef63982cdef6d92cadc4612c50f8382c4d2a222c42325c2c2d83092c1a29112bfc7bed2bb2627d2b69948c2b2a76162b25f1c52afe09d52afd8c522a554b8d2a37f9162a2bb0422a00355d29f5789c29c7962029c478db29af2b64298b593d297c99f8291385ac28e1d56328d3f68428b96dc828b13185289a985c289a15a22889cbcf27b3f5412750b4f6274e4fcc273a86802727c9a626f6561a26da10d526bad6df25e030e425dc2a282568133f254954e52517e4d624ec380a24851f70247a1050247367df245fcad9242930a92400fd4d23d675a923ade26823aa74da23a73b32239e1af52359c6d02353b18e233e519823303d132314f10022d25b5c
  | 6, 4 => 0x3868b8b7380d7bfe37d0dfcd37c3b2cc379218e33784fc6737596ec3374fedbb372b333936eb893b36b5383e369e286b3609387935e921d135bfbca9350fe1ad34ecd7be34e12a5934a771a7349824f434926031346502b5344f47aa340fff2c34064f6c33df688433da662c33d93c6b33d52e7733a8219a339be83033864f1f3331392c33202fea32d9eef032054f5f31fd931f318b739a31752de731647c2b30e8373330a13daa30a02a493064cfac2fbf35272f81a0e12f68da3b2f2fce4c2f2d39052f2c65032f15a0e52f0a93ca2efbd9642ec68d272ebd3d6c2eba05a82ea523322e8fba352dfdbfd52df741622d91dd902d8366eb2d7d41f82cf8cd04
  | 6, 5 => 0x45689d7244ecccfe44ea5ff044e5077444dff28e44d582994408d56743e3db9743b9e6c743aea1a44382cd094344cc0c43415cc54335a68143110caa42b779a342ae7c51429130724270b5be4267208642600adc4227977741ada2b4417adc04415fc25e4119dfa141134d074049cb82403b69b74017ff6b3f732d3d3ee878a93ec1acba3e9a6a8f3e8bbe993e82daac3e6dc9363e69a4d83e247c763de11f973dce4f973dc0b3cd3d8f565c3d820b7b3d4903cd3d2c7c353d2562093d1e34fb3d107f313cdf82eb3c644fe93bed01ee3ba7c5f03aab48ca3a67daad3a4fc2063a4df0a53a4487b23a2d6c623a11ea4c39ee2266395f2ed039514ff13929da4e
  | 6, 6 => 0x51496a925137e929512495015122fc19506e67a45059633d500139404fc559f74fbec2eb4f57c7d64f54e6cc4efcd55e4ed752244eb549044e7855394e65ab694df6138a4d84259f4d110f864cec75af4ca2ce1b4c9aca3e4c978c154c4c79c44c388e2d4c1e35cd4beb8c424bd0b1094bb788d34ba1260e4b6de5b24b568f0a4b52d5214acdf8d54ac953704ac3b4a54ab62a164a3f5f3c49dd0e9149c4b7d049b6983f498c6ad4497253c1488ad56b4875d39448739a034840189048027d4547e9072d47d7f35a47c35485477d4b3847246cd24700cb0e46f1b311469cb097469949b5466682484631f358461566634601fe5e45b657d1457ae3f0456daacd
  | 6, 7 => 0x5eb642b75eadb47f5e75f8765e5e95475d94c3725d56d04a5cde0cce5cd798925cc8b8545c9649305c1f443a5c1e7f7b5ba915895ba3354b5b338b775aecd9575a9c6dcb5a34cc425a2473d25a197e005a038f9759ed3d0e59a0c2fc591e47e6591e13c758e6c5465886e5b858797527581fb3565808a35357ad78bd57ac7a6c57ab48c1576c925c5722dfa456b187d25699e7475618cb3455f9c36e55bf057b5571ce4a556f06955551c8e5554ecc54554bcaab55407ef254e2c70654d4e82754b25c705465171a5459014c541ac84153cbf68653cb5340539f4bae539201445361a432533a10a75292ddd95260965c522a087851e52d4c518820f751501bab
  | 6, 8 => 0x6b713d786b50e1d96b0ca3d16af017186ad62f646a41599e6a24ff5269cd7e5369c0add468ade545689e67456827ae8567fbcd3367e0419367df3ad067d214df677e8bdf6741623a67061439667c47636624d4f6661f8dfe65f079d16599d1de64aa6b4464a65ef5640e6da163fb6a7f63a6a9d3639b886c6390794c62e8da6d62da87e162cf6d0062bda42e629d9733627050f9626898c062623a3562261eff620486bb61f427ee61ca400861b8723761ab00a9618ab60c61874d90616fe8b4613f4bb6610c525960f0517b60a7ce4460530ca5603a3c8a5fdd5a815fc559925fbac6fd5f871fd25f5545f95f4ce3e85f35ba935efaed315ed5c2bf5ec2fe40
  | 6, 9 => 0x7b4bbbbb7adcb2987abeb30b7a2bf4367a0875a379684f62791c125478e6cebf78d82dee78d751e1785ee2587800865577ae3ab077a217b17747948576fe097576fdbb7a76f0de3376721d75764e5f6175ea2a0475caa9a47556330474cf39e4744813417433e09b7410bb2473e9209c73de49db73be3a8b737f359473493a277317072172dac58272cb905b728a47a8723698e671ca317b71b731cf717e11df7179360f70e1e95e70d5611b705b5d9f704bbcfc703dde1d701fd290701419896fe51c126fbb45706f3a9e9a6f0659c76ee46b536ec7a3626d60d7e36d18b8176d01b3cf6c95954b6c4b6e046c2d95746c0188046bf7365b6bc715e96bb10260
  | 6, 10 => 0x87cc495887c75f8c87b12daa879add67874d6699873313b2871506e986fc6e9386766635867351b2865cbae8864f59148627949e84f5077184efe6a784de833a849e475c844c1a2d843e7d10841fb46484075d3b84064fcd83b17398831695e582993605827963fa82763972825b35088233416d81a4afbe817673d88170ce64816ee3858154339f813e00738102ccf380b1b4cd80a74cdf808528c48069eaef7fa0bcc37f7763977f685e077f4ff8037f4590c97f3407087f2365ca7ef7ebec7e3ea0f47e1a8a567e047dbf7df4a2987dc381bd7db173387d99a3907d8e4bce7d7728657d591a817d304f3a7ce7e2b17c60f3e37bb4d4f37ba3c0797b6bafbc
  | 6, 11 => 0x95d7f1c1959f952e95872ae6955292bd9551aacc952fccd7952f343094dcea649498a31c941d35b893602c46934a18bd930b0da792efa74792acc722926ae7a991b63940912821e49102d10890f68a7190edb58d90e225fa90c97f539021a9fa90070baf8fe77d2d8fa2db658f74f0a98f4e886f8ee830698e6e30d28e4706038dc4f0798d32e83b8c73f3678c67854a8c3f36198c3e57118c284b988c1abb018bee01d98ba49d898b31c58e8b0efab98ab84b5d8aafa50e8aa94ae58aa657898aa44b2d8a9752098a7994f88a4b2c568a0b34fc89a8e635897fb39b89485095892dc66789143e428903714688a82a5488a4fc21887ddfc28846fbcd8803a86a
  | 6, 12 => 0xa2cd8bc3a2b35b7ca275c8f5a264c4f2a22b6a16a1ff4369a1bb4117a190b783a18a8e87a1558ee5a14e6349a070683ea046c73fa03adbdea0309aeb9f90b24e9f65a7529f281e6a9f22e88e9ec0d7899e93ebe99e2df0669e19eaf09e0455d39df088639db392919d3bb9e79d25116b9cd8b9f79cd7cbd59cb0cb0f9ca2ec309c354d039c3531c39c20d3b29bff60119be41d5a9b34b1219b1664259b0181149af887159a4ad2999a2202919a21f39f99f2e6e2998829a399574cfa994e76d0993f2f2f993adcce990e5292988a6f26986b97ef982e64fb980afa1a97c0eda197a85c9d97a00225979d053597708ba597012b8496b2cff2968d841e9644454f
  | 6, 13 => 0xb06c6b4eb060829aaf73e99baf70889eaf647c31af616e2baf249adcaf161728aeec8abdae7e7e23addfe763ad7309f1ad5ae4ecabe5308aabdc71aaabd7936dab7c17aeab676f4fab671e17ab6407b8ab214571aac40ebdaa30b727aa1f6e87a9efcd79a98e4816a97aa236a8f0d2eda8c54723a877d909a840633ca8249059a817ae6ba7e0c10da748d152a7470e27a746ec86a7202e04a70f3f44a6fdec6ba6f5a3cca6dfcc07a6ce0a9ba6cd1d65a6bd0c77a60a91baa5c2748aa5b27004a5a3fa7da59d567ea598068da550f087a5442393a53aae23a4be299da46db910a41794aaa40177f8a3fec70aa3744415a33239eaa304c619a2efe0c0a2d0fecf
  | 6, 14 => 0xbf6a6deebf436150bedf3b8dbe9e16f9be95c8fabe907f01be5eb282be4e61b0be3add0dbe39f4c5be269a7bbe0e54e8bdfb5dd0bde1cfb5bdaa12d6bd8be129bd5509f0bd41496dbd367e88bced7c31bcc8e334bc95da00bbedd967bb1464cebad020e5ba701036ba572e16b9f31b94b9df77edb9748a1eb9552079b8e21df1b8d90467b8a36524b87e451bb8767b00b871b7fdb86243b6b840c1cbb81d8499b7f32202b79e42f9b76b88a8b6be7634b638841db5dd345bb4d0d4a4b4bad623b49eb830b47be621b3e7728fb39e2651b2fa3a99b2e8abfab2dacd1bb2774c55b253b846b222061fb2026dacb1e2cf82b1ab4137b0dd839ab09f38ffb0754665
  | 6, 15 => 0xc9d8b236c9adbb05c9a73878c9a3b4fac91c5dc6c91a9764c8e779a6c8a47d2ac8843c2bc8385198c82aa73ec829cab5c7fe034ec75d9bc3c7290bd7c6ba7a98c6a44c39c6868d05c68515fbc63e6ab8c60a9cf9c58ccf31c5899ec0c559a437c5382f90c5294a98c48fe98ec43cb38fc436eb4fc434f8fec3ad09c1c398766ec3944fa3c38e86d8c3347db3c330a8d4c32be95bc3117bbbc2f38d46c2c56a8ec2afde01c29a9771c26d0ba9c23e4196c2145295c1ebf1e0c1dbd993c1affee9c166fc71c148abb5c121cba0c11b9ec3c0d835bdc0ae1084c0a55ccdc0957461c0873760c02e5d34c01d1494bfbdb5dbbfb4dd66bf83682fbf79164fbf701bba
  | 6, 16 => 0xd42b6155d3d2caa2d3ab69cdd3a84f1fd36f30acd338b056d3152e0bd2fd1e15d2e2669dd27142f3d26e2c13d26b44f3d213ba9dd2099c14d2061043d1efb8f3d1c3301ed1879d90d17bf5cfd0afe803d07de0a3d028b587cfaaeb5dcf7f31b3cf7dbe6dcf2eb760cf2c74c4cf087841cf07fdd0cedb460fced995d4ce39d75bce1ee8e6cdb0a1f9cda6e723cd969af4cd87f6b1cd69efddcd4e5eb7cd223ed1cd19d01fcd13336dccfb6ba3ccca3424ccbe85adccba3bdccc452051cc0295eccbe6744acbe2a4b1cbd798ffcbc97890cbb9f257cba7c9c6cb9100d3cb7ec15ccb35c4fccb2d3d5ccad3949acaad7443ca92fe79ca35eab9c9fddb4fc9f2a206
  | 6, 17 => 0xdfbe1decdfa15b07df9ae990df5144dadf3d5635df1659adde5e1fafde4eb049de35f7a5de104f4addf96729dd06f15fdca563d6dc8494b9dc46adf8dc3179d4dc0740d3dbfb5445dbf961f4dbd11a6cdba15c1fdb711277db4f33a9db092744dac0e1e9dab1c29cdaa10b17da8d8f9bda62d3c3d9eccea3d99b8409d8c89669d88d7dfad87f9952d872797ad812cfdbd7c43538d78c0afed7896e3ad76eed8dd76d9a26d7216316d7168563d70c7ee5d6d35949d6af2d85d6a59d29d6208956d60dd1a0d5f3eb55d5cc9499d5c938eed5bffca0d5bfd6fdd5bb9267d5af29e1d5a7fca5d5a0d46dd57db6c6d568b144d54deaadd52b0a13d4f14d08d469ff7b
  | 6, 18 => 0xebc28ee5eb6cdec5eb32e76eeb154746eafba6c3eaf7f023ea9f02d8ea812a8be9e0e609e9d711dae9bd6f91e97582a0e9674be0e945efd6e86bd220e8316ca5e82d725ee80aa186e8027d18e80138e2e7fb1212e7e6faa8e7e0e5e1e7a46de3e78e4205e6fe9ff5e65393cae61e3e4ee5f7c8dfe5f130bbe5e351dce5b7129ee5a002ace58afe19e56ae1b2e5432933e5243755e512c7ade504ee61e4f1e372e4a5cfdee451171fe4279e13e403510ce3ef42d0e39552f0e3840ba4e3624776e31a7a5ae2f911b0e2b6d2f7e280ec37e254a19ee248aa56e230c8c7e1a01fa8e1151f08e111b6dbe0cbaf88e0cadf64e0bbc7c6e0930e9de07ca19ce064cc45
  | 6, 19 => 0xf5cbc9b9f5cbaefef5c1f3eaf5bdd01ff59108abf51cd756f4c89bddf4bb552ef4483035f418610ef3ef218bf3dfbe5ff3dd72f6f3b27adff33b5fd0f3020adff2d52de2f2c41b18f2b121c6f29edce5f279123cf249a559f208a2b9f195102ff171c893f16a2142f15a4793f0fcd1a5f05edfe3f052953bf042de66f03d9387f0010e1befc2e112ef9c1ff3ef321432ef099ce9eedca26feec40f0ceec22234eeaee916ee8adc3fee6cfdefee622b56ee5390f5ee2c8024ee1fa362ee1e2c58ee004e53edc88ddded86fa4eed52219ced4e20d2ed215bcfed1a88f1ecfa8274ecf2ba94ecef841fecc260f5ec6b46deec3e9026ebf03b1eebefca4bebcf7c01
  | 6, 20 => 0xffc703bfffc6e326ffabe638ff6c71b0fec6917efebe0ea5feaf7861fd80eb38fd64caacfd48403efce8a04bfcc6b47cfc97bf31fc250e5efc24bdbcfc1d5e2efc0c146cfbeed6c8fba53b3bfb2c7319fb237bfffaddb0c9fad62506fab903a7fa5422b6fa3b31f7f8d5ce41f890187ef87bafe7f86f3443f86d3d08f82e86a3f7f9dae8f7f41e79f7b3f210f7ae70fdf766edbbf716d4caf6e5cf63f6c92fedf6a1142df69dc9faf66fcaf6f6655c2cf6281cb5f61da697f5e5463cf5dadf09
  | 7, 0 => 0x11b4128d119811441187183a11761aa81134c93410d1aa960ff61b8b0fd4c3f50fc22fb60f8898390f79f41c0f3badb20efa46790e8414b20e57c7a70dfb96ef0de2aecb0db675560d9cbe430d91ebc20d61f2fb0d4d98860cf91d9f0cea20e10cc7aa850cb3009d0cabde0a0c867e660c6d390f0c22507d0c167f100bd753a90bb2ffb10b41c7720ae892150acf09dd0ab0afbb0a71f9560a029d7e09ee1b6f08d79a32089ab0f3087867580864c5e50762c3070754e4280733ffed06ecbabd06b07a03064612c7061ab28605c61dd6059e8b1703e36454033a727c02d5abde0291d00a024a740d023c952e01a603fb0198251c01013f360086a50c00649915
  | 7, 1 => 0x1fd3d3851f3d31db1ee4e3db1eb3facb1e8eec381e3d0e221e1aa3ae1e17d8601e08e1531d989e101d81c57f1d73f5661d094b741ca0b1831c93f14f1c53b96d1c1ffead1bea35011bde45011b8f7b921b78d4bc1b70b1901b61a0cd1b52f3321b1036f41a5d39541a45ab1d1a4058c31a2bfa9c19deb3e219b1d4481979f417196672e11923eb0b1922d7aa1900f429183e8305181aa94117d6fff4175a929b174ef90f170db67f16b50ee9168e69a21623f29c1606144c15ff8a4715f86a801561a43a141a4f1c1415063f1413d60814121a0c13b5da6d135211a2131bfefa1317dd2b12b8884a12ae5da312798028124e26351232479711eb7ccf11d74806
  | 7, 2 => 0x3055c0a62fc976f62fa1c82a2f7655c82f65d7a92f1362052edbd6b52ea6e42e2e9e70832e46479b2de85b922d90db782d014b912cf3c0ef2cf085992cdef6d92cae27f22c9946a22c50f8382bdd94e82a2213b229e942c429c478db292df8a128c04ce02889888f2882e2b227f341652774c460275958f22727707326e36c2426d2458e26beaf6f264ea12126488ebe261c309d259eb530258a6ea42509c4b8246ade96246554a62429651523a7fde623555d1c233e519823038dd422daf26b22c7351322c1b3a322521a04223682592219ec0a21e9d24d21a5f96820df43cc2081cc612064873a204aaf2d2046aaad203e530f203cd04e20292edb2014c644
  | 7, 3 => 0x4305883642b779a341d9fb7841d622d341a8390641a4b5d640db2d8b4079af63405c8f3d40455b7a3ffca0873f8b9abe3f49363a3f086e6d3d8620523d6d0b963d18fbc93d0124c93cedcf813c9f3cdf3c3d49423c39fd5e3b5624293b3c318a3acd3e823a8b9b213a8b1a653a861c993a3129ab3a305add3950034038ad846e3899ed18387c221637dd7e80378f31e8375fd1e836c744ae368990f73678c0eb363c57f4361b1af435d89aaa359f67e7359aee6d358e7c13358633f2357bcd573518dab134744a7f342cdee933ab0d08339be830333e196732f6275b32e7627a32ba82ac326a0621317141fd315024ba31381b073129ad3f30f26f0930ccd1eb
  | 7, 4 => 0x51a4e007516924ff51099cc651007c3a50c4b4ed50a706e85038abd64fb2394c4f9b055d4f943bc44f717d1d4f624ff44f57c7d64f0fba7a4ed5e3f64ec7de7a4ec05ebd4eb549044e79bd534e7327324e1db72a4e0e9fc94e00c0ea4dd111674d17706a4cd8ba054c854e674c4c79c44c173de94c1326ad4bff26be4bf147df4bb8974e4bb13b214b83a20b4b7591cb4b62f61f4b40518f4b02825d4ac0774d4a9691394a0d1974499cfa0a49226c8f49148db048f889f848f0bd7d48b0ac9d484e6acf475141bb472e33c146792c03466b4d244615666345c07cca457c5ed145179a8f44d9dfff44cd758b43cee64d43555fb0433f660a432891ef4309ffd8
  | 7, 5 => 0x64015902639cee926379a67663669d956336351163353df463275f15631f350062e07e9b6292bf226284e043626bc61861f427ee61aa33686129ea295f492eb65f2a63495edafec85ec2fe405e06e6065dc82fa15d9647d45d93d62e5d7bf2db5d3a46645d23bf8f5c91de815c0095e65b2acd595b0171135af03eb05ab946475aa8a6b95a73054d59e5330159d66aa0596bf2065943cbfb59051596584e132a5806ebe257ac7a6c56dbe56f567ee6cd5640306855df5df855a4d29e5592bd7c558b87505550fad054ed1c7554b47b9853b7a8b553b3d16b5342fdb7531915d1530ec13f52e996fb52acbe7d528ca242523dc211520a3fab51efbb6051d2062b
  | 7, 6 => 0x73f60c3a7341d2fd7333c42e73227b8e72dac58272b28339727daf3d72739f547263b2ee7260e48f721cd83371be65bd70ffce1070cdf07470946692707cee8d706753917005f1236fa6c90d6f6c29a26f69601f6ebe77696e9f1e276e38e6f66e1ad9ba6ddedbb86db8095f6d9b14bb6ce170276cd622c66c4b6e046bed6d236be1bd3a6bcb63fb6b89f08a6b7c11ab6b6909ce6b46b4d16adde2696a7ff6686a5eea176a510b386a4fc62d6a2a46cf6a0139de69f9213969c031bf69b2eaed69387cae68ff5c7d68b561d0683fb3fc67f1c0d3679d352a67425c6166fb4c91668c477066742ba7651506a464ffcc4e64cf00c564789948645092fc6449b75d
  | 7, 7 => 0x867726a18651842c8635a6fc862851b985f48e9f85520fcd8549f6d2850f030e8492c7cd844c1a2d83f048fb83c5bc52838341f483233d80830766bf82d3eb99828511a482739f208241b05981cc74a781bd8a2f804281917fe35f827fc0036d7fb9fc427f27d8097ecd8d627ebd26667ebbf6017e8559377e22428f7dd5c4a57db1e1917d776c2f7d356db97d33ff317cd372a07c3be1d57c0721267bc86ac17b2b17a17ab597257aa157477a70b1287a58579279a4d76c798a90b2791d9b417900675a7892577578493a7f77d135d077211a3f76fcab1e76f0de3376f0916b76eecc3f76db0b2e764692e675400898751c82e774f2245d74e1bd61749b9886
  | 7, 8 => 0x94331b6593f42b8d934043b8933bc3c7933451c192ef453392a6c201928df768927a567e926d751e9262028d925c0be491bec62691b98d1291a946d591426eab9074f28c906d26119037c66b900c696690061e318fe9ad8f8f9d1d5f8f7fd14d8f78512d8f255fd78ebf00228e6e30d28e4941358e2374cd8df2ab598dcbb2008d92f6958d7f04bb8d3d413a8d1e3ac28ce77a638c8386ea8c76bee98c1a6ee88bc68b508bbc73f08b8fda438b3e939c8b308e208aef68758a18c288899b6c72897643b689605ac289143e4288edfe0d88ede028881ad29987ec230287d8b03e87ca80ca87b12daa877c8a9f877910e2876b320387080352869b7594868cb424
  | 7, 9 => 0xa80fa957a80d4bfda8098f40a7bb98b7a77ce252a6877d59a661d0dfa623790ea5cabbeaa5103ec2a4a02823a3f2435da36baaf7a35f8a0fa302d5f5a2f4f716a2359dfca1f6e797a141bf77a0d63b5ba0c045e2a0b26703a0309aeba0059e389ffd08839e6bbe4b9de02fb29d3508f49d2d50bb9d2006f69ce015509c3d6b929c36144f9bfcd7929b9a2f2b9b71391a9aec1f2b9ab0be7a9a36658d99ed5e8799bbfbc99985b807996c23f498d83969985a34f797ec88bb97a5128c97a4f387978d297c97251c989721f5ed9710a45896e3fc3596c2e36896a4b77d9680ac86965531e69603a49895fe78aa9597dcf5956125c6955a08989502be16946763cc
  | 7, 10 => 0xba2399e2ba1f06b4b9782853b84d21e0b837fe7bb7610a65b749840db69fded2b604cd19b59a84ddb52557b8b4e46fecb327cb8cb2f03ccbb2dc7687b2b203c0b272f2abb2313513b2306866b22e7c90b1b17014b18cc501b12375bdb108215ab0ec7e1fb0e1dcffb080f6ebb07bc511b0480e0daffee213afebec7dafd2c793af01b67aaef43dc2aee65ee3ae5c9576ae0f7c92ae064aa9adab993dada32de2ad85a160ad6e1b08ad6b0c80ad1a90a7ace974c5ac296414ac23afedabe5308aabbe6e52ab962e79ab94b348ab681b8eaab1140caaa935daaa38618da9cb11c2a98e4816a98c5b5da9647ee6a94c6287a8e78fc4a8d9852aa8d69abba817ae6b
  | 7, 11 => 0xcae6d7d7cacb5047ca35eab9c9e65a89c8e779a6c8df6e8fc846bb6ac7a3ca76c7554d2ec707ac1ec6ea46f2c689fa79c6398efac5e58a67c5dca5abc5d3e588c5c226a0c59d6c30c5899ec0c57cede8c5690328c52f7576c4eae2e7c4605fcec398766ec3935453c37f968dc34f33b5c3334588c31b6fd9c23de552c21dcfbbc1c6e06ec1c5a5bec150c440c110cb7dc1043454c07ccfeebf4172fabf01fb40bef5700abef1afedbee065e9beb2f988be6b5265be4be64fbe3418b4be2639d5be1fe45dbe107ab6bddd5bacbd3f82f8bd2744b8bcf5d0c6bcc8e334bcb2dff7bc5e25f5bc545819bc18011abb3f92c0bab08b31baa8a17cba477786ba45dd7f
  | 7, 12 => 0xdd547ea2dd4db3aadd0995b1dbeeb34ddb53d48eda8fa153da7890dfda26b2c9d9ed2281d9eccea3d9e7a089d9b9b7a8d988b69cd986de71d96359b3d958a3e4d8f62b1fd8e7dfa1d87f9952d7d8277ed7c2c847d7c0c947d7661623d6890d25d62ad27fd5d7c256d5d13c99d58853add56748abd4fb6d4fd3fa20bfd3c1c38ed3a21f4ed38eac86d355d4ffd3152e0bd30f653ad27a66b2d2522cc3d229a3e5d1d3f658d1b38e6dd17f337bd0dd3a20d051c79bd0317033d010ef66cfe713d2cf9551ebcf84bc20cf6e15b1cf5856edceecb93fcecb96dfce6b8b90ce3bc8d3cdd2d617cdb20f90cd5fbf4fcc0fb7b2cc0b8b0bcbf938c0cba24973caec3482
  | 7, 13 => 0xf14d1f92f11d8484f0f10dbef0dd9aa2f0c2900ff05fc8f2f0107b11efdfd1c7ef907b32ef4adc1aef0e3eb4eec76f65eeae7dabee6bbfe2ee570e7dee22ff53edc88ddded5ae6a4ecfeda8beaf7dac4eabec0cdeaa64cb1ea782c38ea39f55dea04555ae9f23fa9e9d3bc26e8f19d4fe8b54ab1e7a75556e73f702ce73c37a0e7283c3de606f433e5b5122de575a6eae5179d48e48a3599e45c7de4e3ed24d8e3d420a8e33582dbe2f6cc76e2f02cffe2e94854e2e453e9e1e7aed7e1b94d76e0f3695fe0d9cf49e0d27efae07b344edfdba1afdfa5c541df91a28ddf6d0221dede789bded29fcddec49712de7f8515de1b0bb2ddfd151addd7f9c9dd7d8853
  | 7, 14 => 0xffcceadcffabe638ffa13466ff3df527ff3992a2ff24a7f5fed37441febf47eefe809189fe5cb65dfdf560cffd875a02fd797b23fcf8d17ffce2758bfcb0a9dbfc7cb7dbfc3e0176fbe5e7c4fac274d4fab903a7fab495f5faa130d0fa6ea56dfa58df1bfa3b31f7fa101145f9d3a84ef96feb04f9092d95f8b72109f80fe67ff7fbcecdf7c476a1f7c42f43f76d67adf762f14af725d631f6f16d4af6da4390f6657479f65fed09f646c3bff637ead7f5a8ee32f5210d0ef51b3615f4e77514f3e60244f3dfbe5ff39bac49f32a1730f30eb1d1f23e3488f1c1f496f17a65ebf171c893f15afe71
  | 8, 0 => 0xf33b5fd0f2854adfdee29a6add9de376dac0e1e9c3d681efbad4da24a6563cc3a1f16def8a7994f87cea112d5e22a75455df5df851bb2a0f5059633d4f8c57c24aee737942b779a33e277fff2efbd9642eedfa851e7359ed1b78d4bc1729918f
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0xc445484301000003108420100000310842010000031084201
  | 4, 0 => 0x5720c515480400000c445484301000003508520000000254c420300000454c4203000c44548430100000410c120c000000010910200000000c410100000000000050011931084301000000000000f71508520c54000000031084201001193108430100000000c4101714c8250414000000000109102000000000000200000000c41010000031084201000003108420100000324c820000000521052000000035085202521853210540000000000000050000031084201
  | 5, 0 => 0x2000000000000a000000000000400000000c410300000454c4203000000000000e0018532041300000000000000300000510812010000052105200000000000000f0000000000011000003508120100195420c030000194414c1300000000000000e000004540220100000000c81000000045402201000000000000a00000310842010000000000004000000000000b000004508520000000410c120c00000000000030000051081201000000000000d000000000001100000214c520600000310842010000000109106
  | 5, 1 => 0x109106000000010d10600000000c4101000003108420100000454842010000020480201000000000000c0000000000005000c825041300000000000000000000001081040000000000005000000000000a0000020480200000005210520000000454842010000000000005000000000000600000000c4101000003508520000000000c810c0000045402202000000000000b00000521052000000031084201000003148520600000454c42010000000000005000c515480300000000000000400000304c02000000045484201
  | 5, 2 => 0x50000000108104000000000000e000000000000b00000324c820200000000c410100185450c130000000450c1200000000000000f00000000000020000000000008000000000000d00000350852020000000000000000000010910600000410c120800000000c4101000000000000b000005210520000000524c4203000000000000500000000000010000000000003000000000000d000000008510200000310842010000045484201000000000000500000450812000000000000005000000000000a0000000000005
  | 5, 3 => 0x514c8202000000010810000000000c41010000000000006000000000000a0000021040201000000000000500000514c820200000000c5106000000000000400000000c1103000003508120100000000000020000000000005000000000000d00000304c020200000514c820200000521052000000000000005000000000000e000000000000300000000c510a00000504c4203000000000000d0000000000002000c44548430100000001091060000000109102000000000000500000454842010000000000004000000010d106
  | 5, 4 => 0x2000000000000e0000000108100000000000000b0000000000005000003108420100000454842010000000000002000000000000a001182540e3000000051508200000000000000d001853210530000000000c510a0000045484201000000000000500108520c5300000003508520000000310842010000031084201000000000000100000000c4101000000000000200000001091060000000108100000000000000b000000000000900000000000020000000000009000000010910200000454c4201000000000000b
  | 5, 5 => 0xf00000000000020000000000005001483210530000000000000050000000000011000000000000f00000000c510a00000504c820200185420c53000000000000001000000000210000000000c410300000000c410800148321053000000035081201000000000000600000000c110400000454c4201000000000000d00000450c9200000000010810000000454c420100000000000080000045484201000000008410100000000000050018831480300000000000000200000000c4101000000000000b0000045484201
  | 5, 6 => 0xe00000000c510a00000454c420100000000c810000000324c8200000000000000300000324c820000000000000050000045402201000000000000200194414c1300000003108420100000454c42010000000000007000000000000b0000035085200000000000000b00000454c4201000000000000d00000000c41010000035081201
  | 6, 0 => 0x81100000004508520000000450c1200000000000000b0000000000001000000000000e000000000000a00000450c12000000000000006000002540e2000000000000006000003508120000000324c82000000035085202000003104020100000304c02000000000109102000000000000000000454c4201000000000000e00000000c41080000000081101000000000000a00000324c82000000015480200000000000000100000000c5102000000000000500000058c8200000000000000c000003508520100000450c1200
  | 6, 1 => 0xc81000000000002100000000000000300000514c82020000000000008000000000000d0000000000006000001550020000000000c410100000000c8101000000000000a000000000000500000324c82000000000000005000000000000500000000c4101000000000000000000000c4101000000008410100000000c0101000000000000800000324c82020000000084101000000000000300000000000040000000000010000002148420100000000401010000031480200000000008010100000324c82000000052105200
  | 6, 2 => 0x45402201000000000000e00000000000030000000000005000000000a101000000008510200000000000080000045081200000003540a2000000000000005000000004110200000000c910200000000000000000000000002000004508520000000000000050000000002100000000000000e0000035085201000000000000b000000000000d00000454c820200000324c820200000000000050000002905200000000000000a000000000000600000420802000000000080101000000000a10100000350852000000045402201
  | 6, 3 => 0x104402010000035081201000000000000100000324c820000000000000060000000000002000000000a1000000000108100000000008510200000420c0200000000000000d000000000a1000000000000005000002048020100000304c0200000000000000d000000000000b000000000000100000000c410100000000c0102000000480a2000000045085200000000000000700000001051000000000000005000000000000e000000000000200000414c1200000000000000a00000001081000000010440201000000000000a
  | 6, 4 => 0x5000000000000500000000c410100000000000010000000000008000000000a10200000001081000000000000010000000000000700000304c020000000000c5106000000000000300000001091020000000000005000000000000600000000000030000000000005000000000000e000004508520000000450c1200000002048020000000000000060000000000004000000000000800000414c1200000000000a101000005150820000000000c41010000000000006000000000e1000000000000002000000000a100
  | 6, 5 => 0x30000051081201000000280620000000000c910200000304c020000000304c0200000000000e1020000000000003000004508120000000304c0202000000000000f0000000000005000005210520000000000000030000000000002000000000000600000304c020000000000c81000000000000000000000000000600000521052000000000000009000004540220100000001091020000000000002000004500e200000000008410100000454c8202000004548420100000521052000000000000005000000000e100
  | 6, 6 => 0x515082000000000006100000000000000a000000000000b000000000000a000000000000900000450c92000000000108100000000000000a0000000000003000003504120100000048062000000000084101000000000001100000420c0200000000000000a00000420c8200000000000000500000000000010000002905200000000000000f000000000000100000000000060000000000008000000010810000000001091020000000000006000000000000a00000000000060000051508200000000000000500000454c8202
  | 6, 7 => 0x5000000290520000000000000090000035085200000000000000b0000000000003000000000000500000000000060000000000005000000000000500000520c1200000000000000a0000000084101000003548020200000000000030000031084201000000000a1010000000000001000000000000d000000008410100000000000050000000000008000000480a20000000000c8101000000000000200000354802000000010440201000002048020000000000c11020000000084101000001540e200000000000000b
  | 6, 8 => 0x600000420c8200000000010810000000000c8102000000000a102000005150820000000000000080000000084101000000000000b00000414c120000000414c1200000000000000a00000000000050000000084101000000000e1020000000000005000000000210100000000000030000000000006000002500e20000000000000010000000000006000000000000c0000000000005000000000610200000001091020000035085200000000000a10100000000000050000003905200000003540a2000000000000003
  | 6, 9 => 0xb00000204802000000045484201000000000000d00000000c1103000000008410100000000c8102000000000e10200000000c41010000003841200000000000a101000000008510000000304c020000000454022020000003802200000000000000a00000000c0101000000000000500000304c020200000000c9102000000000000200000000000030000000000008000000000000200000000411000000021484201000002048020100000000841010000052105200000005150c200000000540a2000000000000003
  | 6, 10 => 0x450c920000000515082000000000108104000000000000f00000000000020000000000003000000000001000000155002000000000000006000000000000b000000008510200000324c8200000000010810000000048062000000000000003000000000000600000450c120000000000c410100000000c5102000000000000e00000001081000000000000005000000000a1010000002806200000004540220200000000c110300000304c020200000001081040000000000005000003504120100000450812000000000000004
  | 6, 11 => 0x454c420100000450c120000000000c41010000000084101000000000000b00000000c4101000000000000b000000000000c00000000c41010000035041200000000000000b0000031084201000000010910600000000c4101000000000000300000000000000000000002100000000010810000000304c020000000000000040000003908200000000000000a000000000000d000000000000500000350812010000000000000000003508120000000514c8200000000000000800000454c420100000000000000000000000005
  | 6, 12 => 0x5150820000000000000000000051508200000003208020000000000000030000020480202000004548420100000000c810200000000c4101000000000610100000104402010000045081200000005150820000000000000030000000000006000000000210100000450c1200000000000000200000450c9200000000000e1010000000108100000000000000300000000021010000000000006000000000e10200000000c510600000000c810200000450852000000000085106000000000000500000000061020000000000008
  | 6, 13 => 0xc410100000250412010000000000003000000000000d00000000841010000000000001000000008010100000204802020000035085202000004200220000000520c12000000035085202000000000000d000000000000600000304c020000000000000080000000105100000000380220000000000c41010000000000003000005210520000000000000050000051508200000000000000600000001091060000000040101000000000000e000000000000b000000000000f000002048020000000000c91020000000084101
  | 6, 14 => 0x9000004548420100000420c520000000000c51060000035480200000000390820000000000000030000000000001000000000e10200000000000010000045081200000000010d1060000000084101000000000000a000003508120100000450c1200000000000000500000000851020000020480200000000000000a00000520c5200000000000000d000000000210100000000c4101000003508520200000000c510200000000c4101000004540a2000000000000006000000000a10100000000000050000000000000
  | 6, 15 => 0xb00000450c9200000000000000d000001044020100000000c41010000000000007000000000a100000000000000500000000c41010000000000008000000000000300000450812000000000000002000000000000000000000000050000000000005000000000000e00000001051000000003908200000000000000500000038802000000000000003000000000000b000000000000200000000c810200000324c820200000450812000000052105200000000000000e0000020480200000003550020000000000c4101
  | 6, 16 => 0xd00000450c92000000000105100000000000000a0000020480201000000000000e0000000000001000000000000b000000000000600000000c010100000000000030000000000003000000000000400000450c9200000000000000d0000000000005000000000000d00000000000020000000085102000000000000300000001081000000051508200000005150c200000000000e1000000000012100000000000000000000000000020000000000006000000000000a0000000002102000000004010100000000c1102
  | 6, 17 => 0xd000000000000a000000010910200000000c11020000000000006000000000000a000004540a2000000000000000000000004010100000250412000000000000003000000000000c0000000002100000003508520000000000c410300000254c02010000000080101000000000000600000450852000000000000004000000000000400000000000050000000105100000000010d1060000000000001000005150820000000450c12000000000000008000000000000800000000401010000032105200000000000000a
  | 6, 18 => 0x2000004540a20000000000c51060000000000005000003210520000000324c8200000000000000300000000000020000000000002000003508520000000450c1200000000000610000000000c4101000005210520000000000000020000000000000000000000000200000000841010000000000000000000000000b00000454c8202000002048020100000000c4101000000000000d00000454c4201000000000210000000000401010000000000003000000000000b0000000002102000000000000b00000454c4201
  | 6, 19 => 0xb000000000000b000000000000a00000000c410100000000c810000000000c8100000000000000e0000000000005000000000000d00000000c41030000000000005000000000000a000000000000300000450c1200000000000000600000000841010000035500200000000000210000000450c920000000000c91000000035480200000005150820000000000c410100000000061010000000084101000000000000500000000c9102000000000000e00000000021020000000000006000000000e10200000454c8202
  | 6, 20 => 0xc0000000000003000000004010100000000c41010000000000006000000000000a000000000000a000000000e1010000000000005000005210520000000000000040000000000003000000008510000000454c420100000001091060000051508200000000000000500000000c51000000000000005000000000000e000000284120000000000000010000000000006000000000000500000000c4103000000540a200000000000a100000000010d10600000000c1103000002504120000000000000060000035508200
  | 6, 21 => 0x35085200000000000000500000450c12000000000000004000003504120100000454022020000000000003000000480e200000000390820000000000000050000020480200000000000000b0000035041200000000008410100000000000070000051508200000000000000b0000000000005000000000000b000000380a20000000000c41010000000000003000000000000900000000c5106000000000000f00000000811010000000000001000000008410100000000c5102000004508520000000039052000000000000006
  | 6, 22 => 0xe000000010d10600000204802020000000084101000000000000d0000052105200000005150820000000000000000000035085200000000000000b00000000000050000000000004000000010c100000000000e1020000035085200000004508520000000304c02020000000000006000000000000100000324c8202000000000a10200000000000060000000000006000000000e10000000000c410100000001081000000000000006000000000e1000000020480202000000000000a00000520c52000000000000000
  | 6, 23 => 0x324c82000000000000001000000000000d000000000000b00000000061010000000000005000000390520000000350412010000000000011000000000e102000000000000300000454c42010000052105200000000010810000000000c4103000000000000b00000324c820000000000801010000000000003000000000000400000058c8200000000000000d00000000c810000000000000000000000000005000000000000500000000c8100000000000000600000000c1103000000000000500000414022000000000000005
  | 6, 24 => 0xe000000000000000000000000020000000000005000000380a200000000004010100000450c920000000001081040000000000006000000000000500000000000060000000000005000000000000e000000000e10200000154802000000000000006000000000e1010000003905200000000000000300000000000060000000084101000000000e1010000000000005000000008510600000000c4101000000000210100000038062000000000000006000000000000e000004200220000000000c410800000000c4101
  | 6, 25 => 0x30000000000002000000000210000000000000050000020480201000000000610100000000c410100000450852000000000000004000000000000500000000c4103000000000000300000350852020000000000005000004540a20000000350852000000035085201000000000000500000304c0200000000480e2000000000000003000000000000a0000003880200000004208020000000000c4108000000000000800000000000030000000000005000000000000d000000000000300000000c41010000051508200
  | 6, 26 => 0x200000454022020000000000006000000000000d000003540a2000000000000011000000000e102000000000000d00000000c1103000000000000c00000000c410100000454c42010000000000002000000000000300000000c8100000004508520000000058c82000000052105200000000000000300000000841010000000000005000000000000900000000000030000045085200000000000000d000000000000e000000000000500000000000030000042080200000003550820000000000000030000035081201
  | 6, 27 => 0xc410100000350812010000000000004000004540220100000000021010000003806200000000000000e000000000000b0000000000006000000000001000000000000050000000000004000000000a10200000000c81020000051508200000000000000b00000000c410800000000c8101000000000000200000000c4103000000000210000000058c520000000324c820200000324c820200000000c5102000000000000300000324c8200000000000000300000000c510200000000c4101000000008410100000304c0200
  | 6, 28 => 0x520c520000000515082000000051508200000000000000800000000000010000045484201000000000000f0000025041200000000000000a00000000c5106000002540620100000001001000000000000002000000000000e0000000000002000002048020000000450c9200000000008010100000154c020000000000000020000000000004000003508520100000450c920000000000c410100000000c41080000000000006000000000000b000001541220000000000c4101000005150820000000000000050000000002101
  | 6, 29 => 0xc410100000000c11020000000000003000000000a10100000350412010000000000008000000000000b0000000000006000000000000800000000c4101000000000000800000000c4101000000000000e00000000000010000000000007000000000000300000000c010100000000c4101000002500e200000000000000500000000c9102000000000000600000350852000000000084101000000000000d0000000000000000000000a102000000000000f0000035085201000000000000200000450852000000000000006
  | 6, 30 => 0x8510200000000c1102000000000000e00000304c020000000000c8101000000000000d0000045402201000002048020000000000c810000000000000040000000000006000000000a10200000450c920000000304c02000000000000008000000000000600000000c8100000000000000300000000000030000000000003000000000e1010000002802200000000008010100000000c4101000000000000a00000454c820200000454c8202000000008410100000000000000000020480200000000000000b0000051508200
  | 6, 31 => 0xc410800000000c51060000015412200000002148420100000000000060000000000003000000540e200000000000000a0000000084101000000000000600000001091020000000000006000000000000300000454c4201000000000000b00000355082000000000000005000000010d106000000000000b000000000000300000000000000000003905200000000500e20000000001081000000045081200000000000000b000000000000d00000000c810100000059082000000035085200000000004110600000000c8101
  | 6, 32 => 0x324c820000000001091020000015480200000000000000300000000000060000000000005000004200a20000000454c420100000000841010000000000006000000000000d0000000000005000000000e100000000000a1000000015480202000000000000200000000000060000035085200000005150820000000000c41010000020480200000003550020000000000000020000035085200000000000000d0000000000008000000000000d000000000000d000000000000a000000000000600000000000050000000000001
  | 6, 33 => 0x18022000000000000008000000000a102000000004010100000000000020000052105200000000008010100000000000030000000000001000001540e20000000214842010000000000005000000000000600000001091060000000109102000000000e1000000000081101000000000a10200000154802000000000000000000000008410100000000401010000000000006000000000000b000000010d106000000000a1020000000000004000000000e101000000010810400000450c920000000000000100000045081200
  | 6, 34 => 0xa1010000000000006000000280220000000000c41010000000000003000000010910200000304c0202000000000000100000000c010100000000c11020000000000005000000000a10100000304c020000000000021000000000000005000000000000f000000000000f000000010810000000324c82000000041402200000001548020000000000000080000000006102000000010810000000450c920000000058c5200000000000000a00000324c8200000000000000b000000008010100000000000050000000002102
  | 6, 35 => 0x851060000045484201000004208020000000000c8101000000000000a000000008010100000304c02000000021484201000000000000900000000c4101000004508520000000000c11080000000000003000000000000a0000000000005000000000000600000000841010000005908200000003508520000000000000080000000000006000000000000c00000048022000000035085200000000000000000000454c42010000000084101000000000000d00000000000030000000000008000000000000b0000020480200
  | 6, 36 => 0xb0000000000005000000008010100000000000040000045081200000004200a20000000000061020000002880200000000000000b0000045402202000002504120000000000c510600000304c020000000320412000000045402201000003550820000000154c0200000000000000d000000000000d00000514c8200000000010910600000000c4101000000000000e0000005908200000000000000300000000841010000042006200000000000000600000450c12000000000000002000000010810000000000c1103
  | 6, 37 => 0x1000000000000b000003508520000000000c4101000000000000a00000000c910200000000c4101000000000a102000000000a101000004540220200000450c1200000000000e102000000008410100000450812000000045484201000000000000200000324c820000000154c020000000000000030000045081200000000000000a000000000000600000000c41010000000000006000000000000100000000c010100000000000080000045081200000000000000b000002148420100000324c8200000000000000b
  | 6, 38 => 0x8000000008410100000000c410800000000c010100000000c41080000000000005000000000000e000000000000b000000000000600000420c52000000003908200000001550020000000355082000000000000009000000010d10600000000801010000000080101000004200a2000000000000003000000000000800000000841010000020480202000005150c20000000000c410100000001081000000000080101000000000000b000002048020000000000000080000000000001000000180220000000000c4101
  | 6, 39 => 0xf00000000c410100000000000030000045085200000000000000b00000324c8200000000000000400000454c4201000000000000a000000000000500000000851020000042006200000000000610200000000000090000000000002000000000a102000000384120000000000c51020000000000005000000000a101000000000000d00000304c0202000000000000b0000000000004000000000000800000000c110800000000c010100000000000050000000000005000000000000600000000c01010000000084101
  | 6, 40 => 0xc81010000045484201000000000000600000000021010000000084101000000000000b00000000c41010000005908200000000000000d00000450c92000000000040101000004200620000000000c41030000001880200000000000000500000000c41010000035085200000000000000b0000000000005000000000e1000000000000008000000010d106000000000000800000000000050000000000004000000000000b000000000000200000000c81010000000000003000000000000500000000000060000000000005
  | 6, 41 => 0x6000002048020100000000c4101000000000000b0000035085200000000000000600000000c4101000000000000800000000841010000000000000000004508120000000000c41010000000084101000000000000800000521052000000000000005
  | 7, 0 => 0x5000000000610000000000000030000000000008000000000000d000000008410100000001051000000000002100000000000000200000000000050000000041100000000000610000000000c41010000000108100000000008010000000000c9102000000000000a000000000000600000000000050000000000001000000000000300000000851020000000000006000000010c100000000000000b000000000a101000000000e1000000000006101000000000a100000000000000200000000811000000000085100
  | 7, 1 => 0x10810000000000c11000000000000006000000000e10000000000c9100000000000a1000000000000005000000000000500000000411000000000012100000000000000300000000000080000000002100000000000000100000000c910000000000000020000000000002000000000000d0000000000003000000010c100000000000a10200000000811000000000000008000000000e10000000000000010000000108100000000000a1000000000006100000000000000b000000000a1010000000000006000000010c100
  | 7, 2 => 0x100000000c110000000000c110000000000c5100000000008110200000000c010200000000000020000000000001000000008510000000000000080000000002100000000010810000000000c5100000000000e10000000000061010000000000002000000000a100000000008110000000000000020000000100100000000000000600000000c01020000000080100000000000210000000000021000000000081102000000000000100000000c910000000000c1102000000000000600000000411010000000002100
  | 7, 3 => 0x20000000000006000000000000200000000c1100000000000e100000000000e100000000008010000000000c41010000000000002000000000a100000000000210000000000000050000000000006000000000000a000000000000a000000008010000000000021020000000000001000000000000a000000010810000000000061000000000085100000000000000300000000021010000000000005000000000000200000000c5100000000000000300000000851000000000000005000000000a1010000000108100
  | 7, 4 => 0xc9102000000000210000000000c8102000000000000100000000c9100000000010c1000000000000001000000000e1000000000000002000000000a1000000000000003000000000e10200000001081000000000000006000000000a102000000000a1010000000000003000000010c10000000000000050000000006101000000000000b00000000c81020000000002102000000000610200000000811000000000000006000000000000100000001081000000000000002000000004110000000000061000000000000003
  | 7, 5 => 0xb000000008510200000000801010000000041100000000000000100000000851000000000100100000000010510000000000c5102000000000000200000000c510000000000000030000000000002000000000e1010000000000000000000000000a000000010810000000000c01000000000000006000000000000d000000010810000000000021000000000000008000000000e1020000000000002000000000a102000000000000800000000c4101000000000210200000000000010000000041100000000010c100
  | 7, 6 => 0xa100000000000e101000000010010000000000000050000000080100000000000000a0000000108100000000000000000000000c110000000000801000000000000000000000000610100000000c0100000000000e10200000000000020000000000002000000000000e000000000000d000000001210000000000000050000000000003000000008010000000000000010000000100100000000000000a0000000000008000000000e100000000000a10000000000c9100000000000e102000000010c100000000000a100
  | 7, 7 => 0xa000000000000000000000000030000000000003000000000000100000000000060000000000001000000000000a0000000006100000000008510000000000c8101000000000a1000000000041101000000000000800000000c1100000000000000300000000000020000000000001000000000000200000000121000000000041100000000000000600000000c0100000000000000200000000c810000000000811010000000000006000000010c100000000000000b000000000000300000000000030000000000006
  | 7, 8 => 0x801020000000000008000000000000100000000c410100000000021000000000000000000000008010000000000c91000000000105100000000000e100000000000000e0000000006101000000000a1000000000000006000000000000600000000021010000000002102000000000210000000000411020000000000001000000010510000000000000060000000000003000000000000b00000000000020000000000006000000000610000000000c81000000000000001000000000000500000000000000000000041100
  | 7, 9 => 0x100100000000000000e000000000000b000000000e100000000000000a00000000c0100000000000a101000000000210100000000000030000000006101000000004110000000000c0100000000000000b0000000085101000000008110000000001001000000000000006000000000000600000000000030000000000000000000000000e000000008110100000000c11000000000000006000000000000b000000004110100000000c01000000000000006000000000610000000000c8100000000000e1010000000012100
  | 7, 10 => 0x10000000000000000000000000d00000000c510000000000c5102000000000000200000000c4101000000000a100000000000000100000000000060000000000001000000000000b000000000210100000000121000000000105100000000010c10000000000c110000000000c4101000000008110200000000000080000000085100000000000000500000000000030000000000003000000000e1000000000100100000000000210000000000c5100000000000210100000000c910000000000000060000000000002
  | 7, 11 => 0x41100000000004110000000000c81010000000000001000000000000800000000021010000000002100000000000000500000000c4101000000008510100000000c91000000000105100000000000000500000000000010000000002100000000000a101000000010c10000000000c81000000000000005000000000000d000000000a10100000000c81000000000000003000000000610100000000c11000000000006101000000000610000000000c110200000000121000000000085100000000008510100000000c8100
  | 7, 12 => 0xa100000000000610000000000000010000000085100000000000000300000000000030000000084101000000000a102000000000000100000000c5100000000000000e000000000000000000000c1100000000000e100000000000000b00000000061010000000105100000000000a102000000008110200000000000030000000012100000000000000a000000000000200000000000080000000100100000000010c100000000000a10000000000c010200000000c91000000000000001000000008110200000000c0100
  | 7, 13 => 0x40101000000000000300000000c810200000000c81020000000000006000000004110000000000c8100000000000000000000000000050000000002100000000000210200000000c9100000000000000500000000c1100000000000000100000000000020000000000006000000000a102000000008010000000000c11020000000000001000000001210000000000811010000000000001000000000e10000000000000060000000002102000000000000a0000000000000000000000e10000000000000080000000000003
  | 7, 14 => 0xe100000000000000800000000c1100000000008110000000000851000000000000001000000000000b000000000000100000000000010000000085100000000000610000000000000050000000000002000000000e10200000000c51000000000000003000000000a1020000000006100000000000a1000000000000003000000000000200000000c810100000000021000000000080100000000010c10000000000000030000000000005000000000e102000000000000500000000c11020000000000002000000000a102
  | 7, 15 => 0x100000000c51000000000081100000000010c100000000000210000000000c9100000000000000200000000000060000000002102000000000000500000000c9102000000000210100000000061020000000085101000000000000b000000000e1020000000000008000000000e10200000000000080000000105100000000000e1000000000000008000000000000600000000c010200000000000050000000002100000000000000b000000000000200000000c510000000000c910000000000000010000000000003
  | 7, 16 => 0xd000000000a100000000008010100000000c510000000000000010000000000003000000000000000000000000010000000006100000000000000100000000000010000000081100000000010010000000000000010000000002102000000000000800000000c91020000000108100000000000000500000000c01000000000000008000000010010000000000000000000000000001000000000000d0000000000003000000008510000000000401010000000080100000000000a10000000000021000000000000000
  | 7, 17 => 0x81100000000000000b000000004110200000001081000000000000002000000010c100000000008410100000000000020000000100100000000008510200000001081000000000002100000000000000500000000c9100000000000000200000000c51020000000000006000000000000600000000c010000000000000080000000000001000000000a100000000000210000000000c0101000000000000300000000000050000000000002000000000000f0000000085100000000000e1000000000000003000000000000a
  | 7, 18 => 0xd0000000081101000000000000b0000000084101000000000000100000000851000000000000003000000000e101000000010c10000000000c51000000000000006000000000000e000000000000200000000411000000000041102000000000000300000000c8101000000000e10000000000c81000000000006101000000000000300000000000010000000080100000000000a10000000000000020000000000003000000000000d0000000000001000000000000e000000000000600000000000080000000000001
  | 7, 19 => 0x6000000000000300000000401010000000000002000000000e1010000000002100000000000e100000000010c100000000000000300000000000030000000006101000000000000a0000000080100000000000a10100000000c010100000001001000000000000002000000000000100000000811000000000000002000000008010100000000c010000000000000020000000041100000000008110000000000c810000000000000020000000081101000000000000e000000008110000000000000060000000108100
  | 7, 20 => 0x85100000000008410100000000c81000000000080102000000000e1000000000000001000000000e100000000000000300000000000020000000108100000000000a10000000000c010000000000000010000000108100000000004110000000000000050000000000001000000000000500000000000030000000000006000000000a10100000000021000000000080100000000000000b00000000000030000000081101000000000210000000001081000000000000003000000000000600000000801020000000000002
  | 7, 21 => 0xc910000000000c510000000000000010000000000001000000000000f0000000000002000000010810000000000801000000000108100000000008110200000000411000000000081100000000010810000000000801000000000000006000000000000f0000000000003000000000e10000000000000060000000100100000000000000a000000000a100000000000210100000000c0101000000000e10000000000000010000000085101000000000a102000000000a100000000010c10000000000c01000000000000006
  | 7, 22 => 0x200000000000080000000080101000000010810000000000c1102000000000a102000000000000100000000021020000000100100000000000000b0000000000000000000000210100000000c41010000000002100000000000a101000000000e10000000000c810000000000851010000000000001000000000a10000000000000030000000040101000000000000500000000c010000000000000020000000000003000000000a10200000000000020000000002101000000000000100000000000030000000000003
  | 7, 23 => 0xc81000000000080100000000000000600000000000020000000000003000000000000000000000c410100000000c010200000000000020000000000001000000000e102000000000e1020000000000002000000000a1020000000000001000000000e100000000010010000000000801000000000000008000000010810000000000c1102000000000a10000000000c81010000000000002000000000000500000000c010100000000c010000000000c510000000000000030000000000001000000000000800000000c0102
  | 7, 24 => 0x6000000000000300000000000020000000000008000000000000500000000c810100000001051000000000100100000000008110000000000c8100000000000000f000000000000300000000c81020000000041100000000000000100000000c010000000000061020000000084101000000000000300000001081000000000041100000000000000600000000c8100000000000000200000000000010000000081100000000000e100000000004110000000000c8100000000000000f00000000000020000000108100
  | 7, 25 => 0xc51020000000000008000000000000b00000000c010000000001051000000000002102000000000e100000000000e10000000000c9102000000000000800000000c110000000000411010000000081100000000000000500000000000030000000000003000000004110200000000121000000000000008000000001210000000000000060000000000006000000000a100000000000000d000000000210200000000c8102000000000000300000000c91020000000040101000000000a10000000000061020000000000002
  | 7, 26 => 0x3000000000000300000001081000000000000006000000000e1020000000041102000000000000600000000000060000000041100000000000000b0000000040101000000000210000000000c11000000000085102000000000000600000000c5102000000000e10000000000121000000000081100000000000000600000000021020000000000005000000000e102000000000000300000000021000000000000002000000000a101000000008510200000000c8100000000000a10000000000411010000000000006
  | 7, 27 => 0x81100000000000a10000000000c01010000000000005000000000000e000000000000600000000000050000000000001000000010810000000000000060000000002100000000000a101000000008010100000000c9100000000000000200000000061010000000000006000000000e1000000000108100000000000000300000000411000000000000003000000000e100000000000210000000000c41010000000000002000000000a10000000000000000000000000003000000000000200000000021010000000080102
  | 7, 28 => 0xc11000000000000000000000000a100000000000210000000000021000000000000001000000000a100000000001210000000000c9100000000008510000000000000020000000108100000000010810000000000000030000000105100000000000000600000000c5100000000000000e00000000000060000000105100000000000a100000000000000500000000c41010000000000002000000000000200000000000060000000105100000000000e100000000000610000000000000080000000041101
  | 7, 29 => 0x3000000000000500000000c1100000000000000600000000c510000000000000020000000080102000000000000200000000c0101000000000000600000000c110000000000c410100000001081000000000000005000000008410100000000c1100000000000000b000000008010100000000121000000000002101000000000000500000000021000000000012100000000008010200000000000060000000000006
  | 8, 0 => 0x200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000002000000000000100000000000010000000000000000000000000200000000000000000000000002000000000000100000000000000000000000000000000000000000000000000010000000000000000000000000000000000000010000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_9 roots_9 8 s ws hint
  | 1 => checkCutEntry dom_13 roots_13 7 s ws hint
  | 2 => checkCutEntry dom_17 roots_17 7 s ws hint
  | 3 => checkCutEntry dom_19 roots_19 6 s ws hint
  | 4 => checkCutEntry dom_21 roots_21 6 s ws hint
  | 5 => checkCutEntry dom_22 roots_22 6 s ws hint
  | 6 => checkCutEntry dom_23 roots_23 6 s ws hint
  | 7 => checkCutEntry dom_8 roots_8 5 s ws hint
  | 8 => checkCutEntry dom_5 roots_5 5 s ws hint
  | 9 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 10 => checkCutEntry dom_10 roots_10 5 s ws hint
  | 11 => checkCutEntry dom_18 roots_18 5 s ws hint
  | 12 => checkCutEntry dom_20 roots_20 5 s ws hint
  | 13 => checkCutEntry dom_24 roots_24 5 s ws hint
  | 14 => checkCutEntry dom_25 roots_25 5 s ws hint
  | 15 => checkCutEntry dom_4 roots_4 4 s ws hint
  | 16 => checkCutEntry dom_11 roots_11 4 s ws hint
  | 17 => checkCutEntry dom_16 roots_16 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_26 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_22 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_26 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_26 == dom_26) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_26 goalM u ys) : RunD dom_26 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_26 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
theorem z4_16 : ∀ i, 16 ≤ i → i < 22 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 16 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 22 → Z 4 i = true := range_split z4_0 (range_split z4_8 (z4_16))
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
theorem z5_48 : ∀ i, 48 ≤ i → i < 52 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 48 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 52 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (z5_48))))))
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
theorem z6_168 : ∀ i, 168 ≤ i → i < 172 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 168 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 172 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (z6_168)))))))))))))))))))))
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
theorem z7_160 : ∀ i, 160 ≤ i → i < 162 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 160 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 162 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (z7_160))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 22 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 16 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 22 → Z 8 i = true := range_split z8_0 (range_split z8_8 (z8_16))
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
  scr dom_26 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_26 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_26 roots_26 goal_26 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_26 goal_26 := by
    have h0 : isConstB dom_26 goal_26 = false := by decide +kernel
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

end S_26

theorem low_26 : Lower dom_26 roots_26 goal_26 10 := S_26.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_26_bits : ∀ r : Fin 64, roots_26.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_26_lt : ∀ r : Fin 64, dom_26.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_26 T)
    (hlow : Lower dom_26 roots_26 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_26, Avail mask256 roots_26 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_26 hfan 0 roots_26 roots_26 rfl hsup0
  set out := (execN C.gates roots_26).getD C.output 0
  have hout : out &&& dom_26 = T &&& dom_26 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_26_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_26 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_26_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_26).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_26)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_26.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_26 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_26).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_26 &&& mask256 = dom_26 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_26 = T &&& dom_26 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_26, hd63, hout]
  have hnc_m : ¬ IsConst dom_26 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_26 roots_26 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_26, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_26 roots_26 0 roots_26 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4242599104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_26.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_26 10 hT6 (by unfold IsConst; decide) low_26

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [1, 12]⟩, ⟨GateOp.and, [13, 11]⟩, ⟨GateOp.or, [9, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_16725_aux

theorem PEqualNP.Outside.L_meta_16725 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4242599104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4242599104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_16725_aux.wit, PEqualNP.Outside.L_meta_16725_aux.wmono, le_trans PEqualNP.Outside.L_meta_16725_aux.wsize (PEqualNP.Outside.L_meta_16725_aux.lower s hs), PEqualNP.Outside.L_meta_16725_aux.weval⟩
