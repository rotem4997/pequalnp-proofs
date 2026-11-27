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

namespace PEqualNP.Outside.L_meta_16013_aux

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

def dom_0 : Nat := 0x55550000
def goal_0 : Nat := 0x54400000
def roots_0 : List Nat := [0x44440000, 0x50500000, 0x55000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(18, 22), (18, 26), (20, 22), (20, 28), (24, 26), (24, 28)]
def r1sG : List Nat := [18, 18, 20, 20, 24, 24]
def r2sG : List Nat := [22, 26, 22, 28, 26, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x27cf59fb
  | 3, 0 => 0x27cf59fb
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5500000000000000505000000000000044440000
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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

def dom_1 : Nat := 0x55555555
def goal_1 : Nat := 0x54404440
def roots_1 : List Nat := [0x44444444, 0x50505050, 0x55005500, 0x55550000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x55550000, 12, 28)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0xff00ff
def goal_2 : Nat := 0xe800e0
def roots_2 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_iso [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xffff0000
def goal_3 : Nat := 0xfce80000
def roots_3 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000, 18, 19)] (by decide +kernel) (by decide +kernel) low_0

def dom_4 : Nat := 0xffff
def goal_4 : Nat := 0xece0
def roots_4 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

namespace S_4
def pairsG : List (Nat × Nat) := [(1, 5), (2, 6), (2, 10), (3, 7), (3, 11), (4, 5), (4, 6), (8, 10), (9, 11), (9, 13), (12, 13), (12, 14)]
def r1sG : List Nat := [1, 2, 2, 3, 3, 4, 4, 8, 9, 9, 12, 12]
def r2sG : List Nat := [5, 6, 10, 7, 11, 5, 6, 10, 11, 13, 13, 14]
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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

def dom_5 : Nat := 0xffffffff
def goal_5 : Nat := 0xfce8ece0
def roots_5 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_5
def pairsG : List (Nat × Nat) := [(1, 5), (2, 6), (2, 10), (3, 7), (3, 11), (3, 19), (4, 5), (4, 6), (8, 10), (9, 11), (9, 13), (12, 13), (12, 14), (12, 28), (17, 19), (17, 21), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 26), (24, 28), (25, 27), (25, 29)]
def r1sG : List Nat := [1, 2, 2, 3, 3, 3, 4, 4, 8, 9, 9, 12, 12, 12, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 25, 25]
def r2sG : List Nat := [5, 6, 10, 7, 11, 19, 5, 6, 10, 11, 13, 13, 14, 28, 19, 21, 19, 22, 26, 21, 22, 28, 26, 28, 27, 29]
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
  | 3, 0 => 0xad1bb9739e34e7fb22d83a7221830673
  | 4, 0 => 0xf0b2ef13b9ea831fb0acf07da45dd1cb8fe29d1d804147d875616bdc622d3a095c7af21656ba86e85284960d4f8b6766423bf0db4142f00a30ad3e4c2a2deaeb158632870bd9fad805f76b690316dd3a
  | 5, 0 => 0xf0b2ef13e84cd5f5bd9dd4e5b2878a8aa3e82e789e9c03b29e9267f79b70605193c0f7228f6b7fb17ecfa183744473ec718e98da6baa581364d48033649f4cab62f275ca62b9685c5d1295e953baf88c537bfbe75299e96d46836c3c4595136344a78f1f32f633fb30b39f272596f91122894d34210a77a11f6c5e8b1cd6e59f1ac7d7cf18b8e630186f73eb1586328715436e13141aecf1125300860fd67280049ac07003d2ccb1034963b1
  | 6, 0 => 0xc5159104b4992a82ac05225eaa29454193c0f7227ecfa183744473ec5299e96d3a6b8d41206585ea0241d3e1
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x11111111000000000f0f0f0f000000000c0c0c0c000000000505050500000000030303030000000000ff00ff0000000000550055000000000000ffff
  | 0, 1 => 0xc8c8c8c800000000c0c0c0c000000000afafafaf00000000aaaaaaaa00000000a8a8a8a80000000055555555000000003f3f3f3f0000000033333333
  | 0, 2 => 0xeeeaeeea00000000eaeaeaea00000000e0e0e0e000000000cfcfcfcf00000000cccccccc00000000ccc8ccc800000000ccc0ccc000000000cc88cc88
  | 0, 3 => 0xfafaaaaa00000000fafa000000000000f0f0f0f000000000f0f0000000000000f0c0f0c000000000f0a0f0a000000000eeeeeeee00000000eeeeaaaa
  | 0, 4 => 0xff03ff0300000000ff00ff0000000000fefefefe00000000fcfcfcfc00000000fcfcf0f000000000fcfc000000000000fc00fc0000000000fafafafa
  | 0, 5 => 0xfffafffa00000000fff0fff000000000ffccffcc00000000ffcc000000000000ffc0ffc000000000ffaaffaa00000000ffaa000000000000ff0fff0f
  | 0, 6 => 0xffffc0c000000000ffff0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc2b9164c2138b499e5534c6b90c4
  | 4, 0, 0 => 0xc267593d719a438c59a488e31709dd4cc5c26911317199d5935c2b9133170b5d44c5c267574d7085d4cb5c2b7564d6ea5d4cc5c2b75331709a458e59a27532d6eb1d4cc5
  | 4, 0, 1 => 0xc2690e3170b9a4cc5c2484e317099d48c5
  | 5, 0, 0 => 0xc267dd4cc6c267533056c2e9a44cc602c99d4cc5c2a99d65360307532825c2675330169a489d4cc6030add4cc5c2675340c6c2eb5d4cc69a079d4cc6c2899d4cc6c267533096c6675338c6c2f99d4cc6
  | 5, 0, 1 => 0xc2675338c6c267554cc60264cc180503098c2065c267584cc6c2675334c6c2675b4cc6c267564cc6c2485d4cc60267532805030993306502999d4cc5c268dd4cc6aa999d4cc60304cc182502689d4cc5
  | 5, 0, 2 => 0x309a438c5c267533036c267544cc6c267533046c26753307603074c2025c2695d4cc6c2691d38c6c2691d4cc6c267564ce6c267533086
  | 6, 0, 0 => 0x267533005c267594cc603099d4cc5c2a99d4cc6c2691d4cc6c267533086c2675338c6030993306503099d4ca5c2681d4cc6c2675c4cc6
  | 7, 0, 0 => 0x3099d4cc5
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
  | 0, 0 => 0x3e0e703c7c73f01c00f8c70106f031c043fc0ff0fc0318003fff
  | 0, 1 => 0xe0000000f1f1cff00c63900000e0ff39c6ffffffff8ffc1
  | 0, 2 => 0xc0318e700c6390000003c7c73f01c00f80000380000000000038
  | 0, 3 => 0xce318e738c0000e0e300380000000e000003800c1f18ff07c639
  | 0, 4 => 0xf03fc07c03f00cfffbfc3f38fe0fce3003f0000000e00338fef9
  | 0, 5 => 0xfe3ffe7f83fc0f1cfcfbc70000f00fc03c0ff39f030003c7ff3f
  | 0, 6 => 0xfff0003ffc000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x28080014543345150cd044010400000001bc0eb0480208001fdf
  | 0, 1 => 0x44d4ae812108ad373df709ce79c2739e4f63186fb7bdd6a8ac41
  | 0, 2 => 0xd7f7fff1bdefb86a732d5753be55d4ef95753be5584e7945533c
  | 0, 3 => 0xeefb9e7bbe020aeaf32ebaa000ac8f22aa8bc49d7f7fff5fce79
  | 0, 4 => 0xf90fc53e43f14fffffffffffffffff3afffe020f90fc53bbfefb
  | 0, 5 => 0xffffffffebfdffddfefbf76020fd8fe7bedff7dfb78083e57f34
  | 0, 6 => 0xfffc2abffe020
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 50 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 50 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 50 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 50 then wireAt i else 0
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
  | 4, 0 => 0xfa681206e073355ec94d0e65ac05225ea94f863194adef5c919370388e6702ab7bb4f3a479e76c50700f6e5a6bff23c86623f80a588cfc87486fb1803b937b2339d7ff9f3649f21e350602553175eed630b39f272ce96b6d252ab9081f6c5e8b18c3dfb01824abc90c54e263
  | 5, 0 => 0xf853f986f775f5dfdebcf34cd591247cd051f507ca1ce8d5c56e12e7c5159104c1afdc6dbc1d98f3ba3f056eb4992a82b279bdb6ac05225eaa294541a8a24dcda5c5b6cda1e4e2f19cf85a29956e3e229208691087288d1481836061814b23f77bbca0f37ada523b76ca893f75e14c78724f2eeb6bff23c8649117035ab861c2554c825e551445f4526e44fc4f3cfc264e43575c4279fe8d3b937b233a6b8d4129ed978a289b62ea276bea432637312d25303d3720ca757e206585ea1be300d41b8a7ef1172f5666126b25b708dabbe6074368e8067329db0241d3e1
  | 6, 0 => 0xd051f507c1afdc6d81836061554c825e276bea4325303d371b8a7ef1126b25b7
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x200000c000000000000000100000c000000000080000200000cc810000000400002300404c4101000008000030000000000331040400003000000c81003104040000131040000000
  | 5, 0 => 0x8000000000080000200000c0000300000400003000000000003104000000000000c00000000004000020000000000000000000000000000000010344080000000000800002000000000010000040000200000000002
  | 5, 1 => 0x10000080000100000000000000008000020000080000000000000003000000000010000000000000000800003000004000030000040000200000c00002
  | 6, 0 => 0x8000000000080000100000800001
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

def symsG : List (List (Nat × Nat)) := [[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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

def dom_6 : Nat := 0xff0000
def goal_6 : Nat := 0xe80000
def roots_6 : List Nat := [0xaa0000, 0xcc0000, 0xf00000]

theorem low_6 : Lower dom_6 roots_6 goal_6 4 :=
  lower_iso [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_7 : Nat := 0xff000000ff0000
def goal_7 : Nat := 0xea000000e80000
def roots_7 : List Nat := [0xaa000000aa0000, 0xcc000000cc0000, 0xf0000000f00000, 0xff000000000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000000000, 17, 49)] (by decide +kernel) (by decide +kernel) low_6

def dom_8 : Nat := 0x5555000000000000
def goal_8 : Nat := 0x5440000000000000
def roots_8 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]

namespace S_8
def pairsG : List (Nat × Nat) := [(50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [54, 58, 54, 60, 58, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_8.map (· &&& dom_8)
def goalM : Nat := goal_8 &&& dom_8
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_8 == dom_8) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_8 goalM u ys) : RunD dom_8 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_8 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_8 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_8 roots_8 goal_8 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_8 goal_8 := by
    have h0 : isConstB dom_8 goal_8 = false := by decide +kernel
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

end S_8

theorem low_8 : Lower dom_8 roots_8 goal_8 4 := S_8.noCircuit

def dom_9 : Nat := 0xffff000000000000
def goal_9 : Nat := 0xfeea000000000000
def roots_9 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0x3333000033330000
def goal_10 : Nat := 0x3222000030200000
def roots_10 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]

namespace S_10
def pairsG : List (Nat × Nat) := [(17, 21), (17, 49), (20, 21), (20, 28), (24, 28), (25, 29), (25, 57), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [17, 17, 20, 20, 24, 25, 25, 48, 52, 52, 56, 56]
def r2sG : List Nat := [21, 49, 21, 28, 28, 29, 57, 49, 53, 60, 57, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_10.map (· &&& dom_10)
def goalM : Nat := goal_10 &&& dom_10
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x2baa1fe3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3333000000000000330000003300000030300000303000002222000022220000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_10 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_10 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_10 == dom_10) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_10 goalM u ys) : RunD dom_10 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_10 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_10 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_10 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_10 roots_10 goal_10 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_10 goal_10 := by
    have h0 : isConstB dom_10 goal_10 = false := by decide +kernel
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

end S_10

theorem low_10 : Lower dom_10 roots_10 goal_10 4 := S_10.noCircuit

def dom_11 : Nat := 0xffff0000ffff0000
def goal_11 : Nat := 0xfeea0000fce80000
def roots_11 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

namespace S_11
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 49), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 26), (24, 28), (25, 27), (25, 29), (25, 57), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 25, 25, 25, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [19, 21, 49, 19, 22, 26, 21, 22, 28, 26, 28, 27, 29, 57, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_11.map (· &&& dom_11)
def goalM : Nat := goal_11 &&& dom_11
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x301879e71b7e4038
  | 6, 0 => 0x73240d52
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000ff000000ff000000fcfc0000fcfc0000f0f00000f0f00000cccc0000cccc0000aaaa0000aaaa00003333000033330000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xd634586ac85
  | 6, 0, 0 => 0x6ad15
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffc000e03e001f81f81c01c0038038003807fc7fc7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xffe004f23f20df9ffb9d15d24b8ab924f84fb47546
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 24 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 24 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 7 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 7 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 7 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 7 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 4
  | 5 => 24
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x73240d524e8b4ff309e8339c01e0734e
  | 5, 0 => 0xef4cf998eddd1af5ed3576e3d7c737ebc998fb3f98f9af048f2f91ef73abf9b97395259e73240d5267fbc5974de089154bce347c472ec03543d9a45b3c1f93602868627c28531e57204c65761a287331195e30fe18dba2f41391194e05dfb75b
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x800004
  | 5, 0 => 0x4000010000000000300000400001000000000030000040000000000c0000000000c000030000000000000000000004000010000020000000000100000400000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_7 roots_7 5 s ws hint
  | 1 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 2 => checkCutEntry dom_9 roots_9 5 s ws hint
  | 3 => checkCutEntry dom_0 roots_0 4 s ws hint
  | 4 => checkCutEntry dom_10 roots_10 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_11 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := z5_0
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
  scr dom_11 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_11 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_11 roots_11 goal_11 7 := by
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

theorem low_11 : Lower dom_11 roots_11 goal_11 7 := S_11.noCircuit

def dom_12 : Nat := 0xff00ff00ff00ff
def goal_12 : Nat := 0xea00ea00e800e0
def roots_12 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff0000, 3, 19)] (by decide +kernel) (by decide +kernel) low_7

def dom_13 : Nat := 0x5555555500000000
def goal_13 : Nat := 0x5440444000000000
def roots_13 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 44, 60)] (by decide +kernel) (by decide +kernel) low_8

def dom_14 : Nat := 0xffffffff00000000
def goal_14 : Nat := 0xfeeaeeea00000000
def roots_14 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_13

def dom_15 : Nat := 0x3300330033003300
def goal_15 : Nat := 0x3200220030002000
def roots_15 : List Nat := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 4 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10

def dom_16 : Nat := 0x3333333333333333
def goal_16 : Nat := 0x3222222230202020
def roots_16 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3300330033003300, 20, 28)] (by decide +kernel) (by decide +kernel) low_15

def dom_17 : Nat := 0xf0f00000f0f0000
def goal_17 : Nat := 0xe0a00000c080000
def roots_17 : List Nat := [0xa0a00000a0a0000, 0xc0c00000c0c0000, 0xf0000000f000000, 0xf0f000000000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10

def dom_18 : Nat := 0xf0f0f0f0f0f0f0f
def goal_18 : Nat := 0xe0a0e0a0c080c00
def roots_18 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0000, 3, 19)] (by decide +kernel) (by decide +kernel) low_17

def dom_19 : Nat := 0xff00ff00ff00ff00
def goal_19 : Nat := 0xfe00ee00fc00ec00
def roots_19 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc00, 8, 10)] (by decide +kernel) (by decide +kernel) low_15

def dom_20 : Nat := 0xff000000ff
def goal_20 : Nat := 0xea000000e0
def roots_20 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

theorem low_20 : Lower dom_20 roots_20 goal_20 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_21 : Nat := 0xffff0000ffff
def goal_21 : Nat := 0xeeea0000ece0
def roots_21 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_21 : Lower dom_21 roots_21 goal_21 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff00, 2, 10)] (by decide +kernel) (by decide +kernel) low_20

def dom_22 : Nat := 0xffffffffffffffff
def goal_22 : Nat := 0xfeeaeeeafce8ece0
def roots_22 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_22
def pairsG : List (Nat × Nat) := [(1, 5), (1, 33), (2, 6), (2, 10), (3, 7), (3, 11), (3, 19), (3, 35), (4, 5), (4, 6), (8, 10), (9, 11), (9, 13), (9, 41), (12, 13), (12, 14), (12, 28), (17, 19), (17, 21), (17, 49), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 26), (24, 28), (25, 27), (25, 29), (25, 57), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 8, 9, 9, 9, 12, 12, 12, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 25, 25, 25, 32, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 33, 6, 10, 7, 11, 19, 35, 5, 6, 10, 11, 13, 41, 13, 14, 28, 19, 21, 49, 19, 22, 26, 21, 22, 28, 26, 28, 27, 29, 57, 33, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xfffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_22.map (· &&& dom_22)
def goalM : Nat := goal_22 &&& dom_22
def NN : Nat → Nat
  | 2 => 2
  | 3 => 20
  | 4 => 135
  | 5 => 546
  | 6 => 986
  | 7 => 424
  | 8 => 26
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x93a81dee4d247e13
  | 3, 0 => 0xf5b01ce8ecec1fccdfbcda9fd75edd2ed43ff7dcd3da7dead127b96ecab3dd21bc01c391aa5f8dbba7fab3a0a662158284c86c1173a066a358f405d24d2865e33cb66cb81a9c4f1706fa355b022a1d15
  | 4, 0 => 0x7dbe848c7c24652c7ab0044079338a9678b49ea877df8c9e7759d247772ba4fc754a75ca74c0113373fd9332703860606e0504336b1625646a22059169934ef560d0cd9360b95e925ff683415fd8a8675f52eaa35f19abb15e2bbc585c693f255c58644d5be378875929a38956ca0b29554f05234edc743c494db72146543ea644b8bebf43e25e2f41c662173ebd5dfb3b0e48ef39e23d7238a1e0ab383409e637406709371934b3359f093e34596bc43363c4952e7fe5ad2dd6badb2a71846129e1314f283d01c2266bd6d6201dcf471e2ccc811cb290d71a695e721951c300149da19112845a191218bb090a9f822f079844f2043d47dc03d8b4a901bb19af
  | 4, 1 => 0xed01a27bec051d3beb2481c8e6fe9d58e62e3b20e228798ee216f3d8df6a1c1ededb2e65d869eb9ad773553dd5e9bed9d5801de1cfdc0863cf3e78a9ce6d10dacd8ba78acbe4f914cb76f86ecaeae2feca539231c913aa88c4a8d486c4274248c049857fbeb329efbb4ecbc7b5692862b4c80e72b39f2246b308e9bfb2c2abb9b2319d41af25a94aaae4665baa42ae27aa32544faa2a45dda8719d69a80e8944a57b4427a54b0a5da51a7445a296ee87a1b2927f9f8dee459b4da8379b03a047990143fa98dd0a789801e43a977ac75d91accccc8f7f32af8ead2f3e8e2656998de3ee6c8baf3ecd89e358b6891bcb5c836f366e82eedfbd82afacc280e59160
  | 4, 2 => 0xfc452ce4fb52ef3ff984233ef876ead1f41567d8f0798cf5f01a60ff
  | 5, 0 => 0x1763c8e2174eba44172b26c515dac5e915924a5d148a4f5713f1225a1389877213613757135f49f112fc993212443421122a381912204883119dfe10117c00f310d9d92a1098ac7d106fe4ed1056a0981002c8780f22cb830f05e3880e674c760d732ca30d2996c10ce476070cce82c00bb032dc0b931def0afb86320a8596bb0a23aba30a0e92f10a0398d909f408910988915a0929eb3b08ea0cab087d22ae080764f207d12e4b07b40e280770b60c073e9ab3072cba910729de7506dedab706bd437806bbc9dd05f5b00604afd03a0430d7f0041026660384cbae036d4b3c02c8dd81027a6e0401b54c0b01aac27e01a4edb200e3221d00e2315000282fd4
  | 5, 1 => 0x3480fa58345dd54c3362609131a604fe31777dab2f8deb682dcb19bb2d044c592c6cf26e2c22e3092c1f26252b864c3c2aada6d02a864ffe295b498b2936672829165f3e28ce111228007d2a27a428cf279ba41d272c93bd270f2864268fea7f264006cf2600d3d425a6c1cc256eb4e124aeadd5249e59292488c1ff248882af23f3aedb232991f62311f50522f2e81022e74ca7224942e121c79841218f1e9621787c53210fab9e20f214c4206d0bcf1fa1ff841f8774231f50bbd11f16a4cc1ed15b311e2fdef51e200e6f1d593aa41c97bec91c3edc2f1c05c5ba1bf396ca1ba74c001b9c1cd41ae1c6821a0dcc73194882ed1936676418c1be6717baf800
  | 5, 2 => 0x4d7b6cef4d01541d4cf6e4114cdfbcf24bfbbd304b98ddfa4b0aa4d84a9dd617495f9c874880b28248388c2847b4abff470c51e646cf94044650aa0246261e3945e8159945de5f1a45b5025445ad066944fcba3544c5769f44c0d69444791ed0443662b543ab0e6e430bb76f42eab0b642934605422c19c3420642cc41faed3b41c3e6074191f6cf4149f94240fee99240a605d040a546543ff556303e89d6f73e54c7593dcddf0f3d899b263cee00213c286a943b932d743b530b4c3b0b663939cf80cd390a251b39055a2338d324c8381b56ff37708322364023f935f90a9235c7f49935ba542d358675333584e75834fdf3de34e6291134c5f9743492314e
  | 5, 3 => 0x6ee365476ed28ebf6df09d366dc9f3016d3e98496bae9e266b66a16f6b09813367b12a1267942513664bc80c657a888065704d386498771c6446cbbb63d0905f62f6613a626ff0286204510161f2f4f061e0177f61d7af80616b93555fd25c015f4701495e9ff2d95e2d8aab5e2c2c165dea55e85c14151d5bbbecff5b6a57bc5ae34b1f5acbdc1e5a7362575a6a73fb59b17cea59b05794595f37e85819358457c9f04556e6fb7356da2af65582c45355285daa54cf074b544aa3f654284ef9541923d153375ae45262514a519da05c50d94738500492244fdfcafb4fd94a7d4fd6e4de4f7c60744eb19c7e4e58e5db4e4243214e3da7e34e29c7d14e14e593
  | 5, 4 => 0x926fe23e91d127b591a2ce55912a672c90c277a0907fcf9d9041853d8e4542108e02e1808da484dc8d0fee198cfb70658c6df65a8bc776c58bb723b48b76cf9b8b22a1258b0a959589a88257894d8b378808a6cc86cb8ede858e6d0d85730c51853eb3bb8503125583e972a983ba94f483531d7c81c7c5bd815c694d80cda34b7fcc94cc7f9550167f4b3f3c7dc410ae7d3078287bbb12ac7b6818d07b55f43779e6d451797a96907924f3de78890f6f781d1ae8780a86a277df801c75885875751113a074d028b97441f7027334dd10731267d872234e8471a7a88971a3faaf7158a08c70f2c9de70b87f0170b1e8637018d75270126baa6f9f08ef6eeccbd5
  | 5, 5 => 0xb4b2f8e6b3c371e8b38e109cb33e8640b32ddb97b313dfb3b12ef38fb0df25b0b092cc10b087fbabb001aa5faf562516ae4b4cd0ae3211d5adf0a941adaf7c38ad54bfebad51c8feacebe7f0abc3344fab960c9cab5d7604a9365dfaa8f06a62a80e7ed0a7163fffa6cf9975a6abffe1a4c253dea481cfcca44ecba6a400ecdca36dd21da34ffa3ea21facb0a1e7cb4aa1aacbf3a09730c1a02fc5eda02b671e9f2eac0e9ed6cc0e9e3ec3279dfdf3cd9dc5dfd09dae70159d7f031f9d7220e89cf8e96c9cf0cf2d9cd54a509cb2e4159c951a629c3cd9109bf429089bc811e39b0d0fc398aaf76795025a4794f2cd0393eb0e0d93a2e0f693364abb92879af9
  | 5, 6 => 0xd684f950d67a4ca1d504162dd477d8f9d455f772d3ca9cbad3202969d307c559d279eabad22df917d216a5d9d1941c87d1454bb2d00bf48acf88cc23cf5af697cf2180a7cc6835e5cad5fab4c9bcfde8c950f635c945fe97c91c43e9c77cf27bc759db72c7163729c6b993f1c62204a2c598271cc48f92c7c3b7bda1c313831cc2e1ec4cc2a2cffcc29b51d0c1a85a88c179f7d8c146d381c0a2636fc07ca694bf4f9b90bf3fd0ccbefccfe9beede719bedd9d2abe8dbec0bdfcf5bdbd41ff14bc83b976bbd34287bb018765ba68ab79ba583c81b950c2ecb91036b5b9068347b8bfc42fb87b69a2b864e5c9b83eefd5b7304d8cb6ff990eb6ead686b4e3f2bf
  | 5, 7 => 0xf2affc01f1cae8a3f09ba6c7ef6e2331ee8b098dee80253fee8000a3ee7d4306ee230365ee221f72edd55da7ed5c38c6ebdb1404eaf8e3c2e9ee24e9e9af11bde9a8dd11e9a565b8e984c3b8e966ba77e942a6c9e913a980e8a9b0a9e8735cc3e75c7ce2e75c42a5e7338541e6b72a29e6a72104e62afb66e5f36952e5a6c51de5650c89e531dc61e4a4979ee3a08d48e2efa377e29f57dce254d007e23edf5de1d242f9e1c9df61e1887c41e146e841e130803ee02b6c65dff65054dfeef4bedd7c2bccdd57f7a0dce8ce41dc6bb256dc50386adc297164dc0e7fb2db8530f8db42cc9bda3c9899d9043ef7d7aa92d6d74bda27d745baf4d741da9ed6c6d6ab
  | 5, 8 => 0xff9a5ee7ff7c7d93ff419561ff349f99fdd8feecfdd4fa2afd77e23ffd6aaa89fd64ab9dfd2d0a86fcfcb63cfcc41558fcade97cfb490f52fb465885fb2a838afacd16f7fa26367ef9b362e9f99adbc6f85b8e44f7ea4fbaf75e5177f73a4590f7156afff6eeffc6f68277c7f675aaa0f5efd88af4dc4714f4b2d026f2fc5ba2f2eefbbff2e8dad3
  | 6, 0 => 0x12123e381141c44811408e9a10cc6bad108d3a531072050410060e320fec104b0fcb33c20f9550a90ecdeef30ea8faac0d6e8d170d40405c0cc62e6c0c8a4ae10bb8a2180ba8521d0b88cc090ae653d70a6572fc0a4613430a2deef80a2d481b0a01f69909e9743d09874f3d0919997808c00bc9084ecf1407e99e2e07e4ea3e07a676fd06f102a806a40871068d7fe10681af190680b92c060f596e05e77d710512d18904963a7b0460bf69045a691d0453118103f8e99a03833f2603598f5d0346d7a7032f719c0298285b02867f1c0255c3fe02193b5e01ad44030195ffdc0185b851017f3bda012a5840010ab0bf00f94cd000f91aa800ad42790046618f
  | 6, 1 => 0x219634db214f0d1120de5f9620d5617920819f3a20810030206969b8205b0a2a1fde0f001fc4f9a61f6fbf471f634b621f399eee1f129f391eafff3f1e7148da1e62464a1e4008941dbe4d991db45b721d940b681d88a2031d66c50e1d4df85b1c96ea491c7f55261c397d011c2546331bee157b1ba367651b1af4f51b1a2ca91b0bab3e1a256c931a1f1cf019ba301a1956d57318e16a7f18c4770b188f92a4186cfbda181c0a6c17e7c6aa17ce2ba217ae9e2a176c9a2616b3ff1616b01e54165a143315fc5b6615c3143a1596d48d155ed0bb155a7dc41535fac814c7480c1409a61313fd04b3133d44ab12468f8712348c5912324797122a38191223d250
  | 6, 2 => 0x312099a030cca4c430b3c7d0309ade1b2fdf32122f653d432f5ca5572f37b6b72f2fce4c2f2d39052f15a0e52e450d9e2e3cd5d82e2327552df741622de6358a2d52d1502cadc4612c5afc882c4d2a222c42325c2c3593cc2c1a29112bb2627d2b43cf532b35846d2b27b74c2afd8c522ad9fd9b2a36732f29f5789c29d10a3229cba4772934275728e1d56328bda13e28b13185289a15a2279ad8902750b4f6273a868026548cc425f116f125dc2a2825c5c2a22566dfcd2550cf70254b6a5725318cf4250b3e6a24ebf64f247367df242f629b241eca5d23fc45a223e6582623bb3be323ade2682383a1de23679dba226fd98422599897225540ef21bde807
  | 6, 3 => 0x43e3db9743b9e6c743130f0343110caa42e28e14415fc25e412c1b38408a3dc73fd84d593fcf86193f0f37c13e69a4d83e6329a03e247c763df99e973dce4f973dc0b3cd3d8a3cae3d4e5b033d2562093d1e34fb3ccc486b3c9ce34e3c346cd83b8e30ae3b754d643b4891dc3b43ce223b04898939de473f395f2ed03909b49e38d3d4183829639837d59bc63784fc673748575a372b33393715bfdb36d69bdf36cd76be36b5383e363ae82035c10950357f73883505b6fb34e12a59347939b8346502b533df688433dd474d33da662c33a95ef33366c242333d305e331b439e330f147832eb626b32e38d4f32e16b893241f77231fefd8b31ae084531472fc2
  | 6, 4 => 0x533a6d585318541d52c657935299439f5290580b51f6a40d51ccc13e51c09e3351496a925139dea750ce962c5038f11c4fb1b6794f526fbe4f0d9c4b4ec280834eae9d164e4388a54e3da7e34e37dfb54ddb76074dd542384d977a104d8d48cc4d5109994d5001c34d1acf0f4cec75af4cad82f14c8a818c4c388e2d4c0f52314b77d19c4b75ea1e4abd1d0b4a7c767c4a67671149dd0e9149c0fcf449b6983f49780ea8497253c149335a0b48d154f34840189047fe1959473400504700cb0e46f1b31146bddc5e46ba812f466dcded462000d245cb4f1b45b657d145a7f5984545462a4541527444ea5ff044d58299446729e644623ede4449f5954408d567
  | 6, 5 => 0x63c9dda363939f33633b61f76326e6d96273e1e7627050f9622a4e0c620a3042620486bb61f617a361f5a73b61b87237617c8feb603ba18c6017f9735fd4e0885f65070f5e8dc5755dd193db5d8bf1475d72a47e5d46331d5d0ffb5a5cbe4b0e5cac1ec35c97debb5c8357335c6c35a95c10eb415be0d81b5b796d475b00c4075ad883ea5a353b1759f502be59ed3d0e59a0c2fc596452765944924459254669581ef1aa5770ff1d576611cb56e8a03d56a791e3566c96a256488c3a55f9c36e55f2f73355a4b45955739b7c556f069554b5735e54a96c095488605d5479ade65464d08f544f103754304cc253f49ec153eff8a9537b674553447d04533b7ec1
  | 6, 6 => 0x7369c7667301de5f728256e4727253ef71db3bab71b731cf7193d4b1710cff02710750de7037bb1370345b606fb7655e6f9599c06f1741246ec7a3626e1154bf6dbbe1966db3cd8b6d60d7e36d5b00e46cc7f9b76ca99a0b6c79ed6a6c6cca846c2d95746c0fb1986bd1a3056bc67ad66bbdf9a36bbbe0b36b4b51b96afee7646af2d7f26aefcfd96aafcc206a95be0b6a41599e6a0abb036a08bb0569a9dbb86992c1b16933ccb268b68ec9689e674567f4aa3e67d214df67a09366677d8db96774f552676c4ad46741623a671ea51e66be836966b60782664cb09665ec78e265e76cd565961aed64dbd5c464cb1eea6497fa93646d8437640f62e363f38a81
  | 6, 7 => 0x86cb1e0086981ab6864f5914863b65ee85c3cf3c8544e64684e1769f84d9addf849e475c844e79e883f8d5db83f53a1c83b173988320fd1b8312ea9182cca1d482c4fa70829835b3827963fa8267361782348b3c81f114c7818c8a24817cef808153ce4880d851b580b1b4cd8069eaef80265a157fc09d597f78c21c7d8dbfab7ce7e2b17c7054c17c16ecba7b4bbbbb7b2c1b347af9f9577af39e807abeb30b7a33585379e5550479d342cd79c2eecc792b8cc878b458a0785ee2587800865577e0dac777ae3ab077abf41376c379d576aa9650761e2a8775a1e3db7597c94175791c4b74f8ca7a74cf39e474a44fa47481ccfa7448134173be3a8b7388972f
  | 6, 8 => 0x9601231395b93d7695b448499551aacc94dcea6494b791e694ad81c794a0b6d3949046119464b8f8945f301894518fac9381e4a0934a18bd92d45119928f624e91fd1dbb91f1d16091d14c5191d127b59102d26a90e91ce690d217489054b16b8fd304808fc3c7a68f74f0a98e3f8c778e2526e78e01c6188dd7584d8d869bbd8d5ebf6f8cfa91f68cc6a3578c51c7138c46c50f8ba51dad8b1bf90a8adb09b18acbbf098a8f779789f074c389a8e63589a86b258986be5c897fb39b8945a6a9891d8b7d8905ec5388e0387f887ddfc288107e08880bb85687f5beb087f2850a87edb1a287e13aa0876db58987648dca8756c638874f01c787257dec871506e9
  | 6, 9 => 0xa6aa7b4ba67bd044a63809e4a6353a8ca61bfe94a53aae23a52c7e6ba4ef0d12a4428e5ba434b4b6a4093031a37956e6a3744415a35b4fb5a33588fda3105a4fa2efe0c0a2cd8bc3a2a97873a174a2c0a16ca8ada126213ca070683ea01e0a0a9f9d3ddb9f8fc8a09f5eff5f9ec9ae489e44433a9e1e3e099de8ff369d6fd84f9d3bb9e79d25116b9c9ccc9d9bacb5569af9d2839aca79e39a8f04879a255f3b9a2202919a0d459599cf7f7d99ce129a993a7ae3990f019198bf8e8d98a19efa987e22a4986b97ef985600c5982e64fb9816081b980afa1a97f60d3397c0eda197a00225977d7102976491d09736bddf96fd835396424b41960bb76c96099aa9
  | 6, 10 => 0xb76b88a8b7547ca0b73847c9b7083aceb6d8a086b692b6acb64676f4b515d8e3b3f19d82b38c209bb36d3a2db34ae530b31900d3b2ce525eb2516d61b222061fb22053d7b104f48eb08325ddb060829ab05c264fb03615abaf7112d2af70889eaf647c31af204a12aeeb3210ae77067aae6de29cae6872d8ae553aabae4cad44ad58a5d0ad54bfebad148ffdacc719e5acb74da7ac2d59fbac06f897abe9eccbabd7936dabb3dcc5ab676f4faae79678a9fdc82ea98e4816a959581ca931991aa8f0d2eda8e78fc4a8cb32a4a8b24ba4a893383aa84edc83a81e07a4a81cf63ba7853e24a764468aa74b09e8a748d152a71892dba6ebdd47a6cd1d65a6aa8094
  | 6, 11 => 0xc5c2d3b0c5b0f683c5736c6ac518bf53c4e045a8c497cd3dc453a13bc3d3686cc3ad09c1c34fd073c30d6fe3c2f38d46c2d89b35c2bc05a5c27af562c26d0ba9c267cbdec20f81e7c148abb5c13f5760c128b4b5c0e08b57c0d8bcdac0440dc4c0171c7cbfe17047bfcea96abf8c3f1dbf79164fbf5d435bbf3daf06bf307c4ebeef2e68beed43e6bec2b53cbe97b2cebe4e61b0bde1cfb5bd8be129bd41496dbcf469d8bccba248bc9c5c20bc878e76bc545819bc0bf607bb8f7c21bb897c82bb4177cfbafceb8cbad82625bab9a1bdba49421eb99d8907b94719e8b8c9f8fbb8a185a6b81bcc44b7dce78eb7d6b31fb7d36574b7b92ec7b780656bb7784d34
  | 6, 12 => 0xd8a2e1fed79dcf25d76eed8dd76d9a26d740303ad6c3a000d5554a27d553ea4cd54deaadd52fb620d52b0a13d4f14d08d4af50cfd4938e6ad445852fd3dbb87dd3a84f1fd2a903ffd26e2c13d26d319fd23fd7cdd2370a95d215039fd2099c14d1358e44d10ca139d0d43b52d0705c58d028b587d019acf1cfe1e7becfaaeb5dcf4fba80cf384970cf1d7974cdd77710cd969af4cd73df73cd69efddcd13336dccba459bccac709dcc87d8b5cc678650cc389808cbe6744acbd5b4f2cb7814d6cb5a385fcb2d7f47cab27f88ca77f241ca5d1f3fc996b3b6c9760326c934d057c8f59c70c8bdc356c8bcd3fdc8843c2bc7337313c73369bbc72c9218c6631c17
  | 6, 13 => 0xe9a1d114e9375f3ce898d1cee86bd220e85b8981e82ca1a0e8027d18e7e8d4afe7b699c8e79a729ee6f5ef60e6dfa69ee6d9419ae61eeb27e5830406e4e54ac1e4dd38a3e4a745e5e417b86ce3ca2ab6e3840ba4e2f6af66e2e44efbe2ba0a9be26cad09e248aa56e247b55ee21be8d9e171d949e1151f08e111b6dbdff3a4ccdf7dc165df64decadf3d5635ded5d017de90f3a7de84395fde4eb049de2c8b95ddfb04cdddcb021ddd36d6a1dcd5e9e6dc5b4c2ddc530e5fdc3179d4dbc7b3a7dbaf123adba68411db75c240db711277db2e8ec4daa10b17da934e32da26d716da1cea69d9e38cacd99b8409d97fc822d94a31a4d90b7b3fd9021d31d8c9c9e2
  | 6, 14 => 0xf918fb51f867a20ff8202e5df81e117ff81b3b58f7d6a695f7ad73dbf79bcb08f7968602f779760bf716d4caf6535463f6281cb5f5ebce57f5e5463cf5cbaefef59108abf5192827f4bb552ef47fc6bef4723ae7f3b27adff320cdd2f29edce5f23a1c75f1a59475f19580b8f1914f74f17d86d6f153019ff0d5c0b0f05edfe3f052953bf03f9791f0346202efa77ca6ef885172ef321432eec22234ee71c1e8ee44a0bcee1fa362edf838d8ed9de86aed86fa4eecf6bbe2ecc601fdecc260f5ecc12505ec6537dcebdc8430ebc0c7caeba28a2aeb93c63beb475aefeb121e74eb0238a0eb023407eafba6c3eabd810bea8e0ff7ea326695ea267a7fe9e0e609
  | 6, 15 => 0xffc703bfffc6e326ff84627aff1c032afefc3625fed1b51bfea1950dfe4b532dfe43557cfe2c0696fd75c11dfce3f7c2fc97bf31fc6afe7dfc43d33dfc0c146cfb86197cfb314dddfb17c36ffad62506faab44fcfaa91205fa06476af9cab482f9afb2a4f9a7b435
  | 7, 0 => 0x26488ebe26396ad425eb7b52258a6ea424296515233e519822ea3ac022daf26b22c7351322521a04223682592219ec0a204aaf2d2014c6441fb72b911f3d31db1f3108e21d73f5661d094b741ca0b1831bea35011b8548e61b61a0cd1b52f3321a433cbc19b1d448196672e119169d33175a929b16a6119915ff8a47153eaa1812baa6771234695d1232479711eb7ccf0faa77070f79f41c0f3d84400e8414b20e7dd0190e783ebe0d9cbe430d52c9a60cc7aa850c22507d0c167f100afb5dd30a2e187209f8447009874f3d08d6f026089ab0f3076636a70754ea1506b07a0306291d8305c61dd605a3eb0a059e8b1705869eb10291d00a01a603fb01283a17
  | 7, 1 => 0x4dc27b5b4d1acf0f4d17706a4cd8ba054ca60af44c8f74574c4c79c44c1e35cd4bff26be4b7591cb4b0c2c394a3f78dc49e125c649ccf756499b08ca49226c8f48f889f848f0bd7d461566634609964845f6b584457c5ed144d9dfff43a9f84843555fb0433f660a430588364214fad141a4b5d6410d769640db2d8b4079af633ee6de3d3d6d0b963c9d75a23c39fd5e3c21f90f3a8b9b213a8b1a653a305add38ad846e387c221636c744ae36b6da92359f67e73481847a34746a9f339be830330961a632ba82ac3264f1943055c0a6302ca7772d90db782c50f8382ba0a43a2b81626d2b698d6c2a6cf0712964176b28a4a83e27f34165275958f22705880d
  | 7, 2 => 0x751c82e773f60c3a73b2320a70946692706753916f69601f6e9f1e276e834bca6d9b14bb6d483b2f6bed6d236b89f08a6b6909ce6b46b4d169c0add469b2eaed689e6745679d352a6379a67663669d956347643b63353df462623a3561f427ee61aa3368602f2d625f492eb65ec2fe405dc82fa15d7bf2db5d6275f45c9fbd605bff541c5af03eb05abc6cf25aa8a6b95a17fce059f684b25806ebe257a1024a56dbe56f567ee6cd5640306855f952e7556f069554c1de105342fdb753346db9531915d152942b72523dc21151efbb60514aca6d51099cc650c4b4ed5038abd6500139404fb2394c4f943bc44f0fba7a4ec05ebd4e2ce2974de254b54dd11167
  | 7, 3 => 0x9b71391a9b1dd7b09aec1f2b9a36658d99ed5e87996c23f498411d8197a4f387974a939b9710a45897012b84944ede009442b06893f42b8d93602c469351acbb91bec62691495fea9117715e9074f28c906d261190061e318f7fd14d8f6e24048f255fd78e7679718df2ab598d5eaaf98d3d413a8c1a6ee88aef68758ada8b1e8a81f0ca8a0d10dd8968a0cb8934bc8a89143e4287b12daa877910e2872610b8867726a1850f030e83c5bc5283233d80830766bf82763972806266ad7ecd8d627e22428f7e05acff7dd5c4a57db173387d303bbe7c0721267bf0d3337bc86ac17b8db51e7b2b17a17a7a23a87a38d5c279e15a2878bca81277d135d0764692e6
  | 7, 4 => 0xbe907f01be107ab6bde1cfb5bd199d0fbcc8e334bc545819bba736d9bb04b807baa8a17cba88bda4ba45dd7fb9782853b85c2f59b84d21e0b837fe7bb81d78f4b55b444cb511b645b3feb3cab37ef559b2dc7687b272f2abb253eee6b2306866b0e1dcffb080f6ebae064aa9ada32de2ace974c5acac34b6abbe6e52ab94b348aab1140caa8df529aa87c3f1a98e4816a98c5b5da8e78fc4a8d9852aa840633ca80fa957a8098f40a77ce252a6910249a68098aea5d7b751a4dede88a4a02823a499e38aa494c22fa4711fa3a3f2435da302d5f5a275c8f5a1946574a1689281a07b3991a02ef21b9e58572e9db654639d3508f49d3121ea9ce015509c48de23
  | 7, 5 => 0xe8b03ee3e73f702ce7283c3de606f433e575a6eae49194eae4625a30e45c7de4e33582dbe21fca1de1ccafbce1283faae07b344edfeb09c7dfb32b5bdf6d0221dec49712ddd7f9c9dd0995b1dcd6712cd9b9b7a8d986de71d96359b3d8653959d7c2c847d7c0c947d76eed8dd6af2d85d697c1d4d3a21f4ed27a66b2d17f337bd0e5095fd0dd3a20d0a7e5c1d010ef66cf84bc20cf6ea403cf2fed9ececb96dfcea2794ccdd2d617cdae7ca3cd73df73c9f2a206c8d8951dc7d3f23bc7466283c707ac1ec5dca5abc576ef75c4eae2e7c483e9fec3fbe96fc398766ec33e8ebcc3334588c2d0e2fcc1a069d3c150c440bfa41077bef1afedbeb2f988bea336b7
  | 7, 6 => 0xffcceadcffabe638ff939cefff3df527fefb8721fe809189fe5cb65dfd875a02fce2758bfc3e0176fb74cedafb192d73fac274d4fa58df1bf9acd0faf9323ec7f7e68aa8f6e94291f6657479f5210d0ef4535bf8f34c8d5af30eb1d1f22186e7f15afe71f109fd47f1027f58f05fc8f2f053c1fdf03d9387efdfd1c7efc2e112eef3064deec76f65ee22ff53ec164c1eeaa64cb1ea555bf2ea206746ea04555a
  | 8, 0 => 0xd1efb8f3c2afde01b6be7634b47be6219b34b1218ab84b5d8a7994f8876dd2497f4590c97e1a8a567cea112d76f0de33764e5f61705b5d9f61ca40085fbac6fd5cde0cce4f8c57c234064f6c2efbd9641b78d4bc1606144c1561a43a1142fa410e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33ffff0033ffff00333333003333330033003300330033000f0f0f000f0f0f000f000f000f000f0000ffff0f0fffff0000ffff0000ffff000000000f0f0f0f
  | 0, 1 => 0xcc00cc00cc00cc00aa00aa00aa00aa005f005f005f005f0055ffff0055ffff0055555500555555005500ff005500ff0055005500550055003f003f003f003f
  | 0, 2 => 0x3030f0f03030f0f0303030303030303010101010101010100ff00ff00ff00ff00ff00ff00f000f000ff000000ff000000fc00fc00fc00fc00f000f000f000f0
  | 0, 3 => 0x505ffff0505ffff050555550505555505050f0f05050f0f05050505050505050333033303330333030f030f030f030f0303ffff0303ffff0303333303033333
  | 0, 4 => 0xf0a0f0a0f0a0f0a0f000f000f000f000e0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a07070707070707070555055505550555050f050f050f050f
  | 0, 5 => 0x11111111111111110f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0c0c00000f0f0f0f0c000c000f0f0f0f050505050f0f00000f0f00000f0c0f0c0f0c0f0c
  | 0, 6 => 0x30303030303030302222222222222222151515151515151513131313131313131155115511551155113311331133113311115555111155551111333311113333
  | 0, 7 => 0x33333333333333333333333330303030333300003f3f000033330000333300003330333033303330332233223322332233003300330033003232323232323232
  | 0, 8 => 0x505050505050505044444444444444443f3f3f3f3f3f3f3f3f3f00003f3f00003c3c3c3c3c3c3c3c3333ffff3333ffff3333ffff3030f0f0333333333f3f3f3f
  | 0, 9 => 0x88888888888888885555555555555555555555555050505055550000555500005550555055505550554455445544554455005500550055005454545454545454
  | 0, 10 => 0xaa00ffffaa00ffffaa00aa00aa00aa00a8a8a8a8a8a8a8a8a8a0a8a0a8a0a8a0a5a5a5a5a5a5a5a5a0a0ffffa0a0ffffa0a0a0a0a0a0a0a09999999999999999
  | 0, 11 => 0xaaaaaaaaa0a00000aaaaaaaa88880000aaaaaaaa80808080aaaa0000aaaa0000aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa80aa80aa80aa80aa55aa55aa55aa55
  | 0, 12 => 0xaaeeaaeeaaeeaaeeaabbaabbaabbaabbaaafaaafaaafaaafaaaaaaaaaaaaaaaaaaaaaaaaa8a8a0a0aaaaaaaaa8a80000aaaaaaaaa8a0a8a0aaaaaaaaa0a0a0a0
  | 0, 13 => 0xb3b3b3b3b3b3b3b3afafafafafafafafafafafafa5a5a5a5afafaaaaafafaaaaaeaeaeaeaeaeaeaeababababababababaaffaaaaaaffaaaaaafaaafaaafaaafa
  | 0, 14 => 0xc0c0ffffc0c0ffffc0c0c0c0c0c0c0c0c0c00000c0c00000bbbbbbbbbbbbbbbbbbbbbbbbb0b0b0b0bbbbaaaabbbbaaaabbbb0000bbbb0000babababababababa
  | 0, 15 => 0xcc88cc88cc88cc88cc88cc00cc88cc00cc80cc80cc80cc80cc33cc33cc33cc33cc00ffffcc00ffffcc00cc00cc00cc00c8c8c8c8c8c8c8c8c3c3c3c3c3c3c3c3
  | 1, 0 => 0xccddccddccddccddcccfcccfcccfcccfccccccccccccccccccccccccc0c0c0c0cccc0000cccc0000cccc0000c0c00000ccc8ccc8ccc8ccc8ccc0ccc0ccc0ccc0
  | 1, 1 => 0xddddccccddddccccdcdcdcdcdcdcdcdccfcfcfcfcfcfcfcfcfcfcccccfcfcccccf0fcf0fcf0fcf0fcdcdcdcdcdcdcdcdccffccccccffccccccfcccfcccfcccfc
  | 1, 2 => 0xeaeac0c0eaeac0c0eaeaaaaaeaeaaaaaeaea0000eaea0000eac0eac0eac0eac0ea00ea00ea00ea00e8e8e8e8e8e8e8e8e0e0e0e0e0e0e0e0e0a0e0a0e0a0e0a0
  | 1, 3 => 0xee00ee00ee00ee00ececececececececececa0a0ececa0a0ecec0000ecec0000eca0eca0eca0eca0ec00ec00ec00ec00eaeaeaeaeaeaeaeaeaeaeaeae0e0e0e0
  | 1, 4 => 0xeee0eee0eee0eee0eecceecceecceecceeccaa00eeccaa00eeaaeeaaeeaaeeaaeeaaeeaaeca0eca0eeaaeeaae0a0e0a0eeaacc00eeaacc00eeaa0000eeaa0000
  | 1, 5 => 0xeeeeeeeee0e00000eeeeeeeee000e000eeeecccceeeecccceeeeaaaaeeeeaaaaeeeeaaaaececa0a0eeeeaaaae0e0a0a0eeee0000eeee0000eeeaeeeaeeeaeeea
  | 1, 6 => 0xf0a0f0a0f0a0f0a0f0a0f000f0a0f000f00ff00ff00ff00ff000f000f000f000eeeeeeeeeeeeeeeeeeeeeeeeececececeeeeeeeeeaeaeaeaeeeeeeeee0e0e0e0
  | 1, 7 => 0xf0fff0f0f0fff0f0f0fcf0fcf0fcf0fcf0f5f0f5f0f5f0f5f0f3f0f3f0f3f0f3f0f0f0f0f0f0f0f0f0f00000f0f00000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0
  | 1, 8 => 0xf8f88888f8f88888f8f80000f8f80000f888f888f888f888f5f5f0f0f5f5f0f0f4f4f4f4f4f4f4f4f3f3f3f3f3f3f3f3f3f3f0f0f3f3f0f0f1f1f1f1f1f1f1f1
  | 1, 9 => 0xfaeafaeaf0e0f0e0fac8fac8fac8fac8faaafaaafaaafaaafaaafaaaf0a0f0a0faaaf000faaaf000faaa0000faaa0000fa00fa00fa00fa00f8f8f8f8f8f8f8f8
  | 1, 10 => 0xfafaf0f0fafaf0f0fafaeaeafafae0e0fafaaaaafafaaaaafafaaaaaf0f0a0a0fafa0000fafa0000faf0faf0faf0faf0faf0aa00faf0aa00faeafaeafaeafaea
  | 1, 11 => 0xfca8cc00fca8cc00fca0fca0fca0fca0fc00fc00fc00fc00fc00cc00fc00cc00fafafafafafafafafafafafaf8f8f0f0fafafafac8c80000fafafafac800c800
  | 1, 12 => 0xfcecfcecfcecfcecfce0fce0fce0fce0fcccfcccfcccfcccfcccf000fcccf000fccc0000fccc0000fcc0fcc0fcc0fcc0fca8fca8fca8fca8fca8fc00fca8fc00
  | 1, 13 => 0xfcfcccccfcfcccccfcfcc0c0fcfcc0c0fcfc0000fcfc0000fcf8fcf8fcf8fcf8fcf8fcf0fcf8fcf0fcf0fcf0fcf0fcf0fcf0cc00fcf0cc00fcf00000fcf00000
  | 1, 14 => 0xfefa0000fefa0000feeefeeefeeefeeefeaafeaafca0fca0feaafc00feaafc00fe00fe00fe00fe00fe00cc00fe00cc00fcfcfcfcfcfcfcfcfcfcf0f0fcfcf0f0
  | 1, 15 => 0xfefeccccfefeccccfefeaaaafefeaaaafefeaaaafcfca0a0fefe0000fefe0000fefcfefcfefcfefcfefcaa00fefcaa00fefafefafefafefafefacc00fefacc00
  | 2, 0 => 0xff00ff00ff00ff00ff00ff00f000f000ff000000ff000000fefefefefefefefefefefcfcfefefcfcfefefafafefefafafefef0f0fefef0f0fefeeeeefefeeeee
  | 2, 1 => 0xff88ff88ff88ff88ff888888ff888888ff880000ff880000ff33ff33ff33ff33ff22ff22ff22ff22ff0fff0fff0fff0fff0f0000ff0f0000ff03ff03ff03ff03
  | 2, 2 => 0xffaaff00ffaaff00ffaaaaaaffaaaaaaffaaaaaaf0a0a0a0ffaa0000ffaa0000ffaa0000faaa0000ffa0ffa0ffa0ffa0ffa0a0a0ffa0a0a0ffa00000ffa00000
  | 2, 3 => 0xffaaffaaffaaffaaffaaffaaffa0ffa0ffaaffaafca0fca0ffaaffaafaaafaaaffaaffaaf0a0f0a0ffaaffaaf0a00000ffaaffaacc880000ffaaffaac080c080
  | 2, 4 => 0xffccccccffccccccffcc0000ffcc0000ffcc0000fccc0000ffc0ffc0ffc0ffc0ffc0ff00ffc0ff00ffc0ccc0ffc0ccc0ffc0c0c0ffc0c0c0ffc00000ffc00000
  | 2, 5 => 0xffeac0c0ffeac0c0ffea0000ffea0000ffe0ffe0ffe0ffe0ffccffccffccffccffccffccffc0ffc0ffccffccfcccfcccffccffccf0c0f0c0ffccff00ffccff00
  | 2, 6 => 0xffeeaaaaffeeaaaaffee0000ffee0000ffecffecffecffecffeca0a0ffeca0a0ffec0000ffec0000ffeaffeaffeaffeaffeaff00ffeaff00ffeaccc0ffeaccc0
  | 2, 7 => 0xfff0fff0fff0fff0fff0ff00fff0ff00fff0f0f0fff0f0f0fff00000fff00000ffeeffeeffeeffeeffeeffeef0e0f0e0ffeeeeeeffeeeeeeffeeccccffeecccc
  | 2, 8 => 0xfffcccccfffcccccfffc0000fffc0000fffafffafffafffafffaff00fffaff00fffafafafffafafafffaf0f0fffaf0f0fffaaaaafffaaaaafffa0000fffa0000
  | 2, 9 => 0xffff0505ffff0505ffff0303ffff0303ffff0000ffff0000ffff0000f0f00000fffcfffcfffcfffcfffcff00fffcff00fffcfcfcfffcfcfcfffcf0f0fffcf0f0
  | 2, 10 => 0xffffffff00f000f0ffffffff00000000ffffff00fff0ff00ffffeeeeffffe0e0ffffccccffffc0c0ffffccccfcfcccccffffc0c0ffffc0c0ffffaaaafafaaaaa
  | 2, 11 => 0xffffffff55005500ffffffff50505050ffffffff44444444ffffffff30303030ffffffff15151515ffffffff11551155ffffffff11111111ffffffff05050505
  | 2, 12 => 0xffffffffcc88cc00ffffffffcc80cc80ffffffffcc00cc00ffffffffc0c0c0c0ffffffffa8a0a8a0ffffffffa0a0a0a0ffffffff55555555ffffffff55550000
  | 2, 13 => 0xfffffffff0a0f000fffffffff000f000ffffffffecec0000ffffffffec00ec00ffffffffe0e0e0e0ffffffffe0a0e0a0ffffffffcccc0000ffffffffccc0ccc0
  | 2, 14 => 0xfffffffffcfc0000fffffffffcf0fcf0fffffffffcf00000fffffffffc00fc00fffffffff0f0f0f0fffffffff0f00000fffffffff0c0f0c0fffffffff0a0f0a0
  | 2, 15 => 0xfffffffffcfcf0f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x20ed6591d359ca33
  | 3, 0, 0 => 0xab4c1e2644a6b25026048a3a90a6149234d0a60483b4d02604b9bb5ba99483b4d308548a2ed4685483b5960854ab4e1d6644a6b38f46048a3a90a604aa41db6b24a6cb1b6a348ac1dae854a6b74f2604
  | 3, 0, 1 => 0x9fb290a604b9b8d00644a6c1dd8b04a6bccf2604
  | 4, 0, 0 => 0xb9d35ca80322d360eda5621569b2c6d9e8c0b73a6bc5ba995ab3b5babb4cadce9ae2429916ad4d72a9cc8b56a6cfd8ab35a6c1db6ab42adda28ea4299169b1d75214c8b0769a14f2605b9c997680322dce4cb83d19169b1583b6d0ab73a6c1de2a85
  | 4, 0, 1 => 0xa6c1db6aa42ac1df8db4298169b1b75214c8b76a6b890a645ab545e2dd4cadce0ef176a656ad4d9fb8566b4d83bc532605ab5365ac859ad5a9b1f78a516ad2478bb8c8b4d83bb10a605a6c1d9e85322dae9b07642cd6a9076dac10ab73923b50a645
  | 4, 0, 2 => 0xab535c280322d59c6bb4019169b076da610ab07782e90a635b9c1da681322d360ec85821569b0778a64bab4d83be50a615ab3b5ba91322d360ece4298160eed6d214c8b56933a966645b9c99d485322c1db6d3582156eedc5da14c8b4d8fba90a605
  | 4, 0, 3 => 0x83b4d0a76302d5a9af1712656e74d799e4c8b4d962ed466459341db685302c560ebb429716ed2675214c8b73a6b2502645ab4e1767e322d5a9ae74019169b076da04c0b4d79b6d0a605b9c91a685322d160ed34298169b075da04c0b3f83b4d0a605
  | 4, 0, 4 => 0xb9cfd9485322d5a7f2778191681076da14c0b4d83bc530645a6c1de279302c1dfabb429916e74d6ea650ab4083aed0a605a6cfd9885322dce0ed3599e56ad2478bb532b075da14e2605a6bd57685322d368ac94298169b246da14c0b738b41dae855
  | 4, 0, 5 => 0x8a2ed0a7a302dce0edb69a796c94d78b7532b4d83b6d0a6d5a6c1de2994c2d360ed0429816e70776a650ab56a6c7de2a75b9d35ba79322d360ec859ac16ad3675214c8b1383aed0a605ab425d485322d363ebb51a156a9075dac8c8b4d6eb6d0a605
  | 4, 0, 6 => 0xab53658db4dad59bebb4299160eed5da14c6b4d83aed607f5a6c7dd48530ad5aa2f1711916c90778bb532b568fbe976855ab4be0ef1322c1d94bb4298169b07821e4c0b73a6c1dd8b3583bb5b685302d5a0ef1772656ad1475a14c8b7383b218cb35
  | 4, 0, 7 => 0xa6c1db6a242adce0ed34ca1560efe5da14c4b739fb8d0a645a6c1db6b2422dce2ed55da156ad1478a00c8b7376b74ec645b9c1db6d3592d360ef94298169b077ca890ab4d83bc5b6b05ab5367ee5542d5a9b22789916e70776a00c8b4d83b6d46855
  | 4, 0, 8 => 0x5ce9ace3d1916ad305da14c8b3f8a2ed0a605a6cfd9a85302d5a9ae6429916e71475214c8b4d83b6d64b05
  | 5, 0, 0 => 0xab5364cea42991aad095da14f4646b9d3658ea42991a9b1983aed0a646ab5360af140191aad3f69ad10a646a6cfd688532181aad0776b6d0a516ab5362eea42991aad4d6eaed32856ab53624ea42991ae73f932ed0a646ab5360ee15dacdaad4d83be50a546b55360ebb52215a9b1483aed0a606
  | 5, 0, 1 => 0xab4d976853d191aad4d8bbad0a646004520ebb429816ad4d83c10f2516ab53662bb4ca15aad145da1500646acd360ebb5993da9b1b83b6d0a646ab5360ee13b191aad3f72b8d0a646ab535babb5993daad4d963a966646a6c91768532175ae72683ae10a646ab536490778a65aad3f82bc10a646
  | 5, 0, 2 => 0xab41ddabb5995580156933a90a645b15360eea42991aad4683bc4ec6460055aa324789916c34d962ecf4646ab4a22cbb42991ae74583b4d0a646b9d360ebb40991aad388baed0a646b9cfe0ed342991aad3f652ed0a646bb5363eea42991aad4d9fb890a6460041db685300056ad278baed0a646
  | 5, 0, 3 => 0xab3c9a6bb42991ae74d83b6d02646b9d320ed742991aad4d79a450a646a6c1d7685320b1aad4d78b890a646b149a0ebb42991ae74d79b6d0a646ab4ba0ebb4ca15a0eed5da14c8606b4d360edb42945ae94d83bc4ec646b9c9a0ebb42991ae71782aed0a646ab5367eb45993da9b075da1506636
  | 5, 0, 4 => 0x55a9b074294d6e74d83bc532856a6c1d76a451215ae7076aaed0a5c6b241da6bb42991aad0776aed32856b9c9a0edb42991acf4d8baed0a646b65360ebb4f1918014d83b6cc03f5ab3f1e6bb42991add0769aed0a646ab535babb3c991a9b4583aed0a606ab5367ee540191aad4d753890a646
  | 5, 0, 5 => 0xb9d367ee542991aad4d78b7532766a6d160edb42981aad076db4d769e6ab4fe4ebb41991aad2478bb50a646a6c1d76853a181a9b3f83b6d0a606ab41ddabb5993dae70769a14ec646b2d363ebb59a15aad4d83c11224f6ab41da6bb52215a9b075da14fe606ab5363ebb52a15a9b075da910a606
  | 5, 0, 6 => 0x8fc520ebb42981ae74d83aed50856bb53658ea42991ae75083aed0a5c6b75360ebb5993dae74d83b6d58856ab5360ef942945aad076431976b36b9d368ac942991ae74d9236d0a646ab41deeea42991aad4d9fb9566646ab4ce0ebb4f191ae74d5c214f4646b9c1db6d359a15a371483aed0a646
  | 5, 0, 7 => 0xa6c1de2bb58191ae74683aed0a646ab535d4b842991aad3f76b750a646b9d020ebb42991aad4d83b6d3a856ab5363eea59a15a9b075da8d0a646b9c1d768538991aad4d962ed36646bbd360ef13b191aad4d923c532646ab536430778991a9b0778b6d0a606a6cb20edb42981aad4d83bb176b36
  | 5, 0, 8 => 0xb9d360ebb599e5a9b1683aed0a606b2d360ebb4f191ae11483aed0a646b24520ebb42991aad4d702ed0a646b1535babb42991a9b0782b6d0a606a6c1db6b358215a9b076da14ec606ab535d4de42991aad4d83bc54e646b9d360ef13c991aad4d73aecf4646b9d360ec859a1580156a6aecf8645
  | 5, 0, 9 => 0xb95360eea42991a9b075c214c8606ab449dabb42991aad3f933c50a646ab535ba9142991aef077f2ed0a646a6c1de0bb4298da9b075da14e6646b9d35badb42991aaced753750a646ab3b5b8bb42991aad0778bb532766ab535e2b440191aad4d9fb150a646b9d020edb42991ae7075da14c83d6
  | 5, 0, 10 => 0xb9c4e0ebb42991aad4d83ba93c646ab5360ef14b991aacfc6eaed0a646b9d360ef140191a9b075dac908646ac53e0ebb429918014d83b6d60855b5d360ebb5993dae74d83b6d66796ab41ddabb40191ad14d9fad10a646b7d362ebb42991ae74d83b2176b36b1d360eea42991aad2c76aecf4646
  | 5, 0, 11 => 0xb9d360ed042991aad4d892ed48856ab5365abb5993dae74c8baed0a646ab4b24cea42991a9b075da890a646b25362ebb42991ae72c932ecf4646ab49a0ebb4f191add4d8baed0a646ab53676bb4f93daad4d8fbc4ec566bad360eea42991ae72882aed0a646a6c1d76b142981aacef6e2ed06646
  | 5, 0, 12 => 0xab546490778991aaced6eaecec646ab53614ea42991aad077d2ed0a646b4d3624bb42991ac50776aed0a646b9d360edb4f215aad07783550a646b8d3658bb3d191aad4d83aed66506a6c1d76b258191aad4d83b2166916b9d360ef952215ae70776aed0a646ab5360f043b155aad4d8baed48856
  | 5, 0, 13 => 0xab5367ee142991aad3f71aed0a646b4cfe0abb42991aad0776a450a646ab5366abb4d191a9b1f83aed60856ab421dabb42991ae70776b6d0a646a6c1dd48532185a9b07662ed0a646b9c1ddebb41991ae7145da14f4646b9d35e2dd3b191a9b076da14c01c6a6c1db6c942981a9b078236d0a606
  | 5, 0, 14 => 0xb9c1daeba42991a9b1583aed0a646b9c1d94bb42991aad4d9fc1de2996ab49e0ef05d99180156a6c1cc8435b0c9a0ebb42991aad0769aed32856a6c1d769942981ae74d83c10f26460055a9b075d9416ad4d8faed28856b0d360eea42991aad077c2ed0a646b15360ebb52215ae70d83aed0a646
  | 5, 0, 15 => 0xa85360ebb42981aad4d9fb9d0a646a6c1db6b442981aad0778b4cec646a6c1de27632181aad4d6eaed3c646b0d3648bb42991aad4d83ae5664f6b9c960ebb42991ae54d6eaed0a646b25360ef14c991adb4d83aed3c646ba3b5babb42991a9b076aaed0a606ab451d4bb42991ae74d83b6d48856
  | 5, 1, 0 => 0xab53658db3d145a9b075dac10a4f6add360ebb4ca15a9b075daad0a646005ce9b0778a656ad4d83b1d76b36ab53696dd3b19180156a6c1cf0645ab535e2b83d191aad077baed48856a6d320edb42981af107782e90a646ab545e2dd3b191aad4d672ecf4646b9c1da6bb42981ae70778bb4ec646
  | 5, 1, 1 => 0xab4d20ebb42991ae74d83b6d64856bbbb5babb42991ae74d8b41db685600535b685300516e74d83be50a646ab5356e8540191aad1483aed32856ab4da0ebb5993dae7076db4d0a606bbc1ddebb42991aad4d9fc1d90b36b9c9e0ebb41991aad265dae0f4646b4c5a0ebb42991aad4d83bc576a86
  | 5, 1, 2 => 0xb9c520ebb42981ae74d83b6d62856005ce9b07642cd6ad1483bc4ec6460055a9ab5429916d30777aed0a646ab4b1a6bb3d191aad0776aed3c646a6c1d769942975a9b2c5d9e8c8606b2c1ddabb42991ac34d6eaed0a646a6c1d7685320a9aad1483aed667f6ab5360edb4da15a9b076da1508606
  | 5, 1, 3 => 0x5360e85300716e70769aed0a646b9c7e28bb42959aad4d83aed489e6ab41ddaea42991aad4d712ed0a646ab5367f2778991aad4d8baed328560055aa30778a656c34d9fad10a646b95360ebb52215ae74d83b6d76b26aa41d76b042991aacf376aed0a646b9c1db6d342945ab14d83b6d0a516
  | 5, 1, 4 => 0xa6c1daabb4297dac92683aed0a646b9cfe28bb42991aad466eaed0a646ab4fe2cbb42971aad4d8bbc4ec646ac41da6bb42991ae74d9fb350a646ab5367eb454215ae7175dae90a646b4d360ebb4f191ae7076bb4d0a646ab535e2dd5da65aad4d9fc1db69e6a6c1de27632175aad077e36d0a516
  | 5, 1, 5 => 0xb4c1daabb42991a9b075daa90a646b8c9a0ebb42991aad4d8a3a90a646ab53648f159991ae74d83aed667f6b9d3648f142991a9b075da14c8416a6c1db48541991ae54d8faed0a566ab491dabb42991aad0769a450a646bb5360ef942991aad4d72aed00646b0c1ddabb42991801568bb5576855
  | 5, 1, 6 => 0xb9c520ebb42991aad4d78b7500646a6c1db6b042991801568a3a90a645b9d360ef16dacda9b1f5da14f4606b0d360ebb52215a9b1883aed0a646b4c9e0ebb42991a9b1c83aed0a606a6c6d76853d191ae73683aed0a646005ce9b076da7969b075dabd0a646b9d360ebc42991ae74d83b6d32856
  | 5, 1, 7 => 0xab45176853f191a9b1a83aed0a646ab41dded742991aad4d843c4ec646a6c1da8bb42991aad4d9fc7de2b36ab535e2e23b191a0edb69aed0a606ab41df8bb5993dae707632ed0a646b9c1dc6bb42991aad4d963a576646ab535bcbb42991aad4d83bc4f0646b9c1da6853c991aad0778bb576996
  | 5, 1, 8 => 0xa6c1db6ba42981aad265daccf4646a6c1d76b35813daad4d5ca7d0a646b9c9976853d191aad077e3c4ec646ab5365af142991aad4d932ed00646a6c1d76853c981aef4d6eaed0a646ba41ddabb42991ae74d962ed00646b9c520edb42991acb4d83b6d0a516ab4a20eef5d991ae74d962e0f4646
  | 5, 1, 9 => 0x55a4cbb401916ad4d83b6d02516a6c1db6853c981ac54d962ecf4646a6c1d9abb42981a9b076da14c0146a6c1db685300b5aad3f76ad10a646ba535e2dd3b191ac94d6eaed0a646b5d360edb59a15aad2478bb4ec646ab535e6db42945a9b075da610a646b2c7e28bb42991aad4d93aed00646
  | 5, 1, 10 => 0xab5363ebb53a15ab54d83aed48856ab47e28ea42991ae74d9636cf4646b9cfe0eed42991aad365da7d0a646ab499d4bb42991acb0769aed0a646ab49a0edb42945aad0778bb500646a6c1db685300fdad34d6eaed0a646b9d360edb58215aad4d83bc528646b9d35ba853b19180156a6c91e2995
  | 5, 1, 11 => 0xab535d4b742991add0776aed0a646b9c1d90c64299180173a6c1db6b25ab41dd4d342991a9b0775214c8606ab41da6bb40991ae75283aed06646b95360ebb5993daa3075da14c85d6ab535e2dd48991aad4da2b250a516a6c1d76994c215ad34d9fad10a6460055a9abb429616acf369aed0a646
  | 5, 1, 12 => 0xb9c1dda853b191ae7077e2ed0a646ab535e6bb5993dae70782b5d0a646bc41ddabb42991aad3f8a3c50a646ab41ddabb52215ae74d83bc532646ab5363ef140191a9b076da14f4606b241ddabb42991ae74d83bb10a6469341d768532181ae74d842ed0a646ab3c5dadd3b191aad4d992ed26856
  | 5, 1, 13 => 0xab49a0ebb5993da0eed5da14c8626a6c1da6bb42981a9b1e8daed0a646a6c7e36bb42959ae707782e90a646ab5360ec55dacdacd4d892ed0a646ab491a6bb42991aad4d83aed66926ab45e0ed55da15a9b245da14c8606ab5360edb4294daad2683aed32856ab53568a742991ac94d78b74ec646
  | 5, 1, 14 => 0xab535badb42945ae74d8fba90a646ab41df89142991ac34d83aed32856ab45ddebb42991aad4e842ed0a646ab41de2ee3b191a9b075dab10a5e6ab4be0ebb42991a9b076c2ed0a646b9c1df8db42991a9b3a83aed0a646ab5020edb42945ae7178a2ed0a646ab5363ed15da15aad4d79bc4ec646
  | 5, 1, 15 => 0xa6cfe3ebb42981ae71683aed0a5c6ab5367f0778aa1ae74d5a21500646b9535b8bb42991a9b076db4d0a6060041da6bb429816ad4d79aecf2646ab49a0ef13b191a9b3f8daed0a646ab47ddabb42959aad4d7a2ed0a646ab41de2ed48991aad4d64aed02646ab5360ef948215ae74d8fc1d76b26
  | 5, 2, 0 => 0xb241de2ed3b191a9add5da14c86060041db6d3429816ad076db4d22856b0d360ef13b191ae14d8faed0a566ab535babb59955aad4d912ed0a646b25363ebb42959aad5183bc532646b2d362ebb42991acb4d892ed0a646ab45a0ed75da15ae54d962ecf4646bbc1de2ed3b191a9b075da14c82b6
  | 5, 2, 1 => 0xab5365af159991ae74d83b390a646005929b0778a6569b078336d0a606ab535ba7632155aad4d9dba90a646b4d363ebb42959a9b075dab90a646a6c1db6bb58215aaced6eaed66646ab5367ee442991ae6ed6eaed0a646ab53572853d191a9b1e832ed0a646a6c1db68541981aacdd69aed0a646
  | 5, 2, 2 => 0xa6c1db2bb42991aad0769aed66796
  | 6, 0, 0 => 0xb9d3625075da14c8e00a6c7e0ebb42981ae74d83aed3285323d5a9b4783aed0a647ab5363ebb42a00c8e00ab4a20abb42991aad2683aed0a64273d5a851483aed0a647ab535e6f15da14c8f73a6cf20ebb42991ead4da5c1de276323dce9b075da14c82f7b75360ebb59a14c8e00ab41d76853b991aad4da2c1d76b342b802ad4d83bc500646
  | 6, 0, 1 => 0xab49a0ebb429909ef56a6c5176853d191ead4d83c15769e323d5a9b075dacd48857ab5367eb442a0cc8f56a6c1de2ea42991ead4d83aed669f27b802ad2c932ecf46460055a9b245d9907ed56a6c1d8abb42991c015ea6c1d76852735ce9b1783aed0a647005869b075d9907ed56a6c1d768532061ec94d83aed6685323802e74d83aed3c646
  | 6, 0, 2 => 0xab5362ebb429f8c8f56a6c91768532139ead4d962ecf4642d3d5a9b075da14c84a7b4d360ebb59a14c8f61a6cfe0ebb42991ead4d894417685323dce9b0778aed66647ab49a0ef15da14c8e00ab535ba85320b58015683bb57685323002ac85320b428016ab41daed35da14c8f73a6c9a0ebb42991ee74d83b557685323dce9b075da14c8027
  | 6, 0, 3 => 0xb0d3659075da14c8f73a6c1db6b442991ead4d83b6d0a7928b802ad145da14f4646ab47e29075dacd0ae00ab535e2dd3b19180157a6aed0a640a355a9b076da14a21470055a9abb3d1900ad56a6cfd9abb42991eef0778bb57685323802e74d83ba90a6460055a9b07789908ad56a6c1d768534991c01566eaed0a6400b5ce9b2783aed0a647
  | 6, 0, 4 => 0xab5360ef159a44c8f56a6c1d768532079c0156a6c1d76641a35969b075da14c8517ab5360edb429447ee00ab41d7671320fdaad2683aed0a76323dce9b075da14c80f7b9d3699076da14c8f56a6c91e2bb42991ec34d83bc57685323d5a9b175dad90a647b9d429b075da14c8f56a6c1d768532059c01739341d7685323002ad0777aed06646
  | 6, 0, 5 => 0xab5360ef14299020e00b9d360edb59a15aad4d83bd97685323802ad4d320fc5a146ab535babb42990aae00ab41da6bb42939aad4d83aed3c9a323802ad4d83b6d769e60058a9abb4299028d56a6c1d78bb42991ead4d83bc57664233d5a9b076daed32857ab5367f075daa10af69a6c1d76ac42991c015686c1d7685323002ad3f5a214c8016
  | 6, 0, 6 => 0xb95360eef5da14c8e00ab41daeba42991aad4d83aed0a70323d363f1b83aed0a647b5d360ebb59a14c8f56a8c1d769942991c0156a6b7576641fb002ad07652ed0a6460055976641f85002d6ea6c1d768541991c0156a6c3176641cb002e74d922ed0a646ab5366f075da14c8f56a541ddabb42991e9b075dae90a64303802ad075da14c8076
  | 6, 0, 7 => 0xab53676bb4fa14c8f56a6c1dfebb42991ee74c83aed0a83323d5a9b075da290a647005ce9adb4299028d56a6c5a0ebb59a15ead0769aed0a640a3d5a9b0778bb4ec647a6c1d76853218028f5683b4d7685320b5ead4d924157685323d5a9b0778b6d76b37a6c1d7685321805af56a6c1d768f42991ec34d83c157685323d869b075da14ec647
  | 6, 0, 8 => 0xb9d3697075da14c8e00ab5360ef14899180164a6c1d769942b55a0eef5da14c85c7b9d360ebb58214c8f73a6c1db68542191ead4d6eaed0a64273d5a9b0770aed0a647ab5360ebb4299050e00ab41dda85320b5ae74d94c1d76853238029b075da149c006ab5360eea42990a2f56a6c1d768534191ef14d83aed0a83323d5a0ed35da14f2647
  | 6, 0, 9 => 0xab5360ebb4f270c8f56a6c1d76ba5993dead4d83b6d0a7a28bd5a9b075da650a147ab53658bb5c1e8c8f568fc1ddabb42991ee74d83b6d7685303802ad4d9fad0c83f60055a9b3f5c214c8d56a6cb576b342991ead2683aed0a6428bd5a0ed35da14c83f7ab5360ef16d9d8c8e00b05360ebb42939a9b075da14c8601fbd5a912683aed0a647
  | 6, 0, 10 => 0xab5360ebb5993c5ae00b741d76853200580164a6c1d0a6416b5ca9b075da14c8567ab5360ebb4299096f56a341de2bb42991ead4d9ec1de285323d5a0eff69aed0a647ab5360abb42a00c8f56a6c1d76853205dead4d823cd7685323d5a29076daed0a647ab5360ebb429a8c8e00ab41de2ed3b191aad4d6eaed0a6427b802dd4d83a14c82d6
  | 6, 0, 11 => 0xb2d360ebb42990b8e00b9d350a641685180176a6c1dd48532355a9b075da9120857ab47e28bb429e8c8e00ab5360ea4428b5ae74d8fc1d76b342b802c9075da14c8016ab5120ed35da14c8e00ab5360ef13b139aad4d83aed0a6413bd5a9b075da850a647ab53649075da650af74a6c1de2bb42991ead4d83aed664f0a3d5a9b3f5a214c84e7
  | 6, 0, 12 => 0x55a29075da149cd56a6cfd68853213dead4d9fc1de280323d5a9b1f5da1506567005cd76853205002c00ab49e0ebb4199180169a6c1d0a6416b55a0eed5da14c8557005ce9b075dac8c8d56a6c1d768532075c0164a6c1de27632355a9b07789d8c81670055a0ebb5221402d70a6c7e0ebb42991c0161a6aed0a4e0a35929b1f83aed0a647
  | 6, 0, 13 => 0xa6c1d76853d190c0f69a6c7e0ebb42991ead4d83b9d7685323d5a9add5da14ec647ab5360ef15dab4c8e00ab41ddabb320fd80156a8c91768532355a9b2c83bbd76647ab5360ec35da14c8f56a6c1de27632051ead4d9fbc56885323802e74d83a14c81c6ab5361d075da14c8e00ab5365abb42991aad077f3b57685323802e74d6eaed0a646
  | 6, 0, 14 => 0xab41ddabb429909cf56a6cb1b6bb3d191c016ea6c1d76641fb55a9b076db4d0a517ab4fe0eed5da14c8f56a6c1d769e320d1ee74d83aed0a641e3d5a9b2483bc4ec647ab53576b7429e8c8f56a6c1d768532085ead1483aed0a6416bd5a9b075da1d0a647b95360ed55da14c8e00ab535768532029aad0769aed0a7a323dce9b2883aed0a647
  | 6, 0, 15 => 0xb75360ebb429909cf5683bb576853213dee74d83b5d7685323d5a9b1f8a2ed0a5670055a9b075da907ed568a41d7685320fdc0156a6c7d0a5616b55a9b3f83bc566647005929b075d9907ed73a6c3e0ebb42991ee74d9fc1de285323d5a0ed35dacd0a647005ce9b3f5a214c8d56a6c1d768842991ead4d83ba90a642e3d5a9b4983aed0a647
  | 6, 1, 0 => 0x55a9b2c5d9e89cd56a6c1d76b34ca15c0169a6c1d76641fb5929b075da14c84e7ab5360ebb429904af64a6cfe0ebb42991ead2783aed0a642e3802ad07429385a016ab535b8bb5d214c8f56a6c1d82bb42991ead2c83bb57685323d5a0ef076aed0a647ab5360eb959a14c8f73a6c1ddabb42991c0173a6aecc83f0a3002ad1f5da14ac016
  | 6, 1, 1 => 0xab5360eec5da14c8f56a6c91768532171ead4d83aed0a64193dce9b075dacd0a4f7b9d3639075da14c8f6ea6c1d76853213dc0172a6aed0a640a355a9b2c5dae8f4647ab5360ebb522149cf56a6c1db68541945ead4d922ed0a642b3d5a0ec8632ed0a647ab535babb42990a2f77a6c1de2bb42991ead4d9941d769942b802ad076db4d0a516
  | 6, 1, 2 => 0xb9d363ebb429e8c8f56a6cfe28bb42991c017383bb5768532355a9b175da14c82d70055a9abb4f19028d56a6cb1767a320b5ec94d9641d7685323dce592683aed0a647b9c1e0abb42990b8f69a6c1d768532139c015683b4d7685323002ad1f8a2ed0a566b4d367f075da14c8f56a6c1d76a842991edd4d83bc57685323d5a9b076aaed66857
  | 6, 1, 3 => 0xb9d360ef1429d8c8e00ab5360eb942991ae34d9641d7685323d5a9b245da650a647ab49e4d075da14c8f56a6c7d76b34fa15ead4d83bc576a442bd5a9b2183aed0a647ab41ddabb429d8c8f56a6c1d7685320e1ef14d83bc17685323d5a0f056baed0a647b9d367d075da14c8f56a6c1de2bb4c991c0156a6c1d769642b5929b0778aed0a647
  | 6, 1, 4 => 0xab53608dd5da14c8f69a6c1de2bb42991ead4da1c1d7685323802ad4d83aed32856ab5360ef1599d8c8e00ab5363ebb2b0fdaad4d83bc5ba76323da69b2c83aed0a647b4d360ef05da14c8f56a6c5d7685320fdee7076db4d7685323802ad175dae90a646ac5360edb5da14c8f4d83aed74853217dead3683aed6685323d5a9b125da14c83f7
  | 6, 1, 5 => 0xab5360ebb4299060f64a6c1e0abb42991c0173a6c1d76a442b55a29075dacd0a6470055a0edb4294402d4d83aed0a8332181ead4d93c1de2bb323802ad075d9387e0160055a7f145da14c8d73a6c1d768532015ead4d83aed329542bdce9b075da14c8167b0d360ebb5a214c8f5683bc176ba42991c0156a6c1c9c3f16b55a9b076da450a647
  | 6, 1, 6 => 0xa6c1d768541990bce00ab4260ebb42991aad2683aed0a642d3d5a9b075daccf2647ab5363eea5da14c8f56a6c1d768942991c0173a6c1db68527355a9f075da14c81c70055a4cbb4299028d56a6c1d76a742991ec54d83aed0a640a3d360f065da14c8607b9d360ebb429e4c8e00ab5360ebb599fd80156a6c91e28532355a0efc6daed0a647
  | 6, 1, 7 => 0xab535babb42990b8f56a6c7de2bb42959ead4d5dad10a80323d5a9b0774aed0a647ab53676bb429e8c8f56a6c7d76853f959ee74d83aed0a64093d5a9b085da14c8167ab41ddabb42990a2f62a6c1d7685320fdc01569b41d768532355a9b075da14cc647005360edb4299000d73a6c920ebb42991ee74d83aed0a64263dce9b076dae90a647
  | 6, 1, 8 => 0xb9d4a9b075da14c8f56a6c1e02bb42991c015683b4d0a6416b002ad4d83b08c8376ab53624bb429e8c8e00a6c1d0a64300b5aad4d864157685323dce9b076da14f2647005869abb4299028c00b9d360e852711dae74d9541d7685323dce9b0766aed0a647b9d360edb4299028f73a6c1d90bb42991ead4d83aed669127bdce9b076da14c82d7
  | 6, 1, 9 => 0x5a60f055da14c8d56a6d060ebb42991ead4d9ac1d769e323d669b075da14c82f70055a9b076d9447ed73a6c1db685320fdead4d83c1176852abd5a9b075da14e46470041d76853218002d56a6c1d768533991ead4e83aed0a640b3802ad1483aed0a646b9d360ed25da14c8f56a6c5d76853d191ee74d83aed0a64213dce9b075da14c8097
  | 6, 1, 10 => 0xab5360ebb52214a2f56a6cfd688532171ead0777bb57685323802e74d83a149c2d6ab5360ebb4ba14c8f7383aed748541991ead4d962ed667a323802e74d8f2ed0a646ab47e0ed35da14c8f73a6c1d768540191c015683b19768532355a9b265da14f4647b9d360ebb42a08c8e00b9d363ebb429598015683b8d76853235ce9b2c5da14f4647
  | 6, 1, 11 => 0xab5360ed15da14c8f56a6c1d9cbb42991ead4d78b7576b3323802ad075da650a01600592a3075da14c8d56a6d160edb42945ed34d83aed0a6428b802ad4d83aed0a336b9d35e2dd5da14c8e00b9c1d768527005aad4d9fc1db68528bd5a0f0476aed0a6470055a9b074ca145ac00b9d360edb42981aad4d8faed0a762b3d5a9b077f2ed0a647
  | 6, 1, 12 => 0xab5360ebb4299034f56a6c7d76b742959c015683aed664f00b55a9b077cba90a647b9d569b075da14c8e00ab5360ef14c9d980156932ed0a7a3235ce9b075da14c8137b15360ebb429e8c8f56a6c1d76853206dc0156a6c1d664f16b0020ebb4299002006ab5363f075da650af56a6c1de2b842991ead4d9fcf16885323802ad4d962ed00646
  | 6, 1, 13 => 0xb95360edb5da14c8e00b9d360eb842991aad4d8fc1de2bb59bd5a0eed5da14c8567ab54649075da14c8f569341d76b842991ead4d8fc1d76b33fb802ad0769aecc83f6005360ebb321807ed56a6c1d76b35493dead4d8fc1daabb42bd5a9b2c752ed0a647ab5360ef16da14a2e00ab4260e85320b58015683aed0a640fb55a9b2c83b6d0a517
  | 6, 1, 14 => 0x55a2907429905ad73a6c1db6b342991ead4d8fc1de276323d5a9b0778b5d0a647ab5160ed35da14c8f56a6c1d768532019ead4d83c097685323dce9b075da14c83e7005ce9b076da14a2c00b9d360ebb270fdaad3f83b4d7685323802ad07789d8c8016a6cfe0ebb42990c0f73a6c6e0ebb42991ecb4d83b6d7685323dce9b076da14f4647
  | 6, 1, 15 => 0xb9d367f065da14c8f56a6c1de2bb59955c0172a6c1d76852735929b075da14c85c7b9d360ebb56214c8e00a6c1d76641f801aad4d83aed0a6b323d5a9b075da14c80b7ab5360f056da14a2f73a6c7e0ebb42981ec94d83aed0a642b3d5a9b0f83aed66857b75360ebb42990b8e00ab5360ebb428d580156a6c1d76991fb5ca9b3e83aed0a647
  | 6, 2, 0 => 0xa6c1de2bb42990c0f56a6cfe0ebb4ca15c0165a6c1d768527355a590769aed0a647b9d320ebb42990b8f73a6c1d768532091ee74d83b4d7685323d3659075da14c86070055a9b0745a14c8d56a6c1de0db42991c0156a6c8d768532355a9b07753a10a647ab535e6db5da14c8f56a6c49768541991ead4d9fc597685323d5a9b3983aed0a647
  | 6, 2, 1 => 0xb25360ebb4ca14c8f56a6c1de27632155ead4d83aed0a64103d5a9b077536d0a647ab41de2ed5daccc8f65a6c1d76ba42991ead4d83b6d7681323da69b075da14c8567b9c1de2ed5da14c8e00b9d360ed742991aad077e2ed6685323d5a0ef169aed0a647ab5360ebb4ca149cf56a6c1d76b332091ead0776aed6885323d5a9b075da910a5c7
  | 6, 2, 2 => 0xab5360ef15da650af56a6c1d769e32051ee74d83b6da685323802e70769aed0a646b9d360ebb4299006f569fc15768541991ead4d9641d769942bd5a9b075da14d8647ab49a0edb5da14c8f65a6c1d7685320b5ead4d9fad10a642dbd5a9b3f83aed664f7ab5360ebb4ea14c8f5ca6c1d7685320fdee54d83aed0a640a3d5a9b4b6eaed0a647
  | 6, 2, 3 => 0xb9d367f1f5da14c8e00ab5360eea4293980156a6c5d0a6416b002ad4d961e8c82d6ab41da6bb429d8c8f73a6c1d76a642991c0156a6aed0a64043002ad4d89214c82d6a6c1e0abb42990c0f56a6c1d8ebb42991e9b075dacd6085323d360ebb429d8c8607ab5360ebb4299008f72a6c1d7685320fdead4d8faed66853d3802ad4d842ed0a646
  | 6, 2, 4 => 0xab5360eea5d214c8f56a6aed70853d191ead076db4d76b342b802ad2c5d9e8c8016005969b1f5da14c8d568bc1d76ba42991ee74d95c1d7685323d5a9b3f72aed0a647ab5360ef13b1909ce00ab449768532005aad4d83aed3c641fbd5a9b0778aed664f7ab5367f07789d8c8e00ab4520ebb320fdaad4d9641d76b327bd8a9b075da1506647
  | 6, 2, 5 => 0xab5360edb5ba14c8e00ab41d768532065aad4d83ba90a6416b802e7076db4d0a646ab5360edb5dab10af56a6cfe0ec842991ead4da441d7685323802e74d83aed328560055a9b0a429904cd56a6d1592bb42991c0173a6c1d0a6423b55a9b246daed0a6470055a4d075da149cd69a6c1d76b442991c015676aed0a640a3002ad077e2ed0a646
  | 6, 2, 6 => 0xab5360edb64a14a2f56a6c1e08db42945ead4d83c1576b327b802ad178a2ed0a646005929abb4299028d73a6c1e0cdb42991ead4d83c017685323d5a4d075da14c82d7ab53616bb429907ef56a6c920ef142991c0173a6c1d76b327b55a9b2c83bc4ec647ab53618bb5a214c8f73a6c1db68541991c015683bc1748532355a9b0782aed32857
  | 6, 2, 7 => 0xab4de4d075da14c8e00a6c1db6bb429818016283aed0a6400b55a4d075da14c83f7ab5360ebb42994c8f61a6c1d76ba42991ead1483bc57685323802ad4d8fba90a646ab5360ebb4ca4d0af56a6c1d80bb42991ead1483aed0a7f323dce9b1483aed0a647ab5360edb4294438e00b15360e85320b580156a6c9176852730029b075dac10a646
  | 6, 2, 8 => 0xab5360ecd5dacd0af56a6c1e08bb42991ead4d83bc57679323d5a9b075f2ed0a647ab5360ec85dacd0ae00b4d3576853205180156a6c4976641fb002e74d83bc4ec6460055a0e641f8b402d56a6cfde2dd42991ead4b83bb57685323d5a9b0778b490a647b9d3619075da14c8e00b253648bb42991ae54d83aed0a7a323dce9b075daa50a647
  | 6, 2, 9 => 0x55a9b075d9d06cc00b9c520ebb42991801568b41d76852e355a9b075da950a647ab535dadd5da14c8f73a6c1d768532101ead4d83aed488519b802e74d83b210a646b95360ebb59a14c8f73a6c1de2bb42191ead4d83c15e276323d5a9b075da78f4647b0d360ebb4299028f56a6c1d768532071ec34d83aed0a6416b802ad4d8baecc83f6
  | 6, 2, 10 => 0xab5360ebd5da14c8f569649976853d191ee74d8f41d7685323d5a29075da14ec647b9d363f076da14c8f56a6c1d7685320c5c0173a6c1da4853235869b075da14c83f7ab53658bb3d1909cf56a041db6bb42991ead4d83aed1c85323dce9b075da790a647ab5360ebb522810af65a6c1d76b342991ead1683aed0a83323802e7076da14c8016
  | 6, 2, 11 => 0xab53614bb429e8c8f56a6cfe4ebb42991ead4d83b117685323d5a9b1278aed0a6470058a9b075d9907ec00ab3b5babb42991aad4d79aed6685323802ad5183aed32856ab41da6bb4299038f56a6bc5d4dd42991ead0769b257685323d5a0f0469aed0a647ab5367f265da14c8f56a6c1d768642991ee74d9fcb17685323d5a9add6daed0a647
  | 6, 2, 12 => 0xab5360eea59a14c8f73a6c1d7685320a5ead4d83aed1885323802acbb4293828016a6c1d76853b190bae00ab5360e8d32091aad1483aed6e85323d5a9b0778aed006470057e9b075da149cd56a6c5de2bb42991c0156a6a149c2d0a3002ad075da14f6646b9d3659075c214c8f56a6cb1e2bb3d191ead4d83aed2c85323d5a9b076daed66797
  | 6, 2, 13 => 0xb9d367f055da14c8e00b9d360edb320fdaad2683aed6685323802e707429905a016ab535babb5d214c8f56a6c1d769942991ead168a41d7685323d5a0eef5da15066470055a7f265da14c8d62a6cfe0ebb42991c0161a6c1d0a4e16b5ce9b4583aed0a647ab5360ebb429905ef56a6cfdb6b442991ead4d78b750a76323802ad4d6eaed0a4e6
  | 6, 2, 14 => 0xb9d360ebb52214c8f56a6c1df2bb52215ead4d83b417685323802ad4d963a90a646ab4fe0ef176a14c8f56a6c1d7685320d1ead4d83c1176b327b802e74d8baed0a6460055a9abb429901ac00b9d3658bb3d19180173a6c1d0a6e3235a29b3f83aed0a647005860ebb4293802c00ab5360e8532069aad4d6eaed0a640b3802e74d892ed0a646
  | 6, 2, 15 => 0xb15360ef15da14c8f56a6c1dc8bb42991c0156a6cfd68852735ce9b075da14e8647b9d367f076da14c8f62a6cb20ebb42991ead4d83aed667f323d5a9b075faed0a647ab5360edb5da790af56a6c5d76853b191c0156a8c1de2763235869b075da14f4647b9d360ebb429fcc8f73a6c1de0bb42991ead4d894157685323d5a9add5da14c82d7
  | 6, 3, 0 => 0x55a9abb270fc28d73a6c1d768532119ed34d9441d7685323d5a9b3883aed0a6470055a9b3f5ba14c8d56a6c1e08f13b191ead4d83aed32852e3dce9b075da14c84d7ab535e2dd5d9d8c8f56a6c9176b342991c0156a6c1d768132355a9add5da14c83f7ab5360ebb4ca14acf56a6c1d7685320edee74d83ba97685323dce9b4583b6d0a647
  | 6, 3, 1 => 0xa6d320ebb42990c0e00b9d360e641f8b5aad4d843c57685323dce9b0778b6d0a647ab41daad35da14c8e00ab49a0ebb42991801568bc15768532355a0ed35dad10a647ab4a20ebb5d214c8f73a6cb20edb42991e9b075dad10a64303dce3f1483aed0a6470055a9abb4299022d5683bb5b6bb42991c0156a6b6d0a510a355a9b075da7906647
  | 6, 3, 2 => 0xab53658bb3d190a2f73a6c1db6bb59a15ead4d9fad10a641fbd5a9b07822ecf2647005de0eed5da14c8d56a6cee0ebb5993dc017383aecc83f00b5ba9b076daed0a647b15360f055da14c8f73a6cfe0eba42991ead0772b8d7685323802ad075da14c8446ab5360ef148a14c8e00b0d360ebb270fdaad0782bc17685323802ad4d5a214c8036
  | 6, 3, 3 => 0x55a0ed55da14b8d56a6c1db6bb52215c0156a6c91768532355a9b07789d8c85c7005969b07429905ad5683b5d76ba42991ead4d9fc7de285323d5a0ef176a14ec6470055a0eed5da149cd5683bf1e2bb42991ead4d83bc4ec642b3802ad075da14c80c6005ca9b07429905ad64a6c1db6bb42991ead4d83aed664f17bdce0ebb5d214c85c7
  | 6, 3, 4 => 0xab53685075da14c8e00ab41d769e32005ad34d83b6d7685323802dd4d83aed0a4e6ba535e2dd5da14c8f56a6c1d76b45993dead4d77b717685323d5a9b3f8faed66857005960ebb4299002d5683b55768541991ee54d8fc1d7685323d5a9b075da14c8337b9d360f056da14c8f73a6c1db6853b191ead0776aed0a640b3802ad4d83a78c82d6
  | 6, 3, 5 => 0xab53649205da14c8f4d83aed0a8432181c0156a6cfdca8532355a9b076dacd22857ab5360ef14c9d8c8f5693c1d768541991ead4d9fad10a80323dce9b075dac90a647005929b075da149cc00aed360ebb42939aad4d83b2d7685323d5a0eed5da14c8147b9d362d075da14c8e00ab34d768532051aad0776aed0a6416b8029abb42990c0146
  | 6, 3, 6 => 0x5a69b075da149cc00ab53576994285180156a6c1d76a842b55a9b075dae948857b0d360ebb42a0cc8e00ab5360ebb278bd8015ca6c1d76641fb55a0ef176aecec647005ce9abb4293828d5683bb57685320fdeb34d83aed6685323802ad4d83aecde646ab5360ef15da98c8e00ab5360e8528871aad4d6eaed6685323d5a9b075da6d0a647
  | 6, 3, 7 => 0xb9d360ebb58a14c8f76a6c1dd4bb42991ead4d88c1d7685323dba9b075da14c83f7ab5367f07429906ee00b95360ebb320fd80156a6aed0a5604b55a9b075da910a2d70055a0ebb429c4c8c00ab49a0e85320b58015683ba90a6400b002ad4d83bc5769960053576853205000d7383c15768541991ec94d83aed0a640a3dce9b07612ed0a647
  | 6, 3, 8 => 0x55a81075da14c8d69a6c1d768532051c015683aed0a642bb5a69b075da14c82d7ab5360ebb4a214c8f56a6c1d7685320d5ee74d83bbd7685323d5a9b075da14c8227b253649075da14c8e00ab41d768532149aad4d9fad16685323802cb4d83aecc83f6b9d360ebb56a14c8f56a6c1d7685320e9c0156a6c91769942b002ad4d5dacc9e146
  | 6, 3, 9 => 0x55a9b07429b846d73a9c1d768542191ead4d892ed0a7d323802ad4683aed0a646ab5360ef95da14c8f56a6cb1767a32171ee54d83aed0a64273d5a9b0772aed66647b9d360ebb4299038f72a6cfe0ebb42991c0000a6c1db685302dce9b07822ed0a6470055a9b076da450ad73a6c1dcabb42991ee74d9ec1d7685323d5a9b0777aed66647
  | 6, 3, 10 => 0xab5363ebb5d214ace00ab5360ebb599e5ae54d83aed0a6427b802ad4d85aecc83f60055a48bb4299002c00b0c1d768532005aacf176b757685323802ad4d789d8c8146ab5367f075da78c8f56a6cfe58f142991c0156a6c910a6416b55a9b1683b6d76857005a60ebb5d214c8d65a6c1d768532139c0161a6c1d0a6416b55a711483aed0a647
  | 6, 3, 11 => 0xab5367f0778214c8f58a6c1d768532071ee74d83b6d0a640e3802ad4d923c4ec646ab4fe0abb42990b8e00ab451768532051aad4d8fc1d76ac42bdce9b076db250a6470055a9b07751907ed73a6c1e08db42991ee54d83bc57685323802ad4d839d8c8166ab5360ebb4299090f72a6cb20ebb42991ead4d83bed7685323d5a0eed5da14f4647
  | 6, 3, 12 => 0x55a9b07642ed66d56a6c91768532165ead4d6eaed0a83323d5a9b075da14c8157ab5360eea42990a8f56a6cb24cbb3d191ead4d8baed6885323d5a9b0778aed3c6470055a4d075d9907ed5683bb576b342991ead0766b297685323d5a0eed6eaed0a647ab53659075da78c8f56a6c1e089142991ead4d8faed0a5616bd969b0778aed0a647
  | 6, 3, 13 => 0x2ad4d83c0d7685323d5a9b1f5da14ac3f7ab41db6d35da14a2f56a6c1dd48532069ee74d9dc1d7685323d5a0f047e2ed0a6470053637075da14c8d56a6c1d7699428d5ead4d9fc15e285323d5a9b0775214c84e7
  | 7, 0, 0 => 0x5ce9b4c83aed0a6470055a9b1f5da14f464700002ad0776aed0a6460055a592683aed0a6470055a0f055da14c85c7005ce9b075dad10a647ab5360ebb59a14c8148ab5360ebb59a14c82d80055a9abb429909c1470055a9b075dacd0a4f7ab5360ebb4ca14ec648ab5360edb69aed0a6480055a9b3f5da14c8147ab5360ebb5d2cd0a648ab5360ebb429e8c82d8ab53651075da1506648
  | 7, 0, 1 => 0x55a9b075da14c805700002c94d83aed0a6460055a9b075da14c8167ab5360edb5da150664800002dd4d83aed0a6460055a0edb69aed0a6470055a9b0a83aed0a6470055a9b0778a14ec6470055a9af15da14c8147ab53659075da14c85a80055a9b075da14c84770055a9b2c5da14c8147ab5360ebb59a14c83f80055a9abb429909e147ab5367f075da14c85b80055a9b3e83aed0a647
  | 7, 0, 2 => 0x55a9b245da14ec6470055a9b075da14c8127ab536970778aed0a6480055a9b075da350a6470055a9b0778aecec6470055a9b2483aed0a6470055a9b075da14c84c70055a9b075da15064e7005ce9b075da15086470055a9abb429d8c81470055a9b075d9907e39700002d34d83aed0a6460055a9b075da14f264700002e74d5da14c8146ab5360ebb429905a24800002ad4d83aed48856
  | 7, 0, 3 => 0x55a9b2c5da14f46470055a9abb4299028107005a69b075da15066470055a9b075d9907e3c7ab5363f076daed0a6480055a9b07692ed0a6470055a9b075da14c8427ab5360ebb42a0cc81480055a9b075da14c80970055a9b075da14c82e7ab5360ebb42a0cc82d80055a0edb5da14c8017ab5360ebb59a14f46480055a9b0766aed0a6470055a9b07642ed0a6470055a9b076da14c82d7
  | 7, 0, 4 => 0x55a0ebb42990280170055a9b076daecc83f70055a0ebb429905a017ab5363f075dae90a6480055a9b07429905a1470055a9b1f83aed0a4e70055a9af16eaed0a647ab53659075dae10a64800002ad075da149c0160055a9b075d214c82d70055a9abb42990a21470055a9b0a83a14c82d700002ad4d83a149c2d60055a0ebb5d215066470055a9b075da150064700002ad4d8faed0a566
  | 7, 0, 5 => 0x55a9b075dae8c83f7ab5360ebb59a450a64800002ad4d83b6d0a516ab5360ef176aed0a64800002ad4d83aec9c3f6ab5363f075da14c83f80055a9b07429905a237ab5368b076daed0a648ab5367f076daed0a6480055a0ebb429907e0170055a9b0746a14c82d7ab5360ebb5a214c85c80055a9b07429907e2d70055a9b075da14c8457ab5363f075da14c82d80055a9b075da14dc647
  | 7, 0, 6 => 0xab5367f075da14c82d8ab5360ebb429905a2980055a0ef176aed0a647ab5360ebb429907e3780055a9abb42990b8147ab5360ebb5d214c84e8ab5367f075dae90a6480055a9b075d9907e1470055a9b075da14c82470055a9b0769aed0a6470055a9b075d9907e2d70055a9b3f83aed0a4e7ab5360ef16daed0a6480055a9b075dab10a647ab5360ebb59a1506648ab53659076daed0a648
  | 7, 0, 7 => 0x55a9b07429b8c82d700002ad0769aed0a646ab5360f056daed0a648ab5360edb5da14ec648ab53659075dae90a648000029b075da14c86060055a9b075da14c80370055a9b075da450a6470055a0ebb429e8c8017ab5360ebb5d214c84f80055a9b0778aed0a4e7ab5360ebb429909c1480055a9b2c83aed0a4e7005ce9b076daed0a647ab5360ebb429909c2d80055a9b07429e8c82d7
  | 7, 0, 8 => 0xab5363f075dacd0a648ab5360ef15da14c81480055a9b075da149c467ab5360ef15da14c82d80055a9b3f8faed0a6470055a0ebb59a14c8017ab53659075da14c82d8ab5360ebb429909e1480055a9b075da990a647ab5360ebb429909c3f8ab5360ebb429909e2d8ab5367f075da14c83f8ab5360ef15da14c81680055a9b0759a14c82d7ab5360ebb5621506648ab5360ef15dae90a648
  | 7, 0, 9 => 0xab5360ebb429907e368ab5367f075da1500648005ce9b075da14c814700002ad4d83aed664f6005ce9b075da14c82d7005929b075da14ec647ab5360ef15da14c83f8000029b075da14c8006ab53659075da14c83f80055a9b0782aed0a4e70055a9b075da14ec4e7005ce9b075dae90a64700002ad4d83aed328560055a9abb42990280e7ab5360ebb59aa50a64800002e74d83aed0a4e6
  | 7, 0, 10 => 0x2ad1483aed0a646ab5367f075dacd0a648ab5360f055da14c83f800002ad4d83bc4ec646ab53649075da14ec648ab5360ebb429e8c84e80055a9b0c83aed0a6470055a9b075daa50a6470055a9b075daccc83f7005ce9b075da14c83f70055a9abb42990280f70055a9b1483aed0a647ab5360ebb429d8c81480055a9b07429905a247ab5360f055da14c82d80055a9b075d9e8c83f7
  | 7, 0, 11 => 0xab5360eef5dae90a648ab5360ebb42990a23f8005ce9b075da14f4647ab5360ef15dacd0a648ab5360ef16eaed0a648ab53659075dacd0a648ab5363f075da1506648ab5360ebb42990a21480055a9b3f962ed0a6470055a9b075da14c8377ab5360edb5da14c81c8ab5360ef15da14f4648ab5360edb64aed0a648ab5360f046daed0a6480055a9b075da790a6470055a9b0742a0cc82d7
  | 7, 0, 12 => 0x55a9b075da14fe6470055a9b07782ed0a647ab5363f1483aed0a6480055a9b075da910a6470055a9b075da0cc83f7ab5360f055dacd0a6480055a9b1f83a14c82d7ab5360ebb59a14ec64800002ad4d8baed0a64600002ad4d962ecf464600002ad4d892ed0a6460055a9b3f82aed0a64700002ad07429905a016005ce9b075dacd0a6470055a9b4583aed0a6470055a9b075da14c8297
  | 7, 0, 13 => 0x2ad4d839907e2d6ab5360ebb42990b8148ab5360ebb42990b82d800002c54d83aed0a646005ca9b075dae90a6470055a3f1483aed0a647ab5360ebb429e8c8518ab5360ebb42990ac2d80055a9b075da14c8467ab5360edb5dad10a648ab5360ebb42a0cc84e8ab5367f075da1506648ab5360ebb5d214c85680055a9b07752ed0a6470055a9b075da14e86470055a3f075da14c8017
  | 7, 0, 14 => 0xab5360ed55dae90a64800002e74d83b6d0a6460055a9b07429909c2d70055a9b3f83a14c82d70055a9b07429905a2970055a9b0c83aecc83f7ab5360ebb42990b83f80055a9b1f83aecc83f70055a0ebb5d214c85c70055a9b075dad10a4e70055a9b076daed6685700002ad075d9907e016ab5360ebb42990ac3f8ab5360ef15da1506648ab53659075da1506648ab5360ef05da1506648
  | 7, 0, 15 => 0xab5360ebb5a214c83f80055a59075da14c80170055a9b075d9907e377ab5360f045dacd0a6480055a0ebb429909e0170055a9b0778a14c82d70055a9b2c83a14c82d70055a9b1683aed0a647005ce9b07832ed0a6470055a9b07429909e2d70055a9b075da14c81070055a9adb5da14c8147005ce9b075da15066470055a0ebb429909c0170055a9b075dadd0a6470055a7f075da14c8017
  | 7, 1, 0 => 0x55a9abb429905a1470055a9b075d9909c3f700002e7075da14c80160055a9b3f83aecc83f7ab5360ebb429e8c85c800002c34d83aed0a4e600002e74d83a14c82d60055a0f055da15066470055a9abb5d214c81470055a9b07612ed0a647ab5363f0778aed0a64800002ad4d5da149c146ab5363f075da14fe6480055a9b075da650a767ab5360ebb429905a2680055a0ef15da14c8017
  | 7, 1, 1 => 0x55a9abb429907e1470055a9b075d9909e3f7ab5367f075da14c84e80055a9b075da14c81c7ab5363f075da14ec6480055a9b07822ed0a647ab5360ef15da14c85580055a9b0772aed0a6470055a9b3d83aed0a647ab5360ebb42a0cc85180055a0ebb429d8c80170055a9b0777aed0a647005ce9b1f83aed0a6470055a9b075dab50a6470055a9b0782a14c82d70055a9b07429d8c82d7
  | 7, 1, 2 => 0x55a9b0742990a22d700002e74d83aecc83f6ab5360ebb5a2cd0a648ab5360ef15da14c84e8ab5367f0778aed0a648ab5363f075dadd0a648ab53659075da14c84e80055a9b3f5dad10a6470055a9b075d9907e367ab5367f075da14c84f80055a9b075d9d0c83f7ab5360ebb59a14c82f80055a9b0778aecc83f70055a9abb42990281270055a9b2c83aecc83f7ab53677075dacd0a648
  | 7, 1, 3 => 0x55a9b1283aed0a647ab5367f075da14ec6480055a9b075da650a64700002cb4d83aed0a6460055a9b3c83aed0a6470055a9b075da14c82f7005ce9b075da14c84e7005ce9b3f83aed0a647ab536590778aed0a64800002e54d83aed0a6460055a9b3b83aed0a647ab5360ef15da14c84f80055a9b0782aecc83f7ab53659075da14c84f80055a0ebb42990a20170055a9b075d9d8c83f7
  | 7, 1, 4 => 0xab5360ef15da14ec648ab53659075da14ec6480055a9b0778aed66647ab5360f055da14c84f8ab5360ebb429907e398005ce9b0778aed0a6470055a9b2683aed0a6470055a9abb59a14c81470055a9b076aaed0a647005ce9b2c83aed0a647005ce9b075da14c84f7ab5360ebb42a0cc85680055a9b1783aed0a647ab5360f055da14c84e8ab5360ebb429d8c84e800002ad4d83aed3c646
  | 7, 1, 5 => 0x55a9b0742990b82d70055a9b076daed0a4e7ab5360ebb429907e3c80055a9b075da14c80f7ab5360ebb5a21506648005ce9b0782aed0a647005ce9b075da14ec647ab5367f075da14c85180055a9b0742990ac2d70055a9b07612ecc83f7005ce9b075da14c860700002ad2683aed0a64600002ad4d83ba90a6460055a9b075d990a23f70055a9b2783aed0a647ab5360f0578aed0a648
  | 7, 1, 6 => 0x55a9abb42a0cc8147ab5360edb5da14c83f80055a9b075dae90a4e70055a9b075a214c82d7ab5360edb5da14f2648ab5367d075dae90a6480055a9b075da149c477ab5360edb5da14c8148ab5360ef15da14c8518ab5360edb5da14c82d800002ad4d922ed0a64600002c34d83aed0a646ab53659075da14c8518ab5360edb5dae90a648ab5360f055da14ec6480055a0ebb42990ac017
  | 7, 1, 7 => 0xab5360ebb429905a1480055a9b075da149c3f70055a9b075da149c4c70055a9b075da149c497ab5360f0478aed0a648ab5360ebb5d214c81480055a9b075d990b83f70055a9b07429905a267ab5360f055da14c85180055a9b075d990ac3f70055a9b075da149c1470055a9b075da149c2d70055a9b4b83aed0a647005ce9b075da14c85170055a0ebb5a214c8017ab5360ebb59a7d0a648
  | 7, 1, 8 => 0xab5360edb5da14f4648ab5360ef15da14c85680055a9b1f5da14c8147ab5367f3c83aed0a6480055a9b075dad0c83f70055a9b075dae10a6470055a9b075da14ea64700002ad4d6eaed0a64600002acbb4299028016ab5360ebb429907e148ab5360ebb429907e2d800002ad4d429905a1460055a9b1f83aed66857ab5367f075da14c85c80055aa3075da14ec647ab5360ebb5d214c83f8
  | 7, 1, 9 => 0xab5360ebb5a214c84f8ab5360ebb429d8c8568005ce9b075da14c85c70055a9b0f83aed0a6470055a9b075da14f44e70055a9b3f83bc50a64700002ad4d9fad10a646005ce9b075da14c85670055a9b075da14c83c7ab5360ebb5a214c84e8ab5360edb5dacd0a6480055a9b076daed0a5170055a9b2883aed0a647ab5360ef15da14c85c8ab5360ebb429905a238ab53659075da14c85c8
  | 7, 1, 10 => 0x55a9b075dacd0a4e70055a9b0776aed0a64700002ad4d5d9907e146ab5360ef15dad10a648ab536592683aed0a648ab5360ebb429d8c85c80055a9b076baed0a647ab5360ebb5d214f4648
  | 8, 0, 0 => 0xab5360ebb429909ef56a6c1d768532139ead4d9fc1d7685323802ad4d83aecc83f6ab5363f075da14c8e00ab41d76853200580156a6c1d0a6416b55a9b075da1506647ab5360ebb59a14c8f56a6c1d76853d191ead4d83aed0a641fbd5a9b075da14c8147ab5360ebb429905af56a6c1d76ba42991c0156a6c1d768527355a9b076daed0a647
  | 8, 0, 1 => 0x156a6aed0a640a355a9b075dad10a647ab5360ebb42990b8f56a6c1d768532159ead4d83aed0a6428bd5a9b0782aed0a647ab5360ebb429d8c8e00b9d360ebb42991aad4d83bc57685323d5a9b2c83aed0a647
  | 9, 0, 0 => 0x2ad4d83aed0a646
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 31
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
  | 0, 0 => 0x1c7ff838fffff1c7f8838fff031c418838e030303c67807e3cff03c07807e00ff003fffc7fffff003ff8001ffff000007c7e3cff
  | 0, 1 => 0x3807007000fc00000000e00f31fc1f83fe03ff1ffff83f1ffff1ffff83f1c70c1fc1f83f003ff1fc1f83f0030c1fc1f83fe03ff
  | 0, 2 => 0xe0467fc0e3cffe0460fc0e3c03e04608c0004001fc1f83fe03ff1fc1f838003001fc0003fe00001f81f03f003fc1c01803800300
  | 0, 3 => 0xe3fff8c71ffffe3fff8c71c70ce3c678c703cffe3c678c70040cfc478ff8e3f03e3c67fc7e3cffe07fffc0fffffe07f8fc0fff03
  | 0, 4 => 0xe00607c0e3cf3e00607c003c0003807707e38ff03807007000fc00000700e38f3e3c67fc7e3c0fffc7f8ff0070ce3c678c7e04ff
  | 0, 5 => 0xfc7f88f81c700e3ffffc7fffffe3c67fc7e3cffe3c6780700000e3c6780000000e3c678c70040ce3c007c7e0000e38677c703cfc
  | 0, 6 => 0x1c3980381c30000000700e3803fffff8ff1c70cfc7f8ff8fff03fffff8ff1c70cfc7f88f8fc703fc7ff8f81c70cfc7f88f81ff03
  | 0, 7 => 0xfc7f8ff8fff03fc7f88381c300fc4007ffe0000fc4007f8e0000fc3f87f81ff00e03e07c0ffc03e03e07c01fc001c398738ffb03
  | 0, 8 => 0x1c3980381c300038070070000cfffffffffffffffc007ffe00001fb9f03f1c3fcfc7ffff8ffffffc7ff8381c300fc7f8ffffffff
  | 0, 9 => 0xf0fffff8ff1c70cfffff8381c300ffc000ff00000fc3f80f81c700e3be70c71c40ce03e00c01c4001fb9f03f1c30c
  | 0, 10 => 0x3fff001ffff000007000380000000000000f00000000000000e3c678c70040c003ff8001ffff0000000000000fc7f88f81c7f0
  | 0, 11 => 0x700e0000000007000380000000700038f000000700038001fc1ff3f03b0c
  | 0, 12 => 0x3807707e38ff1c418f38e3bf303c07f07e38ff00000700e38f30000000000000000000000000000000000000000000000000000
  | 0, 13 => 0xfc7f8ff8fff03e3c67fc7e3cffe3c678c70040ce3c007c7e38f303807707e38ffe0460fc0e3cf31fc0073fe38f31c018738e3bf3
  | 0, 14 => 0x3ff8001ffff00000000000000000000000000fc7f8ff8ffff3fc7f88381c300fc4007f8e38f3fc4007f8e00001c398738ffbf3
  | 0, 15 => 0xf0000000000000000000000000001c418838e0303003ff8001ffff000000000000000000000000f0e0460fc0e3c03
  | 1, 0 => 0x1fc1f83f003fc03c07807e00ff03807007000fc03807000000000380000700000038000000000000000000000f00000000000000
  | 1, 1 => 0xffc070ff000fc1fb9f03f1c3fce3c67fc7e3cffe3c077c7e00fce3c67fc7e3cffe3c678c7004fc1fc0703fe00fc1f81f03f003fc
  | 1, 2 => 0x700e000000000700e38f300000700e00000000070003800000007000380000000000000f000000000000000000000000000
  | 1, 3 => 0x7000380003807007000fc038000070000003800007000000000000000000000000000000000000700e38f30000000000000
  | 1, 4 => 0x7000380003807707038fc038007070380000000700e38f30000000000000000000000000000000700e000000000700e0000
  | 1, 5 => 0x380700000000038070000000003807707e00fc03800707e38f30380000700000038000000000003800707e000000000700e38f3
  | 1, 6 => 0x3800001c000003800001c00003f87807fc0ff003800001c00003807707e38ff03807007000fc03807700e38f30380700000000
  | 1, 7 => 0x1ff9803ffc3001fb9f03f1c3fc1ff9f83f1c30c1c798838fc3031c3980381c3001c00003800000003800001c000003800001c000
  | 1, 8 => 0x1c000038000f01c00003800000003800001c0f0fff980ff1c3001fb9f03f1c30cfc7f8ff8fff03fc7987f8fc300fc7f88f81c700
  | 1, 9 => 0x3800001c000003807001f8f000380700ff8f3003800001c00000380700fc00000000700e0000003807001f8001c3980381c3f0
  | 1, 10 => 0x1c398738fc3001c000738e00001c000738e38f31c000038000001c000738e00001c3987381fb001c0007380380000380700ff8f3
  | 1, 11 => 0x3800001c000003800001c00000000000000001c398738ffbf31c3980381c3001c398000000001c39800000000
  | 1, 12 => 0x3b870071c0fc003800001c00003b870071c0fc03b800071c0000380000700000003800001c000003800001c0f0003800001c000
  | 1, 13 => 0x1f80703f000fc1f80003f000001f80003f000001c3980381c3f01c3980381c3001c3980381c3001c000038000001c00003800000
  | 1, 14 => 0x1c000738e000003b87707ff8ff003800001c00000380700fc000003807001f80000000700000001fb9f03f1c3fc1fb9803f1c300
  | 1, 15 => 0x1f80773fe00fc1f80073fe38f31f80003f000001f80073fe00001fb9f73f1fbfc1f80073f038001c398738ffbf31c000738e0000
  | 2, 0 => 0xe03e07c01fc00e03e00001c000e00007c0000001fb9f73fffbff1fb9f73ffc3fc1fb9873fffbf31fb9873ffc3001f80773fe38ff
  | 2, 1 => 0xe03e07c01fcf0e00007c0000f0e00007c000000fc7f8ff8fff03e03e07c0ffc03e3fe7fc7ffcffe3c007c7e0000e07e0fc0ffc03
  | 2, 2 => 0xe03e07c0ffc00e00007c0e38f3e000000000000e00007c0e0000e0000700e0000e03e07c01fc00e00007c000000e00007c000000
  | 2, 3 => 0xe03e07c0ffcf3e03e07c01fc00e03e00001c000e03e0700ff8f3e03e00001c000e03e000000000e03e000000000e03e000000000
  | 2, 4 => 0xe38077c7000fce38007c700000e380000700000e03e07c01fc00e03e07c01fc00e00007c000000e00007c000000e00007c000000
  | 2, 5 => 0xe00007c0e0000e00007c0e0000e03e07c01fc00e3be77c71fcfce3be77c01fc00e3be70071c0fce3be70001c000e3be07c71fc00
  | 2, 6 => 0xe38007c7e38f3e38007c7e0000e3be77c71fcfce38007c700000e38007c700000e03e07c0ffcf3e03e07c0ffc00e00007c0e0000
  | 2, 7 => 0xfc3f87f81ff00fc3e07f81fc00fc3987f81c300fc0007f800000e3be77c7ffcffe3be70001c000e38077c7e38ffe38077c7e00fc
  | 2, 8 => 0xff8077ff000fcff8007ff00000fc3f87f8ffff3fc3e07f8ffc00fc3987f8ffbf3fc3987f8fc300fc0007f8e38f3fc0007f8e0000
  | 2, 9 => 0xffc67fffe040cffc60fffe3c03ffc007ffe0000ffc0003800000ffbff7ff1fffcffbe07ff1fc00ffb9f7ff1c3fcffb987ff1c300
  | 2, 10 => 0xfffff83800300fffff80000000fffe07f81fc00ffc077ffe0000ffc077ffe0000ffc0703f000fcffc007ffe0000ffc00738e38f3
  | 2, 11 => 0xfffff8c01c400fffff8381c300fffff8070000cfffff8381c300fffff8ff1c70cfffff8ff1c70cfffff8f81c700fffff8c70040c
  | 2, 12 => 0xfffff80000000fffff80000000fffff80000000fffff80000000fffff80000000fffff80000000fffff8ff1c70cfffff8ff00000
  | 2, 13 => 0xfffff8001c000fffff8001c000fffff80700000fffff80000000fffff80000000fffff80000000fffff80700000fffff80000000
  | 2, 14 => 0xfffff83f00000fffff8381c300fffff83800000fffff8001c000fffff8381c300fffff83800000fffff8001c000fffff8001c000
  | 2, 15 => 0xfffff83f1c300
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x45ff808cffbf044a8808c710304408808c010300c65801a2cea00c01801a00c2001ff9452ffff001ff8000ffbf0000014520c68
  | 0, 1 => 0x9813013202d404c09809e01d309c13813a02c6091ff8120ffbf091560120860c0901b81200397090120120020404c09809e01c3
  | 0, 2 => 0x20465c0082caa20420c008200200000000000000dc1b81be03d70dc1b81ac03970dc0001be00400d81b01b603d50d01a01a40315
  | 0, 3 => 0x421ff8440ffbf421560440860c4206584402caa420440440040824428c08c210320c21c01a20c2205ffc008ffbf204a8c0087103
  | 0, 4 => 0x62c65d45a2cea6206454402c2862c65d45a2cea4284514520ce820c21d01a28e262464c448240a4b0560560060c42c45845a04ca
  | 0, 5 => 0x902000a01000062dffd45affff62c65d45a2cea62c65d45a20c262c65d4482caa62c65c448248a62c00545a00406286554522ce8
  | 0, 6 => 0x942882a855101244a8e08c7103d22440e410408b0620ca092002992120b210204946088a8d0103903560a01860c902a88a017103
  | 0, 7 => 0xb46a8ea8d7103b46a8ea8d7103b46007edf0040b46006a8d0000b42a86a857101b46a8ea8d7103b02a06a017000b46a8ea8d7103
  | 0, 8 => 0x993120b2182044b1560560860cf6eedfedf7debf6e007edf0040d6acd3ed75de9b47ffea8dffbfb47ffea8df397b46a8fedf7d6b
  | 0, 9 => 0x801101208f0db3560f61860cdb3560b218204db2000f610000db3560f61860cdb3560f61860cd23440e418408db3560f61860c
  | 0, 10 => 0x201fff000ffbf200a07000782004889309659f10408830845931460cc24c45519041ffa084ffbf040882084511190a011a1308f0
  | 0, 11 => 0x24ca9e08c208224ca9d01a20c224ca9c008209224c00709e0040240a870847931208a1701278f0200a070007830290b271207a24
  | 0, 12 => 0x2dcbbf1be7bf724ca9f09e79f324ca9f09e79f324ca9f09e79f324ca9f09e71d324ca9f09e20c224ca9f08c79b324ca9e08c7193
  | 0, 13 => 0xb46a8ea8d711366cedf4de7dfb66cede4cc759b66ca9f4de79f366cedf4de7dfb24ca9f09e79f32dca9f1be79f32dcbbf1be7bf7
  | 0, 14 => 0x91ff8120ffbf09112012082140900001200000b4ea9fa9f79f3b4ea9ea8d7193b4ea9fa9f79f3b4e007a9f0040b4ea9fa9f79f3
  | 0, 15 => 0x4294514528cf84294414528c684214414408c384654c94cc8d2b421ff9440ffbf4214414408c280991311328af429532c128a216
  | 1, 0 => 0x4b95715728efc4bd57957a8efe4b95715728efc4b957012082944b800157200404b800012000004b95715728efc4b15615608e3c
  | 1, 1 => 0xdbb571f738efcdbb571f738efc6bd77d57aaefe6bd57557a8efc62d65d45aacea4b95715728efc4fd5715fe8efc4f95f15f68ffd
  | 1, 2 => 0x2dd1271be82542dca9f1be79f32dc0071be0040291b27120fa34201a07000f8200d99b31b6dbf50d19a21a4d315041882084d111
  | 1, 3 => 0x621e47440fc284f9df35f6dffd4f88835f651514f80035f60040461cc34c4dd39421c43440dc282ddbbf1befbf72ddbbe1acf397
  | 1, 4 => 0x6f1fe75e4ff3d6b9f77572fefc6b8a07572786066dedf4defdfb66dedf4ccfdbb66dede08cf19366d4474de8c6866c0074de0040
  | 1, 5 => 0x6fdffe1ac20826fdffe008f0826fd5775fe8efc6fca9f5fe79f36fca9f5fe71d36fca9e1ac71936fc0075fe00406fdfff5feffff
  | 1, 6 => 0x943882a85d111943802a85d00090f81aa1bd0c2903802a01d0006fdfff5feffff6fdfff5feffff6fdfff1befbf76fdffe1acf397
  | 1, 7 => 0x9df9a2bbfd3559db9b2bb7d3d59d39a2ba5d3159d79aabadd3179d39a2ba5d3159d2002ba500009d39a2ba5d315993922b21d214
  | 1, 8 => 0x9da013bb708f09da003bb7004090b813a13d8f0df39a2fe5d315df3de2fe5d71dbd7baebadf317bd79a6badd3159d39a2ba5d315
  | 1, 9 => 0xbdfbbebadf397b9bb37b33faf4b4fa9fa9ff9f3b4fa9ea8df193b4f807a9fd040b4e007a9f0040b03a07a01f8209db9b3bb7dbf5
  | 1, 10 => 0xbdf9a7bbfd355bdfbbfbbff3d7bdea9fbbf79f3bdea9ebad7193bde007bbf0040bd3ba7ba5fb35bd2a07ba57820bdfbbfbbffbf7
  | 1, 11 => 0xd6b443ed78c68d63cc3ec5dd39d23c43e41dc28d23443e418c28bdfbbfbbffbf7bdfbbfbbff3d7bdfbbd13a20c2bdfbbd008a8a2
  | 1, 12 => 0xdfbdf3ff7dffddf3de3fe5df3ddbbd73f73defcdbb803f73d040dba003f730040db3d63f61de3cd6bcd3ed7ddf9d6bc43ed7dc68
  | 1, 13 => 0xdfb573ff78efcdfb123ff78254dfa003ff70040dfbdf3ff7dffddfbde3ff7df7ddf3de3fe5df3ddf3443fe58c28df2003fe50000
  | 1, 14 => 0xffe007fff0040ffffffffffffff6fedfecdfdbbf6fc47edfdc68f23e47e41fc28f23447e418c28dfbdf3ff7dffddfb9a3ff7d355
  | 1, 15 => 0xfff577fff8efcffea9ffff79f3ffea9ffff71d3ffe007fff0040ffbff7ff7fffdffaa07ff77860ffffffffffffffff447fff8c68
  | 2, 0 => 0xf23e47e41fc28f23e46a01f000f22007e410000ffffffffffffffffdf7fffdffdfffbbfffffbf7fff9a7fffd355fffffffffffff
  | 2, 1 => 0xf2be57e53fcf8f2a017e5308f0f2a007e530040f67ecfecdfd2bf67ecfecdfd2bf2fe5fe5bfceaf2e007e5b0040f27e4fe49fc2a
  | 2, 2 => 0xf6fe47edffc68f6ea9fedf79f3f6ea9ea8d7193f6e007edf0040f6e007a9f0040f63ec7ec5fd39f62887ec55111f62007ec50000
  | 2, 3 => 0xf6fedfedffdfbf6fedfecdfdbbf6fedfecdfdbbf6fedfa9ff9f3f6fedea8df193f6fedea8d2082f6fedd45a20c2f6fedc008a092
  | 2, 4 => 0xfbb577f738efcfba007f730040fba007f730040fb3f67f61fe3cfb3e47f61fc28fb3567f618e3cfb3127f618214fb2007f610000
  | 2, 5 => 0xfff127fff8254ffe007fff0040ff3fe7fe5ff3dfbbf77f73fefcfbbf77f61febcfbbf77f73fefcfbbf76b21f294fbbe47f73fc68
  | 2, 6 => 0xffea9ffff79f3ffe007fff0040ffbff7ff7fffdffa887ff75151ffa007ff70040ffffffffffffffffe47ffffc68fff567fff8e7c
  | 2, 7 => 0xff3fe7fe5ff3dff3e47fe5fc28ff39a7fe5d315ff2007fe50000ffffffffffffffffffebadf397ffffffffffffffff577fff8efc
  | 2, 8 => 0xffb577ff78efcffa007ff70040ffffffffffffffffe47ffffc68fffbbfffffbf7fff9a7fffd355ffea9ffff79f3ffe007fff0040
  | 2, 9 => 0xffe447fff0448ffe20ffff2042ffe007fff0040ffe006bad0000ffbff7ff7fffdffbe47ff7fc68ffbdf7ff7dffdffb9a7ff7d355
  | 2, 10 => 0xfffffc1ac2397fffffc0082082fffe47fedfc28ffffffffff3d7fff577fff82d4fff577fff8efcfff127fff8254ffea9fbbf79f3
  | 2, 11 => 0xfffffce49a48afffffcb29a286fffffc568a68efffffea8d7183fffffce49248afffffcb292286fffffca092082fffffc448248a
  | 2, 12 => 0xfffffd45aaceafffffd448acbafffffd448acaafffffc128a296ffffff08c79b3fffffe08c7193fffffcf69a68efffffcf692082
  | 2, 13 => 0xfffffea8df082fffffea09f082ffffff5fe20c2ffffff448fcaafffffe1acf397fffffe08cf193fffffd57a20c2fffffd568aebe
  | 2, 14 => 0xfffffffff20c2fffffffedffbffffffffed2082ffffffe49fcaafffffebadf397fffffebad2082fffffeb29f296fffffea8df193
  | 2, 15 => 0xffffffffff3d7
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 52 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 52 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 377 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 377 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 377 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 377 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 11 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 3 => 9
  | 4 => 145
  | 5 => 1095
  | 6 => 2487
  | 7 => 863
  | 8 => 19
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xe10e516ed8778d9e949cdd448d6cb6f78650330d80fd7d135c9740bb2ce1bba029552b82
  | 4, 0 => 0x731267d872a675c46ecf21716eac448e690dc4fe68247050672cf27966091ce464ef9797644cb9cf64422b15631bcbf16281cfcd6060e4cb5fdb48285b1ceb625aeb549257bb4d5e56f4522154d3384551ef7e254d9f0b264a1d14af48e642b94779103e46ec6c0646579685465650fc45ff80d844791ed043cc9c9542d9d45441d972113fa91fda3e9c82ae391a8b4434ec5fe231dafabb31b2ef1b2dc65d9b2d0e816529a15a1f2719e33d260c49c621bcff321cf2e6b2198f0bd51493105c13df267a12fa4f7c12ba411c1098ac7d0f0572400d36d4990ccc5d2b0c1fcc080b8e87900a0398d90973360a09699aa908c6a7eb0898c5b9085b9b6304a722d4
  | 4, 1 => 0xdd3bf9b0dbd1c9b1da70df53d97aa94cd5d547dad477d8f9d37ef8ded1f63c10cf29ec47cd9492f3c89d780dc6112d30c3f493adc2e1ec4cc16720c4bfa53a28bc10d9afb90f1da2b81930aab5a4db08af5318f4ad3d50b5ac41fe6babc3344faa8da259aa530849a98e95e0a8e03474a8a214c3a80c30bea51f0c1ba4c253dea3fcd073a3bce62aa244d455a1283bd0a127f4a4a0f69aa9a04ac9b29bedc6ea9a2142d299c1d810999b2c5798985da59749e9bd96e9898a950acc9a92898d689259cdef914599c88f3161bf8f1fdc868add92a689a8825787ec670185d2e6fc845f78807f4a6ff37ddbdc757c79d4cd767123ad757d00bd73d9ffb3731d1efa
  | 4, 2 => 0xfb802304f736a8e6f559d055f40d0487f39e206df1a1a5f1ef029114ee8000a3edfeccf7edf838d8eca927b0ea97adf8e73e5085e4dd8b41e18ca2b5df94b892dd5a867f
  | 5, 0 => 0xe2792cd0e15721d0db09f980dab4c210d351cfe0d0aff3d0d0073760cc79e370ca8f48b0c645dec0c2777f60c1a655c0bf8a62e0be619df0bd5dce90b91ff750b13235e0ad939ea0ad59e710a7e198b0a6c0c690a02e36209d0c57e09c5e5d209adf9d1099ad82c09907306098b9ffe09874f3d09438fc208c9b55708b04fcd0898c5b9088521e20871fbfe07fc470107d973cd07c3c88906ff5f22065eb5700634897b06275f7305e4ea0805e01d3205d4ab0b0536897804cee2e2047366b104450d510414a35503db0b4b03d3407003c941e203598f5d0354b9ff032f719c02fff0f60269762b025fa4b801201d2d00e3021600a7cf8b005448090046618f
  | 5, 1 => 0x1abf35371ab883531a1f0ef619c24abf19bb05571968c7ac19169d3318f26c4c18ae189c1896d391188f92a41856b928181d7b9217d6fff417c6219b17603fa517597bc2173324b9170d8c6c16cd5ae216b3ff1616716f5b15f9fdd015ba433715a9ceb4158062d0153eaa181526b4fe1507bb7014e8d5f814e03b2014c6ceeb14ab6a6213b8cc2813b1e74c1379562113396fbd1320dc5a12fc8c931299497c1293710d127c1943124688131234695d1223d250120466ad11791d7911471f0d1127c8ab10dbf53010cc6bad107205040fce77530fb8ab870faa77070f8d5ea70f7bd8a40f33272f0f15cefb0f1377e50eb6e6710ea8faac0e98fa660e3c71e3
  | 5, 2 => 0x2e0522a52dc127c62d028d5d2c08bf9a2bed7f9b2b95ff442b2de9d32af712932af65d012a98ca942a8e8ce62a36732f2a3198e02a25967329fd2b78296d9ffc29596b1529240e0e28b65c9628b0dc0f2884fdf82810052827987c29273a86802705880d26fa494525d20d0b25a31684251bbf86250b3e6a24bd3060248ba27c23e92d1223c3c9dd2379f29f228bcf2c227394b521b0632821970f56218ce75e217c18ce212e32d3205d8479202016cd1fd5918a1fb620fe1f771dcf1f5bf0711f56d8a61ef254801ee233921e7ac8861e4008941dcf29111db4fc781d4df85b1d1d36831cf2e6b21cc7c4c71c2546331c0516cb1bf750b41bf6a8921bda505f
  | 5, 3 => 0x3b2597ba3adc15ed3a9dd5413a982f283a41ae9239ce437c39c5c12539957fd339822658397e0b063920589d390f71bb38e1164638b37f93389a23f9388623e637ef7fdc37c2cb5c37c18a1637c03f5d377ab9dd3761c3f337463f943710815436806a4b367d4a353655ffd33620c340360ac24835f2677c35edce0a35e7ff7635cdb6d5355135a835374c5035194c0335176eb93505b6fb34c436cf349e3e31347939b83366c242330f147832e38d4f32710398323d52f4322d2f653210d20531e3890231c32dd1318e6c923168dd79315db1f13107ca4930b3c7d030ab0740308a916b30599af9303166692fd3c53d2f98de682ee7a1cf2edcd3252e1838a5
  | 5, 4 => 0x496ee829495b4db1494d102248ed7499486fe2214869ed974829145047fdf1bb47aa0641479580c9477e821d471c98aa471c279b468678ec467570564647284445a5d096459b1a41456691754545237444b6f224449d9d2c447962e24432cc7e441f2e6d439bf0c4436c1640435fa88143330dc842c6e51c42b779a3429c57fe429a974e42943811425d8ab84212d09a41c1c8b240db670440cac16a409bb26640722d16402a13e13fa91fda3f4a71253efd8ad53ed86d6d3ec44bf33e9c32c83e7840563e6329a03e30959e3e00b3d23dceb69d3d6d512b3d149ab03d0b66a33cf875583cec53693ceaa2193ce925d23cd46a253ca9563c3c9d75a23c0aed04
  | 5, 5 => 0x593af06c584a41b7581ef1aa57c4e3cd570643fa56f2c9c356c78d95568406dc565fae23562433d6559269bb556f06955542946554fdd21e5416395f53fc57df538bceb4534694835318541d52a44006529b0565526a8b2b521d127351ef29925198e0a65196fbf8518a3b31517631a05136721b50965316508c20d6507425ff501d2ed74ff7fc604fe3e7264fb119a54fa0e5564f93257d4f69b3604f5a105b4f0d9c4b4efbba7b4e9c1ef24e0e4fda4e0610dd4d1f41294d1acf0f4d035fd24c8f74574c56afea4c32c98e4c187e4f4bbf7dfd4b9389664b24895f4b040f154ae0bcd24aa8075b4aa59fc74a8b03b14a899ff94a76e1cb4a6882f34984414b
  | 5, 6 => 0x689e67456879c49e685d58d167ffb5c167da434d675c9d8f6745babf66f1c46b66eed05465cfe10f657fa726657d47b965735823650bfc256473437b646c71d463748ccc63669d9563374e1062b2b0a762b1e2c46284634462668785624ed7ea622b535d61f5a73b61ec630f619a2c2d618a6a106109420b61080b9e60ce576460c63c435fa9c4225f535c335f07899d5efdef5e5ef1218b5ee1c5a75ebbe63f5e8dc5755ded18815de3fb985d9849c45d6525cd5d5f28555d45eb4a5cbf688d5c47a4b45be0d81b5bdcf6cb5bb4a4775babd7175b796d475b5a05c25b16d8295aa8a6b95a709cc15a40a3f65a3142dc59f502be59a0445d5967c8f75948bfa6
  | 5, 7 => 0x76b9c58c768fbe7b76485825761e2a8775dc40b375a1e3db75988e0e75976e54758cb7557557dd5e754a7af0753588617506b6eb74e00fc47492b4e0747a5f9f744822c67388972f7344f669733927ec732d37cc732cd8d972e18a9b72a88229727b1359727661f972462f94717e14fb710b8ed970cb6e547049eaf46f9cfc706f7855d36f30a2ab6ef98cb76ee120c26e6d26566e5661bc6e30fa396e194f236e0043fe6dff63696deeb1446db1896c6d6a8de86ce805ba6cb081016c95d74d6c95d0d56c6cca846bfda1866bf0df266bd1a3056b4b51b96b21999c6a666ff96a25047e6a1d12c669c197106972b762695d162a694efbfc68f79ab368ec5e7f
  | 5, 8 => 0x859062948565afd284ca8d4b847b982684750a79845407c984521e5c842c50d48427787b83d893b883cc75a883a789fc8380f135822fe2c5822bfa848211e0e081e05eb981d862608175276a8158933e8153ce488105c76780cdcee280ab136780a76a0a808f945b805f6c4f8052da2a8049a0dd7fc0020e7f3f15757f19782e7ef79a577ee90ee47ec375137ea2f5447e373f027d8ecad87d14b58d7cecfc4a7cdf2fa47cc9195e7c7054c17c2120b27be1fa6d7bcc18817bb0128c7b971a887b8db51e7b2b17a17aca0b7b7a7f46e27a7a23a87a2f062379bc0fa178f16fad78c56cdc781762e9780e5ba377be10877793da377746be7b76fe097576c54e7e
  | 5, 9 => 0x928f3a4d928a5f9d92743a0b9268a0bc91fad25291c5b8699190d39c91495fea91286ffd911cd0ad90c01054902779c58fbf93e48fa843f58f9504aa8f6cb6f78efdd69e8ec05c368eb51c718e275eee8de2a4938d7e0df58d6a0cb08d22a5d48d22906d8ce1dd188cb445068c76bee98c1fbd1f8bb8582e8b88fb878b7ac87f8b2e8f198ad6733c8aa56f408a8f77978a6d7dde8a62980e89f5165189d86b2e89bba1c189b7ce058983dc348934bc8a8923577389153c8f88df30a8889c272b88872c14882be4e187c1a4c787b0e4ec87839059874f9d0b8725883886f41d8b86e482b386ddfa1f86d946b086babd4586ac5a5b868ebbe6868ab93d862ff0fc
  | 5, 10 => 0xa190b783a174a2c0a11323b6a0b7fc57a070ad90a061114aa03a41aea01d11f79ff7717c9fd4ea269fc1e7f19f4489879f2e4bdb9ea0779e9e7c1f059e6b99699e3db1909e11eefe9df0e5b79de8ff369d73e7da9d6e98e59d5e0e199d036fc99ca055eb9c97795a9c8ff8209c7e5f079be530079bba71139bacb5569b4404729b29479a9a91dcc29a87cff89a255f3b9a22a3a499cf7f7d99997b07993bc0d598c0bf6f98a19efa989a6927984fc9d59807941097ceacc397b5cdf7977ed1a09736b29e96d86ce296d69f5a96c9f409968281c3961be3db96114c9595594957953df84d952c5ba294fdd57994f8f31893c3f4f193bf213c93a2fb68928f624e
  | 5, 11 => 0xb149ef60b065425bb02d486dafb2587faf8c880aaf7b177eaf7112d2af327887aed0b3cbaebd675cad99b7a7ad68591aad25e2dbad148ffdac8e73deac3646a5ac067d02abe9eccbabd19988abc86761aba3a126aa879d64aa2d3a96a9ffe287a9e3e07ca9789f6da9445b08a93a9cc5a93a8d00a90bdb18a90844aca8f67609a8db08d3a8d5d3f3a8d30b90a8be667ba890ecd1a87b6d4aa81cf63ba8112672a7ce168da67b5273a672de31a61f8d2ea5d5d46ea55e26eaa550f087a4ef0d12a496bc57a46c63afa45a6710a43f6bafa3d30303a3975e0da38ccc30a3441e1ba3105a4fa2fe4972a25e4bf1a2327799a21c11fea20cca36a1dadcb3a1a6a058
  | 5, 12 => 0xc16f05abc1656a4ac13f5760c11c5d25c0dfe6dfc095d15ac0440dc4c03fc09ebf43eec6bf307c4ebee90ccabee2037ebea336b7be9eb679bdfddfc4bd578f7dbd525c98bd199d0fbd14a6b0bcf469d8bce032e7bcd62099bcc676ebbcb5de76bca7146dbc91311cbc11cc8dbbb4621bbb701e32bb624560bb5bf358bb352651bb203f95bad4832dba88bda4ba7256beba47eeb6b9eae4c7b916784db7e0e0f4b7b3e8e4b7aa0c84b789dca9b7199e54b6bc1d12b65c9658b65be785b64970dab6445922b5d22f43b55760a1b5406affb5266748b47e9f86b46eb9a3b42e327eb411607db3a5b92fb3542d0eb2db658ab25dac8bb24f00d3b23ad043b1f6ec50
  | 5, 13 => 0xd01189aecfeebea1cfe56affcfe1293acf6867bbcf1f2821cf041131cedcfbd9ce59c5dbce03cf96cde4c89dcddd1867cd73df73cd0f1f41cd045b36ccc23c69cc240e2fcbf71b79cbc5e2c2cbc4e291cb8f0de8cb702a88ca715efbca5d1f3fca1f9b65ca1ab20ac9f2a206c9c1e28dc929c0b4c90c09efc8ff47f7c8bcd3fdc8865fe4c87b316bc858f251c825034fc809920cc7fa8cb7c7e1e1ebc79b0139c6f20f0bc6dbe2c2c61131fdc5c42df8c57bfcc3c5074187c4f7a12bc4ec1310c4ea5ce7c4e47f86c4122956c3db19e1c3c13429c3aabe58c2ec8822c2e02198c24a1187c23fdb75c1e2415cc1c9b8cec1c7272ec1bb9ca7c190f9ffc18a15ce
  | 5, 14 => 0xdfd537a6df470ea1df415612df3d5635de66565dde2abc10de160a38ddf2197bddebd9d1ddd96ad2ddd3ac13ddc8c101ddbf2f3fdd90f2dedd8427f0dc78da3cdc374be2dbc7ecb9dbc3afcbdb94c6aadb7460efdb6c3599db37e196db34876cdacc0db0daa715a0daa1192eda6f60a5da569807da39dde4d906d666d8a2e1fed8785eeed86eade6d835ee75d8265658d8102e57d7c16063d76eed8dd736bdccd714b64ad6af2d85d62d38b9d5d9b825d5c4fcd5d531990cd50aca25d4de3103d47823c6d3d638ded2f73113d2eeb790d28e4411d23fd7cdd1ec5f18d1a099bcd171cfb5d16b37a1d154e98cd117c8aed10e0725d0cde02ed07e2ef0d0705c58
  | 5, 15 => 0xee362384ee085c8fede74c73edc426f0ed9421cced86fa4eed786edbed22804fecdaea36ecc9f930ecc12505ec2eb1cbebfe0707ebd80ac2ebd49c57ebbe285ceb949f2aeb861aafeb287186eb21bc63eac3b1b3ea70c2cfea3a763dea07492de907f834e8dba40fe882f5e0e848ec8be82e69d7e7c6cd59e7b699c8e768cc30e753efaee73e5085e7170491e714a497e6dfa69ee69a76f7e5eacb78e5ea9bc8e5bc5864e5901b05e5243755e4bf56f6e417b86ce3d6ebd6e3b6baa3e3a88b38e39a1325e38650b8e3539c22e2fe02e2e2d80636e260e440e2540ce9e229e20fe1ec3d6be1e3cf1ce1af9cd7e12b0384e0a84603e09ee903e06fab46dfe672cd
  | 5, 16 => 0xfe44fcfffd75c11dfd55db2ffd3f8b5cfcdd0c3efc2e27a5fbe653bdfbde5656fb9c2d62fb9a2272fb926471fb49d201fae73b35fac3bf92fa850269fa3bdae3f9ff0f81f9e10570f9cc3189f9b7bb63f9acd0faf99b4bbff96feb04f8f72873f8e460dcf8cf82a7f830b686f81e117ff79316e9f748961bf717d064f7055979f6dfb90bf6972dbbf6815977f678d20af5e77c9bf580c509f5702ccbf5192827f49c2b22f4737ad3f3ea4061f3aedd49f3a4d4e8f382d58df37843e1f21b4b77f187f8e4f1275cb5f0f8df95f0f03238f0440ce1f02859f0f01c36a6f0040747effb1e42efd4a863efcd789aefc2e112efa77ca6ef601aa3ef09fd94ee96d50a
  | 5, 17 => 0xff95acedff7c7227ff6826bdff067dc5fead2cf8fea1950dfe819b18
  | 6, 0 => 0x5d4ab0b05a47d0105687e89055afcf40555b2b90551a37505505c7b053cd7d1051f1fac051a6ec905169eb004f7559904dbb86404c9880c04bca65904ac2cb3047e05410479bbe1042d77d50425399004127e5b03fe743403f7cba003c75b2a03a442530384d118037f68990376fe1b035b2fd10341d11b033b05b5033a727c0322eb18030dcc68030a7d9703087e0402eac56702d6a72e02c7a62002c1685702a27623029bda2f02975eb90293b45202898f5e02664004024ad8f90249a99b0248132d02465a5101e3cad001ca161a019c9fad018309d901752afa015842e8013e3f93011f27fd01147e9b010ac53100a7cf8b00a28bea006c268400296567
  | 6, 1 => 0xcfc43180cd896110cd4b54f0cba81470c6f23470c3486130c0ba5d40bd0ae970b9beb890b8ad6cc0b7002330b2e0ec30b2c8ce60b28f6400b23fcd60b1a7d630b05d34b0afb5dd30aefe7a00ae892150ac4d5b90ab8b2690a7677f50a53c4d60a4bf36d0a3ff76609f8447009c0e32809bdf0a0098c38fd097c0ec409785bd1093e7356093a1b9a092d20e8090dfc8408fadadf08d6f02608b0816608a3620f0848694b083fa81e0815b7f907d1c87f078f1e53078c6002077a422d076636a7074eba94073a22a1072f1b210715437d0715311406fe4f3806f6a3d806e4ef6406dc984206b031a206a136850665520c0644c923063d522405f2ecc205f2790c
  | 6, 2 => 0x123c1c3b1233466a120466ad11f373c011eac26e11be491311b4bd5b11a18517118eca211187183a11804b36116b47241161181a115b67ca1142fa41113ec3a41137d80a1120d646111de81010e1c50f10d89c4810bf6ca610aeb074108ef5b91058a219104ef36110424357102d4a7a101f34a210105d9b0ffdfe370ff651070ff073950fda9e160fa2a5570f79f41c0f78ea770f47a0390f3d84400f21afa70f1c66040f0572400eee99640eee197d0eec435f0ee5d4340ed5a7770ea887730ea800b80e96d1cc0e7e15130e737a980e67dc250e4ffb2c0e25ce180dede7600de1cc4b0ddd4aa00dcab45d0dc9b4060d9dd24c0d9cbe430d9a92370d4430e8
  | 6, 3 => 0x16741ef11673385e1665ef1c16654882165c2d5c164f38e0162baad5161b95e216118174160f154516066cd91606144c15da08fc15badb7e158c470e1587591d158062d01574b12d15680e6c1561a43a15608d7b1560201415423b41153eaa18153802db1517feab14c37a0914b6e97514b29a231499cfe514696ac214649f8f1437977c1436a4701422b86f140b2e6e13ea83c213e1444713e0e2a7139b02df13971d6413967e2f139302bf138cad001374ec0113728f5613604859133c08ef13347fe713346ed1132f4ac7132af56d130a5a891305f52212f2217912ee238212ec372612d1fe4012cd450012baa67712a888d212838bee126e710112423e08
  | 6, 4 => 0x1d75a3ee1d73f5661d4c60a11d35f1f81d3110c21d2d215e1d07cbc61cf670511cbd20421caf33921ca0b1831c6af0321c53915b1bb1776b1baefe391ba64fad1b8548e61b78d4bc1b62a5db1b61a0cd1b55df541b3c1cc21b27d2611ac6e6c71ac6cf551aad97251a7fa1b81a4058c319ff9c8019e5257c19c2b1f019224d721921f28d1921237f18ef4baf18eed24c18ac994f188affa91882b16918787ffd186c3881186bcef3185955ec18560fc718545dd6181a048118103f88180c2da517f938b617cb86b117c5bde017b8d5e517adb3cc176346e0175a929b173aec2717353650172938d717206e3517135e9f1712096e16dbf17016a5446f168a4efe
  | 6, 5 => 0x24425a84243971d52416c07e240707cf23fa873323b6748b23abbd1f23aa74da2360951f2359c6d02353b18e233e519822e093b222d25b5c22c73513229eb02f228b5910227a82792241f9d7221388372202198b21dae13221d8db4721ce372521c7964a218ce6fb21730a3e213bddeb213ba1a4213819c921357f5020e249a720b8602f20a84c142065dc9f2064873a2052d8262015ae6f2014c6441ff6fee71fd652f71fba95f01fb72b911fa432931f8f063d1f8738591f7f06c31f3387171f3108e21f0c9a181f09477c1f05df5c1efda3231ee50e861ecbe4b41ea60e4c1ea327491e808ee71e7be0ab1e4f42c11e2780c41ddd2b031dc7548a1d826c88
  | 6, 6 => 0x2b5b865a2b25f1c52b13d0122afe09d52af8e8dd2a97a7b92a68501c2a47f4e42a430f592a3198e02a14d0f72a1317a02a121f8d2a00355d29f0b1cd29e11e8129c7962029c478db29af2b64298f7056298b593d297c99f829740e86296669a2292c9652291d2a9e291385ac2912a74929025cbe28e38c4e28d6af5928d3f68428c73e9828b96dc828668e6d28483606281a4d9f2819312c27fdb4b527d2a87727b3f541275958f2272ec81d2713cf0026bb2fef26b886cd26a8a4502686b911267b41f526786863265363bb26339d4625fc139f25eb7b52258822082568133f2565ea95256186d2255c4db2250aba5724f27cee24cc78e024abde13245fcad9
  | 6, 7 => 0x31f5eab331f21e3331e895d431b1ab2931968b41318e6c923185f30f31752de731302720312ae6df3116a68e3112a29330d9fb7930d5282030b1e59a30ad71ad30a9d7c9309e97613093efd23078e78b3078c081306f6ccb3067a3353012b9612fec250b2fbf35272fae5bcd2f81a0e12f7a8db12f2c65032f0a93ca2efbd9642ede098d2ed6bfec2ec68d272ebd3d6c2eba05a82ea523322ea1c1f32e8fba352e45ee3b2e3061ae2df229832dec4b6b2de6367c2db09fc22d9165262d7d41f82d618f3b2d3ea4312d3a56d62d1894d92d06d0c22cf8cd042cef63982ce3b7132cadd3bf2c5dadfc2c50f8382c45359f2c3e81882c119b4b2bfd49b32b69948c
  | 6, 8 => 0x37fdfb7837e06fd637d8b58137c3b2cc37a858a7376b796b37596ec33729e7e336cb597836c0973836a8e1d9369e286b366fa272366487033652dfea362821393619ea8d3610c82c3609387935fe022a35f2a55735e921d135cdf94b35bfbca935abf1c9357ada31354e1e60353aa3c6353a8a3035239d6d350d0fa434f3ec2d34f1480534ecd7be34d2fbb734a771a734962a6d34960dad3492c5e83492603134886bc33481cae43481847a347c735e3451707d344f47aa344b0a55342f69f634064f6c33f5890233d93c6b33a8219a339be83033864f1f336a01d2335d8195335802fd32d484fe32aa3348326bf53f325f2c64324a6b873211e7f131fd931f
  | 6, 9 => 0x3f227ddf3f0ad8ad3f09c54c3f086e6d3ee052543e9b9b153e9a6a8f3e6c73253e0fc03d3e0ad2fb3decda2b3de11f973dde4a203d8f565c3d820b7b3d68cdf13d5ea5413d4d9ea03d4903cd3d2c7c353d12016d3d107f313ce925d23ce8d0283cd948b53cb227733c5112f13c27f8ae3bf021da3bed01ee3be497a23bdc2ed73bb70e843ba7c5f03ba09a7a3b9e4ff53b33d6c03b1015bb3b0db0ad3aab48ca3a8122023a67daad3a5b11913a4fc2063a4df0a53a2d6c6239ffcc7c39ff1f0a39ddf64839d765b439b8a2b73971fac739514ff1394f1420394374ee3929da4e390153ab38eec90038c86292389a23f938658553385204ef38385a61380d7bfe
  | 6, 10 => 0x46b55adf469949b54640bf184639627f462f96b74615666345b797dc459774c245913ff4457ae3f0456daacd4526b408451ed6694502434f44f4548e44ecccfe44e5077444ae84d944ab1cba44978530447ac66c445a478f43f5039043db6ae443c469ce43738d7443555fb043415cc5433f660a4335a68142b779a342ae7c514288da784270b5be426720864210028741d22c9a41cd461741b4d9a641b3665641af2a2541a587774197b05c417adc044170ec6e4170bcbe416eec4f416e9813413206594115ab1e410d769640f0f80a40c11d8e40a8378340936de14071490e4049cb824019119d3fd2f7ef3fc23f033f7898033f732d3d3f384bf13f362482
  | 6, 11 => 0x4d9bad584d84259f4d7c0ddb4d6c43d14d67b2e34d4b82a54d244e3f4ca1aa074c8f74574c7463374c6700e74c51dc5f4c4c79c44c46545e4c1e35cd4beb8c424ba1260e4b93e1974b83f37a4b2e44754b2472944b21fba14b11aa524b0d87ba4b093b3e4b03fc924ac953704ac64d7b4ab8c3e84ab62a164a9f53ac4a932f4e4a8b09ee4a3f5f3c4a39d0ac4a1d562e4a1935bc4a0a03904a01731049fdd8ca49eb066449e3bfbd49d9a14a499696e9498effba495caf394954e85b4905a44648d58fd648d1b1bc48c35a8b48ae22b548a811f8488ad56b48739a0347f0cb2247e9072d47d8b1d947d7f35a4754508e4739116c46ed067a46df279b46dd66d8
  | 6, 12 => 0x538ec4195361a43253514749534afad3534934bd52b1ef9552a599fd52a439b5529028f052839f995281620b527b6c17525316e95250eadd524f45c5522a0878520442b951e91276518d110e518820f75170cf8d5160844351501bab5137e929512495015122fc19510a33e250eadeb950df0cf150a9730450a1bacb506e67a450695857505beeb35059633d500139404fffcd0a4ff9d5294fc559f74fbec2eb4faafd564f9d2f8d4f9d1e774f9834ad4f8c57c24f8c4e0e4f8b86e64f7141a24f54e6cc4efcd55e4eec3b944edc4fc74ead7c894e92e7bf4e8c86004e7855394e6d16534e65ab694e23904c4e1717654dc9c7c04dc8be514dc7b19a4db24816
  | 6, 13 => 0x58cb5ee5588df5d95886e5b858817b3f58761ced583d5a59582969ea5823a7c8582291a2581a3e365808a35357c03d2857b93b9557ad78bd57ab48c1578add84576c925c576751eb5764b649574995685742a7955713d78556e6f7eb56ac9efd56aaafbf5699e747568e1c39567c7f51566b01f8563d70e0563603f25618ad155612b12055f952e755f6748055eb37fb55d72eec55c413ab55bf057b55914c4d5571ce4a5551c8e5554bcaab55461c9a5530a86c54fb57fa54f251df54f0504c54e3e57954e2c70654d4e82754d391cb54d24b7a54ba411f54b25c705465171a545dc05f5459014c541334f253fe4a8053f3dce653ee2a9c53ec72ba53cbf686
  | 6, 14 => 0x5f4ce3e85f35ba935f20e9805ef6b1695ee4680f5ed6a3f15ed5c2bf5ec41cb35ec2fe405ea728f45e82f8175e75f8765e5e95475e1ca47d5e13ada65dff623c5da6006b5d8057bb5d6a2d1e5d68b9495d4b941a5d3f7bd25d19fb115d00c56d5cde0cce5cb55e505c9649305c8d589a5c5fae8d5c5ccb105c1f443a5c1e7f7b5bf13ab45bdee7215bd6c6db5bb03c075ba915895ba3354b5ba1deb45b4dbe2c5b3cadce5b023f875afb09185af154955aecd9575aea31985ace577e5ac7832c5abcb8a95abc6cf25a315df15a197e005a17fce059f684b259efad2e59aeef8f59a0445d5989a08a597e76b459483db559393962592ae156591e47e658e6c546
  | 6, 15 => 0x6560b6cd6557fc2665438d0165381a02651adfe064d90bd964bd70fe64b23f0e64b2251164aa6b44648a2c2b647758b16472b701642e54a0640fa63f640e6da16407d9c463fb6a7f63e7618863b3fbc963a6a9d36394e9c96310f02f6309bc0f62da87e162d4bd2362bf39f9629d973362623a356243e4b462261eff61fc0a4c61f63a0061f427ee61e27f4b61ca400861ab00a961874d90616fe8b461570a296154a5f5613f4bb66119d7e161176eed60f47f6c60f0517b60d8b88860d62fb160d089a360a7ce4460a08da7607f3e8c607744386043727f6042b364602f2d62600139515fdd5a815fc559925fbac6fd5fb758ac5fa001255f991b495f871fd2
  | 6, 16 => 0x6cb3a7766cae11a46c95954b6c4b6e046be903d06bdbd1346bc8f9716ba23abc6b9d976b6b50e1d96b379a1e6b0ca3d16ad62f646aca076f6ab1a0db6aab580b6a729fe46a2177b56a08291469cd7e5369c0add469ac5725699f003a696bc1f769575adf68c1438968ade545689f85b86896eaea6885fcc0685a49466854735f684a9053682c83d86827ae85681a57ac67ffd2a667fbcd3367e0419367dacb4167c4360067b115c867a2a106679637916786b84767852479677d84d86776f078677213ae67619883670872aa6706143966b0a48a669a488666938280667c47636624d4f6661f8dfe661dc2cd65f140fe65f010c765e88a3d658155c9657d47b9
  | 6, 17 => 0x73170721730cc97a72aa6db7728726c9727718da726a4e017255576072552ff1722120737218e0f571f3b43571d8f93471ca317b71c7957571c4843571b1d6817180f687717e11df7179360f716e5da9715bc440710cca227108872f70fe4ee070e1e95e70da344670d5611b70bb677e709738ae705b5d9f703b7bb4701419897001f6a36fbb45706f90c8936f8476496f7855d36f5030256f4ebd9a6f4c3cf56f43e1be6f271ce46ee46b536e8379536e7ad1816e7107f36e2ae7006e24e7616e027d566df7e42c6dd08b0e6d9d833c6d8815996d7e78d66d7b510a6d4a622d6d483b2f6d26125d6d1c77766d18b8176d06d7a76d01b3cf6cf9e7a76cdc8ae7
  | 6, 18 => 0x7a2bf43679c0734279bb6d1e797abaaa79717a8d79684f627951d578794fbed27937dd20791c1254790b452278e6cebf78dd6d3878d1319678bb1eaa788f951178849c947879923b785240d67850917f784337a87819d38577d135d077c7b61177a8449777a217b1779ca86b7731b80f7730263a7728326676fe097576fdbb7a76fcecf676f6d5a476f0de3376c2010e76b9c58c76a139dd768e81ea766e04be764e5f61764692e6764050df7613d46a76109d4975ee73ad75ea2a0475d32c7d75c8f03e75ace69a75a4c7eb757345647508aada7502d39f74b7658874789e647460b49d74601fa77433e09b73e9209c73da4b1a739a0e5473493a27733927ec
  | 6, 19 => 0x81a4afbe81a4282781a22e7c816ee385815a18058154339f81025bc480cdcee280c8d8e7808528c4806266ad805e0fe97fca014e7fa0bcc37f685e077f4590c97f2365ca7f1e33537f0fc1c87eeb32617ed7db307ed513f37ed1cb467ec231f37ec002077ea020fc7e912cbc7e6cc6297e4b58517e25afd37e22428f7e1a8a567e05acff7dfb85ac7df7c5a07df4a2987dd747b97dc594b27db173387d9294ba7d8e4bce7d4bf7b77d41b0af7d304f3a7cea112d7cb560537c69c65e7c6664907c458a8e7c2f60d67bc64b9a7bb5c0517ba3c0797b91074f7b8db51e7b6ec17b7b6793fc7b4614867acbd9467a9933267a8392537a7a23a87a7688337a38d5c2
  | 6, 20 => 0x882be4e1881c0d428803a86a87fff5c087f2d3ba87e93a0d87e7ffe087e4b66087cc495887b2ceb487b12daa879add67876dd249874d6699873cbec9873313b28709807d8703169686fe088a86fc6e9386c20be1868f8bfa868952b7867726a18676ba268660afd3865cbae885c55edf85912956857f1b66854dfbe28527bd3a84fbb42084f5077184efe6a784dec8e884ab4127849745b1846b9cfe845f90f7845a67dc841fb464840994f684064fcd83f0101583d7542a83c4aef483bec71383b00fae8362909783621177833df903831ab88982e0b6ab82de711782b11d7e82afb4f7827984f9827639728233416d822bfa848229cf8c81b77d6f81b76e8e
  | 6, 21 => 0x8f3acded8f00d8a38edd5f888ed741c18ec635f58eb599738e965ddb8e7d732a8e52fbf68e27cd4e8e2522c88dc4f0798dc3e5858da207fd8d88441d8d6b37518d5c0a998d395ff68d32e83b8d2eb7558d1d99c48cfeab508c73f3678c5cc43e8c4a4e318c1abb018bf5595f8b3f92418b31c58e8b0efab98adfa09e8ab84b5d8aafa50e8aa94ae58aa657898aa44b2d8aa3b04f8a91658a8a7994f88a69d2278a4b2c568a2ec80d8a0b34fc89efee9189e82eb989cdf33589cd068489b9a4c5897dd4148974814d89485095892f9eb889143e428910bff488ede02888dbccf288cd013b88a82a5488a4fc218898b407886fedcf8862933d8846fbcd884052b7
  | 6, 22 => 0x95daf82895bcff2e95a7bcd395872ae69582ff9e95370e769520bde9951ba0c994b8834e94933acd947da14a947012d3942856c8941d35b8940d963193f38d2a93e2499393ad21ba93a597699365df5093602c46935371a9934b34329349a8669322c346932295b993154ea393104a2b930b07bd92cd311e9280652692624761924b56d492470525922ccdbb92002a6a91b6394091a9378a9190d39c918b0169916bb660915bff58914d614e91336cd3912821e49102d10890f68a7190e225fa90d48e7390c97f53906837b89066fa26903733999037307490247a8c9022657e9021a9fa8feff2ee8fe77d2d8fd5443a8fa2db658fa19e1f8f6057d08f4a1642
  | 6, 23 => 0x9d413caf9d3121ea9d2f099b9cf14cd49cd8b9f79cd7cbd59cbb54e09c8160609c5ca0df9c354d039c3531c39c19ae4e9bff60119bfb29749be41d5a9b74bd5f9b65baef9b34b1219af887159ae9b04a9aa07b839a95b69e9a5f17019a4ad2999a235e0599f80ac699d8cbd4998cea0d998829a3996e299c994b9d0899440663993bc0d59933b443990e529298e9771598ddc02e98d9c6b898910278988a6f26986d00ac97f029a397b54e7e97a75f8e97a53cfb97a4f387979d0535979939bb97708ba597012b8496f8e2cf96e4918296da145596d6a62496b2164796a4ba90969f6b1c9696455296661ea3965db264961be3db9608f40395e5515995e12b3f
  | 6, 24 => 0xa33926f8a3219133a3098384a304c619a2d0fecfa2b92933a2b3fd1fa2a6f9a5a2a24eeda275c8f5a26ac20ea256c1a0a23d2cffa22b6a16a201acb6a1fff7b4a1fee453a1f16defa1e5f75fa190b783a18a8e87a171e072a15ebe12a1521c33a0f696e5a0e0586ca0c27a1ca0aab22aa0a41939a099d7c2a0772712a06b55ada03c38c2a0369f44a0363e9fa02ef21b9fc485669f90b24e9f7f6c789f7298a79f726bb59f6e4b0d9f55b6a39f3584529f307a4a9f281e6a9f22e88e9efaea139eeb49849ee2b6579ed6de7b9ec0d7899ebfb44d9ea0779e9e93ebe99e64b9f29e56566f9e3c45669de1aca49db823729daae7359d99351f9d770c479d42c3eb
  | 6, 25 => 0xaabddd55aabd8836aa3bafddaa1f6e87aa191824aa00aaa3a9c667e4a97aa236a97a0c43a9789f6da95dfcd0a94093e3a93be014a92fbfbda92ef1eea909e4c1a8e4ad46a8d62ca7a8c54723a89be350a84782efa840633ca8249059a80fa957a7fbc882a7e0c10da7835c62a765d18da75b8798a746ec86a72e629ca71f7ceda69eb47fa69d5214a6910249a68d7cf8a6563cc3a60a91baa5fa6e2ba5d7b751a5d4719da5c2748aa5b27004a5ae8250a5a62689a598068da56f4746a55beef2a550f087a53255c5a5268c5fa50cabd5a509d3d0a4d69db9a4be299da47fbd12a476e968a471443fa46db910a40177f8a3a56a26a34e2da3a34731dba33b889c
  | 6, 26 => 0xb1fba0bfb1f9e3e0b1ce22c6b1b8bb56b197c8cdb169cadfb101c6aab0c8b55bb0b9922fb0a1a8ebb09f38ffb03048a6b02f596cb02e3777b02513ebaff20c80afd23c0cafc83106afc719aeafaab267af943b0faf73e99baf73942eaf63fae1af616e2baf6075e9af249adcaf13a005aef5af7aaeec8abdaeb38838ae948155ae6822efae5ad4f8ae52400bae43eb51ae11518cae110966adec3e13adeaf2e8addfe763ad9c65faad9683faad965e55ad83b721ad7309f1ad48125ead3b090dad05790aacbf5c17aca9b064ac54c35bac41a9b3abe10579abc968a3abc00307abbcbea2ab89854eab671e17ab63d8acab3a6fdeab214571aad9b799aac40ebd
  | 6, 27 => 0xb91d4ce9b90dc9b5b8d90467b8a1b513b889a36bb88932b6b8767b00b871b7fdb86243b6b846a1a8b81e2e8ab7f73197b7c093d7b79ef288b78864c3b777ceffb73a7128b72f93ffb6f0c5d1b6cb1964b6cade13b6be7634b66e795fb666254db63701c7b62922e8b6251136b5dd345bb5c04ca8b57d5dacb573f4c8b55f3ecfb55daf2bb542871cb5406affb4d0d4a4b4bad623b4acbb32b4aa19c9b4a8fae1b47be621b432738eb3f39d47b3e7728fb3d062adb38eb12cb37c045eb36b0913b33db3e6b32acdd7b2fa3a99b2d40c22b2c70f7fb2c0fc52b2ad74deb27deebbb27cccb0b2794cefb272d876b24f00d3b2478df1b245d9dab2118fd6b1fe93d5
  | 6, 28 => 0xbfb0ffd1bfb0cba3bfa41077bf83682fbf62c138bf5cc181beea5a39bedf3b8dbece32d5bec0a575bea336b7be95c8fabe907f01be584277be53e0d5be51f704be4769d9be3add0dbe269a7bbe179289bdfb5dd0bdeb6445bdbc7deebd6e211abd367e88bced7c31bceb8a3dbccd4b3fbcc8e334bcb7912bbc95da00bc87e6edbc84df1cbc7e8f37bc6f3652bc591900bc10ccdcbbedd967bbe3d513bbcf1011bbcc115cbba736d9bb75fc4ebb47b9debb29fef1bb28b1adbb1464cebaf3a306bae9d770bad09d59bad020e5ba701036ba5b824aba45dd7fba423037ba231cbbba1aa2e5ba133d13ba0b356ab9b83f34b9aa6055b99d5700b9552079b93206de
  | 6, 29 => 0xc5c29045c5899ec0c582c47ac562a862c5382f90c5368674c50c7b54c4f7a12bc4f0f67cc4e960c4c4e47f86c4b9fc07c4949487c48fe98ec48d67a4c46ac8f7c45a607ec434f8fec432019bc41f6b96c3b34d4ec3a56e6fc398766ec391afb2c38e86d8c38acab3c3737f0cc3675414c3606443c337f1aac3347db3c3334588c3117bbbc2ed32f6c2c56a8ec2b84f8ac2afde01c2a091e1c29a9771c29577aec2932210c278c27bc26e5d2bc23c3efdc23a672fc1fa1783c1ebf1e0c1dbd993c1907b16c182a013c1711256c150dc12c121cba0c11b9ec3c0ae1084c0a55ccdc09670e8c095d15ac0876925c05fc100c02e5d34c00da4a7bffca9abbfb4dd66
  | 6, 30 => 0xcba7c9c6cba55076cba24973cb8410e2cb7ec15ccb7bf774cb308914cb2d3d5ccb2d12cccb22d64bcb15e403cb09853fcaf2086dcad3949acad25745cabb86a9caa6b7f9ca8af8c4ca55486bca5290e6ca35eab9c9fddb4fc9f2a206c9ee7b2ec9bdabcac9a3b4fac99a8360c938f864c933e748c91a9764c904d60fc8e779a6c8e3e5cfc8b997bbc89b91e3c8646ec8c85e0905c842caacc8385198c82aa73ec822cda5c8205f4fc809f2e1c7fe034ec7fb9b52c7fb6ba2c7f451a9c7d9cf9cc7d85b91c7d3f23bc78909acc75d9bc3c756f41ec73b92adc70560b5c6f8273dc6da308dc69fce5ec694f353c63ef557c63e6ab8c63e4d23c637c9f1c5d6acb5
  | 6, 31 => 0xd2f75b26d2eb9853d2e4589cd2e2669dd2def3e9d2d16c5ed2cc6b2ad2c6073ad29440d5d26b44f3d231461dd2299bdcd20d1552d1efb8f3d1de8b17d1d6acffd1cb1b0cd1879d90d17bf5cfd164974dd0f6d7dfd0afe803d0418164d02d5d1bd027ba97d010ef66d0022fedcf908834cf7566e4cf4fc704cf2fed9ecf2c74c4cf1f3ed4cf15b2e6cf000eafcec778f9ceb692f4ce5af25dce51c518ce39d75bce20611ace1ee8e6ce08e40dcdf98342cddd1867cdb0a1f9cda6e723cda438cecd8c6716ccca3424ccc7daa6ccbe85adccba3bdccc98d68acc8aecc0cc56fb91cc452051cc3d2a65cc314ee5cc1d4d7bcc1a159bcbf0bd33cbd798ffcbb9f257
  | 6, 32 => 0xd812cfdbd7c4b6a3d7c43538d7b1f09fd7adc8ffd7948ba0d78c0afed78a0a44d786c099d783df75d748aebdd744500ed7404b60d7216316d7168563d70a1d9bd6de8f0bd6d35949d6c78025d6af2d85d6a5bda7d697b081d68e0ee1d66524e6d6382f23d6360ac3d62dbb6dd612c66fd6064892d5f531afd5f3eb55d5ce88c2d5c9d7fbd5c0efffd5bfd6fdd5aad949d5a0d46dd57db6c6d568b144d5676af3d528804dd51780c3d50bf219d4890869d47eb7c1d47790a3d438da3ed42ea9d3d42b6155d40aec9cd3fd79dad3d2caa2d3cec290d3bfb42ed3ab69cdd3980975d3792a58d37558c8d36f30acd34d4128d342c3fbd3152e0bd3103ad1d2fd1e15
  | 6, 33 => 0xde5e1fafde35f7a5de2834c3de1ecea9de18e6c8de01046cddf96729dddb30c3ddc15ca4ddb5fd1cdd8ed5d6dd50c1cddd393b92dd2a54f0dd1a865bdca563d6dc7f74e5dc778fdfdc374bc4dc2c6374dc0740d3dbf961f4dbe6b227dbd11a6cdbc7af05dbbd4d6bdbbae8e2dbb7842adbabf10cdb83fe16db5ec7f6db4f33a9db48ce50db43194adb15c90ddb0b8a8cdb092744dafef9a9dac7a96adac0e1e9da650bedda62d3c3da48bd92da0e6468d9d792fcd9c29a4fd9b417f4d9840b17d970540cd96edbf4d94ad137d942b014d916dedcd8f65272d8c89669d8c3dd20d8c00a96d88d7dfad87f9952d872797ad8702450d85d0165d81684ecd81564fc
  | 6, 34 => 0xe55dcfb7e54d2d9be54c555fe5432f87e5432933e537d6d0e5243755e510d727e504ee61e4de93f4e4a3126fe485a5e1e455e20ae451171fe443cbace4279e13e41e5447e3ef42d0e3e18a9be3d3e65de3760cf3e35f01f3e3548cede33cbb01e31a7a5ae2f911b0e2e5bc00e29b9837e280ec37e254a19ee230c8c7e22b4d5de20f79eae1f91c91e1e77a90e1b1f408e195a639e11fddafe11bb465e0bfe9fbe0bbc7c6e0af52eee09bc3c8e09b3ae1e0930e9de0800c8de07b344ee0675ff1e04e0661e02ccb21dffa03e8dfeb09c7dfd12c8bdfbe1decdfa5e763df66edf2df60a9c0df5bf037df2c783edf204264df1659addeec6317dec9dac1debf7146
  | 6, 35 => 0xec0c1396ebf03b1eebefca4bebd9c278ebc28ee5eb949f2aeb6a4ac1eb6724bbeb5ee70eeb29f7dfeb0eb4bdeaf7f023eaf5c476eab31e8aea99b7d8ea96d1e2ea812a8bea6e77a2ea5f1dabea5d5ff0ea0fb8bde9d9bca8e9d711dae9c69768e9bd6f91e9b0c204e96fe5a4e9674be0e964ad1ae95432b3e945efd6e905686be8f9d38de8df0d24e896cba3e88d44c1e879dc3ee86eb0d6e865b5b0e8529c71e8372b18e82d725ee80aa186e8047120e80138e2e7eb888ae7e6faa8e7b301e7e7a21dd1e71b0a50e714a497e6729df9e6628092e65393cae648521fe61e3e4ee61c8455e5f7c8dfe5e351dce5e14f13e5cc13a1e5b44ac5e58afe19e56ae1b2
  | 6, 36 => 0xf2978429f279123cf274adb0f25014fff249a559f23bfa06f23a36e7f208a2b9f1ea6d7df1d8e4a8f1d7f84cf1c6f18ff1a91aa5f19a275cf1820790f171c893f15a4793f0fcd1a5f0fa8a62f0f8df95f0e86fe3f0b082cdf09b8930f0985b0df0835436f0557068f0556ec8f03d9387f02597d4f0010e1beff3c368efc2e112efafc882ef94b1afef831902ef5b4d9fef459853eec40f0ceebe9aeaeeb70349eeadf89cee812039ee622b56ee5bfb02ee5390f5ee1e2c58ee02495bee000531edd0785cedc03d67eda7101fed786edbed52219ced50c2e9ed215bcfed1a88f1ecf2ba94ecd37faaecb47af8ec86a5d8ec7befe2ec7abfabec6b46deec3e9026
  | 6, 37 => 0xf9495e50f9300d32f9143161f8d5ce41f8cfbf33f87cadc2f87a4a6af8577a8bf83dd259f830b686f82a1642f7f9dae8f7e68aa8f7dda69af7a45692f766edbbf755edc8f74f43f7f74c3499f73a66a0f6e6c10cf6e496dcf6d3c780f6cc6686f6c722e5f6a1142df69357a9f68e6a67f681b3f2f6655c2cf650f9aaf6334be5f61da697f5e77c9bf5dadf09f5c1f3eaf5bdd01ff58f108cf58d3b0df58182cff5277aadf51561b7f50a2f19f4e8230af4c89bddf4a631d0f4583038f4535bf8f41eb87ef3ef218bf3dd72f6f3d533ccf3ab159ff34d8d5cf3487822f33b5fd0f2dc9b47f2da1b3ef2d7e58ef2c92a07f2c41b18f2b97b7df2b121c6f2a6d50a
  | 6, 38 => 0xffabe638ff98826cff91be5cff3bcdecff2325bafef4c9f6fee5981efec6917efebe0ea5fe967428fe78c91efe6ebe66fe5cb65dfe579c7afe5264f5fe4d0768fe3abca4fdd6902afd9eb53cfd8987c4fd80eb38fd64caacfd580db9fd48403efd3bb91bfd135a84fce8a04bfcd7f438fcbce5a3fcacbd6afc86bf18fc4a1fedfc3f5bf1fc3650befc35f46ffc30abd5fc250e5efc17630bfbeed6c8fbc84b48fb992bf4fb7005dbfb4008c7fb30cdadfb192d73faf92908faed5a6dfaec6079fad8dc57fa72f38afa728806fa6ba27bf9fd9034f9d074b8f9b8c4f3
  | 7, 0 => 0x12b8ab4112b8884a12ae5da312798028124e263511d7480611b4128d119811441187183a11761aa81134c93410d1aa96102d8cd30fd4c3f50fc22fb60f8898390f3badb20efa46790e57c7a70dfb96ef0db675560d9a92370d91ebc20d61f2fb0d4d98860cf91d9f0cea20e10cb3009d0cabde0a0c867e660bd753a90bb2ffb10b989d440b41c7720ae892150acf09dd0ab7b9ae0ab0afbb0a71f95609ee1b6f087867580864c5e507bd347d07af559e06ecbabd065223ce064612c7061ab28604d0acec03e36454036df150033a727c0322eb1802d5abde0296f579024a740d023c952e0198251c018309d90129b75501013f360086a50c0064991500103def
  | 7, 1 => 0x2282fd3e21e9d24d21a5f96820df43cc2081cc612064873a2046aaad203e530f203cd04e20292edb1fd3d3851ee4e3db1eb3facb1e8eec381e3d0e221e1aa3ae1e17d8601e08e1531d989e101d81c57f1c53b96d1c1ffead1bde45011b78d4bc1b70b1901b325a461b2d157f1b1036f41a5d39541a45ab1d1a4058c31a2bfa9c1a0dc40d19f08aad19deb3e21979f4171923eb0b1922d7aa191531f41900f42918e3fb0a183e8305181aa94117d6fff417d07b00174ef90f17206e35170db67f16e8db1816b50ee9168a4efe1623f29c1606144c15f86a801561a43a14f37973141a4f1c1415063f1413d60814121a0c13b5da6d135211a2131bfefa1317dd2b
  | 7, 2 => 0x34744a7f342cdee933d93c6b33ab0d08333e196732e7627a32e64fc5326a0621317141fd315024ba31381b073129ad3f30f26f0930ccd1eb3078c0812fc976f62fbf18df2fa1c82a2f7655c82f1362052edbd6b52ea0b9112e9e70832e46479b2de85b922d6df75a2d014b912cf3c0ef2cf085992cb7e2692cae27f22c9946a22bdd94e82b48380c2a7c85282a6bdfc029e942c429c478db292df8a1291abe562889888f2882e2b2284db2db2838c79a2774c4602727707326e36c2426d2458e26beaf6f26a4b5bf264ea121261c309d25bece64259eb530255ffecb2509c4b8246ade96246554a623fe6fae23e92d1223afce9223a7fde623038dd422c1b3a3
  | 7, 3 => 0x48ebd2aa48b0ac9d484e6acf475141bb472e33c145c07cca45179a8f44cd758b43cee64d43b42571432891ef4309ffd842b779a34223bdb941d9fb7841d622d341a83906405c8f3d40455b7a3ffca0873f8b9abe3f49363a3f086e6d3dff89d03dc32c533d8620523d18fbc93d0124c93cedcf813c9f3cdf3c9dc2fe3c3d49423bd0b7833bc2d8a43b5624293b3c318a3b23954e3afd7b253acd3e823a861c993a67daad3a476634396f572d395003403899ed1837f1b87637dd7e8037a1ed1c378f31e8375fd1e83732d33a36e4026d36ad5160368990f73678c0eb363c57f436224d1b361b1af435d89aaa359aee6d358e7c13357bcd57354bc4fd3518dab1
  | 7, 4 => 0x5a7078f859e9c31b59e5330159d66aa0596bf2065943cbfb5923c1c65905159658a5f177584e132a581fb8f657c3519855df5df855ab6c465592bd7c558b8750557f4cd954ed1c7554b47b9853b7a8b553b3d16b53169294530ec13f52e996fb52acbe7d528ca242520a3fab51e81d5151d2062b51a4e007516924ff515c291951007c3a50a706e84f9b055d4f717d1d4f624ff44ed5e3f64ec7de7a4e9d19034e79bd534e7327324e1db72a4e0e9fc94e00c0ea4d0476064cfd734b4c854e674c173de94c1326ad4bf147df4bb8974e4bb13b214b62f61f4b40518f4b02825d4afc5e1e4ac0774d4a9f53ac4a6707154a0d197449d602e8499cfa0a49148db0
  | 7, 5 => 0x6ce170276cd622c66c8fa51c6c4b6e046be1bd3a6bcb63fb6b7c11ab6b1be3666af785736adde2696a7ff6686a5eea176a510b386a4fc62d6a2a46cf6a0139de69f9213969f5d2f969c031bf692e70ee6920920f68ff5c7d68b561d0683fb3fc67f1c0d367425c616709aa6166fb4c91668c477066742ba766357542651506a464ffcc4e64cf00c564789948645092fc6449b75d64015902633af0116336351163275f1562b43c176292bf226284e04362542af86129ea2960c016455f2a63495eebace45edafec85e90082e5e06e6065debf6475d9647d45d93d62e5d3a46645d2e415c5d23bf8f5c91de815c0095e65b2acd595b0171135ab946475a73054d
  | 7, 6 => 0x7fb9fc427f5f0e0b7f27d8097f1797dc7ebd26667ebbf6017e8559377dfd47397db1e1917d776c2f7d356db97d33ff317cd372a07c439fcf7ab597257ab2c9087aa157477a70b1287a14827479a4d76c798a90b2791d9b417900675a78f04d3478925775785a178978493a7f7733bc5377211a3f76fcab1e76f0de3376f0916b76eecc3f76db0b2e76bdf4b976b015da75ee73ad7540089874f2245d74e1bd61749b988673a1eeb77341d2fd7333c42e73227b8e72b28339727daf3d72739f547263b2ee7260e48f721cd83371be65bd70ffce1070cdf074707cee8d7005f1236fa6c90d6f6c29a26ebe77696eba99336e38e6f66e1ad9ba6ddedbb86db8095f
  | 7, 7 => 0x925c0be491b98d1291426eab913b5e9f9037c66b9011f582900c69668fe9ad8f8fa2db658f9d1d5f8f78512d8ebf00228e4941358e35cdb08e2374cd8d92f6958d7f04bb8d1e3ac28ce77a638c8386ea8c76bee98bedc1998bc68b508bbc73f08b8fda438b3e939c8b308e208a8bfac78a18c28889beef4c899b6c72897643b689605ac288edfe0d88ede028881ad29987ec230287ca80ca877c8a9f876b320387080352869b7594868cb4248651842c8635a6fc862851b985f48e9f85e99b5485520fcd8549f6d285210b0384fbb4208492c7cd83f048fb838341f4833df90382d3eb99828511a482739f208241b05981bd8a2f804281917fe35f827fc0036d
  | 7, 8 => 0xa661d0dfa623790ea5e4c2a9a5cabbeaa5103ec2a36baaf7a35f8a0fa2f4f716a25e4bf1a141bf77a0c045e2a0b26703a00d2aa29ffd08839eab30d29e6bbe4b9de02fb29da1794d9d2d50bb9d2006f69c97dd089c36144f9bfcd7929ab0be7a9a95b69e99bbfbc99985b807997d456498d83969989a69279882e2ec985a34f798553ede981b7e9297ec88bb97a5128c978d297c974e731797251c989721f5ed96e3fc3596a4b77d9680ac86965f3458965531e69603a49895fe78aa956125c6955a0898950fbbe39502be1694b8834e94331b659396353d934043b892ef453392b08ece92a6c201929a9c84928df768927a567e9272b1cc926d751e9262028d
  | 7, 9 => 0xbbec3344bb3f92c0bab08b31ba477786ba2399e2ba1f06b4b8a1b513b7a3f583b7610a65b713f0d0b69fded2b65f3e8fb63701c7b59a84ddb52557b8b4e46fecb3823d02b32b1ae2b2f03ccbb2313513b22e7c90b210ca3fb1b17014b18cc501b12375bdb108215ab0ec7e1fb07bc511b0480e0db01ae1b0affee213afebec7daf01b67aaef43dc2aee65ee3aec64c0eaebd223cae5c9576ae0f7c92adab993dad85a160ad6e1b08ad6b0c80ad1a90a7ac3ab49dac296414ac23afedabe5308aab962e79ab681b8eaaa935daaa3f12b1aa38618daa21bb6da9cb11c2a9647ee6a95dfcd0a94c6287a909e4c1a8d69abba80d4bfda7bb98b7a71939e5a6877d59
  | 7, 10 => 0xce3bc8d3ce37cadccdb20f90cd5fbf4fcc0fb7b2cc0b8b0bcbfcbae9cba24973cb46a5f8cb26fa2bcae6d7d7ca35eab9c9e65a89c9e24337c9a019fdc8e779a6c8df6e8fc7a9b843c7a3ca76c7554d2ec70541aac6ea46f2c689fa79c6398efac61b5c10c5e58a67c5d3e588c5c226a0c59d6c30c5899ec0c57cede8c5690328c52f7576c4ac2c82c4605fcec3935453c37f968dc34f33b5c31b6fd9c278c27bc23de552c21dcfbbc1c6e06ec1c5a5bec110cb7dc1043454c07ccfeebf4172fabf01fb40bef5700abee065e9be6b5265be4f311bbe4be64fbe3418b4be2639d5be1fe45dbddd5bacbd3f82f8bd2744b8bcf5d0c6bcb2dff7bc5e25f5bc18011a
  | 7, 11 => 0xe2e94854e2e453e9e1e7aed7e1c2a466e1b94d76e1b1f408e0f3695fe0d9cf49e0d27efae088d44de044fe41dfdba1afdfa5c541df91a28ddf7fbf91dede789bdec9aaa0de7f8515de1b0bb2ddfd151add547ea2dd4db3aadc240579dbeeb34dda8fa153da7890dfda26b2c9d9ed2281d9eccea3d9e7a089d988b69cd958a3e4d8f62b1fd8e7dfa1d8c00a96d87f9952d7d8277ed7661623d6890d25d62ad27fd5d7c256d5d13c99d58853add56748abd4fb6d4fd3fa20bfd3c1c38ed38eac86d355d4ffd3152e0bd30f653ad2f75b26d229a3e5d1d3f658d1b38e6dd0ab600ed051c79bd0317033cfe713d2cf9551ebcf6e15b1ceecb93fceeb1ad8ce6b8b90
  | 7, 12 => 0xf76d67adf762f14af734b506f725d631f6f16d4af646c3bff637ead7f5a8ee32f50771aef4e77514f3e60244f39bac49f32a1730f1c1f496f17a65ebf171c893f14d1f92f11d8484f117a0a5f0f10dbef0dd9aa2f0c2900ff0107b11efeaeca8efdef6d4ef94b1afef4adc1aef0e3eb4eeae7dabee6bbfe2ee570e7dee1e2c58ee185818ed5ae6a4ecfeda8bebc28ee5ebb77889eb7a065aeb0c9569eaf7dac4eabec0cdea782c38ea72c195ea39f55de9f23fa9e9d3bc26e9b38944e8f19d4fe8b54ab1e878be20e812cbdfe7a75556e795c008e73c37a0e6a7c695e5c6ac76e5b5122de5179d48e48a3599e4402e8ee3ed24d8e3d420a8e2f6cc76e2f02cff
  | 7, 13 => 0xffa13466ff5a28feff3992a2fef2bd64fed37441febf47eefe12eeb4fe091979fdf560cffd797b23fcf8d17ffcb4afe6fcb0a9dbfc7cb7dbfbefb591fbe5e7c4fab495f5faa130d0fa6ea56dfa101145f9d3a84ef9824cb5f96feb04f9092d95f8b72109f8327782f80ff336f80fe67ff7fbcecdf7c476a1f7c42f43
  | 8, 0 => 0xf33b5fd0f2854adfdee29a6add9de376dac0e1e9c3d681efbad4da24a6563cc3a1f16def5e22a75455df5df851bb2a0f5059633d4aee737942b779a33e277fff2eedfa851e7359ed1729918f
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x180424c130100000000c8105275804144140100000000c410400180424813011758042481401450592008140047081154804001758042481401
  | 4, 0 => 0x1048120300000000c11017050c3550440000000000c810400000450c1200000000000000400000000c410400000254c42003618021484400000004248120100095104403012151550484400001942044130000180424c13010018042481301000592008130000000000c810400000104c120300114200c130000000000c4102000000000000000000000c410400000000c810500000000c8105000995010530100000000c8104001182048030000000450812000000050484200000000000000400000450852000000000000003
  | 4, 1 => 0x600000000c810500000000c81040000045484200000c9514c8301001944248130100180424813010000000000004001185148130000095314c430100000000c810545099310c140000000000c810500000000c81050000000000002214d55048440045184324c540000000000c810500000454c420200180414413010018042481301001804248130100000000c810500000000c810400000314c420000000000c8105000855048430100000000c81051758042481401000942044130045099310c140000000000c8104
  | 4, 2 => 0xc41040000035484200001182044130000180424813010000000109101000d52148430100180424c1301000552048030100000000c410400000450c5200001804248130100000504c420000000000c81040000020441203001843548130000000001051010000000081103000d8514813000008550484300000000000000300000000c110300000000000040005950109301001804248130100000424c120146094204414000018045485301000002148420000180424c13012151550484400000000004c104000c5254c4301
  | 4, 3 => 0xc810500000000c4104000000008110370508355004000000045085200000002044120300000000c410400000000c41040018042481301460942044140000000000c41040000000000000001804248130100000000c8105001842044130000000000c41040000035085200001183548130000000000c810400000000c8104000c15010930100000000c8105001804248130100000000c0102214d5504844004708115480400000000004c104000c9514c8301470c5254c4400215153548440000000454c42020000000000004
  | 4, 4 => 0x5050c200001142008130000000000c4104000c14248130100114310c130000000000c410400000000c810400000000c410400181350853010000000081103000412544030100000000c41020018042481301000811548030000000504c4200000595010930100000000c4104
  | 5, 0 => 0x400000000000060000050109201000000000000400000000c41020000000000006000000000000200000001091010000000000007000853548430100000000c41040000000000004000000000000200000000000070000000000004000004508120000118304c03000000000000002001182544030000000450812000000000000003000000000000400118514c8300000000000000400000504c42000000045480201000001044020100180424813010000000000004001183550030000000000411000000000000005
  | 5, 1 => 0x85504843000000000000002000000000000400118314c430000000000000040000000000004000000000000200000504842000000000000008000000000000600194204413000000000000006000000010910200000200c1200000000000000200184324c53000000000000002000005010920100000000000050000042481201000d825441300000004508520000188354413000000000000008000000010910200000001091020000000000006000000000000500000450852000000000000004000000000000000000254c4200
  | 5, 2 => 0x18142100300000005048420100000254c420000000000c4102001843044130000000454c420200000454c420100184304413000000000109102001843548130000000000c810500000000841000000000085101000001500220000000000c410400000450c5200000000000000600000000c410200000000c0102000d8214843000000000000007000000000000200000000c810000000450812000000000000008000000000000800000000411030000000000006000d851481300000000010910200000000000060000000000003
  | 5, 3 => 0x214842000000000000004000002148420000000424c1201000000000000600000450812000000000104100000001044020100118354413000000000000001000000000000400000000c410200000254c420100000000000010000000000002000d430441300000000000000600000450c52000000000000004000000008510100000000c810400000000000040000000000008000000000000800000000c010200000000000030000000000002000000000000600000000000000000000000005000000000000700000304c0200
  | 5, 4 => 0x1000c5254c43010000000000008000005010920100000000000010000021484201000000000000400000000c8100000000000000200000354842000000035484201000000000000600000254c42010011820441300000d945084300000000008110300000450c12000000000000002000000008c10000000000000040000000081101000002048020100000154802010000000000008000000000000800000000000040000000081103000003548420000118504c8300000000000000000000000000060000000104100
  | 5, 5 => 0x501092010000000000000000000001210000000000c01020000000000006000000000000000000000c41040000000000005000d905885300000005048420100118214843000000000000000000000000000500000000c410400000254c420000000424c1201000004248120100000000000030000000000000000000000000700000304c02010000000109102000000000000600000304c02000000000000003000000010910100000000000040000000000003000000000000600000001091020000000000008
  | 5, 6 => 0xc11010000000000001000003508520000000000000010000000000007000000000000600000000c41020000000109102000000010910200000000c51010000000041103000002148420000000000000030000000000006000000000000600000514c820100000314c420000000454c4201000003548020000000000c41040000000000008000000000000500000254c4200001182544130000000000c4104000000000000600000000000010000000000002000000000000500000504c4201000000000000600000000c1100
  | 5, 7 => 0xc0102000004508120000000001091010000000000008000855048430000000001041000000000000005000000000000800000350852000018d450c13000000000000005000000000000000000000000000000000000008000002500220000000214842010000000109101000000000000600000000000080000010440201000000000000200000104402010009420441300000000000000600118354813000000000109101000004540220100000000811030000000000008001082550430000000000000050000000000005
  | 5, 8 => 0x4000000000000000000000000080000000000007000c9514c83010000000109102000000000000000000454c42010000000000006000000000000600000000c1101000000008110300000000000080018420441300000000000000500000254c4201000000000000800000230c92000000000000006000000000000800180424813010018143100300000000000000200000000c510100099310c130000000424812010000000000004001942044130000000000000060000000006100000000000000400000000c0102
  | 5, 9 => 0x800000254402010000050085200000d4500853000000000000008000001044020000000000c410200181510c93000000000000003000000000000800000454802010000000109102000000000000600000000000060000020081200000003508520100000350852010000000000005000000000000600000000000080000000000004000000000000100000424812010000000000007000003548120000000424c120100000324c82000000000000005000000000000000000000c0102000000000000000000000c9100
  | 5, 10 => 0x500000000000050000045402201000000000000400000000c410200000424812010000035085201001182544130000000000000050000045085200001143508530000000000000060000000000006001155048430000000450812000000000000002000000000000300000000000060000000000002000003548420100000000c010200000000851000000000000004000000000000300000214842000000000000005000005048420000000001091020000000000002000000000000200000000c51000000000000005
  | 5, 11 => 0x800000000000070000000000005000000010c10000000000c41040000000084100000000010910200000450c1200000000000000800000504c4201000000000000500000000c010200114324c5300000000000000400000504c420000000324c8201000004508520000000000000060000030509201000000000000500000000000040000000000004000000000000200000000000050018042481301000000000000500000000000070000035484201000000000000300000000000020000000000008
  | 5, 12 => 0x1843548130000000000c51010000000000001000000010810000000504c42000000000000004000003548020100000000c1101001183540a30000000000000030000000000005000855048430000000000000020000000000006000000000000600000000c110100099310c13000000000000005000000000000100000000c110100000354802010000000000005000000000000200085454843000000010440200000190588530000000204412000000045402201000000010910200000450022000000000000007000c5254c4300
  | 5, 13 => 0x450c12000011805884300000000000000400000001091020000030481201000000010c103000004248120100000000c110300000000000040000000000006000000000000200118355043000010c3550030000000000c4104000000000000200000350852010000000000003000002148420000000000000010000000109102001145008530000000000c810400148324c13000008115480300000000000000700000000000070000000109102000000000000600000000000030000000000004000000000000300000000c4104
  | 5, 14 => 0x194324c530000000000000030000000105101000000000000000000324c820100000324c820100000000000050000000000008001182044130000000000c8105000000010910100000000000010000050484201000000000000800000000000000000020441203000000010910200000000c11030000000000008000000000000600000000c4104000000000000800000504c42010000045480201000000000000200000000000050000000000006000000000000600000000000040000035500200000003508520100000314c4200
  | 5, 15 => 0x2000000010510100000000000040008550484300000000588120000000000c4102000000000000600000000000040000000000000000003508120000000000000070000051481200000000000000500000000000020000000000004000000000000400000000000080000000000005000003508520100000200812000000000000008000000000000500000324c82010000000109101000004248120100000000c81040000021484201000000000000600000000000040000000109101000000000000800180424c1301
  | 5, 16 => 0x6000855048430000000000c41040000000000002000000000000600000000000010000020081200000001548020100000000000000000000000007000000000000600181510c930000000000000060000000000006000d8254413000000000000006000003550020000000314c4200000005048420100000000c4102000003548020000000000000030000000000006000005050c200000000000000800000000000030000000109101000000000000600000000c4102000c9514c830000000000000020000041441201
  | 5, 17 => 0x94204413000000000000004001183548130000000504c420100000000c110300000454c8201000003548020000000450c520000085504843010000000000008000004144120100000304412010000000000008000d55048430000000001051010000020480200000000000000000000000000080000000000000000000000000800000200812000000000000005000002500e20000000254c4200000000000000800000000c81040000000000008000000000000500000000c4102001180540630000000000000010000000000008
  | 5, 18 => 0xc0102000000000000000000000000080000042481201000000000000400000000000040000000000008000004548420000000000000080000000000004001183044130000000000801000000045081200000000000000100000454c82010000000000000000000000000300000000000000000030441201001183548530000000000c4104000000000000800000000000030000000000000001182048030000000454842010000000000006000000008110000000304c020100000000c010200000000000000000000000008
  | 5, 19 => 0x45081200000000000000500000000c1101000000010910200085504843010000000090100000000000000300000000000040000000000001000000000000000118204803000008535484300000000000000400000001091010000000000008000004248120100000000c8100000000000000400000454852010000035484200000000000000500000000c410400000000c410200000000c4102001842044130000000000000080000000000005000000000000000000454c4202000000010910100000000000020000000000004
  | 5, 20 => 0x60000000000006000004508120000000000000060010c3550430000000250022000000000000004000000000000100000504c420100000000000080000000000001001843248530000000000c01020000000000006000000000000100000000000020000000000003000000000000500000000c8105000003044120100000000000020000000000003000000000000800000254c420100000000000060000000000003000000000000500000454022010000000000006000000010910200000000000040000000000007
  | 5, 21 => 0x11825504300001183550030000000001091020000000000005000000004110300000000c810400000304c0201000001044020000000000811030000015480201000000000000400000001081000019420441300000003508520000180424813010000000000008000000000e100000000000000400118314c4300000000008510100000000c410200000000811010000000000007000000000000800000000000050000000000002001155048430000000000000040000000000004000000010910100000450812000000000000005
  | 5, 22 => 0x2148420000114310c1300001183044130000000000000070004125440301000d82148430000000210852000000000000005000000000000600000350852000000000000001000000008510100000314c4201000000010910200000000000020000000000002000595010930100000000c8104000000010910100094204413000000000000008000000000000400000000841000000000000006000002504120000000000c5101000000000000100000000000000000000000003000004248120100000000841000000000000005
  | 5, 23 => 0x10410000000324c8200000000000000600000000c010200000001091020008550484300000000010910200000200812000000000000004001183544030000000000c11030000000000007000002148420000000000c11010000035484201000005010920100000000c0102000000000000400184204413000000035440201000000000000600000304c0201001854210430000000000c8104000000000000600000254c420000000000000020000000000007000000000000400000000c110300000000c81050000000000005
  | 5, 24 => 0x5000000000000600000001081000000000000008000001044020000000214842010000000000004000004540220100000254c420000000000000010000000000000000000000000800181430c93000000000000006000000000000800108255003000000050484200000002048020100118504c8300000002500620000000000c110100000254c420100000000000060004125440300000000000000300000000000060000000081103000000000000600000450c1200000000000000100000000000020000000000007
  | 5, 25 => 0x20480200000000008110000000000000020000000000004000004508520000000230c920000000424c1201000004508520000148324c53000000000000004000003548420000000000c810500000154802000000000000004000853548430100181510c9300000000000000300000000c4100000942144130000000000000070000042481201000000000000100000000000050000000000002000000000000300180214843000000000000007000000010910200000001091020000000000001000000000000200000450c5200
  | 5, 26 => 0x60000015480200000000000000200114310c13000000035484201000000008510100000001051010000000000005000003548020100000000000040004125440300000005010920100000000c010200000000c01020000000000002000000000000800000314c420000000314c4201000000000000400000000000040000000000000000811548030100000000c4104000000000000800000000000020011821484300000000000000700000000000040000000000004000000000000400000001051030000000000008
  | 5, 27 => 0x5010920100000000c01020000000000008000000000000000000000000060011535484300000000000000600000354802010008550484300000000000000000000000c4102000000000000200000450c5200000d92504130000000000000080000000000006000000000000600194304413000000000000008000005010520100000000000040018543104300000000008110300000000000060000000000004000000000000300000254c420000000000000020000000000006000000000000400000000000010000000000005
  | 5, 28 => 0x800000000c410200000000c110100000314c4201000002148420100000424c120100000354842000000000000004000000000000600000000021000000000000004000000000000800000000000050000000000007000000000000500000000000030000020480201000000010510100000000000040000000000004000000000000700000450852000000045081200000d550484300000d82148430000000000c41000000000000006000000000000600000314c420100000000c810400000454842010000000000005
  | 5, 29 => 0x60000000000004000000000000700000000000020000000000004000001044020100118254413000000000109101001814310430000000504c820100000000000080000000000005000000010910200000001081000000035085200000000008110300181450843000000045081200000942144130000000000c410200000000000050000000000004000000000000600000000c11010000000002100000000000000200000324c8201000000010910200000000c1101000000000000300000000c11010000000081101
  | 5, 30 => 0x454842010000000000004001814508430000000454842000000000000006000002048020000000000c1101000005050c200000000000000500000000000020011825500300000000004c10400000000000050000000000008000000000000800000510812000000000000006000000000000800000000c0102000000000000800000515092010011851481300000000000e100000000000000600000001091020000000000005000000000a100000811548030000000000c8105001804248130100000000000080000000000008
  | 5, 31 => 0x10510100000000c11010000000108103000000000000300000000000060000000000006001942044130000181450c1300000003500220000000310c120000000000000070000000000002001083550030000000000841000000000000007000d92504130000000210852000000000081103000000008410000188354413000000000000000000000000000200000000000040000000109102000000000000200000000c1103000000000000800000000000050000000000004000000000610000118054063000000015480201
  | 5, 32 => 0x5001183540a30000000000000010000000000007000000000000100000000411030000000081103000000000000500000000c010200000000000000018430441300000003548020100000424812010008535484300000000000000500000000000040000000000008000005048420100000000000030000042481201000000000000700114324c130000000204c120100000000c4102000004248120100000314c42010000020480201000003508520000000000000070000000000005000000000000200000000c0102
  | 5, 33 => 0x700000000000040000000000007000000000000400000000c41020000000109101000000000000600000000c110100000000000080018042481301000000000000800000000c41000000020480201000000000000500000154802010000035085201001183544130000000000000030000000000006000000000000700000324c82000000000000000000000000000000000450c120000000000000000000000000006000001548020000085354843000000000000005000004508520000000450812000000000109101
  | 5, 34 => 0x600000000000060018042481301000000000000500000314c420100000520c12000000000000008
  | 6, 0 => 0xa1000000000000004000000000000000000324c820000000350852010000025041200000000008510100000304c0200000000000000300000000000020000000000005000000010910200000001091010000000000002000000000000600000000000070000000000007000000010910100000324c8200000001548020000000000c510100000504c420000000504c42000000000000002000000000000300000450062000000000109101000000000000700000450c1200000000010910100000000401010000000000008
  | 6, 1 => 0x200000324c520000000324c82000000000000005000000000000200000250062000000000000004000005048420000000000c1101000000000000200000000000040000045085200000000000000500000450c120000000000000020000000109102000003550020000000000000050000000000007000000000000500000000c110100000000000050000000109102000000000e100000005050c20000000450c1200000000000000600000000000030000000000007000000000000700000000000010000000000002
  | 6, 2 => 0x5000000000610000000000000060000000000002000000000000200000450c520000000324c820000000324c12000000000085101000000000000800000000000000000000000004000000004110100000000000020000000000002000000008c10000000324c8201000001500a20000000001091020000000000007000004508520000000000000050000000000008000000010410000000000000030000000109101000000000000200000000000060000000104100000000000000000000504842010000000000000
  | 6, 3 => 0x454c8201000000000000800000324c8201000000000000400000000c810000000324c1200000000010910100000000c5101000000000000600000000000000000000000003000003508520000000104402010000000000006000000000000300000000c8100000000000000700000000c91010000000109101000000000210000000514c8201000000000000400000104402000000000080100000000000000100000000000040000000000002000000000000200000155002000000000000006000000000000300000450c5200
  | 6, 4 => 0x100000354812000000000000004000004508120000000000000000000000000006000003540a20000000000000030000000000004000000000000000000000000040000000000008000000010910200000000c91010000000000002000004508520000000000000020000000000005000000000210000000000000070000000000007000004500a200000000500a20000000000c11010000000000002000000000000500000254c420100000000801000000000109102000002500220000000000000020000000000005
  | 6, 5 => 0x5000003540620000000000000030000000000002000000480a2000000045085200000000000000500000000000050000000000007000000000000400000000c0102000000000000700000104402000000000000001000000010810000000000000080000000000002000005250c200000000004110100000000000040000000000005000000004110100000504c4200000000000000500000001091010000000000007000000000000400000000000000000000000006000000000000300000000000010000000000007
  | 6, 6 => 0x1000000000a10000000000c0101000000008510100000214842010000050484200000001044020000000000000020000035500200000000000a10000000000000060000000000002000000000a1000000000000008000000000000500000304c020000000314c420000000214842000000000000006000000000000200000000000040000000000006000000010910100000424c1201000000000000300000000000070000000000005000000000000700000450c52000000035480200000000000a10100000430c9200
  | 6, 7 => 0x355002000000000012100000000280220000000000000010000000000008000000000000200000510c120000000450c120000000314c420000000255042000000000000002000000000e100000000008110100000504c4200000000000000400000000c8104000000000000300000000c410200000000c4104000000000a1000000035480200000000000000100000000000080000000000002000000004110100000324c82000000000000007000000000000200000000c9101000000000000100000000801010000000081101
  | 6, 8 => 0x40000000000005000000000000100000000000070000045041200000004508520000000000c1100000000000000100000450c12000000005406200000002048020000000000000040000000000004000003548420100000058852000000000109101000000000000300000000000040000000109102000003550020000000000000040000000000003000000000000500000000000030000000000004000000008510100000154802000000000012100000000540a20000000504c820100000354802000000000081100
  | 6, 9 => 0x504c4200000004500e20000000454c82010000000000004000000000a10000000450062000000000000004000000000610100000000c41000000000085101000000000000600000504c420100000454c42010000000000006000000000e100000000000000800000000000070000000006100000000000000400000450022000000000000004000000000a101000000000a101000000000000500000304c0200000000000000500000254c4200000003500220000000000000070000035441200000000010910100000000c1101
  | 6, 10 => 0x454c420100000000000040000000081100000000000000400000000000040000000000001000000000000200000450c1200000004548420100000450c1200000000000000400000304c0200000001500e20000000000c81000000035085200000000000000000000354842000000000000007000000000000500000000000000000025500200000000000000300000504c8200000000000000500000001091020000015002200000000000000700000000000040000000109101000001548020100000000000050000000000001
  | 6, 11 => 0x504c42000000000000005000000000000100000000000000000000000006000000000000600000450c52000000000000004000000000000200000000000020000000000002000000000000200000504c420100000454c820100000000000070000000000006000000280620000000000000060000015480201000000000000500000450c120000000000000070000021484200000003548120000000000411000000045081200000000008010000000304c0201000000000000500000000841000000000109102000001540a200
  | 6, 12 => 0x400000000c110100000504c4201000000000000300000001041000000000000006000005050c200000000000e1010000000006100000000000000500000421002000000000006100000000000000100000001051010000000000006000000000000700000000000010000000000000000000000000100000000000050000020441200000000010410000000450c1200000000480620000000000000050000000000005000004548420100000354412000000045085200000000000000700000000000010000000000005
  | 6, 13 => 0x3550020000000000000020000000000006000003548020100000314c420000000000000030000000000006000003548020000000000c9101000000000000000000000000040000000085101000000000000500000000000020000000000007000005048420000000000c01020000000000004000000480a200000000590420000000000c510100000000000010000000104100000000000000200000254c42010000000000000000003548020000000000000070000000000002000000000000200000450812000000020480200
  | 6, 14 => 0x200000000000060000000000007000000000000200000000000020000000006101000000000000600000001091010000000000005000000000000500000000000010000000000004000004210420000000000c010100000254c4201000003540a200000000584120000000058842000000035484201000000000000400000000c910000000000000020000000000008000000000000400000000c5101000000010910100000350852000000000000003000000010510100000000c1101000000000000400000520c1200
  | 6, 15 => 0x314c4200000000000000600000000000050000000000005000000000e10100000000000040000000000004000000000000400000000000000000050484200000001500a20000000000c51010000000000004000001044020000000450c9200000000008110100000504c4200000000000000500000001051010000000109102000000000000000000000000020000000000004000000000000600000000000060000000000008000005050c200000000000000200000000000000000000000004000002500e20000000000c4100
  | 6, 16 => 0xe101000000000000400000000c510000000304c0201000000000000600000000000050000000000000000000000000100000000000010000000104100000000000000500000000000070000000000002000000000000200000000000040000000109101000000000000400000000000050000000000002000005150c20000000000000060000000000006000000000000500000000000050000000000001000000010910200000000000040000000000004000000000000400000000000080000000000008000000000a101
  | 6, 17 => 0xc0101000000010910100000214842000000000000002000000000000400000000c510100000000c81010000000000008000000000000800000154802000000035484201000000008510000000000000010000010440200000000000000100000001091020000000105101000000000000600000304c020000000000851000000000000005000004540220100000000000040000003802200000000000000600000510c120000000000c510100000000021010000050484200000000000000600000000000060000000000006
  | 6, 18 => 0x200000001081000000015480200000000000000400000000401010000000000003000003548420100000000000080000000000006000000000000200000000000080000002806200000004540220100000304c0201000000000000300000354842000000000000004000000000000600000454802010000043104200000004508120000000000000000000045085200000000000000300000000000000000000000002000000000000200000000000030000000000000000000010910100000254062000000020480200
  | 6, 19 => 0x2148420000000450c120000000450c120000000000000040000020480200000000000000600000515082000000000000006000000000a1010000000109101000000000000400000155002000000000000004000000008510100000324c820000000001051010000000000007000000010410000000001081000000004806200000000000000200000450c1200000005048420000000001091010000000000004000000010910200000001091020000000000005000000000000700000000c010200000000c81010000000109101
  | 6, 20 => 0x304c0200000000000000300000254c42000000000084100000004248120100000000000030000000000005000000000000400000504842000000005881200000000000000800000000c8104000000010c10000000000000060000000000000000000008410000000000c410400000000411010000025441200000000000000600000450022000000050484200000000000000600000514c8200000005250c200000000000000200000154802000000000109102000000000000000000000c41020000050109201
  | 6, 21 => 0x81101000000000e1010000000000004000000010910200000000c410200000450852000000000109101000000000000200000450c520000000000061010000000000002000000000000000000000000060000000000007000005050c20000000450c12000000000000006000000000000800000204412000000000000002000000000e10100000450c12000000000000000000000000000000000000000070000000109101000000000000500000000000020000000081101000000000000600000000000000000000002100
  | 6, 22 => 0x81100000002048020100000324c8200000000000000300000000c11010000000000004000000000000200000000c410200000000000020000000000001000000000000500000000c410200000000000010000000000000000000588420000000000000060000000000002000000000000400000000841010000000000007000000000000000000450812000000000000004000000010910200000450c12000000045085200000000000000100000000000040000000000005000000000000500000104402000000000000006
  | 6, 23 => 0x60000003802200000000001210000000000c41020000015480200000000010810000000000000060000000041101000000008010000000000000000000000000005000000000000200000000000070000000000001000000000000600000000000070000020480200000000000000400000000000000000000000007000000000e101000000000000200000254c42000000000000002000000000000400000000000040000051508200000000000000800000520c12000000000000004000000000a1000000000000007
  | 6, 24 => 0x1091020000000000001000000000000100000000000020000035500200000001540a20000000204802010000035085201000000000000500000314c4200000002148420000000000000060000000104100000003548420000000000c1100000000000000500000520c1200000003508520100000354802000000000000007000000000000600000450c5200000003044120000000304c020000000150022000000000000004000000000000000000000000010000010440200000000000000700000000000010000000000002
  | 6, 25 => 0x10910100000350852010000000006101000005048420000000000000050000000109101000000000000600000000000010000000000004000000008110000000314c42010000000109101000000000000600000001091020000035441200000000000000600000000c1101000002550420000000000061010000000000008000000000000200000104402010000000000000000000000000200000000000020000000000002000000000000500000000c11030000050484200000000000000500000000000020000000000002
  | 6, 26 => 0x10000000108100000000000000600000504842000000000000003000000000000500000000000050000000000003000000000e1010000045081200000000000000200000000801000000000000005000000000000400000000000040000000000003000000010910200000000c010200000450c1200000000000000700000450c920000000000000080000000000008000000008510100000058412000000020480200000000000000200000000000000000000000006000000540a200000000000000500000520c5200
  | 6, 27 => 0x109101000003548420000000450812000000000000005000000000000500000000021000000000000005000000000000400000000021010000000000008000002048020000000000000060000000000003000003550020000000000000020000000000000000000000000600000000000060000000109102000003550020000000000c9101000003044120100000314c4200000001548020000000000000030000035480200000002044120000000314c42010000000000004000000000000400000354802000000010440200
  | 6, 28 => 0x40000000000006000000000000400000000000040000000000001000000000000000000450c520000000058c1200000005050820000000001081000000000084100000000000a10000000000000070000000000002000001548020000000504c42000000000081101000000000e10000000501092010000000000008000000000a10000000000841000000000000008000000000000500000000000030000015480200000000008010100000254c420000000450812000000000000002000000000000100000324c8201
  | 6, 29 => 0x20000000000002000000000a1000000000109102000000000000300000214842000000000000006000000010910100000000c1101000000000000400000000000050000000000002000000000000400000000061000000000000006000005010920100000504842000000021441200000000010910100000000c510100000324c8201000000000000200000000000070000000000005000000000a10000000000000020000000000004000000010910100000450c1200000000000000200000000000070000045081200
  | 6, 30 => 0x80000000041101000000000000400000000c1100000000000000300000000000020000000000008000000000000600000504842000000000000002000005108120000000001051010000021484200000000008510100000000000050000035480200000004548420000000000000020000000000006000005048420100000000851010000000000003000000008110100000000061000000000000002000005150c200000000000e10000000000121000000050109201000002544120000000000841010000000000000
  | 6, 31 => 0x6101000000000000300000000000060000000006100000000000000400000254c42000000000081101000000000000000000000021000000000000005000000010910100000000000040000050484200000003548520000000000c910000000450c1200000004500a2000000000000002000000000000600000000000030000000000004000000000000600000504842010000000000000000000000000200000000c11010000000109101000000000000700000354062000000000000005000000000000600000254c4200
  | 6, 32 => 0x1044020100000000000040000000000006000001500e200000004548420100000000021000000035085200000000000000400000355002000000000000006000000480a20000000000000070000035440201000000000000600000000000050000000000002000000008110100000314c42000000000000006000004508520000000354802000000000000000000000000000400000000000030000000000003000000000000200000254c4200000000000000100000431002000000000000004000000000000500000450c5200
  | 6, 33 => 0x3000000000000500000000021000000000000004000000000e10100000000c5100000000000000400000000000040000021484200000000000000700000000000070000000109101000000000000200000000000030000000000006000000004010000000000000050000000000004000000000000400000000000000000000000004000001044020000000450c520000000504c4200000004500a2000000000085101000002504120000000001091010000050484201000004508120000000450c52000000000000001
  | 6, 34 => 0x200000000000020000000000003000000000000200000354842000000000000002000000000000600000214842000000000000004000001548020100000454c82010000000000008000000000000400000154802000000000000005000000000210100000000000030000000000007000001044020100000454c420100000000c510100000510c1200000000000000700000000000050000025006200000000008510100000254c420000000000000020000000085100000000000000300000000000020000000000004
  | 6, 35 => 0x10000005841200000000000000500000000000040000000000004000002148420000000354842000000000000005000000000000600000000000030000000084100000000000610100000324c8200000000000a10000000000000080000000000005000000000000600000000000010000000000001000004548420100000000061010000000000004000002148420100000354412000000035085200000005048420000000450c120000000000000000000000000005000000000610000000000000050000000000000
  | 6, 36 => 0x8000000000a10000000000021000000000000005000000000000200000000000000000021484201000000000000700000000c9100000004500a20000000000c11010000010440200000000000000000000000c9100000003548020000000454842010000000000008000000000e1010000000000004000000000000800000000000040000025002200000000010910200000504c420100000350852010000000000004000000000000200000000000070000000000005000003548420000000454c82010000000000003
  | 6, 37 => 0x100000254c420000000000000040000000041100000000004110100000000c810000000504842000000000000004000000000000600000000000070000000000003000000000000800000504c4201000000000000400000000c410000000001091020000035485200000000010c100000000000000600000001051010000002806200000000000000000000000000070000000000008000000010910100000450c120000000001091020000000000007000000000000500000000c910100000000000020000035500200
  | 6, 38 => 0x85101000000540620000000000c510100000000000070000000000000000000004110000000000000020000000081101000000000000800000000c410000000450c5200000000000a10000000000401000000000105101000000000000400000000801010000000000004000002144120000000000c110100000001091010000000000004000000000000600000000c1101000000000000400000000c4102000000000000100000324c820000000000000000000000000004000000000000400000254c420100000000c9101
  | 6, 39 => 0x45085200000000010910100000000061000000000000002000003550420000000000c4104000000000000400000000000030000000000004000000000000600000000000050000045041200000000008110300000000000020000000000003000000008510000000000000020000000109102000000000000700000000000030000000000005000000000000000000214842000000000000000000000000000000000000000070000050504200000000000000300000000811010000000109101000000000000500000000c5100
  | 6, 40 => 0x851000000000000006000000000000400000000c410100000504842000000000000005000000000000800000000000060000000000002000000380a20000000450c1200000000000000200000424812010000000000007000003550020000000000000040000000109102000000000000100000314c42000000000000004000000000000400000000000060000000000006000003548020000000304412000000000109102000000000000200000000c51010000000105101000004548420000000000000040000000000004
  | 6, 41 => 0x354802010000000000000000000000000500000354842010000045084200000000000000700000001091020000035085200000000000210100000450c12000000000000003000000000000000000000c410400000354842000000045402201000000000000000000000000020000000000002000000480e20000000000000040000000000001000000000e101000001500220000000214412000000000000002000002048020000000000000000000000109101000000000000100000000000050000000000005
  | 6, 42 => 0xe1010000035085200000004508520000000304c0201000001044020000000355002000000000084100000000000000400000324c820100000314c4200000000000a1010000000000001000000008110000000001091010000000000006000000000000500000354802000000000000002000000000e10000000000c1101000000010810000000000000050000000000004000000000210100000314c4201000000000e10000000204802010000000081101000000010510100000000c110100000520c520000000504c4200
  | 6, 43 => 0xe101000000010510100000000c81040000000081103000000000000800000000c1101000000000a10100000000c910100000314c4201000000000210100000000851010000000000007000000000a10100000354802010000000000006000000000000700000504c4200000000000000500000000000060000000000006000000010510100000450812000000020480201000003550420000000000000000000000000000000000000000300000510c9200000000000000400000000000030000000000005000000010c100
  | 6, 44 => 0x10510100000000c41040000000000006000000000210100000324c82000000005406200000000000000300000000000020000000080100000000000000200000000000060000000000002000000000000200000000c010200000000000030000000000002000000000000600000000c8100000000000000200000000000000000000000006000000000a10000000000000000000000006101000000000000000000450062000000000000002000000000000500000000c8100000000000000500000000000010000000006101
  | 6, 45 => 0x50000000109102000000000000600000000000020000000085101000000000000200000000000060000000000008000000000000400000324c8200000000000000000000000000040000000000005000000000e1010000000085101000000000000000000000000000000000041101000000004110000000354802000000000000006000000008410000000000000030000000000008000002148420000000354402000000015480200000000000000400000000c1101000000000000800000000000040000032485200
  | 6, 46 => 0x100000314c4200000000000000400000000000060000000109101000000000000200000000c110100000000000020000000000002000000000000100000450852000000000000008000000000000500000000c1101000000380620000000000c110100000000000070000000000002000003550020000000000000000000045081200000004548020100000000000030000000000006000000000000300000314c4200000002550020000000504c42000000000000003000004500220000000354802000000035484200
  | 6, 47 => 0x2000005048420000000000000020000000081101000000000000200000000c810400000000000060000000000005000004548020100000000000070000000000000000000000000500000000000080000000000008000000380a200000000000000700000000000020000000000004000000000000700000450c520000000000c11010000000012100000001548020000000000000080000000000006000000000000100000000000080000000000004000000000e101000001548020100000001041000000000000004
  | 6, 48 => 0x204802010000000000005000000000000000000254062000000000000008000003508520000000430c9200000000000000000000000000000000000000004000000000000400000000000020000000000002000000000000400000304c02000000000006101000004248120100000000000020000000000005000000480e20000000254062000000000000002000000000000700000254c4200000000000000400000000000010000000000003000000000000700000000000010000000000005000000000000700000254c0200
  | 6, 49 => 0xc110100000000000050000000000000000003550820000000000c81040000000109101000000000000500000454c4201000000010910100000000021000000000000005000000000000000000000c0100000000000000200000310c120000000304412000000030441200000000000000100000450c520000000450852000000000000003000000000000400000304412000000000000001000000000000200000450c520000000000c4102000000000000200000431002000000000000005000000010910200000000c4100
  | 6, 50 => 0xc1101000000000a10000000000851010000021484200000000000000100000000000060000000000006000000004110100000504c420000000000c8100000004508520000000254c4200000002500220000000000c41040000000000001000005048420000000000000020000000000002000000000000700000000801000000000084100000003504120000000000000020000000100100000000000000200000424812010000045085200000000000000700000000c4101000000000000400000000000050000000000005
  | 6, 51 => 0x80000000000007000000588520000000324c820100000000000060000025441200000000000000700000324c82000000000012100000000000000300000000c41000000000000004000003548020100000450c5200000000000000400000000000020000000000003000000000000600000000c510100000000000060000000000004000000000000200000304c020000000000c910100000510812000000045402201000004508120000000000000050000043104200000003540a20000000000000080000000000007
  | 6, 52 => 0x450c5200000000010810000000000c11010000045484200000000000000600000000000070000000000006000000000000600000000000080000000000001000000000000400000000000040000000000002000000000000300000504c4200000000004110100000000000010000000000007000000000000400000000811010000000000007000003548420000000501092010000000109101000000000000100000000c11000000000000001000000000000500000504842010000000002100000001548020000000058c5200
  | 6, 53 => 0x3000000000000500000000000040000000000001000000000000000000504c4200000000000000400000000c01020000000081101000000000000600000000c010200000000000050000000000000000005010920100000504c4200000000000000400000001091020000000000001000000000000400000000000060000000109102000000000000300000000c4104000005108120000000038062000000000000006000000000000700000000811000000000000005000000000000200000000000040000000000005
  | 6, 54 => 0x500000000000010000000000003000000000000100000204802000000000000004000001540a200000005048420100000000c01000000000000005000002148420000000154c0200000000000000800000354842000000000000004000004500220000000000000060000035484200000000000000300000000000070000045480201000000000a101000000000000400000000c410100000000000040000000000000000003544020000000000000010000000000005000000000610100000000000070000000000006
  | 6, 55 => 0x4000005048420100000520c5200000000000000100000000c41000000000000004000000000000400000000000050000000000003000000008110100000504c8200000003500a2000000025440200000000000000700000000411010000000000001000003548420000000314c420000000000000070000000000004000000000000700000000000010000000000005000000000000500000254c420000000254c4200000000000000200000000000070000000000004000004500e200000004508420000000000c8104
  | 6, 56 => 0xa1010000010440200000000008110000000058c9200000000000000500000350852000000000000006000000008110000000000000060000000002100000000000000400000254c02000000000000005000000000000000000000000020000005904200000000000000200000058c120000000000000020000000000000000000590820000000000000070000000041101000000000000200000000061000000015480200000000008510100000000c410200000450c5200000000000000500000450852000000021484201
  | 6, 57 => 0xe100000000000000400000000c1101000002048020000000510c92000000000000005000000000000500000000c4104000000010410000000254402000000000000004000000000000800000000000040000000000002000000000000400000314c420000000104402010000000000002000000000000400000000c91010000000000007000000000000500000204802000000000000004000002500e2000000000000008000005050c200000000000000800000000c9101000000000000400000000000060000035481200
  | 6, 58 => 0x200000000000050000020480200000004548420100000000c81000000021484201000000000000300000000c410200000354402000000000000002000000000000200000000000060000000000005000000000000700000304c020000000000000040000035481200000000000000200000000c110100000310c120000000000c410400000000c81040000002802200000000000000200000000000040000000000003000000000000700000314c420000000454c820100000000c910000000421042000000000000000
  | 6, 59 => 0x504c4201000000500e200000000000000400000254c42000000045081200000000000210000000504c420000000000000020000035500200000000000000600000000000020000000085100000000000000000000000000020000000109101000000000000500000350852000000035085200000003548420000000000000050000000000005000003548420000000000c5101000000000000700000000c11010000004802200000000010910100000000000040000000081101000000000000400000000000060000000081101
  | 6, 60 => 0x450c520000000000000050000000108100000000000000800000510c9200000000000000200000000000060000000109101000000000000800000000000030000000000006000000000000400000000c41040000000108100000000000000400000000c510000000000c110100000000c5101000000000000000000001091010000000000005000005050c2000000021484201000002550020000000154802000000000000002000000000000800000000000050000000000007000000000610100000000000040000000002100
  | 6, 61 => 0x35500200000000540a200000000000000100000000000070000035085200000000000000400000000c110100000000000040000000041103000000000000600000000000080000000041101000000000a1010000000000002000002544020100000454c42010000000000007000000000000200000000000040000000000005000003500a20000000000000060000000000002000000000000500000000000040000000000002000000010510100000000000050000000000007000000000000200000000851000000000000002
  | 6, 62 => 0x40000000000007000000000000100000000811010000035484200000000000000500000001091020000045081200000000000000200000324c8200000000000000400000058812000000000000002000000010910100000154802000000000000004000005048420000000000000060000000002101000000000e100000000000a100000000000000300000058842000000000000006000001548020100000000c110100000000c910100000000c4100000000000a100000000010910100000515082000000020480200
  | 6, 63 => 0x35480200000000000000200000000000050000000000005000003548420000000000061000000000000001000001044020000000000000040000000000008000000000610000000254c42000000000000000000000000e10000000504c420000000000000070000015480201000000000a101000001548020000000000811000000000000006000000000000000000454c420100000000c9101000000000000800000000000020000000006101000003540a2000000000080100000000000000700000000841000000000000003
  | 6, 64 => 0x851010000000002101000000000000200000450c520000000058c5200000000000000700000324c820000000000000060000000085101000000000000600000000c1101000000000000400000310c1200000000010c100000000008410000000000000040000001802200000000000000400000000c510100000000000040000000000007000000000a101000000000a101000000000000500000000000080000000109101000000000000100000000000000000045081200000000000000400000000000000000000000007
  | 6, 65 => 0x8000000590820000000000000020000020441200000000000000200000254c42010000000109101000000000000400000000000050000020480200000000000a1010000000109101000000000000100000000c110100000000000060000000000002000000000000200000304c0200000000000000500000000021000000000000007000000000210100000504842000000000080100000002500220000000000000000000000000003000000000a101000000000000300000000c910100000001081000000000000004
  | 6, 66 => 0x45081200000000000000200000000c51010000000109101000003508520000000000c110100000000c1101000000000000000000314c420100000000c010200000000000080000015480200000000380a2000000000006101000003548020100000000000070000000000006000000000000400000000000050000000000004000005050420000000254c420000000204802000000000000007000000000a1000000000000002000000000000400000028022000000050085200000000000000700000000000060000045081200
  | 6, 67 => 0x304c0200000000000000600000000000000000045085200000003548020100000000000050000045085200000000000000800000000c51010000000000004000000000000600000001091010000000109101000000000000400000254c420100000000c8104000000000000200000450c5200000004508120000000000000020000000000002000003508520000000000000080000000000004000001044020000000000411010000045081200000000000000600000000000030000021484200000001500a2000000004802200
  | 6, 68 => 0x450c9200000000000000300000000000060000000080100000000000000100000424812010000000000001000000000000600000450c1200000000000000800000000c51010000000000001000000000000100000504c820000000000000070000000000004000000000000000000000000070000000000005000000008010000000000000060000000000006000003548420000000000000010000000000003000000000a10100000000c110100000000000000000000000004000000008510100000314c42010000000000000
  | 6, 69 => 0x254c4200000000000000100000000c1101000004508520000000000000030000000000006000004508120000000354842010000000006101000000000000600000000c1101000002148420000000058c9200000004540220100000000000050000025041200000000000000400000304c020000000000000040000000000007000000000000300000000000060000035484200000000000000600000154c020000000000000020000000000008000000008110300000514c8200000000000000600000000000070000000000005
  | 6, 70 => 0x400000450c520000000000c010200000000000020000050508200000004548020100000505042000000025440200000000000000400000324c820000000154c0200000002148420100000450812000000000000001000000000000200000000c9101000000010510100000000851010000000109101000003548420000000000000010000000000004000000008110100000450812000000000000004000000000000700000324c820000000254c4200000000000000800000000c410000000000000070000000000002
  | 6, 71 => 0x10000000000002000000180220000000254c020000000350062000000000000003000000000000000000000000060000000041100000000000000200000000c910100000000c91010000000000005000000000000200000000000070000035484201000000000a101000000000000100000000000010000015002200000000000000000000505082000000045402201000000000000400000450c120000000504c420000000000000070000000000002000000000000400000324c120000000450812000000000000002
  | 6, 72 => 0x2101000003550020000000000c910100000000000050000005908200000000000000700000000000010000000000003000000000000500000000000040000015500200000002544120000000355082000000000000002000000000000400000000000050000000000004000000010910200000000c11010000050484200000000000000400000350852000000020480201000005150c20000000001081000000045480201000000000000000000000000070000000000001000004210020000000204802000000000000004
  | 6, 73 => 0x3548020000000000000020000000000001000000004110100000304c0201000000010910100000000000040000000000002000000590420000000204412000000000000005000000000000100000250062000000050484200000000000000300000000000020000000000001000000000000800000504c42000000000000003000000000000300000000000020000000109102000000000610100000424812010000050484200000000000000100000000000060000000002101000000000000200000000000020000000000002
  | 6, 74 => 0x40000000000001000000000000800000000000040000045085200000001044020000000000000020000045484201000000000000400000000c010200000000c1101000004248120100000000000030000000000006000000000000300000000c510100000000c11010000000085101000000000610100000000000060000035500200000000588120000000314c42000000000000001000000000000400000354842000000000081100000003508120000000000c5101000000000000700000000000080000051481200
  | 6, 75 => 0x5000000000000500000000000000000000000004000000000000200000000000020000000085101000000000000700000000c51010000000000004000000000000000000350852000000045006200000000000000200000000000080000000000004000000000000100000000c51010000000000005000000008510100000000000060000000104100000001044020000000450c120000000001091010000000000003000000000a10100000001091010000000000007000000000000100000000000020000000000004
  | 6, 76 => 0x400000501092010000045081200000000000000500000000000030000035500200000000000000500000314c42000000000002100000000000000100000000000050000000000006000000000000200000001091010000000000002000004500e200000003548020000000214842000000000000000000000000000400000000000040000000000004000000010910200000000000020000000000001000000000210100000000000060000035406200000004504120000000000c91010000000002101
  | 6, 77 => 0x851010000010440201000002148420000000505082000000000084101000000000000700000000c11010000035085200000000000000600000000000040000000000005000000000610100000000811010000000000001000000000000800000214842000000000000004000000000000700000000811010000000000002000000000000400000350852010000000109101
  | 7, 0 => 0x8410000000000061000000000000004000000000000400000000c4100000000000000200000000000060000000002100000000004110000000000061000000000000005000000000610000000000c910100000000c4101000000000000600000000000060000000000005000000008510100000000c41000000000000002000000000a100000000010c10000000000841000000000000002000000000e100000000000a100000000000000200000000000000000000000001000000008110000000000851000000000000001
  | 7, 1 => 0x81101000000000000200000000c910000000000c11010000000002100000000010810000000000c11000000000000004000000000e10000000000c9100000000000a10000000000000020000000000002000000004110000000000121000000000000004000000000210000000000c9100000000000000100000000000020000000000002000000010c100000000000a10100000000811000000000000004000000000e1000000000108100000000000a1000000000006100000000010c1000000000000002
  | 7, 2 => 0x100000000000020000000000004000000010810000000000c110000000000c1100000000004010000000000c51000000000000000000000008110100000000c01010000000000001000000004010000000000851000000000000004000000000000400000000061000000000002100000000000000300000000c5100000000000e1000000000000001000000000a1000000000040100000000008110000000000000010000000100100000000000000700000000c0101000000008010000000000021000000000002100
  | 7, 3 => 0x8410000000000c8101000000000210100000000061010000000081100000000000000400000001081000000000000001000000004110000000000061000000000000001000000000000100000000c1100000000000e100000000000e100000000008010000000000000010000000000001000000000a10000000000021000000000080100000000000210100000000000070000000006100000000008510000000000c410000000000000060000000000002000000000000100000000c510000000000000020000000085100
  | 7, 4 => 0x20000000104100000000000610000000000c410000000000021000000000000004000000000e1010000000006101000000000a10100000000000040000000000005000000000000200000000021010000000041100000000010c10000000000c91010000000002100000000008410000000000c810100000000c91000000000006100000000010c1000000000084100000000000e1000000000000001000000000a100000000010410000000000000010000000006100000000000e101000000000a101000000010c100
  | 7, 5 => 0x20000000012100000000000000200000000000040000000080100000000010010000000000000020000000000004000000000e100000000000a10000000000c9100000000000e101000000010c100000000000a1000000000000000000000008510100000000000050000000000002000000004110000000000851000000000100100000000000610100000000c5101000000000000100000000c510000000000401010000000000001000000000000100000000000000000000040100000000010810000000000c0100
  | 7, 6 => 0x5000000010410000000000c010000000000000010000000000005000000008410100000000c8100000000010c1000000000000002000000008410000000000000010000000000004000000000a1000000000109101000000010010000000000000050000000000004000000008010000000000c4100000000000610000000000061010000000108100000000000000000000000c110000000000401000000000080100000000000000000000000c0100000000000e101000000000000100000000000040000000000002
  | 7, 7 => 0x84100000000000000400000000021010000000002100000000004110100000000000040000000000001000000000610000000000c8100000000000000200000000000000000000041100000000000000000000000c4101000000000000700000000000040000000041101000000000610000000000851000000000000002000000000a1000000000000004000000000000400000000c4100000000000000200000000c1100000000000000100000000000040000000000001000000001210000000000c41010000000041100
  | 7, 8 => 0xe10000000000c01000000000000004000000004110000000000c0100000000008110000000001001000000000084100000000000000400000000000000000000000007000000000000200000000c110000000000c4100000000000610000000000c0100000000000610000000000c8100000000001210000000000801010000000000002000000000210000000000000000000000080100000000010410000000000c9100000000000a10000000000c4100000000000e10000000000000050000000000002000000000a100
  | 7, 9 => 0x50000000000004000000000000200000000c510000000000c51010000000000001000000000000500000000000060000000040100000000000a1000000000000002000000010410000000000121000000000000005000000010c10000000000c1100000000010410000000000811010000000000004000000008510000000000000020000000040100000000000e1000000000100100000000000210000000000c510000000000c910000000000000020000000000001000000010010000000000000020000000040100
  | 7, 10 => 0xc010100000000c91000000000000004000000008110100000000c010000000000411000000000000005000000000000200000000021000000000000001000000000000200000000c9100000000010410000000000021000000000000000000000010c100000000008410000000000c810000000001041000000000000002000000000000100000000c8100000000000000400000000c110000000000000010000000000006000000000610000000000c11010000000012100000000008510000000000c81000000000000000
  | 7, 11 => 0xe10000000000000010000000000004000000000a10000000000061000000000085100000000000000200000001041000000000000002000000000a101000000000000200000000c51000000000000002000000000000000000000c1100000000000e1000000000000002000000000000600000000000050000000040100000000000a1010000000081101000000000000400000000121000000000000001000000000000100000000000040000000100100000000010c1000000000084100000000000a100
  | 7, 12 => 0x10c1000000000000004000000000000500000000841000000000000003000000000e10100000000c11010000000000001000000000a1010000000040101000000000000400000000c810100000000c8101000000004110000000000c8100000000000000000000000000040000000002100000000000210100000000c9100000000000000400000000c11000000000000001000000000a101000000008010000000000c1101000000001210000000000000020000000000004000000000e10000000000000060000000002101
  | 7, 13 => 0x4000000000610000000000021000000000006101000000000000100000000c510000000000c91000000000006101000000000e100000000000000200000000c110000000000811000000000085100000000000000500000000851000000000006101000000000610000000000000060000000109101000000000e10100000000c51000000000000004000000000a101000000000000500000000061000000000040100000000000a10000000000000040000000000001000000000000200000000021000000000080100
  | 7, 14 => 0x10810000000000c0100000000000000400000001001000000000000000000000000000200000000851000000000080100000000000a1000000000002100000000000000000000000c51000000000081100000000010c1000000000002100000000008410000000000c9100000000000000100000000401000000000000003000000000210100000000c910100000000061010000000000004000000000e1010000000000004000000000e1010000000000004000000000e1000000000000004000000000000700000000c0101
  | 7, 15 => 0x210000000000c910000000000c5101000000000000600000000c010000000000401010000000000004000000000a1000000000000002000000000210000000000000040000000000001000000008510000000000c4101000000000e1000000000000002000000000a10000000000c51000000000085101000000000000400000000000000000000040100000000000610000000000c5101000000000610100000000811000000000100100000000004010100000000021010000000000005000000000000200000000c9101
  | 7, 16 => 0x4010000000000841010000000041100000000004110100000000000010000000000005000000000e10000000000c810000000000000070000000080100000000000a100000000008410000000000000010000000000004000000000000200000000000070000000000006000000010910100000000000020000000000004000000008110000000000061000000000041101000000010c1000000000084100000000000000200000000c410100000000000010000000100100000000000000200000000851010000000108100
  | 7, 17 => 0xe100000000010c10000000000841000000000000004000000000000400000000801000000000000002000000010010000000000000010000000081100000000000000200000000c010000000000000020000000081100000000000000400000000c8100000000000000100000000841010000000000007000000008110000000000061000000000000002000000000000400000000851000000000109101000000010c10000000000c510000000000841000000000000002000000000000100000000000010000000000001
  | 7, 18 => 0x85100000000000000200000000c8100000000000000100000000000020000000080101000000000e100000000000e10000000000000010000000108100000000000a10000000000c010000000000000050000000108100000000004110000000000000020000000000004000000000000700000000021000000000000000000000008010000000000000020000000000002000000000210000000000000020000000108100000000000000200000000801010000000000004000000000000100000000c41000000000002100
  | 7, 19 => 0x100000000000010000000000004000000000000400000000c910000000000c51000000000000001000000000610000000000000010000000104100000000008010000000000061000000000000002000000008110100000000411000000000081100000000000610000000000000010000000080100000000000e100000000010010000000000000010000000000007000000000a10000000000000040000000000004000000000e100000000000a101000000000a10000000000c4100000000010c10000000000c0100
  | 7, 20 => 0xa10000000000000050000000000001000000000000100000000c010000000000c510000000000000040000000000002000000000000400000000c010100000000000010000000000002000000010810000000000c1101000000000a10100000000000020000000002101000000010010000000000000000000000000006000000000000200000000021000000000000002000000000e10000000000c81000000000000002000000000a1000000000000004000000000000400000000c01000000000000001000000000a101
  | 7, 21 => 0x100000000c11010000000081100000000000e100000000004110000000000c810000000000061010000000000001000000000610000000000c410000000000c81000000000000002000000000000100000000c4100000000000000200000000000020000000000000000000010410000000000c0101000000000000100000000c4100000000000e101000000000e10100000000000010000000000002000000000a101000000000e100000000010010000000000801000000000000004000000010810000000000c1101
  | 7, 22 => 0x411010000000012100000000000000300000000000040000000012100000000000a1000000000000002000000000210100000000c8101000000000000400000000c91010000000000004000000000a10000000000061010000000000001000000000000200000000000010000000000004000000000000200000000000040000000100100000000008110000000000c8100000000010410000000000c8101000000004110000000000c0100000000000610100000000000040000000041100000000000000400000000c8100
  | 7, 23 => 0xc110000000000851010000000000006000000000000200000000c51010000000000004000000000e100000000001210000000000811000000000040101000000008410100000000021010000000000002000000000e10100000000c4101000000000210000000000c4100000000008510100000000c8100000000000a10000000000c51010000000000004000000004010100000000c01000000000002101000000000e100000000000e10000000000c9101000000000000200000000c110000000000811000000000000007
  | 7, 24 => 0x84101000000000e1000000000108100000000000000200000001041000000000006100000000010910100000000000040000000041100000000000e100000000010410000000000021000000000000001000000000a10000000000841010000000000000000000000000400000000061000000000000002000000000000100000001041000000000080101000000010910100000000c41000000000108100000000000e101000000004110100000000000020000000000006000000004110000000000000060000000002100
  | 7, 25 => 0xc91000000000085100000000000610000000000000010000000108100000000000000200000000c510000000000000070000000040100000000000a100000000000000200000000000010000000000001000000000e100000000000610000000000000020000000081100000000000a1000000000000004000000000000400000000000060000000000002000000000000200000000061000000000000002000000000000400000000000060000000002100000000000000400000000c910000000000000010000000000002
  | 7, 26 => 0xc1100000000010410000000000c51000000000000002000000008010100000000000010000000000002000000004010000000000c110000000001081000000000000004000000000000500000000c1100000000000000200000000401000000000012100000000000210000000000121000000000080101000000000000000000000c110000000000c41000000000000000000000000a10000000000021000000000000001000000000000400000000021000000000000002000000000a1000000000012100
  | 8, 0 => 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000010000000000000000000000000100000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_5 roots_5 8 s ws hint
  | 1 => checkCutEntry dom_11 roots_11 7 s ws hint
  | 2 => checkCutEntry dom_12 roots_12 6 s ws hint
  | 3 => checkCutEntry dom_14 roots_14 6 s ws hint
  | 4 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 5 => checkCutEntry dom_16 roots_16 5 s ws hint
  | 6 => checkCutEntry dom_18 roots_18 5 s ws hint
  | 7 => checkCutEntry dom_19 roots_19 5 s ws hint
  | 8 => checkCutEntry dom_21 roots_21 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_22 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_22 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_22 == dom_22) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_22 goalM u ys) : RunD dom_22 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_22 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 2 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := z2_0
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
theorem z4_72 : ∀ i, 72 ≤ i → i < 80 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_80 : ∀ i, 80 ≤ i → i < 88 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_88 : ∀ i, 88 ≤ i → i < 96 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_96 : ∀ i, 96 ≤ i → i < 104 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_104 : ∀ i, 104 ≤ i → i < 112 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_112 : ∀ i, 112 ≤ i → i < 120 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_120 : ∀ i, 120 ≤ i → i < 128 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_128 : ∀ i, 128 ≤ i → i < 135 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 128 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 135 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (range_split z4_48 (range_split z4_56 (range_split z4_64 (range_split z4_72 (range_split z4_80 (range_split z4_88 (range_split z4_96 (range_split z4_104 (range_split z4_112 (range_split z4_120 (z4_128))))))))))))))))
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
theorem z5_232 : ∀ i, 232 ≤ i → i < 240 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_240 : ∀ i, 240 ≤ i → i < 248 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_248 : ∀ i, 248 ≤ i → i < 256 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_256 : ∀ i, 256 ≤ i → i < 264 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_264 : ∀ i, 264 ≤ i → i < 272 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_272 : ∀ i, 272 ≤ i → i < 280 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_280 : ∀ i, 280 ≤ i → i < 288 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_288 : ∀ i, 288 ≤ i → i < 296 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_296 : ∀ i, 296 ≤ i → i < 304 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_304 : ∀ i, 304 ≤ i → i < 312 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_312 : ∀ i, 312 ≤ i → i < 320 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_320 : ∀ i, 320 ≤ i → i < 328 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_328 : ∀ i, 328 ≤ i → i < 336 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_336 : ∀ i, 336 ≤ i → i < 344 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_344 : ∀ i, 344 ≤ i → i < 352 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_352 : ∀ i, 352 ≤ i → i < 360 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_360 : ∀ i, 360 ≤ i → i < 368 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_368 : ∀ i, 368 ≤ i → i < 376 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_376 : ∀ i, 376 ≤ i → i < 384 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_384 : ∀ i, 384 ≤ i → i < 392 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_392 : ∀ i, 392 ≤ i → i < 400 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_400 : ∀ i, 400 ≤ i → i < 408 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_408 : ∀ i, 408 ≤ i → i < 416 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_416 : ∀ i, 416 ≤ i → i < 424 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_424 : ∀ i, 424 ≤ i → i < 432 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_432 : ∀ i, 432 ≤ i → i < 440 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_440 : ∀ i, 440 ≤ i → i < 448 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_448 : ∀ i, 448 ≤ i → i < 456 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_456 : ∀ i, 456 ≤ i → i < 464 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_464 : ∀ i, 464 ≤ i → i < 472 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_472 : ∀ i, 472 ≤ i → i < 480 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_480 : ∀ i, 480 ≤ i → i < 488 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_488 : ∀ i, 488 ≤ i → i < 496 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_496 : ∀ i, 496 ≤ i → i < 504 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_504 : ∀ i, 504 ≤ i → i < 512 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_512 : ∀ i, 512 ≤ i → i < 520 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_520 : ∀ i, 520 ≤ i → i < 528 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 520 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_528 : ∀ i, 528 ≤ i → i < 536 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_536 : ∀ i, 536 ≤ i → i < 544 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 536 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_544 : ∀ i, 544 ≤ i → i < 546 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 544 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 546 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (range_split z5_200 (range_split z5_208 (range_split z5_216 (range_split z5_224 (range_split z5_232 (range_split z5_240 (range_split z5_248 (range_split z5_256 (range_split z5_264 (range_split z5_272 (range_split z5_280 (range_split z5_288 (range_split z5_296 (range_split z5_304 (range_split z5_312 (range_split z5_320 (range_split z5_328 (range_split z5_336 (range_split z5_344 (range_split z5_352 (range_split z5_360 (range_split z5_368 (range_split z5_376 (range_split z5_384 (range_split z5_392 (range_split z5_400 (range_split z5_408 (range_split z5_416 (range_split z5_424 (range_split z5_432 (range_split z5_440 (range_split z5_448 (range_split z5_456 (range_split z5_464 (range_split z5_472 (range_split z5_480 (range_split z5_488 (range_split z5_496 (range_split z5_504 (range_split z5_512 (range_split z5_520 (range_split z5_528 (range_split z5_536 (z5_544))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z6_376 : ∀ i, 376 ≤ i → i < 384 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_384 : ∀ i, 384 ≤ i → i < 392 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_392 : ∀ i, 392 ≤ i → i < 400 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_400 : ∀ i, 400 ≤ i → i < 408 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_408 : ∀ i, 408 ≤ i → i < 416 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_416 : ∀ i, 416 ≤ i → i < 424 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_424 : ∀ i, 424 ≤ i → i < 432 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_432 : ∀ i, 432 ≤ i → i < 440 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_440 : ∀ i, 440 ≤ i → i < 448 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 440 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_448 : ∀ i, 448 ≤ i → i < 456 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_456 : ∀ i, 456 ≤ i → i < 464 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 456 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_464 : ∀ i, 464 ≤ i → i < 472 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_472 : ∀ i, 472 ≤ i → i < 480 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 472 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_480 : ∀ i, 480 ≤ i → i < 488 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_488 : ∀ i, 488 ≤ i → i < 496 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 488 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_496 : ∀ i, 496 ≤ i → i < 504 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_504 : ∀ i, 504 ≤ i → i < 512 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 504 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_512 : ∀ i, 512 ≤ i → i < 520 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_520 : ∀ i, 520 ≤ i → i < 528 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 520 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_528 : ∀ i, 528 ≤ i → i < 536 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_536 : ∀ i, 536 ≤ i → i < 544 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 536 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_544 : ∀ i, 544 ≤ i → i < 552 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_552 : ∀ i, 552 ≤ i → i < 560 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 552 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_560 : ∀ i, 560 ≤ i → i < 568 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_568 : ∀ i, 568 ≤ i → i < 576 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 568 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_576 : ∀ i, 576 ≤ i → i < 584 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_584 : ∀ i, 584 ≤ i → i < 592 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 584 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_592 : ∀ i, 592 ≤ i → i < 600 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_600 : ∀ i, 600 ≤ i → i < 608 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 600 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_608 : ∀ i, 608 ≤ i → i < 616 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_616 : ∀ i, 616 ≤ i → i < 624 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 616 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_624 : ∀ i, 624 ≤ i → i < 632 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_632 : ∀ i, 632 ≤ i → i < 640 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 632 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_640 : ∀ i, 640 ≤ i → i < 648 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_648 : ∀ i, 648 ≤ i → i < 656 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 648 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_656 : ∀ i, 656 ≤ i → i < 664 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_664 : ∀ i, 664 ≤ i → i < 672 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 664 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_672 : ∀ i, 672 ≤ i → i < 680 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_680 : ∀ i, 680 ≤ i → i < 688 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 680 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_688 : ∀ i, 688 ≤ i → i < 696 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 688 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_696 : ∀ i, 696 ≤ i → i < 704 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 696 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_704 : ∀ i, 704 ≤ i → i < 712 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 704 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_712 : ∀ i, 712 ≤ i → i < 720 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 712 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_720 : ∀ i, 720 ≤ i → i < 728 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 720 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_728 : ∀ i, 728 ≤ i → i < 736 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 728 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_736 : ∀ i, 736 ≤ i → i < 744 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 736 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_744 : ∀ i, 744 ≤ i → i < 752 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 744 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_752 : ∀ i, 752 ≤ i → i < 760 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 752 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_760 : ∀ i, 760 ≤ i → i < 768 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 760 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_768 : ∀ i, 768 ≤ i → i < 776 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 768 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_776 : ∀ i, 776 ≤ i → i < 784 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 776 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_784 : ∀ i, 784 ≤ i → i < 792 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 784 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_792 : ∀ i, 792 ≤ i → i < 800 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 792 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_800 : ∀ i, 800 ≤ i → i < 808 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 800 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_808 : ∀ i, 808 ≤ i → i < 816 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 808 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_816 : ∀ i, 816 ≤ i → i < 824 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 816 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_824 : ∀ i, 824 ≤ i → i < 832 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 824 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_832 : ∀ i, 832 ≤ i → i < 840 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 832 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_840 : ∀ i, 840 ≤ i → i < 848 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 840 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_848 : ∀ i, 848 ≤ i → i < 856 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 848 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_856 : ∀ i, 856 ≤ i → i < 864 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 856 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_864 : ∀ i, 864 ≤ i → i < 872 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 864 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_872 : ∀ i, 872 ≤ i → i < 880 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 872 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_880 : ∀ i, 880 ≤ i → i < 888 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 880 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_888 : ∀ i, 888 ≤ i → i < 896 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 888 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_896 : ∀ i, 896 ≤ i → i < 904 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 896 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_904 : ∀ i, 904 ≤ i → i < 912 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 904 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_912 : ∀ i, 912 ≤ i → i < 920 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 912 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_920 : ∀ i, 920 ≤ i → i < 928 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 920 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_928 : ∀ i, 928 ≤ i → i < 936 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 928 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_936 : ∀ i, 936 ≤ i → i < 944 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 936 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_944 : ∀ i, 944 ≤ i → i < 952 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 944 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_952 : ∀ i, 952 ≤ i → i < 960 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 952 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_960 : ∀ i, 960 ≤ i → i < 968 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 960 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_968 : ∀ i, 968 ≤ i → i < 976 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 968 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_976 : ∀ i, 976 ≤ i → i < 984 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 976 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_984 : ∀ i, 984 ≤ i → i < 986 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 984 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 986 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (range_split z6_376 (range_split z6_384 (range_split z6_392 (range_split z6_400 (range_split z6_408 (range_split z6_416 (range_split z6_424 (range_split z6_432 (range_split z6_440 (range_split z6_448 (range_split z6_456 (range_split z6_464 (range_split z6_472 (range_split z6_480 (range_split z6_488 (range_split z6_496 (range_split z6_504 (range_split z6_512 (range_split z6_520 (range_split z6_528 (range_split z6_536 (range_split z6_544 (range_split z6_552 (range_split z6_560 (range_split z6_568 (range_split z6_576 (range_split z6_584 (range_split z6_592 (range_split z6_600 (range_split z6_608 (range_split z6_616 (range_split z6_624 (range_split z6_632 (range_split z6_640 (range_split z6_648 (range_split z6_656 (range_split z6_664 (range_split z6_672 (range_split z6_680 (range_split z6_688 (range_split z6_696 (range_split z6_704 (range_split z6_712 (range_split z6_720 (range_split z6_728 (range_split z6_736 (range_split z6_744 (range_split z6_752 (range_split z6_760 (range_split z6_768 (range_split z6_776 (range_split z6_784 (range_split z6_792 (range_split z6_800 (range_split z6_808 (range_split z6_816 (range_split z6_824 (range_split z6_832 (range_split z6_840 (range_split z6_848 (range_split z6_856 (range_split z6_864 (range_split z6_872 (range_split z6_880 (range_split z6_888 (range_split z6_896 (range_split z6_904 (range_split z6_912 (range_split z6_920 (range_split z6_928 (range_split z6_936 (range_split z6_944 (range_split z6_952 (range_split z6_960 (range_split z6_968 (range_split z6_976 (z6_984)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z7_200 : ∀ i, 200 ≤ i → i < 208 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_208 : ∀ i, 208 ≤ i → i < 216 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_216 : ∀ i, 216 ≤ i → i < 224 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_224 : ∀ i, 224 ≤ i → i < 232 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_232 : ∀ i, 232 ≤ i → i < 240 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 232 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_240 : ∀ i, 240 ≤ i → i < 248 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_248 : ∀ i, 248 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 248 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_256 : ∀ i, 256 ≤ i → i < 264 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_264 : ∀ i, 264 ≤ i → i < 272 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 264 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_272 : ∀ i, 272 ≤ i → i < 280 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_280 : ∀ i, 280 ≤ i → i < 288 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 280 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_288 : ∀ i, 288 ≤ i → i < 296 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_296 : ∀ i, 296 ≤ i → i < 304 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 296 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_304 : ∀ i, 304 ≤ i → i < 312 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_312 : ∀ i, 312 ≤ i → i < 320 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 312 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_320 : ∀ i, 320 ≤ i → i < 328 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_328 : ∀ i, 328 ≤ i → i < 336 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 328 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_336 : ∀ i, 336 ≤ i → i < 344 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_344 : ∀ i, 344 ≤ i → i < 352 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 344 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_352 : ∀ i, 352 ≤ i → i < 360 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_360 : ∀ i, 360 ≤ i → i < 368 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 360 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_368 : ∀ i, 368 ≤ i → i < 376 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_376 : ∀ i, 376 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 376 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_384 : ∀ i, 384 ≤ i → i < 392 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_392 : ∀ i, 392 ≤ i → i < 400 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 392 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_400 : ∀ i, 400 ≤ i → i < 408 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_408 : ∀ i, 408 ≤ i → i < 416 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 408 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_416 : ∀ i, 416 ≤ i → i < 424 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 416 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 424 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (range_split z7_208 (range_split z7_216 (range_split z7_224 (range_split z7_232 (range_split z7_240 (range_split z7_248 (range_split z7_256 (range_split z7_264 (range_split z7_272 (range_split z7_280 (range_split z7_288 (range_split z7_296 (range_split z7_304 (range_split z7_312 (range_split z7_320 (range_split z7_328 (range_split z7_336 (range_split z7_344 (range_split z7_352 (range_split z7_360 (range_split z7_368 (range_split z7_376 (range_split z7_384 (range_split z7_392 (range_split z7_400 (range_split z7_408 (z7_416))))))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_24 : ∀ i, 24 ≤ i → i < 26 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 24 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 26 → Z 8 i = true := range_split z8_0 (range_split z8_8 (range_split z8_16 (z8_24)))
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
  scr dom_22 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_22 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_22 roots_22 goal_22 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_22 goal_22 := by
    have h0 : isConstB dom_22 goal_22 = false := by decide +kernel
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

end S_22

theorem low_22 : Lower dom_22 roots_22 goal_22 10 := S_22.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_22_bits : ∀ r : Fin 64, roots_22.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_22_lt : ∀ r : Fin 64, dom_22.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_22 T)
    (hlow : Lower dom_22 roots_22 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_22, Avail mask256 roots_22 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_22 hfan 0 roots_22 roots_22 rfl hsup0
  set out := (execN C.gates roots_22).getD C.output 0
  have hout : out &&& dom_22 = T &&& dom_22 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_22_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_22 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_22_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_22).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_22)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_22.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_22 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_22).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_22 &&& mask256 = dom_22 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_22 = T &&& dom_22 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_22, hd63, hout]
  have hnc_m : ¬ IsConst dom_22 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_22 roots_22 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_22, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_22 roots_22 0 roots_22 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_22.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_22 10 hT6 (by unfold IsConst; decide) low_22

def wit : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.and, [8, 4]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_16013_aux

theorem PEqualNP.Outside.L_meta_16013 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_16013_aux.wit, PEqualNP.Outside.L_meta_16013_aux.wmono, le_trans PEqualNP.Outside.L_meta_16013_aux.wsize (PEqualNP.Outside.L_meta_16013_aux.lower s hs), PEqualNP.Outside.L_meta_16013_aux.weval⟩
