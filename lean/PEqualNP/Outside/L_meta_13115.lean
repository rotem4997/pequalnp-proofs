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

namespace PEqualNP.Outside.L_meta_13115_aux

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

def dom_0 : Nat := 0xf000f00
def goal_0 : Nat := 0xe000800
def roots_0 : List Nat := [0xa000a00, 0xc000c00, 0xf000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(9, 11), (9, 25), (10, 11), (10, 26), (24, 25), (24, 26)]
def r1sG : List Nat := [9, 9, 10, 10, 24, 24]
def r2sG : List Nat := [11, 25, 11, 26, 25, 26]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x721b65a4
  | 3, 0 => 0x721b65a4
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000c000c00000000000a000a00
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

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
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

def dom_1 : Nat := 0xf000f000f000f00
def goal_1 : Nat := 0xe000a000e000800
def roots_1 : List Nat := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f0000000000, 9, 41)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0xf0f0f0f0f0f0f0f
def goal_2 : Nat := 0xe0e0a0a0e0c0808
def roots_2 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f00, 17, 25)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xf000f000f000f0
def goal_3 : Nat := 0xe000e000c00080
def roots_3 : List Nat := [0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_4 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_4 : Nat := 0xf0e0f0e0f0c0f080
def roots_4 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f000, 4, 12)] (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0xff00ff00ff00ff
def goal_5 : Nat := 0xee00ea00cc0088
def roots_5 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_6 : Nat := 0xff00ff00ff00ff00
def goal_6 : Nat := 0xfe00fa00fe00f800
def roots_6 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_7 : Nat := 0xf0000000f0
def goal_7 : Nat := 0xe000000080
def roots_7 : List Nat := [0xa0000000a0, 0xc0000000c0, 0xf000000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 4 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_8 : Nat := 0xf0f00000f0f0
def goal_8 : Nat := 0xf0e00000f080
def roots_8 : List Nat := [0xa0a00000a0a0, 0xc0c00000c0c0, 0xf0000000f000, 0xf0f000000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f000, 4, 12)] (by decide +kernel) (by decide +kernel) low_7

def dom_9 : Nat := 0xffff0000ffff
def goal_9 : Nat := 0xfaea0000f888
def roots_9 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0, 8, 12)] (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0xffffffff
def goal_10 : Nat := 0xfeccf888
def roots_10 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_10 : Lower dom_10 roots_10 goal_10 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9

def dom_11 : Nat := 0x5555555500000000
def goal_11 : Nat := 0x5444504000000000
def roots_11 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

namespace S_11
def pairsG : List (Nat × Nat) := [(34, 38), (34, 50), (36, 38), (36, 44), (40, 44), (42, 46), (42, 58), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [34, 34, 36, 36, 40, 42, 42, 48, 52, 52, 56, 56]
def r2sG : List Nat := [38, 50, 38, 44, 44, 46, 58, 50, 54, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_11.map (· &&& dom_11)
def goalM : Nat := goal_11 &&& dom_11
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x4b5c3f1e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5555000000000000550055000000000050505050000000004444444400000000
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

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_12 : Nat := 0x5555555555555555
def goal_12 : Nat := 0x5444504054445000
def roots_12 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555555500000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0x3333333333333333
def goal_13 : Nat := 0x3222322232003000
def roots_13 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_14 : Nat := 0x3333000033330000
def goal_14 : Nat := 0x3222000032000000
def roots_14 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_15 : Nat := 0xffff0000ffff0000
def goal_15 : Nat := 0xfeee0000fecc0000
def roots_15 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc0000, 16, 18)] (by decide +kernel) (by decide +kernel) low_14

def dom_16 : Nat := 0xffffffff00000000
def goal_16 : Nat := 0xfeeefaea00000000
def roots_16 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def dom_17 : Nat := 0xffffffffffffffff
def goal_17 : Nat := 0xfeeefaeafeccf888
def roots_17 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_17
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (2, 18), (4, 12), (5, 7), (5, 13), (5, 37), (6, 7), (6, 14), (6, 22), (6, 38), (8, 12), (9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 26), (16, 18), (17, 19), (17, 25), (17, 49), (20, 22), (20, 28), (21, 23), (21, 29), (21, 53), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 38), (34, 50), (36, 37), (36, 38), (36, 44), (40, 41), (40, 44), (42, 43), (42, 46), (42, 58), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 2, 4, 5, 5, 5, 6, 6, 6, 6, 8, 9, 9, 9, 9, 10, 10, 10, 16, 17, 17, 17, 20, 20, 21, 21, 21, 24, 24, 24, 32, 34, 34, 34, 36, 36, 36, 40, 40, 42, 42, 42, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 33, 3, 18, 12, 7, 13, 37, 7, 14, 22, 38, 12, 11, 13, 25, 41, 11, 14, 26, 18, 19, 25, 49, 22, 28, 23, 29, 53, 25, 26, 28, 33, 35, 38, 50, 37, 38, 44, 41, 44, 43, 46, 58, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xfffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_17.map (· &&& dom_17)
def goalM : Nat := goal_17 &&& dom_17
def NN : Nat → Nat
  | 3 => 13
  | 4 => 77
  | 5 => 396
  | 6 => 802
  | 7 => 440
  | 8 => 25
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xfbb39bb2d6755a4aba719f71a7bf35108e966db875ea20b772bafbe44fa066884be8133944614dc002cdbec002200d7e00812e2a
  | 4, 0 => 0xab32bfdba76ccd1ba69a2826a42727099a91965287857b7e7ea9a5f87166856d6ff5f3896e297dad6da67423690dc4fe68391bfd67f45c1866c27f786643b8fa60f832056056054c602ecf3d5f79f85d5cebcb435c2b928a5aae476555c9dc9d4e4afb424c0d1f964a102a22492a59a147fcb4ab45f24fb445e856f942f7b56d410926143fb2da623d6423283b1792923b083576397cfa2c37fa6010371934b336c29f1735247ba13260f29c31e6428030b5f22c2d4972ae2bbe4fd029290f0c227d774721d266a02135594d1d9a75de1cebba641cdc31951c9c37271c3e05831951c3000d58fb180b280b0209861a8c055fc1a103d5c90902f4baeb00c7b156
  | 4, 1 => 0xf28baf1ee3a7c5e5d8b6b539d6a34b92d08f2e02cd8ba78accab0e83c8b4fdd3bc82b3e1bbce2997b909cc8bb00c659bac15681b
  | 5, 0 => 0x17e9ca46173324b915dac5e914f6ad4b13e604e413affcc6133e091413350bca1331761912fc993212fc8c93123a1e49120c200c11ff708311ab9d98119dfe101178edc91161181a1153752410d606ee10d2ba0210c38009103dbd960ea7e5180e5f4a880e3bfb810e191fab0e029bc80d89a68d0c9480210c69bfd00bcfb3fa0b76be730b6a7b1d0a6084d10a0dbee00a0bf17109d0c57e09b7e7790993677c093fe48d0901497508ea0cab089ede53085a022307e998db0705106d062efed5061ff023061261730541786f052f839c048e7392046c39c104173ae103e95633034b623b01d9430501373cfc01204fab0105e6ea00ddfc6500c2176000904a51
  | 5, 1 => 0x2d8d30732d8b58242d2ec1b82c22e3092bcd5b7f2b71f0412b5203712b000c4f2aada6d0298d50c2297a776228605c1f281a6a4328173bdd280064ef27a8a3f5277c205e26fe9cc7263b036f261bbf1925a9d301257d59b82330709522c4e84a2292a079228802542259f2bc21b06328215ad64c21488ce020df264920bb269b206d0bcf1f93080c1f50bbd11f426e131f34b1941dec05861d0a27431cd7515e1cb449831c00ccfa1bdc02591babfac91b7e2e5d1afcb9971ae4d2881a761be71a7498901a66cec71a1f0ef61a16d3db1a10f6e51a0aa15e19f07a78194f2d801926f567191083151900d8b018f26c4c18e1427018cd369118ae189c181d7b92
  | 5, 2 => 0x4c8ad3a14c85ff684b04cebf4ac0847c4a9560054a436bbb49abc8654963f70a495b4db1492a59a148fa711d47b4abff45d6f27244b733b343091b424266a0bd4241674c412ae36840c1743d409bb26640183da43f9fefd43f4ef09c3f3f63773c1a39ca3b932d743b52acf83a84e7713a792f6a39bf1eb539b9720e39183f2c38f5500a38db6caf38ced83238c28e5738b1459438a27cd7384d42aa383d0cd037f8c67a37ca88eb3761c3f336bfe51836730fc035dd329c34d3193134ae08e13471896c34365933341f29fa32c3f5043210d20531e3890231d9a86631c32dd1317a69f63100d8de30d6b6c5300d062a2ee7a1cf2ed07be72ec9d7862e7d9cfa
  | 5, 3 => 0x70c4cd536f8795176e5661bc6e0920306dc267686dbb437b6db2c6976d6a8de86d5e69576bed0c326b95d0e06b0981336ae9049a6a63eb3f69c1b8116969bc1a69094ff267535a5b6751c7e766f5720065d47924658e79876586cff76524bde2649cfa0463ae5d666375d82b625a279161ece5a9612ad0e960ad8dc15f14da325e2d8aab5e2c2c165d499fea5cf53b155c6c66715bf6e8f75a9970315a09de3259f9642e59e92d7a5871d44e5796e9b0573ce74e57329b8f56fbf48f56efe638554b493853b991c65362a58853611af552be2f945287732c527036d352156f1c4fab29314f7c60744f5a105b4f52da884eeca8634e9f53f74e05964a4dfe2632
  | 5, 4 => 0x983f1e8f97230872961e20c195d931b69554ae3593fd790193061ff29301798492e8bc00918c42e290a3cde690370fa58f95bdff8e0ba0b88dfec2528c7eb4e58be1a6ca8ba9ec848b7945308b0401ef8ad3bad78a7347018a01964f8803bf8e8722bac7871797e885ac7091845407c9842c50d4841919e083e1bfe481d7f28c81b15167813d68f8805d99ab7f2210c27f1c9e7d7e8451ce7cf2005b7cda4ff47c84a63f7c3bc47e7c3a86f47bd6bb247bb0128c7aa78b3c7a82b9b97a454d6579f2786779e6d45178f3399377919af776c461dd767c5d42751113a074fc2d47743641ce72c5d62072a4a4a572417a9971d0605571c4c2dd71c11994713c4391
  | 5, 5 => 0xdff65054dd55ab1edd1dbc54dc9e31b7dc385fccda702172d9927432d754e645d74fd5ccd62a87b6d3084f68d26c31fed24dd00fd16b37a1cb318dbacb0f381bc9fb49eac9ae378fc962e58fc6a07237c5f0fb2fc4ea5ce7c4a2db87c338dcabc31aa616c311f58bc02c4bbdbe8ee60bbe571b16be469854be306bb3bbe6dd5cb93d8228b934ade4b8f3a8e2b8592092b6ff990eb6b512f6b3db5d80b312a3eeb2f8b09db19d22c1b1635532b12fd890b092cc10af4ed27bacfe865ea9d002ffa6db69e1a5824b5aa521a125a51c6199a467ebffa4432ef1a35c9dd6a24442aea0eb106ca09c29609dd8e2069cc122649b94b0649b3436919a40fa0e98a05a6c
  | 5, 6 => 0xfd9810a5fac9ded5f6604ff8f3b9cc40eeec78f7edc56482e89f1d3be868c059e52d450ce42f8233e3cd2773e254d007
  | 6, 0 => 0xc2c14070c269c8b0c0930a10bbb8e270b5bd3a60b2c8ce60b15b2110ae653d70ac4d5b90a7677f50a75789c0a6572fc0a4eea960a01f69909f7ca3e09da5e5409bdf0a009bd51ef09695d400955e8780938390c0919997808ba381d08b08166087a815b080a8eb707fab1ba07f1b6d607a676fd0787d7a50711d49e06fe79c006e10dd606dc984206b5fac60681af19065d56850644c923063e9172060f596e060e91e705b8649705a9e53f0562a0ac0559e5f5053c7a0b04963a7b0432137103f8e99a0389d21f0380978b035eb4ec02d6a72e02c16857024365d601e3cad001ad4403019c9fad01652a32015e807f00f94cd000e52646007dbb7a006c2684
  | 6, 1 => 0x16766cf21673385e16528f3516446b9c163cc6661611817415f4eac915e9498b1596d48d156a912f155ed0bb1535fac81528c49c1517feab14c15aa414b84f321474608f14696ac2140adaec13fdbe2913ea83c213e0e2a713d6d81d13967e2f1375dc65133c08ef13346ed1130a5a8912ed399912c360531212f14a11d640d0119fba61119ab5831161181a115cdc52115a796710bf6ca610b7c9a8107b5734104ad074102497a91004efa20fec104b0fe0ec5e0f8898390f115ba20ef737100eed14a20ee2d2210ee0af2a0edf18670e7e15130e0550e70dd633720db753420cedf22c0cdc56be0cd88bf40cd4b54f0cd412060cabde0a0c97cf590c319334
  | 6, 2 => 0x23c08397238cde422325c90b22d25b5c22880254219634db217ce7742177d428213dff8121144ec620b8602f20b6484d20810030206bd013204ed6c3204a722020292edb1f9547f51f7c1b131f4eac261f06a07c1ee07af31ec0fa371ebcbc8f1e9a7a0a1de45f961db574801d70c9b71d07cbc61c96ea491c7f55261c6f9fec1c53915b1c397d011c1250521bdb5b301baefe391b27d2611b16f5ed1aa1953a1a548add1a2639791a1f1cf019ba87fd19ba301a198604a81927b99a18eb577118ac994f188e19d01882b169185955ec18545dd617b77a5217aeb25017a260fe176fbdf717617b9e1734bd561701656116f36bf316b01e5416995adb168bc85d
  | 6, 3 => 0x2f643cf62f3c81e32f3294542f2d39052ede35262ed0d2042ea523322e450d9e2e2eb6002dedc9542dec4b6b2de6358a2db09fc22da94f942d52d1502d20bdd92d06d0c22d01ecaa2cadc4612c7dc05e2c6cb9a92c42325c2be51bdf2baaf0272ba8f9b52b1903882b08f8cc2afda44c2af8e8dd2ad3509f2acd7a982ac54d632aa964312a95810c2a53358729af2b6429a6739a293f76f0293427572908d1e428e1d56328d3f68428a4a83e28732d7b285f16652842fbd327d2a877275dc4202750b4f62713cf0026e23bf0267b41f52664076225f116f1259a31372566dfcd2524b4b824cbf971244f823f243e5010242f7cff23f07cfd23ee01b823e65826
  | 6, 4 => 0x3ae826bb3acf9b4b3a822ece3a7feee53a4fc2063a3e996d3a2d6c6239bb3ded398649303965a154392f382438ed9e2f388012b1383545ab38296398380d7bfe37fdfb783790d59937596ec3375583a937468211373817bf3727f4ba36ffac3036c5746f36c1640236b5383e36648703361d50e73609387935fe022a35787e26353aa3c635169f3a34f524f934c589ee34a771a7349995fb343ac70234064f6c33df688433da662c33da452e33d6627333d25e6233a2828e3373c40f33722ba032fa2f953294f0e032441760321d7eb2320f9fd3315c50af315c08eb313ee4c53117e4f43115c93030e94f8c30ba24d830b4f5322fbf5da52f8141142f7e6ae6
  | 6, 5 => 0x4978c0ae497253c149440b174910933d48c35a8b48683a6347ff7ab3476def3e46f1b31146e45dc946df279b46bdac8746ba812f469949b54619497e45f126ed45a7f598455be5b544d46f7844c48b06446729e643e9290d43e3db9743bc23ab435fdc07434ac03242ef746f42b451b04270b5be424acd374221143d418c58194183d8874149254d41320659412c1b38406a83da3ff0f5f13f7f6a493f1e2b9c3e79bb8a3e56ef7b3db4e4813da4f3293d8f565c3d8a3cae3d6b77133d5b65d93d4f2d143d4e5b033d2c7c353d1f3f593cfaa5163ce437ac3cc696da3cbcf7af3c21f90f3c0ce04f3be497a23b8aa58d3b754d643b33d6c03b0f2c583b0a44b3
  | 6, 6 => 0x56f3df7156d29d1756b15356568029ba56488c3a563580cb5618ad155615047155eeb44e55a4b4595592841e55914c4d5571ce4a54dccf5d54d9fe7754ba54e35485444a5479ade65416d04b538c2b2c536a1507535b8ef053466db853447d04532529cc52c16aed5257aedf51ed228251e93bed5074cc075014114e4fc559f74f57f3d24f135c524ecc8e064ebf453b4ea4fa1c4e79be084e1018c74defc3b64dd3ad484dc9c7c04d84259f4d5001c34d2f3d364cd5ea514cad82f14ca489ca4c8a818c4c0f52314ba1260e4b81ba084b5265b34b2472944b236a724b226b904ae1e0704abd1d0b4a5f19f44a55e6434a3f5f3c49fd469d49beb9e849b6983f
  | 6, 7 => 0x685a494667d2ecc667757f61672edba1671ea51e66d0a35666a873e666540d4c66357d3e6557fc266517bf0f64ebe55664610497643988c9643609f563939f336326e6d962dfa08f62bd28d862bc93d2625d869760fe5bb2601c8a0d600ad1db5fce787b5fc559925fa001255f9a0e3f5ed6a3f15e96063b5e5ba43e5e02d08d5deb71af5da6006b5d1e66bc5d0eae245d09bc575c9b90375c97debb5c5ce06b5c499e5b5bf13ab45bb03c075b6b6fdf5b3bed485b1f7a795aa8a6b95aa5f5965a6d6fbe5a5a68e35925466959100b80590c070f58a9df50589311d4588ac935588269ee5875705b58430005583d5a595808a353580006e257a487195702a7c2
  | 6, 8 => 0x791e9fb7791205e2789cb22c7829da41780e8f5777cfa6b1770e4b0576e1a5f076a582cf7636f3227613d46a76076036754fe6cf75364d1d7522e0b674d57dbf74cf39e47481ccfa74789e64745649717407475673f739d4739c3b75738117497369c766730cc97a7301de5f729c25ac7288949c727718da726a4e017218e0f571ec93a571bb8921719597587193d4b1718aa31d715bc440710c7cc670fe4ee070eea42e708b912d700aec186f6a8dfb6efba8276ec7a3626db3cd8b6d76e7956d65318d6cfb7a1c6cd6ca796cc7f9b76c3bd30b6c0fa5ef6be903d06bd3e8686bba04806b3457826af897496a95be0b6a80e84b6a54273769ac57256909bb46
  | 6, 9 => 0x8e0cfa578dd9a8ed8dc082c58dacf6f48d5eaaf98b0e758b8adb09b18aafa50e8aa42a2f8aa3b04f8a81f0ca8a2ec80d8a0b34fc89f074c389e93ef089e7ef1088e0387f8826fc3987b2ceb4879add678786ba78877779c38759f0be8749a55b871506e986d3f20a86465a8a863f5b5b85f6241e857778ec84d0ea0982cfc52182c96d8a829ec1d6829abebd8220babb81f6d6c281e9f85c80ff692c8069eaef7fd8d7587f85d4067f78c21c7f685e077f24c13b7eadd0e57e964a3e7e7a0a4c7e4b58517e22ace77dc594b27d41b0af7d2933597cf889057ca9b5577a92749f7a5b787a7a399f0c7a05242f79e15a2879d342cd79bb6d1e79684f627961f727
  | 6, 10 => 0xa8f0d2eda8afe02ea84edc83a788dfb8a732a1a6a72fdc37a6353a8ca59b5408a533b563a4e8963ea4b188daa47edabfa3978b47a2a97873a284be75a275f6c8a174c228a0d162fda0bf0646a05ab451a008f5839f9ea33e9f9e4cda9f22e88e9ec9ae489e5c023f9e0a09409cefd78c9c96855e9c86b7d99be7a9099bca9a899af9d2839a18a88399d3056b9997d904997374ef994b9d08993a7ae3989a8dc3982e64fb97a00225977488ac969aeb72968d4d5f967fbfcb9661aced9551aacc951cbb329515305d947d9aae93886129935ddd6e918bb4fb9148b103906d80ec8fd304808f9fd3cb8f09a0718efad5908eb3b3e78e3f8c778e2526e78e128689
  | 6, 11 => 0xcaefe3b0cac9e179ca6393caca4b1c80ca34bcdeca14a60bc9db535dc94fa081c8e9878fc8856e22c6d0b208c6068286c54de09cc5057f75c476db43c453a13bc44cc871c4209f4ec3d820fcc3ab1db0c2ac5c31c13d7091c104a00bc0f21befc0e08b57c0d8bcdac01a4c7abf98043bbe20deedbdf67f72bdd61ad8bd7258e7bc7e8f37bc545819bb44492bb90d8a13b8a185a6b86243b6b8554800b7ad2f8cb79618a9b75c39a0b71329c5b63ee375b4bad623b3fd0706b3e7728fb250cd45b1fba0bfb03615abafd75c9cae87a2bbae1bf85dae18ff3dad58a5d0acf0bd5bacc719e5abc0f8acab676f4faaa81632aa2ce68ba9f3d131a9ea9735a94c64a9
  | 6, 12 => 0xf8a016c6f59108abf2c140a1f0f8df95f0cb655eee71eebced215bcfec164c1eeba28a2aeafba6c3ea326695e88e9a99e2f6af66e247b55ee0d0507fdff3a4ccdc8a5345dc778fdfdb7eec9cdaa10b17d9fb6b94d8c1607fd79dcf25d5e44738d568b144d55284a3d445852fd30d0d53d282ff82d1296545d019b0f6cd0facd0cccaebe6cc338a53
  | 7, 0 => 0x16e8db1816b50ee91581f8c8141a4f1c1415063f1413d60813b5da6d135211a2131bfefa1317dd2b12b8884a11ed84b711eb7ccf11d748061198114410d1aa96103ead2a1004221f0ff073950fc22fb60faa77070f8b2a5f0f8898390f6b9a140f5c5cfb0e8414b20e7e15130e7dd0190dfb96ef0df078900d91ebc20d61f2fb0d4d98860cc7aa850cb3009d0cabde0a0c867e660c22507d0bd753a90b41c7720acf09dd0ab7b9ae09ee1b6f0878675807af559e075140fd06b07a0306291d8305c61dd605ad2f34040745c6036df1500347620202d5abde0291d00a023f103c023c952e01a603fb0198251c0188fb4b01013f3600f5a3d20086a50c00273479
  | 7, 1 => 0x2b0f56702acd7a982a7c85282a6cf0712a5175e429e942c4291abe5628a4a83e2774c460275958f2272770732705880d26beaf6f26a4b5bf26488ebe261c309d26093241259eb530258a6ea42509c4b824cb7b29246554a62429651523fe6fae23afce9222daf26b22d85c9a223682592219ec0a21e9d24d21a5f96820df43cc2081cc61204bdfba204aaf2d2046aaad203cd04e20292edb2014c6441fd3d3851e739d441e3d0e221d989e101d89743f1d81c57f1d29fe0a1c1ffead1b78d4bc1b70b1901b52f3321b325a461a0ece701a0dc40d19b1d4481979f417196672e119169d33191531f41900f429183e8305181aa94117d07b0017a82026175a929b
  | 7, 2 => 0x4305883642b779a34223bdb94215deda4214fad141d622d340bb28344079af63405c8f3d4025ca0a3f49363a3ee6de3d3dff89d03d8620523d6d0b963cd7d7c23c9f3cdf3c9dc2fe3c9d75a23c8fe41f3c3d49423c38e0113c21f90f3b5624293a8b9b213a861c993a476634396f572d395003403899ed1837dd7e8037b9fc1b375fd1e83732d33a36e4026d36b6da92363c57f436224d1b359aee6d358e7c13354bc4fd34746a9f342cdee934064f6c330961a632ba82ac3264f1943243d5cd315024ba3129ad3f3122199e30ccd1eb30bda81a302ca7772fc976f62f7655c82f1362052edbd6b52ea0b9112d90db782d6df75a2cf3c0ef2cb7e2692c9946a2
  | 7, 3 => 0x5d1e66bc5cde0cce5c9fbd605bff541c5aa8a6b959d66aa059d395c7596cee2e58a5f17758905d135806ebe2568ff7f15640306856240dff557f4cd954b47b9853b7a8b5531915d15314eaf652e996fb52acbe7d523dc211520a3fab51d2062b51bf3f2b51bb2a0f514f645451099cc650c4b4ed500139404fb2394c4f9b055d4f943bc44f717d1d4f624ff44f0fba7a4e2ce2974e1717654e00c0ea4ca60af44c173de94c1326ad4bc969994bb8974e4b6e21e64b0c2c394b02825d4afc5e1e4aee73794ac0774d4a6707154a3f78dc4a0d1974499b08ca49148db048b0ac9d46e1bded4609964845f6b58445d91ef1457c5ed143a9f848434ac0324309ffd8
  | 7, 4 => 0x7c0721267bc86ac17ab597257ab2c9087aa157477a85129f79e15a28791d9b41785a178978493a7f77211a3f76eecc3f76db0b2e76b015da74d2ee78745a681c72b28339727daf3d7260e48f70cdf0747005f1236f6c29a26f69601f6e38e6f66dcb09b56db8095f6d5cb0976cd622c66c4b6e046bcf90f36bcb63fb6b89f08a6b7c11ab6afac8926a7ff6686a0139de69c0add469b2eaed6920920f679d352a673394256709aa6167044c4c668c477066357542651506a464e6ab0264e30e64645092fc6449b75d6401590263353df46284e04361aa33686129ea2960b58bf55fbac6fd5f5d13a95f2a63495eebace45e90082e5e22a7545dc82fa15d6275f4
  | 7, 5 => 0xa309310ca2f4f716a1c6431fa1662bafa07b39919e6bbe4b9e58572e9da1794d9d61744b9bfcd7929b71391a9b1dd7b09aec1f2b9a81c9ca9a36658d992721c2989a692798553ede981b7e9297a4f38797251c989721f5ed94b8834e944ede0093f42b8d92ef453392b08ece929a9c8491b98d1291426eab9117715e90061e318f7fd14d8ebf00228e7679718e4941358e35cdb08d5eaaf98d3d413a8c76bee98bedc1998b8fda438aef68758a81f0ca8a0d10dd8968a0cb87cdddd0877910e286bb6894869b759485520fcd85210b0383c5bc52838341f4833df903828511a4806266ad804281917e8559377d7d57bc7d356db97d33ff317d303bbe7cea112d
  | 7, 6 => 0xfce2758bfc3e0176f9acd0faf20a7ebff11d8484ec164c1eea555bf2e8b03ee3e5b5122dde1b0bb2dd1bb31cd9e7a089d6fe6644d697c1d4d5d13c99d1786b89cbfcbae9cae6d7d7c9e24337c8d8951dc7ad77bcc7466283c37f968dc3598a1dc110cb7dbf01fb40bef5700abd0683e7bc545819bc18011ab9fc935bb837fe7bb7a1fd24b7610a65b65f3e8fb59a84ddb52557b8b4d0d4a4b3feb3cab253eee6b23cd636b18cc501b0f51e5bb080f6ebb038e43caee65ee3ada32de2ad6e1b08abbe6e52ab47af95a98c5b5da9647ee6a80d4bfda6910249a5e4c2a9a494c22f
  | 8, 0 => 0xc3d681efc2afde01b6be76348ab84b5d8a7994f87cea112d764e5f6161ca40085fbac6fd5e22a7545cde0cce51bb2a0f4aee737942b779a33e277fff34064f6c2efbd9642eedfa851e7359ed1b78d4bc1729918f1561a43a1142fa410e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff0000000000eeeeeeee00000000cccccccc000000007777777700000000555555550000000033333333000000000fff0fff000000000000ffff
  | 0, 1 => 0xcccc0000cccc0000aaaa0000aaaa00005f5f00005f5f000055550000ffff0000555500005555000033333333333300000f0f0000ffff00000000ffffffff
  | 0, 2 => 0x303333303033333030303033333333300ff00ff00ff00ff00330033333333330000ffff0000ffff0000ffff000000000000ffcc0000ffcc0000ff000000ff00
  | 0, 3 => 0x11115555111155551111111155555555111111113333333311111111111111110f0f0f0f0f0f0f0f055505550555055505050505555555550333033303330333
  | 0, 4 => 0x33332222333322223333000033330000332233223322332233003300330033003030303030303030222222222222222213131313131313131133113311331133
  | 0, 5 => 0x44444444444444443333333333333333333333333300330033333333303030303333333322222222333333330000000033333300333333003333303033333030
  | 0, 6 => 0x66666666666666665555555555555555555555555555000055555555000000005555000055550000555055505550555055445544554455445050505050505050
  | 0, 7 => 0xaa88aa88aa88aa88aa00aa00aa00aa00a8a8a8a8a8a8a8a8a888a888a888a888a0a0a0a0a0a0a0a0999999999999999988888888888888887777777777777777
  | 0, 8 => 0xaaaaaaaa88888888aaaaaaaa88880000aaaaaaaa88008800aaaaaaaa00000000aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa0000aaaa0000
  | 0, 9 => 0xaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaaa000000aaaaaaaaa0a0a0a0aaaaaaaaa000a000
  | 0, 10 => 0xcc00cc00cc00cc00c8c8c8c8c8c8c8c8c888c888c888c888c0c0c0c0c0c0c0c0bbbbbbbbbbbbbbbbaaaaeeeeaaaaeeeeaaaabbbbaaaabbbbaaaaaaaaeeeeeeee
  | 0, 11 => 0xcccccc00cccccc00ccccc0c0ccccc0c0ccccc0c0cccc0000cccc8888cccc8888cccc3333cccc3333cccc0000cccc0000ccc0ccc0ccc0ccc0cc88cc88cc88cc88
  | 0, 12 => 0xcccccccccccc8888cccccccccccc0000cccccccccc00cc00cccccccccc000000ccccccccc000c000cccccccc88888888cccccccc33333333cccccccc00000000
  | 0, 13 => 0xeaeac0c0eaeac0c0eac0eac0eac0eac0e0e0e0e0e0e0e0e0e0e0e0e0c0c0c0c0dddddddddddddddddddd5555dddd5555ccccddddccccddddcccccccccccccccc
  | 0, 14 => 0xee00ee00ee00ee00ee00ee00cc00cc00ececececececececececececa0a0a0a0ececa0a0ececa0a0eca0eca0eca0eca0eaeaeaeaeaeaeaeaeaeaeaeac0c0c0c0
  | 0, 15 => 0xeeeaeeeaeeeaeeeaeee0eee0eee0eee0eecceecceecceecceeccaa00eeccaa00eecc0000eecc0000eeaaeeaaeeaaeeaaeeaaeeaacc00cc00eeaacc00eeaacc00
  | 1, 0 => 0xeeeeccccaaaa0000eeeeaaaaeeeeaaaaeeeeaaaaeeee0000eeeeaaaacccc0000eeeea0a0eeeea0a0eeee8888eeee8888eeee0000eeee0000eeee0000cccc0000
  | 1, 1 => 0xeeeeeeee00000000eeeeeecceeeeeecceeeeeeaaeeeeeeaaeeeeee00eeeeee00eeeeeaaaeeeeeaaaeeeee0e0eeee0000eeeee000eeeee000eeeecccceeeecccc
  | 1, 2 => 0xeeeeeeeeeeaaeeaaeeeeeeeeee00ee00eeeeeeeeee000000eeeeeeeecccccccceeeeeeeecccc8888eeeeeeeecc00cc00eeeeeeeeaaaaaaaaeeeeeeee88888888
  | 1, 3 => 0xf0e0f0e0f0c0f0c0f0c0f0c0f0c0f0c0f000f000f000f000eeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeeeeeeeeee0000eeeeeeeeeecceecceeeeeeeeeecccccc
  | 1, 4 => 0xf0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0c0c0f0f0c0c0f0f00000f0f00000f0e0f0e0f0e0f0e0
  | 1, 5 => 0xf8f88888f8f88888f8c8f8c8f8c8f8c8f888f888f888f888f555f555f555f555f3f3f3f3f3f3f3f3f3f3f3f300000000f300f300f300f300f0f0f0f0f0f0f0f0
  | 1, 6 => 0xfaaafaaafa00fa00faaafaaaf000f000faaafaaa00000000fa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f8f8f888f888f8f8f8f8f800f800f8f8f8f888888888
  | 1, 7 => 0xfaf0faf0aa00aa00faf0aa00faf0aa00faeafaeaf0c0f0c0fac8fac8fac8fac8fac8fa00fac8fa00fac8f0c0fac8f0c0fac8f0c0fa00f000faaafaaafaaafaaa
  | 1, 8 => 0xfafafa00fafafa00fafaf8f8fafaf8f8fafaf0f0fafaf0f0fafaf0f0fa00f000fafaf0f0aaaa0000fafac8c8fafac8c8fafaaaaafafaaaaafafaaaaaf0f00000
  | 1, 9 => 0xfafafafaf8f8f0f0fafafafaf888f888fafafafaf0f0f0f0fafafafaf000f000fafafafac8c8c8c8fafafafaaaaaaaaafafafafa88888888fafafafa00000000
  | 1, 10 => 0xfcccf000fcccf000fccc0000fccc0000fca8fca8fca8fca8fafafafafafafafafafafafafafaf0f0fafafafafa00fa00fafafafafa000000fafafafaf8f8f8f8
  | 1, 11 => 0xfcfcccccf0f00000fcfca8a8fcfca8a8fcf0fcf0cc00cc00fcf0cc00fcf0cc00fcccfcccfcccfcccfcccfcccf000f000fcccfccc00000000fcccf0c0fcccf0c0
  | 1, 12 => 0xfcfcfcfcccccccccfcfcfcfca8a8a8a8fcfcfc00fcfcfc00fcfcf8f8fcfcf8f8fcfcf8f8fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fc00f000fcfcccccfcfccccc
  | 1, 13 => 0xfeeefaaafeeefaaafeeeaaaafeeeaaaafeee0000feee0000feccfeccfa00fa00feccfa00feccfa00fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcfc00fc00
  | 1, 14 => 0xfefef0f0fcfcf0f0fefef0f0eeee0000fefe0000fefe0000fefafefacc00cc00feeefeeefeeefeeefeeefeeefcccfcccfeeefeeef000f000feeefeeecccccccc
  | 1, 15 => 0xfefefefefefefefefefefefefcfcfcfcfefefafafefefafafefefafaf0f0f0f0fefefafacccc0000fefefafa00000000fefef0f0fefef0f0fefef0f0feeef000
  | 2, 0 => 0xff00ff0000000000ff00f000ff00f000ff00f000ff000000ff00cc00ff00cc00ff00aa00ff000000ff00a000ff00a000ff008800ff008800ff000000ff000000
  | 2, 1 => 0xff55ff55ff55ff55ff33ff33ff33ff33ff00ff00ff00ff00ff00ff00ff000000ff00ff00cc00cc00ff00ff00cc000000ff00ff00aa00aa00ff00ff0088008800
  | 2, 2 => 0xffaaaaaaffaaaaaaffaaaaaaff000000ffa0ffa0a0a0a0a0ffa0a0a0ffa0a0a0ff88ff88ff88ff88ff88ff8888888888ff88f888ff88f888ff888888ff888888
  | 2, 3 => 0xffc0c0c0ffc0c0c0ffaaffaaffaaffaaffaaffaaffaa0000ffaaffaaff00ff00ffaaffaaf0a0f0a0ffaaffaaaaaaaaaaffaaff00aaaa0000ffaafaaaff00f000
  | 2, 4 => 0xffccfcccff00f000ffccf0c0ffccf0c0ffccf000ffccf000ffccccccffccccccffccaa88ffcc0000ffcca080ffcca080ffcc8888ffcc8888ffcc0000ffcc0000
  | 2, 5 => 0xffccffccff00ff00ffccffccccccccccffccffccaa88aa88ffccffc0ffccff00ffccff88ffccff88ffccff80ffccff80ffccff00ffccff00ffccff00cccc0000
  | 2, 6 => 0xffeeffaaffeeffaaffeeeeeeffeeeeeeffee0000ffee0000ffeca0a0ffeca0a0ffccffccffccffccffccffccffccff00ffccffccffcc0000ffccffccff88ff88
  | 2, 7 => 0xfff0fff0aaa0aaa0fff0ff00f0f00000fff0f0f0ff000000fff0aaa0fff0aaa0ffeeffeeffeeffeeffeeffeeffccffccffeeffeeff00ff00ffeeffeeeeeeeeee
  | 2, 8 => 0xffff0000aaaa0000ffff000088880000ffff00000000ffffffff000000000000fffefafaffcc0000fffafafaff000000fff0fff0fff0fff0fff0fff0fff00000
  | 2, 9 => 0xffff888888888888ffff5555ffff5555ffff3333ffff3333ffff1111ffff1111ffff0000ffff0000ffff0000f0000000ffff0000eeee0000ffff0000cc000000
  | 2, 10 => 0xffffaaaaff00aa00ffffaaaacccc8888ffffaaaa00000000ffffaa00ffffaa00ffffaa00aa00aa00ffffa8a8ffffa8a8ffffa0a0ffffa0a0ffff8888ffff8888
  | 2, 11 => 0xffffcc00cc00cc00ffffc888ffffc888ffffaaaaffffaaaaffffaaaaffffa0a0ffffaaaaffffa000ffffaaaaffff8888ffffaaaaffff8800ffffaaaaffff0000
  | 2, 12 => 0xffffeeeeffffccccffffeeeeeeeeeeeeffffeeee00000000ffffccccffffccccffffccccccccccccffffccccaaaa8888ffffcccc00000000ffffcc00ffffcc00
  | 2, 13 => 0xfffff0f0fffff0f0fffff0f0ffff8080fffff0f0ffff0000fffff0f0ff00f000fffff0f0aaaaa0a0fffff000fffff000fffff000f000f000ffffeeeeffffeeee
  | 2, 14 => 0xffffff00ffffff00ffffff00ffff0000ffffff00f0f0f000ffffff00cccccc00ffffff00aaaaaa00fffffcccfffffcccfffffaaafffffaaafffffaaaffff0000
  | 2, 15 => 0xffffffffaa00aa00ffffffff88888888ffffffff55555555ffffffff55550000ffffffff55005500ffffffff33333333ffffffff11111111ffffffff00000000
  | 3, 0 => 0xffffffffccccccccffffffffcccc8888ffffffffcccc0000ffffffffcc88cc88ffffffffcc00cc00ffffffffc888c888ffffffffaaaaaaaaffffffffaaaa0000
  | 3, 1 => 0xfffffffffcccfcccfffffffffccc0000fffffffffaaafaaafffffffff0f0f0f0fffffffff0f00000fffffffff000f000ffffffffeeeeeeeeffffffffeeeeaaaa
  | 3, 2 => 0xffffffffffffccccffffffffffffaaaaffffffffffff0000ffffffffffccf000ffffffffff00ff00ffffffffff00cc00ffffffffff00a000ffffffffff000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xab435509a4a7c35509a4b14355084489acd1e814ab43550874a1a74d04e486aa12a5c4cadb170684a5c359c9c486aa12082489aa11e8249caa10247486b151e5c4
  | 4, 0, 0 => 0xbc52e4cb8342e4e96f05c2a16f13486b50d0b4b99aa1244e5a5c35509a23ade2430d5427161aa847a04b8b81a5c35d2705bc52e82ad4e2de21aa84d9717274b8ab50d0b78b7c35de68586be51e86342e524aa83413972b93b7ae0d0b9586bdd284e5
  | 4, 0, 1 => 0x9caa11e811cad961aa8408e56f1135427104b7886b15385c5b6c35509c23ae1ebb0d5421d6f16f8e304d0b78a5c79d26e5bc435f068272e4e5ca84093970733542049cb78b7c3582945bc5a97868272c355090409397194b8f2fcd0b86aec3550885
  | 4, 0, 2 => 0xc3d2e1ad048ad2e66cc3413970f0d542289cb78ab43550885bc52d7268272e1e970d6a1d172b6c4e9a09cb78b23ad504e5a2435509a1cad4226a84e23d70f4b762a09cb0d5423d02395bc5be1adb432e06c90d542116fd0d5427104b85b7c3570685
  | 4, 0, 3 => 0x86aa11e5a20ae569f0d5427170f5d86aa134b7886be5385c5903213a68272e4eb0b8541a17194b86ac138b0d5423cb8405a5c4d669c47ad2e1ace3413961ab347a0472b78b2505ae4e5b1435505a222e42bb0d542616f16ca5ae0d0b5d86be51e685
  | 4, 0, 4 => 0x14386aa0d04e5cac355094432de297115427172b1c711a09cb9586b89284e5bc52e66d4392e56ad0d5427161aa847a0872b4b86aa1264e5c9dc170a8342e1e5ea8409396970d532708eb5686aa0c0405
  | 5, 0, 0 => 0xbc54652a8341398014b86a99284e5c0c821aa834111af15894aa0d04e6c3d2d68a830139af14b832a1284e6bc52e1adb57139af14b5c2a0d03f6bc435509c410e5af14b86ac4d04e6cad121ad4340edabb0d642a0d0406bc5be1ac14e1a1af14b8e2a10c686a5c4d90a834139afd0d5427102396
  | 5, 0, 1 => 0xbc5c6df0d5c1a1b0f0d54204c04e6c3de2bb0d54221b2f7886aa10c686bc5761aa84d9a1a970d5023cd04e6bc5de00cd34139b1f4b86b65504e6a5ce5509c478e5af15d86aa1105c6bcd2e1aa84e0e5a970d54250c44e6cac35509440139acb4b86aa138396c9d2d70a834111a970d64aa0d04e6
  | 5, 0, 2 => 0xa5c3582a8479a1a970d542711e396bc5bebb0d6d939af12286aa0d04e6c552e66d434139af14b9d2a0ec4e6c55421aa834139af15d92435509c6c9d6a1aa834139af15e86ae150686c2d2e1a9e34139b2b93b7a74d04e6bc5be1a9d431a1af15886ae150686a5c1da4a834139a970d54250ca4e6
  | 5, 0, 3 => 0xbc52e1af74a139a410d642a0d04e6bc52dd46d34139af16a86aa138396bc52e5d0d71139b1d4b86b6d504e6bc52e210d54271b0f4b86aa1204e6bc481a89d34139b0b4b86b50d03b6c1d461aa834139af10d54220b84e6c1d621aa834139af15d86aa10e686a5ce5509c4a139af14ba0a7538396
  | 5, 0, 4 => 0xbc5621ae234139a72a847a04d04e6a5c35d28f2a139b2778b7d2d70686bcc35508134139b034b832a0d0446bc5921ac62d139abb0d5423d02686bc5921aa83e139acb0d54204d04e6bc52e1ad834139af177802a138396c9d2e5ca82d139af16d94aa0d04e69ac35508f34139af16f86b70d04e6
  | 5, 0, 5 => 0xbc52e1aff368e5af16d89aa0d04e6bc52e3ca83e1a1b2b4486aa138396bc5aa1aa84a139a970d59a3cd04e6c9d721aa834139a970d7d2a10c686cad4e1aa834139af14b86bcd50556bc52e829d4a139a96b45423cd04e6bc55a1aa834101a970d7a2a0d04e6bc5621ae334139a972f541a09c476
  | 5, 0, 6 => 0xc0d76970d54251af14b9743550866bc435b6a840939b215886aa0d04e6c1db61aa834139af177802ccd04e6bc5de00a84a139af1414ea04d04e6bc52dd8a834139a1aa847a04d04e6a5c3590a8431a1af177803a4a84e6a5c35508f340fdaf14b99aa0f24e6bc5421aa634139af14b86ac8d04e6
  | 5, 0, 7 => 0xbc5621aa8431a1af14b93274d04e6bc435508534139af14b99aa0e44e6cad121ab334139af16a92aa0d04e6bc5461ad44e1a1af14b86bf8d84e6bc52e3f0d74939b2b445a2a0d04e6bc5761ae434101af16f86af8d04e6c65de00a334139afd6d86aa0d04e6cad121ae92a139a890d54268d04e6
  | 5, 0, 8 => 0xbf52e1ab8541a1af12486aa0b84e6bc52e1a9f4a139af54b86aa1284e6bc5921ad754139a97335423cae4e6c552e1aa84a139b075d86aa0d0406c0d2e829d34111af14b86b84d04e6bc5921ab854169b0f78a8435509c6bc5761aa83c1a1afd0d54271024e6bc5be3d0d609a1af15186aa10c686
  | 5, 0, 9 => 0xbc5de2ca834139a970d54250cc4e6c0dde00a834111b150d54204d04e6bc435508a34139af16286aa0b44e6bc5421a9e34139af14b86a9938396bc435509c4091daf15d86b1538686bc5a21aa8408e5af15d99c3550886bc52e1af254139a970d59a711e396c0daa1aa834111af14b86b50e8686
  | 5, 0, 10 => 0xbc54654a834139af16d86aa10c686bc52e1af3540e5b076f86a84d04e6c556e1aa834139a970d5423cd0416a5c35508f408e5afb6d86aa0d04e6c3de2b50d54271af14ba0ab4d04e6c2d2d68a834139af16f89a84d04e686aa1388f408e5af15d95aa0d0406c85b61aa834139b0f4b86a99384e6
  | 5, 0, 11 => 0xc8d461aa834139b274b6daa09c446bc54a1aa84e1a1aef00642a0d04e6a5c35509c3011dafd2086aa0d04e6bc52e1aae34139af10d53204d04e6bc5be1aaf341398010d5423d02395cae1e1aa82f139af14b8f3a4a83e6c1d2e66e954139a1aa84a23d024e6bf5be1aa1341398014b86aa0c24e5
  | 5, 0, 12 => 0xc152e1ab8541a1b274b83b50d03b6c3d2e72a84e139b2b7886aa1385c6bc435dab8541a1af14b9caa138396c85761aa834129af15886b6d504e6bc52e1a9e4e0e5af14b86aa1383a686bd5508f34139aa30d5423cd04e6bc52e1afc431a1af158a0a74d04e6c2dbe1a9d34139b2b93a5ae150686
  | 5, 0, 13 => 0x5e2970d540e96f14b8f2a0dc686b6c3550682711db274b83b14d04e6bc542670d54271a970d5423cb84e6cac3550942d139af16fa5ccd70686a5c3550662711daf14b86a79284e6bc401caa834139af10d612a0b44e6c3d2e1ab854181af10d54271025c6c3d761aa830101b274b8caa0d04e6
  | 5, 0, 14 => 0x52e1acc341396f14b5c2dd50686c852e1aa84c139a97295423cd04e6c3dbe1aa130139af15d8f4358a686bc54168a834139af16786aa1004e6c55621aa834139af13954204d04e6bc5b658a834139af14b97b50d03b6a5c35f6a834139af14b8c2a0d04e6cac7150682d139b2b0d54210d04e6
  | 5, 0, 15 => 0xa5c7990a8340f9b034b86a78d0446bc576829d34101b0b5886aa0d04e6bc52e82b634139a97135423cd04e6c9d2d70b5541a1af15d86aa0de686a5c3550a34e11daf14b9fa74d04e6bc52e5ec534139af14b86a8138396bc5361ac534139b195086a8cd04e6bc5da1ae234139afd6e86aa0d04e6
  | 5, 1, 0 => 0xbf52e1adb54139af13586aa138396bc52e4ea834139b2b87aec35509c6c6d2e1ab5541a1afd4ba0a74d04e6bc52e66d42b8edaf10d5426cb44e6bc435509c411a1b2b5786aa0d04e6b2435508f2d139af14b86bb9b6a86bc5b2969d34139b274b83aa138396bc52e26b354271b0f4b86b69504e6
  | 5, 1, 1 => 0xc1d661aa834139af10d5421904686bc592670d54219b0f4b86aa12c4e6bc5761aa84d1a1af10d5421906686b7c35428f34139af17686aa10c686a5c35e2a834139b2b4486ae150686a5c35c48f34139a970d68aa0d04e6a5ba9508f34139af16f86b5cd04e6c9d2e0ee92a139afd4b86acd509c6
  | 5, 1, 2 => 0xc95921aa82d139af14b8e3a4a84e6bc5429713542718017886aa0b64e5bc435508934139af14b86b10d04e6bc52e290d6a1a1b2b78b7c3570686bc52d68a84a139b2787a5b6d504e6a5c4d509c478e5b155d86aa0d040690435508f34139b0f4b86aa12e4e6bc52e66cd2b939b0f4b832a0c04e6
  | 5, 1, 3 => 0xbc435dadb54139af14b86af4d04e6a5d0a1aa834139af12386aa0d04e6005e2a113542716fd50a5c35509c6bc52e1adb54219af14b5daa0d04e6c6435468134139af12f54204d04e6bc5be1ac034139af14b8ac35a8686bc5b63ca8340f9af0b454204d04e6bc435509440939af10d74a04a84e6
  | 5, 1, 4 => 0xbcd321aa834139b2b44992a0d04e6c2d2e1acf34139af14b86aa134396a5c3590a84e0e5af13354204ae4e6005e2970d540dd7194b99a8cae4e6c652e1ab034139b0f77802a0c04e6005faa10d542717034b5a2a0d0446bc5be1aa84e171b034b86ba4a8446bc52e1a9e2e139a970d54270c4446
  | 5, 1, 5 => 0x5e2971359a717194b86afcd04e6bc52e52cd34139af15886ba4a84e6c1d2e1ad4340edb0d4b86aa1384e6a5c35b6a847939b2b5d8e2a0d04e6c0d2e66a82b911a1aa847a049c396cadbe1aa84a139a970d53250d04e6bc435eaa84e0e5a970d54240d04e6cad761aa84a139b2b9386b88d04e6
  | 5, 1, 6 => 0xbc52d70a83412db2b4f86aa0d04e6bc43550682d135b0f4b8f2a0c03e6bc5aa1aa8459a1a9733642a0ae4e6bc5921acd2d139af16d86aa138396c85761aa84e1a1af10d542190a686bc52e1aba34139af14fa5c35509c6bc5465ea834139b2b44a0a74d04e6cada61aa834139b275d86aa0d04c6
  | 5, 1, 7 => 0xbc52d3a7e34139b276f83a84d04e6bc5765ea834101b274b83b88d04e6c3d2e1ad4300edaf10d7b2a0d04e6c0d2e1aa8421a1b0f4b86a78c04e6cadb21aa834139af12086b34d04e6c9d920ea82d139af14b94aa1284e6a5c354c682711da970d54248d04e6005161aa8341397214b86b50d03b6
  | 5, 1, 8 => 0xbc52e809d34139af14b86aa128866bc52d789d34139b036486aa0b4446cad5a1aa834139af14b8e388d04e6bf435508134139af16f86a85284e6c35761aa834101af1648e2a0b44e6bc55a970d54271af14b86ab5509c6
  | 6, 0, 0 => 0xbc52e1aa8341382ef78a5c35506827051c0178a5c353c681b35e2970d83accd04e7a5c35508f369a09cf78a5d123ca8340f9ef172a5c35b6a8273e06f14ba0a74d04e7bc4821aa8341386cf78b7cce1aa134139f0f4b8f4355060273de2db0d82aa0d04e7c552e1aa84e1a09cf78a5cce1ae234139e970d642a0d04e203de2df0d509a09c397
  | 6, 0, 1 => 0x5e2d50d6a1a09cd8aa5c35506827121ef10d5428d0268273de297414e9a0b44e7bc52e3b0d541a09cf4b86aa11e682d139c0178a5c3550861735e2970d54270ee397bc55a970d541a09ce00bf52e1aa84e139af15086b515068273e42970d541a09c367c0de2970d6daa09cf81bc5aa1aa834139ef14b86ab55068273802f10d541a09c0d6
  | 6, 0, 2 => 0xc3de2970d542209ce00c0d2d506822055af14b86aa13668273802f12054274d04e6c0de2ef00541a09ce00bc1a09c1b0a84daf14b94aa0d04e1dbe1ef14ba0a74d04e7bc52e1aa8341409cf7886aa0d05a27105ef10d83aa10268273de2970d541a4d04e7bc4821aa83413872f7ea5c3600a834139ec94b86aa11e68273802f14b86b6da84e6
  | 6, 0, 3 => 0xbc52e1a9e3413888f87bc52e1adb54139f0f78b54355068273de2970d6db65504e7c852e1aa83413872f78bbd2e1aa84e0e5ef14b86aa12876273de2970d541a09c317bc592970d6daa09ce00a5c35509c1c82180193a5c359a68273616970d54270d04e7bc52e1aa83413832f7890435d2a834139ef14b86b6d505a273de2d50d541a0b44e7
  | 6, 0, 4 => 0xbc5761aa8441a09ce00a5c3550682701980178a5c35509c23b5e2970d541a09c2d7005e2970d541a06cd78a5c921aa84e139ef173a5c355068273e42970d74aa0d04e7a5c35509c4a23c9cf9586aa0d05a27111ef14b9c4355068273de297414e9a09c137bc52e1aa8431a06ce00a5c34d04e0d821a970d5423cd04e09bde2974186aa10c687
  | 6, 0, 5 => 0x5e2970d629a06cd78a5c354c9c34139c014b86aa1388f1cb5e2970d5421cd04e7bc5829733541a09cf78b4435508134139ef15186aa0d060273de2970d4f1a09c2e7bc52e1adb5413826f95a5c3550682711df0f78bbc015068273de2970d6a1a076157005e29706541385cc0086aa0d04e0982180178a843550681b35e296a84e9a09c3f7
  | 6, 0, 6 => 0xc45e2970d54218d0f78b2435505a270edef15da5c35c868273de2973386aa10c687bc5de970d749509cf7ebc52e1aa84e0e5e1aa84e23d0268273802970d479a09c1b6bc52e890d4f1a09cf78a5c7950681f021c014b86ba4a84e0435e2971386aa138397bc43550682d13898f81a5c3550a434111f274b54274d04e223de2a10d54284d04e7
  | 6, 0, 7 => 0xbc52e0ca8341386ce0086aa11e682704daff78a5c795068273de2973c86aa0d04e7bc5769713541a09cf78a5ccd50a32b939ef15086aa0d04e0dbe1e974186aa0c04e7c1d2e1aa83413876f78bbd2e1aa84a139ef14b86b50d03b173de2410d541a0a84e7bc52e1ae954218d0f95bc52e829d34139c014b5a2a0d04e0435e2970d582a0d04e7
  | 6, 0, 8 => 0xa5c35508f409a09cf95bc52e1adb54139e971e86aa11e68273de2974486b50d03b7bc52e3ca84e1a07cf78bbd2e1ab334139f2b4486aa0d066273de2b10d54274d04e7bc52e1afd54218d0f78a5ccd70a834139c0178a5c359a681b3002970d599a09c086005e21aa83413812c00bc5053a682704daf15086aa0d04e0abe1e970d541809c367
  | 6, 0, 9 => 0xc1d76970d541a09ce00bc52e1ca8270918017886aa0d04e0635e2970d6db59504e70052d90a8341382ac00bc5de00682706daf14b86b795068273de2df4b89aa0d04e7c65de970d519a09ce00bc435b6a82704daf14b86bcd5068273de2973786aa10c687005e2964e1706c2ac00c552e1ad434139af14b86b14d04e0abe42970d541a0a84e7
  | 6, 0, 10 => 0x52e1aa8270b810d78a5c4e1ab334139ef14b86aa12880273de2db0d541a09c407bc542890d541a09cf87a5c35d2a830139efd5da5c355068273de2970d669a09c157bc52e1ac5341385cf87bc52e1aa84e11df0f4b99c355060273de2970d541a09c0a7bc52e1ad45427072e00bc2a09c2e0a84db154b86aa0d05a273de29706541a09c397
  | 6, 0, 11 => 0x5e2970d541383ad78a5c35506829139efd6fa5c355068273e2a970d541a09c13700435508f409a09cd78a5ced507734139f2b7886aa0d05e2738032b44869a09c1b6bc52e1aa8341383cf7ba5c355068270d9f076fa5c355068273de2970d61aa0d04e7bc52e2f0d54270d0f7ebc52e1ab334139f2564a5c355068273de2a10d59aa0d04e7
  | 6, 0, 12 => 0x5e297414e9385cc00a5c35508f270b980178ac2a0d04e0ab002f10d541a09c116cad123d0d541a09cf78904355068270edc0193a5c1d50681b3002f94b86aa0d0366c9de2df4b4e9a09cf78aed561aa834101ef15da5cad5068273de2970d54238d04e7bc52e1acd341385cf78a5c353c6827021c0193a5c3550942735e2970d6aaa0d04e7
  | 6, 0, 13 => 0x5e2d50d541385cd78a843602a834139f0f4b86c0150602738021a682706c26086c852e1aa83413876e00a5c35506827011af14b86aa1429c1cbde2970d4f270d04e7bc52e1ad43415c76f78a5c35a8681d821c0178a5c34d0360db0030f4b86aa1224e6c9d2e0ea8509a09cf78bad2e1aa834139c0178a8aa0d04e0ab002f15d86aa0d0426
  | 6, 0, 14 => 0xa5d061aa8479a09cf78a5c357ea834139c018a86aa0d04e09b64e9707541a09c1b7bc52e1aa84a1b09cf78a5c355068270c9ef14b9caa13868273de2db0d541a0ba4e7bc52e1ab8541a080f87a5c3550a530139f0377a5c355068223de2971e541f4d04e70052e66a82b93810d78a5cbda8a834139ef15da5c35509c343de29d0d541a0b44e7
  | 6, 0, 15 => 0xbc52e1adb5413830f81bc52e3ca8340f9ef14b86b055068223802f14b86ba4a8366bc435509c409a072f78a5c6a1ad4541a1c0178bbc01504e1735e2970d541e0d04e7bc435a8a8409a09cf78b252e1aa634139ef14b86b5138681dbde297414e9a09c367bc5921aa82d1387cf4b86aa11e68270d9ef14b86aa138390dbde2970d531a0b44e7
  | 6, 1, 0 => 0x5e2970d599a06cd93a5c1d5068270b9ef14b86aa11a68273de2970d629a0ae4e7bc52e1ac53413810f78a5c35b6a8270d9f1978a5ca55068273de2d50d541a09c367bc52e1aa8431a076e00c252e1aa834139af15d924355068273802f14b5a2a0d036600606970d542509cd78a5c3570a834181ef15086aa0d04e043de2bb0d541a0c0407
  | 6, 1, 1 => 0xbc5de00a8341386ce00a5c3554a8270b980195a2435504e1735e2a30d83aa0d04e7bc592971e541a07cf78a8435509c34139c0178a5cbd50681b35e2970d54270d04e7bc52e829d3413872f78a5c7950682d0f9f2b9386aa0d05a273de2a74b86aa0d04e7005fa9713541a09cd4b86aa11e68270e5ef14b86a98d04e09bde2970d54285284e7
  | 6, 1, 2 => 0xbc5be1aa1341387cf78a5c3550942706def15d86aa13a68203de2970d6daa09c397bc52e1ae2341387cf78b54355068270e5ef14b86b153868273de2972f54284d04e7bc52e1ab6541a09ce00bc52e38a8340d9af14b86ba4a84e0abde2974486aa138397bc52e670d542209cf87bc52e3ca8340f9e970d74aa11e68273802f54b86aa09c2a6
  | 6, 1, 3 => 0xcad12830d541a09cf87a5c355060270edef14b86accd04e0ab802f16d541a09c1560052e1a4e1706c10c00c85761aa834139af14b8f2a0d03e09be56890d5429cd04e7bc52e38a8509a09cf78a5ad1506827111f214b86aa0d064273de2970d541a09c167c65e2bb0d541a080f78a5c35509427055f0b4b8f4355068273e4ef14b86b50d03b7
  | 6, 1, 4 => 0x5e21aa63413826c00c552e1aa8270b98010d541385c13043632970d519a09c157bbd2e1ac8541a09cf81a5c35a8a834111ef14b86aa0d04e163de2970d66a70d04e7005e2970d540d85cd78a5c355068270adef16486aa13a5a273e56890d541a09c367bc52e1aa83413834f78bbc015068270e5c0187a5cbd50682735e2971b86aa0d04e7
  | 6, 1, 5 => 0xcad121aa83413872f93bc52e1ac534139e970d5423cd054273802f14b8f1a07c1b6bc52e1aa83413850f81bc52e1a9e34139efd4b86aa13a68273de21aa8409a09c157bc43550813413836f78b7c35426830139ef14b5a2a0d04e173de2971c541a09c1b7bc5de00e9541a09cf78a5ccda8a82b939ef10d541a0b44e213de2971e86b2950687
  | 6, 1, 6 => 0x5e21a681b06c26d78b252e1a9e34139f0378a5c35a8681dbde2970d6faa0d04e7bc52e1aa04e1a09ce00cad2e1aa84a139b154b86aa0d04e1b3de2971c541a09c2e7c55e29733541a09ce00bc5421aa834139af14ba24356668273e56893386aa0d04e7cade2971e541a07cf78b25761aa84e1a1efd78a5c35509c273e1ebb4b86aa0c04e7
  | 6, 1, 7 => 0xbc52e1aa84e1380af78a5c35a8682d0edef14b86b755068273e06970d54284d0447bc5de00a8341509ce00a8c35506827021b274b86aa0d04e24be570f0d541a0b44e7005e297335415c6cd7886aa0fa7b34139ef14b86aa13839043e1ef14b86a78d04e700616970d541385cc00bc575506820055af14b86aa10c680fbe1edf4b86aa0c04e7
  | 6, 1, 8 => 0xbc52e1aa83f9a09cf78a5c3582a84e1a1f0f78a5c35a8681dbe06f15086aa0d04e7005e2bb06541a09cc00bc591505a27055af14b94aa14668273e4e970754270d04e7bc52e1a9e3413826f78a5c35506827081ef14b86aa10c681f38030f4b86aa0c44e6bc592970d6a1a076e00cad2e38a834139af14b86b695068273de2973354284ae4e7
  | 6, 1, 9 => 0x5e2b50d541a09cd95a243550682a139efb4b86aa0d060273802fd4b541a09c156c3d2e1aa84e23c9cf78afd2e1aa834139f0378a5c358a68273802f14b86a989c2e6c0d2e1aa8341102af78a5c35509c478e5c014b541a06c15043616970d541a09c367c0d2e1aa83411036f93ac52e1aa834139f0b4ba0c355068273e4f0f4b54274d04e7
  | 6, 1, 10 => 0xbc52e1aa6341386cf85a5cce1aa834139f0f4b86aa0c04e1f3de2bb0d83aa0d0407bc52e1ab33413810f78b7d2e1adb34139f034b86aa0d044173de26b0d54270d04e7cade2970d4f1a09cf78a5cf61aa834139ef14b86b995068273d2e1aa8479a09c3b7bc52e26a8519a09cf95bc52e1ad334139f2b78aec35509c343de2970d6a1a076137
  | 6, 1, 11 => 0xc9e1e970d542709cf78b243550a32d139c0193ac43550682735e2e34b86ae150687005e2970d1b0b836d78a5c35509c4a139f2778a5c35509c1cbe32970d519a0ae4e7c55e2970d6a1a09cf85a5c35d2a834139ef14b944355068273e0e974886aa0d04e7005e2dea1341382ad87bc52e1ac534139ef14b86ba15068273802f14b711a09c156
  | 6, 1, 12 => 0xbf52e1aa8519a09cf78a5c19506830139c017886aa06c2e09b5e2c94b86b34d04e7cae4e96a84e9a09cf5da5c35508f34139ef14b86aa13a86343de2c90d54218d04e7bc52e1ab34e1a09ce00bed2e1aa8340d1af14b86b34d05a273802970d642a0d0366cade2970d6a1a076f83a5c3550a334139ef14b86aa12c68273de2970d54264d04e7
  | 6, 1, 13 => 0xbc542970d599a09cf81bc52e1aa8389a1ef10d542710268273dbe970d5423cd04e7bc52e7d0d541a09cf78a5c35509734139ef14b86aa0fc68273de2bb4b86b6d504e7bc52e38a84e1a09cf78a5c35509c340fdef14b8f435a8681db802890d541a09c006005e2a10d5427072d8ca5c35469c34139c0178a5c35509c1cb606970d541a0c4447
  | 6, 1, 14 => 0xbc52e1adc541a09cf81bc52e1aa84e0e5c0178b7d2e1ab83435e2971286aa0d04e7bc5423d0d541a09cf78a5cb61aa834139f0f78a5c35505e2738029729541a09c086cad121aa83413876f4b86b21506827055e970d7faa11e68273e4ef14b6daa0d04e7c9de2970d749509cf78a5c359a682704df0f78ad4355068273802f15c86aa0d04e6
  | 6, 1, 15 => 0xbc4821aa8519a09ce00bc52d508634055b2764a5c1d5068273802bb0d541a080086005e2970d5593846c00a5c4d506827021b274b83aa0d05a273e56f10d54218d04e7bc5621aa8509a09cf85a5c35506827119ef16fa5ccd3a68273de2971e86b14d04e7005e2a30d541a06cc00bc52e1aa833939af14b86aa0d04e14bde2971e74aa0d03e7
  | 6, 2, 0 => 0xbc52e1aa83413c9cf93a5c1d50682704de970d541a0c04e23bde2970d541bcd04e7bc52e1aa8341449cf90a5c3550a334139ef15186aa0d04e0abe06970d54270d0447005921aa82d13810d4b86aa11e68270f9ef15886aa0d04e0abde6970d541a09c1c7bc52e3d0d669a09cf78ac43550682706df0f78a5c35509c1cbde2970d54270c44e7
  | 6, 2, 1 => 0xbc52e1a9e3413872f78a5c3550942d139efb4b86aa14668273e16970d541a09c3b70061e96a8301382ad78a8c355068270b9ef16a86aa0d04e203d2e770d5423cd04e7005e2a10d541385cc00bc52d52a8270b9afd77a5c355068273e06f14b86accd04e70064ef14b5c2a0d0d78a5c7950682a0f9ef14ba0a74d04e203d2e1aa8479a09c407
  | 6, 2, 2 => 0x5e2970d4e0e436d78a5c7a1aa8389a1ef15da5c35507a343de2a34486aa0d04e7c3db6970d541a09cf87bc52d68a834139ef14b86b50ea68273de2970d5428d0c687bc52e1abe541a09cf4b86aa11e6827071ef14b86af15068273de297296a2a0d04e7bc592970d542509ce00bc52e1aa84e0e1b0f78a5c35d254273e16970d852a0d04e7
  | 6, 2, 3 => 0xbc5de00a8341809ce00bc52e1acd270b9af164a5c715068273802f16f86b04d04e6bc52e1aa84a13826f78a5c7150682d139c0178b6c3550681b35e2a14186aa0d04e7c652e1aa3341689cf78a5c35508434139f2b78a5c35509c1cb802df0d509a09c0860052e1ae23413810d7886aa1026d34139ef16a86aa0d060273de2c94b86accd04e7
  | 6, 2, 4 => 0xbc5921ad4541689cf78a5c7150682704de970d642a13868273802410d541a09c086c05e2bb0d541a09cf8ca5c3546682704def15d86c01509c3438030f4b86aa0cc4e6bc52e1ab33413826f78a5d021aa834139ef15da5c355068113802f10d3413836136bc52e3d0d60aa0d0f78a5c7a1aa84e0e5e970d542751e68273de297136a2a0d04e7
  | 6, 2, 5 => 0x5e29713541a06cd95bc52e1ab334139c0178a5cbcd04e0db5e2970d541a09c277005e168a83413826c00bc43550942704db2f7886aa0d05a273802f10d749509c136bc5421ae9541a09cf78aed2e1aa634139f074b86b515068273e2a974a86aa0d04e7005e2970d59a7072d78a84ce1aa834139ef16d86aa0d04e0abde2970d54268d04e7
  | 6, 2, 6 => 0x60e970d541a06cd81b252e1aa834111c0178b2435505a1b3002970d541a09c016bc52e670d73aa09ce00c9d2e0ea8270b9b034b86aa0d05a223e56890d54274d04e7bc52e6d0d541a09ce00c643546682704daf14b8f4356668273e57275d86aa0d04e7005e21a813413836c00bc4bd50682704daf15186aa0d04e043de2d74b86aa0d04e7
  | 6, 2, 7 => 0xc9d2e0ea8341386cf7ca5c355068270d9c0178a5c35506a343606970d541a088137005e21aa8270b826d78a5c35a8a83411df0b4b86aa0d04e1f3de2bb0d541a080157cae4edf0d541a09cf89bc52e1aa84e0e5c0178a5c349c2e0db61ef14b99aa0ae4e7bc5761aa83410036f7886bd5509c34139ef15186aa13868273de2af4b86aa0d04e7
  | 6, 2, 8 => 0xbc52e1acb541a09cf78a4c35509c34139c0181a5c35506823b642970d6a2a0d04e7bc52e890d5c2a0d0f83a5c35506827111c0178a5c35c4681b3606f14b982a0d04e7bc4821ad4541a09cf4b86aa146682711def14b86bcd70a8343e2e970d541a09c447c3de2bb4b86aa138f78a5d061aa84e0e5ef14b86aa0e668273dfa970d54284d04e7
  | 6, 2, 9 => 0xbc52e1ad454218d0f64a5c3590a834139f2b87aec355068273e06971e86aa0d0447005e21aa8409385cd4b86b2150682d139c01789043550681b35e2a34b86b50d04e7005e266a82b93826d78a5c35d254270d9c018ca5c35464e173002970d541a088036bc52e1aa84e1709ce00bc43550682002db274b83ba55068273802f14b9995c9c1b6
  | 6, 2, 10 => 0xbc52e1ae9542509cf81bc5461aa834139ef14b86b6d504e1e3e06974786aa0d0447bc4355081341386cf4b86b2150682704def163a5c35509c273de2971e541a0c03e7bc52e670d749509cf78ac43606a834139f194b86a8cd04e1b3803214b86aa0d0366bc5b61aa84e1a09cf7ea5c3566a834139ef177802a14668273e26f10d54204d04e7
  | 6, 2, 11 => 0xbc52e1ab854270d0f78aec35509c34101c0185a5aa0d04e0ab5e2971c74aa0d04e7bc4ce1aa8409a09ce00bc52e1aac541a1af12086aa0d04e173e42970d541a09c447c652e670d519a09cf7ea5c3610a834139f0f4b86b515060273de2b10d541a0b44e7bc5761aa83410010f78a5c3600a84e0e5f0f4b86c2d5060273802f15186b50d04e6
  | 6, 2, 12 => 0xc1d2e1aa8341388af78a5c3550682707def14b86a78d060273de2df0d54218d04e7c0d2e830d541a088e00c3d2e1aa8300d980178a5c355053113002970d6daa09c086bc52e1aa83e1a09cf78a5c353c6827101ef14b86c01d254273de2bb4b86b34d04e7bc52e4d0d541a09cf77a5c35508f34139f214b86aa0d04e173de2970d63aa0d04e7
  | 6, 2, 13 => 0xa5c35509c479a072f78a5c35506827071f274b86aa0d04e263e4ebb4b83aa0d04e7005ee970d541a06cd8aa5c35506831939c014b86a98d04e2235e2a31e86aa0d04e7005e2a113541a09cd93bc5921aa82d139f034b86ba55068223dfaa14b86aa0d04e7bc52e1ad43418076f85a5c3550a334139f0f78a5c35507d273e4e9707541a09c3b7
  | 6, 2, 14 => 0xbc43550813413876f78aed2e1aa84a139ef14b99b513a68273de2970d4e9a0bc4e7bc52e2d0d541a09cf78ba52e1aa834139f0f7886aa13881273e4ef14b86b88d04e7bc52e1aa83413842f78a5c35fea84e0e5c017ea84355068273606f15d86aa0d0407bc52e1aa8341386af78a5c358a6830139ef16f86aa0d05c273e4edf4b83aa0d04e7
  | 6, 2, 15 => 0xc3de2c90d541689cf78a5c3570a83404dc0178a5ca4d04e0db606970d84aa0d0447bc576971c541a09cf78a5c35508c34139c0178a5c35504e0c35e21af94e204d04e7005e2970d6daa06cd78b7d2e1aa84a139efd4ba34355068273e1ef14b89aa0d04e7005e2b10d541385cd78aec3550682e101ef14b86ae150682d3de2970d54270b04e7
  | 6, 3, 0 => 0x5e29713599a09cd78a5c35509d4e0e5f2b4486aa0d04e0dbde2d54486aa0d04e7bc52e1ad4541e8d0f78a5c35b6a8270b9ef14ba25053a68273de2d34b86aa0d04e7bc52e1aa84e0e438f78ac4ce1aa834139c0178a82a0d04e0ab002f14b899a09c1b60052e1aa63413810d78b152e1aa834139ef14b98c355068273de2a30d812a0d04e7
  | 6, 3, 1 => 0x5e2970d431a036c00bcd2e1aa834139af166a5c355068273de2d94b86aa0d04e7bc5de970d6a1a076e00bc52cd04e0d855af14b86aa0dc68273de297414ea70d04e7bc52e1aa8341384af78a5cfe1aa834139c0178a5c3550390e35e6970d54270d04e7bc53e970d541a09cf78a5c35507234139c017e86aa0d04e09b61ef12086aa0d04e7
  | 6, 3, 2 => 0x32b4486aa13868273de2971e54284d03e7
  | 7, 0, 0 => 0x5e2970d54270d03970052e1aa83413826087bc592970d822a0d04e8bc52e1aa83415c9c448005e2970d541a09c057bc52e1b00541a0c04e8bc52e1aa850a70d04e8c3de2ef4b86aa0d04e8bc52e1aa8341382a088bc52e1aa83415c9c1b8bc52e1aa834138360880061e970d541a09c08700002f177802a0d04e6005e2970d54244d04e7c9de2970d6a2a0d04e800592970d541a09c087
  | 7, 0, 1 => 0xc0de2970d6a2a0d04e8bc52e1aa84e1a09c2e8c9de2970d54284d04e800002970d3413836086005e2970d83aa09c2e7005e296a83413872157c65e2970d802a0d04e8005e2970d5428c9c2e7005e2970f86aa0d0367bc52e890d541a0ae4e80064ef14b86aa0d0367bc52e1aa84e1a09c448bc52e1aa8341385c088000032b4486aa0d04e6bc52e1aa84e1a09c1b8005e296a8341386c157
  | 7, 0, 2 => 0x5e2ef0d541a09c137005e2970d54250d04e7005e2970d541a09c0f7bc52e890d54270d04e800003154b86aa0d04e6005e2973386ba5504e7000021aa83413826086005e2df5d86aa0d04e7bc576ab4b86aa0d04e8005e2970d749a0a84e700002f14b86aa0d0366005e296e9541a09c157005e2a94b86aa0d04e700656970d541a09c08700642f14b86aa0d04e7005e2ef4b869a09c1b7
  | 7, 0, 3 => 0xc9de2970d541a09c2e800606f14b86aa0d0367005e2970d541a09c027c3de2970d6a2a0d04e8005e29d4b86aa0d04e700602f14b86aa0d04e7bc576970d541a09c3e8bc52e1aa8341809c3b8bc52e1b07541a09c368005f6f14b86aa0d04e7bc592970d6a2a0d04e8c3de2970d85aa0d04e8bc52e1ad4541a0b44e8bc52e1aa8519a09c3680052e3d0d541a09c087c9de2970d541a09c1b8
  | 7, 0, 4 => 0xbc52e1b0774aa0d04e8005e2970d541a0b4367bc52e1aa83415c9c088bc576970d541a0c04e8005e2c14b86aa0d04e7005e296a8341509c157c0de2970d54284d04e8005e2970d541385c247000030b4b86aa0d04e6bc52e1b07541a09c398bc52e670d5428cd04e8bc52e1ad4541a09c138bc5be970d541a09c3e8bc52e1aa8519a09c398cade2970d541a09c4c8005e2970d541a0ac4e7
  | 7, 0, 5 => 0xcade2970d6a2a0d04e800002f14b86a98d04e6bc52e1aa84e1a0ae4e8c3de2970d54284d04e8bc52e1aa84e1a09c08800002970d541385c086005e2970d5c2a0d04e7005e2bb0d541a09c407bc5be970d541a0c04e8c0de2970d541a09c158c0de2970d541a09c1b80061f034b86aa0d04e70061ef14b86aa0d036700657274b86aa0d04e7005e2c94b86aa0d0367005e2970d541a09c2e7
  | 7, 0, 6 => 0x5e2970d541a0ca4e7bc52e1b005428cd04e8005e2970d541385c267c3de2970d541a09c158bc592970d541a09c448c3de2970d541a09c1b8bc52e3d0d6a2a0d04e8bc52e1aa8341689c448c0de2970d541a09c2e8bc52e1aa8341689c158005e2970d541a0c44e7bc52e1aa8341689c1b8005e21ad4541a09c137bc576970d54274d04e8005e2970d541a06c137005e2ef4b86aa09c2e7
  | 7, 0, 7 => 0xc0de2970d541a0c44e8005e2bb4b86aa138687c3de2970d541a09c2e8005e296a83413876157bc52e1aa8341388813800656f14b86aa0d0367bc592970d541a09c2e800002f14b869a06c1b6bc5de970d541a09c368005e2970d541a0b24e7bc52e1aa84e23cd04e800002f14b8f2a0d03e60052e1aa8341386c087bc52e1b07541a0a84e8005e29733541a0ae4e70052e830d541a09c087
  | 7, 0, 8 => 0x5e2970d34138881b7005e2bb4b541a09c157005e2970d541a09c477cade2970d541a09c1b8006570f4b86aa0d04e7005e2970d3413836157bc5de970d74aa0d04e8c9de2970d54270d04e80052e1ae9541a09c087bc52e1aa8341809c408bc52e1aa8341385c138005e2971e86aa0d0367bc5de970d541a09c398005e21aa834138260f70052e1aa83413872087bc52e1aa8341809c3e8
  | 7, 0, 9 => 0xbc52e1b07541a09c3b8c0de2970d541a0ae4e8cade2970d541a09c2e8bc52e1aa84e9a09c408bc52e3d0d541a09c448bf5e2970d541a09c398c65e2970d541a09c3e8005e2df4b541a09c157bc52e270d541a09c398bc52e3d0d541a09c1b8005e21aa83413888137005e2970d54270d04e7005e21aa8341382a137005e2970d6a2a09c2e7005e21aa83413836137cade2970d862a0d04e8
  | 7, 0, 10 => 0x5e21aa83413826127bc592970d541a0ae4e800002f14b86b50d03b6bc592970d541a09c088c0de2970d54270d04e8005e2972e86aa0d04e700002f14b86aa06c2e6005fef14b86aa0d04e7bc52e3d0d541a09c2e80052e1b00541a09c0870052e1aa8341509c087005e2a14b86aa0d04e7bc52e1ad4541a09c368005e29744869a09c1b7c65e2970d541a09c40800002f14b86a78d04e6
  | 7, 0, 11 => 0x5e2970d541385c1b700002f14b86aa0d04e6bc52e1aa83415c9c138bc52e1aa83413826088005e2974186aa0d0367bc52e1aa8341386c308bc592c34b86aa0d04e8bc52e670d6a2a0d04e8005e2970d541385c2a7c3de2970d541a09c478bc52e1ad4541a09c398005e2970d542849c2e7c3de2970d541a0ae4e8bc52e891e86aa0d04e8bc52e1aa84e1b4d04e8bc576970d5428cd04e8
  | 7, 0, 12 => 0x606f14b86aa0d04e7bc52e830d541a09c448cade2970d541a0ae4e8bc52e1aa8341386c158005e296a8341809c157bc52e1aa8341386c1b8005e2970d3413836087005e2970d541a0723670052e1aa83413810077bc52e1aa8341385c238005e296a8341388015700002f14b86b14d04e6bc52e1aa8509a09c368005e2970d541385c15700002f15086aa0d04e6c3de2970d54270d04e8
  | 7, 0, 13 => 0xbc52e1aa834138721b8cade2970d54270d04e8bc52e1aa8519a09c3e8bc52e830d541a09c2e8005e2970d4e1a09c1b7005e2970d541a0be4e7bc52e3d0d541a09c088bc52e670d54284d04e8005e2974486aa09c2e70062af14b86aa0d04e7c9de2c94b86aa0d04e8bc5de970d541a09c3b800002f14b86b34d04e6005e2970d74aa0d03670052e1aa83413876087c9de2970d541a0b44e8
  | 7, 0, 14 => 0xbc52e1ae9541a09c448bc52e3d0d54270d04e8005e2970d541a0cc4e7bc52e1b07541a09c408bc52e890d541a09c368005e2970d541a06c2f7bc52e894186aa0d04e8005e21aa834138260e700576970d541a09c0870061ef14b86aa0d04e7c9de2970d541a09c138005e21aa84e1a09c137bc52e670d541a09c1b8005e2970d541f4d04e7bc52e1aa8341386c2e8bc52e1aa8341386c338
  | 7, 0, 15 => 0x5e21aa84e204d04e700002f14b869a09c1b6005e2970d5415c9c2e7bc52e1aa8341385c22800002f14b86aa138396bc52e893386aa0d04e800003274b83aa0d04e6005e2c74b86aa0d04e7bc52e890d541a09c398c0de2c94b86aa0d04e8bc52e1ae9541a09c2e80065af14b86aa0d04e7005e2970d541a0a8367005be970d541a09c08700616f14b86aa0d04e7005e2970d541acd0367
  | 7, 1, 0 => 0xbc576970d6a2a0d04e80052e1aa8341387c087c4de2970d54270d04e8bc52e1aa83415c9c368bc52e830d541a09c088005e2970d542709c2e7bc52e1aa8341386c348005e2ef6f86aa0d04e700002f10d541a09c136c3de2c94b86aa0d04e8bc52e1b00541a09c448bc52e1aa8341509c448c3de2970d541a0b44e800656f14b86aa0d04e7bc52e1aa8341509c158bc52e1b00541a09c1b8
  | 7, 1, 1 => 0xbc52e1ae9541a09c08800002f14b8e2a0d04e6005e2c94b869a09c1b7c0de2971e86aa0d04e8005e2970d541d4d04e7005e2970d341689c1b7bc52e1aa83413872088bc52e830d54270d04e800002f14b86accd04e6005e2c90d541a0b44e7005e2970d541a09c0370052e1aa83413880087bc52e890d541a0a84e800606f14b869a09c1b700002f14b86aa1284e6c3de2970d541a09c138
  | 7, 1, 2 => 0x626f14b86aa0d04e70052e1aa84e9a09c087c9de2970d541a09c368c3de2971e86aa0d04e8005e2970d3413836137bc592971e86aa0d04e8bc52e670d54270d04e8bc52e1aa84e1a09c398005e2df4b86a74d04e7005e2bb4b86aa0d0367005e2c90d541a09c137005e296a8519a09c157005e2970d541a09c3d700002f10d54204d04e60064ef14b86aa09c2e7bc52e1ae9541a0ae4e8
  | 7, 1, 3 => 0xbc52e1b0054270d04e8bc52e1aa84e1a0a84e8c9de2970d74aa0d04e8bc576970d541a09c2e8005eaf14b86aa09c2e700003034b86aa0d044600002f10d3413836136bc52e1ad4541a09c408c9de2970d541a09c39800656f14b869a09c1b7005e21aa83413826107bc52e1b00541a09c088bc52e1ad4541a09c3e8bc52e1aa8341509c08800656f10d541a0b44e7c65e2ef4b86aa0d04e8
  | 7, 1, 4 => 0x5e2970d652a0d04e7005e2970d541a0c0367c3de2974186aa0d04e8c0de2970d541a09c398bc52e1aa8341689c368005e2970d541385c137005e2970d541a09c227005e2970d541a080367005e2970d541a0a64e7005e2970d541a07c367c0de2974186aa0d04e8005e2a10d541a09c397cade2971e86aa0d04e8bc52e1ad4541a0c04e8005e2970d541689c2e7005e2970d541a09c397
  | 7, 1, 5 => 0xbc52e1aa834138802e8005e2a34b86aa0d04e7005e2970d54274d0367c3de2970d74aa0d04e8bc576970d541a0ae4e800002f10d541385c136bc52e1aa8341387c2e800002970d642a0d04e6c3de2970d541a09c398005e29b4b86aa09c2e7bc52e670d541a0b44e800002f14b869385c1b6bc52e1aa83413880158bc52e1aa834138801b8bc592970d54288d04e8bc52e1aa83415c9c3b8
  | 7, 1, 6 => 0x2f15186aa0d04e6cade2970d541a09c398bc592970d541a0a84e8005e2971786aa0d04e7c65e2970d541a09c158bc52e1aa84e9a09c448005e2970d541a09c387005e296d4541a09c157005e21aa8341386c137c0de2970d802a0d04e8c0de2970d541a0a84e8bc5be970d541a0ae4e8cade2974186aa0d04e8bc52e670d541a09c138005e2970d341386c1b7005e2970e86aa09c2e7
  | 7, 1, 7 => 0x5de970d541a09c087bc52e1aa83413880088c9de2df4b86aa0d04e8005e2970d599a09c397005e296a8509a09c157bc52e890d54274d04e8bc52e3d0d74aa0d04e8bc52e1aa8341509c138c9de2bb4b86aa0d04e8bc52e3d0d541a09c398bc52e1aa84e9a09c2e8005e2670d541a09c137005e2970d541385c237c3de2970d54294d04e8bc52e1aff54270d04e8005e2970d541a09c4b7
  | 7, 1, 8 => 0x5e2970d541a09c007bc52e1b07541a09c1b8c3de2bb4b86aa0d04e8bc52e830d541a09c3980061e970d5428cd04e7bc52e1aa84e9a09c088bc52e1aa84e1a09c1c8bc52e1b0754284d04e8005e2973386aa09c2e700002f16d86aa0d04e6bc52e3d0d541a0a84e8005e2970d5428cd0367bc52e1aa84e1a09c408005e2970d702a0d04e7cade2970d541a0a84e8005e2970d541386c2e7
  | 7, 1, 9 => 0x52e1aa8509a09c087005e2ef4b86aa0d0367c0de2970d541a09c408005e2df0d541a0b44e7005e2970d541a09c1c7005e2bb4b869a09c1b7005e2973354274d04e7005e21aa8341387613700002f14b86ae15068600002f15d86aa0d0406bc52e1aa8519a09c2e8bc5de970d6a2a0d04e8c65e2970d54270d04e8005e2970d541a09c437bc52e1aa84ea70d04e8bc52e670d541a09c368
  | 7, 1, 10 => 0xbc52e1aa8509a09c448cade2970d54274d04e8005e2ed4b86aa0d04e7bc52e3d0d541a0c04e8c65e2970d541a09c138bc52e670d541a09c3b8bc52e3d0d541a09c408c65e2c94b86aa0d04e8bc5de970d541a09c2e8c0de2970d54274d04e8bc52e1aa8519a0ae4e8005e2970d54138762e7bc5de970d541a09c448bc52e1b0074aa0d04e8c3de2970d541a09c3e8005e2df0d541a09c137
  | 7, 1, 11 => 0xbc52e1aa84e9a09c398bc52e1aa8341509c3e800002f14ba0a74d04e6bc52e1b07541a09c138bc52e890d541a09c1b800002f14b3413836156bc52e830d541a09c408bc52e1aa83413836158
  | 8, 0, 0 => 0xcade2970d541a09ce00bc52e1a682706db0f78a5c355068273e06f14b86aa0d04e7005e2970d541a09cd93bc52e1aa834139ef14b86aa13868273de2970d541a0ae4e7bc52e1aa83413810f78a5d121aa834139ef14b86aa0d04e173de2970d541a09c447bc52e1aa83413836f78a5c3550a134139c0178a5c3550681b35e2970d6a2a0d04e7
  | 8, 0, 1 => 0x632f14b86aa0d04e7bc52e1aa84e9a09cf78a5c35506827101ef14b86c015068273de2970d541a0a84e7bc52e1aa83413872f78a5d061aa834139ef14b8f4355068273802f10d541a09c136
  | 9, 0, 0 => 0x2f14b86aa0d04e6
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
  | 0, 0 => 0xe00ff000000001cefefef00000000e0f0c00000ffffffff00000e31e1f1c00000fff1f0f300000ffffffff00000000fffff
  | 0, 1 => 0xe0e000e0f0c000000001e0e300fff000fff1f00fff000fffff00fff000e1f1c001f1fff1f0f300f8f000fffff00000ffffffff
  | 0, 2 => 0xe31f1e0f1f0f3e3181fff1f0f31f07f1ff00fff1f071fff1f0f300fff000fffff00fff0000000000f8e000fff0c00f80000ff000
  | 0, 3 => 0xfffffe31e1f1cff1f1e31e1f1cff1f1fff1f0f3ff1f1e3101010e3f8fe0fff00ffffffe31e1f1ce3f8fe31e1f1cff1f1fff1f0f3
  | 0, 4 => 0xff000fff1e0e3ff000fff00000e0180fce1f0e3e0180e001f0001c0701f0000f0000001ce1e0e3ff1f1e3f1f013ff1f1fff010f3
  | 0, 5 => 0xe0e000e0f0cff1f1fff1f0f3ff1f1e001f000ff1f11f0000f0ff1f11ce1e0e3ff1f100000000ff180fff1f000ff070fff000f0
  | 0, 6 => 0xe0e1cefefeffffffe31e1f1cfffffe3100000fffff00000000ff000e3100000fcff0e30e1f10e0f8ee00e1f0c1c07003000f10
  | 0, 7 => 0x1e000000000001e000000001c0000e00000000000000000001c0000e0ff1f1e31010100000000000000fffffffffffff
  | 0, 8 => 0x1ce1e000000001ce000e0000001ce00000000001ce00000
  | 0, 9 => 0x1cefffff000001ce1e0e3000001ce00000000001ce00000000000001e0000000000000000000001c0000e00000000000000
  | 0, 10 => 0xe00000e00000000000000f0000000000000000000000000f00ff1f1fff1f0f300e0e1cefefef001f11ce1f0f3000001cefefef
  | 0, 11 => 0xe00000e00000000000000f0000000000000000000000000000001f10001f0f3000000000000000e00000e0f0000e00000e0000
  | 0, 12 => 0xe0e0000000000e0e0000000000e0e000e000000e0e0000000000e0e0000000000e0e0000000000e0efff1f0f300e0e00000000
  | 0, 13 => 0x1ce00f00000000001ef00000001c000fe00000000000f00fffffe31e1f1cfffffe31e1f1c00fff000e1f1c00e0e000e0f0c
  | 0, 14 => 0xe00000fe00000e00000e000000e0e1c0e0fec00e0e1c0000e0000001c0000e000e001c0e00e0000001ce1efe30000000000f00
  | 0, 15 => 0xe001cefefe300e001c0fefe000e0e000fef0c000000001e000000000000000000e001cefe0e300e00000e000000e001cee0000
  | 1, 0 => 0xe0e1ce00000000001ce1e0e3000001ce000000000000000000000001ce000e0000001ce00000000001ce000000000000000000
  | 1, 1 => 0xe0e0000000000e0e1cefef0c00e001cefe0e300e001cefe000000001ce1e0e3000001ce00000000001ce0000000e0e1cee0f0c
  | 1, 2 => 0xe0e1cefe0e300e0e000fe00000e0e0000000000e0e000e0f0c00e0e0000000000e0e000e000000e0e1ce1e0e300e0e00000000
  | 1, 3 => 0xf000000000000f00000000000000000e0e1cefefef00e0e1cee0f0c00e0e1ce0000000e0e000fef0c00e0e000e0f0c
  | 1, 4 => 0x1c0701f0000001c070000000001c07000000f001c0701c0000e01c070000000001c0001f000f001c0001f000000000001c000fe0
  | 1, 5 => 0x1c0001f0000000000000000f000000000000000fffffe31e1f1cff1f1fff1fff3ff1f100000000e0180e001f0001c0701f000ff0
  | 1, 6 => 0x1e00000000000000000000000000000000000001e0001c0701f000ff01c070000000001c070000000001c07000000000
  | 1, 7 => 0x1c0700001e0001c0001f01e0000000000000f00000000001ef00000000001e0000000000000f000000000000000000001ce1e0e3
  | 1, 8 => 0x1c0001fe1e0001c0701fe00ff01c0701fe00ff01c070000000001c0701ce000001c0001fe00f001c0001fe1e0e31c0001f000000
  | 1, 9 => 0x1c0701f000ff01c070000000001c0701f000ff01c070000000001c07000000f001c0701ce1e0e31c070000000001c07000000000
  | 1, 10 => 0xe001c0e00e01c0701fe1eff31c0701fe00ff01c0700001e0001c070000000001c0701f000ff0
  | 1, 11 => 0x1ce0e1f0000001c0001f0000e01ce70000e00001ce001f0e000000e0e000e0f0c00e0e0000000000e0e000000000000000000f00
  | 1, 12 => 0x1ce7e000e0f0c1ce7e1c0000e01ce001f0e00001c0701f000ff01c0701f000ff01c0701f000ff01c070000000001ce0e1f0e0f0c
  | 1, 13 => 0x1ce1e0e3000001ce1e0e3000001ce0000000e0e0001e000000000001e00000e00000fe0001ce7e1f0e0ffc1ce7e000e0000
  | 1, 14 => 0x1c0701f000ff01c0701ce000001c0001fe000001ce70000e000000e0e1cefefef00e0e000e0f0c00e0e0000000000e0e000e0f0c
  | 1, 15 => 0x1ce7e1fefefff1ce7e1f0e0ffc1c0701fe1eff31c0701f000ff01c070000000001c070000000001c0701fe00ff01c0701ce00000
  | 2, 0 => 0xe0f8000000000e0000e0000000e0000e0000000e0e00e00e0000e0000e0000000e0000e0000000e0000e0000000e0000e0000000
  | 2, 1 => 0xfffffe31fff1cffff1fffff0f3e0f80e00ff000e0f80e0000000e0f80000e0000e0f8000000000e0f800001e000e0f8000000000
  | 2, 2 => 0xe0000fce1e0e3e0000e0000000e0f801c0000e0e0000fc0000e0e0f80e00ff000e0f8000000000e0000e0000000e0000e0000000
  | 2, 3 => 0xe0000e0000f00e0f80fceff0e3e0f80fce00000e0f80e00ff000e0f801c0000e0e0f801ce1e0e3e0f801ce00000e0000e0000000
  | 2, 4 => 0xe0e0ee0000000e0000e0000f00e0000e0000000e0e0ee00e0f0ce0000e0000000e0000e0000000e0000e0000000e0000e0000000
  | 2, 5 => 0xe0f8ee00ff000e0f8e000e0f0ce0f8e0001e000e0f80e00ff000e0f80e00ff000e0f80e00ff000e0f80e00ff000e0f8000000000
  | 2, 6 => 0xe0f80fceff0e3e0e0efcefefefe0000fce00000e0000fc0000e0e0f8ee00fff0ce0f8ee00ff000e0f8ee0000000e0f8ee00ff000
  | 2, 7 => 0xfcff01c01e0e0fcf801f000000fc070e0000000fc000ff01e0e0e0f8efcefffefe0f8ee00fff0ce0f8ee00ff000e0f8e1cefefef
  | 2, 8 => 0xff0001ce00000ff00000000000ff000000fffffff00000000000fc070e0000000fc070e0000000fcff0ff0ffff0fcff0ff000000
  | 2, 9 => 0xff00000000000ffffffffe1f1cff1f1fff1f0f3ff1f1fff01010ff000fff00000ff00000000000ff0001ce00000ff00000000000
  | 2, 10 => 0xff000e001e000ff00000000000ff00000000000ff000fff1e000ff0000001e000ff000fff000e0ff000fff000e0ff000fff00000
  | 2, 11 => 0xffe00000e0000ff000fff00000ff000fff1e0e3ff000fff000e0ff000fff00000ff000fff00000ff000fff00000ff000fff00000
  | 2, 12 => 0xffe0efffe0f0cffe0e1cefefefffe0e00000000ffe0efffe0f0cffe0e000e0f0cffe0e1ce00000ffe0e00000000ffe00fffe0000
  | 2, 13 => 0xff070fff00ff0ff070fff00000ff070fff00000ff070e0000000ff0701ce000e0ff000fff00000ff00000000000ffe0effffefef
  | 2, 14 => 0xfff80fffff000fff80fff00000fff801f000000fff80000e0000fff801ce1e000ffe0efffe0f0cff000fff1e0e3ff000fff00000
  | 2, 15 => 0xfffff0001e000fffff00000000fffffe31e1f1cfffffe3100000fffffe00e1000ffffffff1f0f3fffffe3101010fffff00000000
  | 3, 0 => 0xfffff000e0f0cfffff00000000fffff00000000fffff000e0000fffff000e0000fffff00000000fffff1ce1e0e3fffff1ce00000
  | 3, 1 => 0xfffff000e0f0cfffff00000000fffff1ce1e0e3fffff1f000ff0fffff1f000000fffff00000000fffff1cefefeffffff1ce1e0e3
  | 3, 2 => 0xffffffffe0f0cffffffff1e0e3ffffffff00000fffffe0000000fffffe00ff000fffffe00e0000fffffe0000000fffffe0000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xea4ef250000006d7ee76d00000453e272d00000eb5cd65800000c31c161800000aa40d05000000657aa52d0000000067375
  | 0, 1 => 0x62600062b2500293000361e7007e700073a170056400067b750056400041a10001d1aa41d0d2002830007737700000ef7ef77d
  | 0, 2 => 0x211d120c1d0d221081aac1d0520f03f15b00daf05011bac0d0d2007f700077bf7007f700010882007e600077b75007c000077250
  | 0, 3 => 0x9056482041a1090140c31c161890140aa40d050901408200101063a8b60fba00f4a82c41180c0842808c31c16182509130c18082
  | 0, 4 => 0xb5091bac1c0c2b5000bac08000b51d1bac1d0d2b01c0aa41d050941509a0050d02509138c1c0c2b11c1a2c190129515192801092
  | 0, 5 => 0x4ac2c411c0e08b51d1bac1d0d2b51d1bac1d0d2b51d19a8150d2b51d138c1c0c2b51d110810082b51c0bac1d050b5150bac0d0d0
  | 0, 6 => 0x6fcbd79ddcecadad6cc31c1e18dad6cc3180c08dad6c00000800da808c3180408d8d64c30c1e10dad6cc31c1e189856483041e10
  | 0, 7 => 0x202822c63e165202802843e040042121c2261e5002020c226165040101c0041e090342862231350020204222125ffdfdfbdddeda
  | 0, 8 => 0x2529314a321a72529314a1008225293108320822529310810082252803ce3e040250103ce0c1e0252023ce2a125250003ce08000
  | 0, 9 => 0x252933ce7f3f7252933ce3e1e7252933ce3a1a7252933ce180822529338c3e0c22529338c18082252931c8141e225293188140c2
  | 0, 10 => 0x40e00400e22000862605262f2500602042623250842405040f20b53d3bee3f1f7256b73ce7ebe7253d33ce3f1f7252937dffe7ef
  | 0, 11 => 0x4ae08453e26084ac2c453c0f284ac2c45380c084aa0a453a252d4a9d9453954da4a8084538040848e24450e2f2040e02442e2325
  | 0, 12 => 0x4ae2e453a2d2d4ae2e45380c084ae2e400e2a004ae2e400808004ae2e00040a004ae2e042229254ae2eaa40d8504ae2e00000800
  | 0, 13 => 0x2d4243de48f20286a42d47ef600c4341d044fe00c43415040fa0daf6ec73e3f3ddad6cc73c1e184af6e453e3f3d4ae2e453e2f2d
  | 0, 14 => 0x60e80684fe24060e80400f22004ee3e5d3e6fed4ee3e1c0049e04e8185d3845e844e105c0e63e02d6b73de7efe72d6b715850fa2
  | 0, 15 => 0x6deb77defefe76ceb47d4fefe06aeae6d7fef6d6aa886d7be4486a8086d78840865e937cefe3e765e93508f228265e007ceea200
  | 1, 0 => 0x6fe2e3ce088006fa9b7dfbe5ef6fa9b7df9848a6fa9b55b9048a6f8187df8c5e86fa0a7dfaa52d6f8087df884086f80855b80408
  | 1, 1 => 0x6febf108108826feae7dffef6d6fe9b7dffe7ef6fe887dffe6486fe9b7dffe7ef6fc3c7df88c886fc087dfcc6486fe2e7dfeaf2d
  | 1, 2 => 0x6febf7cefebe76febf78cfeac26febf78c988826febf55bf2faf6febf55bb2daf6febf508f2a826febf3ce3e9e76febf14a329a7
  | 1, 3 => 0x9c5749f045ff0985648f045f70905408a0452506febf7dffefef6febf7dffafaf6febf7df98c8a6febf7dffefef6febf7dffafaf
  | 1, 4 => 0x9c5749f000c809c5749a045ad09c57415040fa09c5741c0049e09c574100008809c4249f040f209c0009f0004009c5749f045ff0
  | 1, 5 => 0x9c2029f222525987668f267f75907428e267375dad6ccb1c5e58bd5f5bfc5dff2bd5f510810882b05c0aa45d2509c5749f045ff0
  | 1, 6 => 0xb57d3bac7f2d2b57d39a8552d2b57d310810082b07c0aa47f2509c7769f267ff59c7769e267bf59c7769a067ad09c776142229a5
  | 1, 7 => 0xbc7f43843e8c0bc280bf43e440bd7f79f855ff2b87e6af67ff75b87c0af67f650b8564af64df70b8564aa44da50b57d3bee7f3f7
  | 1, 8 => 0xbd7c0bfe7f650bd776bfe6fff5bd574bfe4dff0bd574bac4dad0bd5743ce08880bd626bfe6af25bd293bfe3e5e7bd2939f810482
  | 1, 9 => 0xbd7f79fa55ff2bd7f79ea77bf7bd7f79f855ff2bd7f79a855ad2bd7f715a72fa7bd7f73ce3e9e7bd7f714a329a7bd7f710810882
  | 1, 10 => 0xdad48cf3c5658da808cf380408d4f52de2e73f5bd7f7bfe7fff7bd7f7bfe5dff2bd7f7bac7fad2bd7f7bac18882bd7f79fa77ff7
  | 1, 11 => 0xdee2e9f000c00dea1adf3a65eddcf74500e2a80dce00df0e2600daf6ecf3e7f7ddaf6e8a045a50daf6e00000800dad6ccf3c5f78
  | 1, 12 => 0xdef7e553e2faddef7e1c2269e5def48df3e7658def7edf3e7ffddef7edf3c5ff8ded7cdf3c5ff8ded7cda0c5ad0dee2edf3e2f2d
  | 1, 13 => 0xfffdbfffff7ffffa9bfffbe5efff808fff88408fafeeaa47fa50fafc8ef7ff658f0fc0ea4ff250def7edf3e7ffddef7eda0e7ad0
  | 1, 14 => 0xffd7cdfbc5ff8ffd7c7df88c88ff808fff88408fdff7508f2a82ffffffffffffffffffdfbf7ffffffff9a855ad2fffff55bf2faf
  | 1, 15 => 0xffffffffffffffffffdfbf7fffffffffffffffffffff9f855ff2fffff55b90c8afffff10810882ffd7cfffcdff8ffd7cfffcded8
  | 2, 0 => 0xf0fc000010000f0d40ea4cd250f0d40ea488000f0e00ea4ea200f0a80ea498000f0800ea48c040f0a00ea4aa000f0800ea488000
  | 2, 1 => 0xfafeceb5ffe58f5fd1facff2d2f0fc0ea4ff250f0fc0ea498000f0fc0400f2200f0fc040090000f0fc02843e040f0fc000032000
  | 2, 2 => 0xf5a93feebe1e7f5a93fac98082f4fd01c0141e0f4810fe48c1e0f0fc2ee6ff375f0fc204232125f0f42ee6ef375f0a02ee6aa125
  | 2, 3 => 0xf8c24ef4c8f20f5fd3feeff3f7f5fd3fee98082f5fd3facff2d2f5fd39e8553f2f5fd33ce3e1e7f5fc03ce18000f5fd3facdd2d2
  | 2, 4 => 0xfaf6eea4cda50fad6cef7cdf78fad48ef7cd658fae2eef7eaf2dfaa8aef798408fa808ef78c568faa0aef7aa52dfa808ef788408
  | 2, 5 => 0xfafeeea4ffa50fafee453f2f2dfafee2c63e965fafecef7ffe58fafcaef7ff77dfafc8ef7ff778fafc8ef7ff658fafc845390408
  | 2, 6 => 0xfffdbfffff7ffffebfffffefefff808fff88408fe818ff78c5e8fafeeef7fff7dfafeeef7ffe58fafeeef798c08fafeeee6ffb75
  | 2, 7 => 0xfcff43c43e9e0fcfc09f010400fcd74fa488880fca90ff4be5e0ffffffffffffffffffffffffffffffffacffad2fffff7dffefef
  | 2, 8 => 0xff8083ce08000ff80814a00000ff80810867375ff80810800000ffffffff98c8afdff7fac98882fcff4ff4ffff0fcff4ff498c80
  | 2, 9 => 0xffa0a14a22125ffd6cfffc9e18ff9d9fff9d4daff948fff89418ff808fff88408ff8089a800000ff8087df88408ff80850880000
  | 2, 10 => 0xffa9bfacbe0c2ffa9b55bb25afffa9b10810082ffa88fffbe448ffa8838c3e040ffa1afffae5edff818fff8c5e8ffa0afffaa52d
  | 2, 11 => 0xffe08508e2200ffe0afffea72dffa9bfffbe5efffa9bfff9c5eaffa9bfff9c4caffa9bfffba5afffa9bfffba48affa9bfff9848a
  | 2, 12 => 0xffebfffffafafffebf7dffefefffebf10810882ffe2efffeaf2dffe2e55be2f2dffe2e3ce2a925ffe2e10800800ffe08fffea608
  | 2, 13 => 0xffd7cfffcdff8ffd7cfff88da8ffd7cfff88c88ffd7cfaccdad0ffd7c3ce0c9e0ffd48fffcd658ffd489a845250ffebfffffefef
  | 2, 14 => 0xfffc8fffff658fffc8fff98408fffc89f855650fffc855bf2608fffc83ce3e040fff6efffeff7dfffdbfffff7fffffdbfff9848a
  | 2, 15 => 0xfffff38c3e8c2fffff14a329a7fffffd39d1e9afffffd3990c8afffffd28d1a92fffffbac1d8d2fffff92811892fffff10810882
  | 3, 0 => 0xfffff55bf2faffffff55bb2daffffff55b90c8afffff54af2ba7fffff508f2a82fffff14a72ba7fffff3ce3e9e7fffff3ce18882
  | 3, 1 => 0xfffffdfbf7ffffffffdfb90c8afffffbee7fbf7fffff9f855ff2fffff9f810c82fffff9a855ad2fffff7dffefeffffff7dfbedef
  | 3, 2 => 0xfffffffffafafffffffffbedefffffffff98c8affffffffddedaffffffacffad2ffffffacfaa82ffffffac9c8c2ffffffac98882
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 52 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 52 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 408 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 408 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 408 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 408 then wireAt i else 0
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
  | 4 => 28
  | 5 => 473
  | 6 => 1530
  | 7 => 429
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xc6af05b9bd17e3a7afcd51f4ab2ed927ab12b0df8bd732db81d53f8a80ca8fbf78bd379d70e7d8f462250d915f47b959561f08694e3aad4b420a64ab407a5daf205cc7cf1f9f07d41c501087197c925a172363c7121403cf0fde8d05084d1e4f079d7a75067fcdf006126173040f212d
  | 5, 0 => 0x1052a5ff1016abb3100eb51c0fe749af0fb8ab870faa77070f8499530f672d690f564f730f46fe910f415ad90ee25c460ee0af2a0e7545940e56fe570e39926d0db432850d9e19500d8627fa0d83c6990d6903d40d47cafd0d0b45210c405bc60bb0c3ae0b768ece0b551fb20b4536de0acb84370a9b49120a75789c0a41d8c409248f9408b575e4088521e2084bb82d07f4bdbf07c081c70772bb3e075140fd074cee0b06ff5f2206ce7e4f06b922e4064bab2605d9946205bc287805b864970562713e0414a35502dc1b2602c8dd270274c39c0242b7970226934702204f5101d29fcd01c22df601b2c4c6018267cf01013f36007d93d80044916d00272583
  | 5, 1 => 0x2775a7642705880d26befc402616581725f712e925663b0e255d72822548cf24249bda2023ee01b8233153392304f17122df9e0e220c243b21b339f321b04b48219f06a121819ab7217c18ce20bd424e2075da64204bdfba203fef5c203f350c1f2c9cf31ef254801ed32ef81e06e3f41d1c780a1bf750b41bc24f8a1b8129591b6505171b5300e41b3ab7121aedcb0e1ae2b9091a9569301a13e99e19705bce19169d3319009fff18c37efc18611f4a17af690017989514178e4a2c16f1c8b216e6d2c2167df75e16667d6d1658de3316052fbe150d4cfa14abe851147df0991467f41e1415238712cc1c5512aced29123f979f12279d24116a8758110e4b74
  | 5, 2 => 0x3ae782143a9646163a3e996d39d021a739c5c12539ab184e38e1164638bbbf8c382d00c137edc5f637b9fc1b377ab9dd372f8b5f364e56b0362bcb463602739135e7ff7635c9c57835a96a46358f6bef3575685835554bd23515beef35099e56343096ad342691893366c242335802fd32d6b502328fba18325bb8f131479f313115c9303107ca4930b4f53230a6565630378bbb300bb48d2fbc30502ed537322eadcace2e84d2cd2e124b852dde33dd2d636b692b6874ff2b66c1882b06dce52adb98fe2a7f696e2a76e8352a60e87e2a438fa12a347f192a3198e02a272d5b2a23da6e29808263293a8985291d1d9b28b0dc0f28732d7b28627e8a2798ce9c
  | 5, 3 => 0x529efe0851ef2992519ffb99519fb45c518a3b31514e1f2050d1414c50a0531c503e7b63500122f84fd7eac94f57f3d24f0d9c4b4e62b0254dfe08b04beee6fc4bc38b784bb9e57a4b81a28f4b6e21e64a55e64349fd469d49a0b8ec4934b96c49129c2f47d3da5547c3a69247bbe7434705cf5646f0214b46d5ab81465781a14623350345e92e5b45d91ef145ce926e459ecff74597d6de4574949345577d4d4551190a4516803644ae3fb043e9290d43bb1b0b436ccacc435117db434ac03242e7ad3142b779a3422eb48341bf37ea41262c3d405f52873fe776d33f22b8393ee0318d3e01209b3d99f2943d7b67de3d30bc313d149ab03c9d75a23bc2146d
  | 5, 4 => 0x6daa31ab6cdf2d166cba734f6bcf90f36afac8926aa8731b69acc53667de5e2e673394256713ea066658f13a651cffbd64e6ab0264e0c49164bac8366479564e643988c963f9e424635f4efc6357134663474bf462a04737629d6705623e1247620020f661f5a73b618a6a105ffd4b0a5f9defbf5e9b3ccc5e02d08d5dca4c075d76ae0a5d5624535c9f2bce5c87800c5bbb72fe5b3bed485ae7f84c5aa8a6b95aa68a9559e29b7259dd50c859d395c759be44955998eb6058f528b7587328fb583a210d57d6023c57a5936e574085e656f8c50256d8d8bb56b15356569dbc4456811f7b567d130c55e38eb7552df35454ea9893541df39b53e2703d5318541d
  | 5, 5 => 0x8f9864378ed083598eadbcbc8dd166b68d9ceb9f8d65f46e8c76bee98c6170088b6f2f0e89db0760896fa3ea88368716862ff0fc85c2d5988576a604854099a384f9389d84bcf21883aca2a8831d6c2c82ebf5a881999d008179416181663bcd814e51e280b2170f8022937a7fed880f7f6313a77f24c13b7ef470087dd1112a7da6b7ed7da4ff0f7d39e6137cf270267ced496e7ce877917cc5294b7c13cf467bbe5e307bb7eb767a92749f7a85129f7a03bd0e7924126d78b8fe8c783597a076a6f2e87680fac474e00fc4731825f57238707e71b9f521716e44967123e9af7060d574701596636fe675ef6fdc96956fa78ebe6f80bd776f00fbc36db2a4bb
  | 5, 6 => 0xca1f5955c9cb70f2c5158df3c3fe745ac3c15af4be95f8dfbd8e396cbb03c57ab8745914b8554800b7a1fd24b7610a65b66dbaabb5fb4010b427f6dfb3e461b2b344f1d4b32bad84b23370d8b08b963db0605e43afd87cd4ae6954e3ae27cbe2ac377ad1ab719c89ab47af95ab2d8538aa5b1640aa4d3edba968d4e1a8a9dbf0a879ea9da8112672a6669c95a4c39a54a3d30303a3c65a94a1c1ac7ea11e14dda04a320da03691efa02420769fa732239f0a53779d1b6c029d01d3cd9c49c90a9c1f10a99a3e92c299766af8996a2a2d993a456c98a19efa989a69279867cc6a96db33259623f904947d9aae9475d27893fd123c935a49219205c37090862484
  | 5, 7 => 0xfadf00caf9acd0faf37019b2f0f8df95ef5e1cefef3144deeab341b9e937df5de907f834e901b450e7430d79e1254bc6e0684dc6dc894658d846dda1d80b7990d800cab8d61fdc86d5a13716d4e1cfcad376d5e9cf8745bfcdcfc436cc6652b0cafb2985
  | 6, 0 => 0x5ccd23505c61dd605b43f6005a509e6057729b60575e13b05687e89055afcf4054d1e1505270d1e051a6ec905169eb00514ebac04dbb86404c021da04bca65904941f6a048dacd704890ef50479bbe10457261403f1b95203c4e71303b5fb4003ae4e9903abb2f00375c6cf035a9565034762020341d11b033b05b503087e0402e9d44b02e8a90d02a27623029aef9e028da25d0248132d02470b1b0241c4e10225f9ec0219fdf802102cb901f2900401b2c4c601a6e4da01a44b7b0198403d014fcec70146c416012a5840011eaa2f0111cbc9010ac53100f5a3d200eff696009787b3007d93d8006fb9d3005b006f003e83f9003b1ab4002e9cb3000db973
  | 6, 1 => 0xbb0f9310bb0c3ae0ba77e000b88cc090b651c800b50e2ee0b3b2aae0b1a7d630b0896c40af6cb310af23e1b0ae34fac0ac986c50ab8b2690ab6224b0aa769cf0aa0caca0aa03d900a9628be0a81a3e10a7d079a0a6426b20a4bf36d0a3d884a09fb12fd09ea0c3209a18f54096e691e09480ced093e73560938c975092be94c090e3a080903dbc50901863008fadadf08fa445b08d6f02608739b700856ca26084aafc70848694b083f2726083843fe0815b7f9080f361f080f15bc07c2594907962ead078f1e53078c6002075140fd074921400737882a0715437d06a693b5068a399a0665520c0659646506540181063d522405eb17b705e77d7105e13265
  | 6, 2 => 0x1103719910d89c4810c5277710a92875109faa42108ef5b91087cb5e104ef361102d648a102d4a7a101f34a2100eb51c1004221f0ffdfe370ff073950fe0ac610fde41e30fcb33c20fc7e3a30fc75d210faa77070fa2a5570f8e38f60f8899180f8009980f78ea770f76f4eb0f6b9a140f56ffe60f1c66040ee7b93a0ee672b50ee271f80ed86b730ea800b80ea022dc0e67dc250e2c4ae30dfb96ef0ddd4aa00dcd46f30db51cee0db432850da46fb90d9cbe430d9a92370d92daa50d6e8d170d5098740d2aded90d1802ee0d15a3500d0b45210cfc43180cf439bf0cba81470ca165b80c903f7b0c8c4ccf0c82609c0c7bcab90c6f23470c60dcf80c03b901
  | 6, 3 => 0x17dbb70317bcd81e17bba65117989514175a929b17497f4a172c13601729918f1712096e16d8a81c16bd508a16987722164ab0e816100cbf15f71c1b15b18426158c470e1581f8c8157b3ef615776f951574b12d1561a43a15602014155cba4e14db18b514b47c3e14a3cc181486a38f1476b3641461a2571415063f1413d60813e90d2b13dbc3bf139b02df139302bf13728f561327faa11317dd2b12cd450012cbbb2c12baa67712b8ab41125d0b7e124d6d63123c1c3b1233466a12324797121b1123119b91ab119557c6118eca21118d0e1d11894c1a11880f961187183a116b4724116a8758115b67ca1142fa41112506a81120d646110f8d8e1106ad57
  | 6, 4 => 0x1d55e79b1d4a9d981d29fe0a1cf670511c9fd8f01c8f14451c84fb571c5d3d531c5377201c35b2841c18469a1c0c1b4b1bf5be811bd1fa481bbbe6161bbaa2fd1bb1776b1b9386ad1b8548e61b7eaebf1b7aa30b1b78d4bc1b62a5db1b55df541b4b11361b40c0441b29bf4b1ac899ce1ac6cf551a87fcc01a8148131a6b63331a58a2341a4b36dd1a4058c31a0dc40d1a04d97919f9a28419f2db1c19e220af19b9717319b64fa1197741991966b800192a0dd61921f28d1921237f19169d3318f811bf18ef4baf18eed24c18e3fb0a18c91a2e18c904ec189d69961892cd85188349881870ade6186366e3184ab4571841fcce1839cef01835b7a618043d69
  | 6, 5 => 0x22d85c9a229eb02f226346d522521a042246c520221f487122016d1d21d8db472194ff3b21901609214d97092145ca59213bddeb20e249a720a84c14209b7f302089ff202062e284205cc8cb204bdfba2014c6441ff58b481fe039d21fd3d3851fb72b911fac95641fa432931f9bef851f9874111f87b1c01f75faad1f3387171f05df5c1f0286b71efda3231ecb1f881ec4d0da1ebb13731eae27731eaa0f9b1e961c6a1e8465841e7359ed1e6f5e891e5a4bef1e4837591e3f594f1e3a97551e35b7f71e184c7d1e08e1531e06b5881e0576261dff4d111df468421ddb52551db4e0681da019151d984e6e1d89743f1d85cfcc1d826c881d825b1b1d5bd817
  | 6, 6 => 0x29a1070d2992b932298b593d29740e862971ba40296b38aa296669a2295678be29319d85292af8b7292576e32920d8b3291385ac28df87aa28c93b9c28bc54b328b1318528a1dfb02882d990285a6120284836062844d6392842e26228367c31282a58e7281a4d9f28191047281909f627a497ea275b976e2752ae75272a02302707a0fd26b886cd26a8a450269608f926786863266cd792265363bb262a32f4260932412604931525eb7b5225de408525afebbc254b6a5725494af5250aba5724fedf5924bc09df2443fd30244232e6241b265d2416c07e241577b924140a4123fe5bdc23e8c56e23bb3be323aa74da2373cc522365101622f578d322ea3ac0
  | 6, 7 => 0x2f4f90262f20329b2f1abea52efbd9642ef7eddb2eedfa852ee716dc2ede098d2ec68d272ebd3d6c2eba05a82e75f9142e45ee3b2df877932dd75a262d9f970e2d9165262d8de92d2d7d41f82d618f3b2d3ff5e92cf8cd042cf085992cc795ae2cae25c92cadd3bf2ca069f22c66b7e12c611b6b2c3e81882c1a29112be8c6dd2bcf9a012baf6f8f2b79d3f12b4013f32b25f1c52b236b422b09ceab2af68de12ac41d2c2a8e42722a8c0ae32a892cd02a76e8352a734e672a6347522a60e87e2a42cf9a2a4238582a3dda1c2a3198e02a222ab32a1d57d02a180b4c2a14d0f72a1317a02a023a7d29ff23b729e188d329dcd53d29d10a3229c478db29a78cc4
  | 6, 8 => 0x34e85a3334c8f0c734c7ff3c3492603134886bc33481cae43481847a347c735e3474fb8034578f96344f47aa344da13934417d0f343a84db340993c533e6b2b633d93c6b33d51d6733ce134333a8219a338e027c3389f6ab33864f1f3380f3e4337f0a06336a01d23366c242335d8195332a02773327d92c33193e9a32def36c32b96323329cbbfb32906673326bf53f325f2c64324765313228b42331f5eab331752de731660f0b3157bf6e314b72693122199e311dfd6a3112a29330d5282030be0b3130bda81a30b9d1dd30ad71ad30a5e218309c65f3306f6ccb306aaa7f30633068303564fd30010ce22fdcbf742fbf35272fafb1b32f954dd02f6745e1
  | 6, 9 => 0x3c35f2033c27f8ae3bd6ad1d3bbf524e3bb70d6b3ba5ac113b9031bd3b5624293b34c0e23af9666f3aca75eb3aace7f43a9a85bd3a97b4d03a73bcfc3a5b11913a03d4b139e99ade39de4fb639ddbebc39b103453989122439731d65396f572d396d2e4d3958c2ee38eb527838ea75ab38c8629238c1057038abbdef3885fcd2386f6c39386890e837ea5ebc37d4a1c237c3b2cc37b9fc1b37a4a2c837a4666c379a618237997d53377ee725376ecd623767fbde3702e44236fb367836de7a8736898ece3678c0eb3619ea8d36126244360d07b93601d28435f2a55735d89aaa35bf14c335a96a46358ad894356512d0355e29ce35239d6d35099e5634ecd7be
  | 6, 10 => 0x447f91b143fdf1ec43b9f0a3435117db433f660a4335a68143110caa42eda89a42c90b1142b779a34288da78425ac010425327d74250d60941a0c1284175ef23413f306a413586ab4113406d411103a140db9c8640a8378340a60e3740a28b4c4071490e4062ec42404b3013400945b43ff4ef3e3fd24e333fd11fd73fc11baf3f6ce07e3f62ae583f39b76f3f384bf13f147cd73f086e6d3eb6cf343eadce583e7b57fa3e49633b3e38dfb93e38a55b3e277fff3e0be7f03dce4f973dc293cd3daf73bc3d9f76143d946b583d820b7b3d60158c3d2562093d254e653d1c18ae3d03aadf3cedcf813ceb95653ce6437e3ccb90303c9643853c3970963c38e011
  | 6, 11 => 0x4af8703d4aee73794acdf8d54ac953704aa02b774a95df414a2e53494a0125c049e579ed49e3bfbd49e0f04f49d9a14a49ae952049980430498effba4973f4c7496fc9e449697f42496885e549585913493b17444931ec3848f6c24648ce78fe4854372b48339399482de2cd4828dac04827cfeb4824b1684812707947d7f35a47d1bb1b47bc77594795ee6d47953816479508b6478b713d4772d05c46ed067a46b9893046b6a8dc46b55adf46a6e54b46610b584631106d462000d246115b0845d91ef1459ecff7459774c2458338fd457c8acd457a79f14563ccbf4526b4084523bdd9451ed6694519cf8c450ea01a450651ef44c79b8a449d303544978530
  | 6, 12 => 0x5314eaf652f2e65052e9b7ba52e8c50e52e2321e52dc9cdc52943af55290580b528ce0195281620b5248446851cf671751bb2a0f51ac2dfd51ab7a23518820f7516a823f5143b19c5137f86e5137e9295129991d51249501511d2be450ef354250eca9cc50b80df750b19406503999f0501f9e51500139404fc71f074faafd564fa753334f7b77d94f7141a24f5e8ec74f4f19b14ea43e9e4e1717654dc7b19a4db0fe984d8cd6aa4ccdf14b4ca859dc4ca1aa074c7463374c51dc5f4c4c79c44c46545e4c2f2a6b4c2eb5784c2571154c1e35cd4bd15be94bb8d2fa4b77d19c4b6e21e64b6d33644b4b81c74b2e44754b21fba14b1e92974b1168534b0d87ba
  | 6, 13 => 0x5b023f875af98e345aa2af7a5a9f5dfd5a8723c85a6fa4e45a1dcce55a02c45a59c84b70596cee2e5944bdd6593f5843593aae7858bb531a586233b258514614583019b9582969ea5807cc095802414f57d21cf857b93b9557ab48c1576c925c573149745712d2ee56f411bd56ccc280568ff7f1567d130c567c7f515672a487564a5295564404f355f9c36e55f6748055f5a32a55e93b6a55d8d84b55a0239d5582b7b3557f4cd955739b7c5530a86c54f0504c54ecbb8754ba411f54b8020854aaac7454a9557c5488605d545a8902545833245402bb78540174e053ec72ba53dbb72c53cd1deb53c3fb8e53a51bbc537b088b53514afd534934bd533fb48d
  | 6, 14 => 0x64c8c42e64b153c164a0c73f64789948646b996f63e431ee63a6a9d3635c10ae62dd8f1e627050f962356cc061cd881d61ca400861818f6f617d3f4b616fe8b461444ca2613f4bb661381f9760fbe7f960e8d6d560dc0ef760d0e7fb60c1af3f60c0e6cc60687f6660638fc460617b6c6043727f5ff7afde5fd7d1ae5fbac6fd5fa9e2065f871fd25f7ab97d5f4ce3e85f411ea25f35ba935f20e9805ed985675ed000cb5ecbb8db5ec2fe405ebc0fda5eb5ede35e5e95475e22a7545e13ada65e0e53495dda43b15dbe740c5d7d6e2d5d59965f5d5624535cde0cce5ccd4b075cb55e505cb1099a5cac1ec35c8c12a65c7754db5c6c5b6b5baef06d5b1580d1
  | 6, 15 => 0x6e4e713c6e3f00b06e04f5ec6d7e78d66d79ee906d71e5326d547e0c6d545ce36d3ddb8c6d1da4d86d1a240c6d0c81136d0b6a236cfdbf986c80921c6c4b6e046bcf90f36bcccd376bbe0e9d6ba44eea6ba0f1c86b4493be6b2262386afac8926ae6f02c6a9119966a41bcfc6a2ef61d6a258de66a22b4f869cd7e5369c0add46962df3869148b68684cb17468329f336827ae856825e35167fbf59e67d9415267a3bf0d6786b84767852479677701556776f078677213ae675e86876733942567296a4a6709aa6167044c4c66fd841f66d94f9766d1c7a966c97e4e66596eea665174db663bc18865ee6d3a65b1125865438d016502386064e6ab0264dbdd21
  | 6, 16 => 0x7812071777dc326977d135d0778424c27777dbfe7770373f7753784a76fdbb7a76d69d9076d00d2c76509acf764e5f6176461d727623dab17605fbc075cf5cc1756ef7e9756948e6752cfb2e74d2ee7874c85d02744a99ed7448134174238cce7415da3a7408724473a488797365dcea7361e71e734eaa0d73493a277331c26873265eb0731a9a37731046f872b2833972b1ed017239d99b7238707e722d71c671fa161671f2133171d3d74b71a26241718d4b857179360f7166cf87714b8ec87130886e70e9cc8f703b7bb4701419896f7090bd6f596a256f4ebd9a6f4c3cf56f3a9e9a6ee7589d6ed8da0b6ec911ee6e97547b6e97376a6e81dc4c6e6a3120
  | 6, 17 => 0x805c90738051d8b380424c1a800bb67b7fbacdd57fb9c7817fb866157fa786767f9c730f7f8ef2d87f7ed9fb7f7c17707f3d62797f1a1c937f10104d7f05801f7f0507a47f00ecae7ef775487ee0fc947ed513f37ecfd02c7ec8813d7ebbf6017e6829297e2488817e05acff7df1da2c7ddacfa87d7d57bc7d5fc8b57d5aa3917d4bf7b77d2e7cf97cfde4937cea112d7cb560537c9e1f737c9c8f237c826dfd7c69c65e7c4faf817bf8b5337bf0b2df7bd019c77ba3c0797b4614867b334ca57aeab7127ada8ab67abe6b607a85129f7a7382a17a67caff7a2bf4367a258db87a11764d797004af792903cc78c9173878ad3fcb78a46f127850917f7819d385
  | 6, 18 => 0x8c5b2b6f8c51c7138bd322518b31c58e8af097cd8ad81a8e8ab84b5d8a7994f88a51c9de8a4c27bb8a4b2c568a37c65d8a2340618a1fecb889efee9189b52b508974814d893fe42c892cfdea891e93a388dbccf288bd66ca8836871687fc390c87f2d3ba87e13aa0878be23f874f926987038fdf86d9723486be95e986bb6894867254828665f643862d7dc2861db7ce85fa1a2f85ef75c685a0b970857f1b6685569ca78527bd3a84a4c2e6845d1c66840e75af83eaa2da83d7542a83a21eb1837f6b3f836a4ef383629097833df90383328cfd8323215e82de71178295aa1e827639728275807782673617818c305a8115138080b3c20480a78bdc806266ad
  | 6, 19 => 0x98d108c9989a6927980955f297e2d59297aa9cac97a53cfb97a4f387977e30779713ecb196fb60e996d93d1e96ad47ba96449dee963ca10f95daf82895a7bcd395955e8d956d102894e8477894b8834e94adb8bf94ad8e5d945654d793e5c51a937619ce92bb0e5892904ad892806526924b56d491e8ccbe91aecc4091a73dfd919ac8ae9176ae5f912821e490e225fa90c97f5390c7888690543b818fd08d408fc42d338fa19e1f8f74f0a98f7301af8f68c10c8f4a16428f1f96978eca0a408ebf00228e7d732a8e60a20b8e5d90ed8e323b688e13a1f68dbe23998da068838d9b3a468d395ff68cf6da0a8ca14df68c76bee98c73f3678c6170088c5e2c4f
  | 6, 20 => 0xa748d152a6e98352a6910249a63c52c1a5c2748aa59b37c9a54a6a95a52d601ca4943c01a4437ae7a3e9ce97a3c65a94a3c1ab4ba33926f8a31c39e8a3098384a2cd8bc3a2a6f9a5a284b47ea27f4475a26ac20ea263fdeea2487bd3a23d1ba0a177f149a1662bafa1040fa4a0aab22aa0569a1b9ff352249fce48649fa7e8e29f7298a79f3584529f0c76639e93ebe99e91ae509e4370ac9dee332e9de2e3f49daae7359d72dd149d1f09df9ce0c3739c8b0ef49c70cc409c5f65c29c2506d59c0647769c01232b9be3accb9bc7f7b09b74bd5f9b6512559b0c849e9af887159aca79e399d668539930a0fc992c6b7e992721c299200f9299004fbf98ff0c18
  | 6, 21 => 0xb4d0d4a4b4b7aa29b4508effb40596d8b3fad78cb37ea96bb36706acb2f25cf9b2e2d36fb2e06130b2d40c22b27560a3b272d876b23cd636b210ca3fb1c67554b1aab58bb1976043b18d6e74b110e951b104f48eb0c88900b0a47233b074fd4cb04d71d7b038e43cb03646e7b02268afb002dcf0afdcaeb4af841f0aaf332a10aeff15d3aef128d3ae61e220ae5e2b50ae559e30adfb4a1aaddfe763ad9c65faacf45b22aca9b064ac8a86ebac68c860abf06f62abd597ceabad06fbab559622ab47af95ab3f45e1aa6b2cfcaa67fba6a9d57912a97e6899a95dfcd0a9501df1a91d7cfca909e4c1a8fd26c9a8e78fc4a8a73885a8309305a7e1ec9aa7a2a7a3
  | 6, 22 => 0xcdc288cbcd404df9cc314ee5cc1d4d7bcbe36130cb66226cca5290e6c9bdabcac91a9764c904d60fc8e3e5cfc885719dc7718d50c7554d2ec7327c7fc722c587c6e21188c6b2dd46c63e6ab8c5d1834fc59c2c97c5158df3c4d20e6dc48fe98ec4745ea1c41ed601c3d681efc398766ec31aba35c2c56a8ec2afde01c1b77a4ac10e3d6bbfb4dd66bf82112cbec0a575be70a23bbe269a7bbdf8e8acbd9159b9bd63e280bd5fbcfebd328e64bbe49247bb28b1adbb245530bb22dcfdbb13bee6ba694344b9e01b82b9b83f34b8e9992fb8e03f25b889a36bb8767b00b7b26079b7ae1533b7a1fd24b7610a65b6fb2445b6be7634b58ba30bb51ce2f2b4e732f9
  | 6, 23 => 0xfa4ce404f966b7b2f7368355f3828995f3740fcef12be4b6ef11e681eec40f0cee8f1728ee5390f5ee02495be99333dee8da166de8027d18e7d5c6bbe6debce7e61291b4e4d154f8e3ef42d0e2ef9098e2587574e195a639e095f543e050a6c1e026649fdfbea839df7b7600de5cb0fbddb7dd18dc52a6e6daf5c757d9de0ce9d8f800a3d8c3f1bfd85d0165d800cab8d7f9e631d7adc8ffd748aebdd5dffed2d528804dd51bbe8dd48f315dd459f8ffd2cd00b1d219e748d1f83001d130dacfd0620e95d0541adecfd1b474cfafaacccfaaeb5dcf6e5413ceafa34ace597d4cce4267c6cdfcc0df
  | 7, 0 => 0x14121a0c130748e512baa67712b8ab4112ae5da3129997eb127980281232479711b4128d1187183a11761aa81142fa411134c9340ffdfe370fd4c3f50f3badb20edd17080ea68d810e783ebe0e589c450d9cbe430d9a92370d52c9a60cf91d9f0cea20e10c2cfbb60c167f100b989d440afb5dd30ab0afbb0aa9dacf0a9628be0a71f9560a172c4908d6f02607d82e3c07bd347d06ecbabd06cd9ad406c7654b0663442506556796065223ce064612c7061ab28605a3eb0a059e8b170590310f05869eb105169eb004d0acec03f1b95203e3645403601271033b05b5033a727c02e9d44b0296f579024a740d0129b75501283a1700dd496a0064991500103def
  | 7, 1 => 0x26e36c2426d2458e26aa53c3265363bb264ea12126396ad4262d41fb25eb7b5225bece64255ffecb24a7e76c2485a934246ade96231857ea22ea3ac0225c733222543c1c22521a042179389d2064873a203e530f2015ae6f1fe039d21fb72b911f9bef851f608b651ee4e3db1ee472391ebb13731e8eec381e7359ed1e17d8601e08e1531d73f5661d094b741ca0b1831c53b96d1bea35011be841c11bde45011bbbe6161b8548e61b2d157f1b1036f41a5d39541a45ab1d1a4058c31a2bfa9c19f08aad19e3604919deb3e2192a0dd61923eb0b18e3fb0a18787ffd17d7cb951729918f170db67f16d8a81c1662ea0a15ff8a4715f86a801561a43a1528ba3c
  | 7, 2 => 0x3cedcf813c52b0633c39fd5e3bf3e2703bd0b7833b76a7473b3c318a3b23954e3a8b1a6539de879e3958c2ee38ad846e37a1ed1c379a6182378f31e83724f45b36c744ae36ad51603678c0eb361b1af435d89aaa357bcd5735743559355e29ce3528ce783518dab13481847a33d93c6b33ab0d08339be830333d92c433193e9a32c3d3da329cbbfb3294bf40326a062131381b0730f26f092fa1c82a2efbd9642eedfa852e9e70832e46479b2daad2e42d770a592d014b912cf085992cae27f22ca821632bdd94e82bcf9a012baacaed2ba0a43a2b698d6c2b48380c2af4104e2a6bdfc02a5e00e129c478db2964176b284db2db2838c79a2775450f2752ae75
  | 7, 3 => 0x56fffaeb56da22f056abec6255bb43f755ab6c46552722ed54ed1c7554c1de1053b3d16b5316929452f2fea452de426a52943af55275541c51ee61ea51e81d5151ab7a23516924ff515c291951007c3a50c9577f50a706e84f490be64e7327324e5bae794e1db72a4e0e9fc94de254b54dd111674dc27b5b4d0476064cd8ba054c4c79c44c1e35cd4bb13b214b40518f4a59283649d602e848f889f848ebd2aa47f69d2646e149a24696c818465e79d543cee64d43b9f0a343b4257143555fb0433f660a432891ef425327d741d9fb7841a4b5d6413f306a413ca6963ffca0873f8b9abe3f6ce07e3f086e6d3e9c5ebb3e277fff3df1aaf13dc32c533d18fbc9
  | 7, 4 => 0x7db1e1917cfde4937b4614867ae97d0f7a70b1287a2bfc5d7a2bf4367952d274794717d67946d3e377d135d07770373f764e5f6175a74bbc74e1bd617341d2fd73227b8e71fb25a271be65bd710f96de70ffce10707cee8d706753916f3b46226d45b13a6d2657c06c8fa51c6b46b4d16aa2ab606a4fc62d6a2a46cf69f5d2f969c031bf692e70ee68b561d066742ba76659a12a647899486347643b633af011633635116292bf226240ab8761ca40086001a2b65fd513de5edafec85ec6f1c75ec2fe405e06e6065d93d62e5d3a46645d23bf8f5c0095e65b4388f85a73054d5a1dcce559f223e559e533015992adb0596bf2065943cbfb5923c1c65916f562
  | 7, 5 => 0xa909e4c1a8e78fc4a80fa957a70b5b06a6395456a623790ea512b068a35f8a0fa0c045e29ffd08839f9262399eab30d29de02fb29d3508f49c36144f9b308e9f996c23f498fcecee985a34f7978d297c9713ecb197012b849680ac86963c456d956125c6955a08989396353d93527dd5927a567e92278ab591bec62691015b8b906d26118fe9ad8f8f6680978f46f2108dbfa66d8d92f6958d6bb4b28b3e939c8b308e208ab84b5d8a7994f889f226db88edfe0d881ad29987080352868cb42485faf2fb850f030e83d9bb2c83833bd7834a6d9382d3eb998276397282739f208241b0597fe35f827fc0036d7f97da8d7ebd26667ebbf6017e05acff7dd5c4a5
  | 7, 6 => 0xf646c3bff0f10dbee9f23fa9e9599105e5c6ac76e1c2a466daf5c757d958a3e4d90de9d2d6890d25d229a3e5ceeb1ad8cdb20f90cda803e7c7554d2ec707ac1ec4ac2c82c3d681efc398766ec30bd3fac2afde01c16463c6c07ccfeebf4172fabe107ab6bd3f82f8bc008a33bbe49247ba9e7ab4ba2399e2b9e01b82b6be7634b55b444cb2f03ccbb2313513b210ca3fb04d71d7b02268afafebec7dad1a90a7ac8a86ebab962e79aa3f12b1aa21bb6da95dfcd0
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x15500203454c8200504c420115500200054c4201054c4201054c420242485201054c4201000000045150020000085101350852000000000525500203054c420100000005324852031550020045081202155002032550020315500200054c420135500203054c4201000c810500000005
  | 5, 0 => 0x10510000085101000000000000000400080100000c91030000000100000004000000080000000200000007000000010000000600085101000c910100000006000000050000000200000005000c41010000000600081101000000050000000700000006255002030000000415500203000000020010010300085101000c9101
  | 5, 1 => 0x80000000900000001000000060000000200000000000000000000000000000005000841020000000100000005000000060000000600100100001001000000000100000007000c81050000000000000002000c8105000000020010510300000003000000050008c104000c810500081102454c42010010910100100103
  | 5, 2 => 0xc11010000000651500203000000060000000400000008000000090000000900000004000000070000000700109101000c110100085100255002030000000300081102000811010000000400000006054c4201000000000010d103000000020010010000000004001091010000000200000000000000050000000400000007
  | 5, 3 => 0x900000002000c4101454c4201000000090008510300000009000c9103001001000000000500000002000000080008510300000000000000050000000600085101000c91010000000000000009000c9103000000000010010300000001000000050000000200000001000c1101000c9102000000050000000500000006
  | 5, 4 => 0x105103000000070000000500105103000000070000000600000006000000070000000700000004000d1101000000070000000400109101000000040000000900000006000c1101000000040000000100109101000000060000000500000006001001000000000300085101000c910100000005000000050010510300000006
  | 5, 5 => 0x900000003000c11020008c104000000070008110300000005000000070008c104001091030000000000000002000000080000000700000004000c11010000000700085103000000030000000600000006000d110100000002000000010000000600109101000c41020000000300000009000c91030000000800000006
  | 5, 6 => 0x900000006000000010000000400000003000000070010d103001051000000000400085101000801000000000500109100000000000010010000000006000000010000000000000004000000030000000000085100000c410200105103000000050000000300000005000c810500000006000000020000000000109101
  | 5, 7 => 0x700000002000000060000000500000007000c810500000008000c91010000000400000006000000070000000600000000000c9103355002030008510100000006000c41010000000600000001000000070010d1030000000000000006000000030000000500085101000d110300000000000000030000000800109101
  | 5, 8 => 0x3000000050000000200000004000000010000000615500200000000060000000500000008000000090000000200109103454c820000000000000000080000000545081202000811010000000700000002000000030000000500000007454c42010000000435085200000c110100000008000000070000000600000000
  | 5, 9 => 0x1000000070000000200000004000000030008510300000004000c110100000001054c4201054c42020000000700000005000000060000000125500203000000070000000700000006000000040008110300000005000c9102000000010000000500000003000000090000000300000008000c4102000c110100000006
  | 5, 10 => 0x60000000600000009000000000000000700000006000000010000000000000007000c4101000000070000000500000006000c11010000000000000007000c81000000000000000000000000090000000300000009000851030008c1040000000300085103000000040008110300000005000000090008010000000005
  | 5, 11 => 0x10008c104000000020000000300000000000000000010010000000000000000090000000800000001000000030000000400085100000000040010810200081101000c81000010510000000001000000064508120200100100000000070010d10300000006000000070008510100085101000000060000000000000004
  | 5, 12 => 0xc410200000007000c9101001001000000000400000004254c42010000000600000000155002000000000000000007000481020000000900000008454c820000000004000000060000000500000008000c410200000001000000000008510000085103054c42020000000600085101000c9103054c42020000000715500203
  | 5, 13 => 0x54c42010000000100000003000000063508520015500200000000010000000500081101001001000000000000000004000000000010910300000009000c8105000000080000000400000005000000060008010000000006000d110100000009000c4102054c420200000000000000000000000500000004001051030008c104
  | 5, 14 => 0xc110200000000000000060000000900105103000c81050010d103000000080000000200100100000d1103000000090000000700000004000000090000000600000004000c81000000000500000006000c41020000000600000004054c420100000007
  | 6, 0 => 0x200000001000000090000000000000008000000030000000500000004000000080000000100000001000000050000000400000005000000060000000800000002000000050000000100000002000000050000000300000005000000020000000400000005000000090000000500000001000c91010000000400000002
  | 6, 1 => 0x10910000000007000000050000000400000001000811010000000000000007000000090000000500000002000000000000000500000007000000020000000200000005000851030000000900000000000000010000000100000000000000020000000700000008000000030000000500000005000000010000000400000000
  | 6, 2 => 0x6000000090000000200000003000000030000000500000002000000000000000400000001000000010000000500105103000000050000000400000005000000040000000200000004000000070000000800000003000000040008510000000000000000070000000400000001000000020000000300000005
  | 6, 3 => 0x6000000030000000300000003000000020000000900000005000000020008410200000000000000030000000300000002000000030000000400000008000000020000000100000001000000080000000500000000000c4102000000000008510000000009000000090000000600109100000000070000000500000003
  | 6, 4 => 0x2000000080000000200000005000000030000000200000002000000010000000100000009000000010000000900000000000000000000000000000000000000010010010000000008000c410200000002000000090000000300000006000000060010810200000002000c810500000006001001000000000300000008
  | 6, 5 => 0x10000000300000003000000010000000000000000000000000000000300000008000000040000000000000001000000050000000400000004000000000000000600000003000000010000000500000000000000060000000100000000000000060000000500000004000c110100000007000000040000000700000000
  | 6, 6 => 0x600000004000000020000000000000004000c810000000006000000070000000300000003000000050000000200000009000000070000000300000001000000040000000200000008000000030000000200000002000000060000000100000003000000040000000000000000000c1101000000010000000600000003
  | 6, 7 => 0x500000006000000040000000300000001000000000000000000000005000000000000000200000003000000010000000100000001000000000000000600000006000000090000000500000002000c410200000000000000000000000400000005000000050000000600000009000d1103000801000000000600000004
  | 6, 8 => 0x900000006000000020000000200000003000000010000000300000009000000000000000400000006000851010000000200000001000000070000000400000003000000010000000300000005001051000000000500000008000000000000000100000008000000000000000800000005000c91030000000900000006
  | 6, 9 => 0x300000004000d11030000000700000008000000050000000700085100000000040000000200000002000000070000000800000008000000030000000300000000000000020000000000000003000000040000000700000001000000000000000300000000000000080000000500000003000000000000000400000009
  | 6, 10 => 0x400000002000000010000000100000005000000050000000900000001000000050000000300000004000000050000000000000008000000010000000000000006000000010000000300000004000000000000000100000002001051030000000300000002000000030000000900000000000000080000000800000007
  | 6, 11 => 0x700000000000c41020000000000000000000000010000000300000000000000040000000600000009000000080000000300000000000000010000000400000008000000060000000700000000000000000000000500000005000000040000000100000003000000020000000400000007000000010008110300000005
  | 6, 12 => 0x400000004000000000000000000000005000000050000000100000002000000030000000800000004000000040000000700000004000000020000000300000003000000040000000400000004000000000000000800000001000000060008410200000006000000010000000000000004000000050000000400000004
  | 6, 13 => 0x20000000100000004000000070000000400000007000000020000000900000002000000090000000600000001000000030000000500000001000000090000000300000005000000090000000700000009000000080000000000000000000c910200000009000000000000000200000002000000010000000100000005
  | 6, 14 => 0x40000000000000000000000020000000500000006000000080000000400000007000000040000000300000004000000090000000800000001000d1103000000070000000200000005000000050000000400000000000000030000000000000002000c81000000000300000001000000000000000000000000
  | 6, 15 => 0x900000007000000060000000200000002000000050008510000000002000000010000000200000002000000000000000700000000000000080000000900000001000000000000000000000009000000020000000000000005000000000000000000000004000000070000000000000005000000040000000100109101
  | 6, 16 => 0x600000004000000050000000100000006000000020000000600000002000000000000000800000004000000060000000600000003000000040000000600000007000000090000000000000000000c91010000000000000002000c11010000000400000003000000020000000500000004000c11020000000100000000
  | 6, 17 => 0x40000000800000001000000040000000000000003001091000010910000000002000000040000000400000003000000070000000100000001000000050000000000000009000000060000000400000000000000020008010000000007000000040000000000000003000000040000000500000004
  | 6, 18 => 0x400000002000000050000000400000002000000000000000500000007000000000000000600000000000000090000000300000006000000030000000300000000000000030000000400000000000000010000000400000004000000050000000100000003000000040000000500000001000000000000000100000006
  | 6, 19 => 0x500000007000000010000000500000009000000060000000900000002000000060000000300000008000000060000000900000002000000060000000400000001000000060000000700000001000000000000000400000009000000080000000800000005000000090000000000000000000000000000000300000002
  | 6, 20 => 0x50000000900000001000c41020000000600000003000000040000000200000000000000030000000500000009000000020000000000000001000000060000000500000007000000060000000100000006000000010000000300100100000c410200000003000801000000000500000002000000000000000400000002
  | 6, 21 => 0x1000000030000000400000005000000010000000000000003000000020010010300000000000000040000000100000001000000020000000000000000000000030000000700000000000c410100000009000000040000000900000005000000000000000400000000000000080000000700000002000c410100081101
  | 6, 22 => 0x500105100000000050000000100000002000000040000000500000007000000010000000500000000000000060000000100000008000000010000000500000001000000030000000200000008000000080000000100000003000000050000000200000000000000010000000500000002000000000000000500000000
  | 6, 23 => 0x5000000020000000900000008000000080000000800000004000000050000000800000002000000070000000300000002000000030000000200000008000000020000000600000002000851000000000700105103000000000000000300000005000000080000000200000008000000040000000500000008
  | 6, 24 => 0xd11010000000200000007000000060008c104001091010000000300000008000000010000000200000004000000030000000400000005000000020000000100000001000000000000000100000005000000000000000800000005000000010000000100085100000000090000000300000002000000050000000100000002
  | 6, 25 => 0x700000000000000040000000000000008000000010000000100000004000000090000000200000009000000040000000500000004000000050000000400000002000000030000000300000002000000040000000100000005000000070000000800000007000000050000000800000007000000020000000300000007
  | 6, 26 => 0x20008c10400000000000000000000000600000004000c810000000000000000000000000400000001000000000000000900000002000000040000000600000005000000090000000100000003000000020000000100000002000000070008110300000002000000030000000500000004000000060000000700000003
  | 6, 27 => 0x100100000000000000000800000006000000050000000600000002000000010000000300000004000000020000000100000002000000040000000200000001000000020000000700000005000c91030000000400000009000000020000000000000005000d1101000000020000000300000008000000040000000300000008
  | 6, 28 => 0x200000000000c1102000000010000000600000000001001000000000100000000000000050000000300000003000000080000000000000004000000000000000000109103000d1103000000010000000600000005000000000000000800000002000c110200000003000c410100000001001091000000000300000005
  | 6, 29 => 0x7000000080000000300000000000000000000000300000000000000010000000500000003000c8100000c91030000000200085103000000060000000400000004000000000000000600000004000000050000000800000004000000000000000300000001000000020000000200000009000000000000000200000004
  | 6, 30 => 0x3000000040010810200000005000000000000000200000003000000070000000100000003000000000000000700000002000c1101000000010000000100000008000000040000000900000001000000050008110100000000000000020000000400000004000000090000000000000000000000000000000500000005
  | 6, 31 => 0x4000000010000000600000009000000020000000200000001000000020000000400000005001091000000000600000005000000000000000700000001000000040000000300000001000000020000000400000000000d11010000000300000006000c9101000000000000000200000004000000070000000000000000
  | 6, 32 => 0x500000003000811030000000900000001000000000000000300000005000000080000000500000009000000040000000500000003000000080000000000000004000000000000000700000000000000000000000800000000000000000000000200000002000000040000000800000000000000030000000500000000
  | 6, 33 => 0x800000002000000010000000600000005000000030000000600000003000000080000000600000002000000000000000500000006000000040000000000000003000000070000000000000004000c11020008510000000000000000030000000500000007000000000000000500000000000000030000000000000005
  | 6, 34 => 0x200000004000000000000000600000004000000060000000400000004000000060000000500085103000000050000000200000001000000020000000500000003000000000000000900000005000000000000000100000000000000080000000700000001000000050000000000000005000000040000000400000005
  | 6, 35 => 0x400000005000000020000000600084102000000050000000100000006000801000000000600000000000000000000000400000001000000080000000800000001000000010000000400000008000000050000000900000004000000030000000200000000000000010000000000000002000000060000000200105103
  | 6, 36 => 0x100000005000000000000000200000000000000030000000600000001000000000000000000000009000000040000000400000000000000030000000000000005000000080000000300000006000000080000000800000000000000070000000100000006000000010000000000000004000000050000000100000007
  | 6, 37 => 0x200000001000000060000000300000002000000010000000200000000000000070000000000000001000000000000000000000003000000030000000300000002000000000000000000000004000000040000000400000003000000010000000300000001000000060000000000000005000000000000000900000000
  | 6, 38 => 0x60000000200000002000000000000000000000001000c81050000000600000007000000070000000100000002000c11020000000400000003000c110200000000000000000000000200000009000000020010d10300000005000000080000000100000007000c41010000000300000001000000010000000000000006
  | 6, 39 => 0x10000000000000000000000050010010300000007000000020000000500000002000000010000000200000004000000040000000100000007000000000000000600000007000000080000000600000005000000070000000500000000000c110100000008000000050000000000000004000000000000000100000000
  | 6, 40 => 0x400000002000000060000000300000003000000070000000300000004000000010000000000000006000000010000000200000007000851000000000200000000000000090000000800000006000000010000000100000006000000010000000100000008000000020000000500000003000000060000000500000005
  | 6, 41 => 0x100000008000000000000000800000000000000070000000200000006000000090000000600000000000000040000000100000004000000020000000400000001000000090000000800000008000000070000000700000005000000080000000000000006000000060000000200000002000c41020000000500000007
  | 6, 42 => 0x85100000c11010000000600000003000000010000000400000004000000080000000200000006000000030000000000000000000000020000000300000000000000000000000000000009000c9103000000010008410200000002000000090000000200000001000c81000000000100000009000000070000000500000008
  | 6, 43 => 0x30000000600000001000000080000000000000005000000040000000200000000000000080000000300000004000000030000000800000004000000070000000400000008000000030000000100000003000c810000000006000000030000000300105100000000070000000500000005000000040000000300000007
  | 6, 44 => 0x8010000000005000000000000000100000006000000060008c1040000000300000006000000090000000600000004000000050000000400000001000000070000000600000004000c4102000000080000000100000002000000000000000000000005000000000000000400000009000000040000000200000009000c8100
  | 6, 45 => 0x8000000040000000000000009000000060000000800000007000000000000000200000001000000030000000000000004000000010000000800000009000c4101000000050000000100000001000000050000000300000003000000000000000300000002000000000000000300000007000000010000000000000005
  | 6, 46 => 0x500000003000000020000000300000000000000020000000600000006000000010000000400000003000000010000000000000002000000000000000300000004000000080000000600000006000000030000000100000005000000020000000100000000000000010000000400000006000000010000000100000006
  | 6, 47 => 0x600000001000000040000000700000005000000010008c10400000003000000060000000300000006000000050000000100000003000000000000000500000001000000000000000300000006000000040000000800000007000000090000000500000000
  | 7, 0 => 0x1000000030000000900000007000000010000000100000005000000040000000200000002000000000000000000000000000000010000000800000003000000010000000400000001000000010000000500000004000000010000000200000007000000020000000000000004000000080000000100000004
  | 7, 1 => 0x100000005000000030000000500000000000000050000000200000001000000000000000100000002000000000000000000000004000000020000000600000003000000080000000300000004000000000000000000000003000000060000000200000003000000010000000000000003000000020000000500000005
  | 7, 2 => 0x300000003000000010000000000000000000000000000000200000003000000030000000300000000000000020000000400000002000000020000000000000002000000050000000400000002000000030000000500000003000000050000000500000000000000020000000400000000000000040000000000000001
  | 7, 3 => 0x200000003000000050000000200000000000000030000000500000004000000070000000000000005000000090000000400000004000000040000000500000000000000000000000300000001000000040000000100000005000000010000000500000005000000040000000400000005000000020000000400000004
  | 7, 4 => 0x400000004000000050000000000000001000000020000000200000002000000050000000300000004000000020000000500000004000000050000000400000003000000000000000000000008000000030000000000000004000000010000000200000005000000000000000000000007000000000000000100000001
  | 7, 5 => 0x300000000000000010000000500000007000000040000000200000007000000010000000400000005000000010000000000000000000000000000000500000000000000070000000500000000000000050000000400000003000000010000000400000002000000000000000200000004000000000000000400000005
  | 7, 6 => 0x100000000000000020000000300000005000000040000000000000000000000040000000800000001000000090000000000000005000000020000000100000004000000000000000100000003000000010000000300000000000000020000000000000005000000030000000500000003000000050000000200000004
  | 7, 7 => 0x500000008000000010000000500000007000000000000000100000003000000020000000600000001000000050000000200000008000000000000000200000005000000020000000600000002000000080000000200000009000000000000000100000003000000020000000400000000000000000000000200000000
  | 7, 8 => 0x7000000010000000400000009000000000000000000000007000000020000000200000005000000030000000500000001000000020000000900000004000000020000000000000003000000000000000300000003000000000000000200000009000000000000000900000003000000040000000700000003
  | 7, 9 => 0x200000000000000020000000900000000000000030000000000000009000000050000000200000001000000030000000100000005000000000000000600000000000000080000000300000002000000040000000400000001000000090000000400000009000000040000000100000005000000020000000200000002
  | 7, 10 => 0x100000000000000020000000500000009000000000000000500000001000000060000000200000000000000010000000600000004000000010000000500000004000000000000000300000005000000050000000200000001000000030000000000000001000000020000000500000000000000030000000100000003
  | 7, 11 => 0x200000001000000010000000500000005000000040000000000000002000000020000000000000005000000060000000400000003000000020000000400000001000000010000000400000004000000020000000000000000000000050000000300000000000000070000000500000004000000000000000000000005
  | 7, 12 => 0x800000001000000000000000700000001000000040000000500000000000000010000000100000002000000000000000000000005000000040000000500000001000000040000000400000000000000000000000200000004000000050000000500000002000000020000000300000004000000040000000200000002
  | 7, 13 => 0x60000000400000000000000020000000200000000000000030000000500000002000000040000000600000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_2 roots_2 6 s ws hint
  | 1 => checkCutEntry dom_4 roots_4 6 s ws hint
  | 2 => checkCutEntry dom_5 roots_5 6 s ws hint
  | 3 => checkCutEntry dom_6 roots_6 6 s ws hint
  | 4 => checkCutEntry dom_9 roots_9 6 s ws hint
  | 5 => checkCutEntry dom_10 roots_10 6 s ws hint
  | 6 => checkCutEntry dom_12 roots_12 5 s ws hint
  | 7 => checkCutEntry dom_13 roots_13 5 s ws hint
  | 8 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 9 => checkCutEntry dom_16 roots_16 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_17 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_17 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 8 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_8 : ∀ i, 8 ≤ i → i < 13 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 8 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 13 → Z 3 i = true := range_split z3_0 (z3_8)
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
theorem z5_392 : ∀ i, 392 ≤ i → i < 396 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 392 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 396 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (range_split z5_200 (range_split z5_208 (range_split z5_216 (range_split z5_224 (range_split z5_232 (range_split z5_240 (range_split z5_248 (range_split z5_256 (range_split z5_264 (range_split z5_272 (range_split z5_280 (range_split z5_288 (range_split z5_296 (range_split z5_304 (range_split z5_312 (range_split z5_320 (range_split z5_328 (range_split z5_336 (range_split z5_344 (range_split z5_352 (range_split z5_360 (range_split z5_368 (range_split z5_376 (range_split z5_384 (z5_392)))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z6_800 : ∀ i, 800 ≤ i → i < 802 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 800 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 802 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (range_split z6_376 (range_split z6_384 (range_split z6_392 (range_split z6_400 (range_split z6_408 (range_split z6_416 (range_split z6_424 (range_split z6_432 (range_split z6_440 (range_split z6_448 (range_split z6_456 (range_split z6_464 (range_split z6_472 (range_split z6_480 (range_split z6_488 (range_split z6_496 (range_split z6_504 (range_split z6_512 (range_split z6_520 (range_split z6_528 (range_split z6_536 (range_split z6_544 (range_split z6_552 (range_split z6_560 (range_split z6_568 (range_split z6_576 (range_split z6_584 (range_split z6_592 (range_split z6_600 (range_split z6_608 (range_split z6_616 (range_split z6_624 (range_split z6_632 (range_split z6_640 (range_split z6_648 (range_split z6_656 (range_split z6_664 (range_split z6_672 (range_split z6_680 (range_split z6_688 (range_split z6_696 (range_split z6_704 (range_split z6_712 (range_split z6_720 (range_split z6_728 (range_split z6_736 (range_split z6_744 (range_split z6_752 (range_split z6_760 (range_split z6_768 (range_split z6_776 (range_split z6_784 (range_split z6_792 (z6_800))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_424 : ∀ i, 424 ≤ i → i < 432 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 424 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_432 : ∀ i, 432 ≤ i → i < 440 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 432 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 440 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (range_split z7_208 (range_split z7_216 (range_split z7_224 (range_split z7_232 (range_split z7_240 (range_split z7_248 (range_split z7_256 (range_split z7_264 (range_split z7_272 (range_split z7_280 (range_split z7_288 (range_split z7_296 (range_split z7_304 (range_split z7_312 (range_split z7_320 (range_split z7_328 (range_split z7_336 (range_split z7_344 (range_split z7_352 (range_split z7_360 (range_split z7_368 (range_split z7_376 (range_split z7_384 (range_split z7_392 (range_split z7_400 (range_split z7_408 (range_split z7_416 (range_split z7_424 (z7_432))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z8_24 : ∀ i, 24 ≤ i → i < 25 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 24 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 25 → Z 8 i = true := range_split z8_0 (range_split z8_8 (range_split z8_16 (z8_24)))
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
  scr dom_17 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_17 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_17 roots_17 goal_17 10 := by
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

theorem low_17 : Lower dom_17 roots_17 goal_17 10 := S_17.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_17_bits : ∀ r : Fin 64, roots_17.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_17_lt : ∀ r : Fin 64, dom_17.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_17 T)
    (hlow : Lower dom_17 roots_17 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_17, Avail mask256 roots_17 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_17 hfan 0 roots_17 roots_17 rfl hsup0
  set out := (execN C.gates roots_17).getD C.output 0
  have hout : out &&& dom_17 = T &&& dom_17 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_17_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_17 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_17_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_17).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_17)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_17.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_17 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_17).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_17 &&& mask256 = dom_17 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_17 = T &&& dom_17 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_17, hd63, hout]
  have hnc_m : ¬ IsConst dom_17 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_17 roots_17 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_17, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_17 roots_17 0 roots_17 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4274845832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_17.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_17 10 hT6 (by unfold IsConst; decide) low_17

def wit : Circuit := ⟨[⟨GateOp.or, [1, 0]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.and, [7, 13]⟩, ⟨GateOp.or, [9, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_13115_aux

theorem PEqualNP.Outside.L_meta_13115 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4274845832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4274845832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_13115_aux.wit, PEqualNP.Outside.L_meta_13115_aux.wmono, le_trans PEqualNP.Outside.L_meta_13115_aux.wsize (PEqualNP.Outside.L_meta_13115_aux.lower s hs), PEqualNP.Outside.L_meta_13115_aux.weval⟩
