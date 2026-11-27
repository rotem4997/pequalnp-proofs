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

namespace PEqualNP.Outside.L_meta_13125_aux

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

def dom_0 : Nat := 0xff000000ff
def goal_0 : Nat := 0xea000000a8
def roots_0 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 33), (2, 3), (4, 5), (6, 7), (6, 38), (32, 33), (34, 35), (34, 38), (36, 37), (36, 38)]
def r1sG : List Nat := [1, 1, 1, 2, 4, 6, 6, 32, 34, 34, 36, 36]
def r2sG : List Nat := [3, 5, 33, 3, 5, 7, 38, 33, 35, 38, 37, 38]
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
  | 3, 0 => 0x46202a8c32c150cb257ee5610f5fbc57007d8e3c
  | 4, 0 => 0xc27a10467f944054788449cb77342e6e58040aa349727ca3257ee5611fad1ecd0b0816ca
  | 5, 0 => 0x257ee561
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc000000cc000000cc00000088000000c0000000c0000000aa000000aa000000aa000000000000005500000055000000330000003300000000000000ff
  | 0, 1 => 0xff000000cc000000ff000000aa000000ff00000000000000fc000000fc000000fa000000f0000000f0000000f0000000f000000000000000ee000000ee
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xdc544db744da744ea734da644
  | 4, 0, 0 => 0xda7425da74050da724da87450da414da97450da744da7435fda745
  | 5, 0, 0 => 0xda744
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x368300060007000ff8c9707f
  | 0, 1 => 0xfe8f87f80f78c70c70c0036f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xb69b69a605bf584a4049603b
  | 0, 1 => 0xfedffffc4f7bff6e72e40fff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 16 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 16 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 16 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 16 then wireAt i else 0
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_1 : Nat := 0x3333
def goal_1 : Nat := 0x3220
def roots_1 : List Nat := [0x2222, 0x3030, 0x3300]

namespace S_1
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (4, 5), (4, 12), (8, 9), (8, 12)]
def r1sG : List Nat := [1, 1, 4, 4, 8, 8]
def r2sG : List Nat := [5, 9, 5, 12, 9, 12]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xfaf3d3b0
  | 3, 0 => 0xfaf3d3b0
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x330000000000000030300000000000002222
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_1 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_1 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_1 == dom_1) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_1 goalM u ys) : RunD dom_1 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_1 roots_1 goal_1 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_1 goal_1 := by
    have h0 : isConstB dom_1 goal_1 = false := by decide +kernel
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

end S_1

theorem low_1 : Lower dom_1 roots_1 goal_1 4 := S_1.noCircuit

def dom_2 : Nat := 0x333300003333
def goal_2 : Nat := 0x322200003220
def roots_2 : List Nat := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x333300000000, 1, 33)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xffff
def goal_3 : Nat := 0xfaa8
def roots_3 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_iso [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0xffff0000ffff
def goal_4 : Nat := 0xfaea0000faa8
def roots_4 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

namespace S_4
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 33), (2, 3), (4, 5), (4, 12), (6, 7), (6, 14), (6, 38), (8, 9), (8, 12), (10, 11), (10, 14), (32, 33), (34, 35), (34, 38), (36, 37), (36, 38), (36, 44), (40, 41), (40, 44), (42, 43), (42, 46)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 4, 4, 6, 6, 6, 8, 8, 10, 10, 32, 34, 34, 36, 36, 36, 40, 40, 42, 42]
def r2sG : List Nat := [3, 5, 9, 33, 3, 5, 12, 7, 14, 38, 9, 12, 11, 14, 33, 35, 38, 37, 38, 44, 41, 44, 43, 46]
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_4.map (· &&& dom_4)
def goalM : Nat := goal_4 &&& dom_4
def NN : Nat → Nat
  | 2 => 1
  | 3 => 6
  | 4 => 24
  | 5 => 35
  | 6 => 10
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x2c651989
  | 3, 0 => 0xe146d987aeea054388aa2759747fae4571854c561c83c1f2
  | 4, 0 => 0xfa7b037ae7838a1fe68c5eb9c9e2d772bbb52bc6a57f744e9ef637b792f51485910d76e58eb090158cad58426a1cf8c863cbc541420a16ad3d8be7573a5b366c3147983b29616e43189190470e2071120db104600c91eeb004b686ca03b7e656
  | 5, 0 => 0xf16bb5a5ec8f6e8de6295839e0ff3f70deb0dcdadea6adbbd86c0d65d508e921d4c9adb2c6befed0ba4126a8b91eb561ae736661ae41ebada7e1de7e9d9588649c5521128cad58428c98c6547fed28667a692d996d24aa586991ce2463f1beb45acd6bb55400e09b53d7f7b54a0593be48143a504580630f2e1b67d1200c7def1efeb8c61b2929df19cb6222
  | 6, 0 => 0xe505bdfab7253fbda7da18faa1712e8b8888432e5ba073fa5b61388b4d7877b92fef2b28270b03de
  | 7, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000333300000f0f00000f0f00000a0a00000a0a0000050500000505000000000000ffff000000000000555500000000000033330000000000000f0f
  | 0, 1 => 0xaaaa0000aaaa0000aaaa0000a0a00000aaaa000088880000a8a80000a8a80000a0a00000a0a000005f5f00005f5f00005555000055550000505000005050
  | 0, 2 => 0xeeee0000ecec0000ecec0000ecec0000e0e00000e0e00000cccc0000dddd0000cccc0000cccc0000cccc000088880000c8c80000c8c80000afaf0000afaf
  | 0, 3 => 0xfcfc0000fcfc0000fafa0000fafa0000fafa0000f8f80000fafa000000000000f5f50000f5f50000f0f00000f0f00000f0f00000c0c00000eeee0000eeee
  | 0, 4 => 0xffec0000ffec0000ffcc0000ff880000ffaa0000ffa00000ffaa0000ff880000ffa00000ffa00000ff050000ff050000ff000000ff000000fefe0000fefe
  | 0, 5 => 0xffff0000eeee0000ffff0000cccc0000ffff0000aaaa0000ffff0000a0a00000ffff000055550000ffff00000f0f0000ffff000005050000ffff00000000
  | 0, 6 => 0xffff0000ffa00000ffff0000fcfc0000ffff0000f0f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x329de3
  | 3, 0, 0 => 0xca768f4a257934b217964ca379348de7134b237934
  | 4, 0, 0 => 0xa237933d6885a5cf5b216933d6c85e4cb5a256933d6da2668f5b216963d6d85a4cd5a237932d728da4cf5a217912d6885e4cc585c6913d6885f54f5a236963d6885d4cf5
  | 4, 0, 1 => 0xa2379a4d6889a4cf5a246933d6c85e4cf5a216943d6985a4cf50288de4d2d85a4ce5
  | 5, 0, 0 => 0xa2169340f685e71a4cf6c2885e4cf6b2885a4cf6a216994cf6a217da60f6be885a4cf60288da4cf5a216933ce6a2179a4cb6a2181a4cf6aa885a4cf6bad85a4cf6b216933cb602168f1c35a216933c06
  | 5, 0, 1 => 0xae885a4cf6a216933c46a217933cb6a216933c1602884f1c6502885a2475a216933ca6c6885a4cf6a216933c26a216954cf6a216933c560288532465a216933c86b6885a48f602c85a4cf5a216da4cf6
  | 5, 0, 2 => 0xa216933cd602885e4cb5a236933cb6
  | 6, 0, 0 => 0xba885a4cf6a216933c66a2179a4cf6a216933cb602885a3c750288533c6502885a4c95a216933c96c2885a4cf6b6885a4cf6
  | 7, 0, 0 => 0x2885a4cf5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 22
  | 3 => 28
  | 4 => 34
  | 5 => 40
  | 6 => 40
  | 7 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3e4c6ff1fc1f00000ff1fc10003fff003ff0000c6f003c1f
  | 0, 1 => 0xf000000000000000000000000fffffffffff00e03e0
  | 0, 2 => 0xc1b390c1b390000380c1bff0c1b390c18000000380f1fc1f
  | 0, 3 => 0xcfb3f00e03ef0e03e00e0000fffff00e03e00e0380c1b39f
  | 0, 4 => 0xf1bf90f1bc00f03c00f03c00f03c00f1fc10f03c00cfb3ff
  | 0, 5 => 0xfff39ffff390ffc00fffc000fffff0fffc1ffffc10ffc000
  | 0, 6 => 0xfffc00fff3f0ffc3e0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3a4c6e50d41d50d41d000000003df7002940000c66001415
  | 0, 1 => 0x52d4bf52c0aa52d0994290b30200a2fdff5dad2b40ad2b40
  | 0, 2 => 0xd7f3bbc7b3b38723a2c5bbd1c5b391c59291c5b39152d4bf
  | 0, 3 => 0xefbbf3fffffffffbfbffc208af2be2af2be2af2380d7f7bf
  | 0, 4 => 0xffbff7fdbfd5fafdeefafdddfa3de6f83d44f83d44ffffff
  | 0, 5 => 0xfff7bffff399ffd6bfffc2aaffeb48ffd61dffc208ffc208
  | 0, 6 => 0xffffeefffbfbffebea
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 24 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 24 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 51 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 51 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 51 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 51 then wireAt i else 0
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
  | 3 => 4
  | 4 => 20
  | 5 => 56
  | 6 => 14
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xf1f9bb15b00f685d92e3e0c01c79e279
  | 4, 0 => 0xf1a63112f0d3fff6c854d27ab65c8af99e484f4c9dc337ac995cbd9d6d2fe2996698a8af6679720254a4b84750b5378c4a97b06d465b4bdf3f66812a32f5f596286448962323b63b0f1fce070335d817
  | 5, 0 => 0xfde03eecfdb89ab0fa667ec4ea1c807fbc3c0242b7253fbdacf0db7fac1eaa63a7188f03a687f110a67f7706a60109ac915d40018d9f05b38a3920667b1ce2dc741e76a472b20a2a71f40ace6fa9a6b36c4fd1666b3e4af7640b49fc61dff08a60b7367f6077fb105e9639f3598d301e580158be55c13d20528f3a3e51635f9050d47de64d7877b942c1d77f42829c103f2d04c03c9e90833b21efc13a381623372650b93505edad33ba69392c21c6632acab2b22a48ff952514d4b51f3813f41ce122ff1ae8b27a13645f70125878620f1fce07085ae9b3072d757705549da1
  | 6, 0 => 0xf641318ce9082d54af535e0e8c5e12727445a6b56b7180a36949f7d6686e9bda6594bfe255c13d20160058941436908c0f1fce070da784ce
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x20480200144c0201244c02012440c201
  | 4, 0 => 0x2048020020480200000c51012048020000000001000c010134480200000000000004d1010000000100000000000000020000410200000001410812000000000200000001144802000000000000000001
  | 5, 0 => 0xa1000000210000000001000c5100000000020000610000002100000000010008d100000021000000a10000002100000000010008d100000000010000e100000411000008d100000c1100000c1100000000000000000200000001000000010008110000081100000000000000a10000000000000000010000000200002100
  | 5, 1 => 0x4d1000000a1000000a100000811000008110000000002000801000008110000000000000000010000610000000001000000020000000100000000000000010000610000000000000801000000000100000001
  | 6, 0 => 0x200000000000000010000000000000000000000010000000100000000000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 6 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_3 roots_3 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_4 == dom_4) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_4 goalM u ys) : RunD dom_4 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_4 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 6 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 6 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 6 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_8 : ∀ i, 8 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_16 : ∀ i, 16 ≤ i → i < 24 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 16 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 24 → Z 4 i = true := range_split z4_0 (range_split z4_8 (z4_16))
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
theorem z5_32 : ∀ i, 32 ≤ i → i < 35 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 32 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 35 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (z5_32))))
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
  scr dom_4 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_4 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_4 roots_4 goal_4 8 := by
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

theorem low_4 : Lower dom_4 roots_4 goal_4 8 := S_4.noCircuit

def dom_5 : Nat := 0xff00ff00ff00ff
def goal_5 : Nat := 0xee00ea00ec00a8
def roots_5 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff0000, 2, 18)] (by decide +kernel) (by decide +kernel) low_0

def dom_6 : Nat := 0x33330000
def goal_6 : Nat := 0x32200000
def roots_6 : List Nat := [0x22220000, 0x30300000, 0x33000000]

namespace S_6
def pairsG : List (Nat × Nat) := [(17, 21), (17, 25), (20, 21), (20, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [17, 17, 20, 20, 24, 24]
def r2sG : List Nat := [21, 25, 21, 28, 25, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_6.map (· &&& dom_6)
def goalM : Nat := goal_6 &&& dom_6
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x1d20c287
  | 3, 0 => 0x1d20c287
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3300000000000000303000000000000022220000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_6 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_6 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_6 == dom_6) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_6 goalM u ys) : RunD dom_6 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_6 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_6 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_6 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_6 roots_6 goal_6 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_6 goal_6 := by
    have h0 : isConstB dom_6 goal_6 = false := by decide +kernel
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

end S_6

theorem low_6 : Lower dom_6 roots_6 goal_6 4 := S_6.noCircuit

def dom_7 : Nat := 0xffff0000
def goal_7 : Nat := 0xfeec0000
def roots_7 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000, 16, 18)] (by decide +kernel) (by decide +kernel) low_6

def dom_8 : Nat := 0xf0f0f0f
def goal_8 : Nat := 0xe0c0a08
def roots_8 : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]

namespace S_8
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (2, 3), (2, 18), (8, 9), (10, 11), (10, 26), (16, 18), (17, 19), (17, 25), (24, 25), (24, 26)]
def r1sG : List Nat := [1, 1, 2, 2, 8, 10, 10, 16, 17, 17, 24, 24]
def r2sG : List Nat := [3, 9, 3, 18, 9, 11, 26, 18, 19, 25, 25, 26]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_8.map (· &&& dom_8)
def goalM : Nat := goal_8 &&& dom_8
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x317f6efe
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000f000f00000000000c0c0c0c000000000a0a0a0a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf80c7006c303
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc8e729ed737
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_8 == dom_8) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_8 goalM u ys) : RunD dom_8 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_8 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_8 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
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

def dom_9 : Nat := 0xff00ff
def goal_9 : Nat := 0xec00a8
def roots_9 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

theorem low_9 : Lower dom_9 roots_9 goal_9 4 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0xffffffff
def goal_10 : Nat := 0xfeecfaa8
def roots_10 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_10
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (2, 18), (4, 5), (4, 12), (6, 7), (6, 14), (6, 22), (8, 9), (8, 12), (10, 11), (10, 14), (10, 26), (16, 18), (17, 19), (17, 21), (17, 25), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 8, 10, 10, 10, 16, 17, 17, 17, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [3, 5, 9, 3, 18, 5, 12, 7, 14, 22, 9, 12, 11, 14, 26, 18, 19, 21, 25, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_10.map (· &&& dom_10)
def goalM : Nat := goal_10 &&& dom_10
def NN : Nat → Nat
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xe40c141bd051f5075299e96d3a6b8d41206585ea
  | 6, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfff0fff000000000ff00ff0000000000fafafafa00000000f0f0f0f000000000cccccccc00000000aaaaaaaa0000000055555555000000000f0f0f0f
  | 0, 1 => 0xffff0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x87643268643216086320508643158654326
  | 6, 0, 0 => 0x864325
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc3ff0701f0007e07ce3803e00039cc01c001ff1fff1c7fc1f
  | 0, 1 => 0x1ff8000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xff3ff3791f512fe7fdf3a2be248f9cc93c52bf61d6a0c5d41d
  | 0, 1 => 0x1ffc210
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
  | 4, 0 => 0xac05225e5e1d4aa848da8d522637312d25e0cf66
  | 5, 0 => 0xe0bddffad0f6fc56ce00c9b9c5159104c1afdc6dbe3fb924ba7741d8b4992a82ac05225ea0508cfd7ecfa1837702c5a9640253eb554c825e30706e42276bea4325303d371b8a7ef1126b25b70241d3e1
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0xc0000000000c00004
  | 5, 0 => 0x10000010000000000000001000002000000000020000000000200000800000000000000000000080000000000c0000000000800000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 1 => checkCutEntry dom_7 roots_7 5 s ws hint
  | 2 => checkCutEntry dom_1 roots_1 4 s ws hint
  | 3 => checkCutEntry dom_8 roots_8 4 s ws hint
  | 4 => checkCutEntry dom_9 roots_9 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_10 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
  scr dom_10 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_10 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_10 roots_10 goal_10 7 := by
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

theorem low_10 : Lower dom_10 roots_10 goal_10 7 := S_10.noCircuit

def dom_11 : Nat := 0x3333000033330000
def goal_11 : Nat := 0x3222000032200000
def roots_11 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000000000000, 17, 49)] (by decide +kernel) (by decide +kernel) low_6

def dom_12 : Nat := 0xffff0000ffff0000
def goal_12 : Nat := 0xfeee0000feec0000
def roots_12 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc0000, 16, 18)] (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0x5555555500000000
def goal_13 : Nat := 0x5444504000000000
def roots_13 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

namespace S_13
def pairsG : List (Nat × Nat) := [(34, 38), (34, 50), (36, 38), (36, 44), (40, 44), (42, 46), (42, 58), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [34, 34, 36, 36, 40, 42, 42, 48, 52, 52, 56, 56]
def r2sG : List Nat := [38, 50, 38, 44, 44, 46, 58, 50, 54, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_13.map (· &&& dom_13)
def goalM : Nat := goal_13 &&& dom_13
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_13 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_13 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
  scr dom_13 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_13 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_13 roots_13 goal_13 4 := by
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

theorem low_13 : Lower dom_13 roots_13 goal_13 4 := S_13.noCircuit

def dom_14 : Nat := 0x5555555555555555
def goal_14 : Nat := 0x5444504054445000
def roots_14 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555555500000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_13

def dom_15 : Nat := 0xf000f000f000f
def goal_15 : Nat := 0xe000a000c0008
def roots_15 : List Nat := [0xa000a000a000a, 0xc000c000c000c, 0xf0000000f0000, 0xf000f00000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 4 :=
  lower_iso [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_16 : Nat := 0xf0f0f0f0f0f0f0f
def goal_16 : Nat := 0xe0e0a0a0e0c0a08
def roots_16 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f00, 1, 9)] (by decide +kernel) (by decide +kernel) low_15

def dom_17 : Nat := 0xffffffff00000000
def goal_17 : Nat := 0xfeeefaea00000000
def roots_17 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_13

def dom_18 : Nat := 0xffffffffffffffff
def goal_18 : Nat := 0xfeeefaeafeecfaa8
def roots_18 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_18
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 33), (2, 3), (2, 18), (4, 5), (4, 12), (6, 7), (6, 14), (6, 22), (6, 38), (8, 9), (8, 12), (10, 11), (10, 14), (10, 26), (16, 18), (17, 19), (17, 21), (17, 25), (17, 49), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 38), (34, 50), (36, 37), (36, 38), (36, 44), (40, 41), (40, 44), (42, 43), (42, 46), (42, 58), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 6, 6, 6, 6, 8, 8, 10, 10, 10, 16, 17, 17, 17, 17, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 36, 36, 36, 40, 40, 42, 42, 42, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 5, 9, 33, 3, 18, 5, 12, 7, 14, 22, 38, 9, 12, 11, 14, 26, 18, 19, 21, 25, 49, 21, 22, 28, 25, 26, 28, 33, 35, 38, 50, 37, 38, 44, 41, 44, 43, 46, 58, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_18.map (· &&& dom_18)
def goalM : Nat := goal_18 &&& dom_18
def NN : Nat → Nat
  | 2 => 3
  | 3 => 47
  | 4 => 239
  | 5 => 603
  | 6 => 930
  | 7 => 371
  | 8 => 23
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xeb75f46c5260b4b8025e46d4
  | 3, 0 => 0xfa27e057eefdd0eaed912975ea46c1f6e9c865aae828eac5e5dac714e0d21619d76fb95bd7606b2ed225de68cabcafabc53022e6c347c31bbeb2aa39be27114bb85bafe8b71af64aa5a119b8a5950812a043ed5e950bfd339068ab718fee051888343901785fb43b72bd8887697da3cf5c1782475ae7997d5a7423d852a37dce402944ea3bc825453a6bb6723436a12c30bbcd6130771d0022fe76b81f387d20187c2ed315c943e0122741d809064e710663c1a701d2046701bbb2a3
  | 4, 0 => 0x4856c7be484798a6468b869845eb5cb34505964743ff9c304318d6ca41c201a04149bdbe40f2cdd2404018043ef6c1953ed011d43da67a7b3cdc3b433b25911438b159a73782656a371eaccb369c8e0933940cfb3362c63e334f732a3343ac8230cd2e633028f3e52eeba1dd2d08cff32a754c7d29e5ae83291cd8e428e4fbca26c3cb2c24aebcf3243f61ec23bf411422825b47215c1b5b1f8c64581d64632c1bb934101b74cb1f1b56c4de18cf497516b33f7115ee24a91526afaf12e09dcf12b281431184ada7117e5ae41096f481107a4b140e8e70ea0c8c821f09ff579b0863ba4005c12d760580205d03b691550359173d02b0f47e029f5e620266b548
  | 4, 1 => 0x848eb85983a7a3de831f384d818fa073807a2f3f80649a007f3420d77f1bdbab7f0381fa7eeb8bc07e73302b7a7410747a19538479fa721777bd200a778bd94d7786c2b3776cbf917556374374f6417274ca617b731292c2721af45670be7d576fb897496ed76a4d6d6c35466d2353c46d0eddb86ca6c7fc6c49e0646abc42226910059368db0f9e6874b95b679db0b1675b4d726631093c65a22d6f6599250664bff8636250162d5cdba6465c125b1a5bead3535bded3315a5efdcd5a45054c5a2c2dea59e961465965c9d5595c7faa58583af357e31e6e5764049156d5fbf35678c33955b6786c5552131b54f12ea5546b42e452a5fe5d4f5674274f4f02f1
  | 4, 2 => 0xc85fd0f4c824aaecc6dfe259c6d83c60c5d6448cc538498dc52417c9c48d8eb5c480f27dc3d0b655c2a1f231c1b84b34c154d5e5bffab974bf7abb15bf750958bf03b785be7888e8be322b75bcf28e37bcde1badbb851cf3baac3033b976daa8b96965dfb7fea0c8b7506283b48f3658b4316139b41020bcb40c8d62b3acdbaab25d4adeb1bc7a03b1954855b09dd645b0961bd0ae741ddbadcd57a5ada5569dad30f4d2acafe72eaba16124aae91c08aa75a375a87bafc3a48e4e36a1993fd49c4e83199ad848839736467b9343417c90230e008ff3f99f8f8472438d8068e88d09c92d8c8c74c788dc3aa7883913e18828af3f88268d15879e3e6b85ba3013
  | 4, 3 => 0xffae3002ff0af561fedc66b7fdcfd6ebfdba525afd9c132bfa0fbcfaf9a1d5a2f6dad6b0f622c558f609d497f4a584f4f36c0a11ef7a0d2eee5b3cb9ec431a49eb5d684ee9397b18e9350985e8363d64e7865694e6375336e5fa7c90e585c31ce1eed96ce18dea83e0815b37df4860a7def5eb73dd1d7f77da08ce29d82afa81d790f5dcd775733cd767d910d5fcc6d8d3c26efad1f9af06d0807301ceb78ac0ccfe6547cc6226f0caf0d786ca1a1b7ac8e2284fc8c54de4c8844eb2
  | 5, 0 => 0x1e25c4db1d6a57b31cc7c4c71c457b1e1bec56d41be2e8291a631ac11a4ac110182cb54417c82bff1752ee851715e07516fca86416f631e816e6ef68161ec38615ee24a9131aa3e612888ccd1283aafd123e099e12074b6711b00dca1179d41610d606ee108b31050fc9e5d50f6a655f0f4934c70e2fbf900d79cb890d3591b80d31bdf20d2d416d0c9239bf0c79e00e0be980d00b7673f90b0d1a750aa017db0a71ff200a6c0c690a38ec8009f4089109ec9fe509d0c57e096c602d09115a4608ea0cab07a920060794529a0770d02b066a716f065af8c805947e820338386f02b0f47e026da0a0024877fc023ef43201cb210e0189cb1b013755e700c274f1
  | 5, 1 => 0x408614eb402ce71a3fdf78903f3f0ba43e0c79e43de6fdcf3db635933d7bdce63d68049d3c72d4343c39a7123c1a39ca3b792ec93af5ae8e3a300cf63a06e07e385f7a1c3758d5e03693090835c6e9dd34355bc333e5d16633cd77b533c9ffc433727c903367765d3365f3a0332d048932bd4e68329e2ae932922c61323ff97530a656562ff0424a2ecdec932e490dac2c663bc22c15a6212bae16132af9626f2ae698952a23da6e29c4e12d27e6e44c274f272b272842d626de9c4e26bbe66b26a8447724f25ef224e0c8d6246d800b2450623c2419e1ff23cb5651239ccdbb22e782b6224ea2aa2072376d206d0bcf1fca70471ed15b311e55c8501e537c0a
  | 5, 2 => 0x569c579f56373846561b599855faacc655d62f0855c033575583f2e854a11016544e9a74543837d5541d53b753fe39fb53a9202e52db162352ce399d529a75dd5256d44f521c806f51f57fdc51a6b53c5196b9045187bbdc50fca456506eb2234fffdc294ff503ef4f7c60744f79cde74eee75374eb3dff64eac6ec04e87686e4e29c7d14de852f14d6ed5974d33af8f4d2923874d2805f24ce284c44c9cf8434beee6fc4a3e3eab4a1b7e2849b047704986cc25496d53bb492cc47047af8a0a4600ab8845e8f26745a182e44597b3564509be17441b97814411cfac439d85cf435d07ff42ec1c5a42e7e3ea42c3a86e428dc58a41ed2050415ca96e40a7298d
  | 5, 3 => 0x67f0f6da67d2252a678c34f8676b15b06727cfa766fdde0f66fb1c80668b1e6e65a22d6f656decab6560118b652361f264de372464ba29a9645dac91645d671c641d64326417a29d6404f01663f3cb9d638b283263474bf462db1c0c62602b1062393cb561eae8ca61ad5b4b617fe0fd61382c096126dd7661117c48610c61d96010936a5fe7e4ef5fa4c0845f7599dc5f700d1a5e2d8aab5da230e05d21c4245ce063db5c9ffa7f5c4eedba5bc8ec3f5b6fc6e95b3ef3845a351edf5a0e3ce659be44955967c8f758b9eb7958a6f8795891c98a5890f56f5870ff4f57f00393579673a2577377cb5745f8dc572127c557208cb35708b3a957058ade56e6cdf3
  | 5, 4 => 0x84698e75845134c482c55ac082b9b69c8212fe4a81a4eff581a2cdcb80ed0c428084472780536cf67fc205cf7f7ea8347f2210c27f1ec19d7f0b1a867e918ca67e88360d7e60edc97e59dbf87e48f78f7daa8d6d7d8bba9c7cf06b427cd1f5077c4828367c0194777ba6ee947b2626847a76756b7a6158be7a506f8f791c630d77ca74e677937d8f7790896c776684f475bbfa4c754a7af0750c721874f742c7745c49f0743ecfa672fc213072c825e571c5d7ad71a3faaf701596636ca4a14a6c6c49876c6b8da26c5dccc86c4727326c2f51d46b8cd3026b23bd9e6b0981336aec875b6a93dd8b69b50a696969bc1a68c36bc66896931a6842f50e68108bd3
  | 5, 5 => 0xa12b98dca1093cb4a0b49a9fa0593d1f9feae83f9fbcf4a39f8a09519efe070b9ed753839ec8dab69e4c362d9e2603659dde4e189d01f0759c4914fe9c3bdc8b9c17f24e9c06ff279b6d2a959ab138179a5524859a35b45298e3524198c6079597cea53d97716c839738ad00970bcbef9693b24a94a1c9789457b35d936dd64b932fd64a9298f4ac9225cb7091fa01bd919d2683912cef69907324c28f6469e28f51656e8f50482c8e26c2bf8e209bbb8d82dd5c8cedacd18c3f68f78c31cecb8bf059ec8b83519c8b76cf9b8b4634ff8b12713f8ae74c6489cd889b8903187b87ae630587861b0e87194e5785e3397885d74f348520da5c84f8457a84973f94
  | 5, 6 => 0xbab2170cba448e79ba2a0bd3b9eae4c7b914f590b8809cc5b7b43f8bb75c0c97b757a727b70beaccb5fb4010b5eeeabcb5dc3306b56d3772b54c59f0b537f888b4bc74ebb42870e9b41e24b7b3eca227b3cce361b2c69723b2b79c1ab299cca6b26608e6b2647874b192cbbab119e5d2b094a0b1afb9ec24af845120af6d6ebbaf527550ae44a233ae3af661ae3211d5ae2bdd87ae078702adce6b9bad9d4a94ad603c84ad601288ad02c26cac22dcb4aba1afbcaaff64dea9b888c8a909351da8f3a15aa898caada8821919a85241b0a6db69e1a6893e1fa6768669a5fe8323a556c84ea3d3c556a36482bda2b69e03a296d7afa22de227a1d69c51a171b865
  | 5, 7 => 0xdbb8451cdb6b1a22daea3edfdac5427bda6117bed978b2aed6a13764d62314ccd5ee461ed4c71adbd443ec35d401e4acd38d7cf1d367c20cd1f7228dd1a9ce41d03de5e2cff51147cef151a2ceccb289ceaca55fcea7736fce71bc15ce1795b1ce14f68fce094f7acde805e0ccbb893bcc5bd116cbb0b965cba7d1accb80f6e2ca6c0ad6c9b086d2c9298db9c9215889c91f365fc90ea0d3c7ef7d92c7eee2b8c7cc907dc7a74112c72e2c94c6a778e5c5d6448cc58fe8dec5842aabc5795c5ac571c825c54f1ca7c4a7e0f7c46929e7c3a7a319c1eb3fe6c197032ac0c5d13ec05a918fc043f5f1bf582543bf1bf8a0beb5652bbe1f64edbc3b877cbc2db16e
  | 5, 8 => 0xf43b197af40d0db1f3c056cdf391830df343dceef2f8ea79f2f181b2f0860121f01f006aeffd0b81ef72c857ef721839ef3fcfbbef390e9eeeae5ea5edf2d9bceda89078ed3241faed31415ded1c15dfec229bcaeba104aceba08618eafcefadeabad41dea52045ae9ac0f0de9683f34e93dc15be920f5ade8a1808ce7c3be80e6d04f60e6c25cf1e6bfeabee6bdc894e690d205e5a0c77de58b804be4129520e3f9b5a8e3f78b60e3b31c60e39ce52de3964059e2f1edc5e2ea498fe2d7e608e23edf5de1b673cce130803ee0b97435df377c0adf1f8621dd58e65bdd4e81f4dcf85272dced9aa7dc756ec8dc730934dc3faa6cdbef570fdbe50096dbc3afcb
  | 5, 9 => 0xffe435a3ffae0e75ff8ba194ff430832fe885360fe37fb57fe11464ffe0ef89dfdd6c4f7fd6a5f57fcac40e4fba4d97dfaa630edfa6d48b3fa551251f9940a74f6fd43faf68663a7f638427ff603d96ef5cd81faf5a79f2cf58ae842f5803127f4b0c0fcf4ac687bf4a44342
  | 6, 0 => 0x14e002401486263b14736e8513e1552d13c7990313346ed1133218de12ec372612a3a5671232479711fced1511d4f792118eca211173f9011161181a11408e9a1106ad5710f49ff50ff651070fe9faec0f8e38f60f8899180f115ba20ee2d2210ee0af2a0edf18670e5127a30db432850c8aad3c0c498d8c0c3486130bb0c3ae0b258c830b09f3650af23e1b0ae653d70a7677f50a5f1f610a0528f4080f361f0808f998078adcd907530e340720ca0a06ce230906cbb1b4068a399a05b8649705a9e53f0575e13b0520799e05169eb0050dc1e8048dacd7042d77d5035b2fd102d6a72e025216e80249a99b01427f89012a58400101e60c00ec2b2d003e83f9
  | 6, 1 => 0x2686b9112685aea52654e049263aeadb25fdf32825d56e8125c5c2a22569b56a250b3e6a24f25ef224cbf94624af0b1424a38298247d56ba246d800b23e6582623bb3be3235b3ad0226df44b21ce372520eebdc420d56179207965cb20182f6b1eedab581de643f11de45f961dbe4d991d07cbc61c967cc51be2e8291be14d961ba2e6ed1b805bb41b3bd7731a23cbaa19ff9c8019e5257c19ba301a19b9717319affd6f19a82cdf1966b8001949528b193eae6e18bfb7c3187cdaee186cfbda18260451181c0a6c17fc7f6d17953088175d1cd31701656116edd2ef16abddcf167bcf1e165a14331609fe781603f2a51601c14115f4eac915c3143a155ed0bb
  | 6, 2 => 0x36c76ce136a79752369ac91a35a96a4635999cd9356b27a5353872e33536d8dc3510021135009d3534c8f0c7347c735e3392c792338dfabc332ae38432fa2f9532e16b89328e8708326bf53f32543cf331fefd8b313fc734313665253018e9f92f2d39052f15a0e52eb2c9812e8c4cc62e2aeb442dec4b6b2dc4434f2d63ee082d6146532d52d1502d44ea432d3352b72cf6a4682ce1824f2c4f91e52c42325c2b52c4ba2b27b74c2ad9fd9b2a60e87e2a47f4e42a2684592a1fc85a29e188d32992b932293f76f02912a74928c8048a289c633c28610c6c27d2a87727bde86d27b8940827b671de27a5dc52276143a026f72d0626ceb60226af69af26ac92fa
  | 6, 3 => 0x4914e5ad4901a2e248683a634828752047ff7ab347f536de47baec8d472b0d9a470778494640bf18462000d245d098b6459ecff74539148445280d8444d46f7844ad1ab2446729e6440b24a843c469ce43ac9409439588c34286fca942454fb94221143d41e4d47741892944414a8c1f40102aba3fdc66fa3fc23f033fc11baf3f3ce45f3ee052543ebac68e3e8c263a3e0f9fc73d7e58413cdfdd733cda06bb3cd948b53ccc486b3cc696da3c0ce04f3bf021da3b43ce223b13a8a83b0a44b33ae953a93ab95d963a7c3c153a7189e33a4fc20639ffcc7c39ddbebc3996a26039817a5e392d295a3821da66380d7bfe37f5ed4437d59bc637d06dee36de7a87
  | 6, 4 => 0x5bb03c075b26580e5af98e3459b8610d5954cf0e5952f0d857a4871957a1bfdd5702a7c256f3df71569febcd56488c3a5618ad1555f9c36e55a75e14552e1ac4552ba96f54fb57fa54d9fe7754a00c23547299fe54652f1354499f4153eff8a953dbb72c53d41e1e53bbaa0253514749533b7ec15318541d5257aedf5188bd315139dea750288f955019d6c14f7b2dd24f7b0f794f526fbe4ecf76c84ebf453b4e25e6484def80874ddb76074d84259f4d67b2e34ca859dc4c4491e44bb67d884ba1260e4b93e1974b81ba084b093b3e4ab9d7494a932f4e4a8570144a4249ab4a3ff2504a20e91b4a0a039049f2e31049b6e59a49ae95204990919f49894780
  | 6, 5 => 0x6b2e8ee46aec875b6aafcc206a95be0b6a41599e6a08bb0569c0add468e2482d68b691b768b68ec968ab6b9568a8fa4068959ecc6883db64683fc95b67eee67a6728889166d0a3566684dce865e88a3d653364ff650512e26502386064a3ed3364610497642e8ac464179578640f62e363bad2eb63a6a9d3633765a862dfa08f62de92fb62a39a81626e518e625d8697624cc7996220e30461f617a361b87237618076186131deb86119d7e160fe5bb260f47f6c60d62fb15ff943825fa001255ed985675ed6a3f15e8c56795e5ba43e5e366a5f5df837b25dda43b15db6ae185da6006b5d71535d5cd9f6e05c97debb5c5c6ad45c2303735bf13ab45be81a29
  | 6, 6 => 0x7a2a8dff79e85dd379d7de1679d3e13a79bfc59f79bb6d1e7961f727794a1e1d792b8cc8791c125478a087b07878a2ba7852e1917847c1c2780086557723c8d076e1a5f076c3631076b57f7c76b41f6f76b21b94766e04be760a28d075ea2a0475c13b5b74cf39e47481ccfa74601fa7745deae374481341739c3b75731046f8730cc97a730b27807301de5f72d338e87241469d7236e265722b1a8271ff99de71b731cf719f8882715bc4407136fac37111f3bb70fe4ee070ce38587099e98f70345b60700bf4506ffe59226f77c41e6f6a8dfb6f23ef386ebb13b06e7107f36e027d566df7e42c6def4db26da876da6c3e88df6bcccd376bc8f9716b9d976b
  | 6, 7 => 0x8aa3b04f8a7c25bc8a69d2278a2e7f9d89e93ef089acfcb189907459897dd41489693a1b893e8c2c8934bc8a88cc88e288b00c9586da25b186a84c4a869ed19086981ab68676ba26865cbae886465a8a862a726a85b60ed484ff925284fac0d5849aa637847e77b1847e462b8455b14984520cd584380434842c533e83f4ab6383e08d34831dfd40831ab88982c96d8a82b11d7e827963fa8239485c8222c68f81edf27781e62af8817ebe3581025bc48101e0aa808751628071c7677fca15487f59c8ed7ea020fc7e9756197daa8d6d7ceab7897ce9266b7c2f60d67bd003c87ba594057b5baecf7b47a4e87b045a637aaf2d897a8787dc7a8392537a7a23a8
  | 6, 8 => 0x9db830709d7b9d929d72dd149d55141e9d4043e99d3bb9e79ce0c3739cb145819c32deb99c05368b9c00c3dc9be41d5a9b5e450a9ad8f9be9aca79e39a4d785899fd1e0d99a4f628998cea0d998059c0997632ef988f1cec987811a697a002259798951797962ac4976491d0972fe19096fd835396cf405e96ced85296764443951cbb3294a0b6d3947d9aae940a6f8393104a2b928065269231308291feb1dc91ba058f91a73dfd9190d39c9112800b906d80ec90680bc68f2383368e7b64d08e70bc488e3f8c778dce3d768daba1d48d8ba3088d6360018d261b1b8cfa91f68cb966468cb824a98bdc92648b87a4638b4e53938b4da15b8ae768e48aace1a0
  | 6, 9 => 0xb03df0bbb01ef75baff20c80afc500beaf91d673af6565fcaf616e2baeeb3210aeb2ceaeae45c213ae147cf0ae110966ad90c81dad7f4391ad64f2d1acf5e8efac374779abe530a5abcaeb0eab7ff0caab6a77ecab5d2e2fab37265aaa4c653aa9efcd79a98e4816a9608d64a95ab8cba8e78fc4a8d57a2aa8cca005a8b83798a881d6d5a84782efa81e07a4a79e1993a7973e8aa76244d0a7553701a6d8aa08a6919f97a61bfe94a5b2d2f3a55beef2a5375660a5268c5fa5121f85a506c534a45512c8a434b4b6a41ce4eaa3744415a36482bda35b4fb5a2cd8bc3a18357d9a17eb990a0d162fda068b6649f8ceb469f48540e9f1a60729f0d923a9e8992aa
  | 6, 10 => 0xc0f7668fc0e08b57c0d8bcdac0c2be92c04496cac0171c7cc00cf403bfa39d58bf83682fbf662c09bf39cbf0bea336b7be8463e6be0cd55bbdbc7deebcf6ec4abccba248bccaf6d5bc67da83bc545819bb779f5abb75fc4ebb6aaac0ba6027beba133d13b9fe2647b99d8907b91d4ce9b8d90467b89e2e8fb88f7056b88932b6b8767b00b7eb4147b7dce78eb7b27654b7ad2f8cb7083aceb6d8a086b601f9d2b5f54076b5dd345bb5c7ebe9b5b55af9b57c967eb561d715b5406affb533931eb46735e4b454fa62b42863c4b303514fb2ce525eb2c0fc52b2b48f36b2a6c045b29648ffb272d876b22053d7b2118fd6b204a317b1847130b13563bfb0d3c397
  | 6, 11 => 0xd1296545d08e6ef0d05d132cd048f176d02d5d1bd028b587d01c2c80d019a99dcf78f9d1cf527d16ce844c52ce0a112ecde66f1dcdd3764dcda6e723cca414f9cc804dadcc7bfae6cc314ee5cbd5b4f2cbca57dbcbb9f257cbb5b04acb5a385fcb3bdcc9cb2d3d5ccb239f89cade62b1cab81a64caa6b7f9ca5d1f3fc9e93248c996b3b6c92a9c24c90eb287c87ec458c86c0ca2c74c4e87c73369bbc6e4d562c6da308dc6972f43c63e6ab8c63e4d23c637c9f1c61983a6c5c2d3b0c595198ec4ee7d33c4ed54adc4d22123c497cd3dc469c87ec3e122edc3be040ac3516528c22c52b3c20d3382c1fa1783c1907b16c15c2f7ac148abb5c143d5c9c13f717f
  | 6, 12 => 0xe4d154f8e485a5e1e476b4d9e4635b42e45d2c07e3af474de38f80f9e33cbff7e2f6af66e2e47feae2e44efbe247b55ee2433ca3e230c8c7e1151f08e0e69321e0932adae0859490dfcd3263df7909f5df6bddf0df21d8d9df17ac0edecd4938debe8247de99cc50ddb5fd1cdbc7e08adbc7af05dba80839db566004daf18bb7d9ad9916d999119bd8d16934d8c9c9e2d8c3dd20d872797ad86b43ded85d0165d82123ffd704847fd6a5bda7d669db5dd65d9880d6382f23d627c4ebd615987fd5c9d7fbd57db6c6d53d3f77d528804dd4667f95d445852fd3feda6ad3fd79dad2e063b0d2def3e9d2d60b25d282ff82d26d319fd263d178d2370a95d1399e4d
  | 6, 13 => 0xf49376aff410061df3b03a53f3974e1bf34d8d5cf31deba9f318916ef2fd4c61f2d66f9ff2b38eeef2b2f7b9f2a6d50af2a33ee6f29edce5f24a19dbf23a1c75f2367bbbf0f8df95f0bdaa08f052953bf0346202f0297054efee1f55ef7c6c39eecf8408eec40f0cee5bfb02ee58bbd2ecaad606ec6b46deec53a50dec36d44aebf335f6ebefca4bebbeebd1eb93c63beb6154feeb36180ceb121e74ead2e780ea99b7d8ea87956bea86642cea7cf14eea5a5b7cea56c1efea326695e9e8d9b8e9e0e609e96fe5a4e96f9708e96cbedbe9644731e93f4a53e8e66798e8cbcf91e88e9a99e8529c71e7d15352e7abfef4e78c2717e662ee24e4f80626e4f2353b
  | 6, 14 => 0xffae0e75ffa2aab0ff8b0fb5feb6d93cfd601635fd3430c6fd1f0f41fcd91be7fca28232fc82a2d2fc758997fc6afe7dfba4cc58fb992bf4fb314dddfb294fc5fa75cae1fa1aff5efa06476af9d42adcf9cab482f8ba2970f867a20ff70808aaf6ff9e9cf6ede9c0f6e1ce90f681b3f2f66bd375f665e0bcf6535463f6281cb5f5277aadf4f3fc00
  | 7, 0 => 0x2a6cf07129c478db2964176b28a4a83e2752ae7526beaf6f261c309d246554a62429651523afce9222c735132179389d2064873a20292edb1fb72b911f3d31db1eb3facb1e1aa3ae1d989e101d89743f1d81c57f1d094b741ca0b1831c53b96d1bea35011be563841bde45011b8548e619b1d4481923eb0b17206e35170db67f16e8db1816b50ee915ff8a471581f8c8141a4f1c14121a0c1317dd2b12baa67712324797119811441187183a10d1aa9610c280c50f8b2a5f0f3d84400e7dd0190e783ebe0d9cbe430d4d98860cabde0a0c22507d0c167f100b989d440acf09dd0a172c4909f5ca2f09ee1b6f06b07a0306291d83044a0e720086a50c00649915
  | 7, 1 => 0x4f0fba7a4ed5e3f64ec05ebd4e9d19034e2ce2974e1db72a4dc27b5b4cd8ba054c4c79c44c1e35cd4b0c2c394b02825d49e125c6499b08ca4980ebae48f889f848b0ac9d434ac0324309ffd8430588364214fad141d9fb7841d622d341a4b5d64079af6340455b7a4025ca0a3f49363a3f086e6d3e4ce77f3dc34cb73d6d0b963c9d75a23c3d49423c21f90f3bf167e33b0787993b0516443a8b9b213a8b1a653a4766343a305add3950034038ad846e36c744ae36778df535f834e9359f67e73574355934a8e39d34746a9f339be83032ba82ac31381b073122199e2f7655c82f62b4552f1362052de85b922d90db782cebdf402cb7e2692ba0a43a2b0f5670
  | 7, 2 => 0x8029ed027fe35f827f5f0e0b7f27d8097ebbf6017e8559377e77018b7cd372a07bf0d3337ab597257a7a23a878925775785a178977d135d0779372647770373f73f60c3a72b283397260e48f70cdf074709466926f69601f6e2bfc016d483b2f6c4b6e046bed6d236be1bd3a6bcb63fb6b46b4d16ad42daa6a0139de69c0add4683fb3fc67c75f4c679d352a6733942567044c4c66fb4c91651506a464cf00c56401590263669d9561aa33685d93d62e5d7bf2db5b9aa8305af03eb05aa8a6b95a3c07d75a3757b85916f562584e132a582e787856abec625640306854b47b98531915d1530ec13f523dc21151efbb60514aca6d50c4b4ed4fb2394c4f943bc4
  | 7, 3 => 0xa98c5b5da8e78fc4a8d9852aa73cdd50a5103ec2a4a02823a499e38aa494c22fa3f2435da36baaf79f84ffc39e58572e9db654639d3508f49d1bacbd9c97dd089bfcd7929aec1f2b9a81c9ca9a36658d996c23f4992721c2989a692798411d8197ec88bb97d6cddc9710a45896e3fc3596a4b77d9680ac869603a498956b43489497281e944ede0094331b659409b1f093602c4692b08ece9117715e9074f28c8fa4cc1f8f9d1d5f8f6e24048e4941358d1e3ac28c8386ea8b7e195e8aeb8c5a8a81f0ca8934bc8a89211e6a88f823fd88ede028877c8a9f8651842c8635a6fc85f48e9f85e99b5485520fcd85210b03848e320d833df90382ddd8a581bd8a2f
  | 7, 4 => 0xd87f9952d7c2c847d7c0c947d7661623d697c1d4d468faf0d43f7d82d3152e0bd2f75b26d1d3f658d0dd3a20cecb96dfcdb20f90cd856bc9cb46a5f8cadf9d59c8d8951dc5f36a1fc59d6c30c576ef75c52f7576c44be902c41df566c33e8ebcc31b6fd9c23de552bf8705ebbeb2f988bea88b1cbea336b7be907f01be4be64fbe107ab6bde1cfb5bd3f82f8bc545819bbb69bf5bad08760bab08b31baa8a17cba477786ba45dd7fba1f06b4b9714c04b702d21ab55b444cb52557b8b4e46fecb403d0cab37ef559b2dc7687b272f2abb253eee6b0e1dcffb080f6ebada32de2ace974c5abbe6e52ab94b348ab681b8eaab1140caa87c3f1aa38618da98e4816
  | 7, 5 => 0xffcceadcffa13466ff939cefff3992a2fe091979fbefb591fb192d73f90b85b3f80fe67ff76d67adf6657479f5a8ee32f5210d0ef38ef249f30eb1d1f30da622f17a65ebf117a0a5f03f71bdf03d9387ee22ff53ec164c1eeabec0cde85aee1ae73f702ce72fe7a7e5ff6e7ee575a6eae51088f7e3d420a8e32cc12de2e94854e1b1f408e1283faae0f3695fe07b344ee0063b84df63bcb2dede789bddfd151addd7f9c9dd4db3aadcbb3b65daf5c757da802b72da26b2c9d9b9b7a8d970baf0d96359b3d958a3e4d8cf7726
  | 8, 0 => 0xf2854adfd1efb8f3c3d681efabccd6f49b34b1218a7994f87f4590c97e1a8a567cea112d76f0de33764e5f61705b5d9f61ca40085cde0cce51bb2a0f4aee73793e277fff34064f6c1b78d4bc1561a43a0e7e151305169eb001bed059
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfafafafa00000000eeeeeeee0000000077777777000000005f5f5f5f00000000555555550000000033333333000000000f0f0f0f0000000000ff00ff
  | 0, 1 => 0x3f003f003f003f00330033003300330011001100110011000f000f000f000f00050005000500050003000300030003000055550000555500000000ffffffff
  | 0, 2 => 0x5050505050505050303030303030303010101010101010100ff00ff00ff00ff00fa00fa00fa00fa0077007700770077005f005f005f005f0055005500550055
  | 0, 3 => 0xf0f0f0f0a0a0a0a0f0f0a0a0f0f0a0a0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0e0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0707070707070707
  | 0, 4 => 0x1515151515151515131313131313131311111111111111110f0f5f5f0f0f5f5f0f0f0f0f0fff0fff0f0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0f0c0c0c0c
  | 0, 5 => 0x33333333303030303333333322222222333322223333222233303330333033303322332233223322323232323232323230303030303030302222222222222222
  | 0, 6 => 0x5550555055505550554455445544554454545454545454545050505050f050f05050505050505050444444444444444433333333333333333333333333003300
  | 0, 7 => 0x5f5f5f5f5f005f005a5a5a5a5a5a5a5a5555555555ff55ff55555555555555555555555555005500555555555050505055555555444444445555111155551111
  | 0, 8 => 0xa8a8a8a8a8a8a8a8a5a5a5a5a5a5a5a5a0a0a0a0a0a0a0a0a0a0a0a0a000a00099999999999999998f8f8f8f8f8f8f8f88888888888888885f5f5f5f5f5f5f5f
  | 0, 9 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaa0aaaaaaaaaa88aa88aaaaaaaaaa00aa00aaaaaaaaa0a0a0a0aaaaaaaa88888888aaa0aaa0aaa0aaa0aa88aa88aa88aa88
  | 0, 10 => 0xbabababababababaafafafafafafafafababababababababaabbaabbaabbaabbaaafaaafaaafaaafaaaaaaaabbbbbbbbaaaaaaaaafafafafaaaaaaaaaaffaaff
  | 0, 11 => 0xcccc8888cccc8888cccc8080cccc8080ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc80cc80cc80cc80c8c8c8c8c8c8c8c8c3c3c3c3c3c3c3c3c0c0c0c0c0c0c0c0
  | 0, 12 => 0xccccccccddddddddcccccccccfcfcfcfccccccccccffccffcccccccccccccccccccccccccc00cc00ccccccccc0c0c0c0cccccccc88888888cccccccc80808080
  | 0, 13 => 0xdcdcdcdcdcdcdcdccfcfcfcfcfcfcfcfcfcfcfcfcf00cf00cfcf8a8acfcf8a8acececececececececdcdcdcdcdcdcdcdccddccddccddccddcccfcccfcccfcccf
  | 0, 14 => 0xececa8a8ececa8a8eaeaeaeaeaeaeaeaeaeaeaeaea00ea00eaeaeaea00000000e8e8e8e8e8e8e8e8e0e0e0e0e0e0e0e0dddddddddddddddddddd9999dddd9999
  | 0, 15 => 0xeeeeeeeee0e0e0e0eeeeeeeecccc8888eeeeeeee88888888eeeeeeee00000000eeeceeeceeeceeeceee0eee0eee0eee0ecececececececececececececcceccc
  | 1, 0 => 0xf0a0f0a0f0a0f0a0f080f080f080f080eeeeeeeeeeeeeeeeeeeeeeeeeeeceeeceeeeeeeeeecceecceeeeeeeeeeaaeeaaeeeeeeeeee00ee00eeeeeeeeecececec
  | 1, 1 => 0xf0f0f0f0f0a0f0a0f0f0f0f0f000f000f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f080808080f0f0a0a0f0f0a0a0f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0
  | 1, 2 => 0xf0f5f0f5f0f5f0f5f0f3f0f3f0f3f0f3f0f1f0f1f0f1f0f1f0f0f0f0f5f5f5f5f0f0f0f0f3f3f3f3f0f0f0f0f0fff0fff0f0f0f0f0f0f0f0f0f0f0f0f0c0f0c0
  | 1, 3 => 0xfaaafaaafaa0faa0faa8faa8faa8faa8faa0faa0faa0faa0fa00fa00fa00fa00f8f8f8f8f8f8f8f8f5f5f5f5f5f5f5f5f2f2f2f2f2f2f2f2f1f1f1f1f1f1f1f1
  | 1, 4 => 0xfafafafaeaeaeaeafafafafac8c8c8c8fafafafaa0a0a0a0fafafafa00000000faf8faf8faf8faf8faeafaeafaeafaeafaeafaeafa00fa00fac8fac8fac8fac8
  | 1, 5 => 0xfafafafafafafafafafafafafaf8faf8fafafafafaf0faf0fafafafafaaafaaafafafafafaa8faa8fafafafafaa0faa0fafafafafa00fa00fafafafaf8f8f8f8
  | 1, 6 => 0xfcfcfcfcfc00fc00fcfcfcfcececececfcfcfcfca8a8a8a8fcfcf8f8fcfcf8f8fcfcececfcfcececfcfca8a8fcfca8a8fcecfcecfcecfcecfca8fca8fca8fca8
  | 1, 7 => 0xfefefefefefefefefefefefefe00fe00fefefefe00000000feecfeecfeecfeecfe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcfcf0fcf0fcfcfcfcfcccfccc
  | 1, 8 => 0xff0aff0aff0aff0aff05ff05ff05ff05ff03ff03ff03ff03ff01ff01ff01ff01ff00ff00ff55ff55ff00ff00ff33ff33ff00ff00ff0fff0fff00ff00ff00ff00
  | 1, 9 => 0xff55ff55ff55ff55ff50ff50ff50ff50ff30ff30ff30ff30ff22ff22ff22ff22ff11ff11ff11ff11ff0fff0fff0fff0fff0fff0fff0cff0cff0cff0cff0cff0c
  | 1, 10 => 0xffaaffaaff88ff88ffaaffaaff00ff00ffaaffaaf0a0f0a0ffaaffaacc88cc88ffa8ffa8ffa8ffa8ffa5ffa5ffa5ffa5ffa0ffa0ffa0ffa0ff88ff88ff88ff88
  | 1, 11 => 0xffccffccaa88aa88ffccff88ffccff88ffccf0c0ffccf000ffccaa88ffccaa88ffcca080ffcca080ffc0ffc0ffc0ffc0ffaaffaaffaaffaaffaaffaaffa0ffa0
  | 1, 12 => 0xffeaffeaffeaffeaffeaffeaff00ff00ffe0ffe0ffe0ffe0ffccffccffccffccffccffccff88ff88ffccffccff80ff80ffccffccff00ff00ffccffccf0c0f0c0
  | 1, 13 => 0xffeeffeeffeeffeeffeeffeeffccffccffeeffeeffccff88ffeeffeeff88ff88ffeeffeeff00ff00ffeeffee00000000ffeeaaaaffccaa88ffecffecffecffec
  | 1, 14 => 0xfff8fff8fff8fff8fff0fff0fff0fff0fff0fff0ffc0ffc0fff0fff0ffa0ffa0fff0fff0ccc0ccc0fff0fff0aaa0aaa0fff0ffa0fff0ffa0fff0aaa0fff0aaa0
  | 1, 15 => 0xffff0000ffff0000fffefffefffefffefffcfffcfffcfffcfffcaaa8fffcaaa8fffafffafffafffafffafffaffa0ffa0fffafffaff00ff00fffafffa00000000
  | 2, 0 => 0xffff3333ffff3333ffff3030ffff3030ffff2222ffff2222ffff1313ffff1313ffff1111ffff1111ffff0a0affff0a0affff0303ffff0303ffff0033ffff0033
  | 2, 1 => 0xffffaaaaf0f0a0a0ffffaaaacccc8888ffffaaa0ffffaaa0ffffaa88ffffaa88ffffa8a8ffffa8a8ffffa0a0ffffa0a0ffffa0a0cccc8080ffff8888ffff8888
  | 2, 2 => 0xfffff080fffff080ffffaaaaffffaaaaffffaaaaffffaa00ffffaaaaffffa0a0ffffaaaaffff8888ffffaaaaffccaa88ffffaaaaff00aa00ffffaaaafcfca8a8
  | 2, 3 => 0xffffffff00000000fffffafafffffa00fffffaa0fffffaa0fffff0f0fffff0a0fffff0f0fffff000fffff0f0ffffa0a0fffff0f0ffff8080fffff0a0fffff0a0
  | 2, 4 => 0xffffffffa0a0a0a0ffffffff88888888ffffffff55555555ffffffff30303030ffffffff11111111ffffffff0f0f0f0fffffffff0c0c0c0cffffffff05050505
  | 2, 5 => 0xffffffffcccc8888ffffffffcc88cc88ffffffffcc80cc80ffffffffc0c0c0c0ffffffffaaaaaaaaffffffffaaa0aaa0ffffffffaa88aa88ffffffffa8a8a8a8
  | 2, 6 => 0xfffffffff8f8f8f8fffffffff0f0f0f0fffffffff0f0a0a0fffffffff0a0f0a0fffffffff080f080ffffffffeeeeeeeeffffffffececececffffffffcccccccc
  | 2, 7 => 0xffffffffffa0ffa0ffffffffff88ff88ffffffffff05ff05ffffffffff00ff00fffffffffcfcfcfcfffffffffcfca8a8fffffffffafafafafffffffffaa0faa0
  | 2, 8 => 0xfffffffffff0fff0fffffffffff0ffa0fffffffffff0aaa0ffffffffffccffccffffffffffccff88ffffffffffccaa88ffffffffffaaffaaffffffffffa8ffa8
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x894097ce78b2511c5962a93
  | 3, 0, 0 => 0x77a45025f49e289225f48b3b1228549e224be4f48b345526448db655a6447fac15264475ba5228547fb61586449c3fd78af49e45974a249e45962af48b2a50e6448b3011c8449e375744f47fac5524f4
  | 3, 0, 1 => 0x75ac9228547fb6562a948b3ad688549fbfd78af47fb915a8247fb4d566447fb65546448fc7578af48f3655a6449ab01688548b301527948b291387948b3ad368547fb01588448b3455464475b7122854
  | 3, 0, 2 => 0x6ca45025f48b2913a6447fa913c6447fb65527949e2c9104f48b225026447fb015880489301228248fb0164a249d301688547fb4d526448b3011e8348b399747649e2250a5f48b3b522854
  | 4, 0, 0 => 0x89301226327acf1feb15793d63eff722c15eb1f602e964765602450a812fabfdd6893213d63ec0592bd0ab3f7fb015e7957faa50e6427abfd808e4213d5feeb48a148eb477fb65586457fb015864272c7d80b248a156790c722450ab1f7fabd3e645
  | 4, 0, 1 => 0x8fbfda4af322d05fed656991679166024508b35602450a5f57fb01546427ac7dbcdc48a155fed9471909cb1e602b4c84f59fc29a2af322cbe1cc048a15670ff57a74c8b3c8b2bd0e6458fbfdd0af2dacf1fed956991678ff5d2889eb16602bd48795
  | 4, 0, 2 => 0x9c3fda2af322bad80914297d67916449909eb1f602450a7057fb45526427ac7da2af3217d678ff6cab8c8aff68abd4a6459e429a2af322cf1c8b24893d67f1668abcc8b418b301228359e3bd22852fabfdb28f3213167916722d09eb3c6ea44c84f5
  | 4, 0, 3 => 0x8fb0112852fabfd5ea44e991679166ca4506aff6c23cc84f593bfd5e9d322cf22cd1579915feee48a049eb3f7fb455e7959f459a09142ac7e0ed157991678ff582bcc8b438b301228558fbf1809142ace980b248a156791651244c8aff762450a4f5
  | 4, 0, 4 => 0x8fbfd78af4eac7d80af3917d5fec056a08c8b16722450a8159fbfda2ac322ca1fec05d1d9678ff6aabcc8b3c7fb455e7959e45980ba3b2b718091429f1678e46e2450ab16602a4c84558fc295e9d322c59d6914297d62cef48a04c8b1652270c8455
  | 4, 0, 5 => 0x9fbfdb2af322bfdd69b4293d679167224504b1f8b2bd3a6457fbad228327ac7dfeaf4f1915fed157a90c8b417fb015a8358b30136853e2bfd5ea94399168eff6caa4c8b16773ad228557fb01589141abad22852f93d5fee448a0898aff68aa8c84f5
  | 4, 0, 6 => 0x8fbfda2bc57abfd80af529e55feef48a0482b3c853015e7958fb0168b242acfdfed8579915fea44e1e49eb3c8b2c5224f58fb4522852fac7d80b24413d678ff68ab0c8b1f7fb4d747659e459809b42abfda6af521915feeb48a1490b207fb455e645
  | 4, 0, 7 => 0x7fb9174a927acb5fed15799163ec0579dcc8b1675ae9228557fb01586425ac59d6e448a1562ceb48a1482b3c7fb655a8359e459b2ad322c5980ba3b1d164ec048a14beb1f7fabd3a7957fbad227927ac7db8d948a155fec0549e49eb1f602bcf25f5
  | 4, 0, 8 => 0x8f3655291322c7e2cc05d28963f16602c55eb1f8eabd3a6458fb01688a42ac59b2a9489915fec0472009eaff68abd52645a03fda6af322c7d80b2489d95fef957a1cc8b1f68abcc85e59e45980af3cacf1fed857991580914097c9eb1b60245064f5
  | 4, 0, 9 => 0x8b30168853e2d122cc048a09678ff602b0f2b1f8eb455e6457fb655a8e322c598091429f963f0b602e8ecb1660238c84e59e459748827acf21cc048a15683156024506aff6cae9526459ab01686427acfdfeaf4e9915fefa68abcc8b3c77a44be4f5
  | 4, 0, 10 => 0x7fb655287322c7dfed95d281636c0569909eaff602a4c84759e459a09142ac29a2af5219167916602d10ab2b8730122855602c922853e2c59808f321315fea44e1908eb16682450a7c57fb455eaa322c0dd6913213d5fef968abcc8b3c8930122855
  | 4, 0, 11 => 0x9e3fdb2ba3b2cf1fed958abd678ff5d2809eaff6caa4c84559fbfda2af322c7d80a24897d679156ca4506aff732e8ec4f59d459809142abfd4a9c3213d62cde48a14f8b3c602c922855a1c59bc9142acf22c894299163ec04497c9eb1f602450a775
  | 4, 0, 12 => 0x8fc295e9c3cacf122882f93d5fee45698c9eb417fb655a6457fb917c9127ad0a2cc048a15678d948a14beb1672245024f58b3455ea4322cfa2cc048a1563ec0579e4bcb3c8b379228557fb011e8327abfdb08e3213d64eff57a70f2aff6cab552645
  | 4, 0, 13 => 0x8b3992276322c7e2caf4e1e563eff68afcb4b426e301228559e46dc8ba27abfd12813213d646c048a14beb3c7fa250a4158db652264262cf1fed3579915fed157a90f2aff75ae8e44f58fc41809142acf1fed94da155fed9489d4c8aff50a44c84f5
  | 4, 0, 14 => 0x42980af521e563ec0579e4eeaff75a450a4d57fb655a6431ac7d80bf3917d679156cab4c8b3c7fb655e7959d301686427ac59b2914099162cc048a14fab3f7fba15e6458fc49809142a801d6914297d26cff6caa4c8aff52274c84f5
  | 5, 0, 0 => 0x91bfd8091429058013c7fac5224f57fbad22723213da3edc602450a4f68fc59808f3213d801268b301228557fb01228e4193da7aff63244c84f60047d80b248a15678ff602450a4d67fb015ea43c915a7f1f7fb455e6469e41db2913213da3f1060244c84f69e3fdb29b3213d9fec048a14f8476
  | 5, 0, 1 => 0x8fbfda2af42991a2cc048a15026469e3fd80ad4193da7916602b4c84f60047e2cde48a15684dc60244c84f6a3c6d80913213da3ec048a14be2269e47dfe893213d9febd5da44c84f69a3fdc8913213da3eff602fcb44569fbfda2c0579919fec0449f0c84f69e3fdc8893213da78ff602450a476
  | 5, 0, 2 => 0x4f1fed9569915feeb48a04c84f67fb9122813213da3eff5d270b44f67fb015ea43c93d9fec0489b4c84f69e455ac913213da8d1660244c84f68fb6d80913213da3f03602450a4167fbe5b2af48991a3eff6cab5226469e46dc8913213d9fec048a08c84c68fc5da0913213da3eff6c3015e646
  | 5, 0, 3 => 0x7fb455ea448991a2cc054a44c84f69a3fd80af3213da7916602450464693bfd80af429918011f7fb455e645a0bfd809141931a831660244c84c69e3fd5e873213da2ca44e244c84f69e47dfed157991a78ff68a38c84f68fc5980ba429c9a79186ca44c84f68fc4980913213d800ff75a450a415
  | 5, 0, 4 => 0x8fbbd80912f93da3ec059244c84f69e431c8913213da7eff68a44c84f6a3bfdc8913193da571f7fb455e6469b3fd80ac3213da78ff60245084f60047dfed357991678ff6caa5226469ac59809142991a3eff602fce441697c5980914293d8011f7fb00c84659245980913213da7eff68abcc8456
  | 5, 0, 5 => 0x9e3fda8913213da3eff57a70c84768fb0164af3213da7eff68abcc84f6a0bfd80914193da3eff722bd0e6468fb01228a4297da3ec0489e4bc4f69847dfed1579919fec0471909e4b68f30152913213da78ff6d2e9224f68fc59fac048a15a791677a450a646003fdb2a948991678ff6cac5224f6
  | 5, 0, 6 => 0x7fb0174a93213da78ff6ca3cc84f695c7dfec05d1d9a3eff7ba18c84f68b3ad809142991a78ff6ca45064c69e459b29132131a79367fa20c84f68fc59ec873213da78ff68abcc84569e47d80914297d9fec048a15024167fae9489c3213da790a6ca44c84f69e3fdc8b94893da3f16602e9104f6
  | 5, 0, 7 => 0x9e3fda6913213da571f602450a5f6004f22ce448a1563ec05d2c9228567fb015a8e3213da78ff77245064f697c3980913213da3f1668abd226469e3fdb291321399fef66cabd486469e3fd44913213da611f89b0122856a3c59808e3213da3eff6cb455e6469e471808f3213d9fec05d290b44f6
  | 5, 0, 8 => 0x9ab0122642f93da78ff6ca45064f68fb0174b22c13da78ff77a24c84f68fc598089429918013c7fae9104f59e47dfeb14893da3ede6e244c84f69e3fda2af3213da3eff68abcf26469e4598091320a1a4d1f8b301228569fc2980913213da3f1668301228568fb0122853917da7cff682450a4f6
  | 5, 0, 9 => 0x8fbfd80bf2c11da2cc048a14f85f68fbfdb2c05d1d9a3eff6cb0162af695c7dfec04da15a78ff77a450a4168fc5a1cc048a15a3eff57a70c84b68fbfd80ba5013da6d1f7fb615e6468fb71809142991a4eff6cb015e6460047dfed1578c55fec652244c84f67fb01589132131a78ff601909e346
  | 5, 0, 10 => 0x9e47dfed9569918011f60214be2259e3fdb29132065a4eff602bcf26469e3fd8a913213da790a602bcc84568fbfdf6d157991a78ff7ea20c84f68fc59bcc048a15a3f16602e9227668fbfd80914290da3eff7b3455e6469e429c8913213d9feef48a04c84f67fa91386427915a40ff63244c84f6
  | 5, 0, 11 => 0x8fc5980af39191a7916602450a5f68fc3980914293d9fec056aa4c84f69e3fd80ba3b13da7f1660244c84f6a23fdb2913193da7eff74244c84f67fb01526427915a78ff722e1224f68fb015e642f9159fec057a94c84569e3fdc88f3213da82ff602b4c84c67fb0122833193da791560245064f6
  | 5, 0, 12 => 0x9e3fdc0913213da3eff62244c84f67fb9122854093da78ff6ca44f24f68b3ad22853213da891b60244c84f68fbfda2ba57991a3eff602e8ec4769e4c22cc048a159fec057a90c84768fbfdc8d15799198091429f0be4f68fbfda0af48a15a3ed9602450a5f68fbfd5e9d321158011f7fb655a645
  | 5, 0, 13 => 0x9e3fdc8b74893da74c059244c84f6933fd80af48a15a3eff69ae95e6469e30122852f93d8011f7fb01224358fb0122793b93da78ff77a44c84868fbfdfad957991a3ec048a20be4f69b3fdc88e3213da3f167b3655e6467fbb9d6914293da78ff60238f24f67fbad809142905a471660244c84f6
  | 5, 0, 14 => 0x7fb0136853e13da3f16602d10a4f68fbfdb2c04da159fec057a94c84f69f459a0913213da3eff6caa5226469e3fdc8914093d801277fb455e6459e3fdc8914193da3f16602c9228568fc1d80af321158011f7fabcc8115a1c5980913213da7cff6ca44c84f68fbf180913213da3f0a602bcf2646
  | 5, 0, 15 => 0x9947d80914297da78ff72245044f67fb0122853e121800ff72245024f59e3fdc89142921a3eff69b015e6468fbfd5e9d3213da3f166026d22856003fda2af521914013c72244be4f57fb65228e32131a78ff489909e2b6a0bfd80ad3213da7916602bcc84567fbad7e913213da612b8b30122856
  | 5, 1, 0 => 0x9e3fd809b4293da3f1668a450a6469e3fdb2ad32131a78ff602bcc84e68fb0122852f8f1a3ef6602450a5f68fb0164914293da3eff602250a4169e3fd80914193d9fec0489d4c84f69e3fdd0913213da4d1960244c84f68fc598c913213da7eff60244f24f695c7dfec0579e5a78ff722e91c4f6
  | 5, 1, 1 => 0x7fbad226427895a78e46e244c84f69e3fd80af3c915a791648a1cc84f67fbbdd6913213da3eff74244b64f68fbfd80953213da78ff72244f24f68fc59bc914293da3f16602bcf26468db01226427931a3eff6ca8d226460047e14d1579914011f7fb00b24f58fbfdc8b04893da8f3c7fb655e646
  | 5, 1, 2 => 0x7fb015ea443991a78ff6cab4c84f69fbfda2af489919fec05d1d8e84f69e3fd80913c93da791660244ec6469b3fd80a93213da2cc05d2450a7c69e47e2ce448a15a691660244c84f68b3918091429f1a4f16602450a6468b30122853e105a3eff68abd3a6469fc29a2913213da7cff6ba44c84f6
  | 5, 1, 3 => 0x7fb0122834093da2cc048a04c84f69e459809142905a3eff68abcc81768fbfda2bf57991a3f16602bd227968fbfdb0af489919feeb5d2450a4f69e47dfeba4413da4eff71244c84f67fbadc8914293da78ff722e9104f6983fd80914093da3eff6cb015e7969fbfda28f3213d9feeb48a149e416
  | 5, 1, 4 => 0x8fbfdc8d95d2bda7916602e8b04f6903fd80af321159fec056990c64f69e45580ad3213da78ff7da1cc84f67fb017c913213da3ec0489b8be4f68fc31c8c048a15a78ff602bcf24f69dc7e2cc048a15a78ff66244c84f69e3fd2264278d9a7916602e9228560047e2cd1579916893c8b30122856
  | 5, 1, 5 => 0x9e3fdac914193da3eff64a44c84f68fc5980b348a15a3ed148990be4f68fbfda2af3216da8eff602b0c84f68fb0122852f915a790a68a44c84f67fb6552913213da79166026cc84f69e3fd80ac32115a3f16602e8e44f69fc59a2913213da50ff602e8b04f67fb91226327931a82ff6ca44c84c6
  | 5, 1, 6 => 0x9f3fd22863213da791b602e8c84f68fb01226c3213da78ff722b4c84f69e459c8913193da3eff602e9444f6a0c55809132131a3f0e602450a6460047dfed1579e54011f8b301747659e3fdb29132135a3ec05a2c8c84f68fbfd80b15793da3eff7223cc84f69e3fdc8ba5793da78ff68abd22646
  | 5, 1, 7 => 0xa3cf1fe883213da3eff722dd224f693b0122642f93da7eff68a44f24f68fc59c8d948a15a79166cabd226468fc1da2913213d8011f6e301228559e3fd60913213da4f1f7fb455e6469e459de913213da3ec05fa450a5f68fc5980af43991a6d1f7fb455e6469e3fdc8913293da3edc6ca44c84f6
  | 5, 1, 8 => 0x8fb015e642f1159feaf52270c8456a0bfdc89132131a7916722450a4f691c0d80913213d801277fb015e79593bfda2c057991a2cc0489d8e864693bfd5e9c32115a3eff72245024f69e3fd80ad3213da78ff602a0c84f69e459a2913213da3eff69ae8b04f69e47dc8912f93da6b16602bcc84f6
  | 5, 1, 9 => 0x81b01227c3213da4f0760244c84f67fb015ea932115a3eff602e8b24f68fc59c8c05a13d8011f8b301368558fb01649142991a8f1f7fb655e646a3bfdb28e3213da78ff60245004f67fb011c6427939a88ff60245024f67fb9152913213da731f7fb455e6467fb4580af52191a3eff722e91c4f6
  | 5, 1, 10 => 0x8fc295e9c32115a3f16602d1228569e3fdc8bf4893d9fed048a14f84f6903fd38913213da78ff58a44c84f67fba980893213d9fed948990c64c69e455b29132131a3ec05a228c84f68fb0122852f895a88ff60245044f68fc598091429e58013c7fabd0e6458fbbd80914297da78ff73a44c84f6
  | 5, 1, 11 => 0x9e3fdb2ba579918011f7fb65466457fb012264278fda3f01602e8b04f69b47d80914297da3ec0489c8be4f68fb0166912f93d9fec0479909e4c6004be2cc048a1563eff57a75226469e3fdaa913213d8011f853015e7958fc29a2c057991a78ff68a44f24f693bfd5e9c3213da3ee4602c9224f6
  | 5, 1, 12 => 0x9e459808f3213da3eff602c15e6469e459c8912f93da79156ca44c84f67fb015ea432125a3f1660289226468fb0164912c13da78ff602b8c84f60047dfed13205d4011f60244be2559e3fd12853213da48ff602bcc84f69e3fd8c913213d9fed157a90c84569e3fda0914293da3f1660224c84f6
  | 5, 1, 13 => 0x9e3fd8e913213da8eff72238c84f69e3fdb2ac489918011f8b3015e7950047dfed85799163f1668b015e6468fbfdd0d157991a3f1657a70c84560047dfec0320f967eff6ca44c84f60047d22852f851678ff77ae9224f6004fdfed1579916891f8b301228569e3fdde912e13da3ee46ca44be4f6
  | 5, 1, 14 => 0x9b459808c3213da3f16602e95e8569e43980913213da78ff6cabd0e6469e459b29142991a3f0960244c84f69e3fdb2ad48991a6d1660238c84f67fb455ea43213d8013c7fa24c84f59e3fd809142929a78ff602bcc84769f3fd80914293d800ff68abcc80859e3fdacad3213da791660244c84e6
  | 5, 1, 15 => 0x95c3980913213da3eff69abd22646004f1fed15799163eff57a70f24568fb91b8c048a15a82ff6b244c84c69e3fdb2af32115a3ec0489e4be4f69e44980913213d9fef9602bcc84569e45922883213da791660245064f69e42980913c93da68ff6cb015e6469e3fd80913c13da7eff6c244c84f6
  | 5, 2, 0 => 0x96bfda2913213da3ec0489dcc84f68fbfd80af32119a791572244c84f6a2c5980913213da791668244c84f68fbfda2af32045a79086ca44c84f68fbfd80ba3993da7916602d0c84f68fc2d80ba48a15a3eff6ab015e646853015ea432115a78ff6fa44c84f68fbfda2c0579e59fec05d1f0e44f6
  | 5, 2, 1 => 0x8fb4522642f13da751660244c84f69e45980913c93da78ff6c244c84f69fbfd80af32115a78ff74244f24f68fbfdb2a048991a78ff602e8e44f69e30164913213da7eff72244c84f68fc1d80913c93da891660244c64f6a1c59bc913213da4f1f7fb015e79691c59809142991a3f0b602e8b04f6
  | 5, 2, 2 => 0x47e1cc048a15679166f244c84f68fb012264278e1a78ff6ca24c84f69e47dfeaf43991a80ff69a44c84f67fb9922763213da7916722450a6468fbfd5e9c3c93da8eff602a4c84f69e401c8913213da78ff602bcc84b67fb655ea948991a3f0460244f24f6a3c6d808e3213d800c048a14be085
  | 5, 2, 3 => 0x9e36522642f93da78ff72a44c84f697c7e2cc048a15a7916722e9224f69e45994913213da791b6ca44c84f69e3fdc8af32115a3eff68abcc85a600459d69142991666ff68244c84f69e3fdb2913b191a2cc057a90c84569f45980913213da78ff5d220c84f60030122853e17d678ff50244c84f6
  | 5, 2, 4 => 0x47e2cc05a2156411660244c84f68fc5980bf39191a3ec057a450a5f68fbfd8caf321158013c602450a5f59fbfd80af3213d9fed948a04c84f6a145980913213da3f16602c5224f68fbfdc8d951991a4ec048990bc4f67fb0122853e93da78ff6ba44c84f69e3fdb29142905a3eff68abcc8316
  | 5, 2, 5 => 0x23f16602e8ec4f68fbfd8c913213da79166d244c84f69e4d9fed9579918011f7fabd3a6458fc59b8c048a15a78ff6ca44c85069e3fdc8a33213d8011f8b341228559e3fdb2ba2c13da611f8730122856
  | 6, 0, 0 => 0x8fc2180af489909eeff6cb015ea448991c01277fb01227927b47dfec057a44c84f793bfda2c0489909ef1f7fb9180ba4413de3eff60244c84f08bc7e00c0489909e0e77fb01227c391909ee009e42180913213da3eff60244c84f06bcf256ff72244c84f78fbfdfac05d1609ef308fc5980914293de7916602451c6427bc7dfec051a44c84f7
  | 6, 0, 1 => 0x9e3fd8091391909ef1f7fbd180913213de3eff66301226427bc7dfec0489909e367003fd80914290410c009e3fdb291278c5800c048990be4f0434f260ff72244c84f79e3fd80b8489909ef1f60244c85e27915e3f16602450a64113cf23eff6ca44c84c7003fd8091320f000c008fc5922641e051a3eff72329226427b8024cff602450a4f6
  | 6, 0, 2 => 0x8fbfda091431909ef3c7fb652264278f1e3eff7db010e6427b8023f0e60244c84f68fbfd809b3213c30f1f7fb01748d3213dc011f8430122641e3001fec0489909e0660047dfec048a1494d1f7fb012264278c1c013c7fa450e6427b0023eff602bcc84767fb012285409909ef1f7fb0580913213de8f1f7fb65226427b8023eff6ca44c84c6
  | 6, 0, 3 => 0x9e3fd8091479909ee008fc2980913c93da3f0a68b01226427bcf1fec05ba44c84f70047d80914299012c007fb017458278218013c7fb90c84f11300268ff60244c84f68fc5980913213c2ef1f7fb01226427859e3f16602fd226427bcf1fefb6ca44c84f78fbfd96c0489909ef3c7fb65226427801c00ff602450a7c20b47dfec057990b4457
  | 6, 0, 4 => 0x9e3fdb291321709ef1f7fb012c913213dc013c8db01226427b0020ec0489909e0868fbfd5e9c489908ae007fb01366427821a78ff6ca44c84f20bcf1fec048a04c84f78fbfd90913213c44f1f7fb0174853913de78ff60245066427b801fed9489909e00697c7e2cc0489909ef1f84301226427889c011f7fb01224f13347dfec0579908a317
  | 6, 0, 5 => 0x9e3fd8091411909ef278fc2980913213dc00ff60245026427b0023e913213c280968fbfdfac0489749eeff77ba980913213dc011f7f93c62220a34da3f0a60244c84f7004f1fec048a1482d417fb01226427931e3eff7230174af27bcf1fed95d244c84f7004f180913217c9ed449e3fdb2913213de3eff68b015e913238024eff489909e146
  | 6, 0, 6 => 0x8fbfd80913213c3af1f8b3bd80913213dc013c7fb01745827b3fdf6f860244c84f78fbfd8091359909ef1f7fb01226a3213de3f166e301226427b8023f1668244c84f69847e1cc0489909ee008fc5980b43213da611f7fb012285253c7dfec048990ae4f78fbfd80af48a1482f1f602bd22642f93dc00008fbfda2af322cf1fec05d238c84f7
  | 6, 0, 7 => 0x8fbfdd0d1489909ef3c7fbbd22853213de451f8b301226427b80278ff6026cc84f60047d80913217c78d3c8fc5580913213de3eff602e95e5827bc7e2cc0489909e2570047dfec05d1c89ec008fb0164913213da3f166cb015e91323cf1fec0489909e4d70047e0e91278c428d3c7fb6522642c13dc013f7fb45226427b47dfec058244c84f7
  | 6, 0, 8 => 0x8fbfd80af4d9909ee007fb01226427815a3eff60244c84f053cf1fec0489e4c84f70049a2cc0489909ed1f8b301228a42991c011f85244c84f0a3506791660244c84f70047e2cc0489e49ec008fbfdb0913213da3f1668b01226427b8022cc048990780868fc5980913b1909ee009e41d80913213d8013c7fb91224f18b47dfefd602450a4f7
  | 6, 0, 9 => 0x8fc59c8c048a149ef1f7fb01228520889e78ff72244c84f1e3cf22cc057a44c84f79e3fd80913213c76f1f60244c85f27889e78ff60244c84f14bc7dfec0489909e3779e3fd80913213c8ef1f7fafd76913213de3eff60244c85527b8023eff602bcc84b6003fda2913213c10d1f83b015e913213dc011f7fb01227b27b0023eff489909e126
  | 6, 0, 10 => 0x8fbfd80ba2c13c2ce008fbfd806427861a3eff602bd226424b801fee4489909e0069a3fdb2c0489909ee009e3fdc8913193da3f1687b01226427bcf23f16602450a6470047dfec05d16078d1f7fb01226427871e4f1f8b301226427bc7e2cc05d2450a4f70047e2cde489909ed1f7fb015e8532115e78ff72244c84f003cf1fed948a1cc84f7
  | 6, 0, 11 => 0x9b47e2cc0579909ee009e3fdb2af489918013c8b30122641e30023eff6ba44c84f69e3fdc8ba489909ee0094bfd80913213da78ff6ca44c84f22b80278ff77a44c84f6a24f1fee4489909ef1f7fb0126913213dc011f7fb015e8732347dfee760244c84f77fbad8091429909ee008fc1d8091320f1a78ff6ca44c84f2638023eff6026cc83c6
  | 6, 0, 12 => 0x9cc7e2cc0489909ee0060244c84f04821a3eff68b01227927bc7e0ec0489909e227003fd804f1888810d277fb0122643013de3eff6026cc84f113c7dfe9c48990b44f7004f1fed1489909ed1f7fb9180bf4893de6d1f7fb41226427bcf23eff602bcc8457000023ec048a14beb1f7fb0162913213de78ff60238c84f22bcfa3eff68244c84f7
  | 6, 0, 13 => 0x4f1fee448a149ecff602bd489132115e791f84301226427bcf9fed060244c84f78fc598091429c8c8f3c8b301226427889e571f8b3012285323c7dfec048990a44f78fbfda2af489909ef1f7fb01227927899e3eff60244c84f17bc7dfec0489909e2e78fbfda2913213c22f1f7fb0122693213de8f1f7fb015e6427bc7dfed560244c84f7
  | 6, 0, 14 => 0x9847dfed7489909ef1f7fb0112853213de3f1660245186427bc7dfec660244c84f79847e2cc048a14c8f3c8b3012264278c5e3f1660244c84f0f3cf1fec0489909e2879347dfec048a149ef1f8b301228e3213de4f1f7fb01227927bc7dfed0602450a4f77fb0122643193c98f3c8ab01226427931e6d1f7fb01227927bc7dfed9602e95e647
  | 6, 0, 15 => 0x9e3fdb2d6489909ef1f7fb0170913213dc010a60244c84f0434f1fec05d2bcc84f79e3fd80913213c96f3c7fb0122713213dc011f7fb01466427b4f1fec0489909e3d70047e04c03213c44c008fbfda291320f1a3eff60244c84f0db80279166ca44c84f60047dfed94899090c0083b01224f18821a7eff60244c84f22bcae3eff602bcc8457
  | 6, 1, 0 => 0x9847dfec0579908af277fb015e913213de571f84301226427b8023eff6ca44c84969e47dfe91439909ef1f7fbbd80912e13de78ff602451a6427bc7dfec05d2bcc84778fbfdeac0489909ef3b8fbfd80af3213dc011f7fb01228523b00278c0489909e0968fc59c8c04897c9ee008fbfd22642784da3f167eb01226427b80278ff6013c62226
  | 6, 1, 1 => 0x8fbfd80913213c54f2e7fb6580913213de78ff60244ca6427bcf1fee4489909e4c78fbfd8ec0489909ef1f7fb0174913b13dc011f8b3010a641130024cff489909e1469e45980913218c9ef1f6024514642f93dc011f7fa44f24f0a3001fe91320f02808698c7dfec0489e49ef1f7fbdda0913213de3eff61301226427bc7dfeef602e9224f7
  | 6, 1, 2 => 0x47e2c642788828c0093bfd8091320f1a3eff602dd226427bc7dfec360244c84f7004f20ec04893c62d3c8fc6d80913213de78ff77b65226427bc81fec057a44c84f78fbfdb2c057a1cc8f16602450a7c3213de3f166cb0122853238023f05602449e3168fbfda2913213c62e008fbfd80893213da3eff602d5226427bcf1fee4489909e457
  | 6, 1, 3 => 0x8fbfdb2c0579908af1f7fbd9b2af3213de3f0a602bd226427bd123eff6ca44c84f7a3cf22cc0489909ef1f8b30122883213de3eff60245026427b802790a60244c84f68fbfd8091419909ef3c983fd80914293de78ff602b1226427b8023eff600f0622269e47dfec048a1482f1f7fb015e723213de791f60244c85f27b801fec03213c44006
  | 6, 1, 4 => 0x47dfeaf4e1908ad3c8fbfd80ba2c13de791660245146427bcc23f1360244c84f78fc5980af489908ae008fbfd906427889a79367fb65226427bc7dfef660244f64f795c7dfec0489d8c8e008fc21806427889a3eff602e91c6427bc7dfec0489e8c84f7004f1fec0479909ed3c8b30122853213de3eff602450a64243cf1fec056a44c84f7
  | 6, 1, 5 => 0x9e3fdc8e1489909ef3c8fbfd809b3213de571f60244c85f27bc7e10d960244c84f70047e2cc048a1462c009e459c8913213da4eff60244c84f18bc7dfec048990a84f78fb0174b2489909ee008fc1d80911e0c59fec052244c85a27bc7dfedf60244c84f79dc7dfec05d1609ef3f8fbfda2913213dc011f7fb4580af3233fd80bf489f0c84f7
  | 6, 1, 6 => 0x4d9fec0461909ec007fb41226427821a3eff63244c84f0bbc7dfec04da450a4f7933fd8091459909ef268fc5980913213dc01367fb011c6427b4ca3f16602450a6470047e14c04899078d1f8b34180913213de78ff602bcc84f22bc7dfec048a14e4417984adfec048a149ef1f7fb015e7932115e791f83b01226427bcae3eff602450a417
  | 6, 1, 7 => 0x4f1fe91441909ec009e3fd80914193da3eff74301227927bc8dfec0489909e2570047dfec05791462d1f7fb017e913211de3eff60244f26427bc7e2cc048a14c83c7a0c7e2cc0489909ef1f80b01226427859c00ff602449e310030023f164893c621469e3fd80913213c2ef3f7fb4580913213de3f167b3012285323cf1fec05fa44c84f7
  | 6, 1, 8 => 0x8fbfdecc0579908af1f8b391809142991e571f83b01226427bcda3eff60245004f795c7dfec04d9909ef1f8b43980913213de3f0072301226427b801fec0489e49e086003fd80913213c08d1f7fb01226427849e3eff60244c84f1dbcf23eff72244c64f7004a1fec0489909ed1f7fb6180913213de3eff68a450a6427bcae3eff602e8b04f7
  | 6, 1, 9 => 0x7fb01227c3213c4af3c95c5980913213de3eff60281226427bcf1fed948a38c84f78fc59bcc0489909ef1f81b01226427895e3eff6cb01126427bc7dfec053a44c84f78fbfdf6c0579908af3c8fbfdde913213de3f0a60244c84f18bc7e2cc05d2450a6477fabd489c489909eeff77b01227c3213de52ff72301226427bcf1feef72244c84f7
  | 6, 1, 10 => 0x8fc21ecc0489909ef1f7fb0122642893dc012a7fb01226427b3fd80af54a44c84f78fc5980913213c66f1f7fb3580913213dc013c7fb41226427b4f23eff68a44c84f70045980642788810c008fbfd808520889a3eff6cb0122763238023eff68abcc84560047d80642f93c44d1f7fb0174883213de3eff602bcf26427bcf23eff6cabd22647
  | 6, 1, 11 => 0x9e4d9fee4489909ee008fbfd80af32125a79308b301226427bbfd8091429f09e4178fbfdaec0489909ef1f7fb65809142905e3eff682bd226427bc7db2c048990be4f78fbfd80ba579908af1f7fb9580913213de3f1672301749127bcf22cc048990be4f78fc5994c0489909ef1f7fb0122673213de3eff723015e6422bc7dfec0579909e297
  | 6, 1, 12 => 0x8fc59e0c0489909ef1f7fbd9b29132125e3f1660244c84f01380278ff60244f24f69fbfda2913213c8af3c7fb0122763213ddfec05d2450a7c27bc7e2cc0489909e0e79e47dfee448a149ef3c7fb01226427895e3f1660244c84f0b3bfdc8c048a14f84f7003fd80913213c0ec00a23fd80913193da4eff602450a6427b8023eff68a44c84f6
  | 6, 1, 13 => 0x47e2cc04899050d1f7fb9180a33213dc01277fb015e6422b0023eff68244c83c695c7dfed1489909ef1f7fb6580ba2c13de791f8b365226427bcf1fec048a149e4170047e0ec03213c44d267fb015e913213dc011f7fb4d226427b47dfec057a44f24f78fbfdc8d94899090f1f7fb0122663213de78ff6b244c84f263cf1fec0489909e217
  | 6, 1, 14 => 0x8fbfd80ba48a148ef3b8fbfd80914293dc00ff602bd486422b47dfed96026cc84f7004f9fec0489909ed1f8b301226e3213de3f16602e9225827b8027916601909e2268fc59b4c0489909ef1f7fb012264278e9e78ff602e9228527b8023eff68abcc84f69b47dfed9602bcc8f3c7fb0122903213de3f16602c9226427bd1278ff602450a4f7
  | 6, 1, 15 => 0x9947dfec048a1482e009e3fdc8ba4893d8011f7fb0122791e300278ff65244c84f68fc298091429909ef1f7fb41226427889c011f8b30122713234c23eff68a44c84f79e3fdc8913213c90e008b301224f18821801277fb01226427b47e2cc04da44c84f78fbfdecc03213c66f1f83b6580913213de571f8d301226427bcc2571660244c84f7
  | 6, 2, 0 => 0x8fb0122642f93c78f1f7fbd9809142905e3ef660244c85f27b80278ff489909e0e69e3fd8092489909ef3c7fb01226427911e3f16602450a6422bc7dfec05d1609e4779e4d9fec0579909ee008fbfd80b14893da3f1660244c84f083cf1fec048990a04f79ac598091451909ee00933fd8091320f1a8eff602451c6427bc7dfee448a1cc84f7
  | 6, 2, 1 => 0x8fbfd80a6489909ee008fbfda264278898012b7fb0122642534f23f0a60244c84f70049dfec0579909ec008fc2980af32115a4cff60244c84f113cf1fed1489909e4570047e2cc0320f044d1f7fb017464278cdc01207fb01226427b47dfec048994c84f795c7dfee3489909ef1f8b2bd38913213de78ff722451c6427bc7dfee460224c84f7
  | 6, 2, 2 => 0x9e3fd8091461909ef419e3fdb2913213de3eff6cb45226427bcda56ff602bcc84f78fbfd8091401909ee009847e2cc048a158013c8b301224f18b47dfec05d1609e3c78fbfd80ac489909ee009ac5980913213da3eff60244f24f18b8023f16602450a5f68fbfdecc05d1609ef3c7fbf5c8913213dc011f7fb01747627b00278ff6d244c84f6
  | 6, 2, 3 => 0x4f1fe913213c20d217fb01226427889c011f7fb00c84f2130023eff6023cc84f67fbe580af489909ef1f7fb015e873213de3eff602b5226427bc7e2cc048990ac4f78fbfd80a8489909ef1f8c36580913213de3f0760244c84f1e3801fe6427888280868fc1decc0489909ef1f8b3017e9142991e3eff7b301366427bd1e3f1660244c84f7
  | 6, 2, 4 => 0x4f1feca3213c44d1f7fb0130913213dc011660244c84f00347dfec0579908a177004f1fec0569909ec0093bfd806427889a3eff602fd5e6422bc7dfed1489e4c84f78fc59e2c0489909ef2b8fc2980913213dc011f602450a5f27b4f22cc0489909e0078fbfdc8d948a149ef3c7fb655e913213de791660244c84f1e3cf23f1672244c84f7
  | 6, 2, 5 => 0x4f1fed94899078d277fb6580913213dc011f7fb45224f18b4c23f0a60244c84f79e47dfe91441909ef3c8b30174913213de791f7fb01228327bd12791660244c84f79e3fdc891441909ef1f7fb0122642993dc011f8b3015e6422b3fd80913b1d0c84f70047e2cc0488f062d1f7fbed809132125c011f601909e2204b4f22cc0489909e417
  | 6, 2, 6 => 0x8fc59dec048a14c8e008fbfd80914193da3eff6cb01629127bcda3eff602bcc84b7983fd8091471909ef1f7fae95e9c3213de3eff7b3655e91323ca9fef660244c84f78fc31c8c0489909ef1f7fb0122642785de3f16602bd146427bcee3f1660244c84f78fbfd80bf489909ef368fbfdb0913213de50ff602e9226427bc7dfec04a244c84f7
  | 6, 2, 7 => 0x93bfd80913c9909ef3c85301226427915e3eff602450a7927bcf1fec054a44c84f70047e0ec0278c444d3c7fb65226427889c00ff4893c621404347dfec0489bcc84f7003fd489c489909ed1f8b301228532095e791b602451c6427bc7dfef668a44c84f7983fd8091461909ef1f7fbd980af32125c011f7fb01368527b47dfeda602e9224f7
  | 6, 2, 8 => 0x8fc5980b3489909ee007fb0152913213da78ff602bd226422bc7dfee46cabd226478fbfd8091341909ee008fc29806427889a3ec048990be4f22bc7dfec05d2bcb44f79e4598091321609ef3c8fbfda0913213de3eff6025d226427bc7dfec0489909e0b79e45a22c0489909ee008fc598091188a1801417fb0122642630023eff602450a486
  | 6, 2, 9 => 0x8fbfda2c0579908af16602bd48913213dc011f7f99078220a34b23f1660244c84f78fc29b2c0489909ef1f7fb4574913213dc01277fb01224f18b47dfec04ca44c84f7a0cf1fee4489909ef1f7fb91a2913213de6d1f8b3012285323c7dfed460244c84f79e3fdb2913213c62f1f8b301226427831c01247fb01226427b47e2cc0489c8c84f7
  | 6, 2, 10 => 0x93bfdecc0489909ef3c7fb65226427841e3eff6cb011e6427bc7dfec0489909e2578fbfdfad9489909ee008fbfd809a320cda78ff722bd226427bc7e2cf66ca44c84f79e47dfec0489e49ef1f7fb01228532129c011f7fb00dc4f0d30023eff60244e23269b47dfec0441909ef3c7fb0122642788dc011f602449e3104b0023eff602bcf2456
  | 6, 2, 11 => 0x49dfed1489909ed1f7fb01226427899e3eff602fd228520bc7dfec0489909e2178fc1d80913213c8ae008fbfd226427845a78ff6ca44c86327bc7e14c0489e4c84f793c7dfec0579908af1f7fbcd80913213de571f7fb41226427b8023eff60244f24f60047e2cc0489d8c8d1f7fb4d74913213de6d1f7fb015e6422b8023f1660244c8256
  | 6, 2, 12 => 0x47e2ce4602450ad448fbfd80914293dc013c7fb9122641e349dfee460244c84f79b47e10c0489909ee008fc592285320518011f8b301228520b4f22cc0489909e4578fc59c8d9489909ef1f7fb195e913213de3eff67301226427bbfdf6c052244c84f79e3fd80914193c98f1f7fb0144913213de791660244c84f2638023edc60244c84f6
  | 6, 2, 13 => 0x8fbfd80bf5d1609ee008fbfd80ba4413da78ff72244c84f0738023eff602bcf24f68fbfda2c0579909ef1f7fabd386427915e3eff60244c84f163cf23eff722e9224f795c7dfec0489e49ef3c8fbfd94913213de3eff7f301226427b8023f0a602449e3168fbfd80af489908ee008fc5980ba48a15a4eff602e9226427bc7dfed360244c84f7
  | 6, 2, 14 => 0x8fbfd8091321409ee008fc5980ba2c13da3f0a7b301226427b8023eff579908a1468fbfd38913213c2ef398fbfd80af32115e78ff72244c84f1138023eff488f062146a3cf1fed9489909ee008fbfd80af32101a3eff5fa71226427bcf1fec0489909e4e7004f1fed94899098d1f7fbbd80893213dc011f7fbd90e6427b3fdecc057a90c84f7
  | 6, 2, 15 => 0x47dfed03213c44d3c7fb0134913213dc011f85345226427b0023f166026cc84f68fc35ecc0489909ef1f7fb0174723213de3eff722451c6427bc7e2cc0489909e03793c7dfec0579909ef1f7fb0174af4293de3eff60249226427bcf1fed948a14c84f79e3fd80913213c60f1f7fb016c913213de611f7fb01227927bcf1fec0489909e337
  | 6, 3, 0 => 0x8fc0580ba489909ef1f7fbf580883213de3eff60244f66427bc7e14c05d244c84f70047dfed157a44c8d1f7fb01228520895e6b1f8b301226427bc7e14e460244c84f77fb0174af521909ef3c8fbfdb4913213de3f1660244f26427b8023f08489909e1468fbfd80bf489689ee00a3bfd808e3213da3eff77b01228520bcf1fec0489909e167
  | 6, 3, 1 => 0x499fec03213c44c0097c5980913213d8011f83301224f18b0023eff601e49e2268fbfd80913213c1ee007fb00c83c11021a88ff602451c6427bc7dfef760244c84f7a3bfd80913218c9ef1f7fb65809132065e3eff62b01226427bc7e2cc05a244c84f78fc5980913213c52f368fbfd8064278cde78ff60244f24f22bc7dfed968244c84f7
  | 6, 3, 2 => 0x8fbfd80913213c72f1f8b301226427801e791f7fb015a6427bc7dfec0489fcc84f79e3fd80913213c32f368fc5180913213dc012785301226427b47dfee060244c84f79e3fd809b489909ef267fb6580913213de3eff6cb01227927bcca3f1660244c84f79b47dfec048a1482f3c7fb01226e3213de6d1f60244c85f27bcf1fec05d244b04f7
  | 6, 3, 3 => 0x8fbfd80af461909ef368fbfd80ba2c13dc0116602450a6404347dfec0489909e1f70047dfec0569909ec008fbfd80a83213d8011f8b345226427b4de3eff6026cc84f70047dfec0489044ad1f7fb015e913212dc01247fb01224f18b48dfec048a14c84f78fbfda0913213c24f1f7fbbd809132121c011f7fb00c8450bb47e2cfb60244c84f7
  | 6, 3, 4 => 0x47dfe914290428d1f7fbd9b2873213dc011f48990be4f0a3002791560244c84f68fbfdc8d9489709ef1f8b3d980af3213de6d1f83b01226427bcf1fec0489909e4078fbfde4c0489909ef368fbfd809b3213de891f8b301226427b80278ff6019078226a3cf1fee4489909ef3c7fb0172913213dc01217fb00c84f1134f256ff6ca44c84f7
  | 6, 3, 5 => 0x9e4da2cc0489909ee007fb01223c18821a79307fb65226427bc7dfec0489909e277004598091429f0c8d1f8b3012264278b5e3eff60244c84f0c38022c913213c280868fbfdecd0489909ef1f7fb91b2ba4893de3f1660244c84f1238023ee460244be4f69e3fdc891429909ef1f7fbf580af3213de3eff60244c84f15bc7e06c048a14c84f7
  | 6, 3, 6 => 0x8fc5980ba579909ee0091bfd80913213da3eff602a5226427b8023eff60190ac1968fbfda2913216c9ef3c7fb01226427929e6d1f7fabd386427b801feeb48a14c84f67fb015ea43213c8af1f7fba180913213ddfec05faf5226427b8023eff60245004f6004fdfec0489909ec007fb015e64228218012b7fb01226425b47dfee4602450a487
  | 6, 3, 7 => 0x8fc598091469909ef398fbfd38913213dc013c8b30122853230023f166013c622267fb0148913213c2ef267fbd980913213dc010860244c84f04347e2d1160244c84f77fb01228e3213c98e008fbfdecd957991a611f7fb01506427bbfd80bf52244c84f79e3fd8091321589ee008fbfd745827851801278b301226427b47dfef660244f24f7
  | 6, 3, 8 => 0x8fbfdc8c0489e49ef3c7fb015a6427931e3eff602fce46427bcda571660244c84f7903fd80913213c2ef1f8b3015e9142991c011f83a44c84f0a35063eff72244c84f7004f1fed93213c44d1f7fb69b2913213dc011f7fa6cc84f0a30023eff68a44f24f60047dfec02c13c2cd1f7fb012264278d5e3eff602450a6423bc7dfec0489909e207
  | 6, 3, 9 => 0x8fc0980913213c44f1f85b0174913213de4f1f7fb45226427b8023eff682450a4f68fc5980913213c02f1f7fbdd809b3213de3ee46e301226427b80256ff60244c84c68fc598091439909ef1f7fb01226427855c013c7fb015e6422b4da3eff68a44c84f78fbfd80ba489e49ee009e3fd80911e0c58013e7fb41226427b51e78ff602bcc84f7
  | 6, 3, 10 => 0x11f7fb19226427b47e2cc048a14be4f7
  | 7, 0, 0 => 0x8fbfdc8c0489909e4880047dfec0489909e33795c7dfec057a44c84f800001fec03213c440860047dfe913213c821478fbfdecc0489909e4989b47dfec048990b04f80047dfecf60244c83c79b47dfec0489909e4b8004f256ff60244c84f7004f23eff60244c83c78fbfd8091429909e2280047dfe913213c781470047e2cc0489909e4579e47dfec057a44c84f89b47dfec05d244c84f8
  | 7, 0, 1 => 0x9e47dfec0489909e318004ae3eff60244c83c78fbfd80913213c441a80047dfec0489909e0279847dfec057a44c84f88fbfdfaf660244c84f8004963eff60244c84f70047dfec0489909e0e70047dfec0489909e167003fdb2c0489909e0870047dfec04d244c84f79e47dfec0489909e228004f260ff60244c84f70047dfee4602e9224f70047dfeca60244c84f70047dfeba489909e147
  | 7, 0, 2 => 0xa0c7dfed960244c84f893c7dfec0489909e45895c7dfec0489909e228004c256ff60244c84f7004c23eff60244c83c78fbfdfac05d244c84f80047dfec0489b8c84f79b47dfec0489909e4580047dfec05d244b04f70000278ff601909e2268fbfdfae460244c84f80047dfeda60244c84f70047dfe91321609e147004f23eff6ca44c84f70047dfec0489e49e4578fbfda2c0489909e458
  | 7, 0, 3 => 0x47dfe913213c8a1470047dfec0489909e4070047dfeca601909e227000023eff60190782260047dfeaf4e244c84f7003fd80913213c78087003fdecc0489909e0879847dfec0489909e2288fbfdb2c057a44c84f895c7dfec0489909e3180047dfec0489909e1079e47dfec048990c64f80047dfec0489909e19700001fec04893c620860047dfec04da44c84f70047dfec0579909e227
  | 7, 0, 4 => 0x4f23eff72244c84f7000023f16602450a6468fbfdb2c0489909e2280047dfec048990ac4f70047dfec057a449e3170051e3eff60244c84f70047dfec0489909e4a79e47dfec048a14c84f80000278ff602449e316003fd80ba489909e087003fdc8c0489909e0870047dfed960244c83c7004da3f1660244c84f7003fd80913213c820878fbfdc8c048a20c84f895c7dfec048990c24f8
  | 7, 0, 5 => 0x23eff602bcc845695c7dfec048a14c84f8000023eff6024478316004f1fec0489909e41700001fec0489909e006000023f16489909e1468fbfdb2c0489909e3180047dfec03213c44197003fd8091321609e0878fbfdf6c057a44c84f88fbfd80af489909e3c88fbfdecc057a44c84f80047dfec0371909e227004f1fec0489909e007004f1fec0489909e3c70047dfec03213c62227
  | 7, 0, 6 => 0x47dfec048990823c7000023f0860244c84f69847dfec048a14c84f80047dfec04893c622270047dfef660244c83c78fbfdb2c0489909e1088fbfd80913213c783388fbfd80ba57a44c84f88fbfdc8c057a44c84f8004ee3eff60244c84f79847dfec0489909e4a88fbfd80af489909e4180047dfecf60244c84f7004f1fec05d244c84f70051278ff60244c84f78fbfd8091429c8c84f8
  | 7, 0, 7 => 0x8fbfdecc0489909e318003fd80af52244c84f78fbfd80ba489909e168004b23eff60244c84f70047dfec0429909e2278fbfdc8c0489909e0e80047dfec0321589e2278fbfd80af48990b04f80047dfec0489909e0c70047dfec0489c8c84f70047dfec05d244c83c7003fd80913213c8a0870047dfee460244c83c78fbfd80913213c78228004f1fec048990b04f78fbfdecc0489909e228
  | 7, 0, 8 => 0x4f1fec0489909e457000023ec048990be4f60047dfee46ca44c84f7004f23eff601909e227004f1fec0489909e4c79b47dfec048990c44f80047dfec048990b03c70047dfec0489c4c83c78fbfdb2c048a14c84f8004da3eff489909e1470047dfec048990783278fbfd80ba489909e2280047dfef66ca44c84f78fbfdc8c0489909e2288fbfd80913213c783188fbfd80913213c82228
  | 7, 0, 9 => 0x8fbfd8091429909e3c8000023f0760244c84f68fbfdecc048a14c84f8000023eff6026cc84f60047dfec0489909e0370047dfec0489908a3c7004ae3eff601909e227a3c7dfef660244c84f89947dfec048a14c84f8000023eff602e8b04f60047dfec048a149e3178fbfd80af489909e4580047dfec03213c441a7000022cc0489909e0868fbfdecc048990ba4f8000023eff602450a416
  | 7, 0, 10 => 0x8fbfd80913213c8a318004ca3eff60244c84f79e47dfec0489909e3c89847dfed960244c84f88fbfd80ba48a14c84f88fbfdc8c048a14c84f80047e2cc057a44c84f70047dfec0489909e2970047dfec0489909e4778fbfd80af489909e178004c23eff601909e227004f23eff602449e3178fbfd80bf57a44c84f800002791660244c84f695c7dfed960244c84f80047dfec0489e4c84f7
  | 7, 0, 11 => 0x47dfef6602bcc84f78fbfdecc0489909e0c8004c23eff602449e31795c7dfec0489909e3c8005123eff60244c84f795c7dfef660244c84f80047e2cc0489909e2279dc7dfec05d244c84f80047dfed9601909e2279e47dfec05d244c84f8000023eff68a44c84f6004ae3eff602449e3179e47dfec0489909e4180047dfefb60244c84f7000023f1660244c83c60047dfec0489909e007
  | 7, 0, 12 => 0x23eff6013c62226000024eff60244c84f60047dfec05d2bcc84f70047dfec0489909e4b70047dfec0489c4c84f795c7dfec05d244c84f895c7dfee460244c84f89b47dfec057a44c84f89847dfec0489909e3c89e47dfec048990b04f89847dfef660244c84f895c7dfec0489909e4180047e2cc0489909e3170047dfec0489909e287004f26cff60244c84f700001fe913213c28086
  | 7, 0, 13 => 0x9e47dfec0489909e4c80047dfeaf489909e1479cc7dfec057a44c84f80047dfec0489909e0170047dfec048a1cc84f795c7dfec048990b04f80047dfec03213c782270047dfef6601909e227004da56ff60244c84f7004da3eff60244c83c70047dfed9602449e3179847dfec05d244c84f89847dfee460244c84f88fbfd8091429909e4580047dfec048a34c84f7000023ec0489909e096
  | 7, 0, 14 => 0x8fbfdb2c0489909e4180047dfec04893c622979847dfec048a34c84f88fbfd80bf48a14c84f80047dfec05d1909e2270047dfec0489909e4c7000023f0a60244c84f60047dfee4601909e227004c23eff602450a4f7004f1fec048a38c84f70047dfec03213c822278fbfdf6d960244c84f89e47dfec0489909e4589b47dfec0489909e2288fbfdb2c0489909e3c8000023f07602449e316
  | 7, 0, 15 => 0x8fbfdb2c048990b04f80047dfec05fa44c84f78fbfd80ba489909e478004f23f1660244c84f70047dfec0579909e4570047dfec0321609e2270047dfe913213c441470047dfec04893c783170047dfef6602449e31795c7dfec0489909e4580047e2cc048a28c84f78fbfdb2c05d244c84f8000023eff48990781468fbfdb2c048990b84f80047e2cc048a14c84f79b47dfec0489909e318
  | 7, 1, 0 => 0x4ae3f1660244c84f78fbfd80ba489909e3c88fbfdecc05d244c84f88fbfdb2c048a1cc84f88fbfdc8c0489909e3c80047dfec04893c622878fbfdecc0489909e4188fbfd8091429909e2580047dfec05d2449e3170047dfee4602449e3178fbfddec048a14c84f88fbfdf6f660244c84f80047dfe913213c621478fbfdecc0489909e3c89847dfec0489909e4580047dfec0489909e177
  | 7, 1, 1 => 0x8fbfdecc048990b04f80047dfec0489d8c84f70048a3eff60244c84f70047dfec0489909e2570047dfed9602bd22647004c23f1660244c84f78fbfd80913213c783288fbfdc8c05d244c84f88fbfdb2c0489909e4580047dfeef60244c84f7a247dfee460244c84f80047e2cc048990be4f7000023eff68244c84f60047dfec03213c8a2279b47dfec048a14c84f8003fd80af489909e087
  | 7, 1, 2 => 0x47dfec04893c8a317000023f16601909e2260049e3eff60244c84f70047dfec05d2450a4f7003fd80913213c440870047dfee4602450a4f7004f1fec057a44c84f70047dfe91429909e1470047dfec048a149e4178fbfd80913c9909e458000024cff60244c84f68fbfd8091321609e3c80050678ff60244c84f7000023eff60244f24f60047dfed160244c84f700001fec04899078086
  | 7, 1, 3 => 0x47dfec0489909e4978fbfd80ba489909e4588fbfd80af489909e2280048a3eff601909e2278fbfdc8c0489909e458004f1fec0489909e2279e47dfec048a38c84f80047dfec0489909e4870047dfed1489909e457004e63eff60244c84f70047dfec057a44c83c78fbfdecc0489909e458004da3eff602bcc84f70000278ff60244c83c6003fd80913213c620870047e2cd960244c84f7
  | 7, 1, 4 => 0x47dfefd60244c84f70047e2cc0489909e3c70047e2cf660244c84f7004963eff60244c83c7004da3eff601909e2278fbfd80af489909e3180047dfec04d244c83c70000278ff6ca44c84f60047dfec048a30c84f7004f1fec0489909e317004ae3eff489909e1478fbfd80af48990b44f8000023f16602449e3160047dfec048990783378fbfdded960244c84f80047dfec048a38c84f7
  | 7, 1, 5 => 0x47dfec048a20c84f78fbfd80913213c62228000023eff3213c44146003fd8091429f0c84f70047e2cc05d244c84f70047dfec048990783170047e2ce460244c84f70047e2cc0489909e4178fbfd80bf5d244c84f8004f1fec048990c64f7003fd8091429909e08795c7dfec048a30c84f89b47dfed960244c84f80049dfec0489909e4570047dfec04899078227004c23eff489909e147
  | 7, 1, 6 => 0x9b47dfee460244c84f89b47dfec0489909e4180049a3eff60244c84f70047dfed060244c84f70000278ff72244c84f69b47dfec0489909e3c89b47dfef660244c84f88fbfd80af48a14c84f88fbfddee460244c84f80047dfec057a44c84570047e2cc048990b04f78fbfd80913213c44198004f1fec048a14c84f7004da3eff602449e3170047e14c0489909e4570051e78ff60244c84f7
  | 7, 1, 7 => 0x47dfec048a14c83c7005063eff60244c84f7000023eff4893c62146
  | 8, 0, 0 => 0x8fbfdc8c0489909ef1f7fb01226427905e3eff60244c84f1e3c7dfef660244c84f70047dfec04893c62d1f7fb6580913213dc011f7fb00c84f1134c23eff60244c84f795c7dfec0489909ef3c8fbfd80913213de3eff602450a6427bc7dfec0489909e3178fbfd80913213c44e008fbfd8091320f1a3eff602bd226427b80278ff60244c84f6
  | 8, 0, 1 => 0x7fb012264278218011f7fa44c84f0a34da3eff60244c84f70047e2cc0489909ed1f7fb01226427915e3eff60244c85827bc7dfec05d244c84f7
  | 9, 0, 0 => 0x23eff60244c84f6
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
  | 0, 0 => 0x1fc0fcf0000003dcf3f00000fffffff00000fffffff00000fc3fff000000ffe30cf00000e3ff03f000001fe0fff
  | 0, 1 => 0x1f07f1fe00ff1f0711fe00cf1f0711c200c00300f03e003f0300f00200300300103e000f00fff001fff000000fffffff
  | 0, 2 => 0xe3f8fe03f030e3181e3e300fe3181e0230001f07f1fe0fff1c0701fc0fcf1f07f1fe0fff1f07f1fe0fff1f07f1c20ff0
  | 0, 3 => 0xe3f8f03c000fe3000e3e000fe0f8ee01f030e0f80e3df00f00e0e03dc03f00e0e001c0300000003c000fe3f8fe3ff03f
  | 0, 4 => 0xffffffc3f0f0ff1f1ffe30cfff1f1fc230c0e3fffe3fffffe3f8ffffffffe3f8fe3ff03fe3f8fe01f000e3f8f001c030
  | 0, 5 => 0xff1f11c000c0ff1f103c000fff000ffe000ffc1f0fc030c0e0180e3c300f1c0701fc00cf1c0701c000c00000003c000f
  | 0, 6 => 0xfcff0fc1ffc0e0f8ee01ff301ce7e1c1cff01c0701c00fc01c0701c00fc000e0e001cf30ff1f1ffe30cfff1f1e003000
  | 0, 7 => 0xfffffe01f0001c0701fc0fcfffffffffffffffffffc3fff0fffffe01f000fffff1c00fc0fffff001cf30ff1f1fc230c0
  | 0, 8 => 0xe3f8fe03f030000000000000000000000000ff1f1fc230c0e3f8fe3ff03f000000000000ffffffffffff
  | 0, 9 => 0x3c000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 10 => 0x1c0701fc00cfe3f8fe3ff03fe3181e3e300f1f0711fe00cf0300f03e003f00000ffe30cf00000e3ff03f000001fe0fff
  | 0, 11 => 0xe00001cf0000e00001c00000e00001c000000000000f00e3181e3e3f0f000000000f00
  | 0, 12 => 0xe0efc3fff000e0ee3fff3f00e0e1ffcfff00e0e001cf3000e0e001c00000e0e0000f0000e0e000000000e0e0000000
  | 0, 13 => 0x1ce7e1c1cff0e3f8fe3fff3fe3f8fe01f000e3000e3e000f00e0e03dcf3fe3f8fe03ff301fe7f1c3cff003e0f03fcf3f
  | 0, 14 => 0x3c0f0f000000000000000000000000000000000f00000000000f00ffffffc3fff0ff1f1fc230c0
  | 0, 15 => 0xe0e0000f0000e0e000000000e0e000000000e0e000000000e0e001cf3000e00001cf0000e0e001cf3000e0e001cf30
  | 1, 0 => 0xe0e03dcf3f00e0e001cf3000e0e001cf3000e0e03dc00f00e0e001c00000e0e001cf30
  | 1, 1 => 0x1c07000000001c07000000001c0700000f001c07000000001c07000000001c0001c00000000000000f00000000000f00
  | 1, 2 => 0x1f07f1c20ff01f0711fe0fcf1f0711c20fc01c070fc3fff01c070ffe3fcf1c0701fe0fff1c0701c00fc01c0700000f00
  | 1, 3 => 0x1c0701c00fc0ffffffc3fff01c0701fc0fcfff1f1fc23fc0
  | 1, 4 => 0x1c07003c0f0f1c0700000f001c07000000001c07000000001c0701c00fc00000003c0f0f000000000000000000000f00
  | 1, 5 => 0x1c0701fc0fcf1c0701c00fc01c0701c00fc01c07003c000f1c07000000001c07000000001c07000000001c0701c00fc0
  | 1, 6 => 0x1ce7e001c0001ce7e001cf301ce7e00000001c0701c00fc01ce0e1c1cf301c0001c0000000e0e001cf3000e00001c000
  | 1, 7 => 0x1ce7e1fdcfff1ce7e001c0001ce7e000000000e0e001cf3000e00001c0001ce7e1c1cff01ce7e1c1cfc01ce7e001cf30
  | 1, 8 => 0xe0f80e3df00fe3f8fe03f030e3f81e3ff00fe3f81e03f000e0f80fc3fff0e0f80ffff0cfe0f80e3ff03fe0f80e01f000
  | 1, 9 => 0xffffffc3fff0fcff0fc1ffc0fcff0fc1f0c0e0f80e3df00fffff1fc3f0c0e3f8fe3ff03fe3f8fe01f030e0f8ee01f030
  | 1, 10 => 0xe0f80e01f000e0f80e01f000e0f800000000e0f80001c000e0f80e01f000e3f8fe03f030e0f80e01f000e0f80e01f000
  | 1, 11 => 0xe0f8e0000000e0f80e01f000e0000e000000e0000e000000e0000e000000e0f80e01ff00e0f80e3df00fe0f80e01f000
  | 1, 12 => 0xe0f80e3dff0fe0f80e01f000e0f80e01ff00e0f8ee01ff30e0f8ee01f000e0f8ee01f000e0f8ee01f000e0f8e0000f00
  | 1, 13 => 0xe0f8ee3dff3fe0f8ee01ff30e0f8ee01f000e0f8ee01f000e0f8ee01f000e0f8e0000000e0000e000000e0f8ee01ff30
  | 1, 14 => 0xfcff0fc1ffc0fcff0fc1ffc0fcff0e01ff00fcff0e01f000fcff0001cf00fcff00000000fcf80fc1f000fc000fc00000
  | 1, 15 => 0xff000ffe0000fcffeffdfffffcffefc1fff0fc000fc00000fcff0ffdffcffcff0e01f000fcff0e01f000fcff00000000
  | 2, 0 => 0xff1f1ffe30cfff070ffe00c0ff000ffe000fff1f1ffe30cfff1f1ffe30c0ff000ffe000fff181ffe300fff071ffe00cf
  | 2, 1 => 0xff0001c00000ff0000000000ff000ffe0000ff000ffe0000ff000ffe0000ff000ffe0000ff0000000000ff000ffe0000
  | 2, 2 => 0xff000ffe0000ff000ffe000fff000ffe0000ff000ffe0000ff000ffe0000ff000e000000ff000e000000ff0001c00000
  | 2, 3 => 0xfffff0000000ff070ffe0000ff000ffe0000ff070ffe0000ff070ffe0000ff070ffe0000ff070ffe0000ff000ffe0000
  | 2, 4 => 0xfffff0000000fffff0000000ffffffc3fff0fffff1c000c0ffffffc230c0fffffe3ff03ffffff001c030fffffe03f030
  | 2, 5 => 0xfffff0000000fffff001c000fffff001c000fffff0000f00fffff03c000ffffff0000000fffff0000000fffff0000000
  | 2, 6 => 0xfffff1c00fc0fffff1c00fc0fffff1c00000fffff0000000fffff0000000fffff03dcf3ffffff001cf30fffff001cf30
  | 2, 7 => 0xfffffe01f000fffffe01f000fffffe03f030fffffe01f000fffff1c1cff0fffff1c00000fffff1fc0fcffffff0000000
  | 2, 8 => 0xffffffc1ffc0ffffffc1f000ffffffc00000fffffe01ff30fffffe01f000fffffe000000fffffe3df00ffffffe01f000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xbdcf7d7000006dfd77700000fdbb6e600000f97f6b500000d83a6a000000b5830c6000006175035000000ce0573
  | 0, 1 => 0x701b06e007b05011068004a0000000000000300b026003902008002002001001020000800564000aa8000000fdff7f7
  | 0, 2 => 0x42808403002021081230100c0000000000000f03f0ee0d7b0d0370ec0d5b0f03d0ea0c6a0b02f0a60c390a02c0820c20
  | 0, 3 => 0x63a8b234501d63a8b637503d62a8a617503561a83635501d63a8b637503d42a0a407403121283234501d63889633102c
  | 0, 4 => 0xd2948d0320a0b11c1b30308c90140900208063fef637fabd63a8b6ff557f63a8b637503d63a8b631500c63a8b4274039
  | 0, 5 => 0xb51d196820cab51d1278104eb5091b78104eb41d0b5830c6b51d1b7830ceb51d1b7830ce9415094820c225091278104e
  | 0, 6 => 0xd8d64d81ae80dad6cd83aea0dad6cd83aea0985649c8afc298564980ae804ac2c4838e20b51d1b7830ceb51d1b30308c
  | 0, 7 => 0xfbfeff31fa8cb97e7bb4fe9ddad6cdcfaff3dad6cd83aea0dad6cd01aa80dad6c980ae80dad6c4838e20da948d8324a0
  | 0, 8 => 0x421204c41534681844b016204010048014204010000000090342904619163a8b637513d002020044111fbfeffb7febd
  | 0, 9 => 0x2529327c515f25293278514e25293234511d25293230500c25293068014a252930244119242902585146202822145115
  | 0, 10 => 0xb53d3b7c71df67a9b67f517f2529327c515f2529327c515f2729b27e517f25293b7c71df2529367f517f252932fe557f
  | 0, 11 => 0x4aa0a48745314a808487052048e24481cf0040e02405c31140e00401c30008626084cf11294a52b09f0c084240808f00
  | 0, 12 => 0x4ae2ed87efb14ae2e697df354ae2e4cfcf734ae2e487cf314ae2e401ca004ae2e0808f004ae2e00449114ae2e0000900
  | 0, 13 => 0xdaf6ed87efb16beaf6b7df3d6beaf631da0c6ba8b6b7553d6beaf6b7df3d4ae2e487cf314ae2e487cf314be2f4a7cf39
  | 0, 14 => 0x4ea1a4cf45732d6b72fcdf5f2d6b7230da0c2d6b702008080c6360cccf530c4340c88f42daf6ed87efb1dab4ad8765b1
  | 0, 15 => 0x6febf0e88f4a6febf4a74d396febf02449196febf02008086eebe6dfdf776ceb46d9df464ee3e4cfcf734ee3e487cf31
  | 1, 0 => 0x94550948a3c290540900a3806febf6ffdf7f6febf6ffdf7f6febf6b7df3d6febf67ddb5f6febf631da0c6febf4efcf7b
  | 1, 1 => 0x9c574948abc29c574900aa809c5740808f009c57404809429c57400009009c0109c805429c5749c8afc298564980af80
  | 1, 2 => 0x9e57c9caafe29d5759e8afca9c5749c8afc29c574dcbafe29c574bd8bfc69c5749ceaff39c5749c8afc29c574980af80
  | 1, 3 => 0xb57d3b78f3ceb47d2b5cf3d7b47d0b58f3c6b07c0b10f2849c7769ccefd3ded7cdcbafe2bd5f5bf8bfce9c5749c8afc2
  | 1, 4 => 0xbd7f72fcdf5fbd7f70a4cf19bd7f7068094abd7f70200808bc7f6bdcffd7bd7f7bfcffdfbd7f7b30fa8cb87e6b94ff95
  | 1, 5 => 0xbd7f7bfcffdfbd7f7bfcffdfbd7f7bf8ffcebd7f7b7cfbdfbd7f7b7cfbdfbd7f7b78fbcebd7f7b30fa8cbd7f79ecefdb
  | 1, 6 => 0xdef7ed01ea80def7e4cfcf73def7e04c4953def7edcfeff3dee3edcfcf73dea1adcf4573def7edcfeff3d4f52d4de3d3
  | 1, 7 => 0xffffffffffffffffff31fa8cfffff0200808feffefdffff7f0fc0f11f284def7edcfeff3def7edc9efc2def7ed87efb1
  | 1, 8 => 0xf1fc3f35f29df2fc8f13f2a4f1fc1f31f28cf0fc0f11f284f0fc0f93f6a4f0fc0f59f2c6f0fc0f17f2b5f0fc0f11f284
  | 1, 9 => 0xfafecf93fea4f8fe4f91fe84f4fd0f59f2c6f5fd1f79f2cef0fc0f11f284f3fcbf37f2bdf3fcbf37f2bdf2fcaf17f2b5
  | 1, 10 => 0xf5fd3f35f39df5fd3f31f28cf5fd3968a3caf5fd3425c319f4fd2f5df3d7f6fd8f5bf3e6f4fd0f59f3c6f0fc2f15f395
  | 1, 11 => 0xfafee2145915fafcaf97f7b5fad6cf97aea0faa8af975535fa808f970520f8fe4f91ff84f5fd3f7df3dff5fd3f79f3ce
  | 1, 12 => 0xfdff7ffdffdffdff7f31fa8cfcff4fd9ffc6fafeef97ffb5fafeef15fb95fafeef11fb84fafeef11fa84fafee980af80
  | 1, 13 => 0xffffffffffffffffffb7ffbdffffffb7ffbdffffff35fb9dffffff31fa8cfffff0200808ffa9bfb7553dfeffefdffff7
  | 1, 14 => 0xfcff6fddffd7fcff4fd9ffc6fcff4f91ff84fcff4f59fbc6fcff4481cf00fcff42585946fcfd0fd9f7c6fca90fd95546
  | 1, 15 => 0xff808fff0420fffffffffffffeffefdffff7fea9afdf5577fdff7ffdffdffdff7f79fbcefdff7f31fa8cfdff70200808
  | 2, 0 => 0xff9d9fff34eeff958fff24e2ff899fff146eff9c9fff34acff948fff24a0ffa8bfff543dff889fff142cff819fff046a
  | 2, 1 => 0xffa9b9e8054affa9b4a74539ffa98fff5566ffa8afff5535ffa1afff4573ff818fff0562ff8184a70520ffa0afff4531
  | 2, 2 => 0xffd48fffa7a0ffa9bfff557fffa9bfff542cffa9bfff056affa9bfff4539ffa9bfb7553dffa9bf31500cffa9bdef457b
  | 2, 3 => 0xfffff0200808fffffffffeacfffd8ffff7e6ffd7cfffafe2ffd7cfffaea0ffd7cfff0d62ffd7cfff0d20ffd58fffa7e2
  | 2, 4 => 0xfffff068094afffff0244919fffffda3aea8fffff96828cafffff9202888fffff637583dfffff4274839fffff4230828
  | 2, 5 => 0xfffff4a74d39fffff425cb19fffff421cb08fffff0a08f08fffff27c595ffffff278594efffff234591dfffff06c495b
  | 2, 6 => 0xfffff9ecefdbfffff9e8afcafffff9e80d4afffff968abcafffff920ab88fffff6ffdf7ffffff4efcf7bfffff4a7cf39
  | 2, 7 => 0xffffff79fbceffffff35fb9dffffff33faacffffff31fa8cfffffdefeffbfffffdef4d7bfffffbfcffdffffffb78fbce
  | 2, 8 => 0xfffffff9ffcefffffff9ffcefffffff95d4effffffb7ffbdffffffb7ffbdffffffb75d3dffffff7dfbdfffffff7dfbdf
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 48 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 48 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 328 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 328 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 328 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 328 then wireAt i else 0
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
  | 2 => 4
  | 3 => 23
  | 4 => 284
  | 5 => 1418
  | 6 => 2290
  | 7 => 800
  | 8 => 23
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0xe99558236c7fdd1764e82928174ad6ad
  | 3, 0 => 0xf36c0a11ef9023f0a3eff836a0a451257e2f353872eed29b706f250f6dc7ec526d1d2afd6a8ffd686585770e625c6936619ca49e602a7dbc5c4150b942d3cafd2f5cd3512e31ccde2d0153b5128d2b4109df8df80729b2880073313b
  | 4, 0 => 0x33824d9932df4cff32deb72332932f4d3292f881325f8517315789632eefdeba2e96b48c2d5a92722d4972ae2c9e6bcd2a9f27e52a155b1429742172295d4153292ee6ae2915c1ac28f359622843a849279cf08c2703a15e26de9c4e259811322585d2b322e782b61f9284c51f3cc98e1f185fe61e59672a1d6bc4081be2e8291b8d14e41b84f5301b006b401a38c0801809fa8017347fc316b20a15161ec38615389a841414e92012de7ba5117d81f20eb928980ce55f7e0cd27c020be980d00bc965db0bb58cc70bb547040aeb6d1b0884b72007a9200606820315065efc68065af8c80644081e059682b20511e3c004e541aa04d3e73a02d8ab3b0034997f
  | 4, 1 => 0x6c0b3f4b69a1c8a46916b0f768851d29676b15b06742f3c1656decab649e55ba62e8fad6618b5c1c61575367613a6f3360c7cba26059def05f79ef835f0f18515e8451b95e61d38f5e055dc15cde9e9f5c18d1285bd1eb0a5b109fa25acbdea55a31fd095985a9c358c5b54a57b44d6e56e6cdf35673afce561f748e551e01905417bbc7511e505250ad92214f8a5b674f1209684db81b1d4d238fa94ce69fba4c264aa549f80ccd49f50c8e478227164659b9694500f44944faff7944cfc8004487fe78441b9781423be28b3ff2fe4e3f36dad63d8ee3723b6edbaf3a9ade083997c9da3969546d385e356337f5ed4435e94bfe354356d9353b9157339b6a11
  | 4, 2 => 0xafb9ec24ae7eec61ae078702ab058977a94b8ccaa821b46aa7f430a0a69f4df9a577016fa46101d9a3d833eda3843c48a2f04149a0a613399efe070b9e89812e9dec33489d96fd259cf2cd9e9be6a5b99bbaab759ba855d29ac0e2249aa5f1d19a03dad798ca228b97a876289795354197716c8396e7a3ef96a13b0f953932ee93dde94093390870929b7ece90e6beee90b77c6d90832d008f3b09118e6b8c0e892fb36784f8457a8286477581ee5f4781b5328a80d8c4438082c160802144027e1b5cd47d6a58827c79d83d7c527493795b584a791072347813e77c75cbbc8774ff303473c07e0471cd0d807142ea80710c72f5707630066f3f85576d971517
  | 4, 3 => 0xe529228ae4b9969ee3ed9461e2b2bdc3e276167be2730441e2028ea1e12944cde118685fdfcf7d83defb8137ddd4aa55dc868bb0dae01010d8e99a80d78ef9a4d78759a8d547da70d4fee998d4f575b4d4d6928ad29b598ad0f4d59dced7fd51ce3f6a4bce094f7acdb12e50cb75e6d0ca8345a6c9215889c91f365fc8b4942bc7e1bdc1c66a3348c5dfe97ec588a1e7c5185f20c4c9db42c2f1e55bc2d8c8e3c1d16d8dc033e01dbf3bf035bd8faa16bd3a426dbd398543bc01822abb7dd253bafa744bba448e79ba443a4eba3614ccb997cd30b9826b6fb8f55527b8b64dc9b78b4756b757a727b6fe9a92b65ace2db5648820b5551181b2c44bbab043637f
  | 4, 4 => 0xfe885360fdd6c4f7fd262794fc860a49fc7f898dfbb585cffba4d97dfb51207ef9ba972af79dc0b8f72166caf5035a6cf2d6f0f5f2277b80f19a8603f01f006aeeeb449bee49f954edacab6eeda89078ed614259ed477d12ebb5e3aee9f4e2a7e9b75850e68d2b18e53e2767e53d861d
  | 5, 0 => 0xbd2fe3a0b6c1ef10b4487ed0b282ef60ae27b2b0a75789c0a62ead209f0365109874f3d0963d6120963668909494e8d093fe48d08627bfd082747ea0819690b07a926b9079efbf7077f91db0745f1fe06f72c6106c2434306b8efe906993bcc0685d424062efed5062cb35d05d352b505b86497059396a2055a0b1105368978051c33660510e815050902f604fdae4a04d5640f04bb046304a0f63a049815c2045412d004262cdb0414a35503cbc6fe03b36b10036d4b3c035b1d2a0303ec3102efe761026210650249790b01d29fcd01a150fc019838030188dce00177b4760161426a013156cd00d0863800c8ca6d00c2176000b7617d00416e5d00094637
  | 5, 1 => 0x173c6c1616af7b0b167a5022165e5599160cfc3915dac5e91571e6df1563d79a15388b8c151183d714fa8df614bde43014abe8511467f41e145dca4513f1225a13ec4d001332e9f61311130412ee29ce12ec372612822361127120111255137c12246f9e121faad311f45ea911e3d18a119dfe10112caf0f1126120510fcb2c910db41d610d9d92a10baa06e108b63c8106792b11056a0981019fa770ffca5890fe9faec0fce77530fa2accd0f5fe0b90f0a5ea80efc073f0ee0af2a0eb6e6710e6c223a0e5f4a880e5127a30e45da7d0e1294ff0df91f740db432850db1b6820d90865d0d1627e00c79a02c0c6f315c0c69bfd00c6805300c4cfab50bd5dce9
  | 5, 2 => 0x23e54df8239d522f23315e9922c6cab422b7579922610ad22238c90c22239d03219e90072188107d217c18ce21700462210b61d920b75a7520839c06203f350c20182f6b20150acd2011dce21f6855df1f63f8281f042da11f009a381ec774bd1ebcb6a31e9621561e61b3dc1e1b6b5c1de643f11de0dc1d1dd9272e1d87a0351d6a44bb1d5b8fa61d405cd51d0a27431c6ad4901bf6a8921bd190dc1bd0c0c21b8129591b3bd7731ae3c27c1ae1c6821a8c1d501a7f19991a4343fe1a150dd21a10f6e519e920e819baa9a5198df5e0193eae6e18ea45ae18ae189c18948389186f177d1860d89a1849b34b18492bf51818f59b17df951917b9de5117ac503d
  | 5, 3 => 0x2f6848b42f4b482e2f0acc7e2ed07be72e2aeb442e1c714d2e0cfe7c2daad6d32d8de92d2d8d097b2d6e8c932ce0e51e2c3ed48f2c3908c72bed559b2b90297d2b170e4b2a60e87e2a496f192a4436ad2a1fc85a2a0d88cb2a0d6cad2a0d224f2a0cc3e029e0a5f929c61d00299c7e4a2984d1c328e7389028b7c648289c633c2899c1c7288cdf0b2884fdf828732d7b27b8940827b671de2798ce9c2745adc026fd7ac726ceb60226bea663265efa53264c4816263aeadb262efa6025c97e8025c09efd25ad634d259a01602590f64e254ec7e0251f1c0e250b3e6a25016ec724c5f1c124aeadd5249bda20246479a924497b2c242c6e2623fae01e23ee01b8
  | 5, 4 => 0x3b4318a23b1dc72f3b0f2c583af34df93a9646163a792f6a3990a72338efb48938e635833864abd738527df93835535138095c8137f8c67a37ee12d537d3505d37ab25933786d55d3780d5ff3766628737503d30374e15da37488051373b41c136c912c236a77ece369a93a3364bea3736040f8b35ee51be35dd329c35a96a463597517035756858356b27a5355e7c643536d8dc34cea3d134c8f0c734b89a4b34a8e39d34a1828e34504a3233fb55fb33a70d7c339e73d33366de1d330e5e7932932f4d3292f881327189f5324b0df8322c432231ec1e97319421a93191ff7f313fc734313295093115c93030b4f5323064f12a30545a88302a9d442f924358
  | 5, 5 => 0x488c1e26484e93cf48388c284800e9fe47baec8d47b4abff4765748947487081473dddcc4712aa5546f99db04641a39d45ec2dc445ce0d5945b7253845ac3f68459ecff7459e6fa044d3714444ae3fb04453eec34446b25443d1a48743ae2c72436649ea4351a0fe434ac03242dae63442c814bf42b779a3429eaeb9428ee3a042590cb54243f1c9422d017a41ef4b0e418184494149f94241112fa2411086cd40d00f7e408d9052405fd836402a13e140187e7a3ff757073f533ef13f47a2c03e8566223e66b9023e341fed3e2c17f13da407ce3da0d95e3d829b1d3d78a92a3d30bc313ceb31ff3c9d75a23bcbcc643bbb858e3baefc873b9029673b6273ae
  | 5, 6 => 0x54e4c8df54adabc0547506745409bc4e53e701f453e5913153de887253b991c6538bceb4531ef71e531a12905318541d51b1ea8851a5bee65172efef514bfb5651314591512693d6510c533a50523ca95041de115031c182501c4cb9500d4be7500492244fd571744f8fc07e4f8b6d384f6d05dc4f5a105b4f52da884f478e4d4ecf9ceb4e8bf4a34e74a48e4e2355ba4dc398ce4d7289584d57de764cd675ff4cc4a49e4c7b77174c59b16a4c1b6ec94c156db64be720004bd06d3e4bce6b924bc4ffc14bbf7b5f4b9eabc74b81a28f4b7937eb4b093b3e4b04cebf4aa4a4954aa242e14a9560054a899ff94a0a039049a0b8ec495f9c87491c350b48a62c9c
  | 5, 7 => 0x6292f1ad6280b9c7627701ec62751e44621cf3e061b98262618a6a106150ac8a61407e9060ba4ab46079fe79605a49425ff943825f7b3e0d5f0cd58b5e6b33b15e4ffd505e4ef02c5e4c367a5e2e85785d9eadec5d6c69ff5d1f8edf5c965e4b5c5c6ad45c4f171b5c12f4f15bc20eaa5bbb72fe5b9c33845b37ce335aa8a6b95a66dc565a56df135a3757b85a183dfc5a0480025a047a5759b17cea59b06ca3595cf8895924fe1f58a01ce05851d2a95843178b580e89bf57a8f5b0576e19235754fe0b571de0785711b93d5705008c56e4f36256d814fc56157fb355ed2b8355c9d84955920674557aca7b5569025e5558078f553d3ac15520b77354e930db
  | 5, 8 => 0x6cd54f906c8b9acc6c3e88df6bf27bb06bed99c26bed0c326bcf90f36bcba0fb6bb965ee6b93033d6b8491136b69b7816b5c09196b3326bd6b2e8ee46af4f7a76ad42daa6a63eb3f6a34dbee6a2e7ddb69f6fc5269c89b4169ac4f77685e611c6854fbaf684d6acd683d8390680ff84a6802d1d467ea6ea867c75f4c6733942566f332cf66b38a4266498e176638497066276d02661599596601d15f65d251fc65c227eb65b58cf265b059d4659800236586cff7657fa7266552cbf36542424765358c4d650379be64f3896864ef92d264dabe7e640a85da63f5bffd63e3b9e363a5037e63951ec7636b22b963669d9562da0cb162b0bf07629eb4c3629da206
  | 5, 9 => 0x75988e0e7589cc8b755ba818751113a074de7ab074c953df74c620ff7484046a74601fa7743f258074202dc473c713b073a20626739112cc7358fdf773221ae0730cb1f8730c7bc772bbb011725681b5722884ce721d09a171d43d3671c4c2dd71b7b36371ae55cb71a7a8897174131a716e4496715e7461715e1b21715373dc714d30aa710b04307106331370de2b65708488277049eaf4701144db6ffeeb946ff014e46fdb1a4d6f9408c46f80bd776f7ca6206f03e74a6efba8276ecdc1e86e861e126e7282286e67b5196e36355e6e35d6ef6e14fc116ddec5a36daa31ab6d89d1a16d82caf46d5e69576d3538996d2abce16d1c819b6ceee4aa6cdb059e
  | 5, 10 => 0x817ebe35815082c5813018cc811127c480910d1d806025218046c835802e8a8b7fe02d2f7fada1b67f81ab497f0741177ee37b707ec99bcd7ec4e8e57eb3723a7e6828e37e60ade77e5407697e4fb0497e373f027dd8cfb57db5f65b7d7727c47ce877917ce4b67e7cd35ea17cb789f97c73677d7c306b6d7bdac8f27bb27f847bb0128c7b9c86517b3fe7747b28b6407b1cdc757b18592e7b0e77b87a82b9b97a7a23a87a2450637a1d4edb79e85dd379e6d45178bfd4587813e77c77f60c7b77ecbdc477b37ad5775f6c04774e3f8e772eb724770625e676c98fd676c2a71e76b57f7c76a98aa67683dc327680fac4767c5d42764e96f6761a168075f1ccea
  | 5, 11 => 0x8bd02ea38bb03b728b8bf21b8b5fbb678b5a4bd68b581b6b8b2e23918b1066cb8ae7aeb08adafe228a7d5da58a2e7f9d8a29528d8a0d63768a036f11899fef99896fa3ea8934bc8a88dea2ab88d14822883687168832b43d8831f2da882be4e18803925f87e7afde87cc6b09876f8b51873a88e986e19bb186d946b0868ce6e686342c0b862a726a85ac709185a2ad5a85730c51851bfb9a84d9962f84a8e3fe84a6d5bc8455b14984129c4083fef7e183f5d3e983e08d3483bcf993839cf592834a31778347c583833bab24831ab88982eed003827b240b824978c682355347821b03d08211e0e081ded60881cd1add81c1d1c681a32288819cce7f819921ab
  | 5, 12 => 0x98d7ba4a98a19efa989a6927984da755983e73d9982f0559981a5c0298008fec97f4e73c97962ac496d52c1d96ced85296a5488695c7f38495315420945ad49194482b9a94272473940048aa93bbbfea9383c8e2937645cf9346f631934245f4933525ab93177c9993104a2b92cc42fa92879af992806526926b9939926b50be9243e7b7921989189204f0b491adbb9491a56c189190d39c912a6acc91039b0590cbcf2f9098a4f79090df99908416828ffa71be8fe9e4ba8f3ac3928ee08a598e83fe1c8e7da85d8e6864fe8dfb55e68dec4b398da754a78d96037e8d65c6a08d257af88d103d6f8d0a05788cba6ff48cb824a98c76bee98c6831808c4e3a0c
  | 5, 13 => 0xa3f69cfea3e1dafaa3d51455a3923af8a38b10ffa3877199a3686bcda362c7e6a31d7223a2f14521a2e26162a23b01a2a22ad791a21abb17a20add15a1ee43b8a1b0b37ea1934eb5a17d6d31a12c6ce0a125e9a0a11e14dda0dec6c1a0a2d218a09cebd3a08134aaa04439cba01d11f79fe503ae9fa381259f94f8489f012d219ebec7979e8084f69e2855369e1b9f809de70cfa9d8fab8c9d6f612f9d5e0e199d55141e9d18ff239d0d020c9cf0e0d69cdab98e9c379cce9c246d989bdb4c879b9cc2be9b3436919b29479a9b05f86d9b05c1a19afd294c9ac0defe9a91dcc29a6647d79a3e92c29a06172e99cbd5c299caffad99571356993bc0d5992e87dc
  | 5, 14 => 0xaf7d917daf4ef1eeaf21e241aeeeb27eaeca37c8aeb42d48aea58b29ae774a7cade663acad73eca4ad64f2d1ad567612ad3fd07cad2a8438ad268b67ad25e2dbacd9c01aac9841fdac851212ac1381b7abe530a5ab96b379ab817109ab70cc4fab2de1d2ab2d8538aab73fb7aa997957aa6b890eaa67f4a6aa0f5a41a9e3e07ca9c0914fa9ba59c2a9a0d992a9944925a9844804a96c3f81a8f43c14a8db08d3a8c2f0c1a89e845aa84f5f0fa8411ac0a7e9c861a7cb1877a7228789a7005ac4a6ce9060a6c2509aa6b636afa698faffa64a0a6ca61f8d2ea5fb88b6a5b2d2f3a590f7bca560dc50a5297267a5112d33a4e838f8a4d53b88a467ebffa42c1dfd
  | 5, 15 => 0xb729db6eb7256835b706f7edb702d21ab6eec924b6e90b25b6c951fcb6accc0db69c193bb66990e1b63eeb70b5f166b2b5e352a6b5dd89e8b5d73681b5d6ae26b5ca66d8b5ac93d1b5406affb5204112b4a1fea2b4837f37b47c9722b479ff72b4665269b454fa62b41e988fb4055b42b3f8a25db3a5b92fb376f82fb36ed58cb36b4394b31f60e1b3183d29b2f9c2dfb2cd9beab2978881b26fe78bb2571dabb24cd3dab247bca4b2479df5b237e818b1ab07d8b1a14c67b19d22c1b186a492b1786fe5b15c2cedb140d322b13563bfb0fe152ab0f2d96bb0e8ce19b0d3c397b0d049deb092cc10b08b963db055039cb02b7637afd87cd4afb6854baf84e516
  | 5, 16 => 0xc343a0f4c3014cc9c2b1c558c29577c9c22740d5c20c7b6fc1d16d8dc1a85a88c194ef38c1803655c13f717fc13c3aa3c0798154c038ad83c0278d75c01e386bc0042012bff33eacbfdb5b4dbfb39434bf8705ebbf599713bf45ef84bf40cb94bee5feedbedd9d2abea336b7be8463e6be73add1be278d1abd1b8d38bcd62099bc45454bbbfc2d04bbb787aabb0dfdd9baddaebfbadd628ebad678ecba8ae829ba68ab79ba64289aba540194ba4a95faba47eeb6ba270602ba14c9e1b98c9672b96d01eab96c5357b950c2ecb9498d19b8e2a583b8aa6eb4b88932b6b827606eb822f99cb80e08f0b7ee51a2b7bb5068b7a15aa5b78d52bcb7820e2cb76976f1
  | 5, 17 => 0xcf910780cf795bbacf3979dacf1f6c09cf041131cedad5b5cebf7783ce82b02fce716302ce34f10bce30afeace03cf96cdfc0853cd73df73cd5b39ddcd4ee61acd045b36ccaca7e8cc912bb9cc66ce56cc50c4b5cc34acf9cbf0b223cb9c1072cb054186cad2f430cad172fbcab81a64ca5d1f3fca44c153ca430f2bca3f3c1dca359b14c9f94a2fc9f5c996c9e0b175c9bd2b95c97b4c03c92a9c24c87ec458c7e6be8ec7e5aae3c7b01ce1c7840abbc759db72c73fff91c7358d41c72f343dc6a48b8ac66b81a4c60b9dedc5a09282c599208bc56315d2c53414e5c50c4648c4fc1c37c4f7a12bc4f6356cc4aa166fc43968eec3be040ac36745a0c35faa12
  | 5, 18 => 0xdb2e7931dae11edcdab86160dab625c4daaef95ada781b2fda38a0cdd9ebdae7d9e9df8fd999119bd957e7abd8fda80dd89725a0d834007bd831564ad7b4d507d7a7adb3d79df1d0d784aa27d77f0dded7119595d706e400d6b60f37d69430a8d6910a27d67d0a21d62e3f4ad6022aadd5bf52dbd553e630d5537ddbd5445470d531990cd517be23d4de3103d4b946cdd484081fd4667f95d443cdc7d4210e0bd418da8dd41025e3d3d0177dd3c75b8dd3b847d9d2dc5717d29e1562d28e4411d284cdf3d277525dd263d178d222c20dd1f5a45dd1d685d4d1941c87d18988e3d16c01bad1529d48d10e0725d0680223d05b35c7d048f176cfc8e793cfc1d305
  | 5, 19 => 0xe63e97d2e5bd5e06e5bc61c4e5a6c51de53c68ede4be79b0e4b4ba03e4aa6d3ae488f426e45d2c07e4446088e4309154e3da91c9e3af474de393565ce38f80f9e35c9ff9e3402171e2fdbb24e2c6974ee260e440e259ae6de1c315b0e17111ebe1686188e1151fb1e10d6663e1046774e0df467ce09e660ce09dd864e0859ac6dff65054dfdae348dfcadccddfc20d2edf92727bdf71fee7df468bc2df415612df3387d8df2f0b7cdf25fa9ade94ae66de1bfd27de160a38dde61cd7ddd4b9eddd757cf8dd445c18dcffa871dce9e450dce8ce41dce5c8f7dcbb3b65dca906badca10becdc956c08dc61085fdc385fccdc2cb996dbd937a4db9115e2db4dcdcf
  | 5, 20 => 0xf179c6e7f1414232f105dbf6f0f8df95f0b3fa0af09fbb0df0550015f04bdcbbf0370367ef7dfa6def7c6c39ef3182d2eef2ddfceed06b16eeb0cd47ee9ef01dee8d12c0ee58bbd2ede32d35ed9421cced6b0e9aed176cc4ecdaea36ecb5cc9cecaad606ec94b0b1ec32c97dec307449ec3015daebe83bd4ebe58dbaebdcd2a5ebdb1404ebd49c57eb9e3af4eb7bd3afeb710f3eeb710de8eb16c6b9eab341b9eaad1051ea9982dcea941b86ea7cf14eea6e68c7e9ad5a5de93dc9e5e9271f10e91dd7f9e914189ce907f834e8f339afe8a11dfbe83a1e8ce7ca0c5be7c739aae7bb4e07e799e180e759c994e732670fe6f02cf9e69a76f7e666fd26e6439765
  | 5, 21 => 0xfd92f7fffd3430c6fd217a84fd1d2ea1fc9f2eedfc9ca9a6fc99fb60fc7f8fc3fc7a83edfc25a77cfc0050f3fbf968fdfb79482bfb762421fb1b20c1fb0d732bfad3231afab6533dfa787248fa75cae1fa6d3f3afa69ca64fa5f8e71fa5a946bfa401789fa0e34d7f9b30f7df99ecc42f99d9cccf96feb04f93e71dbf93d2d50f90b85b3f8cf82a7f89a03eff8687c28f8344973f7f79e35f7d9633ff79ec873f768c96ff73a4590f70cd719f681b7cbf670cfb3f63fb1a7f62f32aef6003f8df5eaf4b4f50a4d50f4fc0a22f4f21d8ef4591915f44e89faf3fb5bf2f3d0477df384bc0ef35eb230f355e703f2e7fe07f2d98d99f2ae6432f24a19dbf195102f
  | 5, 22 => 0xffbe2bfaffbb28f6ffae1933ff0f98f7ff06759dfe6a5cedfe5ae9d2fe46b171fe38934ffe2d9670
  | 6, 0 => 0x84aafc707f77e4607f4a3780787d7a50749214007253e8a07246e590715437d0715311406ff4e7106efb8e106eddaab06ad6f4d06a408710665520c0654018106467f3b0638a75e060f596e060ab98a05e063d205ba977d051cbd1904f7559904d32ad804bca6590479bbe1045bade8044a0e720432137103f2801303f1b95203d3ed880375c6cf035eb4ec0341d11b033a727c02dd1e5f02c6934202adc91f029bda2f0265f82e025cb6660254d8c402470b1b0246bcc00240dc18023c7f130219fdf801f5db9e01e3cad001bed05901ad440301a6e4da0185b851016f07f101652a3201521d0b0146c416013156cd00f5a3d200ba50d80082d9db002df207
  | 6, 1 => 0xf21afa70f1c66040ef737100ece75bd0ecc811e0e7e15130e737a980e259c130e2116680dcd46f30da46fb90d9cbe430d95c7350d92daa50d6e8d170d6e7ee10d6a3eb60d166eba0cedf22c0cd896110cb015bc0c7d9f2b0c710b750c336a080c13a5aa0c04ca010bd70bfb0bd154320bc7415d0b9beb890b8ad6cc0b88cc090b53d07a0b2c8ce60b2a386d0b28f6400b1a7d630ae34fac0acd3ae60ab8b2690aaabd360a8df2b50a7b89000a5ed5a50a53c4d60a2deef80a01f69909c0e32809bded4609bd51ef09b9c4c009785bd1096774ce0966c06b09444f6c093e7356092d20e8091afb8909199978090dfc8408b0816608739b70087080150856ca26
  | 6, 2 => 0x16a5446f16995adb16987722168bdf9b168bc85d1662347716517b8a164f38e01643e413163cc666160ed30d15e9498b15a578b715974ea71561a43a15608d7b1560201414c15aa41499cfe51476b3641461a25713ea83c213e90d2b13e0e2a713d6d81d13967e2f139302bf138cad001317dd2b130a5a8912ea1c2e12c36053129ffcb5126ef8381233466a121f421211c9749711be491311af78a8119b91ab118d0e1d1187183a115d3eaf115b67ca110f8d8e10b7c9a8108ef5b9106ef598104b03f510424357103a9912103887e6102497a91004221f0fec104b0fcb33c20fc4095d0fbbccd70faa77070f8009980f776a020f4eb1a70f47a0390f3d8440
  | 6, 3 => 0x1d55e79b1cf65b471cf34cfd1ca0b1831c96ea491c65d3711c5d3d531c32bad41c25bd721c0c1b4b1c0434fe1bd1fa481baefe391b9d622f1b9386ad1b933b9e1b8548e61b78d4bc1b62a5db1b55df541b45c5b71aa1953a1a90e4691a8ffa5d1a6b63331a4058c31a1acdb31a04d97919cbdc9a197a5c0319749e0d194e418d19468cb7194625971921f28d1905a67f18ef4baf18eed24c18c4770b18c3223f18baf70f18ac994f1892cd85188affa91882b169187dc518186366e3185955ec18545dd618103f8818043d6917f938b617e7c6aa17c2274f17bcd81e17bba65117b77a52177154d6175a929b1729918f17206e351712096e16bcc03716afa028
  | 6, 4 => 0x250aba57244d0567243971d5241d3313241b265d24140a4123fae01e23e8c56e23ade26823aa74da237feffe235c252e2359c6d0233e6264233e51982335ab562325c90b2311f0ac23057c1922d85c9a229eb02f228802542241f9d721d8db47219d905421970f56219634db2190160921730a3e216990eb2145ca5920fbfbd620fb7ea420f291fc20ed435e20e249a720df647f20ad102e20abc76120a84c1420a611532089ff20206a118a2064873a2062e284205b0a2a204b60b62014c64420031f961fee5c461fb72b911fac1ffd1f8f31e11f47d9851f0286b71ee07af31ec0fa371ea7893e1de6beed1ddd2b031db574801d9945271d85cfcc1d826c88
  | 6, 5 => 0x2afe09d52af8e8dd2af68de12ad6e7a92a95810c2a6568252a36732f2a3198e02a021f4829f0b1cd29cba47729c8244f29c478db29af2b64297c99f8296af49a296aed9b295678be29342757292af8b7291d2a9e291385ac29025cbe28e28ebb28e1d56328da4aaa28d3f68428c73e9828bc54b328b13185289a15a22856d04b28375f5e281909f627fd4ed027ca04a42794720b277b82482772c7e9275958f22750b4f62737411c2713cf0026f2b8fd26e3a6f026d16b4626d0c803269ac23a2683dcda2667974f263b7183260ba3022604931525f116f125edcb6425e15e0825b1d6bb25ad634d25a4fef925a31684259a3137255fdd51253d09d2252f3624
  | 6, 6 => 0x31b9d9ef317af60a31752de7314b726931381b073122199e30d5282030ba24d830b973d63067a3353047d9d02fd4322f2fcfbe272fc6445a2fb10f502f8f1ff32f8141142f7a8db12f3c81e32f20329b2f1abea52eefaf272edf397b2ed88f702ed53ac92ec68d272ea96fa42e2eb6002df741622de6358a2dd0b5592dad88fd2da94f942d9f970e2d85f2612d7d41f82d7403a82d7296ec2d618f3b2d3ff5e92d19df392d06d0c22cf8cd042cf085992ce3b7132ce0e51e2cc795ae2c7dc05e2c48a2d92c3593cc2c323fec2c30cd2a2c2fc9bd2c2937292c217ac22be8c6dd2b9c405e2b927ad62b8ab9012b79d3f12b25f1c52b1903882b0a8d592b09ceab
  | 6, 7 => 0x3794e38c3766c850372b33393714ce5e3710072a36fb367836d975ff36d88c8636d7e61c36cb597836c9ea4736c0973836b5383e36778df53672ec70366772b536648703363ae8203610c82c360938793601d28435fe022a35f834e935bf14c335974020354de99c3541768b35239d6d3500593e34d2fbb734c589ee349995fb3499662c3481847a3440ba3e343eb057343a84db3439bb633424fc8c34064f6c33df688433ce134333a70d7c339be8303398d185338e027c33864f1f3380d2fa335d8195335802fd3350f8a7334b480a3346a1af333e1d3d331b439e32fee09032f8b2d132aa33483295aaa83294f0e0325e970c3235900a31f4cbe031f21e33
  | 6, 8 => 0x3e9b9b153e7b57fa3e79bb8a3e402f123e277fff3e22c8533e02f5993dc34cb73dc293cd3dc0b3cd3db4e4813da0d95e3d8a3cae3d2c7c353d2562093d254e653d1e34fb3ceb95653ce437ac3c84ae723c7acf473c3977383c38e0113c37b5643c346cd83c2a8b5c3c0cb8773bf52fb13bd6ad1d3bcf60543ba5ac113ba09a7a3b9e4ff53b9031bd3b5624293b34c0e23b15f9f53b1118053b0cb4883acf9b4b3accd4263a9a85bd3a822ece3a67daad3a4d6a953a03d4b139ff1f0a39b8a2b739b1034539777c37394f1420390153ab38eec90038eb527838e8b0de38afba5738a4a5e23885fcd23808c78237d8b58137a858a737a4666c379db3ff37962c63
  | 6, 9 => 0x476fc0964760868246f1b31146df279b467bb779466dd89a4612fb7945e00ffb45d7d33445a7f598457e7d57457c8acd456daacd454c87af4526b408450ea01a4502434f44ea5ff044c3648d44ae84d944578d0c444fd0374420cf3443f50390435ea17843555fb043022bf442ef746f42bebde742b779a34291ffc9425327d7424d58ad422a91db4214c55a41ec4f6f41b00ac74194f6a3416eec4f412c1b3840cda10840a6c27d40a60e3740936de14088ba654074bfff4059fe8540455b7a3ff4ef3e3feafc213f7f6a493f74e55b3f732d3d3f69bd633f639cfd3f62ae583f54ef623f4645963f45ce053f3143b83f227ddf3f086e6d3ef9b7083ea24167
  | 6, 10 => 0x4f19bfb24f084ed24eec3b944ee3183a4ecc8e064ea4fa1c4ea43e9e4e9d19034e92e7bf4dd542384dc9c7c04dc8be514dc7b19a4dc656d84dbe641b4d8cd6aa4d86bbea4d2f3d364d27d5194d244e3f4cfd734b4ccdf14b4ca87c0d4ca489ca4c6e0f504c6601af4c46545e4c247c7d4c1e35cd4c1326ad4c0d39104b862d814b6e21e64b6d33644b67c11e4b2e44754b226b904b03fc924af8703d4aee73794ae8df9b4ac7afc84ac751594ac64d7b4ac2a1d44a8b09ee4a8a40314a55e6434a4c2f544a3f5f3c4a0125c049e0f04f498effba497253c14939e1cf4905a44648f6c24648ed4cc2488161eb487c4b4347e8622b47d260c24795ee6d477f8762
  | 6, 11 => 0x5530a86c55122fc954fdc76d54fd2ea354f251df54d89be654d7ec3654c66e2d54b5735e54b25c7054a96c095488605d547393db546dad965459014c5427678854198a3e540bbf0d5409bc4e53fde02e53e2c57853cbf68653bfda045377f3e6536a150753514afd534dbcc653466db853447d04532df2e1531108a652e0edce52d2403352a1af07528ce019526782fc524e709e524e5dbf524a17a8522a087851ed228251e93bed51bb2a0f51b7cebd51954e1e5184da3a5160844350ef354250eca9cc50c237f650bcb2a75070134c503999f0500307f2500139404ff9d5294ff0f4044fc71f074fc559f74f9d1e774f57f3d24f55eefe4f54e6cc4f547fd7
  | 6, 12 => 0x5b4dbe2c5b3eec9d5b3bed485b1f7a795b00c4075aecd9575ace577e5acd55a85ac2ecb55aa5f5965a9f5dfd5a8723c85a6d6fbe5a4ac6f55a3ecee15a3757b859e9114a59b3a05959aeef8f59a0c2fc598cb1c55989a08a59766e625967c0c75927b4ea59254669591e47e65916351558f528b758d3ef9058bad099589a1073588d54ab588269ee5875705b584579ff583d5a59582e7878581a3e36580ad4f35808a35357c76c8957c03d28578c8c39578a39a2576751eb573389a957188d6b570aae8c56f5a29e56b227ca56425f31563603f2563580cb5615f03c55f6748055f5a32a55d8ab8a55d88bb755bf057b55b8b591555d1ca2555c889c5548eb3e
  | 6, 13 => 0x63e431ee6394e9c963939f3362fcc0e862cefac662ce7cf162c22e4b6296399e62854855627050f962623a35624a2d736212b35a620486bb61f63a0061f5a73b61cb20f861ca400861abfb7c618722e0613f4bb6613bbe3961381f976113aedb60f7ef9060d0e7fb60a01a8560723ebc606d8265606b4b1960638fc4603132d260205a025fbe37825fa9e2065f871fd25f4ce3e85f411ea25f3648d15f20e9805e5e95475e02d08d5dd193db5dbe740c5da6d4765da20cb25d9db11c5d8bf1475d7d6e2d5d5624535d1c01d85cde0cce5cd8aa345cd794895cbdab195cbb87cc5caa48d35ca1e84d5c9649305c8357335c1f443a5bdee7215bb226b25ba3354b
  | 6, 14 => 0x6c49cc986bff319c6be903d06bd3e8686bb6caf46bb04cef6ba44eea6b91dda16b50e1d96b44bd5a6b4493be6b379a1e6afac8926acc62a96abf8ae76ababa2c6aac51006a3f14a66a08291469d67ca969cd7e5369ac5725693b08246909bb4668fcb6d068ade54568a0901b689f890e68742b92682c83d868113b7767fb119167faa20867cd75db67c75f4c678eb5406786b847673f974f67339425671ea51e66fd841f66c97e4e66be836966b38a4266b0a48a669a4886666aceee6633e2ad6627df6e65a8269665a7b45e65862b1a657b75cf654d602765381a02650a838864f56bf264f09cd464e6ab0264b23f0e64b153c164a0c73f649e55ba642e54a0
  | 6, 15 => 0x7317072173018d4f72ff2f9d72b28339727718da726a4e01725996fa7238707e7221207371fa161671da3dee71d78ca271d3d74b71a6de3f71959758718aa31d7179360f7166cf877128e634710cca2270eea42e70ec4efb70d8df6c70d6da3270921b29705b5d9f7041bbc2701a846e700aec186fc73c866fb7655e6f90c8936f5f82676f51dbed6f4ebd9a6f4c3cf56f43e1be6f271ce46edebf9c6edb7b276ec7a3626e8cbcc66e72942b6e187aa16e0fd6066df71c386dd08b0e6d79ee906d72ad596d483b2f6d377e806d2a833e6d1a240c6d1282446d0c81136d035db96cff25276cfdbf986ceccbe26ce170276cd6ca796c8b24206c79ed6a6c4b6e04
  | 6, 16 => 0x7a0989047a05242f7a01223179ec827e79e5550479dc30da79a555bc797abaaa794d343579480fd078d1319678c917387877b05378299fcd77fd168b77f702aa77d370e877d135d077ae3ab077abf41377a1a53877997203778424c27753784a772c48f476fcecf676f0de3376ef06c676e9909e76d00d2c76cb0fb876a139dd768e81ea767c507d764e5f61763744917626fba57613d46a76109d4975f78e3875c2fead75a7bbab75791c4b756f4a91756ef7e9756b3d6c7556228d75364d1d7502d39f74d57dbf749c3d6b7495e96f744a431774238cce7408724474068ac973fa28f273f739d473ea5b6e73da4b1a73bcfd3f73833cd773655c0c734eaa0d
  | 6, 17 => 0x8035cb8680087aa87fd8d7587fca544a7fadd4737fa7685f7f8776eb7f82bf8b7f4590c97f24c13b7f1b719d7f1a1c937eff2d3a7ed1cb467ebbf6017eadd0e57eacabf87e77018b7e757d657e7152747e63c5ee7e4dc0ce7e4d767e7e22428f7e1a8a567e0c74cf7dfb85ac7de3db497ddacfa87dc594b27db493707db1e1917db173387d97d5b77d7d57bc7d5aa3917d41b0af7d3371107cf270267cea112d7ce4b2627c9e1f737c6afef27c69c65e7c46d9ae7c2d3a7c7bfa0c557bf8b5337bd28ea77bce08927bc3baf47bb2ffa97ba3c0797b8f3da37af9f9577aea77727ad3415f7acbd9467abdf2ab7a9c758b7a8ef3507a5b787a7a2ef0847a0b0ec5
  | 6, 18 => 0x87f2d3ba87e6c54587db3bb487d070c48787efba877779c3877115088756c638874f01c78730fd46872dc00586bb6894867726a18672548286713568865ca3e485f6241e85aae0a7858e52b88562f4b38527bd3a85184ada84dec8e884d45c2184d0ea0984a4c2e6849e475c848e320d847f6162847f16828476fe1e845f90f78436e17f84064fcd83f8825383c7eb8383c0be0983629097836211778355b61483533fb8833df90382fbb52882eae1e882e1f31882e0b6ab82de7117829ec1d68276397281f9585b81b76e8e81b734b781ae3390819a78c68182b79a8123ee8881086da080d51044808528c48070f4f8806fefec8069eaef806266ad803be492
  | 6, 19 => 0x8fb5d5348fa19e1f8f9fd3cb8f74f0a98f6057d08f5dec0f8f4fdf788f1f96978f1e8f928ee20b498ec635f58eb3b3e78e817cf48e207e638e1286898e0cfa578dd9958a8dc5fb878da207fd8d88441d8d869bbd8d6b37518d395ff68d2eb7558cfeab508cde80148c73f3678c5291f68c46c50f8c2444fa8bedb9eb8b7e195e8b74ea068b69996d8b0cdb878aef77aa8ae257588aa657898aa45d458a7994f88a553e488a51c9de8a516cc38a2ec80d8a0d8ef789f074c389e6f40f89b9a4c589b52b508986be5c8979e48b8974814d8962ca5d893fe42c893d416f88f823fd88ede02888e36b1588a82a5488a4fc21882be4e18823b6e4881c0d428803925f
  | 6, 20 => 0x95d27d40959a686b956c3d25956b43489551aacc953154209520bde99515305d94d7782194b8834e94adb8bf94aba5ca94943acc947da14a9469ef4294576e3e9419634b9410817d94062d5193f91dd793f1ef8693e2499393a597699365df5093614fb593602c46934b34329322c346931c4d0793154ea392d9d62c92d5a09492d3b19e92cd311e92c5f29b92beb26492bb0e5892976d6492904ad8924056089235af52921c84c191f1d16091b3cbf191aecc40918b0169917fb21d917adf6f916bb660915bff58914d614e912a6acc90db4d0e90c97f5390c78886906eb64390373399903730749021893c901ae55e8ff17fce8fda83be8fd304808fc42d33
  | 6, 21 => 0x9c3b434d9bd769ee9bca9a899bc7f7b09b7a6f559b6cf8b59b6512559b4d17b59b4650979b42e6359b34b1219a5f17019a47902f9a3776ef9a2202919a0d459599ee402799eaf18f99d6685399cce8d399bed3f999bbf5089997d904998e1fc9997b2b99997374ef996e299c993bc0d5993a7ae3992cedf898f4255998e9771598bf8e8d98a19efa9890016a988a6f26986dd153986d00ac9848610498386cf6980357d697d6cddc97aa9cac9786f008977d7102977488ac97708ba59736bddf97337441972b9c5b97012b8496da342696d6a62496c56ede96a22677969aeb729661aced963297ec961e10dc960bb76c96099aa99605e2ea95e5515995ddc41b
  | 6, 22 => 0xa256c1a0a2487bd3a22e6082a213d2a9a20c5825a1f9f6d6a1f9730da195b11ca181a08ea16ae806a1662bafa1521c33a13237eea1070560a0f04834a0d1767ea099d7c2a0569a1ba03c38c2a02ef21ba01e0a0aa008f5839ff394c19fe503ae9fd1658e9fce48649fa86b219fa7e8e29f9e274c9f8e1e3c9f828b049f726bb59f6676b19f281e6a9f2620f29eedf7fb9ed6de7b9ec9ae489ec315a79ec0d7899ebfb44d9e9ab5fc9e93ebe99e6b13689e5fc6b79e519fea9e3e2dc49e14ab229e0a09409df94a519daae7359d96e1cb9d770c479d678a6e9d58b7ee9d4fe22c9cee99bc9cd8b9f79cbb54e09ca53a2c9c97c5ac9c96775d9c5ca0df9c3d31f6
  | 6, 23 => 0xa9983258a97aa236a9679bafa93be014a92cd75ca8d62ca7a8cb32a4a8a73885a85da819a85b062fa851a7e3a840633ca828f69ba8249059a81dcbbea7eb27f5a7b5ef13a7853e24a77665fba74b09e8a732a1a6a6d889a4a6b636afa6aeac0ca69d5214a66d501ba65ebbd6a65c121ea6551343a63809e4a6373e5da6193286a6032cd2a5c2748aa5b035efa533b563a53255c5a51a34faa4e8963ea4e3c223a4d69db9a4b188daa49fea3ba4557672a4437ae7a4033c3aa3d73c45a3c65a94a3c1ab4ba3b1d158a3975e0da3913837a3814b1aa362c88da34731dba33952fca32a6fffa31c39e8a2efe0c0a2a97873a296a4d8a284b47ea26a9449a265fcc7
  | 6, 24 => 0xaf3465dfaf13a005af1123ebaf0da55baeffd43aaef5af7aaeefd66faee7287daed94acbaeca37c8aebe772faeb38838ae9ccfdfae871500ae61e220ae1bf85dae18ff3dae119917ae11518cadf1a5e6adec3e13adeaf2e8addfe763ad965e55ad70d26ead58a5d0ad25830ead1ad330acc6441eacb5a4bdacb48d9baca9b064aca56a1bac6abd01ac41a9b3ac0c7f6aabdd680fabccd6f4abcb65acabc85ff8abbd86cdab89854eab676f4fab46bc03ab3fc05cab3f45e1ab2d8538ab1da2d4ab12b296aaf5dc2faae79678aad9b799aac9e59baab9f914aaa90603aa8f010faa75a9a3aa6b2cfcaa5f3da5aa5b6f83aa22d3e7aa10736aaa0dd57daa00aaa3
  | 6, 25 => 0xb729f7fab71329c5b702d21ab6f9cc08b6f03782b6ede15eb6dd0eebb6a064f5b666254db64676f4b61e9d8db612d09cb5e82352b5b29b6bb573f5cdb55bb1afb542ec61b5378037b50f2cb0b4fc8e64b4ca072db4bad623b4b7aa29b4acbb32b4a99d57b4a8fae1b4a147fbb47be621b4754922b4669b87b37c045eb37aeefcb343b09ab325de37b31e2f22b2c70f7fb2a45d0bb27cccb0b2794cefb250cd45b1ce22c6b1b92624b192c005b18eaca0b169bc48b151cf00b12d5351b0d5dbb4b0a47233b055f4d1b0433de6b03cc05ab038e43cb0333b6cb0114f0ab00afbf8afd768e6afaab267afa1d792af897aa1af777a6aaf6b3d75af647c31af44ea3d
  | 6, 26 => 0xbec2b53cbec0a575bebfe1aabeb33ceebea88b1cbe9af3a5be907f01be4769d9be1b71a7be1113babde1cfb5bdce499fbd70c0e6bd6e211abd3f82f8bd199d0fbcdd2ef2bca0cb13bc9691cebc95da00bc87e6edbc7e8f37bc591900bc5784f4bc3e1aa1bc19ed6dbc0bf607bbe3d513bbcf1011bbc085e6bba99846bb6820b3bb13142ebaf70c47bace5c64bab9a1bdbaaaab6fbaa65613ba9dff06ba70a6dcba701036ba5b88ccba45dd7fba40b91aba208429ba1aa2e5b9fc935bb9e29b05b9b08731b9552079b93ba479b93206deb8c9f8fbb8c07ea2b889a36bb8771bafb871b7fdb84d5911b8405c07b8367464b7bb5068b7b92ec7b7a1fd24b72f93ff
  | 6, 27 => 0xc59d6c30c5899ec0c5736c6ac53ffe14c5368674c530ad7ec4f7a12bc4f4a2e1c4cd748cc4c69b44c4b9fc07c4acd4d8c4a9c569c4a4bbb4c4949487c46c4205c453a13bc44cc871c41ed601c3e38b32c3d7b039c3d681efc3b34d4ec3aeb668c388629ec3675414c3432490c3347db3c2e8f318c2c56a8ec2afde01c2a091e1c2932210c27d1d85c27af562c24ddc2ec2472df4c23c3efdc22cbc1cc228c216c22701b7c1f12b01c1dbd993c16a70b1c1698805c12474cec10e3d6bc104a00bc0b02379c05d09f4c0557f6cc03e8f3ac0310e0bc0309b29c00da4a7bfe7e809bfb4dd66bfb0cba3bfa55542bf97d6e8bf8705ebbf57dce3bf12e93cbeea5a39
  | 6, 28 => 0xcdd3d7d4cdb3193ecd9b22c9cd8df699cd8b6b68cd853652cd7d9d9fcd28ef85cd1c72e6ccd3cdb7ccca3424cca27ba8cc8d2a32cc6d1337cc5be40acc56fb91cc50c4b5cc452051cc338a53cc26ccdbcc1d4d7bcc1a159bcbfbc436cbe6744acbb3c535cb7814d6cb779786cb430ccacb22d64bcad25745cac158cdcaad7443ca5180ccca3fc6e9ca35eab9ca2ab66fc9fddb4fc9eaa662c9c11cbcc97ec64ec96ab8b0c91a9764c904d60fc8f1bc47c8e779a6c8a46cc0c88ea5f3c86a7b32c809f2e1c7d9cf9cc7bdffc1c7a246c4c7970651c75c2593c7327c7fc70560b5c6d0b208c6bef9f1c6a95673c6a389f1c681aa27c66d8871c6068286c5c8dc0d
  | 6, 29 => 0xd4061f74d3efca1cd3d2caa2d3c4ec44d3c1642ad3b8d6e1d3a84f1fd3a13996d39af946d3980975d383a931d31c5cf5d3152e0bd3049f3dd3024a1dd2f75b26d2e60201d2cd00b1d2aeea40d2849381d26e2c13d26dffcbd26b44f3d266e319d254b839d23c352cd21f33e1d219e748d1ffa714d1efb8f3d1d3f658d1cce0ccd1cb1b0cd1c1fd2dd1c001f7d1b5b459d19a03c6d17bf5cfd13a9d20d1358e44d0f6d7dfd0f624a3d0e64a54d0d40464d0c08da1d0bd03c8d0afe803d08863c9d07c82add027ba97cfaaeb5dcf8f4d70cf7566e4cf1f3ed4cf000eafcef3ff30ced23ed4ceafa34ace928115ce8ab657ce5c094bce44daf6ce08e6b9cdf98342
  | 6, 30 => 0xda802b72da68f783da2fbc16da0e6468d9f2b1e6d9b417f4d998bf50d98bcbcad9840b17d94ad137d947af79d9021d31d8f800a3d8c89669d89de169d885ee0ed87f9952d83f1cb6d818a0f5d7eb51c0d79df1d0d786c099d783df75d7783301d76d9a26d7168563d6f3fc90d6f19143d6d35949d6b4c389d661e951d65ec261d65afff9d6374d0fd630e845d5f6cd78d5d37a8ad5ce88c2d5be46c4d5aad949d5a0d46dd58ce416d5806030d560cb55d558d240d5537ddbd54deaadd540c625d53c4309d52fb620d52b0a13d50adb0ed5092ac7d4fc2d73d4e47617d4dbd29dd4c765fdd49216d9d4894f7ed4890869d468faf0d45ced63d438da3ed43140b7
  | 6, 31 => 0xe29d8d40e2810b3ce277b2dee276167be25b26f3e21be8d9e1dfb350e1ce8bc9e1b1f408e185ebf9e0b51845e0930e9de07b344ee064565ce0626e26e05c847ce04e0661e046d2d6e00f9652e006d7bae0063b84dfe4bfcddfd12c8bdf9155d6df75e0f9df66edf2df5b7ac3df50f4a6dee6275bdec48499debf7146de90f3a7de86f571de4eb049de385f98de312a05de18e6c8ddf2abbaddb9d253dd9de376dd8ed5d6dd60d74cdd39b02edcd2e8c7dcaf7ec7dc989a28dc956c08dc8a5345dc778fdfdc5d3e51dc4db354dc4d3caedc3179d4dc273699dba68411db88fca5db4f33a9db3a90b6dafc3026daf5c757daf2339cdace3c8adaa10b17da8c9f9c
  | 6, 32 => 0xea812aa7ea5d5ff0ea5d24ffea2580a6e9d4d14ee9c5752fe9a7a24ae9901984e977c3fee9681333e964ad1ae8843d7ce8796d32e86eb0d6e863d8b7e8623c33e8372b18e82d725ee81adc62e8047120e8027d18e7eb888ae7bfc3aae79c2edfe79a729ee7978a5be775de2ae73d86abe7379fe0e72bf883e65a052be61291b4e5ff6e7ee5cc13a1e5a218f0e56c6f69e56ae1b2e5420695e5061030e4f3f667e4a6b616e46256b4e4446088e44074f2e435b2ede41e5447e412110de3efe807e3ef42d0e3e18a9be3df41ede3d35b32e3cc7821e39a6ff0e3994e13e35f01f3e35df4cfe31ee655e3136461e2fc4f4ce2f18e2be2e5bc00e2bb0fede2ba0a9b
  | 6, 33 => 0xf2033d79f1ed8e22f1e45433f1a91aa5f1a60e7bf13569a4f1307296f12be4b6f117a0a5f103a542f1018053f0e8b557f0e86fe3f0556ec8f0479b38f03f71bdf03d9387f0224e72f01a8b8befeb934aefe31fbaefa77ca6efa21175ef8c83f2ef7fbe4aef75fb71ef2fe076ef0d263aeebe9aeaeea98865ee8f06c5ee812039ee365bcfee03301aee02495bedd26beeedd0785ced9e1365ed74eae1ed640052ed5daac6ed4c8833ed2ae9e7ed215bcfecee993fecd37faaecb47af8ec8498aeec535654ec3e9026ec338729ec0c1396ebf7dc4febbcb677eb8d81a9eb584eeeeb57e6efeb3c36aaeb32e76eeb1b7e54eb194214eafba6c3eacc9208ea88b923
  | 6, 34 => 0xfad62506fa8a9421fa728806fa5d7adffa3689a5fa0c6cfaf9be88bff9b99d75f9afb2a4f996d7d9f908e400f90675c0f8d5ce41f8c6c002f8b10ac9f8aa5a14f8a43307f89a03eff88dae7ef876ade3f8623b2cf84fd4fbf8266916f7f2a92ef7e73469f7d45d73f7a4dbeff7a45692f74120e2f72b7b72f71746d7f6dbfbf0f6d3c780f696889ef685383bf66a42e8f662787ff61da697f58f108cf58c1c3af5735d60f51dc18bf512f24df4dff160f4a631d0f4658084f3c06a7bf390e940f388db30f3828995f36b8289f2e09321f2dc9b47f2c92a07f2b97b7df2978429f2854adff27d326af26d9b06f265e2cdf254d637f239c184f21a5b36f20d814e
  | 6, 35 => 0xfffffe6bffde5bbbffc6e326ffa13466ff98826cff91be5cff90111bff8b865fff8b32caff51a2beff4cb230ff3d011eff27336bff03a3d4feed7483feea712efed1b51bfec4ed6ffebe0ea5fe4d0768fe0fc523fdfe64ebfdcde09ffd3bb91bfd22ec1ffd066537fcf063cefca60f23fc86bf18fc78f6f8fc4a1fedfc392c47fc152a89fc151d11fc087b7ffbefb591fbc0d01bfba354b9fba10062fb92e0d5fb436e48fb192d73fb17c36ffb152bdafb07d043faf92908faf32e46faea169efad8dc57fad89014
  | 7, 0 => 0x17d07b00175a929b1606144c1561a43a1528ba3c14e6b4ae1415063f136d10ac135211a2131bfefa12b8ab4112b8884a12ae5da3129997eb12798028124e263511ed84b711eb7ccf11d7480611761aa81134c9340fc22fb60f8898390f60b9f30f3badb20edd17080e93ae780e8414b20d61f2fb0d52c9a60cf91d9f0cea20e10cc7aa850cb3009d0c867e660bd753a90b41c7720a71f95609874f3d0935920308d6f0260878675807d82e3c07bd347d07af559e0754ea1506ecbabd064612c705c61dd605ad2f3405a3eb0a059e8b1705869eb103e3645402e9d44b0296f5790291d00a023f103c01a603fb0198251c0188fb4b014e28b60129b75500273479
  | 7, 1 => 0x2a5e00e129e942c4291abe562889888f284db2db2775450f2774c460275958f2272770732705880d26d2458e26aa53c326a4b5bf26488ebe26396ad4262d41fb2609324125bece64258a6ea4255ffecb253d09d2252e5c372509c4b82485a93423ea37752310763b23038dd422d85c9a22543c1c223682592219ec0a21a5f96820df43cc20d196be2081cc61204aaf2d2046aaad203cd04e1f608b651ec21db31ebb13731e3d0e221e08e1531d9143721d29fe0a1c1ffead1bc6e5d41b78d4bc1b70b1901b61a0cd1b52f3321b2d157f1a45ab1d1a4058c31a2bfa9c19e360491979f417196672e11937c600191531f41900f42918e3fb0a186f177d183e8305
  | 7, 2 => 0x3f8b9abe3ee6de3d3dff89d03df1aaf13dc32c533da0d95e3d8620523d21e10c3d0124c93cedcf813c39fd5e3bf3e2703b23954e3afd7b253a861c99396f572d3899ed18387c221637dd7e8037a1ed1c378f31e8375fd1e83732d33a3724f45b36e4026d36ad51603678c0eb363c57f436224d1b361b1af435d89aaa359aee6d358e7c13355e29ce3555b617354bc4fd3518dab13481847a33d93c6b326a06213264f19432291be0315024ba3129ad3f30ccd1eb30bda81a3055c0a6302ca7772fc976f62eedfa852ea0b9112e9e70832d770a592d6df75a2cf085992ca821632c11eb5e2bc53b522b81626d2b698d6c2acd7a982a7c85282a6bdfc02a60bc7d
  | 7, 3 => 0x52943af552942b72528ca242520a3fab51bf3f2b516924ff515c2919514f645451099cc650bcb2a75038abd64f9b055d4f717d1d4f490be64e79bd534e0e9fc94e00c0ea4de27c5e4dd111674d2b306b4d17706a4cfd734b4ca60af44c173de94bc969994bb8974e4b7591cb4b62f61f4afc5e1e4ac0774d4ab696904a3f78dc4a0d197449bfa213499cfa0a49226c8f49148db048fa38cc48f0bd7d48ebd2aa484e6acf47f7f7bb475141bb472e33c146e1bded46b340c74696c818465e79d5461566634609964845f6b58445c07cca457c5ed144d9dfff44cd758b43cee64d43a9f84843555fb0433f660a42b779a341a8390640db2d8b4088ba65405c8f3d
  | 7, 4 => 0x6347643b633af01163353df463275f156292bf226284e04362623a3561f427ee61abfb7c619eba9d6129ea2960f8c4a56001a2b65f5d13a95f492eb65eebace45ec6f1c75ec2fe405ebcebc25e90082e5e1657ce5debf6475dc82fa15d6275f45d3a46645d23bf8f5d1e66bc5c9fbd605c91de815c0095e65bff541c5b2acd595b0171135a73054d5a7078f85a437adf59f223e559e9c31b59d66aa059d395c75992adb059766e62596bf2065923c1c65905159658a5f17758905d13581fb8f65806ebe257c3519856dbe56f568ff7f1567ee6cd56240dff55ab6c46558b875054ed1c7554d7c72354c1de1053b7a8b55342fdb75316929452f2fea452acbe7d
  | 7, 5 => 0x76f0916b76db0b2e76bdf4b976b015da764692e675c5ccea74f2245d749b9886745a681c73a4532b73a1eeb7738e53f273833cd77341d2fd72e03d9b727daf3d72739f54721cd83371be65bd70c4152b706753917005f1236fa6c90d6f6c29a26f3b46226ebe77696e9f1e276e834bca6e38e6f66ddedbb86db8095f6d2657c06ce170276cd622c66bcf90f36b89f08a6b7c11ab6b6909ce6b1be3666a7ff6686a5eea176a510b386a4f220869d0a4b069c6f98169c031bf69b2eaed692e70ee6920920f68ff5c7d68b561d0688d1b55686b713367f1c0d3668c47706659a12a66357542655d937964f3896864e30e6464789948645092fc6449b75d6379a676
  | 7, 6 => 0x8b3e939c8aef68758a8bfac78a18c28889beef4c897643b68968a0cb886bb2a587ec2302877910e2876b3203872610b8870ba4c387080352869b7594868cb424867726a1862851b9850f030e8492c7cd83f048fb83c5bc52838341f483233d8082d3eb99828511a48241b05981b734b781b633a5806266ad80428191803eeee07f97da8d7f1b719d7f1797dc7ecd8d627e22428f7dfd47397dd5c4a57d7d57bc7d356db97d33ff317d303bbe7c439fcf7c0721267bc86ac17b2b17a17ae97d0f7ab2c9087aa157477a85129f7a2bfc5d7a09890479e15a2879dc30da798a90b27952d274791d9b417900675a78f04d34787a872c78493a7f7733bc5376f0de33
  | 7, 7 => 0x9c48de239b71391a9b1dd7b09ab47d5a9ab0be7a99ed5e8799bbfbc99985b807997d45649882e2ec98553ede984899db981b7e92981136b5980357d697a5128c974e731797251c98965f3458965531e6963c456d95f5d7ed956125c6955a089894cad17a94b8834e93f42b8d939a58519396353d9351acbb934043b892ef4533928df768927d83849272b1cc926d751e9262028d925c0be491b98d1291426eab90f70fa9906d26119011f582900c696690061e318fe9ad8f8f7fd14d8f78512d8ebf00228e7679718dbfa66d8da125578d7f04bb8d6fdaea8d5eaaf98d3d413a8cfea6858ce77a638c76bee98c1a6ee88bedc1998bc68b508bbc73f08b8fda43
  | 7, 8 => 0xb559ed2fb3feb3cab315333eb2f03ccbb2572353b242b686b2306866b22e7c90b1e4f845b1b17014b18cc501b12375bdb0f51e5bb07bc511b0480e0db038e43cb01ae1b0b00d02d1afebec7daf01b67aae8d3699ae5c9576ae064aa9adab993dacac34b6ac3ab49dac23afedaabfa2cbaaa935daaa8df529aa2867c5a9cb11c2a9647ee6a909e4c1a8d69abba80d4bfda8098f40a77ce252a661d0dfa6395456a62fa927a6032cd2a5e4c2a9a5cabbeaa4dede88a309310ca2d8fffaa1c6431fa1662bafa141bf77a129dc1ca07b3991a02ef21b9ffd08839f9262399eab30d29e0fe1399de9f1209da1794d9d61744b9d42bc1d9d2d50bb9ce015509ca53a2c
  | 7, 9 => 0xceecb93fceeb1ad8cea2794ccdd2d617cd73df73cd5fbf4fcc0d7bc5cbfcbae9cae6d7d7ca5eb5a5ca35eab9c9d88a90c9a019fdc8df6e8fc7554d2ec7466283c707ac1ec61b5c10c5e58a67c5dca5abc5d3e588c5c226a0c577bfccc5690328c4eae2e7c4ac2c82c483e9fec398766ec37f968dc34f33b5c30bd3fac16463c6c110cb7dc1043454c07ccfeebfa55542bf46884bbf4172fabf01fb40bef5700abef1afedbe4f311bbe2639d5be1fe45dbddd5bacbd2744b8bcf5d0c6bcc8e334bcb2dff7bc18011aba2399e2b9fc935bb9782853b85c2f59b84d21e0b837fe7bb81d78f4b7a3f583b6edc245b69fded2b67d321ab65f3e8fb644e080b59a84dd
  | 7, 10 => 0xe2f02cffe2e453e9e25263cde21fca1de1e7aed7e1ccafbce1c2a466e1b94d76e0d9cf49e0d27efae088d44de044fe41dfdba1afdfd1f158df91a28ddf6d0221df41afa0dec9aaa0dec49712de7f8515dd7ab0a3dd547ea2dd0995b1dcd6712cdc240579da8fa153da86c913da7890dfda52a0c6da0af02ed9ed2281d9eccea3d9e7a089d988b69cd90de9d2d8f62b1fd8653959d6fe6644d69e993fd630e845d62ad27fd5d13c99d58ce416d58853add56748abd50d6b02d4fb6d4fd3fa20bfd3b34341d3a21f4ed38eac86d355d4ffd2da325bd27a66b2d2746762d1b38e6dd1786b89d0e5095fd0ab600ed0a7e5c1d04a50f7d0317033cf9551ebcf6e15b1
  | 7, 11 => 0xf637ead7f50771aef34c8d5af24a784af22186e7f15afe71f14d1f92f13569a4f11d8484f109fd47f103a542f1027f58f0f10dbef05fc8f2f053c1fdefeaeca8efdfd1c7efdef6d4ef4adc1aef0e3eb4eef3064deec76f65eeae7dabeeab662cee6bbfe2ee1e2c58ee185818ee03301aedf5513bede64ad6ed5ae6a4eca193e2ebc28ee5eb7a065aeaf7dac4ea88152aea555bf2ea39f55dea2580a6ea04555ae9d3bc26e9b38944e9ad5a5de8b54ab1e8b03ee3e8a00017e878be20e86f0f45e812cbdfe7a75556e73c37a0e7283c3de7199440e606f433e5d4dd4ce5179d48e48a3599e4625a30e45c7de4e45b71d7e3ed24d8e33582dbe2f7dbbfe2f6cc76
  | 7, 12 => 0xffabe638ff8b32caff5a28feff3df527fefb8721fed37441fe809189fe12eeb4fdf560cffce2758bfcb0a9dbfc3e0176fba354b9fb7259a6fb113ac2fac274d4fabc44b5fab495f5fa6ea56df9b99d75f9acd0faf96feb04f9092d95f8b72109f80ff336f7e68aa8f7c476a1f772bfb1f762f14af734b506f6e94291f646c3bf
  | 8, 0 => 0xf33b5fd0dee29a6add9de376c2afde01bad4da24b6be7634b47be621a6563cc3a1f16def8ab84b5d5fbac6fd5e22a7545967c0c755df5df85059633d4f8c57c242b779a32efbd9642eedfa851e7359ed1729918f1606144c1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x6851c104d5101401e1450d9010415003851426404105400e14704125440500
  | 3, 0 => 0x1844044130200000000913008140067041454404003851c104951014000000000151012026851c104d510140000450d9010414000010d620d51050000000000244c020500000001444048080000000244c02050011c104d5101001196148135480500001142640410500000751190104140000000264c0304c08003751421441400000dd450c51050000037518104404000011c1049510100000714d945041400001d4434c5105000003751401041400
  | 4, 0 => 0x814545520100000000001510120200000001413208080000000354802000000000000424418007510d3148140000000000913008140000000104402020019c204d52010000060580434c54000000036480204c080000000310c520200000001444048080000000244c0205000813545520100000000003144120300000001141048040000000000c010500000001142048040043588314854000000000000300414000000000109106000000000032441400000d94504130000000000000000100027580434c540000000001444048080000000214c5203000000014440480800000d92008130200000000003244140072115314c1400
  | 4, 1 => 0x185204d5201000000018430441301000000014830480800760c930481400000000000000000400000813548030200000000004044080000000520c120200000000004244180000184404413020019c105151010000027580434c14000000045085104c000000000434c520000000450c5104c0000000584044130200000000c521480c00000000010110200000001152008000000118104403000000036480204c08000000045081201000000011420480400000005110120200000610c1104c04000000000000004000000000032441400000813548030200000000812008040043585520c1400001d8434d5105000000008135480300
  | 4, 2 => 0x36514104c0000750c530481400000000014910080400464c53548040000000610c1104c040000000314c12000000010495100c000000000434c52000000016101104c080000000000c91050000000000424418005610d3150140000000000003044040027580314c140000000204d5200c000000000454c82020000060105104c000000000214842010000000000424418000000051408200000dd46041101000007510d3048140000000000812008080000000244c0205000dd6008520500000000002048020000000001142048040000000000411030009d6010d3050000062588434c54000010d6154830500000434d915480400
  | 4, 3 => 0x4244180043499500c54000000000000324414000000000109106000000011410480400000000010110200000001443048040000000434c520000000204d5200c0800000002048020100000204d5200c080027580314c1400000000000030041400000004504120100000000004244180000184404413020010d3148120100000000001548020000000610c1104c040000000000c0105001c4204d52010000000000000c9105000000000042441800435883148540000000610c1104c040043594314814000010d621413150000000000000c11010000000000000010000011901041300000000010d314800000000031441203
  | 4, 4 => 0x14440480800714d94504140000000264c0304c080000081354803000000046416104c00007510d314414000000036514104c0000001093550830100000001483048080000000000000040009d6010d3050000000081354803000000061101104c080000000000c91050000000000304404000001831441300001d4434c5105000000018440441302000000010d304800004708135480400000000000032441400205153548040000000000000000040047548314c14000010d6214131500000000000010910600000204d5200c00000000020480201000000000030041400000000000000200000001444048080027580434c1400
  | 4, 5 => 0x8120080400204d515480400000000000000001000000d9010413000000000000300414003758042481400000000010510480c0000081354803000000010515100c00000005840441302000000010d3148000000000434c520000000000000000080000099300c130200000610c1104c040000000244c02050000036514104c0000000000010910600000104d5100c00004704125440400000000010d3148000000000000c11010000026404104c00000000000109106000000008510480c0000000434c520000188314c12050000000184404413020000000000000014000000000109106000000008510480c0000000154c0202
  | 4, 6 => 0x1c84350931500000435883048140000000204d5200c08000018440441302000000010510480c000009421441300000000010d3148000031481354804000000000000000014004658535480400001c86050d31500000000002048020100000000003244140020515154804000010d52548315000000008135480302000006510d104c000000000000000040000000000324414000018430441301000000004110080400374595010d4000000000000424418003751421441400000dd450c5105000000000041441203000000011510080400375181044040000000264c0304c080000081154803000010d61548305000000000021441203
  | 4, 7 => 0x114204804004358835441400000000004110080800000813548030000000000000000000000000511012020000036514104c000000000000c1101000000000000000400375804248140000000434c5104c000000000434c520000119204d520100000001843044130100000204d5200c080000000000c9105000000000032441400434d9154804000000000000000014000010d3544130000000001444048080000081354803020009d600c530500000435883148540000000001150208000000000250412010000000095300808000008135480300000000000030440400000000000000400000000000000100043541500c5400
  | 4, 8 => 0x802048040000000000000040000036514104c000000000314412030000000115100804000011401041300000000008510480c000010d010c530000000000004244180000000300c12020010d620d510500000000005110120200000620d5104c00007510d314414000010d204d520100000000004044120200000610c1104c040000000000c9105000000010d31480000001844044130200000000003244140043588354414000011c104d5101000000000000109106000dd6008520500000001844044130200000610c1104c04000000000109106
  | 5, 0 => 0x100000000000c11020000016540424c0000000000000000600000000000000080000000000000030000000000000014000000000000006000000000000000800000000000000500000000000000040000000000c9105000000000000000c00000002048020000000464d5200c000000180425013000000000000000010000010d524c5300000000000040440800000000000000400000001141048000000000001011020000000000304400000000000000004000000011420480400000000000000300000000c110480400000000004110000000000d510080800000000010d1000000000000000010000000000000001
  | 5, 1 => 0x1c00000000010110200000610c1104c04000000000109106000000010d314800000000000000002000000005530080800000000010d100000000000000000000000c9304813000000060109204c00000000000000005000000004110080800000001548020200000000812008040000081354803020000046416104c00000000000000004000000014430480400000000000000100000000000000040000000254402010000036540424c0000000002550020100000000411008040000000000401020000036514104c000000000434c12000000000000000010000000000041100000000000000001c000000035480200
  | 5, 2 => 0x400001802144130000000204d5200c000000000000c91050000000000000010000000021484200000000000001840000000995010d3000000000144404808000000001404201000000000032441400000000000000400000000000000040000000000000040000000041100808000000045081201000000000000001000000000010d103000000000020040400000004250820100000000003044040000000000c11010000000000000010000000000000001000000010110480800000d515480300000000000000001000000000000000300000001142048040000184404413020000000000000004000000000000001
  | 5, 3 => 0x8000000000002100000000000000001000000d9058813000000000000324400000000025041201000000005520080800000004540420100000434c5214c0000000000000000200000000000000100000000434c52000000036540414c0000000000208120200000000000000180000000454802000000000055200800000018043501300000000000043440c00000000000000200000000000000180000000000000050000000115104800000010d204803000000043548314c0000000005204120100000000003004140000000000c410200000000411008040000000510c120100000464d5100c000000000000c9105
  | 5, 4 => 0x36514104c00000000052101201000000000030440800000000010d10300000204d5200c0000000000000000600000000000000080000115154803000000000000000010000000045041201000000000000001800000d825441300000000000032440800000000010110200000000003244140000000354802020000046416104c000000000000000040000000000324414000000000000005000000010d1008000000000434c5200000000011410480000000d9450413000000000000434400000000000000001000000010d314800000000000000005000000000043440c0000000000c11010000000085210808000000000109106
  | 5, 5 => 0x1c000000045081201000000000000000400000000000000500000000000000100000180434c130000000000c11048040000000434c520000000000000000100000181434c5300000000000000000400000c53548030000000000000000140000000000c1101000000000042441800000002550020100000000000000100000000000000020000000095300808000005950109300000000009510080800000000008510000000000812008040000000000c510300000000d501880400000c53048130000000000000000100000000000c9105000000000021440c00000002048020100000000003144000000000000c9105
  | 5, 6 => 0x100000000454802010000000081200804000000000000002000000000000001000000000000000400000000d510080400000d94504130000000434c5204c0000000004340620000000000004344000000000510c120100000104d5100c000000000000c910500000000003044040000000000000000000000000000000000000005006200000000000012040400001804144130000000000d54008040000000000000040000000000000018000010d520c13000000000000300408000000015480200000000014830480800001802148130000000000000000180000184404413020000000000000004000000000000002
  | 5, 7 => 0x11420480400000004508120100000204d5200c00000004145440300000000000031440c0000000254c020200000000003044040000000454802010000000000000010000008115480300000000009510080800000000500a20000000000c110480400000000000000300000000001004040000000001051030000061101104c08000000020480202000000000000001800000000000000500000000000000100000000404412020000000055200808000000035480200000000000000001000000000000000400000001142048040000119520c130000000204d5200c000000000000c510000000204d5200c00000000000000004
  | 5, 8 => 0x434c5214c0000000000000000400000000000000100000000520c12020000000000104404000008135480302000000008120080400000000000000300000000001044000000016434c530000000000004244180000000000000040000065085104c00000008135480302000000000000001400001195008530000000204d5200c000000000000000010000000000000010000000000000005000000000010440c00001944344130000000000000000100000000000000040000000000410404000000035480202000000000000001400000000000000200000434c5008c000000000214842010000031515200c00000000030441201
  | 5, 9 => 0x43440c00001193548030000000000000000080000000000801000000000000000008000011810440300000000000031440800000002008120100000204d5200c000000000401012010000000000000010000000045480202000000000000001000001804144130000000000000000080000185520c1300000000010510480000000002048020100000000d5200808000000052005201000006010d304c00000008135480300000004340a314c000000000000000040000000000000008000000000000003000000000030440400000000104120000000434c5104c000000000000000000000000000300414000000000000004
  | 5, 10 => 0x81200808000000045041201000000009510080800000000000000500000000d54008040000000354802000000060109204c000000149520c53000000016540324c000000000000000040000000000000008000000045480201000000000043440c0000000204802020000000000000014000000000008101000000014430480400000d95010930000000000d51008040000000000c910500000000000000100000000000000010000020455200c0000000000010d1030000000000000010000010d25440300000000000000001000000595010d3000000025085104c000000188434c530000000600c5104c00000000000000002
  | 5, 11 => 0x42441800000d95008530000000000411008040000000000c5100000000000000001000000002148420100000000c0304808000000000000007000000000032441400000000000000400000000000000140000000000000070000000085210800000000000000002000000000000000400000000000000400000000001004040000000000000010000000000000014000000052101201000006510d104c00000000000000003000000000000001400000000010d103000000000000001000000003544020200000000001004000000000254c02020000043441100c000000000000000000000000081200804000000000000005
  | 5, 12 => 0xd52008080000000000c910500000000000000040000094214413000000050540314c0000000000000000400000434c1204c0000000001548020200000000000000100000000000000040000036540414c000000119500c530000000000d5018804000010d35441300000000000030440400000000004110300000000c1104804000000051408201000000005440480800000002544020100000620c1204c00000000000080101000000000010440c0000081354803000000000000000010000000010041202000000000000000400000000000000400000000000000080000000154802000000000000304404000000025441200
  | 5, 13 => 0x100000000520c120200000434d5104c0000000000104120000000620c5214c0000000000000000400000000d542080400000002048020100000000d52008040000189434c5300000000008120080800000002504120100000000000000100000000000000010000000000324414000010d31485300000000000000000c0000000434c5200000000000041440c000000000000006000000000031440c000010d354803000000000000000010000000010440202000000011520080000000000000000100000000d520080400000000010d100000000000000001c0000000450412000000000115200808000000040441202
  | 5, 14 => 0xd510080400000d9154803000000000000010400000000000080102000000009540080400000003544120000000000552008040000000000000020000000000000014000000000000005000000000043440c000000000109106000000000043440c00000000000000600000000004344000000000000000040000000000434400000000045041201000000000000000400000000208120100000000c11048040000000404412020000000000000010000010d314413000000000000404408000000010440201000000000000000c00000000000000400000000000000140000000000000010000000144304804000000035440202
  | 5, 15 => 0x140000115314c1300000000000820480400000000000000500000000951008040000180324c1300000000000000001c00000000000000400000000d5020804000018021441300000000000010440c000000000000003000000000820480400000000000000400000000000000180000099500c53000000000085210804000010d35441300000000000021440c0000000000000050000021541210c000000000214412030000000000200404000000000000005000000000000001c0000180314c1300000000001610480000000004044120200000000951008040000000450412010000000000000004000000010440200
  | 5, 16 => 0x5520080800000000000000100000000000000100000000000c1101000000000000000400000002008120200000000552008040000000511012020000000000000014000000020480200000000000000001000000000000000400000000d510080400000000000000100000001142048040000000000000020000000085104800000000000000000000000000000000400000000000000400000000812008040000000314412000000000000000004000008135480300000000000000001800000000010910000000000d5200808000000021484200000000004110080000000003540620100000000004344000000000154c0202
  | 5, 17 => 0x434c5404c0000000000000000600000000000000100000000001011020000000144404808000000052101201000000000000000000000003540620100000204d5200c000000000000000000000061101104c0800000d5154803000000036514104c0000000000010d10300000000002104040000000450812010000000000434400000000045440202000000000043440c0000000300c12020000000095100804000018835441300000000000000001400000000000000000000434c5104c0000000003508120200000000004244180000000000c510200000000003044040000081354803000000000000018400000000025440200
  | 5, 18 => 0x1151008040000000000c9105000000014502080400000000000000400000610c1104c0400000000000000000000000d5420804000000041441203000000000000001c0000000100412010000000000000018000000000000007000000000000001800000000000000600000000000000040000000000000040000000000000010000000000000006000000005440480800000001548020000000000000000100000000000c9105000000011510080400000003508120200000000000000180000000454802010000000040104808000000000000003000000010d3148000000000304412010000000000000014000000000000005
  | 5, 19 => 0x5520080400000d820480300000000005520080800000002048020100000000000000100000000314c1200000000000000001000000000000000500000204d5200c000000000000c510300000000802048080000000000000000000043505314c0000000000000000400000000000000140000180214413000000062141434c000000000000801010000000000314400000018835441300000000000410480000000d9028c53000000000000324414000000010440201000000004110080800000000000e100000000008521080400000000000000400000000001004040000000000c910500000000d51008080000000510c1201
  | 5, 20 => 0x114104804000000000000004000000000000001800000000000000600000204d5200c0000000004544020200000000c510480c00000002148420100000000d5200800000011515480300000000010110480800000002048020100000000411008000000000000c110100000000000000040000000000000040000000000000000000000000000004000000000031440c000000035081202000000000043440c0000000434c5200000000000000001000000000010d1000000000000000010000008135480300000000000030440400000000000000200000001151008040000000000411030000000000000010000000000000004
  | 5, 21 => 0x10000000051101202000000000043440c00000000000000300000000000000100000000010c52000000000144304804000000025440201000000000000000400000000000000100000204d5200c0000000000000000400000000d5018804000000000000006000004340a314c00000000025440200000000010110480800000000000000400000000003044040000000254402010000000000000018000014842501300000000000000001c0000000000c910500000000d52008040000000104402010000061081200c0000000000000000000000001443048040000188354413000000000000000010000018843509300
  | 5, 22 => 0xd520080800000004544020100000000003004140000000214842010000065085104c0000000004548020200000001483048080000000000c1101000000000000000c000000000000004000000000000001000000000000000100000000c11048040000000000000040000000000000014000000025440201000000009510080800000000000000100000000000204040000081454803000000046540214c000000000000c0102000000008120080400000002048020100000000004044080000000204802020000043548314c0000000000000000400000000411008080000000521012010000016540434c0000000000010d103
  | 5, 23 => 0x1000000000000000400000001481048040000000000c910500000000000000100000000000c910500000000003244140000081354803000000016540434c000000000000000060000000114104800000010d3540a300000000000000001400000000004110300000000d501880400000000000000400000000951008040000000454802000000000080204808000000000000004000000000000001400000000010910300000000482148040000000000000020000000115010800000000000000005000000000010440c000000000000004000000000000001c0000000000000040000000000000018000000000109106
  | 5, 24 => 0x4840000001853548030000000001444048080000000000c9105000000000043440000000000000000700000650c9304c000000000000000000000000000000010000018032481300000000000040440800000000000000000000620c5214c000000081354803000000000000000014000000045406202000000009410480400000000000000100000001484048040000000000c910500000000000000100000000204802010000021541210c000000119500c930000000000000000100000000000c11010000000115100808000010d3544030000000000000000180000000000000020000016416204c000000000434c1200
  | 5, 25 => 0x434c5008c000000000000000000000000000200400000000000000000000000014840480400000d9500853000000000000000008000000000080100000000000000001000000000010910300000000c1104804000000000000005000000000043440c0000000000000010000000000000004000010d15480300000000010110480800000003544020200000204d5200c0800000000000000500000000d520080400000000000000400000000004044080000099501053000000000000000010000000000101102000000000000001000000004344120000000000812008000000000204802000000000000000014000000000000004
  | 5, 26 => 0x1000000000000000400000000000000100000000000c9105000000690d314c00000000000109106000000000000001000000002148420100000001484048040000000000000060000046081200c0000000000000000700000464d5100c000000000000000060000000080204804000000020480201000000000032441400000002148420200000000000000180000081354803000000000000000004000000025500201000000000000001c0000000000000060000051544434c0000000000000000400000000002004080000000000c01050000020515200c00000001a434c5300000000000000000c000000045041200
  | 5, 27 => 0x1444048080000000000000030000000115100804000000035480200000000010d3048000000000000000040000061548304c000000000000c11010000036514104c00000000015480201000000000000001800000005110120200000000000000140000000000c910500000204d5200c0800000000000000500000000000000000000000354802020000000000434400000010d31485300000000000000001000000000000000400000434d5028c000000185434c5300000000000031440c00000001510120200000000003244140000000104402020000065109404c000000000000811010000000115018808000000025440202
  | 5, 28 => 0x20515200c0000001843044130100000000000000080000000450412010000000144304804000000000109103000000000000001400000002148420200000000000000000000000434c5200000000000000001c00001190588130000000000000000040000000000401010000000000000004000000035440201000000005540080400000000000000500000000003044040000000511012020000000000000000000000000080100000000010d31480000000000208120000000000000000040000184404413020000035144204c0000000001548020200000000000000100000000000811000000000041100808000004125440300
  | 5, 29 => 0x100000000000c9105000000010d0108000000000000000010000000000000004000000000000004000000000010440000000000010910600000000000000100000059500c93000000000000000010000000000000004000000000000001000000000000000200000434d5210c00000000021484202000000000000001c0000000254402010000000000000014000008115480300000000000000001000000813548030000000001141048040000000454802010000060105404c00000000025006200000000000000000400000000010110200000000000000080000000350812020000000000000014000000000000006
  | 5, 30 => 0x14000000000000004000000008120080400000002544020100000450c5104c000000000454802010000000000000010000000000000005000000011520080000000003548020200000000000000100000194434c530000000000000000100000000204802000000046041100c00000000045406202000000000000001400000000010d100000000000000001c000000040101201000000000020440400000002544020200000000000000100000000104402010000000000000010000000010440200000000000000001000000000010d100000000000000001000000000000000400000000d5200804000000015101202
  | 5, 31 => 0x40000000000c91050000000000000014000000035440200000000000031441400000003044120100000204d5200c080000000000401020000000000000014000000041504201000000011502080800000000000000300000000003244140000000000c1102000000000000001000000002504120100000000802048040000000000000070000046494018c0000000000000a10000000000002144040000000001011020000000000000004000000045081201000000000000000400000004508120100000000000000100000188454c13000000045085104c0000000000000000600000000000000040000000434c5200
  | 5, 32 => 0x21440c0000184434c530000000000411008000000180434c530000000000d420480000000000000000400000000d5200804000000000000005000000014810480400000000000000200000000000000140000185520c130000000000411008080000000000000040000026540434c000000000154802010000000000000010000010d520c13000000000085210800000000000000006000000000021440c00000d9154803000000020455200c00000000000000003000000000000000000000002048020100000610c1104c04000000000000000000000000043440c00000000000000000000000d5420804000000035081202
  | 5, 33 => 0x80000000155002010000026540414c0000000595010d3000000000144204800000000045440201000000000000001400000004548020100000460d5104c0000000003548020200000001443048040000000244c0205000000000032441400000000010d1030000046540314c0000000002544020200000000d5010808000010d504c5300000000010d31480000000004548020200000001151008000000000000000040000020455200c000000000434c1200000000000000000800000002048020100000000552008000000000000000050000060105104c0000000000010110200000434c5200c00000000000000003
  | 5, 34 => 0x41440c000010d31441300000000000000000800000000000000100000000003044040000000000000040000000085210804000000000000004000000000040040400001415010d300000000000000001000001803144130000000000812008000000000000c0105000000000000001c0000000504c82020000000000000004000000000101102000000000000000000000002550020100000000401048080000114350813000000000000000008000000051101202000000000000001400000000000000100000000000000140000000000c810200000000d5200808000000001041200000000000042440c00000995010d300
  | 5, 35 => 0x1c0000000214842010000020455200c000000000000000060000000000000018000000015480200000000000000001c000000035440200000006510d314c00000000000000005000000000032441400000000000000200000000004044080000000000000000000016540424c00000000051101202000000000000000000001145108130000000560c5404c0000000813548030000000000950108000000000000000020000046494018c00000000000000007000006510d204c00000000000000004000000000000001400000000010010100000000002004040000000000000010000000000000010000000000000007
  | 5, 36 => 0x9020804000000000000006000000000000001c0000000000c51020000060085204c0000000000000000600000001011048080000184304413010000000000000008000000000101102000000000030440400000000000000400000000000000180000184404413020000000000000000000000012448201000000000021440c0000099500c5300000000010842480400000004508120100000000003144000000000000000010000000081200804000000000101102000000000000000000000000000000400000000d520080400000004548020200000600c5304c000000000000000040000000000304404000000000000004
  | 5, 37 => 0x3144000000000450812010000000000404408000000000000004000000000000001000000000000000200000000000000100000180314413000000000000000004000000000105103000000000000000800000000000000400000610c1104c04000000000041103000000000000001000000000000000700000454d5200c000000000020812000000016540434c0000000000000000400000000c530480000000004544020000000001142048040000000000000020000000114204804000004125440300000000000002040000000000000000400000000552008040000000000000040000065085104c00000000035440202
  | 5, 38 => 0x941048040000188314853000000000000000010000000021484200000000000043440c00000002048020100000000954008040000000104402010000000000000014000008115480300000000000040440800001943148130000000000d510080800001182544130000000000004344000000188504c53000000000000000010000000000000001000000000021440c0000000151012020000000041100804000000001041200000000010d30480000000000000000400000000812008040000000354042000000046540314c000000000204802020000043541314c00000000000040101000000010d314800000000000000005
  | 5, 39 => 0x144404808000010d424c530000000000552008080000000214842010000036540414c00000000000000002000000000043440c0000000000c9105000000000000001800000000000000400000000004344000000000000000040000016416404c000000000000000040000031481200c0000000003548020000000610c1104c04000000040441202000000000000001000000002048020100000001142048000000000454802020000000115100804000000000000007000006010d304c0000000001548020100000520c9304c000000000250c1202000000005520080400000000010d1000000000000000008000000035480200
  | 5, 40 => 0x25085104c0000000001548020100000000c11048040000000000c1102000000000030440400000000000000000000204d5200c000000180434c1300000000000040440000000000000000200000000000000100000000510c120100000204d5200c000000000000c51000000043485210c00000000015480201000000000030440400001495210d30000000000000000040000000000000040000000000200400000000000000004000000014440480800000001550020100000000552008000000000154c0202000000000041440c0000000000000020000000000304404000000020480202000000000000000000000d945041300
  | 5, 41 => 0x4144000000000001011020000000114104804000000000000007000000014830480800000000000000300000204d5200c080000000000000040000000114204804000000035480200000000000010440800000002048020100000001151008080000000354402020000026540314c0000000000000000100000000000000180000000000000040000060105104c000000000000000060000000000000010000000040500201000000000000000400000001004120100000001152008040000180314c1300000000000000000c000000020480200000000000000001000000000010d1030000000000424418000000025041200
  | 5, 42 => 0x10d314800000000000000006000000000000000c00000004504120000000000000000100000000434c52000000000000000014000008135480300000000000010440c000000045408201000000010110480800000000000000500000000552008080000148314c130000000000000000100000000000000020000043548314c000000000000801020000043540314c00000000000081101000000000000000800000005110120200000104d5100c00000000002081201000000000000001000000000000000400000000812008080000000354062010000000000000014000010d154803000000000115200800000000000000001
  | 5, 43 => 0x100000000000000040000000144304804000000045081201000000000042441800000000000a100000000010d30480000000414544030000000000941048040000000000000040000036544404c000000000434c12000000000095400804000000000109106000000000041440c00000995010d3000000016540434c000000188434c530000000000000000040000000000c910500000000000000040000000000000020000026540414c0000000000000000700000000d51008040000188504c530000000001443048040000000000c91050000000000000008000000000000002000000590d314c00000000000109106
  | 5, 44 => 0x80000000151012020000000000434400000000020480202000000000000001000000000000000500000000951008040000000000c11010000000115200800000000000000002
  | 6, 0 => 0xa3148000000000454c1200000000009510080400000000000a1010000000000000004000000000000002000000000e02880000000004540620200000000000000040000000000000070000000000324414000000000000004000000000000000800000000010d100000000000000001c0000000000000040000000095100808000000000000006000000000040440400000000010d100000000000000840000000000000000200000000002144040000000450412000000000000304408000000000080102000000000000000800000000000000300000000000000080000000000000000000000000200404000000000041101
  | 6, 1 => 0x20404000000030441201000000000000001c00000004544020000000000000000140000000000c1101000000000040440400000000000210100000001152148000000000000c110100000001494348000000000520c5200000000010d3148000000000154802000000000000000018000000000000000000000000000001400000000590d2000000000041100804000000035402200000000010d314800000000000101102000000010d21480000000000010d10000000000000000080000000000000010000000000000014000000000109103000000000020040000000000000000300000000d5018804000000000000002
  | 6, 2 => 0x28404000000010440200000000000a00880000000002048020000000000000000040000000454c5200000000000032441400000000000000400000000552008000000000000000040000000000000010000000035480201000000000000001c0000000354802000000000000214400000000000000001000000010d10480000000000000e10200000000000000000000000454c5200000000000000840400000000008110200000000000000140000000000000050000000115200804000000040441202000000000e02880000000000000000100000000004144040000000000000020000000000204408000000000000001
  | 6, 3 => 0x1152008040000000000000000000000000100404000000000100101000000000000001c00000000000210000000000000204040000000000000040000000148434800000000000081102000000000000001c0000000250022000000000000000008000000000000006000000000000001400000000000000100000000000000140000000000000000000000000104408000000000000000000000000000001000000000000000400000000000284000000000434c5200000000000000001c0000000000c9105000000000000001000000002048020000000000003044080000000000000060000000000000008000000000040101
  | 6, 4 => 0x11510080000000000000000400000000000000140000000000c110100000000d510080000000000010110000000000002004040000000000000010000000000000004000000025402200000000000030440000000003540a200000000008120080800000004548020200000000852108000000000000000040000000000028404000000000000004000000011532480000000000008010000000001404148000000000000000020000000081200804000000000006101000000000043440c0000000434c52000000000000000004000000000000004000000000000001c000000000101102000000000000001800000003540a200
  | 6, 5 => 0x200404000000035440201000000008520480000000000004110000000000000084080000000000061010000000115304800000000000000001000000000e018800000000035440200000000010d3148000000000000c910200000000004044040000000435012000000000000028400000000035480202000000001502880000000000001210100000000163248000000000434c520000000000002004040000000214842000000000115008800000000000000005000000011410480000000000000a102000000009410480400000000000000100000001150088000000000000000050000000000420404000000000008102
  | 6, 6 => 0x10000000000000007000000000000001000000000000000200000000d52148000000000000491010000000055200804000000000000005000000000043440000000004504120000000000d52008040000000001051000000000000304408000000043402200000000009401880000000002048020000000000001044040000000000000070000000000000010000000000000007000000000000001400000000010d10000000001151008080000000000000000000000095100800000000000081102000000000000001400000000000000200000000552008000000000000000060000000000000014000000000000006
  | 6, 7 => 0x14000000000000003000000010d018800000000000000006000000000e0188000000000000000030000000000214404000000000081101000000010d104800000000000000005000000000000000000000000500620000000000000384080000000000121000000000000000004000000000081102000000000012040400000000000610000000000000000100000000000000040000000000304404000000035440200000000000000000800000001540a200000000000000001c000000000000001000000000000001400000000000000400000000000000000000000000000020000000000000010000000000101102
  | 6, 8 => 0x43440000000000010410100000000c1104804000000000000006000000010110480800000000010d1000000000000000014000000000000000000000010d40480000000005010d20000000001152008040000000000000040000000055008800000000021484200000000000032440800000000000000100000000004044080000000000061000000000000000014000000000000006000000000000000c0000000454852000000000000000004000000000085102000000011510080000000000180220000000000c500880000000001548020000000000003144080000000000000040000000000000018000000015480200
  | 6, 9 => 0x1c0000000250022000000000000000014000000000000001000000000020040800000000000000400000000000000040000000000000040000000000028400000000000000004000000000032441400000000480a20000000000000000040000000000c9100000000000000000400000000000000700000001151008000000000000c11010000000014028800000000000040102000000000000001800000004504120000000000552008000000000214842020000000000434400000000000000000000000000010440400000000000000400000000000000180000000000061010000000016404800000000000000004
  | 6, 10 => 0x95008800000000000000001000000000000001c0000000404412020000000000434400000000000000002000000010d414800000000000084101000000000001840400000005110120200000000000184080000000000c1101000000000000000c0000000000000010000000000000008000000000000000000000000000840000000000000000500000000c5214800000000000000007000000011521080000000000008010000000000d50288000000000000c910000000001153148000000000000000030000000000324414000000000000005000000000000840400000004548020100000000000000000000000000c9105
  | 6, 11 => 0xd5200800000000000012101000000000000000c00000000010d10000000000d5100804000000000000003000000008521080000000000000000200000000000000080000000000000000000000055200800000000045402200000000000000001000000000480a2000000000016314800000000000041102000000001631480000000004350520000000000411008000000000415012000000000000000008000000000000007000000000000000400000000588520000000000812008040000000000000040000000081200808000000000040101000000000020040800000000004810100000000003044000000000000c1101
  | 6, 12 => 0x840800000004548420000000001443048040000000000000060000000000404400000000000002102000000000000001c00000000000000100000000002044040000000000c910200000000000000040000000000000020000000000000018000000000000003000000000000001800000000000a1010000000000000000000000000085100000000001641480000000000000000400000000002044080000000000000050000000000424404000000000000002000000000010440400000000010d103000000000000001400000000000000000000000000000040000000000481020000000000314400000000035440200
  | 6, 13 => 0x1c00000000000000200000000812008000000000454402010000000000424404000000000040102000000004110080800000000000210100000000c5104800000000015480201000000000000000c0000000434c120000000000d52008040000000000000010000000016200800000000035440201000000011510080800000000000000200000000004044040000000354402020000000041100808000000000041101000000000010440c00000000008510000000000000000140000000000811010000000144404808000000000081100000000004110080400000000000210100000000552008000000000000c5100
  | 6, 14 => 0x10000000000000005000000000041440000000000000000300000000c530480000000004150120000000000000084000000000000411000000000000100404000000000000005000000005520080000000000000000600000000002144080000000454402000000000000000018000000045480202000000008521080400000000000000300000000550288000000000000c1101000000000000000c0000000000c910500000001402148000000000000411000000000000000014000000015480200000000010d02880000000000000610100000000000000100000000354842000000000000404408000000021484200
  | 6, 15 => 0x10000000000000004000000000001840000000000500a20000000000000000100000000000401010000000012018800000000000081101000000000000000c0000000000000000000000000204404000000015480202000000008521080400000000590d2000000000000008400000000025440200000000004110080000000000008510100000000000000180000000001051010000000000000000000000000085102000000010d008800000000025440200000000000000840800000000010d100000000000010040400000000000000000000000000184000000000000c510200000000d5200804000000000000005
  | 6, 16 => 0x18000000000000007000000000000000400000000000000400000000d5018804000000052105200000000011500880000000000008010200000000000000100000000000000070000000095100804000000000000001000000000000000400000000000a102000000000000001c00000004548020000000000002144040000000058c1200000000000000000800000000000000200000000000000040000000000c0102000000010d0288000000000000000020000000000324408000000000000001000000009510080400000002148420200000000000000140000000000401020000000000028404000000000002100
  | 6, 17 => 0x552008040000000520c120000000000000284000000000000c510200000000004344000000000000c110100000000d42048000000000001051010000000000000010000000000002100000000000001840400000000000000100000000002044040000000048062000000000081200800000000000104101000000000032440000000000000a10100000000002044080000000000c910500000000000284080000000454062020000000000000004000000000041100000000000000001400000000000000400000000000000100000000434c120000000000000000140000000000000050000000095100808000000015480202
  | 6, 18 => 0x1400000003148020000000000000000040000000000000050000000000000000000000000000004000000000021040400000000000a1010000000000324414000000000000000000000000000001c0000000000000070000000000018400000000005880200000000010d3048000000000000851020000000000000014000000000000004000000011510080400000000000610100000000000000080000000000c91050000000000028400000000000000007000000000a008800000000000101102000000000000000800000000008110100000000852108000000000354022000000000000000004000000000000005
  | 6, 19 => 0x1840000000000000000400000000000084040000000104402020000000144304804000000051101202000000010d018800000000000000002000000000040440400000000280220000000000003244140000000501052000000000000000004000000051081200000000000000000800000000000000200000001413148000000000000c5100000000010d304800000000000000000000000000000001c0000000000c110000000000003244140000000000000020000000000000018000000000000005000000000030440400000002544020000000000000000000000000000000000000000000018408000000000000002
  | 6, 20 => 0x8000000000085101000000000040440800000000000610100000000001044040000000000000060000000115028800000000000101100000000000000000000000000008010000000000000000100000000000000000000000000204404000000000081102000000000000001c0000000000000050000000015028800000000020480200000000000000000000000000000000100000000d5104800000000020480200000000000000001c000000035480200000000000000001c000000000000007000000000010440c00000000000000300000001153248000000000501052000000000000000008000000041441200
  | 6, 21 => 0x14843480000000003144120000000000d520080800000000000000400000000000084080000000000411020000000000424404000000000048102000000000042440000000000000a101000000004110080800000000008010100000001412108000000000434802000000000000038408000000000000001000000000000001400000000000a10200000000164348000000000000000060000000000018408000000000000000000000010d008800000000000105101000000000030440400000004340620000000000d52048000000000434c520000000000000000180000000000000010000000000404408000000000000005
  | 6, 22 => 0x6008800000000043440200000000000000001c000000000008101000000000000001400000000000e10200000000000000140000000000801010000000000200408000000035440202000000000041440000000000590d200000000010d204800000000000000001000000004110080000000000004010000000000001004000000000434c12000000000000104400000000000000007000000000000000c000000000000001000000000000000400000000000000600000000852048000000000001001010000000081200800000000021484202000000000000000c000000000081101000000000000001c000000000004100
  | 6, 23 => 0x14000000000000002000000000000001000000004348520000000000411008000000000000c1102000000000030440400000000000000400000000000000140000000000000000000000000018404000000021484201000000014543480000000000000000300000000812008080000000501092000000000000120408000000035406201000000000000000c00000004540620200000000004204040000000000000070000000000324414000000025440201000000009510080800000000004010200000000812008000000000000061020000000000104400000000000040101000000000000001c000000000006100
  | 6, 24 => 0x1040000000000000000500000000000084080000000434c5200000000000000840800000005010d200000000000000000000000000590d200000000008120080000000000000a1010000000115200800000000000081102000000010d21080000000000008410100000000003044040000000000c11010000000000404408000000045485200000000000000840000000000004110100000000d520080000000000004110200000000000000140000000000000060000000000000010000000000000006000000005520080400000000000000500000000d5008800000000000100101000000010d02880000000000000a102
  | 6, 25 => 0x1c00000000000210100000000000000140000000000411020000000000204400000000000000000000000005520080400000000000a100000000010d31480000000000000410200000000000000100000000000000020000000000100408000000000000004000000000000001c000000000040100000000000000001000000000000000000000000000000140000000204802000000000148414800000000015480202000000000000840000000000000000000000000000000080000000018022000000000148314800000000000000005000000000000000c0000000000c91000000000000000000000000005909200
  | 6, 26 => 0x1000000000000000100000000000000040000000000000020000000000000004000000000000004000000000032441400000000000a102000000000000001000000000000000300000001403148000000000454c5200000000000020040800000005150d20000000000000000100000000000000050000000095100808000000000000002000000000004840400000000000a100000000000042441800000005250d2000000000000008404000000000000004000000010d314800000000000000005000000000000001000000004548020100000000000244040000000000000060000000115100804000000000000002
  | 6, 27 => 0x800000000000000600000000002144040000000058c920000000000000000100000000250412000000000000304404000000000000000000000000040440800000000000410100000000000184040000000000000010000000000000004000000000080100000000000000000000000000000000000000000002144000000000000c1100000000000004840400000000000000400000000000000040000000504c520000000000001004040000000434c52000000000000008404000000000000000000000000031440000000000000000700000000003244140000000000000030000000000000004000000043484200
  | 6, 28 => 0x14042480000000001540220000000000000184000000000000c510500000000d510080000000000010d10000000000000000140000000000000050000000000000014000000000000000000000000020040400000000000000100000000d520080800000000000000200000000000000080000000000000040000000000000014000000000000007000000000000001000000004508120000000000d420480000000004548420000000000000184080000000000c1101000000000000001000000004548020000000000000000080000000000000020000000140314800000000035440200000000010d314800000000000000007
  | 6, 29 => 0x1152008000000000000c110100000000d5200804000000000041102000000000000000c0000000000000050000000000000004000000000104101000000000012040400000000000610100000000000000180000000524c520000000000000000080000000424c520000000000003144140000000000000010000000000000000000000000101102000000000000840400000000000210100000000000000080000000000000050000000000000014000000000000005000000005400880000000000000000700000000004044080000000000c9105000000000000000800000000000000400000000000000040000000324c1200
  | 6, 30 => 0x1c0000000354802000000000000000000000000000000005000000000000000000000001548020000000001404348000000000000000050000000000210404000000000000003000000000000001c000000000100101000000000000000c0000000000000040000000041100800000000000000001000000000000001c00000002500620000000000c110480400000000010110100000000004244040000000434c520000000001152008080000000000000040000000000210400000000000000004000000000032440800000000000000200000000001004080000000000000030000000000104404000000000000004
  | 6, 31 => 0x14830480000000000004110300000000000204080000000000411020000000000000014000000000000005000000000004840400000000000000500000000000000180000000000000030000000000008404000000000000007000000000000001c000000000000002000000000000840800000000000e10200000000d52008000000000454402000000000000314408000000000000006000000000000001400000004348020000000000003204080000000000000040000000085104800000000000006100000000000000001000000000000000600000001151008000000000314c12000000000141214800000000000000007
  | 6, 32 => 0x85210800000000000000007000000000032440000000000000000500000000000000100000000104402000000000000000008000000000000007000000014830480800000000010d100000000011520080400000000000000100000000000000140000000000801020000000000410404000000025041200000000000000001c000000025440200000000000001840000000005210120000000000003244140000000000000040000000095100800000000000101100000000000002840400000000010510100000000000000080000000000000050000000000000018000000000000001000000000000000c000000035402200
  | 6, 33 => 0x400000000500620000000000002044040000000434c52000000000041100800000000000104101000000000041440400000000004110200000000001044040000000001081010000000000000010000000000000006000000000000001800000005010d200000000000000001400000003540620100000000001004040000000000811010000000000020404000000010440200000000000030440800000000000000500000000000000100000000000000040000000000000014000000000000000000000000000840000000004144120000000000000484040000000000000040000000000000014000000000000002
  | 6, 34 => 0x400000000008010100000000001004000000000435052000000000000048400000000000000002000000000000000c00000000000000400000000000000040000000000801000000000000000014000000000000004000000000000001c0000000000000040000000000214408000000031485200000000000002840800000000010110200000000003044040000000000000050000000000000010000000000000007000000014831480000000000000210100000000004144000000000001091010000000000204404000000000000004000000000000000800000002544020000000000002144040000000500c5200
  | 6, 35 => 0x100000000000000010000000000000014000000000000004000000000021440c00000000000000400000000000000040000000000801010000000000214400000000000000005000000000003840000000000000a101000000000000001c0000000214842000000000000414404000000000000005000000000043440c00000000000a100000000000000000c000000000000003000000000000000400000000000000100000000163148000000000000401010000000000314400000000045480200000000000000001400000002544020000000000000000040000000000411020000000016404800000000000000001
  | 6, 36 => 0x9510080000000000000000100000000940188000000000434c5200000000004110080000000003548420000000000004044040000000000c1101000000000010440400000000000000400000001402148000000000000c91050000000000000008000000000000006000000000000001800000002544020000000000000000040000000001011020000000000000010000000000000001000000000000001800000000000000700000000000384000000000354402000000000000304400000000000000004000000000000001800000001548020000000000000000140000000214842000000000000000014000000003802200
  | 6, 37 => 0xd521080000000000000000200000000000000140000000001011020000000000314408000000000006101000000014931480000000000008110100000000d5200800000000000000004000000000000000000000000000000200000000540088000000000254402000000000144404808000000043485200000000000002840000000000010d10000000000d5100800000000000084101000000000000001400000000000000100000000d520080400000000000000500000001152008080000000000000070000000081200800000000000006100000000000010440c00000000010d1000000000000000000000000000000006
  | 6, 38 => 0xd5100808000000000101102000000000000001400000000000000400000000003044000000000001091000000000016200800000000000084100000000000000001c000000000084102000000000010040400000000010510100000000003044080000000000411000000000000304404000000000000005000000000010040400000000000000500000000000000100000000000000010000000115104800000000000000006000000000000000400000000008010200000000550088000000000000c11020000000000038408000000020480200000000000000000800000000000000400000000d5200800000000000000005
  | 6, 39 => 0x324408000000000000005000000000010040800000000008010100000000162148000000000000c110100000000000184080000000000801010000000000000014000000000000004000000000000000000000004144120000000000d520480000000000590d2000000000115100800000000000002101000000000000001c00000005110120200000000d5200800000000000000006000000000021440400000003548520000000000000000140000000154802000000000114204800000000000105101000000008120080000000000008010000000000851048000000000154802000000000000000014000000000084102
  | 6, 40 => 0x1000000000000000000000001443048040000000354402000000000140324800000000000006101000000000000000800000000010510300000000d520080800000000004010100000000552008040000000000c510500000000002004080000000000000010000000000000004000000000000002000000000000001c0000000000000010000000000000018000000035480200000000000000001c0000000001091010000000000000010000000000000005000000000000001800000000000a102000000000000000c0000000000c110100000000003144000000000000000070000000000204400000000000000005
  | 6, 41 => 0x100000000000000050000000115314800000000000006100000000000002840400000000000000100000000000000180000000000411000000000000000014000000000000004000000000000000800000000000a1020000000000324414000000000000002000000000010040000000000000610100000000000000040000000001001010000000000100404000000000040102000000000031440800000000000000200000000001044080000000354802020000000144434800000000000080101000000011520080000000002148420200000000000484040000000154802020000000000000010000000045440201
  | 6, 42 => 0x38400000000000000000000000000000000c00000000000000100000000120388000000000000000010000000000000014000000000000007000000000004840000000005210d200000000000030440800000000008010100000000d5200800000000000006102000000000021440400000000000000500000001483148000000000434c520000000000000000040000000324812000000000115200800000000000000005000000014440480000000000000210200000000002144040000000000411010000000000200404000000000000005000000011520080000000000010110200000000d5200800000000025402200
  | 6, 43 => 0x100000000204802000000000115104800000000000000004000000000000000800000000000000400000000000000140000000000000070000000109404800000000045440200000000000000001000000001548020000000000c52148000000000000000040000000000028404000000000081101000000001401880000000000000000000000000164148000000000000c5100000000000000000800000000000000000000000003044080000000435092000000000012314800000000000006100000000005520080000000000000000300000000000084000000000000021010000000000000004000000000000006
  | 6, 44 => 0x32440000000000000000000000000001004040000000001011020000000000000014000000000000005000000000021440800000000480e20000000000000000140000000454c520000000000000144040000000000c11010000000114104800000000000000001000000000000000c00000000001210100000000000084080000000000c5100000000009510080000000000000000500000000163148000000000000c910200000000003144000000000000c51030000000000304404000000000000001000000000000001800000000010810100000000000084000000000000000030000000115200800000000000081101
  | 6, 45 => 0x80000000000000020000000148414800000000040441202000000010d314800000000000000005000000000000001400000000008410100000000002144040000000000c81020000000095100800000000025006200000000000a0188000000000434c5200000000000020040800000000480220000000000000000140000000000000010000000081200800000000000000005000000000002840000000000000210000000000000000080000000454802000000000085204800000000000000002000000014042480000000000000000500000000550088000000000001011020000000000214404000000000000002
  | 6, 46 => 0x30440000000000010810100000000000000100000000000c510200000000000000040000000000811010000000115100804000000000000001000000011410480400000000008110200000001152008000000000000000050000000000000010000000000040102000000000031440800000000000000000000000000000140000000000000030000000000000000000000000008102000000000000001c0000000000c110100000000001004040000000354402020000000000000014000000000000001000000008120080400000001044020000000000000000140000000000401000000000148404804000000000081101
  | 6, 47 => 0x140000000000121010000000000000008000000035480200000000000043440c00000000000000600000000000000140000000000000070000000000214400000000000000001000000000000001400000000000000100000000000184080000000001091010000000000000010000000000081101000000000000001c000000002806200000000000043440000000003548520000000000003144000000000000c110100000000003044040000000434412000000000000028408000000030441201000000000021440800000000010910000000001094048000000000454802000000000000304404000000000006102
  | 6, 48 => 0x1c00000000000000500000000000000000000000314812000000000000000004000000000000000000000011510080400000000010d10000000000001004080000000000c110200000000852108000000000434c12000000000000204404000000000000006000000000000000c00000000000a10100000000000000100000000000000040000000055200804000000015480202000000000000000400000000590920000000000001204040000000000000030000000000000008000000000000007000000000032441400000005150d20000000000000000000000000520c1200000000000000000c000000000000007
  | 6, 49 => 0x951008000000000000811020000000000400404000000000000005000000000000000c000000000000005000000000000001000000000010d10000000001152148000000000000000010000000000008408000000000000004000000010510480000000005210d20000000000812008040000000000c91020000000000008408000000000000004000000000000001800000000000000400000000000000180000000000000060000000000000000000000000000004000000010d304800000000000000005000000000000000400000000008410200000001011048080000000000841010000000109204800000000000000004
  | 6, 50 => 0xc000000000000004000000000000001c000000045480200000000000000000c000000000000004000000000000000800000000008010100000000000000100000000000000070000000000210408000000000000007000000000000000800000000010d1000000000000304408000000000000005000000008120080000000004548020200000000004004040000000000c9105000000000000000800000005250d20000000000002004080000000434022000000000140434800000000000000006000000000000001c00000000000000500000000000000100000000000000070000000000008404000000000048101
  | 6, 51 => 0x800000000008510200000000000000140000000000c1102000000000000001c00000000010d100000000000000000c0000000000000000000000000000014000000000041101000000000000001c000000000000005000000000031440800000000000000000000000c5008800000000000000003000000000000001400000000000000000000000d510080400000000000a10200000000d42048000000000204802020000000000100408000000000000004000000000020440000000005048420000000000c110480400000000000000100000000000384000000000038022000000000000000010000000015480200
  | 6, 52 => 0xc510480000000000000000700000000c5304800000000003802200000000000043440c00000003148520000000000004144040000000000c5102000000000000000800000000000000400000000001044040000000001081010000000000100404000000000006102000000000000000400000001044020000000000163148000000000000121000000000000000014000000021484200000000000000001400000004548020200000000000000040000000434c1200000000000000001400000005008520000000000d510080800000000000a10100000000000000000000000000851010000000000000004000000000105101
  | 6, 53 => 0x104400000000000000007000000000042440400000000010d10000000000004044040000000000061010000000000020404000000010440200000000000000840000000000000210000000000000000140000000454812000000000000200404000000000000004000000011502880000000000000000100000000000000140000000454852000000000000214404000000020480201000000000000001c0000000000c0105000000000000001c0000000028c52000000000085104800000000000000002000000000020440400000000000000600000000002044080000000204802000000000000304404000000045440202
  | 6, 54 => 0x1c00000005050d20000000000d52008000000000000801020000000000210408000000000000006000000000000000c000000000000003000000009510080000000000000000100000000000000100000000000c01020000000000304408000000025402200000000000002040400000004144120000000000000084080000000000c9105000000010d41480000000000588120000000000000000080000000434c520000000000003244080000000000000040000000000000008000000000000004000000000040440000000002544120000000000000000140000000000c11010000000000000000000000000000005
  | 6, 55 => 0x20408000000000000001000000000000840400000000590d2000000000000008408000000000000006000000000000000400000000000a100000000000032441400000005010d200000000000021440800000000008010200000000c530480000000003544020000000000000000080000000000000050000000000000014000000000080100000000000000000400000000000000500000000d51008000000000001091000000000000210404000000000000004000000000040440800000000000000400000000d510080400000000000000600000000003044040000000204802020000000000000004000000021484200
  | 6, 56 => 0x140000000000121010000000000000004000000035440200000000000000000000000005150d200000000010d314800000000000006100000000000000840400000000000000100000000002144080000000000c11020000000000000004000000000000001000000000043440000000000000000200000000000000180000000000c5102000000000000001c000000051101202000000010d31480000000000000000300000001151048000000000214842000000000115100800000000000000001000000000010040800000000000000000000000d52008000000000254402000000000000000014000000000000004
  | 6, 57 => 0x1c000000035440200000000000000001800000000000000400000000003244140000000000000010000000000314408000000045440200000000010540480000000000000000400000000000000000000000000000020000000000000008000000010440201000000011510080000000000000a101000000000000001400000001548020000000000d5200804000000000000005000000000041440400000000000a10200000001443048040000000000811000000000000018404000000015480200000000000000001400000000000000200000000000000180000000254402000000000000404408000000000000001
  | 6, 58 => 0x552008000000000000061010000000000000008000000000000001000000000000000400000000000000700000000003244140000000454802000000000000000018000000035441200000000000010040800000003044120100000000000000140000000000401020000000000000008000000000000007000000000030440800000000000000000000000000284040000000404412020000000000000010000000000000004000000005502880000000000000000500000000000000100000000104402000000000000214404000000000000005000000000000001000000000000a1010000000000304404000000000000007
  | 6, 59 => 0xd510080000000004540a200000000008120080400000000004110000000001151048000000000001081010000000000200404000000000041102000000000000001400000000000000500000000000000040000000434022000000000000100404000000005841200000000000020040800000003548020000000000004044080000000000000040000000115100800000000000000004000000000001840400000003544020000000000000000000000000304812000000000144404808000000000000007000000000000001c000000000000004000000009510480000000000000e10000000000002044080000000000c9105
  | 6, 60 => 0xc5214800000000045440200000000000040040400000000010110200000000000000000000000104402010000000000000018000000000101100000000000000001c00000000008410200000000000084000000000000000040000000141434800000000015480200000000000000840000000003548020000000001152008000000000000851000000000085210804000000000012100000000000040040400000000480220000000000000000040000000000c0102000000010d314800000000050484200000000000000001c000000000000004000000010d0288000000000434c520000000000002104080000000000c1101
  | 6, 61 => 0x10d01880000000000010d10000000001443048040000000154802000000000000000014000000035480200000000000010440000000003540620100000000d51048000000000000000050000000000000004000000005885200000000009510080400000002048020100000000000000080000000000c110100000000002004040000000001011020000000000000010000000000000002000000000000000c0000000000000050000000081200808000000000000005000000008521080000000000000000000000000000000180000000434c120000000000000484040000000000000010000000000324414000000015480202
  | 6, 62 => 0x8000000000084101000000000032441400000004544020200000000d520080000000000008110100000000003144080000000000000020000000000000018000000000000006000000000031440800000000000000400000001151008080000000000c1101000000000000001400000004544020000000000004144000000000000c9105000000011520080000000004508120000000000000284000000000214412000000000055200800000000000101102000000001200880000000002544020000000000c510480000000000008010200000001151008000000000434812000000000041100804000000000084101
  | 6, 63 => 0x104408000000045406202000000000000001c000000000000000000000000000001000000000000000500000000003244140000000000021010000000115200800000000045041200000000014041480000000002504120000000000002144040000000000000040000000000000010000000000000006000000000000000800000000000000100000000c11048040000000000000010000000000008400000000045406202000000000000001800000005010d20000000000d5100804000000025441200000000000040440800000002544020200000000000000100000000154802000000000000000008000000000000005
  | 6, 64 => 0x10400000000000000000000000000043440000000000584120000000000000000040000000000c51020000000000404408000000000080102000000000000001400000004248120000000000004344000000000000c1101000000010d008800000000000000004000000000000001c000000000101102000000000040440400000000000000400000000000000000000000314c12000000000000000010000000000101102000000000010440000000002148420100000000d51048000000000000c1101000000000000001400000000000210000000000004044080000000000000000000000000000004000000021484200
  | 6, 65 => 0x434400000000000000005000000010d304800000000000002100000000010d1048000000000500c520000000000d52008000000000434c120000000000000000140000000434852000000000000204404000000045481200000000000000000000000004548020000000000000000180000000000000000000000000000010000000000109101000000000000001c00000002148420000000000000084040000000058c120000000000d50188040000000000811000000000000028400000000000000004000000000020040800000000000000500000000000000140000000254402010000000000204404000000000109101
  | 6, 66 => 0x1151008000000000000000010000000000000010000000000000002000000000000001000000000000000700000000000000080000000314412000000000000008400000000000000006000000000000001400000002048020000000000004244000000000454802000000000000000008000000000000007000000000000001000000000008010100000000411008000000000058812000000000000000008000000000000004000000000000001000000000008510100000000000000100000000000000040000000000000004000000035081202000000010d0288000000000000411010000000000304404000000043402200
  | 6, 67 => 0x1000000000004010000000000c54048000000000000000070000000148404800000000035440200000000010d0188000000000454c920000000000002004000000000000021000000000000404408000000000000003000000000000001c000000035440200000000000000001400000000010910100000000002104040000000250022000000000000010400000000000108101000000010d30480000000000000000000000000004044080000000000000050000000148434800000000043509200000000014032480000000000000000600000000161048000000000000000030000000085104800000000035480200
  | 6, 68 => 0x4110080400000000010d10000000000004044080000000000411020000000144304804000000000000000000000004110080800000000010110200000000000000140000000511012020000000000000000000000000000002000000000000001800000004350920000000000000000100000000000000050000000000324414000000000000005000000010d30480000000000000000100000000000000100000000450812010000000000104404000000035480202000000000004840000000000000a102000000000000001400000000000000500000000000000000000000000c51000000000115008800000000000000004
  | 6, 69 => 0x104400000000000101101000000000020040400000000000000100000000000000040000000000c1101000000010d3048000000000454402000000000000028404000000000000006000000000003840800000000000000700000000000000100000000434c12000000000105314800000000000000007000000000000001400000000000000300000000003044040000000434402000000000115200800000000000000005000000010d3048000000000000000070000000000028400000000000080100000000000030040800000000000000000000000000000080000000354852000000000000000010000000000000005
  | 6, 70 => 0x180000000214842020000000000008404000000000006100000000000000001000000004548020000000000000000040000000000000070000000000000010000000000084102000000000000001400000000000a102000000000042440400000000008010000000000003144000000000000000050000000000434400000000000040102000000014443480000000000008110000000000002144000000000000c1101000000000000000000000000004010100000000000184000000000000000030000000000038400000000045480201000000000000001000000000000000500000000940088000000000510c1201
  | 6, 71 => 0x20440400000000000000000000000000184040000000001011010000000041100800000000021484201000000000032441400000000000000200000000000000080000000000c1101000000000000001c000000000000007000000000000000c00000003544020000000000000000040000000000000040000000095104800000000000000005
  | 7, 0 => 0x1400000000010d1000000000000018404000000000109100000000000001840800000000008410100000000000000000000000000121000000000000314400000000000041102000000000000001c0000000000061010000000000018408000000000041101000000000032440000000000000000600000000000000140000000000121000000000000000014000000000081100000000000000000400000000008510000000000000000040000000000841020000000000104400000000000105100000000000002840400000000000a10200000000000000080000000001051000000000000000008000000000012100
  | 7, 1 => 0x100408000000000000005000000000003840000000000000a100000000000000001c00000000010d100000000000000840000000000000000000000000002004080000000000021010000000000000008000000000081100000000000000000400000000000000200000000000000040000000000c1100000000000041440400000000008110000000000000084080000000000000010000000000324408000000000041100000000000004840000000000010d100000000000020040000000000010d100000000000043440000000000000000500000000000284000000000000000010000000000200404000000000000001
  | 7, 2 => 0x1840000000000000000100000000002044000000000000411010000000000414400000000000041102000000000000000800000000010d100000000000000000800000000010110100000000003144000000000000c110100000000004344000000000000021000000000000204400000000000006100000000000021440400000000000000000000000000084000000000000801010000000000000004000000000000001000000000021440800000000010d1000000000000404400000000000006101000000000040440800000000004010100000000003144080000000000000020000000000434400000000000081100
  | 7, 3 => 0x8000000000002100000000000001840000000000000a100000000000001840000000000010910000000000000084000000000000000050000000000104408000000000000001000000000032440000000000010110000000000002104040000000000000010000000000000004000000000000002000000000000001400000000000000500000000000184000000000000841020000000000000000000000000002100000000000041440400000000000000700000000004044080000000001091000000000000028400000000000000005000000000000000800000000000a1000000000000204400000000000002100
  | 7, 4 => 0x384000000000001091000000000000000004000000000000005000000000000000400000000000000500000000000000040000000000801010000000000028400000000000006100000000000002840800000000000e1000000000000028400000000000105100000000000030440000000000000a101000000000021440000000000001210000000000000184000000000000c51000000000000414400000000000040100000000000000000800000000000000700000000000284000000000000c1101000000000000840000000000000a10000000000001044000000000000000050000000000000004000000000085100
  | 7, 5 => 0x2840800000000000610000000000004144040000000000000020000000000000004000000000000001000000000030440000000000000000100000000000000000000000000c11000000000000214400000000000000002000000000000001400000000008410000000000000484000000000000401000000000000028400000000000006100000000000042440000000000008410000000000000000000000000000801010000000000404404000000000000002000000000001840000000000000610000000000000000080000000000c110200000000000000140000000000801020000000000000008000000000109101
  | 7, 6 => 0x3840800000000010d100000000000000000400000000000a1010000000000028408000000000012100000000000002840000000000008410200000000000084000000000000c11010000000000000010000000000041100000000000004840400000000010110200000000004244000000000000000020000000000214400000000000000005000000000003840000000000000000400000000000084000000000000c910000000000000184080000000001091010000000000018404000000000000005000000000000000000000000000000000000000001044000000000000411000000000000000014000000000006102
  | 7, 7 => 0x400000000008510100000000003144080000000000c91000000000000048400000000000000001000000000010040800000000010d100000000000010440000000000000000300000000001004040000000000021000000000000104400000000000000007000000000000840400000000000000100000000003044080000000000000020000000000214400000000000000002000000000020440000000000000000500000000003144000000000000061000000000000434400000000000080100000000000010040000000000000210200000000004344000000000000c91020000000000104400000000000002101
  | 7, 8 => 0x214400000000000000002000000000021040400000000000000200000000000000080000000000000050000000000314400000000000000001000000000043440000000000000210000000000003144000000000000000050000000000210400000000000040100000000000040440000000000000000100000000000000140000000001011000000000000000014000000000101100000000000000840000000000001210000000000000000140000000000c1102000000000020440000000000010d10000000000000000040000000000851020000000000104400000000000040102000000000000001c000000000002100
  | 7, 9 => 0x14000000000000005000000000000840400000000000210200000000000000040000000000c910200000000000000140000000000000000000000000000008000000000101100000000000000840800000000010d10000000000004244040000000001051000000000000000004000000000084102000000000040440000000000000000000000000000000080000000001051000000000000404400000000000006100000000000021040400000000000a1000000000000000004000000000000006000000000010440000000000000610100000000000184080000000000c1100000000000000001400000000010d100
  | 7, 10 => 0x800000000000e10200000000000000000000000000851010000000000214408000000000081101000000000000000400000000000a10000000000000000040000000000c5102000000000041440000000000000000200000000004344000000000000801000000000000028400000000000040101000000000010040800000000000a100000000000020440000000000000000000000000004144000000000001011000000000000048400000000000101100000000000021040000000000010d100000000000000000400000000010510000000000000000140000000000811000000000000048404000000000006100
  | 7, 11 => 0x2004000000000000811010000000000210404000000000084102000000000000000000000000010d100000000000030440000000000000a1000000000000424400000000000000002000000000010040000000000000a1000000000000000004000000000000004000000000000001c00000000001210100000000000000080000000000021000000000000000004000000000101100000000000021440400000000000a10000000000002004080000000000c1100000000000000001c000000000105100000000000030440000000000008010100000000000000140000000000000060000000000008400000000000105100
  | 7, 12 => 0x484000000000000c110100000000000184000000000000c110000000000000000140000000000061000000000000304400000000000000005000000000030440000000000008110200000000000184000000000000000050000000000104400000000000000005000000000000000400000000000000700000000000184000000000000000050000000000000008000000000000007000000000000000400000000000a100000000000000000800000000000000100000000004144000000000000811000000000000028400000000000000005000000000030440000000000000a1000000000000100400000000000002100
  | 7, 13 => 0x2044080000000000c5100000000000010040000000000000210000000000001004000000000000c910000000000000284000000000000000020000000000000008000000000080101000000000020040800000000000a101000000000001840000000000000a1020000000000008408000000000000002000000000000001400000000010d1000000000000204404000000000002100000000000032440000000000000210000000000000184000000000000c910000000000000384000000000000021000000000000000010000000000000001000000000000001c0000000000000050000000000008404000000000101102
  | 7, 14 => 0x2044000000000000000010000000000000004000000000085100000000000042440000000000000210000000000003244000000000000c5100000000000000000400000000000a1000000000000100400000000000080100000000000000001400000000000000600000000000184000000000000000010000000000200400000000000002101000000000000001c000000000002100000000000002840800000000000000200000000000184000000000000061010000000000324400000000000085100000000000000000800000000008510000000000000000140000000000061000000000000314400000000000006100
  | 7, 15 => 0x2144000000000000061010000000000314400000000000101101000000000021440000000000004010000000000004144000000000000c51000000000000000014000000000084100000000000010040000000000000000200000000002104000000000000c110100000000004044080000000000411000000000000210400000000000109101000000000000001400000000000a1000000000000000004000000000085100000000000000000400000000000a1010000000000314400000000000000005000000000000840000000000004010000000000000184080000000000c91000000000000104400000000000101100
  | 7, 16 => 0x8408000000000000001000000000020040000000000004110000000000002004000000000000841000000000000038408000000000000002000000000043440000000000000000300000000002104000000000000411010000000000028400000000000012100000000000042440000000000010d1000000000000000014000000000081101000000000021040000000000000e100000000000000001400000000008110200000000004244000000000000000040000000000000004000000000000001000000000021040000000000010d10000000000000000080000000000000010000000000028404000000000000002
  | 7, 17 => 0x4144000000000000411010000000000000008000000000080102000000000000001c00000000010d100000000000000000400000000010d10000000000002004000000000000000010000000000028404000000000000004000000000041440000000000000a1000000000000028408000000000000002000000000042440400000000000000200000000000000040000000000851020000000000404400000000000080100000000000000001400000000000e1000000000000038400000000000000005000000000010440800000000010d100000000000000840400000000000000500000000004044000000000000c1100
  | 7, 18 => 0x484000000000000c110000000000000284000000000000000030000000000000008000000000000001000000000000840000000000010110000000000000084000000000000c9100000000000003840800000000000000100000000000000040000000000000040000000000000010000000000000000000000000040440400000000000a1000000000000324408000000000000001000000000000001400000000000610000000000000000140000000000801000000000000000014000000000006101000000000000000800000000008010000000000004244000000000000061020000000000000008000000000081100
  | 7, 19 => 0x104408000000000000004000000000002840400000000000000500000000000000000000000000000010000000000000008000000000006100000000000040440400000000000000200000000000000040000000000000020000000000000004000000000000002000000000021440000000000008510000000000000000140000000000c51000000000000028400000000000000005000000000004840400000000010510000000000000000000000000000c11000000000000100400000000000000005000000000001840400000000000000000000000004144040000000000c51020000000000000008000000000000007
  | 7, 20 => 0x30440800000000008110200000000000000080000000000411000000000000204404000000000109100000000000000000800000000000000200000000000084000000000000c110000000000000000140000000000c910000000000000000100000000000000010000000000028408000000000006100000000000042440400000000008110000000000000000040000000000c910000000000000000080000000000841000000000000434400000000000105101000000000042440000000000000a100000000000042440000000000000610000000000004344000000000000411010000000000018400000000000000004
  | 7, 21 => 0x84080000000000851000000000000000008000000000006101000000000000001800000000000210100000000000000040000000000c51000000000000424400000000000081100000000000010040000000000008410000000000000084000000000000c510000000000000384000000000000411010000000000424400000000000012101000000000003840000000000008510000000000004344000000000000c5100000000000000840000000000000a1010000000000100400000000000002100000000000042440000000000000000100000000000000040000000000000070000000000324400000000000000001
  | 7, 22 => 0x400000000000610200000000000084000000000000c51000000000000324400000000000002100000000000000000c00000000000610000000000000284080000000000841000000000000314400000000000002101000000000002840400000000000e1000000000000018408000000000000000000000000000000400000000004110000000000002004000000000000021000000000000404404000000000002101000000000000000800000000000e100000000000010440000000000000610000000000000284040000000000c110100000000000284000000000000801000000000000000008000000000000006
  | 7, 23 => 0x3144080000000000401020000000000214400000000000000000000000000031440000000000008110100000000002044080000000000000050000000000028400000000000085101000000000000840000000000000000100000000001004000000000000c91000000000000018404000000000006102000000000000000000000000000000100000000000000180000000000021020000000000038400000000000006101000000000010040400000000010d1000000000000324408000000000000001000000000021040000000000000000100000000000000080000000001051010000000000038400000000000000002
  | 7, 24 => 0x200000000000484000000000000851010000000000314400000000000080100000000000021040000000000000000100000000000000040000000000401010000000000304408000000000084101000000000000000c000000000101100000000000000001c00000000000210100000000000000080000000000021020000000000200400000000000000005000000000000000400000000000000200000000000284040000000000021020000000000100404000000000000000000000000002840800000000010510000000000002144080000000000061000000000000008404000000000000001
  | 8, 0 => 0x40000000000000020000000000000004000000000000002000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000200000000000000000000000000000020000000000000004000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_4 roots_4 8 s ws hint
  | 1 => checkCutEntry dom_5 roots_5 7 s ws hint
  | 2 => checkCutEntry dom_10 roots_10 7 s ws hint
  | 3 => checkCutEntry dom_12 roots_12 6 s ws hint
  | 4 => checkCutEntry dom_14 roots_14 5 s ws hint
  | 5 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 6 => checkCutEntry dom_16 roots_16 5 s ws hint
  | 7 => checkCutEntry dom_17 roots_17 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 62 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_18 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_18 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_18 == dom_18) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_18 goalM u ys) : RunD dom_18 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_18 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 3 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 3 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 3 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 8 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_8 : ∀ i, 8 ≤ i → i < 16 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_16 : ∀ i, 16 ≤ i → i < 24 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_24 : ∀ i, 24 ≤ i → i < 32 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_32 : ∀ i, 32 ≤ i → i < 40 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_40 : ∀ i, 40 ≤ i → i < 47 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 7 40 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 47 → Z 3 i = true := range_split z3_0 (range_split z3_8 (range_split z3_16 (range_split z3_24 (range_split z3_32 (z3_40)))))
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
theorem z4_128 : ∀ i, 128 ≤ i → i < 136 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_136 : ∀ i, 136 ≤ i → i < 144 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 136 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_144 : ∀ i, 144 ≤ i → i < 152 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_152 : ∀ i, 152 ≤ i → i < 160 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 152 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_160 : ∀ i, 160 ≤ i → i < 168 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_168 : ∀ i, 168 ≤ i → i < 176 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 168 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_176 : ∀ i, 176 ≤ i → i < 184 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_184 : ∀ i, 184 ≤ i → i < 192 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 184 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_192 : ∀ i, 192 ≤ i → i < 200 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_200 : ∀ i, 200 ≤ i → i < 208 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 200 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_208 : ∀ i, 208 ≤ i → i < 216 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_216 : ∀ i, 216 ≤ i → i < 224 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 216 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_224 : ∀ i, 224 ≤ i → i < 232 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_232 : ∀ i, 232 ≤ i → i < 239 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 232 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 239 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (range_split z4_48 (range_split z4_56 (range_split z4_64 (range_split z4_72 (range_split z4_80 (range_split z4_88 (range_split z4_96 (range_split z4_104 (range_split z4_112 (range_split z4_120 (range_split z4_128 (range_split z4_136 (range_split z4_144 (range_split z4_152 (range_split z4_160 (range_split z4_168 (range_split z4_176 (range_split z4_184 (range_split z4_192 (range_split z4_200 (range_split z4_208 (range_split z4_216 (range_split z4_224 (z4_232)))))))))))))))))))))))))))))
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
theorem z5_544 : ∀ i, 544 ≤ i → i < 552 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_552 : ∀ i, 552 ≤ i → i < 560 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 552 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_560 : ∀ i, 560 ≤ i → i < 568 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_568 : ∀ i, 568 ≤ i → i < 576 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 568 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_576 : ∀ i, 576 ≤ i → i < 584 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_584 : ∀ i, 584 ≤ i → i < 592 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 584 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_592 : ∀ i, 592 ≤ i → i < 600 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_600 : ∀ i, 600 ≤ i → i < 603 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 600 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 603 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (range_split z5_200 (range_split z5_208 (range_split z5_216 (range_split z5_224 (range_split z5_232 (range_split z5_240 (range_split z5_248 (range_split z5_256 (range_split z5_264 (range_split z5_272 (range_split z5_280 (range_split z5_288 (range_split z5_296 (range_split z5_304 (range_split z5_312 (range_split z5_320 (range_split z5_328 (range_split z5_336 (range_split z5_344 (range_split z5_352 (range_split z5_360 (range_split z5_368 (range_split z5_376 (range_split z5_384 (range_split z5_392 (range_split z5_400 (range_split z5_408 (range_split z5_416 (range_split z5_424 (range_split z5_432 (range_split z5_440 (range_split z5_448 (range_split z5_456 (range_split z5_464 (range_split z5_472 (range_split z5_480 (range_split z5_488 (range_split z5_496 (range_split z5_504 (range_split z5_512 (range_split z5_520 (range_split z5_528 (range_split z5_536 (range_split z5_544 (range_split z5_552 (range_split z5_560 (range_split z5_568 (range_split z5_576 (range_split z5_584 (range_split z5_592 (z5_600)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z6_928 : ∀ i, 928 ≤ i → i < 930 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 928 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 930 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (range_split z6_376 (range_split z6_384 (range_split z6_392 (range_split z6_400 (range_split z6_408 (range_split z6_416 (range_split z6_424 (range_split z6_432 (range_split z6_440 (range_split z6_448 (range_split z6_456 (range_split z6_464 (range_split z6_472 (range_split z6_480 (range_split z6_488 (range_split z6_496 (range_split z6_504 (range_split z6_512 (range_split z6_520 (range_split z6_528 (range_split z6_536 (range_split z6_544 (range_split z6_552 (range_split z6_560 (range_split z6_568 (range_split z6_576 (range_split z6_584 (range_split z6_592 (range_split z6_600 (range_split z6_608 (range_split z6_616 (range_split z6_624 (range_split z6_632 (range_split z6_640 (range_split z6_648 (range_split z6_656 (range_split z6_664 (range_split z6_672 (range_split z6_680 (range_split z6_688 (range_split z6_696 (range_split z6_704 (range_split z6_712 (range_split z6_720 (range_split z6_728 (range_split z6_736 (range_split z6_744 (range_split z6_752 (range_split z6_760 (range_split z6_768 (range_split z6_776 (range_split z6_784 (range_split z6_792 (range_split z6_800 (range_split z6_808 (range_split z6_816 (range_split z6_824 (range_split z6_832 (range_split z6_840 (range_split z6_848 (range_split z6_856 (range_split z6_864 (range_split z6_872 (range_split z6_880 (range_split z6_888 (range_split z6_896 (range_split z6_904 (range_split z6_912 (range_split z6_920 (z6_928))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z7_368 : ∀ i, 368 ≤ i → i < 371 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 368 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 371 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (range_split z7_208 (range_split z7_216 (range_split z7_224 (range_split z7_232 (range_split z7_240 (range_split z7_248 (range_split z7_256 (range_split z7_264 (range_split z7_272 (range_split z7_280 (range_split z7_288 (range_split z7_296 (range_split z7_304 (range_split z7_312 (range_split z7_320 (range_split z7_328 (range_split z7_336 (range_split z7_344 (range_split z7_352 (range_split z7_360 (z7_368))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 23 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 7 16 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 23 → Z 8 i = true := range_split z8_0 (range_split z8_8 (z8_16))
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
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_18 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
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

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_18_bits : ∀ r : Fin 64, roots_18.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_18_lt : ∀ r : Fin 64, dom_18.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_18 T)
    (hlow : Lower dom_18 roots_18 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_18, Avail mask256 roots_18 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_18 hfan 0 roots_18 roots_18 rfl hsup0
  set out := (execN C.gates roots_18).getD C.output 0
  have hout : out &&& dom_18 = T &&& dom_18 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_18_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_18 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_18_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_18).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_18)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_18.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_18 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_18).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_18 &&& mask256 = dom_18 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_18 = T &&& dom_18 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_18, hd63, hout]
  have hnc_m : ¬ IsConst dom_18 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_18 roots_18 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_18, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_18 roots_18 0 roots_18 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_18.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_18 10 hT6 (by unfold IsConst; decide) low_18

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [7, 1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [12, 3]⟩, ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.or, [11, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_13125_aux

theorem PEqualNP.Outside.L_meta_13125 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_13125_aux.wit, PEqualNP.Outside.L_meta_13125_aux.wmono, le_trans PEqualNP.Outside.L_meta_13125_aux.wsize (PEqualNP.Outside.L_meta_13125_aux.lower s hs), PEqualNP.Outside.L_meta_13125_aux.weval⟩
