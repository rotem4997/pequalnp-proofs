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

namespace PEqualNP.Outside.L_meta_13099_aux

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

def dom_0 : Nat := 0x3333
def goal_0 : Nat := 0x3220
def roots_0 : List Nat := [0x2222, 0x3030, 0x3300]

namespace S_0
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (4, 5), (4, 12), (8, 9), (8, 12)]
def r1sG : List Nat := [1, 1, 4, 4, 8, 8]
def r2sG : List Nat := [5, 9, 5, 12, 9, 12]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_0 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_0 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
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

def dom_1 : Nat := 0x33333333
def goal_1 : Nat := 0x32223220
def roots_1 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x33330000, 1, 17)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0xf0f0f0f
def goal_2 : Nat := 0xe0e0a08
def roots_2 : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xff00ff
def goal_3 : Nat := 0xee00a8
def roots_3 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0xffff
def goal_4 : Nat := 0xfaa8
def roots_4 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

theorem low_4 : Lower dom_4 roots_4 goal_4 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0xffffffff
def goal_5 : Nat := 0xfeeefaa8
def roots_5 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_5
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (2, 3), (2, 18), (4, 5), (4, 12), (6, 7), (6, 14), (6, 22), (8, 9), (8, 12), (10, 11), (10, 14), (10, 26), (16, 17), (16, 18), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 8, 10, 10, 10, 16, 16, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [3, 5, 9, 17, 3, 18, 5, 12, 7, 14, 22, 9, 12, 11, 14, 26, 17, 18, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_5.map (· &&& dom_5)
def goalM : Nat := goal_5 &&& dom_5
def NN : Nat → Nat
  | 3 => 1
  | 4 => 6
  | 5 => 19
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x38e05052
  | 4, 0 => 0xa5105bb06714300d3c7caaf912161fe50e562d7c0523c5ca
  | 5, 0 => 0xd051f5079a4132f288a34107830aadb3755161bc64d48033579c5aa73a6b8d4132f633fb20ca757e1ac7d7cf18c41cbb18b8e630172f56661604e97e0ad7cab8074368e8061a7d51034963b1
  | 6, 0 => 0xd051f507ce00c9b9ac05225e5299e96d3a6b8d4130706e42206585ea
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa8a8a8a800000000555555550000000033333333000000000f0f0f0f0000000000ff00ff0000000000550055000000000000333300000000000000ff
  | 0, 1 => 0xfa00fa0000000000f0f0f0f000000000eeeeeeee00000000dddddddd00000000cccccccc00000000aaaaaaaa00000000aaaa888800000000aa88aa88
  | 0, 2 => 0xfffafffa00000000ffeeffee00000000ffccffcc00000000ffaaffaa00000000ffa8ffa800000000ff00ff0000000000fcfcfcfc00000000fafafafa
  | 0, 3 => 0xffffff0000000000fffffcfc00000000ffffcccc00000000ffffaaaa00000000ffffaaa000000000ffff111100000000ffff0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc4e0b4
  | 4, 0, 0 => 0x39b939aba9396a5c51cb42ee4e5a573272d4b89b96a5
  | 5, 0, 0 => 0xc49cb525b1272d4160624a291715945ca60624e5994185a8835f628e5a981872cc35c49cc5a9b1272d426c49cb51db98939aa6c5a4e5a9bb89396a6c49cb501b179396a6
  | 5, 0, 1 => 0x31272d466c41ee5a9b14941cb6
  | 6, 0, 0 => 0x31272d466e624e5a98189396a50624b511418939665c564e5a9b128396a6
  | 7, 0, 0 => 0x189396a5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 24
  | 4 => 29
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfffff0ff18cfe3f83f1f07ff1f07f00018cf0007ff
  | 0, 1 => 0x1c07c000e73ffffff000e73000000f000000000000
  | 0, 2 => 0xfcffcfe0ff3fe0ff30e0f80fe0f800e0f8001ce7f01c07cf
  | 0, 3 => 0xfff800ffe7f0ffe730ff000fff0000ff18c0ff0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x42153dad6a0b518ce63a83d0f057b0a04200018c6000153
  | 0, 1 => 0xb07a849c57c26fef7fdaf7b14ae73125295f252119202915
  | 0, 2 => 0xfdffdffffffffaffb5f5fbdff4fbd7f0fa84def7f3bd7fdf
  | 0, 3 => 0xfffeacfff7fbffe739ffad7fffad6eff94a8ff8428
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 24 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 24 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 31 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 31 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 31 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 31 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 3 => 3
  | 4 => 15
  | 5 => 23
  | 6 => 4
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0x67c7c04e4191492403fc0fa6
  | 4, 0 => 0xac05225e895739db701d4c4c4a3ffc5a419de0e53649f21e32bc99002fda874d2d070f792720edd8261b9e0a08a43bb3064edd46054298b804ed2e99
  | 5, 0 => 0xce00c9b9ac05225e81ea162e6b778c425e1d4aa8554c825e5299e96d48c00fe030706e422fe12a1b2efff7362d02a0a62637312d25e0cf6625303d37206585ea1b8a7ef11863781a148cee9c12fe2d5b08dabbe60241d3e100b965fd
  | 6, 0 => 0x554c825e25303d371b8a7ef10241d3e1
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x114480201
  | 4, 0 => 0x30008d101000c01000000000100000001000000030000000200080101000000020008d10100000001000851010000000300000002
  | 5, 0 => 0x20000000100000003000000010000000000000000000000000008d100000000010000000100000002000000010000000100000003000000010000000100000000000000010000000100000001
  | 6, 0 => 0x3000000010000000300000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 3 => checkCutEntry dom_4 roots_4 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_16 : ∀ i, 16 ≤ i → i < 19 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 16 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 19 → Z 5 i = true := range_split z5_0 (range_split z5_8 (z5_16))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := z6_0
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

def dom_6 : Nat := 0xff00000000
def goal_6 : Nat := 0xe800000000
def roots_6 : List Nat := [0xaa00000000, 0xcc00000000, 0xf000000000]

namespace S_6
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (34, 35), (34, 38), (36, 37), (36, 38)]
def r1sG : List Nat := [33, 33, 34, 34, 36, 36]
def r2sG : List Nat := [35, 37, 35, 38, 37, 38]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_6.map (· &&& dom_6)
def goalM : Nat := goal_6 &&& dom_6
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x7cdd6334
  | 3, 0 => 0x7cdd6334
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000cc00000000000000aa00000000
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_7 : Nat := 0xff000000ff
def goal_7 : Nat := 0xe8000000a8
def roots_7 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_6

def dom_8 : Nat := 0xf000f00000000
def goal_8 : Nat := 0xe000800000000
def roots_8 : List Nat := [0xa000a00000000, 0xc000c00000000, 0xf000000000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 4 :=
  lower_iso [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_9 : Nat := 0xff00ff00000000
def goal_9 : Nat := 0xee00e800000000
def roots_9 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000000000, 33, 37)] (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0xf000f
def goal_10 : Nat := 0xe0008
def roots_10 : List Nat := [0xa000a, 0xc000c, 0xf0000]

theorem low_10 : Lower dom_10 roots_10 goal_10 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_11 : Nat := 0xff00ff00ff00ff
def goal_11 : Nat := 0xee00e800ee00a8
def roots_11 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

namespace S_11
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 17), (2, 3), (2, 18), (4, 5), (6, 7), (6, 22), (6, 38), (16, 17), (16, 18), (20, 21), (20, 22), (33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (34, 50), (36, 37), (36, 38), (48, 49), (48, 50), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 4, 6, 6, 6, 16, 16, 20, 20, 33, 33, 33, 34, 34, 34, 36, 36, 48, 48, 52, 52]
def r2sG : List Nat := [3, 5, 17, 3, 18, 5, 7, 22, 38, 17, 18, 21, 22, 35, 37, 49, 35, 38, 50, 37, 38, 49, 50, 53, 54]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_11.map (· &&& dom_11)
def goalM : Nat := goal_11 &&& dom_11
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 6
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x5b89fc99
  | 4, 0 => 0xf154aa00628184da28206f83
  | 5, 0 => 0xa4f836c38a64578150eeb30f2f17f7c427ca5be017bdcd44
  | 6, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf800f800f800f800f000f000f000f000ee00ee00ee00ee00cc00cc00cc00cc00aa00aa00aa00aa008800880088008800550055005500550033003300330033
  | 0, 1 => 0xff00ff0000000000ff008800ff008800ff000000ff0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa9654
  | 4, 0, 0 => 0xa87435a96435a86525
  | 5, 0, 0 => 0xa864150a86305a865436a864326a864316a864306
  | 6, 0, 0 => 0xa86435
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xcc0cf066067800fc3be0701d80070038000003fe3ff1f8fe27
  | 0, 1 => 0x7ff8003c03c01e01e00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xcdbcf5e69678bffffff5735d954f5378048126ac2b20a8ca26
  | 0, 1 => 0x7ff8403cb7dbbe49e94
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 25 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 25 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 11 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 11 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 11 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 11 then wireAt i else 0
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
  | 4 => 7
  | 5 => 30
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xb50fb2d6af3d516b90f7f02b47baa070411ca7c6385234e716dc37a0
  | 5, 0 => 0xfd05eeb0e96532dbe0d44139dcfd0cfed6fb56ced4743512c9d5353ac2948086adf99dfb92c817469034ec5b88ca29be804151d27f9c59f37c735e0c771382077517405673ea86206c8e686a6b85db7469ad9211514fa09147baa070464257373daee4bc35e49768290a2e9c20b49e3815dbc31515521a2e
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x3000008000010000000000100000000002
  | 5, 0 => 0xc0000000000c00001000000000020000000000100000400003000000000000000000000100000400001000004000010000040000000000c0000300000000000000000000010000000000000000000003
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_7 roots_7 5 s ws hint
  | 1 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 2 => checkCutEntry dom_9 roots_9 5 s ws hint
  | 3 => checkCutEntry dom_10 roots_10 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_11 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := z5_0
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

def dom_12 : Nat := 0xffff0000ffff
def goal_12 : Nat := 0xfae80000faa8
def roots_12 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 7 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0x333300000000
def goal_13 : Nat := 0x322000000000
def roots_13 : List Nat := [0x222200000000, 0x303000000000, 0x330000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_14 : Nat := 0x3333333300000000
def goal_14 : Nat := 0x3222322000000000
def roots_14 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000000000000, 33, 49)] (by decide +kernel) (by decide +kernel) low_13

def dom_15 : Nat := 0xf0f0f0f00000000
def goal_15 : Nat := 0xe0e0a0800000000
def roots_15 : List Nat := [0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14

def dom_16 : Nat := 0xffff00000000
def goal_16 : Nat := 0xfae800000000
def roots_16 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9

def dom_17 : Nat := 0x5555555500000000
def goal_17 : Nat := 0x5444504000000000
def roots_17 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

namespace S_17
def pairsG : List (Nat × Nat) := [(34, 38), (34, 50), (36, 38), (36, 44), (40, 44), (42, 46), (42, 58), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [34, 34, 36, 36, 40, 42, 42, 48, 52, 52, 56, 56]
def r2sG : List Nat := [38, 50, 38, 44, 44, 46, 58, 50, 54, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_17.map (· &&& dom_17)
def goalM : Nat := goal_17 &&& dom_17
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_17 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_17 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_17 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_17 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_17 roots_17 goal_17 4 := by
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

theorem low_17 : Lower dom_17 roots_17 goal_17 4 := S_17.noCircuit

def dom_18 : Nat := 0xffffffff00000000
def goal_18 : Nat := 0xfeeefae800000000
def roots_18 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

namespace S_18
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 50), (36, 37), (36, 38), (36, 44), (40, 41), (40, 44), (42, 43), (42, 46), (42, 58), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 33, 34, 34, 34, 36, 36, 36, 40, 40, 42, 42, 42, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [35, 37, 41, 49, 35, 38, 50, 37, 38, 44, 41, 44, 43, 46, 58, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_18.map (· &&& dom_18)
def goalM : Nat := goal_18 &&& dom_18
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x7523d75b
  | 6, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000ff00ff0000000000f0f0f0f000000000cccccccc00000000aaaaaaaa000000005555555500000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x58d05
  | 6, 0, 0 => 0x58d15
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3fc000707c001c070001c1c000007fffff0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3fe024787e049c574495c5c494a4fed6b60
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 23 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 23 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 6 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
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
  | 4 => 1
  | 5 => 19
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x5f5ce351
  | 5, 0 => 0xccf2db85b740b46e8f19090286cfb07d6b1890e0608578e95fcdfb9d5f5ce351531e2a99527e04584fbea8484995ef473c415933358964b82f5e14ef273b926c1dcf210308666be9059706fd
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x2000000000000000080000100000c00001000000000020000000000000001000003000000000000000040000000000000002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_14 roots_14 5 s ws hint
  | 1 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 2 => checkCutEntry dom_9 roots_9 5 s ws hint
  | 3 => checkCutEntry dom_16 roots_16 5 s ws hint
  | 4 => checkCutEntry dom_17 roots_17 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_18 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_18 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
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
  scr dom_18 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_18 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_18 roots_18 goal_18 7 := by
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

theorem low_18 : Lower dom_18 roots_18 goal_18 7 := S_18.noCircuit

def dom_19 : Nat := 0x5555555555555555
def goal_19 : Nat := 0x5444504054445000
def roots_19 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555555500000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_17

def dom_20 : Nat := 0xffffffffffffffff
def goal_20 : Nat := 0xfeeefae8feeefaa8
def roots_20 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_20
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (2, 3), (2, 18), (4, 5), (4, 12), (6, 7), (6, 14), (6, 22), (6, 38), (8, 9), (8, 12), (10, 11), (10, 14), (10, 26), (16, 17), (16, 18), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 50), (36, 37), (36, 38), (36, 44), (40, 41), (40, 44), (42, 43), (42, 46), (42, 58), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 6, 6, 6, 6, 8, 8, 10, 10, 10, 16, 16, 20, 20, 20, 24, 24, 24, 33, 33, 33, 33, 34, 34, 34, 36, 36, 36, 40, 40, 42, 42, 42, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 5, 9, 17, 3, 18, 5, 12, 7, 14, 22, 38, 9, 12, 11, 14, 26, 17, 18, 21, 22, 28, 25, 26, 28, 35, 37, 41, 49, 35, 38, 50, 37, 38, 44, 41, 44, 43, 46, 58, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_20.map (· &&& dom_20)
def goalM : Nat := goal_20 &&& dom_20
def NN : Nat → Nat
  | 3 => 32
  | 4 => 142
  | 5 => 340
  | 6 => 458
  | 7 => 197
  | 8 => 15
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xdda6776bbf91adddbacbdd4fb5f22c1fada7aa44a5a119b89bc1db5d8d99699c80b24cd47b9443577900c977755b87817375dc897186e61f61bab7dc56c5765755de4b3f5561b01f5320197d49b21a5d444352dc41130e13335a380b3100ea652fc498d12efd9bc02e8fdfe6284487ba1eea447d187c2ed308f2c898003064a1
  | 4, 0 => 0x48ccd5af481739c6464f954845b3d36f458f6165412baef13fcc02043c3db06f3b2955f43ad333c239d88b313879e5e8371fed6c368b7d15364e50f2347da62733940cfb316a3038303b30572efd64752e154e2f2bd8dd942b69a3682b58fbd72b4dd05d28a64a0a288b1a8026c3cb2c26a687d42687a58222aa74a6206b916e206336c11e3d3b311d0fcc0f1d09b8221bd58e201b63203c19e09ee6179c52af175ac4a1170aa30816e6787916b33f7113ea8fa2117e5ae40fbbb8c20ead82770e16f6270c7723a00b6b91df0b3f3c000a9b192409af0d0205a088bc04433f4103c42e89029f5e6202842db402424c8b01ea00c1019394c8005581a8000ae42c
  | 4, 1 => 0xa679458ea1c87caba1b0c6f49fb3a90a99470c8497e3ae25976407569628a4fb9619bd7994eec91a94e714e1944d0a1690d7d1888d09c92d8a27f3cf8820216787fb4671848eb8598242fd0d81787b1c7f7fb1147ee9d5ad7dcf50ff7db3c8a77cdef3cc7ab8a39b79c896d27885cfe077f4aee877bd200a77a31a93778b8c0474a62d25738b8b947092371d6f36a2686e761a876e2040346d2353c469ff4ad4693e2613685a65e96825804a669e0d846684bd506631093c660aa3de6469e55963cd794663547887632949fa61fab41d61a503fb5aea4c805a45054c5a2c2dea577bd2cf56f87dbf5665e28755efcf3f5578037751333bcc4c78363e4bd1c7de
  | 4, 2 => 0xfd892266f962e301eae7091ce6cdbad4dfe0271ed4c03d18d4baa1a7d07f96abd01e219eb9ea2164b60244b9b3b77c11a87bafc3a73713e8
  | 5, 0 => 0x18ca129918437bda1803399616fa0bbd167df75e1643e4481638cc531597077e14a09ea0146c010b134ffbfc12d8702812888ccd1283aafd11fd45e311fa007f11cfe2b61121288810c073e110b21ff71092374f108b31050fe6da180fbe042b0e2cfc7d0e29400b0ddb4eda0dcf3e3e0d79cb890d7724750d7461f60d392fc60d31bdf20cc2220b0c6f315c09fdc56609f40891097492f7096c602d09527ede0922466509115a4608bab40108b5236d0879eb6f064b112505fc2df405dff3fa05d2edac058a52e7056b757e0569edca046cdf0c043b49460422db74037f7c4a0338386f03353284020e17cb01965c48010bb0000106a6aa004e76c5000bd3c9
  | 5, 1 => 0x369e232b36040f8b35f0746335c6e9dd3597517034bd2f6f332d048932adfe26322ce69132160a3c318b93d1315c08073144b1fb30ef49ec3058609b2ff0424a2e490dac2dacfc532da400082d2638102bc78db22ba9cb6f2b5203712aa7cf972a7011e82a4753512a2e62ab2a0bb9492984d1c329126c59290c819b28d35366286491bc27e1f33026bd6a98264c4816260c591a2608d42924e0c8d624a14e02236836cc2307642b22e826d522e782b622c8772f22072f0121e8c03621d2dc4921a0038b21632ca02075da641fca8cda1fadcda71fa2c65c1f4785601ed15b311e3256f91d8dc7b51bd606951b8901f21b533fa21ae1c6821ac9fde719fbc7f6
  | 5, 2 => 0x55d62f0855b922f05503ba8754a110165483f169544e9a745353c3c752f9f01252d30e32527c9acb5186e6ad51139f0d50fca45650c5dda150a9f403506eb2235042a31c4fbb048c4faa8c684f7c60744e87686e4e6ee5554e29c7d14dc8f4d44d8f3ad14d6ed5974d33af8f4ce6565e4c4b52524beee6fc4be4306f4b0b9f9b4b04cebf4ade2a5c4ad28be94aa4a4954a305d0d488375944662210f4453eec3435d07ff434bad464335b829426fe94d4208c76a416a1ca140fc1fe840a7298d408614eb401c1c233f83721f3efbc18d3e62bd113ddc03723d85d96b3ce0a2883c7ac0fa3c3f23c43b2fe8e93af5ae8e39a3fc2a38e63583385f7a1c383678b8
  | 5, 3 => 0x78180ca477a756e8774be0377729fef17642075e7576699e754a7af074f742c772c825e5725681b5724d2f3171e347c371a3faaf7134af5a712f5ee170466fca701596636f7fb5426e9d24c26c6d7d316c6c49876bb965ee6b0981336ae09dd56a93dd8b69b50a6968d124ca6854fbaf66fdde0f66a2a5e665f46a9b64a08d0e6404f01662fba04a629d2282625b6a08617d4d7e611b693360813c40605a49426053a152604a9ea45f94b6535f7599dc5f7026165dd2ccff5da6c3e35d43a14f5d34e16f5d21c4245d1370125a8d3ad45a2551045a0287bc597002395967c8f75915f40d58eadbde57f003935746b35a5745f8dc56bf109b569786905634acd0
  | 5, 4 => 0xc62d7540c61fdb14c54f1ca7c4684e1fc1148968beb5652bbd3b9c5ebbb9aa50b7a15aa5b67e44c7b6130e4eb6017894b1c52ab8af7c72ccae3211d5ae10f213aba1afbcab04e8c7a9575e6ba955f470a82594e1a72e32c1a72550e9a5d2aec5a4e24862a22de227a12ea434a019841a9cd60e619c855c9b9c4d926b96db332596d07fa8960620a595fdcd9a93364a859297f864919d26838e01f5168d1d9b418ce3377d89cd889b8854d6f987ae630587861b0e872b4b26872255ff8319ef2882b9b69c8212fe4a81fd43e381ee3ff2817874d37f376ade7f1ec19d7df42acb7d6bb3817c3b3a587c306b6d7bfcc3507bc66d5d7b98f5687a6158be7a06cfbc
  | 5, 5 => 0xfa2a5962f89a03eff3b38055f28c88fbec96b17ae7b13259e010ac74df3a652bdefe316fdcf85272da6910aed9ebdae7d67d0a21cfcdc8b5cc66ce56c96caa6cc9440b4dc918cab1c8502d97c7e6e660
  | 6, 0 => 0x160ed30d15f4eac915eeff3915c3143a15a80236155ed0bb1499cfe5145d9e29140adaec13ea83c213e1376313d1f75e133ea38d133218de12b1100c12324797118eca21117a220611408e9a1106ad5710daf28b0ff651070f8e38f60f190a620f115ba20e1ee4940ddf711a0db432850d86abda0d0d7a9a0cf439bf0c8aad3c0ba77e000b2c8ce60af23e1b0ae653d709ff43110919997808bc19b1086bbfd207f1b6d607f0433f07a7264906ad6f4d06a3cff506552c8005a9e53f05827359053da15d048dacd7047f625d04321371042d77d503c715c60372fa4e025216e80249a99b023d494001c9b31e01a5e6740198403d012a58400096401f003e83f9
  | 6, 1 => 0x29a4bf202992b932297c99f82912a74928ecb0ec28c8048a282426c9281f075127d2a877275dc420275a769026b3685326af69af26ac92fa2686b911263aeadb24e53f922495ac0c246d800b244f823f243e5010241577b923bb3be3226df44b224d3e3d21bee72e213d50c520eebdc420d561792071473a2032e0911fd27f2f1e0aec781ddd2b031dd9e72b1d826c881d19149d1d07cbc61c8c79111bf5be811be2e8291bd1fa481b3bd7731b24771a1b16f5ed1aa911841aa1953a1a0692b219ff9c8019ba301a19affd6f1966b800194727b518ef4baf18714ed1181c0a6c181ac3f417b77a52172decb916987722165a143316446b9c163cc66616278eac
  | 6, 2 => 0x421dba1942115aa64208a2ce414a8c1f3fc11baf3f3ce45f3eece4723e8c263a3dd0ef663d7dc3333c6b32503bd82cc93bb1f7013ac6e89c39ddbebc39ab24c43996a260392d295a38e8b0de382d39c93819736d374d282d3739958935cfc0d835bf01b535999cd9358ef804347c735e343eb057343a84db33e6b2b633c3d97933c08bc93360306f3301de5532fa2f9532e16b89326bf53f3228448c31869e0c30d2ce7b30b973d6306aaa7f304d48782f954dd02f34e7c52f2d39052f15a0e52dd75a262d44ea432ca10ba02c83d6252c42325c2bc2b7902bb5fd6b2b52c4ba2b4ef7cf2b27b74c2afe09d52af68de12ad9fd9b2a35a5cd2a1fc85a2a079cb6
  | 6, 3 => 0x5970e32e593f5843592cf52959254669587ff1fd585f3acc584579ff5802414f57a1bfdd578a39a256d3b3db56503afa56488c3a5592189f54ef689a53dbb72c52e2321e527d165f51954e1e519348e05188bd31503999f04f10fdde4ddb76074dc656d84d7ecab74d3f45bb4cde6d854ca859dc4c6601af4bf837324b093b3e4ae59fe04aca3bcf4aabf4e84aa02b774a932f4e4a43210e4a4249ab4a3f5f3c4a0e701449ae952049a85ad5498effba49894780491e4f5448da76e748d1f62d48c32bdf48b2faee4828752047f536de4781f3344694616246361230462000d245afa45845a9a14045a7f598446729e643c469ce439f8000424acd3742454fb9
  | 6, 4 => 0x75282299751532dd74b5d9f47481ccfa7337da1f7301de5f722b1a8271b731cf7179360f715bc4407099e98f6f39211a6f2972ce6ea4ed216e8cbcc66df7e42c6cdea9ec6c3bd30b6aafcc206a95be0b6a53b3216a41599e6a08bb0569849e93693b519b68959ecc688d4903682d62f068239c7567f57eec67f05e3367eee67a67dc1aed66d1c7a96684dce865f74f0265e88a3d65c0029c64a0c73f6468b3576461049764512d1c643a3fff64179578625d86976240770e6142379a5ff8bcbf5ed985675e5c41985df837b25db6ae185d71535d5d062afa5caa48d35c97debb5bf13ab45bb03c075b2fe5715b26580e5afabf435a8d4a5259c0f58959a0c2fc
  | 6, 5 => 0x9daae7359d92fd0c9c96775d9aca79e39ab91a00998cea0d996e299c9847a6bd97a00225977d7102972d561a96ced852937619ce936053589323975e90de8f3690a6fd2a90623c408fdbed7a8f6057d08e7b64d08db59d498daba1d48cfa91f68c73f36789b019e5881775a687f036a38784e625871e3ea4865ca3e485c40c768455b1498426677583629097831dfd40827963fa8222c68f817ebe358160c9fc8101e0aa8082f99c8069eaef7fff2add7fa0b5d97ea020fc7ce9266b7cb8d26e7c0014947bf8b5337b5baecf7a05242f79e85dd379bb6d1e79b690e77961f7277920d8f37800865577abf413774e72ca76e1a5f0760a28d075a7ec44755c9246
  | 6, 6 => 0xe0704e26dfb2a488de0091c7dba68411db59748fd998007fd9719f58d735f252d615987fd57db6c6d26dda29d26d319fd1399e4dd02d5d1bcf527d16cbca57dbcb239f89cad25745caa6b7f9c996b3b6c74c4e87c743034ac73369bbc66d8871c63e6ab8c63e4d23c637c9f1c20d3382c1436d07c111313ec0e08b57bf1723febe0cd55bbac1507dbab9a1bdbaa65613b91d4ce9b84d5911b800b3d7b68b3589b4ca072db3c1e194b217ac16b2118fd6b0d3c397b0619e49ad7f4391ad64f2d1ab5d2e2fab225dd6aa2ce68ba9c4420fa98e4816a94c64a9a93be014a8e78fc4a6e98352a63c52c1a5e47aa0a3744415a2cd8bc3a275f6c89f241f2f9e48e6c4
  | 6, 7 => 0xfc6afe7df89a03eff6535463f6281cb5f48bd63cf250bba1eea98865eb93c63be9681333e1151f08
  | 7, 0 => 0x38b8c6ed38ad846e387c221636f4981f35f834e9359f67e7358e7c1334746a9f32ba82ac3264f1943129ad3f2fc976f62f62b4552d988a382d90db782d6df75a2ba0a43a2b89112d2b81626d2acd7a982a6cf07128ac56fe28a4a83e2774c4602752ae7526bb2fef2429651523038dd422c735132219ec0a2064873a1fb72b911f3d31db1edad9521ec21db31e08e1531c27ad6d1c1ffead1be563841bde45011b8548e619b1d44816ac3b501415063f14121a0c1308cd7712baa67712b8884a123247971187183a0f8b2a5f0f6b9a140f60b9f30e7dd0190e783ebe0d61f2fb0c2cfbb60c22507d0c167f100acf09dd06ecbabd06b07a0306291d8303e36454
  | 7, 1 => 0x7dfd47397bf0d33379e15a2879613c9777d135d06f6c29a26c4b6e046bed6d236b46b4d16a7ff66868b561d0673394256554bad163669d9560b58bf55d7bf2db5d1d08615c50bd215c0095e65af03eb05a3c07d75647df285640306854ed1c7554b47b98531915d1523dc211514aca6d51099cc650c4b4ed4f943bc44ec05ebd4e1db72a4c4c79c44b13daf94b0c2c3949e8d48649e125c6499b08ca4980ebae48b85b5d48b0ac9d46e149a2434ac03242bf286341d9fb7841d622d341a4b5d6413f306a40ccbe134079af633f49363a3e4ce77f3e38a7a13d6d0b963cedcf813c9d75a23bf167e33afd7b253a8b9b213a8b1a653a305add396f572d39500340
  | 7, 2 => 0xed71b5aee575a6eae4191cbbe1b94d76e12fee6ae1283faada802b72da4c5f43d958a3e4d87f9952d697c1d4d468faf0d0e4e8e0d0dd3a20cd856bc9c7554d2ec5e58a67c5690328c1043454bf09aa00bf01fb40beb2f988bde1cfb5baa8a17cba477786b59a84ddb4d0d4a4b37ef559b253eee6b031ca64af95e2ffabbe6e52ab681b8ea98e4816a98c5b5da8e78fc4a8d9852aa8d69abba5103ec29e8d17b19e58572e9bfcd792996c23f4989a692798411d819710a4589603a49895a996be9351acbb928df7689117715e8f6e24048f3423d38ebf00228d5eaaf98ce77a638bbc73f08a81f0ca89211e6a8492c7cd83f048fb83d9bb2c8029ed027fe35f82
  | 7, 3 => 0xf6657479f5a8ee32f1c31697eef3064dee22ff53
  | 8, 0 => 0xf33b5fd08a7994f87f4590c97e1a8a567cea112d76f0de3361ca40085fbac6fd5cde0cce5059633d1561a43a0e85c3d30e7e151305169eb001bed059
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000333300000f0f00005f5f00000f0f00000fff00000f0f00000f0f000000ff000000ff000000ff000000aa00000055000000550000003300000033
  | 0, 1 => 0xf000f000f000f000500050005000500030003000300030000ffff0000ffff000077770000777700005f5f00005f5f000055550000555500003f3f00003f3f
  | 0, 2 => 0xff00ff00ff00ff00fa00fa00fa00fa0077007700770077005f005f005f005f0055005500550055005500550055000000330033003300330011001100110011
  | 0, 3 => 0xf0a0f0a0f0a0f0a0e0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0707070707070707050505050505050503030303030303030101010101010101
  | 0, 4 => 0x22222222222222221515151515151515131313131313131311111111111111110f0f0f0f0f0f0f0f0f0f0f000f0f0f000f0f0a0a0f0f0a0a0f0c0f0c0f0c0f0c
  | 0, 5 => 0x55555500555555005550555055505550554455445544554454545454545454545050505050505050444444444444444433333333333333333330333033303330
  | 0, 6 => 0xa8a8a8a8a8a8a8a8a5a5a5a5a5a5a5a5a0a0a0a0a0a0a0a099999999999999998888888888888888555555555555555555555555555500005555555555005500
  | 0, 7 => 0xaaaaaaffaaaaaaffaaaaaaaaaaaaaaaaaaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa88aa88aa88aa00
  | 0, 8 => 0xcc88cc88cc88cc88cc80cc80cc80cc80c8c8c8c8c8c8c8c8c3c3c3c3c3c3c3c3c0c0c0c0c0c0c0c0ababababababababaaaabbbbaaaabbbbaaaaafafaaaaafaf
  | 0, 9 => 0xcccccc00cccccc00ccccc8c8ccccc8c8ccccc8c8cccc8888ccccc0c0ccccc0c0ccccc0c0ccccc000ccccc0c0cccc8080cccc8888cccc8888ccc0ccc0ccc0ccc0
  | 0, 10 => 0xcccccccccccc8888cccccccccccc8080cccccccccccc0000cccccccccc88cc88cccccccccc80cc80cccccccccc00cc00cccccccc88888888cccccccc0c0c0c0c
  | 0, 11 => 0xcececececececececdcdcdcdcdcdcdcdccffccffcc33cc33ccccddddccccddddcccccdcdcccccdcdcccccccccccccccccccccccccccccc88cccccccccccccc00
  | 0, 12 => 0xececececa8a8a8a8eaeaeaeaeaeaeaeaeaeaeaeaea00ea00e8e8e8e8e8e8e8e8e0e0e0e0e0e0e0e0dddddddddddddddddddddddddddd0000dddddddddd00dd00
  | 0, 13 => 0xeecceecceeccaa88eecceeccee88ee88ececececececececececececececa8a8ececececececa0a0ecececececec0000ecececececa0eca0ececececec00ec00
  | 0, 14 => 0xeeeee0e0eeeee000eeeee0e0eeeea0a0eeeecccceeee8888eeeeaa88eeeeaa88eeee8888eeee8888eeee0000eeee0000eeeceeeceeeceeeceee0eee0eee0eee0
  | 0, 15 => 0xeeeeeeeeee00ee00eeeeeecceeeeeecceeeeeecceeeeaa88eeeeee00eeeeee00eeeeececeeeeececeeeeececeeeeeccceeeeeaeaeeeeeaaaeeeee0e0eeeee0e0
  | 1, 0 => 0xf0c0f0c0f080f080f0a0f0a0f0a0f0a0f080f080f080f080eeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaeeeeeeeeeeee8888eeeeeeeeeeee0000eeeeeeeeeeaaeeaa
  | 1, 1 => 0xf0f0f0f0a0a0a0a0f0f0f000f0f0f000f0f0a0a0f0f0a0a0f0f08080f0f08080f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0a0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f000
  | 1, 2 => 0xf0f0f0fff0f0f0fff0f0f0f0f0f0f0f0f0f0f0f0f0f0f000f0f0f0f0f0f0a0a0f0f0f0f0f0f08080f0f0f0f0f0f00000f0f0f0f0f0a0f0a0f0f0f0f0f000f000
  | 1, 3 => 0xf8f8f8f8f8a8f8a8f8f8f8f8f888f888f8f8f8f8f800f800f8f8f8f8a8a8a8a8f5f5f5f5f5f5f5f5f0f3f0f3f0f3f0f3f0f0f5f5f0f0f5f5f0f0f3f3f0f0f3f3
  | 1, 4 => 0xfac8fac8fac8fa00fac8fac8fa00fa00faa8faa8faa8faa8faa0faa0faa0faa0fa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f8f8f8f8f88888f8f8f8f8f8f80000
  | 1, 5 => 0xfafafa00fafafa00fafaf8f8fafaf8f8faf8faf8faf8faf8faf8faf8faf8faf0faf8faf8faa8faa8faeafaeafaeafaaafaeafaeafaaafaaafac8fac8fac8fac8
  | 1, 6 => 0xfca8fca8fca8fca8fafafafafafafafafafafafafafaaaaafafafafafafa0000fafafafafaaafaaafafafafafaa0faa0fafafafafa00fa00fafafaf0fafafaf0
  | 1, 7 => 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000fcfcfcfcfc00fc00fcfcfcfca8a8a8a8fcfcfc00fcfcfc00fcfcf8f8fcfcf8f8fcfca8a8fcfca8a8fcecfcecfcecfcec
  | 1, 8 => 0xfefefefefefeaaaafefefefefefe0000fefefefefeaafeaafefefefefe00fe00fefef8f8fefef8f8fefe0000fefe0000feecfeecfeecfeecfe00fe00fe00fe00
  | 1, 9 => 0xff11ff11ff11ff11ff0cff0cff0cff0cff05ff05ff05ff05ff01ff01ff01ff01ff00ff55ff00ff55ff00ff00ff00ff00ff00fa00ff00fa00fefefefefefefefe
  | 1, 10 => 0xffaaf0a0ffaaf0a0ffa8ffa8ffa8ffa8ffa5ffa5ffa5ffa5ffa0ffa0ffa0ffa0ff88ff88ff88ff88ff55ff55ff55ff55ff55ff55ff55ff00ff22ff22ff22ff22
  | 1, 11 => 0xffccaa88ffccaa88ffc0ffc0ffc0ffc0ffc0ffc0ffc00000ffc0ffc0aa80aa80ffaaffaaffaaffaaffaaffa0ffaaffa0ffaaffa0ffaaff00ffaaff88ffaaff88
  | 1, 12 => 0xffccffccffcc0000ffccffccff88ff88ffccffccff0cff0cffccffccaa88aa88ffccffc0ffccff80ffccffc0ffccff00ffccff88ffccff88ffccf0c0ffccf0c0
  | 1, 13 => 0xffecffecffecffecffecffecffecff00ffecffecffa8ffa8ffeaffeaffeaffeaffccffccffccffccffccffccffccff88ffccffccffccff80ffccffccffccff00
  | 1, 14 => 0xfff0ccc0fff0ccc0fff0aaa0fff0aaa0ffeeffeeffeeffeeffeeffeeffeeffaaffeeffeeffee0000ffeeffeeffaaffaaffeeff88ffeeff88ffee0000ffee0000
  | 1, 15 => 0xfffafffafffaaaaafffafffafffa0000fff8fff8fff8fff8fff0fff0fff0fff0fff0fff0fff0ff00fff0fff0fff00000fff0fff0ffa0ffa0fff0fff0aaa0aaa0
  | 2, 0 => 0xffff000fffff000fffff0000ffff0000fffefffefffefffefffcfffcfffcfffcfffcfffcfffcfff0fffcfffcfffc0000fffcfffcfff8fff8fffafffafffafffa
  | 2, 1 => 0xffff5555ffff5555ffff5555ff005500ffff3330ffff3330ffff2222ffff2222ffff1111ffff1111ffff0303ffff0303ffff0033ffff0033ffff0011ffff0011
  | 2, 2 => 0xffffccccaaaa8888ffffc0c0ffffc0c0ffffaaaaffffaaaaffffaaa0ffffaaa0ffffaa88ffffaa88ffffa8a8ffffa8a8ffffa0a0ffffa0a0ffff8888ffff8888
  | 2, 3 => 0xffffeeeeffffeeeeffffeeeeffffeeaaffffeeeeffffee00ffffececffffececffffccccffffccccffffccccffffcc00ffffccccffff8888ffffccccff00cc00
  | 2, 4 => 0xfffff8f8ffffa8a8fffff0f0fffff0f0fffff0f0fffff0a0fffff0f0fffff000fffff0f0ffffa0a0fffff0f0ff00f000fffff0f0aaaaa0a0fffff080fffff080
  | 2, 5 => 0xfffffafafffffafafffffafafffffaaafffffafafffffa00fffffafaffffaaaafffffafaffaafaaafffff8f8fffff8f8fffff8f8fffff888fffff8f8fffff800
  | 2, 6 => 0xffffffa0ffffffa0ffffff88ffffff88ffffff00ffffff00fffffcfcfffffcfcfffffcfcfffffc00fffffcfcffffececfffffcfcffffa8a8fffffcfcaaaaa8a8
  | 2, 7 => 0xfffffff0ffffaaa0ffffffeeffffffeeffffffccffffffccffffffccffffff88ffffffccffffaa88ffffffccaaaaaa88ffffffc0ffffffc0ffffffaaffffffaa
  | 2, 8 => 0xffffffff0f0f0f0fffffffff05050505ffffffff03030303ffffffff00330033ffffffff00003333ffffffff00000000fffffffcfffffffcfffffff0fffffff0
  | 2, 9 => 0xffffffffff88ff88ffffffffff05ff05ffffffffff00ff00fffffffffaa0faa0ffffffffeeee8888ffffffffaaaaaaaaffffffff33333333ffffffff11111111
  | 2, 10 => 0xffffffffffffa0a0ffffffffffff8888ffffffffffff0000ffffffffffaaffaaffffffffffaaffa0ffffffffffaaff88ffffffffffa8ffa8ffffffffffa0ffa0
  | 2, 11 => 0xffffffffffffffaaffffffffffffff00ffffffffffffaaaaffffffffffffaa88ffffffffffffa8a8
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x75a58ee3e489b992c844a13c58684483405525a491b2944844893292084483329667b4833d1585a489bad2c804963292c7b4833995a844833296c6c494b292c844a641982b64833ad5a8048336d565a4
  | 3, 0, 1 => 0x8ab29207b4933a1545a48ab292c7d493b2944844923897e3e4a841982b64832fd4e3e49532926844923297e79489b292c83483359665a48ab292c7548340d545a4652d8ec5a4833b56c5a49332942844
  | 4, 0, 0 => 0x8cc559496422c5594962b8f1685356fa5908b0669a59023e5833a154962d2b292c772d0f964cca4921066b428832986845833296c6d28ad3626eb4b211646db652d8b4b0675a58d23e5aac19acb62d2c1994bf5e19960ceb4b1747cb2371a58b43e5
  | 4, 0, 1 => 0x883292c8440ac1994b32d0f1668ca491307cb3265258943e5933a16c5a1f2c19949f2d0f9658ca4b16878b066d244b43e5a5b292c8439ac419496492116851575a58f8b42833bd6c465ad45594963dad0a0ceb5bad964d0675af47cb4278a5908735
  | 4, 0, 2 => 0x83351625a1f2d0a20ca45a1160ceb59a5908b26743297e3e593329244e1f2c1a06882d0f960ceb5facc7cb06732a52c5a5aac4d9496422c19dc962d0f960cf86dad8b4b42833556c5a5a9c19b4b62d2d099496421d160cd6481687cb0674258da3e5
  | 4, 0, 3 => 0x833f1b6b32d2c19de96298f960ce8451687cb06732d8b43558336d225a1eaca594962d0f960ce85fad87cb0676a58da3e591b292c7b1f2c19d6ad290f9694ca51210e4b06652712c84592b6d94b32d2c1994b62a8dd62b067525908b246525908335
  | 4, 0, 4 => 0x83329665a1bac4994902d0f962b0675a5900b2669a48b43e589bad2c521f2c9194bf258f960cd4591687cb42833056ca45833296c692d2c1994b63699d646ca4b1347cb0665258de3e597b29245a1e2d6a2aca4b1f960cf44b16870b42933ad763e5
  | 4, 0, 5 => 0x94329445a1f2c1994b63596960cca569547cb0675a58d03e58336d2c551cac8d6ca32d0f9685066b2fcccb5a83329748458336d225a1d2c41949642209622e94b1687cb42883c52c84591b29445a1f2d0a0cb6529696aaca5f9e07cb066a2d8b4535
  | 4, 0, 6 => 0x923652c5a1f2c19d6bf588f96450675afc7cb066a2d9685a5932d1465a1f2d5624ca4b21168515652fcf0b1165258ae3e5883292c8f422c41949648211633156525906b5b8336d605a5933a1105a1f2c1994b1368f9626e64b1687cb56953292c845
  | 4, 0, 7 => 0x833bd2c521f2c19d6c54b0f9622e64b1687cb066b244b43e5aac19b6ad2d2c91d6bf2d0f9626ca4b1547cb06652fd6c835933298c5a1f2c194c962d0f9694ca4b210e6b0675a59003959234d2c5a1f2d460cd65b169648ca4b1e87cb4d6525908735
  | 4, 0, 8 => 0x20cca5e2d908b429ab817e3e500499d0bf1f250a20ca6418d60cef4b1a07cb23652d9085a5923892c5a1f2c99948d2b8f9594963b1687cb067325908395933296a842d2c9d94962d0f96a1065b290b4b0675a58dc3e5
  | 5, 0, 0 => 0x833ad2c521f045ab50665259084969346994962d0f9a85066dac12c5a69fc1994962d0f9a0cf96da44b43e6883292c932d0f9aab2669a58b43e6a74199a962d0f9a4adb65258b43e6a14560ce14b2118010675a58a4325833296a9642169a351565258b43e6003292c5a1f01940155883292c845
  | 5, 0, 1 => 0xa1419a8b642169a4cdb65248b43e6a143594962d0f9a490675a58b43e6a141994c8228d5aad10833292c846a6c19d68b2d0f9a0d0465258aa3e6aac199496388f9a9b0665259083768340994962d0f9a851065259080b6833ad2c521f08da4d06652ccb43e6adc1994b02d0f9a0cca5faf8863e6
  | 5, 0, 2 => 0x8336d94b34b169a7b0675a58a43e60052a0cca5121160cd34b240b43e6833296c5a2a8d5a850b65259083368ac1994964215da0ceb5ea58b43e6833996c962d0f9a85348ab292c846923292c842d0f98012365258b4325a1481a6962d0f9a0cca481687c3768cc199496420f9aa906652e12c3e6
  | 5, 0, 3 => 0x833a12c5a1f0e1ab31365258b43e69ec1994962c0f9a2b0665259005a6a1419aeca5b169a850675a58f83e69ac9994952d0f9a4cca5fa58aa3e6aac9994b62d0f1a4ceb65258aa3e60055a20ca4b21160cd34b23cb43e6833ad2c7f2d0f9a85065fa8c8a3e60050994964202d4012674258b43e5
  | 5, 0, 4 => 0xaac9994bf260f9a0cd44b168a43e6a14d5c0962d0f9a0cca5e2d8b43e6ac44994962d0f9a4cca5b2d0b43e6003292c5a1f0154014283328b4365833512c5a288f9a0cfe65258b43e6a1419b6af4b169a0cca4b234ae3e60049994921f0a5684c260258b43e691b292c5a1f0a5a0cca63a58b43e6
  | 5, 0, 5 => 0x833292c602d0f9a4cca491687c336aac1994ad2d0f9a84d34b210e43e691b292c5a1f0f1a3b0665258b43e6a6c4dd6962d0f9aab066da58b43968ac19949642145a0cca4b1a0b43e6833d1d0962d0f980142833596c5a58337194962d0f9a710665258ae3e693329245a1f0c9a0ce7652fd2c3e6
  | 5, 0, 6 => 0xa8419a8b62d0f9a85356fa58b43e69d41994962d0f980126652d4b43e5a5419a8ca5b169a48ca4b1687c056a144594b642169a95065b28cb4356a144194964218da85358ab292c7e69246d94962d0f9aab066da58b43a6a146e0cd45b169a4ceb65248b43e6aac199496420dda0ceb4b1687c306
  | 5, 0, 7 => 0x833297ebc218f9a9b15833ad2c84600419d0bf4b0f9685067ea14b43e6a6c9a0ceb5f8f9a4d1965258b43e6833292c843f8cda9506652fd6c84691b292c5a1f019800ca491687c045a13292c84398f9a85358abad2c846833296c8f42169a8535933ad7e3e68cc5594962d0f9a85065b28cb4376
  | 5, 0, 8 => 0xa6c19ac962d0f9a85106db292c84688b292c5a290f9aab066a3296c5a69741994962d0f9aab065b28cb435697c9994922d0f9aab2665320b43e60050a2aca4b1ed6b72665238b43e60050a20ca4208d685066db516c5a6833292c672d0f9801426a2d8b40c5833297eb12d0f9a0cdd65258b43e6
  | 5, 0, 9 => 0xa1449949642169aa9067e218b43e6aa419d696238f9a8537833516c5a60049194961f0a569b1065259083e68741994962d0f9994963f9c8b43e6a6c19a8b62d0f9a652365258b43e695c1994962d0f9a8513833292c84691c1994b62d0f9a6b1565258ae3e683329225a1f04da9f0669a59083e6
  | 5, 0, 10 => 0x90c1994b62d0f9a85408336d6c5a691c6d94962d0f9a85066525908346a34199a962d0f9a0cd44b168aa3e6a141994c8218dda670665258b43e6aac4d94962d0f9a85066db297e666a1419b6ca5c2d9801428336d605a50050a26ca4b21168506652fd503e60048d94b62d0f96630665258b43e6
  | 5, 0, 11 => 0xa6c1994bf330f999496421c8a23e69ac19d0962d0f9aa10677a58b43e6833fd94962d0f9a0cca589687c356a1419b4b64b169ab7066da58b43d6003ad2c521f03160ceb59a58b43e68c419d6962d0f9a3d0665258b43e6a141a00d45b169a48ca4b1687c326833292c92420cda9b0682224b43e6
  | 5, 0, 12 => 0x8332944922d0f9a9b067aa58b43960049994bf2a8f96b506652589c3e6833292c6d350f9a0cca4b21102336aac9994bf420f9a850666258b43e6a1445b6ca5b169aab06652d8b43a6a141994bf330dda4d1565250b43e6a1419d6d45b169a48ca4b1687c336a141994962d8f9a9b1b8ab292c846
  | 5, 0, 13 => 0xa1419b6ca51211a951b8ab292c846a541994bf330f9a0cca4b1b4a23e6a6c4594b62d0f9a46db65258b43e6aac19ac962d0f9a850865258b43e69e41994962d0f9a0cca4b1687c0268332944a02d0f9a85066b2fd6c5a69341994b12d0f9a4adb65244b43e69a49994962a8f980126652d0b43e5
  | 5, 0, 14 => 0xa1419d6b74b0f9a0cfc6da44b43e6ad46e2aca4b211a0cdb652cd225a6a6c1994a2420f9a852f833516c5a6a1419948b420cda0ce66da58b43e6833292c652d0f9a9b0677a58b43e6003992c5a1f03169aeb4b210e43e6a1419acca5b169a0cca5fa41083e600419cc5a1f08d4010675af52c3e5
  | 5, 0, 15 => 0x833292c612d0f9a5f0665258ae3e6833adb6912d0f9a0ce84b1687c23691b292c5a1f0c9a0ceb652f92c3e6a1419de96230f9a9b0675a58da3e6a1419b6ad4b169a84f06522cb43e69a49994922d0f9a5b0665258b43e60050a0cca220f9685268ab297e846833292c5a1f0498010674258b4325
  | 5, 1, 0 => 0xa1419a8b62d069a85066a3216c5a6923292c5a258f9a0ceb6da58aa3e6aac4594b62d0f9a0cca51270b43e6a1419b6ca5b1b5a0cca4ea58b43e691bad94962d0f9a46ca4b1687c336a132916722d0f9a852a883292c8469245594962d0f9aab1465258b43e6a1419a8b652169a0ce8652fd2c3e6
  | 5, 1, 1 => 0x88b292c5a2b0f9a0d0065244b43e68334594962d0f9a0cf273258b43e6833292c6d2a8f9a85066a2d8b4466933296c5a2a8f9aaaca4b1e0b43e6ad45594962d0f5a0cca62258b43e6aac9994963d8f9a851375b292c846a6c1994b6368f9a9b06652d8b43c6833e1b6962d0f9a8506703297e3e6
  | 5, 1, 2 => 0x833ad62962d0f9aab2a65288b43e60050a20ca4b0916450675a58b43e68340dd0962d0f9a4cca49168983e6aac999496420cda790673258b43e6a145594963c169a85066b2fc863e6833ad7ebd4b0f9a85268ab292c7b6833293c962d0f9ab50670a58b43e6833992c872d0f9a850675aed2c3e6
  | 5, 1, 3 => 0x833ad2c521f0e5aa9066da58b4396a141994b75b169a950b65258b43e6a9419b0962d0f9a9b0666a58b43e6833296c9641969a710665258b23e6a6c2d94962d0f9a0cca4b23d08336833292c692d0f9a0cf8652d8b43e6833292c622a8f9a431565258b43e6a141994bf220f980106729687c235
  | 5, 1, 4 => 0x9dc1994962d0f98014a833516c5a50053620ca4b21160cca5faccb43e69332924842d0f9a8506652fcc83e697c1994942d0f9a84ca4b210e4396a13294484390f9a610665258b43e6a14d60cd45b169ab51565258b43b6a541994a24b211801426525908735833cd94962d0f9a0cca481687c3c6
  | 5, 1, 5 => 0x52a0cca5f9996850b65258b43e6a144194964208da6b2365258b43e6
  | 6, 0, 0 => 0xa54420cca4b1687cf42833ad94bf448f9c010665259245a19300284ca4b1687c0a6a141994962d0f828e0083328b4521f08d800ca4b168a23e0630029b1065258b43e6a141994962d0f820f5a8ac19949642169eab0665258b43e09bd0a0cca4b168803e7a145a2aca4b1687cf428341194bf218f9c010665168a23e11b50a0cca56a58b43e7
  | 6, 0, 1 => 0xa1419b0ca4b1687cf429ac199496420cde8506683292c5a1f3d0a0cca4b1687c2d7005260cca4b0c852c00a11687c230b831a9538833292c5a1f38029506652d8b4356a141994962e1687ce00a54199496190a58015583328b43211b536370675a58b43e7003292c5a290f818d55832d946962d0f9e8510652d92c5a1f3c19b6ca4b168a23e7
  | 6, 0, 2 => 0xa14199eca4b1687cf0665259245a1f0a5e8506652d8b4451abd0a0cd34b214b43e700419f6ca4b1687cd428340194862d0f9e850665288b43e0db802951065258b43e60050a20ca4b16864d4297c1994962d0f1eb506652591a5a1f38028506652d8b4376a14d20cca4b2107cf4a833292c5a1f00de850665b292c5a1f3c199496421fcb43e7
  | 6, 0, 3 => 0x535d6962d0f818d42883292c5a1f08dc0106652f12c5a1f30028506652587c2569348a0cca4b1687cf42833296c5a1a8a5e8507833292c5a1f3d6a710665258b43e7a14560cca5d1687cf429ac1994bf218f9ea906652590c5a1f3d56692665258b43e7005564cca5f9687cc00a6c19d65a1f08d80124833292c5a1f350a0cca4b1687c197
  | 6, 0, 4 => 0xa141a08ca4b1207ce00a14187c291185d8014d833292c8419b50a0ceb652fd6c3e7a149a2aca5b1687cf42a0c1994962d0f9c0106652f52c5a1f350a0cca4d258b43e7a541994962d0f81ef429ac1994a22d0f9c014288419949642350a5f06652fcb43e7a141994bf4218c7cf42833d994962d0f9e85158334d2c5a1f3d6e6b0675a58b43e7
  | 6, 0, 5 => 0xaac19a4ca4b1687cf428ac199496368f9e0cca4b168a43e193d0a390665258b43e7a5419f8db4b1687cf42833296c96420cdc0000923292c5a1f2d0a371565258923e70000285066a2d8b4b428641994962d0f9c010665258fe5a1f3002ab066525864296a141994b94b1687cf0665258b4511f0c9e85268334d2c5a1f3c19f8ca4b168a23e7
  | 6, 0, 6 => 0xa5419d6db4b1687ce008339194962d0f980150833512c5a1f350a2b0670a58b43e7a141994963f1687cf42833292c5a1f089e850665258b43e1038029b06652fc863e60055620ca4b1687cd06652fd7c962d0f9c014a833292c662d350a0cca4b17cb43e7a141994962f1687ce00833297e902d0f98010665259005a1f3556812665258b43e7
  | 6, 0, 7 => 0xa14d60cca4b1f87cf42833296ca22d0f9e8509833292c5a1f3d0a0cca4b1687c0d7a53292c84391687cf4d833292c6d2d0f9e85358336d6c962d3d2a6b1565258b43e70050a22962d0f82ec00a145594962d0f1801428336d2c5a1eb50a6b067aa58b43e7005360ceb4b0f852d42834119496420f9e850677b512c5a1f38029b0665288b43e6
  | 6, 0, 8 => 0xa147e0cca4b16876f4d833ad2c5a1f0c9c01066525908511f352a6b2665258b43e7a141994962d0f85cf429341994b62d0f1ead10833292c5a1f3d360cca4b1687c377aac1994962d0f81ef428332180962d0f9e8535833512c5a1f3d0a20ca4b1687c0b7a141994962d1087ce00a3c18b43e1185d80142833292c711f3419949649210b43e7
  | 6, 0, 9 => 0xad4d62aca4b1687cf066525908812d0f9c014a83329445a1f3002850665288b4326a141994bf218f832f42833296c962d0e9e2b0665258b4571f38020cca4b1687c30600419945a2a8f846d429ac19d696420f9e85348ab292c5a1f3d560cfc6da58b43e7a141994994b1687ce00a541994bf218f980142833297e4319350a0cca4b1687c1f7
  | 6, 0, 10 => 0xa141946962d1147cf42833ad94c84b0f9c014d651687c23063002470665258b43e6aac19d6db4b1687cf429ac55b6962d0f9eab2665258b43e023800010675a58a43e58336d94962d1547cf4d833ad7e962d0f9e950665258da5a1f3d0a0cec65258b43e70050994962d0f816d429c419d6962d0f9e8506652612c5a1f3d0a810665238b43e7
  | 6, 0, 11 => 0x833292c5a290f86ae00833292c812d0f98000091b292c5a1f2d0a0cd365259083e7a1419b6ca5fad8b4e00a6c19d696420f9a0cca4b168a23e1abd3e0cd365258b43e700419f4ca4b1687cd428336994962d0f9e85408ab292c5a1f3802850665258f63e6a14d64cdb4b1687cf54833d594962d0f9e850665288b43e11b802ab066525908336
  | 6, 0, 12 => 0xaac199496369687cf55933292c5a260f9e9b06652fd6c5a1f3d360cca4b188b43e70049a0cca481687cd429c41994962d0f5c015583329445a1f350a0cca4b1687c1e700529945a1f08c18d15833292c5a288f9c014265168642306350a0cca45a10b43e7a14199aca4b1687cf4a8340194962d0f9e851b8ab292c842d3d360cca4b1687c277
  | 6, 0, 13 => 0x833292c5a2a8f864f429ac19d696278f9e8506652ed2c5a1f3d0a4d1565234b43e7a1419eaca4b11c7cf067e3292c5a2a8f9e8506652fd6c5a1bbd0a3706652d8b43579341994962d1447ce00a14192c5a1f059ab73d833292c5a1f3d0a7d0665258b43e7005360cca1f0a446d429ac4594962d0f9e2b0665258b4521f3c19b6ca4b168a83e7
  | 6, 0, 14 => 0xa14d62cca4b1687cf06652fd78962d0f9e9b2f833292c5a1f3d564cca5b258b43e7a6c19d6962d0f86af4288b292c5a1f029e6b06652591e5a1f380285064b1b47c176a6c460cca4b1687ce00833292c5a190c5a4d0665258b4521f3d2a0cca4b1687c097a1419fad34b1687ce00a6b292c3e14831a95067e3296c5a1f380285066da58b43a6
  | 6, 0, 15 => 0x419945a280f846d42833295c962d0f9c014a652587c2906300284ca4b0c8520c6ad41994962d0f812e00a4c19943e1488da9b15833ad2c5a1f3d0a6b2675a58b43e70053622ca4b1687cd4d8b41994962d0f9eab06803292c5a1f38029506650f8522360050a0cca190a446d4d8dc199496420f9e9506652fd6c5a1f3d0a0cdb652d90c5a7
  | 6, 1, 0 => 0x50a0cb6519686ad4a97c1994962d0f9c014283338b43e11b50a0cfc65258e23e70050a20ca2d0f846d4293419b4962d0f9e9b26833ad2c5a1f3d0a0cca4b1c0b43e7a141994964216872f428336d94b62d0d5c0106652cd2c5a1f350a0cfc6dad8b43e7005564cca4b16864d4a88c1994962d0f9e9506652d92c842d380284ca5b1686a0c6
  | 6, 1, 1 => 0x8dc620cca4b1687cf4293419b6ca5b169e850666a58b43e0d3d0a6b1565258b43d7a141994a24b2107cf0665258b43e190c1e85368334d2c5a1f3802951165258b43e60050a22ca4b16864d4a8b41994962d0f9e853d833292c841f3d360cca5b1687c357a1441b6ca4b1687cf55833292c5a1f09de6b06652592a5a1f3c19d6e465258b43e7
  | 6, 1, 2 => 0xadc1994962d0f806f42833292c5a208f9e850677b292c6d1f3d220cca4b1687c2470041994964796864c00a141994b61a8a5a8506653212c5a1bb80295064b16864176a241994962d0f822f4d833292c5a1f069eb738833292c5a1f38020cca4b240b4326aac1994bf5b1687cf55933292c5a1f0a5eab0665258c45a1f3d360cca64258b43e7
  | 6, 1, 3 => 0x833292c902d0f852f428335d94962d0f9e9506653212c5a1f3d0a0cdb65258cc5a7aac9994962d0f878f428332950962d0f9e85066db29165a1f3d0a0d00652d8b4357a14de0cca4b1687cf4288b292c5a1f0a5e9b067abad2c5a1f3d364d06652d8b43e7833292c5a2a8f86af42833292e962d0f9c014289b292c5a1f350a0cca4b1687c157
  | 6, 1, 4 => 0xa549a0cca5b1687cf429ac19d6bf4b0f9e9b0665258b43e123d0a2b0665258b42770050a0cca5b16874d428336d9496420cdeb70665258b44f1f3d0a0cd35b258b43e70050a0cca4b1f87cd42833ad94b62d0d5c01426525908330634199496479687c297a1441f8ca4b1687ce00a6c19a6962d0f9801064b168a23e0bb52a0cca4b1687c1a7
  | 6, 1, 5 => 0x50a0cd45b1687cc00933292c5a2a8f9a8539833292c5a1f3d0a0ceb652b4b43e7a1419b6ca5f90c7cf4d833292c841f0cdc0142833592c5a1f3002ab1665258b43e6a1419d6db4b16872f55933292c842d0f9c0142652fc863e0630020cdb65244b43e6a14420cca4b2107cf42833f1b6962d0e9e9b0665258cc5a1f3802ab064b16864176
  | 6, 1, 6 => 0x45e0cca4b1687cc008339d94962d0f9a0cca4b23d085a1f3d0a150665258b43e7a1419d6ca459687cf066525920842d0f9c014d83258b43e08b50a0cca5f90c7c377a14be0cca5b1686af4a833292c662d0f9e870665258b43e03bd6e6b1565258b43e7a5419b6ca5b258b4f429ec5594962d0f9e9b34833292c5a1f3802af1165258b43e6
  | 6, 1, 7 => 0xa14aa0cca4b1687cf558335194962d0f9c01428a3292c5a1f350a0cfc65288b43e7aac19b6ca5b258b4f428336da8962d0f9e851c833292c6d1f3d0a4d1565259085a7a141994bf218f864e00a13512c5a1f031801428dc5594964230028506652fccc3e6a149a2aca5f9687cf4297c1992962d0f9e9534833292c5a1f3d6a371565258b43e7
  | 6, 1, 8 => 0xa14197eb6519687cf45833292c5a1f065e8506703292c5a1f3d360cca4b1687c047a141994962d0f834f42833295e962d0f9e8537833512c5a1f3d0a0cca64258b43e7a149a20ca4b1687cf428dc4594962d0f9c01064b168aa3e0bb50a0cca5b1686a1a7a141994c85b1686ae00a144594b62d0f9a9540833292c5a1f3c6e2f0665258b43e7
  | 6, 1, 9 => 0xa1419acbf4b1687ce00a5258b43e0b831801424b168641706350a4d0675b297e3e70050a0cca4b18854d428941994962d0f9c0147651687c2306352a0cca4b1687c047a14be0ca34b1687cf42833292c5a1f021eab0665258b43e1cbd0a0cca4b1687c0e70050a0cca4b21072d4d833292c5a1f0ede85067e3296c5a1d3802850665289083e6
  | 6, 1, 10 => 0xa141990a34b1687cf429341994a22d0f9e85067ab29165a1f3d0a0cca642fc863e7a14196ca32d0f86ae008cc1994962d0f9a850665258b43e143d0a2b0665288b43e7a141a0aca4b1687ce00a144594961f0a5a8506652d92c5a1bbd0a0ccd5b258b43e7ae4e20cca4b1687cf42833292c5a1f0bde850665258b43e12bd6a3f0665258b43e7
  | 6, 1, 11 => 0xadc1994962d0f87af42833292c5a1f005e950665258b43e0cb80284ca4b1b47c0c6a5419d6ca5fa587cf54833adb6962d0f9e850665258b43e10bd0a0cca4b1687c007a1419b6d34b1687cf428341194892d0f9e8526832d9465a1f3d0a0cca642588a3e7a6c1994962d0f832f428a3f194962d0f9e8506652fd6c841f3d0a0ca34b1687c1a7
  | 6, 1, 12 => 0x2850665258b43e0c3802850b65258b43e60050a0cca218f832d42833292c5a1f0b1e850665258b43f1f3d0a0cf765258b43e7a14419496461687cf42833292c5a1f099e9b26833297e5a1f38028506651686a1a6
  | 7, 0, 0 => 0x50a0cca4b1687c1970050a0cca4da58b43e70050a0ceb652fd2c3e70050a4d1565258b43e700536370665258b43e70050a0cbf4b1687c177a1419d6ca4b1687c3980050a6b06651687c237a14d60cca4b238b43e80050a0c962d0f866177a1419f8ca4b1687c3a80050a0cd265258b4327a15020cfc65258b43e8a14199496421687c2380050a0c962d0f864177a14d20cca5fa58b43e8
  | 7, 0, 1 => 0x50a0cca5b1687c2370056e6b0665258b43e7000029aca4b1687c0c60050a7b0665258b43e70052a370665258b43e70050a370665258b4327000029b06651687c236a141a08eb65258b43e80050a0cde65258b43e70050a0c962d10c7c177000020cca4b168aa3e60050a1f0665258b43e7a141a08fc65258b43e8005560cca4b210b43e70050a0cca4b1687c117a146e0cca5b258b43e8
  | 7, 0, 2 => 0xa1419d6ca4b224b43e80000294ca4b1687c0c60000284ca4b168640c60050a2b0665259085a70050a0c962d0f86a177000029506651687c2360000285066516864236a14d60cca4b1687c3280050a0cb651a58b43e70050a0cca4b1687c3c7a1419b6ca5b258b43e8a146e0cca4b1687c2380050a0cca4b1687c1370050994b64b1687c0c70050a0cca4b1687c1c70050a0cca51258b43e7
  | 7, 0, 3 => 0x20cca4b248b43e6a1419f8ca5b258b43e80050994962d0f8520c7a15024d0665258b43e8005360cca4b1687c3270050a0cca2d0f8522370050a4d064b1687c177a1419b6ca4b1687c2380050a0cca5b2587c2970050994962d0f8460c70050a2b064b1687c177a14d60cca5fa58b43e8000029b06652587c2960052a0cdb65258b43e70050a0cdb65258b4327a14d60cca4b1687c338
  | 7, 0, 4 => 0x50a0cca4b1687c037005560cdb65258b43e7a1419d6ca5b258b43e8a141994b64b1687c338005360cca5fa58b43e7000029306652587c296a141994964218cb43e80050a710665258b43e7000028506652d8b4356005360cca4b1687c337a14d60cca4b168863e8a1419b6ca4b1687c2980050a0cca2d0f8461c7a141a00ca5b258b43e80050a210665258b43e7a141994b64b1687c328
  | 7, 0, 5 => 0xa1419d6ca4b1687c1180050a0cca4b1687c0f70052a0cca5fa58b43e70050a0cca5fa58b43270052a0ceb65258b43e70050a0ceb65258b4327a141994962d0f864238005360cca4b168863e70052a0cca4b1687c3370050a0cca4b16866327a147e2b0665258b43e800002851065258b43e60052a0cca4b1687c327a1419b6ca4b1687c138a141994962d0f8642b8a141994bf5b258b43e8
  | 7, 0, 6 => 0x5560ceb65258b43e70050a6b1565258b43e7a14e20cdb65258b43e8a1419f8ca4b168903e8005360cca4b1687c3570052a0cca4b168863e70050a0cca4b16886327a14be0cca5b258b43e80050a0cca4b188b4327a1419b6ca4b210b43e80050a0cca4b168642a70050a0cfc6da58b43e7005099496421687c0c7a1419d6ca4b1687c238a141994962d0f866238a141994bf4b1687c198
  | 7, 0, 7 => 0x50a3706652587c2970050a0cdb651687c2370000284ca2d0f8460c60056a2b0665258b43e70050a0d0065258b43e7a146e0cdb65258b43e80050a0cca4b1687c377a141994b64b1687c1a8a141994c85b258b43e80050a3706651687c237a149a0cca5b258b43e800002850665288b43e6a14d60cca4b1687c3d8000028506652fc863e60050a6b2665258b43e70050a0cca2d0f8461d7
  | 7, 0, 8 => 0x509f8ca4b1687c0c70050a5f0665258b43e70050a0cca2d0f8642370050a0cdb652587c29700002ab2665258b43e60050a230665258b43e70000284ca4b0f8520c6a146e0cca5fa58b43e8a146e0ceb65258b43e8000028506650f8522360050a0cca5fad8b43e7a146e0cca4b1687c328a146e0cfc65258b43e8a15026b0665258b43e80050a0cfc652d8b43e7a1419f8ca4b1687c0f8
  | 7, 0, 9 => 0xa141a00fc65258b43e80050a0cca4b1687c1a7a1419b6ca4b168863e80050a0cca64258b43e7a141994bf4b1687c378a146e0cca4b1687c3580050a0cca5b1687c357000020cca4b23cb43e6a1419b6ca5fa58b43e8a1419b6ca4b1687c3380050a0cca5f9687c23700002851165258b43e60050a0ceb651687c2370050a0cca2d0f866237a1419b6ca4b1687c328a14560cca4b234b43e8
  | 7, 0, 10 => 0xa14d60cca4b1687c238a149a0cdb65258b43e8a14560cdb65258b43e80052a6b0665258b43e70050a6b0665258b4327a141994962d10c7c3280050a0cca4b198b43e7a1419d6ca5fa58b43e8a1419b6ca4b1687c358a14d60cca5b258b43e80050a0cca4b1687c3d7a141994bf4b1687c328a1419d6ca4b1687c3280050a4d06652d8b43e7a14560cca4b168923e80050a0ceb652587c297
  | 7, 0, 11 => 0xa14e26b0665258b43e8a141994c85fa58b43e8005560cca5b258b43e7a149a0ceb65258b43e80052a0cca4b1687c2370050a0cca4b16864237005360cca4b1687c29700002950665258b4326a1419eadb65258b43e80050a0cca4b1687c3a7a1419d6ca4b1687c358005360cca4b1687c2370052a0cca5b258b43e70050a0cca5b258b4327000029b0665258b43260050a690665258b43e7
  | 7, 0, 12 => 0xa141994b64b210b43e8a1419eaeb65258b43e8a14d60cca4b1687c0380000284962d0f82e0c6a141994962d0f852238
  | 8, 0, 0 => 0x1429ac1994962d0f9e850665258b4431f3d0a0cca5fa58b43e7a1419d6ca4b1687cf42833292c5a1f0cde850665258b43e193d0a0cdb65258b43e70050994962d0f818c00a1419945a1f08da851b833292c5a1f3d0a0cca4b1687c2370052a0cca4b1687cc00a141994962d0c9a8506652d92c5a1f38029b0665258b43e6
  | 9, 0, 0 => 0x2850665258b43e6
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
  | 0, 0 => 0x1f1e0030cf00f8fe01ffff00f8fe01ffff00f8fe01f03f0007fe000fff0007fe00000f0007e0000ff000071e0000cf
  | 0, 1 => 0x300fe06003f0300e006003003001e06000f00fffe01ffff00fffe01ffff00fffe01ffff00ffe001fff000fffe01f0ff
  | 0, 2 => 0x1f07fe3e0fff1c071e380fcf1f07fe3e0fff1f07fe3e0fff1f07e03e0ff01f07e03e00001f071e3e00cf1f07003e00c0
  | 0, 3 => 0xe0f81fc1f00f00e0fe01c03f00e0e001c03000001e00000fe3f8ffc7f03fe3f8e1c7f030e3181fc6300fe31801c63000
  | 0, 4 => 0x1e00000fffffe1fff0f0ff1f1ffe30cfff1f01fe30c0e3f8ffc7f03fe3f801c7f000e3001fc6000fe0f8e1c1f030
  | 0, 5 => 0xfff801fff000fcff01f9ffc0e0f8e1c1ff301ce7e039cff01c0700380fc000e0e001cf30ff1f1ffe30cffc1f01f830c0
  | 0, 6 => 0xe3f8e1c7f030000000000000ff1f01fe30c0000000000000ffffe1fffff0ffffe1fe0000ffffe1c1f000
  | 0, 7 => 0x7fe000fff00001e00000f000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 8 => 0xe00001c00000e00001c000000000000f00e3181fc63f0f000000000f00e3181fc6300f001f1e0030cf00f8fe01f03f
  | 0, 9 => 0xe00001c000000000000f00000000000000000000000f0000000000000000000000000000000000000000e00001cf00
  | 0, 10 => 0xe0e000000000e0e000000000e0e000000000e0e001c00000e0e001c00000e0e001c00000e0e000000000e0e001c030
  | 0, 11 => 0xe0fe01cf3fe3f8e1c7ff301fe7fe3fc0cf00ffe001fff000f8e001ff3000e0e001cf3000e0e001c00000e0e001c000
  | 0, 12 => 0xe0e000000000001e000f0f00001e000000000000000f00000000000f00ffffe1fffff0ffffe1fe0000ffffe1c1f000
  | 0, 13 => 0xe0e000000000e0e001c00000e0e001cf3000e0e000000000e0e000000000e0e000000000e0e001c00000e0e001c000
  | 0, 14 => 0xe0e000000000000000000000000000000000000000000000e0e001cf3000e00001cf00
  | 0, 15 => 0xe0fe01c00000e0e001cf3000e0e000000000e00001c00000e0e001cf3000e0e001cf3000001e00000f000000000f00
  | 1, 0 => 0xe0fe01cf3f00e0fe00000f00e0fe00000000e0fe00000000e0fe01c00f
  | 1, 1 => 0x1c07000000001c00003800001c00003800001c0000380000000000000f00000000000000000000000f00000000000000
  | 1, 2 => 0x1c07fe380fff1c0700380fc01c07003800001c07003800001c07003800001c07003800001c07000000001c0700000000
  | 1, 3 => 0x1c07000000001c07000000001c07000000001c0700000000ffffe1fffff01f071e3e0fcf1cffe039fff01c1f1e383fcf
  | 1, 4 => 0x1c0700380fc01c07003800001c0700380000
  | 1, 5 => 0x1c00003800001c0700380fc01c0700380fc01c0700380fc01c070000000000001e00000f00001e00000f000000000f00
  | 1, 6 => 0xe00001c0001c071e380fcf1c071e38000f1c071e3800001c071e00000f1c071e0000001c071e0000001c0700380fc0
  | 1, 7 => 0x1ce7e039cff01ce7e03800001ce7e001c0001ce7e00000001ce00039c0001c0700380fc01c000038000000e0e001cf30
  | 1, 8 => 0x1ce7fe38000f1ce7fe3800001ce7fe01c00f1ce7fe01c0001c0700380fc01c000038000000e0e001cf3000e00001c000
  | 1, 9 => 0xffff01fff0c0e0f8e1c1f030e3f8e1c7f030e3f801c7f000e0ffe1c1fff0e0f801c1f000e00001c000001ce7fe39cfff
  | 1, 10 => 0xe00001c00000e0f801c1f000e3f8e1c7f030e0f801c1f000e0f801c1f000ffffe1fffff0ffffe1fff000e0f81fc1f00f
  | 1, 11 => 0xe00001c00000e0f801c1ff00e0f801c00000e0f800000000e0f81fc1f00fe0f801c1f000e0f801c1f000e0f801c1f000
  | 1, 12 => 0xe0f8e1c00000e0f8e1c1f000e0f8e1c1f030e0f8e0000000e0f801c1f000e0f801c1f000e0f801c1f000e00001c00f00
  | 1, 13 => 0xe0f8e1c1ff30e0f8e1c1f000e0f8e1c1f000e0f81fc1ff0fe0f8e1c1ff30e0f8e1c1f000e0f8e1c1f000e0f8e1c1f000
  | 1, 14 => 0xfce001f9cf00fc0001f80000e0f8ffc1ff3fe0f8ffc1f00fe0f8ffc00000e0f8ffc1f00fe0f801c1f000e00001c00000
  | 1, 15 => 0xfcff1ff8000ffcff1ff80000fcff01f9ffc0fcff01f9ffc0fcff01f9f000fcff01f80000fcff01c1f000fcff00000000
  | 2, 0 => 0xff00fffe003fff0001fe0000fcfffff9fffffcffe1f9fff0fcffe1f9ffc0fcffe1f80000fcffe1f9ffc0fcff1ff9ffcf
  | 2, 1 => 0xffffe1fffff0ffffe1c1f000ff1f01fe30c0ff001ffe000fff1f01fe30c0ff181ffe300fff071ffe00cfff0701fe00c0
  | 2, 2 => 0xffe0e0000000ff0001fe0f00ff001ffe000fff0001fe0000ff0001fe0000ff0001fe0000ff0001fe0000ff0001fe0000
  | 2, 3 => 0xffe0ffffcf3fffe0ffffc00fffe0ffffc000ffe0e1ffcf30ffe0e1ffcf30ffe0e1ffc000ffe0e1fe0000ffe0e1c1c000
  | 2, 4 => 0xff0701fe0000ff0701fe0fc0ff0701fe0000ff0701fe0000ff0701fe0000ff0701c00000ff0700000000ff0001fe0000
  | 2, 5 => 0xff071ffe0fcfff071ffe000fff071ffe0000ff071ffe000fff071fc0000fff0701fe0fc0ff0701fe0000ff0701fe0000
  | 2, 6 => 0xfff801fff000fff801fff000fff801fff000ffe7e1ffcff0ffe7e1ffc000ffe7e1ffcf30ffe7e1fe0000ffe7e0000000
  | 2, 7 => 0xffff01fe0000fff8ffffff3ffff8e1ffff30fff8e1fff000fff8e1fe0000fff8e0000000fff801ffff00fff81ffff00f
  | 2, 8 => 0xffffffc7f03fffffffc7f030ffffffc6300ffffffe3e00cffffffe0030cffffffe000000ffffe1fffff0ffff01ffffc0
  | 2, 9 => 0xffffffc1f000ffffffc7f030ffffffc1f000fffffe000000fffffe000000fffffe00000ffffffffe30cffffffffe30c0
  | 2, 10 => 0xfffffffe0000fffffffe0000fffffffe0000ffffffc1f00fffffffc1f000ffffffc1f000ffffffc1f000ffffffc1f000
  | 2, 11 => 0xfffffffff00ffffffffff000fffffffe000ffffffffe0000fffffffe0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1d0c0030c600282a00f29500282a00515700282a005015000366000953000366000953000240000800000104000042
  | 0, 1 => 0x300b2060039020080040020010010020008007f6e00fbd7005f4c00bac6007e6a00fa9500564000aa80003d2e0070d7
  | 0, 2 => 0xf03f61e0d7b0d03761a0d5b0f03d41e0c6a0b02f2160c390a02c0140c200a02c0140c200501140a004a000000000000
  | 0, 3 => 0x61a83ac3501d63a8bac7503d42a0a285403121283a42501d638898c7102c42808085002021081842100c000000000000
  | 0, 4 => 0x25091c4a104ed29481a520a0b11c1962308c90140120208063a8bac7503d63a898c7502c63a8bac7503d62a8aac55035
  | 0, 5 => 0xdad481b5a6a0d8d641b1ae80dad6c1b5aea0dad6c1b5aea098564130ae804ac2c0958e20b51d1d6a30ceb41d0d6830c6
  | 0, 6 => 0x421260841534681848d0162040104080142903423206191002022004111dad6c1b5aea0dad6c1b50c20dad6c1a1aa80
  | 0, 7 => 0x252b7e4a595f25293e4a515f2528184a500c2501144a014a2520324a411924290c48514620282a40511520282a405004
  | 0, 8 => 0x40e02281c31140e00081c30008626210cf11294a58529f0c084240108f0025293e4a515f253d3e4a71df25293e4a515f
  | 0, 9 => 0x4ae08095c6204ae2e295cf314ae2e2954d314ac2c0958f204ac2c0958e204ac2c0950d204aa0a295453148e24091cf00
  | 0, 10 => 0x4ae2e2954d314ae2e2950d204ae2e2950c204ae2e281cb114ae2e281cb004ae2e281ca004ae2e20049114ae2e2854831
  | 0, 11 => 0x6beafad7df3d4ae2e295cf314fe3f68bca4a4af6e295efb14ae2e295cf314ae2e295cf314ae2e295cf314ae2e295ce20
  | 0, 12 => 0x4ee3e60849532d6b7e5adf5f2d6b7e40da040c636618cf530c4344188f42daf6e3b5efb1daf6e3b50c20daf6e3a1ea80
  | 0, 13 => 0x6aeaead55d356aeaeac1db154ee3e69dcf734ee3e69d4d734ee3e69d0d624ee3e69d0c204ee3e689cb424ee3e681ca00
  | 0, 14 => 0x6fc3d4df8e286fc3d4df0d6a6fe2f2df4d396fa8badf553d6fa0b2df45396f8090df04286eebeedddf776ceb4cd9df46
  | 0, 15 => 0x6febfec1da046feafadfdf3d6feafadf5d3d6fe898dfd62c6fe3f6dfcf7b6fe3f6dfcf396febfedfdf7f6fc3d4df8f6a
  | 1, 0 => 0x98564120ab8094550528a3c290540120a3806febfedfdf7f6febfedf5d7f6febfedf4d396febfedf0c286febfecbdb5f
  | 1, 1 => 0x9c57440809429c540138a6809c01053805429c00013805009c574538afc29c574538afc298564130af8098564130ae80
  | 1, 2 => 0x9c576738afd39c574538afc29c574538ae809c5745380d429c5745380d009c5745380c009c574528abc29c574520aa80
  | 1, 3 => 0x9c776728ebd39c776720eb919c776720ea809c7766084953ded7c5bdafe29d57553aafca9c574538afc29c5f4d38bfc6
  | 1, 4 => 0xb87e6b70fe84b87e6b60fa84b47d2f68f3d7b47d0d68f3c6b07c0960f2849c776738efd39c7767384d119c7767380c00
  | 1, 5 => 0xbd7c197af68cbd77777aefdbbc7f6f78ffd7bc7f6f78ffc6bc7f6f68fbd7bd7f7f7affdfbd7f7f6afbdfb87e6b70ff95
  | 1, 6 => 0xd4f527a9e3d3bd7f7f7affdfbd7f7f7a5d5fbd7f7f7a0c08bd7f7f6afbdfbd7f7f68fbc6bd7f7f60fa84bd7f5d7affce
  | 1, 7 => 0xdef7e7bdeff3def7e7bd0c20def7e7a1ea80def7e6084953def481bde6a0def7e7bdeff3dea1a7bd4573def7e7bdeff3
  | 1, 8 => 0xffffffff5d7fffffffff0c28ffffffebfbdfffffffe1fa84fff7f7ffeffbff8091ff0428feffeffdfff7f0fc09e1f284
  | 1, 9 => 0xf0fc09e1f284f2fcabe5f2b5f2fc89e5f2a4f0fc09e1f284f0fe49e1fa84f0fc09e1f284f0fc09e1f284ffffffffffff
  | 1, 10 => 0xf5d515eba3caf4fd2fe9f3d7f6fd8dedf3e6f4fd0de9f3c6f0fc2be1f395fafec9f5fea4fafec9f5fea4f5fd1debf2ce
  | 1, 11 => 0xfaa8abf55535f8fe49f1ff84f8fe49f10c00f8fe48405904f5fd3febf3dff5fd1debf3cef5fd1debf28cf5fc3bebf39d
  | 1, 12 => 0xfafeebf50c20fafeebe1fb95fafeebe5fab5fafeea405915fafec9f5ffa4fafec9f5fea4fafcabf5f7b5fad6c1f5afa0
  | 1, 13 => 0xfeffeffdfff7feffeffdfea4feffefe9fbd7fdff7ffbffdffafeebf5ffb5fafeebf5ffb5fafeebf5ffa4fafeebf5fea4
  | 1, 14 => 0xfce241f9cf00fca90df95546ffffffffffffffffffffffffffffffff0c28ffffffebfbdffffcbbfff7bdff8091ff0428
  | 1, 15 => 0xfdff7ffb5d5ffdff7ffb0c08fcff6ff9ffd7fcff4df9ffc6fcff4df9fe84fcff4df90c00fcff4de9fbc6fcff4c485946
  | 2, 0 => 0xff80b3ff0439ff8091ff0428fffffffffffffeffeffdfff7feffeffdffe6feffeffd0c20feffeff9ffd7fdff7ffbffdf
  | 2, 1 => 0xffd6d1ffaea8ffd6d1e1aa80ff9d9dff34eeff899dff146eff9491ff24a8ff8899ff142cff8195ff046aff8091ff0428
  | 2, 2 => 0xffe2f24a4919ffc2d1ff8f28ffa9bfff557fffa99dff556effa8bbff553dffa1b7ff457bff8195ff056affa0b3ff4539
  | 2, 3 => 0xffebffffdf7fffebffffdf7fffebffffde2cffe3f7ffcf7bffe2f3ffcf39ffe2f3ffce28ffe2f3ff4d39ffe2f3e1ca00
  | 2, 4 => 0xfff7f7ff4d7bffd7d5ffafeaffd7d5ffafeaffd7d5ffaea8ffd7d5ff0d6affd7d5e1aa80ffd7d44a094affd491ffa7a8
  | 2, 5 => 0xfffffffffffffffffffffffffffffffffeacffffffff5d7fffffffebfbdffff7f7ffeffbfff7f7ffefb9fff7f7ffeea8
  | 2, 6 => 0xfffd9dfff7eefffcbbfff7bdfffc99fff6acfff7f7ffeffbfff7f7ffeea8fff7f7ffcf7bfff7f7ff4d7bfff7f64a495b
  | 2, 7 => 0xffffddff5d6efffffffffffffffefbffffbdfffefbffffbdfffefbff5d3dfffefa4a591dfffed9ffffacfffdbffff7ff
  | 2, 8 => 0xfffffec7583dfffffe850820fffffe42180cfffffe0a084afffffe0038c6fffffe000800ffffffffffffffffddffffee
  | 2, 9 => 0xffffffe1fb95ffffffe5faa4ffffffe1fa84ffffff68fbc6fffffedf4d39fffffe4a595fffffff6a38ceffffff202880
  | 2, 10 => 0xffffffff0d6affffffff4d39ffffffff0c28ffffffebfbdfffffffebfbceffffffebfb9dffffffe9fbd7ffffffe9fbc6
  | 2, 11 => 0xfffffffffffffffffffffeacffffffff5d7fffffffff5d3dffffffff4d7b
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 48 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 48 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 349 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 349 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 349 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 349 then wireAt i else 0
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
  | 3 => 15
  | 4 => 201
  | 5 => 870
  | 6 => 1335
  | 7 => 473
  | 8 => 15
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xeae7091cc784253ba0895834843a2feb743b1ab66261186c505246c346f1d47b43c46d9e36939426359f549b287bf8db24767baf13e1db8f047ae1bd
  | 4, 0 => 0x30dc92612d2638102ca5ed0b2be8d4692968974428a335132875e09928641fb227d0d923279684de2656b13826462bd02622f9a425f177eb258eee2624aee1e22462192c237e2774230e150422e782b622b0039d1f63123b1e870bac1d5ed5011d500dfc1c8c79111c6a57a01c61f8591c3112ff1be2e8291aac09b61a47156418c248a6163af8c1144762c914018d6c134ffbfc12aa070e1223924311fa007f11ae1d0d11657ecc10c8d32810c073e10ea19d5d0e993b2d0dded2fc0dd9f4020ca3c47c0b52a9080a53b8e9091b2cdf070261e506ac1cda063949ec05cbddda0453b051044975120401dfae0303c3b3019917d1014adfa700ca251a0034aad1
  | 4, 1 => 0x6ac89b046abc4222685ad38c67e48da467a73a8363969d82618b5c1c61575367607a7da55fceed285f78dcd05f28af6d5eeb46d65e9c33915dc567355d6375445d1370125c593cab5bdcc50d5bca02cb5b3178535af403c658f0b3ef58b7810d583919d25829818157e31e6e57b49983571ba282569fc903550dee70546a50024ce6565e4c585a984c4b52524c1226c64be4306f4bd96a244b9b0fe84b896c8349c5240c484798a6478261ab469ffad74574e7c1452a481c44ac9d6c43b9e3d4434565834208a2ce3c7ac0fa3c6c566639c8718239c61f983963aefa38b159a73859bc18377bc9e0370b254635f0746335cfc0d834cd26293112d4f2310eeed6
  | 4, 2 => 0xc1835472bfed0e9ebdb40cf6ba642b1bb7eed30cb0ba2ff7ae54d563ac0add41abc11b27ab64108baac90c7faa79519aa912a648a81e8aeba81b48bca5f483eba3bf77a5a2904c3fa276a748a18a60dba0e68d7d9c63f3469b275afb9af87b279a27c5e099ea462099c29ff39936d00f97ca72a497c69a78960480399517a1ca93ea5ee89388f835935b1a7191aec9bb911bfee38e99a3318e2fa9cd8c9fafba8b64eed98a09e27c8a0371bd89f197be889b0739882d5b578800032d83a7a3de82de348b81ee6b70818132fa81653ce38000f0f17f8d6ade7a7c40cc76dc422e7590956d74b8f350721af45671cd0d807142ea806f4e0cc26dff57dc6dcd5112
  | 4, 3 => 0xfa2a5962ee5b3cb9e7b13259e010ac74d9061cb1d6a867dfc7c52738c5dfe97ec3108832
  | 5, 0 => 0x8d0d8d208cc66e208abbcb9085a20c2085416980845900a0830e72f082747ea081e977a0819690b07e998db07c081c707a676f9076ce5b1075ce39c0759d80b0727ebe6071a104906c24343069f81830685d424065cf49b063a73a7061bb4c505afb477056b49b6051c336604ed330504e549e404e075a704d5640f04a0f63a0467c7db045b4176045412d0043375330414a355040dbc7503d8a54b03c8d54903bfe0d703b9c8a6034b623b0345d3820342f57b030e670f02c4de2d02912c4902866328025216e8023ef43201e14266015b816901414df30107a89000f2b63300e3021600c274f100c2176000b698c600ab6b9b00973af700904a5100286329
  | 5, 1 => 0x15573d771504f3e714b2cd65142a76c5140d444a13f1230213cb6ed2135c5872133e0b0b133b87e21336a87312b1100c123e099e12327c8e11febfc311e339b611a76921119dfe10119217d8116d1a271136f9e51110584210fcb2c910daf28b10c1f54c1094236c1017aefe100bb3910fce77530fc57d630fb377100f581fc30f190a620e936ba10e73f1a00e41792b0e2a7d1e0e1c9d1d0e0d3e320dede7600ddbe26d0dc281530db432850db1b6820c63897a0c61e1b00bdc92600bd5dce90babf42a0b855b460b1fe0e70aec64450aebc7760ae27b2b0acd8dfa0a834cc40a7abfa40a6c0c6909dbb6cb09d0c57e097d6fc00913787508febdff08ea0cab
  | 5, 2 => 0x20a67c43207e77462071473a2032e0911fbb085b1f1c72191f009a381ee69e4d1e88b6ad1e7950191e06e3f41de0dc1d1db72cc41d5a51b51d06d5571c8c79111c795c1a1c6ad4901c1146c21bff83251be2e8291bd190dc1bb986461ba5da191b6505171af9a43b1aba8eda1a73dea31a720a881a59580e1a4343fe1a3fc2e51a27484b1a10f6e519f07a7819baa9a5196ffbe41958fcab194fe8a0191b744418f26c4c1886d0eb1878c809185284941849b34b1814878f17c1d152177f95eb1752ee85173f81df172decb91715e07516ecceb916e471a516d7856e16ac3b50166693e1164440d8163ebd771611654d15f0b91115dac5e915d84dc0159b8121
  | 5, 3 => 0x2cded53d2c3262cf2c15a6212bed559b2bac62dc2b23a65c2b06dce52ae698952a7f696e2a6f972d2a3d72cc2a3c73b92a1fc85a29c718f129bf2fc8297a7762293ede3a28fa6a4c28f7f21d28e7389028b7c64828a4f9b72884fdf828641fb2285dd70a27e9389d27d0d923279d69392798ce9c276494dd275dc42027593f0a271e96a1270a377826a23a9f26a1ae9d263aeadb260edcd4257d59b8250c0dff24cd0fd2247838b8246d800b2452ae8f24497b2c2419e1ff240f87f823f0780323b642802388293c234acf0b231ae4ec22b75799228290c8225771d222239d032201b4e321e92f6121b06328219e12d52185771a217c18ce21464164213d50c5
  | 5, 4 => 0x3761c3f3373bd8d3373b41c136b30c3c36b232e836aef64e369309083689045c36495ec135ee51be35abd13a359826f8358b546d35754e33353625f4351c18b5350f0edb34cea3d13487434e344eb4ca34313a1333fb55fb339dd11a3367765d334cc7793301de5532d5d35132bd4e68329f57f5327189f5326062483239456f321ad22832187561318c533531869e0c313951c13135d5b93133f20431329509311e3b6a3109335a30c5c97930a67ff82ffbb9dc2fb45d662fa7a6b32f845c8c2f6848b42f0acc7e2eab3f582e9a00b42e93469d2e7338f92e683fc92e65064f2e0236cb2db22c392db18c9f2d96974c2d94137c2d85129e2d1d24532cff612d
  | 5, 5 => 0x43d1a48743bccaae43767976437211c3434ac03242b779a3429eaeb94278d18f424f44f44243f1c94208a2ce41ec74b74192d6064189b8df40c5dc48405fd836404604094034903f4031dd2b3fefbd6a3ea362cd3e2c17f13e0abdb43d7cbb5e3d6fd1923d52b1513d30bc313d0e4d583d02f7853c9d75a23c72d4343c3ae0643bd82cc93bc70d473b62bf503afcd3513af81fa03ad66c3d3aa59b5f3a84e7713a792f6a3a5b06f63a184b1e3a06e07e3a068ac739c61f9839bf1eb539ad658638efb48938e84b1538da6e9f38d885d238b8c6ed38527df9382e3a70382d39c938282fa93823084137ee12d537d872f43783dd373780d5ff376a9e8637666287
  | 5, 6 => 0x51872e0e5132a5e95131491b51045f545086e646507a95f15023fb7950235ecf501c4cb94fb3d76c4edd80ed4eac6ec04e6ac9b04df5a61f4db73d124d4d08654d2923874d18a3a44cef4cf74cbcfb904c937e784c7b77174c5beb634c27808e4bd6c4d84b9b34674b266b6b4b17beb24b093b3e4af30b6b4a6fe0ba49bd3837498927d2496d53bb4968e360490ec94648f7a52d48b438cc48576daa48388c2847b4abff47a05b084797e1024781f334475bff4e4712aa5546e02be346b1d3994636123046320f1746297b2a4614d99b45bdaeb845b7253845b6a80345b3ba6a459e6fa045696f5b453a72e2453231264522df4344fa88f844ef23234438b4ed
  | 5, 7 => 0x5f9defbf5f73c8245f0af8b35e4eaf565e323a585e273f465debdb125daf15185d4e99fd5d175c9f5d094a0a5cd6dd445c51913c5c2f35f95bbb72fe5bb1eaf35b9dce135b3ef3845b37ce335b2fe5715b193db65abb056b59cdfa6259af5fe859764228596fc10a591a903758a2b58f582356fe581a76985814f1a457eff8aa57e5220757a8f5b057a1bfdd579799045796e9b0571375965711b93d56ea7c2256ce84f856b44698568842c9561ae53156157fb355c7af29558cfd36554a001554e930db545a40c853f2862353e5913153e2716e5399f3e55368384a5338070d5318541d52e2b63b528873ed527f69b85275c61951e9f25051ac20305187bbdc
  | 5, 8 => 0x6e85ad376e46e8416e4440f86dcad6f76db516756d66356b6d2297f26c8ec8b36c8a0b076c688e486c31ecb26b7347f16b2971f66ad764e76a527bf76a14b97f69f1c24b699076f3689993126882b55d6864c18d683cef24683a11b568152eb668108bd3675a8850673394256677b32966276d0266149fd26601d15f65d4793565b58cf265a22d6f6586cff76580e3c96580daed650379be64fe4f9064f3896864f0441964dabe7e64981c66648d4acb646fe92a6468b357644e9466643f09a863e3b9e363669d95631274fb62db1c0c62bd28d86215319461c4af0f618a6a10609958d06076a65d605f74066044e07c602dd5b86010936a5fdb9f045fceed28
  | 5, 9 => 0x802e8a8b802b3c317fe02d2f7fbe3ee27f3f15757f11e2d57f0741177ed3e2a77ec790e67e96b9f47e59dbf87e57f6857e551eb07e48f78f7dacffa07d7727c47d6bf5367d412f737cf270267ce97d317ce8273b7ca20dc77c8d9b0a7c3af1e37c0b4acf7c09ecbc7bc320eb7b8a37f879e85dd379333d017924126d7920d8f37829da4177a41d05778cdda47758b67f770625e676d684c875aba6e67594f423755ba818751113a07509b08f74d2344074bc702b74017231739ab7e5732cec12730c7bc77220191371a7a8897182e3317174131a709b6797707b70f26fe8041f6fe675ef6fdb1a4d6f3e3d3b6f0817006eea39b46ea01f006e8cbcc66e861e12
  | 5, 10 => 0x9086da4d906fd3e1904bfbbc8fe9e4ba8fb09c168faa3f0c8f3423d38f0617178da754a78d9ceb9f8d80c1988d5b5a268d50c6af8cf0e0088cee7c1d8cedacd18cb824a98c8080b98b4570388b2e23918af793c78a224e5d8a163a328a09748889f197be89cabe23896fa3ea8950ce3b88d14822889d8287889c62f4888a1465882be4e187a174708730e823864dac808601fdac86006efa8600536085d830bd85d14e8085c40c7685a1a78a84fea4a984d14f9784896c498488b36a8455b14984129c4083be730383b0b2bb83704754836f9d6883461d61832189ea8253c01a824978c68211e0e081a6eabf817ebe358154e8ae815380d28141b30581203a08
  | 5, 11 => 0xa953fed7a8db08d3a83cd88ba7d551c1a79986aea757444ea7228789a71f77e0a6f98d1fa547d07fa467ebffa399dfc8a2f14521a28b143ea2784c06a275f6c8a238f043a20fedeea20c8f94a1367b9ba0da3c49a0caab20a05a8e69a03c85349fa381259e8d17b19d653d4e9d5e0e199c96775d9c84dd6f9c246d989a8e36429a3e92c29a224da099a0bb1998f919d998ecf0c298a19efa989a6927987313b097f5170b96ced85296a47b2f961fcafc9613055f95f88da695ceaa2395c7f3849542bb3194f8e65494e00715942ab011940048aa938f9a29936dd64b936c84d592d30da792879af991e86a1191adbb949190d39c91654ffe91505fc390c4341b
  | 5, 12 => 0xcb9c1072c9cf3697c8cab25cc7e374b9c7b01ce1c7a2a7d0c7724034c76f3070c743034ac70d1729c6f6cdd8c6aeb261c5d3b2eec439e2a9c34ff323c10f4154c01e2105c00a6224c006d447beffb15fbd8e396cbd347685bc15e568bbddeafebaddaebfb955447eb950c2ecb80e08f0b7f60488b7a7b8afb74229b2b6b0bda3b60f9f5fb5d73681b5ca66d8b5ac93d1b5591f7eb542a130b502e1f8b4bc74ebb3eca227b3cd0f4cb2d95111b1ab07d8b144a4a3b0d3c397b0be516db092cc10b08b963dae69a340adda7edaad9feb4bad64f2d1ac9841fdac851212ac81cbceac66441eabd5072babc4b861ab68a3a5aaef9617aa67f4a6a9e1f04ea9b888c8
  | 5, 13 => 0xfc56b3d4f3aedd49f26460def1b199daf19b99cbf0550015ef46ce9cee49a450ea91aab1e64556c5e5ae3b9ee4a3126fe495e3c6dffc7862df145ecfded43b94dd445c18dbd937a4dba78fe2db809297d9d2f90cd8788062d7e6c2f0d64fc1b6d4de3103d4bdf3f6d418da8dd36eeaf4d31dd4a4d28e4411d0c6f25dd0669516cf4a1943cf160bd2ce8dd51cce63320fcc26ccdbcbb0b965
  | 6, 0 => 0x7382cc50737882a0715437d0711d49e06ce230906a40871068a399a0665520c065bd6fd060f596e0608061805e8faa005e063d205bdadfa0585bda20575e13b056ad819054d4fbe054b0cc905169eb0050c65e00507112004bca65903cf5e0b0384992f0375c6cf036e7ac0035eb4ec035d7c18033b05b5033a727c0309fe0902f09b1102dea06a02d6a72e02c7a620029bda2f029aef9e028da25d0266dda8025cb6660246bcc00240dc18023deca2022bdad10219fdf802102cb901d18b1e01c45ed601bed059019c9fad0185b85101385c4e012ba05000f89051009bfdb90082d9db006c2684004fceaa00468720003b1ab4002df20700058aa0000099dd
  | 6, 1 => 0xe7e15130e4ddd170e2b33fe0dfb96ef0de298690d9cbe430d8b234d0d6e8d170cd896110cb1ddfb0ca165b80c83298b0c7d9f2b0c7bcab90c61b8110c60dcf80c336a080c0761960bc7415d0b9beb890b8ad6cc0b88cc090b761e140b62f1840b53d07a0b3b257d0b258c830afaa0150ae34fac0ad6b89d0abb903e0abb3de50ab8b2690aae691e0aa03d900a83e0780a7677f50a5ed5a50a2deef809ec7bb709eba6f409cff8a309c0e32809917683099089cb098d4fc709633a88093e7356091a8957090dfc8408cf6ef908c6f6e608b34900086010a2085c29ce0856ca26083843fe080c0243080a8eb707fb111907db2a7f076549f1074eba940744478b
  | 6, 2 => 0x15d3ee2015c3555915808c4715776f951561a43a15608d7b1560201415212d4d14e6b4ae14696ac214344a2d1415063f141390f013f006f713e90d2b13e0e2a713d6d81d13967e2f138cad0013840285134e8ed113346ed1130cc1b3130a5a8912dbba76129e663b1294144211d640d0118d0e1d1187183a1161181a115b67ca110f8d8e10e5e4bf10d7221f10bf6ca610b7c9a8109faa421094c3a5108ef5b9106ef598106dc4111051842f104243571015aee7100f12a2100eb51c0ff95c4a0fec104b0fde41e30f9a9c580f8009980f6345690f5d348a0f3d84400f37de040f23a9e00f1c66040f0db03a0f0a85da0ef737100ec9dee60e8fc0970e85c3d3
  | 6, 3 => 0x1bf04d8c1be14d961bb5bc3e1b9386ad1b86a0301b62a5db1b5813d71b55df541b27d2611ad212461a5d20641a54311f1a4058c31a3456221a27484b1a04d97919e5619519e5257c19b9717319468cb71921f28d18eed24c18c4770b18c397ac1892cd851882b169187cdaee18787ffd1871d538186cfbda186366e3185955ec1857241818545dd6184b45791839cef01835a70818103f8817ec7ffd17ec7abb17e7c6aa17d6fff417bcd81e17bba651177a15d2175d1cd3175a929b174a0ecc17446697173643a8172f3961172938d717206e351701656116bcc03716b01e5416abddcf16a5446f16995adb1691aff31673385e164f38e016100cbf15ea9fee
  | 6, 4 => 0x2340355d233e51982335ab562325c90b22fdc41a22e55f9722c9a32f22c54fb3229eb02f228802542272790c225e42212257ddbb2241f9d72241e41521ee36a221d8db4721ce372521ada82821992a06219634db21901609216990eb213bddeb2114be8720fbfbd620fb7ea420e2e2e920a84c1420a2447e2064873a205b0a2a204b60b62015ae6f2014c6441fdbe3151fbce2ab1fb72b911f25d85c1f0740291ec0fa371e857c0f1e2d9df31e25f90f1e08e1531e03f6dd1de631f51da019151d92d90f1d825b1b1d3768591d20f0e41d0e392e1cf34cfd1cc5aa5e1ca0b1831c8d62a61c5f89e21c5f2bde1c5d3d531c2fe5291c2a38e31c0c1b4b1c03a2d4
  | 6, 5 => 0x2aa7b7282a9148702a47f4e42a4774b22a430f592a3198e02a023a7d29faee4829f0b1cd29dcd53d29d41fa529cba47729c478db29ba407729af2b6429a9145b296b38aa2920d8b3291d2a9e291385ac29025cbe28e1d56328d3f68428b13185282a58e7280b572827cafcf927c931e5277b82482759c577275958f22750b4f62713cf0026d747e026d4db0c26bb2fef26a23a9f26719c3426470b75263cc605262e99c1261101172604931525c5c2a2253ef9ad2529f166250b3e6a250aba572503934e2501500724fd26ae24c13a83245472f0244e24ea243971d5241ebbb1241d331323fafbfb23fae01e23f4a9a223d31a2523aa74da237feffe235c0631
  | 6, 6 => 0x31cea48d31a154553192e8383177ea8831752de731660f0b31629df0315ab97f30d5282030c1d39830ba24d830b6183230a5e2183067a3353046e378300601422fe11cf22fd3b15e2fa78a0a2f8f1ff32f8141142f7a8db12f51808b2f20329b2ec68d272e707eae2e31c8492e3084652e2eb6002e2509872e1a843f2df877932df741622de6358a2dda71352dc4434f2dc2721e2da94f942d618f3b2d19df392d15ed192d0ef86e2d06d0c22cf6a4682cd2606b2ccca5e22cb585092ca929c32ca0b8b82c2937292c119b4b2c0b7bec2c0281762beeba672beae6a62b9f06d02b9c405e2b25f1c52b20b3d82ae9f3842ad6e7a92ac975db2ac54d632abb56d0
  | 6, 7 => 0x39e16a4739b8a2b7399953e5396f572d394f1420394838c0390153ab388c67693849f1483824ad143821da663819b834380d7bfe37d8b58137d4a1c237d06dee37a858a7378ba63f3766c85036fb367836ea2d9636de7a8736d88c8636cdde4e36c9ea4736b5383e3679dd0b366fa27236648703363ae8203612624435fe022a35f834e935bf14c335a563b8359e2116358b20763583f091356b27a5354de99c353aa3c63510021134fe1fe134d8057634d2fbb734ceb8d134c589ee34a771a7349995fb3481847a344ddb76344782f1339be83033864f1f333ea61a333e1d3d32d7f49132c99a9e32aa3348325e970c32543cf332139fa731fefd8b31d38f2c
  | 6, 8 => 0x43f5039043acd9484389d59343555fb0434ac0324344ef7b42f1f99042ef746f42bf286342b779a34214dd1641ec4f6f41d387bf4192d6064176068d4164b840412c1b38411103a141011dbc40f6a5f940cde8cc40cda10840936de1408a06cf404b3013402d1cbd3ff4ef3e3feafc213fc23f033f3143b83f277ef23f227ddf3ebac68e3e9b9b153e80cd693e7b57fa3db4e4813d8f565c3d8a3cae3d51fe0d3d2c7c353cfaa5163cee74523cedcf813ce8e5a03cd249253c84ae723c6067923c346cd83c20e4c73bd6ad1d3ba7c9d93ba5ac113ba09a7a3b72da473b484dca3b34c0e23b33d6c03a97b4d03a822ece3a4fc2063a4d6b3c3a4d6a953a1d8e95
  | 6, 9 => 0x4dd542384dc9c7c04dc8be514dbe2e094d84259f4d67b2e34d4c1d7d4d43334a4d3bc9154ceaadad4c9d6ec24c760f734c30b0dd4be0ab424ba1260e4b86b0b34b81ba084b4c4aa34b3fdb3a4b2e44754b204aef4ac64d7b4ac2a1d44a94064b4a8b70964a8b09ee4a83d73a4a52b8ee4a1e617149c9cfdc497253c1494ba1ec493aa5864905cf5748ef45c648c35a8b48b99ca548683a63482713f647cb2c4747c6c732479eea004795ee6d4760868246f961d146f1b31146250f83461b66ed45fa3e6645f5ff6d45d91ef1458da50c457e7d57456daacd4563ccbf45280d8444d46f7844ce283544c22fd144ae84d944501f4c44451821442ba9634408d567
  | 6, 10 => 0x5617184155f9c36e55f6748055f5a32a55bc144755aa37af5571ce4a554910f15530a86c552e1ac4551db61354fb57fa54f251df54bc2a5854b8020854a96c0954a16d3c5425107553f946ff53eff8a953e591e85380fde95377f3e653738fe3536a1507534625b6533a5276532df2e15318541d530e3d0852f5cae352cb4ca352b5e32e5289b2c4524e709e524570d151ed22825160844351583e2d50ef354250eca9cc50e499dd50ded2da50c8fcab50694d92505beeb35059633d503182d950288f95501f9e51500139404fc9b71a4fa753334f9d1e774f5e8ec74f2dc6724f17f0274f0c43334f050fd04ebf453b4e80dc5e4e60acdb4dec8ea24de6f872
  | 6, 11 => 0x5f2479f65ef0b1fa5ed6a3f15eb5ede35ead0d0a5e7be5ee5e6e56a55e5e95475e5c4d5c5e11571c5da77f2c5da6006b5d7c88575d65b8685d4b941a5d24c09a5d0eae245cde0cce5cab1e5b5c7fd5c75c1f443a5c1938155ba3354b5b8e88025b6fefcf5b6bdc6c5b64ef195b4dbe2c5b469b5d5b3eec9d5b3bed485b00c4075af98e345aecd9575a6fa4e45a2d95ac59eaea5859982e6b5996e7a05989a08a58e6c54658e3d83358bb531a58b7554858a9df50588269ee585d4a97583d5a59581a3e365814f1a4576751eb5742a7955739f9c156f411bd56ba13a056b55f7156b4469856a8f0c5567c7f5156427f92563603f256279b32561ae5315618ad15
  | 6, 12 => 0x6acc942a6ababa2c6a8f01346a44543e6a08291469d67ca96911fb2368ff6c1a68ab6b95684a905368395c4067d94152676e8c9f6736134867339425672751d86725e9c5671ea51e66df9173669a48866668115266156d5865aa068765a3a87f6579a4ac65381a026516b7cb650396ea64b23f0e64595919642e54a063939f33638ae51b6355524c632206b2630f4f11630aea4563075f5062de92fb62a39a81627050f962623a3561f63a0061f617a361e2ef1b61de4e6a61ca40086113aedb60fbe7f960f47f6c60ec3cbe60d62fb160c0e6cc60a443556086cd7e606d82656012a1605fdbd9e55fbac6fd5fa001255f9ee40f5f64e4b85f4ce3e85f3648d1
  | 6, 13 => 0x75cef4d3756ef7e9756948e67544eddc74d57dbf74481341743386c573d82b5a73bcfd3f73bc6aed73bb015973acb1c4734eaa0d731a9a37730cc97a72db63be72d00deb72a47fc9729573027292c06c728270b4727718da7225a91b71dbb25a71d3d74b71907573716e0061713742487108872f70fe4ee070eea42e70e9cc8f70de88f270d6da3270ce3858709d46b9700515c07004d2676fceb7f16f6a8dfb6f5c19d66f4c3cf56f36ba026f10f2176ec7a3626e7acf386de954416dc17e2d6d748c516d3475df6d2c12e76d18984f6d0c81136c79ed6a6c6129046c4facab6c4b6e046c49cc986c3e88df6bfd3c4b6be903d06b9d976b6b70d1e96b4493be
  | 6, 14 => 0x7f24c13b7f1a1c937eff710d7ee241677eadd0e57e7a7cc27e63c5ee7e5243da7e4b58517e34e5be7e1a8a567e05acff7ddeb6337dd809747dc60b6b7dc594b27db173387d7d57bc7cf3e1457cea112d7c7494757c4faf817c2f60d67c0dda9d7bf8dcbf7ba594057ba3c0797b90729e7b8f3da37b7883947b657cab7b4e627f7b045a637af389fa7a8392537a5b787a7a4afe707a0303137a01223179e61c3179e5550479d3e13a79a36bfb79717a8d79613c97794b0d21792b8cc87927575878d1319678a2805c7852267d77d6a9ea77d135d077ae3ab07790fd56778560f7778424c27727b8097723c8d07710f44076f0de3376d00d2c7626fba575e62f9c
  | 6, 15 => 0x899c93cf897dd414894b34c5893fe42c893d416f88cd013b88b00c9588ab274188a82a5488972d64887d8650885e54708856311d882c7025882be4e188012a9f87ba7d7487b2ceb487ac503387a174708756c638874f01c786ade3978680741c863f7c5985f6241e85d068a285cadd8b854ecaa48538bdd2852921ce8527bd3a84fb0b2c84f5700884e60ad184dec8e884d0ea09849e475c84064fcd83533fb8834c2dc0832f5495831ab88982de7117829ec1d68276397281f6d6c28144ef408123ee88810ed63081086da0809f1ed4808528c48068a9ba8040d07880087aa87fd8d7587fca15487fc048557f8776eb7f82bf8b7f4590c97f3dc0ab7f317026
  | 6, 16 => 0x96d6a62496a49fae968d4d5f967fbfcb960bb76c960434e995e2af5795d27d409551aacc94d778219499c431947da14a943f2111940a6f839365df509322c34692904ad8928df76892806526925d2bb5919f9a929190d39c913f335d90c788869087a31f904c06a99022657e8ff17fce8fd86e468fd08d408fa3b1518fa19e1f8f6ecc898f66c09e8f2383368f1f96978eff20308ed0d90d8ebf00228e965ddb8e730e028e2b23528d869bbd8d69b98a8cad401e8c7bea548c5291f68b9be2688b4b91ec8b4b712b8b0cdb878ae257588ad177728aace1a08aa44b2d8aa3b04f8a7994f88a516cc38a4b2c568a37c65d8a0b34fc89ff1c9a89f05af589b9a4c5
  | 6, 17 => 0xa93868c4a8cca005a8cb32a4a8c90d8fa8afe02ea8a73885a8898aafa80fa957a8001edfa7eb27f5a732a1a6a632f312a55beef2a5535ce4a4add723a44de382a3c1ab4ba30ca221a2b0f0bfa29af479a29057b5a265fcc7a2487bd3a1c87a5fa181a08ea10bbc20a0d162fda0569a1ba046c73f9fce48649f828b049f2620f29ee3783b9ed6de7b9ec9ae489ec0d7899e5fc6b79dda20ac9d72dd149d58b7ee9cdfd9b79cd0c7aa9cbb54e09cad2a7e9c3d31f69c3b05cf9bf9dfd99bf3d47a9bcb613f9bca9a899bc7f7b09b6cf8b59b6512559a2468c8993824c7992cedf898e9771598ddf70098a19efa989a69279832c62697ed115a97a4f3879786f008
  | 6, 18 => 0xbb3da774bace5c64baa8c339ba5309b8b9fc935bb8ef4caeb8c9f8fbb8b12b4bb871b7fdb8405c07b7a1fd24b751bcc3b72e368bb6d8a086b6cbcc38b666254db61e9d8db6190e7ab5eebe46b50f2cb0b4bad623b4875a89b47be621b42863c4b2e6fb00b2c0fc52b2a47694b272d876b258530ab2312f64b1ce22c6b1b4fc06b0b9922fb0a47233b03d009fb03cc05ab0333b6cb01ef75bafc8849aaf8eabd5af647c31af13a005aee7287dae8bf1ddae61e220adfa5d03ad58a5d0ad3b090dac54c35babdd680fabcd69f1ab676f4fab12b296aae50a4baad16a66aaca33f1aac711ecaabd67a8aa5561f1aa00aaa3a9dd3bf7a9ba03d8a977e211a95f879b
  | 6, 19 => 0xd50bf219d468faf0d3ab69cdd3980975d23f72c4d223fd6fd201f6a4d1134f71cfaaeb5dcfa9be89cf4410ffcee24fd2ce540370cde66f1dcda6e723cd8b6b68ccd3cdb7cccf8966ccc7daa6cc26ccdbcbdfad4ecb811bc8cb7a3068cb7814d6cb32ce66caad7443ca5180ccc9eaa662c9bf6964c92a9c24c922e551c7554d2ec70d1729c6bef9f1c636a1a5c5b14e52c5821593c4cd748cc4b9fc07c4a4bbb4c4949487c40a2416c3aeb668c3606443c332008ac27d1d85c1dbd993c19e20c3c1698805c0ef573ebfb0cba3bede3efabec0a575bde1cfb5bdc979a2bce5ead5bcbbca35bc9691cebc87e6edbc4e7163bc0bddb7bbde9dddbbae1bf7bb7dc5f8
  | 6, 20 => 0xff9c5d73ff88f5fdfe69481bfb379514f8fa6c3ff8becfc9f765639df6623816f33b5fd0f317844af2b782f5f265e2cdf117a0a5f10bb195f087d5f3f03d9387ee5bfb02ecb47af8ec2b8b6ae68ed5dbe60ea2f3e5cc13a1e5702ba1e3e18a9be3cc7821e2e44efbe12fee6ae09b3ae1e05c847cdfbea839deae6443de99cc50de90f3a7de4eb049de312a05dd6b1e26dc16fe65dba78fe2daf18bb7daef5864da802b72da68f783da650bedda525ee2d9a47da2d947af79d937fb5cd87f9952d872797ad72620ccd6e8f3a9d675048ed5b9f124d52b0a13d528804d
  | 7, 0 => 0x1317dd2b12b8ab4112ae5da312798028124e263511eb7ccf11d74806119811441134c93410d1aa961094c3a5103ead2a0fc22fb60f8898390f5c5cfb0f3d84400f3badb20ea68d810e93ae780e8414b20dfe576f0da469ce0d9cbe430d52c9a60d4d98860cf91d9f0cea20e10cc7aa850cabde0a0c867e660c8323040b989d440b41c7720a9628be0a71f95609ee1b6f09eba6f40878675807bd347d0754ea1506634425064612c705c61dd605a3eb0a059e8b170590310f05869eb104d3f6f00452788e040745c60296f5790291d00a023f103c01a603fb0198251c0129b75501013f3600dd496a0086a50c006f281c0064991500368d390027347900103def
  | 7, 1 => 0x275958f2272770732705880d26beaf6f26a4b5bf265363bb264ea12126488ebe26396ad425bece64258a6ea424cb7b2924c13a83246554a623a7fde62310763b225e42212236825921e9d24d21ada82821a5f96820d196be2081cc61204aaf2d203e530f203cd04e1fd3d3851ee4e3db1eb3facb1e1aa3ae1d989e101d81c57f1ca0b1831c53b96d1b70b1901b5aa1f21b52f3321b2d157f1a5d39541a45ab1d1a4058c31a2bfa9c1a27484b1a0ece70196672e1191531f41900f42918e3fb0a181aa941175a929b17206e35170db67f16e8db1816b50ee91606144c15ff8a4715f86a801561a43a14e6b4ae1460a7d9141a4f1c13b5da6d135211a2131bfefa
  | 7, 2 => 0x3d0124c93cd7d7c23c9f3cdf3c9dc2fe3c8fe41f3c39fd5e3b3c318a3b23954e3b0787993a47663437a1ed1c378f31e8375fd1e836c744ae36ad51603678c0eb36778df5366fa272363c57f4361b1af4360aefae35d89aaa359275fc357bcd5735743559355e29ce354bc4fd3518dab134e1dc033481847a345b6585342cdee933d93c6b339be83033193e9a330961a632d2967c326a06213217690131cc3c38315024ba31381b07306d73203055c0a6302ca7772f5be1482f1362052ef010ab2ea0b9112e9e70832e8ed5cd2de85b922d014b912cf085992cb7e2692b698d6c2a9b9ca62a7c852829c478db2964176b291abe562889888f284db2db2775450f
  | 7, 3 => 0x520a3fab51efbb6051d2062b516924ff515c291951165515505beeb35038abd64ed5e3f64e9d19034e79bd534e1717654e0e9fc94e00c0ea4dd111674dc27b5b4d17706a4cfd734b4cd8ba054ca60af44c173de94bff26be4bf147df4bc969994b83735c4b7591cb4b62f61f4a3f78dc4a32c5ee4a24047e4a0d197449bfa213499cfa0a4951a01349148db048f0bd7d48ebd2aa484e6acf475141bb472e33c145f6b58445c07cca457c5ed145179a8f43a9f84843555fb0433f660a4309ffd842b779a342815d8a413ca69640db2d8b40cb4f8b40bb2834405c8f3d40455b7a3f8b9abe3ee6de3d3ebd45083e80cd693dc32c533d8620523d21e10c3d18fbc9
  | 7, 4 => 0x6e56f3256e34ebde6dcb09b56cd622c66be1bd3a6bcb63fb6bc490ee6b7c11ab6b58c0516b1be3666a5eea176a510b386a0139de69c6f98169b2eaed692e70ee6920920f67f1c0d36709aa61651506a464ffcc4e64f3896864cf00c56478994864015902639458dd6347643b63275f1562623a3561f427ee6129ea2960d158045f5d13a95f492eb65eebace45ec2fe405dc82fa15d93d62e5d6275f45d3a46645d2e415c5d23bf8f5bff541c5b4388f85b2acd5959e9c31b5905159658905d13584e132a582e7878572d859756dbe56f568ff7f15686958d567ee6cd55ab6c465423f49e53b7a8b55380fde95342fdb753169294530ec13f52942b72528ca242
  | 7, 5 => 0x98fcecee9892bda9985a34f7981b7e9296a4b77d965f3458956125c69396353d92b08ece900c696690061e318f6680978d7f04bb8c76bee98c1a6ee88c0e14188a8bfac789f226db8968a0cb8934bc8a877c8a9f872610b8869b75948651842c85f48e9f85e99b5485520fcd85210b0383c5bc5283233d808241b059804a3051804281917f5f0e0b7f27d8097dd5c4a57dad4e397d7d57bc7d356db97d33ff317d303bbe7cd372a07c439fcf7b2b17a17ab597257aa1574779a4d76c798a90b2791d9b4178f04d34785a178977211a3f76f0de3376db0b2e76b015da764692e675c5ccea74f2245d73833cd772b28339729906d472739f547260e48f6e834bca
  | 7, 6 => 0xd27a66b2d2746762d0e5095fd0317033cea2794cca35eab9c7ad77bcc7466283c707ac1ec62e45d3c61b5c10c5dca5abc59d6c30c52f7576c4eae2e7c4c107afc4ac2c82c4605fcec21dcfbbc1c6e06ec047fa35bef4bb49bef1afedbe4be64fbcc8e334bc5e25f5bc4e7163bbec3344bafa41a4b9fc935bb9782853b89ec208b84d21e0b7a3f583b559ed2fb4e46fecb32b1ae2b2a58f0eb242b686b1b17014b18cc501b12375bdb0f51e5bb04d71d7af01b67aaed71d6aaec64c0eadab993dac3ab49dac100e7aaabfa2cbaaa935daaa8df529aa38618da9cb11c2a8098f40a6c41187a4dede88a4a02823a309310c9ffd08839eab30d29ce015509985b807
  | 7, 7 => 0xfc3e0176fb7259a6fab495f5f8b72109f117a0a5f109fd47f087d5f3f03d9387ee03301aeb3fcd10e9d3bc26e8b54ab1e878be20e606f433e2f02cffe1b1f408e0d9cf49df71e0b2dede789bdec49712dd114471dd0995b1dc984483d6e961fcd56748ab
  | 8, 0 => 0xf2854adfbad4da24b47be6218ab84b5d7e6c2a7e51bb2a0f4f8c57c24aee737942b779a33e277fff2eedfa851e7359ed1729918f1606144c1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0xc5424493033708115480400000d95210130100000000000060004125440303000d952101301000414544030300000521012016708135480400000d95110130247580314414000008135480300000005210120100184434c9301000d952101301
  | 4, 0 => 0x27580314c14003758021481400001181044030000000434c9201000414544030000000000c51020000051480202000003150920300188434c5302000d9511013020000000101102000000000000400000511012020004135440301000d9511013020018d521013010000000000005000d9100413010000000085106000d95210130100000000c5103000005110d2010000051101201000495044830300000000000050000020480201000000010d102475803144140000000001091030018442449300000d9521013010000000008106
  | 4, 1 => 0xd9420853010000042481203000001548020000099300c1302000000000000500184454c13010004145440300000000000000500000000000036704145440400000d952101301375804248140000188434c93010000020480200000d950109300000813548030000000000000050008135480300000d95210130100000000000040000000000006000004544820300000000c91010000035508201000000000000500000454c8200000000010110200041254403030000045448203000813548030000000000000050000000000005
  | 4, 2 => 0x40008135480300000000000000437081454804000000042481203000000008510600000434c920100000000000050004145440303670813548040000081354803030008135480300000000000000500000521012020000000000005000000104120000041354403010000045408200000000000000400188504c53000000052101201000000000000600000000851060008135480303000005210120100081154803030000000000006000003148520300000310c52000000000000005000000008510600099500c5300
  | 4, 3 => 0x414544030000081354803030008135480302000d951101302000811548030000099300c13020000020480201000813548030000184434c5302000000000000627580434c14000004145440303000005110d20137580214814000000000101101000000000000500000424492030004145440300000d95110130000000000000060000051101202000005210120100000434c9201000000000000500000521012010015831501302000855048430300000000000050000000085106475801244140000184434c53020000000000006
  | 4, 4 => 0xd95100a30000114424813000000025440200000d43148530000000434c92010000000000006000855048430000000000c510500188454c130100000204802020000000085106000001044020327580434c1400000d9100413014758031441400000813548030300000000851060000045480200000003550820137580214814000018d511013020000000000006000d952101301000004544020000188434c530200000511012023708115480400000813548030200000204802010000000000005000d95110130200000434c5202
  | 4, 5 => 0x3000d9511013020000051101202000000010d1020000000000005000000000000000000000000050010931485303000d95210130127580434c1400475803144140000184434c5302000000010110100000000000060000010440202000414544030027580314c14000015831501302000000000000600041454403030000000000006000813548030300119520c130017580425014000018031441300000995110130000188454c1302001583150130200184434c9301000000000000200000000c51050008135480302
  | 4, 6 => 0x567081354804000000000000004000000000000500000000c910100184454c13010000000085106000813548030027580314c1400
  | 5, 0 => 0x600184434c53020000000000000000811548030000000000000010000000000006001804248130000000000000040000000000000000003550420200000000c0105000d9501053000000000000004000003548420300000000c9105000000000000100000511012020000000000005000813548030000000420c920100000001081010000000000006001802148130000000000c11000000000000002001801244130000000354402000000031441203000000010d102000000000000600000000c01050000035508201
  | 5, 1 => 0x355082010000000000000000005110120100000000000040004135440301000005210120100000000c5105000002048020100000355042020008135480300000001044020000000000c51050000000000004000000000000500000544c520000000000000010000000000005000000000000500000254402010000051081202000001044020100000300c120200000000c5102000000010110100000001011020000000000005000000000000400000511012020000000000005000000010d10200000000000000000000000005
  | 5, 2 => 0x40018450509300000000000000600000254402020000000000000000000000000500000511012010000000000001001583250130100000000000040000000000004000000000000100000000000050000000000006000000010410100000000000010000042449203000000000000500000000000060000000000006000002544020000000434c5202001804144130000000521012010000020480203000d85148130000000511012020018835441300000d952101301000811548030000000000000020000010440203
  | 5, 3 => 0xd9521013010000000000000000000000000600041454403000000020480203001803450130000000000000060000000000003000000000000600000000c51050000052101202000005210d202000811548030000000355042020000000000002001804248130000000001011020000010440201000000000000500000000000040000021484200000005210d2020000000000005000005210d2010000000000006000005210120200000354802020000000000000000000140420100000000c510000000434c92010000000101101
  | 5, 4 => 0x300000450412030000025440202000000000000500000521012010000000000003000000010d1010000045480203000001044020100000355042020000000000000000000000000600000434c5202000000000000500000521012020000000000005000813548030000000000000050000010041202000003548020300000000000020000005909200000000000000400000001041000000000000000000005110d20100000254c020100099500d1300000000000000000000520412010000000000004000005210d202
  | 5, 5 => 0x119500493000000000000004000000008510300000000411030000000000004000005110120100000204802010000000000006000000000000500000000811000000000000004000002048020100000000000020000000041100000005210d201000000010910300041454403000008135480302000000000000000000104402020000000000006000000000000000000000000050000000000006000000008010200000454c1201000004544020300000000000050000035081202000d95110130200000000000050000000000002
  | 5, 6 => 0x50000000000004000000000000000180424813000000000000005000d950105300000002544020100000000000050000000000006000005110d20100000354802000000000000006000000000000600081354803000000000000001000000000000500000434c52020000000109100000005050820200000000000000000000000004000003250120100000000c510500000434c5202000000000000600000315012020000021484201000000010d1020000000000004000000000000100000000000060000000000005
  | 5, 7 => 0x50448203000000000000000000000851060000000040101000003544020200000000c9101000000000000300081354803000000000080102000000000000500000000000060000012448200000000000000400000204802030000051101201000002540420200000521012010000051101202000000010910300000000c51020008135480302000000010d101000002048020100000000000050000051109200000000000000400000511012020000035480203000003544020100000000c910600000000801020000000000006
  | 5, 8 => 0x6000001044020300059500c93000000035002200000000000000400099500c53000000000000003000003548020000000000000060000000000000000000000000000000000000040000000000000000005210d2020000000000000000005210120100000450812010008135480302000000000000500188434c930100000000c51030000035480200000c930481300000000010110200000204802020000045448200001804150130000180414413000000035440201000005200620000000000000040000035440200
  | 5, 9 => 0x10440202000000000810000000000000040000000000006000000000000600000000000060008550484300000000010110100000000411020000000000002000000000000000000000c9106000005210d20200000511012000000045480203000d95010930000000000000050008135480300000000010910300119058413000000010440202000000000000400000000000000000000000006000001548020200000000000040000051101202000d4214813000000015480202000000000000400000001011000000000000003
  | 5, 10 => 0x40000000000001000d90588130000000000000030000000000003000001244820300000000021000000035440202001181044030000000000000040000000000000001442148130000000001011020000000000006000003540420200000001051000000020081201000005110d20100099500d13000000045041202000000010810000000000000040000000000004000005210120200000154c02010000000101101000000000000000000254402030000035440203000003548020000000154c02010000052005201
  | 5, 11 => 0xd91500a3000000000000002000000010d101000000000000400000454402000000000000000000002048020100000354402000000000000000000000000000000000001091030000000000005000000000000300000324c82010000035440202000000000000000000104402020004145440300000000000000500000434c52020000025440203000000000000500000300c120200000000c910500000204802010000000000006000000000000400000000c910100000434c92010000020480200000c9304813000000000000003
  | 5, 12 => 0x4000d9058813000018021481300000000001210000184434c5302000000000000200000354802030000010440201000002148420100000000061000000051101202000005210d2020000000101102000000000000400000410c520200000000000050000000000005000000000a10000000434c920100000000000020000045480203000000000000100000000000040000000000004000000000000100000204802000000052101201000000000000300000000c5103000000000000200000000000040000020480200
  | 5, 13 => 0x40000000000006000c930481300000414544030000099500c5300001804150130000000000000040000035508201000000000000400000000000050000052101202000d82048030000180314c130000000434c920100000000c11000000000000004000412544030000000000000040000010440203000005210d2010000045480200000000000000400000521012010000000000005000000010110100184434c930100105404413000000000000000000000008010100000000000040000000000006000000010d101
  | 5, 14 => 0xd950109300000000010d10200000000000060008135480300000001508120200000454402030000000000001000000008d105000000000000600000000c9101000004244920000000000c4101000000000000400000000c510200000454c12020000000000000000003544020000000304c0201000000000000400000000000040000051101200001804248130000000450812020000041049202000000000000600000501092000000015480202000005110120000180324c1300000003548020300000000000050000000000006
  | 5, 15 => 0x140420200188434c9301000000010d1010000000000004000005210d20200000000000050000000000005000000000000300000521012010000052101202000005110120100000521012010000000000003000000000000600000254402010004135440300000003548020100000154802030000000000001000000008110300000511012020000035440200000d4424813000000000006100000995010530000000000000050000000000006000d95110130200000154c020200099058c130000000000000000000035484203
  | 5, 16 => 0x2048020200081354803000000035440201000000010d10200000000000000000000000002000000000000000000000000010000015480202000002048020100000314c120200000355082010000000101102000000000000400000000000060000000000004000002048020100000214842000018042501300000003144120300000000c91010000010440200000000000000300000000000030018442449300000000008510600184454c130100000000021000000000041100000003148520300000424492030000000000006
  | 5, 17 => 0x30018c454813000000000000004000000000000500000434c52020000000000001000005110d2020000035081200000000000000400000450c92010018021481300000000000000300000450412000000035480201000000000000300000000c510300000511012020000000000001000000008510000000000c51020000000000004000002048020300000000000060000035081202000003148520300000204802000000025440200000004548020300000000000010000000000005000001548020100059500c9300
  | 5, 18 => 0x20000000000002000595010930000119500c530000000434c5202000000000000400041454403000000000000005000001548020000000204802010000000000006000d9500853000000000000003000000010d1000000052101201000000000000000000000801010000000000005000002148420100000000000060000000000004000d951101302000000000000600000154c02020000000000002000001004120100000000c5103000005210d2010000045440203000002544020000000000000040000000000004
  | 5, 19 => 0x2544020100000001091030000000000001000002544020200000354802010000000000005000000000000400000000000040000000000005000000000000600000000000060000000000005000000000000600085504843000000000000003000000000000500000505082010000000000005000000000000600000354802020000000000003000000000000400000434c52020000000000003000000010110200000001091030000000000005000d9501053000000020480201000000000000400000324c12010000000000004
  | 5, 20 => 0x4250120000000000c510300000000c51050000000000005000003540420000000000c510300180434c130000180414413000000045480200000000000000500000104402020000000041103000000010d10200000000801000000000000004000000000000400000000000050000000000005000000010110100099500c53000000035480200000000000000200000434c92010000020480201000002048020000000420852010000000000004001803248130000180314c130000000000000040000000000006
  | 5, 21 => 0x4000004504920200081354803020000035081200000000010910000000001091000000021484203000002048020100000000000060000051081202000000010d10200000000000030000000000006000000000000300000214842030000000000006000001548020300000001011000000000000005000000000000500085504843000000015480200000d9521013010000000000005000000000000600000254402010000052101201000000000000400059500c930000000000000000000000000005
  | 5, 22 => 0x4000000010110200000000000060000000000006000000000000300000000000020000045480200000000208120000000000000050000000000005000000010d10100000000000050000015480203000001044020000000000000050000000000001000000000000000000000000060000000000005000000000000500081354803000000000000006000000000000600000000000040000025440203000002048020200000000000030000000000005000000000000300000000000030000000101102000005110d201
  | 5, 23 => 0x5000002148420000000000c01050000045440203000000000000500000511012020000000000001000004504120000000000000050000000000005000001044020000000504c5200000001548020100000000000000000000109103000000000000400000154c020200000000000050000000000000000000008d10600000001011020000000000006000000000000400000000000030000000081101000000000810000000354402010000021484201000000000000400000454c82000000020081201000d820480300
  | 5, 24 => 0x521012020000000000004000002008120100000000000030000000000004000005048420000000154c020100000000801060004135440300000d9521013010000000000001000000000000400000000000060000010440201000005210d20100000104402020000000000004000000000000300184454813000000031441200000000000000400000254402010000000000005000000000000600000000000000000031441203000003550820100000000000040000035480200000003508120000000000000000008135480300
  | 5, 25 => 0x300000524c5200000000000000300000315012020000000000004000000000000000000000000050000015480200000005110120200000454c1200000000000000600000000c9101000005050420200000454802030000000000001000000000000200000000000000008135480300000004548020300000000000040000025440202000414544030000000000000050000000000005000003508120200000000000060000012448202000813548030000000000000050000035504202000595010d30000184434c5302
  | 5, 26 => 0x454c120100000000c010200000254402000000000000003000000000000000000000000020000000000001000d95008530000000000000000000020081202000000000000100000000401010000000000003000000000000000000000c5100000003548020100000000000000000035480200000000000000300000000000000000000000000000005110d20200000424c5203000001244820100000000000040000000000003000000000000500000000c91010000000000003000000000000200000000000050008135480300
  | 5, 27 => 0x21484203000003548020200000000000050000000000000000d9511013020008135480300
  | 6, 0 => 0x5110d20100000314852000000052041200000000004910200000000000010000000000005000000000610200000000021000000000000005000000010d102000000500a2000000000000006000000000000600000254402000000000049102000000000210000000000c9100000000000000000000000c5102000000008510100000000c5102000001244120000000434c92010000000049103000000008010100000000401020000000000005000000000e10100000000c9101000000004110100000000000060000031441200
  | 6, 1 => 0xc9101000000000910200000000021010000000105100000000000210300000154802010000000085106000000000000600000000000050000010440201000000010d101000000008110100000434c52020000000080102000000588520000000304812000000000000000000000010d102000000010d1010000000081100000000000e103000000000000300000000000010000000000006000000000000500000454c1200000000000610300000254402000000000101102000000000000200000000000010000045449200
  | 6, 2 => 0x4000000000a100000000000a102000000000210200000104402000000035480201000003548020200000434c120000000000c410100000000411020000000000001000000010110100000000c51000000000000000000000004910200000000000050000000109103000000000000100000001011020000000000006000000010410100000000401000000000000002000000000000100000000811020000005881200000000004010200000000000050000000006103000005244120000000000c51010000000108100
  | 6, 3 => 0x21000000005909200000000010810100000000000010000000081100000002500220000000000121000000000000005000000000000200000000811000000000080102000000008110000000000000040000000000004000000000000300000000c410100000434c5202000005210d20100000000c110000000000000060000000000000000000004010100000000411030000000000006000000000a101000000000a1030000000000006000000008410300000454c520000000000000040000000049100000000008d105
  | 6, 4 => 0x204802000000000101101000000000a100000000004110200000454802000000000000006000000000610000000124482020000000000004000005210d202000005210120100000000000040000000000000000000000e10300000000c910100000001011010000020480201000000008010200000000c11000000000000004000000000000500000000c4100000000000a10100000000c91010000000000005000000000000200000001011020000035509200000000004010100000500c520000000000000030000000000000
  | 6, 5 => 0x100000000c110000000354402000000000000001000000000a1000000035480200000000000000600000000411020000000012100000000008010200000500c92000000045402200000000000000500000000c8100000004540220000000104402000000045041200000000000a1000000000000001000000000000500000500d1200000002148420000000001051000000000000005000000010d1010000000000006000005210120200000000401020000000000001000002540220000000104402000000000000006
  | 6, 6 => 0x314852000000000041101000000008d10500000345092000000000085103000000588520000000000000060000041501200000000000000500000000000010000045440200000000000000200000001081010000000080106000000000000500000000021000000000000005000003504120100000001051000000000000002000001548020000000254402000000000000005000000000e10100000000411030000035480200000003544020100000000000020000000012100000000000000100000000811020000000002100
  | 6, 7 => 0xc110200000000851030000000080103000000000000100000058c5200000000000000400000000c11010000000000004000000000a1010000005841200000000480a2000000000006103000000000000100000304812000000000101100000000000000400000000000050000035441200000004548020000000000000040000000000004000000004910100000154802010000035441200000003548020100000000c11000000000000006000000000e1010000000040102000000000e10300000000000060000020480200
  | 6, 8 => 0xc910000000000000020000000000001000000000000400000000c910100000000000050000000000003000000000000300000001011030000052101201000000000a100000000008510300000000c5101000005050920000000000000040000000000001000000000000600000000801020000000104101000001548020000000354802000000000000005000000010d10100000000000060000000000005000005044820000000000c810000000000851010000035485200000000000000500000000000050000000000002
  | 6, 9 => 0x2100000000000000100000000000030000000109103000000000000500000000061000000031441200000000010d10100000000000060000045041200000000010110300000001011000000000000005000000000000600000000000020000000002100000002148420000000354812000000000012100000001044020000000000411010000000000004000000000610100000000c110100000254402000000000000004000000010d10200000000000040000000000002000000004010000000000000040000012448202
  | 6, 10 => 0x6100000000010910300000454c5200000000008010200000000000000000005909200000000010110300000434c52000000000000005000000010d102000004544820000000000000060000000000000000000590d2000000000000006000003544120000000001041010000000000006000005210d201000000000210000000000061000000000104102000000000000500000000c910000000000000010000000101100000000000000100000124412000000000000005000000000000400000000000050000045441200
  | 6, 11 => 0x38122000000000101102000003548020000000000c91000000000000002000000000000000000000000010000000000003000000000000200000000801020000000104102000001548020200000000000040000000000005000000480a20000000000000060000000000005000000000000200000000000000000035480200000000000000100000204802010000020480200000000004810100000000c91010000000000006000000380a20000000001011020000000000000000000004110000000000841010000000006101
  | 6, 12 => 0x104402010000000002101000000480620000000000c510300000001011020000000002100000000584120000000000811010000000085100000005010520000000000c9100000000000210300000000c910100000000c510300000434c12000000000105103000000010d1010000000000005000000000000200000000000000000000000005000000000000500000000c510000000001081010000000041101000000000000100000000000060000000002100000000010d10200000001011010000000002102000000000a103
  | 6, 13 => 0xa102000000010410100000500c52000000000000001000002048020200000000c11010000000000005000000010d103000001044020000000001011010000000002101000000008110300000000000020000015480201000000000000400000000000020000000000003000000008110000000000c11030000035440201000004544020000000000000000000000002100000003544020000000000811010000051101201000000000000500000000000050000000081102000005210520000000000000050000000000005
  | 6, 14 => 0x2100000002544020200000000000010000000000005000000010d10200000001091030000000000003000000010d102000000000210100000000c51000000000000003000000004110300000000c51000000000000002000004548020000000000c510100000000000050000000000005000000000a10300000150022000000000000006000000000000600000000851000000000000005000000010110200000000000060000015480202000000000000400000000c510300000000c510000000000c11030000035509200
  | 6, 15 => 0x200000000d1103000003250120100000000401020000000000000000000010110100000000000000000000000000000000008410000000058c12000000035440200000000000000400000204802000000021484200000000000000200000000801030000000000005000000000000400000000000040000000040101000000010110100000354402000000000081101000003544020000000000811010000021484201000000000000100000000801020000010440200000000004910100000000000060000000049100
  | 6, 16 => 0x4544020000000154802010000000041100000000000000600000000061010000000085101000000008110100000059052000000004806200000000010d100000000000610200000000c110100000000c1103000000004110000000000000050000000000006000000000000500000000411020000000000005000004248120000000254402000000015480200000000004110000000038062000000015402200000000004010100000000000010000025440201000000180a200000000000000100000000000010000000002103
  | 6, 17 => 0x1051000000000000001000001500a200000000000000500000000000060000000109103000002544020000000000021000000000000000000000010110200000000000050000000000000000000000000300000000000030000000000005000000000a1010000000049102000000000a103000000000000200000000c510000000000000050000050484200000000004910200000000000060000051101200000000000000500000000000040000015480200000000008110100000000000050000012448200
  | 6, 18 => 0x590920000000434c520000000001011030000000084101000000010910300000454802000000051101202000000000610300000000d110300000000121030000000000000000000000000400000001011010000000002101000004544120000000000491000000000000006000000000000000000000000020000000108102000000000000500000000000010000000000005000000008010300000204802000000000002103000000000a10300000000000020000000000005000000000210000000000c9103000000000e101
  | 6, 19 => 0xa1010000010440200000000008010100000000c91030000003802200000001548020000000000c51020000041441200000002540220000000001081010000000002103000000000000400000000000050000000108102000002048020000000038022000000045440200000000000000300000314852000000000006101000004250120000000000000020000000081101000000380a2000000000101102000000008110000000414412000000000000000000000010d101000000000000300000204802020000000000004
  | 6, 20 => 0x454c1201000000000000000000454402000000000000005000000008010000000000000050000000109100000000000000500000000000050000000000004000000000000500000000c1101000000000000300000000401020000000105100000000000a10000000000c1103000000004010200000000000010000045402200000004244920000000214842000000000000004000000008010000000001051030000000000004000000000e101000000000e1030000025402200000000000210300000000000030000005885200
  | 6, 21 => 0x500000000000060000000000006000000000000400000001081020000000105103000000000e10200000000000020000000000005000000000a10300000000c110000000000021030000010440202000000000000400000000000040000000006101000000000000000000000c9101000000000e10000000000811030000000041102000000000a100000002544020100000000c410000000254402000000000000006000000000000500000354402000000000000006000000001210000000000851060000051509200
  | 6, 22 => 0x600000000000020000000000004000000010d10100000000c510100000000061030000035440200000001548020000000000c1101000000000a102000000000000200000324c1200000000010110000000000000050000000080103000000000210000000000000020000000000000000000008410100000000c9102000003548420000000000000010000021484200000000004910300000000c910100000434c920100000000c510100000000000010000035480200000000000000000000000c51020000010440200
  | 6, 23 => 0x2000004504120000000214842000000045440200000005110d20100000058c12000000000000005000000000000400000000411020000003806200000005110d20200000504842000000000041103000000000e10000000000c910100000000000050000000109100000000000a10000000000c910600000000000050000000009101000000500a2000000000000000000005010d20000000501052000000025440200000000010410100000058c12000000000101101000000000210100000000000050000000081102
  | 6, 24 => 0x434c9201000000010510000000000000050000000000000000003508120000000000c51000000025440200000000000410100000000061010000000000002000000000610300000314c1200000000000000600000000c110000000000c51030000000000002000002148420000000000000060000035480200000000000000200000000c91010000000000004000000000000500000000021020000035402200000000001210000000524412000000050085200000000000000500000000000010000000000005
  | 6, 25 => 0x50000000000001000000004010200000000021000000000002101000000380220000000000801030000000000005000000000610300000000000050000000000005000000000000500000000c5100000000480220000000000000050000000012100000000008010200000000000050000000000006000000000000000000511012010000042449200000000000a10000000000c510300000000000050000000006100000000008110000000000000000000000000000000000280220000000354852000000000085101
  | 6, 26 => 0x4000000000000400000000c51030000000040103000000000000500000254022000000000101103000002544020000000000000060000021484200000000000610300000000000060000000084101000000010d101000004250120000000000801020000000000000000000000000400000001091000000052101202000004548020000000000411010000000006102000000000000600000000000040000045480200000000000000300000000000050000035480201000002148420000000000c01010000000000006
  | 6, 27 => 0x300000000000050000000000005000000010d10000000000000050000000000006000000010910300000000c01010000000000006000000010110100000000000050000000000005000000000000400000000c0101000000584120000000000c910100000434c9201000000008010300000000c51010000045402200000000000000200000000000050000000041103000005210120100000500c5200000000008110200000000c510000000000000060000000000005000003544120000000000000050000000048102
  | 6, 28 => 0x31441200000000010d10200000000411030000025440202000000010410200000354842000000000081101000000010410100000104402020000010440200000005210d20100000000000020000000101100000000000a10200000000000060000000006100000000000000400000454c12000000020480200000000180220000000000811010000000008101000000010d1030000000048102000000000000400000000c1100000000000000600000000c11010000000002100000000000000400000000000040000000104102
  | 6, 29 => 0x5000000000a1010000045440200000000500a20000000000000050000000048103000000000000100000000000040000000081102000002544020000000000c51000000000000002000000590520000000000000000000000101102000000004110000000000000010000045440200000000590d2000000000000004000002148120000000000000000000012441200000000010d102000000010d102000003144120000000000000040000000006103000000000000300000434c9201000000010d1020000052505200
  | 6, 30 => 0x50000000101102000000000000200000354802010000045480200000002048020100000000000010000000041101000000000000000000001011020000000000006000000000000600000254402000000000000001000000000e10100000058c1200000003544020200000000c510300000000c1102000000000000400000000000060000000000005000000000000500000000000010000000000005000000000a10300000000c510200000000000010000000080101000000008510000000504c92000000000000005
  | 6, 31 => 0x3000003548020000000404412000000000000006000000000000100000000c510100000000000060000000108101000000000e1000000000101102000000000a103000000008010300000000000030000000101102000000000000000000058c92000000000101102000000000210200000511092000000000109103000000008110100000354802020000000000001000000000000400000000c1101000000000a1020000035081200000000010110100000000000000000051101201000005210d2020000000000005
  | 6, 32 => 0x3812200000000010110200000000c51030000000080101000000000210300000001011020000000080102000000000a102000000000000400000454492000000000085101000000010d101000000000000400000000000050000000000006000005210120100000354402010000000000005000000000000500000000c11020000052101201000000008510600000000c9101000001044020000000000841000000000040101000000008d1010000000000004000000000a102000000480220000000000c01010000000000005
  | 6, 33 => 0x105103000005110d2010000000000005000000000210200000000000050000000101101000000000a1030000000000004000000000a101000000000000500000000000040000000000000000000000610300000454802000000035480200000002148420000000000000000000000081102000000000000600000000c910100000000c910100000000000030000000000004000000000000400000000021000000000000000000000000610200000000c51020000000109103000000000000400000000000060000000000005
  | 6, 34 => 0x400000000000050000000000005000000381220000000454412000000000012103000000000000600000000c5102000000010d101000000000000300000000000060000000000006000000008110100000504852000000000006103000000000000600000000000020000045041200000000000000400000000000040000000000005000000010410100000000000030000000002101000000000000600000001051030000000000002000000000000600000000c1101000004544020000000000000010000000080101
  | 6, 35 => 0x10d10100000000851030000000000005000000000000600000000411020000050085200000000004010300000000000010000050085200000000008110100000000c510200000000000060000050484200000005010520000000000041000000000000004000000000000500000001091030000000000006000000000000200000000021030000000081101000000000000000000454402000000000085101000000010d100000004548020000000000000010000000000001000000000000000000000851010000000040101
  | 6, 36 => 0x20000020480202000000000000200000000000050000000000003000000000000600000324c1200000005210d20200000000021010000000081100000000010d10200000000061030000020480201000000000e101000000000000500000000411020000000000002000000000000100000000c5103000002148420100000000000040000000085103000000000000500000058c920000000000000020000000101100000001548020000000514812000000000000000000000010d1010000000000002000000000e103
  | 6, 37 => 0x500000314c1202000004544920000000000c91010000000000001000000010d1010000000000005000005210d2010000000000005000003544020000000000000010000000040102000000590d20000000000061030000000109103000000000000500000000000030000000084103000000010d10000000354402010000020480200000000004110300000000000010000000000006000000008110000000000000060000000000006000003544020000000000c9102000005010920000000000000040000052101202
  | 6, 38 => 0x30000000000001000000180a200000002544020000000000000020000000000005000000008510000000000000050000000000000000004250120000000000000040000000081101000000000a10000000000000030000000000004000000010910300000000c1100000000000000600000000000040000000000006000002544020000000000000050000045448200000000000000400000000000050000000085101000003548120000000000021000000000000006000003248120000000001011020000000000003
  | 6, 39 => 0x2000000000a100000000000a10100000000000050000041441200000000000000600000535052000000000109100000000000a101000000010d1030000000000003000000000000200000000000020000000006103000001548020000000000000050000000000004000000010110100000000021010000000000005000003548420000000000c010200000001011020000015480202000000000a100000000000000100000000000050000000000003000000000a102000000000000600000000000050000000049102
  | 6, 40 => 0x400000000000040000000006103000000000a100000003548020100000000000060000000000004000000000000200000000c1103000000000000500000000841010000045440200000000000000400000355092000000000000003000000000000600000000000050000000006100000000010d10200000000c11010000000000005000000010d1030000000000001000000000000500000000801010000002802200000000010d10000000000000030000002802200000000010110200000214842010000000000006
  | 6, 41 => 0x84103000000000e101000000000000000000000c11010000000002100000000000000000000000000050000000002100000000010d1000000000002102000003544020000000000000050000045480200000004548120000000000000000000000084101000005148120000000000000000000034509200000000010d100000000010110100000000000020000021484200
  | 7, 0 => 0x6100000000000000000000000481010000000002100000000000000200000000411000000000006101000000004110100000000000020000000000006000000000000500000000000050000000081102000000000000200000000000010000000109100000000010510000000000c510100000000841000000000041102000000010d100000000000a101000000000a100000000000000000000000000010000000000002000000008110000000001011000000000049100000000001210000000001051000000000000002
  | 7, 1 => 0x21000000000000000000000000000100000000c910000000000000010000000081102000000000210000000000c110000000000c9100000000000a100000000000000300000000000020000000041100000000001210000000001011000000000000006000000008010200000000d1100000000010d1020000000000005000000010d101000000000e1000000000000006000000000000100000000811000000000080101000000000e1000000000000005000000000a100000000000610000000000841000000000048100
  | 7, 2 => 0x600000000801000000000085100000000010110200000000021020000000080101000000000000200000000c510000000000000010000000049100000000000000300000001011000000000006101000000004010000000000c5100000000000000000000000c910100000000000050000000000006000000000000600000000061000000000002100000000000e10000000000000060000000000002000000000a100000000010d1020000000000003000000008110000000000c110100000000801000000000002100
  | 7, 3 => 0x50000000041100000000000000100000000021000000000084100000000000000100000000c9101000000000000100000000000010000000006100000000000610200000001051000000000002100000000000a10000000000c510100000001011000000000000003000000000a10200000000c110100000001011020000000002102000000000000100000000811000000000041101000000000000200000000411000000000000002000000000000200000000c11000000000080100000000000a1000000000002100
  | 7, 4 => 0x100000000000060000000000000000000000e1010000000000003000000008010100000000000030000000109100000000000a10000000000c9100000000000e10000000000c1102000000000a10100000000000020000000085100000000010d10000000000061020000000000001000000000000200000000c5100000000000000200000000000000000000040100000000000a10200000000000030000000006100000000000000600000000000060000000000005000000000a10200000000061020000000109100
  | 7, 5 => 0x20000000101100000000001210000000000c51010000000105100000000004910200000000000010000000000005000000000000300000000841000000000048102000000000000200000000801000000000000006000000000000500000000000000000000000003000000000000600000000c11000000000080100000000000000000000000000000000000000003000000000000200000000c51000000000109100000000000000500000000000010000000000002000000000000500000001011020000000012100
  | 7, 6 => 0x10000000000003000000000a100000000000a1020000000084100000000000000400000000021000000000041102000000000e102000000000000400000000021020000000000001000000000610100000000000050000000000002000000004110000000000000000000000109100000000010910000000000411020000000081100000000010510000000000061000000000085100000000000a100000000000610200000000000020000000000003000000000000100000000c110000000000000010000000000002
  | 7, 7 => 0xc91000000000000006000000000000200000000000010000000040100000000000a100000000000000500000000401010000000081100000000008410000000000021010000000000005000000000000100000000c11000000000049102000000000000600000000811010000000006100000000000000600000000c51020000000006100000000000e10100000000121000000000105100000000000000000000000401020000000002100000000000210100000000021000000000000000000000000e1000000000000001
  | 7, 8 => 0x10510000000000000010000000084100000000000000200000000841010000000000006000000000a10100000000c1100000000000000200000000000060000000000005000000010d1000000000012100000000000000500000000481020000000105100000000000a100000000000000300000000061000000000000005000000010110000000001011010000000002101000000000000500000000000030000000085100000000000000600000000411020000000040100000000000e100000000008510100000000c5100
  | 7, 9 => 0x3000000010910000000000c9101000000000e100000000000a100000000000610000000001051000000000085100000000010d1000000000000001000000000000100000000c510000000000c11000000000000003000000000a1020000000040101000000004010000000000121000000000000002000000000a1000000000000001000000000000100000000c910000000000000050000000041100000000008110000000000000050000000002100000000000000500000000000020000000002100000000010d100
  | 7, 10 => 0x21010000000006100000000000210000000000c11020000000101100000000000000500000000c1100000000008110000000000061020000000085100000000000000500000000000010000000085100000000000610000000000c910100000000c5100000000008110200000000000050000000040100000000000e1010000000002100000000008110100000000841000000000000002000000010d10200000000c1102000000000000100000000411000000000085100000000000000000000000021000000000080101
  | 7, 11 => 0x109100000000000a10000000000c510100000000000050000000080100000000008410000000000000010000000006100000000008410000000000801020000000000005000000010d100000000000a100000000000000000000000851020000000105100000000000000500000000c9101000000000a10200000000000030000000085100000000000a101000000000210000000000c51000000000002100000000008410000000000c91000000000040100000000000210200000000c910200000000000040000000101101
  | 7, 12 => 0x50000000006100000000010910000000000811000000000000002000000000210000000000000010000000000001000000000a100000000000000400000001011000000000000000000000008510000000001051000000000000002000000000e10000000000000050000000006100000000010d100000000000210000000000000050000000080100000000000000100000000801020000000000003000000000a1010000000000006000000010d10000000000811000000000000004000000000a10100000000c5100
  | 7, 13 => 0x84101000000010d102000000000a1020000000041100000000000a1010000000000001000000010d100000000008510100000000000050000000084100000000000000100000000000050000000080100000000000a100000000004010100000000000000000000000005000000000000200000000c5101000000000000200000000c110000000000000020000000002101000000000210000000000000020000000000002000000000210000000000000020000000085100000000000000100000000000050000000040100
  | 7, 14 => 0x84101000000010d10000000000021000000000002100000000000000600000000851010000000000000000000000000600000000000010000000105100000000000a100000000000210100000000061000000000002101000000000210000000000000060000000012100000000010d1000000000002100000000000e1020000000101102000000000210200000000c510000000000801000000000000004
  | 8, 0 => 0x1000000000000100000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_5 roots_5 8 s ws hint
  | 1 => checkCutEntry dom_11 roots_11 7 s ws hint
  | 2 => checkCutEntry dom_12 roots_12 7 s ws hint
  | 3 => checkCutEntry dom_18 roots_18 7 s ws hint
  | 4 => checkCutEntry dom_19 roots_19 5 s ws hint
  | 5 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 6 => checkCutEntry dom_2 roots_2 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_20 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_20 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_20 == dom_20) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_20 goalM u ys) : RunD dom_20 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_20 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
theorem z3_16 : ∀ i, 16 ≤ i → i < 24 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_24 : ∀ i, 24 ≤ i → i < 32 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 24 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 32 → Z 3 i = true := range_split z3_0 (range_split z3_8 (range_split z3_16 (z3_24)))
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
theorem z4_136 : ∀ i, 136 ≤ i → i < 142 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 136 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 142 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (range_split z4_48 (range_split z4_56 (range_split z4_64 (range_split z4_72 (range_split z4_80 (range_split z4_88 (range_split z4_96 (range_split z4_104 (range_split z4_112 (range_split z4_120 (range_split z4_128 (z4_136)))))))))))))))))
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
theorem z5_336 : ∀ i, 336 ≤ i → i < 340 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 336 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 340 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (range_split z5_200 (range_split z5_208 (range_split z5_216 (range_split z5_224 (range_split z5_232 (range_split z5_240 (range_split z5_248 (range_split z5_256 (range_split z5_264 (range_split z5_272 (range_split z5_280 (range_split z5_288 (range_split z5_296 (range_split z5_304 (range_split z5_312 (range_split z5_320 (range_split z5_328 (z5_336))))))))))))))))))))))))))))))))))))))))))
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
theorem z6_456 : ∀ i, 456 ≤ i → i < 458 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 456 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 458 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (range_split z6_376 (range_split z6_384 (range_split z6_392 (range_split z6_400 (range_split z6_408 (range_split z6_416 (range_split z6_424 (range_split z6_432 (range_split z6_440 (range_split z6_448 (z6_456)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z7_192 : ∀ i, 192 ≤ i → i < 197 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 192 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 197 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (z7_192))))))))))))))))))))))))
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
  scr dom_20 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_20 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_20 roots_20 goal_20 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_20 goal_20 := by
    have h0 : isConstB dom_20 goal_20 = false := by decide +kernel
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

end S_20

theorem low_20 : Lower dom_20 roots_20 goal_20 10 := S_20.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_20_bits : ∀ r : Fin 64, roots_20.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_20_lt : ∀ r : Fin 64, dom_20.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_20 T)
    (hlow : Lower dom_20 roots_20 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_20, Avail mask256 roots_20 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_20 hfan 0 roots_20 roots_20 rfl hsup0
  set out := (execN C.gates roots_20).getD C.output 0
  have hout : out &&& dom_20 = T &&& dom_20 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_20_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_20 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_20_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_20).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_20)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_20.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_20 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_20).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_20 &&& mask256 = dom_20 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_20 = T &&& dom_20 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_20, hd63, hout]
  have hnc_m : ¬ IsConst dom_20 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_20 roots_20 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_20, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_20 roots_20 0 roots_20 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4277074600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_20.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_20 10 hT6 (by unfold IsConst; decide) low_20

def wit : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [6, 2]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [11, 4]⟩, ⟨GateOp.and, [9, 3]⟩, ⟨GateOp.and, [8, 12]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_13099_aux

theorem PEqualNP.Outside.L_meta_13099 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4277074600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4277074600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_13099_aux.wit, PEqualNP.Outside.L_meta_13099_aux.wmono, le_trans PEqualNP.Outside.L_meta_13099_aux.wsize (PEqualNP.Outside.L_meta_13099_aux.lower s hs), PEqualNP.Outside.L_meta_13099_aux.weval⟩
