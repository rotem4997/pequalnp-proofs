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

namespace PEqualNP.Outside.L_meta_15907_aux

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

def dom_0 : Nat := 0xcc000000cc
def goal_0 : Nat := 0xc800000080
def roots_0 : List Nat := [0x8800000088, 0xc0000000c0, 0xcc00000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(3, 7), (3, 35), (6, 7), (6, 38), (34, 35), (34, 38)]
def r1sG : List Nat := [3, 3, 6, 6, 34, 34]
def r2sG : List Nat := [7, 35, 7, 38, 35, 38]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xeca5b8a1
  | 3, 0 => 0xeca5b8a1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc00000000000000c0000000c00000008800000088
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_1 : Nat := 0xcc00cc00cc00cc
def goal_1 : Nat := 0xc800c800c00080
def roots_1 : List Nat := [0x88008800880088, 0xc000c000c000c0, 0xcc000000cc0000, 0xcc00cc00000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc000000cc0000, 6, 22)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0xff000000ff
def goal_2 : Nat := 0xe8000000a0
def roots_2 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc000000cc, 33, 35)] (by decide +kernel) (by decide +kernel) low_0

def dom_3 : Nat := 0xff00ff00000000
def goal_3 : Nat := 0xea00e800000000
def roots_3 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_4 : Nat := 0xff000000ff0000
def goal_4 : Nat := 0xea000000e00000
def roots_4 : List Nat := [0xaa000000aa0000, 0xcc000000cc0000, 0xf0000000f00000, 0xff000000000000]

namespace S_4
def pairsG : List (Nat × Nat) := [(17, 21), (17, 49), (18, 22), (19, 23), (19, 51), (20, 21), (20, 22), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [17, 17, 18, 19, 19, 20, 20, 48, 50, 50, 52, 52]
def r2sG : List Nat := [21, 49, 22, 23, 51, 21, 22, 49, 51, 54, 53, 54]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_4.map (· &&& dom_4)
def goalM : Nat := goal_4 &&& dom_4
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xd0e4fa84
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000f0000000f0000000cc000000cc000000aa000000aa0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf80c6031c01b
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf92e6db5c5bb
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

def symsG : List (List (Nat × Nat)) := [[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
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

def dom_5 : Nat := 0xff00ff00ff00ff
def goal_5 : Nat := 0xea00e800e000a0
def roots_5 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

namespace S_5
def pairsG : List (Nat × Nat) := [(1, 5), (3, 7), (3, 35), (4, 5), (6, 7), (6, 22), (6, 38), (17, 21), (17, 49), (18, 22), (19, 23), (19, 51), (20, 21), (20, 22), (33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (36, 37), (36, 38), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 3, 3, 4, 6, 6, 6, 17, 17, 18, 19, 19, 20, 20, 33, 33, 33, 34, 34, 36, 36, 48, 50, 50, 52, 52]
def r2sG : List Nat := [5, 7, 35, 5, 7, 22, 38, 21, 49, 22, 23, 51, 21, 22, 35, 37, 49, 35, 38, 37, 38, 49, 51, 54, 53, 54]
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
  | 3, 0 => 0xa54b09769f1d53d41cc1cb5d07b69828
  | 4, 0 => 0xecf374aee34d3fabbc5068e7b476905291a9887c85ee25de59e4da3554c5e1114cd9999445b8ce5d3b18a10038a12a812c8c54b22b2bb3fc290a174d2176de3f1dba490617bcb3cf0b93b1cf006274db
  | 5, 0 => 0xfa529f1ce0d44139dfe8340dda330f57d7ccb4b7c73af6dcc3b173a2b714b6a3b6943d31b2ee19b5aedbef74ae7d80f9a90f92f2a4f836c39980c81797b5c12492c817468f621d4c7901d4d676fa35f16a8e8ae769b565db688e3a605e33f31e5a43850356c06ab354c5e1115067bf944cd9999449dedc2e44bbcd7c3fafa5c1293bbd5d2935d46027ca5be020d129b41fb2e99a171aa0eb1435d5d10c27593009309ea2014e820700168dd5
  | 6, 0 => 0xe0d44139a4f836c392c817467f9c59f373ea86206b85db7469ad921147baa0703daee4bc2f17f7c427ca5be0
  | 7, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33003300ff00ff0033003300330033000f000f00ff00ff000f000f000f000f000f000f000000000005000500050005000000ff000000ff0000000000ff00ff
  | 0, 1 => 0xa000a0000000000088008800880088005f005f005f005f005f005f000000000055005500ff00ff005500550055005500550055000000000050005000500050
  | 0, 2 => 0xcc00cc0000000000c800c800c800c800c000c000c000c000c000c00000000000af00af00af00af00aa00aa00aa00aa00aa00aa0000000000a000a000a000a0
  | 0, 3 => 0xf800f800f000f000f000f000f000f000f000f00000000000f000a000f000a000ee00ee00aa00aa00ec00ec00ec00ec00ea00ea0000000000cc00cc00cc00cc
  | 0, 4 => 0xff000000ff000000fc00fc00f000f000fa00fa00fa00fa00fa00fa00f000f000fa00fa00aa00aa00fa00fa0000000000fa000000fa000000f800f800f800f8
  | 0, 5 => 0xff00ff0000000000ff00f000ff00f000ff00f000ff000000ff00f00000000000ff00cc00ff000000ff00aa0000000000ff00a000ff00a000ff008800ff0088
  | 0, 6 => 0xff00ff00a000a0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x9e25904c2795a4b6461248a16104
  | 4, 0, 0 => 0xbe7592416f9e05525be7956416f9e56105be7796496285e61259e4758496779848c5be791841709de69259de658496f9e65525be77d849709e56105beb795496fa5e6925
  | 4, 0, 1 => 0xbe9958416789e5925be5858416d7984915
  | 5, 0, 0 => 0xbe7798485602f9de5925be879848e6be779848b602f9d218459e589e61260276121005be779848a602f6121015be78de6126be77985126be77975526be779848f6be779848d6be779a4906bea9de6126
  | 5, 0, 1 => 0xbe76154906be795e610602f9de60a5be7798489601e6120405be795e6126bec9de6126be9798490602fade6125be791e6126be77984836be779b6126be77984d2602f9d8284502fb5e612502f9e56105
  | 5, 0, 2 => 0xbe585e6126be7798490602fa5e6125be77985926be779c6126be77984876be779548e6be779848260277921805be77984886beb7985d26
  | 6, 0, 0 => 0xbe7798490602f9de60a5be795e6126be77985d26027798480502f7984815be7798552602f9de6125bee9de6126be779848e6be779848a6
  | 7, 0, 0 => 0x2f9de6125
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
  | 0, 0 => 0xce7ffff39f18939ffffce7cf8739f0000e6020007f01fc003fff
  | 0, 1 => 0xc06fffffffffc000ff8fffffe3278ff80003183078
  | 0, 2 => 0x3180000000c7600001c000000039f3e1c01cd870070000000000
  | 0, 3 => 0xc60c1e3183078c60000300300031f361cc60e760070000c60e76
  | 0, 4 => 0xf80fe03de3078c67f7ff19f078c67361f19c000c00f603183c7e
  | 0, 5 => 0xfff0003f83ff8fe0fe03f80000f98fe03e1c000f80fe03e03f86
  | 0, 6 => 0x3ffc000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x4a6deed29918918dfefc63490418d241000000007b017c0036bb
  | 0, 1 => 0x4220000424c16bddad92f74944a50dbee942260a500102942260
  | 0, 2 => 0xb592112d66e76a5099ca9400405af767d6bdd9f5af241108949b
  | 0, 3 => 0xf7bfbff9cb6fbe72010388b6bbfff777fdefefffff2512d66e76
  | 0, 4 => 0xf84fe83defeffffffffffffffffff777fffc944f84fe83defeff
  | 0, 5 => 0xfff2513fdbffbff6ff83fd8940fddff93ebc904fa6feefe37fb6
  | 0, 6 => 0x3ffdddf
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
  | 4, 0 => 0xe1c199b7dfe8340dce51d072b8f639bdb50fb2d6b14bfd7eaf4528469ea327b293d381db8a863ecd7aff582c714ed5ab6e45bf925c9b54fd59b1f1f756c06ab347baa07042184c7b3c6189bf35de20fe31e37675262f85c22141f546157477c40ab1732e07705073012766cc
  | 5, 0 => 0xe50cfdc3e4b5cb55c73d7e53c2948086c069e56cbaa4afd0b4c0e045af4528468f7d5c088a01a40988ca29be8330162a830c511d7f9c59f37e596fd573ea8620715cac866d1cc4466b94d2ac6b85db7469ad921165920fdd653d78ff6493ec5a5ab85f62586310335712780b55a1e42b5471a15851b6b1b44f053df24b31838847baa070464257373daee4bc3ab3329d39017e81387bb923382b87b23793056235e49768317ce67631138b9e2f17f7c42ef3d89a20b49e381a4f9c3e1814479f17bdcd4415dbc31515521a2e133a4b1a0ef7856d0ab1732e066ead81
  | 6, 0 => 0xc294808688ca29be4642573735e4976820b49e3817bdcd4415dbc31515521a2e
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x100000c8110000000400000000000000010000048d10000000000003000004000033144080000332440800000000000c910200000000003314408000003244080000200000800003
  | 5, 0 => 0x2130404000000000000000000000c0000100000400000000004000010000080000200000c000010000040000200000c00001000000000010000040000200000000000000000000000000080000200000800002
  | 5, 1 => 0x300000c000000000000000200000c00001000004000010000040000100000c000020000008110000000800003000000000000000040000000000400002
  | 6, 0 => 0x2000004000020000040000000000400000
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

def symsG : List (List (Nat × Nat)) := [[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
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

def dom_6 : Nat := 0xffffffff
def goal_6 : Nat := 0xeee0eca0
def roots_6 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_6
def pairsG : List (Nat × Nat) := [(1, 5), (2, 10), (3, 7), (3, 11), (4, 5), (6, 7), (6, 14), (6, 22), (8, 10), (9, 11), (9, 13), (9, 25), (12, 13), (12, 14), (17, 21), (17, 25), (18, 22), (18, 26), (19, 23), (19, 27), (20, 21), (20, 22), (24, 25), (24, 26), (28, 29), (28, 30)]
def r1sG : List Nat := [1, 2, 3, 3, 4, 6, 6, 6, 8, 9, 9, 9, 12, 12, 17, 17, 18, 18, 19, 19, 20, 20, 24, 24, 28, 28]
def r2sG : List Nat := [5, 10, 7, 11, 5, 7, 14, 22, 10, 11, 13, 25, 13, 14, 21, 25, 22, 26, 23, 27, 21, 22, 25, 26, 29, 30]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_6.map (· &&& dom_6)
def goalM : Nat := goal_6 &&& dom_6
def NN : Nat → Nat
  | 2 => 1
  | 3 => 4
  | 4 => 13
  | 5 => 13
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x27dacd5d
  | 3, 0 => 0x70e6067767c7c04e323e053d12e7ff0c
  | 4, 0 => 0xd591247cc56e12e7ac05225ea3d6d9bc5d1936d0526e44fc419de0e54166ee5a2637312d1f6c5e8b1d0f712618c3dfb0104f441f
  | 5, 0 => 0xc5159104b4992a82ac05225e93c0f7227ecfa183744473ec3a6b8d41276bea4325303d37206585ea1b8a7ef1126b25b70241d3e1
  | 6, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaa000000000000aaa0aaa000000000aa00aa0000000000a0a0a0a0000000008888888800000000555555550000000033333333000000000000ffff
  | 0, 1 => 0xeeeeeeee00000000eeeecccc00000000eeee000000000000cccccccc00000000cccc000000000000cc00cc0000000000c0c0c0c000000000aaaaaaaa
  | 0, 2 => 0xff00cc0000000000fcfcfcfc00000000fcf0fcf000000000fafafafa00000000f0f0f0f000000000f0f0a0a000000000f0f0000000000000f000f000
  | 0, 3 => 0xffffaaaa00000000ffff888800000000ffff000000000000fff0ff0000000000fff0f0f000000000ffcc000000000000ffaaffaa00000000ff00ff00
  | 0, 4 => 0xffffff0000000000fffff00000000000ffffcccc00000000ffffcc00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x1848e3
  | 3, 0, 0 => 0x69328847984cf48db30846123074
  | 4, 0, 0 => 0x1d65330558584cb215d613308561334c216061330857584cf0d6261330857574cc215d61430456984cc215d613306575854c215d7133085
  | 5, 0, 0 => 0x184cc20057584cf308601d613308575859330867584cc20167584cc248601d61330257dd61330867584d0308675851330867584cc20067584cc28867584d13086
  | 6, 0, 0 => 0x1d6133085
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 22
  | 3 => 28
  | 4 => 34
  | 5 => 40
  | 6 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x330000000e0000038000000000300033f331f2fc3fc44003fff
  | 0, 1 => 0x3f3bbc0fc0ee03f00000f00ee03c000000000000003800cce0d
  | 0, 2 => 0xf0000033f30fecc0c3c33cfefdcc0c3c3300000cc00003003000
  | 0, 3 => 0xfff3837ffc00cfff0003f03f00fc0c3c3cf0000f33fc37c03f00
  | 0, 4 => 0xffffc03fff000fff03bbffc000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x57320015cde3d522782114543503008b2a321c2543704400377f
  | 0, 1 => 0xfffffffffebeefff2202af23eeabc02028a234a89483915cde3d
  | 0, 2 => 0xf2aad2bbf77ffefddfff7dfefdcd5d3d73554b5cd50203003440
  | 0, 3 => 0xfff7af7ffcaacfff2203ffffcaffff3d7ef8880f7bfdffcabf4a
  | 0, 4 => 0xfffff2bfffcc0fffafbbffebca
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 36 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 36 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 36 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 36 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_6 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_6 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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
theorem z3_0 : ∀ i, 0 ≤ i → i < 4 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 4 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 4 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_8 : ∀ i, 8 ≤ i → i < 13 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 8 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 13 → Z 4 i = true := range_split z4_0 (z4_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 13 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 8 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 13 → Z 5 i = true := range_split z5_0 (z5_8)
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
  scr dom_6 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_6 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_6 roots_6 goal_6 7 := by
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

theorem low_6 : Lower dom_6 roots_6 goal_6 7 := S_6.noCircuit

def dom_7 : Nat := 0xcccccccccccccccc
def goal_7 : Nat := 0xccc8ccc8ccc0cc80
def roots_7 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc00, 2, 10)] (by decide +kernel) (by decide +kernel) low_1

def dom_8 : Nat := 0xcccc0000cccc
def goal_8 : Nat := 0xccc80000cc80
def roots_8 : List Nat := [0x888800008888, 0xc0c00000c0c0, 0xcc000000cc00, 0xcccc00000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc000000cc00, 2, 10)] (by decide +kernel) (by decide +kernel) low_0

def dom_9 : Nat := 0xffff0000ffff
def goal_9 : Nat := 0xece80000eca0
def roots_9 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc, 8, 10)] (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0xffffffff00000000
def goal_10 : Nat := 0xeeeaece800000000
def roots_10 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00ff0000000000, 34, 42)] (by decide +kernel) (by decide +kernel) low_3

def dom_11 : Nat := 0xf0f00000f0f0000
def goal_11 : Nat := 0xe0a00000e000000
def roots_11 : List Nat := [0xa0a00000a0a0000, 0xc0c00000c0c0000, 0xf0000000f000000, 0xf0f000000000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 4 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_12 : Nat := 0xf0f0f0f0f0f0f0f
def goal_12 : Nat := 0xe0a0c080e000c00
def roots_12 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0000, 9, 25)] (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xffff0000ffff0000
def goal_13 : Nat := 0xeeea0000eee00000
def roots_13 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f00000, 17, 21)] (by decide +kernel) (by decide +kernel) low_11

def dom_14 : Nat := 0xffffffffffffffff
def goal_14 : Nat := 0xeeeaece8eee0eca0
def roots_14 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_14
def pairsG : List (Nat × Nat) := [(1, 5), (2, 10), (3, 7), (3, 11), (3, 35), (4, 5), (6, 7), (6, 14), (6, 22), (6, 38), (8, 10), (9, 11), (9, 13), (9, 25), (12, 13), (12, 14), (17, 21), (17, 25), (17, 49), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (20, 21), (20, 22), (24, 25), (24, 26), (28, 29), (28, 30), (33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 42), (41, 43), (41, 45), (41, 57), (44, 45), (44, 46), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (56, 57), (56, 58), (60, 61), (60, 62)]
def r1sG : List Nat := [1, 2, 3, 3, 3, 4, 6, 6, 6, 6, 8, 9, 9, 9, 12, 12, 17, 17, 17, 18, 18, 19, 19, 19, 20, 20, 24, 24, 28, 28, 33, 33, 33, 34, 34, 34, 36, 36, 40, 41, 41, 41, 44, 44, 48, 50, 50, 50, 52, 52, 56, 56, 60, 60]
def r2sG : List Nat := [5, 10, 7, 11, 35, 5, 7, 14, 22, 38, 10, 11, 13, 25, 13, 14, 21, 25, 49, 22, 26, 23, 27, 51, 21, 22, 25, 26, 29, 30, 35, 37, 49, 35, 38, 42, 37, 38, 42, 43, 45, 57, 45, 46, 49, 51, 54, 58, 53, 54, 57, 58, 61, 62]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_14.map (· &&& dom_14)
def goalM : Nat := goal_14 &&& dom_14
def NN : Nat → Nat
  | 2 => 2
  | 3 => 10
  | 4 => 55
  | 5 => 228
  | 6 => 592
  | 7 => 361
  | 8 => 25
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xeca5364bcd046cbe
  | 3, 0 => 0xc936b0b5c6760761c26b180bbf70eff0b3cf7b33a4a105ec54a0acf529921ae21937b52c0f0cc098
  | 4, 0 => 0xecb4e8dae693af06e18dea83d8b4efe1d7826082ced986dccb0b766ec7b4368fc5bd184fc15954c4bbdcb2aeb8d65a9db631307cb310bf21b0ec938bafe84b02a231faa99c026a5a9b1414ee99b6968993ccc4499138874d8b6f6c98864d4c4e8132805680c1a6887cb4d3b67c48a44179c50ea1776cbf9174fc4a596d8ae40d684ef8d6681d3d1c5a162bdf58551f91562ce64c545f9fed542422224a4ca85b49fac67b49d0a17641c201a04127b9013e88cebd3391ac6123275d0a1f8683e5162a552b0ef692c10ee3b0920c9c7c960623954c04736be501500f39
  | 5, 0 => 0x51a6b53c509d2fb8505953e04f7cd72c4d95bcc54d7c05aa4a8f64b4499d722d49482969493456ee489f9bb947a232a344c0d694436cb0c542ec1c5a4137831b3fa6c1e13e3abc403d30bc3136ffa62936d3b46736040d1b355a6e4e34d939fe334cc779327cea3931ea42e231de776a308692632edb97302cd585572ba9686f2ae8b0492777ae8525140cb424d67c2723a7002b238af09b236579e3228bcbc920aa9977207e77461ed15b311e537c0a1e4eb9071c3c932e1b5300e414ed2f32133eb35d12bda1d610c683960efc073f0e3bfa500c213ba50c17cb990bd0538509f4089108442f230759ae0503dfc5e40269762b024877fc013b1ae200416e5d
  | 5, 1 => 0x9c03c9569bf429089924bc9097cea53d9752afea95c1b3459512c8399510524f939811f692879af9926b50be91bb1c4d90c62f3590c0105490b0bf828d9d945a8d7e0df58c5661d88b83b92d8b76cf9b8adf479f89c8031987839059870fac6e86e482b3867b1047851a494384dd791484a5e2cf84129109821e84e67f63396f7ec375137d9bc8f67b0d6a377a506f8f7955a5c6754a7af0746bf3d87306f4997235667c72234e846f3911d06dc9f3016d6a8de86d2a6cfc6b6ddc7b68fc91a866b3495665b58cf2650bfc25638d3dfc61d7af805fdf4d7f5d83e86959fffe085944bef95833617c56024d2455d316d555bacc89549cf24c53fe39fb53b87aa1
  | 5, 2 => 0xdb26ece0da38a0cdd888216ed8102e57d5c844e4d47823c6d279eabad23eef32cedcfbd9ce60eb47c9068c23c7cc907dc7784909c6f20f0bc679ccc7c4858242c4230668c2ec8822c2cb5af0c0a10220c04245c9bf5a4220be23db91be1f64edbdbbf972bb1c0433b869ae59b60e2ebdb5d22f43b4c421cbb358641db326a863b24cd3dab0927e87b08b963db014fbc3adb0d70cabfce9d5aa7cfe78a97f7b2fa949959fa88eb6c2a867dcf5a7d551c1a6893e1fa481cfcca392964ba3923af8a35c9dd6a32a5e35a30310fca2b31758a2b10166a21df81ba12e18efa125e9a0a08ade13a0593d1f9f6d129c9f690b349ef8eaa09ef63e2a9dfdf3cd9d6f612f
  | 5, 3 => 0xfe1a2a68fe0907acfdde4d4cfda191f6fcfad9a4fcfa9f7ffaf1b649fa850269f92388a2f84dd208f71f7b60f6dfb90bf5061225f4a03c33f3aedd49efd7ce9eefcd789aef23b46aeba08618eb0efedfe8f339afe8a11dfbe7a0a6f1e6a14148e3687acbe2f1edc5e260e440e23edf5de130803eded62f90de2abc10dd90a44add8f3560dce2c5e4dc3faa6cdbecf613
  | 6, 0 => 0x20fbfbd62064873a204a72202000d6ea1fdbe3151fc4f9a61fb72b911f87b1c01ddd2b031d9945271d07cbc61b9d622f1b805bb41b62a5db1b3c1cc21b16f5ed19b971731921237f18e16a7f17e7c6aa175a929b16a0de4915fc5b6615f4eac9158c470e155ed0bb14e0d35f14b9a6ad1486263b14696ac21437977c13e0e2a713346ed112cd450011d640d011d430a611408e9a0fde41e30f115ba20ee7b93a0ec4f4730d871bf50d6e8d170d4430e80ca165b80c7bcab90aaabd360aa03d900a7677f50a2deef8092d46d807a19af206dc6cc3060e91e705a9e53f0520799e05169eb004321371037319a002f13a0a02c7a62001a5e67401179a04006c2684
  | 6, 1 => 0x4228e6a741892944404b30134028922d3fc23f033ee052543e79bb8a3e69a4d83d946b583d6b77133d2c7c353d2562093d0b3b903cd948b53bf021da3a4fc206388012b137a858a737962c6336cd76be36186a26345f2e9f343eb05732eb626b32b9632332aa3348325f2c643185f30f3176335b30ad71ad2f954dd02f2d39052f29cd512ef3a4c42e45ee3b2e3ae3492e2eb6002dec4b6b2d52d1502b35846d2ac54d632a47f4e42a180b4c2a16023a29af2b64293427572802e9c927b671de275dc42026bb2fef2686b91125dc2a2825c5c2a225bf78b925a316842566dfcd246d800b23e8c56e23a34d13238cde422241f9d721bde80721997fae21901609
  | 6, 2 => 0x61f617a36119d7e160d62fb15f6139d15ddb6fc75da6006b5d8bf1475d71535d5d1d88c75cbe4b0e5cbb87cc5c7fa2ba5c1e7f7b5b3bed485b00c4075af98e345acd55a85a9f5dfd5a6fa4e459a0c2fc593f5843593939625929e890592546695808a353572aa6ec56488c3a5621d24155f9c36e5551c8e554fb57fa54f251df53eff8a9538cf532533b7ec1533777b25257aedf5160844350ef354250e499dd505beeb3501f9e514fc559f74f526fbe4decf5114c0f52314c01c6a54ba1260e4b93e1974b81ba084a3f5f3c497253c148683a6348040ac6475897464700cb0e46a6e54b4640bf18462000d245a7f59844d46f7843686f9d43555fb0434ac032
  | 6, 3 => 0x80a78bdc8069eaef7fb866157fa0b5d97ed1cb467e7a0a4c7e7152747e4b58517ceab7897ce7e2b17c9e1f737c69c65e7bdb97337bd948807abeb30b7a83925379e5027779c02f72792b8cc877dfa17577abf413778424c276d00d2c76b2d3b676a635e5768e81ea7613d46a7607603674cf39e474601fa774068ac973627f61728119cc727718da71ff99de715bc44070eea42e70d6da326fbd701e6f4c3cf56e7107f36df71c386dd08b0e6d547e0c6cc7f9b76bc8f9716bba04806b9d976b6b8993dd6a729fe46a41599e6909bb4667770155677213ae6741623a672edba166fd841f65e88a3d650bdfd764c8c42e6461049763cf9d8563a6a9d362dfa08f
  | 6, 4 => 0x95e551599598cffb954bc9dd951cbb3294dcea6494b8834e94a0b6d3948c576e947012d39464b8f8934a18bd92ab9dea92806526927fc7e792002a6a919ac8ae9022657e8fd08d408fa19e1f8ee20b498e965ddb8e27cd4e8e2526e78dd9a8ed8dbac1bf8da6f0c78da207fd8d9c69668d395ff68cfeab508c9ec9328c73f3678b0cdb878a69d2278a293c538a0b34fc89e93ef089a8e6358986be5c897dd414897c1ede8944278788f4b3ca88a4fc218898b407881c0d4287b2ceb4878be23f874f01c7874d6699865cbae8864f591485f6241e84e1769f847e77b184129c40831ab88982cfc52182b11d7e8275807781b726b3818c8a248154339f81025bc4
  | 6, 5 => 0xaf05cc12aef5af7aaeb38838ae87a2bbad9683faad6d5218aca9b064abd7936dab193334aada2ddaaa881170aa3d4546a98e4816a943d136a93be014a8cb32a4a8b61457a8afe02ea88d53b0a81e07a4a79e1993a7853e24a6c282b6a63809e4a598068da56f4746a55beef2a5323c56a4eb786ea4a20be6a43fb431a3744415a35b4fb5a2cd8bc3a18357d9a11662b6a0d162fda0c59c23a099d7c2a03c38c2a008f5839fb7f0179fa65d939f76efe99efaea139e56566f9cf14cd49c5ca0df9c32deb99bd769ee9bd198379bc7f7b09b62bf279af9d2839ab78fed989a692797a00225977d710296da145596d6a624968d4d5f967fbfcb964c093396099aa9
  | 6, 6 => 0xc680dba4c664bad1c63e4d23c637c9f1c5c2d3b0c5057f75c46ac8f7c469c87ec44cc871c4232d1ac3aeb668c3675414c2a091e1c228c216c0f7668fc08f171bc0171c7cbfb0cba3bfa39d58bf98043bbf83682fbf74c678beea5a39be4769d9be4533cabe20deedbde1cfb5bdd61ad8bdbc7deebd6e211abd196541bcbbca35bb75fc4eb9e29b05b99d8907b9910a03b93206deb91d4ce9b88932b6b846a1a8b833d843b78864c3b75432adb751bcc3b7083aceb6d8a086b4b954c9b4acbb32b4a8fae1b49852fdb4520808b3f19d82b34ae530b325de37b2f32daab2c0fc52b1f9e3e0b0a47233b09debbbb03df0bbb03615abb019cfffaf73942eaf332a10
  | 6, 7 => 0xe2e47feae25fc445e21be8d9e164b5f1e1151f08e10b95a5e0932adadf7909f5df17ac0ede9d2c44de90f3a7de625519de18e6c8dcd2e8c7dc4d3caedc374bc4dbce5bdddbc7af05dba68411db4f33a9dab09827da329af0da0e6468d9b417f4d9719f58d94ad137d91765b2d8c9c9e2d872797ad76d9a26d612c66fd5e8b2e6d53d3f66d53c4309d528804dd4af50cfd2cd00b1d26d319fd2061043d1cb1b0cd1879d90d1581d0ed0f7508cd0c08da1d05d132ccf1bfc50ceafa34ace7088d0ce3e5449ce39d75bcd646acbcd0facd0ccd3cdb7cbb9f257cb2d3d5cc9c13136c9b443f0c82107d4c7d402f1c70560b5c6f8273dc6f3980cc6da308dc681aa27
  | 6, 8 => 0xf84fd4fbf7396181f7271afbf716d4caf69a966ef665e0bcf6334be5f6281cb5f5e77c9bf57d219df568a6a7f4f3fc00f4bb552ef488e676f45300e6f3ef218bf3dd72f6f34d8d5cf318916ef303dc29f2dc9b47f2d492adf2a6d50af1fcdbc4f1ed8e22f1ad40a0f193a1eff052953bf0346202f02597d4eecf8408eec22234eea98865ee812039edd0785ceda7feeced8d35c2ecee993fecd37faaec7befe2ec6b46deec4760d3ec0419a9ebefca4bebbcb677eb9a6ef5eb93c63beb8d81a9eb66372beb121e74e8fb991ee86eb0d6e8529c71e82ca1a0e54d2d9be50cc564e504ee61e4d154f8e4b5bc3ce485a5e1e4635b42e3e18a9be3cc7821e2ef9098
  | 6, 9 => 0xff84627aff2325baff221992fd62561afd601635fd3bb91bfce8a04bfc82fc20fc3650befb992bf4fb1e670afb152bdafaf32e46fa72f38af87afe59f867a20f
  | 7, 0 => 0x2f1362052ea0b9112cf3c0ef2cb7e2692b81626d2b698d6c2a73350a29e942c429c478db28c04ce028a4a83e2889888f2775450f26beaf6f26bb2fef246554a623afce922310763b23038dd422d85c9a223682592219ec0a21a5f9682081cc612064873a2046aaad20292edb1fd3d3851fb72b911f3d31db1e1aa3ae1d989e101d81c57f1c53b96d1c1ffead1bea35011b52f3321979f417183e8305175a929b17206e3516b50ee915ff8a47141a4f1c1415063f12b8884a11eb7ccf1187183a0ff073950f8898390f79f41c0f6b9a140f3badb20d9cbe430d4d98860cabde0a0b989d4406b07a0305ad2f3405a3eb0a059e8b170291d00a0064991500273479
  | 7, 1 => 0x58905d1357c351985640306856240dff54ed1c7554b47b985314eaf6523dc21151efbb6051d2062b51bf3f2b51099cc6505beeb34fb2394c4f9b055d4f943bc44f717d1d4ed5e3f64e2ce2974dd111674dc27b5b4d1acf0f4cd8ba054c1e35cd4b7591cb4b0c2c394b02825d499b08ca48f0bd7d48b0ac9d484e6acf475141bb472e33c145c07cca457c5ed143555fb0434ac0324305883641d622d341a4b5d6410d76963f49363a3ee6de3d3c9d75a23c3d49423c21f90f3a8b1a653a476634396f572d39500340387c221637dd7e8036e4026d36c744ae366fa27236224d1b359f67e734ceb8d13481847a339be83032ba82ac3264f1943122199e30ccd1eb
  | 7, 2 => 0x8934bc8a88f823fd877c8a9f867726a18635a6fc85f48e9f85210b038492c7cd83c5bc52838341f4828511a481102355806266ad7f27d8097f1797dc7ebd26667e05acff7d7d57bc7d303bbe7b25f4ae7ab2c9087aa157477a7a23a87a2bf43679e15a28791d9b417900675a7892577578493a7f7733bc53759ff9f375217693749b988673f60c3a73a1eeb7721cd8337005f1236ebe77696db8095f6d5cb0976c4b6e046bed6d236be1bd3a6bcf90f36b46b4d16a7ff66869b2eaed68b561d0683fb3fc67f1c0d366fb4c91668c4770651506a464e30e6464789948645092fc63669d955fd513de5e1657ce5debf6475d93d62e5d7bf2db5aa8a6b959e9c31b
  | 7, 3 => 0xb0f51e5bb07bc511af95e2ffae8d3699ae5c9576ae064aa9aa8df529aa38618daa2867c5a98e4816a8d69abba80d4bfda8098f40a77ce252a5e4c2a9a5103ec2a4a02823a494c22fa36baaf7a02ef21b9eab30d29e3c45669da1794d9c97dd089c48de239ab0be7a99ed5e87996c23f4989a69279882e2ec98553ede97a5128c974e73179710a4589680ac86965f3458965531e695a996be94b8834e94331b6593f42b8d939a9e61934043b892b08ece928df768926d751e9262028d925c0be49117715e906d26119011f5828f9d1d5f8f7fd14d8ebf00228d5eaaf98c8386ea8bc68b508b8fda438b7e195e8a81f0ca8a59f30f8a18c28889beef4c8968a0cb
  | 7, 4 => 0xdd4db3aadd0995b1dc240579dc050ceadaf5c757da8fa153d9b9b7a8d96359b3d7c2c847d7c0c947d7661623d6fe6644d62ad27fd58ce416d56748abd3fa20bfd3a21f4ed2f75b26d1786b89d0e5095fd0dd3a20d0ab600ecf9551ebcf6e15b1ceeb1ad8cdd2d617cb9cd379cb46a5f8c8d8951dc6e5027ac6398efac5c226a0c52f7576c4ac2c82c3598a1dc3334588c31b6fd9c23de552c110cb7dc07ccfeebef5700abef4bb49beb2f988bea336b7be4be64fbde1cfb5bd2744b8bd0683e7bc18011abbec3344bb3f92c0bab08b31ba88bda4b96ec08eb837fe7bb81d78f4b7610a65b69fded2b55b444cb559ed2fb52557b8b4e46fecb37ef559b12375bd
  | 7, 5 => 0xffcceadcff5a28fefed37441fe809189fe5cb65dfe091979fc3cf275fc3650befaba4034fa6ea56df80fe67ff6657479f5210d0ef34c8d5af30eb1d1f17a65ebf15a4793f117a0a5f0f10dbeee22ff53ee185818eaf7dac4eabceb59ea04555ae9b38944e73f702ce73c37a0e7283c3de4625a30e3d420a8e2e453e9e1b1f408e1283faae0d9cf49e088d44de044fe41dfdba1afdede789bde7f8515ddfd151addd7f9c9
  | 8, 0 => 0xf2854adfc3d681efb6be7634a6563cc3a1f16def9b34b1218a7994f87f4590c97cea112d76f0de33705b5d9f5fbac6fd5e22a7545cde0cce55df5df851bb2a0f5059633d4f8c57c24aee737934064f6c1b78d4bc1561a43a1142fa410e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xeeee0000eeee0000cccc0000cccc0000aaaa0000aaaa000077770000777700005f5f00005f5f000055550000555500000f0f00000f0f00000000ffffffff
  | 0, 1 => 0x505050505050505040404040404040403030f0f03030f0f005f005f005f005f000f00ff000f00ff0000ffff0000ffff0000fafa0000fafa0000f0f00000f0f0
  | 0, 2 => 0xf0f00000f0f00000e0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a08080808080808080707070707070707050555550505555505050f0f05050f0f
  | 0, 3 => 0x151515151515151511115555111155550f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a
  | 0, 4 => 0x333377773333777733333f3f33333f3f3333333377777777333333333f3f3f3f333333333333ffff33333333333333332a2a2a2a2a2a2a2a1f1f1f1f1f1f1f1f
  | 0, 5 => 0x545454545454545450505050505050504c4c4c4c4c4c4c4c44444c4c44444c4c44444444444444443f3f3f3f3f3f3f3f3c3c3c3c3c3c3c3c3737373737373737
  | 0, 6 => 0x555555555555ffff5555555555555555555555555555000055555555505050505555555544444444555550505555505055554444555544445555000055550000
  | 0, 7 => 0x66666666666666665f5f5f5f5f5f5f5f5a5a5a5a5a5a5a5a5757575757575757555577775555777755555f5f55555f5f5555555577777777555555555f5f5f5f
  | 0, 8 => 0x88888888888888888888888888880000888888888080808088888080888880808888000088880000808080808080808077777777777777777777000077770000
  | 0, 9 => 0xaaaa0000aaaa0000aaa0aa00aaa0aa00a8a8a8a8a8a8a8a8a8a8a0a0a8a8a0a0a5a5a5a5a5a5a5a5a2a2a2a2a2a2a2a2a0a0a0a0a0a0a0a08c8c8c8c8c8c8c8c
  | 0, 10 => 0xaaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa8080aaaa8080aaaa5555aaaa5555aaaa2222aaaa2222aaaa0a0aaaaa0a0a
  | 0, 11 => 0xafafafafafafafafaeaeaeaeaeaeaeaeaaaafafaaaaafafaaaaaeeeeaaaaeeeeaaaaafafaaaaafafaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaa0aaa0
  | 0, 12 => 0xc8c8c8c8c8c8c8c8c8c8c0c0c8c8c0c0c8c88888c8c88888c4c4c4c4c4c4c4c4c0c0c0c0c0c0c0c0bbbbbbbbbbbbbbbbbbbb3333bbbb3333b3b3b3b3b3b3b3b3
  | 0, 13 => 0xccccc0c0ccccc0c0cccc8888cccc8888cccc8080cccc8080cccc4444cccc4444cccc0c0ccccc0c0ccccc0000cccc0000ccc0cc00ccc0cc00cc80cc80cc80cc80
  | 0, 14 => 0xcfcfcfcfcfcfcfcfcfcf0000cfcf0000cccccccccccccccccccccccccccc0000ccccccccccc0cc00ccccccccc0c0c0c0cccccccc88888888ccccc8c8ccccc8c8
  | 0, 15 => 0xeaeaeaeaeaeaeaeaeaeaeaea00000000eaeac0c0eaeac0c0eaea0000eaea0000e0e0e0e0e0e0e0e0dddddddddddddddddddd5555dddd5555d5d5d5d5d5d5d5d5
  | 1, 0 => 0xeeeecccceeeecccceeeeaaaaeeeeaaaaeeeea0a0eeeea0a0eeee0000eeee0000eeeaeeaaeeeaeeaaeee0ee00eee0ee00ececececececececececa0a0ececa0a0
  | 1, 1 => 0xeeeeeeeeeeeeaaaaeeeeeeeeeeee0000eeeeeeeeeaeaeaeaeeeeeeeee0e0e0e0eeeeeeeee0e00000eeeeececeeeeececeeeeeaeaeeeeeaeaeeeee0e0eeeee0e0
  | 1, 2 => 0xf0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f08080f0f08080f0f00f0ff0f00f0ff0f00000f0f00000eeeeeeeeeeeeeeee
  | 1, 3 => 0xf3f3f3f3f3f3f3f3f3f33333f3f33333f3f30000f3f30000f0f0fcfcf0f0fcfcf0f0fafaf0f0fafaf0f0f5f5f0f0f5f5f0f0f0f0f0f0f0f0f0f0f0f0f0f00000
  | 1, 4 => 0xfafa8888fafa8888fafa0000fafa0000f8f8f8f8f8f8f8f8f8f88888f8f88888f7f7f7f7f7f7f7f7f5f5f5f5f5f5f5f5f5f55555f5f55555f4f4f4f4f4f4f4f4
  | 1, 5 => 0xfafafafa00000000fafaf8f8fafaf8f8fafaf0f0fafaf0f0fafaf0f0fafa0000fafaeaeafafaeaeafafac8c8fafac8c8fafaaaaafafaaaaafafaa0a0fafaa0a0
  | 1, 6 => 0xfafafafafafafafafafafafafafaf0f0fafafafafafaaaaafafafafafafa0000fafafafaf8f8f8f8fafafafaeaeaeaeafafafafac8c8c8c8fafafafaa0a0a0a0
  | 1, 7 => 0xfcfcfcfcfcfcf0f0fcfcfcfcfcfc0000fcfcfcfcf8f8f8f8fcfcfcfca8a8a8a8fcfcf8f8fcfcf8f8fcfcf0f0fcfcf0f0fcfca8a8fcfca8a8fbfbfbfbfbfbfbfb
  | 1, 8 => 0xffa00000ffa00000ff88ff88ff80ff80ff80ff80ff80ff80ff00ff00ff00ff00fefefefefefefefefefefafafefefafafefe0000fefe0000fcfcfcfcfcfcfcfc
  | 1, 9 => 0xfff0ffa0fff0ffa0fff0ff80fff0ff80fff0ff00fff0ff00ffecffecffecffecffeaffeaff00ff00ffaaffaaffa0ffa0ffa0ffa0ffa0ffa0ffa0cc80ffa0cc80
  | 1, 10 => 0xffff0000ffff0000ffff0000fafa0000fffcffccfffcffccfffafffaffa0ffa0fffafffaff00ff00fffaffaafffaffaafff0fff0fff0ff00fff0fff0ffa0ffa0
  | 1, 11 => 0xffffa0a0ffffa0a0ffff8888ffff8888ffff8080ffff8080ffff5555ffff5555ffff3333ffff3333ffff0f0fffff0f0fffff0c0cffff0c0cffff0505ffff0505
  | 1, 12 => 0xffffccccaaaa8888ffffcccca0a08080ffffcc80ffffcc80ffffc0c0ffffc0c0ffffaaaaffffaaaaffffaaaaf0f0a0a0ffffaaaacccc8888ffffa8a8ffffa8a8
  | 1, 13 => 0xfffff0f0ffffa0a0fffff0f0ccccc0c0fffff0f0aaaaa0a0ffffe0e0ffffe0e0ffffccccffffccccffffccccffff8888ffffccccfff0cc00ffffccccf0f0c0c0
  | 1, 14 => 0xffffffff55550000ffffffff33333333ffffffff0f0f0f0fffffffff05050505ffffffff00000000ffffffa0ffffffa0fffffafafffffafafffff0f0fffff0f0
  | 1, 15 => 0xffffffffcc80cc80ffffffffc0c0c0c0ffffffffaaaaaaaaffffffffaaa0aa00ffffffffa0a0a0a0ffffffff88888888ffffffff80808080ffffffff55555555
  | 2, 0 => 0xfffffffffafafafafffffffff0f0f0f0fffffffff0f0a0a0fffffffff0f08080fffffffff0f00000ffffffffe0e0e0e0ffffffffccccccccffffffffccc0cc00
  | 2, 1 => 0xffffffffffff0000fffffffffff0ffa0fffffffffff0ff00ffffffffffa0ffa0ffffffffffa00000ffffffffff80ff80
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x1a8a6409ba532833
  | 3, 0, 0 => 0x6a298ea49485bad3283474a64d25a4622c14c814659f0ea4946bb516e81469a990249464abd4c81469aa0ea49485bc106754
  | 4, 0, 0 => 0x622bd4c8124ab61a6993a969606c45b9d4aab0a6bb256e81569a98ea5a24abcda2752d1555f2d76229520ad7659fcea49579bad9a9941abcda2ad3a969618f0679d4b4ac457aa0ea4956bb4d6e8124ab255ea63a925616f03a9a4b4af367ab4ea5a5
  | 4, 0, 1 => 0x79b5d8aa5482b5da8b73a9255e6c453a6520af36bb254a90565a64f8752d2bcd9a883a9695aec45bac102af378335145a5621f8f87524abcde0cd399695e6f066a0ceab0b6ba650675579bb59a752d2bcd9ab73a9555f8f0669d4b4ae966a64ea5a5
  | 4, 0, 2 => 0x79bc104752d2c01e0cd3a9695aecb3d9d4b4b0b75a64d25a579bc1aa692d2bcd9e9943969616f0691d4b4afb622dd4c81579bc1a475272bcd92b753205588b0531d492ad35ba98ea49579b116e9443abcde0cd4811d5a6a64c9d492afb6bb114a905
  | 4, 0, 3 => 0x34d82993a9695bed35b9d492ad764add5e8150034d4c7524a42de0cd399695aed3531d492af368a650e5a5
  | 5, 0, 0 => 0x79b1152993a9519e6d74ca08ea5a68035d9a993a9699f6d7622dd025a679b114c993a9359e6f069334ea5a679bad8899479699e6eb67a64ea5a679b5d88c3339259e6e3621ecea4f679bad88b74ca199e6d76aa64d25a67dbad8899351699aec45babd0249679b10fe7c3a9259e6d764add025a6
  | 5, 0, 1 => 0x79b114c993a95da16f378334ea5a679b5d88b63a9259e6c456264ea5a679b5d88ad3a95d9e6d7622a8ea4968435d8a993a969a16d766a64e65a679bada2993a9699e6e36226514556003cdaec43a92d614d764adcea4968535d3275341699e6d7622d0ea49679b7988994810d9e6eb66a64d25a6
  | 5, 0, 2 => 0x6c3115e993a9699e6f066adcea5a679b7988b73a9259e6c44ca610e5a6622bd4c752d125988993f1f0ea5a679bc19a75379699eedc62264ea5a679b8d88994093d9e6d764a650e5a67cb7988993a969a06f0622dcea5a679b1172993a93d800f3781d4b40b579b114c963a969800f0669d4b4005
  | 5, 0, 3 => 0x7db5d88b7409d59e6df622650e5a679bc19a752d139a16d74c9d4d25a685bad9a993a9699e6c44ca408e40679bc1aacd3a9699e6c44ca10ea5767cb5d88994811d9aed35ba64ea49679b1152993a955800f378334ea3657a36188993a9699e6c456a50ea5a679b5d92b7409d59f6d7622650e5a6
  | 5, 0, 4 => 0x79b5d88a5481099e6c45ba10ea49679b114c994811d9a6b753264ea5a6003cdaec42d0a55e6f0669d4b455679bc19a7534969a18d767a64ea5a679b114c75339259e6da622650e5a679b7988993f9d59f2d762294ea5a679b116e943a93d9e6f0669d4b42266bb116eb03a9259e6ea62265205a6
  | 5, 0, 5 => 0x79b256ea63a9259e6d764ab4ea5a679b7992993a969a14df64a64ea5a684b5d92993a9699e6d766264d05a67335d88993a969a06c44c9d4b454679b3d32752d13d9e6d7622913290679b11807c319699e6c460298c65a679b8d88993e9d59e6f066a40ea5a66bb4d3275339699e6e367a64ea4f6
  | 5, 0, 6 => 0x7db116ea63a9259f6d7622b4ea5a6003cd88923a9695e8d7622dcea49680bcde0cd3a9699f6de62264ea5a679b116ea83a9259e6d14c9d4b44f6622bd4c993a9259e6c44ca50ea5468535d92993a9619e6c953264ea5a679b798a993a9699faf378334ea5a679b115a983a9699e6cd4c9d4b4546
  | 5, 0, 7 => 0x79b5d8a994811d9e8c453264ea5a679b799c993a969800f36bb256e8156bb4d4c993a969a06dc62264ea5a679b5d8890339259e6de62265204f67db114c993a9699e6c460adcea49679b5d92994811d9e6df62265145a679b5d88ae3a925988b757a98ea4960035da6b73a9255e6c454264ea5a6
  | 5, 0, 8 => 0x3cdaec44c8fd60ae362264ea4f679b114e993a9699e6ed62244ea5a679b658899481699e6dc66a64ea5a60034d4c993a9695f6d7622652047679b116e913a955a14d764a65025a679b10f87b3a9699f8d766a64ea5a679b8d88ad3a9259e6d764a94ea5a679b114c7b3a9699e6d76229520496
  | 5, 0, 9 => 0x7db1132843a9699e6d7652652075679b7d88994811d9e6f0669d4b43667db5d88a53a9699e6c44ca40dc4f679b1130752d155800f378334b4225003cde0cf3a9695e6d762a94ea5a681b1132752d155a08de62264ea5a6003edaec45ba055aec44ca2cea5a685bc19a993a9699e6c94ca10ea5a6
  | 5, 0, 10 => 0x79b1122883a9699e6c45ba990249679b7588994811d800f362264ea525003cd9a752d0055e6f062245145a6003cde0d13a9695aec95babcea49679b8d88b74ca1da06de62264ea5a679bc19ac03a9699e6f0669d4b447679bad88b7351259e6cd4c9d4b455679b5d9a99399699e6d766a6506756
  | 5, 0, 11 => 0x79b5d92993a9619e6df64adcea5a679b5d88994395d9e6e362300c64f679b113275371559e6f162298ea49681b5d88994811d9e6d763264ea5a679b9592993a969800c457a98ea49579b114c9940969800f36bb10ea3d579b799a993a9699e6f263a64ea5a679b1132863a9559aec457a98ea496
  | 5, 0, 12 => 0x7db7d88b73a9699e6c44ca14ea5a679b5988b73a9259e2d769a64ea5a679b7988b74ca419f6f36bb116e816623055e993a9699fed764a64ea5a679b5d88b73a92d9e6d766a652047679bc188914811d9e6e262264ea4f679b5d8899238fd9aec43f9f8ea4966fb116eaf3a9259e6de62264b42b6
  | 5, 0, 13 => 0x6bb4d86993a969a0cf378334ea5a679b5da4993a9399e6eb62265005a66bb4d6e752d1259e6c44ca510e5a679bc19a752d02d9e6d7622652065679b5d88992d0b19e6d7622dd0e49679bad9299351699e6d764264ea5a679b6188b73a9259e6e364a64ea4f66bb2d327f3a9698010b78334ea5a5
  | 5, 0, 14 => 0x85b5da4993a9699e6de62295329067db8d88993a93d9aed34c9d4b40f6
  | 6, 0, 0 => 0x35d88994811c00cf36bb258e993a969c00f36bb4532752d33cdaec43d9d4b44f7003cdaec44c984b4cf370b5d88993a969de6de622dd32752d3801f6d762265025a679b5d88b74c9d4b4e0079b1132752d00d9e6d766b0132752d3bf5e6d7622650e5a779bc188c0489d4b4ef36bb1132752d969de6d766a64ea5a23bbcde0c4489d4b4477
  | 6, 0, 1 => 0x35d88c03196800cf36bb1132863a91dde6de6226522752d3bcdaec44ca40ea57779b5d88b73a99c92ef371b11327527925c00f36f31132751b33cdaec44c9d4b427779b5d887f3d9d4b4e0079ba988993a969800f36bb11805a1533cdaec45d1d4c65a779b7d88993a9689eef36bb1132752d0edde6df6bb1132812d3801e6c4489d4b4016
  | 6, 0, 2 => 0x833cdbec44c9d4b4ef36bb11327532969c00f36229932751b33cdaec460264b42b779b5d88993a99cb4f0d79b1132752d151de6d762264ea5a08bbcdbcc44c9d4b41d779b5d88992d11c56ef36bb116e7524889c00f36bb110e5a0eb419e6d7621ecea5a7003cdbec44ca04b4cf375b11326a2d125de6da62264ea5a27bbe9e6d76226520477
  | 6, 0, 3 => 0x79b5d88b74096892ef36bb1132752d051de6de6229532752d38021af3622650e5a679b5d889945168aaef36229932752d075de6d76229532752d3bcdaec44c9d4b41c779b8daec44ca04b4ef36bb1132752d0e5de6d7622dd329023b8018899421d4b40067dbcdbec44c9d4b4ef36bb116ea23a969c00f36d310ea5a0bb3cdaec45ca64ea5a7
  | 6, 0, 4 => 0x3cdc6c44c9d4aacf36bb1132752d155de6d76632532752d3bcd88a64c9d4b422779b5d88c05b98cb4ef36bb11327535969c00f36bb11325a16b001eed762264ea36600429aec94c9d4b4cf36bb1144752d0b9e1af3622b532752d3bcdaec44c9d4b85a779bc1aec44ca04b4ef362299327533969de6d7622f932752d3bcdaec44c9e8b42b7
  | 6, 0, 5 => 0x79b6588993a9683aef36bb1132872d0d9de6d76227932752d3bcdaec44c9d4e05a779b116e99421d4b4ef36bb116e903a925de6d76226520470ebbcdaec44c9d4b40d779b7188993a9a8b4e006bb2532752d001800f37831130752d33cdaec44c9d4ba5a700310ea5a0e82800cf36bb1132914811dc01037831132752d3001e6d765264ea5a6
  | 6, 0, 6 => 0x833cdc6c44c9d49eef36bb114a994811dc00f36226508751b33cdaec450264ea5a70042daecd4c9d4b4c0079bc19a993a969800f362264ea5a0233cdaec44c9d4b410779b5d88993a9686eef36bb1132812d13dde6d76228532752d3bcdaec44c9d4b44c779bb1aec43d9d4b4ef37831152993a969de6d76226932752d3801e6d762300c6366
  | 6, 0, 7 => 0x79b5d9a993a96816efb79b5d889940969de6d7622dd28752d3bcdaec44f9d4b4497833cdaec44ca04b4ed7622dd5e993a925de6c44ca10ea5a0ebbcd88a64ca40ea5a779b7988993a96886ef362264ea6a2d155c00c44c968440a0033cdaec45ba98ea497833cdd6c44c9a8b4ef36bb256e993a969de6d764a64ea5a063801aec42d0883a006
  | 6, 0, 8 => 0x7db5d88b74c9d4b4efd79b7988993a969de6eb6bb116e7524bbcdaec45b9d4d44970037d88993a96800d0679b5d9a993a969e0cf37831122752d3801e6c45ba98ea49679b5d88993a968a2e0079b5d92993a8d99e6d762264ea5a0b3801e6c43a8d83a0a67ebcdaec45b9d492e006bb10f6752d0019e6d762264ea5a0ab801e6de62264ea5a6
  | 6, 0, 9 => 0x7a35d88b74c9d4b4ef371b5d9e993a969de6d764a64ea5a113bcdaec44ca1cb449779b5d88bc4c9d4b4ef36f35d88994811dde6de62264ea6e2d3bcdaec44c9d4b453779b5d88993a9b8b4ef36f311327535169de6d7622dcea49053bcdaec460264fe5a779bad88994a1d4b4ef36bb115299481d5e1af362264ea5a2abc05e6d7622dcea497
  | 6, 0, 10 => 0x3cd88763a9683acf36bb1132752d115de6e362264ea5a2a3801e6c45b9d4920a679b5d88ae4c9d4b4ec45babd4c993a969c00d769add32752d3001e6c44c8d8440a686bcdaec45b9d492ef36bb499a993a969c00f36bb106c220eb3cdaec44ca40b406779b5d88b73d9d4b4efd79b114c993a969c00fb6bb1132751b33cdaec44ca408e437
  | 6, 0, 11 => 0x7db5d88993a96844ed7622bd327533969e14f36bb2532752d3801e6d7621ecea36679b5d887f3a96892efd79b5d88993f9d5de6d76226520672d3801e6de621d4b41d679b6588993a9682aef36c31132752d03dde6d762264ea5a1c3801e6d962264ea5a680bcd88a64c9d4b4e0079b7988994811d9e6c460add32752d3bcdbec45ba64ea5a7
  | 6, 0, 12 => 0x7cb5d88993a9688eef36bb11327533169c00f36bb116e491133cdaec44ca40e25a779b5d88993a96848ef371b115a993a969c00f362298ea5a0eb001c6c44c9d49e00679b5d88c04c9c8b4ef36bb114a9948169de6de62264ea5a213bcdaec44c9d4b4267003cdbec44c9d46cc0079b8d8899439699e6d7622dd027524bbf5e6d76226520477
  | 6, 0, 13 => 0x85bcdaecd4c9d4b4e0079b5d8899481059e6d7622c932752d3bcdbec44c9d4b4227003cdbcc44c96844cf36bb116e75248d9de6c44c9d4b447203bf9e6d762300c65a70035d88994096800cf36bb2932752d15dde6d7622652047053bcdaec45da64ea5a779b5d88993e9d4b4ef36bb2532903a969c00eb62264d45a0033f5e6d762300c65a7
  | 6, 0, 14 => 0x3cdae993a96816cf371b116e993a93dde6d7623016e7524bbcdaec44c9d49e4d7003cd88994811c14cf36f31132752d0d9de6d7622dcea4923b801aecd4c9d4b4006003cdb2c43a9683acf36bb1180632d029e1af36bb11329023b801e0c4489d4b4006003cdaec44811c3ac0079b5d92b73a9259faf36226508752d3bcdaec44c9d4b4317
  | 6, 0, 15 => 0x79b5d88b74c9d4aae0079b1180632d0299e6f062244ea6f2d3bcdbcd762265205a786bcdaec46018cb4ef36bb11328e3a969c00f377b1132752d33cdd6c45ba64d45a78535d92993a96892f036bb116e993a969de6df62264ea5a2abbcdaec44ca408e42700001e6f0669d4b4b0679b5d889943969c00f362299325a1133edaec44ca40ea5a7
  | 6, 1, 0 => 0x79b5d92993a9a8b4ef36229932752d11dc00d7622dd5e7524b00206d762264ea366003cd88843a9683acf36bb1132752f169de6d762264ea5a1a3801e6d762a64ea5a6003edaec45b9d492cf376b5d88993a969dfaf36bb2532752d3bcdaec44c9d4b43a779ba1aec44c9d4b4ef36bb1184993a969de6c453264ea5a1b3bcdaec45ba65025a7
  | 6, 1, 1 => 0x79b7988993a98cb4e0079b5d8899408d99e6d76226d32752d3bcdc6c44c9d49e1d779b7d8899481d4b4ef3623014c993a969de6d762265205a0abc05e6d764a64ea5a7003cdbcc44ca40b4cf36bb356e993a969de6d762294ea5a213bcdbed7622dcea49779bc188b7489d4b4ef375b5d92993a969c00f375b11326a1b33cd88993a96882407
  | 6, 1, 2 => 0x79b8d88993a93c44ef371b1132752d155de6d762264fe7523bbcdaec44ca408e36779bad8899351683ae0079b7188993a8c19e6d76226500752d3bddaec44c9d4b436782b8daec44c9d4b4ef36bb11809937969de6d764a64ea5a053801e6d7621d4b416679b5d88993a980b4ed7622bd4c993a969de6eb6226530752d3bcde2d7622dcea497
  | 6, 1, 3 => 0x86bcdaec94c9d4b4ef36bb559a993a969de6de62264ea5a20bbcdaec458a64ea5a779b114c993a98cb4ef36bb1132752d105c00f36bb24ea5a0eb3cdaec44c9d4ae4f779b5d88993a96842ef36bb1148993a969e06d762264ea5a113801e6d766a64ea366003cdbec45b9d492cf36bb1132752d095c00f37831122751b33cdaec44c9d4b4467
  | 6, 1, 4 => 0x79b5d88b34c9d4b4ef371b5d88b73a925dfaf36bb10f6752d3bcdbcc44c9d4b449779b5d9a993a9689cef36bb116e99431d5de6d7622f532752d3801e6df62264ea5a679b5d88c0319686ce0079b2532752d029800c457a9932752d33edd6d762264ea5a779b5d8899481b8b4e0079b113275278099e6c44c9f0ea632d3bedaec44c9d4d45a7
  | 6, 1, 5 => 0x3edaec43a9683acf36bb1186b73a925de6d764a6502752d3bcdaec455a64ea5a77ebcdbec44c9d4b4ef36bb11447531969de6d7622e132752d3bcde0d7622dcea49779b1132843a9686cef36bb11328f3a969de6d766a64ea5a113bcde0d762265145a779bc188913a96844ef36bb115a752d125de6f16229932752d3bedaec44c9d4b40a7
  | 6, 1, 6 => 0x79b5d88a34c9d4b4ef371b1132903a93dde6d766a64ea692d3801e6d764a64b422680bcdbec44c9d4b4e0079b10b4220e8299e6d7621ecea5a053801f6c44c9d4b40a679b114c993a96892ef36fb11327535169daec44c9fcfc752d3bcdaec44c9d4da5a779b5d8899469d4b4ef36bb1132752d08dde6d76226510752d3bcdaec45b9d4920f7
  | 6, 1, 7 => 0x86bcdaec43d9d4b4ef36bb114a7531969de6d764a64ea5a1b3bcde0c44ca18ea5a779b5d88993a96894e0079bad8899431699e6d762265204720bc0daec44ca40ea5a779b8d88994a1d49ee0079b7588993a969800d7622650e5a0033cde0c4489d4b455779b5d88993a9681ee0079b113a992d0899e6f26bb2532752d3bcdaec460264ce5a7
  | 6, 1, 8 => 0x79b8daec44c9fceaef36bb116a993a969de6c44ca50ea5a27bbcd88a64c9d4b40f779b1186a64c9d4b4ef36bb1132902491dde6d762264ea5a283801e6df621d4b41d679b5d88993a984b4ef36bb116e7527925c00f3621ecea5a0533edaec44ca04ea5a779b5d88993a9683cef36b3116e993a969de6c45ba98ea5a24bbcdc8c44c9d4d45a7
  | 6, 1, 9 => 0x3cdaec4511d45ccf371b5d88994811dc00f36bb10ee5a0ab409e6d7621ecea5a779b91aec46018cb4e0079b5d88993d0ad800f36bb116e8124b3cdb0c45ba64ea5a779b5d9a99481d4b4ef37831122903a969de6d7621d4ce5a24bbcdbcc44c9d4b44f779b5d92c04c9d4b4e007db5d88992d0899e6d762264ea5a193bcdaec94c9d4b4477
  | 6, 1, 10 => 0x3cdae993a96818cf36bb114a752d125de6df6226502752d3bf5e6e362264ea4f77dbcdaec45b9d492e0079bad88993a1699e6d762264ea5a073bcde0d7622652047779b5d8a993a9688eef36bb1132752d0d5de6d762264fe752d3bcde0c44c9d4dc5a7833cdaec45b9d492efb6bb1132752d0d9de6d7622dd32872d3801e6eb62264dc5a6
  | 6, 1, 11 => 0x3cdaec44ca1c6cd0179b8d88993a93dc00f36fb11325a1133cdaec45ba64ea4d77db5d88c04c9d4b4ef371b1132753713dde6d762264ea5a143c19e6de62264ea5a779b1132843a96892efd79bad889935169de6de62265205a23bbedaec44c9d4b447779b8daec46018cb4e0079b8188993a969800fb6bb2532752d33cde0c44c9d4e85a7
  | 6, 1, 12 => 0x79b113275371689ef0679b114c993a969de6d7622650e5a0ebbcdced762264ea5a779b7d88993a9686cf0779b5d88b73a925c00f36bb116e751f33cd8899489d4b454779b11327f3e1d4b4ef37135d88993a969de6d7621ecea5a1b3bcde0d762300c65a7833cdaec4569d4b4e0079b5da0993a9699faf36bb1132812d3bcdbed764a64ea5a7
  | 6, 1, 13 => 0x80bcde0c4489d4b4efb6fb5d88993a969de6df6230132752d380206d7621d4b41d679b7d88993a9688eef36bb11869933969c010375b1132752d33cdaec44ca04b40a7003cdc6c43a93c3acf36bb1132893a969de6c44c9d4e85a27bbcdaec44c9d4b42d7003cdbec94c9d4b4cfd79b5d9a993a969de6d762265204f23bbf5e6f062244ea5a7
  | 6, 1, 14 => 0x79b6d88993a9689ef0679b5d88994811dc00f362265025a05300188993a8d81400679bad88a94c9d4b4ef37735d88993a969e1af36bb1132812d3bcdc6d764a64ea5a779b5d88993a96830ef36bb1132752d121de6c44fa7532752d3801e6d762204b41d60035d88751b07400cf36bb1180632d13dc00f375b10d45a0eb405e6d766a64ea5a7
  | 6, 1, 15 => 0x79b5d88b74c9d4aeef36bb11327536169c00f36bb1132602d33cdaec44c9d4a8497003cdaec43a9241ec0079b5d9a752d0759e6d762264ea5a19bbcdaec44ca30ea5a7003edbec44c9d4b4c0079b1132752d01d9e6d762300fe632d3801e6eb66a64ea5a679bc1aec94c9d4b4ef36bb256e752d125de2d7622bd32752d3c1de6c453264ea5a7
  | 6, 2, 0 => 0x3cde0c44a1d4b4cf36bb1132752d049de6eb6bb11325a15bbedc6d762264ea5a7833cdaec4529d4b4e0081b5d88992d089800f362264ea5a04b3cdbac44c9d4b4477003cdc6c44c93c44cf36bb116e963a969de6d7622d132752d3c19e6d762300c65a779b5d88993a96834ef36bb1132783a969de6d762264ea5a1e3bcdaec44c9d4b4447
  | 6, 2, 1 => 0x79b798899499d4b4ef36bb2532752d13dde6d762264ea5a09bbcdd4c44c9d4e25a779b5d88b64c9d4b4f0679b1132843a969df6f06bb1132752d3bcdb8c44ca44ea5a70035d88b73a92400cf36bb1132752c925de6d7622a932752d3801aec44c8d84400679b8188993a9689aef371b113275278d9de6d762264ea5a0fbbedaec45b9d4b4497
  | 6, 2, 2 => 0x3cde0c44896844cd7622bd32752d03dc00de62264ea5a0033cd88994c1d4b44f779b5d8899409686cef371b5d887b3a969daec461abd32752d3801e6e362264ea54679b7988993a968a8ef36bb1132752d065de6e362264ea4f23b801e6d7621d4be14679b5d92993a9a0b4ef375b11326a2d0d9daec45babcea5a24bc0daec44c9d4b4367
  | 6, 2, 3 => 0x79b5d88993a990b4ef37835d887b3a969c00f36bb10ea5a10340daec460264ea5a779b7188993a96860e0079b5d9299409699e6d762264f2752d3bcdaec44c9d4b42f7003cdb0c44c9d4b4cf36bb1138993a969c00f36bb10fe7524b3cdaec44c9d4b41b781b5d88993a9688ee0079b5d9a992d089800f36bb3d32752d33cdc6c460264ea4f7
  | 6, 2, 4 => 0x79b116ea64c9d492ef371b1132753193dde6c44ca44ea5a2abbcdaec45fa64ea5a77dbcdaec94c9d4b4efb6bb1132752d13dc00c453264ea5a0033e9e6de62264ea5a779b5d88993a9bcb4f0679b5d92993a969de6d766a64ea5a1b3bcdbec44c9d4da5a779b7d88b73a96892ef37831122752d0d9de6d762264ea5523bbd1aec44c9d4b40f7
  | 7, 0, 0 => 0x3cdaec44c9d4b40670000188993a96814006003cd88b753264ea5a7003cde0e362264ea5a779b5d88993a9689e498003cdaec44c9d4b42e77ebcdaec45ba64ea5a800001aec43a9683a006833cdaec44c9d4c65a879b5d8899481d4b41d80035d88993a9681400779b5d88993f9d4c65a879b5d88b753264ea5a879b5d889948a40ea5a8833cdaec460264ea5a8003adaec44c9d4b4007
  | 7, 0, 1 => 0x405e6d762264ea367833cdaec44c9d4b4498003cdd6d762264ea367003cdaec460264c65a7003cdaec44c9d4d43677ebcdaec44ca44ea5a879b5d88b74c9d4b40a8003cdaec44c9d4ce5a7003cdaec44ca04b4497003f5e6d762264ea36779b5d88993a9683a15880bcdaec45ba64ea5a8003cdb8d762264ea5a779badaec45ba64ea5a879b5d88b74c9d4d45a8003cdaec451264ea5a7
  | 7, 0, 2 => 0x7ebcdaec44c9d4b4228833cdc6d762264ea5a879badaec44c9d4b41d8003cdaec44c9d4e25a779b5d88993a9a8b41d8003cd88b74c9d4b40a7003cdaec44c9d46c0a786bcdaec45ba64ea5a8003cdaec44c9d4b414780bcdaec44ca44ea5a800001aec44c96844006003cdc6c44c9d4b44f7003cdaec452a64ea5a7003cdaec45b9d4b41d77dbcdaec44c9d4b44987ebcdaec44c9d4b41d8
  | 7, 0, 3 => 0x35d88c04c9d4b400779b5d88993a968440a8003cd88993a968140670035d88993a9688e00700001e6c44c9d46c0a6003cdaec4489d4b41d7003cdaec43a98cb449700435e6d762264ea367003cdaec44c9d4b43e7003cdd6c44ca44ea5a700001e6d7621d46c1d679b5d88993a9683a0a8833cde0d762264ea5a80035d88993a9686c007003cdaec44c9d4b455780bcdaec44c9d4b41d8
  | 7, 0, 4 => 0x3cdbcd762264ea5a779b5d88b74c9d4b4368003cd88993a968440a7833cdaec44c9d4b44f886bcdaec44c9d4b4228003cdaec43b9d4b41d7003cdaec44ca50ea5a77d3cdaec44c9d4b4478003cdaec43a968441d7003cdaec44c9d4b4057003cdaec44c9d4b42a7003cdaec44c9d4be5a7003cdaec45ba64b4227003cd88993a9683a0a7003cdaec44c9d4b456786bcdaec44c9d4b41d8
  | 7, 0, 5 => 0x79b5d8899481d4b40a879b5d88a24c9d4b436879b5d8899489d4b4368003cdaec44c9d4b415700001e6de62264ea5a6003cdaec44c968441d779b5d88993a9686c2e879b5d88c05ba64ea5a8003cdaec44ca18ea5a779b5d88b74c9d4b4478003cdaec44ca44b422700001e6d7622dcea4967ebcdaec44ca40ea5a800001e6d7622646c226003cdaec43a9683a1470035d88993a98cb4007
  | 7, 0, 6 => 0x86bcdaec44ca40ea5a80035d88b757a64ea5a7003cdaec4481d4b41d779b5d88c04ca44ea5a8003cdaec43a97cb41d700001e6c453264ea5a679b5d88b74c9d4c65a8003cdaec44c9ecea5a779b5d8899489d4b4478003cdaec460264ea3670035d88993a9689200779b5d88993a9686c1d879b5d88993a9683a178003cdaec44c9d48e36779b71aec44c9d4b43687c3cdaec44c9d4b4368
  | 7, 0, 7 => 0x7ebcdd6d762264ea5a87ebcdaec44c9d4d45a8003cdaec44c9d4c6367003c1aec44c9d4b400779bc5aec45ba64ea5a8003cdaec44c9e8ea367003cdaec44c9d4e85a7003cdaec44c9d46c2b779b5d88c04c9d4b41d8003cd88993a968140570038daec44c9d4b4007003cd8899481d4b40a7003cdaec44c9d4dc5a779b5d88993a9686c22879b5d88993a9686c30879b5d88993a9688e1d8
  | 7, 0, 8 => 0x79b5d8899481d4b4368003f5e6c44c9d4b40a7003cdaec44c9d4923670035d88993a9689e007003f5e6d7621d4b41d780bcdaec44c9d4b40a8003cdaec44c9d4b442779b8daec45ba64ea5a800001e6d762300c65a679bc1aec44c9d4de5a87ebcdaec44c9d4b40a8003cdb6d762264ea5a779b5d88b74c9d4b4498003cdaec43a9683a15700001e6d7622652047679b5d88a54c9d4b4478
  | 7, 0, 9 => 0x79b8daec44c9d4b41d879b5d88993a9689222879b79aec44c9d4b4478003cde0d762264ea367003cdaec43a9683a0a700405e6c44c9d4b40a7003cdc6d762264ea367003cdd6c44c9d4b40a7003cdaec44c9d4b44d779b5d88b74c9d4b40f800405e6d7621d4b41d700001e6c44ca10ea5a679b5d88c35ba64ea5a8003cdd6d7621d4b41d7003cdaec43a9a8b41d779bc1aec45ba64ea5a8
  | 7, 0, 10 => 0x3cdaec45d264ea5a7003cdbcc44c9d4b4477003cdaec44c9a8b422700435e6c44c9d4b40a779b8daec44c9d4b4228003d9e6d762264b422700001e6d764a64ea5a6003cdaec44ca54ea5a700001e6c43a9683a0a679b5d88b74c9d4b44f879bc1aec44c9d4b41d8003f5e6d762264b422700435e6d7621d4b41d779b5d88993a9688e43800435e6eb62264ea5a7003cdaec44ca60ea5a7
  | 7, 0, 11 => 0x1f6d762264ea5a6003cdaec44c9d4b45777ebcdaec460264ea5a8003cdaec44c9d4b42b7833cdaec45ba64ea5a880bcdaec44c9d4b43687ebcdaec44c9d4b447879badaec44c9d4b436879b5d88993a9a8b4368003cdaec44c968440a7003cdaec44c9d49e367003cdaec44c9d4b4027003cdaec44c9d4c45a77ebcdaec44c9d4b436879bc1aec44c9d4b4228003cde0c44ca44ea5a7
  | 7, 0, 12 => 0x3cdaec43a9686c1d7003cdaec43a9683a17779b5d88993a9688e0a800419e6d762264ea36779b5d88993a9689e228003cdbed762264ea5a700001e6c44c968440a679b5d8899481d4b449800435e6d762264b4227003cdb6d762264b4227003cdaec44ca5cea5a700001e6d762168441d679bc1aec44c9d4b455879b5d88993a9686c0a879b5d88993a9a8b447879b5d88993a9689e1d8
  | 7, 0, 13 => 0x79b5d88993a9a8c65a8003cdaec43a9688e1d7833cdaec44c9d4b41d87f3cdaec44c9d4c65a8003cdb4d762264ea5a779b8daec44ca50ea5a8003cdaec44c9d4b441783bcdaec45ba64ea5a8003cd88993a9686c0a700001e6d7621ecea5a679b8daec44ca40ea5a87ebcdaec44c9d4c65a8003cde2d762264ea5a779b5d88c04c9d4b40a8833cdaec44ca44ea5a886bcdaec44c9d4b4368
  | 7, 0, 14 => 0x3cdaec43a98cb41d7003cdaec44c9686c2277ebcdaec44c9d4b4498003cdaec44fa64ea5a779b5d88993a9688e428003cdaec44c9d4b408779b5d88993a98cb40a8833cdaec44c9d4b4228003cd88c04c9d4b40a786bcdaec460264ea5a8003cd88993a9688e0a7003cdaec4601d4b41d700001e6df62264ea5a6003cdc8d762264ea5a786bcdaec44c9d4b447879bc1aec44ca40ea5a8
  | 7, 0, 15 => 0x80bcdc6d762264ea5a8003cdb4d7621d4b41d779b8daec44c9d4dc5a87ebcde0d762264ea5a879b5d88993a968920a8003cdaec44c988b4227003cdaec44c9688e22780bcdaec44c9d4b44987ebcdc6d762264ea5a8003cdaec44c9d4b40f779badaec44c9d4b449879b5d8899481d4b44f879b5d88993a9a8b4498003cd88993a98cb40a786bcdaec44c9d4c65a8003cdaec45b9d4b4497
  | 7, 1, 0 => 0x3cdc6d7621d4b41d700001e6eb62264d45a6003cd88993a9681408779b5d88993a9686c2b80000206d762264ea5a6003cdd6e362264ea5a7003cd88993a968920a7003cdaec44c98cb422700001e6e362264ea4f686bcdaec44c9d4b4498003cdaec43a968921d780bcde0d762264ea5a8833cdaec44ca40ea5a80035d88b74c9d4b400779b5d88c04c9d4b436879b5d88993a9688e368
  | 7, 1, 1 => 0x35d88993a9683a00779b5d88993a98cb4478003cde0c44c9d4b40a7003cdaec454a64ea5a7003cdaec44ca40b447779b5d8899409d4b44980035d8899489d4b4007003cde0d7621d4b41d77ebcdaec44c9d4b44f8003cdc6c44c9d4b40a779b5d88993a98cb436800001e6d762265025a600001aec44c9d46c006003cdaec44c9fcea5a779b5d88993d1d4b4368003cde0c44c9d4d45a7
  | 7, 1, 2 => 0x79b5d88b74ca44ea5a8003cdaec94c9d4b4497833cdd6d762264ea5a8003cdaec43a9689e1d7003cdaec45ba64ea367833cdaec44c9d4d45a8003cdc6d762264b422779b5d88993a9689236879b5d88993a9688e418003cdaec44fa64b422700435e6f062264ea5a70035d88993a96844007003cdaec44c9689222700001e6d766a64ea5a600001e6f062244ea5a680bcdaec44c9d4b44f8
  | 7, 1, 3 => 0x3cdaec451264ea367003cdaec44ca44ea36779b8daec44c9d4b447800435e6c44c9d4b44f7003cdaec44ca58ea5a779bc1aec44c9d4b436879b5d88b74c9d4ce5a8003cdaec44c9d46c2e779b5d88c04c9d4b449879b5d88b74c9d4b41d8003d5e6d7621d4b41d7833cdaec44c9d4b40a879b8daec44c9d4b4368003cdaec44c9d4e45a779b5d88993a96892478003cde0d762264b4227
  | 7, 1, 4 => 0x3cdaec44c9d46c22779b7daec44c9d4b4498003cdaec44c9d46c307003cdaec44c9689e2270035d8899481d4b400779bc1aec460264ea5a8003edaec44c9d4b4497003cdaec44c9d46c1d700419e6c44c9d4b40a779bc1aec44c9d4b447879b91aec44c9d4c65a8003cdb8d762264ea367003e1e6d762264ea36779b8daec460264ea5a800419e6d7621d4b41d779b5d88b74c9d4b4228
  | 7, 1, 5 => 0x79b8daec44c9d4b4498833cdaec44c9d4b436879b5d88b74ca40ea5a8003cdaec45ba64ea49779b5d88c04c9d4b44f879b5d88993a9683a14800419e6d762264b4227003cdaec44c9d4b4547003cdbec44c9d4b449779b5d88993a9689e47879b5d88993a968441d879bc1aec44c9d4c65a879b5d88993a9689e368003cdaec44c9d4b401779b5d8899489d4b422879b8daec44c9d4c65a8
  | 7, 1, 6 => 0x3cdaec44ca40ea3670035d88993a9a8b400779bc1aec44c9d4b449879b5d88993a98cb44f8003cdaec456a64ea5a7833cdaec44c9d4b4478003cdaec44c9d4b4597003cdaec44c9d4de5a700001e6d7622650e5a6
  | 8, 0, 0 => 0x79b5d88993a9686ce0079b5d88992d089800f362264ea5a053435e6d762264ea5a7003cdaec43a9683acf36bb1132752d029e02f36bb1132752d3bcdd6d762264ea5a779b5d88993a9a8b4efd79b5d88993a969de6d76226520752d3bcdaec44c9d4b422779b5d88993a9683aef36bb1132913a969c00f36bb1132751b33cdaec45ba64ea5a7
  | 8, 0, 1 => 0x1aec44c9d4b4006833cdaec44c9d4b4ef36bb1132752d13dde6f06bb1132752d3bcdc6d762264ea5a779b5d88993a96892ef36bb11327531969de6d76230132752d3bcdaec44c9d4b4477
  | 9, 0, 0 => 0x1e6d762264ea5a6
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
  | 0, 0 => 0xe3f0000ef7c0000e000003de000e070000e07400fffc000ffe3003fff0003fffc00c7e0000c7e2000f3f0000f07c000003fffffff
  | 0, 1 => 0x33c138306010080e00e00180002304f3f301cf07c3f03fc3ff03ff03c0ff03fc0ffc00fffc000ffff003ec70003eff400c300000c3e0
  | 0, 2 => 0x33c00033fc00000e38fc0ff381f03803803e0007800381c0e7381d00000003800070cf3cfcc1f3c0333f1f830631f88cf3cfcc183c1f
  | 0, 3 => 0xfff1f8fc63108bf1c7e3f00c7e233cf3f33fcf07ccf3cfccff000033cf3f03e00078cf3cfc0e7381d33c03833fc0078cf381ccff381d
  | 0, 4 => 0xfc7ffffc1fff8ff1fffff07fc3ffc7fc7fc7fff8ff1ff1fffffc3ffc7fc7fc1ffffff1ff1ff07fc21000e07039ce077ffffffffffc3f
  | 0, 5 => 0xcfb0f8cc630f8b30c303300c3e003803803e00f780e00e001803de03803800600f0bffffffffffc3fcfb0f8cfe300fbfffffff1ffc23
  | 0, 6 => 0xfff1f8fc63ffffffc7e3f18c7e2fff1f8fc600003ffc7e3300c3e0fff1f800600f0bffc303f18c3e0ffc038fc600f0bff0003f180000
  | 0, 7 => 0x38e3f007cef0ffffffffffffffcc3ec7cf9feff7fffffff1fffe3fffffffc63ff8ffffffff18fffffff1f8fc7fff8fffc7e3fffffff
  | 0, 8 => 0x38000700000000e00000000000000000000000000e00000000000038000000000000000000fffffffc7fff8fff0003f1f0000
  | 0, 9 => 0x39c00000038000003800000000038000700000000e0000033c1383060100800381c0073801000000000000000e00e00f8001e
  | 0, 10 => 0xe070000000000381c0e0001c000000039c00000000000e7001c000000039c000000c7e00e7c7e2000e07039ce00400381c0e7381d
  | 0, 11 => 0x33cf3f33fcf07c0e38fc0ff381f003ec7039feff40038fc0e73bdf000f3f039cf07c00381c0e7381d000e07039c000000381c0003800
  | 0, 12 => 0x3800f700000000e003c0000000038000700e00e001803c200000000000f03f1ff1ffe7fc3dfc7fc7ff9ff087f1ff1ff07fc21
  | 0, 13 => 0x3800003e00f000e00000f8001c03800003e000000e00e00f803c203803803e000780e00000f80000000000000000000000000000000
  | 0, 14 => 0x33cf3f33fcff7ccf0000cff000003803803e00f780e00e00f80000038038000000000e00e000003c0038038038000700e00000f803dc
  | 0, 15 => 0xe07039cef7400381c0000000000000039c0f000000000e7000000000000000f03ffc7e3ff8c7fefff1f8ffe31f8bffc7e3f18c7e2
  | 1, 0 => 0x3803803fc0f780e381c0ff381d03800003fc00000e00000ff0000000e07039ce074003800000380003803803e00f780e00000f80000
  | 1, 1 => 0x38e3f03fce0740e38fc0ff0000038e3f039cef740e38fc00003c0038e3f000000000e00e00ff03de038e0703fcef740e00000ff03c0
  | 1, 2 => 0xcc30c000000f0330c3000000000cc0000cc000f033000033000000cc0000cc000003303cff3003c1fcc0000cc0000000e38fc0ff3bdf
  | 1, 3 => 0xfc7fc7fc1fff87f1ff1ff07fc21fc4000fc1c000330c3e3300c3fecc3ec7cc03eff730c7e3300c7e2cc30c0cc030f8330c3033000000
  | 1, 4 => 0xcc0000cf9c00733000033e70000cc30c0cf830ff33000033e0001cfffffffc7fff8fffc7e3f18c7e2fff1f8fc631f8b3ec3e3318c3e2
  | 1, 5 => 0xcc3ec70000000330c3033e7c3fccc30c0cf9f0f8330c3033e70000cc0e07cf9cef773000033e703dccc0e07cf9ce0773000033e70000
  | 1, 6 => 0xcc3ec7cf9feff730fb1f3e7c3e0cc3ec7cf9ce07730fb1f3e70000cc3ec7cf830ff330fb1c0e73bddcc3ec703800f7330fb1c0000000
  | 1, 7 => 0xcfb0f8cfe30f833ec3e33f80000cfb0f8cf830ff33ec3e00e0001ccfb0c0cfe30ff33ec3033f8c3e0cf8000cfe00073f1ff1ffe7fffd
  | 1, 8 => 0xf00000f0000003c0fc03c00fc00f03f00f003f003c0fc03c00fc00cfbeffcfffefff3efb1f3fffbfdcf8000cffc00033ec3e33f8c3fe
  | 1, 9 => 0xfc3f00fc03f003f0fc03f00fc00fc3f00fc03f003cefce3cf8ffdef03f07f003f003c0fc1fc00fc00f03f00f003f003c00003c000000
  | 1, 10 => 0xffc000fffc0003ff00033e70000ffbf38ffe3ff7bf0ff1fc00fc00fc3fc7f003f003f0fc1ffe7fc1dfc3fc0fc03f003f0ff03c00fc00
  | 1, 11 => 0xffc000fffc0003ff0003fff001cffc000fffc0003ffc7e3fffc7e2ffffc7fffff087ff3cfffff3c1fffc038fffc007bff04e3fff0402
  | 1, 12 => 0xffc038039c0073ff00e00000000ffc000fffc0003ff0003fff03c0ffce07fffce077ff381f3000000ffce0703e00073ff0003fff001c
  | 1, 13 => 0xfff0c0fffc0003ffc3000f803c0fff0c0039c0003ff0003fff03c0ffc038fffc0f7bff00e3fff001cffc038fc000003ff00e330003c0
  | 1, 14 => 0xfffffffc600003fffffff07fc21ffffff33fcf07ffffffcc180402ffffff00000003fffc03ffffc00fffec7ffffeff7ffc303fffc3e0
  | 1, 15 => 0xffffff00000003fffffc00003c0ffffff039ce077fffffc0003800ffffff00000003fffffc0e0001cffffff00000003fffffff18c7e2
  | 2, 0 => 0xffffffcf9feff7ffffff300c3e0ffffffcc000003ffffff3000000ffffffcc000003fffffc00003c0ffffff03e00f7bfffffc0000000
  | 2, 1 => 0xfffffffffc0003fffffff00fc00fffffffc03f003ffffffc00fc00fffffff0000003ffffffc00fc00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x37fb00037bfc008ee40008ede00164b000161f400d7c8000d6a30023b900023a680086c0000868200032900003068000003f7bfdef
  | 0, 1 => 0x220120204010088804808100402104b2d1018b06827027428c031000c0df021009d400dfec000deff0036db00036bf400d348000d2e5
  | 0, 2 => 0x32c80433588000cb2cb4cd62c1a228329234030684328344c6281800820903002060c92490c1624022221b020421a08880ca48100c1a
  | 0, 3 => 0x220120204010080086c0000868232cb2d3358b068cb2cb4cd6201032cb2d23503068cb2cb44c6281832cb2d3358b068cb2834cd62818
  | 0, 4 => 0x547df6541fda8d517dbd5077c3b545c46fc7fd68d517119d577c2b545c46541ff3bd517119507702154de4f571de0e4cb2cb4cd62c1a
  | 0, 5 => 0xab21b0a8621e0a2482422088380aba3b9ab623e6aac8ee6a188f9aab21b0a8621e09db7dbddd77c3b66976b674570edd97599d177423
  | 0, 6 => 0xab21b0a8637fbeac86c2a188782ab21b0a8600c02ac86c22088380ab21b0a8621e0aac8242a188380ab21b0a8621e0aac0002a180100
  | 0, 7 => 0xff7df6fc7fde8eefaef6edeaf9a99ea9d9b3aae62eda6d2e1ea782ab35f2a8635e8eac8ee6a188f9aab21b0fc6fde8eac86c2e5aaf8a
  | 0, 8 => 0x8209038021700208240e00010008209028001500200000e00044008000038000000000000200044ff7df6fc7fde8ffd2013f1f2100
  | 0, 9 => 0x54c804579c8001507801563780844964b478561f51251091e1506566156264c5519d5171195277065441442448541948a0ca48f00c5e
  | 0, 10 => 0x54de4f469541d553793c0e4085c54dc46579dc1955328355e7285c54c804579c811153a6d15e7a68254dc46579dc0855328355e72818
  | 0, 11 => 0x76df6f77ddf1fddb7dbddf77c7f54fedf579febf553fffd5e7feff54df6f579df1fd53793d5e7787d54de4f579c804153793d5e7787d
  | 0, 12 => 0x89a2998ba22f722682422e883c48982098ba02572ac86c2a3887c689209088a20f1153793d5e7787d54dc46579dc0855171195277065
  | 0, 13 => 0xaba090abe20f12ae0826af8095cab8000abe00512ae86c2af88782ab8329abe0346aae0002af80100ab2320a9e2362a888c828708cce
  | 0, 14 => 0xbbebbdbbfabf7aef2012efe2100aba3b9abe23f7aae8ee6af80310aba3b9abe23e6aae8ee62a883d4aba3b903802972ae8a66af88bdc
  | 0, 15 => 0xddfedfdfbfeff777fb7c0840210dde894dfbe8f137720137ef2100cd34d2cca74f96ae8ee6af88fdeaba1b0abe21e0aac86c2a3887c6
  | 1, 0 => 0xffebbdfffebf7bff793ffff797dffdc46fffdc597ff2013fff2100ffff6ffffff7fffcfc83f7bfd8aefb7fbefe77fffbe510bbf95165
  | 1, 1 => 0xfffffffffdedf7fffffffff2310ffffffdfbfeff7ffffff3add3f5ffffffceb40c43ffffffffffffffffedfffffeff7fff35bffff3e5
  | 1, 2 => 0xcd34d288a20f1334d3491215265cd2090cca60f1334510b3295165cd0000cca40513340ca73290d1acd0000cca40403fffffffffffff
  | 1, 3 => 0xdd7cd6dcbfcf9775711b72f7121dd4804dcbc840334dfef329dfffcd36dbcca76ff734d7cb329d7e7cd34d2cca74f9734d34b3290300
  | 1, 4 => 0xddca0ddfbca5737720137ef2100cdb6dbcfa76ff73608273e9095cff7df6fcffdf9fbcd7cbb39d7e7ef21b0ece61e0bbcd7cbb39d7e7
  | 1, 5 => 0xddfedf0210084377fb7f7effbfdddfcd6dfbfcf9777f35b7ef2300ddfedfdfbfeff777aa777efabdcddde4fdfbde5f777711b7ef7165
  | 1, 6 => 0xddfedfdfbfeff777fb7f7eff3f5ddfedfdfbdedf777fb7f7ef2310ddfedfcfb76ff777fb7f7effbfdddfedf8bb22f7377fb7d1a55275
  | 1, 7 => 0xefb7fbefe74fd7bedfefbf90310efb7fbcfa76ff7bedfed1e15a7defb6dbefe76ff7bed34bbf9d3e5ef964befe565f777fb7f7effbfd
  | 1, 8 => 0xf60800f5cc8003cafca7cf2fcdef23f20f1cbf33bc8fc83c52fc8afffffffffffffffffb7fffffbfdffc804fffc8403bedfefbf9dfff
  | 1, 9 => 0xff3f62fdeff7bffcfc83f7bfdceff3f20fdeff62bfeffefffbfffffffffff35bfa6bdbfdbfdf7fcfff63f62f5cff3bfd8ac83d73acce
  | 1, 10 => 0xffc804fffc8403ff20137ef2100ffbfb9ffefff7bffffffdf7fefffffffff35bfa6bfffdbfffffdffff3ff2fdeffe2bfcffcbd73feef
  | 1, 11 => 0xffdc46fffdc597ff2837fff295cffc804fffc8513ffa6d3fffa782ffdc46fffdc487ff2cb7fff2d1affcb2dfffcb46bff2493fff2502
  | 1, 12 => 0xffebbd579ca973ffaef51a50254ffeb24fffeb73bffa253fffa3c4ffde4ffffde5f7ff793f3ad5175ffde4fabf02573ff793ffff797d
  | 1, 13 => 0xfffcd6fffdcd97fff35aafc83c4fffcd6579dc997fff35bffff3e5ffebbdfffebf7bffaef7fff2b5cffebbdfffebe6bffaef73ad83d4
  | 1, 14 => 0xffffffaa700c43fffffd5877231ffffff3358b86bfffffc8940612ffffff02100843fffd9bffffdeffffedfffffeff7fff35bffff3e5
  | 1, 15 => 0xffffffa3d23b7bfffffe2ac83d4ffffff579de9f7fffffd5e77a18ffffff469549d7fffffc0e40a5cffffff02900953fffffea9c8792
  | 2, 0 => 0xffffffdfbfeff7ffffff3add3f5ffffffceb54dd7ffffff3ad0354ffffffceb40c43ffffff3add3f5ffffffabf23f7bfffffeafc8f9a
  | 2, 1 => 0xfffffffffc8c43ffffffffffffffffffffffffe6bffffffdf7fefffffffff7dc8843ffffffcf6fede
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 54 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 54 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 270 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 270 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 270 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 270 then wireAt i else 0
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
  | 3 => 5
  | 4 => 59
  | 5 => 501
  | 6 => 1576
  | 7 => 859
  | 8 => 19
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xdd8d068587ebbeb76e1f6de32bf048622116b6c2
  | 4, 0 => 0xf50fae59f05efd09e412dc03e3a43f04dd5be14add1aecc2da139d9ed3e210cdd249b67ed0e2d30ac9e11ea5c785cbf7c59adc79c56b2cd7c3326763c32df9dfc166087ebd84d9cfb3a9302fb1093d61af5eb8afab3c079c9f9386139616d5678eb9ce3e88c33210838ac70b834f19c77f1d7d587c66ed3a7bdb97337b1bab22798ab8836f00c72a6ac89b0464ae66135edce4cd5dbc98935d21cefb5c6c247d5c14e66a571a48b55662006d562d43d750c58a25451c19ab44dcb52c3bae6abf3b7ddbc6329408942fcfa3102d57433d27eafe4c1ccb4b3a1c9eabfe1b76815d13fe1e560c84e73b09ff579b
  | 5, 0 => 0x21d36b412000d6ea1fca25dd1f650d741f426e131eb161c11e4008941e0daafc1d04d9481b86f9701a6f9aca1a4343fe1a150dd21a0e0e30196ca0e418d18a6c186e278718376eef17c82738170d086f16d8b46e16c20106167ababa14f31a8c1467f41e143f166c13adb779123a1e4911f45ea9119217d810a447c01081e5dc0ff8d4400eb6e6710e6c223a0e3765260d97fb330d871bf50cb6d1e10c79f28f0ba9f0b20b6be2620ac99aed088389eb08627bfd085a20c20807ac1506b8efe9060821c405ab788a051d95a004d33b87042b1f1e03d3407003bfe0d7034b623b034a43b102b51b60025216e8023a36ea01b54c0b01373cfc01204fab00796abe
  | 5, 1 => 0x4551190a44d0f3e84479857a43ba464e434ac03242b779a3428dc58a42590cb542254c0e419d977340a6c27d4034903f401c1c233f13eb023e147f2a3d78a92a3d3c10683c9d75a23be5e98e3bd82cc9386b233a38355351382e3a7037a5b0c53780d5ff3779f03837108154366c5dce358f6bef358ad8943556e6073529bcdd3287d93031d01747318b93d13156fc53313295092f0c4da82edae5ed2e80cd732e7338f92e0236cb2d89e6562d2b50ac2c5351652a3198e02a2ac81c28e4560b2873acb228654c91280064ef27a8a3f5275dc42027560ddb274ebbf025a31684250b3e6a2493b3c5246d800b23e108e923d71bc222d6f43b2259f2bc21d91500
  | 5, 2 => 0x64b72f90640d4f5d6406968863f9e42463cf9d85639717c3636b22b963669d9561cd2d0b618a6a1061666769611ec37f5f9defbf5f9b97155f0cd58b5f07899d5efd00525caaac8c5c7fa2ba5aa8a6b95aa68a955a2afa605a183dfc59a0445d583465bb57a1bfdd577e2ebe56fbf48f567d130c56039e5c555e3f0a531a1290528873ed523d749b5187bbdc51872e0e50d4e7b250523ca9504daf1f501d2ed74f52da884f0d9c4b4e89edde4e85c1ca4e202add4de39f7e4ddea7a24d1acf0f4d01541d4ce015774b9d64f24b70617e4b4b962b4ae0bcd24a9e518c4a4c5f0d4a0a03904901fa34488375944749057a4700cb0e46a2d17045fe2012456aee17
  | 5, 3 => 0x85732cb684e8680b83d893b8833cfe11831ab8898211e0e081cd1add81c1d1c6813018cc8033c7f07f369d637f2d20827e7c1d2e7e7152747d9d73db7d8ecad87d6a3e7e7cf2005b7c25007d7bc320eb7b9fed3a7b9865cb7b18592e7b14bd9e7a7a23a8799337ae7860ae8477d7e1bd7790896c76a772fd7680fac474601fa77433fa1c73721cde736ddbc971792f0e715fe455715463bb70eeaddc70e6f46f70b4df866fa78ebe6e82475e6e7282286e562ff76e33b4c56e1b2a956e197bc66cb31ca66c9dd2616c74a8ce6bcf90f36a950dc36a63eb3f69e18490699703fe6896931a6834489f68121815675a8850667feca465d4792465694af9652d9691
  | 5, 4 => 0xa7d55d23a77fc6c2a69fb8c2a5e6cd1da590843ba4ed8a1aa467ebffa3edccfea3c4aa24a39d29efa35cfbb6a316381ba2711272a23fb8a3a1e94f4da1934eb5a16b6bb4a136af1e9f6e2c9a9d7ef36f9d01be6e9c41fbd59b3436919b29479a9ac0e93c9aa80fd19a6181019a06172e98a19efa98a05a6c989a692794cd33199473e953945efd87939a9e6192e8bc00928f3a4d92806526925b6a6a921f543b9190d39c91526071914fb84690a397f88f99748d8deb13c88de455e58d0a05788c76bee98c0d1a1c8adafe22897c1ede8934bc8a89153c8f88dea2ab88633b1687d5b2398755ef6286f41d8b86d946b08674343886342c0b85ef7c8485a464a5
  | 5, 5 => 0xc6398efac53414e5c4ec1310c43968eec39db288c327ab1ac28c44a4c25a25b2c228c216c2217392c1803655c1803146c0cafe79c0bd7c18bfb39434bf367d46bedd9d2abedbad5ebea336b7bd62e85abd3eebc7bcbbca35bbec3344bbdb6b75bb99b62abadd628eba88bda4b9bb622eb9498d19b88932b6b86f2db3b80a3f30b796ed02b7610a65b7416db2b58ed639b579079cb4eed351b4a3b416b46ffd5db46eb9a3b46b266bb448728cb3facfbcb2666447b247bca4b104327aafd60e4daf727cf1ad6d5218ad25e2dbac633309ac34fcd2ac1f1206aba3a126aada2ddaaa6d8de1aa32834aa9ffa255a9e3e07ca993afaca98670d0a926e6eaa816b5e9
  | 5, 6 => 0xe6651ad6e5bc61c4e5447448e4aa6d3ae3a0d4f4e3322541e3055e51e2fe02e2e2a54940e259ae6de13395dadf082da0deca6df7debb2123de7a3572ddb49b66dd59e3a7dd3fd063dc385fccdc2b606bdbe50096db37e196da5f439cda476c3cda17e148d96b098ed8fda80dd8a2e1fed89d39a8d72f8afbd4c71adbd458ceb1d38d7cf1d38d72dad32129d7d274ce1fd2061043d1a9ce41d1529d48d14857e6d0680223cfceec51cfac23aecf5af697cf4e8f3dcf18dd1fcdbcf587cd5f1ae5cc8e72abcbe47fb0cbb214f8cb68375dcb5d4866cae2d399ca430f2bc9f5c996c97b4c03c96833eec8595d10c7ab504cc7a74112c6fb428fc6e5027ac649ebf6
  | 5, 7 => 0xffeac083ff06759dfecbff17feb29b76fe0727f6fdfc38fffb71faf4fb4d86c3faba4034f984a0c6f96feb04f8cc43baf89a03eff735d725f6b08ef4f6960d31f670cfb3f5e77c9bf599ff63f57b6daaf568a6a7f45f73d5f4591915f3f8f7b4f3b9cc40f39d56e8f384bc0ef355e703f1fcdbc4f0cc763af0968af3f08dd881f08513e6f04bdcbbeffd19caee7d4306edfe2d87ed5ff0f8ecb5b939ec1f29efebb11d4aeb7a34c6eb66372beb5a3525ead9e5cee9ad18d9e97d8de5e91f6202e91b0d51e7bb4e07e794266ce6ade019e690d205
  | 6, 0 => 0xc97cf590c2225c50bb7fee20ba77e000b5334f40b2c8ce60b28f6400b258c830b09f3650acc38510aa0caca0a5ed5a50a53c4d609d24e7409bdf0a009695d400941c54b093e7356092d20e8092be94c0919997808c00bc9085c29ce080a8eb707fab1ba07f1b6d6075d2466073a22a10737882a06cd9ad406b5fac606a4087106596465060f596e05f2790c055f0adf050dc1e804d32ad803f1b95203cf5e0b03ae4e9903abb2f0039dbf55033b05b502eaaf3d029aef9e028da25d02898f5e0285087d025cb666025216e8024ad8f90240dc1801f5db9e01a6e4da019c9fad0198403d015437cd012a584000f5a3d2008dd725007dbb7a002e9cb30014cd4c
  | 6, 1 => 0x1415063f1413d60813fe949713ea83c213e90d2b13b3dc4e13adb77913967e2f139302bf138cad001317dd2b130a5a891305f52212db4a7b125d0b7e1248887612324797121c41ac121b11231187183a1161181a115b67ca1142fa41110f8d8e10d7221f10c5277710b7c9a8108ef5b9106ef59810532c1f104243571015aee71004221f0ff073950fec104b0f8899180f865b750f79f41c0f6345690f47a0390f21afa70eff00d20eed14a20ee672b50ee2d2210ed86b730ea71dcf0e7e15130e6ebfe90e4ddd170e1ee4940dfbaa4f0de224890de1cc4b0ddd4aa00da962390da6941f0d9cbe430d95c7350d86abda0d2d22890d2aded90cf439bf0cb015bc
  | 6, 2 => 0x1e2780c41e0ecd901d826c881d825b1b1d4653921d2d215e1cf34cfd1ca0b1831c96ea491c0c1b4b1bf725aa1bf5be811bc5498a1ba64fad1b933b9e1b78d4bc1b61a0cd1a87fcc01a8148131a6b63331a25944819f6ee7f19cd069919c2b1f019ba301a19affd6f1977419919749e0d194f93b81921f28d18d274d918c4770b189d69961892cd85186cfbda185955ec1839cef017f938b617cad5e217bd8d8e17bcd81e1729918f17206e351712096e16b3ccba16afa02816995adb168bc85d1673385e164f38e016256de516100cbf16066cd915f022ce15c3143a1561a43a15608d7b15602014155cba4e151b16a5150cfd8114db18b514736e8514649f8f
  | 6, 3 => 0x2a222ab32a1317a02a023a7d29cba47729c478db29990f44296b38aa292576e3290647be28e1d56328da4aaa28d3f68428bc54b328a20861284a715827f9aa2127d2a8772707a0fd26786863262a32f4261ef6c62604931525471fea253ef9ad250b3e6a24fedf5924cbf971243971d52416c07e23d2578423aa74da237feffe2373cc5223057c1922ea3ac022d2ddb12278b072226df44b2263093522521a042238f64221d8db4721d562ba218ce6fb2177d42821730a3e20eebdc420e249a720d5617920bb659020a84c14206a118a206969b82062e284205b0a2a203ca2472015ae6f1fcb8bd31fac1ffd1f6239f81f06a07c1efda3231eb6c6781e400894
  | 6, 4 => 0x3389f6ab33864f1f3380d2fa336e091f335d81953327d92c32f1ebf132e16b8932def36c31f21e3331b1ab293177ea8831752de73157bf6e3156fc533130272030d52820306aaa7f3067a33530631eec3028fd262fdcbf742fd3b15e2fcfbe272fc6445a2fc5bf282fb10f502f8f1ff32f8141142f7e6ae62f6745e12f2fce4c2f1abea52e8fba352e8108342e80cd732e5125f22df741622db09fc22da94f942d9f970e2d7296ec2d6d756d2d3ea4312cf8cd042cf085992ce3b7132c4d2a222c2fc9bd2bebe72d2bb2627d2baf6f8f2b83ba742b77b9702b52c4ba2b26d94b2af68de12ae9f3842ad6e7a92a95810c2a83c59a2a6bc7352a6347522a3198e0
  | 6, 5 => 0x3ba7c5f03ba09a7a3b9e4ff53b9743c83b8aa58d3b36b9843b34c0e23aebff0b3acf9b4b3a8122023a7c3c153a5b119139ffcc7c39b8a2b739b6850939731d65396f572d395f2ed0395b9cf539514ff1394f142039334aec3929da4e390153ab38e8b0de38da452b38c8629238afba57386b233a38695c3f385c254e3819d239380d7bfe37fdfb7837d8b5813794e38c378f31e8378ba63f37596ec33748575a3710072a36b5383e3679dd0b366fa272366487033610c82c35974020358ad89435787e26355e29ce35239d6d34f524f934ecd7be34ceb8d134c589ee34a750a9349995fb3481847a347c735e344da1393428cd4934064f6c33ce1343339be830
  | 6, 6 => 0x459774c2458338fd457e7d57457c8acd456daacd45280d84451ed66944c7681044ae84d94490ec0c441e848e43df582343db6ae443c469ce435a2562433f660a42bb11ee42b779a34291ffc9427c5b8942672086425327d7418c58194183d8874115ab1e410d769640f66c0b40f404f840a60e3740936de1408a06cf406a83da4062ec4240455b7a4041a8df40177a0b40066efb3f69bd633f227ddf3f1e2b9c3f0262fb3ef9b7083ebfffd23ebac68e3e9b9b153e56ef7b3e0ad2fb3dc47d1c3dbce7733d7dc3333d4903cd3d2ac1fc3d0d03b53d0124c93ce437ac3ccc486b3cc696da3c84ae723c7acf473c346cd83c0ce04f3bf4ea113be497a23bd82cc9
  | 6, 7 => 0x5059633d503999f0500307f24f9d1e774f8c57c24f86a4154f7b0f794f4c81644f2dc6724f29237a4f135c524eec3b944ee3183a4e9d19034e89edde4e6d16534e0aa9784de1baa04ddb76074dc9c7c04dc7b19a4dc656d84d84259f4d67b2e34d43a2314d2f3d364d244e3f4d1acf0f4cfd734b4ca1aa074c7463374c6601af4c46545e4c1e35cd4be3ee324b51d8934b2472944b03fc924af8703d4aee73794ad762854ac953704aa02b774a8b09ee4a8570144a6717d14a3ff2504a2e53494a0a039049c0fcf449894780491e4f544910933d4905a446488ad56b4824b16847ff7ab346df279b46b55adf46b021cb469949b54631f35845f126ed45e00ffb
  | 6, 8 => 0x59e9114a59d5a23b598cb1c55989a08a58ca2eae58a9df50588ac9355886e5b858817b3f5875705b585fd550583d5a595817540b5813f0b4580611d557d21cf857c03d2857a1bfdd578a39a25712d2ee56f411bd56d7ea5656d29d17568ff7f1567d130c5672a4875659605e563603f25618ad15560915a955f6748055e93b6a55df5df855d88bb7557f4cd95571ce4a555c889c5530a86c54fdc76d54c66e2d5488605d546b22205459014c545833245427678854198a3e53bfda04538c2b2c53466db8533fb48d53181bf852e71d0152e2321e52a439b552a1f517524e709e5247743851ed228251e9127651bb2a0f51954e1e5139dea7510a33e250eca9cc
  | 6, 9 => 0x65381a0264789948646b996f6452482b644d72e664179578640f62e363a63bbf6386d6c462dd8f1e626770156264afc1625d86976235df0f62261eff621cd20f61f63a0061f427ee61cd881d61cb6c4d61ab00a9618722e06169ffad613f4bb6611ff8cd60fbe7f960f47f6c60dc0ef76042b36460205a025fce787b5fbac6fd5f4ce3e85f3648d15f31e5c05f20e9805ed6a3f15ebac33b5eb5ede35e82f8175e5e95475e5903545e22a7545e0e53495debf6475d9db11c5d59fdec5d439c1c5d1e66bc5d0eae245cde0cce5cc5425a5c8357335c50e6185bdee7215bb03c075b6fefcf5b1f7a795b023f875ace577e5abcb8a95aa2af7a59f4348059efad2e
  | 6, 10 => 0x6e027d566dc2375d6dbfabf96d8815996d76e7956d748c516d67d5df6d483b2f6d26125d6d0c81136d035db96d01b3cf6cfdbf986cf9e7a76ce170276cd6ca796cbe1d396c80742d6c7eacb26c66f60c6c5bf97a6c4b6e046c49cc986c2d95746c2aeef76be903d06bd3e8686bcf90f36bcccd376bbe0e9d6ba0f1c86b4493be6b0ca3d16ae97d196aafcc206a923d956a8f01346a610cd96a344b406a258de669c0add469148b6868ade54568959ecc6885fcc06854735f680cb64d680392f367faa20867d94152678eb540677d84d8673f974f672888916725e9c5671ea51e66e9390a66c97e4e66b0a48a669a4886665174db6644c8f86624d4f665ee6d3a
  | 6, 11 => 0x785ee2587800865577cf974077728e4a7768e8a77730263a76fcecf676f0de3376e1a5f076a582cf7668611b765bdd3276509acf764692e676461d7275ce6c6f75791c4b756948e67502d39f74ae25e07495e96f7481ccfa74564971740e753073655c0c7361e71e734eaa0d7306471f72ff2f9d72b283397221207372002e2e71fa161671f3b43571d8f93471c4843571b731cf71a7da9771a6de3f71a262417179360f7166cf877130886e710cca2270f077f170e9cc8f705b5d9f7041bbc2703b7bb470345b606fe548956f9a15cd6f90c8936f7090bd6f63d0f66f567eab6f51dbed6f4ebd9a6f43e1be6f271ce46ef1ab8c6ec13cc56e3f00b06e0d4a90
  | 6, 12 => 0x823a9c3e82348b3c8222c68f8220babb8175c915817106db8110235580b1b4cd806266ad805c90738056248e7fdefe227fd8d7587fd11f437fa7685f7f4590c97f3d62797ef775487eaf48d67eadd0e57e912cbc7e159c437e0c74cf7e05acff7dfb85ac7dc594b27daa8d6d7d8e4bce7d7d57bc7d3371107d2a63907cf889057cea112d7ce9266b7cb1fb967c4faf817c0dda9d7bf0b2df7bd28ea77bd019c77ba3c0797b9fed3a7af389fa7ada8ab67ad3415f7ab2a4927aaf2d897a8ef3507a7382a17a36543c7a2bf43679e5550479d3e13a79bfc59f79bb6d1e797004af795acc8c791c125478e6cebf78a46f127893519d7877b05378761744787589f8
  | 6, 13 => 0x8dacf6f48d88441d8d72216c8d32e83b8d2eb7558cfa91f68cf6da0a8ca14df68c9a668c8c5291f68bd322518b4b91ec8afc87408ae257588aafa50e8aa45d458aa42a2f8aa3b04f8a7ee8668a7994f889f27f8489efee9189b9a4c58958e8bc8934bc8a89143e4288ede02888dbccf288bd66ca887ddfc28826fc3987e7ffe087a030ec8759f0be8756c638874f9269873abea486fe088a86d3f20a86be95e986bb6894867726a185ef75c6857f1b668540e5b08527bd3a85184ada84fb0b2c84f92b6a84e9742a84dec8e884d0ea09849e475c845f90f783ea69c583d7542a83c0be0983a21eb183629097833df90382e1f31882de711782d65b2b827963fa
  | 6, 14 => 0x992c6b7e98e3b9919882e2ec986d00ac9857d41098386cf697cb439c97885ff9977488ac976491d0973d9af496fd835396e560fb96bae4c896ad47ba965531e695ddc41b95b3875295a7bcd395a0aa079570831894adb8bf94aba5ca94943acc943bd39a9419634b940d9631940a6f839407d37b93f38d2a93e24993939a9e619365df50934b343293342c279322c34693154ea392cd311e92ba7ebb928df7689249c75b9235af529233bc8791f1d16091e8ccbe91b3cbf19190d39c918b0169916bb660914d614e908462249066fa26905e4b30903730748f4fdf788f4a16428f3acded8f0aa4bd8ebf00228e7d732a8e3f8c778e183e158dd7584d8dce939b
  | 6, 15 => 0xa3913837a2efe0c0a2a97873a2a0e2c4a29e4ecda284b47ea26ac20ea2487bd3a1f16defa1ce7e41a16c4690a13c87fba0fec4d5a0f04834a09190e1a070683ea06f7c80a02ef21b9fbc36d19f9ea33e9f77feb79f726bb59f6676b19f0c76639f092c3f9ec0d7899ebfb44d9e3e2dc49e3c45669e0a09409daae7359d99351f9d4043e99d2f099b9c3b434d9c1ef4619c0647769c01232b9be41d5a9b8d299c9b7a6f559b74bd5f9b571a669b4650979b34b1219b0c63a09af887159aca79e39aaba6e69a5f17019a4ad2999a35a57f9a18a88399fd1e0d99f80ac699bbf508998f2d11998cea0d998829a3997632ef997374ef996e299c994b9d0899440663
  | 6, 16 => 0xae110966adec3e13add28485ad965e55ad58a5d0ad0cc562acedd5b7acec63f0ac54c35bac4df83bac38c2aaabc24d7cabb996c5ab8bcb77ab676f4fab47af95ab3e2661aaf5dc2faad9b799aa67fba6aa00aaa3a9dd3bf7a9d57912a9c4420fa97a0c43a9762739a95d0e24a8e78fc4a8d62ca7a8a73885a85da819a85b062fa84782efa828f69ba822b426a7fbc882a7e69d5ca7e1ec9aa7be4cf9a732a1a6a6e98352a6cd1d65a69d5214a6910249a664f1e7a65ef21ea65ebbd6a6563cc3a649b5c6a63c52c1a602287da5fd28f8a5d7b751a5d42f5ba5d3bbe5a5b035efa4b188daa49fea3ba4033c3aa3e9ce97a3a56a26a3978b47a3975e0da391e913
  | 6, 17 => 0xb8c07ea2b8bc058fb8767b00b84d5911b7dce78eb7c9ca50b7ad2f8cb75c39a0b729f7fab71329c5b6fb2445b6be7634b635de6ab5b29b6bb5995d73b5198f66b50f2cb0b4fc8e64b4bad623b4b7aa29b4442e98b432738eb42863c4b40596d8b3c1e194b391ac48b37aeefcb36d3a2db33db3e6b31b835cb2e06130b2d40c22b2d110c1b2c70f7fb2ad64c6b27deebbb27cccb0b2700fdcb23ecad5b2227074b1eae14fb1ce22c6b1aab58bb1976043b192c005b182f0c4b164572ab110e951b0dde46bb0b9922fb0619e49b055f4d1b01ef75baff20c80afbb0ccdafaab267af777a6aaf616e2baeeb3210aed94acbaebe772fae61e220ae18ff3dae11518c
  | 6, 18 => 0xc24ddc2ec2472df4c23cf56ac23c3efdc22cbc1cc1fa1783c1f8fe15c1b77a4ac1a99556c1907b16c13e825dc121cba0c0e8397bc0d8bcdac0b02379bff5be0ebff1f28cbeefdc2cbedf3b8dbec0a575bea336b7be95c8fabe70a23bbdce499fbdc979a2bd712593bd640d13bd4b0a16bd3f82f8bd2fb554bd0683e7bccba248bc95da00bc545819bc19ed6dbbe3d513bbd1589fbbcf1011bbcc115cbb7ee8f8bb6820b3bb44492bbb3da774bb28b1adbb11473fbae1c4e0bad4da24bad03517bab9a1bdbaa3d292ba88bda4ba85faa9ba701036ba5b88ccba565299ba423037ba231cbbba1aa2e5ba133d13b9fe2647b9d7cf39b9c196eab90fb401b8e03f25
  | 6, 19 => 0xcc7593fecc6d1337cc4ce26fcc452051cc338a53cc314ee5cc1a159bcc0ad82ccbd5b4f2cb7814d6cb66226ccb5a385fcb3988b3cb22d64bcb1e4e07cb09853fca8af8c4c9ff3712c9bdabcac9b0660ac996b3b6c993c7a7c98c6e10c95ab98bc945c0d2c90a98fcc904d60fc8dcf1b0c86a7b32c82aa73ec828f799c809f2e1c7fb6ba2c75d9bc3c75c2593c7554d2ec7327c7fc731841fc70b1e59c6b2dd46c6aaa746c6a95673c694f353c64e72fcc5ae265bc59d6c30c595198ec572feb0c5382f90c5368674c4acd4d8c497cd3dc4745ea1c42e642ac40a2416c3d681efc391afb2c3432490c3334588c2f978fec2c56a8ec2bfb77ac29a9771c2772a64
  | 6, 20 => 0xd508da27d4c1c33fd486ec14d4725d87d445852fd438da3ed3fd79dad3d2caa2d3bfb42ed3b9e099d3980975d383a931d37b9b4dd342c3fbd32129d7d31c5cf5d317dc6dd3024a1dd2fd1e15d2f75b26d2d1a5eed2849381d282ff82d2370a95d1d3f658d1a278a6d17bf5cfd1358e44d12d3400d0f6d7dfd0e64a54d0cf7350d0a6a70fd08e6ef0d04d744bd028b587cf7566e4cf6e5413cf524e2dcf2c5820cf1f3ed4cf18dd1fcf000eafcefdaf14cef7ca4bceefcea1cec778f9ceb4067ace814ad2ce745571ce72f0cace08daddcdf98342cdd3764dcdcd35ebcdc288cbcdb0a1f9cda6e723cd969af4cd6f67d0cd13336dccf24bcbcca414f9cc9b4d7f
  | 6, 21 => 0xdfbea839df7b7600df75e0f9df6bddf0df66edf2df5bf037df51dd7cdf204264dee6275bdedb2a3bdebe8247de41358fde312a05de23d5bfde059452dddb30c3ddd7a141ddb7dd18ddb5fd1cddb1ac85dd9de376dd93fd71dd8ed5d6dd5b2d34dcf5126bdcb96231dcaf7ec7dc530e5fdc1c3838db9b701bdb71c496db5cb9b6dafef9a9daf18bb7dadff429dab03a9fdaa10b17da60bae0da0ce6cfd9fb6b94d9bf06ebd99b8409d8c89669d8a2e1fed85d0165d7d69a16d7adc8ffd78c0afed786c099d783df75d748aebdd7168563d6f3fc90d6c3a000d6b73d34d676207ed673d0cad661e951d65ec261d627c4ebd5f3eb55d5ce88c2d5b6ad2cd52b0a13
  | 6, 22 => 0xebc7f551ebb0b335eb6a4ac1eb1e533ceb023407eaf7f023eabceb59ea88b923e9e0e609e9d9bca8e97a8bc0e945efd6e8cbcf91e8796d32e8623c33e8372b18e82172bfe80b29b5e8047120e80138e2e7c7a396e7abfef4e7a75556e775de2ae75ebc56e6f5a3e6e6f0c116e6ad2c24e6886563e61e3e4ee6118099e5c286a5e54c555fe5432933e5378123e4f3f667e426fc9fe3ecf174e3e84fd4e383dba9e35f01f3e358b1ffe2f6af66e2ee6b60e2eb09aae29ba2b8e250302be1dfb350e1d99749e1b1f408e18ace26e1808a81e175a2ade126cb02e11a7f21e09b3ae1e0930e9de064565ce0626e26e05c847ce0129c16dffa03e8dfd69e60dfd68d84
  | 6, 23 => 0xf79aba4bf755edc8f74120e2f73a66a0f71db1a3f6f16d4af6d3c780f6a1142df68e6a67f6535463f62a4690f6260c95f61ecacef61da697f5ebce57f5b9b417f58f108cf57a4822f576f928f5277aadf512f24df4ebb8c3f3d60f87f3cea65ff388db30f3740fcef360add7f3041da1f2c92a07f2c41b18f2a33ee6f29edce5f2978429f2854adff27d326af2681b9af23a1c75f21a5b36f15a4793f117a0a5f0fdb089f0e8b557f0e86fe3f0556ec8f0297054f0158209efefa548efdfd1c7ef831902ee8c0f30ee622b56ee1fa362ee1641d6ed215bcfecf2ba94ecc260f5ecaad606ec9be3e4ec53a50dec338729ec17d5dfec0c1396ec0915fdebf03b1e
  | 6, 24 => 0xffc703bfffabe638ffa01f3aff9ec55eff98826cff91be5cff55b127fee788cafe5cb65dfe4d0768fe3673f0fdf82a2ffd9b65b0fcf8d17ffc78f6f8fc392c47fc30abd5fc2b3a6efbefb591fbac7402fba4cc58fb89f1edfb314dddfb294fc5fb07d043faf92908fad8dc57faba4034fa7f4c38fa7be838fa56aa6cf9d074b8f918fb51f8ff31bdf8d5ce41f8a016c6f876ade3f7e6759ef7d45d73f7ad73db
  | 7, 0 => 0x12ae5da31232479711ed84b711d7480611b4128d1198114410d1aa9610c280c5103ead2a0ffdfe370fc22fb60f60b9f30f5c5cfb0f3d84400ea68d810e93ae780e8414b20e7dd0190df078900d61f2fb0cf91d9f0cc7aa850cb3009d0c867e660c22507d0bd753a90bb2ffb10b41c7720afb5dd30acf09dd0ab8b26f0a9628be0a71f9560a172c4909f5ca2f09ee1b6f0878675807d82e3c07bd347d07af559e0754ea15075140fd06634425064612c706291d83061ab28605c61dd60590310f04d0acec0452788e040745c603e36454033b05b502e9d44b0296f579023f103c01a603fb0198251c0188fb4b0129b75501283a1700dd496a0086a50c00103def
  | 7, 1 => 0x246ade962429651523fe6fae23a7fde62325e28c231857ea22ea3ac022daf26b22543c1c22521a0421e9d24d21698b1520df43cc204aaf2d203e530f203cd04e2015ae6f1f9bef851f608b651ee4e3db1ec21db31ebb13731e739d441e3d0e221e17d8601e08e1531d29fe0a1d094b741ca0b1831be563841b8548e61b78d4bc1b70b1901b61a0cd1b2d157f1a5d39541a4058c31a2bfa9c1a0ece7019deb3e219b1d448196672e1191531f418e3fb0a18787ffd181aa94117d07b0017a82026170db67f16e8db1816d8a81c1662ea0a1647ff7315f86a801581f8c81561a43a1528ba3c14e6b4ae1413d60813b5da6d135211a2131bfefa1317dd2b12b8ab41
  | 7, 2 => 0x357bcd57355e29ce354bc4fd34746a9f342cdee933d93c6b33ab0d08333d92c433193e9a330961a632e7627a32c3d3da3294bf40326a06213243d5cd319b3e42317141fd315024ba31381b073129ad3f3055c0a6302ca7772fc976f62fbf18df2f7655c82f62b4552eedfa852edbd6b52e46479b2de85b922d90db782d770a592d6df75a2d014b912cf085992cae27f22c1543872baacaed2ba064522b48380c2b0f56702af4104e2a7c85282a6cf0712a5175e42964176b292df8a1291abe562882e2b2284db2db2774c4602727707326aa53c326a4b5bf265363bb264ea121262d41fb261c309d25bece64258a6ea4255ffecb2509c4b824cb7b292485a934
  | 7, 3 => 0x4609964845f6b58444d9dfff44cd758b43cee64d43b9f0a343a9f848433f660a432891ef4309ffd842b779a342815d8a4223bdb94215deda4214fad141a83906413ca69640db2d8b40bb28344079af63405c8f3d40455b7a4025ca0a3f8b9abe3f086e6d3e4ce77f3e1c8eb63dff89d03df1aaf13d6d0b963d18fbc93d0124c93cedcf813cd7d7c23c9f3cdf3c9dc2fe3c8fe41f3c39fd5e3bf3e2703bf167e33bd0b7833bc2d8a43b76a7473b23954e3afd7b253a8b9b213a861c993a305add39de879e38ad846e3899ed1837a1ed1c378f31e8375fd1e83732d33a3724f45b36f4981f36b6da9236ad5160361b1af435f834e935d89aaa359aee6d358e7c13
  | 7, 4 => 0x5905159658a5f177584e132a5806ebe256dbe56f56da22f056abec62568ff7f1567ee6cd55df5df855ab6c46557f4cd953b7a8b55342fdb7531915d153169294530ec13f52f2fea452e996fb52acbe7d52943af552942b725275541c51a4e007515c2919514f645450c9577f50c4b4ed5038abd64f490be64f0fba7a4ec05ebd4e9d19034e79bd534e5bae794de27c5e4de254b54d2b306b4d17706a4cfd734b4ca60af44c173de94bff26be4bf147df4bc969994bb8974e4b62f61f4afc5e1e4a6707154a5928364a3f78dc49e125c649d602e84980ebae49226c8f49148db048fa38cc48f889f848ebd2aa47f69d2646e1bded46e149a24696c818465e79d5
  | 7, 5 => 0x6bcb63fb6bc490ee6b89f08a6b7c11ab6b6909ce6af785736a4f22086a0139de69d0a4b069c0add469c031bf692e70ee6920920f68ff5c7d688d1b55679d352a67425c616709aa6167044c4c6659a12a66357542655d93796449b75d64015902638147926379a6766347643b633af01163353df463275f1562b43c1762623a3562542af861f427ee61abfb7c61aa33686129ea2960f8c4a560b58bf56001a2b65f5d13a95eebace45ec6f1c75ebcebc25e90082e5dc82fa15d6275f45d2e415c5d23bf8f5d1e66bc5c9fbd605c91de815bff541c5b2acd595b0171135a73054d5a7078f85a437adf5a3c07d75a1dcce559f223e55992adb05943cbfb5923c1c6
  | 7, 6 => 0x7d33ff317cd372a07c439fcf7c0721267bf0d3337bc86ac17b4614867ae97d0f7ac854af7ab597257a85129f7a70b12879a4d76c7952d27478f04d34785a178977f10ba277d135d077211a3f76f0de3376f0916b76db0b2e76bdf4b976b015da766385db764692e675c5ccea75400898751c82e774f2245d74e1bd61745a681c73a4532b7341d2fd72b28339727daf3d72739f547263b2ee7260e48f71fb25a2714a8ba9711dc56670ffce1070cdf07470c4152b70946692707cee8d706753916fa6c90d6f6c29a26f69601f6f3b46226ec13cc56e9f1e276e834bca6e8018a76e38e6f66e34ebde6ddedbb86d483b2f6d45b13a6d2657c06ce170276c8fa51c
  | 7, 7 => 0x8fe9ad8f8fa4cc1f8f6e24048f255fd78e7679718e4941358e35cdb08e27eed18dbfa66d8d7f04bb8d6fdaea8d3d413a8d1e3ac28ce77a638c76bee98c1a6ee88bedc1998bbc73f08b3e939c8b308e208aef68758ada8b1e8a8bfac78a0d10dd89f226db897643b689605ac28958e8bc89143e4288ede028886bb2a5881ad29987cdddd0877910e2876b3203872610b887080352869b75948651842c85e99b5485ba4fb985520fcd8549f6d2850f030e84e9742a83f048fb833df90383233d80830766bf82ddd8a58241b05982121d0d81bd8a2f81b633a5804281917fb9fc427f97da8d7f5f0e0b7ecd8d627ebbf6017e8559377dfd47397dad4e397d356db9
  | 7, 8 => 0xa6395456a623790ea5d7b751a5cabbeaa4dede88a499e38aa3f2435da309310ca302d5f5a2f4f716a2d8fffaa1c6431fa141bf77a07b39919ffd08839f9262399e58572e9de02fb29db654639d61744b9d42bc1d9ce015509c27c3cd9bfcd7929b71391a9b56a6c89b1dd7b09aec1f2b9ab47d5a9a81c9ca9a36658d99bbfbc99985b807997d456498fcecee985a34f7984899db98411d81981b7e92978d297c97251c9896fad25696a4b77d968ac1e99603a49895708318955a0898944ede009409b1f09396353d9351acbb92ef4533929a9c84928cbda5927d8384927a567e91bec62691b98d1291426eab913b5e9f908ca4449074f28c900c696690061e31
  | 7, 9 => 0xbbe49247baa8a17cba477786ba45dd7fb97e2118b9782853b85c2f59b84d21e0b7a3f583b713f0d0b6edc245b67d321ab65f3e8fb5c9ec3db59a84ddb5195244b3feb3cab3f8265db32b1ae2b315333eb2f03ccbb2dc7687b2572353b253eee6b24f00d3b23cd636b22e7c90b210ca3fb18cc501b16429bbb108215ab0e1dcffb080f6ebb0480e0db02268afb01ae1b0b00d02d1af935789af01b67aaec64c0eada32de2ad85a160ad6e1b08ace974c5ac3ab49dac296414ac23afedabe5308aabbe6e52ab962e79ab94b348aabfa2cbaab1140caaa935daaa87c3f1aa3f12b1aa07d0ffa98c5b5da9647ee6a909e4c1a8e78fc4a8d9852aa7bb98b7a6910249
  | 7, 10 => 0xd0317033cfe713d2cf84bc20cf0c769cceecb93fcecb96dfcea2794ccdfcbe79cda803e7cd856bc9cd6ebd58cc0d7bc5cbfcbae9cae6d7d7ca5eb5a5ca35eab9c9e65a89c9d88a90c8df6e8fc876c3bec7a9b843c7a3ca76c7554d2ec7466283c707ac1ec62ad07cc5e58a67c5dca5abc5d3e588c59d6c30c57cede8c577bfccc576ef75c5690328c4eae2e7c483e9fec4605fcec41df566c3935453c37f968dc33e8ebcc30bd3fac21dcfbbc1c6e06ec1c16a74c16463c6c150c440c1043454bff0ea6dbfa41077bf46884bbf01fb40bef1afedbee065e9be907f01be6b5265be107ab6bddd5bacbd5c9ba0bd3f82f8bcf5d0c6bcb2dff7bc5e25f5bc545819
  | 7, 11 => 0xe5b5122de575a6eae5179d48e49194eae48a3599e45c7de4e3ed24d8e33582dbe32cc12de2f7dbbfe2f6cc76e2f02cffe2e94854e25263cde21fca1de1e7aed7e1ccafbce1b94d76e0f3695fe0d27efae07b344ee04a17a1dfb32b5bdf91a28ddf6d0221df41afa0dec9aaa0dec49712de1b0bb2dd547ea2dcd6712cda802b72da8008d2da26b2c9da0af02ed9ed2281d9eccea3d988b69cd986de71d8f62b1fd8e7dfa1d8653959d7d8277ed69e993fd697c1d4d64007d5d5d7c256d5d13c99d58853add4fb6d4fd4f736c8d468faf0d3c1c38ed3b34341d355d4ffd2da325bd27a66b2d229a3e5d1d3f658d1b38e6dd17f337bd0a7e5c1d051c79bd04a50f7
  | 7, 12 => 0xf9091127f8b72109f80ff336f7fbcecdf7e68aa8f7c476a1f772bfb1f76d67adf762f14af734b506f6f16d4af6e94291f6b08ef4f6655c2cf62cba88f62c0f9af5493ef0f50771aef4535bf8f30da622f22186e7f20a7ebff1c7ebb4f15afe71f14d1f92f11d8484f109fd47f0dd9aa2f0c5c7cbf053c1fdefeaeca8efdfd1c7ef4adc1aef0e3eb4eef3064deec76f65eeae7dabee570e7dee1e2c58ede64ad6ed5ae6a4ecfeda8beca193e2ec848404ec164c1eebc28ee5ebb77889eb7a065aeb3fcd10eabec0cdeaa64cb1ea72c195ea555bf2ea39f55de9f23fa9e9d3bc26e8b54ab1e8b03ee3e878be20e86f0f45e7a75556e7199440e606f433e5d4dd4c
  | 7, 13 => 0xffabe638ffa13466ff939cefff8b32caff3df527ff3992a2fefc312dfebf47eefd875a02fd797b23fd75d7f8fcf8d17ffce2758bfcb4afe6fc3e0176fbefb591fbe5e7c4fb7259a6fb192d73fac274d4fabc44b5fab495f5faa130d0fa58df1bfa4dc81bf96feb04f9092d95
  | 8, 0 => 0xf33b5fd0dee29a6add9de376d1efb8f3c2afde01bad4da24b47be6218ab84b5d7e1a8a56764e5f6161ca400842b779a33e277fff2efbd9642eedfa851e7359ed1729918f1606144c01bed059
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x70109355084010710935508401375085010940100180425083017210115500401
  | 4, 0 => 0x1190104130100000254c4202000000000000300000324c82000000045480200001153548030000190204803010004145440301000005110d203001182048030100000504c420200000254c4202001140208130100000324c8200000004508120000115324c8300000d94210930100000454c4202001011550030100000000c9106001814110530100000255002040010935508301000004548020000000325092040018042508301460d82048040000000000000030010935508301000004250820100000255002042051515480400
  | 4, 1 => 0x454c82000000015500204000003548020000000000c910600109355083010018840500301001085010930100000000000030001842508301001142008130100000254c420200000000000030010935508301001182048030100000155002040010935508301000001550020400000454c420200109355083010000025500204001182048030100000000c910600115154803000000050109200001055050430100000254c42020009840500301
  | 5, 0 => 0x4250820100000450812000000000000005000003550820100000000000020000000105104000000000000500000324c820000000000c91040000000000005001182048030100000000c9106000001548020100000000c1102000005010920100000000c1104000d82048030000000415042010000000000003000000000000200000001051040000045081201000000000000100000000c11020000000000006000000010910400194314c130000188434c930000000000801000000020480201000004050020100000000c9106
  | 5, 1 => 0x15500201000000010d1020000000000002000c9454c8300000001044020100000304c020000000000000030000000000002000c5504c4300000d91500a300000c1154c030000041354403000000035480201000000000000100105505043010000000105104000001550020400000454c420200000000000050000000000001000002048020100109355083010000045408201000000010d102000000208120100000000c410200194324c130000000000c110200000000c1102000000000000600000355082010000000000003
  | 5, 2 => 0x15500201000000000000300000000c11020000000000004000003548020100184434c5300000000000000500000000000040000035480201000000000000600000324c8200000000000000500144314c130000000000000010000000000001000001550020100000000000050000035508201000002148420100000450412010000000000006000004508120100000000801000000000000005000000000000200000254c4202000004548020000000000c9106000000010d103000c1154c0300000005050420100000454c8200
  | 5, 3 => 0x30000045081200000001550020100109355083010000035440200000000000000000115354803000000020480201000000000000500119320c5300000d81540a30000000000c11020004135440300000003548020100000000c1102000d952101300000d9500853000000000000005000000000000500000000000020000000000003000004548020100000000c11020000000000003000003548020100000540812010000000000005001093550830100000000c1102000000000000300000000000010000000000005
  | 5, 4 => 0x200000001051040008135480300000000000000600000324c8200000000000000500109355083010000000000005000004548020100000000000030000000000003000000000000500000000c810000000000c910400000000c1102000000000000300000000801000000000000003000000000000200000354802000000000000005000002148420100000000000050000000000001000000000000200000454c420200041354403000000000000005000d820480300000000000000100000001051040000000000003
  | 5, 5 => 0x15500204000c5504c43000010d154c030000000000c110200000000c11020000000000002000003548020100000214842000000000000005000000000000400000000c1102000000010d102000000000000600000000000050000000000005000000010810100000354082010000000000001000000000000600000000000020000000000001001153548030000000000801010011935002300000002504120100194324c1300000004110520100000405002010000000000003000000000000500000254c42020000020480201
  | 5, 6 => 0x4508120100000104402010000041105201000001548020000000000801000000000000005000000000000300000000c910400000000c1102000000000000100000000c91060000000000005000000000000500000000c11040000025101201000004050020100000000c11020010d154c0300000c5504c4300000003504120000000001051040000045440201000d925040300000000000000600115154803000000000000005001093550830100000204802010000035508201000004250820100000000000050000000000001
  | 5, 7 => 0x250412010000045081201000000000000300000154802010008145480300000002048020100000000000050000010440201000d9500853000011515480300000000010010400000000c110200184434c530000000001091040000035508201000000000000200000001001040000042508201000004548020000144314c1300000d825406300000005010920100000454402010000025041201000000008010000000454c420200000000c910400000450812010008115480300000000000000500000000000010000020480200
  | 5, 8 => 0x320c52000000000000005000002504120000000450412010000045081201000813548030000000254c420200000000000060000000000004000000000000600000000000060000000000005000d51548030000000000000030000045081201000004544020100000000000010000000000003000000000000500000000c1102000004548020000000000000020000020081201000005010920000000501092000000000000003000000000000100000000000050000000000004000003548020100000254c42020000000000005
  | 5, 9 => 0xc1154c030000000000c410200000000000050000000000005000004540420100000000c1102000001044020100000204802000000000000005000004504120100000000c1102000c9454c830000180324c130000000000000030000000109104000003548020100000454c8200000003550820100000000c910600000000c1102000000000000500000454c4202000002148420100000000000050000000000001000000010d1020000000000006000000008010100000000000020000001041201000003548020000000324c8200
  | 5, 10 => 0x20000000000003000000000000500000450412010000000000004000d905881300000000000000300181210803000000000000005000003508120000000000c9106000000010d1030000005109201000003548020100180314c1300000002550020400000324c820000000000c110200000214842010000000100104000002048020000000000c11020000000000005000000000000500148324c1300000000000000600000000c1102000000000000500000214842010000000000005000000000000500000000c8100
  | 5, 11 => 0x324c820000000000000010000000000003000003548020100000000000050000000109104000413544030000180324c130000000000c110200000421092010000035480201000004540420100000000000050000000000004000004548020100000000c11020000020480200000000000000600000154802000000000000001000000000000600000000c110200000314c420000000000000020000000000000000000000000500000454c8200000d8204803000000000000005000811548030000000504c42020000015500201
  | 5, 12 => 0xd515480300000005108120000000000c41020000000000003000000000000300000000c110400000000c110400000000000030000045480201001011550030100000000c110200000350812000000050504201000000000000200000000000060000000000006000d951101300000004508120000000000c91060000025041201000000000000500000000000030000000000005000000000000100000000c110200119320c5300000000000000100000521012010000045480200000000000000400000000c81000000000000005
  | 5, 13 => 0x180324c13000000015480201001143508130000058058803000000000000003000000000000600000415042010000000000003000000010d1020000045480201000000010d1030010d154c0300000000000000600000000000060000040500201000000000000100000250412010000000000003000002048020100000454802000008115480300000000000000500000000c1102000000000000400000000000050004135440300000000000000500000000000030000000000005000000000000500118204803000000000000005
  | 5, 14 => 0x10d10200000000000010010935508301000004150420100000000c110200000000c1104000002048020100000000c11020004135440300000002048020100000000000050000045480200000000000000500000000000030000051081200000003550820100148324c13000000045081201000000000000500000000000020000025041201000000000000500000000c1102000000010d1020000000000006000000000000500188434c930000000000000050000000000002000000000000500000000000030008145480300
  | 5, 15 => 0x354802000000000000005000c1154c0300000003550820100000425082010000000000005000000000000100000000c110200000154c0200000d95210130000000000000010000045480200000000000000200041454403010000000000001000000000000300000154802010000000000006000000000000600041454403010000000000005
  | 6, 0 => 0xc11020000010440200000000000000100000250412000000045480200000000000000100000000000010000000000005000000000000200000000000060000000000002000000000000300000000000030000000000005000000000000200000454c82000000000080100000001500a2000000035440200000000000000500000000000040000000000004000000000000100000324c8200000000000000600000000000040000021484200000000000000100000000000050000000100101000000000000300000504c4200
  | 6, 1 => 0x121010000035081200000002504120100000500c520000000250412010000010440200000000000000500000250412000000052101200000000008010000000000000000000035480200000000000000400000354802000000000000002000000000000200000000c11000000000000002000004548020000000510c1200000000380a2000000000000003000000000000200000000000020000035041200000000000000200000000c410200000000000040000000000006000000000000100000450412010000015480200
  | 6, 2 => 0x10000000000003000002048020000000000000020000000000002000003508120000000510c120000000000000050000045480200000000000a10000000000c1102000000010910100000000000040000000000006000000000000500000000021000000000105104000000000000400000000000060000000000005000000000000300000000000000000000000003000000010510100000000c91000000025002200000000000000100000000000020000000000001000000010810100000058c12000000000000005
  | 6, 3 => 0x35402200000000010010100000000000020000021484200000000000000400000000121010000035480200000000000a101000002504120000000000000000000045402200000001044020000000000000050000000000002000000000000000000000000060000000000002000005110d200000000000000300000254022000000000000002000003540a20000000000c81000000020480201000000000a101000000500e200000004548020100000000000050000000000005000000010910400000000801000000000000001
  | 6, 4 => 0x600000354802000000045480200000002048020100000434c9200000000000000400000204802000000000000003000004544020100000000000010000015480200000000000000400000511092000000000000005000003544020000000000021010000000012101000000000000000000000000030000000000006000000000000000000000000010000000000002000000000a10000000354802010000000000005000000000000200000000000050000000000003000000000000100000354802000000000000003
  | 6, 5 => 0x300000000c0100000000000000200000000000060000000000002000000010d1020000035406200000001540a200000000380620000000000c110200000000000010000000000006000000010010100000000000030000000081101000000000610000000350022000000000000000000000000000300000000000040000000000005000000000000200000154c020000000000000030000002806200000001044020000000454402010000000000005000002500e200000002540220000000521012010000015480200
  | 6, 6 => 0x4150420100000000000060000000000003000002504120000000320c52000000021484200000000000000100000000000030000000000005000002148420100000000000020000045081201000000000a1010000000000004000000000000200000000000020000000000002000000010010400000000000030000045480200000003508120000000000000020000000000002000000000000600000000000030000000000001000000000000400000000000050000045440201000000000000400000000000050000000000003
  | 6, 7 => 0x100000000000030000000000000000000000000200000000000050000000105101000000000000600000304c020000000314c1200000002048020000000000000050000020480201000000008010100000434c020000000000000040000000000005000003548020000000000000030000000000001000000000000000000000000030000000000004000000000000600000000000010000000000002000005110d200000004050020100000000000020000000000006000000000000200000000000050000025040200
  | 6, 8 => 0x1044020100000000000030000025041201000000000000400000154c0200000001044020000000314c42000000000002101000000000000400000048022000000000105101000000000000400000000000000000000000001000000000000500000454c8200000000008110100000154c02000000000000003000000000000300000314c420000000000000050000050085200000000010910000000000000060000000002101000003504120000000354402000000000000003000001044020000000000000060000000000001
  | 6, 9 => 0x40500201000000540a20000000454802010000000109100000002148420000000000000030000000000003000000000000200000000000030000000000005000000588420000000000000000000000000005000000000000300000000000040000000000001000001044020100000000c110200000154802000000000000002000000010410100000000000010000000081101000003548020000000000000000000025041200000000000000500000354402000000045440201000004050020100000324c82000000035081200
  | 6, 10 => 0x2048020000000324c8200000002148420100000000000050000000000003000000000000200000304c0200000000000000200000058802000000021484200000000000000000000000000050000010440201000000000000500000000021010000000000003000000000610100000001091010000000000003000000000610100000000000020000000000003000003548020000000434c520000000000c11020000000000005000005048420000000304c0200000005210d200000000000000200000000000050000000000005
  | 6, 11 => 0x40000015480201000000000000500000000000050000000002101000000000000100000000000020000000000003000000008010100000454c82000000015480200000000000000300000000000040000045480200000001548020000000000841010000000000006000003508120000000000000060000045081201000000000000100000520c520000000000000040000000000001000000380a200000000000000400000000000000000000000001000000000000300000520c1200000000010810100000324c4200
  | 6, 12 => 0x30000000085101000004504120100000058c120000000155002010000005406200000002148420100000350412000000035508201000000000000000000154c0200000003544020000000154802000000042508201000000000000300000324c8200000000010810100000500c92000000000000003000000000000500000254c420000000000000030000000081101000000000000200000000000020000035440200000000000a10100000214842000000000000002000000000000300000314c42000000000000002
  | 6, 13 => 0x1091040000015002200000000000000600000000000000000045480200000000000000500000000000030000000000003000000000000200000250412000000000085101000000000000100000058812000000000000003000000000000300000154c020000000000000000000000006101000000000000200000000000040000000000001000000010110100000000401010000000000003000000000000300000000c810000000000000030000000000004000000000000400000000000020000000000002
  | 6, 14 => 0x3548120000000000000020000000000001000000000000200000314c420000000000000050000000000004000000010110000000000000060000000000002000000000000600000000811010000052105200000000000000300000521052000000000000006000000000000200000454c820000000028062000000035480200000000010810100000000000050000035081200000003504120000000501092000000010440201000000000000300000434c920000000304c020000000324c820000000001091010000000000001
  | 6, 15 => 0xc510000000000000060000000000000000002148420100000000c41000000000000005000000500a20000000000000010000000080101000000000000500000000841010000035480201000000000000500000000481010000000000003000000000000400000000801000000000000002000001548020000000104402010000000000006000003548020000000048022000000000000002000005210d200000000000a101000000000000500000000000030000045406200000000000000300000000000010000003806200
  | 6, 16 => 0xe1000000015480200000000010410100000324c8200000003540a200000000000000500000000000020000000000004000002148420000000314c12000000020480201000000000000000000000000060000000048101000000584020000000304c0200000000000610100000511092000000000000005000000000000000000354842000000000000006000002504120000000000c1102000004050020100000000801010000000000004000000010510000000354812000000000000002000000000000500000000c1102
  | 6, 17 => 0x40000000012100000000000000600000154802010000000000004000000010110100000000c11020000045081201000005108120000000000021010000000000001000000000210100000314c42000000035041200000004504120100000350412000000000000005000003548020000000354842000000000109101000000000000000000324c82000000041504201000000010110100000000000030000000000006000000010010100000354802010000010440200000005210120000000000000050000000000003
  | 6, 18 => 0x254062000000000000005000000000a101000002148420000000000000060000000000006000000000000300000000000050000000000003000000010d1000000000000005000003540620000000000000050000000000003000002500e20000000350412000000000109101000000000a1000000045480200000004548020000000000000060000000000005000002048020000000000000040000000041101000000010810100000154802000000000000003000000000000600000000000030000000000003
  | 6, 19 => 0x6101000000000000500000001091040000000000001000000000000400000204802000000000000002000000010910100000000000060000000000001000002500e20000000324c820000000354402000000000000005000000000000500000000121000000000000003000000000000200000324c420000000355082010000000000004000000000000500000000000050000000000000000004250820100000000c110200000000000020000000000002000000000000300000000000020000000080101000000000e100
  | 6, 20 => 0x454c820000000000000040000015480200000000010d102000000000000200000000000050000000000005000000000000300000000000020000000000003000000000000400000058812000000000000003000000000000500000250412010000000000005000000000000400000000c110200000000000040000000000002000003504120000000000000040000000000005000000000000200000250412000000000000003000003548020100000000000010000000000003000000000000500000454c82000000000000004
  | 6, 21 => 0x40000000000003000000000000400000314c42000000000100101000000000000100000000c11020000000000002000000000000300000454802010000000000005000000000000400000000000050000000000000000000000000100000000401010000000000001000000000000300000154c02000000000081100000000000000200000000000020000000000004000003508120000000354802000000035480200000000004110100000000000020000050109200000000000000300000450412010000000000005
  | 6, 22 => 0x600000000841010000000000002000000000000300000204802000000000000003000000000000100000000000030000035480200000000000000400000314c42000000000000005000000000000500000000000050000000006100000000000000500000000000020000020480200000000000000200000314c42000000045480200000000000000000000000000030000025041201000000000000500000000000020000000000002000001548020000000000c410200000154c020000000000000060000000105104
  | 6, 23 => 0x300000204802000000000000001000000010510100000000c81000000000000005000000000000300000000021000000035440200000000010410100000304c020000000000000030000000000000000003500a200000000000000100000000021000000045480200000000000000200000000000040000000081100000000000000600000504842000000045480201000000010010100000000000060000000000003000003540220000000000000030000000008101000000004110100000000000050000000000003
  | 6, 24 => 0x401000000050484200000000000a100000000000000100000324c42000000000000001000000480a20000000000000000000000000002000000000000300000314c42000000000000001000000000000200000154c020000000000000040000000000001000000000000300000000000020000000000002000000000000200000000000020000050105200000001044020000000254c0200000000000000500000250412000000000000003000000000000200000000c8100000000000000500000314c120000000324c8200
  | 6, 25 => 0x504c82000000035081200000001044020000000000000020000035508201000000000000500000000000060000035081200000000000000200000304c02000000000000005000002504120000000000c110200000250412010000000000005000000008510000000000000030000000000003000000480e2000000035440200000000000000400000000021000000000000005000000000000300000000000040000000041101000001548020000000000000030000035440200000000000000100000000000060000000012101
  | 6, 26 => 0x10410100000000811000000000000001000000000000300000000000000000000012101000000000410100000000000010000015002200000001500e200000000000000600000324c8200000000000000500000000000000000000000006000000000a1000000025041200000003548020000000454802010000020480200000000000000500000520c520000000504c420000000000000020000000000000000003548420000000000000020000000000001000000000000200000154c02000000021484200
  | 6, 27 => 0x12101000000000000500000000000050000000000005000000000000500000000000020000000000003000000584020000000254022000000000000005000004050020100000354402000000000000006000003504120000000304c0200000000000000500000434c9200000000000000200000324c1200000000008410000000154c0200000003540620000000254062000000000000002000000000000400000454c820000000154022000000000000003000000000000300000350812000000000105101000001500a200
  | 6, 28 => 0x3548020100000000000040000000000003000002148420100000154802010000000000003000005010920100000000000060000050109200000003548020100000154802000000015480200000000000000100000000000040000000000004000000000000000000000000040000000000005000000000000300000000000010000041504201000000000a1010000004806200000000000000300000314c42000000025041200000000000000600000324c82000000010440200000004250820100000454c82000000000000001
  | 6, 29 => 0x100000000000050000000000006000000000000000000320c52000000000000004000000000000400000000121010000000006101000000000000200000314c4200000002148420000000154c020000000000000030000000000002000003540a200000000000000600000000401010000000000005000001550020100000000c81000000000000001000000000a1010000051109200000005110d2000000000000000000000000000300000354802000000000000003000000000000100000000000010000000000002
  | 6, 30 => 0x4508120000000000000000000000000005000000000000300000000000000000000100101000000480a2000000000000003000000000000100000254c420000000355082010000000000004000000000000500000434c020000000254c02000000025440200000004250820100000154802010000035081200000000000000400000001051010000052101200000000000000600000000000030000000000005000000008010000000324c820000000000000020000000000002000000000000200000001041010000000000003
  | 6, 31 => 0x8101000002048020000000104402000000035508201000000000000200000000000060000000000002000000000000100000000c110000000500c92000000000000001000000000000200000000000060000000080101000000000000300000000000020000000000002000002540620000000000c4102000000001210100000000000050000000000001000003504120000000000000060000000000005000000480e200000000000000400000000000060000000000003000000000210100000000000060000000000002
  | 6, 32 => 0x454802000000000006101000004150420100000000000040000000000004000000000000100000000000010000035041200000000000000600000454c8200000000000a101000000000000200000000000020000000000005000000008510100000000c910000000000000000000000000006000000000000200000000000000000000000002000000000000300000000000050000000000005000000008110100000000000040000000040101000000000000500000304c0200000004050020100000000000030000000000003
  | 6, 33 => 0x801000000000000005000000000000600000000000050000000000002000005050420100000000000030000000000004000000000000300000415042010000000000003000000000000600000500c520000000000000020000021484200000000000000100000154c02000000000000005000001548020100000324c12000000000000002000000000000100000324c820000000058c920000000000121010000000000003000000000000200000000000020000000000005000000000000400000000000020000000000000
  | 6, 34 => 0x304c02000000000000004000002504120000000324c8200000000000000200000425082010000000101100000002504120000000454c82000000000000002000000000000300000304c0200000000008410100000520c1200000000000000200000000000020000000108101000000000000300000500c52000000045480201000003548020000000000000020000000000002000000000000500000000000050000004806200000000000000200000000000020000000002101000002048020000000000021010000000000002
  | 6, 35 => 0x4548020100000254c02000000020480200000000000000600000028022000000000000002000003548020000000314c4200000000000000100000000851010000000104101000000000000300000000000030000000000003000000000000600000154c02000000035440200000000000a10100000204802010000000040101000000000000300000000000030000020480200000000000000600000000000060000000000002000000000000500000350812000000000000005000003550820100000000000060000015002200
  | 6, 36 => 0x20480200000000000000200000000000010000000000005000000010d1020000000081101000000000000500000210802000000045440201000005010d20000000510c9200000000000000100000000000030000000004101000000000000100000304c0200000000380220000000000000020000000000003000000010110000000000000010000000000005000000010510400000000000030000000000000000000000610100000154802000000000000002000000000000400000154c020000000000811010000000000006
  | 6, 37 => 0x80101000000008410100000434c52000000000000005000000000000600000250022000000010440200000000000000100000324c8200000004508120000000000000020000000000003000000000210100000000000020000000002101000000000000100000324c820000000000000030000035081200000000000000400000000000020000000000003000003544020000000000000040000000000006000000000000100000254c02000000000000006000004540a200000000000e10000000000000030000045480200
  | 6, 38 => 0x10810100000000000030000035480200000000000000200000000000020000025041200000000000e10000000000000010000042508201000000004010100000000000030000000000001000000000000500000000081010000050085200000000010d1000000045081201000000000210100000000801010000045480200000005010d200000000000a1000000000109104000000010910000000510812000000035440200000000000000300000001091040000020480201000000000000400000000000040000000002101
  | 6, 39 => 0xa10000000104402000000051101200000000000000200000354802000000035480200000000000a1010000000000000000002048020000000000000020000000000006000000180220000000000000060000000080100000000010d10200000000000030000000000000000002504120000000000000030000000081101000000000000200000000000060000000000004000000000a10100000000000030000000101101000000008510100000000000020000000000001000000000000300000250402000000000000002
  | 6, 40 => 0x84101000002540220000000000c4102000000000000200000000000040000000000003000000000e10000000155002010000000000002000000000000200000000000020000025041200000001500e2000000000000002000000000000300000000000030000035081200000003540220000000324c120000000154c0200000000000000400000000000020000000000002000000000000600000000000030000000000002000000000000300000001091010000035081200000000000000300000250022000000000000005
  | 6, 41 => 0x50000000000006000000000000300000001001040000000000002000000008410100000354802000000020480200000000000000500000000000030000000000005000000000000000000000000020000045081201000000000000300000354022000000000002101000000008010100000504c82000000000080100000000000000600000000000040000035440200000001044020000000000811010000000000003000000000000200000454802000000000000005000000000000500000000401010000000000004
  | 6, 42 => 0x314c4200000002148420000000001051040000000000001000001044020000000000000040000000000003000000000a101000000010110100000454c82000000020480200000000000000300000254402000000000000003000000000000000000000000030000005406200000002048020100000000000030000000000003000000000000500000000000030000000000004000001550020100000304c02000000051081200000001548020100000154802000000000000003000001044020000000000000060000021484200
  | 6, 43 => 0x500000000000010000035440200000000500a2000000000000002000000000000300000000811010000000000001000000000000400000304c0200000002544020000000000021000000045440201000000010910100000000000020000000000003000000010010100000000000000000015480200000000010810100000000000010000035041200000000000000200000500c9200000000000000300000000c4102000004544020100000350812000000000000001000002504120000000000000060000000000002
  | 6, 44 => 0x324c820000000454c820000000434c5200000000008010100000000000010000045041201000000000000300000000000020000021484200000000000000000000000000020000000000001000000000000000000000000050000000000003000005110120000000000000060000045480200000000000000600000000000000000000000002000000000000300000500c9200000003548020000000000000060000000000005000000588020000000000000050000000006101000000000000500000000c81000000000000003
  | 6, 45 => 0x35041200000000010110100000000000010000000104101000000000000300000304c02000000000000006000000380220000000104402000000000000004000002108020000000350812000000005880200000000000000300000000000030000000000002000000000000600000000000050000000000002000004508120100000320c520000000028022000000000000002000000008010100000500852000000000000002000001550020100000510c920000000000021000000000000003000000000000500000500c9200
  | 6, 46 => 0x354802010000000012100000000000a1010000000104101000001548020000000000000040000000000002000003548020000000000000050000035440200000000000000400000354402000000050105200000000010910100000304c0200000000000000300000314c42000000000100101000000000000200000454c820000000000000050000020480200000000000000400000000000020000045480200000000010d102000000000000400000000000020000000000005000000000000600000000000020000000000000
  | 6, 47 => 0x60000000000001000000000000300000000000030000000108101000001044020000000000000040000000000003000000000000200000154c020000000000000030000000000002000000000000300000454c820000000000000060000010440201000000001210100000520c1200000000000000200000000000030000000000002000000500e20000000354402000000005884200000000000000100000000000020000000000006000004508120000000304c0200000000540a2000000021484200
  | 6, 48 => 0x30000021484201000000000000200000058c920000000000000030000000000003000000000a1010000000000006000000000000500000000000040000000004101000003544020000000204802000000000000002000000000000200000018022000000035041200000004548020000000000000060000000000002000000000000500000000c8100000000000000600000324c820000000254c420000000000000020000000000002000000004110100000354402000000000000004000000000000600000504c4200
  | 6, 49 => 0x2000000000000200000000c110200000000c11020000000000002000002148420000000000121010000000000001
  | 7, 0 => 0x84100000000000000400000001011000000000002100000000004110100000001011000000000006100000000000610100000000411000000000000001000000000e1000000000000005000000000210000000000000030000000000002000000000000600000000c4100000000000000200000000c510000000000000020000000000003000000000000000000000841010000000105100000000000a100000000000a1010000000000001000000000000100000000c410000000000c5100000000008110000000000c4100
  | 7, 1 => 0x20000000105100000000000210100000001081010000000012100000000000a1000000000105100000000000e1000000000000002000000004110100000000c51000000000101101000000000a100000000010d10000000000c4100000000000000200000000851000000000000001000000000a1000000000080100000000000000200000000c81000000000006100000000004010000000001091000000000000000000000000610100000000c8100000000000210000000000c51000000000000001
  | 7, 2 => 0x8510000000000000030000000080100000000000000300000000000000000000085101000000010110100000000000030000000084100000000000610000000000401000000000000001000000000e10000000000c9100000000004010100000000000040000000080100000000000610000000000000000000000000003000000008010000000000000030000000000002000000000a1000000000000004000000000e100000000000000400000000c11000000000080101000000000210000000000000040000000000001
  | 7, 3 => 0x30000000081100000000010410100000000c510000000000000030000000000003000000000000300000000c41000000000000001000000000000300000000c110000000000c910000000000061000000000041100000000000000300000000411010000000000003000000000000100000000000010000000000003000000000e100000000000000100000001091010000000101100000000000000300000000c5100000000010d10000000000851000000000000002000000000a10000000000841000000000006100
  | 7, 4 => 0x40100000000000000300000000000010000000000003000000010510100000000c5100000000000e100000000010410100000000000040000000000006000000000000200000000801000000000012101000000000a100000000000e100000000000000200000000c010000000000000020000000002100000000004110100000000000010000000084100000000000000000000000c910000000000000010000000012100000000000000200000000000020000000084101000000010510000000001051010000000000002
  | 7, 5 => 0xe10000000000000040000000040100000000000a1000000000012101000000000000000000000c010000000000000030000000000001000000000e1000000000100101000000001210100000000000010000000080100000000010d1000000000012101000000010d100000000000a101000000010910000000000c110000000000c8100000000000a1000000000085100000000000000300000000411000000000006100000000001210000000001001010000000000003000000001210000000000021000000000000001
  | 7, 6 => 0xc11000000000101101000000001210100000000c5100000000010510100000000000020000000000001000000004010000000000c4100000000010410100000000121010000000006100000000008410000000000061000000000012100000000008110000000000000010000000081100000000000a1010000000000005000000000000300000000801000000000101100000000000000100000000c910000000000c01000000000000002000000008010100000000021000000000000001000000010910000000000c9100
  | 7, 7 => 0x200000000c010000000000c81000000000006101000000010910000000000000010000000006100000000000000300000000000010000000000002000000000000000000000c9100000000000e1000000000012101000000000210000000000000020000000109101000000000000200000001051010000000081100000000000610100000000000020000000000002000000000a1010000000002100000000008510000000000c110000000001051000000000000001000000000000200000000000030000000000003
  | 7, 8 => 0x4000000000210000000000000060000000012100000000000000300000001051000000000081100000000000000400000000c81000000000006101000000000e100000000001210100000000c51000000000080100000000000210100000000c4100000000010d10000000000000010000000002100000000000210000000000000030000000084100000000000a100000000000a1010000000000001000000000a100000000008410100000000000030000000012100000000000000600000000000040000000101100
  | 7, 9 => 0x50000000040101000000000a1000000000000002000000000610000000000c9100000000000000400000000000040000000002100000000000e1000000000000002000000000000400000000851010000000000002000000004110000000000401010000000109100000000000000400000000c010000000000021010000000000000000000008510000000000c110000000001001010000000040101000000000e1000000000000004000000000a1000000000040100000000000000200000000061000000000000002
  | 7, 10 => 0x3000000000000300000000121000000000000002000000000210100000000c110000000000c91000000000109100000000000000200000000841010000000000004000000000000100000000000020000000084100000000000a100000000000000200000000000050000000000002000000000610000000000061010000000000002000000000e1000000000085101000000000000100000000841000000000000001000000008010000000000000000000000000001000000010d10000000000c81000000000000002
  | 7, 11 => 0x610000000000000060000000085100000000008510100000000811000000000000003000000000000200000001011000000000000001000000000000200000000000050000000040100000000004010100000000000050000000000003000000004110000000000c0100000000000000200000000000040000000000001000000008410100000000c91000000000012100000000000000200000000000030000000006100000000008410000000000000020000000002100000000000210100000000000030000000006100
  | 7, 12 => 0x10000000002100000000000000200000000121000000000000001000000000000300000000021000000000000004000000000000300000000c0100000000000000300000001051000000000000004000000000000200000000000030000000085100000000008010100000000c510000000000411000000000000004000000000000300000000c4100000000008010000000000000040000000000002000000010910100000000000050000000000002000000000e100000000000000100000000000010000000000003
  | 7, 13 => 0x81101000000000000200000000000050000000041100000000000a10000000000000020000000000000000000000000400000001091010000000085100000000000000100000000c810000000000c910000000000000020000000000002000000004010000000000000020000000081100000000000e100000000000210000000000801010000000081100000000008410000000000841010000000101101000000000000300000000c010000000000c11000000000000003000000000e10000000000000030000000109100
  | 7, 14 => 0x200000000801000000000080101000000000a100000000000a1010000000002101000000010110000000000841000000000000004000000010510000000000000030000000081100000000000000200000000c5100000000000000200000000c410000000000c810000000001091000000000000005000000010910100000000121000000000000002000000000210000000000c010000000000000010000000000002000000000e1000000000105100000000010110000000000000020000000101101000000010d100
  | 7, 15 => 0x50000000000004000000000610000000000000030000000002100000000000000200000000c110000000001011010000000105100000000000a101000000000000100000000061000000000105100000000000000200000000000010000000000002000000000000200000000c51000000000081101000000010010100000000c41000000000000003000000000000200000000c010000000000c9100000000000e100000000010810100000000000020000000000003000000000000200000000000010000000000003
  | 7, 16 => 0x10d1000000000000002000000000000600000000c51000000000000001000000000a100000000000000200000000c4100000000010910000000000000020000000080100000000000000200000000021000000000000003000000000a100000000008110000000000000040000000006101000000000e100000000010110000000000c91000000000109101000000000000000000001001010000000000003000000010d100000000000e10000000000c81000000000000004000000000a10000000000000050000000006100
  | 7, 17 => 0x1000000010d10000000000000020000000041100000000000a100000000000a1000000000006100000000001210000000000c01000000000100101000000000000400000000c9100000000008110000000000c8100000000008110100000000000010000000085100000000000e100000000000210000000000c11000000000000001000000000a10000000000c1100000000004010000000000061000000000041100000000000e10000000000000020000000101100000000000000200000000000020000000105100
  | 7, 18 => 0x40100000000000a1010000000000001000000010910000000000000010000000000006000000008510100000000000030000000000002000000000000300000000c810000000000000020000000000005000000010810100000000411010000000000000000000000610000000000000030000000041100000000010d1000000000006100000000000210000000000021000000000000001000000000000000000000841000000000002101000000000000000000000000020000000000002000000000e1000000000000002
  | 7, 19 => 0x3000000008510000000000801000000000041100000000000000300000000000020000000006100000000004010000000000061000000000104101000000000000100000000000040000000006101000000000000600000000811000000000000003000000004110000000000000060000000000003000000000000100000000801010000000085100000000010910000000000021000000000000000000000000000400000000c01000000000000003000000000a100000000000000300000000000030000000000002
  | 7, 20 => 0x200000000c91000000000040100000000000610000000000000030000000081100000000000000300000001051000000000041100000000000000100000000c510000000000c81000000000000006000000000000400000000c410000000000c110000000000c510000000000c010000000001091000000000002100000000000210000000000000010000000080100000000000000300000000841000000000000000000000000000600000000000040000000000005000000010110000000000000030000000000002
  | 7, 21 => 0x41100000000010d10000000000c4100000000000000300000000411010000000080100000000000a10000000000121010000000000004000000000210000000000000030000000000001000000000610000000001011000000000000001000000000000000000000000030000000000001000000000000100000001051010000000104101000000000e100000000000000200000000851000000000000002000000010d100000000000a10000000000841000000000012100000000000000400000000000030000000000003
  | 7, 22 => 0xc11000000000101100000000000000400000000c91000000000000000000000008110100000000c81000000000000002000000000000300000000811000000000012101000000000000100000000801000000000000001000000000e10000000000c010000000000c1100000000000a1010000000000002000000000a1000000000000003000000010910000000000c910000000000000010000000084100000000000000300000000000040000000105100000000000e100000000000000200000000c510000000000c8100
  | 7, 23 => 0x1081010000000000002000000000e10000000000c81000000000041100000000000a100000000000000500000000801000000000000004000000000000100000000000050000000002101000000010910000000000000010000000006100000000000a100000000000210000000000c91000000000105100000000008110100000000851000000000000006000000000e10000000000c510000000000411000000000000001000000001210000000000c4100000000010d10000000000c1100000000000a1000000000006100
  | 7, 24 => 0x50000000002101000000000e1000000000006100000000004010000000000c910000000000000000000000105100000000010d1000000000108101000000000000100000000c5100000000000a100000000000000000000000c41000000000006101000000010510100000000000020000000041100000000010410100000000c0100000000000210100000000c1100000000000a1010000000002100000000000a100000000000610100000000000030000000000002000000010110000000000021000000000000001
  | 7, 25 => 0x10000000002101000000004010000000000000000000000000002000000000a10100000000000020000000109100000000008510100000000061010000000000004000000000210000000000000010000000000000000000000000600000000000010000000000002000000004010100000000c4100000000004110000000000c0100000000000e100000000000000600000000811000000000081101000000000a101000000008510000000000000030000000012101000000000610000000000061010000000000003
  | 7, 26 => 0x300000001011000000000006100000000000000100000000851000000000109100000000000000200000000c010000000000c81000000000108101000000000000100000000000030000000040100000000000000300000000841000000000000004000000000e1000000000101100000000004010000000000021000000000000001000000000210100000000121010000000085100000000010d1000000000000001000000000a100
  | 8, 0 => 0x10000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000001000000000000100000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_5 roots_5 8 s ws hint
  | 1 => checkCutEntry dom_6 roots_6 7 s ws hint
  | 2 => checkCutEntry dom_7 roots_7 6 s ws hint
  | 3 => checkCutEntry dom_9 roots_9 6 s ws hint
  | 4 => checkCutEntry dom_10 roots_10 6 s ws hint
  | 5 => checkCutEntry dom_12 roots_12 5 s ws hint
  | 6 => checkCutEntry dom_13 roots_13 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_14 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_14 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
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
theorem z2_0 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 2 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 8 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_8 : ∀ i, 8 ≤ i → i < 10 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 8 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 10 → Z 3 i = true := range_split z3_0 (z3_8)
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
theorem z4_48 : ∀ i, 48 ≤ i → i < 55 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 48 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 55 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (z4_48))))))
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
theorem z5_224 : ∀ i, 224 ≤ i → i < 228 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 224 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 228 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (range_split z5_200 (range_split z5_208 (range_split z5_216 (z5_224))))))))))))))))))))))))))))
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
theorem z6 : ∀ i, 0 ≤ i → i < 592 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (range_split z6_376 (range_split z6_384 (range_split z6_392 (range_split z6_400 (range_split z6_408 (range_split z6_416 (range_split z6_424 (range_split z6_432 (range_split z6_440 (range_split z6_448 (range_split z6_456 (range_split z6_464 (range_split z6_472 (range_split z6_480 (range_split z6_488 (range_split z6_496 (range_split z6_504 (range_split z6_512 (range_split z6_520 (range_split z6_528 (range_split z6_536 (range_split z6_544 (range_split z6_552 (range_split z6_560 (range_split z6_568 (range_split z6_576 (z6_584)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z7_360 : ∀ i, 360 ≤ i → i < 361 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 360 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 361 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (range_split z7_208 (range_split z7_216 (range_split z7_224 (range_split z7_232 (range_split z7_240 (range_split z7_248 (range_split z7_256 (range_split z7_264 (range_split z7_272 (range_split z7_280 (range_split z7_288 (range_split z7_296 (range_split z7_304 (range_split z7_312 (range_split z7_320 (range_split z7_328 (range_split z7_336 (range_split z7_344 (range_split z7_352 (z7_360)))))))))))))))))))))))))))))))))))))))))))))
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
  scr dom_14 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_14 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_14 roots_14 goal_14 10 := by
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

theorem low_14 : Lower dom_14 roots_14 goal_14 10 := S_14.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_14_bits : ∀ r : Fin 64, roots_14.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_14_lt : ∀ r : Fin 64, dom_14.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_14 T)
    (hlow : Lower dom_14 roots_14 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_14, Avail mask256 roots_14 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_14 hfan 0 roots_14 roots_14 rfl hsup0
  set out := (execN C.gates roots_14).getD C.output 0
  have hout : out &&& dom_14 = T &&& dom_14 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_14_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_14 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_14_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_14).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_14)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_14.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_14 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_14).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_14 &&& mask256 = dom_14 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_14 = T &&& dom_14 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_14, hd63, hout]
  have hnc_m : ¬ IsConst dom_14 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_14 roots_14 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_14, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_14 roots_14 0 roots_14 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4008373480 * 2 ^ 32 + 4007718048) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_14.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_14 10 hT6 (by unfold IsConst; decide) low_14

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.and, [7, 5]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.and, [12, 9]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.and, [6, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_15907_aux

theorem PEqualNP.Outside.L_meta_15907 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373480 * 2 ^ 32 + 4007718048) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373480 * 2 ^ 32 + 4007718048) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_15907_aux.wit, PEqualNP.Outside.L_meta_15907_aux.wmono, le_trans PEqualNP.Outside.L_meta_15907_aux.wsize (PEqualNP.Outside.L_meta_15907_aux.lower s hs), PEqualNP.Outside.L_meta_15907_aux.weval⟩
