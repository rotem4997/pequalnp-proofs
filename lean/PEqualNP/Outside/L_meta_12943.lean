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

namespace PEqualNP.Outside.L_meta_12943_aux

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

def dom_0 : Nat := 0x2200220022002200
def goal_0 : Nat := 0x2200200020000000
def roots_0 : List Nat := [0x2000200020002000, 0x2200000022000000, 0x2200220000000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(13, 29), (13, 45), (25, 29), (25, 57), (41, 45), (41, 57)]
def r1sG : List Nat := [13, 13, 25, 25, 41, 41]
def r2sG : List Nat := [29, 45, 29, 57, 45, 57]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xe2a6abe7
  | 3, 0 => 0xe2a6abe7
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x220022000000000022000000220000002000200020002000
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

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
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

def dom_1 : Nat := 0xa000a000a000a00
def goal_1 : Nat := 0xa00080008000000
def roots_1 : List Nat := [0x800080008000800, 0xa0000000a000000, 0xa000a0000000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0xaa000000aa00
def goal_2 : Nat := 0xa80000008000
def roots_2 : List Nat := [0x880000008800, 0xa0000000a000, 0xaa0000000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 4 :=
  lower_iso [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xaa00aa00
def goal_3 : Nat := 0xa8008000
def roots_3 : List Nat := [0x88008800, 0xa000a000, 0xaa000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 4 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0xaa00aa00aa00aa00
def goal_4 : Nat := 0xaa00a800a8008000
def roots_4 : List Nat := [0x8800880088008800, 0xa000a000a000a000, 0xaa000000aa000000, 0xaa00aa0000000000]

namespace S_4
def pairsG : List (Nat × Nat) := [(11, 15), (11, 27), (11, 43), (13, 15), (13, 29), (13, 45), (25, 27), (25, 29), (25, 57), (41, 43), (41, 45), (41, 57)]
def r1sG : List Nat := [11, 11, 11, 13, 13, 13, 25, 25, 25, 41, 41, 41]
def r2sG : List Nat := [15, 27, 43, 15, 29, 45, 27, 29, 57, 43, 45, 57]
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
  | 3, 0 => 0x2a806a9a
  | 4, 0 => 0x53c0c5294efaf868110320ee103f7be9
  | 5, 0 => 0x88299f88057fbb6d02c98a43
  | 6, 0 => 0x2c98a43
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaa008800aa008800aa000000aa000000a800a800a800a800a000a000a000a000880088008800880022002200220022000a000a000a000a000000000022002200
  | 0, 1 => 0xaa00aa00aa000000aa00aa00a800a800aa00aa00a000a000aa00aa0000000000aa00a000aa00a000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xca834
  | 4, 0, 0 => 0x96214964305c97435b96435
  | 5, 0, 0 => 0x96314965435096434
  | 6, 0, 0 => 0x96434
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1c71c003f038007ff8fc71f8
  | 0, 1 => 0xfc0e3fe38e001f8
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xbdf9d26ff4b924fdb0b46090
  | 0, 1 => 0xff6ffffbdf24dfb
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 13 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 13 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 13 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 13 then wireAt i else 0
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
  | 2, 0 => 0x22e34e9e
  | 3, 0 => 0x212a598707e54e6c06f5de2802c98a43
  | 4, 0 => 0x88299f8849db56441937123b1874445214e0e8550c413b0b057fbb6d02c98a43
  | 5, 0 => 0x187444520c413b0b
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x1
  | 3, 0 => 0x80000300000800000
  | 4, 0 => 0x4000010000080000300000c0000100000000000
  | 5, 0 => 0xc00001
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

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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

def dom_5 : Nat := 0x888800008888
def goal_5 : Nat := 0x888000008000
def roots_5 : List Nat := [0x808000008080, 0x880000008800, 0x888800000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_6 : Nat := 0xa0a00000a0a0
def goal_6 : Nat := 0xa08000008000
def roots_6 : List Nat := [0x808000008080, 0xa0000000a000, 0xa0a000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 4 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_7 : Nat := 0xaaaa00000000
def goal_7 : Nat := 0xa88000000000
def roots_7 : List Nat := [0x888800000000, 0xa0a000000000, 0xaa0000000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 4 :=
  lower_iso [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3

def dom_8 : Nat := 0xaaaa0000aaaa
def goal_8 : Nat := 0xa88000008000
def roots_8 : List Nat := [0x888800008888, 0xa0a00000a0a0, 0xaa000000aa00, 0xaaaa00000000]

namespace S_8
def pairsG : List (Nat × Nat) := [(7, 15), (7, 39), (11, 15), (11, 43), (13, 15), (13, 45), (35, 39), (35, 43), (37, 39), (37, 45), (41, 43), (41, 45)]
def r1sG : List Nat := [7, 7, 11, 11, 13, 13, 35, 35, 37, 37, 41, 41]
def r2sG : List Nat := [15, 39, 15, 43, 15, 45, 39, 43, 39, 45, 43, 45]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_8.map (· &&& dom_8)
def goalM : Nat := goal_8 &&& dom_8
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x186bc852
  | 4, 0 => 0x5e791b544b3685321893a8da0ac7e000
  | 5, 0 => 0x4cae1e633fdd614111ac9d39
  | 6, 0 => 0x3fdd6141
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x888800000000000088000000880000008800000000000000808000008080000022220000222200000a0a0000aaaa00000a0a00000a0a000000000000aaaa
  | 0, 1 => 0xaaaa000000000000aa000000aa000000a0a00000a0a00000a0a0000000000000a0000000a0000000888800008888
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xd9644
  | 4, 0, 0 => 0xdcb8550cb304cba875dcb825
  | 5, 0, 0 => 0xdc8140dcb84dcb875
  | 6, 0, 0 => 0xdcb84
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xc000c000003f30cffccc03f
  | 0, 1 => 0xfc0c3c3333000300cf
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x5ca49d488157a2049d488015
  | 0, 1 => 0xfeaebdb77b62a355df
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
  | 2, 0 => 0x1d730175
  | 3, 0 => 0x3fdd614133cb02e0201a0db50837f44e
  | 4, 0 => 0x4cae1e63468e6d833fdd614135d445ae241459fe222948df11ac9d390cd5254f
  | 5, 0 => 0x468e6d83222948df
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x1
  | 3, 0 => 0xc00000
  | 4, 0 => 0x400003000000000020000000000000000000002
  | 5, 0 => 0xc00000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_5 roots_5 4 s ws hint
  | 1 => checkCutEntry dom_6 roots_6 4 s ws hint
  | 2 => checkCutEntry dom_2 roots_2 4 s ws hint
  | 3 => checkCutEntry dom_7 roots_7 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
  scr dom_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_8 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_8 roots_8 goal_8 7 := by
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

theorem low_8 : Lower dom_8 roots_8 goal_8 7 := S_8.noCircuit

def dom_9 : Nat := 0xaaaaaaaa
def goal_9 : Nat := 0xa8808000
def roots_9 : List Nat := [0x88888888, 0xa0a0a0a0, 0xaa00aa00, 0xaaaa0000]

theorem low_9 : Lower dom_9 roots_9 goal_9 7 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0x2222222222222222
def goal_10 : Nat := 0x2200200020000000
def roots_10 : List Nat := [0x2020202020202020, 0x2200220022002200, 0x2222000022220000, 0x2222222200000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x2200220022002200, 21, 29)] (by decide +kernel) (by decide +kernel) low_0

def dom_11 : Nat := 0x8888888888888888
def goal_11 : Nat := 0x8880888088808000
def roots_11 : List Nat := [0x8080808080808080, 0x8800880088008800, 0x8888000088880000, 0x8888888800000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888000088880000, 7, 23)] (by decide +kernel) (by decide +kernel) low_5

def dom_12 : Nat := 0xa0a0a0a0a0a0a0a
def goal_12 : Nat := 0xa00080008000000
def roots_12 : List Nat := [0x808080808080808, 0xa000a000a000a00, 0xa0a00000a0a0000, 0xa0a0a0a00000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10

def dom_13 : Nat := 0xa0a0a0a0a0a0a0a0
def goal_13 : Nat := 0xa080a080a0808000
def roots_13 : List Nat := [0x8080808080808080, 0xa000a000a000a000, 0xa0a00000a0a00000, 0xa0a0a0a000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_14 : Nat := 0xaaaa0000
def goal_14 : Nat := 0xa8800000
def roots_14 : List Nat := [0x88880000, 0xa0a00000, 0xaa000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 4 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

def dom_15 : Nat := 0xaaaa0000aaaa0000
def goal_15 : Nat := 0xaa800000a8800000
def roots_15 : List Nat := [0x8888000088880000, 0xa0a00000a0a00000, 0xaa000000aa000000, 0xaaaa000000000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 25, 57)] (by decide +kernel) (by decide +kernel) low_14

def dom_16 : Nat := 0xaaaaaaaa00000000
def goal_16 : Nat := 0xaa80a88000000000
def roots_16 : List Nat := [0x8888888800000000, 0xa0a0a0a000000000, 0xaa00aa0000000000, 0xaaaa000000000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 5 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def dom_17 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_17 : Nat := 0xaa80a880a8808000
def roots_17 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]

namespace S_17
def pairsG : List (Nat × Nat) := [(7, 15), (7, 23), (7, 39), (11, 15), (11, 27), (11, 43), (13, 15), (13, 29), (13, 45), (19, 23), (19, 27), (21, 23), (21, 29), (25, 27), (25, 29), (25, 57), (35, 39), (35, 43), (37, 39), (37, 45), (41, 43), (41, 45), (41, 57), (49, 57), (51, 55), (51, 59), (53, 55), (53, 61)]
def r1sG : List Nat := [7, 7, 7, 11, 11, 11, 13, 13, 13, 19, 19, 21, 21, 25, 25, 25, 35, 35, 37, 37, 41, 41, 41, 49, 51, 51, 53, 53]
def r2sG : List Nat := [15, 23, 39, 15, 27, 43, 15, 29, 45, 23, 27, 23, 29, 27, 29, 57, 39, 43, 39, 45, 43, 45, 57, 57, 55, 59, 55, 61]
def mpG : Nat := 0xfffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_17.map (· &&& dom_17)
def goalM : Nat := goal_17 &&& dom_17
def NN : Nat → Nat
  | 3 => 3
  | 4 => 28
  | 5 => 118
  | 6 => 242
  | 7 => 76
  | 8 => 10
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xbfbac9fa4b435600449954fb
  | 4, 0 => 0xe3e585b5d7643d239a88ddd4963a1f6e9033cda588bd897c86fa85bb8423ad777c3b56b87746a1a26fe27dfc58fa3ef950631e9d4466c7213c39e8a7387c7b81367b81682ca1edf328a936272551151f24c5869419f5116014c036080f9ae3c606ca56dd06998e9a02c298f4005c2e6e
  | 5, 0 => 0x4d01605c4bf971674aed2e9647cc85044697c72b451727784275db55420fd21e410f0aa13f6a5e323cf5307e3bae591639203399385f315e37a463d936ac038135fffdeb33f70d4132b1ee163147cb34312376da30464fc32f6374ed2e21bdbf2c64fcac2c568d55284c6e0b264d0469251bae302500800a2326113222af7132229575e222657d0621ed83471f9b30251f14d9fd1f0f08ed1e56c0ee1ddf44851c5d45d61b00a59117f5a06916c9b8fd13b4711f12cbe4931243771210d5a286107201ec0fcb92d70eac4b550e09abbe0da642350d82df840ccad7830c7adc460c43a14307a0f73005b398e9049ea68002c298f401227d0800c665ac0073403c
  | 5, 1 => 0xefea78e5e9054e52e70ad37ed8eabe49d1cd86fbc6568484c47e2180c151ce00bc4811c6b7401a82b4ac85c5b39a5129b0eae219ab77640da844bdc7a540ed14a4765a949da05e49983a4a9c97f870cc95f275c594b0903d93b1efc5929e71eb90289b308f8d27e28ceebdbe8ca44832806d86cb7d29ca9477902cbe73b148576fb569416c9cb2936bae55636b2d9e19678f092e66af17c8659fe7636589dfee6185429460ac176c5dd968875cc514675b10b7595a316aa359439d2a56de52b355ef2d835508bc6e52e390e751078fb1507efe024da88195
  | 6, 0 => 0x180e822017954551179224d0177102dd16f4bc2716a04da01639ba9a160bc3b31589260a151830bd14adee2b13bfb53b12f1be6812a3a57c12510b85121c67c31218589311ba9a4a11a1b8931158ee221117d107104b30130f7716430f566aa80f3000c30eb757ff0e8f0dac0e8ac5e50e4fd1d70e0d16eb0da4d7900d4442730d0232640cbed31c0afd81d90a2a8c5709fd878b09f80db5093ba2100928f9ff0914075b088da04e0848c62b08106d470797c483076f8d99073f787c06f9095e065a03e505ed6b34059f3fa00592950104ebfe6004cd4255047288cc03cd29fd0379839d03730ec803084b8202e7ba3a022403450205025301397c6501174a93
  | 6, 1 => 0x3bdeba013a143bc339c17edf38ff7bc538c3fa0c36be6c3e36b3f12a3676a758358a0e8c356cd0e3351d513434ddc0e034d190403305f40e32c6a26f31dfd8cc31790983314b69dc309a62f730423eef2fd3f6fd2ec3c82a2e89c9422e42ee4e2de14f2a2db287372d7ecd342d36c1292c95ed092c84b6582b76cfc72b62dcc22b52e0982ac6caf62a29a7222823278a26bf38ba25f4576925c34052252d8a4e23b15e1b233814c92308331a22e6c9b4222ad3a621357faa2100752720a90bf91f7c614a1f2e159c1ef119731ebba7cb1eb1b84c1e5cc1021dd4694a1d0b6a2f1ce500bc1cb62bd01c91ca9f1c8ec01719eb59da18e7695418da2dc618258838
  | 6, 2 => 0x797daca57974291577952c4276a2484c75e2ecfc75b94043758971f8755f7bea7442b5c173b1485772553d117164a0d2715765446e8113fd6e03e0f66c2828dc6b20dcfa6a1ef01167035c3d66ec05fc651a60a264ac14e46385f15d61ea744a611771c25f8792ff5ec1b6b75c095b1a5ac03ed55a6341a959f3fdb559f2441b582b62055681508f55f769035396effb52330250522128f95210658652066ab950d2e52a4ee80a3c4c7bd15749db006e498510384852a6c44787b71547039b4146f8aaae4572bdc04402d68343c81bfa422c708941a225234130782140b2d1143f9c7c9c3eaa74af3e5582e83e5401833e497c143c8c80c83c3084cd3bf6c79b
  | 6, 3 => 0xfc83b1c4fa322d97e97ec691e0ac0765deb4d1cade890c29d8710df2d6f122f2d273f1f7cec43e4ecce08f6dc752cd09bffa2d5abfdf9650bf180dd3bef2f15ebce820cab7a0a5e4b605d6dbafb3a1d2ae33021fad03e273ab68ce73aa8b1404a4754e1ca20896a2a1c4031b9fdd297a9d7f9b199d453cb89cfafd8d9c99dde096710962960a5d93949e5b8b943334759414c09593542c6991f686c490b3e81990680a9f8e43dd7489d096578579207d84ae649e83a2d79e7d3250a67cc36a667bce39407b968f93
  | 7, 0 => 0x8390a2ec830707f681d42c978198aade7fbc28477f3e813a7d3624d57cdb8fe27cd52c3a7937758e768144647502577e6eae6fa86b20dcfa6982ba4869527b1c659e35f364d5345d644ef0785b1a703d539e5c45534137d950dcbbab4fa3812d4d43082546f94835462374a942fe38f23fc52c8b3d161bbe3ba8163937f5943e3744ee25306009543022bf823006bd362a9a5d9a2a634f5d2833e87a255b3deb24a92463206b50e41f6f587c1f5ba64a1d513d981ca4ce981c92e1de1a5524231904fd951780817414b587b312a3a57c113e3cfa111d1b070e53dc660db699640cc6b0ab0c9dd6920b84120006ae4a8e0592950101e405c9011ba5c30096982a
  | 7, 1 => 0xe9e58226d8710df2bc03f926ad668d2a9ea5e93399fe3f839842640990b64a7c8c71e27a8bed44ee87bebf2a878efd03
  | 8, 0 => 0xc813320c768144646eae6fa85dfb08a2534137d94ced500330f1064f2a9a5d9a0e619fdd0672c8d5
  | 9, 0 => 0x4ced5003
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x22220a0a2a2a00000aaa00000aaa00000a0a00000a0a00000000aaaaaaaa000000002a2a2a2a0000000022222222000000000a0a0a0a000000000000aaaa
  | 0, 1 => 0xaa00aaa0aaa0aa00aa00aa0aaa0aaa00aa00aa02aa02aa00aa00aa00aaaaaa00aa00aa00aa22aa00aa00aa00aa0aaa00aa00aa00aa00aa0000aaaa0000aaaa
  | 0, 2 => 0xa000a000a000a00080808080808080802aa02aa02aa02aa020a020a020a020a020202020202aaaa020202020202020200aa2aaa00aa2aaa00aa22aa00aa22aa
  | 0, 3 => 0x2222202022222020220022002200220020aa20aa20aa20aa20202020202020200aaa0aaa0aaa0aaa0aaa08880aaa08880a0a2a2a0a0a2a2a0a0a0a0a0a0a0a0a
  | 0, 4 => 0x2a2a2a2a2a2a00002a002a002a002a00282828282828282822aa22aa22aa22aa22aa22aa22aa0000222222222222aaaa22222222222222222222222222220000
  | 0, 5 => 0x880088008000800088008000880080008282828282828282808080808080aaaa8080808080808080808080808080000080008000800080002a2a2a2a2a2a2a2a
  | 0, 6 => 0x88888888800080008888808088888080888088808880808088008a0a88008a0a880088008800aaaa880088008800880088008800880080008800880088000000
  | 0, 7 => 0xa000a000a0000000a000a000800080008a8a8a8a8a8a8a8a8a8a8a8a8a8a00008a888a888a888a88888888888888888888888888888800008888888880808080
  | 0, 8 => 0xa0a0a0a080808080a0a0a0a080008000a0a0a0a020202020a0a08080a0a08080a0a08000a0a08000a080a080a0808080a000a000a000a000a000a000a0008000
  | 0, 9 => 0xa800a800a8000000a2a2a2a2a2a2a2a2a222a222a222a222a200a200a200a200a0a0a0a0a0a0a0a0a0a0a0a0a0a08080a0a0a0a0a0a08000a0a0a0a0a0a00000
  | 0, 10 => 0xa8a0a8a0a8a08800a8a0a8a0a8a00000a888a888a888a888a888a888a8888888a888a888a8880000a888a080a888a080a880a880a8808080a800a800a800a800
  | 0, 11 => 0xaa008000aa008000aa002200aa002200a8a8a8a8a8a8a8a8a8a8a8a8a8a88888a8a8a8a8a8a88080a8a8a8a8a8a80000a8a0a8a0a8a0a8a0a8a0a8a0a8a0a0a0
  | 0, 12 => 0xaa00aa0088008800aa00aa0080008000aa00aa000a000a00aa00a800aa00a800aa00a000aa00a000aa00a00088008000aa008800aa008800aa008800a0008000
  | 0, 13 => 0xaa80aa80aa808080aa00aa00aa00aa00aa00aa00aa00a000aa00aa00aa008800aa00aa00aa008000aa00aa00aa000000aa00aa00a800a800aa00aa00a000a000
  | 0, 14 => 0xaaaa0000aaaa0000aaa0aaa0aaa0a8a0aaa0aaa0aaa0a0a0aaa0aaa0a8a0a8a0aa88aa88aa88a888aa88aa88aa888888aa88aa88a888a888aa88a888aa88a888
  | 0, 15 => 0xaaaa8800aaaa8800aaaa8800aaaa8000aaaa8080aaaa8080aaaa8000aaaa8000aaaa2222aaaa2222aaaa2020aaaa2020aaaa0a0aaaaa0a0aaaaa0a0a88880808
  | 1, 0 => 0xaaaaa0a0aaaaa0a0aaaaa0a0aaaa8000aaaaa0a088888080aaaaa0a088008000aaaaa000aaaaa000aaaa8888aaaa8888aaaa8888aaaa8080aaaa8888a0a08080
  | 1, 1 => 0xaaaaaaaa80808080aaaaaaaa80008000aaaaaaaa22222222aaaaaaaa22002200aaaaaaaa0a0a0a0aaaaaaaaa00000000aaaaaa00aaaaa000aaaaa8a8aaaaa8a8
  | 1, 2 => 0xaaaaaaaaa888a888aaaaaaaaa800a800aaaaaaaaa0a0a0a0aaaaaaaaa000a000aaaaaaaaa0008000aaaaaaaa88888888aaaaaaaa88008800aaaaaaaa88008000
  | 1, 3 => 0xaaaaaaaaaaaaa0a0aaaaaaaaaaaa8888aaaaaaaaaaaa8800aaaaaaaaaaaa8080aaaaaaaaaaaa0000aaaaaaaaaa00a800aaaaaaaaa8a8a8a8
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x8a776e5148a776f5047768573a4
  | 4, 0, 0 => 0x8a776a502b5008a6e250849a68614b3a58a7776403a59077706e4b500776e2d0448a776e562b58a776e42395917f6a4b3a58a776f413a58a776a413558a7766502b58a614b413958a776b5d2b58a776e5a2b595776e573a5
  | 4, 0, 1 => 0x8a776f6e5d5008a77250948f776e5a2b58a8361554b58a776e4f2b58a776e423058a866e593a58a776e5b2b5008a772d0948a776e2d2559a6e624b3a58a77756e545
  | 5, 0, 0 => 0x8a7767634b3a68a77756e483a6008a776e502858a776e4b3a1d6009a856e4b3a58a77634b322b68a7771684b3268a776e604b3a68a776e5d2b0069a876e674b3a69a8a776e5c2b68a78776e4b3a6008a776e5a2b58a776e4f4b3a60092776e391858a77746e3e3a6
  | 5, 0, 1 => 0x8a84776e4b3a6008a776e2b155008a774b3a0d58a776d4b3a3268a776a413a2b68a77716e4b3868a776e4b3c3a69a8a776e4b3568a776e5d2b0368a776e4b3a2c6006e2118080459382776e4b3a68a776e534b3a692776e4b41396008a6e4e1c0858a776e4b3a1a6
  | 5, 0, 2 => 0x8a7e6e684b3a68a776a48413a6008a774b3a0a5928a7774413a69a8a776e583a68a77684b383268a77694b3a0d68a776e4b3a0f68a7768593a3268a776e5d5a2b68a866e4b3a326998a77644b3a68a776e502b1568a776e4b3a336008a772b12095003a180908045
  | 5, 0, 3 => 0x8a776f6e4b3a68a776e5d2b1568f8a776e502b68a776e6a4b356008a775d28095006e5d2b080458a776e5f5d2b6008a776e2812500776e552b0458a776e4b3a2368a776e5a3a2b68a776e4b3a3469a8a776e552b69a8f7d6e4b3a69a77684b3a3268a776e59463a6
  | 5, 0, 4 => 0x9a8a77724b3268a776e4b3a0768a776e48392b68a776e524b3a68a776e4b3a136008a6e502b0858a776e6a583a691776a4b3a32692776e4b391869a8f776e5d2b692776e4b413768a77726e4b30600776e68483a58a776e59473a68a877f6e593a68a77736d4b3a6
  | 5, 0, 5 => 0x8a776e4b3a0d68a776e4b3a276008a6e2b120858a77726a4b326008a776e2d2b50092774b39095008a776c3a1858a776e493a3269b8a776e5d2b68a776e5a4b3a68a776b4b3a2b69a917f6e4b3a68a7f634b3a32600008a776e2d4008a211809085008a694b3a085
  | 5, 0, 6 => 0x968a776e5d2b68a776a504b3a69a8a776e5a2b68a776d4b3a3168a776a4b3a296008a6e5d28085008a774a3a095007c6e4b3a0458a776c4b3a0b6008a774e1c0958a776e4b3a0a6968a776e502b69a8a776e502b68a776e4b3a1168a776e4e483a6008a5d2b09085
  | 5, 0, 7 => 0x8a776e5d2558a776e6a5d2b68a776e574b3a68a776c4b3a1868a776e5c4b39600008a776e254
  | 6, 0, 0 => 0x9a8a776e483a2b7008a776e5e4b216008a5d4b3a0908600008a776e5d2b5008a773a2b18096008c8a776e4b21600776e4b3a290460079776e3a180468a82776e4b3a1970087774b3a090469d8a776e4b3a187008a776e4c4b3a600776e614b3a046008a776e5d2118600776e5d3a2b046008a6e4b3a12086
  | 6, 0, 1 => 0x8a7f776e4b216008a775d3a18096928a776e634b3a7009e8a774b3a096008a6e4b3d3a0868a8777634b3a327008a776e4c4b2169a8a776e504b3a7008a774b3a16096008a6e4b3a24086008a776e5d502b6008a6e4b3a08026006e4b3a3208046008a776e4b211b68a87776e4b3a2e78a87776e4b3a1f7
  | 6, 0, 2 => 0x8a776e2b125008a6e4b3a1e08600006e3a18080458a776e664b3a2b700776e504b3a0468b8a776e4b3a32700988a6e4b3a0869a8a776a4b413a7008a776e3a1802600776e3a3218046968a776e504b3a7008a776e211812600008a776e592b58a776e6a4b3a1879a8a876e4b413a7928a83776e4b3a7
  | 6, 0, 3 => 0x8a6e4b211e0869a8a776e5d4b2b700958a6e4b21086008a776e3d211868a77706e634b3a700008a775d2b095008a776e6d4b3a6948a83776e4b3a78a89776e684b3a78a77756e6a4b3a78a776e4b413a067008a7d776e5d2b6008a82774b21096008a776e3a21186007b776e4b3a0468a87776e4b36327
  | 6, 0, 4 => 0x918a776e4b3a187008a776e211e1869a8a776e4b3a2279a8a826e4b3a18700958a776e211868a776e614b3a187009a8a774b210969a8a776e4b3a0c7958a80776e4b3a7008a6e4b3a28086008a4b3a2109086007d776e4b3a046008a776e654b3a6008a776e503a2b6008a776e3a1e1868a82776e4b3a177
  | 6, 0, 5 => 0x8a8777706e4b3a700776e413a18046008a776e2821186948a87776e4b3a7009a92776e4b216008a77634b3a3260000774b2109045008a83776e4b216008a773a21180968a776e684b3a2f79a8a776e4b3a177008a776e634b216008a773d3a180968a776e4b413a027008a776e3a39186008b8a776e21186
  | 6, 0, 6 => 0x9a92774b3a0968a776e4b3a18007978a776e4b413a78a7f776e5d4b3a78a776e4b3a321479591776e4b3a3278a7b776e4b3a187009a776e684b3a68a82776e594b3a7008a774b3a090169a8a776e4b3a2079a8a776e5a4b3a78a776e4b3a21057008d8a776e3a186008a6e413a2b086008b8a773a18096
  | 6, 0, 7 => 0x8a776e684b3a0e7008a6e4b3a1c086008a776a4b3a3268a7f776e594b3a79a8a776e594b3a7008a776e413a166008a776e6a4b21600776e4b2b2104600008a776e5d285968a776e5d4b3a7008a7a776e4b21600008a77644b3a5008a776e322b1868a776e4b413a397008a776e3a2b1768a82776e4b3a107
  | 6, 0, 8 => 0x8a776e6a4b3a0c79a8a776e4b3d3a79a8a776e4b3a2478b8a82776e4b3a79a92776e4b3a2b78a776e4b3a211b700774b3a2b0904600776e594b3a046008a776e4b3a0e600776e3a1816046008f8a776e3a1868a776e634b3a2b700776e5d4b210469a8a776e4b3a127008a6e4e4b21086928a776e554b417
  | 6, 0, 9 => 0x9a8a776e4b3a28700008a6e2118085008a776e504b216008a776e32211868a776e4b433a3278a776e6a4b3a2b7008a776e3d3218600008e776e4b3a5008a775d3a2b096008a776e4b3a2669c8a776e4b3a327008a776e3b3a186928a7d776e4b3a7008a87774b21096008a776e211c186008a776e614b216
  | 6, 0, 10 => 0x8a776e4b3a21187006e4b3a18080468a776e6a4b483a79a8a776e413a2b78a776e4b443a327008a774b3a09006008a776e4b3a0c6008a7b774b3a0968a776e684b3a387958a89776e4b3a78a776e4d4b413a78a82776e413a2b7958a81776e4b3a7008a776e694b3a68a776e6a5d4b3a7008a776e4b21006
  | 6, 0, 11 => 0x8a776e4b3a391879a8a776e4b3a2a70087776e3a180469a8a776e5c4b3a7008a774b3a38096008a776e553a1869a8a776e4b3a1c78a776e4b3a2b0079e8a776e4b3a327008a776e5a4b3a6008a776e3a361868a776e504b3a2b78a776e4b3a1e1878a87776e4b3a2478a87776e4b3a027008a7d774b3a096
  | 6, 0, 12 => 0x8a774b483a09600008a776e4e1c5008a774b3a12096008a776e4b3a156009a8a776e21186008a6e3a2118086009a92876e4b3a6008a773a1816096008a776e5f4b3a68a776e4b3a2b0378a7d776e5d4b3a700008a6e5d2b0858a776e5d4b3a007009a8a876e4b2169a8a776e48413a7000092776e4b395
  | 6, 0, 13 => 0x6e5d4b3a08046008a774b3a28096006e4b3a2b080469a8a776e4b3f3a700776e4b443a046009d8a776e3a18600008a776d4b3a59a91776e4b3a327008a88774b3a09600008a776e4a3a500004b3a09080458a776e5d5a4b3a7008a774b3d3a096008a85776e4b3a69a8a77726e4b3a78a776e504b3a157
  | 6, 0, 14 => 0x8a7721180959b8a776e4b3a2b700008a776e502b5008a776e3d3a16600008a776e211858a776e6a4b3f3a78a776e4b483a3978a776e4b3a32007008a776e4b3d3268f8a7d776e4b3a79a8f776e4b3a2b700918a6e4b3a086009a8a776e5d2b6008a776e4b452168a776e5d4b3a1579a92776e4b413a7
  | 6, 0, 15 => 0x9a8a776e4b3a297008a776e2b21186
  | 7, 0, 0 => 0x928a776e4b3a187009a8a774b3a0960000776e4b21045008a776e3a2118600958a6e4b3a086008a776e3d3a186958a776e4b3a3278a776e5d4b413a7009a8a776e4b216008a82774b3a096008a6e4b3a21086008a7f776e4b3a600008a776e5d2b5008a82776e4b216008a776e4b3a1b68a87776e634b3a7
  | 7, 0, 1 => 0x8a87776e4b216008a776e6a4b3a600776e4b3a2b0469a8a776e5d4b3a7008a776e4b3a186958a776e4b413a79a8a776e4b3a2b7009d8a776e4b3a68a776e4b413a217009a92776e4b3a60000774b3a09045928a87776e4b3a78a82776e4b3a2b7008a776e4b3a016008a776e634b3a6008b8a776e3a186
  | 7, 0, 2 => 0x928a776e4b473a7008a776e4b3a38600008a774b21095008a7d776e4b3a6008a776e4b3a00600008a776e4b215008a7b776e4b3a6008a776e504b3a6008a776e3a321869a8a776e4b3a217008a6e4b3a32086008a776e4b3a296008a776e5d3a2b69a8a776e4b483a7008a774b3a1809600776e5d4b3a046
  | 7, 0, 3 => 0x8a776e4b483a6008a776e4b3a1268a7f776e4b3a3279a8a776e4b3a327008a774b3a2b096008a776e594b3a6008a776e3a181668a7d776e4b3a2b7008a776e5d4b2168a776e5d504b3a7008a776e5d4b3a6008a776e4b2b216008a776e4b3a2b68a776e4b3a21187008a776e4b3a176008a776e413a186
  | 7, 0, 4 => 0x9a8a776e6a4b3a700008a776e21185008a776e4b3a1c6008a776e413a2b6008a776e4b3a286008a776e4b211e68a776e5d4b3a2b7008a88776e4b3a600006e4b3a08045008a776e4b3d3a68a776e554b413a7008a775d4b3a096
  | 8, 0, 0 => 0x8a776e4b3a3268a776e5d4b3a68a776e4b3a2b6008a774b3a095008a776e4b215008a776e4b3a58a87776e4b3a68a776e4b3a18600776e4b3a0459a8a776e4b3a6
  | 9, 0, 0 => 0x8a776e4b3a5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 36
  | 4 => 44
  | 5 => 52
  | 6 => 60
  | 7 => 60
  | 8 => 52
  | 9 => 44
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x7ce7f807f003f0730038000ffff000fff8000f9c0000e63800001ff
  | 0, 1 => 0xf8f1fc7f8ffe3ff8ffe07f8f1ffff8f1fc7f8f1e3ff8f1e0707f01ff
  | 0, 2 => 0x70e0383030638ffffe073f3e6000f0e1ff0f0e000fff1ffffff1fc7
  | 0, 3 => 0xc8cf9c0070e1c0f8f1fc7c0c19c0ffffe3ff83fe3f3ffe7f83f3e638
  | 0, 4 => 0xffffe00070e1f8f0f1ff8fffffc7ffffe00cfcf9ffcfcf9c0cfcf800
  | 0, 5 => 0xf0e00700001ff000000700000000000000ffffff8
  | 0, 6 => 0x303000030006070000007073003800001ff000003800000000000000
  | 0, 7 => 0x3f3e63f3f3e600373e63f303063f30306003030007
  | 0, 8 => 0xc0c0007c0c0000c0c19c0c001807c001800000000700001c00000000
  | 0, 9 => 0xcfcf9c7cfcf9c0070e1c0c0c19c7c0c1807c0c1800c0c1800
  | 0, 10 => 0xc0c1838c0c180030307ff303063f303060030007c7000000700001f8
  | 0, 11 => 0xe000070e1c0f0f1ffff0f1e3ff0f1e07f0f1e00c0c19ffc0c19c7
  | 0, 12 => 0x7000380700000070e038000e1f8000e1c00000000000e0380000000
  | 0, 13 => 0x70e007070e1f8070e1c0070e038070e000070e00007001f807001c0
  | 0, 14 => 0xf80fe00c7cf9ffc7cf9c7c7c19ff373e7ff373e63f37307ff303e7ff
  | 0, 15 => 0xf80fe38f80fe00f80fe07f80fe00ffcffc0f8cffc0ff3fe38ff30638
  | 1, 0 => 0xf8cffc7f8cfe00f8c0607f8c0000f80ffc0f83fe3ff83fe07f831807
  | 1, 1 => 0xfff0007fff0000ffff9c0fffe1c0fffe638fff0000ff0ffc0f8fffff
  | 1, 2 => 0xfff07fffff01f8fff19c7fff01c0fff0000fff063ffff0038fff0000
  | 1, 3 => 0xfffffc7ffffe3fffffe38ffffe07ffffe00fffe1f8fff1fff
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x282510017002401200200007edb0007490000508000024100000049
  | 0, 1 => 0x5055acf5052e165050a065050a4f5050a065050a065050a0603f016d
  | 0, 2 => 0x2d2a43021224305c58a060c080000c080490c0800053f0b2652d0b06
  | 0, 3 => 0x8e8d1808e8d180d2d5b8682851807d7ae367d7ae362faa5302d2a430
  | 0, 4 => 0xafaf5b0afaf5b0a3a75b0deddb86deddb868e8d1c98e8d1808e8d180
  | 0, 5 => 0x212006920024595c58a4f5050a4f5050a4f5050a060000049afaf5b0
  | 0, 6 => 0x717006d7052e5f7172e7f21224792122479212247921224792122430
  | 0, 7 => 0x828518082801497d7ae7f7d7ae367d7ae7f7172e7f7172e367170a6f
  | 0, 8 => 0xd2d0b4fd2d014dd2d5184d055acfd005acbd2d5bcf82851c982851c9
  | 0, 9 => 0xa3a75b0deddbcf8e8d1c98e8d1c9d2d5bcfd2d5bcfd2d5bcfd2d5b86
  | 0, 10 => 0xf3f7ffff3f7fb6f3f7ffff3f7ffff3f7fb6f2d7fdff3f7fffa3a75f9
  | 0, 11 => 0xac0f4d9ae8f590f3f7ffff3f7ffff3f7ffff3f7fb6f3f7ffff3f7fff
  | 0, 12 => 0xafaa579afa8169afaa530afaf5f9ae8f5d9ae8a559ad2f4f9ad2d0e9
  | 0, 13 => 0xfffffffafaf5f9afaf5f9afaf5f9afaf5f9afaf5b0afaf5f9afad1e9
  | 0, 14 => 0xfc0fe92fffffffffffffffffffffffffffffffffffffffffffffffff
  | 0, 15 => 0xfd2fefbfd2fefbfc5fedffc0fedbfe8ff92fe8ff92fd2feb2fd2ae32
  | 1, 0 => 0xfedffdffedffdffedaf5ffeda55dfe8ffdbfd7fefffd7fefffd7daef
  | 1, 1 => 0xfff8b6ffff816dfffd1a4fffd1a4fffa534fff8124ffafffbfffffff
  | 1, 2 => 0xfffffffffff5fdfffdbeffffd1edfffd1edfffaf7ffffa57dfffa57d
  | 1, 3 => 0xfffffffffffffffffffffffffffffffffb6ffff5fdfffffff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 28 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 28 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 159 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 159 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 159 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 159 then wireAt i else 0
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
  | 3 => 10
  | 4 => 138
  | 5 => 692
  | 6 => 1214
  | 7 => 153
  | 8 => 7
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xa88fb487803d2379720817256b61361b5c590df05900ece83bfd4359367270bd2fa07909086021a9
  | 4, 0 => 0x3c6061663a2c918d396370b239205584367270bd3613ade6355587d734e5ae6234ddc0e0345a239b33aabdb232c641fc306d08f62d1a04f12bda647229d0f96e29629c4428d1fa462883470227fe55a727f08c1f2781c043273de2fe26d656d8254c1fda24ebc74e24e6825024d0cbe324967c4f22d542cf2256f9b62175a9361dfdba011cbb21031be6ad8e1b128c031906525118df532e1841556616774bbc141daaf413e3e64e113851ed10a05d9e10773bed0fee68330e4fd1d70cb31e6b0c644f450ae488a90aabafb709db452d09c1955b06914e84057d5ec405768cb504a5888b035d84f40203e88b01b7fa180198b1b1013639b400fbb2d000995653
  | 4, 1 => 0xc54f617dc3b0a8d7be058831b8763730b361fbadb09ba72babb8caa1a7612020a5ba6a42a4754e1ca1441a299fdd297a99520fcb994fbf2c95351a5d94c1927a90dd1cd0908e74e18856a387849988fb7f0b89bd7edca70b7ed170167dd345cb7bff01257b968f937b0fafbd7a6656f27a5c3d2179be7cf17976935e7967b7f8779dfe08761c241b72ca04ab70a508476cd00b626bec051b6be2ee126b8b0ae26b2d9e196989820d697c391b67a6e50a64d34ea364a7334f63ba7e3b62d9d00861907af46006651e5cffd3f75bb16106597296d355c34e345331717d52066ab9518f1c4e4df4499c4ced50034c2e20174933b9df476448e84663bdd245d7ac40
  | 4, 2 => 0xf6ad5e66eff7e98fee991a7ce817a429deb4d1cade526046d78a67cfcbea2265c8c9c402c6568484
  | 5, 0 => 0x8faf8e908b2189c089fa2d50857ba920848c62b082a79c5082a0d6008123a0a07ecab3007b13cfc078a8202077d434e0758ed8f07099e3106ae4a8e06a0ecee067f6c05064e72b306279ef60623c9c005fb9fa305929501054e856e04fdcb2c04de4d4e04cebbee04cdb69a04b3b0b5048352bb0460bac604559ad00446328b0429dbff03fb2549038e388b03541ee4033922910331d587031191d802eb3d0302e7ba3a02e16c2902bc344f02b884fb026cdfe4025e611002137cfa0203f44b01ddede101d4d26601be9fdd019cc41b01919888016ff903011ba5c300f3d6aa00e1fac200ca5b1600c9d11d00a938a900671105005a60d500537cf700396303
  | 5, 1 => 0x13b179f813970894134f2890132a788a12f93c5c129977ac128ace771232c98c1218c3131218589311f6847b11d213ab1175e15f11730b4d115eaf42110ce2291106030110b414ce10a8b1f410889a1e108417221080e276102181901011a257100ca8f10ff86f2f0fa9ef690f9e061d0f8770e30f5e7ecf0f47a7f80f2079ff0efb58dd0e4fd1d70e35c7700e1185690dc4f2ae0d8c66540d752ec90d2c99430d27335e0d1831d90c7e0a270c7155af0c6909b90c492fc50c457efe0c0a5de90c03f1640bd8dc820bc433d80b8be38b0b7e0e600b3fa4a00b30ef250b2fd9430b0a42470aa1520b0a9ba0730a5ff4d00a10b0f209bc5221096fbe9509528a48
  | 5, 2 => 0x1e40827e1ded6c171de24a461d662c251d5c1de01cfed0571cd391b51ca4ce981c92e1de1c7cf2111c22d2a31c1e581d1c0615c01bd2b1321b9ee8301b8c05e51b681cb11b51db001b256c091b194fb61b030b831af240791ab629911a9114151a5924091a254d9719ef522319edca2019eb59da19d44d9619b141d3198cbf7c195309db18e1772c18dd746618c9b18a18bd90b818ac06dd187ec37718614f9a180f1db417f9208017c2d5e317bfbecd17b0a6c017739fcb175fbaec1757b39316a919a516a04da0168ea91d163e72f0161e884915e8d611155b10ec14f2d9d614ee37c614ce89bd14b587b314b1d616147f947b143aa75d14091fea13bfb53b
  | 5, 3 => 0x2a32e87729c6f90c29195ba128eefed528e0edf428b0401a28ad7fa1286b0ab82855e8732747733926f6cf7a26f5000e26ebd14026eb6d6b26e65a8726beead1267882a5266d1d032658d217262043582601064825c29aae25aa86752594ee85255b3deb24f57c2424d1a51324ce8ce82450ab1023ef0d0323a914bd238d9d832368cf7f235f811623574568234cea90234860db233bc2302327bb0722f5531222be7bac22b46d6d22b07dde22af4e97228590b9227dcc43226d6f7721994f99219650c4219211d721461a822141da632124545d209e3a62206b50e4202e165220121f951f752c341f6f587c1f5d8a761f3b512a1edac8071ed21bfc1e4bcac1
  | 5, 4 => 0x37c2eda437bb312837a2d4213793f20a3780b13e3775152a373c7cde36df25b33699b2b0366ff4a0360ef66735ebeb5a35c3914035c29f03358a0e8c356213b535524b77352a10de352479e934ddc0e034d30284344aa7573449a555340d4b2933d9398433c4dc0c339345dd32af6a913287460a324b91eb31a5776c319dec06311a709130f68cef30e281b730c6c6cd306d6afa3060095430585deb303adde23033898d2fe107c42f92fcb22f42d9852f1f798a2f14c78e2ec9695e2e3d88b72df2083d2de652fb2dd1712f2dc9bd022d2078be2d05622d2cfa7d262cd09cd12c6b423c2bcb2e602bb781ec2ba343a92b079f362a9a5d9a2a8993932a48326a
  | 5, 5 => 0x45ffa3cc45d73f1e45a9f312458c7b15453a7f4044cd1348449215a14446c0b744449713441da9e7441b03c94410591043e2726343bf65914373463f43355e4a432173d243043c2142fe38f242b7affe4295aa5e4293b9d9418ba83f417e5b0c4072bc5240710ab4406c57b03fe279133fc52c8b3f7ef7053f76a28f3f0e7d4a3e5c938c3e474b623e45d3fa3e1bb7083d81340e3cf5efd93ceb1c853cd8d1c83cace64f3c82eb253c8238ae3c4a4c4e3c35e7ea3c15cace3bc430123bbb63403bac4cf43baaa31c3b31a8b63a5bb5e23a3d6dcb3a3242cf3a09dbae3a008958398823b33941077938caa40b389bb45e3893c7bd3854c98a37fe914c37efeed1
  | 5, 6 => 0x5b1a703d5addbe105ab8302c59dab3d359a6aa2e5962a24c58a96621585a528f58497fc7582ef68957b4f523574b2e3157165fee56f8c11f56b80ae35681508f561a9ab055bce94d551186b954d6b5ad53a93233539e5c45534137d9531ee59e52a0f13c527abe925246a17f52066ab951844113513466fe50dcbbab50bb41f850ae558450437c494fa3812d4f758da04ed2f5bd4e7ff76a4e48a81e4e023a994d08c8704ced50034bf47ea14b9c00124b84cbcc4aeaaea44ac7b6844ac2be184ab740e64a905d0f4a2aadc74a13edb349811102495b8f7a495835a148fe860548c21ebb48826961484a52db4825661d4803592b473fa8de46235a7a460d7af1
  | 5, 7 => 0x706e47d8704f60e9703c5891701e82e46ffe25d36fa6c4b06f61157b6f1286326e8e260a6ce6424d6cd539506c73d1d56c723f4d6b70fa486b2e1c6e6b2483ee6ab5b7046982ba4868d8af8868a625656873cf53681fe90c67023bed66cee22d66cd095566417a46661a3c736528f63c6523973164d5345d64c7c17164bf79f6644ef0786423793b641c803d63cea38363c4b734639e71136358ff16631423586235de1361f1247e61aaec5c6186f6e7617e85f8612ea4fd6111988b60e698f260e13d3e6053978160086b075fbdcf575f7fdfbb5f0948e45ee098e35ed0b8a55dfac6ee5d8c9a2d5d6d6bfc5c508e0c5c27c5ea5c1c6f345c023d205bf1ec0a
  | 5, 8 => 0x908e74e18ec4c0888df165118dc7d5928da9d0668c71e27a8bed44ee8bdb39ce8a78be1d8a2584da892d7585887904688864ba1e884224ee87e8076d868585e1866f4702863dc07985a0fa1184207b2783a2d79e8390a2ec833777cb83272197830707f68227015081fb2dd581bb81477ff7e34d7f3e813a7e3d38cc7d8a37117c9feef77c5f29207ab19c2f7a60c89b7a5c3d217960e6ef792295897904c7bd78fc89937893f541785c9761784434f5780670f877c682bc77b2ae4c778b01037728876376a914d87609aae1749b39907455e6e773f9546273d2af71731b75f672b7cc3f72665a4a723a79b97224e91771955eb070a62afa7098206e70866090
  | 5, 9 => 0xb6d0bef6b66c20efb4e15331b4ae14f4b32aeeaeb239e27cb1c218b6af7e1109ae9c5e32ad668d2aad2400deac1a6e91aa417321aa132505a9ccadfea953cfbaa93949c1a7d26d16a7612020a6ddf99aa4754e1ca43592dda3298f56a23c302ba2244dfda1840cc1a1546824a147560ca09aea839fe76c0e9ea5e9339e9759de9e3fa8099d57af389d364b149d11032b9cc838bc9c99dde09b78fcc79b5d6ad59ab334069a9bddc59a514ba799f9880699b3fc47994d0661993845e598af47179891016c985becad98146595976423c796d4983395da76b195bf7b469589369995679bee9555ba5293df0737929f892892656f81925665cc9100353290b64a7c
  | 5, 10 => 0xfec1f412fba37df0f8db840ef3ea7102f37e69a1f2c7e59cefc28a69ebfe74e3ea6542c1e97ec691e7ce300be606a6cfe31d3555e0b3ba3cdeb4d1cadd4b046bdb576419db330348dae86fa5d8710df2d691582cd4c5bab9d46d28d7d2f6094cd0f51481d0d9b643d08b1910cf4f1298cce08f6dccd220b2cc98070bcc1278bbcac428a6c813320cc6b1fd97c5a65e8dc45783c3c19e491fc0cf70f9c0b50825c0101336bfeeb043bf73cdafbf538f8cbf180dd3beeae7c0bcc251c8bc337d89bc03f926bbf963e2bb9eecb1bb41461b
  | 6, 0 => 0x551e1db0538152c05260cb30507cebb04fd760d04e0f2a204cdb69a0494d76e04768f57046f0730046e575303de0a3503d6354903caf95303a5cb3203998d140388ef0603802ea70369ae640343a38d032027ae031e3e77031191d80309ae2102dd58c402cfa57d02b5063a028f29790282ea0e0258b7190244a3800242053602412a3502350fe90231bf960210a65701f8b6ba01e405c901b82f7e01b00a4301ab67ea01a0e589019f8841019cc41b01981fd0019722c9015a5357013042fa01238485010f1c79010c183700f7f5b400eb86ad00c6df0100bc73fb00b80f4800a97d5500a884e40096982a007ffe6e007e77de0078df0b00537cf7000315e0
  | 6, 1 => 0xa7ff6ed0a62347d09d0b16b09c7f61f09bd3e2d09b2e18b09ab3979099cbba9098e2051098d3ff8095ef437091b514e091484d80900f252090084ae08cdf73c08c0b29908c079050899b16c088b300b0852d32a0844f5d40836de0f0816db2c081631340812e11707e0b20a07dfed5d07914a60078c78a30773e6eb07710ad8073ea90b073c4a01071326f70712dfbe0702a2a106f3e07806def8cc06cd36f806ccc6e106ccafd006ae4a8e06a764cd06a649f706a4c722069f11400690bc6a068c8abb0672c8d50662c809062916f00603cd3e05e3c4a805e3585705dd7e2f05d92d1305c3b2ae05aad0f705a4d23005a33fba059cb08305798a0d05714380
  | 6, 2 => 0xfd343f30fc1da660fb60f0b0f9c35a20f95ab660f9554ee0f8c50620f4407970f2079ff0f1721ba0eff32d90ed53b970ed1ff4e0ec68d190ebf6a0b0ebc0dc60eaa210c0e9e13e60e7a400a0e68eaf80e619fdd0e3c02790debc9450de9fa0f0dd9f8770dd206760dd08d4e0dbc92560db699640d90a6580d4f82ce0d4037100d2e11e50d23d5170d1d80ad0d19fdbe0cfbb5a70cdf36c20cd24fc70cc6b0ab0cb29a6f0c991d890c67ac2a0c55ea560c457efe0c37a23f0c0f51980bf9bf000bdc2c850bd8dc820bb59e3e0bb55bfa0b8412000b726c050b51fa620b513d9f0b2fd9430b0f6e930b0380f50ade45ff0acad9c10ac500080aa3dd420a9ba073
  | 6, 3 => 0x1512ac1f150b44f5150984f91506a0e914ea8b6714e8a06014b587b3149fe90f147f947b1463bfa0144710c1142378e314141b9513ee575413ee171e13ed7a8e13c5dde613bac31b139fe615138e16bf138872fa13886f9913823ad51378024d137078531364bc5e13337eed1320529a13127997130699c412b5d1d91273a145124f1fc0124a89cf12374dbd122c0d62122b137612295e62121d8d8711f06575119f6395118697aa1175f9731172f34c116a9a2311674bc511613596114e3a501146f367111d1b071113bb5a1104b81210f3cf4710f0e1a610ee47bd10d85f6210c2ce8010bf4434105a5f1a1045f48010406e57101add4d0ff5a2fa0fea799d
  | 6, 4 => 0x1a1d5e8b19d841b919d44d9619cbcb3c19c76e6119bda458199ee9f6197c881c19770ab21958c29b1948c26f19383264192aba5919234d9e191da153190d3cce190821881904fd9518fdab2d18ed6fbc18e70bfd18d7316d18c11c7918af5aa5189f073b1899be121892aa63187ff5381873513a186686e3183471451823b102181ace9117fc375617f98b5417f7732717f46c7c17cfae3517bc032d17b7278b17727d19173b1b9b16fded7b16f6811716ee79be16dc8d0416dc34d216d00fc716b53ee216a79985167c7cca1673d63a16639b131622c2b216043d3716001f7a15f1adf215e8d61115e6209515a3620a1591a03615430929152f8b9d1524e900
  | 6, 5 => 0x21b2b2b1219a431d21780e5021610251213d49c721160fc52113fee42105282820ab4689208fa0e42063c5772051986220457d60203b2c8f1fe692701fc84a591fbf7fbb1fa271291f791be81f7215df1f6eb2d81f04ec041ed9fb1e1ed21bfc1ec140be1eb54e7a1e82da2b1e69d6381e5aad2f1e2d8d961dd183cb1dbdb5231dbadae11db110081da6d6281d9559ef1d723a221d513d981d4e20ab1ce7d0611cd232ab1ccf96e21cb19cc81c99e2531c92e1de1c8c0ec51c896b941c60ca311c59345e1c55b0571c4af9561c3cbde71bd1780a1addf35d1adb12191aced5791acc86d51aaff60f1a60edbd1a5ddf121a5524231a3c5cf61a342c841a32f630
  | 6, 6 => 0x288e72ef288cce3b288c6f33286f6a332853c2252851534028406f6a2833e87a2824434727e95e7627c1750a27ba23f627a5b99827a4343c274d3b6c271c5d2627093d122701ef3e26e2b49926dc9aff269cb242267882a52649843726204358260111ba25d663e825d07b0125d00294258bb5b42588f9212583027225665abc254d429525241254251f58f424baabf824b369b724aa379024a9246324a0e1942486d420241dcb572415f64b24080c1523ef2a5e23d5bf4c238d9d83234ca751233e8327233bef12233bc230232299ee2319d16a22f5531222dcc56822b0c819227ac2482277488222305fb722149c9c2205d12221d3acb421cc7ed521b5649d
  | 6, 7 => 0x2e2fcc862df4c6b52de596012de24bae2de1e5122dbd79122db6be982dabe6582da09a7d2d6f2f2c2d508ec42d3343b42d2607e42d1858ce2d0c84eb2d05622d2ced24502ce5e8f02ccd4b1e2ca572812c9d048d2c74e1292c6f163f2c6778d52c0a605f2be7d30a2bda3f742bb5e4442baf25c12ba52aa62ba2f1bd2b3f07d02b3ab1752b23448c2b0bb5d02b079f362aed6db92ae452572adfacad2ade22742aaf9a242aadaaa12a9a5d9a2a8e94d02a8a25092a8950f22a7afdf92a634f5d2a6041c22a37cbc02a21bc8a29e7715829caddac29a08f272990bf73298f79702972775c296db940295995a5294f7f38294bada929493ae828ea1c6028ac9c1b
  | 6, 8 => 0x3729db2f37208bac37111596370af73c36df25b336cd139836b4f2d636952e2235d6157a356301ac354e9915351c08653515782034e071f734d0fd9c348cb2f2348c50f9346cbf5134605a42345a27d5344b8ed8344aa757343c4de633e692e133d6aa1233aa096033a7377932c8c8ff32bfc88d32b3ce03328a11393287460a327e4056323370dc31f372cf31dc6bb931a9d5e631a9b88531a5776c317cb4a93146f1a4313abf0231320a4a3125892e311a7091310fe98a30f1064f3055d82f3038b2473022bf823006bd362fc026a12fb3a7782f793a2f2f78d2642f425f0b2f2fc8a12f039d9b2eee56cc2ee5d63c2ee0b6112ec9695e2eb9c8d52eaa3ff0
  | 6, 9 => 0x40768874407598d0406426b84061aea3402bdef64009a1963fde06d53fca8fc83fc52c8b3faf3baf3f7cca723f59186c3f560b3c3eddbbbe3ed61e433ec167013ebf6f673e668df43e46f9163e26f7a93dc441923da0502b3d330d893d161bbe3d01281e3cfc30733cf566673ce637663cd8d5f63c82eb253bf7d1ec3bebdb133bbcda163bbbc96f3bae5db83bac4cf43ba816393b46cc963b3946a73b233d023b14b06a3b028a6b3b01b5c43ae76e8d3a9012de3a7b71df3a68b7173a0bf56c39bdf8b939b4e4c13938524c392b6a3a39202ba1391c80c538c77dd4388cce1c382ce56c3828aceb37f5943e37ce020037a9f5b637a81d7b3775152a3744ee25
  | 6, 10 => 0x4b0ccd4e4b0ae19b4a736cfe4a3bc34e4a2aadc74a29b5ed49ff454549c6318f49836137495b8f7a495220c848f7170348af971748acd794488269614871691f4858fc3e484a52db4818f01e481753a8480022c347f7b14647d2434b472fc7df471caf0646f9483546f912494626d63f461914614613939a45b59b7345b473f045700b184558770745380b734536622944daf10f445c9d00443e583c439d108f4389bd2e4379388e435d6270434cf4f043471c62432173d242fe38f242ee90f742e8bd06429c9efd427f15c8427b5db5424d259d424a48ca41c865a641bac05b416dc1f34160ed9b4141efce413ce1514138baa24133cf3f40d707a84096950f
  | 6, 11 => 0x542e51fb541c9027540bf19153c590ad53453add534137d9533fd45853394e26530f6bd052c8d5bb52a2f1455271257a52274ac7520d2ac651ea60ec51cc18d551c8625a51ba0d78519a8218512b592c512b41c35102a75150dcbbab50a4d1d1508f8021501247d04ff228824fa3812d4f8c7bd74f7a648e4f1b37ea4f037eed4edd70784ecfc6274e67028e4e4612624e259eb24e2012184df24cc54deaf1884dcfb7bd4d9722064d8a98554d60175f4d48b7234d4308254d31af6b4cfb283b4ced50034cd48b134cadc5cb4c8c28fa4c61ad8e4c5b7d3f4c4af01d4c1d3da44c028e044bd33f5b4bac47cc4b91edba4b747a844b5191fe4b30593d4b2666d1
  | 6, 12 => 0x5f04ae155ed3791e5e5a728d5e50c0c45e4beea65e4488175e28c8aa5e22bc8b5e20d4185e12afcf5dfb08a25df999d25ddb51bb5d7d6e6a5d1df2ad5ce45ca75cd809c85ccf21665cb8e8a15c8cfc045c6d604d5c4b21b05c0dd99a5c023d205bfd6bbe5be3c0435bd02b495bc04bfa5ba2d40b5b43330f5b2b0bfa5b1cb05c5b1a703d5b0722435af6320d5aec89df5abdb0b55a6259b459e4c0d259bd245359b1d08a59a6aa2e597573d759737e1559498faa5933895d5926a8bd588cea0d57d2d680578b4de2575e01cc574e0359574b2e3157312d48570ea3cd56ec738b56662fa655621c7855312d1554ef4b3954e8cafc54d6b5ad5499fa38543440c1
  | 6, 13 => 0x6982ba486962b4b269527b1c694220df68cec25a68b79ca168ad78ee6898475567e545cb67a16f416793550d67023bed66e2cbe366cd095566cc1f90666f284a6659ef32663adcf7661d6adf6603cb0565ff5b3e65e1bd4b659e35f36541c03e653a36c065239731650929fd6507810864ec553964e4d48764d5345d64c4acf064bf589764bcbc93644ef07863eeb4e263b800d863b694ff637a072863423786632fe21d62e5591362cabd2a627ada84626d6d47624146f16219c65561f40c9461b36b2d6194e2ea618baf6d613db08361172ae160db74eb60b4158d60b139cc605bdc575fee42565fc765eb5f98725b5f82fce85f75f8dd5f53cb015f3df64f
  | 6, 14 => 0x7937758e78f206f178c7a58f78b6420e7870609277f3d634772d165576814464767a348c7662133876317294760278a575dee47e75952ff0755fda61754f6a297545bffe7502577e74d26a9a745cfe31742d6e2e742151237416397f73f95462735e01c4735a1cc072d25ba1729ddb5072625a38723e811d720be5cc71fd207571dab505717e1892715f6c9370c5f38770aa985d6fee51826fbca6166fb0a3756f4e9fef6f4d47456f1d17ef6ee40e116eae6fa86e6358136e5775b86e3cc9176dc6c4916d96e4546d4333856cf156d16cc6a3b66cb256706cacafd76c922d536bde55a86b291c336afc3dcd6a530a216a39311069d6c33769b7caf2699a5285
  | 6, 15 => 0x8c23b6918c2119148bed44ee8b43d9ed8adb68208a465c088a41af2e8a26f00389806fab897a88208944edf2893616778864ba1e881060f787d4655787bebf2a878efd03874e340e86cfb173864b7bdc85bd39208547e14d85027c848491b95f845d455183930e91838e270483077276830707f682ee8feb82d736d482320203822132dd8203823681f4b26481ecd7f281d42c9781bb8147810a05b980c4fd3380b8770a808f7a728039c4547ff008c47fbc28477f5515f67f3e813a7e420fdc7e2492767d3624d57cdb8fe27cd52c3a7c52f6ca7c006ce17beef8d57b4ea1c57b349dba7a99fca97a9072e77a70b00c7a62f5747a6033bb79b0f435798bd3e5
  | 6, 16 => 0xa35cf822a33d7601a2932168a16c9400a13ae083a0a0a36ca06d7481a031f2c8a00e28ed9f7457c89edcc54c9ea5e9339e390db59d8ea5939d6fa4a79c766a3d9c4e91879bf64e999b78fcc79a1516ef99ff848199fe3f8399f98806996de111994497d69844579b9842640997d0bd78976423c79759347b970bfef696eb802b96ccf3709634d4aa95f0496995bf803a959cb0bc9590c411957967f194cc0b4194a025e0946d9cbd942379dd9375af69936c7ba69322eebc9316aea99284abe5923089c6919c5680918568c9917dc5bb90c867f590b64a7c905228b89016d0fe8ef3a2ca8ee4f3678e461f178d4ec7be8d31fa208cd588cf8c7901268c480189
  | 6, 17 => 0xc0cf70f9c0bdbdbcc0b50825c06708d8c033c360bfeeb043bfc5009abf272538beeae7c0be7445c9be241afbbe058831bc1e8183bc03f926bbee18d1bb195d2abaeb0e94bae0164aba4a3eddb6c5f114b64a46aab5c9271db581394fb54882a7b4c23340b4ae14f4b47fd3c2b42055adb346886eb3322e71b2a24c8ab2776a21b2321b01b11a77bab0dbb16baef319c5ae9d8f59ae704bf1ae0d8e27adae6493ad6f496bad668d2aad24974dad1b2c4dac9afc57ac88f59aab85eb5dab6555fdab3cebfdab0bf822aa0e0464a9221e34a8583910a811d2f5a78230b4a6cda279a69f1185a613294ca551c291a500e209a4c8279ba4b7bfeaa49a7522a3777619
  | 6, 18 => 0xff2ff43cfba37df0f9536981f37e69a1f2aa30aaf18094c5ee59d7a9ead75beee9e58226e9746c75e544964ae49a56cfe3fc10ade220a264e1afcfe8e1750ff3e0a6051ae0013595dfc6a7d6debedec9dd5e06b5dd4b046bdd1f6892dab67d0fd976b015d7c3c7bcd6fa818bd691582cd6708162d60dd6cdd5c70378d5b59f81d5b35c53d58d4c3ad499601ed35bed5ad2db975fd29fe169d275a64ad1b9ea17d196bb51d10d9129d022e0f3cff05da4cfc7488bce90bdc7cd414f61ccf0ec83cbcc6d73cb03dd11cac96336ca88360fc839dd94c813320cc5d05e0fc51e17c7c5074216c49f19a4c463f4fac29751a8c248c06ec206fce1
  | 7, 0 => 0x30f1064f2de596012d6f2f2c2b3ab1752ade227429e77158296db94028f61a0c288cce3b25241254240c59ec238baec5233bef122319d16a2308457d216d3abf21663c201f7215df1e82da2b1e3e4eea1dd183cb1cb19cc81c3cbde7160ce25b16001f7a15e8d611159f0bfb13c5dde6118471651045f4800f56e6a30f1c6f950e9e13e60e94b88a0e619fdd0d90a6580d23d5170c991d890c67ac2a0b95722f0b4b7bbf099cbba90899b16c088b300b0852d32a082658340773e6eb071d87b606def8cc0672c8d505e3c4a805a33fba0547555e0494d76e04768f570453760c0339582202dfc1ef02ad0a7c02137cfa00c6df0100bc73fb0078df0b00537cf7
  | 7, 1 => 0xa8b2a0eaa6aa695ba675548da35cf8229e3fb3739c59309b9c0d73ae96d07d3d942379dd918568c98944edf2868585e184830b72829bb51b81989a58810a05b97731b0a972d25ba172625a386da978f4699a528567e545cb66cc1f9064bf589762cabd2a627ada845f48870c5dfb08a25df999d25ddb51bb5ce270f45b5b470859737e155870e674552c7e8654ef4b3954a24a37542e51fb526c4e89520d2ac6501247d04e4612624dcfb7bd4ced50034cb3732f4cadc5cb4c5b7d3f4ae55729483bd70b4818f01e472fc7df4558770745585ff644daf10f443c1e523f7cca723f59186c3f048f313d1259793a22a09e37a9f5b635a19b24352853d134278a09
  | 7, 2 => 0xf9536981f2aa30aaf18094c5ef2d2818ead75beedebedec9dd4b046bda23f4e8d920eaabd75d25ebd5b35c53cfbf7520cd414f61ccf0ec83c9163c49c813320cc51e17c7c06708d8be241afbba4f266aba4a3eddb346886eb2a24c8aac9afc57ac79e26c
  | 8, 0 => 0xdd4b046bcfbf7520c9163c49a35cf8223f048f312319d16a15e8d611
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x16540324c1400000413444030000000000c91042654430441400361452004040161141320c0401000412444030036141310044010000000000002000d410440301
  | 4, 0 => 0x8000000008d10400000000851000004810080302000000000000700041344403000000000040102000000000000800000000c910400140314053000000010440200000000000000400014344843020000000000007000000144020000095410c13000000000080101000d4104403010004134440300001411204030200000000000050000000000001000c0404c4301000000008410100000000000020000000084101000000000000500000000000010000000000004000941044030100000000000040000000080102
  | 4, 1 => 0xc4420c5302000413444030000141310043010000010440202000d410440301000c4420c53010000000000008000812144130000000244412000014032481300000000000000400000410c1201000000000000700000244c520000000000000030000000000004000000000000400144234c5300000003104820200000000c1100000000008d10600000000c91000000000000007000000008d10400141320c03010004820040302000000000000300000000000040000034485200001411208030100000000c110700100304c5300
  | 4, 2 => 0x30000000040105000000008d104000d410440301001412100430100000000c5107000000008510000000000c9100000000000000400000000811000000010440202000c831084301001453408030100000000000040000000000000000d5040843010014434481300000d410440301000000000000500000000000070000000000003000d4104403020000000081100000003444020000140414c83010000000000007000000000000000000000000040000010440201000d404484301000d410440301000000008d104
  | 4, 3 => 0x4001483444130100000000000000004134440300000941044030100000000c51070000000000005000d4404c4301000941044030200000344852000009410440302001443448130000094104403020014132080301000c03100430100000000000040000000000000000000000000100144234c5300000000000000700041244403000009410440302000412444030000000000c9104000000000000400140234c13000000000000004000941044030200000000c9104000000000000100094104403020000000000004
  | 4, 4 => 0x40101000d41044030100000000000030000000000003000001044020000140324c13000000000000008000941044030100055400c93000000000000003
  | 5, 0 => 0x104402000000000000000000000004110000000000411000000000000002000000000000300000000000050000000040103000001440220000000000c810200000000000060000001404200000001040420000000038022020000000000001000002440520000000000000020000000000006000d524004302000000000000100000000000040000000000006000000000610000000000841010000000000003000000000e1000000000000003000000000000300145200403010000042005202000000000000100000000c1107
  | 5, 1 => 0x30000000000001000000000a102000000000000700000104402000000000000000000000000a1010000000000006000000000000300000410c120200000000841010000030405200000000000000800000414c020100000000811000014121004301000003248520000000000c9100000001044020000000300c42010000000000008000001044020000000344082010000010440201000000000000100000000801020000000000004000000008010100000000000060000001440200000000000000700000000c5100
  | 5, 2 => 0x144234c5300000000140420000000000c5108000000000000500000018022020000000008102000000000000100000000000040000000000003000000380a202000000380620100000000841020000000000008000000000000300000048482020000000000004000000000000800000344412000000024440200000000000000800000000000060000000000005000000000000300000144802010014834441302000004200420100000244c120000000000000040000034402200000000000000600000048082020000000000008
  | 5, 3 => 0x420c5201000000000000300000000c510000000314c120000000420c12020000000085100000000000000600000240412020000010440202000000000000400144344813000004124440300000002444020000000420c520100140234c130000000344402020000001404200000000008010200000000000010000000000004001403248130000000000000040000000000008000004204120200000000000040000010404200000000000000200000104402020000000000000000000000000700000140022020000000000003
  | 5, 4 => 0x401020000042005201000000000410100000000c910000000000000040000024041201000000180a202000000000000100000000000030000004804202000000004110200000420c520200144344813000004124440300000000000000300000048c52010000024041202000001044020000000344852000000000000005000002444020000000000000000000000085100000003404120200000000851000000000000004000000380220000000000c910000000400c5201000000484120000000000c01010000010440201
  | 5, 5 => 0x4140820100000410c12010014432485300000002044120000000000000070000000000004000000000000600000048c52000000000085100000000000000300000410c1202001403248130000000410c120100000000c51000000003802202000000008410300000340412010000000000000000000000000300000000c9100000000000000400000310c52010000042041201000000000000500000000000060000000006100000000000000500000140c12020000034406200000000000000300000000c41010000000000008
  | 5, 6 => 0x40000001084201000000000000700094104403020000000000004000004204020100000038022000000000000004000000180220200000040c520100000420c1202001443448130000000420c52010000000000004000000008010100000000000030000004484202000003444020000000000000040000000000004000000000000500000420c520100000234c1200000000000000500000000000010000024006202000000000e1000000001440200000000004010300000414c820100000344842010000000040102
  | 5, 7 => 0x841010000002004201000000008110000000000000080000000002102000000004010000000420c52010000034402200000001044020000000344852000000032080201000004204120100148344413020000014402200000002444020000000104402010000034440200000000008d1040000000000008000000488520000000400c520200000000021020000000000005000000008510000000344812000000000000006000000000000400000000851000000024041201000000000000300000000c11000000024405200
  | 5, 8 => 0x500000310c5202000003448120000000000c5101000000004010300000000c9100000000380220000144344813000000024040201000000000000800000140802010000000000001000000008d10400000000c91060000014002201000000000000400000300c1201000000000000300000000401010000000000006000d524040301000001044020000000104402010000000000007000000000000100000000c8102000000000000500000000000060000010440200000000000610000000000000030000014402200
  | 5, 9 => 0x40000034480202000000000210100000240412010000010440200000000000000600000000000020000034002201000004108120000000000000050000000000000000941044030100000410c12020000001440200000000000000300000420c520200000000000050000000040101000001044020000000000000040000034485200000000000000000000000000010000002802200000000008110000000014402000000004840200000000000410200000048c9200000001208020100000344852000000000000006
  | 5, 10 => 0x8000000000000300094104403020000000000008000002444020000000000000040000001404200000002404120100000000000020000034406200000003448020100000000000010000000000005000000000a1000000000000004000000000a10200000000000040000000000006000000000000400000420c5202000003448520000000000c9106000003100420100000000000020000000000004000000000000700000000c110700000000c910000000040c52020000000000004000000208420200000000c1100
  | 5, 11 => 0xc01010000010440200000000000210000000344402020000000000005000000000000200000300c120100094104403010000000040102000d52404030100000000c5101000000000000100000420c5201000000000000600000000c9104000000000610000000400062010000000000007000000000000300000420c5201000000008d10400000000c910400000420c520200000420c120200000244402000000000000003000000000000700000000801010000010440200001483444030200000000000080000034441200
  | 5, 12 => 0xc910600000000c910600000000051000000000084101000000000000300000410c120200000000000080000000006101000000000000000000000000000000000080101000000488520000000310c520100000420c5201000000000000600000000000020000000000006000000000000100000104402020000000000001000004108120000000104402010000000000004000000000000600000000841020000001404200000000140420200000040c520200000000c910600000310c520200000400c52010000000080101
  | 5, 13 => 0x244402000009410440301000003444120000000104402000000000000004000000000000700000424c52000000000000003000000000000300000000000030000000000003000000000000300000000000060000000040102000002400620100000018022010000000000006000001200420200000000000010000000000005000001044020100000048c92000000000002100000001044020100000048c020100000420c520200000234c5200000003444020000000028022010000000000005000002440220000000048c8201
  | 5, 14 => 0x21000000000000003000000000000400000000c110800000000000040000000000005000002100420200000344402000000034041201000000000000500000420c1201000001044020000000000c110800000340022010000000002102000003404120100000420c120100000000801020000000000003000004204020200094104403010000000000008000000004010000000000c910000000000000070000000000007000000000000600148344413020000000000004000002444020000000104402000000000084101
  | 5, 15 => 0x300c120100000048c120000000048412010009410440301000000000000100000000021020000000000004000001044020000000000c110700000000000050000024440200000001448020100000038022010000034441200000000000000400000104402010000000000007000000000610000000410c12010000000000006000000008d104000000000000400000000000040000010440201000000140420000000000c110000000000000080000024440200000001044020200000400c520000148344413010000001440200
  | 5, 16 => 0x400c52020000000000008001452004030100000244402000000000000007000000000000200000044062010000010440201000003444120000000000000030000032080201000000000000700000400c52020000000081100000000488020100000000c91000000000000004000000000210100000410c120200094104403020000010440200000000000000400000000000030000034406202000000008010200000000c0101000000000000800000240412010000034440200000000280220100000000801010000010440200
  | 5, 17 => 0x1000000000000400000000c11080000000040105000000008d104000000280e2000000004406200000000484020100145200403010000024440200000000000000600000420c5202000001044020000000000000050000000000007000000000000200000234c1200000000008110000000000401010000000000006000001044020100000410c920000000234c520000000324c1200000000000000400000000411000000034440200000001044020100000324c1200000000000510000000000000050000000000005
  | 5, 18 => 0x8d106000000000000300000000000040000000000007000000000000500000400c52020000010440202000000000000800000320c4201000002100420100000000000040000000000003000000000000400000420c5201000000000000200000000000080000000000008000000380a20100000000000000000010440200000000488020100000120802020000000000004000000000000100000000000000000010440200000000000000400000104402000000010440200000000000000300000000000070000000041101
  | 5, 19 => 0x30009410440302000000000000600000048c92000000000000008000000000000600000310842010000002802202000000004010300000340402010000000000004000001044020200000420412020000000000003000000000000000000140022010000010440200000003404120100000000000020000000000006000000000000700000000000020000000040102000004204120200000000000000000000000004000000000000400000000801010000000000000000000000000300000000c9100
  | 5, 20 => 0x4108d2000000010440200000000000000300000018022000000034041201000000000000400000300c12010000000000007000000440620000000104402000000010440200000000000000400148344413020000000000000000003404120200000018022010000000000007000000000000400000144022000000000000003000000008d104000000000000300000008062000000000000003000001044020100000344402010000000000005000001044020000000140022000000010440200000000000000300000000c9100
  | 5, 21 => 0x10440200000001044020000000000c9100000000000000700000410c920000000104402010000010440200000000380a200000002404120200000018022000000000000003000000000000700000410c92000000034084201000000144020000000000000000000000000000000000000000700000000000070000001802200
  | 6, 0 => 0xe101000000000000700000000c4101000000004110000000410c12010000000002101000000000000800000410c1202000000008010200000000c410100000000c51010000000081100000000000410200000000051000000000000003000000000610200000048c520200000000c110200000000841020000000080101000000008510000000000061020000000000001000000000610000000000021020000000000006000000008510000000000401000000000000005000000000e10100000000000010000014480202
  | 6, 1 => 0x240412020000000000003000000000000400000000c1102000000080620100000400c520200000000000040000000040102000000000410000000000c110100000000000060000000000008000000000410000000048c5202000000000a101000000000610100000000000030000034441200000000000000500000000801020000000002102000000004010100000000000050000024041201000000008510000000244412000000000048102000000008010200000000c110200000000c110100000000000050000000085100
  | 6, 2 => 0x3440620000000344402010000000000004000000000000000000000061010000000000005000000004110000000324852000000003802201000000000e1000000000081100000000000210100000048802010000000000003000000000000400000000c510200000000c810200000000c910000000410c920000000048c12010000000000002000000000410000000000c51010000004840202000000484120000000000021000000003806200000000000000800000000021000000000002101000000000e1020000000085100
  | 6, 3 => 0x400c52010000000002101000003440220000000420c1201000000004010100000000061010000000081100000000000210100000000c0102000000380220100000000c110100000400c5202000000000e101000000000210200000000c1100000000000000700000104402010000000000005000000000210000000000061010000000041100000000448420200000000000060000000080101000000440620100000000000030000000000000000000000510000000410c1200000000000000400000000021000000000006102
  | 6, 4 => 0xc5100000000000e1010000000000005000000000410200000410c1200000000004110100000048c1200000000000210100000000000040000000006102000000004110200000000c5102000000000000500000324852000000000000008000000004010000000000000040000000000008000000000410100000000061020000000002101000000000410200000000000020000000000002000000000000600000000061020000000085100000000000000300000000c1100000000000000600000000481020000000000008
  | 6, 5 => 0x24002201000000400620200000000021010000000041100000000000e10200000344402000000000000003000000280e200000000000000300000000c41010000003802201000000000210200000000000030000000041101000000440620000000048c52010000000048101000000000610100000000021000000000000005000000000e1000000014402200000000008110000000400c9200000000000a1020000000002101000000000000600000000000030000000005100000000000210100000000021000000000006100
  | 6, 6 => 0xc510000000000000040000034406201000000000000000000000c51000000000006100000000000610100000000000000000000002101000000380a20100000014042010000000000005000000004810100000410c1202000000000a1010000034406201000000000e10200000000000050000000000002000000000000600000000021010000000084101000000004010000000000c51020000000000008000000484020000000000841020000000002100000000004110000000400c920000000000000040000000000002
  | 6, 7 => 0xe101000000008d100000000008010200000000411000000000000005000000000210100000000021020000000040101000000000000700000000c8101000000380a2010000000000005000000000000600000410c92000000000000001000000000a10200000000c1101000000000a10200000000c010100000410c12010000000000004000002444120000000048c520200000000000030000034481200000000484120000000000c510200000000c110000000000c5100000000000000300000000c41020000014002200
  | 6, 8 => 0xc5100000000000510000000000c01010000034406200000000000000200000000061010000000081100000000000610200000000c110100000000c11020000000002102000000000000300000048c5201000000004810100000420c12020000000000005000000000610200000000000070000000002100000000004110000000038062000000000000003000000000000800000000c5100000001044020200000000000000000000000006000000000000600000000c910600000000c110100000000841020000014480202
  | 6, 9 => 0x510000000000021010000000000006000000000000300000000000030000000000004000000000000500000000c110200000000c410200000410c920000000000c1101000000000000000000240402020000000084101000000000000400000000401020000000084101000000000610200000000411000000004841202000000000000600000048842020000000041100000003248520000000000411000000000000004000000000610200000000021000000000002101000000000610200000000000040000004880201
  | 6, 10 => 0x841020000000006100000000280620200000000c810100000000000050000000040101000000140420200000000851000000000000003000000280e2000000000006101000000000e1010000000085100000000000e10100000000000030000000002100000000000a10100000000061020000004406200000000000210000000000000050000000000006000000000210000000048402010000000006100000000000000300000000c910000000048c12000000000006102000000000000600000000c510100000000c1101
  | 6, 11 => 0x2100000000000000300000048402000000000000007000000000610200000000c510200000244412000000000081100000000000000500000000c5102000000488020200000000c910000000000021000000000000003000000000210200000048c12000000000000001000000000a10100000040062020000000006101000000000000200000000021010000000004101000000000000700000000000040000000000006000000000000000000344802020000000040102000000004110200000000021000000000040101
  | 6, 12 => 0x610100000000411010000000006100000000000a100000000000810100000000c1100000000000210000000000401020000000084102000000000410100000000401010000000002100000000380620000000000000050000000000006000000000000100000028062000000000002100000000000000300000000000050000000000002000000000000400000000000050000000000006000000000000300000000c8101000000000410200000000401010000004484201000000440620200000000000050000004406200
  | 6, 13 => 0x610000000000061000000000004100000000000000300000000000040000034484202000000000e10000000000401010000000080101000000000210100000000021000000000002100000000000e1010000000080102000000004110200000000c110700000344022020000000000005000000000000800000000000060000034441202000000000000800000000401020000000000006000000000a100000000000000400000410c920000000240412020000000000000000002400220200000344062000000000000007
  | 6, 14 => 0x10000000000008000000000610200000104402000000034406200000000000610000000000021000000000000001000000000000500000000000020000000006100000000000e102000000000a1000000000041100000000000000400000000c51000000000002102000000000210200000000000050000000041101000000000e10200000000021010000024002202000002100420100000000021000000000002102000000380620000000000801010000000040102000000000000400000000481010000000000005
  | 6, 15 => 0x300000400c5200000000008d10000000344802020000000000002000000000000400000000c11000000000000003000000008510000000000c110100000000000060000000000006000000000410200000000000040000000000001000001044020200000000c510000000000000000000000000003000000000e10100000000c1102000000000000000000048402000000000000003000000008d10000000000c9100000000000610000000000000060000000000004000000000610000000000000000000034440200
  | 6, 16 => 0x610000000000c4101000000000000600000104402010000000000004000000000610000000000000060000000005100000003444020200000000c1100000000000210100000000c510000000000000050000000000004000000008510000000000401010000000004100000000004010200000000411010000000000007000000000210000000000c11020000000006102000002440620000000000000020000004840200000000000000500000240412020000001802200000000000000700000420c120100000420c5202
  | 6, 17 => 0x30000000006102000000000000700000000401030000000000002000000008010100000000000040000034484202000000000000300000000c110000000344402010000000000008000002404020100000000021010000000000007000000000000600000048402020000021004201000000000610200000000000010000000000003000000000000000000104402020000034480201000000000e1000000000000000000000000000600000000021000000000006102000000000000400000000841020000000000007
  | 6, 18 => 0x5000000000000100000144022000000000000004000000000610000000420c520100000000061010000034440200000000000e1010000000000000000000004010200000000000040000000000004000000280220200000000c510200000000000070000000040100000000000000500000000000070000000000000000000000000300000000411000000000000005000000000000300000140022010000000041101000000004110200000000041000000000040100000000000210000000000000060000000002101
  | 6, 19 => 0x21010000000000006000004108120000000000c510000000344402010000000000004000000000e1010000000000002000000000000300000240062020000000041100000000004110100000000000000000000000003000001400220000000000c5102000000000000400000000061000000000000006000000000610000000000041000000004006202000000000210200000000c4101000000000000400000000000060000000008102000000008d100000000380620100000000000080000034440200000000000a101
  | 6, 20 => 0x4000000000210100000000c410100000000000040000000040102000000000000700000000000030000000000005000000008010200000420c520100000000000020000021004202000000000e1010000000000003000000004010000000000c110000000344412020000000006101000000488520000000000000040000000000004000000000a1000000000000004000002404120100000000c910000000234c5200000000380220100000000c51010000000000002000000000000500000000061010000000085100
  | 6, 21 => 0x40102000000000000200000000c0101000000004110100000104402020000000006102000000008d10400000000c11000000034440200000000000000400000000000030000000084101000000000000300000000021000000000000003000000008010100000000c11000000000000004000000000210100000000000030000000000007000000000000000000000411000000000006100000000000000000000000021010000000005100000000000000600000000000030000024041202000000000e1010000000002101
  | 6, 22 => 0x7000000008110000000000c5100000000000610100000000c9100000000000a10200000000000030000000000004000000000a10000000000841020000000006100000000000410200000000000030000000006100000000004010100000000c010100000000000000000000000005000000004110200000000c4101000001400220000000000000050000000000004000000000610000000048412010000000000006000000000210000000400c520000000000021020000002802200000000000a1010000000002101
  | 6, 23 => 0x500000000c9106000000004010000000000021010000000005100000000000210000000000401020000000000005000003440620200000000000060000000000006000000080620000000000c1100000000000610000000140022020000014002200000000000210200000000000080000000000004000000000000300000000000020000000000005000000000210100000000000060000000041100000000000a1000000000004101000000004110000000244c5200000000000610100000000021010000000000003
  | 6, 24 => 0x40101000000008d1040000000002102000000004010000000000000020000034441201000000000000000000000c4102000000004110100000000000040000000000007000000008d100000000000a101000000484120200000028022010000000000001000000008d1000000000006100000000000000500000200402020000000000003000000000a100000000000000800000400c52010000002802201000000000e102000000000000400000000061000000004406201000000000000500000018022010000000000007
  | 6, 25 => 0x20000000040102000002400620100000000061000000000081100000000000000300000048852000000000000000000003440620100000000000010000000000000000000000e10000000000000000000000000001000000008110000000344402000000000000005000000000a100000000000210200000038062010000000000001000000000610100000410812000000010440200000000000000400000000401010000000000008000000000e1010000000081100000000180220000000000021020000000081100
  | 6, 26 => 0x40100000000000a1000000000002100000000000610000000000000080000000041101000000000a10200000000000060000000000004000000000000300000000c1100000000000610000000000000010000000000001000000440620200000000021000000000002100000000000000500000000401020000000000005000000000410000000000c9100000000000000600000000411000000000000006000000000610200000000021020000000002101000000380a20000000000000030000002806201000000000e101
  | 6, 27 => 0x61000000000000003000000000610000000000c1100000000080620000000000000030000000000001000003440220200000000061000000004840201000000004110200000000000040000034441202000000000000600000000000000000000000003000000008510000000000811000000000004101000000000000200000000c9100000000000000400000000041020000000002101000001044020000000104402020000000002101000000000000500000420c1201000000008d10400000000401020000000000005
  | 6, 28 => 0x21000000000000006000003444120000000000c410100000000051000000000004100000000000000300000000411000000000000008000000000000500000000021020000000002100000000000000300000000000060000001802202000000004110000000000000030000000000008000000000e10200000000411020000041081200000000448420100000000c110100000000000030000000000003000000000000300000000c110000000000000000000000000006000000000000200000040062000000000000005
  | 6, 29 => 0x411000000000000004000000008110000000000021000000000000007000000000000100000000c5101000000000000400000000000080000000004100000000000210000000000000010000000000004000000000810100000000c1101000000000000300000000c51010000000000003000000484020200000000061000000000004102000000000000200000144802010000000000004000000000000000000044062010000000006102000000000000300000000000000000000000000000000000000300000000c0101
  | 6, 30 => 0x3444020100000000000050000000005100000000000000000000000811000000010440201000000000610000000044062010000000000003000002444020000000000000060000000000002000000004010000000048802010000000005100000000000000100000000c9100000000000000600000000401010000000000004000000000000500000000000020000034485200000000000000400000000401020000000040102000000000610000000000000030000000000003000000000610000000000000040000000041102
  | 6, 31 => 0x500000000000020000000000004000000000000500000000000070000000000003000000000000700000000061000000000081100000003448520000000000c9100000000000000300000104402000000000000000000000000000400000000051000000000041100000000000e101000000008d1000000000006100000000000000400000000000030000004885200000000000610000000104402020000021004202000000000000400000000411020000000000004000000000000100000000801010000024040202
  | 6, 32 => 0x61000000010440200000001044020000000000021020000000000000000000000a1010000000000006000000000000400000000000000000000000000000000004010000000000c01010000000000004000000000e101000000000000600000234c1200000000000000400000000c81010000000000002000000000000300000000000070000000041101000000000000600000000c410200000000000050000034485200000000000e10000000000401050000000000000000000000000600000000481020000000040102
  | 6, 33 => 0x234c1200000000000a102000000180220100000000000010000000000003000000008110000000000c9100000000008d1040000000002101000000000000400000000000030000000000008000000000210200000000000040000000081100000000000a1000000000041100000001044020200000000841020000000085100000000000210000000000000030000000040100000000004110000000000c9100000000000000300000000411000000010440200000000000610000000000811000000000002102
  | 6, 34 => 0x6100000000000000000000140022010000000040100000000080620200000000c810100000048412010000000000004000000000000000000000041000000000000005000000000a102000000000000400000000c810100000000c9100000000000000400000344402010000000002100000000488d2000000000000000000000484120000000000c910000000000000040000000006100000000000e1020000000041100000000000000500000420c12020000000000004000000000000500000000061000000000004100
  | 6, 35 => 0x600000000c9100000000000000300000000000030000000080101000000000000300000000000030000024040201000000000000700000000041000000000040100000000000000000000000000060000000000004000001044020100000000411020000000000003000000004010200000000411010000000000003000000000000500000000000030000000000004000000008010100000000000030000000000006000000000000400000048c9200000000004010200000000c910000000000c51010000000000004
  | 6, 36 => 0xe101000000000a10000000000000050000001404200000000008d1000000000040100000000000410000000000c9100000000004110000000000000070000010440200000000004010200000104402000000000000008000000000e101000000008d1000000000002100000000004110000000240412010000000002100000000004110000000000061000000000000003000000000000000000000401000000000040100000000000a10000000000c91000000000000006000001044020000000000000050000000000004
  | 6, 37 => 0x4841201000000000000300000000411000000000000005000000004110100000000401000000000004100000000004010100000000c91000000024440200000000004110000000000c910000000048c920000000000401010000000000003000000004110000000000000030000000041100000000004010000000000000000000000000005000000000000000000000000000000000000000000000484120000000000c9100000000000000500000000c410200000048c92000000000041100
  | 7, 0 => 0x60000000000001000000000000200000000000040000000000007000000000610200000000411020000000000000000000000000100000000021010000000000003000000000610100000000411000000000000000000000000210000000000c5102000000004110000000000000010000000000005000000000000300000000c51000000000040102000000000410000000000c1101000000000e10100000000000020000000000002000000000000100000000061020000000000001000000000e1010000000000001
  | 7, 1 => 0x1000000000000200000000c1101000000000000100000000000010000000041101000000000210200000000c510000000000061000000000000004000000000000200000000c5100000000000210000000000000020000000000001000000000a1000000000000000000000000610100000000000000000000000000000000000210000000000061010000000002101000000000000000000000c51000000000000000000000008410100000000000040000000000002000000000210000000000c51010000000085100
  | 7, 2 => 0x20000000000000000000000e10000000000061000000000000002000000000000600000000000020000000006102000000000a1010000000006101000000000a10000000000000000000000000002000000004110200000000000050000000000000000000000000100000000021010000000000006000000000210100000000000000000000040102000000008010100000000411010000000000004000000000000100000000000020000000000001000000004010100000000c110100000000c1102000000000a102
  | 7, 3 => 0xc910000000000000000000000000000000000000000000000000801020000000000002000000000000200000000c91000000000040100000000000000200000000c91000000000000002000000000000100000000000010000000000002000000000610000000000000060000000000005000000000000000000000811000000000000005000000000610000000000000000000000000003000000000000200000000061000000000000000000000000000000000000801020000000000000000000008d100000000000a100
  | 7, 4 => 0x41100000000004110100000000401000000000000000000000004010100000000000000000000000000000000000a1010000000000000000000000e101000000000000600000000000000000000002100000000004110000000000000010000000000000000000004010000000000000030000000000003000000008410200000000000040000000040102000000000000700000000000040000000000000
  | 8, 0 => 0x10000000000000000000000000100000000000020000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_4 roots_4 7 s ws hint
  | 1 => checkCutEntry dom_8 roots_8 7 s ws hint
  | 2 => checkCutEntry dom_9 roots_9 7 s ws hint
  | 3 => checkCutEntry dom_10 roots_10 5 s ws hint
  | 4 => checkCutEntry dom_11 roots_11 5 s ws hint
  | 5 => checkCutEntry dom_12 roots_12 5 s ws hint
  | 6 => checkCutEntry dom_13 roots_13 5 s ws hint
  | 7 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 8 => checkCutEntry dom_16 roots_16 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_17 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_17 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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
theorem z4_24 : ∀ i, 24 ≤ i → i < 28 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 24 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 28 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (z4_24)))
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
theorem z5_112 : ∀ i, 112 ≤ i → i < 118 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 112 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 118 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (z5_112))))))))))))))
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
theorem z6_240 : ∀ i, 240 ≤ i → i < 242 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 240 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 242 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (z6_240))))))))))))))))))))))))))))))
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
theorem z7_72 : ∀ i, 72 ≤ i → i < 76 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 72 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 76 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (z7_72)))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 8 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := range_split z8_0 (z8_8)
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
theorem rootChecked : span RootG 6 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_17 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
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

def dom_18 : Nat := 0xffffffffffffffff
def goal_18 : Nat := 0xeac0e8c0e8c08000
def roots_18 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 11 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaaaaaaaaaa, 14, 15)] (by decide +kernel) (by decide +kernel) low_17

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

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (3938511040 * 2 ^ 32 + 3904929792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_18.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 11 ≤ t :=
  lower_to_circuit6 fG goal_18 11 hT6 (by unfold IsConst; decide) low_18

def wit : Circuit := ⟨[⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [6, 1]⟩, ⟨GateOp.and, [2, 1]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [6, 11]⟩, ⟨GateOp.or, [12, 8]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [14, 10]⟩, ⟨GateOp.and, [13, 15]⟩], 16⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 11 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_12943_aux

theorem PEqualNP.Outside.L_meta_12943 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3938511040 * 2 ^ 32 + 3904929792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3938511040 * 2 ^ 32 + 3904929792) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_12943_aux.wit, PEqualNP.Outside.L_meta_12943_aux.wmono, le_trans PEqualNP.Outside.L_meta_12943_aux.wsize (PEqualNP.Outside.L_meta_12943_aux.lower s hs), PEqualNP.Outside.L_meta_12943_aux.weval⟩
