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

namespace PEqualNP.Outside.L_meta_15341_aux

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

def dom_0 : Nat := 0xffff0000
def goal_0 : Nat := 0xeaa80000
def roots_0 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 25), (18, 19), (20, 21), (22, 23), (22, 30), (24, 25), (26, 27), (26, 30), (28, 29), (28, 30)]
def r1sG : List Nat := [17, 17, 17, 18, 20, 22, 22, 24, 26, 26, 28, 28]
def r2sG : List Nat := [19, 21, 25, 19, 21, 23, 30, 25, 27, 30, 29, 30]
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
  | 3, 0 => 0x8d5c6a423f94f88f202b72e107432cf305c93d22
  | 4, 0 => 0xc3634ca994145e3381df1c4f6f3c17516a2e6bc2202b72e119ec07501375cbc2111eaaac
  | 5, 0 => 0x202b72e1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccc000000000000cc88000000000000cc00000000000000c0c0000000000000aaaa0000000000008888000000000000555500000000000000ff0000
  | 0, 1 => 0xfff0000000000000ffcc000000000000ffaa000000000000ff88000000000000ff00000000000000f0f0000000000000eeee0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xd9534a9634a9734b9734a9824
  | 4, 0, 0 => 0xea9735a97305097304a973250a97140a9734a97435a97315ca9735
  | 5, 0, 0 => 0xa9734
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x368300300060007000ff807f
  | 0, 1 => 0xff0fe8f87f80f80c7036f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xb69b69b40a605bf129a4003b
  | 0, 1 => 0xff6fedffffedfc4e72fff
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_0 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_0 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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

def dom_1 : Nat := 0xf000f000
def goal_1 : Nat := 0xe0008000
def roots_1 : List Nat := [0xa000a000, 0xc000c000, 0xf0000000]

namespace S_1
def pairsG : List (Nat × Nat) := [(13, 15), (13, 29), (14, 15), (14, 30), (28, 29), (28, 30)]
def r1sG : List Nat := [13, 13, 14, 14, 28, 28]
def r2sG : List Nat := [15, 29, 15, 30, 29, 30]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x881487a2
  | 3, 0 => 0x881487a2
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000c000c00000000000a000a000
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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

def dom_2 : Nat := 0xf0f0f0f0
def goal_2 : Nat := 0xe0a08080
def roots_2 : List Nat := [0xa0a0a0a0, 0xc0c0c0c0, 0xf000f000, 0xf0f00000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000, 22, 30)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xff00ff00
def goal_3 : Nat := 0xea008800
def roots_3 : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0xffffffff
def goal_4 : Nat := 0xeaa88888
def roots_4 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_4
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (5, 7), (5, 21), (6, 7), (9, 11), (9, 25), (10, 11), (13, 15), (13, 29), (14, 15), (14, 30), (17, 19), (17, 21), (17, 25), (18, 19), (20, 21), (22, 23), (22, 30), (24, 25), (26, 27), (26, 30), (28, 29), (28, 30)]
def r1sG : List Nat := [1, 2, 5, 5, 6, 9, 9, 10, 13, 13, 14, 14, 17, 17, 17, 18, 20, 22, 22, 24, 26, 26, 28, 28]
def r2sG : List Nat := [3, 3, 7, 21, 7, 11, 25, 11, 15, 29, 15, 30, 19, 21, 25, 19, 21, 23, 30, 25, 27, 30, 29, 30]
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
  | 2, 0 => 0xe2a76056
  | 3, 0 => 0xf9b2eaccd94557d5b6f96528835e63a65c77f97444d245dc
  | 4, 0 => 0xfc47ccedf4b3cebed7e0e6e7d7925bfcb866540aa9597679a45c4ebc74cd4d546d3a4a3a62e4412c5bddd0524a3ffc5a41abf4364111cb1438e382722df686cd2059e1a12010751c19244aae13f398990d5aab730b91c9e50b178bec023bdc95
  | 5, 0 => 0xe917fd05e854acc2d83a9daacef5cf51c0e85040bb95578cac6ae1e0a3e82e78a3d6d9bc9e8aa37996153e6995402eff7cbf7665718e98da64d480335d1295e9526e44fc4ca6240749a5d3384626a7f74111cb143903b34637e9f09c32f633fb2d5135c8262ad7ad24e2e5ac1ac7d7cf18c41cbb14e5b487148cee9c12fe2d5b0ffc86f50de1e4bc049ac070
  | 6, 0 => 0xd051f507c1afdc6dbe3fb924b4992a82a0508cfd7ecfa1835299e96d3a6b8d4125303d37126b25b7
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3f3f3f3f0000000033333333000000003030303000000000222222220000000011111111000000000fff0fff000000000f0f0f0f0000000000ff00ff
  | 0, 1 => 0x77777777000000007777000000000000707070700000000055ff55ff00000000555555550000000050f050f000000000505050500000000044444444
  | 0, 2 => 0xc000c00000000000bbbbbbbb00000000aaaaaaaa00000000aa00aa0000000000a0a0a0a000000000a000a00000000000888888880000000088008800
  | 0, 3 => 0xe0e0e0e000000000e0e0000000000000e0a0e0a000000000dddddddd00000000cccccccc00000000cc00cc0000000000c888c88800000000c0c0c0c0
  | 0, 4 => 0xeecceecc00000000eeaaeeaa00000000eeaa000000000000ee00ee0000000000ee00000000000000ecececec00000000eaeaeaea00000000eaea0000
  | 0, 5 => 0xfaf0000000000000faaafaaa00000000faaa000000000000f8f8f8f800000000f0f0f0f000000000f000f00000000000eeeeeeee00000000eeee0000
  | 0, 6 => 0xffff000000000000ffa0ffa000000000ff88ff8800000000ff00ff0000000000fcccfccc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x237913
  | 3, 0, 0 => 0xd247d14caba114ae88d14c6b8114c687d148de6d54
  | 4, 0, 0 => 0xd31a5f4574c616d35d247db5571ae9a115031ae84534ae46d55ae891b5574c5b54a5c6f6d55174c5d6d55ae88db5574c626155d31ae64571ae56d55d31b294571ae86d15
  | 4, 0, 1 => 0xd32b1b5571adb54e5c6dadb5571ae85515d31ad95574c5b54d5d31b9b4d74ae45515
  | 5, 0, 0 => 0xd31ada5516034ae46d55d31c2b6d56d32adb55160346d50405d31adb5426d31adb5486d31adb5506034adb2c05d31adc6d56d31ae76d56d31adb5496d31ae96d16d316d85536d31adb54c6d31adb5476
  | 5, 0, 1 => 0xd31adb54f6d31a9b5536d31adb5d56c6ba686d56d31adb5436031ae86d55d31bab6d56d31adb5456d31adb5956d33adb5536d31adf6d56034c551815d31ae16d56034c6ba515034c6b2c65d2ba646d56
  | 5, 0, 2 => 0xd31adb5446d31ae95516d31adb5526
  | 6, 0, 0 => 0xd31adb54b6d31adb5546034c6b5465d31ae96d56d31adb5516d31adb5466034c5b5415034c6b6cb5d31aea6d56d31adb6956
  | 7, 0, 0 => 0x34c6b6d55
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
  | 0, 0 => 0xf9f3efc9736dc1030c00736dc900003ff0ff38f0e307f01f
  | 0, 1 => 0xfffffffff000c70f1cfffc9fff8c92c70c1cc70c10368c92
  | 0, 2 => 0xc00c9736d00736d00036000030c000300000000000000
  | 0, 3 => 0x60f1c060000000f0cff8c92368c92300c80000c00060c10
  | 0, 4 => 0x368ff2307fed307000300fe0300000368f9e067f7d067000
  | 0, 5 => 0xc70000c07f6dc07000c70f1cc70f1cc00f0036ffff36f000
  | 0, 6 => 0xfff000f80fecf80fe0f80fe0f68f92
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x59f2eb4962484122084962480000001bf0ff18d0e303b01f
  | 0, 1 => 0xed6a48ed6a48e52a08a7b81fa40800a7281ca40800a40800
  | 0, 2 => 0xa40d005bf7ff5bf7ff5847e043271c4007001295b71005a0
  | 0, 3 => 0xe72f1ce72a08e72f1cb69db7b69db7b40da0b69db7a60d14
  | 0, 4 => 0xfedff7fffffffffa48fc4fe0fc4a40f7bfbffffffffffa48
  | 0, 5 => 0xff6a48fffffffffa48f7bfbfe72f1ce40f00fffffffffa48
  | 0, 6 => 0xfffa48ff6ffcfedff7fc4fe0f69fb7
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 24 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 24 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 53 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 53 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 53 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 53 then wireAt i else 0
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
  | 3, 0 => 0xf153617b7a33b422343b29b010cdf458
  | 4, 0 => 0xf48264fdd777b0eab07c00edac05225e9820e22384a9f6726c5dd27d5c132aed53cbd26e4d436bee369c381e25e0cf66218257c4215293501d34fcbf19b036a0104713d20e562d7c08884c8504b79bb9
  | 5, 0 => 0xfb15c6cefa4bc7a9f853f986ee32c418e5eacd86e0bddffad8a46edcd75027cad0af7d7cd051f507be9c3955b9d3a5c5b5aa084fb3b18537ac05225ea9f572eea8a24dcda76ef1c19f4f7b3f9b7060519812ced29208691081ea162e7f88ab437ecfa1837bd1354c700151036fa1aa3c6d2f1cb26baa58136b778c4269e2a59569bef96960186ac75e1d4aa8553f160d537bfbe74bcfcd42439e85fd4279fe8d410f07923649f21e361753d6321d42c22a4ee1c829ed978a2637312d2616908a1fc3b4311072b8430f6bda8c0c1ef63c0ad7cab808dabbe6067329db018df46b
  | 6, 0 => 0xe40c141be0bddfface00c9b9c5159104ba7741d8ac05225e7702c5a9578462a3554c825e30706e42276bea43206585ea1b8a7ef10241d3e1
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x41081201104402003408120234081201
  | 4, 0 => 0x8410100081101000811010000000010440200240412000000000110440200000841023444020000000002000000010000000034041200000000010000000210440200000000000000000200000002
  | 5, 0 => 0x610000002100000c410000006100000c01000000a100000000020000000200006100000411000000000100000002000021000004010000000002000000020000000000000002000000010008410000006100000000020000000100000000000841000000a100000000010000000000000002000000010008010000000001
  | 5, 1 => 0x4010000041100000c810000040100000021000000e1000000000000006100000c810000002100000000010000a1000000000000040100000000000004010000000000000000020000210000000001000000000000000000000002000c0100
  | 6, 0 => 0x100000002000000000000000000000000000000000000000000000000000000000000000200000000000000010000000000000000
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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

def dom_5 : Nat := 0xffff0000ffff0000
def goal_5 : Nat := 0xeaaa0000eaa80000
def roots_5 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffff000000000000, 17, 49)] (by decide +kernel) (by decide +kernel) low_0

def dom_6 : Nat := 0xf000f000f000f000
def goal_6 : Nat := 0xe000c000e0008000
def roots_6 : List Nat := [0xa000a000a000a000, 0xc000c000c000c000, 0xf0000000f0000000, 0xf000f00000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000, 14, 46)] (by decide +kernel) (by decide +kernel) low_1

def dom_7 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_7 : Nat := 0xe0a0c080e0a08080
def roots_7 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f000, 22, 30)] (by decide +kernel) (by decide +kernel) low_6

def dom_8 : Nat := 0xff00ff00ff00ff00
def goal_8 : Nat := 0xea00c800ea008800
def roots_8 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 6 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

def dom_9 : Nat := 0xf0f0f0f000000000
def goal_9 : Nat := 0xe0a0c08000000000
def roots_9 : List Nat := [0xa0a0a0a000000000, 0xc0c0c0c000000000, 0xf000f00000000000, 0xf0f0000000000000]

namespace S_9
def pairsG : List (Nat × Nat) := [(37, 39), (37, 53), (38, 39), (38, 46), (44, 46), (45, 47), (45, 61), (52, 53), (54, 55), (54, 62), (60, 61), (60, 62)]
def r1sG : List Nat := [37, 37, 38, 38, 44, 45, 45, 52, 54, 54, 60, 60]
def r2sG : List Nat := [39, 53, 39, 46, 46, 47, 61, 53, 55, 62, 61, 62]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_9.map (· &&& dom_9)
def goalM : Nat := goal_9 &&& dom_9
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe25a8f37
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000f000f00000000000c0c0c0c000000000a0a0a0a000000000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_9 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_9 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_9 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_9 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_9 roots_9 goal_9 4 := by
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

theorem low_9 : Lower dom_9 roots_9 goal_9 4 := S_9.noCircuit

def dom_10 : Nat := 0xffffffff00000000
def goal_10 : Nat := 0xeaaac88800000000
def roots_10 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f000000000, 42, 46)] (by decide +kernel) (by decide +kernel) low_9

def dom_11 : Nat := 0xffffffffffffffff
def goal_11 : Nat := 0xeaaac888eaa88888
def roots_11 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_11
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (5, 7), (5, 21), (6, 7), (9, 11), (9, 25), (10, 11), (13, 15), (13, 29), (14, 15), (14, 30), (14, 46), (17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (20, 21), (22, 23), (22, 30), (24, 25), (26, 27), (26, 30), (28, 29), (28, 30), (33, 35), (33, 49), (34, 35), (37, 39), (37, 53), (38, 39), (38, 46), (41, 43), (41, 57), (42, 43), (42, 46), (44, 46), (45, 47), (45, 61), (48, 49), (50, 51), (52, 53), (54, 55), (54, 62), (56, 57), (58, 59), (58, 62), (60, 61), (60, 62)]
def r1sG : List Nat := [1, 2, 5, 5, 6, 9, 9, 10, 13, 13, 14, 14, 14, 17, 17, 17, 17, 18, 20, 22, 22, 24, 26, 26, 28, 28, 33, 33, 34, 37, 37, 38, 38, 41, 41, 42, 42, 44, 45, 45, 48, 50, 52, 54, 54, 56, 58, 58, 60, 60]
def r2sG : List Nat := [3, 3, 7, 21, 7, 11, 25, 11, 15, 29, 15, 30, 46, 19, 21, 25, 49, 19, 21, 23, 30, 25, 27, 30, 29, 30, 35, 49, 35, 39, 53, 39, 46, 43, 57, 43, 46, 46, 47, 61, 49, 51, 53, 55, 62, 57, 59, 62, 61, 62]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_11.map (· &&& dom_11)
def goalM : Nat := goal_11 &&& dom_11
def NN : Nat → Nat
  | 3 => 6
  | 4 => 81
  | 5 => 519
  | 6 => 843
  | 7 => 295
  | 8 => 18
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe47005e1b85dd54f90f46b086203bc595c93669e58e02be2
  | 4, 0 => 0xa2239b93a1f704569e229fb29b429828999bb85594fe021a8d2638b284ce2fe782b50a537f32762b7d1dd34f73b4c9d57349b9c4711a003e6f3d0f106d3d18e46c599f6266fc267065dffa1b6489b67263c3399b62dfb13062ad445160d1f253602499465778d9584e26bba44cddb98a4ac4de354aa5645a4aa06c9a4a1270b747ff9d49463a1fb744e50bc53b78bc5c3b4ab500370984dc35f10f5131f970fe2f18a0822b66a8c62b3ec3532ac5f93a2a836999252b925423f9baf3226ea3621f302e7e1efa8c671e5381311e3e5a1e1ddbfd671dafb5c11c736a0c1b2b5c1519b4e942167bb7c91111c90010271b050ef0709d0cc252a50abd93bf06fb831d
  | 4, 1 => 0xf58a0d23efe89191e78e2c34e408e5c6d899fd4cd677a7ded50c8fd0c7a6272fc4a04b1ac1582ac7be9f647ebb24a338baaa45b8b9d0c8b7acb49b33a9213d0fa3d1d397
  | 5, 0 => 0x1433c99a140ae8b1139a195a12ff48d912fc993212e6d7c012dc22d312995651122898fc119dfe10107fce3c106a2aa910497aa20fe749af0e55716a0d88c2480d534ed20d1bca3e0d1388000d0073760ce06d960c6923780c4710080c12dc4e0ba421e10b7fcbcd0b73023b0b6be2620b3ec3760b13235e0afe05870aee62910a6170fe0a2af1a40950c9ef0947c16b0900418408ea0cab086c60f1080764f207e5f6d8072c671c064bab26062b136d0626ca58061f91cb05f4036505048e7704afd03a046b7eec046236b50416c31803f4ac2a03e9563303a24a60034b623b0283531601ed20180141351e013b1ae200e2288800904a5100276a460025d314
  | 5, 1 => 0x2d409beb2d2b50ac2cf0bc342cdc369c2b3cf8522afde7e92a080cbe28b61d20285b57bf28058bd3278464572700849c261746b4253d50a624945bd1248ba27c244135fd24030d0d23e7f03023c709ff2379f29f23698f052343055d2325167e22cc4ae822c4e84a22afbece22a52b7c2286900321d9150021668d1f21574b44214d753d21298448212356cd20ac592c206d0bcf2061481e2049c7fb2049bc481fd723ee1f9c98751f365ab61eee48821e5b93861e56495d1e35b92a1d6032921d4df85b1ca5d5401bebad481bd100791a10f6e519820e5917d4f22c1763c8e21702d2d716dea19916710e07166063f115dac5e915d259ae14c9349a14c287d1
  | 5, 2 => 0x44497ae743a94b4442ecbb3d429c3f0e422eb483422cec3641dc04534119ddbc4107b4dd40c567154053ccc13fd14ec33f8a08203dd89af53d92b7b53d8f5f5d3d20e24e3c0aed043be5e98e3b932d743b8cc8883b8652763b52acf83a6e9a8f3a6417223a5522ce3a3fe3c339c5c125393e58ee3885138538505600381f795b37f9855b37c18a16368498b1365185cc36497f61363099583624a4d6360ac24835dd6809358ad89434a536a73465a4f1343264da33b355d13339ebb332db8cba32b38ed8329000d332321bee31ea42e231a837f53168dd79315db1f1311672873107ca492efd25b42ed4161b2eb38dc92e90bff52e43f23f2e212fbc2d8de92d
  | 5, 3 => 0x579b9d36557046f6553ddd4e5500170054e764eb543abce152fc346152b3fe7752add8db523c23f952062045519ffb9950d766ba50d02a0e508b29e85035ea78501d9f5d501d2ed7500307f24fd457ba4fd099414fd038964fa487734f7c60744f2a29f34efbc95a4ee852904edbe69c4e89edde4d7c05aa4d74a6104d23282d4d1272884d11c68b4d0592df4c56afea4bdb7b304bc7d61e4bc38b784b87b2694b81a28f4b6a6c614b24895f4b246af94aef0ffe4adbba2b4ad60f734a91db544a4b1c5a49e903f149499ae649482969492cc4d1489ab7c347f63ed647e36a7847b4abff475e6c0e45b50254457f164345310e04450a855e45063b0d447eeee8
  | 5, 4 => 0x74f947067479b118732cd8d972b21ef0722b9b8a716c87776ecb5e0c6e23ca026d82caf46d38cdb46cd0620d6c8a1ff86bf743676bcf90f36b0981336aef90ef6a702d6469f9c1f16919a65868f282c568b8d133688ea6bc685791566853286567483fa2663dcbdf6561044c6525730f650bfc25649bbfe364014a2463f5bffd637c8f42632407c262d2be1162c3e288627701ec620f27bf620b79df61d7af8061bd5fe1618603275fc1bf8f5f9775545f8f5efc5e2d8aab5e1f702b5db5bfba5d990bee5d09c4c35ca970d15c00ae415b8613975aa8a6b95a344c0b5a08fe285a06f3165901c7ff58cf7f79589bb110584e78e457e9f62757e3d55457ac2122
  | 5, 5 => 0x8aedaab78ada770a8acdfd2a8a96bc408a00162a898ee94087a2718586bd3941861243e685e4f0b585d4451d858e6d0d8576a6048549ae5b84a18e0e847dc7148477f149843fbd9583ed8e148387b9dd835af91482dc22e982b1f70a82abe74282a7ea0e81f9441481cd1add81b53369805f6c4f8052da2a804a1f5b802135607fb807ca7f1a51607eb648017e579aa17e373f027e34a38b7df8983f7d969eb77d2f7c4a7ce4b67e7c9c1abb7c306b6d7c14337a7c0fa8837bd6bb247bb9d4ba79f38a0c79e6d45179d7acfb79c57db779a0e703799337ae794a3ff077e8accb77a7a78d7789cc7c767c5d427672126f760f6cfb7577e69975150714750d5444
  | 5, 6 => 0xb2268db4b0f6692eb0a05b50b091393bafd55091adf83960ad0bf2cdad04e533ac879ab7ac1f1206abdc8a8dab05838ba83e40e6a83cd88ba6db69e1a5a254caa5543e16a5412c5fa521a125a4e71114a49bf773a453ca85a40ff91ea3d51455a35c9dd6a247a747a1d941a4a0abb8cb9fa732239f7f4b169ed6cc0e9e18e01d9dfdf3cd9d8c3d109cdccb949c382fb69be530079b09f1a29979b08a98cdc7fe983c3eaf983465cb95f6cf7b955532ce9510a09f94a0f6b59420cb5f93d2d17c939a9e61925ff84a9224092091a1cc4690746405904bab759025d46f8fdc10c48f7111e18f33bf628f265ce38e72841b8d1a81c78cdbd0dc8c7eb4e58b28c966
  | 5, 7 => 0xf1d8600ef1b9111ef0c5b533eb1b78e9eafcb607eaa1d166e89f1d3be7c9aae8e78a4674e6a78be8e408e5c6e3a0d4f4e3550cfee32a55c2e2e81b9ae08873f5e03629dddff65054ddd3ac13dd992c0ddd8f3560dc12332bdb8c9188daf4ccc9da1e842cd979a3f9d8c07109d8a61c5ed85628d4d821173dd80b7990d782a9f3d5d9b825d4a3e2c7d4434fb2d33e275fd3307e4bd279eabad0c88e6cd00bf48acb5d4866cab6f4f1c9ea5b57c945fe97c87da9afc80bd7c9c7cc907dc7a9a723c1663267c0ebd4e7be09ba63bd1a038fbcee6080bbbadbcfbba6b133bafce32eba5eeba5b942f32eb6f1b0a2b4f4d751b4d4214cb46b266bb2d8cbf9b25a64dc
  | 5, 8 => 0xfd18a49ffa13f115f8028b6df7f1552bf59225eef37019b2f24b67a9
  | 6, 0 => 0xd377cd70d3762fc0d0b45210ce551400cc693a50cba81470c7d9f2b0c3734200bc252a20b7002330b5bd3a60b29023d0b19047e0ae653d70a6572fc09fb12fd09eac84a09c0e32809b8a79109a638da093e7356092d20e8091999780903dbc508fadadf08d01fc9088078d60856ca26083fa81e07a19af2078c60020787d7a507492140073e300206f6a3d80681af190665d8580665520c0659646506457cb9060f596e05fc8ebd0562a0ac055afcf4054dd0e6050dc1e804ed297a04c5847804bca65904963a7b0479bbe104360c7703f8e99a03b5fb4002fa793702867f1c0285087d024ad8f901f00f2c0195ffdc015842e800b2dc97008dd725002e9cb3
  | 6, 1 => 0x18dfe56918734073186cfbda18612faf18545dd61852c22b18043d6917bba651176c9a26176aac0017617b9e173643a816b01e541698d4041655fe6815fc5b6615b18426158c470e1587591d1575dcf9155ed0bb15423b41150f2c6414b6e975146bdca813fe9497139b02df139302bf13728f5613604859130a5a891305f52212cd450012ae5da3123c1c3b121b1123118d0e1d11880f96116a87581144e41f113ec3a4109d1e43108ef5b9101f34a20fec104b0fe033430fa2a5570f976fc60f92e2980f8009980f21afa70f1c66040f15f96a0eff00d20ef737100ec4f4730e96d1cc0e2c4ae30e065f720e0550e70dfec5070db753420d9a92370d6e8d17
  | 6, 2 => 0x28e1d56327f9aa2127f28eca27a497ea2750b4f626f0b50c26a8a45026339d462616b60025f85c3825e030e425dc2a28259284602566dfcd2522e8d623ff3ca523e8c56e23e6582623d675a923cebc7823b6748b23aa74da22d2ddb122afbece229eb02f219634db21901609214f0d1120c6f22620bc14c1206a118a206969b8204a72202014c6442009a42c1ffd86e11f9547f51f129f391e63e3c01e62464a1e35b7f71e2acf241dbe4d991d4df85b1d07cbc61c96ea491c397d011bf0c1dd1bee157b1bcc3d7d1ba9084a1b55df541ac6e6c71a21fbf41a1f1cf019eea4ba19ba301a19b009fd1975091c19749e0d194d51da1921237f18eb577118e16a7f
  | 6, 3 => 0x356b27a535239d6d350d0fa434ecd7be3481847a344f47aa34064f6c33df688433da662c33d25e6233b6403a33b3f658339db8dd338e027c3380f3e4336a01d2335d81953359cc58333d305e3326d91332fa2f95325c5248324a6b873228b42331752de73157bf6e3156fc5331357ac630ba24d8306cb522304b4ca93012b9612fbf35272f969e972f311afe2f2d39052ede35262eba05a82e45ee3b2e450d9e2e2eb6002de6358a2d8de92d2d627bcd2d52d1502d04572b2cf8cd042c91587f2c4642572c42325c2bb2627d2baf6f8f2b8202f02b25f1c52b09ceab2afda44c2afd8c522a42385829c7962029c478db29a6739a293f76f02934275729025cbe
  | 6, 4 => 0x412c1b3840ef423c40c11d8e40810b2f4071490e405c6ec8402754cd3ffc41a43ff4ef3e3feafc213f8bb6273f7f6a493f14ef783f0151163e79bb8a3e69a4d83e0713153dd26d833db4e4813d8f5f5d3d8a3cae3cff2e683c6b322a3c61cde53c346cd83c27f8ae3c229a643b7b8ba93b754d643ae086193acf7d883ab0d7363aace7f43aab48ca3a822ece3a8122023a5b119139ffcc7c395f2ed0392f38243929da4e39200c0d38f51e0738eec90038c86292386b233a38422411382963983803b6ee37962c633766c8503729e7e33710072a3703f24536cb597836b5383e36816bd03681559c361d50e735f2a55735efb05d35cf8632358ad894357f7388
  | 6, 5 => 0x500139404faafd564f9834ad4f7141a24f29237a4f08c8964ee3916b4ed752244ebf453b4e89edde4dc2d7694d9bad584d74a6104d5001c34d11c68b4cc656324cad82f14c8a818c4c1e35cd4c07671d4bae4c0d4b24895f4abffef04abd1d0b4aa4d41c49d9a14a49c7418d49c2c56749c0fcf449b6983f49ab509c4905a446490384d34824b16847ee69e8479508b647883d4b47154d3e470bc80346ee463d46ed067a46ba812f46af8fd84608747345b7253845a7f598459774c2451ed66944fe769744e5077444ae84d9449785304490ec0c447cb9f8446729e64408d567437c154542ecbb3d426720864250d60941ec4f6f417adc044170ec6e416abf89
  | 6, 6 => 0x5f6139d15f411ea25f35ba935e82f8175e5e95475e13ada65ddb6fc75d994f8a5d8bf1475ce86af15ce5500a5cb55e505c97debb5c8357335c098ff55bf13ab45bde0aeb5bb03c075b3eec9d5b3bed485ad883ea59f6336d59efad2e59a0445d59254669588269ee58761ced582969ea5813f0b4579b9d36576aac015711b93d5701c18f56ff19ed56a94294567d130c56569ab456488c3a56425f3155f9c36e55f6748055f5a32a5530a86c54fdc76d54fb57fa54f251df54bf317c54b5735e54a96c095479ade65464d08f5461485353cb53405377f3e6534934bd53447d0452e38bef51c09e33517e9cbd5139dea7510a33e250890b34506c7ad0500307f2
  | 6, 7 => 0x71c867877193d4b170d8574c708b912d7041bbc2703b7bb46fbd701e6f43e1be6e8379536e5a9f856df33b5f6dc2375d6db3cd8b6d18b8176c66f60c6c5bf97a6bcf90f36bc67ad66b8993dd6b1c765d6aefcfd96a95be0b6a258de66a08291469a9dbb868715d01682b8c5b68240a4467c6dab467c080b767be1d3b67b115c867852479677d84d866e9390a6644c8f8662eccee661f8dfe658155c96557fc26654872a765438d01653364ff650bdfd764ef4f5b647899486478967363fb6a7f63939f336351f12b6330b2ce62da87e16235df0f62261eff61f617a361874d90618127b3617d3f4b616fe8b4613f4bb661381f9760e52e4160617b6c60205a02
  | 6, 8 => 0x8295aa1e824504b081f6d6c281e62af881b76e8e819be9998182bb738154339f8069eaef806266ad804787517fdefe227fd2c9987fa89f6e7f8ef2d87f82bf8b7f4ff8037f24c13b7e3ea0f47e0c74cf7db173387d9a49677d7b98ea7d334cc57cea112d7c69c65e7c2f9e497b4332737afb729a7abeb30b7a8392537a13568c79e555047961f727791917a87911f99d790b452278e6cebf78a46f127893519d785ee258780479c977e8b9bb77dfa17577abf413779785bb778f984b7730263a7723c8d0770164c976c2010e76b57f7c7679496f765bdd3274f8ca7a74cf39e47433e09b740872447369c766734fd69572f47114727718da7236e2657218e0f5
  | 6, 9 => 0x94a203b794a0b6d393f0934d939a9e6193886129934a18bd93104a2b92efcbe392cd311e9231308291d475fb915bff5890e225fa90578f388fe77d2d8fd5443a8ee20b498e3f8c778e25b3d38e2526e78e183c1b8e01c6188dda0ddc8dd9a8ed8dd7584d8ccb4d078c3f36198bf69a1e8b4fe1e38b4da15b8adfa09e8ab20f158a693f6e8a29179989eee1ee8974814d894068d889047c68887ddfc287be0786878be23f874d6699871506e98703169686fbbef286bd3941864f591485f6241e85e02341858e52b8857183e9854dfbe28527bd3a84bde8d684a7b472849e475c846b9cfe8436e17f84064fcd83c0be09833df903831ab88982de711782c4fa70
  | 6, 10 => 0xab8bcb77ab12b296a9681578a943d136a926c0faa89be350a84782efa840633ca7470e27a732a1a6a72e629ca65ef21ea602287da4ed51b6a453ca85a3cde0e8a3219133a2d05d47a296a4d8a1f9723ea1c37e10a1904c10a1558ee5a0f696e5a06f7c80a008f5839f6676b19f2e8bc29f281e6a9ef41ebc9ec9ae489dc197aa9d99351f9d72dd149d465cb99c3b434d9b6cf8b59b430ccd9b0c849e9a4ad2999a24c22a99e98606997374ef99440663990f01919900ed78986d00ac985e9e289848610497a53cfb97a00225974aa2a796f902c9964c30c0964c0933960bb76c95d27d4095a7bcd395872ae69551aacc954bc9dd9520bde994d7782194b8834e
  | 6, 11 => 0xc9bdabcac9a3b4fac89efc22c7d402f1c73369bbc731841fc720b32ac6d0b208c63ef557c5b0f683c5736c6ac48fe98ec44cc871c3aeb668c13e825dc121cba0c0d8bcdac01a4c7abeefdc2cbedf3b8dbec74491be3add0dbe3232c1be269a7bbd8be129bcb2b5b1bc87fe75bc545819ba231cbbb9d0b111b9885577b91d4ce9b7dce78eb77b91b6b751909cb66e795fb66235d3b6251136b5406affb4f63ecdb432738eb3e10419b325de37b2d74cacb2b3aebab2227074b1f9e3e0b0d5dbb4b09debbbb052e84bb03615abaee89f20ae018b7aadbae7b2ad58a5d0ad148ffdad0bf2cdacfa5f20aca9b064ac25a728abd7936dabd5fcedabd053b4abb5d1f0
  | 6, 12 => 0xf44935f4f3c06a7bf31deba9f1d7f84cf0f8df95f0886534f0369adaee02495bed2b5e9ded2ae9e7ec39cb86ec338729ebc7f551ebc0c7caeafba6c3e82ca1a0e65393cae56c6f69e4dd38a3e2f6af66e2e44efbe247b55ee0675ff1dff3a4ccdfd68d84df1659addec1b6bddddb30c3ddb7dd18dd36d6a1dc8a5345dbc5236bdb7eec9cdaa10b17d9eccea3d97fc822d8c3f1bfd84bd8e7d7783301d76d9a26d70a1d9bd6de8f0bd53d3f77d445852fd3a84f1fd2e4589cd29440d5d26e2c13d1ffa714d1296545d0f6d7dfd028b587cf1f3ed4cefdaf14ceefcea1ceafa34acdcd35ebcd78f521cd19d01fcc9b4d7fcc98d68acc7a0e9ecc5be40acbd4b795
  | 6, 13 => 0xfaeaf5bdfaea169efaab44fcfa4ce404f9495e50f82f3da8f7a45692f71b05e1f6e5cf63f6334be5f503eb5a
  | 7, 0 => 0x2fa1c82a2d90db782bdd94e82b81626d2a73350a2a6cf07129c478db2964176b28a4a83e284db2db2838c79a275958f22705880d25eb7b52258a6ea42429651522ea3ac022521a04223682592219ec0a204aaf2d2014c6441ca0b1831b61a0cd1b52f3321b2d157f1b1e87e21b1036f419f08aad19deb3e219b1d448198eb565196672e1192a0dd619169d33175a929b170db67f12ae5da311eb7ccf0fd4c3f50f3badb20e8414b20e7dd0190d9cbe430d9a92370cf91d9f0cc7aa850c22507d0bb2ffb10acf09dd0ab0afbb0a71f956089ab0f307bd347d06b07a0306291d83061ab28605c61dd605a3eb0a058ce34a04d0acec0291d00a01a603fb01283a17
  | 7, 1 => 0x5342fdb7531915d1523dc21151e81d5151099cc650c4b4ed500139404fb2394c4f9b055d4f943bc44f0fba7a4e2ce2974de254b54dc27b5b4d1acf0f4ca60af44c1e35cd4bff26be4b7591cb49e125c649d602e8499b08ca48b0ac9d46ba5dbb4609964845f6b58445c07cca457c5ed143b42571433f660a430588364214fad141d622d3410d769640db2d8b4079af633ffca0873f49363a3ee6de3d3d6d0b963d0124c93c21f90f3bd0b7833b23954e3a8b9b2139500340387c221637a1ed1c36c744ae36b6da92359f67e7354bc4fd3481847a34746a9f33d93c6b33ab0d08339be83032e64fc532ba82ac326a06213264f1943055c0a6302ca7772fbf18df
  | 7, 2 => 0x867726a184e9742a83c5bc52833df90383233d80830766bf828511a4806266ad7fb9fc427db173387d7d57bc7d776c2f7d303bbe7c439fcf7bf0d3337a70b12879e15a28791d9b417733bc5376db0b2e76bdf4b973f60c3a70ffce1070b1e1016f69601f6e834bca6e38e6f66d483b2f6c4b6e046c3d1b7e6bcf90f36b89f08a6ababa2c69c031bf69b2eaed692e70ee683fb3fc679d352a6733942566fb4c9164f38968647899486379a67663669d956347643b6336351163353df462a97e1361f427ee61aa33685d6275f45d1e66bc5c9fbd605bff541c5aa8a6b95a7078f859e533015923c1c65905159656dbe56f567ee6cd5640306855ab6c4654b47b98
  | 7, 3 => 0xbf8705ebbd2744b8bcc8e334bc545819bab08b31baa8a17cba88bda4b84d21e0b837fe7bb3feb3cab253eee6b12375bdb108215ab0e1dcffb080f6ebae064aa9ada32de2abe5308aabbe6e52aa8df529aa87c3f1aa21bb6da98c5b5da840633ca80d4bfda8098f40a6910249a5d7b751a4a02823a494c22fa3f2435da302d5f5a1662bafa0c045e2a07b3991a00d2aa29eab30d29b71391a9b1dd7b09a36658d99ed5e8797a4f38794b8834e93f42b8d939a9e6193602c469351acbb92a6c20191bec62690061e318f7fd14d8f78512d8e7679718d92f6958d5eaaf98c8386ea8aef68758a81f0ca89beef4c8968a0cb8934bc8a88ede028887e449e877910e2
  | 7, 4 => 0xffcceadcfcf8d17ffce2758bf9b99d75f9acd0faf7e68aa8f6e94291f22186e7f0f10dbef053c1fdefdfd1c7ee22ff53ec164c1eeaf7dac4ea555bf2e8b03ee3e73f702ce7283c3de4625a30e1283faadfb32b5bd9eccea3d986de71d96359b3d87f9952d697c1d4d56748abd2f75b26d27a66b2d0a7e5c1cf84bc20cf6e15b1ceeb1ad8cd6ebd58c8d8951dc69a5462c398766ec31b6fd9c1c5a5be
  | 8, 0 => 0xc2afde01b6be76349b34b1217e1a8a567cea112d76f0de33764e5f61705b5d9f5fbac6fd5cde0cce4f8c57c234064f6c2efbd9641b78d4bc1561a43a1142fa410e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaaaa00aaaaaa0033ffff0033ffff000fffff000fffff0000ffff0000ffff00000000777777770000000055ff55ff000000003333ffff000000000f0fffff
  | 0, 1 => 0x5ff05ff05ff05ff05550555055505550505ffff0505ffff05055555050555550333033303330333030333330303333300ffffff00ffffff00ff00ff00ff00ff
  | 0, 2 => 0xf5f0f5f0f5f0f5f0f3f0f3f0f3f0f3f0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f00ff000f00ff000ccc0ccc0ccc0ccc0c0ccccc0c0ccccc0aaa0aaa0aaa0aaa
  | 0, 3 => 0x11113333111133331111111111111111111100001111000011001100110011000fffffff0fffffff0fff0fff0fff0fff0fff00000fff00000ff00ff00ff00ff0
  | 0, 4 => 0x222200002222000022002200220022001f1f1f1f1f1f1f1f11ff11ff11ff11ff115511551155115511331133113311331111ffff1111ffff1111555511115555
  | 0, 5 => 0x3300000033000000323232323232323230f030f030f030f03030303030303030300030003000300022aa22aa22aa22aa2222aaaa2222aaaa2222222222222222
  | 0, 6 => 0x333f333f333f333f3333ffff3333ffff33333333333333333333000033330000333033303330333033223322332233223300ff003300ff003300330033003300
  | 0, 7 => 0x3fff3fff3fff3fff3f3fffff3f3fffff3f3f3f3f3f3f3f3f3c3c3c3c3c3c3c3c373737373737373733ff000033ff000033cc33cc33cc33cc3377337733773377
  | 0, 8 => 0x5050000050500000500050005000500044cccccc44cccccc44cc44cc44cc44cc4444cccc4444cccc444444444444444444440000444400004400440044004400
  | 0, 9 => 0x5555000055550000555055505550555055445544554455445500ff005500ff00550055005500550050f050f050f050f050705070507050705050505050505050
  | 0, 10 => 0x5a5a5a5a5a5a5a5a55ffffff55ffffff55ff55ff55ff55ff55ff000055ff00005577557755775577555f555f555f555f5555ffff5555ffff5555555555555555
  | 0, 11 => 0x770077007700770070f070f070f070f0707070707070707066666666666666665fff5fff5fff5fff5f5f5f5f5f5f5f5f5f00ff005f00ff005f005f005f005f00
  | 0, 12 => 0x808000008080000080008000800080007f7f7f7f7f7f7f7f77ff000077ff00007777ffff7777ffff777777777777777777770000777700007700ff007700ff00
  | 0, 13 => 0x8a8a8a8a8a8a8a8a88cc88cc88cc88cc8888ffff8888ffff88888888888888888888000088880000888088808880888088008800880088008080808080808080
  | 0, 14 => 0xa0ffa0ffa0ffa0ffa0a0a0a0a0a0a0a0a0a00000a0a00000a080a080a080a080a000a000a000a000a0000000a000000099999999999999998f8f8f8f8f8f8f8f
  | 0, 15 => 0xaaa00000aaa00000aa88aa88aa88aa88aa880000aa880000aa00aa00aa00aa00aa000000aa000000a8a8a8a8a8a8a8a8a8a88888a8a88888a888a888a888a888
  | 1, 0 => 0xafaf0000afaf0000af00af00af00af00aaff00ffaaff00ffaaaaaaaaaaaaaaaaaaaaaaaaa0a00000aaaaaaaa88880000aaaa0000aaaa0000aaa0aaa0aaa0aaa0
  | 1, 1 => 0xbbbb3333bbbb3333bbbb0000bbbb0000bb33bb33bb33bb33bb00bb00bb00bb00babababababababaafffafffafffafffafafffffafafffffafafafafafafafaf
  | 1, 2 => 0xc0c00000c0c00000c080c080c080c080c000c000c000c000c0000000c0000000bfbfbfbfbfbfbfbfbbbbffffbbbbffffbbbbbbbbbbbbbbbbbbbbaaaabbbbaaaa
  | 1, 3 => 0xcc000000cc000000c8c8c8c8c8c8c8c8c8c88888c8c88888c8c80000c8c80000c888c888c888c888c800c800c800c800c0f0c0f0c0f0c0f0c0c0c0c0c0c0c0c0
  | 1, 4 => 0xcccccccccc000000cccccccc80808080cccc0000cccc0000ccc0ccc0ccc0ccc0ccc00000ccc00000cc88cc88cc88cc88cc880000cc880000cc00cc00cc00cc00
  | 1, 5 => 0xcfcf0f0fcfcf0f0fcfcf0000cfcf0000cf0fcf0fcf0fcf0fcf00ff00cf00ff00cf00cf00cf00cf00cdddcdddcdddcdddccffccffccffccffcccccccccccccccc
  | 1, 6 => 0xdddd0000dddd0000ddccddccddccddccdd55dd55dd55dd55dd00dd00dd00dd00d0f0d0f0d0f0d0f0cfffcfffcfffcfffcfcfffffcfcfffffcfcfcfcfcfcfcfcf
  | 1, 7 => 0xe0c0e0c0e0c0e0c0e0a0e0a0e0a0e0a0e000e000e000e000dfdfdfdfdfdfdfdfddddffffddddffffddddddddddddddddddddccccddddccccdddd5555dddd5555
  | 1, 8 => 0xea00ea00ea00ea00ea00c000ea00c000e8e8e8e8e8e8e8e8e0f0e0f0e0f0e0f0e0e0e0e0e0e0e0e0e0e0c0c0e0e0c0c0e0e0a0a0e0e0a0a0e0e00000e0e00000
  | 1, 9 => 0xeaeaeaeae0e00000eaeac0c0eaeac0c0eaea0000eaea0000eae0eae0eae0eae0eaaaeaaaeaaaeaaaeaaaaaaaeaaaaaaaeaaa0000eaaa0000eaa0eaa0eaa0eaa0
  | 1, 10 => 0xee000000ee000000ececececececececececccccececccccececa0a0ececa0a0eccceccceccceccceccccccceccccccceca0eca0eca0eca0eaeaeaeaeaeaeaea
  | 1, 11 => 0xeeaaeeaaeeaaeeaaeeaacc00eeaacc00eeaaaaaaeeaaaaaaeeaa0000eeaa0000ee88ee88ee88ee88ee88cc88ee88cc88ee00ee00ee00ee00ee00cc00ee00cc00
  | 1, 12 => 0xeeeceeeceeeceeeceeeccccceeeccccceeeaeeeaeeeaeeeaeeea0000eeea0000eee0eee0eee0eee0eecceecceecceecceecccccceecccccceecc0000eecc0000
  | 1, 13 => 0xefefefefefefefefefef0000efef0000eeeeeeeeeeeeeeeeeeeeeeeeee000000eeeecccceeeecccceeeeaaaaeeeeaaaaeeee8888eeee8888eeee0000eeee0000
  | 1, 14 => 0xf0c0f0c0f0c0f0c0f0c0c0c0f0c0c0c0f0a0f0a0f0a0f0a0f0a0a0a0f0a0a0a0f0a00000f0a00000f030f030f030f030f000f000f000f000f0000000f0000000
  | 1, 15 => 0xf1f1f1f1f1f1f1f1f0ff00fff0ff00fff0f0f0f0f0f0f0f0f0f0f0f0f0000000f0f0f0f080808080f0f00000f0f00000f0e0f0e0f0e0f0e0f0e0f000f0e0f000
  | 2, 0 => 0xf3f3f3f3f3f3f3f3f3f33333f3f33333f3f30000f3f30000f3f0f3f0f3f0f3f0f333f333f333f333f3330000f3330000f330f330f330f330f300f300f300f300
  | 2, 1 => 0xfa000000fa000000f8f8f8f8f8f8f8f8f8f8f0f0f8f8f0f0f8f0f8f0f8f0f8f0f8a8f8a8f8a8f8a8f888f888f888f888f5f5f5f5f5f5f5f5f555f555f555f555
  | 2, 2 => 0xfaaafaaafa000000faaaf000faaaf000faaaaaaafaaaaaaafaaa0000faaa0000faa0faa0faa0faa0faa0f000faa0f000fa00fa00fa00fa00fa00f000fa00f000
  | 2, 3 => 0xfafa0000fafa0000faf8faf8faf8faf8faf0faf0faf0faf0faf0fa00faf0fa00faf0f0f0faf0f0f0faf0aa00faf0aa00faaafaaafaaafaaafaaafaaafaa00000
  | 2, 4 => 0xfca8fca8fca8fca8fc00fc00fc00fc00fc000000fc000000fafafafafafafafafafafafafa000000fafafafaf8f8f0f0fafaf0f0fafaf0f0fafaaaaafafaaaaa
  | 2, 5 => 0xfcfc0000fcfc0000fcf8fcf8fcf8fcf8fcf0fcf0fcf0fcf0fcecfcecfcecfcecfcccfcccfcccfcccfcccf000fcccf000fcccccccfcccccccfccc0000fccc0000
  | 2, 6 => 0xfeaafeaafeaafeaafeaa0000feaa0000fe00fe00fe00fe00fe00ee00fe00ee00fe00cc00fe00cc00fcfcfcfcfcfcfcfcfcfcf0f0fcfcf0f0fcfcccccfcfccccc
  | 2, 7 => 0xfefefefefefefefefefef0f0fefef0f0fefeccccfefeccccfefe0000fefe0000fef0fef0fef0fef0feeefeeefeeefeeefeee0000feee0000feccfeccfeccfecc
  | 2, 8 => 0xff33ff33ff33ff33ff30ff30ff30ff30ff11ff11ff11ff11ff0fff0fff0fff0fff00ff00ff00ff00ff00ff00cc000000ff00ff00a000a000ff000000ff000000
  | 2, 9 => 0xffa0a0a0ffa0a0a0ff88ff88ff88ff88ff88ff00ff88ff00ff88cc88ff88cc88ff888888ff888888ff80ff80ff80ff80ff55ff55ff55ff55ff555555ff555555
  | 2, 10 => 0xffaaffaaffa0ff00ffaaffaacc880000ffaaff00ffaaff00ffaaaaaaffaaaaaaffaa0000ffaa0000ffa8ffa8ffa8ffa8ffa0ffa0ffa0ffa0ffa0ff00ffa0ff00
  | 2, 11 => 0xffccffccffccffccffccff00ffccff00ffccccccffccccccffcc0000ffcc0000ffc8ffc8ffc8ffc8ffc0ffc0ffc0ffc0ffc0c0c0ffc0c0c0ffaaffaaffaaffaa
  | 2, 12 => 0xfff00000fff00000ffeeffeeffeeffeeffeeff00ffeeff00ffeeeeeeffeeeeeeffeeccccffeeccccffeeaaaaffeeaaaaffee0000ffee0000ffe0ffe0ffe0ffe0
  | 2, 13 => 0xffff000088880000fffcccccfffcccccfffaff00fffaff00fffaf0f0fffaf0f0fffaaaaafffaaaaafff0fff0fff0fff0fff0ff00fff0ff00fff0f0f0fff0f0f0
  | 2, 14 => 0xffffffff11111111ffffffff00000000ffff8888ffff8888ffff8800ffff8800ffff8080ffff8080ffff1111ffff1111ffff0000ffff0000ffff0000aa000000
  | 2, 15 => 0xffffffffa000a000ffffffff88888888ffffffff88880000ffffffff88008800ffffffff80808080ffffffff55550000ffffffff33003300ffffffff30303030
  | 3, 0 => 0xffffffffc0c00000ffffffffaaa0aaa0ffffffffaa88aa88ffffffffaa00aa00ffffffffaa000000ffffffffa8a8a8a8ffffffffa0a0a0a0ffffffffa0a00000
  | 3, 1 => 0xfffffffffa000000fffffffff0f00000fffffffff0000000ffffffffee000000ffffffffcccc0000ffffffffcc880000ffffffffcc000000ffffffffc8c80000
  | 3, 2 => 0xfffffffffff00000ffffffffffcc0000ffffffffff000000fffffffffcfc0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc35c536844bb45136804b8c6150844c9dc536844c750d9c6c4c35c596a84
  | 4, 0, 0 => 0xbb5d69cfd682e2dfaeb6c2116f3717aaa108b76873a1b26c5c8bf54081362e12e2be54211709717eb7cd8b81b8d45a0a85bb5c620d5422de6e2fd512116ed4374260f4b76a1cf1866c5bb5c6269b422e3ae2c7542116ecfd6e280fcb8e882a108815
  | 4, 0, 1 => 0xbb52dfaa040addae29b422016ecfd7436cd8b76b8d757c845bb3f5b8a23e2ddae2f570a1171d43672a108b81b8d453c845bb5c602a8422dda3314542016ed717eb6908b76b8db92a845bb5c6ce9b422e12e2fd4da116ed758736508b71a1b3d50845
  | 4, 0, 2 => 0xc75c6869b422ddae2fd6f1f96fd75a1b0d08b76b3c5950845bb5c6a2d0362dda86e9619b16ed407eb78d8b84b8c4d50845bf50dd0c3362e1ae3195421171d437ebacd8b768a3f5367c5c05c620a8422dd9d0d9619b16ed757eb6d08b86b8aa12a845
  | 4, 0, 3 => 0xc7445508440ae46e319541d96f371792a108b917ea8908815c25c5facb542e0ee2f554211707717ea8908b86b8c6550805b8c5dfaa8422dda2913542116ed71642a108b767eb71b26c5c0dc632a83e2ddae312542116ed436e2f8d8b76b8d0da0795
  | 4, 0, 4 => 0xbb5c5e2e6422ddae36a659b16ed71b526d08b86b8c4d50845bb3f5d0d8362e4ee31954211727715425508b76a1c7d866c5bb3f5d0a23e2ddad5144da116ed718ca6d00b76b8b2d50805bb5d69d0e76ae2e86fd759b1725437ebad08b8eb8d0da06c5
  | 4, 0, 5 => 0x19378aa108815
  | 5, 0, 0 => 0xb8d5a86fd54211aed75a1c3930846bb5c686f54f211aed71b54ad2a846bb50deae854211aed718cbf5507e6bb5c686ff769b1aed437ebb5d26c6c75c687304c211b0971ac47550846bf5d686fd50211aed436833550766bf5c694fd54211afd437ebb5d06c6bb50df49e42205aed716831d50766
  | 5, 0, 1 => 0xc4dc6befd50211b1d437eaa1026c6c250e3efd54211b09717eb8940846bb5c6870e681b1aef71a1bf5da6c6c8dc5faa0421b1aed71a1c9d30846bb5c69cc354211aed71a1b7d7c6c6bf5d686fd76a11b1d71b4bc550846bcdc5faf154211aed71882a108756c35c686a84c211aed71a74393c846
  | 5, 0, 2 => 0xbb5c63b19541f1aed717ebb5b66c6bb50df0e854211aed7199bf550846bb5c5b2be54211aed75a1c3150846bb5c5faa2409f1aed437eba1c2846bb5c5fadf6c9b1b09717ebd550846c05c686a84c211b1d71a1b0d50846c25c6b11d541f1aed719a3f550846bb5c6871d70a11aed7189c4550846
  | 5, 0, 3 => 0xbb5c6d51654211aed71aebf544846bb5c6bafd6fa11aed71a63f544846c5dc68724541d9aed71a1cc12a846bb5c5dad9619b1aed71a1bc5aa846bb5c5faac54211aed71b53c5da6c6bb5c5faeb6c1b1afd71a1b0d50846bb5c6611154211aed71a73f5da696bb5c670fd50211afd71a1c393c846
  | 5, 0, 4 => 0xbb50e28fd54211aed71a743940846c1dc6b0fd54211aed71aabf5c2846bbd0dfae854211b0371a1bf544846bb5c5fac654211aed338fbf550846bb5c6befd6c211b0971a1bf5da6c6bf5c5faa84217daed7189aa1087c6bb5c66ac354211aed717eb61086c6bb50dfee854211aed71a6bf5da6c6
  | 5, 0, 5 => 0xbb5c69b0e54211b097188bf550846bf5c686fd6f9b1b1f438fbf550846bb5c6873f619b1aed4354210c25d6bb5c686a83b15daed437eb35506c6bb5c69ced619b1b0971a1cc930846bb5c6870e75a11aed71a1b413c766bb5c68ac354211aed43a03f5d66c6bb57dfadc5021180191b8bf544845
  | 5, 0, 6 => 0x63ae311542116ece86cb0d50846bb5c686c351211aed71a1c31da6c6c5d0e3efd54211b0971a1c3950846bb5d686c3421b1b25717ebc550846bb5c6391154211aed6a78ba150846bb5c686c3421b1aed71a1bf5d67e6bb5c5e2a8421fdb1d717eb6550846bb5c5fad8409b1aed71a73f536846
  | 5, 0, 7 => 0xbb5c6ab1b54211aed71a8b4150766bb50dfae8541e9b17437eba950816bddc68724541d9aed7178aa108186c8d61faa842205aed718ea89087c6bf5c686ed619b1b09437eba150846c750dfaeb54211aed717eb85b0846bb5c5faa842181b0771ac3f5507c6bb5c626f154211aed43983f5d0846
  | 5, 0, 8 => 0xbb5c686d054201aed71a5bf540846bb50e3314541d9af775a1bf550846bb5aa331454211aed588fbf5507c6bb58a86fd54205aed71a1cc936846c5dc686fd769b1aed437ebb950846c75c69cfd54211aed71a1b0d74846bb50dfaa84ea05aed71a1b0d026c6bb5d686a842175aed71a1aa1085d6
  | 5, 0, 9 => 0xbb5c5faa2420c1aed6d87bf550846bb5d2870c54211aed717eb6d40846bedc69afd54211b09717ea81086c6be5c69cfd54211aed63a1bf54a846bb5c686be51211aed437eaa108616bb5c686be421b1afd75a73f550846bedc686fd75a11b0571a1bc550846c450e3efd54211aed71a1bf554846
  | 5, 0, 10 => 0xbb5c6a2d054211aed407eb7950846c0dc686d0541d9aed71b542950846c750e42a842205b2354a1bf550816c5dc622fd54211b0b71a1c7950846bb5c626a842201aed717eb6544846c55c686fd51211b1771a1cc930846bb50dfadd54205b1f7188bf550846bb5c686a842125aed71afbf534846
  | 5, 0, 11 => 0xbb5c6bf0c50211b0171a1bc550846bb5c5fadf541f1b1771a1bf53c846c5d0dfae854211aed717ab6550846bbdc686c354211b1771a1c7550846bb50dfae854245aed71a73f5d66c6bb50dfaa842191aed717aaa108306bb45222fd54211aed437eba1b26c6c5dc6870e54211aed437eba1506c6
  | 5, 0, 12 => 0xbb5c5fae16ca11aed71922a0ec586bf5c686fd759b1af771a1bf5da6c6c25c63b1154211aed436e2f950846c0dc6bef154211aed75a73f544846bb5c6b1324c1f1aed437eb7db86c6bb5c6873267211aed71a1bb4d85d6bb5c686f54da11aed71a1c91aa766bb50df498409b1af171a1aa130846
  | 5, 0, 13 => 0xbb3f5b8d954211aed717eb8940846bb5c6869b421d9aed71a1cc186846c0dc686d054211aed437430d086c6bf5c69cfd769b1aed71a1b1550846bb5c6b10e541f1b037188aa108766bb5c686fd6aa1180184b8bf544845bb52e86fd54205b1d71abbf550846c75c686fd51211aed7178aa108336
  | 5, 0, 14 => 0xbb561fae8541f1aed71a1cc9a0686bb5c5faa842161afd71a1bf544846c25c686c354211b13437eaa108816bb5c632fd4d9f1aed71a1bf5da716bb5c5facb541f1b17437ebad08816bb5c6bf19541d9aed71a1b3150846bb50dfacd54211aed437ebb4d8616bb5c5fac754211aed439f30150846
  | 5, 0, 15 => 0xbb5c68719541d9aecfd75b614a846bb50e6cfd54211aed71a1c91aa846bb5c686fd6f1b1aed75a73f53084600612e2f55421170371a1a7908766c75c686f554211b19437eba150846bddc687324c211aed71ac3f5c46c6c25c5f4f15421180176b8c6550805bb5c6b0fd4f1f1b0371a8aa130846
  | 5, 1, 0 => 0xbb5c61cd9421b1b23717eaa12a846bb501eaa842205aed71a1a61027a6bb5c68119541d9aed71a1bf5da6c6bc5c6870754211b0971a1aa1084a6bb50e1ca842185aed717ebb5407e6bb5c69cfd681b1aed7178b9d50846bf5c69d0e54211aed717ea89087b6bb5c6870b54211afd71a1bd550846
  | 5, 1, 1 => 0xbb5c5f4c754211aed71a1b41307a6c25c63af154211aed71983f5b2846bb5c648f5541f1aed718eaa144846bb50e1ce8541b180176b8d0d083c5bb5c5faa842165aed717eb7d507e6bb5c5eaa8421edaed71b550da06c6bb5c68724541e580176b8d0dfa715bcdc6870454211aed107d2a108816
  | 5, 1, 2 => 0xc8dc632fd54211b1771a1b0d50846bddc6a2fd54211b0771a1c7550846c5d0dfaa8409b1aed71a1cc9a06c6c75c6871154211aed438abf550816bfdc6d4f154211b09717eb6550846c8dc680fd51211b25437eaa108816bb50e3efd769b1b23717eaa1084b6bb5c6d4f14da11aed71b52a108466
  | 5, 1, 3 => 0xbf5c69cfd50211aed71ac47550736bb5c686fd729b1af771a53f550846c9d0dfaa842205b2371a1bf5c2846b8d0dfaec54211aed719931d30846c0dc6b0fd541f1b2371a03d550846bb5d686fd4f211aed71a1bf5cc846bb5c69ef154211aed437eba150846bb5c686f9769b1aed71a1aa1085e6
  | 5, 1, 4 => 0xc15c68698421e9aed61a1bf5da6c6bb5c63311541d9b0771aabf550846bf5c69afd54211b1d437eaa108346c75c6bef154211aed71ac30d507c60064ee2f1542116fd71a1bf5d6846bf5c6d4f154211aed71a2bfd50846bb50dfadc51211aed718eb1d50846bb5c63ae250211aed71a1b153c846
  | 5, 1, 5 => 0xbb5d6870e769b1aed717ea8108396bb50dfae8501b1b037178aa1087c6c0dc686f754211b2371933f550846bb5c69524541d9aed71adbf534846c75c686d054211aed7188bf5da6c6bb5c68724619b1aed437cba150846bb5c686c454211aed71a849150766b8d0e46fd54211aef71a2bf550846
  | 5, 1, 6 => 0xbb5c550842f975aed717eb6d086c6bb5c5faab421b1b2771a1aa130846bb5ca8afd54211b2371a1c6d50846bb5c698fd54211aed71a1c75da6c6c6d0dfaa842205aed718cc4d50846bb5c687246b1a1aed437eb2550846bb5ae86fd54205aed71ad4c92a846bb5c686fd42115aed71a743150846
  | 5, 1, 7 => 0xc8bf5e2a842205aed5388bf550846c25c5faa84aa11aed71a83f5aa846bb5c5b2c3421b1aed717ebb5447c6bb50e28fd4da11aed717eb6150846c5d0dfaeb54211aed71b73c550846bb5c6d519541cdaed5f8fbf540846bb57286fd75a11aed718caa0f8766c05c686fd6aa11aed71a1b40ec6c6
  | 5, 1, 8 => 0xbb5c686c354211b09717eaa1084b6bb54e86fd4f211b0371a1bf5aa846c65c5fad954211aed43873a150846bb5c6cea84aa11b0d7178aa108806c95c5faa850211aed71a9261087a6bb5c6d4a84da11aed437430d506c6bb54e870e54211aed71a8aa108486bb50e64e84c211aed717eb8540846
  | 5, 1, 9 => 0xbb50e3ec354211aed71b3c6550846bb5c6bebe54211aed717eb8944846bb5c686fd769e5aed71b02f550846bddce86fd54211aed71a8a61086c6bb5c6d4bd54211b09718cbf550846bb5c6872c4b211aed437eba13c846bb5c6d4be54211aff71ac3f5507c6bedc686fd769b1aed438eba150846
  | 5, 1, 10 => 0xc0dc686a84f211af371ac3f550846c5dc6872254211aed75a1bf5be6c6005dae313542116ed71a1bf5be6c6bb5c5eae254211afd71ac3f5507c6005dae3437e9716ed71a1a6108796bb5c69ca842175afb71a1c3950846bb5c6bf0e50211afd71a1b0d086c6c75c6b0fd541f1b0371a1c6550766
  | 5, 1, 11 => 0xbb5c68f0454211aed71a03f536846c25c6871b54211aed71a1bf5966c6bb3f5d0d854211aed75a1c39da846bb5c686fd4da11b237178aa108766bb5c686b354211aed75a1bb5866c6bb5c550954220180176b8aa108185bb5c680fd6f9b1aed43873b5d06c6bbdca86fd54211af771a73f550846
  | 5, 1, 12 => 0xbb5c6d5194da11aed71b532d50846bb59de2a842205aed437eba5506c6bb50dfacd4c1b1b1b71b53c550846c05c6a0fd54211aed71a6c3550846bf50dfae8541b1aed718caa108806005dae31d512116ed71802a1082c6bb5c69afd75a11aed1f7eb6550846bb58686c354211afd437eaa108616
  | 5, 1, 13 => 0xbb58e86fd50a11aed4376ba1866c6bb5aa28f154211aed715f2a1087c6c5dc69afd54211b1d71a1bf5da6c6bb5c632f154201b1771b53c550846bb5c6a2c354211aed719936530846bf50e3efd54211aed617eb6550846c8dc5faa851211b0971a1c3150846005dae3435415d71d435426108816
  | 5, 1, 14 => 0xbf5c687324c211aed7178b8d50846bb50e72fd54211b0b717eaa140846bb5c686fd36171aed75a743950846c8d0e3efd542118018ba1bf5d6845bb5c6d50354211aed71a1ba1866c6bb5c6d495421b1aed71a1bf5a4846bfdc6871d54211b17437eaa108346bf5d686fd769b1af5437eaa108816
  | 5, 1, 15 => 0xc8dc687324c211b2771b3bc550846bb5c5b0c254211aed719bbf5507c6bb5022cfd54211aed71a1bf594a86bf50dfae854211b17437ebad4a846bf5c6871d54211aed71b750d30846005dae36a4da1171d437eba150846005da86e8619b16ed437ebad4a6c6bb5c6bf324aa11aed71a73f53c846
  | 5, 2, 0 => 0x2ed7188bd5508460061ae2f1542116ed437eb9150846bb50e04fd54211aed437ebadd06c6bb5c69d0e769b1b1d71a8bf550846
  | 6, 0, 0 => 0xbb5c686fd5421038f76b8d0e14fd54211eed71a1bf55096423802ed71a1c1108356bb5c686fd5421014f76b8d75faf154211eed71a1bf5508416bddae36ea1bf550847bb5c5fad954210ecf8eb8d0dfaa84c211eed71a1c75508439bddad953a1bf550847bb5c686fd5421026e00bb5c5faa2421f1aed71a1b0d508412bdda86fd7430150847
  | 6, 0, 1 => 0xbf5c686fd5426108f76b8d0dfaa242141f1d437ebe9508440bddae36a78aa14a847bb5c5f4f154210f8f76b8d0dfad64c211eed75a1bf5daa8363ddae3437d3dd50847bb5c686fd76b64d8f76b8d0dfaa84216df2371a1bf55084283e2ee3437eaa140847bf5c686fd54204d8f81b8d4686fd54211c0176b8c4550843b30031b71a1bf550846
  | 6, 0, 2 => 0xc1dc686fd54210f6f76b8da9faa84212dc0176b8d4550984235dae34d7eaa14a847bb5c686fd76aa122f81b8d0dfaf154211c01765421028080235dae34e7eaa108627bb5c6bb437ea8108f7fb8d0dfaa8421d9c0176b8d0dea841ab5dae3437ead150847bb5c686fd5421042f76b8d0d86a842205eed71ac475faa83e3dfae343a03f550847
  | 6, 0, 3 => 0xbb5c686c3542103cf76b8d0dfaa2421b1c0191b8bf5e2a84235dae35da03f540847bb5c686fd6fa10d8f76b8d2286fd54211f0d71a1bf55084403e12e3437eb8950847c25c686fd5429508e00c85c686fd54211b2371a1bf55084363ddae366a1b0d50847bb5c68cfd542106af76b8d0dfaa842135f1771a1bf5daa8423ddae35f7eaa12a847
  | 6, 0, 4 => 0xbb5c687327ea8908f76b8d39faa8421d9f0371a1d05faa8423ddae3437eaa1087d7bb5c686f554210a0e00bb5c556a842051aed717ebc550843f3ddae3436830d50847bb50dfaa852a1068f76b8c45faa84d211eed71a1aa55099423ddae35da1bf5da847bb5c686fd6fa8908f91b8d0e64fd54211eed71a1bf550840d3802ed71a1cc9083d6
  | 6, 0, 5 => 0xbb5c686fd752a0d8f76b8d0dfaa84aa11eed71a1c1d5084163802ed437eaa108216bb5c6befd5421096f7eb8d0dfaa842189c0176a1bf5d6a54235dae3439c3f550847bb5c686fd542100cf76b8d0dfad354211eed71a1cc93097423ddae3438cbf550767bb5c68724541d810f76b8d0dd6c254211eed71a1c21faa8423ddae34354210f84a7
  | 6, 0, 6 => 0xbb5c69d0e54210d8f76b8d0dfa8436109eed54a1bf5508440bddae3437ea7934847bb5c68724541d86af76a9d0dfaa850a11eed71a1bd55084363ddae3437eaa108317c8dc686fd7e2a108f76b8d0ddac3421b1eed71a1bf9faa8423ddae34378b0d50847bb5c687147eaa108f8bb8d0dfaa8421adeed71a750dfaed363e3ae3437eaa108767
  | 6, 0, 7 => 0xc25c5faa850210f8e00c0dc686a84c21180181b8bf550840435dae31d78aa1087c7bb5c6b0fd76aa0f8f8eb8d0df4a84c211efd71a1bf550843b3ddae3437eadd50847c5dc686fd752a108f76b8d0e64f554211eed71afc65faa8423dda86fd7436550847005dad4f15421008d76b8d01faa84aa11c0176b8d0d50994235dae3437eaa1080c7
  | 6, 0, 8 => 0xbb5c6c5437eaa108f76b8bf5b2a8421f1eed71803f550841abddae3437eaa108747bb5c686fd5126108f76bad0dfa98421b1eed71a1ce9faa8423e26e343a03f550847005dae2841a85010d76b8d0dfafa6aa11eed71a1c7550842abe06e3517eaa108767005dae3437ea1076d76b8d0dfaa84ea11f2371a1bf55098423802ed438fbf550506
  | 6, 0, 9 => 0xbb5d6870e7eaa108f76b8d0e32fd54211eed71a1bf5c48434bddae34394bf550847bb5c69d43872a108f76b8d0dfab954211eed437d2a1308440be3ae343983f550847bf5c6870e54210d8f76b8d01faa84212deed71a1bf5508b423802ed438a3f550846bb5c687247ebb4d8e00bb3f508350401180176b8d1dfa8418300309437eaa108046
  | 6, 0, 10 => 0xbb5c687095421090f76b8d0e4efd54211eed71a1bf55084093ddae3437eb7550847c75c686fd782a108f76b8d0e48a83b169c0176b8b0d5084043002ed71a1b0d086c6bb5c686f55426108f76b8d99fad954211eed71a1bf57484213ddae3439ebf550847bb5c686c25421102f76a1bf5bedc54211f0371a1bf5508439bdda871f7eaa108087
  | 6, 0, 11 => 0xbb5c6872454280ecf76b8d0d86c054211eed71a1bf544841c3ddae2fd78aa108307005dae36a78a106ac00c25c6871d54211aed71a1bf5eca8423e1ee3437eaa12e847c8dc6a9437eaa108f76b8d0dfaa8420e9eed71a1cddfaa8423dda871f7eaa108357bb5c686fd5d26108e00bd5c686fd54141aed71a1bf53081363ddae3408cbf550847
  | 6, 0, 12 => 0xbb5c686fd68260d8f76b8d0dfaa842139eed439ec7dfaa8423ddae3437eaa108617bb5c686fd51210ecf76b8d7e4cfd54211eed71a73f5508440bddae3587eb8950847bb54e87247eaa108f76b8d0e1ced541b1eed437ebc1508440bddae3437eaa1085a7c8dc686fd54210ece00b8d0dfaa84200daed71a1bf5f4ed363802ed717eaa108776
  | 6, 0, 13 => 0xbb5c686fd702a108f76b8d0df498421b1eed717eb7d50a03e3802ed71a1cc930506bb50dfaed742a0d8f76b8d0dfad754211eed71a1c19faa8423ddae3437eb7950847bb50e48fd742a108f76b8da9e2a842141c0176b8d0d50842eb5dae3437d2a13c847bb5c686fd769b028f76b8d0dfaf14da11eed71a1bf550842338030971a1bf508356
  | 6, 0, 14 => 0xbb5c687324c25508f76b8d0deaa8421d9c018bb8d0d50840a3612e3437eaa108507005dae343872a0a0d76b8d39faa0421b1ef571a1bf5508427bddae34e7eaa108697bb5c68724541d8eaf76a1bf5d0a842085c017bb8d0dfaa84235dae34378b5950847005dae3117eaa0a0d76b8cedfad954211eff71a1bf5e2a8423ddae3697ebc150847
  | 6, 0, 15 => 0x616e3437eaa108d76b8d0dfaa84211deed71a1bf562a8423ddae3437ebad086c7bb5c686fd542107af76b8d61fae2541f1eed71a1bf5daa8423ddae36a78aa1086c7bb5c6b0fd54294f8e00bf5c69cfd54211aed71a1c7550843dbddae3437eba1506c7be5c686fd54210f8f7eb8d0dfaa842205eed719c445faa8423ddae3437ebb4d8357
  | 6, 1, 0 => 0x5dae3437ea78a0c00bb50dfae854141aed71a73f5da84363ddaa7437ebe950847bb5c5faa842168b0f76b8d35faa8421b1eed71a1bf55ca8423ddae3439926108087c8dc6d1437eaa108e00bb5c6871d54141aed71afd0dfaeb423ddae3437eaa146847bb5c6d4a85025508f76b8d0e60a84c211c0176a1bf5508430b5dae34ba1bf550847
  | 6, 1, 1 => 0xbf5c686fd54210d2f76b3d0dfaa842205eed71a1c395084043e3ae3437ebc550847bb50dfafa742a108f81b8d0dfaa853211eed438fbf550a0423e46e3437eaa14e847c75c686fd5421106f84b8d0dfaa8421b1eed71b550da0a8423ddae3437eaad50847bb5c686fd54210cce00c750dfaa842205aed7188bf55084043e2ee358a1bf550847
  | 6, 1, 2 => 0xbb5c6bf3278aa108f76b8c41faa842205eed7188bf550841ab802ed437eba1506c6bb5c6bf247ea8108f7cb8d0dfaa8421a5eed71a1d0236a8423ddae3437eaa108077bb5c6b5439926108f76b8d0e6498420d5c0176b8d0d50840bb612e343993f550847bb5c686fd542101cf7eb8d0dfaa0421b1c0184b8bf5e2a84235dae34390aa108757
  | 6, 1, 3 => 0x5dae358541f028c00c1dc686fd54211aed71a1bf5e8a8423ddae3437ebad026c7bb5c686fd56aa108f76b8bf55095421f1c0176b8d9de2a84235dae3437eb5508757bb5c6870e542106af7eb8d0dfaed421b1eed71a1bf53c84043dfae3437ebc550847005dae3437ea1064d76b8d0db2c354211eed437eba150840a3dda871f7ebb550847
  | 6, 1, 4 => 0xbb5c686fd4f2106af76b8d0e56fd4c211eed71a1bf59aa8423802ed71b52a1081a6bb50dfae8542106af76a03f5e2a842205eed71a1be5daa8423802ed587eaa0f8046bb5c6871d542106ae00bb5c5fadf541f180171a1bf550840035dae31988bf550847bb5c68732682a108f76ae50dfaa842205eed55a03f5508440bddae343922a108757
  | 6, 1, 5 => 0xbb5c6871154210ecf76b2d0dfae854211eed717eaa1087c25bddae2fd78aa1087b7bfdc686fd54210e6f76b8d15faa842079eed71a1bf5448440be12e343a03f550847bb5c686fd76a80d8e00c5dc686fd420d5b0971a1bf55098423ddae343862a1086c7005dae3588eaa108c00bb50d50500a011aed71a1bf55084203ddae3437eabd50847
  | 6, 1, 6 => 0xc5dc6d5437eaa108f76b8d0dfae554211eed71a1bf586a8423ddae367a1aa130847c25c6b0fd54210f8e00bb5c686fd6aa11b0171a1bf5f4a8423ddae3437eaa108227bb5c6813278aa108f76b8d0dfaa846a11c018eb8d0d50984235da87407eaa1083470063ae2fd5421010d76b8d7dfafa50211c0176b8da950954235dae3517ebe950847
  | 6, 1, 7 => 0xbb5c686fd712a108f76b8d0e64a04c211eed71a1c81faa83abddae3437eb7d506c7bb5c686fd54210cae00bb5c6b11d541f1aed71a1bd5508440bddae3438cbf550737005fae2fd5421010c00bb50dfacd54211aed718cbf550843e3ddae3437eaa112847005dae2fd63aa108d8bb8d0dfaa842141c0176b8bf5c4a0423636e343a03f550847
  | 6, 1, 8 => 0x5dae3587e9f06ad8bb8d7e86fd54211f1771a1cc5faa8423dda87057eaa108357bb5c686fd592a108f76b8d0e1ca850211f1771a1bf55084363ddac3437ebb550847bb5c687157eaa108f76b8d6686fd54211eed71a1bf550842a3ddae3437eaa1082e7bb5c686fd5424d08f8eb8d0df4f154211c0176b8d0d30843d3002ed717eaa108586
  | 6, 1, 9 => 0xbb5c686fd70a1102f76b8d0e3aa850211eed71a1bb586a8363802ed437eba950816bb5c686fd5421094e00bb5c686501a851aed7188bf5daa8423ddae3439230d50847bb5c686fd54210e0f76b8d0dfaa84214deed71a1cc930841ebddae3437eaa0d828700606e3437eaa0a0d76b8d0dfaed361adeed71a1bf5c2843e3ddae343993b530847
  | 6, 1, 10 => 0x5dae2f15421100d76b8d628724541d9eed71ac3f5507c283802ed75a1bf5da6c6bb5c686fd542103ef76b8d7de2a8421d9eed438fbf550a5423802f571a1bf550846005da86fd280d408d76b8d0e1ced54211eed71a1bf55091143ddae3437eaa136847bb50dfae85428108e00bb5c68719541d9b0971a1bf550843b3802ed71b546550846
  | 6, 1, 11 => 0x5dae34361aa0a0d76b8d0dfaa842149eed71b54ade2a8423ddae3437eaa108417bb5c68724541d8d0f76b8d0dfabe54211eed71a1b4150843b3ddae3437eaa108447bb5c686fd76a7908f76b8d19faa8420b1eed71b4be9e2a8423ddae3437eaa1082f7bb5c686fd71aa108f81b8d0dfaa842021eed71a1c75daa8423ddae3437ebb5507e7
  | 6, 1, 12 => 0xbb5c6b1327eaa0f8f76a1bf5d4a852a05c0176b8bf550841235dae36a78bc150847bb5c6a2a84c210ecf76b8d0df4c354211f0371a1bf550841abddae3267eaa1087c7c8dc686fd5421012f76b8d0e1ca8421adeed71a1ca1faa8423ddae3437eaf550847bb5c6b0fd541f0d8f76a1bf5f4a8409b1c0191b8bf550840435dae3437eaf150847
  | 6, 1, 13 => 0xbb5c686fd5faa108f76b8d0dfaed529b1eed71a1b0d5084043ddae34361aa108147bb5c6871b54210f8f76b8d0e4afd54211eed71af3f5509f423e2ee3437eaa108827bb5c632fd78aa0f8f76b8d0dfac254211efd71a1bf5f6a8423ddaeb437eaa108687bb5c686f579aa108f76b8d0dfaa8421a1eed71aed0dfa98423802ed71ac3f550556
  | 6, 1, 14 => 0x5da86fd742a108d76b8d71faa850211ef771a1bf55084363ddae3517aaa108767bb5c6d7437eaa108f77b8d0dfaa842079eed437eba9d0a8423802ed71a4bf5504b6bb5c686fd5424108f76b8d0e36a842205c0171a1bf5508401364ae35ca1bf550847005daeb43872a108d76b8d0d508436175eed71a1aa13084403e3ae3437eaa12e847
  | 6, 1, 15 => 0xbb5c622fd5429508f8bb8d0dfaa8421d9eed71a6bf5508440b802ed71803f508356c0dc686fd54210b4f76b8d0e64a54c211eed437eaa1086c30bddae3437eaa108277bb5c686fd542101af93b8d9e86fd54211f1b71a1bf5e0a8423dda86fd5425d08817bb5c6d4f15421102f76b8d0dfaa8421ddeed71923f5b2a8423ddae34361aa108357
  | 6, 2, 0 => 0xbb5c687245421058f76b8d41faa8421d5eed71a1bf550924238030d71a1bf550846bedc686fd54210d6e00bb50dfaa8421b5aed71a1bf5508405b802ed71a1bb4d8146bb5c686fd54210e4f76b8d0e1ca852a11eed71a1c69faa8423de6e3437eaa108307c25c686fd5421102e00bb5c686fd76989aed72a1bf550840f3e2ee343a13f550847
  | 6, 2, 1 => 0xbb5c686fd76ba0d8f76b8d3a48fd54211ef771a1bf55098423ddae3437ea953c8470061ee3437eaa108d76a1c7dfaa842035eed437eba150a5423ddae2fd7d36550847005da86fd542101ad76b8d0e3ae254211efd71a750dfaa8423ddae3437eaa1027a7005da86fd769b008d76b8d0dfaeb541b1eed71a1c7550a5423ddae3437eb4150687
  | 6, 2, 2 => 0xbb5c686fd5422908e00bb5c6870e769b1aed437ebe9d6a8423e06e3437eaa108757bb5c686fd6faa108f76b8d0e18a8421f1eed71a1bf550841fbddae3437eb65086c7bb5c686fd54210d8f76b8d0dfaed361a1c017db8d0dfaa84235dae2fd54281087e7005dae3117d2a108c00bb50e3efd420d5b0371a1bf5daa8423e12e3437eaa108697
  | 6, 2, 3 => 0xbf5c686fd76aa0d8e00bb5c686fa4f2118017688bf550840235fae343923f550847bb5c686fd54210def76b8d01fadf54211eed71a73f54484363dda871f7eaa108507005da87324c21008d76b8d0dfaa848a11eed71a1bf55084153ddae34361aa140847bb5c686fd54210acf76b8d0dfaa250a11eed71a1aa108622ebddae3587eaa0f8767
  | 6, 2, 4 => 0xc3dc686fd5429508f76b8d39fafa54211eed437ebad4a8440bddae3437eaa1083e7bb5c687324c210d0f8db8d0dfaf154211f0971b850dfaa8423ddae343a049150767bb5c686fd542100ae00bb50e1ca842011aed71ac445faa8423802ed437ebb5d06c6bb5c686fd5421050e00c0dc68724541d9aed71a1bf5dea8423802ed53a1aa108146
  | 6, 2, 5 => 0xbb5c687197ea6d08f76b8d0dfaa842131eed71a1bf596a8423ddae3437eaa108267005da86fd4f21008d7db8d0dfaa852a11eed5fa1c7dfaa8423802ed438eaa108046bb50dfaa842188c2f76a1c7dfaa8421b1eed71b250dfaa8423ddae3437eb7d507c7bb5c6870c54210d2e00bb5c5fad8542118018eb8d0dfaa8283002ed43742a108146
  | 6, 2, 6 => 0xbb5c686fd769b0a0f76b8daa86fd769b1c0184b8bf550840435dae3437eb5150847bb5c686fd70aa108f78b8d0dfaa8420d5eed71a73f53084363deae3437eaa108507c75c686fd5421010f76b8d0deaa84205deed71a1bf5508407bddae3437eaa122817bb5c6b1437ea7908e00bf5c686fd54141aed71a1bf550841bb802ed71a1cc130846
  | 6, 2, 7 => 0xbb5c6d5434c210d8e00bb5c6a2a842051aed717eaa14084183802ed71a1b0d50846c8dc687247eaa108f8eb8d0dfaa8420d5c0181b8d0e48a842363ae343923e950847bb5c686fd5421d08f7eb8d0dfaa842051eed71a1af950a0423ddae3437eaa1082b7bb5c6d4f154210e6f76b8bc550843e1d9eed71a1c3dfaa8423ddae3437eaa108117
  | 6, 2, 8 => 0xbf5c686fd542106af76b8d0dfaa8420e1eed71a1cc93084283ddae3407ebd5508470062e86fd5421102d76b8bf5b2a850211eed437eb355098423ddae35fa1bf5da6c7c15c686fd54210f4f76b8d0dfac154211eed71a1bf55085423802ed71afa8108146bb5d686fd54210c4f76b8d0dfaa842059c0176b8d0e1c841ab5dae3437eaa108627
  | 6, 2, 9 => 0xbb5c687324c210d8e00bb5c686a8421c1aed438a3f5e2a8423ddae3517eaa108687bb5c6870e54210a0f76b8d0dfaa84206deed71ac3f550813e3dda871f87bf550847c8dc686fd54210f6f76b8d0e5aa84aa11c0176a1bf5d0841ab5da86fd54211024f7c5dc686fd78aa108f76a1c91f4a842205eed71a1bf55086423802ed71a1c7508356
  | 6, 2, 10 => 0xbb5c687037eaa108f76b8d76b0fd54211eed71afd0e1ca8423ddaeb43872a1086c7bb5c686fd4aa10d8f76b8d0dfafa51211eed71a1bf550840cbddae354a1bf5507c7bb5c686c35429508f76a1bf5d0a842141eed6aa1bf5d0a8423dda86fd54295026c7bb5c686fd54210fef76b8d0e3aa842141eed71afd0e6498423ddae3437eaa108637
  | 6, 2, 11 => 0x5dae34376b0cd8d76b8d49faa8421e9eed71a1be9eaa8423802ed4382bf508356c0dc686f154210ecf76b8d0e60fd4ba11f0371ac50dfaa8423ddae34395bf550847bb5c686fd5421048f76afd0dfae854211eed43903f5f4a840bddae3436b26108767bb50dfae854210d8f76b8d0e3aa8421b1c0176b8d0dfadf36362e86fd5429508817
  | 6, 2, 12 => 0x5da86c35421008c00bfdc686fd54211aed71a1bf55084103ddae3437eaed50847bb50ddae861aa108f76b8da950a04c211c0176b8d0dfa91143002ed54a1bf550816005dae3437ea6d08d76b8d0e1ca8409b1eed71a1bf5da6c3138032371ac3f550846c75c686fd76aa108f76b8d0dfab654211eed717eaa144843e3ddae3437eac1086c7
  | 6, 2, 13 => 0x5dae2a82805010d76b8d623aa8421f1eed717eb89b2a8423ddae3437ea91086c7bedc686fd54210d8f76b8d7dfadf50211c0178b8d0dfaa842360ee3437eaa108817bb5c686fd5427108f76b8bf550a0421edeed71a1bf5da76363ddae3437430d50847c1dc686fd54210f8f76b8d0d86bd54211eed71a1bf5508f423dfae3437ebb550847
  | 6, 2, 14 => 0xbb5c6873f7ebb4d8e00bf5d686fd54211aed437eba9508440bdda871f7eaa1087c7bb5c68afd76aa108f76b8d61faa83e1cdf1371a1bf550a0423ddae3437eaa108797bb552a7437eaa108e00bb50dd0c354211aed437ebad50a5423ddae3437eaa1081e7bb5c686fd5423108f7eb8d0dfaa8421adeed71a1a610876363802ed71a1bf574426
  | 6, 2, 15 => 0xbb5c686fd54210cef76b8da9e2a84aa11eed717eb418ea8423ddae34361aa108507bb5c686fd5421066f76b8daa86c354211eed71a1cbde2a8423dfae36fa1bf550847c5dc686fd5425d08f76b8d0e54fd54211c0176b8da9e2a82835dae36a78aa1081a7bb50dfae854210ecf76bad0dfaed421b1c0176b8d0d86841ab5da871f7eaa108817
  | 6, 3, 0 => 0xbb50e7efd742a108e00bb5c69ca842051b0371a1bf55098423ddae3439930d50847bb5c686fd76ae908f76b8d7e86c354211eed437ebadd0a8423ddae3437ebb5026c7bb5c686c354210d8f84b8d0dfafa54211eed71a1cadfa95423ddae7437eaa108687005c686fd5421002c00bb5c686fd759b1afd71a1bf550a5423ddae34a7eaa130847
  | 6, 3, 1 => 0x5dae34e872a108d76b8d0dfaf1769b1eed71a1bf5508439bddae3437eaa108237bb5c69cfd54210d0f76b8d0dfaa8421b9c017eb8d0dfaed3635dae3439926108817bb5c6d51978aa108f76b8d0dfaa84a211eed71a1bf5cea8423ddae3437ebb4d81e7bb5c6befd50210ecf76b8d0dfaea541adeed71a1bf56aa8423ddae36a78aa108357
  | 6, 3, 2 => 0xbb5c686fd54210f0f76a1bf5d0a842079c018bb8d0dfaa8283002ed71a1bf4d81e6005e2e3437ea106ad77b8d0dfaed54211eed71a1bf5508414bddae3437eb4550847bb50dfae85421102f76b8d0dfae2421b1eed71a1c75508440bddae3437eaa11c847bb5c686fd54210bef76b8d0e2cfd54211c017ea1bf550840235dae343973f544847
  | 6, 3, 3 => 0x64ee3437eaa108d7eb8d0dfaa842141efd71b550dfaa8423e2ee3437eaa108357005dee3437eaa108d76b8d0dfaa84210defb71a1bf5508440bddae3437eaa1086a7005dae3435121028c00bf5c686fd420d5aed7176b6586a8423dda86fd76ba1086c7bb50dfaf1742a108f8bb8d0dfaa842051eed71b53c5daa84238031d71a1bf508356
  | 6, 3, 4 => 0xbb5c5b2c354211afd71afd0dfaa8423dda87198a3f550847bf5d686fd54210d8f8bb8d0dfaa8420d9eed717eb8950a0423ddae3437eaa1081d7bb5c69afd54210d6f76b8d0dfaa842041eed71a1bf570a8423ddae3437ebad086b7
  | 7, 0, 0 => 0x5dae3437eaa1087b7005dae349a1bf550507bb5c687407ebc550848bb5c686fd78aa130848005da87407eaa108817bb5c686fd5428108358bb5c686fd76aa108148005dae2fd54210a0087bb5c686fd7d2a108758005dae3437ebb5506c7bb5c686fd682a130848005dae36aa1aa130847bb5c686fd542953e848bb5c686fd7d3b550848bb5c686fd5428108148bb5c6bd437eaa14a848
  | 7, 0, 1 => 0x5dae3437ea106a30700646e343a03f550847000031771a1bf550846005dae3437eaa13c847bb5c6a3437eaa108768005dae3437eaa12a847bb5c687247eaa14a848bb5c6bb43a03f550848bb5c686fd5421102768005dae343992a130847005dae3327eaa108087005dae3437eaa108487005dae3437eaa1081a7bb5c686fd54210f8768bb5c686fd76aa108358005dae2fd54210d8087
  | 7, 0, 2 => 0x5dae3437eaa108367005dae3437eaa108157bb5c686fd5429508148005da87247eaa108047bb5c686fd76aa140848005dae3438cbf550847005dae3437eac150847005dae3437eaa1084f7005dae3437eaa14a507bb5c686fd78aa108768005dae343923e950847bb5c687407eaa108098005dae3407eaa108087bb5c686fd75aa108818005dae2fd5426108087005dae3437ea61086c7
  | 7, 0, 3 => 0xbb5c686fd54210f8698005dae358a1bf550507bb5c686fd78bc15084800002ed437eaa0a0046005dae3435426108767005dae2fd54210ec087005dae3437eaa1085a7005dae344a1aa10814700002ed71a1aa0a0146bb5c686fd5429508358bb5c6872b7ebc550848005dae3437eaa14884700002ed71ac3f5507c60062ee3437eaa14a847005dae3437ea106a347bb5c6b143923f550848
  | 7, 0, 4 => 0x5dae343582a108147bb5c686fd78aa108818005dae343542106a147bb5c69d437eaa1086c8005dae3437eaa1083d7bb5c6b1437eaa108148005dae343933f550847bb5c6ab437eaa108818005dae3437eaa110847005dae3407eaa140847005dae343923f508357bb5c686fd54210ec738005da86fd5421028047bb5c6b1437ebe950848005dae3435421028087bb5c686fd5429508368
  | 7, 0, 5 => 0xbb5c686fd54210a0488005dae3437eba950847bb5c686fd76aa14a848bb5c6bf43923f550848bb5c687407eaa13e848bb5c687247eaa1086c8005dae3437ebe908357bb5c686fd76b0d50848005dae3437eaa1086b700002ed71a1bf4a0356bb5c686fd5429540848bb5c68f437eaa108358bb5c6b1437eaa108358bb5c687247eaa108508005da86fd542106a047bb5c686fd542612e848
  | 7, 0, 6 => 0x5dae3437eb0d50847005da86fd5428108047bb5c686fd7d2a1086c8005dae35fa1bf550507bb5c686fd54295086b8bb5c686fd54210a0148005dae3437eaa0d8507005dae343993c550847bb5c686fd542106a2c8005dae2fd5421102087bb5c687097eaa108508bb5c686fd7d2a108508005dae2fd54210f8087005dae3438fbf550847005dae3437ea106a147005dae36aa1bf550507
  | 7, 0, 7 => 0xbb5c686fd76ba150848bb5c6b1437ebb550848005dae3437eaa0a0427005dae2fd78aa108087005da86fd76aa108047bb5c6bf437eaa108148005dae3437eb8950847bb5c686fd54210a0358bb5c686fd54210a04f8bb5c686fd54210d8148bb5c6d5437eaa108358005dae34376aa108147bb5c686fd752a14a848005dae343542210814700002ed438fbf550846bb5c6bf437ebe950848
  | 7, 0, 8 => 0x5dae3437eba150847005dae3437ebb508357bb5c687407eaa108148005da86fd76ba150847005dae3437ea8108357bb5c686fd542106a28800002ed71a1bf5da6c6bb5c686fd542612a848bb5c686fd78aa108738bb5c686fd5424508358bb5c686fd7d2a130848bb5c6bf437eaa108358005dae343a03f550507005dae3437eaa130507bb5c686fd54210d8358005dae3437eae950507
  | 7, 0, 9 => 0x2ed71a1c7550846bb5c686fd7d2a108768005dae3435429508147bb5c686fd54281086c8bb5c686fd76aa108508bb5c6d5437ebb55084800002ed71a1c3950846005dae3437eaa0ec50700002ed7188bf550846005dae3437eaa108687bb5c687407eaa10835800002ed71a1cc930846bb5c6b5437eaa130848bb5c686fd54210f8558bb5c686fd5428108508005dae34378aa108767
  | 7, 0, 10 => 0x2ed435421028046bb5c687247eaa108818bb5c686fd54210d86b8bb5c687247eaa1087c8bb5c686fd5428130848bb5c686fd54210ec358bb5c686fd542110251800612e3437eaa1087c7bb5c6bf437ebb550848bb5c686fd54210ec088bb5c686fd76aa1086c8005dae3437eaa1082c7005dae3437eaa1087a700002ed71a1bf53c84600002ed437eba150846bb5c687327eaa140848
  | 7, 0, 11 => 0x5dae3437eaa108427005dae34376b0d50847bb5c686fd5429508508005dae3437eaa108287bb5c6d5437eaa14a848bb5c686fd7d2a1087c8005dae3437eaa102507005dae3437eaa122847bb5c686fd54211027b8005dae3437eb7d50847005daeb437eaa1086c7bb5c686fd54210f87b8005dae3437ea9508357bb5c686fd54261083d8005dae358a1aa108147bb5c686fd7d3c150848
  | 7, 0, 12 => 0xbb5c687207ebe950848005dae347a1bf508357bb5c686fd5421102358005dae3587eaa1087c7005dae3437ebc550507bb5c686fd78aa1081a800002ed437ea106a046bb5c686fd76aa108768bb5c6bf437eaa14a84800002ed71a1a106a146bb5c686fd54295086c8bb5c686fd5421102148000030371a1bf550846005dae3437eae950847005dae3437eaa1026c7bb5c686fd5428108768
  | 7, 0, 13 => 0x5dae343872a1086c7bb5c686fd54281087c8005dae2fd7d2a108087bb5c687197ebc550848bb5c686fd54210d8688bb5c686fd78aa108358005dabf437eaa108047bb5c6873f7ebb550848005da86fd54210d8047005dae354a1bf550847005dae3437eaa108627005da86fd54210a004700002ed71a1b0d50846005dae3437ebd550847005dad5437eaa108047bb5c686fd78aa12a848
  | 7, 0, 14 => 0xbb5c686fd76aa1081e8005dae3437ebc150847005dae35fa1bf508357005dae3437ea10d8357bb5c6d5437eaa108508bb5c686fd5428108698bb5c6b1437eaa130848005dae34395bf550847bb5c686fd76aa108818bb5c686fd5429508768005dae343983f550847005dae3437ebad50847005dae3435426108147005dae3437ea10a0357005dae36aa1bf508357bb5c686fd5428108818
  | 7, 0, 15 => 0x2fd71a1bf550846bb5c686fd5d2a108508005dae367a1bf550847005dae3437eaa1081e7bb5c686fd54210a0428bb5c6bf43993f550848000031d71a1bf550846bb5c6bf437eaa1086c8005da86fd54210ec047bb5c686fd78bb550848bb5c6bf437eaa108508bb5c686fd54210d8508bb5c686fd54211026b8005dae3437ea106a287bb5c6d5437eaa1086c8005dae3437ea4508357
  | 7, 1, 0 => 0x5dae3437eaa0a0487005dae3437eaa108807bb5c6bf437eaa108768bb5c686fd54210ec6c8005dae3517eaa108767bb5c687407eaa130848bb5c686fd542106a348bb5c686fd78aa14a848bb5c686fd54210ec508bb5c686fd54210d8628005da86fd5429508817005dae3437ea10ec357005dae3407ebc550847005dae35ca1bf550847005dae3437ebb5086c7bb5c686fd712a1087c8
  | 7, 1, 1 => 0xbb5c6bf437eaa108818bb5c686fd54211026c8005dae3437ebc508357005dae3437eaa12e847bb5c686fd542106a14800002ed715421028086bb5c686fd5421102508bb5c6d5437eaa108818bb5c686fd5421028088005dae3437eaa0a0357005dae3437eaa0a04f7005dae3437ea1102357005dae3437eaa0a0147005da86fd78aa108047005dae3437eaa108737bb5c6d3437ebe950848
  | 7, 1, 2 => 0x5dae3437ebb550507005dae3437eaa108517bb5c686fd78aa1086c8005fae3437eaa1086c700002ed71b53c550846005dae3437eaa108347bb5c686fd78aa108508
  | 8, 0, 0 => 0xbb5c686fd54210ecf76b8d7e86fd54211eed71a1bf55084363ddae3437eaa108507bb5c6d5437eaa108e00bb5c686fd420d580176a1bf55084023002ed71a1aa108146bb5c686fd5429508f76b8d0dfaed54211eed71a1bf550a0423ddae3437eaa108357bb5c686fd5421028f76b8d0dfafa54211c0176b8d0dfaa82835dae343923f550847
  | 8, 0, 1 => 0x2ed71a1bf5e2a8423ddae3437eaa108817
  | 9, 0, 0 => 0x2ed71a1bf550846
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
  | 0, 0 => 0x319b0078db405fffc05ffff00ffff00ffffc00fffc001fff000000ffffffc000003fffc9f000000c97fffc000000e3ffff
  | 0, 1 => 0x3fc67f3ff827cff1990fe009238ffff3887ffce33990e21c9209419b09781b421e66c21e36d07ffff07ffffc1f01fc1fe01f
  | 0, 2 => 0x3fc7e73ff83cce71e7ce7e0ef38ffff38ffffce31e1ce3e0e3383f803807f80da1990da0092308664308724800066c01e06d
  | 0, 3 => 0xc9799bc900db7252003240000c94000c9000032020032000003fffff3fffffcff1ffcffe0ff3fc0003ff8000fc1fe0fc00fc
  | 0, 4 => 0x7800000c600000360f9cf87f9f838f3f21ff3fe01fcfc864cf8004b25206f25e00dc97fffc907fff253993241c92
  | 0, 5 => 0xc80000c80000304e66f05e36dc73878c700c7304e06304030cc03800c000c0000c66c01e36d00319b0078db400c66c01e36d
  | 0, 6 => 0xc9f99fc9f8dbf25ffff25ffffc9799bc978db725000325e000c93998c900db320e66f21e36dc83f80c807f8320e603200360
  | 0, 7 => 0xfffffffff8fffe7ffffe7fffff9ff9ff9f8fbfc6f873c6038ef9ff9ff9f8fbf3f00033fe000ceb9e4ce80dcb3fe7ff3fe37f
  | 0, 8 => 0xc70000c700003002003001c003686643687248da1990da1c923686643687248da1990da1c923680003680000c01800c01c80
  | 0, 9 => 0xffc000ff80003fc3983fc1c90fe8e64fe8724be0fe03e01fe0f80e00f8072031c21e31c1c1cc70878c7070731c21831c1c10
  | 0, 10 => 0xc709e3c77f1c7ffffffffffffffce7fffff27fff0003ffe000ffce7fffff27fff399ffffc93ffffffff87fffff3993fe1c92
  | 0, 11 => 0xf83f80f807f831ce1e31c1f1cc73878c707c70dadffcdbffffffcfffffff3ffff3f9ffffcf3f83f80f807f83e03e03e01ce0
  | 0, 12 => 0xfffffffffffffff0003ffe000fffffffffffffffffffffffffffc000fff8003e0fe03e01fe0
  | 0, 13 => 0x18300781841a01901a0012003fff0007ffc00000000000000000000000000000000000000000000000000000000000000
  | 0, 14 => 0x7f07f07f8c7c00c06000030c000000000000000c0000003000030000000c00000000000000c94800c900000e31e1ce3e0e3
  | 0, 15 => 0xc600000360000000000000000c600000360000000000000000c06000030c000000000000000c000000300
  | 1, 0 => 0x38c00038f8000e0de00e003e007c07f07f807c00c66c01e36d00319b000000000c66c000000000000007800000c66000036c
  | 1, 1 => 0xc9799bc978db725000325e000c9799bc978db720e603200360c1399bc178db4ffdffcffe3ff38ffff38ffffce3de7ce3e3ef
  | 1, 2 => 0x600000600000000000001c000000000007000000000000000f9ff9ff9f8fbf25ffff25ffffc9799bc978db725c66f25e36d
  | 1, 3 => 0x3000003000000180180181c1006000006000001800001800000000000007000000000001c000700780707070180180181c10
  | 1, 4 => 0x3686643000000da19900000003680003680000d81980d81c903600003600000c01800c01c803000003000000c01800c01c80
  | 1, 5 => 0x3ec7873ef838cfb0000fbe00038c78738ff38ce0fe00e01fe03807803807380ff1990fe1c9237c67f37ff27cda1990da1c92
  | 1, 6 => 0xffc000ff80003fa3993fa1c92ffce64ff8724be03803e01c80c70878c707070ff1ffcfffcff3effff3effffcfb1f9cfbfcf3
  | 1, 7 => 0x630600607c4000c060001f0c0030000007c03ff3f9ffffcf3ffffffff87fffff3993fe1c92ffc664ff8724bff3993fe1c92
  | 1, 8 => 0x31800007d80000000001c000630780607c701cc1e01c1f1c0630780607c70180180181c100630180600c30180000180000
  | 1, 9 => 0x631fb060000018018019fc10060000067800018c7e0181f7c00319b007fdb400c66c01e36d000000007800000c660001f6c
  | 1, 10 => 0x3000003000000dad9f0da1f9e3686643687248dac060da030c36b6643687e48da1990da1c923036183007e3018c7ec19ff7d
  | 1, 11 => 0x30379b307ffb4c01800c1fc8030319b3078db4c00000c1e0003037803007f80c01800c01c803037803007f80c01800c01c80
  | 1, 12 => 0x36b7fc3687ff8da1990da1c923637fb367fff4d80000d9e0003637f83607ff0dadf90da1ff23686643687248da0000da0000
  | 1, 13 => 0x3ef7ff3effffcfb0000fbe00036b7ff36ffffcdadffcc0000036866436ff248dac66cdbe36d36800036f8000da0000dbe000
  | 1, 14 => 0xc63860c607c43180183181c10c03818c007c3300c06300030cc00000c00000304e063041f0cc03800c007c03000003000000
  | 1, 15 => 0xcf7878cf07c731f01ff1fe01fc73878c707c731ce1e3000000c7387800000031c00031c0000c63878c607c7318e003181f00
  | 2, 0 => 0xcf79fbcf7fdf73de66f3de36dcf4000cf780033ce7e33c1f7cc9799bc97fdb725000325e000c93998c907db320e603201f60
  | 2, 1 => 0xc00000c0000031ce1e31c1f1cc73878c707c731ce1e31c1f1cc03818c007c3300e003001f00fffe7cff87e7bfff993fe1f92
  | 2, 2 => 0xc0399bc00000300e00301ff00c0319bc078db700000301e000c03998c007db300e003001f00c03980c007d8300e003001f00
  | 2, 3 => 0xc70000c7780031ce7e31c1f7cc739f8c707df31ce6031c1f60c73878c707c731cc6031c0360c0399bc07fdb700e66f000000
  | 2, 4 => 0xf03e18f007e33c0f803c01f80f00000f0000031ce7ef1dff7dc739fbc0000031ce7ef1c1f1cc73878c77fc731cc66f1de36d
  | 2, 5 => 0xf78000f780003dcf9e3dc1f9cf73e78f707e73daf9f3da1f9ef6be64f687e4bdae003da1f00f68664f68724bda0003da0000
  | 2, 6 => 0xf03f9bf07ffb7c00003c1e000f03f80f007f83c0de03c01fe0f00600f007203def9f3de1f9ef7b878f787c73de1993de1c92
  | 2, 7 => 0xf7bffff7fffffdee1e3dfff1cf78664f7ff24bde0003dfe000f73ff8f707ff3daffffdbfffff68000f6f8003daff93da1ff2
  | 2, 8 => 0xf97f9bf97ffb7e4fe63e41fecf97f80f907f83e3fe1fe3ffe3f83f80f807f83e0fe00c00000f83f800000c03e00003e00000
  | 2, 9 => 0xf83018f800c33e0fe03e01fe0f83f80f807f83e01803e01c80f80000f800003e0fe03e01fe0ffffe4ff87fcbff3993fe1c92
  | 2, 10 => 0xf83f9bf807f83e0fe6cc00000f83f80f87ff83e0c66fe1e36df80000f878003e0fe63e01fecf83f98f807fb3e0fe03e01fe0
  | 2, 11 => 0xfebfe4fe87fcbfafe03fa1fe0fe8664fe8724bfa0003fa0000fe3fe0fe07fc3f8ff83f81ff0fe0060fe07043e0fe6fe1ffed
  | 2, 12 => 0xff0000ff00003fafffffbfffffebf80fefff83fadffffbfffffe8664feff24bfac66ffbe36dfe8000fef8003f8ffe3f81ffc
  | 2, 13 => 0xffc0000000003fe1993fe1c92ff3f80ff7ff83fce1e3fdff1cff319bff78db7fcffe3fc1ffcff3f80ff07f83fce1e3fc1f1c
  | 2, 14 => 0xffffffc900003fffffc000000ffc000fff8003ff0003ffe000ffc000fff8003ff2003ffe000ffc000fff8003ff0000000000
  | 2, 15 => 0xffffff0000c03fffffc000000ffffff0000003fffffc000000ffffff0000003fffffffe0000ffffffc800d83ffffff04030c
  | 3, 0 => 0xffffff0600003fffffc00036cffffff0000d83fffffc000360ffffff0000003fffffc00030cffffff0000c33fffffc000000
  | 3, 1 => 0xffffffc000003ffffff1c0000ffffffc000003fffffcc00000ffffff3680003fffffcc00000ffffff3000003fffffc180000
  | 3, 2 => 0xffffffff00003fffffffa0000fffffff800003ffffffde0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3d2bf03d96fc057bfc0555bf00deef00cd6dc007bb40015b7000000ed329200000029e681f0000004931ffc00000062a5f7
  | 0, 1 => 0x3c03f03d807c000000000000001eed00056dc003100001000094112097012021040821804003deff03dd6fc0f00fc0f601f
  | 0, 2 => 0x18c38718e838c670e5c67e0eb18dfef18ed7dc630e1c63a0e3181fc018257804a0ab44a20b7109eed108d6dc6f0efc6fe0ff
  | 0, 3 => 0x1bdfff1bfd7fc6f0efc6fe0ff1bc1121bf81206c0ee06cc0fc
  | 0, 4 => 0x496112497092120840120824018c38718e838c0f00fc0f601f0000000000000050048054008001eed00056dc003100001000
  | 0, 5 => 0x482100482090125844925c248432038431087104804104420840200040008012f84fd2fe25f4973bf4971ffd25844925c248
  | 0, 6 => 0x49e11749f892d25fffd25d7ff496112497092125844925c248492110493092125844925c248483fc04825f81208401208240
  | 0, 7 => 0x5be3bf5bf8bfd67fffd67f7ff59e39759f8bad468a554662ab49611249709212f84492fe2484aa12d4aa895d25844925c248
  | 0, 8 => 0xa40000a402002903102901800a69eeda68f6de9a31b69a3817a41eeda4076de903102901800a40000a402002903102901800
  | 0, 9 => 0xa40000a402002903102901800a40c40a406002907b02901da0a40c40a4060029c31e29c581ca50c50a516022903102901800
  | 0, 10 => 0xbccfc7bcee38e9f7bfe9f7dbfa7cc7fa7de07e9f004a9f6808a54c52a55602293311e933803a41eeda4076de903102901800
  | 0, 11 => 0xec2d40ec269039cb1e39c5a1ce52c50e516823b5b54bb5da48bfcfffbffe3fef33f1ef3b8e3bc1fc0bc27782f03f02f098e0
  | 0, 12 => 0x200000200000004000000500fdefd7fdfebafbf844bbfea48ed7fffed77fffb5b54bb5da48ed6112ed72923b0ff03b09fe0
  | 0, 13 => 0x1ad3af1ae97dc4a4ab44a25b7129eed128d6dc4a4ab44a25b71280001288000484aa04805b410128010016800840a0080514
  | 0, 14 => 0x43f03f43d9c7d0cc0e10c471c432010431082108c0a10807144030004001c010080010002001292ad12896dc6b4ebc6ba5f7
  | 0, 15 => 0x5b21105b309216aceb56aa7f75aa1005aa890160ce016087e058210058209014ecaf54e67bf53b2bd5399efd4acab54a27b7
  | 1, 0 => 0x5be1125bf892160ce016087e05be13f5bf897d6fcefd6fe7ff5bf3bf43508216fcefc4b20005be1125bf89216ccee16cc7fc
  | 1, 1 => 0x5be1125bf89216f84496fe2485973925971fa160ce016087e05bf3bf5bf9ffd6fcefd6fe7ff5bffff5bfdffd6fcefd6fe7ff
  | 1, 2 => 0xa60000a6020029871a2981d14a41c40a4074029000029008005bf3bf5bf9ffd6ffffd6ff7ff5bf3bf5bf9ffd6fcefd6fe7ff
  | 1, 3 => 0xb40000b402002da7bb6da3db7b692adb68b6deda0002da2800b69eedb68f6ded07b02d01da0a71c78a7174729871a2981d14
  | 1, 4 => 0xb69eedb406002da7bb4081514b68000b68a002d87ba2d81db4b60000b602002da7bb6da3db7b68000b68a002d07b02d01da0
  | 1, 5 => 0xbec387beea38efb040afba840bcdfc7bcef78ef07f02f09de0bc1fc0bc27782da7bb6da3db7b7deffb7df6feda7bb6da3db7
  | 1, 6 => 0xb68000b68a002da7bb6da3db7b41ec0b407682d07b02d01da0a71c78a717472ff7ffefffdffbedfefbeef7defb7fbefbbdf7
  | 1, 7 => 0xe63c68e607c539cf1e39c5f1ce43c40e407c02fb7fbefbbdf7b69eedb68f6deda7bb6da3db7b69eedb68f6deda3102da3800
  | 1, 8 => 0xfc3fc0fc27f83f0f503f09f40f7befdf79feff9cf1e39c5f1ce73c78e717c739cf1e39c5f1ce73038e713c739c80439c4a08
  | 1, 9 => 0xffffffe756823fff5ebffff5cffe112fffa923fcffe3fcdffcfffffffffffffffceffffefffffe112fffa923fcffe3fcdffc
  | 1, 10 => 0xfc2100fc22903defbf7de7fbff7befdf79feffdec0e3de6f1cf6beedf68fedfdafbb7da3fb7f73ef8f717ef3ffffffffffff
  | 1, 11 => 0xfffffffffffffffff4bffffe8fff3bffffbfffff844bffea48febfedfeaffdffaffb7fabff7fc3fc0fc27f83f0ff03f09fe0
  | 1, 12 => 0xffbffdffbfffffefff7fefffffffffffffffffff844bffea48ff3ff8ff37ff3faffb7fabff7febfedfeaffdffa8403faaa40
  | 1, 13 => 0xfffffffffffffff844bffea48ffffffffffffffffffff19a40fffffffffffffffceffffeffffff3bffffbfffff844bffea48
  | 1, 14 => 0xe63c68e607c5398f1a3981f14e73c78e717c739cc0e39c4f1ce72010e71282394f143945f08e43c40e407c03908003900a00
  | 1, 15 => 0xe73c78e717c739f80ff9f6a1fe73c78e717c739cf1e3901a00e73c7802054539c80439c4a08e73c78e717c739cf1439c5f08
  | 2, 0 => 0xef7d7aef77d73bd844bbdca48ef6112ef72923bcf5e3bcdf5ced7d52ed77d23b5844bb5ca48ed3d50ed37d23b0f503b09f40
  | 2, 1 => 0xfc2100fc22903defbf7de7fbff7bc78f79fc73dcfbe3dc5fbcf7befdf79feffdafbb7da3fb7e73c78e717c7390f103901f00
  | 2, 2 => 0xfffffffc66903fff54bffff48fff3bffffbfffff844bffea48ff3ff8ff37ff3fcf543fcdf48fc3fc0fc27f83f0f503f09f40
  | 2, 3 => 0xffe112fffa923fefff7feffffff3ff8ff37ff3fcff43fcdfe8ff3d78ff37d73fcce43fccfe8ffffffffffffffffffffdda48
  | 2, 4 => 0xf7befdf79feffd0fb03d01fa0f42000f402803fffffffffffffffffffc66903ffffffdf7f1cfffd7affffd73ffceffffefff
  | 2, 5 => 0xf7a010f79a823defbf7de7fbff73ef8f717ef3defbf7de7fbff6beedf68fedfdaf103da3f00f6beedf68fedfda8003da2a00
  | 2, 6 => 0xfffffffffffffff844bffea48fc3fc0fc27f83f0ff03f09fe0fc3fc0fc27f83defbf7de7fbff7bc78f79fc73defbf7de7fbf
  | 2, 7 => 0xffffffffffffffff5ebffff5cfffffffffffffff844bffea48ff3ff8ff37ff3ffffffffffffffe112fffa923faffb7fabff7
  | 2, 8 => 0xfd7fd2fd77fa3f4ff43f4dfe8fc3fc0fc27f83f3ff1ff3bfe3fc3fc0fc27f83f0ff02d01800fc3fc04005c03f08403f08a40
  | 2, 9 => 0xff3138ff33d73faffb7fabff7febfc0feaff83faffb7fabff7feb3adfeabfdff8ffa3f89ff4fc3fc0fc27f83f0b503f09a40
  | 2, 10 => 0xffffffff77fa3fffffedb3800ffffd2fffffa3ffceffffefffffe112fffa923fefff7feffffff3ff8ff37ff3fcff43fcdfe8
  | 2, 11 => 0xfebfedfeaffdffaff03fabfe0febfedfeaffdffa8403faaa40febfedfeaffdff8ffa3f89ff4fe3d68fe27d53ffffffffffff
  | 2, 12 => 0xff2110ff32923ffffffffffffffffd2fffffa3fffffffffffffffffffffffffffceffffefffffe112fffa923fcffe3fcdffc
  | 2, 13 => 0xffe11212c8003fefff7feffffffffd2fffffa3fff5ebffff5cfff3bffffbffffcffe3fcdffcff3fd0ff37fa3fcf5e3fcdf5c
  | 2, 14 => 0xffffff0044003fffffc011000fff3bffffbfffffce4bffefe8fff13afffbd73ff844bffea48ffe112fffa923ff8449618240
  | 2, 15 => 0xffffff4045c03fffffc4b35b7ffffff12cc003fffffc4115a0ffffff0245453fffffe911800ffffff4864903fffffd055208
  | 3, 0 => 0xffffffa646003fffffd6dd7fcffffff5aedfdffffffd6197e0ffffff5864903fffffd4f77bfffffff4355c73fffffd0d5208
  | 3, 1 => 0xfffffffc66903ffffff9d5a08ffffffe446803fffffff19a40ffffffb6ce003fffffedb3800ffffffb446003fffffedb3800
  | 3, 2 => 0xffffffff76923fffffffbba40fffffffc66903ffffffdf7a08
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 50 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 50 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 404 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 404 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 404 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 404 then wireAt i else 0
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
  | 3 => 2
  | 4 => 49
  | 5 => 570
  | 6 => 1008
  | 7 => 475
  | 8 => 15
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xdc7e7507020a5389
  | 4, 0 => 0xff094118fa13f115e2c00436daf4ccc9d845be6bd6599d73c8b4fdd3c4fbf55ec47bc6bab6f1b0a2a49bf773a35315e39ef2a16c9b5567619a0d7e5f8f24fa2c8ca6c23b70f14c436da6742369220b08656659295ca6646853eb859b530209c452fc346150d02a0e4f87487e4efa820b4e35bab34b246af9461787ca40a156e63bbe889c3899e83d38800e1834dd85312c4b05662c0146d0246657c7244135fd22c91ef12124d1991d60329216e2db1615ca2fbc10882c080a942b79070e619e003c3d10
  | 5, 0 => 0x11fb74e311f45ea911c821b0116a87581168306d10bd421e108b3105106792b10ef548390e7bd46f0db432850ccf58020cc58a3e0cb6d1e10bd5dce90bc688930b7e952c0b4657820ac775770a8f48c109d0c57e09d0754409b8a79109a718fc099cda1a0922708f08ff714208ebe62108442f23083ca64d0823f604080335f307c93fb406fa4a3206ed9fc506616038064a514a064a1aee06307106062efed505b70abb05abc1db058adacd04ed297a04950c42048ec966047366b10401ab7403f6b91003d3407003aea7f40395bc07031dba3702e789a90269762b020592da017648a500e3021600c2176000b9a3dd00b2dc9700903b23007660d4002d2537
  | 5, 1 => 0x22ed54d222ed2e1722d41702221853502216623b21b0632821732b8d2169865720ecbca020bd424e20924f102074fcd120610db11f6e04b41f2586511ed32ef81e0daafc1ded76201dec05861cdef6471cc410b81c65b06a1c4c210a1c42d7171c37b7771c0516cb1bf750b41babfac91b8c51ac1b5300e41af6c21e1ad114311abf35371abc2e8e1a4e06791a3fc2e51a2f8ff21a1f0ef61a13e99e19a9e3c21926f56719169d331911b3c618f26c4c18ae189c17f3bd0717c6219b17b4fde4175d7c6f16fe03a316cb578b16a670351655fe68164903c0161016f015cdda5815bc22d8154b8fd4145fee0f134e1ef712ddb664129f3edf1274318012013e5b
  | 5, 2 => 0x357ae2e8356b27a534eec54d34d939fe3489f42c343096ad329ed0d9329258463257a96531f627d33156fc5330d00e6a304c697530378bbb30377924302b3ef92f98de682f9289702f55e4892edae5ed2e89e6012e80cd732e289d962df068002decef992db398dd2d89e6562cd2797e2cb22ac42c41c0112bac62dc2a86e1112a68a3f12a3198e0299c304b297e4c8929240ca929047fbf28d6964728b47f0628b0dc0f2848f75a2831914d281f411f27a9ba222798ce9c2775a7642731e3512717622c2705880d26c5eaee265184c225f712e925f66fed25be9e1c257d59b8255cc0792507acb52493f7db248897c02328289523132e5322f58cdf22f10a58
  | 5, 3 => 0x49ab509c497d28ad495caf39495b4db1492a59a148f38b2748621bd64843c42147baec8d47ae5c34477e821d475023e9471c279b46a895224623350345d6a73d45b725384574949345590e74449d9d2c444ac25f43d2fd9f4389d593434ac03243091b4242efcb4642e7ad3142d2ceea42b779a341bedc2941a86183419d83c5416e9813408a526e40398212402a13e13fb183a83f4ef09c3f44341e3e7501b43e2a4c6e3c72f8f73c3337063bf51afc3b536b673abe6baa3a792f6a3a325cd53979a0cb38e1164638bbbf8c37c3affe37b9be6e3761c3f337611281373b41c136b26c6836b01e88369f769f367ca0bb36040d1b35dd329c35c19396358f6bef
  | 5, 4 => 0x67bc3f5c6733942566fb1c8065cb8b296586cff764f3896864659dd063f9e42463f3cb9d63d9a5e763aaa7d863669d9562443cd861f5a73b618a6a10616068a1614e68166144942c60a9e5a35f7c9eb05f772fc05dbda7b15d1f8edf5bde0aeb5bdbb2565bbb72fe5bad75885a88f3f359c8e23859a0445d5998eb6059448a4a58e995d657a4a76c57a455c0579a8c285711b93d57058ade567d130c5652bba655c8d7ad54fc31ea54114e7b53fe39fb5318541d51c3d9c051b443d551b1ea8851afd6d85164bb37506c7ad0500fa0b04f86259c4f27ed514e81933b4d1acf0f4c7acf5f4c72cff24b228ca14b093b3e4af336034ae0bcd24aa242e14a34f315
  | 5, 5 => 0x7caef41f7bfd68427b9fed3a7b6c9a927b609e247b3f90937b14bd9e7afb729a7a20f03779019a1d78bd6f8177efc7c2774de09976c54e7e76b57f7c7606145c75b7ea5c751e0f98750f72cf74efb63874b3d62c74b31014739705457388d4bc738810d373788e1d736b2712735b0e257338ccfa730c7bc772e18a9b72d0fed1722280a5720efac671bad8767196e991717e14fb717aeb7d714eca07711d96fc70df9c5f70de2b6570c4cd537083b44a70260ef66f9408c46f4c48f66e9359986e5661bc6e2f9b786d66356b6cca45826c6a3bd76c52c08b6c3d1b7e6b9e12da6b4e00bb6ababa2c6a37315e6a30f6996996f1236913f13268e3173e68076924
  | 5, 6 => 0x9de5c1829d739f979d302a159cc3eb289c8064269b29479a9b0f3bbb9ac0defe99c2574f99591aab979ccfd497497af19736b29e9719d31c95c9f32995c1b345956975f494c9b8bd942de4f0937c3766934ad3df92fa59589278c53991ed703c915c2b4490baa361908897c1903798938fa0b8628c0d1a1c8c053a258adead688ab20f1589e7431289c80319897431fe8934bc8a88e77e7388d3033388b1c642884799cf875d23c7859c0f7c859309478557628184670fcc8430e02983cc75a883c0be0983b8ce7a8349acb8831d6c2c828922a9824504b08229ac847f5a80f67f2d20827f24c13b7f0741177f013b6a7ec02ce37d9bc8f67d8ecad87cc2e4d8
  | 5, 7 => 0xc649ebf6c4ec1310c3a2f9c7c33f65e7c28555d7c24cd4dcc14997dcc13e8e2abf8705ebbec26037be76e8d0bbec3344bb1c0433ba88bda4b9db5cfdb7aa0c84b7610a65b598d2feb5406affb46eb9a3b4105733b3d82589b31f866fb2557659b25188beb24f00d3b1ff95c3b1a3e438b1a3671eb19d22c1b149ef60b143fc31b065425bb052e84baf4ed27badf6df84addb5324ad6398f5ad148ffdac25a728abc3113dabad9d3baba9f353ab8bcb77aa879d64a8642789a8109a26a7190249a685bbbaa5fad8b7a5d9d369a57708b2a15aafcfa1448a91a10778e3a0b7fc57a03a41aea01d11f7a013d1da9f97c5979ef63e2a9ed1c1b29eb8c0059e9e8115
  | 5, 8 => 0xff3907cffa755b5ffa401789f9acd0faf96feb04f89a03eff899168bf863ef6af6fd9e68f5a67f8bf56457eaf44f92d4f447d0bef1c0a554f0f8df95f0d92f0bef7c3c3deccbf01cecc12505eb5a3525e3ef73cde322b518e207e790df644aeedf5048d4df0cb9a5ddbdf96edcd73064dbbf41e7d968302fd832dd31d8265658d8102e57d7783301d55d8dbfd2294a34d2061043d1e1314bcfe56affcf56485ccf45a100cf092a22cf02bcabcec7a0b1ce14f68fcd786ec8cd0d552dcced3e11cc7a0e9ecc0bb236cbfe463fcbae7febcb9c1072ca5180ccc9c5f187c8bcd3fdc73fff91c6a8014f
  | 6, 0 => 0x96a781f0941c54b0932006208f0123c08c00bc908b0816608683c45086725540848694b0815b7f907d530e907ba286c078f1e53075d2466074eba9407246e59072385510715437d06e5daf306e4ef6406b5fac606ad70f9069bb130068a399a0644c9230617f3be05a9e53f058ce34a05687e8905169eb004d32ad804c9880c04c021da04b12ffb03d8385d03ae4e990384d118035eb4ec035765580341d11b033b05b5033a727c030d3b3003087e0402faa3c602d6a72e02c1685702898f5e02734c9f022ee80801e3cad0019c9fad0185f46d012a5840011f27fd011eaa2f00eff69600e3021600ccfaeb0082d9db007dbb7a006c2684003e83f900285078
  | 6, 1 => 0x1327faa1129f3edf12324797121558d811d640d011b4bd5b118eca211187183a11804b36116b47241161181a1142fa4111408e9a1137d80a110f8d8e1106ad5710bf6ca6106ef598104ef361102d4a7a0ffdfe370ff073950fe0ac610fde41e30fcb33c20f9550a90f8e38f60f79f41c0f78ea770f115ba20eed14a20ee271f80e7e15130e737a980e67dc250e5682a60dfbaa4f0ddd4aa00db432850da6941f0d9cbe430d4430e80d1412f10cd4b54f0ca165b80c8f5e1d0c8c4ccf0bd5dce90bb7fee20bb2ffb10b88cc090b5334f40b3c22580b2c8ce60b28f6400afb5dd30af23e1b0ab8b2690a7677f50a53c4d60a2deef809cc529509bdf0a0098773d9
  | 6, 2 => 0x1c5377201c0c1b4b1c0aecba1bd1fa481bb1776b1ba64fad1b9d622f1b8548e61b78d4bc1b61a0cd1b42406d1b3ea0591b27d2611b1e87e21b059d2c1ac6cf551a888b681a8148131a04d9791a03291619c2b1f019774199192a0dd619224d721921f28d18ac994f1882b169186c388117f938b617b77a52175a929b1731a087172938d717135e9f1712096e170165611673385e16528f35163fa58d163cc6661611817415f4eac915f3a94215776f951561a43a156020141517feab14d6eb7414c37a0914c15aa414b9a6ad14696ac21461a2571437977c1436a4701415063f13ea83c213e0e2a713d6d81d13967e2f1349e7ce133c08ef13346ed11330db9c
  | 6, 3 => 0x2752ae752751de462713cf0026e9fa6926bb2fef26b886cd26786863265363bb263faf6d25eb7b5225a00ed52581e5702581dd4e25494af524cc78e0243971d5241d33132416c07e23abbd1f2359c6d0233e51982325c90b231de27b22dd669422c73513228802542202198b21d8db47218ce6fb21730a3e213bddeb20e7b2b020e249a720a84c14206bd0132064873a2062e284205b0a2a1fc5a2fc1fc4f9a61fb72b911fa432931f3387171f0c9a181f05df5c1ecbe4b41ec0fa371eb6c6781e7be0ab1e4008941e3a97551e2780c41e003ae81df83a6e1de886c51d826c881d73f5661d3110c21d2d215e1d0d4e0b1cf670511cc101ab1ca0b1831c5d3d53
  | 6, 4 => 0x32845a41326bf53f3257a965323ebfbe31f5eab331f21e3331eba44231b1ab293176335b30d5282030be0b3130b1e59a30a760753093efd2303564fd2fc5bf282fb10f502f8f1ff32f6745e12f3c81e32f20329b2f1abea52f15a0e52efbd9642ec68d272ea523322e9c408b2e8fba352e8108342e4975d52dfdbfd52da94f942d8efa482d618f3b2d19df392d14647b2d06d0c22ce3b7132c3e81882b6e1af02b26d94b2ac54d632a430f592a3dda1c2a3198e02a14d0f72a1317a029e188d329af2b642992b932298f705629740e86294399dc28d6af5928c73e9828c04ce028b131852857f16a28483606281a4d9f27d3a37327b3f541279d6c64275958f2
  | 6, 5 => 0x3cd948b53c4016173bf021da3be497a23bd6ad1d3ba7c5f03ba5ac113ba1e58b3b9031bd3b34c0e23a63374c3a5085363a4fc2063a4cde683a2d6c623a16892639ddbebc39b8a2b73965a15439514ff139463aca388a7a143821da66380d7bfe37fdfb7837d8b581379db3ff37596ec3374e2d4036fb367836de7a8736cd76be369e286b366fa272366487033619ea8d3609387935fed77835bf14c3357bed92353aa3c635169f3a350b1e3b34d88c5e34d2fbb734ceb8d134c7ff3c34a771a7349995fb3492c5e83481cae4347c735e346f2328344da1393442a8cf342f69f633d93c6b33a8219a33a2828e339be83033864f1f32e16b8932def36c329bda81
  | 6, 6 => 0x478b713d47608682475023e94700cb0e46df279b46dd66d846d0e8cf46ba5dbb46b55adf469949b546769a764631f358462000d2457a615d4526b408450651ef45038a9e44f4548e44ecccfe44c937f044a429bd43aea1a443686f9d43555fb0433f660a42ef746f42b779a34288da784270b5be41eef09a41d22c9a41ada2b441a861834170bcbe416eec4f416e981341320659412e341e4119dfa1410d769640e7b61440d845e240af69b240af336a40936de14062ec424041a8df4028922d3f2cd2183f227ddf3ee746153e0ad2fb3e0954d53d946b583d820b7b3d68cdf13d64e4c33d60158c3d5a97a73d4903cd3d2c7c353d2562093d0124c93ceb9565
  | 6, 7 => 0x5551c8e554f0504c54e2c70654dbf01954d391cb54a9557c5423d3be536a150752fd2fd052f9f55b528d48c35281620b525d9d93522a087851ed22825160844351501bab512a0a4a505beeb35059633d503dadbf501f9e514ff9d5294f9d1e774f8c57c24f86a4154edef3a34ead7c894e7855394e6d16534e1717654dcf02ea4dc9c7c04d84259f4d1acf0f4ca859dc4ca1aa074ca101584c7463374c4c79c44c2f2a6b4b9af8c44b77d19c4b2472944b222bf34b093b3e4acdf8d54ab9d7494a63a2644a530fc249eb066449e3bfbd49ae95204973f4c7495caf3949585913493ccd6c48c35a8b488ad56b47f8fbc847e9072d47d7f35a47baec8d4795ee6d
  | 6, 8 => 0x64b153c164aa6b4464a0c73f640e6da163d9a5e7638acc66635964b26319bcf962dfa08f62623a35623d0ac261f427ee61ab00a961176eed60fbe7f960f47f6c60d62fb160ca36e160af76616042b3645fd7d1ae5fc559925fbac6fd5fa001255f871fd25f4ce3e85f205a9d5ef0b1fa5ed985675ed6a3f15e2768cf5e0843465debf6475deb71af5d7d6e2d5d71535d5d1e66bc5cde0cce5c8bac4c5c1f443a5c1e7f7b5bfb9d265bdee7215b26580e5aea31985ad4f9385abcb8a95a8bb72c5a1dcce559e9114a59aa952c5978becb591e47e658e6c546588ac93558739c60583d5a59580611d556f13b0e567c7f5156318d585618ad1555739b7c555d1ca2
  | 6, 9 => 0x73f739d473e9209c73be3a8b7361e71e73170721730cc97a72f1b40272957302726a4e0171f3b43571d8f93471d3d74b71ca317b71a7da9771a262417108872f70eea42e70b1e101705b5d9f701fd2906fb9b8376f6a8dfb6f567eab6dd08b0e6dbfabf96da2ccf46d8815996d7e78d66d76e7956d66356b6d4a622d6d483b2f6d2a833e6d26125d6c4b6e046c3d1b7e6be9fecc6ba0f1c86b9d976b6ababa2c6a14d42a69b37b9c69ac57256996f12369148b6868ce740b6885fcc06854735f684a9053680cb64d6741623a673f974f6733942566be8369669a488666596eea664cb0966633371c662ac0886624d4f66623177d65f140fe65381a0264f38968
  | 6, 10 => 0x8123ee8880e85af480b1b4cd808528c4805eb719805e0fe9805c90737fd11f437f8776eb7f64ffd37ef775487ed513f37ed1cb467ec231f37eadd0e57e912cbc7e4b58517e1a8a567e05acff7dfb85ac7de29e817dd747b97dc594b27d57f1e27ce7e2b17cb560537b40cbea7aea77727ad3415f7a5b787a7a2bf43679df051879d3e13a79c02f7279be6a98797abaaa79717a8d797004af79684f62791c1254785ca3c67850917f781b6dbd7819d38577d135d077ae3ab0778424c277382d2e7707b5a176f0de3376e1a5f076da66f9768e81ea766e04be764e5f61763744917626fba57613d46a756ef7e9756aa4d474d57dbf74d3d2e07474155474068ac9
  | 6, 11 => 0x9608f40394ad8e5d9405ef3093e249939365df5093602c469322c34692bb0e5892904ad8924b56d4922d875892002a6a9176ae5f91592acd9066fa26903730749033dd689022657e8f74f0a98f4a16428f35c5428e965ddb8e27cd4e8d72216c8d32e83b8d1d99c48ca14df68c51c7138b607b078aa44b2d8aa3b04f8a553e488a4b2c568a0b34fc89b9a4c589b52b5089a8e63589118b2d88ede02888e77e7388a4fc21886fedcf8803a86a87e13aa087b2ceb487a8492f874f9269873abea486bbbf68867726a1865cbae8863f7c59862ff1338625e7dd85c55edf84e9742a845d1c66843db0268388b19f829ec1d68298043b826736178229ac84818c8a24
  | 6, 12 => 0xaa1f6e87a97aa236a9762739a9679bafa8fde80ca8e78fc4a8afe02ea798ccf5a748d152a6fdec6ba6c282b6a6910249a685bbbaa61dcadfa5f8bd8ca5d7b751a598068da55beef2a54a6a95a3c1ab4ba3a56a26a34731dba33926f8a3257e1da3098384a29e4ecda27ea81ba2602c83a1f16defa1662bafa1521c33a13c87fba0dcb925a0c59c23a099d7c29fce48649fa7e8e29f7298a79f726bb59f3cb69a9f307a4a9f22e88e9f0c76639efaea139e93ebe99e56566f9e519fea9c20d3b29c1ef4619be41d5a9bd198379bca9a899bc7f7b09b74bd5f9b34b1219af887159aca79e399f80ac6998cf53c998829a397c54e4097a4f38797708ba597012b84
  | 6, 13 => 0xc398766ec395a7f7c3628329c3606443c3432490c337f1aac31a15fdc2afde01c2a091e1c28555d7c219e413c1fa1783c1ebf1e0c166fc71c0769ef0c0171c7cbfa41077bfa1f555bece32d5bc7e8f37bbe3d513bb779f5abb11473fba423037b9e29b05b9df8830b99d8907b8d90467b8984defb79ef288b78864c3b751bcc3b6be7634b63ee375b635de6ab4968ca0b3ff36d3b37c045eb365558ab31e2f22b285abbdb24f00d3b1eb36f8b1b8bb56b1aab58bb197c2ddaf777a6aaf73942eaf715ab0af224626af05cc12aebb3672ae11518cadf1a5e6adc4db54ad9c65faad3b090dacedf7dcacb5a4bdac54c35babe5308aab89854eab559622aafef900
  | 6, 14 => 0xe07b344edf60a9c0de9d2c44de4eb049de17a701dca23d94dbce5bdddb83fe16db4f33a9da60bae0d87f9952d85d0165d7c4b6a3d78c0afed76e7147d6d35949d64c9b36d5f3eb55d568b144d44635d3d3895d08d361b26fd2f75b26d2c6073ad2aeea40d2702ac5d231461dd2294a34d2061043d19a03c6d1816a5dd17bf5cfcfaaeb5dce8ab657ce74d1cece1ee8e6cdb0a1f9cd786ec8cd28ef85cd13336dcc3d2a65cc1a159bcbb9f257cb22d64bcb1e4e07cb09853fca5d1f3fca5180ccca3191cfca0808a6c9f4ae78c996b3b6c89b91e3c86c0ca2c85e0905c82aa73ec7bdffc1c75d9bc3c6990989c63e6ab8c5382f90c5368674c4597455c3ad5c8c
  | 6, 15 => 0xff98826cfd9b65b0fcee7b04fc82fc20fb4008c7f9b99d75f89a03eff886c565f7e68aa8f755edc8f74f43f7f69a966ef61ecacef58f108cf2c41b18f1ea6d7df193a1eff15a4793f02597d4efdfd1c7ef831902ef459853eec40f0ceebe9aeaee622b56ee365bcfecbb97f1ec07bc21ebefca4beb9a6ef5eaf7f023eab31e8aea5f1dabe9e8d9b8e82d725ee5eea4cee5e351dce504ee61e3ecf174e35f01f3e2ee6b60e2d81aade280ec37e277b2dee195a639e1151f08e0b85344e0800c8d
  | 7, 0 => 0x183e8305181aa94117d07b0016e8db1816b50ee915ff8a4715f86a801561a43a141a4f1c1415063f1413d60814121a0c13b5da6d135211a21317dd2b12b8ab4112b8884a124e26351232479711d7480611b4128d119811441187183a11761aa81134c93410d1aa960fc22fb60f8898390f79f41c0e783ebe0dfb96ef0db675560d91ebc20d61f2fb0d52c9a60d4d98860cea20e10cabde0a0c167f100bd753a90b989d440b41c7720afb5dd30ab7b9ae09ee1b6f0878675807af559e06ecbabd065223ce064612c7059e8b1705869eb103e36454036df150033a727c02d5abde0296f579024a740d0198251c0129b75501013f360086a50c0064991500103def
  | 7, 1 => 0x2cae27f22ba0a43a2b48380c2a7c852829e942c4291abe5628c04ce02889888f2774c4602752ae752727707326e36c2426d2458e26beaf6f26a4b5bf264ea12126396ad4261c309d25bece64259eb530255ffecb246ade96246554a623fe6fae23afce92233e519823038dd422c7351321e9d24d21a5f96820df43cc2081cc612064873a2046aaad203e530f203cd04e20292edb1fd3d3851fb72b911f3d31db1ee4e3db1eb3facb1e8eec381e1aa3ae1e17d8601e08e1531d989e101d81c57f1d73f5661c53b96d1c1ffead1bea35011bde45011b8548e61b78d4bc1b325a461a5d39541a2bfa9c1a0dc40d1979f4171923eb0b1922d7aa1900f42918e3fb0a
  | 7, 2 => 0x43cee64d43555fb0434ac032432891ef4309ffd842b779a34223bdb941d9fb7841a8390641a4b5d6405c8f3d40455b7a3dff89d03dc32c533d8620523cedcf813c9f3cdf3c9dc2fe3c3d49423c39fd5e3bc2d8a43b5624293b3c318a3afd7b253acd3e823a8b1a653a861c993a4766343a305add396f572d38ad846e3899ed1837dd7e80375fd1e83732d33a36e4026d36ad51603678c0eb363c57f436224d1b361b1af435d89aaa359aee6d357bcd573518dab1342cdee932e7627a315024ba31381b073129ad3f30ccd1eb2fc976f62f7655c82edbd6b52ea0b9112e9e70832e9c408b2e46479b2de85b922d6df75a2d014b912cf3c0ef2cf085992cb7e269
  | 7, 3 => 0x5f2a63495e90082e5e06e6065debf6475d9647d45d93d62e5d7bf2db5d3a46645d2e415c5c91de815b2acd595af03eb05a73054d59d66aa05943cbfb5916f56258a5f17757c3519855df5df85592bd7c558b8750557f4cd954ed1c7553169294531505d8530ec13f52acbe7d528ca242520a3fab51d2062b51a4e007516924ff515c2919514aca6d51007c3a4f717d1d4e9d19034e7327324e1db72a4e00c0ea4dd111674cfd734b4cd8ba054c4c79c44c173de94c1326ad4bf147df4b62f61f4b40518f4b02825d4afc5e1e4ac0774d4a6707154a0d197449148db048f889f848f0bd7d48ebd2aa484e6acf475141bb472e33c145179a8f44d9dfff44cd758b
  | 7, 4 => 0x7dfd47397db1e1917d33ff317cd372a07ab597257ab2c9087aa157477a09890479a4d76c7900675a78925775785a178978493a7f77d135d077211a3f76f0de3376f0916b76eecc3f749b988673a1eeb773227b8e72b28339727daf3d72739f547260e48f721cd83371be65bd707cee8d7005f1236fa6c90d6ebe77696e1ad9ba6ddedbb86db8095f6cd622c66c8fa51c6be1bd3a6bcb63fb6b6909ce6b46b4d16b1be3666af785736a7ff6686a5eea176a510b386a4fc62d6920920f68ff5c7d67f1c0d36709aa61668c477066742ba7651506a464ffcc4e64cf00c5645092fc6401590263275f1562b43c176292bf226284e04362623a3562542af86129ea29
  | 7, 5 => 0xa9cb11c2a9647ee6a8e78fc4a8d69abba36baaf7a2f4f716a141bf779ffd08839e6bbe4b9d3508f49985b80798d8396998553ede97a5128c9721f5ed97012b84965f3458965531e6955a08989396353d934043b8927a567e925c0be491b98d1291426eab906d26119011f5828e35cdb08d7f04bb8d1e3ac28c76bee98bedc1998bc68b508bbc73f08b8fda438b308e208a8bfac78a18c288897643b6881ad299876b320387080352869b7594868cb4248651842c862851b985f48e9f85e99b5485520fcd8549f6d285210b03850f030e8492c7cd83f048fb838341f482d3eb9982739f207fe35f827fc0036d7f5f0e0b7f27d8097f1797dc7e8559377e05acff
  | 7, 6 => 0xe2cd10cbe07b344edfdba1afdf7fbf91dede789bde1b0bb2dd547ea2dc240579dc050cead8f62b1fd8e7dfa1d7d8277ed7c2c847d6890d25d62ad27fd5d7c256d58853add3c1c38ed355d4ffd229a3e5d1d3f658d1b38e6dd051c79bcf9551ebceecb93fcecb96dfce6b8b90cd5fbf4fcc0b8b0bcb46a5f8cae6d7d7c9e65a89c7a9b843c5c226a0c52f7576c4605fcec3935453c1c6e06ebfa41077bef5700abee065e9be4be64fbc5e25f5bbec3344ba2399e2b7610a65b713f0d0b69fded2b65f3e8fb59a84ddb2f03ccbb210ca3fb1b17014b0ec7e1fb0480e0daf01b67aaee65ee3aec64c0eae5c9576ad85a160ac23afedab681b8eaa3f12b1aa38618d
  | 7, 7 => 0xff5a28fefe12eeb4fbefb591fab495f5faa130d0f96feb04f8b72109f734b506f646c3bff637ead7f50771aef32a1730f11d8484f05fc8f2efeaeca8ef0e3eb4ee6bbfe2eb7a065aeabec0cdea72c195ea39f55de9d3bc26e878be20e7a75556e575a6eae3d420a8e2f02cff
  | 8, 0 => 0xf2854adfdd9de376bad4da24a6563cc3a1f16def5e22a75455df5df851bb2a0f5059633d4aee737942b779a33e277fff2eedfa851e7359ed1729918f
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x800c96114132140000000d441441301
  | 4, 0 => 0x10840080000470412544040000000000004144040000118324c83000011c6048410100000000000008c1040011832541321000000000000101103000000000020440800700c9504c84000000000000320410000000051081202000000000040440c0000000510812020000000144204808000014c4248130100000464c9320c040000000350412010000043544304c04000000051081203000000000020440c0000000421002000000000000434408000000051081202000000010510480400000000010d10300000000002044080000000510812020000036540420c000000000001091010000046485210c040000000000c8104
  | 4, 1 => 0x1181044030000000000004044080032584504c840000000001051048040036098104404000000025105104c040067041454404000000000000320410000010415500300000000000020440c000000000081102001d8325413210000032584504c84000000046041100c0000460981044040000000464c9320c04000010951081301
  | 5, 0 => 0xc000000000000002000000000000000800000c1254c0300000000011510080400000000000000300000000d4204804000000000040100000000011510080400000003548020100000000000000040000000000000020000032494310c0000000002048020100000001142048000000000000811020000000000000004000000045081200000000000000000000000000000000300000000000000040000000000000000000000115200804000000000000004000000009510080400000000000000200000000d5100800000000000081103000000000000000c0000000000811030000000000000004000000035480200
  | 5, 1 => 0x32541320c000000041454403000000000000000008000000000041101000000000021040c000000000084103000000004110080400000000010110300000604c8200c000000000000000030000000000000008000000025041201000000000000000400000004548020100000000000000080000000454c92010000000000000010000000000000002000000000000000c00001181044030000000260d5104c00000000000000003000000000021040c000000035041200000000000043440c000000000101103000000000000001000000000010d10300000000941048040000000000000000000000000304404000000051081203
  | 5, 2 => 0x852108000000000000000010000041055400c00000000015480201000000000042440400000002148420000000000000000100000000001051010000000055300804000000000104100000000000000000800000001044020100000460d5104c000000000000c010000000000000000080000000000000000000041055400c0000000005010c2000000000000000000000000000000002000000000021040c0000000000000040000036141210c00000000000000004000000000000001000000000010d102000000000000000c00000000000000000000000000000040000000000000030000000000000008000000010440200
  | 5, 3 => 0x115214804000000000084102000000000000000000000004508120000000000002104080000000214842010000000095300800000000025041201000000000000000c0000000000000040000000144204804000000000081103000000010840080000000000008110200000000d5100804000000000000002000000000000000400000000000000200000000951008000000000000000040000000144304800000000000000004000000014c2048000000000454c8201000000000000000c0000118504c83000000000000000000000000053081200000000000000000c0000000104402010000000000424404000000035440200
  | 5, 4 => 0x8000000000000000000000011530080400000000000000000000000000000100000000254c0201000000000000001000000000000000200000000000000000000000000811030000036055028c0000000005108120300000001151008040000000304c020100000000000000100000000510c12000000000000000010000000000000003000000005520080400000000000000000000000000000100000000304c020000000460c9320c0000000002544020100000000c5310804000000000000004000000014420480800000004348c201000000011410480000000004348c201000000014420480000000000008c104
  | 5, 5 => 0x100000000000000040000036141210c00000000045402201000000000020440800000004544020100000001052108040000000000000030000036494018c00000000000000004000000000000001000000000010d1010000000000000008000000035440201000000000042440400000000010d10200000000000000080000000510812030000063081200c0000000002048020100000000000000100000000000000040000000000404408000000000000004000000000000000000000004508120000000000d4104804000000000000003000000014420480800000000000000300000000d5100804000000051081201
  | 5, 6 => 0x3000000000042040000000000010110200000000000000040000118104403000000000041100804000000053081201000000000040440c00000000010d103000000000020440c00000000000000100000000812008040000000000c11010000046041100c00000000000000003000000000042440400000000000000000000001151008040000000001011030000000000000004000000010440201000000000040440c00000000010110200000001443048040000000001011030000061081200c000000180324c83000000046141210c000000041254403000000000000204408000000010440201
  | 5, 7 => 0x21040800000002504120100000000000000000000000254402010000046041100c00000000000000003000000000000000c0000000314c420100000000000000080000000510c1201000000011520080400000000000000300000000002044080000000000000040000000115100804000000000000002000000000020440800000000010d1030000000000430400000000000000001000000000043440c000000045480201000000000000000400000000000000100000001151008040000000424c82010000063095018c0000000000000000300000000000000000000000000000020000000000000000000000000000004
  | 5, 8 => 0x100000000324c82010000000055300804000000000041101000000000020440800000000008110200000000001044040000181320803000000032541320c000000000434c42010000000094304804000000020480200000000000000000c00000000008410300000000c13008040000000001011030000000000000010000000000000004000000000000000800000000000000400000000943048040000000000000030000000094304804000000045081200000000000000000800000000008410200000001153108040000000000811020000000094104800000000021484200000000000020440c00000000010c100
  | 5, 9 => 0xc000000000000002000000000020440800000000000000100000000d42048040000000530812000000061141230c00000000021484201000000008120080000000000000000200000000d42048000000000214842000000026041100c00000000000000003000000000000001000000003504120000000000000000040000000424842010000035108204c0000000000010d10200000000000000100000000000000000000000000204408000000000000002000000000043440c00000000000000200000604c4100c000000000434c42010000043144304c00000000045002200000000000043440c000000000000004
  | 5, 10 => 0xc000000000101103000000010531080400000000000000200000000004344080000000354402010000000000000000000000045402201000000014430480400000002048020000000000c13008000000000000000040000000000000010000000000000003000000000030040000000000000000400000000c93208040000000454c920100000000000000040000000000841020000000000000010000000000000004000000014420480000000000008110300000000953008040000000254c0200000000000040440c00000005108120100000000000000000000000254c02010000000108204800000000000000004
  | 5, 11 => 0x510812030000046095018c00000000000084102000000000040440c0000000000000020000000094104800000000000000002000000000000000400000000000000100000000004144040000000000000000000000115314804000000041441201000000000040440c00000003544020100000000000000080000000000000020000000000420400000000000081103000000000020440c000000045041200000000011530080400000000010110300000000000000100000000000000040000045094104c00000000025440201000000000040440c00000000008110200000000c9320804000000000000004
  | 5, 12 => 0x852108040000000000000020000000115200804000000000000000000000000020040000000000000000100000000002044080000000421002000000000115320804000000000101103000000000000001000001181044030000000000411008040000000000811020000036416104c000000000414412010000046041100c0000000000008410300000001141048000000000000000010000000000000008000000000000002000000000000000c00000000010c1000000000041100804000004125440300000000000040440c00000000000000000000000002104080000000000811020000000000000004000000045440201
  | 5, 13 => 0x20440800000000010110200000000c93208040000098058c0300000000000000000800000000008110200000000c93208040000000000000040000000144204804000011805840300000000000042040000000000000000100000000000000100000181310c0300000000000000001000000000010910100000000953008040000000000000030000000094104804000000000000004000000000020440400000000000000100000000d42048040000000000841030000026016100c0000000000010110200000001152108040000000454c42010000036055400c00000000025041201000000000020440c000000000109101
  | 5, 14 => 0xc93208000000000000000040000000000100400000000025440201000000000020440800000002544020100000000003044040000000434c12010000061141320c00000000000000004000000000000000800000981044030000000000c13008040000000454c0201000000000000000c000000045440200000000000000000000000000008110200000000c53108040000000154c020100000000000000000000000154c0201000000005520080400000000000000200000000c1300804000000010440200000000004110080400000000000000100000000002044080000000000000010000000000404408000000000000000
  | 5, 15 => 0x9410480400000000010d102000000010d304804000000000108100000000000000000c0000000000811020000000000000000000000000081102000000000000001000000000000000300000000411008000000000000000010000000000424404000000000108100000000000000000400000000000000100000000000000040000000454c0201000000009401880000000000010d10200000460c9320c000000000000841020000000115310804000000000000001000000010840080000000000000000100000000001044040000000000000040000035094104c000000118104403000000000000410400000000045041200
  | 5, 16 => 0xc130080000000000008c104000000000000001000000981044030000000000002044080000000314c420100000000852108040000000104402000000016500100c0000000000000000300000000004244040000000314c42010000000000000008000000025440201000000000043440c000000000000000000000008d23080400000000010d10200000204d5200c00000000000000003000000004110080400000003504120100000000411008040000000000811010000060484100c00000000045440201000000000000001000000000000000300000000000000080000000000000020000000041100800000000000000000
  | 5, 17 => 0x1153008040000000324c820100000000c93208040000000324c8200000000000000000000000000000000100000000000000080000000324c8200000000000000001000000001044020100000001151008040000000001051010000046041100c00000005940040300000000000000001000000004544020100000000d41048000000000000000030000000000000008000000000041101000000009530080400000000000000000000001143248000000000254c02010000000000000000000000000000004
  | 6, 0 => 0x43440c000000000000000000000000000000800000000008410100000001143048000000000254402000000000000200404000000000000002000000000000000400000002540e20000000000d42048000000000324c8200000000000042040000000002504120000000000c1300800000000000109101000000000000000000000000008410200000000c93208000000000000c5101000000001632080000000000000000200000001140188000000000350812000000000000000004000000000000002000000010820480000000000000000200000000004004000000000000401010000000000000008000000000084101
  | 6, 1 => 0x210404000000035041201000000000000000400000000000000200000000000000080000000324c820000000001442048000000000510c12000000000000214404000000000000000000000000000000c000000023085200000000000010440400000000008410100000000c93208040000000000c0100000000014420480000000000000000300000000953008000000000001041000000000114104800000000035006200000000000000000c0000000000000030000000000410400000000000000002000000000020440400000000000000200000000c932080000000000000000200000000000000000000000450c1200
  | 6, 2 => 0x8400000000000000003000000000000000c0000000450c420000000000002104040000000000000020000000000000008000000035041201000000009400880000000000000000200000000000184000000000324c820100000000000000040000000454c0201000000000043440c00000000000000200000000941048000000000000c0101000000000000000c0000000250412000000000094304804000000010440201000000000000000800000000008d101000000000000000c0000000000000030000000041100800000000000080100000000000000000c0000000059002000000000055400800000000000000002
  | 6, 3 => 0xc00000000000000300000000000000080000000454c02010000000000000004000000000000002000000000000000c000000025402200000000000000000c0000000000000030000000041100800000000000108100000000000000000800000000000000300000000812008000000000000000030000000000104404000000000000002000000000000000c00000000000000000000000000000040000000000000010000000000000000000000000080101000000000000000c000000000081102000000000000000800000004508120000000000000000000000000000021010000000000104404000000000000000
  | 6, 4 => 0x214404000000000012100000000001502880000000002544020000000000000484000000000304c0200000000000000000c00000003544020100000000c531080000000000000a1010000000000000004000000035081201000000000002840000000000000000100000000c9320800000000000081103000000000000000c0000000350812000000000094104800000000000080101000000000000000800000000000000100000000000284000000000000000010000000085210804000000010440200000000011410480000000000000a100000000000000000c0000000304c020000000000852108000000000058c4200
  | 6, 5 => 0x1044040000000000061010000000144204800000000000000001000000000000000c0000000000000020000000114104800000000000000003000000000001840000000004500220000000000000000080000000254c02010000000000028404000000000081101000000000000000c0000000304c02000000000095300800000000000041101000000000000000c000000032080200000000000042440400000004544020000000000004304000000000000c1101000000000000000800000004504120000000000003044000000000450c120000000000000000100000000254402010000000000000008000000000108100
  | 6, 6 => 0x5502880000000000000000200000000951008000000000000000020000000000000004000000000000002000000000000000c00000000000000200000000000000080000000304c0200000000000000000000000000000000300000000000000000000000504c82000000000115100804000000000080101000000000000000c0000000000000020000000000000000000000000109101000000000040440c0000000000000010000000000000008000000000000001000000000003840400000000000a10000000001140188000000000430c120000000000000184040000000510812010000000000000008000000000000002
  | 6, 7 => 0xd420480000000000010110300000000000184000000000314c420000000000000000040000000001051010000000000000000000000000000001000000000021040c00000000010410000000000000000080000000000851010000000000000008000000035081200000000000000000c0000000000000020000000000000008000000000000001000000011431480000000000000000200000000000000080000000454402010000000000320404000000000000003000000000000000c0000000450412000000000114304800000000021484200000000011420480000000000008010000000000c1300804000000000080100
  | 6, 8 => 0xd420480000000000584120000000000000000080000000000000020000000000324400000000000081102000000000041440400000000000000200000000d41048000000000000000010000000000324404000000000000001000000000000000000000000000000300000000002144040000000000000030000000012028800000000000000002000000001641080000000000010410000000000d4008800000000045081200000000000000000c000000000000001000000000000000c00000000008410200000000000000100000000001041000000000000000004000000000006100000000000000000c000000000000002
  | 6, 9 => 0x40440c000000000000002000000000000000c0000000510c120100000000c53108000000000000000020000000000000004000000000000003000000009410480400000001044020000000000000000040000000450c92000000000000434404000000000105101000000000000000c00000002504120000000000000000040000000000c410100000000003204040000000304c020000000000d510080000000001044020000000000000000080000000000c4100000000000000000800000000000610100000001442048000000000001091010000000094104800000000000002100000000014c214800000000000002100
  | 6, 10 => 0x214400000000000000001000000004110080000000000010510100000000c13008000000000254c020100000000000000080000000510c120000000000000084040000000000061000000000141310800000000051081200000000000031440000000000000000100000000004344040000000304c02010000000000104404000000000000000000000000041040000000000000000300000000004204000000000000c11010000000000100400000000000109101000000000000000800000005150c2000000000000100400000000000000002000000000000000c0000000000000020000000000008404000000000081101
  | 6, 11 => 0x204408000000000000003000000000000000c0000000000c81010000000000000008000000000108100000000009510080000000002504120000000000000000100000000154022000000000000430400000000000101103000000000a0188000000000454c020100000000c13008040000000250c1201000000000000000800000004548020100000000d4204800000000045081200000000000000000800000002504120100000000d5100800000000020480200000000000030040400000002148420000000000000000080000000000c8101000000000000000800000000000000300000000d5100800000000000000002
  | 6, 12 => 0x10c100000000000000000800000000000000000000000002104000000000450c82000000000000000000000000000041101000000000000000c00000000000000100000000d42048000000000510812000000000141210800000000000000001000000011410480000000000000000200000000953008000000000214842000000000000000008000000000109101000000000020440c00000000004010100000000c93208000000000001051010000000000000008000000025440200000000000000000800000000010810000000000120188000000000000000020000000000100404000000000000003
  | 6, 13 => 0x114104800000000000000003000000000000000c000000000000002000000004110080000000000000000300000000c1300800000000000000002000000000020440400000000000e10100000000953008000000000000c810100000000000000080000000000000020000000000000000000000000000001000000000000000400000005050c2000000000114304800000000000000003000000000000000800000003504120000000000941048000000000000000020000000000204404000000025440200000000000000000000000000000000000000000c13008000000000000000030000000000210400000000000000003
  | 6, 14 => 0x411008000000000038022000000000000000008000000000000003000000000010440400000000000000300000000000000000000000000000020000000000000000000000000000000000000000000000800000000000e101000000014430480000000000000000300000000000000000000000250c120000000000003104040000000250412000000000000000008000000000000001000000000000000c00000004308c200000000000000000000000000000e1010000000000000008000000000084101000000011420480000000005108120000000001143048000000000000000010000000000000008000000000000000
  | 6, 15 => 0x114204800000000000000004000000000000000c000000021080200000000000000000c0000000000000040000000144304800000000025440200000000000000000c0000000250c120000000000002004000000000314c42010000000000430400000000000000002000000000020040000000001044020100000000000000000000000350812000000000000000004000000000000001000000000021040800000000000000100000000550288000000000214842000000000000410400000000000084101000000000000000400000000000000200000000c13008000000000150022000000000000000004000000000084103
  | 6, 16 => 0x4000000025440201000000009510080000000000000a101000000011410480000000000000a100000000009530080400000000000000300000001142048000000000250c12000000000000404408000000000081102000000000000000c00000000000000300000000002044040000000350412010000000000000004000000005880200000000000031040400000000000000400000000000000040000000324c82010000000000104404000000051081200000000000000840000000004504120000000000953008000000000314c4201000000000041040000000001044020000000000000000080000000000c0100
  | 6, 17 => 0x400000000000000300000000d51008040000000450c1200000000000000000800000000000000100000000953008000000000510c12010000000041100800000000035406200000000000000000c0000000000411010000000000000010000000000105101000000000001840400000002148420000000000d5200800000000000000004000000010c400800000000000081101000000000000000400000000000e10000000000000484000000000254412000000000000000000000000000000002000000000000000800000004504120000000000000000080000000214842000000000115300804000000000000001
  | 6, 18 => 0xd4204800000000000085101000000000000000800000000000000200000000000000040000000450412000000000085210800000000000000002000000000000000c000000000000000000000004110080000000000000000000000000002104040000000001001000000000114204800000000000000001000000004110080400000002504120000000000000000080000000450412000000000000000008000000000000003000000000000000000000000008d101000000000000000c0000000000c8101000000009530080000000000000000400000000000000080000000000000010000000000018400000000000000002
  | 6, 19 => 0xd4204800000000000000003000000000000000800000000008410100000000000000040000000058412000000000095300800000000035081201000000008521080000000000008410000000000000184040000000500c520000000000c9320800000000000000001000000000000840400000002148420100000000000184040000000000c0100000000000001840000000000000000100000000000000080000000254402000000000094104800000000010440201000000009410080000000000000000300000000003144040000000510c120000000000004004000000000000000010000000000000008000000025006200
  | 6, 20 => 0x41100800000000000081101000000009530080000000000004110000000000001044040000000000000020000000000320400000000000000003000000009530080400000000010510100000000d4204804000000000000000000000000000000800000000000000300000000000084040000000230c0200000000009430480000000000000210000000000003244040000000250c4200000000008521080400000000000000300000000003244000000000254402000000000000000008000000010440200000000000000000c00000003104020000000000951008040000000421002000000000144204800000000045041200
  | 6, 21 => 0xc00000000008c101000000000000000800000000000000300000000d42048000000000450412000000000000300404000000025041200000000000000000c00000005108120100000000001044040000000000000000000000085210800000000000000000000000000031440400000005050420000000000002044040000000000c51000000000000214404000000005406200000000009530080400000000000000000000000001044000000000450c02000000000000434408000000000105101000000014420480000000000000000300000001141048000000000254402010000000000000004000000051081201
  | 6, 22 => 0xc932080400000000000a1010000000000000008000000000000003000000000000000800000000004010100000000550088000000000000000010000000081200804000000000105101000000000000000000000000000000200000000000084040000000510812000000000000000000000000045041200000000009410480000000001500220000000000812008000000000304c020100000001082108000000000254c020000000000000000000000000250412000000000000000000000000000000003000000014430480400000002544020000000000c8314800000000000000002000000000000000c000000000000002
  | 6, 23 => 0x114008800000000000006101000000000000000800000000000000000000000d520080000000000000000300000000852108000000000000000010000000000000000000000000105101000000009530080000000000000210100000000d420480000000000000e101000000000000000000000000000a10000000000000000040000000000061010000000000000008000000000006101000000010c23080000000000000a10100000000000084040000000000801010000000000434408000000000105101000000000000000c00000000000000200000000943048040000000304c02010000000041100800000000005006200
  | 6, 24 => 0x20440c000000000000002000000000000000800000000000000000000000001004000000000000000000000000000000000000000000000003000000000000000c0000000304c02000000000000000004000000000006101000000000000000c0000000000000020000000000000008000000000000001000000000001840400000000380a2000000000094104800000000045041200000000000020040400000000000000200000000002004000000000000000020000000000000008000000000000001000000000000000000000000000e101000000000000000c0000000000c11010000000000000008000000000000003
  | 6, 25 => 0xc93208040000000324c820000000001141048000000000000000000000000000000004000000000000002000000000010440400000000004010100000000000000080000000000000030000000094104804000000000085101000000000000000000000000008110300000000000000000000000000411010000000000000008000000050484200000000000043040000000000000000200000000003104040000000000000030000000000304404000000000000001000000000000000000000002504120000000000004204000000000450c920000000000000000040000000254402000000000000000004000000025041201
  | 6, 26 => 0x40040000000004544020100000000001004040000000324c8200000000000000000800000000000000300000000000000080000000500c920000000000553008040000000000000010000000000000008000000000000001000000000010040400000000010c100000000001620080000000000000000200000001153008040000000000c11010000000094104800000000015500200000000000000000800000000004010000000001001008000000000000000010000000000104404000000000000002000000000000000800000000008110100000000002304040000000000c11000000000000000000000000035041200
  | 6, 27 => 0x3144040000000250412000000000000320404000000000081101000000000032040400000000000000200000000001004040000000000c81000000000085210804000000000000003000000000000001000000000000000300000000c13008000000000000c8100000000008d2108000000000000000030000000000304404000000000100100000000000041040000000001044020000000000000000080000000000811020000000000200404000000000041101000000004110080400000000000000100000000000000080000000520c520000000001141008000000000000000030000000000104404000000000000001
  | 6, 28 => 0x800000000004010000000001443048000000000324c820000000000004244040000000000000030000000115100804000000000000002000000000030440400000000000a10000000000812008000000000000000030000000055400800000000000041101000000000000000c00000000000000300000001153008040000000350842000000000095300804000000000000002000000000042040000000000008110300000001443248000000000001091010000000000100400000000000109101000000000000000800000000000000200000001142048000000000000021000000000000000008000000000040101
  | 6, 29 => 0x80000000000000040000000000000004000000000000002000000000023040400000000008c101000000000000000400000002148420000000000120088000000000058402000000000000000008000000000000002000000001642080000000000010910100000001412308000000000304c0200000000009430480000000000010810000000000c93208000000000000c9101000000000043440400000004110020000000000d52008000000000104402000000000115100804000000000000003000000000001840000000000000000300000000004244040000000350022000000000144204800000000015480200
  | 6, 30 => 0x10040400000000000000100000000000084040000000000841010000000000324404000000005908200000000000000000c000000000000001000000005540080000000004544020100000000d420080000000000004110100000000060088000000000000021010000000000324404000000000000002000000000000000400000000004110100000000c932080000000000000000200000000c9320800000000000006101000000011410480000000000000000200000000000000000000000254c02000000000145320800000000000000004000000000000000400000000000000200000000001004000000000504c8200
  | 6, 31 => 0x411008040000000000021010000000000000004000000045440200000000000000000000000000004010000000000000000040000000058402000000000114018800000000000000001000000000031440400000000000210100000000001004040000000104402000000000000314404000000005904200
  | 7, 0 => 0x43040000000000000a101000000000000000c000000000081100000000000003840000000000000a100000000000000000800000000010c1000000000000210400000000000006100000000000000000c0000000000c4100000000000000840000000000004110000000000000184000000000000c91010000000000310404000000000000002000000000000000800000000000000300000000002144040000000000c4100000000000000000800000000010c1000000000000210400000000000000003000000000002840000000000000000000000000000000040000000000811000000000000214400000000000000001
  | 7, 1 => 0x2044040000000000c010100000000001004000000000000061000000000000008400000000000000002000000000000000400000000000a100000000000020440000000000000000100000000004004000000000000000020000000000300404000000000080100000000000000840000000000000000000000000002044040000000000c1101000000000000000800000000000210000000000004204000000000000c1100000000000000000800000000000e100000000000032440000000000000a100000000000010440000000000001210000000000000000080000000000000030000000000000004000000000000003
  | 7, 2 => 0x800000000010810000000000000000040000000000411000000000000018400000000000000001000000000000000800000000000000200000000000000040000000000c1100000000000003840000000000008010000000000000000040000000000000010000000000028400000000000002100000000000000000c0000000000801000000000000008404000000000000002000000000000000c00000000000000300000000000184000000000000c41000000000000000004000000000085100000000000000000400000000010810000000000003044000000000000c11000000000000314400000000000000000
  | 7, 3 => 0x42040000000000000000300000000004104000000000000061000000000000008400000000000006101000000000000000400000000000a1010000000000008404000000000000002000000000010440000000000010c100000000000023440400000000000210000000000002104000000000000c8101000000000000000c0000000000c9100000000000001840000000000010c100000000000021040000000000000000100000000000284000000000001041000000000000018400000000000000002000000000002840400000000000000300000000003204040000000000021010000000000018404000000000081100
  | 7, 4 => 0x40040000000000008010000000000003104000000000000061000000000000018404000000000000000000000000030440000000000004010000000000002004000000000000000000000000000300400000000000000001000000000000000c000000000012100000000000040040000000000000a100000000000032440000000000000e1010000000000028400000000000085101000000000010440000000000010010000000000000184040000000000c51010000000000000008000000000000001000000000031440000000000004010100000000000000040000000000000010000000000000000000000000040100
  | 7, 5 => 0x320400000000000000002000000000000000400000000000000000000000001044000000000000000000000000000310404000000000000003000000000010440400000000000000200000000000184000000000000851000000000000310400000000000000003000000000030440000000000000000100000000000484000000000000c4101000000000010440000000000000000200000000004104000000000000c01000000000000000004000000000084101000000000032040000000000000000200000000004304000000000000841000000000000000008000000000000001000000000000000800000000000a100
  | 7, 6 => 0x10040000000000000000300000000000384000000000000411000000000000210400000000000000000000000000000000c0000000000c11000000000000000008000000000006100000000000000000800000000000000200000000000184000000000000c81000000000000048400000000000002100000000000000000000000000008010000000000004104000000000000c9100000000000031040000000000000e10000000000000284000000000000000020000000000000008000000000084100000000000000840400000000000210000000000001044040000000000000010000000000000008000000000006100
  | 7, 7 => 0x430400000000000104100000000000000000c000000000000001000000000032040000000000000000200000000000000080000000000c11000000000000000004000000000006100000000000004840000000000000000200000000000000000000000000c510000000000000000040000000000000030000000000100400000000000104100000000000004840000000000010c10000000000003044000000000001041000000000000204404000000000040100000000000021040000000000000e10000000000000084000000000000c510000000000003244000000000000000010000000000400400000000000000003
  | 7, 8 => 0x8000000000002101000000000003840000000000000000100000000000284000000000000061000000000000000008000000000000002000000000000000c00000000010410000000000000284040000000000000030000000000314400000000000000003000000000010040000000000000a1010000000000048400000000000000001000000000040040000000000010c10000000000000284000000000000c010100000000003244000000000000811010000000000104400000000000002100000000000000000400000000000000300000000003244000000000000000030000000000410400000000000002100
  | 7, 9 => 0x1840400000000000e10000000000002044000000000000851000000000000214400000000000006101000000000001840000000000008c100000000000003840400000000000a101000000000001840000000000004010000000000000284000000000000000020000000000000004000000000002100000000000020040000000000010c100000000000002840400000000004010100000000003204040000000000411000000000000320400000000000000000000000000000840000000000000210100000000002344000000000000000010000000000028404000000000080100000000000004840000000000000e100
  | 7, 10 => 0x184000000000000c5101000000000001840400000000010010000000000001004040000000000021010000000000324404000000000100100000000000020040000000000000a1000000000000008400000000000000000000000000031440000000000010c10000000000000084000000000000841000000000000324400000000000000001000000000010040000000000000000200000000000084040000000000c9101000000000001840400000000000e1010000000000038404000000000000002000000000030040400000000000610000000000000084000000000000061010000000000324400000000000000002
  | 7, 11 => 0xc000000000002100000000000000000800000000008010100000000002004000000000001001000000000000204400000000000081100000000000032040000000000000000300000000003144000000000000000030000000000100400000000000041101000000000032040000000000000000300000000002104000000000000000010000000000000008000000000006100000000000010440400000000010010000000000000084000000000000c9100000000000031440400000000000000200000000001004040000000000c410100000000000284000000000000c51000000000000000000000000000040100
  | 7, 12 => 0x41040000000000010010000000000000284000000000000000010000000000000004000000000000001000000000000000c000000000100100000000000000000000000000000210000000000000000040000000000000010000000000324400000000000000001000000000041040000000000008010000000000000184000000000000811010000000000200400000000000000001000000000000000c00000000000e10000000000000284000000000000851000000000000320400000000000000001000000000020040400000000000000100000000001044000000000000000020000000000000000000000000080100
  | 7, 13 => 0x43040000000000000000200000000000084040000000000c410100000000000084000000000000c8100000000000031440400000000004010100000000004004000000000000411010000000000048400000000000012100000000000000000800000000000000300000000000084040000000000c81010000000000324404000000000000001000000000000000400000000010010000000000002044000000000000c810000000000003204040000000000061010000000000104400000000000000002000000000032040000000000000e10000000000003204000000000000061000000000000320400000000000000001
  | 7, 14 => 0x104100000000000000000c0000000000401000000000000008400000000000012100000000000000000000000000000210000000000000184000000000000000020000000000314400000000000040100000000000000000400000000000a100000000000000000800000000000610000000000000084000000000000c910000000000000184000000000000411000000000000410400000000000002100000000000002840000000000000610000000000000000040000000000000020000000000104400000000000002100
  | 8, 0 => 0x400000000000000100000000000000000000000000000010000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_4 roots_4 8 s ws hint
  | 1 => checkCutEntry dom_5 roots_5 7 s ws hint
  | 2 => checkCutEntry dom_7 roots_7 6 s ws hint
  | 3 => checkCutEntry dom_8 roots_8 6 s ws hint
  | 4 => checkCutEntry dom_10 roots_10 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 62 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_11 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_11 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
theorem z4_80 : ∀ i, 80 ≤ i → i < 81 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 80 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 81 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (range_split z4_48 (range_split z4_56 (range_split z4_64 (range_split z4_72 (z4_80))))))))))
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
theorem z5_512 : ∀ i, 512 ≤ i → i < 519 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 512 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 519 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (range_split z5_200 (range_split z5_208 (range_split z5_216 (range_split z5_224 (range_split z5_232 (range_split z5_240 (range_split z5_248 (range_split z5_256 (range_split z5_264 (range_split z5_272 (range_split z5_280 (range_split z5_288 (range_split z5_296 (range_split z5_304 (range_split z5_312 (range_split z5_320 (range_split z5_328 (range_split z5_336 (range_split z5_344 (range_split z5_352 (range_split z5_360 (range_split z5_368 (range_split z5_376 (range_split z5_384 (range_split z5_392 (range_split z5_400 (range_split z5_408 (range_split z5_416 (range_split z5_424 (range_split z5_432 (range_split z5_440 (range_split z5_448 (range_split z5_456 (range_split z5_464 (range_split z5_472 (range_split z5_480 (range_split z5_488 (range_split z5_496 (range_split z5_504 (z5_512))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z6_840 : ∀ i, 840 ≤ i → i < 843 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 840 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 843 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (range_split z6_376 (range_split z6_384 (range_split z6_392 (range_split z6_400 (range_split z6_408 (range_split z6_416 (range_split z6_424 (range_split z6_432 (range_split z6_440 (range_split z6_448 (range_split z6_456 (range_split z6_464 (range_split z6_472 (range_split z6_480 (range_split z6_488 (range_split z6_496 (range_split z6_504 (range_split z6_512 (range_split z6_520 (range_split z6_528 (range_split z6_536 (range_split z6_544 (range_split z6_552 (range_split z6_560 (range_split z6_568 (range_split z6_576 (range_split z6_584 (range_split z6_592 (range_split z6_600 (range_split z6_608 (range_split z6_616 (range_split z6_624 (range_split z6_632 (range_split z6_640 (range_split z6_648 (range_split z6_656 (range_split z6_664 (range_split z6_672 (range_split z6_680 (range_split z6_688 (range_split z6_696 (range_split z6_704 (range_split z6_712 (range_split z6_720 (range_split z6_728 (range_split z6_736 (range_split z6_744 (range_split z6_752 (range_split z6_760 (range_split z6_768 (range_split z6_776 (range_split z6_784 (range_split z6_792 (range_split z6_800 (range_split z6_808 (range_split z6_816 (range_split z6_824 (range_split z6_832 (z6_840)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z7_288 : ∀ i, 288 ≤ i → i < 295 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 288 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 295 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (range_split z7_208 (range_split z7_216 (range_split z7_224 (range_split z7_232 (range_split z7_240 (range_split z7_248 (range_split z7_256 (range_split z7_264 (range_split z7_272 (range_split z7_280 (z7_288))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 18 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 16 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 18 → Z 8 i = true := range_split z8_0 (range_split z8_8 (z8_16))
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

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (3937061000 * 2 ^ 32 + 3936913544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_11.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_11 10 hT6 (by unfold IsConst; decide) low_11

def wit : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [8, 2]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [11, 4]⟩, ⟨GateOp.or, [12, 5]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [6, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_15341_aux

theorem PEqualNP.Outside.L_meta_15341 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937061000 * 2 ^ 32 + 3936913544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937061000 * 2 ^ 32 + 3936913544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_15341_aux.wit, PEqualNP.Outside.L_meta_15341_aux.wmono, le_trans PEqualNP.Outside.L_meta_15341_aux.wsize (PEqualNP.Outside.L_meta_15341_aux.lower s hs), PEqualNP.Outside.L_meta_15341_aux.weval⟩
