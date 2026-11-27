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

namespace PEqualNP.Outside.L_meta_16219_aux

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

def dom_0 : Nat := 0xaa000000aa00
def goal_0 : Nat := 0xa80000008000
def roots_0 : List Nat := [0x880000008800, 0xa0000000a000, 0xaa0000000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(11, 15), (11, 43), (13, 15), (13, 45), (41, 43), (41, 45)]
def r1sG : List Nat := [11, 11, 13, 13, 41, 41]
def r2sG : List Nat := [15, 43, 15, 45, 43, 45]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x65eae3e3
  | 3, 0 => 0x65eae3e3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaa00000000000000a0000000a0000000880000008800
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

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
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

def dom_1 : Nat := 0xaa00aa00aa00aa00
def goal_1 : Nat := 0xaa00a800aa008000
def roots_1 : List Nat := [0x8800880088008800, 0xa000a000a000a000, 0xaa000000aa000000, 0xaa00aa0000000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa000000, 9, 25)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0xf000f0000000000
def goal_2 : Nat := 0xe00080000000000
def roots_2 : List Nat := [0xa000a0000000000, 0xc000c0000000000, 0xf00000000000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 4 :=
  lower_iso [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_3 : Nat := 0xff00ff0000000000
def goal_3 : Nat := 0xee00e80000000000
def roots_3 : List Nat := [0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000, 41, 45)] (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0xff000000ff00
def goal_4 : Nat := 0xe8000000c000
def roots_4 : List Nat := [0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa00, 42, 43)] (by decide +kernel) (by decide +kernel) low_0

def dom_5 : Nat := 0xf000f000f000f00
def goal_5 : Nat := 0xe0008000a000000
def roots_5 : List Nat := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_6 : Nat := 0xcc00cc00cc00cc00
def goal_6 : Nat := 0xcc00c800c800c000
def roots_6 : List Nat := [0x8800880088008800, 0xc000c000c000c000, 0xcc000000cc000000, 0xcc00cc0000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_7 : Nat := 0xff0000000000
def goal_7 : Nat := 0xe80000000000
def roots_7 : List Nat := [0xaa0000000000, 0xcc0000000000, 0xf00000000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 4 :=
  lower_iso [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_8 : Nat := 0xc000c000c000c00
def goal_8 : Nat := 0xc00080008000000
def roots_8 : List Nat := [0x800080008000800, 0xc0000000c000000, 0xc000c0000000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 4 :=
  lower_iso [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_9 : Nat := 0xff00ff00ff00ff00
def goal_9 : Nat := 0xee00e800ea00c000
def roots_9 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

namespace S_9
def pairsG : List (Nat × Nat) := [(9, 25), (10, 14), (11, 15), (11, 27), (11, 43), (12, 14), (13, 15), (13, 29), (13, 45), (24, 25), (26, 27), (26, 30), (26, 58), (28, 29), (28, 30), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (56, 57), (56, 58), (60, 61), (60, 62)]
def r1sG : List Nat := [9, 10, 11, 11, 11, 12, 13, 13, 13, 24, 26, 26, 26, 28, 28, 41, 41, 41, 42, 42, 42, 44, 44, 56, 56, 60, 60]
def r2sG : List Nat := [25, 14, 15, 27, 43, 14, 15, 29, 45, 25, 27, 30, 58, 29, 30, 43, 45, 57, 43, 46, 58, 45, 46, 57, 58, 61, 62]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_9.map (· &&& dom_9)
def goalM : Nat := goal_9 &&& dom_9
def NN : Nat → Nat
  | 4 => 1
  | 5 => 9
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xb8658246
  | 5, 0 => 0xe4b84b419918b15e6b7d6c256af46eac69d96c505d2d869337252ae62f77a27825bf5f41
  | 6, 0 => 0xe035bfc0c22d231ea5c90d369192a4a67a5e75653d53052727f195c0
  | 7, 0 => 0xc22d231e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x7700770077007700550055005500550033003300ff00ff0033003300330033000f000f000f000f000000ff000000ff0000000f0000000f0000000000ff00ff00
  | 0, 1 => 0xf800f800f000f000f000f000f000f000cc00cc00cc00cc00cc00cc0000000000aa00aa00aa00aa00aa00aa000000000088008800880088008800880000000000
  | 0, 2 => 0xff00ff0000000000ff00f000ff00f000ff000000ff000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x1283dab5
  | 5, 0, 0 => 0x12838c45049ab18960e6b16a6941cd595a50735686941cd59d81072c80504a0d30d650735616
  | 6, 0, 0 => 0x2507358b604a0e6ad651839ab6049cd589410735605941cd5a5812839a65
  | 7, 0, 0 => 0x12839ab5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 29
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfffffc7ff1f88bf1fffffe3e3e133f3c3e1fe07fc0fc00f8007fff
  | 0, 1 => 0xcc0c3c198187800e0e0f01c000000703ba00e000000000e0000000
  | 0, 2 => 0x1ffe0003f03ff07807e00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xff6f747561608951b7f7aa3238132d2c321b605d80240080006eef
  | 0, 1 => 0xcdbd3ed9a5a79aae6e3f55c901054f4fbaa9e044002422e0048010
  | 0, 2 => 0x1ffe4443fdbff7f927e89
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 27 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 27 (i % 8)
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
  | 5 => 46
  | 6 => 12
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xc22d231e92aa67082e188189
  | 5, 0 => 0xe035bfc0c22d231ebab09f3cb423baa7b34ee5e6a78eb371a5c90d36964e51979302567b91d2b4f99192a4a68f5655dc8efe5fbf8b28a92c8ab0eb9d8679e5577a5e75657753501576f54b5e6d93d5d36b383860686746ca685c2a2d6172b3455f41b2b85962781e4fc64c8849c3f6ed49ab943446fd8e0540d709da3d5305273268067431e969f52fe4e8a52b5ada05287f8e3c27f195c026c3c18a182bcd7217f899e01689962c11f32cff11761e050715da67043cf9a1
  | 6, 0 => 0xb34ee5e6964e51978b28a92c6d93d5d36b383860686746ca5962781e49ab94342b5ada05287f8e3c1689962c11f32cff
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x6000004000020000000000000001000001000010000050000180000031040c0000500000c00002300408000000000148d101000008000020000000000000000800001000004000010000004910400000000001
  | 5, 1 => 0x4000000000040000100000c0000100000800001000018000070000080000300000800000
  | 6, 0 => 0x1000001000008000000000100000200000c000030000080000000000400000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 1 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 2 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 3 => checkCutEntry dom_5 roots_5 5 s ws hint
  | 4 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 5 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 6 => checkCutEntry dom_8 roots_8 4 s ws hint
  | 7 => checkCutEntry dom_0 roots_0 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_9 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 9 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 8 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := range_split z5_0 (z5_8)
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

def dom_10 : Nat := 0xffff0000ffff0000
def goal_10 : Nat := 0xeee00000eac00000
def roots_10 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

namespace S_10
def pairsG : List (Nat × Nat) := [(17, 25), (18, 22), (19, 23), (19, 27), (20, 22), (21, 23), (21, 29), (21, 53), (24, 25), (26, 27), (26, 30), (26, 58), (28, 29), (28, 30), (49, 53), (49, 57), (50, 54), (50, 58), (51, 55), (51, 59), (52, 53), (52, 54), (56, 57), (56, 58), (60, 61), (60, 62)]
def r1sG : List Nat := [17, 18, 19, 19, 20, 21, 21, 21, 24, 26, 26, 26, 28, 28, 49, 49, 50, 50, 51, 51, 52, 52, 56, 56, 60, 60]
def r2sG : List Nat := [25, 22, 23, 27, 22, 23, 29, 53, 25, 27, 30, 58, 29, 30, 53, 57, 54, 58, 55, 59, 53, 54, 57, 58, 61, 62]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_10.map (· &&& dom_10)
def goalM : Nat := goal_10 &&& dom_10
def NN : Nat → Nat
  | 2 => 1
  | 3 => 4
  | 4 => 13
  | 5 => 13
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x869ee2b1
  | 3, 0 => 0x80aa4a843d12acc031e3df9f058692b7
  | 4, 0 => 0x97398ddd73b692c173240d524c0e0adf25f134cf20e49f441d226cf71793ae7c1725c79d0bce8c130726140801e0734e01141bf7
  | 5, 0 => 0xeddd1af5c998fb3f9260bb9d73abf9b973240d526d6db878301879e72868627c28531e57204c6576195e30fe18dba2f405dfb75b
  | 6, 0 => 0x73240d52
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaa0000aaaa0000aaaa0000aa000000aa000000aa000000a0a00000a0a000008888000088880000333300003333000000ff000000ff000000000000ffff0000
  | 0, 1 => 0xeeee0000cccc0000eeee000000000000ee000000ee000000eaea0000eaea0000cccc0000cccc0000cccc0000c0c00000cc000000cc000000c0c00000c0c00000
  | 0, 2 => 0xff000000ff000000ff00000000000000fcfc0000fcfc0000fafa0000fafa0000f0f00000f0f00000f0f00000c0c00000f0f0000000000000eeee0000eeee0000
  | 0, 3 => 0xffff0000f0f00000ffff0000f0000000ffff0000cccc0000ffff0000aa000000ffff000088880000ffff000000000000fff00000ff000000ffaa000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x65473
  | 3, 0, 0 => 0xc4d654dde704fe5674b4d664
  | 4, 0, 0 => 0x179b9675c5e6b3aeaf359d7f78acebabd1645d5e6f3af2f359d75792ceba9b5675d5e701afaf359d757aa0ebabcd8b5
  | 5, 0, 0 => 0x179ace05d5e6b381b579c1676d5e9359d81abcd675d5e6b38db57acd676d5e6b49db579ace26d5e6b41db57b4d676eeaf359d81a9ace15
  | 6, 0, 0 => 0x1abcd675
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 19
  | 3 => 24
  | 4 => 29
  | 5 => 34
  | 6 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3303b40cc00000000000000e00300033f0f1f10ff03fc003fff
  | 0, 1 => 0x3f38380fc00000038000cc0ed03c38380f00000003800000000
  | 0, 2 => 0xf00fc03c00000cfcfbfb3cf0fdcc0c3c3300000cc000000fceef
  | 0, 3 => 0xfffc3c3fff000fff383bffc000fff0033ffc000fc0fc03ccc000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x5734fb55cd3c95224d251450e403008b150d1c10d502d800377f
  | 0, 1 => 0xfffbafbffc880f2afd277df7ffabcb8faaf2c36a28b822252436
  | 0, 2 => 0xf2afd27ca8800efdfbfb7df7ffcd5d3db3564b6cd50203ffffff
  | 0, 3 => 0xffff3dbfffcc0fffbafbffdbc9fff2ab3ffc880fffff27dec880
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 32 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 32 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 32 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 32 then wireAt i else 0
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

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_10 == dom_10) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_10 goalM u ys) : RunD dom_10 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_10 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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

def dom_11 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_11 : Nat := 0xaaa0a8a0aa808080
def roots_11 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa00aa00aa00, 17, 25)] (by decide +kernel) (by decide +kernel) low_1

def dom_12 : Nat := 0xc0c0c0c0c0c0c0c
def goal_12 : Nat := 0xc00080008000000
def roots_12 : List Nat := [0x808080808080808, 0xc000c000c000c00, 0xc0c00000c0c0000, 0xc0c0c0c00000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c000c000c00, 19, 27)] (by decide +kernel) (by decide +kernel) low_8

def dom_13 : Nat := 0xcccccccccccccccc
def goal_13 : Nat := 0xccc0c8c0c8c0c0c0
def roots_13 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c0, 2, 6)] (by decide +kernel) (by decide +kernel) low_12

def dom_14 : Nat := 0xf0f0f0f0f0f0f0f
def goal_14 : Nat := 0xe0008000a000000
def roots_14 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c, 41, 43)] (by decide +kernel) (by decide +kernel) low_12

def dom_15 : Nat := 0xaaaa0000aaaa
def goal_15 : Nat := 0xa8a000008080
def roots_15 : List Nat := [0x888800008888, 0xa0a00000a0a0, 0xaa000000aa00, 0xaaaa00000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa00, 35, 43)] (by decide +kernel) (by decide +kernel) low_0

def dom_16 : Nat := 0xffff0000ffff
def goal_16 : Nat := 0xe8e00000c0c0
def roots_16 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa, 36, 37)] (by decide +kernel) (by decide +kernel) low_15

def dom_17 : Nat := 0xf0f0f0f00000000
def goal_17 : Nat := 0xe00080000000000
def roots_17 : List Nat := [0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 5 :=
  lower_iso [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_18 : Nat := 0xffffffff00000000
def goal_18 : Nat := 0xeee0e8e000000000
def roots_18 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f000000000, 33, 37)] (by decide +kernel) (by decide +kernel) low_17

def dom_19 : Nat := 0xffff00000000
def goal_19 : Nat := 0xe8e000000000
def roots_19 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 5 :=
  lower_iso [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def dom_20 : Nat := 0xffffffffffffffff
def goal_20 : Nat := 0xeee0e8e0eac0c0c0
def roots_20 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_20
def pairsG : List (Nat × Nat) := [(2, 6), (3, 7), (4, 6), (5, 7), (5, 37), (9, 25), (10, 14), (11, 15), (11, 27), (11, 43), (12, 14), (13, 15), (13, 29), (13, 45), (17, 25), (18, 22), (19, 23), (19, 27), (20, 22), (21, 23), (21, 29), (21, 53), (24, 25), (26, 27), (26, 30), (26, 58), (28, 29), (28, 30), (33, 37), (34, 38), (35, 39), (35, 43), (36, 37), (36, 38), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (49, 53), (49, 57), (50, 54), (50, 58), (51, 55), (51, 59), (52, 53), (52, 54), (56, 57), (56, 58), (60, 61), (60, 62)]
def r1sG : List Nat := [2, 3, 4, 5, 5, 9, 10, 11, 11, 11, 12, 13, 13, 13, 17, 18, 19, 19, 20, 21, 21, 21, 24, 26, 26, 26, 28, 28, 33, 34, 35, 35, 36, 36, 41, 41, 41, 42, 42, 42, 44, 44, 49, 49, 50, 50, 51, 51, 52, 52, 56, 56, 60, 60]
def r2sG : List Nat := [6, 7, 6, 7, 37, 25, 14, 15, 27, 43, 14, 15, 29, 45, 25, 22, 23, 27, 22, 23, 29, 53, 25, 27, 30, 58, 29, 30, 37, 38, 39, 43, 37, 38, 43, 45, 57, 43, 46, 58, 45, 46, 53, 57, 54, 58, 55, 59, 53, 54, 57, 58, 61, 62]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_20.map (· &&& dom_20)
def goalM : Nat := goal_20 &&& dom_20
def NN : Nat → Nat
  | 3 => 2
  | 4 => 12
  | 5 => 51
  | 6 => 130
  | 7 => 145
  | 8 => 25
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x87a6373c7e2c8ae0
  | 4, 0 => 0xd675645acebb8b5bccf0dfb6c5e8be5ac04423ddb6ca7781a3852a70a1e7622b9a0b7e144f3d3f4c451f0ef6176c3da5
  | 5, 0 => 0xfa685baff529176cf0081edfe8cfd2eae8517414e5f297eadd8f3560dc231711d2a96ab5cfa3077cce3b459ac04bf92ebc3a0aeab3ec4d36aba1ab4daa39e96ba9431c8ba35c9dd6a2ad5d869f24ec359e6ead799c302b2a97cb2040962ce5c28e32f90b7eac01577ac07e9979bcfeaa782ba4e777aac17673721cde7285bc306f4bcbfc6253acf95e2487c25d4f21f456bf226a55360c77542a48b84e65610a4b4a6fcd3bceecb539be3d17372f49d43400396e329d8e8532969fae2f58572021cfe5df058ecc5704a2f44a
  | 6, 0 => 0x7b334ca5792903cc77dfa17575aa44ea750d73c9727718da6eaf5c196d964c5c6cc7f9b76a729fe46a44543e6777015564a204836391bbb05ea8d1895cbb87cc5a9f5dfd59d5a23b5925466956488c3a53466db8530e3d0851ab7a2350b194064f2ef4ab4b29df734a25f49947d1bb1b46df279b466dcded45a7f59843fede534365b3a9425751533daf73bc3d2c7c353b132c693a4fc206390153ab3597402032eb626b30d528202f2d39052db882ce2b35846d2a191a7929af2b6427288344216dbf8b1d9945271a2bfc7a18e3fb0a18939c08168bc85d13e0e2a711c6cff80be712130b83676e0a7d079a0a7677f50733e68204941f6a01d18b1e01a44b7b
  | 6, 1 => 0xf6360869f146644dedb06ad3ebefca4beb121e74e955d96fe8ba254ae8b769b1e5a66be6e45a7bffe3e18a9be3cc7821e2ee6b60e0d18bdadf204264ddfb04cddc2aec62db4f33a9da5c901dd872797ad76d9a26d72da707d0698fbac46ac8f7c278d53fc277339ec10d2575bc598a38bc19ed6dbafa413db87ee534b84aaf1eb1f9e3e0ae18ff3dacdcb081aca9b064aa11ec3fa8b61457a8a9a379a828f69ba7853e24a6c134b9a2487bd3a1ff2380a1040fa4a0c59c23a0908dfca00c68569ec11d629e0a094097a00225963e51e195b38752959bf1de956d102894b8834e9389b4aa927fc7e78ca36bc48069eaef7dfdc7517c60a6ce7c0b0c277b6ec17b
  | 6, 2 => 0xfafd1dd1f84fd4fb
  | 7, 0 => 0x66fb4c9163669d9563275f155c91de815bdfea355b0171135aa8a6b95a437adf59e9c31b56403068556f069554b47b9853b7a8b55316929452de426a51ab7a23515c29194fb2394c4e67282b4c173de94b0c2c39499b08ca48b0ac9d44cd758b4365b3a9425327d73c9d75a23c21f90f3a8b1a653899ed18387c221636224d1b360aefae35d89aaa342cdee932ba82ac3264f194315024ba3122199e2f1362052cb7e2692b81626d2a6f6cf928a4a83e26beaf6f23afce9222d85c9a2064873a203cd04e20292edb1fb72b911f3d31db1d81c57f18e3fb0a17d7cb95175a929b1234695d11d748061187183a0f8898390cabde0a07af559e06cd9ad403f1b952
  | 7, 1 => 0xe4625a30e3d420a8e2f02cffe25263cde1283faadede789bdd4db3aad863d13ed7d8277ed69e993fd58ce416d4fb6d4fd2fa81f2d0e5095fceeb1ad8cb46a5f8c9c8daa4c8df6e8fc6f762cbbeb2f988be4be64fba708858b837fe7bb4e46fecb37ef559ae064aa9aa8df529aa07d0ffa9647ee6a77ce252a494c22f9c48de2399ed5e879710a45894b8834e939a9e619117715e91015b8b906d26118f9d1d5f8f7fd14d8f46f2108d5eaaf98a81f0ca8968a0cb88f823fd869b759485f48e9f7e05acff7d33ff317d303bbe7aa157477a85129f79e15a28791304537892577572739f547268845a6c4b6e046bcf90f36aa2ab6069d0a4b069b2eaed6920920f
  | 7, 2 => 0xfe809189fe5cb65dfe091979fab495f5faa130d0f96feb04f80fe67ff734b506f50771aef34c8d5af17a65ebefeaeca8ef0e3eb4ed5612f6e878be20e73f702ce4763a0b
  | 8, 0 => 0xf2854adfdd9de376c3d681efbad4da24b6be76349b34b1218a7994f87f4590c97cea112d76f0de33705b5d9f5fbac6fd5cde0cce51bb2a0f4f8c57c24aee737934064f6c2eedfa851e7359ed1b78d4bc1729918f1561a43a1142fa410e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5050505ffffffff050505050f0f0f0f03030f0f03030f0f03030303ffffffff030303030f0f0f0f0000ffff0000ffff00000f0f0f0f0f0f00000000ffffffff
  | 0, 1 => 0x333333333333333322222222aaaaaaaa11111111ffffffff0f0f0f0f0f0f0f0f0f0f00000f0f00000a0a0a0a0a0a0a0a070707070707070705050f0f05050f0f
  | 0, 2 => 0x555555555f5f5f5f555555555555555544444444cccccccc373737373737373733333333ffffffff33333333cccccccc3333333377777777333333333f3f3f3f
  | 0, 3 => 0x77777777ffffffff777777777777777777777777000000006666666666666666575757575757575755555555ffffffff55555555aaaaaaaa5555555577777777
  | 0, 4 => 0xa8a8a8a8a8a8a8a8a8a8a8a8a0a0a0a0a8a8a8a800000000a0a0a0a0a0a0a0a088888888ffffffff888888888888888888888888808080808888888800000000
  | 0, 5 => 0xbbbbbbbb33333333bbbb3333bbbb3333aaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa00000000aaaa0000aaaa0000
  | 0, 6 => 0xcccc0000cccc0000c8c8c8c8c8c8c8c8c8c8c8c8c0c0c0c0c8c8c8c800000000c8c8c0c0c8c8c0c0c4c4c4c4c4c4c4c4c0c0c0c0c0c0c0c0bbbbbbbbbbbbbbbb
  | 0, 7 => 0xdddddddd55555555d5d5d5d5d5d5d5d5ccccccccffffffffccccccccccccccccccccccccc0c0c0c0cccccccc88888888cccccccc00000000ccccc0c0c0c0c0c0
  | 0, 8 => 0xeeee0000eeee0000ee00ee00ee00ee00ee00ee00ea00ea00ee00ee00aa00aa00eaeaeaeaeaeaeaeaeaeac0c0eaeac0c0e0e0e0e0e0e0e0e0dddddddddddddddd
  | 0, 9 => 0xf0f0f0f0c0c0c0c0f0f0f0f000000000f0f00000f0f00000eeeeeeeeeeeeeeeeeeeeeeeeeaeaeaeaeeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000
  | 0, 10 => 0xf8f8f8f800000000f7f7f7f7f7f7f7f7f5f5f5f5fffffffff5f5f5f5f5f5f5f5f5f5f5f555555555f5f5f5f500000000f3f3f3f3fffffffff0f0f0f0f0f0f0f0
  | 0, 11 => 0xfcfcf0f0fcfcf0f0fcfc000000000000fafafafafafafafafafafafaf0f0f0f0fafafafa00000000fafaf0f0fafaf0f0f8f8f8f8f8f8f8f8f8f8f8f8f0f0f0f0
  | 0, 12 => 0xff00ff00aa00aa00ff008800ff000000fefefefeaaaaaaaafefe0000aaaa0000fe00fe00aa00aa00fcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfc00000000
  | 0, 13 => 0xffffffff00000000fffff0f0f0f0f0f0ffff8888ffff0000ffff333333333333ffff0000ffff0000ffff0000aaaa0000ffff000000000000ff00ff00ff00ff00
  | 0, 14 => 0xfffffffff0f0f0f0ffffffffccccccccffffffffc0c0c0c0ffffffffaaaaaaaaffffffff88888888ffffffff55555555ffffffff33333333
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xd1918a54d78d8a54
  | 4, 0, 0 => 0xd73e23958bae84576a575e8cac52aead1425205d19303158baf1e062b17464a0f12aebcf425205d78e83c4abaf44e968575ce8aed62ebd13e4a05
  | 5, 0, 0 => 0xd74223c72a5b5e7a0f148f6ebae84472b1b5e7a0f14a06d7a30315859b5e7a129e29601af450584975e89ee5620601a3031580977e6a0f16206d7a274b76b1b5e8a0f1499601af44f725975e89f25cac6d7a32e062b1b5e89ced6166
  | 5, 0, 1 => 0xdfae84576b1b9ebd142520601af44e765975e89ee56166ebaf4509281b5e8c0c56286d79e83c5269b568a0f148f6d7a30315895b568a0f14a06d7a305e62b1b96bd1426206d7a27b9584db568a129e29601af44e5841406bd141e195
  | 5, 0, 2 => 0xd7a32d07895b5e89ced621601af460625977ebd14111c6d19305078b1b5e3c141e2c601ab450523d406ad141e1a501af431581175e8a12dda96d7a28395849806bcf4148f501af3d0786977ebd1425a1601bf5e8a0717568a0f149a6
  | 5, 0, 3 => 0x6bd13d6135d7a273b5841b5e8c0c56046
  | 6, 0, 0 => 0xd7a32e0a0f163efd7a283c5861c000d7a303158bbf5e8a0f16207dfaf45078b023f5d7a28395859f96fd7a284c44faf4e8c141e2c7d7a305078b023efdba283c5881f5e8c141e2c52e035e8a1311006dfaf44f78b0b3ebd16e83c72b1c06bd18283c2cdbf5e8a0fde2c7
  | 6, 0, 1 => 0xdfaf45078b0d3efd7a283b5885f7ebd141e2c46e03450583c1006dfaf45094b10380d7a160f1801b7ebd15e83c58e03b6bd139e166dfaf45078b043efd7a284c4481c06fd7a31312cdbf5d088f1cac7dfaf45078b02befd7a283c5835c06878b060200dbf5e7a0f160f7
  | 6, 0, 2 => 0xdfaf45078b10b80d74233c5801806fd140b0f04c037ebd05878c6e7af45078a47b80d18283c5809b7ebd141e2c26fcf5e8a0f14a07dfaf45076b083efd5a283c583df7ebd141e3558fcf5e8a129e297dfaf450988803f4d7a283c5859c06fd0f0b0c04dbf5e8a0f16077
  | 6, 0, 3 => 0xe7af45078a4d380ebaf450584db7ebd141e284efbf5e8a0f161f7d7a284a72b14b80dfaf4509879b7ebd1424bc40faf45078ed6297dfaf45084f163efd7a283c66b1f5e8c141e2c2cfbf5e8a0f16107dfaf45076b1138001af44f72b177ebd141dac2cfbf5e8a0f16177
  | 6, 0, 4 => 0x1bf5e89ef0b376d7a273c5859f7ebd1898ac2cfbf5d08cf16007e5af45078b103ebd18283c5895f7ebd141e2f58fbf5e8a0f161e7d7a305ea0f163efd7a283c5845f7ebd1425bb58e037e8c4c5602600035e7a0f14aefd7a283c5899c06fd79e82c1ec037ebd141f3c6
  | 6, 0, 5 => 0xdfaf45078b96380ebaf4507259b7ebd16283c58fbf5e8a13111e7d7a305078b143efd7a2b5078b1f5e8a125e3952e039ebd14148f601bf42c1e301300e7af4507869b7ebd141e2c4ae0006ad141e295dfaf453a0f163efd7a2a3c62b1faebd1424b958e037ead14160f6
  | 6, 0, 6 => 0x1af45078b02300d141e160401b5e8c341e2c52e035e878586006dfaf46262b143efd7a283c5819c000d7a273b58bbf5e8a0f1614701af45076b14b6fd7a283c5839f7ebd141e3858e037ebd1416106dfaf452a0f163efd7a283c5805faebd141cac40fbf5e8a341e2c7
  | 6, 0, 7 => 0x1bf5e8a0ecb375d7a2839584dc06bd141e2c1ac035e8a0587806dfaf45078b04befd7a2ad078b1f7ebd141e2c06fbf5e8a0f16157d7a284878b003efd7a28396cb1f7ebd141f3c58fbf5e8a0f161b7dfaf45078b0ebebd14243c5835f7ebd141e3458e03a6bd141e166
  | 6, 0, 8 => 0x37ecd7a283c58fbf5e8a0f192c7
  | 7, 0, 0 => 0xdfaf45098f1600800035e8a0b0780601bf5e8b341e2c701bf5e8baf160c701d77ebd141e16701bf5e8a0f16207dfaf45078b149a801bf5e8a0f1b2c70003a6bd141e2c6dfaf4509cf1616801bf5e8a941e2c7000345078b0100600035e878b06006dfaf45078b0780801bf76bd141e2c701bf5e8b941e2c7
  | 7, 0, 1 => 0x35e8c141e2c601bf5e8a121e2c701bf45078b1482701bf5e8bb4160f701bf45078b0602701bf5e878b148c701bf5e8a0f162a701af462a0f1600701af45078b1100700037e8a0f0b02600037ebd141dac600037ebd0f0b0c601af45078b0b007e7bf5e8a0f160f801bf5e8a0f1d2c701bf5e8a0f160a7
  | 7, 0, 2 => 0xdfaf45078b14a28dfaf45078b0b0f800037ebcf41e2c601bf5e9d14160f701bf5e8c541e167dfaf45078b0b0c801bf5e8a0f1116701bf5e8a0b148f701bf5e8a0f161a701bf5e8c341e2c700037ebd175e24600037ebd140b0f601bf5e878b060a701bf5e9d0f160c701bf45078b07827e5bf5e8a0f16228
  | 7, 0, 3 => 0x1bf5e8a0f1216700037ebd1898ac6dfaf45078b0b00801bf5e8a0b0780701db5e8a0f16297dfaf4e8c541e2c800037ebd142622601af4507af16007dfaf459a0f1622801bf5e8a0f1896700037ebd1421bc601bf5e8a101e167dfaf462a0f16298dfaf45078b1120801af45078e5629701bf5e8a0f16137
  | 7, 0, 4 => 0x1bf5e8bf41e2c7dfaf45da0f1cac801bf5e8a0dd60f701c37ebd14160f700039ebd141e29600037e878b06026dfaf45092f1cac801cf7ebd14160f701bf5e8c141e2c700037ead141e2c601bf5e8a0f1627700037e8a11de2c601af45078e560070003b6bd139e2c601bf5e878dd60c7dfaf45078b11008
  | 7, 0, 5 => 0x1bf45078b1102701bf5e878b110c701bf5e8a0f161e700037ebd105e2c601bf5e878b0b0c7dfaf45078e5620801bf5e878b060b701db7ebd141e167dfaf45078b140f8dfaf45078e5629800037e8a0b0782600037ebd0b078c6dfaf45078b140c801bf5e8a0f162b701bf5e8a0f1c967ebbf5e8a0f16168
  | 7, 0, 6 => 0xdfaf45078e5613801bf5e8b741e2c701af45078b14807dfaf45078c5616800035e8a0f0b006dfaf461a0f1cac801bf45078b1202701af45da0f16007dfaf462a0f1616801bf5e8a0c160f701bf5e8a0b110f700037eba119e2c601bf5e8a139e16701bf45078c5602701bf5e8a0b0b0f701bf462a0f16027
  | 7, 0, 7 => 0x1bf5e8a0b140f701af45098f1600701bf5e8a0f149670003aebd141cac601bf5e8a0f0b0c701c77ebd141e16701bf5e8a941e167dfaf45ca0f1629801bf45078e5602701af45078b5600701bf5e8a0f1dac701bf5e878e560c700037ebd13de2c601bf5e878b140c7dfaf45078b111e801af45078b07807
  | 7, 0, 8 => 0x1bf5e8b541e2c7edbf5e8a0f1622801bf5e8a0f0b00701bf4509cf1602700035e8a121e2c6edbf5e8a0f16168dfaf4e8a0f160f8dfaf45078e56228dfaf462a0f1628801db7ebd14160f7dfaf45078b148f8dfaf45078e56168dfaf45078b14a0801bf5e8a0e560f701bf5e8a0f0b0f7dfaf45094f16298
  | 7, 0, 9 => 0xdfaf45078c56288
  | 8, 0, 0 => 0xdfaf45078b0b380dfaf450583d806fd141e2c04c037ebd0f160c6ebbf5e8a0f163efd7a283c6eb1f9efd7a283c58fbf5e8a131e2c7dfaf45078b003efd7a745078b1f7ebd141e2c1efbf5e8a0f16297dfaf45078b063efd7a284d78b1c06fd7a283c2cdbf5e8bb41e2c7
  | 8, 0, 1 => 0x35e8a0f16006dfaf4509cf163f6dfaf45078b1f7ebd141e3958fbf5e8a0f16287dfaf45078b123efd7a283c62b1f7ebd18a83c58fbf5e8a0f16227
  | 9, 0, 0 => 0x37ebd141e2c6
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
  | 0, 0 => 0x30c380bffffffcc30e023c3c3e33033f3c1010f8cc0c1c1fffffff3030704f0f0f8c003fff0003fff0003f3cf0f0f8c000000fffffff
  | 0, 1 => 0xfc3c7c71f1f0f000c1c103b7bbafc0c0c3ffffffccfcfcf3c3c3e333f0000f0f00000cc1cd00343a230f3f0cf030184c30fcf3c083e3
  | 0, 2 => 0xfccf8cbf1f1f9ff33e32fc4844500c3808e0e0f0ff3fff3ffcfc7dfc3c7c7ffffffff0f1f138383c3fc3c7c7ff3f1f7f0f1f1fffffff
  | 0, 3 => 0xfcfffcfffffffff3fff3ffcfc7dfcfffcc000000003cfc33b8f879fcfffcff131197f33e32ffffffffccf8c80edeeebf33e32ffcfc7d
  | 0, 4 => 0x3000300ecee680c000c03838180300030000000000000003838180300033ffffffc0c000c0030382030003000000000c000c0000000
  | 0, 5 => 0xff3c7f71f1f0f3fcf1f1c7f7c3c0330737ffffffc0cc1cd03b7bba03307340e0e0600cc1cd0030382033073400000000cc00003b4000
  | 0, 6 => 0x3c0000e0e00000c000c0030382030003000000000c000c0000000030000000c0000030e02380804100000000000003fcf1fdc7f7fbe
  | 0, 7 => 0xffcf8fbf121117f33e32fc4844503c383bffffffc0f0e0e38383c303c383800000000f0e0e003038203c383800000000f00000000000
  | 0, 8 => 0x3f0000eef0000000fc03803be00003f00000ee80000fc00003ba003307340edeee80cc00003b400000000000e0e063ff3e3efc787c7
  | 0, 9 => 0xcc0c0c000000033030300000000cc000030f000000fcfcf3bbfbfb03f3f3c0edeee80fcfcf38383c303f3f3c0edeee80fcfcf0000000
  | 0, 10 => 0xcf0c0f00000003f3fff3ffcfc7dfccf8cbffffffff33e32ffcbc5dfccf8cbf121117f33e320000000fc3c7c7fffffff303030c3c3c1c
  | 0, 11 => 0xcfcc0c3efef0733f00000000000cf3c7f70fdfefb3cf1fdc3c3c1ccf3c7f400000033cf030c3f7c1ccf0c0f30fcfe7b3c303cc3c3c1c
  | 0, 12 => 0xf00ff00000ee83c00000fc00000cfffffc0edeeeb3fc00003b4000c00ff00000ee833f3e3efbfbfdfcfcf8fb0f0f0733f3e3e0000000
  | 0, 13 => 0xffffffc0000003fff030c3c3c1cfff0033fff0003fff1f1c7c7c3cfff0003fff0003ffc00003b4000fff00000000003c03fc0fc03fe0
  | 0, 14 => 0x3ffffffc3c3c1cffffffce0e0f0fffffff0000000ffffffc0edeeebffffff0030382ffffffff121117ffffffc7c7c3c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2082003f7f77bc8208002c241201020d201010880408100ddfddef102040030904800036ff0002edf00009203090c80000000ddfddef
  | 0, 1 => 0x54346451c1c0c150d1914fb79ba000000377f77bcca8b482c2432032a2400b0904804883480c2432030a24009010080820a482000200
  | 0, 2 => 0xa8cb08af1b1596a32c22b048445a8cb08ae3e373dd2d991670703054346477fff7fd50d1919afaddf54346475d3d1d550d1914f27130
  | 0, 3 => 0xfcff6cfffff7fff3fdb3f74f475fcff6cc8808043f3fdb3f74f475b8eb48ad131196a32c22fdfddefa8cb089b6d66aaa32c22f54d465
  | 0, 4 => 0x4714b752ecee691c52dd4393a9a4714b740808841145095439389a030093377f7fbc0c024c08b0b8a03009300242a280c024c0000200
  | 0, 5 => 0x5734f751c1c8c15cd1914fb71305734f777fffffd5cd3dd4fb7bba5734f750e4ea695cd3dd0ab2b9a5734f7408088415cc1004fb5120
  | 0, 6 => 0xabc2002e3e04022d266e98f8fcf8b499ba4363b3e2d266e00002008b4909a63e373ea72c26b0d8ccf894909a436333d5cd3dd4fb7bba
  | 0, 7 => 0xabcb9bac121916a72c26b0d8ccfabcb9bbf7f7fbeaf2e6eb8f8fcfabcb9bac363b3eaf2e6e28b0b8aabcb9b88000802af2c26b0d8ccf
  | 0, 8 => 0xfff2403fff4483cabfc8fd27fe0f2aff23f49ff83cabfc86d27ba0df7dfff7ffffff7de526dffddefcd5d2df4f6f37eaf2e6eb8f8fcf
  | 0, 9 => 0xcd5d2de4b6b37f3574b70202010cd500034f64003fffffffffffffffffffffffffffffffffbafafdfffffffdbedeeebffffff2202210
  | 0, 10 => 0xcf5dbfc0808843f7fdb7f7dfcffeddf2dfffff7ffb77cb7f3dbcdfeddf2dec929157b77cb72202010dd7d6df7fff7ff3574b7d3dbcdf
  | 0, 11 => 0xefdf2dfefef77fbf48002200000df7dfff7ffffff7df7ffd3dbedfdf7dffc08088437df5b7dfffdffcf5dbff6feff7f3d76ffd3dbedf
  | 0, 12 => 0xf2aff21b49ee83ca8b48fd25320ffffffdbedeeebffc9006fb5120f2aff21b49ee83bf7efffbfbfdfefdfbffcf6fb7fbf7eff2202210
  | 0, 13 => 0xffffffc8808843fffdb7f3dbcdffff2d33fff4c83ffd9916707030fff2403fff4483ffc9006fb5120fff24008800003cabfc8fd27fe0
  | 0, 14 => 0x3fffffff3dbedfffffffeebebf7fffffffb2daedfffffffdbedeeebffffff2ab2b9affffffec929957ffffff6707230
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 54 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 54 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 119 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 119 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 119 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 119 then wireAt i else 0
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
  | 3 => 3
  | 4 => 21
  | 5 => 211
  | 6 => 1145
  | 7 => 1070
  | 8 => 19
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xebcbfe89be5a4d2833df28a2
  | 4, 0 => 0xd0698fbabae19876b29fd0bfb1019abbad3bbc7aa7e4280ba1ff23809ff80b5e9e33fbf39e0ee5168fe507db8ed58d3c8d003e8c7dfdc751709d33b56391bbb05b1130fc5631281427d078581a2bfc7a00eb1c74
  | 5, 0 => 0x4d48131d4c8947ef4a7802d549a0b8ec47f2cf3144708c4b4328eb7842b779a3427b921e422dfc384074a10a3f3807003f264f903cf42ef73bed1c1f3a8692913a1419e0393ec2df38f9c5ac3893024036e0565936ca64db360aefae3556e607315b74403156fc53313762d02fa384062f1e5ca72ebde5a52d53e0cf2ce3896c2c55fa862bfd49b32a6f6cf92976999d2819a9902703d90426a4d0282245ca792203f96221f787de1e9b46451e280fc61e0daafc1d5349c61cca0fa81cc6d82f1b036358190eefa9186a6174146d7eab14550ffe1415a1dd1234695d0e58cdc80bf607510a9c2744098d4fc705e9b3c305c248fd045c0b3b03dfc40503dc73d8
  | 5, 1 => 0xa570947da3b82a63a25e4bf19c8a818a9b0114ab9951f26098245a7c95b952fb9556528c92d9dbeb922adf2d9125aba68edbcd6c8e4383418dd801a58bf068f88b9fb0eb8b2247168ad2a5708a370dca898789da882be4e1854cd06284425cd7839480b882a48215819a585280ed75e78095090a7b709a6a7b5291b77a85129f7a66f3d279d2cec87965f0c676b9a0057680fac4754dbe2974a94e177268845a6ff765c36d6a8de86d247f036ce37f6d6c0837396bbb0dc06b1a345d6b0c920869d0a4b0685a030e63669d956339632f622cce345fa1cf0a5db0e8a65aa8a6b95a7ae819583a210d57861766556f0695556db67250a7f1e8508b52a54e67282b
  | 5, 2 => 0xe2421ff8e1e85794e19c8a71e127de5ae0f1caa4e02fc1b4e0141211de8d3aa6dd623433dc253d49d89e3a2cd8102e57d798b841d68cdd78d596093ed556282ed4f1d031d4821794d39ccd00d2fa81f2d2e064dcd0daa806ce0d08b0cdbcf587cd64c8f8cd5f1ae5cbca789dcb8dcfbbcb1954becaafe2a7c971f0acc914e149c78bb67cc754549ec611282bc5bfe2a6c433ebfcc2cbaffcc278d53fc2087c8dbe7d9ce9be6720dbbe07eef1bdaaca5cbc25b6abbbd6fe92bb5365cfba8bde77b9baaf2ab981b018b6c34288b56df66fb5170e3bb4b9b714b226724faee37064add0151dab928d6aaab48070aa07d0ffa9643bcaa73ef941a72ca08ba5f28ce7
  | 5, 3 => 0xfa26b397f96feb04f839d932f5e7dcc4f2f9cbbdf2c9fb00ef7c561fee9e1466ed7a9723ed6cdd14ebc3c099eb287186eac088b0ea22e07ae9c13ed5e8251b64e656f4cfe391740fe25263cd
  | 6, 0 => 0xda6941f0d95c7350d6e8d170d4eee2d0d4430e80d2d197c0cd23f600c97cf590bb7fee20ba8521d0b5334f40b2c8ce60aeff36b0a9628be0a71eca009ea0c3209c8fdf309bd51ef09a18f54097c0ec409598a570941c54b0919997808bab8a208b51a4508739b7007fab1ba07a19af20711d49e06b5fac60644c923062b4d43060f596e05f2ecc205f2790c057729b6055f0adf053cd7d105169eb00496704c03f1b95203abb2f003833f26034762020330c81202c18e620285087d0242a22d0240dc180235e80301b2233d01a6e4da01a0c3aa01866a3601652a32012a584000f91aa800f5a3d200f4e623009e65ee009787b3008dd725005b006f002e9cb3
  | 6, 1 => 0x1abba94e1a548add1a2dc39b19ba301a1921f28d1882b169185955ec17dbb70317ce2ba2175a929b1749ce821729918f16b3ccba16a5eddb1673385e1665488216066cd915e9498b158c470e1581f8c81561a43a155ed0bb155b532914ee289d14db18b514649f8f13ea83c213c7072613967e2f13924c52138cad0013346ed11317dd2b130a5a8912e4f2f812c3605312b8ab41124d6d631234695d121b11231187183a1161181a11408e9a10c64d38108ef5b9106ef5981028210e10105d9b1004221f0fec104b0fc7e3a30f18438c0ee2d2210ee271f80ed86b730ecc4ac70ec4f4730ebf94530eaf32cd0e9765830e93a5210e7e15130e5d92a50de1cc4b
  | 6, 2 => 0x29c478db2934275728e1d56328d3f68428c93b9c28bda13e28bc54b328a1dfb02842e2622819312c27f9aa2127691ed52759c5772713cf002707a0fd26d0c80326bb2fef267434a3262c08ca25df735525d7174c255c4db224d6bcb124b5fa3e23fa873323aa74da23057c1922d9401722d85c9a22d2ddb1224f4f6f22417090223655962225318021d8db472177d428213819c9211152c220eebdc420a84c142064873a205b0a2a1fd652f71fb72b911f09477c1efda3231e7359ed1e5a4bef1e56e02b1e0ecd901cf2a8c91cd584061c96ea491c84fb571c15531c1bcc3d7d1bbe42c21b9d622f1b78d4bc1b62a5db1b3c1cc21afb53ac1ae163af1abc9d47
  | 6, 3 => 0x37444b183702e44236f47cbe36b5383e3664870336550c59360aefae35fe022a35d89aaa35a69de235787e26356512d03556e60734f524f934d2fbb734c7a967342e9e8c340a9e4334064f6c33ce134333a2828e335d819532e38d4f32e16b8932bcf31332a666cf3234763e3185f30f317af60a3176335b31752de73157bf6e31472fc231302720312ae6df3122199e308c42f8306cb5222fc5bf282fbfd15a2f37b6b72f1abea52eedfa852e8e6a142e3061ae2e2eb6002e1a49802df741622da94f942d52d1502d06d0c22cf085992c5afc882c14318a2baf6f8f2b7b7d022b26d94b2b1903882b08f8cc2a6f6cf92a5335872a2308752a121f8d2a0b1b2d
  | 6, 4 => 0x4512aef1450ea01a44ee3ad244beee70449d3035449600244490ec0c441e848e43df582343c4e0bf43acd9484397dd8b43686f9d433f660a42dfcdcd42b779a34291ffc94288da78427c5b89425ac010425327d742487af741f0f93141b3665641a58777418c58194170bcbe4132065940a60e374041a8df3fd84d593fb5fdf43f2a3e083f227ddf3f1e2b9c3ef9b7083e79bb8a3e41e9843e38dfb93e2f1fca3d97514e3d2562093d1f3f593cb64d0f3c346cd83c0ce04f3bc8e96e3bbf524e3b75f2e23b34c0e23af7a7e33acf9b4b3a9da90d3a73bcfc3a03d4b139731d6538956ead38115693380d7bfe37d8b58137a858a737a4666c37962c63376ecd62
  | 6, 5 => 0x542767885416d04b534afad3533fb48d52e8c50e51ed228251e9127651bb2a0f5188980651761d5f5160844350df0cf15038f11c503182d94fc559f74f9d1e774f8c57c24f7b0f794ecc8e064ec280834e9d19034e6d5c1c4e2464a44e23904c4dd3ad484dc9c7c04d977a104d84259f4d2f3d364cfd734b4c7463374c6700e74c2571154bb8d2fa4ba1260e4b75ea1e4b4c25c34b4b81c74b17e2734aee73794acdf8d54a3f5f3c49d9fcdb4982335e497253c14932d4034910933d4841ce1d4834edba4824b1684795ee6d4772ba53473400504705d2b147017e8346da9c4646bddc5e45f5a3ba45f126ed45da9aaa45cb4f1b45b71f03457c8acd456daacd
  | 6, 6 => 0x61f63a00618f0c8060f47f6c607f3e8c606aab195fbac6fd5f6139d15f4ce3e85ee4680f5ed6a3f15ed5c2bf5eace41b5e9f053c5e8818c95e7275db5e5e95475e0652b75d8bf1475d8128125d6ad8975d1e66bc5d0eae245cde0cce5c7754db5c2fe5c85c0911c55bdfea355b5310a45b3c064a5b1f7a795afb09185ae1ffbf5aa5f5965a353b1759f684b259a0c2fc58a9df5058a9d59358817b3f5875705b585146145813f0b45808a353580611d557d21cf857ce35d1576611cb56ba13a056aaafbf569e22015694ac205659605e5618ad155615047155cdf411556f06955530a86c551db61354fdc76d54f251df54e177af54ba7ac55488605d5459014c
  | 6, 7 => 0x705b5d9f703d8738700050ab6f9599c06f897d916f567eab6f4c3cf56f43e1be6f3a9e9a6f25a2b96e24e7616de0ebc56dd88ab66dd08b0e6d76e7956cfdbf986cf4f29e6cd6ca796c66f60c6c5bf97a6c4b6e046bcccd376ba0f1c86b9d976b6b6a75856b3457826aca076f6ac035c96ab1a0db6a41bcfc6a41599e6a258de669dd5e9e69d255dc69c0add469a1d56c6936cd5a6909bb466896eaea688dbb5668329f33680cb64d67741da6675e8687673f974f67044c4c66fd841f66e9390a66c9726065d27dac65318d936472b7016410a41c640f62e363b75a2363aed3aa63a6a9d3636352f96330b2ce6329ad906310f02f624ac82b6243e4b46232c142
  | 6, 8 => 0x7e1fc9157e0bc1687dfb85ac7dd13d877dcd0b037d8e4bce7d44009e7d3371107cf889057cea112d7ccb503d7cb1fb967c69c65e7c4ba7b87ba3c0797b9474917b8706d77ad3415f7a9f7e307a8ef3507a80e2fd79e5550479bfc59f79ad6602797004af79684f627951d5787911f99d78a46f127893519d7800865577abf41377728e4a770e4b0576f0de3376a582cf768e81ea764692e6761e2a877613d46a75d8724475d32c7d75ce6c6f759d1162758c523f74cf39e474b4975974068ac9729906d472956c1c72739f54727253ef72703eb37240c1f97231884e7205699a71b731cf71936650718d4b85718aa31d716e5da9716e00617128819770da3446
  | 6, 9 => 0x8ae257588aa3b04f8a7994f88a0b34fc89a9614589a86b258905ec5388f823fd88f4b3ca88ede02888ed272688e36b1588a82a5488a4fc218899bfb58826fc398809f96f87e72a6d87b4d5698784293187806e588759f0be874f926986d3f20a86be95e986bb6894867726a1863b65ee8634c12785f6241e85c3b1498527bd3a84e9742a84b0006a849e475c847e77b1845d1c668438f64283f8d5db83c0be09837f6b3f837e681f833df9038320fd1b8312ea9182fe545d82eca47782c92c1882c8532e82a08cbb827963fa81e0e926818c8a24818c305a816c34c6806266ad7fdefe227fd11f437f78cf077f4590c97ed1cb467eaca16f7e79e8eb7e6cc629
  | 6, 10 => 0x9bd198379b74bd5f9b56a6c89b34b1219af887159ab78fed99f80ac699a9b2ce997632ef997374ef98ff0c189823ba7b97885ff9977488ac969aeb72967a8905966c9f46964c30c0962943809627b628960a5d0495ddc41b959b0bcb9582ff9e9544e3fa9541ee6894adb8bf94aba5ca948c576e945654d7942f6296940d963193f91dd793e24993935371a9932dab1b9322c34692d649fa9249c75b92409e49922ccdbb91fd1dbb91a91fbd919d19e6917b4abf90e5803790e48abf90d21748908462249022657e8f0aa4bd8e88272c8e79b0618e5d90ed8e3f8c778e142b368e0e30198dfe33ce8dacf6f48cfa91f68ca14df68c8f17858c73f3678af53f51
  | 6, 11 => 0xa74b4154a732a1a6a6e45fa9a6c282b6a6a1e8eaa6563cc3a6522b53a6491c9ba6290dd7a6193286a602287da5ff6a18a5cf7206a533b563a509d3d0a4eb786ea4ba7d29a4b188daa4428e5ba4033c3aa3eb5964a387b4e2a3744415a33588fda2efe0c0a2cd8bc3a2a97873a29e4ecda28ccd7aa284be75a27771aca1f7dfcba174c228a16ca8ada13c87fba0d0e204a0c4a17fa09b5bdda06f7c80a05ab451a0369f44a0363e9fa008f5839ffa6b569fe5c6099f6676b19f295df39f19428c9f0c76639ed7031a9ed1e5489ec0d7899e9195249e76698a9e56566f9daae7359d6fd84f9d4388ce9d3121ea9cec41bf9c6f27f09c33d9779c32deb99be41d5a
  | 6, 12 => 0xb6be7634b603540cb5e82352b5a0fe76b58b0cf8b542d854b51ce2f2b4fc8e64b4f19ce0b4bad623b4b7aa29b432738eb391ac48b2ad64c6b251b86eb23ecad5b2227074b21e5031b205eb4bb1d1766ab0dde46bb09debbbb099228eb07d72ebb0114f0aaf616e2baf05cc12aef69b80aef5af7aaeb6623cae28502fae1bf85dadd493a1adcb950dadbc24f4ada11c77ad744688ad58a5d0ac9b1be4ac84e178abbbdd0bab8e7545ab8bcb77ab676f4faafef900aa801c35aa75a9a3aa67d157aa63c251aa361d56a9f3d131a98e4816a9762739a94093e3a8cb32a4a8a73885a893383aa85da819a85b062fa827e4dca7fbc882a7cf5c2ca7c82b51a76c99de
  | 6, 13 => 0xc42e642ac3d681efc391afb2c30d6fe3c2c56a8ec2b84f8ac2a091e1c285e459c26e24bcc2472df4c23b26dcc21422aac1f8fe15c13e825dc0d8bcdac02b94a9bff418e7bfb0cba3bf83682fbf7d00d2bf3ee1b3bf3102d4bec0a575be4769d9be27a8c3bde1cfb5bd2fb554bc545819bc2d2173bbcf1011bbacdf6fbb75fc4ebb29e98abb22dcfdbaefd317bae1c4e0bad4da24bab9a1bdbaa3d292ba701036ba6676f7ba2a9fafb9fe2647b9a7ac49b9910a03b947df4ab93206deb91d4ce9b90dc9b5b90b816bb8767b00b84d5911b8025b3bb7efb67db7dce78eb7ae1533b7a9ba99b75432adb751909cb729f7fab729b85fb71329c5b6dcaf1eb6c47bb9
  | 6, 14 => 0xd383a931d2c6073ad2b5723cd2af93e6d2849381d260daa2d2370a95d2361075d231461dd191abc0d1879d90d0f15981d0e64a54d0bd03c8d0474b66cfe1e7becf863077cefdaf14ceefcea1ce6a884ecde202f0cdcd35ebcd8c6716ccbe85adcc614d5ecc4ce26fcc1a159bcbd5b4f2cbb9f257cb5a385fcb2d3d5ccae5bbd8ca4b1c80c9ff3712c9bdabcac996b3b6c9760326c90a98fcc8df6e8fc8b75089c88fa312c885719dc7fb6ba2c7d402f1c71b0c31c70b1e59c6bc9380c69a8dc0c68488acc637c9f1c59d6c30c59c2c97c595198ec577bfccc572feb0c555d6ccc5497397c5432efec5368674c4f9eddfc462ab86c44fda13c44cc871c44957bb
  | 6, 15 => 0xe42cf0d8e3ecf174e2f6af66e2e47feae1fe325ee1ee1201e1808a81e159e427e1151f08e0bfe9fbe09c6b8ce094249fe0932adae0129c16dfe045a4dfd68d84dfcf6011dfcc093ddf811425df52ada1def7cc0fdee02152de90f3a7de67d326de41358fde23d5bfddd7a141ddb7dd18dd9de376dd93fd71dd040b83dc5e2b89dc5bf6d5dbce5bdddbc7af05db9b701bdb95112edb5cb9b6db317bc8daf35326dad45ebcdaa10b17da82fa9fda60bae0da3d3e35d8c89669d89de169d85d0165d7abb4fbd6f8f5dad697b081d68e0ee1d653149dd612c66fd5ce88c2d58ce416d5676af3d52bcb4ed52b0a13d4c56c15d4938e6ad445852fd3d2caa2d3980975
  | 6, 16 => 0xf3ef218bf3ab2319f3878ca6f2d492adf2a27320f29edce5f2854adff276acbdf260e8b8f20d4857f1c9ec54f19a275cf0557068f052953beffdcf4cef82e6a2ee65afa3ee0a9ec1edd0785cedbcaaa0ed303909ed215bcfecee993fecce9206ec90ead9ec6b46deec17d5dfebf03b1eebc7f551eb7ec531eb6cc432eaf5c476eabec0cdea9da33bea9496edea9248f2ea85e4dbea63c2d5e9e0e609e9cfba14e94d91fee9306d3be8796d32e8623c33e84d4a98e8047120e6debce7e695e825e694be0de68ed5dbe6709071e66f80ebe6548bb9e6226647e6118099e5b44ac5e5830406e576d920e506db91e504ee61e501ca94e4de93f4e4a745e5e43a6889
  | 6, 17 => 0xffc703bfffabe638ff98826cff91be5cff55b127ff27467fff2325bafee184e5fe78c91efe4b532dfe34f967fdbe07a2fd40c7e7fd199790fd0a6dbffcbce5a3fca60f23fc78f6f8fc3650befc30abd5fbefb591fbe81295fb89f1edfb4008c7fb07d043fae7fa4efa7d76fdf9ec5cb3f96feb04f966b7b2f9414bd9f908e400f8faed97f8ed2165f8c97e8bf86a14bbf81e117ff7db9c7ff79aba4bf74120e2f7271afbf6d3c780f6adfee5f6905ec9f6535463f6281cb5f6260c95f61da697f58f108cf58182cff57a4822f5277aadf5192827f512f24df4dff160f4723ae7f428f87c
  | 7, 0 => 0x1004221f0fc22fb60f3d84400f3badb20e8414b20e7dd0190e589c450df078900d9cbe430d61f2fb0d4d98860cf91d9f0cc7aa850cb3009d0cb114e30c867e660c22507d0bd753a90bb2ffb10b989d440b41c7720afb5dd30acf09dd0ab7b9ae0aa9dacf0a71f9560a172c4909ee1b6f089ab0f30878675807d82e3c07bd347d0754ea15075140fd06c7654b06b07a03064612c706291d83061ab28605c61dd605ad2f3405a3eb0a059e8b1704d0acec03e36454036df150036012710347620202e9d44b02d5abde0296f5790291d00a023f103c023c952e01a603fb0198251c0188fb4b0129b75501283a1700f5a3d20086a50c006499150027347900103def
  | 7, 1 => 0x1ee4e3db1ee472391ebb13731e739d441e3d0e221e1aa3ae1e17d8601d989e101d094b741ca0b1831c53b96d1c1ffead1bea35011b8548e61b78d4bc1b70b1901b61a0cd1b52f3321b325a461b2d157f1a90e4691a5d39541a4058c31a2bfa9c1a0ece7019e3604919deb3e219b1d4481979f417196672e119529451191531f41900f429183e830517d07b00170db67f16e8db1816b50ee915ff8a4715f86a8015f022ce15b2bcae1581f8c81561a43a1528ba3c141a4f1c1415063f1413d608135211a2131bfefa1317dd2b130748e512b8ab4112b8884a12ae5da3129997eb1232479711ed84b711eb7ccf11b4128d119811441134c9341110c79410d1aa96
  | 7, 2 => 0x2d014b912cf3c0ef2cf085992cae27f22c9946a22c1543872bcf9a012b698d6c2b48380c2b0f56702a7c85282a73350a2a6cf0712a5e00e12a5175e429e942c429c478db2964176b291abe562889888f2882e2b2284db2db2775450f2774c4602727707326d0c80326aa53c326a4b5bf262d41fb261c309d25bece64259eb530258a6ea4255ffecb2509c4b824cb7b2924a7e76c2485a934246ade96246554a62438a2592429651523fe6fae2310763b23038dd422ea3ac022daf26b22bdc500225c733222543c1c22521a04223682592219ec0a21a5f96821a1d26720df43cc2081cc61207b34ed204aaf2d2046aaad203e530f1fd3d3851f608b651f3108e2
  | 7, 3 => 0x3c52b0633c3d49423c39fd5e3bf3e2703bd0b7833bc2d8a43b76a7473b23954e3afd7b253acd3e823a8b9b213a861c993a4766343a305add39de879e396f572d3950034038ad846e37dd7e8037a1ed1c378f31e8375fd1e83732d33a3724f45b36e4026d36c744ae36b6da9236ad5160363c57f4361b1af4359f67e7359aee6d357bcd57355e29ce354bc4fd3528ce783481847a34746a9f33d93c6b33ab0d08339be830330961a632e7627a329cbbfb3294bf40326a0621319b3e4231381b0730ccd1eb3055c0a6302ca7772fc976f62fbf18df2f7a1e352f7655c82eedfa852ee51d392edbd6b52ea0b9112e46479b2de85b922d90db782d770a592d6df75a
  | 7, 4 => 0x4afc5e1e4ac0774d4a5928364a3f78dc4a0d197449e125c649d602e849226c8f49148db048fa38cc48f889f848f0bd7d48ebd2aa4879fd83484e6acf475141bb472e33c146e1bded4696c818465e79d5462e19684609964845f6b58445c07cca457c5ed144d9dfff4461859e43cee64d43b9f0a343a9f84843555fb0433f660a432891ef4309ffd84305883642b779a34215deda4214fad141d622d341a8390641a4b5d6413ca696410d769640db2d8b4079af63405c8f3d40455b7a4025ca0a3f8b9abe3f49363a3f086e6d3ee6de3d3e9c5ebb3dff89d03df1aaf13d8620523d6d0b963d6054973d57f2ca3d18fbc93d0124c93cd7d7c23c9f3cdf3c8fe41f
  | 7, 5 => 0x584e132a5806ebe257c3519857797e5c56fffaeb56f2d96f56dbe56f56abec62569e2201568ff7f1567ee6cd56240dff55df5df855bb43f755ab6c46557f4cd9552722ed54ed1c755342fdb7531915d1530ec13f52f2fea452e996fb52acbe7d52943af552942b72528ca242523dc211520a3fab51efbb6051d2062b51bf3f2b51a4e00751099cc650c4b4ed5038abd64f9b055d4f943bc44f717d1d4f624ff44f490be64f0fba7a4ec05ebd4e9d19034e79bd534e7327324e2ce2974e00c0ea4de27c5e4de254b54dd111674dc27b5b4d2b306b4d17706a4cfd734b4cd8ba054ca60af44c1e35cd4bff26be4bf147df4bb8974e4b7591cb4b62f61f4b02825d
  | 7, 6 => 0x683fb3fc67f1c0d3679d352a67425c61673ddef96709aa6167044c4c668c477066742ba76659a12a66357542651506a464e30e6464789948645092fc6449b75d6401590263f935ea6379a6766347643b633af01163353df4631f350062b43c176284e04362623a3562542af86240ab8761f427ee61aa33686129ea2960c01645605a4fd26001a2b65f5d13a95f2a63495eebace45ec6f1c75ebcebc25e90082e5e1657ce5debf6475dc82fa15d9647d45d93d62e5d7bf2db5d6275f45d2e415c5d23bf8f5d1e66bc5c9fbd605bff541c5b2acd595a73054d5a7078f859f684b259f223e559d66aa0596cee2e5943cbfb5923c1c65905159658a5f17758905d13
  | 7, 7 => 0x76b015da766385db764692e6762a5dc1751c82e774e1bd61749b9886745a681c73f60c3a73a4532b73a1eeb77341d2fd72b28339729906d4727daf3d7263b2ee7260e48f721cd83370ffce1070cdf07470c4152b70946692707cee8d70675391704f94ac7005f1236fa6c90d6f69601f6f3b46226ebe77696e9f1e276e834bca6e38e6f66ddedbb86db8095f6d550f7b6d483b2f6d2657c06ce170276cdc675f6cd622c66cbe1d396c8fa51c6bed6d236be1bd3a6bcb63fb6b89f08a6b7c11ab6b6909ce6b58c0516b46b4d16af785736a7ff6686a510b386a4f22086a2a46cf6a0139de69c0add469c031bf692e70ee6905cc4e68ff5c7d68b561d0688d1b55
  | 7, 8 => 0x85faf2fb85e99b5485e28a2b8562e87285520fcd8549f6d285210b03850f030e84e9742a8492c7cd83c5bc52838341f483833bd7834a6d93833df90383233d80830766bf828511a48241b05982121d0d81bd8a2f81b633a580ca3544806266ad804281917fb9fc427f97da8d7f5f0e0b7f27d8097f1797dc7ecd8d627ebd26667ebbf6017e8559377dfd47397dad4e397cd372a07c439fcf7c0721267bf0d3337bc86ac17ae97d0f7ac854af7ab597257ab2c9087a9f7e307a70b12879c9043d7952d274794717d6791d9b417900675a78f04d34785a178978493a7f77d135d07733bc5377211a3f76f0de3376f0916b76eecc3f76ec02b076db0b2e76bdf4b9
  | 7, 9 => 0x92b08ece928df768928cbda5927d8384927a567e926d751e9262028d925c0be492278ab591bec626913b5e9f9074f28c9037c66b9011f582900c696690061e318fe9ad8f8f6e24048ebf00228eb06ba68e7679718e4941358e27eed18e2374cd8e21c9a38e0d834f8df2ab598dce939b8dbfa66d8d7f04bb8d6fdaea8d6bb4b28d3d413a8d1e3ac28ce77a638c8386ea8c1a6ee88bedc1998bc68b508b8fda438b7e195e8b3e939c8b308e208aef68758ada8b1e8a8bfac78a4b2c048a18c2888a0d10dd89beef4c89605ac288edfe0d88ede028886bb2a5881ad299877c8a9f877910e2876b3203872610b88708035286bb6894867726a18651842c8635a6fc
  | 7, 10 => 0xa1689281a141bf77a0b26703a07b3991a02ef21b9ffd08839f9262399eab30d29e6bbe4b9e58572e9e14ab229db654639da1794d9d42bc1d9d3121ea9ce015509ccaae389c97dd089c55bf839c1021289bfcd7929b71391a9b56a6c89b308e9f9b1dd7b09aec1f2b9ab47d5a9ab0be7a9a9c46339a81c9ca9a36658d99bbfbc9997d4564996c23f4992c67909882e2ec98553ede984899db98411d81981b7e9297a5128c978d297c974e731797251c989721f5ed9713ecb196ac2a8596a4b77d9690ba6e9680ac86967182b5965f3458965531e69603a498955a0898944ede0094331b659409b1f093f42b8d9396353d93527dd59351acbb934043b892ef4533
  | 7, 11 => 0xb0e1dcffb080f6ebb07bc511b0480e0db01ae1b0b00d02d1af1123ebaf01b67aaee65ee3aec64c0eaeba478dae8d3699ae5c9576adab993dada32de2ad85a160ad6e1b08ace974c5ac8a86ebac3ab49dac296414ac23afedabe5308aabbe6e52ab962e79ab94b348ab8e7545ab47af95aab1140caaa935daaa87c3f1aa75a9a3aa3f12b1aa38618daa2867c5a98e4816a98c5b5da909e4c1a8e78fc4a8d9852aa8d69abba80d4bfda8098f40a71939e5a70b5b06a6910249a661d0dfa6395456a5e4c2a9a5d7b751a5cabbeaa5103ec2a4dede88a4a02823a499e38aa486547fa3f2435da39764cea36baaf7a309310ca302d5f5a2f4f716a25e4bf1a16c4690
  | 7, 12 => 0xbfa41077bf74ae55bf46884bbf01fb40bef5700abef1afedbee065e9be907f01be6b5265be2639d5be107ab6bde1cfb5bddd5bacbd3f82f8bd2744b8bcf5d0c6bcb2dff7bc5e25f5bc545819bc18011abc008a33bbec3344bb3f92c0bab08b31baa8a17cba9e7ab4ba477786ba45dd7fba40b91ab9782853b959c3c0b85c2f59b84d21e0b81d78f4b7a3f583b7610a65b713f0d0b6edc245b69fded2b67d321ab67cc233b65f3e8fb644e080b59a84ddb55b444cb559ed2fb52557b8b3feb3cab354b256b32b1ae2b315333eb2f03ccbb2dc7687b2572353b253eee6b22e7c90b210ca3fb20ffb62b18cc501b17d9b30b12375bdb108215ab0f51e5bb0ec7e1f
  | 7, 13 => 0xd0ab600ed0a7e5c1d0317033cfca0951cf9551ebcf84bc20cf6e15b1cef7401aceecb93fcecb96dfcec64beccea2794cce412b29cdfcbe79cdd2d617cd6ebd58cc0d7bc5cbfcbae9cba07d9ccb191b4ccae6d7d7ca5eb5a5ca35eab9c9e65a89c9e24337c9d88a90c9d46458c8d8951dc8cd18f2c876c3bec7ad77bcc7a9b843c7554d2ec7466283c707ac1ec6b603d4c6398efac5e58a67c5dca5abc5d3e588c5c226a0c59d6c30c57cede8c577bfccc52f7576c4eae2e7c4d4624bc4ad7d99c4ac2c82c483e9fec4605fcec3935453c37f968dc33e8ebcc3334588c31b6fd9c30bd3fac23de552c237985ec1c6e06ec16463c6c150c440c110cb7dc07ccfee
  | 7, 14 => 0xe1fe325ee1e7aed7e1ccafbce0f3695fe0d9cf49e0d27efae088d44de07b344ee044fe41dfdba1afdfb32b5bdf71e0b2df6d0221df41afa0dec9aaa0dec49712de7f8515de0efbc2ddfd151addd7f9c9dd0995b1dcd6712cdc55cfb7dc240579daf5c757da8fa153da26b2c9da0af02ed9eccea3d9e7a089d9b9b7a8d9ab6bc3d988b69cd986de71d96359b3d90de9d2d8f62b1fd8e7dfa1d8dd76c6d89de169d8653959d7c2c847d7c0c947d76eed8dd7661623d6fe6644d697c1d4d64007d5d62ad27fd5d13c99d56748abd3fa20bfd3c1c38ed3b34341d3a21f4ed2da325bd27a66b2d229a3e5d1d3f658d1b38e6dd17f337bd1786b89d121cb88d0dd3a20
  | 7, 15 => 0xf15afe71f14d1f92f11d8484f109fd47f0f10dbef0dd9aa2f0c5c7cbf053c1fdefdfd1c7ef7de2e4ef4adc1aeef3064deec76f65eeae7dabee6bbfe2ee22ff53ee1e2c58ee185818edf5513bede64ad6ed74eae1ed10ebe0ecfeda8beca193e2ec164c1eebc28ee5ebb77889eb7a065aeb3fcd10eaf7dac4eabec0cdea782c38ea72c195ea555bf2ea39f55dea206746ea04555ae9d3bc26e9b38944e9599105e8f19d4fe8b54ab1e8b03ee3e86f0f45e7a75556e73c37a0e7283c3de7199440e606f433e5d4dd4ce5b5122de575a6eae49194eae48a3599e45c7de4e3ed24d8e33582dbe32cc12de2f7dbbfe2f6cc76e2e94854e2e453e9e2897b1ee21fca1d
  | 7, 16 => 0xffcceadcffabe638ffa13466ff939cefff5a28feff3df527ff3992a2fed37441febf47eefd875a02fd797b23fd75d7f8fcf8d17ffce2758bfcb4afe6fcb0a9dbfc3e0176fbefb591fbe5e7c4fb7259a6fb192d73fac274d4fabc44b5fa6ea56df9092d95f9091127f8b72109f80ff336f7fbcecdf7e68aa8f7c476a1f772bfb1f76d67adf762f14af74120e2f6f16d4af6e94291f6657479f637ead7f5596f20f5210d0ef4535bf8f30eb1d1f2e571d9f22186e7f1c1f496
  | 8, 0 => 0xf33b5fd0dee29a6ad1efb8f3c2afde01b47be621a6563cc3a1f16def9493b4628ab84b5d7e1a8a56764e5f6161ca40085e22a75455df5df85059633d42b779a33e277fff2efbd9641606144c
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x1011550030173101155004017210550504401
  | 4, 0 => 0x1844250830000101155003010010550504301000000000000b0000000104104000000000000c0018c405003000011821484301000000000000c000004050020100041454403010011821484301000000000000b00000405002000018c40500301001884150430000184425083010018841504301000000000000c00118214843000011821484301
  | 5, 0 => 0x1182148430000000000000040000051109200000000000000100000000511030018841504300000000000000c001844250830000000001041040018c4050030000000001041040000000100105000000000000100000001001050000045085201000000000000a000000000000a0000000104104001844250830000000001041040018442500300001884150430000000454842000018c405003000000000104104000000000000700000000000010018c405003000000000104104000000010010500000000000010018442508300
  | 5, 1 => 0x1044020100000000000090018c4050030100000000000030018442508300000000000000c00000001001050000000000000000000010010500184425083000000000104104000000000000b000000000000500000000000030000000104104000000000000a00000000000010011821484300000000010410400000000000060018841504300001884150430100000450852000000000000001000000000000100000000000040018c4050030000184425083010018442508301000000000000c00118214843010000000104104
  | 5, 2 => 0x1884150430100000001041040011821484301001884150430100000000000020018c40500300000000000000b00000531012000011821484301000005048420100000405002010000040500200001182148430000000000000020018841504300000000000000a000004250820000118214843010000021484200000000000000b001182148430000184425083000000000000002000001044020000000001041040000000000003000001550020100000000000020000000100105000000000000b00000001041040000000101100
  | 5, 3 => 0x4050020000184425083000000000000001001844250830100000000000090000000104104000000000000b000000000000b0000000104104000000010410400000000000010018c4050030100000001041040018c40500300000000010410400118214843000018c40500301000005050420100000000000090000000104104000000000000b0000000000002001844250830000000001041040000000000002001884150430000188415043000018442508300000000000000c000000010010500000001041040000040500200
  | 5, 4 => 0x300000001041040000000100105000000000000b0000000104104001884150430100000000000060000000000002000000000000b00000000000060000000105103000000000000a000000000000b00000450852010000000105103000000000000b000000000000b0000000104104000000000000b00188415043000000051109201000000000000c0000045440201001182148430000000000000060018841504300000004508520100000000411000011821484300000000000000600000000000020018841504300
  | 5, 5 => 0x200000000000090018c40500301000000000000700184425083000018c405003000018c40500300000000000000b0018c40500300001844250830000000001041040000021484201000000000000c00000001041040018c405003000018841504300000004150420100000000000020000000104104000005210520000000000000070000000104104000000000000c00000000000010018841504300000000000000100184425003000000000000002000000000000c00118214843000018c405003000018c40500301
  | 5, 6 => 0x90000045041200000000000000c000000000000b001182148430000188415043000018442508300000000000000b0011821484300000000000000c00000000000090000000105103000000000000a0011821484300000000000000b0000000104104001182148430000184425083010000041504200
  | 6, 0 => 0x104402000000050484200000000000000c00000000000020000025041200000000000000b00000000000020000000104104000000000000b00000000000010000000105103000000000000600000000000070000045041200000000000000200000000000040000000000006000004508520000000000000030000000000002000005310120000000450412000000041504200000002148420000000000000050000000000002000000000000500000000000030000000000005000000000000400000415042000000000000005
  | 6, 1 => 0x35041201000000000000b0000000000004000000000000600000000000070000000000003000000000000600000450412010000000000003000000000210000000000000040000010440200000000000000a000000000000100000000000020000041504201000000010010100000405002000000000000002000004548420000000450852000000035041201000000380a200000000000000400000001041040000000000003000003504120000000000000020000045041201000000000000700000000000030000000000006
  | 6, 2 => 0x45402200000001044020000000000000050000000000002000000000000300000000000030000000000004000000000000500000254022000000000000002000000000000200000000000020000000000004000000000000400000048022000000000000006000000000000300000204802000000000000001000000010410400000000000060000045085200000000000000100000000000030000000000002000000000000c0000000000003000000000000800000531012000000000002100000005210520000000254c0200
  | 6, 3 => 0x4508120000000425082000000000000002000000280620000000000000000000045041200000000000000900000000000060000000000002000000000000200000000000000000000100100000005110920000000000000060000000000009000000000000100000254c4200000004150420000000000000020000000000003000000000a100000000000000700000521052000000000051103000004504120100000000811010000021484200000000480e200000000000000700000000000050000025440200000000000000b
  | 6, 4 => 0x600000000000030000000000004000000000a1010000000105103000000000000b00000000000030000000000005000000000000400000000000030000045484201000000000000700000000000070000000000006000000010c1000000000000004000004150420000000000000020000000000009000000010910100000038062000000000000003000000010410400000000411000000000000007000000000000c00000000061000000000000002000000000a101000005210520000000531012010000000000003
  | 6, 5 => 0x400000000000070000020480200000000000000b0000000000003000005048420000000000000060000045081200000000000000400000000000040000000000004000005110920000000000000030000000000003000000000000500000054122000000000000001000000000000b000000000000b000005110920000000000000050000045484201000005210520000000000000070000000000004000000000000400000000000010000000000002000000000000200000250412000000045085200000000000000b
  | 6, 6 => 0x45484200000000000000c000000000000900000000000030000000000002000000000000700000250412000000003802200000000000000c00000000000020000000012100000005250c2000000000041103000000000000200000000000020000010440200000000000000200000000000070000045041200000000000000200000000000040000000109101000000000000500000000000010000000000007000000000000300000405002000000000000006000004150420000000000000060000000000002000000000000b
  | 6, 7 => 0xc0000000000006000000000000300000214842000000000000009000000000000600000000000030000000000003000000000000200000000000070000000000003000004504120000000000000010000000006101000004504120000000000000020000041504200000000010410400000000411000000000000004000000000000200000214842000000000000004000000000000300000521052000000000000006000005210520100000000000090000045085200000002504120100000000000040000000000005
  | 6, 8 => 0x45041200000000000000b000003504120000000501092000000000000007000000000000b00000450412010000000000002000005110920100000000000020000042508200000000000000c000002148420000000000000030000025500200000000000000b000000000000a0000000000003000005110920000000000000070000000000006000005010520000000000000060000000000006000003504120000000511092010000020480200000000000000b0000000000007000000000000600000000000020000040500200
  | 6, 9 => 0xb0000000000003000000000000700000521052000000000000006000000000000b000000000000300000250412000000000085101000000000000500000450852010000000000006000000000000b00000000811010000000000003000000000000000000000000070000000000005000000000000300000000000010000000000007000000010010500000000021000000050484200000000000000b0000041504201000004504120000000000000030000000000006000000000000200000000000070000000000002
  | 6, 10 => 0x415042000000000000003000000000000700000000c0100000004504120000000000000060000000000003000000010110000000450412000000020480201000000000000c00000511092000000000000007000004508520100000000000090000000000007000004508520000000350412000000000000003000000000000c00000504842000000000101100000000000000c000000000000200000000000020000000000004000004150420100000511092010000045484200000005310120000000000000010000050085200
  | 6, 11 => 0x10000041504200000000000000200000000000000000000000004000000000000200000000000060000000105100000000000000600000450852010000010440201000005048420000000254c020000000000000070000020480201000000000000b00000000c410000000000000000000000000006000000010510300000000000040000000000003000000000000500000000000050000040500200000000000000200000454842000000004802200000000000000b000004540620000000000000020000000000007
  | 6, 12 => 0x20000045484200000004548420000000000000090000045041201000005250c20000000510812000000000000002000004250820000000350412000000020480201000000000000c000003504120000000000000060000000000002000000000000300000000000060000000101100000000000000b000000000000c000001044020000000425082000000025500200000000000000200000000000040000045085200000000000000300000000000090000000000000000000010510300000214842000000000000004
  | 6, 13 => 0x50000053101201000000000000300000504842010000000000007000000000e1000000000000002000000500a20000000000000060000021484200000000000000200000531012000000000000006000000480a200000000000000c0000000000004000005110920000000000000020000000100105000000000000600000350412000000045041201000000000a100000004250820100000411002000000053101201000000000000600000059002000000000000009000000000000700000000000040000000000002
  | 6, 14 => 0x2000005310120100000000000030000045085200000005108120000000000000020000050484201000000000000b00000000000090000000000002000000000000c0000000000006000003504120000000000000020000000000007000002504120000000405002000000051109200000004250020000000000411030000045484200000000000000200000000000020000000000003000000000000400000254022000000000000008000000000000b0000050484201000004150420000000000000070000052105200
  | 6, 15 => 0x61000000000000003000000000000700000000000040000000040101000000000000900000000000040000000000003000004508120000000521052000000000002101000000000000400000531012000000010440201000000000000200000000000040000000000002000000000000300000000000020000000000003000000000000300000000000000000000000005000000000000b00000000000090000045041200000000000000600000450402000000000000004000000000000400000000000070000000000002
  | 6, 16 => 0x425082010000000002101000000000210000000000000070000021484201000003500a200000000000000400000104402010000000000006000004548420100000000000020000050085200000004250820000000000000070000051101200000000000000200000450852000000000000003000000000000300000000000090000051109200000000500a2000000000104104000000480620000000204802000000025440200000000000000300000415042000000045484201000004508520000000000000070000050484201
  | 6, 17 => 0x380a200000004508520000000000000020000000000001000000000000300000000000050000035041201000000000000b000004250820100000000401000000000000004000000000000700000000000070000051109200000000000000300000000000050000000000007000000000000300000531012000000000000007000000280220000000000000020000000000000000004250820000000254c02000000045041200000000000000200000000000090000000000003000000000000700000204802000000000000009
  | 6, 18 => 0x25041200000000000000500000204802000000000000002000000000000500000450852010000045484200000000000000200000000000060000052105200000000000000300000000000020000000000007000005010520000000001041040000000000003000000000000600000000000020000021484200000005250c20000000000000020000000000004000000000000600000054062000000025041200000000000000b000000000000000000000851000000021484201000000000000000000000000020000000000006
  | 6, 19 => 0x3504120000000000000020000000084100000000000a1010000051109201000000000000200000504842000000000000006000000000000700000154022000000000104104000004250820000000450412000000020480201000000000000200000405002010000000000003000004508520000000450412000000000000003000000000000100000000000090000000000004000000000000c000000000000600000000000020000000000002000000000000c0000000000002000000000000700000000000090000000000004
  | 6, 20 => 0x600000000000020000000000004000000000e100000000000000300000415042000000050109200000000000000b000004548420000000000411030000000000003000000380620000000531012000000000000001000005010520000000504842000000000000005000000000610100000250412000000000104104000002048020000000405002010000010440200000000000000a00000511092010000001802200000004050020100000000000030000000000000000000000000b0000020480201000000000000b
  | 6, 21 => 0x20000000000000000000004110000000000000020000000000000000000000000b000000000000100000450852010000000000003000000000000300000000000020000000100105000000000000900000000000070000000000002000000000000500000521052000000000041100000000000000b00000001041040000000000008000000000000100000450412000000000085101000004508520100000059002000000000000002000000000000b000000000000c000000000000700000255042000000000085101
  | 6, 22 => 0x3000004548420000000250412010000000104104000000000000700000000000030000000000003000000000000200000000000020000000000005000000000000200000000000060000000000008000003504120000000000000040000000000003000000000000100000000000090000000000002000000480e200000000000000b000000000000c000000000000900000000000010000050484200000004250820000000504842000000025041200000000000000200000511092000000000000007000000480a200
  | 6, 23 => 0x504842000000035041200000000000000200000250412010000000000002000000000000100000000000020000052105200000000000000400000000000030000000000002000005310120000000000000000000042508200000000000000600000000000020000041100200000000000000700000504842000000000000007000000000000b00000059042000000000000002000000000210000000204802000000000000002000001044020000000000000030000000000006000004150420000000000000040000040500200
  | 6, 24 => 0x40000053101200000004250020000000531012010000000104101000000000000300000000000020000010440200000000000000300000511092000000000000002000002148420000000000000080000000000002000001541220000000511092000000000002100000000000000200000450412000000000000002000000000000500000000000070000000000007000000000000600000000411030000000000003000005010520000000001051030000000000006000004508520000000000000020000000000006
  | 6, 25 => 0xc010000000450852000000040500200000004150420000000415042010000021484200000000000000300000000000070000000000000000000000000700000000000020000000000005000000000000300000250412000000000000009000000000000200000250412000000000000008000005310120100000425082000000000000007000000000000900000531012000000053101200000000000000600000048062000000025041201000000000000b0000000000007000000000000600000000000030000040500200
  | 6, 26 => 0xa00000000000060000000000000000000000000200000001041000000003802200000000000000300000000000040000000000006000000000000b0000000000003000005110920000000000000040000000000007000002148420100000000000020000050484201000000000000300000204802000000000000001000000000000400000000000060000002802200000000000000200000350412010000000000002000000004110000000000000070000000000005000000000000b00000000000030000000000006
  | 6, 27 => 0x700000001091000000000000000000000000000400000000000020000045484200000002148420100000405002000000000000002000000000000b000000000000200000405002000000000000002000000000000300000000000020000000101100000000000000400000000000070000000000004000000000000b000005210520000000000000060000000000006000001044020100000500852000000000000002000003504120100000000000020000000000009000000000000200000425082000000000000002
  | 6, 28 => 0x405002000000025041200000000000000400000000000030000000000002000004250820100000000000020000000000001000000000000700000425082010000000000007000000000000200000000000030000000000009000000000000300000511092000000000000006000000000000700000000000040000040500201000000000000000000001091010000035041201000000010410400000000000030000045085200000000000000200000000000020000000000005000004508520000000000000020000000000003
  | 6, 29 => 0x25402200000000000000300000000000020000000104104000000000000600000000000040000010440200000004508520000000000000030000000000007000000000a101000000010410400000000000060000000000003000000000000600000254c42000000000000006000002504120000000000000030000052105200000000000000200000000000020000000000007000004504120000000405002000000000000000000000000000700000204802000000000000002000000180220000000000000040000000000002
  | 6, 30 => 0x200000000000010000000000007000002504120000000425082000000000000003000000000000600000511092000000050109200000001044020000000521052000000000000006000000000000600000204802000000000000006000000000000000000000000030000000000003000000000210100000000000040000053101200000000000a1010000010440200000000000000600000504842000000000000009000002148420000000000000050000000000004000000000000200000204802000000000000002
  | 6, 31 => 0x5310120000000000000030000000000002000000000000b0000052105200000000000000700000511012000000042508200000000000000200000000000040000052105201000000010110000000000000020000000006101000000000000300000000000020000000000003000002550420000000000021010000051109200000000010410400000000000040000000000004000000000000600000000000020000040500201000000000000c00000058402000000000108100000003504120000000000000030000002806200
  | 6, 32 => 0x4504120000000425002000000000000003000000010110000000000000060000045040200000001044020000000521052010000000000006000000000000b0000000000005000000000000500000000000070000021484201000004050020000000000000030000005840200000004508520000000000000020000000000002000000000000b00000521052010000000000004000004504120000000454842000000025041200000000000000600000000061010000000041100000000000000400000504842000000000000002
  | 6, 33 => 0x851010000000000004000000000000600000250412010000000000006000002148420000000000121000000000000001000005310120000000521052000000000000003000005048420000000000000040000000000004000000000000c000000000000b0000052105201000000000000600000000000070000000000005000000000000a00000204802000000000000007000000000000b0000000000006000000000000b0000000000002000005108120000000350412000000005904200000000000000a0000000105103
  | 6, 34 => 0x900000405002000000000000006000000000000200000000000000000000000009000004250820000000001041040000000000006000004110020000000000000070000021484200000000000000000000511092000000000000003000000000000400000104402000000000000009000005110920100000000000030000000000002000000000000500000000000050000000000007000004548420100000415042010000000000003000000000000200000000000050000045041200000000000e1000000000000005
  | 6, 35 => 0x3000000008510100000104402010000021484200000000000000c000000000000c0000000084101000000000000600000454842000000000000002000000000000600000511092000000000000004000000010410400000000000060000045484200000000000000600000000000070000000000001000000000000400000000000060000000000005000000000000300000000000030000035041200
  | 7, 0 => 0x41100000000000000100000000000060000000000007000000000000400000000021000000000000004000000000000300000000121010000000000004000000000000200000000c41000000000085101000000010010000000000000060000000000006000000010510000000001041000000000000007000000000000700000001051000000000012100000000000a100000000000000b0000000000006000000000000400000000c4100000000000000200000000811000000000000007000000001210100000000c4100
  | 7, 1 => 0x300000000000090000000000000000000000000900000000000030000000085100000000000000500000000121010000000000002000000000a10000000000000020000000080100000000000000300000000c8100000000010410000000000061000000000040100000000010910000000000c01000000000000004000000000000700000000000000000000002100000000010c100000000000000600000000841000000000000006000000000210000000000c0100000000000000200000001011000000000006100
  | 7, 2 => 0x1081000000000081101000000000000700000000801000000000006100000000000000200000000000040000000000001000000000000100000001091000000000000003000000000a1000000000000006000000000000700000000000010000000000006000000000000700000000021000000000000006000000000000600000000000030000000081101000000008410000000001001000000000000003000000010510000000000000090000000000004000000001210000000001081000000000108100000000000a100
  | 7, 3 => 0x1000000000000500000000000060000000104101000000010110000000000000040000000000001000000000000b000000008510000000000000030000000000004000000000210100000000000040000000000000000000000610000000000851000000000000002000000000000900000000121000000000080100000000000000b0000000000001000000000210000000000000040000000104101000000010c100000000000000500000000841000000000000009000000000610000000000000070000000040100
  | 7, 4 => 0x300000000000040000000105100000000010010100000001041000000000000003000000000000100000000000070000000000001000000008110000000000000090000000109101000000000a101000000000000500000000c4100000000000000c000000000000c000000000000400000000000040000000000007000000000000900000000021010000000000004000000000610000000000811010000000100100000000004110000000000000070000000000001000000000000100000000000020000000084100
  | 7, 5 => 0x10000000000001000000000000200000000000010000000104100000000000000100000000000040000000000004000000000000100000000000020000000000003000000000000400000000801000000000012100000000010010100000000021010000000000004000000000a1000000000006101000000000a10100000000c010000000000000030000000109101000000000210000000000000020000000000002000000000000600000000841000000000000006000000001210000000000000030000000108100
  | 7, 6 => 0xe1000000000000001000000004010000000000000050000000000004000000000a100000000008510000000000c01000000000000002000000000e100000000000000500000000000050000000100101000000008010000000000000010000000000000000000000a10100000000c8100000000000a10000000000851000000000000005000000010810000000000411000000000012100000000000000b000000000000c000000000610100000000000010000000012100000000000210000000000000060000000040100
  | 7, 7 => 0x10810100000000000020000000000003000000000000600000000c4100000000000000c000000000000100000000061000000000084100000000010410000000000061000000000012100000000000000b00000000811000000000000001000000000000100000000000020000000081100000000000000c000000000000400000000000040000000080100000000010110000000000000060000000006101000000000000400000000c010000000000061010000000100100000000000000400000000000070000000109100
  | 7, 8 => 0x40000000000003000000000000700000000000000000000012101000000000210000000000000020000000041101000000000000700000001081010000000000002000000000000300000000811000000000000003000000000000300000000000030000000000004000000000000200000000000000000000000007000000010010000000001051000000000000006000000010c10000000000000020000000108100000000004110000000000000010000000000005000000010810100000000000010000000012101
  | 7, 9 => 0xc4100000000010010000000000121010000000002100000000010410000000000021000000000000005000000000a100000000000000b0000000000006000000000a1000000000000004000000000000400000000000050000000002101000000000000200000000411010000000012100000000000000600000001011000000000000004000000000000300000000c01000000000000002000000000000900000000c8100000000001210000000001091000000000000001000000000610000000000000070000000000005
  | 7, 10 => 0xc0000000000009000000000a10000000000401000000000000002000000000000700000000411010000000108100000000000000300000000061000000000000003000000000000600000000021000000000108100000000000000700000000121000000000012100000000000000500000000000040000000000004000000010510000000000811000000000000006000000000000400000000c81000000000000004000000000e100000000000000c000000008010000000000000070000000000002000000000000b
  | 7, 11 => 0xa10000000000000030000000000009000000000000b00000001041000000000081100000000000610000000000000060000000000002000000000000100000000021000000000012101000000000e10000000000000070000000000003000000000000600000001081000000000081101000000000000200000000411000000000109100000000000000600000000c010000000000000090000000109100000000008510000000001001000000000000002000000010c100000000000000400000000000010000000012101
  | 7, 12 => 0x2100000000010910000000001051010000000100100000000000000b000000010110100000000000040000000000003000000010110100000000000010000000084100000000010810000000000000020000000000007000000000a10000000000000010000000000004000000000000200000000061000000000000003000000000e1000000000000004000000008410000000000000040000000000006000000010c100000000000000300000000c81000000000000003000000000000400000000000090000000101101
  | 7, 13 => 0x20000000000009000000004110000000000c0100000000000a10000000000000010000000000002000000000000c000000010c1000000000101101000000000000b000000000000b00000001051010000000000004000000008110100000000121000000000000002000000000e100000000000610000000000841000000000000003000000000210000000000c8100000000000000100000000121000000000000000000000000000500000001001010000000000005000000000000300000000000020000000104100
  | 7, 14 => 0x200000000000040000000002101000000000610000000000000030000000105101000000000000b00000000000040000000108100000000000000200000000000010000000000002000000000000700000000061000000000085100000000000000b0000000081100000000010410000000000000020000000000001000000000a10100000000121000000000000001000000010010000000001011000000000000003000000000000400000000401000000000100100000000000a10100000000811010000000000005
  | 7, 15 => 0xb00000001001010000000000005000000000000000000000000040000000000001000000000a10100000001091000000000000007000000000000600000000401010000000002100000000000000200000000000030000000012100000000000000500000000021000000000002101000000000000500000001051000000000000002000000000000300000000000010000000085100000000010c100000000000a101000000000000b00000000411000000000000002000000000000c00000000c41000000000080100
  | 7, 16 => 0x10110000000000061010000000000001000000000000300000000000040000000041100000000000a10000000000000030000000000002000000010010100000000851000000000006101000000000000200000000c81000000000108100000000010510100000000000070000000000002000000000a10100000000000030000000040100000000000a10100000000000000000000000009000000000e100000000000210000000000000090000000012100000000010010000000000811000000000084100
  | 7, 17 => 0x50000000084100000000004110000000000000060000000105100000000000000100000000000020000000081100000000000000200000000021010000000000009000000000610100000001001000000000012100000000000000300000000c410000000000c81000000000000009000000000000400000000000010000000012100000000000000300000000121000000000000002000000000210000000000c01000000000012101000000000000300000000000020000000006101000000000e1000000000000001
  | 7, 18 => 0x6100000000010510000000000851010000000000002000000000000300000000000030000000006101000000000610100000000000040000000000002000000000000900000000c4100000000000000500000000401010000000012100000000000210100000000c0100000000000000900000000000070000000100100000000000000300000000000060000000000005000000000000b0000000080100000000000000b000000000a100000000000000b000000000000200000000000020000000101100000000000000b
  | 7, 19 => 0xb00000000000010000000012101000000010110000000000000010000000085101000000000000400000000021010000000000004000000000000400000000c8100000000000a100000000010c100000000004010100000000000040000000006100000000000000400000000061000000000000001000000001210000000000021000000000000003000000001210100000001041000000000108100000000010410100000000000020000000000001000000010510000000000000070000000000003000000000000b
  | 7, 20 => 0x300000000000070000000000005000000000000100000000401010000000000006000000000a1000000000084101000000004110100000000c4100000000000000700000001091000000000100100000000001210000000000000060000000080100000000000000c00000000000040000000000006000000000000400000000000010000000002100000000000a100000000008110000000000000020000000000006000000000000900000000000030000000000009000000000e10000000000411010000000101100
  | 7, 21 => 0xc41000000000081100000000001210000000000c81000000000000007000000000000400000000000060000000000007000000010c100000000008510000000000000000000000002100000000008410100000000000060000000000004000000000a1000000000101100000000000000700000000000050000000000004000000004010000000000061000000000000002000000010c100000000000e1000000000000003000000010110000000000851010000000000005000000000000300000000000020000000105100
  | 7, 22 => 0x50000000000007000000010110100000000000020000000084100000000008110000000000000020000000000003000000008010100000000000020000000000007000000010410000000000000060000000000003000000010010000000000000060000000084101000000000000300000000411000000000000002000000000a1000000000000004000000000a1000000000080100000000000610000000001051000000000000002000000001210000000000c0100000000000000c00000000000010000000000001
  | 7, 23 => 0x30000000040100000000000a1010000000000004000000010910000000000000060000000000000000000000000300000000121000000000000001000000000a10000000001011010000000080101000000010c1000000000000002000000000000100000000c81000000000000003000000000000000000000000040000000000004000000000000300000000c8100000000000610000000000000050000000041100000000000000600000000000010000000006100000000000210000000000021000000000000003
  | 7, 24 => 0x40100000000000000700000000061000000000000001000000000000500000000000060000000080101000000010910100000000000090000000000007000000010410000000000811000000000000004000000010510100000000000070000000041100000000010010000000000000010000000000006000000000000400000000851000000000109100000000000210000000000c01000000000000001000000000000b000000000a10000000001051000000000000002000000000000500000001051010000000108100
  | 7, 25 => 0x1091000000000002100000000000000200000000021000000000000005000000000000000000000000040000000012100000000008410000000000000020000000040100000000000000400000000000020000000000004000000010110000000000000010000000000002000000000a10100000000121010000000000001000000000000100000000000020000000085100000000010c1000000000080100000000000000000000000000000000000000003000000000000b0000000006100
  | 7, 26 => 0x10000000085100000000000000300000000000040000000000001000000000a10000000000841000000000012100000000000000c000000000000600000000000040000000000005000000000000b00000000401000000000000006000000010c1000000000000007000000000610000000000000010000000000001000000010510000000000411000000000000002000000000000200000000000060000000000004000000000610000000000c8100000000000000600000000c4100000000000000b000000000a101
  | 7, 27 => 0xc000000000000300000000411000000000000001000000000610100000000c41000000000000002000000010c100000000000000700000000801000000000040100000000000a100000000000000c00000001041010000000000007000000000000500000000000060000000006100000000008410000000000121000000000101100000000000000b000000000a10000000000000010000000108100000000000000300000000000060000000000007000000000210000000001041010000000100100000000000000c
  | 7, 28 => 0x200000000c810000000000000020000000108100000000004110100000000000010000000104100000000000000600000000811000000000000004000000000000400000000000000000000000004000000010910100000000801000000000104101000000000210100000000c01000000000000007000000000610100000000000010000000109100000000000000400000000000060000000084100000000000000100000000000020000000105100000000000e100000000010910100000000851000000000000002
  | 7, 29 => 0x3000000000a10000000000021000000000105100000000000000c00000000000090000000040101000000000000000000000841010000000002101000000000e100000000001210000000000411000000000109101000000001210000000000c410000000000851010000000000004000000000000b00000000000070000000000009000000000a1000000000084100000000004010100000000000040000000002101000000010110000000000000020000000080100000000010410000000000000020000000000006
  | 7, 30 => 0x700000000c0100000000000000900000000000040000000000007000000000000b00000000841010000000108100000000010c1000000000002100000000000a10000000000000050000000000001000000008010100000000000020000000101100000000000210000000000000060000000000009000000000000300000000c81000000000041100000000000a100000000000000400000000801000000000000002000000000000200000000000040000000109100000000008510100000000000050000000006100
  | 7, 31 => 0x81100000000000000b000000000000b00000000851000000000000009000000000000400000001081010000000006100000000000000400000000000060000000000004000000000e100000000000610000000000401000000000104100000000000000700000000411000000000084101000000001210000000001051000000000000004000000008010000000000000010000000000006000000000a100000000000610000000000c410000000000000030000000108101000000000000200000000000020000000100100
  | 7, 32 => 0x5000000010810000000000841000000000000006000000000e10000000001011000000000000000000000000210000000000000060000000080101000000000a10000000001081010000000000002000000004010000000000c410000000000000030000000000004000000000000300000001091000000000000003000000000000300000000000060000000002100000000000000200000001041000000000000004000000000000400000000000000000000000004000000000000900000000c0100000000010c100
  | 7, 33 => 0x2000000000000500000000000000000000006100000000000000c00000000851000000000109100000000008010100000000c010000000000c8100000000000000b000000000000100000000000050000000040100
  | 8, 0 => 0x10000000000001000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000100000000000010000000000000000000000000000000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_9 roots_9 8 s ws hint
  | 1 => checkCutEntry dom_10 roots_10 7 s ws hint
  | 2 => checkCutEntry dom_11 roots_11 6 s ws hint
  | 3 => checkCutEntry dom_13 roots_13 6 s ws hint
  | 4 => checkCutEntry dom_14 roots_14 6 s ws hint
  | 5 => checkCutEntry dom_16 roots_16 6 s ws hint
  | 6 => checkCutEntry dom_18 roots_18 6 s ws hint
  | 7 => checkCutEntry dom_12 roots_12 5 s ws hint
  | 8 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 9 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 10 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 11 => checkCutEntry dom_17 roots_17 5 s ws hint
  | 12 => checkCutEntry dom_19 roots_19 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_20 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
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
theorem z3_0 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_8 : ∀ i, 8 ≤ i → i < 12 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 8 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 12 → Z 4 i = true := range_split z4_0 (z4_8)
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
theorem z5_48 : ∀ i, 48 ≤ i → i < 51 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 48 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 51 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (z5_48))))))
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
theorem z6_128 : ∀ i, 128 ≤ i → i < 130 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 128 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 130 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (z6_128))))))))))))))))
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
theorem z7_144 : ∀ i, 144 ≤ i → i < 145 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 144 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 145 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (z7_144))))))))))))))))))
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

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4007717088 * 2 ^ 32 + 3938500800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_20.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_20 10 hT6 (by unfold IsConst; decide) low_20

def wit : Circuit := ⟨[⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [9, 5]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.or, [11, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_16219_aux

theorem PEqualNP.Outside.L_meta_16219 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717088 * 2 ^ 32 + 3938500800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717088 * 2 ^ 32 + 3938500800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_16219_aux.wit, PEqualNP.Outside.L_meta_16219_aux.wmono, le_trans PEqualNP.Outside.L_meta_16219_aux.wsize (PEqualNP.Outside.L_meta_16219_aux.lower s hs), PEqualNP.Outside.L_meta_16219_aux.weval⟩
