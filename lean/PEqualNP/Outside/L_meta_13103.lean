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

namespace PEqualNP.Outside.L_meta_13103_aux

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

def dom_0 : Nat := 0xf0000000f0
def goal_0 : Nat := 0xe000000080
def roots_0 : List Nat := [0xa0000000a0, 0xc0000000c0, 0xf000000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(5, 7), (5, 37), (6, 7), (6, 38), (36, 37), (36, 38)]
def r1sG : List Nat := [5, 5, 6, 6, 36, 36]
def r2sG : List Nat := [7, 37, 7, 38, 37, 38]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x71a83fb5
  | 3, 0 => 0x71a83fb5
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000c0000000c0000000a0000000a0
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_1 : Nat := 0xf000f000f000f0
def goal_1 : Nat := 0xe000e000e00080
def roots_1 : List Nat := [0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f00000, 5, 21)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0xff000000ff
def goal_2 : Nat := 0xea00000088
def roots_2 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f0, 34, 38)] (by decide +kernel) (by decide +kernel) low_0

def dom_3 : Nat := 0xff00ff
def goal_3 : Nat := 0xec0088
def roots_3 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0xf000f000f000f
def goal_4 : Nat := 0xe000a000c0008
def roots_4 : List Nat := [0xa000a000a000a, 0xc000c000c000c, 0xf0000000f0000, 0xf000f00000000]

namespace S_4
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (2, 18), (16, 18), (17, 19), (17, 49), (32, 33), (34, 35), (34, 50), (48, 49), (48, 50)]
def r1sG : List Nat := [1, 1, 2, 2, 16, 17, 17, 32, 34, 34, 48, 48]
def r2sG : List Nat := [3, 33, 3, 18, 18, 19, 49, 33, 35, 50, 49, 50]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_4.map (· &&& dom_4)
def goalM : Nat := goal_4 &&& dom_4
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x6ba3d11
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f00000000000f0000000f0000000c000c000c000c000a000a000a000a
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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
def goal_5 : Nat := 0xee00ea00ec0088
def roots_5 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

namespace S_5
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (2, 18), (5, 7), (5, 21), (5, 37), (6, 7), (6, 22), (6, 38), (16, 18), (17, 19), (17, 21), (17, 49), (20, 21), (20, 22), (32, 33), (34, 35), (34, 38), (34, 50), (36, 37), (36, 38), (48, 49), (48, 50), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 1, 2, 2, 5, 5, 5, 6, 6, 6, 16, 17, 17, 17, 20, 20, 32, 34, 34, 34, 36, 36, 48, 48, 52, 52]
def r2sG : List Nat := [3, 33, 3, 18, 7, 21, 37, 7, 22, 38, 18, 19, 21, 49, 21, 22, 33, 35, 38, 50, 37, 38, 49, 50, 53, 54]
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
  | 3, 0 => 0xc30cad94a485e6e908e5f8b105240629
  | 4, 0 => 0xd1ba7913ca0435d5a5a7474da1412d0a957581e96940f86b628184da616753e955683abe5292cf0742e753ed41b3d74131b43c3d2b17ee4728206f83267310691be6777d18b803fa12294ab80c1b8e6a
  | 5, 0 => 0xef164bbfe7a1edd4d8b20154cfb56fb3be43c575bb694c1ab6943d31b50fb2d6b46e6442ae2f9285aaf294a0a1cffb6397b5c12496bb5d0c8a64578186bd830c8449660472fb0af9628184da5ac8629855733a195471a15850eeb30f4f4e152849dedc2e48ab5f82418647863fafa5c13e6f1d623d3e009d39017e81302842c53025d50d2f17f7c428206f8320d129b41f650f8c1a4f9c3e17bdcd44133a4b1a0c5178f4077aa6ae074cd068
  | 6, 0 => 0xfd05eeb0d6fb56cec29480868a64578188ca29be6b85db7469ad921150eeb30f47baa0702f17f7c417bdcd44
  | 7, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x330033003300330011001100110011000f000f000f000f000000ff000000ff0000000000ff00ff0000000000550055000000000033003300000000000000ff
  | 0, 1 => 0xc000c000c000c000aa00aa00aa00aa00aa00aa0088008800aa008800aa00880088008800880088007700770077007700550055005500550044004400440044
  | 0, 2 => 0xee000000ee000000ea00ea00ea00ea00e000e000e000e000dd00dd00dd00dd00cc00cc00cc00cc00cc00cc00cc008800cc00cc00cc000000cc00cc00880088
  | 0, 3 => 0xff000000ff000000f800f800f800f800f000f000f000f000f000f000f0000000f000f000a000a000f000c000f000c000ee00ee00ee00ee00ee00ee00000000
  | 0, 4 => 0xff00ff0055005500ff00ff0033003300ff00ff0011001100ff00ff0000000000ff00cc00ff00cc00ff00aa00ff00aa00ff00aa00ff008800ff008800ff0088
  | 0, 5 => 0xff00ff00ff00aa00ff00ff00ff000000ff00ff00ee00ee00ff00ff00cc00cc00ff00ff00c000c000ff00ff00aa00aa00ff00ff00a000a000ff00ff00880088
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa2075947db4cd47585cb49207994
  | 4, 0, 0 => 0x91f6552d6c7dd44e5920753396c7dc4ce5922753316a7dd4cd59207592d647dd64d57585d339687dd64e591f7592d657dd4ce591f75239647595cb5921753396481e4ce5
  | 4, 0, 1 => 0x91f7992d6881d4ce5917553396c7db4ce5
  | 5, 0, 0 => 0x247ce1c55b247dd64e69207dd4ce6be47dd4ce6ba489d4ce6ba47dc4ce691f75338b60247dd64b50244ce14459a47dd4ce6ae47dd4ce691f7533876a647dd4ce691f75340e60247da4ce591f7533866
  | 5, 0, 1 => 0x91f753380601d4ce10359237da4ce60247dd387591f7564ce691f75344e691f75338a602481d4ce5b647dd4ce691f753381691f7544ce691f7594ce6b2a7dd4ce692075338b691f75338d691d6574ce6
  | 5, 0, 2 => 0x247dc4ce50247dd247591f79338b69e47dd4ce691f6554ce691f753388601f74e1c350247d54ce591f753382602474e1c4591f75938b6
  | 6, 0, 0 => 0x247d338559237dd4ce6b247dd4ce60247dd3875ba47dd4ce6024753384591f7533ce691f7594ce60247dd4ce591f75338b691f7533876
  | 7, 0, 0 => 0x247dd4ce5
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
  | 0, 0 => 0xfc7f1cff1c40033cf03c3f03ff003fffc00c78c003f1cc0003ff
  | 0, 1 => 0xe0000387300000000038000000003fffffffff1e300e038c
  | 0, 2 => 0xe000003bf30000fc3ffc78c0380e300e000003800000e0000
  | 0, 3 => 0xf03f00330c3f0cc30fc330c000cc001c300c380038effc0e0000
  | 0, 4 => 0xfff1e33fffc73fff1003ff0000f3bfe33c0fc73f03f003c0fc00
  | 0, 5 => 0xffff1cffffc00ffcefffff038cffc0e03ff3873ffc01c3ff0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x545c18800000032cb03c3702d700376f40085080014080000095
  | 0, 1 => 0x8920e415378f754ca35d4278b50082257fdf76aab21c22ac8708
  | 0, 2 => 0xf23f4a377fbf7cd34fc2ae8f9daba3e76ae8f9daba3c22ae0a95
  | 0, 3 => 0xf23f4a336dbf5cd34fc334d360cd14bc324d3b0fffffffff2242
  | 0, 4 => 0xffe9d2bff7262ffc890bff2242fbbfef7dbfdfff6ff7ffcafdbd
  | 0, 5 => 0xfffffffffff6afffffffffafdfffe8f4bff7af7ffdcbcbff2ad7
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 48 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 48 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 48 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 48 then wireAt i else 0
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
  | 4, 0 => 0xf2e6f993f293bda5f154aa00b50fb2d69f1691f08ca64a7f67b2d6ba5de0c3745bb8ff014ea891f34ccc715e47baa0703f1d60ab385234e737034d4935de20fe2e9d12192e300f8a290a174d27ca1d6a1d671d1e1d086b041b507caa1980d6eb1638e054077aa6ae0269168a
  | 5, 0 => 0xfd05eeb0f154aa00d798062ed6fb56cec812b73fc2948086b9e72f3eb2ee19b5b144d080ae7d80f9a90f92f288ca29be86d4643b843e49e1830c511d829d0e308241b4737f9c59f37c2ed0a07994985a6e6b48ca6d1cc4466bac6fc06b85db7469ad92116493ec5a6190dffe5ff000245bc4588f56c0623c54c5e111514fa0914f053df247baa07046425737459e5be1435ffda03d0687ed3ab3329d385234e73793056235e49768290a2e9c20b49e381814479f17c303b0171aa0eb15dbc31515521a2e130eb0aa0c275930095964b709309ea2038dd72800168dd5
  | 6, 0 => 0x7f9c59f3514fa0914642573735e49768290a2e9c20b49e3815dbc31515521a2e
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x30000000000000000c081020204080000300000800000000000c8102000000000010000040000300000c000023204040000200000c000000000088410100000800001210404c8101
  | 5, 0 => 0x4000000000080000100000400003000000000000000000000100000000001000000000030000040000200000400001000000000010000000000000000400002000004000000000040000200000c0000300000000002
  | 5, 1 => 0x4000010000088010200000c0000100000c00000000004000010000080000000000c00000000008000010000008d10000000800003
  | 6, 0 => 0x800000000004000000000040000100000400000
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

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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

def dom_6 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_6 : Nat := 0xf0e0f0e0f0e0f080
def roots_6 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f000, 4, 12)] (by decide +kernel) (by decide +kernel) low_1

def dom_7 : Nat := 0xf0f00000f0f0
def goal_7 : Nat := 0xf0e00000f080
def roots_7 : List Nat := [0xa0a00000a0a0, 0xc0c00000c0c0, 0xf0000000f000, 0xf0f000000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f000, 4, 12)] (by decide +kernel) (by decide +kernel) low_0

def dom_8 : Nat := 0xffff0000ffff
def goal_8 : Nat := 0xfaea0000f888
def roots_8 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0, 8, 12)] (by decide +kernel) (by decide +kernel) low_7

def dom_9 : Nat := 0xffffffff
def goal_9 : Nat := 0xfcecf888
def roots_9 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_9 : Lower dom_9 roots_9 goal_9 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0x5555555500000000
def goal_10 : Nat := 0x5444504000000000
def roots_10 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

namespace S_10
def pairsG : List (Nat × Nat) := [(34, 38), (34, 50), (36, 38), (36, 44), (40, 44), (42, 46), (42, 58), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [34, 34, 36, 36, 40, 42, 42, 48, 52, 52, 56, 56]
def r2sG : List Nat := [38, 50, 38, 44, 44, 46, 58, 50, 54, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_10.map (· &&& dom_10)
def goalM : Nat := goal_10 &&& dom_10
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_10 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_10 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_11 : Nat := 0x5555555555555555
def goal_11 : Nat := 0x5444504054445000
def roots_11 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555555500000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_10

def dom_12 : Nat := 0x3333333333333333
def goal_12 : Nat := 0x3222322230203000
def roots_12 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xf000f000f000f00
def goal_13 : Nat := 0xe000a000c000800
def roots_13 : List Nat := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 4 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10

def dom_14 : Nat := 0xff00ff00ff00ff00
def goal_14 : Nat := 0xfe00fa00fc00f800
def roots_14 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f000, 8, 12)] (by decide +kernel) (by decide +kernel) low_13

def dom_15 : Nat := 0xffff0000ffff0000
def goal_15 : Nat := 0xfeee0000fcec0000
def roots_15 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14

def dom_16 : Nat := 0xffffffff00000000
def goal_16 : Nat := 0xfeeefaea00000000
def roots_16 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def dom_17 : Nat := 0xffffffffffffffff
def goal_17 : Nat := 0xfeeefaeafcecf888
def roots_17 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_17
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (2, 18), (4, 12), (5, 7), (5, 13), (5, 21), (5, 37), (6, 7), (6, 14), (6, 22), (6, 38), (8, 12), (9, 11), (9, 13), (9, 41), (10, 11), (10, 14), (10, 26), (16, 18), (17, 19), (17, 21), (17, 49), (20, 21), (20, 22), (20, 28), (24, 26), (24, 28), (25, 27), (25, 29), (25, 57), (32, 33), (34, 35), (34, 38), (34, 50), (36, 37), (36, 38), (36, 44), (40, 41), (40, 44), (42, 43), (42, 46), (42, 58), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 2, 4, 5, 5, 5, 5, 6, 6, 6, 6, 8, 9, 9, 9, 10, 10, 10, 16, 17, 17, 17, 20, 20, 20, 24, 24, 25, 25, 25, 32, 34, 34, 34, 36, 36, 36, 40, 40, 42, 42, 42, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 33, 3, 18, 12, 7, 13, 21, 37, 7, 14, 22, 38, 12, 11, 13, 41, 11, 14, 26, 18, 19, 21, 49, 21, 22, 28, 26, 28, 27, 29, 57, 33, 35, 38, 50, 37, 38, 44, 41, 44, 43, 46, 58, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xfffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_17.map (· &&& dom_17)
def goalM : Nat := goal_17 &&& dom_17
def NN : Nat → Nat
  | 3 => 11
  | 4 => 53
  | 5 => 228
  | 6 => 471
  | 7 => 267
  | 8 => 18
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xfbb39bb2d6755a4aba719f71b2fe80cba8716da4a7bf35108e966db844614dc02ffdf2fa27383abe02200d7e
  | 4, 0 => 0xead9cd49e3a7c5e5ccab0e83ca56cbf7ca2f3cc9c8b4fdd3bd75b218bc82b3e1b1898289ac15681bab32bfdba76ccd1ba69a28269cd3fa838b2be70f8702ac4c7166856d70cc28bf6ff5f3896da6742368391bfd674fbf7f66a2e2ac62250d9160f83205602ecf3d5f79f85d5adfa99556c18ad54e4afb424657968545f24fb445e856f9410926143fb2da623b083576397cfa2c32e8bab0316d4cf82d4972ae29290f0c2719e33d2695a68d201ca0201cebba641c9c37271c3e0583172363c70fde8d050d58fb180d044eb306774c7b00c7b156
  | 5, 0 => 0x297a776228173bdd27a8a3f5277c205e2484ee8c2259f2bc21787c53206d0bcf203fef5c2019abe41f93080c1f426e131dec05861cd7515e1bf396ca1b7e2e5d1b289f481ae4d2881a761be71a7498901a66cec71a1f0ef61a10f6e519ea910e194f2d801910831518cd369118047ef117e9ca4616b67cf514e0136b1467f41e13350bca12fc993212f36941123a1e4911ff708311ab9d980f7b40a10d79cb890b6a7b1d0a6084d10a4696100a0dbee00a0bf171093fe48d0901497508ea0cab089ede53085a022307e998db06816de2062efed505d4b84a05ab788a052f839c04f1e25a034b623b02f4c1e301373cfc01204fab00ddfc6500c2176000904a51
  | 5, 1 => 0x5362a58853611af55287732c4f7c60744f5a105b4ae0bcd24adbba2b4a956005495b4db1492a59a148fa711d47ff4ff947f6b52f4585704044f7caa244c44b0944b733b343541d444350fce643091b4242979cd2429346054266a0bd412ae3684120e71540c5dc483fd0b9a93f9fefd43f4ef09c3f3f63773e8f6e5c3c1a39ca3baa073b3a84e7713a792f6a39cc6e7f39bf1eb538db6caf38b1459438a27cd737f8c67a37eaeb8b377083223761c3f33714fee63613cebe35dd329c34ae08e13417461633305b8632c3f5043246267f31ca9e2c300d062a2f8deb682f86aebc2f44012c2ed07be72d9e8b902d8d30732d2ec1b82d1eba6e2bcd5b7f2b000c4f
  | 5, 2 => 0xa35c9dd6a2a6e02ba09d9ac7a01d11f79f3586549dd8e2069b34369198a05a6c955532ce93fd79019385fd4291a361c78fc0f0418dfec2528c7eb4e58ba9ec848b0401ef8656db8585ac70918481bc9d82baab7681df9a4881c1d1c68188a01e813d68f87f1c9e7d7d2114097cf2005b7b9c99747a454d6578f1ec4677919af774fc2d4774863936743641ce72a4a4a572234e8471c119947096269d6e0920306dbb437b6d7f1f186d6a8de86a69951e6969bc1a66f5720065d479246524bde263ae5d66625a279161d7af80610a5cba5f14da325e2d8aab5d976ce45d499fea5bf6e8f75a99703159f9642e593840165796e9b057329b8f56fbf48f54f55e56
  | 5, 3 => 0xfac9ded5f3b9cc40eeec78f7e89f1d3be868c059e52d450ce42f8233e3cd2773e31855fde3055e51e15155b9e0456f93d9927432d8102e57d7562baccb318dbac9ae378fc962e58fc4a2db87c338dcabc311f58bbe8ee60bb93d8228b8f3a8e2b6b512f6b58ed639b22e8133b19d22c1b0feeee4afcd06d4af4ed27bacfe865eace90987ac7a279ea6db69e1a51c6199
  | 6, 0 => 0x1673385e163cc66615fc5b6615f4eac9155ed0bb1528c49c14b84f321474608f14696ac2140adaec13e0e2a713d6d81d13967e2f13346ed112f1a00e12ed399912c3605312468f8711d640d011be49131161181a115cdc521106ad5710bf6ca6103887e6102497a90fa65f9a0f97753d0f8899180f115ba20eed14a20ee2d2210ee0af2a0d6e8d170d2aded90cedf22c0cdc56be0cd412060c97cf590bee5d4b0bb8a2180a7677f50a6572fc09bdf0a009695d4008ba381d087a815b080a8eb707f1b6d60711d49e06b5fac60644c923063e9172060e91e705b8649705a9e53f0559c07103f8e99a0334643b02d6a72e0251096c015437cd007dbb7a006c2684
  | 6, 1 => 0x2d59ed9f2d52d1502be51bdf2baaf0272b8af0a62b5b865a2b1903882ad3509f2ac54d632a709ff12a611d332a16023a29e188d329af2b64293f76f02934275728d3f68428c2d85628732d7b2713cf002566dfcd24cbf971244f823f242f7cff23c08397239e1af5238cde42237fdc382325c90b228802542246c52021997fae217ce7742177d428213dff8120b6484d206bd013204a72201fac95641f7c1b131f4eac261f06a07c1ee07af31ec0fa371de45f961dbe4d991db4e0681d70c9b71d07cbc61c8d62a61c1250521b16f5ed1aa1953a18ac994f188affa9186366e3185955ec17aeb250176fbdf71734bd561701656116f36bf3168bc85d16741ef1
  | 6, 2 => 0x424acd374221143d41ec4f6f418c58194183d88741320659406a83da3f2e25783e79bb8a3e56ef7b3decda2b3dc0b3cd3da4f3293d727f8e3d2c7c353d0b3b903ce437ac3cc696da3cbcf7af3c0ce04f3b8aa58d3b1e56293b0f2c583acf9b4b3a4fc20639de473f39bb3ded39864930388012b137d8b58137a858a73790d5993748575a372b333936c16402366487033652dfea35a96a463597402035787e2635169f3a34f524f9349995fb343ac70234064f6c33d25e6233a2828e33722ba0333d305e32fa2f95315c08eb3156fc533117e4f430b4f53230631eec2f8141142f7e6ae62f2d39052ede35262e2eb6002dec4b6b2da94f942d8de92d2d6a9b2e
  | 6, 3 => 0x5da6006b5d8bf1475d71535d5d0eae245c499e5b5b6b6fdf5b3bed485b1f7a795aa5f59659c3015b59b9b5c25925466959100b8058a9df5058a4f987588ac935588269ee5875705b584300055808a35356488c3a563580cb55f9c36e55a4b4595548eb3e544f1037536a150753466db85257aedf5247743851ed228251e93bed5139dea75014114e4f9d1e774f57f3d24f135c524ecc8e064ea4fa1c4dc9c7c04d5001c34d2f3d364ba1260e4b81ba084b51d8934a55e6434a3f5f3c4978c0ae4910933d47bc7759476def3e4754508e46df279b46ba812f46a8c7ac4619497e44d46f7843e9290d43df582343bc23ab43b9e6c7434ac03242ef746f4291ffc9
  | 6, 4 => 0x7a05242f797abaaa7961f727791205e2789cb22c780e8f5777cfa6b177728e4a7723c8d0770e4b0576a582cf763744917636f3227616152c7613d46a7607603674cf39e4730cc97a72ff2f9d729c25ac7288949c727718da726a4e0171bb89217193d4b170eea42e703b0e086f6a8dfb6f4c3cf56d76e7956d65318d6d01b3cf6cd6ca796cc7f9b76c3bd30b6bd3e8686bba04806a95be0b6a54273769c0add469ac57256909bb4668716f4067c6dab467c43600672edba1671ea51e66d0a35666540d4c66357d3e6557fc26653364ff643988c9640f62e363a6a9d363a63bbf62dfa08f617c4550601c8a0d600ad1db6006ca9b5fa001255e96063b5e5ba43e
  | 6, 5 => 0x9c96855e9bca9a899bc930f99af9d28399d3056b997632ef997374ef994b9d0896edc457969aeb72968d4d5f967fbfcb9515305d94aba5ca947d9aae94028408934a18bd92d7911192beb26492002a6a906d80ec8efad5908eb3b3e78e2526e78e1286898dd9a8ed8dc082c58dacf6f48aa3b04f8a91658a8a0b34fc89acfcb1883687168826fc3987b2ceb48759f0be864f591485215bbd84129c4084090aae82c96d8a829ec1d6829abebd8220babb81e9f85c81b726b38123ee8880ff692c8069eaef805e03487fd8d7587f24c13b7f0d3e2d7e7a0a4c7e4b58517e22ace77dc594b27d2933597cf889057c64c2c77c039c0f7af4fa237aaf2d897a92749f
  | 6, 6 => 0xd1296545cef3ff30cd0facd0cc12eeb2caefe3b0c90a98fcc82107d4c7e2dc81c6d0b208c63e11c5c56e42c0c54de09cc5057f75c4209f4ec104a00bc0f16310c0e08b57c0d8bcdac0b02379c01a4c7abf98043bbf40b10bbf39cbf0be4769d9be20deedbc7e8f37bc75feb0bc545819ba1aa2e5b93206deb75da9c9b63ee375b4bad623b4a8fae1b49852fdb03615abae18ff3dad90c81dad58a5d0aaa81632a97a0c43a8afe02ea85da819a851a7e3a7853e24a6e30931a55beef2a4eb786ea4b188daa47edabfa43fb431a3e88400a3978b47a33952fca11662b6a070683ea05ab451a008f5839f9ea33e9f9e4cda9f9940d39e5f82759e0a09409d72dd14
  | 6, 7 => 0xf9cab482f8a016c6f0f8df95f0cb655ee6925698e57a471fe4d154f8e2f6af66e29d8d40e247b55ee0d0507fdf067d83de2eb4bfdc8a5345dc7b2823dbad392ddb7eec9cd9fb6b94d445852fd43813c6d35e22bdd26dffcbd1879d90
  | 7, 0 => 0x246554a623fe6fae23afce922310763b22d85c9a223682592219ec0a21a5f9682081cc612046aaad203cd04e20292edb1fd3d3851e739d441e1aa3ae1d989e101d89743f1d81c57f1ca0b1831c1ffead1b52f3321a0ece701979f41719169d33183e830517d07b0017a82026175a929b16b50ee91581f8c8141a4f1c1415063f1413d608135211a21317dd2b12b8884a11eb7ccf11d748061004221f0ff073950fc22fb60f8898390f5c5cfb0e8414b20df078900d9cbe430d4d98860cc7aa850cabde0a0b41c77209874f3d0878675807af559e075140fd06b07a0305c61dd605ad2f3405a3eb0a034762020291d00a0198251c0188fb4b00f5a3d200273479
  | 7, 1 => 0x4fb2394c4f9b055d4f943bc44f717d1d4e9d19034e2ce2974c1e35cd4c173de94b6e21e64b02825d499b08ca49148db048b0ac9d457c5ed1434ac0324309ffd8430588364215deda41d622d340bb2834405c8f3d4025ca0a3f49363a3ee6de3d3d6d0b963c9f3cdf3c9d75a23c8fe41f3c3d49423c21f90f3a476634396f572d395003403899ed1836e4026d36c744ae366fa27236224d1b359f67e7342cdee932ba82ac3264f194315024ba3122199e30ccd1eb30bda81a2edbd6b52ea0b9112cf3c0ef2cb7e2692b698d6c2b0f56702acd7a982a7c85282a5175e429e942c429c478db291abe5628a4a83e2727707326beaf6f26bb2fef258a6ea424cb7b29
  | 7, 2 => 0x7bc86ac17ac854af7ab2c9087aa157477a85129f7a5857927a2bf436791d9b4178493a7f76b015da7521769374d2ee7873f60c3a73a4532b72b28339721cd833709466926e38e6f66db8095f6d5cb0976be1bd3a6bcf90f36afac89269d0a4b069c0add46920920f68742b92673394256709aa6167044c4c66fb4c91668c477066357542651506a464e6ab0264e30e6464789948645092fc6401590261aa33686129ea295f5d13a95eebace45e90082e5d1e66bc5bff541c5b0171135aa8a6b959e9c31b596cee2e58a5f17758905d13568ff7f15640306856240dff557f4cd954b47b985314eaf652acbe7d523dc21151d2062b51bf3f2b51a4e00751099cc6
  | 7, 3 => 0xbef5700abc545819b7610a65b702d21ab37ef559b23cd636b0f51e5bb07bc511ae8d3699ada32de2ace974c5ab47af95aa38618da80d4bfda5e4c2a9a4a02823a494c22fa2f4f716a2d8fffaa16c4690a1662baf9e3c45669d42bc1d9c97dd089c48de239aec1f2b9a36658d997d45649882e2ec98553ede981b7e9297a5128c9710a458965f3458965531e695a996be94b8834e93f42b8d92b08ece928cbda5926d751e908ca4448f9d1d5f8f7fd14d8d5eaaf98c1a6ee88bedc1998b8fda438968a0cb88f823fd87cdddd0876b320386bb6894869b759485210b0383c5bc52838341f4833df903828511a4806266ad7f1797dc7d7d57bc7d33ff317d303bbe
  | 7, 4 => 0xf13569a4f11d8484f0c5c7cbe5b5122de54dbc12e088d44dd0e5095fcdd2d617cb2728e7c3334588c110cb7d
  | 8, 0 => 0xb6be7634a6563cc38a7994f87cea112d5fbac6fd5e22a7545cde0cce51bb2a0f4aee737934064f6c2eedfa851e7359ed1b78d4bc1729918f1561a43a1142fa410e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfafafafa00000000f0f0f0f000000000eeeeeeee00000000cccccccc000000007777777700000000555555550000000033333333000000000000ffff
  | 0, 1 => 0xf0f00000f0f00000cccc0000cccc0000aaaa0000aaaa000055550000ffff0000555500005555000033333333333300000f0f0000ffff00000000ffffffff
  | 0, 2 => 0xf0f0f0f0f0f0f0f050555550505555503033333030333330077007700770077005500ff005500ff003300ff003300ff0000ffff0000ffff0000ffff00000000
  | 0, 3 => 0x32323232323232323030303030303030222222222222222213131313131313131111555511115555111111115555555511111111333333331111111111111111
  | 0, 4 => 0x3c3c3c3c3c3c3c3c3333333333333333333333333030303033333333222222223333333300000000333330303333303033332222333322223333000033330000
  | 0, 5 => 0x5f5f5f5f5f5f5f5f5555555555555555555555555555000055555555000000005555000055550000505050505050505044444444444444443f3f3f3f3f3f3f3f
  | 0, 6 => 0xa0a0a0a0a0a0a0a099999999999999998f8f8f8f8f8f8f8f88888888888888888080808080808080777777777777777770707070707070706666666666666666
  | 0, 7 => 0xaaaaaaaaa0a00000aaaaaaaa88888888aaaaaaaa88880000aaaaaaaa00000000aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa0000aaaa0000aa88aa00aa88aa00
  | 0, 8 => 0xaaaaeeeeaaaaeeeeaaaabbbbaaaabbbbaaaaaaaaeeeeeeeeaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaa0a0a0a0
  | 0, 9 => 0xcc88cc00cc88cc00cc0ccc0ccc0ccc0cc8c8c8c8c8c8c8c8c0c0c0c0c0c0c0c0bbbbbbbbbbbbbbbbbabababababababaafafafaf0f0f0f0faaaafafaaaaafafa
  | 0, 10 => 0xcccccccc88888888cccccccc33333333cccccccc00000000ccccc0c0ccccc0c0ccccc0c0cccc0000cccc8888cccc8888cccc3333cccc3333cccc0000cccc0000
  | 0, 11 => 0xdddd5555dddd5555cfcfcfcfcfcfcfcfccccfcfcccccfcfcccccddddccccddddcccccccccccccccccccccccccccc8888cccccccccccc0000ccccccccc0c00000
  | 0, 12 => 0xeaeaeaeaeaeaeaeaeaeaeaeac0c0c0c0eaeaeaea00000000eaeac0c0eaeac0c0e0e0e0e0e0e0e0e0e0e0e0e0c0c0c0c0e0e0a0a0e0e0a0a0dddddddddddddddd
  | 0, 13 => 0xeeeeaaaacccc0000eeee8888eeee8888eeee0000eeee0000eeee0000cccc0000ececececececececececececa0a0a0a0ececa0a0ececa0a0ecec0000ecec0000
  | 0, 14 => 0xeeeeeeee88888888eeeeeeee00000000eeeee0e0eeeee0e0eeeee0e0eeee0000eeeecccceeeecccceeeeccccaaaa0000eeeeaaaaeeeeaaaaeeeeaaaaeeee0000
  | 0, 15 => 0xeeeeeeeeeeee0000eeeeeeeeececececeeeeeeeeececcccceeeeeeeeeaeaeaeaeeeeeeeee0e00000eeeeeeeecccccccceeeeeeeecccc8888eeeeeeeeaaaaaaaa
  | 1, 0 => 0xf0f0a0a0f0f00000f0f00000f0f00000f0c0f0c0f000f000f0c0f000f0c0f000f0a0f000f0a0f000f080f080f080f080eeeeeeeeeeeeeeeeeeeeeeeeeeeecccc
  | 1, 1 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f080808080f0f0f0f000000000f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0
  | 1, 2 => 0xfafaaaaafafaaaaafafaaaaaf0f00000faeafaeafaaafaaaf8f8f8f8f8f8f8f8f8f8f8f888888888f8f88888f8f88888f3f3f3f3f3f3f3f3f3f3f3f300000000
  | 1, 3 => 0xfafafafaf8f8f8f8fafafafaf0f0f0f0fafafafaaaaaaaaafafafafa88888888fafafafa00000000fafaf0f0aaaa0000fafaeaeafafaeaeafafac8c8fafac8c8
  | 1, 4 => 0xfcfca8a8fcfc0000fcfc8888fcfc8888fcfc0000fcfc0000fcecfcecfcccfcccfca8fca8fc00fc00fca8fc00fca8fc00fafafafafafafafafafafafafafaaaaa
  | 1, 5 => 0xfcfcfcfca8a8a8a8fcfcf8f8fcfcf8f8fcfcf8f8fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0cccc0000fcfcececfcfcececfcfcccccfcfcccccfcfca8a8fcfca8a8
  | 1, 6 => 0xfefef0f0eeee0000fefeeeeefefeeeeefefeeeeef0f00000fefeaaaafcfc0000fefe0000fefe0000fcfcfcfcfcfcfcfcfcfcfcfcfcfc0000fcfcfcfccccccccc
  | 1, 7 => 0xff0fff0f00000000ff00ff00ff00ff00fefefefefefefefefefefefefcfcfcfcfefefefe00000000fefefafafefefafafefefafa00000000fefef0f0fcfcf0f0
  | 1, 8 => 0xffaaff00ffaaff00ffaaff00f0a0f000ffaaf0a0ff00f000ff88ff88ff88ff88ff88f080ff88f080ff880000ff880000ff80ff80ff80ff80ff0fff0fff0fff0f
  | 1, 9 => 0xffccff0000000000ffcc0000ff000000ffaaffaaffaaff00ffaaffaaffa0ff00ffaaffaaff88ff88ffaaffaaff00ff00ffaaffa0ffaaff00ffaaff88ffaaff88
  | 1, 10 => 0xffeeff00ffeeff00ffeeff00ffccff00ffccffccffccff00ffccffccff88ff88ffccffccff00ff00ffccff88ffccff88ffccff88ffccff00ffccff00ffccff00
  | 1, 11 => 0xffff0000eeee0000ffff0000aaaa0000ffff000088880000ffff00000000ffffffff000000000000ffeeffeeffccff00ffeeffeeff88ff88ffeeffeeff00ff00
  | 1, 12 => 0xffffaaaa00000000ffff8888ffff8888ffff888888888888ffff5555ffff5555ffff3333ffff3333ffff1111ffff1111ffff0f0fffff0f0fffff0000ffff0000
  | 1, 13 => 0xffffcccc00000000ffffc0c0ffffc0c0ffffc0c0c0c0c0c0ffffaaaaffffaaaaffffaaaaffff8888ffffaaaaffff0000ffffaaaaf0f0a0a0ffffaaaacccc8888
  | 1, 14 => 0xffffeeeeffffeeeeffffeeeeffffccccffffeeeeeeeeeeeeffffeeee00000000ffffccccffffccccffffccccf0f0c0c0ffffccccccccccccffffccccaaaa8888
  | 1, 15 => 0xffffffff33333333ffffffff11111111ffffffff0f0f0f0fffffffff00000000fffff0f0fffff0f0fffff0f0ffff8080fffff0f0ffff0000fffff080fffff080
  | 2, 0 => 0xffffffffc0c0c0c0ffffffffaaaaaaaaffffffffaaaa0000ffffffffa0a0a0a0ffffffff88888888ffffffff80808080ffffffff55555555ffffffff55550000
  | 2, 1 => 0xfffffffff0a0f000ffffffffeeeeeeeeffffffffeeeeaaaaffffffffccccccccffffffffcccc8888ffffffffcccc0000ffffffffcc88cc00ffffffffcc0ccc0c
  | 2, 2 => 0xffffffffffffccccffffffffffffaaaaffffffffffff0000fffffffff0f0f0f0fffffffff0f00000fffffffff0c0f000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x742f91e7f472af91e7f4782f91e6f45f250ec6e45f23cf652462250ec6d4742f91e7245f23cee6e469a3cda3e47626d065b46c23cda3e4
  | 4, 0, 0 => 0x7631d1e762dab5d1e763896d57c8f3b9b486b0b762f91e7357e3ed7c9240ab8136832d90d5f8cd479c4b6ae05f23cfe3e55f23cec6d292c19c0be591995c0d9479e886afb5f238f44357e2f91e80292c31c0b24290d622ec5f23cfab135f2e0f4435
  | 4, 0, 1 => 0x7e3211e712dac497cb72d90d5c0be50a30f4b0c702f93e785862f91e7421abf1d0be479cd5f8e04a20902b0c69a951e4356daf91e7f1a2bf1d8be5919160cf35f23cdeb035f23d026e56c23cec6d1a2bd17c8f368d15f2be47a047cb0c762f91e725
  | 4, 0, 2 => 0x5f23cec6e1a2b111e76368d15c0be479e486ae05f25102775742f91e551caaf91e76280e9626e55f23d02b0c762f91e7f5703691e7a21ac31b08f3690d5f8be5323d02abe479d8a43957e31d1e81292b818894409d957c943b1b468af05f23ca03c5
  | 4, 0, 3 => 0x1035f251026d589af91e7a38ac4dd0be47a055c0d847a047cb135f278e25b5
  | 5, 0, 0 => 0x702f91e7a2b90da26be479e8d84367a3817c8f408d19f8be47a1902526702f9388f2d90da22e05f23cfa43679af9368f2810d9f8ea6823cb64367e2f94e8f2d90d9f8be47a04dc34683381808f2d8f1a26db5f284b6376762f9368f2d8e59f8e06523ce25b670311368f2d90da06be47a04da346
  | 5, 0, 1 => 0x863817c8f3b90da14e05f284b63767e2f9528f2910d9f8be479cca44367e3b17c8f3916d9c0d847a04f443688ba97c8f2d90d9f8f86223cb6436862f91e6d2a90da18fc762f91e73684381808f2d90da2afc5f23ce25b67e3b17c8f4016d9c0d847a04ec3467e3b17c8f399499fce05f23d02346
  | 5, 0, 2 => 0x863818e8f2a90d9f8ea5f2b4b64367034d1e5b218f99f8ea5f2b0b64366c23cec6d2d90d9c0be591d8984367f2f91e6d2d90d9f8be47a24e25b6762f91e763696d9e8be479b4b64367e3e5a08f2d90da24be4716ca04367e3817cb83d10d9f8f964a3cb64367e2f91e8e3896d9c0be50a30b63c6
  | 5, 0, 3 => 0x7e3b17cae2d8e5a06f95f23cb64366daf91e7f2d90da0cec702f91e7a6702f91e8c2d8f99c0be4da3ce25b67e2f94a8f408d19f8e05f2f4c6346703511e5b218f19f8ea6023cb64367e3e5888f2d90da26db5f23d02346702f928762d90d9c0be5ca3ce25b684b818e8f2d90d9f8e85f23cb6396
  | 5, 0, 4 => 0x863811e852d90da20e06823cb64367fb817c8f3d10d9c0c7479d8b64367e3294a8f2d90da18fc732f91e8167e3817ca13496da26ed5f23cb64367e34d4a8f2d90da06be47a04da436702f96a8f2d90d9f8ea5f23ce25b67e2f91e702d90d9f8e051a3cb643689b6d7c942d90d9f8e05f2f0c4436
  | 5, 0, 5 => 0x7e399c0be4a2059f8fb62218b64365f23d0276368d1a22ec5f23cb63f67e3b1a48f2d8e59c0be479e8b24367e2f91e742d90d9f8f05f23ca04367e2f91e81368f99f8ec5f2c91e7367e381448f2d90d9f8f75f23cda346863817c9d47a059f8e15f23ce25b6702f928813b0d19f8e05f284d45b6
  | 5, 0, 6 => 0x5f23cf4763690d9f8e062a3cb6436833817c8f3316da06fb5f218b643689c497c8f3896da1ee063a3cb6436003817c8f2b10d5f8f95f23ce25b689af93c5b2810d9f8f36423ca04367e3b1808f2d8e59c0be479d8b63a6702f91e76368d1a02f95f23cb64367e3b18ea14796da18fc75af91e816
  | 5, 0, 7 => 0x86381b08f4090da26fc5f23d025267e381b08f408d19f8e05f23d023665f2cd1e762d90d9c0be591949843688b81988f2d90d9c0be47a04aa3e67e3ed7c922d90d800be479d8da34589c317c8f2a10d9f8e069a551e5b681b81808f2d90d800fc732f92881589b6d9a8f2d90d9f8be5a23cb6436
  | 5, 0, 8 => 0x7e3611e6d2d90d9f8e069a84b6376003f1c0be2189d5f8e06023ce25b689af91e6f2d90d800fc702f91e3657e3997cb247a059f2be4796c863e6702f91e762910da26be479e8a0436702f91e59218f99f8e647a08b64367e2f9308f2810d9f8be47a04da526863b17c8f2a8e59f8e06323cb6436
  | 5, 0, 9 => 0x7e2f91e802810d9f8be4f1b4b64367e2f91e813716d9e6be479d8a04367e3817c9247a059f8e0622511e8167e3811e82408d1a14ea5f23cb6436703111e762d90d9f8ec63a3d025b67e3b17c8f3216da24ec5f238b643681be97c8f2d90d9c0d0479d8b6436863ed7c862a90d9f8f65f23cd8436
  | 5, 0, 10 => 0x3f17c8f2890d606be52a3cb6436703111e813b0d1a24e05f2acb64367e38194a44790d9c0c0479d8b6436893817c8a408d19f8f35f2c91e7167e2f91e713716d9f8ec5f23cfe5b67e38128822d90d9f6be431d8b643689b6d888f2d90da06e05f2511e816703551e5b218f1a270c762f91e816
  | 5, 0, 11 => 0x3f1c0be478c1624e063a28b64367e38d8e8f2d90d9c0be5da3d023467e38142832d90d80103732f91e815833817cb2260f19c0be47a04ae3c67e2f91e6d2690da06e6702f91e81689bb17c9e2d90d9f8e06b23cf443689b6d808f2d90d9f8be479e8da4367e2f9646d2610d9f8e0652c898436
  | 5, 0, 12 => 0x7e2f91e713816d9f8e5702f91e816003f1c0c44a2055f8e068278b643685b817c8f4090d97c9b479b4b64367e381868f2d90d97c8f3b1b48634689ba57c8f2d90d9f8ea68a3cb6436702f91e772d90da26ec5f23cf4436893817c9a2d90da22ec5f23d025b67f3897c8f2d90d9f8e05f23cfe346
  | 5, 0, 13 => 0x7e3ed7c863d10da16ec5f23cb63967e3cd948f2810d9f8e8702f91e8167e381808f408d1a24f35f228a04367e3817c9e3896da22e069a3cb6436833817c8f3796d9f8ec5f2c89839689381a08a2d90d800dc5f23cb643589b957c8f2d90d9f8be4796ca04267e3cd7c9e2810d9f8f95f23d02346
  | 5, 0, 14 => 0x7e3817c8f3d1c5a0cf35f23ca03c689ba17c8f2d90da06be479b4b6436
  | 6, 0, 0 => 0x7e3817c8f2e16c86ef3702f91e762d90ddf8be47a28da5b21bb817c8f3b16ca0437003f1c0be479c44ccfc743817c8f2d90dc0103702f91e8121b3f1ccbe50a3cb64377e381808f2d90c68efc702f91e5b21855df8ec5f23d0c812dbb817c8f3b18cb6437003f1805b2185c22c00893817c8e2d90d9c0be4da3cb6431cbbf1f6be4316c86347
  | 6, 0, 1 => 0x3f1c0be47a047cc007e3817cb2218a19c0be47a38b6431e3b817c8f409e8ec43789af91e5b2810c78efc702f91e712d8b9dc0be479d8b64308bc4e24ec5f23cb64377e3818e8f2d93c86e00702f91e811a021a14e05f23d025b21bc31f8e05f23ce64377e3817c8f4016c86efc703411e5b218dddf8e05f23cb64521bbf17c8f2d940863a7
  | 6, 0, 2 => 0x833817c8f4616c78efc7031d1e832d90ddf8e65f23d0c5b21bc19f8be52a3cb6437003817c8f409d868cfc702f91e722d90ddf8e06223d045b21bbf1eebe479b4b64377e2f91e682d90c6ef13702f91e5b218f9df8ec5f2a51e5b21bbf1c0be4ea3d025b77e3817cb24696c86e007e3997c8f2d8b99f8ec5f23ce65b21b801c0be4796c86056
  | 6, 0, 3 => 0x2f91e762d90c22cfc76381888f2d90ddf8e05f23cb6430b3bf1ccbe4796c861777e3817ca12d8dc4cefc702f9648f3896ddf8e05f24d1e5b21bc35f8e05f23ce25b77e3cd7c8f2810c6eefc763817cae2d90de06fc702f91e811a3af91e813b1b4b6437003817c762d90c2ec00702f9644c21821800fc7030086260bb3f17c8f2d94086417
  | 6, 0, 4 => 0x7e3817ca147a0468efc773817cb22d90dc00fc5f23cb6430633f1c0be5423cb64377e3edc0c44796c86ee05f23cec6d2d90de18fc5f2951e5b21bbf1f6e05f16c861e77e381b6be5096c6ef136daf91e5b2c90ddf8e05f2e91e712db801f8e05f278b62e6003817c942d90c10c007e2f91e5b21825a18e05f23caa43173bf1c0c747a28b6437
  | 6, 0, 5 => 0x89bf17c8f2d95086e0089b6d7c5b2185d9f8e05f23cb6430d3bf1c0be4d23cb643781bf1c0be4a16c86efc732f9288f2d90ddf8e069b391e5b21bbf1c0be479e8d84377e3e57c8f2d90c72efc7336d7c8f2d90de18e05f2c91e5521bc0dd8e05f23cb6437863f1c0be47a047cefc702f91e5b2510ddf8e06833d1e5b21bbf1c0be4796c860a7
  | 6, 0, 6 => 0x7e3817ca12d8dc10efc5f23d0c5b2910dc010c702f91e7821b001c0be479d88626600401c0be4796c5ccfc7639d7c8f2d8e5df8ec703491e5b21bbf1c0be4f16c86267003f1c0be4790c32c0088bb17c8f2d90d9f8e05f23cb64721b801f8e04796c8612681bedc0be4796c86e005f23cec6d2d90d9f8e05f2c8b64307bbf1c0be58a3cb6437
  | 6, 0, 7 => 0x7e38194a14796c86efc702f91e811a05ddf8e06c23d025b21bbf1f2be4796ca64377e3817c8f38984b6e007031d1e5b21821a18e05f23d1a5521bbf1c0d350a3cb64377e3917c8f2d94086e0089b817c9e2d90d9f8ec703011e5b21bbf1c0be4796c90437003f1c08f2d90c28c005f16c861708821800e05f23cb64301b3f1c0be47a1902347
  | 6, 0, 8 => 0x429c0be2d90c2ec007e3817c942d8b9a24fc703411e5b21b80204e05f23cb64367e3817c8f3896c6ee00833817c8f3d10d9f8e05f23cba5b21bbf1ccbe4796c860877e3b17c8f2d95472e007e3817cb2260b99f8be47a04da5b1a3bf17ca1479b4b64377e3817ca14096c6eee05f23cec5b218b9c00fc702f8b64318b001f8e047a10b6436
  | 6, 0, 9 => 0x7e3817cb2479cc86e007e2f94a8f21899800fc703291e5b1733f1c0db5f23d023477e38d7c8f4316c86e007e381968f2d90d80112702f9145b173001fee05f23c86236003817c904790c4cc0089b6d7c8f218999f8e65f23d025b21b801f8e069a3cb62e67e3817c8f4096c86e0081b81888f2d90d9c0be479d8b6431a3bf1c0be47a18f4437
  | 6, 0, 10 => 0x833817ca14796c78efc702f91e5b21895df8e05f279025b21bbf1c0be4796c8624789b6d7c8f2d90c5cefc7034d1e5b2185dc010c7034d1e5b21b431c0be4795486377003817c431305c10c007e3811e5b2184da26db5f23d1c5b21bbf1c0ca47a18b6437893f1d8be4796c72efc702f9644c218f1df8e05f2511e811a3bf1c0be479e886177
  | 6, 0, 11 => 0x7e3cdd8be47a04b6f037e3817c8f4090ddf8e05f2c8ce5b21bc31d8e05f23caa43789b6d7c8f2d90c68ee05f23cec5b2610ddf8e05f23cb643113bf1c0c04796c863977e2f91e6d2d90c2eefc7daf90c5b2a90ddf8e063a851e5b21bbf17ca54796c862e77e381948f2d90c2eefc702f9608f4090dc00be4790c4c11043449f8f35f23ca0437
  | 6, 0, 12 => 0x833817c8f4316c78f0c702f91e8e2d90de270c5f23cb65021b801f8e063a3cb62e67e3817c8f408d010e00853817c8f218999f8ed702f91e5b21bbf1c0be479c4b61b7833f1c0be5096c6ee0089b817c8f3d10da26db5f2c91e5b21bbf1c0ca4796c862677e2f94a8f2d90c68e007e3997c8f2d90d9f8e06daf9285b21bc49c0be4516c86267
  | 6, 0, 13 => 0x7e3817c8f2d90c3ef137e3b17c8f4096ddf8e05f2c89843043801f8eb5f23cb643689b6d7c8f2d93086f01702f91e5b2a90de18e05f23d027621bbf1c0be47a04ec347853817c8f2d90c5cf06702f91e5b1e05de18fc702f9425b1bbc19f8e65f23cb64377e3817caa4796c86e00863817c8f2b90d9f8f3702f9425b1bbbf1c0be47a0486047
  | 6, 0, 14 => 0x7e3817c944096c86e0080b817c8f2d8b19f8e05f278b65021bc4df8e05f284b6377003f1c0be170982ecfc702f91e813d10ddf8e05f284c65b21bc29c0be5923cb64377eb817c8f2d90c78efc7031d1e5b21899df8e05f250b643043c19c0be4796c782677e3817caf4796c86efc762f91e8a2d8e5dc0be479d8b6431bbbf1c0c447a28b6437
  | 6, 0, 15 => 0x833f1c0be4799cb6efc702f91e812690dc00fc732f8b6430bb3edc0be479d8b64377e381948f4096c86e006daf91e5b21801800fc732f91e811a3449c0be45204b6437833817c8f2d95c78efc7034d1e812d90de24fc702f91e712db801f8be478b84c1167e3cdc0be4f16c86eec702f91e762d90dc00fc7023d045b21b3f1e6be479c4b6437
  | 6, 1, 0 => 0x89bf17c8f3896c86efc752f91e862d90de14e05f23cb6431ebc0dc0be47a2cb6437003f1c0be4796886cfc702f91e81318d1df8e05f284d65b1bbc4df6be4796c863c7833f1c0be47a0468e007e3811e852d90da18fc702f91e5421b801c0d04796c8608688bf1d8be4796c86ee05f2f51e762d90ddf8e05f278b64308bc31f8eb5f23cb6437
  | 6, 1, 1 => 0x702f91e5b2a90c7cefc702f91e642d90ddf8e05f23cb64621bc19c0be47a04b63c7003cd7c8f2810c10cfe702f91e5b21861df8ea5f23cb6430bbbf1c0be479acb6437863f1c0be47a0468efc702f91e812b90dc00fc5f278b64308b001f8e65f250b64367e3818e8f2d90c10e00762f91e5b1c821800fc702f922430f3001c0c44796c86086
  | 6, 1, 2 => 0x3f1c0be408d02ece05f23cec5b21861dc0be47a30b6431e3bf1c0d050a3cb64377e3cdc0be479e886e007e3817c8f408c9a18fc702f9644c21bbf1c0be479e8a0437853817c8f2d90c6ee007e3997c8f21899a06fc703111e5b21bc19f8e05f250b643783bf1c0be5913086ee05f23cec5b218e5df8e05f23cb64421bc45c0be4796cb0437
  | 6, 1, 3 => 0x7e3b1c0be4796c3aee05f2ed1e812d90ddf8e0622851e5b21b801f8e05f278862667e3cdc0ca4796c86efc702f91e7a21845df8e06523cb65021bc49e6e05f228b64377e3817ca12d90c3ce007e3e57c8f2d8b9a24e05f228b65021bc31f8e05f250b64377e3817c8f3796c86efc79b81a68f2d90de26fc702f91e811a3801f6be4316c86086
  | 6, 1, 4 => 0x3f17cb22610c22c007e3819a8f2d90d9f8e65f2c91e5b21b801f8e05f25102346003f1c0be3d10c2ecfc702f91e7f2d90ddf8f35f2851e5021bbf1c0ca4796c86117702f9368f4096c86f057e3b17c8f2d90de24e05f228b64308b801f8e05f16c92436003f1c0d04796c5cc00703011e5b21821800e05f23cb64303b00218e05f23cb2436
  | 6, 1, 5 => 0x3f1c0d44796c86d0679b817c8f2d8f1c00fc79af91e50173419c0be4796ca03c700445c0be4796c5cc007e381945b2185d800fc703051e5b21b3f1f2be4796c86267003f1c0c44796c5cd137e3817c942d90dc00fc7034cb6430bb3f1c0be4796c86217003f17c8f3d10c22cfc793817c8f2d90ddf8e0623091e5b21bc55f8be4796ca0437
  | 6, 1, 6 => 0x88b817c8f2d90c4cefc7023d045b218d1df8e06db111e5b21b801f8fb5f218b62e6833f1c0d44796c86f11702f91e5b218f1e18fc763817c8f40bbf1c0be479a4b643781b817c8f4316c86f00702f91e5b218b9c00fc702f91e5f2db419c0be4796c78117873f1c0be47a0468f0c7e3818e8f2d90ddf8ec5f23cb6390bbbf1c0c44796c86177
  | 6, 1, 7 => 0x7e3e57c8f4096c86f0e7e2f91e6d2d90de26fc703351e5b21bbf1c0be50a3ce25b789c31d8be4796c86efc702f91e7e2d90dc00fc5f23cda431333817c9b4796ca0437003f1c0c04796c5cc00702f91e5b1e0099f8e05f23d025221b801f8be4796c720b67e37d7c8f4096c86e00833817c5b1e05d80106702f91e5b1f33f1c0c44a23cb6437
  | 6, 1, 8 => 0x863817ca14795486efc752f91e5b2810ddf8e05f23cea5b21bbf1c0c04796c862677e3b17c8f2d8e410efc703111e5b21821df8e05f2651e5b21bbf1c0be5b23cb643783381bcbe4796c78efc5f23cda5b218b9dc0be4da3cb64308bbf1e2e05f23d024377e381808f2d90c78efc703411e5b218e1e24e05f228b643173801f8e05f16c86356
  | 6, 1, 9 => 0x7e3817ca12d9546eefc763817c8f3396ddf8e05f2811e5b21bbf1c0be4796c861b700431c0be479545cd0c702f91e8c2d90dc00fc702f91e4b0eb3f1d8e05f278b6437002f9368f2d90c22cfc762f91e812d8e5df8be5923cda5b21bbf1c0c447a04b6437003f17c431305c22cfc7036d808f2d90ddc0be4799cca5b21bbf1c0be479f0b6437
  | 6, 1, 10 => 0x7e3817c8f2d90c38efc702f97a8f408d1dc0be4da3cb64317380206e65f23cb6436833f1d8be4796c72f0c7e381a08f2d90de0cfc703111e5b21bbf1f6e05f23d023477e3817c8f2d90c5aee05f23d02762d8d1df8e06023d025b21bbf1c0be4796c86187003817c9b4790c4ccfc773817cb22610ddf8e06023cb643043c0dcce05f23cb6437
  | 6, 1, 11 => 0x3f1c0c42d90c2ec007e381888f408d19f8f0702f91e5b21bbf1f6e069a3cb6437863f1e6be4794086f12763817c8a2d90ddf8e9702f91e5b21bbf1c0c05fa3cb643781b81babe4796c86efc752f91e872d90dc00fc7caf8b6430bb001f8ea5f23c862667e3b17c8f2d94872efc763817c8f3d10de18fc5f23d026d21bbf1c0d34796c86377
  | 6, 1, 12 => 0x3f1c0be478d030ce06c23d02762d90ddfce05f23d025b21bbf1cae05f23cb64377e381a08f4216c86efc703011e5b2710dc01035f23cb64308b3f1c0d34796c863977e3817c964796c86e007e38188942d90da26db5f23cb6430bbbf1c0be47a04681877e3a97cb24796c86f067e381808f2d90de26fc703111e5b21b801f8ec5f16c72176
  | 6, 1, 13 => 0xfc702f97a632d90de26db5f23d025b21b801fce05f23cb64367e3d5c0be4796c86f137e381808f2d90ddf8f95f23cb6431a3bf1c0be50a30b6437
  | 7, 0, 0 => 0x1c0be2d90c2e086003f1c0be47a288626700001f8be52a3cb64367e3817c8f4096c863c87e3817c8f2d90c4c0880000226db5f23cb64367e3817c8f4096c86178003f1c0be47a04b6347003817c8f2d90c220877e3817c8f3396c98438003f1c0be4796c860477e3817c8f43204b64387e3817c8f2d90c2e08800431c0be4796c86087003f1c0be479e0b6437003cdc0be4796c86087
  | 7, 0, 1 => 0x415f8e05f23cb64377e3817c8f2d9548637800405f8e05f23cb64377e3cdc0be50a3cb64387e3817ca14796ca04387e3817c8f4516c862e8003f1c0be479e8b6437003f1c0be4796c860e77e381b6be47a04b6438000017c8f2d90c220867e3b1cee05f23cb6438003f1c0be5916c984370044dc0be4796c86087003f1c0be4796c862a7833f1c0be50a3cb64387e3817c8f4096c86268
  | 7, 0, 2 => 0x4320ce05f23cb643700431f8e05f23cb62e7003f1c0be47978b6437003f1e6e05f23cb62e7003f1c0be4796ca02e77e3b1c0be4796caa438833f1c0be47a18b64380000214e05f23cb64367e3817ca14796c861187e3817c8f4516c8634889bf1c0be4796c86418003f1c0be4796c9a43700419f8e05f23cb62e7003f1c0be4796c86017863f1c0be50a3cb6438003f1c8e05f23cb6437
  | 7, 0, 3 => 0x863f1c0be4796c861787e3817c8f2d940863c8833f1c0be4796c86268893f1d8e05f23cb6438003f1c0be4796cae4377e3817c8f2d94086178003f17ca14796c86117003f1c0be4796c5c11789bf1c0be50a3cb6438863f1c0be47a18b64387e3817c8f4096c8608800001c0be4790c4c086003f1d8be4796c863977e3edc0be4796caa438823f1c0be4796c86378833f1c0be4796c86178
  | 7, 0, 4 => 0x3f17c8f2d90c220e7003817c8f2d90c68087003f1c0be4316c86177833f1c0be4796cae438003f1d8e05f23d025b7863f1c0be4796c862687e3817c8f2d90c781180044df8e05f23cb62e7003f1c0be4796c862f77e3cdc0be4796c8626800001f8e05f16c5c1767e3817c8f409d8b6438003817c8f2d90c5c087003f1c0be4796c863b7003f1c0be4790c4c2077e3cdc0be4796c863c8
  | 7, 0, 5 => 0x7e3817ca14796c862e8003f1c0db5f16c8617789bf1c0be4796c86268003f1c0be2f16c86177003f1c0be47a20b643781bf1c0be4796c86348003f1c0be2d90c4c177003f17c8f2d90c78117003f1c0be50a3c86267003f17c8f2d90c2e117003f1c0be2d90c78177003f1c0be4796c863e789bf1c0be4796c861780044e18e05f23cb64377e3817c8f2d954863987e3817c8f2d90c4c118
  | 7, 0, 6 => 0x3f1c0be4790c4c1777e3817c8f2d90c220887e3817c8f2d90c5c2a87e3cddee05f23cb6438003f1c0be4790c4c237863f1c0be4796c863e87e3817ca14796c86348003f1c0be47a18862677e3817c8f4098cb6438003f17c8f2d90c2210700001f8e05f284b63767e3cdc0be4796c86088833f1c0be47a04b643800001f8e05f23c5c266003817c8f2d93086087003f1cce05f23cb6437
  | 7, 0, 7 => 0x7e3817c8f2d90c5c2687e3817c8f2d90c5c2b87e3817c8f2d90c6817889bf1c0be47a04b64380041df8e05f23cb6437003f1c0be4096c86177003f1c0be4798cb6437003f1c0db5f23c8626700001f8e05f278b6436003817c8f2d90c6e0877e3817c8f2d90c5c178003f1c0be2d90c2e087003f1c0be4796c682e77e3817c8f4316c862e800001f8e65f23cb6436863f1c0be47a04b6438
  | 7, 0, 8 => 0x7e3817c944796c86348003f1e2e05f23cb64377e381b6be4796c86348833f1e6e05f23cb643800451f8e05f23cb6437003f1c0be4796c982e7003edc0be4796c8608700429f8e05f23cb6437003f1c0be47980b62e7003f1c0be4796cb24377e381b6be4796c862e8003f1c0be4796c5c297003f17c8f2d90c220d7003b1c0be4796c860877e3817c8f4516c86398003f17c8f4096c86117
  | 7, 0, 9 => 0x7e381b6be4796c9843800419f8e05f16c8617700001f8e05f23cf4436863f1c0be4796c86118003f1c0be4796c863377e3b1c0be50a3cb6438873f1c0be47a04b6438003f1c0be47a04862677e3817c8f2d90c5c2c8863f1e6e05f23cb64387e3817c8f2d930863c8863f1c0be4796ca0438003f17c8f409b4b64377e3817c8f2d90c4c1d87e381b6be5923cb643800001f8e05f23d02346
  | 7, 0, 10 => 0x7e3817cb247a04b64387e3817c8f4096c86348003f1d8e05f23cb62e7003f1e6be4796c8611700431f8e05f16c8617700001f8be479b4b643600001f8e06523cb64360000224e05f228b6436003f1c0be479acb64377e3817c8f2d90c6808800001f8e069a3cb643600001f8e05f250b6436003f1e6be4796ca0437003f1c0be4796c86027003f1c0be4796c6e2e7003817c8f2d90c72087
  | 7, 0, 11 => 0x7e3817c8f4096c984387e3edc0be4796c863c87e3b1c0be4796c86268003fdf8e05f23c86267000020ce05f23cb63c6003f1d8be47a18b6437003f1c0be47a24b64377e3817ca14796c863980044df8e05f16c861777e3817c8f2d93086088003f1c0be47a38b64370044df8be4796ca04377e3817c8f2d90c6e26800449c0be4796c8608700439f8e05f23cb6437003f1f6e05f23cb62e7
  | 7, 0, 12 => 0x7e3817c8f2d90c72178003f1c0be4796c864077e3cdc0be47a24b64387e3817c8f2d90c6e088003f1c0be4ea3cb6437003f1c0be4796caa2e7833f1c0be4796c863487e3817c8f2d940862e8003f1c0be4790c4c117003f1c0be4796c861d7003f1c0be4796c722e7003f1c0be4796c964377e3edc0be4796c86268003f1ccbe4796c863477e3817ca14796caa438003f1c0be4794086267
  | 7, 0, 13 => 0x3f1c0be2d90c6817783bf1c0be4796c98438003f1c2e05f23cb64377e3b1c0be47a20b6438003f1c0be4796c86327003f17c8f2d90c5c117833f1c0be4796c984387e3edc0be4796c860887e3817cb24796c8611889bf1c0be47a38b643800449f8e05f23cb62e77e3817c8f2d90c7226800001f8be4790c4c1167e3817cb24796ca0438863f1c0be4796c86348003f1c6e05f23c86267
  | 7, 0, 14 => 0x3f1c0be4790c5c2677e3817c8f2d90c720880044e24e05f23cb6437003f1f2e05f23cb6437003f1c0be4a16c86347003f1c0be4796c860f7003817c8f2d90c10067893f1c0be4796c86268003f17cb24796c86117003f1c0be4790c4c1e77e3817cbd47a04b6438863f1c0be4796c98438003f1dce05f23cb643789bf1c0be4796c863487e3cdc0be4796c984387e3edc0be47a04b6438
  | 7, 0, 15 => 0x833f1c0be4796c86398003f1c0be4796c8618700001f8ec5f23cb639600001f8e06223cb64367e3817cb24796c862e8003f1c0be4796c86007863f1d8e05f23cb6438003f1c2e05f16c86177833f1f6e05f23cb64387e3817c8f4096c86188003f1c0be5923c8626700001f8f95f23cb6436863f1c0be4796c863787e3817c8f4096c8639889bf1c0be4796c98438003f1c0be2d93086177
  | 7, 1, 0 => 0x3f1c0c44796c863477e381b6be4796c861787e3817c8f4516c861187e3817c8f4316c863c800001f8e06016c861767e3edc0be4796c86348003f1c0be2d90c72177003f1c0be48a3c8626700001f8e06023cb6436003f1c0be4ba3cb6437003817c8f4316c86087
  | 8, 0, 0 => 0x7e3817c8f2d93086efc702f91e5b218d1c00fc5f23cb64308b44df8e05f23cb6437003f1c0be2d90c2ed0c7e3817c8f2d90de0cfc702f91e5b21bbf1c0be47a04b64377e3817c8f2d90c10efc7036d7c8f2d90ddf8e05f23cb643133bf1c0be4796c863c77e3817c8f2d90c2eefc702f91e862d90dc00fc702f91e5b1733f1c0be50a3cb6437
  | 8, 0, 1 => 0x1f8e05f23cb6431cbbf1f6e05f23cb6437
  | 9, 0, 0 => 0x1f8e05f23cb6436
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
  | 0, 0 => 0xe7e1dff30000007001ff000000e0efdfef00000000e1e0c00000ffffffff000001f1e3e1c00000fff1e1f300000000fffff
  | 0, 1 => 0x7000001ff000e0e000e1e0c000000001c1e300fff000fffff00fff000e3e1c001f1fff1e1f300f8f000fffff00000ffffffff
  | 0, 2 => 0xe3f8ff8ffe00fe3fff181e3e1ce31f1f8f1e1f31f07f07f01fff1f07f07101fff1f07f07f01fff00fff000fffff00fff00000000
  | 0, 3 => 0x1c070e7e1c1f31c070070001f000000e0e1c1e3ff1f1fff1e013fffff1f1e3e1cff1f11f1e3e1cff1f1fff1e1f3ff1f11f102010
  | 0, 4 => 0x1ce7e070e01fcff1f1fff1e1f3ff1f1070001f0ff1f1e0e1c1e3ff1f100000000ff070fff001f0ff000fff1c1e3ff000fff00000
  | 0, 5 => 0xffffffffffe1ffffff1f1e3e1cfffff1f100000fffff00000000ff0001f1000001c07007001e1000e0e000e1e0cfffffffffe1ff
  | 0, 6 => 0x1e0ff1f11f102010e3f8ff8ffe00f00000000000000000000000000fffffffffffff1c07007001ff000e0ee0efdfef
  | 0, 7 => 0xe0e001e000000e0e0000000000e0e0000000000e001c000
  | 0, 8 => 0xe0ee0efdfef001f1e0e1e1f300000e0efdfef00000e0efffff00000e0e1c1e300000e0e0000000000e0e0000000000000001e0
  | 0, 9 => 0xe00000e000000e0e000e000c0000000001e000000000001e00ff1f1fff1e1f31c070e7e1c1f3e3f8ff8ffe00f00070e0e1dff3
  | 0, 10 => 0xe0e0000000000e0efff1e1f300e0e000000000000000001e0000000000000000000000000000001f10001e1f30000000000000
  | 0, 11 => 0xfffff1f1e3e1ce3f8ff8fffe0f00e7e000e1ffc00fff000e3e1c00e0e000e1e0c00e0e0000000000e0e0000000000e0e00000000
  | 0, 12 => 0xe0e1dfe30000000001e00000000000000000000e0e01e000000000001fe00000000001e0000000000001e0fffff1f1e3e1c
  | 0, 13 => 0xe0e0000000000e0e00000000000000000000e0e000e1fec00e0e000001e000000000001e00000000000000
  | 0, 14 => 0xe0e0000000000e0e0000000000000e0e01fe000000e0e0000000e0ee0ee1e0c00e0ee0e0000000000e0e1c1e300000e0e00000
  | 0, 15 => 0xe0ee0e0000000e0e000e1fec00e0e000e1e0c00e0ee0e1dfe300e0e0000000000e0e000e1e0c00e0e0000000000e0ee0e1c1e3
  | 1, 0 => 0x1c000070000001c00007000000000000000000000000000000000000000000000000000000000000e0ee0efdfef00e0ee0ee1e0c
  | 1, 1 => 0x1c07007001ff01c070070000001c07000001e001c070000001e01c070000000001c070000000001c00007001e001c000070001e0
  | 1, 2 => 0x1c000e7e1c1e31c0000700000000000e0e1c1e31c07007001ff01c070000000001c00007000000ff1f1fff1fff3ff1f100000000
  | 1, 3 => 0x1c07007001ff01c07007001ff01c070e0e1c1e31c070000000001c070000000001c070e0e000001c000e7e1dfe31c000e7e01e00
  | 1, 4 => 0x1c000070000001c000070000001c0000700000000e0e000e1e0c00e00000e000000e00000e00001c070e7e1dff31c070e7e1c1e3
  | 1, 5 => 0x1ce7e000001e01c07007001ff01c07007001ff01c07007001ff01c070000000001ce0e070e1fec1ce0e070e1e0c1c000070001e0
  | 1, 6 => 0x1c070e0e000001ce0ee7efdfef1ce0e070000001c000070000001c000e7e000001ce7e070e1ffc1ce7e070000001ce7e000e1e0c
  | 1, 7 => 0xe3f8f00000000e0f80f80fe0001ce7ee7efdfff1ce7e070e1ffc1ce7e000000001c070e7e1dff31c070000000001c07007001ff0
  | 1, 8 => 0xe0f80f8efe000e0f8000000000e0000f8000000e0f80f80fe000e0000f8000000e0000f8000000e0f80f80fe000e3f8ff8ffe00f
  | 1, 9 => 0xe0f8000000000e0000f8000000e0f80f8efe000e0f80f80fe000e0f80f80fe000e0f80f80fe000e0f80f8efe000e0f80f8efe000
  | 1, 10 => 0xe0f80f8efe000e0f80f80fe000e0f8ef80fe000e0f8ef80fe000e0f8ef80fe000e0f80f80fe000e0f80f80fe000e0f80f80fe000
  | 1, 11 => 0xff000e0e00000ff000e0e00000ff00000000000ff000000fffffff00000000000e0f8ef80fe000e0f8ef80fe000e0f8ef80fe000
  | 1, 12 => 0xff00000000000ff000fff00000ff00000000000ffffffffe3e1cff1f1fff1e1f3ff1f1fff02010fff8fffffe00fff000fff00000
  | 1, 13 => 0xffe0e00000000ff000fff01e00ff00000001e00ff000fff1c1e3ff000fff00000ff000fff00000ff000070001e0ff00000000000
  | 1, 14 => 0xffe0effffdfefffe0efffe1e0cffe0ee0efdfefffe0e00000000ffe0efffe1e0cffe0e07001e00ffe0e000e1e0cffe0ee0e00000
  | 1, 15 => 0xffffffff1e1f3fffff1f102010ffffff8ffe00ffffff00000000ff070fff01ff0ff070fff00000ff070fff00000ff000fff00000
  | 2, 0 => 0xfffff00001e00fffffe0e1c1e3fffffe0e00000fffff000001e0fffff00000000fffff00000000fffff1f1e3e1cfffff1f100000
  | 2, 1 => 0xfffff00000000fffffe0efdfeffffffe0e1c1e3fffff000e1e0cfffff00000000fffff00000000fffff000e0000fffff000e000c
  | 2, 2 => 0xffffffffe1e0cffffffff1c1e3ffffffff00000fffff07001ff0fffff07000000fffff00000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7766eef5000005744aef0000006b7eceed000002a3e4e2d000005f5cacd8000001e1c2c18000005540a0d0000000006e675
  | 0, 1 => 0x5740004b7700062600065625002930003c367005640006f6750056400043410001d15541a1d2002830007e677000007f7eeefd
  | 0, 2 => 0x63a8ba8bb400f42d6c081c3418211d18081a1520f03d03d0198a0a03f02101b2f0503701c013a7007f70007f777007f700011102
  | 0, 3 => 0xb51d1d5c1a1d2941505540a1d025091c1c181c2b11c1948120129056414043410901401e1c2c18901405540a0d09014014002010
  | 0, 4 => 0xd6b5a7d7ae1ddb51d1d5c1a1d2b51d1d5c1a1d2b51d1c1c181c2b51d180810102b5150d5c0a1d0b5091d5c181c2b5000d5c00080
  | 0, 5 => 0xfbfefbebf7c1fdad6c1e1c3c18dad6c1e181808dad6c00001000da8081e1808089856416043c104ac2c0a1c1c08f7bdbfdfbe1df
  | 0, 6 => 0x4010414083e0903423422623563a8ba8bb422f00202202242250000000000220ffdfddfddbdda9c5745744bdd06fcbdcbdd9dca
  | 0, 7 => 0x25293c1c1018225293a0a3432725293a0a10102252938081010225010e1e083e025202e1e242a525000e1e0008020280e023c040
  | 0, 8 => 0x256b7e1e7d7e7253d3e1e3e3f725293ebffcfef25293e1e7e7f725293e1e3c3e725293e1e343a725293e1e1018225293c1c183e2
  | 0, 9 => 0x40e00282e440042e0a283e440d0862622265e250842402041e20b53d3f5e3e3f7b53d3f5e3e3f767a9ba8bb410f257f7e1e7f7f7
  | 0, 10 => 0x4ae2e202252254ae2e5540b0d04ae2e000010004ac2c2a3c1e284ac2c2a3818084aa0a2a3a4a2d4a9d92a39a95a4a8082a380808
  | 0, 11 => 0xdad6c3e3c3c186beafaabf5e2f4af7e2a3eff7d4af6e2a3e7e3d4ae2e2a3e5e2d4ae2e2a3a5a2d4ae2e2a3818084ae2e02001800
  | 0, 12 => 0x2d6b7e3e7dfe72d6b782851f222d6b7808111022d424e3e41ea00c43443449fe00c43402041f200c01043408be0daf6e3e3e7e3d
  | 0, 13 => 0x6fa9baab9090a6fa0aebfa4aad6f808ebf808886f808aab808084ee3e6b7edfed4ee3e414093e04e8186b788be84e8086b780888
  | 0, 14 => 0x6febfa0a353276febf808111026fc3cebfc9fe86fc3cebf819886fe2eebfe5ead6fe2ee1e010806fa9bebfbcbef6fa9bebf9098a
  | 0, 15 => 0x6febfebf9198a6febfebffdfef6febfebff5faf6febfe3e7dfe76febfc3c119826febfaabf5f2f6febfaabb5b2f6febfe1e3d3e7
  | 1, 0 => 0x9c010574009809c00057400880985645404b450985405604ac50945405544a4d0905405404a6706febfebffdfef6febfebff5faf
  | 1, 1 => 0x9c5745744bff09c574574019809c57402041f209c574414093e09c574000013209c574000011009c42457441ea09c01057408be0
  | 1, 2 => 0xbd293f7e3cbe7bd293d7c10982bd7f7f5e7f7f79c7767766fff59c776202253259c20277624aa5bd5f5d7c5bff2bd5f580811102
  | 1, 3 => 0xbd7f7f7e7fff7bd7f7d7c5bff2bd7f7e1e3d3e7bd7f7a0a35327bd7f780811102bd574e1e01180bd6b7f7e7dfe7bd626f7e65ea5
  | 1, 4 => 0xdea1a7f780988dea0a7f7a4aadde8087f780888def7e7e3eff7dd4f527c0ee550d4f407d6ee4d0bd7f7f7e7fff7bd7f7f7e3dbe7
  | 1, 5 => 0xdef7e6162d3e5def7e7f7efffddef7e7f7cbff8ded7c7f7cbff8ded7c2a381908dee3e7f7edfeddee2e7f7e5eaddea1a7f7acbed
  | 1, 6 => 0xffd7cebf81988ffebfffffdfefffebfd7c11982ffa9bfff9098aff808fff80888def7e7f7efffddef7e7f781988def7e2a3e5f2d
  | 1, 7 => 0xf3fcb80810002f0fc0fc0fe450fffffffffffffffffffffffffffffff80811102ffffffffffffffffff80811102ffd7cfffcbff8
  | 1, 8 => 0xf5fc0fdefe4d0f5fc0d5c5a4d0f5d50fc8ca550f0fc2fc2fe675f0d40fc2ca670f0800fc280000f0fc0fc0fe670f3fcbfcbfe45f
  | 1, 9 => 0xfafc880010000fa808fc080000f5fd3fdefe5d2f5fd3fdcfe5d2f5fd3fcafe777f5fd3fc8fe552f5fd0fdefe5d0f5fc2fdefe6f5
  | 1, 10 => 0xfffc8ffffecd8fffc8febfec58fafeefe3ffc58fafeefc2ff675fafeefc0ff450fafcafe3fee7dfafcafe3fec58fafc8fe3fec58
  | 1, 11 => 0xff808ebf80888ff808e1e00080ff808a0a00000ff8088086e675ff80880800000ffffffebffd5affffffcaff777ffffffc8ff552
  | 1, 12 => 0xffa9b80810102ffa0afffa4aadffa0aa0a24225ffd6cfffc3c98ff9d9fff9a9daff948fff82898ffa8bfffb488fff808fff80888
  | 1, 13 => 0xffe2e80801000ffc2cfffc1ea8ffc2c82841e20ffa9bfffbcbefffa9bfffb4bafffa9bfff9098affa9bd7c18be2ffa9baabb4b2f
  | 1, 14 => 0xffebfffffdfefffebfffff5fafffebfebffdfefffebf80811102ffe2efffe5eadffe2ed7c41ea0ffe2eaabe5e2dffe2ee1e252a5
  | 1, 15 => 0xfffffd5c1b1d2fffff94813112fffffa8bb510ffffff80811102ffd7cfffcbff8ffd7cfff81ba8ffd7cfff81988ffd48fffcaef8
  | 2, 0 => 0xfffff82851f22fffffe1e3d3e7fffffe1e11182fffffc1c193e2fffffa0a35327fffff80811322fffff9e9d3d1afffff9e99190a
  | 2, 1 => 0xfffffd5c5b5d2fffffebffdfeffffffebfbdbeffffffaabf5f2ffffffaabb5b2ffffffaab9190afffffa8af5502fffffa8bf550f
  | 2, 2 => 0xfffffffff5fafffffffffbdbefffffffff9198afffffd7c5bff2fffffd7c11982fffffd685bd52
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 52 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 52 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 278 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 278 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 278 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 278 then wireAt i else 0
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
  | 4 => 19
  | 5 => 331
  | 6 => 1225
  | 7 => 492
  | 8 => 10
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xd9baeb0bd3c6a46ac2ba8f309e3e74ae983e85048fcd3a3e850c62a68167794569ecccc7654f69745a475a7c4e808dfd441abaa920c9f1e5205cc7cf1b4c51f60fd6cd990bf644fd040f212d
  | 5, 0 => 0x1d1f641f1bc24f8a1b8129591b5300e41ae2b9091a9569301a7eccc11a3fc2e51a13e99e1a0aa15e19169d3319009fff18daf86218c37efc170d086f15fd38b015dac5e915bc22d8150d4cfa14e03b20143aacf3143aa46e135a3c0613106c0312279d241223d25011f21271116a87581161181a0f564f730f415ad90f302f500f11262b0ee25c460ee0af2a0db432850d9e19500be3993f0b7002330a447c3409874f3d09636689084bb82d0808d5e007b40e280772bb3e075140fd06ce7e4f064bab2605b864970562713e048e7392046c39c1040e560f02dc1b26028e1fb30274c39c0226934702204f5101d29fcd01c77b8801b2c4c601858bf90175e562
  | 5, 1 => 0x3b52acf83aa6609939c5c12539c34d3138c18fab38bbbf8c37edc5f63795f6ec3765a7c03710815435c6e9dd358f6bef356728f635176eb9343096ad33ef4f633107ca4930ef39b630b4f53230a67ff830378bbb300bb48d2f7f04ef2edae5ed2ed537322eadcace2e84d2cd2e6f42b42e124b852e0369bf2ddee4c92dde33dd2d8de92d2d6799552d636b692cdae89a2bfa091a2bed559b2bac62dc2b66c1882b20b3c52a709ff12a60e87e2a347f192a3198e02a17b630298d50c22873acb228732d7b27907a0e266f0cb225f712e925d26c85248ba27c239e1af522fb36db22df9e0e21b339f321b04b482118a16c1fe529721fdd54731f2c9cf31ebe3426
  | 5, 2 => 0x6195457d618a6a10611f9d875f9defbf5f8023fa5f07899d5ecca7015e6a0b595cecbbb75c5f899a5b3bed485aa8a6b95aa68a955902096e58a4f987587328fb583a210d574085e6567d130c541df39b53e2703d529efe08519fb45c50d1414c50a2613b501d2ed74fd7eac94f57f3d24f20d9454df1c4d74d43211f4c45ddef4bc38b784b6e21e64b24895f4ac2b82f4a7e3fa34a55e64349a0b8ec49305b9b462335034597d6de4551190a44ae3fb0449b0d9243e9290d4351a0fe435117db434ac03242b779a3425d8ab8423bf0e0422eb483422d017a410769b740a605d0407225523f19de853ee0318d3e01209b3dd1dfcb3d99f2943d30bc313c9d75a2
  | 5, 3 => 0x863518c785a614e5855c86f084ba446a82ebf5a881d7f28c80b2170f806558a88022937a7fb807ca7fb169e17f2cc9377f24c13b7eb098bb7dd1112a7c4ad5867bb0128c7a92749f7a85129f7a014426793a6fd8783597a077842e82770cd63976d684c876d5223b76bf1f707573b11d73b6019e738810d373436dd970e87d7670c1f8716fe675ef6fa78ebe6f80bd776e52eccf6d3905586cdf2d166bcf90f36afac8926aa8731b69f6eb0d69e46dbf69d0a4b069acc5366991e76868f79ab3688ea6bc68742b926733942566b349566586cff765365ca4651cffbd64e6ab0264e0c49164bac83664553680643988c963f9e424635f4efc623e1247620020f6
  | 5, 4 => 0xdfe672cddce8ce41d80b7990d74dcec0d4e1cfcad05fa3b3cfc3ca17cef3ff30cde805e0cb72d8eecb2728e7c99d9a0bc570b187c39f608cc2b1c558c1fb2a7ec18a15cec07fdf22c0188a3cbe0880f8bdc77e2bbd19af86bb06ca40bb03c57ab9e60c65b7610a65b702d21ab4d0e6a0b38384c6b35b4e1ab1d9005cb1019719b0e8ce19ae2f6e77ae27cbe2ac0a3fd7ab47af95ab3c18fdaa4d3edba9b9ea93a7abc528a6ef532ea3c65a94a11e14dda0dbfa33a033f13ca01b91ce9f6a83109f012d219d01d3cd99814291996a2a2d995b2d06947d9aae9205c370919f32ee9190d39c908d19698f5dcb3c8e0ba0b88b39fcd789db0760882be4e1882032ad
  | 5, 5 => 0xfd53dd81fbfc557ff37019b2f0f8df95efa34369ef1b3934e7d60daae76dd47ce7677ebde4fbf9a4e1c315b0
  | 6, 0 => 0x78f1e530787d7a5077edc7e074921400737882a06a693b50665520c0659646506540181063d5224060f596e05e1326505b43f60057729b6055afcf4054d1e1505270d1e05169eb00514ebac04f7559904d32ad804bca65904941f6a047e054104572614040e560f03f1b95203ae4e9903abb2f00375c6cf035eb4ec035a956503476202033b05b5031a0daa02eac567029aef9e028da25d02898f5e024ad8f90241c4e10219fdf802102cb901f5db9e01f2900401b2c4c601a6e4da01a44b7b019c9fad0198403d01866a36017f753501652a32015e807f0146c416012a58400111cbc900f5a3d200e52646009787b3007d93d800693658005b006f002e9cb3
  | 6, 1 => 0xee7b93a0ee672b50ed86b730ea887730ea022dc0e7e15130ddd4aa00db432850da46fb90da1b46e0d9cbe430d92daa50d82e74d0d2d22890d1802ee0cf439bf0cc62e6c0ca165b80c7bcab90c6f23470c3193340c03b9010bb0f9310ba77e000b3b2aae0b2e0ec30b2c8ce60b2c4f690b15b2110b09f3650af6cb310af23e1b0ac986c50abb3de50ab8b2690ab6224b0aa0caca0aa03d900a9628be0a81a3e10a7d079a0a75789c0a3d884a09ea0c3209bd51ef09a8e93109a18f5409874f3d093e7356092be94c091999780903dbc50901863008fa445b08f4d80808739b700856ca260848694b0815b7f9080f15bc07fab1ba07c2594907b5400d07962ead
  | 6, 2 => 0x15e9498b15b18426158c470e1581f8c8156a912f1561a43a15602014155cba4e14db18b514b47c3e1486a38f147fea6e147cb67b1415063f1413d60813fdbe2913eb15dd13ea83c213e90d2b13dbc3bf13d5001c139302bf1317dd2b130a5a891305f52212e9443c12cd450012b8ab41125d0b7e124d6d63123c1c3b1233466a123247971223d250121b1123119557c6118eca2111894c1a11880f961187183a116eed1b116b4724116a8758115b67ca1142fa4111408e9a110f8d8e10c5277710a92875108ef5b91072050410532c1f1004221f0ffdfe370ff073950fec104b0fe0ec5e0fde41e30fc7e3a30fc75d210f8e38f60f8009980f76f4eb0f56ffe6
  | 6, 3 => 0x1d5bd8171d4a9d981d0c1c131cf670511cbf657e1caf33921ca0b1831c96ea491c84fb571c6f9fec1c1fc9361c0c1b4b1bf5be811bd1fa481bbaa2fd1baefe391ba367651b7aa30b1b78d4bc1b62a5db1b52bdbb1b3c1cc21b29bf4b1ac899ce1a87fcc01a8148131a6b63331a548add19f9a28419e220af19c2b1f019ba87fd19ba301a19774199197460391921237f19169d3318c91a2e18c904ec189d69961882b169184b4579184ab4571841fcce1839cef01835b7a618043d6917dbb70317bcd81e17bba65117b77a5217a260fe175a929b173643a81729918f172938d71712096e16d7d05c16995adb16987722167fda5b16766cf2165c2d5c16100cbf
  | 6, 4 => 0x25afebbc25471fea250aba5724fedf5924f27cee24bc09df2443fd30241b265d2416c07e24140a4123fc45a223ee01b823ade26823aa74da23895e5b2373cc522365101622ea3ac022d85c9a22521a0421d8db4721a5c3f121901609214d97092145ca59212c87fc20a84c142064873a2062e284205cc8cb205b0a2a203ca2471fe039d21fb72b911f9bef851f9874111f9547f51f87b1c01f70dac81f47d9851f0286b71ed9e4c41ec4d0da1ebcbc8f1eaa0f9b1e7359ed1e6f5e891e5a4bef1e56e02b1e4837591e3f594f1e3a97551e35b7f71e346cd21e2780c41e184c7d1e06b5881e0576261dff4d111db574801d984e6e1d826c881d825b1b1d66c50e
  | 6, 5 => 0x2d3c50982d06d0c22cf8cd042cf085992cef63982cc795ae2ca069f22c611b6b2c4d2a222c3e81882c119b4b2baf6f8f2b812cf62b4013f32b09ceab2b08f8cc2af68de12ac41d2c2a95810c2a734e672a6347522a60e87e2a5335872a4238582a36732f2a3198e02a222ab32a1317a029f5789c29c478db2992b93229740e862971ba40296b38aa2956f3e6292af8b7292576e32920d8b3291385ac28e1d56328df87aa28c93b9c28bc54b328b96dc8289a15a2285a6120284836062842e262281a4d9f281909f62802e9c9275d28bc272a02302707a0fd26e23bf026bb2fef26b886cd26a0c9d226786863266cd792266407622604931525eb7b5225bf78b9
  | 6, 6 => 0x3619ea8d361262443601d28435d89aaa359ba67a35970aa9358ad894356512d03551f40935239d6d34ecd7be34e85a3334e12a5934d2fbb734b928773481cae4347c735e344da139340993c533e6b2b633d51d6733ce1343338e027c3389f6ab33864f1f336a01d2335d81953327d92c332329e733193e9a32e16b8932def36c32d3764f32b96323329cbbfb32906673328e8708325f2c64320e189f31b1ab293177ea883157bf6e3122199e311dfd6a30d528202fdcbf742f954dd02f8f1ff32f74af282f6745e12f1abea52eedfa852ec5ec072e8d1d1d2e45ee3b2e41d80f2e2503b32df741622dd75a262db09fc22d9f970e2d618f3b2d3ff5e92d3ea431
  | 6, 7 => 0x3d946b583d7dc3333d60158c3d4903cd3d2562093d1f3f593d1e34fb3ce6437e3cd7acd73c9643853c3970963c346cd83c27f8ae3c21c3983be497a23bd6ad1d3bbf524e3ba5ac113b9031bd3b34c0e23ae826bb3aace7f43a9a85bd3a97b4d03a822ece3a7feee53a5b119139ff1f0a39e37c1a39ddbebc39891224396f572d396d2e4d3965a1543958c2ee38eec90038ea75ab38da452b38d186c938c86292386f6c3938695c3f383545ab38296398381efb7a381859c33808c78237fdfb7837ea5ebc37d4a1c237d1be9637a4a2c837a4666c376ecd623766c85037596ec3374682113702e44236de7a8736d69bdf36cd76be36cb59783679dd0b366fa272
  | 6, 8 => 0x4812707947ff7ab347d1bb1b4795ee6d478b713d4760868246ed067a46de284246b9893046b6a8dc46a6e54b46a11ddf469949b546463055462e1968462000d24615666346115b08459774c2457c8acd456daacd456958424526b408450ea01a44ea5ff044d5829944ae84d9449d3035447f91b144300bdc43fdf1ec435117db433f660a4335a68143334a0242c90b1142b779a342b7442c4288da78425ac010425327d741a826db41a0c128413586ab40af69b240a8378340a60e3740a28b4c4062ec4240455b7a3ff4ef3e3f7f6a493f6ce07e3f62ae583f296b073f1e2b9c3ef9b7083ebac68e3eb6cf343e38dfb93e0ad2fb3dc293cd3daf73bc3d9f7614
  | 6, 9 => 0x528ce01951cf671751bb2a0f51ab7a23516401cd51496a925129991d511d2be4510a33e250ef354250eca9cc50e499dd50b80df750b19406501f9e514fffcd0a4ff70f444ff5df0d4faafd564fa753334f86a4154f56d9744f29237a4efcd55e4ef9e6304ebf453b4e9d19034e3f790c4e23904c4dd3ad484dc7b19a4d8cd6aa4d43a2314ccdf14b4cad82f14ca859dc4ca1aa074c7463374c2eb5784c1e35cd4be62b244be3ee324bd15be94bc5e4304bb8d2fa4b6e21e64b6aa13e4b4b81c74b1f8d454b1e92974b1168534af8703d4aee73794ad762854ac953704a5f19f44a2e53494a0125c0497ec74849697f42496885e54931ec384919875c488de70f
  | 6, 10 => 0x5c0b37e05bcb95c25bb5dc8a5bb226b25bb03c075b33e9485b1580d15b023f875ab7f2675aa2af7a5a9f5dfd5a6fa4e45a5a68e35a197e0059e9114a59c84b70598cb1c5596cee2e596b7d44593f584358ca2eae58bb531a58aa0f00589311d45882ba88586233b25817540b5813f0b45807cc0957b93b955731497456f411bd56f3df7156d7ea5656b3de6b568ff7f1567d130c5672a48756425f3155f67480557f4cd95571ce4a556f277754f8a63854f0504c54ba54e354b8020854aaac745488605d5479ade654198a3e5416d04b53c3fb8e53a51bbc5377f3e653514afd534934bd533c9ba053181bf85314eaf652ead02b52e8c50e52e2321e52dc9cdc
  | 6, 11 => 0x67e0419367d9415267d2ecc667770155673f974f6733942567296a4a6725e9c56706143967044c4c66fd841f66d94f9766c97e4e66af839d669a4886665174db663bc1886624d4f6660d92ba65ee6d3a65a681e065438d01650bdfd764e6ab0264dbdd216486b143646b996f644d72e663c9dda362dd8f1e626770156264afc1625d8697624a2d73620486bb61ad365a61ab00a96169ffad613f4bb660fbe7f960f47f6c60dc0ef760d8b88860d0e7fb60c0e6cc6056b15e5fc559925fbac6fd5f20e9805ed6a3f15ecbb8db5eb5ede35e5e95475e5438f05e22a7545e0e53495da6d4765d7d6e2d5d59965f5d5624535d1e66bc5cde0cce5cbb87cc5c7754db
  | 6, 12 => 0x7502d39f74d2ee7874c5ce3d7481ccfa7410bb2473e9209c7365dcea7361e71e7331c2687306471f72b28339729573027251ab777218e0f571fa161671c8678771a26241718d4b857166cf87714b8ec87136656e7130886e70fe4ee070ab2568700050ab6f9a15cd6f7090bd6f596a256f4ebd9a6ed8da0b6ec911ee6e3f00b06e04f5ec6dbfabf96db7d3e86da6d4a26d8815996d71e5326d60d7e36d547e0c6d2a833e6d1da4d86d1163566d0422a36cf9e7a76bcf90f36bcccd376bbe0e9d6ba0f1c86b2262386b0ca3d16af897496af4e10b6a610cd96a41bcfc6a258de66a22b4f86962df3869148b6868c1438968ade54568576a0d68329f3367fbf59e
  | 6, 13 => 0x7fb866157fa786767f8ef2d87f3d62797f2cc9377f05801f7f00ecae7ef775487ef20d5d7ee0fc947eadd0e57e9982a87e964a3e7df1da2c7d7d57bc7d2e7cf97cea112d7ce7e2b17c9c8f237c69c65e7c4faf817bf0b2df7bd019c77bb2ffa97ba3c0797b334ca57ada8ab67a8ef3507a7382a17a5857927a2bf43679d342cd79bb6d1e79ad660279684f62795acc8c792903cc791c12547915ad7b7911f99d78bb1eaa78a46f127877b0537850917f781b6dbd78120717780402147800865577e8b9bb778424c27777dbfe7753784a7730263a76e1a5f076d69d9076d00d2c766e04be76461d727626fba57623dab175cf5cc175a838e0756948e675217693
  | 6, 14 => 0x8e183e158da6f0c78d88441d8d72216c8d395ff68d2f53818ca14df68c5e2c4f8c51eb2d8bd322518b74ea068aafa50e8aa657898a7f22088a7994f88a293c538a0d8ef789efee91893fe42c892cfdea88fe5bb888f823fd88f4b3ca88bd66ca88a82a5488003ed287f03d1a87e13aa0878be23f874f92698749a55b871e3ea487038fdf86d1329986be95e986bb68948665f64386465a8a85ef75c685a0b970857f1b66849e475c845d1c66844b1cd4840e75af83ee5c6183df594383a21eb183814402837f6b3f833df90383328cfd82de71178295aa1e82768228820b9a5f81f6d6c281b76e8e818c8a2481151380806266ad8051d8b38040d0787fb9c781
  | 6, 15 => 0xa049bbb59fa7e8e29f7298a79f0c76639ec0d7899e3c45669de2e3f49dd1537e9daae7359d1f09df9c0647769c01232b9b4d17b59aa07b839a35a57f99f80ac699d6685399cb170e99a181bf9997d904992cedf8992c6b7e99200f9299004fbf98ff0c1898f42b2698e977159882e2ec979939bb977e307796fb60e996ad47ba968aafbe9689804d965531e695ddc41b95955e8d956d1028954ef73394e8477894b8834e94ad8e5d947012d39409b1f093f38d2a93e5c51a931a02fc92d649fa92cd311e929bf5d992976d6492904ad8927200f6924b56d4919ac8ae918b0169916155de8fda83be8fc42d338fa19e1f8f4a16428e7d732a8e5d90ed8e3f8c77
  | 6, 16 => 0xb1019719b0a7b14db0a47233b06a21d7b03646e7b02268afafdcaeb4afaab267af616e2baf448f52aed94acbae55a6dcae1bf85dae00205dad965e55ad8b64a9acbf5c17aca9b064ac68c860abcb65acab676f4fab47af95ab3f45e1aa6b2cfcaa3d4546aa00aaa3a91d7cfca8e78fc4a8cb32a4a8b61457a85b062fa8309305a7fbc882a7a2a7a3a7262e14a6bf3e86a6563cc3a5d3bbe5a5b27004a5a2b6d9a533b563a5323c56a52d601ca49fea3ba434b4b6a410b11aa3c65a94a34c43b5a2e65551a2cd8bc3a2a97873a2a6c31ca29f9104a284be75a284b47ea26ac20ea263fdeea2487bd3a23d1ba0a16c4690a1662bafa0c4a17fa0a48f39a05aa24d
  | 6, 17 => 0xc940b3fec904d60fc8df6e8fc828f799c7718d50c7554d2ec7327c7fc6f8273dc6b2dd46c59c2c97c4df0d37c46ac8f7c4410a46c42d7db4c391afb2c3780010c3334588c29d7199c2932210c2755bb0c22701b7c158964dc0f21befc0cb7d2fbf4aa2bebf200208be4bb0d8bc446fb2bbe49247bb9c9e61bb8f7c21bb245530bb13bee6baf70c47ba701036b9d7cf39b99d8907b9349dd0b8e9992fb8025b3bb7ae1533b717dd2fb6fb2445b6cade13b6be7634b6671ba4b64676f4b63a6097b5e82352b541bdfab51ce2f2b4d0e6a0b4b7aa29b4442e98b37ea96bb36706acb2f25cf9b2e06130b27deebbb23cd636b1ce22c6b1c67554b1aab58bb1037f98
  | 6, 18 => 0xf3f26c29f1a91aa5f13569a4efab81e4ee1edf3bedd0785ced8d35c2ec5d6e52eba28b6ae9e0e609e9d44651e967135fe8da166de863d8b7e729b89ae6118099e54dbc12e4635b42e28562ede259762ee2433ca3e1151f08e0a18849e095f543e0918c13e050a6c1df2c783edf204264dede9553ddb7dd18ddb1ac85dd93fd71dd4834b4db726f76db3a90b6daa10b17da9fdba6d99b8409d9719f58d8c3f1bfd615987fd5ce88c2d553ea4cd49d3a61d38bde2bd2373aebd2370a95d09a8c53cf7ca766cf0b78d5ceafa34acdfcc0dfcdc288cbccf24bcbcbe36130cbd5b4f2cbb9f257cb67622ecb5a385fcb2728e7cad3949acad25745ca8af8c4ca5a75fa
  | 6, 19 => 0xfcd91be7fa4ce404f9f7f128f87fe82cf836611ef79d8a68f7368355f66bd375f5cbaefe
  | 7, 0 => 0x12ae5da31232479711ed84b711b4128d119811441187183a1134c93410d1aa9610c280c5103ead2a0ffdfe370f8b2a5f0f3d84400ea68d810e7ddf9c0e7dd0190e589c450d61f2fb0cf91d9f0cb3009d0c867e660c22507d0bd753a90bb2ffb10b989d440afb5dd30acf09dd0ab7b9ae0aa9dacf0a9628be0a71f9560a172c4909ee1b6f09eba6f407d82e3c07bd347d0754ea1506cd9ad406c7654b06634425064612c706291d83061ab286059e8b170590310f04d0acec040745c603f1b95203e36454036df15003601271033b05b502e9d44b02d5abde0296f579023f103c023c952e01a603fb0129b75501283a1700dd496a0086a50c0064991500103def
  | 7, 1 => 0x25bece64259eb530255ffecb2509c4b824a7e76c2485a934246ade9624296515231857ea22ea3ac022daf26b225c733222543c1c22521a0421e9d24d21a1d2672064873a204aaf2d203e530f1fe039d21fb72b911f9bef851f608b651f3d31db1ee4e3db1ee472391ebb13731e3d0e221e17d8601e08e1531d094b741c53b96d1bea35011b8548e61b78d4bc1b70b1901b325a461a90e4691a5d39541a4058c31a2bfa9c19e3604919deb3e219b1d448197fec7b196672e1191531f41900f42918e3fb0a18787ffd181aa94117d7cb95170db67f16e8db1816d8a81c1662ea0a15ff8a4715f86a801561a43a1528ba3c13b5da6d131bfefa130748e512b8ab41
  | 7, 2 => 0x3a8b1a653a861c9939de879e3958c2ee38ad846e37a1ed1c375fd1e83732d33a3724f45b36f4981f36b6da9236ad5160363c57f4361b1af435d89aaa359aee6d358e7c13357bcd57355e29ce354bc4fd3528ce7834746a9f33d93c6b33193e9a330961a632c3d3da329cbbfb3294bf40326a06213243d5cd317141fd31381b073129ad3f302ca7772f7655c82eedfa852ee51d392e6753e42e46479b2de85b922d90db782d770a592d6df75a2d014b912cf085992cae27f22c9946a22ba064522b48380c2af4104e2a60bc7d2964176b2882e2b2284db2db27f341652775450f2752ae7526aa53c326a4b5bf265363bb264ea121262d41fb261c309d25eb7b52
  | 7, 3 => 0x4f624ff44f490be64f0fba7a4ec05ebd4e79bd534e7327324e00c0ea4de254b54dd111674d2b306b4cd8ba054ca60af44bff26be4bc969994bb8974e4afc5e1e4ac0774d4a6707154a601e184a5928364a3f78dc49e125c649d602e849226c8f48f889f848ebd2aa47f69d2646e1bded46e149a24696c818462e19684615666345f6b58445dbcb8245c07cca43b9f0a343a9f848433f660a432891ef42b779a3425327d74223bdb94214fad141a4b5d6413ca69640f8a7b54079af6340455b7a3f8b9abe3f6ce07e3f086e6d3e1c8eb63df1aaf13d8620523d18fbc93cedcf813c9dc2fe3c52b0633c39fd5e3bd0b7833b76a7473b23954e3afd7b253a8b9b21
  | 7, 4 => 0x6cd622c66c8fa51c6bcb63fb6b89f08a6b6909ce6b58c0516b46b4d16ad0038a6aa2ab606a510b386a2a46cf6a0139de692e70ee68ff5c7d679d352a67425c6166742ba76659a12a64f38968633af01163353df46284e0436240ab8760b58bf56001a2b65f2a63495ec6f1c75ebcebc25dc82fa15d9647d45d93d62e5d6275f45d23bf8f5c9fbd605b2acd595a73054d5a5562f25a1dcce559f223e55943cbfb5923c1c6575addc156fffaeb56dbe56f56da22f056abec6255bb43f755ab6c46552722ed54ed1c75531915d153169294530b9a9452de426a52942b72528ca242520a3fab51efbb6051ab7a23515c2919514f64545143ad3f50c9577f5038abd6
  | 7, 5 => 0x9409b1f09396353d93527dd592ef4533927d8384927a567e91bec62691b98d1291015b8b9074f28c8f46f2108eb06ba68e7679718e35cdb08dbfa66d8d9d33148d1e3ac28b308e208ada8b1e8a0d10dd89f226db89211e6a881ad299877910e28708035286d07c7e8635a6fc85faf2fb85520fcd850f030e830766bf82121d0d81bd8a2f7fb9fc427f97da8d7e8559377d356db97c439fcf7c0721267bf0d3337ae97d0f7ab597257a70b12879a4d76c7952d274794717d67900675a77d135d076eecc3f745a681c727daf3d7263b2ee7260e48f71fb25a270ffce1070cdf074707cee8d6fe858716fa6c90d6f6c29a26f3b46226d45b13a6d2657c06ce17027
  | 7, 6 => 0xc33e8ebcc30bd3fac1c6e06ec1c16a74c16463c6c07ccfeebf74ae55be6b5265be2639d5be107ab6bddd5bacbc008a33bbe49247ba477786ba45dd7fb959c3c0b8cc1a32b7a3f583b3feb3cab3f8265db210ca3fb16429bbb0ec7e1fb080f6ebb0480e0db02268afb00d02d1af1123ebaee65ee3adab993dac8a86ebac3ab49dac296414ab94b348aabfa2cbaaa935daaa3f12b1a98c5b5da8e78fc4a8d9852aa70b5b06a661d0dfa6395456a623790ea4dede88a499e38aa141bf779eab30d29e6bbe4b9de02fb29dd1537e9db654639ce015509bfcd7929b71391a9b308e9f9a04b05998fcecee98c015d3985a34f7984899db978d297c9721f5ed955a0898
  | 7, 7 => 0xfce2758bfb192d73f80ff336f2a07f39f1c1f496f109fd47f0f10dbeee1e2c58ed5ae6a4ec164c1eea555bf2e9f23fa9e8f19d4fe8b03ee3e45c7de4e2f6cc76e2897b1ee23845c8e21fca1de1e7aed7e1b94d76e0918c13df6d0221de1b0bb2dcd6712cda26b2c9d9ed2281d9e7a089d5d13c99d4f736c8d229a3e5d17f337bceeb1ad8cda803e7cae6d7d7ca35eab9c8df6e8fc7554d2ec6b603d4c65b9dfdc62ad07cc5690328c4ad7d99c4ac2c82
  | 8, 0 => 0xd1efb8f3c2afde018ab84b5d7e9982a8764e5f6161ca400842b779a33e277fff2efbd9641606144c
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x1051535440400000000000000900041254403000000010440200720d1054c4400000000010d1013611801404400104d52544040062144314c1400000004150420000000000000020151525404400721011550040000000000000090000000000003000000000000200000000d110100000000d11010000000000003
  | 5, 0 => 0x354402000000000000003000000000000400000000000010000000000005000412544030000000000d110100000520c02000000035085200000000010d101000000000000200041354403000000001404200001182540630000000434d02000000000000005000000000000400000000000040000000000003000004150420000000155002000000035041200000000000000300000000d1101000000000000400000000000030000000000005000000000000400000000d1101000000000000200000000000040000000000009
  | 5, 1 => 0x9000d9450063000000000000004000000000000400000000000020000000000007000000000000900000000000020000000000008000004050020000000454c420000000000000050000035005200000000000000500000000000030000000000006000002504120000000000000080000000000009000000000000600188314c4300000000010d10100005454043000000052004200000000000000300000000000020000051500200000000000000200118014043000000000000003000000000000100188344c4300
  | 5, 2 => 0x4000000000000600000000000020011905805300000c5054c43000000000040100000000000000400000000000020000000000002000000010d10100000000000010000000000004000000000000300000000c8103000003450c20000000000000050000000000003000004050020000000014042000000000000008000000000000200000000000020000000000002000000000000100000001041000000000000003000000000000400000000000040011525404300000000000000600000000000030000000000001
  | 5, 3 => 0x454c420000000000c41000000000000005000d1054c430000180344c1300000000000000500000001001000000035041200000d1254c4300000000000000900000000000060000000000004000000010410000000000000060000000000004000000010d10100000000000050018840505300000000000000300000000000040000000000005000000000000400000000d11010000000000004000000000000500000000000050000000000002000005210420000000000d1101000000000000100180314c13000000000000005
  | 5, 4 => 0x4000002550020000000000000020018041405300000d1054c4300000000000000500000000000030014040505300000000000000800000000000050000000000002000005210120000000000000040000000000003000000000000600000000000030000035404200000000000000000000000000020000052100200000000000000200000000000010000000000009000002500520000000000000050000000000005000000000000300000000000060000000104100000000000000300000000000040000020480200
  | 5, 5 => 0x188344c130000000000000080000000000008000000000000700119320c1300000000010d10100000000000040011435041300000000000000900000000000090004135440300000000000000400000000000030000000000002000002504020000000000000070000000000003000000000000500000000000020000000000005000000000000400000000000050000000000003000000000000700000000000040000000000005000000000000500000000000040000000000009000000000000100118014043000000045404200
  | 5, 6 => 0x115254043000000000000002000000000000300000000000080000000000006001192500430000000000000050000000000002000000010010000000000c4100000000000000200000000d110100000425082000000000000002000000010d10100000314c42000000000000005000000010410000000254042000000000000004000003544020000000000000020000000000005000005150020000000000000040000000000001001050550430000000000000050000000000005000000000000400000000000010000000000003
  | 5, 7 => 0x1142500530000000504c420000000000c41000000000000006000000000000400000415042000000000000004000000000000500000000000050000000000004000000000000600158314c13000004125440300000000000000300000000000020000000000006000004500520000000000000050000040500200000d1254c4300000000010d1010000000000005000000000000900000000000020000000000004000000000000200188314c43000000000000004000000010d10100000000000080000041504200000000010d101
  | 5, 8 => 0x40000000000009000000000000800000000c8102000003550820000000000000010000000000002000000000000600000000000020000000000001000000000000200000000000040000000000006000000000000500184544c13000000000000002000000000000400000000000070000000000006000000000000700000155002000000000000004000000000000500000000000090000000000001000000000410000000415042000000035041200000d950105300000000000000700000000000010000000000005
  | 5, 9 => 0x20000010440200000000000000400000000000020000000000004001404050530000000000d1101000001044020000180414053000000000000004000000000a10000188434c930000000000000060000000000008000000010d10100000000000040000000000002000000004010000000000000040009805840300000c5054c4300001884350c30000041254403000000000000003000003550020000000304c0200000000000410000000000000010000000000005000000000000400000000000070000000000002
  | 5, 10 => 0x41254403000011535440300000000000000400000000000080000000000001000000010d10100000520c42000009810440300000001044020000000254402000000045404200
  | 6, 0 => 0x3000000000000200000344c1200000000000e1000000000000005000000000000700000454c820000000000000090000000000002000000000000100000000000010000000000001000000000000300000000000020000000000003000000000000400000324c820000000000000070000045005200000004548020000000415042000000035508200000000000000300000214842000000015500200000000000000300000254c420000000000000020000000000003000002550020000000415042000000000000002
  | 6, 1 => 0x2000004540420000000434c92000000000000005000000000000700000000000020000000000009000000000000500000000000020000000000001000001044020000000000000030000000000003000000000000100000454c42000000000000008000000000000300000000811000000000000003000003508520000000000000030000000000000000000000000300000000000060000000000001000000000000200000000000010000000000005000000000000700000544c120000000254042000000000000003
  | 6, 2 => 0x510c120000000154022000000000000002000000000000000000000000010000000000001000000000000700000000000030000025500200000000000000900000000000080000040500200000000004010000000000000080000000000001000000000000500000510c1200000000380a2000000000000004000000000000800000000000060000000000006000000000000300000000000000000000000002000000000000300000000000030000035041200000000000000200000000000010000000000003
  | 6, 3 => 0x500000000d1101000000000000700000000000020000000000003000000000210000000000000010000000000001000004548420000000000000020000025002200000000000000900000254c42000000000000003000000000000700000058c1200000000000e10000000000000040000000000004000004508120000000054c42000000000000007000000000000400000500c5200000000000000300000000d1100000001044020000000520c52000000015500200000005210120000000000000050000005006200
  | 6, 4 => 0x10000000000002000000000000200000000000070000005841200000000000000000000000000040000025402200000005110920000000514c82000000000000002000003540a20000000000c810000000000000010000000000004000000500e20000000000000010000000000005000002148420000000000d1101000000000000300000000000020000000000002000002048020000000000061000000000000004000000000000100000000000030000000000001000000000000400000000000020000000000005
  | 6, 5 => 0x415042000000000000004000000000000400000000000080000015500200000000000a100000000000000700000000000020000000000003000000000000300000454c4200000000501220000000054c42000000035402200000000000000200000054c4200000005210d20000000214842000000000000004000000000000200000344c120000000250412000000045402200000001044020000000000000090000000000001000000000000500000450062000000000000000000000000000800000000000050000045406200
  | 6, 6 => 0x28062000000000000004000000000000200000000000050000000000002000000000000300000000000030000000000007000004500520000000354062000000000000007000000000000300000434c92000000000000008000000000000400000000000030000000000004000000000000200000254402000000035500200000000000000100000350412000000000100100000000000000200000000000080000052101200000003544020000000000000010000035508200000000000210000000000000020000000000001
  | 6, 7 => 0x500000000000020000035508200000000000000500000000000080000000000002000000000000100000038062000000000000005000000004010000000000c510000000000000050000000000007000000000000700000355002000000045081200000003508520000000000000020000000006100000000000000100000000c4100000000000000100000000000070000000000003000000000000000000000000020000000000008000004250820000000000000010000000000008000000000000200000054c4200
  | 6, 8 => 0x255002000000000000001000004500e200000000000000500000254402000000000000001000000000a10000000000d11010000000000000000004050020000000000000030000025500200000000000000100000000d0100000000000000300000000000030000041504200000000000000700000254c4200000000000000200000000000040000041504200000000010d101000000000000100000000000020000000000007000000000000100000415042000000000000006000000000000700000000000070000000006100
  | 6, 9 => 0x50000000000007000004540520000000510d120000000000000020000000000002000000000000200000000000090000000000007000000000000400000000021000000015500200000000000000100000000000040000035441200000000000000200000000000030000000000002000000000000500000000000020000000000005000000000e1000000000000004000000000000800000000000070000000000004000000000000100000000000010000000000004000000000000500000000000010000000000007
  | 6, 10 => 0x200000000000050000025012200000000000000800000304c020000000000000010000045480200000002048020000000000000030000000000001000000000000800000304c0200000003508520000000000000050000000000008000000000000300000000000080000000000000000000010d101000000000000100000000000030000000000002000003550020000000000000010000000000002000004500520000000000000030000000000003000004350c200000000000000700000454c42000000000000005
  | 6, 11 => 0x500c5200000004500520000000000000000000045002200000003508520000000000000080000000000005000000000000300000454c8200000000000000200000000c01000000000000002000000000e1000000035508200000000000000400000405002000000000000007000000000000200000354402000000000000008000000000000700000000000010000041504200000000000000500000000000010000000000003000000000000300000000000020000000004100000000000000400000000000010000000000005
  | 6, 12 => 0x454c8200000000000000400000000000020000000000003000000000000100000000000040000043500200000000588420000000000000000000000000002000000000000400000000c4100000000000000400000000000030000000000001000003544020000000000d110100000324c820000000000000040000000012100000000000000100000000000020000000000005000000000000900000254402000000010440200000000000000700000314c42000000000000008000000000000800000000000000000000000005
  | 6, 13 => 0x2000000000000900000000000020000000000003000004540420000000425082000000000000002000004500520000000450052000000000000002000000000000400000000000090000000000002000004500520000000314c42000000000000002000005048420000000304c0200000000000000500000000000010000035500200000000000000500000000000040000000000002000000540a2000000000000005000002148420000000000000020000051508200000000000000300000000000010000000000002
  | 6, 14 => 0x70000000100100000001550020000000000000000000000000009000000000000800000000000020000000000000000000000000200000520c1200000001550020000000454c4200000005010d20000000510c9200000002544020000000324c8200000000000000300000000000020000045404200000000000000300000000000050000040500200000000000000400000304c020000000254c42000000000000004000000000000600000514c82000000000000001000000000000200000000000000000000000009
  | 6, 15 => 0x400000500c92000000000000004000000000000200000000000010000042508200000003508520000000000000030000005504200000005210d200000000000000200000214842000000000000005000000000610000000314c420000000000000010000000000003000000000000400000000000080000000000004000004350c20000000454042000000000000008000000000000000000254402000000035508200000000000000200000454842000000000000004000000000000100000000000020000000000007
  | 6, 16 => 0x10000000000009000004350c200000004350020000000000000000000000002100000000000000200000000000010000000000001000000140420000000520c52000000000000005000000010c1000000000000002000000000000800000000000030000000000002000000000000100000000000050000045404200000000010010000000454042000000015012200000003504120000000000000000000035440200000000000000200000000000030000000000002000000000000400000000000030000000000005
  | 6, 17 => 0x30000050109200000000000000300000000000030000000000002000000004010000000014042000000025500200000000000000100000000000030000000000004000000000000100000304c02000000000000007000003550820000000000000010000035085200000000000000300000000000000000000000007000000000000000000350852000000000000003000000000000300000350852000000000000001000000000000200000000000030000025500200000000000000300000000000060000000000003
  | 6, 18 => 0x5210d200000000000000200000454c420000000000000060000000000002000000000000300000000000010000000000009000001550020000000000d11010000000000007000000010410000000000000030000000000001000000480e2000000000000008000000000a10000000000000030000000000001000000000000700000001011000000000000001000000000000800000054c42000000000000007000000000000200000250022000000000000000000000000000400000000000050000000000007000000480a200
  | 6, 19 => 0x8000000000000200000001051000000000000003000000590520000000000000010000000000002000000000000300000000000050000000000005000000000000700000000000040000000000005000000000000300000000000050000000000004000003540220000000454c0200000002148420000000000d110100000000000050000000000003000000000000400000000c110000000454022000000045404200000000000000800000000000020000000000002000004050020000000000000070000000000000
  | 6, 20 => 0x4140520000000324c820000000454c820000000000000070000000000002000000000000700000000411000000000000009000000000000200000324c8200000000000000900000454c4200000000000000800000254c420000000000000040000000000003000002148420000000454c42000000000000008000004150420000000058c520000000000000030000025404200000000000000400000000000050000051081200000000000000400000000000050000000000000000000000000300000354842000000000000001
  | 6, 21 => 0x4806200000003550820000000304c02000000045404200000002048020000000000021000000000000003000000000000100000000000040000000000007000000000000400000000000040000000104100000000000000200000000000040000015500200000000000000700000000000020000040505200000000000000100000000000080000000000002000000000000200000054c4200000001540a200000000000000000000314c42000000035041200000000000000300000454c420000000000000030000000000000
  | 6, 22 => 0x354402000000000000000000000000000100000254c42000000000000008000000000000900000000000000000000000002000000000000100000000000070000000000005000000000000200000000c410000000155002000000045081200000000000e100000000000000100000214842000000000000003000000000000700000000000040000052101200000000010d100000000000000900000000000040000000000001000000000000400000000000030000035041200000000000a10000000000000040000000000001
  | 6, 23 => 0x104100000000000000500000054c42000000000000005000003504120000000000000010000000000007000000000000900000000000020000000000008000000000000100000000000030000000000002000003044120000000000000030000000000002000000000000200000454c820000000000000010000000000008000000588020000000000000090000000000004000000000000300000000000030000002802200000000010d101000000000000800000000c01000000000000003000002500e20000000324c8200
  | 6, 24 => 0x4000000000000800000000c110000000000d110100000314c420000000000000000000000000002000000000000100000001011000000000000003000000000a10000000501052000000000000000000000000000200000501092000000000000001000000000000200000434c920000000454c820000000355002000000000000001000000000000900000000000030000000000002000000000000500000514d0200000000000000200000000000020000000000008000000000000500000000000030000000000006
  | 6, 25 => 0x8000000000000200000054c4200000005048420000000320c120000000154c02000000000000003000000000000200000000000030000000000002000000000000800000000c510000000520c120000000454c4200000000000000700000000c41000000000000002000000000000300000000000070000000000009000000000000300000314c420000000450052000000000000003000000000000300000314c42000000000000000000004350c2000000000000002000000000000200000000000070000000000001
  | 6, 26 => 0x1044020000000425082000000045005200000000000000400000000000030000025041200000004350c20000000000000050000045081200000000000000200000000000090000000000002000000000e1000000000000007000000180220000000204802000000045404200000000000000400000000000030000000000004000000000000500000354402000000000000007000000000000400000250062000000000000003000000000000100000000000040000000000009000000000000700000000000050000000000009
  | 6, 27 => 0x100000000000040000000000004000000000000200000354402000000000000007000000000000100000000000020000000000000000000000000700000354402000000000000000000003550820000000000d1101000003544020000000000000020000000000004000000010d101000000000000200000000000040000000000003000000000000300000000000000000000000005000000000000100000000000030000000000003000000000000300000000000020000000000002000000000000900000504c8200
  | 6, 28 => 0x300000255002000000000000008000000000000300000000000030000025440200000001500e20000000000000040000000000001000002048020000000000000020000000000001000004350c20000000355002000000000000003000000000000000000515082000000000000003000000500620000000000000070000000000009000000000000500000000000010000000000006000000000e1000000000000004000000000000100000000000020000005406200000000000000300000000000010000000000003
  | 6, 29 => 0x1000000000000100000000000010000000000004000000000000500000000000040000005840200000000000000400000000000010000000000004000000000000400000304c0200000000000000100000454842000000000084100000000000000100000001001000000035406200000000000000900000000000040000000000005000000000000100000000000040000000000002000004500520000000250412000000000000000000000000000100000000000040000000000003000004350c20000000314c1200
  | 6, 30 => 0x10440200000004350c200000003540a20000000000000010000000000004000000000000500000514d02000000000000007000000000000400000000000050000000000004000000000000100000000000030000000000009000003550020000000415042000000000000002000000000a1000000000006100000000000000300000544c120000000000000020000000000004000000000000000000454c4200000000000000800000000000050000000000005000000000000200000324c820000000000000080000010440200
  | 6, 31 => 0x15500200000000000000500000000000020000000000004000000480e20000000000000020000000000002000000000a1000000000000001000000000000400000000000000000000000008000000000000800000000c01000000000000008000000000000700000000000070000000000006000000000000000000405002000000000002100000000000000300000000000040000000000003000000000000300000000000020000000000009000000000000700000000c0100000000000000300000000000010000000000002
  | 6, 32 => 0x800000000000070000000000002000000000000800000000c9100000000000000400000350852000000051480200000004250820000000000000050000000000004000000000000800000000000010000000000001000000000000200000000d11010000005901200000000000000100000104402000000000000005000000000000300000415042000000000000007000000000000500000000000050000000000003000000000000700000000000030000025440200000000000000300000000000020000025040200
  | 6, 33 => 0x200000000000000000000000004000003550420000000000000050000000000003000000000000200000000000090000004806200000000000000700000000000010000000000002000004050020000000000000010000000000004000004350c20000000000000060000000000004000000000000900000454042000000021484200000000000000300000000000080000000000008000000000000100000000000010000000000000000000000000100000000000010000000000001000000000000000000314c4200
  | 6, 34 => 0x50000045404200000000000000300000000d11010000000000001000000000000400000000000070000000000003000000000000300000000000080000000000008000000000000600000000c01000000040500200000000004110000000320c1200000004050020000000454c42000000000000008000000000000100000000000040000000000002000000000000300000000000020000000000000000000000000700000324c82000000000000007000000000000400000254c42000000000000002000005210d200
  | 6, 35 => 0x380620000000000000010000000000001000002504020000000000000020000000000001000000000000700000000000010000000000003000000000000300000054c42000000000000005000000000000300000000c11000000051081200000000000000400000000000020000050508200000004540420000000000000050000000000001000000000000400000254c420000000250412000000000000003000000500620000000000121000000005406200000000000000200000000c410000000214842000000000000002
  | 6, 36 => 0x25440200000004350c20000000000000040000010440200000004350c20000000454c82000000000000001000000000000400000000401000000010440200000000000000100000000000010000000041100000003540a2000000010440200000000584020000000250412000000015500200000000000000400000000000040000000000007000000000000200000000000040000020480200000000000000100000000000020000001802200000000000a1000000000000000000000000000100000000000000000035508200
  | 6, 37 => 0x2544020000000000000080000000040100000000010d101000000590d200000000000000100000000000010000000000009000000584020000000104402000000000000002000000590d2000000000000001000000000000900000355082000000000000009000000000a1000000000000001000000000000200000254402000000000000006000000000000100000510c1200000000000000500000001041000000000000008000000000000200000000000030000035508200000000000000000000000000090000035041200
  | 6, 38 => 0x2544020000000000000040000000000007000005210d20000000058412000000000000002000000000000200000254402000000035085200
  | 7, 0 => 0x210000000000c410000000001011000000000006100000000004110000000000000010000000000003000000000e1000000000000001000000000210000000000000020000000000001000000000000700000000c410000000000c51000000000000001000000000000100000001001000000000000003000000000000200000000000000000000104100000000000000500000001051000000000012100000000000a100000000000000300000000c410000000000c51000000000081100000000000000100000000c4100
  | 7, 1 => 0x100000001051000000000000002000000001210000000000000010000000108100000000000a1000000000105100000000000e10000000000000020000000085100000000000a100000000010d100000000000000000000000851000000000000002000000000a100000000008010000000000c81000000000006100000000004010000000001091000000000000000000000000000100000000c8100000000000210000000000d01000000000000003000000000000300000000841000000000000001
  | 7, 2 => 0x10000000084100000000000610000000000851000000000012100000000000000100000000000020000000000000000000000000100000000d01000000000000002000000008410000000001081000000000006100000000000410000000001081000000000000003000000000e10000000000c91000000000000003000000008010000000000061000000000000000000000000000200000000000010000000000002000000000a100000000000000100000000c1100000000000210000000000000030000000000003
  | 7, 3 => 0x500000001081000000000000009000000010510000000001041000000000000008000000000000200000000811000000000000002000000000000200000000c410000000000000030000000000001000000000000200000000c11000000000000003000000000000100000000051000000000000002000000000000300000000000010000000000003000000000000300000000000010000000000002000000000000200000000000030000000101100000000000000200000000c510000000000851000000000000001
  | 7, 4 => 0xc1100000000000a1000000000005100000000001210000000000000030000000012100000000000000200000000121000000000002100000000000000300000000401000000000000002000000000000300000000000020000000104100000000000e100000000000000200000000000010000000000001000000000a10000000000c0100000000000000500000000000020000000000001000000008110000000000000030000000084100000000000000000000000c9100000000000000300000000121000000000000002
  | 7, 5 => 0x10000000012100000000000000200000000000030000000081100000000000000500000000801000000000101100000000000000300000000c910000000000c01000000000000005000000010010000000000000090000000000003000000010910000000000c9100000000000e100000000000000100000000401000000000000002000000000a10000000000000000000000000003000000000e1000000000000002000000000000200000000000030000000080100000000010d100000000010d1000000000109100
  | 7, 6 => 0xc010000000000c91000000000000004000000000000300000000061000000000000002000000000000200000000000000000000000001000000000e10000000000021000000000000001000000000000100000000811000000000081100000000000000100000000000010000000000003000000000210000000000c11000000000000003000000010c100000000000000200000000c110000000000c51000000000000003000000000000100000000c41000000000000002000000000610000000000841000000000006100
  | 7, 7 => 0x108100000000000000800000000061000000000000001000000000210000000000000000000000012100000000000000200000000000010000000105100000000000000100000000c8100000000000e10000000000c5100000000008010000000000c4100000000010010000000000d110000000000021000000000000003000000000210000000000021000000000000002000000000a100000000000a1000000000000005000000000000200000000121000000000000007000000000000100000000000030000000000001
  | 7, 8 => 0x10000000006100000000000e1000000000000003000000010c1000000000000000000000000000800000000c8100000000000000500000000061000000000104100000000000610000000000c910000000000000010000000000003000000000000500000001081000000000000001000000004110000000000000040000000100100000000000000300000000851000000000100100000000010c100000000000000100000000000030000000000004000000000e100000000000a10000000000000070000000040100
  | 7, 9 => 0x1081000000000000002000000000610000000000851000000000081100000000010410000000000000010000000012100000000000000300000000121000000000000000000000010110000000000041000000000000001000000004110000000000c0100000000010c10000000000000080000000000000000000000000500000000021000000000012100000000000000300000000c91000000000109100000000010010000000000000080000000000001000000008410000000001081000000000000001000000000a100
  | 7, 10 => 0x1210000000000c010000000000000030000000101100000000010d10000000000000050000000041100000000000a1000000000000008000000008510000000000c810000000000c910000000000000080000000000003000000000000100000000811000000000012100000000010910000000000121000000000000002000000000210000000000000070000000000002000000010510000000000000020000000041100000000000000400000000c51000000000000008000000000e10000000000000080000000000001
  | 7, 11 => 0x1000000000000500000000000030000000101100000000000000000000000000020000000000002000000010d1000000000000003000000000a10000000000000030000000012100000000000210000000000c11000000000105100000000010510000000001051000000000000004000000000000200000000c010000000000c910000000000000010000000000002000000008010000000000000010000000101100000000000000100000000000020000000105100000000008110000000000c81000000000000002
  | 7, 12 => 0x90000000041100000000010d10000000000021000000000000002000000008410000000000000010000000000001000000000000300000001001000000000000003000000010d100000000000a100000000000a10000000000811000000000000004000000010c100000000000e10000000000000010000000002100000000000a10000000000401000000000006100000000010c100000000010d1000000000000001000000000a10000000000c5100000000000000300000000c41000000000100100000000000a100
  | 7, 13 => 0x41100000000000000300000000c8100000000000000700000000000010000000000001000000010c1000000000000002000000001210000000000841000000000000000000000000000300000000000020000000080100000000004110000000000000030000000040100000000000610000000000411000000000000007000000000000200000000000020000000108100000000004010000000000000010000000000003000000000000300000001001000000000012100000000010c10000000001041000000000000005
  | 7, 14 => 0xa100000000000a1000000000000009000000000000200000000c91000000000006100000000000a10000000000c910000000000000030000000041100000000010d100000000000a100000000010110000000000c9100000000010410000000000c010000000000000070000000000002000000000e10000000000000040000000000007000000010110000000000000000000000000003000000000000100000000000030000000084100000000010d10000000000c9100000000010c1000000000000005
  | 7, 15 => 0x401000000000040100000000004010000000000c0100000000010c100000000008510000000000000040000000000000000000010d100000000000a10000000000c010000000000c1100
  | 8, 0 => 0x0
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_5 roots_5 8 s ws hint
  | 1 => checkCutEntry dom_6 roots_6 6 s ws hint
  | 2 => checkCutEntry dom_8 roots_8 6 s ws hint
  | 3 => checkCutEntry dom_9 roots_9 6 s ws hint
  | 4 => checkCutEntry dom_11 roots_11 5 s ws hint
  | 5 => checkCutEntry dom_12 roots_12 5 s ws hint
  | 6 => checkCutEntry dom_14 roots_14 5 s ws hint
  | 7 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 8 => checkCutEntry dom_16 roots_16 5 s ws hint
  | 9 => checkCutEntry dom_4 roots_4 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_17 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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
theorem z3_8 : ∀ i, 8 ≤ i → i < 11 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 8 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 11 → Z 3 i = true := range_split z3_0 (z3_8)
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
theorem z4_48 : ∀ i, 48 ≤ i → i < 53 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 48 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 53 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (z4_48))))))
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
theorem z6_464 : ∀ i, 464 ≤ i → i < 471 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 464 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 471 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (range_split z6_376 (range_split z6_384 (range_split z6_392 (range_split z6_400 (range_split z6_408 (range_split z6_416 (range_split z6_424 (range_split z6_432 (range_split z6_440 (range_split z6_448 (range_split z6_456 (z6_464))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z7_264 : ∀ i, 264 ≤ i → i < 267 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 264 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 267 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (range_split z7_208 (range_split z7_216 (range_split z7_224 (range_split z7_232 (range_split z7_240 (range_split z7_248 (range_split z7_256 (z7_264)))))))))))))))))))))))))))))))))
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

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4243388552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_17.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_17 10 hT6 (by unfold IsConst; decide) low_17

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.and, [11, 9]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_13103_aux

theorem PEqualNP.Outside.L_meta_13103 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4243388552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4243388552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_13103_aux.wit, PEqualNP.Outside.L_meta_13103_aux.wmono, le_trans PEqualNP.Outside.L_meta_13103_aux.wsize (PEqualNP.Outside.L_meta_13103_aux.lower s hs), PEqualNP.Outside.L_meta_13103_aux.weval⟩
