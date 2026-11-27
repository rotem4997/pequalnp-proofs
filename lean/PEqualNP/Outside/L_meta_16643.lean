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

namespace PEqualNP.Outside.L_meta_16643_aux

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

def dom_0 : Nat := 0x33003300
def goal_0 : Nat := 0x32002000
def roots_0 : List Nat := [0x22002200, 0x30003000, 0x33000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(9, 13), (9, 25), (12, 13), (12, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [9, 9, 12, 12, 24, 24]
def r2sG : List Nat := [13, 25, 13, 28, 25, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x2b0ea840
  | 3, 0 => 0x2b0ea840
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3300000000000000300030000000000022002200
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

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
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
def goal_1 : Nat := 0x32222020
def roots_1 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x33003300, 20, 28)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0xff00ff00
def goal_2 : Nat := 0xfa00e800
def roots_2 : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00, 9, 11)] (by decide +kernel) (by decide +kernel) low_0

def dom_3 : Nat := 0xffff
def goal_3 : Nat := 0xe8e0
def roots_3 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_4 : Nat := 0xff00
def goal_4 : Nat := 0xe800
def roots_4 : List Nat := [0xaa00, 0xcc00, 0xf000]

theorem low_4 : Lower dom_4 roots_4 goal_4 4 :=
  lower_iso [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_5 : Nat := 0xff00ff
def goal_5 : Nat := 0xea00e0
def roots_5 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

namespace S_5
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (2, 6), (3, 7), (3, 19), (4, 5), (4, 6), (16, 17), (18, 19), (18, 22), (20, 21), (20, 22)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 4, 4, 16, 18, 18, 20, 20]
def r2sG : List Nat := [5, 17, 6, 7, 19, 5, 6, 17, 19, 22, 21, 22]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_5.map (· &&& dom_5)
def goalM : Nat := goal_5 &&& dom_5
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x678b910d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000f000f00000000000cc00cc0000000000aa00aa
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_5 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_5 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_5 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_5 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_5 roots_5 goal_5 4 := by
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

theorem low_5 : Lower dom_5 roots_5 goal_5 4 := S_5.noCircuit

def dom_6 : Nat := 0xffffffff
def goal_6 : Nat := 0xfaeae8e0
def roots_6 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_6
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (2, 6), (3, 7), (3, 11), (3, 19), (4, 5), (4, 6), (9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (12, 13), (12, 14), (12, 28), (16, 17), (18, 19), (18, 22), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 3, 4, 4, 9, 9, 9, 10, 10, 12, 12, 12, 16, 18, 18, 20, 20, 20, 24, 24, 26, 26]
def r2sG : List Nat := [5, 17, 6, 7, 11, 19, 5, 6, 11, 13, 25, 11, 14, 13, 14, 28, 17, 19, 22, 21, 22, 28, 25, 28, 27, 30]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_6.map (· &&& dom_6)
def goalM : Nat := goal_6 &&& dom_6
def NN : Nat → Nat
  | 3 => 4
  | 4 => 20
  | 5 => 40
  | 6 => 11
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x8da2fce54f26fc414dcac31014f4229e
  | 4, 0 => 0xedfd1401cfa1a29dc94d0e65b403438db07c00eda2da0da4a012de35994494eb896b0e1f6623f80a59e6725d5560996149d3b16c352865b22cce9c262637312d1a0e38881824abc917ce4a020f22775b
  | 5, 0 => 0xf27aa6a5e1005450d75027cad051f507cfa1a29dbc1d98f3b2878a8aa6753a59a3e82e789e9267f79a4132f27cbf7665755161bc6f1d831c6bff23c8636295b562f275ca560409b853baf88c537bfbe74ca624074b2652af4166ee5a410f07923a6b8d41361753d62637312d2616908a25e0cf66206585ea1ac7d7cf18c41cbb1863781a161726e41604e97e148cee9c13b8d5b712530086074368e800b965fd
  | 6, 0 => 0xf27aa6a5d051f507ce00c9b9be3fb924ac05225e8c616cec818360613a6b8d41276bea4325303d37206585ea
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x333333330000000011111111000000000f0f0f0f00000000050505050000000000ff00ff000000000000ffff00000000000055550000000000003333
  | 0, 1 => 0xaaaaaaaa00000000aaaaa0a000000000aaaa888800000000a8a8a8a800000000a0a0a0a0000000005f5f5f5f00000000555555550000000050505050
  | 0, 2 => 0xeeeeeeee00000000eeeeecec00000000ecececec00000000e0e0e0e000000000dddddddd00000000cccccccc00000000c8c8c8c800000000afafafaf
  | 0, 3 => 0xfafa000000000000faf0faf000000000fa00fa0000000000f0f0f0f000000000f0f0e0e000000000f0f0c0c000000000f0f0a0a000000000f000f000
  | 0, 4 => 0xffa0ffa000000000ff00ff0000000000ff00cc0000000000ff00aa0000000000fefefefe00000000fcfcfcfc00000000fc00fc0000000000fafafafa
  | 0, 5 => 0xfffffcfc00000000fffff0f000000000ffffcccc00000000ffffaaaa00000000ffffa0a000000000ffff555500000000ffff050500000000ffff0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xae7812491c48e4ae6815499f44b4
  | 4, 0, 0 => 0xa278122d689a048e5a207522d6b9a048f5a257173d6999c48f5ae77123d6899b48f5ae68122d6899c5cd5a267163d689a048b5ae67153d6681f48b57dd7123d667dc44f5
  | 4, 0, 1 => 0xa268943d6b99c48f5a26717316885c5cf5
  | 5, 0, 0 => 0x2899c4895a2679c48f60289a048b5ae899c48f602875c48f5a2681c48f60287122435a2671348f6a2671a48f6ae67123cb6b6899c5cf6a267123c86a267123ca69a07dc48f6be899c48f6a2671948f6
  | 5, 0, 1 => 0xa267123c66a268dc48f6a2075c48f6a277123cb6a267123c06a267123ce602885c48f5b6895c48f6a2671240f6a267123c16a2285c48f6026712242502899c2475ba89a048f602895c48f5aa899c48f6
  | 5, 0, 2 => 0xa267123cb6028992245502670f1c25a267123c9602b99c48f5a268123cb6a267123c46bac99c48f6
  | 6, 0, 0 => 0xa267123cb6a267123c96b6899c48f602899c3c7502899c48f50287123c35ba899c48f602899c4895b2899c48f6a2671848f6a2681c48f6
  | 7, 0, 0 => 0x2899c48f5
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
  | 0, 0 => 0x3e79f0cf9e0c0f1c7cffc718040fc03fc00ffff003e31000e7c3
  | 0, 1 => 0x1cec00000000000e00000380000003fffffffffe31038e0c0
  | 0, 2 => 0xc187cff06183cc1860f0000000fffe3f306183c00000e3c71f3f
  | 0, 3 => 0xe0000038e7c00039c0038e0c00e000003800000e0000000e000
  | 0, 4 => 0xf03fc03c0ff00f006003c00700cfbffff3ef8fcc03e00038e7fb
  | 0, 5 => 0xfffe3f3ffe0c0ffc60f3ff073bffc0003fff8c4ffc6013ff0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3a6990ca0800050c34c800000007c03bc007bdd0014210002241
  | 0, 1 => 0x52cbded4b266b52c34e90a2b790208927f7ddb6ad34212b4d084
  | 0, 2 => 0xd7dffff5f7fffc79eff61c72cdedb66f31659bcc5966f14b2f7b
  | 0, 3 => 0xffe108bfcffddf83fc42bcf2cdaf3cb36bcd08caf28926a0f200
  | 0, 4 => 0xfa3fd67e0ff10f837443e0af10fffffffbefbfde83ec43ffffff
  | 0, 5 => 0xffffffffff6effff76fbffaf7bffe99afffd4a6ffe108bff8422
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
  | 4 => 25
  | 5 => 58
  | 6 => 8
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xfaaf4652f27b02cce073355eca894aa8b0acf07db0288a63ac05225ea3cc7a0e8fe29d1d878a975673ae8cf7729d58de622d3a095acfdee34f2ebdfa4d7cb1de491657893b937b233649f21e32bc99003239f07b2720edd825e0cf661d34fcbf054298b8
  | 5, 0 => 0xe67e8438e457f490e0bddffaddc4e51ed83a9daad6f33033ce00c9b9caba06d6c56e12e7c05b96d6be3fb924bb95578cba7741d8b6da7f65b5a2e9c5ac05225eaa2945419e9c03b29bd16d7495c361688c616cec8aa6652c81836061814b23f77a3e5c567a3d427471f3b0a45e1d4aa8554c825e526e44fc42897f173d43b4583acce27d3903b3463739cd823649f21e30706e422fe12a1b29ed978a276bea43262ad7ad25303d3724e2e5ac22894d3420d33bcc1d34fcbf1be300d41b8a7ef114e5b48712fe2d5b126b25b70fd672800de1e4bc0ad7cab808dabbe6067329db034963b10241d3e1
  | 6, 0 => 0xe0bddffaba7741d8aa294541554c825e30706e421b8a7ef1126b25b70241d3e1
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x532040000002000000481000000140000000000000000000004481000000140000132040000001000004c810000000000001000008000050000140000500000000002
  | 5, 0 => 0xc00001000008000001344040000200000800004210400000010000000000000000400002000000000010000000000000000800000000000000020000100000000000000001000014000010000040000200000400002
  | 5, 1 => 0x1400002000004000000000140000100000000001000000000040000000000000000000005000000000000000040000400000400003000004000010000080000200000800005
  | 6, 0 => 0x400000000004000020000040000200000000002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 3 => checkCutEntry dom_4 roots_4 4 s ws hint
  | 4 => checkCutEntry dom_0 roots_0 4 s ws hint
  | 5 => checkCutEntry dom_5 roots_5 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_6 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_6 == dom_6) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_6 goalM u ys) : RunD dom_6 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_6 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
theorem z5 : ∀ i, 0 ≤ i → i < 40 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (z5_32))))
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
  scr dom_6 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_6 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_6 roots_6 goal_6 8 := by
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

theorem low_6 : Lower dom_6 roots_6 goal_6 8 := S_6.noCircuit

def dom_7 : Nat := 0x3300330000000000
def goal_7 : Nat := 0x3200200000000000
def roots_7 : List Nat := [0x2200220000000000, 0x3000300000000000, 0x3300000000000000]

namespace S_7
def pairsG : List (Nat × Nat) := [(41, 45), (41, 57), (44, 45), (44, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [41, 41, 44, 44, 56, 56]
def r2sG : List Nat := [45, 57, 45, 60, 57, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_7.map (· &&& dom_7)
def goalM : Nat := goal_7 &&& dom_7
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x833d6492
  | 3, 0 => 0x833d6492
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x330000000000000030003000000000002200220000000000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_7 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_7 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_7 == dom_7) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_7 goalM u ys) : RunD dom_7 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_7 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_7 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_7 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_7 roots_7 goal_7 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_7 goal_7 := by
    have h0 : isConstB dom_7 goal_7 = false := by decide +kernel
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

end S_7

theorem low_7 : Lower dom_7 roots_7 goal_7 4 := S_7.noCircuit

def dom_8 : Nat := 0x3333333300000000
def goal_8 : Nat := 0x3222202000000000
def roots_8 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3300330000000000, 52, 60)] (by decide +kernel) (by decide +kernel) low_7

def dom_9 : Nat := 0x5555555500000000
def goal_9 : Nat := 0x5440444000000000
def roots_9 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0x5555000000000000
def goal_10 : Nat := 0x5440000000000000
def roots_10 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

def dom_11 : Nat := 0xffff000000000000
def goal_11 : Nat := 0xfeea000000000000
def roots_11 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_10

def dom_12 : Nat := 0xff00ff0000000000
def goal_12 : Nat := 0xfe00ec0000000000
def roots_12 : List Nat := [0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xffff00000000
def goal_13 : Nat := 0xece000000000
def roots_13 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]

namespace S_13
def pairsG : List (Nat × Nat) := [(33, 37), (34, 38), (34, 42), (35, 39), (35, 43), (36, 37), (36, 38), (40, 42), (41, 43), (41, 45), (44, 45), (44, 46)]
def r1sG : List Nat := [33, 34, 34, 35, 35, 36, 36, 40, 41, 41, 44, 44]
def r2sG : List Nat := [37, 38, 42, 39, 43, 37, 38, 42, 43, 45, 45, 46]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_13.map (· &&& dom_13)
def goalM : Nat := goal_13 &&& dom_13
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x5e2aba2c
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000f0f0000000000000cccc000000000000aaaa00000000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_13 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_13 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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

def dom_14 : Nat := 0xff00ff00000000
def goal_14 : Nat := 0xea00e000000000
def roots_14 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13

def dom_15 : Nat := 0xffffffff00000000
def goal_15 : Nat := 0xfeeaece000000000
def roots_15 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

namespace S_15
def pairsG : List (Nat × Nat) := [(33, 37), (33, 49), (34, 38), (34, 42), (35, 39), (35, 43), (35, 51), (36, 37), (36, 38), (40, 42), (41, 43), (41, 45), (41, 57), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [33, 33, 34, 34, 35, 35, 35, 36, 36, 40, 41, 41, 41, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [37, 49, 38, 42, 39, 43, 51, 37, 38, 42, 43, 45, 57, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_15.map (· &&& dom_15)
def goalM : Nat := goal_15 &&& dom_15
def NN : Nat → Nat
  | 3 => 1
  | 4 => 2
  | 5 => 17
  | 6 => 9
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x976d2e84
  | 4, 0 => 0xede4ed110a607b65
  | 5, 0 => 0xeea07002e139fe35d71579e4cd07a878cce3300ebc17d563b8694a068f0d19b08986d9d561cc1db65afe2727550aef012830407a24bb21a715350e9c0467640c0433e158
  | 6, 0 => 0xeea070028f1909028986d9d57523d75b608578e95fcdfb9d5f5ce351527e0458059706fd
  | 7, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaaaaaa000000005555555500000000333333330000000011111111000000000f0f0f0f00000000030303030000000000ff00ff000000000000ffff00000000
  | 0, 1 => 0xfafafafa00000000fafa000000000000f0f0f0f000000000f0f0000000000000eeeeeeee00000000e0e0e0e000000000cccccccc00000000afafafaf00000000
  | 0, 2 => 0xffff000000000000fff0f0f000000000ff00ff0000000000ff00000000000000fefefefe00000000fcfcfcfc00000000fcfccccc00000000fc00fc0000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xab9494
  | 4, 0, 0 => 0x2f57a92b7835675
  | 5, 0, 0 => 0xbd66d49daf56a927605ead31540d49c205bd5a941d81569ca05055cd49d6f56a4e36bd5a939181749c615bdaad49daf56a4e26bd62d49daaf73527605ea930d6f57b5696
  | 5, 0, 1 => 0x17aa4e35
  | 6, 0, 0 => 0x17aa4e35bd64d49daf56a4e3605ead4994156a4e05bd5ac49d817ab5275bd5ab49daf5a35276
  | 7, 0, 0 => 0x17ab5275
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
  | 0, 0 => 0x71cfffe38cfc7fe0ff1e380e3c79ff811e031fc07fc00ffff
  | 0, 1 => 0x1c3f7cc7000001c3860070000003871fc00000003801f38f1e7f
  | 0, 2 => 0xffc0003f0e180e03f8038000001fbf7fc7ee1fc1f801f000e000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x24cf3cf6cc30cb46e20e40800062c59a88110020dc075c006fbd
  | 0, 1 => 0xbdff7def790429d3a6567480006fdfffc3469954b91df19b3efb
  | 0, 2 => 0xffe410bfcf995f23f8a3c89000fffffff7eeffddfb1df348ee28
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 24 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 24 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 24 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 24 then wireAt i else 0
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
  | 4 => 10
  | 5 => 53
  | 6 => 10
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xd2568d6ea1c0b9c783cbecbb6a8753ee657f8e1b643ce6935f5ce35128ba648d288e1adb0467f571
  | 5, 0 => 0xfb45fe20f8694079dc1b0d52ccf2db85c7faffd0c2a50a77beede581ad4120b7a4918cb097711ee79346a38b8f1909028be00848877482d886cfb07d7d657ff377dc40c77523d75b71cd33b46df5855968d494196259fa14608578e95fcdfb9d5f5ce3515f2e44265b53380654386dd3527e04584fbea8484906851945c2944c3c4159333a877c60358964b82f5e14ef2c86160f2c1e54252b87dba629d28c3728ce4bfb273b926c239e6b9322e2bbd21f18b64d1dcf210319eda9ec1407618e12c2aa9a127d1d85080fb46f059706fd003b0799
  | 6, 0 => 0xccf2db85a4918cb086cfb07d7d657ff34fbea8483c415933358964b82f5e14ef273b926c1dcf2103
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x3104040000221040084100000004000010000000000600001c00003
  | 5, 0 => 0x4000020000080000000001000001000000000000000000000200000c000020000000000000000000000000010000050000080000100000800005000018000070000000000300000c0000320440800000000008c4101
  | 5, 1 => 0x200000000000000008000060000180000100000c00000000008000030000000000723040000001000000000030000044110300001400001
  | 6, 0 => 0x80000300000400000000008000020000000000000000800000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_8 roots_8 5 s ws hint
  | 1 => checkCutEntry dom_9 roots_9 5 s ws hint
  | 2 => checkCutEntry dom_11 roots_11 5 s ws hint
  | 3 => checkCutEntry dom_12 roots_12 5 s ws hint
  | 4 => checkCutEntry dom_10 roots_10 4 s ws hint
  | 5 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 6 => checkCutEntry dom_13 roots_13 4 s ws hint
  | 7 => checkCutEntry dom_14 roots_14 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15 == dom_15) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15 goalM u ys) : RunD dom_15 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_16 : ∀ i, 16 ≤ i → i < 17 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 16 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 17 → Z 5 i = true := range_split z5_0 (range_split z5_8 (z5_16))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_8 : ∀ i, 8 ≤ i → i < 9 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 8 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 9 → Z 6 i = true := range_split z6_0 (z6_8)
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
  scr dom_15 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_15 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15 roots_15 goal_15 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_15 goal_15 := by
    have h0 : isConstB dom_15 goal_15 = false := by decide +kernel
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

end S_15

theorem low_15 : Lower dom_15 roots_15 goal_15 8 := S_15.noCircuit

def dom_16 : Nat := 0xff000000ff00
def goal_16 : Nat := 0xec000000e800
def roots_16 : List Nat := [0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff0000000000, 10, 42)] (by decide +kernel) (by decide +kernel) low_4

def dom_17 : Nat := 0x5500550055005500
def goal_17 : Nat := 0x5400440050004000
def roots_17 : List Nat := [0x4400440044004400, 0x5000500050005000, 0x5500000055000000, 0x5500550000000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14

def dom_18 : Nat := 0xf000f000f000f00
def goal_18 : Nat := 0xe000c000a000800
def roots_18 : List Nat := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 4 :=
  lower_iso [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14

def dom_19 : Nat := 0xff00ff00ff00ff00
def goal_19 : Nat := 0xfe00ec00fa00e800
def roots_19 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

namespace S_19
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (10, 42), (12, 13), (12, 14), (12, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (40, 42), (41, 43), (41, 45), (41, 57), (44, 45), (44, 46), (44, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [9, 9, 9, 10, 10, 10, 12, 12, 12, 24, 24, 26, 26, 26, 40, 41, 41, 41, 44, 44, 44, 56, 56, 56]
def r2sG : List Nat := [11, 13, 25, 11, 14, 42, 13, 14, 28, 25, 28, 27, 30, 58, 42, 43, 45, 57, 45, 46, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_19.map (· &&& dom_19)
def goalM : Nat := goal_19 &&& dom_19
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x287f8e3c27f195c0
  | 6, 0 => 0xc22d231e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff0000000000ff000000ff000000fa00fa00fa00fa00f000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa005500550055005500
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xd634586ad05
  | 6, 0, 0 => 0x6ad15
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffc000e03e001f81c71c01c0003838038007fc7ff8
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xffe020f23f04bf9fdf9d15d248f8b9278a4fd875b0
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
  | 4, 0 => 0xcdf81260c75c54eec22d231e0a1bf3fa
  | 5, 0 => 0xe035bfc0d9937660cde8d0adc22d231ea5c90d36964e51979192a4a6825f7dc67ef3d89f7a5e75657771784875db05a76d93d5d36b383860686746ca5962781e49ab9434440a9ef93d53052735dec3a92dda33ed2b5ada051689962c11f32cff
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0xc0000200000000000
  | 5, 0 => 0x2000000000000000080000000000800000000010000000000080000200001000004000000000030000140000100000c000000000100000200000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_12 roots_12 5 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_16 roots_16 5 s ws hint
  | 3 => checkCutEntry dom_17 roots_17 4 s ws hint
  | 4 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 5 => checkCutEntry dom_18 roots_18 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_19 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_19 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_19 == dom_19) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_19 goalM u ys) : RunD dom_19 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_19 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_19 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_19 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_19 roots_19 goal_19 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_19 goal_19 := by
    have h0 : isConstB dom_19 goal_19 = false := by decide +kernel
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

end S_19

theorem low_19 : Lower dom_19 roots_19 goal_19 7 := S_19.noCircuit

def dom_20 : Nat := 0x5555000055550000
def goal_20 : Nat := 0x5440000050400000
def roots_20 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]

theorem low_20 : Lower dom_20 roots_20 goal_20 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9

def dom_21 : Nat := 0x5555555555555555
def goal_21 : Nat := 0x5440444050404040
def roots_21 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_21 : Lower dom_21 roots_21 goal_21 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000055550000, 12, 28)] (by decide +kernel) (by decide +kernel) low_20

def dom_22 : Nat := 0xffff0000ffff
def goal_22 : Nat := 0xece00000e8e0
def roots_22 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_22 : Lower dom_22 roots_22 goal_22 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff00, 3, 11)] (by decide +kernel) (by decide +kernel) low_16

def dom_23 : Nat := 0xffff0000ffff0000
def goal_23 : Nat := 0xfeea0000faea0000
def roots_23 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_23 : Lower dom_23 roots_23 goal_23 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa0000, 16, 17)] (by decide +kernel) (by decide +kernel) low_20

def dom_24 : Nat := 0xc0c0c0c0c0c0c0c
def goal_24 : Nat := 0xc080c0008080800
def roots_24 : List Nat := [0x808080808080808, 0xc000c000c000c00, 0xc0c00000c0c0000, 0xc0c0c0c00000000]

theorem low_24 : Lower dom_24 roots_24 goal_24 4 :=
  lower_iso [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18

def dom_25 : Nat := 0xf0f0f0f0f0f0f0f
def goal_25 : Nat := 0xe0a0c000a0a0800
def roots_25 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_25 : Lower dom_25 roots_25 goal_25 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c, 9, 11)] (by decide +kernel) (by decide +kernel) low_24

def dom_26 : Nat := 0xcccccccccccccccc
def goal_26 : Nat := 0xccc8ccc0c8c8c8c0
def roots_26 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

theorem low_26 : Lower dom_26 roots_26 goal_26 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c0, 2, 6)] (by decide +kernel) (by decide +kernel) low_24

def dom_27 : Nat := 0xffffffffffffffff
def goal_27 : Nat := 0xfeeaece0faeae8e0
def roots_27 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_27
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (2, 6), (3, 7), (3, 11), (3, 19), (4, 5), (4, 6), (9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (10, 42), (12, 13), (12, 14), (12, 28), (16, 17), (18, 19), (18, 22), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (33, 37), (33, 49), (34, 38), (34, 42), (35, 39), (35, 43), (35, 51), (36, 37), (36, 38), (40, 42), (41, 43), (41, 45), (41, 57), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 3, 4, 4, 9, 9, 9, 10, 10, 10, 12, 12, 12, 16, 18, 18, 20, 20, 20, 24, 24, 26, 26, 26, 33, 33, 34, 34, 35, 35, 35, 36, 36, 40, 41, 41, 41, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 17, 6, 7, 11, 19, 5, 6, 11, 13, 25, 11, 14, 42, 13, 14, 28, 17, 19, 22, 21, 22, 28, 25, 28, 27, 30, 58, 37, 49, 38, 42, 39, 43, 51, 37, 38, 42, 43, 45, 57, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_27.map (· &&& dom_27)
def goalM : Nat := goal_27 &&& dom_27
def NN : Nat → Nat
  | 4 => 2
  | 5 => 35
  | 6 => 180
  | 7 => 209
  | 8 => 25
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x465796850278229b
  | 5, 0 => 0xff7c7d93fd77e23ffa26367ef7ea4fbaf2e48660f1275cb5ee7d4306ed5c38c6e130803eddc8baeed8102e57cf5af697c3e11b77bfcfc0079dfdf3cd95888eb391fad252815c694d71a3faaf6dc9f3016d6a8de86a105c9f646c71d46339934e5fd25c015e2d8aab5944bef95890abe3575cf6e745b502543782b0fe3086926322f2e8101ed15b31024944bd
  | 6, 0 => 0x5b00c40759254669576611cb56488c3a55f9c36e55739b7c5361a4324fbec2eb4f526fbe4efcd55e4ddb76074bd118f54700cb0e45a7f59843ad14693fd2f7ef3e69a4d83e0fc03d3b754d6439310451360d07b935f43fbe32eb626b2f81a0e12f2d39052b35846d2ad9fd9b29025cbe28e1d56327d2a87725e030e425dc2a2825c5c2a2250b3e6a23fc45a221bde807205b0a2a1fc4f9a61e9a7a0a1dbe4d991d66c50e1c96ea491b3c1cc21b16f5ed19ba301a1956d57318e16a7f18c4770b188f92a41883498817ce2ba216dbf17015fc5b6615c3143a14e0d35f129b996a11408e9a107205040cc62e6c09e9743d0919997805d4ab0b02eac56702e8a90d
  | 6, 1 => 0xb7784d34b4a8fae1b3f19d82b36d3a2db34ae530b2c0fc52b222061fb1eb36f8b03615abafbb0ccdacb74da7aae79678a98e4816a7853e24a748d152a550f087a3744415a2efe0c0a21b0ffea0607bea9af9d283985600c597a0022594dcea6494d417ce9381e4a09022657e8d9b3a468cfa91f68cc6a3578c67854a8c51c7138a0b34fc89a8e63589a86b2587e13aa08756c6388660afd384dec8e884d9addf8320fd1b82673617818c8a248069eaef7abeb30b7a67caff7a0a9b177917ae7177e0dac776b9c58c768e81ea74cf39e4737d02ed727253ef6f9599c06d9445326cc7f9b76a41599e6896eaea6741623a63c9dda3607f3e8c600139515cbe4b0e
  | 6, 2 => 0xff84627aff2325bafe4b532dfd75c11dfaab44fcf69357a9f6535463f6281cb5f3ef218bf3dd72f6f1914f74f052953befc2e112ef885172ed86fa4eeb93c63beb121e74e6dfa69ee504ee61e2f6af66e1151f08dff3a4ccdff2e4cfd97fc822d9719f58d8c9c9e2d79dcf25d76d9a26d612c66fd2eb9853d26d319fd1879d90cf1993fdcc7593fecbd5b4f2cb5a385fc9997d21c9760326c91c5dc6c8a7981ec842caacc70560b5c63e4d23c4f7a12bc4e47f86c2a091e1bc84df1cbb897c82bab9a1bdb99d8907b90dc9b5b7dce78e
  | 7, 0 => 0x4fb2394c4f943bc44e2ce2974dc27b5b4d1acf0f4d17706a4cd8ba054c1e35cd4bff26be4b0c2c39499b08ca49226c8f48f0bd7d45d91ef14305883641a4b5d6410d76963ee6de3d3c9d75a23c39fd5e3c21f90f3a8b1a65387c221636c744ae366fa272359f67e7358e7c1333d93c6b339be83032e64fc532ba82ac3264f1943129ad3f2ea0b9112c50f8382b81626d2b698d6c2a6cf07128a4a83e2889888f265363bb264ea121258a6ea423e92d12233e5198223682592219ec0a21e9d24d2014c6441fb72b911f3d31db1ca0b1831bea35011b52f3321a4058c31232479711eb7ccf0f79f41c0e7dd0190d9cbe430d9a923706291d83059e8b1701a603fb
  | 7, 1 => 0xa25e4bf1a00d2aa29db654639da1794d9c48de239aec1f2b996c23f4989a692797a4f3879710a458944ede00929a9c84926d751e9117715e906d26118f7fd14d8e7679718e35cdb08df2ab598d5eaaf98a81f0ca8968a0cb877910e2872610b8850f030e838341f4827639727f1797dc7ebd26667e05acff7dfd47397db173387c0721267b4614867ab2c9087a2bf43679e15a287900675a752d3810749b988673227b8e706753917005f1236d483b2f6bed6d236b6909ce6b46b4d16adde2696a7ff66869c0add469b2eaed63669d9563353df461aa33685d7bf2db5d6275f45aa8a6b9567ee6cd56403068556f06955342fdb7523dc21151099cc650013940
  | 7, 2 => 0xeef3064dee1e2c58ee185818ec164c1ee9b38944e73f702ce606f433e4625a30e45c7de4e2e453e9e21fca1de1283faadfb32b5bdf91a28ddf6d0221de7f8515ddd7f9c9dd0995b1dcd6712cd9b9b7a8d96359b3d7c0c947d3fa20bfd3a21f4ed0e5095fd0dd3a20cf9551ebcea2794cca35eab9c8d8951dc7d3f23bc7466283c6398efac576ef75c33e8ebcc3334588c07ccfeebeb2f988bea336b7bde1cfb5bc545819bc18011abbec3344b85c2f59b7610a65b55b444cb37ef559b24f00d3b0e1dcffb07bc511ace974c5a98e4816a909e4c1a8e78fc4a8d9852aa840633ca80fa957a77ce252a6910249a5d7b751a4dede88a4a02823a499e38aa494c22f
  | 7, 3 => 0xffcceadcff939ceffe809189fe5cb65dfac274d4faba4034f8327782f6e94291f6657479f6655c2cf5210d0ef34c8d5af30eb1d1f15afe71f109fd47f053c1fdefc2e112
  | 8, 0 => 0xd1efb8f3c2afde01b6be7634b47be621a6563cc3a1f16def9b34b1218ab84b5d8a7994f87f4590c97cea112d76f0de33705b5d9f5fbac6fd5cde0cce55df5df85059633d4f8c57c234064f6c2efbd9641b78d4bc1561a43a1142fa410e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x30f030f030f030f03030f0f03030f0f030303030303030300ff33ff00ff33ff00ff00ff00ff00ff0055555500555555000f0f0f000f0f0f0000ffff0000ffff
  | 0, 1 => 0xa0a0a0a0a0a0a0a07070707070707070555055505550555050f050f050f050f050555550505555505050f0f05050f0f050505050505050503ff03ff03ff03ff
  | 0, 2 => 0x111133331111333311111111111111110fff0fff0fff0fff0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0c
  | 0, 3 => 0x33333333333333333333000033330000303030303030303022222222222222221515151515151515131313131313131311551155115511551111555511115555
  | 0, 4 => 0xa0a0a0a0a0a0a0a09999999999999999888888888888888855555555555555555500550055005500545454545454545450505050505050504444444444444444
  | 0, 5 => 0xafaf0f0fafaf0f0fababababababababaaaaaaaaaaaaaaaaaaaa0000aaaa0000aa00aa00aa00aa00a8a8a8a8a8a8a8a8a5a5a5a5a5a5a5a5a0ffa0ffa0ffa0ff
  | 0, 6 => 0xcccc0000cccc0000cc00cc00cc00cc00c8c8c8c8c8c8c8c8c8c8c0c0c8c8c0c0c3c3c3c3c3c3c3c3c0c0c0c0c0c0c0c0babababababababaafafafafafafafaf
  | 0, 7 => 0xeca0eca0eca0eca0ec00ec00ec00ec00eaeaeaeaeaeaeaeaeaeac0c0eaeac0c0eaea0000eaea0000e0e0e0e0e0e0e0e0cfcfcfcfcfcfcfcfcccccccccccccccc
  | 0, 8 => 0xeeeeeeeeeeeeeeeeeeeecccceeeecccceeeeaaaaeeeeaaaaeeee0000eeee0000eecceecceecceecceeaaeeaaeeaaeeaaee00ee00ee00ee00ecececececececec
  | 0, 9 => 0xfaaa0000faaa0000fa00fa00fa00fa00f8f8f8f8f8f8f8f8f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0f00000f0f00000f000f000f000f000
  | 0, 10 => 0xfc00fc00fc00fc00fc00cc00fc00cc00fafafafafafafafafafaf0f0fafaf0f0fafaaaaafafaaaaafafa0000fafa0000faf0faf0faf0faf0faaafaaafaaafaaa
  | 0, 11 => 0xfe00fc00fe00fc00fcfcfcfcfcfcfcfcfcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfca8a8fcfca8a8fcfc0000fcfc0000fcf0fcf0fcf0fcf0fcccfcccfcccfccc
  | 0, 12 => 0xfefefafafefefafafefe0000fefe0000fefafefafefafefafef0fef0fef0fef0feaafeaafeaafeaafeaafc00feaafc00feaa0000feaa0000fe00fe00fe00fe00
  | 0, 13 => 0xff00ff00ff00ff00ff00f000ff00f000ff00cc00ff00cc00ff00aa00ff00aa00ff000f00ff000f00ff000000ff000000fefefefefefefefefefefcfcfefefcfc
  | 0, 14 => 0xffff0505ffff0505ffff0000ffff0000fffafafafffafafafff0fcf0fff0fcf0fff0faf0fff0faf0fff0f0f0fff0f0f0ffccccccffccccccffaaaaaaffaaaaaa
  | 0, 15 => 0xfffff000fffff000ffffeaeaffffeaeaffffccccffffccccffffcc00ffffcc00ffffc0c0ffffc0c0ffffaaaaffffaaaaffffa0a0ffffa0a0ffff0f0fffff0f0f
  | 1, 0 => 0xffffffff00000000fffffc00fffffc00fffff0f0fffff0f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x827a6f5e3c5828076573d5
  | 5, 0, 0 => 0x826f5e52322d6827a6f4c3c38682766f5955476827a574c382c682765950382d6826f524c3d3860082766f4c265826f52383527682766f543d386008276574c3d582766f5e3c2d682807657322d6826f5b4c382c6826f55524c4060082766f382958261574c382d6
  | 5, 0, 1 => 0x826f55523a38682765754382d6827e6f4c3b3868276604c352d68276624c382d682766f553829682765f54382d6827a6f5e322c68260524c382d682766f68342d68276574c3d2d6826f523a382d6008276573a2d58280766f5e3d682766f553f3860082766f332d5
  | 5, 0, 2 => 0x826f524c47356827657322d2a68257524c382d6
  | 6, 0, 0 => 0x82766f554c40682766f54382d14782766f554c3d387827a766f504c38782766f4c382d0b70082766f4c2d1a60082766f462d146826f555452382d782766f5538352770082765e57322d60082574c382d00600827657382d1460082382d14030060082765948382d68276574c382d00782766f6854382d7
  | 6, 0, 1 => 0x82766f5e55322d70082766f5e3a2d68276574c382d247826f524c38352d782766f5e5a322d7826f524c382d14782766f54382d1f782766f4c38312d7008276574c2d1f600824c2d1f030060082786f382d12682766f5b4c382d70082762d1f140368276574c382d2a700826f524c3824682766f4c403e2d7
  | 6, 0, 2 => 0x826f524c47382d700827c6f382d14682766f4c382d0d78276746d4c382d782766f54382d0a7008276574c472d682766f4c382d0a7827659574c382d70082766f5e3224682766f4c382d06782766f4c382e2d70082764c382d28682766f5538362770082794c382d03682766f634c382d7826f524c382d1f7
  | 6, 0, 3 => 0x826f66554c382d700826f4c241f00682766f4c3d3b3870082766f241f14682766f553a382d78276756f4c382d7828076574c382d7828176574c382d782766f5e4c3d2d7827a76574c382d70082764c402d0360082764c382d04600826f55523827600826f3824140060082766f382f2d68276704c38362d7
  | 6, 0, 4 => 0x82766f4c382d077008276564c382d682766f5e322d0070082766f47251460082766f542d1f600826f4c3d380060082766f3d3814682766f5438342d782766f4c3c382d70082766f55271f682766f4c3d3800700826f52382d1468276574c382d2c7827e766f4c3d3870082764c382d08682776f4c382d097
  | 6, 0, 5 => 0x827a6f4c382c147826f5e524c382d782766f4c3d3824782766f5d55382d7827660554c382d782766a594c382d782796f4c38362d782766f4c382d0270082766f4c381b682766f5e54382d782766f674c382d700826f5e322d00600826f524c2d1f60082766f382d0a682766f574c472d782766a4c47362d7
  | 6, 0, 6 => 0x82766f55382709782766f554e382770082766b382d14682806a4c38362d782766f554c45387826f55524c4738782766f5e322d247826f524c38322d78276736f4c382d782766f4c382d017827a6f4c382c1f782766f5438322d782766f5e322d2a782766f4c382d0c7008276574c322d682766f5955382d7
  | 6, 0, 7 => 0x82766f554c47357827a766f4c3d387826f524c382d097826f524e4c382d7826f69524c382d70082796f382d146827657554c382d78276726f55382d782766f4c382d1870082766f4c2d17682765a574c382d782766f4c40362d782766f4c382d09700826f2d1f1400682766f5e51382d7008276584c362d6
  | 6, 0, 8 => 0x8276746f4c382d782766f4c3d382c782766f644c382d782766f594c472d78276504c38362d78280766f5e322d70082796f4c2d1f6008276604c382d6008276714c362d6827a766f5e322d700827b6f382d146008276574c3824600824c3824030060082766f392d1068280766f4c3d387008276382414036
  | 6, 0, 9 => 0x82766f382709682766f4c3f382d70082766d4c2d1f682766f4c382d19782766f4c382d1370082766f402d14682766f554c4238782766f5e322d2c700827d6f372d146827663574c382d782766f694c352d700827a6f382c14682766f554c473670082766d382d1460082765538270360082764c241f036
  | 6, 0, 10 => 0x826f504f4c382d7827c6f4c382d1470082766f322d05682766f4c382d227827a6f5e4c382c70082806f492d1f68276706f554c3870082766f38300f6008276574c382d682766f654c382d70082766f553a38682766f4c382d1b782766f4c382d0e70082766f5e4c3d600827a6f4c2c1f60082766f4c25166
  | 6, 0, 11 => 0x826f55524c38277827a6f4c38322c782766f4c3d381b70082766f4d4c476
  | 7, 0, 0 => 0x82766f504c382d70082766f4d4c382d70082766f55382d1470082766f4c39382d70082766f5e4c322d70082766f4c38372470082766f4c382d2370082766f4c382d05782766f554c38372d800826f55524c382d70082765e4c382d0370082766f4c382d2170082766f4c382d1570082764c382d2403782766f55524c382d882766f4c38362d148
  | 7, 0, 1 => 0x827a764c382d03782766f4c382d1f0080082765e574c382d70000826f4c38240060082766f49382d1470082764c382d27037000082766f382414682766f4c382d140080082766f6e4c382d78280766f4c48382d80082766f4c2d1f1e70000827c6f4c382d60082766f514c382d782766f4c38372d14800826f554c382d007827a766f4c48382d8
  | 7, 0, 2 => 0x82766f4c45382d70082766f4c492d1f7000082766f553827682766f5e5a4c382d8000082766f4c241f60082766f382d140f700826f4c382d1f0070082766f39382d1470082766f4c4a382d70082766f382d1f147008280764c382d0370082766f574c382d70082766f4c38302d70082766a4c38362d70082766f554c2d1f700826f4c382d14007
  | 7, 0, 3 => 0x82766f4c382d241f882766f4c382d251480082766f47382d1470082766f38302d1470000826f524c382d682766f6a554c382d882766f554c38322d80082766f4c3a382d700826f4c38362d0070082766f5e4c3824782766f4c382d241480082766f38362d14782766f4c382d14128000082766f54382d60082766f4c2d1f14782766f5e554c382d8
  | 7, 0, 4 => 0x827d766f382d1470082766f4c40382d70082766f38372d147000082766f5e322d682766f4c38362d2480082766f4c472d1f70082766f382d1410782766f6a4c382d148000082766f4c472560082766f6a4c382470082766f4c3832247000082766f4c3d38682766f4c4744382d80082766f4c382420700826f4c47382d0070082766f4c43382d7
  | 7, 0, 5 => 0x82766f6a4c47382d80082766f6c4c382d7827a766f4c382d1f80082766f4c4b382d70000826f382d140068280766f4c382d1480082766f4c47362d7827a766f4c382d148827f766f4c48382d882766f5e574c382d80082766f382d140070082766f4c382d1d782766f554c382d09882766f554e4c382d882766f69554c382d80082764c4838362d7
  | 7, 0, 6 => 0x82766f4c4838247827a766f4c38362d80082766f554c473870000826f4c2d1f006000082766f2d1f14682766f4c382d2c14882766f4c38362d27882766f4c382d2b14882766f554c48382d80082766f4c2d1f0070082766f594c382d78280766f4c382d1f80082806f4c49382d70082766f5d4c382d700827d766f4c2d1f70082766f4c42382d7
  | 7, 0, 7 => 0x827b6f4c382d682766f504c48382d8000082764c382403682766f4c38322d00800826f5e4c382d0070082766f4c2d1f1d70082766f5e382d147000082796f4c382d6008276706f4c382d70082766f382d25147008276554c382d0378280766f4c38362d882766f5e4c382d0080082766f382d241470082766f382d1412782766f4c382d2c1f8
  | 7, 0, 8 => 0x82766f4c2d1f1c7008278766f382d1470082766f5e4c2d1f70082766f4c382d0970082766f4e4c382d70082766f694c382d782766f5e4c382d2a80082766f584c382d7008276726f4c382d700826f4c38322d0070082766f5c4c382d70082766f4c46382d70082766f6a382d1470082766f38322d1470082764c382d140370082766f4c2d241f7
  | 7, 0, 9 => 0x82806f49382d60082766f5e4c472d70082764c47382d0370082766f534c382d7008280766f382d14782766f4c38322d248000082766f4c402d60082766f4c3d382d70082766f4c382d16700827a766f382d1470000827d6f4c372d60082766f6a4c2d1f70000827a6f4c382c60082766f382d2714782766f5e4c382d248000082766d4c382d6
  | 7, 0, 10 => 0x82766f554c382d1f80082766f4c49382470082766f48382d14782766f554c38352d80082766f4c382421782766f554c382d148008280766f4c2d1f782766f554c49382d80082766f382d2c1470082766f554c3824700827a766f4c2d1f70082766f382d2b1470082766f4c382d1170082766f4c2d271f7008276716f4c382d782766f6a5e4c382d8
  | 7, 0, 11 => 0x824c382d030060082766f4c41382d78280766f4c38322d800008276382d14036827a766f4c38322d80082766f4c38241f70082766f4c38242370082766f4c2d2c1f70082766f382d141178280766f5e4c382d80082766f4c2d2b1f70082766f4c382414700826f4c48382d00700827d764c382d03782766f4c4741382d8827a766f5e4c382d8
  | 7, 0, 12 => 0x82764c2d1f03682766f4c38322d2c80082766f544c382d70082766f4c3836247000082766f4c462d60082806f6a4c382d782766f4c48382d24882766f554c47382d80082766f6d4c382d70082766f554c3827782766f5e4c382d2c882766f4c382d140f882766f554c38362d882766f5e4c382d2b80082766f4c482d1f700008276574c382d6
  | 7, 0, 13 => 0x82766f4c4738247
  | 8, 0, 0 => 0x82766f5e4c382d782766f4c382d25782766f4c382d2470082766f4c2d1f600826f4c382d0060082766f382d14682766f4c382d007827d766f4c382d782766f4c38372d782766f4c47382d782766f4c38362d782766f4c382d1f782766f4c382d14782766f4c49382d70082766f4c3824682766f554c382d7
  | 8, 0, 1 => 0x82764c382d03682766f4c48382d782766f4c382d2c782766f4c382d2b78280766f4c382d7827a766f4c382d782766f4c382d27782766f6a4c382d782766f4c38322d7
  | 9, 0, 0 => 0x82766f4c382d6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 44
  | 5 => 52
  | 6 => 60
  | 7 => 68
  | 8 => 60
  | 9 => 52
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe3c79fc6381cff811e7f1823f3fe04780c6081c0c7fffff07fc7ff1fc07fc1f803fc7fe38c07ff8c403c79fc038fcfc00ffff001ffff
  | 0, 1 => 0x71cc0001cef8f1e0ff8e3f07ffc0e33ff8e3138f027ff8e383fe3f8e33e3fe3138f1e7ff8e3f3fe3c0833e38e013ff1fff1fe07ff
  | 0, 2 => 0xfc7fe0c7cf1f0ff1e3801f3c0c0ffc7fffff8ffff8f1e7ff8e3f3fe3c71cfe381cef8f0000f8e0000e007803e00fc000e007ce0c383c
  | 0, 3 => 0xfc7fe0c7cf1f0ff100001f200001c386001c70300001c030000703fff8e33fffe313f1ff831f3c7c3fff8e307ff0313f1e38c1f3f8c4
  | 0, 4 => 0x3f1e3f01f3c0f800001c000000e3ffe38cffff8c4e038803e07e0007ee18ce7df8c41c386001c703000e000ce0c3804
  | 0, 5 => 0xe3c79ffe38fcff811e73182073b00071cc0001cec000000000000000070000001c000000700000038e3c0833e38e0107f01ff07e00ff
  | 0, 6 => 0x3800038300000000000e00380000001c000000e00000000000000e04780c6081c0c00000000000001c3f7cc1c71fef8f1e7ff8e3f3f
  | 0, 7 => 0x3800e000000000e00380000071cc0001cec0000000000000000000000000000000000000000e3c79ffe38fcfc0e007ce0c383c
  | 0, 8 => 0x3871ff830fcfc0e007ce0c383c03871cf8301cec0e0000e0c000003871f3830fcf0001c73e003f3b0007003800fc000e007ce0c383c
  | 0, 9 => 0xfc00001c7001c387c01c703e070e180071c0c01c000001c0000070000007000001c000001c0000000e000001c000
  | 0, 10 => 0x38003807e000000000e0038001c3f7cc1c71fec70e180071c0c01c071cc1c01cec70000007000001c3f6001c71f0000fc73001c73b
  | 0, 11 => 0x38003807e0007ee1fce7df8fc1fb86039f703007e007ce7c383c1f801c39f000e07e0000e7c00001c386039c7e3000ee07ce0df83c
  | 0, 12 => 0x1fbf7cf9f71fec7e0000e7c00001c3f7cf9c7ffec70fd80e71ffc0003f1cf807fcec00e000e01f8000000003800000000fc00e01ff00
  | 0, 13 => 0xe03f803e07fc0380e000f81c000e000003e00e003801c00f800700e007803e00fc03800000f8000001fbf7ff9f7fffc7ee1fce7df8fc
  | 0, 14 => 0xffc0833ff8e013ff0000ffe0000fc3f7cffc71feff0e180ff1f8c0fc3f603fc71f03f0e180ff1c0c0e3801f3e30e0f3801c73f80073b
  | 0, 15 => 0xfff8003fff0003ff1c73ffe073bffc01f3ff8e0f3ff0000ffe3800ffc0003ff80003ff1c73ffe073bffc0003ff80003ff1e7fffe3f3f
  | 1, 0 => 0x3ffffff0000000fff8003fffe003ffe180fffc0c0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x20c4108218108881162a0822d12204400820810083729d703e42ef0dc075c0f803bc24430c028b08400c19a8018a4c8006fbd000fbdd
  | 0, 1 => 0x20c5188a1834c989120a88224024b00c320a082110b024a80620224210c32002c211080628800291042008220008000b711d70be04ef
  | 0, 2 => 0x902a204505090640800014100006fc5ffeaf8b7fd8b166aa862d3262c518aa1834c98b1042a86042262058a2a00b4410a0668a042930
  | 0, 3 => 0xb46e20c74d190ed190021d30402942a20454509049138830924643d2208225048002c190021c3040299204105a4021240c30c141b084
  | 0, 4 => 0x40a2440410926428470345093800811c081024e36cc30cd69b084d230823506c0036cc30cd69b08499304115a642112c430cc28b084
  | 0, 5 => 0x66c59aaa58b4c8933cf32964f7b24cf3cca593dec9310422960422200f080a013c40122cf12144b79460aa6604189243729d703e42ef
  | 0, 6 => 0x4b801038b00081084628e00b91009915d18b266f026415462c90ac29544592aa5238244114428908cb4ef3ccf5d3ded9b3efba966f7b
  | 0, 7 => 0x461bae7843ed65086e28e00fb102ddf7ddafb7ffcb751566be94ae2dc4109af81088346995438d2cd6bd5dfbabaf6f92e477ce2cb9bc
  | 0, 8 => 0x6fdffffafbfffdbf577eebebdbe6fcf3cfaf93dedbf1042ebe04226b9fdf3ab3fef19b7efbe96ff7b621f8a3a03fc413e6ffde3cfbfd
  | 0, 9 => 0xb4e4109f5c108ac0fc207c1df109dbb7d5df76ff674e995579d2cd9d304515e6423274a89157942499d200015e4000240e800541d200
  | 0, 10 => 0xd23b8a3d07ec4348c628f41b910bdff7ddfff7ffef7f9d77ffd6efbdef3cdffd3deef790427ff0422bd3f6d5fe77f76d3fcf37d7df7b
  | 0, 11 => 0xf23f8a3f07fc437eeffdf7dfbfddfba757df74bb77ec77cf7db9bcdfab3c7df52de77e8040f7d0020df3bef7de7ef776eef7cf6dfbbc
  | 0, 12 => 0xffff7dffff7fffff9042fff0422fffffffffffffffcffbdff9ffddf6ffbeff5ffdefdbfe6afd7ff32f6e410bf5c108bc8fe28fc1ff10
  | 0, 13 => 0xf23f8a3f07fc43c8f800fc1d600f2358a3f06f443c8bc20fc14f10f2258a3f04b443c89000fc10400fffffffffffffffffffffffffff
  | 0, 14 => 0xffe492bffc908bff9042fff0422ffff7dffff7ffffcffbdff9ffddff3f6d7fe77f77fcf995ff9d6cdfbb5df3fb6f6f3dbbcf3fd74f7b
  | 0, 15 => 0xfffe10bfff588bfffdf7fffdffffff5dfbffef6fbffd66afffbd32fff455bffe52bbffbcf3fff4f7bffee34fffd19afff966afff2d32
  | 1, 0 => 0x3ffffff8002000ffff9abffffccbfff9d7fffd6ef
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 54 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 54 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 131 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 131 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 131 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 131 then wireAt i else 0
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
  | 4 => 22
  | 5 => 335
  | 6 => 1947
  | 7 => 1107
  | 8 => 22
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xf75696f9e9dbf8b7e71f3f96de981f4acd8ba78ab3479012a8401ba59c134f8d95888eb3883ef7bc7f164aaf6156d8e3525eace54ee75b3340f828da3d3f8cb2318cb7db254ad762232b41171cbf1ec518d03b7f015974dd
  | 5, 0 => 0x2c61255c2c22e3092b95ff442b7791ed29474944293bab2928aaa8c7283be713250b3e6a23e92d1223b9319b232991f6227394b5225707d3217c18ce212f504a1fc92cf81e3d629e1dcf29111db4fc781ca66f151c97bec91c29cdf91af819111949f04e194882ed185edf94185eb47517c6219b17ab6e3a17597bc2172faa3b16716f5b15560eab1415238713b668f313a2adad135e69c41293710d11aa73f01136f9e510cc6bad0f33272f0e98fa660e3bfa500d71cd260ca8f48b0bd5dce909f4089109d1088f09adf9d1099ad82c0988915a0749b9e606fa4a3205d4ab0b04e398fb03d3407003c57b0f033f62e501c289ee00e3021600ac520600027c2f
  | 5, 1 => 0x6248ec6661f2f4f05d45eb4a5d38323e5be475045aa8a6b959b17cea592446c158c197145881c1695835cf7a5833dde557eb78fb556f069555429465553ddd4e54da5958500307f24f0d9c4b4e58e5db4e29c7d14e0c261f4d496b6f4d1acf0f4cf7eeba4c7acf5f4c187e4f4c0609b747ccf53646a217bf45d91ef14551190a449d9d2c435fa88142d61d4c42c6e51c42b779a342afcd1b42880fbc4276ae21422c19c341895be6406e451a403ac75d3f59133d3ec44bf33d163d493c9d75a23adc15ed3ac6bd5239957fd3392c94fc37c2cb5c377ab9dd37108154367f996d35f43fbe34c04b9d347939b8339a65cf325eabab309eac212eade2f22d2473d5
  | 5, 2 => 0x94556b6093eb0e0d93a2e0f6928f3a4d92879af990c5eb5b90b2c9b690a397f8904657ca90408f378fe09bab8fd90a7c8e4542108d92204d8d7e0df58cedacd18cc282af8c67854a8be07d838bb723b4897431fe886516f387f47cd38783905986f0dd8386ddfa1f86d946b086d7647c8682a3f6853e546784cdaf8b84b68dd1845e47978425943482b57be98175276a802658367f8529c17ec375137eaddb9f7c3be1d57c0d3d957aaa98647a7a23a87a3a562378890f6f785203c57780e2e975f66e48751113a07344f66972462f94711f3ab77018d7526e05021f6bae9e266b435fb36a81bc9f6972b76267f27727657914db650bfc2563669d9563374e10
  | 5, 3 => 0xc1e2415cc08a8789c0212655bedd9d2abea336b7be9bf688bceb2438bbec3344bbb4621bbb912b42bb701e32b955447eb7c8876db7aa0c84b761bec4b7610a65b61a6aa4b42e327eb2adf0ceb26e7667b25521c5b24f00d3b1b186bcb12ef38fb0f1ba6bb0166772ad7e96b2aab48070a8e25bada890ecd1a852eb36a822d3a4a7c5a7a3a6c33c2fa687e42da6846c82a61632f5a6016038a57ff13fa5225143a4d00d79a39b8aa7a3524039a2f0416ca25e4bf1a1d7c858a1c525e8a04323b3a0344db39fd4ea269f1f123c9e6b99699d933d629d6e98e59c3cd9109bc344489b73524099b4981d98a19efa989a692796d86ce29695ef3995b6b0df953df84d
  | 5, 4 => 0xf37843e1f34882a6f2b16536f1eafb75f0d9889aefcd789aefc2e112edeb49d6ed86fa4eed4e20d2ecc12505ecacb11feca6d576ec2eb1cbec0e5798ebd49c57ebd36905eb556c09eb1b78e9ea70c2cfea62b354ea07492de9a8dd11e433f1b1e3e8108be2fe02e2e229e20fe1d242f9e1c9df61e090f5b4dfeef4bedfd537a6dc404f34da9092dbda331ca9d99eea0cd8f11becd714b64ad5e60037d4bdf3f6d2eeb790d2c7a86fd28749dcd216a5d9d1a2f53bd1941c87d11dddf0d10e0725d107e0f6d0669516cfe56affcf194ff5ccc23c69ca46aedfc8bcd3fdc6398efac5c28003c5b6886dc57bfcc3c4f7a12bc406e7abc3aabe58c342cba3c2ec8822
  | 5, 5 => 0xff7c7227fe244110fd47943ffce6647afaba4034f9ef6757f9e10570f8805f7ff85a4a54f7156afff6cc6079f5e77c9bf49c2b22f46a6070f44a0543
  | 6, 0 => 0x8aa00e5085c29ce0848694b083843fe0815b7f90802d45d07f0433f07e99e2e07d21a78078f1e53078286a10737882a06dc6cc306a408710665520c0653736a0617f3be060f596e05fd0f1105f2ecc205f2790c05ea9b94059a2872054f0a5e053cd7d1051f1fac05169eb004bca6590460bf6904321371042abe3b04127e5b040eba5803f8e99a03cf5e0b039dbf550388a316037f689903598f5d033a727c030d3b3002f13a0a02c7a620029bda2f029aef9e0298285b028da25d027c6a3c02734c9f023deca20220bd12020e052301ee3fd501d18b1e019c9fad0198403d0185f46d012a5840011eaa2f010ab0bf00f91aa800a28bea006c268400296567
  | 6, 1 => 0x116b47241161181a1144e41f1142fa411120d6461103719910d7221f10d465f910bf6ca610b7c9a8108ef5b9102d8cd3101fadf4101f34a20fec104b0fa2a5570f9550a90f79f41c0f78ea770f47a0390f3dab0c0f07d9780eec435f0ee271f80ed5a7770ea8faac0e7e15130e65492f0e25ce180e0550e70dfbaa4f0dfb96ef0de224890de1cc4b0ddd4aa00d9cbe430d86abda0d6e8d170d4430e80ce551400cdbc0c60c8a4ae10ba8521d0b8ad6cc0b2e0ec30b2c8ce60b28f6400aefe7a00acc38510ac4d5b90aae691e0aa03d900a7677f50a5ed5a50a2d481b09ff431109c0e32809bdf0a0097689a80950b937090dfc8408fadadf08cc55e208c00bc9
  | 6, 2 => 0x1921237f191407ae18e9193f18ac994f1892cd85186cfbda185955ec18103f8817ec7ffd17e7c6aa17bd8d8e175a929b17237b8617206e351712096e16e24b2d16b01e541673385e1665ef1c16654882165a1433164f38e016256de516100cbf16066cd915f3a94215edc3f315da08fc15d3ee201587591d1563ab101561a43a15602014155ed0bb153802db14e76c0514863cc114696ac214649f8f14393d881437977c1422b86f14180334140b2e6e13ea83c213e0e2a713967e2f139302bf138cad0013728f561368b3e213346ed1132af56d130a5a8912db4a7b12cd4500125d0b7e121171f411b4bd5b11a76921119fba61118eca211188f51f1187183a
  | 6, 3 => 0x233e519822f5b6a922ea3ac02256b04f22521a042241f9d72238f642221f487121d8db47219634db2194ff3b218ce6fb215e4c98213d50c520e249a720d5617920a84c14206969b82064873a2014c6441fc92cf81fb72b911fa46e431f7f06c31f6d41b71f634b621f59336e1f3387171f1addaa1efda3231eb6c6781e65a7d81e4008941e2bb9ef1df83a6e1ddd2b031da440d61d826c881d75a3ee1d4df85b1d4653921d07cbc61cbd20421ca0b1831c16c93a1bcf83701baea4651ba64fad1b78d4bc1b62a5db1b27d2611a87fcc01a8148131a7bac721a4b36dd1a4058c31a2594481a1f1cf01a0dc40d19f6ee7f19cd069919b97173195f5caf1927b99a
  | 6, 4 => 0x2be5a9712bb2627d2bada1a72b83ba742b7791ed2b27b74c2b25f1c52b15732c2abb56d02aa7b7282a6c61542a1317a02a121f8d2a00355d29f85bda29f5789c29e11e8129dcd53d29d2dd3329d10a3229cba47729c478db29af2b64298b593d296669a2294399dc2934275728d3f68428bda13e2819312c27e4c34027d3a37327cafcf92796635c275958f22750b4f6272cb2762713cf0026bb2fef26a8a450267868632655fd64265363bb25fc001b255c4db2254954e525471fea2539609625320fbe24cbf97124a38602247367df245472f024136d51240fc14523fa873323e92d1223d675a923bca7fa23aa74da237d543d237418ee2373cc522359c6d0
  | 6, 5 => 0x335d81953316827432ecdd7e32e38d4f32e16b8932d484fe32aa3348326a549432476531321d7eb2321a0d07320f9fd331f21e3331968b41318b16ac3185f30f31752de731302720312ae6df30d5bde930d5282030cca4c430ad71ad309e97613067a335303166692fbf35272f8690f92f7e6ae62f6745e12f48cad42f37b6b72f34e7c52f2fce4c2f2288ef2efbd9642ef3a4c42eba05a82ea523322ea1c1f32e80cd732e5125f22e3061ae2dfdbfd52df741622df23de92decd8e72dec4b6b2de6358a2db09fc22d9810ff2d618f3b2d52d1502d15ed192cf8cd042cf6f6a82ce3b7132cadc4612c91587f2c5afc882c50f8382c45359f2c2026e82bebe72d
  | 6, 6 => 0x3b0db0ad3a4fc2063a11673839d765b4395f2ed039514ff1394f14203916855f390dd70d390153ab38eec90038c86292389a23f9388012b138695c3f386585533849f148380d7bfe37fdfb7837d8b58137d0dfcd37c3b2cc37a858a73784fc67376b796b37596ec33748575a3727f4ba36d69bdf36cb597836c0973836b5383e36ac2c9936a8e1d93679dd0b366fa272366ef10f36648703361d50e73610c82c35abf1c9358ef804354e1e6035239d6d3505b6fb34ecd7be34d88abb34c589ee3492603134886bc3347c735e347939b83451cc6e344da13934064f6c33e7285d33d93c6b33a95ef333a8219a339be8303389f6ab33864f1f3380d2fa336e091f
  | 6, 7 => 0x44e5077444ce283544ba778544ae84d944ab1cba449785304449f59543e3db9743c469ce43aea1a443a0a4d643555fb0433f660a4335a68143130f0342fbf37742bb11ee42b779a3427c5b8941b3665641a587774170bcbe4160ec3a415ab3f94149254d412c1b384115ab1e40fb824040c11d8e40936de1408a06cf4071490e406a83da404b301340066efb3fc23f033f7098da3f227ddf3e9b9b153e896cb83e7df9ca3e6c73253e56ef7b3e0ad2fb3dce4f973d8f565c3d8a3cae3d5d39623d4e5b033d4d9ea03d44b5c43d2c7c353d2562093d0b3b903ce8d0283ccc486b3c96bad83c86366e3c346cd83be497a23ba09a7a3b9e4ff53b7b8ba93b1bb4d2
  | 6, 8 => 0x4dc9c7c04dc7b19a4d84259f4d7c0ddb4d67b2e34d356aa64d1acf0f4ca1aa074c7dcf654c54b7244c1e35cd4c0f95d84c0f52314ba1260e4b9af8c44b86b0b34b75ea1e4b51d8934b2ea4f74b2472944b11aa524b03fc924ad762854acdf8d54ac953704abd1d0b4a8b70964a8b09ee4a3f5f3c4a11489b4a0a039049eb066449e3bfbd49d3f72f497fbd68497253c149516f1e494f43124932d403488ad56b48683a634840189047ee69e847d7f35a47d4da1d475897464734005047145eb646f1b31146df279b46bddc5e46b55adf469949b5466dcded46610b584631f35845fa3e6645b657d145afa458459774c2456daacd4526b408451ed66944f4548e
  | 6, 9 => 0x55f2f73355df5df85571ce4a556f06955551c8e5554bcaab5530a86c54f251df54e37e2f54dccf5d54c9884054a96c095488605d5459014c54583324544f103754304cc2541334f253ee2a9c53cb534053b8fa54538c2b2c537b088b536b8d0a534afad3533777b2530e3d0852adfd10525316e95250eadd52477438522c1d2d51e91276518d110e5160844351501bab5139dea75137e9295122fc1950df0cf1506e67a4505beeb35059633d503c745d503999f05038f11c503182d95029a31c500139404ff9d5294fc559f74f9d1e774f8c57c24f8552334f7141a24f159ccf4ed752244e7a219a4e4483a24e37dfb54e1018c74de6f8724de09d794dd54238
  | 6, 10 => 0x5f4ce3e85f4c3dc55ef6b1695ef302735ed6a3f15ed5c2bf5ec2fe405e5e95475e5903545e1f277e5e1ca47d5e1bc49c5e13ada65dc79a275da6006b5d8bf1475d72a47e5d5671905d4b941a5cde0cce5c50e6185c3f74815c1e7f7b5bdd230c5bc9771f5b6bdc6c5b3bf4fb5af98e345ad883ea5ace577e5a7cb15559f4348059efad2e59c0f58959a0c2fc5989a08a59449244592cf5295901034658e6c5465890cb2f5886e5b858817b3f586b2bf9585f3acc5855625e582969ea582291a25817540b5808a35357f4e8a3578012d056e8a03d56d7ea5656d29d1756cd250c56ba13a0565eeb7f56503afa56427f925627cd4d5618ad1555f6748055f5099e
  | 6, 11 => 0x67361348672edba1671ea51e66be8369669a48866697463e6633371c661f8dfe65e88a3d65cecc036560b6cd65438d0164ebe55664cb1eea64bd70fe64b225116472b701646d84376468b3576461049764595919644d72e6640f62e36407d9c463f6c75063df885163bd32ed63aed3aa63a6a9d363939f3363733db76310f02f6309bc0f62dc6c4b62d2e7006264afc16243e4b4622dc12b62261eff621cd20f620a30426208149661f63a0061f427ee61ca400861b15e4961874d90616fe8b461570a2961444ca2613f4bb66131e222611ff8cd60f47f6c60dc0ef760da144560a08da760774438603f22b95fbac6fd5f9ee40f5f9ddded5f593dd35f57a7bd
  | 6, 12 => 0x6f50990b6f4ebd9a6f4c3cf56f43e1be6f3c653d6f3a9e9a6f271ce46f0ee7fe6ee46b536ec13cc56e9b00a06e7107f36e4e713c6e3f00b06e2ca1cb6e2c96216e24e7616dd08b0e6d8815996d5f2f646d5d03586d5b00e46d483b2f6d26125d6d0c81136cae50056c7eacb26c4b6e046c2d95746c14b3b56be903d06bba04806bab48676b9d976b6b4493be6b09bc616ae97d196ac69eeb6aafcc206aab580b6a95be0b6a8f01346a729fe46a610cd96a50f1666a44543e6a1a8bbe6a0e5faa6a08bb056a08291469c0add469849e9369148b6868ade545689f85b8689e6745681571496805a91367f4aa3e67e0419367c13f6967a2a10667852479677213ae
  | 6, 13 => 0x766e04be764e5f61764692e6761e2a877613d46a76109d497607603675d32c7d75c8f03e75ace69a75791c4b755c9246752d38107508aada750876887502d39f74f8ca7a74d82ef174b5d9f474ae25e07481ccfa7460b49d74601fa77447c1c2743386c5740ead6c73e9209c73ddf38773655c0c7361e71e73493a277306471f72d7a0b5728256e4727718da725f4c797224534d71f4b8b871d8f93471b731cf71a6018171a2624171910fb3716e5da9715bc4407130886e710cca22710750de70e1e95e70da344670803a51705b5d9f7037bb1370345b60701fd2907001f6a36fe548956fceb7f16fbb45706f9a15cd6f8ded466f8476496f7090bd6f63d0f6
  | 6, 14 => 0x7e912cbc7e4b58517e2c43e47e22428f7e1d4b037e1a8a567e159c437e0bc1687e05acff7dd747b97db173387d8e4bce7d304f3a7cea112d7ce7e2b17cd49e1d7cc227717c9e1f737c69c65e7c6664907c6322a47c3be1d57c2f60d67bd948807baca6227ba3c0797b91074f7b90729e7b6ec17b7b4614867b25fb187b1fa70a7ada8ab67ab2a4927a7382a17a70559e7a2bf4367a1283817a02c9e479e5550479d342cd79c2eecc797004af7951d578792b8cc8791c125478e6cebf78d1319678976aae788f95117879923b785ee258785240d67852267d784337a87829da417800865577dfa17577d6a9ea77abf413779ca86b76fcecf676f0de3376d063dd
  | 6, 15 => 0x868f8bfa8679f841867726a1864f5914863b65ee8615d4dc85e8ce4485c3cf3c85ab6563859d9b7c857f1b668527bd3a84f92b6a84d0ea09849e475c849bc036845f90f784064fcd83ea69c583d7542a83ab9e3383915aeb834c2dc0833df9038323215e831ab8898312ea918300c2b982de711782d65b2b827963fa827639728257f5cf82348b3c8233416d8220babb81f114c781b76e8e81afa673818dcfcc8174a988817106db8154339f8153ce48813c2fa481025bc480da817180d851b580b1b4cd808528c4806266ad805c90738018916b800bb67b7fd737657fc015437fb866157fa0bcc37f8529c17f799cb27f55144d7f4ff8037f4590c97ed1cb46
  | 6, 16 => 0x8e2522c88e183e158e0ae11d8de1d4a88dd9f0ab8da6f0c78d88441d8d869bbd8d451e718d2eb7558c73f3678c5291f68c4a4e318c3f36198c1369598bee01d98bb5ea1b8b43d38e8b105bec8ab84b5d8aafa50e8aa94ae58aa3b04f8a8f77978a7994f88a7180e78a69d2278a1f83f089f27f8489e93ef089cd068489b019e589a54b3d8958e8bc892bf4c28905ec538903b09788ede02888d853e588cf7fea88bd66ca88a82a5488a4fc218898b407887ddfc28867195f884052b7882be4e18822a2498803a86a87f629bf87d2e6a887ba7d7487b2ceb48787f032874d669987257dec87151f96871506e98703169686c118bf86ba1c7b86ade39786981ab6
  | 6, 17 => 0x95ad999095a7bcd395a465ac95a0aa079582ff9e9551aacc9544e3fa951ba0c994d3db9f94b8834e94b791e694a0b6d3941783a1940d9631940a6f8393e2499393ad21ba93a23c6b939bad8c9380b44293602c46935e59519322c34693154ea392cd311e92c0ee8f928f624e92806526923130829207d92a92002a6a91fd1dbb91f1d16091e8ccbe91d127b5918b0169915bff58914d614e914539a5912821e49123b77090edb58d90d48e7390d21748905e4b30903730749021a9fa8fe77d2d8fe7744e8fb2b4cd8fa19e1f8f6057d08f5142b18f4a16428f3acded8f018fb88ec635f58ebf00228ea2abb28e965ddb8e94ccd38e7d732a8e3f8c778e323b68
  | 6, 18 => 0x9f092c3f9efaea139ec0d7899e9360949e8581b59e56566f9e3a30379e1a2c639dce524d9daae7359d6fd84f9d465cb99d42c3eb9d3121ea9d2f099b9cf14cd49cd8b9f79c5fe6c39c480cab9c1ef4619c068d939be46a309be41d5a9b74bd5f9b34b1219af887159aca79e39aaba6e69a5f17019a4ad2999a255f3b9a2202919a0d45959a08309399ce129a99a9b2ce998829a3996e299c98e9771598e3b99198a19efa989a6927988a6f269882e2ec98825709986d00ac982e64fb97c0eda197b559b097a4f387976491d0973d9af497012b8496fd835396f22a4e96e560fb96e491829695ef39967fbfcb965531e696321393960434e995f3331995b44849
  | 6, 19 => 0xa8a54093a893383aa840633ca822b426a81e07a4a81cf63ba80fa957a7fc18f5a7cf5c2ca79e1993a7470e27a6929344a6910249a664f1e7a6563cc3a611643ba60a91baa5d42f5ba59b9012a598068da5755eafa53255c5a513133da508355ea4d69db9a47fbd12a4428e5ba434b4b6a41794aaa4175ce7a3e9ce97a3e19170a3a56a26a39dd69ca3978b47a391e913a35b4fb5a33926f8a33588fda2cd8bc3a2b35b7ca2a97873a275f6c8a25e4bf1a24024d1a23d2cffa1f16defa1558ee5a1521c33a11662b6a0f696e5a0d162fda0cfe7b7a099d7c2a070683ea046c73fa03c38c2a0369f44a02ef21b9fce9c1e9f90b24e9f726bb59f5eff5f9f358452
  | 6, 20 => 0xb1aab58bb1976043b161fc5db110e951b10f4115b0c8b55bb0c4ab5eb0a1a8ebb08b6c2bb06c817bb000358baff20c80afc3aa61afaab267af943b0faf91d9ddaf73942eaf647c31af616e2baef5af7aaeee7c42aeeb3210aebb3672ae77067aae11518cadec3e13addfe763adbf072fad965e55ad710d02ad6e83e8ad58a5d0ad148ffdacdd4030aca9b064ac4df83bac38c2aaabe0a6eeabd5fcedab676f4fab3e2661ab225dd6ab193334aad9b799aa9545c7aa881170aa5561f1aa5550f9aa3d4546aa1f6e87aa11ec3faa00aaa3a9d57912a9b58ea8a977e211a95d0e24a931991aa909e4c1a8fcec0aa8f0d2eda8e78fc4a8d62ca7a8cca005a8cb32a4
  | 6, 21 => 0xba951fd0ba85faa9ba82afb3ba71d741ba701036ba6b17daba423037ba133d13b9ec7688b9e390b6b9e01b82b9df8830b9cbfbe4b9ba5ddab9748a1eb9662413b93206deb91d4ce9b8e03f25b8ca6580b8c07ea2b8b7e9f7b88932b6b8767b00b846a1a8b81bcc44b7e4964eb7d6b31fb7c9ca50b7ad2f8cb79d8b6fb78864c3b76b88a8b75c39a0b7566acab7547ca0b6fac561b6d8a086b6cb1964b6be7634b635de6ab5e0a511b5960b03b5863046b5406affb53177b6b4bad623b47be621b4520808b432738eb3d062adb33db3e6b3216c62b2d110c1b285abbdb27deebbb27cccb0b2794cefb2700fdcb26e940cb24f00d3b1fe93d5b1f9e3e0b1ce22c6
  | 6, 22 => 0xc26e5d2bc26d0ba9c267cbdec233a65cc22cbc1cc1fa1783c1a99556c182a013c1711256c152b13fc121cba0c0e08b57c0d8bcdac01d1494c0144dd9bffc6d2cbff0ea6dbfb4dd66bfb0ffd1bfb0cba3bfa2d939bf83682fbf458987bf3daf06bf23def2beea5a39bee24cdcbedf3b8dbecf96e5bec0a575bead23ffbea336b7be97b2cebe95c8fabe584277be4e61b0be4769d9be2aea4dbe269a7bbe179289bdf67f72bdeb6445bde1cfb5bdbc7deebd9d4a99bd8be129bd196541bccd4b3fbcc8e334bc95da00bc545819bc1340e7bc0bf607bbfaa1a4bbedd967bbe3d513bbcf1011bb912b42bb8f7c21bb75fc4ebb28b1adbb11473fbad020e5bac1507d
  | 6, 23 => 0xca2b008dc9bdabcac9a75c34c996b3b6c993c7a7c984c951c9831ef5c949310cc945c0d2c9282e46c91a9764c9135bd4c8f59c70c8e779a6c8843c2bc822cda5c809f2e1c7d3f23bc79e0f45c75c2593c7554d2ec7337313c72c9218c6f8273dc6da308dc6aaa746c6a48b8ac6888a64c680dba4c664bad1c63e6ab8c637c9f1c636a1a5c60a9cf9c5d1834fc5ae265bc576e528c5736c6ac5432efec541038bc5382f90c5368674c5057f75c4b5fa89c4949487c434f8fec4232d1ac400c1b2c3ad09c1c39b851ac398766ec3737f0cc3606443c34fd073c337f1aac3334588c332008ac3290eb6c3117bbbc30f2aaec30d6fe3c2c56a8ec2bc05a5c2afde01
  | 6, 24 => 0xd3152e0bd2fd1e15d2f3e8b2d2cd00b1d2a903ffd29440d5d279c252d2370a95d215039fd20d1552d2099c14d1f95dd8d1efb8f3d1de8b17d1cb1b0cd1979f1ad17bf5cfd161c738d0a5ce8bd07de0a3d028b587d027ba97d0022fedcf8af3fdcf524e2dcf384970cf2c5820cf000eafcec778f9ceb4067ace816823ce7088d0ce5b02e5ce597d4cce39d75bce20611ace08daddcdf98342cdba2e84cda6e723cd969af4cd8c6716cd70e6f1cd646acbcd13336dcd0aac50ccd3cdb7ccc7daa6cc452051cc389808cc338a53cc314ee5cbb9f257cbad0853cb7ec15ccb7814d6cb61e71fcb3988b3cb2d3d5ccad3949acad25745ca8af8c4ca5290e6ca35eab9
  | 6, 25 => 0xdb483e4cdb092744db0885a7dafef9a9daa10b17da934e32da650bedda0e6468d9ee6557d9d792fcd9d2c684d9ad9916d9a3cb49d96b0873d96b053ed968dc67d951bebdd94ad137d8d572ecd8c89669d8a2e1fed87f9952d872797ad85d0165d7adc8ffd7970f9bd783df75d7783301d748aebdd7168563d70a1d9bd6c3a000d6a5bda7d697b081d68e0ee1d676207ed675048ed670e039d5f531afd5ce88c2d5676af3d563257bd53d3f66d52b0a13d528804dd5115e41d4efa931d4af50cfd4938e6ad46d133fd44f1a02d445852fd3fd79dad3d2caa2d3bfb42ed3b6fe4ed3ab69cdd3a84f1fd3980975d37b9b4dd35ad9f4d359a462d34d4128d342c3fb
  | 6, 26 => 0xe2e44efbe2cad771e294f37de280ec37e26cad09e245b324e238aa93e21be8d9e2043fb8e1fd09cae195a639e18c682ce18ace26e171d949e165e754e11bb465e111b6dbe10cf448e0bf88c4e0a67868e0930e9de0800c8de05c847ce04e0661dffebf9ddfd12c8bdfbea839df66edf2df5bf037df1659addeec6317ded5d017dec9dac1de90f3a7de7f9787de12fcccde0091c7ddfb04cdddc81e20ddc15ca4ddb5fd1cddaa279ddd8ed5d6dd73e459dd6c186cdd50c1cddd2d6207dd2a54f0dccc35b4dc90e37bdc5b5f15dc5b4c2ddc530e5fdc374bc4dc0740d3dbf961f4dbe6b227dbd24f01dbc7af05dba78fe2dba68411db76ec15db711277db4f33a9
  | 6, 27 => 0xec0915fdebf03b1eebefca4bebe31074eb8575c1eb6724bbeb66372beb475aefeb32e76eeaf7f023eaeb060eeabceb59eab31e8aeaa80466ea96d1e2ea8e0ff7ea6e77a2ea4461ebea206746e9f2555fe9e0e609e9d9bca8e9674be0e945efd6e8c040abe86efbb3e8372b18e82ca1a0e8047120e80138e2e7b87f31e7b39f5ae7b301e7e7a6205be714a497e6fe9ff5e6f0c116e6b68bace6886563e65393cae648521fe61e3e4ee60ea2f3e5e5e691e5e14f13e5b698cbe56ae1b2e54d2d9be54c555fe542f8f1e4be959ce4a745e5e49c409fe485a5e1e3f51417e3e18a9be3c45a32e383dba9e35f01f3e358b1ffe33cbb01e31a7a5ae316571de30962e5
  | 6, 28 => 0xf4723ae7f3d533ccf360add7f32a1730f315bb40f2ff5c43f2dc9b47f2d7e58ef2c41b18f29edce5f279123cf25a5c53f25014fff23a1c75f221adebf2190accf208a2b9f1d1b98df1a91aa5f19a275cf19580b8f15a4793f117a0a5f0f8df95f0771dd6f0557068f03d9387f03745e0f02597d4f01e020ff014970eefefa548efb77742efb0189befafc882ef831902ef0c9bc8eedd17f9eec40f0ceebe9aeaee71c1e8ee6c74d1ee622b56ee5bfb02ee44a0bcee1e2c58ee03b1aeedd0785cedc03d67edb51c7aedb21186edae8b10ed9de86aed84be95ed50c2e9ed215bcfed211c1aed07c3a8ecf6bbe2ecc601fdecc260f5ec81985dec6b46deec0c1396
  | 6, 29 => 0xfc86bf18fc6afe7dfc421525fc3f5bf1fc392c47fc3650befc30abd5fc17630bfbbdb1d0fb9b5cd3fb6cc623fb314dddfb152bdafadb836ffad8dc57fa72f38afa57e792fa4fd28dfa111c28fa06476af9d074b8f9b8c4f3f9afb2a4f9968090f9287a1cf8d5ce41f8805f7ff86fdb15f86a14bbf85cda48f85b44fef81f4268f81e117ff80e59ccf80908f4f7f9dae8f7e68aa8f7d45d73f7a45692f76764a8f766edbbf755edc8f73a66a0f737c7bbf71db1a3f7055979f7019136f6e5cf63f6d3c780f6add2cef68e6a67f6655c2cf65d051ef62a4690f61da697f5e77c9bf5e5463cf5b9b417f5a6f02df58f108cf5192827f4ebb8c3f47fc6bef472f26e
  | 6, 30 => 0xffc703bfffb41ef8ffabe638ffa7869bff98826cff91be5cff7efb7eff6a3260ff37ead4ff221992ff08b859fee7f663fee5981efed1b51bfec6917efeb499f5fe4d0768fe3abca4fe3673f0fe255537fd9b65b0fd64caacfce8a04bfce6647afcaa882bfc9f7816fc97bf31
  | 7, 0 => 0xf3badb20e8414b20dfb96ef0da469ce0d91ebc20d61f2fb0d4d98860cf91d9f0cea20e10cc7aa850cb3009d0cabde0a0c867e660c22507d0bd753a90bb2ffb10b989d440b41c7720afb5dd30acf09dd0ab8b26f0ab7b9ae0ab0afbb0a9628be0a71f95609f8447009ee1b6f089ab0f30878675807bd347d07af559e076636a70754ea1506b07a0306634425065223ce064612c7061ab2860618ade405c61dd605ad2f3405a3eb0a0590310f04d0acec0452788e040745c603e36454036df150033b05b50322eb1802d5abde0296f5790291d00a024a740d01b3df100198251c0129b75501283a1701013f3600dd496a0086a50c006499150027347900103def
  | 7, 1 => 0x1b8548e61b78d4bc1b70b1901b61a0cd1b5aa1f21b325a461b2d157f1b1036f41a5d39541a2bfa9c1a0ece701a0dc40d19f08aad19deb3e219b1d4481979f417196672e1191531f418e3fb0a18787ffd183e8305181aa94117d07b00175a929b17206e35170db67f16e8db1816b50ee916a611991680e7551662ea0a1606144c15ff8a4715f86a801561a43a143e5742141a4f1c1415063f1413d60813b5da6d135211a2131bfefa1317dd2b12b8ab4112b8884a12ae5da31234695d11d7480611b4128d1187183a10d1aa96109bc6601094c3a5103ead2a102d8cd30ffdfe370ff073950fd4c3f50fc22fb60faa77070f8898390f6b9a140f5c5cfb0f3d8440
  | 7, 2 => 0x29e942c429c478db2964176b292df8a1291abe5628ac56fe2882e2b2284db2db2838c79a2775450f2774c460272770732705880d26e36c2426beaf6f26bb2fef26a4b5bf26488ebe26396ad425bece64259eb530255ffecb24cb7b2924c13a83246ade96246554a62457669f2429651523fe6fae23afce9223a7fde62325e28c231857ea2310763b23038dd422ea3ac022daf26b22724f2222521a0421ada82821a5f96820df43cc2081cc612064873a204aaf2d2046aaad203e530f203cd04e20292edb2015ae6f1fd3d3851f9bef851f3108e21ee4e3db1e739d441e1aa3ae1e17d8601e08e1531d989e101d81c57f1d094b741c53b96d1c27ad6d1c1ffead
  | 7, 3 => 0x3950034038ad846e3899ed1837dd7e8037a1ed1c378f31e8375fd1e83732d33a36f4981f36e4026d36b6da9236ad516036224d1b361b1af4360aefae35d89aaa359aee6d357bcd57355e29ce354bc4fd34ceb8d13481847a34746a9f34744a7f342cdee933ab0d08333d92c433193e9a330961a632e7627a32c3d3da326a0621319b3e42315024ba30f26f0930ccd1eb3078c0813055c0a6302ca7772fc976f62fbf18df2fa1c82a2f7655c82f1362052edbd6b52e46479b2d90db782d6df75a2d014b912cf3c0ef2cf085992cb7e2692cae27f22c9946a22c1543872bdd94e82baacaed2ba064522b89112d2b48380c2af4104e2a7c85282a6bdfc02a5175e4
  | 7, 4 => 0x47f69d26475141bb472e33c146e149a24609964845f6b58445c07cca457c5ed145179a8f44d9dfff44cd758b43cee64d43b4257143a9f84843555fb0433f660a432891ef4309ffd842bf286342b779a342815d8a4223bdb94215deda4214fad141d622d341a83906413ca69640db2d8b40cb4f8b40bb28344079af63405c8f3d40455b7a3ffca0873f8b9abe3f49363a3f086e6d3e38a7a13e1c8eb63dff89d03dc32c533d6d0b963d18fbc93d0124c93cedcf813cd7d7c23c9f3cdf3c9dc2fe3c8fe41f3c3d49423c29a7cf3bd0b7833bc2d8a43b76a7473b5624293b3c318a3b23954e3afd7b253acd3e823a8b9b213a861c993a4766343a305add396f572d
  | 7, 5 => 0x53b7a8b553b3d16b53346db9531915d153169294530ec13f52e996fb52acbe7d52942b725275541c51efbb6051e81d5151d2062b51bf3f2b51a4e007515c2919514f64545116551550c4b4ed50a706e8505beeb35038abd64f9b055d4f717d1d4f624ff44f0fba7a4ec05ebd4e9d19034e79bd534e7327324e5bae794e0e9fc94de254b54dd111674d0476064cfd734b4cf7ab1c4ca60af44c173de94c1326ad4bf147df4bc969994bb8974e4bb222f34bb13b214b7591cb4b62f61f4b13daf94b02825d4afc5e1e4a9f53ac4a6707154a3f78dc4a32c5ee4a0d197449e125c649d602e849ccf75649148db048f889f848ebd2aa48b85b5d48b0ac9d484e6acf
  | 7, 6 => 0x6347643b633af0116336351163275f1562b43c176292bf2262623a3562542af861f427ee6129ea2960c01645602f2d625fd513de5f5d13a95f492eb65f2a63495eebace45edafec85e90082e5e1657ce5e06e6065debf6475dc82fa15d9647d45d93d62e5d2e415c5d23bf8f5c9fbd605c91de815bff541c5b2acd595b0171135a73054d5a7078f85a1dcce55a17fce059f684b259e9c31b59e533015943cbfb5923c1c65905159658a5f17758905d13584e132a581fb8f65806ebe257ca6bbf57c35198572d859756dbe56f56da22f0568ff7f15686958d5647df2856240dff55f952e755df5df855ab6c465592bd7c557f4cd954ed1c7554c1de1054b47b98
  | 7, 7 => 0x714a8ba971056b6270ffce1070b1e10170946692707cee8d6fbb00476fa6c90d6f6c29a26f69601f6ec13cc56ebe77696eba99336e9f1e276e834bca6e4086346e38e6f66e34ebde6ddedbb86dbfb81f6db8095f6d5cb0976d45b13a6ce170276cd622c66c8fa51c6c4b6e046be1bd3a6bcb63fb6bc490ee6b89f08a6b7c11ab6b1be3666af785736ab08a3f6a5eea176a4f22086a2a46cf69f5d2f969c031bf692e70ee6920920f68ff5c7d68b561d0683fb3fc67f1c0d3679d352a67425c616709aa616702fb5166fb4c91668c477066742ba766357542651506a464ffcc4e64e30e6464d90fd164789948645092fc6449b75d64015902638147926379a676
  | 7, 8 => 0x806266ad804a3051804281917fc0036d7fb9fc427f5f0e0b7f27d8097ecd8d627dad4e397d776c2f7d33ff317d303bbe7cd372a07c439fcf7bf0d3337bc86ac17b8db51e7b3b45dd7b2b17a17b25f4ae7ac854af7ab597257aa157477a7a23a87a70b1287a38d5c279a4d76c791d9b4178f04d3478bca81278925775785a178978493a7f77f10ba277d135d07733bc5377211a3f76fcab1e76f0de3376f0916b76eecc3f76db0b2e76bdf4b976b015da766385db764692e6754008987524155b751c82e774f2245d74e1bd6173f60c3a73b2320a73a1eeb77341d2fd7333c42e72b28339729906d4727daf3d72739f547263b2ee7260e48f722486f3721cd833
  | 7, 9 => 0x8f78512d8f6e24048f255fd78ebf00228ebe4a858e7e28318e4941358e27eed18d92f6958d7f04bb8d3d413a8ce77a638c8386ea8c1a6ee88c0e14188bedc1998bc68b508bbc73f08b8fda438b41089d8b3e939c8b308e208aef68758ada8b1e8a8bfac78a59f30f8a18c2888a0d10dd89f226db89beef4c897643b689605ac28958e8bc8934bc8a89143e4288edfe0d88ede028881ad29987cdddd087ca80ca877c8a9f876b320387080352869b7594867726a18635a6fc862851b985f48e9f85e99b548549f6d285210b038492c7cd83f048fb83c5bc52833df90383233d80830766bf82d3eb99828cc064828511a48241b05982121d0d81bd8a2f81102355
  | 7, 10 => 0x9c27c3cd9bfcd7929b71391a9b6f77d89b1dd7b09ab0be7a9a95b69e9a36658d99ed5e8799bbfbc9997d456498fcecee9892bda99882e2ec985a34f798553ede98411d81981b7e9297a5128c978d297c974e73179721f5ed96fad25696a4b77d968ac1e99680ac86965f3458965531e69603a49895fe78aa95a996be956b46b2955a0898950fbbe39502be1694b8834e9442b06894331b6593f42b8d93c8c08d9396353d9351acbb934043b892ef453392b08ece92a6c201928df768928cbda5927a567e9272b1cc9262028d925c0be491bec62691940ed391426eab913b5e9f9074f28c9037c66b9011f582900c696690061e318fe9ad8f8fa2db658f9d1d5f
  | 7, 11 => 0xaee65ee3aec64c0eaebd223cae8d3699ae5c9576ae064aa9adab993dada32de2ad85a160ad6e1b08ad1a90a7acac34b6ac3ab49dac296414ac23afedac100e7aabe5308aabbe6e52ab962e79ab94b348aab1140caaa935daaa8df529aa87c3f1aa3f12b1aa38618daa2867c5aa21bb6da9cb11c2a98c5b5da9647ee6a8d69abba80d4bfda8098f40a7bb98b7a71939e5a661d0dfa623790ea5e4c2a9a5cabbeaa5103ec2a4711fa3a3f2435da36baaf7a302d5f5a2f4f716a1c6431fa1946574a141bf77a0c045e2a0b26703a07b3991a02ef21b9ffd08839eab30d29e6bbe4b9e58572e9e3c45669de02fb29dbe03239d61744b9d3121ea9ce015509c97dd08
  | 7, 12 => 0xbdd38f62bd5c9ba0bd3f82f8bd2744b8bcf5d0c6bcb2dff7bca07defbc5e25f5bc4e7163bbe49247bba736d9bb3f92c0bafa41a4bab08b31baa8a17cba88bda4ba477786ba45dd7fb9e01b82b97e2118b9782853b89ec208b84d21e0b837fe7bb81d78f4b7a3f583b713f0d0b69fded2b65f3e8fb5c9ec3db5a1cf19b59a84ddb559ed2fb52557b8b5195244b511b645b4e46fecb3feb3cab3f8265db32b1ae2b2f03ccbb2dc7687b2a58f0eb253eee6b2306866b22e7c90b210ca3fb18cc501b16429bbb12375bdb108215ab0f51e5bb080f6ebb0480e0db031ca64b02268afb01bd45eb01ae1b0afebec7daf95e2ffaf935789af4ec8e3af01b67aaef43dc2
  | 7, 13 => 0xcdd2d617cc0b8b0bcbfcbae9cba07d9ccb46a5f8cb26fa2bcae6d7d7c9e65a89c9e24337c9a019fdc8df6e8fc876c3bec7a9b843c7a3ca76c7554d2ec707ac1ec66cfc38c62e45d3c61b5c10c5e58a67c5dca5abc5c226a0c59d6c30c57cede8c5690328c52f7576c4eae2e7c4ac2c82c483e9fec4605fcec3fbe96fc3935453c37f968dc3598a1dc31b6fd9c278c27bc23de552c21dcfbbc1c6e06ec1c5a5bec1c16a74c1a069d3c150c440c110cb7dc1043454bff0ea6dbfa41077bf8705ebbf7d381ebf4172fabf01fb40bef5700abef4bb49bef1afedbee065e9be907f01be6b5265be4f311bbe4be64fbe3418b4be2639d5be1fe45dbe107ab6bddd5bac
  | 7, 14 => 0xdd547ea2dd4db3aadd114471dcac824edc240579dbeeb34dda8fa153da8008d2da7890dfda4c5f43da26b2c9d9ed2281d9eccea3d988b69cd986de71d8f62b1fd8e7dfa1d8653959d7d8277ed7c2c847d7ab2662d76eed8dd7661623d6fe6644d6e961fcd6b34f54d697c1d4d62ad27fd5d7c256d5d13c99d58853add56748abd4fb6d4fd4f736c8d3c1c38ed38eac86d355d4ffd30f653ad2f75b26d27a66b2d229a3e5d1d3f658d1b38e6dd17f337bd1786b89d0e4e8e0d0ab600ed0a7e5c1d081713bd051c79bd0317033d01dcec0cfe713d2cf84bc20cf6ea403cf6e15b1cf2fed9ecf0c769cceecb93fceeb1ad8cecb96dfce6b8b90ce3bc8d3cdfcbe79
  | 7, 15 => 0xebb77889eb7a065aeb3fcd10eb0c9569eaf7dac4eabec0cdeabceb59ea7abc7eea72c195ea555bf2ea3c0619ea39f55dea206746ea04555ae9f23fa9e9d3bc26e9561ebee8f19d4fe8b54ab1e8b03ee3e878be20e812cbdfe7a75556e7471eece73c37a0e7283c3de6a7c695e5c6ac76e5b5122de575a6eae5179d48e49194eae48a3599e4402e8ee3ed24d8e3d420a8e33582dbe2f6cc76e2f02cffe20aed9ee1e7aed7e1ccafbce1c2a466e1b94d76e1b1f408e12fee6ae0f3695fe0d9cf49e0d27efae088d44de07b344ee04a17a1e044fe41dfeb09c7dfdba1afdfa5c541df7fbf91df0801eadede789bdec9aaa0dec49712de1b0bb2ddfd151adda61eca
  | 7, 16 => 0xfc3650befbefb591fbe5e7c4fb74cedafb192d73faf72242faca2394fab495f5faa130d0fa6ea56df9b99d75f9acd0faf9824cb5f96feb04f9323ec7f9092d95f8b72109f80ff336f80fe67ff7fbcecdf7e68aa8f7c476a1f762f14af734b506f725d631f6f16d4af6b08ef4f646c3bff62cba88f5493ef0f50771aef4535bf8f3e60244f32a1730f273270ff22186e7f20a7ebff1c7ebb4f17a65ebf171c893f15a4793f14d1f92f11d8484f117a0a5f0f10dbef0dd9aa2f0c5c7cbf087d5f3f03096fcf0107b11efeaeca8efdfd1c7efdef6d4ef94b1afef4adc1aef0e3eb4eec76f65eeae7dabee570e7dee22ff53ed5ae6a4ecfeda8bec848404ebc28ee5
  | 7, 17 => 0xffd4999cffabe638ff5a28feff3df527fefc312dfef2bd64feed7483fed37441febf47eefe648edcfe12eeb4fe091979fd875a02fd797b23fcf8d17ffce2758bfcb4afe6fc7cb7dbfc3e0176
  | 8, 0 => 0xf33b5fd0f2854adfdee29a6add9de376c3d681efbad4da24a279eac4876dd2497e6c2a7e7e1a8a56764e5f6161ca40085e22a75451bb2a0f4aee737942b779a33e277fff2eedfa851e7359ed1729918f1606144c0e85c3d3
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x84109461842048040037085504844000000000084107000552048030247081154804010000000084109370855048440100000000841094609420441401360942144140136094214414010000000084109000000000000c000000000000d0000000084109000000000000736094214414003708550484401000000008110537085504844014609420441401
  | 5, 0 => 0x3000002550020100000000000040000025500201000000008410700000000841090010c254c430100000454c4200000002148420000000000000020000000000004000942144130100000000c4103000000000000d00000000000040000000000003000000000000d0000015480200000d82544130100185430c4301000005048420200000450812000000000000003000000008510200000000000040000045081200000d8214843000000050484200000d8214413010000000000003000d8254413000000000000005
  | 5, 1 => 0x8410900000154802020008550484301000d8254c4300000000008510200094204413000011820441301000000000000c000000000000900000454c4200000000008410900000000841070000000000005000000000000000000000000070000000000003000000000000500000204802000000000000006000000000000600000254c42010000045081201000d821484300000004508120100000350852010000000084107000000000000d0009421441300000000000000b000d8514813010000000000009000000000000a
  | 5, 2 => 0x50000000000007000000000000300000000c410400000000000000000035085200000d85150830100000350852010004125440301000c8254c430000000450812000009420441301000000008510200000000000070004125440301000000000000300000450812000000000000000000000000000400000255002000000000000009000000000000b00000000000090000035085200000000000000a00000000c1105000d8254c43010000025500200000000000000d0000025500200000000000000c0000000084107
  | 5, 3 => 0x53105200000855048430200081154803010004125440300000d821484301000001044020000000154802020008115480300000c8254c4300000000000000a000d8214843010000000000003000000000000b000000000000700000000c41040000000000004000993104130100000000000030000000000004000000000000d000000000000a000000008410900094204413000000045081200000000000000b000000000000b00000304c0202000000000000d0018420441301000855048430000000255002000000000000004
  | 5, 4 => 0x35085200000000000000a001182048030000000000000000000000000002000d8254c430000000000c410300118504c83010000000000002000000000000b000d821441301000000000000200000454802000004125440302000811548030000185320c430000000450812010000020480202000000000000d000000000000a00185320c430100000000841070000000041105000000000000a000811548030100000000c8107000000000000900000504c4201000002048020100000000c410300000214842000000000000005
  | 5, 5 => 0x5000000000000d00081154803020000045081200000000000000d000d82544130100185430c4301000000000000900000000000090000050484201000000000000d0011820480301000005048420200000000000000011820480301000002148420100000000000000000000084107000000000000b0011820480301000000000000000000000841070018c4540a30000000000c410300185320c430000000405002010000000000009000000000000a0000000084107000004050020100094214413000000035085201
  | 5, 6 => 0xa0011820480300000000000000600185430c430000000000c5102000000000000d00000000811050000040500200000000000000b0011820480301000000008110500189450813010000000000005001842048030000118204413010000015480200000d8214843000000000000006000000008410700000000000040000035085200000000000000600000214842020000000000004000000000000c00118204803010000000000004000004548020000000000000070000000000007000d8214413000000000000009
  | 5, 7 => 0x200000204802010000000000000000000000000d0000015480200000d820480300000000000000a00000415042000018935085301000d8254c4301000d85150830100094204413010000000000001000000000000500000000000010000040500200000002148420100041254403000008550484301000d851508300001145108130000000531052000000051081200000000008410700000255002010011905881300000000000000c000004050020000000000c4104000000000000600085504843010019420441301
  | 5, 8 => 0xd82148430100000254c02020008550484300000000000000c0000000000009000942044130100185430c430000000000000000000000000003000c8254c430100000000c4103000000000000a000c8254c43010000020480202000d8214843010000035480202000004508120100000000000010000000000004001143508130000000000000090000000000000000000000000200000425082000000000000000000d82144130000000000c4104000000000000a00000000000060000000000006000002550020000000000c4103
  | 5, 9 => 0x7000005048420000000000000000000000000001000942144130100000000000060000035085200000d825441300000000000000900000000000020000000000002000d82144130000000254c0202000000000000b0000000084107000000000000200000000c51020011851481301000000000000b0000000000004000005048420100185320c4301000000000000d000000000000d000000000000a000000000000400000000000090000035081202000000000000d0000000000000000d8214843010000000000009
  | 5, 10 => 0x90000000084107000d851508300000000000000000000155002000000000000004000000000000100000000411050000021484201000000000000a0000020480200000000000000500000000c410400000000000030000000081105
  | 6, 0 => 0x3000000000000a00000000000050000015500200000005150c20000000250022010000015480201000000000000200000350812000000015500200000000000000d000000000000a000000000000700000504842010000000000005000000000000b00000000000000000052101201000004548420000000000000060000042508200000000000210000000324c8202000000000000500000058c82000000021484202000003508120000000058412010000000000004000004150420100000000000060000000000004
  | 6, 1 => 0x25441200000000000000400000000000040000000000003000000000000000000514c820000000018022010000050508201000005250c20000000000000040000000084107000000000000500000000000070000000000006000000000000900000515082000000000000009000000000000e000000000000500000504842020000000000000000003500a20000000155002000000000006101000005048420000000000000060000000000003000000000000a00000000021010000000000005000000000000100000000c1102
  | 6, 2 => 0x400000000000080000000000004000002500220000000000411050000000000007000000000000700000000c41040000050504201000005150c2010000000002102000000000000000000350852000000010440202000000000000600000425082010000000000006000000000000a000000000a100000000000000500000104402000000000000003000002144120100000018022010000000002102000001550020000000454c42000000005881200000000000000b00000000c510200000350812000000000000004
  | 6, 3 => 0x20000010440200000000000000a0000000108100000005250c2000000000000008000000000a100000000000a10000000000000060000045480200000000000000700000454c420000000454c4200000000000000900000204802020000000000003000000008110200000450812000000000000000000000000000900000214842000000000085100000003500a2010000000000000000000008510200000254c420100000000021000000000000000000000500a200000000000000a000000000000900000000c1102
  | 6, 4 => 0x5000000000000d0000000000006000000000000000000430c42000000000000006000000000000400000000851010000000000005000000000000600000000c8107000000000000d00000214842020000010440200000000000a1000000000000009000000000000b000000000000400000000000050000021484200000000000000b0000010440202000000000000a000000000000600000000000030000053105200000000000000700000255002010000000000003000000000000200000000000050000000000003
  | 6, 5 => 0x7000000000a101000004508120100000450412000000000000009000000000e10100000204802000000005885200000002504120100000000000070000000000004000000000000700000405002000000015480200000000540a2000000050484201000000000e102000000001210000000028022000000000000005000000000000a000000000000b00000155002000000000000005000000000000800000000000050000000000005000000000000600000000c910200000000c810300000000c8101000000000a100
  | 6, 6 => 0x4000000000610000000000c410400000000000030000050484200000000000000500000504c42000000000000004000000000000d000000000000300000000c41000000000000009000000584120000000154c02010000041504200000000000000400000000061000000000000003000000000a102000000000000900000000000030000045484200000002550020000000350022000000000000006000000000000a00000000c5102000000000000400000154c02020000045480200000000000000400000254c0202
  | 6, 7 => 0x811020000050508200000000000000400000000000090000000000004000000000000600000521012010000025500200000002148420000000000411020000025500200000004508120000000454842000000050484201000001540a200000000000000a000000000000300000350812020000000000003000000008110200000000000050000000000003000003508520000000350852000000000084101000000000000d00000454c420000000000000000000000000007000002550020000000000000060000015480200
  | 6, 8 => 0x380a200000005150c2000000000000002000000000610200000350852000000000006100000000000000300000000000090000000000000000000004c10400000000c910200000425082000000000012101000000000000b0000000000005000002144120000000000000020000040500200000000000e10100000000000040000000006100000000000000600000000c8101000000000000900000000c51020000000000007000000001210100000000000030000045484200000000000000b00000415042000000000085102
  | 6, 9 => 0x310412000000000000004000000000000600000000000050000035085200000000000000a00000000851020000000000005000000000a101000000480e200000005310520000000000000040000000000007000000000000b000003500a2000000000084107000005048420000000000000030000035041200000000000a10100000000000060000000000003000000480a200000000000000400000000811020000035002200000000000000600000204802000000050484202000000000000900000000000010000000000005
  | 6, 10 => 0x214842010000035081202000000000000500000000c41000000000000003000000000000400000000061020000000000007000000000000100000154c02020000000000007000003508520000000104402020000000081101000005050820100000000000030000000002102000000000000600000000121010000005841200000000000000d000000008510000000000000090000035081201000000000000300000000121010000000006101000000000a1010000035085200000000000000100000454c420000000154c0202
  | 6, 11 => 0x7000000000000000000454c42000000021484201000000000000a000003504120100000000000030000053109200000000000000b0000000000008000005310520000000255002000000000000009000000000000e00000000c5102000000000000300000000000030000000000000000005048420000000204802000000010440200000000380a2010000000000006000000000000700000000000030000000000006000000000000400000515082000000040500200000000000000400000000c51020000000012101
  | 6, 12 => 0x320c420100000000c1102000000000000300000000000050000015500200000001044020000000154c0202000000000000900000250412010000015480201000000000000d000000000000400000000000020000000000003000005310520000000454802000000000000005000000000000500000000000020000035085201000002550020000000304c0202000000004110000000431092000000000085102000000480e201000005150c20000000000000090000040500200000000000000200000454802000000053105200
  | 6, 13 => 0xc9102000000280620000000255002000000020480201000000000000800000450812000000000000000000002500620100000000000060000000000000000000000000b00000000000030000000000001000004050020000000000000020000000000000000000008410000000204802000000000000006000002148420000000320c4201000000000000b00000000000030000000084107000000000000a0000000000008000000000000a000000000000300000514c8202000000000000400000154802000000021484202
  | 6, 14 => 0xa0000000000006000001550020000000154802000000015500201000002148420000000000000090000045484200000000000a100000000000000900000425082000000042508201000000000000a0000000085102000000008110200000000000070000000006101000000010410000000454842000000004806200000000000000600000415042000000043109201000000000000a00000000000060000053105200000002148420200000000000080000015480200000002048020100000000851010000053105201
  | 6, 15 => 0x9000000000210100000000c910200000000000040000020441200000000000a10200000038062010000000002101000000000000200000350412000000000012100000001500a20000000000000040000000000009000002550020100000000c510200000000000040000000000000000000000000d00000000000070000050484200000000010c10000000254c020100000000121000000025500200000000000a10200000000c410300000310412010000000000009000005048420000000000000050000000000009
  | 6, 16 => 0x5000002550420100000504c42010000000000006000002500220000000058c8200000000001210000000450812000000045480200000000000000d0000000000003000000000000500000204802010000042508200000005048420200000531012010000000002102000001044020000000000000070000000000004000000000000800000000021010000000000004000000000000800000521052010000000000004000000480a2010000000000007000000000000300000000000000000000000009000005050c200
  | 6, 17 => 0x10440200000000000000500000038022000000000012100000001548020000000531052000000000000004000000000000400000320c4200000004050020100000000000090000000084107000000000000d00000204802000000000000000000000380220000000000c0102000000000000a0000045081200000000000000800000254c42000000000000003000000000000500000000000000000051508200000000000000a00000425082010000000081100000000000000600000454c420000000000000030000000085102
  | 6, 18 => 0x25504200000000000000700000000000030000000000000000000000000a000000000000b000000000000b0000050484200000000008410700000000000050000000000004000000000000400000000000050000000000004000000000a10000000000411020000000041102000001540a2000000000000006000002148420000000001041000000035085200000000000000700000531052000000000000009000005310520000000254c4201000000000a102000002550020000000058852000000035041200000000000a102
  | 6, 19 => 0xa0000000012100000000000000800000000000070000045081200000000000000a0000000000007000000000000300000204802000000025500200000003500a2000000000006102000000000000e000002048020000000000000070000000006102000004508120100000000c4104000000540a200000000000000900000000000000000040500200000000000000400000000000050000050484200000000000000300000000121000000000000004000002500220100000058c820100000405002000000045484200
  | 6, 20 => 0x4000002044120100000000000060000015480200000000000000a0000004806201000000000000400000000c1102000000000210000000450812000000000000007000005150c2000000002806201000001540a2000000000000007000000000000600000415042000000020480200000004310920000000000c5102000000588520100000324c82020000041504200000003104120000000214842000000000000007000000280620100000000c11020000053105200000001044020000000000000090000035002200
  | 6, 21 => 0x300000000c5102000003500220100000254c0200000002148420000000000000090000000000002000000000000300000000000040000025500200000000000610000000000000060000000000009000000000000c000005048420000000000000070000000085102000000000000600000000c9102000000000a100000000000000500000000000050000045081200000000000000500000504c8200000002544020000000048062010000000000003000000000000a000001548020000000155002000000000000003
  | 6, 22 => 0x400000000c510200000425082000000000000007000004508120100000000000090000053105200000000000000a00000531092000000000000004000000000000400000000000020000000081101000000000000b0000000000004000001540a20100000255002000000000000009000000000210100000425082000000021484200000000000000500000000000010000021484201000000000000700000000411050000000012100000005008520000000454c420000000521052010000025440201
  | 6, 23 => 0x48022000000040500200000000000000700000000000020000000000000000000000000700000000000080000000000004000000000000300000000021000000000000004000000000000900000254c020200000504c820100000000000060000000002100000005048420000000254402010000045480201000000000000300000028022000000052105200000000000000d000004500a200000000010810100000000000050000005881200000000000610000000000000030000000085102000005050c2010000000000007
  | 6, 24 => 0x7000002148420000000000000090000053109201000005210120000000000c11020000015480202000000004010000000058412010000000000005000000000000700000000000090000051081200000000000210000000000000060000051081201000000000000a0000000002102000000000000300000038022010000000000004000002504120000000454c42010000000000002000000000a101000003508520000000254c020100000350852000000000000005000000480a20000000000000090000000000003
  | 6, 25 => 0x540a200000000000000400000214842000000000000003000004508120000000000000000000015480202000000000000c0000000101101000001550020000000430c4200000001548020000000000000040000000000005000000000610100000454842010000000000006000000000000600000314c4202000002500220000000058c8200000000280220100000250062000000000000004000004548020000000000c5102000000000000300000000000030000035081202000004508120100000354802020000041504200
  | 6, 26 => 0x15500200000000000000a0000000000003000005150820100000521012000000005885200000000000000700000204802020000015500201000000000000300000350022000000000101101000000000000d0000000000004000000000000300000350852010000035085200000005048420000000000c8100000000000610000000048022010000020480202000000000000500000000c810700000415042000000000101101000000000000b0000000000005000003508520000000000c910200000000000090000000000003
  | 6, 27 => 0x20000000000002000004500a200000000000000700000104402000000000000000000004250820000000001091010000000000004000003548420200000000c410100000058812010000000041102000000000000300000000000090000025002200000000000000a0000035081201000002544120100000000000060000050484202000000000000a00000000000030000000000006000000010910100000514c82010000000000002000005250c2010000000000005000000000000400000001091010000000000003
  | 6, 28 => 0x8000004250820000000514c8200000000000000500000000000030000035002200000000000000600000504c8202000000008510200000254c02020000050484200000000000000d00000000000020000000000004000000000000300000000c81030000035085201000000010c1000000000000004000000540a201000002048020000000028062000000000000006000002048020200000000000030000001802200000000000000600000430c4201000000000000400000000021000000045484200
  | 6, 29 => 0x505042000000000000006000003500a2000000000000002000005310520100000000000020000000000006000000010c1000000000000004000000000000000000000411020000000000004000000000a1000000000040100000000008110100000000801000000050504200000000000000300000000000030000000000006000001540a2000000000000002000002144120000000155002000000021484200000000000000300000000000070000000006101000000000000300000000c110200000521012010000000000007
  | 6, 30 => 0x1000003508120200000000c5102000000000000a000000000000a000000000000300000000c4101000002550020000000504c8201000000000000900000000c4103000002048020100000254c02020000000000003000000004c104000000180220100000350812020000000000002000000000000700000000000030000000000006000000000000300000504c8200000000000e10000000000000050000000000004000003508520000000254402000000050484201000000000000900000000851000000021484200
  | 6, 31 => 0x500000454c42000000015002200000000000210100000001001010000053109200000000000e1000000050504201000004548420000000000c510200000000000050000000000007000000000000d000004548020000000000000060000000100101000000000000900000000811020000000000002000000000000200000454c420000000001011000000000000000000000500620000000000000050000020480201000000000000700000254c02000000000000009000000000000800000214842020000000085102
  | 6, 32 => 0x50000000000005000000000000a000005048420200000000811010000000000003000000000000000000450812000000040500200000000000e100000000000000300000000000060000035081202000000280220000000504c42000000000000000000000584120100000000000000000000109100000002504120000000415042010000000000006000000000000500000000c410300000000c11020000035081200000000000000a0000000041102000005310520000000000411010000000002102000000000000a
  | 6, 33 => 0xa0000042508200000005310520000000000000020000000000004000000000000700000000000090000000085102000000000000c0000000000006000000000000600000000000050000000000000000000000000b0000035085200000003508520000000154c0200000000480220000000000c8107000000010c10000000304c0202000003508520000000104402000000025500201000000008410000000154802010000000000003000000000000b0000000000008000000000000300000000000090000050484201
  | 6, 34 => 0x1548020200000000000000000045081201000000000000b0000000000009000000000000900000214412010000000041102000005048420000000058c8200000002504120100000504842020000041504200000000000a10000000000000000000000000004000000000000b0000000101100000000000000700000000000050000020480201000000000000400000314c42020000050508201000000000000400000000000030000000000007000000000000d000004548420000000324c820200000104402020000000000000
  | 6, 35 => 0xc51020000000000009000000000000000000155002000000000000007000000000a10200000001011000000000000004000005150c200000000000000300000154c0201000000000a10200000001091000000000000004000004548020000000000000000000000000006000005150c201000003508520000000000000050000000000002000000540a20000000214842000000015480200000000000000400000000c910200000000000020000000000003000000000a101000004250820100000000000060000000000007
  | 6, 36 => 0x8110200000000000000000000081102000000010910000000324c82020000000000006000000000000900000000000090000000000004000000000000300000000811020000000000005000000000a101000000000000b000000000e1020000000085102000000000000400000000c1102000000000000a00000314c42020000000000002000002148420200000531012000000015500200000000000000000000000000070000000000005000004540a2000000052101200000003500a2010000045081201000000000a102
  | 6, 37 => 0x5000000000000d000000480e20000000000c810700000531052000000000000003000002550020100000254c020200000454842000000000000005000000000000e000000000000800000254c0200000005048420000000000000080000000000006000000000000b00000204802000000003802201000000000000400000454c42000000001802200000000380a20000000000000020000000000003000000000000200000254402020000042508200000001548020000000000000040000050484201000000000a102
  | 6, 38 => 0x8000000000000600000405002000000000000004000000000a10100000000000040000000002102000000000000d0000000000005000000000000600000000000030000000000005000000010410100000000c0100000000010110000000000000040000000000005000000000000600000000c1102000004548020000000505042000000000000007000000000000a000000008510200000000000060000000000007000000000000700000450812010000035085200000000000000000000104402010000000000004
  | 6, 39 => 0x411020000000000007000000008510200000415042000000000006102000002148420100000000c9102000000000000500000000c01000000045480200000000000000b00000320c4200000000000000400000155002000000000000004000000000000600000000000090000000000004000002550020000000000c41030000015480200000000000a102000000000000300000454c420000000350412000000000100100000000000000e000000000000d000000000000b0000000000001000000000000500000000c5102
  | 6, 40 => 0x400000450812000000000000003000004150420000000000000030000025041200000000000000a000000000000e00000154c0202000000588520100000000000050000015480200000004548420000000155002000000015480200000000000a101000000000000500000000c9102000000010010000000254412000000000000005000004508120100000000000040000000000003000000000610200000000811020000025006200000000000000d000000000000a000000000000900000000851010000000000007
  | 6, 41 => 0x300000304c020200000454842000000000000004000000000000d00000000c410400000000c51020000000000007000000000000500000000061010000000000005000000000000300000154c0200000000000000900000320c4201000000000a10100000000c41030000000002102000000380620000000000000070000000000003000000000000a0000015500200000001548020100000000000090000000000009000000000000400000531052000000000000003000000000000100000000000050000000000007
  | 6, 42 => 0x20000041504200000000000000200000000c5102000005310120000000000061010000000000003000000010010000000000000040000052105200000000480a2000000000000005000000000000100000504842000000020480200000000000000200000000c410300000000000040000000000004000000000000600000000c510200000405002000000000000006000000000000800000000000030000000000000000004250820000000000121010000000000005000002500620100000000000070000000000003
  | 6, 43 => 0x60000053105200000000000000300000425082000000000000000000001044020000000000000040000015480200000003504120100000310412010000025500200000000000000500000350412000000025504200000000000000500000504c42000000000000007000000000000300000425082000000021441200000004548020000000000000060000000000003000002048020200000000000060000000085102000000380a2010000000000004000000000000a000003548020200000000000030000000000006
  | 6, 44 => 0x480a2010000000000004000000000000d000000000000d000000000000600000254c4200000000000000300000000000040000025500200000000000000700000000000070000020480200000000000000500000000c11020000000000003000000000000400000000000020000000000009000000000000a000003508520000000000811020000000085102000003508520000000000000090000000081100000003508520100000000841070000000000003000000000000000000000000040000000000008000000480e201
  | 6, 45 => 0xb000000000000d00000504c42010000053105201000004548020000000000000020000042508200000000000a1020000035484202000005310520000000000c4103000000000000a000000000000a00000454c820100000454c4200000005310120100000531052000000000000000000000000e1000000000000003000000000000600000204802000000000081100000000000000a000000004c1040000000000007000005210520100000000c410300000454c4200000002544020000000531052000000000000003
  | 6, 46 => 0x2806200000000000000000000000000080000000000009000000004c1040000000002102000000000e100000000000000000000450812000000000002100000000000000500000350812000000000000000000003508520000000415042000000043109201000000000000d0000035085200000000000000200000425082010000000081102000000008410200000000000030000000000004000000000a10000000214842000000000085102000000000610100000000000070000020480200000002550420100000000c8100
  | 6, 47 => 0x2550020100000000000030000020441200000000000000a0000000000005000000000000f000001548020000000000061000000000000004000000000a10000000000411020000004806200000000000000d000000000000200000000841070000000000004000000000000900000000c5102000000000000700000354802020000000000005000000000000e00000254c4201000002550020000000154802000000042508200000000000000100000155002010000000000003000004050020000000000000020000000000003
  | 6, 48 => 0xa00000000000060000045081200000000000000b00000154c0202000000588120000000531052000000015480200000000000000400000504842000000003806201000000000000d0000000000008000002500620000000000000030000000002102000000000000600000000000020000000000005000003548020200000204802000000000000000000003508520000000000000060000003806201000004050020000000000000030000000000008000000000000600000000000080000000000007000003500a200
  | 6, 49 => 0x200000000000020000000081101000000000000300000204412010000000000003000000000000000000104402020000004806201000000000000000000000811010000000085101000000000e10000000504c42000000000000006000000000a101000001548020000000000c51020000000000005000000000000c000000000000a0000000000004000000000000700000000c8107000000000000500000028062010000015500200000000000000500000000000040000041504200000000000000b0000042508200
  | 6, 50 => 0x20000000000006000005048420000000155002000000002802200000000000000000000354842020000000000003000000000000900000254c42000000042508200000000000000e000000000000d00000000000080000031041200000000000a101000000008110100000000c51020000045480200000000000000a00000354802020000000000003000000000000900000454c4200000000000a10200000000801020000000000007000000000000a0000053101200000005050c20000000000000000000045081200
  | 6, 51 => 0x450812010000035085200000005310120000000314c4202000000000000d000000000000a00000000c110200000154802000000052105200000000380a2000000000000005000000000a101000000480a2000000025002201000000380220000000058c820100000048022000000000000007000005150c20000000204802000000000000004000000000000200000028022000000000000002000000000000700000000c5102000002048020000000104402010000000000004000000000000400000000811020000000000004
  | 6, 52 => 0xc9102000000000000700000425082000000045484200000000588520100000000021010000025504200000003548420200000154802020000000000005000000000000900000504c4200000000010c10100000454802010000000084101000000000000300000000c410000000000000060000000002101000005050c201000000000000800000450812000000000084107000003508520000000000000040000000002100000001044020000000000000010000000000006000000000000500000000021010000004802200
  | 6, 53 => 0x61010000000000000000000000000100000514c82000000003802201000005150820000000254c4200000000000000700000255002000000000000000000000000000500000155002000000000000005000000000000a00000531012000000000000002000000000000a00000504c420100000255002000000020441201000000000000500000504c820000000000000090000000000000000000000a101000002500620100000000000030000000000005000000000000400000000000030000000000007000000000000d
  | 6, 54 => 0xc9102000000000000500000454842010000000000008000001550020000000000811000000000000006000000000000300000000000060000045081200000003500220100000000c510200000254c420000000255002010000000041102000000000000500000324c820200000058812000000035081200000000000000e0000025441200000002148420000000514c82000000000000003000005250c200000004150420000000000000090000000000007000000000000900000154c020000000350852000000035484202
  | 6, 55 => 0x30000000000007000000180220000000504c82010000025440201000002148420100000000000050000051508201000003508520000000304c0202000000000a10000000000000050000000081102000000380a201000000000e10200000155002010000000000005000000280620000000454842000000001802200000000000000e0000050508200000000008510200000450812000000000000005000001540a20100000000000030000000006101000000000000a0000045081200000002148420100000000c1102
  | 6, 56 => 0x454c42010000000000006000000000000600000314c420200000254c0201000000000000a00000000000020000000000005000000000000a00000000000050000015500200000002544120000000058812010000000041102000005310520000000000000030000035081201000002044120000000000c5102000000000000a0000025441201000000480e20100000350852000000020480202000000480620000000504c820100000514c8201000005250c201000000000000a000000000000600000204802000000000000005
  | 6, 57 => 0xe1020000000000009000000000000500000000c9102000004050020000000450852000000000000003000000008110000000304c0202000000000000e000000000000b00000000061010000000041102000001548020200000531092010000000084107000000000000b000000000a10100000250062000000050484200000000000a10200000000000030000045480200000000000000100000000000060000050484200000000000000200000000000030000000000006000000000210000000154c02000000000000005
  | 6, 58 => 0x7000000000000600000058412000000035085200000004500620000000000000030000000000004000005050c20000000000000030000000000005000000000000400000000c510200000000000040000053105201000000000a100000000000000300000104402000000000000000000004250820100000000c510200000254c0202000001550020000000000000030000000000005000000000000a0000000000005000002550020000000104402000000000000007000000000000500000000061020000002802201
  | 6, 59 => 0x7000000000000a000000588120100000000021000000000000005000000000000500000000000090000040500201000003508120100000514812010000000000002000000000000a0000000000005000000000000600000000000050000000000006000001548020000000000c410400000000c8107000001548020200000324c82020000000000006000000000a102000005048420000000000c81030000000000003000000000000600000531052000000000081100000004548020000000454c42000000035085201
  | 6, 60 => 0xa00000000411000000000000004000003508520100000000000060000021484200000000000000b000000540a201000001548020000000000c41030000000000007000005050820000000000c5102000000000000a000003508520000000430c420100000214842000000000081102000000000000a00000038062010000000000003000000000000a000004508120000000000000000000000000007000000000000b0000000084107
  | 7, 0 => 0x41102000000000000d000000000e10200000000000070000000000009000000000000400000001091000000000000007000000001210000000000000070000000000005000000000000400000001051000000000000005000000000000a00000000c41000000000000004000000000a100000000010c1000000000084100000000000000d00000000000020000000101100000000000a100000000000000000000000c4102000000000000200000000c510200000000811000000000085100000000010510000000000c4102
  | 7, 1 => 0x300000000000070000000000005000000000e100000000010c100000000000a10200000000811000000000000003000000000e10000000000000070000000108100000000000a1000000000006100000000000000e000000010c1000000000000003000000008410000000000061000000000000002000000000210200000000c510200000000c410000000000000020000000000000000000000000900000000000020000000002100000000000000400000000411000000000000007000000000610000000000c8101
  | 7, 2 => 0xd0000000000003000000000a10000000000c010000000000811000000000000003000000010010000000000000030000000080100000000000210000000000021000000000000000000000000000600000000000070000000000001000000000210000000001081000000000000003000000000a10000000000c41000000000000001000000000e1020000000000007000000000000400000000000050000000000004000000004110000000000000010000000012100000000000000500000001011000000000000002
  | 7, 3 => 0x2000000000610000000000851000000000000004000000010410100000000c410000000000000090000000000004000000000000400000000851000000000101100000000000000500000000000020000000000003000000000000e0000000108100000000000000e00000000401000000000000000000000000000200000000000060000000000006000000004010000000000000070000000000003000000008010200000000061000000000002100000000000e10100000001001000000000000004000000000e100
  | 7, 4 => 0x40000000101100000000000000d000000000000400000000c410200000000c810000000000000040000000012101000000000000600000000061020000000081100000000000000300000000000070000000108100000000000000400000000411000000000006100000000000000400000000000030000000000000000000000000700000000000040000000109100000000008010000000000000040000000000002000000000a10000000000021000000000085102000000008010000000001051010000000000006
  | 7, 5 => 0x21000000000000003000000000a102000000000e1020000000000007000000000a10100000000000030000000000007000000000000d0000000109100000000000210200000000411000000000000002000000010c100000000000210000000000000030000000084100000000000000200000000000020000000006100000000010c1000000000084100000000010510000000000021000000000000004000000000a100000000000000000000000811020000000104100000000000610000000000c51020000000000004
  | 7, 6 => 0x12100000000000a100000000010c100000000000a100000000000000000000000c8102000000000a1020000000085102000000000000400000000000030000000041100000000008510000000001001000000000000004000000000210200000000401020000000000004000000000000500000000000000000000040100000000010810000000000c01000000000105100000000000000800000000c5102000000000e102000000001210100000001041000000000000005000000000610000000000c41000000000012100
  | 7, 7 => 0x30000000081102000000000a100000000010010000000000000070000000000003000000008010000000000c410000000000c9102000000000610000000000000080000000000007000000004010000000000801000000000000000000000000000000000000c0100000000000e1020000000109100000000004010200000000000030000000000007000000000a1020000000000002000000001210000000000c010200000000000040000000000000000000000e102000000010010000000000121000000000000003
  | 7, 8 => 0x851000000000000004000000000a100000000000000300000000000020000000006101000000010110000000000c41000000000000002000000000000d00000000000040000000000003000000000000200000001011000000000012100000000000000700000001051000000000041100000000000610100000000000070000000104100000000001210000000000c010000000000000020000000006102000000008410200000000c81000000000006102000000010c100000000008410000000000811020000000000005
  | 7, 9 => 0x40000000002100000000000000600000000000050000000000007000000000000800000000000030000000000006000000000000200000000c8102000000000610000000000c810000000000000020000000006102000000000000700000000000040000000000000000000004110000000000021010000000000000000000010910000000000000080000000012100000000000210200000000000030000000000006000000010910000000000000070000000081100000000010510000000000811020000000006100
  | 7, 10 => 0x4000000000000d00000000c41000000000006100000000010810000000000c8102000000000610000000000c81000000000012100000000010510000000000801020000000100101000000000000300000000000060000000002100000000008510100000000801000000000104100000000000a10000000000c410000000000021020000000002100000000000e100000000000210200000000000040000000081101000000000a100000000000a1020000000084100000000004010100000000000030000000000003
  | 7, 11 => 0x851000000000000004000000000210100000000411020000000040100000000000e10000000001001000000000002100000000008510200000000c1102000000000000d000000000000200000000000050000000101100000000010010000000000401000000000012100000000000a100000000000a10200000000c0100000000000000700000000401020000000000003000000004110000000000c01000000000006102000000000000a00000000841000000000000003000000000000000000000000050000000000002
  | 7, 12 => 0x70000000000005000000000a10100000000841010000000000003000000000000900000000000040000000000007000000000000900000000401000000000105100000000000a10000000000000020000000000007000000008110100000001041000000000006100000000000610200000000c91020000000101100000000010c10100000000841010000000109100000000010810100000000121000000000000007000000010c1000000000104100000000000000600000000000020000000000003
  | 7, 13 => 0x8410200000000000070000000000003000000000210000000000000040000000000002000000000000200000001041000000000000004000000000210000000000000000000000006101000000000000500000001051000000000000002000000010c100000000008410000000000c81000000000104100000000001210000000000000020000000000005000000008410200000000c810000000000000030000000000004000000000000900000000000070000000006100000000000000700000000121000000000085100
  | 7, 14 => 0x2000000010410000000000c410000000000000020000000105100000000000000000000000000070000000000006000000000000700000000401000000000000009000000000000600000000000030000000012100000000004110200000000c01020000000000007000000008010100000000000030000000100100000000010c1000000000084100000000000a1000000000000002000000001210000000000811000000000000003000000000000600000000c010000000000411000000000000004000000000000e
  | 7, 15 => 0x121000000000108100000000000000300000000c0101000000000000a00000000000040000000041100000000008010000000000c5102000000004110200000000000030000000012100000000000000700000000c41020000000080102000000000210000000000000030000000109100000000000000900000001011010000000000006000000000000500000000000040000000000000000000000e10000000000000040000000000003000000000a1000000000006100000000010510000000000000070000000085100
  | 7, 16 => 0xa1000000000105100000000000000200000000000030000000000005000000000000200000000021000000000080100000000010c1000000000000003000000000000700000000841000000000101100000000000000400000000c1102000000000a1000000000000004000000000e1020000000000004000000000000d00000000c41010000000000003000000000210200000000000020000000041100000000008510000000000c810000000000000000000000000003000000000210000000001091010000000000006
  | 7, 17 => 0x700000000c010100000000000030000000000003000000000000300000000061000000000002100000000000e102000000010110000000000000030000000081100000000000000700000000851000000000000007000000000a1020000000000007000000000000200000000061000000000000002000000001210000000001091000000000085100000000000610000000000000020000000000004000000000000200000000c910200000000000030000000000007000000004110100000000061000000000040100
  | 7, 18 => 0x50000000000001000000010810100000000c0100000000000000300000001001000000000000005000000000000200000000851000000000080100000000000a100000000000210000000000000070000000081100000000010c1000000000002100000000008410000000000000040000000040100000000000000600000000c51020000000000006000000000000300000000c4102000000000000600000000000020000000100101000000000000300000000000030000000109100000000000e1000000000000005
  | 7, 19 => 0x200000000061020000000000004000000000000500000000c410000000000c8101000000008510000000001011000000000000009000000000a100000000000000e000000000000a0000000000003000000000000700000001051000000000040100000000000610000000000c5102000000000000700000001041000000000081100000000010010000000000c4102000000000000400000000000060000000000005000000000000600000000c010200000000000050000000000006000000000e1020000000108100
  | 7, 20 => 0x900000001051010000000000003000000000000300000001041010000000081100000000000000600000000411000000000006100000000000e1020000000000006000000010c1000000000084100000000000000900000000000050000000109100000000010010000000000000020000000108100000000000210000000000000040000000012100000000000e1020000000000008000000000a10200000000c0100000000000000600000000000030000000006102000000000a10000000000c81010000000002100
  | 7, 21 => 0xc11020000000040102000000000000d0000000012100000000000e10200000000851000000000012101000000000000a0000000000006000000010c10000000000841000000000109100000000000a100000000000000500000000000040000000040100000000000a102000000000000700000000000060000000000004000000000000700000000c8100000000000000500000000801000000000000006000000000a100000000008410000000000000050000000002102000000000000200000000000050000000000001
  | 7, 22 => 0x30000000000006000000000000400000000c4100000000000e100000000010c100000000008410000000000000030000000000003000000001210100000000061020000000080100000000000000800000001001000000000109100000000000a1010000000081100000000000000200000000c0100000000000000800000000000070000000081100000000000000300000000c8100000000008510200000000000050000000000004000000000e10100000001011000000000000007000000000000c0000000006100
  | 7, 23 => 0xc810000000000000040000000000007000000010910000000000000060000000000007000000000e100000000000000a0000000000004000000010810000000000c0100000000000000200000000000070000000108100000000004110000000000061000000000000004000000000610200000000000030000000041102000000000000e00000000021000000000000007000000000210200000000000000000000080100000000010110000000000000070000000000002000000008410200000000021000000000000006
  | 7, 24 => 0x1091000000000041100000000000000400000000061010000000081100000000000000d000000000000500000000000040000000080100000000008510200000000021000000000002102000000000000200000001001000000000000004000000000a10000000000000040000000000003000000000000300000001011000000000040102000000000a10000000000000060000000000000000000010510000000000c410000000000c010000000000000050000000000005000000010410000000000851000000000000002
  | 7, 25 => 0x50000000101100000000000a1000000000000003000000000000300000000c0100000000000a1000000000000004000000000210000000000121000000000002101000000000000500000000851000000000000003000000008510200000000000010000000080102000000000000200000000000030000000000004000000000000700000000401000000000040102000000000000600000000000070000000006100000000010410000000000801000000000006100000000010110000000000121000000000081102
  | 7, 26 => 0xc01000000000000005000000000000300000000000070000000000003000000000000600000000c81020000000000003000000010910000000000401010000000000006000000010810000000000c1102000000000000500000000000020000000000001000000001210000000000000020000000002102000000010010000000000000050000000000006000000000000000000000000020000000000004000000000000200000000021000000000000002000000000e10000000000c810000000000841020000000000003
  | 7, 27 => 0x700000000c810000000000061020000000000007000000000610000000000c410000000000c8100000000000000400000000c41000000000000002000000000000000000001051000000000104100000000000000600000000000050000000000007000000010c10000000000841000000000000002000000000a102000000008410200000001001000000000080100000000010810000000000c9102000000000a100000000000000600000000000070000000000007000000000000400000000851010000000000004
  | 7, 28 => 0xa100000000000000500000000000040000000000002000000000000200000000000040000000000003000000000000e0000000100100000000008110000000000c810000000000000060000000105100000000008110100000001041000000000000007000000000e101000000000000d0000000041100000000000610000000000c01000000000000008000000010c10100000000000030000000084101000000001210000000000411000000000000003000000008010200000000c810000000000000060000000012100
  | 7, 29 => 0xc1102000000000000300000001081010000000040100000000000000300000000c010000000000000060000000000005000000000e1000000000002101000000000e10000000000c91020000000000003000000008110000000000c81020000000000006000000001210000000000811020000000012100000000000000d00000000000010000000000002000000000a10000000000121000000000080100000000000210000000000801020000000000003000000000000800000000c010200000000c11020000000000003
  | 7, 30 => 0x411020000000000007000000000000900000000411000000000000006000000000000900000000021000000000109100000000000a1020000000002102000000000000200000000c91020000000080101000000000a101000000000e10000000000121000000000081100000000000000600000000000020000000000005000000000000700000000801010000000000003000000000000400000000000020000000085100000000000210000000000c4100000000000000800000000c8100000000000a1000000000101100
  | 7, 31 => 0x104100000000000610000000001051000000000109101000000000000300000000411000000000000005000000010c100000000010410000000000c0102000000008410000000000021000000000000007000000000000d0000000000004000000000a100000000000610100000000000000000000000003000000000a102000000000610000000000000020000000000005000000000610100000000000030000000000006000000010110100000000c41000000000108100000000000000a000000000000800000000c8102
  | 7, 32 => 0x40000000000005000000010010000000000c0102000000001210000000000000050000000006100000000000000300000000000030000000081100000000000a1000000000000003000000000000300000000000040000000012100000000000000000000000c01000000000000004000000000610000000000000040000000000002000000000000300000000000090000000002100000000000610200000000000030000000000004000000000000d000000000e10000000001081000000000105100000000000000e
  | 7, 33 => 0x70000000040100000000001210000000001001010000000000002000000008010000000000c41010000000002100000000001210000000000000030000000040101000000000000200000000c4100000000000000000000000c0101000000000a10000000000021000000000000003000000000210000000000000040000000000004000000000a1000000000085100000000000610000000000000020000000108100000000000000000000000000020000000000005000000000000500000000401000000000000002
  | 7, 34 => 0x4110100000000000040000000104100000000000000d0000000000005000000000000700000000000010000000000006000000000000400000000c810000000000000020000000040100000000000000800000001081000000000000003000000000000e00000000000040000000000002000000000000e
  | 8, 0 => 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000002000000000000200000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_6 roots_6 8 s ws hint
  | 1 => checkCutEntry dom_15 roots_15 8 s ws hint
  | 2 => checkCutEntry dom_19 roots_19 7 s ws hint
  | 3 => checkCutEntry dom_21 roots_21 6 s ws hint
  | 4 => checkCutEntry dom_22 roots_22 6 s ws hint
  | 5 => checkCutEntry dom_23 roots_23 6 s ws hint
  | 6 => checkCutEntry dom_20 roots_20 5 s ws hint
  | 7 => checkCutEntry dom_8 roots_8 5 s ws hint
  | 8 => checkCutEntry dom_16 roots_16 5 s ws hint
  | 9 => checkCutEntry dom_25 roots_25 5 s ws hint
  | 10 => checkCutEntry dom_26 roots_26 5 s ws hint
  | 11 => checkCutEntry dom_14 roots_14 4 s ws hint
  | 12 => checkCutEntry dom_18 roots_18 4 s ws hint
  | 13 => checkCutEntry dom_24 roots_24 4 s ws hint
  | 14 => checkCutEntry dom_0 roots_0 4 s ws hint
  | 15 => checkCutEntry dom_17 roots_17 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_27 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_22 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_26 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_27 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_27 == dom_27) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_27 goalM u ys) : RunD dom_27 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_27 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := z4_0
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
theorem z6_176 : ∀ i, 176 ≤ i → i < 180 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 176 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 180 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (z6_176))))))))))))))))))))))
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
theorem z7_208 : ∀ i, 208 ≤ i → i < 209 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 208 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 209 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (z7_208))))))))))))))))))))))))))
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
  scr dom_27 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_27 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_27 roots_27 goal_27 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_27 goal_27 := by
    have h0 : isConstB dom_27 goal_27 = false := by decide +kernel
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

end S_27

theorem low_27 : Lower dom_27 roots_27 goal_27 10 := S_27.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_27_bits : ∀ r : Fin 64, roots_27.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_27_lt : ∀ r : Fin 64, dom_27.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_27 T)
    (hlow : Lower dom_27 roots_27 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_27, Avail mask256 roots_27 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_27 hfan 0 roots_27 roots_27 rfl hsup0
  set out := (execN C.gates roots_27).getD C.output 0
  have hout : out &&& dom_27 = T &&& dom_27 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_27_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_27 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_27_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_27).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_27)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_27.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_27 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_27).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_27 &&& mask256 = dom_27 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_27 = T &&& dom_27 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_27, hd63, hout]
  have hnc_m : ¬ IsConst dom_27 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_27 roots_27 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_27, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_27 roots_27 0 roots_27 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_27.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_27 10 hT6 (by unfold IsConst; decide) low_27

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [7, 4]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [7, 5]⟩, ⟨GateOp.and, [9, 3]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.and, [14, 12]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_16643_aux

theorem PEqualNP.Outside.L_meta_16643 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_16643_aux.wit, PEqualNP.Outside.L_meta_16643_aux.wmono, le_trans PEqualNP.Outside.L_meta_16643_aux.wsize (PEqualNP.Outside.L_meta_16643_aux.lower s hs), PEqualNP.Outside.L_meta_16643_aux.weval⟩
