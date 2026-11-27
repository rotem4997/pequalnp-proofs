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

namespace PEqualNP.Outside.L_meta_13135_aux

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

def dom_0 : Nat := 0xf0f0f0f0f0f0f0f
def goal_0 : Nat := 0xe0e0e000e0a0c00
def roots_0 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(1, 17), (2, 10), (3, 11), (3, 19), (8, 10), (9, 11), (9, 25), (9, 41), (16, 17), (18, 19), (18, 26), (18, 50), (24, 25), (24, 26), (33, 41), (33, 49), (34, 42), (34, 50), (35, 43), (35, 51), (40, 41), (40, 42), (48, 49), (48, 50), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 2, 3, 3, 8, 9, 9, 9, 16, 18, 18, 18, 24, 24, 33, 33, 34, 34, 35, 35, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [17, 10, 11, 19, 10, 11, 25, 41, 17, 19, 26, 50, 25, 26, 41, 49, 42, 50, 43, 51, 41, 42, 49, 50, 57, 58]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 4
  | 4 => 13
  | 5 => 13
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x7cc4bc55
  | 3, 0 => 0xbf461d0b3dcbee230b6748890123779e
  | 4, 0 => 0xc38274819a28898069369245585fd0b3410d737d2fd455da26f145cd26bc2b5e1ba5db2b0b59138309710d2b061f7558026c8c29
  | 5, 0 => 0xeaaab64ac3827481a4e072978ea8457e72783b7e6c35459f5a3c9a365878c3dd418db97037f8ccf42a5942f414d4acce006bb7a1
  | 6, 0 => 0xc3827481
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xc0c00000c0c00000c000c000c000c000a0a0a0a0a0a0a0a0a0a0a0a000000000a0a00000a0a0000050505050505050500000f0f00000f0f000000000f0f0f0f
  | 0, 1 => 0xe0e0e0e0e0e0e0e0e0e0e0e0a0a0a0a0e0e0e0e000000000e0e0c0c0e0e0c0c0e000e000e000e000c0c0c0c0c0c0c0c0c0c0c0c0c000c000c0c0c0c00000000
  | 0, 2 => 0xf0f0a0a0f0f0a0a0f0f0a0a000000000f0f00000f0f00000f0f00000a0a00000f0f0000000000000f0c0f0c000000000f000f000f000f000f0000000f000000
  | 0, 3 => 0xf0f0f0f0f000f000f0f0f0f0a0a00000f0f0f0f080808080f0f0f0f000000000f0f0f000f0f0f000f0f0f000f0f00000f0f0f000f000f000f0f0c0c0f0f0c0c
  | 0, 4 => 0xf0f0f0f0f0f0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x1a2453
  | 3, 0, 0 => 0x75544f4552185481928545112844
  | 4, 0, 0 => 0x1c551285575544a155c54b285571544e295c551305579544a155c5d1283571b40a155544d285559544a155c6111c5581344a155c5512455
  | 5, 0, 0 => 0x1544a140501c551285571b551285671544a1c56718551285671544a2056717551285671544a18567dc551285601c44a141571544a142671544a14067154502856
  | 6, 0, 0 => 0x1c5512855
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
  | 0, 0 => 0x380000000003303b40cc0000000003f33f120ff03fc003fff
  | 0, 1 => 0x3f3bbc0fc0ed03f00000f0e0e00003800f0e0e03c00000f0000
  | 0, 2 => 0xf33ffb7ccc000f00fc03c00000f0000033f0000cc0c3c3003000
  | 0, 3 => 0xfffc3c3ffc000fff0033ffc000fc0ffc3f03f00fc0c3c3cf3f0e
  | 0, 4 => 0x3ffff00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xa28b8222524365734fb55cc0805224d26a32c120d502d800377f
  | 0, 1 => 0xfffffffffdbedfff2203efbf7fcd5d3daaf2e3eabcb0daaf0800
  | 0, 2 => 0xf7bffb7dec880f2afd27ca9b49f2a2003bf4880cd5d3db003440
  | 0, 3 => 0xffff3dbffdbc9fff2ab3ffc880fffffffffffc9ffff3dbefbf7f
  | 0, 4 => 0x3ffffc9
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 33 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 33 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 33 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 33 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_0 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_0 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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
  scr dom_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_0 roots_0 goal_0 7 := by
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

theorem low_0 : Lower dom_0 roots_0 goal_0 7 := S_0.noCircuit

def dom_1 : Nat := 0x333300000000
def goal_1 : Nat := 0x322000000000
def roots_1 : List Nat := [0x222200000000, 0x303000000000, 0x330000000000]

namespace S_1
def pairsG : List (Nat × Nat) := [(33, 37), (33, 41), (36, 37), (36, 44), (40, 41), (40, 44)]
def r1sG : List Nat := [33, 33, 36, 36, 40, 40]
def r2sG : List Nat := [37, 41, 37, 44, 41, 44]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xee06ffbf
  | 3, 0 => 0xee06ffbf
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33000000000000003030000000000000222200000000
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
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
def goal_2 : Nat := 0x322000003020
def roots_2 : List Nat := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x333300000000, 9, 41)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0x5555
def goal_3 : Nat := 0x5440
def roots_3 : List Nat := [0x4444, 0x5050, 0x5500]

namespace S_3
def pairsG : List (Nat × Nat) := [(2, 6), (2, 10), (4, 6), (4, 12), (8, 10), (8, 12)]
def r1sG : List Nat := [2, 2, 4, 4, 8, 8]
def r2sG : List Nat := [6, 10, 6, 12, 10, 12]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_3.map (· &&& dom_3)
def goalM : Nat := goal_3 &&& dom_3
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xb533a08
  | 3, 0 => 0xb533a08
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x550000000000000050500000000000004444
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_3 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_3 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_3 == dom_3) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_3 goalM u ys) : RunD dom_3 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_3 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_3 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_3 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_3 roots_3 goal_3 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_3 goal_3 := by
    have h0 : isConstB dom_3 goal_3 = false := by decide +kernel
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

end S_3

theorem low_3 : Lower dom_3 roots_3 goal_3 4 := S_3.noCircuit

def dom_4 : Nat := 0xffff
def goal_4 : Nat := 0xfce0
def roots_4 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

theorem low_4 : Lower dom_4 roots_4 goal_4 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa, 4, 5)] (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0x555500000000
def goal_5 : Nat := 0x544000000000
def roots_5 : List Nat := [0x444400000000, 0x505000000000, 0x550000000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_6 : Nat := 0xffff00000000
def goal_6 : Nat := 0xfee000000000
def roots_6 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa00000000, 36, 37)] (by decide +kernel) (by decide +kernel) low_5

def dom_7 : Nat := 0xffff0000ffff
def goal_7 : Nat := 0xfee00000fce0
def roots_7 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

namespace S_7
def pairsG : List (Nat × Nat) := [(1, 5), (2, 6), (2, 10), (3, 7), (3, 11), (4, 5), (4, 6), (4, 12), (8, 10), (8, 12), (9, 11), (9, 13), (9, 41), (33, 37), (33, 41), (34, 38), (34, 42), (35, 39), (35, 43), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [1, 2, 2, 3, 3, 4, 4, 4, 8, 8, 9, 9, 9, 33, 33, 34, 34, 35, 35, 36, 36, 36, 40, 40, 40]
def r2sG : List Nat := [5, 6, 10, 7, 11, 5, 6, 12, 10, 12, 11, 13, 41, 37, 41, 38, 42, 39, 43, 37, 38, 44, 41, 42, 44]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_7.map (· &&& dom_7)
def goalM : Nat := goal_7 &&& dom_7
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 6
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xf71dac53
  | 4, 0 => 0x7b074be34fada6a40fdea189
  | 5, 0 => 0xf641318cb7253fbd6949f7d6686e9bda5ba073fa0da784ce
  | 6, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfccc0000fccc0000faaa0000faaa0000f0f00000f0f00000f0000000f0000000cccc0000cccc0000aaaa0000aaaa00000f0f00000f0f000000ff000000ff
  | 0, 1 => 0xffff000000000000fff00000fff00000ff000000ff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa9724
  | 4, 0, 0 => 0xa86535a94325a87525
  | 5, 0, 0 => 0xa53205a853216a985326a8543260a83215a853206
  | 6, 0, 0 => 0xa85325
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3c00f019f0647001c000000003c00f019f0678ffe3e3fe0ff
  | 0, 1 => 0x7ff8003f03fc1c01f00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xdbc7ef5b9fae67555d7200a804bc2af139f0e58aaa281aa06b
  | 0, 1 => 0x7ffc003ffffffe55f94
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
  | 4, 0 => 0xff998d69e7f01270e594e3d0db55ef26947e0d9e1412d30a0f1fce07
  | 5, 0 => 0xf11b066ee9082d54e505bdfaaf799c90af535e0eaf12d875a7da18faa1c0b4b8a1712e8ba12a17a39f39fa5295fc1c0b92b6c7608c5e12728888432e7ea52a9a7445a6b572657d5c6b7180a36594bfe25b61388b55c13d20530ab5464d7877b9391be2b22fef2b28270b03de160058940f1fce0708214818
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x10000000000200000c0000100000800000
  | 5, 0 => 0x4000000000000000100000c0000000000c0000100000c0000000000000000000004000010000000000100000c000000000000000000000c0000000000800003000004000010000040000100000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 1 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 2 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 3 => checkCutEntry dom_3 roots_3 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_7 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_7 == dom_7) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_7 goalM u ys) : RunD dom_7 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_7 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_7 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_7 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_7 roots_7 goal_7 7 := by
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

theorem low_7 : Lower dom_7 roots_7 goal_7 7 := S_7.noCircuit

def dom_8 : Nat := 0x55550000
def goal_8 : Nat := 0x54400000
def roots_8 : List Nat := [0x44440000, 0x50500000, 0x55000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 4 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_9 : Nat := 0xffff0000
def goal_9 : Nat := 0xfeea0000
def roots_9 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000, 16, 17)] (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0x33333333
def goal_10 : Nat := 0x32223020
def roots_10 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

namespace S_10
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (4, 5), (4, 12), (8, 12), (9, 13), (9, 25), (16, 17), (20, 21), (20, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [1, 1, 4, 4, 8, 9, 9, 16, 20, 20, 24, 24]
def r2sG : List Nat := [5, 17, 5, 12, 12, 13, 25, 17, 21, 28, 25, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_10.map (· &&& dom_10)
def goalM : Nat := goal_10 &&& dom_10
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x13ac53d7
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000000000003300330000000000303030300000000022222222
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

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_11 : Nat := 0xff00ff
def goal_11 : Nat := 0xea00e0
def roots_11 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

theorem low_11 : Lower dom_11 roots_11 goal_11 4 :=
  lower_iso [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10

def dom_12 : Nat := 0xffffffff
def goal_12 : Nat := 0xfeeafce0
def roots_12 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_12
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (2, 6), (2, 10), (3, 7), (3, 11), (3, 19), (4, 5), (4, 6), (4, 12), (8, 10), (8, 12), (9, 11), (9, 13), (9, 25), (16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 8, 8, 9, 9, 9, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [5, 17, 6, 10, 7, 11, 19, 5, 6, 12, 10, 12, 11, 13, 25, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_12.map (· &&& dom_12)
def goalM : Nat := goal_12 &&& dom_12
def NN : Nat → Nat
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xfd575aab93c0f7228c616cec5299e96d30706e42
  | 6, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffccffcc00000000ff00ff0000000000fcfcfcfc00000000f0f0f0f000000000cccccccc00000000aaaaaaaa000000000f0f0f0f0000000000ff00ff
  | 0, 1 => 0xffff0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x86432168654326084320508632158764326
  | 6, 0, 0 => 0x864325
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe3be3e701f0007e07f838038003803e001c1cf8ff8fe3f83ff
  | 0, 1 => 0x1ff8000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfbbfbe791f8a37e7ffb3a2b954b8abe127c3cd8ba8d41b81d7
  | 0, 1 => 0x1ffc042
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
  | 4, 0 => 0xac05225e81ea162e5e1d4aa81f7c8e900e1c2916
  | 5, 0 => 0xfed79471f27aa6a5d051f507c5159104ba7741d8ac05225eaa294541a0508cfd818360617ecfa1837702c5a9554c825e3a6b8d412b0e7274276bea4325303d37206585ea1b8a7ef1126b25b70241d3e1
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0xc0000400000c00000
  | 5, 0 => 0x2000008000000000000000000000800002000000000030000000000000000800001000000000040000080000000000c00000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 1 => checkCutEntry dom_9 roots_9 5 s ws hint
  | 2 => checkCutEntry dom_3 roots_3 4 s ws hint
  | 3 => checkCutEntry dom_10 roots_10 4 s ws hint
  | 4 => checkCutEntry dom_11 roots_11 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_12 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_12 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_12 == dom_12) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_12 goalM u ys) : RunD dom_12 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_12 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_12 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_12 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_12 roots_12 goal_12 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_12 goal_12 := by
    have h0 : isConstB dom_12 goal_12 = false := by decide +kernel
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

end S_12

theorem low_12 : Lower dom_12 roots_12 goal_12 7 := S_12.noCircuit

def dom_13 : Nat := 0x5555555555555555
def goal_13 : Nat := 0x5444544054405440
def roots_13 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000055550000, 34, 50), (0x5555555500000000, 18, 50)] (by decide +kernel) (by decide +kernel) low_3

def dom_14 : Nat := 0x3333333333333333
def goal_14 : Nat := 0x3222322032223020
def roots_14 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000033330000, 1, 17)] (by decide +kernel) (by decide +kernel) low_2

def dom_15 : Nat := 0x5555000055550000
def goal_15 : Nat := 0x5444000054400000
def roots_15 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 18, 50)] (by decide +kernel) (by decide +kernel) low_8

def dom_16 : Nat := 0xffff0000ffff0000
def goal_16 : Nat := 0xfeee0000feea0000
def roots_16 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa0000, 16, 17)] (by decide +kernel) (by decide +kernel) low_15

def dom_17 : Nat := 0x5555555500000000
def goal_17 : Nat := 0x5444544000000000
def roots_17 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 5 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def dom_18 : Nat := 0xffffffff00000000
def goal_18 : Nat := 0xfeeefee000000000
def roots_18 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000, 36, 37)] (by decide +kernel) (by decide +kernel) low_17

def dom_19 : Nat := 0xff00ff00ff00ff
def goal_19 : Nat := 0xee00e000ea00e0
def roots_19 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00ff00000000, 18, 50)] (by decide +kernel) (by decide +kernel) low_11

def dom_20 : Nat := 0xffffffffffffffff
def goal_20 : Nat := 0xfeeefee0feeafce0
def roots_20 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_20
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (2, 6), (2, 10), (3, 7), (3, 11), (3, 19), (4, 5), (4, 6), (4, 12), (8, 10), (8, 12), (9, 11), (9, 13), (9, 25), (9, 41), (16, 17), (18, 19), (18, 22), (18, 26), (18, 50), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (33, 37), (33, 41), (33, 49), (34, 38), (34, 42), (34, 50), (35, 39), (35, 43), (35, 51), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 8, 8, 9, 9, 9, 9, 16, 18, 18, 18, 18, 20, 20, 20, 24, 24, 24, 33, 33, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 40, 40, 40, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 17, 6, 10, 7, 11, 19, 5, 6, 12, 10, 12, 11, 13, 25, 41, 17, 19, 22, 26, 50, 21, 22, 28, 25, 26, 28, 37, 41, 49, 38, 42, 50, 39, 43, 51, 37, 38, 44, 41, 42, 44, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_20.map (· &&& dom_20)
def goalM : Nat := goal_20 &&& dom_20
def NN : Nat → Nat
  | 2 => 1
  | 3 => 11
  | 4 => 71
  | 5 => 244
  | 6 => 615
  | 7 => 419
  | 8 => 30
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x9d740531
  | 3, 0 => 0xde2bf613d00b1c2bc6c8e104b68a034596c3527c8f7f49a4881f6adb84dd0fd7835e3629530d2451490fd720
  | 4, 0 => 0xea5d3232d43955b5d0e7739fcfe67b1ecbd5d5adca968169ca825a99c7d8c0ecc216609ec0a7682ebb8af7cbb6257f57b5f54d23b055cd44b00c0033a88bb445a80e8944a09b316a90aaca5b8e3581098d2632798c6806218ad580e68a38ce7c857886c684c3f0b58472e7d37f2e0b957e824ad87a381eb476d49f2575cf003275697a9c738263e76ca28b676ca155586b0ba6086924c7376276caee5b192d2557749a9b532825c34e6dd5714d12605a49c6f173490fd72048a494dd3a6bef7f38a1e0ab32608c062fbf3bcb24bd6cd81f85c2ff1efe081b1eedf8d51d3a9bfb191cfd1916ec3f35156ba229122dec6108a93f0a063c531801936e8c00adddc3
  | 4, 1 => 0xfce32bb1fa87942cf8858f27f2ebd26ef20cd202f09c946bec39ac90
  | 5, 0 => 0x3c9e47f73c4d5af13ba5ffb23a90924d3a792f6a39aaaf12393c1802392da9a93584e75835669d793534a6a83492314e346f56d533252d9d318d0df431315a0530f871e33016446b2de725212c7ddac72c63130b29daf2982800253a27f87318268dd86d2593a42423249a2621fab4be20d2fd1f20ba890320942f291eedd9fc1e58da191dd8257d1c58f30b1bd606951ae1c6821a10f6e519d2733e179c964d17603fa516e279ed167df75e15873acf1563d79a14d3ff53144e3c761191e69f108b31050fecc0fa0fce77530bf8a62e0bb0d3750b8c81980abfc79c0a6c0c6909debc7408ea0cab084a588003ff4e230375b19801a4edb200e45e9700e3221d
  | 5, 1 => 0x7d95439a7ce3060d7bb0128c79c0a36378890f6f770616a076e5267c755bd48f750c721872db50be725681b570c527e0709436206ff542016d575eb46c6ee1ed6a105c9f6611101764d38e9763d55b9f6304355561ec630f5e6364645e2d8aab5dd77c0e5d8ec6855d3757a85c5c76085ae34b1f5ad838e959f9f29a59eaad435967c8f756c4733f554f1f0054da595854820f6152265ca14f83e1b74f7c60744f5417114f03da4e4ef9742d4eb19c7e4dc981a44c60b3d94b4b41674af78f914abe883d4abb1d6f4a5b44d349b8c60148ac4e2c4873117a48388c284650aa0245a878b244c5769f4235772a420642cc41c57bfc40e31f3840d2b7803d163d49
  | 5, 2 => 0xc0f96166c0226483bba4d4e3bb018765ba48e8d1b9eaf900b94bb5b3b7f6aad7b76c2ea2b47e9f86b42e327eb3e59aeeb322a4d7b313dfb3b2b79c1ab26c55d6b1078e10afe83168afd756daaf527550aed0e464aace425caac1fc64a890ecd1a8009196a7ebb6f8a73bd05ca6db69e1a6cf7961a67f94aba5f746f4a55e26eaa47ee62b9f7526dd9eee94429e2df3f59cd18ffa9740e88f9686bbc796638ec594d05cba9373f08592e9407390a4c65c8ed4e3968db0441f8d4d107c8d0d68078c9463de8b7e349089bfe5948938e0ef88d474618763c658868b359184b83562841028b683f82383839c0c6882b370817edb443f7e67432c7e12f27f7d9e2cd7
  | 5, 3 => 0xff326ce9f9fc33f7f9a1b173f72c1ac9f5d8948cf280d167f17347f3f1713d7ff09ba6c7efbda0a8ef4205daeec94adcee9b9288ee0fb87be6b72a29e6250d17e43742f3e38b8236e2e8d2a2e29d6ae0e1e87bb3e03b0db4df415612de160a38dce8ce41dbddd683dad83790da6f60a5d927ff99d8810550d7717168d1abc2c5d0dc8135cf88cc23cf2180a7ce21fa69cd129f25cc28719fcb74c0cec9c2af35c928ce25c87716afc7b267c1c6dc7213c6c3fdf7c6a5c670c65db2c7c60c4a4cc5efb17fc406e7abc2f2b812c194ef38
  | 6, 0 => 0x1c6af0321c53915b1bfe84a81b9386ad1b86a0301b16f5ed19ff9c8019e5257c19ba301a18eed24c18572418181c0a6c17ae9e2a17a712b017a61d62173643a816446b9c1621e04314f168c61432396c13d6d81d13be640112ee238212bbd30812baa67711b9e05611a579d6118eca211161181a1144e41f10aeb074104ef361102400b2101595880fcb33c20edf18670ea8faac0dd633720dcab45d0d9dd24c0cd7607a0c21c3560b88cc090b3080880b2c8ce60ae653d70a7677f509c0e3280919997807c8b9b30715437d06a13685065d5685060f596e060e91e705b76fa405b10e6b0566b4e003f7cba0034afbbb0249a99b0185b851010ab0bf00ad4279
  | 6, 1 => 0x3451707d33dd474d33a95ef3330f147832d484fe3241f77230f2019a30e1709b30b3c7d030a9d7c93078e78b2f653d432f5ca5572e2327552df741622df23de92d9165262d0132102cbb9f1f2c42325c2c2026e82be5a9712bcd35552bc612742baefdce2bada1a72b27b74c2b25f1c52af8e8dd2ad9fd9b2a93c93429ce843e29af2b64292c96522912a7492842fbd3282426c927c009a426d4db0c25e030e4242f629b23e658262383a1de23679dba2325c90b22c735132288025422758e69223c385a223380ee21997fae219634db213bddeb20e401dc20d5617920b8602f205f9e87203d498a20257d1e1f59336e1d75a3ee1d1168bd1cc926421c96ea49
  | 6, 2 => 0x542758495372c4795257aedf51f6a40d5139dea750288f954ebf453b4e8c86004d84259f4d43334a4d2abf2e4c51dc5f4beb8c424bb67d884b2e44754b11aa524abd1d0b4aabf4e84a932f4e4a67671149780ea8494572b94929b01e491b32f748d58fd647acc7154717bb2b46f1b31146881d5845a7f59844ab1cba4449f5954408d56743c469ce42fbf37742e940124270b5be4144ac47412c1b38408a3dc7406a83da3fcf86193f7898033ed249333e0fc03d3dbc5b023d8a3cae3d2c7c353cc696da3c96bad83c21f90f3c0ce04f3b43ce223b1bb4d23b0a44b33a4fc206390dd70d38abbdef376cce2b3661a5cb364ef29f36093879359e209534a771a7
  | 6, 3 => 0x6d79ee906d1c77766d0dc9146cf954796bbbe0b36ad62f646a95be0b6a1a8bbe6a19a43b6a08bb0569db04a5693b519b689f85b8689359986786b847677d8db966e193ff66d1c7a9653b202b64dbd5c4643609f563939f33637bd113629689a2627050f9626898c061b8723760fe5bb260df819b60a7ce44607e393a5ffaba205fa001255f878d095f57a7bd5ef6b1695e84dccf5c97debb5c1f443a5bec1ae15b98587d5b28b7355ac7832c5a9c6dcb5a8a6f275a383b9c59f502be593cbb0a592ae156592546695838ecf2582291a2582078d657a48719578012d05770ff1d5713d785567c7f5156488c3a56427f925618ad1554d9fe7754a96c09546fd00b
  | 6, 4 => 0x86981ab685d3ced98544e646850f970a847e77b184064fcd83f7115a83d093ae83c702f183c0be098362117782cfc52182b8d63d82647cae8220babb81b726b3817cef80812f07f480d851b5809939598034d29c8018916b80087aa87fc09d597f78c21c7f1e33537ea020fc7e7a0a4c7c2f60d67c16ecba7b83ced07af39e807a7688337a399f0c7a0a9b1779c0734278dd6d3877e0dac777abf41376c379d5769b1dfd76670e747613d46a75b270237597c941751532dd74cf39e474a44fa474789e64738c0a8473627f61730cc97a7301de5f7236e265710cff0270fe4ee070ad30ae706400707037bb13700aec186e2e056d6df7e42c6def4db26d9d833c
  | 6, 5 => 0xa4d69db9a476e968a466259aa43fb431a434b4b6a3105a4fa2649992a1d4bf62a15ebe12a0772712a046c73f9f69f2ff9f5eff5f9f307a4a9ec0d7899e93ebe99e5fc6b79e454f609db654639da91d819d459b779be41d5a9bca9a899aca79e39a3dde069a0d45959927cdcc982e64fb97f60d33974b40d796a2e0f996964552965db26495c7f38495b93d769551aacc951cbb3294d417ce94b791e6947fb432945f301892d5a09492ce8e82904161388f818ca58f15bfe78eb04c618e3f8c778dc4f0798da35b008d869bbd8d5bce128cc6a3578cab2e268c51c7138bb8582e8aa44b2d8aa3b04f8a9e78b189e7ef1088e0387f87ba84e88756c63886ade397
  | 6, 6 => 0xc104a00bc0d8bcdac05eefcebffc6d2cbfe17047bf8c3f1dbf662c09bf5d435bbe4769d9be20deedbd9159b9bd7b6565bd6d67c4bc9691cebc545819bab9a1bdba45dd7fb9e390b6b8a185a6b7dce78eb7784d34b764087ab72f93ffb70ac2a9b64676f4b5b55af9b57d39c5b4b954c9b3e7728fb3216c62b2ce525eb285abbdb22053d7b2118fd6b08325ddafd23c0caf7112d2af647c31af616e2baec1fd5fae1b1d36ade4afffac06f897abd5fcedab5c0932aaf7ef58aa2ce68ba9c667e4a99c2534a95258eea94c64a9a900f5c2a8cca005a8249059a7e206d2a7853e24a764468aa748d152a71f7ceda651932aa625ea14a61bfe94a5268c5fa508355e
  | 6, 7 => 0xd9de4eddd9ad9916d9840b17d97fc822d91ff9ced8960f8bd88d7dfad872797ad85d0165d834e651d7fc44e2d7f9e631d79dcf25d7896e3ad740303ad6d35949d6a5bda7d5554a27d4adc04ad49b357ad445852fd3b6fe4ed26d319fd2370a95d2299bdcd215039fd1ffa714d1f83001d029b4cecf1993fdcea577afce5b02e5ce597d4ccd0facd0cccaebe6cb5a385fcad25745caa6b7f9ca14a60bc9997d21c984c951c934d057c91c5dc6c91a9764c910e3d5c8a7981ec822d2dec82107d4c80d6cb3c73369bbc66d7f59c63e6ab8c5c29045c562a862c50c7b54c4f7a12bc4d20e6dc311d738c267cbdec2442d3fc20f81e7c1a1144bc13d7091c111313e
  | 6, 8 => 0xee5bfb02edb21186edae8b10ec06ff87ec0419a9ebefca4bebda4c2debd9c278eb2b9f5deb121e74eb0eb4bdeaa64cb1ea99b7d8ea326695ea15700fe9e8d9b8e9e0e609e9a1d114e9472e07e9375f3ce91cdba7e905686be8a543c6e88e9a99e8027d18e7b11765e6f5ef60e6d9419ae648521fe56c6f69e56ae1b2e55dcfb7e4b5bc3ce3ef42d0e35df4cfe2f6af66e2a76435e28f5f02e26cad09e247b55ee230c8c7e175a2ade171d949e0932adadfbd15aadf7909f5df64decadecd4938dec9dac1de2c8b95ddf2abbadde63f57ddc7aa45dc8a5345dc2c6374dbe127c4dbc7af05db4f33a9db43194adb411a8fda650bedda329af0da26d716da1cea69
  | 6, 9 => 0xfff7afa9ffc6e326ff98826cff939cefff1c032afefc3625fed1b51bfe73e1fffe2c0696fd8987c4fd75c11dfce29772fc6afe7dfc4a1fedfc43d33dfb6cc623fa3689a5f9fb7eeaf6281cb5f5e5463cf570441cf460b034f31deba9f2b97b7df250bba1f1d8e4a8f1a59475f153019ff0bdaa08f0b082cdf0771dd6f049f146f014970eefafc882ef885172ef37b654ef26ef96ee8f06c5ee71eebc
  | 7, 0 => 0x26beaf6f265363bb261c309d2509c4b82429651523e92d1223afce9223a7fde6233e51982310763b22c735132219ec0a21f6124620df43cc2081cc6120292edb1fb72b911eb3facb1e3d0e221d81c57f1d094b741c1ffead1bde45011a433cbc1a4058c3196672e1181aa94116e8db1816d8a81c16b50ee916a611991606144c153eaa18141a4f1c14121a0c12baa67712b8884a124e2635123247971198114411761aa80f8b2a5f0f8898390e7e15130e7dd0190e783ebe0d61f2fb0d52c9a60d4d98860cea20e10cabde0a0c22507d0c167f1009ee1b6f0754ea1506ecbabd06291d8305869eb103e36454033a727c02e9d44b023f103c0086a50c00273479
  | 7, 1 => 0x516924ff514aca6d51099cc65038abd6500139404fb2394c4f717d1d4f0fba7a4ec05ebd4e2ce2974e1db72a4e0e9fc94c4c79c44bff26be4bc969994b0c2c394a6707154a3f78dc49e125c6499cfa0a49226c8f43b4257143a9f8484309ffd84214fad141d9fb7841a839064079af633f69e5183c3d49423c21f90f3a8b9b213a67daad3a305add387c221637f1b8763732d33a36e4026d359f67e7359aee6d358e7c133518dab134064f6c33d93c6b330961a632ba82ac317141fd3129ad3f302ca7772fc976f62f7655c82f1362052e9e70832de85b922d90db782d6df75a2cb7e2692b81626d2a6bdfc029e942c428a4a83e2774c4602705880d26d2458e
  | 7, 2 => 0x77d135d075400898752d3810745a681c73b2320a7260e48f721cd83371be65bd70cdf0747094669270675391705b5d9f6f6c29a26f69601f6ebe77696db8095f6d9b14bb6bed6d236be1bd3a6bcb63fb6b6909ce6b46b4d16b1be3666a7ff6686a0139de69b07ce367f1c0d3679d352a651506a464ffcc4e64cf00c5645092fc6449b75d6401590263353df46292bf2261ca400861aa3368602f2d625fff77045f5d13a95f492eb65d3a46645d1e66bc5c0095e65b2acd595af03eb05abc6cf25aa8a6b9596bf20658905d13584e132a581fb8f657a1024a56240dff54ed1c7554c1de1053346db9531915d1530ec13f52943af552942b72523dc21151bf3f2b
  | 7, 3 => 0x968ac1e9956125c6950fbbe3944ede0094355c1494331b6593f42b8d93cd8fe09351acbb934043b8929a9c84927d83849272b1cc925c0be491b98d129117715e8f9d1d5f8f6e24048e4941358e35cdb08df2ab598d5eaaf98d3d413a8d1e3ac28ce77a638bc68b508bbc73f08a81f0ca88f300e1877c8a9f86e6840f8651842c85f48e9f85520fcd8492c7cd83f048fb8380407182d3eb998276397282739f2081bd8a2f7fe35f827f5f0e0b7f1797dc7ecd8d627e8559377e1a8a567dfd47397db173387d356db97cd372a07bf841387bf0d3337b4614867b2b17a17ab597257ab2c90879e15a2879a4d76c798a90b278bca81278925775785a178978493a7f
  | 7, 4 => 0xbba736d9baa8a17cba45dd7fba1f06b4ba0d3369b8689f9eb59a84ddb559ed2fb52557b8b511b645b4e46fecb37ef559b253eee6b1b17014b0f51e5bb0e1dcffb080f6ebb031ca64b01ae1b0afebec7dae8d3699ada32de2ace974c5abbe6e52aba1ac24ab94b348ab681b8eaab1140caa87c3f1aa2867c5a98e4816a909e4c1a8e78fc4a8d9852aa68098aea494c22fa4711fa3a3f2435da35f8a0fa309310ca1c6431fa1807b919e58572e9db654639d61744b9d3508f49d2d50bb9c97dd089c7605899c48de239b1dd7b09ab0be7a9a36658d99ed5e879985b80798d8396998553ede98411d8197ec88bb97a5128c974a939b97251c989710a45896e3fc35
  | 7, 5 => 0xe48a3599e46b0a58e3d420a8e2e94854e21fca1de1ccafbce1b94d76e0f3695fe0d9cf49e088d44de07b344edf91a28ddf7fbf91df6d0221dec9aaa0de7f8515ddd7f9c9ddd589c4dd547ea2da8fa153da26b2c9d9b9b7a8d958a3e4d8f62b1fd8653959d58853add3fa20bfd3ca8022d1efb8f3d17f337bd1786b89d0dd3a20cfe713d2cf9551ebcf446c2dcea2794cce37cadccdae7ca3cd5fbf4fcbfcbae9cb46a5f8c9f2a206c9a019fdc8e779a6c689fa79c5d3e588c576ef75c5690328c37f968dc33e8ebcc2d0e2fcc21dcfbbc1a069d3c1043454bf8705ebbf4172fabf355634bf01fb40be4be64fbe3418b4bd199d0fbc545819bc18011abbb69bf5
  | 7, 6 => 0xffcceadcff939cefff3992a2fe091979fb7259a6fb192d73fac274d4fa58df1bf9323ec7f80fe67ff6657479f6655c2cf5a8ee32f498545ef17a65ebf15afe71f109fd47f1027f58efdef6d4eef3064deec76f65eeab662cee1e2c58ed5ae6a4ec164c1eebc28ee5eb94b67beabec0cdeaa64cb1ea643d52e812cbdfe73f702ce6a7c695e606f433e575a6ea
  | 8, 0 => 0xf33b5fd0f2854adfd1efb8f3c3d681efb47be621b031a5c8a6563cc3a1f16def876dd2497f4590c97e1a8a567cea112d76f0de33764e5f61705b5d9f61ca40085fbac6fd5e22a7545cde0cce51bb2a0f5059633d4aee737942b779a33e277fff34064f6c2efbd9641b78d4bc1606144c0e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x11001100110011000f000f000f000f000500050005000500030003000300030000ffff0000ffff00000f0f00000f0f00000000ffffffff000000000f0f0f0f
  | 0, 1 => 0xfc00fc00fc00fc00fa00fa00fa00fa00ee00ee00ee00ee00cc00cc00cc00cc00aa00aa00aa00aa007700770077007700550055005500550033003300330033
  | 0, 2 => 0xff00ff00ff00ff00ff00ff00ff000000ff00ff00f000f000ff00ff00cc00cc00ff00ff00aa00aa00ff00f000ff00f000ff00cc00ff00cc00ff00aa00ff00aa
  | 0, 3 => 0x707070707070707050f050f050f050f0505050505050505030f030f030f030f0303030303030303010101010101010100ff0fff00ff0fff00ff00ff0fff0fff
  | 0, 4 => 0x33223322332233223300330033003300323232323232323222222222222222221155115511551155113311331133113311111111111111110f0f0f0f0f0f0f0f
  | 0, 5 => 0x33333333333300003333333333003300333333333030303033333333222222223333330033333300333330303333303033332222333322223330333033303330
  | 0, 6 => 0x55555050555550505555444455554444555055505550555055445544554455445500550055005500545454545454545444444444444444443333333333333333
  | 0, 7 => 0x99999999999999998888888888888888555555555555555555555555555500005555555555005500555555555050505055555555444444445555550055555500
  | 0, 8 => 0xaaaaaaa0aaaaaaa0aaaaa0a0aaaaa0a0aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa55aa55aa55aa55aa00aa00aa00aa00a8a8a8a8a8a8a8a8a8a0a8a0a8a0a8a0
  | 0, 9 => 0xababababababababaaffaaffaaffaaffaaffaaffa0f0a0f0aaffa0f0aaffa0f0aabbaabbaabbaabbaaafaaafaaafaaafaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0
  | 0, 10 => 0xccccccc0ccccccc0ccccc0c0ccccc0c0ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc33cc33cc33cc33cc00cc00cc00cc00c8c8c8c8c8c8c8c8bbaabbaabbaabbaa
  | 0, 11 => 0xcdcdcdcdcdcdcdcdccffccffccffccffcceecceecceecceeccddccddccddccddcccfcccfcccfcccfccccccccccccccccccccccccccc0ccc0ccccccccc0c0c0c0
  | 0, 12 => 0xeeeaeeeaeeeaeeeaeee0eee0eee0eee0eecceecceecceecceecceecce0c0e0c0eecceecc00000000eeaaeeaaeeaaeeaaee00ee00ee00ee00ddccddccddccddcc
  | 0, 13 => 0xeeeeee00eeeeee00eeeeececeeeeececeeeeece0eeeeece0eeeeeaeaeeeeeaeaeeeee0e0eeeee0e0eeeecc00eeeecc00eeee0000eeee0000eeee0000eaea0000
  | 0, 14 => 0xeeeeeeeeee00ee00eeeeeeeeececececeeeeeeeeece0ece0eeeeeeeeeaeaeaeaeeeeeeeee0e0e0e0eeeeeeeecc00cc00eeeeeeee88888888eeeeeeee00000000
  | 0, 15 => 0xf0fff0fff0fff0fff0f5f0f5f0f5f0f5f0f3f0f3f0f3f0f3f0f1f0f1f0f1f0f1f0f0f0f0f0f0f0f0f0e0f0e0f0e0f0e0eeeeeeeeeeeeeeeeeeeeeeeeeeee0000
  | 1, 0 => 0xfafac8c8fafac8c8faf0faf0faf0faf0fac8fac8fac8fac8fa00fa00fa00fa00f8f8f8f8f8f8f8f8f5f0f5f0f5f0f5f0f3f0f3f0f3f0f3f0f1f1f1f1f1f1f1f1
  | 1, 1 => 0xfca8fca8fca8fca8fc00fc00fc00fc00fafafafafafafafafafafafafafa0000fafafafafa00fa00fafafafac8c8c8c8fafafa00fafafa00fafaf0f0fafaf0f0
  | 1, 2 => 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000fcfcfcfcfc00fc00fcfcfcfca8a8a8a8fcfcfc00fcfcfc00fcfca8a8fcfca8a8fcf0fcf0fcf0fcf0fcc0fcc0fcc0fcc0
  | 1, 3 => 0xfefe0000fefe0000fefcfefcfefcfefcfefafefafefafefafef0fef0fef0fef0feeafeeafeeafeeafeccfeccfeccfeccfeaafeaafeaafeaafe00fe00fe00fe00
  | 1, 4 => 0xff00cc00ff00cc00ff00aa00ff00aa00fefefefefefefefefefefefef8f8f8f8fefefefef0f0f0f0fefefefe00000000fefef0f0fefef0f0fefef0f0fafaf0f0
  | 1, 5 => 0xff01ff01ff01ff01ff00ff00ff00ff00ff00ff00ff000000ff00ff00fc00fc00ff00ff00f000f000ff00ff00cc00cc00ff00ff00aa00aa00ff00f000ff00f000
  | 1, 6 => 0xffaafaaaffaafaaaffaaf0a0ffaaf0a0ffaaeeaaffaaeeaaffaacc88ffaacc88ff88ff88ff88ff88ff11ff11ff11ff11ff05ff05ff05ff05ff03ff03ff03ff03
  | 1, 7 => 0xffaaffaaffaaaaaaffaaffaaffaa0000ffaaffaaffa0ffa0ffaaffaafaaafaaaffaaffaaf0a0f0a0ffaaffaaeeaaeeaaffaaffaacc88cc88ffaaffa0ffaaffa0
  | 1, 8 => 0xffccffccaa88aa88ffccffcc00000000ffccffc0ffccffc0ffccfcccffccfcccffccf0c0ffccf0c0ffcceeccffcceeccffccaa88ffccaa88ffaaffaaffaaffaa
  | 1, 9 => 0xffccffccffccffccffccffccffccccccffccffccffcc0000ffccffccffc0ffc0ffccffccfcccfcccffccffccfcc0fcc0ffccffccf0c0f0c0ffccffcceecceecc
  | 1, 10 => 0xfff0faf0fff0faf0fff0ccc0fff0ccc0fff0aaa0fff0aaa0ffeeffeeffeeffeeffeeffeef0e0f0e0ffeeffee00000000ffeef0e0ffeef0e0ffee0000ffee0000
  | 1, 11 => 0xfff0fff0fff0fff0fff0fff0fff0f0f0fff0fff0fff00000fff0fff0fcf0fcf0fff0fff0faf0faf0fff0fff0ccc0ccc0fff0fff0aaa0aaa0fff0fcf0fff0fcf0
  | 1, 12 => 0xffff0000ffff0000fffefffefffefffefffcfffcfffcfffcfffcfffcfcf0fcf0fffcfffcf0f0f0f0fffcfffc00000000fffafffafffafffafff8fff8fff8fff8
  | 1, 13 => 0xffffaaaaff00aa00ffffaaaaf0f0a0a0ffffaaaacccc8888ffffaaaacc008800ffffa8a0ffffa8a0ffff5500ffff5500ffff1111ffff1111ffff00ffffff00ff
  | 1, 14 => 0xffffccccffffccccffffccccff00cc00ffffccccf0f0c0c0ffffccccaaaa8888ffffccc0ffffccc0ffffcc00ffffcc00ffffcc00aaaa8800ffffaaaaffffaaaa
  | 1, 15 => 0xfffffc00fffffc00fffffafafffffafafffff0f0fffff0f0fffff0f0ff00f000fffff0f0ccccc0c0fffff0f0aaaaa0a0ffffeeeeffffeeeeffffeeaaffffeeaa
  | 2, 0 => 0xffffff00fffff000ffffff00f0f0f000ffffff00cccccc00ffffff00aaaaaa00ffffff0088888800fffffcfcfffffcfcfffffcf0fffffcf0fffffcc0fffffcc0
  | 2, 1 => 0xffffffff00ff00ffffffffff00aa00aaffffffff00330033ffffffff00000000fffffff0fffffff0ffffffccffffffccffffffaaffffffaaffffff00ffffff00
  | 2, 2 => 0xffffffffc8c8c8c8ffffffffaaaaaaaaffffffffaaaaa0a0ffffffffa8a8a8a8ffffffffa8a0a8a0ffffffff88888888ffffffff55005500ffffffff11111111
  | 2, 3 => 0xfffffffff8f8f8f8fffffffff0f0f0f0ffffffffeeeeeeeeffffffffeeaaeeaaffffffffccccccccffffffffccc0ccc0ffffffffcc88cc88ffffffffcc00cc00
  | 2, 4 => 0xffffffffff00ff00ffffffffff00f000fffffffffcfcfcfcfffffffffcf0fcf0fffffffffcc0fcc0fffffffffc00fc00fffffffffafafafafffffffffafaf0f0
  | 2, 5 => 0xffffffffffff0000fffffffffff0fff0ffffffffffccffccffffffffffaaffaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x4058c9b3
  | 3, 0, 0 => 0x57280e65a4864059e9b473b91204947eb292249480b292249473b193691480b25224947eab94879480b1920494862b93a6d473b2922494
  | 4, 0, 0 => 0x8639dbe8f3cab9d96ae3d9d155ca33596892b1e57280e85a58939d307b3cac31a2ae46969648e765a4492ae757244ea49557284e65a24ac31e2ae3d9e563cae509e47cb187eab91a795892b8f67935aab91a70359695ceca489ec92b0c75b3d22495
  | 4, 0, 1 => 0x73b19229024ac315ca1419e561ae767a4492b0167b192249581b9d5c7b3cabf55c833c9c16190157274f2ae76a3192249583b30f65a24ac49d2ae3d9e5618ae489b492b0c73b3d3a4057eab946791f2801ceca48925218ae469b8d6a0073b2522494
  | 4, 0, 2 => 0x8639d8097332c315c8d37159618ae469aca4b1373b3d2249573b295c9124abf59ec648925624e76a1ecc2b0c57244d64958639d949124ac1d5c7b3a1695cecf6524492ae757244e649573b255c9124ac31ced448911618e764a4492ae767b2522495
  | 4, 0, 3 => 0x923f59e9124ac3200cf489256190167a7492ae757290f6795892b9427b3cac9202cf48925646e767a4492b1e73b01385a58639d9e9b48ac5dfaae469e563ce764a4492aae3d9e4e2695864059e9024ac315c833c9ad5cee467a4492b1e80b3d22495
  | 4, 0, 4 => 0x479cecb489255faae3d9e4e2ae771b3d224955728d425a24ac7dfaae419e5618fd60270b4b2473b2922495
  | 5, 0, 0 => 0x863a55c7b3c8f99ceae559ece85a68639da87b2a109a48e756244b44968bb9d5c8d3d9e58010c73b3c921c500449faae3d9e55cea24c1ecb44968b431e4ae3d9e5a20e7571ecf23e600431fab846969618ae50a34f25a68939d5ca53d9e5a18e75723cf6796893f5ceae3d9e5a18e757274b4406
  | 5, 0, 1 => 0x8b431cecf48925a0eae3d968b0496864059e913d925a18e760224f65a68627d307b2d125a20ae3d9a4b44968639d8097431699ceae3d9e4e449673b00f67030969a24e7571ecf22168639d6cae46969a18fa571ecf25a68cb9d807b2d109a24e76a2b8f67968fbf55c832d125a4f0c73b3d22496
  | 5, 0, 2 => 0x8639dbe994b969a18e757250f67968cb9d80ae3d9e580112739ecf21758c2b8f67934925a190873a64f65a657284f6702d125a18fd57214b4496862b9067b3c9a58011273ab8f62157eab946792d1258011e73b010c5a5792b8f67938125a18f2602b8f67968f39d927b29125800e767b1922495
  | 5, 0, 3 => 0x8639d807b37969a18fd4c234b44968639d809c3d969a18fd5bab91a5a6571ecf270348f9a18ae3d96898496862b9227934925a18f1571ecb44968639d5c9733125a48e767a44f64968639d9ec0489258010c739eca64958c3f55c8d2d1258010c67a449203595c31cecf48925a18e75a2b8f6796
  | 5, 0, 4 => 0x431fac0431694010c7eab91a6e58639d9e91248f5a18e76fb3d224968939d5c7b3c985a18e767a44924068639da87b308f99ceae3d9d0b44868639d5c8d359699ceae3d9d8b0496893e5ceae3d9e5a26e757244b449673ab8f65a26925a18fd73b010c5a6862b91a7935969a3ee75720cf6796
  | 5, 0, 5 => 0x8639d5e7b2d125a18ae3d9b0b44668f39d5c9c2d125a3ce757244f24968639d5c9d489e5a530c73b3d22496004315c8d35969618e7571ecf23f673b7d9ec64b925a18fd70a10b44968f2b8f674341699ceae3d9d8e649689421ceae3d9e5a18fd5c2b91a5a68639d9e9124871a18ae3d9e4d4496
  | 5, 0, 6 => 0x8639d5c91469e5a3ce7602b90c5a6571ece06b2d1258010c80b3d2249573b3d8cae48925a3ce7659eca44968f431cec0431698010c73ab8f63f5864055c913c9259cee3679eca44968c39d5c8d3d9e5a3d0157244b44968639dbe8f2d1258011e73b3d2249586405cecf48925a40fd57234b4496
  | 5, 0, 7 => 0x863455c7b2d1258012473b3d2249573a60f6702d125a18fd73b3d224968639dbeae419e5a18fd57274c45a69239d5c913c925a18f073b3d224968639d5c7c2d125a18e757228f6796863415c7a2d125a30fd571ecf24968939d5c7b3c85da18e7679eca6496933f55c8d2d125a18fd57234f2516
  | 5, 0, 8 => 0x863f55c8d31169a18ae46968ac46686300f66930969a18ae509ecf23e673b3d8c8e3d925a18fd57294a24968a39d5c973d9e5a190157274b4496863f55c8d3c949a18fd5b2b91a5a600431facf48925618e76fb512e4967eab8f679380f9a490157244b4496863f55c9c2d125a18fd57244f2496
  | 5, 0, 9 => 0x863f55c9d2d125800e7649eca44958f39d9eae48925a48fd57244b449673ab8f67439969a3d0c73b3d22496863e95c8d2d125a18e76a2b92249673ab9467b3c8f9a18e75cab8f6796863f5808d42169a2afd571ecf25a6863f580ae43169a18e76a33d2249681b9d5c7b2d125800e7571ecf2715
  | 5, 0, 10 => 0x8639dbe8e3c925a2d0c73ab92279673ab8f6642d1259d2ae3d9c0b44968f3c95c7b3c925a18f473ab8f679600431ce9124821618fd73ab9067968639d9e9148125a190167ab922496862b8f66e35925a20e9571ecb44968dc31faae469e5a18e767a44924465728cf6692d125a3ce7601ecc25a6
  | 5, 0, 11 => 0x9239d9eae489259ced4631eca44968639d80aa3d9e59ceae3d9e4e63e6004495c7b3c80d630e7602b8f679692431cecf48925a18ae469acb449600449ceae3c881618eb57244b449673ab9067b3c9c1a18e772b3d22496863f55c8d35969a18e76fb012e79673b495c7a2d1258010c7eab906795
  | 5, 0, 12 => 0x863f55c7d2d12595c7b399a4b449673b2d5c7b2c125a18e75721cf6796863f5a8ae46969a3cae3d9e4d23e6863f59eae489259ceae489e4e04968639d80ae489e5a190873b3d22496004495c7b3c9a5618ae3d9e4d63e60039d9e9124805618f257234f67968639d9e9d489259a4d0571ecb4496
  | 5, 0, 13 => 0x431cecf488f5618fd57234d85a68639da87b2911195ca24f9ecb44968639d307b3c8f9a18e7649eca449673b3d927b29125a3ce755a44b4496602b8f67034969a18e767a451a49673b3d8c913d925a1ae7679eca44968939dbeae3d9e58010c739ecb44358639d807b33169a18fd601ecc25a6
  | 5, 0, 14 => 0x863f55c8d37169a18fd67a34a449686429cecf489259facf631eca44968639dbeae4b99da18fd5c1ecf25a6862b8f66b29125a3cae509e4b44968639d807b2d10da18983d9a4b449673b4d5c7b2d125a18e767a449208673ab8f673291259cec9571eca44968bbf55c8d2d1259cecc559ecb4496
  | 5, 0, 15 => 0x862b8f66e2b1259d8e7571ecb44967eab91a7938169a4901571ecb4496
  | 6, 0, 0 => 0x430b4491005c06c008abf55c7b2d125a18e7601ecb44204bc31cec0571ecca5a78639d7cae3d96892f0c73ab8f679308f9e18ed73ab8f65a24bc31ceae3d974921778639d78ae3d96892f1b863f55c7b3c925e3ce767ab8f65224b80230e7571ecf24968639d5c7b2d1240ef0c73a612e7b2d125e3ce7571ecb44910bc31cee1571ecf25a7
  | 6, 0, 1 => 0x431ceae489e492d0c73b795c7b2d125c010c739eca449043431ceae3d968922e700479ceae4896892d0c8239d5c7b2d125e190173ab9225a24bc79ceae3d9689c4978f3b9ceae3d96892e008f41d5c7b2d125a18e7679eca44922380218fd3d9687a17686421ceae3d9e47cf0c73ab8f65a248d1c00e7571ecf23e00b431cedf3d96892337
  | 6, 0, 2 => 0x8639daaae3d96892e0000431cecf4892562d0c73ab8f679293c31ced457234f65a7571ecf2703496892f0c602b8f67934969e3d0873b00f65a24bc31cecf57244f64978639d5c7b2d12410f0c7eab8f66b2d125e18e75d2b8f65a24bc31ceb2571ecb44970039d5c7b3c9c07cd0c73ab9347b2d125e4f0c73ab8f6622d3c31ceae3d968920f7
  | 6, 0, 3 => 0x863e1ceae3d988b4f187839d5c7b2d125e3d07572acf65a24b80218e760210f65a673b195c7b2d12410f0c73ab9247b2d125e18e772ab8f65524bb9da8d2571ecb449700431ce49180802ed0c73b959e7b29125dcecf632b92e7b24bc31ceae3e9ecb44978639dbeae3d99cb4f0c7eb0d5c7b2d125c010c80ab9225a24b4315c7b34984b4497
  | 6, 0, 4 => 0x4315c7b248c004d0c7eab8f65a248dde18e757258f65a24bc31ced43d984b449786425cec03d96884f0c7eab91a5a24875e18e7571ecbe5a24bc61fae7571ecb4497863f55c8d4216892f0c7eab94a8d2d125e18e765ab8f65a24bc9e18f2571ecb44978b431ceae3d988b4f0c7eab8f6792d119c010e739ecb4490bb002187b248c02e036
  | 6, 0, 5 => 0x2b8b4491000c02d0c7839d5c912d125e18e7571ecb449023c320ce7571ecb449786421cec0469ecb4f0c7eb515c7b2d125e14e7632b8f65a24bc31ceae4c9ecb44978f39d5c7b3996892f0c73ab91e7b2d125e3ce764ab8f65a24b801ceae3d9687a006893f5ceae3d96892f0c73ab8f65a24825c00ae3d9c0d25a24b49e18e7601ecb4427
  | 6, 0, 6 => 0x863f5ceae4896892e00893f55c7b2d125a18fd67ab8f65224bc31ceae3d968923578b431e4ae3d96892ee7571ecf27029125e18e7602b8f679293801faae3d9687a01686421cecf3d94892f0c73add5c7b2d125e18e752a60f65a24bc31cecf471ecb44970039d9e7b2912402d0c73ab8f65a27925c01187eab8f65a24b431faae3d96892217
  | 6, 0, 7 => 0x8639d80ae3d988b4f0c73b7d5c972a925c011e3d968921701b0023ce7571ecec4968f39d5c7b3096892e00862b8f6622d00da18e75fab8f65a24bc31ceae3d9689215700491ceae4896892d2b8639d5c7b31169e3ce7571ecb44913380218e757188b42068f39d80ae3d9e4b4f2273ab92e7b2d125e18e7571ecf23e0bbc5dceae469ecb4497
  | 6, 0, 8 => 0x8639d5c7b2d1245af0c73ab94e7b3c925c010c73ab8f63d183431ceae3d968922c78639d5c7b2e16892f1e73ab94e7b2d125e18e75dab8f65a24b801ceae248c040016863f5ceae469e4b4f0c73ab8f65a24849c010c7eab9225a24b431faae3d9689c4978b431eee7571ecf2f1b8639d807b2d109c010c7eab91a5a233431eee7601ecb4427
  | 6, 0, 9 => 0x431807b2d10806d0c73ac55c7b2d125e18f2602b8f65a24b80218fd57234f25a695c31cec03d96884f16863f55c7b3c969c010c73b00b442103431cedf5725cf24978639d5c7b2d12454f1e73acd5c7b2d125e3ce7559ecb45224bc31faae3d9b0b449700431e4ae2d12440d0c73b7d5c7b2c925e18e767a34f65224b8015c7b248c006016
  | 6, 0, 10 => 0x8639d5c7b2d12444f0c73ab9267b2d125e18e76a2b8f65424bc79cebc571ecb44978639d5c7b311687ae00863f51a5a2485da430c7eab91a5a24bc31ceae551ecf24978639dbeae3d988b4f0c7ebed5c7b2d125e4cfd572a0f65a24b80218e7679eca43d600431cedf67a5c92c00862b8b43d1000d9ceae469ecf2702d38023ce73d92460176
  | 6, 0, 11 => 0x863f58aae3d96892f0c73ad15c7b2d125e18e757250f65a24bc31cec03d9e4c25a78639d5c7b2d1244af1973b015c7b2d125c0112739ecb4490bb46e18e7602b8f67970039cf65a1e85c02cf773ab8f67938125e18f773b015c7b3cb80230e73d968921768639d5c7b2d1241af0c73b515c973d925e18e7679eca449043c7a18e757244b4497
  | 6, 0, 12 => 0x431ce912d1242ec00862b8f63d1800d9faae3d9e4e05a24bc31e4ae3d968923d7863f580ae3d9e4b4f0c73ab8f6772d125e18f26fab8f65a24bc79ceae3d9689208786421cec03d9e4b4f0c8539d9e7b29125c010c73ab87a30103431cec0531ecb449793c31ceae3d9e47cf0c73ab92a7b2d125c010c73b00f642183431faae3d9b8b4497
  | 6, 0, 13 => 0x73ab94a7b3816892f0c73b015ca53d969e3ee75720cf65a24bc79ceae3d9689233700431faae2d1243ad0c73ab8f6662d125e18e770b00f65a213c31fafc571ecb4497863f55c7b3096892f0c7eb115c7b2d125e390c73ab8f6622d3c31cedf601ecb44278639d58973d96892e008639d9eae489258011e73ab8f6622d3431faae3d96892267
  | 6, 0, 14 => 0x431fab83d96892d0c7eb9d80ae46969e2d0c73ab92e7b3cbc79cecb571ecb44978639d5c7b2d12456f0c73b012e7b2d109c01267eab8f65a24b4315ca13d9e4b44978639d807b2d15084f0c73b3d807b2d109e18e7571ecb44b24bc31cec7571ecb44978739d5c7b2d1242ee008639d807b309699cee367ab8f65a24bc31cece571ecb4497
  | 6, 0, 15 => 0x8639d80a93d96892f248639d5c912d125c010c7e9ec92300bb47a0ce7571ecb449700479cec03d96884c008639dbe8e2d125a20e7571ecb44910b80218f2571ecf2496863f55c7b2d12432f0c73ab94a7b2d105c00fd57234b44900b435ceae3d9689208700479e4ae3d96892d0c7eacd5c7b2d125e190873accf65a24bc79ceae3d96892097
  | 6, 1, 0 => 0x863c1ceae3d988b4f0c7eab91a5a2b125e18e7571ecb4491b3b9d5c7b38168922178639d5c853d96892f0c74ab8f65a24885c010c73ab8f65a11b39da8ae3d9c0b449700431fac057234b4d0c7eab9547b2d125c011e571ecb43d01b44a10e7571ecb449773ab9467b3c96892f0c73ab8f65a24829e18e7571ecb4491dbc6210e7571ecb4497
  | 6, 1, 1 => 0x86421ceae4896892f0c73b755c7b2d125e18e757238f67924b801ceae4896892016863f5ceae3d988b4f0c73ab8f65a24871c010c571ecf23e01b431ceae4ea44b449793c31cecf3d94892ee76fb3d8c7b2d125e570c73ab8f6791f3c31faae46a20b44978f39d5c7b2d1242af0c73ad95c7b2d125c010c73ab8f23e1030015c7b2d12406006
  | 6, 1, 2 => 0x8f39d5c7b2d1245ae008f39d5c7b3a1698011e73ab8f63d183431ceae3d9e4bc497863f55c7b2d12410f0c73ad55c7b2d125c010c73b3d1c7b24b479cebb571ecb44978c39d5c8d3d96892f1e73ab8f65e2d125e18e76fb00f65a22bc31ceae3d9e0b449773ab92e7b3c9c092f0c73b015c973d9e5e18e76fab8f65724bc31cec0571ecf2547
  | 6, 1, 3 => 0x8639d5c973d9e482e00863f55c8d2d0f5800e7571ec9230003431cedc571ecb44978639d5c7b2d12474f0c73b01087b2d125c00e767b18f65224b002187b2d1242e0268639d5c7b2d1242ce00862b8f679348f9a2d0c73b3cf65224bc31f4e7571ecb449700431faae3d988b4d0c73b6d5c7b2d125e18e7571ecb44914bc31eae7571ecb4497
  | 6, 1, 4 => 0x8639d5c7b2d1241ce007eab8f64918005a18e772a38f65a24bc31faae46968921778639d5c7b2d1243ce00863e95c7b2d125a18e7572451a5a24b801dce7571ecb4496863f5cec03d96884f1d8639d5c7b3c8f9e18e76fb3d5c9724bc31dee7571ecb449700461ceae3d9687ad0c7eab8f65a248cde18e74c234f65a24bc3210e73d96892337
  | 6, 1, 5 => 0x8f431ceae3d988b4e008639d80863d9698010c73ab9225a1eb00218e767948922068639d5c8a3d96892f0c73b5d5c7b2d125e3ce7571ecca5a24b80218fd601ecb442673ab8f6793996892f1273ab8f65a2485de18fd57234b449183c31faae3d9689209700431d4ae3d9687ad0c73ab9027b2d125e18fd57234b45124bc31cedf571ecf23e7
  | 6, 1, 6 => 0x7cb9d5c7b3816892f0c571ecf26929125c010c739ecb43d0bb431faae54234b44970000224e7571ecf2a007396892200b805a3b0c571ecd25a24bc31cedf5720cb44978639d9ec03d94892f0c73b85087b2d125e18fd5bab8f65a24b80218cf3d948920368f39d98ae3d96892f0c73ab8f65a28125e18f673ab8f65a24bcae18e7679eca4497
  | 6, 1, 7 => 0x73ab8f6703096892e008639cf6622d05d800ae3d968920200b431ceae3d9acb44978639d5c803d96892e0073ab8f6732d125800e764ab8f65a24b4795c7b3c9a4b449773b015c7b3c9c0b4f1e73ab8f65a24861e190873a38f65a24bc315c7b3c9acb449700479ceae3d9e47cc008639cf65a2702d8007b2d1242e0300b431ced4601ecb4427
  | 6, 1, 8 => 0x431faae3d8f460c00863f55c7b37125a18e757224f65a24bb9d5cab3d968b04978a39d5c973d96892f1e8639d807b2d109e18fd571ecbc5a24b80218ae248c0400368639dbe974716892f0c73ab92e862d125e18e76fb3cf65524bc31faae46968a4497863f55c7b2d12424f0c73ab8f65a25125e18e770ab8f65a22bc7a18f2571ecb4497
  | 6, 1, 9 => 0x8639d5c7e3d96892f0c73ab8f65a24815e3ce75eab8f65a24bc79cec0571ecb442700479ceae4316892d0c73b3cf652248f5c00e73d924601700b431cedf679eca4497004315c7b3596892d0c7eab8f65a248a9e18e7571ecc45a11bc31ceae3d980b4497863f55c8d3c96892f0c7eae15c7b2d125e18e761ab8f65a24bc31cedf6a1ecb4497
  | 6, 1, 10 => 0x8639da8ae3d96892f1e73ab8f67929125c011173ab8f65a1eb00218e72d0f4401768639d5c8d3d9e4a2f0c73b055c7b2d125e530c73b3cf65224bc315c8d3d9e4d25a78639d307b3c96892f0c73ae55c7b2d125e4f0c7eab91a5a24bc31ceae3d968923778dc31ceae3d99492e00863c8f65a2485da18e7571ecb65a24bc31eee7571ecca497
  | 6, 1, 11 => 0x8dc315c7b3c9a492f0c73ab94a7b3c8f9c010c571ecb43d013479ceae531ecb449700479cecf3d94892d1a73b7d5c7b2d125e18e76d2b8f65a24b80218e757168921c6863f5ceae3d9e47cf0c73ab8f65a248f1e18e7571ecb4490a3c31faae3d994b449700431ceae4c9ecb4d0c73b3d2e8e3d925e18e7571ecb44910b802187b2d0f42e036
  | 6, 1, 12 => 0x73b3d8cae3d94892f0c73ab8f65a248a1e3cf573ab8f65a24bc31cee6571ecb449786421ceae3d988b4f278639d5c912d125c00e7571ecc45a00b00218e74c1ecb44968639d5c7b2d12420ee76a3195c7b2d125e3ce7571ecc45a24bc5a18fd57234b44978639d5c9d3d988b4e008639cf65d2485da190573ab8f65a24bc31ceae3d96892387
  | 6, 1, 13 => 0x863f5ceae4316892f0c7a39d5c7b2d125e18e766ab8f65a24b80218e73d8f460176863f5ceae4196892f0c73b515c7a2d125e18e7571ecde5a24bc31ced8571ecb44978639d5c823d96892f1e73ab8f65a248e9e18e757270f65a24bc31cec03d984b44978dc31faae4696892f0c73ab9227b3c925c010c7eab8f6791f3431dce7571ecb4497
  | 6, 1, 14 => 0x8639d60ae3d96892f0c73b7d80972d125c010c7eab9065a24b435cecf571ecb44978639d5c7b3c8f842e00792b8f65a24805a18e757294f65124bc31ced4571ecf23e78b431ceae4896892e008f2b8f6491800da18ae529ecd25a24bc31ceae3d96892117864055c913d96892f0c73ab91a7b3c949c010c73b3d227b24b431cec2571ecb4497
  | 6, 1, 15 => 0x8639d80ae431ecb4e008939d5c5a24881a18d4682b8f65a24bc31ceae3d96892237863f580ae4696892f0c7eb015c7b2d109c010c739ecbc49063001ceae2d0f4400168639dc0ae3d96892e00863f55c862d1259cee5712b8f65a24bc31ceae3d968921378639d5c8d3d988b4f0c8439d807b2d109c011873ab8b449103001cec03d96884016
  | 6, 2, 0 => 0x863f5cecf3d94892f1e73ab8f6762d125e18e760235087b2d3c31cec0551ecb449773b3d92ae3d96892e00892b8f65a2480da30e7602b8f65a24bb9d8cae3d968924478f431ceae3d9e47ce00571ecb43d01805a18e76f9ecb449133c79eee7571ecf2497863c1cecf3d94892f0c7db9d5c7b2d125e18e76fb00f6792d380230ae3d96892036
  | 6, 2, 1 => 0x8639d5c8c3d96892f288639d807b2d109e18d4571ecd25a24b80218e7571ec7c216863f55c7b3c94892f0c7ead95c7b2d125c011e739ecb43d0bb441ceae3d9e4b44978639da8ae3d96888f0c73ab8f65a248bde18e75725cf66524bc31ceae3d968923978639d90ae3d96892f0c73ab8f6732d125dceae3d968b049243c31cec9571ecb4497
  | 6, 2, 2 => 0x431ce7b3c8f82ed1e73ab8f6742d125dcee5632b8f65a24bc91ceae489ecb4497863fd5c973d96892f0c73b015c912d125c010c7eb3cf65224b431ced9571ecb449700431ce7b2d10812c00863f55c8d248c18010c57244b44901b001ce7b2d1242e006863c95c8d3d96892f0c571ecd25a24885e18e7679ecc25a24bcae18e757244b4497
  | 6, 2, 3 => 0x73ab94aa23d96892f0c73b3d4e7b2d125e18e7622b8f65a24bc31cedf571ecb44778639d5c873d96892e0073ab8f63d180058010673ab8f65a24b47a18e757218b4497863f55c7b3116892f0c73ab8f65a2487de18f36fab8f65a24bc31cec0571ecf25a78639dbeb33d96892f0c73ab8f65a2489de18ae3d968ac49233c31d2ae3d9e4b4497
  | 6, 2, 4 => 0x8639da8cf3d94892f0c73b595c7b2d125e370c73ab91a7b3cbc31cedf67a5cb44978c39d5c7b2d1247af0c73ab9167b2d125e30e76fab8f65a24bc31eee757234f6797863f5f4ae3d96892ee7571ecca632d125c010c792b8f65a1eb431ceae4e9ecb4497003f4f65a2485c02d0c7eb855c8d2d125e18ae4b9ecf26924bc31f8e7571ecb4497
  | 6, 2, 5 => 0x4315c8d2d12404d0c73ab9225a248f5e18e76fab9225a24b80218e75720cf67968b4315c7b3c9a4b4f0c73ab8f65a24869e3d0c73b3cf65224bc31ceae48968924078639da8ae3d94892f0c73b3d547b2d125e18e7572652e7b2d3c31ceae3d968923278639d5c9e3d96892f0c7eb3d5c8d2d125dfacf632b8f65a24bc49cedf571ecb4497
  | 6, 2, 6 => 0x10c7eab9527b2d125e18e7601ecb442183c31f2e7571ecf23e700431ce7b248c02ed0c73ab9225a24871e3ce76a2b8f65a24bc315ca54f9ecb4497
  | 7, 0, 0 => 0x8b431ceae469ecb44980043e18e73d9689217700001ceae2d1244001600431ce7b2d1247c1778639dbeae3d968924580049e18e7571ecb43d78639d5c7b3c968921788642dcedf571ecb449800431ce7b2d1247a17700431cedf3d9689217786409ceae4b9ecb449800431ceae3f9ecb449700431ceae551ecb44978dc3210e7571ecb449893c31ceae469ecb4498003ddceae3d96892017
  | 7, 0, 1 => 0x218e7571ecc45a68dc31ceae469ecb44988639dcadf571ecb449800431ceae3d96892087863ddceae469ecb449886421cec0571ecb449800431ceae3d968921b70039d80ae3d9689201793c31ceae3d9689217800431cecf5725cf6497000015c7b2d124060160000218e7571ecb43d600431ce973d968921778639d9eae3d968924480043210e7571689220700431cecf3d96892177
  | 7, 0, 2 => 0x431ceae419ecb449794431cec0571ecb44988b431ceae3d968921780046e18e7571ecb43d78639dcaae4b9ecb449800431eee7571ecb43d78639dcacf571ecb449800479ceae3d968b049700431ceae3d9689233700431ceae3d92460267863f5ceae3d9689242893c31ceae3d9689230800431ceae569ecb44970045a18e7571ecb43d7000023ce73d9689217600431ceae3d96892177
  | 7, 0, 3 => 0x39d5c7b2d1247a01700431ceae541ecb44970039dbeae3d968920178dc31ceae3d968921788639d80ae469ecb44980000218f2571ecb44968b431ceae3d96892308863ddceae3d9689217800431ceae431ecb44978f431e0e7571ecb449800431ceae3d96892097004315c8d3d9689203700431faae3d968924270043210e7571ec9230795c31ceae469ecb449800001ceae3d92460016
  | 7, 0, 4 => 0x431ceae2d1244017786421ceae4b9ecb449893c31ceae3d9e4b44980039d5c973d9689201786421cecf571ecb44980039d9eae3d9689201700431cec0571ecb43d786421ceae3d968923e80039d5c7b2d1247c0170000218ae3d9687a03693c31ceae3d968a4498004ae18e7571ecb43d70000218e7571687a20686421ceae3d968923d80000218e7601ecb442686421cedf571ecb4498
  | 7, 0, 5 => 0x431ceae3d978b44978639dc2ae469ecb4498004315c7b2d124600370047a10e7571ecb44978b431ceae3d968a449895c31ceae3d9689230800431ceae2d124602078f431ceae3d9689242800431fae73d968921778639d80ae3d9689217800431ceae3d9e4b449700431ceae471ecb4497004315c7b2d1242e03700431ceae469ec9230795c31ceae3d9689217800431e0e73d96892177
  | 7, 0, 6 => 0x95c31ceae3d968a44988639d5c7b2d1247a17800431cecf571ecb43d78639dbeae3d9689217800431ceae2d1489220700431ce7b2d1248417700431ceae3d924601778dc31ceae3d9e4b449800431cedf571ecb43d78639d80ae3d96892098863ddceae3d9e4b44988639d9eae469ecb44980000218fd3d968921768b431ceae3d9e4b44980000218e7571ec7a3068639d80ae3d96892308
  | 7, 0, 7 => 0x8639d9eae3d9689217800431cedf601ecb4497004315c7b3c968920378639d5c7b2d1247c17800431ceae3d994b44978639d5c7b2d1247a30895c31ceae3d9e4b44988639dbeae3d968923088639d5c973d968921b800431ceae3c968922078639d9eae3d968920888639d80ae3d968a449800431ceae3d96892067004315c7b2d1489203793c31eee7571ecb449800431ceae4b9ecb43d7
  | 7, 0, 8 => 0x218e7571ecf23e686429cecf571ecb44988b431eee7571ecb44980049e18e7571689220700431ce7b2d1389217700001ceae3d96892006003f5ceae3d96892017863f9ceae469ecb449800431ce7b2d1242e0b7000023ce7571ecb43d68639d80ae3d9e4b44980047a18e73d9689217700431ceae559ecb44978639d5c973d9689217800431ceae3d9687a317003c1ceae3d96892017
  | 7, 0, 9 => 0x39d5c7b2d124840178ec31ceae3d9e4b44988639d5c7b2d148923d88639dbeae3d968a449800431cec0571ecb449700431ceae3d9e49230700479ceae3d9689230700001faae3d968920168dc31eee7571ecb449800431ce7b2d1242e0c793c31cec0571ecb4498004315c7b3c9a4b449786425cec0571ecb44980049e18ae3d968920378639dbeae3d968aa49800479ceae3d96892177
  | 7, 0, 10 => 0x431cedf679ecb44978639d5c8d3d968921d80046e18e757168922070049e18e7571ec923078639d5c8d421ecb44988639d5ca5469ecb449800431cec0571ecb442700431eee757168922078b431cec0571ecb449800431faae3d968ac4970045a18ae3d968920378639dbeae3d9e4b44980045a18e7571689220786421ceae3d9689242895431cedf571ecb4498863c1ceae469ecb4498
  | 7, 0, 11 => 0x431cee1571ecb4497863c1ceae3d9689217800431ceae3d9e4a44978f43210e7571ecb449800479ceae3d968a449793c31ceae3d968923d800431fae7571ecb43d793c31cedf571ecb44988dc31cec0571ecb44988639d5c973d9e4b44988639d5c97471ecb44980000218e7571ec92306863ddcec0571ecb44988639d9eae3d9e4b44980046e18ae3d9689203700431e0e7571ecb43d7
  | 7, 0, 12 => 0x431ceae3d988b449795c31cec0571ecb449892c31ceae4b9ecb44980000218fd571ecb43d600431cec0571689220700431ceae531ecb44970000218e7679eca449693c31ceae4b9ecb4498863c1ceae3d968923080000218ae2d12440036863f5ceae3d9689217893c31cecf571ecb449800479ceae3d9e4b44970045a18e7571ec9230793c31ceae3d968923e8004ae18e75716892207
  | 7, 0, 13 => 0x8dc31ceae3d968923d88dc31cedf571ecb4498863ddceae3d968923d8863ddcedf571ecb449800431faae3d9689217700431d0e73d9689217700431ceae489ecb44970043210e73d9689217700001ce7b2d1242e0168639dbeae3d968920680046e18e7571ec92307863f5ceae3d968923080043180ae3d968920378b431cedf571ecb449800431cecf571ecb449700431eee7571ec92307
  | 7, 0, 14 => 0x47a18e7571ecb43d700431cec0571ec923078dc31ceae4b9ecb4498863c1ceae3d968a449800431ceae469ecf25a70000218ae3d924600368639d5c7b2d124843088dc31cecf571ecb4498863ddceae4b9ecb4498004ae18e7571ec92307863ddcecf571ecb44980000218e7571246020600431faae3d968923078b431ceae4b9ecb44980039d9ec6571ecb44978b431cecf571ecb4498
  | 7, 0, 15 => 0x431eee7571ecf24978639dbec0571ecb449800479eee7571ecb449700431ce8d3d9689217700431faae3d9689246790c31ceae469ecb4498004315c7b2d1247a03700431faae541ecb449700431beae3d96892037863c1ceae3d9e4b4498863f5ceae3d968a449800431ceae549ecb449700431ce7f3d9689217795c31ceae3d968923d895c31cedf571ecb449800431ceae2d1247a207
  | 7, 1, 0 => 0x431faae3d968a4497004315c973d96892037004319eae3d9689203795c31ceae4b9ecb44988639d5ca53d9e4b4498004315c7b2d1247c03795c31cecf571ecb44988639d5c7b2d1242e0b895c31ceae3d968923e800431cecf57168922070046e18e7571ecf2497863f5ceae3d9e4b449800479ceae559ecb44978f431ceae3d9689217800431ceae2d1247c2078639dc2c0571ecb4498
  | 7, 1, 1 => 0x431ceae529ecb44978639d5c973d9689241800479cec0571ecb449700431ceae3d9247a307000023cae3d9689203600431cedf571ec923078639d5c7b2d1242e0c800421ceae3d9689201793c31fae7571ecb449800431faae3d9e4b44978639d80ae4b9ecb44980000218e73d9687a17693c31e0e7571ecb44988639d80ae3d968a84988639d9ec0571ecb44988f431ceae3d96892308
  | 7, 1, 2 => 0x8639dbeae3d968923e800431fae757234b44978f431ceae3d968a449893c31ceae3d968924288b431fae7571ecb44988639d5c7b3c9689221800431ceae4b9ec9230700431cecf571ec923070049e18fd571ecb44978639da8ae3d9e4b44988639dc2df571ecb449800431ce7b2d124601778639dbeae3d968923d88b431e0e7571ecb449800431ceae3d968921d700431ceae421ecb4497
  | 7, 1, 3 => 0x479ceae3d968923d78639d9eae4b9ecb449800431ced4571ecb449794c31cecf571ecb44980000218fd57234b44960045a18fd571ecb449786421ceae469ecb44988dc31fae7571ecb44988f431ceae3d9e4b4498000023ce7571ec923060039d5c8d3d968920178639d5c973d968923d88639d9eae3d968923d88639dbecf571ecb44988dc31e0e7571ecb449800431ceae3d92460247
  | 7, 1, 4 => 0x8dc31ceae3d9689242800431ce7b3c9689217700479cecf571ecb4497863ddceae3d9689242800479ceae3d968923e7863c1cec0571ecb44980000224e7571ecb449600431cecf571eca44970046e18fd571ecb44970043210e7571ecb43d700001ceae3d9687a01600431ce7b2d148921770000230e7571ecb449600431ceae3d9689221700431e0e7571689220700431cec057234f65a7
  | 7, 1, 5 => 0x95c31ceae3d9689242800431e0e7571ec9230700431fac0571ecb449700431ceae2d124842070043210e7601ecb449700479ceae3d968924870049e18e73d9689217786421ceae3d968923080039d5c7b2d124600170000218e757244b449600431ce7b2f1689217700431ceae3d9689c49786421ceae3d968921780039d5c7b2d1242e01700431ceae4b9ecf2497863f5cec0571ecb4498
  | 7, 1, 6 => 0x8639d5c8d3d968923080000218fd571ec92306863c1cecf571ecb4498863f5ceae3d968923d80045a18e73d968921778639d5c8d3d968a24988639da8c0571ecb4498863e5ceae3d9e4b44988639d5c8d3d96892178863c1cedf571ecb449800431fae7571ec923070045a18e7571ecf25a70000218e73d96892176004315c7b2d124840378f431eee7571ecb449800431ceae469ecb43d7
  | 7, 1, 7 => 0x86421ceae3d9e4b449800431faae3d968923d70039d5c7b3c968920178f431cec0571ecb449800431ceae3d9248430700431ceae3d9687a177863f5cecf571ecb44980046e18e73d968921770047a18ae3d96892037863f5ceae3d968923e800431cee5571ecb449700431eee73d9689217786421ceae3d968a44988639d5c7b3c984b44980039d5c7b2d14892017863c1ceae4b9ecb4498
  | 7, 1, 8 => 0x2187b2d1242e0368639d5c7b2d1246017893c3210e7571ecb449800431ceae3d984b4497004ae18e73d968921770000218e72d1244017600431ceae3d9689226700431facf571ecb44970039d5c7b3c9c0b449700431cec0571ecf25a700431faae3d968923e78639dbeae3d9689242800431ceae3d9687a30700479e0e7571ecb449700431ceae3d9687a3378639d5ca54b9ecb4498
  | 7, 1, 9 => 0x8f431ceae3d968923e88b43210e7571ecb449800431ceb3571ecb449700431ceae3d968a43d700431cedf5725cb449700479ceae3d968924278f431ceae3d968923d88639d5c8d3d9e4b449800431ceae539ecb44978639da8cf571ecb44980000218ae3d968920260047a18e7571ec923078639d5c8d3d968a44988639d5c973d9689242800431cec03d968921778639d9eae3d96892428
  | 7, 1, 10 => 0x431ceae3d9e4b43d70000218e73d924601768f431cecf571ecb4498
  | 8, 0, 0 => 0x431ceae3d92460d0c73b015c7b2d125c010c571ecb44901b4ae18e7571ecb449700431ceae2d12440d1b8639d5c7b2d125e18f773ab8f65a24bc5a18e7571ecb449700431ceae3d96892d278639d5c7b2d125e18e7571ecf25a24bc31ceae3d968a44978639d5c7b2d12460f0c73ab8f65a2485dc010c73ab8f65a1eb431ceae469ecb4497
  | 8, 0, 1 => 0x2190873ab8f65a24b801ceae3d9689201600431ce7b2d1242ed1e8639d5c7b2d125e18e7571ecb44921380218fd571ecb4496863f5ceae3d96892f0c7839d5c7b2d125c011e73ab8f65a24b431ceae4b9ecb44978639d9eae3d96892f0c73ab8f65a248f9e18e7571ecb4491ebc31cedf571ecb4497
  | 9, 0, 0 => 0x218e7571ecb4496
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
  | 0, 0 => 0x1f1c003840e000c0ff81f007f03007007c00300c003801000300fffe003fffc038ff800fc7f000001ffffffc0000071ffc7f
  | 0, 1 => 0x1c1ff03f80ff0707e38e003f30003fe07801fc000fc01e007c00038e00001cc7c71f8ff038f1f1c703fc0e307c7038e10383
  | 0, 2 => 0x1f1ffe3fc0ffc7c7ff8ff00001f1ffe3800e007c7ff81e007c1f1ffe00001cc7c7000ff03801f03f03fc01f07c0e38ff0073
  | 0, 3 => 0xe3e07fc7ff03f8f8fff1f0c7fe3e071c7c30338f8fff1ffc7fe3e00fc07f00f8f8007010c001ffffe3fffffc7c7fffffffff
  | 0, 4 => 0xe0e00fc03f00f83800700fc001c1c0e383ce0c00003800f003fffc71ffc3e33fff03fe10f83fffc01f843e038f8fff1ffc7f
  | 0, 5 => 0xfffc0ff840003fff03f00fc00fffc0e3800e03fff03800f003ffe001f87f003fc7007e10380ff000ff87c00ff3f007e0ff80
  | 0, 6 => 0xff1c01ffc0e03fc01c7ff000cfcfc01f803e038381c71e0c0ce0e001c0030007071c0fe038c0000700780033fff03fe1ff83
  | 0, 7 => 0xffff81f843fc0000e00000070fffc71ffc3e33fff1c7ff0000fffc71c003003fff1c0e00380fffc700780033ff8007ff0c00
  | 0, 8 => 0x3c000000000000000000000003c000000e0000f0701f1c703ffce3000000000f00000038000001c0000000000000
  | 0, 9 => 0xe3e38fc07f1cc7c7ff8fff3ff1f1ffe3800e007c7000ff03801f1f8e387cfcc0c0ff81ff07f00038e003c1cc000e38000000
  | 0, 10 => 0x7800000000001e00000000000000000000e000000701f1c0e3840e0c00000000000000038000001c3838e3f00fc73
  | 0, 11 => 0xe3e3f1c7c31f07c7ff8ff03ff0003fe07801fc7c7fc0ff03fc0303fe07c01fc000fc01e007c0003f00000000000fc0000000
  | 0, 12 => 0x38e003c1cc00000000f0000003f007bc1f0000fc00000000003f00000000000e3800f073000000003c003838fc71e0c7c
  | 0, 13 => 0x7bc000000fc01e007c0000000780000000e381ef07300000007800000000001e00000000000780000000000000000
  | 0, 14 => 0x3fe003c000000ff81e007c0003fe0000000000ff800f0730003fe0000000000ff80000000003fe00001c0000ff8000000
  | 0, 15 => 0x1f1ffe3fc0ffc7c71c0ff038c1f1c0e3840e0c7c7000e103801c1c003800e000000000000000003fe07bc1fc000ff81e0000
  | 1, 0 => 0x1c038038001c0707000e0f380000380003c1c000000000f0001c1f803800fc3f3f007e00f80fcfc01f83fe03fff007e10f80
  | 1, 1 => 0x38000001c00000000000001c1f8e383cfcc707e38e000001c1f8e003c000707e380000701c0000383c000707000e00380
  | 1, 2 => 0x1c1ff03f80ff0707fc0fe00001c1ff00000000707fc00000701c00003f80000700e00fe00701c1c003800e00000000000000
  | 1, 3 => 0x1c00003f80000707fc0fef3fc1c1f8e383cfcc707000e0f38000038e003c1cc000fc01ef07c00038e003c1cc00000000f000
  | 1, 4 => 0xe00001c00000380000700f0001c1ffe3fbcffc707ff8e003f01c1ffe3800e00707ff80000001c1c003f80e00707000e00380
  | 1, 5 => 0xe3e001c07f00383800700fc00e0e001c000003838000000000e0e0000000003838000000000e0e000003c003800007000000
  | 1, 6 => 0xe0038fc03c1cf800007000000e0038fc03c1cf800e07000070e0e381c03f1c3fff007e1ff80e3e071c7ff0338f803f01fc03
  | 1, 7 => 0xe0e38fc03c1cf838e3f000000e0e38fc03f003838e3800f073e0e38e0000003838e3800f073e0e38e00001c383800700fc00
  | 1, 8 => 0xe0e3f0003c1c3838fc0000000e0e001c7bf003800fc71e007ce00001c780003800fc71ef07ce00381c7bc1c3838e3f00fc73
  | 1, 9 => 0xe0e3f1c7bf1f3838fc71e007ce0e3f1c780003838fc700fc00e0e3f007801f3838fc0000000e0e3f00000003838fc01ef07c
  | 1, 10 => 0xfc1c01f83ce03f00007e00000fc0001f83c003838fff1efc7fe0e3fe0000003838ff8000000e00001c7800038000071e0000
  | 1, 11 => 0xfcfc01f83fe03f3f007e00380fcfc01f800003f3f000e00380fcfc00383ce03f3f000000000fcfc00003c003f07007e00380
  | 1, 12 => 0xff0001ffc0003f3fffffefffffcfff1ffbfff3f3ffc0e00380fcfff03800e03f3ffc0000000fcff8ff83ffcff3fe07e0fff0
  | 1, 13 => 0xff038fc03c003fc0e38e00000ff038e07801c3fc0e38000000ff0001ffc0003ff8007ff0c00fffc01ffc3e03fc7fffff03ff
  | 1, 14 => 0xff03f1ffc01f3fc0fc7000000ff03f03800003fc0fc0000070ff0001ffc0003fc0007ff0000ff00000000003fc0e3ffff073
  | 1, 15 => 0xff0001ffc0003fc7e3ffff3f3ff1c01ffc0e03fc7007000000ff1c000780003fc7000000000ff03fffffc1fffc0e3ffff073
  | 2, 0 => 0xffe001ffc0003ff8000e00000ffe0000780003ff800000f000ffe0000000003fc7fc7ff03fcff1c01ffc0e03fc0007ff0000
  | 2, 1 => 0xfffffe3fc0ffffffff8000073fffffe3840e0ffffff8000000fffc01ffffe03ff8fc7fffc7cffe38fffff1cfff8007fffc00
  | 2, 2 => 0xfffffe00001c3fffff800f073fffffe0000003fffff8000070fffffe0000003fffff8000070ffffffc003003ffffffe10f80
  | 2, 3 => 0xfffffe3800fc3fffff8e00380fffffe07bc1fffffff800f073fffffe07801f3fffff8000000fffffe00001c3fffff8000000
  | 2, 4 => 0xffffffc03f003ffffff000000fffffe3f80ff3fffff8e00380fffffe0000003fffff8000000fffffe383cfcffffff8e00380
  | 2, 5 => 0xffffffffc0003ffffffe0ff80ffffffc7bf1f3ffffff00fc73
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xc0920130042020040040000004002001000200fdb6002fef4018490009428000001fbdfffc0000030b546a
  | 0, 1 => 0xe0ed21d80754343a686701d70f0eda1dc075c282b4056015405068a08c034c3c31687501870a08501500410141028210083
  | 0, 2 => 0xf0eda1dc075c3c3b687700420f0eda1d006543c3b685601540f0eda0cc034c3c3b687701d70f0ad81dc05583c1b287700d3
  | 0, 3 => 0x63606cc6710290d09a21b044a42406086010208c893113c04221200c40700080000000000000f6ffe1de57fc3c3b6b7f55ff
  | 0, 4 => 0xb5b40f687aa0ec2c01580ea00b5b40f687aa0c94903921e0839a98513502c1256502ca10a8390900120028018d8db31bd46a
  | 0, 5 => 0xb5b40f687000ad6d03d80ea00b5b40f282aa06d6d03921e083b5b00d687a80ad6502da16a83b5240f687820ed2d01da0ea81
  | 0, 6 => 0xda9851b702c136921c6dc050cd8d831b303c336b61c6dc0f0cd0d021a2038236b61c6dc0f0c4a48709701432d6d03da1ea83
  | 0, 7 => 0x90938120869c0000e00021070dad871b703c336b61c6dc0000dad871a6038236b61c4d40b04dad87097014336b4186dc0e08
  | 0, 8 => 0x25278e48fc3cc941a292360d3242586483c2c4808e1102f0702a2954553c49080841100f020040782088c3c41016082030b1
  | 0, 9 => 0x25278e48fc3ccbcbf7977f1f72f2fde1d28654bc3b697761d725278e48fc3cc9c9f3933f0f325278e48fc3cc949e3820a091
  | 0, 10 => 0x4a4bf097855f1282b425e01544849b093054f1010e820a147845452a8a452ad010482081428080b9011845d2d6de3da3faf3
  | 0, 11 => 0x4a4bf097855f13d3fea7f15ff4f4ffa9fc57fd292fc25e157c4b4bf897c55f9292fc25e157c4a4bf097054f1292fc0540114
  | 0, 12 => 0x6d6fbedbfd7fdb1b6db6cf5bd6a6bf4d7bd5f1a9afd054a1146a6bf40420001959ebb2bf4fb606124c23d0a36b6fc6de1f7c
  | 0, 13 => 0x6f636cdffd1a9bd3feb7f75ff6f4ffadfdd7fdbcbf7b7ff1f76f0edadfd875dbd0da37f546a6f0248dfd0109bc0921774042
  | 0, 14 => 0x6f6ffec63d0a1bdbffa7eb5fd6f6ffe9f2d6f5bdbff977f1f76f6ffe1d28655bdbffa1894286f6ffe04a41c1bdbff8108000
  | 0, 15 => 0x9f9edb3dcaf5e7a734cf42b959d9c9b394ae5e72724ce42b959c9c93390ae5672724ce42b956f6ffedffd7fdbdbffb7fc042
  | 1, 0 => 0xbd0b9979d45daf2f65de4fbb5b8bb9571bedd2c2c41580fa209c9f93398efd77372ceec2f9dbcbc97793ae5672724ce42b95
  | 1, 1 => 0xd4d7a3aa8fbe7434486883e28bdbf9f79fefdef6fe7de7c042bdbf9f603e882f6fe78469174bdb30d79fe98af67a6de76bd7
  | 1, 2 => 0xdedff3bf8fff77b7fcefe0040dedff3a60f8a37b7fc83230f1ded361bf8f9a3781f0efe30f1dcddb3bb0fef76366c6cc3f3c
  | 1, 3 => 0xff0249ffd010bfbffdffefffdfdffbffbffffff3f6dfecffbdfdffbffbfffffebefd7deff7cf5f7afeaffbefc3c49788fe28
  | 1, 4 => 0xf04121e2150a3c0841788f020ffffffffffffffffffcf6bbf5ffffff3d2ae57fffff8108000ff9edbffdaf5ffe7b6df76bd7
  | 1, 5 => 0xf0f125e23f8a3c3c49788fe28f0f125e230003c3c49688be28f0f125202a803c3c492089428f0f124403c083c24007886a00
  | 1, 6 => 0xf5b78feafebcfd65a2fab6ad3f567afeafd3efd50ea7ab547af0f3a5e2bf9e3c3c49788fe28f2f165e63f8a3c7c4b789fe2a
  | 1, 7 => 0xf5f7afeafc3cfd7debfabc042f5f7afea3fae7d7debda3faf3f5f7af282aa47d7debb2bf4fbf5f7ae82a51e3d7debfabfefb
  | 1, 8 => 0xfafbf444bc1c3ebefd0108000fafbf5f7bfdf3eb6fc7de7f7cfa9ad1f79ad53e9afd7def57cfa23c5f7bc1c3d7debfabfefb
  | 1, 9 => 0xfafbf5f7bfdf3ebefd7ded57cfafbf5f7b0103ebefd7dcff3cfafbf5b7afdf3ebefd6dcbf3cfafbf5352ac53ebefd35ef57c
  | 1, 10 => 0xfcbd97fb3eed7f126c7ec553cfc2587fb3c2c7ffffffffffffffffff3d2ae57fffff8108000ff9edbffdaf5ffc0927ff4042
  | 1, 11 => 0xfcfdb7fb3fef7f3f6dfeceb95fcfdb7fb30003f3f6deecbfbdfcfdb7793eed7f3f6da4c953cfcfdb6483c2c7f376cfec7fbd
  | 1, 12 => 0xff0249ffd010bfffffffffffffefff7ffbfff7fbffdefcbfbdfefff73d2ae57fbffd8108000fdffbffbffffff3fedfeefffd
  | 1, 13 => 0xff27cfe63c083fc9f3cf4a091ff27ce97a41c3fc9f3a189020ff07cbffdc3cfff49a7ff4e4aff9249ffd290bfc3b6fff41d7
  | 1, 14 => 0xff4bf9ffd55fbfd2fe7985428ff4bf93d00453fd2fe1335072ff4bf9ffd55fbfd0da7ff546aff43684cd418bfc9f3ffff0f3
  | 1, 15 => 0xffd369ffdf9abfeff7ffffbf7ff9edbffdaf5ffe7b6f986a00ff9eda9780553fe7b693360d3ff6ffffffd7fffd9fbffff4fb
  | 2, 0 => 0xfff36dfffa90bffcdb4f4aa00fff36c97a51a3ffcdb133f062fff36c04a4183ff7fefff7fffffdffbffdffffff6fe7ff7f7e
  | 2, 1 => 0xfffffe1de075ffffff83380d3fffffe0c6020ffffff8108000fffffffffffffffeff7ffff7efff7efffffbefffcdb7fffe6a
  | 2, 2 => 0xfffffe15a45d3fffff933f0f3fffffe4cf834ffffff832b0f1fffffe0c2c2c7fffff8129070ffffffa623823fffffc908a00
  | 2, 3 => 0xffffff3daefd7fffffcf4ab95fffffedffd7fffffffb3bf4fbfffffe97a55f3fffffa5c953cfffffe86a51e3fffffa189428
  | 2, 4 => 0xffffffe63f8a3ffffff98ea00ffffffbfafff7fffffefcbfbdffffffb72fcf3fffffe98be28ffffff7dfefdffffffdf7ebd7
  | 2, 5 => 0xfffffffff010bfffffffcffbdfffffff7bfdf3ffffffbbfefb
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 50 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 50 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 300 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 300 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 300 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 300 then wireAt i else 0
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
  | 2 => 1
  | 3 => 8
  | 4 => 99
  | 5 => 723
  | 6 => 1925
  | 7 => 958
  | 8 => 15
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0xed0ba7f0
  | 3, 0 => 0xf60ecf46d6232e25a324e6f2689b718f51c3ea743a6bef7f303766e90f426ff8
  | 4, 0 => 0x9f7526dd9d459b7799832b9797a5253495ff73989110e32d8cc6eb378acb7105892ea2ab86cb64f9845b016e80a6da4c7eb943ee7d90d7197ce3060d79feb8b17805182c77bab5ab75e2624175c12840759cde3971fc57526ce160666b25caf163d55b9f630a008d5b8f610a58f4db21543af2ce4f83e1b74def793f4abb1d6f49fd1e6b4951ae68474f28d147241fa945d2eafa41084baf40cc9d103d04c4783cebd8d135600ddb303ccc5f29043e2526b04f4020c7b0ce204ad69b1f8f45a71eedd9fc1d13199b18a58279172e384a1621e0430ff7dafb0ed45ebc0df2bf980def5aac0dcc774e0da2f0d70cfd4e450cef530208d811960867fd68084a5880
  | 4, 1 => 0xfcc5d5b5f32fc0cef2ef86ebee2e5239e1888794e0a53e3ce012e0c6daf0d667dabba79dd8d53eb9d7624249d5bbfdecd2415403d0cc9b4ecd90b780cc79e1edcb7ba95fcaa27bbfc94b9bb1c732ad0ec61d5aedc3b517a2bc83c90fb927efe3b2085434b1e71770ae190e7eada675f1ac7e0d0fabb141d7ab10af44aa4045d5a8fe2379a77a4ddea1946aff
  | 5, 0 => 0x13bf8c24135bd055130a5c1612ec372612aced29129fa7fd1299497c1244342111a44754119dfe101192001f114fce0c1120e2e3109f8fb3108a8674102400b20fe5f2a70fdec5b70fd0edc50ef2d2bc0edf2f2c0e55716a0e15721d0cd92b840c2777f60c21c3560bd5dce90b3239bd09f4089109d0c57e09adf9d1099abdc409335f11087149db086e08a3085a260f08373b7c0807792307e998db07c8b9b30743a30b06fe0c7c06f6939e06b250ec06ae47df05fd06d705f5b00605eee5d804b4455c0469c1c7045412d003b1c3d00351e975034afbbb03421fa9033eb4db02c6626d025861250223c06a01c03b0201b54c0b00e3021600c274f100904a51
  | 5, 1 => 0x2ae793e92a93c93429af0976296d9ffc2949c4982884fdf82810052828007d2a27fa285b27e4c34027add3f227a8a3f5270f28642705880d25ea45ee2541a1e0251b288724b4966c2460211b23e92d122246fcf021d5db3a217c18ce20f029a020c56933206d0bcf1fe0906c1f426e131f0740291ec256a71e64a3c31e313f771e02d8001dfc58011dcf29111d3dffd51d360a691d2143e41cdb8cd11c699c801bb834231b9386ad1adf1ef61a1f37bf1a1daaff19c24abf19b3c5f0194ec74918f325e618f26c4c18ae189c187d0f6b17c6219b17a61d62176346e016f2cb9216ecceb9169f119e16716f5b1621e04315dac5e9153eaa1813dc01c413cf35c5
  | 5, 2 => 0x421eb534410c88e1409bb26640722d163fc4defb3fbea77e3fad8f4c3f8bbd3f3f7098da3f54840f3eab7bf33ea347e93e9c32c83e56c1683e04c0723dde76173d505c953c78af4e3c6b79a73c57d5253c2f57bf3c1fa3d43bd82cc93b9680a23b054936389a23f937f8c67a37c66edb377ab9dd376662873761c3f336dcbfb136a8c2383674818d35ee51be359e20953505b6fb34c851ef34b052553480fa58341fdf1833d5399b330f14783271cd503268d4fb3239456f31c32dd13115c93030b3c7d0300680393000f80e2fd181c62f0ac9132ef7b6ea2ee611342ebed3bb2eb983852e80cd732ded0ebb2d5b9c6c2d028d5d2c5ac63c2c45359f2b74375b
  | 5, 3 => 0x5a383b9c59f502be59b8c80d59a81d935954785258f528b758de4bd558d5e2955832d09b567e41cf55bbd2f055383e8253c5d37d5318541d52aff76952806a6251ef29925198e0a65137e59450450396500f1fa2500d4be74ffd65c74f5a105b4edbcdea4e58e5db4e29c7d14e2355ba4e1eb31a4c7acf5f4c32c98e4b8574484b83735c4b02581f4a929dfa4a899ff94a70f06247dd17c847b4abff47287742471c98aa46b110c0466bf2a64645a3f54643b5a54640e97e45de5f1a45ce2e294549c267454310ba44f25f2644efb4cf44b733b3443bc0a443091b4242f1fa8b42eab0b642e92eab42d48b0542b779a34298de82427ed8d6423252c5422c19c3
  | 5, 4 => 0x70adf63e708e3d3a7086143f7033375d6fefc60e6fe06c296f82efcb6f6571206e9f17c16e6d26566e5d2e3b6e111e4b6cb081016c3e88df6c10cf366bd11c156bcf90f36badac316b9318dc6b0981336aefed426ad62f646ac1a0f46a1a8bbe69bcb1c368c235f0689f85b866e193ff657fa726657914db6528c4c9637bd11363681aca6307673262f9b0eb62b2b0a7629db8d16294d7e761f5a73b61e48c9561c4af0f6181a41760a7ce44605a49426049df5360168b5b5f462eec5e730bba5e4be6235e42f9625e3fd68c5e22b1fd5e1107985de7fec25dc903805d89ccf35d3cc0765be44dd65be0d81b5bb6c60e5b796d475b5689a25aa8a6b95a55165b
  | 5, 5 => 0x86fee2ec86a4d00a86925a64866e3ba385d14e80850c74d184f8ef6b84987d05847b982684129c4083b736de832189ea82b8d63d82a72bca822d8caa81c1d1c6812f07f48112076c80cdcee2804aa3b0802e890e80087aa87f2210c27ecb7f377e871de57e7152747dd0cb7e7cf270267cdf2fa47ca64a5e7c5adb4f7c5490e87c35140d7c306b6d7b979e707b8f9e427b72281d7b6362a27b2b17a17b23417a79e6d45179835c6e7853636378363a71767c5d42755ba818753f0566751113a0740ef46673faa17673e4c23173bcf26973b9b909733290bc73221ae072ac28357268845a722a71d271c4c2dd71c3dff871a7a8897147b3d970c5a4ca70bd21a0
  | 5, 6 => 0xa070ad90a03a41aea01d11f79f8b05bb9f52393c9e5b41d39d5e0e199c7f3b019c1f10a99b8a57529b0d0fc39adff9ea9a6945399a4e8d8e9a4922e59a4682a099de0c9099ac50f5993824c798c0bf6f98b5a1d397ceacc3977ed1a0974c8b9f9742e1059702dd0e96f1613796d86ce2961a44a195c7f38495b907ff9559495795069a7e93bf213c936378079268a0bc9220e9a991e523f791609da7909c45b8907b694f906af4ff8e8c69608dfec2528de455e58dcf97c28d90e6f28d5a4ec18d3534808cfb70658cedacd18cc282af8cb824a98cb5310c8bf5595f8bd5ef478b8bf21b8acdc3638a6d7dde8a28dcd4890db2d2883c679987e64cc1879b79a4
  | 5, 7 => 0xb542871cb5406affb51ffa20b331515db32de68fb2f8b09db2dfaeb1b2666447b24d010ab1aa955cb172b195b164a8abb143fc31b1084a16b0bcb6dcb092cc10b06d7fccb05bf62aaffacab8af8bf02eaea48dc0ae8b5846ae40b070ae1b1d36ae0021f9ad04b00aacedf229ac8ec481ac76b407ac58602fac2d5707abd19988ab97eca5ab4bc5abab2d8538aadc2258aa879d64a99797dca9789f6da95258eea6ac57a1a6abffe1a64ea6dfa611830da60d590da5d5d46ea5777bf2a56db28fa5378064a5342840a48f4794a43f6bafa3105a4fa30f2c71a2649992a256c1a0a24442aea2327799a167ab79a127f4a4a11323b6a0faae62a09730c1a089409d
  | 5, 8 => 0xccc4c05bcc34016fcbf71b79cbf4f15bcb789be5cb6ed8f0cad05078c9f2a206c9bbb852c9ba0de4c95b0440c8de92fdc858f251c820b6bac76f2ee3c76b6ab0c73fff91c6a07237c4f7a12bc4bed34ec4b67857c40c2e54c3d5d573c3baf135c3a7fa27c373b307c2d92d22c29352fcc255f098c24c330ac22ad897c19af202c13f5760c11acc9bc0cdefecc0928042c0440dc4c036486abf8705ebbedd9d2abd6d67c4bd525c98bd3530b1bd199d0fbcd62099bca7146dbc8b62f3bc82f4bbbc8249c2bc41cd4cbbb787aabb68bd29bb5bf358bb2c743bbaf33382ba68ab79ba47eeb6ba0d3369b8b0c928b777ceffb72f59aeb6ff990eb5dd3eb9b5671537
  | 5, 9 => 0xe4424211e417b86ce3f2dbe8e2fac4fee27b0455e1ec3d6be1d58b5ce1c9df61e13593a7e10ebe2ae0610bafe03ae746dff65054df3d5635de2abc10de1c8bb6dda7c63edd90a44add1abb82dc9a3425dc894658dbc3afcbdade8469daca5f9eda8ac8e5da7e4c2ada24f17ed9d87172d9360cd8d899bfc1d8540204d7b4d507d74fd5ccd6d5df35d6caf2f8d69c53abd651f12ad5f05dd2d531990cd5214da5d4de3103d4b826a0d4ad7a42d46c8f66d3b847d9d39f72aed393cc07d3886fabd28e4411d260d727d1fe607fd1f695ddd1941c87d16186ccd1294f8dd089d057cf3edb34cf281175cebf7783ceb52b9acea577afcdc25462cd40a50dcd3de873
  | 5, 10 => 0xf88edacbf821c371f79316e9f6eadee7f6b41a82f660ee02f61a1a8bf601a4eef580c509f482be77f4725183f46a6070f44935f4f428c717f2d175dcf2c0232df2b6afd3f1ddc08df1dacc65f195102ff120615bf0f8df95f0233337efd4a863efd221f4efa9fe19eea93419ee58bbd2ee1ffc1eee08b194ed82a6cded8209ebed0f5146ecdaea36ec9eed60ec6d9f47ec4e0eccec2eb1cbebbf06ddeb9f4f67eb5e26b6eb54fbcdeb1b78e9eac3b1b3ea93f82fea6e77a2e9ee24e9e9dfc586e9d23b36e9707aece96da3d2e8d96a67e8cc0adae85c655de841648be7bb4e07e743f1a6e64ba758e5a6c51de59969e5e58c1d85e5466d31e4ad60e1e488f426
  | 5, 11 => 0xff819ea7ff7c7227fee24069fead2cf8fd9de17ffd685c8efcfcb63cfcd15abbfcc4bfbbfb1fea94fb1bc8fafaf4e16cfabe68c9f9a3acbdf96feb04f96767daf9328453f8aa7cf2f89a03ef
  | 6, 0 => 0x6a14de7068d7fe10680b92c05c61dd605bbae7e05b8649705b43f600555b2b9051a6ec905169eb004dbb86404c4bfc004bca65904ac2cb3048dacd7047b57a904253990040eba580404ee0e03ebaeda03d31bcd03b67192037b8ad90376fe1b0375c6cf0357f0400341d11b033a727c031d0181030d3b3002f1f85902d6a72e02c1685702a27623029bda2f0293b4520289e8080284a245027c6a3c0266400402470b1b02465a510232af73020e052301e3cad001a6e4da01a0c3aa019c9fad018309d901752afa01652a320146c416013e3f93012c73fe012a584000f5a3d200da586b00a28bea0096f226006cf49b006c26840046618f0034aae000296567
  | 6, 1 => 0xfaa77070f8b2a5f0f8899180f3d84400f31b5270ee2d2210ee271f80ee0af2a0ee057d40ebee7890ea800b80e7e15130e737a980e67dc250dfb96ef0df124ef0de298690da91e400d91ebc20d86abda0cedf22c0cd896110c18c4240c13a5aa0c0ba5d40bf303a40bcc18bf0b9beb890b8ad6cc0b641d450b59e3bd0b25135a0b05d34b0afb5dd30ae34fac0ab8b2690aa0caca0a577bf40a3ff7660a2d481b09ede5f809e3b12e09bd51ef097689a8093e73560938390c090dfc8408cdebfc08b0816608aedd4608739b70085c29ce084ecf14083843fe07d1c87f078c60020787d7a5076636a7074eba9407492140072f1b210711d49e06fe4f3806ad70f9
  | 6, 2 => 0x17fa4d9917e7c6aa17ce2ba217cb86b1175a929b17563868174a0ecc173aec27172938d71708743b16d828f516b3ccba16b01e5416a61199168bc85d168410e61673385e1665ef1c1661bbe9165a1433164f38e0161181741606144c15f3a94215e9498b15d3ee201596d48d1589d57c155ed0bb153eaa18153802db15212d4d1517feab14db18b514c7480c1499cfe51404726713fac4d313ea83c213e90d2b13e0e2a713967e2f138cad001349e7ce133c08ef13346ed1130a5a8912d1fe4012aced29125d0b7e1233466a11f373c011b4bd5b119b91ab1187183a11408e9a10bf6ca6103a9912102d8cd3101fadf41004efa21004221f0ff651070fec104b
  | 6, 3 => 0x22e093b2228be26a226fd984221388372177d42821357f502062e28420292edb2014c6442014059b1fa432931f8738591f75faad1f634b621f3387171ee07af31ed20e051ec0fa371ea60e4c1ea327491e6285251e08e1531df468421de45f961ddb52551db574801d73f5661d07cbc61ca3d9531ca0b1831c5377201c5376f01c397d011c32bad41bcc6c301b9d622f1b933b9e1b8548e61b78d4bc1b62a5db1b27d2611b0bab3e1ac6cf551a87fcc01a58a2341a548add1a4058c31a0dc40d1a04d9791972f1be194727b519224d721921f28d18ef4baf18bf975f18ac994f1882b1691880d8c818545dd61839cef0182b10bf18103f88180c2da518043d69
  | 6, 4 => 0x2d52d1502d2230702d1894d92d06d0c22cf8cd042c5dadfc2c119b4b2bfff1562bd19fe72bc2b7902b81626d2b5787d12b4875c42b15732c2b08f8cc2a97a7b92a42cf9a2a14d0f72a00355d29f1177429f0b1cd2980ce66297c99f8296af49a295678be294399dc293f76f02934275729319d852930c81a292162fe291d2a9e28e1d56328c73e9828b1318528a4a83e289a985c28668e6d2844d639279ad890275a7690275958f22750b4f6273a86802713cf002705880d2664076226488ebe262a32f4259a31372578e98e25318cf4250b3e6a250aba5724ae713a2467ee6a24425a84243971d523e92d1223b12dec2359c6d0233e5198230229b922ec6a87
  | 6, 5 => 0x34f3ec2d34f1480534d2fbb734c8f0c734c7a967349824f43492603134886bc33473d1a6344f47aa34064f6c33df688433da662c33d93c6b339be8303398d185338e027c338cf14333422da53303cae532f11b9a32ecdd7e32e16b893294f0e0326a5494322a93ea31f5eab3318b16ac314b726931381b07312099a03112a29330d5282030cca4c4309ade1b3096bd9030959bfe306f6ccb304b0f21302a0a26300cd34d30010ce22ff2eea02fd3b15e2fc6445a2fbf35272f48cad42f3c81e32f2d39052f1a95f82f1488772efbd9642ede35262ede098d2ec68d272eba05a82ea523322e2eb6002e142ffa2dfdbfd52dec4b6b2de6358a2db09fc22d618f3b
  | 6, 6 => 0x3df99e973dace14d3d8f565c3d8b1b8b3d5d39623d1f3f593d12016d3d0b3b903cedcf813ce437ac3cd249253cb938473cb227733c9ce34e3c644fe93c5112f13c38e0113bdc2ed73bb70e843bb1f7013b9031bd3b8aa58d3b5624293b34c0e23b33d6c03b28a8c83b1015bb3ae826bb3a67daad3a388a373a2d6c6239ddf64839b1034539a39666394f1420394ead04390153ab38a4a5e23885fcd2388012b1385204ef380d7bfe37fdfb7837b0b97137a858a737962c63378ba63f373fb95f36b5383e3679dd0b3678c0eb366487033643e73e36282139361d6c383618de163610a03935fe022a35e23d5c35d89aaa35974020353aa3c6350fe1ad34f524f9
  | 6, 7 => 0x46bddc5e469949b5467c9b5d4649a34b4639627f4617f58845f126ed45d91ef145b797dc45b71f03459774c245940ada456daacd4526b408450ea01a44d46f78446729e644578d0c4431695943f5039043df582343aea1a443ab146a4330d951432e5dba43110caa42e28e1442ba8c1c42b779a342b451b04291ffc94214c55a4210028741b4d9a6418c58194183d8874119dfa1410d769640cde8cc40a60e37408f5a30408a21dc404b301340455b7a403528553fb3ab613fab5da13f9a82dd3f8054793f7f6a493f69e5183f62ae583f545ac33f4e227d3f1e2b9c3f086e6d3ef9b7083ecbdd503eab06f43e9e85263e3e67183e38a55b3e2f1fca3e277fff
  | 6, 8 => 0x4fcc8ff24fc71f074f9d2f8d4f7735ef4f7141a24f6f0b154f159ccf4ea4fa1c4e79b24a4e7855394e65ab694df560734dd542384dd3ad484dc9c7c04db248164cf5a2254ce11a174ca61d4a4c7b14224c46545e4c1e35cd4c1a30724c1326ad4ba260e84ba1260e4b83735c4b40518f4b29df734b2472944b226b904b21fba14b093b3e4aee73794ae54a4b4acdf8d54aab8ec54aab55a94a8b09ee4a7c767c4a3f5f3c4a1660524a0a039049f952cf49eb066449e3bfbd49d9a14a49d72e8749b6983f498effba49802bc148a811f8486ff37c4863129447f0cb2247ee69e847b4688547a02cf14766fac84746a66547335cda470853b246f379b846df279b
  | 6, 9 => 0x58e6c54658cb5ee558a9df505837177e581a3e365808a35357ce35d15794fb70576f03e75764b6495742a79556f3df7156e8a03d56e6f7eb568ff7f1565eeb7f563d70e056385430563580cb5615047155f9c36e55e93b6a55914c4d5571ce4a556f06955521817b54f251df54e3e57954b5735e5488605d54583324544183055421f2ba5416d04b53e2c57853dbb72c53ba6d32538ec419536b8d0a53466db853447d0453346db95318541d52b1ef95528d58f75281620b525afe54525316e951ccc13e51bb2a0f518d110e51761d5f51608443514aca6d5137e9295124950150ea111b50a9730450a1bacb507207e45069bcbd506958575059633d50013940
  | 6, 10 => 0x61f427ee61dfaca961ca400861874d9061818f6f613f4bb66115d86e60f47f6c607744386043727f603f22b9602f2d62602921f26017f9735ffe18ca5fbac6fd5fa9e2065f4c3dc55ef0b1fa5eebf4b85ed6a3f15ec41cb35ec2fe405eace41b5ea610db5e8886d85e22a7545e1bc49c5e13ada65db7bfac5d9a53b05d8bf1475d5624535d3f7bd25d384f2c5d1e66bc5d0eae245d00c56d5cde0cce5cb55e505c5ccb105bf13ab45be0d81b5bc0ce6c5bb03c075b8f00c25b6a25605b4dbe2c5b1f7a795b00c4075aecd9575aea31985abc6cf25ab003015aa8a6b95a9f5dfd5a8723c859aeef8f59a0c2fc59907843596cee2e59483db5593aae7859255cf6
  | 6, 11 => 0x6b1be3666b09bc616afee7646a9639c16a9119966a4f22086a41599e6a2177b56a08291469c0add469ac57256969e1b66909bb4668b29a2d6886c0b6687631ad684a905367f4aa3e67c13f6967a2a1066785247967757f6167619883673f974f6733c99a672edba166fc78da66eea10d66ea172966c9726066ac6aec663e596f661f8dfe661dc2cd660f2a8665e88a3d65aa06876575faf26560b6cd653397fa653364ff65088ed264e6ab0264d90bd964b23f0e648a2c2b647e187f646d8437642e54a0640f62e363fb6a7f63df885163bad2eb63b75a2362dfa08f62d4bd2362d2e70062bf39f9629d973362623a35622a4e0c6212a51f61f63a0061f5a73b
  | 6, 12 => 0x76c6a15d76a139dd764e5f6176076036759b9aea75364d1d752d38107508aada74b765887448134174068ac973fa28f273ea5b6e73da4b1a7388972f734eaa0d734049fb733927ec72c5abb472b28339727718da726a4e01722b1a8271c7957571b731cf71a6de3f718aa31d7166cf877108872f70b49ea1705b5d9f6f7090bd6f54c88d6f3a9e9a6f29bf656f0659c76efd35fe6ec7a3626ea7701a6ea6a0236dd08b0e6dcf6ff56dbbe1966d9b14bb6d8ab79e6d6074136d5b00e46d1b608b6cbe1d396cb3a7766cae50056c79ed6a6c4b6e046c3a90ed6bd6e2826bd3e8686bcf90f36bbdf9a36bba04806bab48676b9d976b6b713d786b70d1e96b50e1d9
  | 6, 13 => 0x7e4dc0ce7e4b58517e3cacea7e25afd37e22428f7e1a8a567e16e3887dfb85ac7df7c5a07ddacfa87db1e1917db173387d4bf7b77d0556847cea112d7cb6ccc37caf54c07c69c65e7c6664907c1bbc077bf841387bf0b2df7ba3c0797b9910b97b8db51e7b75c3147b2f19917b2b17a17b25fb187b16ea687b00d7ff7ad3415f7a8ef3507a7a23a87a36543c7a260a2f7a01223179e5550479d3e13a79c2eecc79c02f7279bb6d1e797abaaa79717a8d794fbed2792d2bd6792757587915ad7b78e65c2c78d1319678bca812788f9511784337a87800865577d135d077cf974077ae3ab077728e4a7753784a7728326676fcecf676f6d5a476f0de3376d6e321
  | 6, 14 => 0x868f8bfa8679f841867726a18676ba26866977d4865e272f863f7c5985f6241e85f58910857f1b668518ff1e85184ada8452d4418450db8384203dbe83f53a1c83bec71383b00fae83a21eb183804071834e1a45834632f0833df9038323215e82fc24ed82e8729d82e0b6ab82bd697582a1cfc3827963fa827639728257f5cf8220478281ebe28481e62af881bd8a2f81b77d6f81b591e281b49c6081ae339081a42827818f326481086da080e73cd180c16b8180920950806d16b98069eaef806266ad8032d766802889c8800c7ccf800a6df47fd737a37fbcd7ec7fac73bc7f8776eb7f4590c97f1a591a7f0f88c77f01445f7eeb32617ed1cb467ebbf601
  | 6, 15 => 0x8d560f3a8d3157b68d219bf58cfa91f68c8f17858c73f3678c4a4e318c3f36198c353f988bee01d98bcae49b8ba51dad8b830d788b66da5c8b4da15b8b03a0648aee218b8ae257588aba15e18ab84b5d8aafa50e8aaf8d4e8aa42a2f8a82f1838a81f0ca8a4b2c568a2ec80d89f074c389efee9189d1b07b89cdf33589b9a4c589b52b508974814d8945a6a988f300e188ede02888e36b1588dbccf288cd013b88a82a54887d410f884052b7882be4e18826fc3988118a8287edb1a287ec230287e6c54587e4b66087bd68e187b2ceb48787f0328787efba877779c3876dd24987648dca873abea48709807d8703169686e6840f86d3f20a86cb1e0086bb6894
  | 6, 16 => 0x94e227fc94b8834e94adb8bf94aba5ca947da14a94487611941d35b894062d5193f0934d93cd8fe093c2bae393a5976993835e6693602c4692f7889692d649fa92cd700b92cc7f6e92c0ee8f928df7689231308292002a6a91c9a37991c8a36f91b3cbf1919ac8ae917fb21d917b4abf915bff58912821e49102d26a90d48e7390b87dbd906af4ff906837b8905288bf9022657e8ff6aa358fe77d2d8fe7744e8fcd3fb08fc3c7a68f78512d8f74f0a98f6057d08f3acded8f1f96978ec635f58e7f4b558e7b64d08e59ee6c8e52fbf68e48ebd08e323b688e2522c88e1286898e0cfa578e0b555c8df2ab598de04c348d88441d8d6a7b858d5eaaf98d5c0a99
  | 6, 17 => 0x9d413caf9d3bb9e79cf14cd49cbb54e09c9ccc9d9c9c57949c6826aa9c5e325a9c20d3b29c068d939bd769ee9b58bf3b9b4650979b43d0559aa07b839a95b69e9a6ab1be9a21f39f99bed3f99997d904998cf53c998cea0d998829a3997374ef993824c799341bba9933b44398ebd17898e9771598ddc02e98a19efa988a6f269882dab2987e22a49848610497ec88bb97a4f38797a00225979c56d897885ff9977488ac97708ba5976b1da997570162974a939b9736bddf97012b8496b21647968d4d5f968ac1e99689804d9661aced961ed463960bb76c9601231395ddc41b95daf82895c913b395bcff2e95ad999095370e769536a67a9515305d95124759
  | 6, 18 => 0xa4dee153a4be299da4b188daa46ef71ea41794aaa4033c3aa3f2ed10a3e19170a3a56a26a380bc2ca37956e6a3744415a352c6cfa34731dba2efe0c0a2cd8bc3a2b3fd1fa2b35b7ca2a97873a2a6f9a5a2a24eeda256c1a0a23d04efa22b6a16a21ef55aa20297e8a1f16defa188a62da1807b91a171e072a15d9d05a1536890a0b9d488a099d7c2a0732669a06b55ada05f6e2fa0369f44a02ef21ba00c68569fe480b99fa7e8e29f6676b19f665ba79f55b6a39f3584529f22e88e9efaea139ed6de7b9ec9ae489ebfb44d9eb2472c9e9c45c39e64b9f29e10e9b59e0a09409ddfb7989db392919db087499daae7359d86ff729d6c560b9d58b7ee9d42c3eb
  | 6, 19 => 0xac2d59fbabcb65acabc00307abb46943abb3dcc5ab63d8acab37265aaad76587aabfa2cbaabd67a8aa7b50eeaa67fba6aa30b727aa00aaa3a9f3d131a9eed033a97aa236a9789f6da977e211a95dfcd0a92ef1eea90bc50fa909e4c1a8e78fc4a8e4ad46a8d0504ea8c54723a8afe02ea893383aa85f673ea85da819a85b062fa840633ca828f69ba81e26c1a80fa957a7fc18f5a77ba7efa7509ec7a7470e27a732a1a6a71892dba6fdec6ba6e98352a6aa8094a6a209e6a6910249a68098aea66580e8a6563cc3a6547150a643b44ba60a91baa5ff6a18a5d7b751a5d4719da5ae8250a5766eeba56be49ba54a6a95a5480804a5342840a533b563a4e8963e
  | 6, 20 => 0xb511b645b47be621b37c045eb3534b16b2dcefbab2d110c1b2ccfe2db27deebbb27cccb0b2516d61b245d9dab1fe93d5b1fba0bfb169cadfb0d67463b0d5dbb4b0cf1072b0c4ab5eb085e999b08080b4b072d957b047d02fb031a5c8b02513ebb019cfffaff20c80af973c98af47d2e4af22367caf1cc9bcaf1123ebaf057aaeaef69b80aef5af7aaeec8abdaee09f75aed94acbae948155ae8f2a8cae6de29cae6872d8ae66d589ae52400bae32fe10ae1bf85dae18ff3dae1759bbae11518cae110966adfafb7badf1a5e6adeaf2e8adcb950dadbf879fad58a5d0ad3b090dad14af02acb3e394aca9b064ac8ec481ac8a86ebac829a92ac54c35bac41a9b3
  | 6, 21 => 0xbea336b7be97b2cebe907f01be4be64fbe3add0dbdeb6445bde1cfb5bdce499fbd9001abbd7258e7bd47dfdabd199d0fbccd4b3fbc8a8d59bc87e6edbc878e76bc7e8f37bc591900bbcf1011bbb69bf5bba736d9bb4177cfbb184a9abb1464cebaf70c47bae9d770ba951fd0ba779f70ba437f4eba40b91ab9fe2647b9e29b05b9df8830b9c6a5e9b9c08083b99861f2b9748a1eb932cbabb92956c4b91d4ce9b90d8a13b8fd9f81b8ba7db4b8b7e9f7b889a36bb80e6715b7d6b31fb7b92ec7b7a1fd24b79ef288b78864c3b768dbdfb75c39a0b71329c5b6f9cc08b666254db64ecbd7b63701c7b62bd8c0b62922e8b6251136b5e82352b5d41e0cb5a0fe76
  | 6, 22 => 0xc65acfb2c6124ee3c5c67bfbc5899ec0c576ef75c5736c6ac55096e5c541038bc5368674c51b2e6fc518bf53c4b9fc07c4949487c4789a6bc463c956c453a13bc4232d1ac41ed601c40a2416c3d681efc3baf135c398766ec3724ea7c3606443c337f1aac3347db3c3334588c330a8d4c32be95bc31b6fd9c2d89b35c2d0e2fcc2afde01c2a091e1c29352fcc2932210c278c27bc2683a37c1f12b01c1ebf1e0c1dbd993c1d25f49c1a99556c1698805c13f5760c134f450c0cd281cc0ae99dec0a55ccdc095d15ac05fc100c0144dd9c00e671abfb0cba3bfa41077bfa2d939bf98043bbf74ae55bf4172fabeea5a39bee24cdcbecf96e5bec4f692bec0a575
  | 6, 23 => 0xce8ab657ce745571ce7088d0ce540370ce3a426ace37cadcce32531fce0f4162cdf98342cdcc5fdecda95987cda438cecd853652cd3517becd28ef85ccfb6ba3ccc7daa6ccbe85adcca27ba8cc647027cc5be40acc3d2a65cc1d4d7bcc1b72b3cbd5b4f2cbb9f257cb980245cb66226ccb308914cb2d7f47cb2d12cccb09853fcaefe3b0cabb86a9caad7443ca5d1f3fca35eab9c9f2a206c9ee7b2ec9b0660ac996b3b6c92a9c24c90a98fcc8e779a6c8369917c823f470c8205f4fc7f451a9c7ec7312c7d85b91c7d3f23bc7bdffc1c7af1d03c79e0f45c76b6ab0c7554d2ec74dc1ecc7327c7fc72c9218c70c24ecc6e21188c6d0b208c6c817b7c664bad1
  | 6, 24 => 0xd6360ac3d612c66fd607477ad5dffed2d5ce88c2d5bfd6fdd5a0d46dd59ccb60d57db6c6d578611ad53d3f66d52fb620d52b0a13d50bf219d4e47617d4890869d47e7871d46d133fd44fd9dfd42ea9d3d3ca8022d3a84f1fd3a13996d355d4ffd34d4128d317dc6dd3152e0bd2aeea40d2a903ffd29440d5d2849381d26e2c13d242f053d23c352cd2273c28d21f33e1d20d1552d1f2c56dd1efb8f3d1d3f658d1c001f7d1a278a6d1879d90d14c6d48d137f74ed1293c1cd10b22e6d0afe803d0a5ce8bd0418164d028b587d027ba97d010ef66cfdc665acfaaeb5dcf6e5413cf4fba80cf446c2dcf384970cf2fed9ecf1f3ed4cf18dd1fced995d4ceb81e7b
  | 6, 25 => 0xdea3b271de9d2c44de99cc50de86f571de5cb0fbde4eb049de2834c3de23d5bfddd589c4ddb9d253ddaa279ddd8ed5d6dd312984dd2a54f0dd1bb31cdd1a865bdcbac6b9dca2e161dbe6b227dbb7842adbabf10cdb95112edb15c90ddb1540e0dafef9a9daf2339cdac26754dabbb2acdaa10b17da9fdba6d9d792fcd9c29a4fd9bf06ebd9bee8b0d9ae4b1dd99d8f06d96edbf4d942b014d8f65272d8ebb4bad8c00a96d884cac0d883e886d87f9952d84bd8e7d81684ecd7de5cbdd7c94e2dd7c43538d7a472f4d7970f9bd7948ba0d7894d3cd786c099d7783301d76eed8dd7482c02d744500ed733dc2ad6c78025d6bc63dbd6b4c389d673d0cad670e039
  | 6, 26 => 0xe85b8981e82d725ee8047120e7ff3ec4e7eb888ae7e8d4afe7e6faa8e7d72f7ce7b39f5ae7a75556e79f0ae9e6f71c21e636d437e5f130bbe5e14f13e5cc13a1e5b51d7be5a92eafe54c555fe54b61f5e504ee61e4ea6364e4e54ac1e4d154f8e46b0a58e45040b6e41e5447e3ca2ab6e3760cf3e358b1ffe346d5a3e31a7a5ae2ef9098e2e5bc00e2cad771e2b6d2f7e2a6f24ce2783331e277b2dee1fd09cae1f91c91e1808a81e165e754e147418ee12c5e2fe1151f08e1135edae0b2b2ede0a16a4de09738f3e07b344ee0558fe3e02caf5ee026649fe0129c16dfeb09c7dfbe1decdf921631df66edf2df1659addefe0162dee29a6aded5d017debf7146
  | 6, 27 => 0xf0010e1beff44d67eff3c368eff06597efefac9cefbd7900ef8f5b7cef831902ef75fb71ef321432eef3064deebe9aeaeeb70349eea631b0ee5a91beee4697f9ee44aee7ee44a0bcee365bcfee21b801ee1e2c58ee02495bee000531eddc92d2edc03d67ed9de86aed86fa4eed4c8833ed459ef7ed2ae9e7ed215bcfecef841fecee993fecdaea36ec6b46deec362226ec338729ec164c1eec0c1396ec0915fdebf03b1eebcc6fffebc28ee5eb9c6eb4eb94b67beb949f2aeb7fd924eb57e6efeb2c0db6eafba6c3eaf7f023eaf24c7aead3279eeabec0cdeabd810beab31e8aea5d5ff0e9b0c204e96fe5a4e964ad1ae8fb991ee8d96a67e8c040abe88d44c1
  | 6, 28 => 0xf755edc8f74f43f7f74c3499f74120e2f737c7bbf71746d7f6d3c780f6ccb78cf6c722e5f69357a9f6680c4df6535463f652f43ef650f9aaf601a4eef5b7b2e4f59108abf58f108cf58d3b0df58017a1f5664f27f5277aadf51cd756f5192827f503ca7df4dff160f4d8c155f4658084f4583038f4535bf8f43fcaf3f41eb87ef409b81ff3f152c6f3ef218bf3dd72f6f3cea65ff3c06a7bf39bac49f395a0bef38fa371f37e6192f33b5fd0f32a1730f2f9478bf2c41b18f29edce5f2854adff25014fff249a559f23bfa06f1e76b99f195102ff1820790f171c893f16927fef12be4b6f0fa8a62f0f8df95f0b82528f05804caf0556ec8f03d9387f02597d4
  | 6, 29 => 0xff4cb230ff4044e3ff0bb4c4febe0ea5fe3abca4fe3673f0fd9eb53cfd7e6f06fd22ec1ffd1ef844fd058035fcf27d52fcaa882bfc9f7816fc78f6f8fc714592fc686073fc17630bfc151d11fc0c146cfc075989fb6cd77efb4809cbfb449103fb314dddfb2b821dfb237bfffb211cecfb192d73fb07d043faed5a6dfaec6079faea169efaea070ffac23f5dfaba4034fa72f38afa5422b6f9f9d20ff9cab482f9b99d75f9afb2a4f9a7b435f9872d4af9824cb5f96feb04f9098d40f908e400f8f84583f8a016c6f89c6bb5f89a03eff87cadc2f87a4a6af875480ff85b44fef835fac3f7fc1ceff7f3c11df7e6759ef7ae70fdf7a45692f79aba4bf7968602
  | 6, 30 => 0xffec61e4ffa13466ff8b865fff65136aff55b127
  | 7, 0 => 0x1279802811ed84b711eb7ccf11d748061187183a1142fa411134c93410d1aa9610c280c5103ead2a102d8cd30fc22fb60f6b9a140f5c5cfb0edd17080ea68d810e8414b20dfb96ef0df078900db675560d9cbe430cf91d9f0cc7aa850cb3009d0c867e660c2cfbb60bd753a90bb2ffb10b989d440b41c7720acf09dd0ab8b26f0ab7b9ae0a9628be0a2e18720a172c4908aedd460878675807d82e3c07bd347d07af559e076636a7075140fd06b07a0306634425065223ce05c61dd605ad2f34059e8b170590310f05169eb0040745c6036df1500291d00a024a740d023c952e01a603fb0188fb4b018309d901013f3600dd496a0064991500103def0008238d
  | 7, 1 => 0x2438a2592398f31023038dd422daf26b22d85c9a22543c1c21e9d24d21a5f9682179389d204aaf2d2046aaad203e530f203cd04e1fd3d3851f608b651f3d31db1ee4e3db1ebb13731e8eec381e739d441e7359ed1e08e1531d989e101d89743f1d73f5661d29fe0a1c53b96d1bea35011b78d4bc1b70b1901b61a0cd1b52f3321b325a461a5d39541a45ab1d1a2bfa9c1a0ece701a0dc40d19f08aad19e3604919b1d4481979f417191531f41900f42918e3fb0a1881f686183e830517d07b0017a82026175a929b1729918f168a4efe15f86a801581f8c81561a43a1528ba3c1415063f13b5da6d136d10ac131bfefa1317dd2b12b8ab4112ae5da3129997eb
  | 7, 2 => 0x363c57f436224d1b35d89aaa357bcd57355e29ce354bc4fd34cf795334746a9f34744a7f342cdee933193e9a3294bf403264f1943243d5cd3150ae14315024ba31381b073122199e30ccd1eb3055c0a6302a0a262fa1c82a2efbd9642eedfa852ea0b9112d770a592d014b912cf3c0ef2cf085992cae27f22ca821632c9946a22c1543872baacaed2ba0a43a2b0f56702af4104e2a7c85282a6cf0712a5e00e129f1177429f0f1842964176b292df8a1291abe562882e2b2284f0649284db2db2775450f275958f22727707326bb2fef26aa53c3264ea12126488ebe26396ad4262d41fb2609324125bece64258a6ea424cb7b292485a9342468a85e246554a6
  | 7, 3 => 0x45f6b58445c07cca457c5ed145179a8f44d9dfff44cd758b43cee64d43b9f0a3433f660a4305883642b779a342815d8a4223bdb941d622d341a4b5d6413f306a413ca69640db2d8b40d0012440bb2834405c8f3d40455b7a4025ca0a3f9a82dd3f49363a3f086e6d3ee6de3d3e277fff3e1c8eb63dff89d03df1aaf13dc32c533d8620523d6d0b963d18fbc93d0124c93cedcf813cd7d7c23c9f3cdf3c9dc2fe3c9d75a23c8fe41f3c39fd5e3bf3e2703bd0b7833b5624293b3c318a3b23954e3afd7b253a8b1a653a861c993a47663439de879e396f572d3950034038ad846e3899ed1837dd7e803724f45b36f4981f36c744ae36ad51603678c0eb366fa272
  | 7, 4 => 0x5275541c520a3fab51efbb6051e81d5151d2062b51bb2a0f515c2919514f645451007c3a50c9577f50c4b4ed50a706e8505beeb35059633d4f9b055d4f943bc44f8c57c24f624ff44f490be64e79bd534e5bae794e1717654e00c0ea4de27c5e4dd111674dc27b5b4d2b306b4d17706a4d0476064cfd734b4cd8ba054ca60af44c5cc68f4c1e35cd4c173de94bf147df4bb8974e4bb13b214b83735c4b7591cb4b62f61f4b40518f4b180f9b4b02825d4afc5e1e4aee73794ac0774d4a9f53ac4a5928364a0d197449ccf756499b08ca49148db048fa38cc48f889f848b0ac9d484e6acf475141bb472e33c146e1bded46e149a24696c818465e79d546099648
  | 7, 5 => 0x633af011633635116329b29363275f156284e04362623a3561f427ee6129ea2960d1580460c0164560b58bf56001a2b65fd513de5fbac6fd5ec6f1c75ec2fe405ebcebc25e90082e5e22a7545e1657ce5e06e6065debf6475dc82fa15d93d62e5d7bf2db5d2e415c5cde0cce5c9fbd605c91de815bff541c5bdfea355ba915895b4388f85b0171135a437adf5a17fce059f223e559e9c31b59d66aa059d395c75992adb05923c1c658a5f1775837177e5806ebe257c3519856dbe56f56da22f056abec62568ff7f1567ee6cd5640306855f952e755df5df855ab6c46558b875054b47b9853b7a8b55342fdb7531692945314eaf652f2fea452acbe7d528ca242
  | 7, 6 => 0x749b988673f60c3a73e4c23173b9b90973a4532b73a1eeb77341d2fd7333c42e72e03d9b72b283397290cad5727daf3d72739f547268845a71fb25a2714a8ba9711dc56670c4152b707cee8d7005f1236f3b46226eba99336e9f1e276e834bca6e8018a76e38e6f66e34ebde6e1ad9ba6d5cb0976d483b2f6d2657c06cd622c66c4b6e046bcf90f36bc490ee6b89f08a6b7c11ab6b58c0516af785736a5eea176a510b386a4fc62d6a4f22086a2a46cf69f5d2f969d0a4b069b2eaed692e70ee6920920f68b561d0688d1b55683fb3fc67425c616709aa6167044c4c66fb4c91668c47706659a12a6554bad164e30e6464789948638147926379a67663669d95
  | 7, 7 => 0x85e99b5485ba4fb985210b03850f030e84fbb42084a3bdb483d9bb2c83c5bc52838341f4833df90383233d80830766bf82ddd8a582dbd05f828511a482121d0d81b633a581102355806266ad804281917fc0036d7f97da8d7f4590c97f27d8097ebd26667ebbf6017e22428f7dd5c4a57db1e1917dad4e397d776c2f7d33ff317d303bbe7cea112d7c0721267bc86ac17b25f4ae7ae97d0f7ac854af7aa157477a9f7e307a85129f7a2bfc5d7a2bf4367a1482747952d274791d9b417900675a78f04d34781054e377f10ba27770373f7733bc5377211a3f76fcab1e76f0de3376db0b2e76bdf4b9766385db764e5f6175ee73ad7521769374f2245d74e1bd61
  | 7, 8 => 0x9502be1694b8834e9497281e9442b0689409b1f09396353d93602c4692ef453392b08ece928df768928cbda5926d751e9262028d91426eab908ca4449074f28c906d26119037c66b9011f58290061e318fa4cc1f8f7fd14d8f78512d8f6680978e7679718e27eed18e2374cd8e21c9a38dbfa66d8d6fdaea8c8386ea8c1a6ee88bedc1998bed86128b8fda438b7e195e8b3e939c8aef68758ab84b5d8a8bfac78a7994f88a59f30f8a18c2888a0d10dd89f226db89beef4c897643b68958e8bc88f823fd88edfe0d88ede028886bb2a587ec230287cdddd087ca80ca877910e2876dd249872610b887080352869b7594868cb424867726a18635a6fc862851b9
  | 7, 9 => 0xaa21bb6da9cb11c2a98c5b5da9647ee6a95dfcd0a8d69abba80d4bfda77ce252a71939e5a661d0dfa6563cc3a6395456a62fa927a623790ea5e4c2a9a5cabbeaa5103ec2a4dede88a499e38aa36baaf7a302d5f5a2d8fffaa2d855f3a1f16defa1946574a141bf77a0c045e2a0b26703a07b3991a02ef21b9ffd08839f9262399eab30d29de9f1209d42bc1d9c6826aa9c36144f9c27c3cd9bfcd7929b71391a9b34b1219aec1f2b9ab47d5a9a95b69e9a81c9ca9a488f1699d7582f99bbfbc9997d4564996c23f4992721c298fcecee985a34f7984899db981b7e9297012b8496fad25696a4b77d9680ac86967182b5963c456d9603a49895fe78aa95a996be
  | 7, 10 => 0xbcb2dff7bc5e25f5bbec3344bb3f92c0bb04b807bad4da24bab08b31ba477786ba2399e2b97e2118b9782853b85c2f59b84d21e0b837fe7bb81d78f4b7a3f583b7610a65b6edc245b6be7634b69fded2b67d321ab65f3e8fb644e080b63701c7b5c9ec3db5195244b4d0d4a4b47be621b3feb3cab3f8265db32b1ae2b315333eb2dc7687b272f2abb2572353b23cd636b2313513b2306866b22e7c90b210ca3fb12375bdb0ec7e1fb07bc511b04d71d7b031a5c8b02268afb00d02d1af95e2ffaf935789af01b67aaef43dc2aec64c0eaebd223cae064aa9adab993dad85a160ad1a90a7acac34b6ac23afedaabfa2cbaab0e49aaaa935daaa8df529aa38618d
  | 7, 11 => 0xce8cc780cdd2d617cda803e7cc0d7bc5cb9cd379cb26fa2bcae6d7d7ca5eb5a5ca5838f3c9e24337c9d88a90c8df6e8fc8d8951dc876c3bec7ad77bcc7a3ca76c7554d2ec7466283c707ac1ec6ea46f2c6398efac62ad07cc61b5c10c5e58a67c5dca5abc5c226a0c5899ec0c577bfccc52f7576c4eae2e7c4ac2c82c483e9fec4605fcec3fbe96fc3d681efc398766ec3598a1dc34f33b5c31b6fd9c30bd3fac2afde01c278c27bc1c6e06ec1c5a5bec1c16a74c16463c6c150c440c110cb7dc07ccfeebf46884bbef5700abef4bb49bef1afedbeb2f988be4f311bbe2639d5be1fe45dbe107ab6bddd5bacbdd38f62bd5c9ba0bd2744b8bd0683e7bcc8e334
  | 7, 12 => 0xdec49712de2834c3de1b0bb2ddfd151add9de376dd4db3aadd0995b1dc240579dbeeb34ddaf5c757da8008d2da7890dfda52a0c6da0af02ed9ed2281d9eccea3d9e7a089d988b69cd96359b3d90de9d2d8e7dfa1d8cf7726d8c00a96d87f9952d7d8277ed7c2c847d7c0c947d7661623d6fe6644d69e993fd697c1d4d6890d25d64007d5d630e845d62ad27fd5d13c99d58ce416d56748abd4fb6d4fd4f736c8d43f7d82d3b34341d3a21f4ed38eac86d355d4ffd3152e0bd2f3ad55d2da325bd229a3e5d1d3f658d1b38e6dd0e5095fd0ab600ed0a7e5c1d051c79bd0317033d010ef66cf6ea403cf6e15b1cf2fed9ecef7401aceecb93fceeb1ad8cecb96df
  | 7, 13 => 0xf171c893f15a4793f14d1f92f10e5ab3f0f10dbef0c2900ff05fc8f2f053c1fdf03d9387efeaeca8ef0e3eb4eeae7dabee6bbfe2ee570e7dee22ff53ee185818edf5513bede64ad6ed71b5aeecbfbceeeca193e2ec848404eb7a065aeb3fcd10eb0c9569eaf7dac4eabceb59ea782c38ea555bf2ea39f55dea04555ae9f23fa9e9b38944e8b54ab1e8b03ee3e878be20e86f0f45e7a75556e7283c3de7199440e5d4dd4ce5c6ac76e5179d48e49194eae4625a30e45c7de4e4402e8ee3c88b86e32cc12de2f7dbbfe2f02cffe2e453e9e25263cde1c2a466e1283faae0d27efae04a17a1dfeb09c7dfdba1afdfb32b5bdf71e0b2df41afa0dee29a6adede789b
  | 7, 14 => 0xffabe638ffa13466ff8b32caff5a28feff3df527fefc312dfefb8721fef2bd64fed37441fe9afd92fe12eeb4fdf560cffd875a02fd75d7f8fce2758bfcb0a9dbfc7cb7dbfc3e0176fc3cf275fc3650befbefb591fbe5e7c4fb74cedafb113ac2fabc44b5fab495f5faa130d0fa6ea56dfa4dc81bf9b99d75f9acd0faf9824cb5f96feb04f9092d95f9091127f8b72109f8327782f80ff336f7fbcecdf7f3c11df7e68aa8f772bfb1f76d67adf762f14af734b506f725d631f6e94291f646c3bff637ead7f62cba88f5493ef0f5210d0ef50771aef4e7fe6ef39bac49f34c8d5af33b5fd0f2854adff22186e7f1c7ebb4f1c31697f1c1f496
  | 8, 0 => 0xdee29a6add9de376c2afde01bad4da24b6be76349b34b1218ab84b5d8a7994f855df5df84f8c57c22eedfa851e7359ed1729918f1561a43a1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x9945041306
  | 3, 0 => 0x26514104c18994504130646085210c00002044120546085210c011821484300001484148111821484300
  | 4, 0 => 0xc000000000431495310c08c5254c430231495310c04005210520431495310c04004244120600114214800c5254c430100148414810002044120500148414810414544030000114104818c5254c430200000420410000004110600041100809182148430000085210800000004110600000000010000000000000041100808000000000031495310c08005210520446085210c00000004110665109104c0400000c5103
  | 4, 1 => 0x46085210c004145440300001484148100050109202000001044191821484300000c1204814c5254c430100114104818002148420000085210800005210520400081104814001044020200000414410414544030100081104814001048120500141210804c5254c430231495310c080052105204000c120481400154c020400000314410414544030010515100c05182148430010515100c00003504120031495310c0800000c5103
  | 4, 2 => 0x46085210c00c5254c430100000104418005010920200014424808c5254c430131495310c089931041301000852108000000041106000c1204814414544030031495310c08003504120000085210800005210520400000104414184248130200000000000414544030100114214800002044120500140424804005210520410515100c00000004110600000104419182148430031495310c040030441205000c11048140030441205
  | 4, 3 => 0x310515100c051821484300
  | 5, 0 => 0x21040400001091050014841480000001091060000000001c00350412000004110080800000c51030000000001c00000411060000010441800001091060000042440800001091020000041441000450852000000000000000000411010000000000800000000070000000001800000000040008120080000154c020000114104818c5254c43020014121080000254c42020000021040000000000010000040040c00000c0103
  | 5, 1 => 0x8120080000214842000000042440400000000000000043441400505042000000040041000454842000000031440c00104402000014432480800530852020000042441400000411050011410480000000000040000010440400450852000000042440800000c5104464c4104c0400000000070000000000400104402000011410480000001091050000000000c0000108104000050108000045041200000941048000050109201
  | 5, 2 => 0x80052105200000d521080041454403000000000001c0000041106000003144100020441205264c4104c0400204802000000031440c000010d1060011421480000001091010000000001c00000411060000000000800104402010011410480400000000020000000001c00000c51040000000000000454842000000000000400350412000000000000c0000000004000941048000050484200001011048140000105103
  | 5, 3 => 0x14121080000000c51040000030041000254c420231495310c040020480200000c130080400001051040000000000800000000000000042440800450412010001521080000000000030000031440c00000841000011421480000051092020011410481800354842000014042480400000c51030000000000000350852020008521080000104402000001442480800104402010000000000c00000000060000010441800000c0104
  | 5, 4 => 0x800000411050000000000400000c010000000000000000010110516540424c0400450412000000000000000450852000000041440c00250412000000000000c00000000060011531080400000000040000041441000450852000000043441400304c02020000010441400000000000000000001c00000c51030000031441000000000000008120080000214842000000000000800504c4202000000000000000000005
  | 5, 5 => 0xd54208000000105103001152108000000000000000c531080400000000050000000001c00350412000000042440400000000060014841480059501093010009531080400000c01040000042440400314c4202000004244140000000004000c410480400504842000000010440400214842000000000000c00000000050011531080800000000000000030040c00000411060000000001c00204802000004110080400000c5103
  | 5, 6 => 0x800354842000014841481000000000070000000001800304c0201000812008000042441206000004144100000000002001413108080000041106000c130080400504c42020000021040000000c51040000043441800000000050000031440c00504c4201001141048080000000001001151008004145440300001152108000000101105000001044180000000000000000000000000000000001153208000010440200
  | 5, 7 => 0x100000105104000001044180042481202001143248000000000000000001044180000000000000c130080800001081040000000001000001091010000031440c00000000000000000001000000411060000000001c00000000040000031441000001091020011530080000104402020005432480800450412010000041441000104402000004110080000350412000008120080000250412000000000001c00000c5103
  | 5, 8 => 0xc51040000000000000000000060000020441400000000040000000000400000000010000000001800000000020000000001c00000000050008020480000000411060000042441800001091060000000000c000008110500000000008c5254c43010009531080400000411010000010440400000c51040008120080000450852000000000001000454c420200000000000c5254c4302000411008000000109106
  | 5, 9 => 0x109105000d421480800000c510310515100c0000000c51040000021440000500c92000008521080000354842000000000000400000c51040000000000800000000030000041440c41454403000000000000400001011050000000001000104402000004110080000000841000011431480400000000040014c42480400424412060000041441000000c510300000000000004540420000000420410000010d105
  | 5, 10 => 0xc130080800350412000000000001c00000000010000000000c00454c420100085210800000008110100041100804000010d1060011410480800000000000011510080000450412000000000001800214842000011521080000504c42020000000000800510c92020000000000800000c51030000030040c00314c42020000000000400450c12000004110080800000000010008521080000350412000010920480800000c5103
  | 5, 11 => 0x11432480000304c02020000020441400450412020000040040c00450412010000030041000314c42020014131080400000000000000010441800000000010000031441000000411060000010441800104402000000041441000000411010000000000000254c4202000411008080021484200000001044180000000006000d410480000000000000011510080400000000000011410480000000c11050000031440c0000108104
  | 5, 12 => 0x41441000001051030000000000800001051040000031440c00450852000000000001000000000020000043441400000000050009531080400450412020011420480400000000060000000000c00001081040000031440c00155002000011510080000000000020000000000000214412010000000001000104402020008521080000130c52020000041440cc5254c43010008020480000254c42010000000001c0000041105
  | 5, 13 => 0x10441800304c02010004110080800000811010000000000400000c5103000852108000000041106000000000040000000002001412108000000000006000c531080400000000030000041440c000008110560109204c0800000811050000000001800504842000000010441800000000000000000001c005010920100000000000c5254c43010000000000c00000000040008521080000200812000000000001c00254c4201
  | 5, 14 => 0x9530080000000000020000000000000314c42010008120080000000c41020000000001800000c510310515100c000000109101000c130080800521052040000000000800314c420131495310c0800204412050000000001c000000000010515100c0400450412000011410480000000411060011421480000000000020008521080000000000020000000001c0050109201000004144100000081105000004144100015500200
  | 5, 15 => 0x400000c51030000031440c00314c420200000104414000510920231495310c08000000000400114104804000010910500114104808002148420000145230808001044020110515100c0400000000000000010441800450c120165109104c04000010d1050000000001c00350412000011421480000000000000014121080000000000050000010441800314c4202000c53108080000100104
  | 5, 16 => 0x1000511092000009530080000000000000000042440400000411060011510080000250052000000000001c0000000006000c120481400454842000000000001400000000060000000001000000c510310515100c0400051092020004110080400000411050000000000400000c51040000010441800250412000004110080800000000000000010441800000000040000000000800454842000000031441000000c5104
  | 5, 17 => 0x504842000000040041000000411060000030441400450412020000042440800000841000000030441400000411060000031441000000c51040000000000000001091020014121080000000000050000040040c00304c02020009410480000210852000000000000400000411060000030441400000c9103000852108000030441205001092048080000000000000004144100045041202000d41048000045041202
  | 5, 18 => 0x43441400000000010000000000800000411050000010441400001091020008120080000354842000000000001800000000060000000001c00000c510300000000000000004110631495310c0400504c42010008521080000001091020000031440c0045085200000812008000053101200001092048080042481202000004244180000000004000000000180000041101000842148000045041200000001044180035484200
  | 5, 19 => 0x42441800000000040000000000000000000010014042480800001051040000010441800104402000000010441800254c4202000001044180045085200000941048000000000000000411008000050484200000852108000050109201000c120481400000c5103000000000040045041200000d521080000314c42020011410480400204802000000042440800504c4201000812008000000041106000000000100000000006
  | 5, 20 => 0x14c40480000001091030000031440c00051092020000031440c00000000070000021440000304c02010000030441400001091060000000001c000000000231495310c080000000000001412108000000000007000001044180000000007000002044140000000005000852108000000109105000000000140035041200000d421480800000000030009410480000000000010000000001c4145440301000852108000000000000
  | 5, 21 => 0xd4214808000010510400000000010000008110100000404414000010510446085210c00000010d105000001044180000000006000000000000000000001000000000040000000004000d4104800000004110500000104418c5254c43010010920480800000000060014131080800000000060000000001800314c42010011510080000000411060014141080000000000030014131080400154c0200000842148000000000006
  | 5, 22 => 0x424812020000000000000510c92000008521080000001051040000000001400450412000000000000400001091010009531080800000000070009531080800000000070009531080400000000020000000000c00450c1200000144248080000000005
  | 6, 0 => 0xc130080400000000060000000001c00001051030000031440000001091050000000001c00000000040000000000800001091050000031440c00000811010000040440000000000020000003840400000851000000000001000504c4202000003044080000000002000000000180000101105000002144000000000002000000000000000109101000000000100000081100000001004000000000004001404248080000000001
  | 6, 1 => 0x31440c00000000040000000001000000000030000003840800000000030000000000800000000040011531080400000000000011521080000001081000000000001c00000000060000021440000000000000000000001000000000030000010441400001051000000000001800001091020000010441800000000060000000001400000c510300000028400000000a100000000384080000000006000000384080045041200
  | 6, 2 => 0x14000000000300000000010000010d1020000041440c00000411000000023040800000811050000003840800000000050000000001000001011010000000001c00000411060000041440000000000000000000000800000000010000042440400000811010000041440c0000000003001151008040000000000000003144000045440200000004144100000105102000000000100000000006
  | 6, 3 => 0x851000000000000000000000000000000001400000000060000000000800000000030000031440c000000e100000000000100000002100000000000000000000004000000304040000000006000002044080000006100000000000040000041105000001044080000000001000000000100000000006000003144000000000002000000184080000000000000000000080000109102000000000140000000005
  | 6, 4 => 0x43440000000000020000041441000000000050000041441000000811000000032440000000000030000000000c000000a1020000000001c0000000007000c130080800000121000000000000c00000851000000000001800000000030000000001000254c42010000021040000000000060000000840000000041000000010440400000000060000000001000454c420200000414404000000000200000204400000000a100
  | 6, 5 => 0x1400000000040000000000000001051030000010040000314c420200000008408000010510300000000004000000210000000314410000000000400000038400000000a1000000000840800000801000000004840800000021000000010440000000411000000000001c00214842000000002840000000000050000032440800000c81000011521080000000c8100000000184000000000004000000000100000041101
  | 6, 6 => 0x100000081102000003044140000012101000002044080000000000000000184000000000003000000284040000000000000c130080800000000000000000001800000c91000000000000c000004c1010000000000c000000a1010000020441400000000010000000000c00000000050000020440000450412010000030440800000411060000000000c0000000005000004244080000000006000003244000045440200
  | 6, 7 => 0x1000000061000000021040000504c42010000002840400001051030000000000c00000061020000000000000000c11010000000000c00001081000000000000c00000411000000000000800000851020000003840800000000030000000001000000000000000000001800000c51010000020040000000411060000000000800000c51020000000000400000000030000000001c0000000000000000000040000000005
  | 6, 8 => 0x21040000000000030008521080000000021000000000001800504c42010000000001400001001000000000000c00000841000000001840000000000000000001840800000000030000030440400000000040000000000c00000021020000000001400000851000000000000000000000060000000001400001091020000000001000000000040000000001000000c51040000021040000000801000000000000c0000000001
  | 6, 9 => 0x41100800000000e1020000042440400000c910200000000000000010910500000000004000010d1040000031440c00000811050000000840400000c510300000000014000000000500000434408000000000600000000008000000000300094104800000000e10000000000004000000a100000000000140000041102000004344140000000006000000000180010440200000000000080000081100000000084000000000002
  | 6, 10 => 0x41100808000000a1000014121080000000000030000031440c00314c42010000021440000000000000000000000c0000000001000003144100000081102000000000000000000001000000000100000000003000000084000000040100000004204100000084100000003004100000000007000002044000000000001000000184040000081101000002044040000000006000001044000000002100000003004040000000006
  | 6, 11 => 0x10000031440800000000000000020440400000c9101000000000140000000005000004244140000000003000001044000000040100000c130080400000841000000000000000000851020011510080400000411020000000001400000c51030000010440000000000040000001840000000061020000000001800424812020000000001000000000040000000000c0000109100001153108040000000001
  | 6, 12 => 0x400000000008000000e1000000000000800000c91020000021440000001091010000042441400001091000000020040000000411020000000000c00000021010000000000c00414412010000002840000000000030000000000800104402010000020440800001051030000040441400000811020000041440c0000085102000004244140000000002000000084000000002101000002144000000006101
  | 6, 13 => 0x9531080400000000030000021440400000c510400000000010000000a1000011521080000001091010000030440400000811020000010440800000000060000042440400001091010000031440400001051040000000000800001091010000000001c00000c11050000000001800000021010000003040800000000030000010040400001001000000000001800000c91010000000001c0000000002000c13008040000000003
  | 6, 14 => 0x9531080800000000060000040440800000401010000000000800000000010000031440800000000060000031440c00000411020000000000000001051000010920480800000411060000000840800000411010000000840800454402000000002840000000000060000000001400001011000000003840400000000030000000000c005210520000000204414000004c1020000000001c0000000006000000084040000109100
  | 6, 15 => 0x104400000000e1010000000001000000000000000041441000000c410200000424408000000000100000424404000000e1010000000001000000000020000000000c00000000020000000000800001011000000010440000000000060000042441800000000020000021440400000000060000042440800000000050000000001800304c02010000000001000000000010000000000000000c5101000000184000000108100
  | 6, 16 => 0xc00001011000000031440c00000000020000020441400001091020000020440800001051040000031440000000121000000000000c00000c510300000210400000000000500000000010000000c10200085210800000000000500000000018000010010000000000000000000000400000028400000000000300000000010000000000600000000000000000e10100000038408000000e102000000000080010440202
  | 6, 17 => 0x4244080000000003000c531080800001091020000000001000001091050000000001800000411020000000001c00304c02020000000000c000008510000085210800000000e10200041100808000000000400000424408000000000500000018408000000610200000000014000000000000000304404000000000000000048400000010510000000000008000000000200000018404000000e101000001044080021484200
  | 6, 18 => 0x30440000000c0102000000000000000081100000000000080000109105000d521080000000061020000010440400000021000000000000000001091050000043040800000000040000000000800000000000000000001000001051000000000001000000000020000000000c00000811000000000001c00000000070000010441400000000040000000001000001091020000031440c0000109101000003144000000000003
  | 6, 19 => 0x304400000010510300000404408000000e10000000000004000010d1000000041440c00000061010000000000800000000000000032440400000411060000001840000314c420100000404404000000000400000008400004248120200000104408000008410000000000000000000000100115310804000000a100000000000000000000005000411008040000105104000001044000000084100000000000100000085100
  | 6, 20 => 0x800504c420100000424414000004110100000424408005048420000000000000000000000100000000010000000000300000000010000000000700000204400000000000600000414410000000000600000104400000008110100000000004000000a1000000002840000000411060000000000c000000000300000000008000000000400000038400000000a1000000000000400254c4202000000000180000105102
  | 6, 21 => 0x4000010d1050000000000c000000000700000000010000000000000000000014000010510000000000010000000000600000104414000000610000000310408000010910100000310408000000e1000000000001c00000000040011410480800000c51030000042440000001091050000000000400000c4101000000000140000105101000004344000000000004000000000000000000000000000000080000000004
  | 6, 22 => 0x400254c42020000000840000000000030000002840800000000010000000000400000411020011510080000000411020000000000800000841000000000000800001091010000000001400000401000000000001800104402000000000000c00000000050000010441800000411010000000000c00000c1101000001304040000109105000002144000000000004000004244040000081105000000000040000000001
  | 6, 23 => 0xc00000c81000000041441000000c11020000020441400001051010000001840000000000030000000000c000000000000000000010000010910600000000010000004110100000048408000000000200000000010000008010000000000014000000e100000000000000000105102000c5310808000010d1010000031440c00000121010000042441800000000020000042440800000c4102000002004000000000005
  | 6, 24 => 0x800000000020000000000800304c02010000031441000204802000000003840000001011050004110080400000c910200141210800000008510000000000010000000e1020000000840000001091060000000000400000000060000000001400000000040000010040000000000040000030040000000411020000000000400001091010000004840400354842000000040440000000801000000000000c0000000000
  | 6, 25 => 0x214408000000000200000000000000001210000000314408003504120000000000010000000000300000424404000000000000000404404000000a1020000000000800000000040000000001000000000030000031441000000000060000030040400000411020000000000c000010510000000204400000001210000000204400000000000200000038408000000000500000314400000000a100000000184000000000000
  | 6, 26 => 0x800000000000000000000c00000121000000000000000104402010000040040c00000000040000020440400000000030000010440800000000010000041440c00000000010000001840800000c01010000030440800000000030000010440000000841000000001840000000851000000020440000000000020008120080000000c51000000000000c000000000100000000004000000a102000000084000000012102
  | 6, 27 => 0x1c0000081101000004244180000109105000000000100000085100000000000140000000004000000000040000000006000000384080000000004000000000180000085100000001004000000000005000003144100010440200000d521080000000000020000000840000000000020000000000c0000000005000000000040000000005000000000080000000004000000000000000000000000001044140000105101
  | 6, 28 => 0x42440400424812020000000000c000000e1020000042440400000000060000000001400000000000000042441400000c5103000003044040000000001000c410480400000c51030000031440c000000e1000000000001000001091020000000000000000000060000000000400000c51030000000840800000061000000000001c00000000000000032440800000c91020000000840000000000060000043440000000c5102
  | 6, 29 => 0x1400454c42020000000000c00000411060000000001400001091020000000000c000000a1010000042441400000000040000000000c00000000000000000001400424412010000002840000000000040000041440c000010510300000000000000000a10000000320400000010c1010000000000c0000000005000004244180000000002000000000000000000002000003044040000081100000002104000000000006
  | 6, 30 => 0xc00000000030014131080400000061000000000000c00000811000000000000400000000040000003840800000411060000000001800000000020000041440800000851020000000000000000000020000000000800000000060000041040000000021010000000001400000c510200000018408000000000000095310804000000000100000410400000000000700000314408000000e100000004204000000000000
  | 6, 31 => 0x31440c00000401000000000001400000401000000002840400000c11000000000000800000000070000042440800350852020000000001800454842000000000001400000000030000000000c00001091060000000000400000c11010000000001800000000010000003840400000c51040000043441400000411020000001840000000c9100000000000100000041101000000000100000041102000004244040000000004
  | 6, 32 => 0x20040000000000050000000001c00000c51040000001840400000000020000000000400000000070000000000c00454842000000000000c000008010000000000014000000e1010000000000c00000000010010920480800000851000000000840000314c420100000230408000000000200000214404004544020000000008408000000a10200000104400000000a1020000000000000000c91020000001840400504c4202
  | 6, 33 => 0x424418000000000300000000008000000a1020000000000800000000040000003840400000401020000000001000000c810000000314410000004110200000314410000000000000000304408000010d1020000041441000000c11020000023040400000c11000011510080000000021000000000001800000000040000041441000000000030000042040000000c1101000000000000000000007000000284000000000000
  | 6, 34 => 0x800000841000000000001000000411020000000000400000021000000042440800000121020000001840000000851000000040441400000c51030000042040000000000040000000000000001051040000000001000000411010000003840400000851020000000840000000000040000020440000000000030000000001000000811010000041441000000000070014121080000000c5102000001044040000105104
  | 6, 35 => 0x1c00000000000000020440400000000000000021040000000000050000004840000001091050000000001400454c420200000304400000000000000000424414000000000700000304404000000e1000000042440800000000010000000000800000c1102000000000080000081100000000284000000006101000000000180000000002000c53108080053109201000000000000000109105000000000040000080100
  | 6, 36 => 0x800000000040000000001000000000040000000000000000000040000001840000000061010000042441800000000040000032440400000411060000041440c0000000001000c130080800000061000000000001000000851000000000001000001091000000031440c00254c42020000031440c00000021000000000001400000000030000000001c00000000050000031440c0000000007000003144040000000006
  | 6, 37 => 0x800000000070000020440800000000060000000001c00000401000000042440800354842000000031040400414412010000042440400000021000000042440800000000040000020040000000051000000000001000000000050004110080400000000060000041441000000000020014c4148040000000003000001044040000000005000003044000000006102000001044000000105103000000184080000084100
  | 6, 38 => 0x61020000000840800000c81000000000001400000c91020000032440800000000070000031440400001051040008120080000000000050000042440400000000010000000000000000811000000010441800000000000000042441800424812020000000000000000c91010000000000400504c420200095310804000000000200000324400000010c101000000000180000000000000002144000000000006
  | 6, 39 => 0x41441000000000040000042440400000000040000041040000000000040000020440000000c5104000004344040000101102000000000040000000005000003244000000000006000004344080000002102000000484000000000006000000000040000000004000000000000000000007000002004000000041100000000000180000109106000003144040000041101000000000100000000001000002144040000000003
  | 6, 40 => 0x21440400000401000000000001c00000000020000000001400000000040000000001c00504c42010000000001000000c41000000030441400000000010000032440800000021020000010040800000000000000000000000000000050000000000c00000000000000031440400001051000000000001000000411010000010440400000811050000000000c00000000050000000000800000c5103000000000040000000001
  | 6, 41 => 0x1840000000000030000000000c00000000010000000000c000010d1010000010441800000841000000000000c00000851000000000000400000000000000000001800504c42020000000001800000000030000004840400000000050000042440400000411050000021440800000851020000000000000504842000000020440400000411000000000000c00000c51020000042440800000c5102000000000080000109105
  | 6, 42 => 0x14000000a1000000000001400000000000000000001400000000030000003840400000000030000040440800001091020000042440800000000000000000001800000000010000000000400000000040000000000000000000040000010440000000000060000043440400000851020000030440800000000040000000001000000000040000043040400254c42020000000001000000c510200000424404000000e102
  | 6, 43 => 0xe1000000000000000000021020008120080000000000040000000000000000000050000000001400001091020000030040800000000040000000000400001051030000000001800000811000000040041000000000060000020440800000811000000000840000000000040000043040800000000070000000001800000000040000020440400000c51040000013040800000000000000000000c0000000003
  | 6, 44 => 0xc11000000000000000000000060000000001000000000060000000001800204802000000000000c00000c51040000042440000000c11020000000001000000000050000000001400000021000000000001c0000000006000c531080800454c4202000004204000000040100000000000040000041101000004044040000000001000000000100000000004000000000000035484200000002044000000000006
  | 6, 45 => 0x1c00000000010000042441400000000030000010440000000021000000000001800000000020000000840800000121000000041441000000851020000000000800000000010000000001c00000000040000040440400000000070000000001400000000000000000001400000000010000000001800000811010000020040000000000000000000000000304c0202000c53108040000000003000004144100000085100
  | 6, 46 => 0x41440400000000040000000001c00000000000000000000000000000040011531080400000811010000010440000000000000000030440000000000070000002840000000000030000000001800001051030000001840000000000010000000000400000000030000020441400000000040000000001400000c5100000004244080000000005000002104000000000001000002044040045440201000000000140000105101
  | 6, 47 => 0x1000000c91030000040440000000000010000042440800000c110100000430408000010910500000000018000000000100000018400000010510300000000018000008110100000000010000000a10000000008404000000e1020000000000800450c52010011510080400000000010000000001000000411010000002840000001011000000030040800000c5104000000000040000105104000001044180000000001
  | 6, 48 => 0x31441000000000060000000000800001091030000000000800000000000000002840000001011000000000000800000000010000002840400000000060000000001400000000010008510480400000000020000000001400454c42010000000000000000000010000000001000000c51040000002840000000000010014042480400000811000000001840000000000000000000000c0000000003000000000000000000006
  | 6, 49 => 0x420400000000a1010000000000400000000060000000000c00000000030000000001800000000020000021440000000811050000041440000000851010000020040000000000010000000000800000000030000042441800000000050000003840400001051030000010440800214842000000010440800000c91000000000000800000021010000000000c00454402010000010440000000000030000000000c0000006100
  | 6, 50 => 0x40440800000121010000010441800000000070000041440c00501092010000000001000000c01000000004840000000000060000032040000000801000000000001000000000000000030441400000000050000000001c00001091020000000001400000000040000043441400000000040000000000c00000000000000000001c00000c11000000000001800254c4201000000000000000081100000003044040000000002
  | 6, 51 => 0x1800000000050000000000c00000000020000000001000000841000000004840000001091020000001840000000c51020000000001400000000000000000000800000000030000043040400254c42010000010441400000411060000000000400000000000000041440c000008010000000000004000008510000000304404000000000600000000000000000e10200041100800000000e101000000284000000006101
  | 6, 52 => 0xc0000000001000000000080000000007000000000180000000007000000000180000000002000000000180000000004000000000180000041102000002104000000002100000003044080000000005000003204000000085100000002144000000000005000004244180000000002000000184040000000000000000000000000000005000000000140000000003000000000140000000002000001044000000000002
  | 6, 53 => 0x1091000000031440000001091020000000001400504842000000000001c00000000000000003040400000411010000010440400000000020000010440000000841000000000001800000000010000030441400000c01020000020440000000811000000001840400001091060000001840000000000000000000840000001011050000000000c00504842000000041441000000000040000000001c0000000006
  | 6, 54 => 0x42440400000000060000004840000001091060000030040c000000a1000000000001400000411010000000001000000c51030000000001000000c51040000021440000000000060000031040000000000030000042441800000411000000032440400001091050000000001400000411020000000001000000801000000000001000504c4202000002044000000000003000000000100000000005000000000140000000007
  | 6, 55 => 0xc130080400001051020000000001c00000841000000031440c00000000050000000001000000c91010000042441400314c42010000003840400000000050000000001800000000070000000000400000c51030000021040000000021000000000001800000c01000000000001c00000000030000000001000000c5104000002004000000041100000000000000000000000000003104040000000004000003244000000000007
  | 6, 56 => 0x1400000c51040000021440400000061000000000001400000000030000003840400000c41010000042441400000c11050000032440000000000000000031441000000c51010000002840000000121000000010440400000000030000042440400531092010000000001800454842000000000000c00000411010000000001400504c42010000000001800000c5103000004244000000000005000000000000000002101
  | 6, 57 => 0x1000000c51010000000001000000000000000000001c00000000030004110080800000021000000042440400354842000000031440c000000610000114104804000000000400000000018000000210100081200800001044020000000000010000000000200000424408000000000300000424400000000000400000000008000000000200000000008000010d1050000000001800000000010000031440c00000c1101
  | 6, 58 => 0x1000001091020000000001c00000000010000000840000000000070000010440400000411000000000000c002048020000000000010000010510300000130408000000000200114214800000000a1000000000000000000411010000000001400000000050000000001000000851010014042480800454c4202000000000040000006100000000000000000000004000000384080000000001000000000100000000004
  | 6, 59 => 0x1800000000070000021440000000000000000000000c00000000000000000000400000000050000000000000001011000000000000000000c510300000000010000000000700000028408000010d1010000000001000001091010000000001000314c42010000043440800000411000000010441800000411010000000000000000121020008521080000000c41000000000000c000000e101000004144100000000004
  | 6, 60 => 0x1000003044080000000002000003044140000012102
  | 7, 0 => 0x31040400000000020000042440400000000060000000000000000411020000000001800000000040000001840800000000000000000000400000411000000000000400000000040000000001000000121010000020440400000000010000000000000000000050000031040800000411000000000001c000000e102000002104000000000002000000000100000000001000000000040000000000000000000040000000005
  | 7, 1 => 0x32440800000000060000020440400000021000000000000c00000000000000000000000001091000000000001800000000010000000001000000411010000000001400001011020000043440400000000010000000000000000000050000000000800000000070000000000000000801000000000001000001091000000001840800000c91000000042440400000000010000000000000000061000000000000c0000000005
  | 7, 2 => 0x310408000000000100000314408000000000000000404408000000000500000038404000010d1010000002840000001011000000010040800000851000000000000800000000050000020440400000401000000000001400000000040000000000800000000060000000000400000000060000000000000000000060000000000c00000000030000000000400000021020000000000c0000000002000000000000000000002
  | 7, 3 => 0x4000000000200000314400000000e101000000000100000000000000003044000000002101000000000180000000004000004144000000000001000001044080000000001000000000080000000000000003144000000000002000000384080000109102000000000040000000005000004044000000000006000000000040000000006000000000000000000000000000000100000085102000000000040000002101
  | 7, 4 => 0x4000000000500000214400000000000600000000014000000000400000028400000000000200000000004000000000600000000000000000e1010000000001000000c010100000424408000000610100000000000000000000400000104408000000000300000404404000000000000000000010000000a100000000000080000000004000000000100000006101000004144080000000006000000000140000105100
  | 7, 5 => 0x304408000000000300000000008000000000100000000014000000000300000000014000008110000000200400000001210200000000008000000000200000038400000000000500000000000000000a10200000000018000000000300000434400000008110000000000000000000000300000000010000000000200000018404000010510100000000004000000000100000000008000010d1000000000001800000c0102
  | 7, 6 => 0x30440400000411000000000000400000000010000000001400000c11000000000000400000000040000000000000001051020000021440400000000020000031040400000000060000000000400000000040000032440000000000000000004840400000121000000000000400000000050000000000c0000000000000000284040000109101000000000080000000005000000000000000000004000000000080000000000
  | 7, 7 => 0x3840400000000030000000840000000000010000000000000000061020000000000000000000010000000000400000061000000000000000001091020000031040400000021000000000000000000000050000000000000000411010000000001400001051020000001840800000000060000000001800000411010000000000c0000000003000000184000000000002000004044080000000004000000000080000000000
  | 7, 8 => 0x424408000000000000000018404000001210200000324400000008010000000000008000004010000000008408000000000200000000000000001210000000434404000000000200000324408000000000000000000008000000e1020000000000000000021000000002840800000121010000000000000000000030000000000c0000000003000001044040000000002000000000140000109101000000000080000006100
  | 7, 9 => 0x400000c910100000000000000000a10000000000004000000000200000100408000010d1010000000001c00000000050000021440000000c0102000000000100000000001000000084040000040100000000000040000080100000000000180000000003000000000140000000004000003044080000000002000000000000000000000000000000080000081101000003104080000000004000000000000000085100
  | 7, 10 => 0x1400000851010000000000800000000000000000000800000000030000031440400000000020000000000800000000040000010040400000000050000000001000001011010000000001000000000010000000001800000000050000000840400000021000000000000000000000010000000001000000c11020000000000c00000851020000010440400000401020000000001000000000060000000840400000c5102
  | 7, 11 => 0x184000000000003000004244040000002102000003244080000000004000000000040000002102000004344080000000002000000000140000000002000000000140000000001000000000180000000001000000000000000105101000000000040000101101000000384040000000004000000284000000000000000000000000000000001000000000000000000004000000184080000000004000000000080000000000
  | 7, 12 => 0xc000000000100000000004000000000400000214408000010d10200000000004000000000400000314408000000a100000000000140000000002000000000100000000000000000284040000000004000001004080000000000000000000040000000003000000000040000000001000000000180000002100000000484040000000002000000000140000105101000000000000000000001000000184040000000000
  | 7, 13 => 0x30440000000061000000000000800000000020000000000800000000030000000000c00000c910000000000018000000000600000000000000001210000000000008000000000100000000014000000000100000000004000010110100000304400000000a10100000000018000000000400000304404000000a10000000000014000000000300000424408000000e10200000000004000000000000000000008000000a100
  | 7, 14 => 0x1840400000000030000010440400000411000000000000400000000060000042440800000000040000000001800000000020000000001800000000000000000001800000000060000020440400000000000000000001000001091020000000001400000000060000010040400000000010000031040400000000030000000000c0000084100000004044080000000000000000000180000000000000003044040000000000
  | 7, 15 => 0x42440000000000050000000000c00000000000000000001800001091020000000001400000021010000001840400000000030000032440400000801000000000001800000000000000000840400000000010000000001800000000050000000001000000000030000000000c00000000020000000000000000000030000000000000000000060000000001000000c1101000000000180000000001000003004040000081102
  | 7, 16 => 0x1000000000010000000001000000000000000020440800000c510100000000004000000000400000000000000000000500000008404000000e1010000000001400000401010000032440400000000050000000000c00000c01020000000000c00000000020000000000800000c51000000000001c000008410000000000000000008010000000000000000000210200000000008000000000400000000000000010d101
  | 7, 17 => 0xc00000000030000000001800001091010000000001800000061020000000000000001011010000040440000000000050000042440800000851010000000000000000c51010000043440000000000000000000000000000c01010000010040400000000040000000001800000061010000000000c000010d1020000000840000001011020000003840800000c9100000000000180000000002000001044000000085101
  | 7, 18 => 0x10040000000000020000004840000001091020000000001c00000000050000000000c00000061000000000000000000061000000000001800001091010000041440000000000000000000000800001051010000041440000000000000000000000c00000000050000000000400000000020000031440000000000000000000001400001091000000000000000000000060000000000800000000030000002840000000c1100
  | 7, 19 => 0x1000000c11010000020440000000021000000000001000000c510000000104404000000e10000000310408000000e10200000000000000000000000000000018000000000100000434400000000000300000000000000000a1010000002840000001011000000031040400000000060000000001400000000010000000000000000811020000000001c00000c0102000000284000000000004000000000000000109101
  | 7, 20 => 0x811000000000001800000000050000003840800000000000000043440400000000010000000000c000000a1000000000000000000000020000000000000000000020000000000800000000050000000000400000851020000021040000000000010000000001000000000040000003840400000000010000000000c000000e101000001044080000000005000000000080000002102000000000100000105100
  | 7, 21 => 0xc000000000000000000004000000e1000000000000000000000020000000000c000008110000000324408000000000100000000010000000610100000000010000000e10000000018400000000610200000000004000000000200000000004000010d1000000000001800000061000000000000800000000040000000001400000000010000000000c0000000003000001044000000000001000000000040000000002
  | 7, 22 => 0x400000000000000000000000000000010000000000400000c51020000000000c000000000200000000000000000000400000324400000000000300000000004000000000600000300404000001210000000000000000000000200000404404000000000100000008404000000210000000324404000000e1020000042440000000000000000000000c0000000005000000000040000000003000000000040000000001
  | 7, 23 => 0x1400000000040000000001400000000020000000001400000c41020000040440000000000020000000000000000841000000000000800000000020000001840000001051020000043440800000c01010000000001400000851010000000000000000000070000000000000000000050000031440400000c91000000021440000001051010000000000c0000000001000000484000000040101000001004000000000004
  | 7, 24 => 0x800000000020000000000c00000c110100000000010000004010000000028408000000000500000424400000000000600000000000000000000300000000014000000000300000000014000000000200000000004000000000600000414400000000a1010000042440400000061010000031440000000411020000000001000001091010000000840000000000000000000000400000411000000000000c0000000000
  | 7, 25 => 0x38404000000000200000434400000000000000000000000000000000300000008400000000000300000300408000000000000000000014000000e102000000000080000000006000000000000000000000000003044080000081102000000084000000109100000000000040000000000000000000180000000003000000484080000000000000000000000000000000000004244040000000002000002144000000000007
  | 7, 26 => 0x304400000000000300000028400000000610200000000004000000000500000008404000000000200000404400000000000400000038404000000a1000000001840400000000000000031040400000000000000040440000000000020000000840800000000000000000000800000811000000000840000000811010000000001400000000000000000000c000000e100000004344080000000002000000000080000000003
  | 7, 27 => 0xc000000000300000204408000010510100000100404000000e1010000032440400000061000000000000000000061020000000840800000000030000032440800000000010000001840000000000000000000000800000000020000000001400000000000000041440000001051020000001840800000c510000000000000000000210100000000014000000e102000003244040000002101000000184000000000001
  | 7, 28 => 0x600000000008000000a10200000434400000000210200000000004000000000300000000004000000000000000000004000010510100000000000000008510200000018404000000000100000008400000000000000000314408000000000500000000014000000000000000100408000000000000000000014000008510100000000004000000000200000314404000000000500000000014000000e101
  | 7, 29 => 0x400000000060000000000800000121010000000000000000000050000031440400000841000000000000000000000050000021440000000c11020000021040000000000010000010040000000811000000030040400000801000000000000c00000000040000000001800000121020000042440400000000060000000000800000021020000003840000000c1100000000000080000000003
  | 8, 0 => 0x2000000000000000000000000000000080000000001000000000000000000001000000000000000000001000000000040000000002000000000040000000002000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 7 s ws hint
  | 1 => checkCutEntry dom_7 roots_7 7 s ws hint
  | 2 => checkCutEntry dom_12 roots_12 7 s ws hint
  | 3 => checkCutEntry dom_13 roots_13 6 s ws hint
  | 4 => checkCutEntry dom_14 roots_14 6 s ws hint
  | 5 => checkCutEntry dom_16 roots_16 6 s ws hint
  | 6 => checkCutEntry dom_18 roots_18 6 s ws hint
  | 7 => checkCutEntry dom_19 roots_19 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_20 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
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
theorem z4_48 : ∀ i, 48 ≤ i → i < 56 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_56 : ∀ i, 56 ≤ i → i < 64 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_64 : ∀ i, 64 ≤ i → i < 71 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 64 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 71 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (range_split z4_48 (range_split z4_56 (z4_64))))))))
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
theorem z5_240 : ∀ i, 240 ≤ i → i < 244 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 240 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 244 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (range_split z5_200 (range_split z5_208 (range_split z5_216 (range_split z5_224 (range_split z5_232 (z5_240))))))))))))))))))))))))))))))
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
theorem z6_608 : ∀ i, 608 ≤ i → i < 615 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 608 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 615 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (range_split z6_376 (range_split z6_384 (range_split z6_392 (range_split z6_400 (range_split z6_408 (range_split z6_416 (range_split z6_424 (range_split z6_432 (range_split z6_440 (range_split z6_448 (range_split z6_456 (range_split z6_464 (range_split z6_472 (range_split z6_480 (range_split z6_488 (range_split z6_496 (range_split z6_504 (range_split z6_512 (range_split z6_520 (range_split z6_528 (range_split z6_536 (range_split z6_544 (range_split z6_552 (range_split z6_560 (range_split z6_568 (range_split z6_576 (range_split z6_584 (range_split z6_592 (range_split z6_600 (z6_608))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z7_416 : ∀ i, 416 ≤ i → i < 419 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 416 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 419 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (range_split z7_208 (range_split z7_216 (range_split z7_224 (range_split z7_232 (range_split z7_240 (range_split z7_248 (range_split z7_256 (range_split z7_264 (range_split z7_272 (range_split z7_280 (range_split z7_288 (range_split z7_296 (range_split z7_304 (range_split z7_312 (range_split z7_320 (range_split z7_328 (range_split z7_336 (range_split z7_344 (range_split z7_352 (range_split z7_360 (range_split z7_368 (range_split z7_376 (range_split z7_384 (range_split z7_392 (range_split z7_400 (range_split z7_408 (z7_416))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z8_24 : ∀ i, 24 ≤ i → i < 30 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 24 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 30 → Z 8 i = true := range_split z8_0 (range_split z8_8 (range_split z8_16 (z8_24)))
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

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276813024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_20.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_20 10 hT6 (by unfold IsConst; decide) low_20

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [7, 2]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.and, [9, 3]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [11, 5]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [14, 10]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_13135_aux

theorem PEqualNP.Outside.L_meta_13135 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276813024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4276813024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_13135_aux.wit, PEqualNP.Outside.L_meta_13135_aux.wmono, le_trans PEqualNP.Outside.L_meta_13135_aux.wsize (PEqualNP.Outside.L_meta_13135_aux.lower s hs), PEqualNP.Outside.L_meta_13135_aux.weval⟩
