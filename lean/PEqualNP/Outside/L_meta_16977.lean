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

namespace PEqualNP.Outside.L_meta_16977_aux

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

def dom_0 : Nat := 0x404040404040404
def goal_0 : Nat := 0x404040004000000
def roots_0 : List Nat := [0x400040004000400, 0x404000004040000, 0x404040400000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(10, 26), (10, 42), (18, 26), (18, 50), (34, 42), (34, 50)]
def r1sG : List Nat := [10, 10, 18, 18, 34, 34]
def r2sG : List Nat := [26, 42, 26, 50, 42, 50]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x8ca6dfa5
  | 3, 0 => 0x8ca6dfa5
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x40404040000000004040000040400000400040004000400
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

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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

def dom_1 : Nat := 0x4444444444444444
def goal_1 : Nat := 0x4444444044404040
def roots_1 : List Nat := [0x4040404040404040, 0x4400440044004400, 0x4444000044440000, 0x4444444400000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x4040404040404040, 2, 6)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0x505050505050505
def goal_2 : Nat := 0x404040004000000
def roots_2 : List Nat := [0x404040404040404, 0x500050005000500, 0x505000005050000, 0x505050500000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x404040404040404, 24, 26)] (by decide +kernel) (by decide +kernel) low_0

def dom_3 : Nat := 0x555500000000
def goal_3 : Nat := 0x544000000000
def roots_3 : List Nat := [0x444400000000, 0x505000000000, 0x550000000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 4 :=
  lower_iso [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_4 : Nat := 0x5555555500000000
def goal_4 : Nat := 0x5444544000000000
def roots_4 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 34, 50)] (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0x55550000
def goal_5 : Nat := 0x54400000
def roots_5 : List Nat := [0x44440000, 0x50500000, 0x55000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 4 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3

def dom_6 : Nat := 0x55555555
def goal_6 : Nat := 0x54405040
def roots_6 : List Nat := [0x44444444, 0x50505050, 0x55005500, 0x55550000]

theorem low_6 : Lower dom_6 roots_6 goal_6 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x55550000, 10, 26)] (by decide +kernel) (by decide +kernel) low_5

def dom_7 : Nat := 0x555500005555
def goal_7 : Nat := 0x544000005040
def roots_7 : List Nat := [0x444400004444, 0x505000005050, 0x550000005500, 0x555500000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 5 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_8 : Nat := 0x5555000055550000
def goal_8 : Nat := 0x5444000054400000
def roots_8 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 5 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_9 : Nat := 0x5555555555555555
def goal_9 : Nat := 0x5444544054405040
def roots_9 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

namespace S_9
def pairsG : List (Nat × Nat) := [(2, 6), (4, 6), (4, 12), (8, 12), (10, 14), (10, 26), (10, 42), (18, 22), (18, 26), (18, 50), (20, 22), (20, 28), (24, 26), (24, 28), (34, 38), (34, 42), (34, 50), (36, 38), (36, 44), (40, 42), (40, 44), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 4, 4, 8, 10, 10, 10, 18, 18, 18, 20, 20, 24, 24, 34, 34, 34, 36, 36, 40, 40, 48, 52, 52, 56, 56]
def r2sG : List Nat := [6, 6, 12, 12, 14, 26, 42, 22, 26, 50, 22, 28, 26, 28, 38, 42, 50, 38, 44, 42, 44, 50, 54, 60, 58, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_9.map (· &&& dom_9)
def goalM : Nat := goal_9 &&& dom_9
def NN : Nat → Nat
  | 5 => 15
  | 6 => 10
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xe77511a6d11bbdccb197e02ea8a49cec8920bf4e7f1654644d896a013fd9525d26c253012278734a1cbfaf881901fc09186b1a11174662b60925d246
  | 6, 0 => 0xdeee3556c894e17cb197e02eabf0fefda91103de929bbc978920bf4e45028db10ebf8666009ef5f6
  | 7, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x11551155115511551111111111111111050505050505050500550055005500550044004400440044000500050005000500005555000055550000000055555555
  | 0, 1 => 0x55550000555500005550555055505550550055005500550050555055505550555050505050505050444444444444444444444444000000004400440044004400
  | 0, 2 => 0x555555555050505055555555000000005555505055555050
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x117acc4503d6a4914117ad4457b56a491a2f6ad44603daa2814117a8a458bdab51da2f6b16a68c1ab511a2f6ad43603dab30162f6ad4260456a2054127ad445
  | 6, 0, 0 => 0x45ed59940f6ad495045eb51162f6ad486045ed5a962f7356a68bdab5118117b5455045ab5054127b56a5
  | 7, 0, 0 => 0x117b56a5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffffe3ffe3c0ece7cfe4e7cf870070e0421c38107f01fc003fff
  | 0, 1 => 0xf80fe03de3c7ec60c1e0e7cf87318301801c3f10070000000070
  | 0, 2 => 0x3ffcc06fff0003e63f86
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xbddba3e94280c4a64d8063468318d1a0c21020007b017c003dbf
  | 0, 1 => 0xf84fe83defdffe72e5f2f76e9fb59b27d6bd7f35af0901089170
  | 0, 2 => 0x3ffeedffff0903f77fbf
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
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
  | 5 => 106
  | 6 => 15
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xc894e17ca91103de009ef5f6
  | 5, 0 => 0x6e6b15296da08be96775c469664d787e64866b4f61b810305d1d00a55c81a6f059b0f7305975714e58d74d1351611c384e5c1d1d48d34d1946ecb51545028db143c04d4042c02137423432924231bff2418260a83f2991103ef79fa83de578bc3d5d2b1839f193b038fdad373771174237272296367c276e35c2b3aa3149fbb430f9b38330602c332f6bafef2df959362caa0b3b2bf37093297eb424276abb79264621db2512ec2b24982a05247a692822ade254220f8ca01d8eff491c6a746a1b12df04176a2f3714447d23129b33ee100e14170fe7d2510ebf86660bb638c60a97920e07215e2206ed8b2e05cc22e2058f0e8d037ef11501ea44f4009ef5f6
  | 5, 1 => 0xfeb66bbae4605ff0deee3556da6eec38cd5dd687cb74dc9bc894e17cbea9733ebcf336a4ba39e421b40f9908b2d634ddb2cded72b21f9a35b1f7cb58b12b6c36abf0fefda91103dea55430d8a1e8f17ea127b8309ff7eb879c96fa119c907fc99b7d27a899f6a9f2939387ca9352573f929bbc97917f85c890c3bbb090a07422902700288a0e0c5f8341b7ab7ec014a87c05848e7adfbf297a3bd46c7535b93672a0d11c713fde12
  | 6, 0 => 0xcd5dd687b2cded729b7d27a89352573f713fde125c81a6f046ecb51539f193b0276abb79247a692822ade2541b12df040fe7d25105cc22e2058f0e8d
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0xc1100
  | 5, 0 => 0x30040800000300404c01020000040000100001400004000018c01040000140000200000000000000008c5104000004c01020000040000400000c000010000100000020440000002300410000020000100000700001000001
  | 5, 1 => 0x10c51020000040000600001c0000331441000000000010000000000000000120040400006000000000010000180000100000c00000304400000073144100000420040400000000008c51033144080000700000cc1100
  | 5, 2 => 0x304400c01010000000000700000400005000000000000000040000000001c0000500000000001000004000010000040000100000400001000000000000000140000010440000002000000000073044000000000000400000
  | 5, 3 => 0x1c0000000000000001000008000000000004010100001000007
  | 6, 0 => 0x200000c00001000004000000000000000000000400005000008000000000140000100000c00004
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 8 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 3 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 4 => checkCutEntry dom_7 roots_7 5 s ws hint
  | 5 => checkCutEntry dom_8 roots_8 5 s ws hint
  | 6 => checkCutEntry dom_3 roots_3 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_9 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 8 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := range_split z5_0 (z5_8)
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

def dom_10 : Nat := 0xffff0000
def goal_10 : Nat := 0xfeea0000
def roots_10 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 5 :=
  lower_iso [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_11 : Nat := 0x33333333
def goal_11 : Nat := 0x32223020
def roots_11 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

namespace S_11
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (4, 5), (4, 12), (8, 12), (9, 13), (9, 25), (16, 17), (20, 21), (20, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [1, 1, 4, 4, 8, 9, 9, 16, 20, 20, 24, 24]
def r2sG : List Nat := [5, 17, 5, 12, 12, 13, 25, 17, 21, 28, 25, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_11.map (· &&& dom_11)
def goalM : Nat := goal_11 &&& dom_11
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_11 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_11 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_12 : Nat := 0xff00ff
def goal_12 : Nat := 0xea00e0
def roots_12 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

theorem low_12 : Lower dom_12 roots_12 goal_12 4 :=
  lower_iso [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xffffffff
def goal_13 : Nat := 0xfeeaf0e0
def roots_13 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_13
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (2, 6), (3, 7), (3, 19), (4, 5), (4, 6), (4, 12), (8, 12), (9, 13), (9, 25), (10, 14), (10, 26), (11, 15), (11, 27), (16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 4, 4, 4, 8, 9, 9, 10, 10, 11, 11, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [5, 17, 6, 7, 19, 5, 6, 12, 12, 13, 25, 14, 26, 15, 27, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_13.map (· &&& dom_13)
def goalM : Nat := goal_13 &&& dom_13
def NN : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xe1c2916
  | 5, 0 => 0xfd575aab93c0f7228c616cec5299e96d30706e42
  | 6, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff0000000000fcfcfcfc00000000f0f0f0f000000000cccccccc00000000aaaaaaaa000000000f0f0f0f000000000f0f00000000000000ff00ff
  | 0, 1 => 0xffff000000000000ffccffcc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x754315
  | 5, 0, 0 => 0x97543269765436095430509743259875436
  | 6, 0, 0 => 0x975435
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe03f800fde3f07001c007781c00330df1ffc7f8f00003f80ff
  | 0, 1 => 0x3ff0001c77f1c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf23fc06fdeff67457da97785c24f31db1750498ba8241b807f
  | 0, 1 => 0x3ffa825f77fdc
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 25 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 25 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 10 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 10 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 10 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 10 then wireAt i else 0
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
  | 4 => 4
  | 5 => 20
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xac05225e81ea162e5e1d4aa81f7c8e90
  | 5, 0 => 0xf27aa6a5d051f507c5159104ba7741d8ac05225eaa294541a0508cfd818360617ecfa1837702c5a955ccd233554c825e3a6b8d412b0e7274276bea4325303d37206585ea1b8a7ef1126b25b70241d3e1
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x200000c00002
  | 5, 0 => 0x400001000000000000000000000100000400000000008000000000040000000000400000000000000030000040000000000800000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_10 roots_10 5 s ws hint
  | 1 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 2 => checkCutEntry dom_11 roots_11 4 s ws hint
  | 3 => checkCutEntry dom_12 roots_12 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_13 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
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
  scr dom_13 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_13 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_13 roots_13 goal_13 7 := by
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

theorem low_13 : Lower dom_13 roots_13 goal_13 7 := S_13.noCircuit

def dom_14 : Nat := 0x333300003333
def goal_14 : Nat := 0x322000003020
def roots_14 : List Nat := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

def dom_15 : Nat := 0x3333333333333333
def goal_15 : Nat := 0x3222322032223020
def roots_15 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000033330000, 1, 17)] (by decide +kernel) (by decide +kernel) low_14

def dom_16 : Nat := 0xcccccccccccccccc
def goal_16 : Nat := 0xccccccc0ccc8c0c0
def roots_16 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888888888888888, 18, 19)] (by decide +kernel) (by decide +kernel) low_1

def dom_17 : Nat := 0xf0f0f0f0f0f0f0f
def goal_17 : Nat := 0xe0e0e000e0a0000
def roots_17 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a0a0a0a0a, 16, 17)] (by decide +kernel) (by decide +kernel) low_2

def dom_18 : Nat := 0xffff0000ffff
def goal_18 : Nat := 0xfee00000f0e0
def roots_18 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa, 4, 5)] (by decide +kernel) (by decide +kernel) low_7

def dom_19 : Nat := 0xffff0000ffff0000
def goal_19 : Nat := 0xfeee0000feea0000
def roots_19 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 6 :=
  lower_iso [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16

def dom_20 : Nat := 0xffffffff00000000
def goal_20 : Nat := 0xfeeefee000000000
def roots_20 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_20 : Lower dom_20 roots_20 goal_20 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000, 36, 37)] (by decide +kernel) (by decide +kernel) low_4

def dom_21 : Nat := 0xc0c0c0c0c0c0c0c
def goal_21 : Nat := 0xc0c0c000c080000
def roots_21 : List Nat := [0x808080808080808, 0xc000c000c000c00, 0xc0c00000c0c0000, 0xc0c0c0c00000000]

theorem low_21 : Lower dom_21 roots_21 goal_21 5 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_22 : Nat := 0x3333333300000000
def goal_22 : Nat := 0x3222322000000000
def roots_22 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]

theorem low_22 : Lower dom_22 roots_22 goal_22 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_23 : Nat := 0xffff00000000
def goal_23 : Nat := 0xfee000000000
def roots_23 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]

theorem low_23 : Lower dom_23 roots_23 goal_23 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa00000000, 36, 37)] (by decide +kernel) (by decide +kernel) low_3

def dom_24 : Nat := 0xff00ff00ff00ff
def goal_24 : Nat := 0xee00e000ea00e0
def roots_24 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_24 : Lower dom_24 roots_24 goal_24 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00ff00000000, 18, 50)] (by decide +kernel) (by decide +kernel) low_12

def dom_25 : Nat := 0xffffffffffffffff
def goal_25 : Nat := 0xfeeefee0feeaf0e0
def roots_25 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_25
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (2, 6), (3, 7), (3, 19), (4, 5), (4, 6), (4, 12), (8, 12), (9, 13), (9, 25), (9, 41), (10, 14), (10, 26), (10, 42), (11, 15), (11, 27), (11, 43), (16, 17), (18, 19), (18, 22), (18, 26), (18, 50), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (33, 37), (33, 41), (33, 49), (34, 38), (34, 42), (34, 50), (35, 39), (35, 43), (35, 51), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 4, 4, 4, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 16, 18, 18, 18, 18, 20, 20, 20, 24, 24, 24, 33, 33, 33, 34, 34, 34, 35, 35, 35, 36, 36, 36, 40, 40, 40, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 17, 6, 7, 19, 5, 6, 12, 12, 13, 25, 41, 14, 26, 42, 15, 27, 43, 17, 19, 22, 26, 50, 21, 22, 28, 25, 26, 28, 37, 41, 49, 38, 42, 50, 39, 43, 51, 37, 38, 44, 41, 42, 44, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xfffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_25.map (· &&& dom_25)
def goalM : Nat := goal_25 &&& dom_25
def NN : Nat → Nat
  | 4 => 2
  | 5 => 11
  | 6 => 157
  | 7 => 170
  | 8 => 27
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x881956b812216bee
  | 5, 0 => 0xfee24069fce75fdbdaa1192ec11acc9bbb9f8c8aab3e8d4b8ec2fa558808a6cc770616a029daf29804bae51f
  | 6, 0 => 0x5571ce4a54275849541c698b537096944c4c79c44b2472944aabf4e84a16605249c0fcf448d58fd647f0cb224717bb2b46da3c74447ac66c4449f5954417aa9f4214c55a3ea368413dbc5b023d2c7c353a4fc206394ead0438abbdef376cce2b36b5383e349824f433a95ef331968b4130e1709b30cca4c42f653d432b35846d29af2b642980ce6628bda13e27e01bb225628c1b241577b92360951f223c385a1f87b1c01c96ea491bfe84a81b27d2611a26397919ba301a188e19d017ae9e2a16b01e5415d3ee201589d57c1517feab104ef361104ad0741015958810060e320f5a3b3b0ebee7890cd4b54f0c21c3560919997804c4bfc004c021da0341d11b
  | 6, 1 => 0xb8fe1f9faf616e2bada6d24cacf0bd5bac06f897aabd8836aa30b727a97aa236a7853e24a625ea14a58443aea476e968a3d366b3a16ca8ada0772712a046c73f9ee2b6579ec0d7899be41d5a9b74bd5f998829a394ad81c7941d35b89381e4a09102d26a8f3acded8dd7584d8da35b008c5b2b6f8c3dbf858b888b4e8a4b2c56889121c586cb1e0084203dbe83d093ae83c702f1834e1a4582b8d63d7b83ced07a399f0c7a260a2f77e0dac775ace69a7597c94173be3a8b71c79575710cff0270b49ea16d7b510a6d0dc9146b09bc616a19a43b6825e35167a2a10667963791676fce60637bd113626ef88961cd881d60617b6c5aea3198599078435742a795
  | 6, 2 => 0xf918fb51f29edce5ef37b654ebda4c2deb4fcf47e82d725ee6d9419ae5830406e4a745e5e3d3e65dd9d792fcd8c3dd20d88d7dfad883e886d4a54a7ed3ab69cdd30d2ad5d215039fcfaaeb5dcac9e179c8369917c51b2e6fc20f81e7c00e671abe97b2cebdfb5dd0bd6d67c4b9c6a5e9b92956c4
  | 7, 0 => 0x5af03eb05abc6cf2584e132a57a1024a556f0695530ec13f52943af552942b7251e81d51516924ff4c4c79c44a9f53ac499cfa0a49226c8f45179a8f43a9f8483f69e5183dc32c5337f1b876358e7c1333d93c6b330961a63264f194317141fd3150ae1430ccd1eb302ca7772fc976f62f1362052e9e70832de85b9229f11774292df8a12889888f26d2458e265363bb26396ad4261c309d2509c4b823a7fde622daf26b20df43cc20292edb1b8548e619f08aad19b1d44816d8a81c16a61199153eaa181234695d10d1aa960faa77070f8898390e7dd0190d61f2fb0d52c9a60cea20e10cabde0a0afb5dd306ecbabd05869eb1033a727c02e9d44b01013f36
  | 7, 1 => 0xc07ccfeebf4172fabe4f311bbe3418b4bd0683e7bbec3344bb04b807ba88bda4b7a1fd24b511b645acac34b6aba1ac24aab1140ca80fa957a4dede88a499e38aa4711fa3a3f2435da35f8a0fa25e4bf1a1946574a07b39919c7605899c48de239b1dd7b09a488f16974a939b97251c9893cd8fe09351acbb9272b1cc91b98d129074f28c906d26118d5eaaf98a81f0ca897643b68380407183233d8082d3eb998276397282739f2081bd8a2f8021fbeb7fe35f827e05acff7b2b17a179e15a2879a4d76c78493a7f7333c42e727daf3d71be65bd7005f1236a4fc62d69b2eaed69b07ce364cf00c563669d956292bf225fff77045f492eb65dc82fa15d6275f4
  | 7, 2 => 0xff939ceffd22ec1ffd058035f9acd0faf8327782f76d67adf4e7fe6ef498545ef4535bf8f0c2900ff05fc8f2eef3064deec76f65ed5ae6a4ec164c1eeb0c9569e8b03ee3e5179d48e49194eae45c7de4e3c88b86e0f3695fdfb32b5bdf91a28ddec49712de1b0bb2ddfd151addd589c4d9ed2281d76eed8dd5d7c256d3fa20bfd1293c1ccd5fbf4fca5838f3ca35eab9c9a019fdc689fa79c6398efac5e58a67c5d3e588c52f7576
  | 8, 0 => 0xf33b5fd0f2854adfd1efb8f3c3d681efc2afde01b031a5c8a6563cc38ab84b5d8a7994f8876dd2497f4590c97e1a8a56764e5f61705b5d9f5fbac6fd5e22a7545cde0cce55df5df851bb2a0f5059633d4f8c57c23e277fff2efbd9641b78d4bc1606144c1561a43a1142fa41
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3300ff003300ff000f0f0f000f0f0f000f00ff000f00ff000f000f000f000f0000ffff0000ffff00000f0f00000f0f00000000ffffffff000000000f0f0f0f
  | 0, 1 => 0xff00ff00ff000000ff00ff00f000f000ff00f000ff00f000ff000000ff000000fc00fc00fc00fc00f000f000f000f000cc00cc00cc00cc003f003f003f003f
  | 0, 2 => 0xf0f0f000f0f0f000f0f00000f0f00000f000f000f000f00030f030f030f030f03030f0f03030f0f00ff0fff00ff0fff00ff00ff0fff0fff00ff00ff00ff00ff
  | 0, 3 => 0xc0ffc0ffc0ffc0ffc0c0c0c0c0c0c0c0aaaaaaaaaaaaaaaa333333333333333311551155115511550f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f00000000
  | 0, 4 => 0xccffccffccffccffccccccccccccccccccccccccccc0ccc0ccccccc0ccccccc0ccccc0c0ccccc0c0cccc0000cccc0000ccc0ccc0ccc0ccc0cc00cc00cc00cc00
  | 0, 5 => 0xf0f0f0f0f0f0f0f0f0f00000f0f00000f00ff00ff00ff00ff000f000f000f000eeeeeeeeeeeaeeeaeeeaeeeaeeeaeeeaeeaaeeaaeeaaeeaaeaeaeaeaeaeaeaea
  | 0, 6 => 0xfcfcfc00fcfcfc00fcfcf0f0fcfcf0f0fcf0fcf0fcf0fcf0fcccfcccfcccfcccfc00fc00fc00fc00faaafaaafaaafaaaf0fff0fff0fff0fff0f0fffff0f0ffff
  | 0, 7 => 0xff00ff00ff000000ff00ff00f000f000ff00ff00cc00cc00ff00f000ff00f000ff000000ff000000fefafefafefafefafeaafeaafeaafeaafcfcfcfcfcfcfcfc
  | 0, 8 => 0xfff0f0f0fff0f0f0fff00000fff00000ffccffccffccffccffccffc0ffccffc0ffccff00ffccff00ffccff0000000000ffc0ffc0ffc0ffc0ff00ff00ff00ff00
  | 0, 9 => 0xffff00ffffff00ffffff00f0ffff00f0ffff0000ffff0000fffcfff0fffcfff0fff0fff0fff0fff0fff0fff0fff0f0f0fff0fff0fff00000fff0ff00fff0ff00
  | 0, 10 => 0xffffff00ffffff00ffffff00fffff000ffffff00f0f0f000fffff0f0fffff0f0fffff0f0f0f0f0f0fffff000fffff000ffffccccffffccccffffc0c0ffffc0c0
  | 0, 11 => 0xfffffffff0f00000fffffffff000f000ffffffffccccccccffffffffc0c0c0c0ffffffff00ff00ffffffffff00f000f0ffffffff00000000fffffff0fffffff0
  | 0, 12 => 0xffffffffffff0000fffffffffff0fff0fffffffffff00000ffffffffff00ff00ffffffffff00f000ffffffffff000000fffffffff0f0f0f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x2ccd96b15ae4b0b131d5
  | 5, 0, 0 => 0x2ccd96b121d6c1520314c75acd88cb131d6b3365ac4a75accd96b531d6c9365ac4c75b25880bd31d601666ad4c756cd480e94a66b35e6b95e99accd97017ab6
  | 6, 0, 0 => 0x1665ac4c741b599b2de2f4c75ecd48f017a63af9accd96b131d7b33602f4c745bd99b01a2f3a0deccd95017a63ae02d4d5e98e90601657a63a588300b30131d3409accd96b131d06e0305680bd31d6016531d34401b60a901f2f4c75f0cd97017a63af666cb5898e847
  | 6, 0, 1 => 0x10131d340c0b00b298e9a2c41accd80bd42620f926cb80bd31d79b0e1405e98ebd99b017a63a5dc0599abd31f3ac02cc05e74e026b33602f4c74cb80b2bce9c200db05680f97a63ae02cd77698e9a601660345e741b00b334e9c3441b3599b01a2f3af666cb80bd5267
  | 6, 0, 2 => 0xb3365be5e98eb80c35202f4c75accd97017a53ae0202f3a701816013601d38680b00c1017a63a09accd80bd31d1ae02cd480d531d6b3360383c7483d9af2ddaf4c75c0605e98e9006c02cd05e98e906b33602f4c747380c13531d344180599b014a634d666c05e98e937
  | 6, 0, 3 => 0x166a2e4c748359a91202f4c75ed4d80bd31d20f6602f4c74b107b33602f4c742380b3457a23a41accd80dd7a63ae020263a68b016017e6af4c7483599b2e02f5299f04d80c57a63af8aa4078bd31d701666b25e988300b3397a63a4180609abce9c20c02cc06098e9a6
  | 6, 0, 4 => 0xb3520315e98ebd99b057a63a21c059a8bce9c20d826c078bd31d7b35202f4c7493d9af360325e99c0404c74d1806d666c05e98e87701360325e980b00c55202f4c75acd78f017a63af66a4380bd31d701866af4c748300b3358a63a298059a898e9a20d66c4680bd31d7
  | 6, 0, 5 => 0xb33a02f4c7483e09b2df2f4c75c060a8bd31d20c02caf4c748026b33602f4c747bd9a92de2f4c75c059a9017a94cd666cb80bd21d7b3364c05e98eb80a90131d3405accd80bd31d28f668405e98e907c13602f4c7473d99b2e32c4c75c04d8098e9a00c02ccd80bd31b6
  | 6, 0, 6 => 0x17a6af4c7483005e98e900605804d4c74d1002d666cc80bd31d7b35202e4c748380b3357a63a2180599ebd31d18d666c05e98e867c13602f4c7423d9a3017a23a41efcd80bd31d20e02a405e74e01601666b45e748300b3497a63a418061af017a63ad66c4d96b131d7
  | 6, 0, 7 => 0xc1529c05e98eb809abce9c2005acd79b01a2f3ae026c068bce816b33602f5298dbd99b057a63a41ecd79b2d6263ae026cb5898e816016601d38681b59a9017a63a35c0599b1602f52c02ccd5ea53106c33602f4c74d380b9357a63a41b04d80bd31d22f66bcd66bd31d7
  | 6, 0, 8 => 0xc15203c5e98eb80b30192f4c0dacd776bd31d34f9accd80c97a67018202f3a701b00b3356263a11accd80c97a606f82a405e98e907015202f4c7403599b01d2f5299ecd480f97a63ae030404c74d036b33602f4c742b80b3360395e99acd480bd31d08e02cb05e98e906
  | 6, 0, 9 => 0x1666cb80d931d701666b83c748300a8bd31d200580559b017a63ac030cd8098e9a6cb666cb5898eb809abd31d2001ae4d80bd31d20e02ccd5ea13106b3365c35e98eb809a98e9a3041accd80bd31d10e02ccd5e9ce896
  | 7, 0, 0 => 0x2ccd80bd4a660002e4d80bd31d6c7666c05e98e9a80002f4d80bd31d6000202f4c74181601666b85e98e9070166bcd8098e9a701666c55e98e907016eccd5e98e90700026c04c74d01601666c880bd31d7b3626cb80bd31d801666cb5e98e90701666c062bd31d701666c07abd31d70002cd776bd31d6
  | 7, 0, 1 => 0xb33602f4c748038b33602f4c74d038b35e6cb80bd31d801666c078bd31d701666af4c7480a701365c05e98e817bb666c05e98e908b3466c05e98e908b33602f4c88e9080166bcd80bce9c700026c05e74e01601666c180bd31d701666bb5e98e90701666af4c78e90701666c07ebd31d7000304d5e98e906
  | 7, 0, 2 => 0x2cd45e98e90601666cb80b131d70182bcd80bd31d70166a4d5e98e90701666c066bd31d7016602f4c748037016602f4c74d037cd666c05e98e9080182cd480bd31d7cd666c05e98e9a801666c04c74d107b35e6c070bd31d801360385e98e817b35e6c580bd31d801362c05e98e8170002cc060bd31d6
  | 7, 0, 3 => 0xb3365c05e9909d801826c05e98e907018eccd8098e9a700026c05e98e8060002ccd80bd42660182ccd5e98e90701666c07cbd31d7b3360385e98e90801666af5898e907b3362c05e98e90801666c05e98e84700026c04c74d186b3365c05e98e90801666c04c80e9a70166bc076bd31d701666c05e74e107
  | 7, 0, 4 => 0xb3526c05e98e908019accd8098e9a7b35e6c05eb131d8013602f5898e817c7666cb80bd31d801666c04c74d037b33602f4c7480a801666c04c88e9a70166a405e9919d7cb666cb80bd31d80002ccd80e0f1d6b3365c05e9901d80002a405e98e81601666af4c748097b33602f4c78e908b33603b5e98e9a8
  | 7, 0, 5 => 0x1666cb8098e9a701666c04c74d1670002cc05e74e0360002ccd8074e1a6b3365c05e98e8380166a405e98e907b3365c05e9911d801667cd5e98e90701666c06abd31d70166bcd5e98e90700026af4c7480160002cc05e98e966b3365c05e98e84801666c06cbd31d70002ccd8abd01d60002cc04c74d036
  | 7, 0, 6 => 0x30405e98e83601666cb80bce9c7b33602f4c7480980002cd080bd31d6000304d8098e9a601666af5c98e9070166a405e9901d701660385e98e83701662c05e98e8370002cc04c74d16601826c07cbd31d7c1666c05e98e9080166a4078bd31d701665c05e98e83701666b15e98e907cd666cb80bd31d8
  | 7, 0, 7 => 0x166a4d8098e9a701666c580bd01d7b3365c076bd31d801666af4c80e9070166a405e9911d70002cd180bd11d601826cb80bd31d70002fcd80bd31d60002ccd80c97a66000304d80bce9c601666af4c7480c7018ecd480bd31d701666af4c74e10701666c780bd31d701666c07698e9a701666af4c74d107
  | 7, 0, 8 => 0x182ccd8098e9a70002cd480bce9c6b3526cb80bd31d80002ccd82bd31d6b33602f5898e8380166a4d80bce9c700030cd80bd31d6018eccd5e98e9070002cd48098e9a601666c05e98e95701666af4e98e907b35e6c05e98e9080002cd480b931d6b35e6c05e98e9a8013602f4c748017013602f4c74d017
  | 7, 0, 9 => 0xb3365c680bd31d80002caf4c748036b33602f4c74e108019accd5e98e9070002ccd4c74d1060182a4d80bd31d7b33602f4c74d10801666af4c748037b33602f5c98e90801666c04c74d1570166a4b80bd31d70176ccd5e98e907016602f5898e83701668cd5e98e90701666af4c88e907cd666c05eb131d8
  | 7, 0, 10 => 0x2ccd5e74e1060002ccd80d179d60002cd280bd31d60002ccd96b131d60166a4076bd31d7c1666cb80bd31d8000305480bd31d60002cc05e98e82601666c380bd31d7b33602f4c7480c8
  | 8, 0, 0 => 0xb3362c05e98ebd99b2e02f4c75c0599b0179d38c02cc05e98e836cd666c05e98eb80b3360263a69accd80bd31d06f76ccd80bd31d7b3466c05e98ebd99b017a64475f1d99b017a63af666c05e9901d7b33602f4c74e3d99b017a63a41eccd80bd31d34f666c05eb931d7
  | 8, 0, 1 => 0x59af3602f4c75c04d80bd31d02c02ccd5e98e906c1666c05e98ebd99b017ac4c75c059a9017a63ad66a4d80bd31d7b33603b5e98ebd99b017a63c75c0609b017a63ad666c070bd31d7
  | 9, 0, 0 => 0x2ccd80bd31d6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 39
  | 5 => 46
  | 6 => 53
  | 7 => 60
  | 8 => 53
  | 9 => 46
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1f1ffe38400ff03e3fe07fff1f031ffe07c00ff0303fe07c001f00fffe003ffff00e3fe003ff1f000001fffffff000001c7fff1f
  | 0, 1 => 0x1f1ffe3fc00001f1ffe38000e01f1c003fc00e01f00003fc00001c1ff03f800fc1c1c0038000e00003f0078001c1f1ffe3fc00ff
  | 0, 2 => 0xe3e001c7fff00e30001c7c0000e0e001c03ff00e3e3ffc7c0f1fe3e3ffc07ff1f1ffffe3ffffff1f1ffffffffff1f1ffe3fc00ff
  | 0, 3 => 0x1f1ffe3fc00ff000000000000000038e0038e1bfffc0ff840fe3fffc71ffc01e4e3e3ffc7fff1fe3e3ffc7c0000e3e3fe0000000
  | 0, 4 => 0x1f1ffe3fff0ff0003f007bf01c0003f0003f00000000007bf00000000007800000000000780000000000003f000000000003f000
  | 0, 5 => 0x1c1c0038000e01c000038000000303fe07c001f00000000000000003fe003fe1b00038e003fe1b00038e003fe1b00038e0038e1b
  | 0, 6 => 0x1c00003fbf0001c1c003f800e01c1c00383f0e00003f007bf01c000000003f00000038e0038e1b1f1ffe3fc00ff1cfffe383ffff
  | 0, 7 => 0xe0e001c000000e0e0000000000e0e000003f000e00001c000000e00001c0000001c1f8e383fefb00038e003fe1b1c1ff03fbf0fc
  | 0, 8 => 0xfc1c01f8000e0fc0001f800000e0e3f1c7bff1ce0e001c7bff00e0e001c7bff00e0e0000000000e0e001c03ff00e0e001c03ff00
  | 0, 9 => 0xff1fffffc00ffff1c01ffc00e0ff0001ffc0000fcfc01ffbffe0fcfc01f83ffe0fcfc01f8000e0fcfc01f800000fce001f83ff00
  | 0, 10 => 0xffe001fffff00ffe001ffc0000ffe0003800000ff1c01ffc00e0ff1c0038000e0ff0001ffc0000ff03f1ffff01cff0001ffc0000
  | 0, 11 => 0xfffffe3800000fffffe0000000fffffe07bf01cfffffe0000000fffffe3fc00fffffffe38000e0fffffe0000000fffc01fffffe0
  | 0, 12 => 0xffffffffc0000fffffff83ffe0fffffff800000ffffffc03ff00ffffffc000000ffffffc000000fffffe38000e0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x50c9a084006f03636c04e4812030eda04c007f03024804c001200fdb6002dbed0061240024800000001fbdb7ff000000c2d2412
  | 0, 1 => 0xf0eda1dc00120f0eda1d0006d0f0eda1dc007f0f02481dc00120e0ed21d8007d0c0c92190006d0a0ad0158005c07064a0cc0033
  | 0, 2 => 0x63636cc6f6c12630248c6d2412606124c236c0023224c44c0c1221612c4064c020f6ffe1de487f0f0edadfd247f0f0eda1dc007f
  | 0, 3 => 0xf0eda1dc907f080890110904c25278e48f8e3bb5b40f6840fa39a985135001c463636cc6f6c1263636cc6f6c1263636c0424800
  | 0, 4 => 0x4f4ffa9fff07f4a4bf097bf05c4a4bf0973f04c4a4bf097bf05c4a0ad0979b05c4a024097920104849b0933f04c404120823f000
  | 0, 5 => 0x9c9c9339093ed9c0001390000093924924c939290900120093806f6ffedfffe7f6d6fbedbffe7f6567aecaffe3b2d2f9e59f9e7f
  | 0, 6 => 0xded361bfbf390de9ed3bf9b3fddcddb3bb3f3eddadbf1b7bf3dcd0d121a23f380b5b78f68f9fbb9f9edb3dc93ff9cfdb7392dbed
  | 0, 7 => 0xf0f125e236c00f0f125202db80f0f124823f800f09001e21b780f00001e212400fdffbffbffffff5f7afeafffbbdedff3bfbf3fd
  | 0, 8 => 0xfc9c93fb1b7edfc0001fb12400fafbf5f7bffdcfafbf5f7bffdcfaf365f7bff90faf3640424800f8f9b5f33ffccf0f125e23ff80
  | 0, 9 => 0xff0edbffd247fff0edbffd247fff0249ffd2412fefff7ffbfffdfcfdb7fb3ffedfcfdb7fb3ffedfcfdb7fb36c00fcf125fb3ff80
  | 0, 10 => 0xfff36dfffff92fff36dfffff92fff36d3d2db80ff9edbffdb7ffff9edb3d093edff9249ffdb792ff4bf9ffff45eff0ad9ffdb45e
  | 0, 11 => 0xffffff3d24800ffffff242db80fffffe97bf85cfffffe152d84cfffffe1de487ffffffe1d2486dfffffe0424800fffffffffffff
  | 0, 12 => 0xfffffffff6c12ffffffff3ffedffffffff36c00ffffffe63ff80ffffffe63ff80ffffffe636c00ffffff3d2dbed
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 52 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 52 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 103 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 103 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 103 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 103 then wireAt i else 0
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
  | 4 => 3
  | 5 => 145
  | 6 => 1500
  | 7 => 1138
  | 8 => 19
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xd8908a3caa8454f9823d7bb7
  | 5, 0 => 0x7d24a32c7cb6ccc37c3bc47e7b8f9e4279835c6e75ebc2b774520a8b708e3d3a6f6571206d575eb46ba3007d6726fd1f6684f65a63dddc6763669d9559547852556f0695525322025137e5944db3015a4d035fd2487ef5e247ece91247acd04445ce2e294549c26742b779a3423252c5421eb53441bbd8db3fad8f4c3e6329a03e04c0723b51cf693aff6277320baad93078c0813000f80e2eb983852e5034ad2e0ffd7f2ae793e92ada198828e38c4e27add3f226778b4020f029a01dd8257d1b935e6e1a1f37bf17e8f1d815822d32153eaa1812fe6fd31234695d11f1ce821192001f0faa77070e93be640e15721d0cd49b0a026dfa600223c06a01013f36
  | 5, 1 => 0xe5cd6a22e1af96d7e152b03ae140d5ebddcfdea5da24f17ed76eed8dd6caf2f8d6bdfbfad4b826a0d1b9e9fad1293c1ccd46e6fecc34016fc8ea34e9c8b64b69c821b5bac81790e6c7b267c1c76f2ee3c76a9453c6e7045ec6d6b739c6398efac1bcb379c16d2569c095d15ac08ee41bbe469854bc5ccb60bc03177bbbec3344bb6cb1b2ba88bda4b7a1fd24b5671537b542871cae503d67acedf229a9ad2fbfa87de980a5342840a47ee62ba25e4bf19c9c57949b0d0fc3977ed1a09504ce1394ead10893740721911a363b907b694f8f1775d28d2dbf3f881e9373876db58986fee2ec84d4c6ed839c0c6882f209e582d540a880cdcee28021fbeb7d9e2cd7
  | 5, 2 => 0xff067dc5fd99091cfd685c8efd22ec1ffd058035f9acd0faf7249a68f4e7fe6ef44935f4efc4c28eeec28614ea3a9c54e9ee24e9e9c168d1e9b793f4e8cf45b2e71e2e62
  | 6, 0 => 0x9ede5f8097c0ec40938390c08b08166084aafc7080fe2c3076636a7074eba9406dc984206a14de7068d7fe10681af190617f3be05fd0f1105f2ecc205f2790c05bbae7e05b10e6b05a509e605687e890562a0ac0559e5f5053cd7d1053c7a0b051f1fac0512d18904ac2cb3047b57a903f7cba003ebaeda03c75b2a03b6719203833f26033a727c0337e2930322eb18031d018103087e04028da25d0289e80802898f5e024ad8f90248132d02465a51024365d60225f9ec020e052301e3cad001bcdc8d019c9fad0183de15018309d9017f3bda01752afa01410437013616b3012a584001147e9b00f94cd000ba1c5000a28bea006c268400296567001a6049
  | 6, 1 => 0x1305f52212ee238212d1fe4012bbd30812baa677125d0b7e11b4bd5b11a579d611a18517119b91ab116b4724115b67ca1142fa411120d64610d89c4810aeb074108ef5b91089979f10674965103a9912102d648a10105d9b1004efa20fcb33c20faa77070f3d84400f0e91990eec435f0ee5d4340ee271f80ea8faac0ea800b80e255d760df70cce0db753420d9dd24c0d9a92370d91ebc20d6e8d170d4430e80cfc43180c8c4ccf0c6aeda60c60dcf80c18c4240c0ba5d40c0930a10bcc18bf0bbb8e270ba8521d0b88cc090b641d450b5bd3a60b59e3bd0b3080880b1a7d630b05d34b0afb5dd30aefe7a00ab629b70aa0caca0aa03d900a3ff7660a386e39
  | 6, 2 => 0x1f09477c1ed20e051e6285251e2780c41e08e1531df468421da04c391d73f5661d4c60a11d35f1f81ca3d9531c7f55261c6af0321c4d1cb21c35b2841c2546331c18469a1bdb5b301bb1776b1b78d4bc1b40c0441b3c1cc21b0865be1a7bac7219ff9c8019fb483619f2db1c19c2b1f01972f1be195f5caf192a0dd618ef4baf18eed24c18eb577118bf975f1870ade6181a0481180c2da517ce2ba217b93ed6175a9ac81756386817497f4a17353650172c13601665ef1c1611817416100cbf16066cd91606144c15f71c1b1561a43a14c7480c1499cfe5146bdca814696ac21422b86f13fd04b313fac4d313ea83c213b3807b139b02df1368b3e213346ed1
  | 6, 3 => 0x2c5afc882c4d2a222c1a29112be8c6dd2bc612742baefdce2bada1a72b5787d12b3d279f2b25f1c52b15a4b82af8e8dd2aa964312a430f592a42cf9a2a1317a02a121f8d29f9ea3229f1177429f0b1cd29d10a3229a6739a292162fe28b13185289a985c287ee42c28668e6d2819312c2802e9c9275958f22750b4f6265363bb262a32f425e030e4255c4db225320fbe25318cf4251c2949245fcad924425a8423fa873323b12dec237d543d2373cc5223679dba2359c6d022e093b222d25b5c228be26a2256b04f22521a042213883721d8db472177d428215e4c98213819c9205b0a2a20257d1e2014059b1fd652f71faa948b1f8738591f6fbf471f3108e2
  | 6, 4 => 0x34c7ff3c347c735e3473d1a63451707d33df688433d93c6b335d8195331682743303cae532e38d4f32e16b89326a54943247aaca3241f772322e87c431f5eab33185f30f31761594315c50af31472fc2313ee4c5313df41531381b07312ae6df30f2019a30d9fb7930b9d1dd30a9d7c930a5e218309e9761309c65f3309ade1b3078c081306f6ccb30633068304b0f21302a0a2630010ce22ff2eea02fefcd272fec250b2fbf5da52f7a8db12f7343ff2f6745e12f643cf62f37b6b72f2d39052f1a95f82efbd9642ec68d272ebd3d6c2ea523322e8fba352e3061ae2dfdbfd52de6358a2db09fc22d9165262d90a6012d7d41f82cbb9f1f2cadc4612c7dc05e
  | 6, 5 => 0x3e9e85263e896cb83e63d62e3e6329a03e56ef7b3e277fff3e0ad2fb3dce4f973d8f565c3d8b1b8b3d8a3cae3d820b7b3d6b77133d4e5b033d4903cd3d44b5c43d1f3f593d0b3b903ce8d0283caa19c33c644fe93c5112f13c38e0113c346cd83be497a23bdc2ed73ba7c5f03b33d6c03b2c3bb53b28a8c83b195d1a3b0db0ad3ae826bb3ac9b30a3a84baa43a8122023a67daad3a10565439ff1f0a39b103453993975b392f38243929da4e3909b49e38c1057038a4a5e23885fcd2386890e838658553385204ef37fdfb7837d8b58137b016de379a6182373817bf36b0664736a8e1d93661a5cb35f2a55735e23d5c354e1e60353aa3c6352464f9350fe1ad
  | 6, 6 => 0x491b32f748c35a8b47a02cf14734005047335cda47329de246f1b31146dd66d846bddc5e46b55adf46a11ddf468eecc8466dcded4649a34b463a36bb45f9c57745cb4f1b45b797dc45a7f59845940ada456daacd453038ad4523bdd94519cf8c44e919b244c79b8a44be7c334497853043e3db9743a7d46c43a0a4d643415cc54336dee14330d951432e5dba4307103b42eda89a42e28e1442bf1bb542ba8c1c42b779a3428120f84267208641d944c541bbd8db41b4d9a641b3665641ada2b441a58777413f306a40eca96440d00124408a06cf4089915f400945b43fde2fa63fd84d593f7898033f4e227d3f227ddf3f0f37c13ef9b7083ed249333ecbdd50
  | 6, 7 => 0x534afad352dd3cb652cc268252bab121528d58f7528866f75281620b522c1d2d51e9127651cda2a251ccc13e51bb2a0f512cbc7f512495015121a07a50df0cf150d485a150a9730450a1bacb5069bcbd5059633d4fb1b6794f9d2f8d4f9d1e774f8c57c24f8c4e0e4f7735ef4f050fd04ec280834e79b24a4e1717654df560734dd542384db248164d977a104d84259f4d7c0ddb4d6535ec4c6700e74c388e2d4c1326ad4be8975b4be3ee324ba260e84b83f37a4b75ea1e4b47cce84b2e44754b21fba14b11aa524b0d87ba4af8703d4ad762854ac64d7b4a9f53ac4a6767114a01731049eb066449dd0e9149b6983f496bd12849585913494572b949335a0b
  | 6, 8 => 0x5d8030b75d59fdec5d4b941a5d3f7bd25d0a06c85d00c56d5cde0cce5cd770455ccd4b075c5ce06b5bec1ae15bdd230c5bc0ce6c5ba915895b8f00c25b7008c45b28b7355afb09185ac7832c5abc6cf25a353b175a17fce059f684b259f502be597e76b45925466958e6c54658e35704588df5d95865c8095837177e5817540b57ab48c157a1024a5794fb70576c925c576751eb576611cb56e6f7eb56d7ea5656d29d1756aaafbf568029ba567eb156567c7f51566bc97456488c3a55eeb91a55df5df855dbd5b355b9f6e555a0239d5582b7b355739b7c556a900e5530a86c54c9884054a9557c549413d75488605d545833245421f2ba53e2c57853cd1deb
  | 6, 9 => 0x6b7188956b713d786b0ca3d16aca076f6ab1a0db6a9d18446a8f01346a2ef61d69db04a569148b686909685e68eefaff68df8d966896eaea6886c0b6682c83d86827ae8567d30b406776f078676198836726fd1f66fc78da66ac6aec66596eea663e596f6624d4f6661f8dfe660f2a866575faf264dbd5c464bd70fe64b23f0e64aa6b44647d2ee06472b7016310f02f62da87e162bf39f96264afc16243e4b4622a4e0c61dfaca961b6a79261ab00a961874d9061818f6f6115d86e60f47f6c60dc0ef760c1af3f60a44355607f3e8c603ba18c602f2d625ffaba205fbac6fd5f4ce3e85f35ba935ee4680f5ed6a3f15ed5c2bf5ea610db5e22a7545e12ce5c
  | 6, 10 => 0x7607603675ee73ad75d32c7d7522e0b67508aada7508768874e062cc74b7658874a44fa47447c6f973fa28f273c6a9c6739a2d4a739a0e54738c0a847361e71e73493a27731a9a3772c5abb4727253ef725557607246fea771ca317b718aa31d7180f6877170d1b4716e5da97130886e7129e8b070da344670640070705b5d9f7037bb13702276206f9a15cd6f9599c06f8476496f4c3cf56f1715236f0ee7fe6f01a5d36efd35fe6ee7589d6ee46b536ec9ecb36ea7701a6e97547b6e97376a6e3f00b06e24e7616db3cd8b6d8815996d6074136d5b00e46d1b608b6d055eef6d01b3cf6cf954796c84c2676c665bac6c587ccd6c0fb1986bba04806b9d976b
  | 6, 11 => 0x818c8a24816ee385815a180580f9a39480d851b58069eaef802889c88021fbeb80087aa87fd737a37fb866157fae95827fa0bcc37f685e077f4590c97f1e33537f0f88c77ed1cb467e6cc6297e6829297e4dc0ce7e4b58517e41f46b7e2488817e2317227e1a8a567df7c5a07db1e1917d24a32c7d1b507d7cfde4937ce7e2b17cb6ccc37b9202477b1fa70a7b0c17e77acbd9467a7382a17a1482747a0a9b177a01223179c2eecc7985d1f97951d578792d2bd6791e9fb778f27e2878dd6d38788f95117879923b787589f8784337a87829da4177a8449777820cc07728326676f6d5a476d063dd769b1dfd768e81ea764e5f61764692e67644e31d761e2a87
  | 6, 12 => 0x8ab84b5d8aaf8d4e8a7994f88a4c27bb89cee35d89cdf33589cd0684892bf4c289143e428910bff48905ec5388ff750b88f300e1885d12d78858f5c18809d5f487f2d3ba87e4b66087e13aa087bd68e187b2ceb4879add67876dd2498749a55b873cbec986a439fb868f8bfa864f5914863b65ee862d7dc2861db7ce85f5891085d48fa385ab6563859b43c4858659ca8544e6468527bd3a85184ada8512c0cc850f970a84f507718452d44184047b2383f8d5db83f7115a83f48aff83d7542a83b1739883b00fae83a21eb1838040718362909783621177834632f08320fd1b8312ea9182dbd05f827984f9827963fa827639728220478281ad224981a42827
  | 6, 13 => 0x95d7f1c19582ff9e9551aacc95370e7694d38517940d963193cd8fe093c2bae393ad21ba9388612993835e66935ddd6e935371a9934a18bd9349e0409322c34692cd700b92c0ee8f927dd870922ccdbb92002a6a91fd1dbb91c9a37991c8a36f919f9a92917fb21d91592acd91131f3590f68a7190e225fa90d2174890d0b25890c97f53906466e59063583d905e4b308ff6aa358fce68418fa2db658f74f0a98f7301af8f4a16428f25ac578f09a0718ea2abb28e965ddb8e94ccd38e7d732a8e52fbf68e48ebd08e183e158e0b555c8d6a7b858d5c0a998d5bce128d32e83b8d219bf58cfa91f68bee01d98b66da5c8b48f93b8af097cd8aee218b8aba15e1
  | 6, 14 => 0xa0edcb9ea0bf0646a05f6e2f9fe480b99fb4bcba9f9298bf9f34c2509f008cf19efaea139ed6de7b9eb2472c9ddfb7989dd260f69dce524d9da91d819d6fd84f9d6c560b9d678a6e9d3121ea9d2c5ffd9cefd78c9ced70249cec5eb39ce1a3729c9c57949c8160609c6826aa9c5e325a9c20d3b29c1ef4619c0647769be7a9099be3accb9ba065419b8d299c9b3509fc9aaba6e69a95b69e9a847d599a488f169a3dde069a255f3b9a22029199ce129a994e0ce69933b4439930a0fc9927cdcc98ebd17898c599a1982e64fb980955f297ebea0897a00225979c56d897708ba5974a939b973d9af497012b84969645529689804d965db264961ed46396012313
  | 6, 15 => 0xadfafb7badc5dfe7adbf879fad896662ad7309f1ad6e83e8acf5e8efacd35171ac5aad7aac4df83babe10579abd7936dabad06fbab676f4fab3d5878aad76587aaa90603aa9545c7aa7b50eeaa3d4546aa1f6e87aa191824a9ea9735a9d57912a99c2534a900f5c2a85f673ea85b062fa840633ca822b426a80fa957a7e206d2a77ba7efa73b62e2a7228789a71f7ceda6cd1d65a6c1dd27a6563cc3a6547150a651932aa630d5b0a61bfe94a5fa6e2ba5d4719da5d42f5ba5c2748aa56be49ba54a6a95a5480804a53255c5a509d3d0a477d6c5a466259aa4428e5ba41794aaa3e65ce5a3d87e06a33588fda2d855f3a2b35b7ca1ded325a188a62da1536890
  | 6, 16 => 0xbc5ccb60bc591900bc10ccdcbb850c9ebb184a9abb11473fbae9d770bab9a1bdba549375ba437f4eba423037ba40b91ab93206deb90dc9b5b8e03f25b8ba7db4b86243b6b8197fd1b7dce78eb78864c3b75c39a0b747237bb72f93ffb6cb1964b6459460b635de6ab62bd8c0b6251136b5a0fe76b57d39c5b55b2dceb45b607bb4184376b3fad78cb3b8e1a9b32acdd7b3120380b2ce525eb2adafd4b281625bb27deebbb2700fdcb2516d61b1eb36f8b169cadfb161fc5db0cf1072b08b6c2bb072d957b05fd0e5b031a5c8b03048a6b02f596cb02513ebb000358bafe1db8faf73e99baf647c31af47d2e4aec1fd5fae8f2a8cae87a2bbae6de29cae66d589
  | 6, 17 => 0xc6aaa746c6a5ad90c69fce5ec6535a97c5c29045c5736c6ac543e6bec50c7b54c4e045a8c4d85491c48fe98ec476db43c4370babc432019bc4232d1ac41ed601c3d681efc3b34d4ec3a56e6fc398766ec3737f0cc3606443c32be95bc30d6fe3c2f978fec2e932bac2bc05a5c2b84f8ac2afde01c2a091e1c29a9771c278c27bc27811e5c2683a37c219e413c1d25f49c1a99556c182a013c1711256c0cd281cc0c2be92c0ae99dec0a55ccdc095d15ac05fc100c05eefcec02e5d34c012b8d4bfe17047bfb0ffd1bf82112cbf64a542bec4f692be179289bd9d4a99bd9159b9bd9001abbd6d9bddbd0b3f0bbcc8e334bcc6ad89bcb01311bc878e76bc84df1c
  | 6, 18 => 0xd2099c14d1f83001d1efb8f3d1c8904fd195040bd1779821d137f74ed1293c1cd07186c8d0541aded010ef66d0022fedcfcd16b6cfafaacccf4fc704cf384970cef1d2aaceb692f4ceb4067acea577afce7088d0ce3a426ace32531fce1ee8e6cdbf33b3cdb0a1f9cda95987cd8c6716cd853652cd13ed6bccfb6ba3ccc7daa6cc994278cbdbb155cbae6cbdcb5a385fcb430ccacaad7443ca35eab9c9fcc544c9db535dc9b19f1dc9a3b4fac996b3b6c95a165ac933e748c8e9878fc8cc1ba5c8bdc356c8a7981ec82aa73ec822cda5c80d6cb3c7f13af4c7eee8dbc7ec7312c7e41740c7922905c76b6ab0c75d9bc3c74dc1ecc72c9218c70c24ecc6e21188
  | 6, 19 => 0xdc90e37bdc52a6e6dbb7842adb76ec15db711277db4f33a9db1540e0dafef9a9dabbb2acda9fdba6da650bedd9feee8cd9fb6b94d9d2c684d9c29a4fd9bee8b0d99d8f06d99b8409d8ebb4bad8decc69d8c00a96d89f3369d872797ad8339111d7adc8ffd78c0afed76d9a26d74ad0d5d748aebdd7482c02d744500ed70a1d9bd6bc63dbd6b4c389d697b081d68e0ee1d6360ac3d612c66fd5f531afd5f3eb55d5dffed2d5c6db4ed5735722d568b144d5676af3d53d3f66d52b0a13d4b826a0d4af50cfd4938e6ad48a8f6cd44fd9dfd3a84f1fd3895d08d3661707d355d4ffd30f653ad3028444d2fd1e15d2def3e9d26e2c13d242f053d2273c28d20d1552
  | 6, 20 => 0xe7c5c420e7b11765e78eae99e714a497e6f71c21e6dfa69ee6729df9e636d437e5f7c8dfe5f130bbe5e351dce5e14f13e54c555fe54b61f5e545e120e5432933e510d727e4ea6364e4de93f4e4512071e443cbace41e5447e3ec2954e3ca2ab6e3c0bf0be383dba9e3689fd2e30962e5e2f911b0e2a76435e2a6f24ce2783331e26cad09e254a19ee1fd09cae12c5e2fe11e7f50e0fca6aee0bfe9fbe0b2b2ede0a16a4de079edc2e0558fe3dfa5e763df921631df7dc165defee7bcdefe0162deec6317dee29a6adecb25b6dec9dac1de90f3a7de5cb0fbde4eb049de35f7a5de2834c3de059452ddfe1a3bddfb04cddde63f57ddc15ca4dd7bf247dd1bb31c
  | 6, 21 => 0xf2483ceaf1e76b99f1e66869f1d51328f1d30ad0f19a275cf19580b8f12be4b6f0fa8a62f05804caf0557068f03d9387f03c0281f02597d4eff06597ef885172ef831902ef6b82bbef321432eec22234ee6c74d1ee5455feee5390f5ee44aee7ee410803ee2c8976ee1fa362ee000531edae8b10eda41927ed459ef7ed37c018ecf2ba94ecef841fecc601fdeca37684ec9469cdec362226ec06ff87ebefca4bebe2554eeb7fd924eb38e2e2eb2c0db6eb2b9f5deafba6c3eaf5c476eabceb59eaa27e4fea96d1e2ea206746ea15700fe9596d01e949dff6e93c0117e8a543c6e8927ce9e88faa9de88d44c1e86bd220e82ca1a0e8047120e7e8d4afe7e6faa8
  | 6, 22 => 0xfb379514fb2b821dfb237bfffb211cecfaec6079fadb836ffac23f5dfa72f38afa574c46fa3689a5f9d074b8f9872d4af9824cb5f9143161f908e400f8c57b06f89c6bb5f892f27bf8758691f84ec7eef842a86df83f5c6cf83dd259f82e9ecff81e117ff81132e5f7fc1ceff7f3c11df79aba4bf73a66a0f716d4caf6e6c10cf6a1142df681b3f2f6725022f6535463f650f9aaf601a4eef5ebce57f5b7b2e4f58182cff51cd756f4ebb8c3f4e8230af4bb552ef498545ef4723ae7f4535bf8f430144af409b81ff406e049f3dd72f6f3dd268ff39bac49f360add7f33b5fd0f32a1730f3050dd7f2da1b3ef2c1cb3af2b97b7df2854adff275e045f25014ff
  | 6, 23 => 0xffabe638ffa2cedeff91be5cff88f5fdff641879fecd2018fec38c0ffebe0ea5fe78c91efe73e1fffe4b532dfd48403efd22ec1ffd1ef844fd058035fce3f7c2fcbce5a3fc9f7816fc714592fc5855cafc4a1fedfc3650befc0c146cfc075989fbeed6c8fbe81295fbc9a0e1fb6cc623
  | 7, 0 => 0xe8414b20e783ebe0df078900db675560d9a92370d91ebc20cc7aa850cb3009d0c867e660c2cfbb60c22507d0c167f100bd753a90bb2ffb10b989d440b41c7720ab7b9ae0ab0afbb0a9628be0a71f9560a2e18720a172c490a07e09b09ee1b6f08e13cad08aedd4607bd347d07af559e076636a70754ea15075140fd06b07a0306634425065223ce064612c706291d83061ab28605ad2f3405a3eb0a0590310f04d0acec040745c603e36454036df150033b05b50322eb1802d5abde0296f5790291d00a024a740d023f103c023c952e01a603fb0198251c0188fb4b018309d90129b75501283a1700dd496a0086a50c006499150027347900103def0008238d
  | 7, 1 => 0x1d73f5661d29fe0a1d094b741ca0b1831c53b96d1c1ffead1bea35011bde45011b78d4bc1b70b1901b52f3321b325a461b2d157f1b1036f41a5d39541a45ab1d1a433cbc1a2bfa9c1a0dc40d19e360491979f417196672e1192a0dd61900f4291881f68618787ffd183e83051821179f181aa94117a8202616e8db18168a4efe1662ea0a1606144c15ff8a471581f8c81561a43a1528ba3c141a4f1c14121a0c136d10ac12baa67712b8ab4112b8884a12ae5da3129997eb12798028124e26351232479711ed84b711eb7ccf11b4128d1198114411761aa81134c934103ead2a0ffdfe370ff073950fd4c3f50f8b2a5f0f6b9a140f3d84400edd17080ea68d81
  | 7, 2 => 0x29f0f18429e942c42964176b291abe5628a4a83e284f0649284db2db2838c79a2775450f2774c460275958f226e36c2426beaf6f26bb2fef26a4b5bf264ea12126488ebe262d41fb2609324125bece64259eb530258a6ea4255ffecb24cb7b292485a934246ade962468a85e246554a62438a25923fe6fae23afce922398f3102325e28c231857ea2310763b23038dd422ea3ac022543c1c22521a04223682592219ec0a21f6124621e9d24d21a5f9682179389d2081cc612064873a204aaf2d2046aaad203e530f2015ae6f2014c6441f9bef851f3d31db1f3108e21ee4e3db1ebb13731e8eec381e739d441e3d0e221e17d8601e08e1531d989e101d81c57f
  | 7, 3 => 0x387c221637dd7e8037a1ed1c379a6182378f31e83732d33a36f4981f36e4026d36c744ae36b6da9236ad5160359f67e7359aee6d357bcd57355e29ce3518dab134cf795334ceb8d13481847a34746a9f34744a7f342cdee9339be830333d92c433193e9a32c3d3da32ba82ac3294bf403243d5cd319b3e42315024ba31381b073129ad3f3122199e30f26f093078c0813055c0a6302a0a262fbf18df2f7655c82eedfa852ea0b9112e46479b2d770a592d6df75a2d014b912cf3c0ef2cb7e2692cae27f22ca821632c1543872bdd94e82baacaed2ba0a43a2ba064522b81626d2b698d6c2b48380c2af4104e2a7c85282a6cf0712a6bdfc02a5e00e12a5175e4
  | 7, 4 => 0x472e33c146e1bded4696c818465e79d54609964845f6b584457c5ed144d9dfff44cd758b43cee64d43b9f0a343b4257143555fb0432891ef4309ffd84305883642b779a342815d8a4223bdb94215deda4214fad141a8390641a4b5d6413f306a413ca696410d769640db2d8b40d0012440bb28344079af63405c8f3d40455b7a4025ca0a3ffca0873f8b9abe3ee6de3d3dff89d03df1aaf13d18fbc93d0124c93cedcf813c9f3cdf3c9dc2fe3c8fe41f3c39fd5e3c21f90f3bf3e2703bd0b7833bc2d8a43b76a7473b3c318a3b23954e3afd7b253acd3e823a8b9b213a8b1a653a861c993a67daad3a47663439de879e396cbe7c38b6a98b38ad846e3899ed18
  | 7, 5 => 0x5275541c520a3fab51efbb6051d2062b51bf3f2b514f6454514aca6d51099cc651007c3a50c9577f50c4b4ed5038abd64fb2394c4f943bc44f717d1d4f490be64f0fba7a4ec05ebd4e9d19034e7327324e5bae794e2ce2974e1db72a4e1717654e0e9fc94de27c5e4de254b54dd111674dc27b5b4d2b306b4d17706a4d0476064cfd734b4cd8ba054ca60af44c5cc68f4c173de94c1326ad4bff26be4bf147df4bc969994bb8974e4b83735c4b7591cb4b40518f4b180f9b4b0c2c394b02825d4afc5e1e4ac0774d4a6707154a5928364a3f78dc4a0d197449e125c649d602e849ccf756499b08ca49148db048fa38cc48f889f848f0bd7d48ebd2aa47f69d26
  | 7, 6 => 0x5f5d13a95f2a63495eebace45edafec85ebcebc25e90082e5e1657ce5e06e6065debf6475d9647d45d7bf2db5d3a46645d2e415c5d23bf8f5c9fbd605c91de815c3772f85bff541c5bdfea355ba915895b9302e65b4388f85b2acd595b0171135a7078f85a437adf5a1dcce55a17fce059f684b259f223e559e5330159d66aa059d395c75992adb0596bf2065943cbfb5923c1c65905159658905d135837177e581fb8f65806ebe257c35198577458ed56dbe56f56da22f056abec62568ff7f1567ee6cd5640306856240dff55f952e755df5df855ab6c465592bd7c557f4cd954c1de1053b7a8b553b3d16b53346db95314eaf652f2fea452cc2682528ca242
  | 7, 7 => 0x6eba99336e9f1e276e834bca6e8018a76e34ebde6e1ad9ba6ddedbb86d9b14bb6d5cb0976d483b2f6d45b13a6d2657c06ce170276cd622c66c8fa51c6c4b6e046be1bd3a6bcb63fb6bc490ee6b89f08a6b7c11ab6b58c0516af785736a7ff6686a5eea176a510b386a4f220869f5d2f969d0a4b069c031bf692e70ee68ff5c7d68b561d067f1c0d3679d352a67425c616709aa61668c477066742ba76659a12a663575426554bad1651506a464ffcc4e64e30e64647899486449b75d638147926379a6766347643b633af01163353df46329b29362b43c176284e04362623a3562542af861aa336860d1580460c0164560b58bf5602f2d626001a2b65fd513de
  | 7, 8 => 0x7d303bbe7d1b507d7cfde4937cd372a07c439fcf7c0721267bf841387bf0d3337bc86ac17b25f4ae7ac854af7ab597257ab2c9087aa157477a70b1287a2bfc5d7a2bf4367a148274798a90b27952d2747900675a78f04d3478bca81278925775785a1789781054e377f10ba277d135d07770373f77211a3f76fcab1e76eecc3f76bdf4b976b015da764692e675ee73ad75400898752d381075217693751c82e774f2245d74e1bd61749b9886745a681c73f60c3a73e4c23173b2320a73a4532b73227b8e72e03d9b72b283397290cad572739f547260e48f721cd83371fb25a2714a8ba970cdf07470946692707cee8d706753916f6c29a26f69601f6ebe7769
  | 7, 9 => 0x8bed86128bc68b508bbc73f08b8fda438b7e195e8aef68758ada8b1e8a8bfac78a59f30f8a18c2888a0d10dd89f226db89beef4c8968a0cb89605ac28958e8bc89143e4288f823fd88f300e1886bb2a587ec230287cdddd087ca80ca877c8a9f877910e2872610b88708035286e6840f868cb4248651842c8635a6fc862851b985f48e9f85e99b5485ba4fb985520fcd8549f6d2850f030e84fbb42084a3bdb48492c7cd8458deab83f048fb83d9bb2c83c5bc52838341f4833df903830766bf82ddd8a582dbd05f82121d0d81b633a5806266ad7f97da8d7f5f0e0b7f1797dc7ecd8d627ebd26667ebbf6017e8559377dfd47397db1e1917db173387d356db9
  | 7, 10 => 0x97a5128c97a4f387978d297c974e73179721f5ed9710a45897012b8496fad25696a4b77d968ac1e99680ac86967182b5965f3458965531e6963c456d95fe78aa95bdb66e956125c6955a0898950fbbe39497281e944ede009442b06894355c149409b1f093f42b8d9396353d92ef453392b08ece92a6c201929a9c84928df768928cbda5926d751e9262028d925c0be491bec62691426eab913b5e9f9117715e908ca4449011f58290061e318fe9ad8f8fa4cc1f8fa2db658f9d1d5f8f7fd14d8f6e24048f6680978e7679718e4941358e35cdb08e2374cd8e21c9a38dbfa66d8d92f6958d7f04bb8d6fdaea8d3d413a8d1e3ac28ce77a638c1a6ee88bedc199
  | 7, 11 => 0xa840633ca8098f40a7bb98b7a77ce252a71939e5a6910249a68098aea661d0dfa6395456a62fa927a623790ea5ec25a9a5e4c2a9a4a02823a494c22fa4540600a30f6b7aa309310ca302d5f5a2d8fffaa2d855f3a1c6431fa1807b91a0c045e2a02ef21ba00d2aa29f9262399e6bbe4b9e58572e9e3c45669de9f1209de02fb29db654639da1794d9d61744b9d42bc1d9d3121ea9d2d50bb9ce015509c97dd089c6826aa9c36144f9c10bca49b71391a9aec1f2b9ab0be7a9a95b69e9a81c9ca99ed5e8799d7582f99bbfbc99985b807997d4564996c23f4992721c298fcecee98d839699882e2ec985a34f798553ede984899db98411d81981b7e9297ec88bb
  | 7, 12 => 0xb65f3e8fb644e080b59a84ddb55b444cb559ed2fb52557b8b5195244b4e46fecb4d0d4a4b3feb3cab3f8265db37ef559b32b1ae2b315333eb2dc7687b2572353b253eee6b23cd636b2313513b2306866b22e7c90b210ca3fb1b17014b18cc501b16429bbb0f51e5bb0ec7e1fb0e1dcffb080f6ebb07bc511b04d71d7b0480e0db031ca64b01ae1b0b00d02d1afebec7daf935789af01b67aaef43dc2aee65ee3aec64c0eaebd223cae8d3699ae5c9576ae064aa9adab993dad6e1b08ace974c5ac3ab49dac296414abe5308aabbe6e52ab681b8eaabfa2cbaa8df529aa87c3f1aa3f12b1aa38618daa21bb6da9cb11c2a98c5b5da8e78fc4a8d9852aa8d69abb
  | 7, 13 => 0xc577bfccc576ef75c5690328c4eae2e7c4ac2c82c483e9fec4605fcec44be902c3fbe96fc398766ec3935453c37f968dc3598a1dc34f33b5c33e8ebcc3334588c2d0e2fcc278c27bc21dcfbbc1c6e06ec1c16a74c1a069d3c16463c6c150c440c110cb7dbf46884bbf355634bf01fb40bef4bb49bef1afedbeb2f988be6b5265be4be64fbe2639d5be1fe45dbe107ab6bde1cfb5bddd5bacbdd38f62bd5c9ba0bd3f82f8bcc8e334bc7fbe0dbc5e25f5bc18011abbe49247bba736d9bb3f92c0baa8a17cba45dd7fba2399e2ba1f06b4ba0d3369b97e2118b9782853b8689f9eb85c2f59b84d21e0b837fe7bb81d78f4b7a3f583b713f0d0b69fded2b67d321a
  | 7, 14 => 0xd355d4ffd3152e0bd30f653ad2da325bd27a66b2d229a3e5d1d3f658d1b38e6dd17f337bd1786b89d0e9aa09d0e5095fd0ab600ed0aaf3a4d0a7e5c1d051c79bd010ef66cfe713d2cf9551ebcf84bc20cf6ea403cf446c2dcf2fed9ecf0c769ccef7401acecb96dfcea2794cce8cc780ce6b8b90ce37cadccdfcbe79cdd2d617cdae7ca3cda803e7cd9f30f5cd6ebd58cc0d7bc5cc0b8b0bcbfcbae9cb9cd379cb46a5f8cb26fa2bcae6d7d7ca5eb5a5c9e65a89c9e24337c9d88a90c8e779a6c8d8951dc876c3bec7d3f23bc7ad77bcc7a9b843c7a3ca76c7554d2ec7466283c707ac1ec6ea46f2c62ad07cc61b5c10c5dca5abc5c226a0c5899ec0c57cede8
  | 7, 15 => 0xe575a6eae48a3599e46b0a58e4625a30e4402e8ee3ed24d8e3d420a8e33582dbe2f6cc76e2e94854e2e453e9e25263cde21fca1de1e7aed7e1ccafbce1c2a466e1b94d76e1283faae0d9cf49e088d44de07b344ee044fe41dfeb09c7dfa5c541df7fbf91df71e0b2df41afa0dec9aaa0de7f8515de2834c3ddd7f9c9dd547ea2dd0995b1dcd6712cda8fa153da7890dfda52a0c6da26b2c9d9eccea3d986de71d90de9d2d8e7dfa1d8cf7726d8c00a96d87f9952d8653959d7d8277ed7c2c847d7c0c947d7661623d6fe6644d69e993fd697c1d4d6890d25d64007d5d58ce416d58853add544ef90d4fb6d4fd4f736c8d43f7d82d3c1c38ed3b34341d3a21f4e
  | 7, 16 => 0xf62cba88f5a8ee32f5493ef0f3e60244f39bac49f34c8d5af32a1730f30eb1d1f22186e7f20a7ebff1c31697f1c1f496f17a65ebf15afe71f15a4793f11d8484f109fd47f1027f58f0dd9aa2f0c5c7cbf053c1fdf03d9387f0107b11efeaeca8efdfd1c7efdef6d4ef4adc1aeeab662cee6bbfe2ee570e7dee22ff53ee185818edf5513bede64ad6ed71b5aeecfeda8becbfbceeeca193e2ec879b6fec848404ebc28ee5ebb77889eb94b67beb7a065aeb3fcd10eabceb59ea782c38ea72c195ea643d52ea555bf2ea206746ea04555ae9f23fa9e9d3bc26e9b38944e8f19d4fe878be20e86f0f45e812cbdfe7a75556e73f702ce6a7c695e5c6ac76e5b5122d
  | 7, 17 => 0xffabe638ffa13466ff8b32caff5a28feff3df527ff3992a2fefc312dfefb8721fef2bd64fed37441febf47eefe9afd92fe809189fe12eeb4fe091979fd875a02fd797b23fd75d7f8fce2758bfcb4afe6fc7cb7dbfc3e0176fc3cf275fc3650befbe5e7c4fb74cedafb7259a6fb113ac2fac274d4faa130d0fa4dc81bf9824cb5f9323ec7f9092d95f9091127f80fe67ff7fbcecdf7f3c11df7e68aa8f7c476a1f772bfb1f762f14af734b506f725d631f6f16d4af6e94291f6655c2cf6630474f646c3bff637ead7
  | 8, 0 => 0xdee29a6add9de376bad4da24b6be7634b47be621a1f16def9b34b12188e8d84f7cea112d76f0de3361ca40084aee737942b779a334064f6c2eedfa851e7359ed1729918f0e7e151305169eb0
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x181510c9301604d4214c04c515480300
  | 5, 0 => 0x42441400000000100000042441d583250530000000000004000010d1060000031440800514c82010000042441c0000041108000c93208040000000002000004244040000000004000d421480400000c910900000434418d95210530000000434419813508530100000200400000004110800115100800000000000a0014432480400454842000000000001400000000020008120080000324c82010000010442000324c8200
  | 5, 1 => 0x1000000000060014132080400000c51020000043441c000000000e0000000001c00001091060008521080119520c530000000434418000000000432515320c00000004110800041100800000010910600000100400d9521053000000031440800000811030000000003919320c530000000000008000000000e00000314408000010d107000000000000000109107000004244040000000004000941048000000000004
  | 5, 2 => 0x3800454c42000000021040000000c51020000000001000000811030000010442119520c53000000000001000000c510331455200c0000354402000000000001800000411080000020440c000004110800000434418000000000e00000314408000010d1060000043441c000000000e0000000003800000000020000000000519320c5300000000000200000000001000003244240000000004000d4018800c515480300
  | 5, 3 => 0x38002048020000000424418000010910100000000008000010910100095100800000000000100000104420000010910532515320c0000454c8200000552008000000041108000c5200800004500a201000000000040000000001000000000200000041108000000000380000109101560c9414c0000314c42000014532080400001091060000000001c0000109106000c93208040000000004000c932080400304c0200
  | 5, 4 => 0x231541310c0400001091010014121080000354842000008521080000000000060010531480000000000050014c424814004350c20100000104420000004110800000000008000008110300141320804d952105300
  | 6, 0 => 0x115100800000000000e000c530080000450062000000003840400000000040000000000c00001091060000000001400000000040000000002000001091060000000000c0000000006000c831480000214842000000000002000000000080000042441c00000801000000042441400504c42010000000001000414852000000000000c00000000040011521080000454c42000000000002000314c4200000000000140000000004
  | 6, 1 => 0x2304040000000007000c932080000000000080000021040000001091060000000001000000000080011521080000000c51000000020040000000000080000000001000000000040000000002800000000010000003840400521052000000000001400324c8201001153208000050484200000000000240035484200000c831480000000000020000000001c0000000004000000000200000109107000000384040000109101
  | 6, 2 => 0x24002048020000000000024000290520000000000010000010c1010000000000800000000020000000001c0000000009000c531080000000000060000000000800001051030000000002000000061010014532080400254402000008120080000001091010011532080000000000060000a3148000000000007000000000100000000004000000000100000000004000000000080000000006000004144000000000009
  | 6, 3 => 0x11531080000325052000000000000800000000080000000000c00000000000000000000800521012000009510080000000000070000000000c0000000004000003104000000000007000000000080000000009000000000080031406200000940188000000000007000000000180045440200000000000280000000003000000000100000000004000000000100000000004000000000140000000001000000000240000000002
  | 6, 4 => 0xc00000000090008521080000000000060000000002800001091060000010040000001091010011532080000314c4201000000000100000000000000000000100045006200000c531080400314c420000000000038000000a1000000000001000000061000000041440800000000060000000001c00304c0200000d5100800000000000200105314800000000000a00000424404000000000e000000000180000000009
  | 6, 5 => 0x8000000e1010014841480000000000040000000000c000008410000095100800003500a20000000000020000010510000000000038000000000800000000028004500a201001412108000000000004000d521080000000000030000000001000000021000000000001000000000040011402880400454842010000000002000414022000000000001800454c4200000000000180000000004001153208000000000003
  | 6, 6 => 0x250412000000000002800000000060000041440c00000000040000000000800000000020000000001000000c510200000000010004150420100016414800000000000800000000008000000000d00000000020000000000400000000010000000000200085210804000000a1010011521080400000000020000000000c0000000003000c93208000000000002000000000100000000007000000000280025440200
  | 6, 7 => 0x1000454c420000000000028000000000100012314800000000000a0014831480000000c51000000000001400000000030000000001c00000000090000000002000000000050000000000400000000040000010040000314852000000000001400000000050000000001000454c82000010531480000000000030000000000c0000000004000000000280000000004000000000100000000002000000000200000000006
  | 6, 8 => 0x114018800000000000200115320800000000000800000000010000000000500000314408000000000d0009510080000504c82010000000000400001091060000000001000000000030000000002800104402000010531480000000000020008521080000454842000000000002800454c42000000000000800000000070008521080000304c020000000000028005210520000000000010000000000800000000034000000a101
  | 6, 9 => 0x1400254402000000042441800000801000008521080000000000030000000000800000000010000031440000000000020000000000c00000000070000a018800000000000a000000000180000000002000000000000000000004001412108000045440200000d521080000414c5200000003244040050484201001484348000000000000000000000100000000009000000000140000000002000000000100000041108
  | 6, 10 => 0x32440400058c520000095300800000000000400015028800000000000d0000000001c00000000030000000001000000000070011531080000000000090000000001000000c91010000000000c0000000008000000000040000109106000c53108000010440200000000000100000084100000d521080000511092010009510080000028c52000000000000800001091060000031440c00324c82000000e0288000000000008
  | 6, 11 => 0x1304040045484201000c831480000000000040010942080400001091000000000001000000000030000000002800000c51020008120080000324c82010000030040000000000080000000001400454842010000003840400000000080000000003400000000040000000002800001051020000000000400000000020000000002000001091050000000001000324c82000010531480000414c5200001053148000000000004
  | 6, 12 => 0xd521080000000000060000000001c00000c5102001153208000000000002000c500880000000000050000000000000350062000000000001c000000000400000000010000000000700000000008000000000e0014121080400000000060000041440800000000060000000000c0000000005000000000180021484200000000000080000000009001053148000021484201000000000200000000000001403148000000000008
  | 6, 13 => 0x148404800000000000a0000000001c000000000c0000003840400324c82000008120080000000000040000010040000314c420000000000024000000a1010011510080000000000040000042441c00000c510000000000010000000000d0000e01880000000000010000000000000454c820000000000038000000000500000000010000000000400105314800000000000400115210800004500a201000000484040000000004
  | 6, 14 => 0x20000000000200000000008000480a2000000004840400414c52000011510080000000000040000023040400350062000000000000400001091010000000000400254402000000000001400000000030000000000800000000090000000002000000000040000000001800000000050000002840400521052000000000003800000000080011521080000000000080005502880000000000050000a3148000025440200
  | 6, 15 => 0x240004806200000d4018800000000000e0000043040400504c82010000000000800000000090000000001c00454c820000000000008000010110000095310800001540a2000000000003800000000090000000001800000801000000000000800000c510000000304400000000000400081200800002148420100000300400003548420100000424404000000000600000000008000000000e0000000000800000c5103
  | 6, 16 => 0x34000000000700000000028000000000400000000010000000000a000c5310804000000000600105410804000000000700000000030000000000d0000000000c00001091010000600880000324c8200000000384000045484200000120388000050484200000d521080000514c82000000000003000000000020000000001c0000000007000d401880000000000030000000000800414c52000000000001000504c8201
  | 6, 17 => 0x1400000c510200000000010000000000a0014843480000000000020000001840000029052000000000001800504842000000000002c00000000020000000003800000000040000000001c00000801000000031440c0000000004000000000240002905200000000000280041406200001151008000000000009000c93208000003802200000852108000000000008000000000100045440200000163148000041504201
  | 6, 18 => 0x8000280220000000000008000000000200000000010000010510300109420804000000000200000424414000010d1060009510080000454c4200000941048000000000002000000000180000000003000c1300800000000000400000000010000000000a0000000001000414022000000000000c000000e1000000000000000000000040000000001c0000000009000001004000000000006000004344000035006200
  | 6, 19 => 0x4144000021484200000000000140000000007001151008000000000004000c130080000000000050001231480000000000020000000001800414c520000000000010000000000a0000004840400000000000011521080000000000080000000003800314c4201000000000100000109107001053148000000000005000000000180000000007000000000140035006200000003144080000105103000d51008000000000001
  | 6, 20 => 0xe414800001540e2000000000000c00000000040000000003800000000020000000002000250062000014121080000000c5102001412108000045484200000d5210800000000000d00000000010004350c2010000000001800354402000008521080000000000020000003840400414062000010931480000001091010000000001c000000000d001483148000000000008001140288040000105102000000000240010440200
  | 6, 21 => 0x2c00000000070000000001000454c82010000000000000000000040000000001000001091050000000003400001091010000002840400000000010000000000400354842010014031480000000000040000000001000324c8200000c9320800000000000a000d52108040052105200000c9320804000000e101000000000100035006200001151008000000000002001412108000000000009000000000200000002100
  | 6, 22 => 0x18000000000d00000000008000010910700000000010000000000400000424418002504120000000210400000000000200000424418005048420100000314400004350c20100000000020000000000a00000000020000010c101000000000100000000008000c5310800000000000d00105314800000000000500000028404003544020000000000024000000000a000002144000035006200000000000180000000002
  | 6, 23 => 0x5530080000454842000000000001c000000000e00105008800000000000a0000031440800350062000000000000c00000c51000000000001800000000040000000001400000000070000010440000001051030000032440400000000090011510080000531092010000000003800304c0200000000000100000000004000c9414800000000000200000000014004540a200000000000100050484200000d521080000454c4200
  | 6, 24 => 0x11532080400000000060000a31480000001091060000000002400104402000000000001000048022000000000002000000000040000000001800414c52000011510080000000000030008521080000254c02000011521080000001051000000000001000028c520000000000018002048020000000000018000000000c00000000008003140620000000000010001044020000000000008000000000b000000000140032505200
  | 6, 25 => 0x32040000000c51020000010040000000000040000000001c000000000d000000000100000000003001153108000000000002000000000100000000004000c5008800000000000c000d40188000000000004000000000280000000007000553008000000000008000c130080000000000070000041440000000c81010000000002400000000050000000001800454c4200001151008000000000004000000000140000109106
  | 6, 26 => 0x1000000c51020000000002000304c020000000000004000010910100115210800002148420000000000014000000000200000000020000000000800000000008000000000800115210804000000000400000000028000008c10100109420804000000a1010000032440400504c42010000a3148000000000004000000000180010440200000d42148040000000000000c9320800000000000e000000000140000000007
  | 6, 27 => 0xc932080400000000020000000002000000411080000031440800000000050014831480000000c5102000d510080000454c82000000031440800504c8201000000000100000000008000000000140021484201000004144080000000006000162148000000000004000c531080000000000020000000001c00000000020000000001800000000010000000001400001091010000000001c0021484200000000000080045006200
  | 6, 28 => 0xd5210800000004010000000000014000000000d000c531080000039052000000000001400350062000008120080000000000040000000001000254402000014532080400314c42010011532080400520c52000000000003400521052000000000002800514c8201001153208040010440200000004244040000000008001484148000000000003000000000100000000009000000384040000000009000c50188000041485200
  | 6, 29 => 0xa4148000050484200000000000100000109107000000000140000000007000d4018800000000000e0000000002000000000020000042441c000000000600016414800000000000900148314800000000000a0000000003800000c910100000100400004350c2010011532080000001091060000000000c00000000060000000001800000000020001231480000001091060000000000c000000000200000000010004350c201
  | 6, 30 => 0x324404004350c201000000000100000000008000000000200000000005000003144000000109107000c520080000048c52000001621480000000000040014131080400000000040000000001000001091060000000001c005210520000094018800000000000200000000038000000000b00000000030000000000e0000000002000504c8201000951008000000109101000000000180000000005000000184040000000008
  | 6, 31 => 0x1800000000080000031440c000000000600115210800003544020000000000010000000000b0000000001800415042010009510080000454c420000000000024000000000a0000000001000000c51020000000000c00354402000000031440000314c4200000000000100000000004000000000240000000006000c500880000000000090000000001400000000000000000000c00415042010000000001400000c5103
  | 6, 32 => 0x1000000000040000000001000354842010000000004000000000030000000001000000000040000000002000425082010000000002000514c82000014131080400000000020000000002c003544020000000214404000000000c0000031440000000000020000000000400504c42010000000000800500c52000000000001c00204802000000031440400000000080000000003800314c0200000000000280000000008
  | 6, 33 => 0x1000000000070000000000800000000080000043040400314c420000000000008000380a200000d4018800000004c101000c130080000000000010000000000800000000040000000001800001091010000000001c00000000040000a01880000314c42000000000002400414c52000000000000c00000000000000000001400304c02000000043040400204802000000003840400424c5200000000000200035006200
  | 6, 34 => 0x11532080000000000070000000001c00000c51020000000002c0000000008000d510080000000000060000000004000414c5200000002004000000000007000c531080400058c520000000000034000380620000000000020000000e101001412108000035484200000c5214800000000000500000000018000000000f000000000180000000009000000000140000000005000004244040000000004001052148000000000004
  | 6, 35 => 0x1094208040000000008000000000100035006200000000000280021484200000000000200000000009001052148000000000004000000000100000000008000553008000035484201000c13008000000000003000004144000000000002000d521080400000000030000000001000324c82000000000002800000000020000042441c000000000400000000020000000000a0000000001000104402000000000001c0000000002
  | 6, 36 => 0x1c00000000050000000001000028022000000000000400000000030009401880000324c82000000000000c00028c52000000000001000104402000010531480000254402000014121080000354842000009510080000154802000000000001400000000050000000000c000010d1070001202880000000000080000000001000000000040000000001800000000050000042440400000000080000000001400314c0200
  | 6, 37 => 0x115210800000000000a00000028400000000000400141210800003548420000000000018000000000500000000038000000000e000000000080000000002000000000100000000004000953008000000000008000d52108000000000009000000000080000000008000c53108000000109101000004304040021484200000d401880000000000050000000002000504842010000000001c00000000080000000003800324c8200
  | 6, 38 => 0x100000084100000d510080000000000040000000000400000000080000000001000000000050000000001c0000000008000c932080000324c820100000000010000000000800041100800000000000700000000010004544020000141210800000000000e00081200800000000000500115320800000000000600000000014000000000c0009531080000000000090000000002000000c5102000000000040000000001
  | 6, 39 => 0xd5100800000000000600000000010000000000600115210800000480e2000000000002000304c020000000038404000000e1010008120080000520c520000000028404000000000400000000028000000000d0000000003800454c42000010531480000514c820100016414800003500620000012018800000000000e00000000008000000000500041100800000010910100000000010000000000e001053148000021484200
  | 6, 40 => 0xa414800000000000400000000004000000000800000424404000010d10100000000010000000000600000000018003500620000000000018002544020000000000018000000000a0000000001000000000060000000000800000000010000000001400000000080004110080000000000020000000002000000000040000000000400000c5102000000000140045440200001484048000000000002001484148000000000001
  | 6, 41 => 0x10501880000314022000000042441800000000040000000000400000000040000000000800414c5200000953108000000000008000c93208040000000007000c531080000314852000000000002000000000070000000000800001091070000000001000000000050000000000800000000000000000002000000411080000000001000000000030000042441c000000000600000000038003148020000148434800000000000e
  | 6, 42 => 0x1000204802000000000003400000000040000000001400000c51030000021440000048022000014c4248040000000008000000000100000109107000c520080000214842000000000000800000000060000e414800000000000a000d510080000500c5200001453208040000000008001153208040000000008000c50188000035440200000000000380000000008000000000200000000003000001044200000000003
  | 6, 43 => 0xe008800000008c101000d4018800005210d2000010931480000504842010000000001000000000060014131080400001091070014121080400000000030011532080000304c02000000000002000154802000000000002000018022000008120080000454c42000000000001800354842000000000001c00000000030014532080000000000050000000001000000000020000000000c003148520000000000028004350c201
  | 6, 44 => 0x1c002544020000000314400000000000300081200800000000000700000000020001540e2000000000001c00000000100000000000c00414c520000115310800000000000600000000028000000000200000000010000000000600000424404000000000800000320404003540a2000000000000c00000c91000000000001000000000080000000002400504c82010008120080000000121000000042441c00324c8200
  | 6, 45 => 0xc932080000000121010000000002000000000080000000000800354402000000000002400314c42000000000001800000000030000000001000001051000000013040400000000010000003840400000000040000000001800000000100000000002c000000a10100000000014004500a2010000000001400000000040000000000800000000040000000002000000c5102000000000080000000002000000000100000000004
  | 6, 46 => 0xc000000000e0008521080400000000060000000001000000000090010531480000000000040000000000800058c52000000000003000000000010000000000c00414c52000000000001000254402000000000001c000000000e0000000002c00000000040000000002000000000020000000000c000010d1010000000002000154c0200000000000140020480200
  | 7, 0 => 0x14000000000200000018400000000a10000000310400000000000b0000010040000000c51000000000000800000000030000000000c000008010000000038400000000000400000430404000008410100000310400000000000e0000000002c000000e10100000000020000000a10100000000004000000000200000000004000000000200000000018000010910000000000020000000000b0000000001400000c5100
  | 7, 1 => 0x8000008110000000000004000000000e00000000010000000000700000008400000000000d00000018404000000000600000028400000008510000000000034000000000000000000010000000610100000310404000000000e0000000000400000000040000000003400001051000000041440000001091000000021040000000c510000000000008000000610100000000010000000a100000000000040000006100
  | 7, 2 => 0x38400000000a1000000000001000000000030000001840000000000070000040440000000000080000000001400000000030000000000400000c11000000000000800001091000000032440400000c91000000000000c00000000030000030040000001081010000004840000000000100000032440400000000060000000000c00000000020000000001400000000030000031440000000000040000000001c0000000006
  | 7, 3 => 0x1400000000070000000000c00000000030000041440000000c11000000000001000000000030000000840000000851010000030040000000c41010000021040000000000050000031440000000c51010000000002400000851010000000001800000000010000031040000000000030000000001400000c510100000000018000000000500000038400000000a10000000314400000010d100000000000240000105100
  | 7, 4 => 0x1400000000050000041440000000000080000000000800000000010000000001000000000080000003840000000c510000000210400000000e1000000000001c000010d10000000000000000008010000000000020000000e10000000000014000008410000000000004000000610000000000008000000000500000000004000000e10100000424404000000a100000000000140000000003000000184000000101100
  | 7, 5 => 0x434400000010d1000000000001000000000020000001840000001091010000000000800000000040000000002c00000c910000000000008000010c1010000004840000000000000000021040400000000040000000000800001011000000000000800000000020000043040400000000030000021040400000c11000000000000c00000000050000000001800000000080000031440000000c0100000000084000000000001
  | 7, 6 => 0x28400000000000000000430404000000000100000310400000000000400000000008000010910000000048400000000000a0000000001400000000010000032440000000000050000000001800000121000000000001400000000070000041440400000000040000000000c000000000300000000014000000e10000000000010000010410100000000018000000000200000028400000000000900000000004000000e100
  | 7, 7 => 0x28000010510000000000008000000000400000000000000008010000000000018000000000900000000010000008410000000000008000000000800000414400000000000500000000018000000a10000000000018000000000000000000008000000610000000210400000000e10000000018400000000000500000000004000001210100000008400000010d100000000000180000012101000000184000000000007
  | 7, 8 => 0x40440000000000050000002840400000000080000000000800000000010000000001400000000000000032440000000121010000000000800001051010000000000c00000021000000000000400000000020000041040400000121010000000001400000000020000000002800000c810100000008400000000610000000000034000000000300000000024000000000100000324400000001210000000214400000000a101
  | 7, 9 => 0x3840000000000010000000001c000010910000000000008000000a10000000310400000000000400000008400000000000400000000004000000a1000000000000800000000010000040440000000000080000000000000001091010000000002800000121010000021440000000c11000000010440000000000060000042440400000c0100000003004000000000006000004144040000081100000000184040000000003
  | 7, 10 => 0x800000401000000000002000001091010000001840400000000070000000002800000121010000000002400000c91000000000000400000c410000000000004000010910100000104400000001210000000000024000008510000000000024000000000100000028400000000e1010000020440000000c010000000414400000000610000000028404000000000100000000010000000000400000210404000000e100
  | 7, 11 => 0x32440000000c910100000000010000000e10000000048400000000000b00000214400000000e10000000000038000000000600000000020000000a1000000000840000000061000000043440000000000030000000002000000000030000000001c00000000010000000001800000061000000000000c00000000020000020040000000000010000030040000000000040000001840000000000010000032040000000c4101
  | 7, 12 => 0x400000000010000000000c00000000050000000840000000000040000030440000000000060000002840000000000020000030040000000c41000000000000800000000060000000001c000010d1000000032040000000401000000000002c0000000004000000384000000002100000000000140000000007000000284000000041100000003204000000105100000000000080000105100000000000100000081100
  | 7, 13 => 0xc00000c81000000010040000000c810100000000004000000000200000038400000000000e0000000000800000c81010000000002000001091000000000000800000000040000000000800000061010000002840000000021000000041440000000000040000001840000000000060000000003400000851010000000000800000000010000000001800000000040000000000800001011000000021040000000c5101
  | 7, 14 => 0x314400000000e1000000021440000000c910000000000008000001210000000430404000010d1000000021040400000c91000000001840000000c9100000000000280000000000000000484000000000005000000000280000000002000000000080000080100000000000040000000005000003244040000000002000000000080000002100000004344040000000001000000000180000000008000000000040000000006
  | 7, 15 => 0x800000c010000000028400000000000600000424404000000e10100000018400000000000800000000018000000000300000000014000000000100000000004000000e10100000000014000000000000000000020000000000900000000018000000000200000214404000010d1010000000001400000000080000000000800000c51010000000000c00000801000000000000400000c4100000002004000000000004
  | 7, 16 => 0x8000008410100000000014000000000700000028400000008010000000000010000000000400000038400000000000400000018400000000000b0000000840000000000010000000002400000000010000000001000000000070000040440000000c510000000000004000010910000000314400000010d1000000000001400001011000000010440000000c41000000000000c00000c110000000204400000000000d
  | 7, 17 => 0x800000000040000000001000000000030000000000800000c81000000031440000000061000000010040000000000060000031440000000000090000000840000000000020000000001000000000070000000001000000000070000000002400000000030000000001000000000020000041440000000021000000042440000001091010000000000c00000851000000000001c000000000600000000028000010c101
  | 7, 18 => 0x40440000000000090000000001800000000080000031040000000841000000000001c00000c510000000304400000010910000000000020000000000600000300400000000000a0000000000000000c41000000000001c00000000040000042440400001011000000000840000000000010000000000c00000000080000003840000000000040000000000c00000851000000000000c000000000700000200400000010d100
  | 7, 19 => 0x42440400000000090000000000c00000000020000000001000000000020000000000800000c110000000314400000000e10000000028400000000000600000300400000000610000000420404000000000300000000010000000000000000000020000001210000000000004000000000300000028400000004110000000200400000000610000000028404000000000300000000004000008110000000414400000000000d
  | 7, 20 => 0x424404000000000a00000000010000010d10000000310400000000000a00000000010000000610000000000018000000e10000000000008000000000400000414400000000000400000414400000000210000000008400000010d10100000210400000000000300000200400000000e10100000434404000000000300000000010000000a1010000000000400000021000000000000c0000000003000000000080000101100
  | 7, 21 => 0x31440000000c81000000000001400000000020000021040000000061000000000001000000000030000042440000000c110000000000010000000000700000000008000000000400000000004000000000e00000300400000008510000000000010000000000800000424400000000a1000000000002400000c51000000000001c000000e1000000001840400000c81000000010040000000000040000000002800000c5100
  | 7, 22 => 0x28400000000000a00000424400000000000100000000008000008110000000000010000000000800000424404000000a1000000003840000000000080000000000c000000000900000000034000000000300000038400000000000100000000028000000000900000000008000000000800000000000000000000600000028400000000000600000000014000010d100000004144000000000008000000000080000101100
  | 7, 23 => 0xc00000c010000000000014000000000a00000310404000000000300000414400000000a10000000000004000000000700000000014000000e10000000000024000000000400000008400000010d10000000018400000000000b00000200400000000000700000000018000000000b0000031440000000801000000000000800000841000000000000400000c8101000001044000000000004000000000040000000005
  | 7, 24 => 0x31440000000000090000000000400001091000000030440000000851010000000002000000c810100000300400000000000200000314400000000e10000000008400000000e1010000042040400000000030000010040000001081010000000001000000000030000021440000000000060000000840000000851000000000000400001011000000020040000000c81000000010040000000411000000010440000000c1100
  | 7, 25 => 0x18404000000000100000324400000000610000000000020000010510000000038400000001210000000000000000008410000000000018000004110000000000014000000000100000000020000000000700000204400000000000600000038404000000000400000424400000000000500000000020000000a10100000000014000010110000000038404000000210000000214400000000000400000000004000000a101
  | 7, 26 => 0x48400000000e10100000000040000000000400000100400000000000000000000018000010d1000000000001000000000050000021440000000000050000001840000000000050000041440000000000060000000000c00000811000000032440400000000030000031440000000000050000010440000000c5100000000000280000081100000000384000000000002000000184040000104101000004344000000000007
  | 7, 27 => 0x1400000411000000031440000000c81000000010040000000000020000030440000000811000000000002000000000050000030040000001011000000000001800000c51010000002840000000c41000000000002000000000020000030440000000000050000000001800001051000000000001c00000c01000000000003400000000010000000002000000c91000000003840000000c8100000001004000000000004
  | 7, 28 => 0x41440000000000060000041440000000c01000000041440000000000040000000002800000000060000000002400000c41010000021040000000000010000003840000000c410100000000004000000a1000000000840000001051010000000000c00000c910000000410404000000e1000000000000c000000000a00000000008000000000e00000000018000000000a000000000080000101100000000000000000000004
  | 7, 29 => 0x18000000000000000000014000000000100000000028000010d10000000414400000000000800000038400000000000800000320400000000610000000000024000004010000000000008000000000800000000008000010d1000000000840000000000080000000003400000c51000000000001000000000050000043440400000851000000001840000000000060000032040400000c9100000000484040000000002
  | 7, 30 => 0x310400000000000400000314400000000e10100000000004000000a10000000000000000000000400000000004000000000500000000010000000000700000000000000000a1000000004840400000411000000001840000000000040000000002c000001210000000204400000000000e0000000000400000000020000021440000000021000000002840400000000030000000001c000000e1000000000001c00000c4100
  | 7, 31 => 0x10440000000c91000000031440000000021000000000000800000000040000004840000000c81000000010040000001051000000000002000000000010000000840000000000040000002840000000841000000000002000000061000000000003400000c51000000000000c00000000020000041440000000c810000000000028000010d101000000000040000000009000001044000000000001000000084000000081100
  | 7, 32 => 0x400000000010000032440000001081010000000002000000000010000031440000001051010000000000c00001041010000000002000000061010000041440400000000060000002840000001041010000031440000000851000000000000800000000080000032040000000061000000010040000000000010000001840400000000050000021440000000c11000000000840000001051000000000000800000c4100
  | 7, 33 => 0x314400000008110000000304400000000000500000000018000004110000000000018000000610000000204400000001210100000000018000000e10100000000024000008010000000000000000000a10100000104400000000a10000000000010000001210100000000020000000000400000000014000000210000000000008000008110000000000010000000000b000003244040000000005000000000200000000004
  | 7, 34 => 0x210400000000000200000320400000004010000000000000000000000200000048404000010510000000324400000010910000000200400000001210100000000004000000000700000414400000000a1010000000000400001051000000000000800000000040000000000c000000a1010000000000c00000851010000001840400000000050000000001c00000841000000000002800000c51000000000001000000c5101
  | 7, 35 => 0x1400001091000000000000400000000090000000001000000000080000030440000000000030000000000800000c5100000003204000000000006000001004000000000008000004144000000000008000004204040000000001
  | 8, 0 => 0x1000000000040000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000040000000000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_9 roots_9 8 s ws hint
  | 1 => checkCutEntry dom_13 roots_13 7 s ws hint
  | 2 => checkCutEntry dom_15 roots_15 6 s ws hint
  | 3 => checkCutEntry dom_16 roots_16 6 s ws hint
  | 4 => checkCutEntry dom_17 roots_17 6 s ws hint
  | 5 => checkCutEntry dom_18 roots_18 6 s ws hint
  | 6 => checkCutEntry dom_19 roots_19 6 s ws hint
  | 7 => checkCutEntry dom_20 roots_20 6 s ws hint
  | 8 => checkCutEntry dom_21 roots_21 5 s ws hint
  | 9 => checkCutEntry dom_22 roots_22 5 s ws hint
  | 10 => checkCutEntry dom_14 roots_14 5 s ws hint
  | 11 => checkCutEntry dom_10 roots_10 5 s ws hint
  | 12 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 13 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 14 => checkCutEntry dom_24 roots_24 5 s ws hint
  | 15 => checkCutEntry dom_11 roots_11 4 s ws hint
  | 16 => checkCutEntry dom_12 roots_12 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_25 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_22 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_25 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_25 == dom_25) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_25 goalM u ys) : RunD dom_25 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_25 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
theorem z5_8 : ∀ i, 8 ≤ i → i < 11 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 8 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := range_split z5_0 (z5_8)
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
theorem z6_152 : ∀ i, 152 ≤ i → i < 157 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 152 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 157 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (z6_152)))))))))))))))))))
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
theorem z7_168 : ∀ i, 168 ≤ i → i < 170 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 168 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 170 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (z7_168)))))))))))))))))))))
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
theorem z8_24 : ∀ i, 24 ≤ i → i < 27 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 24 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 27 → Z 8 i = true := range_split z8_0 (range_split z8_8 (range_split z8_16 (z8_24)))
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
  scr dom_25 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_25 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_25 roots_25 goal_25 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_25 goal_25 := by
    have h0 : isConstB dom_25 goal_25 = false := by decide +kernel
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

end S_25

theorem low_25 : Lower dom_25 roots_25 goal_25 10 := S_25.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_25_bits : ∀ r : Fin 64, roots_25.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_25_lt : ∀ r : Fin 64, dom_25.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_25 T)
    (hlow : Lower dom_25 roots_25 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_25, Avail mask256 roots_25 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_25 hfan 0 roots_25 roots_25 rfl hsup0
  set out := (execN C.gates roots_25).getD C.output 0
  have hout : out &&& dom_25 = T &&& dom_25 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_25_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_25 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_25_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_25).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_25)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_25.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_25 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_25).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_25 &&& mask256 = dom_25 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_25 = T &&& dom_25 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_25, hd63, hout]
  have hnc_m : ¬ IsConst dom_25 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_25 roots_25 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_25, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_25 roots_25 0 roots_25 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276809952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_25.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_25 10 hT6 (by unfold IsConst; decide) low_25

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [7, 5]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.or, [9, 3]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [11, 4]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [13, 2]⟩, ⟨GateOp.and, [14, 10]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_16977_aux

theorem PEqualNP.Outside.L_meta_16977 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276809952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4276809952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_16977_aux.wit, PEqualNP.Outside.L_meta_16977_aux.wmono, le_trans PEqualNP.Outside.L_meta_16977_aux.wsize (PEqualNP.Outside.L_meta_16977_aux.lower s hs), PEqualNP.Outside.L_meta_16977_aux.weval⟩
