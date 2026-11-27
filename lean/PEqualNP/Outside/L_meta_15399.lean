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

namespace PEqualNP.Outside.L_meta_15399_aux

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

def dom_0 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_0 : Nat := 0xaa88a080a888a000
def roots_0 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(3, 19), (5, 13), (7, 15), (7, 23), (7, 39), (9, 13), (11, 15), (11, 27), (17, 19), (21, 23), (21, 29), (25, 27), (25, 29), (25, 57), (35, 39), (35, 51), (37, 39), (37, 45), (41, 45), (41, 57), (43, 47), (43, 59), (49, 51), (49, 57), (53, 55), (53, 61)]
def r1sG : List Nat := [3, 5, 7, 7, 7, 9, 11, 11, 17, 21, 21, 25, 25, 25, 35, 35, 37, 37, 41, 41, 43, 43, 49, 49, 53, 53]
def r2sG : List Nat := [19, 13, 15, 23, 39, 13, 15, 27, 19, 23, 29, 27, 29, 57, 39, 51, 39, 45, 45, 57, 47, 59, 51, 57, 55, 61]
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
  | 2, 0 => 0x78d83c34
  | 3, 0 => 0xac1f0b2752c99e0d18d6ab320e9bd6fe
  | 4, 0 => 0xb2136df5aad2a5e7a54b3fd36fad59526d5d3bc7619e078459448a854ced500347a034fe153f3474089d877d0592950102dfc1ef
  | 5, 0 => 0xe2d3b7c9e2b56fb276814464534137d94ced50034736fb2941c5084830f1064f2a9a5d9a2319d16a15e8d6110e619fdd0672c8d5
  | 6, 0 => 0x4ced5003
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x8888888888888888888888888888000088888888000000008888000088880000808080808080808022222222222222220a0a0a0a0a0a0a0a00000000aaaaaaaa
  | 0, 1 => 0xaa88aa8888888888aa880000aa880000aa00aa00aa00aa00aa000000aa000000a8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0a0a00000a0a00000a000a000a000a000
  | 0, 2 => 0xaaaaa0a000000000aaaaa000aaaaa000aaaa8888aaaa8888aaaa888800000000aaaa0000aaaa0000aaaa000088880000aaa0aaa0aaa0aaa0aaa0aaa000000000
  | 0, 3 => 0xaaaaaaaaaa00aa00aaaaaaaaa0a00000aaaaaaaaa000a000aaaaaaaa88888888aaaaaaaa88008800aaaaaaaa00000000aaaaa0a0aaaaa0a0aaaaa0a0a0a0a0a0
  | 0, 4 => 0xaaaaaaaaaaaa0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x183463
  | 3, 0, 0 => 0x4d0207448d28547d33ca47993474
  | 4, 0, 0 => 0x144cd287569634a1d5a38d287575334a1d5b4cd287569334a195a64d247569334a1d5a54d28455d334a1d5a4cf34a569334b0d5c4cd2855
  | 5, 0, 0 => 0x69334a1c0669344d287669334b287601a4cd282501a4cd287569334a1c4669334a24766994cd287669334a1c1669334a1c5669334c287601334a1c0581a4cd2876
  | 6, 0, 0 => 0x1a4cd2875
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
  | 0, 0 => 0xc3037430c0000c300000000000000073cf3f223f3e784003fff
  | 0, 1 => 0xf303740038000f0e380003800ccf1b7f03061ec001800000000
  | 0, 2 => 0xf0c0003c03f00fc3ff77f0c000f00fc03c00000cfcfbfb3f0000
  | 0, 3 => 0xfffe383ffc600fff0003ffc0ddfff0303ffc000f0cfc7bc3061e
  | 0, 4 => 0x3ffff00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x5c72f7571cb995c70041608b8944509728e34223a2a604001fef
  | 0, 1 => 0xfffaf77e8bf89af8f39aa83c80ddf7fff17567ec005822161466
  | 0, 2 => 0xfff8043febfeffe7ff77f9e010fa2fe27e8ab89efdfbfbbf6010
  | 0, 3 => 0xffff3dbfff618fffd1dbffebddfffa353ffe010ffffffffff67e
  | 0, 4 => 0x3ffff99
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

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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

def dom_1 : Nat := 0xff000000
def goal_1 : Nat := 0xe8000000
def roots_1 : List Nat := [0xaa000000, 0xcc000000, 0xf0000000]

namespace S_1
def pairsG : List (Nat × Nat) := [(25, 27), (25, 29), (26, 27), (26, 30), (28, 29), (28, 30)]
def r1sG : List Nat := [25, 25, 26, 26, 28, 28]
def r2sG : List Nat := [27, 29, 27, 30, 29, 30]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x63e993a8
  | 3, 0 => 0x63e993a8
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000cc00000000000000aa000000
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_2 : Nat := 0xff000000ff000000
def goal_2 : Nat := 0xea000000e8000000
def roots_2 : List Nat := [0xaa000000aa000000, 0xcc000000cc000000, 0xf0000000f0000000, 0xff00000000000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00000000000000, 25, 57)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xff00ff00ff00ff00
def goal_3 : Nat := 0xea00e000e800e000
def roots_3 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff000000, 11, 27)] (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0xffff0000ffff0000
def goal_4 : Nat := 0xeac80000e8c80000
def roots_4 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 6 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0xff00ff00
def goal_5 : Nat := 0xe800e000
def roots_5 : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000, 11, 27)] (by decide +kernel) (by decide +kernel) low_1

def dom_6 : Nat := 0xffffffff
def goal_6 : Nat := 0xe8c8e000
def roots_6 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_6 : Lower dom_6 roots_6 goal_6 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00ff00, 5, 13)] (by decide +kernel) (by decide +kernel) low_5

def dom_7 : Nat := 0xcc00cc00cc00cc
def goal_7 : Nat := 0xc800c000c80000
def roots_7 : List Nat := [0x88008800880088, 0xc000c000c000c0, 0xcc000000cc0000, 0xcc00cc00000000]

namespace S_7
def pairsG : List (Nat × Nat) := [(3, 19), (6, 22), (6, 38), (7, 23), (7, 39), (18, 19), (18, 22), (34, 38), (35, 39), (35, 51), (50, 51), (50, 54)]
def r1sG : List Nat := [3, 6, 6, 7, 7, 18, 18, 34, 35, 35, 50, 50]
def r2sG : List Nat := [19, 22, 38, 23, 39, 19, 22, 38, 39, 51, 51, 54]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_7.map (· &&& dom_7)
def goalM : Nat := goal_7 &&& dom_7
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xf53251d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc00cc0000000000cc000000cc000000c000c000c000c00088008800880088
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_7 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_7 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_7 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
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

def dom_8 : Nat := 0xcccccccccccccccc
def goal_8 : Nat := 0xc8c8c0c0c8c8c000
def roots_8 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc00, 6, 14)] (by decide +kernel) (by decide +kernel) low_7

def dom_9 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_9 : Nat := 0xe0c0e0c0e0c0e000
def roots_9 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0xff00ff00ff00ff
def goal_10 : Nat := 0xc800c000c80000
def roots_10 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc, 17, 19)] (by decide +kernel) (by decide +kernel) low_7

def dom_11 : Nat := 0xffff0000ffff
def goal_11 : Nat := 0xe0c00000e000
def roots_11 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10

def dom_12 : Nat := 0xff00ff0000000000
def goal_12 : Nat := 0xea00e00000000000
def roots_12 : List Nat := [0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000]

namespace S_12
def pairsG : List (Nat × Nat) := [(41, 45), (41, 57), (42, 46), (43, 47), (43, 59), (44, 45), (44, 46), (56, 57), (58, 59), (58, 62), (60, 61), (60, 62)]
def r1sG : List Nat := [41, 41, 42, 43, 43, 44, 44, 56, 58, 58, 60, 60]
def r2sG : List Nat := [45, 57, 46, 47, 59, 45, 46, 57, 59, 62, 61, 62]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_12.map (· &&& dom_12)
def goalM : Nat := goal_12 &&& dom_12
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xf7713b09
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000f000f00000000000cc00cc0000000000aa00aa0000000000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_12 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_12 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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
  scr dom_12 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_12 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_12 roots_12 goal_12 4 := by
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

theorem low_12 : Lower dom_12 roots_12 goal_12 4 := S_12.noCircuit

def dom_13 : Nat := 0xffffffff00000000
def goal_13 : Nat := 0xeac8e0c000000000
def roots_13 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00ff0000000000, 37, 45)] (by decide +kernel) (by decide +kernel) low_12

def dom_14 : Nat := 0xffffffffffffffff
def goal_14 : Nat := 0xeac8e0c0e8c8e000
def roots_14 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_14
def pairsG : List (Nat × Nat) := [(3, 19), (5, 13), (6, 14), (6, 22), (6, 38), (7, 15), (7, 23), (7, 39), (9, 13), (10, 14), (11, 15), (11, 27), (12, 13), (12, 14), (17, 19), (18, 19), (18, 22), (20, 22), (21, 23), (21, 29), (25, 27), (25, 29), (25, 57), (26, 27), (26, 30), (28, 29), (28, 30), (34, 38), (35, 39), (35, 51), (36, 38), (37, 39), (37, 45), (41, 45), (41, 57), (42, 46), (43, 47), (43, 59), (44, 45), (44, 46), (49, 51), (49, 57), (50, 51), (50, 54), (52, 54), (53, 55), (53, 61), (56, 57), (58, 59), (58, 62), (60, 61), (60, 62)]
def r1sG : List Nat := [3, 5, 6, 6, 6, 7, 7, 7, 9, 10, 11, 11, 12, 12, 17, 18, 18, 20, 21, 21, 25, 25, 25, 26, 26, 28, 28, 34, 35, 35, 36, 37, 37, 41, 41, 42, 43, 43, 44, 44, 49, 49, 50, 50, 52, 53, 53, 56, 58, 58, 60, 60]
def r2sG : List Nat := [19, 13, 14, 22, 38, 15, 23, 39, 13, 14, 15, 27, 13, 14, 19, 19, 22, 22, 23, 29, 27, 29, 57, 27, 30, 29, 30, 38, 39, 51, 38, 39, 45, 45, 57, 46, 47, 59, 45, 46, 51, 57, 51, 54, 54, 55, 61, 57, 59, 62, 61, 62]
def mpG : Nat := 0xfffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_14.map (· &&& dom_14)
def goalM : Nat := goal_14 &&& dom_14
def NN : Nat → Nat
  | 3 => 2
  | 4 => 41
  | 5 => 270
  | 6 => 720
  | 7 => 405
  | 8 => 23
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xf825b540697b375d
  | 4, 0 => 0xe141fd41dd7ce802d0d76f55c720c60db797e2b5ad447d50a43fef58a018c9ee90b2822987b5d02978431ecb578dbea85412d3015200b22c48170aa747f25018439eb2fc434e85a440b1dfd33d92d1363c92e11a35f2df6130529b2d2de16be128628742282bcad9262890851e4647421bc41b4a1ad34f611757b29f161e19e41404a8740fe1a0b00c087a60078f52d80724b7c80635c22b0399279d02f3e494002e8354
  | 5, 0 => 0x281a6a4328173bdd280064ef2791abf2270e20b12706ff8825edd45b25e8261b25a9d30124d67c27241eab422340c867232ee1702265286521b06328218ce75e2151b8be21488ce01e98bdc11e29d4931db4a4271d7460e11a761be718c37efc1882c6cf1824717d16cd3fe516a4004a15a6ffdb1544916c1525469b13c101fd12cc1c551244e177124434211202bfe710b8f40f0f1856960ee0d70d0e8094730e191fab0d29dbbb0c4bdce50bcfb3fa0ab93c020a8376200a65bc300a34a5740a27f3aa0a1e04840960f61e091a132f07b31bbb06f5bc8406a1171605c96afd047f2ce6046f8a0203ee7b9d0235b100019eeec40141a004012855df00abd848
  | 5, 1 => 0x4cac6da54c93d4734bfb957a4bf9c6274a71890d494cd94448ecbb9d476850d8474d6cd046af769a461b5c19459c77c3441f1f6842c49da2427e34ef421e621441e96fc341bcc69841b382f3419bebfa4101887b409bb266405414153ff513d53fc4defb3ed34f223cde19613aa565e83a0ef55238db6caf38becf7838aa8a3b38a3b6003885dd5b37f11b4c37e7479337ad1f9c3738488636baa4293668cae436601741364e56b03624a4d635c2f1d935a956d034fe968831be6cad30ef32ec30599af92fe7b69c2f86aebc2f3c2c452f2b90fd2f115a972f058bb02ecd01b42dfd3b902c8a8e7a2bfd49b32bc11edb2a0f2d46298bd0ea287591982873acb2
  | 5, 2 => 0x7d6a3e7e7c5dc37b7b34cd0f7b0c25577aff52b479b692a479857dee7924005c7903c4e978f3399376d58b90764c936475bda65e757ca731754c27f874de46bd742c198b739d7a9e73776b547377369172f8e6de72e18a9b7264af1e724633b371a3faaf7086143f6f2611c96f00fbc36d0d2f766cf96e326b62c33d6ac9d4ae69e7c97d68a623dc6834f5c5682d2d79675a114665d4792465102aa1623d06ec61d7af80609a30955f07899d5ef091f65e9b3ccc5de38ba85de350f95d499fea5c7631395b20db4559e4d35a59be1e2e58e9dee85871d44e5538800953ce7fa652c5d2e751d4aa4f51d1d295518a3b31510af6a14e87bebc4e7e9a394d294445
  | 5, 3 => 0xcaa3cd5dc89d02d5c809920cc785cbf7c7146088c62fa96fc5fa79bdc515821cc16ba852c14532f3be469854be306bb3bd536e3abc6bc99cba95c07eb77f00fab566e894b38b4404af8b401caf407f5aada5e64ba9d2034fa999cad5a993afaca73d73d6a670e323a5389490a394c35da2721ea6a19a38829e82f3649d5462e39ca06a5f9b12cfc59af3cbb9999741a29947bb24980781bd9591f3be9466c7cf931fcd5d92b0498591d007099134c5009011f0d38b8d065a8b0ccb548a9dd38889234f8488df30a888d963dc886f013b87d430d387b2993d872961db840714eb83ecdae883ba10d7838c0b9e81d7f28c7f3c8c247efc7a197ebbc1417df74d94
  | 5, 4 => 0xfead2cf8ee247a42e543b7dae3cc6250e3bb4d93e3111b61db37e196d8dddb4bd73f8adad376d5e9d3329addd07e8131cf4c7316cf292b3d
  | 6, 0 => 0xcabde0a0c7bcab90c710b750c59d4660c3c687c0c2c14070c18c4240c0930a10bd800270b7002330b56888f0b28c1c80a6426b20a3d884a09fb12fd09a32801099089cb0955e8780919997808f0123c08d01fc908ba381d08b08166086010a2085f7171080a8eb707ae59bb07a676fd075ae443074eba94072852b906f72c6106dc984206a693b50681af19067d884b0665520c06612d3f06457cb9060a822405b8895305a509e6058e95d30588cebe055afcf404c5847804963a7b03d8385d03c4e71303b5fb4003ae4e990380978b03087e0402fa793702975eb9024ad8f9019c9fad015437cd01521d0b012c70a700e6aadd00e30216009787b3006c2684
  | 6, 1 => 0x1b55df541b52bdbb1b3c1cc21b3b5e1c1b27d2611b1a2ca91b1700c91a7036271a624c741a548add1a2594481a0ef3fa1a02b75719ba301a18af851c187444e41832b48e17aa7313174a0ecc172c136016c59e4d16b01e541611817415ef946d15ea9fee15e9498b159e48891596d48d1535fac81517feab150cfd8114de23b614b84f3214696ac213ea83c213e144471375dc651350ed1413346ed11327edf61305f52212d0695311b4bd5b11af78a8116a8758115cdc5210d7221f108ef5b9105861cc102497a91004efa20fe0ec5e0faa77070f8898390ef737100ea800b80e7ddf9c0dfbaa4f0d6e8d170d60d6180d4430e80d2aded90d15a3500cd4b54f
  | 6, 2 => 0x2a147f222a1317a029d10a3229b62a9829af2b6429740e862971ba402908ceef285f1665285a6120284a71582842fbd328296f412802e9c92750b4f627305dda26aab09626a8a450259a3137254b6a572467744a245472f02423c020241b265d23f579f923f07cfd22e55f9722e058c322d25b5c227a827921d8db4721a5c3f121997fae2177d428213ba1a4212c87fc20d0237020c5f98b20bb659020b8602f20b6484d205b0a2a1fee5c461f08361b1ee15f4e1ebe34261eb6c6781e62464a1e4008941e2d9df31dfc58011dc7548a1db72cc41da019151d9945271d85cfcc1d7de1f81d4c60a11d0c1c131d01f4191c84fb571c7f55261c6f9fec1c1fc936
  | 6, 3 => 0x37444b183707514c36ffac3036c5746f36b5383e36590d6b3619ea8d35e38d4f3597402035970aa9357f738835787e263536fd9035169f3a34f524f934e85a333481847a343ac702340993c533d66273333d305e32b9632332a61e253294f0e03228b42331f5eab331f21e333196b9003185f30f30e3267e30a5e218300cd34d2f2d39052e69b8f32e45ee3b2e450d9e2e41d80f2e3cd5d82e2327552dff29252df877932de4e1f12db09fc22cadc4612c7dc05e2c7d0fd42c4d2a222c2967562c26fb112bfd49b32bb3707a2b812cf62b77b9702b6e1af02b4013f32b1903882af8e8dd2ab3915a2aad75692aa964312a8e42722a8c0ae32a5335872a4774b2
  | 6, 4 => 0x448eda3a43fda76743df5823435fdc074340ca9c42c1977442b451b04291ffc94267208641a0c1284183d887413586ab40a6c27d4028922d3ff1e5963f227ddf3f147cd73e72aa493e40cb2d3e0d36b93e0ad2fb3e0acfe73dd26d833d955f8e3d8f565c3d68cdf13d58882c3d4c8f823d2c7c353d1f3f593d03aadf3c9643853c61cde53c346cd83b33d6c03b1e56293b1599a03b1118053b0f2c583ae826bb3ad3f9603acf9b4b3a8122023a7feee53a73bcfc3a71b7533a4fc2063a0c939f3a03d4b139e99ade39de4fb6399a9e2c3993975b392de5893929da4e38ea75ab389a48a738948c6638838ab1386b233a385c254e37fdfb7837d8b58137997d53
  | 6, 5 => 0x5530a86c54be89f654bd4975548f43ef5479ade65464d08f5416d04b53b74366534934bd52c16aed5281620b52482a60522a087851ee61ea51c09e33506c7ad04f9d2f8d4f9d1e774f86a4154f2dc6724f29237a4f135c524e92e7bf4e79be084e25dd764e20ca5e4dd542384d84259f4d80a61f4c88dffd4c51dc5f4c388e2d4bd7ce484b236a724aabf4e84a32907749e0f04f49dd0e9149d9a14a49c0fcf449beb9e849b6983f49585913493b17444931ec3848c35a8b48bac7e048b0772647bc7759473ba5294739116c46f1b31146ecc97246a8c7ac465e45354652c8274631f35845f126ed45a7f59845913ff4451ed66944c79b8a44c48b0644978530
  | 6, 6 => 0x66a873e666849eaf66596eea65aa0687655de01765438d01653519e36502386064c8c42e64a5eedc646b996f640ee4c863669d956326e6d962bc93d262b99322628e69ce624ac82b6226b9cb6169ffad6154a5f5612833c4611ff8cd601c8a0d600ad1db5fce787b5fcbe2e35f35ba935ed6a3f15eab57b15ea728f45e95b4465e47ff1d5df837b25d994f8a5d65b8685d4be8d35c92b39c5c118deb5b61bbf05b0c632c5acd55a85a9f5dfd5a5a68e3592ed0a2592546695817540b576c925c56f8e29d56e6f7eb56d8e5cd56d29d1756b3de6b5659605e56569ab456488c3a5615047155f6748055f5a32a5592841e55914c4d5582b7b35571ce4a5548eb3e
  | 6, 7 => 0x7dca49407d41b0af7cf889057c60a6ce7c347e527c2f9e497c039c0f7bc5288a7b9c0fe77b6ec17b7b4332737a399f0c79e15a2879c137d279ad6602795acc8c79275758791e9fb77915ad7b7822a7ca7769c495771fe42476d6e321761e2a877616152c759d116275950b387508aada73d6472973bf6508732a242c727dbd767218e0f571ec93a571d8f934718aa31d70d8df6c703b7bb46f4c3cf56e6a31206d8815996d01b3cf6cfb7a1c6cd6ca796cc7f9b76c7e6ef86bba04806b37a4776ae6f02c6a610cd96a13619069edc244692b528c6874fb72683e1dfa680dfb0f67faa20867bf3c7567a3bf0d678524796777015567619883672751d8671ea51e
  | 6, 8 => 0x924b56d4919ac8ae913e25c59133fdb4905e4b308ff254f18fc3c7a68f9fd3cb8efad5908ebf5b3d8e965ddb8e52fbf68dd7584d8d5eaaf98d32e83b8cfa91f68c9c3f098c7bea548c3dbf858c2a9c0c8ba51dad8b7e195e8b4b712b8aef77aa8aba15e18a81f0ca8a51c9de8a37c65d89cd0684895726ae88fe5bb888f4b3ca88ec22aa87c7d78887b2ceb4879add6787657c618730fd4686ef90bf869c242f8690a30e864f5914860d929c85fa1a2f8527bd3a84c8f81684af188b847f168283b173988389289c830562c282e72b3682cca1d4829abebd8233d2a881fbf38a81b76e8e81b726b38069eaef7f7c17707e2488817de2b05b7de08e727ddacfa8
  | 6, 9 => 0xb541bdfab5406affb3a5c8ecb1f9e3e0b1b8a042b151cf00b10e63d6b0cf1072b03646e7b0347cebb0114f0aafd75c9caf018d0daeefd66faea00db0ae6822efacc719e5abc0f8acab676f4fab30f7eaaa3f67bcaa2ce68baa032758a9ea89e0a8309305a822b426a6846df0a59b5408a50242b8a4a20be6a2ce5e77a284be75a2184986a1e5f75fa0aab22aa06b55ada01e0a0a9f77feb79ec0d7899e4056129d99351f9c7381819c508a709b8d299c993a7ae3984648e797cb439c977488ac9742e1059696455296180f8e960c1ebd95b387529551aacc952f9fe39499c431947012d39464b8f8943bd39a942026d993e5c51a93de583e9322c3469278f665
  | 6, 10 => 0xe863d8b7e41c8ef3e413ccc3e3cc7821e2e44efbe254a19ee0d0507fe0675ff1dff57bd6dfbea839ddad0ebedd4a9b86dd09603adc2f9bbedb83fe16db711277da329af0d872797ad84abcd0d740303ad6c060b6d5735722d53d3f66d52b0a13d5194ea3d4b1b5d0d4af50cfd3ab69cdd0c08da1d0a6a70fcf0b78d5ce41280bcd853652cd4c173bcccaebe6ccc7daa6cc12eeb2cbdbb155cabb86a9c9363a22c8a99bdac5b0f683c55c62e5c4f4a2e1c47b6c05c35be029c31f9c69c2f91008c2ac5c31c0f16310c01d1494bfa1f555be1113babd792bb6bab9a1bdba88bda4b9d7cf39b9ab4d11b9aa6055b8bc058fb86243b6b729db6eb6f57744b6cb1964
  | 6, 11 => 0xfc2bdcc0fb17c36ffa870d02f908e400f716d4caf6535463f47b8ceef42af7c7f250bba1ef0d263aeef3064ded37c018eb6f4652eabbbb9de9c9090ee86bd220
  | 7, 0 => 0x19b1d448198eb565196672e1191531f41900f429181aa941170db67f16e8db181581f8c81561a43a1413d608136d10ac135211a212ae5da31232479711ed84b71142fa411134c93410d1aa9610c280c50fd4c3f50faa77070f8898390e8414b20e7ddf9c0e7dd0190df078900d9a92370d91ebc20d61f2fb0cea20e10cb3009d0cabde0a0c867e660c22507d0bd753a90bb2ffb10b989d440b41c7720ab7b9ae0a71f9560a172c4909ee1b6f07bd347d075140fd06cd9ad4065223ce05ad2f3403f1b952036df15003476202033a727c02e9d44b02d5abde0296f579023f103c023c952e01a603fb0198251c0188fb4b014e28b601283a1701013f3600273479
  | 7, 1 => 0x3122199e30bda81a302ca7772fc976f62f1362052edbd6b52ea0b9112e46479b2de85b922d6df75a2d014b912cb7e2692c9946a22b81626d2b698d6c2a6cf0712a5175e429c478db2964176b292df8a128a4a83e2889888f284db2db2838c79a275958f226bb2fef26a4b5bf265363bb264ea12126488ebe2609324125eb7b5225bece64258a6ea42509c4b824cb7b29246554a623fe6fae23a7fde6233e519823038dd422daf26b22543c1c22521a042236825921a5f96820e970f52064873a2046aaad2015ae6f1fb72b911e1aa3ae1d81c57f1ca0b1831c53b96d1c1ffead1b70b1901b52f3321b325a461b2d157f1ac4a36f1a2bfa9c19f08aad19deb3e2
  | 7, 2 => 0x4bff26be4bf147df4bc969994b83735c4b7591cb4b0c2c394afc5e1e4a24047e4a0d197449e125c649148db048ebd2aa46e1bded45f6b58443cee64d43b4257143a9f84843555fb042815d8a425327d74223bdb9413ca696405c8f3d40455b7a3ee6de3d3dff89d03d18fbc93d0124c93c9dc2fe3c8fe41f3c39fd5e3bd0b7833bc2d8a43b76a7473b23954e3afd7b253acd3e823a8b1a653a861c993a476634387c221637dd7e8037b9fc1b37a1ed1c378f31e8375fd1e836c744ae36b6da9236ad5160361b1af4359f67e7359aee6d358e7c13357bcd57354bc4fd3481847a342cdee933d93c6b33ab0d08330961a6326a06213264f194317141fd315024ba
  | 7, 3 => 0x6bd591246bcb63fb6b7c11ab6b58c0516aa264eb6a7ff6686a510b3869d0a4b069b2eaed692e70ee6920920f68742b926709aa6164e30e64647899486449b75d63669d956347643b62542af85fbac6fd5f2a63495eebace45dc82fa15d9647d45d7bf2db5d6275f45d23bf8f5cde0cce5ca9ea895b2acd5959e9c31b596cee2e59051596584e132a56abec62567ee6cd5640306855ab6c465592bd7c53b7a8b5531692945314eaf6530ec13f52e996fb52943af552942b72528ca242520a3fab51ee61ea51e81d5151bb2a0f50c4b4ed5038abd6500139404f943bc44f8c57c24e9d19034e1717654dd111674cfd734b4ca60af44c5e0b844c173de94c1326ad
  | 7, 4 => 0x9d3121ea9985b807996c23f4992721c298411d81981b7e929713ecb19710a45896a4b77d965f34589396353d9351acbb900c696690061e318e2374cd8d7f04bb8d5eaaf98c1a6ee88b7e195e8ab84b5d8a8bfac78a81f0ca8a7994f88a0d10dd8968a0cb89605ac289143e42886bb2a5881ad299872610b8869b7594863bb48b85e99b5485520fcd83f048fb83233d80830766bf827639728241b0597f5f0e0b7f4590c97e05acff7dfd47397db1e1917d303bbe7cfde4937c439fcf7b2b17a17ab597257aa1574779e15a2879a4d76c78f04d34785a178976eecc3f76b015da764692e6727daf3d7263b2ee6eba99336e834bca6cd622c66c4b6e046be1bd3a
  | 7, 5 => 0xd87f9952d697c1d4d630e845d3b34341d30f653ad27a66b2d0e5095fd0ab600ecf84bc20cea2794ccd73df73cd6ebd58ca35eab9c7ad77bcc7466283c707ac1ec5e58a67c5dca5abc59d6c30c57cede8c52f7576c4eae2e7c4ac2c82c21dcfbbc110cb7dc0101992bf01fb40be4be64fbde51875bcc8e334bbec3344ba88bda4b9fc935bb9782853b84d21e0b7a3f583b559ed2fb4d0d4a4b22e7c90b18cc501b0ec7e1fb03d009fb038e43caf01b67aadab993dac3ab49dabe5308aabbe6e52aaa935daaa8df529aa38618da8d9852aa8d69abba80fa957a8098f40a71939e5a4dede88a4a02823a309310ca1689281a0b267039eab30d29e6bbe4b9d42bc1d
  | 7, 6 => 0xfd875a02fc3e0176fab495f5f6f16d4af2854adff1c1f496f171c893f109fd47f03d9387eef3064dee22ff53eb3fcd10e9d3bc26e878be20e1b94d76e1283faae0d9cf49df71e0b2dec49712dd0995b1d89de169
  | 8, 0 => 0xf33b5fd0f2854adfbad4da24b47be6218ab84b5d8a7994f87f4590c97e1a8a567cea112d5fbac6fd5cde0cce51bb2a0f5059633d4f8c57c242b779a33e277fff2eedfa851e7359ed1729918f1606144c1561a43a1142fa410e7e1513
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff0000000000f0f0f0f000000000cccccccc00000000aaaaaaaa0000000033333333000000000fff0fff000000000f0fffff000000000f0f0f0f
  | 0, 1 => 0xf0f0f000f0f0f000aaaaaa00aaaaaa0033ffff0033ffff0000ffff0000ffff00000000ffffffff00000000ffffcccc00000000ffff000000000000ffccffcc
  | 0, 2 => 0xc0c0c0c0c0c0c0c0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0a030303030303030300ffffff00ffffff00ffff0000ffff0000ff00ff0fff0fff00ff00ff00ff00ff
  | 0, 3 => 0xf0fffff0f0fffff0f0ff0f00f0ff0f00f0f3f3f0f0f3f3f0f0f0f0f0f0fffff0f0f0f0f0f0f0f0f0f0f00000f0f00000f0c0f0c0f0c0f0c0f000f000f000f00
  | 0, 4 => 0x330033003300330030f030f030f030f03030f0f03030f0f030303030303030302a2a2a2a2a2a2a2a2222aaaa2222aaaa0fff0fff0fff0fff0fff00000fff0000
  | 0, 5 => 0x3333cccc3333cccc33333f3f33333f3f333333ff333333ff333333333f3f3f3f333333333333ffff333333333333333333333333000000003333000033330000
  | 0, 6 => 0x555555555555ffff555555555555555550f050f050f050f04c4c4c4c4c4c4c4c44cc44cc44cc44cc3f3f3f3f3f3f3f3f3c3c3c3c3c3c3c3c33ff33ff33ff33ff
  | 0, 7 => 0x5f5f5f5f5f5f5f5f575757575757575755ff55ff55ff55ff5577557755775577555577775555777755555f5f55555f5f555555ff555555ff5555555577777777
  | 0, 8 => 0x88888888808080808888888800000000888888008888880088888080888880808888000088880000880088008800880080808080808080807f7f7f7f7f7f7f7f
  | 0, 9 => 0xa0a00000a0a00000a080a080a080a080a000a000a000a0008f8f8f8f8f8f8f8f8a8a8a8a8a8a8a8a8888aaaa8888aaaa88888888888888888888888888880000
  | 0, 10 => 0xa8a8a8a8a0a0a0a0a8a8a0a0a8a8a0a0a8a0a8a0a8a0a8a0a0a0aaaaa0a0aaaaa0a0a0a0a0a0a0a0a0a0a0a0a0a00000a0a0a000a0a0a000a0a08080a0a08080
  | 0, 11 => 0xaa88a888aa88a888aa88a080aa88a080aa88a000aa88a000aa880000aa880000aa00aa00aa00aa00aa00a000aa00a000aa000000aa000000a8a8a8a8a8a8a8a8
  | 0, 12 => 0xaaa0aaa0a0a0a0a0aaa0a0a0aaa0a0a0aa88aa88aa88aa88aa88aa88a888a888aa88aa8888888888aa88aa8800000000aa88aa80aa88aa80aa88aa00aa88aa00
  | 0, 13 => 0xaaaaa0a0aaaaa0a0aaaaa0a0a8a8a0a0aaaaa0a000000000aaaaa000aaaaa000aaaa8888aaaa8888aaaa2222aaaa2222aaaa0000aaaa0000aaa0aaa0aaa0aaa0
  | 0, 14 => 0xaaaaaaaa88008800aaaaaaaa80808080aaaaaaaa0a0a0a0aaaaaaaaa00aa00aaaaaaaaaa00000000aaaaaa00aaaaaa00aaaaaa00aaaaa000aaaaaa0000000000
  | 0, 15 => 0xaaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaaa000000aaaaaaaaa8a8a8a8aaaaaaaaa0a0a0a0aaaaaaaaa0a00000aaaaaaaaa000a000aaaaaaaa88888888
  | 1, 0 => 0xc0c0c0c000000000c0c0c000c0c0c000c0c00000c0c00000c000c000c000c000bbbb3333bbbb3333bb33bb33bb33bb33afafafaf0f0f0f0faaaaaaaaaaaaaaaa
  | 1, 1 => 0xccc0ccc0ccc0ccc0cc00cc00cc00cc00cc00c000cc00c000c3c3c3c3c3c3c3c3c0ccc0ccc0ccc0ccc0c0ccccc0c0ccccc0c0c0c0c0c0c0c0c0c0c0c0c0c00000
  | 1, 2 => 0xccccccccc000c000cccccccc88880000cccccccc88008800cccccccc00000000cccccc00cccccc00ccccc0c0ccccc0c0ccccc0c000000000cccc0000cccc0000
  | 1, 3 => 0xcfcf0f0fcfcf0f0fcfcf0000cfcf0000ccccffffccccffffcccccccccccccccccccccccccccc0000cccccccccc00cc00ccccccccc0c0c0c0ccccccccc0c00000
  | 1, 4 => 0xe0e0e0e0c0c0c0c0e0e0e0c0e0e0e0c0e0e0c0c0e0e0c0c0e0c0e0c0e0c0e0c0d5d5d5d5d5d5d5d5cfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfcf00000000
  | 1, 5 => 0xececececececececececa0a0ececa0a0eccceccceccceccceaeaeaeaeaeaeaeaeaeaeaeac0c0c0c0eaeaeac0eaeaeac0eaeac0c0eaeac0c0eac0eac0eac0eac0
  | 1, 6 => 0xeecceecce000e000eecceeccaa00aa00eecceecc00000000eeccee00eeccee00eeccaa00eeccaa00eecc0000eecc0000eeaaeeaacc00cc00eeaacc00eeaacc00
  | 1, 7 => 0xeeeeeecceeeeeecceeeeececeeeeececeeeeecec00000000eeeecccceeeecccceeeeccccaaaa0000eeeecccc00000000eeee0000cccc0000eecceecceecceecc
  | 1, 8 => 0xf0f00000f0f00000f0c0f0c0f0c0f0c0f0c0f0c0c0c0c0c0f0c0c0c0f0c0c0c0f000fffff000fffff000f000f000f000f0000000f0000000eeeeeeeecccccccc
  | 1, 9 => 0xf0f0f0f030303030f0f0f0f00f0f0f0ff0f0f0f000f000f0f0f0f0f00000f0f0f0f0f0f000000000f0f0f000f0f0f000f0f0c0c0f0f0c0c0f0f0c0c0c0c0c0c0
  | 1, 10 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0f0000000f0f0f0f0c0c0c0c0f0f0f0f0c0c00000f0f0f0f0c000c000f0f0f0f080808080
  | 1, 11 => 0xf8f88888f8f88888f888f888f888f888f3f3f3f3f3f3f3f3f3f3f3f300000000f3f33333f3f33333f0fff0fff0fff0fff0f0fffff0f0fffff0f0ffff0000ffff
  | 1, 12 => 0xfaf0aa00faf0aa00fac8f000fac8f000faaafaaaf000f000faaaf000faaaf000fa00f000fa00f000f8f8f8f8f8f8f8f8f8f8f8f888888888f8f8f0f0f8f8f0f0
  | 1, 13 => 0xfafafaf000000000fafaf0f0fafaf0f0fafaf0f0fafa0000fafaf0f0aaaa0000fafaf000fafaf000faf8faf8faf8faf8faf80000faf80000faf0faf0faf0faf0
  | 1, 14 => 0xfcf0cc00fcf0cc00fcccfcccfcccfcccfcccfcccf000f000fcccf000fcccf000fc00fc00fc00fc00fafafafaf0f0f0f0fafafafaf0f00000fafafafaf000f000
  | 1, 15 => 0xfcfcfcfcccccccccfcfcfcfc00000000fcfcfc00fcfcfc00fcfcf0f0fcfcf0f0fcfcccccfcfcccccfcfcccccf0f00000fcfc0000fcfc0000fcf0fcf0fcf0fcf0
  | 2, 0 => 0xff00f000f000f000ff00cc00ff00cc00ff000000ff000000feccf000feccf000fcfcfcfcfcfcfcfcfcfcfcfcfcfc0000fcfcfcfcfc00fc00fcfcfcfcf0f0f0f0
  | 2, 1 => 0xff00ff00ff00ff00ff00ff00fc00fc00ff00ff00f000f000ff00ff00cc00cc00ff00ff00cc000000ff00ff0000000000ff00f000ff00f000ff00f000fc00f000
  | 2, 2 => 0xff888888ff888888ff33ff33ff33ff33ff33ff3333333333ff0fff0fff0fff0fff0fff0f0f0f0f0fff0f0f0fff0f0f0fff0cff0cff0cff0cff00ffffff00ffff
  | 2, 3 => 0xffc0c0c0ffc0c0c0ffaaffa0ffaaffa0ffaaff00ffaaff00ffaaaaaaff000000ffa0ffa0ffa0ffa0ff88ff88ff88ff88ff88ff88ff00ff00ff88ff8888888888
  | 2, 4 => 0xffccf000fcccf000ffccccccffccccccffcccccc00000000ffcc0000ffcc0000ffcc0000cccc0000ffc0ffc0ffc0ffc0ffc0ffc0c0c0c0c0ffc0ffc000000000
  | 2, 5 => 0xffccff00ffccff00ffccff00fcccf000ffccff00f0c0f000ffccff00cccc0000ffccfcccff00f000ffccf0c0ffccf0c0ffccf0c0ff00f000ffccf000ffccf000
  | 2, 6 => 0xffccffccffc0ff00ffccffccff00ff00ffccffccfcccf000ffccffccf000f000ffccffccccccccccffccffcc00000000ffccffc0ffccffc0ffccffc000000000
  | 2, 7 => 0xfff0f0f0fff0f0f0fff0f0f0ff000000fff0f0f000000000fff0ccc0fff0ccc0fff00000fff00000ffccffccffccffccffccffccffccff00ffccffccffcc0000
  | 2, 8 => 0xfff0fff0fff0fff0fff0fff0fff00000fff0fff0f0f0f0f0fff0fff0f000f000fff0fff0ccc0ccc0fff0fff0ccc00000fff0fff000000000fff0ff00fff0ff00
  | 2, 9 => 0xffff0000f0f00000ffff0000cccc0000ffff0000cc000000ffff000000000000fffcfff0cccc0000fffcffccf0f00000fffcf0f0fffcf0f0fffcf0f000000000
  | 2, 10 => 0xffffa0a0a0a0a0a0ffffa000ffffa000ffff888888888888ffff3333ffff3333ffff0f0fffff0f0fffff00ff00000000ffff0000ffff0000ffff0000ff000000
  | 2, 11 => 0xffffc0c0ffff0000ffffc0c0c0c0c0c0ffffc0c000000000ffffc000ffffc000ffffaa88ffffaa88ffffaa00ffffaa00ffffaa00aa00aa00ffffa0a0ffff0000
  | 2, 12 => 0xffffccccf0f0c0c0ffffccccf000c000ffffccccccccccccffffcccccc00cc00ffffcccc00000000ffffcc00ffffcc00ffffcc00cc00cc00ffffc0c0ffffc0c0
  | 2, 13 => 0xfffff0f0cc00c000fffff0f000000000fffff0c0fffff0c0fffff0c0ffff0000fffff000fffff000fffff000f000f000ffffccccffffccccffffccccff00cc00
  | 2, 14 => 0xfffff0f0fffff000fffff0f0ffff0000fffff0f0ff00f000fffff0f0fcfcf0f0fffff0f0f0f0f0f0fffff0f0f000f000fffff0f0ccccc0c0fffff0f0cccc0000
  | 2, 15 => 0xffffffff00ff00ffffffffff0000ffffffffffff00000000ffffff00ffffff00ffffff00ffccff00ffffff00f0f0f000ffffff00cccccc00fffff0f0fffff0f0
  | 3, 0 => 0xffffffffa0a00000ffffffffa000a000ffffffff88888888ffffffff88880000ffffffff88008800ffffffff33333333ffffffff30303030ffffffff0f0f0f0f
  | 3, 1 => 0xffffffffc0c0c0c0ffffffffc000c000ffffffffaaaaaa00ffffffffaaaaa0a0ffffffffaaaa0000ffffffffaa88aa88ffffffffa0a0a0a0ffffffffa0a0a000
  | 3, 2 => 0xfffffffff0c00000fffffffff000f000fffffffff0000000ffffffffccccccccffffffffcccccc00ffffffffccccc0c0ffffffffcccc0000ffffffffcc00cc00
  | 3, 3 => 0xffffffffff00ff00ffffffffff000000fffffffffcfcfcfcfffffffffcfc0000fffffffffc00fc00fffffffff0f0f0f0fffffffff0f0f000fffffffff0f00000
  | 3, 4 => 0xffffffffffff0000ffffffffffcc0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xbec9d12804ccbb9385b4
  | 4, 0, 0 => 0xba43da49c402df61ea4481a571d516ba70cab4e6ba69005b5b243dae90402df5ccd74e2017230f77270a6b7d93b5d38805bec3d529029ae465ed74e1bd6a3356ba7100b936ba70d25b5bebadae9c2dad761ed75624161ed75ca6900b7da8c3ddcad5
  | 4, 0, 1 => 0xbec3d5c8934ad3a6cd744a0172d516ba70c8b4e9cb5d38805a8d09849c402d45aeb74e20172d286ba7100b5190b5538805a8cb5969c402df63ec248201721516ba24cab7d82bf512805a8ccdaa89402df650d74e1756faee65270b6b7d91b0912805
  | 4, 0, 2 => 0x17d9e30920805b5cd1ae9c402e621eee4e16d6fb2a63a3900b7d82bd112805becbddc9c29ae661eee4e2016fb046ba7100b9187b5d70695
  | 5, 0, 0 => 0xbed4612d74e195aeb518535d38806c8545ae9c40195afb5198b5d1a806a44921ed74e201b230f6ba71006f6b754674d747201aa32087b5d589c6a8c35aed64e201afb5187bb95e9c6cc5f61eee4e201afb6887b5d20806bedce1e9044a01adf5187b5d38806bec1dae9c48201afb4e87b5d24806
  | 5, 0, 1 => 0xcb5461eee4e201afb5187b5d50496cdd461f0344a01af92582b5d38806bed461ea448201b2d516ba70b6496a8d121ad74e201b310f6bb1d386f6c8d461ec64e201afb5187b89125b6c8d465ed74e181aa30f6bb0134806bbc29aed54e201aa30a6ab1d38806cc5e21ecb4e201afb5187b81385b6
  | 5, 0, 2 => 0xb853a1ed74e201afb519d35d62806bec3dae9c37825afb2f6ba70d2536bedae1f0344a01afb6ba3b09386c6a8cd9ae9c401e1b29519cb5d36806a8c31aed54e201afb5186b5d38726bed821ed756241aa3326127112806bed461e8940159aa3416127112806ccc3dae9c401a5aa32087c0d12806
  | 5, 0, 3 => 0xcd5f20acb4e201b0b7687b5d38806d0d321f0344a01afb0f7731d385b6bed45aeb44e201afb5f87b5d589c6bec3d8e9c449bdb2d7787b5d38806c85da1ed74e201afb0f76b5d38806cd5ae1ecb4e201b235197b5d128060054668d74e2014017d6ba7100125bedf20b0344a01aa30f7835d38806
  | 5, 0, 4 => 0xcb5461f0344a01b2d7da8b5d38656d0d7a1ed74e201b434c87b5d38656005461ece4e2016ed0f8635d38806005f61e9c400796fb5187bf512806cfdf6a2d75c125b2d519a35d38806bed461ed74e08daa30f8635d36806c55461ed74e189acd5187b5d38806cc43dae9c3494dafb6087c0d0a806
  | 5, 0, 5 => 0xaec3dae9044a01b235187bf112806c7d466cd74e201aa34b87b5d38806a8c3daebd4e1bdaa34f86b2d38806bed461ed75c10dafb5186b5d38656c8dd21ed74e201b216987b5d20806c1d4634d74e201afb516127112656005f65ed74e1bd6fb5f87c0d12806c754674d74e201a990f6ba6920806
  | 5, 0, 6 => 0xc9c3dae9c401a5b310f6ba70d25b6b5cc9aec24e201afb6987b5d20606c8d461ed74e195b217887b1d38806b5d05aec24e2018019887b5d386f5d0d3274d747201b23519b35d38806a8d2a1ed74e2018017686b5d38805cc5466ed74e201aa30f6bb0136806c95461ed748a01b215187b5d386f6
  | 5, 0, 7 => 0xbed461f034488dafb0f7727120536005461ad64e20169d0f6bb5538806bed461ec656271afb6b6ba7100656cb545ae9c3496dafb5187a90b6496a8c35969c4ca01afb6b87bd912806bed461ec649201afb4e87b5d386e6bed45aeb84d201afb51a1b0938806becbdae9c481bdafb3f6127120806
  | 5, 0, 8 => 0xbed721f0344a01b1d5187c0d12806a8cca1ed749201afb5187a24b6586b74921ed74e201afb057eb5d38806b2d461ed74d201b3f5199b5d12806bed461ed749185af35187b5d28806a8ccdaed54e201b23519d35d1c806c854674d744a01ac70f6ba411c806bed721ed756271b1d5187b5d589c6
  | 5, 0, 9 => 0xbed4642c24e201afb0f7732938806cfd4614d749201aa30d6bb5538806b95461ed74e201b297887b1d28806a8cce1ed74da01afb76a3b0938806005f6a30f400c56fb518f35d385a6a8c3de2d74e201aa30f77b5d38726beca212d74e201afb3c87b5d20806ca5461ed74a1bdaed0f6ba7100786
  | 5, 0, 10 => 0xbed4612d74e17dafb5187b5d7c446cb545aec24e195b355187b2d38726a743daed24e201afb69a3b0920806bed461ad74e1c5afb5187ab912806005f6a30f462016a30a80b5d38806a743dae9447201afb51612a138806bed461f03449c9afb2484b5d38806d0c35ae9c401a5ae35187b5d28806
  | 5, 0, 11 => 0xd0c3dae9c3d9a5b317d87b5d386f6ca545ae9a4016daa33087b5d24806005f650d74e2016fb5183a7112806bed3a10d74e201b2d5187b5d386c6bed461ed749195afb5195b5d38806bed466cd749201afb5187a9938726becbddcd74e201afad7612c938806bec3dae9c429bdafb5187bf158896
  | 5, 0, 12 => 0xbed466d0344a01b2d6987b5d20806bec3dced74e1a5ae10f6ba7120806beca1ae9c48201afb6986b5d20806bed461ed75f915b3f6587b5d20806d0d5e1ed74e201aa30a6aa7112806c4d621ed74e201b295184b5d28806cd5da1e9c44a01aa3446bb0938806bb43e1ad74e201afb7c7735d385b6
  | 5, 0, 13 => 0xca5ae1ed74a2018017d87b5d002f5ca5461ed75b201afb6c87b1938806ca5468ec24a201afb519735d38806bec25ae9044a01afb0f74b5d38656cbd461ec64e201b35516aa71005b6bed3a12d74e201afad74e24cd25b6a8c3e1ad64e201afb5187b5d385e6bed45dcc24e16db297087b5d38806
  | 5, 0, 14 => 0xa8c35ae9c4d201b3f516ba7100636cc5461ec64e201ac95187b5d38806b1d468ec24e201afb5187bd112806bed461e89400c5b1f5187c0d0e806bed4654d747201afb5187b5d549c6bf5466cd74e201afb0f6bab938696bed45c8d74e16dafb0f48224d2536006461ed74e1bd6fb5196b5d38806
  | 5, 0, 15 => 0xa743dae9444a01b1b5187b5d38706bedf23ed74e2018019887bb938805a8cca1ed74e1bdb3f0f6bae538806c45461ed74e1c9b2d5199b5d38806bec15849044a01b2d6b9d35d38806d0d328ec24e201b436a87b5d38806bec7e1ed748201afb5187a24e6586bed461ea44e1a5afb5194b5d38806
  | 5, 1, 0 => 0xbede274c747201afb7887b1d38656c2d466cd74e201b1f5f87b5d38806bedda74d747201afb7ca8b5d70496cc5461f0344a01b2d516bae138806bed4612c64e201afb057a35d38806bedda1ed74e195afb5c9135d38806c8c25ae9c48201b1d519135d38806
  | 6, 0, 0 => 0xbedda1ed74e200a6f7da8c99aec24e201efb6987b5d2089403802fb5187b1938366cb5f6a3476127100f7da8c3dae9c40099efb5187b5d589c42be62a30f6ba7112807bede2750f63a7100e00cd5461ed64e201b135187b5d3894403d469f0f6ba7128807005461ed74920016c00bed461ee04e2018017d87b61ae9c4035f6f10f63a7100497
  | 6, 0, 1 => 0xcb5461ed74e200f2f7dbc43dae9c40025efb51a3b093890403df6a2d76aa71005b7bed461ed757a2500f96bedae1ed74e201efb5187b1d8c9c403df6a30f6ba71126f7bedd29d0f6ba7100e00bec3daec34e201afb5187b5d387f2dbdf6a30f6bb2d38657c8d461ed74e23900e00cad461ed74e201afb5187b79ae9c403802fb5187b8912806
  | 6, 0, 2 => 0xb7546750f6ba7100e00bec91aec24e2018017d4e20036100635f6a30f6ba2500587c35461ed74e200a6f7da8cbdae9c4014df297da8d1d849c403dbaa30f6ba7100497005f6470f6ba7100d7d87b5d3890401adefb5187bb9ae9c2dbdf6490f6ba7100497cfdf6a2d75c27100f7db4d468ec24e201c017d87b5d729c4030032d519d35d38806
  | 6, 0, 3 => 0x5461e9c4006c16d7da8c3dae9c400edc017da743d38800db5f6a30f7b30912807bedae1ec24e22500f7da8c3d8c9c401cdefb5187b5d388b403e52fb6b87b5d38807005f6a30f6b9a854c00ce5461ed74e201afb5687b5d388029be7ea34c6ba71005b7bed461ec64e20036f7da8c3daea74e201efb519d35d3884403802a5516ba7100106
  | 6, 0, 4 => 0xbed461ec64e2009cfa1a8c3dae9c401e1f297dbe415ae9c403802fb5184b5d002a60065aa30f6ba7100c0087b5d38800602dafb516bb09388032b802fb519d35d00306005f6a30d6ba7100d7dbc43d8e9c44a01c017da8c3e0680193002c70f6ba7120806bed461efc4e22500f5187b5dac9c401cdefb0f8335d3890403df6a34761271000c7
  | 6, 0, 5 => 0xbed461ee16ba7100f7db4c3dae904014defb7ca8c3e0689403df6a30f6bab138877bed46990f6327100f7d87b5d3c9c4006dc015187c0d128005b5f6a30f6bb3538807cc5461ed74e200a6e00bed45ae9c47195afb5187be13889403df6a31b6ba71004d7005f61ed75e24100d7da8c3daebb4e201c0163a8c3d38800db5f6a30f81a250a807
  | 6, 0, 6 => 0xbedee9d0f6ba7100e00bed45ae9c40045801519943dae9c1b3002fb6b87a71001b6bed461ed74e1bca6e00bed1d849c40031afb519d35d968e403dbaa30f6ba711280700546830f6ba706cd94a8d1e1ed74a201efb5187b5d388a403e42a30f6ba7100537bec921ed74e22500fa1bed468ec24e201efb0f7735d3890403802fb51a2b0938806
  | 6, 0, 7 => 0xbed461ed74e2009cf7da8c35ae9c48201c017da9c3d38800d3686a33387b5d38807005f6f9054e20036c00bec3dae9c40035afb5187b5d2893403802a30f6ba70ca0b6bf5461ed765a7100f9abe5461ecb4e201efb5187b25388029bd46650f6bb1d38807005f6a30f6ba7074c00bed45002a0d841aa34187b5d8e9c403e7ecb5187b5d38807
  | 6, 0, 8 => 0x5f61eee63a7100d519943dae9c4006dc017da8c39ae9c4035f6a30f6ba7064237005f6f12f6ba7100d7da8cea12d74e201efb5187b5d38801c3e6aa30f6bb5538807bedce1ed74e24100f96b4d461ed74e201efb7687b5d38802dbe02a30f8535d38807ca5461ed74a20092f96a8c3dae9c48201efb5184b5d388024bdf6d35186b5d38807
  | 6, 0, 9 => 0xbed461f026ba7100e00d0d321e9c4006dafb5187c0d589c44bdf6a30f6ba70f0537bed461ed74e1cce4f7da8c3d489c4016df439a87b5d388034be42f15187b5d38807bed461eec6ba7100f7da8c3e06f944a01c017da743dae801535f6a30f6ba70e41b7cb5461ec24e22500e00bed461ed74e1f1afb7887b1d388029be62a30f7db5d38807
  | 6, 0, 10 => 0xb75461ed74e200a6f7da8c3daec44e201c019fa8c29ae9c1b35f6932487b5d38807bed461ed74920020e00b1d461ed7400a9aa34e87b5d3894403e26a30f6bb2d38807a8d3e1ed765a7100f7da8c3d8c9c4002dea34187b5d3880153df6a30f6ba24b6497cb5461ed74e20018f7da8c3dae9c40095efb5187c0d1287403df6a30d6ba71000c7
  | 6, 0, 11 => 0xca5461ed74a22500f7dbc43df6c74e201c0196a8c3d38800db5f6a30f6ba70b61570043d38800d83016d91a8c3dae9c4da01c017db4cbdae904035f6a30f7135d385b7cfd4614d763a7100f7da8cbdae9c4a201c015187b5d38800535f6f55187b5d38807bed461eea6ba70cae00cc5e21ed74e2018017da8d1d8480153642fb516ba71005b7
  | 6, 0, 12 => 0x5f6a30f6ba7072c00bed461ed74e08dafb5187b5d38803a3802fb0d6ba71000c6bed461ed34e200a6e00bed467ec24e201afb7687b5d849c403e52a30f6bb4d288070054674d74720016c00bedadae9c4016dafb5187b5d388033b802fb6b87b5d002a6bed461ed74e25500f7dbc4bdae9c48201f295187c15ae94403d8ea34787b5d38807
  | 6, 0, 13 => 0x5f6a30f81a246cd7da8b5d388e2d925efb5187b6dae9c403df6a30f6bac138807bed461ed76427100f7da8c8a1ed756271f375187c0dae9c4038029d0f6ba7128806bed461ed74e21900f7da8c3daebf4e1c9efb6987b5d20802db8032d0f6ba71000c6cfd4614d74e20036f7da743dae9c40125f315187b5d38802dbdf6a30f6bb09386c7
  | 6, 0, 14 => 0xbed461ed74e20064e00bed466cd74e0d9afb6987b5d2890403df6b35187b5d3880700646a30f4e20036d7da8c3dae9c400ddf315187b5d3894403e7ea30a6ba71002a7bed4634d74e20084f90bed4674d747201efb5187c0d8e89403e86a30f86b5d38807bed461ed74e200acf63a8c3dae9c40125efb7c87b5d38800d3df6a30f6ba70de5b7
  | 6, 0, 15 => 0xbed461ed74ca4100f7da8c3dae9c32971efb519b35d8e9c403df6a30f72b5d38807bed461f0344a0020e00bedf1ae9c3496d8019187b5d3880063002fb5187bb9385360066aa30f65a706cc00cd5461acb4e201afb518bc3dae9c403803055187b5d00296c85461ed74e25100e00a8c3db8d7400a9801a1a643dae801535f6a30f6ba7102807
  | 6, 1, 0 => 0x5461ecb4e20000d7da8c3dae9c401e5efb5187b5d388016b802fb0f6bac938806bedae1f036ba7100f7da8c3daec74e195f315187b5d38803d3df6a30f6ba8538807bed461ed74e200c6f7da8c3dae9c3902defb5187b5d2491403803310f6ba7100696cd5461ecb63a7100f7dbc43d8e9c4016defb5187c0d128039bdf6a30f6ba7100777
  | 6, 1, 1 => 0xbed461ed74e2001cf7da8c8a1f0344a01efb7c82b5d388024bdf6a3366ba71001b7bed461ee04e20092f7da743daed34e201c0194a8cd9ae9c403686994787b5d38807a8c821ed74e22500f94a8c3dae944014df315187b5d849c403802fb766ba7100106bed461ed74e1e0b6e00c75461ed74e2018015187a00541b05b5f69d0f6ba7112807
  | 6, 1, 2 => 0xbed461ed74e1cccaf63a8c3dae9c44a01efb5187b5d849c37bdf61f056ba411280700662f10f63a7100d7da8c3dc48940125efb5171b5d388034be7efb516ba70b6497bedf20b036ba7100f91b4c3dae9c48201c0196a8b5d38802db5f6a30f6ba70ca1b70043dae801503016d9aa8c3d969c40041efb0f84b5d3890403df6a30f6b30938807
  | 6, 1, 3 => 0xbed461ec64e24100f519ec3e0ad74e201f434c87c0dae9c403e5afb519d35d38807bed461ed74e1949cf7da8cbdae9c48181f434c9d43dae9c403e6aa30f65a71002a7005461ed74e20002d7da8c3d92c24e201f434c87b5d388024bdf6a3366ba71002a7005f61ed74f27100d7da8c3dba9c4014dedd5187b5d38802dbdf6a34c87c0d12807
  | 6, 1, 4 => 0xca5461ed76b27100f92bed461ed749201efb5187b5d589c193802fb519d35d1c366a8d3a1ed765a7100f7daf5461ed74e201efb51a643dae9c32bdf6a30f6ba70b6437bede21ec76127100f94bc5461ed74a201c017d87a706c1b0635f6490f6ba7128807bed461ed74fa7100f7db5c3dae9c44a01efb5187be9ae9c403802fb51a3a7100216
  | 6, 1, 5 => 0xbed821ed74822500f7da8cbdaecb4e201efb5187bf5ae9c403802a30d6ba7128806bed46750d6ba7100f96a8c3dae9c40125efb5187b5d388240380331516ba7100106bed461ef56ba7100f7da8ce9aec747201c017dbe35d388009b5f6a33a6127112807bed461ed74e25900f7dbe415ae9c44a01ea30f6ba8138800dbdf6a30d6ba7100497
  | 6, 1, 6 => 0xbed4674d747200e6f7da8c3e06894002defb6087b5d3885403d8ea30f6ba7100537bed461ed74e20080fa1a643dae9c44a01f357d9243dae9c403df6c35187b5d38807b75461ed76127100f7db6d461ec64e201efb519d35d1c800db802a2d74e0d8200b6005f6a2d74e1bc20d9fbed461ed749201c0190a8b5d388008365aa30f81b5d38807
  | 6, 1, 7 => 0xbed461f0344a0064f7da8c35ae9c401edc017d87b1938800635461ed75aa71005b7c8d46750f6ba7100f91a8c3df8d74e201f295187b5d28802dbdf6a2d74e269005b7c8d461ed74e20092f7da8cfa1ed74e201efb62a8ce9ae8e403e32fb5187b5d386f7bed468ec24e200a6f7da8c3d849c44a01efb518fc3dae9c403802fb5187a2500586
  | 6, 1, 8 => 0xa8d061ed74e24100f7da8d3274d747201efb5187b5d386505bdf6d30f6bb2d20807cc5461f0a6ba7100f94a8c3dae94401a5efb5187b5d38801ab802fb51878d8541b6cd5461ecb4e23900f7da8c3dae9c40131efb5187b5d38801e3df6a32c87b5d38807c85469b0f6ba7100f7db5c3dae9c4014dc017dbc31d3880083602a30f6ba7100737
  | 6, 1, 9 => 0xbed461ed74e1c8e0e00bed46229c4006dafb5187b5d388019b802dd516ba7100106a8d061ed74e20018f80a8d321ed74e201efb5f87b5d3889403e52fb5187b5d38727bed461ed74e1bcdae00bec3d3c9c4006dafb5187b5d388023bdf6a3096ba7128807bed461ed765a70dee00bec3dae3615031afb6987c29ae90403e5aa30f6ba7112807
  | 6, 1, 10 => 0xbedae1ef66ba7100f94a8c3daec24a201c017da8c3df8894035f6a30f6ba71001c7c7df6a30f6bab138f7dbe43dae9c3494defb7887b2d8e9c403e52fb5187b5d24807005465ed74e20016da1a643dae9c4014df294e87b5d969c403df6a3477b30938807cfdf6a30f81a2500f519943dae9c40031efb5187b5d38800b3df6a31587b5d38807
  | 6, 1, 11 => 0xcfd4614d74e24100e00bed461e9c3906dafb7c9fc15ae9c403802a33287a71001b6005f6a30f6320054d7da8c3daea54e201f1b7da8c3dae9c393803355187b5538806bed461ed74e2005cf7da8c3d84ac4e225f317dbc43dae9c403df69d0f6ba71005b7005f6a30f81a2500d7da8c3deed74e201efb518c43dae9c403df6a30f6ba491a807
  | 6, 1, 12 => 0xbed461ed74e1f892f7da8c3dae9c40075efb0f6ba41128034bdf6a30f6bb3d38807bed461e9c44a009af63a8c3dae9c4016defb516ba711c692dbdf6a30f6aa7112807d0d461ed74e200f6e00cb54614d74e201afb5187b75849c403df6a30f6ba9138807bed461ed74e20058f7da8ce9ae8e4002dc014187b5d3880063002fb5187b7500246
  | 6, 1, 13 => 0xc8d461f0b6ba7100f7da8c3d8c9c40125c017daa43dae8014300329516ba5100106a8c3daed54e200e6f7da8c3e069044a01f1f7da8c3e0689403df6a30f6bb1538807beda65f0f6ba4100f98a8c3dae9c4c201f3f518535d3880063d461ed74e25100787bed461ed754a7100f7db5d1daec24e201c016987b5d208005b002fb5187a7100196
  | 6, 1, 14 => 0x546650f6ba0054d7dbe415ae9c4a201f434c87b5d38802dbd46990f6bb5538807cfdf6a2d74e1a4b6f7da8c3daed14e201c019f8535d3880063002fb5187c0d58896beda6a3366ba7100f7da8c3dae9c2d961efb518cb5d388024bdf6a30f6ba7100557c5d461f0a6ba7100f7da8c3dae9c4488defb5187b5d2480173df6a30f6bb3138807
  | 6, 1, 15 => 0xbed461ed74e19418e009243dae9c4002db355187b2d3880063df6a30f6ba71005770061ea30f6ba7100c00c25461ed74e2018017da8cbdae9c1b35f6a2d74e24d005b7bed466cd74e20018e00bed461ed751a71afb516ba711c8032bdf6a34687b5d38807005f61e9c4006c18d96bed45ae9c4016df355187c35969c403df6a30f6ba7100527
  | 6, 2, 0 => 0xcb5461ed74e200d2f7dae43dae9c44a01efb5187b5d3880253df6a32f6ba71001b7cc546810f6ba7100e00bed466c9c4006db1d5187b5d3889403802fb7c6ba7100596bed461ed74e20096f7db3d461ed74e201c017d87c0d12800635f6a30f6327112807cd5f6d70f6ba7100e00ca5da1ed74e201afb5187b5d38651e38033f518635d38806
  | 6, 2, 1 => 0xbed461f036ba70e4f96a8c3dae9c4a201c017db4c3dae901b3002a30f6ba71000260054664d76127100d7da8c3dae9c401f1f2d519d35d849c403803235197b5d38806bed461ed74e1c892e00cc5461ed74e0d9b437da8c3dae9c32bdf6a30f6bb5138807bed461f0344a0082e00bed461e9c3286dafb5197b5d388039be7ea34f87b5d38807
  | 6, 2, 2 => 0xbed6ea30f6ba70caf7da8cea1ed749201c017db5b5d38800835f6a30f4822500537c85461ed763a7100f7da8c3daed34e201efb5187b5d248024bdf6a30f6ba7100757005461ed74e20010c00bed461e801506db1f5187b5d3894403df6a30f6ba7100517bed46250f6ba7100f7da8b5d949c4016defb5197b5d3880153df6a30f7127100417
  | 6, 2, 3 => 0x646d30f6ba4100d7da8c3dae9c40121efb51a7c35ae9c403e46a30f6ba7128807beda61ed748200e6f7da8c3dae9c4003df215187b5d38800dbd461ed765a7100787cc5461ed74e200e6f7da8c3dae9c40151efb6987b5d20800dbdf6a33a6ba39000c7cc5461ed74e20020e00bec3dae8015031b315187b5d38800dbdf6a30f81a2500587
  | 6, 2, 4 => 0x666a30f6ba7100da1bed4674d747201c017da8cd9ae801535f6e75187a7112807c2d461ed74e2008ce00bed46748e4006dafb5a87b5d38692dbdf6a30f6ba7100397bed461ed74e20046f7da8c3dbed74e201efb5187b5d368e403df6a30f6ba7112727bed461eff6ba2500f7da8c3dae9c39145efb5187c0dfc89403df6a30f6d27112807
  | 6, 2, 5 => 0x53a1ed74e20016d7d9243dae9c401cdf21519d35d388e403e42a30f6ba7134807bec921ed74e20036f7da8c3dae9c44201c00d74e200200c05b5f6a30f6ba70e4397bed461f0344a0092f7da8cbdae9c4002defb5187be5ae89403e86fb0f6ba71001a7005f6490f6ba706cc00bed461ed7328a9b355187b5d389b403803355187b2d002a6
  | 6, 2, 6 => 0xbed461ed759a7100f7da8c3d8c9c401a5efb5187c160689403802fb0f6ba7100206bed461ed74e1a092f7da8caa1ed74e201efb51853093889403df6a30f77270d2537beda61ed74823900f7db4c3dae904002dc017da8b5d849c32b67aa30f6ba7100737bed466d036ba7100f7da8c3dae9c400adefb7ca743dae9c403e52a30f8635d28807
  | 6, 2, 7 => 0xc8d461f0a6ba7100e00c0d461ed74e201afb5187b092089403df6a30f6ba7106807bed461ed75c24100e00cfd3a1ed74e201afb5189c3dae9c403802f9056ba71000b6bed466cd74e22500f99a8c3daeca4e201f355187b2d38803dbdf6a30f6327128807005f6a30f5227100d7da8c3dae9c401d9f439487b5d388034be82fb2487b5d38807
  | 6, 2, 8 => 0xbed46390f6ba7100f7da8cd9ae9c4014df2d6ba8c3dae9c403d461ed75d27100697005f69d0f6ba706cd7d87b5d38903494dc017d6ba706c10063003315187b5d38806cd5461ed76b27100e00bed461ed7400b9afb2487b5d388005bdf6f90f7735d38807cb5461ed74e25d00e00cfd4666d74e201afb5187b5d386a153df6a30f6ba7100667
  | 6, 2, 9 => 0x67ea30d6ba7100d94bed461ed74e1bdefb519c43dae9c403802fb7c82b5d38366bede2a3366ba7100f9ebedf20ad74e201f2169a8c3dae9c403df6a30f6ba5124807006469d0f6ba7100d7da8c3de8d74e201ea34c87b5d389a403df69d0f6ba71001b7bed461ed74e250e4f7da8c3dae9c401f5efb5187b5d386529be7ea30f7935d38807
  | 6, 2, 10 => 0xbedc6a30f6ba7100e00a8c3d38360d82dafb5187b5d38732c3803215187a71001b6bec3dae9c481a4b6f7dbe415ae9c401cdf297dbc43d8e9c403df6a30f81a25005b7bed461ed758a7100f87a8c3dae9c4014dc0198a8c3d38800db5f6f9056ba71001b7bed461ed74e20068f8fa8c3dae9c43a01f3f5187b5d809c403df6f15187b5d38657
  | 6, 2, 11 => 0xbed461ed76827100f96a8c3dae9c401cdefb5187b5d3869343df6a30f6ba71003e700606a30f6ba0054d96a8c3dae9c4006defb55a8c3dae9c403df6a30f6ba7100227bed461ed755a7100f7da8c3dae9c40141f3f7da8c25ae9c403df60ad76127120807bed461ad763a7100f7fa8c3daecb4e201efb5187c0d28894038032d5187b5d38366
  | 6, 2, 12 => 0x5461ed74e1c816c00bec921ed7400a9afb518d35d385b24b803355165a7100106cc5461f036ba7100e00bed461e8940051801518535daa9c40367e990f6ba7120807bed46790f6ba7100f7dbbc3daed54e201c017d6ba7100100635f6f9056ba71000b7bed461ed74e25d00f7da8c3dae9344a01f355187b2d849c403e5aa30f6ba71002a7
  | 7, 0, 0 => 0x5f6a30f7935d38807bed461ed74e23900738005f6a30f6ba7100057005f6a30f6d35d38807005f6a30f8635d38807bed461f056ba7128808bed461ed74e25112808ca5f6f95187b5d38808bed461ed74e200200b8bed461ed74e239001b8bed461ed74e200360b800652a30f6ba71000b700652fb4e87b5d38807bed465f0f6ba712080800002fb7c82b5d38806005a6a30f6ba71000b7
  | 7, 0, 1 => 0x2a30f4e200360b6005f6a30f8535d002a7005f6a2d74e20092107cd5f6a30f82b5d38808005f6a30f6ba7100597cd5f6a30f6ba7112808005f6a30f6bb2d002a7bed46990f6ba711c808bed461ed76127112808cd5f6a30f6ba71007b80067efb5187b5d38367bed461ed74e239002a800003434c87b5d38806005f6e75187b5d38807bed8aa30f6ba711c808005461ed74e200180b7
  | 7, 0, 2 => 0x5f6a30f6bb1d38807bed468f0f6bb2d38808cfdf6a30f6ba71001b80067f295187b5d38807bed464d0f82b5d38808000032d5187b5d38806000021ed74e200180b6005f6a30f81a711280700002fb5186b5d38806005f6a3036ba710010700686a30f6ba71000b7005f6a30f6ba71002170067afb5187b5d38807005f6f95187a71001b7005fefb516ba7100107cfdf6a30f6bb1d38808
  | 7, 0, 3 => 0x5f6a2d74e22500107005f6a30f6ba2500497005f6a30f6ba0054277bed461f0a6ba7100498bed46750f6bb2d38808bede2a30f6ba71005b8bed46370f6ba7100538cfdf6a30f6ba71002a8005f6a30f6ba7100037005f6a30f6ba71001b70062efb5187b5d38807005f6a35087b5d38807bed461ed74e25100538005f6a30f6ba7108807005f6a30f6ba7100147ca5f6a30f8635d38808
  | 7, 0, 4 => 0xca5f6a30f6bb1d38808005f6a30f6cb5d38807005f6a30f7135d38807c4df6a30f6ba710053800652fb5187b5d38367005f6a30f6ba8938807cd5f6a30f6ba7100538005f6d35187b5d38367bed461f0a81b5d38808005f6a30f6ba7120367bed461ed74e239000b8bed461ed76127100538005f6a30a6bb0938807bed461f036bb2d38808005f6a3056ba7100107bed461ed75e27100698
  | 7, 0, 5 => 0xc15f6a30f6ba71002a8005f6a30f6ba0054287ca5f6a30f6ba7100108beda6a30f6ba7100738ca5f6a30f6ba71001b8bed461ed74e24100738beda6a30f6ba7100108005f6a30f7435d38807beda6a30f6ba71001b8bed461ed74e241001080066aa30f6bb2d38807005f6a30f6ba71001f7bed461ed74e241001b8005f6a30f6ba706c0c7005f6f9516ba71005b7005f6a30f6ba7100157
  | 7, 0, 6 => 0xbed461ed74e200e60c8005f6a30f6ba71003f7005f6a31487a71001b7bed461ed74e200200c800002fb5187a706c1b6bed461ed74e200360c8bed461ed74e241002a8bed461ef66bb0938808005f6a30f6ba711e807005f6a30f6ba71006f7bed461f0a6ba7112808005f6a30f84b5d38807bede2a30f6bb0938808005f6a33a6ba711c807005f6a30f6ba713480700646a30f6ba7120807
  | 7, 0, 7 => 0x5f6a30f6ba710078700687295187b5d38807005f6a30f4e20036107bedf2a30f81b5d38808005461f036ba71000b7bed461ed74e25100698bed461ed74e200540c8005f61ed763a71000c700546750f6ba71000b7bedf2a30f6ba7100498005f61ed74ea71000c7005461ed74e200920b7bed461ed74e251005b800002fb0f6ba706c0c6005f6a30f63a71001b7005f6a2d74e200a6107
  | 7, 0, 8 => 0xbed52a30f6ba71002a8bed461ed765a7100538005f6a30f4e200541b7cd5f6a30f6ba71005b8005f6f1516ba7100107005f6210f6ba71000c7bed46350f6ba7100498005f6a30f6ba7100327005f61ed74e200e60c7005f6a30f79b5d38807bed463b0f6ba7100698005f61ed74e200200c7bed461ed74e200a64d8005f61ed74e200360c7d0df6a30f6ba7100108005f6a30f4e200e61b7
  | 7, 0, 9 => 0xbed461ed74e241000b8005f6990f6ba71000c7bed462d0f6ba71002a8bedf2a30f6ba7112808bed461ed76127128808005f6a30f4e20036157005461f056ba71000b7005461ed74e225000b7005f61ed74e200540c7cd5f6a30f6ba710069800002fb5187b1938806bed461ed74e2250a808005f6a30f6ba71004f7bed461f0a6ba7100538005f6a30f51271001b7bed461ed76127100698
  | 7, 0, 10 => 0x5f6a30f6ba0054107005f6a30f6ba7100177bede2a30f8535d38808005f6a30f8035d38807bed461ed74e239000c8bede2a30f6bb2d38808005f6a30f6ba005429700676fb5187b5d38807005f6a30f6bb1d002a7ca5f6a30f6ba711c808005f61ed96ba71000c7005f6a30f6ba7100437beda6a30f6ba711c808beda6a30f6ba71000b8bed461f037cb5d38808bed461ed74e2411c808
  | 7, 0, 11 => 0x5f61ed74e239000c7005f61ed74e200180b7cfdf6d35187b5d3880800002a33287b5d38806bed461ed763a7100498005f6a30f81b5d38367cfdf6a30f6ba712080800002a34187b5d38806005f6a2d74e25100107005f6a33a87b5d38367005f6a30f4e200360b7bed461ed74e2250e808005461ed74e20016077005f6a2d74e200d2107cd5f6a30f6bb0938808005f6a2d74e200b6107
  | 7, 0, 12 => 0x5f6a30f6127112807005f6a2d7612710010700652fb5187b5d38807bed46750f6ba71001b8bed461ed74e20092108005f6a30f6bae138807bed461ed74e200921b8005f6a30f6ba71208070063efb5187b5d38807005f6a30f6ba7126807bed461f036bb1d388080060afb5187b5d38807bed46750f6bb1d3880800002fb5187b5d38726005f6a34c87b5d002a70065afb5187b5d38807
  | 7, 0, 13 => 0xbed461ed763a71128080067efb5187a71001b7cd5f6a30f6ba7132808005f6a30f82b5d38367005f6a30f6ba7112367bed461ed74e200922a8cf5f6a30f82b5d38808bed461f036ba7100738bed461ed74e20092468005f6a30f6ba71368070066afb516ba7100107bed461f0a6ba7100698005f6a30f86b5d38807bed461f036ba7100108bed46750f6ba7100738bed46994787b5d38808
  | 7, 0, 14 => 0x2fb5187c0d12806bed46450f6ba7112808c8df6a30f6ba712080800002fb0f6ba71000c6bed461f056ba7100738bed461ed74e22500738bed461ed74e22500108bed461ed765b0938808005f6a30f4e20036177bed461f056ba71001b8bed461ed74e225001b800002fb5187a71001b6005f6a2d74e239005b70067efb0f6ba71000c7bed461ee26ba7100498005f6cb5187b5d38807
  | 7, 0, 15 => 0x67efb516ba71005b70067efb5187b5d002a7bed461f036ba71000b8bedf2a30f6ba712880800002fb5187b5d38656005f6d35187a71001b7bed46750f6ba71000b800003355187b2d38806005f6a30f4e241001b7bed461ed74e23900498bed461ed74e200920b800002fb519b35d38806005f6d30f6ba7120807ca5f6a30f6ba71000c8005f6a30f6ba7100417005461ed74e200b60b7
  | 7, 1, 0 => 0xcfdf6a30f81b5d388080060afb5187b5d002a700002fb0f4e200360c6bede2a30f6ba7100108bed461edd6ba71002a8cfdf6a30f6ba7100498bed461f056ba71000b8bed461ed74e225000b8005f6a30f6ba71001a7005461ed761271000b7bed461eee6ba7100698bed461ef86ba711c808bed461ed74e200a6108005f6a2d765a7100107005f6a30f6ba710058700652fb5187a71001b7
  | 7, 1, 1 => 0xcfdf6a30f6ba7112808ca5f6a34787b5d38808beda6a34787b5d38808bed468f0f6ba7120808bed461ed763a71005b8005f6a30f7c35d38807bed461ed74e200a63f800652fb5187b5d002a7005f6a30f81b5d38807005f6a30f7e35d38807005f6d35187b5d002a7005fefb5187b5d38807005f6a30f6ba41002a7005f6d70f6bb0938807bed461ed74e2250032800002fb519d35d1c806
  | 7, 1, 2 => 0x2fb0f6ba00540c6bed461f036ba7120808005f6a30f6bb4d38807005f6a30f82b5d38807beda6a30f6ba710049800002fb5187a00541b6005f6a30f6ba7112807bed461ed74e200d2108bed461ed74e200d21b8bed461ed763a712880800662a30f6bb1d38807005461ed74e20016047c5df6a30f6ba7100698bed461ed74e200b61b8005f6a30f6ba7128367005f6a30f6ba70b6497
  | 7, 1, 3 => 0x5f6a30f6bab138897d0df6a33a87b5d38808005f6a30f81a71001b7005f6a30f6ba71007e7005f6a33a87a71001b7beda6a30f6ba7112808005f6a30f6ba7100077005f6a30f4e200921b7cfdf6a30f6ba7100538c7df6a30f6ba7112808bed461ed74e251002a8005f68f0f6ba71000c7bed461ed74e200a64f8005f6a31687b5d002a7bed461ed74e25100108bed461ed74e251001b8
  | 7, 1, 4 => 0x5f6a30f8535d38367005f6a30f6ba00922a7ca5f6a30f6ba7100538bed461f036ba7100588beda6a30f6ba7100538005f6a33f87b5d38807bed461ed74e24100538bed461ed74e2511c808005f6a30f82a71001b7005f6a30f4e225001b7005f2a30f6ba71000b7005f61f056ba7120807bed461ed74e200b60b8bed461ed74e20092418bed46990f6bb0938808005461ed74e20016067
  | 7, 1, 5 => 0x5f6a33a6bb0938807bed461f036ba7100498bed46750f6ba7100498bed461f0a6ba71002a8ca5f6f15187b5d38808005f6a30f6ba7100727cfdf6a30f6ba7100698bed461f0a6ba71001b8bed461ed765a710010800002fb5197b5d3880600652a30f6bb2d38807bed461f037f35d38808005f6a34c6ba7100107bed461ed74e22500418005f6a30f6bb0538807005f6a33a87b5d002a7
  | 7, 1, 6 => 0xbedf2a30f6ba71001b8bed46750f6ba711280800626fb5187b5d38807cc5f6a30f6bb1d38808005461ed74e200360b7bed461f056ba7100498bed461ed74e22500498beda6a30f6ba71005b8005461ed763a71000b7005f6a30f6ba70d25b7005f6f95187b5d3836700002a30f6ba706c0b600686a30f8535d38807005f6a33b87b5d3880700002fb6987b5d2080600003315187b5d38806
  | 7, 1, 7 => 0x5f6a30f6ba7100687bed46750f6ba71005380067ea30f6ba7100737cd5f6a30f86b5d38808005f6a30f6ba7100137bed461f056ba7112808005f6a30f4e200d21b7cd5f6a30f6ba7120808bed461ed76127120808005f6a30f4e200b61b700002fb2487b5d38806005f61ed74e24100697005f6a30f6ba7100187bedf2a30f6ba7100738bed461f0581b5d38808bed461f036ba7112808
  | 7, 1, 8 => 0xbed46990f6ba7100108005f6a30f6ba71003d7bed461f036ba71005b8005f6a30f6bb193880700002fad74e200200c6bed461ed74e200541b8beda6a30f6bb2d38808bed461ed74e200e61b8005f6a30f6ba51002a7bede2a33a87b5d38808005f6a30f6ba706c1b70066afb0f6ba71000c7bedf2a30f6ba71000b8005f6a2d74e24100107005f6a30f6bb1d38367005f6a30f6ba7100047
  | 7, 1, 9 => 0xbed461ed763a711c808bed461ed74e225005b8005f6a30f6ba706c0b700662fb5187b5d3880700002a30f6ba71000b6
  | 8, 0, 0 => 0xbed46750f6ba7100f7da8c3dae9c40125c017d87b5d3880063002fb5187a71001b6ca5f6a30f6ba7100f7db4d461ed74e201efb5187b5d3890403802fb5187b5d38806cfdf6a30f6ba7100f7da8c3dae9c4002defb51a643dae9c403df6a30f6ba7100737bed461ed74e20020f7da8c3dae9c4006defb5187b5d8e9c403802fb5187b5d38366
  | 8, 0, 1 => 0x17dbe5461ed74e201c015187b5d388005b5f6a30f6ba7128807bed461ed74e200b6f7da8c3e0ad74e201efb5187b5d3889403df6a30f81b5d38807
  | 9, 0, 0 => 0x2fb5187b5d38806
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
  | 0, 0 => 0x7f03f0000000060e30fe0000001818efd00000007c4de300000067e71020000001ffcfff0000001f1ffff0000001f1cf01
  | 0, 1 => 0x70c1c00e30fe06337b00c4de3073fff80e7fff000fff8003fff0000007ffffff0000007ffcefd0000007ffc0000000007f1bffd
  | 0, 2 => 0x30c3839818e0100337b0704de30033630704d01083060070410007ffff80fffff07ffe000fff0007f01f9ffcfff07f01f80fc0ff
  | 0, 3 => 0x38ffff9f1ffff38fc1c1f1f0fe38ffff9f1ff0338f3e39f1ffff38f3e39f1cf0138f0001f1c00038c3e39f18f013803e01f00f00
  | 0, 4 => 0xc80c606703100c70c1c60e30fec70c1c60e30fec70c1c60e300206337b07c4d0306337b07c4de33ff3ff9ffcfff3ff0001ffc000
  | 0, 5 => 0xcf3383e7e4efdcf3fffe7e7f03cf3c7fe7e71ffcf3c7c7ffff03cf3c7c67e7fffcf3c7c67e7102cf3c7c0000000cf300067e4000
  | 0, 6 => 0xf9cc84f83bffff9cc84f83b21cc70c1c60e30fe30c3839818e1d30c08398182fdfffffffffff03f7cf9ff8fbe03cffc7fe7ff1ff
  | 0, 7 => 0xf9ffe7ff3ff1df9fce4ff3f31cfffc9ff8ff2fffffc9cf8ff21ef9ccfcf83b31ef9cfe7f83bf1df9cc9ff83b2fff9cc84ffff31e
  | 0, 8 => 0x30300000e000030300000000003000000c0000000000000e000000000000000003000000c0000000000000e0fffffffffff1f
  | 0, 9 => 0x6000000c000000000000000e0000000000000038f3e39f1cfe10033630704de100037b0000de30003030000ce10003030000000
  | 0, 10 => 0x6031b00c00e206001800c00e206031800c0ce206037b00c0de306001800c00e206001800c000006000000c000006000000c00e0
  | 0, 11 => 0x3030700ce100000007000e0000000070000000000007000000003600700d000000000700000000000070000006031b00c0ce3
  | 0, 12 => 0x6037800c00e206001807c00e20003630700de10003630000ce10003630000ce100036300000000003600700de00003600700d00
  | 0, 13 => 0x6301807c40e206301800c00e2063018000000006300007c400006330307c4ce106307807c410206300007c400006037807c0de2
  | 0, 14 => 0x6337b0000c0006337b00000e006337b0704d0106337b00c40e306337b000000006336007c4d0006336007c40000633600000000
  | 0, 15 => 0x6337b07c400006337b0700d0006337b070000006337b00c0ce306337b00c00e206337b00c000006337b000000006337b0000ce1
  | 1, 0 => 0xcf3c7c67e7102cf3f7c67e7d023ef3fb9f1cf0106337b07c4de3
  | 1, 1 => 0x3003801800efc3003801800e00300000180000008306007041fc00c00380180fd0003838000efd00000000000fc0000000000000
  | 1, 2 => 0x30c383800000030c383800000030c3838000c0030c383800000030c3801818e0030c00018180fc30c000000000030c0001818000
  | 1, 3 => 0x38f3e39f1cf0138f0001f1c00030cfff981bfff30c3839818efd30c383981800030c3839800e0030c38380000fc30c3838000000
  | 1, 4 => 0x6001800000fc06000000c00fc06000000c00fc00000000000fcf9cc84f83b2fc38f3e39f1cffd38f3e39f1cf0138f3e38000000
  | 1, 5 => 0x36c39b98d8eff36c01818d80e230c3839818efd06337b07c4dff06337b00000fc06336007c4dfc06300007c40fc0003600700dfc
  | 1, 6 => 0x30c3e3800000030c3e38700d0030c3e3800000030c3e01f18f0030c3601f18d0030c0001f180003633fb1800e003633801fc4e00
  | 1, 7 => 0x36f3e39fdcffd36f39b9fdceff36f39b800000036f3839fdcefd36f38387c400036f383800000036f000181800030c3e39f18ffd
  | 1, 8 => 0xc7000060e0000c00c0060030fcc00c0000000fcc0000060000fcc00fffe003fffc00c006003000c00000600000036f3fb9818efd
  | 1, 9 => 0xc70c1c60e3002c70c1c1f1cf01c70c1c00e00fec70c1c00030fec70c1c0000000c70c0060e3000c7000060e00fcc7000000000fc
  | 1, 10 => 0xc70c1c60e30fec70c1c60e0000c70c1c6003000c70c1c6000000c70c1c00000fcc70c1c0000000c70c1c0000000c70c1c00000e0
  | 1, 11 => 0xc7030360e0ce1c00f036003ce1cf3c7c67e71fecf3c7c0000000cf3c7c67e7102c7fc1fe0ff0ffc70fffe0e3fffc70fff8003fff
  | 1, 12 => 0xc7036067e0d00c00c006703000c63f7b6003000c63c0067c7000c00c006703000c70f1f60e3cffc70f1f0000ce1c70c1c60e30fe
  | 1, 13 => 0xc73f7c0000000c73c1c67e70fec73c1c67e4000c73c1c07c4000c73c0067e7000c70f7f67e3dffc7000067e0000c70f7c67e3dfe
  | 1, 14 => 0xf7038078e0e00f0cf83f81befdf0cf83e003000f0cc00781b000f00f807803e00c73f7f60e30fec73f7f60e0000c73f7f6003000
  | 1, 15 => 0xf7cf9f9818efdf7cf9f8000000f7cf8078fbe00f7cc1c78fb0fef7c383f8f8efdf7c383e0e0000f7c00078f8000f70f9c78e3efe
  | 2, 0 => 0xf80c006003000f803807f00e00f800007f00000f0cc007f1b000f7cf9ff8fbefff7cf9ff8f8000f7cf9ff803e00f7cf9fe0e30fe
  | 2, 1 => 0xf80fe07f03f00f80fe07803e00f80fe06003000f80fe01800e00f80fe01800000f80fe00000000f80c007f03000f80c007803000
  | 2, 2 => 0xf803037f00ce1ff3ffc7fe7f02ff3ffc67e7102f8ffe3ff1ff01f8ffe39f1cf01f8f3e3ff1cf01f8cfe3ff1bf01f80fffff03fff
  | 2, 3 => 0xf800007f000fcfe3ff87fc7fe2fe3fe07fc7f00fe337b7f00000fe0ff87fc3fe2f80fe37f03fe1f80fe37f03f00f80fe30000ce1
  | 2, 4 => 0xf8cc00781b000f8c383ff18efdf8c3838000000f8c0007f18000f8c0001818000f80fe07f03ffcf80fe000000fcf80fe00000000
  | 2, 5 => 0xf8cfe07f1bf00f8cfe0781b000f8cfe06003000f8cfe01818000f8cf83ff03000f8cc007f1b0fcf8cc007f03000f8cc007f1b000
  | 2, 6 => 0xf8cfe3ff03f00f8cfe3ff03f00f8cfe3f81b000f8cfe3e003000f8cfe39818efdf8cfe38000000f8cfe07f1bffcf8cfe00000000
  | 2, 7 => 0xff0c1c7fe30feff0c1c7f00000ff0c1c0000000ff03807fe0efcff00007fe0000f8cfe3ff1bffdf8cfe3ff1bf00f8cfe3ff18000
  | 2, 8 => 0xff0ffc7fe3ffeff0ffc7fe0000ff0ffc60e30feff0ffc6003000ff0ffc1800efcff0ffc1800000ff0ffc0000000ff0fe07fe3f00
  | 2, 9 => 0xfff00060e0000fff0001818000fff0001800000fff0000000000ffcffc1818000ffcfe3e0e0000ffcc1c7ffb0feffcc1c0000000
  | 2, 10 => 0xfff01800c00e2fff0007ffc000fff3030000ce1fffc7c7fff102fff3e3fffcf01fff01f8000000fff0007ffc000fff0007f00000
  | 2, 11 => 0xfff0007ffc000fff00000000fcfff0000000000fff0007ffc000fff3637ffcde1fff3607ffcd00fff3600700d00fff0187ffc000
  | 2, 12 => 0xfff383e0e00fcfff383e000000fff3839818efdfff3839800e00fff3838000000fff3807ffce00fff3801800e00fff0007ffc0fc
  | 2, 13 => 0xfffc1c1800000fffc1c0000000fffc007fff0fcfffc007ffc000fffc007fff000fffc006003000fff383fffcefdfff383ff00e00
  | 2, 14 => 0xfffc1c7fff000fffc1c7ffc000fffc1c7f03000fffc1c78fb0fefffc1c60e30fefffc1c6003000fffc1c18180fcfffc1c1818000
  | 2, 15 => 0xffffff80fc0ffffffff8003fffffffff8000000ffffe07ffff00ffffe07f1bf00ffffe060e3000ffffe01818e00fffc1c7fff0fe
  | 3, 0 => 0xffffff80c0000ffffff8000000ffffff8000ce1ffffff8000000ffffff8000c00ffffffe7e7102ffffffe0e3002ffffff9f1cf01
  | 3, 1 => 0xffffff80000fcffffff8000000ffffff87c4d00ffffff87c40e2ffffff87c4000ffffff8700de1ffffff80c00e2ffffff80c0000
  | 3, 2 => 0xffffffe000000ffffffe003000ffffffe000000ffffff9818efdffffff9818e00ffffff98180fcffffff9818000ffffff9800e00
  | 3, 3 => 0xffffffff03f00ffffffff00000fffffff8fbefffffffff8f8000fffffff803e00ffffffe0e30feffffffe0e3000ffffffe0e0000
  | 3, 4 => 0xfffffffffc000ffffffff18000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7b83f2600000072f376e000000597ee6d0000002bcdd630000002281102000000097c849000000090ff27000000090c801
  | 0, 1 => 0x38dbd80737fe02553b004d5e3000dbd80037b6000dbd80037b60000007bfff6f0000007bfee6d0000007bfc8490000007bfff6f
  | 0, 2 => 0x105202090c80118777b0d0dda31872420d0c801082040040000003ddbf807f7ff03ddb2007f76f03d00f897c8d903d00f807c0d9
  | 0, 3 => 0x187fff8d0ffb7187fff8d0ffb71876720d0d9031872420d0ff271872420d0c8011872420d0c8011872420d0c8011822400d00800
  | 0, 4 => 0x4c2470268110247843da2f11da440dbda2837b644043022811025c76722f8d9034c257926815a21bf24f8d7c8d91bf2420d7c849
  | 0, 5 => 0x4c29cda6826b44c247026811024c247da6811924c24702f8d9034c247026837264c247026811024c247004000004c20402680000
  | 0, 6 => 0xa18884d03373ea18884d03221ca3888dd0722dcb1da86d93ea1da3d88fd07e2dd5c76722f8d9035456322b8d9034ff47fa6fd1db
  | 0, 7 => 0xb9fac6dd3ea1da9a8c4d43221ca3d88fd07e2dda18884d03221ca18cb4d03331ea18884d03221ca1888dd03229ca18884f2b331e
  | 0, 8 => 0x12530b00404e012530b0000080125302094cc6112530b094cce1125202094c8411003000900c2002010900404e0fdfef6ffbfb1f
  | 0, 9 => 0x46000022c004046053922c15e244053022815221a734b0d4cce11a734b0d4cce112573b094dde312530b094cce112530b094c8c1
  | 0, 10 => 0x56573b22c15e256573b2bcdde35607392bc1de246053922c15e246053922c15e246053922c00c046053022c156246010922c04e0
  | 0, 11 => 0x5e777b2fcdde35e777b2fcdde35e77722fcdd635e72422fcc8415c27702f81d225c27702f81d225c22402f8080056573b2bcdde3
  | 0, 12 => 0x5e277926c15e25e27792fc1de25e777b2fcdde35e777b2fcdde35e777b0d4cce15e777b04000805e777b2fcdde35e77722fcdd63
  | 0, 13 => 0x5e777b2fcdde35e777b2fcdde35e777b04000805e77722fcdd635e734b2fccce15e76722fcd9435e72422fcc8415e27792fc1de2
  | 0, 14 => 0x5e777b0d00ca05e777b04404e05e777b0d0c8815e777b044c0c15e777b04000805e77722fcdd635e77722fcdd635e77720400000
  | 0, 15 => 0x5e777b2fcc8c15e777b2f81da25e777b2f808805e777b2fcdde35e777b26c15e25e777b26c00c05e777b26815a25e777b0d4cce1
  | 1, 0 => 0xa3898d8000090a38980507266ca380005070048a0098050026245e76722fcd9435c27702f81d225e777b0d0c8815e777b2fcdde3
  | 1, 1 => 0xb38b8dd972efcb00b805902e24b00b805902e24aba9cdd4726fca3d98fd07e6fda3898dd0726fca3898dd0726fca3898dd0700d8
  | 1, 2 => 0xb3db8fd0026b4b3db8f894c8d1b3db8f8900cb0b3db8f8000090b3db82597ee6db3db8fd97eefdb3db8f8000090b3d202597c849
  | 1, 3 => 0xbbf2425d7c849bbf2425d7c849b3dfbfd97ffffb3db8fd97eefdb3db8fd97c8d9b3db8fd902eb4b3db8fd0726fcb3db8fd0700d8
  | 1, 4 => 0xe78dbdd0726fce78dbdf2f37fee7898df2f26fce78dbdf2f37fea3898dd0726fcbbfbcfdd7eefdbbfbcf8d0c891bbfbcf8400090
  | 1, 5 => 0xf7dfbffbffffff7d73b7bfddebf7dfbffbffffffffffffffffffffffffd4726fcffffffffffffffffbcffffeefdffaffdfff3ffe
  | 1, 6 => 0xfffffff6837b6ffffffaf81db2ffffff8400090fffff27ffff6ffff7727ffdd6bfff2427ffc849fe7ffb5d02ea4fe7bc27fcee65
  | 1, 7 => 0xffffffffffffffffffffffffffffffff8400090fffbcffffeefdfffbcfafcc8d1fffbcf8400090fff2425d7c849fffffffffffff
  | 1, 8 => 0xe7800072f0048e78dbdf2f37fee78dbdd0726fce7898df2f26fce40dbdf2837b6e40db07283726e400007280000ffffffdd7eefd
  | 1, 9 => 0xe78dbda281192e78dbd890c891e78dbd80700d8e78dbd80037b6e78dbd8000090e78db072f376ee7898df2f26fce7898dd0726fc
  | 1, 10 => 0xe78dbdf2f37fee78dbdf2f00d8e78dbdf2837b6e78dbdf280090e78dbdd0726fce78dbdd0700d8e78dbdd0026b4e78dbd80404f0
  | 1, 11 => 0xf7d30b7bfcce9f65fbb7bcffe7efadfdf6f37feefadfd8400090efa47076f114ae7ddbff2ff7ffe78dbdf2f37fee78dbd80037b6
  | 1, 12 => 0xffa7707ff1d6afffff27ffff6ffe7ffb76837a6fe7ff27fcff67fc2ff07f83f26f7dfbffbffffff7dfbf894ccf1f7dfbffbfffff
  | 1, 13 => 0xffffff8400090ffffffffffffffffffffffc8d9ffffffafcc8d1fffff27ffff6fffffffffffffffff2427ffc849ffaffdfff3ffe
  | 1, 14 => 0xf78b807bf2e6cf7dfbffbffffff7dfbff2837b6f7dfb27bfff6ff40fb07b83f26fffffff6f37fefffffff6f00d8fffffff6837b6
  | 1, 15 => 0xf7dfbfd97eefdf7dfbf8000090f7dfb27bfff6ff7dfbffbffffff7db8ffbfeefdf7db8ff2f00d8f7d2027bfc849f78fbdfbf3ffe
  | 2, 0 => 0xfc2ff07683726fc2bc07f82e24fc22407f80800fffff27ffff6ff7dfbffbffffff7dfbffbfc8d9f7dfbffb83fb6f7dfbff2f37fe
  | 2, 1 => 0xfc2ff07f83f26fc2ff07f83f26fc2ff07683726fc2ff05d02e24fc2ff05d00800fc2ff00400000fc2ff07f83f26fc2ff07f83f26
  | 2, 2 => 0xfe734b7fccce1fc2ff07f83f26fc2ff02681102fc7ff27f8ff27fc7ff20d0c801fc72427f8c801fc7ff27f8ff27fc2ffdff83fb6
  | 2, 3 => 0xffabcdfff2efcfe7ffb7fcffe7fe7ff27fcff67fe777b7f80880fe2ff97fc3fe6fe7ffb7fcffe7fe7ffb7f83fa6fe7ffb0d4cce1
  | 2, 4 => 0xfffff27ffff6ffffbcffffeefdfffbcf8400090fff2427ffc849fff2425d7c849ffaffdfff3ffeffaffdd4726fcffaffd8400090
  | 2, 5 => 0xfffff27ffff6ffffff27ffff6ffffff276f376efffff25d7c849ffffffff83fb6fffffffffffffffffffff83fb6fffff27ffff6f
  | 2, 6 => 0xfffffffff3ffeffffffff83fb6ffffffffffffffffffff6837b6ffffffdd7eefdffffff8400090fffffffffffffffffff8400090
  | 2, 7 => 0xffaffdfff3ffeffaffdff80890ffaffd8400090ffabcdfff2efcffa2407ff0848fffffffffffffffffffffffffffffffffffc8d9
  | 2, 8 => 0xffaffdfff3ffeffaffdfff08d8ffaffdf6f37feffaffdf6837b6ffaffddd72efcffaffddd708d8ffaffd8400090ffaff07ff3f6e
  | 2, 9 => 0xfff24276f0048fff2425d7c849fff2425d00800fff2420400000ffffffdd7c8d9fffffff6f00d8fffffffffffffffffff8400090
  | 2, 10 => 0xfff77b26c15e2fff7727ffdd6bfff34b0d4cce1fff6727ffd94bfff2427ffc849fff24f8400090fff2427ffc849fff2427f80800
  | 2, 11 => 0xfffbcffffc8d9fffbcfd4726fcfffbcf8400090fffbc27ffee6dfff77b7ffddebfff7727ffdd6bfff7722f81d22fff77b7ffc8c9
  | 2, 12 => 0xfffbcff6f26fcfffbcff6826b4fffbcfdd7eefdfffbcfdd02eb4fffbcf8400090fffbc27ffee6dfffbc25d02e24fffbcffffeefd
  | 2, 13 => 0xffffffdd02eb4ffffff8400090ffffffffffffffffffffffc8d9fffff27ffff6ffffff27683726fffbcffffeefdfffbcfff82eb4
  | 2, 14 => 0xffffffffffffffffffffffc8d9ffffffff83fb6ffffffffffffffffffff6f37fefffffff6837b6ffffffdd7eefdffffffdd7c8d9
  | 2, 15 => 0xffffff847c0d9ffffff84037b6ffffff8400090fffff27ffff6ffffff27ffff6ffffff276f376efffff25d7ee6dfffffffffffff
  | 3, 0 => 0xffffffa6c00d0ffffffa6815b2ffffff8d4ccf1ffffff8d4c8d1ffffff8d00cb0ffffffa681192ffffffa681192ffffff8d0c891
  | 3, 1 => 0xffffffd4726fcffffffd4026b4ffffffafcddf3ffffffafcddf3ffffffafcc8d1ffffffafcddf3ffffffa6c15f2ffffffa6c15f2
  | 3, 2 => 0xfffffff6f00d8fffffff6837b6fffffff680090ffffffdd7eefdffffffdd7eefdffffffdd7eefdffffffdd7c8d9ffffffdd02eb4
  | 3, 3 => 0xffffffff83fb6ffffffff80890ffffffffffffffffffffffc8d9ffffffff83fb6fffffff6f37fefffffff6f37fefffffff6f00d8
  | 3, 4 => 0xfffffffffc8d9fffffffffc8d9
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 52 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 52 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 418 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 418 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 418 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 418 then wireAt i else 0
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
  | 3 => 4
  | 4 => 41
  | 5 => 579
  | 6 => 1483
  | 7 => 438
  | 8 => 4
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0x6d926fbb6603006e4338906800e850fe
  | 4, 0 => 0xdf74ac10cf67bc27c785cbf7b975c19fb88f8c6cb1093d61acef58a09e82f3649d7ea98f95993efa852ea5df7aff52b474faebed6e426d555b0a2f4f56886eca4eaf82744e99c3464e3aad4b4bfb957a4ade36054a31fdc149d0a17644237b1b3ff513d53aa565e835a956d0351be62325432154232ee17021cfd93f1ec3f1431cc563371c00683e13fe1e5613d2bc141308af2c0cda0bba0c84e73b031a757e01d5fa33
  | 5, 0 => 0xf2b8b8d0ea1bc0a0e7ddf9c0e4a76f20d97fb330cad16120c645dec0c405bc60bb5b40f0b77be9e0b7002330b66e0330a41d8c40a3d4f150a38fd090a14064f09c5e5d20990730609681be60956336f0955e87808ede8fa08b222d40863db9b085f7171080e30f807c75c36079e46270772bb3e075140fd074cee0b0748db5e072852b906fa4a3206f72c610677ec9c065188e1064ddc5a0622fe19061ff0230605f16d0541786f0502053c04c5847804bd0d2a04acf97f047e89c50436ec830416c3180415b2f303d8385d0352a55e03403ad702ec2c5402cc506b02b90b3802a072960221b684015437cd01373cfc01013f3600e3021600ce9089007d93d8
  | 5, 1 => 0x1e0daafc1de9f1cc1de8ac961db72cc41d90a3691d7826551ca7aa811c6d40e31c4aae911c3d20d71b95e62c1b5300e41b3ab7121a787e0d1a4e06791a2f8ff21a13e99e1a0e0e301a08cdef18f26c4c18d42f2c18cd36911828bb3817b9de51175fb2e61749d95516cb578b16b6ee5b168fc54f16808cef1658de3315bc22d814f6ad4b14c287d114b6577e14969591147df099144f729613b8cc28133ae9cc1324f70012fc993212f99c3c12eccffb12d0695312ad1cd1122cdb6911eff488119f84ea119dfe10118ba122116a8758115889ff10c8c50d109faa42106bad28101b721b0fe749af0fe3d2ed0fda79110fbd0d270faa77070f46fe910f446214
  | 5, 2 => 0x32854531324a8d1031de776a31c32dd1318c912931813652317a69f63069d1f9303aa5a3302bf8fc2f8deb682f242cf22ed86dec2e7dd00a2e2cebd12dff29252d6dce4f2d6b081b2d22afae2c188cc22b71f0412b6e1af02abe16482ab3915a2a9f240b2a3198e02a2ac81c2a2573462a180b4c29995dc3292379a528b65c962802e9c9275177ee26d89cc1266f0cb2262cbf962616581725f712e9259edca6255cc07925140cb424bc460324b4175d23a7002b237d7862234c018c2318f396226203f922599745220f6ca4220e56f8220d430721fc0fee2077d85c2075da641fd50f721fb4d5ec1f7099581f4321541f426e131ebe34261e77a35a1e400894
  | 5, 3 => 0x44b40a21448a1be4446842f34442d4e14414224c43f4eb1443d1a48743947f124378d237435d8a9443516ea6431a711442dd039442b779a342aa2f094274e34b42590cb5422b3cc04176068d40aaf52140a6c27d40722d16405ec65a4046e2bb3fecc9063f22b8393f0371bc3efb0da43ee0318d3e16ad7a3df25cd43d58882c3d253d6d3c61985c3bc70d473b8cc8883b6273ae3b0f2c583a71b75339d021a7399a9e2c38ced832386b233a37b9fc1b3779d4de36f4c4b6366449c736590d6b3647c4cb362f22d635f99b9635ecb95535e38d4f35df008035abd13a356728f63566e80b34d3193134a369a7342facf533feb98933673ef03313c2a133036cac
  | 5, 4 => 0x5dfff3c65dcbbee45d9849c45d9278095d76ae0a5cee05275cd3dd1c5c4eedba5afa89cc5a72e5015a292fbd59dd50c859be44955944e18d5931c1115901c7ff58f528b75899c2a556c160f056811f7b566c726d559bfa53556f069554f25555541df39b53f3d92253bbdb1453b8fa54539234c4532879d05318541d5263178f520bcc1b519fb45c514adeb45130d9bc506c7ad0501d2ed74e29c7d14e1eb31a4e190b6e4d74a6104c6c32f94c5e0b844c33661d4b9af8c44b83735c4afed5a04ae0a75d4acd3e544a9560054a3290774a286d454a24047e499e6f6d492957c04843c42147ece91247b4abff47b3b3d645696f5b4545237444d3714444bfc70a
  | 5, 5 => 0x761e2a87761a7a5175e4f86d7594f423758ebedc753dbe26751113a074fcb1d374540656743087d1738fc095732cd8d9721abd7371a7a8897123e9af709ea2966f8795176f595e3a6ef98cb76e9a1b496e85ad376e5661bc6d86b5166cac9bb66c32974e6bd6b7e36aa264eb69e46dbf69d0a4b06991e768697dbe0a6971083c68742b92681fc87867f3fbbd67db820d6766c32b67453cc96705e3da66b3495666b2689466232256656acfb06502386063d77c0f6374a07263669d95634d5ef6632407c2630946fe6288094d625a27916226b9cb6215319461fa3a1e611f9d876101905a60eac9c35fcfff465f9873005f9791165ecae9965e91f2235e3b004e
  | 5, 6 => 0x8cde74b08cd1964a8cb445068ba2856b8b5188dd8b2527288ad061938acdc36389bf0ebf892ed109887b7faa87cb71cc87657c6187258838867d560586743438854ecaa48522d06f84e54b5e849fed47845407c9842ac024841977848327705e81c1d1c681408b0480edd4f080db56f4806558a88049a0dd800963637fc339537ef470087e1a3ff27de2b05b7d8ecad87d80b13a7d2ffe037ced496e7cd1d33c7c8831a27c8488987c7a122e7c73ef427c347e527c2f9e497bf6635c7b9865cb7b2bb8847b2b17a17aa362b27a6b3b7a7a6ae8b179bfb22979a5b36c79019a1d78f1ec4678ea2e5878bd6f8178a7b60178966d61783204ae7774639376ebe5b9
  | 5, 7 => 0xb15bcfd6b151cf00b0fe9586b03d009faf018d0daef9a5d8ad83e4eaacc7bd95ac3102f8ab30f7eaaa879d64aa58d6bda98670d0a97f6571a92d2c39a82aaacea7e64ccca72ca08ba6fe2278a6846df0a5bbb548a4ffb119a3d30303a393d6f5a3718c5ba3308952a2f8a3c1a240fb08a1e94f4da10fab86a0ec493ea09b5bdd9f7a1a3e9f1af27e9e27409b9dab815d9d87a64e9d451bee9d302a159d062dcd9b5ee1c59b5c78ff9b3436919addb7b8993824c79908f6739742e10597301eb69651cd1b96114c95952030b394f22956942d1aaf9420cb5f93fd123c9367ed2090c62f3590839ba29067b4048f95bdff8e2f3ed68de2a4938d5a4ec18d01eeb8
  | 5, 8 => 0xf7fa745bf47b8ceeeddd5066edac53a1ec3dd694eab52b64e82c56a1e3584c78e2cad771e2c48151e02b6c65de341c2bddc58adcdc230461d83dd7abd3f322a0d0530e8ed050066bcf66fc07ce7d2689cde2f3facd73df73cd404a96cd1a9dc6cc373e1ec9717ee9c8a99bdac82e2db5c7d65913c766c827c759db72c6a07237c4a58b79c4122956c39f608cc276f4edc23db151c1b919ffc01e2105c0188a3cbf3d75aebecd9540be9e609dbcbea3d5bc53e7dcbbec3344bbc46e34bb676267ba88bda4b9eab265b76b0c1fb729db6eb6ff990eb6eec924b6b9e4cbb6626367b5ca66d8b5406affb46eb9a3b413a94eb2f8b09db2d95111b2813c73b27b8782
  | 5, 9 => 0xfae3e393fa0fc86bf9870f85
  | 6, 0 => 0x5b10e6b057729b605725c9f05687e89054d1e15053cd7d1053c7a0b05169eb005124b8004d32ad804890ef5046ad0d10452788e0415b2f303f8e99a03f1b95203def96a0389d21f03856d13035a956503476202033a727c02e9d44b02c7a62002c1685702a27623029bda2f028da25d02898f5e02867f1c02734c9f0266dda80248132d0240dc180225f9ec01f5db9e01f2900401f00f2c01e3cad001e0d7df01c45ed601ad4403019cbfce0185f46d01652a32015e807f015842e8014fcec7014e28b6012a58400129b75501248fc7011f27fd01195bd5010ac53101013f3600f94cd000eff696007d93d8006fb9d3005b006f003e83f900296567000db973
  | 6, 1 => 0xb0896c40afb5dd30af6cb310af23e1b0ae34fac0ac986c50ac01d010abb903e0ab629b70aa7d1170aa769cf0aa0caca0aa03d900a9628be0a8213ec0a7d079a0a7677f50a689b530a6572fc0a4fed4e0a4bf36d0a3325db0a01f69909ede5f809ea0c3209da5e5409d8734909cc529509bd51ef09695d400938c9750938390c0901863008ffecd508fadadf08d6f02608c12dc408c00bc9087a815b0848694b0815b7f9080f361f080f15bc07c75c3607c25949078f1e53078c60020772bb3e073a22a106f6a3d806cd9ad406cd85b206c4413d06ad70f9068a399a0654018106493889063d52240617f3be05fc8ebd05f2ecc205f2790c05e77d7105bbae7e
  | 6, 2 => 0x1142fa41113ec3a41120d64610d89c4810c280c510a92875109faa42109d1e431087cb5e107b5734106ef598104ef361102d648a102d4a7a101f34a2101595880ff073950fec104b0fe0ac610fc7e3a30f8899180f76f4eb0f47a0390f3d84400f1c66040eee197d0ee672b50ee271f80edf18670ed86b730ecb2c040ebd30910e8414b20e7e15130e68420e0e5682a60dfb96ef0df124ef0de298690de1cc4b0ddd4aa00db51cee0da46fb90d9cbe430d9a92370d91ebc20d66037f0cfc43180cd88bf40c8ca9130c89d7430c83298b0c60dcf80c498d8c0c0bc1730bbdf1470bb2ffb10ba77e000b8ad6cc0b88cc090b82c4a10b2c8ce60b28f6400b1a7d63
  | 6, 3 => 0x17dbb70317aeb25017a228d0176c9a26175a929b1729918f172938d71712096e170ecd2616f36bf316bd508a16b4d972168bc85d167fda5b162e4ad216100cbf16066cd91606144c15f71c1b15f022ce15d3ee2015c35559158c470e1581f8c81574b12d1561a43a155ed0bb155cba4e14b6e9751486a38f1474a73714649f8f1437977c1413d60813e0e2a713dbc3bf13b3dc4e139b02df138cad001377feae136d10ac13604859133c08ef1330db9c1327faa11317dd2b130a5a8912baa67712b8ab4112ae5da3126ef838124d6d63123c1c3b1233466a1232479711c6cff811a579d6119b91ab119557c61187183a116b4724115d3eaf115b67ca115a7967
  | 6, 4 => 0x1d8190081d73f5661d70c9b71d5e20161d55e79b1d4a9d981cf670511cd584061cce2f151cbf657e1ca0b1831c9fd8f01c8f14451c8ebaa91c8373521c5d3d531c53915b1c4c15fd1c32bad41bee157b1bd1fa481bcc3d7d1bc5498a1bbaa2fd1bb1776b1ba64fad1b8a39d81b8548e61b7aa30b1b6624961b4b11361b264b181b02bfb21ae98c221ac4a36f1aaa51371a90e4691a8ffa5d1a87fcc01a4058c31a1f1cf019e220af19c2b1f0198fca60198eb56519856a8018f9443318f811bf18ef4baf18eed24c18e3fb0a18c91a2e18ab6b36189d699618787ffd1870ade618612faf185955ec1841fcce1839cef01835b7a618103f8818016c8017e170dd
  | 6, 5 => 0x237fdc38236b3365233e519822d85c9a22be9cac2278d29b226f1f9b226346d52263093522543c1c22521a04224581e022016d1d21fc0fee21e729ef21c107aa2183f1d2217c18ce21466fe220eebdc420e970f520e249a720d8285520a84c142089ff202064873a203ca24720257d1e2015ae6f2014c6442009a42c1ffd86e11ff58b481fb72b911faca62d1fa45a3f1fa432931f96513b1f8738591f4eac261f47d9851f3387171efda3231ee07af31ed20e051ebb13731eae27731e961c6a1e8465841e7be0ab1e7359ed1e5a4bef1e56e02b1e42b5251e3a97551e2780c41e06b5881ddb52551dbe4d991db574801db4e0681d984e6e1d826c881d825b1b
  | 6, 6 => 0x298b593d29319d85291385ac28e1d56328d3f68428c93b9c28bda13e28bc54b328b1318528a4a83e28a20861289a985c284836062844d6392842e262281a4d9f2819ebce2819312c281909f627fd4ed027a497ea27873465275b976e275958f2273f53a62738adc82707a0fd26bb2fef26b886cd26b638702683dcda267b41f5266cd79226640762266041af265363bb26488ebe262a32f4260932412604931525eb7b5225e030e425dfe4c825c5c2a225a00ed525471fea24fedf5924d3a65424b5fa3e24b2b20a24a64e2a2444ce752443fd30243e5010243971d5241577b924136d51240707cf23fa873323cebc7823bb3be323b6748b23abbd1f23aa74da
  | 6, 7 => 0x306876803048c4d23012b9613006014230010ce22fb10f502f7e6ae62f74af282f6745e12f311afe2eedfa852ee8e9622ed88f702ec68d272ebd3d6c2e8fba352e8e6a142dfdbfd52df741622de6358a2dad88fd2d90a6012d7d41f82d676d642d4f458b2d4acbf62d3ff5e92d3ea4312d0189f82ce246052cd4b9eb2cc795ae2ca069f22c7da4662c66b7e12c4642572c3e81882c2fc9bd2c14318a2be8c6dd2bcf9a012baf6f8f2baaf0272b81626d2b5f449a2b35846d2b25f1c52b08f8cc2ae9f3842ad9fd9b2ad3509f2a9002d62a892cd02a734e672a68501c2a430f592a222ab32a1d57d02a180b4c2a14d0f729e90d4d29e11e8129a1070d298f7056
  | 6, 8 => 0x36fb367836cb597836bdaf0a3679dd0b366fa2723668643f36648703365a8560363ae8203610c82c3609387935ecb95535d89aaa355e29ce353aa3c6350d0fa435009d3534ecd7be34ceb8d134a771a73492c5e83492603134886bc3344f47aa344da13934417d0f342f69f633da662c33d93c6b33d92a90339be8303398d185333ea61a332a02773327d92c33193e9a3316827432f1ebf132eb626b32e16b89329cbbfb326bf53f324f63603247653132139fa731f43daa31eba44231cc3c3831b1ab2931752de73157e493313ee4c531381b07312ae6df3122199e311dfd6a30f2019a30e43c9430d5282030be0b3130bda81a30b1e59a309c65f33097e570
  | 6, 9 => 0x3dc32c533dbce7733daf73bc3d8a3cae3d820b7b3d7dc3333d4903cd3d12016d3d02d9913d0124c93cff2e683ceb95653ce6437e3cdae5e73cda06bb3cd249253ccb90303cc696da3cb938473c7acf473bf4ea113bd7d5273bc8e96e3bc70d473bc2c63b3ba7c5f03b8aa58d3b72da473b1696283b0489893af9666f3af444543a4b4a043a2d6c6239e16a4739bb3ded39b6fb3b39731d65396f572d396d2e4d390153ab38eec90038ed9e2f38eb527838da452b38d186c938c8629238b3a76238a96ef8389771133891e847386f6c3938658553383f7f1838296398380d7bfe37c7d31d37c3b2cc37b9fc1b37b9f43e37a858a7378f31e83779d4de3702e442
  | 6, 10 => 0x456daacd4563ccbf455be5b545415274453e55c14519cf8c45179a8f4504d9ca44f4548e44b8f92b449d303544893b2c446f8a9444300bdc4408d56743e3db9743db6ae443d1a48743833f964363c00443555fb0433f660a432891ef43008d1e42ecbb3d42c90b1142bebde742b779a342824baf4270b5be4267af6a425ac010425327d7423475a94214c55a41ca7c2641a58777418c5819417adc044176fcae413f306a412c1b384119dfa14115ab1e40e7b61440936de1408a06cf405c6ec840455b7a400945b43ff0f5f13fa66a2d3f82b8df3f676f1b3f384bf13f301ba13ef9b7083ecbdd503eb160ae3eadce583e38a55b3e277fff3df0ff943dce4f97
  | 6, 11 => 0x4cfd734b4cf6f0224c8a818c4c6821664c5e0b844c4c79c44c468ba94c4491e44c2f2a6b4c2571154c1326ad4c01c6a54be3ee324bd15be94bc5e4304bb8d2fa4ba1260e4b9af8c44b83735c4b2e44754b226b904b21fba14b0d87ba4aee73794ac953704a95df414a4a4b134a3f5f3c4a24047e4a0ea6114a0173104a0125c049f0e1f749e579ed49d9fcdb49c985be497253c1495caf39493ccd6c492cc4da491e4f544910933d4901a2e2487c835c4827cfeb4812707947d7f35a47ce11e047bbd5324795ee6d4795381647883d4b4758974646e45dc946bdac8746b9893046b55adf464ad999462f96b7462e196845e1e20f45e00ffb457c8acd457a615d
  | 6, 12 => 0x54f251df54f0504c54ecbb8754d391cb54ba411f54b88b5354aaac7454a96c0954a16d3c5495055a545833245427678853ec72ba53e2c57853cb534053b8fa545354fc35533fb48d5314eaf652f5cae352e8c50e52e2321e52a439b552943af5524844685247743851e9127651bb2a0f51af8e6f517e9cbd516a823f516084435143b19c5137f86e5129991d51249501510a33e250df0cf150d485a1505beeb35059633d501f9e51500139404ff9d5294fc71f074f8c57c24f7b77d94f7141a24f050fd04ead7c894ea43e9e4e9d19034e7327324e6d5c1c4e337a064e1717654dd3ad484dc2d7694db0fe984d9bad584d6c43d14d43a2314d2f3d364d1acf0f
  | 6, 13 => 0x5f908c985f4ce3e85f205a9d5f03cb625ebac33b5e5e95475e374d3e5dedb7c05da6d4765d6558c35d4b941a5d19fb115cde0cce5ccd4b075cb55e505cb45f9c5cac1ec35ca9ea895c9b90375c8fe54c5bf13ab45bc0ce6c5b8e88025b6fefcf5b6b6fdf5b69415e5b2562705b1f7a795afe18b25ad883ea5aa67b745a4f521459fff51e59e9114a59c3015b59a0c2fc596cee2e5944bdd6593f58435932e9a35927b4ea591e47e658f528b758f47f0f58e6c54658b9c8d2589e681e586233b25836cf0a580f558b5802414f57ab48c1576751eb5702a7c256e6c4ac56ccc280567d130c567c7f515679544a5618ad1555eeb91a55ea834055739b7c556f0695
  | 6, 14 => 0x689fb5e7688d1b5568742b92686a7ac0684a905367b115c8677d84d86776f078675e8687672edba16725e9c56709aa6166eea10d665174db663e596f6624d4f6661f8dfe66126b4765a82696658f4356658f322f658155c9657d6fb8654b550165459a1264f3896864e1199364b320fe64aa6b44647899486472b701644d72e6642e54a063fb6a7f63e431ee63a63bbf63939f33638acc666386d6c4635c10ae6351f12b6310f02f62da87e162d2e70062623a356243e4b462356cc06212b35a61f63a0061f427ee61cd881d61874d906155056160f47f6c60ec287660c0e6cc60a44355609eba3e60723ebc6043727f60205a025fd017e95fbac6fd5f938bea
  | 6, 15 => 0x727253ef726a4e0171ffba4f71ff99de71f2133171d3d74b7179360f7136656e7108872f7101940170e9cc8f70d851ec70ab2568702d9a19702ba006701fd290701d3552701419896f9a15cd6f9599c06f596a256f4ebd9a6ecdef756ec7a3626e9f65f36e97376a6e1c26fb6df33b5f6dbfabf96d71e5326d545ce36d0b6a236cf9e7a76c80742d6c79ed6a6c4b6e046c49cc986c3d1b7e6bf360ab6bd591246ba44eea6b9d976b6b70d1e96b0ca3d16af175756aefcfd96ab78b856aa264eb6a9be0a66a8f01346a67d8cb6a41599e6a2ef61d6a08bb0569d0a4b069ac572569a9dbb8699f003a6962df38696158de693e342369148b686913e2eb6909685e
  | 6, 16 => 0x7e1111297e05acff7df7c5a07db1e1917db173387d7b98ea7d5aa3917d57f1e27cfde4937cea112d7ce7e2b17c4faf817c3064e57bfa0c557b9474917b75c3147b2b17a17afa65817ad5cce27acbd9467a9933267a2a8dff793a18dc792b8cc8792903cc78d82dee78d1319678a7b60178a46f1278444e8578208a857800865577ec248877c7b61177abf4137770373f77635fc87730263a76da66f976d69d9076c5d6f276c2010e769f2393764692e67614107e75a838e0744813417433e09b7415da3a74074756739a2d4a736eecaa73265eb0731d0cce731a9a3772d95ec172c1261e72b2833972aa6db7729c25ac7299780c728270b4727718da72739f54
  | 6, 17 => 0x8945a6a989143e4288cd013b884052b78826fc398803a86a87e7ffe087e13aa087cbde0a87c11c378759f0be874f92698738c306869b401d8518ff1e84ab412784a4c2e6849e475c846b9cfe845f90f7840e75af83ea69c583df594383a21eb1837f6b3f836a4ef38362909783621177834632f082effa2282de7117827963fa827639728267361781f114c7818c305a818bda6581829889816ee385814662f380977014808528c4800c7ccf7fd2c9987fbacdd57f78c21c7f5e60a67f4590c97f2587b17f1a591a7f10104d7f0fc1c87eff2d3a7eeb32617ee0fc947ed513f37ec8813d7ec3b0df7eb15f457e912cbc7e6829297e4b58517e1a8a567e16e388
  | 6, 18 => 0x97a4f38797a00225979895179713ecb196d93d1e960bb76c95d8122595872ae695219f0994ad8e5d94aba5ca945edd3e943ad535941d35b8940d96319405ef3093f38d2a93d288649349a86693342c279247052591fd1dbb919f9a929196f8c791592acd90f68a7190e225fa90d217489079ad95906fc1bc906837b89054b16b9022657e8ff6aa358fda83be8fd304808fcad59a8fa19e1f8f6057d08f26b32c8f1f96978f15bfe78ebf00228e7885f48e7643fa8e7599118e183e158e183c1b8dce939b8d869bbd8c76bee98c670cfd8c1a40aa8bf8e0e98bee01d98b31c58e8ae4720e8ab84b5d8aa44b2d8a7994f88a4b2c568a0b34fc89eee1ee89b9a4c5
  | 6, 19 => 0xa49fea3ba49c2d6fa4943c01a47a3dd7a42e9c98a3cde0e8a3b1d158a3a56a26a3098384a2a9280da2487bd3a18bd668a16c4690a16ae806a1689281a0fec4d5a0c27a1ca0bb9e7fa09b5bdda0908dfca070683ea049bbb59fce48649f19428c9f0c76639edbc97b9ecbd68b9ec9ae489e5f82759e56566f9e3c45669e394aa99ddfb7989daae7359d6fd84f9d6c560b9d678a6e9d42c3eb9d3121ea9ce1a3729cad90229c8160609c1ef4619c0b11509bff60119bfb29749be3accb9bb9bd659b4d17b59b430ccd9b18954a9ad5a6089aa748109a8f048799e9860699d8cbd499bbf508997632ef994649a29933b44399331f9b992721c298f42b2697aa9cac
  | 6, 20 => 0xb5e82352b5b29b6bb58ba30bb58b0cf8b51ce2f2b4bad623b4a99d57b47be621b3ff36d3b3e7728fb2d95111b272d876b1ce22c6b110e951b0c88900b09b89e2b074fd4cb06cb434b0433de6b03d009fb038e43cafa1d792af647c31aeff15d3aee89f20ae92fd92ad58a5d0ad3b090dad0c14ceacc7bd95ac1d3e4eabe5308aabd597ceab559622ab00c9d6aabd67a8aaa90063aa00aaa3a9e95962a9d57912a97e6899a94093e3a922e4e6a8f6772ea8e78fc4a8a73885a893383aa85b062fa8249059a80fa957a7f8f405a7ee4e57a7be4cf9a73b62e2a7347521a7307c11a6bf3e86a6aa7b4ba66fb308a65dd945a6353a8ca60c4fd4a5ffa0c9a5d42f5b
  | 6, 21 => 0xc871b992c8646ec8c82aa73ec7ae1fdec756f41ec7554d2ec7337313c73369bbc71b0c31c6bc9036c6b6c3c5c63ef557c637c9f1c6379303c59d6c30c4597455c364e4f4c3606443c2bfb77ac285e459c2472df4c1f9d8fcc1ad43f5c148abb5c0e08b57c0d5f8e8c0c2be92c08f171bc02e5d34bfb0cba3bf74ae55bec0a575be4be64fbe431619be227802bde1cfb5bdc979a2bccd4b3fbcc8e334bc5e25f5bc5bcfc9bbec3344bb11473fbaf9d5f0bad4da24ba4b6001ba437f4eba423037b9fe2647b9fc935bb9885577b8eccdc4b8c9f8fbb89d2df8b8984defb889a36bb84d5911b81c8db4b7eaa85bb7a557cbb72f93ffb71329c5b64b2e2db5f8c400
  | 6, 22 => 0xf172fccef03d9387eedf9f01eec22234e8f19d4fe88b2394e7a21dd1e5d018dfe52ef26ce4842702e383dba9e2fa15d8e2cad771e2783331e126cb02e04e0661dffa03e8de90f3a7de84395fde80f92cde4eb049dd040b83dbe35b38db4bb429dabbb2acda8d8f9bda650bedd9f6b427d89de169d87f9952d6de8f0bd6c3a000d6b7f5e6d5aad949d30f653ad2e808a9d2ddd086d2d1a5eed2c6073ad26c6f3ed2273c28d0dd04a9cfd7bd48cfaaeb5dceddfab4cd8c6716cd73df73cd6ebd58ccf24bcbcca27ba8cba82e50cb7bd7bacb6f5908cb1d44eecb0bd363cad25745caad7443ca7e11e2ca35eab9c9fcc544c9dc5937c996b3b6c8e3e5cfc8a800fc
  | 6, 23 => 0xff88f5fdfedc9cb5fce1f1b1fb379514fb2cad3cf6f16d4af5e5463cf3c06008f33b5fd0f32a1730f2854adf
  | 7, 0 => 0x12baa67712b8ab4112b8884a129997eb12798028124e263511eb7ccf11d7480611b4128d1198114411761aa8103ead2a0ff073950fc22fb60f3d84400f3badb20edd17080ea68d810e7e15130e783ebe0e68420e0e589c450dfb96ef0db675560d52c9a60cf91d9f0cc7aa850c2cfbb60c167f100afb5dd30acf09dd0ab0afbb0aa9dacf0a9628be08d6f026087867580754ea1506ecbabd06c7654b06b07a030663442506556796064612c706291d83061ab28605c61dd605a3eb0a0590310f05869eb105169eb004d0acec0452788e040745c603e3645403601271033b05b50291d00a024a740d0129b75500f5a3d200dd496a0086a50c0064991500103def
  | 7, 1 => 0x2775450f2774c4602705880d26e36c2426d0c80326beaf6f26aa53c326396ad4262d41fb24a7e76c2325e28c231857ea2310763b225c73322219ec0a21e9d24d21e729ef21a1d2672179389d2081cc61204aaf2d203e530f203cd04e2014c6441fd3d3851f9bef851f608b651f3d31db1ee4e3db1ee472391ebb13731e8eec381e7359ed1e3d0e221e17d8601e08e1531d989e101d73f5661bde45011b8548e61b1036f41a974b451a90e4691a5d39541a45ab1d1a0ece7019e360491979f41718e3fb0a18787ffd17d7cb9517a820261729918f1662ea0a1606144c15ff8a4715f86a8015f022ce1528ba3c141a4f1c14121a0c13b5da6d131bfefa130748e5
  | 7, 2 => 0x432891ef4309ffd842b779a341a4b5d6413f306a40db2d8b40bb28344079af633ffca0873f8b9abe3f49363a3e9c5ebb3e277fff3df1aaf13dc32c533d8620523d6054973cedcf813cd7d7c23c9f3cdf3c9d75a23bf3e2703b3c318a3a8b9b2139de879e396f572d38ad846e3724f45b36f4981f363c57f435743559355e29ce3518dab134ceb8d134746a9f34744a7f339be83033193e9a32e7627a32ba82ac329cbbfb31cc3c38319b3e4231381b073129ad3f30f26f093055c0a62fbf18df2fa1c82a2eedfa852ee51d392e9e70832daad2e42d770a592ca821632bcf9a012ba0a43a2ba064522b48380c2a7c85282a6bdfc02a5e00e1291abe562882e2b2
  | 7, 3 => 0x5e06e6065d93d62e5d3a46645d2e415c5bff541c5b4388f85af03eb05a437adf59f223e55992adb05943cbfb58905d1357c3519856fffaeb56dbe56f568ff7f155bb43f7556f0695552722ed54b47b9853b3d16b52f2fea452de426a523dc21151efbb6051d2062b516924ff515c291951099cc651007c3a50c9577f50a706e85059633d4f490be64ec05ebd4e7327324e1db72a4e0e9fc94e00c0ea4de27c5e4de254b54dc27b5b4d2b306b4d17706a4cd8ba054c4c79c44bb13b214b62f61f4aee73794a3f78dc49d602e8499cfa0a499b08ca48f0bd7d48b0ac9d4879fd8347f69d26472e33c1465e79d5462e1968457c5ed145179a8f43b9f0a34365b3a9
  | 7, 4 => 0x83c5bc52834a6d93804281917fe35f827e1a8a567db173387dad4e397d776c2f7d356db97d33ff317cea112d7cd372a07bf0d3337b25f4ae7a85129f7a70b12879c9043d798a90b27952d274794717d67946d3e3791d9b4177d135d07770373f77211a3f76f0de3376db0b2e74f2245d731d0cce72e03d9b72b2833972739f547260e48f71fb25a26f6c29a26e8018a76e34ebde6d45b13a6d2657c06cbe1d396bc490ee6b1be3666af785736aa2ab606a5eea176a2a46cf69f5d2f968b561d067f1c0d36554bad1651506a464ffcc4e64cf00c56336351163275f1562b43c1762623a356240ab8761ca400860d1580460b58bf55f5d13a95f492eb65ebcebc2
  | 7, 5 => 0xb47be621b37ef559b354b256b32b1ae2b253eee6b1b17014b12375bdb0f51e5bb04d71d7afebec7daec64c0eaebd223cab681b8eaabfa2cba9cb11c2a98c5b5da8e78fc4a70b5b06a62fa927a5103ec2a35f8a0fa16c46909ffd08839f9262399e58572e9e3c45669e14ab229de9f1209ce015509bfcd79298fcecee985a34f797a4f387956125c692ef453392b08ece92a6c201928df76892278ab59117715e91015b8b8f6e24048f6680978f46f2108ebf00228eb06ba68dce939b8dbfa66d8ce77a638bbc73f08a4b2c0489f226db88edfe0d87ca80ca877c8a9f8651842c862851b985faf2fb85f48e9f8549f6d285210b03851cbe168492c7cd83d9bb2c
  | 7, 6 => 0xfce1f1b1fc7cb7dbfb7259a6fabc44b5f8b72109f5a8ee32f33b5fd0f32a1730f1c31697ed71b5aee8f19d4fe8b54ab1e606f433e575a6eae2f7dbbfe2f02cffdfa5c541dede789bd9ab6bc3d8dd76c6d86400d8d863d13ed69e993fd64007d5d56748abd2da325bd0317033cb26fa2bc7554d2ec6f762cbc6b603d4c61b5c10c5690328c4d4624bc4605fcec30bd3fac1c6e06ebf74ae55bef4bb49bef1afedbeb2f988be6b5265bde1cfb5bcb2dff7bc5e25f5bad4da24baa8a17cba9e7ab4ba477786b713f0d0b6edc245b644e080b59a84ddb4e46fec
  | 8, 0 => 0x76f0de3361ca40084aee737905169eb0
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x8145480300000000010910473101255004007110950508400
  | 4, 0 => 0x18c405003000010d5150c30000000000c910100118304c030000000500c5202000000010d10500105355043000018442508300000000010d1050000015500201000005310920200000500c52020010535504300000c5454c4300000000010d105000000010910200000000c810300000000c51020011920009300000002550020200000001091017310125500400001095050830000000531052010008145480300000002550020200000531052010010d5150c30000000500c9201000000010d105000000010910400000500c9201
  | 4, 1 => 0x204802000000000109104000000010d1050000053109202000000010d105000000010d10500000001091040000000105102000000010d105
  | 5, 0 => 0x10410300000000000050000000109101000000000000100000000000060000000000008000000000000100000000c5102000000010910200000350812000000053101200000000000000600000001091020000000109101000000000000700000000c01020000000000006000000000000200000014042000000000000008000000008c103000000000000500000000000020000000000001000000000000200000001051020000000109102000004350c20000000324c8200000000000000500000000000080000000100101
  | 5, 1 => 0xc510000000450c1200000005210520000000000000050000000000004000000000000100000214842000000000105101000000000000200000001041030000000000007000000000000200000001001010000000000004000000000000300000000000010000000000007000004548420000000450c120000000000000050000000000001000001500920000000000c8103000005210520000000001041030000000000005000000010c10100000000000020000000000003000004350c20000000000000020000000000001
  | 5, 2 => 0x3548420000000254c0200000000000000100000001051020000000000003000000000000200000324c82000000000000002000000000000300000454c02000000000000004000000000000800000000000010000000104103000000000000800000000c910100000000000050000021484200000000010c10100000304c0200000000000000700000000c810300000000c910100000001091020000000000006000002048020000000000c510200000504842000000035484200000004548420000000000000040000000000005
  | 5, 3 => 0x20000053105201000003500920000000000c9101000000000000500000001051010000000000007000000000000300000000c810300000000c9101000000010510100000304c0200000001550020100000000000070000000000004000000010910200000000000080000000000003000004350c20000000324c820000000154c020000000000c510200000000c010100000000000040000000000004000000008c103000000000000300000000000040000010041200000000005010300000505082000000000000008
  | 5, 4 => 0x109102000000000000600000000000020000052105200000000008c103000000010510200000454c0200000000010910100000000000060000000000005000000000000100000454c42000000000000005000000010410300000000000060000000109102000004548420000000000000080000000000001000000010910400000000000060000000000001000000000000800000000c910100000454c0200000005310520100000000c91010000000000006000004350c2000000000000004000000010410300000314c4200
  | 5, 5 => 0x70000000000002000c5454c430000000454802000000000105101000000010510200000214842000000000000008000000000000300000500c920100000514c02000000000000004000000010910400000000000030000000000002000000010410300000000000080000053105201000000000000400000000c510200000000c51020000000000005000000000000400000000c010200000001051010000000000000000005150c20000000000000080000000000002000000009110400000001051010000000000008
  | 5, 6 => 0x80000000000002000000000000700000000000010000000105101000000000000600000000c5102000000000000400000324c82000000000000007000005108120000000000000030000035504200000000010910200000000c910000000000c010200000000000070000000000002000000000000100000000c510000000000000020000000000003000000010910100000500c5200000003548420000000000000010000045049200000005004d20000000000c810300000000c51020000051109200
  | 5, 7 => 0x4548020000000000c910100000000000040008145480300000000005010300000000000040000000000001001884150430000000001041030000000000000000000010c1020000000109101000000010410300000000000000000000100101001804350c3000000041504200000000144020000000000000020000000000001000000000000400000000000040000000000001000000004d10000000000000020000000105101000000010d10500000000000010000000000003000001500920000000500c52020000000000006
  | 5, 8 => 0x8000000000000300000000000080000000000006000001004120000000104402000000010440200000004150420000000000c01010000000000000000000010910200000000c910000000001051010000000000003000004508120000000500c520000000000000040000000000002000004050020000000000c8103000000000000200000450852000000000109101000000000000100000000000060000000000001000001044020000000000000000000045081200000000000000700000001051010000000000004
  | 5, 9 => 0x500c520000000000c510200000104402000000000000007000000000000100000000000030000000000000000000010910100000531092020000000000004000000000000100000000000080000000109101000000000000400000000c9101000002048020000000000c91010000000000002000000008d100000000000000700000000000000000041504200000000000000000000000c0101000000010510200000001091020000000050103000000000000300118304c0300000000010510200000000000000000000000006
  | 5, 10 => 0x2550020000000000000060000000000005000000010410300000531092020000000109101000000000000100000104402000000000109101000000010910200000000c81030000000109101000000000000600000450812000000010440200000000000000100000104402000000000000008000000000000200000255002000000000000005000004508520000000000000060000000000004000005150c20000000000000060000000000007000000000000100000000c810300000000c010100000001091010000045081200
  | 5, 11 => 0x1044020000000454c420000000000000070000000000005000000000000000000000000050000020480200000000000000400000000501030018c40500300000000000000600000000000000000000000001000000000000400000000c510200000000000060000051081200000005010d2000000000105102000000008d10000000000000080000021484200000000000000400000000000080000000000004000000010910100000000811000000000109102000004150420000000001091020000000104103000004504d200
  | 5, 12 => 0x70000000000008000000010510200000000000000000000000005000000010910100000000c51020000000109104000004150420000000000000010000000000005000000000000500000000000070000000000007000000000000200000001001020000025500200000002048020000000001051010000000000002000000010c10100000500c9201000000000000800000000000020000000100101000000010d105000000010510200000000000020000000000002000000000000500000000000080000000000002
  | 5, 13 => 0x811000000000000004000001004120000000000c0101000000000000400000000000080000000000001000000000000400000154c02000000000109101000000000000200000000000070000000000001000000000000800000000c0101000000000000200000000000020000000000005000000000000800000354842000000045484200000000000000600000000000060000052105200000004150420000101255003000000000000006000001044020000000255002000000000105101000000010d10500000000c8103
  | 5, 14 => 0x20000000104103000000008c1030000000109102000000000000500000454842000000000000006000000000000100000000000070000000000002000001044020000000000000050000000000001000000000000300000001091020000010440200000000000000300000000000070000000000000000000010510200000000c010200000454c020000000000c910100000000000020000000000005000000000000400000500c920100000355042000000000000008000002048020000000001051010000000109101
  | 5, 15 => 0x8000000000000200000254c020000000000000040000053109202000000000000800000000000030000000000002000000000000600000314c420000000014042000000000000000000000000000600000000c510200000000000020000051109200000000000000000000200092000000000000001000000000000500000000000010000000000007000000010910200000000000080000000000008000000000000500000000000020000000109102000000000000000000000000070000040500200
  | 5, 16 => 0x6000000548420000000454c4200000000008c10300000000000010000015009200000000000000300000000000040000000000008000004508520000000000c51020000051081200000000000000800000304c020000000000d110500000000c910100000454c420000000000000060000000000006000000010510100000454802000000000109101000000000000600000000c91010000021484200000000000000400000454c4200000000000000300000204802000000000000002000000000000500000450c5200
  | 5, 17 => 0x100000000c0101000000000000600000001051010000000000003000001044020000000000000020000000000003000000000000500000350812000000000000002000000000000800000250c52000000000000008000000000000100000000000010000000000005000000000000800000425082000000000000006000003508120000000454c4200000000000000800000000c51000000000000008000000000000700000254c02000000000000006000005310520100000350812000000040500200
  | 5, 18 => 0x1044020000000001091010010d5150c300
  | 6, 0 => 0x10000000000008000000000000200000000000050000000000003000000000000600000214842000000000000004000000000000500000350812000000000000002000000000000600000405002000000000000002000000000000600000250c52000000000000004000000000000400000000000030000000000005000000000000800000000000010000000000001000000000000100000454842000000000000002000000000000300000000000080000000000003000000000000500000000000070000000000003
  | 6, 1 => 0x7000000000000600000000000080000000012100000003548420000000000000000000000000008000000000000300000000000080000000000001000000000000200000000000020000000000004000000010510000000001091000000000000004000000000000200000000000030000000000003000000000000100000000000060000000000005000000010c10000000454802000000000000004000000000000200000000000070000000000004000000000000300000450c5200
  | 6, 2 => 0x80000000000004000000000000600000000000010000000000006000000004d100000000000000000000000000070000000000003000000010510100000000000030000000000003000000000000300000000000070000000049100000000000000300000000000080000000000007000000000000300000000000010000000000002000000000000800000000000010000000000004000000000000200000000000030000000000005000000000000600000000c9100000000000000300000000000010000000000001
  | 6, 3 => 0x10000000000001000000000000800000000000010000000000001000000000000600000000000060000000000005000000010910100000000000010000000000002000000000000600000000000020000000000002000000000000100000000000030000000012100000000000000600000454c0200000000000000200000000000020000000000002000000000000400000000000080000000000004000000000000200000000000020000000000007000000000a1000000000000004000000000000300000324c8200
  | 6, 4 => 0x4000000000000000000000000000000000000008000000008d100000000000000800000450812000000000000006000000000000500000000000080000000000008000000000000000000000000060000000000008000000000000300000000000080000000000000000000000000000000000000000000045085200000000000000100000000000010000000000005000000000000600000000c8100000000000000100000000000030000000000001000000000000700000000c910000000000c41000000000109101
  | 6, 5 => 0xc41000000000000007000000000000500000000000010000000105101000005150c20000000000000020000000000004000000000000100000000000040000000000005000000000000100000000000020000000000003000000000000000000000000050000000000002000000000a10000000000000030000000000002000000000000400000254c0200000000000610000000000000010000000000007000000000000700000000000020000000000003000000000000400000000000020000000000003000000008d100
  | 6, 6 => 0x2000000010d100000000010110000000000c510200000000000020000000000006000000000000600000500c52000000000000001000000000000700000000121000000000000006000000000000100000000000000000000081100000000000000100000000000030000000000006000000000000500000405002000000000000004000000000000100000000000040000000000003000000000000000000001091010000000000002000000000000000000000000010000053101200000000000000100000000c5102
  | 6, 7 => 0x121000000000000002000000000000200000454c02000000000000000000000000000000000000000040000000000000000000000000700000000000020000042508200000005210520000000405002000000000000001000000000000200000314c42000000000000006000000000a10000000000000020000000000002000000000000500000450c12000000000000000000000000000400000000000010000000006100000000000210000000000000040000000000006000000000000800000000000020000000000007
  | 6, 8 => 0x2000000000000200000000c8103000000000000500000000000030000000000004000000000000600000000000000000000000000000000000000400000454c420000000000000020000000040100000000000000500000000000030000000000001000000000000100000000000010000000100100000000000000300000000000030000000000002000000000000100000000000020000000000006000000010c100000000000000300000000c91010000000000008000000000000800000000c41000000045484200
  | 6, 9 => 0x800000000000010000000000004000000000000300000000000010000000000007000000000000400000000000070000000000005000000010910200000000000040000000000002000000000000300000000000020000000000006000000000000100000454802000000000000004000004250820000000000000000000000000002000000000000000000000000070000000000001000000000000100000000c4100000000000000400000000000010000000000003000000000000600000000000010000000000001
  | 6, 10 => 0x3000000000510000000000000010000000000002000000010910000000000c5102000000000000600000000000020000000000008000000000000300000000000050000000000004000000000000100000000000030000000000008000000000000300000000000010000000000001000000010c10000000000000030000000000004000000000000200000000000030000000109102000000000000300000001051010000000000000000000000000400000000000010000000000001000000000000200000000c5100
  | 6, 11 => 0x1000000000000200000000851000000000000000000000000000400000000000020000053101200000000000000700000000000030000000000003000000000000700000531012000000000000001000000000000100000000000020000000000004000000000000300000000000000000000104103000000000000400000000c9100000000000000400000000c0102000000000000500000000000020000000006100000000000000200000000000040000000000002000000000000000000000000060000000000004
  | 6, 12 => 0x3000004350c200000000000000600000000000020000000000001000000000000600000000000010000000000002000000000000700000000000000000000000003000000140420000000000000050000000000002000000000000100000000c8103000000000000300000000000020000000000003000000000000400000000000070000000000004000000000000400000000000050000000000006000000000000100000000c410000000000000000000000000005000000000000700000000000080000000006100
  | 6, 13 => 0x700000001001010000000000001000000008010000000000121000000000000004000000000a10000000001051000000000000001000000000610000000000c01010000000000004000000000000800000000000020000000000003000000000000800000000000020000000006100000000000000600000000000050000000000006000000000000600000000000050000000000001000000000000300000000000000000000000007000000004d1000000000105102000000000000400000531012000000000000002
  | 6, 14 => 0x200000000c0102000000000000300000000401000000000105102000004150420000000000000030000000000003000000000000300000000000070000000000002000000000e100000000010c1020000000000005000000000000400000000c910000000450c1200000000000000000000255002000000000000001000000000000100000000000080000000000001000000000000500000000000030000000000007000000000000200000000000010000000000008000000000000000000000000060000000000007
  | 6, 15 => 0x500000000000030000000000007000000000000100000000000060000000000002000000010010000000000000080000000000007000000008010000000000121000000000000002000000000000400000214842000000045484200000000000000700000000000060000000000008000000000a100000002148420000000000000040000052105200000000000000100000450c520000000000000000000000000003000000000000600000000000080000000081100000000000000200000000000020000000000004
  | 6, 16 => 0x4000000000000100000000000000000000000002000000000000300000000000050000000000005000000000000400000000000030000000085100000000000000200000000000060000000000004000000000000100000000000020000000000002000000000000100000000c4100000004350c20000000354842000000000000001000000010c10000000001011000000000000001000000000000000000000c8103000000010010000000000000020000000105102000000000000800000000c91010000000000006
  | 6, 17 => 0x100000000000070000000000002000000000000600000000000000000000000001000000010c100000000000000300000000000050000000000005000000010110000000000000010000000000000000000000000200000324c820000000000000040000000000005000000000d100000000000e10000000000c11000000000000003000000000000200000000000020000000009100000000008d10000000000c5102000000010910200000000c01000000000000006000000008410000000000000000000000000004
  | 6, 18 => 0x7000000000e100000000000000100000000000020000000000003000000000000800000000c110000000355042000000000000003000000000000600000000000040000000109100000000000000800000000000070000000000006000000000000800000000000010000000000002000000000000100000001051020000000000003000000000000600000454c020000000001091000000000000001000000000000600000000000010000000000003000000004110000000000c410000000000000030000000000008
  | 6, 19 => 0x10000000000008000000000000300000204802000000000000001000000000000100000000000070000000000006000000000000400000000c01000000000000006000000000000100000000000030000000000006000000000000000000450812000000000000006000000000000400000000000010000000000005000000000000200000000000040000000000006000000000000200000000000010000000000008000004350c2000000045085200000000010410300000454c420000000000000010000000000007
  | 6, 20 => 0x300000000000020000000000005000000000000200000000121000000040500200000000000000700000250c5200000000000000100000000061000000000000003000000000000000000000000010000000000000000000000000200000000000060000000000004000000000000200000510812000000000000003000000000000100000000000050000000000001000000000000000000000000060000000000006000000000000200000000000030000000000008000000010910000000000000010000000000004
  | 6, 21 => 0x60000000000001000000000000400000000000050000000000003000000000000100000000000010000000000003000000000000000000000000010000000000003000000000000700000000000050000000000003000000000e10000000454842000000000000003000000000000100000000000020000000000004000000000000500000000000000000000000003000000000000700000000000000000000100101000000000000700000000000000000000000003000000010d10000000500c52000000000000002
  | 6, 22 => 0x600000000000030000000000003000000010410300000000c0100000000000000300000000411000000000000003000000000000200000000c410000000000000040000000000002000000000000200000000000030000000000002000000000000100000000c0102000000000000300000000000050000000000006000000000000500000000000040000000000004000000000000300000314c42000000000000003000000000000100000000000030000000000003000000000000300000000000020000000049100
  | 6, 23 => 0x80000000000000000000000000000000000000010000000000001000000000000100000000000000000000000001000000000000300000000000030000000000008000000000000200000000000030000000000002000000000000100000000000030000000101100000000000000300000000000010000000000001000004250820000000000000060000000109101000000000000000000000000040000000000002000000008410000000000c11000000000000001000000000000600000000000060000000000007
  | 6, 24 => 0x1000000000000100000000000070000000000000000000000000000000001091000000000000002000000000000000000000c1100000000000000200000000811000000000000004000000010910000000000c01000000000000006000000000000000000000000010000000000005000000000000800000000000080000000000003000000000000300000000000010000000000001000000000a1000000000000000000000005110000000000000000000000000001000000000000100000000061000000000000000
  | 6, 25 => 0xc010000000454c0200000000000000600000000000010000000000007000000000000100000000000030000000002100000000000000300000000c91000000000000006000000000000200000000000040000000000001000000000000400000000000030000000000003000000000000100000000000020000000000001000000000000300000000000020000000000002000000000000600000000000080000000104100000000000000500000001011000000000000002000000000000700000000c510200000000c1100
  | 6, 26 => 0x200000000000080000025500200000000000e1000000000000003000000000000600000000000050000000000002000000000000300000000000020000000000002000000000000600000214842000000000000006000000000000000000000000060000000000004000000000000600000000c9101000000000000600000000000010000000000004000000000000100000510812000000000000000000000000000100000000c8103000000010910000000324c820000000450c120000000000000000000000000000
  | 6, 27 => 0x50000000000005000000000000500000000000060000000000002000000000410000000000000030000000000002000000010510000000000000070000000000005000000000000100000000061000000000000002000000000000400000000000080000000000001000000008010000000000000000000000000008000000008110000000000000060000000000008000000000000800000000000020000000000006000004508120000000415042000000000000002000000000000400000001091020000000000002
  | 6, 28 => 0x1000000000a10000000000000010000000100102000000004110000000000000020000000000002000000000000500000000c010000000000c110000000000000060000000000002000000000000100000000c0100000000000000600000000000060000000000007000000000000000000000c910100000000000060000000000005000000000000400000000000030000000000001000000000000200000000000040000000109101000000000000800000000000040000000000005000000000e1000000000000002
  | 6, 29 => 0x10000000000000000000000000100000000c010100000000c1100000000000000700000000c01000000000000006000000000000500000000121000000000000002000000000000200000000000030000000000007000000000000200000000000080000000000006000000000000100000000000080000000000003000000000000300000000000070000000000006000000000000300000000000070000000000000000000010d10000000000000080000000000001000000004010000000001011000000000000008
  | 6, 30 => 0x600000000000070000020480200000000004110000000000000020000000000000000005108120000000001091000000000000004000001044020000000000c9100000000010910200000000000030000000000000000000000000200000000000010000000000000000000000000200000000501030000000002100000000000000600000000411000000000000003000000010110000000000000000000000000001000000000000100000000000020000000040100000000000000700000000000030000000000001
  | 6, 31 => 0xe1000000000000004000000008c1030000000000000000000000000300000000000080000000000001000000000000300000000000040000000000003000000000000200000001041030000025500200000000000000100000500c520000000000000020000000000004000000000000100000000000020000000006100000000000000200000000000040000000000003000000004010000000000000080000000000001000000000000200000000000060000000000008000000000000600000000000060000000000003
  | 6, 32 => 0x40000000000007000000000e10000000000000010000000000006000000004010000000000000080000000000002000000000000000000000000000000000000007000000000000500000000000060000000000002000000000000400000000000060000000000003000000010510200000000000030000000000006000000000000200000000000010000000000001000000008110000000000000070000000000000000000000000700000254c02000000000000003000000000000200000000021000000000000003
  | 6, 33 => 0x300000000000050000000000001000000000000100000000000000000000000006000000010510100000000000080000000000006000000000000000000454c4200000000000000300000000000030000000000004000000000000700000000000020000000000001000000000000500000000c910000000000000050000000000001000000010910100000000000030000000005100000000000000300000000000060000000000004000000000000200000000c0100000000000000400000000c01020000000081100
  | 6, 34 => 0x5000000000000500000000000040000000000003000000000000100000000000060000000000006000000000000300000000c910000000000000010000000000008000000000000600000000000010000045480200000000010c1020000000041100000000010510100000000000010000000000002000000000000100000000000040000000000008000000000000200000000000030000000000007000000000000300000000000020000000000000000000000000600000304c020000000000811000000000000002
  | 6, 35 => 0x70000000000004000000000000000000000c11000000000000003000000000000100000154c020000000000c0102000000000000100000000c01000000000000003000000004d100000000008c103000000010d10000000000401000000000000008000000008c1000000000000007000000000410000000000000030000000000001000000000000300000000000060000000000003000000000000200000000000010000020480200000000000000200000450c120000000000000000000010440200
  | 6, 36 => 0x210000000001091010000000000008000003508120000000000000020000000000000000000000000200000000000010000000085100000000000000500000000c510000000000000020000000000006000000005010300000000000020000000000004000000010d1000000000000004000000000000000000000000050000000000000000000000000700000000000060000000000001000000000000300000000c810000000000c510000000000401000000000000001000000000610000000000000000000000000001
  | 6, 37 => 0x10440200000000000000000000000000030000000000003000000008110000000000000010000000000006000000000000300000000000040000000006100000000000000100000000000060000000000001000000000000700000000000050000000000003000000000000200000000000070000000000000000000000000700000000411000000000000001000000000000300000000000060000000000008000000000000600000000811000000000000005000000000000700000001051010000000000000
  | 6, 38 => 0x2000000000000200000000c810000000000000060000000000005000000000000500000000401000000000000002000002550020000000000000010000000000007000000000000100000000000070000000000007000003548420000000000000060000000000008000000000000600000000000060000000000006000000000000000000000000050000000000006000000000000700000000000070000000000004000005010d20000000000000060000000000003000000010910000000000000070000000000000
  | 6, 39 => 0x800000250c520000000000000080000000109102000000000000200000000000070000000000002000000008010000000000000030000000000007000000000000300000254c02000000000000002000000000000800000000000070000000000002000000000000100000001041030000000000003000004050020000000000000000000000000004000000000000300000000111000000000000002000000008110000000000c910000000000000040000000000001000000004d10000000000000020000000000001
  | 6, 40 => 0x600000000000030000000000005000004508120000000000c81030000000000000000000000000200000000000020000000000001000000000610000000000000030000000000001000000000000000000000000080000000041100000000000000600000001051000000000000005000000010c101000000004010000000000000030000000000006000000000000200000000000040000000000008000003508120000000000000000000000000001000000000000400000000c810300000000000030000000000007
  | 6, 41 => 0x8110000000000000070000000000006000000000000300000000000040000000100100000005310120000000000000000000000040100000000000000400000000000020000000000001000000000000400000000000040000000000002000000000000200000000000010000000000005000000000000100000000000010000000000003000000010510000000204802000000000000001000000000000400000254c0200000000000210000000304c020000000000000060000000000003000000010d1000000000000006
  | 6, 42 => 0x121000000000040100000000000000100000000000000000000000002000000000000700000000000010000000000002000000000000500000000000020000000000007000000000000700000001001000000000000003000000000000800000304c02000000000101100000000000000100000000401000000000000005000000000000500000000000080000000000008000000010510100000000000020000000000002000000000000300000001001020000000000001000000004110000000510812000000000000008
  | 6, 43 => 0x700000000000070000000109102000002550020000000000000040000000000002000000000000000000000000040000000000004000000005010300000000401000000000000007000000000510000000000000080000000105100000000000000500000000c5102000002348c20000000454c420000000000c8100000000004010000000000000050000000000001000000000000000000000000040000000000007000000000000500000000000020000000109101000000004110000000000000010000000000005
  | 6, 44 => 0x35081200000000000000600000000000030000000000003000000000000200000001001000000000000002000000000000300000521052000000000000003000000000000100000000000040000000100100000000000000100000000c01000000000000002000000000000300000000c51020000000000001000000000000500000000000020000000000004000000000000500000000000010000000000000000000000000500000000000060000000081100000001044020000000000000010000000000003
  | 6, 45 => 0x60000000000001000000000000100000454c42000000000000003000000010510200000000000070000000109102000000000000000000000000000000000000002000000000000100000000000030000000000006000000000000700000000000030000000000005000001044020000000000000040000000050103000000000000100000000000030000000000002000000000000200000000000010000000000006000002048020000000000000010000000012100000000004910000000000000060000000000005
  | 6, 46 => 0x10000000000006000000000000100000324c8200000000000000700000000000080000000000004000000000000600000000c910000000000000020000000012100
  | 7, 0 => 0x3000000000000300000000000010000000000000000000000a100000000000000100000000000030000000006100000000000000200000000000030000000006100000000000a10000000000000070000000000000000000004010000000000c51000000000000001000000000000000000000000070000000000002000000000000200000000000040000000000003000000000000000000000c41000000000000001000000000000300000000000000000000000002000000010910000000000000050000000000002
  | 7, 1 => 0x1000000000000300000000c11000000000000003000000000000100000000c910000000000c0100000000010410000000000000070000000012100000000000000100000000000020000000000002000000010c100000000000000100000000000000000000000001000000000000200000000000000000000000001000000000000000000000000030000000000002000000000000100000000000010000000000000000000000210000000000000010000000000001000000000000100000000000000000000000006
  | 7, 2 => 0x3000000000a100000000000000700000000000010000000006100000000000000100000000000010000000000001000000000000600000000000030000000000003000000000000200000000000010000000100100000000000000300000000c410000000000000030000000000001000000000000300000000000020000000000000000000000e1000000000000001000000000000500000000000000000000000002000000000000500000001011000000000000001000000000000000000001081000000000012100
  | 7, 3 => 0x500000000c91000000000000000000000000000600000000000000000000012100000000010c1000000000000001000000000000300000000000030000000000002000000000000200000001051000000000000003000000000e1000000000084100000000000000200000001041000000000000001000000010d1000000000080100000000000e1000000000012100000000000000000000000000000000000000002000000000000000000000061000000000000002000000000000300000000000030000000000001
  | 7, 4 => 0xa10000000000000020000000006100000000000000600000000000000000000000003000000000000700000000021000000000000003000000000000200000000000020000000000001000000000a100000000000000600000000c410000000000000070000000000006000000000000300000000000030000000000001000000000000300000000000030000000000001000000000000300000000000010000000000002000000000000700000000000040000000000001000000000000300000000000040000000000000
  | 7, 5 => 0x3000000010110000000000000000000000005100000000000000100000000c0100000000000000200000000811000000000000006000000000000500000000000000000000000003000000000000100000000000030000000000001000000010c1000000000000003000000000000000000001041000000000000002000000000000000000000000030000000000001000000000210000000000000020000000000002000000008510000000000121000000000000002000000000000000000000000010000000000002
  | 7, 6 => 0x2000000000000400000000000040000000000003000000000000100000000801000000000012100000000000000300000000c010000000000061000000000000008000000008c10000000000041000000000000001000000000000600000000000000000000000000000000000a10000000000000070000000000001000000000610000000000000050000000000000000000010c1000000000000002000000000e1000000000109100000000000000300000000c4100000000000000100000000000030000000000003
  | 7, 7 => 0x1000000000000000000001091000000000000002000000000000400000000000010000000000001000000000000300000001011000000000000008000000000000700000000c110000000000c0100000000000000300000000000040000000000000000000000000300000000000000000000000003000000000000000000000000060000000105100000000000000300000000000000000000000005000000000000200000000000010000000000000000000000e100000000000000100000000000020000000000006
  | 7, 8 => 0x109100000000010d10000000000c110000000000000020000000000002000000000000200000000000080000000000000000000000000200000000000000000000000002000000000000300000000000010000000000003000000008010000000000c5100000000000e100000000000000100000000061000000000000001000000000000100000000000060000000012100000000000000200000000000010000000000003000000000000000000000000010000000000002000000000000400000000000010000000000003
  | 7, 9 => 0xc010000000000000030000000000000000000000000100000000000010000000000000000000010c1000000000000006000000010d100000000010010000000000000000000000000004000000000610000000000000020000000000000000000000000700000000000030000000000001000000000000400000000000030000000000003000000000000000000000000000000000000001000000000000200000000000000000000000000000000000e1000000000000001000000000000100000000000000000000000003
  | 7, 10 => 0x8510000000000c810000000000401000000000000006000000000000000000000000030000000006100000000000000300000000021000000000000001000000000000300000000000020000000000003000000000000200000000000040000000000004000000000000400000000000030000000000002000000000000000000000000010000000041100000000008110000000000000010000000000003000000010110000000000000070000000000000000000000000300000000c11000000000000001
  | 7, 11 => 0x411000000000000003000000000000200000000811000000000000001000000000000000000001011000000000000003000000000000100000000c010000000000000060000000085100000000000000100000000c810000000000401000000000000000000000000000300000000000010000000000000000000000000100000000000020000000104100000000000000300000000411000000000000002000000000000100000000000010000000000005000000000000000000000000020000000000002
  | 7, 12 => 0x1210000000000000030000000000000000000000000800000001081000000000000006000000000000200000000000030000000000003000000000000100000000c510000000000000030000000000002000000010010000000000000020000000000001000000000e10000000000c8100000000004010000000000000070000000000000000000000000000000000000020000000000003000000000000400000000000030000000000000000000000000700000000000000000000000003000000008d1000000000012100
  | 7, 13 => 0x1000000000000600000000c910000000000121000000000000000000000008110000000000000010000000000002000000000000100000000c910000000000000030000000000000000000000000000000000411000000000000000000000000000000000000c810000000000000000000000000003000000000000300000000000030000000000003
  | 8, 0 => 0x0
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 7 s ws hint
  | 1 => checkCutEntry dom_3 roots_3 6 s ws hint
  | 2 => checkCutEntry dom_4 roots_4 6 s ws hint
  | 3 => checkCutEntry dom_6 roots_6 6 s ws hint
  | 4 => checkCutEntry dom_8 roots_8 5 s ws hint
  | 5 => checkCutEntry dom_9 roots_9 5 s ws hint
  | 6 => checkCutEntry dom_10 roots_10 5 s ws hint
  | 7 => checkCutEntry dom_11 roots_11 5 s ws hint
  | 8 => checkCutEntry dom_13 roots_13 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_14 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_14 == dom_14) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_14 goalM u ys) : RunD dom_14 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_14 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
theorem z4_40 : ∀ i, 40 ≤ i → i < 41 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 40 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 41 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (z4_40)))))
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
theorem z5_264 : ∀ i, 264 ≤ i → i < 270 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 264 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 270 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (range_split z5_200 (range_split z5_208 (range_split z5_216 (range_split z5_224 (range_split z5_232 (range_split z5_240 (range_split z5_248 (range_split z5_256 (z5_264)))))))))))))))))))))))))))))))))
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
theorem z6 : ∀ i, 0 ≤ i → i < 720 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (range_split z6_376 (range_split z6_384 (range_split z6_392 (range_split z6_400 (range_split z6_408 (range_split z6_416 (range_split z6_424 (range_split z6_432 (range_split z6_440 (range_split z6_448 (range_split z6_456 (range_split z6_464 (range_split z6_472 (range_split z6_480 (range_split z6_488 (range_split z6_496 (range_split z6_504 (range_split z6_512 (range_split z6_520 (range_split z6_528 (range_split z6_536 (range_split z6_544 (range_split z6_552 (range_split z6_560 (range_split z6_568 (range_split z6_576 (range_split z6_584 (range_split z6_592 (range_split z6_600 (range_split z6_608 (range_split z6_616 (range_split z6_624 (range_split z6_632 (range_split z6_640 (range_split z6_648 (range_split z6_656 (range_split z6_664 (range_split z6_672 (range_split z6_680 (range_split z6_688 (range_split z6_696 (range_split z6_704 (z6_712)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z7_400 : ∀ i, 400 ≤ i → i < 405 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 400 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 405 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (range_split z7_208 (range_split z7_216 (range_split z7_224 (range_split z7_232 (range_split z7_240 (range_split z7_248 (range_split z7_256 (range_split z7_264 (range_split z7_272 (range_split z7_280 (range_split z7_288 (range_split z7_296 (range_split z7_304 (range_split z7_312 (range_split z7_320 (range_split z7_328 (range_split z7_336 (range_split z7_344 (range_split z7_352 (range_split z7_360 (range_split z7_368 (range_split z7_376 (range_split z7_384 (range_split z7_392 (z7_400))))))))))))))))))))))))))))))))))))))))))))))))))
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

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (3939033280 * 2 ^ 32 + 3905478656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_14.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_14 10 hT6 (by unfold IsConst; decide) low_14

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [7, 2]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [9, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_15399_aux

theorem PEqualNP.Outside.L_meta_15399 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3939033280 * 2 ^ 32 + 3905478656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3939033280 * 2 ^ 32 + 3905478656) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_15399_aux.wit, PEqualNP.Outside.L_meta_15399_aux.wmono, le_trans PEqualNP.Outside.L_meta_15399_aux.wsize (PEqualNP.Outside.L_meta_15399_aux.lower s hs), PEqualNP.Outside.L_meta_15399_aux.weval⟩
