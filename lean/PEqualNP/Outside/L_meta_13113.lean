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

namespace PEqualNP.Outside.L_meta_13113_aux

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

def dom_0 : Nat := 0xffffffff
def goal_0 : Nat := 0xfeccf080
def roots_0 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_0
def pairsG : List (Nat × Nat) := [(2, 18), (3, 7), (3, 19), (4, 12), (5, 7), (5, 13), (6, 7), (6, 14), (6, 22), (8, 12), (9, 13), (9, 25), (10, 14), (10, 26), (11, 15), (11, 27), (16, 18), (17, 19), (17, 25), (20, 22), (20, 28), (21, 23), (21, 29), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [2, 3, 3, 4, 5, 5, 6, 6, 6, 8, 9, 9, 10, 10, 11, 11, 16, 17, 17, 20, 20, 21, 21, 24, 24, 24]
def r2sG : List Nat := [18, 7, 19, 12, 7, 13, 7, 14, 22, 12, 13, 25, 14, 26, 15, 27, 18, 19, 25, 22, 28, 23, 29, 25, 26, 28]
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
  | 2, 0 => 0x8d976a1
  | 3, 0 => 0x9720a7b3491e19aa035e2d2501a7e3ab
  | 4, 0 => 0xde66a692ac05225e92b4fb248fb0914b81ea162e5e1d4aa8419de0e532bc99002637312d25e0cf661d973d961d0f712608a43bb3
  | 5, 0 => 0xd051f507ce00c9b9ac05225e7702c5a9744473ec554c825e5299e96d3a6b8d4130706e4225303d37206585ea1b8a7ef10241d3e1
  | 6, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaa000000000000aaa0aaa000000000aa88aa8800000000aa00aa0000000000a0a0a0a00000000055555555000000000f0f0f0f000000000000ffff
  | 0, 1 => 0xf0f0000000000000f0a0f0a000000000f000f00000000000eeaaeeaa00000000cccccccc00000000cc00cc0000000000c0c0c0c000000000aaaaaaaa
  | 0, 2 => 0xff00f00000000000ff00000000000000fafafafa00000000fafaf0f000000000fafaaaaa00000000faaafaaa00000000fa00fa0000000000f0f0f0f0
  | 0, 3 => 0xffffff0000000000fffff00000000000ffffcccc00000000ffffa0a000000000ffff000000000000fff0fff000000000ffccffcc00000000ff00ff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x722b3
  | 3, 0, 0 => 0xdb5664de60c4e62ab4db9644
  | 4, 0, 0 => 0x1fb41685de20b42ef105957789c16bbcc1485de9ab42fb105a1778a2d0bbc55635dc60b42eef05a177882ccbbc4a0b5
  | 5, 0, 0 => 0x37882d026eef105a181bc41685fef105a1b7882d286de20b41d81bc2d01506f10589779c41686de20d5a1b78ac1686de20b401b7883d686
  | 6, 0, 0 => 0x1bc41685
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
  | 0, 0 => 0x198000060cc30003301800cc0018000c39933c9e1ff81c00ffff
  | 0, 1 => 0x1e00000600030000000066fc36003c71c00f000000070066cc36
  | 0, 2 => 0xe0000038000001fb37f87e01f81fb30d866cc3600330007801f8
  | 0, 3 => 0xffff803ff0000fffc71fff0030ffc0003f8fff8e03ff1f80fe00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x39a2010e4cc7239b31d8c4cc2018111cb19338961ea0140056fa
  | 0, 1 => 0x9e004027056fa9415aa1e6fcf64afc75d00f0800a14748e6cc76
  | 0, 2 => 0xf53faa3d4a800bfb7ffafedffebfb35daf6defeb537aa27857fa
  | 0, 3 => 0xffffeb7ffffadfffe75fffed77ffea417fcfffafffffffd4fea8
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

def dom_1 : Nat := 0xcc000000cc
def goal_1 : Nat := 0xc800000080
def roots_1 : List Nat := [0x8800000088, 0xc0000000c0, 0xcc00000000]

namespace S_1
def pairsG : List (Nat × Nat) := [(3, 7), (3, 35), (6, 7), (6, 38), (34, 35), (34, 38)]
def r1sG : List Nat := [3, 3, 6, 6, 34, 34]
def r2sG : List Nat := [7, 35, 7, 38, 35, 38]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_1 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_1 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_2 : Nat := 0xcc00cc00cc00cc
def goal_2 : Nat := 0xcc00c800cc0080
def roots_2 : List Nat := [0x88008800880088, 0xc000c000c000c0, 0xcc000000cc0000, 0xcc00cc00000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc000000cc0000, 2, 18)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xcccccccccccccccc
def goal_3 : Nat := 0xccccc8c8ccccc080
def roots_3 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc00, 6, 14)] (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_4 : Nat := 0xf0e0f0e0f0c0f080
def roots_4 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 6 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0xff00ff00ff00ff
def goal_5 : Nat := 0xee00ea00cc0080
def roots_5 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc, 5, 7)] (by decide +kernel) (by decide +kernel) low_2

def dom_6 : Nat := 0xffff0000ffff
def goal_6 : Nat := 0xfaea0000f080
def roots_6 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 6 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_7 : Nat := 0x5555555500000000
def goal_7 : Nat := 0x5444504000000000
def roots_7 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

namespace S_7
def pairsG : List (Nat × Nat) := [(34, 38), (34, 50), (36, 38), (36, 44), (40, 44), (42, 46), (42, 58), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [34, 34, 36, 36, 40, 42, 42, 48, 52, 52, 56, 56]
def r2sG : List Nat := [38, 50, 38, 44, 44, 46, 58, 50, 54, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_7.map (· &&& dom_7)
def goalM : Nat := goal_7 &&& dom_7
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_7 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_7 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_8 : Nat := 0x5555555555555555
def goal_8 : Nat := 0x5444504054445000
def roots_8 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555555500000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_7

def dom_9 : Nat := 0x3333333333333333
def goal_9 : Nat := 0x3222322232003000
def roots_9 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0xf0f0f0f0f0f0f0f
def goal_10 : Nat := 0xe0e0a0a0e0c0000
def roots_10 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9

def dom_11 : Nat := 0xf000f000f000f00
def goal_11 : Nat := 0xe000a000e000000
def roots_11 : List Nat := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 4 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

def dom_12 : Nat := 0xff00ff00ff00ff00
def goal_12 : Nat := 0xfe00fa00fe00f000
def roots_12 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f000, 8, 12)] (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xffff0000ffff0000
def goal_13 : Nat := 0xfeee0000fecc0000
def roots_13 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_14 : Nat := 0xffffffff00000000
def goal_14 : Nat := 0xfeeefaea00000000
def roots_14 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13

def dom_15 : Nat := 0xffffffffffffffff
def goal_15 : Nat := 0xfeeefaeafeccf080
def roots_15 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_15
def pairsG : List (Nat × Nat) := [(1, 33), (2, 18), (3, 7), (3, 19), (3, 35), (4, 12), (5, 7), (5, 13), (5, 37), (6, 7), (6, 14), (6, 22), (6, 38), (8, 12), (9, 13), (9, 25), (9, 41), (10, 14), (10, 26), (11, 15), (11, 27), (11, 43), (16, 18), (17, 19), (17, 25), (17, 49), (20, 22), (20, 28), (21, 23), (21, 29), (21, 53), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 38), (34, 50), (36, 37), (36, 38), (36, 44), (40, 41), (40, 44), (42, 43), (42, 46), (42, 58), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 2, 3, 3, 3, 4, 5, 5, 5, 6, 6, 6, 6, 8, 9, 9, 9, 10, 10, 11, 11, 11, 16, 17, 17, 17, 20, 20, 21, 21, 21, 24, 24, 24, 32, 34, 34, 34, 36, 36, 36, 40, 40, 42, 42, 42, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [33, 18, 7, 19, 35, 12, 7, 13, 37, 7, 14, 22, 38, 12, 13, 25, 41, 14, 26, 15, 27, 43, 18, 19, 25, 49, 22, 28, 23, 29, 53, 25, 26, 28, 33, 35, 38, 50, 37, 38, 44, 41, 44, 43, 46, 58, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_15.map (· &&& dom_15)
def goalM : Nat := goal_15 &&& dom_15
def NN : Nat → Nat
  | 2 => 1
  | 3 => 7
  | 4 => 32
  | 5 => 160
  | 6 => 441
  | 7 => 345
  | 8 => 23
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x1e28f1de
  | 3, 0 => 0xd76e37a4bbd9189b8f4a628e55b558c92cc052e4222c7ddf0e1af3a6
  | 4, 0 => 0xe141fd41da1e18d9d2604107d0341adcc720c60dc6d6c979c1b6ba48bcdf574ca7fe6f35a0f69aa9991e282b8a09e27c8269a8247aff52b46de3619369dda514690dc4fe644cb9cf59b8e4ca4875a9e642f7b56d3c92e11a3b17929239a8f530253d0c96227d77472135594d1220396c09861a8c0631274903d5c90902f4baeb
  | 5, 0 => 0x37ca88eb3574cd493566e80b3566c70d33c9ffc433305b86328fba183210d20530d6b6c530198c392f8deb682ecd01b42ec9d7862ead3fb82dcdeb172d5371672d2ec1b82c22e3092c15a6212bed559b2b71f0412b5203712aada6d02a23da6e2865d77a28605c1f284480fa270c2ba02527842022c4e84a21b063282075da642039f20f1f50bbd11c00ccfa1b697b771ae4e1641a16d3db18f26c4c181d7b9215bfb69214f6ad4b14abe851133e091412fc993211e034c0119dfe101153752410d606ee0e029bc80d89a68d0d79cb890d215a2c0b76be730b46ec9f07f4bdbf07c081c706eb8f42061ff02303e95633020e17cb0105e6ea009b218100458cb8
  | 5, 1 => 0x88df30a8884ce015845407c9825eaa8c7fcc94cc7e73559d7d2ffe037aff52b4796d6ffc786cfdbb751113a072e18a9b72c5d62071cc7ce16fdc96956ef98cb76ecb5e0c6e5661bc6de361936a8b0731698ee7b667535a5b6751c7e765b58cf2658e798763474bf4627701ec61d7af80610c61d95f97c2d65e2c2c165de38ba85d58fd065c4eedba5a09de3259be44955998eb605915f40d5871d44e5796e9b056099c91548f85d353b95bd153611af552be2f9450c3bb25501d9f5d4e62b0254e05964a4dfe2632499d722d47bbe74347b4abff461b5c1944ae3fb043dcb21840de583340183da43dd43d493d46afec3a84e77139bf1eb538c28e5738a27cd7
  | 5, 2 => 0xfead2cf8fd2d0a86f1d8600ee0ba1474dbd937a4d0aa8f16cb0f381bc809920cc759db72c5f0fb2fc0a10220c006d447beb7f9d3bbe6dd5cb5fb4010aa879d64a9d2034fa73d73d6a521a125a4e24862a35c9dd69bfb8f4d9a40fa0e956daad3955532ce93fd123c937f152d8f95c6338e0ba0b88e0120b48b7945308ad3bad7
  | 6, 0 => 0x1474608f14736e85146bdca814696ac213ea83c213e0e2a713346ed11327faa1130a5a8912ed399911d430a6119fba611106ad57109faa42104ad074102497a91004efa20fec104b0fe0ec5e0ef737100ee2d2210dd633720db753420d6e8d170cd4b54f0cd412060c60dcf80c3193340c0930a10bb0c3ae0b5bd3a60b2c8ce60ae653d70a7677f509da5e540955e87809480ced0938390c0919997808ba381d08b0816608828543074eba9406f72c6106dc98420681af19065d5685063e9172060e91e70562a0ac0559e5f5053c7a0b0518880e04963a7b04321371041db66f0415b2f30380978b01e3cad001ad4403019c9fad00f94cd000e6aadd006c2684
  | 6, 1 => 0x2af8e8dd2ac54d632aa964312a180b4c2a16023a29d10a3229af2b6428e1d56328a4a83e2842fbd327d2a877275dc4202750b4f62738adc8267b41f52602ca6f2566dfcd2467744a244f823f237fdc3822d25b5c225998972246c52022016d1d21997fae217ce77421144ec6208100301f75faad1e9a7a0a1db72cc41d4c60a11d07cbc61c7f55261c6f9fec1bb3fa5d1b805bb41b27d2611b16f5ed1aa1953a1a26397919ba87fd19ba301a1927b99a18eb5771188e19d0188da69318545dd6176fbdf717617b9e17497f4a172c136016dbf17016bcc03716b01e5416528f3516446b9c16424e12163cc66615fc5b66155ed0bb1517feab14c15aa41476b364
  | 6, 2 => 0x4614d99b45a7f59844d46f784408d56743e3db9743ad1469435fdc0743110caa4270b5be4267af6a4221143d414a8c1f4149254d412c1b38404b30133ff0f5f13f1e2b9c3e7b57fa3db4e4813d8f565c3d8a3cae3d2c7c353ceb95653c346cd83b754d643b33d6c03a4fc2063a2d6c62382963983821da66380d7bfe37fdfb7837a858a7374682113727f4ba36fb367836b5383e3609387935a96a46357f7388353aa3c634a771a733da662c33da452e333d305e321d7eb2315c50af3156fc53313ee4c53117e4f430ba24d82f3c81e32f2d39052e450d9e2e2eb6002e1a843f2df741622de6358a2db09fc22cadc4612c42325c2ba8f9b52b8af0a62b81626d
  | 6, 3 => 0x606e2c97601c8a0d600ad1db5ff7afde5ed6a3f15dda43b15da6006b5cac1ec35c9b90375c97debb5c5ce06b5bb03c075acd55a859b9b5c259a0c2fc5925466958f528b758e6c546589311d45802414f57a4871956488c3a5618ad1555f9c36e55c7af295571ce4a54bd497554b1935f54a96c0954652f1353dbb72c52f5cae35257aedf51f4fa8951cda2a251c09e335160844350d485a15074cc075014114e4f050fd04e92e7bf4e20ca5e4e1018c74dd542384d84259f4d4c1d7d4c8a818c4c88dffd4c0f52314ba1260e4ab9d7494aabf4e84a3f5f3c49dd0e9149b6983f49ae9520497253c148c35a8b48683a6347c34c8b473ba52946f1b3114619497e
  | 6, 4 => 0x8069eaef7fe02d2f7e7a0a4c7e7152747e4b58517d41b0af7cf270267c039c0f7a399f0c7a2a8dff79e15a2879bb6d1e7961f7277829da4178299fcd7800865577ae3ab077abf413765f7057754fe6cf751532dd7481ccfa74789e6473f739d4737d02ed731a9a377301de5f729c25ac72957302727718da7218e0f571ff99de71c86787715bc440702ba0066f4c3cf56efba8276ec7a3626e1c26fb6def4db26d65318d6d2a833e6cc7f9b76bf360ab6be903d06bba04806b9d976b6a41599e6a0829146909bb4667d2ecc6676fce60673f974f672edba166540d4c6502386064610497643988c963939f336326e6d962bd28d8627050f961cd881d60fe5bb2
  | 6, 5 => 0xa3d366b3a3a56a26a275f6c8a0d162fda01e0a0a9f2620f29ec0d7899e5f82759cefd78c9af9d2839a881050993a7ae3992cedf8989a69279847a6bd97a002259798951796964552968d4d5f967fbfcb9551aacc951cbb329464b8f8940a6f8394028408938861299311a06b928065269148b1039063583d9022657e8fee4cee8fd304808e965ddb8e52fbf68dc082c58d5eaaf98c9b3efd8c7bea548ae257588aace1a08aa44b2d8a81f0ca8a0b34fc89cee35d87b2ceb4879add6786a84c4a863f7c59863f5b5b85f6241e84dec8e884d9addf849e475c847e77b184129c4083eaa2da83b173988362117782e72b36827963fa81f6d6c281b726b38123ee88
  | 6, 6 => 0xf6281cb5f48bd63cf250bba1eef3064deb93c63beb4fcf47e86bd220e545e120e09b3ae1de90f3a7db711277da650bedda329af0d8fa85f9d872797ad6382f23d5aad949d53d3f66d52b0a13d3ab69cdd30d2ad5cd0facd0cccaebe6ccc7daa6cb2ff1f8ca5180ccc63e4d23c5b0f683c3606443c1e70f7dc148abb5c111313ec10e3d6bc08f171bbfd8f6fabde1cfb5bace5c64bab9a1bdb9ab4d11b91d4ce9b86243b6b64b2e2db5b55af9b47c9722b3a5c8ecb2c0fc52b0cf1072af647c31acc719e5abe9481fabc0f8acab676f4faa2ce68ba94c64a9a8afe02ea8249059a55beef2
  | 7, 0 => 0x2046aaad2014c6441fd3d3851e3d0e221e1aa3ae1d989e101d81c57f1d29fe0a1c1ffead1b8548e61b52f33219b1d4481979f4171923eb0b181aa94117a82026175a929b170db67f16e8db1816b50ee9141a4f1c1415063f1413d60813b5da6d1317dd2b12b8884a11eb7ccf1198114410d1aa96103ead2a0ff073950faa77070f8898390f6b9a140f3d84400edd17080e7e15130e7dd0190dfb96ef0d9cbe430d91ebc20d61f2fb0d52c9a60d4d98860cb3009d0cabde0a0c2cfbb60c22507d0bd753a90afb5dd30acf09dd09ee1b6f0754ea1506b07a0306291d8305ad2f3405a3eb0a05869eb10291d00a023f103c01a603fb01013f360086a50c00273479
  | 7, 1 => 0x39500340387c221637dd7e8037b9fc1b36c744ae36b6da92366fa272359f67e7359aee6d358e7c1335743559354bc4fd34ceb8d13481847a34746a9f339be830330961a632ba82ac3264f194317141fd3129ad3f3122199e30bda81a3055c0a6302ca7772fc976f62f1362052ea0b9112de85b922d90db782d6df75a2cb7e2692b81626d2b698d6c2b0f56702acd7a982a6cf07129c478db2964176b292df8a128a4a83e2889888f2774c460275958f22705880d26beaf6f26bb2fef26396ad4260932412509c4b8246554a62429651523a7fde62310763b23038dd422daf26b22d85c9a22c73513223682592219ec0a21e9d24d21a5f9682179389d2081cc61
  | 7, 2 => 0x62623a3561ca400860b58bf55fbac6fd5f492eb65dc82fa15d6275f45cde0cce5b2acd5959e9c31b58905d13584e132a57c35198568ff7f1567ee6cd5640306854b47b98531915d15314eaf6530ec13f52942b72523dc21151ee61ea51d2062b51099cc650c4b4ed505beeb35038abd64f943bc44e9d19034e79bd534e1717654dc27b5b4d17706a4cfd734b4ca60af44c1326ad4bff26be4bc969994b7591cb4b0c2c394afc5e1e4a3f78dc49e125c6499b08ca48b0ac9d472e33c145f6b58445d91ef1457c5ed143a9f8484223bdb941d622d3413f306a4079af633f49363a3ee6de3d3cedcf813c9d75a23afd7b253a8b9b213a861c993a476634396f572d
  | 7, 3 => 0x8ebf00228d5eaaf98b7e195e8a81f0ca8a7994f88a0d10dd8968a0cb877c8a9f872610b88651842c85f48e9f85e99b5485520fcd85210b038492c7cd83f048fb83c5bc5283233d80830766bf804281917f27d8097dd5c4a57db173387d356db97d303bbe7cea112d7bf0d3337b2b17a17b25f4ae7ab597257aa1574779e15a2879a4d76c791d9b41785a17897770373f77211a3f76f0de3376db0b2e74f2245d74d2ee78727daf3d7260e48f70c4152b6f6c29a26e834bca6e8018a76dcb09b56c4b6e046be1bd3a6bcb63fb6a7ff6686a0139de69b2eaed67f1c0d367044c4c6554bad1651506a464f3896864e30e64647899486449b75d63669d956347643b
  | 7, 4 => 0xd0ab600ecf84bc20cea2794ccd73df73c7466283c5e58a67c59d6c30c5821593c5690328c52f7576c4eae2e7c21dcfbbc110cb7dc1043454bf01fb40bef4bb49bef1afedbeb2f988be4be64fbde1cfb5bcb2dff7bbec3344ba477786b9fc935bb7a1fd24b59a84ddb559ed2fb4e46fecb4d0d4a4b37ef559b253eee6b22e7c90b0f51e5bb03d009faf95e2ffaabfa2cbaa8df529aa38618da98c5b5da8d69abba8098f40a5103ec2a4dede88a4a02823a309310c9e58572e9e3c45669bfcd7929985b807992721c2989a692798411d8197a4f3879710a45896a4b77d965f34589603a49895a996be9351acbb92ef453392b08ece9117715e90061e318f6e2404
  | 7, 5 => 0xfd875a02fc3e0176fb7259a6f6f16d4af6657479f33b5fd0f32a1730f117a0a5f109fd47f03d9387eef3064dee22ff53e606f433e1b94d76e1283faae0d9cf49dede789bdec49712dd0995b1d87f9952d697c1d4d27a66b2d1293c1cd0e5095fd0dd3a20
  | 8, 0 => 0xf33b5fd0f2854adfb47be6218ab84b5d8a7994f87f4590c97e1a8a567cea112d76f0de3361ca40085fbac6fd5cde0cce51bb2a0f5059633d4f8c57c24aee737942b779a33e277fff1606144c1561a43a1142fa410e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x555500005555000000ff000000ff00000000ffffffff00000000eeeeeeee0000000055555555000000000fff0fff0000000000ffffff0000000000ff00ff
  | 0, 1 => 0x3300ff003300ff0000ffff0000ffff0000ffcc0000ffcc0000ff000000ff000000f0f00000f0f00000cccc0000cccc0000aaaa0000aaaa00005f5f00005f5f
  | 0, 2 => 0x50555550505555500ff00ff00ff00ff00fa00fa00fa00fa00f000f000f000f000cc00cc00cc00cc00aa00aa00aa00aa00555555005555550055005500550055
  | 0, 3 => 0x3f3f3f3f3f3f3f3f3c3c3c3c3c3c3c3c33333f3f33333f3f3333333333333333151515151515151511115555111155550f0f0f0f0f0f0f0f0555055505550555
  | 0, 4 => 0x55555555505050505555550055555500555055505550555055445544554455445500550055005500545454545454545450505050505050504444444444444444
  | 0, 5 => 0xa0a0a0a0a0a0a0a088888888888888888080808080808080777777777777777766666666666666665f5f5f5f5f5f5f5f55555555555555555555555555005500
  | 0, 6 => 0xaaaaa0a0aaaaa0a0aaaa5555aaaa5555aaaa0000aaaa0000aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa88aa00aa88aa00aa00aa00aa00aa00a8a8a8a8a8a8a8a8
  | 0, 7 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaaaa000000aaaaaaaaa0a0a0a0aaaaaaaaa000a000aaaaaaaa88888888aaaaaa00aaaaaa00
  | 0, 8 => 0xc888c888c888c888c0c0c0c0c0c0c0c0afafafafafafafafafaf0f0fafaf0f0faafaaafaaafaaafaaaaafafaaaaafafaaaaaaaffaaaaaaffaaaaaaaaaaaaffff
  | 0, 9 => 0xccccc0c0ccccc0c0ccccc000ccccc000cccc8888cccc8888cccc0000cccc0000ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc00cc00cc00cc00c8c8c8c8c8c8c8c8
  | 0, 10 => 0xcfcf0000cfcf0000cccccccccccccccccccccccccccc8888cccccccccccc0000cccccccccc00cc00ccccccccc000c000cccccccc88888888cccccc00cccccc00
  | 0, 11 => 0xeaeac0c0eaeac0c0eac0eac0eac0eac0e0e0e0e0e0e0e0e0e0e0a0a0e0e0a0a0dddddddddddddddddddd5555dddd5555cfcfcfcfcfcfcfcfcfcf0f0fcfcf0f0f
  | 0, 12 => 0xeeaaeeaaeeaaeeaaeeaacc00eeaacc00ee00aa00ee00aa00ececececececececececa0a0ececa0a0eca0eca0eca0eca0eaeaeaeaeaeaeaeaeaeaeaea00000000
  | 0, 13 => 0xeeeea0a0eeeea0a0eeee0000eeee0000eeeaeeeaeeeaeeeaeee0eee0eee0eee0eecceecceecceecceecceac0eecceac0eecce0c0eecce0c0eeccaa00eeccaa00
  | 0, 14 => 0xeeeeeeeeee000000eeeeeeeee000e000eeeeeeaaeeeeeeaaeeeeeaaaeeeeeaaaeeeee0e0eeeee0e0eeeee000eeeee000eeeeaaaaeeeeaaaaeeeeaaaaeeee0000
  | 0, 15 => 0xf0a0f0a0f0a0f0a0f080f080f080f080f000f000f000f000eeeeeeeeeeeeeeeeeeeeeeeeeeee0000eeeeeeeeeecccccceeeeeeeeeeaaeeaaeeeeeeeeee00ee00
  | 1, 0 => 0xf0f0f0f0f0000000f0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f000f0f0f000f0f0a0a0f0f0a0a0f0f00000f0f00000f0c0f0c0f0c0f0c0f0c0f000f0c0f000
  | 1, 1 => 0xfa00fa00fa00fa00f8f8f8f8f8f8f8f8f8f88888f8f88888f888f888f888f888f0fff0f0f0fff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f000f000
  | 1, 2 => 0xfaf0aa00faf0aa00faeafaeafaeafaeafac8fac8fac8fac8faaafaaafaaafaaafaaafaaafa88fa88faaafaaafa00fa00faaa0000faaa0000fa88fa88fa88fa88
  | 1, 3 => 0xfafafafaf8f8f0f0fafafafaeaeaeaeafafafafac8c8c8c8fafafaaafafafaaafafafa00fafafa00fafaf0f0fafaf0f0fafac8c8fafac8c8fafaaaaafafaaaaa
  | 1, 4 => 0xfcccfcccfcccfcccfcccf0c0fcccf0c0fcccf000fcccf000fafafafafafafafafafafafafafaf0f0fafafafafafaaaaafafafafafaaafaaafafafafafa00fa00
  | 1, 5 => 0xfeee0000feee0000fcfcfcfcfcfcfcfcfcfcfcfcfcfc0000fcfcfcfca8a8a8a8fcfcfc00fcfcfc00fcfcf0f0fcfcf0f0fcfca8a8fcfca8a8fcf0cc00fcf0cc00
  | 1, 6 => 0xff00ff00cc000000ff00f000ff00f000ff0000ffff0000ffff000000ff000000fefefafafefefafafeeefeeefeeefeeefeeefaaafeeefaaafeeef000feeef000
  | 1, 7 => 0xff88ff88ff88ff88ff888888ff888888ff880000ff880000ff80ff80ff80ff80ff55ff55ff55ff55ff33ff33ff33ff33ff0fff0fff0fff0fff00ff00ff00ff00
  | 1, 8 => 0xffaaffaaffaa0000ffaaffaaff88ff88ffaaffaaf0a0f0a0ffaaffaacc88cc88ffaaf0a0ffaaf0a0ffaaaaaaffaaaaaaffaa0000ffaa0000ffa0ffa0ffa0ffa0
  | 1, 9 => 0xffccf0c0ffccf000ffccf080ffccf080ffccf000ffccf000ffcca080ffcca080ffcc0000ffcc0000ffc0ffc0ffc0ffc0ffc0c0c0ffc0c0c0ffaaffaaffaaffaa
  | 1, 10 => 0xffccffccffcc0000ffccffccff88ff88ffccffccf0c0f0c0ffccffccaa88aa88ffccffc0ffccffc0ffccff88ffccff88ffccff00ffccff00ffccf0c0ffccf0c0
  | 1, 11 => 0xfff0fff0fff00000fff0ff00fff0ff00fff0ccc0fff0ccc0fff0aaa0fff0aaa0ffeeffaaffeeffaaffeca0a0ffeca0a0ffccffccffccffccffccffccffccff00
  | 1, 12 => 0xffffaa00ffffaa00ffffa0a0ffffa0a0ffff8888ffff8888ffff5555ffff5555ffff0000ffff0000ffff0000ff000000ffff0000aaaa0000fff0fff0fff0fff0
  | 1, 13 => 0xffffccccffffccccffffccccf0f0c0c0ffffccccaaaa8888ffffc0c0ffffc0c0ffffaaaaffffaaaaffffaaaaffffa000ffffaaaaff00aa00ffffaaaacccc8888
  | 1, 14 => 0xfffff0f0fffff0f0fffff0f0fffff000fffff0f0ffffa0a0fffff0f0ccccc0c0fffff0c0fffff0c0fffff0a0fffff0a0fffff080fffff080fffff000fffff000
  | 1, 15 => 0xffffffff55005500ffffffff33333333ffffffff00000000ffffffaaffffffaaffffff00ffffff00ffffff00f0f0f000ffffff00aaaaaa00fffffaaafffffaaa
  | 2, 0 => 0xffffffffaaaaaaaaffffffffaaaa0000ffffffffaa00aa00ffffffffa0a0a0a0ffffffff88888888ffffffff80808080ffffffff55555555ffffffff55550000
  | 2, 1 => 0xfffffffff0c0f000fffffffff000f000ffffffffeeeeaaaaffffffffccccccccffffffffccccc0c0ffffffffcccc8080ffffffffcccc0000ffffffffc0c0c0c0
  | 2, 2 => 0xffffffffffffaaaaffffffffffff0000ffffffffffccf000ffffffffff880000ffffffffff00ff00ffffffffff000000fffffffff0f0f0f0fffffffff0f00000
  | 2, 3 => 0xffffffffffffff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x3f5a0b13
  | 3, 0, 0 => 0x7eb754a3f47eb25563f47eb414a3f47ebddb2b147eb41503f47eb40fa7148b44d4c3f4
  | 4, 0, 0 => 0x7ebbdc0a51fabf5eed9540fd5faf76c9f4e2b1689bdd4e3f584bdd70942b2bf568ab230fd5fab84d1f09ab1689a04983f589bf5c6a61fabf5c6d04a1595fada5c290acafd78365147457ebdd70b12b2bf5ac8a370fd62acd451587eb1689bdd28565
  | 4, 0, 1 => 0x7eb74fa4c1fabf5eed14a1595fae349a28acafd68228a03f57eb4104491fabf5eed9528fd5faec5c2947eafd67228ac3f57eb8d908a352bf5f6c9570fd5fad03e9307eafd5c290de5657eae1147b26abf59a8a2b0fd5fae35c2987eafd67a28ac3f5
  | 5, 0, 0 => 0x7eb31708a2b0fda2d137b9f4ac3f67ebdd707d389599faf15fa28ac3f689bf5c6d9550fd9faf87bae1285667eb8da48a3e0fd9fae3479587e0b67ebddb28a280fd9faf75c204983f67eb99a28a2b0fd9fae34a228ac3367ebadc6d2451f19faf75c260f85667eb8d947d260fd9fae362a28ac316
  | 5, 0, 1 => 0x89bf5c6d9451c59fae364228d05667eb8d70b24511d9fae35c299023f68a38d7e8a2b0fda26fd7bb8d285667ebed688a3e0b99faf75c2a0ac3f67eb41708a260fd9faf05c228f82e68b38d8c8a2b0fd9fae35f2e1147c684b8d70a42b0bd9fae36ca95143f67eb8dc07d3e0b99faf775ae14e3f6
  | 5, 0, 2 => 0x7eae114702b0fd9fae36ca28c43f67eb8db2a43f9599fae35fa51145667ebc19a8a2b0fd9fae65c290f85667eb8d92b8570fd9c6b8441587e3b67ebdd7082358fd9faf75c25cac3f67eb8d70a02b0bda24e65c228ac3f67eb8da294451599fae03e9b8ac3f67ebed68ae230fd9fafb68228ac3f6
  | 5, 0, 3 => 0x7ebad709a3e1599fae35c228d43f67eb8d908a278c5a2d135c2289e3f689c45c6812b0fda1ee368a28ac3f67ebdda48a2b0fd9faef5c295143f67ebbd709445131a2d0b5c2289e3f67eb8d70a4319599fae35c2ac8c3f67ebdd90b84c1599fae35c2209e3f689b8d908a2b0f99fae35ca28d63f6
  | 5, 0, 4 => 0x84bdd707d2b0fda2d1371a51145667eae1146e2b0eda26e36ba28ac3f67eb8d90ae230c59fae35c2049e3f67eb8d1e852b0fd9fae36cb21147167eb8d708a348fda1cea5c228ac3f68b3f5707d278fd9fae3451fcac3d67ebdd7e822b0fd9faeb69228ac356872e1146e2b0fd9faed5c228983f6
  | 5, 0, 5 => 0x7eae13456268fda22e36ca20ac3f67ebddc6d94a159a26e36aa28ac3f68938d728a2b0fd9fae6642e1485667ead1568a2b0fd9fab84ca28983f67ebc1b28a260fd9fae35c2c5145667ebe1709145159a2cfd5c228f84d67eae15e94451599fae34a241145667eb21146e2b0c59faf76c228ac3f6
  | 5, 0, 6 => 0x71ae114772b0fd9faeb701f4ac356003f5c6b8530fd5faf068a28ac3f67ebdd70a22b0fd9fae34a249145668938d708a3d0fd9fab8521b8ac2f67ebad90b84d1599fae364281145667eb8d487f2b0c5800fd71ae07e1e57eb9970a432159a26fd7bb8d4e3f67eb8d908a2f1599fadd5c228983f6
  | 5, 0, 7 => 0x873bd708a260fd9faf55c290ac3f6873ad708a2b0d5800fd5aa28ac3f57eb69708a2b0fd9fae36ca28ea3f68738da28a2b0fd800fd66a28ac3f57ebdd70942b1319fae3699f49e3f67eb8db2a4248bd9faef701f4983f68b3a5708a2b0fd9faeb5c29d143567eb8d769445159a12e65c228ac3f6
  | 5, 0, 8 => 0x7eb8d70a5230fd9fae368228923f684b8d709f2b0fd9faeb5c228e6566003f5c6b8450ad5fab8451c4ac3e67eb8d7081268fd9fab858228ac3f67eae1146e240fd9faf768a00ac3f68b44dc6a7450fd9fae363291145667ea3d146e2b0fda12e35c251145667eb95c6bf451f19fab8451c8ac3f6
  | 5, 0, 9 => 0x7ebddb282248fd9c6b8451d8ac3f68938d70ae230fd9fab84a228dc5667eb8d208a2b0fd9faf76c9f4983f68938d70a42b0bd9fafb64a28ac3f67eb2d70a42b0bd9faf05c228e8566003f5708a2b0d9614e65c228ac3f68b3f57081260fda26eb5c228ac3e689b8d8a8a2b0fd9faf764208ac316
  | 6, 0, 0 => 0x7eba1c6b8451587ef1271ae114561f8a5e0efd71ae14e8a1fbc1dfaf05c228ac3f78b3f5b2b8451307eefd71ae1188a2b0fdc00fd5c228ac3f0433f5d6e35c228d63f7003f5d8b8451307ec007eb8d70812b0a5a0efd71b80fa561fbbf596b8451587e2977ebddb2b8411587ef0e71ae1147c2b0fdc00e35c2289e3f02b3f5eeb8411587e2e7
  | 6, 0, 1 => 0x7eb8d708a2b0fc48e0071ae1147c170159faf05c228ac4c1fb801facb451f4ac3f689bf5c67d2b1187ef077ebed688a2b0fdc00fd2b0fc32160733f5c6d1451587e2f7863f5c6e03e9587eefd7bb8d708a358fddfaef71b80fa561fb8021ce36ca28ac3f68738d708a2b0fc74efd71b80fa56260fddfae363ae114561fb801fae35c228e21c6
  | 6, 0, 2 => 0x863f5f6b4451587eefd71ae1485617859c00fd71ad9143f0e33f5c68a3e9587e3370038d708a2b0fc08cfd7cb8d708a2b0fde24e35c2b914561fb801fae35c2b87e1f67eb8dc07d2b0fc1cefd71ae114712b0a5dfafb5a228ac501fbbf5c6e05c228e2567863f5e0b8451587ee007eb8d908a2b0f5a24e35c228ac3f173bf5f6e35c228f82e7
  | 6, 0, 3 => 0x86bf5c6b8451c4acefd73301708a2b0fde24e35c2290e561fbbf5deb8451307e2f77ebedc6b8571187ef037eb8d708a3e0b9c00e35c2b88c3f02b3f5c6b95a228ac3f77eb8d7eb8451f05cefd5c228ac4c1f8f9dfae35c228f8561db801fae35c268ac2967eb8d7e8a3f1587ee007ebdd70842b0fd9fae35c29d143f073c59c6b8451587e397
  | 6, 0, 4 => 0x7eb8d70b3451c4acefd71b65288a2b0fdc00fd71ae14e3f0cb001faf05c1587e1967ebadc6b84a228acefd71b65708a1f881c00fd701f4ac3f073415fae364228ac3f77eb8db8b8451587eefd71ae1147c1f84ddfaeb71afd14561fbbf5c6b8451587e1777eb8d70a42b0bc38f167eb8dc07d2b0fdc00e347a28ac3f02b45a26e36ca28ac3f7
  | 6, 0, 5 => 0x7eb8d70a4451f05cf0e71ae11456260fddfae35b228ac3f173bf5c6d9451f4983f7823f5ccb8451587ee007ebed68561f8659fae35c2a514561fbbf5eee35fa28ac3f7003f570a7450fc1ccfd71b6d708a38959c00fd718fc38190b33f5c6b84d1587e1678938d708a2b1187ef167eb8d70a7450fdc00fd71ae0fa4f1fb3f5c6c8451f0ac317
  | 6, 0, 6 => 0x401c6b84515852cfd71ae1144f1f859dfaeb71b4914561fb801fae3451587e0f68738d708a2b0fc1cefd71ae11456218fddfae35c2b8ac3f05bbf5c6d1451587e3177eb8d70ad451587ef167eae11456278fddfee35c228ac3f14bbf5c6c25c228f85677eb8d70a44515824efd71ae134561f871c00fd7bb4514561fb439dee35c228ac3f7
  | 6, 0, 7 => 0x38db28a248fc0acfd722e11456260fdc00fd782e1143f0e3001faf75c224ac3f67eb8d708a2b1087ee008738d70561f865800b82b0fc320e02b3f5c6b852158922f7003f5c6b82b0a432cfd7d38d708a2b0fdc00fd73228ac3f0b3001faeb5c228ac376003f5c6e03e8fc38cfd71ae1388a2b0fdc00fd5c228ac3f06b445fae35c228d63f7
  | 6, 0, 8 => 0x7ebc1708a2b0fc52efd71ae114712b0bdc00fd71a3d145614b41dfae364228ac317003f5c6b85711852cfd71ae114662b0fddfab852228dc561fb801fae35c228f84d67eb8d708a3e0b82cefd71b80fa561f8a5dfaef5c228983f18b8021cb8451587e0e67eb8d708a2b0fc4aefd71ae1288a2b0d5dfae35c228e25c2b3801fab845158520e6
  | 6, 0, 9 => 0x7eb8d708e451f05cefd71ae154561f8c5dfae35c268f8561fbbf5c6bf451f4ac3f77eb8d70ae230fc2cf0c7eb8d908a2b0c5c00fd71b1914561fb3f5c6be5c228ac3f77ebed688a2b0fc52efd77b8d908a2b0c5dfae364228ac4c18bc5a26b845158983f700425c6b82b0fc32cfd71ae13456248fddfae35c29d143f14b80204e35c228ac3f6
  | 6, 0, 10 => 0x7eae1146e2b0fc2cefd7bb8d707f2b0fddfae347a28ac3f0e3bf5f6b457228ac3f77eb8db2a4451247ee005c2287e1c070159fae35ca28ac3f18bbf5c6ca5c2b88c3f77eb8d708a2b0fc30efd7dad114561f8b9c00e35c0fc381902b3f5c6c845158620e784b8d90b8451587ef117eb8d7e8a2b0fde26fd71ae1485617bbf5eeb8411587e317
  | 6, 0, 11 => 0x3f5eeb8451c4acc007eae0ac290c839a0efd71ae1485617b801fac845158620e68738d708a2b0fc52e007eb8d7056220fda1cfd71b6514561fbbf5c6c860a28ac3178b3f5c6c84515862efd71ae1147c278fde06fd71ae1147c1fbbf5c6bf5c228f83f789bf5c6b84d1587ee007eb8d9056188659fae35c29106561fbc1dfae35c204ac3f7
  | 6, 0, 12 => 0x89bf5c6b84513c7eefd71ae1308a3e159e18fd71ae1485617bc4dfae3451fcac3f77eb8d70ab451587eefd77b8d70a42b0bde1ce35c228ac3f173bf5c6d945208923f7003f5c68a2b0fc2acfd71ae14856260bddfafb5a228ac461fb801ccb8451587e056003f5c6b84515834d0b7eb8d708a278fdc00fd71b65144914b3f5c6b8451c4ac1a7
  | 6, 0, 13 => 0x7eb8d70ac451587eefd71ae11481260fde24e35c228ac3f1e3bf5c6c95c228ac3f77eb95c6b8451f05cefd782e11456270fde2cfd71ae146561fbc59faeb5c228f8567003f5688a2b0fc0cd117eb2d708a2b0fddfaf371ae102561fbc1dfae35c268ac3f77eb8db28a248fc32e0071a28ac290b0159faf76cae1144c1fbbf5c6b8451b4ac3f7
  | 6, 0, 14 => 0x3f5ecb8451587ecfd75b8dc07d2b0fddfae35c228fa712b3bf5f6f76ca28ac3f77eb8d708a3c1587ee007eb8d70290e065a26fd71ae1147c173bf5c6b852174ac3f7003f5c6d95c2a87ec007ebdd04561f859800fd5c204ac3f073001c6b8451ac7e056003f5c6c8450c438d137ebd9708a2b0fddfae3642e1487f2b3bf5c6d945210ac3f7
  | 6, 0, 15 => 0x7eb8d708a38994acf0c7eb8d708a278fdc00e368a28ac3f02b3f5d8e35c1f4ac3f789bf5c6b8571187ef1388b8d908a2b0fde0efd71ae114612b3801facb451587e1667eb8d708a3c9587eefd71ae1146c2b0fddfaeb71ae14e8a1fbbf5c6c85c290ac2f7003f570572b0fc32d117eb8d708a38959c00fd5c290ac2f073001fab8450a4380e6
  | 6, 1, 0 => 0x3f5c6bb4515846cfd71ae1147c288fdc00fd71a28e2560b3001c6b84a228ac05689bf5708a371587ee0075ae114561a815a2cfd5c228e2561fb80222e35c220ac3f6003f5ccb84515852c007eb8d708a2a8fd9fae3642b9145618bbf5c6b854228ac3f7003f5eee35c250accfd71b211456250c5dfaf768ae114561fbbf5c6d45c228ac3f7
  | 6, 1, 1 => 0x7eb8d1e8a2b1307eefd732e114561f871dfae3642e1144f1fbc21fae35c2b88c3f70044dfae34a228accfd71b211456230c5c00fd5c2289e3f0733f5c6b8451587e2877eb8d708a2b1007ef077eb8d1e8a2b0fddfae35c228be561fbbf5c6b8409587e2977eb99708a2b0fc2ce0077ae1144c1f815a0efd71ae15c461fb801fae35c2905e1c6
  | 6, 1, 2 => 0x7eb8d908a3f95862e007eae1147c17039801167eae1144f1fb001c6b8551587e0567eb8d86b8451587eefd71b21708a30959dfaeb71ae114672b3c31fae347a28ac3f7003f5c6b84d0fc38cfd7dad114561f8e1dfae35c25514561fbbf5c6d152228ac3f77ebbdc68f451587ee007eb8d708a3e0b1a12e35c2dd14561fbbf5c6b84f228ac3f7
  | 6, 1, 3 => 0x3f570ae230fc1cc007eb8d908a358fd9fae35c228f6561fb801faf55c228ac3f67ebbd70a4451307ee0065ae114561f815800fd792e114561fb001fae368a28ac2967eb8dbeb8451587ef1388b8db28a2b0fdc00fd5c1587e190733f5c6c85c228f82e77eb8d7ea4451587ee007ebdd70982b0fda2ce35c228ac3f1ebbf5c6d95c290ac2f7
  | 6, 1, 4 => 0x7ebadc6c84515862f1689bad708a2b0fdc00fd5c1b8ac3f0cb3f5ccb845158923f77eb8d708a2b0fc22efd71ae168a42b0bddfae35c228ac3f13b801fae35e228ac3f67ebddc6b8441587ef0e71ae114561f8d5e0efd71b6514491fbbf5c6d1451587e1977eb8d90b8571187ee007ea3d14561f8399faee71ae114561fbbf5c6bf5ea28ac3f7
  | 6, 1, 5 => 0x7eb2d70a4451587eefd77ae1144c1f865dfae36ca28923f073801fae35c228b4566003f5708a1f8701cc007eb8d70582b0fd9fae36cae1144f1fbbf590b8451b8ac3f77eb8db28a3f9587eefd7bb8d908a2b0c5c00fd71ae07e1c0cb3f5d6b8451586a1970038d708a2b0fc02c007ebbd708a260a5800e35c228ac3f01341dfaf55c228ac3f7
  | 6, 1, 6 => 0x7eb8d70a1451587ef167eb8db28a248fddfae35c228f84d1fb801fab8451586a076003f5c6d9248fc32cfd71ae13a8a2b0fddfae35c23514561fbc4dfae65c228ac3f77eb8d7e8e451587ef1271ae1488a2b0fde2cfd7bae0fa561fb801fae65c290ac2f6003f5c6b85515852cfd71ae1288a2b071dfaeb5c228ac350e3bf5d6e35c228ac3d7
  | 6, 1, 7 => 0x8938d708a2b0fc32efd75ae11456248d5c00fd732e148561fb41dfae65c228ac3f77eb2d708a2b0fc32efd71a3d14561f8b9c008a2b0fc2c0e02b3f5c6d1451587e32700449c6b84515852cfd71ae1488a38959c00fd71a2cac3f0b3001facb5c228ac2967eb8d1e8a2b0fc52e007eb99708a2b0fd9faf775ae1147c2b3bf5c6b8571187e297
  | 6, 1, 8 => 0x7eb8d7096409587eefd71b11708a2b0fdc01137eb8d4e8a1fb3f5c6b83e9308c3f7003f5ccb82b0fc32c007dad114561f8159fae36ca28923f14bbf5c6b8451a0ac3f77eb8d708a389582cefd71ae102561f8d5dfae35c2d15c461fbbf5c6d05c228ac3f77eb8d709b451587eefd75ae1147c2b0d5e22fd71b21145618bb8d708a30980ac3f7
  | 6, 1, 9 => 0x3f5c6d9451287ec007eb99708a1f8719fae35c29514561fbbf5f6b452228ac3f7003f5708a358fc1ccfd71ae12c8a2b0fddfae35c228ac3f133bf5c68a3f9587e3177ebdd708a2b1507ef077eb8d709445159dfae35c228c2561fbbf5c6d964228983f7003f51456148581cc007eb8d708a1f875800fd71ae1145b103439c6b845158a43f7
  | 6, 1, 10 => 0x7eb8d70ae309187ee008738d708a2b0a59faeb71b6514491fbbf5e8e35c228ac3f77eb8d1e8a2b0fc6ae0071ae0ac290c815a22fd71ae0ac3f10bc1dfacb5c228ac3f7863f5eeb8411587eefd71ae15c461f8c5dfafb5a228ac3f0cbc59fae35c251145677ebb5c6b8451587eefd71b5d708a2b0fdc00fd7dad1145614b3f5eee35c250ac3f7
  | 6, 1, 11 => 0x3f5c6b8451587e2277eb8d708a2b1047eefd71b75708a2b0fdc00fd451587e160733f5c6b8451587e1b700449c6b82b0fc32d0e71ae114561f871c00fd71ae1288a0e33f5ccb85a228ac3f7
  | 7, 0, 0 => 0x88bf5c6b85a228ac3f8003f5c6de5c228ac3f7003f5c6bb5c228ac2970044dfae35c228ac2977eb8d708a3e1587e1687eb8d708a3e1587e198003f5c68a2b0fc521670038d708a2b0fc1c0577eb8d708a309588c3f8003f5c6e0451587e1677eb8d708a411f0ac3f8863f5f6e35c228ac3f87eb8d708a2b1247e19800001fafb5a228ac3f689bf5c6b852228ac3f8003bdc6b8451587e057
  | 7, 0, 1 => 0x1708a2b0fc1c056003f5eeeb5c228ac3f7003f5c6b95c228ac3f789bf5c6e25c228ac3f800001fae35c228ac296003f5c6ae451587e167003f5cee35c228ac3f7003f5c6b8451587e21700449fae35c228ac3f7003f5f6e35c1587e197003f5c6d9451587e16783bf5c6b852228ac3f889bf5c6b845208ac3f800001c6b82b0fc320567ebedc6b845210ac3f8003f5c68a2b0fc5c167
  | 7, 0, 2 => 0x3f5c6b845158903f77eb8d80b8451587e2f889bf5c6b8451587e1c80041dfae35c228ac297863f5c6b852228ac3f8003f5c8e35c228ac3f700419fae35c228ac3f77ebadc6b8451587e31800405fae35c228ac3f77ebbdc6b852228ac3f87eb8d70a445158983f80038d90b8451587e05789bf5c6b8451587e198003f5f6b8451587e0e7003f5c6b8451587e0a7000021ce35c228ac3f6
  | 7, 0, 3 => 0x863f5c6b845208ac3f8003f5c6b84a228ac3f7003f5d6b8451587e35783bf5c6b8451587e168823f5c6b8451587e2f883bf5c6b8451587e19800431fae35c228ac2970045a26e35c228ac3f7003f5dee35c228ac297003f5c6ca5c228ac3f7003f5c6b84515898297003f5c68a2b1187e16783bf5c6b845208ac3f80044dfae364228ac3f77ebddc6b8451587e3188b3f5c6b8451587e3e8
  | 7, 0, 4 => 0x3f5c6b845158a63f7863f5c6b8451587e168863f5c6b8451587e1987eb8d90b852228ac3f87ebbdc6b8451587e16888bf5d6e35c228ac3f87ebbdc6b8451587e1987eb8d708a2b1307e168003f5c6b845158a23f7003f5c6b8451587e1077eb8d708a2b1307e198003f570a4451587e0e77ebadc6b8451f4ac3f8003f5c6b845158520e789bf5c6b845158a63f88b3f5c6b852228ac3f8
  | 7, 0, 5 => 0x1fab845158520e6003f5c6b8411587e19783bf5c6b845158a23f8003f5d6e35c228f8567003f5c68a2b0fc5e167003f5c6b8451587e2a7003f5c6b95c1587e1977eb8d708a2b0fc2c0e800001fae35c158521967eb8d708a2b0fc320e87ebedc6b8451587e298003f5c6b845158963f700001fae364228ac3160038d708a2b0fc52057003f5c6b8451587e377003f5c68a2b0fc2c147
  | 7, 0, 6 => 0x3f5708a2b0fc2c0e7003f5c6b8522287e1c7003f5708a2b0fc320e78b3f5c6b8451587e168003f5d6e3451587e167003f5c6b8451587e3970045a18e35c228ac3f77eb8d90b845208ac3f8003f5c6b82b0fc321677ebedc6b857228ac3f80038d70ae451587e0577eb8d708a2b0fc380e80038db2b8451587e057003f5c6c85c228ac2977ebedc6b8451587e2e80038d708a2b0fc5c057
  | 7, 0, 7 => 0x7eb8d70a4451587e298003f5708a2b0fc380e788bf5c6b8451587e35800001fae35c204ac3f6003f5c6b82c9587e1977eb8d708a3e9587e358003f5c6b84520cac3f7003f5c6b82b0fc3819788bf5c6b8451587e318003f5eee3451587e1670044dfae36ca28ac3f77eb8d7eb8451587e2e8003f5c6b8451587e097003f5c6b8451587e1f77eb8d90b8451587e198003f5c6b8451588a3f7
  | 7, 0, 8 => 0x1fae35c268ac3f67eb8d708a411587e298003f5c6b8450fc381677eb8d708a2b1247e0e87eb8d708a2b0fc52218003f5c6b8451587e0677eb8db2b852228ac3f87eb8d70a4451587e2e8003f5c6b8452087e1c7003f5f8e35c228ac3f700001fae35c290ac2f67ebedc6b8451588c3f87eb8d90b8451587e1c80038d70b4451587e0570038d708a2b1187e057003f5cae35c228ac3f7
  | 7, 0, 9 => 0x3f5c6b82b1147e1977eb8d70b452228ac3f8003f9fae35c228ac3f77eb8db2b845208ac3f800439fae35c228ac3f7003f5708a2b1247e0e789bf5dee35c228ac3f87eb8d708a411587e2e8003f5c6b857228ac29789bf5c6b845158983f87eb8d708a2b0fc52168003f5c6d95c228ac2977eb8d708a2b0fc52198003f5c6b8451585c2977eb8d708a3e1587e0e8003f5c68a2b0fc6a167
  | 7, 0, 10 => 0x3f5c6b84516cac2977eb8d90b8451f0ac3f8003f5c6b845158a83f700445fae3451587e1677eb8d70ae451587e168003f5c6b84515852207003f5c6b83e9588c3f7003f5708a2b0fc1c097003f5708a3e1587e0e77eb8db2b8451587e198003f5c6b8451589a3f77eb8d708a2b0fc5c1687eb8d708a2b0fc5c19800421fae35c228ac3f77eb8d708a2b0fc52238003f5c6b845158a03f7
  | 7, 0, 11 => 0x3f5c6ba5c228ac3f7003f5c6c85c228ac3f7003f5f6f75c228ac3f700001fab8451587e0e6003f5c68a2b0fc2c1377eb8d708a2b1187e1687eb8d70b4451587e19800001fae35c1587e1960044dfab8451587e0e77eb8d708e451587e2e883bf5dee35c228ac3f80044dfae35c1587e19783bf5c6b845158983f80045dfae35c228ac3f7003f5c6b85a228ac297003f5c6b8451588c297
  | 7, 0, 12 => 0x3f5c6b8451587e30700431fae35c1587e1970044dfae35c2287e1c7003f5dee35c1587e19783bf5c6c85c228ac3f8003f5c6b82b1307e1970041dfab8451587e0e7003f5c6b8451587e0377ebedc6b8451587e3880041dfae35c1587e19700001fae347a28ac3f6863f5c6b8451587e0e8003f5c6b8451587e2d70038d708a2b0fc6205700001fae35c2b88c3f67eb8d94b8451588c3f8
  | 7, 0, 13 => 0x7ebddc6b8451587e1687eb8d70a4451587e35889bf5c6b8451587e2e8003f5c6b8451587e007003f5708a2b0fc1c0c7003f5c6b8451587e2977eb8d70a4451587e3187eb8d90b8451587e0e800459fab845158983f70038d708a3e9587e05789bf5c6b8451587e29883bf5c6e15c228ac3f87ebbdc6c85c228ac3f87eb8d708a2b0fc5e1688b3f5c6b845158a83f8003f5eee35c1f4ac3f7
  | 7, 0, 14 => 0x7eb8d708a2b1307e2987eb8dc0b845158983f87eb8d708a411587e318003f5c6b8451586229783bf5c6b8451587e2987eb8d90c15c228ac3f8003f5c6b84519cac3f78b3f5c6c85c228ac3f8003f5c6b8451307e1c7003f5c6b8451587e2e7003f5c6c85c1587e19700001fae36ca28923f600459fab8451587e0e789bf5c6b857228ac3f8003f9fae35c2287e1c700001fab82b0fc320e6
  | 7, 0, 15 => 0x3f5cce35c228ac3f700001fab8450fc380e6003f5c6b845218ac3f700001fae35c0fc38196003f5c6b8451588c3f77eb8d708a2b0fc6a1687eb8d708a2b0fc6a19883bf5c6b857228ac3f87eb8d708a2b0fc6219883bf5c6d95c228ac3f8863f5c6b8451587e29889bf5c6b8451588c3f8863f5c6e05c228ac3f883bf5c6b8451587e2e87ebbdc6b8451587e2987ebbdc6e05c228ac3f8
  | 7, 1, 0 => 0x8b3f5c6d95c228ac3f8003f5c6b8451587e3d700001fae65c228ac3f6003f5c6d95c1587e197003f5c6c25c228ac3f7003f5c6b82b0fc5c19789bf5c6b8451587e2f8843f5c6b8451588c3f87eb8d90b8451587e2987ebadc6b84520cac3f8003f5c0b8451587e0e783bf5c6b85a228ac3f883bf5c6b8451588c3f8003f5c6b82b0fc52197003f5c6ba5c2287e1c7003f5c6c85c2287e1c7
  | 7, 1, 1 => 0x863f5d6e35c228ac3f800001fae368a28ac3f67ebadc6b8451589a3f800461fae35c228ac3f7003f5c6b8450fc5c1c7863f5c6b8451587e2f87eb8d90b8451588c3f87ebbdc6b8451587e2f87eb8d708a2b1307e2f8003f5c6b8521587e2f7003f5c6b85a1587e197003f5c6b82b1187e197003edc6b8451587e0577eb8d90b857228ac3f8003f5c6b8451587e0b77eb8d90b8451587e2e8
  | 7, 1, 2 => 0x7eb8d70b4451587e2987eb8d708a2b1187e29800001c6b84515852056003f5c6b845184ac3f783bf5c6b8451587e31800001faef5c228983f67eb8d90b8451587e2f8003f5c6d9451f4ac3f700001fae35c251145667ebedc6b852228ac3f8863f5eee35c228ac3f80038d70a4451587e057003f5c6b8451587e3877eb8d70ae451587e2987eb8db2b8451587e29889bf5c6b8451587e358
  | 7, 1, 3 => 0x88bf5c6b845158983f87eb8d708a3e958983f8003f5c6b82b0fc6219700001facb5c228ac3f67eb8d70b457228ac3f87ebedc6b8451587e19800411fae35c228ac3f700001fae35c2a8ac3f67ebddc6c85c228ac3f80038d708a2b0fc320577eb8d70b4451587e2e87ebbdc6b8451587e3180038d708a411587e0577ebadc6c85c228ac3f8003f5f6e35c228ac297003f5d6b8451587e0e7
  | 7, 1, 4 => 0x3f5c6b845204ac3f700001fa8a2b0fc2c0e67eb8d708a2b0fc38198003f5c6b845158522377ebddc6d95c228ac3f8003f5c6b8451585219700445fab8451587e0e700405fae35c228ac297003f5c68a2b1307e167003f5c6b845208ac297003f5c6b8451587e3477eb8db2b8451587e2f87eb8d70b4451588c3f80000224e35c228ac3f6003f5c6b82b0fc6a197003f5c6b852228ac297
  | 7, 1, 5 => 0x7eb8d708a41158923f87eb8d708a2b1187e31883bf5f6e35c228ac3f800441fae35c228ac3f77eb8d70a4451f0ac3f8003f5f6e35c228ac3f7003f5e0e35c228ac3f7003f5ccb8451587e2f77eb8d70ae451587e318
  | 8, 0, 0 => 0x7eb8d708a2b0fc5cefd71ae114561f8a5dfae3642e114561fb801fab8451587e0e6003f5c6b82b0fc32d0c7eb8d708a2b0fddfaef71ae114561fbbf5c6b845158983f783bf5c6b8451587ee007eb8d708a2b0fda26fd71ae114561fbbf5c6b8451587e1677eb8d708a2b0fc32efd71ae114822b0fdc00fd71ae1145614b3f5c6b852228ac3f7
  | 8, 0, 1 => 0xfd7db8d708a2b0fdc00e35c228ac3f02b3f5c6b8451587e3177eb8d70b4451587eefd71ae11456230fddfae35c2b914561fbbf5c6d95c228ac3f7
  | 9, 0, 0 => 0x1fae35c228ac3f6
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
  | 0, 0 => 0xfff00018f888001fc00001fff00000ffffffffc0000073bfdfdf00000e3118f88800003ffffffff000001fffffffc000007fc01fff
  | 0, 1 => 0x1f07f1ff007ffc03ffc003fffff00f8e000fff87803e00003fe00000070000007f8003838003e1e1e00000000e7077403ffc003ffe3f
  | 0, 2 => 0xe3fffe0118f8887c1fc7fc01fff1c0701fe007ff4701c07c001fe00000e00000787800000738001dd1ffff03118f8887c1fc0c401e22
  | 0, 3 => 0xffffffffff87fc739f87c3e01feffffffffff87fffc7c7ffc1e1e1fffffe3118808bfffff8c463e22e3f8fe0fff807ffffff8c463e22
  | 0, 4 => 0xfffff030007883ffe038c462000fcff0e3018f88383e3b80063e02e0f80e00188000739f80c061e221c0700300078800383800061e02
  | 0, 5 => 0x1c0000700000000038001c00000000000003fffffffc7ffe300e0e1ce1f7f0ffffff8ffffe3ffffffe3118f88bfffff80062000
  | 0, 6 => 0x1ce00070003ffc73863e22000001ce000000000007039c1c000000000e70070000000039c00000000000e7000000000703801dc
  | 0, 7 => 0x1cee70774000007380000000000000e700000000000000000000001c0000700000000000000000000000e000700000073b9c000
  | 0, 8 => 0xe000700000000001e00e3f8ffcfff877f8fe3ff3ffe01f1c0701fee77ff4001c073b9dffd0007f1cee77ffc0000073bfffff
  | 0, 9 => 0x7800000000000000000000000e00070000000000000000e00000f8780003800003e001c00e00000f800000000000381e1c
  | 0, 10 => 0xe3000e0f00000003838003e1e1e00e0e000e00070038380000000000e0e000f80000038380000000000e0e000e0007003800003e0000
  | 0, 11 => 0x1ce007800000000039de00000001c0007f0000000700001c0fffffe31f8f8fbfffff8c463e22e3f8fe0ffff87f8fe3f83ffe01f
  | 0, 12 => 0xe001ceff07740380073be000000000000e7000003838703e1fde000001c000070003800703e01c0000001cee77f740000000000000
  | 0, 13 => 0x1ce000700000007380000000e001ceff7f7403800703fdfc000e0e000ff7878000000039de0000000000007800000000039c000
  | 0, 14 => 0xe0e000000000038380000000000e001ceff07740000073b9c1dd000001ce007f000000073800000000001cee707740000073800000
  | 0, 15 => 0x1c00007000000000000000000000000000000383873bfdfdf00e0e1ce00000003838003e1e1e00e0e1ceff077403838003fc000
  | 1, 0 => 0x1c070000000000701c000001e001c0701c0000700700007c0000001c0001f0000700700007c000000000000000078000000000000000
  | 1, 1 => 0xe70000701c07c381ffc1c0001f0e00070000000038001c1f0701ff007f80701c07c001fe01c0701f0000000701c000000000
  | 1, 2 => 0x1c0001f0e700000000073b9dfdd00000000e778700000073b9c1dd00000000e70070000000039c000000001ce000000000000039c01c
  | 1, 3 => 0x1c0701f0007f80701c073b9dfdd1c070000e07870700007fb9c1dd1c0001fee70000701c07f801fe01c0001fee07870700007fb9c1dd
  | 1, 4 => 0xe0e000f878780000000001e0000000000000000701c07fb9dffd1c0701fe007f80701c07fb9c1dd1c0701cee70774701c00039c000
  | 1, 5 => 0x1ce000000739f87c3e1ffe1ce7e1f0000000739f8703801dc1ce001f0f80000701c07c001fe01c0001f0e00770738007c3e0000
  | 1, 6 => 0xe0f800000000038000380000000e007fe00007fff80003800000001c0701fee77ff40383873bfdfdf000001cee707740000073800000
  | 1, 7 => 0xe0f80e00ff8073800038038001ce0000e0000000383e03803fe000fffffe31fff88bfffc7ffffe1e1e3f8fe0fff807f83e03803fe000
  | 1, 8 => 0xe0f80fce00000383e03803fe01ce0f801c000070383e00003e001ce0000fce00070380003f3b9c1dde0000fce00000383e03f03fe1c0
  | 1, 9 => 0xe0000e000000038000380000000e0000e000000038000380000000e0000e0000000383e03803ffe00e0000e0000780383e03f3bfe1dd
  | 1, 10 => 0xe0f8ee0000000383e3b803fe01ce0f8e00000780383e380039c01ce0f80e00fff80383e03803fe01ce0f80e00ff80038000380001e00
  | 1, 11 => 0xfcff0ff0000003f3e03fc3fe000fce00ff0f87803f0003fc39c1c0e0f80fceff877780003f00001c0e0f8ee00fff87b83e3b803fe000
  | 1, 12 => 0xff000fffe70003fc003ffc001c0ff000fffe00073fffffffc63e22ff000fff000003fc00380000000ff0001ce000003f3fc3fc3fffe0
  | 1, 13 => 0xffe0effff8787bff8387c001e00ffe0e1cee00073fc003ffc01e00ff000fffe70777fc003ffc00000ff000e00e70003fc0000038001c
  | 1, 14 => 0xff070fff007f83fc1c3ffc00000ff070fff000703fc1c000001e00ff000fff007803fc003ffc001c0ff000fff000003fc003ffc00000
  | 1, 15 => 0xfffffe00188003fffffffc1e1e1fffff000000003ffe03ffffe1ddfff80fffff8003ffe007c000000fff801cee70003fc003fff9c1dd
  | 2, 0 => 0xfffff1cee70777ffffc73800000fffff000e70003ffffc700001c0fffff000e00073ffffc00000000fffffe3118f88bfffff8c400000
  | 2, 1 => 0xfffff000000003ffffc00000000fffff1cee70777ffffc003e1e1efffff000007803ffffc00000000fffff000000003ffffc00001e00
  | 2, 2 => 0xffffffffe70777fffffffc00000fffffe00000003fffff80000000fffffe00ff8003fffff80000000fffff1f0007f83ffffc7c000000
  | 2, 3 => 0x3fffffffffe000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x56400008d080000dc0000135500000ef77bbbb800001b5decece00000c3118b0880000195d48a4e0000005329bbb80000014c00a4e
  | 0, 1 => 0x5037108004d5401fdc002b77f5007e6000addbd001f00002b64a00057400029df9001898002a165400293000a50f5401f9c00233431
  | 0, 2 => 0x42d6c40118d0883c0fc56c01b5f0d03715a006d74300d054001b440a02e0530069781404c5280035d0a56c01108f088280b004401802
  | 0, 3 => 0xf7bdbfafd786ef5ad6b68f461bab53d3bac8786c6d4746eb01e1a1d2948c2110808a415920802342063a8b60fd6006d2a0b104441802
  | 0, 4 => 0xdad6c83008f0836b5230c462c22d8d64c3018f0836b5b30c463c22d0d40c201890836b5b30c463c229856483008f0812b0b104461c02
  | 0, 5 => 0x40101c0210f100080810b8025c00000040200913ff7f7ef47fda36fcbd79d1f760feffbf8ff7bc3bdad6cc3118f08b6b5b308063420
  | 0, 6 => 0x250103ce630f3095590f392b428250003ce42002090a40f139c3c4202822c6e70b7080a00b1b9c08820280284e702001084870b843dc
  | 0, 7 => 0x252933cee70f7494a4cf3b181192529338ce7064494a4ce3318111252931c8a50f5494a4c622941912529314ae40d7494a00f3b9c088
  | 0, 8 => 0x602042e8197021090140a1e4467a9b7cff70f7d9ea2df3f5801b2d2b73dee76f7495fdcf3bbf7fd252b73cee74f7494a4cf3bbe7fd
  | 0, 9 => 0x4ac2c4537879392b02114de0c0a4aa0a453f029792a02114d4080a48e24450f879110380910be065c40e00400f810002189814ba1e5c
  | 0, 10 => 0x6b80865f5220292b8b914fe1e5e4ae2e453f069792b8b914f4181a4ae2e400f850412b8b8002a14104ae2e042e049712b82114fe0c0a
  | 0, 11 => 0x2d4243de6a7930a1a90b53bdec40c4341d0297f103004074084bc4daf6ec73f8f9fb6b5b31cd63c2a6beaf65ffe797daea2d97f5881b
  | 0, 12 => 0x65e937ceff1f7597801f3be840860a80684f702013b8f974fe5fde4e8185d3712f3913841703e47c42d6b73deef7f74b5adc42211111
  | 0, 13 => 0x6f8187df732f39be021f7d4880a6deb77deff7f75b3ad1f53fdfc46aeae6d7ff7b79abab1b5ffdece6ac2c6d77b7b39aaa21b5fdc88a
  | 0, 14 => 0x6febf78cd64445bfafc622b55916fe9b7dfff3f7dbfa6df7ffcfdf6fc3c7df7b7f39bf021f7decc8a6fa9b7dff72f7dbea6df7f5891b
  | 0, 15 => 0x945509e0299f9241502380a66e4905408a0299281bfafdf7ffdfdf6febf7dfd6646dbfafdf7ff9f5f6febf7ceff5f75bfafde33fd591
  | 1, 0 => 0x9c5749a0004402715d0540a1f449c5741c0214f12715027c0a6ca09c0109f0212f12700027c000800985648f029fb92615023c0a6ca0
  | 1, 1 => 0xb07c0aa4ef928271dda7cba7ffc9c2029f2e0297241d0a38ba66fc9f57c9fb29ffba715d27c0a7fe49c5749f0006402715d2680a75a0
  | 1, 2 => 0xbc280bf4e72202f5fdeffbbfffdb87e6af6effbf2d5f4efbbbe7fdb57d3beeef9ff6d5f4eeb3be5b1b5000bee420022c1f0ab9bbe6fc
  | 1, 3 => 0xbd7f79faedfff6f5fdcf7bbdfddbd7f715aec7d76f5f4effbbeffdbd7c0bfeefb2a2f55d2ff9affecbd626bfeea7972f4a4effb9cbdd
  | 1, 4 => 0xdaf6ecf3f9fbfb6b5b33cde7eeedad48cf379b2aaf5fdeffbbfffdbd7f7bfeeffff6f5fdeffb9dbddbd7f7beeefdff6f5fdeeb3bf5b1
  | 1, 5 => 0xff808fff52202b7bdfb7cfe7ffedef7edf3d0646b7bdf870b853dcdef48df3f9b2ab7b5f37cde7feedea1adf3f12f7b738037c3e0c00
  | 1, 6 => 0xf0fc0400d40003c3503a91ee4a0f0837ea4524d57c2003a9148000ffffffffffffffffffffffffffffffdbfffffbfffff523ffdeecaa
  | 1, 7 => 0xf0fc2ee6ff9bf3c280bb9bc825cf0800ee6520023c3f03b93fe6e4fafeceb5fff28bd7f47eb3fe5a1f3fcbeafff92efc3f03a93fe4a0
  | 1, 8 => 0xf5fd3feed60467d7f4ffbbfe7fdf5fd39e8ad9fd7d7f4d52bf075df5d50fee7b9fb3d6a4ffbbdc3ddf5800fee520023d3f43f93fe7e4
  | 1, 9 => 0xfad6cef77bf2abeb523bddeeeeefad48ef77bb2abea023bddccacefa808ef752202be3f93bd3ffee4f8c24ef47a7913d7f4ffbbfe7fd
  | 1, 10 => 0xfafeeef7d6606bebfbbb9bff6fcfafee8f0adfbd3ebfb8b1b9d2dcfafecef7fffbbbebf2bbdffeefefafc8ef7ffb2abeb5b3bddefeee
  | 1, 11 => 0xfcff4ff4d66403f3f03fd3feca0fce24ff4fa7913f2a43fd3dcbc4fffdbfffffbffffa063fddccbcefafeeef7fffbfbebfbbbdfffcba
  | 1, 12 => 0xffa88ffff7222bfe063ffdccbceffa0affff2297bff5b3ffd6bc2aff808fff52202bfe023eb148000ff8083ce420023f3fd3fd3fffe4
  | 1, 13 => 0xffe2effffa797bff8ba7e2a1e54ffe2e3cee24973ff0b3ffde9e4effa9bffff72f7ffea6ffffdc99bffa9bfacf70647fea6d56fd0b5f
  | 1, 14 => 0xffd7cfff7bffbbff5f3ffdefdaaffd7cfff736f3bff5f156de1f4effd6cfff7bfbbbff563ffdeefeeffd48fff7bbbbbff523ffdeecaa
  | 1, 15 => 0xfffffd289cd4c7ffffeeb21f1b1fffff108844447fff6fffffeffffffc8fffffb2abfff227e2b6ca0fffc83cee70223fff6fffffefff
  | 2, 0 => 0xfffff3cee74f77ffffcf3b19119fffff38ce74647ffffc722953d5fffff14ae44d77ffffc52291355fffffd399cf4cffffff4e651913
  | 2, 1 => 0xfffff9f8adf6c7ffffe6a2b75b1fffff7dff76f7fffffd56ff1f5ffffff55bfc7d7fffffd56fd1b5ffffff55bd4646fffffc562b1f55
  | 2, 2 => 0xfffffffff76f7fffffffff5991bfffffffffff6efffffffbb59119ffffffacffd6c7fffffeb359111fffff9f8adffd7ffffe7e211911
  | 2, 3 => 0x3ffffffffffdbb
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 54 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 54 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 281 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 281 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 281 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 281 then wireAt i else 0
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
  | 3 => 2
  | 4 => 31
  | 5 => 360
  | 6 => 1420
  | 7 => 491
  | 8 => 4
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0x17c069f300812e2a
  | 4, 0 => 0xf962e301de80acecd5b7ea4bd4c83b2eb7e37f3bb797e2b5ab2d2d9ba69a2826a63faf799eed6dd19e6095d4992586dc8878a46884f1cc947444ded67166856d68391bfd669a96f8612ca955576404914ea7504047fcb4ab47f80e3d43f096c242d25ae12ce952b12bbf1bc42334d4bd1f9f07d41af861c5067fcdf0
  | 5, 0 => 0x1aedcb0e1a13e99e198d52e51900d8b019009fff18c37efc188da69318611f4a182539bf17af69001753c8b3173324b9170d086f167df75e167ababa1643e44816052fbe1467f41e1415238713ce3e0012cc1c55123f979f1178edc9100eb51c0fe749af0fce77530fb8ab870faa77070f564f730ee0af2a0e7545940e68d89d0d9e19500d0b45210c69bfd00bb0c3ae0b551fb20b4fd1000a9b49120a75789c0a41d8c40955e878091a132f08c9b557084bb82d081581cc07d14b02074cee0b0705106d06f72c6106f6ea190685d42405ab788a0541786f048e73920414a3550242b79702204f5101373cfc01204fab01013f3600c217600044916d00272583
  | 5, 1 => 0x38becf7838b8c00e38796b4a38355351382d00c137edc5f637b9fc1b377ab9dd3602739135e7ff7635e0004135c6e9dd35a96a46356728f6355e7c6435554bd235099e5634f0851b34d31931335802fd317a69f630ef49ec2f5496f02e84d2cd2c188cc22bac62dc2b06dce52a7f696e2a3198e0298d50c22873acb2281a6a4328100528280064ef2792ba652705880d26befc4026778b40264c4816263b036f261bbf192616581725f712e92502bb72249bda202259f2bc217c18ce20bd424e203f350c2032aaa51f426e131f010a401ef254801ed32ef81e06e3f41db72cc41d1c780a1cd7515e1c781cf41c77fee51c42cc501babfac91b6505171b5300e4
  | 5, 2 => 0x5dfff3c65de2c9845dca4c075cf53b155c8966155b0622f65aa68a955aa3317b59f60be059dd50c859a0445d594f2cfb5931c11159183b0e58f528b7574085e6573ce74e5705008c56811f7b567d130c55c7af29550de69c54ea989354763999545a40c85318541d51beb952516e3a2c501d2ed74ff0673c4e1eb31a4d288b0d4c85ff684bb9e57a4ae0bcd24ac0847c49fd469d49129c2f47c3a6924614d99b45e92e5b45e61f6645d91ef1446950e243bb1b0b42d61d4c42b779a342590cb54189b8df40c1743d40a6c27d405f52873fe776d33fc4defb3c9d75a23ac6f5f63a9646163a6c991439d021a739b9720e39ab184e39a98e67399a9e2c38ced832
  | 5, 3 => 0x82b1a35d81d7f28c81c1d1c6808447277f52e5657ef470087e88360d7e7152747e406bf97e34a38b7da6b7ed7cf270267cf2005b7cf06b427c3bc47e7bb7eb767b9c99747b2b17a17ab83fb27924126d78f1ec467829da4177f496d177919af776c461dd7680fac4765f705774de7ab071b7b3637123e9af70aa281c70159663701144db6fd086ad6f8795176f03e74a6f00fbc36efba8276ef136416e197bc66db2c6976bd6b7e36ba4e9d06ad764e76aa8731b6a0b9dbd69f6eb0d6907ea936834f5c568152eb667de5e2e66b3495666276d0265d4792464f38968643988c963669d9562bd28d8629d670561fa3a1e618a6a105f9defbf5f772fc05e9b3ccc
  | 5, 4 => 0xb7a1fd24b6626367b63eeb70b4bc74ebb47c9722b3eca227b3bdf196b3b200cdb2f8b09db0d3c397b08b963db03d009faf901e29ac377ad1ac1a3caea9b2f2cea993afaca97f199aa9467246a93194efa8a9dbf0a8112672a467ebffa2ac5bd1a275f6c8a24f2000a1bf8b22a1093cb4a02420769cc122649ca06a5f9b3436919a6abdfc99ac50f59947bb24989a692796db332596a5cba59591f3be94f2295694a1c978927512f791d0070991c6b2ff91a9b82e9190d39c911cd0ad9094fad8906b39fd8d9ceb9f8c76bee98c322f5d8be0f6dc8ae7aeb089d3e9738932e91c87d430d387258838868b3a3f85c2d59885ac709184f9389d847e27788319ef28
  | 5, 5 => 0xf89a03eff7fa745bf6dfb90bf3654be1f1cb9cbdeea30769e9683f34e7430d79df145ecfded43b94dc730934d73f8adad376d5e9d1293c1cd0d1efe9d0680223cf4c7316ce7d2689cda4477ecd73df73cc6652b0cbfced30c9f5c996c99d9a0bc7eab85ac72f343dc6a07237c65a4764c5821593c3014cc9c1bcb379c16ba852bf540344be469854bd63ad0fbd536e3abbec3344bb5bf358b8745914b7f60488
  | 6, 0 => 0x7a676fd078c60020737882a0720ca0a0715437d06c4413d06b5fac6068a399a06457cb90638a75e060f596e05e77d7105ccd23505c61dd605a509e60575e13b05687e89055afcf4054d1e1505169eb004d32ad804c021da04890ef504572614042d77d503f1b95203cf5e0b03abb2f00375c6cf03476202033b05b503087e0402e9d44b02e8a90d02dd1e5f02c16857029aef9e028da25d0254d8c40248132d02470b1b024365d60225f9ec02102cb901f5db9e01b2c4c601a6e4da019cbfce0198403d01652a32014fcec7012a58400129b755010ac53101013f3600f5a3d200eff69600e52646007dbb7a006fb9d3003e83f9003b1ab4002e9cb3002df207
  | 6, 1 => 0xe737a980e67dc250e4b46950e0550e70dfb96ef0df70cce0ddd4aa00da46fb90d9cbe430d9a92370d92daa50d82e74d0d5098740d2d22890d2aded90d0b45210cfc43180cf439bf0cdc56be0cd896110cba81470cabde0a0ca165b80c97cf590c8c4ccf0c7bcab90c59d4660c3c687c0c2c14070c269c8b0bbb8e270ba77e000b88cc090b50e2ee0b1a7d630b0896c40afb5dd30ae34fac0ac4d5b90ab8b2690ab6224b0aa769cf0aa0caca0aa03d900a6572fc0a6426b20a5ed5a50a4bf36d0a01f69909fb12fd09f7ca3e09bdf0a009bd51ef09695d40093e7356092be94c0903dbc50901863008d6f026084aafc7083843fe080a8eb707fab1ba07f1b6d6
  | 6, 2 => 0x13967e2f139302bf1377feae1375dc6513728f56136d10ac133c08ef132f4ac71317dd2b12c3605312baa67712ae5da31233466a12324797121b112311af78a8119b91ab118d0e1d1187183a116b47241161181a115b67ca115a79671142fa4111408e9a1137d80a1120d646110f8d8e1103719910d89c4810c5277710b7c9a8108ef5b91087cb5e107b5734105861cc104ef361102d648a101f34a2100eb51c0ff651070ff073950fde41e30faa77070fa2a5570f8899180f8898390f8009980f78ea770f76f4eb0f6b9a140f56ffe60f3d84400f1c66040ee7b93a0ee672b50ee5d4340ee0af2a0edf18670ed86b730ecc811e0ea800b80e8414b20e7e1513
  | 6, 3 => 0x1aaa51371a87fcc01a6b63331a58a2341a548add1a4b36dd1a4058c31a1f1cf01a04d97919b97173194727b519468cb7192a0dd61923eb0b1921f28d1921237f18ef4baf18eed24c18eabeb418e3fb0a189d69961892cd85188349881882b169187cdaee18787ffd1870ade6186366e3185955ec1839cef017e170dd17aeb250175a929b173536501729918f1712096e16afa02816a82ea1168bc85d1673385e1611817416100cbf1606144c15f71c1b15f022ce15e9498b158c470e157b3ef615776f951574b12d1561a43a15602014155cba4e1535fac81528c49c14db18b514a3cc181486a38f1415063f1413d60813fdbe2913e90d2b13dbc3bf139b02df
  | 6, 4 => 0x23aa74da233e519822f578d322d85c9a22c73513229eb02f226346d522521a04221f487121d8db472194ff3b219016092177d4282145ca59213bddeb20e249a720a84c14209b7f302089ff202064873a205cc8cb205b0a2a203ca2472014c6441fd3d3851fb72b911fa45a3f1fa432931f8f063d1f8738591f0286b71efda3231ee15f4e1eae27731e08e1531e0576261dff4d111df468421dccfa121db4e0681da019151d9945271d85cfcc1d826c881d825b1b1d73f5661d5bd8171d55e79b1d4a9d981ca0b1831c9fd8f01c8d62a61c5d3d531c35b2841c32bad41bdb5b301bb1776b1b9386ad1b8548e61b62a5db1b55df541b3c1cc21b1a2ca91ac6cf55
  | 6, 5 => 0x2a1d57d02a14d0f72a1317a02a023a7d2a00355d29dcd53d29c478db29740e862971ba40296b38aa296669a2292576e32920d8b3291385ac28d3f68428bc54b328b13185289a985c285f1665285a6120284836062844d63928367c31282a58e7281a4d9f28191047281909f627a497ea275b976e275958f22752ae752707a0fd2705880d26d0c80326bb2fef26b886cd2678686326640762265363bb262a32f4260932412604931525eb7b52259a3137254b6a5725494af525471fea253ef9ad250aba5724fedf5924f27cee24dc268124b2b20a245fcad92443fd30244232e6243e50102437f8a9241b265d2416c07e241577b924140a4123f07cfd23bb3be3
  | 6, 6 => 0x3177ea8831752de731660f0b3157bf6e3122199e311dfd6a30d5282030be0b3130b9d1dd30b973d630ad71ad30a5e218309c65f33063306830631eec3006014230010ce22fdcbf742fcfbe272fc6445a2fbf5da52fb10f502f954dd02f7e6ae62f7a8db12f6745e12f643cf62f3294542f20329b2f15a0e52ee716dc2ec68d272ebd3d6c2eba05a82e45ee3b2df877932da94f942d9165262d88ef402d7d41f82d3ff5e92d3ea4312d06d0c22cf8cd042cf085992cd4b9eb2c7dc05e2c3e81882c2937292c1a29112be8c6dd2baf6f8f2b08f8cc2afda44c2acd7a982ac41d2c2a8e42722a8c0ae32a892cd02a76b7d12a5335872a42cf9a2a3198e02a222ab3
  | 6, 7 => 0x37d8b58137d59bc637d4a1c237c3b2cc37b9fc1b37ad2a94379db3ff379a618237997d53378f31e83766c85037444b1836de7a8736cd76be3679dd0b3678c0eb366fa27236648703361d50e73619ea8d360d07b93601d284359e21163597402035787e263536fd9035239d6d35099e5634f524f934ceb8d134c589ee3492603134886bc33481847a347c735e3474fb8034578f963451cc6e344f47aa344da139343a84db341c017333ce134333c3d979339be8303389f6ab33864f1f3380f3e4337f0a0633422da5332a02773327d92c32e16b8932b963233294f0e0326bf53f325f2c64324765313228b423320f9fd331f5eab331c8566831b1ab2931ae2c17
  | 6, 8 => 0x40a60e3740936de1408a06cf4062ec42400945b43fed8a9b3fd11fd73fca2bf63f732d3d3f39b76f3f384bf13f227ddf3f147cd73ef9b7083eb6cf343e402f123e38a55b3e277fff3e247c763e0d36b93dce4f973dbce7733d9f76143d820b7b3d7dc3333d1f3f593d03aadf3d0124c93cfaa5163cedcf813ce437ac3cc696da3cb64d0f3c9d75a23c3970963c0ce04f3bf4ea113b8aa58d3b34c0e23af9666f3ae826bb3acf9b4b3aca75eb3abe07193a73bcfc3a5b11913a4b4a0439e99ade39e16a4739de4fb639bb3ded3993975b3989122439731d65396f572d3965a154392d295a38eb527838da452b38c8629238c1057038838ab138695c3f38422411
  | 6, 9 => 0x49469c9d493b17444931ec38491e4f544910933d4901a2e2483393994824b16847d7f35a47953816476def3e4760868246fc866846da3c7446bdac8746b55adf46a6e54b4694616246610b58462f96b7462000d245f126ed45d91ef145913ff4458338fd457c8acd457a615d456daacd4563ccbf455be5b5451ed6694519cf8c45179a8f450651ef44f4548e44c79b8a44b8f92b44ae84d944978530448eda3a447ee81e43f5039043df5823435ea17843555fb0433f660a42eda89a42c90b1142bebde742b779a342b451b04291ffc9425327d74250d60941a0c128418c58194183d887417adc044176fcae4170bcbe413f306a411103a140c11d8e40a83783
  | 6, 10 => 0x510a33e250e499dd50b80df7505beeb35059633d503999f0501f9e51500139404fc71f074fa753334f9d2f8d4f9d1e774f8c57c24f86a4154f7141a24f54e6cc4f29237a4f135c524ecc8e064ea43e9e4e9d19034e6d16534e1717654dd3ad484dc9c7c04dc2d7694d6c43d14d43a2314d2f3d364cfd734b4ca859dc4c7463374c6821664c4c79c44c388e2d4c1326ad4c0e70f24beb8c424bd7ce484bc5e4304b6e21e64b51d8934b2e44754b236a724b226b904b21fba14b0d87ba4b03fc924aee73794aca3bcf4ac953704ac64d7b4aa02b774a932f4e4a0173104a0125c049e579ed49e3bfbd49e0f04f49d9a14a498effba496fc9e4496885e549585913
  | 6, 11 => 0x582969ea5817540b57d21cf857ab48c1576c925c576751eb5702a7c257005c3e56f411bd56e6f7eb56d29d1756ccc280568ff7f1567d130c567c7f515659605e56427f92561504715612b12055f6748055f5a32a55eeb91a55bf057b55a0239d5582b7b355739b7c5567a8505548eb3e5530a86c54f251df54f0504c54ba411f54a9557c54a16d3c5479ade654583324542767885416d04b53e591e853e2c57853cd1deb537b088b53514afd534934bd533fb48d532df2e153181bf85314eaf652e71d0152e2321e52943af55281620b524844685247743851ee61ea51ed228251e9127651cf671751bb2a0f516a823f512f7572512a0a4a512495015121a07a
  | 6, 12 => 0x61ad365a61874d906169ffad61444ca2613f4bb660f47f6c60c0e6cc60b58bf560a44355609eba3e60723ebc60638fc460617b6c60205a025fd7d1ae5fce787b5fbac6fd5f9a0e3f5f938bea5f871fd25f4ce3e85f416ceb5f35ba935ed985675ec2fe405ebac33b5eb5ede35e75f8765e5e95475dedb7c05dbe740c5db456ee5da6d4765d0eae245cde0cce5ccd4b075cb55e505c8966155c3f74815c1f443a5bf13ab45ba3354b5b8e88025b6fefcf5b6b6fdf5b4dbe2c5b3eec9d5b1f7a795af98e345aa2af7a5a9f5dfd5a5a68e35a3ecee159e9114a59b8610d59b3a0595944bdd6593f5843591e47e65901034658bb531a58a9df505875705b583d5a59
  | 6, 13 => 0x6b37a4776b2262386b1be3666afac8926ae97d196ae6f02c6a8f01346a610cd96a2ef61d6a13619069edc244699f003a69148b686909685e68ade545688d1b5568742b926825e351680dfb0f67a3bf0d67963791677701556776f078676198836725e9c5671ea51e66d1c7a966c97e4e66a873e6669a4886666aceee66596eea665174db663e596f6627df6e661f8dfe65ee6d3a65a82696655de01765524fc665381a0264f3896864c8c42e64aa6b4464a0c73f64789948646b996f644d72e6642e54a063fb6a7f63e431ee63a63bbf6386d6c463669d95635c10ae630aea4562da87e162b9932262623a35624ac82b62356cc06226b9cb61f427ee61ca4008
  | 6, 14 => 0x76f0de3376ef06c676d6e32176d00d2c7605fbc075b5252b75734564756ef7e9756948e674d2ee7874c5ce3d7495e96f744813417433e09b73bcfd3f739a2d4a734eaa0d732a242c731d0cce72ff2f9d72b2833972b1ed0171ff734971f3b43571ec93a571d8f93471d3d74b71b731cf71a26241719f8882718aa31d7180f6877179360f70e9cc8f70d8df6c70d6da32702d9a19701419896f9a15cd6f7090bd6f4ebd9a6f16ebf36ea4ed216e97376a6df7e42c6dbfabf96d9445326d8815996d79ee906d76e7956d71e5326d545ce36d1a240c6d0c81136cfb7a1c6cf9e7a76cd6ca796cbe1d396c80742d6c49cc986bd670bc6ba0f1c86b70d1e96b4493be
  | 6, 15 => 0x817106db816ee3858101e0aa809fa26d808528c4805c90738040d078800c7ccf800bb67b7fc048557fbacdd57f82bf8b7f7c17707f4590c97f3d62797f1a1c937f0fc1c87f00ecae7ef20d5d7ed513f37ec8813d7e912cbc7e41f46b7e2488817e1a8a567e16e3887e05acff7dc594b27db1e1917db173387d1b507d7cfde4937cf889057cea112d7c4faf817c2c69b37bf8b5337ba594057ba3c0797b75c3147ad3415f7a9933267a8ef3507a67caff7a1283817a05242f7a01223179e5550479d3e13a797004af79684f62795acc8c791e9fb7791c12547915ad7b78c9173878bb1eaa78a46f127847c1c27819d38577d135d07753784a7730263a771fe424
  | 6, 16 => 0x8c73f3678c670cfd8c5b2b6f8c5291f68c3dbf858c1415108bf8e0e98bddfc858bd322518b7e195e8b4b712b8b31c58e8af097cd8aef77aa8ab84b5d8aa45d458aa3b04f8a7994f88a51c9de8a516cc38a4c27bb8a4b2c568a37c65d8a293c538a0d8ef789cd068489b9a4c58931d08d8931902088fe5bb888f4b3ca88a82a5488637cc7884052b78826fc3987e13aa087c7d7888759f0be874f92698703169686ef90bf86be95e9862d7dc285fa1a2f85ef75c68527bd3a84d0ea0984af188b84a4c2e6848fc39c84520cd584064fcd83ea69c583d7542a83a21eb18362909783328cfd82de711782768228827639728267361782142fcd81ad224981829889
  | 6, 17 => 0x9b4d17b59b18954a9ab78fed99f42d7f99d8cbd499bbf50899a181bf9997d904997632ef994e0ce69933b443992721c299004fbf986d00ac982c402a97aa9cac97a75f8e97a4f387977488ac96bea8b196bae4c8969aeb7295b3875295872ae694aba5ca9499c431947da14a947012d3941d35b893f38d2a937619ce93342c279322c34692cd311e928df768927fc7e79278f665924b56d491c9a379919f9a92919ac8ae9161e4a791592acd9133fdb49112800b90f68a7190e225fa9066fa26905e4b308ff6aa358fd08d408fa19e1f8f7301af8f1f96978efad5908ebf00228e183e158dd9f0ab8dce939b8dc4f0798d9b3a468d2f53818cfa91f68cad401e
  | 6, 18 => 0xa6aa7b4ba6a209e6a63c52c1a6353a8ca602287da5d42f5ba5d3bbe5a59b5408a54844d2a513133da5103ec2a4a20be6a49c2d6fa4943c01a477d6c5a3e65ce5a3d87e06a3744415a2cd8bc3a2487bd3a22b6a16a1e5f75fa1ded325a18bd668a181a08ea16c4690a16ae806a0fec4d5a0f696e5a0c27a1ca0bf0646a070683ea05ab451a0569a1ba04397cd9fce48649fb4bcba9f9ea33e9f9298bf9f77feb79f3584529f0c76639e4370ac9e3c45669e14ab229ddfb7989daae7359d42c3eb9d2f099b9cec5eb39ce1a3729cccd4969cbb54e09c8160609c7381819c70cc409c1ef4619bff60119bfb29749bf3d47a9be3accb9bc6e6ac9bb9bd659b8d299c
  | 6, 19 => 0xb541bdfab4d0d4a4b4bad623b4b7aa29b47be621b3e7728fb3c1e194b3120380b2f32daab2d40c22b272d876b1f9e3e0b1ce22c6b1c67554b1b8a042b1b89675b1aab58bb110e951b0d3c397b0c88900b0a47233b09b89e2b04d71d7b0433de6b03d009fb02f596cafd75c9cafaab267af6b3d75af448f52aeff15d3aef128d3aeefd66faebe772fae6822efae61e220ad58a5d0ad34d12aacf45b22acb5a4bdac54c35bac1d3e4eabdd680fabd597ceab3f45e1aabfa2cbaa00aaa3a9d57912a98e4816a97e6899a977e211a8f6772ea8e78fc4a8cb32a4a8a73885a85b062fa822b426a7e1ec9aa7dd5251a7b5ef13a7a2a7a3a73b62e2a732a1a6a6e98352
  | 6, 20 => 0xccca3424cc994278cbdbb155cbaeeccfcba82e50cb3988b3cad25745c9fcc544c9f99698c996b3b6c9363a22c92a9c24c8e3e5cfc871b992c74c4e87c73369bbc6bef9f1c63e6ab8c637c9f1c6379303c59d6c30c5821593c4a4bbb4c40a2416c391afb2c364e4f4c35be029c285e459c2472df4c0c2be92c02e5d34bec0a575be4be64fbdfb5dd0bdc979a2bd5fbcfebcc8e334bc87e6edbc5b9c36bbcc115cbb28b1adbb11473fbad4da24baa65613ba701036ba5b88ccba423037b9fe2647b9aa6055b8c9f8fbb871b7fdb84d5911b8405c07b7a1fd24b751bcc3b72f93ffb72e368bb71329c5b6d0eb5cb666254db5f8c400b5e82352b5b29b6bb58ba30b
  | 6, 21 => 0xf171c893f117a0a5f03d9387ef0d263aeedf9f01ed37c018ec497f1deb6f4652eabbbb9de863d8b7e7a21dd1e63c9710e4f751b8e41c8ef3e3ecf174e3e18a9be3cc7821e383dba9e2fa15d8e254a19ee126cb02e1151f08e0ed4344e05c847cdfbea839dfb2a488dee6275bde4eb049ddad0ebedd4a9b86dbe35b38d9719f58d96035f2d937fb5cd89de169d87f9952d7168563d6de8f0bd6b7f5e6d630e845d615987fd5dffed2d5735722d568ff65d528804dd3e37591d3980975d3661707d30f653ad2d1a5eed27af234d21f33e1d1293c1cd0c08da1d0a6a70fd07c82add07186c8cfaaeb5dcda6e723cd9b22c9cd853652cd73df73ccf24bcbccd3cdb7
  | 6, 22 => 0xff88f5fdfe69481bfb379514fb17c36ff908e400f6f16d4af6535463f5e5463cf33b5fd0f32a1730f2854adff265e2cd
  | 7, 0 => 0x1232479711ed84b711d7480611b4128d1187183a11761aa81142fa411134c9340fd4c3f50fc22fb60f8b2a5f0f5c5cfb0f3badb20ea68d810e8414b20e783ebe0df078900db675560d9a92370cf91d9f0cea20e10cc7aa850c867e660c167f100bb2ffb10b989d440b41c7720ab7b9ae0ab0afbb0a9628be0a71f9560a172c4908d6f0260878675807d82e3c07bd347d075140fd06ecbabd06634425065223ce064612c7061ab28605c61dd6059e8b170590310f05169eb004d0acec040745c603e36454036df150033b05b5033a727c02e9d44b02d5abde0296f579024a740d023c952e0198251c0188fb4b0129b75501283a1700dd496a0064991500103def
  | 7, 1 => 0x24cb7b2923fe6fae233e51982325e28c231857ea22543c1c22521a042064873a204aaf2d203e530f203cd04e2015ae6f1fb72b911f9bef851f608b651f3d31db1ee4e3db1ebb13731eb3facb1e8eec381e7359ed1e17d8601e08e1531d73f5661ca0b1831c53b96d1bde45011b70b1901b325a461b2d157f1b1036f41a5d39541a45ab1d1a4058c31a2bfa9c1a0ece7019f08aad19e3604919deb3e2196672e1192a0dd6191531f41900f42918e3fb0a18787ffd1729918f16a82ea11662ea0a1606144c15ff8a4715f86a801581f8c81561a43a1528ba3c14121a0c136d10ac135211a2131bfefa12baa67712b8ab4112ae5da3129997eb12798028124e2635
  | 7, 2 => 0x3a8b1a653a305add39de879e38ad846e37a1ed1c379a6182378f31e8375fd1e83724f45b36f4981f36ad51603678c0eb363c57f4361b1af435d89aaa357bcd57355e29ce3518dab134744a7f342cdee933d93c6b33ab0d0833193e9a32e7627a326a0621319b3e42315024ba31381b0730f26f092fbf18df2fa1c82a2eedfa852edbd6b52e9e70832e46479b2d770a592d014b912cf085992ca821632c9946a22ba0a43a2ba064522b48380c2a7c85282a6bdfc02a5e00e12a5175e4291abe562882e2b2284db2db2838c79a2775450f2752ae752727707326e36c2426aa53c326a4b5bf265363bb264ea12126488ebe262d41fb25eb7b5225bece64258a6ea4
  | 7, 3 => 0x4e00c0ea4de27c5e4de254b54dd111674d2b306b4cd8ba054c4c79c44c173de94bf147df4bb13b214b62f61f4aee73794a0d197449d602e8499cfa0a49148db048f0bd7d48ebd2aa484e6acf47f69d26475141bb46e1bded46e149a2465e79d545c07cca45179a8f43cee64d43b9f0a343b4257143555fb0433f660a432891ef4309ffd842b779a342815d8a41d9fb7841a4b5d6413ca69640db2d8b40bb2834405c8f3d40455b7a3ffca0873f8b9abe3e277fff3dff89d03df1aaf13dc32c533d8620523d6d0b963d18fbc93d0124c93cd7d7c23c9f3cdf3c9dc2fe3c8fe41f3c39fd5e3bf3e2703bd0b7833bc2d8a43b76a7473b3c318a3b23954e3acd3e82
  | 7, 4 => 0x688d1b556709aa6164ffcc4e64cf00c5640159026336351163275f1562b43c1762542af861f427ee6129ea2960d158045f5d13a95f2a63495eebace45ec2fe405ebcebc25e06e6065d9647d45d93d62e5d7bf2db5d3a46645d2e415c5d23bf8f5c0095e65bff541c5b4388f85af03eb05a437adf59f223e55992adb05943cbfb5905159656dbe56f56abec6255ab6c465592bd7c54ed1c7553b7a8b553b3d16b5342fdb75316929452f2fea452e996fb52943af5528ca242520a3fab51efbb6051e81d5151bb2a0f516924ff515c291951007c3a50c9577f50a706e85059633d500139404f8c57c24f490be64ed5e3f64ec05ebd4e7327324e1db72a4e0e9fc9
  | 7, 5 => 0x8a8bfac789f226db89605ac288edfe0d886bb2a5881ad29987ca80ca869b7594862851b98549f6d283d9bb2c827639728241b0597fe35f827f5f0e0b7f4590c97e1a8a567e05acff7dfd47397db1e1917dad4e397d776c2f7d33ff317d1b507d7cfde4937cd372a07c439fcf7ae97d0f7a85129f7a70b128798a90b27952d27478f04d3477d135d076eecc3f76b015da764692e6731d0cce72e03d9b72b2833972739f547263b2ee71fb25a26f3b46226eba99336e34ebde6d45b13a6d2657c06cd622c66bed6d236bc490ee6b7c11ab6b58c0516b46b4d16b1be3666af785736a5eea176a510b386a2a46cf69f5d2f969d0a4b0692e70ee6920920f68b561d0
  | 7, 6 => 0xbcc8e334bc5e25f5bad4da24baa8a17cb9782853b84d21e0b7a3f583b713f0d0b6edc245b644e080b47be621b32b1ae2b1b17014b18cc501b12375bdb0ec7e1fb04d71d7b031ca64afebec7daf01b67aaec64c0eaebd223cadab993dac3ab49dabe5308aabbe6e52ab681b8eaaa935daa9cb11c2a98e4816a8e78fc4a8d9852aa80fa957a71939e5a62fa927a35f8a0fa1689281a0b267039ffd08839f9262399eab30d29e6bbe4b9de9f1209d42bc1d9ce01550996c23f498fcecee985a34f7981b7e9297ec88bb956125c69396353d92a6c201928df768900c69668f6680978e2374cd8dbfa66d8d7f04bb8ce77a638c76bee98c1a6ee88bbc73f08ab84b5d
  | 7, 7 => 0xfc7cb7dbfabc44b5fab495f5f8b72109f5a8ee32f2854adff1c31697f1c1f496f171c893ed71b5aeeb3fcd10e9d3bc26e8f19d4fe8b54ab1e878be20e575a6eae2f7dbbfe2f02cffdfa5c541df71e0b2d958a3e4d69e993fd64007d5d630e845d56748abd3b34341d30f653ad2da325bd0317033cd6ebd58cb26fa2bca35eab9c7ad77bcc7554d2ec707ac1ec61b5c10c5dca5abc57cede8c4ac2c82c4605fcec30bd3fac1c6e06ebe6b5265
  | 8, 0 => 0xbad4da242eedfa851e7359ed1729918f
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x35119020814007110125500400
  | 4, 0 => 0x324c52010004135440300000000000000300000504c420200119020813000000031048203000c5504c430000000434c120100098304c0300000005048420100000254c4202001814210930000000434c52010000045484201000d402081300001844050030000018415043000000042481202000c1154c0300000004248120200000304c520100000304c520100000254c4202000d82048030000000120c4203000005048420100000520c520400000520c520400000234c5201000005048420100000504c4202
  | 5, 0 => 0x60000000000003000003508120000000304c020000000000c8104000000000000200000434c5201000000000000000000310c5200000000008410100000000000060000000000000000000000000400000000000050000051109200000000000000900000504c8200000000000000300000520c52040000000000005000004150420000000450c5200000003508120000000000000030000000081102000000000000600000204802000000040500200000004350c2000000035440200000000008510200000000c9102
  | 5, 1 => 0x10125500300000000000000a000000000000500000000c510100000000000060000000000006000000000000200000000c810000000050c920000000000c110200000520c520400000450c5200000000000000000000000811020000045408200000000008d10100000504c4202000000208120000000000000040000000084103000000010910200000000000070000050508200000000000000200000000000050000000000008000000000000300000000c81000000000000000000001044020000081454803000000051109200
  | 5, 2 => 0x8000001244820000000254c420200000304c020000000000c410200000000000070000000081101000000000000100000000d010000000454c4202000000000000a00000000c910100000520c120000000505042000000000000003000000000000a000000000000200000000000080000010440200000000008d1020000000000003000000000000200000000c1102000000000000400000000c9103000005050420000000510c920300000000000090000000000006000003508120000000000c11020000000000005
  | 5, 3 => 0x5110920000000000c1102000000010d102000004548020000000000c810400000000c810000000520c5200000000000000300000000c11020000000000006000c5504c43000000000000008000000008110100000000c810000000520c1200000000010d102000000000000200000154c820000000454c8200000000000000100000324c820000000324c520100000520c520400000000c110100000254c42020000000000005000000000000a00000000c110200000000000000000035081200000000000000600000434d0200
  | 5, 4 => 0x154c820000000000c41020000021484200000004350c200000000000000000000000000080000000085102000000000000400000304c02000000000000007000002550020000000000000030000000109101000000000000400000000000000000020480200000000000000800000000000010000000000001000005048420100000000c410300000314c4200000002048020000000000c11010000000000000000000008110200000000c810400000000d0100000005048420100000000c11010000000000001000004350c200
  | 5, 5 => 0x600000000c11010000000000005000002550020000000000c410200000000c5101000000000000000000000000070000000048103000000000000a00000000000040000000084103000000008410300000000000020000000000007000000000000600000504c8200000000008110200000454c4202000000000000400000000c51010000000081101000000000000900000504c42020000000000008000000000000100081454803000000000000003000000000000600000504c420200000304c02000000045484201
  | 5, 6 => 0x454c820000000520c520400000520c52000000000000007000000008410300000000000030000000000004000004050020000000504c8200000000008410300000000000080000000000009000000008d1010000000000008000000000000400000511092000000051109200000000000000200000000c1102000000000000500000000000010000042508200000003508120000000000000060000021484200000000008110200000000c91030000035484201000000000000a0000000000009000000000000a00000000c4103
  | 5, 7 => 0x5000005310920000000104402000000000109101000000000000300000000000040000000081102000000000000700000000c41030000000000003000002550020000000000000070000042508200000000010910200000504c820000000000c4102000003544020000000314c420000000520c520400000000c1102000003550420000000000c1102000000000000400000434c120100000504c82000000000000000000000010d1020000000000005000001044020000000000c810400000000000030000000081101
  | 5, 8 => 0xc5101000000010d10200000324c8200000004548020000000000c9101000001510120000000000c410200000454c420200000000000080000000109102000000008c104000000000000300000000851020000000000002000000000000000000050c520000000000c91030000000000007000000000000000000504c420000000000c9103000000010d101000000000000000000000c410300000000c8104000000000000a00000000c1102000003548420100000000811010000000081102000000008410400000000c5101
  | 5, 9 => 0x30000035484201000004540820000000000c11020000000109101000000008110100000454c8200000004248120200000314c4200000000000000100000000000050000035504200000005048420100000000c4103000000000000300000000000000000021484200000000010910100000000c5101000000008510200000000c81040000000000006000001044020000000000c110100000000c110200000000c810400000000c110200000001091010000000000007000003508120000000454c82000000021484200
  | 5, 10 => 0xc41020000000081102000000004810300000000c4103000000010c10000000000c5101000004548020000000000c81040000040500200000000000000800000450c520000000504c420200000154c02000000000000000000000010d102000000008510200000504c820000000304c02000000000000006000002550420000000154c020000000154c82000000031048203000000008110100000324c8200000004344d20100000000841040000041504200000000000000300000000811020000000000006
  | 5, 11 => 0x1000000000000600000000000060000000000003000000008110100000154c02000000000109102000000010d101
  | 6, 0 => 0xc41000000000000002000000000000000000304c02000000000000006000000000000100000000000050000000000008000000000000000000000000010000000000009000000004d1010000000000002000000000000400000000000000000000000009000000000000900000000c11000000000000003000000000000100000000000000000000000008000000000000300000000000000000000000003000000004d1010000000100100000000000000a0000000000002000000008d10200000000000040000000084101
  | 6, 1 => 0x100000000000030000000000009000000000000800000000000080000000000009000004504120000000000000080000000000007000000000000900000000000010000000000001000000000000000000000000010000000000004000000008110200000324c820000000000000060000000104100000000000000200000000000000000000000003000000000000a000000000000200000000000080000000000000000000000000200000000000090000000000008000000000000000000000000040000000000003
  | 6, 2 => 0x1000000000000a0000000000003000000004810300000000000040000000000001000000000000100000000000010000000000004000000000000900000000000030000000000002000000010d1010000000000007000000000000500000000c41030000000000001000000008410100000000000010000000000001000000000e1000000000000001000000000000100000000000080000000000005000000000000a000000000000100000000000070000000000002000000000000100000450412000000000000001
  | 6, 3 => 0x8000000000000800000000851020000000000001000000000000300000000000030000000000002000000000000a00000000000070000000000003000000000000700000000000040000000000002000000000000000000001081000000000000003000000000000a0000000000008000000010410000000000000040000000000005000000000a10000000000000050000000012100000000000000300000000000050000000048103000000004810300000520c5200000000000000100000154c82000000000000008
  | 6, 4 => 0x60000000000008000000000000100000000000070000000000008000000000000900000000000070000000000002000000000000800000000000040000000000005000000000000300000000000050000000000001000000001210000000000000050000000000000000000000000400000000c11020000000000006000000000000200000000000040000000000006000000010910000000000000040000000000001000000000000100000000000090000000000008000000000000300000000000010000000002100
  | 6, 5 => 0xa1000000000000007000000000000200000520c5200000000000000400000000d010000000304c020000000000000070000000002100000000000810000000000000010000000000003000000000000600000000000010000000000004000000000000500000000000030000000000003000000000000200000000000010000000000001000000000000700000000c9101000000010810000000000000020000000000003000000000000200000204802000000000000002000000000000400000000000080000045480200
  | 6, 6 => 0x2000000000000500000000000000000000000007000000000000700000000000030000000002100000000001210000000314c42000000000000002000000000e1000000000000007000000000000000000000c910000000000000050000000000000000000000000300000000c4103000000000a10000000000000070000000000001000000000000100000000c110100000000000000000000000005000000000000a0000000000005000000010010000000000c1101000000000000500000000000040000000000003
  | 6, 7 => 0x20000000000003000000000000a000000000000a00000000d1100000002550020000000000000030000000000001000000000000500000000c110200000000c11020000000000001000000000000300000000c110000000000000020000000000006000000000000100000000000010000000000005000000000000000000000000090000000000007000000000000200000000c110000000000811020000000000004000000000000900000000c510100000204802000000000000009000000000000a0000000104100
  | 6, 8 => 0x48103000000000000a000000000000100000000000070000000000002000000000000300000000c110200000355042000000000000003000000000000500000001091020000000000001000000000000900000000000030000051101200000000010910100000000000040000000000001000000000000900000000c51010000000084101000000000000300000000811000000000000001000000000000400000000000030000000000008000000000000200000000000050000000000002000000000000400000304c0200
  | 6, 9 => 0x50000000000002000000000000400000000401000000000000008000000000000700000000c410300000000000040000000000002000002148420000000255002000000000000005000000000a100000000000000900000000000080000000000001000000000000200000000000040000000000009000000000000200000000000060000000000001000000000000900000000000030000000000004000000000000200000000000020000000000003000000000000a000000000000300000000000030000000000002
  | 6, 10 => 0x300000000000000000000000002000000010d101000000000000000000000c11000000000000002000000000000300000000c410000000000000090000000000004000000000210000000000000040000000000003000000000000900000000000000000000000001000000000000800000000000040000000000003000000000000900000000000060000000000004000000000000400000000000010000000000006000000008010000000000000090000000000002000000000000500000520c52000000000000002
  | 6, 11 => 0x40000000000005000000000000400000000000030000000000003000000000000200000000000050000000000006000000000000400000000000060000000000003000000000000500000000000020000000000008000002048020000000000801000000000000001000000000000100000001081000000035504200000000000000a000000000000900000000c910300000000c9103000000010d10100000000c9103000000000000300000000841010000000000002000000000000200000000000020000000000004
  | 6, 12 => 0x30000000000003000000000000600000000000060000000002100000000000000200000000c410300000000000070000000000003000000000000600000000c9100000000000000300000000000000000051109200000000000a10000000000000040000000000006000000000000200000000000000000000000004000000010d100000000008110100000000c110100000000000040000000000006000000000000400000000d01000000000109101000000010c100000000000000000000000000000000000000000
  | 6, 13 => 0x300000000000050000000000009000000000000400000000401000000000000004000001044020000000000000060000000049102000000008d10100000000c110200000000c910200000000c9102000000000000400000000000010000000000004000000000000300000000000000000000000005000000000000300000504c820000000000000050000000000002000004050020000000000000000000000000004000000000000100000505082000000035440200000000000000200000000000030000000000002
  | 6, 14 => 0x200000000000060000000000008000000000000300000000000030000025500200000000000000300000000000040000000000008000000000000300000000000060000000000008000000000000200000405002000000000000007000000000000300000000000020000000000009000000000000800000000000040000000000001000000000000500000000061000000000000002000000000000500000000000030000000000005000002550020000000000000030000000000006000000000000600000000c4103
  | 6, 15 => 0x2148420000000000000010000000000004000000000000300000000000010000000000000000000000000200000000000030000000000005000000000000400000000000050000000000006000000000000800000000000020000000000003000000000000000000000000070000010440200000000000000100000000000040000000000002000000000000400000000000060000000002100000000000610000000000c4100000000000000400000000000020000000006100000000000000400000454802000000000000001
  | 6, 16 => 0x5000000000000200000000000040000000000001000000000000400000000021000000000000001000000000000400000000c91000000000080100000000000000900000000c9103000000000000500000000000040000000000004000000000000500000000000040000000000006000000010810000000000c91020000000000004000000008410000000000000090000035081200000000000000100000000c0100000000000000a00000000000030000000081102000005110920000000000000080000000000003
  | 6, 17 => 0xa000000000000a000000000000100000000000040000000000009000000000000200000000c410200000154c02000000000000000000000000000200000000c4103000001244820000000500c52000000000000003000000000000400000000c5100000000000000a00000000000000000000000001000000008410400000000000010000000108100000002550420000000324c82000000000000008000000000e10000000000c41030000000000004000000010d100000000000000800000000811000000000000001
  | 6, 18 => 0x30000000000003000000000000a0000000000007000000008410100000000000040000000000003000000000000100000500c9200000000000000000000000491000000000000007000000000000200000000000020000000000003000000010d1000000000000004000000000000000000000c51000000000006100000000000000000000000000030000000000007000000010110000000000401000000000000004000000000000900000000d0100000000000000800000000c510100000000000070000000000004
  | 6, 19 => 0x10c100000000008410100000000000060000000000009000000010810000000000000010000000000000000000000000400000000000010000000000002000000010d1010000000000005000000000000300000000000030000000000001000000000000400000000000050000000000008000000000000200000000c410300000000000020000000109100000000000000200000450c5200000000000000900000000000090000000000002000000000000300000000c9101000000000000100000000000070000000000002
  | 6, 20 => 0x355042000000000000002000000010910200000000c810000000000c41020000000000008000000000000600000000c4100000000000000000000000000010000000000001000003550420000000000411000000000000003000000000000300000000c11020000000000000000000000000800000000000010000000000004000000000000900000000000080000000000003000000000000400000000000000000000000009000000000000300000000000060000000000001000000000000900000000000050000000000003
  | 6, 21 => 0x600000000000050000050504200000000000000600000001051000000000000009000000000000600000000000010000000000008000000010d10200000314c42000000021484200000000010410000000000000060000000000006000000000000a00000000000050000000048100000000000210000000001091020000000048100000000000000a0000000000006000000000e1000000010440200000000000000300000000c41030000000000008000000000a100000000000610000000000000080000000000000
  | 6, 22 => 0xa0000000000000000000010d1010000000000003000000000000900000000c010000000000c1101000000000000800000504c820000000000000040000000040100000000000000600000000000080000035440200000000000000500000001041000000000000003000000000000900000000c81000000000000003000000000000a00000405002000000000048103000000008010000000000000020000000000004000000000000000000000000030000000100100000003508120000000000000020000000000003
  | 6, 23 => 0x600000415042000000000000004000000000000300000000000070000000000007000000000000100000000c9103000000000000300000314c4200000004150420000000000000080000000101100000000000000400000000000010000000100100000000000000300000000c4100000000000000900000000000070000000000005000000000000300000000000060000000000007000000000000700000000000020000000000003000000000a10000000000000060000000000005000000000000a0000000000004
  | 6, 24 => 0x801000000000109100000000000a1000000000000009000000000000100000000000040000000000009000000000000800000000000010000000000000000000000000a000000000000a0000000012100000000000000a0000000000005000000004110000000000c1102000000000000900000000000050000035109200000000000000800000000000050000000081101000000000000400000000c41000000000000002000000000000900000000000040000000000004000000010110000000000021000000000002100
  | 6, 25 => 0x25504200000000000000300000000000070000000000004000000000000300000000000010000000000004000000008d102000000008d1020000000000001000000000000a000000000000300000000000030000000000001000000000000300000000801000000000012100000000010910100000000c810400000000000000000000000002000000010110000000000000030000000000002000000000000400000000000090000000000009000000000000300000000000050000000084104000000010d10100000000c5104
  | 6, 26 => 0x4000000000000300000000000060000000000003000000000000a000000000000a00000000000010000000000005000000000610000000000000020000000000006000000000000600000000000080000000000005000000010d102000000000000a0000000000001000000000000300000000000000000000109100000000000000900000000000010000000000002000000000000000000000000030000000000006000000000000100000000c810000000000000020000000000002000000000000100000000c1100
  | 6, 27 => 0x2000000010d10200000000000030000000000000000000000000a00000000000050000000000001000000000000700000000000030000000048104000000000000700000450c520000000000000040000000000008000000000000a0000000100100000000000000000000000000030000000000007000000000000200000000000080000000000006000000000000300000314c420000000000000070000000000001000000008110200000000000040000000104100000000000000000000000000000000000000003
  | 6, 28 => 0x8000000000000700000000c8100000000000000500000000000010000000000000000000000000100000000000030000000000001000000008d1020000000000002000004350c2000000000000008000000000000a00000000000020000000000004000000000000300000001001000000000000003000000010c1000000000000002000004548020000000000121000000000000003000000004010000000000000000000000000004000000000000900000000000040000045041200000000000000800000000c1102
  | 6, 29 => 0x2100000000010d10100000000121000000000000005000000000000400000000c510400000000000040000000081101000000000000100000001041000000050504200000000000000900000000000010000000000003000000000000700000000000000000000000005000000000000600000000000010000000008100000000004110000000000000020000000000004000000008410000000000000010000000000001000000000000a000000000000200000000000040000000109101000000000e1000000000000007
  | 6, 30 => 0x1210000000000401000000000000000000000000000200000000c91010000000109101000000000000100000000000090000000000001000000000000000000000000000000000000002000000000000500000000c1101000000008110200000000000010000000000001000000000000200000000c81000000000000005000004350c200000000000000800000000c0100000000000000700000000c41000000000000001000000000000100000000000000000000000002000000000000100000000000060000000000007
  | 6, 31 => 0x70000000000003000000008110100000154c02000000000000001000000000000400000000c5101000000000000a0000000000005000000000000100000000481030000000000005000000000000100000000851000000000000004000000000000200000000000040000000000002000000000000300000000000000000000000004000000000000a000000004910200000000c910200000000c5100000000000000900000000000020000000041100000000000e100000000000000300000000000030000000000003
  | 6, 32 => 0x3000000000000a0000000105100000000000000200000000c810000000001041000000000000000000000000000300000000000030000000004100000000000000700000000000070000000000008000000000000600000454802000000035504200000000000000a000000000000600000000811020000000000003000000000000800000000000080000000000003000000000000800000000000090000000000001000000000000200000000000020000000000002000000008410400000000000030000035109200
  | 6, 33 => 0x2000000000000200000000000030000000000007000000000000300000504c820000000355042000000000000005000004050020000000000481000000000000006000000000000400000000000030000000000005000000010c10000000000000050000000000001000000008410000000000841000000000000008000000008110200000000000020000000000005000000000000200000000c11000000000000007000000000000200000000000030000000000005000000008d1010000000000005000000000e100
  | 6, 34 => 0x21484200000000000000400000000000020000000000006000000000000200000000000040000000000003000000000000800000000000050000000000007000000000000300000001041000000000000001000000000000a000000000000300000000000000000041504200000000000000000000000000050000000000006000000000000300000000000080000000108100000000000000900000425082000000000000004000000000000000000000000080000000000002000003544020000000000000010000000000005
  | 6, 35 => 0xa00000000c01000000000000002000002550420000000000000040000000000004000000000000300000000c1100000000000000100000154c820000000314c420000000000c010000000000000000000000000003000000000000200000000c110000000000000040000000000003000000000610000000000000010000000000004000000000210000000000401000000000000003000000000a1000000000000005000000000000000000000000050000000000003000000000000000000000c11020000000000002
  | 6, 36 => 0x1010000000000000030000000000001000000000000000000000000040000000012100000000000000a000000000000600000000000030000000000005000000004d10100000000000040000000000000000000000000200000000000020000000000002000000000000300000000000010000000000009000000000000800000000000070000000000006000003550420000000000000060000000000004000000000000400000000000040000000000007000000000000900000000000010000000000003000000010d102
  | 6, 37 => 0x4000000000000300000000000090000000000001000000000000100000000000040000000000005000000010c10000000000000000000000000004000000000000200000000000060000000000002000000000000a0000000000003000000000000300000504c8200000000000000200000000000020000000000000000000000000300000450c52000000000000004000000008d1010000000000002000000000000000000000c81000000000000009000000000000300000000c410300000000000010000000000001
  | 6, 38 => 0x50000000002100000000000000400000000000050000000000001000000000000a0000000000003000000000000200000000000040000000100100000000000000300000000c81000000000000007000000010d10000000000000010000000000002000000000000200000000481030000000000002000000000000000000000000010000000000002000000000000a0000000000003000004150420000000000000000000000000009000000000000a0000000000009000004350c20000000000000010000000000009
  | 6, 39 => 0x104100000000000000500000204802000000000040100000000000000300000000000010000000000009000000000000300000000000050000000000008000000000000800000000000060000000000001000000000000600000000000010000025504200000000000000400000000000010000000000001000000000000200000000000050000000000009000000000000000000000c01000000000000004000000000000000000520c5200000000000000700000000000080000000000009000000008410100000000c1102
  | 6, 40 => 0x210000000000000080000000000009000000010c100000000000000200000000000020000050504200000000000000700000000000000000000000004000000000000000000000c5101000000000000000000000000050000000000004000000000000100000450c52000000000000002000000000000600000000000090000035440200000000000000300000000000050000000000001000000000000a0000000085100000000004d1010000000000006000000000000a00000000c510000000000000040000000000003
  | 6, 41 => 0x40000000000003000000000000300000000000010000000000004000000000000900000000000020000000000003000000000000a0000000000001000005110920000000000000010000000000008000000000000400000000000020000000000001000000008110100000000000010000000000002000000000000a0000000008100000000000000200000000811010000000000009000000000000800000000000040000000000005000000010c1000000000084100000000000000200000000000030000000000002
  | 6, 42 => 0xa00000000c110100000000000000000000000002000000000000400000000000030000000000003000000000000000000000000080000000000003000004350c200000000000000000000000c110200000000000020000000000006000000000000a000000000000300000000000050000000000005000000000000a00000000000030000000000006000000008410000000000c110000000000000030000000000002000000000000100000000000070000000000003000000000000100000000000040000000000005
  | 6, 43 => 0x30000000000005000000000000100000000000070000000000008000004350c20000000000c0100000000000000600000000000060000000000007000000000000400000000c1101000000000000500000000c810000000450412000000000000005000000000000500000000000010000000084103000000010910200000000000040000000000002000000000000400000000000070000000000005000000000000800000000000050000000000002000000000000300000000c410300000000481040000000000002
  | 6, 44 => 0x8000000000000000000000000080000000000001000000000e100000000010810000000000000010000000000001000000010d100000000000000300000000000000000000081101
  | 7, 0 => 0x10000000041100000000000000a0000000000001000000000000000000000000020000000000004000000000000300000000000020000000000004000000000000100000000000020000000000009000000000000200000000000040000000000001000000000000100000000c4100000000000000400000000000020000000000003000000010c10000000000841000000000000003000000000e100000000000a100000000000000000000000000000000000000004000000000000900000000000020000000000004
  | 7, 1 => 0x100000000000010000000002100000000010810000000000000020000000000003000000000000400000000c9100000000000000300000000411000000000000001000000010110000000000000050000000000009000000000000100000000000010000000000000000000000000300000000000030000000000005000000000000300000000000010000000006100000000000000200000000000030000000000002000000000610000000000c41000000000000003000000000000000000000000070000000000002
  | 7, 2 => 0xc510000000000000030000000049100000000010110000000000000030000000000000000000000000400000000000010000000000003000000004010000000000c5100000000000000000000000000040000000000000000000000000300000000000040000000000003000000000000200000000000040000000000001000000000000200000000000020000000000002000000000000400000000801000000000002100000000000000100000000000000000000000003000000000000000000000c91000000000000008
  | 7, 3 => 0x105100000000010410000000000000020000000000004000000000000400000000000000000000000004000000000000200000000000010000000000004000000004110000000000000020000000000002000000000000000000000000000000000000002000000000000400000000000000000000000008000000000e1000000000000000000000000000400000000000010000000000004000000000000100000000000020000000000001000000008510000000000c4100000000000000700000000000030000000000004
  | 7, 4 => 0x10010000000000000080000000000004000000000000000000000000040000000000000000000000000800000000c010000000000000010000000000004000000010410000000000000010000000000003000000000000000000000121000000000000001000000000000500000000000010000000000003000000000000200000000000020000000041100000000010c100000000000000000000000841000000000000003000000000000200000000000010000000000000000000000000400000000000010000000000001
  | 7, 5 => 0x20000000000002000000000000000000000000020000000000006000000000000300000000000040000000080100000000000000000000000000020000000000001000000000000000000000c11000000000080100000000000000000000000000040000000000002000000000000300000000000030000000012100000000000000300000000000040000000000000000000010010000000000000050000000012100000000000a1000000000000002000000010c100000000000000400000000000030000000000000
  | 7, 6 => 0x10000000000000000000010910000000000000080000000000002000000010910000000000000010000000105100000000000610000000000000010000000000003000000000a100000000000000000000000000010000000000000000000000000300000000c11000000000000001000000000000400000000000040000000101100000000001210000000000000010000000105100000000000000100000000000000000000000006000000010410000000000121000000000000003000000000000100000000c8100
  | 7, 7 => 0xc110000000000000000000000000004000000000000200000000000000000000000002000000000000200000000061000000000012100000000000000300000000021000000000000000000000000e10000000000000040000000000003000000000a1000000000000002000000008410000000000000050000000000004000000000000500000000000000000000000009000000000000000000000000050000000000003000000000000200000000000000000000000003000000000000200000000000040000000000000
  | 7, 8 => 0x700000000000010000000000002000000000000100000000000030000000000002000000008510000000000000030000000000001000000004010000000000000020000000100100000000000000300000000c510000000000c9100000000000000200000000000030000000000000000000000000300000000401000000000000003000000000000900000000c0100000000000000100000000000010000000000004000000000000100000000000020000000000001000000000000000000000000010000000000003
  | 7, 9 => 0x40000000000001000000000000300000000000020000000000001000000000000300000000021000000000000004000000000000400000000000040000000002100000000010d1000000000000001000000010c100000000008410000000000000040000000000000000000000000300000000c81000000000000002000000000000200000000000080000000000001000000000000200000000000080000000000001000000000000800000000000020000000000000000000000000000000000000000000000000004
  | 7, 10 => 0x10000000000002000000010c10000000000841000000000000002000000000000100000000000080000000000001000000000000000000000000040000000000009000000000000a0000000000003000000010910000000000000040000000000000000000000e100000000000000200000000000090000000085100000000010d100000000000000200000000000030000000000004000000000000100000000c5100000000000000000000000000030000000000000000000000000600000000401000000000000002
  | 7, 11 => 0x10000000000002000000010810000000000c010000000000000000000000000004000000000000300000000021000000000000003000000000000400000000000080000000000002000000000000500000000000020000000000001000000000000100000000000010000000000002000000000000100000000000030000000101100000000000000300000000811000000000000003000000000000300000000000010000000000006000000000000a0000000000000000000000000400000000000080000000000001
  | 7, 12 => 0x200000000c410000000000000080000000000003000000000000400000000c010000000000811000000000000000000000000000500000000c81000000000000000000000000000000000000000020000000000002000000000000200000000000040000000000001000000000000100000000000080000000006100000000000000300000000000020000000000005000000010d100000000000e1000000000000001000000000a10000000000000010000000000000000000000000100000000000010000000000003
  | 7, 13 => 0x4000000000000400000000000000000000000001000000000000100000000000010000000006100000000010410000000000000000000000000000000000000000300000000000040000000000008000000000a1000000000000005000000000e100000000000000000000000000020000000000003000000008510000000000000040000000000003000000000e100000000000000600000000000030000000000001000000000000200000000021000000000000003000000000000200000000000010000000000001
  | 7, 14 => 0xa1000000000000000000000000000500000000061000000000000001000000000000000000000021000000000000003000000010d100000000000000800000000000000000000000000000000000000000000000000050000000000002000000000000300000000000000000000041100000000000000400000000c41000000000000002000000010d1000000000000001000000000000100000000000030000000000001000000000000400000000000060000000000004000000000000000000000000040000000000004
  | 7, 15 => 0x3000000000000000000000021000000000002100000000000000100000000000000000000000008000000000e100000000000000300000000000080000000105100
  | 8, 0 => 0x0
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 7 s ws hint
  | 1 => checkCutEntry dom_3 roots_3 6 s ws hint
  | 2 => checkCutEntry dom_4 roots_4 6 s ws hint
  | 3 => checkCutEntry dom_5 roots_5 6 s ws hint
  | 4 => checkCutEntry dom_6 roots_6 6 s ws hint
  | 5 => checkCutEntry dom_8 roots_8 5 s ws hint
  | 6 => checkCutEntry dom_9 roots_9 5 s ws hint
  | 7 => checkCutEntry dom_10 roots_10 5 s ws hint
  | 8 => checkCutEntry dom_12 roots_12 5 s ws hint
  | 9 => checkCutEntry dom_13 roots_13 5 s ws hint
  | 10 => checkCutEntry dom_14 roots_14 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15 == dom_15) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15 goalM u ys) : RunD dom_15 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 7 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 7 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 7 → Z 3 i = true := z3_0
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
theorem z4 : ∀ i, 0 ≤ i → i < 32 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (z4_24)))
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
theorem z5 : ∀ i, 0 ≤ i → i < 160 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (z5_152)))))))))))))))))))
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
theorem z6_440 : ∀ i, 440 ≤ i → i < 441 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 440 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 441 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (range_split z6_376 (range_split z6_384 (range_split z6_392 (range_split z6_400 (range_split z6_408 (range_split z6_416 (range_split z6_424 (range_split z6_432 (z6_440)))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z7_344 : ∀ i, 344 ≤ i → i < 345 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 344 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 345 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (range_split z7_208 (range_split z7_216 (range_split z7_224 (range_split z7_232 (range_split z7_240 (range_split z7_248 (range_split z7_256 (range_split z7_264 (range_split z7_272 (range_split z7_280 (range_split z7_288 (range_split z7_296 (range_split z7_304 (range_split z7_312 (range_split z7_320 (range_split z7_328 (range_split z7_336 (z7_344)))))))))))))))))))))))))))))))))))))))))))
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
  scr dom_15 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_15 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15 roots_15 goal_15 10 := by
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

theorem low_15 : Lower dom_15 roots_15 goal_15 10 := S_15.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_15_bits : ∀ r : Fin 64, roots_15.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_15_lt : ∀ r : Fin 64, dom_15.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_15 T)
    (hlow : Lower dom_15 roots_15 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_15, Avail mask256 roots_15 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_15 hfan 0 roots_15 roots_15 rfl hsup0
  set out := (execN C.gates roots_15).getD C.output 0
  have hout : out &&& dom_15 = T &&& dom_15 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_15_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_15 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_15_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_15).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_15)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_15.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_15 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_15).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_15 &&& mask256 = dom_15 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_15 = T &&& dom_15 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_15, hd63, hout]
  have hnc_m : ¬ IsConst dom_15 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_15 roots_15 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_15, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_15 roots_15 0 roots_15 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4274843776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_15.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_15 10 hT6 (by unfold IsConst; decide) low_15

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [6, 4]⟩, ⟨GateOp.or, [9, 2]⟩, ⟨GateOp.or, [7, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [12, 3]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [8, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_13113_aux

theorem PEqualNP.Outside.L_meta_13113 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4274843776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4274843776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_13113_aux.wit, PEqualNP.Outside.L_meta_13113_aux.wmono, le_trans PEqualNP.Outside.L_meta_13113_aux.wsize (PEqualNP.Outside.L_meta_13113_aux.lower s hs), PEqualNP.Outside.L_meta_13113_aux.weval⟩
