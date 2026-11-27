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

namespace PEqualNP.Outside.L_meta_16137_aux

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

def dom_0 : Nat := 0xa0a00000a0a0
def goal_0 : Nat := 0xa08000008000
def roots_0 : List Nat := [0x808000008080, 0xa0000000a000, 0xa0a000000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(7, 15), (7, 39), (13, 15), (13, 45), (37, 39), (37, 45)]
def r1sG : List Nat := [7, 7, 13, 13, 37, 37]
def r2sG : List Nat := [15, 39, 15, 45, 39, 45]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xc22c234c
  | 3, 0 => 0xc22c234c
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0a0000000000000a0000000a0000000808000008080
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

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
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

def dom_1 : Nat := 0xa0a0a0a0a0a0a0a0
def goal_1 : Nat := 0xa0a0a080a0a08000
def roots_1 : List Nat := [0x8080808080808080, 0xa000a000a000a000, 0xa0a00000a0a00000, 0xa0a0a0a000000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a00000a0a00000, 5, 21)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0xf000f000000000
def goal_2 : Nat := 0xe0008000000000
def roots_2 : List Nat := [0xa000a000000000, 0xc000c000000000, 0xf0000000000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 4 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_3 : Nat := 0xf0f0f0f000000000
def goal_3 : Nat := 0xe0e0e08000000000
def roots_3 : List Nat := [0xa0a0a0a000000000, 0xc0c0c0c000000000, 0xf000f00000000000, 0xf0f0000000000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000, 37, 45)] (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0xf0f00000f0f0
def goal_4 : Nat := 0xe0800000c000
def roots_4 : List Nat := [0xa0a00000a0a0, 0xc0c00000c0c0, 0xf0000000f000, 0xf0f000000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a00000a0a0, 38, 39)] (by decide +kernel) (by decide +kernel) low_0

def dom_5 : Nat := 0xf000f000f000f0
def goal_5 : Nat := 0xe0008000a00000
def roots_5 : List Nat := [0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_6 : Nat := 0xc0c0c0c0c0c0c0c0
def goal_6 : Nat := 0xc0c0c080c080c000
def roots_6 : List Nat := [0x8080808080808080, 0xc000c000c000c000, 0xc0c00000c0c00000, 0xc0c0c0c000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_7 : Nat := 0xf0f000000000
def goal_7 : Nat := 0xe08000000000
def roots_7 : List Nat := [0xa0a000000000, 0xc0c000000000, 0xf00000000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 4 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_8 : Nat := 0xc000c000c000c0
def goal_8 : Nat := 0xc0008000800000
def roots_8 : List Nat := [0x80008000800080, 0xc0000000c00000, 0xc000c000000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 4 :=
  lower_iso [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_9 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_9 : Nat := 0xe0e0e080e0a0c000
def roots_9 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

namespace S_9
def pairsG : List (Nat × Nat) := [(5, 21), (6, 14), (7, 15), (7, 23), (7, 39), (12, 14), (13, 15), (13, 29), (13, 45), (20, 21), (22, 23), (22, 30), (22, 54), (28, 29), (28, 30), (37, 39), (37, 45), (37, 53), (38, 39), (38, 46), (38, 54), (44, 45), (44, 46), (52, 53), (52, 54), (60, 61), (60, 62)]
def r1sG : List Nat := [5, 6, 7, 7, 7, 12, 13, 13, 13, 20, 22, 22, 22, 28, 28, 37, 37, 37, 38, 38, 38, 44, 44, 52, 52, 60, 60]
def r2sG : List Nat := [21, 14, 15, 23, 39, 14, 15, 29, 45, 21, 23, 30, 54, 29, 30, 39, 45, 53, 39, 46, 54, 45, 46, 53, 54, 61, 62]
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
  | 4, 0 => 0x53ca7914
  | 5, 0 => 0xeaf43a4ae2e5fc79dee054fbd062fc47ce41ba68c4f1012bc3bd783c2d03a8980be8b62f
  | 6, 0 => 0xab6ac147a29b3d889980a90d89a9a1a26c7847d9481bdf5416a2ecc7
  | 7, 0 => 0x89a9a1a2
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x707070707070707050505050f0f0f0f05050505050505050303030303030303000f000f000f000f00000f0f00000f0f0000000f0000000f000000000f0f0f0f0
  | 0, 1 => 0xf0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0c0c0c0c0c000000000a0a0a0a0a0a0a0a0a0a0a0a00000000080808080808080808080808000000000
  | 0, 2 => 0xf0f0f0f000000000f0f0f000f0f0f000f0f08080f0f00000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x12839ab5
  | 5, 0, 0 => 0x126ac62593dcd5858127b8a45049ed28d64f7356867b9ac5a9a4f73566693dcd59d80f734a05
  | 6, 0, 0 => 0x24f735696945ee6ad80f735605049ee6ad4127b964593dcd62d812735625
  | 7, 0, 0 => 0x127b9ab5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 29
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfffffc7ff1fffffe3f117e3e3e133f3c3e1fe07fc0fc00f8007fff
  | 0, 1 => 0xf00fc0198187800e0e0f01c000000703ba00e000000000e0000000
  | 0, 2 => 0x1ffe0003f03ff07807e00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xff6f747561fbbeac2c112a3238132d2c321b605d80240080006eef
  | 0, 1 => 0xf24fd139a5a79aae6e3f55c901054f4fbaa9e044002422e0048010
  | 0, 2 => 0x1ffe4443fdbff7f96fe99
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
  | 4, 0 => 0x89a9a1a2667bce622cf968d3
  | 5, 0 => 0xf2d75889ddf35383cf4e4497c8e7752fc6d73ed8c11e1c35bd450f73b83db6c7ab6ac147a29b3d889ebd112d9c96c0fc9980a90d9321526a93105dcc8a1ab9ee89a9a1a274ea9f926c7847d95c5445f359a085a256d2d460548ee642512fb049492063ba481bdf54463fd9af40c9955c3dbfae133d3d73d1372fbb86350869d5346712e0341929122f5600b62679f43221e7ef5620def6a21fc19f2516a2ecc714922a9e10afd3c90b84377d06efdbc50679b9da005176d4
  | 6, 0 => 0xf2d75889ddf35383c11e1c3593105dcc8a1ab9ee59a085a2548ee642372fbb86346712e021e7ef5620def6a21fc19f25
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x4
  | 5, 0 => 0x1000000000060000100000000000c000030000000000400000400001000000000063004080000200000c000080000040000100000400005000000000000000040000200000000002124410c010223440400007
  | 5, 1 => 0x800003000000000020000140000200000800005000000000020000000000100000400003
  | 6, 0 => 0x8000030000100000000000800003000000000040000040000000000c00001
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
  | 7 => checkCutEntry dom_2 roots_2 4 s ws hint
  | 8 => checkCutEntry dom_0 roots_0 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_9 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_10 : Nat := 0xcc00cc00cc00cc
def goal_10 : Nat := 0xc8008800880000
def roots_10 : List Nat := [0x88008800880088, 0xc000c000c000c0, 0xcc000000cc0000, 0xcc00cc00000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c000c000c0, 50, 54)] (by decide +kernel) (by decide +kernel) low_8

def dom_11 : Nat := 0xcccc0000cccc
def goal_11 : Nat := 0xc8880000c800
def roots_11 : List Nat := [0x888800008888, 0xc0c00000c0c0, 0xcc000000cc00, 0xcccc00000000]

namespace S_11
def pairsG : List (Nat × Nat) := [(3, 11), (3, 35), (6, 14), (7, 15), (7, 39), (10, 11), (10, 14), (34, 35), (38, 39), (38, 46), (42, 43), (42, 46)]
def r1sG : List Nat := [3, 3, 6, 7, 7, 10, 10, 34, 38, 38, 42, 42]
def r2sG : List Nat := [11, 35, 14, 15, 39, 11, 14, 35, 39, 46, 43, 46]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_11.map (· &&& dom_11)
def goalM : Nat := goal_11 &&& dom_11
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xa6268017
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccc000000000000cc000000cc000000c0c00000c0c00000888800008888
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_11 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_11 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
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

def dom_12 : Nat := 0xcccccccc
def goal_12 : Nat := 0xc888c800
def roots_12 : List Nat := [0x88888888, 0xc0c0c0c0, 0xcc00cc00, 0xcccc0000]

theorem low_12 : Lower dom_12 roots_12 goal_12 4 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xcccccccccccccccc
def goal_13 : Nat := 0xc8c8c888c888c800
def roots_13 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

namespace S_13
def pairsG : List (Nat × Nat) := [(3, 11), (3, 19), (3, 35), (6, 14), (7, 15), (7, 23), (7, 39), (10, 11), (10, 14), (18, 19), (22, 23), (22, 30), (22, 54), (26, 27), (26, 30), (34, 35), (38, 39), (38, 46), (38, 54), (42, 43), (42, 46), (50, 51), (50, 54), (58, 59), (58, 62)]
def r1sG : List Nat := [3, 3, 3, 6, 7, 7, 7, 10, 10, 18, 22, 22, 22, 26, 26, 34, 38, 38, 38, 42, 42, 50, 50, 58, 58]
def r2sG : List Nat := [11, 19, 35, 14, 15, 23, 39, 11, 14, 19, 23, 30, 54, 27, 30, 35, 39, 46, 54, 43, 46, 51, 54, 59, 62]
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
  | 4, 0 => 0x3c49c5bd
  | 5, 0 => 0xfcb866b43b9dd91e36eafe3e0388c29300cfc650
  | 6, 0 => 0xf32b5140
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccc8888cccc8888cccc0000cccc0000cc00cc00cc00cc00c0c0c0c0c0c0c0c088888888888888884444444444444444404040404040404000000000cccccccc
  | 0, 1 => 0xcccccccccccc0000cccccccc00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x865315
  | 5, 0, 0 => 0x8654250654305865432698654368765436
  | 6, 0, 0 => 0x865435
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf03f3bf81f80330c300071c7800003bffffe200e3810007fff
  | 0, 1 => 0x3fffc01ff8000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf6ff7bf91f88b34d333575d7854d37bd596422acb210006fbb
  | 0, 1 => 0x3fffccdff9044
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
  | 4, 0 => 0xf32b5140e61e1d01b411fbcd99c50613
  | 5, 0 => 0xf3c9374df32b5140d7cd308fd67d09dec957d2a7c7ce6a38c3223540b3bb399fac071bf8a053a964944067428600bbb38084c703800c4ee36e5133495e5fa95d5ab2ea4e2e961a2c14ec70e51133ede2
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x200000800002
  | 5, 0 => 0x100000c0000000000000003000000000000000040000000000400000000004000010000080000100000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 1 => checkCutEntry dom_10 roots_10 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_13 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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

def dom_14 : Nat := 0xffff00000000
def goal_14 : Nat := 0xea8800000000
def roots_14 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 5 :=
  lower_iso [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10

def dom_15 : Nat := 0xa0a00000a0a
def goal_15 : Nat := 0xa0800000800
def roots_15 : List Nat := [0x80800000808, 0xa0000000a00, 0xa0a00000000]

namespace S_15
def pairsG : List (Nat × Nat) := [(3, 11), (3, 35), (9, 11), (9, 41), (33, 35), (33, 41)]
def r1sG : List Nat := [3, 3, 9, 9, 33, 33]
def r2sG : List Nat := [11, 35, 11, 41, 35, 41]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_15.map (· &&& dom_15)
def goalM : Nat := goal_15 &&& dom_15
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xa691cf5a
  | 3, 0 => 0xa691cf5a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0a0000000000000a0000000a000000080800000808
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_15 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_15 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15 roots_15 goal_15 4 := by
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

theorem low_15 : Lower dom_15 roots_15 goal_15 4 := S_15.noCircuit

def dom_16 : Nat := 0xf0f00000f0f
def goal_16 : Nat := 0xa0800000800
def roots_16 : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a00000a0a, 10, 11)] (by decide +kernel) (by decide +kernel) low_15

def dom_17 : Nat := 0xff000000ff00
def goal_17 : Nat := 0xea000000c800
def roots_17 : List Nat := [0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 4 :=
  lower_iso [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_18 : Nat := 0xffff0000ffff
def goal_18 : Nat := 0xea880000c800
def roots_18 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

namespace S_18
def pairsG : List (Nat × Nat) := [(3, 11), (3, 35), (6, 14), (7, 15), (7, 39), (9, 11), (9, 41), (10, 11), (10, 14), (12, 14), (13, 15), (13, 45), (33, 35), (33, 41), (34, 35), (37, 39), (37, 45), (38, 39), (38, 46), (40, 41), (42, 43), (42, 46), (44, 45), (44, 46)]
def r1sG : List Nat := [3, 3, 6, 7, 7, 9, 9, 10, 10, 12, 13, 13, 33, 33, 34, 37, 37, 38, 38, 40, 42, 42, 44, 44]
def r2sG : List Nat := [11, 35, 14, 15, 39, 11, 41, 11, 14, 14, 15, 45, 35, 41, 35, 39, 45, 39, 46, 41, 43, 46, 45, 46]
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_18.map (· &&& dom_18)
def goalM : Nat := goal_18 &&& dom_18
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x8888432e72657d5c
  | 6, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000ff000000ff000000f0f00000f0f00000cccc0000cccc0000cc000000cc000000aaaa0000aaaa0000333300003333
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x1ac21758d16
  | 6, 0, 0 => 0x6b195
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfff000f80fe0c78e1c36419f30018001bc7bc9be60
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfff852fd2fede78f1cb6d7bfb407ad5bfcfb492840
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
  | 4, 0 => 0xbbfdd59bb88e4e2f67ae8f750f1fce07
  | 5, 0 => 0xe9082d54e505bdfab7253fbdaf799c90a7da18faa1c0b4b8a1712e8b9f39fa5292b6c7608c5e12727ea52a9a7445a6b56949f7d6686e9bda5ba073fa5b61388b4d7877b94c554d372fef2b28270b03de160058940f1fce070da784ce0ce9d017
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x40000000001000000
  | 5, 0 => 0x10000000000040000300000400000000004000030000000000000000000003000004000010000040000300000c00002000000000000000000000000001000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_14 roots_14 5 s ws hint
  | 1 => checkCutEntry dom_16 roots_16 5 s ws hint
  | 2 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 3 => checkCutEntry dom_15 roots_15 4 s ws hint
  | 4 => checkCutEntry dom_17 roots_17 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_18 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_18 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_18 == dom_18) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_18 goalM u ys) : RunD dom_18 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_18 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_18 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_18 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_18 roots_18 goal_18 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_18 goal_18 := by
    have h0 : isConstB dom_18 goal_18 = false := by decide +kernel
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

end S_18

theorem low_18 : Lower dom_18 roots_18 goal_18 7 := S_18.noCircuit

def dom_19 : Nat := 0xa0a0a0a0a0a0a0a
def goal_19 : Nat := 0xa0a0a080a0a0800
def roots_19 : List Nat := [0x808080808080808, 0xa000a000a000a00, 0xa0a00000a0a0000, 0xa0a0a0a00000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a00000a0a0000, 1, 17)] (by decide +kernel) (by decide +kernel) low_15

def dom_20 : Nat := 0xf0f0f0f0f0f0f0f
def goal_20 : Nat := 0xa0a0a080a0a0800
def roots_20 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_20 : Lower dom_20 roots_20 goal_20 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a0a0a0a0a, 10, 11)] (by decide +kernel) (by decide +kernel) low_19

def dom_21 : Nat := 0xff00ff00ff00ff
def goal_21 : Nat := 0xea008800aa0000
def roots_21 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_21 : Lower dom_21 roots_21 goal_21 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc, 33, 35)] (by decide +kernel) (by decide +kernel) low_10

def dom_22 : Nat := 0xffffffff00000000
def goal_22 : Nat := 0xeaeaea8800000000
def roots_22 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_22 : Lower dom_22 roots_22 goal_22 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f000000000, 42, 46)] (by decide +kernel) (by decide +kernel) low_3

def dom_23 : Nat := 0xff00ff00000000
def goal_23 : Nat := 0xea008800000000
def roots_23 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]

theorem low_23 : Lower dom_23 roots_23 goal_23 5 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14

def dom_24 : Nat := 0xffffffff
def goal_24 : Nat := 0xeaaac800
def roots_24 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_24 : Lower dom_24 roots_24 goal_24 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccccccc, 9, 11)] (by decide +kernel) (by decide +kernel) low_12

def dom_25 : Nat := 0xff00ff00ff00ff00
def goal_25 : Nat := 0xea00ea00ea00c800
def roots_25 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

theorem low_25 : Lower dom_25 roots_25 goal_25 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff000000, 9, 25)] (by decide +kernel) (by decide +kernel) low_17

def dom_26 : Nat := 0xff00ff00
def goal_26 : Nat := 0xea00c800
def roots_26 : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]

theorem low_26 : Lower dom_26 roots_26 goal_26 4 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17

def dom_27 : Nat := 0xffffffffffffffff
def goal_27 : Nat := 0xeaeaea88eaaac800
def roots_27 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_27
def pairsG : List (Nat × Nat) := [(1, 17), (3, 11), (3, 19), (3, 35), (5, 21), (6, 14), (7, 15), (7, 23), (7, 39), (9, 11), (9, 25), (9, 41), (10, 11), (10, 14), (12, 14), (13, 15), (13, 29), (13, 45), (16, 17), (18, 19), (20, 21), (22, 23), (22, 30), (22, 54), (24, 25), (26, 27), (26, 30), (28, 29), (28, 30), (33, 35), (33, 41), (33, 49), (34, 35), (37, 39), (37, 45), (37, 53), (38, 39), (38, 46), (38, 54), (40, 41), (42, 43), (42, 46), (44, 45), (44, 46), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54), (56, 57), (58, 59), (58, 62), (60, 61), (60, 62)]
def r1sG : List Nat := [1, 3, 3, 3, 5, 6, 7, 7, 7, 9, 9, 9, 10, 10, 12, 13, 13, 13, 16, 18, 20, 22, 22, 22, 24, 26, 26, 28, 28, 33, 33, 33, 34, 37, 37, 37, 38, 38, 38, 40, 42, 42, 44, 44, 48, 50, 50, 52, 52, 56, 58, 58, 60, 60]
def r2sG : List Nat := [17, 11, 19, 35, 21, 14, 15, 23, 39, 11, 25, 41, 11, 14, 14, 15, 29, 45, 17, 19, 21, 23, 30, 54, 25, 27, 30, 29, 30, 35, 41, 49, 35, 39, 45, 53, 39, 46, 54, 41, 43, 46, 45, 46, 49, 51, 54, 53, 54, 57, 59, 62, 61, 62]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_27.map (· &&& dom_27)
def goalM : Nat := goal_27 &&& dom_27
def NN : Nat → Nat
  | 1 => 1
  | 2 => 5
  | 3 => 19
  | 4 => 38
  | 5 => 63
  | 6 => 142
  | 7 => 137
  | 8 => 21
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 1, 0 => 0x18d2f01e
  | 2, 0 => 0xfde026f59e01439f9d005b9a47964a9d165217da
  | 3, 0 => 0xf5cba53ee810fea9d16cb136cbc3b619c07f35bfb8aa821ab10dffd7a39d0e50a1043b67815445d26c0a018d67487e5f623f8918613cf0b84515725933988ec82ca3817427a2cb97156c54c5
  | 4, 0 => 0xfdbc98e0eade9072e66cf494e3634d7fe10e517eda1f8f76d2e5b733d2d38d50cee35379b8906937b86ab408b2c8048fb286dabfb017a051acda430ea8f97e209c530cc298efb9b096477f1b85b2092383a2aed879c2cb5676adaa177449c4b26a72ee136754ccc6602997755fbeb0d44d4ee3b448ff1406474cbfef44ca05bb24ab89a1248effbd1e9ffbfa165e1c440d57d30e02ba3d24
  | 5, 0 => 0xffcae455ff09a06efd1b085ff958c955f5a81729f1abbd46eeb28084ee78f5c5e538cb84e4624366dbce60d2db9d9d8dd999e11fd8f9cfc7d356fcb3cf7b4a43cf78f3bbcad1357ccac0deccbb38cee6bb0bd775b831fff6b8287ff0b226724fb07be780a69f125aa50d5a2da38ce6d7a233a7539eac52a39cbe9e4096217c0e945d6fe4928c9d4b8d4d685889e26d3a86702b057e0199417d52a5bf7d43a3e879d4941e7603c96a6fed95156c3542fb6bb25d68625e6c5c5f404b0f5e2487c259b6180454eb6c7853aa8a5d4fb4ade64cf1521343cf01b73f383e383d9279ca364ada462daeb2ee277095f2183710780c3ad8e108e2e9f5022d10fd
  | 6, 0 => 0x7e318a3678d9901a75950b386f897d916a22b4f8656f6c2e61e8177e5ffe18ca5eb5ede35ea8e5c25cfed90c5c7b245559254669582291a252f34f5950892d334e83a6434defc3b64d8a6a384d84259f4d419edb496fc9e446b256944631106d43943547415d8698414fa7b93e4fa7d43d2c7c353b6273ae39de4fb637f1a35037379f603556e60732b96323325dbd6d2cf4d84c2c2937292c008f962bcbbe4a2bae16fd2b7b7d022b7b467f2b15732c2a6347522867c1802865a5ab259a3137238c28701c96ea491b3080b11a4359e7196cd1c912f5236a1236e74d10fc0e1810d8ef350ee7b93a0b362c5e0a2a3f0d04e6f81302f1f85901a44b7b00ce3ea5
  | 6, 1 => 0xddaa279ddd2c37d2db4f33a9d9fc0161d4077324d29440d5d0c96219d0ad9383d0a5ce8bd07db453d0346fc3cdfcc0dfcd368758cb5a385fc9834476c6ca6586c277339ebe129a87bd4db9ffbab9a1bdba694344b932cbabb52c0985b51e52aeb30c27a4b2bdb791b0180197af616e2baf251fb4ae851bdfa828f69ba7fc18f5a6c134b9a4a20be6a23d1ba0a15d9d059f0c76639ec71c229ec0d7899ae7f59e99e5b62f97a53cfb9697d0ec95b3875294cfd1b89499c43194967799927fc7e7919ac8ae9182d7579149dd84910c8c998e0cfa57893fd90988e0387f8823b6e4876e747f8690a30e8519787e8323215e82bd0ad380d47de97f8ef2d87f05801f
  | 6, 2 => 0xfc78742efbd768b2fb12ce0df3cea65ff194b92bf153019ff144479ef0435d49efafc882eeb1ac64ebefca4beb57e6efe73672d5e4516627
  | 7, 0 => 0x6aa2ab606920920f6554bad163353df463275f156240ab87612e3cdc610b1df95c91de8159d395c7551926d754c1de1053a9644a531692945314eaf652de426a51bf3f2b51ab7a23515c2919505beeb34e1717654bff26be4a3f78dc4a0d197448b0ac9d44cd758b4365b3a9413f306a3f086e6d3e1c8eb63c21f90f396f572d3678c0eb36224d1b354bc4fd342cdee9330961a63129ad3f2d6df75a2cb7e2692b81626d29e942c42705880d26beaf6f2609324123e92d1222d85c9a20dfc24720df43cc204bdfba20292edb1a0ece701a0dc40d18e3fb0a15f022ce131bfefa119811440f8898390dfb96ef0c22507d0acf09dd09ee1b6f06291d83055e3849
  | 7, 1 => 0xeef94ae6eef3064ded612b3de6f71c21e2f02cffe1ccafbcdede789bdd1bb31cd7d8277ed69e993fd630e845d17f337bcf9551ebceeb1ad8cd6603e8c6f762cbc5899ec0bf01fb40be4be64fbe2c7e6ebd199d0fb4d0d4a4b04d71d7b02268afaf1123ebac8a86ebaaa935daa6681578a661d0dfa494c22fa3257e1da309310c9dbc98fc9db654639b69643899ed5e8799d7582f992721c298553ede94b8834e8f6e24048e35cdb08e0d834f8dce939b8d5eaaf98bc68b50869b75948279e3b982739f2081c3cec881bd8a2f804281917e22428f7bfded0e7aebbb247a85129f7913045378925775785a17897540089873b9b90973a1eeb77260e48f6bcb63fb
  | 7, 2 => 0xff939ceffe9afd92fc3cf275fbe5e7c4fb192d73fac274d4fab495f5f1027f58ef0e3eb4
  | 8, 0 => 0xf33b5fd0f2854adfdee29a6ad1f5fd8cd1efb8f3bad4da24b47be621a1f16def7cea112d76f0de33705b5d9f61ca40085fbac6fd5e22a7544aee73793e277fff2efbd9642eedfa851729918f1606144c0e7e1513
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55ff000055ff00005555ffffffff000055550000ffff000033ff000033ff000033330000ffff000000ff0000ffff000000ff000000ff00000000ffffffff
  | 0, 1 => 0x3333333333ff33ff333333333333ffff333333333333333322222222aaaaaaaa00ff00ff00ff00ff00aa00aa00aa00aa0000ffff0000ffff0000777700007777
  | 0, 2 => 0x555555555555555550505050505050503f3f3f3f3f3f3f3f33773377337733773333777733337777333333ff333333ff33333333ffffffff3333333377777777
  | 0, 3 => 0x777777777777777770707070707070706262626262626262555555ff555555ff55555555ffffffff55555555aaaaaaaa5555555555ff55ff555555555555ffff
  | 0, 4 => 0xaaaa8800aaaa8800aa88aa88aa00aa00aa00aa00aa00aa0088888888888888888888888888880000888888888800880088888888000000008888880088888800
  | 0, 5 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaa00aa00aaaaaaaa00000000aaaaaa88aaaa8800aaaaaa00aaaaaa00aaaaaa00aaaa0000aaaa8888aaaa0000
  | 0, 6 => 0xcc88cc88cc00cc00cc44cc44cc44cc44cc00cc00cc00cc00c8c8c888c8c8c888c0c0c0c0c0c0c0c0c0c0c0c0c000c000c0c0c000c0c0c000aaaaaaaaffffffff
  | 0, 7 => 0xcccccccc88888888cccccccc00000000cccccc88cccccc88cccccc00cccccc00cccccc00cc000000cccc8888cccc8888cccc8888cccc0000cc88cc88cc88cc88
  | 0, 8 => 0xeaeaeaeaea00ea00eaeaeaeac000c000e0e0e0e0e0a0e0a0dddddddd55555555dd55dd55dd55dd55cccccccccccccccccccccccccccc0000cccccccccc00cc00
  | 0, 9 => 0xf0f0e0a0f0f0e0a0f0f0c000f0f0c000eeeeeeeeeeaaeeaaeeeeeeeeaaaaaaaaeeeeeecceeaacc00eeeeee00eeaa0000eaeaeaeaeaeaeaeaeaeaeaeaeaaaeaaa
  | 0, 10 => 0xff55ff5555555555ff00ff00ff00ff00ff00ff0000000000fafaeaaafafaeaaaf0f0f0f0f0f0f0f0f0f0f0f0f000f000f0f0f0c0f0f0c000f0f0f000f0f0f000
  | 0, 11 => 0xffccffccff00ff00ffaaffaaffaaffaaffaaffaaff00ff00ffaaffaa00000000ff88ff88ff88ff88ff88ff88ff00ff00ff88ff8888008800ff55ff55ff55ff55
  | 0, 12 => 0xffffaaaaffff0000ffffaaaa00000000ffffaa00ffffaa00ffff8888ffff8888ffff8888ffff8800ffff8888ffff0000ffff7777ffff7777ffff0000ffff0000
  | 0, 13 => 0xffffff0000000000ffffeeaaffffeeaaffffeeaacc00cc00ffffeeaa00000000ffffccccffff0000ffffcc88ffffcc00ffffcc00ffffcc00ffffaaaaffffaaaa
  | 0, 14 => 0xffffffff88888888ffffffff55555555ffffffff00000000ffffffccffffcc00ffffffaaffffaaaaffffff88ffff8800ffffff00ffffff00ffffff00ffff0000
  | 0, 15 => 0xffffffffffff0000ffffffffff00ff00ffffffffcc00cc00ffffffffaaaaaaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 1, 0, 0 => 0x39482
  | 2, 0, 0 => 0x1c24223e0c959e3ab20f9325e782cc83
  | 3, 0, 0 => 0xc75592f4e11602f4e14e02b4e1017964a72a02f4e12202f4eb8eb484e94ddaf4ef82d494e54e02f4ef8ab494c16592f4e14602f4e0c97a24e74e0294e14e6a24
  | 3, 0, 1 => 0xc1564224e9c192f4e14e5af4
  | 4, 0, 0 => 0xeb8eb335ebeb8425e594070a700ba00e10192f4eba6b345eb82cd380bd7ad6a9093a80a7017824e14e02f44bdf05692857ae0b52522e0aac97a25eb8ab4948bc29c05ea57055a73512f4e14e02f5
  | 4, 0, 1 => 0xe14e02f2ebd755666bd7356a7093af0a73602f5c1562c05ebcf85380bd70568d017af5c75992f5c15a44058b82ac05e597be0b4cd7ae0ab2202f5ef8ab335ebc29c076bd7ae0ac90eaecad4e1275
  | 4, 0, 2 => 0x70a6bc7a7ae74e1295c7569c05ebc29c05e09785380bc7af5c15a4225
  | 5, 0, 0 => 0x182b5384697ae0b4cd7a46d39ab5384bdbae2accd7a46db82b5384bdbae4ad4e12a601d7056927d7055a7017a26eb82b4980bdbae9ad09796601eb853845d7d75c15a4a46eb82b494801807aa7097825eb82b325e89bae0ad252216
  | 5, 0, 1 => 0xf5c29c25e5dbae4ad4e12e6eb8eb5384bdbae0ad017966eba2b5384a1bae9ad4dd2f6eb82b49487dbad69d097a76eb82b4880bdbbe0accd7a16f5cf85384bdbaf3ad4e1296f582ac25e59bae9ad4deaf60182ad3805d4060ab0192f5
  | 5, 0, 2 => 0xf382b425e59bae0accd7a26c1569c05e5dbae3ad4e02f601d7049482d7ae8ad4e1296ef82d5384bdbae0acdd9af6ef8ab5384bdb055a73602f6f5c29c25e09baeead4e1276eb92b5378bdb05680cd7ac6000385380bd3ae0ad1602f6
  | 5, 0, 3 => 0x3669ad4e12f6eba6b4f84bdbae8ad4e1276ebc2b425e598060ab4d78f5eb82b539a89baeaad4e12f6eb82b4784bdbbf5c15a4a46eb82dd692918060ad252005c15a0325eb1bd70a7097a96c1569c05e3dbae9ad5212f6
  | 6, 0, 0 => 0xeb82b5380bd1380eb4d78d1625baf0ad4e12f2efdfae0accd7a47eb82dd666bd2380c15a9c05eb1bae0ad4e12f0ae0304266bc58060182b335e900375c15a9c25e4dc075c10979516c03ae0ad019af60182b425e580300cd829c25e2dbae0ad4e2425efebae0ad2612f7
  | 6, 0, 1 => 0xeb82b335e910b80eb8ab5384bdbae0ad4e12f30e03ae0a10978b601d7042665c5b75c15a9c26cbdc000eb82b4948a0305684bca806ebc2b5384bc13f5c582b5384bdfae0ad4e12f4cfd7769ad4e12f7eb82b5384bc43f5c15a12f2c2dfae0ad099af5ae03d60ab4e1176
  | 6, 0, 2 => 0x1d70562e586b00eb82b525e358060ad0999700c03053845c5806eb82b335e9003f5c15a9c25e1dc075c15a9c02edd7868ad4e12f701d705680c97b75c15a1355e59fae0ad0979600fd705dad099af7015a9af1a240300eb82d5384bdbae0ad4e12f24f82b5384f97ae7
  | 6, 0, 3 => 0x1d61335e2c4b00eb82b335e7dbae0b54e12f48fd7156a7097a47eb82b5384e57bfac15a1335eb1c000f5c29c25eb9b056a709aaf7f7d7256a7097bf5e15a9c25ea5fae0a709aaf54febae0accd7a4701d6b532e344b75d35a9c25e5dc060ad4212f00debae0ad097967
  | 6, 0, 4 => 0xeb82b5384bd1bf5c15a9ba6abdc075ad4e12f04dd74e0ad3a12f7f582ad384bcbbf5c15a9c25ea1c079c15a9c22edd7056a7097997eb82b5384bc13f5c15a9c25491fae0ad4e12f1efd74e8ad4e12f701d70565e586b75c15a13c62bdfae0ad0979f3cfd75e8ad4e12f7
  | 6, 0, 5 => 0x1e3056a708db75c15a9c25e39fae0ad4e12f06e03360ad4d78d6eb87056a7097b80ad099af1201805384bc58900c03ae9ad3a12f6eb82bd6a7097bf5c15a9c25e51c000c1569c05ebdf056a7097a17eb82b539b017bf5c15a9c25e71c075c12612f16dd7056a7097907
  | 6, 0, 6 => 0xeb82b5384bc63e0ad4e1405eb1fae0ad4e02f1ee03ad3845c5896eb82b5384bd4bf5c15a9c25e81c060ad2612f00dd7056a7017a47eb82b335e90fb80ebc2b53845d8075c108b9616c030535e345806eb82b5380bcbbf5c15a84278bdc078c15a9ac1add74d6a7097847
  | 6, 0, 7 => 0xeba6b5384bd3bf5c15a9bc5e91c056a708b8900c03ae0ad4d78f6eb82b5384dd7bf5c15a9c384bdc075c15a82f1ac03056845cb00601d6b5384bc2375c15a1335e05c060ad4e12f0cdd7056a7097247eb82b427cbcb380eb829971a2db3e0ad4e13e5efd7056a7097847
  | 6, 0, 8 => 0x3ae0ad4e12f4efd78e0a109aaf7ebcf856a7097bf5e392b5384bdfae0ad2612f00fe7056a7097977eb82b5584bcb380eb819af482d8075d35a9c22edd7056850192f70182b532e340375c15a9c25e89fae0b14e1355ee03ae084bcb0b6
  | 7, 0, 0 => 0x1d78e0ad4d78d70003ae0ad4a12f60003056a6bc6806eba3056a709f2f801d74e0ad4e12f701d7056a7097a1701d75e0ad4e12f7eb82b55a70979780182f56a70978070002b5384bc480601d72e0ad4e12f701d705384bd20b701d7058ad4e117701ebae0ad4e117701d705384bcb8b70003ae0ad2612f6
  | 7, 0, 1 => 0x1d705cad4e12f7efd7056a7097a48eb82dd6a7097a4801d6b5384bd609701d6b5384bc589701d7460a70978b7ebc7056a7097a480182b5384bd20070003ad6a708b89601efae0ad4e11770003ae0bd4e12560182b5384bcb80701d7056a70a02f70003ae9ad4e12f601d7056a709faf70003ae0ad08b966
  | 7, 0, 2 => 0x1a3056a709780701d7056a7097917eb82b5384bd624801d7056a709d2f701d7056a709e2f701d6b5384d57897eb82b5384bcb8b801d705384f978b701d7056a709217701d7056a6bd60d701d7056a70979b701d7056a709781701d7058ad4e12f7eba3056ab4e12f80003ae0ad4cb8d601d7260ad4e12f7
  | 7, 0, 3 => 0x182b5384f97807eb82b5384bd2008ebc7056a7097aa8eb82b5384d57978eb82b5384bcb808eb9f056a7097ac80003ae084cd78b60003ae0accd7a4601d7056a6bc68070003d60ab4e12f60003ae0ad09796601d705384bc58a701d78e0ad4212f7eb82b5384bd221801d7056a70a0af70182b5384f97ac7
  | 7, 0, 4 => 0x1d78e0a70978b7000305684cd7806000305384bc580601d7056a709297701d7056a709c2f70003ae0ad0979560003ae0ad4e02f60003c60ad4e12c6eb82b539909f2f801e3ae0ad4d78d7f5d7056a7097a48eba3056a70978b80003360ad4e12f6eb93056a7097a48f5d7056a709797801ebae0ad4d78d7
  | 7, 0, 5 => 0x3ae0ad0999760003ae0a708b8b601d78e0a709aaf701d6b5384bd209701ef056a709f2f701d7056a7097ad7f7d7056a7097a4801d7056a70979f701d705ead4d78d7eba3056a709aaf8ebaf056a709f2f801d73e0ad4e12f70003ad6a6bc689601efae0ad4d78d701d7056a709f17701d78e0ad099af7
  | 7, 0, 6 => 0x1d7056a70978a701d78e0ad4e11770003056a708b80601d705684cd78070003ce0ad4e12f601d7056a7097aa701d77e0ad4e12f701d7360ad4e12f701d705dad4e12f701d705fad4e12f701d7056ab4e117701d705684cd7ac701d705384bd60b701d7056a6bcb8d70003ae0ad4212f601c7056a7097807
  | 7, 0, 7 => 0x3ad684cd78960003ad384bc589601efae0ad099af70003af0ad4e12f601d7056a709617701d7056a708b8b701dbae0ad4e117701d7860ad4e12f701d6b5384f978970182b5384c1780701eb056a7097ac701d6b5384bd289701d7460ad4d78d7eb82b5384bd21f801ebae0ad099af70182b5384bd6007
  | 7, 0, 8 => 0x3ae0a6bc68b6ebc7056a709e2f801d7056a7097ae701d6b55a709789701d705bad4e12f701d7056a709a97701d7056a708b80701d705ea70978b7eb82b5384f97978
  | 8, 0, 0 => 0xeb82b5384f97bf5c15a9c25e95fae8c15a9c25efd7056a7097a47eb82b5384bcbb80eb82b535e35bae0bd5a9c25ee03ad6a7097896f7d7056a7097bf8eb82b5384bdfd75c15a9c25efd7056a709aaf7eb82b5384bc03f5c15a9c25eb1fae0ad4e12f16e03ae0ad4e1176
  | 8, 0, 1 => 0x1d78e0ad4e12f70182b5384bc0375c15aad384bdc075c15a1335ec03ae0a70978b6
  | 9, 0, 0 => 0x3ae0ad4e12f6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 1 => 18
  | 2 => 25
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
  | 0, 0 => 0x3fff8001c7fc00ff11fffffff003fc4000ffffc00cffe003cfff00323b800ffffc0007fe003ffff0001ff800007fc000001fffffff
  | 0, 1 => 0xce723be7ff3fff39c8ef917ffffce723be45f38440000ee0038fdf07c1ff83f007fc0000ee00001df003fff800ffffc00fffe003fe31
  | 0, 2 => 0xffffc47ff1c08318c7018f04020fffe3ffc7ff87f3fcfff9ffce31ce7fffe45ff8c739cfff917cfffce723bffffffff39c8efffffe31
  | 0, 3 => 0xfffffffffff8c718c7e18f3c0300001fb838e38c7ffffffffc71ffffffc47fffffffffff100038fdfffffc47ff1c7ffffff11fffffff
  | 0, 4 => 0x38e00000000000e380000000000001ce000000000000000000000000000000000000000000000000000000
  | 0, 5 => 0x3b800e3f7c0000ee000000000003b800e38000000ee0000000000000000000000000000038e00000000000000000000000000000
  | 0, 6 => 0x300c001800c000c637106e83020300c001800c0000000000e001ce0001c0038007800007000000000000000038000000000effffffff
  | 0, 7 => 0x318dc400000738c637100000000318c001ba0c738c630006e83000318c0018000000c600006e801ce3180001ba00000c0300060031ce
  | 0, 8 => 0x1fb800e38000007ee00000000001f8000e0743ffff11ffc7020ffffc47ff1c080c637106e831ee318dc41ba00000c637106003000
  | 0, 9 => 0xc6003863ce07431800018f00000318dff980eff7cc637fe0038fdf318dc41800c000c6300060000000001fb838e3ffc0007ee0038fdf
  | 0, 10 => 0xffffc47ff1c083e0f801f03fe00f83e00000000031800ef8f38fdfc631f863cf07c318c7e1803c000c631c063c0000318c0018f3c000
  | 0, 11 => 0xf9bfc47c0ff803e0f8eff03ffdff83e3bfc0ff803e0f8ee0000000f83e007c0fff3be0f801f03fe00f83e0000000003ffff11ffffe20
  | 0, 12 => 0xffc03bfff00003ff00ee0000000ffc0007ffe3803ff0001ffc01ceffc0007ff00003ff0001ffc0000fffffffffff8c7ff0001ffc0000
  | 0, 13 => 0xfffe0000000003ff30effffbfdfffcc3b9800c003ff30ee0000000ffcdc47ff00003ff3001ffc3000ffcc007ff0c003ff00effff8fdf
  | 0, 14 => 0xffffff8000073bffffffffc7020ffffff80000003ffff11ffc3000fffe3bfffe3f7ffff801ffc0000fffe007ffff803fff801ffc0000
  | 0, 15 => 0xfffffffff00003fffffff03fe00ffffff9800c003fffffe0038fdf
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x28cc800184a000a201f7df6f70028800003c9880049760020908001211000be988000132000f36a00004c80000420000001f7df6f7
  | 0, 1 => 0x4a523324fc32552948cc917fe734a5233245c30452948ccb3f9ed707c16e82f006740b01ba03c019d003edd800beda800ea440026820
  | 0, 2 => 0xa529805301808294a6014c060205ad637ac7c787d3d4ccc9970c114a7ab3245db0c52949fe9170d194a52337dfffbdd2948cdd576c31
  | 0, 3 => 0xef7bb3775db0c79ce6c1cd36030ef7bb3775db0c694a7334c06128a529807ff7dbde94a600bbd96d7a5298053f182d694a6014c0f262
  | 0, 4 => 0x5ac4222cf65b5d625976b039f4a5816112c0e790842113222893ce10844c88a00630421132200934a10844c8000042042100022892c6
  | 0, 5 => 0x5ad67facfe7f7d6b59feb3f0d9d5ad67fac0e7d296b59fe00209085ad67facfe7f7d6b58ccb3f9ed75ad6332cfc32556b11bab3d059d
  | 0, 6 => 0xb0acccd903cdaad4b6016c0f262b02c805903c98ad6b7336e8f3eea529c85383878294a7214c0e160a52980538383816b59fff7fffff
  | 0, 7 => 0xb5adcc8aa24f3ad6b7320800108b5adccdba3cfbad6b6016e8f2e6b5ad805b000002d615336e893ceb5854cdba00632c2b333668f3ee
  | 0, 8 => 0xffffffff0ffdabffffff4c2e968e739f873cf87c2d6b7334c06128b52d805b03c98ad6b7336e8f3eeb5adccdba00632d6b7336c0f36a
  | 0, 9 => 0xe739f873cf87c39ca681cf1e0f0fffffffffffffffffffebbf9fdffffffffffffffffffecdfff0c95fffffffffffffffffffffffffff
  | 0, 10 => 0xfd3f915309a083e0fa45f43fe62f83e9100082003fffffffffffffe739f873cf87c39ce7e1cc3e160e739f873cf87c39ce6c1cf3e0f0
  | 0, 11 => 0xfdbfddff0ffdabebfbfff7ffffffafefffd0ffdabebfbfe0020908f8beddfdafffbbe2fb77f43ff6af8bedd880a6d2bf4fe45fc3fe62
  | 0, 12 => 0xffd77ffffc3677ff5dfe0820908ffd7337ffe7b5fff15bbffd97dfffc56efff65f7fff15bbffd059dfffbb37ffdb2d7ff0489ffd0495
  | 0, 13 => 0xffffb302082003fffffffffffffffffffdb0bedabfffffe0820908ffedeefff41677ffb7bbffdf7ffffeda27ff7dbdfff5dfffff9fdf
  | 0, 14 => 0xffffff8aaa6f3bffffff4c26928ffffff82082423ffffffffffffffffffffffe7f7ffffffffff9fdfffffb37ffffbdffffecdfff0c95
  | 0, 15 => 0xfffffffffc3677fffffffc3ff6affffffdb0bedabfffffebbf9fdf
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 54 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 54 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 124 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 124 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 124 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 124 then wireAt i else 0
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
  | 2 => 1
  | 3 => 5
  | 4 => 35
  | 5 => 250
  | 6 => 1326
  | 7 => 928
  | 8 => 24
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0x8ab74e99
  | 3, 0 => 0xb549fb989eac52a382a2cce239070fcd253cdea8
  | 4, 0 => 0xfe86b934fc42d4a8f7298a21ef686145e52d1b5ee13f328cca867937b8d2e5cead3579e1ac647e1da887e044a6a5a47aa658f0769697d0ec8350706e787e7cb071567d3a66f6b71a61e8177e610b77b05d7963c1593e8f924f81cc89431cabba4024100931125edf2c008f9624bcc92d233d76451fd864321d285cf10d9111cd0a250b8d037fed8d02832f57
  | 5, 0 => 0x391ed4393834be1237d303d13772577c3710c78d36bdbc033624cf573556e60734de496e3492421531a42c8530fc0a65300bb48d2df79acc29dc83d429a690f628c4cd60283a504827840fa4264a3abc25d654d524473c8b23e92d1222b86d202296b352214edd5b20f3722e20b77d9a204bdfba2036b1611fcd579c1ed1d2411dc589511cd0b10b1ca4ec971c7a546d1babcbad1ae4f7611893101a18616c9c184622e617f95b8717c3e27b1744f8bf1649c0ef162f360d159fa3de15533426137aaed312bd91641099b59d0ee36f060e843d1c0bcfb3fa0a9ecd7d0a5dc22c099f792207bc6fe0063c769705ba8dbd055e384905474521048a0094017c4729
  | 5, 1 => 0x7574e02774e0ff2c7401615073b9b9097396b52f73721cde6f67ea6d6d66356b6cf1c0006c1b37e26bc3a51f6ab1afda69ecb02e6941fb8367586dc666403af365f5d8aa6523518a6387554e623f047b610b1df95fde8e305de0780e5cbf688d5ae899af5a292fbd59d395c759d3008959b2861c5955229858f6f5f958e66ead56a69396551926d75353a0c45336ed4750cdcb395068b8e24fe35e794d48131d4ae0a75d49c9c9c04903dcf04874dd87476bbd4746525c35453e014f4539d01c439435474341a9c042f1c36242d6faaf42b779a340f3505240a1608b405ec65a3f7c7d953f3273a83f2873eb3cd1f4983b6273ae3b4e72f73ad7736a3aa97297
  | 5, 2 => 0xba654efcb87b05cbb857bf9db84643d7b4a06d8eb39b1e46b31a8264b2b29e6bb21dcdabb0be6417b001c01baf298a6eaf201119ac33a785ac2d5707aa299276a9bfb541a9aa32d3a726719fa3695c0ca356a668a3257e1da2537e7ba0735e8da04b2e569ff004f49f67d5a69e762ea49e04e86b9dec93dc9c1aaf089ba8fab59b30cebe9a7514339a1c58ff9a0096fe9963f92d96a0d51a94d0e99e918964198f8bfb7a8d8cc4d58a80a9f989f52c5d89e60579899a257688a8335485c21732848c62798457318c833de7848151d94b7f62ae3e7c2f9e497c0eaaa97beac8e07b8db51e7b3beeb77aebbb247ad4175c7a85129f78273a1d772b5a887697c9e1
  | 5, 3 => 0xff4f2a3ffcd15abbfaba4034fa36940cfa0d8de0f8001501f7bb476cf5e74d7af5d1c538f4b41101f1f43b70f1e4fc05f1269b67ef37139bef15086aed34596be92cbd18e7f88e08e6f71c21e6793b20e5600966e52fb7b2e4584c8ee23c1280e05dd706dd1236cddc8475c3dbebf3a3d9a72ec7d95a67d1d7efb32bd7b30ce6d7ab2662d71900e9d682907ad4dcdc2ed39d7843d16b37a1d0ca6876caa0f797c9f040a6c9810596c94805a8c82bb05dc686cd7bc53314acc4fa1f48c4cbd5a4c49569f0c1d94c5fc1220bcac0a963fbc002d2d7be0a9e18bdf658b3bd199d0fbce2dcf9bb0a6851
  | 6, 0 => 0xc60dcf80c4cf80c0bb0f9310b83676e0b6f45300b5ff3c60b2da7450b2c8ce60b130d7b0b030f4d0ab8b2690aa0caca0a7677f50a3c184c0a23fa7409c3968809bd51ef09a18f54097689a8096f2a9009695d40092be94c09199978090e3a0808ec87f508e9d980078c60020755437f0725e9590715437d06f9696606cffa2206aebb28062f621c061880160609e286059d0d04059a4569058e95d3051a6ec9050bb04c04f4bb1404dbb864049f4c590479bbe103b2369003abb2f003476202033a2c8702f83cf202c1685702a27623029aef9e026249d2025f726902470b1b01dadaa5011daf4c00f5a3d200f4e623006fb9d3005c494f00410b79000db973
  | 6, 1 => 0x17dbb70317d7249017b77a5217784be41734bd56172c7aae1729918f1716dbeb1701656116d8a81c16bd508a16a2327f168e1652168bc85d1606144c15f022ce15d224f715cb87a41596d48d158c470e153ed91e153802db14e9ea9b149b001d1461e8b51413d60813e0e2a713d2e8e6133c08ef1317dd2b130a5a89130021e312c3605312b8ab4112a1148012331668119ab583118f0426118ef5151130ac841114cdbb10bb7651106e7040102d8cd3101fadf4101b64b60fe4d9d00fc7e3a30ea022dc0e7e15130e67dc250e6529c60e5a6c600e33761d0dfb96ef0dfa79ea0d95321f0d60c6780d3a898b0cd896110c9d1f690c903f7b0c8e3a800c82609c
  | 6, 2 => 0x2609324125f8c654257ac9562578e98e24fedf5924f54ac32470feae243e5010243d9f3623f7073723e951ae23e92d1223853347237418ee231de27b22c7351322bf88ab22abccfc226185a3225a2cd4213bddeb2129b3ab2107e3b320dfc24720d5dea920d0237020c965fa20b8602f20b0f0eb2089ff20206bd0131fcbb06f1fa432931f9547f51f7d5bab1f59336e1f38fc891f05df5c1e7359ed1d9063f91d0d17841c9d2ee21c53915b1c32bad41bbbe6161bbaa2fd1b7eaebf1b42de9e1b1700c91b1472091ac6e6c71ac6cf551a8e01df1a0dc40d1a04d97919ba301a196425da194bc9ce1921f28d18f811bf18e3fb0a18d063f718861c9e18787ffd
  | 6, 3 => 0x2f7e6ae62f4f90262f48cad42f1abea52efbd9642ef7eddb2eedfa852ee3da242ede098d2eb937762eb682a02ea5cf562ea523322e8bb09f2e2fd76d2e04ce452df877932dedc9542dda81f02dc4bab32d8de92d2d532f0b2d2875092d21c43f2d20bdd92cf085992cd1b9692cb3ea3b2cae25c92ca069f22c7dc05e2c2026e82c119b4b2baf6f8f2b6fa1512b3e6d342b08f8cc2ab98c602aa7e8212a892cd02a14d0f72a04bc7c2a023a7d29af2b6429a78cc4298b3ec3298727e32941072c29319d852915dc1828c73e982882d9902871a384286aeb79285f16652844d6392771e46a275f05d4275b976e275a769026d0c803269608f92652709a262a32f4
  | 6, 4 => 0x3bc90ad43bbf524e3bb70d6b3ba5ac113b5624293b33d6c03accd4263a4fc2063a2d6c6239fe26b439d8ed3c39d38ebc39b42d8c39979cd9396f572d39359c5e38fe702438eb527838d58864378be4b4376ecd623767fbde371111673702e44236fd2d443681559c3678c0eb3618de163609387935ae36f1357d35e535099e5634f524f934a771a73492603134886bc3347cfb7f3459b8a2344f47aa3419952533da662c33ce13433373c40f33422da533193e9a33102ecf33021c4532fa2f9532ecdd7e3294f0e032528c05324417603228b42331b68e36318b16ac3122199e312099a0310201f930d5282030d5072130be0b31308c42f82fea76652fe4bfe2
  | 6, 5 => 0x47c4887e47854aa1470853b246f1b31146df279b46deec34469949b5469461624667fca04663e3a0462c462e45fd956445fd86b045bb461c45a7f598459774c24493ef31440f588d4408d56743f503904387c0ef4365b3a9434ae4ce43110caa42fbf37742b779a3429e73194270b5be425ac01042487af7424539a741b54809418c58194183d887417b5a1f412c1b384113406d410d769640c148fc40544e8c3fed8a9b3fb8a6af3f90cfd33f8bf5c03f8054793f74539f3f60ec983f5ea61f3f5a7a383f545ac33f509ee43f086e6d3e277fff3e0fc03d3de30fa13daf73bc3d9f5ecf3d946b583d60158c3d4f2d143d4ae0313d254e653d12016d3cc6fe43
  | 6, 6 => 0x536b8d0a536a15075354fc3553466db853220f1b5314eaf652d528d052a76823528d58f7518d110e5160844350b19406505beeb35059633d501f9e514fe59dba4fc71f074f8c57c24f7599534f5dd3104f08c8964f050fd04ecc8e064e7855394e3a55cd4e1ee9d24e1717654dd3ad484d95e5bb4d86bbea4d5f0a034d41414a4d2f3d364cd5ea514c9307444c7b14224c760f734c7463374c5820f84c51dc5f4bd15be94bb8d2fa4b83735c4b77d19c4b226b904b222bf34b1abe0b4aee73794a95df4149e579ed49e3bfbd49dd9ff449dada4749773bc249697f424910933d48e3fc0e4856da1d4854372b48339399482de2cd482bd0f54827cfeb47d1bb1b
  | 6, 7 => 0x5fbac6fd5f9873855f8fd8ef5f871fd25f61952c5f4c3dc55f147ca25f088d3a5ed6fb2f5e22a7545e1bc49c5deb71af5d764ec55d5020ad5cf078975cb9d00b5c9b90375c795cd55c1f443a5baef06d5b94eaad5b8e88025b8707c45b54c91f5b5310a45afe18b25abaaca25aa5f5965a7e77445a377c5459ee392f59c84b70599cddcb58bb889f587b763f5875705b580cae7957f2a50657c2fb835793daab578012d05702a7c256e2168556d32b8f56a79b6e56488c3a56294e625618ad1555914c4d557f4cd9551926d754fdc76d54c822a954b88b5354a96c0954a16d3c548d14555485444a5436a7615431c00f53ad163d53a9644a53981baa538c2b2c
  | 6, 8 => 0x6df7e42c6def4db26d9d833c6d7e78d66d547e0c6d0792ab6cfb7a1c6cf0bd596cbe1d396c5a37056c3a90ed6be9fecc6bab48676b70d1e96b69624d6b4207c06b26b6e96afad9146a082914694217cf6909bb4668716f4068694d9c684cb17468410b2c6816246d67e2aac667dc655267c13f6967c080b767a71cda6786b84767757f6167301ae5672edba167223c0667044c4c66ef807f66c9726066a873e665efd78965946a04658f435665088ed264982c95646959a1641cd74363ff453e63fb6a7f63c1a14a63af236863939f33630aea4562bb107162a39a81627050f962434f5b61ee04f661ca4008616f43b0607744386043727f5ff039eb5fd7d1ae
  | 6, 9 => 0x7b5e52fc7b4614867b334ca57b1850c47aebbb247aea77727ada8ab6796534da795acc8c792903cc791205e278effb007819d38577dc326977cf1a8077ae3ab077abf413779796097722a4c776f0de3376d6e321767418c6765bc18076461d727635a00a762f5b717613d46a75aa44ea7574e027752cfb2e750d73c97433024e742bed3c73fa28f273c2aaeb73bcfd3f73b9b9097365dcea734eaa0d731a9a37727718da7239d99b72365fa8722d71c6721c743171b0febb718d4b85718aa31d7166cf87714b8ec8711dc56670d8df6c70845488705b5d9f6f6ab9496f54c88d6f33ffbf6f29bf656eec198d6ec911ee6ec7a3626eb5165c6eaf5c196ea4ed21
  | 6, 10 => 0x87a6b2428787f0328786f1f7877779c38769f32f876480d38759f0be875324e1874f92698700014386e19d5e86be95e9868f8bfa8679f841867726a186645a1a85cba36285a0b9708549b78484c748c5845d1c668436e17f833df903833bbae28322b4fa83223ce882cc3d9e82bd6975829ec1d681dd85f481b591e2815ba2a3814662f3808e9728801de45e7fe516d97fa0b5d97f85d4067f78cf077f78c21c7f2587b17f1be8777eeb32617ee15e677e76e5cd7e4b07f87e22428f7e1df7af7e1a8a567e16e3887e0e6b537dd13d877db173387d9546aa7d7b98ca7d4bf7b77cea112d7ccb503d7c9b17a77c764baa7c6664907bf0b2df7be6d9367b8db51e
  | 6, 11 => 0x9452dc4b943bd39a94062d5194052b0e93f91dd7931c4d0792e04bde92cc7f6e9285e5eb9276bd1592409e4992104c389207d7489161e4a791309f3490bd0663907c378a906837b8903fc31f8fcd3fb08fc3c7a68f8b6d4f8f69ddde8f5bfeff8f4fefe28f4bbe618f2520898f24e6ba8edfb84f8ed220d88e8c53638e667c0d8e5d90ed8e323b688e139f798de04c348dce939b8dacf6f48cb96a8e8cb45be18cad401e8ca14df68bddfc858ba51dad8b9917d08b8d04f68b7b765e8b31c58e8ae09a9f8ad1c8448aafa50e8aa44b2d8a57b15c8a37c65d8a1fecb889ef6b9089528b67894190bc888da4be8826fc3987fdd03087ec230287c0994387be0786
  | 6, 12 => 0x9f19428c9ef130509ed1e5489e9584799e9410ef9e93ebe99e50c7249dc05c9f9daae7359da5b6f69d5bd3fb9d3a1ad89d19f8919ce2f3a29ce0c3739cbb54e09c70cc409c2309d29c068d939c01232b9bf3d47a9be41d5a9b9023199b6964389ab78fed9a354f1a99fe818999f7365899d7582f99331f9b992b58e7992721c299013a6898ff0c1898869c769869403b982e64fb97f029a397ef087e97d51f3197cc960797aa9cac97aa213c97885ff9977b024e973a389a96d93d1e96c4ed5d969aeb72968fc4e6968d4d5f96853bde9661aced9656e8d595daf82895d8122595ad99909544828995124e4f94f67b1894aba5ca94755e1f947453e6947358b6
  | 6, 13 => 0xa956412ea94c47f6a90befb3a8f6772ea8b61457a8a9a379a89bce41a8249059a8227ef3a7f31d99a7c07a6fa791e204a7853e24a7509ec7a7485cd8a65dd945a643f6c7a6290dd7a6172c05a603d2e3a5fe72d7a5def7aaa5cf7206a59b37c9a592a0a9a5859f09a56b8c1ea54be63aa54844d2a544f1d9a5449835a52ea6b7a508355ea4bb5533a4b0cd10a4877dfba3e19170a3b2e5d0a3a56a26a34731dba302af63a2ab9495a2a6f9a5a22b6a16a20ecd8ca1f7dfcba1f16defa1ad34e4a195b11ca1895910a177f149a09b5bdda0908dfca06b55ada05ab451a0444418a00c6856a00104ae9ff394c19fb7f0179f77feb79f42a6089f307a4a9f22e88e
  | 6, 14 => 0xb5995d73b58b0cf8b5829cbfb55680a4b547b62ab54316feb4f19ce0b4d0d4a4b4b7aa29b4a90c7cb47be621b4531b23b3c54e5cb3b98412b327b0fbb3216c62b2f25cf9b2e6b6d7b2e06130b272d876b250cd45b2292e89b216e083b1fba0bfb0cf1072b0c767b7b09b89e2b06a21d7b04d71d7b047d02fb0433de6b02268afaffa5c3caf841f0aaf67b2c4af647c31af1cc9bcaf1123ebaf0582c4ae932178ae82a0e2ae6872d8ae3a84e1ae1bf85dae18ff3dadec5093ad47653cacec63f0acdcb081aca9b064ac8a86ebac68c860ac6881f3abf06f62abdcca1cabd053b4ab97ffd0ab7678f2ab5c77f3aa801c35aa361d56a9a1d10aa99b1436a95dfcd0
  | 6, 15 => 0xc0144dd9bfb8773abfa41077bf7d00d2bf74ae55bf347acebed0d301becf96e5beac6245be90abcebe3add0dbe2c7e6ebd7258e7bd36fb7cbd199d0fbc770081bbfe358ebbba8ac3bb7bd45ebb69340dbb44492bbb3965d3bb32498dbb184a9abaf70c47baefd317bae1c4e0bad4da24babfe656ba76f2e7ba45b6caba28ff78b9fdf650b9b6422fb9a146b8b95f4ed5b9349dd0b92f756db90d8a13b8ecb18cb889a36bb8554800b84aaf1eb7dce78eb7d6b31fb78a5a9db779d24ab751bcc3b72e368bb729b85fb71329c5b6fb2445b6d68742b6be7634b69c41a7b666148cb64ecbd7b64d6272b6440bf6b6299b57b62155b5b60f4becb5e82352b5e21e76
  | 6, 16 => 0xd0418164d019b0f6cf652c61cf0b78d5cedb421ece5c094bce46f256ce3e5449cde202f0cdda9258ccc7daa6cc4ce26fcc36f087cc2c536acc1d4d7bcbf97cfbcb607cf8cabb86a9ca859a7cca4b1c80c9f99698c9ee7b2ec93da2f3c9202368c8c7f02dc8b75089c8addb16c8369cb3c82773f0c8205f4fc80b3ca5c6f52ab0c6dd9355c6c817b7c6a389f1c636e5bbc5b744d4c59c2c97c5899ec0c51d0fe7c4f5f2d7c4d20e6dc4745ea1c453a13bc447b8d1c3e38b32c3c00863c3b2af59c3679292c2ec8cdec2b2fc6bc2add679c2932210c285e459c2472df4c2384482c237d00fc1ebf1e0c1dbbeefc14cdf44c10cbeb8c0affaeec0451245c028cb77
  | 6, 17 => 0xdc35740bdc310002dc2c6374dc1c3838dbd11a6cdafe40d3daf2339cdaae2c45daa66136da650bedda60bae0da5cb472da25af70da1cea69da015141d9d05035d8acd2f2d89de169d872797ad85d0165d845f1ead7de5cbdd7ab2662d7970f9bd75ee2add7587c29d750f462d740303ad72b3df0d71e06b3d6f8f5dad6d35949d670e039d613fb65d5cbf18fd5bfd6fdd594088dd5121a8ad4e47617d46d133fd45bc4b7d459f8ffd4561e78d3b6fe4ed368f2a2d33b7be2d32d9d03d317dc6dd3152e0bd3008092d2f8748cd2f3ad55d2cf8a77d2cc6b2ad2aff72ad2a43792d21f33e1d1f5fd8cd1efb8f3d18bc9e0d17e5bfed124d3b9d0cfc5e7d04f7200
  | 6, 18 => 0xea8fcd63ea63c2d5ea1efe0ce9e0e609e955d96fe91219b0e8f801fbe8f44b30e8b769b1e86c8ff0e8027d18e7c0b59ae75945f8e6f740bde6f71c21e6debce7e6db0d79e648521fe6118099e5f9b6a9e5ce7bdae57e2587e51de1e1e504ee61e4fe5636e4bec86ce45d2c07e4484145e3ef42d0e358b1ffe2ee6b60e267227de2536edfe220b607e21cc653e1d43bc4e1808a81e11a1893e115da1be0e9fe0ce0531b53e02c3560e00c75e6dff821dddfd9a991dfafb75ddf9a729cdf9560dedf14fdabdee79088dee29a6ade8a7e44de888ed0de825f8bde5cb0fbde23d5bfde1f9362ddb7dd18dd864c18dd5815a7dd559b4edd1bb31cdcbf3510dc5bf6d5
  | 6, 19 => 0xf65cc66ef6260c95f5facc8df59108abf58017a1f54dde90f4d8c155f4bdf7a6f49905bbf48bd63cf4591915f4535bf8f437cf40f3f28c4ff3cbfa40f3b21d67f39bac49f39a7a63f38cf389f33b5fd0f3091ba5f3041da1f2854adff274adb0f249a559f1a2980af19c1e9ff1820790f171c893f15a4793f0d2a9c2f0b2dda9f0b082cdf0556ec8f0010e1befeb934aef5b4d9fef2e15f7eef2b7b5eed9bf3beecd3c85ee8f1728ee570c71ee1641d6edec1b9cedb16f8feda7101fed8d35c2ed0f093ded0092ebecd85786ecc10942ecb027a2ec677269ec4c4dc8ec2d7d95ec127b2aec0222b2ec00923bebd7198aeb7ec531eb264fd7eabd810beaa5cad7
  | 6, 20 => 0xffde5bbbffc6e326ffa50d5cff55b127ff4e5dc5ff27467ffe133845fd62561afd363ec0fcaa882bfc3cf275fc17ccb3fc0ac370fc07c004fbefb591fbe3fc56fb876c1dfb7b9f67fb3bf322fb192d73fae41f82faae1c57fa7d76fdfa1f0076f9efe375f9afb2a4f9a7b435f98da5f1f9824cb5f96feb04f968cab8f90d3ad3f8ce93eef8a43307f87cadc2f85b44fef7db9c7ff74c3499f737c7bbf7233204f71746d7f6adfee5f6ad0e12f69357a9f66bd375f6655c2c
  | 7, 0 => 0x11761aa810d1aa9610c280c5103ead2a102d8cd31004221f0f5c5cfb0edd17080ea68d810e7dd0190df078900db675560d9cbe430d61f2fb0d590e3f0d52c9a60d4d98860cf91d9f0cea20e10cb3009d0cabde0a0c867e660c2cfbb60c2895160bb2ffb10b41c7720ab8b26f0ab7b9ae0aa9dacf0878675807d82e3c07bd347d07af559e0754ea15075140fd06c7654b0663442506556796065223ce062f621c05c61dd605ad2f340590310f05869eb103f1b952036df1500360127103476202033a727c02d5abde0296f579024a740d023f103c023c952e01a603fb0198251c0188fb4b0129b75501013f3600f5a3d200dd496a0086a50c0027347900103def
  | 7, 1 => 0x21051f302081cc61204aaf2d203e530f203cd04e1fe1a1ed1fe039d21fd3d3851fb72b911f608b651ebb13731eb3facb1e8eec381e739d441e3d0e221e08e1531d989e101d81c57f1d73f5661d29fe0a1c1ffead1be841c11bbbe6161b78d4bc1b70b1901b61a0cd1b52f3321b325a461a974b451a90e4691a45ab1d1a4058c319f6cf4619f08aad19e3604919b1d448198eb5651979f417196672e1191531f41881f6861859a2b4181aa94117d7cb9517d07b0017a8202616e8db1816d8a81c16b50ee91606144c15f86a80154f3eab1415063f13b5da6d136d10ac135211a21317dd2b130748e512ae5da3129997eb12798028124e263511d748061187183a
  | 7, 2 => 0x3264f1943243d5cd317141fd315024ba31381b07312ff1d830ccd1eb3055c0a6302ca7772fc976f62fa1c82a2f7655c82f1d68d52f1362052eedfa852ee51d392edbd6b52e9e70832de85b922daad2e42d90db782d014b912cf3c0ef2cf085992cae27f22ca821632c9946a22b0f56702a6cf0712a6bdfc02a5e00e12a5175e429f0f184292df8a128a4a83e2882e2b227c166d52774c46026e36c2426d2458e26d0c80326aa53c326a4b5bf26488ebe26396ad4262d41fb261c309d258a6ea42509c4b824cb7b2924a7e76c2429651523fe6fae23afce9223a7fde6233e51982310763b22daf26b22c73513225c73322219ec0a21e9d24d21a5f9682179389d
  | 7, 3 => 0x45c07cca457c5ed145179a8f43ba6a0a43b9f0a343b4257143a9f8484305883642b779a342815d8a425327d74223bdb94215deda4214fad141d9fb7841d622d3405c8f3d3f49363a3ee6de3d3e9c5ebb3dff89d03df1aaf13d8620523d18fbc93d0124c93cedcf813cd7d7c23c9f3cdf3c9dc2fe3c8fe41f3c3d49423c38e0113bf3e2703bd0b7833bc2d8a43b5624293b3c318a3afd7b253acd3e823a8b9b213a861c993a67daad3a47663439de879e3950034038d7670538c98826387c2216375fd1e83732d33a3724f45b36e4026d366fa272363c57f4359aee6d358e7c13357bcd57355e29ce3518dab1347a700934746a9f34744a7f32ba82ac3294bf40
  | 7, 4 => 0x54ca011a54b47b9853b7a8b5531915d1530ec13f52e996fb52acbe7d52942b72528ca2425275541c523dc21151e81d5151d2062b516924ff514f645451099cc651007c3a50c9577f50a706e85038abd6500139404fb2394c4f9b055d4f943bc44f717d1d4f624ff44e79bd534e7327324e0e9fc94e00c0ea4de27c5e4d2b306b4d20539e4d0476064c173de94bf147df4bc969994bb8974e4bb13b214b7591cb4b6e21e64b62f61f4b40518f4b0c2c394b02825d4afc5e1e4ac0774d4a6707154a5928364a135e0d49e125c6499cfa0a499b08ca49226c8f49148db048fa38cc484e6acf48030da0475141bb46e1bded46e149a2465e79d545fcfa1d45f6b584
  | 7, 5 => 0x6a2a46cf6a0139de69f5d2f96996549e692e70ee688d1b55683fb3fc67fe34f567f1c0d367425c616733942567044c4c66fb4c91668c47706659a12a651506a464ffcc4e64789948645092fc6449b75d633635116292bf226284e0436129ea2960d1580460c016456001a2b65f492eb65f2a63495eebace45edafec85ec6f1c75ec2fe405e1657ce5e06e6065dc82fa15d3a46645ca9ea895c9fbd605c0095e65ba915895b4388f85b2acd595aa8a6b95a73054d5a437adf59f223e559e9c31b5992adb058a5f17758905d13584e132a581fb8f657c3519856fffaeb56da22f0568ff7f1567ee6cd5640306856240dff55df5df855bb43f755ab6c46558b8750
  | 7, 6 => 0x79a4d76c798a90b2794717d67946d3e378493a7f77d135d07770373f7733bc5377211a3f76fcab1e76f0de3376eecc3f76db0b2e76bdf4b976b015da766385db765bc18075a74bbc7521769374f2245d749b9886745a681c73a4532b7341d2fd7333c42e72e03d9b72b28339727daf3d7268845a721cd83371fb25a271be65bd714a8ba9711dc566710f96de70cdf07470c4152b707cee8d6fa6c90d6f6c29a26f3b46226ebe77696eba99336e9f1e276e834bca6e8018a76e38e6f66e211e536e1ad9ba6db8095f6d2657c06cd622c66bc490ee6ba5cda96b89f08a6b7c11ab6b58c0516b1be3666af785736ababa2c6a5eea176a510b386a4fc62d6a4f2208
  | 7, 7 => 0x89beef4c89605ac289528b6788edfe0d88ede028886bb2a587ca80ca877c8a9f877910e2876b3203872610b887109ed286c59ece867726a18651842c862851b985f48e9f85e99b5485ba4fb98562e87285210b03851cbe168492c7cd83d9bb2c83c5bc52838341f483833bd7834a6d9383223ce8830766bf82d3eb99828511a4827639728110235580cc6bd47fc0036d7fbd20fa7f97da8d7f27d8097f1e55b07ecd8d627ebbf6017e8559377dd5c4a57db1e1917db173387dad4e397d776c2f7d356db97d33ff317bf0d3337b4614867b2b17a17b25f4ae7ae97d0f7ac854af7ab597257ab2c9087aa157477a9f7e307a36eb407a2bfc5d79e15a2879c9043d
  | 7, 8 => 0x992c679098d83969984899db97251c989721f5ed9713ecb19710a45897012b8496e3fc3596ac2a8596a4b77d9690ba6e963c456d9603a49895fe78aa95a996be956125c69502be169497281e944ede0093f42b8d9396353d93602c4693527dd59351acbb934043b892ef453392b08ece929a9c84928df768928cbda5927d83849272b1cc925c0be491b98d12917fb21d9117715e91015b8b908ca44490683b3e9037c66b9011f58290061e318f9d1d5f8f78512d8f6680978f46f2108eb06ba68e7679718e27eed18e2374cd8e21c9a38d7f04bb8d6fdaea8d6bb4b28d3d413a8bedc1998b8fda438b308e208a8bfac78a81f0ca8a4b2c048a18c2888a0d10dd
  | 7, 9 => 0xaebd223cae8d3699ae064aa9adb1ddd6adab993dad85a160ad6e1b08ad1a90a7acac34b6ac23afedabccfb90aac3cccfaabfa2cbaab758a5aab1140caa950ad3aa8df529aa87c3f1aa75a9a3aa3f12b1aa2867c5aa21bb6da9cb11c2a98c5b5da9647ee6a95dfcd0a77ce252a71939e5a70b5b06a62fa927a623790ea5e4c2a9a5cabbeaa5449835a499e38aa3f2435da36baaf7a35f8a0fa302d5f5a2f4f716a1ece18ca1c6431fa1662bafa141bf77a0c045e2a0b26703a07b39919eab30d29e58572e9e14ab229de9f1209d61744b9d42bc1d9d3508f49d2d50bb9c48de239c36144f9c27c3cd9bfcd7929b1dd7b09aec1f2b9ab47d5a9ab0be7a9985b807
  | 7, 10 => 0xc110cb7dc1043454bf46884bbf4172fabef5700abef4bb49bef1afedbee065e9beb2f988be5773c2be3a5d4dbe3418b4be2639d5be1fe45dbddd5bacbd5c9ba0bd2744b8bcb2dff7bca06181bc18011abc008a33bb3f92c0bab08b31ba9e7ab4ba708858ba477786ba45dd7fb9782853b85c2f59b84d21e0b837fe7bb7a3f583b7610a65b6edc245b69fded2b67cc233b644e080b5c9ec3db59a84ddb5195244b4e46fecb37ef559b354b256b315333eb272f2abb253eee6b23cd636b2313513b22e7c90b20ffb62b18cc501b12375bdb0f51e5bb0ec7e1fb0e1dcffb080f6ebb01ae1b0b00d02d1afebec7daf95e2ffaf935789aef43dc2aee65ee3aec64c0e
  | 7, 11 => 0xd4e47617d43f7d82d3fa20bfd38eac86d355d4ffd2f3ad55d229a3e5d1d3f658d0dd3a20d0317033d010ef66cfe713d2cfca0951cf6e15b1cef7401acea2794cce8cc780ce412b29ce37cadccdfcbe79cdd2d617cda803e7cd5fbf4fcc0d7bc5cbfcbae9cb46a5f8cb26fa2bcb191b4ccae6d7d7ca5eb5a5c9e24337c9d88a90c9d46458c9c8daa4c9a019fdc8e779a6c8d8951dc876c3bec7ad77bcc7a9b843c7a3ca76c6ea46f2c689fa79c62ad07cc5e58a67c5d3e588c5690328c52f7576c4eae2e7c4d4624bc4b067c5c4ac2c82c3c00863c37f968dc344d355c33e8ebcc31b6fd9c30bd3fac278c27bc21dcfbbc1c6e06ec1c5a5bec1c16a74c150c440
  | 7, 12 => 0xe4625a30e4402e8ee3d420a8e32cc12de2f7dbbfe2e94854e25263cde21fca1de1c2a466e1283faae0f9adf8e0f3695fe0d9cf49e088d44de04a17a1dfdba1afdfb32b5bdf97e726df91a28ddf7fbf91df71e0b2df41afa0decadbabdec9aaa0dec49712de7f8515de1b0bb2dddb9cecdd547ea2dd4db3aadd0995b1dc7f26aadc240579dbeeb34ddbcb4694daf5c757da8fa153da8008d2da7890dfda52a0c6da2cf762da26b2c9da0af02ed9eccea3d9e7a089d9ab6bc3d988b69cd96359b3d958a3e4d90de9d2d8e7dfa1d8dd76c6d8cf7726d89de169d8653959d86400d8d863d13ed6890d25d64007d5d62ad27fd5d13c99d58853add56748abd4fb6d4f
  | 7, 13 => 0xf762f14af725d631f6e94291f637ead7f50771aef3b71d31f39bac49f2e571d9f20a7ebff1c7ebb4f1c31697f1c1f496f17a65ebf171c893f15afe71f14d1f92f109fd47f108c3f1f0f10dbef0c2900ff05def26f053c1fdefeaeca8efdef6d4ef7de2e4eec76f65eeae7dabeeab662cee6bbfe2edf5513bede64ad6ed74eae1ed71b5aeed5ae6a4ed5612f6ec848404ec164c1eebb77889eaf7dac4ea9e47f9ea782c38ea39f55de9f23fa9e9d3bc26e9b38944e8f19d4fe8be280be8b54ab1e8b03ee3e878be20e812cbdfe7a75556e73f702ce7283c3de7199440e606f433e5d4dd4ce5c6ac76e5b5122de51de1e1e5179d48e49194eae48a3599e4763a0b
  | 7, 14 => 0xffcceadcffa13466ff99e188ff5a28fefef2bd64fe091979fdf560cffd875a02fd797b23fd75d7f8fd16ed71fceb370cfce2758bfcb0a9dbfc7cb7dbfc60d880fc3e0176fbfbc2c8fbefb591fb7259a6fb113ac2fabc44b5faa130d0fa6ea56dfa4dc81bf9824cb5f9092d95f9091127f8b72109f80ff336f80fe67ff7fbcecd
  | 8, 0 => 0xdd9de376c3d681efc2afde01b6be7634a6563cc39b34b1218ab84b5d8a7994f87f4590c97e1a8a56764e5f615cde0cce55df5df851bb2a0f5059633d4f8c57c24c93074442b779a334064f6c1e7359ed1b78d4bc1561a43a1142fa4105169eb0
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x7110935508400
  | 3, 0 => 0x71109355084007110935508400001844250830071109355084007110935508400
  | 4, 0 => 0x4350c202001844350c302000000004110a000002510420471109355084000018442508300000994504030071109355084000000035484200000d94504030000184425083007110935508400000000000001071109355084000000051109200001093550830071109355084000000000084107000000004110a7110935508400000000004110a001093550830100000000000100000010440200711093550840000000000c5109711093550840000184425083000000000084107000003404120a00000251042040000042508201
  | 4, 1 => 0x109355083007110935508400
  | 5, 0 => 0x600184425003000000000000000000000004110a001844250030000000510c9201000000000000300000000000040000000000003000000000000c0018442508300000000000000d000000000000a000001510920100000000c91060000000000003000000000000600109355083000000000000005000000000000500000001091010000000109101001844350c302000000004c10a00000001091010018121040302000000000000d00000058402000000000041100000000000000900000000401030000051109200
  | 5, 1 => 0x100000000000030000000000006000000010410400000000000060000000000006000000010d105000000000000c000000000000300109355083000000000109101000000010410400000000000010018121040302000000000000600000354842000000000104104000000000000700000000000080018121040302000000000000a001093550830000000354842000000000000010000000008410500000000000010000000000001000000004010000000001091000000025500201000000010c102000000010d105
  | 5, 2 => 0x510c9201000000000210000000255002010010935508301000000000000c0010935508300000000000000600000355002010000000000001000000000000a00000000000100000000000000000000000001000000000000050009945040300000000010d10500000511092000000000085106000000000a100000000000001000000000000000000000000000001844350c302000000000000d000000010d105000d9450403000018121040302001844350c302000000000000c000000008410500000001041040010935508301
  | 5, 3 => 0x510c92000000000000003001812104030200000450c1200000000000000d0000040500201000000000000300000000000040000045440200000002544020000109355083000000000000010000004108420400184425083000010935508301000000000000c000000010410400184425083000000000012100000000008410500000000401000009945040300000000000000300000000c4102000000008510600000000000010000042508200000d9450403000000000000006000000000000000184425083000000000000006
  | 5, 4 => 0x10d1050000000040103000000010d10500000000000010000000000000000000010d10500000000000070000051109200000000000000a0000015002201000000000000600000000c81070000045040200000000000000700000000000030000015109201000000010910100000510c920100000000000060000035508200000000000000700000000000020010935508300000000010c10200000000000020018442508300000005110920000000000000060000040500200000000000000a00000400402020000000084107
  | 5, 5 => 0x109355083000000000084107000000010d105000005010d200000000010410400000000000070000000000009000000000000100000000000100018442508300000000008410700000001091000000000000000000000000000000000450c12010000000040103001844350c3020010935508300000000004110a0000000100103000002510420400000000c9100001844250830000184425083000000000000004000000001210000000511092000010935508300000000000000d0010935508301000000000000a0000000084105
  | 5, 6 => 0x1000000000c910100000000841050018043504300000000000001000000000c9101000000000000200000354842000000035500201000000000000600000001041040000000109101000000000000a0000025500201000000010d105000005110d2020000000000000000000004110a00000000000050000035508201000000000000c000000000000a000003550020100000000000040000000000007000000000000d000000000000400000001041040000000084105000004548420000000000c91060000000000005
  | 5, 7 => 0x4110a00000000000020000000000001001844250830000000001041040010935508300000000000000500000000000000000000000007000001500220100000000000000000000084107000000000000a000000000000d001844250830000000150c920100000000841050010935508300000003550820000000000c510900184425083000000000104104000000000000d000000010910100000000000000000000000000
  | 6, 0 => 0x841050000000002100000005010d2000000000000004000000000000b0000000084105000000000000800000454c4202000000000000500000254402000000045484200000000000000800000510812000000000000011000000000000700000000121010000000000006000000000000600000304c0202000000000000500000510c1200000000010d10500000000c810200000000000060000000000005000003550820000000001011010000000000002000000000000500000000841020000000002101000004350c202
  | 6, 1 => 0xc410200000001041040000000100102000000000000c0000000100102000000000000300000000c810700000000c9101000000000000600000000c8107000000000000100000000000040000000012101000000500a2000000000000008000000000000600000000000080000040500200000000000000800000028062000000000000001000000000000d000000380a200000005210d2020000000100101000000000000c000002048020000000504842020000000000008000000000000600000000000060000000084105
  | 6, 2 => 0x4050020000000000000010000000000009000000004110100000511092010000000000010000000000000c0000000000006000000008410200000000000110000000000006000003548420000000000000080000000000006000000000000c000000000000000000450c120000000000021000000000081101000000000000500000000c9103000002104020200000000c010200000000000010000000000006000000008110100000000000030000000000002000000000000c000000010810400000000000070000000000005
  | 6, 3 => 0x5000003548020000000000c91000000000002100000000000210000000000c8102000000010010000000001041040000000012100000000010c1020000000000005000000000a10000000000000030000000002101000000000a100000000010d1010000051109200000000000000400000454842000000000000006000000000001000000000c910100000000c8104000000000000a00000000411010000000000002000000010110100000001001020000000000008000004540220000000000811010000000041101
  | 6, 4 => 0x400000254402000000000040103000000000000400000000000100000000000002000000000000200000000000100000000000010000000000e101000000000000700000425082000000000109100000000000000d000000000000d00000000000110000000000011000000000000300000510812000000000000006000003550820000000000c910100000000000060000002806200000000480e20000000000c41020000000000000000000000000d0000000100101000000000000a00000504842020000000000002
  | 6, 5 => 0x91101000000000000b000000008410500000354802010000000000008000005110d2020000000000006000000000000100000001001020000000002101000003548420000000000c91010000035508200000000000000400000000c910000000000000060000045040200000000000000a000000000001000000355082010000000000006000000000000a00000000c8102000000000210000000000000060000000000011000000000001000000454842000000000012101000000000000700000454402000000035504200
  | 6, 6 => 0x20000000000002000000000000700000000000070000000000007000000000000500000000c9101000004350c202000000000000a00000048062000000000000004000000480e20000000001091000000000000006000000000000700000000000060000000000004000000010d101000000000000a00000000000050000000100103000000008410200000425082000000000000005000000000000900000450c1201000000000000000000000000100000005412200000005110920100000000841040000000000004
  | 6, 7 => 0x104102000005110920100000000c910100000001001010000000084100000000010c10200000000121000000000041100000000000000400000355082000000000000003000000008510600000000061020000000040100000000010c102000000010010200000510c92000000051109201000001500220100000354842000000000000003000000008410800000000841040000000100102000005210d202000000000000600000000000060000051101200000000000000300000000d110100000425082000000000000008
  | 6, 8 => 0x61020000020480201000000000000100000000000000000000000006000000000000a0000020480201000000000000300000304c02020000051101200000005210d2020000000000008000000000000100000000000060000000041101000000000210000000000c9101000004250820100000038062000000000000006000000000000a000000000000500000000c9101000000000000100000454c420200000000401030000000100101000002500220200000000c9101000000000000600000001091010000051109200
  | 6, 9 => 0x91101000004050020000000000000050000000100100000000000000400000000401020000050109200000000480620000000304c02020000000084105000000000000600000000841070000000000001000000000000600000000c1101000000010910100000000000050000000000005000000000210100000000000010000000000005000000000000500000000c4102000000000000500000001001020000000002100000000000000600000450c12000000020480201000000004010000000000000060000000000000
  | 6, 10 => 0xc1101000000004010200000000841050000020480200000000000000300000000c1101000000004110100000450812000000000000000000000000000d0000000041101000000000000e00000000000060000035508200000000000000600000000000060000000000003000000000000800000000c81040000025402200000000010910000000354842000000000000010000000000000c000000000000c0000000040102000004504020000000000000070000051109200000000000000500000454842000000021040202
  | 6, 11 => 0x600000250022020000000000011000000000210100000000121010000000002100000000000e102000000000000d000001500220100000450c1200000000008410500000000021000000001802200000002110020200000038022000000000000004000000000001100000000000100000000000010000000000000c0000000000003000000000000c000003544020000000304c020200000000000040000000000000000000000000700000000000080000000000000000000010010200000450c1200000000000000a
  | 6, 12 => 0x405002000000000000007000000000000000000450c120100000500c920000000000000060000000109101000000000000400000000000010000000000001000000000000100000000000000000042508201000000000001100000058c920000000001011000000035508200000000000000c00000000000060000035480200000000000000a0000051109200000000000000400000405002000000025402200000000000000c000004250820000000000000080000000000011000000010010200000000000010000040500201
  | 6, 13 => 0x35484200000000001210000000425082010000040500201000000000000300000000d110100000000401030000000000002000000010410400000000c910100000000c1101000000000000c00000000c1101000000000000100000000c1101000000010d10100000000000080000000000001000000010010200000000000050000020480200000000000e102000000000000500000000000040000000104104000000008410200000000c910100000000000080000051109200000000010910100000504842020000005900200
  | 6, 14 => 0x8d106000000000000400000000000080000000000006000000000000700000510c9200000000000001000000000c810200000354842000000000000001000000000000d0000000000006000005110d2020000001802200000005010d200000000010910100000454c4202000000010d10100000000021000000000000001000000000000a0000000091101000000000000a000000000000c0000000000008000000000000600000000000080000000000006000000010910100000000c910000000000c9100000000010c102
  | 6, 15 => 0xe100000000000000500000511092000000045081200000000000000600000000c9101000000000000800000000841070000000000000000000010d10000000000c9101000003544020000000000851060000000000006000005110d2000000041100200000000000000600000000000030000020480200000005110920100000411002000000000000005000000590420000000210402020000000000004000000010c102000005010d2000000000000005000000000000600000510c120000000000000050000000000001
  | 6, 16 => 0x42508201000000010410400000000121020000000000005000000000000500000355082000000000000008000004350c202000000010d10500000000c9101000004250820000000450c120100000000000060000000000002000001500220100000000000080000000000004000000000000100000425082000000020480200000000000000c00000150022010000000109100000000000000600000000000060000025002202000000008110100000000c810200000354842000000045484200000000000000700000000c0102
  | 6, 17 => 0xd00000000000060000000000004000000000000500000000000000000035508200000004350c20200000000000060000000000002000000000000a000000010910100000000c41020000035484200000000000000d00000000c9100000000000000100000510c920100000000c9101000000000000600000000000060000000101101000000000e1000000000000008000005210d202000002500220200000355082000000000041101000000008410500000354842000000000000006000000010d105000000000000d
  | 6, 18 => 0x600000425082000000000000006000002540220000000001001020000000100102000000000000d00000000c0102000000000210100000354842000000000000006000000000000c000000000000b00000000c91000000000000001000000000a1010000000000005000003550020000000000000020000042500200000000000000b0000000006100000000010d1030000000000007000000000000600000000000070000000000006000000000000600000204802000000000000006000000000000c0000000000000
  | 6, 19 => 0x200000000c0102000000000000c00000000000000000000000005000002540220000000450c12000000050484202000005010d2000000000012101000000000610000000000c8108000000000000c000000000000400000000000020000020480200000000000e101000000000000600000000000060000000002100000000000000700000000c81040000051109200000000000000c000000000000a0000000000004000000010d101000000000000c0000000000003000000000000300000001001010000021040202
  | 6, 20 => 0x40000000100102000000000000600000450c920000000000c11010000000000006000000000000d000004548420000000000911010000032484200000000000000500000000c810200000510c920100000000c910100000000811010000000000005000000000000100000000000050000000000010000000000000c000000008110100000450c1200000000004110100000001091010000000040100000000590020000000000c910100000000000100000035484200000000000000600000510c92010000000000002
  | 6, 21 => 0x30000035484200000000000000d000000000000a00000000000000000000000003000004050020200000001041020000045040200000000000000600000001001020000000101101000000000000000000000000080000000002101000000008410200000001041040000000040100000000000000400000511092000000000000002000000000e1000000000000001000004050020000000000000050000035508200000000004010000000450c1201000000010d1000000035508200000000000000500000450c1201
  | 6, 22 => 0x50000000000004000005110d20200000450c12000000000100102000004050020200000000000070000000084102000000000000d000000000000d00000000c01020000045484200000000480a20000000000000080000000000010000000000000200000000c91000000000000000000000000e1020000020480200000000008110100000500c920000000000000060000000109101000000000210000000000000020000000109101000004050020100000510812000000000000001000005110d202000000000e100
  | 6, 23 => 0x5210d2020000000000008000000000000a00000000000080000000000005000000000000500000000000000000000000006000000001210100000000000070000040500200000000010810400000000000050000035480200000000010010200000001001020000015002201000000000000400000000841020000000085106000004548420000000000c910000000000c810400000000c8107000000010c1020000000000006000000000000400000001001020000000084105000000000a10100000000000050000000000003
  | 6, 24 => 0xb000000000000600000000000030000000000005000000000e10100000000c410200000000000070000000109100000003550820000000000000050000035500200000000000000700000000000040000003806200000000000000400000000000080000000000005000000008410200000000c11010000035500200000004250820000000000000050000000109101000004250820100000000000040000000000006000005110920000000450812000000040500200000000010d10500000510c92010000000000006
  | 6, 25 => 0x10000000000010000000000000500000000c810700000058402000000020480201000000010d10500000001001020000000000000000005010d2000000000000006000000000000a0000025002202000000008410500000000000000000025440200000000000000a000000000000400000000c9101000000000000500000058c9200000000480a200000000010010200000000c910100000000000000000000000003000000000000800000000c910100000000d1101000004110020000000000000080000000000005
  | 6, 26 => 0x35484200000005010d202000000000000d00000028062000000035484200000004350420000000000c410200000000811010000050109200000000008410200000000000050000000000004000000000000f000000000000800000000c1101000000000000d0000042508200000000004110a00000000000030000000000001000000010110100000001091010000040500202000000010910000000000061020000000109101000000000000c0000000000006000005110d200000000000000100000000000040000000000008
  | 6, 27 => 0x3550820000000000c9101000002104020200000000000080000000000000000000000000c000004250820000000204802000000000100101000000000000600000000841080000002802200000000380620000000450c1200000000000000c00000255002010000000000003000000590420000000000841040000000000001000000000000400000001041040000000000000000000000000a000002550420000000000c81020000000100102000003550020100000000000080000032484200000000000a10000000000d1101
  | 6, 28 => 0xc810200000000000080000000012101000000000210100000450c12010000000000008000000000210000000000000000000051109200000000010910100000000000060000040500200000000000210100000000000060000000000001000000000000500000000000000000000002101000000010910100000355042000000000084105000000000000300000450c1200000000000000600000000c01020000000100102000000000000600000405002010000000000005000000000610000000000000080000045484200
  | 6, 29 => 0x10d10100000000d11010000035508200000000009110100000001091010000000084105000000000000c00000000c0102000000000000600000058c9200000000000000400000000000060000000000005000000000000000000000c91010000000000004000000000000400000000c910100000000c1101000000000000d000004250820000000510c920100000001011010000000000005000000001210200000510c920100000000c9101000000000000d000000010c10200000450c120000000000000050000000100102
  | 6, 30 => 0x450c1200000000000000300000355082000000025500200000000584020000000000841050000000000007000002550020000000001091010000000000006000000000000000000028022000000000000002000000000000600000511092000000000040102000000000000500000000000020000040500200000000010d1010000000000006000000000000200000000000080000025504200000000010910100000000c8102000000000000600000000000040000000000000000000000000600000405002010000000000010
  | 6, 31 => 0x40000035508201000000000000200000511012000000000000002000000000000c0000000100102000003548420000000500c920000000000c81020000020480200000000001210000000425082000000000000003000000010910100000001081040000000000006000000010010200000450c1200000000000000800000000000050000000000003000000010910000000000000040000000000005000000000000c00000000000060000000104100000000000001000000000c9101000000000000400000450c9200
  | 6, 32 => 0x60000000000004000000000000200000000000010000000000006000000000000700000000000040000004806200000000000000c000000000000d00000000000080000000081101000000000000300000511092000000000006100000000000a1010000000000000000005110d202000000010c10200000511092000000000000005000004050020200000405002000000000000006000000000000d00000204802000000000000005000001500220100000510c92010000000000008000000000000600000000c8102
  | 6, 33 => 0x454c42020000000000005000000500a200000000010910100000000000040000050109200000000000000600000000041020000000100101000004350c2020000000002102000000000000800000450c12000000000000006000000010910100000000c4102000000000210100000001091010000045040200000000000000500000000000050000000109101000000008410500000250022020000035508200000000000000c00000000c1101000000000000a0000004802200000000000000500000000000050000045484200
  | 6, 34 => 0x4000003544020000000450c12020000000000004000000010d1050000021040202000000000000400000000c9101000000000000300000000000070000000084102000000000000800000511092000000000000004000000010d105000000000210200000000000010000000000005000000008410200000450c120000000000000060000000000010000000000000d000000000000e00000000000050000000000000000000000a10000000000c81020000000006100000000000000600000000000070000000000011
  | 6, 35 => 0x6000000000000a0000000000004000000000000c000000500a200000000000000800000000000050000000104104000000000a10000000000c1101000000000000500000000000000000000000007000000000000700000000411000000000000006000000004110a0000000000005000000480220000000000000000000035508201000000000000d000000000000200000000c9101000000000000600000450c1200000000000000900000454842000000000000003000000004110100000000000010000000000008
  | 6, 36 => 0x10d101000000008510900000001001010000000100102000000000000400000504842020000001802200000000001210100000000000030000043504200000004250020000000000c910600000510c1202000000000000100000000c110100000450c1200000000000000600000425002000000000108100000005110920000000510c9201000000000610100000000c91010000040500200000000004110100000000000040000000000001000000000000600000000c9101000000010c10200000000000080000000000006
  | 6, 37 => 0x1000000000000040000000085106000000000a1010000000000000000000000000a0000000085106000000010c102000000000000e0000025504200000000000000600000001001020000000000007000003550820000000000000040000000000008000000000000600000354842000000005840200000000000000300000000841050000000000006000000000e100000000000610200000000c910100000000000080000000000000000000001210100000000000060000000000004000000000000c0000000000004
  | 6, 38 => 0x45484200000000000000d00000304c020200000425082000000000000002000000010d105000005110d20200000000c9101000000000000c000005010d200000003550420000000354402000000000040100000000010410400000000c01020000000000000000000000000300000510c12000000000000006000000000000200000001041040000035508201000003550020000000000000000000000000006000000000000c0000000000004000000000000c000000000000400000000c810200000001091010000000000003
  | 6, 39 => 0x10000000000002000003550820100000204802000000000000008000000000000500000450c1200000000000000500000355082010000000000006000000000000000000000c910100000000000040000000000000000000010c10200000450c1200000000000e1020000000108104000000000000000000000c91000000000000005000000010010200000000121000000035484200000000000000400000000411010000000100102000004548420000000000000040000000000001000003550820000000500c9200
  | 6, 40 => 0x101101000000000000e0000000104102000000000000000000000121000000000081101000005110920000000000000040000040500200000000010c10200000000000020000020480200000004548420000000000000010000000109101000000000000100000000841040000051109201000000380a20000000001091010000000109101000000000000800000000000000000000109101000000000000400000000000060000000000005000004050020200000000411000000035484200000000000a1000000000000001
  | 6, 41 => 0x2000002048020100000000c4102000000000e1010000000000005000000010410200000000000040000000000000000000000000a00000000c9101000000010010200000511092000000051109200000005210d202
  | 7, 0 => 0x12101000000000a1010000000000002000000001210000000000000020000000000004000000000000400000000000060000000000001000000001210200000000c1100000000000a1000000000000000000000000000800000000000050000000000005000000000000000000001041020000000104100000000000000400000000c9101000000000000800000000841000000000012100000000001210100000001041000000000000002000000000000600000000c9101000000010910000000000121010000000000002
  | 7, 1 => 0x4000000010910000000001091010000000000002000000000000400000000000010000000000006000000010d1020000000000002000000000a1000000000000005000000000a101000000000210000000000c91000000000000001000000000a10100000001011000000000080100000000000000400000001091000000000012100000000000000a00000000c910000000000000010000000000002000000000610000000000c910100000000c41020000000012102000000010010100000000000050000000000001
  | 7, 2 => 0x84102000000000e102000000010d102000000000a100000000004010000000001011000000000000001000000000000a000000000000800000000021000000000080100000000000000c00000000401000000000000005000000010910100000000000040000000000006000000000a10000000000000020000000006100000000000001000000000000060000000000002000000010410000000000000050000000000005000000008410000000000000050000000108100000000000000d00000000021000000000000000
  | 7, 3 => 0x100100000000010d100000000000000100000000000020000000012101000000000a1000000000100100000000000000200000000000000000000000005000000000000100000000000060000000000004000000010410000000000000080000000000001000000010110000000000021010000000000002000000000000500000000021010000000000004000000000000500000000061000000000108100000000000000200000000021020000000000008000000000000a000000000000000000001081010000000000004
  | 7, 4 => 0x5000000000e102000000000210000000000c010200000000000090000000000010000000010c10200000000c91000000000000006000000010110200000001081000000000000001000000000a100000000010010100000000121000000000000001000000000a10100000001001010000000000011000000008110000000001001020000000101101000000000a101000000000000000000000c1100000000000e10200000000000060000000104102000000000e10000000000c110000000000021020000000000005
  | 7, 5 => 0xe10000000000000050000000000008000000010010000000000000000000000000006000000010d1000000000081100000000000a10000000000c91000000000000004000000010910100000000c9100000000001210000000000121000000000100100000000010410200000000c9101000000001210100000001081000000000000006000000000e10100000000000020000000000006000000010d100000000010910000000000000080000000000005000000000a100000000000000400000000000050000000100102
  | 7, 6 => 0x104100000000000000100000000121020000000000005000000000000200000000c9100000000010410000000000811010000000012102000000000000100000000121000000000000002000000000210000000000841000000000012100000000000e101000000010810000000000000080000000000005000000010d10100000000c110000000000000060000000080100000000000a10000000000000020000000000000000000000000400000000000010000000081100000000008010000000000061000000000000005
  | 7, 7 => 0x210000000000021000000000000002000000000000a00000000000020000000000004000000000000a000000000610000000000000000000000108100000000000000000000000c4102000000001210200000000021000000000000006000000000210000000000000010000000040100000000000610000000000000080000000000001000000001210100000000c1102000000000e1000000000000002000000000000600000000c110000000000000020000000000001000000001210100000001011010000000000001
  | 7, 8 => 0x6000000000000400000000061020000000000007000000010910100000000c91000000000080100000000004010000000000000000000000000006000000000000800000000021000000000012100000000010d10200000001001000000000000008000000000000500000000000010000000002101000000000a1000000000002100000000008410000000000121000000000012102000000000000600000001091000000000000006000000000000500000000c110100000000000050000000084102000000000e102
  | 7, 9 => 0x101100000000000210100000001001000000000081101000000000a100000000010c1020000000002102000000000a100000000010010100000000000020000000000006000000000a1000000000000002000000000a101000000010d102000000000e1010000000000004000000010d1000000000000004000000000000a0000000000001000000000210100000000021020000000040100000000010d1010000000080100000000000000600000001081000000000000004000000000000800000000000080000000109101
  | 7, 10 => 0x20000000101102000000000e102000000000a100000000000000800000000000040000000000001000000000000600000000c91000000000000007000000000000700000000000010000000100100000000001210100000001011010000000040100000000000000500000000401020000000101101000000010910000000000000040000000101102000000000000800000000c91000000000000005000000000210200000000021000000000012100000000000e100000000010410000000000000010000000000006
  | 7, 11 => 0x400000000000060000000000004000000000e100000000000000100000000000020000000002101000000010d100000000000000700000000000020000000000000000000000000500000000021000000000012102000000000000500000001011000000000000004000000004010000000000c110000000000000080000000000004000000008410000000000121000000000000006000000000001100000000000040000000108100000000000000a0000000100102000000010010000000001081000000000000005
  | 7, 12 => 0x2000000000000200000000000040000000081101000000010110200000000c1100000000010010000000000811010000000000005000000000e101000000008410000000000c1102000000000a10000000000000050000000000001000000000000a00000000000040000000000006000000010d101000000000a100000000010d101000000008110000000000841000000000012100000000000001100000000000040000000000002000000000000000000000000010000000012101000000000a1000000000000001
  | 7, 13 => 0xa100000000010910100000001041000000000000004000000010d100000000000000000000000000050000000040102000000000000200000000c410200000000021000000000012102000000008010000000000841000000000012100000000000000600000000000050000000100100000000010d10000000000c110200000000c110000000000c91000000000012100000000000000600000000c91000000000000005000000000000100000000121000000000000002000000000210000000000000050000000109100
  | 7, 14 => 0x600000000021000000000000004000000000000400000000000070000000000006000000008410200000000000100000000000001000000010110000000000c110200000000000040000000000006000000000000200000000c010200000000000080000000104100000000008110000000000000040000000000001000000000000200000001011010000000100100000000010910000000000c11010000000000001000000000000500000000061000000000109101000000000e1000000000108100
  | 7, 15 => 0x100000001041000000000000006000000000000800000000000010000000000005000000000000400000001011000000000084100000000001210000000000801000000000000004000000004010000000000000060000000101101000000010d10200000000021010000000109100000000010d10100000000121020000000000006000000010c102000000000210100000000c910000000000021020000000006102000000000001100000000000050000000000004000000008010000000000000040000000002102
  | 7, 16 => 0xa1000000000000010000000010d10000000000000000000000002100000000000000c000000010d100000000000000300000000c010200000000401020000000000001000000000210000000000000060000000000004000000000000c000000000000800000000021000000000000007000000000000800000000c910000000001041000000000000001000000001210000000000801010000000000001000000000000100000001001020000000000001000000000610000000000000050000000002102000000000e102
  | 7, 17 => 0x200000000000040000000100100000000000a100000000010010000000000000040000000040100000000000a100000000008110000000000121010000000109100000000010410200000000000050000000000006000000000a10000000000c1100000000008110000000000801000000000000005000000000a1000000000000010000000000000100000000811000000000100102000000000e10000000000c1101000000010110200000001011000000000084100000000000000000000000121000000000000004
  | 7, 18 => 0x80101000000000000a000000000a10000000000061000000000101100000000000000400000000c41020000000012102000000000000300000001091000000000040100000000010810000000000000040000000000008000000000a10000000000401000000000081100000000000000800000000000040000000000007000000001210000000000000060000000081101000000000e100000000000000400000000000060000000000006000000000e10100000000061000000000000005000000010d100000000010d101
  | 7, 19 => 0x4000000010110000000000000010000000084102000000000e102000000000000200000001081000000000000004000000000e102000000000000100000000c1100000000000000900000000000050000000000001000000000a101000000000000700000000000010000000002100000000000000100000000000020000000000006000000000000400000000c1102000000008110000000000021000000000000004000000000e1000000000000001000000000000500000000000050000000000002000000010d100
  | 7, 20 => 0x20000000000005000000010d10000000001001020000000000005000000000000600000000c9100000000000000200000000121000000000002100000000000000800000000000050000000081100000000000210100000000000050000000000004000000010d10200000001001000000000108100000000000000600000000c1101000000000a10000000000000010000000040100000000008410000000000121000000000000004000000000000600000000c1101000000008410000000000121000000000000002
  | 7, 21 => 0x1210000000000000060000000109100000000000000100000001011020000000000002000000000210200000000000020000000002100000000008010000000000000010000000000004000000000000800000001091000000000000004000000000000200000000021010000000000006000000010d10000000000c11000000000000005000000000e1000000000000006000000010c102000000010410000000000811000000000000001000000004010000000000061020000000000001000000000e1000000000108101
  | 7, 22 => 0x12100000000000000c000000000a1010000000000004000000000610000000000000010000000000011000000000000100000000c010200000000000040000000000004000000000000500000000c91000000000000008000000008110000000000121000000000040102000000000000500000001041000000000040100000000000000300000000801010000000000001000000000a101000000000000100000000000050000000000004000000008010100000000c91000000000080101000000010d10000000000c0102
  | 7, 23 => 0x6000000010910000000000061000000000000004000000000000000000000000060000000000002000000000000000000000021000000000108101000000000000a0000000000008000000000000700000000021000000000000002000000008010000000000c9101000000001210200000000000100000000104102000000000610000000000000050000000000008000000010110000000000c91010000000012101000000000000400000000000050000000101100000000001210000000000841000000000000001
  | 7, 24 => 0x60000000000004000000000a1000000000101100000000000210000000000000060000000000008000000000000400000000000060000000000008000000010110000000000801000000000000011000000001210000000001001000000000002100000000008110100000001091000000000000002000000000000800000001091000000000000005000000000a10000000001081010000000100100000000000a1000000000000005000000000000600000000c110200000000c110000000000401000000000104100
  | 7, 25 => 0x610200000000c410200000000121010000000101100000000000000600000000811000000000000001000000000000a000000008110000000000021000000000000001000000000a101000000000e100000000004010000000000000060000000000010000000000e1000000000000001000000000a10100000000000040000000000007000000010d10000000000000010000000000008000000000e10200000000c1100000000010d100000000000000900000000c1101000000000210000000000021000000000080100
  | 7, 26 => 0xd0000000000008000000000000c0000000108101000000000a100000000010c10200000000021020000000108100000000000000800000000021020000000000002000000010010000000000c1100000000000000200000001081000000000000006000000000a10000000000000010000000080100000000000000100000000021010000000002102000000000000500000000000060000000101100000000000000400000001001000000000084102000000000e102000000000a10000000000c91010000000100101
  | 7, 27 => 0x1041000000000000002000000000210000000000000010000000000001000000000000300000000000040000000100102000000010c10200000000c1100000000000000d000000000e1020000000006100000000000000400000000841000000000012100000000008010000000000000060000000040102000000000e10200000000801000000000006100000000010010100000000801010000000000005000000000a101000000000000a00000000000070000000104100000000000000500000001081010000000012100
  | 7, 28 => 0x210100000000000050000000000001000000001210200000000841000000000040100000000000000400000000841000000000012100000000000000200000000c910000000000000040000000040100000000008110000000000c01020000000012100000000008010000000000000080000000000005000000000000700000000000050000000000005000000000e10000000000c1100000000000000500000000000050000000108100000000010d1000000000000006000000000000a00000000021000000000000002
  | 8, 0 => 0x200000000000000000000000000000000000000200000000000000000000000000000000000000100000000000000000000000000000000000000200000000000010000000000001000000000000200000000000000000000000000000000000000100000000000020000000000001000000000000000000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_9 roots_9 8 s ws hint
  | 1 => checkCutEntry dom_13 roots_13 7 s ws hint
  | 2 => checkCutEntry dom_18 roots_18 7 s ws hint
  | 3 => checkCutEntry dom_20 roots_20 6 s ws hint
  | 4 => checkCutEntry dom_21 roots_21 6 s ws hint
  | 5 => checkCutEntry dom_22 roots_22 6 s ws hint
  | 6 => checkCutEntry dom_19 roots_19 5 s ws hint
  | 7 => checkCutEntry dom_14 roots_14 5 s ws hint
  | 8 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 9 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 10 => checkCutEntry dom_10 roots_10 5 s ws hint
  | 11 => checkCutEntry dom_16 roots_16 5 s ws hint
  | 12 => checkCutEntry dom_24 roots_24 5 s ws hint
  | 13 => checkCutEntry dom_25 roots_25 5 s ws hint
  | 14 => checkCutEntry dom_12 roots_12 4 s ws hint
  | 15 => checkCutEntry dom_17 roots_17 4 s ws hint
  | 16 => checkCutEntry dom_15 roots_15 4 s ws hint
  | 17 => checkCutEntry dom_26 roots_26 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_22 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_26 _ hc
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z1_0 : ∀ i, 0 ≤ i → i < 1 → Z 1 i = true := span_ok (by decide +kernel : span (Z 1) 1 0 = true)
theorem z1 : ∀ i, 0 ≤ i → i < 1 → Z 1 i = true := z1_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 5 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 5 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 5 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 8 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_8 : ∀ i, 8 ≤ i → i < 16 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_16 : ∀ i, 16 ≤ i → i < 19 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 16 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 19 → Z 3 i = true := range_split z3_0 (range_split z3_8 (z3_16))
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
theorem z4_32 : ∀ i, 32 ≤ i → i < 38 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 32 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 38 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (z4_32))))
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
theorem z5_56 : ∀ i, 56 ≤ i → i < 63 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 56 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 63 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (z5_56)))))))
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
theorem z6_136 : ∀ i, 136 ≤ i → i < 142 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 136 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 142 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (z6_136)))))))))))))))))
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
theorem z7_136 : ∀ i, 136 ≤ i → i < 137 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 136 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 137 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (z7_136)))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 21 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 5 16 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 21 → Z 8 i = true := range_split z8_0 (range_split z8_8 (z8_16))
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

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (3941264008 * 2 ^ 32 + 3937060864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_27.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_27 10 hT6 (by unfold IsConst; decide) low_27

def wit : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [13, 4]⟩, ⟨GateOp.and, [12, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_16137_aux

theorem PEqualNP.Outside.L_meta_16137 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264008 * 2 ^ 32 + 3937060864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264008 * 2 ^ 32 + 3937060864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_16137_aux.wit, PEqualNP.Outside.L_meta_16137_aux.wmono, le_trans PEqualNP.Outside.L_meta_16137_aux.wsize (PEqualNP.Outside.L_meta_16137_aux.lower s hs), PEqualNP.Outside.L_meta_16137_aux.weval⟩
