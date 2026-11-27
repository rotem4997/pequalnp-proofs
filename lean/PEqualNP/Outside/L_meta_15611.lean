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

namespace PEqualNP.Outside.L_meta_15611_aux

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

def dom_0 : Nat := 0xff00ff00ff00ff
def goal_0 : Nat := 0xea00aa00aa00a8
def roots_0 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 17), (1, 33), (2, 3), (4, 5), (6, 7), (16, 17), (18, 19), (20, 21), (22, 23), (22, 54), (32, 33), (34, 35), (36, 37), (38, 39), (38, 54), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 4, 6, 16, 18, 20, 22, 22, 32, 34, 36, 38, 38, 48, 50, 50, 52, 52]
def r2sG : List Nat := [3, 5, 17, 33, 3, 5, 7, 17, 19, 21, 23, 54, 33, 35, 37, 39, 54, 49, 51, 54, 53, 54]
def mpG : Nat := 0x3fffff
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 3 => 6
  | 4 => 30
  | 5 => 43
  | 6 => 9
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x425948fe331ffd68167741511154ab3b10a090e10edfdb2d
  | 4, 0 => 0x47baa07035de20fe31b43c3d28206f83267310691e53974f1bb096731b94042e18b803fa177be419149143ec12c57e72128b973c12294ab80f1394670dcb40af0d09c89a0cc205f20b5679410ab1732e09e217a0080f99a4066ead81057b960c03f5f653030ef30501b1a27b01753823012766cc006274db
  | 5, 0 => 0xa4f836c39980c81791b066eb8f7d5c087994985a6b85db7465848d205a43850350eeb30f5067bf9447baa07042d6ffea387bb923379305622f17f7c42ef3d89a2e15ce1628206f8327ca5be020d129b41fb2e99a1f650f8c1814479f17bdcd44171aa0eb15dbc31515521a2e133a4b1a0ef7856d0c2759300c15df230ab1732e09309ea2080123b5074cd068066ead81059d97a005029cf803f5f653035c2d6802f7ca32014e820700168dd5
  | 6, 0 => 0xa4f836c36b85db7450eeb30f47baa0702f17f7c427ca5be017bdcd4415dbc31515521a2e
  | 7, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x330033003300330011001100110011000f000f00ff00ff000f000f000f000f000f0000000f00000003000300030003000000ff000000ff000000aa000000aa
  | 0, 1 => 0xa800a800a800a800a000a000a000a000a000a0000000000088008800880088005f005f005f005f005500550055005500550055000000000055000000ff0000
  | 0, 2 => 0xc000c00000000000c0000000c0000000aa00ff00aa00ff00aa00aa00aa00aa00aa00aa00a000a000aa00aa0000000000aa00a000aa00a000aa000000aa0000
  | 0, 3 => 0xcc00fc00cc00fc00cc00cc00cc00cc00cc00cc0000000000cc00880088008800cc000c00cc000c00cc000000cc000000c8008800c8008800c000c000c000c0
  | 0, 4 => 0xf0000000f0000000ee00ee00ee00ee00ee00ee00cc00cc00ee00ee0000000000ee000000ee000000ec00ec00ec00ec00ec00cc00ec00cc00e000e000e000e0
  | 0, 5 => 0xfc00cc00fc00cc00fa00fa00fa00fa00fa00fa00aa00aa00fa00aa00fa00aa00f000f000f000f000f000f000a000a000f000f00000000000f000a000f000a0
  | 0, 6 => 0xff008800ff008800ff005500ff005500ff000000ff000000ff000000f0000000ff000000aa000000fe00fe00fe00fe00fe000000fe000000fc00fc00fc00fc
  | 0, 7 => 0xff00fc00ff00fc00ff00f000ff00f000ff00aa00ff00aa00ff00aa00ff008800ff00aa00ff000000ff00aa00aa000000ff00aa0000000000ff00a000ff00a0
  | 0, 8 => 0xff00ff00f000f000ff00ff00cc00cc00ff00ff00aa00aa00ff00ff00aa00a000ff00ff00a000a000ff00ff0033003300ff00ff0011001100ff00ff00000000
  | 0, 9 => 0xff00ff00ff000000ff00ff00fc00fc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x74acf1446ab4f13480fcb144889cf14492ace14466ad2944
  | 4, 0, 0 => 0x80d501418b018ab3c5160375674a2c06aacd9456aa4f1426b0daab3c5162bb567892c06aad09458ed549e28b0159e282160335678a2c06ac0b94580d559f28b0daae3c51603d56788ac070ad1145
  | 4, 0, 1 => 0x20355678a2c06a88c145569119e28b01aab4c3160b55678a2c06aacc94580e141e28b21aab3a51602b4c8c62c07cb0f1458ed551e28af9cab3c516035587872c078acf145
  | 5, 0, 0 => 0x8701aab3c51a3c06aa4f14680d559e2835a03560b8f146010daab3c5160355678a0b680d57ab3c51a0355678a066011daa93c51603d6aa0f14680d5a2b3c51804066acf1458d01aab3451a0355678a0f680d55a22839a0396aacf146
  | 5, 0, 1 => 0x80d559e2a51a0366aacf14680f559e2841a0355678a0c680d559e280da0355678a0260101aab4c3160355678a0a60100f14080560355aacf1468501aab3c51a03564acf14680d559e281da0355678b94680d559e3451a03560acf146
  | 5, 0, 2 => 0x406aacf0a580d559e2825a0355678a00680f5aab3c41a4406aacf146010159e280560354e78a0e60101a9e141160355698f14680d559e281580406aacf145
  | 6, 0, 0 => 0x406aacf0a5010159e280560355698f1460101aab3c5160355678a0c680d559e2829a0355678a07680d559e3451a03560acf146
  | 7, 0, 0 => 0x406aacf145
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 32
  | 4 => 39
  | 5 => 46
  | 6 => 46
  | 7 => 39
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xc94abf252a038fffce319f3806002108f07c1fc0000f
  | 0, 1 => 0xffffffffff0ffc003e0f80
  | 0, 2 => 0x6000000c0007c1fc0000f0000000000000000000000
  | 0, 3 => 0x37b5c0dad50368000c000030b440c0d0000300018c40
  | 0, 4 => 0xc03800dad5f36b540da000303400dad5036b54018c40
  | 0, 5 => 0xf6bd431ce6fc7003f00e0fc739831c000c7000300e00
  | 0, 6 => 0xf83e03ffff0f83e03e0e00f80003def7ff03c03def70
  | 0, 7 => 0xffbfc3fcfe0f83e3fe0f80f83e03e0000f80003e0f80
  | 0, 8 => 0xfff983ffd50ffc03fff000ffc003ff2afffca83ff000
  | 0, 9 => 0xfffe03fff70
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x494ab80000018dffc6319d1806102108c03c1ec0f07b
  | 0, 1 => 0x539dcd0c6624300004a551bce67690800a4200290f84
  | 0, 2 => 0xa6200290c005bdffd6f7ff5bd9a96f0085b1f9960784
  | 0, 3 => 0xb7b5cedad51b6a002dad51b4b446d0d00b6b54698c40
  | 0, 4 => 0xe43803ffffffff567ff808fc3e13def73f6bd479ce62
  | 0, 5 => 0xf6bd47ffffffffffffffffe7398b9ce62e720039ce62
  | 0, 6 => 0xfebf57f0f84fc3e13f0e00fc3e13ffffffc3e13def73
  | 0, 7 => 0xffbfdffcfe6fffffffffddfffe33fff8cffe023fcfe6
  | 0, 8 => 0xfff9abffd59fffffffffeefff9abffaaeffe023ff808
  | 0, 9 => 0xfffe33fff7b
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 22 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 22 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 74 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 74 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 74 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 74 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
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

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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
theorem z4_24 : ∀ i, 24 ≤ i → i < 30 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 24 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 30 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (z4_24)))
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
  scr dom_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_0 roots_0 goal_0 8 := by
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

theorem low_0 : Lower dom_0 roots_0 goal_0 8 := S_0.noCircuit

def dom_1 : Nat := 0xffff
def goal_1 : Nat := 0xeaa8
def roots_1 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

namespace S_1
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (4, 5), (6, 7), (6, 14), (8, 9), (10, 11), (10, 14), (12, 13), (12, 14)]
def r1sG : List Nat := [1, 1, 1, 2, 4, 6, 6, 8, 10, 10, 12, 12]
def r2sG : List Nat := [3, 5, 9, 3, 5, 7, 14, 9, 11, 14, 13, 14]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1
def NN : Nat → Nat
  | 3 => 5
  | 4 => 9
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xa8d1151276bfd8fd4c81d31d1dd9b64d19cdae2b
  | 4, 0 => 0xc6abdc4ba8d115127693bb1e52cffc6c4e50aa1c4c1ef02a3f859e891a46e13f02e67005
  | 5, 0 => 0xa8d11512
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xeeee000000000000cccc000000000000c0c0000000000000aaaa000000000000aa000000000000008888000000000000555500000000000000ff
  | 0, 1 => 0xfff0000000000000ffaa000000000000ff88000000000000ff00000000000000f0f0000000000000f0a0000000000000f000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xba644e8644da634b9644ca644
  | 4, 0, 0 => 0xa64040ba644ba6425ba6415ba76450ba614eba645ba6545ba6405
  | 5, 0, 0 => 0xba644
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x36f368060007000000ff807f
  | 0, 1 => 0xff0f87f80f80c70c00c00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfffb69a605bf584129a4003b
  | 0, 1 => 0xff6ffffedfc4e72e72e40
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_1 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_1 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_1 == dom_1) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_1 goalM u ys) : RunD dom_1 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_1 roots_1 goal_1 6 := by
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

theorem low_1 : Lower dom_1 roots_1 goal_1 6 := S_1.noCircuit

def dom_2 : Nat := 0xffff0000ffff
def goal_2 : Nat := 0xeaaa0000eaa8
def roots_2 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffff00000000, 1, 33)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xffffffff
def goal_3 : Nat := 0xeaaaeaa8
def roots_3 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_3 : Lower dom_3 roots_3 goal_3 7 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0xffffffffffffffff
def goal_4 : Nat := 0xeaeaeaaaeaaaeaa8
def roots_4 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_4
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (1, 33), (2, 3), (4, 5), (6, 7), (6, 14), (8, 9), (10, 11), (10, 14), (12, 13), (12, 14), (16, 17), (18, 19), (20, 21), (22, 23), (22, 30), (22, 54), (24, 25), (26, 27), (26, 30), (28, 29), (28, 30), (32, 33), (34, 35), (36, 37), (38, 39), (38, 46), (38, 54), (40, 41), (42, 43), (42, 46), (44, 45), (44, 46), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54), (56, 57), (58, 59), (58, 62), (60, 61), (60, 62)]
def r1sG : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 6, 8, 10, 10, 12, 12, 16, 18, 20, 22, 22, 22, 24, 26, 26, 28, 28, 32, 34, 36, 38, 38, 38, 40, 42, 42, 44, 44, 48, 50, 50, 52, 52, 56, 58, 58, 60, 60]
def r2sG : List Nat := [3, 5, 9, 17, 33, 3, 5, 7, 14, 9, 11, 14, 13, 14, 17, 19, 21, 23, 30, 54, 25, 27, 30, 29, 30, 33, 35, 37, 39, 46, 54, 41, 43, 46, 45, 46, 49, 51, 54, 53, 54, 57, 59, 62, 61, 62]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_4.map (· &&& dom_4)
def goalM : Nat := goal_4 &&& dom_4
def NN : Nat → Nat
  | 2 => 1
  | 3 => 14
  | 4 => 92
  | 5 => 355
  | 6 => 482
  | 7 => 179
  | 8 => 12
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x1a7b31db
  | 3, 0 => 0xfbc825499ac64fbb5a1c4bda5233aa8d4f85c03e49115c2e3b6595a438de818233368b4f30953c9e2a23e8a02173ee51180f5bdb109742c0
  | 4, 0 => 0x6b64b3726b4415196a697249695056b66918e162684119b2661eb937659fcb01653b33e063c3399b5f2e77035cc87fbb5a45054c5a2930ff5722acad5514801c52c432ba505f95ab5019b67d4e4b92234c487ea84ade76194714e15d44e8fba94319027141c201a03fbed3e73bcf3a993a43484f37328bab360d0e703596f2853219413e31f970fe30953c9e2f2b387c2e6d6b222e0751262d69e1cc2b63ff5427b4624f27446bd61fdb83bf1eebb2f11e9ce7ef1e098fbd1d39c7941b61ec6d1b2b5c151935bc0214b593c31441dde51380f11c12043680117ea2510d4b3e9f0b5097fd099c73960617072c049a1c650353ff6702dc0baa0245505b01764e4c
  | 4, 1 => 0xdf317fdedbb2b3bbd59d377acfd0de1ecdef3b96c254fc88aa5894f7a359b3d4a06a3b4c990805be988b10808f26da3d8d083d6087e45a89864d4c4e83c7d06883b96e437e1bea917cb4d3b67bc34c31785757f374583ac0707024076ff5f3896fb731cf6f800cad6de90fe56d2353c4
  | 5, 0 => 0x10bd421e10baa873106a2aa9101e57b11014cfa90f865b750f59bb620efc073f0eacf1a40e6c223a0db432850d88c2480d79cb890d34e9280d31bdf20ce5c19e0c665be90c36bb900b20d47c0abd2bf70aa7c5dd0a4e1a200a1163e109f4089109d11e2809d0754409a412bc099c73960900418408ea0cab08e32d17085a20c208259fb107e5f6d8079efbf7079b2f310746d5d7064bab2605b86497052cb604051ce45e05048e7704e549e404712042046b7eec03d8385d03a24a600363eadf034b623b034a43b10342f57b0338386f024877fc01d29fcd01a379540177b476013b1ae200f006a800e2288800d7e88600c274f100a6d68e00904a5100416e5d
  | 5, 1 => 0x27a9ba2226ce087a26c5eaee264c481625a31684259569db250b3e6a24c71b0323fc2cd3236579e32343055d2098ef00207e77462061481e2049c7fb1ffc01dd1fd723ee1fb13e891f9a86b81f8912831f6e04b41f6d1e761f2586511f0740291ef1e5631eee48821ee50c9c1ed15b311e9ce7ef1e5b93861e06e3f41dd04af81db676941d9a4fc41c7034831c6876911c42e7321c04afc41bc7fbbc1b94915e1b8129591b61ec6d1a10f6e518a5cdf31873f32618734073178b4c4e1758473216da5613169a10fc1569f56f154c172714d64fa614c9349a148bb74b14326b8a13579f271266f7f7124b577f123e099e12111ba511e339b6119217d81102d1a7
  | 5, 2 => 0x4272d6fa4249e475405b2ed5403854a23e147f2a3d9419de3d60650f3d30bc313d20e24e3d082c743ce323a33c9d75a23c3337063be5e98e3bd82cc93b72c2ff3a86104b3a792f6a3a6c09213a06e07e39cc0d07389e72c53857579d3834be123740731a373b41c13739d4603713fac9369f769f3678bbab360fd26736040d1b35c6e9dd35099e5634d5feb934473c3933c00cc53382aa1632ee8f2e32ae7f2e320e01dd32048d4b318b93d13156fc53313951c131223ee62f72e55f2ed07be72eb38dc92e490dac2e289d962e212fbc2d2b50ac2d1d24532b6cad7a2b3cf8522b21335e29e0a5f9298d11772985bd94294a5f9c28e7ed54285b57bf27e9389d
  | 5, 3 => 0x67cc370a6733942566b3495665c20ee1659fcb0165389ed56435c6df63f9e42463e39f2563de1ede639717c3633c95a7632407c262c9605962443cd861d7af80618a6a105fc4cd455d99cd9e5d65c0895d3857e75d0aa57c5cc87fbb5cbef0b25c51913c5b4b9cec5b0369225967c8f758f45d6858293bcc57f0039357ed192457cea303569b895553e5913152d3ceb752062045509e0ad6506c7ad0505f95ab50523ca95035ea7850216644501d2ed74fa507fb4f7c60744f4a575e4e87686e4e29c7d14e1755844c7b77174c2c4d784c1029b44bf7d1c64bc38b784b87b2694a49ce8049ecf21149c61e7d44c0d6944446b25443f96595434ac03242ec1c5a
  | 5, 4 => 0xa3435ec4a22de227a06a3b4c9b29479a9aa419e79a3e92c299faddc59979b08a98cdc7fe97cea53d971ff53496ced85296ca2932944972d692fa5797926b50be921f543b9190d39c904fc1d98f33bf628d31b09a8cedacd18cc845518b5a4bd68723084d86e756d3847dc71484200ce684129c4083d4b58d817ebe357fe9047c7ec375137e48f78f7df8983f7d8ecad87d69ed3a7d03682b7c9c1abb7a7a23a87a506f8f7a03bd0e79f38a0c782390d476d684c876a82f1975b7ea5c750d544474f52302736b271272b21ef072b027fb72a69f11729d654a724145a271a3faaf6f80bd776e861e126cd0620d6c3e88df6c3d1b7e6af9f82c6aa180e8688ea6bc
  | 5, 5 => 0xf2645cedf04bdcbbebafd152e82c56a1e5699bdee4842702e31f5139e131a01ede4a459ede160a38dcf85272da9cd2d6d80b7990d104e3ebcd786ec8cb5d4866c9fe2fadc8add0d6c67f638ac57cd932c1962d4ebd20403cbcd62099ae910a3eae3211d5ad64f2d1ac851212aa58d6bda999cad5a98670d0a88eb6c2a8198ebca5fad8b7a4c1c032a35c9dd6
  | 6, 0 => 0x1106ad57106ef5980f8e38f60f8899180f865b750f8009980f56ffe60f47a0390f151d1a0f115ba20ee7b93a0ee2d2210ee0af2a0ed86b730ec4f4730e4ddd170e1ee4940db432850d92daa50d86abda0d6e8d170d377cd70cb015bc0c7bcab90c36bb900c13a5aa0c03b9010b9480970b19047e0aaabd360aa6d20e0a7677f50a53c4d609b8a79109695d40093e73560903dbc508f0123c07f1b6d607492140073a22a106f3c6400665520c06596465060e91e705b8649705a9e53f0520799e05169eb00432137103d8385d03abb2f00357655802d6a72e029aef9e0240dc1801f5db9e01dadaa501a5e6740198403d0185010f012c73fe00d5313e008dd725
  | 6, 1 => 0x204a72201fdbe3151fb72b911fac1ffd1f87b1c01f0740291ee350081ec0fa371ea6aee91e35b7f71e0576261dfd840b1de45f961ddd2b031dbe4d991d826c881d07cbc61c0c1b4b1c0aecba1bf5be811b805bb41b62a5db1b25678b1b16f5ed1aa1953a1a8ffa5d1a2594481a21fbf419b9717319749e0d194d51da194727b518734073184ab4571836a7e618103f8818043d6917f938b617e7c6aa17d15ef5175a929b1758473217016561165a1433163cc66615f4eac915c3143a15b18426158c470e15602014155ed0bb14b9a6ad13fe949713e90d2b13e0e2a713d6d81d13346ed1126ef83812488876123c1c3b1232479711880f961161181a11408e9a
  | 6, 2 => 0x32fa2f9532e16b8932b963233257a9653176335b3156fc533096bd902fb10f502f2d39052f29cd512ede35262e3ae3492d618f3b2d3ea4312ce3b7132cc795ae2ca929c32c4642572bfff1562b21335e2af68de12ad9fd9b2a6347522a47f4e42a42385829e188d329c478db29af2b642992b932296b38aa284ba8d727fd4ed027b671de275dc4202686b9112604931525c5c2a225bf78b925a3168425928460250b3e6a246d800b2466684624622b26243971d52416c07e24140a4123aa74da2325c90b22880254227ea68b2241f9d721d562ba21997fae2190160921730a3e2145ca5920fbfbd620eebdc420e249a720d56179206642322064873a2062e284
  | 6, 3 => 0x4b51d8934b4a1dcf4af8703d4a55e6434a530fc24a4249ab4a3f5f3c4a2e5349496885e5493ccd6c48683a6347154d3e46a6e54b4640bf18462000d245a7f598457c9139457c8acd44fe769744df840d44d46f7844ad1ab2446f8a94434ac0324221143d41ec4f6f40a60e3740936de1406dd97a404b30134028922d3ff4ef3e3feafc213f39b76f3ee746153e0acfe73dc293cd3cd948b53cc696da3c0ce04f3bf021da3bd82cc93bd6ad1d3a4fc20639ffcc7c39e37c1a39ddbebc38ff95f7388a7a1438170f693803b6ee37a858a73794e38c3766c85036de7a8736cd76be369945123610c82c35099e56349995fb3481847a33d25e62339be83033582d34
  | 6, 4 => 0x6d65318d6c4b6e046c49cc986c3e88df6c3d1b7e6bc8f9716b9d976b6a41599e6a344b406a08bb0568ade545684a9053680392f367c080b767339425671ea51e6623177d65e88a3d65524fc6654dfbc0650bdfd764c8c42e647e187f647899486235df0f6169ffad60f47f6c60205a025fa001255f9873855eb5ede35e5e95475df837b25d71535d5d1d88c75cbe4b0e5c7fa2ba5b3bed485a9f5dfd593f5843588269ee58761ced5808a3535693d11756488c3a55f9c36e55f674805530a86c54c66e2d53eff8a9533b7ec153181bf8510a33e250e499dd5074cc07506c7ad04f6e06074f29237a4ee41f594decf5114d67b2e34d43334a4d244e3f4cf6f022
  | 6, 5 => 0x916bb66090c788868fda83be8fa19e1f8d9c69668cfa91f68cf7a7878aa3b04f893fe42c88f4b3ca87a8492f878be23f8680741c8663aea98527bd3a845f90f78455b14984129c4082de7117829ec1d681b76e8e81b726b3817ebe35805e03487fd8d7587f24c13b7eff2d3a7ed1cb467e7a0a4c7d8ecad87d2a63907cea112d7cd727a77c9e1f737c2f60d67ba3c0797a36543c79d3e13a795acc8c792b8cc8791917a878d13196778424c27730263a7723c8d076d00d2c76a635e57626fba575b7ea5c7474155474601fa773627f61730cc97a727718da71ff99de71fa16167108872f70eea42e70d6da32703b0e086f77c41e6f4c3cf56dbfabf96d72ad59
  | 6, 6 => 0xbe20deedbe0cd55bbde1cfb5bdce499fbc5bcfc9bbcc115cb9885577b91d4ce9b8b7e9f7b75432adb7083aceb3ff36d3b1ce22c6afaab267af639a61af448f52aed94acbaeb38838aea2a84aad64f2d1ad58a5d0ab12b296aa00aaa3a98e4816a8e78fc4a8cca005a8cb32a4a8a73885a81e07a4a7a2a7a3a66fb308a5d3bbe5a5b035efa55beef2a5323c56a3c1ab4ba3744415a2cd8bc3a13c87fba076800e9fb7f0179f77feb79d99351f9d72dd149c3b434d9bca9a899bc930f99b6cf8b59b6512559b4d17b5997af9fb98e9771597a0022596ced85296b5570395e5515995d27d40951cbb3294d7782194a0b6d3947012d39402840893064ed59190d39c
  | 6, 7 => 0xfc6afe7df6535463f6281cb5ee5bfb02ecb660fdeb93c63be4842702e3e18a9be3cc7821e1151f08dffa03e8de90f3a7db7eec9cdb4f33a9d9b76c3fd3980975d26d319fd0c08da1cf527d16cd786ec8cbd4b795cbaeeccfcad25745c996b3b6c8dcf1b0c637c9f1c4ba52fcc4a4bbb4c23c3efdc0e08b57c01a4c7abfb0cba3bec74491be4533ca
  | 7, 0 => 0x3594c0ac355e29ce3481847a339be83032ba82ac3264f19430ccd1eb2f1362052e9c408b2cb7e2692b81626d2b0f56702af4104e29f0f18429e942c429c478db291abe5628a4a83e2775450f26beaf6f26bb2fef25bece642310763b23038dd422d85c9a2219ec0a2081cc612064873a1fb72b911f3d31db1e1aa3ae1d989e101ca0b1831c53b96d1c1ffead198eb56517a82026175a929b17206e3516b50ee915ff8a471581f8c81528ba3c1317dd2b12b8884a123247971187183a0f8898390f79f41c0f6b9a140e8414b20d9cbe430d4d98860cc7aa850cabde0a0b989d440a172c4906b07a03064612c705c61dd605a3eb0a03e364540064991500273479
  | 7, 1 => 0x7a7a23a87a2bf43678f04d3478493a7f77f10ba272b2833971fb25a26f3b46226e8018a76c4b6e046c3d1b7e6bed6d236b46b4d16a7ff6686733942567044c4c651506a46478994863669d955ec6f1c75d93d62e5d7bf2db5d23bf8f5bff541c59e9c31b56abec62568ff7f15640306855ab6c4654ed1c7554b47b985314eaf652f2fea4523dc21151efbb6051bf3f2b50c9577f4f943bc44ec05ebd4e9d19034dc27b5b4cfd734b4cd8ba054b0c2c39499b08ca48b0ac9d475141bb46e149a245c07cca43555fb0434ac03241d622d341a8390641a4b5d640455b7a3f49363a3d6d0b963c9d75a23a8b1a653a476634396f572d3950034036c744ae359f67e7
  | 7, 2 => 0xfc3cf275f6657479ee22ff53e575a6eae1283faadede789bd56748abd2f75b26d0dd3a20cda803e7c707ac1ec4ac2c82beb2f988bde1cfb5b9782853b559ed2fb37ef559b23cd636b12375bdac3ab49daa8df529aa2867c5a98e4816a8e78fc4a8d9852aa8d69abba5e4c2a9a5103ec2a4a028239eab30d29ab0be7a996c23f498553ede9710a458968ac1e9965f345892b08ece925c0be49117715e8a81f0ca89211e6a877c8a9f85210b038492c7cd8241b0597f27d8097dfd47397d7d57bc7c439fcf7aa157477a9f7e30
  | 8, 0 => 0x8a7994f87f4590c97cea112d76f0de335fbac6fd5e22a7545cde0cce5059633d4aee73791561a43a0e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f000000000a0a0a0a0000000003030303000000000000ffff000000000000f0f0000000000000aaaa00000000000055550000000000003333
  | 0, 1 => 0x444400004444000005050000050500000000ffffffff00000000eeeeeeee0000000055555555000000003f3f3f3f00000000333333330000000030303030
  | 0, 2 => 0x20202020202020201010101010101010077007700770077005f005f005f005f0000ffff0000ffff0000ffff0000aaaa000077770000777700005f5f00005f5f
  | 0, 3 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f00000e0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a070707070707070705050505050505050303030303030303
  | 0, 4 => 0x222222222222222220202020202020201f1f1f1f1f1f1f1f15151515151515151313131313131313111111111111111110101010101010100f0f0f0f0f0fffff
  | 0, 5 => 0x3737373737373737333377773333777733333f3f33333f3f33333333333333333333333330303030333333332222222230303030303030302a2a2a2a2a2a2a2a
  | 0, 6 => 0x505050505050f0f050505050505050504c4c4c4c4c4c4c4c444444444c4c4c4c444444444444444440404040404040403f3f3f3f3f3f3f3f3c3c3c3c3c3c3c3c
  | 0, 7 => 0x5a5a5a5a5a5a5a5a57575757575757575555777755557777555555555555ffff5555555555555555555555555555000055554444555544445454545454545454
  | 0, 8 => 0x7f7f7f7f7f7f7f7f77777777777777777777000077770000707070707070707066666666666666665f5f5f5f5f5f5f5f5f5f5f5f000000005f5f00005f5f0000
  | 0, 9 => 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0000099999999999999998f8f8f8f8f8f8f8f8a8a8a8a8a8a8a8a888888888888888888888888808080808080808080808080
  | 0, 10 => 0xaaaaaaaa80808080aaaaa8a8aaaaa8a8aaaaa0a0aaaaa0a0aaaa8888aaaa8888aaaa8080aaaa8080aaaa2222aaaa2222a8a8a8a8a8a8a8a8a5a5a5a5a5a5a5a5
  | 0, 11 => 0xaaaaaaaaaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00aaaaaaaaaaaaa0a0aaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaa0a0a0a0aaaaaaaa88888888
  | 0, 12 => 0xc0c08080c0c08080bfbfbfbfbfbfbfbfbbbbbbbbbbbbbbbbbabababababababab0b0b0b0b0b0b0b0afafafafafafafafababababababababaaaaafafaaaaafaf
  | 0, 13 => 0xcccc0c0ccccc0c0cccc8ccc8ccc8ccc8c8c8c8c8c8c8c8c8c3c3c3c3c3c3c3c3c0c0c0c0c0c0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000c0c0c0c080808080
  | 0, 14 => 0xccccccccc0c0c0c0cccccccc88888888cccccccc80808080cccccc88cccccc88ccccc8c8ccccc8c8cccc8888cccc8888cccc8080cccc8080cccc4c4ccccc4c4c
  | 0, 15 => 0xcccccfcfcccccfcfccccccccccccffffccccccccccccccccccccccccccccc0c0cccccccccccc8888cccccccccccc0000cccccccccc88cc88ccccccccc8c8c8c8
  | 1, 0 => 0xd5d5d5d5d5d5d5d5d0d0d0d0d0d0d0d0cfcfcfcfcfcfcfcfcfcfcfcfcfcfcccccfcf0000cfcf0000cececececececececdcdcdcdcdcdcdcdccccddddccccdddd
  | 1, 1 => 0xeaeaeaeae0e0e0e0eaeaeaea00000000eaeae8e8eaeae8e8eaea0000eaea0000e8e8e8e8e8e8e8e8e0e0e0e0e0e0e0e0dfdfdfdfdfdfdfdfdddddddddddddddd
  | 1, 2 => 0xeeeeeeee88888888eeeeeeee00000000eeeeececeeeeececeeee8888eeee8888eeee0000eeee0000ececececececececececececececcccceaeaeaeaeaeaeaea
  | 1, 3 => 0xf080f080f080f080efefefefefefefefeeeeeeeeeeeeeeeeeeeeeeeeeeeeececeeeeeeeeeeeecccceeeeeeeeeeeeaaaaeeeeeeeeeeee0000eeeeeeeeecececec
  | 1, 4 => 0xf0f0f0f0c0c0c0c0f0f0f0f0a0a0a0a0f0f0f0f080808080f0f0f0f050505050f0f0f0a0f0f0f0a0f0f0e0e0f0f0e0e0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0
  | 1, 5 => 0xf3f30000f3f30000f1f1f1f1f1f1f1f1f0f0f1f1f0f0f1f1f0f0f0f0f0f0f0f0f0f0f0f0f0f0e0e0f0f0f0f0f0f00000f0f0f0f0f0a0f0a0f0f0f0f0e0e0e0e0
  | 1, 6 => 0xfafafaa0fafafaa0fafaf8f8fafaf8f8fafa0000fafa0000f8f8f8f8f8f8f8f8f5f5f5f5f5f5f5f5f4f4f4f4f4f4f4f4f3f3f3f3f3f3f3f3f3f3f3f300000000
  | 1, 7 => 0xfcfca8a8fcfca8a8fafafafafafafafafafafafafafaf0f0fafafafafaa0faa0fafafafaf8f8f8f8fafafafaeaeaeaeafafafafac8c8c8c8fafafafa00000000
  | 1, 8 => 0xfefefefe00000000fefe0000fefe0000fdfdfdfdfdfdfdfdfcfcfcfcfcfcfcfcfcfcfcfcfcfcccccfcfcfcfcfcfc0000fcfcfcfca8a8a8a8fcfcececfcfcecec
  | 1, 9 => 0xff08ff08ff08ff08ff05ff05ff05ff05ff04ff04ff04ff04ff01ff01ff01ff01ff00ff30ff00ff30ff00ff00ff11ff11ff00ff00ff00ff00fefefefefefefefe
  | 1, 10 => 0xff80ff80ff80ff80ff3cff3cff3cff3cff33ff33ff30ff30ff30ff30ff30ff30ff15ff15ff15ff15ff11ff11ff11ff11ff0fff0fff0fff00ff0cff0cff0cff0c
  | 1, 11 => 0xffaaffa0ffaaffa0ffaaff88ffaaff88ffaaff80ffaaff80ffa8ffa8ffa8ffa8ffa0ffa0ffa0ffa0ffa0ffa0ffa0ff00ff88ff88ff88ff88ff88ff80ff88ff80
  | 1, 12 => 0xfff8fff8fff8fff8ffecffecffecffecffb0ffb0ffb0ffb0ffaaffaaffaaff88ffaaffaaffaaff00ffaaffaaffa0ffa0ffaaffaaff88ff88ffaaffa8ffaaffa8
  | 1, 13 => 0xffff0404ffff0404ffff0101ffff0101ffff0000ffff5555ffff0000ffff5050ffff0000ffff0000ffff0000fafa0000ffff0000eeee0000ffff0000aaaa0000
  | 1, 14 => 0xffff3c3cffff3c3cffff3333ffff3333ffff3333ffff3030ffff3030ffff3030ffff0f0fffff0f0fffff0f0f00000000ffff0c0cffff0c0cffff0505ffff0505
  | 1, 15 => 0xffffaaaa00000000ffffa8a8ffffa8a8ffffa0a0ffffa0a0ffff8888ffff8888ffff8080ffff8080ffff5f5fffff5f5fffff5555ffff5555ffff4444ffff4444
  | 2, 0 => 0xffffc0c0ffffc0c0ffffafafffffafafffffaaaaffffaaaaffffaaaaffffa8a8ffffaaaaffffa0a0ffffaaaaffff8888ffffaaaaffff8080ffffaaaacccc8888
  | 2, 1 => 0xffffeeeeffffeeeeffffececffffececffffe0e0ffffe0e0ffffddddffffddddffffccccffffccccffffccccffffc0c0ffffccccffff8888ffffccccf0f0c0c0
  | 2, 2 => 0xffffff11ffffff11ffffff0cffffff0cffffff00ffaaff00fffffcfcfffffcfcfffffafafffffafafffff8f8fffff8f8fffff0f0fffff0f0fffff080fffff080
  | 2, 3 => 0xffffffaaffffff88ffffffaaffffff00ffffffaaff00ff00ffffffa8ffffffa8ffffffa0ffffffa0ffffff88ffffff88ffffff80ffffff80ffffff33ff00ff00
  | 2, 4 => 0xffffffff05050505ffffffff03030303ffffffff0000ccccffffffff00000f0fffffffff00000c0cffffffff00000505ffffffff00000000ffffffaaffffffa0
  | 2, 5 => 0xffffffff33333333ffffffff30303030ffffffff15151515ffffffff11111111ffffffff0f0f0f0fffffffff0c0c0c0cffffffff0a0a0a0affffffff08080808
  | 2, 6 => 0xffffffffaaaa8888ffffffffa8a8a8a8ffffffffa0a0a0a0ffffffffa0a08080ffffffff88888888ffffffff80808080ffffffff55555555ffffffff3f3f3f3f
  | 2, 7 => 0xffffffffe0e0e0e0ffffffffcfcfcfcfffffffffccccccccffffffffc0c0c0c0ffffffffb0b0b0b0ffffffffaaaaaaaaffffffffaaaaa8a8ffffffffaaaaa0a0
  | 2, 8 => 0xfffffffffefefefefffffffffcfcfcfcfffffffffafafafafffffffff8f8f8f8fffffffff0f0f0f0ffffffffeeeeeeeeffffffffececececffffffffeaeaeaea
  | 2, 9 => 0xffffffffffaaff00ffffffffffa8ffa8ffffffffffa0ffa0ffffffffff88ff88ffffffffff80ff80ffffffffff11ff11ffffffffff0cff0cffffffffff05ff05
  | 2, 10 => 0xffffffffffffc0c0ffffffffffffaaaaffffffffffffa0a0ffffffffffff8888ffffffffffff5555ffffffffffff0f0fffffffffffff0000ffffffffffaaffa0
  | 2, 11 => 0xfffffffffffffcfcfffffffffffffafafffffffffffff0f0ffffffffffffcccc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x53a38903
  | 3, 0, 0 => 0xa6469689d49b3f9929049b3adb8904a6c6cda5e4a7470d45e490badc0904a6c6d207d49abf19290490c71b890490badb890490bf1b6904a828cfa5e475b71208e4a6adcfa5e4
  | 4, 0, 0 => 0x9abadb6903eac85bcac3a179642eb6ca2cbcb218d365145e575b652c8a2f2cd9d6c9451796991a5627494b218db6d207d59c3ad926d2f2c85fac9369795d6d9562411cb3564ad4da5e590badbcb64eabad929047145642f164a28bcb1d82ab0fa545
  | 4, 0, 1 => 0x90badb6be45acd5d6db369794012175b712092175b795890590c6958792f2d3e3cac3e97963af9561f4bcb4a8bab0fa5e599bf192ac482c85d6dc45179642fe64a2cbcb217bb24d45e590badb2ac482d3234b43e979666eb64a2cbcb2175b2520515
  | 4, 0, 2 => 0x8ebf1587d2f2cd9d6c93517966afd649b4bcb3d8aab0ec5e59d455587d2eac85f8c94813d69719561f4bcb3675b252051590badb2b4482d35d6db5f2496991a56274bcb4d8daa4fa5e59d3ad928a2c2c8616eb6da41666eb6cad13ab2175b2520565
  | 4, 0, 3 => 0xa7471587d2f2c860ac935159642eb6f9b4bcb2182324d45e590badb8be4eac8638dc35179642eb6db1120b2175b70d45e590bad928d2f2c85d6db48129642fc6d9a8bcb2175b65145e575b6d787d2f2c85d6dc481455d6c94b22cbcaeb64a5d145e5
  | 4, 0, 4 => 0x8ebad447d2f2bad928e45979642eb6bad13ab3675b25205e590badb8b44eac85d6e035179642eb6dad13ab4d902b0fa5e590badb890352c85d6db4e9b569b1b3e9a8bcaeb6cad13a96590badaec4482c85d6d94822966afc649a8bcb2175b7188905
  | 4, 0, 5 => 0x90badb88b2f2c85d6dc481f5642eb7336d20b367f324d45e590badac6a2f2ccdf8c95a27569316561f4bcb2175b50da5e590bad928b2f2c85d6dc4817969910561f4bcb3675b70d45e5
  | 5, 0, 0 => 0x90b25589d4a129a42ef64ab0fa5e690badbebe3e979a90eb672b0fa5e675b257cb84913da42eb70ab13a58690c39d6c935179a74eb70ab0fa5e690b25208c3e93da42fe6e2b0fa5e699badaeac3e979a74eb64af4fa5e675b25589d4b145a873a75b24da5e699b25589d49929a42eb6daf9245e6
  | 5, 0, 1 => 0x9abad92a13e979a42eb6ca28fa5e69d40d92ac3e965a42eb6da8cfa5e699c45d6c935179a66fc64ab13a5e699bad92ac4e979a68eb64ab0fa5e690bad92ac42179a42eb6cad0da5e690c1d92ac39179a42eb6d2b0fa5e690bf192b435179a42eb64ad0d45e690bad92ae4e929a710564ab0fa5e6
  | 5, 0, 2 => 0x9cbad92ac3e979a42eb649b4bc4f690c69b2ac35179a42eb6da9cfa5e690badccdb35179a4316682b0fa5e690b396aac3e979a42eb64b20da4f690c1592b63e979a42eb72ab0fa5e690c0d92ac4c179801217eb24da5e590bad92b448129a58eb64ab13a4a69b3ad92ac35179a42fe64ab13a5e6
  | 5, 0, 3 => 0x90badb87d35179a46eb64ab0fa5e699bad928a3e979a431a5627cfa5e6ac485d6c945179a42eb64a49145e690badaaac3e979a6aeb64af9245e690c49d6c936979a42fd64af9244f690bad92be3e945a66eb64ad0da5e690c41b2ac3e979a42eb64aecda5e690badb6be4e9f5a42fd6cab0fa5e6
  | 5, 0, 4 => 0x9abf5b6ac3e979a42c95a9b4bc4f699bf592ac3e979a42eb6cab1145e690bad96ac3e979a42c95724cfa5e690c520ac935179a42ec64ab0fa5e690bf192ac48179a98eb6cab13a4a69d3ad92ac3e95d9d6c95f2e1245e690bad928a2f1459d6c95f2e0fa55690c2d92ac38979a54eb64ab13a5e6
  | 5, 0, 5 => 0x973d192ac3e979a9b218dab0fa5e690badb6903e9a9a22ff64a80fa5e6a1c85d6d935179a74e864ab0fa59690c1592ac3e96da42eb64a41165e690c0992ac4e9618012175b25205159632558933e979a42e964aa0fa5e690c1592ac4d969a6aeb649f4d45e690bf592a13e979a431175b24da5e6
  | 5, 0, 6 => 0x90badb29d45129a893375b24d45e69bbf192ac3e979a42eb64af89e35690badb6b13e979a42f064ab0da5e690bedb2ac3e979a6eeb64ab0fa5e6a63adb2b43e979a42eb64a40da4f68ec460aac3e9798012175b24fa50500485d6d956241642eb69228fa5e690bf592be3e955a66eb64ab1145e6
  | 5, 0, 7 => 0x99bed92ac3e979a4315561f4ec5e690bed92ac49179a42d956275265e690bad92ac2f0d5a42eb6f2d8fa5e690bad92c445179a873375b24d45e699bad92ac3c179a96eb6bab0fa5e690bf1928a2f129a7b2164a4d145e690c1592ac4a955a42c93e9788a44690bad927d278fda42eb64a7514546
  | 5, 0, 8 => 0x90bad928a44179a9aeb6daf8fa5e69abad92b13e979a42fc649f4bc44690badb6903e93da42eb64ad93a54690bad92ad3e979a64eb64af8fa4f690bb592ac3e979a42eb64aed3a5e69c3ad927d35179a4aeb64ab0fa5e664ab0fa5e20901a42f064ab1025e699bad929d45129a42eb64af8fa566
  | 5, 0, 9 => 0x90badce9f3e979a42eb64af4fa5e69abad92ac4c1799d6c951258fa5e6a6469587d2f129a42eb64aa1245e690badb2ac49179a42eb672b1025e690c2d92a035179a431b6fab0fa5e690b25589d4a179a64eb64ab0fa5e690c1592be3e955a74eb64ab0d458690bad92c035179a66c956275265e6
  | 5, 0, 10 => 0x90c15c6ac3e969992ac4ea59264a690bd1927d351799d6c9622e0da5e690bad92ac2f0d1a42c949a49145e690c51d6c936979a42eb649f4bc37690bad92b448179a6ceb64af8fa51690bad92be36945a42eb649f4d65e69ac85d6c936979a42eb64b04d45e690bad92ac48979992ac47230fa5e6
  | 5, 0, 11 => 0x90bad928f3e979a430270ab0fa5e664ac15eac3e979a431b6da8cfa5e690bf992ac49179a42eb64a85245e690bad92b635179a42fc64af8fa4f690badb6903e979a42eb6cab0dc5e69abadb6ac49179a42eb64af8fa4f690bada8be3e979a6aeb64a40fa4f690bad92ac4a979a66eb64ab1245e6
  | 5, 0, 12 => 0x90bad92c835145a42eb6ca75145e690badb8be3e945a74eb71ab0fa5e69dbad92ac3e979a42eb64a98da5e699badb2ac4e929a42eb64a2cfa5e6943ad92ac3e979a42eb66ab0fa5e690c0592ac3e979a4ef064ab0fa5e690bd592ac3e979a42eb6d9b4bc4f690bf192ac3e979a42eb6daf9247d6
  | 5, 0, 13 => 0xa3485d6c948179a66eb64a75145e690bad92be4e945a42eb64af9164f6993ad92c435179a42eb64af5365e690bad926a2f1458013675b24d45e590badb6be56249a6aeb6d9f4d45e690bd192b13e979a42eb64b112048690badb2ac2f0cda42eb64ab13a4d690bf5beac3e979a4eeb672b0fa5e6
  | 5, 0, 14 => 0x96bad92ac3e979a42eb64b14d45e690bc5a0ac3e979a42eb6dab0bc35690badc8ac3e979a9b1b6dab0fa5e600485d6d945179666fc64ab0d45e6913ad92ac3e979a7aeb64ab0d05e69abf592ac49179a42eb662b0fa5e690bad92ac48151a66eb64ab0bc33690bad92c448145a430b75b25204f6
  | 5, 0, 15 => 0x8c3d9d6ac3e979a42eb64ad0fa5e690bad92b44e921a42eb6c2b0fa5e600485d6dc3517966eeb64ab13a5e690badbcac35179a42fc64b10d45e690badbaac3e979a42eb64ab0e05e690bad92b149179a431e71ab0fa5e690bad929035145a42eb64af9165e675b253a96451298012175b24bc305
  | 5, 1, 0 => 0x90c7dc2ac3e9799929649a28fa5e6993adaeac3e979a42eb71af4fa5e690bad94ac3e979a42eb682b10a5e690bad92ac4e1798012175b24d85e5a23ad92a53e979a42eb64ad13a51690bf192ac36979a6ceb64ab0fa5e690bad92ac36979a4315561f4bc0b690bad926a2f159a42eb64b11204a6
  | 5, 1, 1 => 0x90b6d7cb53e93d9d6c9622411c5e690badaebe3e93da42eb64a88fa5e690bad92b445979a42eb64af8e64f690bad92be45129a42eb6dab0fa5e6a6bf5b6ac3e979a66eb6cab13a5e69b3ad926a2f145a42eb6cad0d45e690c15bcac3e951a85218aab0fa5e690bad92ac40979a42eb64a2cda5e6
  | 5, 1, 2 => 0x90c2d92ac37979a4eeb64ab0fa5e690bad92be3e971a42eb6e1a8bc51690badb6ac481f5a6ceb64b10d45e69b485d6c935179a42eb6e2f8fa5e690c1592ac3e959a42eb64a98f05e690bad929027929a431c6e2b0fa5e690badaeac3e979a42eb64a40bc51690badb8ac3e979a42fc649a8bc4f6
  | 5, 1, 3 => 0x90bada6ac3e979a42eb6e310d45e600485d6c945979642eb6db10d45e690bad9eac3e979a42eb64af9244a690badc0ac3e979a64fb64ab0fa5e690badb66a2f1298012175b6d7c92590bad928a2f151a42eb64b11205e690badaeac481f5a3d1d82ab0fa5e6adc85d6c935179a42eb6dab13a4a6
  | 5, 1, 4 => 0x90bad92b445179a42eb6a1f4d45e690bad928a36979a42ee64ab0fa5e67fbad92a23e979a42eb64b10d85e690bad92b44e979a42eb64b10bc32690bad92be35145a42eb649a8bc30690bad92ba3e93da42eb6bad0fa5e690bada2ac3e979a42eb6e2d0fa5e690badaec4351798012175b2558435
  | 5, 1, 5 => 0x90bad928b35179a42eb692b13a4a690bad92ac48129a42eb64ad1245e60053636ac3e979642eb649b4bc29664b1d8cac3e979a42eb64b11165e690bad928b2f129a66fc64ab13a4a690bad92922f0d9a42eb692b0fa5e690badb68a3e979a42eb64a2cbc5169d41592ac3e969a42eb64a40fa516
  | 5, 1, 6 => 0x242eb64aacfa5e690badb6be4913da6cfe64ab0fa5e6
  | 6, 0, 0 => 0x90bad92be561f4bce0090b25587d2f0418012175b25686a2f348612eb64ab0fa5e790bed92ac3e9789eeeb64ab12c8a3e979e42eb64ab0fa672f3ca642eb64ab0fa5e7a1cadd6c9561f4bcf5175b25587d3b179e42eb64ab0fa602f3c860f0564ab0fa5e7a2c85d0c9561f4bcf599d3ad92ac3e979e42eb64a75248a2f3c85d6c9451f4bc257
  | 6, 0, 1 => 0xa1cd5d6c9561f4bce0090badb67d35179a42eb64ab1367d2f3c85d6c956274fa65790badb2ac3e9788cf2175b25586a2f145e42eb64ab1007d2f3ccdd6c9561f4d45e795485d6c9561f4bcf5890bad92ac35179e42eb64ab1246a2f3c85f8c956274fa4a790c01d6c9561f4bce0099bad92ac4e979a42fc64af9587d2f38026aeb64ab1245e6
  | 6, 0, 2 => 0x90c4dd6c9561f4aae0090bad92be3e945a42eb64ab1487d2f3c8628eb64ab13a5e700485d6c96217862d2175b25147d2f089e42eb64ab0bc421abc85d6c9561f4bc3d700485d6c9369789ed469d3ad92ac3e979e42eb64ab0fa5e003c8636db561f4bc4f790bada8ac3e97858f217ebad92ac49179e42e864ab14c7d2f3801d6c956274940d6
  | 6, 0, 3 => 0x90badb2ac4f9f4bcf2175b25587d2786de42eb64ad0fa5e0d3c85d6c96229cfa5e700485d6c949228bcd2175b65587d2f13de42eb64ab0fa7b2f3c85d6c95f1f49e1f790c5222eb649a8bce0090bf192ac3e8eda42eb64ab0fa5e173801d6c9561f4bc0c600485d6c956274b0d21853ad92ac3e979e42eb64a41147d2f3c9242eb64ab0fa5e7
  | 6, 0, 4 => 0x90bad92ac2f12866f21833ad92ac3e979e42eb64af8fa4f163d0e42eb64a28fa5e790bad929d4517894f5390bad92ac3e979e672175b25589d253b25589d4b24cfa5e7003ad92c4351781ad2175b25587d2f019e42eb64ab0fa5e073c85d6c9589f4bc29790bad92ac3e97830f3375b25587d2f119c00eb64ab13a96253485d6c95f1f4da4f7
  | 6, 0, 5 => 0x4d5d6c93e9a8bcd5190c1592ac3e969e42eb649f4d45e2cbc9a42eb64ab0fa5e799bad92ac3e9789ef419abad92ac3e979e42eb64b11585e19bc85d6c95626cbc5a790bad92ac3e9b4bce0090c45d6c936979800eb64ad0fa5e06b485d6c962275145e790c15d6d9561f4bcf217e325587d2f07dc012175b25585e11b485d6d95a1f4bc4a7
  | 6, 0, 6 => 0x90bad92be5627494f217e325587d2f0b1c00eb64ab0da5e06b486170564ab0e45e79ac85fac9561f4bcf2175b257cb33e979e42eb64ab0fa5e2dbc85d6c95fab0fa5e790c45d6d9561f4bcf2164ab10a833e979e42eb64a84fa5e27bc85f8c9561a8bc4a7a1c85fac9561f4bcf3575b6d587d2f13dc012175b25585e17b486230564af8fa5e7
  | 6, 0, 7 => 0x90bf192b4561f4bcf2175b2558952f155e42eb64ad1587d2f3d0dd6c956298fa5e790bad92ac3e9783ce009bbad92ac3e979a873a75b24fa6a2f3cce0aeb64ab0fa5e790bad92be561b49ef3375b25687d2f129e42eb64ab0fa5e01bc85faeb649f4d45e79ec85d6c956274b0f2182bad92ac49179e42eb64ab0fa642f3c861ceb64ab0fa5e7
  | 6, 0, 8 => 0x99c45d6c9561f4bce0064ab12c933e979a430f75b25447d2f3c8622eb64ab1245e790bad92ac3f9f4bcf2175b2584ac3e979e42eb64ab1105e19bcd5d6c956298fa5e790bb5d6c9561f4bcf2175b257c922f13de42eb64ab1047d2f3cfa42eb64ab0fa5e790bad92ac409f4bcf2185bad92ac48179e42eb64ab0fa5e0dbc8618eb64ab0fa5e7
  | 6, 0, 9 => 0x485d6e2561f4bcc0090c1592ac3e955a42eb7336d587d2f3d5e42eb64ab0fa5e790bad92c45f1a8bcf2175b25587d37979c012175b25585e1ab485d6c956220d45e700485d6c962228bcc00a6badb6ac3e9798014690bad926a2f33cde4eb64ab0fa5e790bad92c4589f4bcf217c3ad92ac3e979e42eb70ab0fa5e2c3c85d6c95f1f49e427
  | 6, 0, 10 => 0x9bc2dd6c9561f4bcf2175b25589035129ea32f75b25587d2f380242ed64ab0fa5e690bf192ac3e97822f2175b25587d30979e42eb64ab0fa5e08b801d6db561f4bc0d690bad92b44e9f494e0090bad587d2f055a42eb64ab0fa5e213801927d2f07c260d690bad92be5a1f4bcf2175b25587d2f03de872175b2558782f3d1a42eb64ab0ee5e7
  | 6, 0, 11 => 0x485d6c95a1f476d2175b25886a2f061e42eb64ab0fa5e1e380242eb6a2b0fa5e690c35d6c9451f4bce00993ad92ac3e979a42eb64af8fa5e2abc85f4eb64ab0fa5e700485d6c9621a876d2178b25587d2f07de42c956275267d253c85d6c9561f4e65e796485d6c9561f4bcf3090bad92ac3e979e42eb6daf9587d27bc85d6c9561f4bc087
  | 6, 0, 12 => 0x90c3dd6c9451f4bcf2175b257cac40979c012175b25586d1db485d6c95a2b13a4a79abf592ac3e9789ef2175b65589d2f129e992175b65587d2f3c85d6c9592b0fa5e790c45d6c9539f4bcf2175b25886a2f07dc012175b257a7d2f3485f8c956274fa5e790bad92ac3e97862e0099badb2ac3e979a42eb64ab0fa622f3cea42ed64ab0fa5e7
  | 6, 0, 13 => 0x99bad92ac4e97894f5990bad92be3e979e42eb64ab0da5e0fbc85d6c95a1a8bc4a790c0992ac3e978b0f2175b6d7cac3e979e42eb64ab0fa5e15bc85d6c9561f4bc2a790badb6ac3e97828e0090bad92ac4a979a42eb64ad0fa6d2f3801d6c92f0b03e0d69abad92ac3e9d4bcf2175b8d587d2f169e42eb64ad0fa5e0fbc8592be5aab0da5e7
  | 6, 0, 14 => 0x90bad92be561ccbcf21813ad92ac3e979e42eb64ab0da5e163c85d6c9561f4f85e79d485d6c95f1f49ef3d90badc2ac3e979e42eb682b0fa5e0e380242fc64ab0fa5e699c85d6c956274bcf2175b2588903e979e873375b25587d2f3d0242eb64ab0fa5e788c15fec9561f4bcf2175b257ca03e979e42eb64ac4fa5e27bc85d6c95a1f4bc2c7
  | 6, 0, 15 => 0x90bad92c0561f4bcf2188bad92b13e979ea52175b25587d2f38027aeb64ab0ec5e6003ad9296451f4bcd2175b2588be3e945e430b75b257c7d27bc861eeb64ab0e45e790bad92ac3e97804f2175b2568ac36979c00fd64ab0fa5e06b485d6d2561f4bc22790bad92ac3e978a4e0090badb6ac3e8eda42eb64ab0fa5e0eb80242c93e8ec3e136
  | 6, 1, 0 => 0x9d3ad92ac3e978b2f2775b257cac3e979e42eb6dab0fa5e163cc9d6c9561f4bc48790bad92ac3e998bcf2175b25587d2f14dea32175b257a7d2f380242eb649a8bc51690bb592ac3e97816f2175b25587d2f11dc013a90c55587d2f348616c956280fa5e7a0c85d6c956248bcf0b75b25589d4b179e42eb6dab0fa5e0fbc85d6c956240bc4a7
  | 6, 1, 1 => 0x485d6d03e9783ec0090bf1927d2f07da42f164ab0fa5e0e3c85e0c9561f4bc19700485e2c9561f4bcc0090bf192ac4e929a42eb64ab0fa5e24bc85d6c95b2b0fa5e790bad92b44e9f4bcf2175b25587d3289dea32175b257c7d27bc8628eb649f4d45e700485d6c91d8b03ed2175b257c8a3e979e42eb64ab0fa5e263c85d6c9621a8bc317
  | 6, 1, 2 => 0x485d6c95f1b49ed2175b2568ac4e979e430564ab0fa5e2d3c85d6c9571f4bc22790bf192ac3e97890f2175b25587d2f0b5c012164ab0fa5e093485d6c9561f4bc48790badb67d351789ef2175b25587d2f081e8d2175b25886a2f3c85d6c956224fa5e775b2590ac4b1f4bce009d3ad92ac3e969aa3217e325587d2f3c85d6c95f1f49e487
  | 6, 1, 3 => 0x90bad92ac3e97cbcf2175b25587d2f145eab2175b25587d2f38026ceb64ab0fa5e600485d6c9561b4bcd2175b6d589d3e979e752175b25886a2f380242eb64af89e2c690bad92a63e9a8bcf2175b2590ac3e945e7f2175b25587d2f3c8616eb64ab13a4a790bad9292451789ef2175b24fa5e25111c012175b25687d2f300242eb64ac4bc296
  | 6, 1, 4 => 0x485d6c956204bcd3a90bad92ac36979c012175b6d7c7d27b485d6c9561f4bc39775b2558963e97844e0090bad92ac4e919a42eb64ae9587d2f3d5242fc64ab0fa5e790c2dd6c9621a8bce0090bf192ac2f0b1a42eb64af8fa4f1dbcce42eb6cab0fa5e7a1c85d6c956260bcf3c90bad92c435179e652175b25587d2f3d0e74eb64ab0fa597
  | 6, 1, 5 => 0xa2c85d4c9561f4bcf217eb25587d2f155dd6c9622b13a962f3c85d6c962ab0fa5e790bad92ac4e9f4a8eeb64ab13a962f129e42eb64ab0fa5e273c85d6c9622f8fa4f7993ad92ac3e9a8bcf2175b25587d2f05de42fc64ab0fa5e1dbc85d6c956240fa48790bad92be3e97852f2175b257c7d27929c012178b24fa5e0fb485d6c95f1f4bc517
  | 6, 1, 6 => 0x485d6db5f1f4bcc0090badaeac3e979a42eb64ab13c7d2f3d4642eb64ad0fa5e790bad92ac3e97896f21843ad92ac3e979c012175b71587d2f300242eb71ab0fa5e690bf192c4561f4bce0090bad92b44e929a42eb64ab0fa5e02bd4642eb64b10d45e790bad92ac4c9f4bce0090bad92a23e979a43057cb25587d2f3c85d6c9561f4bc4a7
  | 6, 1, 7 => 0x9d4d5d6c9561f4bcf2175b25687d2f145e7b2b75b25587d2f3c85d6c956240fa4a700485d6c93e9783ad2175b25886a2f145e430b75b24d45e27bd0a42eb64ab13a4a790bad92ac431f4bcf2175b25687d2f121ea32175b25586d2f3c8592ac3e9788c45790bad92ac3e978ace0090bad926d2f07da42eb64b10d45e243c85d6c95f1f4d44f7
  | 6, 1, 8 => 0x90bad92c43e9b4bcf2175b25587d2f029e7b2188bad926a2f3c85d6c9561f4bc21790bad92c43517876e0090bad92c448179a42e864ab0fa5e05bd4642eb6dab0fa5e79b3ad92ac3e978a2f2175b2572ac3e979c012175b25685e16300242eb6d9f4bc1f690bad92ac3e97850f2175b6568ac3e979ea33a82b25587d2f38024eeb64ab0fa5e6
  | 6, 1, 9 => 0x90bad92ac4917884eeb64ab1208e3e979e42eb64ab0fa712f3c85d6c9622d0fa5e790bad92be3e93c32f2175b2590be3e93de430b75b25147d2f3c85d6c9561b4bc3b790bad92ac4d1f4bcf2175b25587d34979e42eb64b10d45e25380242eb649f4bc4c690badb6ac3e97890f4290b2558933e979ea32175b8d587d2f3c85d6c95a1f4bc3b7
  | 6, 1, 10 => 0xadc85d6c9561f4bcf2175b6d587d2f0ede430b75b25588a2f380242eb64ad13a5e600485d6c9561944ed2175b71587d2f145e8f2175b25587d2f3c85d6c9561f4bc19790bad92c8561f4bcf3675b2588ac3e979e42eb64b11586d2f3cda42eb64ab0fa5e700485d6db5617858d5690bad92ac3e969e42eb64ab0da5e253c85d6d7561f4bc487
  | 6, 1, 11 => 0x90bad92ac3e97874f2175b7188ac3e979e42eb64ab1207d2f3d6a42eb64ab0fa5e790bad92b4561a8bcf2175b25587d31979e42eb649a8bc4f25380242eb64ab11033690c45d6c93e9786cf2175b24fa6d2f13de42eb6db11587d2f3c85d6c9561b4d45e790bad92ac3e9784cf2175b25587d2f095e752175b2558782f3d6642eb64aa8fa5e7
  | 6, 1, 12 => 0x90bad92c45f274bce0090bada4ac3e979a42eb6bab0fa6a2f3c85d6c9561f8fa5e790c45d6c95a1f4bcf2175b2590c435179e42eb64b0d587d2f3c85d6c95f2b0fa51790bad92ac369789ef2185badb2ac3e979e42eb6dab0fa6a2f3c85d6c9561f4bc237004cdf8c9561f4bcd2175b25687d2f13de42eb692b13a7d2f3c85d6d7561f4bc4a7
  | 6, 1, 13 => 0x90bad92ac3e97870eeb64b218eac3e979e42eb64ab0fa5e00bc85d6c9561f4bc24700485d6c95624094d2175b2558873e979e42eb64ab0fa5e1f380242eb649f49e19690bad92ac3517838f2175b25889035179c012175b65687d2f300192ac3e8ec260d690c45d6c95f1b4bcf2175b25587d2f0c9e42eb64b21586d2f3c85d6c9561f4bc357
  | 6, 1, 14 => 0x242eb64ab0fa5e0b380242eb649a8bc186
  | 7, 0, 0 => 0x48592be5aab0fa5e700486230564ab0fa5e700485d6c9621f4d45e700485d6c9561f4bc3679d485d6c95f2b0fa5e890bad92ac4e9f4bc2c800001d6c93e9783e0d6a1c85d6c9561f4d45e8a1c85d6c9561f4bc59890bad92ac4e9f4bc1f890bad92ac3e988bc1f800485d6c956274fa4a790bad92ac481f4d45e890c51d6c9622b0fa5e8a1c85d6c9622b0fa5e80042dd6c9561f4bc0d7
  | 7, 0, 1 => 0x485d6c956214fa5e7a1c85d6c9561f4bc4f80048616eb64ab0fa3b700485d6c9561a8bc4a7a8c85d6c9561f4bc5a800485d6c9561f4da5e700485d6c956248bc4f7004ea42eb64ab0fa3b790bad92ac3e9783e1c800485d6c9561f4bc097a1c85d6c9561f4bc078004c642eb64ab0fa5e790c2dd6c95f2b0fa5e800485d6c9561f4bc18700485d6c959ab0fa5e70000192ac3e978260d6
  | 7, 0, 2 => 0x90c2dd6c9561f4bc2c80000242eb649f4761f6a1c8622eb64ab0fa5e8003ad92ac3e978760d700485d6c9561f4bc55797c85d6c9561f4bc2c8a1c860aeb64ab0fa5e890c2dd6c9561f4bc1f800485d6c9561f4ec5e70048592be561f4bc137a8c85d6c95f2b0fa5e800485d6c9561f4bc1b700485d6c95a2b0fa5e700485d6c95f1f4bc1f79ac85d6c9561f4bc4f89d485d6c9561f4bc1f8
  | 7, 0, 3 => 0x48622eb649f4d45e70056642eb64ab0fa5e700485d6c9561f4bc31700485d6c9561f4c45e700485d6c95f2b0bc2c70048592ac3e9783e137a8c85d6c9561f4bc1f8003ad92c4561f4bc0d700485d6c95f2b0da5e7003ad92ac3e978940d70000242c9561f4761369d485d6c9561f4ec5e890c5222eb64ab0fa5e80054674eb64ab0fa5e70054642eb64ab0fa3b700485d6c9561f4bc427
  | 7, 0, 4 => 0x90bad92b3561f4bc3b800485d6c9561f4bc1c70000242fc64ab0fa5e690bad92ac3e9787636890c2dd6c956274fa5e890bad92c45f2b0fa5e80051a42eb64ab0fa5e790bad92be561f4bc4a890bad92ac4ea28fa5e80000242eb64af8fa4f600485d6c93e9783e1b7003ad92ac3e9a8bc0d700485f8eb64ab0fa5e790bad92be561f4bc3b800485d6c9429f4bc1f700485d6c93e978581f7
  | 7, 0, 5 => 0xa2d0e42eb64ab0fa5e800485d6c9561f47633790bad92c4561f4bc1f800415d6c9561f4bc0d7acd4642eb64ab0fa5e890bad92ac3e978941f890bad92c4561f4bc188004f242eb64ab0fa5e700485d6c93e988bc1f7004be42eb64ab0fa5e790bad92be561f4d45e800485d6c9622b0fa3b790bad92ac3e978761f800485d6c9561f4943b798c85d6c9561f4bc3b890c3e0aeb64ab0fa5e8
  | 7, 0, 6 => 0x4ea42eb649f4bc1f700485d6c9561f4bc4870000242eb64b10d45e6ab4ea42eb64ab0fa5e890bad92be561f4bc4f800485d6c93e9783e1c790bad92ac3e9a8bc1f890bad92ac3e9785827890bad92b4561f4bc4a8a1c85d6c9561f4ee5e80055a42eb64ab0fa5e700485d6c9561f4d43b790bad92ac3e978942c890c4dd6c95f2b0fa5e800485d6c956220fa3b700485d6c9561f4f45e7
  | 7, 0, 7 => 0x242eb6dab0fa5e600485d6c956284fa5e790bad92b1561f4bc2c80054642eb649f4bc1f7ac48616eb64ab0fa5e80050a42eb64ab0fa5e7ab54642eb64ab0fa5e89d485d6c9561f4bc0b8a8c85d6c9561f4f45e800485d6c9561f4bc5170000242eb64ab0da5e690bad92be561f4bc19890bad92c85f2b0fa5e80048616eb649f4bc1f70000242eb64ad0fa5e600485d6c9561f4bc0b7
  | 7, 0, 8 => 0x9e485d6c9561f4d45e89d485d6c9561f4d45e8a8c85d6c9561f4bc3b800485d6c93e978761f70000242eb64978581f600485d6c9622f8fa5e79d485d6c9622b0fa5e89d485d6c9561f4bc4a890c2dd6c9561f4bc3b890bad92ac3e9789e4289d485d6c9561f4bc3b80048616eb64ab0bc2c700485f8c9561f4bc4a790bad92ac3e9a8bc318004be42eb64ab0bc2c7004ea42e864ab0fa5e7
  | 7, 0, 9 => 0x90bad92ac3e9a8bc48800485d6c956178942c79d4860aeb64ab0fa5e800485d6c9561f4bc19700485d6c9642b0fa5e790bad92c4561f4bc51890c2dd6c9561f4bc4f8a8c85d6c9561f4d45e800485d6c95f1f4bc4f700485d6c93e9a8bc1f790bad92ac3e97894488a8c85d6c9622b0fa5e800485d6c9621f4bc1f7a8c85d6c9561f4bc4a800485d6c93e978941f70048616eb64ab13a5e7
  | 7, 0, 10 => 0x90bad92c8622b0fa5e800485d6c9561f4761f7004c642eb64ab0fa3b790bad92ac3e9789e4a800485d6db561f4bc4f700485d6c95f2b0fa3b7a8c85d6c9561f4bc04890bad92c4561f4d45e890bad92ac3e9a8bc4a890bad92ac3e9a8bc3b800485d6c956240fa5e790bad92c4561f4bc4a89ec8622eb64ab0fa5e890bad92c4561f4bc3b800485d6c9561f4bc04790bad92ac3e978943b8
  | 7, 0, 11 => 0x485d6c9561f4bc5a790bad92be56274fa5e890bad92ac3e978581f8
  | 8, 0, 0 => 0x90bad92ac3e9a8bcf2175b2588ac3e979e42eb64ab0fa5e253c85d6c9561f4bc3b70048592ac3e97826d5190bad92ac3e979c012175b24fa5e0fb48616eb64ab0fa5e79d485d6c9561f4bcf2175b25587d2f07dc012175b25587d1db485d6c95f2b0fa5e7
  | 9, 0, 0 => 0x242eb64ab0fa5e6
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
  | 0, 0 => 0x1c338fc0000000001f00000041087c00000003fff00000000c7000000000001f00000000ff800000000325f
  | 0, 1 => 0xdd000368000386000e20000007fffffc000006e8dbf000007ffff8000001f1fe7f00000645c97c00001813040
  | 0, 2 => 0x7c2108210420007c1f83f07fc1f07e0fc1ff003ff800fffc00ffe00001f003ff800fffc00ffe003fff
  | 0, 3 => 0x39ce19c338fce738670c000318c118230fcc6304608c2000000000007ce738670ce3f39ce19c338802108210421f
  | 0, 4 => 0x7c00000000000fffe3fc7f9fffff8ff1fe60ce722e45c97f39c8b917240c6302604c100e738670ffff
  | 0, 5 => 0xfffe3fc7f9ff39fff917fffce7e3e45f9ff39c8b91725fce722e04c10339c8a00001fc6302604c1000000000001f
  | 0, 6 => 0xc631e63cc70318c798f31c0318dd1ba3680c63746e8da0318dd1ba3680000700e0180fffe3fc7f9ffdef0de1bc60
  | 0, 7 => 0xc631e63cc77fffffffffffffffffffffffffffffffffffffffffffff83fffffffc000ffcdd7ff3683def7defbde0
  | 0, 8 => 0xfffffffffffffffffffffffffc007ff000318c798f31c0318dd1ba36ffffffffffffffffff8000003ff001ffc000
  | 0, 9 => 0xce722e45c900e738670ce3f00000000007c0000000000000000000000000000000000
  | 0, 10 => 0x1f000000000000e738670ce20
  | 0, 11 => 0xfffc0000000001f000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 12 => 0x380003fff8ff1fe7fce722e45c97f18c0981305fc6302604c100e738670ce3f08420841087c00386000e3f
  | 0, 13 => 0x318c11ba3080c03706e0d800001c0380600210f21e439f0001c038c700000700e01800001c038000000070000000
  | 0, 14 => 0x318dd0380600c6374000000318dd0000000c63006e8c003181c1ba0600c60006e8000318001ba0000c63746e8da0
  | 0, 15 => 0x318fd9ba3efcc63746ebfff318dd1ba3680c63746e8180318dd1ba0000c63746e8000318dd1803000c63740e0180
  | 1, 0 => 0xffffffffff8318c798f31c039cfd9fb3efce73f67ecda039c001fb0000c63746e8dbf39cfd9fb3e80c6ffe6ebfe0
  | 1, 1 => 0x1c0380600000700000000001c0380600000000e00000001c0380600000700e0180fffffffffffffffffffffe0
  | 1, 2 => 0x318dd0000000c6374000000318dd1ba3680c60006e8000318001ba0000c63746e8da0318dd1ba3680000700e019f
  | 1, 3 => 0xc0300600c000e73f67ecfbf318dd1ba36fcc63746e8da0318dd1ba3680c63746e801f318dd1ba0000c63746e8da0
  | 1, 4 => 0xc631e038060318c78000000c631e000000318c798f31c0c630063cc003180718f0180c601c63c0603180018f0000
  | 1, 5 => 0xce40067d000339cfb9f73c0c633ee3ccf0318c798f31c0c631e63c060318c798f0000c631e600c00318c780e0180
  | 1, 6 => 0xc630063cc00318c798f31c0c600063c000318c798f31c0ffffffffff83def7defbde0ce73ee7dcf7f39cfa000000
  | 1, 7 => 0xf78007be000318c798f31dfc631e63cc70318c79803000c631e63cc70318c780e019fc631e038060318c78000000
  | 1, 8 => 0xf7bdf0000003de001ef8000ffffffffff83def7defbde0f7bdf7be3683def7def8000f7bdf0000003de375ef8da0
  | 1, 9 => 0xf83e07c0f803e7f87f0fe20f9be17c2f883e1f83f07e00f83e27c0f903e0f81f17e40f83e07c0f803def7defbdff
  | 1, 10 => 0xf83e07c0f803fef8df1be60fe7e2fc4f903f8f89f13e40fffe3fc7f983f9f8bf17e40f9fe1fc3f803e6f85f0be20
  | 1, 11 => 0xf83e07c0f803e0f81f03e00f83e07c0f803e0f81f03e00f83e07c0f803e0f81f03e00f83e07c0f803e0f81f03e00
  | 1, 12 => 0xfe3fe7fcff03e6ff5febfa0fe3e27c4f903e0f81f03e00f83e07c0f803e0f81f03e00f83e07c0f803e0f81f03e00
  | 1, 13 => 0xffcc17ff3083ff083ffc200ffc007ffff83ff001fff1c0ffc007ff0003ff0018f0000ffc001ba0003ff000000000
  | 1, 14 => 0xfffc37fff183ffc8bfff25ffff22fffc103ffc09fff040ffce1fff38ffff386000000ffcc17ff3083ff387ffce20
  | 1, 15 => 0xffc000000003ff001ffc000ffc007ff0003ff001ffc000ffc007ff0003fffffffffffffffffffff83ff375ffcda0
  | 2, 0 => 0xffc1c7ff0603ff387ffce3fffc007ff007fff001ffc000ffc007ff0003ff001ffc000ffc007ff0003ff0006e8000
  | 2, 1 => 0xffcdd7ff36ffff375ffcda0ffc1c7ff0603fffffffffe0ffcdd7ff3683ff375ffc180ffcdd7ff0003ff3758f0180
  | 2, 2 => 0xfffe2ffff903fff85fffe20fffe07c0f803fff7dfffde0fff1e7ffc77fffc79fff1c0fff1e7ffc703ffc01fff000
  | 2, 3 => 0xfffe07fff803fff81fffe00fffe07c0f803fff81fffe00fffe07fff803fff81fffe00fffe07fff803fff8bf03e00
  | 2, 4 => 0xfffff9c33883ffffe10421ffffff8003683ffffe000e3ffffff8003083ffffe000e20fffff8000003fff81fffe00
  | 2, 5 => 0xfffffe45c97ffffff813040ffffffc7f983fffff917240fffff9c338ffffffe608c20fffff800007fffffe000000
  | 2, 6 => 0xfffff8000003ffffe000000fffff8000003ffffe000000fffff8000003ffffe000000ffffffffff83ffffff1fe7f
  | 2, 7 => 0xfffff8380603ffffe7ecfbffffff9ba3683ffffe0e0180fffffe04c103ffffe00001ffffff8000003ffffe000000
  | 2, 8 => 0xffffffbef7fffffffefbde0fffffe3cc77ffffff8f31c0fffffe3cc703ffffe6e8dbffffff9ba3683ffffe0e019f
  | 2, 9 => 0xffffffc0f803ffffff03e00ffffffc0f803ffffff03e00ffffffc0f803ffffff17e40ffffffc2f883ffffff0fe20
  | 2, 10 => 0xffffffff0603fffffffc01fffffffff0003fffffffc000ffffffffff83fffffffce3fffffffff0003ffffff03e00
  | 2, 11 => 0xfffffffff783ffffffff1dfffffffffc703fffffffcda0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xc318b40000030c62d00000041083000000003fe700000000e708000000016e700000000a40000000001246
  | 0, 1 => 0x288000a40000000000000000007dfffbc00001f7ffef00000510a40000000b1d66f00000245493800000811042
  | 0, 2 => 0x84208410870000000000000741282501681704608c039003ef800ffdc00fbe0016f7003aa800ed5800ba6002f35
  | 0, 3 => 0x18c618c318f46318630c01818c618c318f44210420842118c618c318f42108210421c0000000000002108210421c
  | 0, 4 => 0x4a522a4549790840881104218c618c318f400000000000084208410870000000000000000000000006318630ffff
  | 0, 5 => 0x4a522a45497929eaa917b5e4a563a4559fd2948a91525e4a522a0441492948a91525e4210220441096b58eb1d67f
  | 0, 6 => 0xa5298530e70a94a614c2900b5ad95b2b48694a616cad21a5298530a40294a614c29005ad63ac759fd4a50ca19463
  | 0, 7 => 0xbdef9df3bcf6b5ae35c6b1ca53bad30ed5a94a614c3fe7a5298530a40294a614c0000a5298530a40294a614c2900
  | 0, 8 => 0xffffbff7fdffbdeebdd7b5eef41077500239ce69cd3942ef7baf75ed7af7be77cef3dbdef98200042f70417cc008
  | 0, 9 => 0x4210620c4309084188300001084508a12846319632c6bd18c658cb1af4421142284a110845008020000010020080
  | 0, 10 => 0x5ad6780802416b51cb3d4eb5ad062cf43296b114b3c4a95ac042cf02216b48ab3d25e5294728e538d084188310c2
  | 0, 11 => 0x5ad67acffffd6b59eb3d6ff5ad67acf58716b59eb3d0da5ad67acf12e56b59eb3c0185ad67a0c43496b59e2284b1
  | 0, 12 => 0xa501453802016b59eb3d6ff5ad67acf5bfd6b59eb3d6ff4210620c43096b59eb3d6ff5ad67acf5bfd6b59eb3d6ff
  | 0, 13 => 0xb58515ba1086d6b756eada1b5add5bab686b5af35e6b9ca529c538e70a94a714e2980a529c538000294a700a0080
  | 0, 14 => 0xb5add538a602d6b742a84a1b5add0280202d6b756eada1b5add5bab686d61556e84a1b58145ba0202d6b656ead21
  | 0, 15 => 0xb5afddbabed6d6b756ebfe7b5add5bab686d6b756ea980b5add5ba1286d6b756e8000b5add5bab686d6b756eada1
  | 1, 0 => 0xa529c538a60294a714e2980bdefddfbbef6f7bf77eedb9bdc105fb0022f7bf77eefbdb5add5bab686d6b756eada1
  | 1, 1 => 0xffffff3ce74bffffe080010fffdf7fff7afff041ffc008f7bdf7bef78f9ce79cf39c2bdefddfbbef6d6b756eada1
  | 1, 2 => 0xfffff8aa12c7ffffe080010fffdf7fff7afff155ffc4a9ffc107ff0023def7defbde3f7bdf7beb687fffffffffff
  | 1, 3 => 0xe038c718e603fffffffffffffffffffffffffffffffdfbffffffffb6e7fffffffd6ffffffffff0063fffffefbdf3
  | 1, 4 => 0xe739e538a6039ce788b10c2e739e02802039ce794c2900e739e73ce70b9ce79cf39c2e729c73ca6039c459cf10c2
  | 1, 5 => 0xef41077d00239ce79cf39c2e739e73ce70b9ce79cf39c2e739e73ce70b9ce79cf0000e739e73ce70b9ce79cf39c2
  | 1, 6 => 0xffffe7ffff3bfff7dfffdebffc107ff0023def7defbde3e739e73ce70b9ce79cf39c2ef7bef7def7bbdefa080010
  | 1, 7 => 0xf79577be538ffffffffffffffffffffe76bfffffff3fd6ffffffbef7cfffffffffffffffffdbab6c7ffffe080010
  | 1, 8 => 0xfffff8200043ff041ffc008f7bdf7bef78fdef7defbde3f7bdf7beb687def7def8000f7bdf2ae538fdef7defbde3
  | 1, 9 => 0xf8be97d2fc97e0fa1f43f04f83e87d0fc13e0fa1f43f04f83ea7d0fd1be0fa1f43f04f83e87d0fc13fffffffffff
  | 1, 10 => 0xf83ec7d8fe13eafadf5bf67fa7eafd4fd5be8fa9f53f46f83e87d0fc13e0fa1f43f04f8fe9fd3fc73e2fa5f4bf25
  | 1, 11 => 0xfafee7dfff3bebfb5f7ffadfafec7dffe33eafbdf7bfe7fa3ee7dcff1be8fb9f73f04f8bed7dafe97e2fb1f6bf84
  | 1, 12 => 0xffbff7feff9ffeffdffbfe7fa3ee7dcff1bebfbff7ffbdfafeffdffc73ebfbff73fd6fafeffdafed7ebfbdf7ffef
  | 1, 13 => 0xffc107ff0023ff041ffc008ffc107ffa423ff041ffe908ffc107ff0023ff041ffc008ffc107ff0023ff040bbc008
  | 1, 14 => 0xffd537ff51afff4cbffd25effd32fff416bff449ffd04affc71fff18f7ff1c6080010ffc517ff10a7ff041ffc008
  | 1, 15 => 0xffd778200043ff55dffd4ebffd167ff432bff155ffc4a9ffc147ff0223ffbe7ffef3dffe987ffa423ffa61ffe908
  | 2, 0 => 0xffe9c7ffa623ff5dfffd6ffffd77fff5bffff5dfffd4fbffd77fff436bff5dfffc4b9ffd77fff0263ff5df6e84b1
  | 2, 1 => 0xfffffffffffffff7dfffdebfff9e7ffe72bffb75ffeda9ffedd7ffb6a7ffb75ffe988ffedd7ff12a7ffb75cf2980
  | 2, 2 => 0xffff87fffc33fffe5ffff2dffff87fffc33fff7dfffdebfffffffffffffff7dfffdebfff9e7ffe72bffe71fff988
  | 2, 3 => 0xfffffffffef7fffffffff1cfffffff0fc53ffffdffffefffffe7ffff3bffff5ffffadffffc7fffe33fffebfc3f14
  | 2, 4 => 0xfffff8200043ffffe18421cfffff820b6c7ffffe080635fffff82010c7ffffe080010fffff8200043fffffffffde
  | 2, 5 => 0xfffffa65497bffffe891052fffff8200043ffffe080010fffff8e318f7ffffe288431fffff8e318f7ffffe288431
  | 2, 6 => 0xfffffaef12e7ffffeab94f3fffffa2c434bffffe8b0090fffff8aa12c7ffffe0a0090fffffd30a443ffffeb9d67f
  | 2, 7 => 0xffffff3ce74bfffff7eefbdfffffdbab6c7fffff4e2990fffffa2c434bffffebbd6fffffffaef53efffffebbd0da
  | 2, 8 => 0xfffffffffffffffffefbdf3fffffffffffffffffefbdf3ffffff3ce74bfffffffffffffffffbef7cffffffffffff
  | 2, 9 => 0xfffffffffc73fffffffbff7fffffffcff5bffffffebfb5fffffff8fe53ffffffc3f14fffffff2fcd7ffffffc3f14
  | 2, 10 => 0xffffffffa663fffffffd6ffffffffff436bfffffffc4b9ffffffffa463fffffffc63dffffffff0063fffffffffde
  | 2, 11 => 0xfffffffff7effffffffffffffffffffe76bfffffffedb9
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 46 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 46 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 348 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 348 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 348 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 348 then wireAt i else 0
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
  | 4 => 44
  | 5 => 353
  | 6 => 591
  | 7 => 278
  | 8 => 14
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xe02176271f7065d3
  | 4, 0 => 0xf9cca47fe131a01ed5c13b9fab2767b99af04ac98b43864a8159002d7a74107476b5d53474ab97f773a65e596b81b2ba61de1f935ac98a7e514828654f8ecde64c1226c6410a025d3c28f140397e5b8232bf047c2bf0200b2979d5202851f9672820e76f2812d637261f18da231b843c2022e19b1fac02be1c72d6be1bdec1a41b6fdf4b17aec35712c8a8d60ddbcdea0abee4dd09828b1f07ba92a8077a7fcc0666f190026ecb1202290a3b00c5976c
  | 5, 0 => 0x1467f41e143f166c136c633412ee29ce12dc22d31283aafd126c1aa4122204e311cbdf521081e5dc1017aefe0fe79a5b0fbaaf080f507ee60ee0af2a0eb6e6710e72868d0e5f4a880e41792b0d7087f90d1bca3e0ccf58020cb6d1e10c8ecef20c40b1c80acbca020a9322fd0a6c0c690a3894d009a0e20e0933ef3c08627bfd08442f23084109d2083ca64d07e998db07a2eecc0786c353077a7fcc06ce7e4f069f8183069dcc0d0660383c062efed5062884a8060821c405de78ac04b5357504b25ef4049e8978046952c20466c0b703aea7f40396e0460269762b025216e80232f59901373cfc00f1012e00e3021600c21760007660d4002d25370025d314
  | 5, 1 => 0x2873acb2280064ef27dbafe027a8a3f5275dc42026d75d4726ce316a26bb18ee269dd811269c6ab025f38e1325dd3ce825b8c16725b3f4f0251f1c0e2481a3a2246d800b246a74af2466684624030d0d23e037f722f58cdf22e5ad7d2192e357216f7618208266af20150acd1ffac6c31fb133ec1f831b211f37282e1f3527b21ee7445e1eacf24f1e94ffdd1e4d6ab61e1b8df81dd0a2e51bc24f8a1b86f9701b5300e41ac839e21aa0e7a51a4343fe1a1f0ef61a150dd219f7c2b718c4748718ab355518238c6017b9de5117404ccd173c6c1616ecceb916be551a168af95516710e0715e64b2715dac5e9157866411571e6df1551b0071504578414b54a2d
  | 5, 2 => 0x42a993a4428dc58a426aeb7341f5400941e5741440c5dc4840c083b340623679405fd8363f13eb023ec88a5d3e3e9f083c96218e3b5bfbd43afb2c5d399456f73984106d37ff5d2837ee1a0a3780d5ff3761c3f3371a9ae03706219e36b2cfc63669347b35b7874d358ad8943556e60734eec54d343096ad334cc77932eea4d332df0cd032d0be9d32bd4e68329cbd1c3257a9653158aaac3128b775310faf1630d6e2d8306d1a2130378bbb3017398e3007167c2ff0424a2f9289702f4d460d2f17eea22efd25b42e72cb552e088e562e0236cb2de1c60c2d6e8c932bcd5b7f2bac62dc2a7f696e2a3198e02a2de0082a0d6cad298c9cf128a684df288ddde4
  | 5, 3 => 0x65425012650bfc2564f389686404f01663669d9563496cf262eecc5a627a1b2362132f8d611f9d87601b19215fc3178d5f9defbf5f9775545d1f8edf5cde6a805c7fa2ba5b3bed485b1b10095b02b2bc5a183dfc59af1a5d58c4eceb587328fb5807e47456510a2055d17752559c044953b73abb530174a6517d3ebd512e278450d1414c50ab4803500307f24fa7655e4f5a105b4f52da884edce9e04eb84ae04d7c05aa4d74a6104d6ed5974d1acf0f4bf022ce4b9d64f24b1885324ae0bcd24a9560054a55e64349e903f1495f0bd448837594484f616c45d91ef14558c85444f7caa244bff37944b733b344b3865943d2fd9f437660e54351a0fe42b779a3
  | 5, 4 => 0x9b34369199b781689815970197bdb0d196e49edc96d4085496bbcf6b939811f693734f309317a84c91eb64cd91d33365910da3498e17d22f8c74e0b08b34e3cc8aa43c5689fc215389d859b0882be4e1872b4b2685a2ad5a828343a28211e0e081c1d1c68073089c7f24c13b7e7abe7f7d7edffd7ce4b67e7b549f147a85129f7874022977d537f576fa47eb76d6b2d174601fa7744cff9874202dc47268845a71b7b3637196e991715fe455715e1b216e4f5e636e46e8416e23ca026dcb47606dbb437b6d08bbf36c8241216c4e80596b5c09196a9a88796a7db0b069e1849069d0a4b0693cdad367c4420366b978d06623177d6615995965d5a92c6586cff7
  | 5, 5 => 0xf8047bd7e5a6c51de31215c3e20a5746e00265b6defa3987dbe50096dac5427bcf332cbece83eb81cda636a9c6960ac2c4f7a12bbedd9d2abe1d9c41bd17a6d4bc7e0e31bae36e25b5fe9dcab5d6ae26b1e026e2b1b186bcb07e6010adbb3dbfad286bf6aaa6ea6aaa2b2e5fa9b6265aa8db08d3a5ff58e0a18c04bf9ee376349bee2635
  | 6, 0 => 0xab8b2690aa0caca0aa03d900a5ed5a50a2deef809ea0c3209a252ac0966c06b0941c54b09353328092d20e8092be94c09199978090dfc8408fc683508a5e43f088bad5208739b7008683c45085c29ce0856ca26083843fe080a8eb707a19af20787d7a50772bb3e075d2466075cc27d0737882a072385510711d49e06cd9ad4069167b0067d84ff06540181060f596e05e8faa005b43f60055f0adf050dc1e804d32ad804bca6590423431103f1b95203ae4e990375c6cf035eb4ec03476202033b05b502c7a620029bda2f028da25d0285087d025cb6660257db27025216e80219fdf801a6e4da0185b85101521d0b0146c416012a584000f5a3d2006c2684
  | 6, 1 => 0x1507f5eb14db18b514c15aa41437977c1413d60813ea83c213d5001c13967e2f139302bf138cad00137dbbb11350ed141317dd2b130a5a8912ed399912c3605312b8ab4112a8e676125d0b7e124d6d63121c5c8e118eca211187183a115b67ca1142fa41110f8d8e10ef472310bf6ca610b7c9a8108ef5b9104243571037e7200ffdfe370fec104b0fde41e30f932aef0f6345690f21afa70eff00d20e7e15130e5be2f20ddd4aa00dc513710da6941f0da46fb90d9cbe430d74550a0d743a280d2d22890cf439bf0cedf22c0ca165b80c52793e0c498d8c0c04ca010bf303a40ba77e000b8ad6cc0b2c8ce60b29023d0b28f6400af23e1b0ae34fac0abb3de5
  | 6, 2 => 0x22d85c9a22d2ddb12192e3572177d42821639b7e211fa54b20e7b2b020a84c14206a118a205b0a2a203ca2471fc4f9a61f9547f51f4451831f06a07c1f0286b71ed7e87a1ed5cf831dc5ecc71d9c94d41d825b1b1cf670511cc101ab1ca0b1831c84fb571ba9084a1ba7dc291b61a0cd1b609a391b42406d1b3c1cc21b2c09fb1b29bf4b1a87fcc01a36d8e619e220af19ba301a1977419918ef4baf18e16a7f18c4770b18ac994f186cfbda185955ec17bcd81e17bba65117b77a5217aeb250177154d6175d1cd3173643a81729918f172938d717206e3516bcc03716995adb168bc85d1673385e15f022ce1575dcf91561a43a15608d7b152f0dc01526687d
  | 6, 3 => 0x32def36c32aa334831f21e3331b9d9ef31b603e131b1ab293177ea8830d5282030ba24d83067a3352fd3b15e2fc6445a2f8141142f523f1d2ee8e9622e9c408b2e8108342e2eb6002da94f942d7296ec2d3ff5e92d11d26b2cf8cd042cc746d12c611b6b2c2fc9bd2b27b74c2b1903882b09ceab2ac54d632a6bc7352a3198e029dcd53d29cba47729342757291385ac28e1d56328d3f68428c04ce028a740fe281909f62726069d2713cf002707a0fd26d16b4626bb2fef26ac92fa26aabd36269c6ab0262a32f4260ba30225dc2a28255fdd5125471fea253ef9ad250aba5724fedf5924f27cee24ae713a241ffd06241b265d23e037f723ded5ff23a4af75
  | 6, 4 => 0x3f7f6a493f62ae583f48c35c3f227ddf3f0151163e9b9b153e2f1fca3db4e4813d9d48353d946b583d6b77133d60158c3d2562093d0b3b903ce437ac3c84ae723c7acf473c7a7c2d3c6b32503c346cd83b8aa58d3b3af5c13b13a8a83ac1b5df3a822ece39ff1f0a39b8a2b739a6d4e63996a260396f572d394f142039334aec390153ab38f51e0738eec90038e8b0de38c8629238afba57388012b137d8b581379db3ff373fb95f3710072a36cb597836b5383e368990f73601d28435fe022a359740203594c0ac358ad894355e29ce35239d6d35169f3a34ceb8d134c7a967348b4368347c735e34636f5733a2828e3398d18533864f1f3380d2fa335d8195
  | 6, 5 => 0x51e93bed516b0265512f757250ea111b50d850505059633d500307f24faafd564f9d1e774f86a4154f3260114f17d2804f135c524ef7acb24e9d19034ddb76074dcf02ea4dc656d84d84259f4d74a6104d2f3d364cfd734b4c4507d04ba2e5bf4aee73794a8b09ee4a3ff2504a041b514a0125c0491e4f5448603f7247ff7ab347f8fbc8478f99604758974646ed067a45f5ff6d45d91ef1456daacd4512aef14503852044e13ffc44ae84d944578d0c43df582343b837ee43806d9c4357732f43555fb0434d2f5a42ef746f42e7ad3142b779a342b60bab4291ffc9425327d7418c58194183d887414a8c1f4132065940d675d3408a06cf40455b7a3f8bb627
  | 6, 6 => 0x72b2833971f3b43571b731cf70fe4ee070e9cc8f70695c5370345b606fb9b8376f51dbed6ed9b33e6d748c516cf9e7a76cc507e56cbe1d396c9c25686bba04806ba44eea6aafcc206a8f0134681155c7672edba166c97e4e66b0a48a63ff453e63ed97486346def6625d8697623466376212b35a613f4bb660c042605fbac6fd5f6f8df45f4ce3e85ed985675e8886d85e22a7545cde0cce5c1e7f7b5bc57ae15bb03c075b6b6fdf5b1f7a795abcb8a95a8e414d59a1fc3b5989a08a5875705b58739c60568ff7f15672a48756425f31563603f255e93b6a55d88bb75551c8e555122fc954c9ea995488605d536a150752e71d0152644444524bd7ed51ed2282
  | 6, 7 => 0x977488ac96fd8353967fbfcb9536c16594aba5ca94a203b79419634b93f38d2a934b343292fa7ab292976d64926de0ed918b0169917adf6f915bff589066fa268ec635f58e792b438e5d90ed8ca14df68c8f17858b4fe1e38a7994f8882be4e187f03d1a8756c638874f9269872dc00586be95e9865ca3e486465a8a864102a8863f5b5b849e475c827963fa81b49c60808528c4805eb719800a6df47fdefe227f4590c97f1a1c937ef20d5d7eaf48d67eadd0e57e1a2c3b7d7d57bc7c4faf817bfa0c557bf0b2df7b549f147b045a637a2bf436791c125478ab358178411ee77800865576f0de3376e1a5f076d69d90766e04be7481ccfa734eaa0d72ff2f9d
  | 6, 8 => 0xce745571cd772c5dcc9196c9cbd5b4f2cb22d64bc9ff3712c9b0660ac8e363e4c89efc22c828f799c694f8b9c63e6ab8c595198ec4f7a12bc4b9fc07c49c411ac4745ea1c2472df4c0e8397bc0d6b9cfbf98043bbd70c0e6bbe49247ba2a9fafb7dce78eb7a9ba99b71329c5b69c41a7b432738eb3152a51b2d40c22b26b0dcfaf805c40aef69b80aebe772fae61e220ae110966acec967dacb5a4bdac9b1be4ac4853ecab676f4faae79678aa361d56a8803f70a7a02c31a6a1e8eaa56b8c1ea296a4d8a2487bd3a181a08ea05f25a99fd4013c9ed1e5489ec0d7899c01232b9b9023199ae710529aca79e3998cea0d992cedf8986d00ac9819332997a9fca0
  | 6, 9 => 0xf29edce5eee0d3ace967135fe303f770dfe22038de87e0c6d9fb6b94d85d0165d6a5bda7d52b0a13d3ee0497d3d2caa2d317dc6dd2f75b26d26dda29
  | 7, 0 => 0x1a2bfa9c19b1d4481979f417196672e1191531f418e3fb0a1881f686183e8305181aa941173d5c00170db67f16d8a81c15f86a801561a43a13b5da6d135211a2131bfefa12b8ab4112ae5da311d748061198114410d1aa960fc22fb60f5c5cfb0f3d84400f3badb20ea68d810e7dd0190df078900d61f2fb0cf91d9f0c867e660c22507d0c1a79410bd753a90b41c7720acf09dd0ab8b26f0a9628be0a71f95609f5ca2f09ee1b6f0878675807d82e3c07bd347d0754ea15075140fd06291d8305ad2f34059e8b170590310f058ce34a054dc2ab040745c602e9d44b0296f5790291d00a023f103c01a603fb0198251c0188fb4b0129b75500dd496a0086a50c
  | 7, 1 => 0x3724f45b368990f7361b1af435f0ac8c35d89aaa358e7c13357bcd5734746a9f342cdee933d93c6b330961a63294bf40326a06213243d5cd317141fd31502d65315024ba3129ad3f302ca7772fc976f62eedfa852d90db782d6df75a2d014b912cf3c0ef2cae27f22c1543872baacaed2b698d6c2964176b28c04ce0284db2db2774c4602752ae7526aa53c326a4b5bf264ea121261c309d258a6ea424cb7b292429651523a7fde622543c1c2253e9022236825921e9d24d21a5f968204aaf2d203e530f1fd3d3851ee4e3db1ec21db31ebb13731e739d441e3d0e221e08e1531d094b741b8548e61b70b1901b61a0cd1b52f3321b2d157f1a5d39541a4058c3
  | 7, 2 => 0x64f389686449b75d6347643b63353df463275f156001a2b65eebace45e1657ce5dc82fa15d6275f45d2e415c5c9fbd605b2acd595b0171135a7078f858a5f177567ee6cd53b7a8b55316929452acbe7d52942b7251d2062b5038abd64f9b055d4f0fba7a4e79bd534d1acf0f4d17706a4bff26be4b62f61f4a6707154a5928364a3f78dc49226c8f49148db048f889f846e1bded465e79d544d8e42a43b9f0a342b779a34214fad1413ca69640db2d8b40bb28344079af633f8b9abe3f086e6d3e1c8eb63df1aaf13cedcf813c9f3cdf3c8fe41f3c39fd5e3b23954e3afd7b253a861c993a305add39de879e39a4dffb38ad846e3899ed1837a1ed1c3749605f
  | 7, 3 => 0xbe907f01be107ab6bddd5bacb84d21e0b3feb3cab3f8265db2dc7687b080f6ebad85a160aabfa2cbaa87c3f1a98c5b5da909e4c1a623790ea499e38a9e58572e9db654639d61744b9ce015509bfcd7929ab47d5a98411d819603a498944ede00929a9c8491b98d129074f28c8e7679718bbc73f08968a0cb877910e2872610b883f048fb828511a481bd8a2f804281918029ed027f97da8d7e8559377d356db97bf0d3337b4614867a85129f77d135d076f0de3376db0b2e76b015da766385db7341d2fd72739f547268845a707cee8d706753916f6c29a26bc490ee6b89f08a6b7c11ab6b6909ce6a0139de69d0a4b06920920f688d1b556659a12a66357542
  | 7, 4 => 0xfc3e0176f11d8484f109fd47ed5ae6a4ec164c1eea39f55de8b54ab1e8b03ee3e7283c3de7199440e606f433e1ccafbce07b344ecfe713d2cfc0f36ccea2794cca35eab9c8dd6445c62ad07cc110cb7dbf75ede2bef4bb49
  | 8, 0 => 0xd1efb8f3b47be6218ab84b5d764e5f6161ca400842b779a33e277fff2efbd9642eedfa851e7359ed1729918f1606144c1142fa4101bed059
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x70085504844000000035500201
  | 4, 0 => 0x181120403006704125440400000d94500a3010010951081301470813548040000000501052020011921484301001804248130137081154804002704145440400375802148440000000255002010010951081301000003510120070085504844000011953101300001195310130027041454404001708145480400000d52550030100059501093010011921484301000002048020046085504844004758021484400000003550020267041254404000019441441301000d950105301000d95010530200180414413010011810440300
  | 4, 1 => 0x951550030100115354803007008550484400760855048440000188104403000000000100101000994500630100081154803000005950109302700855048440000000355002016704145440400
  | 5, 0 => 0x52041201000481548030000000000000020000010440202001182540630000000000000000000015500201000002544020200000510812010000000000002000004540220100000000401020000000000001000d82048030000000254402020014441501300001145204130000000454402010018012441300001145108130000000000000020000053101200000004548020100194314c130000000454852020000020480201000d90584130000000000000010000035440202000005204120100000354802020018112080300
  | 5, 1 => 0x2081202000001548020100000000000020000000000002001881044030000144214813000000035101200000413544030000000531012000000000000001000003548020100000000000020000000000001000d820480300000001044020200000450812000000010440200000d9501053000000025440201000002550020100000104402000000052041201000004548020100000510c1200000005108120000180214843000004835480300001185148130000000000000000000000000000000d91500a3000000015480202
  | 5, 2 => 0x18845441300000d52544030000119058c13000000045480202000000000000200000454802010000000000002000d91500a30000000104402010000000000001000002550020100041354403000000012448202000003548020200180435013000018112080300000595010d300000d9058813000000021484202000005108120100000000000020000000000001000000000000000084454403000000045440200000d950109300000005204120000000454802010000015480202000003550020100000155002020004125440300
  | 5, 3 => 0x2148420100000214842010000041484202000004504120100000000801010000045440200000d525440300000000000000100119500853000018425440300000001548020000119058c13000000000000000000001508120200000104402000010552041300000004548020000000501052010000021484202000d452041300001881548030000000510812020000015500201001942148130000000154802010018420480300000000000000200000000000010000035500201000001548020100000520412010000000105101
  | 5, 4 => 0x1000005204120200114214813000000000000002000002500620000188354413000000000000001001145108130000000510812010000035480202000003544020100059058813000000000000000001802148130000184204803000000053410201000000000000000000000000010018420480300000005108120100000204802010000000100101000002544020200000254402010000035440201000000008010100000000000020000000000001000001548020200000355002010000000091101000d820480300
  | 5, 5 => 0x41448201000d5454803000000000000000000004508120100000454842010000035440201000000000000100041354403000000000000002000003548020100041454403000000000109102001883544130000000104402000000000000002000c951081300000412544030000000401012010018835441300000003548020200000104402010000000100101000d441441300000001550020100180314413000000045440201000000000000100000000000020011850484300000004544020100000154802010005805880300
  | 5, 6 => 0x405002010000051101200000000000000000000000000010000045041201000004548020200180415013000000045440201000001044020100000000000000008550484300000000000000100119058813000000052041201001842544030000000214842020000010041202000000004010200000204802000018425440300000413544030000119214843000000000000001000d95008530000000355002010000035041200000004504120200000000000010000045480201000000000000100000354402020000000000000
  | 5, 7 => 0x2000001044020100000000000000004125440300000002148420000000000000000000045402202000002148420100000154802020000012448202000002148420200099500c53000000001404201001812104030000000000801000000051081202000d91500a300000413544030000099500c53000008435440300000000008010200000414412010000035500201000004250820100000454852010000035480200000004508120200000000000010000051081202000990584130000144214813000008550484300
  | 5, 8 => 0x801020000000000000000005108120000059520413000000020480200000004544020200000200812020000000000001000001044020200000254402010000000080100000003544020200000520412020019035481300000002148420000000424482010000035440202000414544030000000520412020000020480201000d4450413000000000000001000d921484300000d9250403000000000000002000d8204803000004125440300000004548020200184204803000000020081202000d9214843000000035440200
  | 5, 9 => 0x214842020000045480202000005010920100000255002010000025440201001055204130100000255002010000045480201000000000000000000214842010000000080102000000010010100000214842010000000000002000d80584030000000414412010000045006201000002550020200114350413000000000000002001803248130000000214842000018032481300000002048020200000104402020000000000000000412544030000000534102020000045440200000001044020000194324c13000000000000002
  | 5, 10 => 0x2148420000000355002010011925040300000580588030000000510092020008115480300000811548030000000454842010000025440200000000000000000184204803000000000000000000002048020000000254402000000045402201000842544030000000534102020000000000000000005204120000105520413000000051081202000c5520413000000020081201000003544020100144214813000000035480201001802148430000000214842020000000000000000855048430000181210403000000051081201
  | 5, 11 => 0x8550484300
  | 6, 0 => 0x5210520000000520412000000000000001000001044020000000000811000000000000002000005204120000000454802000000000000002000000000000000000000c51000000000000002000000008410100000535012000000025440200000000000000200000000000010000000049101000000000000000000000061010000000080100000001500a2000000000101101000003544020000000254402020000000000002000000008510000000000801020000000000002000002148420000000000000020000000040101
  | 6, 1 => 0x154022000000000000000000000000a1010000035480200000003548020100000001051020000000105101000000008110200000000c11000000045081200000004548020000000510c1200000000380a2000000000000000000004548420000000510812020000000105101000000000000200000510812000000000000001000000000000000000000811010000000040101000005204120100000454402000000000000002000000000000100000454062000000000009101000005108120200000001051020000000000001
  | 6, 2 => 0x100000204802000000000080101000000010110100000510c12000000045480200000000000a100000000000210000000000000020000000000001000000010910100000000c9100000004548420000000250022000000042448200000005110d200000000000000200000058c120000000000411020000000080101000000008010100000059092000000045406200000000000000200000500c52000000000000002000001044020000000520412000000020480201000000500620000000454c520000000510c1200
  | 6, 3 => 0x1044020000000000000020000000012100000000000a1010000000000001000002148420000000344c1200000000000a102000005204120000000000000000000000105101000000000a10100000454022000000010440200000000010010100000000081020000000000002000000001010200000000000000000000041102000004244820000000058412000000025402200000003540a20000000000000010000020480202000005350120000000000411010000045480202000002148420100000000801000000052441200
  | 6, 4 => 0x101101000000000000000000350412000000000105101000000180a20000000454402020000035485200000000000210100000154802000000045041201000004548020000000204802010000045440202000000000000100000254402000000000104101000000008110200000204802000000035041200000000000000200000000000010000015480200000001500220000000354402000000000002102000000001210200000001041010000051081200000000000a100000003548020200000520412000000000000001
  | 6, 5 => 0x4010200000520412000000025440200000000000a1010000005901200000000010510100000000801020000000000001000004548020000000214842010000000108101000000000a1010000025440200000000000a101000000004010100000000000000000025040200000000010110200000214842000000000109102000000008010100000000061010000051081200000001540a200000000004010200000000061000000000000000000000000000100000414842000000025406200000000000a1010000000048101
  | 6, 6 => 0x8010100000154802010000010440201000004548020000000204802000000020480202000000000000100000000000020000000000000000000000000100000000061020000000000001000000000000000000000801010000012441200000005008520000000510812000000000000000000000590120000000000061010000045480200000000004810100000000000020000045441200000005110d200000000000000100000454c520000000154802000000000080102000005204120000000001011000000005841200
  | 6, 7 => 0x10000015480201000001244820100000454412000000035081200000000588420000000000000000000010440202000000000210000000154802000000000081102000000000000000000454402020000053101200000000010510100000510812000000052041202000000008110100000000021020000004802200000000000000000000454412000000000000000000001244120000000000000020000000081102000005148120000000000481020000035440201000000000210100000104402000000000000002
  | 6, 8 => 0x200000504482000000000000000000000380a2000000000000000000000000000200000001091010000021484202000000000a10000000414412010000005880200000000000000100000214842000000000000001000000000000100000000491020000000002102000000004810100000000000010000000109101000000000000100000000061020000000000001000000008110100000520c52000000050484200000003544020000000000401020000000085102000000540a20000000454802020000021484200
  | 6, 9 => 0x45440200000004544020000000520412000000021484201000005204120000000154802000000000002101000000000610000000050062000000000040101000000008010100000254402020000020480201000000010910100000000811020000035440200000000000a102000000380a20000000324c120000000214842000000000002101000000000000000000424812000000005406200000002544020000000454842000000045480200000005310120000000510812000000000004101000000000000200000520c5200
  | 6, 10 => 0x51081201000000000000100000001091010000010440200000000000000200000000000010000000000000000000000a1010000000105101000000180a20000000000000010000042501200000000008510100000058c520000000214812000000050109200000001500a200000001540220000000254402010000000000000000000000000000000001051010000000006102000000000000200000001011020000000040101000001044020000000000481020000015002200000000004910100000000491020000051081200
  | 6, 11 => 0x35440202000000000000100000001001020000031441200000005108120000000000c510000000000000000000021484200000002148420200000000841010000000101102000000584020000000000841010000035441200000000004810200000154802000000012080200000003548020000000048022000000000000000000000000a10200000454062000000000048101000004544120000000001011000000000081102000005210520000000425012000000000000001000003548020000000058c52000000050109200
  | 6, 12 => 0x20480200000000000000000000204802000000000105101000000010d100000000000a10000000001051010000025440200000002048020000000000121010000000041102000000000000100000254062000000000101101000001548020200000000021020000051081202000000010110100000000401010000000041100000003548020100000000000010000015480200000000010110100000000000020000000006101000002148420000000254402020000000000000000000000000100000414412000000000080102
  | 6, 13 => 0x411020000000084102000002048020000000450412000000000048101000000008410200000204802000000021484200000003548020100000001091010000000000002000000000000000000510812010000000000001000000590d20000000000121010000000000000000001548020000000000401010000031484200000000001210100000000000010000035480202000005110120000000058812000000051481200000003544020000000344c1200000000000000000000000000000000045041200000000000e100
  | 6, 14 => 0x344c1200000002048020000000214842000000035485200000001540a200000000010d100000000000000100000520412000000000085100000000000a1000000000000000000000480e20000000354402000000000084101000003544020000000000000020000000085102000000000000200000354802000000045041200000000004810100000520412000000004802200000005048420000000204802000000000002100000003544020000000000121010000025006200000005048420000000354022000000000008102
  | 6, 15 => 0x6102000001244820000000000021010000000084100000000000a102000002104020000000000000000000000000002000004548020100000531012000000000006100000005108120000000000000000000000000002000000000000000000000000020000000000001000005108120000000000111020000005840200000000000a10100000510812000000000084100000000000000200000000000000000000081100000000000000200000000000010000000004102000003548520000000254402000000000101101
  | 6, 16 => 0x20480200000000008510100000000021020000020480200000000008010000000000851010000000084100000000004010100000540c12000000021484200000001548020000000000101020000000080100000005108120000000000021010000000100101000002544020000000000000020000000085100000002540620000000510812000000000002102000000480e200000000010010200000001001010000000000001000002544020000000000801000000000002100000000000000000000000481010000000000002
  | 6, 17 => 0x35402200000004540220000000058852000000020480200000000008010000000520412000000000081101000002148420000000504842000000025040200000000000000200000514812000000050085200000000000000000000000851020000021484200000005010d2000000000084102000000000210200000001001010000000101101000000008010000000000000010000000084101000000280220000000000c51000000000085102000005010d2000000000000001000000000000200000150022000000045402201
  | 6, 18 => 0x214842000000005884200000000590d200000000280220000000001011010000000010101000000000a10100000254402000000005885200000002148420000000210402000000020480200000000000210100000000801000000032481200
  | 7, 0 => 0x40100000000010510000000001091000000000006102000000000210000000000c510000000000000020000000048100000000010110000000000021000000000041102000000010110000000000061000000000041100000000000000100000000021000000000012101000000008110100000000000010000000048100000000010110000000000c51000000000000000000000008410200000000411010000000105100000000000a100000000000a1020000000000002000000000000200000000c51000000000081100
  | 7, 1 => 0x4910200000000841000000000101101000000000610000000000401000000000000002000000010d100000000008110100000000c9100000000000a100000000008010000000000000000000000000001000000000a10000000000c1100000000008010200000000021000000000000002000000000000000000000021020000000012100000000000a10000000000411010000000101102000000000a1000000000080101000000010d10000000000851000000000000002000000000a10000000000801000000000006100
  | 7, 2 => 0x210000000000811000000000101101000000008410000000000c9100000000001210000000000061010000000105102000000008110000000000c51000000000000002000000000e100000000000a10100000000c110000000000021010000000041100000000000000100000000000010000000000001000000000e10000000000000020000000109102000000010110000000000c510000000000851000000000084100000000008510000000000000010000000002101000000008010000000000000010000000000000
  | 7, 3 => 0x2000000000000100000000801020000000000001000000000000200000000c9100000000000e100000000000a10000000000121020000000000000000000000e10000000000000020000000080100000000010d100000000010d1000000000002100000000000a10200000000c1100000000000a1000000000085100000000001210000000000021000000000040100000000000000100000000000010000000000001000000000000100000000c5100000000000a101000000000a10000000000000010000000006101
  | 7, 4 => 0x2100000000000a100000000000a102000000000a1000000000012100000000010110000000000841000000000000001000000000000000000000021000000000109102000000004110100000001051020000000081100000000000a102000000000210000000000c1100000000000000200000000c11000000000000001000000010510200000000851010000000006100000000008410000000000121000000000081100000000000000100000000851000000000081100000000000a10100000000841010000000040100
  | 7, 5 => 0x121000000000084100000000000210000000000021020000000109100000000008410200000001011010000000084100000000000a10000000000000010000000006100000000000e100000000008510100000000841000000000040101000000000210000000000851020000000040102000000000210100000000851000000000000001000000004010000000000021010000000006100000000000210000000000000010000000081100000000000e1000000000002102000000010d1000000000000002
  | 7, 6 => 0xc5100000000000210100000000121000000000002100000000008110000000000000020000000101100000000010d100000000000a10000000000000000000000000002000000008110000000000021000000000081100000000008410200000001011020000000002100000000000000200000000000010000000000001000000008510000000000c51000000000000001000000008510000000000851020000000081100000000010110000000000000020000000040102000000000000100000000000020000000084101
  | 7, 7 => 0x8010000000000481000000000000000000000004010000000000411000000000000001000000004910000000000401000000000000001000000010d100000000000210000000000841000000000000000000000010d100000000000a1000000000085100000000000210000000000c1100000000000a10000000000401000000000101100000000000a1000000000002100000000008110000000000c9100000000010d100000000000a100000000000210000000000c5100000000000a1010000000080100000000000a100
  | 7, 8 => 0x84100000000000a1010000000085100000000010d100000000000a10000000000021010000000002100000000000a10000000000021010000000101100000000000210000000000021000000000085100000000010d100000000000a100000000000a10000000000000000000000002100000000010d100000000001210100000000811000000000000001
  | 8, 0 => 0x200000000000010000000000002000000000000000000000000010000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 8 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 7 s ws hint
  | 2 => checkCutEntry dom_3 roots_3 7 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

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

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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
theorem z3_0 : ∀ i, 0 ≤ i → i < 8 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_8 : ∀ i, 8 ≤ i → i < 14 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 6 8 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 14 → Z 3 i = true := range_split z3_0 (z3_8)
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
theorem z4_80 : ∀ i, 80 ≤ i → i < 88 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_88 : ∀ i, 88 ≤ i → i < 92 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 88 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 92 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (range_split z4_48 (range_split z4_56 (range_split z4_64 (range_split z4_72 (range_split z4_80 (z4_88)))))))))))
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
theorem z5_352 : ∀ i, 352 ≤ i → i < 355 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 352 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 355 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (range_split z5_200 (range_split z5_208 (range_split z5_216 (range_split z5_224 (range_split z5_232 (range_split z5_240 (range_split z5_248 (range_split z5_256 (range_split z5_264 (range_split z5_272 (range_split z5_280 (range_split z5_288 (range_split z5_296 (range_split z5_304 (range_split z5_312 (range_split z5_320 (range_split z5_328 (range_split z5_336 (range_split z5_344 (z5_352))))))))))))))))))))))))))))))))))))))))))))
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
theorem z6_480 : ∀ i, 480 ≤ i → i < 482 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 480 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 482 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (range_split z6_376 (range_split z6_384 (range_split z6_392 (range_split z6_400 (range_split z6_408 (range_split z6_416 (range_split z6_424 (range_split z6_432 (range_split z6_440 (range_split z6_448 (range_split z6_456 (range_split z6_464 (range_split z6_472 (z6_480))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z7_176 : ∀ i, 176 ≤ i → i < 179 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 176 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 179 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (z7_176))))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 8 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := range_split z8_0 (z8_8)
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
  scr dom_4 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_4 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_4 roots_4 goal_4 10 := by
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

theorem low_4 : Lower dom_4 roots_4 goal_4 10 := S_4.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_4_bits : ∀ r : Fin 64, roots_4.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_4_lt : ∀ r : Fin 64, dom_4.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_4 T)
    (hlow : Lower dom_4 roots_4 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_4, Avail mask256 roots_4 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_4 hfan 0 roots_4 roots_4 rfl hsup0
  set out := (execN C.gates roots_4).getD C.output 0
  have hout : out &&& dom_4 = T &&& dom_4 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_4_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_4 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_4_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_4).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_4)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_4.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_4 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_4).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_4 &&& mask256 = dom_4 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_4 = T &&& dom_4 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_4, hd63, hout]
  have hnc_m : ¬ IsConst dom_4 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_4 roots_4 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_4, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_4 roots_4 0 roots_4 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (3941264042 * 2 ^ 32 + 3937069736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_4.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_4 10 hT6 (by unfold IsConst; decide) low_4

def wit : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [13, 4]⟩, ⟨GateOp.and, [11, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_15611_aux

theorem PEqualNP.Outside.L_meta_15611 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264042 * 2 ^ 32 + 3937069736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264042 * 2 ^ 32 + 3937069736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_15611_aux.wit, PEqualNP.Outside.L_meta_15611_aux.wmono, le_trans PEqualNP.Outside.L_meta_15611_aux.wsize (PEqualNP.Outside.L_meta_15611_aux.lower s hs), PEqualNP.Outside.L_meta_15611_aux.weval⟩
