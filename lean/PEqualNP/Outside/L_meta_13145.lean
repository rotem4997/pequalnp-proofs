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

namespace PEqualNP.Outside.L_meta_13145_aux

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
def goal_0 : Nat := 0xe0e0e0a0e0c0000
def roots_0 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(1, 33), (2, 18), (3, 19), (3, 35), (9, 25), (9, 41), (10, 26), (10, 42), (11, 27), (11, 43), (16, 18), (17, 19), (17, 25), (17, 49), (24, 25), (24, 26), (32, 33), (34, 35), (34, 42), (34, 50), (40, 41), (40, 42), (48, 49), (48, 50), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 2, 3, 3, 9, 9, 10, 10, 11, 11, 16, 17, 17, 17, 24, 24, 32, 34, 34, 34, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [33, 18, 19, 35, 25, 41, 26, 42, 27, 43, 18, 19, 25, 49, 25, 26, 33, 35, 42, 50, 41, 42, 49, 50, 57, 58]
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
  | 2, 0 => 0xc950010
  | 3, 0 => 0xbbe5e99c494bae381345fe160b674889
  | 4, 0 => 0xc3827481b9ed760e8c5020338bab304b6db0035454363a3526f145cd26bc2b5e243e20471ba5db2b16a6bae609710d2b061f7558
  | 5, 0 => 0xcd1774a2c3827481a052ac9e8ea8457e6e9b733a6c35459f652e56205a3c9a364599038c418db97037f8ccf414d4acce006bb7a1
  | 6, 0 => 0xc3827481
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0a0a0a0a0a0a0a0a0a0a0a0a000a000a0a0a0a000000000a0a00000a0a00000808080808080808000f000f000f000f00000f0f00000f0f000000000f0f0f0f
  | 0, 1 => 0xf000f000a000a000f0000000f0000000e0e0e0e000000000e0c0e0c0e0c0e0c0c0c0c0c0c0c0c0c0c0c0c0c000000000c0c0c000c0c0c000c0c00000c0c0000
  | 0, 2 => 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f00000f0f00000f0f00000f0f0000000000000f0c0f000f0c0f000f0c00000f0c00000f000f000f000f000f000f000f000000
  | 0, 3 => 0xf0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f0a0a0a0a0f0f0f0f000000000f0f0f000f0f0f000f0f0f000f0f00000f0f0f000f000f000f0f0c0c0f0f0c0c
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x69663
  | 3, 0, 0 => 0xf69674abd654e39274fe5674
  | 4, 0, 0 => 0x1cac5675e566b3af33559d7968acebcac5875e4a2b3af2f159179b72cebcac1675ac5ab3af2af59d7988a0ebfa45675
  | 5, 0, 0 => 0x3958ace26072b159d7fcac5676e562b41db958ace36e562b51dbbcac5676e5eb159d81caace25f72b159d81c8ace15e562b381b958b9676
  | 6, 0, 0 => 0x1cac5675
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
  | 0, 0 => 0xecf400033000000000038000000c30cf3c0f0fc0ffc00ffff
  | 0, 1 => 0xcc00cc300c00003800000e03fe0380f380e00000000f00000000
  | 0, 2 => 0xf03fcf7c0fc00f03f003c00000cc30fc300c000cc30fc330c000
  | 0, 3 => 0xffff003ffc3f0ffcecf7ff0000fc3ffc3f0fc00fc30fc3ceffce
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x54decf553733954c88a54079140082c30cb2c0f0dc0aa400dd56
  | 0, 1 => 0xcd14ec300d150ffc8aa7bedffeaba3f3aae0288ab23f1a888d46
  | 0, 2 => 0xf6ffdffdbff7ff23f55bc82000ef37fdb88dd56cd34fc334d3f0
  | 0, 3 => 0xffffffffff3f9ffdeef7ff22a9ff3ffdbfcfff6ff3cfc3eeffde
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

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
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

def dom_1 : Nat := 0x555500000000
def goal_1 : Nat := 0x544000000000
def roots_1 : List Nat := [0x444400000000, 0x505000000000, 0x550000000000]

namespace S_1
def pairsG : List (Nat × Nat) := [(34, 38), (34, 42), (36, 38), (36, 44), (40, 42), (40, 44)]
def r1sG : List Nat := [34, 34, 36, 36, 40, 40]
def r2sG : List Nat := [38, 42, 38, 44, 42, 44]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x95ad01e5
  | 3, 0 => 0x95ad01e5
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55000000000000005050000000000000444400000000
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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

def dom_2 : Nat := 0x555500005555
def goal_2 : Nat := 0x544000005040
def roots_2 : List Nat := [0x444400004444, 0x505000005050, 0x550000005500, 0x555500000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x555500000000, 10, 42)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xffff00000000
def goal_3 : Nat := 0xfeea00000000
def roots_3 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_1

def dom_4 : Nat := 0x333300003333
def goal_4 : Nat := 0x322200003020
def roots_4 : List Nat := [0x222200002222, 0x303000003030, 0x330000003300, 0x333300000000]

namespace S_4
def pairsG : List (Nat × Nat) := [(1, 5), (1, 33), (4, 5), (4, 12), (8, 12), (9, 13), (9, 41), (32, 33), (36, 37), (36, 44), (40, 41), (40, 44)]
def r1sG : List Nat := [1, 1, 4, 4, 8, 9, 9, 32, 36, 36, 40, 40]
def r2sG : List Nat := [5, 33, 5, 12, 12, 13, 41, 33, 37, 44, 41, 44]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_4.map (· &&& dom_4)
def goalM : Nat := goal_4 &&& dom_4
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x96d78117
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x333300000000000033000000330000003030000030300000222200002222
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

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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

def dom_5 : Nat := 0xff000000ff
def goal_5 : Nat := 0xea000000e0
def roots_5 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 4 :=
  lower_iso [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_6 : Nat := 0xffff0000ffff
def goal_6 : Nat := 0xfeea0000f0e0
def roots_6 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

namespace S_6
def pairsG : List (Nat × Nat) := [(1, 5), (1, 33), (2, 6), (3, 7), (3, 35), (4, 5), (4, 6), (4, 12), (8, 12), (9, 13), (9, 41), (10, 14), (10, 42), (11, 15), (11, 43), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 4, 4, 4, 8, 9, 9, 10, 10, 11, 11, 32, 34, 34, 34, 36, 36, 36, 40, 40, 40]
def r2sG : List Nat := [5, 33, 6, 7, 35, 5, 6, 12, 12, 13, 41, 14, 42, 15, 43, 33, 35, 38, 42, 37, 38, 44, 41, 42, 44]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_6.map (· &&& dom_6)
def goalM : Nat := goal_6 &&& dom_6
def NN : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xff998d69
  | 5, 0 => 0xe9082d54b7253fbd8888432e6949f7d65ba073fa
  | 6, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffcc0000ffcc0000ff000000ff000000f0f00000f0f00000cccc0000cccc0000aaaa0000aaaa000033330000333300000f0f00000f0f00000f0f00000000
  | 0, 1 => 0xffff000000000000fff00000fff0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x654305
  | 5, 0, 0 => 0x97654369654316096532598654360964315
  | 6, 0, 0 => 0x965435
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe3bf8e701fc007001c007781c00330dfe21f8f8ffe3fc78000
  | 0, 1 => 0x3ff0001f87fe0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfbbfee791fe027457da97785c24f31dda21e8d8ba824c5d412
  | 0, 1 => 0x3ffa825fe7fed
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
  | 4, 0 => 0xbc1fa3ec67ae8f754fada6a40f1fce07
  | 5, 0 => 0xe505bdfaa7da18faa1c0b4b8a1712e8b9f39fa5292b6c7608c5e12727ea52a9a7445a6b572657d5c686e9bda5cdf53735b61388b530ab5464d7877b92fef2b28270b03de160058940f1fce070da784ce
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0xc0000200000c00000
  | 5, 0 => 0x4000000000040000000000000001000000000010000000000200000c0000000000000001000000000010000000000100000000003
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 1 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 2 => checkCutEntry dom_4 roots_4 4 s ws hint
  | 3 => checkCutEntry dom_5 roots_5 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_6 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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
  scr dom_6 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_6 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_6 roots_6 goal_6 7 := by
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

theorem low_6 : Lower dom_6 roots_6 goal_6 7 := S_6.noCircuit

def dom_7 : Nat := 0xffffffff
def goal_7 : Nat := 0xfeecf0e0
def roots_7 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_7 : Lower dom_7 roots_7 goal_7 7 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_8 : Nat := 0x5555555555555555
def goal_8 : Nat := 0x5444544054445040
def roots_8 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000055550000, 2, 18)] (by decide +kernel) (by decide +kernel) low_2

def dom_9 : Nat := 0x3333333333333333
def goal_9 : Nat := 0x3222322232203020
def roots_9 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0x33330000
def goal_10 : Nat := 0x32200000
def roots_10 : List Nat := [0x22220000, 0x30300000, 0x33000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_11 : Nat := 0x3333000033330000
def goal_11 : Nat := 0x3222000032200000
def roots_11 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000000000000, 17, 49)] (by decide +kernel) (by decide +kernel) low_10

def dom_12 : Nat := 0xffff0000ffff0000
def goal_12 : Nat := 0xfeee0000feec0000
def roots_12 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc0000, 16, 18)] (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xffffffff00000000
def goal_13 : Nat := 0xfeeefeea00000000
def roots_13 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_14 : Nat := 0xff00ff00ff00ff
def goal_14 : Nat := 0xee00ea00ec00e0
def roots_14 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff0000, 2, 18)] (by decide +kernel) (by decide +kernel) low_5

def dom_15 : Nat := 0xffffffffffffffff
def goal_15 : Nat := 0xfeeefeeafeecf0e0
def roots_15 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_15
def pairsG : List (Nat × Nat) := [(1, 5), (1, 33), (2, 6), (2, 18), (3, 7), (3, 19), (3, 35), (4, 5), (4, 6), (4, 12), (8, 12), (9, 13), (9, 25), (9, 41), (10, 14), (10, 26), (10, 42), (11, 15), (11, 27), (11, 43), (16, 18), (17, 19), (17, 21), (17, 25), (17, 49), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 16, 17, 17, 17, 17, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 34, 36, 36, 36, 40, 40, 40, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 33, 6, 18, 7, 19, 35, 5, 6, 12, 12, 13, 25, 41, 14, 26, 42, 15, 27, 43, 18, 19, 21, 25, 49, 21, 22, 28, 25, 26, 28, 33, 35, 38, 42, 50, 37, 38, 44, 41, 42, 44, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_15.map (· &&& dom_15)
def goalM : Nat := goal_15 &&& dom_15
def NN : Nat → Nat
  | 2 => 4
  | 3 => 19
  | 4 => 77
  | 5 => 208
  | 6 => 357
  | 7 => 233
  | 8 => 19
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x79d81553724bcf391e8a7bbc1ab5611c
  | 3, 0 => 0xc9df3de4c36ae1cdb8384df4b0d00c31ab27dd9d94ffda8880175ed97f63f19475bf68dc5241c8074f8463163fbf54662ce389d923a2937a229b02c51ff9bd4b18afef88116a77c60bd4cdb2
  | 4, 0 => 0xa17e5d3d975bad8f902600d69009a6908d80448a8c3fc7158b75e5e48772b630850951c97f91c5617491f057738263e772ac29e5703b2fcf6cc350286a4f4cac6924c73768fb2c8567f1c339615757e65fbc651b5f6230315928c0c756824c375216bf1e520e71af50c1ffa050595e5c4c0fa57d4563f6654302cd9842343c7840c71b51405766043dc097343a00bf9c3563c16034329fef33e8209c30e0a6cb2fb17bdc2937d72528ddf73b2742f535274199282591fcfe25573dd6250c2b1c23152c5920eb59f31d657ce119daef52191cfd1918c67ff718977422156ba2290c74cf0308f20fee061289ca028fd79c02171fdf016e785000250b39000a8b18
  | 4, 1 => 0xf2ebd26eeb4d8c6adb7208e8d2bebe42cec440f2cc115bcfc7d8c0ecc5e18321c351a1dcb69b826bafae689dad36001ea54b0a5d
  | 5, 0 => 0x223e64fc21fab4be212961da1f990ef21f7307771eff4fbe1e200e6f1e0dc9541d8e1ba51d0f70531a10f6e5188a33ec180065e617bf51d017603fa5171ac71616ff8e0d1643e44815fd50f715e06ff2154b9c0314b79ffb149d101313e7a6b81389877213396fbd12fe6fd312dc570a122947da11f1ce8211a3b9ed113bb9910fce77530fa2af160f96c9ee0e970a1b0e5e461c0e5088980e3ec0240df6e2ed0dd58f050d0823750c4fcb820ac4e0780a6c0c69099ca60109484a9d08ea0cab087d22ae0864317207f3386b07a01e5f074133d207050eaf05eb5413042a201f036e78b003331cf0023b93cb01efda4f01a4edb2010b26c500ad124100458cb8
  | 5, 1 => 0x5feda23e5e6364645e2d8aab5cddeeb15c23bcb55967c8f756425b9c554f1f00549d174552d82cfb52d074c25266e3f1511bf5114f7c60744eb19c7e4d208b264cdc80b64c87203c4b98ddfa4b79d9074b0449cd4abe883d4a9dd61748388c284650aa02462abd2745454dd344c5769f448f38e244791ed04123d80e40e31f3840281a5b3f3612893cbf50053bb78faf3b8eaf6f3a8df35d3a792f6a39b1435936d9bd2636d58aee35c7f4993492314e3415bfd232d891c032259cf03193f73a317115293125f58f310d81732fa027f32d5cd8a82d1460e62b9535dc2a66ef6828816fb32800253a268dd86d2671147b264006cf250f4da923cd0d6223249a26
  | 5, 2 => 0xc001d22fbf1d1ff3bb018765b95be50eb61b96f1b2cd9beab118dcdbb02c9557af4c88b0aef213a3aee7fad1abb6cb46a8c71cf8a890ecd1a6db69e1a55e26ea9bd7eb1398985da5988c6c5b95a74ce59373f085900e23e88f04ba9c8efbc7eb8ed4e3968cf5582d8b4ae68489bfe59489a882578938e0ef877da1b6857036be84e790348319ef2881aa186e80cda34b7f03c33b7edb443f7e7135af7d95439a7d2cbcce7bbb12ac7bb0128c7b8be3947b3778cb7b0c272f7805678f750c721874c712c773036a1472db50be725681b5720f6f21701596636ff542016a256cf4689a2e6f6810024f6716e8906611101764d38e9763dddc6763d0905f63474bf4
  | 5, 3 => 0xfaf17dc7e3cd2773e2efa377de160a38dce8ce41d8dcecdfd86a591ad6e5ee1cd6bdfbfacec5fbb1c8fdeb8dc8584d64c598271cc29aac78c194ef38c191f0be
  | 6, 0 => 0x18eed24c183fdbce181c0a6c17d80f9a17ae9e2a17a712b0176d640f173643a816446b9c15776f951432396c13d6d81d13be640112bbd30812baa677125dee4811b9e05611a579d6118eca21118d0e1d1161181a1144e41f10aeb074106f8d04104ef361101595881010fcf00fcb33c20edf18670ea8faac0e255d760dd633720d9dd24c0cd7607a0c21c3560b88cc090b3080880b2c8ce60ae653d70a7677f509c0e32809785bd109199978090241a808a3620f08828543078ac02b0715437d06a13685065d5685060f596e060e91e705e77d7105b10e6b0566b4e003f7cba003b6f376035b2fd10249a99b0185b851014fcec7010ab0bf00ad42790002c0f2
  | 6, 1 => 0x34a771a73451707d341c017333a95ef3330f147832d484fe3241f77231ca075930f2019a30e1709b30b973d630a9d7c93078e78b2fac2bde2f653d432f5ca5572f3e6dd02f29cd722df741622d9165262cbb9f1f2c42325c2bc612742b9c405e2b27b74c2b25f1c52af8e8dd29e188d329af2b642912a7492886920f2842fbd327c009a42602ca6f258afb4b255de84a247cfe3f23e658262383a1de2288025422758e6922747b08223c385a223380ee21ce372521997fae219634db213bddeb20d5617920819f3a20257d1e1e3844ef1db45b721d75a3ee1c96ea491c6af0321bfe84a81b9386ad1b16f5ed1aa1953a1a256c9319ff9c8019e5257c19ba301a
  | 6, 2 => 0x583019b958118ebc57a487195770ff1d568e1c39568a894c567c7f5156488c3a56427f9254d9fe77546fd00b542758495372c479534eebe752839f995257aedf5139dea74f084ed24e8c86004d8d48cc4ca859dc4beb8c424b11aa524abd1d0b4aabf4e84a932f4e4a67671149780ea848d58fd647e95d2f46f1b31146e45dc94502434f44ab1cba43c469ce433fd5ee429d85804270b5be41da7966412c1b38406a83da3fcf86193ed249333df7d4eb3d8a3cae3d2c7c353cc696da3c731f583c21f90f3c0ce04f3bfb94483b43ce223b1bb4d23b0a44b33a4fc2063a4d6a95392d295a376cce2b36de7a8736d58aee3661a5cb3609387935c10950357ada31
  | 6, 3 => 0x82647cae8220babb81b726b38101e0aa80d851b58018916b7ea020fc7e7a0a4c7d8dbfab7c2f60d67b83ced07af39e807aebe6477a399f0c77e0dac7769b1dfd7613d46a7597c941751532dd74cf39e474a44fa474789e64731046f8730f3397730cc97a710cff0270fe4ee0706400707037bb136f9f36356f1deb2a6ec9faec6df7e42c6d79ee906d0dc9146bbbe0b36a95be0b6a19a43b6a08bb0569ebc1aa696bc1f768758a126786b847677d8db966d0a35666276d0264dbd5c4643609f5629689a2626898c0617c8feb5fa001255dd019e35d0ffb5a5c97debb5c6c35a95bec1ae15b83bf685ac7832c5a9c6dcb593cbb0a592546695916f5625838ecf2
  | 6, 4 => 0xbe4769d9be20deedbd9159b9bd7b6565bc9691cebc545819bc3e1aa1ba45dd7fb64676f4b5b55af9b4084f90b3cc7367b303514faf647c31af616e2bae4cad44ade4afffac06f897abe9eccbabdd680fa9c667e4a8249059a7853e24a61bfe94a51a34faa43fb431a434b4b6a3105a4fa15ebe12a053c87f9f5eff5f9f48540e9f307a4a9ec0d7899e93ebe99dcd4e089db654639d770c479bca9a899a6c3ba3982e64fb97f60d33974b40d795c7f38494c167a694b791e6947fb432945f30188f15bfe78eb3b3e78e3f8c778d869bbd8aa44b2d8aa3b04f8a516cc389e7ef1089ca38de86981ab68544e646850f970a84520cd583d093ae83c702f182b8d63d
  | 6, 5 => 0xfd75c11dfc6afe7def885172ee5bfb02eb121e74ea99b7d8e9e0e609e88e9a99e2f6af66e247b55ee2433ca3df64decad8d7c2ffd85d0165d79dcf25d69ca30ed445852fd26dffcbd2370a95d1f83001d1296545cd0facd0cb5a385fcad25745caa6b7f9c91c5dc6c91a9764c82107d4c66d7f59c6631c17c63e6ab8c4f7a12bc44be902c28adb2cc1e70f7dc104a00bc0d8bcda
  | 7, 0 => 0x2705880d26d2458e26beaf6f265363bb261c309d2509c4b82429651523afce92233e51982310763b2219ec0a21f612462081cc6120292edb1fb72b911eb3facb1e3d0e221d81c57f1d094b741c1ffead1bde45011a433cbc1a4058c3196672e11923eb0b181aa94116e8db1816d8a81c16b50ee916a611991606144c153eaa18141a4f1c14121a0c12baa67712b8884a124e2635123247971198114411761aa80f8b2a5f0f8898390e7e15130e7dd0190e783ebe0d61f2fb0d52c9a60d4d98860cea20e10cabde0a0c22507d0c167f1009ee1b6f08d6f0260754ea1506ecbabd06291d8305869eb103e36454033a727c02e9d44b023f103c0086a50c00273479
  | 7, 1 => 0x581fb8f657a1024a56240dff54ed1c7554c1de1053346db9531915d152942b72523dc21151bf3f2b514aca6d51099cc65038abd6500139404fb2394c4f717d1d4f0fba7a4ec05ebd4e2ce2974e0e9fc94c4c79c44bff26be4bc969994a6707154a3f78dc49e125c6499cfa0a49226c8f43b4257143a9f8484309ffd84214fad141d9fb784079af633c3d49423c21f90f3a8b9b213a67daad37f1b8763732d33a36e4026d359f67e7359aee6d358e7c133518dab1343c258234064f6c33d93c6b330961a632ba82ac317141fd3129ad3f302ca7772f7655c82e9e70832de85b922d90db782d6df75a2cb7e2692acd7a982a6bdfc02a60bc7d29e942c428a4a83e
  | 7, 2 => 0x98d8396998553ede97a5128c9710a458956125c6950fbbe393f42b8d93cd8fe0927d83849272b1cc91b98d128f9d1d5f8e35cdb08df2ab598d5eaaf98d1e3ac288f300e185520fcd82739f2081bd8a2f7fe35f827f1797dc7e8559377d356db97bf841387bf0d3337ab597257ab2c90879a4d76c78bca81278493a7f77d135d0745a681c7260e48f721cd83370cdf074709466926f6c29a26db8095f6be1bd3a6bcb63fb6b6909ce6b46b4d16b1be3666a0139de69b07ce3679d352a651506a4645092fc6401590263353df46292bf2261ca400861aa3368602f2d625fff77045f5d13a95d1e66bc5c0095e65b2acd595abc6cf25aa8a6b95916f56258905d13
  | 7, 3 => 0xfb192d73f109fd47eeab662cee1e2c58ed5ae6a4ec164c1ee21fca1de1b94d76e088d44ddf6d0221da26b2c9d958a3e4d1efb8f3d17f337bc5690328c44be902c33e8ebcc2d0e2fcc1a069d3bf355634bc545819ba45dd7fb702d21ab37ef559b0f51e5bb080f6ebafebec7dae8d3699ada32de2ace974c5ab94b348a8e78fc4a8d9852aa68098aea494c22f9db654639d2d50bb9c97dd089c7605899c48de239a36658d
  | 8, 0 => 0xd1efb8f3a6563cc3876dd2497cea112d764e5f6161ca40085fbac6fd5e22a7545cde0cce51bb2a0f4aee737942b779a33e277fff34064f6c2efbd9641b78d4bc1606144c0e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x330033003300330011001100110011000f000f000f000f00030003000300030000ffff0000ffff00000f0f00000f0f00000000ffffffff000000000f0f0f0f
  | 0, 1 => 0xff00ff00f000f000ff00ff00cc00cc00ff00cc00ff00cc00fc00fc00fc00fc00ee00ee00ee00ee00aa00aa00aa00aa00770077007700770055005500550055
  | 0, 2 => 0x7070707070707070505050505050505030f030f030f030f0303030303030303010101010101010100ff0fff00ff0fff00ff00ff00ff00ff00ff00ff00ff0000
  | 0, 3 => 0x33333030333330303333222233332222330033003300330032323232323232321155115511551155113311331133113311111111111111110f0f0f0f0f0f0f0f
  | 0, 4 => 0x55445544554455445500550055005500444444444444444433333333333333333333333333003300333333333030303033333333222222223333330033333300
  | 0, 5 => 0xa8a8a8a8a8a8a8a8999999999999999988ff88ff88ff88ff88888888888888885555555555555555555555555555000055555050555550505550555055505550
  | 0, 6 => 0xaaffaaffaaffaaffaaafaaafaaafaaafaaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0aaaaa0a0aaaaa0a0aaa0aaa0aaa0aaa0aa88aa88aa88aa88aa00aa00aa00aa00
  | 0, 7 => 0xccccccccc0c0c0c0ccccccc0ccccccc0ccccc0c0ccccc0c0ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc33cc33cc33cc33cc00cc00cc00cc00bbaabbaabbaabbaa
  | 0, 8 => 0xeeaaeeaae0a0e0a0eeaaeeaa00000000ee88ee88ee88ee88ee00ee00ee00ee00cdcdcdcdcdcdcdcdccffccffccffccffccddccddccddccddcccccccccccccccc
  | 0, 9 => 0xeeeee0e0eeeee0e0eeee0000eeee0000eeeaeeeaeeeaeeeaeee0eee0eee0eee0eecceecceecceecceecce0c0eecce0c0eecc0000eecc0000eeaaeeaaeeaaeeaa
  | 0, 10 => 0xeeeeeeeeee00ee00eeeeeeeeececececeeeeeeeeeaeaeaeaeeeeeeeee0e0e0e0eeeeeeee00000000eeeeee00eeeeee00eeeeececeeeeececeeeeeaeaeeeeeaea
  | 0, 11 => 0xf0fff0fff0fff0fff0f5f0f5f0f5f0f5f0f3f0f3f0f3f0f3f0f1f0f1f0f1f0f1f0f0f0f0f0f0f0f0f0e0f0e0f0e0f0e0eeeeeeeeeeeeeeeeeeeeeeeeeeee0000
  | 0, 12 => 0xfafafafaf0f0f0f0fafafafac8c8c8c8faf0faf0faf0faf0fac8fac8fac8fac8fa00fa00fa00fa00f8f8f8f8f8f8f8f8f3f0f3f0f3f0f3f0f1f1f1f1f1f1f1f1
  | 0, 13 => 0xfcfcfcfca8a8a8a8fcfcfc00fcfcfc00fcfca8a8fcfca8a8fcf0fcf0fcf0fcf0fca8fca8fca8fca8fc00fc00fc00fc00fafafafafafafafafafafafafa00fa00
  | 0, 14 => 0xfeccfeccfeccfeccfeaafeaafeaafeaafeaafeaa00000000fe88fe88fe88fe88fe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfcfcfc0000fcfcfcfcfc00fc00
  | 0, 15 => 0xfefefefe00000000fefef0f0fefef0f0fefe0000fefe0000fefcfefcfefcfefcfefcf0f0fefcf0f0fefafefafefafefafefafefaf0f0f0f0fef0fef0fef0fef0
  | 1, 0 => 0xff00ff00f000f000ff00ff00cc00cc00ff00ff00aa00aa00ff00f000ff00f000ff00cc00ff00cc00ff00aa00ff00aa00fefefefefefefefefefefefef0f0f0f0
  | 1, 1 => 0xffa8ffa8ffa8ffa8ff88ff88ff88ff88ff11ff11ff11ff11ff05ff05ff05ff05ff01ff01ff01ff01ff00ff00ff00ff00ff00ff00ff000000ff00ff00fa00fa00
  | 1, 2 => 0xffaaffaafaaafaaaffaaffaaf0a0f0a0ffaaffaaeeaaeeaaffaaffaacc88cc88ffaaffaa00000000ffaaf0a0ffaaf0a0ffaaeeaaffaaeeaaffaacc88ffaacc88
  | 1, 3 => 0xffccfcccffccfcccffccf0c0ffccf0c0ffcc0000ffcc0000ffc8ffc8ffc8ffc8ffaaffaaffaaffaaffaaffaaffaaaaaaffaaffaaffaa0000ffaaffaaffa0ffa0
  | 1, 4 => 0xffeeeeaaffcc0000ffee0000ffee0000ffccffccffccffccffccffccffc0ffc0ffccffccfcccfcccffccffccf0c0f0c0ffccffc0ffccffc0ffccfec8ffccf0c0
  | 1, 5 => 0xfff0fff0fcf0fcf0fff0fff0faf0faf0fff0fff0aaa0aaa0fff0aaa0fff0aaa0ffeeffeeffeeffeeffeeffee00000000ffeeffaafeecf0a0ffeef0e0ffeef0e0
  | 1, 6 => 0xfffcf0f0fffcf0f0fffafffafffafffafffafffaf0f0f0f0fffafffa00000000fff8fff8fff8fff8fff0fff0fff0fff0fff0fff0fff0f0f0fff0fff0fff00000
  | 1, 7 => 0xffffaaaaf0f0a0a0ffffaaaacccc8888ffff1133ffff1133ffff1111ffff1111ffff0033ffff0033ffff0000ffff0000fffefffefffefffefffcfffcfffcfffc
  | 1, 8 => 0xffffeeccffffeeccffffeeaaffffeeaaffffccccffffccccffffccccf0f0c0c0ffffccccaaaa8888ffffaaaaffffaaaaffffaaaaffffa0a0ffffaaaaff00aa00
  | 1, 9 => 0xffffff00f0f0f000ffffff00aaaaaa00fffffefafffff0f0fffffcfcfffffcfcfffffafafffffafafffff0f0fffff0f0fffff0f0ff00f000ffffeeeeffffeeee
  | 1, 10 => 0xffffffff00550055ffffffff00000000fffffff0fffffff0ffffffccffffffccffffffaaffffffaaffffffaafffff0a0ffffff00ffffff00ffffff00fffff000
  | 1, 11 => 0xffffffffeeeeeeeeffffffffeeaaeeaaffffffffccccccccffffffffccccc0c0ffffffffaaaaaaaaffffffff11551155ffffffff11111111ffffffff00ff00ff
  | 1, 12 => 0xffffffffffccf0c0ffffffffffaaffaaffffffffff88ff88ffffffffff00ff00ffffffffff00f000fffffffffcfcfcfcfffffffffcfcf0f0fffffffff0f0f0f0
  | 1, 13 => 0xffffffffffff0000ffffffffffccffcc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x8e7e543a95b4b3a0794839e79483
  | 3, 0, 0 => 0xd29665404965b4b494bab59b774cda579484ba96776948a62534f4caa579484e08e7e5948a7e542c48e5b544e4baa57a474d69b7b774ba96784049b937b4b4d09869404e79e5b484
  | 3, 0, 1 => 0xba9664404d29869404a7a55b484
  | 4, 0, 0 => 0xcaa55b48465e7a15b40355d6ca9b7c405d69b7b5b4b58a7e5440355baa5935b485dabaa55b485e08a7e592c5d69b7b4b405d6ca9b724b5ca8a7948405e08e5b594e5ca9b9365405e79e8a72355d68e5b594f5e0ba975b4b5
  | 4, 0, 1 => 0xba8a7976405a59d5b484658a72534f355d69e726a355e0ba965b4b5d6ca8f81405cd8a7948405e0a59d5b485d68a7250335d6b7a56a355baa58a79485e0ba9b77695baab935b4b5e79e5b39355a59b5b534e5d6caa56b355
  | 4, 0, 2 => 0xca8a6259535d6a18472355d69e9b7235500d69b7b4b4e3a15b40355ba965b4b405d6baab5b455d6a88a72355bab59b65405d6bba55b485d6ca8f72595baa576755b500d69e6c354d68a7c4a355d9ba8e5b595d6ba9e6c355
  | 4, 0, 3 => 0xe0baa57835500d69e5b484d69e8a6c355ba9b93775b5d6ba9e5b485bab59b5b4b58a5b534f2c5d6a59e6c355ba989669405d6ca9b7c4b58e5b59534e5d68a7e62595d08a6940345d69e5b44355d69e9b5b595baa55b48475
  | 4, 0, 4 => 0x8a807e40355d6ba745b595d69e8a5b485d6a59e5b485d68a724a355d6cab876405e0ba9b78405e0ba9765405d68e7e5b595d6ca8a6b595d6ca9e6c355d68a72504f5ba8a6259545
  | 5, 0, 0 => 0xba968a6940356d6bd8a5b4b356ba968a5b4030600d6ba5b59095e0ba9b5b4b406e1ca8a7240356d69f8a5b3d356ba8a76755b406e0d0a55b40356d7ba9b5b4030600d6ca8e5b595d68e8a5b594e6d6ba8a6b5b596ba8a794840356d6caab8a72356d6ba965b40306
  | 5, 0, 1 => 0xd6baab5b3b306e0ba975b40306ba8a806959406e0baa55b48356d6ba8e5b5919600d69b5b4b495d6baa57a5b486d6ba9b5b4b45600e0ba9869405d6ca8a7c4b356d6baab8e5b596d6a59d6a5b356ba7f735b4035600d6baa5765b5d6c7ba9b5b4b6d9ba8a5b592c6
  | 5, 0, 2 => 0xd6ba8a5b59456d6baa55b52356e0d08a6940356e0d6ba8e5b596d6baa5785b356d6ca9e5b39356e5d6ba8e5b596d6a19e5b40356e0ba736940356ba938a5b593b6d6caa58a5b486ba9b938a5b4b600d6ba9b5b1a5d6d1baa55b486d6d3ba9b5b4b600baa55b48015
  | 5, 0, 3 => 0xd6ca845b4840600e0ba9b65405e0ba968a69406d6ba9c695b596d6ba9b5b4b1a6d6ca8a81402f6ba8a5b4847406baa55b4846356e0ba8e8a5b59600d6ba8e5b195d98a5b4e40356d6ca9b7240306ba9b935b44406d6ca8a7250356ba9b5b5344406d6bab8765b406
  | 5, 0, 4 => 0xd6baa55b48076ca8a725953356d6ca9b8a72596d69d8a5b4b356d6ca8a7251356d6caa18a72356e0c18a5b59406d6bab38e5b596e79e8a5b403568a7e5b5340356d68a625b594e6ddd6ba9b5b4b6e0bab66340356d6c5ba9b5b4b6d6baa5695b486ca8a805940356
  | 5, 0, 5 => 0xd6ba8e5b59446e0baa59b69406d6d4baa55b486d6baa57a5b356d6ca8a72592f6d6ba9c815b3568a5b59534e2c6d6c8ba8e5b596baab935b40306d6baa59b5b596ba8a69595440600d6ba5b3a355d6ca9f8a72356e9d6ba9b5b4b6d68a724f4035600d6ba9b4b185
  | 5, 0, 6 => 0xd6bab6a55b596d6bab69b5b4b6ba8a5b474035600ba8e5b59535d6bab29b5b4b600d6ca9b65405e0a59d5b39356d6baab5b442c6ba8a5b5540346d6baa576725b6d6d1ba8e5b596ba8a5b563f35600ba8e5b5901500ba8a6954405d6ba9b775b356d6caba9b65406
  | 5, 0, 7 => 0xd6a59b5b594e6e0d6ba9b6540600d6ba8a5b2e5e4d6baa55b48600e0ba9b5b4b5d6ba8b5b40356d6caa15b59356e0ba8a7840356d6a59d5b48356d6ba9b5b4b3b6d6baa59b5b4b6d69b8a5b4b496ba8a795b48406d6ba8a5b592e6ba8a5b5654356ba9b93655b406
  | 5, 0, 8 => 0xe4d6ba765b406d6ca8f7240356d6ba8a665b596d6a68a5a40356d6baa5765b356d6baa56b5b356d6baa55b3a356e0ba9b6963406d6c6baa55b486d6ba8e5b59116d6ca8a5e40356e0ba9b8a654068a5b534f40356d6bab2a55b4d6e0ba8a6948406d6ba9b685b406
  | 5, 0, 9 => 0xd6ca9b5b4b5d6ba9e8a72356baa5935b3b356ba8a69403f346e0baa55b44356ca8a5b59532c600d6a55b48035d6a88a5b40356d6ba8a724f356e0ba8a7a40356ba735b5340356e0baa59b5b596e0ba876540356d6caba9b5b4b6bab59b8a69406d6ba8a5c40356
  | 5, 0, 10 => 0xbab59b5b4030600ba8a7948405e0d6ba9b5b4b6d6baa55b482b6d6ba948a5b596d6a1845b40356d69e9b5b40356d6baab9b5b4b6d6ca9b8a6540600d69e8a72355d6ba8e5b59456d69b5b4e4440600e0ba8a62595d68a7e5b592c6ba968a5b59406d6baa55b45356
  | 5, 0, 11 => 0xd6ba8e5b59096ba9b968a69406ba8a5b59542c6e38a5b403d356d6bab38a5b596a58a5b534e35600d69e5b39355e9d6ba8e5b59600d6ca8a72505d6ca8a767240600d6ba8e59185d6baa59b815b6d6baa55b4c356d6caba8a62596d9bc8a5b40356e0ba9b5b44406
  | 5, 0, 12 => 0xd6ba8e815b596d6beba8a5b596ba9b965b403068a7f7d5b40356d6ba735b592c6d6ca8a6b4035600d6ba5b4b085ca8a5b4846406d6bab88a5b4d600ba9b935b4b5d6ca9b8a5b4b6d6bab28e5b596e0ba8a6954406d68a84723d356aaa68a5b40356d6a59d9b5b596
  | 6, 0, 0 => 0xd6ba9b8a5b4b407d6ba998a5b40357d6ba8a5b59442c7d6beba8a5b4035700d6a59d5b39356d6ba978a5b40357ddd6ca8a5b59357e0baa58a5b39357d6ca8a724035147d6bb8a5b4035077d6ba8a5b4035067d6ba73725b40357d6ba9b845b40357e0ba8a5b4035197d6bab68a5b5940700d6ca8a72402b6
  | 6, 0, 1 => 0xe0ba8a5b4037357e0bfba8a5b4035700e0d08a5b40356d6baa55b393531700d6ca5b402b116d6d1ba8a5b592c7d6ba8a5b403527700ba8a5b592c016d6bab25b4035267e8d69d8a5b4035700d640351811036e0baa58a5b59357bab29b935b40357d6caba8a5b4b357d6ca8a724035117d6ba9b5b4030087
  | 6, 0, 2 => 0xd6ca8a5b4f40357d6ba958a5b40357d6ba8d8a5b40357d6baa55b403526700ba8a5b59532c6d6ba8a775b40357e4d6ba8a5b48407baa59b935b40357d6ba8a5b40350c7d6bab18a5b4035700d6caa15b4035600d6ba5b3935076d6ba8a5b403523700e0ba8a6c40356d6baa5895b40357d6ceba8a5b40357
  | 6, 0, 3 => 0xd6bab8a55b39357d6ca8a724035337d6ba8a5d5b40357d6ca8a847240357d6bab28a5b4d407d6ca9e8a5b403570000d6ba9b5b4b5d68a5b4e4440357d6baac8a5b40357d6d1ba635b40357d6baab8a695b4078a5b59534e40357d69b8a5b594e407d6baa58a6c5b357d6ba8a5b403507700d6ca8a5b4b356
  | 6, 0, 4 => 0xd6ba8a5b434035700e0ba694035116d6baa38a5b40357d6baa58a695b597ba9b968a5b40357dbd6ba8a5b4840700d65b352411036d6c6ba8a5b48407e0d08a875b4035700d6ba9b635b406d6ba8a6d5b40357d6caba8e5b4035700e0ba8a6959406d6bab88a5b3c357baabaa8a5b4035700d6ba352418116
  | 6, 0, 5 => 0xd6caab8a5b40357e0d6ba8a5b4b357d6ca8a725940357d6ca8a726a4035700d6ca8e5b40356d6ba8a6b5b40357e0baa28a5b40357008a5b534e40356e4d6ba9b5b40307ba9b938a5b4030700d68a5b3524026d6ca8a5b4035297bab6b48a5b40357d6ba8a715b40357d6baab5b4440357d6d3ba9b5b40307
  | 6, 0, 6 => 0xe0d1baa55b40357bab6938a5b40357d6ba8a5b592c117d6caba8a6c40357d6caa58a5b39357d6ba8a5b403528700ca8a5b402b016d6baa55b5944357d6ba81735b40357d6baa56a5b4035700baa55b393501600d6ba5b4035096008a40351803016d6ba8a5b4035047d6ba8a77695b357d6cfba8a5b40357
  | 6, 0, 7 => 0xd6c5ba9b5b40307d6ba9b8a5b4840700d6ba5b4b3511600e05b40351103600e0ba8a5b56356e0ba8a5b444035700d68a5b4840036e2d6ca8a7240357d6ba9a8a5b40357d6ba8a5b40350f7d6d1baa55b59357e9d6ba8a5b48407e0ba8a5b40351d7e4d6ca8a724035700d6ba8a4840186e0ba9b8a5b59407
  | 6, 0, 8 => 0xd6ba8a5b2b246d6ba8a5b4035217d6ca845b4039357d6ba8a5b4140357e0ba8a835b40357d6ba968a5b4035700ba8a35241801600d6baa55b44356d6baa58a815b35700d6ca8a6c40356e5d6ba8e5b4035700d6baa59b5b596d6ca8a5b4037357ddd6ba9b5b4030700e0ba8a4035166ba938a5b403b357
  | 6, 0, 9 => 0xd6ab9d8a5b40357ba8a695b5953407d6ba8c8a5b40357ddd6ca8a724035700d6ca8a723d356e9d6ba9b5b40307d6ba9c695b4035700d6ba9b4030186d6ba8a5b40351f7e0ba8e8a5b40357d6ca8a5b5040357d7ba9b8a5b40357d6baa5695b39357008a5b352403016d6ba8a5b4035227dbd6ca8a7240357
  | 6, 0, 10 => 0xd6ba8a5b40351c7d6a59d8a5b59357ddd6ba9b8a5b597e0a59d8a5b40357d6bab38e5b40357d6ba8a5b40350b7e0d6ba8a6c40357d6ba8a5b40351a7d6ba8a6e5b40357d6baab8a5b3b357e0ba978a5b40357d6ba8a5b48402b7d6bab28a5b4840700e0ba9b8a6940600d6baa55b392b6d68a5b4b4940357
  | 6, 0, 11 => 0xd6d1ba5b40351d7d6ba8a7c5b4b357d6ba8a5b5740357e0ba8a5b4035077e0d6ba8a6959407e0ba8a5b5940347d6d4baa55b3935700d6ba8a2b24186d6ba9b825b40357d6ba8a705b40357d6ca8a5b5140357d6caa18a5b40357d6ba908a5b40357d6ca9b8a7240357e0ba8a696740357d6ba8a6f5b40357
  | 6, 0, 12 => 0xd68a7e5b5940357d6baa59b5b4030700ba8a694035006ba8a815b5340357d6ca8a7240352f700e0ba8a69402b6d6ba8a5b4c40357ba8a875b4035347d6cac98a5b4035700d6ba9b8a5b4b6ded6ba8a5b48407d6bab29b5b40307d6ca8a5b40351d700d68a5b2b24036d6baa59b5b40357ca8a5b595340357
  | 6, 0, 13 => 0xd6ba8a5b4035097d6ba9b855b4035700d6ca5b352411600e0ba9b5b40306d9ba8a5b4035197d6ca8a5b4035127d6ba8a815b402f700dcca8a5b4035600ba8a5b4846406d6ca8a7240352b7d6d1ba8e5b40357e0ba8a5b403508700ba8e5b403501600d6ba8a775b356e0baa38a5b40357d6ba8a5b4035207
  | 6, 0, 14 => 0xe9d6ba8a5b592c7e0ba8a5b40350f7d6ba928a5b4035700d6ba8a592c186008a5b403503006d6c2ba8a5b48407e4d6ba9b695b407ba9b938a695b407ba8a5b53403519700d6ba8a5b401b6baab8a5b5340357d6ca8a865b4035700e08a5b402b036d6caa58a7240357d6bab6a55b40357d6ca9b845b40357
  | 6, 0, 15 => 0xd6baae8a5b40357d6ba8a5b40351e7d6c4ba8a5b40357d6baa59b5b4031700e0ba8a5b2b246d6ba918a5b40357d6bab29b5b40327d6ba8a5b5840357e0ba8a694039357ba8a725b5953357d6bab28a5b3e357d6ba9b8a5b593b7d6baa59b8a5b597d6bab08a5b40357d6ba8a5b4035157e4d6baa55b39357
  | 6, 1, 0 => 0xd6ba8a615b40357ddd6c2ba8a5b597d6bab28a5b592c7d6bab86a5b40357d6caba9b5b40307dfd6ba8a5b592c7d6ba8e5b4035117d6c0ba8a5b40357d6baa5855b40357d6ba8a725b592f700ba8a5b3524006d6baaf8a5b40357e0d6ba9b8a6940700d65b403511026d6ba8a5b403510700d6ca8a5b48406
  | 6, 1, 1 => 0xd6ba5b40370a6005b40351103016d6baab9b5b40307e0baa59b5b4035700d6ba5b402b116d69d8a5b4035077dfd68a5b4e40357d6ca8a81724035700d6a55b3935036e0baa48a5b40357d6ba8a5b403835700d6ba9b655b4060000d6ba8e5b595e0ba8a5b4b4035700d6ca9b5b40306ba8a5b595440357
  | 6, 1, 2 => 0xd6ca8a5b40351f7d6ba8a5b48401b700e0ba8a624035600d6ba5b40352d6d6bab2ab5b40357e0d6ba9b5b4030700d68a352418036d6ba8a5b4036357d6ba88695b40357d6ba8a5b4f40357d6ba8a605b4035700ba8a5b5440356ba9b8a5b5953407e4d6ba8a5b4b35700e0ba8a5b592c6d6baa59b5b59357
  | 6, 1, 3 => 0xd6caba8a5b592c7d6ba8a5b40352a7d6ba8a5b40350e7d6ca8a5b4b40357d6baa5726a5b357d6ba8a5b4035197d6c2ba8a725b597d6baab8a5b40357d6ba735b5940357d6ba948a5b4035700d69e8a5b40356d6bab2a55b59357d6baa59b695b407d6baa55b39352b700ba5b35241101600e08a694035036
  | 6, 1, 4 => 0xd6c3ba8a5b4035700d6ba5b2b24116d6caba8a6240357d6baab8a5a40357d6ba8a785b40357d6ba9b5b4440357d6bfba8a5b40357e0c4ba8a5b40357e0bab68a6940357d6bab98a5b4035700d6ba735b40356d6baa58a5b5935700d6ba9b5b4b40600d68a5b4b35036ddd68a5b594e357d6ba8a815b592c7
  | 6, 1, 5 => 0xd6bab28e5b4035700d6ba5b592c116d6baad8a5b4035700d6ba8a5b2c196d9ba8a5b5940357d6ba8e5b4035097ba8a5b403f3534700d6ba8e8a5b596d6bab38a5b40357d6ba8a695b48407bab59b8a5b40357d6ba8a5b592c197e9d6ba8e5b40357d6baab8a5b592c7d6ba8a5b40350d700d6ba8e4035186
  | 6, 1, 6 => 0xd6ba8a625b596d6ba8a5b4035137d6ba8a7a5b40357ba8a817f5b40357d6ba8a5b4035177
  | 7, 0, 0 => 0xd8d6ba5b40351170000ba8a40351801600d6ba5b40352c117d6bab28a5b403532800e4d6ba8a5b402b700d6a59d8a5b40357d6ba8a5b594035118d6d5bab28a5b4035800d6ba5b40352b11700d6bab25b4035117d6ccba8a725b4035800d6ba8a5f5b4035700d6ba8a865b40357ddd6d1ba8a5b40358e4d6ba8a695b4035800c5ba8a5b4035017
  | 7, 0, 1 => 0xddd6ba8a695b40358d6bab8b28a5b4035800d6ba8a5b4035077d6c5ba8a695b40358d6d1ba9b8a5b4035800d6ba8a5b403514700ba9b8a5b4035017e4d6ba8a5b403511800d6baa58a725b35700008a5b4035030160000d6ba8a5b402b600d6ba725b4035117d6baa58a5b403531800d6d1ba8a403518700d6baa55b4035117dbd6ba8a695b40358
  | 7, 0, 2 => 0xdbd6ba8a5b403511800ddd6ba8a5b402b7d6bab88a725b4035800d6c5ba8a5b402b7d6bab8a58a5b4035800e0ba8a5b403f35700d6ba8a5b403526700d6ba8a5b35241d700e4d6ba9b5b40357d6caba8a5b4035308e4d6ba8a5b403524800d6ba8a895b4035700dbd6ba8a5b402b70000e0ba5b403511600d6ba8a5b40351170000d6ba8a5b48406
  | 7, 0, 3 => 0xd6ba9b5b40306d6d1bab28a5b4035800ba8a5b40352b01700d6ba8a845b4035700bab28a5b4035017ddd6ba8a5b4035118d6ba9b8a695b40358dbd6ba8a5b403524800d6ba8a655b40357e0d6c2ba8a5b4035800d68a695b403503700d6ca8a5b4035307e9d6ba8a695b403580000ba8a5b352401600d6ba8a625b40357e6d6ba9b8a5b40358
  | 7, 0, 4 => 0xd68a5b40351103700d6ba8a695b35247e9d6ba8a5b403511800d6c2ba5b403511700d6ba8a403518117e4d6ba8a5b5940358d6d1baa58a5b4035800baa58a5b403501700d6ba9b8a5b402b7d6d1ba8a5b40352c800ba8a5b40352c01700d6c2ba8a5b59407e4d6ba8a5b403935800d6caba8a724035700e9d6ba8a5b402b70000d6ba8a402b186
  | 7, 0, 5 => 0xd6ba9b8a5b4035088d6baa58a695b40358dbd6ba8a5b59403580000d6ba8a5b2b246d6ba9b8a5b403524800d6ba8a5b424035700e0d1ba8a5b40357dbd6ba8a5b4039358e9d6ba8a5b403524800d6ba8a403524187e0d6ba8a5b403530800d6caba5b4035117d6ba9b8a5b40351180000d6ca8a724035600d6ba8a5b594035700d6ba8a6a5b40357
  | 7, 0, 6 => 0xd6bab28a5b4035248d6ba8a725b403514800d6ba8a594035187d6ba9b8a5b403935800d6ba8a5b403505700d68a5b403935037e4d6c5ba8a5b40358e9d6ba8a5b4039358d6ba8a5b40352b11800d6baa58a5b402b7d6bab28a5b403511800d6ba8a40393518700d6ba5b40353011700d6ba8a5b3524117ddd6ba8a5b594035800d6bab28a5b402b7
  | 7, 0, 7 => 0xd6ba5b4037351170000ba8a5b403500600caba8a5b4035017d6cbba8a695b4035800d6ba5b4035110a70000e0ba8a5b402b6d6ba9b8a5b5940358d6ba8a725b403511800d6ba8a5b402b25700c2ba8a5b403501700d6bab29b5b4035700d68a5b594035037d6ba8a5b40352c11800d6ba8a5b4b40357d6ba8a5b40352b248e9d6ba8a5b5940358
  | 7, 0, 8 => 0xd6c2ba8a695b40358dfd6ba8a5b5940358d6ba8a5b4039352b8d6bab28a5b403935800d6ba9b8a5b4035700d6ba8a5b593524700e0ba8a5b40352470000ca8a5b4035016ddd6c5ba8a5b4035800d68a5b594e40357d6d3ba9b8a5b4035800e4d68a5b403503700e0ba8a5b40351170000d6ba8a5b592c600d6baa59b5b40357dbd6c5ba8a5b40358
  | 7, 0, 9 => 0xe0d6d1ba8a5b40358e4d6ba8a5b40352b800d6caba8a5b402b7ddd6ba9b8a5b40358d6ba8a725b5940358d6c5ba9b8a5b4035800d6c2ba8a5b402b700ddd6ba8a403518700e4d6ba8a5b35247d6ba8a69635b40358d6ba8a81695b4035800d6ba9b8a5b40307dbd6ba9b8a5b4035800d6ca8a5b403d357d6bab28a5b594035800dbd6ba8a4035187
  | 7, 0, 10 => 0xd6ca8a5b4035247ddd6bab28a5b4035800d6d1ba5b40351170000ba5b403511016d6bab28a5b4035058d6caba8a5b4035248dbd6bab28a5b40358e9d6ba9b8a5b403580000d6ca8a5b402b600d6ba9b8a4035187e4d6ba8a725b40358d6c2ba8a5b4035248d6caba8a5b403511800e0ba8a5b594035700e9d6ba8a403518700d6bab68a5b40357
  | 7, 0, 11 => 0xd6ba8a5b4035110a8e9d6ba8a5b40352c8d6caba8a5b594035800d6ba8a40352c187d6bab29b8a5b4035800e0c5ba8a5b4035700d68a5b40352b03700d6ca8a845b4035700d6ba8a855b4035700d6ba5f5b4035117e9d6bab28a5b4035800e0d6ba8a5b402b7d6c2ba8a5b403935800d6ba8a695b594070000d68a5b3524036ddd6baa58a5b40358
  | 7, 0, 12 => 0xd6bab28a5b40352c8e4d6ba8a5b4035308dbd6caba8a5b40358d6ba8a5b59403519800d6ba8a725b35247d6baab8a5b594035800d6ba8a815b40357d6ba8a725b40352f800e0ba9b8a5b4035700d6ba8a5b352b2470000d6ba5b402b116d6baa59b8a5b40358e0d6ba8a5b403524800d6ca8a5b403935700d68a725b4035037d6ba8a815b5940358
  | 7, 0, 13 => 0xd6ba8a5b59444035800dbd6ba5b4035117d6baab9b8a5b403580000d6ba5b403511600d68a5b403530037d6caba9b8a5b4035800d6baa58a5b5935700d6ba5b59403511700e0baa58a5b4035700e0ba8a5b40352c700ddd6ca8a5b4035700d6ba8a5b403519700d6baab8a5b403570000d6ba8e5b40356d6ba8a725b40352b8ddd6c2ba8a5b40358
  | 7, 0, 14 => 0xd6ba8e8a5b40357d6ba8a725b4035308e4d6d1ba8a5b4035800d6ba8a5b444035700e9d6ba5b40351170000d6ba40351811600d6ba8a5b3530247d6cabaa58a5b40358d6caba8a5b40352c8
  | 8, 0, 0 => 0xd6ba8a5b40352c7d6bab28a5b40357d6ba9b8a5b4035700d68a5b4035036e9d6ba8a5b4035700d6ba8a4035186ddd6ba8a5b40357dbd6ba8a5b4035700d6ba8a5b40356e4d6ba8a5b40357d6ba8a5b5940357d6ba8a5b4039357d6ba8a5b4035247d6ba8a5b403511700d6ba8a5b402b6d6ba8a695b40357
  | 8, 0, 1 => 0xd6ba5b4035116d6caba8a5b4035700e0ba8a5b40356
  | 9, 0, 0 => 0xd6ba8a5b40356
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 28
  | 3 => 36
  | 4 => 44
  | 5 => 52
  | 6 => 60
  | 7 => 68
  | 8 => 60
  | 9 => 52
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1f1c23fc00e0c7c708e1003800303e07c001fc0c0081f0000300ffe003ffffc038f800ffc7f00001fffffffc000071fffc7f
  | 0, 1 => 0x1f1fe38000e007c7f8000007c1f03c3fc001f0707f0e0003fc0003c078001fc000001e000731f1fe3fc00e3c7c7f8e10038c
  | 0, 2 => 0xe3e3fc7c7f03f8f8ff011c40ce3e3fc7c0f1ff8f80f1f03c03e3e03c04010007fff8fffffff1f1fe3fc00ffc7c7f8ff00000
  | 0, 3 => 0xff1c1ffc00e03fc007ff03803e0e01c000f00070700fe03b83ffffff8401e33fff0fff00783fffc3f8401e038f8ff1fffc7f
  | 0, 4 => 0xe0e3dc007103383807001c4000003c00070033fff0fff03f83fffc3c000f003fff08e000380fffc20780e00fff807ff03c00
  | 0, 5 => 0x3801c3fff0fe1e07f01f1fe3ff80ffc0000000e0070ffffff8471e33fffffe100000ff1c1f8400e03f3f07e01c780
  | 0, 6 => 0x1f1fe3ff8effc0c0f81fe387f0000007b8e1cc00000000000000000078000000000000e3800000000038e1c00000000e3800
  | 0, 7 => 0x3c000000000000000fc00000000000000000000000fc00000000003f01c07c708fffc38300000003f0003838071ee3c73
  | 0, 8 => 0x3fe1c00000000ff800e3e3fc07f11f07c7f8fffc3ff1f1fe387f0ff0000f000fc07c
  | 0, 9 => 0x7800000000001e000000000007bfe1cc0000000ff8000003c003fe1f00000000000000000000000000000001eff873
  | 0, 10 => 0x3c003fe000000f000fc07c0003c07b8e1cc000f000000000003c00000000000001eff8000003c07bf01f0000001ee3873
  | 0, 11 => 0x1f1fe3fc00ffc7c7f8e10038c1f1c23fc00e0c7c708e1003801c1c038000e000000000000000003c07bfe1fc000f01e00000
  | 0, 12 => 0x1c1c038000e007070000e00701c1c03838ee000000000e3870000000038e00070700e0e03f0fcfc1f800fe03fff0fe100780
  | 0, 13 => 0x1c1fc003801c070000e0fc0001c000383801c070700e0fc38000000003f01c00000000fc0001c1c03fb8efcc7070000e3800
  | 0, 14 => 0x3c003fe1f0000001eff87300000000000000000000ff87000000003fe000707f0e0fc3fc1c1fc38000000707f000fc000
  | 0, 15 => 0x1c1fc0000000070700fe003801c0003f800000707f0e0ffbfc1c1c038000e0070700feffbf31c1c038000e0070700e0ffb80
  | 1, 0 => 0xe0e00000000038380000fc000e0e000038e003800070000000e0001c03f00038000700e38001c1fc3fbfeffc707f0e000380
  | 1, 1 => 0xe0e01c03ff1c38380700ffc70fffc3f87ffe038f8ff01ffc0ce3e03c07ff0038380700ffc00e0e01c00000038380000e3800
  | 1, 2 => 0xe0e0007b8e1cf838000000000e0e0007bfe1cf8380000fc070e0e0000000003800071e00000e0001c7bfe1cf800071efc070
  | 1, 3 => 0xe003dc03f01f3800070000000e0001c00000038380700ffc70e0e01c7bff1cf838071ee3873e0e01c78000038380700ffc00
  | 1, 4 => 0xe0001c0000003800071e00000e0e3dc03ff1f3838f700ffc00e0e3c003f01f3838f00000000e0e01c03ff003800070000000
  | 1, 5 => 0xfcfc0383f0e03f3f00e0e3b80fcfc00038e003f0007e0e3800e0e3dc7bff1ff838f00000000e0e0000000003800071e00000
  | 1, 6 => 0xfc1c1f8000e03f3f07feffff3fcfc038000e03f3f000000000fcfc1f83fffc3f3f07e0fff80fcfc1f8000e03f3f07e000000
  | 1, 7 => 0xff00038000003fc00000e0070fffc3ffc01e0ffff0fff00780ff1c3ffc00e0ffc007ff00000fcffdffbffffff3ff7e0ffffc
  | 1, 8 => 0xff03dffffe1f3fc007ffff873ff03dffff01f3fc0f0e000000ff03c07b801c3fc007ffe3873ff001ffc00003fc00700e3800
  | 1, 9 => 0xffe0038000003ff8001ee3800ff1c1ffc00e03fc7f7fffc3fcff1c1fff8efcffc707ff00380ff1c1c0000003fc0f7ffff87f
  | 1, 10 => 0xffffe38400e33ffff80000000fffc1fffffe03ff8f7ffffc7cffe01fffff1cfff807ff00000ffe01fffff003ff807ff00000
  | 1, 11 => 0xffffe07bfe1ffffff81eff873ffffe003f01f3ffff80000000ffffe07b8e1cffffffe10078cffffff8401e03ffff8ff003ff
  | 1, 12 => 0xfffffc0000003fffff1effc73fffffc03ff1c3fffff00ffc00fffffc0000003ffff8e0fc3fcffffe38000e03ffff8e000380
  | 1, 13 => 0xfffffffc00003fffff00ffc7c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x50420d00020c0000000000000302604c001a804008100000200fde002dbf5c01858009204200001fbdb7ef4000030b49028
  | 0, 1 => 0xf0ee1d00075c3c3b8530017e0f0ac1dc005f0383b067001fd0f0ee1dc007fc1411836000f30f0ea1d40063c282a0410010c
  | 0, 2 => 0x63632c646c029090c201180082322646c0c1a884809180300200000000000003dbf877921ff0f0ee1dc007fc3c3b8770006a
  | 0, 3 => 0xb59416f007a06d490dbc03883b0b016200f802d6d0dbc03e839a9a930401c325650cb40068390901200018018d8db1bdb06a
  | 0, 4 => 0xdadb9b0471c3343446801c6004a4b890470432d6d0dbc03e83b5b436600f80ad6d0cb402e83b5b424f00e20ed6c05bc03e00
  | 0, 5 => 0x404409b823c64241482e06700f0ee1df807fc0001002e0070dadb9b0471c336b6e6c118008da9a9b0431c3363666c01c704
  | 0, 6 => 0x2f2ee5ff8e7fc9c9993fe38fb252464fb8e3cc9491834a28d3250404f9862c4909012ce38912020442b8e1c08080108e3800
  | 0, 7 => 0x4a4bc102d0551292e243fc13c4a0a890db04f12126240fc1144041480bf01c11514a34fc08340410803f0002d6d1dbee3ef3
  | 0, 8 => 0x656560d2da34d95958109204260614c2bfe1c18184308ff8004a4bc90ff05f13d3fa77fc1ff4a4bc90ff05f1292f243fc17c
  | 0, 9 => 0x6f0e8dfdb66f5bc0837f490286d6dedfbfe7ddb1b636cff9956a6bcd2ffe5f1a82a34b6d93c6a020d2d240a19595b3eff8f3
  | 0, 10 => 0x6f6fec63fe109bdbfa77fe9ff6f6fe5fbde7ddbdbf874b69d76f6fe04248109bd8c37fff8286f4fcdfff67f5bcbbb7fef9ff
  | 0, 11 => 0x9f9ef3dc93ffe7a7a4e524f9d9d9cb3d093e5e72724e424f959c9c939093e5672724e424f956f6fedfffe7fdbdbfb7fdb06a
  | 0, 12 => 0xbdbcf3d29bf5ef6f3852e6176bcbc97b39fe56e2e35cae7f74b0b016239f80272734e6e4ff5bcbc97b09fe5672724e424f95
  | 0, 13 => 0xdedfc09bc23c77b4c6e7fce28de065b9fa23e773766e4fcf95d4d55a9bf3bc74344680fce00bdbcf7fb9ffdef6f3d98e7e42
  | 0, 14 => 0xfafbdf2fffdf3d7d5fbeffef3f5f560424810bc3c578affe70f0f11e23ff8037b7f6e7fcffddedfdb9f601a37b7f680fce40
  | 0, 15 => 0xffffe0424810bfe7a7ff6dfbdff021ffd240a3fbff7efffffdfe9e9fbdb7ef7f7f7ffeffff7fdfdf3d2dbf5ff3f67ecfff95
  | 1, 0 => 0xf0f11202db803c3c4200fe000f0f10423ce003c2407886de00f0411e23f4003c080788eb800fffffffffffffffffcf4b6fd7
  | 1, 1 => 0xf4f55ebbffbc7c3c578affe70f0f11e23ff803cbcc789ffe08f0f11e23ff803c3c4788ffe00f0f11e236c003c3c4588f7e00
  | 1, 2 => 0xf5f576fbdfbcfd7d5cb4b6ed3f5f56cfbfe3cfd7d5a12fe072f5f560424810bd6507be6deb1f5657efbfe3cfd5057befd070
  | 1, 3 => 0xfadbdf2ff7df3ea6a7cb6df3cfa021f2d240a3e3e77cafff74f5f57efbffbcfd7d5fbefb8f3f5f57efb6c18bd7d5fbcffed3
  | 1, 4 => 0xff677f6f6c1abfc087ff49028fafbdf2fffdf3ebef7c8fff54fafbdb0ffbdf3ebef4c0b6f54fafb9f2fffcf3ebef7cbfff7c
  | 1, 5 => 0xfcfd9b93fbe57f3f65ecf7f95fcfd84b3ce247f0907eceb891fffffffffffffffff81092042fff77fffffbeffe7a7ff6dfbd
  | 1, 6 => 0xfe9e9fbdb7ef7f7f7ffeffff7fdfdf3d2dbf5ff7f781092042fcfddfbbfffd7f3f67ecfff95fcfd9fb3ffe57f3f67ecdb000
  | 1, 7 => 0xff2673d28a34ffc99a53ea07aff963ffd25aaffe487ff49628ff063ffd242affc087ff49028ffffffffffffffbff7efffffd
  | 1, 8 => 0xff6bdffffe5f3fd9dfffff8fbff4bdffff45f3fd2f4f4b4154ff4bc4fbc41c3fc99fffeb8fbff267fffae3effc99f98eb842
  | 1, 9 => 0xfff313d2db803ffcc13ef3820fffffffffffffff7f7fffdffdffbeffffbfffffe7a7ff6dfbdff9e9e61b7803fdbffffff9ff
  | 1, 10 => 0xffffe1464853bffff81092042ffff9fffffef7ffef7fffff7cfff77fffffbefffddfffffefbfff31fffff8a3ffcc7ffffe28
  | 1, 11 => 0xffffedfffe7ffffffb3eff8f3ffffe94ff85fbffffa53fe17effffe4fbce3cfffffcd19274efffff2424990bffff877921ff
  | 1, 12 => 0xffffff6fffdfbfffffbeffef3fffffe6bff9cbfffff98ffe42fffffe63ff90bffffef7feffffffffbdffbfffffffcf4b6fd7
  | 1, 13 => 0xffffffff6c1abfffffdbfff7e
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 50 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 50 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 234 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 234 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 234 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 234 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 10 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 3 => 12
  | 4 => 110
  | 5 => 420
  | 6 => 966
  | 7 => 506
  | 8 => 9
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xc0140fc6b5527ca8975bad8f8e91b4fd615757e660fbf21a4c0fa57d228668e821bee53905521be70509216500379476
  | 4, 0 => 0x576404914eed39d94e5f136a4bd1c7de4b79d9074b0540144a9a02f74a749f9946f1ec71462b3b1344791ed0420259c841aeb9623e868f1c3e5475bb3d8777ad3d4f9f983ce7516c3c9588503854053e37c3fb6136ab91a735c098d535235c9534db1b6334afd98132c1f92e31570937305d9cba3046f6a9299b847527ce3e89274a8bd926470f6e260925922607afaf214255022110368a1f7dcd761d6767941d25cc8d1d0cab6b1b3802ec1877e12a18437cfd182659b6176d640f16008c7d14ea3fe5139e6d2013857f691367ffd213014f44120f59b00e5deb580dd58f05099ca60108c6a7eb04933ce9043d47dc0413723b023b93cb005be7ef003f4606
  | 4, 1 => 0xda35d2e4cfac33c4cec5fbb1ccab0e83c95352b0c029dfb3b8d114c5b3ff953eb118dcdbaf4c88b0adcc2032acf82a6da8627d3ea63085d2a5224220a3f4cfef98985da594c167a68fe512ff8cf5582d8ca16d7a8a85ffa588871362862ee00b84e790348420418182a7a9e381b4f9c8814ca8507dcf50ff7805f298770cac0c76bd46bc73f0c8be717a84e0701ebe506e6bda786d627d076c9cf00f6befdc686baa008f698c3de85d39e9e55c23bcb55a85ccbc595b2f00
  | 5, 0 => 0x13a53e1f1331b78412ec37261299497c125dee4811f91a67119dfe101120e2e31109bf1b108a86741010fcf00ff40bed0fd0edc50f07d9720ef402390ef08abd0e55716a0e15721d0cd92b840cd49b0a0c8b5f720c69bfd00c2777f60c21c3560bb3743f0b840bd10b7002330b2eab570a7e198b0a70ebbf0a6c694b09f4089109d0c57e09adf9d1094c6da808bc39d80807792307e998db07d36683072cba91070fcc2906f6939e06c355f70633e36b05f5b00605f2f0ac05c2ee470594b86104c7c15104b4455c04751f93045ebda7045412d003b1c3d003a3e4f103421fa9028c0b6e0261d2e0025ca66c0223c06a00e3021600c274f100c14c7d00904f93
  | 5, 1 => 0x292e252a29240e0e28a54c982884fdf82874ed462865d77a281b1aa42810052827e4c34027b671de27add3f227a8a3f52723e9ab2705880d252438a924aac5eb247cfe3f2442422e23a00a16223ecfe821a77dae217c18ce214f7c6c2075da64206d0bcf1fc09e2b1f426e131ee50e861ee3e86d1ee233921e4defbc1e02d8001d51061c1cc76a471c9684861c4c210a1c05c5ba1bc24f8a1b9386ad1b15d8b91adf1ef61ab883531a09d18719bb0557194f2d80194e3edd1900873518f26c4c18ae189c187d0f6b182539bf17e8f1d8176d640f176346e016ecceb9169f119e1678242815dac5e915466c5f153eaa1814b9cc04145cbdf713bf8c2413aa57d6
  | 5, 2 => 0x41ea896c41bf37ea408a682f40722d163fdedec33fc4defb3fad8f4c3f8bbd3f3f037a0c3e56c1683dbefb303d505c953d29c89f3ceaa2193c3b0ee53c1fa3d43b6273ae3a84e7713a4d6a953a45c8f1390f71bb389a23f937f8c67a37cbacf1377ab9dd376662873761c3f336a8c2383681202535d8db5235c6e9dd35a96a46358a83993547ad913505b6fb34bc82fe343c2582341812ec3378e8ac330f147832afc3ff3283af4331d2bb4a31aa1a7f314cf634314c572830ef49ec30ec886d3000f80e2ff968f32fa7d1792eb983852e80cd732ded0ebb2d5b9c6c2ca4cf692ca07a3e2c7a55332c5ac63c2c4fa6322c45359f2ae793e92a9548642a1fc85a
  | 5, 3 => 0x5f6e35c95f2f7f645f04cb2e5ee284145ed6f2c45e3fd68c5e02d08d5d89ccf35d3cc0765be0d81b5bd9197a5b83bf685aa8a6b95a599a325944e18d58f528b758d5e295585b96c5571446ee56d0090755a7f767553d3ac1550de69c54c755965416395f53fc57df53fb522353e701f4532d8d755318541d5198e0a65141b8185137e594513145914faef7e04f5a105b4e58e5db4e2355ba4e1eb31a4c7acf5f4c2d52984b5841a648889b66486fe2214856c0ff47b4abff471c98aa4712aa5546b110c04643b5a545ce2e29459ecff74578ef99454310ba44b733b344733f614446b2544351a0fe4313dfbf42b779a3429d85804298de82422c19c3421eb534
  | 5, 4 => 0x82fa8ef582b8d63d81c1d1c681b5b6e180f7e88880cdcee27f7b54597f1c9e7d7cf06b427c35140d7bdcd3957b9c99747a38d3487a058b9779e6d45179b090c079835c6e796bd4b779615058792aefd3780e5ba377919af776485825755ba818754b772773faa17673221ae072d0dce572c5d62071a7a8897147b3d97134af5a70e87d7670aa281c707d47f06fe06c296f595e3a6efa94c66cb081016cafc3806c1bc1326bcf90f36b0981336aae5ceb69ebc1aa697d897d695d162a693356e568e553ee67d0201c678c34f8676b923d66276d0265676d1e639c95eb633f74b161f5a73b61e48c9561d138d360b87751605a49426049df53600d69015fc8e221
  | 5, 5 => 0xbb2c743bba68ab79ba61773ab7aa0c84b72f59aeb711e289b702d21ab5671537b4084f90b3d42e0bb0feeee4ae8b5846ad04b00aac94b6d4ac25a728ac04353eabe530a5aad0cdb6a96eba0fa8cc9955a8704a7fa74d14c5a637e8f2a60d590da46a6d8ca400ecdca388d9f5a3105a4fa24442aea1dadcb3a1819cf9a03a41aea01d11f79f18e9fb9e2823d09c04cd539b0d0fc39b09d79c99a181bf993a456c98c0bf6f97ceacc39765c86d95c7f384957ed1db94c167a6937407219268a0bc91c6b2ff911a363b8f8ac4908dfec2528b0594dc8a62980e890db2d2883a715e87e288ad86babd4586a4d00a862ee00b85ac7091847b982684129c40832189ea
  | 5, 6 => 0xf7249a68f3e97183f3d6d53bf0f8df95f0ed67daeeec78f7eec542e3e5f8e4ade1c9df61dff65054ddee3c72d8d7c2ffd874f4b7d8593076d6caf2f8d4b826a0d3b847d9d28e4411d1a5728bcd73df73cbf71b79caec5670caa3e7b2c95b0440c76b6ab0c6a07237c4f7a12bc3db19e1c28adb2cc22ad897c0f654f7bedd9d2abeb8200abe3c3270bcd62099bbffde47
  | 6, 0 => 0x7f92a9407d1c87f07b1fadf078c6002076636a7072f1b210720ca0a0711d49e06fe4f3806ad70f906a14de7068d7fe105c61dd605bbae7e05b43f6005505c7b05169eb004c4bfc004bca65904ac2cb3048dacd7047b57a90472ece0041db66f03ebd78703ebaeda03b671920376fe1b0375c6cf0357f0400341d11b033a727c0337e293030dcc68030d3b3002d6a72e02c16857029bda2f0293b4520289e8080284a245027c6a3c02470b1b02465a510232af7302102cb901e3cad001ad440301a6e4da019c9fad018309d901752afa01652a32013e3f93012a5840011eaa2f010ac53100f5a3d200da586b00a28bea006cf49b006c26840034aae000296567
  | 6, 1 => 0x103a99121004efa21004221f0ff805cc0ff651070fec104b0fceabe00faa77070f8b2a5f0f8899180f8009980f3d84400f31b5270ee2d2210ee271f80ee0af2a0ee057d40ebee7890ea800b80e7e15130e737a980e67dc250dfb96ef0da91e400d91ebc20d7fca5d0d15a3500cfd809b0cedf22c0cd896110c8b5f720c3486130c18c4240c0ba5d40bee5d4b0bcc18bf0bc7415d0bb0c3ae0b9beb890b8ad6cc0b641d450b59e3bd0b05d34b0afb5dd30ab8b2690aa0caca0a577bf40a3ff7660a2d481b0a01f69909ede5f809c9d51a09bd51ef0966c06b093e73560938390c0913c1b1090dfc8408d6f02608b0816608aedd4608ae3d6e08739b70084ecf14
  | 6, 2 => 0x18545dd61839cef018103f88180c2da517fa4d9917e7c6aa17ce2ba217cb86b1177154d6175a929b17563868173aec27172938d717135e9f1708743b16bcc03716b01e5416a61199168bc85d168410e61673385e1665ef1c1661bbe9165a143316424e12163cc666161181741606144c15f3a94215e9498b15d3ee201589d57c157b3ef6155ed0bb153eaa181517feab14db18b514c7480c1499cfe51436a4701409a61313fac4d313ea83c213e90d2b13e0e2a713a53e1f13967e2f138cad001349e7ce133c08ef13346ed1130a5a8912d1fe4012a888d2125d0b7e1233466a122a381911d430a611b4bd5b119b91ab1187183a11408e9a1106ad5710bf6ca6
  | 6, 3 => 0x233e519822e093b2228be26a223ecfe82213883722032e6b2177d42821357f502072a6642065dc9f2062e284204b60b620292edb2014c6442014059b1fa432931f8738591f75faad1f634b621f47d9851f3387171ee50e861ee07af31ea60e4c1ea327491e2acf241e08e1531df468421de45f961db574801d73f5661d0d4e0b1d07cbc61d0122a41ca3d9531ca0b1831c60ae701c5377201c397d011c32bad41b933b9e1b8548e61b78d4bc1b6a04111b62a5db1b27d2611ae5a86a1ac6cf551a87fcc01a58a2341a548add1a4058c31a0dc40d1a04d9791972f1be1923eb0b19224d721921f28d18ef4baf18eabeb418bf975f18ac994f1882b169186366e3
  | 6, 4 => 0x2eba05a82ea06df12e2eb6002dfdbfd52dec4b6b2de6358a2dc576452db09fc22d88ef402d7480b12d618f3b2d52d1502d2230702d1894d92d06d0c22cf8cd042c5dadfc2c3593cc2b4875c42b09ceab2b08f8cc2afda44c2acd7a982a97a7b92a60e87e2a42cf9a2a14d0f72a00355d29f1177429f0b1cd2980ce66297c99f8294399dc293427572930c81a292162fe2920d8b3291d2a9e28e1d56328c73e9828b1318528a4a83e289a985c28668e6d2844d63927b3f541279ad890275958f22750b4f6273a86802713cf002705880d26e2d5ad2664076226488ebe259a313725318cf4250b3e6a250aba5724f27cee24dc26812467ee6a236a98c52359c6d0
  | 6, 5 => 0x390153ab38c21c7b38a4a5e23885fcd2388012b1385204ef381cb67e37fdfb7837d4a1c237a858a736fb367836b06647369e286b3679dd0b3678c0eb366487033610a03935ebc24a35e23d5c35d89aaa35974020357321f83541768b34f524f934d2fbb734c8f0c7349824f43492603134886bc33473d1a6344f47aa343a84db34064f6c33df688433da662c33d93c6b3398d18533422da532fc41b832f11b9a32e16b893294f0e0326a54943247653131f5eab331763e4131381b073112a29330d5282030cca4c4309ade1b30959bfe306f6ccb304b37ce3006014230010ce22ff2eea02fbf35272f3c81e32f2d39052f1a95f82efbd9642ede35262ec68d27
  | 6, 6 => 0x45940ada456daacd4563ccbf4526b408450ea01a44d46f78446729e644578d0c4431695943df582343a97be94330d951432e5dba43110caa42e28e1442b779a34291ffc941de0f1c41b4d9a6418c58194183d88741662699414a8c1f4119dfa1411103a1410ee2ea40a8378340a60e37408f5a3040455b7a3fdedec33fca2bf63f384bf13f3624823f1e2b9c3f086e6d3ef9b7083e7b57fa3e38a55b3e277fff3d5d39623d1f3f593d0b3b903d03aadf3cedcf813ce437ac3cb938473cb227733c9ce34e3c644fe93c5112f13c38e0113b8aa58d3b34c0e23b33d6c03b28a8c83ae826bb3a67daad3a2d6c6239e16a4739b10345399a9e2c394f1420394ead04
  | 6, 7 => 0x507207e45069bcbd50695857504a74d85014114e500139404fe2b3e44fcc8ff24fc71f074fa753334f7735ef4f7141a24ea4fa1c4e92e7bf4e79b24a4df560734dd542384dd3ad484dc9c7c04db248164cf5a2254ce11a174c7627cf4c46545e4c1e35cd4c1326ad4ba260e84ba1260e4b6e21e64b226b904b21fba14b093b3e4aee73794ab8c3e84a8b09ee4a3f5f3c4a1660524a0a039049f952cf49eb066449e3bfbd49d9a14a49d72e8749b6983f48a811f8486ff37c4856c0ff47f0cb2247ee69e847a02cf14766fac8476409d74760868246df279b46d0e8cf46bddc5e469949b54649a34b4639627f4617f58845dd44e445b797dc459ecff7459774c2
  | 6, 8 => 0x5d8bf1475d5624535d384f2c5d1e66bc5d0eae245d00c56d5cde0cce5cb55e505cac1ec35bf13ab45be0d81b5bc0ce6c5bb03c075b8f00c25b5e87475b1f7a795b00c4075aecd9575aea31985abc6cf25aa8a6b95a9f5dfd5a8723c8596cee2e594a0591593aae7858cb5ee558bb531a58a9df505837177e581a3e365808a3535802414f57ce35d15794fb70576f03e756be0f99568ff7f1567eb156563580cb55f9c36e55e93b6a5571ce4a556f06955521817b55122fc95488605d5416d04b53e2c57853466db853447d0453346db9532df2e15318541d52bab12152b1ef95525316e951e93bed51ccc13e51bb2a0f514aca6d5137e9295124950150a1bacb
  | 6, 9 => 0x6e6ebd0c6dbbe1966d6074136d5b00e46cb3a7766bd6e2826bd3e8686bcf90f36bba04806b713d786b70d1e96b1be3666b09bc616afee7646afac8926a2177b569c0add469ac57256969e1b66909bb4667f4aa3e679fefcd67698764673f974f672edba166ea172966ac6aec663e596f661f8dfe660f2a8665e88a3d65b4b6696575faf26560b6cd64e6ab02648a2c2b646d8437640f62e363f84b3363df885162dfa08f62d4bd2362bf39f9629d9733622a4e0c61f5a73b61ca4008613f4bb66115d86e60f47f6c60c0e6cc602f2d626017f9735fbac6fd5fa9e2065ed6a3f15ec41cb35ec2fe405eb5ede35e22a7545e13ada65dbe740c5db7bfac5d9a53b0
  | 6, 10 => 0x80424c1a8040d078800c7ccf7fca014e7fac73bc7f8776eb7f37f75c7f081c437f01445f7e63c5ee7e4dc0ce7e4b58517e22428f7df7c5a07dd9697e7db1e1917cea112d7cb6ccc37c69c65e7bf841387bf0b2df7ba3c0797b25fb187b16ea687a8ef3507a7a23a87a260a2f7a05242f79c2eecc79bb6d1e797abaaa7961f727794fbed2792d2bd67915ad7b78d1319678bca81278325ccc7800865577d135d077cf9740778decba77728e4a7753784a76d6e32176a139dd764e5f6176076036757356b9756ef7e975447afa7508aada7448134173da4b1a736f42c1733927ec72b28339727718da726a4e01722b1a827166cf876f7090bd6f54c88d6ec7a362
  | 6, 11 => 0x8f1f96978ec635f58e323b688e0cfa578df2ab598d88441d8d5eaaf98d219bf58cb966468c3f36198c353f988b74ea068aee218b8ab84b5d8aafa50e8aaf8d4e8a4b2c568a0d8ef789efee9189acfcb188f300e188e4303688a82a54882be4e18826fc3987bd68e187b2ceb4877779c3876dd2498703169686bb6894868f8bfa863f7c59863f5b5b85f58910857f1b668518ff1e84203dbe8412a34783bec71383b00fae83a21eb1834e1a45834632f0833df90383328cfd82fc24ed82e0b6ab82c96d8a8220478281bd8a2f81b77d6f81ae339081a42827818f3264815fcf978123ee8881086da080e73cd1809fa26d80920950806d16b98069eaef806266ad
  | 6, 12 => 0xa4b188daa37956e6a352c6cfa33952fca2cd8bc3a2a97873a22b6a16a171e072a1536890a0c27a1ca0369f449f22e88e9ed6de7b9e0a09409df94a519db392919daae7359d58b7ee9cbb54e09c9c57949b4650979b3509fc9a95b69e9a21f39f99d3056b9997d904998cf53c997374ef9933b44398e9771598ddc02e9847a6bd97012b84968d4d5f9689804d9661aced961ed4639601231395ddc41b95bdb66e9515305d9512475994b8834e94aba5ca93cd8fe093c2bae393835e66937619ce93602c4692d649fa92beb26492002a6a91eb7da791c8a36f919ac8ae917fb21d917adf6f9102d26a90d48e7390b87dbd8fe7744e8fc42d338f74f0a98f6057d0
  | 6, 13 => 0xc2932210c278c27bbf98043bbf74ae55bf39cbf0bec2b53cbccd4b3fbc7e8f37ba437f4eb932cbabb7b92ec7b7a1fd24b702d21ab666254db5e82352b2dcefbab2ad74deb27deebbb2516d61b1b8a042b169cadfaf1123ebaf057aaeaef5af7aaed94acbae8f2a8cae1bf85dae18ff3dadeaf2e8adbf879fad58a5d0aca9b064ac8a86ebac41a9b3ac2d59fbabb3dcc5ab37265aaad76587aabfa2cbaa93f772aa67fba6aa30b727aa00aaa3a92ef1eea8e78fc4a8e4ad46a8c54723a8afe02ea8704a7fa85f673ea85da819a85b062fa851a7e3a79a2731a7470e27a71892dba6fdec6ba6a209e6a68098aea6563cc3a60a91baa56be49ba54a6a95a533b563
  | 6, 14 => 0xf0f8df95eff3c368efbd7900ee1e2c58ee02495becb47af8ec164c1eeafba6c3e636d437e4d154f8e2783331e1f91c91e1151f08dfeb09c7defe0162dc419738daa10b17da9fdba6d9bee8b0d91d26b3d7c43538d78a0a44d7894d3cd7482c02d66524e6d615987fd5ce88c2d5bfd6fdd5a0d46dd1efb8f3d1879d90d137f74ed1293c1cd0674649cfaaeb5dcef3ff30ced995d4ce0f4162ce08e40dcda438cecd73df73ccfb6ba3cc3d2a65cbd5b4f2cbb9f257cb980245cb2d7f47caefe3b0ca35eab9c90a98fcc8369917c7f451a9c7d3f23bc76b6ab0c7554d2ec7327c7fc5d6acb5c5899ec0c518bf53c4ed54adc3334588c32be95bc2d0e2fcc2afde01
  | 6, 15 => 0xfebe0ea5fb192d73f9cab482f8a016c6f13569a4f12be4b6
  | 7, 0 => 0x1317dd2b12b8ab4112ae5da31279802811ed84b711eb7ccf11d748061187183a1142fa411134c93410d1aa96103ead2a0fc22fb60f6b9a140f5c5cfb0edd17080ea68d810e8414b20dfb96ef0df078900db675560d9cbe430cf91d9f0cc7aa850cb3009d0c867e660c2cfbb60bd753a90bb2ffb10b989d440b41c7720acf09dd0ab7b9ae0a9628be0a2e18720a172c4908aedd460878675807d82e3c07bd347d07af559e076636a7075140fd06b07a0306634425065223ce05c61dd605ad2f34059e8b170590310f05169eb0040745c6036df1500291d00a024a740d023c952e01a603fb0188fb4b018309d901013f3600dd496a0064991500103def0008238d
  | 7, 1 => 0x26396ad4262d41fb2609324125bece64258a6ea424cb7b292485a934246554a62438a2592398f31022daf26b22d85c9a22543c1c21e9d24d21a5f9682179389d204aaf2d2046aaad203e530f203cd04e1fd3d3851f608b651f3d31db1ee4e3db1ebb13731e8eec381e739d441e7359ed1e08e1531d989e101d73f5661c53b96d1bea35011b78d4bc1b70b1901b52f3321b325a461a5d39541a45ab1d1a2bfa9c1a0ece701a0dc40d19f08aad19e3604919b1d4481979f417191531f41900f42918e3fb0a1881f686183e830517d07b0017a82026175a929b1729918f168a4efe15f86a801581f8c81561a43a1528ba3c1415063f13b5da6d136d10ac131bfefa
  | 7, 2 => 0x3b3c318a3b23954e3afd7b253a8b1a653a861c993a47663439de879e396f572d3950034038ad846e3899ed183724f45b36f4981f36c744ae36ad51603678c0eb366fa272363c57f436224d1b35d89aaa357bcd57355e29ce354bc4fd34746a9f34744a7f342cdee933193e9a3294bf403264f1943243d5cd3150ae14315024ba31381b073122199e30ccd1eb30bda81a2fa1c82a2efbd9642eedfa852ea0b9112d770a592d014b912cf3c0ef2cf085992cae27f22ca821632c9946a22ba0a43a2b0f56702af4104e2a7c852829f117742964176b291abe562882e2b2284f0649284db2db2775450f275958f22727707326bb2fef26aa53c3264ea12126488ebe
  | 7, 3 => 0x4f490be64e79bd534e1717654e00c0ea4dd111674d2b306b4d0476064cd8ba054ca60af44c5cc68f4c1e35cd4c173de94bb8974e4bb13b214b180f9b4b02825d4afc5e1e4aee73794ac0774d4a9f53ac4a59283649ccf756499b08ca49148db048f889f848b0ac9d46e1bded46e149a24696c81845f6b58445c07cca457c5ed145179a8f43b9f0a3433f660a4305883642b779a34223bdb941d622d341a4b5d6413f306a413ca69640d0012440bb2834405c8f3d40455b7a4025ca0a3f49363a3f086e6d3ee6de3d3e277fff3e1c8eb63df1aaf13dc32c533d8620523d6d0b963d18fbc93cedcf813c9f3cdf3c9dc2fe3c9d75a23c8fe41f3c39fd5e3bd0b783
  | 7, 4 => 0x6920920f67425c616709aa6167044c4c66fb4c91668c47706659a12a65b4b66964e30e6464789948633af011633635116329b2936284e0436129ea2960b58bf56001a2b65fbac6fd5ec6f1c75ec2fe405ebcebc25e90082e5e22a7545e06e6065dc82fa15d93d62e5cde0cce5c9fbd605bff541c5bdfea355ba915895b4388f85b0171135a17fce059f223e559e9c31b5923c1c658a5f1775837177e56dbe56f56da22f056abec62568ff7f15640306855ab6c46558b875054b47b98531692945314eaf652acbe7d528ca242520a3fab51efbb6051e81d5151d2062b51bb2a0f515c2919514f645451007c3a50c9577f50a706e84f9b055d4f943bc44f624ff4
  | 7, 5 => 0x876dd24987080352869b7594868cb4248635a6fc862851b985210b03850f030e84a3bdb483c5bc52838341f4833df903830766bf828511a482121d0d806266ad7fc0036d7f97da8d7e22428f7dd5c4a57db1e1917d33ff317d303bbe7cea112d7c0721267bc86ac17ae97d0f7ac854af7aa157477a85129f7a2bfc5d7a2bf4367a1482747952d274791d9b417900675a764e5f617521769374d2ee7873f60c3a73a4532b7333c42e72e03d9b72b283397290cad5727daf3d71fb25a2707cee8d6f3b46226eba99336e38e6f66d5cb0976d2657c06cd622c66bcf90f36b89f08a6b58c0516a5eea176a510b386a4fc62d6a2a46cf69f5d2f969d0a4b0692e70ee
  | 7, 6 => 0xb210ca3fb0ec7e1fb07bc511b02268afb00d02d1adab993dacac34b6aabfa2cbaaa935daaa38618da98c5b5da80d4bfda661d0dfa6563cc3a6395456a623790ea5e4c2a9a4dede88a499e38aa2d8fffaa1946574a141bf77a0c045e29eab30d29d42bc1d9bfcd7929b71391a9aec1f2b9a95b69e997d456498fcecee985a34f7984899db981b7e9297012b84963c456d95fe78aa95bdb66e95a996be94b8834e9497281e9409b1f09396353d93602c4692ef453392b08ece928cbda5926d751e908ca4449074f28c8fa4cc1f8f7fd14d8e7679718dbfa66d8c1a6ee88bedc1998b8fda438ab84b5d8a7994f88a0d10dd89f226db88f823fd87cdddd0877910e2
  | 7, 7 => 0xfce2758bf9acd0faf80ff336f646c3bff4e7fe6ef1c1f496f13569a4f0f10dbeea555bf2e9f23fa9e8b03ee3e45c7de4e1c2a466dfeb09c7de1b0bb2dbeeb34dd9ed2281d9e7a089d6890d25d5d13c99d4f736c8d229a3e5d0e5095fceeb1ad8ce8cc780cdd2d617cda803e7cd73df73cb26fa2bcae6d7d7c8df6e8fc7554d2ec62ad07cc61b5c10c5899ec0c4ac2c82c30bd3fac2afde01c278c27bc1c6e06ec1c16a74c16463c6c110cb7dc07ccfeebef5700abe2639d5be107ab6bddd5bacbb04b807ba477786ba2399e2b7a3f583b7610a65b6be7634b3feb3cab3f8265db23cd636b2306866
  | 8, 0 => 0xc2afde01b6be76348ab84b5d8a7994f82eedfa851e7359ed1729918f1561a43a1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x4708151480400470815148040000000520c5204000d821484300000c1514c03010011820480300000d82148430000181350853014708151480400470815148040076109314054027610931485402
  | 4, 0 => 0x194424c530200181350853010000052105203000c5504c43010000035081202000053540430200000000c81040018520081300000c1514c030100081514803000000052105203000c1514c030100041254403000000000100104000815148030000000000000040011820480300000855048430000041254403000000000000003000d8214843000000052105203000c5504c4301000000010510300000000000070000005484202000d821484300000d821484300001813508530100000000c5103470815148040000000520c5204
  | 4, 1 => 0x304812060000015500204000c1514c030100000314852050000000100103000c5504c4302000c1514c0302000003048120600041254403000018520081300000004504120000041354403020000000000000000815148030000000104852050011830405301000c5504c43020011430441301001093140530200000520c52040010931485302000c1514c0301000005110920200000520c5204000c1514c0302000003500520000000521052030011820480300000c1514c0301000000000000400081514803000008151480300
  | 4, 2 => 0x4125440300761093048140100000504c4202000412544030000000155002040000035085200000000000000100000000c01040008550484300000003044120100000000c51030000052105203000004548c20100000520c5204000c5504c430100000214052050000031485205000c1514c0302000001550020400000450812000004135440301000d82148430000000214052050000053109201000c1514c0302000003144120200059500c9302000005048c2020000000000004000000010510300041254403000004135440301
  | 4, 3 => 0x5354043020011820480300000000010810300000414412050010921405302000c5504c430200085504843000004135440301000d82148430000000000c51040000021405205000002148420000000304052017510920441401
  | 5, 0 => 0x45005200000002500520000000514c0201000000000000300000350412000000010440202000000000000300000350852000000053109202000000000510600000000c51040000000000000000000010510400000424812010000052101200000000010510300194424053010000000000000000c1514c0301000000010910200000000000020000000000007000c1514c0302000002048020000194424c130100000001081030000030481201000005048420000000000000010000000100103000000008510500000000c5105
  | 5, 1 => 0x510100000314052020000000000000000000010010400000000c51030000031405205000001044020000000001091050000031485205000004500520000000000c51040011820480300000000010910200000001051040008550484300000003508120200000000000070000000000001000000140420000000000000070000000000004000003508120200000450412000000000109105000000000510100000314052020000000000001000c1514c03020000042481201000004508120000000000051010000001404200
  | 5, 2 => 0x10910100000000000070010931485302000003508120200000424812010000000000002000002048020000000504c420000000000c5103000000010510300000500c92020000000000000000004504120100000450c1201000000004110200000104402010000045005201000000000000200000050c9202000000010d105000000000000300000000000000000000000001000003504120000000000c5104000002504120000000000c510400000504842000004125440300000002140520200000204802000000000105103
  | 5, 3 => 0x504c42020000042481201000000010910600000204802000000000085101000005148020000000314c420100000304c02010000000000000000000000000300000001091020000045041201000000000000700000204802000000000000005000000010910600000000c5103000c1514c03010000000000004000000000000000000521052030000000000000000000008110600000000c510500000104402000000000041102000001044020100000000000060000000109102000000008c10200000000c51030000000000002
  | 5, 4 => 0x1000005048c2020000000000000000000000000700000000000000008550484300000c1514c03010000000105103000000000000500000314c4202000004508120000000514c02010000000081106000003044120100000314852050000535404302000000010d1050008550484300000052540430000000000c510400000000000000000020480200000002148420000000204802000000000000006000005308120200000504c4202000005210520300000000000000000050484200000c1514c03010000000000003
  | 5, 5 => 0x10510300000000c810400000001081030000000000000000000000000300000314c420100000000000070000035041200000000000000700000000c010400000000000010000000109105000c5504c430100000001051030008151480300000002148420000000000000020000025440200000000000000700000000411020000000000002000000000000000000000c010300000000c510400000000000070000020480200000001044020100000000000020000000000007000000000510100000254402000000000000003
  | 5, 6 => 0xc5104000000000000500000450812000000045005201000001044020000000350052000000020480200000002504120000000000c51040000042485202000000000000300000000000010000000000000000002048020000000001051040000000000003000000000000200000304c020100000000c5104000000000000300000350852000000000000005000004500520200000304c02020000000000005000003540420200000000c5105000000000000000000000c4100000000000000000000014042000000035508200
  | 5, 7 => 0xc1514c030100081514803000000035006202000413544030100000424c52020000000000002000000000000300000000c510400000204802000000000000004000005148020000000000000030000010440200000005010920000000130c5201000000000000000000000000000000042405201000005148020000000000000040000051480200000000000000700000000c810400000254c4200000000010510300000504c4202000000008510100000350852000000000000004000000000000000000000000040000000105104
  | 5, 8 => 0x811060000000000007000413544030100000000c510400000000000030000045081200000000000000200000000c510400000450812000000000000001000001044020000000000c510300000000c510400000514c020100000001051030000025440200000000000000400000504c4200000000010010300041254403000000000000007000000004110500000000c510400000514c0201000000000000100000000000010000021405205000000010010400000000000050000020081200000005148020000000450c1201
  | 5, 9 => 0x454c420000000000c5104000000140420000000450812000000535404302000000000000000000000000040000000041105000000008110600000304c020200109204413010000035440201000003144120200000000c510400000104402010000042485202000000010d1060000000000005000002540420000000000c51030000000109105000004144120500000001051030000045005200000005110920200000504c420200000000c01030000000105104000000010d105000002148420000000350412000000021405205
  | 5, 10 => 0x140420200000000c510500041254403000000000085105000000548420000000314c420100000000000030000053109201000005048420000000000000000008151480300000002008120000000000411050000000000003000005210d2000000000105104000000000000400000000c5104000c1514c0302000004500520200000514c02010000000105103000002008120000000001091050000535404302000000008110200000304c02020000030441201000000010010300000504c420100000000000000000000000001
  | 5, 11 => 0xc51040000025041200000004248120100000520c520000000000000020000051480200000002544020000000000c5104000003508520000000000000030000000109105000000010d1050000000000000000000010510300000000c11010000045041202000000000000300000500c9202000c5504c4301000000000000200000000c110100000001091010000000000005000000000000200000350852000000000000000000003508520000000450052000000021484200000000008410200000254c420000000304c0201
  | 5, 12 => 0x70000000105105000412544030000081514803000000010440200000002504120000000000411020000000000003000000010910200000520c52000000000000002000000000000600000000000000000021484200000000008510500000000000010000000100104000000000000700000000c110100000000c5104000000000000500000304c0202000002504120000000001051030000000000003000003504120000000000c5104000002500520000000000c51050018535081302000000000000500000514c0202
  | 5, 13 => 0x5210d200000c1514c030200000000411020000000000006
  | 6, 0 => 0x4110100000001051030000000000006000004500520000000304c02010000000000007000000010510300000000c5100000000010910500000000000070000000000002000000010910500000000c510300000000851010000000101100000000000210100000000000020000000085100000000000000400000504c420200000000c110200000000000060000000085100000003508120200000000c91010000000000002000000000000000000001091010000000081100000000004010000000501092020000000000001
  | 6, 1 => 0x1051050000000105103000000010510200000000000030000000000000000000010510400000000c110600000001051020000000000004000000000000600000000c510300000000000040000000000003000000000e10200000000000020000042481201000000000000000000001081000000000000007000000000000600000000851000000000000000000000000000600000000000030000000005102000000010510000000001091020000000000006000000000000500000000c5103000000000a100000000000a100
  | 6, 2 => 0x400000000c51000000000109105000000000610200000000c1102000000000000300000000000000000000000002000000010910200000000000050000000000000000000000000000000000000030000000000004000000010d102000000010510300000000051000000000085101000000008c1020000000005101000000000e1020000000081102000000000000400000001011010000000000002000000000000700000000c510100000001051000000000000000000004248520200000000000020000000109101
  | 6, 3 => 0x60000000105101000000000000200000000851010000000081100000000000a10000000000c510500000000000000000000085100000000000000000000254402000000000000000000000000000500000000000060000000000002000000000000300000000c5103000000000e1000000000000004000000000210000000000000000000000000004000000000c101000000000610000000000000010000042441202000000004c10100000000c510400000000051020000000000001000000000000400000000c1106
  | 6, 4 => 0x200000000061000000000000004000000010d100000000000000200000001051040000000000005000000000a1020000042481201000000008110000000000c9100000000000000300000000000030000000005101000000000a1020000000000007000000000000700000304c020200000000121000000000000003000000008510000000450c52020000000000003000000000000400000001091010000000000003000000008410000000000000060000000002100000000000410000000254402000000000041101
  | 6, 5 => 0x30000000000005000000000000600000000c910000000000000050000000000004000000000000000000001051030000000081102000000000410000000314c420200000001051030000000000001000000001210200000000021000000000000004000000000e100000000000a100000000000210200000000801000000000012102000000000210000000000411000000000005100000000000000400000000000030000021484200000000000a100000000000000500000000c910200000000c810000000000c8100
  | 6, 6 => 0x300000514c020200000000000070000000000000000003140520200000000000010000000000004000000008110200000000811020000000000000000000000610000000000411050000000000003000000000a10100000000c510200000304c02020000000000000000000000000600000000c91000000000000003000000004c1010000000000003000000000a10100000000c110200000000000010000000000003000000000000500000514c02010000000081100000004500520100000000c11020000000000000
  | 6, 7 => 0x8010000000000000040000000006100000000000000000000504c42010000000000003000000000a101000000010510300000424852020000000081106000000000000300000000c91020000000006102000000000000000000000c11010000000000003000000010810000000000000030000000041100000000000000600000000000020000000000006000000008510200000000000040000000000000000003500220100000000c51010000000080100000000000510600000000c5102000000000000100000450c1201
  | 6, 8 => 0x6000001044020000000000811000000000002100000000000000100000000000020000000084100000000000000300000214842000000000002100000000000000600000504c420100000000000050000000006102000000010010000000000841000000000006100000000000000000000000061020000000000003000000008510500000000c11010000000000004000000000210200000000851000000000000000000000000000600000000000010000051480200000000010910200000000c51040000000084100
  | 6, 9 => 0x10000000005101000000008110100000000000060000000041100000000000210000000000c510200000000c0101000000010c101000000008110200000000000060000010440200000000000e102000000010910100000000c910200000000000000000000109105000000008510100000000000050000035440201000000010d1020000000000003000000004110100000000000060000000000003000000000000200000000000030000025041200000000000e1000000000000001000000000a1000000000000005
  | 6, 10 => 0x41100000000004010000000304c02010000000084100000000008510200000000000050000000000001000000000510000000000061000000000006102000000000000600000520c520000000000000040000021405202000000010910000000000000010000001404202000000000a100000005048420000000000c510300000314c420100000314052020000000000001000000000000100000000c51040000000000001000000000000300000000021000000000004100000000008410000000000c01040000000081100
  | 6, 11 => 0x2000000008510500000000c910200000000851000000000109101000000010910500000000c51050000000080100000000000000100000000000030000025440200000005110920200000000851020000000000003000000000000200000104402010000000105103000000010510300000001091050000000000002000000000210000000000c51020000000000003000000000610100000000c5102000000000000000000000c9101000000000000500000000000050000000109105000000000000300000000c5105
  | 6, 12 => 0xc01010000000000006000000000e101000000000000300000000000030000000000000000000000000600000001091000000000000004000000000a1000000000109101000000008c10100000000c1101000000008110200000000000060000000109101000000010910100000000c510100000001051040000000000002000000000210100000000000030000000040101000000010010000000000c9101000000000000700000304c02010000000000001000000000000000000000000010000000000002000000000e100
  | 6, 13 => 0x200000000000030000000000004000000000000200000000000020000000101100000000004110000000000000060000000109106000000008510100000424c52020000000000005000000000000600000304c0201000000000000400000000000000000000006100000000008510500000000000060000000101102000000004010100000000c110200000000000030000000000002000000008510100000514c02020000000000001000000000000600000000c5103000000010510000000000000040000051480200
  | 6, 14 => 0x1011000000045081200000000008110200000000c51000000000012100000000000000300000000c5103000000008410000000000000050000000000004000000000c1020000021484200000000010010000000000000000000000000000000000000a10000000000000030000000000006000000000000000000000851010000000000003000000140420200000001081030000000041100000000000e1010000000000000000000010510400000000c41020000000005101000000010910100000000000030000000000004
  | 6, 15 => 0x10910200000000c5103000000010910100000000000070000000041105000000000000300000000061000000000109102000000000000300000000851050000000109102000000000000400000000051020000000109101000000000000700000000851000000021484200000000000e10200000014042020000000000004000000010910200000000000050000045005201000000000000500000000000000000000000000000000001210000000001051000000000000002000000000510200000214842000000000000003
  | 6, 16 => 0xc5105000000010510300000000061010000000000002000000000510200000001011010000053109201000000000510200000000000000000000000001000000000a100000000000000000000000000050000000000002000000008410000000000c0102000000000000000000000061020000000041101000000000210000000354042020000000000000000005210d200000000010910500000000000000000025404200000000000000400000001051000000000081100000000000000700000000000070000000000004
  | 6, 17 => 0x40000000000002000000010910500000000411010000000109102000005048420000000000000000000000000001000000000e101000000000000300000000000040000000000007000000008110000000000000060000000105103000000000510000000000811010000000000001000000000a100000000000a100000000000000300000000000030000000000002000000000000100000001011020000000000006000000010510300000000000010000000101102000000000e1000000000000001000000010d100
  | 6, 18 => 0x10000000000001000000000000200000001091010000000004100000001044020000000424852020000000000005000000000000300000000c110100000001091050000000085100000000010910100000000000010000000081100000000000000000000000000050000000105100000000000000100000000061000000000109101000000000e10000000000000070000000109100000000010910500000000000010000000000005000000010d1000000000000000000000000000600000000000000000000000002
  | 6, 19 => 0xc51040000050484200000000000e1020000000002100000000000000600000000c010000000000411020000000000001000000001210100000000801000000000000003000000000000300000000c81000000000105104000000000000200000000000030000000000000000000000000400000001091060000000000004000000008010000000314852020000000081100000000010d101000000001210100000001091020000000080100000000000000500000000000010000000002100000000000000300000000c1101
  | 6, 20 => 0x105103000000000000100000000c0101000000000000300000000051000000000000007000000008510000000000811000000000000002000005148020000000000c5100000000000000300000000121020000000000002000000000000000000000121000000000105105000000000000400000000c51010000000000003000000000000000000000000040000051480200000000000000600000000051020000000000003000000010510000000000811000000000000005000000000000000000000000020000020480200
  | 6, 21 => 0x70000000000004000000000000600000000811060000000006100000000000000700000000c1102000000004110200000000021000000000000007000000000000700000000811010000000000004000000000000100000000c5102000000000e1020000000040100000000000000500000104402000000000002100000000000000200000000000030000000000000000000000000000000000000020000000000000000000001210000000000000030000000000004000000000000300000000051020000000000003
  | 6, 22 => 0x3000000010d105000000010910500000000000040000000000003000000000a100000000008510500000001051030000000105103000000000000000000000c8100000000010c1010000000000003000000010d1040000000109106000000000000000000000000030000000109101000000000e10200000001091010000000000000000000010910500000000c510300000514c0202000003544020100000000c1101000000000000100000514c020100000000c510300000000c5103000000000e1000000000000004
  | 6, 23 => 0x30000000000001000000000000200000000021020000000041100000000000000000000000061010000000000005000000008110600000000000070000000109102000003544020200000000000010000000000001000000000e10100000000c510400000000c910000000000c11020000000000004000002544020000000000061000000000041105000000000e102000000000000200000001051020000000104100000000000210100000000061020000000000000000000000000700000000000000000000000005
  | 6, 24 => 0x4000000000e10100000000851020000000002100000000008110000000000000030000000005101000000000510100000001051040000000000003000000000a10200000000c810000000000c510400000000c510400000000851050000000000000000000010d1020000035440201000000000210000000514c02010000000000004000000000000300000001081000000000000002000000000a100000000000000000000000801000000000000007000000000000400000000801000000000000005
  | 6, 25 => 0x8110200000001091010000000109102000003540420200000000051000000010440201000000000000300000001051030000000084100000000000e101000000000000400000304c02020000000000004000000000210000000000c51010000000000003000000000000500000000c51010000000000000000000000000500000001091050000053109201000000000e1000000000000001000000010510500000000c11020000000000002000000000610100000314c4202000000000000000000001091050000000041105
  | 6, 26 => 0x2000000000000100000001051040000000104100000000008110000000000c5104000000010d101000000010d102000000000000500000000c9100000000000000600000000000000000000005100000000000000600000000c5101000000004110100000000c1101000000000000100000000851010000000000003000000000000300000000c5102000000000000700000001051040000020480200000000000000100000000811000000000000000000000000000000000000c9100000000010c1010000000085100
  | 6, 27 => 0x60000000000004000000010110100000000000010000000000003000000000510100000000000010000000100104000000004c1020000000000003000000000000400000000000000000000000003000000000000400000000c5102000000000000300000001051030000000084100000000008510000000514c020100000504c42020000000000002000000010910500000000041000000000000005000000000000700000000c910200000000021020000000000000000000010510000000000000040000000000003
  | 6, 28 => 0x10000042485202000000000a100000000000000300000000000000000000109105000000000210000000001051030000000000001000000000a1000000000000001000000000a100000000010110000000000c010200000001051040000000105101000000000000000000000c1100000000000a10000000001051030000000000001000000000000500000000c510000000000000050000000002102000000000000300000001051040000000005106000000000000000000314c420100000000851000000000000000
  | 6, 29 => 0x600000000000070000000000005000000000000700000000000030000000000002000000000a1000000000041100000000000510000000000000000000000000007000000000000600000000021000000000000000000000000000500000000851050000010440200000000000e1010000000012101000000000000300000000000070000000105103000000010d105000000000000700000001051030000000000003000000000000300000000000030000000000006000000000a100000000000a1010000000000005
  | 6, 30 => 0x30000000041100000000004110100000000000030000000000005
  | 7, 0 => 0xc4101000000000000200000001091010000000000006000000000000000000000411020000000000006000000000000400000000061020000000000000000000000000100000000411000000000000001000000000000400000000000040000000012101000000008110100000000000010000000000000000000000000500000000c410200000000411000000000000007000000000e10200000000841000000000000002000000000000400000000000010000000000001000000000000000000000000010000000000005
  | 7, 1 => 0x30000000000002000000000000000000000c910200000000000060000000081101000000000210000000000000030000000000000000000000000000000001091000000000000001000000004110100000000000050000000101102000000010d101000000000000100000000000000000000000005000000000000200000000000070000000000000000000008010000000000000040000000109100000000000610200000000c910000000001091010000000000001000000000000000000000061000000000000003
  | 7, 2 => 0x40000000085102000000000210100000000c4102000000000000100000000c5102000000000000000000001011020000000000005000000000e101000000010d101000000000a1000000000101100000000000410200000000851000000000000002000000000000500000000811010000000004100000000000000500000000000040000000000002000000000000600000000000010000000000006000000000000000000000000060000000000003000000000000300000000000010000000002102
  | 7, 3 => 0xa100000000000000200000000000040000000000004000000000610100000001051020000000000006000000010510000000000000010000000000002000000000e1010000000000004000000000000000000000c110000000000021010000000000006000000000000400000001051000000000000001000000000510200000000000010000000000002000000000000000000000c51000000000000002000000000e102000000010910200000000000010000000000005000000010110000000000000010000000000000
  | 7, 4 => 0x60000000000003000000010d100000000000000600000000000030000000000004000000000000200000000061010000000105101000000000000100000000000010000000000002000000010d100000000000000600000000c0102000000008510000000000000060000000000005000000000000400000000000010000000000000000000000000400000000c0101000000010910200000000061010000000000000000000000000400000000051020000000000003000000010110100000000000000000000000004
  | 7, 5 => 0x1000000000000400000000c91000000000000000000000001210100000000121000000000000001000000000000500000000000030000000000000000000000a10100000000000020000000000005000000000000000000000000040000000000002000000000000000000000c11020000000000003000000000000200000000000010000000000005000000000000300000000811000000000080100000000001210200000000000020000000000002000000000e10000000000000050000000000000000000000a102
  | 7, 6 => 0x1000000000000100000000000010000000006100000000000000000000000c4101000000000210000000000000000000000000005000000000000000000000000050000000105102000000000610200000000000060000000000006000000000000300000000000030000000006100000000000000200000001011020000000000002000000000000000000000c11010000000041100000000000000100000000000050000000000001000000000000400000000000000000000105102000000008510100000000c4101
  | 7, 7 => 0x60000000000003000000000000400000000c11020000000000000000000000000200000000c41020000000000000000000008510000000001091020000000000000000000000610100000000c9100000000008010000000000000000000000012100000000010d101000000000000200000000c91020000000000000000000000000200000000000000000000002100000000000a10200000000000000000000000003000000000000200000000000050000000109101000000000e10100000000000030000000002100
  | 7, 8 => 0x8510100000000000000000000000002000000000000300000000000040000000040101000000000000500000000000040000000000001000000000000600000000000050000000002100000000000000400000000c1102000000000000300000000041020000000000004000000000210100000000c510200000000c91010000000000000000000000a100000000000000100000000000020000000040102000000010d1010000000000007000000000000500000000c0102000000000210100000000401000000000080100
  | 7, 9 => 0x410200000000000010000000000001000000000000600000000021000000000012101000000000000200000000c11010000000105101000000000000000000000061000000000000003000000010910100000000c9102000000000210200000000000050000000000002000000000000100000000000060000000000001000000000000000000001051010000000000001000000000e101000000000a1000000000000000000000000000000000000000040000000000004000000000000200000000000000000000000005
  | 7, 10 => 0x60000000000006000000008110100000000000000000000000000000000000000000000000000010000000006100000000000000200000000c91000000000000006000000000000600000000000000000000012100000000000000500000000c110000000000000060000000000004000000000000300000000000010000000000002000000000a10000000000000010000000000004000000010d102000000000000400000000c5102000000000a1000000000000002000000000000400000000000000000000000004
  | 7, 11 => 0x210200000000000020000000000000000000010d101000000000000300000000000000000000109102000000000210100000000061010000000000003000000008010000000000021010000000000001000000000000400000000000030000000000002000000000000400000000c1101000000000000600000000811020000000006101000000000000300000000411010000000005100000000000000600000001091020000000000004000000000000200000000000060000000000000
  | 7, 12 => 0x200000000c510000000000000000000000000002000000000a100000000000510100000000c1100000000000000300000000000060000000000006000000000610200000000000000000000101101000000010110000000001091020000000085101000000010d1000000000000000000000000000600000000061010000000002100000000000000600000000851010000000000004000000000000400000000000010000000000000000000000e1010000000000005000000000000300000000c51000000000084100
  | 7, 13 => 0x1000000000a100000000000000000000000000020000000000002000000000e101000000000e10100000000000050000000002102000000010510000000000811000000000041101000000000e10200000000000000000000000000000000000000100000000d1100000000000a101000000000a1000000000000006000000000000000000000811020000000000007000000004010000000000121000000000000003000000000610000000000061000000000109101000000010510000000000000050000000000001
  | 7, 14 => 0x5000000000000100000000c4102000000010110000000000000020000000000005000000000000500000000c51010000000000003000000000410000000000000020000000000000000000000000400000000c910000000000000010000000000006000000001210000000000000000000000101101000000000e102000000000000000000000000030000000000000000000008110000000000c91020000000006102000000000000100000000000010000000041100000000000000100000000000050000000000000
  | 7, 15 => 0x401000000000000000000000000000300000000000000000000000000000000000e1010000000000003000000004010100000000c91010000000000001000000000a100000000000000000000000811000000000000000000000010d10000000000c0102000000000000000000000c1102000000000000700000000c110100000000000050000000000001000000000a101000000000000300000000000050000000000004
  | 8, 0 => 0x10000000000001000000000000000000000000020000000000001000000000000200000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 7 s ws hint
  | 1 => checkCutEntry dom_6 roots_6 7 s ws hint
  | 2 => checkCutEntry dom_7 roots_7 7 s ws hint
  | 3 => checkCutEntry dom_8 roots_8 6 s ws hint
  | 4 => checkCutEntry dom_9 roots_9 6 s ws hint
  | 5 => checkCutEntry dom_12 roots_12 6 s ws hint
  | 6 => checkCutEntry dom_13 roots_13 6 s ws hint
  | 7 => checkCutEntry dom_14 roots_14 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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
theorem z2_0 : ∀ i, 0 ≤ i → i < 4 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 4 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 4 → Z 2 i = true := z2_0
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
theorem z4_72 : ∀ i, 72 ≤ i → i < 77 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 72 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 77 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (range_split z4_48 (range_split z4_56 (range_split z4_64 (z4_72)))))))))
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
theorem z5 : ∀ i, 0 ≤ i → i < 208 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (z5_200)))))))))))))))))))))))))
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
theorem z6_352 : ∀ i, 352 ≤ i → i < 357 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 352 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 357 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (z6_352))))))))))))))))))))))))))))))))))))))))))))
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
theorem z7_232 : ∀ i, 232 ≤ i → i < 233 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 232 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 233 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (range_split z7_208 (range_split z7_216 (range_split z7_224 (z7_232)))))))))))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 19 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 16 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 19 → Z 8 i = true := range_split z8_0 (range_split z8_8 (z8_16))
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

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276941024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_15.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_15 10 hT6 (by unfold IsConst; decide) low_15

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [10, 2]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [8, 12]⟩, ⟨GateOp.and, [11, 9]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_13145_aux

theorem PEqualNP.Outside.L_meta_13145 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276941024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276941024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_13145_aux.wit, PEqualNP.Outside.L_meta_13145_aux.wmono, le_trans PEqualNP.Outside.L_meta_13145_aux.wsize (PEqualNP.Outside.L_meta_13145_aux.lower s hs), PEqualNP.Outside.L_meta_13145_aux.weval⟩
