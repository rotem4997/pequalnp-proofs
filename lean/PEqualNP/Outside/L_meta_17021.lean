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

namespace PEqualNP.Outside.L_meta_17021_aux

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

def dom_1 : Nat := 0x444400004444
def goal_1 : Nat := 0x444000004000
def roots_1 : List Nat := [0x404000004040, 0x440000004400, 0x444400000000]

namespace S_1
def pairsG : List (Nat × Nat) := [(6, 14), (6, 38), (10, 14), (10, 42), (34, 38), (34, 42)]
def r1sG : List Nat := [6, 6, 10, 10, 34, 34]
def r2sG : List Nat := [14, 38, 14, 42, 38, 42]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x5374d41f
  | 3, 0 => 0x5374d41f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x44440000000000004400000044000000404000004040
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

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
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

def dom_2 : Nat := 0xcccc0000cccc
def goal_2 : Nat := 0xccc80000c080
def roots_2 : List Nat := [0x888800008888, 0xc0c00000c0c0, 0xcc000000cc00, 0xcccc00000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x888800008888, 6, 7)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xcc000000cc
def goal_3 : Nat := 0xc800000080
def roots_3 : List Nat := [0x8800000088, 0xc0000000c0, 0xcc00000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 4 :=
  lower_iso [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_4 : Nat := 0xff000000ff
def goal_4 : Nat := 0xea000000a0
def roots_4 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc000000cc, 36, 38)] (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0x555500000000
def goal_5 : Nat := 0x544000000000
def roots_5 : List Nat := [0x444400000000, 0x505000000000, 0x550000000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 4 :=
  lower_iso [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_6 : Nat := 0xffff00000000
def goal_6 : Nat := 0xfeea00000000
def roots_6 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_5

def dom_7 : Nat := 0x555500005555
def goal_7 : Nat := 0x544000005000
def roots_7 : List Nat := [0x444400004444, 0x505000005050, 0x550000005500, 0x555500000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x444400004444, 36, 38)] (by decide +kernel) (by decide +kernel) low_1

def dom_8 : Nat := 0xffff0000ffff
def goal_8 : Nat := 0xfeea0000f0a0
def roots_8 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

namespace S_8
def pairsG : List (Nat × Nat) := [(1, 5), (1, 33), (3, 7), (3, 35), (4, 5), (4, 12), (6, 7), (6, 14), (6, 38), (8, 12), (9, 13), (9, 41), (10, 14), (10, 42), (11, 15), (11, 43), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [1, 1, 3, 3, 4, 4, 6, 6, 6, 8, 9, 9, 10, 10, 11, 11, 32, 34, 34, 34, 36, 36, 36, 40, 40, 40]
def r2sG : List Nat := [5, 33, 7, 35, 5, 12, 7, 14, 38, 12, 13, 41, 14, 42, 15, 43, 33, 35, 38, 42, 37, 38, 44, 41, 42, 44]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_8.map (· &&& dom_8)
def goalM : Nat := goal_8 &&& dom_8
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xb7253fbd5ba073fa
  | 6, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000ff000000ff000000f0f00000f0f00000cccc0000cccc0000aaaa0000aaaa00000f0f00000f0f
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xb1a21858885
  | 6, 0, 0 => 0x58d15
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffc000380fe001c007c00ef1cc003303f8ffe0f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xffea42bc8fea09d15fd52ef1cc24f317d8ba80a
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 6 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
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
  | 4 => 1
  | 5 => 32
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xf1fce07
  | 5, 0 => 0xf641318cf11b066ee9082d54e505bdfad3f11db1af535e0ea7da18faa1c0b4b8a1712e8ba12a17a39f39fa52985bc5f095fc1c0b92b6c7608c5e12728888432e7ea52a9a7445a6b572657d5c6b7180a36949f7d6686e9bda6594bfe25cdf53735b61388b55c13d204d7877b92fef2b28270b03de160058940f1fce070da784ce
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x400001000000000000000000000100000c0000200000c000000000000000200000000002000008000000000080000100000000000000004000010000000000300000c0000000000c000020000080000100000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 1 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 2 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 3 => checkCutEntry dom_7 roots_7 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_8 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_8 == dom_8) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_8 goalM u ys) : RunD dom_8 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_8 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_8 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_8 roots_8 goal_8 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_8 goal_8 := by
    have h0 : isConstB dom_8 goal_8 = false := by decide +kernel
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

end S_8

theorem low_8 : Lower dom_8 roots_8 goal_8 7 := S_8.noCircuit

def dom_9 : Nat := 0x4444444444444444
def goal_9 : Nat := 0x4444444044444000
def roots_9 : List Nat := [0x4040404040404040, 0x4400440044004400, 0x4444000044440000, 0x4444444400000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 5 :=
  lower_iso [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_10 : Nat := 0x5555555555555555
def goal_10 : Nat := 0x5444544054445000
def roots_10 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x4444444444444444, 16, 18)] (by decide +kernel) (by decide +kernel) low_9

def dom_11 : Nat := 0x5555555500000000
def goal_11 : Nat := 0x5444544000000000
def roots_11 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 34, 50)] (by decide +kernel) (by decide +kernel) low_5

def dom_12 : Nat := 0xffffffff00000000
def goal_12 : Nat := 0xfeeefeea00000000
def roots_12 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0x33333333
def goal_13 : Nat := 0x32203020
def roots_13 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

theorem low_13 : Lower dom_13 roots_13 goal_13 5 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_14 : Nat := 0xffffffff
def goal_14 : Nat := 0xfeecf0a0
def roots_14 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_14 : Lower dom_14 roots_14 goal_14 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccccccc, 16, 18)] (by decide +kernel) (by decide +kernel) low_13

def dom_15 : Nat := 0xffff0000ffff0000
def goal_15 : Nat := 0xfeee0000feec0000
def roots_15 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_16 : Nat := 0xff00ff00ff00ff
def goal_16 : Nat := 0xee00ea00ec00a0
def roots_16 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 6 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14

def dom_17 : Nat := 0xcccccccccccccccc
def goal_17 : Nat := 0xccccccc8ccccc080
def roots_17 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888888888888888, 6, 7)] (by decide +kernel) (by decide +kernel) low_9

def dom_18 : Nat := 0x3333000033330000
def goal_18 : Nat := 0x3222000032200000
def roots_18 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_19 : Nat := 0x3333333333333333
def goal_19 : Nat := 0x3222322232203020
def roots_19 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000033330000, 9, 25)] (by decide +kernel) (by decide +kernel) low_18

def dom_20 : Nat := 0xffff0000
def goal_20 : Nat := 0xfeec0000
def roots_20 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]

theorem low_20 : Lower dom_20 roots_20 goal_20 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_21 : Nat := 0xcc00cc00cc00cc
def goal_21 : Nat := 0xcc00c800cc0080
def roots_21 : List Nat := [0x88008800880088, 0xc000c000c000c0, 0xcc000000cc0000, 0xcc00cc00000000]

theorem low_21 : Lower dom_21 roots_21 goal_21 5 :=
  lower_iso [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20

def dom_22 : Nat := 0xffffffffffffffff
def goal_22 : Nat := 0xfeeefeeafeecf0a0
def roots_22 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_22
def pairsG : List (Nat × Nat) := [(1, 5), (1, 33), (2, 18), (3, 7), (3, 19), (3, 35), (4, 5), (4, 12), (6, 7), (6, 14), (6, 22), (6, 38), (8, 12), (9, 13), (9, 25), (9, 41), (10, 14), (10, 26), (10, 42), (11, 15), (11, 27), (11, 43), (16, 18), (17, 19), (17, 21), (17, 25), (17, 49), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (36, 44), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 3, 4, 4, 6, 6, 6, 6, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 16, 17, 17, 17, 17, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 34, 36, 36, 36, 40, 40, 40, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 33, 18, 7, 19, 35, 5, 12, 7, 14, 22, 38, 12, 13, 25, 41, 14, 26, 42, 15, 27, 43, 18, 19, 21, 25, 49, 21, 22, 28, 25, 26, 28, 33, 35, 38, 42, 50, 37, 38, 44, 41, 42, 44, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xfffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_22.map (· &&& dom_22)
def goalM : Nat := goal_22 &&& dom_22
def NN : Nat → Nat
  | 4 => 2
  | 5 => 21
  | 6 => 129
  | 7 => 159
  | 8 => 32
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xfb0f0c8ac16a6564
  | 5, 0 => 0xf83636d4f77d1f7fee9b9288d86a591ad1028962cf88cc23c001d22fbd3c3d3faee7fad1aad0cdb6a246ef0c88e2e4b67b947b804c87203c3193f73a2a66ef681a09d187182539bf0ef08abd0e3ec02407a01e5f
  | 6, 0 => 0x94aba5ca8dc4f0798cc6a3578a1fecb88786f1f785215bbd81bd8a2f7f0d3e2d7f0507a47ea020fc7b83ced07a399f0c77e0dac7751532dd74cf39e473fa28f2710cff026df7e42c6af8974967fbf59e616de8555c929b395c1f443a5ae1ffbf5925466956488c3a4dd3ad484d84259f4ca859dc4c2eb57845a7f598447f91b143c469ce412c1b383fb8a6af3e49633b3d2c7c353a4fc20638a4a5e2372fb32930e1709b2f653d432ed0d2042c42325c29e188d329af2b6426e23bf022c7351321ce3725213dff81204b60b61ebcbc8f1eaa0f9b1c96ea4919ba301a176d640f13967e2f0bc7415d0a61d8b609bd51ef091999780715437d057729b6011daf4c
  | 6, 1 => 0xfba24b56f7db9c7ff140df91ef885172ebefca4beb121e74ea99b7d8e8ba254ae88e9a99e8027d18e2433ca3dfe44f4adecd4938ddf2abbadb8e5997db4f33a9daa66136d97fc822d872797ad85d0165d7f9e631d79dcf25d72da707d6fb2899d1296545ce12c0f5cb5a385fcb40e25eca7e11e2c7df5fbac237d00fc21e0704c20f81e7bf0a554ebeb13acfbd667629bab9a1bdb7dce78eb795a117b2bdb791b22053d7b2118fd6b1d08fcbaf616e2baf13a005ae861a49ae1bf85dac06f897a956412ea7853e24a61bfe94a5cf7206a5268c5fa088b5779ec0d7899e91ae509db654639c0b11509be41d5a9b5b3fbe9a0d459595c7f3849551aacc94c167a6
  | 6, 2 => 0xfc78f6f8
  | 7, 0 => 0x6afac8926a7ff668651506a464e6ab0264cf00c56284e04361ca40085c0095e65af03eb05aa8a6b959d395c7584e132a558b875054ed1c7554c1de10530ec13f514aca6d4e2ce2974c4c79c44b6e21e64ac0774d4a3f78dc4a0d197449226c8f49148db0425327d74214fad141d9fb783c21f90f3a305add359f67e7358e7c1332ba82ac315024ba3129ad3f302ca7772f1362052de85b922d90db782b81626d28a4a83e2705880d261c309d24296515233e519822c735132219ec0a20292edb1fb72b911e3d0e22153eaa18119811440f8898390e7e15130d61f2fb0cabde0a0c22507d0c167f1006ecbabd06291d8305869eb103f1b952023c952e00f5a3d2
  | 7, 1 => 0xcea2794ccd5fbf4fc5d3e588c5690328bf01fb40be4be64fbe2639d5bc18011abbb69bf5ba2399e2b702d21ab59a84ddb4e46fecb080f6ebaf1123ebac8a86ebab681b8eaaa935daaa87c3f1a98e4816a7f773d9a661d0dfa4e3c223a3f2435da141bf779db654639d3508f498411d8197a9fca097251c989710a45896e3fc35956125c6944ede009351acbb91b98d12917fb21d9117715e8f6e24048d5eaaf98b3e939c8a81f0ca869b75948276397281bd8a2f7fe35f827ecd8d627e8559377db173387d33ff317bf0d3337b2b17a17a85129f79e15a287892577578493a7f77d135d0721cd83371be65bd705b5d9f6bed6d236be1bd3a6bcb63fb6b6909ce
  | 7, 2 => 0xff939cefff8b32caff3992a2fb192d73fac274d4f96feb04f9092d95f2854adff17a65ebf15afe71f1027f58eef3064dee6bbfe2ed5ae6a4ec164c1eea782c38e6f71c21e606f433e3d420a8e25263cde1ccafbcda7890dfda26b2c9d9e7a089d9b9b7a8d8653959d58853add4fb6d4fd4e47617d1efb8f3d0dd3a20
  | 8, 0 => 0xf33b5fd0f2854adfdee29a6ad1efb8f3c3d681efbad4da24b47be621a6563cc3a1f16def7f4590c97e1a8a567cea112d76f0de33764e5f61705b5d9f61ca40085fbac6fd5e22a7545cde0cce51bb2a0f5059633d4aee737942b779a33e277fff34064f6c2efbd9642eedfa851b78d4bc1729918f1606144c0e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55005500ff00ff00550055005500550033003300ff00ff000f000f0f0f0f0f000f000f000f000f00050005000500050000ffff0000ffff00000000ffffffff
  | 0, 1 => 0xff00ff00ff00ff00ff00ff00f000f000ff00ff00aa00aa00ff00ff0000000000fa00fa00fa00fa00aa00aa00aa00aa00770077007700770055005555555555
  | 0, 2 => 0x11111111555555550f0f0f0f0f0f0f0f0707070707070707050f050f050f050f050505050f0f0f0f0505050505050505030f030f030f030f030303030f0f0f0f
  | 0, 3 => 0xaa55aa55aa55aa55aa00aa00aa00aa00888888888888888855555555555555555550555055505550550055005500550033333333333333331155115511551155
  | 0, 4 => 0xcc88cc88cc88cc88cc00cc00cc00cc00c8c8c8c8c8c8c8c8aaafaaafaaafaaafaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaa0aaaaaaaa00000000aaa0aaa0aaa0aaa0
  | 0, 5 => 0xeeeeeeee00000000eecceecceecceecceeaaeeaaeeaaeeaacccccccccccccccccccccccccccc0000cccccccc00000000ccccccc0ccccccc0ccc0ccc0ccc0ccc0
  | 0, 6 => 0xfa00fa00fa00fa00fa00fa00f000f000f8f8f8f8f8f8f8f8f0f5f0f5f0f5f0f5f0f0f0f0f0f0f0f0eeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeeeaaaaaaaa
  | 0, 7 => 0xfefafefafefafefafcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcf0fcf0fcf0fcf0fafafafafafafafafafafafaf0f0f0f0fafafafa00000000faf0faf0faf0faf0
  | 0, 8 => 0xffaaffaaaaaaaaaaffaaffaa00000000ffaaf0a0ffaaf0a0ff88ff88ff88ff88ff05ff05ff05ff05ff00ff00ff00ff00ff00ff0000000000fefefefefafafafa
  | 0, 9 => 0xfff0fff0aaa0aaa0fff0fff000000000ffeeffeeffaaffaaffccffccffccffccffccffccff00ff00ffccffccf0c0f0c0ffaaffaaffaaffaaffaaffaaff00ff00
  | 0, 10 => 0xfffafffafffafffafffafffafff0fff0fffafffafafafafafffafffa00000000fff8fff8fff8fff8fff0fff0fff0fff0fff0fff0fff00000fff0fff0f0f0f0f0
  | 0, 11 => 0xfffffafafffffafafffffafaffff0000fffff0f0fffff0f0ffffccccffffccccffffaaaaffffaaaaffffaaaaffff0000ffff0000ffff0000fffcfffcfff0fff0
  | 0, 12 => 0xffffffffaaaaaaaaffffffff00000000fffffff0fffffff0fffffff0ffff0000ffffffaaffffffaaffffffaaffff0000ffffff00ffffff00ffffff00ffff0000
  | 0, 13 => 0xffffffffffff0000fffffffffff0fff0ffffffffff00ff00fffffffff0f0f0f0ffffffffcccccccc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x324266b112d9a9259ae5
  | 5, 0, 0 => 0x19acb3587d735988cd9096019accc66614066b3119165b33a1335889b359acd96236d792133588d8066b3316965cd66bc966b98066b3257165cd669c466c9acd484cd6206b33e1335885acd46ecd6236cd6663f66b58066b2cd9095
  | 5, 0, 1 => 0x335998cd6986cd664b35c19b35992cd61f6019acb35c196cd492cd61e6
  | 6, 0, 0 => 0xb35ea4266b11be6b3099ac465decd4a5099ac46f9acc274b118f7019acc2588c9b00cccd1991e058066b28cc961ec00066b3259ae5016612f588cb359a926133588df364a5099ac46e033d966b108f601996232c3c0b66b3259ac3c19f35985019ac46e0336084b11966
  | 6, 0, 1 => 0xcd661c266b11b80cd664ac3c59b35984cd6230ef9acc866b118f701099a332040300b3091992c01b5d99d099ac46e0335966ad18f6cd66133588c7380cd6612d5859b3598f09db358f9acc266b119b7019acb3588c4b0084b119602018066b4cd6231ed9acc266b11867
  | 6, 0, 2 => 0x19acc266b0c366b3099ac4625f35a84cd6231ef9acc866b11877000335998cd6ae6b3099ac4611f359af259ac3cf9acc276cd82c7019a13338640b00cd6611c3259b3d984cd6211ee02cb358707806cd669c466b11be6b309ebb588dc06684b0e1602d9acc274d96237
  | 6, 0, 3 => 0x19ecc25884b366b3099ac462df35984cd62328f9accd84cd6237cd665c966b11b80cd6642c4659805966b118f00c0335984c51966cd6694274b11be6b34a4b35881f359a5099a946f9acd184cd6237cd66133588c8be6b316133588dc066b30991d2cc0355982b11966
  | 6, 0, 4 => 0xcd8213b66b11b80cd091992c05b35984cd62446f9acd684cd6237cd66bc266b103e6b3099ac4621c033588c78100d9acd290cd6237019acb358707b66b34a5b3588dc059588cb0f00d9acd084ed6237cd66bb766b11b80cd664b866b18066b3313232cc00066b3119b25
  | 6, 0, 5 => 0xcd6613f66b56380cd6612e4659b35e84ed9ac46f9acd284f5623701999ac383c0b00cd6561c2c3db35993099b058e0336084cd61c6cd6613466b11be6b3099ac4609c066b5096232cc02cb346647806b35213b66b11be6b35a13a588df3d9a5099ac42f9acc266b56187
  | 6, 0, 6 => 0x19acba588c7b66b3099ac4661c05984b0e1600d9acd384cd6237cd66133588c6be6b309db35ab1f35984cd62326f9acd284cd6227019acc4588cb366b35a433588dc066b2cce191ed9ad5284cd6237cd66ac266b11be6c526133588df35984cd6230ae0335984ad1966
  | 6, 0, 7 => 0x19acb3588c3b66b362133588df4d997099ac46f9acc27ecd6237016613338640366b3099ac4655f359a5119ac46f9acc266b11907cd667c266b11b80cd659ac3c19b35988cd62312f9acc274b11937cd6654266b11be6b325db766b1f359a5099ab46e0213358700806
  | 6, 0, 8 => 0x345984a91966
  | 7, 0, 0 => 0x19acc26acd6237cf9acc266b118f8000335984cd6ac601664c266b118070002133588c0806000335984cd61c6019b0d984b119670002cc2588cb006019acb3588ce8f7cd6694266b11a08cd96cd284cd6238019acb3588ce0f7019acd266b118f7019acc274cd6237cd66133588c7808019acc266c16237
  | 7, 0, 1 => 0x19acc276cd1997019acc2588d0967019add966b118f7019acc2588cb0f7016613e66b11807016664266b11807019acc984cd61c7000334266b0e016000335984b0e166000335992cd61e6016694266b11807cd664c276cd6238019acc270cd6237019acc266b11867019a13b66b118170002cc2668cc806
  | 7, 0, 2 => 0x19acd292cd6237019acc264b11967019acc266b11837000335984e96236cd6694266b11a18cd66133588ce0f8019acb358a918f7019acc258991967019acc2588cb007019acc27acd6237019acd284cd61c7cd664c266b11868000335984cce196cd66bc276cd6238019acc2588cc967019aed966b118f7
  | 7, 0, 3 => 0x335990cd6236019ae5984b11967019f35984b11967000335984cd8a36d79acd284cd6238cd6694266b11808019acc984cd6237cd8ecc984cd6238cd6694266b14238000335984cd91d6000355982cd623601ab35984b11967cd664c684cd6238cd7ecc276cd6238019acb3588c78a701a735966b118f7
  | 7, 0, 4 => 0x19acc266b56237cd6613b66b15238019acc984b11967000335998cd323600033d984cd62160003342588cb016019f35984cd199701b335984b11967019acd784cd6237019aed984cd61c7d59acd284cd6238000335984cd1996cd6613b66b1192801a335984b1196701ab35984cd1997cd6613b6ecd6238
  | 7, 0, 5 => 0xcd6694984cd6238019acbb66b118f7019a94266b11817d99acd284cd6238019acd084cd6237019acc2588ce167019acc984cd19970003342668cc816cd6613b72cd62380003359848cc966019acc266b151c7019acc278cd62370002cb3588c7806cd6694266b11838019a4c266b11817cf9acd284cd6238
  | 7, 0, 6 => 0xcd66bd284cd6238019acc282cd61c7cd6694266b119c8019acc266b11927000335984cd5a36019acb3588d08f7000335984cd7236019acd284cd1997cd6614176cd6238000335966b0e0f6cd664c266b13a38019accc84b11967000335a84cd6236d39acc266b118f8019acc2588ce967cd66bc984cd6238
  | 7, 0, 7 => 0x19acc2588cf16701ab35966b118f70166133588c7807cd76cc984cd6238019b0d984cd61c70002cc266b0e006019acb3588c7807019add984b11967019acc984ed9ac7cd6694e84cd6238000335988cd6236cd86cc276cd6238016613b66b11807cd6694266b119d8019acc884cd6237019accb84cd6237
  | 7, 0, 8 => 0xcd66133588d08f8000336084cd6236019acc266b0e1a7016613364b11807000345984cd5236019acc266b0e0f7019acb3588c78c7019f35966b118f7cd664c266b15238cd6613b66b12a38cd6613b66b118f8cd6ecd284cd6238019acc258a91967019acc784cd6237000335966b118f6019acc276cd61c7
  | 7, 0, 9 => 0x3359668cc8f601a6cc266b15237d39accc84cd6238019acc484cd6237019acc266b131c70002cc266bd6236019acc282b119670002cc266b1180601a735984cd1997cd6613b66b13238019acc966b118f70003333588c7816cd6694266b1523801b335966b118f70003359588cb0f6
  | 8, 0, 0 => 0x19a133588c0b6ccd66133588dc066b3096232cda335984cd6237cd72cc266b11be7cd66133588dc066b3099ac46dab35984cd6237cd6613364b11be6b3099ac4c8df35984cd62300f9acc266b11997cd66133588d0be6b3099ac463dc066b3099ac38d9acc276cd6237
  | 8, 0, 1 => 0xcd86cc266b11b80b3099ac4601b35985059ac46e0335966b118f6d39acc266b11be6b3099ac548df35984cd6233cf9aed984cd6237cd6ecc266b11be6b309f33588df35999099ac46f9acc266b119d7cd66133588ce3e6b34a133588dc066b3099a332d9acc984cd6237
  | 9, 0, 0 => 0x335984cd6236
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
  | 0, 0 => 0x1f1fe3fc00fff1f1fe38400fc41f1c23fc00fff0303fc7fff03f0303e07c0003f0303e0040000400ffe003fffff00001ffffffff
  | 0, 1 => 0x1f1fe3fc00fff1f1fe38000fc01f1fe0780003b1f1fe000000001c1c03f800ffb000000780003b1f1fe3fc00fc71f1fff8471fc4
  | 0, 2 => 0xfffc3f8471fc4e3e3fc7fff03fe3e3fc7c7f007e3e3fc7c7103fe3e3fc7fff03fe3e3fc0471004e3e3fc7c0f03fe3e03c7fff03f
  | 0, 3 => 0x1f1fe3878efc4000000038e0000000000380038ffffff8471fc4fcfc1f8071fc0e0e01c0071000fffc3ffc0f0c3ffffff8401fc4
  | 0, 4 => 0x3f003800000003f00000000000380f380303e07f8e03f0000007b8e03b000000038e0000000000000000000000038e000
  | 0, 5 => 0x3c000000000003c003fef3c0000007bfe03b0003c003f0f3c0003c000000000003c0000000000000003f0f0000000003f0f00
  | 0, 6 => 0x38e00000000000000001c1c038380ff81f1fe38400fc41c1c038000fc00003c07bfef3f0003c003f0f3c0003c07b8e03b
  | 0, 7 => 0x1c1c03fbfeffb1c1fc383f0ffc1c1fc38000fc01c1c0383f0fc01c1c03fb8effb1c1c038000fc01c1c0000000001c1c03838efc0
  | 0, 8 => 0xe0e0007b8e03be0e0000000000e0001c7800000e0e01c03ff038e3e3fc07ff004e0e01c03ff000e0e00000000001c1fc3fb8effb
  | 0, 9 => 0xfcfc00038e000fcfc000000000e0e3dc7bff03be0e3dc03fff3ce0e3dc03ff000e0e3c00000f00e0e01c7bff03be0e01c03ff000
  | 0, 10 => 0xfcfc1ffbffffbfcfc1f83fffc0fcfc03fb8effbfcfc000000000fcfc1f83ffff8fcfc1f83fffc0fcfc1f8000000fcfc038000fc0
  | 0, 11 => 0xff1c1fff8effbff1c1ffc00000ff1c1ffc00fc0ff03dffff0f3cff001fff8e03bff001ffc00000ff001ffc00000fcffdf83fffc0
  | 0, 12 => 0xffffe07b8e03bffffe00000000fffc1ffffffc0fffc1ffc00000ffe01fffff03bffe01ffc00000ffe01fffff000ffe01ffc00000
  | 0, 13 => 0xfffffffc00000ffffff83fffc0fffffc03ff000ffffe38000fc0ffffe003f0f3c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xa0a819c00d5d0a0a810400c04050421dc0055f03026c6d240360302604c00036020200040000400fde002dbbeb00001fbdb77dd
  | 0, 1 => 0xf0ee1dc00d7f0f0ee1d000d6b0f0ee0d80097b0f0ee040008220d0ce1d800d7b050460d80017b0f0ea1d400c470a0a9b0431e84
  | 0, 2 => 0x90901b043168463636c6f6c03663632c646c0064343684c6003642430c2d6401442430804600042322646c0c03621202c6d2c016
  | 0, 3 => 0x2a2a85278ec04202004238e0000000400b80138dadb9b0471e84d8d99b0071e80d0d11a0071280b5b436f00f0c39a9a930401c84
  | 0, 4 => 0x4041480bf033840410803f02000808c10b90f38272664ff8e17f252464fb8e17b252464f38e16b2524604208022242404b38e149
  | 0, 5 => 0x6f6fe042488226a6bcd2ffef3c65656cfbfe37b4a4bc90ff0f3c4a4bc90f60c344a4bc002408204a4b890ff0f1c48498903f0f08
  | 0, 6 => 0xb0b016239f280b0b012029b2809c9cd39b93ff99e9e939493fcd9c9c939093fc96f6fedfffef7f6f6fe94ff8f3e6f6fe4fbce97b
  | 0, 7 => 0xfdfdfffbffffbdedfdb9ff3ffddedfd392d3fe9dcdd9b93f3fc9bdbcf7fb9fffbbdbcf3d29bfebbdbce04208822bcbc97b39ffc9
  | 0, 8 => 0xf5f564fbce17bf5f5604248022f5941ef9b73d9f0f15e2bff3b8f2f31e27ff284f0f11e23ff280f0f1000248000fffff7fbdfffb
  | 0, 9 => 0xfcfd84b3ce949fcfd800248800fffffefbffbfbfafbdf2ffffbcfafbde23ffaa0fafbd302dbfa8f5f57efbff3fbf5f57e63ff2a2
  | 0, 10 => 0xfdfdfffbffffbfdfdfff3fffebfdfdf7fbdfffbfdfde04248822fcfddfbbffff9fcfd9fb3fffc9fcfd9fb36cc00fcfd9392dbfc9
  | 0, 11 => 0xffbeffffbffffffbeffff2cc36ff9e9ffdb7fddff4bdffff4f3cff267fffae57fff267fff2c436ff021ffd24414feffdfb3fffe9
  | 0, 12 => 0xffffe4fbce97bffffe04248822ffff9ffffffddffff9fff6cc14fff77fffff7fffff77fff6c436fff31fffff694fff31fff6c414
  | 0, 13 => 0xffffffff6cc36fffffff3fffebfffffe63ffaa2fffff3d2dbfebffffe94ff8f3e
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 52 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 52 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 109 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 109 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 109 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 109 then wireAt i else 0
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
  | 3 => 2
  | 4 => 13
  | 5 => 195
  | 6 => 1081
  | 7 => 1244
  | 8 => 11
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0x7e6d7e233a7cba36
  | 4, 0 => 0xc599750ea02b961c9d6843209b83ab5894c167a6616de8554a14de34467761af361d63262e2f3f4f176d640f13857f690c41564f
  | 5, 0 => 0x4da469374b79d9074b6e21e64ae3fc0945ce0d59448f38e242d05b1742b779a3425f5ccb40e31f383d29c89f3cbf50053c3b0ee53b6273ae39b14359377ab9dd35c6e9dd3470b169341812ec3378e8ac32d891c031c561e3317a69f63171152930b661672ff968f32fa7d1792ded0ebb2a954864292de39f2884fdf827fa285b2705880d23cd0d6222bb5ff7217c18ce1fdd54731fccc3341f7307771e02d8001dc96b4f1d0f705318611f4a16c8fc3615e06ff2153eaa18151183d7150d4cfa14f7c9e7149d101313bf8c24122947da11a3b9ed113bb9910ef402390e5e461c0e5088980df6e2ed0c4fcb820b2eab5709484a9d09332be604751f9303a3e4f1
  | 5, 1 => 0xa6f6c169a6a291b4a60d590da4e3c223a3a9d24fa36442dba256c1a09e2823d09e04e86b9d7264b39b2a44129b1033fb988c6c5b98501f2197a9fca0977ed1a095fef19394f80eff8efbc7eb8eadbcbc8dc04a4f8d1aa7bf8b4ae684882be4e187e288ad84d9962f84129c408175276a80f7e8887e7135af7cf270267cd916067cca1c587b2b17a17b0c272f7a85129f78c378757680fac47495ccaa72c5dc677267536d707d47f06c3b1f926bed0c326afac892689a2e6f686ee828681616b2676b923d64e6ab02634ce8445eeccb305ee284145e6364645aa8a6b95a599a3259d395c757f76733545b5df7544b97f053fc57df52daacc14fdb72544e9f53f7
  | 5, 2 => 0xfc545228fb382a76faf17dc7fa9d20d9f96feb04f8602ac6f63811c1f60e0476f56b233bf4591915f44935f4f3e97183f3294459f203afdaf05c41ceeec542e3ecb47af8ec2a4e25ea178ea6e9ee24e9e714c0f9e6f71c21e69a76f7e5f8e4ade2bb0fede28cf0a1e25263cde24ee520e2421ff8e0dd1820dc8f93a2d8fc4c31d6caf2f8d531990cd4571ed2d3b847d9d38ed5b1d1941c87d0405004cc1639eacbd9bba8cba791caca9b30a8c8584d64c73b354bc50cab75c4f7a12bc4bc713cc058a567bdd97ef6bc03177bb8ab99d5b7d064c6b702d21ab630f23db5ac93d1b436aa11b3fe15f1b253cde2b1c4b500b02c9557ac1aeb1ea7f773d9a7e94bfb
  | 5, 3 => 0xff7c7227ff31a300fee24069
  | 6, 0 => 0xfcb33c20fc7e3a30fc75d210f8898390f8009980f3d84400ee2d2210ea800b80e7e15130e737a980df70cce0dcd46f30cd896110cd88bf40cabde0a0c97cf590c8b5f720c3486130b9636f90b88cc090b2c8ce60b15b2110a7677f509ea0c3209e2061c09c0e32809a18f54096e691e0966c06b08828543078c6002073168250725e9590711d49e068d7fe10644c923060f596e0609e28605e77d7105e1326505bbae7e05169eb00514ebac04f7ea4d04b7f8ed049f4c5904941f6a041db66f0341d11b033a727c02c16857026249d201e3cad001866a36018309d901752afa01652a32014fcec7011eaa2f0111cbc90074ab57005b006f00296567000db973
  | 6, 1 => 0x1b7eaebf1b78d4bc1b62a5db1b3080b11b27d2611ac899ce1ac6cf551aa1953a1a8e01df1a4058c31a04d97919ff9c8019f9a28419bbe0571923eb0b1921f28d18f811bf18eed24c18eabeb418c904ec18bf975f1882b16917a260fe177154d6175a929b173c6c161734bd561729918f16bd508a16b01e5416a82ea1168bc85d1673385e164f38e016446b9c163cc666161181741606144c15e9498b158a31d715776f9515719ffe156a912f1517feab14b47c3e149b001d1499cfe513e0e2a7138cad00133c08ef13346ed1130a5a8912c3605312bbd308124d6d6311b4bd5b1187183a1161181a11408e9a1106ad5710aeb074103a99120ff651070fec104b
  | 6, 2 => 0x2b1903882b09ceab2b08f8cc2af8e8dd2aad75692a892cd02a709ff12a53358729f0b1cd29342757291d2a9e29167c2528e1d56328c73e9828b1318528a4a83e28a1dfb02886920f28668e6d285f166527efd837275958f22750b4f62745d00f272a02302713cf002705880d260932412602ca6f259a313724dc268124b5fa3e24425a84242f7cff23c083972385334722e093b222d85c9a225a2cd4221388372177d428213bddeb2129b3ab20d5617920292edb2014d45a2014c6441fe039d21fa432931f7c1b131f75faad1e961c6a1e56e02b1e184c7d1d75a3ee1c6af0321c32bad41c1250521bfe706a1bbaa2fd1b9f1c631b9d622f1b9386ad1b933b9e
  | 6, 3 => 0x398649303958c2ee394f1420390153ab383545ab3821da6637b281a737a858a737a4a2c83790d599376ecd6236fb367836de7a8736c164023678c0eb366487033609387935fe022a35d89aaa356512d03541768b34d2fbb734c8f0c734a771a734886bc33451707d344f47aa341c017334064f6c33df688433da662c33d93c6b33d51d6733a2828e339be83033722ba03294f0e0329066733241f77231f5eab331381b0730d5282030ad467230a9d7c9309ade1b308c42f8306f6ccb2f20329b2efbd9642eedfa852ec68d272eb937762df741622de6358a2da94f942d9165262d59ed9f2d52d1502d06d0c22c7dc05e2c6cb9a92bae16fd2b81626d2b7b467f
  | 6, 4 => 0x49780ea84910933d48d58fd64854372b47d1bb1b4777cddc4760868246f1b31146df279b46de284246b6a8dc469949b545f126ed45e00ffb45abfc7845940ada4546c2da447ee81e442294a04408d56743fdf1ec43f5039043e9290d43bc23ab432e5dba43110caa43008d1e42e28e1442ddddac42b779a34270b5be425ac010418c58194170bcbe414a8c1f41320659410ee2ea40e3c4e340a28b4c4000dc1f3fdedec33fd24e333fca2bf63fa66a2d3f74539f3f6ce07e3f086e6d3e7b57fa3e38dfb93e277fff3da4f3293d8a3cae3d820b7b3d254e653d1f3f593cedcf813cbcf7af3c21f90f3bc8e96e3bbf524e3b43ce223ae826bb3acf9b4b3a2d6c62
  | 6, 5 => 0x563580cb5618ad155571ce4a5567a85054f251df54b88b5354b1935f54a96c09548d14555416d04b53e2c57853dbb72c53a51bbc5354fc3553514afd53466db8532df2e152dc9cdc52a7682352943af55281620b51ed228251e93bed51ccc13e51bb2a0f51608443514aca6d5137e929512f757251249501511d2be450b1940650a9730450a1bacb508708d35059633d504a74d84f9d2f8d4f7141a24e92e7bf4e7855394dd542384dc9c7c04db248164d2f3d364c46545e4c2571154b40518f4b2e44754b226b904b21fba14b11aa524b1168534b093b3e4aee73794a932f4e4a25f49949fd469d49eb066449e3bfbd49e0f04f49dada4749d9fcdb49b6983f
  | 6, 6 => 0x64b23f0e64a0c73f642e54a0640f62e363fb6a7f63939f336370981062d4bd2362ad0ad462a25050627050f9624ac82b61f63a0061ca4008614299cc6056b15e5fbac6fd5fa9e2065f878d095f147ca25ec2fe405ebc0fda5ea8e5c25e96063b5e22a7545e13ada65dc082c05db6ae185d3f7bd25d0eae245d00c56d5cde0cce5c499e5b5bb03c075b83bf685b4dbe2c5b2752065ac7832c5aa67b745aa5f5965a9c6dcb5a71d2525a0921ad59c84b7059a0c2fc593aae785916f56259100b8058f47f0f58e6c54658bb889f58a9df50587b5a065843000558118ebc5807cc0957c545155742a795573f28535731497456e6f7eb56d32b8f567c7f515659605e
  | 6, 7 => 0x7613d46a7508aada74fe289274789e6473ea5b6e73e2848473da4b1a73be0f4973a48879736f42c17331c268731046f8727718da72739f54722d71c671ca317b71b731cf718d4b85718aa31d7128819770ad25fa70aa5d93706b57b9705b5d9f700050ab6fe0c5006f3a9e9a6ec911ee6ec7a3626e008d486dd08b0e6dbbe1966d76e7956d1da4d86d0792ab6cfb7a1c6cf4f29e6c4b6e046c1c148c6b3457826b1be3666a80e84b6a5698e66a5427376a41599e6a2177b56a08291468716f406816246d6786b84767757f61676198836742e73067296a4a66ef807f66d94f9766d0a35666c9726066a873e6666aceee65e88a3d65b4b669658f435664dbdd21
  | 6, 8 => 0x820b9a5f81e9f85c81dd85f4818bda65815fcf97814662f38123ee88809fa26d8051d8b37fe02d2f7fbd20fa7fa786767f8776eb7f4590c97ed513f37e5697697e4dc0ce7e22ace77e22428f7e1a8a567d41b0af7d2e7cf97cea112d7c69c65e7c698bc57c64c2c77c60a6ce7bfa0c557bf77ccf7b9474917b460e827b334ca57b301d047af39e807aeab7127abe6b607aa19e707a7a23a87a01223179fe78fe79e5550479684f627961f7277955da0f792903cc791205e278dd6d38789cb22c78325ccc7819d385780e8f5777dc326977d135d077cfa6b177ae3ab077abf413778decba7770373f76fcecf676f0de3376d6e3217682f477764e5f61762f5b71
  | 6, 9 => 0x8fc42d338f78512d8f74f0a98f1f96978e8c53638e5d90ed8e52fbf68e3f8c778e13a1f68e0cfa578dacf6f48d88441d8d6a7b858d5eaaf98d5c0a998c73f3678c4a4e318c3e211a8b74ea068aa44b2d8aa3b04f8a81f0ca8a516cc38a4b2c568a3ed98f8a0d8ef789acfcb18945a6a98931d08d88f8d26988f823fd88a82a54884052b78826fc398809f96f87fe15ec87fc390c87ec2302877779c38759f0be8722d2c18703169686d13299868f8bfa868cb4248665f64385f6241e85a0b970858e52b884520cd5844b1cd484064fcd83f9716783f53a1c83ee5c6183e8a98c83e07d8283c0be0983b3542383621177833bbae283223ce882e0b6ab82c96d8a
  | 6, 10 => 0xa0908dfca05ab451a053c87f9fe0f6769f9fa5ee9f342d229f307a4a9f22e88e9ed6de7b9ed1e5489e93ebe99e5c023f9daae7359d42c3eb9d3bb9e79cf14cd49cbb54e09cb443fe9bc6e6ac998cea0d9933b443992721c299200f92990f6ebb98ff0c18989eac8e987d90c0982e64fb97cc960797c54e4097885ff9977b024e977488ac974d430d96d93d1e96c4ed5d96bea8b1969aeb72969645529689804d9661aced965db264963ca10f963297ec95d8122595370e76947da14a942df4bb94062d51936ef3a093602c4693303d3b931c4d07931a02fc92d649fa92beb264927d838492409e4992002a6a91eb7da791aecc409149dd84911a43058ff6aa35
  | 6, 11 => 0xb272d876b250cd45b169cadfb0dde46bb06a21d7b0433de6b02e6dafb02513ebaf647c31af0ce506aef5af7aae6de29cae18ff3dae110966adeaf2e8ad1abbf9ace9658bace77cbcaca9b064ac41a9b3abdd680fab37265aaaa81632aa801c35aa67fba6a9f3d131a97aa236a9679bafa94c64a9a909e4c1a8f6772ea89bce41a851a7e3a828f69ba8249059a788dfb8a6c134b9a6adad0ca65dd945a6563cc3a6193286a5fe72d7a5d4719da592a0a9a58443aea533b563a52d601ca4b188daa476e968a3eb5964a3744415a3677a35a34731dba33952fca2efe0c0a2c8618ea2a97873a284be75a22b6a16a1f7dfcba1f16defa195b11ca0c4a17fa0c3dee6
  | 6, 12 => 0xc0a55ccdc05fc100c04eefd4bfb8773abfb0cba3bfa11256bf751e77bf39cbf0bf1537f5beea5a39bec0a575be907f01be4be64fbe4769d9be3add0dbdeb6445bd7258e7bd63e280bd328e64bccd4b3fbc87e6edbc591900bbcf1011bbb69bf5bb779f5abb69340dbb1f582ebb184a9abae9d770bad4da24babf470fba45dd7fba45b6caba40b91ab9a146b8b95f4ed5b90d8a13b8d90467b87ee534b8405c07b80ba678b7ae1533b7a1fd24b72f93ffb71329c5b6f9cc08b6bcc305b666254db6251136b5e82352b5a0fe76b58b0cf8b51ce2f2b4fc8e64b4cc51f8b4bad623b47be621b37c045eb3152a51b303514fb2fb9a4cb2e2d36fb2ce525eb2bce3e7
  | 6, 13 => 0xcfaaeb5dcf77959ccef3ff30ce998bb2ce597d4cce1ee8e6cdf98342cde202f0cdda9258ccc7daa6ccbe85adcca27ba8cc8d2a32cc1a159bcbe36130cbd5b4f2cb668644cad25745ca5d1f3fca4b1c80ca34bcdeca2ab66fc9e0b175c9b16cf9c8e779a6c8df6e8fc8856e22c7fb6ba2c71b0c31c70a3a3ec6bc9380c63e6ab8c63e11c5c6068286c5c29045c59c2c97c5899ec0c5736c6ac54de09cc5368674c50c7b54c4fac133c4acd4d8c4a4bbb4c462ab86c4209f4ec3f68888c3d7b039c3d681efc38b8267c3780010c362a18ac3606443c337f1aac2c56a8ec2932210c28adb2cc285e459c2472df4c1ebf1e0c1e70f7dc1dbbeefc16a70b1c0d8bcda
  | 6, 14 => 0xe267227de1ee1201e1a29dc4e1151f08e0d18bdae046d2d6dfe045a4dfcc093ddf6c17f5df204264df01c523dee29a6adec9dac1de4eb049de361975de23d5bfdcbf3510dc30d869dbe6b227dbc7af05daa10b17da650bedda26d716d9de4eddd91d26b3d8eda793d8d7c2ffd8c89669d87f9952d87aa7e1d845f1ead6d35949d6b4c389d6ab1780d615987fd612c66fd5ce88c2d5bfd6fdd58ce416d445852fd43813c6d4077324d4061f74d3a84f1fd34d4128d33b7be2d32d9d03d3152e0bd30d0d53d2b5723cd26dffcbd26d319fd2370a95d231461dd20d1552d1efb8f3d1dc942ad19616d2d191abc0d1879d90d0bd03c8d07c82adcfd1b474cfc00382
  | 6, 15 => 0xf10d2c13f0fa8a62f0556ec8f027341ef0010e1beff84593efeb934aef321432ef2e15f7eef3064dee1e2c58ee02495bee000531edb06ad3ed6e538bed4c8833ed215bcfece493ddecb47af8ecadcc7fec6b46deec677269ec19d0deec164c1eec0c1396ec00923bebf03b1eebd9c278eb3c36aaeaf7f023eaf32cf0eabec0cdeab31e8aeaa64cb1e9e0e609e9b0c204e96fe5a4e964ad1ae9644731e94a3d90e88d44c1e8529c71e82d725ee7eb888ae7e8d4afe79a729ee79942ade6debce7e6548bb9e605b34ee5e351dce5e14f13e5d68d5ae5b44ac5e54c555fe4df0f60e4a6b616e41e5447e3ef42d0e3ca2ab6e3182913e2f6af66e2f4375de2e5bc00
  | 6, 16 => 0xffcd14d5ffc6e326ffa13466ff98826cff939cefff55b127ff03a3d4fec4ed6ffebe0ea5fe3abca4fe133845fd60f9a1fd3430c6fc4ac213fc4a1fedfc0c146cfbf20813fb3bf322fb12ce0dfaec6079faae1c57fa7d76fdf9efe375f9b17da6f9afb2a4f98494c9f96feb04f9414bd9f908e400f89c6bb5f7cb8231f7bccefef6e3f0ecf6dac2e4f6d3c780f6adfee5f650f9aaf5facc8df5e5463cf59108abf58f108cf57a4822f51cd756f437cf40f41eea52f390e940f38cf389f33b5fd0f2b97b7df2854adff26d9b06f265e2cdf249a559f171c893f146644df13569a4f12be4b6
  | 7, 0 => 0xe7dd0190e783ebe0dfb96ef0df078900db675560d9cbe430d52c9a60d4d98860cf91d9f0cea20e10cc7aa850cb3009d0c867e660c2cfbb60bd753a90bb2ffb10b989d440b41c7720acf09dd0ab7b9ae0aa9dacf0a9628be0a172c4909ee1b6f08d6f0260878675807d82e3c07bd347d07af559e0754ea15075140fd06c7654b06b07a030663442506556796065223ce05c61dd605ad2f34059e8b170590310f05169eb0040745c603e36454036df1500360127103476202033a727c02e9d44b02d5abde0296f5790291d00a024a740d023f103c01a603fb0198251c0188fb4b018309d90129b75501013f3600dd496a0086a50c006499150027347900103def
  | 7, 1 => 0x1a2bfa9c1a0ece701a0dc40d19f08aad19e3604919b1d4481979f417196672e11923eb0b191531f41900f42918e3fb0a1881f686183e8305181aa94117d7cb9517d07b0017a82026175a929b1729918f16e8db1816d8a81c16b50ee916a82ea11606144c15f86a8015f022ce1581f8c81561a43a1528ba3c141a4f1c1415063f14121a0c13b5da6d136d10ac135211a2131bfefa1317dd2b130748e512baa67712b8ab4112b8884a12ae5da3129997eb12798028124e26351232479711ed84b711eb7ccf11d748061187183a11761aa81142fa411134c93410d1aa96103ead2a1004221f0fc22fb60f8b2a5f0f6b9a140f5c5cfb0edd17080ea68d810e8414b2
  | 7, 2 => 0x26aa53c326a4b5bf265363bb264ea12126488ebe26396ad4262d41fb2609324125bece64258a6ea42509c4b824cb7b2924a7e76c2485a934246554a623fe6fae23afce9223a7fde62310763b23038dd422daf26b22d85c9a225c733222543c1c21e9d24d21a5f9682179389d20df43cc2081cc61204aaf2d2046aaad203e530f203cd04e1fe039d21fd3d3851f608b651f3d31db1ee4e3db1ebb13731eb3facb1e8eec381e739d441e7359ed1e08e1531d989e101d81c57f1d73f5661d29fe0a1d094b741c8c41261c53b96d1c1ffead1bea35011be841c11bde45011b78d4bc1b70b1901b61a0cd1b52f3321b325a461a90e4691a5d39541a45ab1d1a4058c3
  | 7, 3 => 0x354bc4fd3518dab134746a9f34744a7f342cdee934064f6c33d93c6b33193e9a330961a63294bf403264f1943243d5cd317141fd31381b073122199e30ccd1eb30bda81a3055c0a62fc976f62fa1c82a2f7655c82efbd9642eedfa852ee51d392edbd6b52ea0b9112e9e70832daad2e42d770a592d6df75a2d014b912cf3c0ef2cf085992cb7e2692cae27f22ca821632c9946a22c1543872baacaed2ba0a43a2b0f56702af4104e2acd7a982a7c85282a6cf0712a6bdfc02a60bc7d2a5e00e12a5175e429e942c42964176b292df8a1291abe562882e2b2284db2db2775450f2774c460275958f22727707326e36c2426d2458e26d0c80326beaf6f26bb2fef
  | 7, 4 => 0x40bb28344079af63405c8f3d40455b7a4025ca0a3f6ce07e3f49363a3f086e6d3ee6de3d3e9c5ebb3e277fff3e1c8eb63dff89d03df1aaf13dc32c533d8620523d6d0b963d18fbc93d0124c93cedcf813cd7d7c23c9f3cdf3c9dc2fe3c9d75a23c8fe41f3c3d49423c39fd5e3c38e0113bf3e2703bd0b7833bc2d8a43b5624293b3c318a3b23954e3afd7b253acd3e823a8b9b213a8b1a653a861c993a67daad3a47663439de879e396f572d3958c2ee3950034038ad846e3899ed18387c221637dd7e80375fd1e83732d33a3724f45b36f4981f36e4026d36c744ae36ad51603678c0eb366fa272363c57f436224d1b35d89aaa359aee6d357bcd57355e29ce
  | 7, 5 => 0x4e00c0ea4de27c5e4dd111674dc27b5b4d2b306b4d17706a4d0476064cfd734b4cd8ba054ca60af44c1e35cd4c173de94bff26be4bf147df4bc969994bb8974e4bb13b214b7591cb4b62f61f4b40518f4b0c2c394b02825d4afc5e1e4aee73794a6707154a59283649e125c6499cfa0a499b08ca48fa38cc48f889f848b0ac9d484e6acf475141bb472e33c146e1bded46e149a24696c818465e79d54609964845f6b58445c07cca457c5ed145179a8f44d9dfff44cd758b43cee64d43b9f0a343b4257143a9f8484365b3a9433f660a4309ffd84305883642b779a342815d8a4223bdb94215deda41d622d341a8390641a4b5d6413f306a413ca69640db2d8b
  | 7, 6 => 0x58905d13581fb8f65806ebe257c3519856fffaeb56dbe56f56da22f056abec62568ff7f1567ee6cd5640306856240dff55df5df855bb43f755ab6c4654b47b9853b7a8b55342fdb7531915d1531692945314eaf652f2fea452e996fb52de426a52acbe7d52943af552942b72528ca2425275541c523dc211520a3fab51efbb6051e81d5151d2062b51bf3f2b51bb2a0f51ab7a23516924ff515c2919514f645451099cc651007c3a50c9577f50c4b4ed50a706e8505beeb35059633d5038abd6500139404fb2394c4f9b055d4f943bc44f8c57c24f717d1d4f624ff44f490be64f0fba7a4ec05ebd4e79bd534e7327324e5bae794e1db72a4e1717654e0e9fc9
  | 7, 7 => 0x65b4b6696554bad164ffcc4e64e30e6464789948645092fc6449b75d64015902638147926379a67663669d95633af0116336351163353df463275f156292bf2262623a356240ab8761f427ee61aa33686129ea2960d1580460c0164560b58bf56001a2b65fd513de5fbac6fd5f5d13a95f492eb65f2a63495eebace45edafec85ec6f1c75ec2fe405ebcebc25e90082e5e22a7545e1657ce5e06e6065debf6475dc82fa15d93d62e5d7bf2db5d3a46645d2e415c5d1e66bc5cde0cce5c9fbd605c91de815bff541c5ba915895b4388f85b2acd595b0171135a73054d5a437adf59f223e559e9c31b59d66aa05992adb0596bf2065923c1c65916f56258a5f177
  | 7, 8 => 0x72e03d9b72b28339727daf3d72739f547260e48f71fb25a2714a8ba9710f96de70cdf07470c4152b70946692707cee8d706753917005f1236fa6c90d6f6c29a26f69601f6f3b46226ebe77696eba99336e9f1e276e834bca6e8018a76e38e6f66e34ebde6e1ad9ba6db8095f6d5cb0976d483b2f6d2657c06cd622c66c4b6e046c1c148c6bcf90f36bc490ee6b89f08a6b7c11ab6b58c0516b46b4d16b1be3666af785736aa2ab606a5eea176a510b386a4fc62d6a4f22086a2a46cf6a0139de69f5d2f969d0a4b069b2eaed692e70ee6920920f68b561d0688d1b55683fb3fc67f1c0d3679d352a67425c616709aa6167044c4c66fb4c91668c47706659a12a
  | 7, 9 => 0x7f97da8d7f5f0e0b7f4590c97f27d8097f1797dc7ebd26667ebbf6017e22428f7e1a8a567dfd47397dd5c4a57db1e1917dad4e397d776c2f7d356db97d303bbe7cea112d7cd372a07c0721267bc86ac17b4614867b25f4ae7ae97d0f7ac854af7ab597257ab2c9087aa157477a2bfc5d7a2bf43679c9043d79a4d76c798a90b27952d274794717d67946d3e3791d9b41791304537900675a78f04d34785a178977f10ba27770373f7733bc5377211a3f76fcab1e76f0de3376eecc3f76db0b2e76bdf4b976b015da766385db764e5f61754008987521769374f2245d74e1bd6174d2ee78749b9886745a681c73f60c3a73a4532b73a1eeb77341d2fd7333c42e
  | 7, 10 => 0x8bbc73f08b8fda438b7e195e8b308e208aef68758ab84b5d8a8bfac78a7994f88a59f30f8a4b2c048a18c2888a0d10dd89f226db89beef4c897643b689605ac28958e8bc88f823fd88edfe0d88ede028886bb2a587ec230287cdddd087ca80ca877c8a9f877910e2876b3203872610b887080352868cb424867726a18651842c8635a6fc862851b985f48e9f85e99b5485ba4fb98562e87285520fcd85210b03851cbe16850f030e8492c7cd83f048fb83d9bb2c83c5bc52838341f483833bd7834a6d93833df90383233d8083223ce8830766bf82ddd8a582d3eb99828511a482739f2082121d0d81b633a581102355806266ad804281917fc0036d7fbd20fa
  | 7, 11 => 0x96fad25696ac2a8596a4b77d9690ba6e9680ac86963c456d9603a49895fe78aa95bdb66e95a996be9502be1694b8834e9497281e94331b659409b1f093f42b8d9396353d93602c4693527dd5934043b892ef453392b08ece929a9c84928df768928cbda5927d83849272b1cc926d751e9262028d925c0be491426eab91015b8b908ca4449074f28c906d26119037c66b9011f58290061e318fa4cc1f8f9d1d5f8f7fd14d8f78512d8f6680978f46f2108eb06ba68e7679718e4941358e35cdb08e27eed18e2374cd8e21c9a38e0d834f8dce939b8dbfa66d8d7f04bb8d6fdaea8d6bb4b28d3d413a8d1e3ac28ce77a638c8386ea8c1a6ee88bedc1998bc68b50
  | 7, 12 => 0xa71939e5a70b5b06a6563cc3a6395456a62fa927a623790ea5e4c2a9a5cabbeaa5103ec2a4dede88a499e38aa494c22fa36baaf7a35f8a0fa309310ca302d5f5a2f4f716a2d8fffaa1f16defa1c6431fa0c045e2a0b26703a07b3991a02ef21b9ffd08839f9262399eab30d29e58572e9e14ab229de9f1209d61744b9d42bc1d9d2d50bb9c97dd089c48de239c36144f9c27c3cd9bfcd7929b71391a9b34b1219b1dd7b09aec1f2b9ab47d5a9ab0be7a9a81c9ca9a36658d99ed5e8799bbfbc99985b807997d4564996c23f4992c6790992721c298fcecee98d83969985a34f798553ede984899db981b7e9297ec88bb97a5128c9721f5ed9713ecb197012b84
  | 7, 13 => 0xb3feb3cab3f8265db37ef559b354b256b32b1ae2b315333eb2dc7687b272f2abb2572353b253eee6b23cd636b2313513b2306866b22e7c90b210ca3fb20ffb62b1b17014b18cc501b12375bdb0f51e5bb0ec7e1fb0e1dcffb07bc511b04d71d7b02268afb01ae1b0b00d02d1afebec7daf95e2ffaf935789af01b67aaef43dc2aee65ee3aec64c0eaebd223cae8d3699ae064aa9adab993dada32de2ad85a160ad6e1b08ad1a90a7ace974c5acac34b6ac23afedabbe6e52ab94b348aabfa2cbaab1140caa8df529aa75a9a3aa3f12b1aa38618daa2867c5aa21bb6da9cb11c2a98c5b5da9647ee6a909e4c1a8e78fc4a8d9852aa8d69abba80d4bfda77ce252
  | 7, 14 => 0xc33e8ebcc31b6fd9c30bd3fac2afde01c278c27bc21dcfbbc1c6e06ec1c5a5bec1c16a74c16463c6c150c440c110cb7dc1043454c07ccfeebf46884bbf4172fabef5700abef4bb49bef1afedbee065e9beb2f988be4f311bbe3418b4be1fe45dbe107ab6bddd5bacbd5c9ba0bd2744b8bd0683e7bcc8e334bcb2dff7bc5e25f5bc545819bc008a33bbec3344bb3f92c0bad4da24bab08b31baa8a17cba9e7ab4ba708858ba477786ba45dd7fba1f06b4b97e2118b9782853b85c2f59b84d21e0b837fe7bb81d78f4b7a3f583b7610a65b6edc245b6be7634b69fded2b67d321ab65f3e8fb644e080b5c9ec3db559ed2fb52557b8b5195244b4d0d4a4b47be621
  | 7, 15 => 0xcfe713d2cfca0951cf9551ebcf6e15b1cef7401aceecb93fceeb1ad8cecb96dfce8cc780ce412b29cdfcbe79cdd2d617cdb20f90cda803e7cd73df73cc0d7bc5cbfcbae9cb9cd379cb46a5f8cb26fa2bcb191b4ccae6d7d7ca5eb5a5c9e24337c9d88a90c9d46458c9c8daa4c9a019fdc8e779a6c8df6e8fc8d8951dc876c3bec7ad77bcc7a9b843c7a3ca76c7554d2ec7466283c73804a5c707ac1ec6f762cbc6ea46f2c689fa79c6398efac62ad07cc61b5c10c5e58a67c5dca5abc5c226a0c5899ec0c577bfccc576ef75c52f7576c4eae2e7c4d4624bc4ac2c82c483e9fec4605fcec44be902c3d681efc398766ec37f968dc362a18ac3598a1dc34f33b5
  | 7, 16 => 0xde7f8515de1b0bb2ddfd151addd7f9c9dd9de376dd547ea2dd4db3aadd1bb31cdd0995b1dc240579dbeeb34ddaf5c757da8fa153da8008d2da52a0c6da0af02ed9ed2281d9eccea3d9ab6bc3d988b69cd96359b3d958a3e4d90de9d2d8f62b1fd8e7dfa1d8dd76c6d8cf7726d89de169d87f9952d86400d8d863d13ed7d8277ed7c2c847d7c0c947d7661623d6fe6644d69e993fd697c1d4d6890d25d64007d5d62ad27fd5d13c99d58ce416d56748abd4f736c8d43f7d82d3fa20bfd3b34341d3a21f4ed38eac86d355d4ffd3152e0bd2da325bd229a3e5d1d3f658d1b38e6dd17f337bd1786b89d0e5095fd0ab600ed0a7e5c1d051c79bd0317033d010ef66
  | 7, 17 => 0xec848404ebc28ee5ebb77889eb7a065aeb3fcd10eaf7dac4eabec0cdeabceb59eaa64cb1ea9e47f9ea88152aea555bf2ea39f55dea04555ae9f23fa9e9d3bc26e9b38944e8f19d4fe8b54ab1e8b03ee3e878be20e86f0f45e812cbdfe7a75556e73f702ce7283c3de7199440e5d4dd4ce5c6ac76e5b5122de575a6eae5179d48e49194eae48a3599e4763a0be4625a30e45c7de4e4402e8ee32cc12de2f7dbbfe2f02cffe2e94854e2e453e9e21fca1de1c2a466e1b94d76e1283faae0f3695fe0d9cf49e0d27efae088d44de07b344ee04a17a1dfdba1afdfb32b5bdf91a28ddf7fbf91df71e0b2df6d0221df41afa0dee29a6adede789bdec9aaa0dec49712
  | 7, 18 => 0xfab495f5faa130d0fa6ea56dfa4dc81bf9acd0faf9824cb5f9091127f8b72109f80ff336f80fe67ff7fbcecdf7e68aa8f772bfb1f76d67adf762f14af734b506f725d631f6e94291f6657479f6655c2cf646c3bff637ead7f62cba88f62c0f9af5a8ee32f5493ef0f5210d0ef50771aef39bac49f34c8d5af33b5fd0f2e571d9f22186e7f20a7ebff1c7ebb4f1c31697f1c1f496f171c893f15a4793f14d1f92f13569a4f109fd47f0f10dbef0c2900ff05fc8f2f053c1fdf03d9387efeaeca8efdef6d4ef7de2e4ef0e3eb4eec76f65eeae7dabeeab662cee570e7dee22ff53ee1e2c58ee185818edf5513bede64ad6ed74eae1ed71b5aeed5612f6eca193e2
  | 7, 19 => 0xffcceadcffabe638ffa13466ff5a28feff3df527fefc312dfefb8721fef2bd64fed37441fe9afd92fe12eeb4fe091979fdf560cffd875a02fd797b23fd75d7f8fceb370cfce2758bfcb0a9dbfc7cb7dbfc3e0176fc3cf275fc3650befbefb591fbe5e7c4fb7259a6fb113ac2fabc44b5
  | 8, 0 => 0xdd9de376c2afde01b6be76349b34b1218ab84b5d8a7994f855df5df84f8c57c21e7359ed1561a43a1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x70109355084004708115480400
  | 4, 0 => 0x8115480300000000000000f00118204803000018840500300000412544030000085504843000011820480300001182048030000085504843000018042508300000811548030000041254403000010935508300
  | 5, 0 => 0x20480200000000000000c0000000000004000000000000000000255002000000000000004000000008110700000000000040000000000002000000008110700000001001000000000000006000000000000f0000050484200000000000000000000000000000000000000004000000000000f00000204802000000000081107000000000000b000000000000f00085504843000000000081107000000008110700000000811070000000081107000000000001200000000811070000000000006000c1154c03010000000000012
  | 5, 1 => 0xf0000000081107000000010010000000000c51120000000000000000000000000f00000000c91120000000000000000000008110d000000000000b000c5504c4301000000008110700081154803000000000000002000000008110700000000000060000025440200000000000000b0008550484300000c1154c0301000000000000b0000000000000000004050020000000000811070000000000004000855048430000041254403000000020480200000c1154c0301000002550020000000204802000000000000002
  | 5, 2 => 0x85504843000000021484200000000000000b000004050020000000000000020000000000000000c5504c4301000000000000600000000000040004135440301000000000000600000521012000000025500200000000000000b00000000811070008115480300000412544030000000155002000004125440300000005110d20000041354403010000000000012000001044020000000501092000000042508200000000008110700000000000060000000000000000000000000f000000000000400000000000040000035500200
  | 5, 3 => 0xf000000008110700000000000040000015480200000004508120000000000000020000000000004000412544030000000000000020000000081107000000000000a000000000000c0000000000012000000000000200000355002000000000000006000000000000f000000000000000000000811070000000000006000003550820000000000c9112000000008110700000000000040000000081107000004508120000000000000000000000000004000000000000f000000000000b0000000000000000000000000b
  | 5, 4 => 0x400000204802000000000000012000000000000000000000000040000020480200000000000000e000000000000200000510c920100000000000020000000081107000000000000e0000000000012000000000000b00000000000060000000081107000000010010000000000811070000042508200000000000000c0000000081107000002544020000000000000040000000000003000000000000000041354403010008115480300000000008110d000000008110d0000000000002000005110d2000004135440301
  | 5, 5 => 0x855048430000000000000060000000081107000c5504c43010000045041200000000008110d000003550020000000000811070000000000004000000000000200000000000010000000081107000c1154c0301000000000000f00000000000000004125440300000000000000400000000811070008115480300000005048420000000000000120000035508200000004508120000081154803000000000000003000000000000f0000041504200000c5504c43010000000000004000003550820000000000000000000000081107
  | 5, 6 => 0x8110700000510c9200
  | 6, 0 => 0x400000000000070000000081107000004504120100000000000070000000000006000000000000700000255002000000000000006000000000000000000000000040000000000008000005110d200000000000000400000000000040000000000002000000000a100000000000a10000000304c0201000000010d103000000010110000000000000040000000000006000000000000f000000000000c000000000000600000000000060000000000004000005110d20000000000000040000000000001000004350c201
  | 6, 1 => 0x7000000000000500000000000040000000012101000002544020000000000000000000000000003000000000000600000000021000000000000000000000000000600000000000020000000000001000000000000700000000121000000045041201000000008110700000000c110300000001041010000000000007000000000000d0000000000007000000000000f000000000000300000000000080000000000006000000000000300000000000020000000000012000000000000b00000000000020000000104101
  | 6, 2 => 0xa0000000000006000000000001100000000000020000021484200000000000a100000000000000e000000000000e00000000000060000000000005000000000000a000000010d1000000000000004000000000000e00000000000050000000000002000000000000600000000000120000000012100000000000000200000405002000000000000006000000000000300000000841000000000002100000000000000700000000041000000025440200000000000000600000000000030000000081100000000000a100
  | 6, 3 => 0xa0000000006100000000000000200000000c9112000000000a101000000000000400000000000120000000000010000000000000600000000000020000000000002000000000000e000000010010000000000c410b00000000c11030000000000002000000000000a000000000000700000154c020100000001011030000000081100000000000000c0000035500200000000000001200000000401000000000000002000000000000200000001001000000000000003000000000e1000000000000002000000000000c
  | 6, 4 => 0x81107000000000000c0000000000007000000000000e00000000811070000000000003000000000000600000504c4201000000000a101000000000000b000000000000e0000000000007000000000000f000000010410100000000000000000000000002000000000000200000155002010000000000002000000000000400000000000030000000100100000000000000f000000000000b00000000000120000000000005000000010410100000000000050000000000004000000001210100000000000060000000000012
  | 6, 5 => 0x4150420000000354402010000000000009000000000000f0000000000002000004350c201000000000000a0000041504201000000000000100000104402000000000000004000000000000300000000841000000000000002000002148420000000000021000000000000004000000000000c00000504c42010000042508200000005110d20000000000841000000000006100000000000000200000255002010000000000007000000000000200000000000030000000000012000000000001200000154802000000000104100
  | 6, 6 => 0x4000000010010200000000000000000015500200000000000000e0000035500200000000000000b0000000000006000000010910000000000000020000000000002000000000000b0000050484200000000000000400000314c420100000000000080000000084100000000001210000000000811000000035508200000000000000e00000000021000000000100102000000000000b00000000000020000010440200000000000000e00000425082000000015500200000000000000500000000021010000000000002
  | 6, 7 => 0x25500200000000000000200000000000040000000000004000000000000e000000000000f000000000000c00000000000020000000081103000001550020000000000000030000025440200000000000000f000000000000200000000000040000010440201000000000000c000000000000700000000000040000000000004000000000000200000000000070000000000000000000000000b00000000000050000000000006000000000000200000000000060000000041100000000004010000000304c02010000000084100
  | 6, 8 => 0x9000004504120100000000000020000045041200000000000000600000000000040000015500201000000000000a00000000811070000000000006000001548020000000000000040000035508200000000000000200000000000020000000000000000000000000400000000000030000025500200000000000000c00000001081000000000000003000000000a10000000000c11010000000000002000000000000c00000000000060000000000002000000000000700000000c9101000004150420000000304c0201
  | 6, 9 => 0xc000004050020000000000000060000000000003000000000000200000000000040000000000002000000000000c000000000000f00000000811030000035500201000000000e1010000000000009000000000000000000000000120000000000004000000000000700000000000020000000000003000000000000b000000000000a0000000000004000000000000a000000000000c000000000000300000304c020100000000000010000000000008000005110d2000000000000000000000000000b0000000000005
  | 6, 10 => 0x80000000000006000000000000600000000c51000000000000006000000000000c00000000000080000000109101000000000000200000214842000000000000007000000000000600000405002000000000000005000000000000400000000000040000000000007000000000000e0000021484200000000000000f000000000000a00000000000020000000101100000000000000c0000000000008000000000000a000000008410000000000000050000000000006000000000000500000415042010000021484200
  | 6, 11 => 0x2000000000000e000000000a1000000000000006000001044020100000000000080000000000012000000000000c0000000000004000000000000c00000000000000000000081100000000000000200000000000040000000000002000000000000c000000000000e000000000000c00000000000010000000108100000000000000600000450412000000025440200000000008110700000001051000000000000002000000008110000000000000060000000000002000000000000600000000411030000000000002
  | 6, 12 => 0x20000000081100000000000000600000000000030000045041201000000000000f000000010910500000000000030000000000006000000008110300000000000020000000000007000000000e10000000000000030000000081107000000000000a000000010810000000000c11000000000000006000000000000a0000000104101000002550020100000000000070000000000004000000000000300000000c9101000000000000c00000000c110300000314c4201000000000000500000000000070000041504201
  | 6, 13 => 0x40000000000010000000000000300000104402000000000000002000000000000c000000000000200000000c110100000505042010000000000008000000000000c00000415042000000000000001000000008110000000425042010000000041103000000000e1000000000000006000000008110700000000000040000000000001000000000000400000000000050000025500201000000010d1000000000000000000000000000e000000000000e00000504c4201000000000000a00000504842000000000000000
  | 6, 14 => 0x4504120100000000000020000035508200000004350c20100000000000040000000040100000000000000200000001001020000000000002000000000000200000000000120000035500200000000000610000000000000020000000000002000000000000a000000010d10300000000000100000000000009000000000000f0000000000002000000000000500000355082000000000081103000000000000f000000000000c000004350c20100000000c1103000000000000200000000c110100000425082000000000041103
  | 6, 15 => 0xd00000000000020000000081107000000000000b00000000411030000000108100000000000000800000000000120000000000000000001548020000000000000020000000000012000000000000200000001041000000000000004000000010410000000000811000000000000004000000000000e000004504120000000000000050000000000002000000000000c000000000610000000000000040000000000008000000000000400000000000050000020480200000000000000700000104402010000050484200
  | 6, 16 => 0x104101000000000000e00000355002010000000000003000005110d2000000000000000000000000000000000000c110300000104402010000045041200000000000000200000000000020000000000004000000000000c000000000000b000000000000a0000000000006000000000000400000155002010000000000004000000008110000000355002010000020480200000000000000d00000154802000000000000003000000000000100000000021000000000000009000005110d20000000000000000000000000006
  | 6, 17 => 0xc000000000000a0000035508200000000000000400000000000070000000000004000003544020100000154c0201000000004110300000000000020000000000004000000000000200000000000060000000000000000000000000400000001041010000000000006000003550020100000000000080000000000006000000001210100000000000010000000040100000001044020000000000000030000000000000000000000000200000000000030000000000007000000000000100000000c410b0000000000002
  | 6, 18 => 0x300000000000090000041504201000000000000a000000000000c0000000000004000000000000e000004050020100000000000040000000000006000000000000c0000000000005000000010810000000000c1103000000000a1010000000000002000002544020000000000000120000025500201000000000000600000000000020000000081107000000000000c0000000000006000000010110300000000000070000000104101000000000000c0000000000002000000000000400000000000000000000000002
  | 6, 19 => 0x811070000000000002000000008010000000000000020000000000003000000000000300000314c4201000000000000e000000000000a00000000000120000040500201000000000000000000000000060000000006101000000000000800000000c1100000000000000400000000c11030000000000002000000000000b00000000000070000000006100000000000000e00000000c910000000000000080000000000002000002544020000000504c4201000000000000200000000000020000000100100000000000000e
  | 6, 20 => 0x610000000000000050000000000004000000000000400000000000070000000000003000000000000b000000000e101000000000000e000000000000f000000000000700000000000020000000000003000005048420000000000000040000000000003000000000000e000002550020100000000000000000000100100000000000000300000001011030000000000009000003544020100000000000030000040500200000000000210000000154c02010000000000002000000000000500000000000120000000000004
  | 6, 21 => 0x4000004050020100000000000060000000000002000000000000700000000000020000000000006000000000000c00000000000080000000000003000000000000c00000000000050000000000005000000000000300000000000000000000081101000000000000000000000000020000000000007000000008110000000000000060000000000002000000000000200000000000010000000100102000000000000c000000000000e000000000000b000000000000500000000c110100000000000090000000000005
  | 6, 22 => 0x2000000000000c0000000000012000000000000c00000000000020000000101103000000000000c000000000000000000000000030000000000006000000000000f0000000000000000000000000600000000851000000000000002000000000000c00000000000060000000100100000000000210000000000000030000000000008000000000000f00000000801000000000000002000001044020100000000000030000000000002000000000000200000000c1100000004250820000000415042000000000000005
  | 6, 23 => 0xf0000042508200000000000000600000415042000000000000005000000000000300000000000030000050484200000000000000c000000000000a000000004010000000504c4201000000000000c000000000000000000000000000000000000002000000000000700000155002010000000000002000000000000100000000000060000000081100000000000000200000000000030000000000005000000000000a00000000121000000000000002000000000000b000000008010000000000000020000000000004
  | 6, 24 => 0x6000000000000000000355082000000000000000000000000000900000000000000000000000004000000000000f00000154c0201000000000000400000000000000000000000007000000000000c0000000000012000000000000200000000000080000000000006000000000000c000000000000e00000000000040000000000003000004150420000000001041010000000104100000000008010000000000000020000000101103000000000000c0000035500201000000000000000000000000070000025500200
  | 6, 25 => 0x60000000000007000000000000b000000000000e000000004010000000304812010000025500201000000000000200000000000050000000000008000000000000300000000000000000000000012000000000000d00000204802000000000000008000000000000900000155002000000000000002000000000000100000000000030000000000003000000000000c000000008110000000000811070000000000004000000010410100000000000050000000000006000000010410000000001041010000000000007
  | 6, 26 => 0x3550020000000000811070000000000006000000000000200000000000020000000002100000000000000c000000000000c000000000000f0000000104101000000010010200000000811070000000000001000000000000200000000000020000035440201000000000000000000000000040000025500200000000010410100000000811010000000080100000000010010000000000000030000000081107000004050020100000405002000000020480200000000000000b000000000000300000000000020000000000007
  | 6, 27 => 0xa10000000000000020000000000002000000000000a000000000000b000000010010000000000000030000000100102000004350c2010000000002101000000000000e0000000000004000000008110300000450412000000000000002000000000a100000000010010000000000000100000000000000000000000000300000000000020000035440201000000000000c000001548020000000000000060000000100100000000000000a00000450412000000000000007000000000001200000000000040000000000007
  | 6, 28 => 0x8110000000000000020000000000002000000000a1010000000000002000000000000200000001041000000000000007000000000000c00000000000080000000000010000002148420000000000000040000000000006000000010d1030000000000002000000000000c0000000000008000000000000f000000000000c000000000000700000000000070000000000004000000000a100000000000000200000000000040000000104100000000000a10100000000000030000000000012000000000000c0000000000002
  | 6, 29 => 0x10d10300000000000040000025500200000000000210000000000000040000000000006000000000000300000000000060000035500200000000000000400000355002010000000108100000000000000b000000008410000000000000060000000000009000000000000200000000c01110000000000001000000000000f0000010440200000000000000b000000000000e000000000000600000000000020000015500201000000000000e000000010810000000000801000000000000006000000000000e0000000000012
  | 6, 30 => 0x801000000000081107000000000000e000000000000c00000000811000000000000002000000000000c00000000000070000000000006000000000000f000000010910000000000000050000050484200000000000a1010000000000004000000000000200000001001000000000041103000000001210000000000000030000000000008000000000000700000000811000000015500200000000000000800000000000020000000000012000005048420000000000000040000000000007000000000000a0000000000001
  | 6, 31 => 0x700000504c42010000000000005000003550020000000304c02010000000104101000004250820000000314c4201000000010d103000000000e1010000000000006000000000000200000000811070000000000004000000000000a000000000000000000000c910000000154c0201000000000000400000000000030000000012100000000000000500000000c1103000000000a1000000000000005000000000000400000000000060000000000012000000000000200000000c910100000255002000000000000007
  | 6, 32 => 0x800000000000040000045041201000000000a10000000000000050000000000008000000000000a00000000000020000000000008000000000000e00000405002010000000000006000000010d103000000000000700000204802000000010440200000004150420100000001091000000000000004000000000000e0000000081107000000000000500000000c9100000000000000700000000121000000000000008000000008110700000000000020000000000002000000000000400000000000020000000000003
  | 6, 33 => 0x15500200000000000000c00000000000030000000000007000000000000e00000000000090000035440201000002544020000000000000000000000000002000000000000400000154802000000000000002000000000000c000000000000f00000314c4201000000000000a00000000000040000000000005000000000000600000000000040000040500200000000000000100000000000060000020480200
  | 7, 0 => 0x411000000000000001000000000000400000000000060000000000007000000001210100000000811010000000000001000000000000000000000000050000000000007000000000000c000000000000300000000000030000000000006000000000000600000001041010000000104100000000004110000000000000060000000000009000000008410000000000121000000000000003000000000000600000000000000000000000001000000000000100000000000120000000000000000000000000a0000000000001
  | 7, 1 => 0xe00000000000070000000000005000000000000300000000000060000000000000000000000000e00000000000120000000080100000000000000600000000000070000000109100000000000000e00000000c91000000000109101000000000000100000000000000000000006100000000000000200000000c410100000000121010000000000004000000000000300000000000120000000000007000000000000200000000000030000000000007000000000000f000000000000e00000000000010000000000003
  | 7, 2 => 0xe00000000000020000000000001000000010410000000000000120000000000002000000000000300000000000070000000000004000000000000c000000000000000000000000030000000000006000000000000b000000000000700000000000030000000081101000000000210000000000000020000000000006000000000000000000000000000000000109100000000000000100000000000070000000041101000000000000700000000000050000000000005000000010d10100000000000010000000000000
  | 7, 3 => 0xa0000000000005000000000e101000000010d101000000000a100000000010110000000000000070000000000012000000000000e0000000085100000000000000200000000000050000000081101000000000000b00000000000020000000040100000000000000300000000000080000000000002000000000000e000000000000600000000000120000000000002000000000000600000000000010000000000005000000000000300000000000000000000000003000000000000c0000000000002
  | 7, 4 => 0xf000000000000200000000000010000000000002000000000000000000000c5100000000000000300000000000120000000000006000000000000a000000000000100000000000050000000101100000000000000c00000000000010000000000003000000000000700000001041010000000000000000000000000c0000000000000000000000000400000000000070000000000007000000000000e00000000000010000000002101000000000000f0000000000004000000000000100000000000060000000000006
  | 7, 5 => 0x1011010000000108100000000000000600000000000000000000000007000000000a1000000000000003000000000000800000000000070000000006101000000000000e000000000000a0000000000004000000000000300000001051000000000100101000000000000c000000000000b000000000000900000000c5100000000000e10100000000000080000000104101000000000000000000000c11000000000002101000000000000300000000000100000000000012000000000000700000001051000000000000001
  | 7, 6 => 0x4000000000000f000000010d1000000000000003000000000000c00000000000010000000000005000000008510000000000000030000000000005000000000000d0000000000007000000000a1000000000000006000000000000d0000000000003000000010010100000000000120000000000000000000000e101000000000000700000000c010100000000061010000000000000000000000001100000000000080000000000007000000010c101000000000000b000000000000400000000000120000000000002
  | 7, 7 => 0x2000000000000600000000811000000000080100000000000000a000000000000700000000000060000000000004000000000000b0000000000003000000000e1000000000000003000000000000b00000000000030000000000002000000010d10000000000000030000000081100000000000000d0000000000002000000000000e00000000000060000000000003000000010010000000001041010000000006101000000000000b00000000000040000000105101000000000001000000000000010000000000001
  | 7, 8 => 0x1000000000000700000000c91000000000104100000000000000c000000000000000000000121010000000000006000000001210000000000000010000000000005000000000000200000000000020000000000000000000000a101000000000000d00000001091010000000108100000000000000f00000000000030000000000005000000000000d0000000000000000000000000700000000000040000000000000000000000000200000000000020000000000004000000000001200000000000010000000000003
  | 7, 9 => 0x5000000000000c000000000000700000000000030000000000003000000000000200000000000020000000000002000000000610000000000000020000000000003000000000000a00000000000070000000000003000000000000000000000c1101000000004110000000000000010000000000001000000000000500000000c11000000000000001000000000000700000000000000000000000009000000000000c00000000851010000000000007000000000000300000000c410100000000121010000000000003
  | 7, 10 => 0x20000000000002000000004110100000000000030000000000005000000010910100000000000030000000006100000000000e1010000000000002000000000210000000000000010000000000000000000000000c000000000000000000000000010000000000006000000000000e00000000000020000000000001000000000000700000000061000000000000000000000000000a00000000c41010000000012101000000000210000000000000070000000000000000000000000500000000000000000000041101
  | 7, 11 => 0x1200000000000040000000000000000000000000000000000000030000000081101000000000000600000000000030000000000000000000008510000000000000000000000006101000000000000b0000000000009000000000000900000000c91000000000080100000000004010000000000000020000000000004000000000000c0000000012100000000010d1010000000000003000000000000b0000000000003000000000000c00000000000060000000002100000000001210100000000000000000000000002
  | 7, 12 => 0xa1000000000000001000000000000a0000000000003000000000000400000000000060000000000002000000010d101000000000000d000000000000600000000000030000000085100000000000000600000000000080000000000001000000000000e0000000000007000000000000c000000000210100000000401000000000000001000000000000d00000000801000000000000003000000000000e0000000000007000000000000200000000000000000000000005000000000000700000000000080000000000006
  | 7, 13 => 0x90000000000006000000000000700000001011010000000000004000000000000700000000000010000000000003000000000000300000000021010000000002100000000000000a0000000000001000000010410000000000000070000000000002000000000000c0000000041101000000000000c000000000000200000000000080000000000003000000010c101000000000000400000000021010000000000006000000000000e000000000000c0000000000001000000000000c00000000c91010000000000000
  | 7, 14 => 0x300000000000010000000000000000000010510100000000000010000000101101000000000e1010000000000005000000000a1000000000000000000000000000000000000000120000000000001000000000000700000000000000000000000008000000000000f00000000000070000000000000000000000000500000000000090000000085101000000000000000000000000040000000000003000000000000200000000c5101000000000000300000000000070000000000007000000000000c0000000040101
  | 7, 15 => 0xc1101000000000000500000000000060000000105101000000000000000000000000110000000000012000000000000700000000000010000000006101000000000000000000000061000000000000002000000000000c00000000000120000000000006000000000000800000000000020000000000001000000000000700000000000020000000000005000000000000400000000000050000000000003000000000000500000000000010000000000007000000000000e000000010010100000001001000000000108100
  | 7, 16 => 0x2000000000000100000000000010000000000007000000000000f000000000000a000000000000c0000000000006000000000000100000000000040000000000006000000000000f000000000a10000000000000030000000000002000000000001200000000000060000000000000000000000a1010000000000008000000000000f0000000000000000000000000100000000000020000000000009000000000000e000000000000100000000000010000000000003000000000210000000000121010000000000003
  | 7, 17 => 0x30000000000003000000001210000000000000040000000000012000000000000300000000000010000000000004000000000000c0000000101101000000000000700000000c11000000000000007000000000a1010000000100100000000000000c000000000000700000000000030000000000009000000000000600000000c1101000000000a10000000000000030000000000002000000000000500000000000060000000000011000000000000100000000000000000000000003000000000a1000000000000002
  | 7, 18 => 0x3000000010410000000000000040000000081101000000000000400000000000000000000000007000000000000f000000000000500000000000030000000040101000000000000100000000c41010000000000002000000001210100000000000020000000084100000000001210000000000000020000000000000000000000000b000000000000000000000c11010000000000000000000000000100000000c11000000000000009000000000610000000000000030000000000002000000000000200000000c9100
  | 7, 19 => 0x4000000000000700000000000000000000000002000000000000d0000000000000000000000000300000000000080000000000007000000000000700000000c11010000000000003000000000000100000000c0101000000000001200000000061010000000000002000000000000700000000411010000000041100000000000000600000000000010000000000003000000000000a000000000000e000000000000c0000000000008000000000000300000000000000000000108100000000000000b000000000000e
  | 7, 20 => 0x10d101000000000000c000000010910000000000000030000000012101000000000000e0000000000002000000010c1010000000000000000000000000c000000000000e00000000000050000000002101000000000610100000000000020000000000003000000000000200000000c910100000000000040000000080100000000000000300000000000060000000002101000000000000b0000000000001000000000000300000000000050000000000008000000000000200000000000020000000000004
  | 7, 21 => 0x700000000000080000000000000000000010010100000000c5101000000000000100000000000070000000000000000000000000500000000000030000000002101000000000e1010000000000005000000004010100000000c9101000000010410000000000000050000000000002000000000000200000000000020000000000003000000000000400000000c51000000000000006000000000000c000000008410000000000121000000000080100000000000000000000000000040000000000008000000000000c
  | 7, 22 => 0x10d1000000000000000000000000000000000000c010100000000401010000000000008000000000000300000000000120000000006101000000000000200000000000060000000000004000000000000400000000021000000000000007000000000000b0000000000009000000000000e00000000c9100000000000000400000000000050000000000003000000010410000000000000070000000012100000000000000c000000000000700000000000070000000041100000000008510100000000000070000000000010
  | 7, 23 => 0x5000000000000300000001091000000000104101000000000000000000000000030000000000002000000000a100000000004110100000000c1100000000000000200000000000020000000000003000000000001200000000000030000000000011000000000000700000000000000000000100101000000000000c00000001011010000000101100000000000000b000000000000500000000000090000000000006000000000000600000000851010000000000000000000000001100000000c51010000000000004
  | 7, 24 => 0xc000000000000f000000000000d00000000000060000000000005000000000000200000000061000000000000000000000000000d00000000061000000000000003000000000000d0000000105100000000000000700000000000100000000105101000000000000d0000000105100000000000000000000000000010000000000002000000000000500000000000060000000000001000000000000f000000000000300000000c51000000000000007000000000000d000000010010000000000000030000000000000
  | 7, 25 => 0x800000000000030000000000000000000000000000000000000030000000000001000000010d10000000000000020000000000000000000000a101000000000a100000000000000c00000001011000000000000006000000000000a00000000c4101000000001210100000000000030000000000001000000000000900000000000060000000000012000000000a1000000000000008000000000000000000001091010000000040100000000000000c0000000000004000000000000600000000000090000000012100
  | 7, 26 => 0x121000000000000001000000000000600000000000090000000000008000000000e10100000000000070000000000001000000010810000000000000020000000000007000000000e1010000000000007000000000000700000000000070000000000003000000000000e00000000000080000000000004000000000000100000001051000000000000009000000000000600000000c11010000000081100000000000210000000000000060000000000007000000000000700000000c51000000000041101000000000e100
  | 7, 27 => 0x411000000000000001000000000000c000000000000400000000000010000000000003000000000000000000000811000000000000003000000000000c000000000000300000000000060000000000000000000010d10100000000000010000000100100000000000000e000000010810000000000000020000000000009000000000a1000000000000007000000000000000000000000040000000000004000000000000f000000000000300000000000060000000000005000000000000100000000000070000000084100
  | 7, 28 => 0x700000000000030000000000001000000000e100000000000000400000000000020000000000007000000010c10100000000000040000000081100000000000000700000000000070000000000001000000000000700000000061010000000000007000000000e1000000000006100000000000000e000000000000100000000000030000000000001000000010d100000000000000300000000061000000000000003000000000000500000000000090000000000012000000000000100000000000020000000000002
  | 7, 29 => 0xe0000000000002000000000000300000000000000000000000006000000000000b00000000c910000000000000020000000000001000000000000300000000c0101000000001210000000000000110000000000000000000000000300000000000060000000101101000000000000100000000021010000000000001000000000210000000000c91010000000000006000000010910000000000000000000000000002000000000000100000000000020000000000001000000000000100000000000020000000000000
  | 7, 30 => 0xa000000010410100000000c010100000000000050000000085101000000000000500000000000000000000000004000000000000600000000000060000000000000000000000000300000000c510100000000c910000000000851000000000105101000000000000200000000000010000000000007000000001210000000000401010000000000003000000004010000000000000070000000000001000000000000700000000000000000000000001000000000000c000000000000300000000000010000000000007
  | 7, 31 => 0xb000000000000400000000000100000000002100000000000000100000000411000000000000002000000000000000000000000050000000012101000000010410100000000000080000000000012000000000000300000000000010000000000003000000000000d0000000000005000000000000f0000000000006000000000000300000001011000000000000004000000008410000000000000030000000012100000000000000400000000000060000000000006000000000000400000000061000000000000007
  | 7, 32 => 0x1091010000000000004000000008510000000000000060000000000003000000000000200000000c110100000000000080000000040100000000000000500000001091000000000000010000000000000300000000000000000000000002000000000000500000000000020000000000003000000000000100000000000030000000105100000000000000b0000000000009000000000a1010000000109101000000000610100000000c5100000000000000e0000000000008
  | 7, 33 => 0xc000000010d1000000000000000000000000000c0000000000000000000000000c000000000000200000000000050000000002100000000000000200000000000020000000000000000000000001100000000000050000000000003000000000000300000000000000000000000000000000001210000000000000020000000002100000000000000c000000010910000000000000070000000000001000000000000400000000000000000000000002000000000000200000000000040000000000002000000000000a
  | 7, 34 => 0xa100000000000000d00000000000020000000006101000000000000000000000c410100000001011000000000000002000000000000200000000000120000000000000000000000000c0000000081100000000000000d0000000002100000000000000e000000000000900000000811010000000000010000000000000700000000000050000000000002000000000e100000000000000e000000000000600000000000090000000000007000000000000300000000000040000000000002000000000000f000000000e101
  | 7, 35 => 0xa0000000000006000000010c101000000000000700000000c5100000000000210100000000000070000000000005000000000000e0000000108100000000000000d00000000c9101000000000210100000000061000000000000001000000010010000000000c110000000000000010000000000002000000000a1000000000000008000000000000100000000000060000000000005000000000000c000000000210100000000000030000000101100000000000000600000001001000000000000007000000000e101
  | 7, 36 => 0xc5101000000010c10100000000000050000000000005000000000e1010000000000002000000000000200000000000120000000000002000000000000c0000000040101000000000e10100000000c910100000000061000000000000000000000000000c00000000000060000000000003000000000000c000000000000e000000000000200000000000090000000000001000000000610000000000000060000000000000000000000000300000000000030000000000000000000000000500000000000020000000105100
  | 7, 37 => 0x12000000000e10000000000c1100000000000000300000000000000000000000003000000010d10000000000000120000000000002000000000001200000000000010000000000001000000010510100000000000000000000000007000000000610100000000000010000000002100000000000000c0000000000006000000000000000000000000070000000000005000000000000a00000000000070000000000005000000000000000000000000080000000000005000000008510100000000000010000000100101
  | 7, 38 => 0xc0000000000001000000000000300000000121010000000000000000000000000500000000c51010000000084100000000000000000000000000050000000085100000000000000f000000000000600000000841000000000012100000000000000100000000000040000000040100000000008110000000000c01010000000080100000000000000200000000000080000000000003000000000000a000000000000900000000000030000000000003
  | 8, 0 => 0x100000000000000000000000001000000000000000000000000010000000000001000000000000100000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 7 s ws hint
  | 1 => checkCutEntry dom_8 roots_8 7 s ws hint
  | 2 => checkCutEntry dom_10 roots_10 6 s ws hint
  | 3 => checkCutEntry dom_12 roots_12 6 s ws hint
  | 4 => checkCutEntry dom_14 roots_14 6 s ws hint
  | 5 => checkCutEntry dom_15 roots_15 6 s ws hint
  | 6 => checkCutEntry dom_16 roots_16 6 s ws hint
  | 7 => checkCutEntry dom_17 roots_17 6 s ws hint
  | 8 => checkCutEntry dom_19 roots_19 6 s ws hint
  | 9 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 10 => checkCutEntry dom_20 roots_20 5 s ws hint
  | 11 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 12 => checkCutEntry dom_9 roots_9 5 s ws hint
  | 13 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 14 => checkCutEntry dom_21 roots_21 5 s ws hint
  | 15 => checkCutEntry dom_13 roots_13 5 s ws hint
  | 16 => checkCutEntry dom_18 roots_18 5 s ws hint
  | 17 => checkCutEntry dom_7 roots_7 5 s ws hint
  | 18 => checkCutEntry dom_11 roots_11 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_22 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_22 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_22 == dom_22) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_22 goalM u ys) : RunD dom_22 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_22 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
theorem z5_16 : ∀ i, 16 ≤ i → i < 21 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 16 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 21 → Z 5 i = true := range_split z5_0 (range_split z5_8 (z5_16))
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
theorem z6_128 : ∀ i, 128 ≤ i → i < 129 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 128 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 129 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (z6_128))))))))))))))))
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
theorem z7_152 : ∀ i, 152 ≤ i → i < 159 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 152 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 159 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (z7_152)))))))))))))))))))
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
theorem z8_24 : ∀ i, 24 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 24 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 32 → Z 8 i = true := range_split z8_0 (range_split z8_8 (range_split z8_16 (z8_24)))
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
  scr dom_22 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_22 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_22 roots_22 goal_22 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_22 goal_22 := by
    have h0 : isConstB dom_22 goal_22 = false := by decide +kernel
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

end S_22

theorem low_22 : Lower dom_22 roots_22 goal_22 10 := S_22.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_22_bits : ∀ r : Fin 64, roots_22.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_22_lt : ∀ r : Fin 64, dom_22.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_22 T)
    (hlow : Lower dom_22 roots_22 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_22, Avail mask256 roots_22 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_22 hfan 0 roots_22 roots_22 rfl hsup0
  set out := (execN C.gates roots_22).getD C.output 0
  have hout : out &&& dom_22 = T &&& dom_22 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_22_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_22 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_22_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_22).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_22)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_22.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_22 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_22).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_22 &&& mask256 = dom_22 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_22 = T &&& dom_22 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_22, hd63, hout]
  have hnc_m : ¬ IsConst dom_22 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_22 roots_22 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_22, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_22 roots_22 0 roots_22 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276940960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_22.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_22 10 hT6 (by unfold IsConst; decide) low_22

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [8, 4]⟩, ⟨GateOp.and, [10, 5]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [14, 9]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_17021_aux

theorem PEqualNP.Outside.L_meta_17021 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276940960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276940960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_17021_aux.wit, PEqualNP.Outside.L_meta_17021_aux.wmono, le_trans PEqualNP.Outside.L_meta_17021_aux.wsize (PEqualNP.Outside.L_meta_17021_aux.lower s hs), PEqualNP.Outside.L_meta_17021_aux.weval⟩
