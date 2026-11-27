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

namespace PEqualNP.Outside.L_meta_13089_aux

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

def dom_0 : Nat := 0xffff0000ffff
def goal_0 : Nat := 0xfac80000f888
def roots_0 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (4, 12), (5, 7), (5, 13), (6, 7), (6, 14), (6, 38), (8, 12), (9, 11), (9, 13), (9, 41), (10, 11), (10, 14), (33, 35), (33, 41), (34, 35), (34, 38), (36, 38), (36, 44), (37, 39), (37, 45), (40, 41), (40, 44), (42, 43), (42, 46)]
def r1sG : List Nat := [1, 2, 4, 5, 5, 6, 6, 6, 8, 9, 9, 9, 10, 10, 33, 33, 34, 34, 36, 36, 37, 37, 40, 40, 42, 42]
def r2sG : List Nat := [3, 3, 12, 7, 13, 7, 14, 38, 12, 11, 13, 41, 11, 14, 35, 41, 35, 38, 38, 44, 39, 45, 41, 44, 43, 46]
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
  | 2, 0 => 0x84b696a7
  | 3, 0 => 0xadd760487ae1bc6c6a67de2a32ac7a96
  | 4, 0 => 0x8cad584267ae8f7554e97e244fada6a444dbae4a3e9f5e0b2a48ff951412d30a13645f700f1fce070afba44c03b0c7d70335d817
  | 5, 0 => 0xa7da18faa1c0b4b87ea52a9a7445a6b572657d5c6b7180a36949f7d6686e9bda5b61388b270b03de160058940f1fce070da784ce
  | 6, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xc0c00000c0c00000aaaa0000aaaa0000aaaa000088880000aaaa000000000000aa000000aa000000555500005555000000ff000000ff000000000000ffff
  | 0, 1 => 0xfa000000fa000000f8f80000f8f80000f0f00000f0f00000f0000000f0000000eeee000000000000cccc0000cccc0000cccc000088880000cc000000cc00
  | 0, 2 => 0xffcc0000ffcc0000ffcc0000ff000000ffcc000000000000ffaa0000ffaa0000ff000000ff000000ff000000f0000000ff00000000000000fafa0000fafa
  | 0, 3 => 0xffff0000f0000000ffff0000cccc0000ffff0000cc000000ffff0000aaaa0000ffff0000a0a00000ffff000000000000fff00000fff00000fff000000000
  | 0, 4 => 0xffff0000ff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x163453
  | 3, 0, 0 => 0x757346460c286479634644cd2444
  | 4, 0, 0 => 0x1b4cd2865697348195a48d286569930a19554cd286569634a195334b28657d334a195a3cd286569334a195a50d283581134a195a4ce2865
  | 5, 0, 0 => 0x69340d286601334a180569334a18066944cd286669334a206669334a1c666994cd286669334c286601a4cd282571a4cd286669344d286601a4cd286569334a1816
  | 6, 0, 0 => 0x1a4cd2865
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
  | 0, 0 => 0x38030ce190c3000030c0000003803cf31e60ff03fc003fff
  | 0, 1 => 0x38003c00fc0f003f0000000ccf00030330e2c0c0003003000
  | 0, 2 => 0xf0cff8bc33f00f0c0003f0ff19f00fc03c00000f0000003ccefd
  | 0, 3 => 0xfff0003fff0e2fffc003ffce19fff0063ffc000ff0fff3fc0000
  | 0, 4 => 0x3ffff00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x85883a171de3b5c768ad71c80058278428e21c405d02ac00377f
  | 0, 1 => 0xfa2fd53bf77ffaf897f2a82554ddf22031772ebc5d4aaf003240
  | 0, 2 => 0xfffffffffffd4fff2203f9ff7ffa2fd53e8ad54fa22003ffffff
  | 0, 3 => 0xfffb753fffaebfffeb03ffdebbfff32e3ffc880ffafff3fe8880
  | 0, 4 => 0x3ffffd4
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

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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

def dom_1 : Nat := 0xf000f
def goal_1 : Nat := 0xe0008
def roots_1 : List Nat := [0xa000a, 0xc000c, 0xf0000]

namespace S_1
def pairsG : List (Nat × Nat) := [(1, 3), (1, 17), (2, 3), (2, 18), (16, 17), (16, 18)]
def r1sG : List Nat := [1, 1, 2, 2, 16, 16]
def r2sG : List Nat := [3, 17, 3, 18, 17, 18]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x41237c2d
  | 3, 0 => 0x41237c2d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000c000c00000000000a000a
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

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
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

def dom_2 : Nat := 0xf0f0f0f0f0f0f0f
def goal_2 : Nat := 0xe0e0a080e0e0808
def roots_2 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f00, 33, 41), (0xf0f0f0f00000000, 9, 41)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xf000f0
def goal_3 : Nat := 0xe00080
def roots_3 : List Nat := [0xa000a0, 0xc000c0, 0xf00000]

namespace S_3
def pairsG : List (Nat × Nat) := [(5, 7), (5, 21), (6, 7), (6, 22), (20, 21), (20, 22)]
def r1sG : List Nat := [5, 5, 6, 6, 20, 20]
def r2sG : List Nat := [7, 21, 7, 22, 21, 22]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_3.map (· &&& dom_3)
def goalM : Nat := goal_3 &&& dom_3
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x7fe4b035
  | 3, 0 => 0x7fe4b035
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000c000c00000000000a000a0
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

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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

def dom_4 : Nat := 0xf000f000f000f0
def goal_4 : Nat := 0xe000c000e00080
def roots_4 : List Nat := [0xa000a000a000a0, 0xc000c000c000c0, 0xf0000000f00000, 0xf000f000000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_5 : Nat := 0xf0e0f0c0f0e0f080
def roots_5 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f000, 4, 12)] (by decide +kernel) (by decide +kernel) low_4

def dom_6 : Nat := 0xff00ff00ff00ff
def goal_6 : Nat := 0xee00c800ee0088
def roots_6 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_7 : Nat := 0xff00ff00ff00ff00
def goal_7 : Nat := 0xfe00fa00fe00f800
def roots_7 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_8 : Nat := 0xffffffff
def goal_8 : Nat := 0xfeeef888
def roots_8 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_8 : Lower dom_8 roots_8 goal_8 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f0, 8, 12), (0xff00ff00, 4, 12)] (by decide +kernel) (by decide +kernel) low_1

def dom_9 : Nat := 0xf0f0f0f00000000
def goal_9 : Nat := 0xe0e0a0800000000
def roots_9 : List Nat := [0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_10 : Nat := 0xffffffff00000000
def goal_10 : Nat := 0xfeeefac800000000
def roots_10 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f000000000, 34, 38)] (by decide +kernel) (by decide +kernel) low_9

def dom_11 : Nat := 0x5555555500000000
def goal_11 : Nat := 0x5444504000000000
def roots_11 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

namespace S_11
def pairsG : List (Nat × Nat) := [(34, 38), (34, 50), (36, 38), (36, 44), (40, 44), (42, 46), (42, 58), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [34, 34, 36, 36, 40, 42, 42, 48, 52, 52, 56, 56]
def r2sG : List Nat := [38, 50, 38, 44, 44, 46, 58, 50, 54, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_11.map (· &&& dom_11)
def goalM : Nat := goal_11 &&& dom_11
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_11 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_11 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_12 : Nat := 0x5555555555555555
def goal_12 : Nat := 0x5444504054445000
def roots_12 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555555500000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0x3333333333333333
def goal_13 : Nat := 0x3222320032223000
def roots_13 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_14 : Nat := 0xffffffffffffffff
def goal_14 : Nat := 0xfeeefac8feeef888
def roots_14 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_14
def pairsG : List (Nat × Nat) := [(1, 3), (1, 17), (2, 3), (2, 18), (4, 12), (5, 7), (5, 13), (5, 21), (6, 7), (6, 14), (6, 22), (6, 38), (8, 12), (9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 26), (16, 17), (16, 18), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (33, 35), (33, 41), (33, 49), (34, 35), (34, 38), (34, 50), (36, 38), (36, 44), (37, 39), (37, 45), (37, 53), (40, 41), (40, 44), (42, 43), (42, 46), (42, 58), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 2, 4, 5, 5, 5, 6, 6, 6, 6, 8, 9, 9, 9, 9, 10, 10, 10, 16, 16, 20, 20, 20, 24, 24, 24, 33, 33, 33, 34, 34, 34, 36, 36, 37, 37, 37, 40, 40, 42, 42, 42, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 17, 3, 18, 12, 7, 13, 21, 7, 14, 22, 38, 12, 11, 13, 25, 41, 11, 14, 26, 17, 18, 21, 22, 28, 25, 26, 28, 35, 41, 49, 35, 38, 50, 38, 44, 39, 45, 53, 41, 44, 43, 46, 58, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xfffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_14.map (· &&& dom_14)
def goalM : Nat := goal_14 &&& dom_14
def NN : Nat → Nat
  | 2 => 1
  | 3 => 16
  | 4 => 96
  | 5 => 264
  | 6 => 605
  | 7 => 351
  | 8 => 24
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x1889b515
  | 3, 0 => 0xed27681dc7488d62abd45232a7bf35109b87aaa2770b902071bc4fcc58dd4db253907b7a5320197d44614dc01f1b05131a49d19d19b8712b0f40e0ad02cdbec0
  | 4, 0 => 0x8e8266498da0ae968d2fcc758593e74d853a43d381a89e287fd13c127f019ca77820168d770b90206ff5f3896f81603c6f4b4fae6da674236d30271b6bbd74746b7d109e6946f882685a65e9672bf7d4667dc0fc5d28db1053e922984d6cadc94c0d1f964a7f8ea94a102a2245e856f9435ae8fe3dbb35fb3d6423283c8b3c11399fdd66382571e237cc167e371934b3316a303830b5f22c2f1460f82d0a6f1129d54f7729699acd2875e0992487ee4b2229073d21af237220804471206336c11d9a75de1d930f041d8558cd1951c300175ac4a1166dfaec160bd836134ffbfc0f68d2910ead82770e993b2d072223420699e77906196aec04433f4103931f94
  | 4, 1 => 0xff094118ee113b8bedfc5322eccfbbb7e573a32de2559978df7f99d5d7fead15d7c1c71fcf4abbb0ce4a47e0ce15bca6cd8ba78acce4eac3caeb15efc8b4fdd3c01440dabfd1eeeabd34ba74bb5f70efb5fcdd07b3743fc6b13e27aab0aae11ba5f483eba5bae604a545b28ba21cae88985f447a9840003397872a1896d1f90d
  | 5, 0 => 0x21e740f221488ce0210955be20bb269b206d0bcf1f62e3931e870bac1dec05861c795c1a1c00ccfa1bec56d41babfac91afcb9971a761be71a1f0ef61a10f6e51900d8b015dac5e9159fa3de14f6ad4b14b9509b142a76c513e54be613d1291013b1f6a9134ffbfc11fd45e311f45ea9119dfe101161181a10d2ba02108b31051052a5ff103dbd960f11262b0f0e32980e3bfb810d3fd6a00c69bfd00bcfb3fa0a1e048409d0c57e0993677c097492f708fe600308ea0cab08b5236d089ede53085416980804cae007e998db07be90f207b50da1062efed5056b49b6048e739204173ae103e95633034b623b01d9430501bbdaa700c2176000904a51000bd3c9
  | 5, 1 => 0x554b493854ea989354a03b7c53b991c651045f54500d4be74fb8aba24fab29314f7c60744e1eb31a4de5c77b4d8f3ad14d8293864cef4cf74c16b9eb4b3841354ab74b0d4a95600549abc865492a59a1489a7b7747b4abff46c958bf45d6f2724585704045696f5b4350fce642c49da24178e5d140c1743d4034903f401c1c233f9fefd43c74836f3baa073b3b932d743b2fe8e93a792f6a3a3e6b53384d42aa3628709535dd329c3591667034f0851b34d39c4534d319313471896c3280a8153240a7d031e38902318b93d1317a69f62efa4a0c2eab3f582d46cb4b2cbc6a632c22e3092a7011e829404f94279ba41d26f59e05266f0cb2232ee1702292a079
  | 5, 2 => 0x9a06172e9a0096fe9949118798bd040496a5cba5964b0e8193fd790190535a2590370fa58df130898ad3bad788d204b087396bdf85d14e808593094784a818de841edfa481408b047e4fb0497c84a63f7c306b6d7bfcc3507bc2c51c79d50c7d767c5d42762a8d0c751113a0735fedef724c264671c4c2dd71c11994713c43917086143f706d4c4970315a126fc1d9886e5a6e856c32974e6b89afb86b09813369f5f7ab699bd97e68b3b1f3687e9ce966abb3bc65102aa16374a0726308ebc863078275625a279162153194617a53415e2d8aab5e2c2c165e273f465d95877b5c6c66715a66dc565a0d80f25a09de325a0287bc597a3a6358fb42dc57137596
  | 5, 3 => 0xf6604ff8f3b38055ea85c371e5a4fccce254d007dff65054dc9a8eb0da4191acd96b098ed83e477bd7c1c71fd79c81fad68fe03ed354b39ad0d726facf3b86f7cde65e1acc7fcc61c918cab1c835ee5fc73fff91c719694ec5f93171c12f60ffbfd0a83bbed14be0bbefbf91ba816aa7ba6e1453b93d8228b83543b3b6ff990eb53b51fab4898863b3bdf196b2f8b09db19d22c1b149ef60b143fc31b065425baf527550af4ed27bae0a714fadcb99c7ad0e3d8ba9575e6ba83cd88ba7d551c1a6db69e1a51c6199a4301251a35c9dd6a101ba1ca0eb106ca01d11f79dd8e2069d128a3f9cc122649bca36779b3436919b31e9ce9aa634349a6181019a40fa0e
  | 5, 4 => 0xfe4a2c8ffe2dc330fd9810a5fd2d0a86fa401789fa033193f89a03eff6d40b6f
  | 6, 0 => 0x12ee29ce1236e74d11bbe12e119ab583119557c61161181a115a7967107b57340ff47fa50fec104b0f97753d0f115ba20ef737100edf18670ed86b730de298690dd633720d1802ee0cd9f5660cd88bf40cabde0a0c2c14070c269c8b0bbb8e270b2c8ce60ae653d70ac4d5b90aa769cf0a7677f50a75789c09bd51ef09695d400919997808072a4107f1b6d607a72649074eba940711d49e06fe79c006f72c6106e10dd6065d5685065bd6fd060f596e060e91e70608061805a9e53f0559e5f5054b0cc9053c7a0b050c65e004963a7b03abb2f00389d21f0380978b035eb4ec02d6a72e024365d60225f9ec01e3cad00198403d01652a3200f94cd0009bfdb9
  | 6, 1 => 0x1ec0fa371ebcbc8f1e4837591e2d9df31db574801d826c881d4c60a11d07cbc61c96ea491c8d62a61c53915b1c397d011c32bad41c1fc9361bf5be811bd1fa481baefe391b9ff3ad1b3b5e1c1b24771a1b16f5ed1a548add1a2639791a1f1cf019ba301a188e19d01882b1691870ade6186cfbda18545dd617b77a5217617b9e174a0ecc173c6c16173643a81734bd56172decb91701656116bc7a2616b01e54168bc85d1673385e16446b9c163cc6661611817415f4eac915ea9fee15e9498b1596d48d155ed0bb1517feab14c15aa414b84f3214adee10140c1c61140adaec13ea83c213e0e2a713d6d81d13967e2f133c08ef13346ed1130cc1b3130a5a89
  | 6, 2 => 0x2f643cf62f51808b2f3c81e32f2d39052f03b74b2ede35262ed0d2042e1a843f2dedc9542dec4b6b2de6358a2dd75a262da94f942d52d1502d06d0c22d01ecaa2cadc4612ca929c32c7dc05e2c42325c2bb5fd6b2b812cf62b08f8cc2afda44c2af8e8dd2af68de12ad3509f2aa964312a95810c2a709ff12a63475229af2b64296af49a2908d1e428e1d56328d3f68428a4a83e2842fbd32750b4f62713cf00259a3137244f823f2444ce75243e5010242f7cff240f87f823f07cfd23e658262325c90b22e55f97229998fb22880254224d3e3d219634db213dff8121144ec6210955be20b8602f206bd013204ed6c3204a722020292edb1f9547f51ee07af3
  | 6, 3 => 0x3ff0f5f13f7f6a493efd382b3ebac68e3dd0ef663db4e4813d8a3cae3d5b65d93d4e5b033d2c7c353cfaa5163cd249253cc696da3cbcf7af3c66947b3c21f90f3c21c3983c0ce04f3bf7f5823b754d643b72da473b0a44b33acf9b4b3a822ece3a4fc20639ab24c43965a15438f8f67638ed9e2f3821da66380d7bfe37f1a35037d8b58137b281a7375583a9373817bf36c5746f36b5383e36093879359740203591667035787e2634d2fbb734a771a7349995fb34926031343eb057343ac70234064f6c33df688433d25e6233a2828e3360306f33422da532fa2f953294f0e03244176031660f0b315c50af313ee4c530ba24d82fbf5da52fa7a6b32f814114
  | 6, 4 => 0x5416d04b53eb8bdb536a1507535b8ef0532529cc52e2321e5257aedf51ed22825160844350eca9cc50d485a14f9d2f8d4f3260114ebf453b4defc3b64dd3ad484dc9c7c04d43334a4d2f3d364cd5ea514c8a818c4bd15be94ba1260e4b81ba084b4dec0f4b46a3804b226b904b17beb24abd1d0b4aabf4e84a95df414a3f5f3c4a32907749dd0e91496fc9e449440b17491e4f5448c32bdf48b07726482de2cd4827cfeb47d7f35a46f1b31146df279b46bdac87463612304631106d45abfc78455be5b544d46f78446729e64408d56743e3db97434ac03242b7442c4291ffc94270b5be424acd3742115aa6419ac200418c581941320659412c1b38406a83da
  | 6, 5 => 0x6909bb466886c0b668716f40684a905367cb195767c6dab467757f61676fce60672751d8671ea51e65381a0264b153c1643609f563939f3362dfa08f62bd28d8625d8697624ac82b6240770e61f617a360fe5bb25fa001255f64e4b85f27f51b5ef0b1fa5ed6a3f15eb5ede35deb71af5da6006b5d7c88575d71535d5d0eae245ccd4b075c9b90375c97debb5c8357335c7fd5c75c5ce06b5bf13ab45bb03c075b3bed485ae1ffbf5abaaca25aa8a6b959a0c2fc599cddcb593c1d1759255cf65925466959100b80588269ee583d5a595808a35357c5ee1857a487195702a7c256488c3a5618ad1556150471556a900e54fb57fa54bd49755485444a54276788
  | 6, 6 => 0x829abebd81e62af881b726b38160c9fc8068a9ba7fa0b5d97f78c21c7f24c13b7f05801f7eba6e227e7a0a4c7be8a3717a8392537a399f0c7a36543c7a05242f79d3e13a79bb6d1e797abaaa79684f627961f72778bb1eaa77e8b9bb77abf41377728e4a76e1a5f076d6e321763744917616152c7613d46a75404ca07522e0b674cf39e47481ccfa74789e647407475673fa28f273bb0159739c3b757376421073627f61730cc97a7301de5f729573027288949c727718da7236e26571fa161671ec93a571ca317b718aa31d7108872f709d46b9708b912d6fc3fdfa6f6a8dfb6f30b76b6ec7a3626e7acf386cd6ca796bd3e8686a95be0b6a80e84b69846ed5
  | 6, 7 => 0xa828f69ba7853e24a72fdc37a6e98352a63809e4a55beef2a4b188daa43fb431a3d87e06a2c3c9dfa27f4475a21dede4a195b11ca0bf06469ec9ae489e5fc6b79e3e2dc49d235cf89be41d5a9bca9a899b56d6249ab91a009a18a88398ff116697a0022597885ff9972d561a96a47b2f96a2e0f99551aacc94e8477894062d5193458eb19345446093104a2b92d649fa92bb0e58923130829086da4d90623c408f09a0718e3f8c778da068838d54788b8b4da15b8aa3b04f8a81f0ca897c1ede88e36b1588e0387f88cd013b88118a828742e14786465a8a85d48fa385b60ae684569c088436e17f83c0be098323215e82cfc52182c96d8a829ec1d6829acdbb
  | 6, 8 => 0xdec9dac1de9d2c44de99cc50de312a05dcaf7ec7dc8a5345dc07fe40db7eec9cdaa10b17d9bf06ebd8af4f05d79dcf25d7783301d5e44738d445852fd390a498d1ffa714d1296545d031b422cd919533cd827617cccaebe6cc1a159bcc12eeb2cb18ca29cabb86a9c9db535dc8e9878fc6ca6586c4a4bbb4c453a13bc3d820fcc3ab1db0c3432490c1ebf1e0c0e08b57c0d8bcdac0548805c01a4c7abf662c09be20deedbe129a87bdee9ca0bcbbca35bc545819b8a185a6b84d5911b764087ab63ee375b413339bb3e6f422b285abbdb217ac16b0d5dbb4af616e2bad58a5d0acff3eeaacd35171ac5aad7aabcd69f1a97aa236a94c64a9a8f0d2eda84782ef
  | 6, 9 => 0xff98826cfc82fc20fa574c46f89a03eff58f108cf31deba9f318916ef25e1f0feebe9aeaee5455feec164c1eebefca4beba28a2aeafba6c3eacd69c9eabec0cdea76cc8aea326695e9e8d9b8e93c0117e5e351dce56c6f69e413fd8ee2f6af66e247b55ee147418edff821dddff3a4ccdecd4938
  | 7, 0 => 0x204aaf2d203cd04e20292edb2014c6441e739d441e3d0e221d989e101d81c57f1c1ffead1b78d4bc1b70b1901b325a461a0ece701a0dc40d19b1d448196672e11900f429181aa94117d07b00175a929b16e8db1816b50ee915f022ce141a4f1c1415063f13b5da6d131bfefa1308cd7712b8884a11d748061198114410d1aa960faa77070f8b2a5f0f8898390f5c5cfb0e8414b20e7e15130e7ddf9c0e7dd0190dfe576f0dfb96ef0d61f2fb0d4d98860cc7aa850cabde0a0c867e660c22507d0b41c7720acf09dd09ee1b6f0878675807af559e06b07a0306291d8305c61dd6040745c6036df150023f103c01a603fb0198251c00f5a3d20086a50c00273479
  | 7, 1 => 0x3c3d49423c38e0113c21f90f3be08ad93acd3e823a8b9b213a476634396f572d39500340387c221637b9fc1b375fd1e83732d33a36e4026d363c57f436224d1b359aee6d354bc4fd34746a9f342cdee934064f6c32ba82ac3264f19432176901315024ba3129ad3f30ccd1eb302ca7772fc976f62f7655c82f1d68d52de85b922d90db782d6df75a2cb7e2692c9946a22baacaed2b81626d2acd7a982a7c85282a6cf07129e942c4291abe5628a4a83e2774c460275958f2272770732705880d26beaf6f26bb2fef26a4b5bf26488ebe261c309d260932412429651523afce9223a7fde62310763b23038dd422d85c9a2219ec0a21e9d24d20df43cc2081cc61
  | 7, 2 => 0x5bec8f385b2acd595aa8a6b959d395c758905d135806ebe25640306856240dff55f35c3e5550dd6c54b47b985423f49e53b7a8b5531915d15314eaf6530ec13f528ca242523dc21151099cc650c4b4ed505beeb3500139404fb2394c4f943bc44f717d1d4f5ddbaa4f0fba7a4e2ce2974e00c0ea4bff26be4bf147df4bb8974e4b83735c4b6e21e64b0c2c394b02825d4ac0774d4a6707154a3f78dc4a24047e499b08ca49148db048b0ac9d46e149a24609964844cd758b43a9f848434ac0324305883642815d8a4214fad141d622d341a8390640ccbe134079af63405c8f3d3f49363a3e1c8eb63dff89d03d6d0b963cd7d7c23c9dc2fe3c9d75a23c8fe41f
  | 7, 3 => 0x85210b0383f048fb833df90381102355806266ad804281917ecd8d627e8559377d7d57bc7d356db97cea112d7bc86ac17ab597257ab2c9087aa157477a85129f79e15a2879a4d76c785a178978493a7f77f10ba276db0b2e76b015da766385db75d42690745a681c73a1eeb7727daf3d7260e48f70cdf0746f6c29a26f69601f6e38e6f66db8095f6cd622c66c4b6e046be1bd3a6bcb63fb6b89f08a6b58c0516a510b386a0139de69c0add4697c13036920920f67f1c0d3679d352a67339425651506a4645092fc6401590263353df46284e04361aa33686129ea2960b58bf55f5d13a95dc82fa15d1e66bc5d1d08615cde0cce5c9fbd605c91de815bff541c
  | 7, 4 => 0xbf01fb40bca06181bc545819bc18011ab9fc935bb96ec08eb7a1fd24b59a84ddb559ed2fb4d0d4a4b3feb3cab253eee6b0ec7e1fb080f6ebaf95e2ffaee65ee3ada32de2abbe6e52aab0e49aa98c5b5da77ce252a661d0dfa5e4c2a9a494c22fa1b25c0ca16c4690a1662baf9e58572e9d61744b9c27c3cd9bfcd7929b71391a9aec1f2b9a36658d99ed5e8799d7582f997d4564992721c298553ede97a5128c96fad25696a4b77d94b8834e944ede00936159ab9351acbb92b08ece928cbda591b98d129117715e90061e318e7679718e35cdb08e2374cd8d7f04bb8d6fdaea8d3d413a8ce77a638b8fda438a8bfac78a81f0ca8934bc8a87cdddd0877910e2
  | 7, 5 => 0xfd058035fce2758bfc3e0176faa130d0f9b99d75f9acd0faf96feb04f4642245f32a1730f2854adfef0e3eb4ec164c1eeabec0cde8b03ee3e7a75556e3d420a8e2f02cffdfb32b5bde1b0bb2d988b69cd8f62b1fd697c1d4d630e845d4e47617ceecb93fcbfcbae9cae6d7d7c8d8951dc52f7576c21dcfbbbf8705eb
  | 8, 0 => 0xf2854adfdd9de376c2afde01a6563cc38a7994f87cea112d764e5f6161ca40085fbac6fd5e22a7545cde0cce5059633d4aee737942b779a33e277fff34064f6c2efbd9642eedfa8521b9f7ae1b78d4bc1729918f1561a43a0e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33ff000033ff0000333300003333000011110000111100000fff00000fff00000fff0000000000000f0f0000ffff00000000ffffffff000000000000ffff
  | 0, 1 => 0x330033333333330000ffff0000ffff0000eeee0000eeee00007777000077770000777700000000000055ff000055ff000055550000ffff0000555500005555
  | 0, 2 => 0x1133113311331133111111115555555511111111111111110f0f0f0f0f0f0f0f05550555055505550333033303330333030303033333333300ff00ff00ff00ff
  | 0, 3 => 0x33333333000000003333330033333300333330303333303033223322332233223300330033003300303030303030303022222222222222221313131313131313
  | 0, 4 => 0x55505550555055505544554455445544505050505050505044444444444444443333333333333333333333333300330033333333303030303333333322222222
  | 0, 5 => 0x777777777777777777777777777700006666666666666666555555555555ffff5555555555555555555555555555000055555555000000005555444455554444
  | 0, 6 => 0xaa88aa88aa88aa88aa00aa00aa00aa00a8a8a8a8a8a8a8a8a888a888a888a888a0a0a0a0a0a0a0a0999999999999999988888888888888888888888888880000
  | 0, 7 => 0xaaaaaaaaa0a0a0a0aaaaaaaa88888888aaaaaaaa00000000aaaaaa88aaaaaa88aaaaaa00aaaaaa00aaaaa0a0aaaaa0a0aaaaa000aaaaa000aaaa8888aaaa8888
  | 0, 8 => 0xc8c8c8c8c8c8c8c8c888c888c888c888c0c0c0c0c0c0c0c0bbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888aaaaaaaaaaaa0000aaaaaaaaaa00aa00
  | 0, 9 => 0xcccccccc88888888cccccccc00000000ccccc0c0ccccc0c0ccccc000ccccc000cccc8888cccc8888ccc0ccc0ccc0ccc0cc88cc88cc88cc88cc00cc00cc00cc00
  | 0, 10 => 0xeac0eac0eac0eac0e0e0e0e0e0e0e0e0ddddddddddddddddccccddddccccddddcccccccccccccccccccccccccccc8888cccccccccccc0000cccccccccc00cc00
  | 0, 11 => 0xee00ee00ee00ee00ececececececececececececa0a0a0a0eca0eca0eca0eca0eaeaeaeaeaeaeaeaeaeaeaeaeaea0000eaeaeaeac0c0c0c0eaeaeaea00000000
  | 0, 12 => 0xeeee8888eeee8888eeee0000eeee0000eeeaeeeaeeeaeeeaeee0eee0eee0eee0eecceecceecceecceecceeccaa00aa00eeaaeeaaeeaaeeaaeeaaeeaacc00cc00
  | 0, 13 => 0xeeeeeeee88888888eeeeeeee00000000eeeeeecceeeeeecceeeeeeaaeeeeeeaaeeeeeccceeeeeccceeeeeaaaeeeeeaaaeeeee0e0eeeee0e0eeeee000eeeee000
  | 0, 14 => 0xeeeeeeeeeeaaeeaaeeeeeeeeee00ee00eeeeeeeee000e000eeeeeeeecccccccceeeeeeeecccc0000eeeeeeeecc00cc00eeeeeeeeaaaaaaaaeeeeeeeea0a0a0a0
  | 0, 15 => 0xf0c0f0c0f0c0f0c0f000f000f000f000eeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeeeeeeeeeeaaaaeeeeeeeeeeee8888eeeeeeeeeeee0000eeeeeeeeeecceecc
  | 1, 0 => 0xf300f300f300f300f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f000f000f0f0f0f000000000f0f0c0c0f0f0c0c0f0f08080f0f08080f0e0f0e0f0e0f0e0
  | 1, 1 => 0xf8f8f8f8f8f8f8f8f8f8f8f8f888f888f8f8f8f8f800f800f8f8f8f888888888f8c8f8c8f8c8f8c8f888f888f888f888f555f555f555f555f3f3f3f3f3f3f3f3
  | 1, 2 => 0xfaf0faf0aa00aa00fac8fac8fac8fac8fac8fac8fac8f000fac8fac8f0c0f0c0faaafaaafaaafaaafaaafaaaf000f000faaafa00faaafa00fa00fa00fa00fa00
  | 1, 3 => 0xfafafafafafa0000fafafafafa00fa00fafafafaf0f0f0f0fafafafaaaaaaaaafafafafaaaaa0000fafafafa88888888fafafafa00000000fafafa00fafafa00
  | 1, 4 => 0xfcccfcccfcccfcccfcccfcccf000f000fcccfccc00000000fcccf0c0fcccf0c0fca8fca8fca8fca8fafafafafafafafafafafafafafaf0f0fafafafafafaf000
  | 1, 5 => 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfc0000fcfcfcfcfc00fc00fcfcfcfca8a8a8a8fcfcfc00fcfcfc00fcfcf8f8fcfcf8f8fcfca8a8fcfca8a8fcf0fcf0cc00cc00
  | 1, 6 => 0xfefefefe00000000fefef8f8fefef8f8fefafefacc00cc00feeefeeefeeefeeefeeefeeef000f000feeefeee00000000feccfeccfa00fa00fe00fe00fe00fe00
  | 1, 7 => 0xff00ff00ff000000ff00ff00f000f000ff00ff0000000000ff00fa00ff00fa00ff00cc00ff00cc00ff00aa00ff00aa00ff008800ff008800fefefefefefefefe
  | 1, 8 => 0xffa0ffa0a0a0a0a0ff88ff88ff88ff88ff88ff88f888f888ff88ff8888888888ff55ff55ff55ff55ff55ff5500000000ff33ff33ff33ff33ff00ff00ff00ff00
  | 1, 9 => 0xffccff88ffccff88ffccaa88ffccaa88ffc0ffc0c0c0c0c0ffaaffaaffaaffaaffaaffaaffaaaaaaffaaffaaffaa0000ffaaffaaf0a0f0a0ffaaffaaaaaaaaaa
  | 1, 10 => 0xffccffccffcc0000ffccffccff00ff00ffccffccf0c0f0c0ffccffccf000f000ffccffccccccccccffccffccaa88aa88ffccffcca080a080ffccffcc00000000
  | 1, 11 => 0xfff0fff000000000fff0aaa0fff0aaa0ffeeffeeffeeffeeffeeffeeeeeeeeeeffeeff88ffeeff88ffccffccffccffccffccffccffccff00ffccffccffcccccc
  | 1, 12 => 0xffff1111ffff1111ffff0000ffffffffffff0000ffff0000fff8fff888888888fff0fff0fff0fff0fff0fff0fff00000fff0fff0ccc0ccc0fff0fff088808880
  | 1, 13 => 0xffffa8a8ffffa8a8ffffa0a0ffffa0a0ffff9999ffff9999ffff8888ffff8888ffff888800000000ffff5555ffff5555ffff3333ffff3333ffff2222ffff2222
  | 1, 14 => 0xffffaaaaffffaaaaffffaaaaffffa0a0ffffaaaaffff0000ffffaaaacccc8888ffffaaaa00000000ffffaaa0ffffaaa0ffffaa88ffffaa88ffffaa00ffffaa00
  | 1, 15 => 0xffffccccffff8888ffffccccffff0000ffffccccff00cc00ffffccccf0f0c0c0ffffcccc00000000ffffcc00ffffcc00ffffc888ffffc888ffffc0c0ffffc0c0
  | 2, 0 => 0xffffeeeeffffccccffffeeeeffff8888ffffeeeeffff0000ffffeeee00000000ffffeeccffffeeccffffececffffececffffccccffffccccffffccccffffc0c0
  | 2, 1 => 0xfffff888fffff888fffff0f0fffff0f0fffff0f0ffff0000fffff0f0ff00f000fffff0f0aaaaa0a0fffff000fffff000fffff00000000000ffffeeeeffffeeee
  | 2, 2 => 0xffffff00ffff0000ffffff00f0f0f000ffffff00aaaaaa00fffffcfcffffccccfffffcccfffffcccfffffafaffff0000fffffaaafffffaaafffff8f8fffff8f8
  | 2, 3 => 0xffffffff00000000fffffff0ffff0000ffffffccffffffccffffffccffffccccffffffccffff0000ffffffcc00000000ffffffaaffffffaaffffff00ffffff00
  | 2, 4 => 0xffffffffaaaaaaaaffffffffaaaaa000ffffffffaaaa8888ffffffffa0a0a0a0ffffffff88888888ffffffff55005500ffffffff33333333ffffffff11111111
  | 2, 5 => 0xfffffffff0f0f0f0fffffffff0f08080fffffffff000f000ffffffffeeeeeeeeffffffffeeee8888ffffffffccccccccffffffffcc00cc00ffffffffc888c888
  | 2, 6 => 0xffffffffffffa0a0ffffffffffff8888ffffffffffff1111ffffffffffff0000ffffffffff00ff00ffffffffff00cc00fffffffffcccfcccfffffffffaaafaaa
  | 2, 7 => 0xfffffffffffff000ffffffffffffcccc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x36d6c6e3
  | 3, 0, 0 => 0x72b7d147d472b191e7947637cfc7d46323cdc664763011e7a4763010c7a4602d8dc674833010c674763011e7948fb6d6c7d460218de67460218f4674762f5087d475b010c7a472a54a643463218dc674
  | 4, 0, 0 => 0x72b690c7221ab958a832990d5cabd4694c86b1f72b8d147d595b010c7d33acb1d8c0431b963eec601fcfab36763010c7d572b7d145321ac7db6863e99d63eec6ea18beb1f76301688658535d0c5321ac498086298e163eec602d8faae560274f6535
  | 4, 0, 1 => 0x60218dc6729accdd8bd431f566cec6023cfab1f72b315e5758fbb180803eac7e14962990d400ec60218f28e56a288a64357634180863eac15d8c0431f55d8df60218fab34763011e7d5763010c7a29ab9592c04e14d6370e3f14c86aec60218fa795
  | 4, 0, 2 => 0x8fbb180863cabb180863c8c55d8c0431f4f4ae56d2d50c435763016e863eac7df2c05a2195cabd421f462b0a60280a6435763190c7d372cd1d8c0431e5654e558a1886b2360218fa67596b952c5321ac7ddac0431f563ec6431f4ceaec5ea10a6435
  | 4, 0, 3 => 0x3010c6e33a3b180863e9bd5cac0479e462b2e763010c7d5763010c6e33ab95c87e2990d580863e9b8ceb36763010c7b58fc4180813ea801d8c0431e91cac6479f4dcb1f89b010c6a595bb180863eab011e6e330c55d8e560218f4b34763010c7b5
  | 4, 0, 4 => 0x72b650c7c21ab9588842990d5d8c04314482b3660218fa6759b3ad80863eac7dd8c0431e95d8c0431e862ae560218f4315763010c7d05acd9d8c0431e95cae03f14c86b06763010c7d5763010c52212cd1cac6479f55d8c0431e486ae56ca84a6435
  | 4, 0, 5 => 0x60218de6618ac7e1ec0431f565aec60218fab1f762f90c7d572b7cfc7d18ac7d8c8f3e9995cad3421f486b1f7638cfc7d5763010c7d372c81d8c0431f5608ec60218faaec6f9f8a64358fb95b4a22e2b95809d3e93d63ec0431b8ceac0431b8ce315
  | 5, 0, 0 => 0x8fbb180b9431f5a3f0a60218d64368239580863e8c5800e55ea10a62b572b7cfc53218c59cac04d218a64369a3e180af2990da54e5482189c4368fb9580a74590da3ee549a18a63768fb010c7d338c5a3ee560234a643672b7cfc53218ad9cac64ca18a643691b010c7d330c580134763010c7d5
  | 5, 0, 1 => 0x8fc3d80862990da5aec60218a64368fbb17c862990da68e560218f83168fbe580934314da3eec60218fa01672af53c862990d9cac0431d0a0436863957a862990d9cac0401b8a643698b9580a54310da6cec72b010c7d672b0142532890da40e560218fa3168fbb180863e8319cac0431d09e436
  | 5, 0, 2 => 0x8fb9580a42990da3ee558158a643672b010c7129905a3f0a60218fa31672af508532188da3eec60218fa6e600479ca7e2990d5cac0431e4a63167bb957c832990d80136763010c7d50047d80863e8315d8c0431f4dc3168fb95c67e3e8c59cac0431f4dc31696b95b4a22990da3ee760218fa316
  | 5, 0, 3 => 0x72b8180862990da3ee56d218c04360047dd8c0431f563ee560238a64368fb9580b82b0c59cac04e94ca24360047e310e5390d5cac0479b8a643699c7dd8c0431f5a3ee5602d10c4669239580a23e94d9ca90431b8a643672b016a862990d9cad64314c863e672b015e6e2290da40c043198a6436
  | 5, 0, 4 => 0x72b010c7c2890d9cada431b8904368fb010c7d3390da4ee5719f8a63d67ab9580842990da3f01763010c7d672af5087d2990d9eee56f9f8a64368fb95b4862e10da3eec60218fa56693c7dd8c0431f5a5ae560218fa31672b4580862990da3ee55f218fa31600395a8862990d63ee558a18a6436
  | 5, 0, 5 => 0x72b010c6e298e1a691f763010c7d68fbb1cac0479f5a3ee571a28a64360047dd8c03e851580863e9b8cc3169a3b180863e8c5a3eec601fca6436823958086298e19cac0479f4dc3169b3b180862990da4ee56029d0c3d672b4d80862790da4f0a60218a63d691b9580934314da1ce5681f8a6436
  | 5, 0, 6 => 0x7637d80862990d9cac0431f49c3e68fb95808b2990d800c0431b8cc31599b95a6af4310da3ee5662bc8a3669a3b1808f2990da52e56d2bd0c4360047dd8c0479f55cad060288a633693b9580862c94da3ee5709f8a64368fc621c932990da3ee5602d10c316763010c7d3710da3eec663010c7d6
  | 5, 0, 7 => 0x9439580934314da3f1160218a63968fbb1c6c0431f5a66e55ea88a63369647dd8c0431f5a58e560218dc3169b47dd8c0431f5a3ee5601fcfa3168fb9580863e8c9a5ee56620ca636680bdd80863e9b9a68f160218a64369b3b180863e8c5a6ce560218fa3167634180862990d9cada4c9f8a6436
  | 5, 0, 8 => 0x72b0136862990da3ee56b288a633672b7d80863e8c5a66e566a18a64360047dcac0430c963ee566218ae5369a395808f3e8c5800e55f270a64358fbb1b4c0431f5a66ec5ea18a64369b3b1808f2990da3f0e72b692653672b010c7d3c8c5a6ce56023ca6436002f508532183966cec60218a4436
  | 5, 0, 9 => 0x72af55a862990da311260218a643672af50853218ad9cac04f9f8a643672b0126863714d9cad0602bc8a4368db950c7e2990da3ee560200fa3168fb9526914314d800e55ea10862350039580863c8c5668ec60218fa4367db958086299099cad360218a243672b4180863e8c5a0ae560218fa316
  | 5, 0, 10 => 0x9a39580863c8c5a54e56b218fa43699b957a8f2990d9cac059a18a64368fb0100662990da3f10763010c7d69b3b180863e90da470a60218a643691b95c67e2990d9cabd4214c863168fb95b4a2240cda68ec60218a641672b590c53218fda66e55ea18fa3168fb958c8f431f5a54e5602990c436
  | 5, 0, 11 => 0x72b010c702990d9cac0431f09c43600395be7e298ad636f760218a64367a39580862710da730960218a643691bb1cac0431f59cabe431c4a64368fb958ec05114da68e56d24d0c5368fb010c682990d9cad860218a24368fbb180b8431f59cac0431f4dc3868fb010c6e330c5a3f0e763010c7d6
  | 5, 0, 12 => 0x9039d80862990da3ee560218f231672b010c53218b98011f72b010c2d58fbb180863f1f5a5ee560230a643672b016e863e8c580123763010c7d59342980862990da4ee548218a63d697b95809c3e94da4ee5602bc8a3d67bb957a842990da3eec60218fa1568fc4180812990da3ee5601fc96436
  | 5, 0, 13 => 0x9cc29b4862990da46e5601fca6436853010c6e2990da4ee56d218903d660218dc66218c59cac0431cca6436602dd0c662990d9cae33f1b8a643673b010c6e2990d9cac0431bca643672b4180862590d9cac05924d0c53672b010c5a2990d8011f763010c1558fb011e7d330c5a5cec60218a6436
  | 5, 0, 14 => 0x7639580863e9b9a54e56b2bd0c4360047d80863e99d5d8c04314c860b672b010c7d378c5a3ee560250a64368fc21d8c0431f5800e5711f8a64358fbb180863e99d9cadf3f1f4a64368fbb18086419f5a68e56323ca64368fbb1d6c0431f58011f72b191e7d58fbb180934314da52e560288a6336
  | 5, 0, 15 => 0x8fb952c7e2990da3eec60218fa1460037cfc532183963ee549a18a63b68fb95808a431f5a3ee53f190a64369a395c47e2990da471f763010c7d68fbb18cc0431f5a6ceb60218a6436003b180863e9b9668e760218a6436853010c532180da690a6d218a6436003b180863e80566ae760218a6436
  | 5, 1, 0 => 0x72b9180862990da3f0a6d288a64368fb95c47e2990d9cac0431d4a64368fbb1c67e2990d9d8c0431b8a64368fb9d80862990d9cac04314482316
  | 6, 0, 0 => 0x9a395b4862992086f278fc2980862990dc00e54314c861000347dcac045218a64378fbfdcac04314c86f1f72b010c532183dc011f72b00fe5315b47dcac05ea3ca643772b010c6e2b14c86f1f89b9580a74310de3f13853010c5321bc9e3ee5719f8a64378fbe1eec04314c86f2a72b3180862710de5ae560218fa5321bcd1cac057218a6437
  | 6, 0, 1 => 0x47ca6430a0401cd2772b4d80862990de3ee560218a85321b80268e56014c561468fc05cae33f14c86f0172b010c6e2990dc011f72b014ea221b0025ae56d218a64360047e14c05114c86d1f72b2980862990de68e560218a64a21bc7dcac0431f4be3178fbd1cac04314c86e009a3959886298d9a3eec602890c5321bc9e3ee56029d0c437
  | 6, 0, 2 => 0x8fc55cac04314c86f1f72b010c5321809dcac05fa190a5321bc7dcadc60218a64370039580532185002d1f72b00fe53218f5e551f72b014e8621bc7dcac053a950c4378fc61cac0431f462f1f72b010c5321899e3f0172b014e8621bc7e150160218a64370039580863e8c402c0099b95809d2990d8012772a18a63d08347dcac0431f0a6437
  | 6, 0, 3 => 0x4bdcac04e14c86d1f72b010c5321825e68e560218a643163c7dcac0421f4a64378fc51cac04314c86e0072b010c7d370c5a3efa72b690c5321bc7dcac03f94c862379a39596c04314c86f1f72b01445319841e3ee5602710c7d29b8023eec60218a62b68fb950c7e2990c6ef1f72b010c5321889e3f0072b010c5321bb95a0c051218a6437
  | 6, 0, 4 => 0x94b9580862990c66f1f72b0144531988de691f72b8cfc5321b801ca904314c860168fb95808c4314c86f1f8c3954e862990dc013472b01425321b47deee5602a8a64378fc61cac05791486f238fb9580863e8c5d80863e9b8cc5321b801cac03714c861468fb959886298d802e0072b015e4521805a350172b010c5321bc7dcac660218fa317
  | 6, 0, 5 => 0x395a0c04314c56c0093b95809d2990da3ec043198be5321b8023ee560274a62b60047dd8e560218fac0072b011e53218058013472b00fe5321b0023ee33f14c860e69539580862710c56e0060218dc5321839a3ee56f3010c5321bc7deee563218a64378fb95b4864192086f1f763010c5321851c00e56fb010c5315b4a9cae3602189c437
  | 6, 0, 6 => 0x39532862990c20c009a39580a2298cda68e569b010c5321b80268e560218562368fb9580a94314c86f2f8c39580832990dc011f6029d0c4307347dcac05a218a64370047dca431185020d348fb9580a74310ddcacc60218dc5321bcd23f0a60218a643700491ca862990c20d1f72b310c7d298d9e3f1872b011e5321bc7dcada49a18a6437
  | 6, 0, 7 => 0x91bddcac04314c86f1f72b013a5321841e70fb72b010c5321bb95a0c04314c8614795395b4c04313886f1f8139580862990de5b0172b010c5321bc7dcac051218fa3170047d0c43118401cd1f7c39580af2990de52f772b010c5321b8023ee560a18861b699b957aa24314c86f1f80b957c862990de3f017bb010c4b21bc7dd0e560218a6437
  | 6, 0, 8 => 0x91c39cac04314c86ee56fb010c532188dc00e672a18a643083001808637198a6436004d1d8c04314c86d1f72b750c5f2990de3ee560218a6430b3c89cac04314c862b7000023eec60218fab298739580862990de471f72b011e5321bcca02e560218a64378fbb1808f4314c86e0072b010c4311805a3ee5633011e5321bca9cac057a189c437
  | 6, 0, 9 => 0x9639580863714c86f1f72b00fe7d2990de3ee560288a64819bc7dcac05114c660170047dcac0298ac28d1f8b39580862990dc011f72b8cfc4311b001cac0431b886236004cdcabd4314c56d1f7bb959e862990ddcad060218a64311bc7dcac0431b4a64378fb95809d2990c46e008fc61ca934314da3ee5601fca64300bc7dcac051a18a6437
  | 6, 0, 10 => 0x4b580862990c1cd2580b9580862990de66e55ea18a6430a3c7dcac04314c862779b3b1cac04314c86e008faf90c5321839a4f1872b010c531ebc7dcacc4318ca643700395b4862410c02d1f763010c5321831e3ee56b2890c5321b8023f0a60218862368fbb180b94314c86e009a395809d2990da3ee560218a6430638018053218501c016
  | 6, 0, 11 => 0x8fb9580a74310c24e0072b098086298ada4f1f72b310c531b38023ee5602bc8a2b69a39580863194c86f1f60218fa66298c5e3ee564301448629b8023ee560218fa4b68fc05cac04214c86f1f72b01447d298cde3ee5719f8a64315bc7e10e560218a638772b010c6e2990c56f1f72b010c7d18851dcae360218dc5321bc7dcac04ba18a6437
  | 6, 0, 12 => 0x8fb9580863e94c86f1f72b8cfc53218c5c012372b190c5321b39580863714c8631772b010c7d3c94c86f348fbc180862990dc011f72b011e5315b4cdcabd4314c862378fb9580863614c86f1f8cb9574862990de3ee56029d0c4315bc7e14c04314c862b70047dca904314c56d1f72b01268629939c011b72b010c5321b47dd8c04314c86017
  | 6, 0, 13 => 0x8fb9580af2290c7af1f72b013a532410de3ee56029d0c4318bc7e14c04314c863178fb9580924314c86f1f72b015e4521841e551f72b310c531b38025ee56020ca62b6004d9d8c04314c86c0090b9580862187d9cada60218dc5321bc7e02e566218a63678fbb180863e94c86f1f81b9580862990dc011f60218a6430630023ee56b218a62b6
  | 6, 0, 14 => 0x47dcabe4310c46d1f72b010c5321881c000072af5085321ac7dcac04314c8613772b7d80863e94c86f1f72b2580862990de54e5602189c4319bc7dcac04794c861070039580431185002c009a39580863e8c5a3ee548218a6431ebc7e30e5511f8a64378fb9580862990c22f2f8fb958c862990de671f72b01445319bb9580862993886417
  | 6, 0, 15 => 0x93c7dcac03f94c86f2372b010c7e2990de68e56c3010c5321bcce3eec60218a643700395c4c04314c86d1f72a410c532188de3ee56d2890c4821bc7dcacc602710c537004b5cac04310c46c0060218862307005a30e5602650c5321bb95a0c0431f4a64378fb9580862990c42f1f72b013a7d2990de0ae560218fa5321b8023ee56021856236
  | 6, 1, 0 => 0x8fc05cac03f94c86f278fb9580a2298cde3ee560200fa5321b8023ecc4314c6c0e696b9580862990c56e008fbb180862990da3ee55f218a64315bcbdcac04194c862379a47dcacc4314c6cf1f80bdd80863e94dc00e560218f25321b001cac04314c56006953ddcac04313886ee560218dc532290dc011f72b30a6360a347dcac04314c861d7
  | 6, 1, 1 => 0x3957c862993886d2d72b010c53218c5e3ee560218a643053c7dcac054218a64378fc61dcc04314c86f3472b010c5e2990de3ee55f218a64318bc7e30f560218a64378fc71cac04314c86f1f89b9580862990dc011f72b690c4815b47dcac0431f4620179547dcac03f94c86e009a395808f2990da3f177bb010c5321bcbdcac0431c4a6437
  | 6, 1, 2 => 0x8fb9580863e9b862f0172b010c7d3710de4ee560218a63d0a3ccdeae560218a64378fb9580863294c86f1f83b9580862990de551f72b01445319bc9e3eec60218a64379a39580862990c6af1f72b014486298e1e66e55ea18fa5321b8020ae560218a64368fb9580862990c2ef1f72b0156862990de3f17873010c5321bc7e02e560288a6337
  | 6, 1, 3 => 0x9539580862710c6ce0072b01327e2990da3ee56023ca64300bc7e1ce56029ca64379a47dcac03f94c86f1f8c3e180862990de3ee5602b10c5321bb9580863714c863378fbb1cac0431f462f1f80bb180862990de3f0a60218a64c21bc7dcada43120863d7823ddcac04314c86e0091b950c53218418011f72b01084311b49dcac04314c7a107
  | 6, 1, 4 => 0x47d80861588c1cd1f80b95809d2990de3ee56023cfa5321b801cac04ca18a62b69a47dcac05114c66f0172b7d80862990de3ee560218ec5321bc7dcac0431e0a64370047dcac01588c28d338fb9580863e8c5e5ee56020ca64821bcc23ee56024d0c53700491cac04314c56c008fb00fe5321839a3ee560210a64315bc7dece560218a6437
  | 6, 1, 5 => 0x8fc2980862990c08f1f72b010c772990de3ee560218c85321bc91cac04314c861079a3b180862990c62f1f7bb9580a74310de3ee560218fa531bbc7dcacc60288a63370047dd8c0431f462d1f72b0144863894ddcac04320ca64320b8023ee560218fa3160047d80a2298cc1cd277ab9580862990de68e5713010c5321bc05cad060218a6437
  | 6, 1, 6 => 0x8fbb198c04314c86f2a72b010c7e2710de68e560218a6430cbc91cac04314c862378fb95a4c04314c86ee5602e10c6e2990de68e560218a64421b801cce560218a62b68fb010c6e3314c86f338fb9580af2290de691f763010c5321bc7dd8e56023ca643793c7dcac04316ca6f3472b010c792990dc011f76300a6430a3439cac0431b8a6437
  | 6, 1, 7 => 0x8fb9580863e93c86e00683010c53218398011f60274a64307347e02e560218fa3178fc05cac04314c78e008fbb1808f2990da670172af50c5321b801cac049a18a60160037d80862990c1cc008fb958088218699cac04ca18a64311bc7de2e560218a64378fb9580862990c3cf1f72b315e86298d9e4f1f72b010c7d18b8023f0e72b0126536
  | 6, 1, 8 => 0x8fb95807f2990c62f1f72b8cfc532710dc012a72a189c4308347e02e5602bc8a4379a39580862990c60e008fb950e862188da6cec60218a64318bc9e3ee56023ca64379b39580862990c62f1f72b310c53228d9e68e566218a6431b3b95808629938863e793b9580863e94c7af2072b010c5321855e3ee5663013a5321b80268e56010c46146
  | 6, 1, 9 => 0x47dcac03e8c428d1f72b3180862d94de3ef772b010c6129bcaa1ae560218a6437004cdcabd2990c28d3472b010c53218bde3ee560288bc5321bc7dcac043188a64378fb9580862990c50ee560218dc5321855e3ee5602590c5321bc7e02e548218a64378fc05cac0431d086e008fb9580863e8bda3ee760218a6430abcda3eec60218a6437
  | 6, 1, 10 => 0x72b010c7d3710c62f1f72b3180863e8c5dcac05ba18fa5321bb9580863f1b8a64378fb958ca24314c86ee5602650c532410de46e5633010c5321b8023ec0431f4620e697c05cac04194c86f1f7638d80862990dc01335ea18a6430734aa3ee56023ca64378fc05cad64314c86f348fb9580863e8c5e3ee56029d0c4e21bc7e14c04314c9c437
  | 6, 1, 11 => 0x47dcad62990c28d2372b0144862990de3efc72b010c5321b80268f860218a64369a395808f2990c62f1f7639580863e90de52e5602890c5321b8023ee56023cfa3168fbf9eec04314c86f3472b010c7b2990de3ee560218f25321bcdddce560218a64379239580863e94c86f1f72b8980862990de3ee560218fa531c3c7deee560218a6197
  | 6, 1, 12 => 0x97b9598c04194c86e0094b958086298ada3f0172b690c4821bb95a0c057a18a64379a39580a74314c86f1f72b31808f2990de3f0a84b010c5321bb95a0c04314c8631772b7d80862990c62e008fb011e53218398011f60218fa6618b47df4f760218a64378fc2dcac04314c86e008fb958c86298ada691f72b011e5321bb9580bd4314c9e437
  | 6, 1, 13 => 0x72b4180862991486f1f72b010c5d2990dc012472b01445321b4aa30e5602189c4378fbc9cac04314c86f2372b010c5321851c011e72b010c5321b001cad760218a64368fb9580b449a18a6f1f72b8d80863e8c5e3f1d72aed0c5321bc7deee560218fa4b70048dcac04314c56d2c8fb9580863e8c5c011f72b0086230a30023eec60218fa436
  | 6, 1, 14 => 0x8fc41d8c04314c86f3472b010c53218a9c00e52990c281000b4b23ec043198a64379a39580862990c2af3472b3180a24314de02e5602650c5321bcd1cada431f8a64378fb9580af2290c56e0093b010c531e8398011f80bdd80863eb00268e56024d0c5368fbf5cac04314c86e008fb95b44821851a110472b010c5321bccdcabd4314c86317
  | 6, 1, 15 => 0x49dcac0430f446c008fb0086230a0398011f72b01128629b47e1cec60218a64370049180862990c1cce560218b6582990de54e5602890c4e21bc7dcac0431a4a64378fb9580934314c02f1f7bb9578862990de3ee560218a643023cd1cac0431f48631799b957a862991486f1f72b014e86218d1e3ee56d3015e4521bc21cac0431b8a6437
  | 6, 2, 0 => 0x91bb1cac04314c86f398539580862990de68e5643010c5321bc7e02e560218c64379a39580862990c6ef2372b010c7d2990dc00e54310c461000b0023ee560218881969a39580862990462e00853010c53218058011f60218a6430234d1cad760218a643700395c67e2990c02d1f72b0130862990de3ee56024d0c7d29bc91cacc60218a6437
  | 6, 2, 1 => 0x8fb95807e2993486f1f763010c7e2990de3ee56621906531b3c7dcac04314c861878fb9580b8431f462f1f80b95808629909c0123763010c5321b47dcae160218a64378fb9580862990c54ee560218a650218f5c0139853010c5321b0023f0160218964368fb9580862990c2ae00913958086298ada3eef72b010c5321bc7dcace60218a6437
  | 6, 2, 2 => 0x8fb0170863314c86e008fb958c53218519cac04314ca24320bcd1cac05094c8641700001cadf3f14c86b1f72b5d80862990ddcac0431b8a6430a3c7e1ce56b218a6437004d1ca532185020d2980b9580862990dc011f72b010c430930023ee56029d0c2b68fb9580862990c0ef1f80b958c862990de3ee560218fa4921bc7dcada511f8a6437
  | 6, 2, 3 => 0x8fc39cada4312086e008fb010c5321835a46e5663010c5321bc7dd8c04320ca64378fbb1d6c04314c86e0091b010c532183980134853010c5321b0023ee56323ca64368fb9580863f1f462f277bb958086298f5c013472b8cfc5321b47dcac051218c25370048dcac0431f462d1f72b014e862188de3ee560218fa310abca9cac0431c4a6437
  | 6, 2, 4 => 0x8fb95c67e3e94c86ee5602fd0c532890ddcac0431f4dc5321bc7e14e56d218a64378fb9580862990c38f1f73b010c7d2990de3f0a60218a64300bc7dcae33f14c860178fb010c662990c2ae008fc621c7e2990d8011f72b010c310ab481cac0431f4a64378239580863e94c86f3472b010c712990de3ee560218b85321bc7dcad560218a6437
  | 6, 2, 5 => 0x47e10e560218fa31791c7dd8c04314c86f398fc2980862990dc011f73b010c5321b47dcac04320cfa31791b95c6c04314c86e00763010c5321805a3ee560218a64302bc7dcee560218a64378fc2980863e94c86e008fb94a6430a041800e560218562300b47dcac04315ca6437
  | 7, 0, 0 => 0x47dcac04320c862370047dcac360218a62b7004ce3ee560218a62b78fb9580863e94c863d88fb9580862990c460188fb9580863e94c861480047dca862990c561070047dcac0431f4a63178fc05cac05da18a64388fb95808629920863d89547e30e560218a64388fb95808629920861488fb9580862990c280180047dcac0431c4a643799c7dcac051218a643800405cac04314c86017
  | 7, 0, 1 => 0x25ae560218a64360047dcada602bd0c4370000180862990c1c0168fbdde6e560218a64380047dcac05794c8a437000023ee560218a62b6000023ee55f218a64360047dcaaf4314c86107004d1cac04314c904370047de0e560218a64370047e30e56014c8614793c7dcac051218a64388fb9580863e94c8623800001cac02990c280160047dcac05ea18862370047dca862990c62107
  | 7, 0, 2 => 0x8fb95b4c04320ca64388fc39cac04314c863688fb9580864194c863180047dcac04314c8e43799c7dcac04314c862380049e3ee560218a62b70047dfce560218a64379547dcac051218a64380047dd4e560218a64378fbddcac04314c863688fb9580bd4314c862b8004d1cac0431f4a64378fc05cac051218a64388fb9580864194c862b80039598c04314c8601799c7dcac04314c86148
  | 7, 0, 3 => 0x8fb9580863e94c904388fb9580863e94c8601800001cac04310c460160047dcac049a18a64378fc39cac04314c9c43893c7dcac04314c8610893c7dcac04314c86148004aa3ee560218a62b70047e02e560218a62b70047dcac04314c862378fb9580bd57a18a64388fb95808629920860188fbddcac04314c9c4380047df4e560218a64370047dca8629914861070047dcac04310c461b7
  | 7, 0, 4 => 0x39580862990c560170047dcac04314c863a78fb9580bd4314c8a4380047dcada4314c9043700395c6c04314c860170047dcac04314ca04378fb9598c051218a643893c7dcac04314c862388fc05cac04314c8610897c7deee560218a64388fc05cac04314c861480047dcac04314c9e4370047d80a24314c860e78fbddcac0431f8a64380047e30e560218862379a47dcac051218a6438
  | 7, 0, 5 => 0x47dcacc60218a62b78fc61cac04314c863180039580862990c620178fb95808629938863688fc7602e560218a6438000023ec04314c560e60047deee560218fa5379547dcac04314c862380047dca862990c66107004d23ee560218a62b78fc05cac04314c86238000023ee56014c561468fc61cac04314c862b80047dcac04314c944378fb9580863e9b8a6438000023ee566218a6366
  | 7, 0, 6 => 0x97c7dcac04314c863688fb958cc04314c863188fb9598c04314c861480047d80862990c7a0e70047dcac0431f4a64370047dcac051218862370047d80862990c280e7004d1cac04314ca24370047dcac02990c7a1470047deee54314c861079a47dcac04314c861480047dcac02990c281078fc61cac057a18a643899c7dcac0431f4a64380047e30e5431f8a643700395b4c04314c86017
  | 7, 0, 7 => 0x93c7dcac0431f4a64380047dcad360218a6437000023ee560218562360000268e56014c861468fb9580863f14c9c4388fb9598c04314c8623800395808629914860170047dd8e560218a64378fb9580a24314c862b80047d80862990c460e7000023ee5601fca64368fb9580bd4314c8633893c7dcac04314c904389a47dcac04314c862388fb9598c04314c863d891c7dcac04314c86318
  | 7, 0, 8 => 0x47dcac04310c461478fc39cac05ea18a64380047dcae360218a62b78fb9580862990c562588fc05cac0431f4a6438004d1cacc60218a64378fb95b4c051218a64380047dcac04310c461f78fb9580a24314c863188fbddcac05ea18a64389547dcac04314c904388fb9580863e958a64388fbddcac04320ca64388fc05cac04314c90438000023ee560288a63368fc05cac04314c86018
  | 7, 0, 9 => 0x1cad060218a6436000023ee560274a64360047dcac057a18a62b70039580862990c660178fb95c6c04314c863d89a47dcac04314c904388fb9580862990c5610800001cadf60218a64368fb9580862990c561480047dcac02990c280170047dcac04314c622b78fc21eee560218a64388fb9580862990c461a80047dcac04310c7a2370047dcac04310c46107000023eec60218a6436
  | 7, 0, 10 => 0x8fb95b4c04314c863d80047dcac04314c562470047d80863e94c860e78fb95b4c04314c861480047dcac04314c964370047dcac04318ca64378fb9580862990c562388fb9580862990c621489a47dcac0431f4a64380000268e560218862368fb95c6c04314c862380047dcac03e94c861478fb9598c04314c860180047d808629920860e70047d80862990c1c0178fc61cac04314c86338
  | 7, 0, 11 => 0x4d1cac04314c86317004ce3ec04314c860e7000023ee560218fa3160000266e55ea18a643693c7e02e560218a64388fb9580af4314c862380047dcac04314c8a2b700439cac04314c86017004d1cac04314c862b7004d1cae360218a64370047dcac043154a62b7004d1cac043214a64378fb9580af4314c863d88fb9598c0431f4a64380047dcac04314ca2437004be3ee54314c86107
  | 7, 0, 12 => 0x49e3ee56014c861478fbddcac051218a64389647dcac0431f4a64388fb95808629920862b88fb95c6c04314c860180047dcac0431f4862378fb9580862990c562980047e310e60218a64379547e02e560218a64388fb95808629914861080047d80863e998a6437004d1cada60218a6437000023ee56014c861460047dcac043120862370047dcac04310c460178fb9580862990c46198
  | 7, 0, 13 => 0x8fb9580863e94c863180047deee560218a62b70047dca864194c861070047dcac04314c86357004aa3ee56014c86147004ce3ee560218862378fb9580af4314c904388fc61cac04314c9c4388fb95b4c04314c8601893c7dcacc60218a64380047dcac043178a6437004d1cac04314c8a4378fb9580862990c620180049e3ec04314c860e78fb95c6c0431f4a6438000023ee56023ca6436
  | 7, 0, 14 => 0x23ec02990c280e68fc39cac04314c8610899c7dcac04314c86318004d23ee56014c861479c47e02e560218a64388fb9580a24314c863688fb95808629914860188fbddcac04314c863d800001cac04314c8600697c7e30e560218a64388fbb1cac04314c863180039580863f14c8601799c7dcac04314c862b89547dcacc60218a64388fc05cacc60218a64388fb95b4c0431f4a6438
  | 7, 0, 15 => 0x93c7dcac04314c863188fc05cae360218a64380047dcac04314c861970047dcac04314c860870047dcac04314c884370047dcac04314c6c2b70047d98c04314c860e793c7dcae360218a64380047dd8c04314c863179a47dcacc60218a64380047dcac04314c863178fb9580863e94c8a43899c7dcac057a18a64388fbddcac04314c86238004863ee56021886237000024ee560218a63d6
  | 7, 1, 0 => 0x9a47dcae360218a64380047dcac02990c561470047dcac160218862370047dcac0431f8a62b78fbddcac04314c904388fb95808629938861088fb9580862993886148004a9cac04314c9c4378fb9580862990c6c2388fc05cac057a18a64380047dd2e560218862378fc05cac04314c86318000023ee56010c461460000248e560218a64368fc05cac043208a64388fb9580862992086338
  | 7, 1, 1 => 0x47dcac04310c461a78fb9580b8431f4a64380047d80862990c620e7004d1cac04314c9c4379547dcac04314c8a4380047dcac04314c864079a47dcac04314c863188fc39cac0431f4a64388fc05cac04314c8606899c7dcac04314c863380047dcac04314c862f70047dcaa24314c8610700001cce560218a64360047dc6c04314c860e793c7dcac04314c8a4388fc39cac04314c86018
  | 7, 1, 2 => 0x8fb9580863e94c861580047dcada60218862370049dcac05ea18a64378fb9598c04314c8a4380047d808629914860e70047dca862990c7a1079a47dcac04314c8a4380047dcac04310c56237004d1cac0431f8a64370047e1ae560218a64370047dcac04794c863178fb9598c057a18a643899c7deee560218a64388fc65eee560218a64388fb9598c04314c863188fb9580863f14c86238
  | 7, 1, 3 => 0x47e30e560218a62b7004d1cac04320ca64370047dcac04314c861570047deee56014c861470047dcada431f8a64370047e02f760218a6437000023ee56024d0c5368fc61cac051218a64389547e1ce560218a64380047dcac04314c863b78fb9580863f1f4a64388fb95b4c04314c862b88fb9580864194c861088fb95c6c04314c863188fbddcac04314c964388fb9580863f14c86018
  | 7, 1, 4 => 0x39580863e94c860170047dcac04314c7a2b70047d80863f14c860e79a47dcac0431f8a64388fb9580a24314c863d88fc21cac0431f4a64388fb95b4c04314c86338004cdcac04314c863d70047dcac860218a64378fb958086419f4a64388fc61cac04314c8623893c7dcac0431f8a64380047dcac04310c662370039580862990c280178fc05cac04314c863680000246e560218a6436
  | 7, 1, 5 => 0x23f0a60218a64368fb9580863f14c863188fb95808629914863680047d80864194c860e70048dcac04314c86317000023ee5719f8a643600001cac0431b8a6436004d1cac04314c861470047e14e560218a643700001cac04314c860168fb95808629938862b8000023ee52990c281060039580863e9b8a64378fb9580862990c281080047e10e560218a6437
  | 8, 0, 0 => 0x47d80862990c1cd348fb9580862990dc011f72b00a6430a347e02e560218a643793c7dcac04314c86e008fb9580862990da671f72b010c5321bc7dcac0431f4a64378fb9580862992086f1f72b010c5321805c013472b010c5321b47dcac04314c862378fb9580862990c7af1f72b010c5321851c011f72b010c5315b47dcac051218a6437
  | 8, 0, 1 => 0x39580862990c02d1f72b010c832990de3ee560218fc5321bc7e1ce560218a64378fb9580862991486f1f72b010c53218c5e3ee571b010c5321bc7dcacc60218a6437
  | 9, 0, 0 => 0x23ee560218a6436
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
  | 0, 0 => 0x1fff001ffff001fc7001f0f30018c0000101000ffff00fffff00ffff000000000f83f00fffff000000fffffff00000000fffff
  | 0, 1 => 0x1f07c7ff1f0f300ffff00fffff00e73f00fefef00ffff00fffff00ffff000000000ffff00e1fff00f8f800fffff00f8f800e1f1c
  | 0, 2 => 0xff1fc7ff010f3ff18c0ffe1f1cff18c0ff01010e3f83fe3ff00ffff8f8ffe1f1cff1fc7ff1f0f3e31807ff1f0f31f07ff1f00fff
  | 0, 3 => 0xff1fc70000000ff1800ff1f000ff07c0ff000f0e01f07e01f0e3e01800e01f0001c07c01c000f0000707001e0e3ff18c7ff1f013
  | 0, 4 => 0xfcf8c0fce1f10e0f838e0e1f0c1c00c01c00f1000e03800e0f0cff1fc7ff1f0f3ff1fc7e01f000ff1fc71c000f0ff1fc7001e0e3
  | 0, 5 => 0xfffffffffffffffffffff0000000e73f00fefeffff8f8ffffffffff8f8ffe1f1cfff8f8ff00000fff8f80000000ffe038ffe0f0c
  | 0, 6 => 0x1e000000000001e00000070000000e0000000000000000070000000e0ff18c0ff0101000000000000000000000000000
  | 0, 7 => 0x70700000e000070700000000007070000000000000001e000000000001e00000070000000e000000000000000000000000000
  | 0, 8 => 0xf0000000000000000000000000f00ff1fc7ff1f0f3000707001e0e300070700000000007070000000000707001e000
  | 0, 9 => 0xe038000000000e03800000000000000000f000000000000000000000000000000e00000e0f0000e00000e000000e00000e0000
  | 0, 10 => 0x1ef000007000000fe0fff8f8ffe1f1c00f8f800e1f1c00e03800e0f0c00e038000000000e038000000000e03800e0000
  | 0, 11 => 0xe00000fe00000e73800e0fec00e73800000e000e70000e00e0000707001efe300070700000000007070000f000007070000000
  | 0, 12 => 0xe70700fefe300e70000fefe000e03800fef0c00e038001e00000e70700fe0e300e70700e0000
  | 0, 13 => 0xe73f000000000e73f000000000e03800fef0c00e70700fe0e300e03800e0f0c000707001e0e30007000000fe00000000000000
  | 0, 14 => 0xe73f00fe0e300e73f00fe00000e73f000000000e73f00e0f0c00e73f000000000e73f00e000000e73f001e0e300e73f00000e0
  | 0, 15 => 0xf00000000000000000e73f00fefef00e73f00e0f0c00e73f001e0e300e73f000000000e73f000000000e73f00fef0c
  | 1, 0 => 0xe01800e01f0001c07c01c00ff01c07c01c000001c07c000000001c07c000000001c00001c00f001c00001c000000007000000fe0
  | 1, 1 => 0x1c07c01c00ff01c07c000000001c07c000000001c07c000000000000000000f000000000000000fff8f8ffe1f1cff1fc7ff1fff3
  | 1, 2 => 0x1c07c0001e000000000001ef0000000000000000000000000f00000707001e0e30007070000000000000001e000000000001e000
  | 1, 3 => 0x1c07c71c000001c07c7001e0001c07c71c00ff01c07c7001e0e31c07c700000001c07c700000001c07c700000001c00001c1e000
  | 1, 4 => 0xe03800e0f0c00e038000000000e03800000000000000000f0000e70000e00e01c07c71c1eff31c07c71c00ff01c07c71c00000
  | 1, 5 => 0x1ce7f81ce0ffc1ce7f81c000001ce7f800e00001ce7f800000e01ce0001ce00001c07c01c00ff01c07001c000e01ce7c000e0000
  | 1, 6 => 0x1ce7ff00000001c07c01c00ff01ce7c700e000000e73f00fefef00e73f000000000e73f000000000e038001e00000e00000fe000
  | 1, 7 => 0xe0f800e000000e0f8000000000e0f8000000000e00000e01e000e0e000e0e0000e00000e01e000e00000e0000001ce7ff1cfefff
  | 1, 8 => 0xe0ff0000000e0e0f800e0ff000e0f8000000000e0f8000000000fff8f8fffff1cfff8f80000000ffffc7ffff0f3e0f800e0ff000
  | 1, 9 => 0xe0f800e0ff000e00000e01e000e0f8000000f00e0ff07e0ff0e3e0ff07e01e0e3e0ff07e000000e0ff0700000e0e0ff07001e0e3
  | 1, 10 => 0xe0f838e000000e0f838e0ff000e0f8380000f00e0f8380000000e0f83800e0f0ce0f838001e000e0f8380000000e0f8380000000
  | 1, 11 => 0xfcffc00000000fc0700fc1e0e0e0ff3fe0fffefe0ff3f00fefefe0f800e0ff000e0f838e0fff0ce0f838e0ff000e0f838e0e0f0c
  | 1, 12 => 0xff18c0ff01010ff0000fffffffff0000ff00000fcffc00000000fcffc0fcffff0fcffc0fc00000fcffc000e0f00fcffc00000000
  | 1, 13 => 0xff0700ff000e0ff0700ff000e0ff18c0ff01010ff0000ff00000ff00000000000fff8f8ffe1f1cff1fc7ff1f0f3ff0707ff1e0e3
  | 1, 14 => 0xff0707ff1e0e3ff0707ff000e0ff0707ff00000ff07070000000ff07070000000ff0700ff1e0e0ff0000ff1e000ff0000ff1e000
  | 1, 15 => 0xffe038ff00000ffe038ff00000ffe038e0e0000ffe0381c00f00ffe0380000000ffe000ffe0000ff0000ff00000ff0000ff00f00
  | 2, 0 => 0xffe73fffe0f0cffe73fff00000ffe73fff00000ffe73f0000000ffe038fffef0cffe738ffe0fecffe038ffe0f0cffe038ff00f00
  | 2, 1 => 0xff0000ff00000ff07c0ff00ff0ff07c0ff00000ff07c0e000000ff07c000000e0ff0000ff00000ff00000000000ffe73ffffefef
  | 2, 2 => 0xfff800ff00000fff8001c00000fff800001e000ffe7f8ffe0f0cffe038ffe0f0cff07c7ff00000ff0707ff1e0e3ff07c0ff00ff0
  | 2, 3 => 0xffffff0000000ffffc0ff00000fff838fffff0cfff838ffe0f0cfff838ff00000fff8380000000ffff07ffff0e3fff800ffff000
  | 2, 4 => 0xffffff001e0e3ffffff0000000ffffff0000000ffffff00000e0ffffff0000000ffffffe0e1000ffffffff1f0f3ffffffff01010
  | 2, 5 => 0xffffff1c00ff0ffffff1c00000ffffff0000000ffffff00fefefffffff0000000ffffff00e0f0cffffff00e0000ffffff0000000
  | 2, 6 => 0xffffffff000e0ffffffff00000ffffffff01010ffffffff00000ffffffe0ff000ffffffe0e0000ffffff00e0f0cffffff001e0e3
  | 2, 7 => 0xffffffff00000ffffffffe0f0c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1bdb0015975001a820015050001080000101000295b003292500295b001080000280b0077375000000ffef7ff0000000067375
  | 0, 1 => 0x50404b50d0d2007bdb0077b75006b5b0076b65005ad20055a50005ad200108000051d90041b350050d00067b750050d00041a10
  | 0, 2 => 0x9514849501092901080dac1618901080900101063a82f63ba00f4a80704a80c08250c062518082210806b51d0d20f057d0f00daf
  | 0, 3 => 0xb51e860010000b51e86b51d0d2b51684b50d0d2b51e86b51d0d2b01a82b01d05094168094050d0250e06251c0c2b11886b119012
  | 0, 4 => 0xd8d0d0d8c1e10dad0f0dac1e189850d09841e104ac0704ac0e08b51e86b51d0d2b51e86b01d050b51e8694150d0b51e86251c0c2
  | 0, 5 => 0xffdef6ffddedaffdef6ff98c8a6fce766fdcecadad0f0dae7f7ddad0f0dac1e18dad0f0da80c08dad0f00000800dac070dac0e08
  | 0, 6 => 0x202b0b203e165202a02203e04004270904261e5002309002616504070004041e0903189902313500210900221250021090000000
  | 0, 7 => 0x252f0f04141e0252f0f0032125252f0f0010000252f0f253e1e7252e06253e0c2250704250c1e2250604250c0c225250d252a1a7
  | 0, 8 => 0x861590862f2500610900623250841500840f20b53f8fb53f1f7252f0f253e1e7252f0f253a1a7252f0f2518082252f0f203e040
  | 0, 9 => 0x4ae17900229254ae17900008004ac1704ac0f284ac0204ac06084aa1294aa252d48e15048e2f2040e10940e232540e00040e2200
  | 0, 10 => 0x286b52287ef600c47500c44fe0daf1f9dae3f3d4af1f94ae3f3d4ae1794ae2f2d4ae1794aa2d2d4ae1794a80c084ae17940e2a00
  | 0, 11 => 0x60ea0260fe2404ee7794ee6fed4ee77904049e044e70044e63e02d6f5f2d7efe72d6f5f2d18c822d6f5f0850f202d6f5f0010800
  | 0, 12 => 0x6fa52d6faa5af6f84246f8848a6def5f6dfefe76cef526cfefe06aeb7b6afef6d6aeb7b203e84065ef0f65fe3e765ef0f40f2200
  | 0, 13 => 0x6fef7f00329256fef7f00108006fef7f6ffefef6fef2f6ffe7ef6fe77d6feefef6fef2f6ffe7ef6fc7746fccfea6fc6246fcc6ca
  | 0, 14 => 0x6fef7f65febe76fef7f60fea406fef7f0054a406fef7f4af2f2d6fef7f4a90c086fef7f40f2a006fef7f253e9e76fef7f04149e0
  | 0, 15 => 0x9853d09845f7090528090452506fef7f6ffefef6fef7f6ffafaf6fef7f6fbedef6fef7f6fbadaf6fef7f6f98c8a6fef7f6afef6d
  | 1, 0 => 0xb05a82b05d2509c57d09c45ff09c57d09c00c809c57d09045a509c57d000008009c45509c40fa09c05009c005a09c57d09c45ff0
  | 1, 1 => 0x9c77d99c67ff59c77d99067b759c77d99067a509c77d900229259873d99867f759073899067375dad2f0dac5e58bd5fd6bd5dff2
  | 1, 2 => 0xbc7fd2203e840b87bdbb87ff75b87bdbb85de50b87bdb9855f70b57f8fb57f3f7b57f8f9055250b57e86b57f2d2b07a82b07f250
  | 1, 3 => 0xbd7fdfbd18c82bd7fdfb07fa50bd7fdf9c55ff0bd7fdf253e9e7bd7fdf2518882bd7fdf0032925bd7fdf0010800bd7e86bd7f6d2
  | 1, 4 => 0xdaf3f9dae7f7ddaf3f99045a50daf3f90000800dad3f0dac5f78d4f789d4e73f5bd7fdfbd7fff7bd7fdfbd5dff2bd7fdfbd5ded2
  | 1, 5 => 0xdef7f9dee7ffddef7f9de80c88def7f9d0e7a50def7f904269e5def6a0dee76d8def7f9dee7ffddea729dea65eddcf7d040e2a00
  | 1, 6 => 0xffffff0010800fff7fdffefffffdffdf40f2a00fffffffffffffffffff9055a50ffffff0010800fafbfbb07fa50f0fa82f0ff250
  | 1, 7 => 0xf0fa82f098000f0fa829055250f0fa820010000f0fa82f0ff250f0e000f0ea200f0aa02f0be040f0a000f0aa000fffffffffffff
  | 1, 8 => 0xf4ff8204141e0f0fb8bf0ff375f0fb8b9077375f0fb8b0032125fafaf2faffe58fafaf20010800f5fe86f5ff2d2f0fa82f0ff250
  | 1, 9 => 0xfafbabfaff77dfaab2bfabe56df8fbd20850f20f5ff8ff5ff3f7f5ff8ff5be1e7f5ff8ff598082f5ff8f94553f0f5ff8f253e1e7
  | 1, 10 => 0xfafbfbfa98c08fafbfbf0ffa50fafbfb9855f70fafbfb9055a50fafbfb4af2f2dfafbfb203e965fafbfb0014960fafbfb0010800
  | 1, 11 => 0xfcffd20010800fcaf02fcbe5e0fffffffffffffffffff6ffefefffffafffff7fffafbfbfafff7dfafbfbfaffe58fafbfbfafaf2d
  | 1, 12 => 0xff94a4ff8949aff8424ffef7ffff8424ff8848afcffdb0032925fcffd2fcffff0fcffd2fc98c80fcffd248f2f20fcffd20032920
  | 1, 13 => 0xffa72dffae5efff8724ff8c5eaffb5adffab5bfffa52dffaa5afffa52d0000000ffd4f4ffc9e9aff9ea6ff9d4daff8e26ff9c4ca
  | 1, 14 => 0xffaf2fffbe5efffaf2fff9c5eaffaf2fff9848affaf2f4ab252dffaf2f0010000ffaf26ffbe5eaffaf2fffbe5efffae26ffbe4ca
  | 1, 15 => 0xffe57dffaadafffe57dff88c8affe57df0eaa00ffe57d9c40fa0ffe57d0000800ffe424ffea68affe52dffea7afffc574ffc8faa
  | 2, 0 => 0xffef7ffffafafffef7fffbadafffef7fff98c8affef7f0010800ffef7ffffefefffe77dffeefefffe57dffeafafffe57dffc8faa
  | 2, 1 => 0xfff7adffef7ffffd7f4ffcdffaffd7f4ff88c8affd7f4f0cda50ffd7f4250c9e2ffd6a4ffcd6daffd6a40000000ffef7ffffefef
  | 2, 2 => 0xfffea6ff9848afffea69c556d0fffea6253e0c2fff7fdffeafaffff7fdffeffffffffffff98c8affffafffff7fffff7fdffeffff
  | 2, 3 => 0xffffff0010800fffff6ff98c8affffffffffffffffffffffafafffffffff98c8affffff0010800ffffafffff7fffffea6ffff6da
  | 2, 4 => 0xffffff253e9e7ffffff251c8c2ffffff253a9a7ffffff04149e0ffffff0032925ffffffd0d1a10ffffffb51d8d2ffffff9011810
  | 2, 5 => 0xffffff9c55ff0ffffff9c10da0ffffff9055a50ffffff6ffefefffffff6fbadafffffff4af2f2dffffff40f2a00ffffff0072b25
  | 2, 6 => 0xffffffff9cdeaffffffffbadafffffffff99c9affffffff98c8afffffff0ffa50fffffff0faa00ffffffdaf7f7dffffffb57fbf7
  | 2, 7 => 0xffffffffddedafffffffffafaf
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 52 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 52 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 314 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 314 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 314 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 314 then wireAt i else 0
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
  | 3 => 9
  | 4 => 62
  | 5 => 571
  | 6 => 1449
  | 7 => 525
  | 8 => 4
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xe09a1265e02a39f7d723d5eba9c13a818e826649850ae70a2f1460f81748db5c04ae2c4a
  | 4, 0 => 0xf69a8d67e4579ee9cfc3ac4fce335278cd827617c918cab1ba7a0d23b909cc8bb81c5323b55b9366b2d1c0c2b21545c6adbf1494aaab64a5a81b48bc9ad22d4f931ea73791cbc94388cfcf6784a6fd44848fbcbc825ea18c812123427cb9d09b7b7d679178e388d57166856d6dfd08cf6abc687a6929baec68b3b1f368391bfd67ef062e65100cd254847fb34e6c4fbf4e4afb424e3aad4b492a59a1422c06d9420a64ab3fb2da623bf7f5823619e48035247ba134c2242f3260f29c31bc1ea62dacbbfe2921931f2538f7f3210955be1e5da09f1e0464641c9c3727143584c013e54be613b4eac70e20aaee0c855d3705af9fa103dc0b91
  | 5, 0 => 0x140c1c6113cb6ed2132ccf4a12ec372612aced29123f979f119217d81016abb3100eb51c0fe749af0faa77070f8499530f672d690f46fe910f173e660ea220190e7ddf9c0e56fe570e39926d0db432850d83c6990d7c23af0d4db57f0d1d024a0c9067380c796cfe0c405bc60bb5b40f0b7ad8790b7002330b6a7b1d0b55fd400a4e1d2e0a41d8c409b7e77909a0106708febdff08d0a7c2088521e20772bb3e06ce7e4f06519409064bab2605d9946205bc287805ab788a058adacd056ad8190545bc5804ea4bfe04e549e40414a3550312060302e65a9102cc506b02a9b8e80274c39c0269762b0226934701c22df601373cfc01204fab007d93d800272583
  | 5, 1 => 0x249bda20244fc4912331533922ed385a22df9e0e22ddf08e22d09f8722c4e84a22880254220c243b21b0632821b04b48219f06a121819ab7217d7e94217c18ce20df8cd02075da641f63f8281f6144651f426e131f0740291ef254801eb22c171d1c780a1cfdf5c51c41d9ac1bff83251bf750b41bd606951b7e2e5d1b5300e41b3ab7121ae2b9091a3fc2e519f07a781958fcab194f2d80194b6be81910831518f26c4c18e1427018dfc05318ae189c186d2a4d178e4a2c17373c1d172decb916bc7a2616aa615c16a4004a167df75e1658de331642f5aa163ebd77161db96b150d4cfa14aba2a7148d569f147df0991467f41e14596412144f729614152387
  | 5, 2 => 0x35dbbbb035b6c4a335795bf03556e60735099e5634fe1fe134313a13343096ad3426918933f062ad330ba2c2330b5fb032f9fa1e32bb87043239456f315776f53115c93031117aa93109335a30d6b6c5308c42f830378bbb300bb48d2fe11cf22fbc30502fa7a6b32f7a95b72f734f292f508a652ed537322eadcace2e93469d2e1a843f2dde33dd2dd47ff82d1d24532c8a8e7a2be7580c2bcd5b7f2bac62dc2b6874ff2b0aeba02b06dce52a438fa12a3198e029995dc3298d50c2297a7762293a8985291d1d9b287efeee281a6a43280064ef27a8a3f52798ce9c275a76902735f98b27306e542705880d263c6edb263b036f257d59b824ba4fd024a14e02
  | 5, 3 => 0x47b3a3114783d8494760b6c44705cf5646f0214b46d5ab8146b110c04658796046361230459fd698459ecff74551190a44fa88f844ae3fb043f560434389d593434ac032433c06d443091b4242e7ad3142ca756342b779a3426cf99842421ec1422d017a42115aa641d0eedd41bfa6e3418972a841262c3d40aaf521409bb26640722552405f5287404604093f4ef09c3f19de853e26d0633ddc03723dd0ef663d7b67de3d30bc313c9d75a23c5855793bc70d473bc2146d39bcaa9339ab24c438e1164638d885d238ced83238c28e57382e3a7037b9fc1b3795f6ec377ab9dd3761c3f3371b9b8a36feb16e36b02cfe364e56b036495ec1362bcb4635e7ff76
  | 5, 4 => 0x5aec27435abc764c5aa8a6b95aa68a955a7ecbf55a292fbd5a00922459d395c759be449559a0445d58fe810f5834a24e57fba73f57ba866757a5936e5796e9b0578213d257329b8f56fbf48f569dbc4455ee63c45542ba4e54efa37e544b97f0543a1b9f541df39b540e1e1853f2862353b95bd15368384a5318541d52be2f94529efe0851ef299251d1d295519ffb99514e1f2050bdbf0650a0531c501d9f5d4fe19e8b4f1fd9d74f0d9c4b4edd097b4d99d2864d934b664cf152134c33661d4beee6fc4bc38b784ba311f14b83735c4b81a28f4b6e21e64b24895f4b17beb24ae0a75d4ad20efe4ac0847c4a55e6434a24047e492957c047d3da5547bbe743
  | 5, 5 => 0x742fd60273721cde73436dd9733c1bce730a5f69726d1b96725bbd65716e449670de2b6570be4f31701596636fe675ef6fdc96956f00fbc36ea01f006e85ad376e5661bc6e197bc66dbf83216db2a4bb6d82caf46d66356b6cdf2d166bcf90f36b63ee136b2971f669e7c97d69acc536695b4305690a27786901a99c68cb711368638acf67be31e067339425660c640965b58cf2656acfb064fbe88a64cccf5864bac83664b7cb1764a1fc876479564e643988c963cf9d85636ac2ae635f4efc62cee63f62c33c14629d6705618a6a10615f5d1960d2136b60a917d85f9defbf5f9873855e92f96b5d76ae0a5d5e4cb35cbf56355be6bee65bbb72fe5b3bed48
  | 5, 6 => 0x94752d00945d6fe493ba7c3b92fd5597919e26b690d910f69086da4d906b39fd90623c40904bab75903866ff8f531ed78eb93c198d65f46e8c6170088be1a6ca8b4d6be489e26d3a89db0760897c1ede896fa3ea8934bc8a88368716882be4e1882032ad87d07ca987b2993d8610cf9385c2d59884fea4a9846edeff845407c983c0be09832a04fa8327705e82ebad17825289c67fb807ca7f6313a77f24c13b7e9f91ba7e373f027df513a47cf2005b7ced496e7cb318ed7c831cd57c3bc47e7c13cf467bf6635c7b18592e7a85129f79e6d451793eeb6e78fd9cd978cda55478c39c9978b8fe8c78860ca876ebe5b97680fac474e00fc4749b8aac74863936
  | 5, 7 => 0xb96d01eab8e08af4b86b3627b7f60488b7a1fd24b65207bab5d22f43b5406affb4e91aa9b4d0e6a0b4647021b4540a0fb443939cb3e461b2b3ba9ff2b36ac361b24cd3dab172a0fab106faf2b0f2d96bb0eeb5bcb0ba3fc2affef213aef16e79aee8b368acc34d25ac638cddabfce9d5ab16afd2a968d4e1a953fed7a82d1a2fa67a4b82a3d51455a32745cea2330895a20fedeea125e9a0a1093cb4a0d2fccda0bbc0d7a09c2960a04b2e56a03a41ae9fa732239f52393c9f0a53779f0550e29e95058e9e7799a49c09dccf9a4e8d8e9a4655a29a3e92c299766af89926b63f9867cc6a98658eab983bf9ca9742e10596a47b2f952c5ba294be418594762056
  | 5, 8 => 0xfd058035fcc53608fae73b35f9acd0faf96feb04f735d725f6306ac4f4c646bdf44935f4f37019b2f0f8df95f0a2e75deff86bc5efdb1310ef5e1cefed0f093deb5e26b6eb5a3525eb09021bea2b99f7e907f834e8eda3c8e89f1d3be85578fce5541214e48b9278e3322541e0aa5a6cdf6bb463ddd3ac13d93e23a6d80b7990d7783301d640a3b7d5b96fedd35de95ed3084f68d27f16edcebf7783ce7d2689ce4ca24acdf450dacd815726cc378088c7a2a7d0c678e2adc53650fdc4fa1f48c4a2db87c017b2a8bf8705ebbf3d61acbecd9540be469854bdee9ca0bcbbca35bbb787aaba95ed65b9b8f6f9
  | 6, 0 => 0x6b5fac6068a399a0681af190665520c0659646506552c800644c92305c61dd605bdadfa05b43f6005a509e6057729b60575e13b05687e89052cb0ff051a6ec905169eb0050bb04c0507112004dbb86404bca65904941f6a048dacd70479bbe104015d6403f1b95203ae4e9903a0960e0375c6cf035a95650341d11b033b05b503087e0402e9d44b02c1685702a27623029aef9e028da25d02470b1b0240cfa30219fdf801dadaa501c9b31e01a6e4da01a44b7b019c9fad01866a3601521d0b0146c416012eb7b1012c73fe012a5840011eaa2f01195bd500f5a3d2007dbb7a007d93d8006fb9d3006c268400693658005b006f003e83f9003b1ab4000db973
  | 6, 1 => 0xca165b80c97cf590c903f7b0c83298b0c82609c0c7bcab90c6f23470c13a5aa0bf303a40bb0f9310ba77e000b88cc090b651c800b1a7d630b0896c40af6cb310af23e1b0ae34fac0ad2180c0ac986c50ac01d010ab8b2690aa0caca0a9628be0a83e0780a8213ec0a7d079a0a6426b20a53c4d60a3d884a09fb12fd09f7ca3e09eb25bd09ea0c3209da5e5409cff8a309a18f540966c06b09633a880952eb7b093e73560938c9750938390c092d20e8092be94c090e3a080903dbc508c6f6e6085c29ce0856ca26084aafc7083f2726080f361f080f15bc080a8eb707962ead078c60020787d7a5074921400747544407382cc50737882a0715437d06dc9842
  | 6, 2 => 0x12b8ab41129e663b125d0b7e124d6d63123c1c3b1233466a1232479711d640d01198d170118eca21118d0e1d11880f961187183a11803b3c115b67ca110f8d8e1106ad5710bf6ca6109faa42108ef5b91087cb5e104ef361104ad074103a9912102d648a101f34a2100eb51c1004efa20ff073950fe0ac610fde41e30fcb33c20fc7e3a30fa2a5570f8e38f60f8899180f8898390f8009980f37de040f21afa70f1c66040ee2d2210ee271f80ecb2c040ea800b80ea022dc0e7e15130e67dc250e2c4ae30e1fe6e00dfb96ef0df124ef0dcd46f30db51cee0db432850da46fb90d9cbe430d9a92370d6e8d170d2aded90cfc43180cf439bf0cd4b54f0cc21f43
  | 6, 3 => 0x19169d3318fdbc2118f9443318f811bf18ef4baf18eed24c18e3fb0a18d063f718af851c18ac994f18ab6b361871d538186366e3185955ec1852bb5e1841fcce18043d6917e170dd17d98ca617bcd81e17bba65117aa731317989514175a929b17497f4a172c13601729918f172938d71712096e16d8a81c16bd508a16b4d972169cdf8d169877221691aff3167fda5b164ab0e815f71c1b15f022ce15b18426158c470e1581f8c8157b3ef615776f951561a43a1560201415212d4d14db18b514a3cc181476b36414696ac21461a2571415063f1413d60813e90d2b139302bf138402851375dc6513728f561317dd2b1308cd7712dbba7612c3605312baa677
  | 6, 4 => 0x1f3387171f0bc3bf1f0740291f06a07c1ed20e051ec4d0da1eaa0f9b1e961c6a1e5a4bef1e3c357a1e35b7f71e184c7d1e0aec781e08e1531df468421ddb52551da019151d9945271d984e6e1d825b1b1d8190081d5bd8171d55e79b1d01f4191cce2f151cc5aa5e1c8f14451c84fb571c7f55261c5d3d531c5377201c35b2841c18469a1c0c1b4b1c03a2d41bf04d8c1bdb5b301bbbe6161b9d622f1b98c1901b9386ad1b8548e61b7eaebf1b78d4bc1b62a5db1b61a0cd1b55df541b52bdbb1b4b11361b40c0441b27d2611ac6cf551a87fcc01a5d20641a58a2341a4058c31a0ef3fa1a0dc40d1a04d97919ccf3f619b64fa1197741991966b8001921f28d
  | 6, 5 => 0x2844d6392842e26228367c31282a58e7282426c92819104727a497ea27873465275d28bc275b976e275a76902752ae75272a02302707a0fd26bb2fef26b36853269608f926640762265363bb262a32f42604931525afebbc255fdd5125494af52547e4b9253ef9ad250aba5724fedf5924cbf97124a03110241577b923fe5bdc23e8c56e23bb3be323aa74da22d85c9a22d25b5c229eb02f226831b42257ddbb2241e415222b0ffa21d8db4721b9f7ae21a5c3f1219016092177d42821730a3e2155a5e2213bddeb20e249a72062e284205b0a2a2014c6441fe039d21fb72b911fac95641fa432931f9874111f87b1c01f8738591f75faad1f4eac261f47d985
  | 6, 6 => 0x2ea523322e8ed5cd2e2eb6002dda71352db09fc22d90a6012d8de92d2d7d41f82d75a53d2d618f3b2d20bdd92cf8cd042cae25c92c611b6b2c46203c2bfff1562be8c6dd2bcf9a012baf6f8f2b81626d2b5f77182b4ef7cf2b25f1c52b20b3d82b1903882b15a4b82b09ceab2afe09d52acd7a982ac54d632a892cd02a734e672a60e87e2a5335872a42cf9a2a4238582a3198e02a222ab32a14d0f72a147f222a023a7d29faee4829e90d4d29e188d329dcd53d29d10a3229c478db29a1070d2992b93229740e86296b38aa296669a2295678be293f76f02934275729319d85292af8b7291385ac28df87aa28bc54b328b1318528a472c728a1dfb0285f1665
  | 6, 7 => 0x35f2a55735d89aaa35970aa9358ad894356512d0353aa3c635099e5634fe1fe134f524f934e85a3334c8f0c734886bc33481847a347c735e344f47aa343a84db340993c533da662c33d93c6b33ce1343338e027c33864f1f3380f3e4337f0a06336a01d2335d8195332a027733193e9a3316827432def36c32b96323326bf53f3228b4233217690131f5eab33177ea88312099a03115c93030f0dff530e1709b30d5282030b9d1dd30a5e218309c65f33096bd90308c42f8306f6ccb2fe11cf22fc6445a2fbf35272f954dd02f8f1ff32f7e6ae62f5e6cbe2f20329b2f1abea52f1488772efbd9642ef7eddb2eedfa852ee716dc2ede098d2ec68d272ebd3d6c
  | 6, 8 => 0x3cee74523cedcf813ceb95653ce6437e3cb64d0f3c9643853c38e0113c35f2033c27f8ae3c20e4c73be08ad93bd6ad1d3bbf524e3bb1f7013b9031bd3b8aa58d3b5624293b34c0e23ae826bb3abe07193ab838783aace7f43a2d6c623a03d4b139ffcc7c39ff1f0a39de4fb639ddbebc39b1034539758358396f572d38eb527838ea75ab38da452b38d186c938c8629238c10570389a48a73885fcd2388012b1386890e83819736d37fdfb7837c7d31d37b9fc1b37b9f43e37a4a2c8379a618237962c63378ba63f377ee725376ecd6237596ec33702e44236ffac3036fb367836de7a873678c0eb366fa2723668643f36648703365a85603612624435f890ff
  | 6, 9 => 0x449785304490ec0c448eda3a447f91b144578d0c437b17534365b3a9435fdc0743415cc542ef746f42c90b1142b779a342b451b0425ac010425327d74250d60941a0c1284183d8874175ef234170bcbe4164b840413586ab410d769640f6a5f940e3c4e340a60e3740936de1408a06cf4071490e406c7db8404b301340455b7a4041a8df400945b43ff4ef3e3feafc213fc11baf3f5ea61f3f39b76f3f086e6d3ef9b7083ecbdd503e9e85263e7b57fa3e79bb8a3e56ef7b3e55bbba3e43e3b53e38dfb93e38a55b3e277fff3e0be7f03dc57c4b3daf73bc3d946b583d8f565c3d820b7b3d7dc3333d60158c3d2562093d254e653d1c18ae3d0b3b903d0124c9
  | 6, 10 => 0x4e20ca5e4db0fe984d86bbea4ca859dc4c51dc5f4c4c79c44c4ab93a4c2eb5784c1e35cd4bc5e4304bb8d2fa4b93e1974b83735c4b77d19c4b6e21e64b6d33644b4b81c74b2e44754b2472944b21fba14b1168534b0d87ba4af8703d4aee73794ae1e0704ad20efe4acdf8d54a55e6434a20e91b4a1e617149e579ed49e0f04f49dd9ff449d9fcdb49d9a14a49b6983f49ae9520498effba49802bc1497253c149697f42493b1744492cc4da4854372b483393994828dac04812707947ff7ab347d1bb1b4795ee6d46ed067a46de284246b9893046a6e54b469949b5462000d245d91ef1459ecff7459774c24526b4084523bdd9450651ef4504d9ca44c79b8a
  | 6, 11 => 0x5659605e56427f92563ffaf155f9c36e55f6748055f5a32a55f35c3e55a0239d55914c4d5582b7b3554910f15548eb3e5530a86c54f251df54c66e2d5488605d5459014c54583324540174e053ec72ba53e591e853dbb72c53cd1deb53ba6d3253a51bbc538c2b2c5354fc3553447d04533fb48d5314eaf652f2e65052e8c50e52e71d01528866f75281620b525afe545247743851b5014451501bab5143b19c5137f86e5137e9295124950150ef354250e499dd50b1940650694d92505beeb35059633d501f9e51500139404fc71f074fc559f74faafd564f8c57c24f7141a24f5e8ec74f5ddbaa4f56d9744f135c524ed5e3f64ecc8e064e6d16534e303586
  | 6, 12 => 0x5fbac6fd5fa9e2065f9873855f63a5875f4ce3e85f411ea25f35ba935ed985675ed000cb5ebac33b5eab57b15e96063b5e95b4465e82f8175e5e95475e5c4d5c5e22a7545e13ada65dbe740c5d7d6e2d5d4dfc4d5d4be8d35d4618165d1e66bc5cde0cce5cbb87cc5cb45f9c5c7754db5c50e6185c00629e5bec8f385bdee7215baef06d5b6fefcf5b2562705b023f875aa5f5965a9f5dfd5a8723c85a71d2525a6fa4e45a6d6fbe59eaea58597e76b4596cee2e58e3d83358bb531a585d4a9758430005583019b9582969ea5813f0b4580611d55802414f57ab48c1576c925c56f8e29d56f411bd56d3b3db56ccc28056b44698568ff7f1567c7f515672a487
  | 6, 13 => 0x69c0add469bac9686936cae3689dea7d68576a0d684cb1746827ae85680dfb0f67a3bf0d678eb5406786b84767852479677d84d8677701556776f078675249ae673f974f67339425672edba16725e9c566eea10d66d94f9766d1c7a966a873e6658f4356658f322f653364ff650bdfd764c8c42e64b320fe64a0c73f64789948644a97a9642e54a063e431ee63a6a9d362dd8f1e62da87e162c980fc62a49cbc6296bc1f627050f96264afc16248b0fb61f427ee61ca400861818f6f617d3f4b6178b77d613f4bb661381f97610913c860f47f6c60ec287660e8d6d560c1af3f60b814f360a4435560638fc460506f526043727f6012a1605fd7d1ae5fce787b
  | 6, 14 => 0x756948e67557aff175566249754909b1752cfb2e7474c9d8744a99ed7448134174068ac973be3a8b73a48879739a2d4a7365dcea734eaa0d73493a2772dbdfac72b283397299780c728270b47239d99b721ca2bc71d8f93471d3d74b71c8678771a6de3f7195975871907573718d4b857179360f7167d5247166cf87714b8ec87140254b7136656e7129e8b070d8df6c708230287045cf8d703b7bb46f9a15cd6f29bf656ee7589d6e97547b6e6a31206e027d566dd08b0e6dc17e2d6d9d833c6d7e78d66cfdbf986cfb99c96cfb7a1c6cf4f29e6cd111a66c80921c6c4b6e046bcf90f36b70d1e96b39f7fd6aac31a36a9639c16a8f01346a22b4f869cd7e53
  | 6, 15 => 0x7f00ecae7eeb32617ed513f37ebbf6017e5243da7e4b58517e41f46b7e28295a7e2488817e05acff7ddeb6337dbaea3c7d7d57bc7d2e7cf97cfde4937cea112d7c69c65e7c1bbc077bfa0c557bd019c77bab0f147ba3c0797b8db51e7b334ca57ada8ab67abe6b607aaf2d897a9933267a8ef3507a5b787a7a2bf4367a2a8dff7a11764d79e5550479e15a2879c02f7279bfc59f79ad660279717a8d792903cc791e9fb77911f99d78c917387860a52878299fcd7819d38577dc326977d135d077adb12e778560f77770373f76d00d2c76c5d6f276a582cf765bdd32764e5f6176461d727633f097760760367603a98f75c2fead75b293ef756ef7e9756b3d6c
  | 6, 16 => 0x894190bc893fe42c8934bc8a892cfdea8890c621885e5470884052b788368716880c62cc8809f96f87fff5c087f2d3ba87ec230287ea0dcf87e6c54587c7d78887b2ceb4879add67878be23f8786f1f7874f92698749a55b873abea487038fdf86ef90bf86be95e986a525ae869b401d8690a30e86419ece85f6241e85cba36285a0b970858e52b885569ca78527bd3a84520cd584152e7383f7115a83eaa2da83a21eb18398fa6c83814402833df903831ab88982e1f31882de71178276397282204782818bda658123ee8880a78bdc806ec49b806266ad8040d0787fe516d97f9c730f7f8ef2d87f7c17707f685e077f2587b17f1a591a7f1a1c937f0507a4
  | 6, 17 => 0x949bdb7e945654d793e5c51a93e2499393d352af936159ab935ddd6e93303d3b92e04bde92d773ea924f9c0591e61fd391b3cbf191a73dfd919ac8ae916bb660913f5441912821e490f68a7190e225fa90c788869066fa2690543b819022657e8fc42d338fa2db658fa19e1f8f74f0a98f34486f8f26b32c8f1f96978e8c53638e7643fa8e60a20b8e323b688ddbc8d68dbe23998dacf6f48d51ed158d395ff68ca14df68c6170088c5e2c4f8c5b2b6f8c51c7138bddfc858ba51dad8b8d04f68b7e195e8b74ea068b0cdb878af097cd8ae7ae958ae257588aafa50e8a7994f88a4c27bb8a4b2c568a2340618a1fecb88a0b34fc89efee9189b52b508974814d
  | 6, 18 => 0xa3c1ab4ba3978b47a376dcaca31c39e8a2cd8bc3a2a6f9a5a29f9104a26ac20ea1f9723ea1662bafa0c4a17fa0bbc0d7a0aab22aa06b55ada0569a1b9fce48649fa7e8e29f6676b19f19428c9f0c76639ed1e5489ebfb44d9e93ebe99e43f1059daae7359d72dd149cd0c7aa9c5ca0df9c32deb99c2309d29c01232b9bcb613f9b791ada9b6512559b5b3fbe9aca79e39ab69a3e9a4e8d8e9a4655a299e5b62f998829a3994b9d0899331f9b98ec3cf898ce4a8d9869403b9854b6199848610498386cf697ebea0897cb439c97a53cfb97a4f387969aeb72967fbfcb963ca10f95daf82895d8122595b38752954bc9dd9515305d94f67b1894b8834e94ad8e5d
  | 6, 19 => 0xb62fb22db5995d73b58b0cf8b4d0e6a0b4d0d4a4b3fad78cb3c54e5cb391ac48b32c8cd9b31e2f22b2e06130b2d40c22b272d876b2700fdcb258530ab2238cf2b0dde46bb064a705b0433de6b03646e7b002dcf0afdc9ea7af136d71aeff15d3aebe772fae61e220adf98b14addfe763adc2c79eada8d4f1ad7309f1aca9b064ac54c35babf06f62abbd86cdab676f4faaa90063aa760e5faa1f6e87aa032758a97e6899a964496fa95dfcd0a95d0e24a909e4c1a8f6772ea8e78fc4a8afe02ea89bce41a8962102a7e9f7b1a7c82b51a748d152a69d5214a685bbbaa6563cc3a634fa8aa60c4fd4a603d2e3a602287da5cf7206a5323c56a49fea3ba3d787f2
  | 6, 20 => 0xcbae6cbdcb868911cb71c13acb668644cb3988b3cb22a6e0cac50cf0ca1c68dcc9ee7b2ec9e9833fc94fa081c92341aec91a9764c8924c88c885719dc7bdffc1c7327c7fc6d0b208c6c817b7c6a9d361c69fce5ec63e6ab8c5c2d3b0c59d6c30c4d20e6dc48fe98ec4745ea1c4232d1ac41ed601c3d7b039c3675414c3334588c2f91008c2afde01c10e3d6bc0e8397bc05fc100bfb4dd66bf98043bbf940a1ebf8705ebbf82112cbec0a575be4bb0d8bd9159b9bd47dfdabccba248bbe2947cba694344b9d0b111b932cbabb93206deb8ef4caeb8767b00b8025b3bb7b26079b7ae1533b7a1fd24b78864c3b72f93ffb717dd2fb6526912b65207bab64ecbd7
  | 6, 21 => 0xe5d68d5ae5a66be6e50a6e51e4d154f8e3333fdfe2ee6b60e2b58d36e277b2dee254a19ee23cf087e1ee1201e1cc7a45e1280a33e0d18bdae0800c8ddfe44f4adfbea839de86f571ddb7dd18dd9de376dc1c3838db83fe16db70dd00dafef9a9daf2339cda60bae0da4c29ccda389489da1bab7ed9fb6b94d9f6b427d9de0ce9d9c29a4fd8f800a3d8c3f1bfd8c1607fd89aad76d85d0165d7f9e631d7adc8ffd6e908b3d6e8f3a9d673d0cad670e039d568b144d4e47617d4d630b5d45c14ced3e51ce2d2def3e9d2aeea40d22c953bd20af5b0d1f83001d1a278a6d02e62c1cfafaacccfaaeb5dcf78f9d1cee24fd2ce96c38ece5c094bcdfcc0dfccc7daa6
  | 6, 22 => 0xfd058035fbefb591fbe0f7e9fa4ce404f9b99d75f96feb04f9414bd9f8a016c6f886c565f7e67915f7a45692f5735d60f512f24df47b8ceef4642245f4535bf8f2854adff193a1eff12be4b6f0f8df95f0158209eff86bc5efefa548ef75fb71ef5b4d9feec40f0cee8f1728ee8c0f30ee365bcfee02495bedb06ad3ed805da7ed0092ebec9d1042ebc7f551eaf7f023ea39bfe6e8623c33e82d725ee8027d18e7a75556
  | 7, 0 => 0x129997eb124e26351232479711ed84b711eb7ccf1187183a11761aa81142fa411134c93410c280c5103ead2a0fc22fb60f3badb20edd17080ea68d810e783ebe0df078900d9cbe430d9a92370d52c9a60cf91d9f0cea20e10c2cfbb60c167f100bd753a90bb2ffb10b989d440ab7b9ae0ab0afbb0aa9dacf0a9628be0a71f9560a172c4907d82e3c07bd347d075140fd06ecbabd06c7654b0663442506556796065223ce064612c705ad2f3405a3eb0a059e8b1705869eb105169eb003f1b95203e364540360127103476202033a727c02e9d44b02d5abde0296f5790291d00a024a740d0188fb4b0129b75501013f3600dd496a0064991500368d3900103def
  | 7, 1 => 0x22daf26b225c733222543c1c2236825921b9f7ae21a5f96821a1d2672064873a2046aaad203e530f1fe039d21fd3d3851fb72b911f608b651ee4e3db1ebb13731eb3facb1e8eec381e7359ed1e1aa3ae1e08e1531d89743f1d73f5661d29fe0a1d094b741ca0b1831c53b96d1bea35011be841c11bde45011bbbe6161b8548e61b61a0cd1b52f3321b2d157f1ac4a36f1a974b451a90e4691a45ab1d1a4058c31a2bfa9c19f08aad19e360491979f41718e3fb0a183e830517d7cb9517a820261729918f170db67f16d8a81c15ff8a4715f86a801581f8c81561a43a1528ba3c1460a7d914121a0c136d10ac1317dd2b130748e512baa67712b8ab4112ae5da3
  | 7, 2 => 0x3678c0eb366fa272361b1af435d89aaa359275fc357bcd5735743559355e29ce3518dab134e1dc033481847a33d93c6b339be83033193e9a3294bf40326a06213243d5cd31381b073055c0a62fa1c82a2f5be1482efbd9642eedfa852ee51d392ea0b9112e9e70832e8ed5cd2daad2e42cf3c0ef2cae27f22ca821632c1543872bdd94e82bcf9a012ba0a43a2b0f56702af4104e2a60bc7d2a5e00e12a5175e429f0f18429c478db2964176b2889888f2882e2b2284db2db2838c79a2775450f2752ae7526e36c2426d2458e26d0c80326aa53c3265363bb264ea12126396ad4262d41fb25bece64259eb530258a6ea4255ffecb24a7e76c2485a93423fe6fae
  | 7, 3 => 0x4b7591cb4b62f61f4b40518f4aee73794a59283648fa38cc48f889f848f0bd7d48ebd2aa472e33c146e1bded465e79d545f6b584457c5ed145179a8f44d9dfff43cee64d43b9f0a343b425714365b3a943555fb0433f660a432891ef42b779a3425327d74223bdb94215deda41d9fb7841a4b5d6413f306a413ca69640db2d8b40455b7a3f086e6d3ee6de3d3ebd45083e9c5ebb3e277fff3dc32c533d8620523d6054973d0124c93cedcf813c9f3cdf3c52b0633c39fd5e3bc2d8a43b5624293b3c318a3b23954e3a8b1a653a861c9939de879e38ad846e3899ed1837dd7e8037a1ed1c379a6182378f31e83724f45b36f4981f36c744ae36b6da9236ad5160
  | 7, 4 => 0x5e06e6065d9647d45d93d62e5d6275f45d23bf8f5b4388f85a73054d5a437adf59f223e559e5330159d66aa05992adb05923c1c65916f5625905159658a5f17757c3519856fffaeb56da22f056abec62568ff7f155df5df855bb43f755ab6c46558b875054ed1c7554c1de105342fdb75316929452f2fea452e996fb52de426a52acbe7d52943af55275541c520a3fab51ee61ea51e81d5151a4e007516924ff515c2919514f645451007c3a50c9577f5059633d4f9b055d4f8c57c24ed5e3f64e7327324e5bae794e1db72a4e0e9fc94de27c5e4dd111674dc27b5b4d2b306b4d0476064cd8ba054ca60af44c4c79c44c1e35cd4c173de94c1326ad4bb13b21
  | 7, 5 => 0x791d9b41791304537900675a77d135d07770373f7733bc5377211a3f76eecc3f764e5f6174f2245d73a4532b7341d2fd73227b8e72b2833971fb25a271be65bd714a8ba9710f96de70c4152b707cee8d706753917005f1236fa6c90d6e9f1e276e1ad9ba6d5cb0976bcf90f36bc490ee6b46b4d16af785736aa2ab606a4fc62d69f5d2f969c031bf69bac968692e70ee68ff5c7d688d1b5567425c61668c47706659a12a6635754264ffcc4e64cf00c564789948638147926347643b633af011633635116292bf226240ab8761f427ee61ca400860d158046001a2b65fd513de5fbac6fd5f2a63495ec6f1c75ec2fe405ebcebc25e90082e5e22a7545e1657ce
  | 7, 6 => 0x996c23f4992c6790984899db9713ecb197012b849690ba6e965f3458965531e6963c456d956125c6955a089894331b65917fb21d913f544191015b8b906d26119011f582900c69668fa2db658f46f2108dbfa66d8d92f6958d6bb4b28c1a6ee88b7e195e8b3e939c8b308e208a7994f88a59f30f89beef4c897643b6886bb2a587ec230287080352868cb424862851b98562e8728558bace851cbe16850f030e83c5bc5283833bd7834a6d9383233d80830766bf82ddd8a582d3eb998276397282739f208241b05982121d0d7fe35f827fc0036d7f97da8d7ebbf6017dbaea3c7db1e1917d303bbe7cfde4937b25f4ae7ae97d0f7a2bf43679c9043d798a90b2
  | 7, 7 => 0xdf7fbf91dd9de376d958a3e4d8e7dfa1d6890d25d5d7c256d3b34341d355d4ffd0e5095fcfca0951ceeb1ad8ce8cc780ce6b8b90ce412b29cda803e7cd5fbf4fcc0b8b0bc9d46458c707ac1ec61b5c10c59d6c30c4d4624bc4ac2c82c2afde01c1c6e06ec16463c6c150c440bf46884bbf4172fabef1afedbe107ab6bcc8e334bc5e25f5bc008a33ba2399e2b959c3c0b85c2f59b7610a65b55b444cb23cd636b22e7c90b0480e0db031ca64af935789aec64c0ead85a160abe5308aaa3f12b1aa21bb6da95dfcd0a909e4c1a8e78fc4a6563cc3a62fa927a35f8a0fa302d5f5a0c045e2a07b39919eab30d29e6bbe4b9da1794d9d3508f49c36144f9a81c9ca
  | 7, 8 => 0xfd75d7f8fbefb591f9091127f646c3bff5596f20f11d8484f0c5c7cbf05fc8f2e9599105e7199440e5d4dd4ce33582dbe1c2a466
  | 8, 0 => 0x55df5df84f8c57c21e7359ed1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0xc81050011810440300001181044030000118104403000011810440300001181044030000118104403007210d5150c4007110125500400
  | 4, 0 => 0x1181044030000184405003000011801404300001884350c30000000255002040000005504202001181044030000000000000050011810440300001183248c30000000255002040011810440300001884350c300000005210d2010010d5150c3000000025504202000c5454c430000000055042020018c425083000018c4250830000118104403000000010440200000002550420200000001091020011401041300000005050820300118324c830000000255042020000001404200000000008110400118104403000000000108103
  | 4, 1 => 0x118324c830000000104402000000035508201000003550820100118324c8300000001004120000000000c810500105355043000000050508203001181044030000000000c8105000004500520000118104403000018440500300000001044020000118104403000000000081106001181044030000000355082010011810440300000005210d201001804150430000118104403000000010440200000005210d20100000000000060011401041300000001550020400000001081017310950508400
  | 5, 0 => 0x10810100000001001040000025500200000000008c1050000000000000000000000000800000000000010000000000002000000000000800000000000010000000000007000000008510200000000c9102000004508120000000510812000000000000004000005210d20300000000000020000000000008000000000000300000504c8200000000000000800000000000010000000108101000000000000700000454802000000000000005000002550020400000204802000000045081200000000010010400000000c8100
  | 5, 1 => 0x10d102000000010d10100000001081010000000000001000000000000300000000000010000000000008000000000000600000000000020000000000007000004548c2000000000000001000000000000100000000841030000000000003000000010810100000531092000000000100101000000010010100000000000020000000000001000000008110600000000000080000001041200000000010d1010000000081106000000010510400000000000010000000000006000000000000000000415042000000000108103
  | 5, 2 => 0x15500204000000000000000000000000000000025440200000000000000600000450412000000000081106000004504120000000014042000010d5150c3000000000000005000004500520000000001081010000025500204000000010d1010000001041200000000010d101000000000000700000450852010000000081102000000000000700000000000050000000000002000c5454c43000000000000001000005148c200000000000000000000000000030000000100101000000000000500000000000010000000000000
  | 5, 3 => 0x100101000000010d1030000000000003000000010d10200000000851040000000081106001012550030000000324c82000000045041200000000000000100000214842000000000000007000000008510200000000c910200000000811040000000000001000000010810100000000c91040000000104102000000010d104000001044020000000000000060000000000003000002550420200000000c91030000000000006000000000000500000014042000000000000005000000008110400000501052000000010440200
  | 5, 4 => 0x1404200000000140420000118324c8300000000000000700000000c51060000050105200000002544020000000354042000000000109102000000010d102000000000000600000001091020000000000005000002550420200000350812000000025404200000000008510200000000c91020018c42508300000004250820000000214842000000045041200000000000000700000304c0200000000008c105000000000000100000304c02000000000108103000005148c2000000025440200001884350c300000000010d104
  | 5, 5 => 0xc810000000324c820000000001081030000000000005000000000000200000454402000000010440200000004544020000000001091020000045081200000000010410300000001081010000000000002000000010d103000000000000600000000c510600000001051040000000000005000000000000500000504c82000000000000005000003540420000000000000070000000000006000000000000700000450c520000000000000080000000000005000000010810300000000000080000000000008000000010d104
  | 5, 6 => 0x800000000851010000010440200001181044030000000000000080000000000003000000010d102000000010d10200000000c8105000000000000700000204802000000045081203000000000000100000001091020000000081106000001044020000000000000050000045041200000004050020000000454c8200000000000000700000250c52000000053109200000000000000300000104402000000000000005000000010d10100118324c830000000454c4200000000004110000000000000000000000000008
  | 5, 7 => 0x10810100000000c5106000005050820000000000000010000000000004000000340c20000000000000050000000000001000000010d102000000008c1050000000000004000000000000000000000000000000000080101000000000000000000000000020000000004100000000000000600000454402000000000000002000000000000700000000000000000000108101000000010810100000000000020000045041200000004508520100000504c820000118324c83000000000000001000000000000400000454c4200
  | 5, 8 => 0x410000000000000030000051508201000000000000700000000c8105000000008510200000000c910200000304c02000000000000002001884350c30000000000000000000000081104000000010d101000000010d1020000000000007000000010510400000000851020000000000007000000000000500000450c52000000000000007000002550020000000000000000000045041200000000000000700000000000000000045081200000000000000600000450c920000000001081010000000000005000000010d104
  | 5, 9 => 0x50105200000000000000700000000000070000000000005000004504120000000500c52000000000108103000004350c2000000000109104000000000000000000000c910100000000c8105000003550820300000000c8105000000008110200000150812000000000109104000000104120000000415042000000000000008000000010d101000000000000700000000000050000000000001000000000000500000415042000000000104102000000000000700000504c82000000045081200000000000000100000504c8200
  | 5, 10 => 0x8c105000000010d102000002540420000000000000000000020480200000000010410300000001081030000000000008000000000000200000001081010000045005200000002550020400000000000060000000000000000000010810300000000000070000000101102000001044020000000000c91030000000000006000000000000100000520c520000000000811060000001404200000004050020000000000c91010000000000004000005204d2000000000108101000000000000800000000000020000000000007
  | 5, 11 => 0x450412000000000000007000000010510400000450c920000000000000070000000000005000000010d103000000008510400000001011020000000104102000000008510400000000000000000000081104000000008010100000000000020000000000006000003248c2000000045041200000000010410300000000000050000000000007000000000000300000000000080000000000000000000010d1010000045041200000000010810100000000000000000000108103000000140420000000001081010000000000008
  | 5, 12 => 0x1044020000000250c52000000053109200000004350c2000000000000008000000000000700000000851020000000000007000004504d20000000000000010000000108101000004504120000000314c42000000000000006000000010410300000504c82000000000000001000000000000100000000000070000040500200000000140420000000000000030000000108103000000000000500000001081010000000000001000000010810100000000000010000000000001000000000000000000450c52000000025500200
  | 5, 13 => 0x108101000000000000700000500c5200000000010d1010000000000007000000010810100000450c920000000000c9103000000010d1040000025440200000005210d2010000045041200000004504120000000000000010000000000001000004544c200000000000000600000000000070000041504200000000000000700000000000020000045480200000000000000400000000000020000021484200000000010810100000531092000000000000006000000008510100000104402000000000000005000004548c200
  | 5, 14 => 0x70000045085201000000010d102000000010d10100000000000070000000085104000005110120000000000000020000041504200000000000000300000304c0200000000000000800000000000000000000048103000000010d1030000000000001000000000000100000000c8105000000010110200000314c42000000000000007000000000000500000000000080000000085101000000010810100000454402000000000000001000000010d101000000000000600000001051040000000000002
  | 5, 15 => 0x7000000010d10300000450412000000000000008000005048c2000000000100101000002048020000000000000010018c4250830000000000000020000000000005000000010d104000000000000600000000c8105000001550c20000000154c8200000004548020000000000c910200000000c9101000000000000200000250c52000000000108103001884350c30000000000c51060000000000000000000000000500000250c5200000000104120000000000000070000000105104000000010d104000000010d101
  | 5, 16 => 0x118324c8300000000010d102000000000000000000001081010000000000007000000000000700000000c910100000000c8105000005004d200000004350c20000000000000060000000000006000004350c200000000000000700000000c91030000000108103000000010110200000000000050000000108101000000008c10500000000000050000025500200000002550020000000454042000000010440200000004508d20000000324c8200000000010d10100000000041000000010440200000000010d10100000000c8105
  | 5, 17 => 0x8c10000000104402000000020480200000002348c200000000000000500000000000070000010440200000000010d1020000000000000000000000000700000000000060000000000008000000000000500000001081030000000105104000000000000100000000c9104000000004010000000001041030000000000003000000000000300000000c810500000454402000000010440200000000010d10100000000851010000002408200
  | 6, 0 => 0x1000000000000300000304c02000000000000006000000000000100000000061000000000000005000000010d10200000000000020000000000006000000010d1040000000000005000000000000700000000c5100000000000000500000000000060000000000005000000000000500000001011020000000000002000000000000300000000000020000000000005000004508120000000000000050000000000006000000004010000000000000020000000000005000000000000200000000c9102000004350c200
  | 6, 1 => 0x1081000000000085101000002348c20000000000000010000000000008000000010d10200000450052000000000000008000000008010000000000000050000000000000000000000000200000000811020000000000001000000010d10300000454c420000000000811000000000000006000000000000600000000000080000000000003000000000000500000000851040000000000001000000010d1040000000000002000000008410000000000000060000000000004000000000000500000000000020000000000000
  | 6, 2 => 0xc81050000000000006000000008c1000000000041100000000000000600000001041020000000085100000000000000600000000000080000000000005000000010110000000000000010000000000004000005210d2000000000000007000000010d1010000000000000000000000000300000000000010000000000002000000010510400000000000050000000040100000000000000500000000000030000045404200000000000000800000000000060000000000004000000000910000000000000040000000000006
  | 6, 3 => 0x8010000000450412000000000108103000000000000200000000c81050000000000007000000010010100000001011020000000000005000000010010000000000000040000000000004000000000000300000000000030000000084103000000000000100000000000040000000000004000000010d101000000000000300000000000030000000000004000000000000300000001081000000000002100000000010d10300000000000050000000000001000000000000100000000000010000000085101000005148c200
  | 6, 4 => 0x20000000000007000000000000200000000000010000000012100000000000000700000000c91010000000000006000000000000000000000000060000000000003000000000000500000000000030000000000005000000000210000000000000040000000000003000000008c10000000000c01000000000000006000000000000200000000000060000000000002000000000000600000000000010000000000001000000000000100000001001010000000000006000000000000400000324c82000000000000006
  | 6, 5 => 0x5000000010d1010000000000003000000000000600000000000080000000000004000000000000200000000401000000000108103000000000000400000000000030000000000007000000000000200000000c910100000000000010000000000007000000000000400000000411000000000000001000002148420000000000000010000000000004000005148c200000000010d10200000000c81000000000000001000000000000200000001051000000000000000000000000000100000000801000000000000004
  | 6, 6 => 0x10d10100000000000020000000000000000000000000400000000000020000000000001000000010410000000000000070000000000007000000000000600000000000050000000000003000000000a1000000000000001000000000510000000000000050000000000007000000010d104000000008010000000000801010000000002100000000000000000000000000060000000000001000000010d10100000250c5200000000000000000000000000060000000041100000000010d10300000000000060000000000004
  | 6, 7 => 0x300000450c52000000000000004000000000000200000000000040000000000005000000000000500000450c920000000450412000000000000005000000004010000000000000010000020480200000000000000000000000000050000000000007000000000000600000000000030000000000007000000000000000000000000030000000000004000000000000200000000000010000000000001000000010010000000000000000000000000001000000010c10000000000000040000000000006
  | 6, 8 => 0x30000000000008000000000000000000000c1100000005148c20000000000000040000000012100000000010d1010000000000003000000000000100000000000040000000006100000000000000200000000000000000000000001000005310920000000000000040000000000001000000000a10000000000000040000000000001000000000a1000000000000006000000000000300000450c520000000000c4100000000000000400000000000060000000000000000000000000700000000851020000000000002
  | 6, 9 => 0x500000000000060000000000006000000004010000000001041030000000000005000000000000200000000000050000000000001000000010d10200000000000070000000000002000000010d10400000000c510000000000000030000000105104000000000000300000000000070000000000004000000008010000000000000060000000000008000000000000400000001081010000000108101000000010d10300000000000050000000000008000004548c200000000008510100000000000000000000000003
  | 6, 10 => 0x700000000000020000000000001000000000000600000454c820000000000000010000000000005000000010d102000000000000000000000000000000000000001000000000000000000531092000000000000007000000000a1000000000000001000000010d10200000000000040000000000001000000000000700000214842000000000000001000000000000500000000000020000035504200000000000000300000000000060000000000002000000000000300000000811040000000108100000000010d102
  | 6, 11 => 0x60000000000001000000000000100000000c9103000000008110400000000000010000000000003000000000000300000001001010000000000002000000000000400000000000020000025500200000000000000000000000801000000000000004000000000000100000000c1100000000008c1000000000000003000000000000600000000000060000000000006000000000000300000000000050000000000005000000000000400000000000040000000100100000000008110300000000000020000000084103
  | 6, 12 => 0x20000041504200000000010d104000000000000800000000000050000000000005000000000000400000000000080000000000003000000010d101000000000000600000000000040000000080100000000000000100000000000010000000000003000000000000200000001041000000000000008000000000000300000000000060000000000006000001044020000000000000030000000000006000000000000400000000000050000000000006000000000000400000000000020000000000005000004350c200
  | 6, 13 => 0x610000000000000000000000081100000000000610000000000c0100000000000000300000000000010000000000001000000010d1010000000000006000005210d200000000000000100000000000010000000000005000000010d10400000000000060000000109102000000000000100000000000000000000002100000000010d101000000010d1020000000000003000000010d101000000000000600000000000060000035404200000000000000400000000411000000000002100000004350c2000000000000006
  | 6, 14 => 0x700000001041000000000000003000000000000300000454c42000000000000006000000010d101000000000000400000000000070000000000001000000000000000000000000010000000000002000000000000500000314c4200000000000000600000000000010000000000000000000000000200000000000080000000104100000000000410000000000000080000000000007000000000000400000000c4100000000010c10000000000121000000000085101000000000000300000000000020000000000003
  | 6, 15 => 0x500000000000020000000000000000000000000500000000021000000000000002000000000000600000000061000000000000001000000000000100000000000020000000000001000000000000400000000000030000000000004000000010410000000304c020000000000000020000000000001000004544020000000000000010000000000003000003508120000000000000080000000000001000000000000400000001041000000000000002000000000000000000000000070000000000002
  | 6, 16 => 0x100000000000060000000000000000000000000100000000000010000000000007000000000000300000001091000000000000003000000010d10400000000c0100000000010410300000000000010000000000005000000000000500000000000010000000002100000000000000700000000000010000000000006000000008c10000000000000060000035504200000000000000400000000000040000000000004000000008010000000001081030000010440200000000000000500000000000010000000101103
  | 6, 17 => 0x610000000000c110000000000801010000000000005000005010520000000000000010000000000003000000000000500000000000080000000041100000000000a1000000000000002000000000000500000000c9104000000000000600000000021000000000000003000000000000600000000c910000000000000010000000108101000000000000700000304c0200000000000000200000000000060000000000004000000000000800000000000020000000000001000000010d10100000000041000000000000006
  | 6, 18 => 0x10010000000000000060000000000008000000000000700000000811020000000000004000000000000200000000000040000000000003000000000000300000001041030000000000001000000000a10000000001041000000000000006000000000000600000000000050000000000006000000010d1000000000000001000000000000000000000000050000000040100000000008510000000000000020000000000004000000000000700000204802000000000000004000000010010100000001091000000000000000
  | 6, 19 => 0x1000000000610000000250c520000000000000020000000109104000000010d101000000000000500000000c5106000000000000100000254402000000000100104000000000000000000000c51000000000000002000000000000200000000000030000000000001000000004010000000000000010000045005200000000010d10400000000000080000000000000000000000000000000000000050000000000006000000000000600000000491000000000000001000000010d10100000000000010000000000002
  | 6, 20 => 0x30000041504200000000000000800000314c4200000000000000400000000000040000000101103000002048020000000000000030000000085101000000010d10300000000000040000000000005000000000000300000000000050000000000006000000000000500000000000050000000000008000000000000500000000000020000000000007000000000e10000000000000020000000000000000000000000400000000000030000000000005000005148c200000000008c10000000000000050000000000001
  | 6, 21 => 0x100000000000020000000000006000000000000400000000000030000000000002000000010d10100000000000020000000000001000000000000400000000000050000000000001000000000000400000000000020000000000002000000008510100000000000060000000000004000000000e1000000000000003000000000000200000000000030000000000001000000010110000000250c52000000000000000000000000000300000000000060000000000002000000010d10300000000000050000000000003
  | 6, 22 => 0x30000000000001000000000000300000000000050000000108100000000000000600000000000050000000000004000000000000400000000000030000000000002000000000000800000000000070000000000005000000000000600000000041000000000000000000000000410000000000000030000000000004000002048020000000000000080000000000000000000000000800000000000070000000006100000000000000500000000841000000000000002000000000000600000000000060000000000001
  | 6, 23 => 0x41504200000000000000300000001081010000000000001000000000000100000000000070000000002100000000000000100000454c42000000000000001000000000000000000001001010000000000001000001044020000000000000060000000000002000000000000100000000000030000000000003000000000000800000000411000000000081104000000000000300000000000050000000000005000000010c100000000000000300000000051000000000000004000000010410000000000000010000000000001
  | 6, 24 => 0x4000000000000600000000000050000045081200000000000000600000000000070000000000005000000000000500000000000070000000000006000000000000400000000801000000000000000000000000a1000000000000000000000010d10100000255002000000000000003000000000000800000000c4100000000001210000000000c9104000004548c2000000000000001000004508d2000000000000003000000010d10200000000000040000000000002000000010110000000000000040000000040100
  | 6, 25 => 0x30000000000006000000010110300000000000020000000000007000000000000100000000000020000000000001000000008410000000450c52000000025500200000000000000800000000000000000000000001000000004110000000000000000000000000001000000010d1040000000000002000000010110200000450c920000000000000020000000041100000000000a1000000000000007000000010d10300000000000020000000005100000000010d10100000000401000000000000001
  | 6, 26 => 0x2000000000000200000000000040000000000001000000000000500000324c8200000000010d104000000010d10100000000000000000000000004000000010c100000000010c100000000000000000000000c110000000000851040000025440200000000010d102000000000000100000000000070000000000005000000000000200000001081010000000000005000000000000100000000000050000000000001000000000000300000000000060000000000006000000000210000000000c01000000000080100
  | 6, 27 => 0x100000000000000000000000004000000010d1030000000000008000005210d2000000000000001000000000000100000000000020000000000006000000000000400000000000010000001404200000000000000800000000000030000000108101000000010d100000000000000200000000121000000000080100000000000000500000000000050000000081102000004350c20000000000000030000000000005000000000000600000000000070000000000008000000000000600000000000040000000000001
  | 6, 28 => 0x40000000000005000005148c2000000000100101000000010d10200000000121000000021484200000000004c10000000000000050000000000003000000000000100000000000010000000000006000001044020000000000801000000000000003000000000000600000000000010000000108101000004350c2000000000000005000000010010000000000000080000000000002000000000000000000000000040000000000006000000010d1020000000000004000000004010000000000000080000000000001
  | 6, 29 => 0x8000000000a100000000010810300000355042000000000000001000000000000500000000851010000000000001000000010110000000324c82000000000000001000000000000500000001001000000000000004000000000000100000000000060000000000006000000000000500000000000000000000000001000000000000200000000061000000000000006000003508120000000000000050000000000006000000008110000000000000050000000000004000000010d10200000000000060000000000001
  | 6, 30 => 0x80000010440200000000000a1000000000081100000000000000400000000000020000000000000000000000000500000001041000000051081200000000000000100000000c81050000000000006000000000000500000000000030000000000002000000010510100000000841000000000000004000000000000700000000000010000042508200000000000000000000000c9100000000000000500000000000070000000012100000000010d1010000000000001000000000000500000000000040000000000006
  | 6, 31 => 0x84100000000000000600000000000050000000000004000000000000700000000811000000000000001000000000000800000000000010000000000000000000000000600000000000020000000000007000000000000000000000000010000000000007000000000000700000000000050000000104102000000000000300000000c910100000000000020000000000000000000000000500000000000010000000000006000000000000600000000000040000000000005000002544020000000000841000000000109104
  | 6, 32 => 0x70000035404200000000000000100000000000010000000081102000000010d101000000000000400000000000010000000000001000000010d1010000000000004000000000000700000000000010000000000005000000000000100000000000020000000109100000000000000200000354042000000000000002000000010810000000000000080000000000002000000000000100000000801010000000000007000000000000100000454c82000000000105104000000000000400000000000020000000000002
  | 6, 33 => 0x100000000000010000000000001000000010d102000000010d10100000000000060000000000004000000010d103000004150420000000314c420000000000000040000000000004000000010d102000000000000500000000000060000000002100000000000000600000000000070000000000004000000000000100000000c810000000000000000000000108100000000008510100000000000060000000000006000000008c10500000000000070000000000005000000000a1000000000104103
  | 6, 34 => 0x10810100000000000030000000000003000000010d10200000000000050000040500200000000004110000000000000080000000000004000000000000100000000000070000000000003000000000000200000000c010000000454c4200000000010d1040000000000001000000000000700000000000080000000000003000000000000000000000c1100000000000e10000000000841000000000000001000000000000200000000000010000000000004000000000a100000000000000400000000000040000000000003
  | 6, 35 => 0x10410000000000000050000000000001000000000000100000000c0100000000001210000000504c820000000000000020000000000002000000001210000000505082000000000108101000000000000600000000000010000000000007000000000000600000000121000000000000003000000000000600000000000010000000000002000000000000500000000c8105000000000610000000000000080000000000001000000000000800000000000020000000081100000000000000400000000000040000000000004
  | 6, 36 => 0xc91030000000000002000000000000200000000000020000000000005000000000000600000000000040000000000007000000000e100000004508120000000001001010000000000002000000000000300000000c8105000000000000500000000000080000000000006000000000000100000000000060000000000008000000000000000000000000060000000002100000000000000200000000000080000000000004000000000000700000000000070000000041100000000000000500000000000070000000006100
  | 6, 37 => 0x20000000012100000000010d1040000000000003000000000000200000000000060000000000005000000000000800000000000070000000000007000000000000500000000000020000000000003000000000000600000000000030000000000005000000000000600000000c910000000000000070000000000007000000000000600000000000020000000000004000000010d10300000000000020000000000001000000010d10200000454802000000000000002000000000000300000000000060000000000000
  | 6, 38 => 0x100000000000060000021484200000000000000300000450c9200000000000000100000001081010000000084103000000010810100000000000030000000040100000000000000200000000000040000000000002000000004110000000000000030000000104102000000010d1030000000000005000000000000200000000000020000000000005000000000000000000000000060000000000003000000000000600000000401000000000000002000000000000800000000000060000000000005
  | 6, 39 => 0x300000001041000000000000005000000000000200000000c010000000000000010000000100104000000008410000000000000050000000000006000000000410000000000000040000000000004000000001210000000000c91000000035081200000004150420000000000121000000000000004000000000000800000000000050000000000004000000010d104000000008510100000000000070000000000007000000000000500000000000000000000000002000000000000400000000000060000000000007
  | 6, 40 => 0x10910200000000c8100000000008010100000000000070000000000004000000000000500000001011000000000000005000000000000600000000000010000000000002000000000000600000000000040000000104103000000000000100000000000010000000000007000004544020000000000000070000000000001000000010d10100000000000010000000000001000000000000100000000000050000000000001000000004110000000000000040000000000006000000000000600000000000050000000000004
  | 6, 41 => 0x5148c20000000000000050000000000001000000000000200000001011000000000000005000000010d103000000010810100000454c420000000000411000000000041100000000000000100000000000030000000000002000000000000100000000000060000000000006000004544020000000000000030000000041100000000000000100000000000020000000000001000000000000100000000000040000000000001000000000000400000001011000000000000003000003540420000000000000070000000000000
  | 6, 42 => 0x61000000000000007000000000000700000000c810000000000000000000000000002000000000000400000000000020000000000000000000000000600000000c1100000000000000300000324c820000000000000030000000000005000000000000500000000841030000000000004000004544020000000000c810000000000c810500000000000040000000000000000000010d10200000000000010000000000002000000008110600000000000000000000000008000000000000100000000000070000000002100
  | 6, 43 => 0x800000000000050000000108101000000000000100000000000000000000000005000000000000100000000000060000000000001000000010d102000000000000500000000000030000000108101000000000000500000000000060000000000002000000000000100000000000050000000000003000000010810000000000000050000000000008000000000000300000000c1100000000000000600000000000060000000000006000000008c100000000010d104000000000a10000000000000040000000000003
  | 6, 44 => 0x50000000000000000000000000600000000000000000000108101000000000a1000000000000000000000001210000000000401000000000000002000000000000600000000000020000000000005000000000c1000000000109104000000000000000000000000040000000000007000004050020000000000000060000000000007000000000000500000000000060000000000008000000010d10100000000c8100000000008d10000000531092000000000000000000000000000200000000000040000000005100
  | 6, 45 => 0x100000000000060000000000006000000000000700000000000070000000000005000004504120000000000411000000000000007
  | 7, 0 => 0x20000000000006000000000000800000000000000000000000002000000000000500000000000000000000000003000000000000300000000000010000000012100000000000000100000000811000000000000004000000000000200000000000020000000000002000000000000500000000000060000000000002000000000000300000001041000000000000008000000004110000000000000030000000000006000000000000100000000000000000000000000000000000000200000000000000000000000000
  | 7, 1 => 0x5000000000000400000000000020000000000006000000008110000000000000020000000000003000000000000000000000000010000000000006000000000000000000000411000000000080100000000010d100000000000000000000000000040000000000006000000000000100000000000010000000000004000000000000700000000000030000000000004000000000000200000001091000000000000000000000000000100000000c4100000000008c100000000001210000000000000050000000000001
  | 7, 2 => 0x21000000000000001000000000000300000000000050000000000002000000000000300000000000030000000000001000000000e100000000010d100000000010110000000000000050000000081100000000000000500000000000060000000000005000000000000100000000000030000000000001000000000000000000000000060000000000001000000000000200000000000060000000000002000000000000000000000000060000000000005000000000000400000000000050000000000001
  | 7, 3 => 0xe10000000001041000000000000001000000000a1000000000000000000000000210000000000000010000000000002000000010510000000000000000000000000005000000000000000000000000020000000000005000000000000000000000000050000000000004000000000000300000000000000000000000001000000000000400000000000060000000000000000000000000600000000000020000000000001000000000000100000000000010000000000003000000000000400000000000040000000000004
  | 7, 4 => 0xc81000000000000001000000000000400000000000060000000000002000000000000200000000000050000000100100000000000000600000000000010000000000001000000000a10000000000c01000000000006100000000000000100000000000020000000000002000000010c10000000000000040000000000005000000010110000000000000030000000000001000000000000400000000000050000000000008000000010810000000000061000000000000001000000000000500000000000060000000100100
  | 7, 5 => 0x50000000000001000000000000100000000000050000000000006000000000000000000000000040000000000002000000000000300000000000000000000000001000000000000300000000000010000000000005000000000000500000000000010000000000006000000000000200000000c11000000000000003000000000000000000000000030000000000005000000000000500000000061000000000000004000000000000000000000000030000000000000000000000000000000000000040000000000000
  | 7, 6 => 0x200000000000040000000006100000000000000000000000000050000000000004000000000000300000000c110000000000000050000000000000000000000000400000000000000000000000001000000008510000000000121000000000000006000000000000000000000000080000000000002000000001210000000000000000000000000002000000000a100000000010910000000000841000000000000001000000000000000000000000050000000000002000000000000100000000c81000000000000008
  | 7, 7 => 0x40100000000000000700000000000040000000000006000000000000500000000121000000000000001000000000a1000000000000001000000004110000000000000060000000000006000000000e1000000000002100000000000000000000000c910000000000000010000000000000000000000000300000000000050000000000002000000000000000000000000000000000000000000000000000200000000c4100000000001210000000000000040000000000002000000000000400000000000010000000005100
  | 7, 8 => 0x21000000000000003000000000000000000000c910000000000000010000000000003000000010810000000000000030000000000007000000010d100000000000000300000000000060000000000000000000000210000000000000000000000000002000000000000100000000000020000000000004000000000000300000000000050000000085100000000000000100000000000060000000000003000000000000100000000c510000000000000020000000000001000000000610000000000000060000000000003
  | 7, 9 => 0xe10000000000000010000000000001000000000a10000000000000010000000000004000000000000100000000000050000000000006000000000000100000000c51000000000000006000000000000800000000000040000000084100000000004010000000001011000000000000005000000000000000000000000020000000000006000000000000000000000000050000000000008000000000000400000000000020000000000004000000004110000000000000070000000000002000000010c1000000000000005
  | 7, 10 => 0x30000000080100000000000000000000000000080000000000001000000000000000000000000000000000012100000000000000600000000841000000000000003000000000000200000000000010000000000000000000000000100000000000080000000000003000000000000300000000000050000000000000000000000000400000000000040000000000005000000000000200000000000000000000100100000000000000600000000000000000000000001000000010510000000000000000000000101100
  | 7, 11 => 0x811000000000000005000000000000100000000000020000000000004000000004010000000000000000000000012100000000000000200000000c110000000000000060000000000007000000000000100000000000060000000000006000000000000400000000000000000000000003000000010110000000000000000000000000002000000000a100000000000000700000000c110000000000000030000000000000000000000000000000000000000000000000002000000000000000000000000050000000000003
  | 7, 12 => 0x500000000000020000000000005000000010d10000000000121000000000000000000000010c1000000000000001000000000210000000000000050000000000005000000008d10000000000c01000000000000006000000000000300000000000020000000000004000000000000100000000000000000000000002000000000000300000000000050000000000004000000000000200000000000030000000006100000000000000100000000000000000000000006000000000000100000000000050000000000004
  | 7, 13 => 0x200000000000000000000000005000000000000300000000000010000000104100000000000000100000000000010000000000005000000000000400000000000010000000000002000000000000200000000000060000000000005000000000a1000000000040100000000008010000000000000010000000000005000000000000600000000000010000000000005000000008510000000000000010000000000002000000010010000000000000010000000000002000000000410000000000c91000000000000006
  | 7, 14 => 0x5000000000000200000001081000000000006100000000000000000000000000010000000000006000000010d1000000000000001000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000300000000000030000000000003000000000000200000000000000000000000004000000000000300000000c41000000000000003000000000e100000000000000700000000c81000000000084100000000000000400000000000030000000000006
  | 7, 15 => 0x3000000000000100000000000040000000000000000000000000300000000c810000000000000020000000000002000000000a100000000000000500000000000070000000000004000000000000100000000121000000000000006000000000000400000000000010000000000005000000000000100000000c510000000000000060000000000005000000000000800000000000010000000000000000000000000200000000c010000000000000060000000000003000000000210000000000000010000000000000
  | 7, 16 => 0x6000000000000500000000000010000000000001000000000a100000000010810000000000c910000000000000010000000000005000000000000500000000801000000000000003
  | 8, 0 => 0x0
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 7 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 6 s ws hint
  | 2 => checkCutEntry dom_5 roots_5 6 s ws hint
  | 3 => checkCutEntry dom_6 roots_6 6 s ws hint
  | 4 => checkCutEntry dom_7 roots_7 6 s ws hint
  | 5 => checkCutEntry dom_8 roots_8 6 s ws hint
  | 6 => checkCutEntry dom_10 roots_10 6 s ws hint
  | 7 => checkCutEntry dom_12 roots_12 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_14 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_14 == dom_14) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_14 goalM u ys) : RunD dom_14 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_14 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
theorem z3_8 : ∀ i, 8 ≤ i → i < 16 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 8 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 16 → Z 3 i = true := range_split z3_0 (z3_8)
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
theorem z4_88 : ∀ i, 88 ≤ i → i < 96 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 88 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 96 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (range_split z4_48 (range_split z4_56 (range_split z4_64 (range_split z4_72 (range_split z4_80 (z4_88)))))))))))
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
theorem z5 : ∀ i, 0 ≤ i → i < 264 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (range_split z5_152 (range_split z5_160 (range_split z5_168 (range_split z5_176 (range_split z5_184 (range_split z5_192 (range_split z5_200 (range_split z5_208 (range_split z5_216 (range_split z5_224 (range_split z5_232 (range_split z5_240 (range_split z5_248 (z5_256))))))))))))))))))))))))))))))))
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
theorem z6_600 : ∀ i, 600 ≤ i → i < 605 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 600 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 605 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (range_split z6_264 (range_split z6_272 (range_split z6_280 (range_split z6_288 (range_split z6_296 (range_split z6_304 (range_split z6_312 (range_split z6_320 (range_split z6_328 (range_split z6_336 (range_split z6_344 (range_split z6_352 (range_split z6_360 (range_split z6_368 (range_split z6_376 (range_split z6_384 (range_split z6_392 (range_split z6_400 (range_split z6_408 (range_split z6_416 (range_split z6_424 (range_split z6_432 (range_split z6_440 (range_split z6_448 (range_split z6_456 (range_split z6_464 (range_split z6_472 (range_split z6_480 (range_split z6_488 (range_split z6_496 (range_split z6_504 (range_split z6_512 (range_split z6_520 (range_split z6_528 (range_split z6_536 (range_split z6_544 (range_split z6_552 (range_split z6_560 (range_split z6_568 (range_split z6_576 (range_split z6_584 (range_split z6_592 (z6_600)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
theorem z7_344 : ∀ i, 344 ≤ i → i < 351 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 344 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 351 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (range_split z7_208 (range_split z7_216 (range_split z7_224 (range_split z7_232 (range_split z7_240 (range_split z7_248 (range_split z7_256 (range_split z7_264 (range_split z7_272 (range_split z7_280 (range_split z7_288 (range_split z7_296 (range_split z7_304 (range_split z7_312 (range_split z7_320 (range_split z7_328 (range_split z7_336 (z7_344)))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 16 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 24 → Z 8 i = true := range_split z8_0 (range_split z8_8 (z8_16))
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

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4277074056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_14.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_14 10 hT6 (by unfold IsConst; decide) low_14

def wit : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [9, 2]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [11, 3]⟩, ⟨GateOp.and, [8, 7]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_13089_aux

theorem PEqualNP.Outside.L_meta_13089 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4277074056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4277074056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_13089_aux.wit, PEqualNP.Outside.L_meta_13089_aux.wmono, le_trans PEqualNP.Outside.L_meta_13089_aux.wsize (PEqualNP.Outside.L_meta_13089_aux.lower s hs), PEqualNP.Outside.L_meta_13089_aux.weval⟩
