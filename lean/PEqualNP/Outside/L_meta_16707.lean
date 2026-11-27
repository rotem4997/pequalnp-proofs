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

namespace PEqualNP.Outside.L_meta_16707_aux

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

def dom_0 : Nat := 0x3333333333333333
def goal_0 : Nat := 0x3222222222222220
def roots_0 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (1, 17), (1, 33), (4, 5), (8, 9), (12, 13), (16, 17), (20, 21), (24, 25), (28, 29), (28, 60), (32, 33), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 1, 4, 8, 12, 16, 20, 24, 28, 28, 32, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [5, 9, 17, 33, 5, 9, 13, 17, 21, 25, 29, 60, 33, 37, 41, 45, 60, 49, 53, 60, 57, 60]
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
  | 3, 0 => 0x20aa7d5d1da653ce1a059fea0e8b949109fbbe80007f445f
  | 4, 0 => 0x995298d14eadd94241dba76241b1069c3f2dfba636664f9c2effe60c284696351eb0adaf1b58887117823e1513d9b63e135970af11f432f611de48070fbee3f00f92b19f0a124de308fc4e9f072e002f041cbf21035373af03305b3b032e9d9602de25df0293540c0111561a0102379d00d7a374009fac28
  | 5, 0 => 0xd268f7e7995298d168cd66c563db55fb619df3c35a24f14d56ffc2ad501930ff4e3f75c048f93e3d47040e0d40cd85c336e9258f36664f9c2dd111802d8e446c2b313a452ac4f6e52313500e1f4186351dce88e91876f8c117823e15177baa8512ef774712ce089412c5492910b2313c0f92b19f0cee55a50ccad15b0c9ce5800a6fc45f086941f406cfc0630667813a05a61cfb0522c74803d4fcb802b8d37b01c02c6100e0429d00d7a374
  | 6, 0 => 0xd268f7e7995298d168cd66c540cd85c336e9258f2ac4f6e51dce88e912ef7747086941f4
  | 7, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3030303030303030033003333333333002200220022002200003333000033330000330000003300000011110000111100000033000000330000000033333333
  | 0, 1 => 0x22202220222022202200220022002200220022000000000020202020202020201313131313131313113311330000000011111111111111111111000011110000
  | 0, 2 => 0x30003000000000003000000030000000232323232323232322222222222222222222222222220000222222222200220022222020222220202222000022220000
  | 0, 3 => 0x30303030303030303030303020202020303030300000000030303020303030203030202030302020303000003030000030300000000000003000300030003000
  | 0, 4 => 0x32323232000000003232303032323030323222223232222232322020323220203230303032303030322232223222322232223222000000003131313131313131
  | 0, 5 => 0x33223300332233003322222200000000332200003322000033003300330033003300330022002200330033000000000033002200330022003232323232323232
  | 0, 6 => 0x33330000330000003333000022220000333300000033000033330000000000003330333033303330332233223322332233223322330033003322332200000000
  | 0, 7 => 0x33332222333300003333222222222222333322220000000033332220333322203333202033332020333301013333010133330033333300333333000033330000
  | 0, 8 => 0x33333333222022203333333320202020333333330033000033333333000000003333333033333330333333003333000033333232333332323333222233332222
  | 0, 9 => 0x33333333333333003333333333333030333333333333000033333333303030303333333322220000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x88b12144890cb14470cd094488f0c14488b1291488bcd944
  | 4, 0, 0 => 0x70b0f9414b11d2c3e516240587c82c480b0f93570c0f941cb11c223e395c31547ca2c470b1194594b0f9928b2da2c3e5163385868a2c570b0f94594f561f28b11aac3e516338587ca2c464b4f8e5
  | 4, 0, 1 => 0x2238587ca2c476b141458ee161f28b11c2c3851623830507ac970b0e94570b961f28b11b2b3e51653e587ca2ca88a4f9457ae161f28b19c2c3c51633858a062c47ec4f945
  | 5, 0, 0 => 0x8909c2c3e51804480b0f90588e5c2c3e51a238587ca03688e161f2e51a2385868a0c688e161f2831a438587ca1069311c2c3a51a538587ce94688f9c2c3e51a2386eb0f94688e16203e51a23866b141468905c2c3e51804670b0f945
  | 5, 0, 1 => 0x88e192c3e51a238587ce9460125c2c3a516238587ca01600b0f9408016238587ca0d6011161f28116238589cf94688e16263e51a23866b0f94688e161f2815803d70b0f94588e161f282da238587ca09688e161f28499c3260b0f946
  | 5, 0, 2 => 0x4470b0f8950111c2c3e516238587ca076011161f12116238587ca94688e161f2819a64470b0f946890161f2841a238587ca08688e161f2809a23864b0f8e6
  | 6, 0, 0 => 0x4470b0f8950111c2c3e516238587ca07688e192c3e51a238587ce946011161f2811623866b0f94688e161f2825a238587ca0c6
  | 7, 0, 0 => 0x4470b0f945
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
  | 0, 0 => 0xc94abce3fff00003c1f07f0701801f07000c07c00fff
  | 0, 1 => 0xffffffff000ffffc3e0f80
  | 0, 2 => 0x6000000c00c94abc0000f0000000000000000000000
  | 0, 3 => 0x36b540da000368000d8d40303400c0d0030000018c40
  | 0, 4 => 0x368000dad5030343cc0d0036b54018c4f060003ffff0
  | 0, 5 => 0xc7398300000c038031ce60c700031c000c03800dad5f
  | 0, 6 => 0xf83803e0000f80603e0000f7bdc31ce6fc739831c000
  | 0, 7 => 0xf83e03e000ff80003e0f80f83e03e5fa0f8fe7fe0f80
  | 0, 8 => 0xffc003ff000ffc603ff000ffbfc3fcf80febf7fe0f8f
  | 0, 9 => 0x3fffe0ffff43fff80fff543ff000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x494ab8637ff18c6740f07b0301880000000c064007f7
  | 0, 1 => 0x539dcd0c6624300004a551ed6abaf3808a4200290800
  | 0, 2 => 0xa6200290c005bdffd6f7ff5bde316f66a5a9f5560784
  | 0, 3 => 0xb6b546dad51b6a002dad51b6b546d0d00b4200298c40
  | 0, 4 => 0xffe023fafd5fffffffafd5f6bd47fffffffe022dad51
  | 0, 5 => 0xff3f9bff808fc3e139ce62e7398b9c800e7398bfffff
  | 0, 6 => 0xfc3803f0f84fc2613f0800f7bdcfffffffff9abff808
  | 0, 7 => 0xfffe33fffffffe023feff7febf57f0f84fcfe77f0f84
  | 0, 8 => 0xfffdefffd59ffe633ff808ffbfdffcf84fffffffffff
  | 0, 9 => 0x3fffeeffff77fff8cfff567fff8c
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 22 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 22 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 77 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 77 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 77 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 77 then wireAt i else 0
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

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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

def dom_1 : Nat := 0x5555000000000000
def goal_1 : Nat := 0x5440000000000000
def roots_1 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]

namespace S_1
def pairsG : List (Nat × Nat) := [(50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [54, 58, 54, 60, 58, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xf882f5e9
  | 3, 0 => 0xf882f5e9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x550000000000000050500000000000004444000000000000
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

def dom_2 : Nat := 0x5555000055550000
def goal_2 : Nat := 0x5440000044400000
def roots_2 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 28, 60)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xffff0000ffff0000
def goal_3 : Nat := 0xfeea0000eeea0000
def roots_3 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa0000, 16, 17)] (by decide +kernel) (by decide +kernel) low_2

def dom_4 : Nat := 0xffffffff00000000
def goal_4 : Nat := 0xfeeaeeea00000000
def roots_4 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 6 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0x5555555555555555
def goal_5 : Nat := 0x5440444044404440
def roots_5 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000055550000, 44, 60)] (by decide +kernel) (by decide +kernel) low_2

def dom_6 : Nat := 0xffff000000000000
def goal_6 : Nat := 0xfeea000000000000
def roots_6 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_1

def dom_7 : Nat := 0xf0f00000f0f
def goal_7 : Nat := 0xe0a00000e00
def roots_7 : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]

namespace S_7
def pairsG : List (Nat × Nat) := [(1, 9), (1, 33), (2, 10), (3, 11), (3, 35), (8, 9), (8, 10), (32, 33), (34, 35), (34, 42), (40, 41), (40, 42)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 8, 8, 32, 34, 34, 40, 40]
def r2sG : List Nat := [9, 33, 10, 11, 35, 9, 10, 33, 35, 42, 41, 42]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_7.map (· &&& dom_7)
def goalM : Nat := goal_7 &&& dom_7
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x12562096
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000f0000000f0000000c0c00000c0c00000a0a00000a0a
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_7 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_7 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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

def dom_8 : Nat := 0xf0f0f0f0f0f0f0f
def goal_8 : Nat := 0xe0a0e0a0e0a0e00
def roots_8 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0000, 1, 17)] (by decide +kernel) (by decide +kernel) low_7

def dom_9 : Nat := 0x5555555500000000
def goal_9 : Nat := 0x5440444000000000
def roots_9 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 5 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_10 : Nat := 0xff00ff00ff00ff
def goal_10 : Nat := 0xea00ea00ea00e0
def roots_10 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 5 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_11 : Nat := 0xffff0000ffff
def goal_11 : Nat := 0xeeea0000eee0
def roots_11 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0, 1, 5)] (by decide +kernel) (by decide +kernel) low_7

def dom_12 : Nat := 0xffffffff
def goal_12 : Nat := 0xeeeaeee0
def roots_12 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_12 : Lower dom_12 roots_12 goal_12 5 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xf0f0f0f
def goal_13 : Nat := 0xe0a0e00
def roots_13 : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]

theorem low_13 : Lower dom_13 roots_13 goal_13 4 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

def dom_14 : Nat := 0xff000000ff
def goal_14 : Nat := 0xea000000e0
def roots_14 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 4 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

def dom_15 : Nat := 0xff00ff
def goal_15 : Nat := 0xea00e0
def roots_15 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

theorem low_15 : Lower dom_15 roots_15 goal_15 4 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14

def dom_16 : Nat := 0xffffffffffffffff
def goal_16 : Nat := 0xfeeaeeeaeeeaeee0
def roots_16 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_16
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (1, 17), (1, 33), (2, 6), (2, 10), (3, 7), (3, 11), (3, 19), (3, 35), (4, 5), (4, 6), (8, 9), (8, 10), (12, 13), (12, 14), (16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (24, 25), (24, 26), (28, 29), (28, 30), (28, 60), (32, 33), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 8, 8, 12, 12, 16, 18, 18, 18, 20, 20, 24, 24, 28, 28, 28, 32, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 9, 17, 33, 6, 10, 7, 11, 19, 35, 5, 6, 9, 10, 13, 14, 17, 19, 22, 26, 21, 22, 25, 26, 29, 30, 60, 33, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_16.map (· &&& dom_16)
def goalM : Nat := goal_16 &&& dom_16
def NN : Nat → Nat
  | 2 => 2
  | 3 => 13
  | 4 => 65
  | 5 => 154
  | 6 => 265
  | 7 => 144
  | 8 => 17
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x25bb48e10e2998c7
  | 3, 0 => 0xe230c8698f76f391878085d14ffca7494d89371e34b3be6830c09f502f9662fa2e0afe5e29caf85a265fa547192eef3604617712
  | 4, 0 => 0xed361ed8d6b7b714d6073ed4c4b80221a9c35cb8a4a16dad9a7c4a00923dc17a901c42178ec535248d69b7ce8c4818268865e281865b34a27c0fde5e7b36f7ba751f3be4747cbbe66de153b36505ebcf5d61de185b01fdb8589717fb530209c449eaf72c47c2484e453169773fb914d73e6b3b703c6dfd013b7059aa3a9bb969391054cd380204ee379e01bc3627bb4a34d8d93734d04ec93164fbb62e8961f42ddf972b29caf85a27032f9425f8e36225699d4e2404098a215d4c111e0e2bc01c9fda281b19ce2316fe7dde1508c2d4143effd712744ccb10ffd2f70f66cd810f4b345c0c72c3810827e9790666dbf1062d96240589277c035a259e017fcc44
  | 4, 1 => 0xf9c3ac57
  | 5, 0 => 0x354ef29334d8d93734d04ec93332310832e5d9a431d712ec31c6901231ae264f31a837f530a2217b2daad6d32913822f28e3945c28d1938c2884fdf82627af002606965224050abf2404098a2340e638226528651f24bc251ed15b311d4614f61cc85ad81c9fda281c0529661c0516cb1b589d611b326f8119f362ff16201d4d1552df5314ab6a621308ef3a129b689a116c3260108e7deb106a5f020f77894c0f775d430f4b345c0e5f7c0d0d6a224b0ce862fe0cd436710c8522b30b66c38b0b28ffd7098f2d0c08bc21de0898932707c64de407b0db4105bc4a41054d3aaa050fa71c04894642047366b104450d51039ec670021361d4009a0a2500182e23
  | 5, 1 => 0x974d6e9596be265a9421a8a393fc460791608b118cd235918c76d2aa8bced7e38b97f0218808a6cc86d99838863c4e2985deedf884670fcc802492537f5bb4557e9b4eb17e215aab78ef349078e6aa2277cbdb217509d6637498a9e17303d82a72fbb9b269fba345686fbef566285d93637f570761fa7f4b61c4e559613d9a4f60b635815f26e6535ab49b675a436f6259b17cea579aef485711b93d56ca2506558fcb5c54f04d9b544aeb5453a6662a509d6b154eb6808e4b0449cd4a85717c497091df493bdc4348ae6565483a4dd6476871444347e72842abe29940fb7abd3e1bae663aa4d97f3a3d87ee3a1e441938e4ed9a383af96137880be93767a207
  | 5, 2 => 0xff8cccb1fdd35bd0f6c6bb67e130803ee1151fb1dfc7ab9fd869da88d832dd31d538a662d1941c87d0405004cfc5e2fec1c8fd1cbfe4ca91bef11351bea63298bb9f8c8ab4c8b327b17a679eaed3aa25ab05838baa265028a82705e79f9927a39d4317e999ca8b93
  | 6, 0 => 0x166c19fa16446b9c161b95e215c3143a1517feab14e0d35f1494837b1436a47012db4a7b12d7703d129b996a1233002b116723a81145db6210d816a5106749651015958810060e320ff651070fec104b0f9550a90f4dbc720f4bf6100f18d8520e737a980e1456320d40405c0c6fc9640bc7415d0b420c200b28ffd70b09f3650ac923860ac5f3330a4eea9609c0e32809bd51ef09a328010919997808a3620f07b0db4107962ead078a0d3b0730d4d10715437d0659328105bbae7e05b76fa4047b153d042d77d503e41ee90341d11b030a7d9702fa41e00230d7bb0211e28701e7faa101e3cad001ceb6e601ba3ddb01a0c3aa00a16ee20085ca9f007217c6
  | 6, 1 => 0x352464f9349824f4341c017333b858fa33ad9cd4334a1cdc32845a413247aaca2f45be032f29cd722f22fbfb2f15a0e52f095ff92ec68d272e5125f22e3a2e562de6358a2da6f7032c9479822c42325c2c0678ff2bebe72d2b5d74272afd8c5229af2b642987612129025cbe27fdb4b526e23bf023ddefb323c083972391b8a622c73513225998972253603421ce37252177d428204b60b62014c6441ff6fee71fb569c31f9891041f87b1c01ecbe4b41eaa0f9b1e4008941df593e41d4df85b1d3110c21ca973311b5d29fa1b44b5de1b27d2611940c3e618e16a7f18c4770b18bf975f188f92a4186cfbda1849aff117eef06917135e9f170e9bbf16b01e54
  | 6, 2 => 0x63a5541262cd989a60507b9c5db6ae185cbe4b0e5c8c22ee5c8357335c7212b25c1f443a5b26580e5aea31985a9c6dcb5a63981859c4616b59af68bf58118ebc57c028cd5711b93d56ca2506560915a955b9f6e555ab52c8558fcb5c55739b7c541c698b53f49ec153cbf0e350b04b954f3f5b304ece2c6a4ead3d654e7106ca4ddb76074d1acf0f4c6771654c4c79c44aee0505496bd1284958591349279f5a48ef91be48ae22b54700cb0e45a7f5984497853043c469ce429c5d29412c1b3840416ff13ffc132e3fde2fa63fd24e333f09c54c3dd5b53e3d64e4c33ccc486b3bf021da3b754d643b47c0ff3ae826bb38a4a5e2385a6545383a016537b3afd3
  | 6, 3 => 0xd70a1d9bcfaaeb5dcec114e4ca5d1f3fc5736c6ac4d20e6dc1fa1783c0171c7cbe02947cb7dce78eb2118fd6b17a679eae1bf85daa4c653aa9636d3aa82705e7a770aa62a61bfe94a5ff6a18a5268c5fa2c93d67a265fcc7a0dcb9259f307a4a9e519fea9e1a2c639af88715977c2919953d242694a485de94a0b6d3927dd8708ff7d9d28f74f0a98e25b3d38c515f7e8c3d0db98a4b2c568926b11a88ba392485701a2b85215bbd84064fcd83f48aff808c703d7ea020fc7dcbc02e7dbb9e0f7a399f0c797004af77d135d077ae3ab0778decba7696cef56ed606ea6b233ce96aefcfd96a2c3cc268f893bf6741623a664624f0658f322f653df8c46479fe20
  | 6, 4 => 0xfdd35bd0ed786cd3ecb47af8eaef8849e5114d5ce1151f08db4f33a9d9918af2d87aa7e1
  | 7, 0 => 0x3518dab134746a9f344f8b04339be8303264f194315024ba3129ad3f30ccd1eb3055c0a6302ca7772e46479b2d90db782b81626d2a6cf0712964176b28a4a83e2705880d26d2458e265363bb26396ad4261c309d2429651523cf42222398f310233e519822c7351322543c1c22521a0421e9d24d21a1d2672014c6441f3d31db1d989e101d73f56619f08aad18787ffd1821179f17d6fff416d8a81c119811441136e0fc1134c93410d1aa960f8898390f79f41c0d9cbe430d9a92370d61f2fb0cea20e10cabde0a0c167f100afb5dd308e13cad089ab0f3075140fd06ecbabd06291d83059e8b1705869eb103f1b952033a727c0285b6c501013f3600773c2b
  | 7, 1 => 0x9ffd088398d8396997a9fca097012b8493602c4691b98d128e7679718708035286bb6894868cb424850f030e82739f207fe35f827e8559377c09f9567bf0d3337a85129f78493a7f77d135d0727daf3d7268845a6e834bca6cd622c66b6909ce6b1be3666ababa2c6a4fc62d64e6ab0264a4b8996284e0435b9302e658b131c8567ee6cd54af73bf520a3fab51e81d51514aca6d4e7327324dc27b5b4d1acf0f4c4c79c44b47fd5c4ac0774d499b08ca49148db048f889f845d91ef143b42571432891ef4214fad141d9fb783f88d5943dc32c533d8620523a8b1a653a861c993a305add38b6a98b38ad846e3899ed18368990f73678c0eb366fa272357bcd57
  | 7, 2 => 0xf9acd0faf6e94291f646c3bfec164c1eea39f55de8b03ee3e1283faade1b0bb2d96359b3cecb96dfbc7fbe0dba2399e2ab681b8eaa87c3f1a4e3c223a00d2aa2
  | 8, 0 => 0xc2afde019b34b12188e8d84f76f0de33764e5f615fbac6fd5e22a7545cde0cce4aee73793e277fff2eedfa851e7359ed1729918f1561a43a1142fa410e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f000f000f000aa00aa00aa00aa005f005f005f005f0055005500550055000f000f000f000f00050005000500050000ffff0000ffff00000000ffffffff
  | 0, 1 => 0x505050505050505010101010101010100ffffff00ffffff00ffff0000ffff0000ff00ff00ff00ff00ff00ff0000000000ff00aa00ff00aa00ff000000ff0000
  | 0, 2 => 0xf0a0f0a0f0a0f0a0f000f000f000f000e0e0e0e0e0e0e0e0a0a0a0a0a0a0a0a055505550555055505050505ffffffff0505050555555555050505050f0f0f0f
  | 0, 3 => 0x111100001111000011001100110011000fff0fff0fff0fff0ff00ff00ff00ff00f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f00000000
  | 0, 4 => 0x1f001f001f001f00131313131313131311ff11ff11ff11ff1111ffff1111ffff11113333111133331111111133333333111111111111111111110000ffff0000
  | 0, 5 => 0xa5a5a5a5a5a5a5a5a0ffa0ffa0ffa0ffa0a0a0a0a0a0a0a055555555555555555550555055505550550055005500550050505050505050501f1f00001f1f0000
  | 0, 6 => 0xaaffaaaaaaffaaaaaafaaafaaafaaafaaaafaaafaaafaaafaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaa0000aaaa0000aaa0aaa0aaa0aaa0aa00aa00aa00aa00
  | 0, 7 => 0xcccdcccdcccdcccdccccccccccccccccbbbbaaaabbbbaaaabbaabbaabbaabbaaafafafafafafafafababababababababaaffaaffaaffaaffaaffaaff00ff00ff
  | 0, 8 => 0xececececececececec00ec00ec00ec00e0e0e0e0e0e0e0e0e0e0e0e000000000e000e000e000e000cececececececececceecceecceecceecccfcccfcccfcccf
  | 0, 9 => 0xeeeecccceeeecccceeee0000eeee0000eeee000000000000eeeceeeceeeceeeceee0eee0eee0eee0eee0eee0ccc0ccc0eecceecceecceeccee00ee00ee00ee00
  | 0, 10 => 0xf000f000f000f000f000f00000000000f0000000f0000000eeffeeffeeffeeffeeefeeefeeefeeefeeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeee00000000
  | 0, 11 => 0xf0f0f0f000000000f0f0a0a0f0f0a0a0f0f00000ffff0000f0f00000f0f00000f0f0000000000000f0e0f0e0f0e0f0e0f0a0f0a0f0a0f0a0f00ff00ff00ff00f
  | 0, 12 => 0xfaaa0000faaa0000faa0faa0faa0faa0fa00fa00fa00fa00f1f1f1f1f1f1f1f1f0fff0fff0fff0fff0f0ffff00000000f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0
  | 0, 13 => 0xfafa0000fafa0000fafa0000aaaa0000faf0faf0faf0faf0faeafaeafaeafaeafaaafaaafaaafaaafaaafaaaaaaaaaaafaaafaaa00000000faaaaaaafaaaaaaa
  | 0, 14 => 0xfafafafafafafafafafafafaf0f0f0f0fafafafaaaaaaaaafafafafa00000000fafaf0f0fafaf0f0fafaaaaafafaaaaafafaaaaaaaaaaaaafafaaaaa00000000
  | 0, 15 => 0xfefcfefcfefcfefcfef0fef0fef0fef0feeefeeefeeefeeefeee0000feee0000fee0fee0fee0fee0feaafeaafeaafeaafe00fe00fe00fe00fe00fe00ee00ee00
  | 1, 0 => 0xff00f000ff00f000ff000000ff000000ff00000000000000fefefefefefefefefefefefeeeeeeeeefefefefe00000000fefef0f0fefef0f0fefeeeee00000000
  | 1, 1 => 0xff0fff0f00000000ff05ff05ff05ff05ff01ff01ff01ff01ff00ffffff00ffffff00ff00ff00ff00ff00ff00ff000000ff00ff000f000f00ff00ff0000000000
  | 1, 2 => 0xffaaaaaaaaaaaaaaffaaaaaa00000000ffaa0000ffaa0000ffaa0000aaaa0000ffa0ffa0ffa0ffa0ff50ff50ff50ff50ff11ff11ff11ff11ff0fff0fff0fff0f
  | 1, 3 => 0xffe0ffe0ffe0ffe0ffe0ff00ffe0ff00ffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaaaaaaaaaffaaffaa00000000ffaaff00ffaaff00ffaaaaaaffaaaaaa
  | 1, 4 => 0xffeeffeeff00ff00ffeeffee00000000ffeeffccffeeffccffeeff00ffeeff00ffeeeeeeffeeeeeeffee0000ffee0000ffecffecffecffecffeaffeaffeaffea
  | 1, 5 => 0xfff0fff0fff00000fff0fff0ffa0ffa0fff0fff0ff00ff00fff0fff000000000fff0ff00fff0ff00fff0aaa0fff0aaa0fff00000fff00000ffeeffeeffeeffee
  | 1, 6 => 0xfffafffafffafffafffafffa00000000fffafff0fffafff0fffafafafffafafafffaaaaafffaaaaafffa0000fffa0000fff0fff0fff0fff0fff0fff0fff0f0f0
  | 1, 7 => 0xffff0505ffff0505ffff00ffffff0000ffff00ff00000000ffff0000ffff0000ffff0000aaaa0000ffff000000000000fffefffefffefffefffefffe00000000
  | 1, 8 => 0xffffffff00000000fffffff0fffffff0ffffff00ffffff00ffffee00ffffee00ffffe0e0ffffe0e0ffffaaaaffffaaaaffffaaaaffff0000ffffaa00ffffaa00
  | 1, 9 => 0xffffffffe0e0e0e0ffffffffaaaaaaaaffffffffaaaa0000ffffffffaaa0aaa0ffffffffaa00aa00ffffffffa0a0a0a0ffffffff00ff00ffffffffff00f000f0
  | 1, 10 => 0xffffffffffff0000fffffffffff0fff0ffffffffff00ff00fffffffff0f0f0f0ffffffffeeee0000ffffffffeee0eee0ffffffffee00ee00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x69674b39a6f4b3
  | 3, 0, 0 => 0x9a95614b4c7674b3449a957e524c77c4b344d1bc6b4b4c795774b4b16967524c7bc7a4b4c7a2774b4c7bc6b4b4c7bc6a4b4b19a6f524c76b674b4
  | 4, 0, 0 => 0xc7bc9f77525c7bc6b524b5c78b8172525c7bc6c61485b28b7461525c7c37945345c7bc8b724b5c7b16b67525c7bc5a48345bc9f7452345bc9f8252345c7bc9d5f4b5cfbc9f77525c7bc594b345c78b6f4b345c7bcb7574b5
  | 4, 0, 1 => 0xc7b1a2775259a948b61525c7bc9f6b525c7bc7b48345c7bc574b345c7bcb16b525c7bcb16a525c7a25a48345c7bc9d774b500c7bc6b4b4c79f776f5259c9a9561525c7bc6c5a485c7bc9d614b5c7bc9d79455c7bc554b345
  | 4, 0, 2 => 0xc7bc77654b5b6b28b61525c7bc8b6b4b59a956152485c7bcb16b4b5c7b17c52345d1bc574b345b169673e345c79d95614b5d1bc9d614b5c7bc9f774b5c7b19577525bc8b824b345c7bc9b7e525b19a6f3e345c7bcb17a525
  | 4, 0, 3 => 0xb19a9561525c7bc9f77485c7bcb16b4c5c7bc6b48455c7bc6b574b5c7bc7b4b345c7b16752345c7bc6b4b345958b7461525c7bc77574b5c7bc7e7a525c7bc7d4b345c7bc7845345c7bca8774b5c7bc7b52345c7bc794b345
  | 4, 0, 4 => 0x8b696761525
  | 5, 0, 0 => 0xc7bc796152346c7bc88614b346c7958b7761526c7bc8b61523a6a6a28b6152346c7bc8b6140346bc98968b61526c7bc9d8b84456c7a38b614e346c7bca09f615269a8b6f613e3469d9a95613e306c7bc8b7a61526c7a28b7761526c7bc5a5248346c7bc8b6152366
  | 5, 0, 1 => 0xc7bc9d61524b68b7270613e326c78b615234286b6958b613e346c7bcb19d5f526c7bcb15952346c7bc8b7161526b19a95613e346c7a261524834600c7bc5a48345c7b18b6f52346c7bc9d8b7e526bcb79a8b61526c7bc8b6152176c7bcb7b157526c7bc8b77614b6
  | 5, 0, 2 => 0xc7bc9f7752456c78b7c615234600c7bc9d614b5c7bc79614534600c7613e340c5bc9d9c9a6152600c7bc8b3e2f5cfbc8b77524569d9a958b6152600c7bc9f77525c7bcb18b725268b6967613e346d0bc8b7e52346bc8b756152506c7bc9b6152486c795615248346
  | 5, 0, 3 => 0xc7bc9f614834600c7bc574b34500c7bcb16b525c7bcb48b61526bcb68b6152346c7bc9f9d61526c7bc9d7e52346c7bc8b614a346c7b16b673e346c7bc8b6861526ccbcb1573e346c7bcb15552346c7bc9f8452346c7bc786152346c7bcb7573e316c7bc57524b346
  | 5, 0, 4 => 0xbcb18b8252346bc8f8b6152346c7bcb38b615269c9a95613e346c7bc8b61523d6c7bca36148346c7bc9f5752346c7bc9f8445346c78b776f52456bc8b806152346c78b615234206c79a958b61526c7bcb19d77526cfbc8b8445346d5bcb1563e346c7bca79d61526
  | 5, 0, 5 => 0xc7bc9f8b77526c7bc8b844b346c7bc867e523469a948b613e346c7bca16146346c7bcb19d614b6c7bcb16b3e346c7bc8b7e52346c7bcb78b61526c7b19d956152600c7b1673e345c7bcb16a3e346bc82796152346c7bc8b6b52456c7bcb19d61496bcb88b6152346
  | 5, 0, 6 => 0xc7bc8b7752076c7bcb78b614b6c7bc8b574b346c7bcb18b6b526c7bcb76561526c7bc8b61523c6008b746f61525c7a4866152346c7bcad9d61526bc9b9a8b61526c7bcb1574b3469a958b6152346c78b676152346c7b195773e346c7bc9d6561526c7bc615234276
  | 5, 0, 7 => 0xc7bcb17d52346b6b28b613e346bc8b848245346c7bc8b613f346c7bcb1a877526bcb68b7761526c7bc9d614b346c7bc8b7764526c7bc9f5a5234600c7bc583e345c7bca85a48346c7bcb17952346c7bc7a7961526c7bcb16b3e316c7bcb17765526c7bc8b7e4b346
  | 5, 0, 8 => 0xc7bcb19d614c6c7bc574845346c7bc9d7961526c7bc8b7d45346c7bc9d6148456c7bcb15740346c7bcb1583e346c7bcb16b57526c7bc8b614b346c7bc8b794534600c7bc3e341c5c7bc9e6152346c7a28b6152346c7bc8d6152346c7bcb16b52346c7bcb17757526
  | 5, 0, 9 => 0xbcb7b68b61526c7bc8b6b61526c7bcb78b614c6c7bc8b773e2f6c7bcb1574c346c7bc8b6153346c78b6b6761526c7bcb1663e346d1bc8b614b346c7bcb7653e2d6
  | 6, 0, 0 => 0xbc9b8b613e336c7bc8b613e3405700c78b615d3e346c7bcb1573e3403700bc8f8b613e346c7bca98b6152347c7bc8b7e5248347c7bc8b7761524e7c7bc9d8b7761527cec7bcb1573e347c7bcb18b753e347c7bc978b613e34700c7bb613e340b6c7bc8b61524434700c7bc8b6152046c7bcad8b6152347
  | 6, 0, 1 => 0xd5bcb18b5f3e347c7bc8b826152347c7bc8b613e34117c7bcb1613e342a700cebc613e330b600bdbc613e340b600c73e341a0b016bcb19d9a613e34700c7bc8b614034600bc8b613e3412600bcb18b743e346c7bc8b846145347c7bc9d613e30047c7bcb18a613e34700c9bc613e340a6c7bc8b6141340b7
  | 6, 0, 2 => 0xc7bcb08b613e34700c8bc613e340b6c7bcb78b593e347c7bc8b773e2d0b7c7bcb16b613e347c7bc8b7e6152347c7bc9d615248347c7bc8b615239347c7bcb18b593e347c7bc9d8b615c527c7bc8b613e37347c7bcb98b6152347bcb69d8b613e347cdbcb18b613e34700c7bc796152346c7bcae8b613e347
  | 6, 0, 3 => 0xc7bcb18b7761527c7bcaa8b613e347bc9a958b613e34700c7bc8b6134266d6c7bcb1573e34700c7bc8b4f341a6c7bcb188615234700bc9a8b3e341a6c7bc8b614f34237c7bc9d8b61520b7c78b77736f3e347c7bc9d8b61521a7c7c48b615248347c7bc8b614034037c7bca88b5a52347c7bc8b615234167
  | 6, 0, 4 => 0xbc8f8b3e341a6c7bc8b6a613e347bcba8b615250347c7bcba9d8b6152700c7c5863e341a6c7bc8b6152340d700c78b6f613e2c6c7bc8b614746347c7bcb19d573e34700c7bc8b776147600cabc613e340b600c7bc8b521a146c7bcb78b7761527009a8b613e34016cebc8b613e340a700c7b1573e34016
  | 6, 0, 5 => 0xc7bc8b613e34047c7bc8b613e3634700bc9c9a613e346bcb7b68b613e34700d6ba8b3e341a6bcb6b18b613e347c7bc8b6b613e347009a958b613e346c7a8a28b6152347c7bc9d8b6152047c7bc8b613e34197bc8b6b69613e34700c7bc8b3e3410600c78b735c3e346c7bc8b61545234700c78b67613e346
  | 6, 0, 6 => 0xc7bcb1573e342c7bcb19a8b613e34700bc8b777461526c7bc8b613e342b700d68b615b3e346c7bca58b614f34700c7bc8b34211a6c7958b77613e347008b3e341a0100600cd8b86613e34600c7bc613e342e6bc98968b613e34700c7c1613e340b600c7be613e340b600c7bc8b613422600c78b6e613e346
  | 6, 0, 7 => 0xc76152340b016c7c5b186613e34700c7bc6149340b600c7bc8b7752456c7bcb19d5f3e347c7bc9d9a8b61527cbbcb18b613e34700c7bc52341a0b6c7bc8b836152347bcb79a8b613e347c7bc8b856152347c7bc8b613e3417700c7bcb19d61526c7bcb7b1573e347c7bcb18b614f34700c78b613421016
  | 6, 0, 8 => 0xbc9a8b6152346c7bc8b84524534700c7bcb1575234600c7bc613e383469d9a958b613e347c7bc8b6152341f7c7bc8b6d3e341a7c7bc8b614734267c7bc93613e34057c7bc8b613e34137c7bcb18b6140347d6bab18b613e347d5bcac8b613e34700c7bc893e341a6c7bc86615248347d6bcb18b5f3e347
  | 6, 0, 9 => 0xc7bc6147340b600c78b6f613e346c7bc8b614845347c7bc8b613e34037c7bc8b6152341e7c7bc8b63615234700c7c5613e340d6c7bc8b776561527c7bc9d8b6152457c7958b613e3404700c78b776f3e2d600c78b3e2c1a01600c7bcb13e341d6c7bc8e8b613e347c7bc8b6152340e700c7bc9d3e301a6
  | 6, 0, 10 => 0xc7bc918b615234700c7bcb16b3e34600c7bc8b7e52346c7bcb18b603e347008b61523401006c78b776f615234700c7bcb78b61526c7bcb48b613e347c8bc8b613e340b700c799615c3e346c7bc8b6152341d7008b62613e34016c7bc8b796152347c7bc9b8b886152700c7bc8b8445346c7bc8b615234247
  | 6, 0, 11 => 0xc7bc8b615234087c7bc8b776157527c7bc8b7d6152347c7bcb18b614c347c7bf8b613e340f700c79d8b6152016cabc8b613e340b7c7bc8b776152217c7bcb79d613e307c7bcb19d773e34700c7bc633e34076c7bcb19d613e307c7bca88b7761527c7bc8b57524534700c7bc9d8b521a6c7bc8b7f6149347
  | 6, 0, 12 => 0xc7bcaf8b613e347c7bcb18b733e347c7bcb78b613e347c7bc9d61593e307c7bc8b6149341a7c7bc8b61520b06700c7bc8b522c1a600c7bc8b7761216c7bcb38b613e347c7bcb18b8452347c7bc8b61523404700c78b6f3e341a6c7bc8b6b6152347d6bcac8b613e347c7bca48b615234700c7bc8b7561526
  | 6, 0, 13 => 0xc7bc8b42341a6c7bcb1573e3431700cbbc613e340b6c7bc8b615234157bc9b9a8b613e347c7c6bcb1573e347c7bcb7b18b61527c7bc8b61524d34700c7bcb1563e34600c7bc9c3e341a6c7bc9d65613e347c7bcb18b5752347c78b615c524e347c7bcb19d613e317c7bc8b6b6157527c7bc8b77615f527
  | 6, 0, 14 => 0xc7bc8b615243347c7bc8b613e35347c7bbb18b613e347c7bcb78b613e317c7bc8b61524b347c7bcb177653e347c7bc8b773e3407700c7bc613e39066c7bcb18b6d3e347c7bcb58b733e347c7bcb58b613e347c7bcb19d6152347c7bcad9d613e347c7bc8b61565234700c7bc933e341a6c7bc8b615234037
  | 6, 0, 15 => 0xc7bcb16b573e34700c7bc573e3403600c7bc9d61520b600c7bcb1593e34600c7bcb1573e2c6c7bc8b613e34097c7bc928b613e34700c7bc613e34056c7bcb78b615234700c7bc3e2c1a0b6c7bc8b613e3402700c7bc8b614b346cebcb18b613e337ccbcb18b613e347d2bc8b61524e34700c7a28b6152346
  | 6, 1, 0 => 0xc7bc8b6b61526c7bc8b61523425700bcb68b613e346c7bc9d8b6152487c7bcb18b614b34700c7bc8b3e2d0f6008b613e2c01006c7bc8b615952347c7bcb18b6149347
  | 7, 0, 0 => 0xc9c7bc613e340b70000bc8b3e341a006c7bcb18b613e3431800c7bcab8b613e34700c7bc8b61575234700c78b86613e343270000d6ba8b613e346c7c6bcb18b613e34800c7bc613e342c0b7c7bc8b776f613e34800c7bcb1613e340b700c7bc8b76613e34700c7bc8b63613e34700c7bc8b6152342170000c7c586613e34600c7bca88b6152347
  | 7, 0, 1 => 0xcec7bc8b613e341a800c7bc8b613e3408700c7bc86613e340b700c7bc8c8b613e3470000c7bc6152340b60000c7c08b613e34600c7bc8b8a613e34700bc9d8b613e340070000c7bc8b6134216c7bcb18b615f3e348d4c7bc8b613e341a800008b613e340100600c78b776f613e34700c7bc8b613e3429700c7bc8b613e341d700c7c5bc8b3e341a7
  | 7, 0, 2 => 0xc7bc9d613e306c7c5bcb18b613e34800c7bc8b87613e34700c7bc613e340b07700bcb18b613e34007c7bc9d8b77613e34800c7bc8b615f5234700d3bc8b88613e34700c7bc8b6d613e34700c7bc8b613e3404700d3bc8b615f3e34700c7bc8b613e341b7c7c2bc8b61573e348c7bc8b75615f3e34800c7bc8b6b613e34700c7bc8b773e341a7
  | 7, 0, 3 => 0xc7bc9d8b613e340b8c7bc9d8b613e341a800c7bc8b61524834700c7bc8b613e3b34700c78b613e341a01700c7bc8b3e34331a700c7c2bc613e340b7d6c7bc8b613e341a8c7bc9d8b615c3e34800c7bc8b3e341a0b700c78b615c3e3401700c7bc9d8b613e2c70000c78b613e2c01600c7bc613e342d0b700c7bc908b3e341a70000c7bc8b3e2c1a6
  | 7, 0, 4 => 0xc7bc8b615b3e34700c7bcb18b613e2c7c7bc9d8b613e340480000c7bc9d8b6152600c7bcb18b573e347c7bcba9d8b613e34800c7bc8b3e341a14700bc8b86613e34007c7bcb78b77613e3480000bc8b615234006c7bcb18b77613e34800c7bcba8b3e341a700d6c78b615c3e34700c7bc9a8b613e34700c7bc8b615e3e34700c78c8b613e34017
  | 7, 0, 5 => 0xc7bc8b86613e2c70000c7bc8b61522c6c7bcbab18b613e34800c7bc61573e340b700c7bcb19d613e34700c7bc8b61563e34700c7bc8b3e3b341a70000c78b6f613e34600c7bc8b613e3403700c7bc8b776152347c7bcb18b613e34338c7bc8b613e342c1a800c7bc8b3e341a007c7bcb18b613e341a80000c7bc8b733e34600c7bc613e34300b7
  | 7, 0, 6 => 0xcebc8b613e33600d6c7bc8b3e341a700c7bcb78b613e34700bc8b61573e340070000c7bb8b613e346c7bc8b613e342d0b800c7bc615f3e340b7c7bc8b7765613e34800c7bc9d8b613e3070000c7bc8b6d3e346c7bc8b613e340b0780000c7bc8b615134600c7bcba8b6152347c7bcb18b613e3400800c7bc8b6152341a700c7bcb18b5f3e347
  | 7, 0, 7 => 0xc7bc8b77615f3e348c7bc8b613e340b0680000c7c18b613e34600c7bc8b613e3407700c7bc8b61593e347d6c7bcb18b613e34800c7bc8b61573e2c700c7bc8b3e341a18700c7bc8b75613e34700c7bcac8b613e347c7bc8b7761573e34800c7c5bc613e340b7c7bcb18b613e34038cec7bcb18b613e34800c7bc8b61525034700c7bc9d8b3e341a7
  | 7, 0, 8 => 0xc7bcb1573e346c7bc8b61573e342c8c7bcb18b61573e3480000c7bc3e341a0b600c7bcba8b613e2c7c7bc8b613e341a0b800c7bc8b613e2c1a7d6c7bc8b61573e34800c7bc8b613e2c297c7bcb18b613e342d800c7bcb18b6152347c7bcb1ac8b613e348c7bcb7b18b613e348c7bcb18b613e342c80000c7bc8b6149346c7bc8b6b61573e348
  | 8, 0, 0 => 0xc7bc8b613e342d700c7bc8b6152346c7bc8b613e342c7c7bcb18b613e34700c78b613e34016d6c7bc8b613e34700c7bc8b3e341a6cec7bc8b613e347d4c7bc8b613e347c7bc8b613e34007c7bcba8b613e347c7bc8b613e34337c7bc8b613e341a7c7bc8b615c3e34700c7bc8b613e2c6c7bc8b77613e347
  | 8, 0, 1 => 0xc7bc8b61573e347
  | 9, 0, 0 => 0xc7bc8b613e346
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
  | 0, 0 => 0x1c0180300c000000000003cf1fc1f83f0fff1fc1f83f0c3003c0780f03ff03c0780f0030003ff800ffff000007ffffff
  | 0, 1 => 0xe3c678cf3030e04608c130001ffff83fffff1ffe003ff0001fc1f83f0fff1fc1f80000001fc0003f03cf1fc0003f0000
  | 0, 2 => 0xe00600c033cfe00600c030000380700e03ff0000000003cfffc7f8ff3c30e3c67fffffffe3c67ffffc30e3c678cf33ff
  | 0, 3 => 0xfc4007f10000e03e07c0f000ffc7f8ff3ffffc0780f03c00e3fff8cfffffe3c678cf33ffe3c678cf0000e3c678000000
  | 0, 4 => 0xe03e07c0f000fc7f8ff1fc0ffffffffffffffc7ffff1fffffc7f8ff1fc0ffc7f8ff1fc0ffc7f8ff1fc00fc4007ff0000
  | 0, 5 => 0xe3c678cf30301fc1f83f0fff000000000000fffffffffc30fc3f87f0fc00e03e07c0f0001c398730cc00ffc007ff0000
  | 0, 6 => 0x1fc0003f03cf1c0180300fcf03c0780f03ff0000000003cf000000000000000000000000000000000000000000000000
  | 0, 7 => 0x3c0780f03f00380700e03f0fc4007f103cfe03e07c0f3cfe3c678cf33ffe04608c133cf1fc1f83f0fff1fc1f83f0fff
  | 0, 8 => 0x380700e03f00000000000000000000000000000000000000000000000000380700e03ff0380700e03ff03c0780f03ff
  | 0, 9 => 0x380700e03f00380000e00000380000000000380700e03f00000000000000000000000000380700e03f0000000000000
  | 0, 10 => 0x380700c0000038000000000000070000001fc1f83f0fff03c0780f03ff0380700e03ff0380700e03f0038070000000
  | 0, 11 => 0x1c39800000001c00073000001c0007ff00001c00073000001c000000000000380700c00000380700c00003f87f0fc3ff
  | 0, 12 => 0x700000000380700c00000380700c000fc7f8ff1fc001ff9ff3fcfff1c3ff80000001c398730cc001c3980000000
  | 0, 13 => 0x1c00073000001c00000000001c398730cc0000380700c3cf00380700c3cf0038000003cf0038000000000000070003cf
  | 0, 14 => 0x1c398730cfcf1c398730cc001c39800003cf1c39800000001c398730cc001c00073003cf1c00000003cf1c0000000000
  | 0, 15 => 0x1fb9f73ecff01c398730cc0003b8770ec3ff0380070e000000380700c00000380700c3cf00380700c000003800000000
  | 1, 0 => 0xe03807c0c000e00007c00000e000000000001fb9f73ecfff1fb9f00e03ff1fb9f00000001fb9873ecc001f8070000000
  | 1, 1 => 0xe3fe78000000e3fe7fcff030e07e0fc1f000e03fffc0ffffe03e07c0f000e03e07c00000e03e00c03000e03e00000000
  | 1, 2 => 0xe000000003cfe00000000000e00007c00000e00000000000e03e07c0f000fc3f87f0fc00fc7f8ff1fc00e3fe7fcff3ff
  | 1, 3 => 0xe03e07c0f000e03e07c0f000e03e07c0f3cfe03e07c0f000e03e000003cfe03e00000000e03e07c0f000e00007c003cf
  | 1, 4 => 0xe3be77c0f000e3be70000000e3be77cef3f0e3be07cef000e38077ce03ffe38007ce0000e3be77cef3f0e03e07c0f3cf
  | 1, 5 => 0xfc3f87f00000fc3f87c0f000fc3f87c0f000fc3f80000000fc3e07f0f000fc0007f00000fc0007f00000e3be77cef3ff
  | 1, 6 => 0xfc3f87f0ffcffc3f80000000fc3f87f0fc00fc3987f0cfcffc0007f003cffc0007f00000fc3f87f0fc00fc3f87f0cc00
  | 1, 7 => 0xffc67fff3030ffc1ffff0000ffc1f8000000ffc007ff0000ffc000000000ffc000000000ffbff7feffffffbff0000000
  | 1, 8 => 0xfffff8000000ffff87fffc00fffe07fff000ffc007ff0000ffc007ff0000ffc007ff03cfffc007ff0000ffc007ff0000
  | 1, 9 => 0xfffff8000000fffff80003cffffff8000000fffff8000000fffff8000000fffff8000000fffff83f0ffffffff8300c00
  | 1, 10 => 0xffffffff0000fffffff0fc00ffffffc0f000ffffff30cc00fffff80e0000fffff8000000fffff8000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xd01a0340c5104c09813074d09c138270b1c09012024081000c01803030c000000000000001ff800fefb000003fffdf7
  | 0, 1 => 0x4204408820200000000000000ddff837ffff0dde4037f1a60dc1b8370f5d0dc1b80002080dc09837074d0dc000370104
  | 0, 2 => 0x62c658cb33ae620640c830a262c658cb33ae20c21843138e4b0560ac2830420443fffdf7420442aca830420440cb31a6
  | 0, 3 => 0x9020040000009020040000006fc7f8ff3fff6f07e0fc3cf362dff8cbffff62c658cb33ae62c658cb030c62c658000208
  | 0, 4 => 0xf22644c830a2b0620c41100e9de1bc370f5d903ffc00fefb902a8c00540b902005515407902004000000902007ff0104
  | 0, 5 => 0x460cc19864610dc9b9374f5d040881104441db3566aca830db3566aca830d2344688a020993126248810f2e004cb0104
  | 0, 6 => 0x2dca997757cf2dcbb9775fdf24ca995357cf24ca995357cf24ca9800020824c001530104240a815054c3200a01405082
  | 0, 7 => 0x4b9572aeabf04b9572aeabf0b4ea9d5357cfb4ea9d5357cf66ced9db77ef24ca995357cf2dcbb9775fdf2dcbb8370f5d
  | 0, 8 => 0x4f9df3beeff1421c4388e0a00d19a334cc510d19a000000000180300c0006bd77aefbbfe4fd5fabfaffd4bd57aafabfc
  | 0, 9 => 0x6fd573ffabf46fc003ff01046fc0000000006f9ff3fefff36f1fe3fcfcf36f1fe2aca8f06b9f73eefbf2621e43c8f0a2
  | 0, 10 => 0x90380700c0009038040000009020070000006fdffbffffff6fdffbffffff6fdffbffffff6fdffaaeabf86fdff8000208
  | 0, 11 => 0x9d39a40000009d28873444419d2007ff01049d20073400009d20040000009d39a734cc5194388710c44190f81f03c30c
  | 0, 12 => 0xb4e007530104b43a8750d4c3b03a0740d0829d39a734cc519df9bf37cf5d9d3ffc0002089d39a734cc519d39a5104441
  | 0, 13 => 0xbde007770104bde005530104bd3ba774dcd3bdfbbf77dfdfb4fa9f53d7cfb4fa9d5357cfb4fa9c000208b4ea9f5357cf
  | 0, 14 => 0xbdfbbf77dfdfbdfbbf34ce59bdfbbd5357cfbdfbbc000208bdf9a777cd55bdea9f7757cfbdea9d5357cfbdea9c000208
  | 0, 15 => 0xffbff7fefff3ff3fe7fcfcf3ffffffffffffffe007ff0104ff3fe7fcfcf3f6fedfdbf7eff23e47c8f0a2f23e47c8f0a2
  | 1, 0 => 0xf23807c8c000f22007c80000f22004000000fffffffffffffffffffffffffffffc000208fff9a7ffcd55fffffc000208
  | 1, 1 => 0xf2fe5c000208f23e47c8f0a2f23e47c8f0a2f23fffc8fefbf23e47c8f0a2f23e47c80000f23e44c830a2f23e44000000
  | 1, 2 => 0xf6ea9d5357cff6ea9c000208f6e007db0104f6e005530104f63ec7d8f4e3fb3f67ecf8b2f23e47c8f0a2f2fe5fcbf3ae
  | 1, 3 => 0xff3fe7fcfcf3ff3e47fcf0a2f6fedfdbf7eff6fedfc8f2aaf6fedd5357cff6fedc000208f6fe47dbf1a6f6ea9fdb57cf
  | 1, 4 => 0xffffffc8f2aafffffc000208ffff77fffbf6fffe47fff1a6ffffffffffffffe007ff0104ffbff7fefff3ffffffffffff
  | 1, 5 => 0xff3fe7fc0000ff3fe7d8f4e3ff3fe7c8f0a2ff3fe4000000ff3e47fcf0a2ff2a87fc54c3ff2007fc0000ffffffffffff
  | 1, 6 => 0xfffffffffffffffffc000208ffffe7fffdf7fffbbfffdfdfffea9fff57cfffe007ff0104ff3fe7fcfcf3ff3fe7fccc51
  | 1, 7 => 0xffe447ff2124ffe1bfff030cffe1bc000208ffe007ff0104ffe005530104ffe004000000fffffffffffffffffc000208
  | 1, 8 => 0xfffffc000208ffffe7fffdf7fffe47fff1a6fffe47fff1a6fff9a7ffcd55ffea9fff57cfffea9fff030cffea07ff5186
  | 1, 9 => 0xffffff34ce59fffffd5357cffffffd53030cfffffd5056cbfffffd40528afffffd104649fffffc370f5dfffffc340e59
  | 1, 10 => 0xffffffff030cfffffffcfefbffffffc8f2aaffffff34ce59ffffffff030cfffffffcfefbffffffc8f2aa
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 48 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 48 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 215 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 215 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 215 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 215 then wireAt i else 0
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
  | 3 => 7
  | 4 => 44
  | 5 => 284
  | 6 => 914
  | 7 => 448
  | 8 => 9
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xe016f1ac697ba5e660d4f5345d48390a2c21475e13834ac0126b557b
  | 4, 0 => 0xefef98a6e2f742a4de205fa5d6391800c856ba77c4a9aab99d188b3a8dcf53868a549240833d05507d74dbbe7c053e1a7aa0a2d078f5130876b5ac346867f20f5cb880135c6f70535b36511454f730f9544aeb544ee75b334a4c4b85435d96bb418bca293d758e5d3d54dee138fa414f347e53fc3398594730c7f6bd2cdb35f32c91b7002375bac420a4a2081fb3d5951f30b8ff1bc7e01515c1df5110a4e24c0e64c65e0b972e3e06db8e0604293864
  | 5, 0 => 0x1800e30b17d6fff4173cb54b1729da51159efd2214f7c9e71460fd0c13df58cc12dd6a6b12dc570a12c8a066127c1943123b08ea112f8e9410ee985f10d1dad410b6a5fa1081a599106d47050fcaf4390fa9e16b0f7bd8a40f768a8c0ec8d9c10e6c07390e337d6a0d31bd800cd1691d0cce82c00b74839c0b448ab70b33163d0ae07ea50ad874c50a8596bb0a667d6009ee5f490922708f0886d8ae0828ba39078a0d3b075140fd0661603805e4ea08059894120590fa4e047b153d04229cee04174def0410266603e41ee903e1877103c7271d0342755b0341fb7903331cf0030a7d9703077f450261d2e0024877fc01b28593018d520401013f36007f19e9
  | 5, 1 => 0x317991f63168dd793165560c2f0331382d9407002d18bb032d156f002cf59c9a2ceeab392cbe642c2caf01f12c9479822c2077d02b2de9d32a49171829c61d0029ae14bf295ddbb12951557b2920396c291691902874f8f32873bbb628499f7a283cd95e2802bdce27fa285b2723e9ab2705880d26b35df426aa469c2638e32a248f7e5b2473f06b2391b8a6238154d622bb5ff722536034206f9da91ffe811f1fdd54731fb620fe1ee50e861e56f8ae1e33d21a1d7982711d639c741d4df85b1cc96e391c668bb51c41f2ce1bdc02591bb66a771b89b0861acf14bd1ac11fcf1a2d924a1a20637119f86dcc1941997d1911ae4f1907eb8618d23e341860d89a
  | 5, 2 => 0x5309613152daacc152daa667511c0fe950480872500307f24fe9b00e4ead3d654e9f53f74d4164324d1acf0f4ce430cf4c9a26ec4c4012574bc994c74b040f154ac3d5c04ab4464e4a6f824f48ffee334841d718471c279b46a7bf804611b7a445d91ef145b7253845798f3944c0d694449d9d2c448bd111447770e1437c7c2b42e60c7c42b779a341f5400940db6b3940d5a92f409352af40416ff1402a13e13fa6c1e13f88d5943e88aca03e793c823cb2b8233c84b7453c5915793af440063a85a7683a54debc399b360d394b5731391f513938fa414f3871dcb537f8503b3674094b3629ca71360af0363394797732e64cc03268d4fb31d2bb4a317a69f6
  | 5, 3 => 0xa16d0a6f9e46a88e9a5a7e5f9853b55c97a9fca09562731d94337d32926b6225924f06db913a99ea912a672c9096216f9038aeca8be76a948aa95c8385d4451d848da370805f6c4f7fb22b547f5d87237ef76d3b7e586d4e7c3be1d57a85129f78a37476782faeed77be108776b57f7c740ce3b672b9d5527268845a6fe9cf806fbe083e6f556b556ec605916e13fd7c6d9b1b646d36e6b96c91270d6ababa2c6972b762691db4276884bee067cc248367ad777a66dfdc2966c3375366a200a165fc0ed964e6ab0263f5bffd61f22e7660e1ef346089f03f5f9ed2a95bf6981d5bd9197a5b97f8f85833dde5580d07b456bfbe7055b8422d54e4c8df53fe39fb
  | 5, 4 => 0xf9acd0faf7c36f05ed3f6a62ecb47af8e252891bdfedc5e6d4a464efd4434fb2d1028962cd2c456bca5d1f3fc8bcd3fdc1dce9d3c11acc9bbe469854bc03177bba9f11aab4097ad1b0ec18d8b039e7aead0ae267aca71713abecec8ca719c751a4e3c223a43f225ea3a9d24fa348344c
  | 6, 0 => 0x6a136850681af19063d52240617f3be05e1326505d56f2305b10e6b05a60d0105a123ff05687e89054f0a5e051f1fac05169eb00514ebac0511c49504c9880c04c1ddad04941f6a047e0541047d44fb0479bbe10472ece004321371041db66f041b5fb504132e6104127e5b040d80d603f1b95203b236900384d1180370e1a4033a727c030d3b30030b3eb503087e0402f13a0a02e8a90d02d1c02d02c7a62002c16857029aef9e028f84a102867f1c0285b6c5027c6a3c02734c9f0257db270248132d02470b1b022fe8a5020e0523019c9fad0195ffdc0185f46d015842e80111cbc900ad42790082d9db007dbb7a00773c2b006c2684005d9404000db973
  | 6, 1 => 0xd7a7de80d6e7ee10d4eee2d0d37f59a0cda3d310cd88bf40cd4b54f0c8f5e1d0c6f23470c6aeda60c60dcf80c3486130c18c4240be48af20bc252a20bbc56410bbafd6c0bb8a2180b7421250b28f6400b15b2110afb5dd30aa0caca0aa03d900a8213ec0a71eca00a5ed5a50a577bf40a53c4d60a4df9360a38ae290a2deef809b1e68209a7f214098c38fd096e691e0964a434093d5cf80938390c092d20e80925d5bd092491bd0913c1b10905f9ab08c00bc908828543085c29ce083843fe07f90a6207e78d0107c2594907b1fadf078c6002075c3119074eba940737882a0725e95907246e5906e5daf306e4ef6406d6bb7906c4413d06ad0f6306a40871
  | 6, 2 => 0x1499cfe5140b2e6e13faed8013e36e3c139aed6e13924c5213728f561349e7ce13470650133c08ef13197d75130e371512d03dd212c5f2cc12c36053125d0b7e1204018411ddbdec11d3a81f119fba611187183a116b4724115b67ca1144e41f1142fa4111408e9a113ee05b113ae3eb1120d646110b33071103719910d9b7f410a92875108d3a53101f34a21004efa20fe0ac610fc75d210fc153340fa2a5570f97753d0f79f41c0f78ea770f47a0390f31b5270f21afa70f10cd3b0ef095420ee5d4340ed3950c0e7e15130e7c9c400e3834050dfbaa4f0dfb96ef0dede7600de224890de1cc4b0ddd4aa00d9cbe430d9a92370d95c7350d91ebc20d8ede18
  | 6, 3 => 0x1bb1776b1ba64fad1b933b9e1b7eaebf1b7aa30b1b3ea0591b3b5e1c1b29bf4b1b110c8b1b0bab3e1ac899ce1ac6cf551a888b681a8148131a548add1a4b36dd1a1f1cf01a04d97919f6ee7f19f2db1c19d0561919cd069919ba301a198733ab1927b99a1921f28d1921237f18eabeb418e242ff18c904ec1883498818787ffd1860d89a1805550417e170dd17d6fff417b8d5e517aeb25017a260fe1794aa91177154d61749ce82173c6c16173536501729918f17224ba8170e98cc16dfb77416a82ea116741ef1164f38e016256de516100cbf15da08fc15d3ee2015c894111587591d157b3ef6156a912f1561a43a15602014155ed0bb15423b4114b47c3e
  | 6, 4 => 0x2353b18e234d11c8233e5198229eb02f22758e6922747b08224ab0272241f9d7223655962202198b21bde80721a4509b2194ff3b21730a3e214f0d11213bddeb2127260320d5617920cd427720a84c14206969b82064873a205683fe203ca24720257d1e201e2d4f2014059b200df9ca1ffd86e11fe039d21fc4f9a61fac1ffd1fabf81c1fa432931f7c1b131f6d41b71f05df5c1f0407cb1f00d5d21ee50e861eb6c6781eb0f7fe1ea6e7451e9a7a0a1e961c6a1e8f50351e7359ed1e5a4bef1e3a97551e0922ac1e06b5881e003ae81de886c51ddc850e1ddb52551d7876211d73f5661d5319ea1cc703f91c96ea491c32bad41c1250521bf0c1dd1bbaa2fd
  | 6, 5 => 0x2d2230702d19df392cf8cd042ceeab392ce3b7132cbfc8022c91587f2c7dc05e2c119b4b2c09b3112bbf56762bb2627d2b79d3f12b5b865a2b13d0122b08f8cc2afe09d52a892cd02a86ebca2a430f5929f0b1cd29dcd53d29cba47729c7962029c478db294399dc291d2a9e291385ac28e1d56328d6af5928b96dc828a1dfb0285f16652842e26227b3f541275f05d42751de462750b4f626f87edc26c46d4926bb2fef26640762265363bb262a32f425f94b5025dc2a2825d7174c25a00ed5259a313725984c9e2588220825320fbe24dc268124cbf971247367df245fcad9243d9f36241d331324190c96241577b923fade1623d675a923aa74da237418ee
  | 6, 6 => 0x36e51aae369e286b3681559c3678c0eb366fa27236588a44360d07b936042b1e35f2a557357321f8354e1e603541768b353aa3c635239d6d350fe1ad350d0fa434f524f934eff99634c7a96734c589ee34a771a73451cc6e344f47aa344da1393442a8cf33df688433da662c339be8303389f6ab33864f1f3380d2fa33722ba03331392c3326d91332eb626b32abb2013294f0e0326bf53f326a5494321d7eb2320f9fd331752de73157e49331381b073130272030f2019a30b1e59a30ad71ad30ad4672309fd64e3067a3352fc6445a2f7e6ae62f6745e12ef3a4c42eedfa852ee8e9622eafde352ea523322e4975d52e19083b2df877932d75a53d2d59ed9f
  | 6, 7 => 0x4408d56743fede5343c4e0bf43a736a4437c154542b779a342b451b04270b5be424ad53e420f288841ada2b44183d8874170ec6e416eec4f4149254d412e341e410ee2ea40e3c4e340c11d8e40c083b340a28b4c404b3013400945b43f732d3d3f2cd2183f0ad8ad3e9b06e23e69a4d83e56ef7b3e2f1fca3e277fff3e247c763e0954d53dbc5b023d820b7b3d2c7c353cfaa5163cd948b53c6b32503c61cde53c35f2033b8aa58d3b7b8ba93b526bba3af8dbf03a5085363a4cde6839ffcc7c39bb3ded39b8a2b7395f2ed0395b75dc3958c2ee394f142039200c0d38658553385c254e380d7bfe37fdfb7837a4a2c83790d59937596ec33727f4ba36fcc40a
  | 6, 8 => 0x50b4811850b1940650adf9c1504a74d84ffde7224f135c524f08c8964ee60c6c4ed752244ecc0f9f4ead7c894e64548f4e2464a44e192d344e1018c74d829fa94d2f3d364ce430cf4c54b7244c46545e4c2f2a6b4c1326ad4bb222f34b6498c74b51d8934b29df734b226b904b093b3e4af8703d4aee73794ad762854ab8c3e84a25f49949d72e874910933d49054a5d48c35a8b4854372b482bd0f548027d4547ee69e84777cddc472826684727027e46de284246dd66d846da9c4646d0e8cf46b9893046b55adf46af8fd846769a7646610b584631f35845d91ef145b72538459774c24546c2da451ed32f4519cf8c4512aef144f4548e44ecccfe44ba7785
  | 6, 9 => 0x5c9649305c8bac4c5c7754db5c50e6185c098ff55bdee7215bc68c845bc0ce6c5bb639285bb03c075ba3354b5b9302e65b7008c45b6b6fdf5b5213e25b4dbe2c5af403455aa5f5965a1dcce55a0921ad59f4348059c84b705925466958b131c858430005582969ea57f7c21f57c491b8573f285356ff19ed56f13b0e56f0cb5256ee1c3056488c3a563580cb559c0449556e5625555d1ca25551c8e555122fc954fb57fa54e2c70654dccf5d54c9884054b1935f54a96c095499a0ba53ee3c7453e4482853ce1cef53cb534053a51bbc537b088b53514afd53466db8533777b252e8c50e52adfd1052a599fd528d48c3522a087851e45e5d5138718d512f7572
  | 6, 10 => 0x6d36e6b96d18b8176d0c81136d0540346cfb7a1c6bd670bc6bd47dc36bbe0e9d6ababa2c6a91eed46a5427376a44fd666a08291469575adf68859ac8687262b76742e730672edba167296a4a66d402e566c97e4e66c9726066be836966596eea65f010c765bde69f65a1f58964aa6b446435bc2d640e6da163fb6a7f63b75a2363939f336370981063102341626898c061f617a36169ffad61444ca260e8d6d5609b7685607dc47c6042b3645ffaba205fce787b5fbac6fd5f871fd25f4ce3e85f35ba935eace41b5ea9dea95e9f053c5e5e95475e5903545e22a7545e20fc395dff8a4e5d5af03b5d4b941a5d46331d5d33d0945d0a06c85cde0cce5c9ba829
  | 6, 11 => 0x83e07d8283a21eb1837a2d438355d815833bbae2831ab88982de71178267361781e9f85c815ba2a3814662f3813c2fa481025bc4809fa26d808e9728808528c4805c9073800bb67b7f8776eb7f4ff8037ec231f37e4dc0ce7db1e1917b2f19917abe6b607ab2a4927a9f7e307a7382a17a12838178e6cebf78ce1aa778976aae785ca3c678325ccc7819d385780e8f57778f984b7776a25c7747948576f0de3376d69d9076c5d6f2764e5f6176076036751f59317461140273da4b1a737d02ed731a9a3772f1b40271f2133171a26241719e7521710cca2270b1e10170aa5d93706b57b97015ade16f63d0f66f596a256ed8da0b6e3f00b06e008d486db3cd8b
  | 6, 12 => 0xa828f69ba748d152a7204af4a6fdec6ba6c134b9a6adad0ca6a1e8eaa61dcadfa56b8c1ea4ed51b6a348344ca3098384a00c68569f281e6a9ef41ebc9ed6de7b9ed1e5489e93ebe99e56566f9d465cb99c6f27f09b34b1219aaba6e699fd1e0d986d00ac985e9e2897a70f8697708ba597012b84967fbfcb967a8905963297ec93602c4693591a6993104a2b92cd311e929d9ba6917adf6f911a430590e225fa9040bef48e5d90ed8df05ff08dacf6f48c3f36198c0a7d9d8b1bf90a8acf329f8a26beef8931d08d88f8d26988e8d84f88bd66ca8826fc3987deea958749a55b86bb689486ade397868cb4248625e7dd85d0e1f6849e475c8472dbab840e75af
  | 6, 13 => 0xe046d2d6e0129c16dfe22038df3d5635de4eb049dcfd7c6cd9fb6b94d91d26b3d87f9952d84bd8e7d7bddaafd5a9afd9d568b144d544ef90d4b91953d317dc6dd2f75b26d26e2c13d0346fc3cf2c5820cc56fb91cb22d64bcae5bbd8c9a3b4fac8bcd3fdc86c0ca2c693c559c68f6e95c63e6ab8c5d1834fc48fe98ec337f1aac2afde01c23b26dcc0d6b9cfc04eefd4c0111c56bf1537f5be3be041be3add0dbd223cdfb8ed1e4eb899e306b871b7fdb79d8b6fb666254db5e82352b37c045eb3152a51b2ef7be5b2ce525eb1559e02b0ec18d8b0754665ae03da1badcb950dac9b1be4abd5fcedab559622aa361d56a9be0bbca8f0d2eda8d62ca7a84782ef
  | 6, 14 => 0xfdd6902afc53b9bbfc344633f966b7b2f8a016c6f7368355f6e5cf63f260e8b8f12be4b6eec40f0ceafba6c3eab31e8ae66f04e6e5eea4cee41e5447e2871e2fe1660fcde0800c8d
  | 7, 0 => 0x103ead2a1004221f0ffdfe370fd4c3f50fc22fb60f9314140f5c5cfb0f3badb20edd17080ea68d810e7dd0190e589c450dfb96ef0df078900db675560d91ebc20d52c9a60d4d98860cf91d9f0c2cfbb60c22507d0bd753a90bb2ffb10b989d440b41c7720acf09dd0ab8b26f0ab7b9ae0ab0afbb0aa9dacf0a9628be0a71f9560a172c490a07e09b09f5ca2f09ee1b6f0878675807d82e3c07af559e06cd9ad406c7654b06b07a0306634425064612c7061ab28605ad2f340590310f036df1500360127103476202033b05b502d5abde0291d00a024a740d023f103c01a603fb0198251c0188fb4b0129b75500dd496a0086a50c006499150027347900103def
  | 7, 1 => 0x20df43cc2081cc612064873a2046aaad203e530f203cd04e20292edb1fe039d21fd3d3851f9bef851ee4e3db1ee472391eb3facb1e8eec381e739d441e1aa3ae1e17d8601e08e1531ca0b1831c53b96d1c1ffead1b61a0cd1b52f3321b325a461b2d157f1b1036f41a2bfa9c1a0ece7019e3604919deb3e219b1d4481979f4171923eb0b1900f42918e3fb0a183e8305181aa94117d7cb9517d07b0017a82026175a929b170db67f16e8db1816b50ee916a82ea115ff8a4715f86a801561a43a1528ba3c1413d60814121a0c13b5da6d135211a21317dd2b130748e512b8884a12ae5da3129997eb124e263511eb7ccf11d7480611b4128d1187183a11761aa8
  | 7, 2 => 0x359f67e7355e29ce3528ce7834ceb8d1342cdee933ab0d0832e7627a32c3d3da32ba82ac329cbbfb3294bf40326a06213243d5cd31381b0730bda81a2fc976f62fa1c82a2f7655c82eedfa852ee51d392de85b922dd8b4022daad2e42d6df75a2d014b912cf3c0ef2cb7e2692cae27f22ca821632c1543872bdd94e82b48380c2b0f56702af4104e2a5175e429f0f18429e942c429c478db2838c79a2775450f2774c460275958f226e36c2426beaf6f26bb2fef26aa53c326a4b5bf264ea121262d41fb26093241259eb530255ffecb24cb7b29246ade9623fe6fae23afce922325e28c231857ea2310763b23038dd422d85c9a2236825921a5f9682179389d
  | 7, 3 => 0x4f9b055d4f943bc44f717d1d4f0fba7a4e2ce2974cd8ba054c173de94c1326ad4bb222f34b62f61f4b02825d4a6707154a5928364a0d197449e125c648b0ac9d4879fd8347f69d26475141bb46e1bded46e149a245c07cca44cd758b43b9f0a34365b3a943555fb04305883642b779a34215deda41d622d341a4b5d6413f306a413ca6964079af633ffca0873f49363a3df1aaf13cedcf813c9f3cdf3c8fe41f3c52b0633c3d49423c38e0113c21f90f3bc2d8a43b76a7473b3c318a3afd7b253acd3e823a8b9b213a47663439de879e3958c2ee39500340387c221637dd7e80375fd1e83732d33a3724f45b36e4026d36c744ae36b6da92363c57f4361b1af4
  | 7, 4 => 0x6af785736aa2ab606a7ff6686a510b386a4f22086920920f688d1b55683fb3fc679d352a67044c4c66fb4c9166742ba76659a12a647899486379a6766336351163353df46329b29363275f1562b43c176292bf226240ab876001a2b65ec6f1c75e1657ce5e06e6065d93d62e5d7bf2db5d6275f45d5af03b5c91de815b4388f85af03eb05a1dcce559f223e559e5330159d66aa0596cee2e5943cbfb58a5f17758905d1356da22f0568ff7f15640306856240dff54b47b98531915d15314eaf652f2fea452acbe7d528ca242523dc21151d2062b51bf3f2b51a4e007516924ff515c2919514f645451099cc651007c3a50c9577f50c4b4ed500139404fb2394c
  | 7, 5 => 0x9b308e9f9a9c46339985b80798553ede963c456d95a996be955a089892a6c201927a567e925c0be4911fd2258f7fd14d8f78512d8f46f2108df2ab598d92f6958c8386ea8bc68b508b308e208a81f0ca8968a0cb88ede028877910e2876b3203867726a18651842c85faf2fb85ba4fb98549f6d285210b038492c7cd83f048fb83c5bc5283233d80828511a47f97da8d7f27d8097db1e1917d776c2f7c3be1d57a9f7e307a70b1287892577576f0de3376f0916b76eecc3f76db0b2e766385db751f5931745a681c73f60c3a73227b8e72b2833971fb25a270b1e101707cee8d6f3b46226e8018a76ddedbb86d9b14bb6d45b13a6cbe1d396bc490ee6b46b4d1
  | 7, 6 => 0xffcceadcfe12eeb4fce2758bfc3cf275f734b506f11d8484f053c1fdee22ff53e73f702ce7283c3de1660fcde07b344edede789bdb59af84d9eccea3d87f9952d7d8277ed7c2c847d697c1d4d6890d25d56748abd2f75b26d051c79bcf6e15b1ce3bc8d3cda803e7c8d8951dc6f762cbc1c5a5bebef4bb49bee065e9bd2744b8bd223cdfbc008a33bbe49247bab08b31b69fded2b3feb3cab253eee6b23cd636b1b17014b12375bdb108215ab080f6ebafd2c793aee65ee3aec64c0ead85a160aa3f12b1aa2867c5a98c5b5da8e78fc4a8d69abba840633ca7204af4a4a02823a494c22fa4540600a3f2435da0c045e29e6bbe4b9d3508f49c55bf839b71391a
  | 8, 0 => 0x7e1a8a567cea112d705b5d9f5059633d4f8c57c242b779a334064f6c2efbd9641b78d4bc
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x475802148440000000450c4203700855048440067081154804005758021484400170813548040000000000c8106
  | 4, 0 => 0xc910900000000c910900000000c41080000020441202001195008530000000254402000000052041200000000000000600000000c91090000010440200000412544030000000350412000004145440300474854508440000180124413000000000000000000002044120247580214844000000000104103000001004120000000250412000000000000003000003044120200000000c4108000003044120200000000c410800000450c8203000000010810300000304412010000000000006000001548020000000000c910a
  | 4, 1 => 0x2148420000118514813007608550484400001802148430000000000c8106000981044030000000304412043608550484400700855048440000000000c910a000981044030000000000c8108
  | 5, 0 => 0xc81080000000000003000c8254c03000000000080100000000000000600000000c81030010815500300000000000000b000000000000e000004350c200000000010810300000000c410300000001081020000000041102000000010810300000000000060000000000006000000000000c000d815412300001441248130000000000000050018545041300000000010810100000000000060011825406300000000004110100000001081030000000104103000d421441300000000000000000000324c82000000000000002
  | 5, 1 => 0xc81060000035480200000000000000300000000c81060000000000008000000000000a000001508120000000000000060000000000006000000000000e00000450812000000045041200000000008110000000454c02000000000108103000000000000700115410853000000000041100000000000000500104355003000000000104103000000000000900000000c41080000000000001000000000000800000000000010000000108103000000000000d000000000000c000000000000e00000001041030000000000006
  | 5, 2 => 0x108103000000000000800000000c41060000000000006000000000000a001182550030000000000000090000045480200000000000000b00114350413000000000000002000000000000c001884540630000000000c910a0000000041102000000000000900000000c810600085350843000000000000008000000000000b000000000000600000000c410600000000c8103000000000000a00000000411040000000000003000000000000900000000c8108000000000000b000000000000c00000204412020011925006300
  | 5, 3 => 0x800000000c4103000000000000e00000000c4108000000000000600000200812000000020441202000000000000d0011935006300000000010810300000000c810600000450412000000000000000000000000000a0000000000000000000000000e000000008d109000000000000c000001548020000085450843000000000000006000000010110200000000000060000045041200000000000000b00000000c810800000000000030000000000007000002048020000000000c410600000001081030011850485300
  | 5, 4 => 0xc1102000000000000000000000c41080000000000009000004350c20000000000000080000000108103000000000000500000000c41080000000081100000000000000d0000000041101000000004110100000000411010000000104103000003510820300000324c820000000000000030000000080100000000000000e00000000c410800000000000000000045480200000000004110100000000c8103000000004110100000000c410800000450812000000000108103000000500a2000000000108103000000000000b
  | 5, 5 => 0x104103000000000000a000005008520000085504843000000020441202000000000000300000510812000000010041200000000000000b00000000c8103000003504120000000000000020018c45406300000000000000a000000000000e00000000000020000020441204000000000000900000000c910900000204802000014821441300000000000000500000000411010010d450c830000000154c02000000000000003000000000000c00000000000040000000000001000000000000e00000000000070000000000006
  | 5, 6 => 0x411020000000041102000000004110400000514812000011412481300000002008120000000000851000000015480200000001044020000000154c020000000001081030000000000003000000000000000000000411040000000000005000000000000600000000000000000000100100000000000000500000000c81060000015081200000002048020000000000c910a000005110120000000000000070000000000009000000000000300000000811000000000081102000000008010000000000000030000000104103
  | 5, 7 => 0xc81080000000000001000000000000800000355002000018021484300000000010d105000000000000c0000021484200000000000000300000000401000008550484300000d92148430000000000000090000000081102000000000000500180124813000000000000009000002148420000000154c0200000000000000d0000000000000000000000000000000405002000000000108101000003044120400000000000050000000000002000000000000e0011825441300000003510120000000450c8203
  | 5, 8 => 0x2148420000000000000030000000000000000000000000a000000000000500085504843000000000000003000000000000c000000000000e000000000000a0000000000005000000000000000000000000030000021484200000000000000b000000000000b0000000000005000004050020000000000000030011950085300000002048020000000000411020000053101200000000000000d00000000801000000015480200000000000000b0000000000003
  | 6, 0 => 0x1540a20000000000000020000000000009000000000000b000000000000300000154c0200000000000000600000314c4200000000000000600000000000000000000041101000003508520000000000021000000000000007000000000000a000000010810200000254c420000000000000060000000000004000000000000800000314c4200000000000000c000000000000200000000000070000000000006000002544120000000000000030000000104103000000008110000000314c420000000000000090000000000004
  | 6, 1 => 0x2048020000000214842000000000000009000000000000500000000000060000000000003000000000000600000000411040000000000006000000000000500000454c02000000000000008000000000000300000000000010000000000003000000000000d0000000000003000004504120000000000c1104000000000000600000000000000000000000002000000000000100000000000030000035480200000000000000000000000c1101000000000000400000000000030000000000004000000000000c0000000041102
  | 6, 2 => 0x354802000000000000001000000000000500000000000030000000000008000000010810100000000000040000000000005000003548020000000434c420000000450812000000021441200000000000000c000000000000800000000c01000000000000003000000000000c000004204920000000000000040000045081200000000000000300000000000020000021484200000000000000100000000000060000000000002000000000000600000450812000000000080100000000000000100000000c81030000000000008
  | 6, 3 => 0x70000000000002000000000000200000000c810800000354852000000050508200000000000000c0000045480200000000000000b000000000000800000324c820000000000c110200000000000000000000000003000004548020000000000c8103000000000000300000254c0200000000000a1000000000000005000000000000e000000000000d00000000000000000000000001000000010c101000000010c1030000000000003000000000000400000000000020000000000008000000000000d0000000000008
  | 6, 4 => 0x811040000035081200000000000000500000324c820000000000000000000035500200000000010d107000000000000300000505042000000035041200000000000000a000000000000500000000000010000000000002000000000000600000000851000000000000009000000000000e0000000002100000000000000c000000010c10200000314c4200000000000000100000000000080000000041101000000000000700000000000000000015002200000000000000500000000000060000000000002000000000000e
  | 6, 5 => 0x100000314c420000000000000030000000000006000000000000200000000000040000000000009000002048020000000000000040000000000006000000000000b00000454c02000000000000006000000000000000000000000020000000000003000005008520000000454c020000000000000080000000000003000000000000300000254c42000000000000001000002504120000000000c41000000010440200000000000000a000000000000800000000000020000000000009000000000000c0000000000008
  | 6, 6 => 0x20000000041102000000000000200000000000010000000000006000004350c200000000000000b000000000000b0000000000006000000000000e00000000000030000000000003000000000000200000001041000000000000003000000000000a0000000080100000000000000600000000000070000000041101000000000000100000154c0200000000000000c000000000000300000000c81030000000000006000000004110400000000061000000000000001000001044020000000350812000000000000006
  | 6, 7 => 0x50000000000009000000000000600000000c11040000000000004000000000000800000345082000000000000001000000000000e000001500a20000000000000060000000000006000000000000600000304c0200000000000000400000000000030000050484200000000000000300000000c01000000000000001000000010d107000000000000300000028062000000000041101000000000000d00000000000030000000000000000000000000300000000000010000000101102000000000000c0000000000001
  | 6, 8 => 0x40000000000003000000000000800000454c0200000000000000900000000411040000000000006000000000000200000000000050000000000003000000000000500000154c0200000000000000a0000000000001000000010c100000004150420000000000000030000015500200000004350c200000000000000300000154802000000000000003000004500a2000000000000005000003500a20000000000000010000000000003000000380a2000000000000006000000000000100000000000040000000000001
  | 6, 9 => 0x124482000000000041101000000000000300000150812000000000000006000000000000e00000000000070000000000008000000000000200000000000020000035041200000003108520000000000811040000000000002000003504120000000000000080000000000006000000584120000000000000000000000000003000000000000d000000000000300000000000050000000000001000005210520000000000000030000000000008000000000000300000350842000000015500200000000000000c0000000000002
  | 6, 10 => 0x40000041504200000004508120000000540c120000000000000030000021484200000000000000700000000411010000000000001000000000000600000000000010000000000003000000000000b0000035041200000005310120000000000000070000000000006000000004110100000000c810600000000000010000000000007000000000000100000310c020000000000000000000000000001000000000000700000000c4103000000000000d00000214412000000000000000000000000000300000520c1200
  | 6, 11 => 0x7000000000000300000000000050000000000002000000000000300000000c91000000045480200000000000000b00000000c11010000000012100000000000000600000350412000000000000004000000000000600000000000050000000000004000000000000800000000000020000000108103000000000000c000000000000900000000000030000000000008000000000000900000000000030000000000002000000000000a0000000000002000001044020000000000000090000000000003000000000000a
  | 6, 12 => 0x214842000000000000003000000000000c000000000000800000425082000000000000003000000000000200000154c020000000000811040000000000003000000000000400000000000020000000000006000000000000600000000000020000000000008000000000000300000000000080000000000003000000000000500000304c0200000000000000500000000000030000000012100000004350c200000000000000e00000324c8200000000010810300000000000010000000000000000000000000c0000000000003
  | 6, 13 => 0x10110100000450812000000000000003000000000000600000000000010000002802200000000000000c00000000000050000000000000000004508120000000314c8200000000008010000000000000080000000000005000001244820000000058c4200000004350c200000000004110100000000000060000000000004000002048020000000000000060000020480200000000000000300000450812000000021484200000002048020000000000000050000000000003000000000000500000000000040000000000008
  | 6, 14 => 0x70000000085100000000000000b000000480e20000000000c410800000000000030000000000001000000000000300000000c4108000000000000600000454802000000000000003000000000000600000454802000000000000002000004544020000000000000010000000000004000003504120000000000411010000000100100000000000000a0000045480200000000000000a0000000000004000000000000600000000000080000000081102000000000000b000000000000c00000154c02000000000041104
  | 6, 15 => 0x8000000000000a0000000000002000000004110100000154802000000000000000000004350c2000000000000006000004350c20000000000000080000000000007000004350c20000000000c81030000021484200000000008110400000000000020000000000006000000000000600000000000050000000000003000000004110400000000000080000000000001000000000000a000000000000300000000c81060000000041100000003504120000000314c420000000000000060000000000002000001500a200
  | 6, 16 => 0x20000000000004000000004110000000324c8200000000000000200000000d010300000000021000000000000003000000000000400000000c410300000000000000000000081102000000000000500000000000020000000108103000001541220000000000000080000045480200000000000000600000000000080000000000005000000000000300000000000030000000000000000000000000600000000000030000000000009000000000000c000000000000200000000000090000000000001
  | 6, 17 => 0x10000040500200000000010010000000000801000000041085200000004350c20000000000000030000000006100000000000000500000000c810300000000000050000000000008000000000000200000000c810300000000000030000000000006000000000000b0000000000002000000000000300000000000010000000000003000000000000200000454c0200000000000000e00000510c12000000053101200000004250820000000000000030000000000001000000010110000000314c4200000000000000b
  | 6, 18 => 0x48022000000001802200000000010010000000000000040000000000002000000000000200000000c410600000000000060000000000003000003508120000000154c020000000000000020000000000006000002048020000000000000030000000000001000000000000100000000000030000005884200000000008110200000154c0200000000010010000000405002000000000000003000000000000500000154c02000000000000005000000010810300000000000050000000000003000000000000a0000000000001
  | 6, 19 => 0x30000000000008000000000000200000304c02000000015480200000000000000500000000411010000000000007000000000000100000000000030000000000006000000000610000000000000000000000000001000000008410000000000000020000000000006000004050020000000000000010000000000003000000004110100000255002000000003802200000000000000e00000155002000000000000000000000010c10000000000000050000025500200000001548020000000000000060000000000008
  | 6, 20 => 0x204802000000000000003000000000000b00000204802000000045440200000000000000500000000811010000000104103000000000000200000000000090000000000008000005210d2000000000000006000000000e10000000000000050000000000003000002148420000000531012000000000000008000000000000200000104402000000000041101000000010d100000000000000000000000411000000000100100000000000000c000003500a20000000450c820000000000000060000000006100000000000000c
  | 6, 21 => 0x300000000000070000000000003000000008110400000000000040000000000008000000010810300000000000020000000000003000000000a100000000000000b0000035500200000000000000300000000000020000000000006000000001210000000000000030000000000004000000000000100000000c8106000000000000400000405002000000025440200000000000000c000000010c102000000000000600000000000080000000000000000000000000000000000c810600000000000030000053101200
  | 6, 22 => 0x154802000000000000007000000000000000000000411040000015480200000002144120000000124482000000000002100000000000000100000000000050000000085100000000000000400000000121000000000000002000000000000000000154c0200000000000000100000000000030000000000002000000000000300000450812000000000000003000004548020000000000000030000035500200000000000000400000000000030000000000001000004350c20000000000000010000000041104000000000000c
  | 6, 23 => 0x1011020000000000005000000000000400000454c020000000000000030000000000003000000540620000000154c0200000000000000800000540c1200000000000000600000154c02000000000000003000000000000600000540c12000000025406200000000000000300000154c02000000000000007000000000000500000000000000000000000007000004540a20000000000000060000000000002000000000000c0000053101200000000000000400000000000030000000000009000000004110400000000c8103
  | 6, 24 => 0x5000000000000800000000000030000000000009000000000000500000000811020000000000006000000000000500000000c910900000000000020000000000008000000000000400000000000070000000000003000000004110000000124812000000000000006000000000000300000355002000000000000000000000000000300000405002000000000000004000000000000b00000000000060000000000008000000000000a00000000000060000005885200000000000000800000001011000000000000004
  | 6, 25 => 0x4050020000000154802000000000002100000000000000700000000000030000035500200000000010c1030000015480200000000010c1030000015480200000000000000300000000000090000053101200000000000000300000000000030000000000000000000000000200000204802000000000000003000000000000c000000000000400000000401000000000000004000000000000200000000000070000015480200000000010d1000000021484200000001500a200000000000000100000000000040000000080100
  | 6, 26 => 0x8410000000000000040000000000001000000000000600000450852000000035500200000000000000d000000000000300000000021000000000000001000000000000600000000000000000000000003000000000000000000405002000000000000003000000000000100000000411040000005885200000005048520000000000000030000000002100000000000610000000531012000000053101200000002500220000000000000050000000000002000000000000a000005048420000000000000050000000000003
  | 6, 27 => 0x80100000004350c2000000000000002000002148420000000214842000000000002100000000000000b00000000000030000000000003000000000000000000000021000000000000003000000000000b000000000000000000000401000000000000006000002544020000000214842000000000000004000000000000300000000000050000000000005000000010c103000002148420000000000000000000000000003000000000000000000000411020000025441200000000000000c00000000000050000000000003
  | 6, 28 => 0x25441200000000008510000000000841000000000000004000004350c20000000000000040000000000003000000000000c0000000000001000002544020000000214842000000000000007000000000210000000154802000000000000003000000010c10300000000401000000000000002
  | 7, 0 => 0x200000000000060000000000002000000000000600000001001000000000000002000000001210000000000000040000000000002000000000610000000000000010000000000005000000000000500000000000040000000000001000000010010000000000000020000000000000000000000000800000000c810000000000c4100000000000a10000000000c91000000000006100000000000000b0000000012100000000000000000000000c910000000000000060000000105100000000001210000000000c9100
  | 7, 1 => 0x10000000100100000000000e10000000000c8100000000010c10000000000021000000000000001000000000000300000000000020000000000001000000000a100000000000000400000000000010000000000002000000000a1000000000000002000000000a100000000000000600000000000030000000000001000000000a1000000000000004000000000000300000001051000000000104100000000000000300000000c9100000000010c1000000000000007000000000000200000000000040000000084100
  | 7, 2 => 0x6000000010410000000000000000000000000008000000000000800000000000030000000104100000000000000100000000000000000000000003000000010910000000000000060000000000003000000000610000000000000010000000006100000000000000200000000000020000000085100000000000000300000000401000000000000002000000000000200000000411000000000000000000000000000200000000000080000000041100000000000000600000000000050000000000003000000000000e
  | 7, 3 => 0xc91000000000000006000000000000300000000c410000000000000080000000012100000000001210000000000000030000000000003000000000000100000000c410000000000000040000000000006000000000000e00000000c5100000000000000300000000c410000000000c910000000000061000000000000006000000000210000000000000080000000002100000000001210000000000000050000000000007000000010410000000000c1100000000000000200000000c0100000000000a1000000000000004
  | 7, 4 => 0x10110000000000c51000000000000004000000000000200000000000060000000000003000000008410000000000000040000000000008000000000000000000000000070000000000006000000000000300000000000020000000108100000000000000c00000001001000000000000000000000000000c00000001041000000000100100000000000000100000001001000000000101100000000000e100000000000e100000000000000400000000061000000000000000000000000610000000000000080000000109100
  | 7, 5 => 0x61000000000000001000000010c1000000000000001000000000000800000000000030000000000003000000000000100000000411000000000000004000000000000200000000000030000000000001000000000000200000000d110000000000c9100000000008010000000001091000000000012100000000000000300000000121000000000000008000000000000b00000000c9100000000000e100000000000e100000000001210000000000000010000000000002000000010c1000000000000005000000010c100
  | 7, 6 => 0x4000000004110000000000c810000000000411000000000012100000000000000100000000000010000000012100000000000000400000001011000000000108100000000000210000000000121000000000000004000000000000100000000c9100000000008410000000000811000000000012100000000000000100000000000030000000000003000000000e1000000000000004000000000000600000001011000000000000002000000010d1000000000006100000000000000c00000000000030000000000005
  | 7, 7 => 0x30000000006100000000010d100000000008510000000000061000000000041100000000010c1000000000000002000000000000300000000000030000000000006000000010d1000000000000002000000000a10000000000021000000000002100000000000000400000000000010000000000003000000000000200000000c110000000000000030000000100100000000000000200000000000030000000000000000000000610000000000000000000000000004000000000000300000000411000000000000001
  | 7, 8 => 0x85100000000000000100000001011000000000000005000000010c100000000010c1000000000000009000000010c100000000010110000000000000010000000000001000000000210000000000000040000000002100000000008110000000000000000000000000002000000000000600000001001000000000002100000000000000100000000000040000000000006000000000a10000000001001000000000000004000000000e10000000000000070000000000001000000000610000000000801000000000002100
  | 7, 9 => 0x10d100000000001210000000000061000000000012100000000010d10000000000121000000000000004000000000210000000000851000000000000002000000000000300000000000040000000000002000000000000000000000c81000000000000003000000000210000000000000040000000000006000000000e10000000000491000000000000003000000000000200000000000020000000000004000000000000700000000000030000000006100000000000000c000000000000300000000121000000000000001
  | 7, 10 => 0x2100000000008510000000000000030000000000004000000000000300000000000020000000000003000000000000000000000000020000000000005000000010110000000000021000000000000006000000000000400000000000030000000000003000000000000600000000000040000000040100000000000000c00000001011000000000000001000000000000300000000000010000000000002000000010d1000000000000005000000004910000000000000010000000000004000000010d1000000000041100
  | 7, 11 => 0x40000000000004000000010d100000000010d100000000000000200000000000010000000000005000000008410000000000000040000000000006000000000000600000000c010000000000000030000000100100000000004110000000000000050000000040100000000010d10000000000000030000000006100000000000000c00000000021000000000040100000000000000600000000000000000000101100000000010c100000000010d1000000000000008000000010110000000000021000000000085100
  | 7, 12 => 0x300000000000020000000000002000000000210000000000000060000000084100000000000210000000000000010000000049100000000000210000000000c010000000000851000000000085100000000000000b00000000c11000000000000001000000000000000000000000040000000081100000000004110000000000401000000000084100000000000210000000000061000000000002100000000000000600000000851000000000080100000000000000b000000008110000000000000060000000084100
  | 7, 13 => 0x2100000000004810000000000841000000000000003000000010c100000000000000b0000000084100000000000610000000000021000000000000008000000000000300000000851000000000000003000000000000000000000000030000000000003000000000e100000000004010000000000401000000000000007000000004010000000000000030000000084100000000000000300000000c01000000000000001000000004010000000000000060000000080100000000000000100000000000030000000002100
  | 8, 0 => 0x0
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 8 s ws hint
  | 1 => checkCutEntry dom_3 roots_3 6 s ws hint
  | 2 => checkCutEntry dom_4 roots_4 6 s ws hint
  | 3 => checkCutEntry dom_5 roots_5 6 s ws hint
  | 4 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 5 => checkCutEntry dom_8 roots_8 5 s ws hint
  | 6 => checkCutEntry dom_9 roots_9 5 s ws hint
  | 7 => checkCutEntry dom_10 roots_10 5 s ws hint
  | 8 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 9 => checkCutEntry dom_11 roots_11 5 s ws hint
  | 10 => checkCutEntry dom_12 roots_12 5 s ws hint
  | 11 => checkCutEntry dom_13 roots_13 4 s ws hint
  | 12 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 13 => checkCutEntry dom_14 roots_14 4 s ws hint
  | 14 => checkCutEntry dom_15 roots_15 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_16 goalM u ys := by
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_16 == dom_16) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_16 goalM u ys) : RunD dom_16 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_16 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 2 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 2 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 8 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_8 : ∀ i, 8 ≤ i → i < 13 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 8 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 13 → Z 3 i = true := range_split z3_0 (z3_8)
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
theorem z4_64 : ∀ i, 64 ≤ i → i < 65 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 64 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 65 → Z 4 i = true := range_split z4_0 (range_split z4_8 (range_split z4_16 (range_split z4_24 (range_split z4_32 (range_split z4_40 (range_split z4_48 (range_split z4_56 (z4_64))))))))
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
theorem z5_152 : ∀ i, 152 ≤ i → i < 154 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 152 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 154 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (range_split z5_56 (range_split z5_64 (range_split z5_72 (range_split z5_80 (range_split z5_88 (range_split z5_96 (range_split z5_104 (range_split z5_112 (range_split z5_120 (range_split z5_128 (range_split z5_136 (range_split z5_144 (z5_152)))))))))))))))))))
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
theorem z6_264 : ∀ i, 264 ≤ i → i < 265 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 264 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 265 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (range_split z6_184 (range_split z6_192 (range_split z6_200 (range_split z6_208 (range_split z6_216 (range_split z6_224 (range_split z6_232 (range_split z6_240 (range_split z6_248 (range_split z6_256 (z6_264)))))))))))))))))))))))))))))))))
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
theorem z7 : ∀ i, 0 ≤ i → i < 144 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (z7_136)))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 17 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 16 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 17 → Z 8 i = true := range_split z8_0 (range_split z8_8 (z8_16))
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
  scr dom_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_16 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_16 roots_16 goal_16 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_16 goal_16 := by
    have h0 : isConstB dom_16 goal_16 = false := by decide +kernel
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

end S_16

theorem low_16 : Lower dom_16 roots_16 goal_16 10 := S_16.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_16_bits : ∀ r : Fin 64, roots_16.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_16_lt : ∀ r : Fin 64, dom_16.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_16 T)
    (hlow : Lower dom_16 roots_16 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_16, Avail mask256 roots_16 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_16 hfan 0 roots_16 roots_16 rfl hsup0
  set out := (execN C.gates roots_16).getD C.output 0
  have hout : out &&& dom_16 = T &&& dom_16 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_16_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_16 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_16_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_16).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_16)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_16.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_16 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_16).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_16 &&& mask256 = dom_16 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_16 = T &&& dom_16 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_16, hd63, hout]
  have hnc_m : ¬ IsConst dom_16 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_16 roots_16 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_16, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_16 roots_16 0 roots_16 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008373984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_16.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_16 10 hT6 (by unfold IsConst; decide) low_16

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [3, 2]⟩, ⟨GateOp.and, [7, 4]⟩, ⟨GateOp.and, [9, 2]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [11, 5]⟩, ⟨GateOp.or, [9, 8]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_16707_aux

theorem PEqualNP.Outside.L_meta_16707 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008373984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008373984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_16707_aux.wit, PEqualNP.Outside.L_meta_16707_aux.wmono, le_trans PEqualNP.Outside.L_meta_16707_aux.wsize (PEqualNP.Outside.L_meta_16707_aux.lower s hs), PEqualNP.Outside.L_meta_16707_aux.weval⟩
