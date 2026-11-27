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

namespace PEqualNP.Outside.L_meta_16653_aux

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

def dom_0 : Nat := 0x5555000000000000
def goal_0 : Nat := 0x5440000000000000
def roots_0 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [54, 58, 54, 60, 58, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_0 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_0 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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

def dom_1 : Nat := 0x5555555500000000
def goal_1 : Nat := 0x5440444000000000
def roots_1 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 44, 60)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0x3333333300000000
def goal_2 : Nat := 0x3222202000000000
def roots_2 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xffff000000000000
def goal_3 : Nat := 0xfeea000000000000
def roots_3 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_0

def dom_4 : Nat := 0xff00000000
def goal_4 : Nat := 0xe800000000
def roots_4 : List Nat := [0xaa00000000, 0xcc00000000, 0xf000000000]

namespace S_4
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (34, 35), (34, 38), (36, 37), (36, 38)]
def r1sG : List Nat := [33, 33, 34, 34, 36, 36]
def r2sG : List Nat := [35, 37, 35, 38, 37, 38]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_4.map (· &&& dom_4)
def goalM : Nat := goal_4 &&& dom_4
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x7cdd6334
  | 3, 0 => 0x7cdd6334
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000cc00000000000000aa00000000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_4 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
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

def dom_5 : Nat := 0xff00ff00000000
def goal_5 : Nat := 0xea00e800000000
def roots_5 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000000000, 33, 49)] (by decide +kernel) (by decide +kernel) low_4

def dom_6 : Nat := 0xff00ff0000000000
def goal_6 : Nat := 0xfe00ec0000000000
def roots_6 : List Nat := [0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3

def dom_7 : Nat := 0xffff00000000
def goal_7 : Nat := 0xece800000000
def roots_7 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_8 : Nat := 0x3300330000000000
def goal_8 : Nat := 0x3200200000000000
def roots_8 : List Nat := [0x2200220000000000, 0x3000300000000000, 0x3300000000000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_9 : Nat := 0xf0f0f0f00000000
def goal_9 : Nat := 0xe0a0c0800000000
def roots_9 : List Nat := [0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000]

namespace S_9
def pairsG : List (Nat × Nat) := [(33, 35), (33, 49), (34, 35), (34, 42), (40, 42), (41, 43), (41, 57), (48, 49), (50, 51), (50, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [33, 33, 34, 34, 40, 41, 41, 48, 50, 50, 56, 56]
def r2sG : List Nat := [35, 49, 35, 42, 42, 43, 57, 49, 51, 58, 57, 58]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_9.map (· &&& dom_9)
def goalM : Nat := goal_9 &&& dom_9
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x9713a9dd
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000f000f00000000000c0c0c0c000000000a0a0a0a00000000
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_9 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
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
  scr dom_9 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_9 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_9 roots_9 goal_9 4 := by
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

theorem low_9 : Lower dom_9 roots_9 goal_9 4 := S_9.noCircuit

def dom_10 : Nat := 0xffffffff00000000
def goal_10 : Nat := 0xfeeaece800000000
def roots_10 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

namespace S_10
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 42), (41, 43), (41, 45), (41, 57), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 34, 34, 34, 36, 36, 40, 41, 41, 41, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [35, 37, 49, 35, 38, 42, 37, 38, 42, 43, 45, 57, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_10.map (· &&& dom_10)
def goalM : Nat := goal_10 &&& dom_10
def NN : Nat → Nat
  | 4 => 1
  | 5 => 13
  | 6 => 8
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x20ec3cb5
  | 5, 0 => 0xeea07002e139fe35cd07a878b8694a069e2cbe827a5a941b61cc1db65afe27272830407a15350e9c0467640c0433e158034654af
  | 6, 0 => 0xeea070028f1909028986d9d57523d75b7402c7fe608578e95f5ce351527e0458
  | 7, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaaaaaa000000005555555500000000333333330000000011111111000000000f0f0f0f00000000030303030000000000ff00ff000000000000ffff00000000
  | 0, 1 => 0xff00ff0000000000fefefefe00000000fcfcfcfc00000000fafafafa00000000fafa000000000000f0f0f0f000000000eeeeeeee00000000cccccccc00000000
  | 0, 2 => 0xffffcccc00000000ffff000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x107b5895
  | 5, 0, 0 => 0x107a0e3583dca41d8107a8c5503d4728162f520e3683dac41da0f520e460410718560f520e267b16a41d8107a0c3583d8a4a18117a0e35
  | 6, 0, 0 => 0x41e838d60f6a907683d4838d8107a9065045ea41d40f520e05041ea41d60f525076
  | 7, 0, 0 => 0x107a9075
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 29
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x703fffc7e3f1ff8ff8f1c0e3c79ff023c1c7f01fe007fff
  | 0, 1 => 0xe03f800fdfbfc7ee1f0387ec71c00000e1c3000e1c7e070038
  | 0, 2 => 0x3ff0071ff8000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x24cf27ed986c2d1b88d20400062c59690220103701be0037fb
  | 0, 1 => 0xf23f907ffffff7eeff77bfedfbde4024e9d349bf7ffe9723b9
  | 0, 2 => 0x3ffd77bffc804
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 25 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 25 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 18 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 18 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 18 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 18 then wireAt i else 0
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
  | 3 => 2
  | 4 => 11
  | 5 => 72
  | 6 => 12
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0x7b0c59c06151fc20
  | 4, 0 => 0xede4ed11bac053868d40d81d7402c7fe6a8753ee657f8e1b643ce6935f5ce351288e1adb187e076f0467f571
  | 5, 0 => 0xc3341b19beede581bc17d563b81b9f6aad9afddca4918cb09346a38b93416f8b8f1909028f0d19b08be008488986d9d586cfb07d7fbe758d7ed1b8ed7d657ff37c8b9fea77414dc8756547847523d75b7402c7fe72a4d84a71cd33b46cb21d2a67c40f466723e9056259fa14608578e95fcdfb9d5f5ce3515f2e44265e3bd3f45a61311f54386dd352fb0175527e04584fbea8484a2f49654906851945c2944c4403f99c3d1afebe3c4159333a877c60358964b8331bf618327505b02f5e14ef2b87dba629d28c3728ce4bfb273b926c245df8de239e6b9322e2bbd21e7aa2e01dcf21031c4825ff14f7ea31127d1d850ed6daef08b93179080fb46f059706fd
  | 5, 1 => 0xe6af2f83dc1b0d52d71579e4d5a212edccf2db85cce3300ecbe6991bcb98ee7f
  | 6, 0 => 0xccf2db85a4918cb086cfb07d7d657ff35fcdfb9d4fbea8483c415933358964b82f5e14ef273b926c1dcf2103059706fd
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x0
  | 4, 0 => 0x90000000000730440084101000000000000000000000300000400004
  | 5, 0 => 0x80000000001000000000004c1100000008000040000040000000000800001000000000000000040000100000c00002000000000020000000000700001481101000004000050000108110200001c0000400000400002
  | 5, 1 => 0x8000000000240000830440000001000010000040000040000500000c00009000000c51033044080000131440c0000220440400000000004c110210441000000314410000010000000000200000800000000014c1100
  | 5, 2 => 0x1c00000000024000070000080000600000400007
  | 6, 0 => 0x8000040000000000100001400002000008000000000040000200000400003
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 8 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 3 => checkCutEntry dom_5 roots_5 5 s ws hint
  | 4 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 5 => checkCutEntry dom_7 roots_7 5 s ws hint
  | 6 => checkCutEntry dom_4 roots_4 4 s ws hint
  | 7 => checkCutEntry dom_8 roots_8 4 s ws hint
  | 8 => checkCutEntry dom_0 roots_0 4 s ws hint
  | 9 => checkCutEntry dom_9 roots_9 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_10 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
theorem z5_8 : ∀ i, 8 ≤ i → i < 13 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 8 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 13 → Z 5 i = true := range_split z5_0 (z5_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := z6_0
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
  scr dom_10 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_10 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_10 roots_10 goal_10 8 := by
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

theorem low_10 : Lower dom_10 roots_10 goal_10 8 := S_10.noCircuit

def dom_11 : Nat := 0xff000000ff00
def goal_11 : Nat := 0xec000000c800
def roots_11 : List Nat := [0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000]

namespace S_11
def pairsG : List (Nat × Nat) := [(9, 11), (10, 11), (10, 14), (10, 42), (12, 14), (13, 15), (13, 45), (40, 42), (41, 43), (41, 45), (44, 45), (44, 46)]
def r1sG : List Nat := [9, 10, 10, 10, 12, 13, 13, 40, 41, 41, 44, 44]
def r2sG : List Nat := [11, 11, 14, 42, 14, 15, 45, 42, 43, 45, 45, 46]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_11.map (· &&& dom_11)
def goalM : Nat := goal_11 &&& dom_11
def NN : Nat → Nat
  | 3 => 5
  | 4 => 9
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x7117cf4a63a897bc5f7f421847aa167e334e2d52
  | 4, 0 => 0xd720d04673db20f16dec060c6c0b6b1363a897bc526908a14eef4879280ec0e32662c0f0
  | 5, 0 => 0x63a897bc
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc000000cc000000cc00000000000000c0000000c0000000aa000000aa000000a0000000a0000000550000005500000033000000330000000f0000000f00
  | 0, 1 => 0xff000000cc000000ff000000aa000000ff00000000000000fc000000fc000000fc00000000000000fa000000fa000000f0000000f0000000ea000000ea00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xda734d9744b9744f9644d9874
  | 4, 0, 0 => 0xd974150d94140d7404d975450d9744d97425d97435dc9745ed9745
  | 5, 0, 0 => 0xd9744
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe000000361060c9eff138f
  | 0, 1 => 0xf8efe1f80c7ec00f71c70361
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x9bf98883476366089c64018b
  | 0, 1 => 0xffffebfc8ffffc8f77e74f77
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 16 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 16 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 16 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 16 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_11 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_11 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
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
  scr dom_11 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_11 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_11 roots_11 goal_11 6 := by
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

theorem low_11 : Lower dom_11 roots_11 goal_11 6 := S_11.noCircuit

def dom_12 : Nat := 0xffff0000ffff
def goal_12 : Nat := 0xece80000c8c8
def roots_12 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff00, 34, 42)] (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xff00ff00ff00ff00
def goal_13 : Nat := 0xfe00ec00fa00c800
def roots_13 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff000000, 9, 25)] (by decide +kernel) (by decide +kernel) low_11

def dom_14 : Nat := 0x5555000055550000
def goal_14 : Nat := 0x5440000050400000
def roots_14 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_15 : Nat := 0x5555555555555555
def goal_15 : Nat := 0x5440444050404040
def roots_15 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000055550000, 12, 28)] (by decide +kernel) (by decide +kernel) low_14

def dom_16 : Nat := 0xffff0000ffff0000
def goal_16 : Nat := 0xfeea0000faea0000
def roots_16 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa0000, 16, 17)] (by decide +kernel) (by decide +kernel) low_14

def dom_17 : Nat := 0xff000000ff
def goal_17 : Nat := 0xe8000000c8
def roots_17 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00000000, 5, 37)] (by decide +kernel) (by decide +kernel) low_4

def dom_18 : Nat := 0xff00ff00ff00ff
def goal_18 : Nat := 0xea00e800ea00c8
def roots_18 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff0000, 1, 17)] (by decide +kernel) (by decide +kernel) low_17

def dom_19 : Nat := 0x3333333333333333
def goal_19 : Nat := 0x3222202032220000
def roots_19 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def dom_20 : Nat := 0x3300330033003300
def goal_20 : Nat := 0x3200200032000000
def roots_20 : List Nat := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]

theorem low_20 : Lower dom_20 roots_20 goal_20 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14

def dom_21 : Nat := 0x3030303030303030
def goal_21 : Nat := 0x3020202030200000
def roots_21 : List Nat := [0x2020202020202020, 0x3000300030003000, 0x3030000030300000, 0x3030303000000000]

theorem low_21 : Lower dom_21 roots_21 goal_21 4 :=
  lower_iso [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9

def dom_22 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_22 : Nat := 0xf0e0e0e0f0e0c0c0
def roots_22 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

theorem low_22 : Lower dom_22 roots_22 goal_22 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c0, 4, 6)] (by decide +kernel) (by decide +kernel) low_21

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xea00c8
def roots_23 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

namespace S_23
def pairsG : List (Nat × Nat) := [(1, 3), (1, 17), (2, 3), (2, 6), (4, 6), (5, 7), (5, 21), (16, 17), (18, 19), (18, 22), (20, 21), (20, 22)]
def r1sG : List Nat := [1, 1, 2, 2, 4, 5, 5, 16, 18, 18, 20, 20]
def r2sG : List Nat := [3, 17, 3, 6, 6, 7, 21, 17, 19, 22, 21, 22]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_23.map (· &&& dom_23)
def goalM : Nat := goal_23 &&& dom_23
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x678b910d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000f000f00000000000cc00cc0000000000aa00aa
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_23 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_23 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_23 == dom_23) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_23 goalM u ys) : RunD dom_23 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_23 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_23 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_23 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_23 roots_23 goal_23 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_23 goal_23 := by
    have h0 : isConstB dom_23 goal_23 = false := by decide +kernel
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

end S_23

theorem low_23 : Lower dom_23 roots_23 goal_23 4 := S_23.noCircuit

def dom_24 : Nat := 0xffffffff
def goal_24 : Nat := 0xfaeac8c8
def roots_24 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

theorem low_24 : Lower dom_24 roots_24 goal_24 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00ff00, 20, 28)] (by decide +kernel) (by decide +kernel) low_23

def dom_25 : Nat := 0xf000f000f000f00
def goal_25 : Nat := 0xe000c000a000800
def roots_25 : List Nat := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]

theorem low_25 : Lower dom_25 roots_25 goal_25 4 :=
  lower_iso [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9

def dom_26 : Nat := 0xf0f0f0f0f0f0f0f
def goal_26 : Nat := 0xe0a0c080a0a0808
def roots_26 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_26 : Lower dom_26 roots_26 goal_26 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f00, 34, 42)] (by decide +kernel) (by decide +kernel) low_25

def dom_27 : Nat := 0x5500550055005500
def goal_27 : Nat := 0x5400440050004000
def roots_27 : List Nat := [0x4400440044004400, 0x5000500050005000, 0x5500000055000000, 0x5500550000000000]

theorem low_27 : Lower dom_27 roots_27 goal_27 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21

def dom_28 : Nat := 0xffffffffffffffff
def goal_28 : Nat := 0xfeeaece8faeac8c8
def roots_28 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_28
def pairsG : List (Nat × Nat) := [(1, 3), (1, 17), (2, 3), (2, 6), (4, 6), (5, 7), (5, 21), (5, 37), (9, 11), (9, 25), (10, 11), (10, 14), (10, 42), (12, 14), (12, 28), (13, 15), (13, 29), (13, 45), (16, 17), (18, 19), (18, 22), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 42), (41, 43), (41, 45), (41, 57), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 2, 4, 5, 5, 5, 9, 9, 10, 10, 10, 12, 12, 13, 13, 13, 16, 18, 18, 20, 20, 20, 24, 24, 26, 26, 26, 33, 33, 33, 34, 34, 34, 36, 36, 40, 41, 41, 41, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 17, 3, 6, 6, 7, 21, 37, 11, 25, 11, 14, 42, 14, 28, 15, 29, 45, 17, 19, 22, 21, 22, 28, 25, 28, 27, 30, 58, 35, 37, 49, 35, 38, 42, 37, 38, 42, 43, 45, 57, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_28.map (· &&& dom_28)
def goalM : Nat := goal_28 &&& dom_28
def NN : Nat → Nat
  | 3 => 1
  | 4 => 10
  | 5 => 49
  | 6 => 189
  | 7 => 161
  | 8 => 22
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe9ead890
  | 4, 0 => 0xd8e10b3aad05e1528a56899b870c0d98823aa16b31f8504a24813cf823edd32e18466c9c109f4731
  | 5, 0 => 0xfd77e23ff947282af6d9215cf0e569f4ebe1fcbce9ab8a6ee8e18a5ce5da962cd7a31273d51d4b96d39e183ad32372d8cc792574bd1fc97db4fbd2d5b10af83ca43f6bafa2eb00cc987a083793b9a0f987bebd61867ef8727a870eae79c63f0571a3faaf6f3682b0662a900463284fed5e2d8aab4f7c60744d71925d4bbe26724b35ab99486c9ce24241efef40a605d03c8891093a87d710335e65502e58b1fd28868de622a652761ed15b311ae2e85b15dac5e91550ae6f0ef750930577b41e0278f97d
  | 6, 0 => 0x503182d94f57ca794ee8cc0a4d9571e04d88424d4bccdda34b51d8934b193acf4abd1d0b498c6ad4484018904700cb0e45a7f59844ab1cba43acd9484021fadd3fe67d4f3e0fc03d3b754d64379218e335fe022a328e87082f9e6a3e2f2d39052ad9fd9b28b4339b2759c5772713cf0023fc45a2226c9111216dbf8b205e8f4c1e57ecb11dec18bf1d66c50e1c5e13f31b16f5ed1a1f1cf01a03096419ba301a1956d5731937d225171e641b1673385e15b3c68f14a03ebe13967e2f12b814901161181a11075aba10ed3da3107205040b29725509e9743d07db61e5074033b10696410f065a6a9803cde16603a1134a03939ebd02d6a72e023c136c01d18b1e
  | 6, 1 => 0xa9cce718a8f0d2eda8d42801a7853e24a2efe0c0a21b0ffea1ff43699ef7b1789d72dd149c767e099c4e70ec97a002259750c32596e4918295a465ac9544e3fa91a73dfd8e88272c8cfa91f689a86b2588a82a54882be4e184f92b6a848ab3228438f64283e3fad0834c2dc08320fd1b8220babb81de5f788069eaef7d304f3a797abaaa76a635e574f8ca7a74cf39e473105585730cc97a727253ef700050ab6f9599c06a44543e6a41599e68ef1665657e5bd6641d8976640f62e363aed3aa639b886c634e6b946309bc0f607f3e8c5fa001255f9ee40f5d71535d59254669571e9c4f56ba13a056488c3a55f9c36e539f4bae530e3d0850ae56f05097b9bd
  | 6, 2 => 0xfe4b532dfe3673f0fb2c7319fa5286dbf9cab482f770376ef6535463f6281cb5f5df82aef052953bf0509095eedd17f9edb06ad3ed86fa4eed2eb2a3eb93c63be3f2e69de316571de2f6af66e1c9d58be1151f08e111b6dbdff3a4ccdff2e4cfdfcffccdded5d017dcf44214dc2aec62d97fc822d46c5610d445852fd3d1aab8d1de8b17d028b587cf947cd6cc7593fecc1a159bcbd5b4f2cb5a385fc5bb2bd9c5432efec5368674c2a091e1c0e08b57c0d835bdbc84df1cbc545819bc172c05bbcf1011bb897c82ba8cbe19b99d8907b7dce78eb64676f4b533a702b4a8fae1b2750249aeeb5883aeeb3210ad5ae4ecaa5561f1
  | 7, 0 => 0x6a7ff66869c0add46733942563669d9563353df461aa33685d7bf2db5aa8a6b95a41fbd556403068556f0695523dc21151099cc6500139404fb2394c4e2ce2974dc27b5b4c1e35cd4b83a20b4b57c8ab4b0c2c39499b08ca49226c8f434ac032430588363d6d0b963c9d75a23c21f90f3a8b1a65387c221637da77da36c744ae366fa272360aefae359f67e73531374e339be83032ba82ac3264f1942f65d7a92cdef6d92c50f8382b81626d2a6cf07128a4a83e25fb67b223e92d12233e519823038dd42219ec0a2014c6441fb72b911f3d31db1ca0b1831c93f14f1bea3501123247970f79f41c0f02ba780e7dd0190de2aecb0d9cbe4306b07a0306291d83
  | 7, 1 => 0xcea2794cc9cc5372c8d8951dc33e8ebcc07ccfeebeb2f988bde1cfb5bc545819bc18011ab55b444cb3feb3cab37ef559b24f00d3b0e1dcffb07bc511ada32de2ace974c5a98e4816a8e78fc4a8d9852aa840633ca77ce252a4a02823a499e38aa494c22fa25e4bf1a1f098daa0662aee9db654639c48de239aec1f2b9a36658d996c23f49710a45896c2e368944ede00933451c191a946d59117715e8e7679718df2ab598d5eaaf98ce77a638a81f0ca89211e6a87d8b03e877910e2872610b8850f030e84d11e4d827639727dfd47397db173387ab2c9087a2bf43679e15a28749b9886745b5f6d73f60c3a729906d470946692706753916d483b2f6b6909ce
  | 7, 2 => 0xffcceadcff939cefff3df527fac274d4f96feb04f6e94291f6657479f5210d0ef109fd47f05e0f46f053c1fdefc2e112ec164c1eeabec0cde9b38944e97a801fe96d0b92e73f702ce606f433e45c7de4e21fca1de1283faae01309bcdf6d0221de7f8515dcd6712cda2d30a0d96359b3d7c2c847d629fd6ad3fa20bfd0dd3a20cf9551eb
  | 8, 0 => 0xd1efb8f3c2afde01b47be621a6563cc3a1f16def9b34b1218a7994f87f4590c97cea112d76f0de33705b5d9f5fbac6fd5cde0cce5a34cc425059633d34064f6c2efbd9641db3e4af1b78d4bc1561a43a0e7e151305169eb0
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33303330333033303030303ffffffff030303030303030300ff33ff00ff33ff00ff00ff00ff00ff00553377005533770000ffff0000ffff0000333300003333
  | 0, 1 => 0xf0f3f3f000000000f0f0f0f0f0f0f0f0f000f000f000f000c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a070707070707070705550555055505550505050505050505
  | 0, 2 => 0x1515151515151515150015001500150013131313131313131155115511551155113311331133113311111111ffffffff11111111111111110f0f3f3f0f0f3f3f
  | 0, 3 => 0x54545454545454545050505050505050444444444444444433333333333333333333222233332222333300003333000030303030303030302222222222222222
  | 0, 4 => 0xa8a8a8a8a8a8a8a8a5a5a5a5a5a5a5a5a0a0a0a0a0a0a0a099999999999999998f8f8f8f8f8f8f8f888888888888888855555555555555555500550055005500
  | 0, 5 => 0xc3c3c3c3c3c3c3c3c0c0c0c0c0c0c0c0afafafafafafafafafafafaf00000000ababababababababaaffaaffaaffaaffaaaaaaaaaaaaaaaaaa00aa00aa00aa00
  | 0, 6 => 0xecececec00000000eca0eca0eca0eca0eaeaeaeaeaeaeaeae0e0e0e0e0e0e0e0dcdcdcdcdcdcdcdccfcfcfcfcfcfcfcfcccccccccccccccccc00cc00cc00cc00
  | 0, 7 => 0xf000f000f000f000eeeeeeeeeeeeeeeeeeeeeeee00000000eecceecceecceecceeaaeeaaeeaaeeaaeeaaeeaa00000000ee00ee00ee00ee00ecececececececec
  | 0, 8 => 0xfaaaeaaafaaaeaaafaaac888faaac888fa00fa00fa00fa00f8f8f8f8f8f8f8f8f0f0f0f0f0f0f0f0f0f0c0c0f0f0c0c0f0f0a0a0f0f0a0a0f0a0c080f0a0c080
  | 0, 9 => 0xfca8fca8fca8fca8fca8fca800000000fc00fc00fc00fc00fafafafafafafafafafac8c8fafac8c8fafa0000fafa0000faf0faf0faf0faf0faaafaaafaaafaaa
  | 0, 10 => 0xfe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcfcfc00000000fcfcececfcfcececfcfca8a8fcfca8a8fcf0fcf0fcf0fcf0fcf0fcf000000000fcccfcccfcccfccc
  | 0, 11 => 0xff000f00ff000f00fefefefefefefefefefefefef0f0f0f0fefefefeaaaaaaaafefefefe00000000feeefeeefeeefeeefeaafeaafeaafeaafeaafeaa00000000
  | 0, 12 => 0xfffafcf800000000fff0fcf0fff0fcf0fff0fcf000000000ffccccccffccccccffaaffaaffaaffaaffaacc88ffaacc88ff00ff00ff00ff00ff00cc00ff00cc00
  | 0, 13 => 0xffffcc00ffffcc00ffffc0c0ffffc0c0ffffaaaaffffaaaaffff8888ffff8888ffff0f0fffff0f0fffff0c0cffff0c0cffff0000ffff0000fffafcf8fffafcf8
  | 0, 14 => 0xffffffff00000000fffffcfcffff0000fffff0f0fffff0f0ffffeaeaffffeaeaffffccccffffcccc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc32deb44
  | 4, 0, 0 => 0x33e286c54af4e135a295c32e1be7abd34d95c9d7a70aed14af4d1018a95e9865be68bd314786c57a618d0df2f0c331eb45
  | 5, 0, 0 => 0xd386ab15279b4cf9d0d8a96e9a66b462a5ba70c359a296e98634362a58074c4c548e5d38e6437ac5b4d9b10d8a96e9c2bc37ca58074d3858a65d38eacc62a5ba69aed18a96e9c30c886f9ba6287018a96e9a314362a5ba69b3597296
  | 5, 0, 1 => 0xe9a6cc3629dba6286c54826e186ac37ca5807486c54825e9c30da86a5b86186c56296e19704362a58074d3857a95e1861bd68a5ba70c379a296d38edc362a58074d3861a45e9a70c37c91ba709b0df296d3866386ec5ba70c331f346
  | 5, 0, 2 => 0xe9c2cc362a5ba69acb94a06e1861b1523dba6286c548e6e9a67cc62a5ba6986d58a06e186dc37ca5ba6986d58966d366ac362a58074c32e1be5d3567c362a5b861ab098a96e182ac362a5b4e1ab098a96e1866437cf5b4e198f5a316
  | 5, 0, 3 => 0x3a699ab94a76
  | 6, 0, 0 => 0x1a70c37cf51300d38eac362a58070c30deb152c03a69ad35729601d34e198e18b00e9a66b15239ba70c70d8a91ce03a709b0d8a96e9c30de86f94bf4e182b4362a5c074d30d4a038c03a69c6c508e601d383152381b69c30deb462a5f86186f9eb152e034e1ab0d8a16
  | 6, 0, 1 => 0xe9a6cd686c54bf4d30d8ae5281c074d3361a938dd34d69f0d8a97e9a70d386c54bf4d386d4362a5fa70c30df2922e03a6952707036e9a66c362a53b8001d314362a54074d38e1a138c030c37ac54816e9c30d684c54b80e9c30d086a58069c2f58a91cdd34d686c54a07
  | 6, 0, 2 => 0x1a70d598c54b00e9bf0b15239ba69c30d8a912fd3861910d8a97d386b437ac54b80e9a70b152298074e10df2906c03a69c3597216e9a70c362ad4b80e9c30c35245b4e1ab0df3152e034e186f549c6e9a66c362a50b80e90d8a90601b4e1b9561b152fd386186fdf297
  | 6, 0, 3 => 0x1a70d562a47300e9c31b15239ba70c9821b152fa71d6ab0d8a9701c30d586c54b74e1861be72a5fa69c3521b152fd386186c56a97e9a70c362a49b80e98549c3439ba699b0d8a94ae03a6199298a5601d30b142380b69c3321be7ac5f869c3561b152e03a70c2c508e6
  | 6, 0, 4 => 0xe9c30c368c54b80e9c21b152118069c30d8ac52dd38e9c30dab17d386f437ac54be9c3561b1529dc074d9858a91cc03a618684e01601c30c37cf54b00d386b555ca58074d38509c1cdd34e198d18a9701d38618684e300c3561b15205ba70cd821b152e03a6986c55216
  | 6, 0, 5 => 0xd386dc37cc54b80e9ab0b15239ba69c30d8a90ee03a69c2f910e6e9c30c37ca473e9c30deb15245c074c30dab102da70dd86f58a9701d34e16ac47369c3561b15285c074d38662538dd34e3990df31701d34e352707374d38eb4c62a5fa69c30df3444e034e1ab0d49c6
  | 6, 0, 6 => 0xe9a70d662a4f3e9c3561b15295fa69c3597294efd34e186d58a1701a61bd62a41b00d386dc362a5ba69c10d8a91cfd34e386c54887e7a70d586c54bf4d38ef4362a5c069c30dbb152c03a69c30d8976e9a70c362a4dbf4e1861b15241c074c35972902c034e162b148e6
  | 6, 0, 7 => 0xe9c30c37cd14bf4d3864437cc5fa6986c54a01ce03a6152707016e9a70cc8ac52b80e9a6fb152398074e18549c1cc03a6962a948e601d34e162a51b74e1821b15239c074e10d8aa52dd34e1acb94a17e9a71c362a48b80d3861ba62a58069c3461b152db74e1ab0d8a97
  | 6, 0, 8 => 0x1d376162a47374d3861b15245c074d2c50a01cda70cc86f58a9701d34cd86c50b00e9c30be52398074d38592918c03a6962847036e9a6bc37cc54b80e9c21b1420dba6dd3861b562e03a6986a949c6e9a61b15280e3f4d3861b362a5c074c2c548e00da70c370dd8a97
  | 6, 0, 9 => 0x1a71c37ac54b74d3861be4445fa70c30d8a922fa70c376e98a97e9a70d668c54b80e9a61a140718074d3818a91cda70c37ac548e701d34cc62941b00e9a61a1380db4e386f9eb152e034d586c5483601a70c37ac50b74dba70d65ca5fa69c30d8a92ae03a6186a4e006
  | 6, 0, 10 => 0x1d34e198d18b74d38e1b15215fa69c30d8a92ee03a70c0c548e601a6acd86c54b00e9a70c344458074d3661b152c03a69c2c52886e9a66c37cc54bf4d3861b662a5c074d3821a938c03a699f0d8a96e9a70cc7cd18bf4e186b437ca5c069c30d8a90cdd34e186c54947
  | 6, 0, 11 => 0x1d34e186d58977e9a70d684c54b80e9861a138698074e1866437cdd34e1bcd18a9701d386086a4e300e9a70ae5215ba69c30d8a93ee03a61970d8a9601d34e162b45b00e9a58a94039ba69c15a1b152e034e186c54926
  | 7, 0, 0 => 0xe9c34e186c548e801d30cc86c5481701d34e1910d8a9701d34e1890d8a9701d34e198c548e701d34e186c98a9701d3861990d8a9701d34e1ad0d729701d34e186c5485701d30cc950d8a9701d34e386f98a9701d34d686c5483701d3861c10d8a9701d34e186c549e7e9a70c37cc548e801d34c362a50837
  | 7, 0, 1 => 0x1d34e187058a9700034e1ab0d8a9601d34e162a4e0e70003a70c70d8a9601d34e186c56a9701d34e1990d49c701d30c362a470170003a6186a4e1a601d386186c548e701d34d69b0d8a970003a6186c5081601d34c362a528370003a69c2c508e60003a70c30d8a160003a6fc30d8a9601d34e1930d8a97
  | 7, 0, 2 => 0x1d34e162b548e701d34e186d18a9701d386186f98a970003a69c70d49c601d34e1ad0d8a17e9a70c362a508e801d34e162c148e70003a6cc30d8a9601d34e186a4e0e7e9a70c37cd18a980003a69c3318a560003a69c30d09c601d34e162a470b701d30c362a4e0170003a69c6c548e601d34e164c548e7
  | 7, 0, 3 => 0x1d3869c2c548e701d34e186e18a970003a69c3118a960003a69c3597296e9a70c362c14a1801d34e186f949c701d34e162a470c70003a69c30df22601d34e3ad0d8a9701d34e186c572170003a69c30dab1601d34e186c509d701d30c37cc5481701d34e186f18a97e9a70c362a509c801d34e17cc548e7
  | 7, 0, 4 => 0xe9a70cc86fd8a980003a6986c5529601d34e1a50d8a9701d3869c30d49c701d34e186ed8a97e9b74e186c549c801d34e187098a970003a6162a47016e9b74e186c548e80003a70c2c548e6e9a70c362a529c801a70d6ab0d8a97e9a70d686f98a98e9a70d69b0d8a9801d34e186c54997e9a70cc8b0d8a98
  | 7, 0, 5 => 0x1d34e1acc548e701d34e162a510e701d3861ad0d8a9701d34cc86c548370003a6186c5480601d386187098a9701d34e162a508e701d34e186fd8a1701d34e1990df3170003a6186a4e016e9c34e1ad0d8a980003a69c2a4e0e601d34e1ad318a970003a70c30d49c6e9a70c362c14a58e9a70c362a540e8
  | 7, 0, 6 => 0x1d34e1ad0d49c701d34e186c5488701d34e1bd0d8a97e9a70d686c54a7801d34e1a10d8a9701d30c362b9481701d34e162b948e701d34c362a4703701d34e186a509c70003a6ec30d8a960003a6986c50a060003a70c30df2960003a6986c5083601d30d686c5481701d34e186a4e197e9a70de86f98a98
  | 7, 0, 7 => 0x1d34e162a540e70003a70c10d8a9601d34e186a529c701d34c37cc5483701d3969c2c548e7e9a70c362b94a1801d34e186d58a9701d34e186c5491701d36e9c2c548e701d34e162a528e7e9a70c37ef98a98e9a70d686c54a180003a69c10d8a9601d34e186a4e18701d35e9c2c548e7e9a70c37cc54918
  | 7, 0, 8 => 0x1d34e186c509c701d34e186c50a0701d34e162a470d701d34e186a541c701d34e186c508e701d34e3990d8a97e9a70c37ce58a98e9b74e1ad0d8a9801d34e17ec548e701d386186fd8a9701d34e186c509e7e9a70d686c54a580003a6986c54a0601d3969c30d49c701d34e1990d8a1701d36e9c30d49c7
  | 7, 0, 9 => 0x3a6986a4e036e9a70d686fd8a9801d34e186c5821700034e186f58a96e9a70c37ec54a18e9a70cc86f98a9801d34e1990d8a57e9a70d686c54a8801d34e386c548e701d34e186fd49c70003a699b0d8a960003a6962a4703601a70c37cf58a97e9b74e186c572980003a69c70d8a160003a7086c54836
  | 7, 0, 10 => 0x1d34e186f98a17
  | 8, 0, 0 => 0xe9a70c362b94bf4d386b4362a5fa69c30d8a944fd34e186c54a1701d34e186a4e300e9861b152058074d3858a91cc03a70c30d8a96e9c34e186c54bf4d3861be62a5fa69c30d8b052e03a69c70d8a96e9a70c362a4e3f4d3861b15239c074d3861b142dd34e1990d8a97
  | 8, 0, 1 => 0x74d30d8a906dd34e186fd8a97e9a70c362a543f4e5a70c362a5fa6dd3861b152fd34e186c54a57
  | 9, 0, 0 => 0x3a69c30d8a96
  | _, _, _ => 0
def stateW : Nat → Nat
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
  | 0, 0 => 0xfc47e38f900fcf811e0ffffffffe047838c100c0c7ffffe0ffe3ff1fc07f83f003fc7ffffe0ffe3ff003fff800ffffc00ff8e003e3f3
  | 0, 1 => 0xe3ffff800000038f1e7ff1c1f0fe007807c007c000e0071c181c0c00070380000c0f8f1e7ff1c1f0fffc0fc7ff070738f0271f1c1c0c
  | 0, 2 => 0xfff8fc7ff1f07380e201f007c00fc7fe38f918c4fffe3f03fc601cfc78e38f9183cff1e381ffffffffc78e00f9180438ffffff1fffff
  | 0, 3 => 0x1fb87c73e1f07070e1800e0601003801c70607033f1ff8e3e7e3f3fc47038f9e0f8ff100003e400001c3860038f83c0001c0e00383e3
  | 0, 4 => 0xe03838f0271f1f9cec000000000e0383f1e3803e46010e3c79ffc707c3c0000000000000fff8fc7ff1f07380e201f007c00
  | 0, 5 => 0xe047838c100c0c0000000000000e3c79ffc7e7fbf8f1e7e0000000e047838c1e0f8c7f1dfe0ff83ff000703800e0f8c001c000038300
  | 0, 6 => 0x3801c00000000000001c039ce0000703800e0f8c00000000380e01fb87c73e1f0738f1e7ff1c1f0f03801c70607030000001c001c00
  | 0, 7 => 0x3800000f80000e1c7fc1b9fef03871f800000000e1c71c1b9f0c000703f00e7f8c001c0e0000000000700700e7c000e0071c1b9cec
  | 0, 8 => 0x703800e0f8c0000000000000003f00000f8c0070e1800e3e0f01c3860038f83c07000000e000001c0000038e03800000000000000
  | 0, 9 => 0x3800700ff38000e0000000000003800700ff00070fd8e0e3e3f31c0000038000007000000e000001c3f60038f8fc000fc0e003e3e3
  | 0, 10 => 0x3f00700ffc007ee1f1cfbfcfc1fb87c000000007e0071cfb9cec1f800073ee038070e181ce3fcf01c3860000000000ee071c1bfc0c
  | 0, 11 => 0xe007807c007c007efdffcfbffff1fbf7f838f83c07efdfe00383e31fbf7f800000000efc7fc1bffef003f03f00fff8c00fc0e0000000
  | 0, 12 => 0xfc386000000003f0e181fe3fcf0fc3860000000038e0071f181c0ce03f83fc0fff8f800001f001c00e03f807c0ffc03800001f001c00
  | 0, 13 => 0xffc0007ff07003ff0001ffc0000ffc703fffe0f8fff0001ffc0000ffc79ffff07c3fff0071ffc1c0cffc0007ff00003f0e181fe3fcf0
  | 0, 14 => 0x3fffffe0000000fff87c7ff00003ffe181fffe0f0ffc703fffe0f8fff0071ffc1c0c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x24442304900b08811008ffdef7f204402041008083729be07e00ff0dc06f81f003fc2429a40520098001bfd800af6f40028840020080
  | 0, 1 => 0x62cfb7c00842018b165b50c170762059054005c010a0653408150520c50694301c1d89124910412024b00d8414040610802410001000
  | 0, 2 => 0xd220904a0140034882412805000b064020e11080a6481202d040189460230a91030a408000ffdef7f9020000a0100018b3edf50e1787
  | 0, 3 => 0xdb30d86b41e06264c120ad068184b10d86140e062d1b88c3a742c2b46e230e9d0b0ad190083a54242942a210a8d030091388c12702c2
  | 0, 4 => 0x48b2590ae1795182ac502390e0040a21008e0382428412688c52562c596d4325c9c0204124088525db30d86b41e06348c241a807800
  | 0, 5 => 0x29544a2552a8e8244120850a83866cfb7d4be5f9d9b3edf002108024cf2794be1f9cb73dbe57f87ff24cf2794be1f9c803c005038700
  | 0, 6 => 0x4f9bfdc0084201186ec5c23bde02ddf6fb5febffc3469a4873a8f8dbb1dcfb63f4f5af577bd5cbf3f4b91dcf162f4f5084641c00bd00
  | 0, 7 => 0x903a002a0fa001bf7fffd7fbfff6fdfffc0084201ae7f73d5bbf3d66dfb7f4beff9d9b7edf0021080621f90740efc013e6ff7c7bbdfd
  | 0, 8 => 0xb4ff27bebfbf9ed3d41afadef67b03f003e0fbc0276edb6efbedfd9d3a692bcfa3e274c120af1e8789d2a212bcf038250c000aa1e860
  | 0, 9 => 0xd6bbb5faaff7975aeed70021080d23b907a0ff402f7fdbefffefffbdf54ebff7bdfef79008ffd4242bd3f693fcfbfe2d3fc9efafefe7
  | 0, 10 => 0xf23f907e0ffc037eeff7efbfdfddfbbfdc00842037eeff7efbfdfddfab25fbef17977cefe5ef3fdf8df3bf9400842036eef73edbfd3d
  | 0, 11 => 0xf225907e055c03fffffffffffffffffffebcfe3e3ffffff52f97e7ffffffc0084203ffffffffffffff6ffb7febfff9fdbfedf0021080
  | 0, 12 => 0xffffffc0084203fcffe5ff3fff8ff3ff940084203eed773fd9ff3df6ffb7febfff9fdbd65bfadff67f23f907e0ffc03c8d641f81ff00
  | 0, 13 => 0xfff5927ff7fd0bffd129ffdea7affef27ffff1f9fff941bffdc767ffe596fff55d1fff965bffd5747ffe4027ff5090bfffffffffffff
  | 0, 14 => 0x3ffffff0021080fffffffffd4b0bfff9adfffeafaffff6fffffbfffffd77bffdff7f
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 54 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 54 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 117 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 117 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 117 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 117 then wireAt i else 0
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
  | 4 => 21
  | 5 => 270
  | 6 => 1360
  | 7 => 934
  | 8 => 23
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xf48e037ed0f023b7c3f10999b81e01f4b7447fa4b600eaa1b04608e39f3d2c7f85695d0e7bba4765788753785ee74231581e03de57e43a5050d2073c45d961d13522657a31a25f6e2662fcbb1937d225111c590d
  | 5, 0 => 0x434ac03242b779a3422fff313e06271b3e001cf73c9d75a23c738da03c142ecb3c10e15a38e1164636ee485c360aefae35e7ff7635dd329c35d0cfb83531374e34af1430331c6f02321b075b31b67eac30869263306b71a12ff0ebad2fc512132f72e55f2d8de92d2d6659a02b2a76162a37b71f28de6ab92884ad59283b82912510721523e92d12232991f622f58cdf22a6c4f4217c18ce216ecbfb206d0bcf1ef254801a1f0ef616b53d7315a06f65158cc7c1143efb9411f45ea90c2777f60b2972550a86a7ee096b5da908ea0cab088521e20876323407b40e28056e530705044ced0420c92303d3407003c57b0f0350bba401c1f3ad0107a890007f20bf
  | 5, 1 => 0x7ae3f0347a7a23a879ea026877894dd776b9c58c759e4ed874d23440739e0a067254db06722fefdf71e0fc8e71b509a3715bd4c270a0d0b87018d7526f0faba46f0e80b66e5a6e856dcd99b36dade4d26cec59346cb5042c69ea0e0b6971a092696c1f2a674200186733942563669d956309bc0f6187562f60f9ed7a5f6930d15e4898cc5c7fa2ba5aa8a6b95a870a305944bef95881c1695763cfee575b8245571e9c4f571d42735698e9ed55c5e94b556f069554a29b1153e3c9e2536a69af5318541d5021995a4f5a105b4f0d9c4b4ea790e04e29c7d14dfc1cc44d7136b54cf6e4114c83099a4a49d2bb490aeca946dbb6214551190a45224d97449d9d2c
  | 5, 2 => 0xb660e5eeb41e3bf8b31db7e0b24f00d3b12ef38faf3fa94fae61e421ae4b4cd0ad91e1dbad21b84bacce9982abd19988aab48070a7aac782a67b5273a5a6ed24a5a276dea5740e56a3e4d7e9a39b8aa7a25e4bf1a22de227a132d739a0f84ac3a0662aeea01d11f79fa937809f7ff34d9dfdf3cd9d4ea11f9acf07e39ac9805f9a56da71998edc0d9708ff3f95fd3d4795d922c09534777492b46846915532a690a397f8904657ca8e37182b8e3146dc8df6105d8d92204d8d27bb618cf11b068c5d62638a356d0987f47cd385ac70918437c5ee834c2dc0815c694d8084c4d38025d7d17ec375137ebb8f577ea2f5447e5d06957d8ecad87c74a1057bb0128c
  | 5, 3 => 0xef4bbd22eda9ea11eda75009ecf1e4beec5d8326ebe9a8afebbe285ceb71878aea7b7764ea2ce685e9a8dd11e984c3b8e8cfd2eae8b09d91e80052f0e5e9f10ce4fe6d95e1c9d58be14001d4dfeef4bedfd537a6dfcffccdddd3ac13ddcddbe3dd5e2a62dce8ce41dcb55942dc61d225db96f732d979864fd8425515d8102e57d629fd6ad6208956d54ef1e7d2fe24c5d2c69a87d1941c87d1866eb1d0e3e7a7d0dbedbad0159333cbf54aa1cb440644c9cc5372c97d7375c905a361c8f00434c8c289f8c883655ac7daa015c73fff91c6b6237fc66cc2fac54940fac4f7a12bc4eb8581c3f10999c1aba62dbf27e071bc4d6018bbd6fe92babf99f4b6a3faee
  | 5, 4 => 0xfa93a9bcfa5343b2f9e10570f96feb04f8fa4516f7ea4fbaf74d4f6cf4503936f355e703f1f92d3ef1275cb5f0f8df95efc2e112ef9ca9ca
  | 6, 0 => 0xbe712130ba8521d0b8ad6cc0b2e0ec30b2c8ce60b28f6400acc38510ac4d5b90a7677f50a6361fa0a6242b50a120bf109a34f3a097689a809598a57093e7356092a933f09199978090dfc8408b51a4508a530c6072d6b3a0711d49e067dcd790665520c0644c923060f596e05fd0f1105f9f75e05f2ecc205d4ab0b05a9e53f05a123ff059b7ef70585bda2053cd7d1052f642505169eb004bca6590496704c0460bf6903feeafc0386689c03816c48037f6899035eb4ec031da4f702eac56702cbd8f102b0604d029bda2f029aef9e0235e8030219fdf801d78abd01c1f3ad0198403d01866a360140ce05012a584000f91aa800f7d2be005528aa00296567
  | 6, 1 => 0x16fc4e1d16dbf17016995adb164f38e01644fce815f4eac915edc3f31561a43a15602014155ed0bb1540f2be153802db1422b86f13ea83c213e0e2a7139302bf138cad0013728f561368b3e213346ed1132af56d130a5a89129b996a123792d3122a976c11fd2b1311b4bd5b119a9377118eca21118e6ec71188f51f1187183a116c0d7e1142fa4111408e9a112a239910d505b6108ef5b9106dc28b105c94f4102d8cd3101fadf4101f34a20ffdb21e0fec104b0fa2a5570f9550a90f8e38f60f616dc10f47a0390f3dab0c0f115ba20ecc4ac70e98533c0e82ba2b0e7e15130df292670db432850d9cbe430d6e8d170cc62e6c0c9e5fad0c97cf590c54bdb6
  | 6, 2 => 0x258b474b25471fea251a10e22517e4d62503fe79242930a923fa873323aa74da237d543d2256b04f224f4f6f22498af021d8db4721bde807219634db2185333a2167b830215e4c9820e249a720d561792064873a205b0a2a1fa46e431f7f06c31f59336e1f3387171e51cabc1e472b3e1e3bd1161dbe4d991db3e4af1d826c881d75a3ee1d4df85b1d4370751d07cbc61ca0b1831c96ea491c0c1b4b1be886d81b78d4bc1b41c6861b3c1cc21a87fcc01a7bac721a4058c31a25944819d9673c18e16a7f18ac994f18838b6f1882b169185955ec18103f8817f48eca17ce2ba217bcd81e17b77a521799e0ae175a929b172938d71712096e1710ef8e17016561
  | 6, 3 => 0x2f8f1ff32f81a0e12f8141142f65d7a92f48cad42f37b6b72f2288ef2efbd9642ed7e53a2ea734e82ea1c1f32e3061ae2df741622dec4b6b2de6358a2da94f942d8366eb2d618f3b2d52d1502d06d0c22cf8cd042ce3b7132cdef6d92c5afc882c50f8382c2026e82b27b74c2b15732c2afda44c2af68de12a95810c2a6c61542a2bb0422a121f8d2a00355d29f5789c29e11e8129c478db29af9a3629af2b642992b932296669a22934275729025cbe28f27e9628e1d56328d3f68428bda13e2819312c28173a1b27e4c340275958f22750b4f6272cb276271aa0d927087cfe26d9bbbf26bad6df26800d172655fd6426548cc42601675125c5c2a22592fc45
  | 6, 4 => 0x38695c3f384a988a380d7bfe3808c78237e1d9d937d8b58137a858a737a6817a3784fc67376b796b37347e3036cb597836b5383e36a8e1d936648703363ae820362c85d93610c82c35fb583d35bf14c335a69de235a511c5356512d03563f1b635239d6d3505b6fb34e9a81a34d88abb34d2fbb7349eef89349995fb3492603134886bc3347c735e343eb057341e042234064f6c33fffa6733d93c6b33a2828e339be83033864f1f336e091f336787a0335d819532fa2f9532f6275b32ecdd7e32e38d4f32e16b8932aa2b2b32a808193241f60e32054f5f31f21e3331a2e6e731968b41318b16ac31752de7312ae6df30d52820306b71a1303166692fbf3527
  | 6, 5 => 0x466dcded462000d245ec8224459774c2456daacd455606a14526b40844e5077444bd18e044ae84d94434e7ba43ce4ad743c469ce43555fb0430222fd42fbf37742ef746f42dfcdcd42b779a3422fff3141ec4f6f41e9b3f341b3665641a587774170bcbe41320659412c1b3840936de1404b30133ff4ef3e3f6215df3f4880b43f227ddf3ebac68e3e896cb83e6c73253e69a4d83e6308a13e38dfb93d6831243d44b5c43d2c7c353d2562093cf092fa3c914bb53c346cd83c08bd653c0236123bd6ad1d3ba5ac113b90bff03b4c94c13abba4373a822ece3a4fc20639ddbebc39c8c08a394f142039310451390dd70d390153ab38eec90038c86292389a23f9
  | 6, 6 => 0x524e709e522c1d2d51ed493f51ed228251be6a16518d110e5160844351501bab5142fdf25122fc1950ef354250eca9cc50df0cf1506e67a45059633d5033fc2a5021995a4fc559f74fbec2eb4f9d1e774f7141a24f08f8de4efcd55e4e6a26fd4e475deb4df72faa4decf5114dc9c7c04dc7b19a4daeee454d84259f4d700a604d55ed494d520bf74d43334a4d356aa64c55dd5a4c1e35cd4c1258884bd118f54ba1260e4b81ba084b568f0a4b11aa524aeb5bbe4a4249ab4a3f5f3c4a30f9fb49eb066449e3bfbd49c4b7d0497253c14932d4034844a63b4834edba47dddb3347d7f35a477d4b384747d9104734005046f1b31146df279b46bddc5e46792c03
  | 6, 7 => 0x5f5545f95f4ce3e85f4c3dc55efaed315ed6a3f15ed5c2bf5e5e95475e1bc49c5e13ada65dc382f45dc1657c5da6006b5d8bf1475d7d6e2d5d72a47e5d0eae245cf74d185cde0cce5cc8dfb35cbe4b0e5c8ec69d5c59fd6d5bdd230c5b3bed485ad2b24f5a3f2b2b5a34cc4259a0c2fc58adde4458a9df50588269ee582969ea582291a25808a35357c2ae19578012d0576611cb574905b6562261c85618ad1555f2f733556f0695554bcaab55407ef25530a86c55285f42551db61354f251df54ddc53454b5735e54a96c095488605d5459014c541ac84154140d7753ee2a9c537f88b15377f3e6536b8d0a536a15075361a432534afad3533b7ec152cda0dc
  | 6, 8 => 0x6ca5b1e16c4b6e046c2cc65e6c14b3b56bab48676b9d976b6b906e176b3457826ae97d196acd37c86a95be0b6a610cd96a4af37b6a08bb056a08291469e3640069c0add469a1d56c696a9bde68ade5456896eaea685b160567e0419367c13f6967852479677e8bdf6741623a67339425671ea51e66be8369669a48866692ef6e65f7743965f079d164bd70fe64b2bd456472b701644d72e66446662a63c9dda363a6a9d363939f336390794c6310f02f62d51b4a62c54ffb62a39a81625d86976243e4b462261eff621cd20f620a304261f63a0061ca400861874d90616fe8b4613f4bb660fbe7f960f47f6c60774438602a7853600139515fbac6fd5f593dd3
  | 6, 9 => 0x76f0de3376e1a5f076d6907276d063dd768e81ea766e04be764e5f61763744917626fba5761e2a877613d46a75ace69a7508aada750876887502d39f74fe289274d842da74d57dbf74ae25e07481ccfa7460b49d74601fa7740c193c7408724473b4c597739c3b75729906d4727718da7225f95871fa161671bf4e7471b731cf718d4b8571872cf5716e5da9716e006171519cf2713eb64d712881977110673d7108872f70fe4ee070eea42e70e1e95e70da3446709c003a705b5d9f70557dc0703d873870345b606fbb45706f7090bd6f6a8dfb6f63ced86f4ebd9a6f4c3cf56ebc2f256e30bccd6e24e7616dd08b0e6d8a62746d76e7956d483b2f6cec5934
  | 6, 10 => 0x829ec1d6827963fa825b350882348b3c81b76e8e819be999817106db813e007380da8171808528c4806266ad8028e977800ca9ce7fd8d7587f4590c97f24c13b7ed1cb467eb0e6c47eadd0e57e22428f7e1a8a567e159c437e0bc1687dd747b97dcd0b037d7d57bc7d5ab6fd7cf352a37cea112d7c7494757c69c65e7c6664907c4f2cf57bd2a6677bcac5857bb7929e7ba3c0797b91074f7b6ec17b7b6295fa7b1fa70a7ae3f0347ada8ab67abeb30b7a5b787a79e5550479d3e13a79c2eecc799a24ae79684f627951d578792b8cc879278607791c125478d13196786f2162783824f378298bb27800865577e0dac777abf413778424c27723c8d076fcecf6
  | 6, 11 => 0x8ec635f58ebf00228ea2abb28e965ddb8e94ccd38e6e30d28e3f8c778e0ae11d8dc3e5858dae6ecc8d88441d8d869bbd8d395ff68cc9faaf8cc6a3578caa8aaf8c9cabd08c73f3678c51c7138c4a4e318c2b787f8c1415108b2e35708b105bec8b0cdb878aa94ae58aa3b04f8a7994f88a2fd5d88a1f83f08a1659738a0b34fc89f0f1f389f074c389a54b3d897c1ede8905ec5388ede02888a4fc21884052b78703169686c118bf868f8bfa8679f841867726a1867254828660afd386465a8a85f7cea685d9e9f185ab65638527bd3a84d11e4d84c58dce849e475c845f90f7845ec2c68436e17f83ea69c583c8c0a3833df903833cce488312ea9182de7117
  | 6, 12 => 0x9be41d5a9bd6314a9bc7f7b09b6cf8b59b67bc649b6512559b34b1219aca79e39a2202919a0d459599f38c1199a9b2ce9948515b993adcce98e9771598de3ac198a19efa988922779882e2ec986d00ac985600c5983bee0497c0eda19795e40a977bd188976ba15e9736bddf96fd8353965531e695ad9990959bf1de9592eee29551aacc9542488b952ec5d794d7782194b8834e94a0b6d39498a31c93e2499393ad21ba9389b4aa93874bf5938473d69380b44293602c46933451c19322c34692cd311e928f624e91fd1dbb91e8ccbe91b3a6db91a946d5918b0169915bff58912821e490d2174890c7efe590c788869022657e8fa19e1f8f6057d08f4e886f
  | 6, 13 => 0xa7fc18f5a7cf5c2ca7b6a6e8a764c6eda748d152a6910249a6563cc3a611643ba60a91baa56ffdf8a55f2747a550f087a51dbb22a508355ea4d69db9a4b57e08a4428e5ba434b4b6a3e19170a3dbd99ba3c1ab4ba39dd69ca3744415a33588fda2cd8bc3a2a97873a296a4d8a28dae8ba284b47ea25e4bf1a251b83aa1f6e797a1f16defa1f098daa1d46ba7a19cd68fa1662bafa1521c33a13ad5c4a11662b6a0d63b5ba0d317c1a09e7109a03c38c2a0369f44a02ef21b9f90b24e9f726bb59f500c479e9360949e8581b59e5fc6b79e3e6b5e9e3e2dc49e17dae59dce524d9daae7359d6fd84f9d42c3eb9d3121ea9d1aee1b9cd8b9f79c3b05cf9c068d93
  | 6, 14 => 0xb6503f9ab610b333b603540cb602d454b55d5f38b5299bacb50f2cb0b4bad623b47be621b4520808b3f19d82b3b33ed5b36d3a2db34ae530b3216c62b2a6c045b285abbdb2794cefb222061fb1e5ddb4b1ce22c6b164d65db161fc5db0a1a8ebb08b6c2bb000358bafaab267af73942eaf69db5aaf647c31af616e2baf3465dfaef5af7aaee39321aec6eb2eae28502fae11518cadec3e13addfe763add28485ad965e55ad6e83e8ad58a5d0ad4e97cfacd06164acbf9b2aacb74da7aca9b064ab676f4fab225dd6aa9c1556aa9545c7aa77752aaa11ec3faa00aaa3a9f3d131a98e4816a9661f5da94093e3a909e4c1a8e78fc4a89d24c4a893383aa81e07a4
  | 6, 15 => 0xc152b13fc10b9ab5c0d8bcdac0873760c06b50cbc064e263c0144dd9bff0ea6dbfbdb5dbbfb4dd66bfb0cba3bf83682fbf78f153bf3daf06bf23def2bef3e634beea5a39becf96e5bec0a575bead23ffbe9e16f9be9d9d93be584277be4e61b0be4769d9be0e54e8be0cd55bbdeb6445bde1cfb5bdbc7deebd9d4a99bd8eb6dabd5509f0bccd4b3fbcb61da3bc95da00bc8d9161bc7e8f37bc6114c2bc0bf607bbedd967bbe3d513bb8f7c21bb75fc4ebb6820b3bb1b293bbab9a1bdbaa8c339ba85faa9ba701036ba2e1869b9cf0ad9b9937c3db96deb79b93206deb91d4ce9b90dc9b5b8b7e9f7b893b555b8767b00b83ea7bbb7ae1533b7784d34b7083ace
  | 6, 16 => 0xd027ba97d01d781ad017a121d0022fedcf524e2dcf1f3ed4cf000eafcef3ff30ce597d4ccdf98342cde202f0cdba2e84cda6e723cd8c6716cd888f1dcd13336dccbe85adcc452051cc389808cbb9f257cb7ec15ccb2d3d5ccad25745ca35eab9c9cc5372c9adbb05c996b3b6c9760326c8f59c70c8843c2bc842caacc7fdd353c7fb6ba2c778d333c7554d2ec7337313c70560b5c6bc9380c66d8871c65b521ac63e6ab8c5ae265bc576e528c5736c6ac53c59cec4f7a12bc4949487c469c87ec434f8fec3ad09c1c3432490c337f1aac3334588c30d6fe3c2c56a8ec2afde01c2a3c062c275dc23c26e5d2bc26d0ba9c2607e4cc22701b7c1fa1783c1711256
  | 6, 17 => 0xda211301d9d2c684d9ad9916d979864fd9719f58d965b06dd94ad137d909f889d8f800a3d8d003ded8c89669d87f9952d872797ad85d0165d7daa581d79dcf25d7970f9bd783df75d7783301d76d9a26d7168563d6da34e8d6a5bda7d697b081d68e0ee1d62a769ed629fd6ad6208956d612c66fd5f531afd5ce88c2d5c938eed5676af3d563257bd55f2254d52b0a13d4bcd597d49f8f7ed46d133fd3fd10acd3d2caa2d3ceaa59d3b6fe4ed3a84f1fd3980975d34d4128d342c3fbd3152e0bd2eb9853d29440d5d282ff82d2370a95d231461dd20d1552d2034d48d1efb8f3d1c3301ed1879d90d17bf5cfd130dacfd1296545d0f15981d0a5ce8bd0613484
  | 6, 18 => 0xe54d2d9be52dadd6e504ee61e4ff088ae4a745e5e485a5e1e3e18a9be3d4053ee3cbe704e35f01f3e33cbff7e33cbb01e31a7a5ae30962e5e2fedb89e280ec37e247b55ee1b33d58e195a639e18ace26e116cfc0e0d18bdae0c288e2e0930e9de0800c8de05cc12ee04e0661dffebf9ddfbea839df75e0f9df66edf2df5144dadf50f4a6df33a8e5df1659addeec6317ded29fcddeb0d9bade90f3a7de60f740de312a05ddfb04cdddc15ca4ddaa279ddcbe562adcaf7ec7dc90e37bdc530e5fdc374bc4dc0740d3dbf961f4dbe6b227dbc93ba1dbc7af05dba78fe2db922ce1db76ec15db4f33a9db3a90b6db092744daa85144daa10b17da98c278da834ec6
  | 6, 19 => 0xf16a2142f163fbd7f0f8df95f0e8b557f0771dd6f0661805f05e0f46f0557068f0479b38f03d9387f00fa0ceefff90aaefc2e112efb0189befafc882ef885172ef330f7ceec40f0ceebe9aeaeea98865ee5bfb02ee1e2c58eda75009ed899b23ed50c2e9ed215bcfecc2422fec89cef0ec81985dec6b46deec0c1396ebefca4beb6724bbeb121e74eafba6c3eabec0cdeab31e8aea9496edea765f28ea206746e9e0e609e9807fbee9674be0e951e1bfe95148f7e8df19d7e8ae2d6ee899294fe8529c71e8284643e8047120e7a84916e7a6205be72bf883e7079a07e6962fbee68ed5dbe6886563e67d614ee65393cae648521fe5e14f13e5b44ac5e5a002ac
  | 6, 20 => 0xfcd91be7fcaa882bfc97bf31fc86bf18fc6afe7dfb60f246fb2599e7fb113150fadb836ffad8dc57fab3969dfaab44fcfa4fd28dfa111c28f9b8c4f3f9afb2a4f9414bd9f8e3626cf8d76ce5f8d5ce41f87a4a6af86a14bbf85b44fef81e117ff80e59ccf7f9dae8f7f886edf7a45692f79d1c8ff7905c5bf755edc8f73bfad8f737c7bbf6e6a00df6e44091f6d3c780f69357a9f6753fc8f66bd375f62e2c59f5e77c9bf5e5463cf58f108cf53cc3cff5277aadf5192827f47fc6bef4723ae7f3ef218bf3dd72f6f32d4ac4f318916ef2ff5c43f29edce5f279123cf256fda7f21af211f1ed8e22f1dcc683f1ad40a0f1a91aa5f19a275cf19580b8f1952b1b
  | 6, 21 => 0xff98826cff91be5cff84627aff7efb7eff24a7f5ff2325bafef6c3b6fee5981efee2c332fed1b51bfec6917efe4d0768fe3abca4fe05b802fd64caacfd633930
  | 7, 0 => 0x12b8884a12ae5da31234695d11eb7ccf11d748061187183a11752bf710d1aa96102d8cd30fc22fb60f8898390f5c5cfb0f3d84400f3badb20e8414b20dfb96ef0d9a92370d61f2fb0d4d98860cf91d9f0cea20e10cc7aa850cabde0a0c867e660c22507d0bb2ffb10b989d440b41c7720acf09dd0ab8b26f0ab7b9ae0ab0afbb0a9628be0a71f9560a6361fa0a029d7e09f8447009ee1b6f09ea659108d79a320878675807bd347d07af559e0754ea15065223ce064612c705c61dd605a3eb0a059e8b170590310f040745c603e36454036df1500296f5790291d00a024a740d01c1f3ad01a603fb0198251c0129b75500dd496a0086a50c0064991500273479
  | 7, 1 => 0x24cb7b29246554a62429651523afce9223a7fde62310763b2236825921e9d24d21a5f96820df43cc2081cc612064873a204aaf2d203e530f203cd04e20292edb1fd3d3851f3108e21ee4e3db1e739d441e1aa3ae1e08e1531d989e101d81c57f1d094b741c53b96d1c1ffead1b8548e61b78d4bc1b70b1901b61a0cd1b52f3321b325a461b2d157f1ac4a36f1a5d39541a4058c31a2bfa9c1a0ece701a0dc40d19d9673c19b1d448196672e1191531f418e3fb0a183e8305181aa94117ea3a8d17d07b00175a929b170db67f16e8db1816b50ee91606144c15ff8a4715f86a801561a43a141a4f1c1415063f13b5da6d135211a2131bfefa1317dd2b12b8ab41
  | 7, 2 => 0x354bc4fd3481847a34746a9f34744a7f342cdee933d93c6b33193e9a330961a632f6275b32e64fc5326a0621315024ba3129ad3f30dbc90430ccd1eb302ca7772fc976f62fa1c82a2f7655c82f1362052ea6e42e2ea0b9112d90db782d8366eb2d6df75a2d014b912cf3c0ef2cf085992cb7e2692cb7951b2c9946a22c1543872bdd94e82baacaed2b698d6c2b55ce492af4104e2a88c2ce2a7c85282a6bdfc029e942c429c478db2964176b291abe5628c04ce02889888f2882e2b2284db2db2838c79a2775450f2774c460272770732705880d26beaf6f26bb2fef26a4b5bf265363bb264ea12126488ebe26396ad425eade8525bece64258a6ea4255ffecb
  | 7, 3 => 0x43555fb0433f660a4309ffd842b779a342815d8a4223bdb94214fad141d622d341a8390641a4b5d6413ca69640db2d8b40bb28344079af63405c8f3d40455b7a3f8b9abe3f49363a3f086e6d3ee6de3d3e1c8eb63dff89d03dc32c533d18fbc93d0124c93cedcf813cd7d7c23c9f3cdf3c9dc2fe3c8fe41f3c3d49423c39fd5e3bd0b7833b5624293b23954e3afd7b253acd3e823ab732093a8b9b213a4766343a305add39bf694c396f572d39500340391f126038ad846e3899ed1837a1ed1c378f31e8375fd1e83732d33a36f4981f36e4026d36b6da9236ad516036224d1b361b1af435f0ac8c35d89aaa359aee6d358e7c13358633f2357bcd57355e29ce
  | 7, 4 => 0x52942b725275541c51efbb6051ed493f51e81d5151d2062b51bf3f2b515c291950c4b4ed50a706e8505beeb35038abd64f9b055d4f943bc44f717d1d4f624ff44f0fba7a4ec05ebd4e9d19034e79bd534e7327324e5bae794e0e9fc94dd111674d1acf0f4d17706a4d0476064cfd734b4cd8ba054c173de94c1326ad4bff26be4bf147df4bc969994bb8974e4bb13b214b7591cb4b62f61f4b02825d4a9691394a6707154a3f78dc4a0d197449e125c649148db048f889f848f0bd7d48ebd2aa48b0ac9d484e6acf475141bb472e33c146e149a246792c03466b4d244609964845f6b58445c07cca457c5ed144cd758b43cee64d43b4257143a9f848439ad251
  | 7, 5 => 0x645092fc6449b75d64015902638147926379a6766347643b633af0116336351163275f156292bf22626bc61862623a3561f427ee6129ea2960c016455fd513de5f5d13a95f492eb65eebace45edafec85debf6475dc82fa15d9647d45d93d62e5d6275f45d2e415c5d23bf8f5c9fbd605c91de815bff541c5b2acd595b0171135a73054d5a7078f859f684b259e9c31b59e533015923c1c6591ead9b5905159658a5f17758905d13584e132a581fb8f65806ebe257e67c3956dbe56f56da22f0568ff7f1567ee6cd56240dff55df5df855ab6c4655a4d29e54ed1c7554c1de1054b47b9853b7a8b55342fdb7531915d153169294530ec13f52cda0dc52acbe7d
  | 7, 6 => 0x76bdf4b976b015da766385db764692e676311c2d759ff9f37540089874e1bd6173a1eeb77341d2fd7333c42e73227b8e72b28339727daf3d72739f547260e48f721cd833707cee8d7005f1236fa6c90d6f6c29a26f69601f6ebe77696eba99336e834bca6e5c97526e38e6f66e34ebde6ddedbb86db8095f6d5cb0976ce170276cd622c66c4b6e046bed6d236be1bd3a6bcb63fb6bc490ee6b89f08a6b7c11ab6b46b4d16b1be3666adde2696a5eea176a4f22086a2a46cf69f5d2f969c031bf69b2eaed69387cae692e70ee6920920f68ff5c7d68b561d0683fb3fc67f1c0d3679d352a6709aa6166fb4c916635754265760004651506a464ffcc4e64789948
  | 7, 7 => 0x877c8a9f876b320387080352869b7594867726a18635a6fc85f48e9f85e99b5485210b038492c7cd83f048fb83c5bc52838341f4833df903830766bf82d3eb99828511a48241b05982121d0d81cc74a781bd8a2f8152a7cf81102355806266ad804281917fc0036d7f5f0e0b7f27d8097f1797dc7ecd8d627ebd26667dad4e397d7d57bc7d776c2f7d33ff317d303bbe7cedd8fb7cd372a07c439fcf7c0721267bf0d3337bc86ac17b4614867b2b17a17ac854af7ab597257aa157477a7a23a879a4d76c794792a7791d9b417900675a78f04d3478925775785a178978493a7f77f10ba277d135d07733bc5377211a3f76fcab1e76f0de3376f0916b76db0b2e
  | 7, 8 => 0x965531e69603a49895fe78aa95d1453095a996be9597dcf5955a08989542488b9502be1694b8834e946763cc94331b6593f42b8d9396353d9351acbb934043b892b08ece92a6c201929a9c84928df768928cbda59272b1cc926d751e925c0be491bae140913b5e9f9074f28c906d26119037c66b9011f582900c696690061e318fe9ad8f8f9d1d5f8f7fd14d8f78512d8f6e24048ebf00228e6e30d28e4941358e35cdb08e27eed18dcbb2008d92f6958d7f04bb8d3d413a8c8386ea8c1a6ee88bedc1998bc68b508bbc73f08b8fda438b3e939c8a8bfac78a59f30f8a18c28889f226db89beef4c8968a0cb8958e8bc88edfe0d88ede02887cdddd087ca80ca
  | 7, 9 => 0xaaa935daaa8df529aa87c3f1aa38618daa2867c5aa21bb6da98c5b5da9647ee6a909e4c1a8d69abba80d4bfda8098f40a71939e5a661d0dfa5e4c2a9a5cabbeaa5103ec2a4dede88a3f2435da36baaf7a302d5f5a2359dfca1f6e797a1c6431fa1662bafa141bf77a0d63b5ba0c045e2a0b26703a07b3991a02ef21ba00d2aa29ffd08839ed2ecfb9eab30d29e6bbe4b9e58572e9dac490d9da1794d9d61744b9d3121ea9ce015509c97dd089c27c3cd9bfcd7929b71391a9b1dd7b09ab0be7a99ed5e87997d456498fcecee9882e2ec985a34f798553ede98411d81981b7e9297a5128c974e73179721f5ed96fad25696a4b77d968ac1e99680ac86965f3458
  | 7, 10 => 0xbcb2dff7bc5e25f5bbec3344bb3f92c0bab08b31baa8a17cba477786ba45dd7fb97e2118b9782853b96ec08eb89a4e82b85c2f59b84d21e0b837fe7bb81d78f4b7a3f583b7610a65b702d21ab69fded2b65f3e8fb5c9ec3db59a84ddb559ed2fb52557b8b5195244b4e46fecb3f8265db32b1ae2b2f03ccbb2dc7687b2b203c0b253eee6b2306866b210ca3fb18cc501b12375bdb0f51e5bb080f6ebb0480e0db031ca64b02268afb01ae1b0afebec7daf95e2ffaf935789af01b67aaef43dc2aee65ee3aec64c0eaebd223cae8d3699ae5c9576ae064aa9adab993dad85a160ad1a90a7acac34b6ac3ab49dac23afedabe5308aabbe6e52ab94b348aab1140c
  | 7, 11 => 0xd0317033cfe713d2cf84bc20cf6e15b1ceecb93fceeb1ad8cecb96dfce6b8b90ce3bc8d3cdd2d617cd81b5ebcc0b8b0bcbfcbae9cbf938c0cb46a5f8cb26fa2bcae6d7d7ca35eab9c9e24337c9a019fdc8df6e8fc876c3bec7a3ca76c7554d2ec7466283c707ac1ec6398efac5e58a67c5dca5abc59d6c30c5690328c52f7576c4eae2e7c4ac2c82c483e9fec4605fcec37f968dc3598a1dc31b6fd9c278c27bc23de552c21dcfbbc1c5a5bec1c16a74c150c440c1043454bff0ea6dbf8705ebbf4172fabf01fb40bef4bb49bef1afedbe907f01be4be64fbe3418b4be2639d5be1fe45dbe107ab6bddd5bacbdd38f62bd5c9ba0bd3f82f8bd2744b8bcf5d0c6
  | 7, 12 => 0xe1b94d76e0f3695fe0d9cf49e0d27efae088d44de07b344ee04a17a1e044fe41dfdba1afdfb32b5bdf91a28ddf7fbf91dede789bded29fcddec9aaa0dec49712deb0d9bade1b0bb2ddfd151addd7f9c9dd547ea2dd4db3aadd0995b1dc240579dbeeb34ddb53d48eda9d9f72da8fa153da834ec6da8008d2da7890dfda26b2c9d9ed2281d9eccea3d9b9b7a8d988b69cd8f62b1fd8e7dfa1d8653959d7d8277ed7c0c947d76eed8dd7661623d697c1d4d62ad27fd5d7c256d58853add56748abd50c7c51d4fb6d4fd4f736c8d3a21f4ed38eac86d355d4ffd2f75b26d27a66b2d2522cc3d1d3f658d1b38e6dd17f337bd1786b89d0e5095fd0a7e5c1d051c79b
  | 7, 13 => 0xf5493ef0f51b3615f50771aef34c8d5af32a1730f30eb1d1f225fc9bf1c7ebb4f17a65ebf171c893f15afe71f15a4793f14d1f92f13569a4f11d8484f0f10dbeefeaeca8efdfd1c7efdef6d4ef4adc1aef0e3eb4eef3064deec76f65eeae7dabee570e7dee22ff53ee1e2c58ee185818ed5ae6a4ec848404ec3f654debc28ee5eb7a065aeb3fcd10eaf7dac4eabceb59ea39f55dea206746ea04555ae9f23fa9e9d3bc26e8b54ab1e8b03ee3e878be20e812cbdfe7a75556e7797117e73c37a0e7283c3de5c6ac76e575a6eae5179d48e48a3599e4625a30e4402e8ee3ed24d8e3d420a8e33582dbe2f6cc76e2f02cffe2e453e9e1e7aed7e1ccafbce1c2a466
  | 7, 14 => 0xffabe638ff24a7f5fefc312dfef2bd64fed37441fe809189fe12eeb4fe091979fdc3a01ffd875a02fce2758bfc7cb7dbfc3e0176fc3650befbefb591fbe5e7c4fb192d73fab495f5faa130d0fa6ea56df9b99d75f9acd0faf9824cb5f96fc4f9f9092d95f8b72109f80ff336f80fe67ff7fbcecdf7e68aa8f7c476a1f762f14af734b506f6753fc8f6655c2cf65fed09f646c3bff62cba88
  | 8, 0 => 0xf33b5fd0f2854adfdee29a6add9de376c3d681efbad4da24b6be76348ab84b5d7e1a8a56764e5f6161ca40085e22a75455df5df851bb2a0f4f8c57c24aee737942b779a33e277fff2eedfa851e7359ed1729918f1606144c1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x520c12030000025041201000002148420200000000c010a00000000c4108761052044140000194414c130000000000c5102761052044140000000150c120100000001001070000000000001001143144130200000000c0109000005108120700000000000070000000000011000000000000a00000000c410800194414c13000000000000004
  | 5, 0 => 0x1100000454c420000000000841070000000100107000000000000a000000000000600194414c130000000000000110000000000006000000010010700000000c010a00000000c110300000000000110000000084107000000010010300000001001070000000000003000000000000800000000000100000010440200000000000000d0000000105100000000008410700194414c1300000000000001100000214c52020000045041201000000000000b00000000c51020000000000001000000000000b0000000000008
  | 5, 1 => 0x4544020000000000000000000000000003000000000000f000000000000e000000000000300000000c010a000000000000c000000000000a000000000000c0000045085202000000008510000000000000070000000100103000000000000a00000414c12000000000000011000004144120000000000c010a00000000c410800000050852010000000081107000000000000b0000000000000000000000000d0000000000003000000000000a00000000000010000030441200000000010010700000000c410800194414c1300
  | 5, 2 => 0x100103001191500a300000001044020000000001041070000000000011000000000000b00000000000110000031441202000004144120000000000c010a000000000000a0000000000008000005048420000000000c5102000000000000a00000520c120300000000000020000000000005000004504120100000000000010000041441200000000000000b000000010410700000520c1203000001044020200000000c5102000000000000b00000000000060000000000008000000000000100194414c13000000000000005
  | 5, 3 => 0x700000000000020000000000011000000000000a000000004c1010000000000007000004508520200000000c1101000004108420700000504c4200000004504120200000520c12030000000041101000004508520200000000841070008115480300000005108120700000000000100000045085202000000000000a00000000000070018532105300000000000000a0000000104107000000000000b00194414c130000000254402000000021484200000000540a20000000000c11030000035081207000000000000a
  | 5, 4 => 0x194414c130000118254c43010000021484200000000000001100000510c12030000035002201000003144120200194414c1300000000000000d000000000000d000000000000400000450412020000031441202000000000000c00000001001030000045085202000000000000100000154802000018c4540a300000000010010300000000c51060000000100103000000000001100000000c010a000004508520200000000c4103000000000001100000000000060000000000011000000000000500000000000080000000000010
  | 5, 5 => 0x10410700194414c130000000000000070000053105200000000008410700000450852010000000100107000000008510200000001001070000000104107000000000000200000001001070000045085201001944148130000000000000100000035002200000000000001000000000000110000000084107001182048030000000454842000000021484202001143144130200000000c5102000004144120000000000000110000000000011000000000000b000002504120100000000c010a00118504c430100000000c010a
  | 5, 6 => 0x3500220000000000c1103000000000000a00000000c810700000001001060000020480202000000010810600000000c1105000000000000a000000008110700000000c110000000000811070000053105200000000000001000194414c130000000000c010a0000000000011000000000000f00000520c1203000001044020000000000c010a0000020441205000000000000600000000000060000000000006000000000000800000000c5106000004504120200000000c51060000045085201000000000000b00000000c1100
  | 5, 7 => 0xc00194414c130000000000c1103000000000000b000000010010300000000c01080000045041202000000010410700000000c81070000000104107000000000000b0000025041201000000000000c00000000000030000000000010000000000000a000000000000a0000000000006000000000000a000d821484300000000000000d000000008510200000000000010011431485302001143144130200000000000110010520441300000000004c101000000000000a000000000000700194414813000000021484201
  | 5, 8 => 0x1100000450412020000000000000000000004110000000254c42000000000000011000000000000800000000000090000000100103000003508120700000504842010000000000000000003508520000000214c5202
  | 6, 0 => 0x254c020000000000c5106000000000000b000005048420000000000c5102000000000000300000000000060000045085201000000000210000000000c8107000000000000a000000000000a00000250022000000025440200000000000000800000350852010000000000005000000000610200000000000060000000000007000000000000c0000025440200000000010410700000450062000000000000005000000000000c000000000000500000214842020000000000001000000000000a00000514c82000000000000001
  | 6, 1 => 0xc00000000021020000005885200000003508520000000104402020000020480201000000000000a0000000085104000001044020000000350022000000000006104000000000a10200000414c120000000454c4200000004508520200000000000070000000000011000000000a1040000000000006000000000000b0000000000005000000000000a00000000c010a0000000002104000000000000d0000045041201000000000000800000000000050000000081102000005048420200000000000060000000000003
  | 6, 2 => 0x81040000000000001000000000001100000000c5102000003044120000000214842010000000000005000000000000300000454c420000000454c4200000000000000d000000000000a000002048020200000000000030000000081102000000000000b0000000002102000000000000b000000000000b00000000000030000000104107000000000000f0000000000002000000000210000000000811070000000000003000002500220000000000000070000000000009000000000000a00000450412010000000006102
  | 6, 3 => 0xc5106000000008110400000354402020000000000006000000000a1020000000000011000000004c101000000000a1000000000000005000000000001100000000c51020000000000007000000000000800000214842020000010440200000000000000d0000000000006000000000000100000000000050000021484200000003508520100000104402020000000081101000000000000100000000c1103000000000001100000000000070000000085102000000000000200000000c8107000000004c1010000000000003
  | 6, 4 => 0x504c4200000000000000100000000000070000000000003000000000000d00000000061040000000000007000000000a101000000000610000000000c1100000000000a101000000004810400000454842000000035002200000000000000a00000000000010000000002101000004504120100000414412000000045041202000002048020000000000000000000031441202000000000001100000454402000000025440202000000000000300000000000070000000000001000000000000000000000000080000025440200
  | 6, 5 => 0xa1020000000048101000000000000a00000000c51060000000041105000000290520000000504842010000000000003000004548420000000000000080000000104107000000000000a000002148420000000000000110000000041102000004144120000000414c1200000004548420000000000000000000000000011000000500a2000000021484201000000000000b000003508520000000454c420000000154c02000000000081107000000000000300000000c1101000000000001100000000000020000000000005
  | 6, 6 => 0xc5106000000000000700000000000060000000084107000005048420000000000000030000000000011000000480a200000000000000300000000811020000010440201000000000000600000414c1200000000000001100000204802000000050484202000000000000d00000000c11010000000000000000000000000200000000061020000000000010000000000000f0000031485202000000000000a00000000c51020000000000008000000004c10100000000411020000000000007000000000000b00000414c1200
  | 6, 7 => 0x700000000000060000045440200000000000610100000000c51020000000012100000000000000500000000c4100000000000000700000000000030000000000007000000000000700000104402020000000000003000000000210200000001001030000003905200000000000000000000000000110000045041202000000000000600000000000030000002905200000000000a100000003508520000000454c4200000000000000b00000000000050000000041102000000000000500000000000050000053105200
  | 6, 8 => 0x811040000000000002000000000000500000000000110000000041100000000000a10100000000851020000000100103000000000000d00000000000020000053105200000000000000700000000000070000000000003000004140620000000454c42000000021484200000000000000b000000000000a0000035002201000003210520000000000c51060000021484201000000000000a000000000000800000000c51020000020480201000005048420000000104402000000000000008000000004c1010000000000001
  | 6, 9 => 0x200000000c51020000020480200000000000000800000000c11030000021484200000000000000300000414062000000000084107000000004c10100000000000070000000000001000002148420200000000c110200000104402000000000085102000000000000b000000000000b00000000021010000025440201000000008510000000000000030000045041202000000000000300000000000010000000000002000000004110200000531052000000045041202000000540e20000000000000030000000041104
  | 6, 10 => 0x2148420000000454402000000045484200000000000000d0000000041101000000000000800000000c010a00000414c120000000454842000000004806200000002048020100000000c11010000041441200000002148420200000000c5102000000000000a0000000000007000002544020000000000c51060000041441200000000000000a00000254402020000002806200000000000000b000000000000900000058812000000000000006000000000000a0000025440200000000000000600000000000030000000000000
  | 6, 11 => 0x2100000000000000b00000000c5102000000000000600000000000030000000041105000000584120000000000000080000000000003000000000000100000414c120000000000000110000000000002000001500a200000000590520000000000c51020000025440200000004508520100000000000000000000000003000000000000700000531052000000000000007000005048420000000450412010000000100107000000000a1020000000000000000000000000a000000000000700000001051000000000000006
  | 6, 12 => 0x41441200000000000000600000000c010a00000531052000000053105200000000000000d000003048120000000000000060000020480200000004544020000000000c510600000254c42000000053105200000000000000b000000000000a00000350022010000000085102000000004110400000000c5106000002048020100000450852010000000000008000004508520200000028c1200000000008510400000000061010000000000003000005048420200000000021020000010440200000000000000700000000c5102
  | 6, 13 => 0x4544020000000454842000000030402200000000010010300000350022000000000000007000000000000300000514c820000000000c110100000000000060000000000005000000000000500000504842000000000000006000000010510000000414412000000000000005000002048020100000000000060000021484200000000000000700000000c110300000000000090000000000005000003500220000000000c110300000000000050000010440200000000000000500000000c1100000000380220000000214c1200
  | 6, 14 => 0xa0000020480200000000010510000000000c51020000050484201000003500220000000000000060000010440200000000000000b0000000000007000000000000600000000c51020000000000007000000004810400000450852020000010440201000000000a1040000000000007000000000610200000000000080000020480200000000000000a000000000000a000000000000d000000000000a0000000000007000000000000500000254402000000000000009000005048420000000000061020000000000002
  | 6, 15 => 0x5000000000000300000000c5102000000000000a0000021484200000000000000d00000000000030000000000007000000000000d0000000000005000000000a102000005048420000000000000070000025440200000000008510200000000c010a0000000000006000000000a10000000414c1200000000000000b0000052105200000000000000600000000000050000000000003000000000000700000000801010000000105100000000000000a000000004110200000000c010a00000000000030000000000007
  | 6, 16 => 0x531052000000032105200000000000000a0000053105200000005048420000000000000000000000000001000003508520100000000000030000000085102000000010510000000000000070000000000008000000000000a00000254402000000035440202000005048420100000250412010000053105200000000000000b000000000000100000000000020000000000006000000000000100000000000060000000000001000002148420000000000000070000000000005000000000000600000000121000000052105200
  | 6, 17 => 0xa0000000000003000000000000a000004508120000000000000070000021484200000000000000800000001001030000000000000000000000000a0000005841200000000000000d00000000c5102000000000000b000000000210200000350022000000000000003000004508520200000000c110300000000000000000050484201000000000610400000350852000000000000005000000000000d0000000000008000000000a10100000000000030000000000007000000000000200000504842000000000105100
  | 6, 18 => 0x41100000000004110400000001011000000045085202000000000a1040000000006102000000000000c00000350022000000000000007000004504120200000000000070000035085200000005048420000000000c5102000000000610000000204412000000000104107000002048020200000000000060000000008104000002544020000000000c1103000000000000100000214842000000000000005000000000000a000000000000a00000104402010000000081104000004504120100000250062000000000000007
  | 6, 19 => 0x2100000003544020200000521052000000045484200000002148420100000000000020000000000002000002544020000000000000030000000000007000001044020000000354842020000000000003000000000000d0000000000000000000004110200000414412000000000000007000000000000a0000050484202000000000000b00000000000030000052105200000002544020100000314412020000000000003000000008510000000000000030000000000007000004544020000000000000080000020480202
  | 6, 20 => 0x2148120000000000c110500000001051000000031441202000000000000300000000000070000000000003000000000000a00000000000070000000000007000005210120000000000061010000025440201000001044020100000001001030000000085102000005310520000000000000100000050484200000000000000b0000000000007000000000000200000000000030000000000005000000008110200000504c82000000020480202000000000000b000000000000a000000000000300000000000110000000000001
  | 6, 21 => 0x25440200000002148420200000000c51060000035081202000000000000300000504c4201000000000000d000000000000a000000004c101000000000000200000000000070000000085102000000000000300000000000070000000085100000000000000300000214842000000000000007000003544020200000000000020000000000002000000000000a000004508520100000504c820000000001041070000045440200000000000000800000000811070000000040100000000000000b0000000000003000000000000a
  | 6, 22 => 0x414852000000000041101000000004c1010000000000003000005048420200000000000030000000000003000000000000000000000411020000053105200000000008510400000454c42000000015002200000002544020100000254c42010000025440202000003500220000000000c510200000454842000000000000007000000000000200000000000070000020480201000000000000d0000002905200000000000000a000000000000200000000c1103000000500620000000000851020000000000007000000000000d
  | 6, 23 => 0x100000000081010000000000007000000000a1010000045484200000004140220000000104402020000053105200000000000000100000000c1103000000000000b000000008510200000000000070000000002102000000000000b00000000000070000041441200000000000000a000000000000b00000254c0200000000000000a00000504c8200000000008110400000000c81070000000000007000003508520000000104402000000000084100000000010510000000000000060000000000011000000000a101
  | 6, 24 => 0xa1020000000000002000000000000700000000000070000000000003000000000a10200000000c51060000025002200000000000000700000450852010000041441200000000000000b00000000000050000000000002000000000000500000214842000000000000001000000000000200000000000070000052105200000000000000a000005210520000000000000060000000000006000000004110200000504842020000041441200000000000000300000000061010000000000007000000000000500000000c5102
  | 6, 25 => 0x380a20000000414412000000000000003000000000000300000000c5102000000000000700000000000030000025440202000000000a10200000000811020000000000007000000000000b00000304022000000003905200000000000000d00000000000080000000000001000000000000300000000481010000000000006000000000001100000000c11000000000085102000000000000a00000000c5102000000008110200000000000070000021484202000004540a20000000000c5102000000000000c000000000000a
  | 6, 26 => 0x1011000000035002200000000000000400000000c5106000002544020000000000000050000000000002000000000000a000000590520000000000021020000000000011000000000000a000000000000700000000000070000035085200000000540a2000000000041102000000004c101000005310520000000000c010a0000053105200000000000000500000000000030000045484200000000000000500000504842010000000000000000005048420000000000c51020000000000006000000000000b00000454c4200
  | 6, 27 => 0x50000000000010000000000a10200000000c5106000000000000b000000000000100000001091000000000000006000000000000d000000000001100000000c5102000000000000600000000c510200000454c4200000000000001000000350022010000000000008000000000000b00000000c510200000304812000000000000007000000000000a000000000000b0000000002102000000000000b0000010440201000002544020200000000c81070000000000003000000000000500000000851040000000000007
  | 6, 28 => 0x7000000000000a00000304412000000000085100000000000000b000000000000d0000000000001000000000000500000000000030000000000005000000000000700000414c120000000000c110000000000c51020000035085201000000000000300000214842010000005885200000003500220000000454842000000000002102000004508520100000000000000000045041202000000000000b000005210520000000000000030000000081102000000000000b000004144120000000000000070000000006102
  | 6, 29 => 0x414c120000000000c510600000000000100000053105200000000000610100000000c51020000000000003000002048020000000000c01000000000008101000000000000b00000000000020000000081104000000000000b00000000c5102000000000000b0000000041104000001540a200000000000000b0000035002200000000000000300000450062000000045484200000000000000700000000000050000000000005000000000000d00000000c41030000041441200000000000210200000038062000000025440201
  | 6, 30 => 0x100000000000010000035002200000000000000d00000000c11030000000100107000000000000a00000000811020000035085200000000000000d000000008410700000000000030000045440200000000000000a0000000002104000000000000b00000531052000000025041200000005310520000000000c11050000000000006000000000000a000000000000700000000000030000000000011000000000000a000000000000a00000204802020000000000011000000004110000000000000110000000085102
  | 6, 31 => 0x531052000000000000011000000000001100000000c51060000000000006000000000001100000454c4200000005310520000000000000080000015480200000000000000300000204802000000031441202000000000000b000000004c101000000000000a000000000000700000454c4200000000000000000000531052000000000006104000000000000a00000000000060000035085201000000000000a00000000000010000000085102000000000000700000000000070000020480200000000000000500000000c5106
  | 6, 32 => 0x45041201000000000000300000000851010000000000008000000000000b0000000041100000000000000300000000411020000000000002000000000000d000000004c10100000000021020000053105200000000000000600000254412000000045440200000003508520000000000000110000000000008000000000000300000000000010000000000007000002048020000000000c8100000000004110400000304812000000000000006000000000000b0000035002200000000000000a00000000000020000035484202
  | 6, 33 => 0x1000000000000300000414c12000000000000007000000004c101000000000000300000000000050000000000003000000008110400000000000000000000041100000005310520000000154802000000050484200000000000210100000000c81010000045041202000000000000a0000000000002000002048020000000350852000000000000003000000000000a000003500a200000005310520000000000c5102000000000000b0000050484201000000000000b000000008410700000000000060000041441200
  | 6, 34 => 0x8000000000000b00000000000070000000000008000000010510000000000c110300000000c510200000314412020000000000003000004508520200000454c42000000000080102000000000000700000504c4200000004508120000000000000020000000000006000000000000300000000000080000010440202000000010010700000254c42000000053105200000000000e10000000000c5102000000000a10100000000000000000000081105000000000a102000000008510000000000000050000041441200
  | 6, 35 => 0xc11050000000000005000000000a1000000000000007000000000000b000000000000a00000000000070000000000006000000000000300000531052000000020480200000000000000200000028022000000000000002000000000000a000000000001100000000c5102000002048020000000104402000000021484201000000000000100000000811040000000000002000000000000a000005048420000000531052000000035002200000000000000a000000000a101000003548420200000000000030000041402200
  | 6, 36 => 0x2544020000000450062000000000000003000000000000700000000000050000000000002000000000000700000350022000000045440200000000000210000000354842020000000000005000005310520000000454402000000000000007000000000e101000004508120000000000000060000035085200000000000000100000314412020000010440200000000000000000000000c5102000000000000500000048022000000025440201000003508520000000000c1101000000000000800000000c11030000045006200
  | 6, 37 => 0x50000035002200000000000610100000414c120000000000000080000021484200000000000000300000000c1103000000000000900000000000080000025440200000000000000d0000000000000000003548420200000350022010000000000000000000004110000000000c5106000000008110400000000081010000000000011000000000000c00000000000030000000000005000000000000000000414812000000025006200000000000a1000000000000003000004544020000000000000050000000000001
  | 6, 38 => 0x21484200000000000000b0000000041102000000004110000000000811020000000085100000000008110400000454842000000000000008000000008110700000000851020000035002201000000010510000000000c51020000000081105000000000000300000254402000000000000007000000000000b00000028c1200000000000000500000000000080000000041105000000000000a0000045085202000000000000a00000000000050000000000003000000000000a000000000000000000001001070000000002101
  | 6, 39 => 0xc1103000005310520000000000000000000035440202000000000000a000000000000200000028c12000000050484200000000000000700000000000020000000000007000002500220000000000000060000000000006000000000000a000000000000b000000000a102000000000000200000000000050000000000005000000000000b0000000041102000000000000a000000000001100000350852000000020480202000000000000700000000c510200000000c8107000002048020000000000000050000001802200
  | 6, 40 => 0xc5102000000000000800000000000050000010440200000000000001100000018c1200000000000000800000000c51020000000000005000000000000b00000104402000000000002102000000000000300000000000070000000006102000000000e1020000000085101000000000610100000000000090000045440200000004508520100000000000080000000000006000000008110700000414c120000000000000030000045081200000000000000b00000000000000000050484200000000000a1020000035002200
  | 6, 41 => 0x25440202000000000000700000350852010000000000007000000000000b000000000000300000018c12000000000081102000000000000a000000000000500000000000030000000081104000000004c10100000000c8107000000000000a000000000a102000004504120100000000c1103000000000a10200000000000030000000085101000000000000b00000454c420000000000000070000000048101000003508520000000000c51020000000000001000000000000f000000000000a000000000000500000000c1103
  | 6, 42 => 0xa0000021484200000000000000b000000000000600000000000050000000084101000004148120000000000c51020000000085102000000000000b000003508520000000214842000000000081102000000000000a000000000000900000000c5102
  | 7, 0 => 0x1091000000000000008000000000000300000001051000000000000002000000000210000000000c1100000000000000a00000000411000000000000007000000000610000000000411020000000000004000000000000d00000000000070000000000007000000008110100000000000010000000000004000000000000b00000000c410000000000841000000000041101000000000000200000000000010000000000011000000000a10000000000841000000000000001000000008110000000000851000000000105100
  | 7, 1 => 0xa0000000000006000000000000000000000811010000000002100000000000000300000000c1100000000000a100000000000000600000000411000000000012100000000010110000000000000020000000080101000000000000700000000000040000000000006000000000a10200000000811000000000000003000000000e1000000000000007000000000a10000000000061000000000000008000000000000100000000841000000000006100000000000210200000000c510200000000c410000000000c8101
  | 7, 2 => 0xc4100000000000000d00000000c8100000000000000100000000000060000000085100000000010110000000000000040000000000001000000000000800000000000080000000040100000000004010000000000811010000000000004000000000000200000000401000000000000007000000008010200000000061000000000002100000000000e100000000000000b0000000000001000000000a1000000000081100000000000000300000000000030000000080100000000000210000000000000000000000006100
  | 7, 3 => 0x105100000000000a1000000000081102000000000610000000000c51020000000101100000000000a101000000000000400000000021010000000006102000000008110000000000000030000000000007000000000000100000000411000000000006100000000000000100000000000070000000000001000000010910000000000801000000000000002000000000a100000000000210000000000851020000000080100000000000000a00000000000020000000006100000000008510000000000000010000000002101
  | 7, 4 => 0xc810100000000c5102000000000a1010000000000004000000000000500000000c1101000000000610000000000c410000000000021000000000000003000000000a10200000000000070000000000001000000000a10100000000c0101000000000610100000000000060000000109100000000000210200000000411000000000000002000000000210000000000000030000000084100000000000000400000000000040000000000002000000000000200000000c1100000000000610000000000061010000000084100
  | 7, 5 => 0x401020000000000007000000000a1020000000000002000000001210000000000000060000000105100000000000e102000000000000700000000c41010000000000003000000000a100000000000000400000000c1101000000000a100000000000a102000000008510200000000000030000000041100000000008510000000001051000000000006101000000000210200000000c51020000000040102000000000000100000000000010000000002100000000004010000000000c110000000000c01000000000105100
  | 7, 6 => 0xc410100000000000000000000006102000000008410200000000c8100000000000000400000000061020000000084100000000008110200000000c11010000000000005000000000000300000000c11000000000081102000000000a10000000000841010000000000001000000008010000000000c410000000000c9102000000000610000000000c81010000000000007000000004010000000000801000000000105100000000004110000000000c0100000000000000400000000c510200000000000010000000000000
  | 7, 7 => 0x7000000000000100000000411000000000000000000000010910000000000c410100000000021020000000000003000000000000a000000000000b000000010910000000000411010000000105100000000008110200000000061000000000000000000000000a100000000000000300000000000020000000006101000000010110000000000c41000000000000002000000000000100000000000010000000000002000000010110000000000121000000000000004000000010510000000000411000000000085101
  | 7, 8 => 0x12100000000010510000000000801020000000000003000000004010100000000021000000000080100000000010510000000000c41000000000002102000000000e1000000000002102000000000a100000000000a102000000000a101000000008410000000000000030000000000003000000000210000000000411010000000000005000000000000700000001051000000000000007000000000e10100000000000030000000002101000000000610000000000c8100000000000000200000000061020000000000002
  | 7, 9 => 0x851020000000000001000000000000b00000000000030000000000002000000000000100000001011000000000040100000000000a10200000000c01000000000000007000000004010200000000021010000000000011000000004110000000000c01000000000006102000000000000b0000000000000000000000000300000000c81000000000000005000000000000200000000851010000000000001000000008110100000000c410000000000000000000000000011000000000610000000000000000000000000004
  | 7, 10 => 0x80100000000000000700000000841000000000000003000000000000600000000000070000000000002000000008410100000000401000000000105100000000000a10000000000000020000000000007000000000000300000000061020000000000001000000000000000000000021010000000109100000000001210000000000000070000000105100000000000000a000000000000200000000000030000000085100000000004110100000000411020000000040100000000000e10000000000000020000000002100
  | 7, 11 => 0xa00000000c010000000000411000000000000001000000000610100000000841020000000000007000000000000300000000021000000000000002000000010510000000000000020000000000001000000000210000000000c4100000000000000500000001051000000000000002000000008410000000000c81000000000000005000000008410200000000c81000000000000003000000000a1010000000000001000000000000d00000000000070000000006100000000000000700000000121000000000085100
  | 7, 12 => 0xe1000000000000003000000000000b000000000a1000000000006100000000010510000000000000070000000085100000000000000b000000000000200000000000060000000000002000000000000000000000c010000000000000060000000080101000000000a101000000010510000000000000070000000040100000000000000d000000000000a0000000000003000000001210000000000411020000000000001000000000000300000000841000000000000008000000000a10000000000000020000000000003
  | 7, 13 => 0x70000000084100000000010110000000000000010000000000003000000010510000000000c110200000000000010000000000003000000000210200000000000020000000000004000000000000000000000c810000000000851000000000002100000000000000a0000000000001000000000a101000000008010000000000c51020000000041102000000001210000000000000060000000080102000000000000200000000000030000000109100000000000000d000000000000a0000000000001000000000a100
  | 7, 14 => 0x300000000c0101000000008110000000000061010000000000004000000008510000000000000070000000041101000000000a102000000000000700000000000040000000000002000000010910000000000851000000000006100000000000000200000000c910200000000c51020000000081101000000000000b000000000000700000000061000000000040100000000000a100000000010510000000000000020000000040101000000000000100000000c4101000000000210000000000801000000000000003
  | 7, 15 => 0x851000000000080100000000000a100000000000210000000000000070000000081100000000000210000000000841000000000040100000000000000a00000000c510200000000021010000000006101000000000000300000000c010100000000000020000000002101000000000000300000001091000000000105100000000000e10000000000000040000000000005000000000000700000000000030000000000003000000000610000000000021000000000000011000000000e10200000000000010000000101100
  | 7, 16 => 0xa10000000000021000000000006101000000000000200000000061020000000000005000000000000a00000000851000000000000004000000010110000000000c51020000000000006000000000a1000000000000008000000000000300000000851010000000040100000000000610000000000c51020000000000007000000008110000000000000070000000000005000000000210100000000000040000000040101000000000a101000000000000500000000c0100000000000000300000000000050000000000002
  | 7, 17 => 0x50000000002102000000000000200000000c1100000000000000500000000c5102000000000000d00000000000020000000000003000000000000300000000000070000000081100000000000000a0000000006100000000000e102000000000000a0000000084100000000000000600000000000040000000000005000000010910000000000000020000000085101000000000210000000000c110100000000c8101000000000a102000000000a10100000000c0100000000004010100000000801010000000006102
  | 7, 18 => 0x8110000000000c1100000000000000300000000c810000000000851020000000000002000000008410100000001011000000000000007000000000000b000000000610000000000c110200000000401020000000000008000000000e1020000000085100000000000000a00000000841000000000109100000000000000500000000000010000000040100000000000a1020000000000007000000000000a000000008410100000000c810000000000000050000000080100000000000000a000000000a1000000000084100
  | 7, 19 => 0x210000000000000070000000002102000000008010000000001011000000000000006000000008410200000000021000000000000006000000000000a0000000041101000000008010100000000c4100000000000e100000000008410000000000000030000000000003000000000a1010000000006102000000008010000000000c4101000000000000100000000000070000000109100000000000000300000000811000000000000005000000000000200000000c0100000000000e10100000000000070000000000006
  | 7, 20 => 0x210200000000000020000000000001000000000a100000000000000300000001011000000000040102000000000a100000000000000a000000010110000000000c410000000000c0100000000000000500000000000010000000085100000000000000200000000c810000000000000010000000000006000000010910000000000801010000000000007000000000e100000000000000100000000c0100000000000e101000000000000700000000411000000000000001000000000610200000000411020000000000008
  | 7, 21 => 0xc0100000000000000100000000000010000000000001000000000000300000000851020000000080102000000000000200000000000010000000000007000000000000500000000c110000000000061010000000040102000000000000a0000000000007000000000610000000000000010000000000002000000008010000000000061000000000101100000000008110200000001091000000000041100000000000000100000000811000000000000001000000000000100000000801000000000085102000000000000a
  | 7, 22 => 0x4010100000000000070000000000007000000000000100000000c0100000000000000100000000000030000000000006000000000000300000000000040000000000003000000010910000000000c010100000000c1102000000000000500000000000000000000000002000000000210200000000000010000000002101000000000000200000000021000000000000002000000000e10000000000c81000000000084102000000000000300000000000050000000101100000000000000000000000000030000000000003
  | 7, 23 => 0x4110000000000c010000000000c8101000000000000300000000411000000000000003000000008010200000000c81000000000000001000000000000700000000c110000000000c81000000000006102000000000000a000000000610000000000c410000000000c8100000000000000600000000c410000000000000020000000081100000000010510000000000c01010000000000005000000008510100000000000070000000000001000000000a1020000000084102000000000000000000000c9102000000000a100
  | 7, 24 => 0xc9102000000000000300000000000110000000081100000000000000a000000001210000000000811020000000012100000000000000b0000000000002000000000a1000000000080102000000000000300000000c810100000000c110200000000000030000000000002000000000a1000000000000005000000008110100000000000020000000000002000000000000300000000841010000000105100000000000000000000000c810000000000000040000000105100000000000a10100000000061010000000000004
  | 7, 25 => 0xc9102000000000e10000000000121000000000081100000000000000a00000000000020000000000005000000000000700000000000030000000000004000000000000400000000000020000000002100000000000000500000000c4100000000000e101000000000000200000000c8100000000000a100000000000001100000000c110200000000000030000000002101000000000000300000000c0100000000010510000000000c1100000000000000a00000000000070000000000004000000000e100000000000e100
  | 7, 26 => 0x61000000000105100000000000210100000000000050000000002100000000000000700000000061010000000000001000000000a1000000000000003000000000a10200000000061000000000000002000000000000500000000811000000000000003000000000210100000000c4100000000000000b000000000e1010000000041102000000000610100000000c4101000000000a10100000000411000000000080101000000000000d0000000002100000000000000b000000000a10200000000021020000000000002
  | 7, 27 => 0x50000000105100000000004010000000000851010000000000004000000000000b00000000c11000000000000005000000000610000000000000030000000000011000000000000300000000811000000000000003000000000a1000000000040101000000000610000000000000010000000000002000000000000d00000000021000000000000004000000000610200000000000030000000000001000000000001100000000000060000000000011000000000e100000000010510000000000c11010000000000006
  | 7, 28 => 0x20000000040100000000000000200000000c4101000000000000800000000c01010000000000008000000000000700000000000000000000012100000000000000200000000021000000000012100000000000000300000000401000000000000002000000000000000000000c1100000000000a10000000000021000000000000003000000000210000000000000010000000000001000000000a1000000000085100000000000610000000000000080000000000004000000010510000000000000020000000000005
  | 7, 29 => 0x1000000000000500000000000050000000000006000000000000a0000000084101
  | 8, 0 => 0x20000000000000000000000000000000000000000000000000000000000000000000000000000010000000000001000000000000200000000000020000000000002000000000000000000000000010000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_10 roots_10 8 s ws hint
  | 1 => checkCutEntry dom_12 roots_12 7 s ws hint
  | 2 => checkCutEntry dom_13 roots_13 7 s ws hint
  | 3 => checkCutEntry dom_15 roots_15 6 s ws hint
  | 4 => checkCutEntry dom_11 roots_11 6 s ws hint
  | 5 => checkCutEntry dom_16 roots_16 6 s ws hint
  | 6 => checkCutEntry dom_18 roots_18 6 s ws hint
  | 7 => checkCutEntry dom_19 roots_19 6 s ws hint
  | 8 => checkCutEntry dom_20 roots_20 5 s ws hint
  | 9 => checkCutEntry dom_17 roots_17 5 s ws hint
  | 10 => checkCutEntry dom_14 roots_14 5 s ws hint
  | 11 => checkCutEntry dom_22 roots_22 5 s ws hint
  | 12 => checkCutEntry dom_24 roots_24 5 s ws hint
  | 13 => checkCutEntry dom_26 roots_26 5 s ws hint
  | 14 => checkCutEntry dom_27 roots_27 4 s ws hint
  | 15 => checkCutEntry dom_25 roots_25 4 s ws hint
  | 16 => checkCutEntry dom_23 roots_23 4 s ws hint
  | 17 => checkCutEntry dom_21 roots_21 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_28 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_22 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_26 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_28 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_28 == dom_28) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_28 goalM u ys) : RunD dom_28 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_28 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_8 : ∀ i, 8 ≤ i → i < 10 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 8 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 10 → Z 4 i = true := range_split z4_0 (z4_8)
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
theorem z5_48 : ∀ i, 48 ≤ i → i < 49 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 48 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 49 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (z5_48))))))
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
theorem z6_184 : ∀ i, 184 ≤ i → i < 189 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 184 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 189 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (range_split z6_160 (range_split z6_168 (range_split z6_176 (z6_184)))))))))))))))))))))))
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
theorem z7_160 : ∀ i, 160 ≤ i → i < 161 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 160 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 161 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (z7_160))))))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 8 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_8 : ∀ i, 8 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_16 : ∀ i, 16 ≤ i → i < 22 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 16 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 22 → Z 8 i = true := range_split z8_0 (range_split z8_8 (z8_16))
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
  scr dom_28 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_28 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_28 roots_28 goal_28 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_28 goal_28 := by
    have h0 : isConstB dom_28 goal_28 = false := by decide +kernel
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

end S_28

theorem low_28 : Lower dom_28 roots_28 goal_28 10 := S_28.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_28_bits : ∀ r : Fin 64, roots_28.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_28_lt : ∀ r : Fin 64, dom_28.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_28 T)
    (hlow : Lower dom_28 roots_28 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_28, Avail mask256 roots_28 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_28 hfan 0 roots_28 roots_28 rfl hsup0
  set out := (execN C.gates roots_28).getD C.output 0
  have hout : out &&& dom_28 = T &&& dom_28 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_28_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_28 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_28_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_28).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_28)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_28.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_28 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_28).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_28 &&& mask256 = dom_28 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_28 = T &&& dom_28 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_28, hd63, hout]
  have hnc_m : ¬ IsConst dom_28 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_28 roots_28 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_28, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_28 roots_28 0 roots_28 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209690824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_28.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_28 10 hT6 (by unfold IsConst; decide) low_28

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [6, 5]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [8, 2]⟩, ⟨GateOp.and, [9, 2]⟩, ⟨GateOp.and, [10, 3]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.and, [13, 7]⟩, ⟨GateOp.or, [11, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_16653_aux

theorem PEqualNP.Outside.L_meta_16653 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209690824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209690824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_16653_aux.wit, PEqualNP.Outside.L_meta_16653_aux.wmono, le_trans PEqualNP.Outside.L_meta_16653_aux.wsize (PEqualNP.Outside.L_meta_16653_aux.lower s hs), PEqualNP.Outside.L_meta_16653_aux.weval⟩
