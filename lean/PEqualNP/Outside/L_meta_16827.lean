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

namespace PEqualNP.Outside.L_meta_16827_aux

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

def dom_0 : Nat := 0x55555555
def goal_0 : Nat := 0x54444440
def roots_0 : List Nat := [0x44444444, 0x50505050, 0x55005500, 0x55550000]

namespace S_0
def pairsG : List (Nat × Nat) := [(2, 6), (2, 10), (2, 18), (4, 6), (8, 10), (12, 14), (12, 28), (16, 18), (20, 22), (20, 28), (24, 26), (24, 28)]
def r1sG : List Nat := [2, 2, 2, 4, 8, 12, 12, 16, 20, 20, 24, 24]
def r2sG : List Nat := [6, 10, 18, 6, 10, 14, 28, 18, 22, 28, 26, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 3 => 5
  | 4 => 9
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe0cd3775430688dc3184da1925a9cffe1102555d
  | 4, 0 => 0xe0cd3775d8b0438f644592bc5e8a8e404d80fb4742ab9e403be2c1fd158e9dfc0e629920
  | 5, 0 => 0xe0cd3775
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x540054000000000050505050000000005000500000000000444444440000000044440000000000004400440000000000111111110000000000550055
  | 0, 1 => 0x5555444400000000555500000000000055505550000000005500550000000000545454540000000054505450
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xca644c7644ca844cb544da634
  | 4, 0, 0 => 0xca644ca6415cba6450ca614ca64050c6404ca6425ca6545ca9645
  | 5, 0, 0 => 0xca644
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x60368060007000000ff838f
  | 0, 1 => 0xf87f80f78c7036f368
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xe72b69a605bf584432a4018d
  | 0, 1 => 0xffffc4f7be72ffff7b
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 14 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 14 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 14 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 14 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_0 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_0 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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
  scr dom_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_0 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_0 roots_0 goal_0 6 := by
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

theorem low_0 : Lower dom_0 roots_0 goal_0 6 := S_0.noCircuit

def dom_1 : Nat := 0x33330000
def goal_1 : Nat := 0x32200000
def roots_1 : List Nat := [0x22220000, 0x30300000, 0x33000000]

namespace S_1
def pairsG : List (Nat × Nat) := [(17, 21), (17, 25), (20, 21), (20, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [17, 17, 20, 20, 24, 24]
def r2sG : List Nat := [21, 25, 21, 28, 25, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x1d20c287
  | 3, 0 => 0x1d20c287
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3300000000000000303000000000000022220000
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

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
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

def dom_2 : Nat := 0x33333333
def goal_2 : Nat := 0x32202220
def roots_2 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x33330000, 12, 28)] (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0xf0f
def goal_3 : Nat := 0xe08
def roots_3 : List Nat := [0xa0a, 0xc0c, 0xf00]

namespace S_3
def pairsG : List (Nat × Nat) := [(1, 3), (1, 9), (2, 3), (2, 10), (8, 9), (8, 10)]
def r1sG : List Nat := [1, 1, 2, 2, 8, 8]
def r2sG : List Nat := [3, 9, 3, 10, 9, 10]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_3.map (· &&& dom_3)
def goalM : Nat := goal_3 &&& dom_3
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x9c59fd2f
  | 3, 0 => 0x9c59fd2f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000c0c0000000000000a0a
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

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
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

def dom_4 : Nat := 0xf0f0f0f
def goal_4 : Nat := 0xe0c0e08
def roots_4 : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]

theorem low_4 : Lower dom_4 roots_4 goal_4 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0000, 2, 18)] (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0xff00ff
def goal_5 : Nat := 0xec00e8
def roots_5 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]

theorem low_5 : Lower dom_5 roots_5 goal_5 5 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_6 : Nat := 0xffff0000
def goal_6 : Nat := 0xfeec0000
def roots_6 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000, 16, 18)] (by decide +kernel) (by decide +kernel) low_1

def dom_7 : Nat := 0xffff
def goal_7 : Nat := 0xeee8
def roots_7 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

theorem low_7 : Lower dom_7 roots_7 goal_7 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0, 1, 5)] (by decide +kernel) (by decide +kernel) low_3

def dom_8 : Nat := 0xffffffff
def goal_8 : Nat := 0xfeeceee8
def roots_8 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_8
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (2, 6), (2, 10), (2, 18), (4, 5), (4, 6), (8, 9), (8, 10), (12, 13), (12, 14), (12, 28), (16, 18), (17, 19), (17, 21), (17, 25), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 4, 8, 8, 12, 12, 12, 16, 17, 17, 17, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [3, 5, 9, 3, 6, 10, 18, 5, 6, 9, 10, 13, 14, 28, 18, 19, 21, 25, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_8.map (· &&& dom_8)
def goalM : Nat := goal_8 &&& dom_8
def NN : Nat → Nat
  | 5 => 6
  | 6 => 5
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xd6f33033b9bdbc07b23af57d64d4803332f633fb141aecf1
  | 6, 0 => 0xe40c141bc5159104be3fb9245299e96d30706e42
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccccccc00000000aaaaaaaa0000000033333333000000000f0f0f0f0000000000ff00ff000000000033003300000000000f000f000000000000ffff
  | 0, 1 => 0xffff000000000000fffcfffc00000000fff0fff000000000ffccffcc00000000ff00ff0000000000f0f0f0f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xdc98766d987626d9876160d965450d76435dba8766
  | 6, 0, 0 => 0xdb9876609876050d986550d97645da98766
  | 7, 0, 0 => 0xd98765
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 28
  | 6 => 28
  | 7 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x78038007ffff87e3c67f1fc1ff1fc18703c07f003fff
  | 0, 1 => 0xffc000fc3ff8fc3f80e03e78e03e001c3980
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x48d579278a8fb72a8662c66d0dc1db05008200c049001fbf
  | 0, 1 => 0xffe040ffffffff3fb6faff7df23e249d3992
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 24 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 24 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 14 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 14 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 14 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 14 then wireAt i else 0
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
  | 4 => 8
  | 5 => 36
  | 6 => 19
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xe9818af8e8a03effac05225e9ba675cd4f8b6766158632870c54e2630316dd3a
  | 5, 0 => 0xe331931ce0bddffae00c76efd75027cab40d1bbcb2f5d8ecac0a677dac05225ea7119e7f9b7060518f8b54608dd3c3f081ea162e7ecfa18378748e07778bc36575e14c786baa581362b9685c5e1d4aa85d63e9705562483a537bfbe74f3cfc264ca624074279fe8d1f6c5e8b1b8a7ef11ac7d7cf186f73eb172f56660ad7cab808fdee1308dabbe6074368e8034963b1
  | 6, 0 => 0xe0bddffad0f6fc56d051f507ce00c9b9c1afdc6dba7741d8b4992a82ac05225ea0508cfd7ecfa1837702c5a9554c825e3a6b8d41276bea4325303d37206585ea1b8a7ef1126b25b70241d3e1
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x14000040000000000200000400001000000c9105
  | 5, 0 => 0x3840000000000010000003144100000100000849100000004021002044000610000001400007000008000021044008110003840000005008400000010000140e10002840000007000000811002144000000200001085100
  | 5, 1 => 0x84000a10000000400006
  | 6, 0 => 0x3000000000000000100000000000400000000000000000000040000400000000000000000000020000000000400000400002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 6 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 3 => checkCutEntry dom_5 roots_5 5 s ws hint
  | 4 => checkCutEntry dom_6 roots_6 5 s ws hint
  | 5 => checkCutEntry dom_7 roots_7 5 s ws hint
  | 6 => checkCutEntry dom_1 roots_1 4 s ws hint
  | 7 => checkCutEntry dom_3 roots_3 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_8 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
theorem z5_0 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 5 → Z 6 i = true := z6_0
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
  scr dom_8 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_8 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_8 roots_8 goal_8 8 := by
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

theorem low_8 : Lower dom_8 roots_8 goal_8 8 := S_8.noCircuit

def dom_9 : Nat := 0x5555555500000000
def goal_9 : Nat := 0x5444444000000000
def roots_9 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

namespace S_9
def pairsG : List (Nat × Nat) := [(34, 38), (34, 42), (34, 50), (36, 38), (40, 42), (44, 46), (44, 60), (48, 50), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [34, 34, 34, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [38, 42, 50, 38, 42, 46, 60, 50, 54, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_9.map (· &&& dom_9)
def goalM : Nat := goal_9 &&& dom_9
def NN : Nat → Nat
  | 3 => 5
  | 4 => 9
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x4b5c3f1e20e1c98b1c3ae6420b4abdc3007e868c
  | 4, 0 => 0x67fe125a65a893284dcb79834b5c3f1e440e8fef41f3d99b40649e8619cb69170969002f
  | 5, 0 => 0x4b5c3f1e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x54545454000000005050505000000000444444440000000044004400000000004040404000000000111111110000000005050505000000000055005500000000
  | 0, 1 => 0x55555500000000005555505000000000555544000000000055550000000000005544554400000000554400000000000055005500000000005500000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc9654d9654cb644a9654f8654
  | 4, 0, 0 => 0xc98655c96535c965250c96540c9624c96515ec9655c976550c6504
  | 5, 0, 0 => 0xc9654
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x36f368007000000ff8c9738f
  | 0, 1 => 0xff0fe8f80f80c77c00c70c00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfffb695bf432129a4049618d
  | 0, 1 => 0xff6fedff6fc4ffffc4e72e40
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_9 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_9 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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
  scr dom_9 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_9 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_9 roots_9 goal_9 6 := by
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

theorem low_9 : Lower dom_9 roots_9 goal_9 6 := S_9.noCircuit

def dom_10 : Nat := 0xffffffff00000000
def goal_10 : Nat := 0xfeeeeeea00000000
def roots_10 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000, 32, 33)] (by decide +kernel) (by decide +kernel) low_9

def dom_11 : Nat := 0x3333000033330000
def goal_11 : Nat := 0x3222000032200000
def roots_11 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000000000000, 17, 49)] (by decide +kernel) (by decide +kernel) low_1

def dom_12 : Nat := 0x3333333333333333
def goal_12 : Nat := 0x3222222232202220
def roots_12 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000033330000, 12, 28)] (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xf0f00000f0f
def goal_13 : Nat := 0xe0a00000e08
def roots_13 : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_14 : Nat := 0xf0f0f0f0f0f0f0f
def goal_14 : Nat := 0xe0e0e0a0e0c0e08
def roots_14 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0000, 2, 18)] (by decide +kernel) (by decide +kernel) low_13

def dom_15 : Nat := 0xff00ff00ff00ff
def goal_15 : Nat := 0xee00ea00ec00e8
def roots_15 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 6 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14

def dom_16 : Nat := 0xffff0000ffff
def goal_16 : Nat := 0xeeea0000eee8
def roots_16 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0, 1, 5)] (by decide +kernel) (by decide +kernel) low_13

def dom_17 : Nat := 0xffff0000ffff0000
def goal_17 : Nat := 0xfeee0000feec0000
def roots_17 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc0000, 16, 18)] (by decide +kernel) (by decide +kernel) low_11

def dom_18 : Nat := 0xff000000ff
def goal_18 : Nat := 0xea000000e8
def roots_18 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 5 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13

def dom_19 : Nat := 0xf000f000f000f
def goal_19 : Nat := 0xe000a000c0008
def roots_19 : List Nat := [0xa000a000a000a, 0xc000c000c000c, 0xf0000000f0000, 0xf000f00000000]

namespace S_19
def pairsG : List (Nat × Nat) := [(1, 3), (1, 33), (2, 3), (2, 18), (16, 18), (17, 19), (17, 49), (32, 33), (34, 35), (34, 50), (48, 49), (48, 50)]
def r1sG : List Nat := [1, 1, 2, 2, 16, 17, 17, 32, 34, 34, 48, 48]
def r2sG : List Nat := [3, 33, 3, 18, 18, 19, 49, 33, 35, 50, 49, 50]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_19.map (· &&& dom_19)
def goalM : Nat := goal_19 &&& dom_19
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x6ba3d11
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f00000000000f0000000f0000000c000c000c000c000a000a000a000a
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_19 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_19 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_19 == dom_19) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_19 goalM u ys) : RunD dom_19 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_19 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_19 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_19 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_19 roots_19 goal_19 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_19 goal_19 := by
    have h0 : isConstB dom_19 goal_19 = false := by decide +kernel
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

end S_19

theorem low_19 : Lower dom_19 roots_19 goal_19 4 := S_19.noCircuit

def dom_20 : Nat := 0xffffffffffffffff
def goal_20 : Nat := 0xfeeeeeeafeeceee8
def roots_20 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_20
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 33), (2, 3), (2, 6), (2, 10), (2, 18), (4, 5), (4, 6), (8, 9), (8, 10), (12, 13), (12, 14), (12, 28), (16, 18), (17, 19), (17, 21), (17, 25), (17, 49), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 38), (34, 42), (34, 50), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (48, 50), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 8, 8, 12, 12, 12, 16, 17, 17, 17, 17, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 48, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [3, 5, 9, 33, 3, 6, 10, 18, 5, 6, 9, 10, 13, 14, 28, 18, 19, 21, 25, 49, 21, 22, 28, 25, 26, 28, 33, 35, 38, 42, 50, 37, 38, 41, 42, 45, 46, 60, 49, 50, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_20.map (· &&& dom_20)
def goalM : Nat := goal_20 &&& dom_20
def NN : Nat → Nat
  | 3 => 4
  | 4 => 16
  | 5 => 57
  | 6 => 189
  | 7 => 145
  | 8 => 21
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x427b86ec28c8f8692432788923a2937a
  | 4, 0 => 0xed358590afcfb2cd9a71815e7dc442d07b0e131f6fbc4db15638731a51bea41a4eb96e914673e2fd44b3630e3ed011d438a1e0ab2ac49ccd26114912064e5e67
  | 5, 0 => 0xef145619eb9e3af4dfedc5e6d7385bcad4b5a7fdcc1fc9ddc148c600b1d856fba62440fba005ad44993634e6948c2553915547f38808a6cc7b947b8074713e0f6ff5420161117c486109b50d5c0e05b85ae34b1f5967c8f757f7673357b44d6e553537e85196b904511c0fe94e4243214e16da604cdc80b64852b38645bfcfc04509be174410cedd429e1923412cd1f83f3f0ba43eeb24bf3492314e317115292daf8990274f272b26d65338256eb4e123cd0d622238c90c1f990ef21e200e6f1b9854751ac1b12116fca8640f76f0040e3ec02402b0f47e028a305401a4edb200c8ca6d
  | 6, 0 => 0x30b3c7d02f653d432f2d39052f15a0e52ec68d272e5c0f322de76bbe2ca26b712b27b74c2ad9fd9b2912a7492750b4f626ac92fa25c97e8025318cf424f25ef2248bcfc623fade1623e65826226df44b219634db20d5617920b75a75208100301fb306791f634b621ee77a8a1e3844ef1c96ea491a984e151a23cbaa1a1f1cf019ba301a18b06729181c0a6c165a143315fc5b6614765d4b126e71011256732f1232479711fd2b13118eca211155c08d1060e963104ef3610ff651070fcb33c20ea8faac0e0550e70ba1262a091999780905f9ab07530e34073a9894051cbd1903f8e99a035b2fd10249a99b01e79c230185b851012a584000ad4279001a4cbd
  | 6, 1 => 0x7b47a4e87af39e807adb64027776a25c76c379d574f8ca7a7481ccfa723a2c70722b1a82710cff026f1deb2a6e24e7616d36e1736b379a1e68a8fa40683fc95b663298d8636e3c6c62c22e4b629d9733618076186165a2a7612c8f335d1cf190592546695770ff1d5711b93d56e8a03d56488c3a552ba96f5372c47953447d0451f6a40d5139dea74ff0f4044f084ed24ecf76c84c7c5aee4c6601af4a932f4e4990919f47c34c8b47340050462000d24619497e45a7f5984502434f446729e64449f59543c469ce41da7966408a3dc7403615813e0f9fc73d8a3cae3b754d643aba52b6372b333936d58aee347c735e33a95ef332e16b8931968b4130cca4c4
  | 6, 2 => 0xf1a59475efd9603fee71c1e8eafba6c3e4cd485de07b344edf3d5635d9840b17d97fc822d26e2c13cfaaeb5dcc47d1c0caac816ec996b3b6c63e6ab8c5895fa5c5736c6ac4ee7d33c1711256c128b4b5bec2b53cbeb14ce4be9af3a5bcf6ec4abb779f5ab7dce78eb7d36574b561d715b4a147fbb3163514b2a6c045b2516d61b2118fd6b03615abae45c213ac06f897abc4c2b8a8f0d2eda265fcc7a1a0667fa17eb990a00ee0399d770c479ad8f9be993a7ae397708ba596ced85295b93d769551aacc94ad81c79293260c92002a6a8d869bbd8d6b37518c51c71387b2ceb4871506e9856dc6bd83b100457f59c8ed7c039c0f
  | 7, 0 => 0x4305883642f65e654214fad141d9fb7841a4b5d6410d76964079af63406ac2fa3ee6de3d3e4ce77f3d6d0b963d21e10c3c21f90f3b0516443a8b9b213a305add38ad846e37f1b876359f67e73555b61734a8e39d34746a9f32ba82ac3255c7c33129ad3f302ca7772f790d942f62b4552bc53b522ba0a43a2b81626d28a4a83e2866511f26396ad423e92d1222c735132219ec0a21a5f9682014c6441f3d31db1ec21db31c1ffead1bde45011b8548e61b52f33219b1d448196672e116a61199153eaa1814121a0c12b8884a123247970f60b9f30e7dd0190d61f2fb0d52c9a60d166eba09874f3d08d6f02606ecbabd06b07a0305869eb10291d00a01013f36
  | 7, 1 => 0xbbec3344baa8a17cb59a84ddb3feb3cab1b17014b03d009fada32de2abbe6e52ab681b8ea98c5b5da8e78fc4a840633ca6910249a3f2435d9f84ffc39d3508f49b71391a9b1dd7b09a36658d97a4f387954adec79351acbb90f70fa98e7679718df2ab598d5eaaf98aeb8c5a8a81f0ca83f048fb7e77018b7db173387bf0d3337a58579279e15a2877d135d0721cd8336f69601f6d9b14bb6b6909ce6b46b4d16a7ff668679d352a63669d9561aa3368602f2d625d7bf2db5d534c235abc6cf25916f562567ee6cd5640306854ed1c755342fdb7514aca6d51099cc650c4b4ed50b58b1c4f0fba7a4e2ce2974e1db72a4c4c79c449e125c64980ebae48e96027
  | 7, 2 => 0xf9acd0faf053c1fdee22ff53ec164c1ee7fca500e73f702ce72fe7a7e575a6eae1283faae07b344edf63bcb2d970baf0d89aad76d58853adc9f2a206c44be902bc545819
  | 8, 0 => 0xc2afde01abccd6f4a6563cc3a1f16def7e1a8a56764e5f61705b5d9f5fbac6fd5cde0cce55df5df85059633d4f8c57c234064f6c2efbd9641b78d4bc1561a43a15527a691142fa410e7e151305169eb001bed059
  | 9, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3f003f003f003f00330033003300330011001100110011000f000f000f000f000500050005000500030003000300030000ffff0000ffff0000555500005555
  | 0, 1 => 0x30303030303030300ff00ff00ff00ff00ff00ff00f000f000ff00ff00cc00cc00ff00aa00ff00aa00fc00fc00fc00fc00f000f000f000f00055005500550055
  | 0, 2 => 0xf0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a0e0e0e0e0e0e0e0e0c0c0c0c0c0c0c0c0555055505550555050555550505555503330333033303330303333303033333
  | 0, 3 => 0x33333333333333333333333333003300330033003300330032323232323232321515151515151515115511551155115511115555111155551111111111111111
  | 0, 4 => 0xcc00cc00cc00cc00c8c8c8c8c8c8c8c8c0c0c0c0c0c0c0c0ababababababababaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaa8aaa85555555555555555
  | 0, 5 => 0xeaeaeaeaea00ea00eaeaeaeae8e8e8e8e0e0e0e0e0e0e0e0cdcdcdcdcdcdcdcdcccccccccccccccccccc0000cccc0000cc88cc88cc88cc88cc33cc33cc33cc33
  | 0, 6 => 0xeeeeeeeeeeeeeeeeeeeeaaaaeeeeaaaaeeee0000eeee0000eeaaeeaaeeaaeeaaeeaaeeaae0a0e0a0ee88ee88ee88ee88ee00ee00ee00ee00eaeaeaeaeaeaeaea
  | 0, 7 => 0xf0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f00000f0f00000f0e0f0e0f0e0f0e0f0c0f0c0f0c0f0c0f0a0f0a0f0a0f0a0f00ff00ff00ff00ff000f000f000f000
  | 0, 8 => 0xfcccfcccfcccfcccfccca888fccca888fca8fca8fca8fca8fc00fc00fc00fc00fafafafafafafafafaaafaaafaaafaaafa00fa00fa00fa00f0f3f0f3f0f3f0f3
  | 0, 9 => 0xfef0fef0fef0fef0feeefeeefeeefeeefe00fe00fe00fe00fcfcfcfcfcfcfcfcfcfcccccfcfcccccfcfca8a8fcfca8a8fcfc0000fcfc0000fcf0fcf0fcf0fcf0
  | 0, 10 => 0xff01ff01ff01ff01ff00ff00ff00ff00ff000000ff000000fefefefefefefefefefeaaaafefeaaaafefafefafefafefafefafefafef8fef8fef8fef8fef8fef8
  | 0, 11 => 0xffc8ffc8ffc8ffc8ffc0ffc0ffc0ffc0ffaaffaaffaaffaaffaacc88ffaacc88ffaaaaaaffaaaaaaff11ff11ff11ff11ff05ff05ff05ff05ff03ff03ff03ff03
  | 0, 12 => 0xffeeaaaaffeeaaaaffee0000ffee0000ffeaffeaffeaffeaffccffccffccffccffccff00ffccff00ffccccccffccccccffccaa88ffccaa88ffcc0000ffcc0000
  | 0, 13 => 0xfffcaaa8fffcaaa8fffc0000fffc0000fffafffafffafffafff0fff0fff0fff0fff0ffa0fff0ffa0fff0aaa0fff0aaa0ffeeffeeffeeffeeffeeeeeeffeeeeee
  | 0, 14 => 0xffffc8c8ffffc8c8ffffc0c0ffffc0c0ffffaaaaffffaaaaffff0f00ffff0f00ffff0033ffff0033ffff0000ffff0000fffefffefffefffefffcfffcfffcfffc
  | 0, 15 => 0xffffffffccccccccffffffff00000000fffffff0fffffff0ffffff00ffffff00fffffafafffffafafffff0f0fffff0f0ffffccccffffccccffffcc00ffffcc00
  | 1, 0 => 0xfffffffffff0fff0ffffffffffccffccffffffffff00ff00fffffffffcfcfcfcfffffffffcfcccccfffffffffcf0fcf0fffffffffcccfcccfffffffff0f0f0f0
  | 1, 1 => 0xfffffffffffcfffc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x7264513447e614f3747e6c46374726452334
  | 4, 0, 0 => 0x7e56463f37572653f2f2b5807264523457e6c564a37572564c302e57e72645034572564c302f57e756c4e2b57e75644f3757e6c462b2257e75694f2b57e6f563f3757e726c453756e563f2b2157e756c473757e613f37315
  | 5, 0, 0 => 0x7e7570563f37686726c3b2b2267e726c47372267e7264433f3467e75693f312b67e725f433f37672563f34332b67270563f2b2167e75564e3f2b67e75564c372d67e56463f2b2267e7264523f346007e564a3f3757e75564f372b67e7256453f3767e56533f372b6
  | 5, 0, 1 => 0x8572583f2b2267e726c4e2b22680725652342b67e72644f372267e726d643f3767e756c472b226846c56492b2267e75563c372b67e72694f2b22681726c472b2267e756c564c3767e564c4a3f3767e6764563f376007e723f282257e72643f340667e564c4943376
  | 5, 0, 2 => 0x7e6c564a2b2267e72705d3f3767e7256544c30687726c472b226007e72392b225007e7264341757e725d4f372b67e72643f282267e6f563f2b226008672643f345007e72564c1b57e726c452b2267e72573f2b2267e72643f34326007e756c422b57e726c6443376
  | 5, 0, 3 => 0x7e7556473f3767e756c38372b67e726c42372b67e72564c301b6886e563f2b2267e7270564c306007e7256300f57f726c472b226008072643f345
  | 6, 0, 0 => 0x807256482b2267e7262563f37227817256473f2b227007e2b22170e0167e726c5643372b77e75563f372b17784564c493f2b22785564c493f2b2277e72563f2b221077e73563f2b220677e72563f2b220577e72564f372b2277e724d4c3f2b2277e7270564c252277e726d563f372b70072563f221f1e6
  | 6, 0, 1 => 0x7e72221f170e67f564c493f2b2277e7256403f2b2277e72564c372d2277e72563f2b22127008572563f302b6007e74562b221768672563f2b220677e72563f2b220f77e72564c43372b77e725a563f2b2277e7556473f2b22700723f2b220e0c67e72563f2b220a77e726d563a2b227007e723f2722066
  | 6, 0, 2 => 0x8472564c252267e726c56542b2277e7256453f2b227008572564c252267e72693f312b2277e72563f2c2b227007e7556423f2b67e725b563f372b787726c643f2b2277e72564c433f3777f72563f2b220477e726456433f377007e3f221f0e0167e756c563e2b227007e3f2b220e0067e72564e3f2b227
  | 6, 0, 3 => 0x827256482b226007e7256342b176007e72564c252067e72563f2b221677e726d6c382b22700007e72564c3057e75563f2b220b785726c643f2b2277e72544d3f2b2277e72563f2b242277e72563f2b22027007e726c38221f67e7270563f37227007e67563f2b226807270563f2b227007e564a3f2b226
  | 6, 0, 4 => 0x80723f221f0e67e7259563f2b2277e725f433f2b2277e726c564c372277f726c643f2b2277e75563f372d2b77e7264433f272277e72563f2b22137007e563f23221f6007e56493f221f6007e72645d3f3767e7265563f2b22700803f2b220e0167e72564c25220f7007e763f2b220e60080722b22170e6
  | 6, 0, 5 => 0x7e725d3f37312b77e72563f2b221c77e564c49432b2277e6460563f37227007e7556372b176007f562b22170160085563f221f0167e7269563f292277e7570563f2b227007e72563f2b1967e7265563f302b77e72563f2b221577e72563f362b197007e562b20170167e6960563f2b2277e72563c372b227
  | 6, 0, 6 => 0x7e7756433f2b2277e756c564c2b227007e756c382b2267e726c643b2b2277e564c4a3f2b227008576563f2b2267e6764563f2b227007f7256221f176007e563f201f0168072563f2b22067007e726c422b2268072563f2b220f7007e7256201f176007e752b22170e67e725c563f2b2277e66563f372b227
  | 6, 0, 7 => 0x7e75563f2b220f77e725d563f372977f7256473f2b2277e726c64432b2277e725652482b2277e72563f2b221177e725d563f302b78372564b3f2b2277e725d563c2b227007e72563f2b1a67e726d643f2b227007e76563f2b20686726c643f2b2277e7060563f2b227007e753f221f0e67e756c563f372b7
  | 6, 0, 8 => 0x7e72706c382b227007e72564c30226007e7256482b206007e72642722176007e723f2b22076877270563f2b227007e7a563d2b2067e7270443f2b2277e706e563f2b2277e725648432b227007e79563f2a2067e7268563f2b227877d72563f2b22700723f2b220e0d67e756a563f2b227007e72633f2b206
  | 6, 0, 9 => 0x7f7270563f2b2277e72564c432622780726c643f2b2277e72563f2b220377e72563f2b221977e75563f372b1877e72563f342b1a70087726c382b2267e7256423f372b77e726c43412b227847270563f2b2277e756b563f2b227007f60563f2b2267e60563f2b220677e7556543f372b7007e60563f2b206
  | 6, 0, 10 => 0x7e7256544c252277e7271563f2b227887270563f2b227007e726c382b206007e7564563f3767e765d563f2b2277e6c564c492b2277e60563f372b227007f722b22170e60085723f221f0e6007e75563f2b1867e72705d3f2b227007e722b20170e6807264563b2b2277e75563f2b220477e75563f38372b7
  | 6, 0, 11 => 0x7e726c644c2b2278672563f3b2b2277e7256473f372277e726c38372b2277f72563f2b220f77e7270563f2b227007e726c472b2267e6966563f2b2277e72563f2b221a77e726c382b221f7007e72382b22046007f726c382b226008456493f2b226
  | 7, 0, 0 => 0x7e72563f342b67e72706c563f2b2287e797256433f2b228007e72563f2b220f700857972563f2b227007e724c3f2b220e7007e7c72562b22177007e72643f2b220e700007e563f2b2322600007e56493f2b226007e6460563f2b2277e7d726c563f2b2287e72563f372b22178007e726c3f2b220e77e72563f3d372b22800007e7c553f2b226
  | 7, 0, 1 => 0x87726c563f2b227007e723f2b220e09700007e78563f2b226007e72563f2b22087007e56433f2b22017007e72563f2b20017007e7256423f2b227007e7256432b22177000085563f2b22016007e7972563f2b2077e727064563f2b228007e725e563f2b227007e72563f2b2a207007e723f2b25220e7007e72563f221f1d7000080723f2b220e6
  | 7, 0, 2 => 0x7e726c56433f2b22800807c72563f2b227007e72562b221f1770085726c563f2b22700007e75563f372b67e725d563f2b22178007e7256433f221f700007f563f2b22016007e75723f2b220e7007e72562b22170e700007f72562b2217600008572563f221f6007e75563f382b2277e7264563f3b2b22800007e563f2b2001600007e72562b20176
  | 7, 0, 3 => 0x7e72563f221f17700007f72563f221f6007e726c563f2b2077e725d563f2b220887e72564c433f2b228007e72563f362b2277e726456433f2b228008472564c3f2b227007e72563f3d221f7008572564c3f2b2277e72563f372d2b22800857264563f2b22700007e72563f201f600007e753f2b220e67e725d563f2b221f87e726d56433f2b228
  | 7, 0, 4 => 0x7e72645d3f2b227007e7256553f2b207007e72563f2b252077e7b7256433f2b2287e72563f37352b228007e726c5d3f2b227007e563f372b220177e7264563f2b22178007f7264563f2b2277e726c563f2b221f8007e7256372b221777e7264563f2b22068007e72563f2b22047007e7264563f2b207008572563f2b25227007f726c563f2b227
  | 7, 0, 5 => 0x7e75563f3d2b22700007e562b2217016007e726d563f2b227007e7a72563f2b2077e7264563f372b228007e726c643f2b2277e725643413f2b2287e725654433f2b228007e7972562b221777e726c563f372b22800007e72564c25226007e72563f37221f7008072563f2b221f7007e72562b2217147007f7256553f2b227008072563f2b220e7
  | 7, 0, 6 => 0x7e72563f382b221f8007e64563f2b220177e7256543f372b228007e725b563f2b227007f72563f382b227007e6c563f2b22017000085723f2b220e6007e72563f382b207007e7256433f372b700007e563f221f01600007e563f2b2200600007e7256221f1767e79726c563f2b228007e75563f2b22177007e72563f342b227007e725d562b22177
  | 7, 0, 7 => 0x7e79563f2a2267e7264564c3f2b2287e7c7256433f2b2287e72563f38372b2287e726c64563f2b22800007e72633f2b2267e72563f372b22188007e7264563f221f77e726d6c563f2b2287e725d563f2b25228007e7256543f2b227007e7256473f2b227007e72564b3f2b227007e726c563f221f7007e75563f3e2b2277e725d563f2b29228
  | 7, 0, 8 => 0x7e72563f38221f77e72563f2b221f17800007e722b22170e6007f72563f2b22177007e72563f2b201f7007e7564563f2b2277e7256544c3f2b228007e72563f2b20177007e7270563f2b227007e756c563f2b22700007e75563f221f600007e72563f362b67e75726c563f2b22800007e7256482b226007e7264563f37227007e72563f2b22187
  | 7, 0, 9 => 0x7e726c382b226
  | 8, 0, 0 => 0x7e726c563f2b227007e72563f221f6007e563f2b22016007e72562b221767e72563f2b220177e7972563f2b2277e72563f2b2a2277e72563f372b2277e72563f2b272277e72563f2b221f77e72563f2b22177007f72563f2b2267e72563f3d2b227007e72563f2b2067e7256433f2b227008572563f2b226
  | 8, 0, 1 => 0x7e72563f382b227007e75563f2b2267e7a72563f2b2277e7572563f2b2277e7264563f2b227
  | 9, 0, 0 => 0x7e72563f2b226
  | _, _, _ => 0
def stateW : Nat → Nat
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
  | 0, 0 => 0x1f07f1fe0ffc7c1847f830f1f0611c20c000c07c0f80ff0301f00203c00c0040f800f00fff001fffc03ffc007ff0
  | 0, 1 => 0xe3181e3e303c7c1fc7f83ff1f07f1c00c007c1fc0000f01f0001fe003c701f87003f01c0601c00c007c1fc7083f0
  | 0, 2 => 0xe319fe3e33ff806038f0c0f0001e03c03fc000780000f0ff1fffc23fc38ffff80fff0ff1e1ffe3c3f8ff878fff0f
  | 0, 3 => 0xfffe1ffffc3ffff87807c00e0f80e01f000739807f730fffffffc3ffc3ffffff0fff0ffffffc3ffc3fff87f0ff00
  | 0, 4 => 0x38c6078f8c0f00fff03dfffc000000f000f000000000003ffffff0fff0
  | 0, 5 => 0x38c67f808cf00001e00003c0000000000000000000000007c1847f830f
  | 0, 6 => 0x1e03c03fc000000f000f0000003c0000000000f000f00000000000000000000000000000000000000000f000f
  | 0, 7 => 0x1ce601c1cc00700007000001c0001c000000380000700000e00001c0000380000700003e1f03fc3fc03800007000
  | 0, 8 => 0xe1e001c3c00000000000000e00001c000038000070001ce601fdcc3c038000f700f00e00001c0007f9847ff30f
  | 0, 9 => 0x1ce601c1cc00038780f70ff00e00001c000739f87073f01c01e1c003c0700007000001c0001c0000073980707300
  | 0, 10 => 0xe3f81e03f00383e03807c00e0000e000000739f87f73ff1c0001fc003c739807f730f1ce601c1cc0073980707300
  | 0, 11 => 0xe0f80e01f00383e03807c00e0f80e3df03f800038f0000e0000e3c003ffff87f0ff00e3f9fe03f3c38fe078ffc0f
  | 0, 12 => 0xe0000e3c003f800038f0000e0f80e3df03f83e7b807cf0e0f80e01f0038007b8000f0e0000e00000380003800000
  | 0, 13 => 0xfc000fc00003f0003f00000fcfe0ffdfc3ff3f83f07f00fcf80fc1f003f0003f00000e0f9ee3df3ff8007b8f00ff
  | 0, 14 => 0xff000ffe0003fc003ff8000ff000ffe003ffc603ff8c00ff061ffe0c3ffc003ff8000fcffeffdfffff3ffbf07ff0
  | 0, 15 => 0xfffff00003c3ffffc000000fffe0ffffc03ffe03fffc00ffe60fffcc3fff983fff300ff01effe03c3fc003ff8000
  | 1, 0 => 0xffffffc1fc03fffff807cf0fffffe01f003ffffc7073f0fffff1c003c3ffffc707300fffff001c3c3ffffc707300
  | 1, 1 => 0x3ffffff07ff0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x703306e066c140841a010a0000000000000c04c09809902010002020004004080008007ef000fdfc01530002a60
  | 0, 1 => 0x2108123010303c1dc3b83bb0f0770e80ca83c1dc2982b90f0330ee066c381d83383b30c0640c80c88281502082a0
  | 0, 2 => 0x6319b63633758462d8d0c5d6319b6363375084690188d14a15c4822b810957100aae0250a1278143884a848c150e
  | 0, 3 => 0xb5aa1b79543ad6a86cc540cb0a80b115012d6a86de550ed2918d0323026a15260c2a090d4c901a98242002404000
  | 0, 4 => 0x40508400a1002111821223108444080888094a8c9f151f257ef27cfdfc94a8c9f151f252a327c547f6b57360eae0
  | 0, 5 => 0x2d6e7230d030b5b9c3b333b0c6640c8cc892957921aaf14a55e486abc5280412180804050a404a145154a51a294a
  | 0, 6 => 0x6f7ff6fefffdbcacdbf959f6f0106fe020195ead9f3d5f657ab068c42981e29853c5560788610f110b5b9cbf373f
  | 0, 7 => 0x9ce649c9cc8a728827251029c8009c900027399272732298e44981c8825388252710293e13927c26643802407000
  | 0, 8 => 0xdaf5ed87ebc76a84b61d091d4f2ad4de54f43c23407840bdee7bfddcfed7a8edf751fb0e80b11d012779967a732a
  | 0, 9 => 0xfcfecfd9fd9bffffffffffff0f88f11f1137bdfb73fbf3ded5edcfabc77a8cb73d193de810dcf020373db3727b62
  | 0, 10 => 0xf0f88f11f113c3e23c47c44f0800f110003fffffffffffffab3fff567ff7fbfff7f7ffdfefffdfdfff3fbbf77f77
  | 0, 11 => 0xf8fcef95f9d7e3f33e47e64f5fabf7df57fd742bdf6851f5aa3f7d547fc3e23c47c44f2f98f13f313c7e27cc7c4c
  | 0, 12 => 0xffab3fff567ffe043ffc080fdfefffdfdffebf7be5fef5faf98f97f313eb57be5eaf1faa92f975257ea043e5c080
  | 0, 13 => 0xfeab2fdf565ffa043f7c080fdfefffdfdfff3fb3f67f66fcfa8fd9f51bf2a83f65506fffffffffffffffffffffff
  | 0, 14 => 0xffc56fff8ac7ff153ffe2a0ffab3fff567ffe663ffccc4ff831fff062bfe043ffc080fffffffffffffbffbf7fff7
  | 0, 15 => 0xfffff4a6abe7ffffc080008ffffcfffff9bffe63fffcc4ffef7fffdeffff9d3fff3a2ffd5efffabc7ff463ffe8c0
  | 1, 0 => 0xfffffff9fdbbfffffedfefdffffff31f133fffff7bfbfbfffffdefabe7fffff7a7b6afffffda7ebe7ffffe7a732a
  | 1, 1 => 0x3fffffffffff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 46 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 46 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 137 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 137 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 137 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 137 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 3 => 8
  | 4 => 81
  | 5 => 461
  | 6 => 1416
  | 7 => 762
  | 8 => 16
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xf8ae641bbc4c35c55c1ac5955b209a214721a6be3dca836f2985bc0800b2f9c9
  | 4, 0 => 0x9beec7b89a6ecd579742ca678a8313198a1429ef88b68cd485caacc3832dbcf882340df180ac15ed7c95e90f74e3457873d07a7071cec2cf6e9997d76c8747c06bdcb0fc627f712d5d39e9e55ac4e25c5928c0c7566b6bde55b6786c54603670520e71af4bad52344a2fe17947674d243da67a7b3c9d1a26361d632635de7fb230e0a6cb3046f6a92e5c0f322a4f4e342a07b9fd28ca73a828465416280b675e26dbd0d22579821924a70cbc2392a86421ead25c215c1b5b1f82fde01a695e721923405e1897742214d09f0c136a3a89131bc49d0f5fc8270e5deb580bc1ff4b0ab6917e09cc3f2c076b4f8f05a907a0046ce25f0323e0c402b0f47e024f06e4
  | 4, 1 => 0xecec2f6eec2a4e25d4e86f77d26c44e6c1b84b34c1b17122baac0953b65116fdb4eca652b2fda70fb21c7b02afffce9cafcdd183ab2d2d9ba5f32fb89e99d3c39ca96a46
  | 5, 0 => 0x1056a0981037e4da0ff6260a0f82e1070f2d99e20ef402390eb6ddbe0ea8faac0ea7e5180e970a1b0d9467350cc79e370c8b5f720bd5dce90bc50b0e0bb0d3750b931def0b7673f90b2972550b13235e0acfdc4c0a70ebbf0a6c0c690a17ef7c09f4089109d0c57e09a4d5d909874f3d09708bb40929aafb09231bf508cc385608bc39d808b04fcd088521e20839a93f07d12e4b078d1ffb0786f8530770d02b07514ebe072cba91065359c005f5ca2505f5b00605f303c305b120a005834a29045412d00414a35503b36b1002ce271e02c2100602020cbc01aac27e01aaa9db01a460bf019be1010121694f01013f3600e3221d00c90be300ae07c5005de734
  | 5, 1 => 0x2889f3702884fdf82876f33f282acc222804e62727df7ea727c5a4fa27c014b32730c129270f2864264006cf25e70aac25c97e8025a66e5825a088ed25654b3824f25ef2248ba27c23e92d122253aeaf217c18ce21787c5321483e2b206d0bcf1faae4fb1f6e78e51f039e2d1e4593561e369f991e0dc9541dcf29111d9825571cee21221cc827721c2546331ae1c6821abf35371a92901418c1be6718ae189c188f92a4176d640f17603fa516e4e24316aa715516716f5b1658630815dac5e915d62e6f154a08e5153eaa1814da200913b4ed4c13b1e74c1389877213396fbd1279306c11f91a67119dfe101198233a113bb99110dde01a10d9d92a1098c65a
  | 5, 2 => 0x3f24a24c3de6527f3d71302a3d70d0a03cbf50053c620db33a9533273a8367283a06e07e396c4729390de90538e1164638d74e773837847737ee12d5377ab9dd3766628737435cb836f4147a36b28f4d3693090835ee51be35e7ff763584e758355d2f113525813d35194c0334c436cf34a8e39d345dd54c335802fd3307ff5732f60ec632f3cfb5328fede531a604fe30b3c7d030531a682ff968f32fb52baf2fa027f32f7d17312f1b21de2ed840982ed097dd2ecdec932e8cbb092e5c0f322e0369bf2dc127c62d1327702cf7fbf22c3803702be9f1092b6cad512a1fc85a29dd861a29cc158e29c61d0029acba03296525cc2961fe4728f6cd9828b0dc0f
  | 5, 3 => 0x584a41b75843178b57f40a8357f0039357c9f04557359e5555c8d7ad550de69c550ad34d549d174554763daf53862020532d8d755318541d52d074c252b420d5523ede1551b999db5198e0a65141b818513145914f0d9c4b4e2dcec14e29c7d14e0610dd4dd8e4694cc753b74c56afea4c32c98e4b5f5c8c4b24895f4b040f154ab09eb14aa59fc74a9dd6174a99fced4a87be8a4a6f824f4a4cd1d24a1b7e2849f4945049c73ce34874c8ec480714fa47fe89d947baec8d47b4abff4784fce4471c98aa4712aa554641a39d462397f545a182e444f229b143ab0e6e439d85cf4347b02e42b779a34294381141c1c8b24183f38740fee992400aef7d3fdedec3
  | 5, 4 => 0x81fbd7c4818040d78128aa138080aeba7f7b54597f75cfc87ef79a577d8ecad87d6d960e7cca1c587c0a93c47bfbc08e7bbb12ac7ba6ee947ac206ad7a1d4edb79e6d4517836dae377be57fd7746be7b7742489a76ab95f1764d00717441f702732463e771a7a8896f9408c46df703a66be4b38f6bcba0fb6b1e69b36b09813369a8b798699cbe1a696d75e7695bbee065cfe10f657fa726656db31b63d0905f63669d95629573c2622b535d61f5a73b61eae8ca61b2a2b6618a6a10605a49425fec3b125f97089b5e9ff2d95e3d1c7e5e1834e35d6c69ff5d4d264d5d0d93e85ccfbc495bf897c85b796d4759eb055759b6e3935948d9c5593af06c58a7e316
  | 5, 5 => 0xad479927abba794eabaec14fab960c9caa6b0629a8db08d3a84f5f0fa8112672a80c1737a69cd3fda6183c91a5e6fd54a58443aea3d373cba3a9d24fa2630bc3a24844b2a1fa18a9a1bf6e64a0207bb09ed753839dc5dfd09db96fca9d5e0e199c8da2cc9be530079aa5a4549a69453999c92521986cdbad97c8952797716c839762f36a9736b29e96d52c1d9694461e968281c394fa15419447385d94006bd193da724593c46db193660c509333a623915eecb990db024b904fe3d1900f813a8fbd53048da12d178d96037e8d4552f28bc776c58b8bf21b8b17d437873eb5d787194e578663b3ac857036be84670fcc845a0eec844e44c0842c50d48214c699
  | 5, 6 => 0xe2ea498fe24ee520dff65054df3d5635df377c0adebafc51ddf2197bddd3ac13ddccfc77dc9b356bdc1ed1a4dbc3afcbd8d7c2ffd89aad76d8827e37d832dd31d7acb1ccd6c6d6abd5c34bbcd4de3103d418da8dd3ca9cbad1941c87d06e5c96d05b35c7cfc1d305cf2180a7cebf7783ceac14a7ccbad65bcaac816eca872ff9c9f2a206c9bcfde8c945fe97c858f251c75137bbc7163729c6657778c50cab75c509d065c4122956c2568367c2427d6cc194ef38c0db3e37c027168ebca3166abbec3344b83eefd5b5ac93d1b57d2449b542871cb4e3f2bfb411607db3542d0eb2820acab2479df5b140d322b0ccaed7b09ef93cb065425bb03d009faf8c880a
  | 5, 7 => 0xfacb9691f9acd0faf79316e9f5f0bc99f3525b3befa77ca6ef1b2183ec499b3dec2a4e25eb76cf01e6c0d55be47475f3e417b86c
  | 6, 0 => 0x680b92c06743d31065eb57006432260063e91720636e8f6060f596e05fd0f1105f2ecc205e77d7105a47d0105687e890555b2b9053cd7d1051f1fac05169eb00512d18904f7559904bca65904b26b680479bbe104572614044a0e720425399003f7cba003f3df9703dcabd40362bc2b0341d11b033a727c0334643b03087e040305421302f1f85902d6a72e029bda2f0298285b0293b452028da25d0289e808027154fb02664004025cb66602102cb901e3cad001bed05901ad4403019c9fad018309d9017f3bda01752afa010ac531010ab0bf00f94cd000e5264600ba50d800a28bea006c2684005de7340046618f00296567002677b2001688d50014cd4c
  | 6, 1 => 0xd9dd24c0d82e74d0d6e8d170d6a3eb60d166eba0d02db730ce64aca0cd4b54f0cd412060c8b5f720c8a4ae10c60dcf80c3486130c3193340c0ba5d40bc7415d0bb03e4c0ba8521d0b8ad6cc0b88cc090b53d07a0b2a386d0b05d34b0ac4d5b90aa9c2c50aa03d900a72fa560a5f1f610a3ff7660a2d481b0a2a32ae0a01f69909e6e15909874f3d097689a8093e7356093a1b9a0938390c090dfc84090241a808fadadf08fa445b08d6f02608ba381d08b0816608a3620f084ecf140848694b0815b7f907e99e2e07b1fadf07a676fd074eba940743e463072f1b2107253e8a0715437d0715311406fe4f3806ea8bca06cbb1b406bd2d1e068d7fe10681af19
  | 6, 2 => 0x1368b3e213347fe713346ed112ea1c2e12e05c4012cd450012a888d212a3a5671261bfd8122a38191223d65a1223d25011fced1511f373c011eac26e11d4f79211d2b8bb11be491311bcb75211b4bd5b1187183a117e956e116b47241142fa4111408e9a112506a8111de81010dec6f910bf6ca610aeb074108ef5b9106f8d041065fc18105e2d191058a21910522123102d8cd3101fadf4101f34a210060e321004efa20fec104b0fda9e160fa65f9a0f9550a90f78ea770f76f4eb0ef5fe8c0edffd230ed3e0d70ecdeef30ebcf9d50ea887730e7e15130e737a980e67dc250e60a3ca0e19e1cb0e1294ff0df70cce0dcab45d0db839750db432850da0170a
  | 6, 3 => 0x18ef4baf18bf975f18ac994f188affa9183355481832270d18260451181e4c1818103f88180c2da517ce2ba217cb86b117b29b55176fbdf7175e5052175a929b17135e9f16dbf17016b01e5416987722168069d11673385e1665ef1c165c2d5c164f38e016446b9c16424e121611817416100cbf15f0607615badb7e15a1e10415776f951574b12d1561a43a155ed0bb155db13d1554b92415527a69153eaa18153802db1535fac81517feab14fd70f214fa8ddb14e6b4ae14b29a231499cfe51474608f14696ac21436a4701422b86f140b2e6e14009f0a13fdbe2913ea83c213e231c613e1552d13dbc3bf13c7990313a8775c13967e2f139302bf13728f56
  | 6, 4 => 0x2256b04f2213883721d8db4721ce372521a4509b216990eb215e4c98213bddeb212a86b020f72cf120ed435e20dff92e20df647f209b7f3020819f3a207965cb205cc8cb205b0a2a204b60b61fde0f001fb72b911f6fbf471f59336e1f3108e21ee50e861ecbe4b41ea7893e1ea60e4c1e2713961e1a72c21e033eff1db4e0681da4ae0b1d940b681d75a3ee1d51061c1d35f1f81cf34cfd1ca0b1831c6af0321c397d011c2546331ba367651b8548e61b78d4bc1b6a04111b45c5b71b35e26c1b27d2611b1a2ca91b14a1741b0bab3e1a7fa1b81a7bac721a256c931a04d97919ff9c8019f2db1c19e5257c1974603919525df01949528b19468cb71921237f
  | 6, 5 => 0x28b13185289a15a2287a5ebe28668e6d2866511f28610c6c285a61202856d04b28504fb628498f682819312c280a075b27fdb4b527ca04a427c5a4fa27b3f541275958f2273d01e5273a86802713cf0026f72d0626a8a450267b41f5267868632654e04926465937261101172610a0ef25f116f125e45b7625de408525c5c2a22569b56a2568133f2550cf70253d09d2250b3e6a250aba5724cfe814247d56ba2443fd3024425a84243971d5241d3313241a155823fa873323e5cb3323ade268239e1af5237fdc382373cc522360951f2359c6d02353b18e233e6264233e51982335ab5622f4f4a022e093b2229eb02f228b591022734f5d226fd984225d4df4
  | 6, 6 => 0x2fdd75082fd3b15e2fae5bcd2f7a8db12f6745e12f5ca5572f48cad42f3e6dd02f29cd722efbd9642edf397b2ec383ac2eba05a82ea523322e9efc112e3061ae2e2e03ac2e2327552df23de92de6358a2da6f7032d9165262d70a0352d63ee082d618f3b2d6146532d52d1502d19df392d1146c02d06d0c22cef63982c5dadfc2c50c7802c4f91e52c2026e82bf5bbbe2be6404d2bb1f6282b8af0a62b25f1c52b15732c2b0a8d592a97a7b92a76e8352a3198e02a1317a02a121f8d2a0f59b329f0b1cd29e9278e29e11e8129af2b642992b932297c99f82971ba4029342757292c96522920d8b3291d2a9e2911ca7d28fe351428e1d56328c2d85628bda13e
  | 6, 7 => 0x37d4a1c2378e6809377391923770603636d88c8636d7e61c36d69bdf36c9556636b5383e369e286b366fa2723610a03936019e5b35e23d5c35c10950357ada31357321f8354e1e60354de99c353aa3c6350fe1ad34f3ec2d34e12a5934d2fbb734a771a73481847a34417d0f34064f6c33df688433dd474d33d93c6b33a8219a33a21c24339be83033864f1f335d8195335802fd331b439e3307ff5732fee09032ecdd7e32e38d4f326bf53f3241f77231fefd8b31fcd6f731f5eab331de8f8931ae0845318b16ac31808fd0315c08eb31472fc2312ae6df311dfd6a3117e4f430b973d630ad71ad30a9d7c9309ade1b30327c14301c7aab3018e9f92fec250b
  | 6, 8 => 0x4059fe854049cb823fee93873f69bd633f4043ae3f3fbc873f384bf13f3143b83f227ddf3ee66eca3e9a6a8f3e896cb83e6329a03e56ef7b3e4693da3e22c8533e1ce6143e0ad2fb3df99e973df7d4eb3dc47d1c3dc34cb73d820b7b3d7e58413d4e5b033d44b5c43d2c7c353d0b3b903cfaa5163ce925d23cba3bb23cb227733c9ce34e3c9186b63c7b85e53c6b32503c5112f13c3970963c346cd83c2a8b5c3c24c28b3be497a23bdc2ed73b4178103b0db0ad3af9666f3ab95d963a8161553a67b4373a5b11913a4fc2063a3634ea3a326e5739ff1f0a39ddf648394f142039402c7839334aec39264cb738d3d41838840154385204ef37fdfb7837d8b581
  | 6, 9 => 0x4a20e91b4a0e0a804a0a039049fdd8ca49f2e31049eb066449e3bfbd49b6983f498effba49780ea84958591348e193ac48d58fd648c35a8b488161eb487c4b4348603f72484668e54828752047f0cb2247d7f35a46b55adf46a12fe2469949b54639627f45b797dc45913ff445588ab94526b40844f4548e44e5077444d5829944ae84d944ab1cba4497853044623ede4408d56743d8750343ac9409439588c343555fb0433f660a43022bf442fbf37742e28e1442b779a3424d58ad42454fb94210028741ec4f6f41d22c9a41b3665641b00ac74197b05c4194f6a3417d90284170bcbe416e9813412c1b3840f0f80a40c11d8e40936de1408a06cf406ac2fa
  | 6, 10 => 0x545dc05f54499f4154095fad53f59b8a53e591e853bf28c2536b8d0a534afad3533a6d585318541d5290580b5281620b522c1d2d5206faa051cf671751ccc76051ccc13e51954e1e518d110e51501bab51496a925112025150df0cf150b80df750a1bacb505beeb35059633d504c73fe500139404f9d1e774f8c57c24f8b86e64f7141a24f6f0b154e8c86004e65ab694e4388a54e3da7e34def80874db248164d84259f4d6c43d14cf358584cd3d6884ca1aa074c6e0f504c46545e4c1e35cd4b65b90f4b5d9f494b3b99e34b2472944b236a724b11aa524b093b3e4ad762854ab8c3e84aab038a4a9f53ac4a8b09ee4a7b44a54a6c36964a46509b4a4249ab
  | 6, 11 => 0x5d868d205cde0cce5cc77ab85cbdab195c97debb5c79d9865c5ccb105c5551485c266d465c1f443a5bf13ab45be0d81b5b796d475b5c8ab85b4dbe2c5b26580e5b00c4075aecd9575aea31985abc6cf25a9c6dcb5a315df15a197e005a17fce059b9b5c25952f0d859483db5592ae15658f52f1858e6c546589311d4588df5d9588ac935586e2e81582969ea582291a2581a3e36580ad4f357b34ba0578a39a2578012d0576611cb5764b649576054b95742a7955704398356d7ea5656d29d1756b227ca568e1c39567c7f5156485ff955df5df855aa37af55739b7c5530a86c552e1ac455113a3854e3e57954ba54e354b5735e54a96c09547744bc546b2220
  | 6, 12 => 0x67d2ecc667c13f6967a2a106677d8db96752b39f6747b9f2673394256706143966b60782669a488666596eea661dc2cd65ab230365883aeb657d47b965381a0264d90bd964cb1eea64b23f0e64a3ed3364a2156b6497fa93644a653164485a24642e54a063939f336328b5ad62da87e162d4bd2362bf39f9626898c06264afc162623a35624cc79962261eff61fc0a4c61f5a73b61f427ee616fe8b461660cc0613f4bb660f47f6c60dc0ef760a7ce4460a08da7608dac1f60774438602f2d62600ad1db6006ca9b5ff9abbf5fc559925fbac6fd5fa001255f4c3dc55f3648d15f35ba935ed6a3f15ed5c2bf5e42f7405e1bc49c5e13ada65dfcd2655de4c8b2
  | 6, 13 => 0x73018d4f729c25ac725e95e77220008971ff734971ca317b71c79575719e7521717a23367137bf1c711820f570a415bc707b93f8705b5d9f705155297037bb13700bf4506f9a15cd6f9599c06f1715236ee0d4f26ebb13b06e97376a6e3f00b06dbbe1966db3cd8b6d8815996d7b510a6d483b2f6d1c77766d093ce86cf954796cf209256c4fcfcd6c0fb1986c0755aa6bba04806bab48676b9d976b6b91dda16b91c78d6b4b51b96afee7646af4e10b6ac69eeb6ababa2c6a95be0b6a8f01346a3ff44d6a2177b56a0cc1f56a0abb036a08bb05699f003a699c2c4a6992c1b169148b686909685e68f032ac68ab6b95685a494668518872682c83d867eee67a
  | 6, 14 => 0x7af9f9577ac087607abf348a7aaaaa1d7a7382a17a3358537a2bf43679e5550479d342cd79c2eecc79c07342797abaaa79684f62795f3c437951d578794d343579480fd0792c030f78d1319678bfd458788f95117887266f78849c9478761744784337a877ecff3a77e0dac777d135d077ae3ab077abf41377997203776d24f87723c8d076fcecf676e5054776d063dd76afef8876a139dd768e81ea765c7722764e5f617626fba57607603675ee73ad75c13b5b75ace69a75aa6c407597c941756ef7e97556228d751532dd7508768874f94cb774cf39e474c85d0274b1ce5674789e647403934773da4b1a73be3a8b738117497361e71e731a9a37730cc97a
  | 6, 15 => 0x87f2850a87e4b66087648dca8703169686db48f1869c21a686981ab68676ba26864f591485f5891085b60ed48527bd3a84f5077184af188b849aa637849a9d8f848e320d84896c49845a0eec841fb46483d5103283a2fded8362909782e72b3682de711782d80165823f6b27823a9c3e82204782818c8a24817cef808128aa1380d851b5808528c48069eaef806266ad80265a157ff2ec907fbb6eea7fadd4737f8776eb7f57d3697f394fed7f1e33537f00ecae7ed1cb467ec002077ea020fc7e912cbc7e8031507e77018b7e63c5ee7e5407697e4b58517e1a8a567dd747b97d41b0af7ce9266b7c7054c17c2948dc7bc3baf47b82908a7b1fa70a7b045a63
  | 6, 16 => 0x98af20a8988f1cec984afec098249f8697a00225972fe19097012b8496fd835396e6e9c896337734963297ec960bb76c95ad999095a7bcd395370e769447385d93602c469322c34692cd700b924b56d4921c84c192012ccf91dc73c091b63940917bae70915bff5891592acd90e225fa906eb643905e4b30902c5a7f8f74f0a98f63e3fa8f4a16428f1abed38ef926bb8eef58df8eb922578e965ddb8e3f8c778dc082c58d5c0a998bf8e0e98acbbf098aa657898aa44b2d8a978b108a5418158a4b2c568a1561b089b9a4c589b52b50894850958945a6a9893e8c2c893d416f892a2395891d8b7d88fe5bb888ede02888e0387f88687eb2884d9c31882be4e1
  | 6, 17 => 0xa6183c91a5f2097ba5f0d5c5a5ae8250a5aa6600a58443aea55beef2a5375660a5268c5fa51fd700a4e3c223a4be299da3c1ab4ba362c88da33926f8a3219133a2b3fd1fa216970ba213d2a9a1fee453a1f16defa1e5f75fa18bd668a16ca8ada10715c7a0f696e5a0e0586ca0dcb925a0c27a1ca0afbed3a099d7c2a05f6e2fa01e0a0a9f48540e9efaea139eeb49849ed6de7b9ec9ae489e93ebe99e64b9f29e5f82759e519fea9e3d4a399dce524d9d9517099d6fd84f9d58b7ee9d413caf9c9ccc9d9c8da2cc9c7381819c1ef4619be41d5a9af9d2839aaba6e69a4d78589a255f3b99f04df499d8cbd499ce129a998829a398d48fc098d108c998bf8e8d
  | 6, 18 => 0xb635de6ab62922e8b6251136b56cb2e2b55bb1afb52883feb51becfdb4568dc0b455aee0b3b2006db37c045eb3216c62b2d4ff64b2ce525eb29648ffb2700fdcb1febd78b1c67554b1847130b169cadfb15c088fb104f48eb08b6c2bb02513ebaf7940f1aeec8abdae948155ae553aabae4cad44ae11518cae00205dadfa5d03ad48125ead0cc562acc6441eac87cf69ac4df83bac0bbbb6abd7936dabccd6f4ab44d80dab37c3daab35ae3cab1a9a18aac9e59baa3bafddaa22d3e7aa1f6e87a9ada367a980204ba97aa236a9789f6da9608d64a95ab8cba8fa2632a8e78fc4a840633ca822b426a7dff056a7509ec7a73b62e2a6563cc3a6353a8ca61bfe94
  | 6, 19 => 0xcba82e50ca5d1f3fca5180ccc9f2a206c9eaa662c9e9833fc9a3b4fac7ba533ec77995f8c763948fc73369bbc72c9218c69fce5ec6314cecc5c517f6c4d12e58c4b9fc07c4949487c48fe98ec4232d1ac3cea398c398766ec364e4f4c3606443c2afde01c2a091e1c27ad28dc22c52b3c1b3ef36c0d8bcdac0d11869c09606d1c05d353cbf79164fbf40b10bbedd3fb2be269a7bbddeea39bd9d4a99bd41496dbd2315f0bd11debebce43ff6bccaf6d5bc87e6edbc5b9c36bc591900bb4177cfbb13142ebb11473fba6027beba423037b9cae86db9aa6055b99d8907b90dc9b5b88f7056b873fa75b8367464b81e2e8ab79ef288b7888483b78864c3b666254d
  | 6, 20 => 0xe26cad09e247b55ee1ce8bc9e195a639e11f1578e11bb465e1151f08e0e69321e0d1a74ce0800c8de046d2d6e03592fddfb16f80de4eb049de385f98dde0e49bdd1a865bdc4d3caedb88fca5db7c3d73db711277db4f33a9db43194adaa10b17da9e3d59da1fccb5d998bf50d9714ab0d916dedcd8f65272d8dd0a2ad885ee0ed7970f9bd7948ba0d76d9a26d70a1d9bd6f19143d6c78025d6643ea7d5d57342d568b144d520b78bd4b3ae66d4890869d445852fd3a84f1fd2299bdcd13a9d20d0d43b52d028b587d019acf1cfcbd66dcfba7b07cf8f4d70cf1f3ed4ceb4067ace1ee8e6cd90c67acd404df9ccd18a6bcc7bfae6cc3d2a65cc1a159bcbe6744a
  | 6, 21 => 0xf7a45692f6e6c10cf61c967cf59dfad0f4ebb8c3f4cf6b61f405db27f37d4a6df2afc70af250bba1f0f8df95f02597d4f0180015efa77ca6efa21175ef831902eebe9aeaee13d582ecb47af8ebefca4bebc291cbeb6154feeaf7f023ead3279eea6f9829ea2580a6ea23e1e2ea0fb8bde86bd220e865b5b0e82d725ee82ca1a0e7fca500e7eb888ae79e5de2e6f5ef60e65393cae63f2286e63c9710e61e412ae5e5e691e5e351dce5cc13a1e5c286a5e5c095e4e56f8b95e55dcfb7e5495e69e4dd38a3e476b4d9e476652fe455e20ae41e5447e3efe807e3d1e1c2e383dba9e34e3313e2fc4f4ce2f6af66e2f083c8e2e5bc00e2e44efbe2e22383e280ec37
  | 6, 22 => 0xfe646b82fe603c18fe1c6333fc43d33df9f459b8f8b838b6f867a20ff7d75bc1
  | 7, 0 => 0xd9a92370d91ebc20d4d98860cea20e10cc7aa850cabde0a0c2cfbb60c22507d0c167f100bd753a90bb2ffb10b989d440b41c7720afb5dd30acf09dd0ab8b26f0ab7b9ae0ab0afbb0a9628be0a71f9560a2e187209ee1b6f087867580864c5e507bd347d07af559e076636a706a1503206634425065223ce064612c706291d83061ab28605c61dd605ad2f3405a3eb0a059e8b170590310f04d0acec044a0e72040745c603f3df9703e3645403dcabd403bd1a64036df150033b05b5033a727c0322eb1802d5abde0296f579024a740d023f103c01a603fb0198251c0196da2a018309d90129b75501283a1700dd496a0086a50c006499150027347900103def
  | 7, 1 => 0x1d989e101d81c57f1d73f5661ca0b1831bea35011b78d4bc1b325a461b2d157f1b1036f41a5d39541a433cbc1a2bfa9c1a0ece701a0dc40d19f08aad1979f4171937c600192a0dd61923eb0b1922d7aa19169d331900f42918787ffd183e8305181aa941175a929b16e8db18168a4efe1662ea0a1623f29c15ff8a4715f86a801561a43a14e6b4ae141a4f1c13b5da6d12e05c4012b8ab4112ae5da3124e26351234695d11eb7ccf11b4128d1198114411761aa81134c93410d1aa96103ead2a102d8cd30ffdfe370ff073950fd4c3f50fc22fb60faa77070f8898390f6b9a140f5c5cfb0ed7a1e90ea68d810e93ae780e8414b20e783ebe0e57c7a70db67556
  | 7, 2 => 0x2a60bc7d2a5175e429e942c42964176b291abe562889888f287a5ebe284db2db2838c79a27f341652775450f2774c460275958f2272770732705880d26e36c2426d2458e26bb2fef26a4b5bf265363bb264ea121261c309d25eb7b5225bece64259eb530258a6ea4255ffecb24cb7b29246ade96246554a62429651523fe6fae23ea377523afce922325e28c231857ea2310763b23038dd422f4640322ea3ac022c1b3a32282fd3e22521a04223682592227588821e9d24d20df43cc20d196be2081cc612064873a204aaf2d2046aaad203e530f203cd04e20292edb1fd3d3851f9bef851f3108e21ee4e3db1eb3facb1e8eec381e739d441e17d8601e08e153
  | 7, 3 => 0x3b3c318a3b23954e3b0787993afd7b253acd3e823a8b1a653a861c993a47663439fad635395003403899ed18387c221637a1ed1c3732d33a36f4981f36e4026d36c744ae36b6da9236ad51603678c0eb36778df5366fa272363c57f435f834e935d89aaa357bcd57355e29ce3518dab134ceb8d13481847a346540ce342cdee933d93c6b339be83033193e9a32c3d3da3264f194319b3e42315024ba31381b0730ccd1eb3055c0a62fc976f62fbf18df2f7655c82ea0b9112e9e70832e46479b2de85b922d90db782d6df75a2d014b912cf3c0ef2cebdf402cae27f22c1543872bdd94e82baacaed2ba064522b48380c2af4104e2acd7a982a7c85282a6cf071
  | 7, 4 => 0x4b7591cb4b40518f4afc5e1e4ac0774d4a9f53ac4a6707154a0d197449d602e849bfa213499b08ca498bdef949148db048f889f848f0bd7d48ebd2aa47f69d26472e33c146e149a246b340c74609964845f6b584457c5ed1454d83ff45179a8f44d9dfff44cd758b43d63f3a43cee64d43b4257143555fb0433f660a432891ef4309ffd842b779a342815d8a4223bdb94215deda41a83906413f306a413ca69640db2d8b40bb2834405c8f3d40455b7a3ffca0873f49363a3e5fa5093dff89d03dc34cb73dc32c533d8620523d0124c93cedcf813cea22ce3cd7d7c23c9f3cdf3c9dc2fe3c8fe41f3c3d49423c39fd5e3bf167e33bd0b7833bc2d8a43b76a747
  | 7, 5 => 0x5b4388f85b2acd595af03eb05ab946475aa8a6b95a7078f85a3c07d75a1dcce55a17fce059f684b259e5330159d66aa05943cbfb5923c1c65905159658905d13582e787857c3519856dbe56f56da22f0568ff7f156240dff55df5df855ab6c465592bd7c558b8750557f4cd954b47b9853346db9531915d1530ec13f528ca242523dc211520a3fab51e81d5151d2062b51bf3f2b516924ff514f645451007c3a50bcb2a7505beeb34fb2394c4f943bc44f8511f34f717d1d4e9d19034e7327324e5bae794e1717654e00c0ea4de254b54dd111674dc27b5b4cfd734b4cd8ba054ca60af44c8f74574c1e35cd4c173de94c1326ad4bff26be4bf147df4bc96999
  | 7, 6 => 0x6d483b2f6d45b13a6cd622c66c8fa51c6c4b6e046be1bd3a6bcb63fb6bc490ee6b89f08a6b1be3666af785736ad42daa6a5eea176a510b386a4fc62d6a4f220869f9213969c6f98169c031bf69b2eaed692e70ee68ff5c7d683fb3fc67f1c0d36709aa6166742ba76554bad1651506a464ffcc4e64e30e6464cf00c564789948645092fc64015902638147926379a6766347643b63353df462b43c176292bf226284e04362623a3562542af861f427ee60f8c4a560d158045fd513de5f5d13a95f2a63495e90082e5e191a245e1657ce5e06e6065debf6475d9647d45d93d62e5d6275f45d3a46645d2e415c5c9fbd605c91de815bff541c5b9aa8305b83d915
  | 7, 7 => 0x81102355806266ad803eeee07fe35f827f5f0e0b7f1797dc7e8559377e67d7ba7e05acff7dfd47397db1e1917dad4e397d33ff317d303bbe7cd372a07c439fcf7b25f4ae7ac854af7ab597257ab2c9087aa157477a70b1287a38d5c27a2bf43679a4d76c791d9b417900675a78f13d8978bca8127892577578493a7f77f10ba27793726477211a3f76f0de3376eecc3f76db0b2e76bdf4b9766385db75ee73ad75c5ccea749b9886748c6eb5745a681c73f60c3a73b9b90973833cd773227b8e72b28339727daf3d72739f5471be65bd714a8ba9707cee8d7005f1236ebe77696e834bca6e38e6f66e2bfc016e1ad9ba6ddedbb86dcfb1e76db8095f6d5cb097
  | 7, 8 => 0x97a5128c974a939b9721f5ed97012b8496fad256965f3458965531e695a996be955a089893f42b8d9396353d93602c46934043b892a6c201928cbda591bec62691b98d1291495fea91426eab906d26119011f58290061e318fa2db658f7fd14d8f78512d8e35cdb08e27eed18d92f6958d7f04bb8d1e3ac28c8386ea8c76bee98bc68b508bbc73f08b8fda438aef68758a8bfac78a18c28889beef4c897643b68968a0cb895976fa8958e8bc8788b73e877910e287080352869b7594868cb4248651842c862851b985e99b5485520fcd8549f6d2850f030e8492c7cd848e320d83c5bc52838341f4833df90383233d80830766bf82d3eb9982739f2082121d0d
  | 7, 9 => 0xb96ec08eb8a1b513b84d21e0b837fe7bb7610a65b713f0d0b65f3e8fb5c9ec3db5195244b403d0cab3823d02b253eee6b242b686b210ca3fb0f51e5bb0ec7e1fb0e1dcffb080f6ebb0480e0db02268afaf95e2ffaf935789af1156b4af01b67aaee65ee3aec64c0eae8d3699ae5c9576ae064aa9ad85a160ad6b0c80ac23afedabe5308aaa8df529aa87c3f1aa3f12b1aa2867c5aa21bb6da9cb11c2a9647ee6a8d69abba80d4bfda8098f40a68098aea6032cd2a4a02823a494c22fa302d5f5a275c8f5a141bf77a0c045e2a07b3991a00d2aa29ffd08839e6bbe4b9d2006f69d1bacbd9c27c3cd99ed5e879985b80798d83969981136b5980357d697ec88bb
  | 7, 10 => 0xdd547ea2dccf165adc240579d9eccea3d986de71d96359b3d9194922d8f62b1fd8e7dfa1d87f9952d7d8277ed7c2c847d697c1d4d6890d25d64ffb9bd62ad27fd5d7c256d3c1c38ed355d4ffd2f3ad55d27a66b2d1d3f658d1b38e6dd0a7e5c1d051c79bcf9551ebcf84bc20cf6ea403cf2fed9ecf0c769cceecb93fcecb96dfce6b8b90cdfcbe79cd5fbf4fcc0fb7b2cc0b8b0bcba24973cb46a5f8cae6d7d7c9e65a89c8d8951dc876c3bec7a9b843c73804a5c52f7576c4605fcec398766ec3935453c31b6fd9c1c6e06ebfa55542bef4bb49be4be64fbd5c9ba0bd11debebcc8e334bc5e25f5bbe49247bb0a100bbad08760ba88bda4ba2399e2b9714c04
  | 7, 11 => 0xffcceadcff5a28fefefc312dfe12eeb4fce2758bfab495f5faa130d0f96feb04f8b72109f7e68aa8f7c42f43f734b506f6e94291f646c3bff637ead7f5493ef0f4cf6b61f4b969f8f32a1730f22186e7f15a4793f11d8484f103a542f0c5c7cbf05fc8f2efeaeca8efdfd1c7ee6bbfe2ee13d582ede8c63eed71b5aeeb7a065aeb3fcd10eabec0cdea72c195ea555bf2ea39f55dea2580a6e9d3bc26e8b03ee3e878be20e862cb83e81cf98ee7a75556e795c008e7283c3de5ff6e7ee56f8b95e4625a30e3d420a8e11915d9e04a17a1e0063b84dfdba1afdfb32b5bdf7fbf91dede789bde1b0bb2
  | 8, 0 => 0xf2854adfdd9de376dac0e1e9bad4da24b6be76349b34b1217cea112d76f0de335e22a75451bb2a0f4aee737942b779a33e277fff2eedfa851e7359ed1729918f
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0xc910600000520c120300085504843000000020480202000000000000e00000144802020000010440202000c5504c4300
  | 4, 0 => 0xc910e000000000000300085504843000000021484208000001448020800000000c11030000034041208275843044140000000340412020000000000002000000000000e00085504843000000010440208000000000000a0000034081202000000000000f0000010440208000c5504c430100000000c9106000855048430100000214842080000020441201000000000000e000003404120200000144802080000021484208000002148420800000000c510c00000000c510a0000034081208000003404120200000000c910a
  | 4, 1 => 0x14480208000000000000f000000000000f00000000c1104000000000000f3258132101400000003408120800000504842000000000040102000000000000e000004204120800000325052060008550484300000000000000f00000404412010000014081208000855048430100085504843010000000000003000000000000000000204802023258132101400670c54044140000000454c9206000000000000a00000414c4203000000000000f00000340412080000034041208000000000000f000000000000f000000000000f
  | 4, 2 => 0x4044120100000000c8103000000000000f000000000000c00000340412080000000000006000000004010200000000c510c00000504c4205000c5504c4300000000000000e0000020480208000000000000a000c5504c430000000510c120300000340812080000000000002
  | 5, 0 => 0x200000254c420000000000000040000000000000000000000000c0000000080108000005048420100000340812020000000000002000000000000c0000000040108000003408120800000001051030000000105107000000000000c00000000c510e000000000000000000000000050000000000007000855048430000000000c11010000000109103000000000000c000000000000f000000004910800000404412010000000000007000004350c2000000014480202000004044120000000304412010000025006200
  | 5, 1 => 0xc00000000c1104001814508530000000000c11040000000101101000000000000f00000001011010000000105103000000000000a000002048020800000000c810300000504842000000000000003000000000000200000000000060000020441201000000000000f000003408120800000000000020000000000005000000004110800098514c1300000d8254413000008550484300000001044020200098354413000000000081108000004508520000000000811080000021484208000004508520100000000c910c
  | 5, 2 => 0x10910500000520c52010000000105103000000000000e00000214842000008550484300000000000000f001183544130000000000000020000000000002000d43044130000000000c1103000000010d10700000000000020000000109103000000000000f0008550484300000000000000c00000504c4200000002148420800000000c910600000254c4200000002404120800184304413000000021484208000003144120700000214842020000034041202000c5504c4300000003404120800000340412020000000000005
  | 5, 3 => 0x14480202000002148420200000000000000000000085108000000004110800085204413000000000000001000000010110000000000c510a00000144802020000021484208000000004110800000340812020011905885300000000000000f00000340812080000034041202000000000000600000454c4200000003404120800000000000030000034041202000001044020800000104402020000000000003001813210130000000450c520000000214842010000040441201000c5504c430000000344802020008520441300
  | 5, 4 => 0x2048020200000000c910a0000000109103000000000000e00000254c4200000000000000a000000000000a00000000c1104000003408120200000000000010000034081202000855048430000000000061080000034041202000000000000e00000000000030000034041202000003448020200000450c520000000144802080008550484300000855048430000000000000000000000000002000000000000500085504843000014c324813000000021484208000001448020800000000c910a00000204802080000000000000
  | 5, 5 => 0x30441201000000010510600000001051050000000041101000000000000a000003444020800000000c510e00000000000040014421481300000000000000a00000340412020000000000000000000000000900000001011000000000000000000000000000500000140812020000000105103000003404120800000000c910e000855048430000000000000060000000000003000000000000f00000214842080000000109103000000000000700000000c410500000404412000000000109106000000000000700000000c1103
  | 5, 6 => 0x40441201000005048420000000000c910e0000000000007000003404120800000000c910600099510c1300000000000000a000005050420100085504843000000021484201000000000000000000000c81080000000000002000001044020200000000000000000000105103000000000000200000000000010000000000003000000000000a00000000000020000000040108000000000000a000000000000a00000000000000000000000000000000000000c000000000000a000000000000c00000000000050000000000002
  | 5, 7 => 0x6000000010d10700000104402080000010440202000001448020200000000c510e000c9504c830000000000c81030000050484201000000000000e000004548420100000000c11040000000000003000000000000400000000811020000014081208000855048430000181321013000000000000003000000010510300000000000070000000000003000001044020800000104402020000000000004000000000000c000000000000300000000000040000000000005000000000000a00000000000020000000000001
  | 5, 8 => 0x3404120800181450c530000000520c120300000000c11030000000000004000000000000200000000c110400000000801080000021484200000001044020200000000c81030000000000006000000000000a0000020480202000000000000100000000000070000000105103000000000000e0000010440208000000000000e00085504843000000021441207000000000000a00000324c8201000000000000f0000000109103000000000000300000414c42030000045484200001583150130000000000000000000030441201
  | 5, 9 => 0x450c52010000000041102000001500e200000000000000500000000000030000034081202000000000000400000000000040000010440202000000000000f00000254c420100000000c910c0000014480208000c54044130000000340812080000040441200000003408120200000410c12080000014480208000c9514c830000000144802020000034480208000000000610800000504842010000000109103000000000000f000000000000400000000411010000014081208000000000000a00000304412010000014081202
  | 5, 10 => 0x600000000000010000000000002000002044120100000000000050000000109104000000000000000119510c13000000034081208000c932101300000000000000600000000c910c0000000101100000000010110100000000c1104000000000000000000000851080000010440208000000000000a00000324c8200000000000000e000000000000f00000254c420100000000411080008540441300000002148420200000204802020000021484202000003500a200000000000000a00000450c52000000000109103
  | 5, 11 => 0x21484208000000000000a0000021484202000000004110800000000811080000021484200000000000000100000000000030000034081208000000000000c00000514c820000000001091040000000000003000000000000300000324c8200000001044020200000000c9106000004548420100000000c910c0000010440202000004204120800000144802080000034440202000000000000f0000000000003000000000000200000314c4201000000000000e000001448020800000000c9106000000000000b000000000000a
  | 5, 12 => 0x254c42000000020480208000000000000e0000000000004000993504130000000000c41030008550484300000000000000a00000000c410500000000000020000000041108000000010510600118354413000000034081208000002148420200000340412080000041504200000000010510300000000000010000000105104001192500e300000000000000f0000000000001000000008110100000450c52010000000000002000000000000100000000c510c000852044130000000324c820000000355042000000000109105
  | 5, 13 => 0x40441201000000000000a000000000000f0000000000004000000010110100000324c820100000001091070000000000006000000010510600000000c1103000000008410800094214413000000000000002000005050420000000000c8103000002148420200000000c1104000000000000f00000000021080000000000001000000000000000000144802020000021484202000000008410800000340812020000000000002000000000000f000000000000100000000c510c00000314c420000000450852000008550484300
  | 5, 14 => 0xc93210130000000324c82000000000000003000c54044130000000000841080000000000006000c9504c83000000000041101000000000000e0000020441201000004044120100000000021080000000000003
  | 6, 0 => 0x85102000000000e100000002504120000000000000050000000000004000000000000200000000000070000000109107000000010510100000000000030000000109103000000000000300000324c820000000000000000000034081202000000000000a00000504c4200000000010910600000504c4200000000000000c00000000021080000000041101000000000000300000000c8102000000000000c00000314c4202000000000000d00000000000030000000000006000000004110000000000c110400000000c0108
  | 6, 1 => 0x30000000105105000000000000400000000000010000000000003000000010510400000000801020000000000004000000000000a000000000000e00000324c520000000324c820000000000000030000050484200000000000000c000000008110000000000000030000045085200000000000000500000000811010000000000003000000000000c000000000000200000144802020000000109105000000000610000000000851000000000049108000000000000f0000000000005000000000000a00000324c8200
  | 6, 2 => 0xc9100000000000000600000454c420000000000000030000000006100000004350c200000000000000500000000811080000000000005000000000000c00000450c520000000244c020200000324c820000000234c1200000000010910600000000000060000000000000000000000000400000001051000000034081202000000000000c000000000000800000001051030000003901200000000000a102000004508520000000000000030000000080108000000000a10200000000061000000000000003000000000000c
  | 6, 3 => 0x1091050000000000006000000000000300000000c1103000000000e1020000000105105000000010c101000000000000c00000000c01020000000000003000000000000c000000000000700000234c1200000000000000c000000010910700000000c11000000000085100000002444020200000000000000000020480202000000000000f00000000061020000000000004000000000000c0000000006108000000000000700000019012000000000002108000000000000200000000411080000000000002000000000000c
  | 6, 4 => 0x32501200000000010510500000000c9104000000004910800000454c420000000454c42000000000084102000000000e101000004350c200000000000a1020000035481200000000000000a000000000000400000000000000000000000006000000000a10100000000061020000000000000000000000000c000000000210800000450852000000000002100000000000000400000000000030000000000001000000000210100000001011010000000000005000000000000a00000000811010000000000002000000000a108
  | 6, 5 => 0x700000314c42000000021484200000000008d101000000008510000000000c010200000450c520000000000061020000042101200000000000000c0000000000008000000000000600000000411020000000000005000000480a200000000004910800000000121010000045085200000000000e102000000000000300000000000020000000105101000000000000e00000001081000000000040102000000000000c000000000000a0000000108101000000000000a00000504c4200000000000000300000314c1200
  | 6, 6 => 0x500000000c4105000000000a10000000000021020000053101200000000000000700000000000000000000000003000000000000300000000c810300000324c8200000000000a10100000000c11040000000012100000000000000c0000000000007000005050420000000304c0202000000000a1000000034440202000000000000400000001091070000000000003000000000000a00000000c110100000000851010000000000006000000000000a0000000000003000000000a10000000000000040000000000006
  | 6, 7 => 0x7000000000000500000450412000000045085200000003248120000000315012000000000080108000000008110800000058852000000000109107000000000000400000000000020000000105105000000000000c000000000000600000000401020000000012100000000000000c000000000000c000000008510700000029012000000000012100000000280220000000000c41030000000000005000000000000f000000000000300000314c42000000000000007000000000000300000504c4200000000000e101
  | 6, 8 => 0xc910a000000004110100000504c4200000000000000c000000000000200000001091030000000000004000000000000a00000000000030000000000004000000000000600000000000030000000006100000000004110700000000c11040000000000003000000000000c00000000000060000000006101000000000000400000254c4200000004548420000000000000080000000000002000000000000f000000000000700000354412000000000000006000000000000a000000004110800000000000020000000000003
  | 6, 9 => 0x4000000000000300000214842000000035481200000000000000e0000000109103000004548420000000000c91020000021481200000000480620000000000c1103000000001210100000404412000000000000006000000000a108000000000000a0000000000003000000000000a00000000c9100000000000a1020000000000002000000000000a00000454c42000000035484200000000000000100000504c82000000000002102000000000000300000000021080000002806200000000000a1010000035504200
  | 6, 10 => 0x2102000000480620000000000021020000000000002000000000000400000354412000000043101200000000004010800000244c020200000504c420000000000000030000000000005000000008510800000000000040000000049108000000000000c0000000101101000000000000e0000041504200000000000000500000000000050000000000005000000000000c000000000000200000000000010000005901200000000000000300000000000040000002806200000000000610100000144802020000000002102
  | 6, 11 => 0xf000000000000e0000000012100000000000000a000000008d100000000000000a000003550420000000000c11050000000085102000000000000000000000000040000000000003000005050c2000000040441200000000000000100000000061000000000000003000000000000c0000000000004000000000610000000000401020000000000004000000000000700000000000000000002901200000000000000a000000010910300000000c81010000034081202000000010910300000000000060000000000004
  | 6, 12 => 0xc910c000000010910400000454c4200000000541220000000000811080000000081108000000000000c00000000000050000000000007000000000000e0000000000001000000000000600000000000000000000000004000000000000300000000c4108000000000000600000000851080000050484200000000480a20000000000000020000000000007000000000000300000000c4102000000000000a0000000000006000000000000000000000c8108000000000a100000000008010200000000c4103000000000000f
  | 6, 13 => 0xc11050000000081100000005050c200000000000000000000000000040000000000008000000000000300000000c510a00000254c120000000000c4100000000004110700000000c11040000000000005000000000000a000000000000200000000000030000000006108000000008510100000000811010000021484202000000008d100000000000000a000000004110200000000481080000005841200000000008110200000000061020000000000002000000004110800000000c910000000000000060000000109107
  | 6, 14 => 0x4110100000000061020000000000004000000000000300000000000070000034041202000000000000a000000000000a00000454c420000000000000030000000000002000000000000a00000000c1101000000000a10200000314c420000000058c9200000000000a10200000000000030000000006101000003550420000000000c11010000050484200000000000000600000000c0102000000000000a000000000000400000504c4200000000000000f00000000c5101000000008110200000404412000000024440202
  | 6, 15 => 0x60000052101200000000008d101000000000000a00000000491080000000000007000000000000e0000000000001000000000000f000000008510000000000c4102000000000000200000000000030000000000001000000000610800000510c120000000000c5100000000000000a000000010d10600000324c820200000000000050000000000004000000000000600000000c510000000000c11020000000000003000000000000600000000411000000021484202000000000000f0000000000005000005150c200
  | 6, 16 => 0x10910600000000841010000000006100000000000000700000000c410100000000000060000000000003000000000000200000000c1105000000000000c000000010910600000000000070000000000004000000000000600000059012000000000000007000004548420000000000000060000002806200000000000000000000000000050000035484200000000000000200000000000000000000000005000000010910400000000c1103000000008010200000000c8108000000010910500000314c42020000021484200
  | 6, 17 => 0xc510800000514c820000000001091010000000109103000000010c10100000000c510100000340812020000000085108000002148420000000000000020000051508200000004548420000000000000040000042508200000000000000e00000000c1105000000000000a0000000000004000001448020200000000c1101000000010910400000000c510000000324c820000000000061080000000006101000004548420000000048062000000041504200000000010d100000005048420000000000c81020000000105103
  | 6, 18 => 0x6000002044120000000000000040000000109106000000000e102000000000000500000404412000000000002108000001500a20000000000c4102000000000000200000000000050000000000003000000000000000000000c1103000000000000200000254c4200000000000000300000000841000000000000003000000000000a000000588120000000000000020000000000005000000010c1000000000000000000000000610200000254412000000000000004000005048420000000000000070000000085100
  | 6, 19 => 0x214812000000000041101000000000000200000000c4105000000000e10800000000000050000000000007000000000000a00000000000070000000080102000000000000500000001051060000000000005000000000000a00000404412000000000000007000000010d1070000035504200000000004110800000001091050000000000007000000000000400000000c1105000000000a1020000000105103000000000000c00000450c520000000000841010000000000000000005050c20000000000000040000000000006
  | 6, 20 => 0x80102000000010910700000304412000000000000002000000008d106000000000000c000000000000a0000000000003000000380220000000000c410500000000c410800000000c510c00000000c010200000000c1103000000000000700000000401020000000085100000000000000e0000003901200000000000000e000003550420000000254c42000000000000002000000000000700000250c12000000000000007000000000a10000000000811000000053101200000000008510800000000411080000000041102
  | 6, 21 => 0x5841200000000008110800000001011010000041504200000000000000a0000000000007000000000000700000504842000000000105103000000000000400000000000060000000000003000004548420000000001011000000000000003000000000e1080000000000003000000010d1070000000000003000000000000000000000c4103000000000610800000504842000000050504200000000000000300000000c01020000000105100000000000000300000000000020000021484200000000010410000000000c1100
  | 6, 22 => 0x30000000109101000000000000300000344802020000000000006000000001210100000000c8101000000010d1070000000000005000000000000a00000001051030000000085107000000000000c000000010910400000000000070000041504200000000000e1020000020441200000000000000a00000000c810000000000121000000000105101000000000000c0000000000003000000000a10100000000000030000000105103000000000000e0000000000003000000000210200000001051050000000000007
  | 6, 23 => 0xe108000000000a1000000032101200000000000a108000000000000f000000000a101000000000000300000314412000000000000008000000004910200000000000020000000000003000000000000300000000c910100000058c12000000000049102000000000000c00000000000060000000000005000000000e100000000004910200000000c11020000000000006000000000a100000005050420000000000c110400000254c4200000000000000500000000c1103000000000000c000000000000c0000035484200
  | 6, 24 => 0x3000000000000a000000000000400000254c4200000000000000600000000c0102000000000000600000000c11010000000000004000002148420000000000000070000000000005000000000000400000000000080000000000003000000000610000000355042000000042101200000000000000a000000000e100000000001210000000254412000000000000003000000010910300000000000040000021484200000000000000400000425082000000034480202000000000000400000029012000000000101101
  | 6, 25 => 0xe0000000000007000000480a200000000000a108000000000000e00000000000050000000000002000004508520000000000061020000000000000000000000000500000254c42000000040441200000000000e10000000450c5200000000000610000000254c42000000000000004000000000000000000404412000000000081102000000000a10800000058c5200000000010910400000524c5200000000004110200000000c51010000000000004000000000000e000000010910700000000811020000042508200
  | 6, 26 => 0x10110100000000c110500000001051030000003901200000004150420000000000000030000021484200000000000000000000000c11050000000000006000000010510300000000c110400000000000050000000000002000000000210800000304c020200000000c8108000000000000200000000411080000000002108000000004110200000450c52000000000105104000000000e1020000000000003000004350c2000000000105104000000000610100000450c5200000000000e10100000000000020000000041108
  | 6, 27 => 0x41107000000000000c000000000e10100000000c4108000000000000600000324c8200000000000a10000000514c120000000019012000000000109104000000010d106000005050420000000000c11040000000006100000000000a108000000000e108000000000000a0000000000007000000000000400000000c510a00000000c910c000000000000a000004350c2000000000000007000000008010200000214842020000000000003000000000000f000002500620000000254c42000000001901200000000010d101
  | 6, 28 => 0x400000000000060000000006102000004548420000000000c11040000000000000000000000000a000000000000e00000000c91000000000000002000004250820000000000c91000000002901200000000000000f0000000006108000000000e101000000000000300000000c5101000000000000c00000000000040000000000003000000000610200000000000020000000084102000000000000a00000000c81030000000000003000000000000c0000050504200000000000000400000324c82020000005841200
  | 6, 29 => 0xc00000000c0108000000008d10600000000c510c00000425082000000000002102000000000000400000000c0102000000000000e000000000000300000254c4200000000004110000000000c81000000000000008000005048420000000000811080000000000000000000000000a000000000000200000001011010000000109105000000000e10800000524c5200000000010d10700000028062000000000101100000000000000f00000000851020000000048102000000000e10200000000c11030000032501200
  | 6, 30 => 0x21080000000000004000000000000a000000000210200000000851020000050504200000000000a1080000000085107000000000000500000000c11050000031501200000000010910500000000000030000021484200000000000000000000000491020000050504200000000010510400000029012000000000000005000000000000a000000000000c00000000c5100000000000000000000450c520000000000401080000000000004000000000610800000000c1103000000004110800000000000030000031441200
  | 6, 31 => 0x811020000000000001000000000000a000000008010200000000000050000000041108000000004110200000214412000000000002101000000010910700000000c1104000001044020200000000000040000035504200000000000000a000000000000e0000001901200000000000000e0000000000009000000380a20000000000c8101000000000000e0000000000007000000000000c0000000000004000000000000300000000c110500000000c4108000004350c200000000000000c0000000006101000000000000b
  | 6, 32 => 0x1051060000000000003000000008510800000001051060000000002108000000000000a000000000000c0000000085102000000000000200000504c42000000035504200000000000000c000004508520000000000c51020000000085102000000010c101000000000000c000000008410100000000000030000000000002000000000e10000000000801020000001901200000000000000500000000841020000000041102000000000000300000000000020000000002101000005050420000000001081010000000000000
  | 6, 33 => 0x811000000040441200000000000000c00000000000020000010440202000000000000a000002500e2000000000000004000000008110800000001051060000000000002000000008110200000344802020000000000004000000000000500000000000000000000084102000002148420000000001051030000000000003000000000000200000000c9101000000000000300000324c8200000000008510800000000000040000000000005000002148420200000000c11030000041504200000000000e1010000021484202
  | 6, 34 => 0xc0000000081102000000000000a00000000c110800000000000030000000000003000000008110200000254c420000000244c02020000000085102000000000000a000004548420000000000c5101000000000000a000000000000e0000000000005000000000000f000000000000300000355042000000000000003000000380a200000000000000c000004250820000000325012000000000000004000000010510700000340812020000000000004000000000000e000000000000a000000000000c000000000000e
  | 6, 35 => 0x10000000109101000000010510700000254c420000000001051050000000000005000005048420000000000021020000000085102000000541220000000000000020000000000005000000004110200000000c110500000000c810200000000000030000000000003000000000210000000404412000000030441200000000010110000000450c52000000000000003000000000e101000000010910700000000c810200000450c5200000000000000400000000c410500000000c110400000000000030000000000004
  | 6, 36 => 0x504c42000000050504200000004044120000000000000020000041504200000000000210800000000411010000000101100000000000000c0000000109103000000000000300000000000020000000000005000000588520000000000c010200000000000040000000000008000000004110800000324c8200000000000000100000000c41020000021501200000000000a100000000004110200000000000040000041504200000000000000300000000c9100000004350c200000000010910000000000c8103000000000000f
  | 6, 37 => 0x304c020200000254c4200000000000000300000000000050000000000007000003210120000000000000010000050504200000000010110000000000000070000000000002000000000000500000000c1105000000000000f0000000040108000004250820000000000851080000000000003000000000210200000504c4200000000000000300000000c8103000003444020200000504c42000000002901200000000000000500000000000030000000000006000000000e1080000000000004000000000000c000000000000e
  | 6, 38 => 0xc5102000000000e1020000035504200000000010510500000000000020000000000003000000000000700000000c4103000000000000a00000355042000000005412200000000000a1080000035481200000005050420000000058c92000000000000003000000000000a00000314c420200000000491020000000000003000000008110800000450c520000000000000040000000000004000000000000a0000035504200000000380a20000000504c820000000000000030000000101100000000000000a0000000000003
  | 6, 39 => 0x355042000000000000004000000000000300000000000030000000000001000000000000300000000000040000000000003000000000a1010000000006102000000000000f000000000000f00000000000040000000000000000000010510700000505042000000000085100000000000000000000000000040000041504200000003210120000000000000060000000000006000000000000c00000000c8100000000000000a000000000000300000000811020000000041108000000004110200000000c510c0000000002101
  | 6, 40 => 0x500000000000030000010440202000000000000400000000c91080000000000003000000000000f000000010510500000324c82000000000002108000002550420000000000000020000000002102000002048020200000254c42000000000000001000000000000c0000000000004000000000210200000000c1101000000180220000000404412000000000000002000004150420000000324c82000000000006101000000000000600000000c5101000000000000a0000000000006000000000a100000000000000c
  | 6, 41 => 0xa1080000000041101000000000a10800000000000070000000000003000000000000700000000061020000000085102000005050420000000504c820000000000811020000000105104000000000e108000000000000f00000001091030000000000003000000000000a0000045481200000000010110000000000841080000000002101000000480220000000000000050000000084102000000000210000000058c12000000000041107000000000000f000005050420000000254c4200000000000e10200000000c1104
  | 6, 42 => 0xa10000000000000070000050504200000000000000a0000000000002000000000000300000000000030000000041101000000000000500000324c820000000000000060000000000002000000000e102000005050420000000254c420000000000000030000000002101000004044120000000244c020200000058c92000000000000002000000010110000000000021080000041504200000000000000c00000000000070000000002102000000000000500000000000060000000006101000000000000400000514c8200
  | 6, 43 => 0x60000000000004000000001210100000000000060000000000007000000008d100000005050420000000000000010000000084108000000000000f000000000000100000304c0202000000000000300000000000060000000101100000000000000c0000000000007000000000610000000000000000000001802200000000000000600000404412000000000085102000000000000700000244c0202000000590120000000000c910a00000000000000000000006101000005050420000000324c82000000000006101
  | 6, 44 => 0xf0000000084108000000000e1080000014480202000000000000300000000c110400000000061080000000000006
  | 7, 0 => 0xc4102000000000000200000000121000000000000003000000000000c00000000000070000000000003000000000000200000000000070000000006100000000000000a0000000000001000000000000100000000c410000000000000060000000000005000000000a100000000010c10000000000841000000000000005000000010d100000000000000f000000000a100000000000000300000000000030000000000000000000000000300000000000070000000081100000000008510000000001051000000000000006
  | 7, 1 => 0x4000000010c1000000000081100000000000e1000000000000003000000000a1000000000000007000000000a1020000000085102000000010c100000000000000200000000841000000000006100000000000000e0000000000002000000000000700000000c410000000000000050000000000000000000000000400000000000010000000002100000000004110000000000061000000000000003000000000610000000000000040000000000008000000000000600000000000030000000000004000000000a102
  | 7, 2 => 0xa100000000000000e00000000811000000000000002000000000000100000000000000000000000003000000000000e0000000000001000000000000c000000010810000000000c1100000000000e10000000000c9100000000000a10000000000000070000000000003000000000000600000000000030000000000005000000004110000000000000010000000012100000000000000700000001011000000000000000000000010d100000000000000e0000000000003000000008110200000000c91000000000000005
  | 7, 3 => 0xa1000000000002100000000000000600000000000040000000000004000000000610000000000c41000000000084102000000000000500000000c51020000000000001000000008510000000001011000000000000007000000000000500000001081000000000101100000000000000500000000c110000000000c1100000000000000100000000c51000000000000006000000000000c00000000c5102000000000000300000000061000000000000001000000000000600000000c510000000000000040000000000002
  | 7, 4 => 0x1011000000000006100000000000000600000000000060000000101100000000000000c000000000000a0000000000003000000010c10000000000841000000000000004000000000000c0000000000003000000000000c000000000000a00000000000080000000081100000000000000200000000000030000000108100000000000000600000000411000000000006100000000000000200000000000000000000000003000000000000600000000c1100000000000e100000000010910000000000000060000000000007
  | 7, 5 => 0xa0000000012100000000000210000000000000040000000000003000000000000c000000000000a000000000000300000000000040000000000006000000010910000000000c9102000000000000300000000411000000000000002000000010c100000000000000e000000000000200000000841000000000000005000000000000400000000c910000000000000030000000006100000000010c100000000000000a000000008410000000001051000000000000006000000000a10000000000000020000000104100
  | 7, 6 => 0x5000000000000400000000000000000000012100000000000000c0000000012100000000000a10000000000c9100000000000a100000000000000e000000000000a00000000000030000000041100000000000000a000000000000a000000000000600000000c5100000000000000200000000c91020000000000006000000000000700000001011000000000108100000000010510000000000000040000000000007000000000000600000001041000000000000007000000000000a0000000006100000000000a102
  | 7, 7 => 0x500000000000030000000000001000000000000a00000000c81000000000006102000000010c100000000008410000000001011000000000000002000000000a100000000000000a000000000000300000000c41000000000000007000000000610000000000000040000000084102000000000000300000000000000000000000001000000000000400000000c1100000000000000200000000000000000000000006000000010910000000000000050000000000002000000000000300000000000080000000012100
  | 7, 8 => 0x4110000000000000000000000109100000000000000a0000000012100000000000000a00000000000070000000109100000000000000300000001051000000000006100000000008510000000000000050000000000002000000010910000000000c41000000000000001000000000000500000000c110000000000000020000000000007000000000000100000001011000000000012100000000000000300000001051000000000041100000000000000c0000000000002000000000000300000001041000000000012100
  | 7, 9 => 0xc41020000000000000000000010410000000000c9100000000000a10000000000c4100000000000e10000000000c0102000000000000500000000061020000000000002000000000a100000000000000400000000000040000000084100000000000e102000000000000a000000000000700000001011000000000000003000000000a10200000000c41020000000000001000000000000500000000000040000000006100000000010110000000000c8100000000000a102000000000000300000000000060000000000000
  | 7, 10 => 0x200000000c91000000000000005000000000e102000000010110000000000000050000000012100000000000e100000000000000700000000000030000000002102000000000610200000000000020000000041100000000008410000000000000000000000000007000000000000300000000c110000000000000030000000000004000000000000400000000061000000000000004000000000000e00000000000020000000000004000000000610000000000c8100000000000000a00000000121000000000105100
  | 7, 11 => 0x10d1000000000012100000000000000f00000000c8100000000000000200000000000030000000000002000000000000500000000000040000000000003000000008410200000000c5100000000000000600000000000030000000000004000000010510000000000000010000000104100000000000000300000000000070000000101100000000010910000000000121000000000002102000000010c10000000000c11000000000104100000000000000200000000000080000000000002000000000e10000000000c5100
  | 7, 12 => 0x200000000411000000000000006000000000000a000000000000300000000801020000000000006000000000000500000000c91000000000000003000000010410000000000000060000000000008000000010d10000000000000070000000105100000000010c1000000000104100000000000000100000000121000000000000005000000000000300000000c81000000000000002000000000000c00000000c1100000000000000300000000000030000000006100000000000210200000001011000000000000008
  | 7, 13 => 0x40000000000006000000000e10000000000000060000000000002000000000a100000000000610000000001051000000000000003000000000000200000001041000000000000008000000000000300000000c510000000000000050000000105100000000000e100000000000000100000000c4102000000000000c00000000801020000000000004000000000000200000000121000000000000003000000010c10000000000c9102000000000a10000000000c9102000000001210000000000c91000000000000002
  | 7, 14 => 0x200000000000070000000002100000000010c10000000000000020000000000003000000010110000000000000010000000000002000000000000c0000000000008000000010d1000000000002102000000000000000000000000020000000000004000000004110000000000c81000000000000000000000008d10000000000121000000000000006000000000000c0000000012100000000000a10200000000000020000000000002000000000e1000000000006102000000000000200000000000020000000000007
  | 7, 15 => 0x700000000000030000000101100000000000000f0000000006100000000000000a00000000c91000000000000008000000000000c000000000000a000000000e10000000001011000000000081100000000000000300000000851000000000000003000000001210000000001091000000000085100000000000000a00000000061000000000000004000000000000c0000000000004000000000000e00000000000020000000000004000000000000a00000000000080000000006100000000000a1000000000105100
  | 7, 16 => 0x6100000000000000a0000000000003000000000000300000000c1102000000000e10200000000c0102000000000000c00000000061020000000000002000000000000700000001011000000000080102000000000a1000000000002100000000000000000000000c5100000000010c100000000008410000000000c910000000000c4102000000000000400000000c1102000000000000a00000000c0102000000000000a0000000000002000000000000c00000000c41020000000000005000000000000e0000000109100
  | 7, 17 => 0xa000000000000100000000c8100000000000000400000000000070000000084100000000000000400000000000070000000000004000000000e10200000000061000000000000004000000000000200000000000040000000109100000000000000400000000c91000000000000008000000000000a000000000000c000000000e1020000000000003000000000000400000000021020000000000002000000000000a00000001011000000000000004000000000a10000000000c510000000000000020000000000000
  | 7, 18 => 0x4000000000210200000000851020000000000000000000010110000000000801020000000000005000000000210000000000c1102000000000000200000000c010200000000000080000000000007000000000000400000000021020000000080102000000000000200000000811000000000080102000000000000e0000000000004000000008110000000000c8100000000008110000000000000020000000000007000000000e10200000000c5100000000000a102000000000000a00000001011000000000041100
  | 7, 19 => 0x7000000000000a0000000081102000000000e10200000000000020000000104100000000000610000000001011000000000000006000000010110000000000061000000000081102000000000000e00000000000060000000101100000000000e10000000000021020000000085102000000000a1000000000000000000000000000700000000000070000000006100000000008510000000000c810000000000000060000000109100000000000e10200000000000030000000000002000000000a1000000000041100
  | 7, 20 => 0xc81000000000012100000000000e100000000004110000000000c8100000000000000e000000000610000000000c8100000000000e1020000000002102000000010510000000001041000000000101100000000000a10000000000c1102000000000000600000000c0102000000000000200000000000060000000101100000000000000700000000021000000000101100000000000000300000000000060000000000006000000001210000000000000010000000101100000000000000100000000c9100000000000000a
  | 7, 21 => 0xa000000010110000000000000020000000000002000000000000400000000000020000000000001000000000000a00000000121000000000000002000000001210000000000411020000000081102000000000000500000000000000000000000002000000000000c000000000e10200000000000070000000101100000000000000a000000008110000000000c81000000000000003000000000000c000000000000a000000000000c000000000000c0000000000004000000001210000000000411000000000085102
  | 7, 22 => 0x300000000c91000000000000003000000001210000000000000070000000006100000000010510000000000411000000000104100000000008510200000000021000000000000007000000000a100000000000000f00000000061000000000105100000000000000100000000000070000000104100000000000000200000000000020000000000003000000000210200000000411000000000000008000000000000700000000000020000000000002000000000000c0000000000005000000000210000000000c8100
  | 7, 23 => 0x2000000010410000000000c11020000000000005000000008410200000000021000000000012100000000000000000000000021000000000000006000000001210000000000061000000000084102000000000000400000000c5100000000000000700000000000010000000000002000000000000700000000811020000000000002000000000a10000000000000020000000012100000000000000c0000000006100
  | 8, 0 => 0x200000000000020000000000002000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_8 roots_8 8 s ws hint
  | 1 => checkCutEntry dom_10 roots_10 7 s ws hint
  | 2 => checkCutEntry dom_0 roots_0 6 s ws hint
  | 3 => checkCutEntry dom_12 roots_12 6 s ws hint
  | 4 => checkCutEntry dom_14 roots_14 6 s ws hint
  | 5 => checkCutEntry dom_15 roots_15 6 s ws hint
  | 6 => checkCutEntry dom_16 roots_16 6 s ws hint
  | 7 => checkCutEntry dom_17 roots_17 6 s ws hint
  | 8 => checkCutEntry dom_9 roots_9 6 s ws hint
  | 9 => checkCutEntry dom_5 roots_5 5 s ws hint
  | 10 => checkCutEntry dom_11 roots_11 5 s ws hint
  | 11 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 12 => checkCutEntry dom_13 roots_13 5 s ws hint
  | 13 => checkCutEntry dom_4 roots_4 5 s ws hint
  | 14 => checkCutEntry dom_18 roots_18 5 s ws hint
  | 15 => checkCutEntry dom_19 roots_19 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_20 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_20 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_20 == dom_20) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_20 goalM u ys) : RunD dom_20 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_20 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 4 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 4 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 4 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_8 : ∀ i, 8 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 8 8 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 16 → Z 4 i = true := range_split z4_0 (z4_8)
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
theorem z5_56 : ∀ i, 56 ≤ i → i < 57 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 56 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 57 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (range_split z5_40 (range_split z5_48 (z5_56)))))))
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
theorem z7_144 : ∀ i, 144 ≤ i → i < 145 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 144 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 145 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (z7_144))))))))))))))))))
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
  scr dom_20 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_20 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_20 roots_20 goal_20 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_20 goal_20 := by
    have h0 : isConstB dom_20 goal_20 = false := by decide +kernel
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

end S_20

theorem low_20 : Lower dom_20 roots_20 goal_20 10 := S_20.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_20_bits : ∀ r : Fin 64, roots_20.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_20_lt : ∀ r : Fin 64, dom_20.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_20 T)
    (hlow : Lower dom_20 roots_20 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_20, Avail mask256 roots_20 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_20 hfan 0 roots_20 roots_20 rfl hsup0
  set out := (execN C.gates roots_20).getD C.output 0
  have hout : out &&& dom_20 = T &&& dom_20 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_20_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_20 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_20_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_20).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_20)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_20.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_20 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_20).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_20 &&& mask256 = dom_20 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_20 = T &&& dom_20 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_20, hd63, hout]
  have hnc_m : ¬ IsConst dom_20 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_20 roots_20 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_20, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_20 roots_20 0 roots_20 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_20.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t :=
  lower_to_circuit6 fG goal_20 10 hT6 (by unfold IsConst; decide) low_20

def wit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.and, [11, 7]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_16827_aux

theorem PEqualNP.Outside.L_meta_16827 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4276940520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_16827_aux.wit, PEqualNP.Outside.L_meta_16827_aux.wmono, le_trans PEqualNP.Outside.L_meta_16827_aux.wsize (PEqualNP.Outside.L_meta_16827_aux.lower s hs), PEqualNP.Outside.L_meta_16827_aux.weval⟩
