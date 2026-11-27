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

namespace PEqualNP.Outside.L_meta_12316_aux

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
  let x := (((w &&& 4294967295) ^^^ seed) * 2654435761 +
            (((w >>> 32) &&& 4294967295) ^^^ seed) * 2246822519 +
            (((w >>> 64) &&& 4294967295) ^^^ seed) * 3266489917 +
            (((w >>> 96) &&& 4294967295) ^^^ seed) * 668265263 +
            (((w >>> 128) &&& 4294967295) ^^^ seed) * 374761393 +
            (((w >>> 160) &&& 4294967295) ^^^ seed) * 1274126177 +
            (((w >>> 192) &&& 4294967295) ^^^ seed) * 2869860233 +
            (((w >>> 224) &&& 4294967295) ^^^ seed) * 1640531527) &&& 4294967295
  let y := ((x ^^^ (x >>> 16)) * 2246822519) &&& 4294967295
  ((y ^^^ (y >>> 13)) * 3266489917) &&& 4294967295

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

def dom_0 : Nat := 0x4040404040404040
def goal_0 : Nat := 0x4040400040000000
def roots_0 : List Nat := [0x4000400040004000, 0x4040000040400000, 0x4040404000000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(14, 30), (14, 46), (22, 30), (22, 54), (38, 46), (38, 54)]
def r1sG : List Nat := [14, 14, 22, 22, 38, 38]
def r2sG : List Nat := [30, 46, 30, 54, 46, 54]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xcfc9dfd3
  | 3, 0 => 0xcfc9dfd3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x404040400000000040400000404000004000400040004000
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

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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

def dom_1 : Nat := 0x4444444444444444
def goal_1 : Nat := 0x4440440044000000
def roots_1 : List Nat := [0x4040404040404040, 0x4400440044004400, 0x4444000044440000, 0x4444444400000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x4040404040404040, 50, 54)] (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0x5050505050505050
def goal_2 : Nat := 0x5040500050000000
def roots_2 : List Nat := [0x4040404040404040, 0x5000500050005000, 0x5050000050500000, 0x5050505000000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0x5555000055550000
def goal_3 : Nat := 0x5440000054000000
def roots_3 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]

theorem low_3 : Lower dom_3 roots_3 goal_3 5 :=
  lower_iso [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_4 : Nat := 0x5555555500000000
def goal_4 : Nat := 0x5440540000000000
def roots_4 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 5 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0x5555555555555555
def goal_5 : Nat := 0x5440540054000000
def roots_5 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

namespace S_5
def pairsG : List (Nat × Nat) := [(10, 26), (10, 42), (12, 28), (12, 44), (14, 30), (14, 46), (18, 26), (20, 28), (22, 30), (22, 54), (24, 26), (24, 28), (34, 42), (36, 44), (38, 46), (38, 54), (40, 42), (40, 44), (50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [10, 10, 12, 12, 14, 14, 18, 20, 22, 22, 24, 24, 34, 36, 38, 38, 40, 40, 50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [26, 42, 28, 44, 30, 46, 26, 28, 30, 54, 26, 28, 42, 44, 46, 54, 42, 44, 54, 58, 54, 60, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_5.map (· &&& dom_5)
def goalM : Nat := goal_5 &&& dom_5
def NN : Nat → Nat
  | 3 => 1
  | 4 => 6
  | 5 => 19
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x2ae69924
  | 4, 0 => 0x1cc98f361308e48312c7f4200f3f7dc20c9ac91e02794a43
  | 5, 0 => 0xa503cea293787a54616ad6cd4e4b6a1e3c2f2c4e345db57f31c95a622ea4846326d2e27b209953101ea18bd81a3d9d9117b655ee175bf37816a6373313afef9c1355d8d112461eb0018fa1c0
  | 6, 0 => 0xe96adfea85d3f3cd616ad6cd2957f7c71a3d9d9112ad22850c99170a
  | 7, 0 => 0xc99170a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x11115555111155551111111111111111105010501050105000550055555555550055005500550055005000500050005000005555000055550000000055555555
  | 0, 1 => 0x44440000444400004440444044004400440044004400440044000000440000004040404040404040404000004040000040004000400040001515151515151515
  | 0, 2 => 0x55005500000000005500000055000000544454445444544450505050505050505050000050500000500050005000500044444444444444444444444400000000
  | 0, 3 => 0x55555555000000005555550055005500555500005555000055505550550055005550000055000000554055405540554055400000554000005500550055005500
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xdde914
  | 4, 0, 0 => 0x3bcbd22bfec9ab5fe7148affb8a397fdc44abff5a915
  | 5, 0, 0 => 0xff6f6a45bfde62916ff71483d818a44205ff715a49bfdc522a6ff71489dbfdc4a2b607fb488d41fc50c15ee2f48c1bfdc52226ff7148a1bfdc522c6ff7148a5bfdc52246
  | 5, 0, 1 => 0x3fdd6291607e911857fdc52236
  | 6, 0, 0 => 0x3fdc5271607f148857fdc52236ff7148ad81fed2235ff71494581fee2915
  | 7, 0, 0 => 0x1fee2915
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 24
  | 4 => 29
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf3fcbff32c8c30e38c3cffff3cf3c030e38003f03f000fff
  | 0, 1 => 0xc034000c03300003300000000c330000300000030ff3ccf
  | 0, 2 => 0xc30000c00c000cd37f30e3bc30038000003c0cd3730cd000
  | 0, 3 => 0xfff000ff0c3ffc0fc0f3ec3ff00c00c3cf3fc00f00c30c3f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xa378aea2288cb6aa8c148fd514820014820003702a000dd5
  | 0, 1 => 0x5c87515dd77349557348055114c330148310004130eb3ccf
  | 0, 2 => 0xeb702ae80dd5ffffffb6ebbcb48b94a269bc5dd7735dd222
  | 0, 3 => 0xfff22afffffffc8fd5fffffffc8fd5fffffffc8fd5eb7dff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 24 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 24 (i % 8)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 3 => 3
  | 4 => 15
  | 5 => 23
  | 6 => 4
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0x466f897528b44f9918ff61a4
  | 4, 0 => 0x7b5fe0e66bc6ad0862865e7d482ccf6f3c4392bf3484e23b31ed9f052d1c7f71294674112495b66f1a7549e10c99170a067901b304d4737d044e8641
  | 5, 0 => 0xe96adfea9ec9730685d3f3cd5f32b75e5afa38844c93db9b4ad47ae34a8681083ee011903be4ac673b4d48c62957f7c71e19899d143eac4b12ad22850d4f12330c99170a0ae76306040787cf02587f5e01faf53b0095fe58005183e9
  | 6, 0 => 0x5f32b75e4a8681083ee0119001faf53b
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x11408d20200000000
  | 4, 0 => 0x20000000200000002000000010000000200000000000c01000004c102000411010000000000041100000000000000000100000002000c0100
  | 5, 0 => 0x100000000000000020000000100000001000000000000000000000000000000000000000300000000000000000000000100000003000000010000000100000000000801000000000000000001000000000000000300000002
  | 6, 0 => 0x1000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_1 roots_1 5 s ws hint
  | 1 => checkCutEntry dom_2 roots_2 5 s ws hint
  | 2 => checkCutEntry dom_3 roots_3 5 s ws hint
  | 3 => checkCutEntry dom_4 roots_4 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_5 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_5 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_5 == dom_5) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_5 goalM u ys) : RunD dom_5 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_5 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_16 : ∀ i, 16 ≤ i → i < 19 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 16 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 19 → Z 5 i = true := range_split z5_0 (range_split z5_8 (z5_16))
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
  scr dom_5 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_5 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_5 roots_5 goal_5 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_5 goal_5 := by
    have h0 : isConstB dom_5 goal_5 = false := by decide +kernel
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

end S_5

theorem low_5 : Lower dom_5 roots_5 goal_5 8 := S_5.noCircuit

def dom_6 : Nat := 0x3333333333333333
def goal_6 : Nat := 0x3220320032000000
def roots_6 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 8 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_7 : Nat := 0xf0f0f0f0f0f0f0f
def goal_7 : Nat := 0xe080e000e000000
def roots_7 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 8 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_8 : Nat := 0x5555000000000000
def goal_8 : Nat := 0x5440000000000000
def roots_8 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 4 :=
  lower_iso [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_9 : Nat := 0x3333000000000000
def goal_9 : Nat := 0x3220000000000000
def roots_9 : List Nat := [0x2222000000000000, 0x3030000000000000, 0x3300000000000000]

theorem low_9 : Lower dom_9 roots_9 goal_9 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_10 : Nat := 0xf0f000000000000
def goal_10 : Nat := 0xe08000000000000
def roots_10 : List Nat := [0xa0a000000000000, 0xc0c000000000000, 0xf00000000000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9

def dom_11 : Nat := 0xffff000000000000
def goal_11 : Nat := 0xfee8000000000000
def roots_11 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]

namespace S_11
def pairsG : List (Nat × Nat) := [(49, 51), (49, 53), (49, 57), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [49, 49, 49, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [51, 53, 57, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_11.map (· &&& dom_11)
def goalM : Nat := goal_11 &&& dom_11
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x118f7011
  | 4, 0 => 0x7653158a2f30dbf11b52d4db03f05d36
  | 5, 0 => 0xe10825b3680c674b2d040a84
  | 6, 0 => 0xe10825b3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfafa000000000000f0f0000000000000eeee000000000000cccc000000000000aaaa000000000000333300000000000000ff000000000000000f000000000000
  | 0, 1 => 0xfffc000000000000fff0000000000000ffcc000000000000ffaa000000000000ff00000000000000fcfc000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x98754
  | 4, 0, 0 => 0xd96435964305063214cb6435
  | 5, 0, 0 => 0x96434096324a96435
  | 6, 0, 0 => 0x96434
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1c71c003f038007fc71ff03f
  | 0, 1 => 0xff8fc0e38e07e001f8
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xbdf9d26ff4b924fb460db009
  | 0, 1 => 0xfffff6fbdf6ff24dfb
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 2 => 1
  | 3 => 4
  | 4 => 8
  | 5 => 2
  | _ => 0
def CH : Nat → Nat → Nat
  | 2, 0 => 0x35e5be46
  | 3, 0 => 0xe10825b369802de124f99c370eeb4d80
  | 4, 0 => 0xe10825b3680c674b2d040a8427840a8b1ee4ad2d1b54102e0a648355009ba7cb
  | 5, 0 => 0x1ee4ad2d1b54102e
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x0
  | 3, 0 => 0x200000400001
  | 4, 0 => 0x1000000000010000000000200000400000
  | 5, 0 => 0x2
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_8 roots_8 4 s ws hint
  | 1 => checkCutEntry dom_9 roots_9 4 s ws hint
  | 2 => checkCutEntry dom_10 roots_10 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_11 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := z5_0
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
  scr dom_11 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_11 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_11 roots_11 goal_11 7 := by
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

theorem low_11 : Lower dom_11 roots_11 goal_11 7 := S_11.noCircuit

def dom_12 : Nat := 0xffff0000ffff0000
def goal_12 : Nat := 0xfee80000fe000000
def roots_12 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffff000000000000, 19, 51)] (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xffffffff00000000
def goal_13 : Nat := 0xfee8fe0000000000
def roots_13 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 8 :=
  lower_iso [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_14 : Nat := 0x808080808080808
def goal_14 : Nat := 0x808080008000000
def roots_14 : List Nat := [0x800080008000800, 0x808000008080000, 0x808080800000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 4 :=
  lower_iso [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_15 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_15 : Nat := 0xaaa8aa00aa000000
def roots_15 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888888888888888, 49, 51), (0xa0a0a0a0a0a0a0a0, 49, 53)] (by decide +kernel) (by decide +kernel) low_14

def dom_16 : Nat := 0xcccccccccccccccc
def goal_16 : Nat := 0xccc8cc00cc000000
def roots_16 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def dom_17 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_17 : Nat := 0xf0e0f000f0000000
def roots_17 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 6 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16

def dom_18 : Nat := 0xff000000000000
def goal_18 : Nat := 0xe8000000000000
def roots_18 : List Nat := [0xaa000000000000, 0xcc000000000000, 0xf0000000000000]

theorem low_18 : Lower dom_18 roots_18 goal_18 4 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10

def dom_19 : Nat := 0xff000000ff0000
def goal_19 : Nat := 0xe8000000000000
def roots_19 : List Nat := [0xaa000000aa0000, 0xcc000000cc0000, 0xf0000000f00000, 0xff000000000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000000000, 19, 51)] (by decide +kernel) (by decide +kernel) low_18

def dom_20 : Nat := 0xff00ff00ff00ff
def goal_20 : Nat := 0xe8000000000000
def roots_20 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_20 : Lower dom_20 roots_20 goal_20 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff0000, 35, 51)] (by decide +kernel) (by decide +kernel) low_19

def dom_21 : Nat := 0xffffffffffffffff
def goal_21 : Nat := 0xfee8fe00fe000000
def roots_21 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_21
def pairsG : List (Nat × Nat) := [(9, 25), (9, 41), (10, 26), (10, 42), (11, 27), (11, 43), (12, 28), (12, 44), (13, 29), (13, 45), (14, 30), (14, 46), (15, 31), (15, 47), (17, 25), (18, 26), (19, 27), (19, 51), (20, 28), (21, 29), (21, 53), (22, 30), (22, 54), (23, 31), (23, 55), (24, 25), (24, 26), (24, 28), (33, 41), (34, 42), (35, 43), (35, 51), (36, 44), (37, 45), (37, 53), (38, 46), (38, 54), (39, 47), (39, 55), (40, 41), (40, 42), (40, 44), (49, 51), (49, 53), (49, 57), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15, 17, 18, 19, 19, 20, 21, 21, 22, 22, 23, 23, 24, 24, 24, 33, 34, 35, 35, 36, 37, 37, 38, 38, 39, 39, 40, 40, 40, 49, 49, 49, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [25, 41, 26, 42, 27, 43, 28, 44, 29, 45, 30, 46, 31, 47, 25, 26, 27, 51, 28, 29, 53, 30, 54, 31, 55, 25, 26, 28, 41, 42, 43, 51, 44, 45, 53, 46, 54, 47, 55, 41, 42, 44, 51, 53, 57, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_21.map (· &&& dom_21)
def goalM : Nat := goal_21 &&& dom_21
def NN : Nat → Nat
  | 3 => 2
  | 4 => 10
  | 5 => 42
  | 6 => 162
  | 7 => 239
  | 8 => 60
  | 9 => 9
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xc597d1ac06bcc6b9
  | 4, 0 => 0xaa0ca8e69decead88097eb7742b60c0439cec581234eb6541c42a7fb1079b6eb0575a84d0502e0f1
  | 5, 0 => 0xcf80ae968c99442979d9a4354e81769e4b3690a341a1761f3e57230339c2cfd7372859ec36f9b68d3468c70529feb8342951a73f27cbeeae264e56c621ac1dc3217987531f12c6571d7e74fb1ce94e6a1bc0db1d1a76de951a5ada951954a0e2170ee66415d49a53155b2d5110087e310ef97c600e7081710c1216110a27bdda0799c75506b20dfc04b80f02049565ee042e3b4e03f46b1a03792ff3035b74c001aa9170003b48ea
  | 6, 0 => 0x1f7f83161e0879a11db7f4151cff09f11c6e90ba1b41778c1a2b112719cefab51933962018c4205a17b182b6170ee66416cace8c15e9940615d7c7341541688b14e73b7914c2acd0147b51ed13ae0da41396afdb13690b42133edf4912ed49ab12cf542212b2c88512a11da41233ad471222530510df928410a9fb8c0fb2d9df0fa0da7c0efd143c0d683c9f0d227c4c0cfe41cc0c69d3150b667d500aa1e2e4097a578b08d426dc08a2b794089fa4b3080da96807d1bf7d05f864170598520405344eba052e51a6051ef7b805154ba804ba232504b3e1a303f7214a03b475a10379881e034fc2ba01b60d60016ea173011aa5f500abf404007021fb00423292
  | 6, 1 => 0x4e2217624d5287954c4c5e1a4bf390814b631e1948fc36d94873ef5c484d005247e4411146c73b7a45d842c744cbe81942f27aab41fabde64107a38340bad85f405fc97240410a5a3f1627303eb3446d3d6089e83d1458ad3c70aefe3af0f19f3ad326513a426bcb3a34b385392fe44f38e1494e38af9115387e237438419cde37c29f1c32fc7e7c315544b43120bd6530633a7c2fe4b1f62f7710362eb0b80b2e9cc7f72dcd32372bbbea0d2b4508fd2a6fdd9f29490db728ace90e28657fd22864a64228459dec284250ea27addd5e276a298c2707a0ad2518458d2492433424529a9b2374b28423282e1e2207336a21442de62141c228200dd86c1fbafc12
  | 6, 2 => 0xf4da21f0e2165b9bdbcc96d3d7154d41cdd983abc864df7ac2b4f8e6af5b08859ffbbb3c9535d63c92f5f5ec91dd14e3898984eb83d73ee1833bb76a80397c747ed849657a4e7488778508c875462c7d72b0ab21700bfd026f3967d76be093ef6b67b9c169a0b39f653b7c16652b27a2637694805a9b899559e3c8af58b8af755738c896540db023
  | 7, 0 => 0x10a751f0108dfb0010873aff101ce1fd0ed51c0e0ed4b88e0ebd04280e9332a10e00d3cc0def792c0d4c96070ce919930ce6e2370c5352510c1b94cd0bf806d30b53118e0b4ad8bb0b0ab8450a9cd3050a91fbbe0a61674a0a3a77c00a3643350a2aaf470a0b7c4e09d60ff9097f4255094cec4208a20bcc08238d8808118e2207b7fb5607ac332c07942f90078ccce506e4c9e706d2616606d1977a06d133fa0674bcee0620bd3c0601190805e0f05005dba0bf054ee0f8050cdc2204f63fa4041660d7036b5209035871b402dccc8f029ca9130288bdb3023e56a5020a349501ccb6d20188bf7200d506e100a8eff10096dc1100837c32006645eb0040134f
  | 7, 1 => 0x2c05dd8b2bf5fe322b462ec52b0c54332aa75ad22a20277c29dd6ad429d26b1a28acf73c2731a19f25d1e1fb259c3aeb2597e26925335e492518219f246a0b8a2308cf9f22ea378e2284b33322272e9b220099e72185dc3721241f8e2048dd1a2044e8021da1c6791d33b5511ca711891c6686f61beeb5211bb8628c1b9c93d61b63da9f1b4c51111a39bb48196a13e918b8103a18917f94184e84e31805cbd217e6302e17350d61172a701e17269c0e1702826616bb565d1643ac261609134215e3d4b9159e41e51590135b1583f51b14cd3334149a4ea113d3a91313754c0d132e38c2130e3cd912db5da6128628ed123fbccc1227f09d1218d9d31182c6e9
  | 7, 2 => 0x69bc6b26698f8f7769506ea266484c30650679ec635f46a760e85aa460b8a64c5edb0f5c5ed0dd965eb582935e7afffb5e07b1425dd97bc65da183575c4850ef5be7ee235b93d2de5aca5d735ab8a9c85a757c2359e3c8af56cd3b85558827b052f350ad4e4d12634d6207e44cf3eddf4a964121480551b347aac9ba477c54b94675a5fc462698db440413af43f4158c4191ff463f4701b43e4085f23c91b66f3bd23dc43b0292b93a9b07b93a5ac952394be1b837f8c4e6364efb0935e94e9c350e8d4332c69f343274995130dee2fd2f953ec82ed9e3df2e9f02ad2e385f5e2ddbe4da2dd3a3392da2257a2d0b08af2c447f832c235b482c225fc52c076221
  | 7, 3 => 0xf6b5bc52f25e3feedd5c2e0fdd09945fd7154d41cc78d20ecb488ab3c5a3ca78c3e64925c159350cc1438dfbc073b950be5b316fb574c2ceb22773e5b1dae2d0aa9730b5aa8ef7e2a81ce379a1ac26f5a0a58af5989e913d9867eae98e902fad8d696afe8a65f27886dc0689868aede1809c81347ed849657e15ec8c7ddb6c327d4a419d7d449c497c9b983a7c85f1297abee64576d149dc73b23fea719816ba711fee546cd23b446c9455026b9d21576b26204769f8150969f194fb
  | 8, 0 => 0xf61649e1cb5da1a9ca94fea2bb5f66ffb9daa94fb158ad0faf0a244ea5dd0329a04f7c217a5bb7ea67108e52611f66575a0f56b158871ddb538ed0be50d632f7509f8ca34c8d80f449dfd61947e5621745c5716343cfd0223f521ef63cc11777375c328c36c151b135db23933578c84e34f9221f34bd92e3327c9e7a315f0dca2cc710002c33b37427928aca25e0085924f1d90e241a19e723bebf2121f40ce01e08fcca1c1160c61c02e4e51b96e8611ae5543517c0281516ed244d14c25be7141f8fdd10af57190db3a33c0d2c2e2909703723093db680052b8f990451cc9a020fff7e0193adbd00f26ece009cec3f
  | 9, 0 => 0xf61649e1b158ad0fb03b1c5f8f8b65ae69904ec93e51fe3b3ba453601957081117a485a0
  | 10, 0 => 0x69904ec9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffffffffff0000ffff0000ffff0000ffccffccffcc0000ff00ff00ff000000fafafafafafa00000f0f0f0f0f0f000000ff00ff00ff00000000ffffffff
  | 0, 1 => 0x3333330033333300330033003300330011ffff0011ffff001100ff001100ff000fffffffffffff000f000f000f000f0005ffff0005ffff0003ffff0003ffff
  | 0, 2 => 0xfa00fa000000000055ffff0055ffff0055ffff0000000000555555ffffffff005555550055555500550055ffffffff00550055005500550033ffff0033ffff
  | 0, 3 => 0xff00cc00cc00cc00ff0000ffff000000ff000000ff000000ff00000000000000fe00fe00fe00fe00fcfcfc00fcfcfc00fc00fc00fc00fc00fa00fa00fa00fa
  | 0, 4 => 0x101ffff0101ffff01010101ffffffff00ffffffffffffff00ffffff00ffffff00ffffff0000000000ff00ffffffffff00ff00ff00ff00ff00ff00ff00000000
  | 0, 5 => 0x111111111111111111110000ffff00000f0f0f0f0f0f0f0f050505050505050503ff03ff03ff03ff03570357035703570303ffff0303ffff0303030303030303
  | 0, 6 => 0xaaaaaaaaaaaaaaaaaaaaaa00aa00aa00aaa8aaa8aa00aa005555555555555555333333333333333333003300ffffffff1111ffffffffffff1111ffff1111ffff
  | 0, 7 => 0xccccccffccffccffcccccccccccccccccccccc00cc00cc00ccc8ccc8cc00cc00aaffaaaaaaffaaaaaaff0000aaff0000aaaaffffffffffffaaaaffff00000000
  | 0, 8 => 0xeee00000eee00000ee00ee00ee00ee00ee000000ee000000e0eee0eee0eee0eeccffccffccffccffccffccffccccccccccff0000ccff0000ccff000000000000
  | 0, 9 => 0xf0e0f000f0e0f000eeeeeeeeeeeeeeeeeeeeeeee00000000eeeeee00ee00ee00eeeee0e0e0e0e0e0eeee0000eeee0000eeee000000000000eee0eee0eee0eee0
  | 0, 10 => 0xfa00fa00fa00fa00fa00fa0000000000f0fffffff0f0f0f0f0fff0fff0fff0fff0fff0fff0f0f0f0f0f0f0fff0fff0fff0f0f0f0f0f0f0f0f0f0f000f000f000
  | 0, 11 => 0xfca8a8a8fca8a8a8fc00fc00fc00fc00fafafafafafafafafafafafa00000000fafa0000fafa0000fafa000000000000faeafa00faeafa00fac8fac8fac8fac8
  | 0, 12 => 0xfe000000fe000000fcfcfcfcfcfcfcfcfcfcfcfc00000000fcfc0000fcfc0000fcfc000000000000fcecfc00fcecfc00fca8fca8fca8fca8fca8fca800000000
  | 0, 13 => 0xfef0fef0fef0fef0fee8fee8fee8fee8feccfeccfeccfeccfeccfeccccccccccfeaafeaafeaafeaafeaafeaaaaaaaaaafe00fe00fe00fe00fe00fe0000000000
  | 0, 14 => 0xff000000ff000000ff00000000000000fefefefefefefefefefefefef0f0f0f0fefefefe00000000fefeaaaafefeaaaafefe0000fefe0000fefe000000000000
  | 0, 15 => 0xff00ffff00000000ff00ff00ff00ff00ff00ff0000000000ff00cc00cc00cc00ff00aa00aa00aa00ff0000ffffff00ffff000000ffffffffff000000ffff0000
  | 1, 0 => 0xffaa000000000000ff330033ff330033ff050505ff050505ff03ff03ffffffffff03ff03ff03ff03ff03ff0300000000ff00ffffffffffffff00ffff0000ffff
  | 1, 1 => 0xffcc000000000000ffaaffaaffaaffaaffaaffaaaaaaaaaaffaaffaa00000000ffaaaaaaffaaaaaaffaaaaaaaaaaaaaaffaaaaaa00000000ffaa0000ffaa0000
  | 1, 2 => 0xffee0000ff000000ffee000000000000ffccffccffccffccffccffccccccccccffccffcc00000000ffccccccffccccccffcccccc00000000ffcc0000ffcc0000
  | 1, 3 => 0xffeeffeeffeeffeeffeeffeeff00ff00ffeeffee00000000ffeeff00ffeeff00ffeeff00ff000000ffeeff0000000000ffeeccccffeeccccffee0000ffee0000
  | 1, 4 => 0xfffa000000000000fff0fff0fff0fff0fff0fff0f0f0f0f0fff0fff000000000fff0f0f0fff0f0f0fff0ccc0ccc0ccc0fff00000fff00000fff0000000000000
  | 1, 5 => 0xfffafffafafafafafffafffa00000000fffaff00fffaff00fffaff00ff00ff00fffaff0000000000fffafafaff000000fffa0000fffa0000fffa0000ff000000
  | 1, 6 => 0xfffcff00fffcff00fffcff00ff00ff00fffcff00fcfc0000fffcff0000000000fffcfcfcfffcfcfcfffc0000fffc0000fffc0000ff000000fffafffaff00ff00
  | 1, 7 => 0xfffeff00fffeff00fffeff0000000000fffefefeff000000fffeccccfffeccccfffe0000ff000000fffcfffcfffcfffcfffcfffcff00ff00fffcfffc00000000
  | 1, 8 => 0xffffccccccccccccffffaaaaaaaaaaaaffff111111111111ffff00ff00ff00ffffff005500550055ffff0000ffff0000ffff000000000000fffefffeff00ff00
  | 1, 9 => 0xfffffff0fff0fff0ffffffccffccffccffffffaaffaaffaaffffff00ffff0000ffffff00ff00ff00fffffa00fa00fa00fffff0f0f0f0f0f0ffffeeeeeeeeeeee
  | 1, 10 => 0xffffffffff000000ffffffff00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xd0c27e6e4b4775d4e4
  | 4, 0, 0 => 0xbe77513e375d0c27e61585c27d503d365c2ab7e664e5d0b7775d4e59a774f3e3759b7d513e375d0c27e625d5bb68513e375ab77663e375
  | 5, 0, 0 => 0xc2b97d514e376d0a87e514e3e6d1ad77513e376cbc27d513f376d0a87e513c376d0c2a67e584e6d0c27e665b4d6c2938c7e514e6d07e77645d4e6d0c27e665d496ab775d513e376cca57e5c3e376b0a87d513e376d0c27e503f376d07e77503e366d0a17e664a376
  | 5, 0, 1 => 0xc2b97d513e356d0bf67513e376bb7e73513e376b8b17e513e376cba17d513e376c2ac7d513e37600b17d513e375c2948d7e514d6c2be7e513e376d0c27e5d4e196977e7d513e376c2aa7d513e376d0c27e59513e6d0c27e5d473e6d0977e513e376d0cb77503d376
  | 5, 0, 2 => 0x7d7751493e376d0c27e523f376d0bf77513e376d0c29c7e665d6b47764513e376cbc27f513e376d0cb7a513e376c2bd7e513e376d0c27e503d366d0ab77513e376
  | 6, 0, 0 => 0xd0bca97e513e377cbc2c17d503e37700c27e665d4e006d0cca57e5d3e377d0c27e635d3e377cbc9c27d513e377c2c17e513e38377d0c27e513e372e7d0b17e65513e377c27e66513e37237d0c2a67e613e377d0c1a17e663e377c2b87e513e37217d0c2a87e513e377d0c2877e5d513e7d0ccaf7e513e377
  | 6, 0, 1 => 0xd0c27e6d5c51377005137332106006d0c2c17e6f3e37700d0c2665d4e216c29d967e513e377d0c27e513e3731700d077513e37016d0cfc27e513e367d0cbc27b513e377d0c27e514b3e377c1a4a17e513e377c27e55513e3723700d0cb77513e366c2a69d7e513e37700d07e513e37096cbc2937e513e377
  | 6, 0, 2 => 0xd0c27e513e370c7d0c27e513e371f7d0c5c27e513e377d07e7167513e377d0c29e7e5d513e7d0c2b057513e377d0c27e60513e377d07e7d71513e37700d0cb773e372d6c27e7d665c3e37700d07e6b513e066d0c2a27e513e37700c29e7d513e376d0cb9277513e377cbc27e7d503e377d0c27e6c5c51377
  | 6, 0, 3 => 0xd07d7764513e377c2ae7e77513e37700c2a6573e37006d0c2847e513e37700d0c27e655d4e6d1c27e513e37137d08b7e77514a3e7d0a17e513e371d700d0a97e5137336d0c27e6a66513e7c29e7d514d3e37700d0977e513e376c2b87e7d513e37700d0c27e6658376d0ad775d513e37700c17d773e372d6
  | 6, 0, 4 => 0xd0c2a77e513e377d0c27e513e37327d0c27e513f37017d0c2a6887e5d3e7d0c2a58d7e5d3e7d0c3c27e513e377c28c7e65513e377c27e73513e37217d0c27e655b3e377007e73513e37066d0c2a47e5d4e3e700d0cb513e37246d0c2827e513e377d0cbc276513e367c27e73513e37267c2c1ae7e513e377
  | 6, 0, 5 => 0xd0cb7766513e37700c237332d21006d0c28e7e65514e7d0c2867e513e377d0c2c17e665d4e7d0c27e514c3e377d0c2b57e513e377d0c27e77665d4e7c29a7e514e3e377d0c2b67e513e377d0c27e513e37157c2b97e7d513e377d17e77514a3e377d0cb9577513e377d0cdcb77513e377d0c27e513e371a7
  | 6, 0, 6 => 0xd0c27e513e37177009d7e513e37066d0987e513e370d700c27e79513e34600d07e34332d066d0c27e513e370b7c2938c7e513e377d0c2a68e7e664e7d0c27e514e37197c27e7d73513e377c17d7766513e377d0bf7e71513e377c1907e7d513e377d0c27e513e3714700d0c28e5751336d0c29c51453e377
  | 6, 0, 7 => 0xd0c27e513e37057d0c27e513e37037cbc27d513e37077d0c2857e513e377c2adab7e513e377d0c2c1a6573e37700c27e513e34236d0c27e513e37087d0c27e513e3727700d0c27e513d36600c2b8513e37216d0c27e513e371b7c27e7d51493e37700d071513e37216d0c29c7e4f3e377c7c17d77513e377
  | 6, 0, 8 => 0xd0c2c07e513e377d0c17e78513e37700d069513e37066d0c27e5f513e377d0c27e503e37017d0cbc27e503e367d0807e513e371e7d0c2c17e503e367d0c17e71513e377d0c27e513e372a7d0c27e70513e377d0c27e51443e377d0c27e513e37187c29e9d7e513e377007e5134330600600c27e513e37266
  | 6, 0, 9 => 0xd0c2c169513e377d0c2817e513e377d0cbc281513e377d0c27e665d4e217d0c27e51403e377d07e7170513e377d0c27e6f483e377d0cbc27e523e377d0c2c17e523e377c17d77513e3707700d0c2513e371b600d080513e3721600d0c234332d216d0cac27e513e377d0c27e513e37017cbc27d513e37017
  | 6, 0, 10 => 0xd0c281513e37047007d77513e37076
  | 7, 0, 0 => 0xd0cc8d7e513e377d0c27e513e3b3721800c2c1937e513e377d0cbc27e513e37078d0c299887e513e378d0c27e5d56513e37800d0c27e3e372d20700d07e51433e37067d0c2c17e513e3937800d0c2947e513e347d0c9c17e77513e37800d0c6c27e3e372d7d0c2c17e7c513e378d0c28c7e77513e378d0c2c19f7e513e37800d0cc7e7d3e372d7
  | 7, 0, 1 => 0xd0c27e513e37307d0c2958e7e5d513e800d0c27d775137337d0c28e7e64513e378d0c2998e7e513e378d0c2b07e5c513e378008e7e513e370600700c27e773e372d00700d0c27e7d3e342d700d0957e513e34067d0c2ba7e7d513e37800d0c2a5513e3721700d0c2837e513e377c2c17e7d513e3707800d07e513e3711067d0c27e7d513e372f8
  | 7, 0, 2 => 0xd07e77514a3e377d0c27e514a3e3721800c28e7e5d513e00700c27e513e3421007d0c27d77514e3e37800d0c2513e37211c700d0c27e64513e34700c266513e3721007d0c27e66513e37298d0c2897e77513e378d0c2c17e513e370a800007e513e34060060000d0c2955e51376d0c28d7e7d514e3e8d0c27e77513e370a8d0c27e66513e372b8
  | 7, 0, 3 => 0xd0c2907e5d513e3780000c27e51343300600d0c2c13e372d217d0c27e51423e3720800d08e513e372106700d0c2773e372d217d0c28e7e7d514e3e8d0cecbc27e513e37800d0c27e665c3e377d0c7c2a67e513e37800d0c253513e372170000d0b27e513e376d07e776664513e378d0cec2c17e513e37800d0c27e51373311700d0cbc27e503e377
  | 7, 0, 4 => 0xd0c28e51373321700c2a17e513e37007d0c2c18a7e513e378d0c27e54514e3e37800cbc2c17d513e37700d07e66513e34067d0c27e7d665d3e378d0c27e6463513e378d0cbc17e77513e37800d0c28e5d513e217d0c27e5d513e370e800d0c27e545137337d0c2a1957e513e37800d0c27e3e372f2d700d0c2b87e513e3770000d0513e3421066
  | 7, 0, 5 => 0xd0c2c1a07e513e378d0c27e76514e3e378d0c27e655e513e378d0c29e7e514e3e378d0c2957e513e372080000d0c251343321600d0c27e76513733700c27e7977513e377d0c2a4a17e513e378d0c2c17e5a513e37800d0c2a47e663e377d0c27e6f514e3e37800d0c2937e3e372d7d0c2957e665137218d0c27e74514d3e37800c27e513e3724007
  | 7, 0, 6 => 0xc27e66514e37007d0c28e7e513e3707800d0c6c2513e3721700d07e51463e3706700d0c2513e372119700d0c265513e37217d0c27e66513e3724800cbc27e7d513e377d0c27e6f4e463e37800d0c2a1513e37217d0c27e77514d3e37800d0c251433e3421700c27e513e372800700d0c28e7e4e3e2d700d0c27e71513e377d0c2957e58513e378
  | 7, 0, 7 => 0xd0c269513e37600d0c2a68e7e5d3e7d0cbc2c17e513e36800d0c266514e3721700d0c27e513e3710700d0c2957e3e342d7d0c27e513e3707048d0cbc2a67e513e37800c277513e3721007d0c27e66513e3720800d0c2b77e513e377d0c6c27e66513e37800d0c27e513e34077d0cc7e7d66513e378d0c27e66513e3719800d0c2513e3728217
  | 7, 0, 8 => 0xd0c2ba513e3721700d0c2513733211d7d0c2907e513e37218d0cbc27e513e3701800d0c251413e37217d0c27e514a453e378d0c2c17e513e37018d0c2938f7e513e37800d07e5c513e37067c2c1a57e7d513e378d0c2c17e513e371c800c2ba7e513e37007c2c1a67e7d513e378d0c28e7e513e370a8d0c7c6c27e513e378d0c27e7266513e378
  | 7, 0, 9 => 0xd0c27e64513e3729800d0c27e463e372d7c2c17e7d5d513e37800d0c2a67e664e377d0cbc27e5d513e378d0c27e77513e370f800d0c27e51493e377d0c2a5947e513e37800d0c2c17e5134337d0c2a6947e513e378d0c2b37e77513e378d0c2a37e514e3e378d0c27e513e3937078d0c2c17e513e37028d0c2c18e7e5d513e800d0c17e77513e347
  | 7, 0, 10 => 0xd0c27e75513e3721800d0c27e6b66513e700d07e75513e37067007e5d513e370600700d0c266513e3421700d0c27e513e3718700c2927e513e3700700c27e7d513e37077d0c18e887e513e378d0c2c17e66514e37800d0c2917e513e377d0c27e5d514e3e218d0c28e7e513e37128d0cbc6c27e513e378d0c2c17e513e37288d0c7c27e513e37218
  | 7, 0, 11 => 0xd0c27e37332d21700c2513e37211d00700d0cbc27e513733700d0c27e513e342470000cbc27d513e376d0cbc27e513e37218d0c27e6564513e378d0c7c27e76513e378d0c2a69f7e513e378d0c2c17e57513e378d0c27e513e372c21800d0c27e513e3a377d0c8c2c17e513e378d0c2887e513e371680000d0c27e6f3e37600d0c27e61513e377
  | 7, 0, 12 => 0xd0c27e513e371c700d0c2ba7e513e347d0c6c27e513e37078d0cbc27e76513e378007e513e37210600700c2c17e513e37227d0c27e5d513e370780000c27e513e37236d0c27e7d75513e378d0cbc2c176513e378d0c27e513e371d1c8d0c2958f7e513e37800d0c2a07e513e377d0c2c17e51433e378d0c28e7e513e372880000c27e79513e376
  | 7, 0, 13 => 0xd0c27e76513e370780000c17d77513e37600c2c17d513e3721700d0cbc2513e37217d0c27e513e372118800d0c275513e37217d0c27e513e3721078d0c29f7e513e3721800d051433e3721067d0c27e5d5a513e37800d0c277513e37207d0c2c1817e513e378d0c27e513e37201d80000d0c27e665d4e600d0c27e513e37017d0c2c17e513e37258
  | 7, 0, 14 => 0xd0c27e34332d6d0c2c17e513e3704800d0c2513e372107700c27e513e371d00700d0c2817e513e37700d0c27e513e3723700d0c2513e37201d7d0c27e513e37211c8d0c2c17e75513e37800d0cbc276513e3770000513e372106006d0c27e5d58513e378d0c2817e513e370780000d07e71513e376d0c4c2c17e513e378
  | 8, 0, 0 => 0xd07e3e372d066d0c27e7d514e3e37800d0c27e513e372c700d0c27e7d513733700d0c27e75513e377d0c2957e5d513e37800d07e7d513e37067d0c27e5d5c513e378d0c28e887e513e37800d0c9c27e513e37700d0c27e5d514e3e700d0c2a6513e37217d0c27e514e3e37218d0c28b7e77513e37800d07e514e3e37067d0c2c17e513e37078
  | 8, 0, 1 => 0xd0c2a67e5d3e37700007e513e3706006d0c2957e513e3721800d0957e513e3706700d0c2947e513e377d0c27e514e463e378d0c2c1a67e513e378d0c2a67e77513e37800d0c27e4e3e372d700d0c2513e372120700d0c27e513e372270000d0c27e37332d600c2c17e7d513e37700d0c25d513e3721700d0c27e3e372d21700d0cbc27e513e377
  | 8, 0, 2 => 0xd0c27e513e370a700d0c27e513e371d700d0c27d513e3721700d0c27e513e3707700d0c29f7e513e37700d0c2a67e513e347d0c2a68e7e513e37800d0c251433e37217d0c6c2c17e513e3780000d0c2513733216d0c2c17e5d513e3780000d0513e372106600d0c2887e513e37700d1c27e77513e37700c27e513e372100700d0c27e64513e377
  | 8, 0, 3 => 0xd0c2513e37216d0cbc2c17e513e37800d0c27e76513e37700d0c27e51433e37700d0c27d77513e37700d0c27e513e3721700d0c27e57513e37700d0c2c1513e37217d0c27e513e37211d8d0c2c17e76513e37800d0c2c17e5137337d0c2c17e513e37218
  | 9, 0, 0 => 0xd0c2513e37216d0c27e513e3721700d07e513e37066d0c27e5d513e37700d0c27e513e37600d0c27e513e346d0c28e7e513e377d0c2c17e513e377d0c27e77513e377
  | 10, 0, 0 => 0xd0c27e513e376
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 36
  | 4 => 44
  | 5 => 52
  | 6 => 60
  | 7 => 68
  | 8 => 68
  | 9 => 60
  | 10 => 52
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffffffffffc003fff0003fff000fe3bf8efffc003800e003fff0001ff47fdffcc00380fe03c03f0001ffc7ff0000000000fffffff
  | 0, 1 => 0x1c7e1c40710f0c71c07101c40001c0fffc010fffc7007ff004000003fffffffffffc0fc00f003c000038fffc002fffc01ffff0007fff
  | 0, 2 => 0x1c71ff400000007e3fff064bfff1f8fffc00000007e3992fffffff1f8e64819233307e0192fffffff1f80648192000071ffff01c7fff
  | 0, 3 => 0x1ff1e3878e00007fc000fffc0001ff00007ff00007fc00000000001ff1ffc7ff00007e07fe1ffbffc1f81ff87fe000071c7fd1ff4000
  | 0, 4 => 0xe00ffff800ffff803800fffffff1ffffffffffffc7fffff1ffffff1fffffc00000007fc7fffffffff1ff1ffc7ff00007fc7ff0000000
  | 0, 5 => 0xfc0e0438100303f00000fffc000e3fe03f80f00ff8e3802e00800cffffffffff000ffff993e64c003e07ffff801ffff81f801e004003
  | 0, 6 => 0x719b466dcccc01c000000333300019b0000cccffe3992e648cccfc7e1c78710f0f803800ffffffffc0ffffffffffff03fffe043fff
  | 0, 7 => 0x381ffc7fff0f00e078e1e3bc3c0380000000f0f000078c0003c3c1ff19b47ffcccc7fc0001ffc000007ffffffffffc01ffff0000000
  | 0, 8 => 0x7e000000000000003f3f000000000000000fc7ef1fbff001ff1ffc7fff0f07fc7ff1e3bc3c1ff00007ff00007fc0000000000
  | 0, 9 => 0x7e0ff000fc7ef1fbff3f03f1fbc00000000fc0000003f3f03f1f807e0fc000fc0001fbc00003f000000000000007e01f83f3f
  | 0, 10 => 0xffcc00000000000001fffffc7f0ff007fc7ff1ffffc01ff1ffc7f0ff007007ff1ffffc01c01fc07f0ff007000000003fc0
  | 0, 11 => 0x19b066cccc00000000003ffc1c71ff47fdffcc71c7fd00000001c700007fd000071c000000000000700007edffcc00078c1e33ff3
  | 0, 12 => 0x7e07fe1ffbffc1f81ff800000007e00001ff80001f8000000000000e00001fbbffc00019b066cfff000066c0000000
  | 0, 13 => 0x1c01fc07f0fffc0007ec1fb3fff0381e3878efffc0e078e1e3bc3c00719b466dfffc01c66d19b73330000000000fffc0000000000000
  | 0, 14 => 0xe000003800000380000000000001ff1ffc7fffffc7fc7ff1fc3fc01ff1ffc00000007fc66d1fff3331ff00007ff00007fc0000000000
  | 0, 15 => 0xe00fffc0000003803800e003fffe00e00000000038000000003c3ce000000000cccf8007fffffc000e000003fffffff800000fffc000
  | 1, 0 => 0xe0700000000003f1c071e1c4000e38e00b802003381f801fffffffe07e007801ffff81f8010000000e00fffffffffff803fff0003fff
  | 1, 1 => 0xe380000000000381fe6df9b7fffe07f9b466dcccf81fe6d0000000e0719b7e6dcccf81c66d19b7333e0719b4000000381c000f9b4000
  | 1, 2 => 0xe3f000380000038fc0000000000e38fe3bf8effff8e3f8e1e3bc3ce38fe3800000038e078efe3bc3ce381e3800000038e0000fe38000
  | 1, 3 => 0xe3fffbffefffff8fffefe003fffe3fffbc00000038ff800ffbffffe3fe00380000038ff8000000000e3f1e3bfeff0f38fc000ffbc000
  | 1, 4 => 0xfc700000000003f03ff0ffc3ffffc0ffc07f0ff03f03ff00000000fc01fc3ff0ff03f007801e03c3cfc00003ff00003f000000000000
  | 1, 5 => 0xfc7fff47fdffcff1fffd0000000fc7e003ffdfffff1f800e003ffffc7e0000000003f1c7fde000000fc70003ffd0003f1c000e000000
  | 1, 6 => 0xff8e003ffefffffe3800e003fffff8e0007fe0003fe38000000000ff81ffbffefff3fe0000fff8000ff800038000003f1fffde003fff
  | 1, 7 => 0xfffe003ffffffffff8000000000fff1fff8000003ffc78effffc3cfff00038000003fe3ffefffbfffff8fffb800fffffe3ffe0000000
  | 1, 8 => 0xfff1e3878ef0f3ffc66d19b7333fffe0438100303ffc7ff1ffc000fff06481920003ffc000fffc000fff00000000003ffffffe003fff
  | 1, 9 => 0xfffffc3ff0ffffffff8efe3bfffffff9b7e6dfffffff800fffc000fffe003800ffffffc0000003ff3fff1fc07f0ff03ffc7ef1fbff3f
  | 1, 10 => 0xfffffff8000003ffffff0000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xeadfab7fffc003ab70002aaa000eadfab7fffc003ab7eadffff000aad6ab5ffcc001807601c03f00000000000000000000eadd555
  | 0, 1 => 0x42a1c40400a081080400100000000eadc000aaa80000000000000009eaffabffffc0240080020000000eadc000aaa8003ab70002aaa
  | 0, 2 => 0xdb15205480000243bb70402aaa090eedc100aaa8243192eeddddd090c6481002220240100eedd5550900400100000010baf70102aaa
  | 0, 3 => 0xdb1520548000036c548fffd5550db1520548000036c54815200000db1520548000036f7fe1522aa80db1520548000036c5481520000
  | 0, 4 => 0xeadc000aaa8000000eadd5550dbffffffffffc36ffff1522aaa0dbfffc548aaa836c548fffd5550db1520548000036c5481520000
  | 0, 5 => 0x90080420100302400000eadd55562d603d80f00fd081002400800c2df3524d49000ca509012404003204eadc801aaac8108012004003
  | 0, 6 => 0x24f39b4e6dcccc93ce6d39b733324f39b4e6dcccf6c3192c648cccb46a1c68710f0ec12831eadd7d7900eadfab7fffe403ab78042aea
  | 0, 7 => 0x4b95e3978ef0f12e578e5e3bc3c4b95e3978ef0f12e578e5e3bc3c2df3db4f6dccccb7c5483db511124ffbffefffffc93feff1122aaa
  | 0, 8 => 0x6f61501fe75455891aa76a9ff3f6240001aa7545436c7e81fa3f004fb5f397cef0f13ed7ce5f3bc3c4fb15217ce50513ec5481520000
  | 0, 9 => 0x9d29fc27f0ff01bfdfef7fbff3f6ff7fbc548a8a9bfdfef7fbff3f6ff1fa07e8fc01bfc5487fbd5156ff15205480001bd9fe77f9ff3f
  | 0, 10 => 0xb04aad6ab5ffcec12ab50002aa29dbfffe7f8ffaa76e7f89fe3fc09db9fe27f8ff0274a7f09fc3fc09d29fc27f0ff0274a7f09fc3fc0
  | 0, 11 => 0xd6b19b36feddd34832b6cadbffcbdfbff6ffdffcef7effd1522aa2bdf1522ffd5546f7c5481520000bdfbff6ffdffcee76fbdbef7ff3
  | 0, 12 => 0xf240003ab755577ef7fedffbffcdfbdff8548aaa37ec548dff9554dfb152054800037ef7fedffbffcd6bdbfb6fefff35af6fe1122aa8
  | 0, 13 => 0xff6ffdfff7ffffffffffffffffffbdfefffbfffffef7fbf5e3bebef6ffbffeffffffdbfeff39b7bbbf24eadfab7ffffc93ab70002aaa
  | 0, 14 => 0xf240003ab75557c900000000000ffffffffffffffffffff9fe3feaffffffc548aaabffcf6dffff777fff1523fff5557ffc5481520000
  | 0, 15 => 0xf24eadc000aaabc93ab7eadfffff24eadc000aaabc912864a1bc3cf242894a25cccfc90000eadd555f240003ab75557c90000eadd555
  | 1, 0 => 0xf6f11204480003d98040ebdd555f24400bab75577c93ab7eadfffff24eadfab7ffffc93ab70002aaaf24eadfab7ffffc93ab70002aaa
  | 1, 1 => 0xfbd14205080003dbfefffbffffff6ffbfce6deeefdbfeff1122aaaf6f39b7effdddfdbce6d39b7333f6f39b4448888bdbc448fbfd555
  | 1, 2 => 0xfff1523fff5557ffc5481520000fbdfefffbfffffef7fbf5e3bebefbdfefc508aaabef578efeffd7dfbd5e38508a0a3ef4508fefd555
  | 1, 3 => 0xfffffffffffffffffffffffffffffffffc548aaabfffffffffffffffffffffffffffffffff1522aaafff5f3bffff5f7ffc548fffd555
  | 1, 4 => 0xfff15205480003fdbff7ffdffffff6ffde7f0ffabfdbff71502aaaff69fc3ff7ff57fd97c65f1bc3cff61503ff75557fd85401500000
  | 1, 5 => 0xffffffeffdffefffffff1522aaafffffffffffffffffffffffffffffffffc548aaabffeffdffffff7fff1523fff5557ffc548fffd555
  | 1, 6 => 0xffffffffffffffffffffffffffffffffff7fefffbffffff1522aaafffdffbffffff7ffc548fffd555fff1523fff5557fffffffffffff
  | 1, 7 => 0xffffffffffffffffffff1522aaaffffffffffffffffd7ceffffd7dfff1523fff5557fffffffffffffffffffffffffffffffff1522aaa
  | 1, 8 => 0xfff5f397cef0f3ffcf6d3db7333fff95625580303ffc5481520000fff15205480003ffc548fffd555fff15205480003fffffffffffff
  | 1, 9 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffdbff7ff3fff9fe27f8ff03ffdfef7fbff3f
  | 1, 10 => 0xffffffffffffffffffff1522aaa
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 54 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 54 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 210 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 210 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 210 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 210 then wireAt i else 0
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
  | 4 => 16
  | 5 => 190
  | 6 => 841
  | 7 => 1068
  | 8 => 153
  | 9 => 8
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xcaaaed71627e15a84b1a22fb4990758e40c0f74a3126887d2fa06e0621798753128e9c920b9b16660b71587209341f6f05bae0660541e8b002f40bbf019480ae
  | 5, 0 => 0xfa572ba0f59db6d0f3f9cdb0f2b5cf00eabbba50ea882c60e8ec49c0e7f25a10ce919930ce391290cbf9e210c8488780c7c08ae0c18c50b0bd69ce00b35f0b40b1893450adde11d0aa1a23b0a92bcbb0a62b2660a4b63b70a42e26309bd89ab09906129099039b2097748b209500006094cec420946d18b093067ae0911706f08f6106408aa1a2a0855a78a081d5ea807c8913607824cb9077c6528065eb479063805c1060e538105fdc31005f2896805924f280520561004b994f70401c75a03c6f26303b4e1ec02f24fef0211995e0209cd1c01df7fda019c245f0167827d013dd3ea00e5e85f00deecc10090466100693ca60065fedb0020e40300015e7b
  | 5, 1 => 0x2ca6dbc22c05e5a42c05dd8b2ad2198b2976265028dafad228b869c127ded55727326b7226c5bc542678897125b5335224fc96af241608a623f49e3123d39bcc23d0cbc8234a8a2922ffe76622ca1ae621afef7c2147151b21183c7820bbb0ad2031f6511fab693f1f32b4641e91ca771ddf4a2d1cc8f9ed1ca707d81c3ecf021c27a8b71b00e10e1aee2b561a89199d1a53484319f31ca618eea8611838211e16f46c9f16df604816a5a2cd1634c3fd1518e8b614ed301614e2810714830ce41471ba4a13f5807d13bc0ff913a31a85138169f012fa564e1222530511d2d0b111945b19113e95e210d519a710be825e10b54001107ae756101cfe560fcbf77b
  | 5, 2 => 0xf6f92805c3e5ce01baa49a65b574c2ceb344649fad9e1ac1acd99b96ab56eac1aa9730b59cfceb10953ce053935b5bb8891e1227881ae44f85e1212c809c813476db15c273b23fea72d06e196f4f2a586f4882ef6bbf1fbd69904ec969825de1657182eb650679ec615c17305da1835759f16d3b58ace6e457d1c34156378c6b5181809b4f2987074e2fb3494d5c8ddc4cbafc014be7a94c495b4e7e484450d4481de6054700504146f98435453ce7034334cf89422b780041b87be74103f7c23e5abab73cf490603c9e77f53a016d36381d549c37156e1c357fbd01356c28b43366a9d533106123305e236a2fc9e08a2eda47902cf5e9df
  | 6, 0 => 0x43aa70e041c8a42040bd34c040a92de0405ce2103ac249f0389fe190389aaa7038627f2037738920354cea9034788da0346c6ec0333011b033072f6032e490f0309749d02f5fddb02f02c6902ed76e002e3e2e902ddebce02cb48ab02c4fbd302992e7502828f6e0273ccbf0260ba9d025e6bdd02428f470231820001fd262901c9de0601ad321501ab5b5901a4298801a0d8710191c45e01852882017cd96401766d81016857f2015401060135277901134a3f01018f4f00ec5a6000d2516200c78cfd00ad1dd700a26f9200a0b27c0097bdc700977aa0008e8ae4008c4ea3006f9cb6005a4a1b0058c0350054cec900383b0200242408001b1c230015d07c
  | 6, 1 => 0x93db680093bcd46092fd4c80929cc25090d988308eb0ffc08dad81f08bdeb41089d45b6083977440830c46b083062b10815ef790801883507fe3fd307c7070f07bd5be307a01eb8079a6e14078ac7350770abc1076cbfee074d1a30073ad00d0729bbb807281dab070bcdf00700e70406ea6edf06e2e06806d44b1c06b8d21f06894775067ef863067ef395067bf6a5066407a1065c86b4063180260612961b0606cbc606016ac105fcea2e05e9385f05dba0bf05d65b5d05c54fb805be3a16059da3290587e8d6057149670558f72e05539776052b8f99051f9d530505b5d90501739404fb0eb304c9b54f04b5858b04b2361a04a281d90465148b044fa90b
  | 6, 2 => 0xe6286400e2146200deb8c870dbe95af0db7aeca0db766cd0db322380d9feda80d9353370d836e5a0d7a5b4d0d1932e10ce919930ce2473b0cd9c5430ccedb160ccd516f0cc6c7770cb07e820c8db5770c70e55f0c47bbc80c32d5960c1ee07a0c1458640c11c00d0c0ce5e30c01c1ce0bfd12d20bf032db0bdf0d160bb5ba2e0b9be08e0b78f2cf0b6ed0d30b6a8c8c0b480e780b4595710afc06ef0af375fd0aee93700add279f0ac654ce0ab9118c0ab1918c0aa854bf0aa80a720a8ff0ab0a709e320a6f06c80a55d5c10a099a1e0a05c5b709fa4f0909d10c4509c9071c09b0b87809af5f4a0999debc0981130b0968ffc6094ee633094a91aa09455ef8
  | 6, 3 => 0x13810b82136cc4d01351a6ed134d17b01324036c131fd330131475b412fa564e12d1a41812ca42a312b85e6b12b6440d12af143d12977790125cd5f5125adcea12464911123c44e4122e1e59121b07a41218d9d31207319311f4e74011bd7af311b5e4571198801111945b1911910356115dffb71142806211413a2b10f98c4210dbe84e10b47c7510ae9f6f10aafb1710a692e0108b86fa10727d9f106c0b46106b3a58104f2b181046bb01104598a710416d2b1020346a101e2bbf0fe3bfab0fdfac410fd7c2bc0fbfc5910fb803f10f990ba50f7189620f528ca90f5123060f39a9d20f10d9b00f0209020ee3e42e0eba320c0eabbbcd0e6e0c2e0e6a1b3c
  | 6, 4 => 0x19dee4d419da2ec219c3b3bc19c3573319bd668d19afd64f199070ad19709f4b1954cdfe19421181192f28c3190ddbaa18bc18ae18ac6e2518a3b5a4184ef845184a336e184127161832d6a0181710c117edc59717ed92c417e0317f17c2485d17c0b7f517b5b07c17a485a0177c24c6175cdc55174e06d8173a35dc173262261726ed9e1709a0d616fda2d416f46c9f16f382b516ed244d16aa575f169417f9168328c71672abfe15dcedf915a04b37159c89ed158cf482157f2c9b153dc90f1538a3e61532605415303b88151fb03014f6245d14df51e214941428148fc0b9148333361453d515141f8fdd141d00f3141a1a4713beae5413b6a431138169f0
  | 6, 5 => 0x1ff2102c1fe9baa51fd528dc1fcdc75c1fb935101fa0a0031f359ea41f34ea441f2c92761ec5add21ebafe901e975daf1e8f96f61e860d191e8315751e468ced1e3c803d1e0961a01e08fcca1e03fd961debfb601db5992c1db1feae1d96c02e1d28a66a1d111db81cff89931ce2b01e1cdd36561cbb32bb1ca37ef51c9308ff1c70f16b1c6840821c61ee941c2e56ab1c220dbd1c1741381bfa3b3a1bf318101ba376d81b96e8611b764d6b1b38c53a1b249c4c1b1748a21b032e931ae554351acfe5b91accccec1ac1c4da1a97ec0a1a8cfbcc1a8c42f71a81704b1a6ecd711a5e9a0e1a302e541a1dc7bb1a0d81661a05157519f6a4cd19e3a6d419df4d3b
  | 6, 6 => 0x299c90d62993f944290461bc28ed17e52899d9fd2853d74d2830497d28143d1827ded5572770ae5b2740df13273fa42a26af0876269559d12635861e2625811925f9db3425f16e3d25dfff2925db05d625d1e1fb25d1da3a2596817c25775bda257200952541236a251e2eb924c4815c2451925724485baa243d0397241fd60923cdb50423bebf21238b17e02378f932230f42b722f2275b22930288228fa73b226b5baa22340de7221232f421f40ce021de63fe21c676c121c4bf3521afbbd5218dd4b42165506a215ca06d21564a742130820320ebfe8320bde07b20b3056120a5eb2820a0ad3e2051b98a20322cea2017121920087a811fff551b1ff8840e
  | 6, 7 => 0x32124cbd3204226431fd4b1a31f4048a31d7370d31b0b5513112c04d30d73d14307bae0d305f0537305bb51230531ac3303d6d512fb587ee2fa148a82f7566fb2f6094822f49e77b2f1607bd2f015cfe2ef0ffff2edf9e8c2ed7b56f2eb9b0642e8b8f9d2e8b01f82e6331e42e6082662e605cff2e4c66012e248fc42e0503242e03a5742df956b82d8aee882d68ff192d6168582d36a6d82d1c4d4b2ce0de3c2cc710002ca792d02c2525c72c0571d22bf6a1142bd3d9942bca9c222bc312f32bc0697f2bbb22202b8a122b2b82479c2b7e36a02b6b82922b2caf702b2bc2482b1ba8762ad4a1012a89ab9b2a7d8bbe2a6a162529db9b3229ca0e8b29c074c7
  | 6, 8 => 0x3f5beadc3eb6feb63e87cef53e4e90dc3e41d5433e4085f23dbba4613db352d73d99a0973d5edcee3d2be8353cd087463cc117773c5d338d3c14b5ca3be4aaeb3bcdd1793b9f76fe3b9517d93b8795793aeaaa9c3ad243f03a8b73bd3a5309ac39b8d1253998630c3991eac73962276439436aaf392f7750389c8cd037ef9ec837e355da37ae7abe37a6bf74375c328c370b42fc36c151b13698b439366e0912365833d8364f31e63640a9cc3609f05e36000d4e359d4498358c30ae3578c84e34f9221f34de448634bd92e33474962b33d88edc33c2b6c033bd163e33937fbf3366a9d533513a60333c5bee333c467d331f0a4a32c20687326ce4cb32436000
  | 6, 9 => 0x4c97476a4c84fab94be287294bcf77c24bc33bc74ba07d3a4b74bcd24ad794c24acf5bef4ac425a44a4cd7ba4a1bcbda4a00a8a749a7c8fc48f220d54874dc6648024325474a19f947299efd471886c5470496a8468e02ac463840784632ca274623eae5461eeabc4614091745c6448145b5b98145aa076a45784298453d239044ffefce44d3e3a9443a525f43f3c39143e1f57243db200343cfd02243ad9f3b42f9f34042ad9c65429786a6419bcb2c417a81cf416730ad41375169412bdbe64124155841204cd84110d8f140f1377540e1406840314782400183653fed6f703fd129ed3fcb22383fbf61b63f965cf63f92ff2f3f83ff233f7c28273f5ce785
  | 6, 10 => 0x5f8a69be5f73425e5ecb1e385e7ec7515e7afffb5da183575d94e3875d9321e35d089cd05c9dca4d5c943dab5c8c99095c51a2f65c4c5b395c4850ef5b93d2de5b3f08875b141ce05a7008ab5a6f33675a5c0a245a36711a5a0f56b15a0264f459265dfd5918aad958871ddb5853f62f57d412c65768dcaa5721ba1f5638135155ff6dee55fed6fd55ea980d559b5f0754dbc89154afa5b654ae0b3f53a7fc3453952075538da5175387857052c897d952b235145200f47051349e7b51302a375126ef2550de556e50d632f7509f8ca35010f39f4fe962014f82cac34f74e8544f4153a04f29c24c4edc70ae4ead49634e31041e4dc2128d4d3d4b724ced0872
  | 6, 11 => 0x829f1014828d60eb82844b8b824705c48204d32a8189d2bf818821b17e92a2f27e8bfb897ddb6c327d5692a57d0256087c7fc2207c687c9c7be36d2d7bd3ba4d7b2ca2a7789cc4ca7708a1a576635fee755466c474c9fe0a742b430573ce3bd173b23fea71cee00e70dec194703bd3726ee13b6a6e2580c86cd1684b6bd1c0806ba48c426b9d21576b14a9966a97e0c66a79711a6a2491db6a21027069f194fb69a77bb769904ec969830754690c93f86819743368029fc967e36ec267abbf0e67153bdb66a09d9f668fc6c6654d9ac4653d59ad652ed71464c5a10d644fe676642e8936640ba29e62bcc2ab629d31096263302261ddd20d61464e055fc9dc16
  | 6, 12 => 0xc7c9999fc6d9a3e1c63f0551c4617682c3f03268c2219632c124b8ffbc1d1430bb7a9e30bb5f66ffbb2f789bba5d0d80b9daa94fb688fad4b53f0399b4eb6374b244fabcb1f61c6ab135ea27af2c8f77af0a244eae453751ae40f7faada25ab5acd71105acced832a8061b8da75b00d7a4234630a35d3e58a1bccaf39f9971539de3facf9ab5ac9b97fc0d4197c566ed971d1ca3965f601494b1a7dc93e8d97093c92c8791aaa544915d5c10903259a48f9531948f578ee78f5272cc8ed08dfc8e185d658d24a4f78af066f98a3f286189b85242897e646888ce5a2b8888da468888c9e787fd5d5385e0d37385923a2e83a0fdb78379d2b583400b228302b3d6
  | 6, 13 => 0xf6e1da2ce859d351deeb73ebd596d1e6d35eb637d329469bd1c31977ce4f3344ca94fea2
  | 7, 0 => 0x2c57eb202966264028e484802828f6e028029060278ee5c026f38e5026a97cd0260ba9d025607ae0254a4b6025179b502481d51024531aa0244bc380235fea302298a670229321f02292a63021d8bf6020fff7e020343d901fde65c01f8d9f201f3e07301e6376e01e57d3201dfe0b301ca927b019f51af0196e9b50193adbd018890aa0177fdf4017777ea016fe473015f4010013e40d4012b1f8101271ba701189fc60107c7c900f857c500d64fc300d21c5b00c66beb00af0aed00a37c51009cec3f009978f5008576e50082f28d00786499006de43a003f0e1e00379db600351fc300255a050025265100242408001c45a1001ad75f001528ba001447f0
  | 7, 1 => 0x672c3e8065b1a680652abce062a6cd2062327d8062316f706163d0e060bf69f05e90d4b05d6612405d1e74305b329cf05b2eac505ab6a7705a247630583133205758b2f0573298d056af0ba0567fa510544cdf60527f6090524aa2c051c727f050148f804e0e91d049fe5830481caaa047e8d15047839ce0477671a0451cc9a04441f6304298fce04290a3c04264a63041ea0180414a8770402104d03f3b26a03e5727603d142b203c7801603b0a83c03afd081038cc99503713d39035dc2d9035b683203584edc0354cea90346302e033403c70331cac60327c5450315dbf0030df09a030c81b60306fda902fbbdeb02f1772d02f06da502d338cd02cf4839
  | 7, 2 => 0x970372309646595095806c90945fced0922721c091fede00918ed40090b2c30090391aa08f88e9108f8780808f0c66c08e7e79d08dcde4408d908b108d5564808c04d1d08b0b6f30895d5190883b66b087d45640875c3bc08719fb8086df8bb085ff5d1085f7476085d6ff4085340b8084dd723084aa398083591010828fed7081db4450805cd7407f0d02407e00e0a07dca06007c6446507c2197907be88db07a6bbf107a1618d079d5f9b07983db60790c065078ad7c507869901076ec3e307493bb107402e8a073325e0072330e4071274a5070d26b6070b6e270703bc2c06fdc40506f2491d06be7c2e069b54b20694c235068d4b1306858b010682030e
  | 7, 3 => 0xcdf040e0cddbc680cd85b720cd3fbe30cd29d6b0cc838990cbeacf30c99f8fc0c96af7c0c82ab2b0c76b2fc0c7515ce0c676eb60c4eb6810c400fa10c26e5a30c24f1120c23cc180c1de1fe0c16b96e0c04a5550c041eab0bd79f820bb355150bab8a350ba2b5cf0b9449150b70590e0b6ed0d30b5d6d290b39b2ba0b236e970b1c6bf00b10a95a0b0d46330aebd56b0adb42b50ad430aa0ad1fd420ababf4a0a88e2270a75aa570a5e54d50a5db90d0a4c88700a4b0a760a449ebd0a394fcf0a2d480b0a0eeb570a05c5b70a01adfb09e82ea709d10c4509d0d16d09ca1cde09c7715e09bad19109b8268309b595ea099d12b9099bfdcd0985ef7e09709016
  | 7, 4 => 0x1073d1c71073336b1072cc6410726b57105119731039159510349f511005757b0ff42b980fcf05c80fc505640fbd81990fb89c5c0fb894640faf96130fa1b6220fa110ce0f88aeee0f7d0cdf0f52f7e70f1faec60f1c517e0f1960fb0f0818e90eedf3a90ed4fd100ed133ec0ea7bb810e9f3be10e9e97020e86711a0e7b5b730e68bc0a0e61c1210e4468b30e41de8b0e3efe520e347d2b0e2eaff00e14afc00df9749a0dec2c660deb3b790dea00600de910fd0dde4b6f0dd429650db8a9780db6ae630db228940daeef0b0da91c700d9a33710d92a67e0d7414df0d6f53ff0d6550950d52fdb80d4180e80d37e10b0d2f75e70d2c2e290d1a20270d0bf729
  | 7, 5 => 0x14a53b3414861aeb145e6524145be6f114572b63144684b11441ae5b141dadd91409a6a813f695b113dbb07313c54b9e13b13c8e138bc72e136712521364db25134962ee1332ca0113285c66132143f212c75d4d12c1d0f612bb92b912b6212112aa8e291288b0461280b1f6127859a8126f593f12612c5a125d5ce812573c0512422ac7122b8da91205328f11f78a1411e2234011c9fc5911bc5b2a11aed9ae11a63a9011a48b551199c4d81194d57e117787d51167c555116093e1114234e1113fcc38113c00b61128b3f811155738110693d21100772010eed3f310e8bb3110dc987210d8287b10d730f710d401c710bfb41810bcd6ce10b47c75109959ad
  | 7, 6 => 0x1969303719570811193cf22c1929eff619265b80191c8807190d8028190801dd18f5929718ed5c0818d7eddc18ac6e251859e806184a9daa1848035418190b4417e17fa417bee38a17bd685317bc20f017aa280a17a485a017a4090a1790f650178a543217870d941783d36c177939391773db4b1769b970176707ad172fefa9170841f316c3cfc316abaeaf169092ca168684dd1682538b16785d3b1673e576165641e21655ca7b164d3a691633b1f31625c4911623d28a161b6076161ad8331610e795160f586c160f3fdc15f059271593013315911878158fc14a1571eb61156f2722153315f2152ce0e914f312d414f1d2d314d1b9a314af398f14a97cc8
  | 7, 7 => 0x1e85d81f1e6e7b011e6b70661e509d571e2dec111e1aa2331e0c97d61df400891de04d2a1dd9276e1dd645d51daa88951da91cae1d64beba1d21c4091d0839f91cd7104f1cc1bf261ca1fc5c1c92106b1c80039f1c7f660e1c6ef0421c2453b21c1695531c1160c61c0377111c02e4e51bf4b44a1bbf45891ba9074c1b9b06e31b8f4bc21b77905d1b64c5c11b13bb7c1b047b9e1b032e931af846aa1af0de741aef46af1ae8cd5a1ae1beca1adf59281adb9ef91a939d131a9023c91a812e9f1a46e7a11a39cc121a38e3ea1a28899f1a1a9d8a1a197da31a1851fd1a1323471a0cc3181a0a201f1a0397ba19e6a37b19b45c241999d774197293191969cb03
  | 7, 8 => 0x2649628c26385dd62613f6fd25fdcb1625e0085925c5372925c3b0c32572009525651281254bf6f3253f3272252ee82b25029ba324fd8cfe24d78a6824d5ba0324cb8b5524ca727024c4815c2494d98224865381244d7067244a4c22242a74e0241a19e724178ac123fa7d642371f15e2344bf4b22dafc0722b3913a22951f87225b1296223b72902239dda022340de72232186a221bd69122077c5321f0ebfc21da66e821c1edf721b91d4e21adf14b218f924b21677a51212d21b7212bd5322125b16720da045020bd10b420b14afe20b079ce20b00237208715aa207cfb7c2076b11e204cfb9c202b40b21fc1b3651fa9b9161f84e5c51f3416121ef1ff02
  | 7, 9 => 0x2f12e0272f0c8a592eed69452e5488be2e1f3b9f2e11734d2dfd8d012dca65fb2dc26c542dc1a5f82dc19aa32d91f4ea2d8754cf2d3c64902d26d4d02ceb381e2cc710002ca409f32c9aeab82c87d0ef2c60eef42c4752bb2c33b3742c1923942bfeecd02bfb4c212bd13c702bb7e6892b9b449f2b9a961c2af6c6882aedaafd2ae6ef722ae33e892a9ca7622a7fe5ba2a71ab6e2a5f79ad2a5abd462a3e98622993f944297400f82971d80f2963b7aa296140552959a0af2920d6ee28e9f8d628e1f14d28cc0ea0289b69732820b68c280d857f27fe5abe27e4956727df735527d93e002781934227715063276f2c0f2759177726c8b5c626929ca9268d68a7
  | 7, 10 => 0x375c328c371b3b97370ffab036d40a5d36d1397b365188f735db239335d0268335cceb7635a126343576e84c356eb6de354041f835094d6e3509393734e6f8c034de448634c730bd349f0686348ee9a334647388342f6268342e3a9733e5174533e47d5333822754337098c033513a60334f74da333ac8f7332c683a3300041532c20687327c9e7a32681bf43214841a320e970c320dbf0c31da1a7e31be078431a811693191955b318e383a318bced8313175c3311782d5311656bb30f9ec0330dac11430c8104430a94148308b8d4b30865f743079da87306ae5573062345c305f895a302e15b92fb84e032fa842882fa6d2ad2f7e31ac2f53e31d2f38cd65
  | 7, 11 => 0x4204329341ca1d8441b859554193eb204183d824417ae7e7415f7e2c414d56064064ccfe401ab5ae3fe59fac3f9ad3953f248a733f12e7d53ec656b03ebf5c103e70a7d23e51fe3b3e41d5433e294fff3e0c90d83dd370153dccbcab3dbd5f423db4c36c3d5edcee3d43831d3d3c97f43d3900723d31242e3d1f58a03cc117773c8484b03c83586a3c79d3023c771e663c22a8a33c05e1c63bbb8b303ba453603b901f663b7dab8e3b6d1d9a3b1437703afe9aba3aca73853a99cd023a88ac0a3a46edda3a1aa6c239dd2f12397ee837395f96ae38f9f1d038f9c945387cf532385831213830907f382614fb37f723b837e869b337e355da37b2cada377b61d7
  | 7, 12 => 0x4ee29ddf4eb287444e6585f44e5f31114e3c11704e31041e4e2ff7f04d6d7cb44d688c004d10dd8a4d0e53624cdb51174cae6cf64c7de44c4be15cf54bb8f00d4b9779ef4b74c66f4aee95694ae809a44ae0b3c94a4cd7ba4a2e23364a2918e349348d144916875749159a2f48f220d548a98b8848a30f48486b9cc547fd954c47e56217477db19f4759c5fa4751d4de473a9da346da15bd46b17d45463daf3445f0941745d7901145c5716345a855a6459a7aba44d27dc644d0c9c644d04384448e272a447218f744649fa4444412e34421a80f4412eef243ff470e43f9396a43e3a70643cfd022436b49e54318f99742fd434042ed256f429786a642977c98
  | 7, 13 => 0x605806356013f455600403e25f9df1bd5f83829a5f16df6a5ee2fc445ee0352e5e8f784f5e51b6885e471a635e35ee335deb6f4c5d9a5cf25ca052705c8c99095c8704475bf891a25b799ad45a4eb54a5a2cc3f45a168db959f16d3b5999656258ec85ee589bf43158871ddb5812724c57c41e7d575690bd571af9ba56cce91c56b80f9456ae8a1c56337c845629dfc854ae53815477e0bf542a9fec53e9ff7853a2f28c538ed0be5359b3fb5344b7e25337dfe452d9a25b52c85162525043505240bbda5221ab0e5205fd8a51cea8ce51c28f2751801bb451302a37509f8ca35098de325047ce895033b6be50286542500d7a314fce462c4fc44bd14f74e854
  | 7, 14 => 0x78fc34a3789e7b0c77836bf6769aa388764b84887480d247740919a773f742fa72df19eb72dee42172917c0a727f377571f982e87168e4f5715c578a7154491870dbcaae707653cd6efc04706ecfa5666ec5e2e46e35b9466e23adc86d977f9b6d93c5586d87aff76d27afdd6cd1684b6c96dad26b871d676b383ef56b1594e76a4898046a3a5f1d6a09b1cc69b3814569a77bb769a1629769904ec9698ce9f26979e9b468c40f0e684dd453684ad96a67e36ec266c916a366ac554466a4dd9365d993e365d15b1064b3ca606493563e6397fc726336422f62f6941b6241b5f761eea8e661ddd20d61d9161e614c4da1613185056126b1a5611f6657607ce25b
  | 7, 15 => 0xab13e342a84135a5a5ef21d7a5dd0329a590081ba4234630a3dc3944a362f85ea32c520aa304b735a2fe1800a0b4e434a04f7c219fc7ac259ea300e89c461388996dd3cc98e805b397d535199781008d94d5b2c8941f7fc4931a1542923d794b923619c0922628d291d781cd9163028991562baf8fd799028f8b65ae8f1d7bc08ee6b5b58d8425078c98a1ca8c53b6888c1397b98c03c8b18b692a5e8b32840a895ba0f1894e1718891ded1f88a3b6dc8867af228833f55188320b9e87ea643787d31c7d8738119c8687ba56859596f583a9d0ad8302b3d6824705c481384bd680446b3b803b48607f0daca37e89aff77a6dd6987a5bb7ea7976ef16790f6f3e
  | 7, 16 => 0xf698dc15f61649e1f4a1f9dcf1195156ee2eec85ece611e8ebeba476e74840b9e458c67ce40e71cee2a22ed1dfaafd01d8114742d6951e9fd1d2f5f8ce4f3344cb5da1a9c88555b5c6faa50bc6d9a3e1c647a3a0c35a0575c10dfd31bf1a8222bf19b12fbea02607bda7002fbb5f66ffb8f4d881b7a6c752b79ae05fb6776a7eb3c0ea87b35a2bf3b2061123b158ad0fb0a368cfb0778720b03b1c5faf197be6ae4eb9d4ae40f7faad9a0daaab28ba09
  | 8, 0 => 0x1dbf2e791c7f660e1b9b06e319b15e6819959b0d1983ef5b196926bf1957081118ed5c0818bc18ae18b98c2017c2485d17a485a017237154169f5cd9167ebc1d155b070714f312d4147be17a147387c81444561112a036a6126f593f11c9fc59117fcfcb116093e11106cdc710dfc44d10bcd6ce106602d20f88aeee0f1faec60f1c517e0ed133ec0eccb7400de1f81f0db6ae630cf6d6570cd4669f0cd29d6b0cc838990c041eab0bedd9ed0b8bbf6b0b15b6280a4a180909d69a7108719fb80801277907f0d02407a389060790ca2a0769545207540f0805a02dba04be9b5d0499b2c10426a54103e572760346c6ec0327c54501c0cf2f019bcd0d002f4827
  | 8, 1 => 0x6c96dad26bf88c416be3cd7869904ec9684ad96a67e36ec2613185056013f4556001d5a75fecffb25e471a63563d6c9d55fdc57d53e9ff7852b235144f85907a4f1c75a54e31041e4cae6cf64b8b4c2a4b43cfa048a30f48448b58424433319843fdcee4436b49e542a809fe424b4c7341cd32dd3fc0243e3f9ad3953f643da43eb72f933e51fe3b3e0da1cd3d41059b3c79d3023ba453603b9517d93a1aa6c2382614fb381d549c368f6cac32c96d1e30b17a1b30a941482c9d909e292e66d928a5bcb4280d857f27d93e00278193422547379b24c639ab24c4815c244d7067242a74e023d4986c22b3913a21b4474220bd10b41f505e561f28e87e1e21c84f
  | 8, 2 => 0xebeba476c6457565bc1d1430b8b93da7b0b62913b03b1c5facd99b96a5ef21d7a451de4ea4234630a304b7359e60f45a9542aab18f8b65ae8f87e3d58d8425078c53b68888a3b6dc8302b3d679fc07f676cf8eee751d0c7d73f742fa739f2b3970519bba
  | 9, 0 => 0xbc1d1430a42346308302b3d64e31041e448b5842242a74e0196926bf167ebc1d
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x511405210d4034600921405403001405210c308001485010d3040000000005106000d945081303001405210d3030011835485304000000004110746049204414040000000000002000990590d30336108255004004500921405403460c8254c44020000045085203
  | 5, 0 => 0x5010d204000d032108300000d8059083000000000041106000000000000100000000c91040000045081203000000010810000189430c830000000000000060000045041201000c8254c03010000025041202001805250c3010000000000005000000010d10400000001001080010c420c830200000000c81020018021441302000000000000100000000c110400000000c81010010c32108301000d82550430100118514813030000000000001000005110d20400000000000000000045085204001405210d3040000000108100
  | 5, 1 => 0x18135084301000003544120400181350853030000000000001000005110d2030010c420c8301000000590d2040011825441300000d825441300000005110d20300000500d020800189430c83000000000000000000c0154803000000000000000000005010d204001190588530300000000121030000000000004000004350c2040000035508200000d4400413010018943108300000000004110500185500853000000030041201000000000e103000000000000100094204413000000051480201000c8254c430100000000c9104
  | 5, 2 => 0xd94508130400000355082020000045081201001485110d3030019443485303001802144130100118058c8300000000008510500000204052000000000081105000005108120246009214054030000021085200000005108120100000450852010008510481304000005010d2040000000005106001193508130300184254c0301000000000000500000000000060000035441204000000000a10000000054842000000000005106000d9450413030000000000006000000000e1000011835441303000005050d2030000000000000
  | 5, 3 => 0x2001183548530400000250412000000000000004000990590d3040000000000005000990590d3030000000000000000d8204053010000000000007000990590d303000000010110400000000000030000000041103001884350c303000000000000200000000c81000018934108301000000000000400000450812010000000000007001802144130000000000061030000000000006001183548130300118104813030000000085103000004504120400000000c5103001445210d3030011810481303000d432449303
  | 5, 4 => 0x4001181540e303001183544130400085104813030011851481304001405210d3030011825441301000000010d1040011851481304000005010d20300000000000050000000006104000d825441300001884350c30300189430c83000018420405301000000000000100000000c51030000000000002001845250c30000118354813040000000005106000000000000300118354813030018021441301000000000a1000000000085106001405110d30300094214053010011810481303000d8255043010000000000004
  | 5, 5 => 0x118514813030008510481303000000001210300000350412000000000000004000000010d104000000000000300118514813030010c321083000014c43501303000002504120200099300803000000000000005000000000000500181510813010000000041100000000001210300118058c83000000000000006000d85148130300000000c9103000d9450813030000000000000000000010510300000250412010018943108300000d90590d30300000514802000000000000002000000010c100
  | 6, 0 => 0x15480200000000010c10100000058c1203000000000000100000250412000010c420c8300000004508120000000000000080000000000003000002504120100189430c8302000000004110100000000000080000000009107000000004110500000350412010000025041200000004508520000000000000070000000002101000000000000400000350812020000000041104000000000000700000500852000000035085201000d430441303000004500e203000004500e203000005150820100000000000070000000000005
  | 6, 1 => 0x80000035508200000005010d20300000410052020000000085103000000000e10000000300412020000000108100000003240920300118058c830100000000000020000050484201000000000000100000450412020000035441203000003504120100000000c810000000000000000000045005200000000480620300000000000020000015480200000d825441301000004500520000000450812010000000000000000004508120000000000000080000051081200000000000000100000450c92040000000000003
  | 6, 2 => 0x1813508530300000450852030000000000006000005210d20300000340c82000000000000007000000010410100000430c820100094204413000000035085201000000280620000000000c110300000000000060000000005106000000000e101000005210d203000004350c2040000005881202000000010810100000001081020011825441302000000000000000189430c8302000000000000100000000000050000045081202000000000a10000000000000000000005904200000004350c20300000000000070011820441302
  | 6, 3 => 0x5150c20000000320c4201000004500a201000004350c204000000000000000000000000040000032449204000000000000500000000811030000045041200000000004910500000000c5103000002540e2030000051481203000000000510500118024493030000000005102000004350c204000005050c201000000548420000000450052000000000000007000000010c10800000000000050000021441202000d805908301000004508520100000250412000000000000006000000000a10100000000000050000045041200
  | 6, 4 => 0x10c103000000000000600000000000000000035508200000000000000800000001081000000000005107000000000000400000000091060000000085101000004508520300000450c82000000003802200000003504120200000200812010018935041303000000010c100000000010c102000003100520100000450852010000005908202000000480220200000454c820100000454c820100000000000010000000012104000000000000500000350412000000000000008000d85148130400000000851040000000000003
  | 6, 5 => 0x51480202000000380220300000000851060000000009105000004508120000000254c42020000000108100000003550820000000000c81000018135085304000005148020000000500852010000000000006000000500a2000000000041101000000000000800000000000020000000108108000005250c2000000035041201000005050c2000000021085201000000000000800000000c8101000002504120100000000000000000035041202000000000000100000058c5204000000008110000118354853030000000000008
  | 6, 6 => 0x10c1040000045041202000000000000000000321082010000025041200000004004120000000000051050000025041201000004508520100000200812010000021085201000005050820200000000c51030000035041200000004350c20300000450812020000000085101000000000a100000005010d2040000000000006000003508120000000200812000000000041102000004350c203000000008110000000000c8101000005010d2030000005880200000000000e10000000000c110300000001081020000034108202
  | 6, 7 => 0x38022040000041084200000000010c108000005050c2010000000000006000000000000600118354413040000000000006000005250c20300000000000050000000041105000005010d203000004508120200000000000050000003806203000000590d20300000000000010000031485203000003500a20100000354852030000035485204000000010c100000004350c20300000000000050000000000006000000590c2030000050484200000004350c203000004500e20300000000c9103000000000a1000000045005202
  | 6, 8 => 0x700000254c42010000020081202000000004110500000000c0100000000000610000000000000050000034108200000000000000100000000000080000000000005000004508520100000000c8102000d4304813030000000000000000000380a2030000045081201000000588120100000000000000000000000008000005010d203001893410830000000000c1103000000000000300000450c52030000030481204000000004110000000000000050000000000000000000000000800000454c82000000000000005
  | 6, 9 => 0x4000004340a20300000000000050000043406204000005048420100000450c120300000514c82020000035081200000000000000500000054842020000042100200000000000000100000350852000000035485203000000590d20300000450c42010000000080102000000000000500000000000010000021085201000003210820000000204052020000051081200000003544120300000000121020000000000003000000480a2020011851481303000000000000800000000000070000000002100
  | 6, 10 => 0x411070009421405302000000000000500000000000060000000000006000003500a20200000200812000000035041200000000000e103000005250c2000000000000001000004504120100000350852010000000000001000004108420100000038062000000000000002000004350c20300000000000000000001802201000000000000100000430c8201000000000a104000003048120400000354122030000000000000000d032108300000004500e20300000000c8101000004504120100000510812020001935085304
  | 6, 11 => 0x18022040000000006104000000480a2000000000000005000000000a102000004350c203000003544120300000000d01080000035441203000003504120300000000851030000051508200000005050c20200000000000080018135085303000000004110200000000411050000000009106000004310820000000454c820000000420c8201000005010d204000004500a2020000030100200000005050420100189430c830200000214412000011835481303000000010c102000004344120400000351082020000000108101
  | 6, 12 => 0x10d104000000590820000118058c8300000004500e20300000504842010000000000000000d82544130100000000000050000000000002000003500a20200000350812020000000806200001805250c300000004500e20300000430c82020000000085103000000000000400000351082010000000000001000492044130400000058c920300000450812030000000000008000000000a1010000020081200000004500e203000000000000400000000000000000000000007000000010d10300000000c410000000450c8201
  | 6, 13 => 0xe1040000000000003000000008510200000450c5204000000000a100000005250c200000005048420200000000000030000000000000000005050c203000005148120400000214412000000021085201000000000000800000000811030000000000000000003504120100000059052030000045085204000000008510500000354852030000000000004000004508520200000000000080000000000001000000010510300000250412010000000000004000000590c203000001048120400000450812000000020441200
  | 6, 14 => 0xa1020000000005105000851048130300000254c020000000454c1203000000010d103000004508520000000000000010000050508200000004350c204000000000000100000000811020000000041104000000010d10300000058852040000035412203000000008110600000000d0108000003500a201000d432449303000000000e10300000454c820200000000000000000000041100000005148020000000000000060000045041203000005210c2000009421405302000000000000600000350412000000000000000
  | 6, 15 => 0x4806203000000480e203000000590c2030000000000005000003504120200000000000000000035412203000000010c1030000005908200000005050d2040000000006103000000540a20100000434c52030000051480200000005050d203000000010110300000000000070011835441303000000480e203000000008410000000000811000000015412203000000010c10400000450c520300000000000010000000002100000000000000700000210852000000000000005000004500e203000004500e204000d805908300
  | 6, 16 => 0x450c8201000005150c20400000450c820100000000c8100001893410830200000454c8200000003504120100000000000080000035085200000002504120100000450412030000005881204000000000000500000450412030000025041202000003504120000000000851000000020441200000000480e2000000035085201000000180220100000000000050000000000004000004350c2030000000000008000000000000300000514812040000000000004000000000000200000058c120300000014852040000000000004
  | 6, 17 => 0x30000043485203000005150c203000000000000200000350412040000045041203000003504120000000000811050000000000002000002504120100189430c8302000004500a200000000380a200000000000e1040000035508202000000008510700000000d0108000004340e20300000450c42000000034108202000005150c20400000355082000000000000001000000000a100000000000000400000434c92040000045041200000004508520000118514813030000000009105000005148020000000320c4201
  | 6, 18 => 0x1183544130400000000000050000035085201000000010c101000004504120000000000c110400000028022000000000000005000000010c10200000038022000000000000008000000010d103000000480e2000000035041201000000590c2020000025041201000000010d1030000002802201000000280620400000000851050000000049106000000000000600189341083000000045041202000005108120000000000000060000045485203000000000000500000450c1204000000000510700000000000060000000009105
  | 6, 19 => 0xd43140530300000000051060000000000006000000000e1000000000000006000000000a10100000000000080000000000003000000000e103000000540e20300000000000010000005484200000005250c20000000000000040000000000006000001048120300000028062010000035508200000000000a10200000450852040000000000007000000000000600000000000080000025041201000d4324093030000000000007000000000000100000000000080000000085103000004540e20300000250412000000043505203
  | 6, 20 => 0x53101203000000000a100000000590c2020000035108201000004350c203000000010d103000004004120100000354852030000000000000000000000000500000000000040000000000006000000000000300000250052000000005904200000000548420100000500852000000000081104000000590c200000000008110000000250412020000000000005000000000000800000400c0200000005210d2030000000000002000002540220000118058c8300000000000000000000000000060000035481204000000000a100
  | 6, 21 => 0x4350c2030000000000005000004500e2030000000005100000003500a2000000000000007000000010c103000000590c2000000000000002000000010c1080000045041203000005250c2010000051081200000004508520400000250412000000000081106000d825441301000000010d1040010c420c830000000450c8202000000380a202000000588120300000058852000000000041102000004500e2030000000000000000003500a20000000058c520300000000000040000051481203000000010c1040000000000003
  | 6, 22 => 0xd85148130300000450c92030000000000001000003541220300000434c5203000004500e2030000000000001000000010c104000000000000800000000000000000025041200001182544130100000000d010800000000000010000000000000000000004110500000000000040000000000004000000010d10400000350412000000002806203000003410820200000000d01080000000000004000000010d1040009905841300000005250c20200000001081000000051481203000000010d103000000000000400000450c8202
  | 6, 23 => 0x3500a20200000000d0108000000010d1030000000000001000000000000500000450412030000000000006000d85148130300000000c9103000004500e2030000000041102000000010c1010000000000002000000000e103000000480e2020000035412204000005150c2030000000006104000000010d1030000000012103000003508420000000154802000000035104200000000000000800000000000080000000081103000000480e203000000000e103000000010c10100000000000070000005841203000000000e103
  | 6, 24 => 0x4500e2030000000000000000000590c20200000254412020000000012104000000490d203000004508520100000354412030000000000001000000000a100000000010d10300000000000080000000000003000000590820200000000851060000000000005000004500e20300118058c83000000025041201000000000000800118514813030000000000008000942140530000000058412010000002802200000004500e20300000350122030010c420c830000000450052010000051081200000005210c2020000000000000
  | 6, 25 => 0x80000025441202000004500e203000000590d2030000000000008000000590d203000004500e2030000000000003000004500e203000000540a2000008510481303000004500e203000003210820000000000000050000000000005000000010c1000000000000003000000590c203000000000000200000000000010000000084100000004500e203000005050c200000004350c20300000000d010800000000d01080000051481204000000010c10400000000000030000000000005000004500e203000004350c203
  | 6, 26 => 0x4340e2030000000000008000000010c103000005210c20200000000000030008510481303000004504120300000000000080000035108200
  | 7, 0 => 0x10810000000450852040000000080100000000000000500000048022040000000080102000000010c10000000000411010000000006101000000000e1040000000085100000000000e10000000024492040000000000003000000590c200000000010410000000000121030000000000005000000010c1030000000041103000000008110000000000c1103000005150820200000524d020000000000000070000000108102000000380a2010000000000006000000000e103000000000000800000018022010000050508200
  | 7, 1 => 0xc110300000000000060000000006101000000000000000000000000020000000000003000000000e10200000450812040000000000008000005150c2010000000000001000004508120100000001081000000000085102000000000a10100000000c11040000000108101000000280220100000000021000000000000006000000000a100000000008010200000000851030000000000006000000000a10000000351082010000025041202000000000e1010000021405201000000000a103000003508120300000000c8100
  | 7, 2 => 0x12409204000000000a100000000000000500000450412020000035081200000000000510100000000c81020000000085100000000000e1030000030441203000005150c20200000000851030000000012100000000000a1020000000108101000000010c10400000000c810000000000c8100000000000000200000000c110300000254412000000002802200000000000a10100000514c82000000045081201000000010810200000000000030000000084100000000000000000000450c5203000000000a10000000000c8102
  | 7, 3 => 0x610400000000841020000005881200000000000a10000000000801000000025041201000000000000500000000811030000000108102000001540e204000000000000600000000121010000000006103000000480a20300000000801020000000085102000000000e10300000000021030000003802203000000000e1000000000000000000000010c10300000000000000000035508200000003244920300000450c82020000000000000000000010c102000000000610000000058412020000000000002000000000a102
  | 7, 4 => 0xe1040000035481203000000000a102000000010d103000003044120300000038062000000050508200000000010c10400000000c810100000000061000000000108100000000000a1040000000041101000000010c10000000000000080000000081104000000000000500000000c4100000000001210400000000c510300000000051000000000085100000000000e101000004508120000000058c920300000000411050000000000004000000000e10300000018022000000000108101000000000a100000000000e103
  | 7, 5 => 0xc8100000000000000100000000061010000000000005000000010c1020000051508201000000000a101000000000a10300000001041010000000041101000000010810200000000c4102000000244920300000000c810100000058c12040000000000008000000480e20400000000411030000004806200000000000a10400000000c11040000000081101000000000a1010000001802204000003500a20000000059082000000000081101000000000a100000000000e103000000000e104000000480e202000000000a101
  | 7, 6 => 0x5000000010d1030000000012101000005050c20300000000c4101000003508120200000000411030000000000005000004500a20200000000061010000005881204000000480a20100000000000050000000108100000000008510500000454c82020000000041103000000000610100000000000070000000012100000000588520000000000c51040000000108101000000010010100000058852030000000085100000000010c1020000000084100000000004110000000000c810100000314852030000000041104
  | 7, 7 => 0x210300000000c5103000000008110100000000c8100000000000000200000000d010100000000c1103000000000000700000504c820000000000000080000000002100000000000e102000000010c1030000000000004000000000000500000000000010000000000007000000010d10300000000c8100000000000a1010000000084100000000000a1000000000000004000000000a10000000000c11030000000000000000000000000300000000121030000000000000000000010410000000000811000000000002101
  | 7, 8 => 0x10d1030000000108102000000000210000000000061040000020441202000000000e1030000000108102000004500e2030000045041204000001540e20300000000851020000000000005000000590c204000000010c103000000010d1030000000000000000000000a101000000010c104000000380a20300000000811020000000100102000000000a102000000000510100000000851010000025041201000000004110400000000c910400000000411010000000002101000000010410000000000000030000000085101
  | 7, 9 => 0x350412000000000000007000000010c10300000000000060000000000004000000380a20200000000c11040000005841201000000008510000000038062040000000081103000000010c103000000480e20000000000c010000000000d010000000000000040000000081100000000000a1000000000000008000000000000300000000000000000000006100000000000a100000000010d104000000000a1020000001802200000000000e104000000010c1030000000081103000000010c10400000000061000000000000000
  | 7, 10 => 0x32409204000000010c102000000000a100000001540e203000000010c100000000000610000000454c82000000000108102000000000a101000000010d1040000000000008000000000a1030000000081103000005050820000000000801000000000000000000000010c10300000000c010100000000000060000035085202000000000510000000430c820000000058c12030000050508201000003504120100000000c4101000000000e103000000540a201000000000000500000000c810100000000000070000002806200
  | 7, 11 => 0x450c120400000420c820000000000c8100000000010010000000000851020000000006102000000010810200000000c0100000000000a102000000010810200000000c9103000000000e103000000000a102000000001210000000000411020000034108202000000588520200000000851020000000000008000000000e1030000031405203000004508520400000350812010000000000008000000000000800000000061010000000000000000000000a101000000010c1010000000101104000000000000800000000c8100
  | 7, 12 => 0xc91030000000108102000000000000800000000000080000000000005000000001210300000000c51040000000000007000000010c1030000000108102000002044120100000000c1104000000008110200000001041010000000006101000000010d103000000010c100000003504120300000000411030000000000005000000010c100000000000e10300000000c5104000000010c103000000000e104000000000e1040000000081103000000000000000000000000040000000085101000005250c20100000058c9203
  | 7, 13 => 0x1000000010c10000000001081020000000000005000005050c2000000000012104000000000a100000000000610100000000c5103000000001210000000000000080000000000005000001540a2020000000085104000000000000800000000c510300000000000040000000000003000000000a101000000380a200000000010c10000000000c81000000000108100000000000000500000000c81010000005881200000000000a103000000010c10200000000c510300000000021020000003802200000000000e104
  | 7, 14 => 0xa1000000000012103000000000a10200000000000050000021405200000000008410200000000811000000000012101000000004110000000000051020000035085202000000010c103000000000a1030000000002102000000000e1040000000101104000004504120100000000000080000000081100000000000610000000000411030000035041200000000010d104000000000000800000000c8102000000480e204000000380220200000000841010000000080102000000008510000000000121040000000000005
  | 7, 15 => 0xe1030000000108100000000000000500000454c820100000000c01000000000041100000000000e1030000000108101000004500e20300000001081010000000000003000000000000800000000411000000003802203000000010c10300000000851000000005908201000005150c2040000000000003000000000a1000000000041103000000000a10200000000000040000000000006000000000e104000000000a1000000000012103000000000a102000000380a204000000010c10200000000021010000000012100
  | 7, 16 => 0x41102000000010c102000001540a20200000000000070000000108102000000000000800000000000080000002802201000000000e1040000000085103000004500e20300000450c8201000005210c200000000480e201000000010c103000000000000100000000000010000045041200000000000a100000000000e1000000000000008000000000a10000000000000030000035041202000000000610000000000021040000000006104000000000e100000000000a10000000000c51030000025441200000000010c104
  | 7, 17 => 0x5250c203000000000a102000000010c100000000000000200000000c8102000000000a101000005050c20100000000000010000000000005000000000a10000000000c5103000000004110100000000d0102000000000000600000000c510300000000061000000000005101000000010d10400000000000040000000084100000004500e204000000000a10200000000000010000000000000000000000e1040000025441202000000008110100000000811040000000000008000000590c20200000000811000000000000008
  | 7, 18 => 0xe103000000000000400000355082020000000000005000000000e104000000000e104000005050c20000000000061020000000000003000000000e104000000004110000000000c810100000321082000000000000004000000000e10200000000c410100000000c1103000000000000800000038022000000000006100000000010c103000000008010200000000000020000000000007000000000e103000000000610100000001081000000000000008000004500a201000000000e104000000008510300000058c8202
  | 7, 19 => 0x450c5203000000010c1030000000080100000000000a1000000000012103000002140520100000000c5103000000000610300000000000060000045081204000000000a1000000000041100000000000a1020000000041102000000010c10400000000000000000000108101000000000e100000004500a202000000000000100000000121010000000000008000000008010000000000c810100000000811010000000041101000000590c200000000000e10300000000811030000000081100000000000000400000450c9203
  | 7, 20 => 0x5000000000a101000000004110100000350412030000000101103000000010c1010000000085102000000010c104000000008110400000000000080000000000003000005150c20300000354812040000000000005000000000a103000004508120100000000c51040000000100102000000000e1030000000000000000004500a20000000354812030000005881200000000000a1000000000006100000000000000800000000c11040000000000006000000010c10200000000000020000000000008000000010c102
  | 7, 21 => 0xc81000000000002101000000010810000000000000000000000000002000000010c101000000000e104000004500e2040000000041101000000000000400000058d020000000058852010000000081100000005250c200000000008510400000000d01010000000000006000000000e10400000000c81010000000012100000000000a1010000000000006000000000a1000000000000005000005150c200000003500a200000000000e10300000000000030000000000008000001540e20400000430c820200000000c9104
  | 7, 22 => 0x5841202000000000a101000000000e100000000008510300000430c82000000000000004000000280620000000000000000000000000008000000000e10300000000d0101000000380a2000000000000008000000000a100000000000a10100000000411020000000105103000000000510000000000c51040000000108101000000000e103000000180220300000000000020000004806202000003504120300000450c52040000000085101000000000a10100000001041000000000000006000000000a1000000034108200
  | 7, 23 => 0x10c101000000000e10400000000000010000000006100000000000a101000000000a10000000058c8201000000000e1030000000000006000000010c1030000000081100000000000e103000000000000500000001081000000000005100000000000e104000000010c10400000000000000000000000008000000010c102000000008110200000000811010000002802202000000000000200000350412030000000000006000000000a100000000000000600000000c510300000059082000000000012103000000000e103
  | 7, 24 => 0xa10100000000000060000000041100000000000a101000000010c104000000000e101000000000a100000005250c2000000000000008000000010c100000000010c1000000000000008000000008410100000058852030000000000005000000000e103000000010c10300000341082020000000000006000005250c20100000000121040000000101103000000000e104000000000a1010000000000000000000000a101000000010810200000000000050000000105103000000010110300000000000080000045041202
  | 7, 25 => 0x6101000005148120300000059082000000000041100000000000a1020000000000000000000480e200000000010c101000000000e103000000000a100000000000e104000000000e104000000000a102000000000000700000000000060000000000008000000000000100000014852030000000012103000000000a10000000250412010000000000001000005150c204000000000000800000000121040000000000000000000004110000000000000060000000000000000000000e10300000048062040000000000006
  | 7, 26 => 0x10c101000005050c200000000380a200000000010d10300000000c5103000000000000800000000000030000000000003000000010c102000000000e104000000000610300000000811010000000000005000000010c103000000000e104000000000a102000000010510300000058c520400000000000050000000000005000000000e104000000588120300000000000080000000081100000000010c100000000000610100000454c820000000000411000000000000000000000010d103000000000000800000000c0101
  | 7, 27 => 0x454c8200000000000e10000000000000050000000000004000000180220200000000061010000000084100000000010d10300000000c8102000000590c203000000000e1030000025041201000000010c10400000000000070000000080101000000000000600000028062030000035081203000000000a102000000000e103000000000e104000000000a100000000000000200000000000050000000000005000000010c103000000000e1030000000108101000000000000000000000021000000000000008000000010c101
  | 7, 28 => 0x590c2000000000000007000000000e10400000420c82000000000000008000000010c1030000000000000000000590c2010000005881203000000000e103000001540e203000000000a1020000000000000000000010c1030000051481203000000010c10300000000d010800000000d0108000000010c1030000000012103000000000000100000000000000000000000002000000010d1030000000000004000000010d1040000000041101000000000a102000000000a1000000000081101000000000e103000000010c102
  | 7, 29 => 0xa1000000000012103000000010c1030000000081100000000590c20300000028062030000000000008000000010c1030000005841200000000010d104000005250c200000000000a100000003500a2000000000000005000000000e103000000010d10300000250412010000000012103000000000a102000000590c20400000000c9104000000000e104000000010d1030000000000005000000010d104000000010810200000000000020000000000005000000000e103000000000e104000000540a200000000010d103
  | 7, 30 => 0x80000000012103000000000e103000000000a1000000000000006000000001210300000000121030000035441203000000000a100000000010d103000000010c1080000000002100000000010c103000000000a10100000000000070000000000006000000010c103000000480e204000000000e1040000000041105000000000000400000000000000000000000001000000010d103000000010c104000000000e103000000010c103000000000000800000450c8200000000010c1030000000006100000000010d104
  | 7, 31 => 0xe103000000000e104000000000a100000000000e10300000450c82000000000000003000000000000200000000121030000035441203000000000e103000004500e2040000000000008000000000e103000001540a20000000250412000000000000008000000001210400000000000080000000000008000000001210300000420c82000000000012103000000000e10300000000000010000000012104000000000e103000000000000500000514812040000000005100000000000000300000000000000000000000003
  | 7, 32 => 0xe104000000000000500000000000080000000000008000000010d103000000010d103000000000000400000000000050000000000005000000000a100000005148120300000000000010000000000003000000010c1040000005841200000000000a1010000000000007000000010d10300000000000020000000080100000000000a102000000010c104000000590c204000000000a10000000000000080000045041200000000000e100000000010d1030000000012104000000000000500000254412020000000000005
  | 7, 33 => 0x12103000000000a100000000000e103000000480e203000000010c1030000000012103000000000e10300000000000080000000012103000000000000800000000000030000000041100
  | 8, 0 => 0x81102000000000000800000000000000000000006103000000000a1010000000085100000000004110300000000000020000000000004000000000a10000000000000020000000006101000000010c10400000000000040000000006103000000000a1010000000000001000000000e103000000000000000000000851010000000000002000000000e1010000000000003000000004110400000000000010000000081100000000000e103000000000000100000000000080000000006104000000010c1030000000000001
  | 8, 1 => 0x3000000000a10200000000021040000000002101000000010c10300000000000020000000000000000000000000300000000c11040000000000001000000001210000000000000020000000000003000000004110300000000000000000000000003000000008110000000000000000000000012102000000000000300000000061020000000041100000000010c10100000000021020000000000004000000000000100000000c1103000000004110300000000c81010000000000000000000000a1000000000000000
  | 8, 2 => 0x41101000000000000000000000c810200000000c51030000000081103000000000000000000000000020000000000005000000000000600000000000030000000108100000000010c1000000000000003000000000e1030000000012104000000000000100000000121030000000000008000000000e103000000000000600000000c510300000000c11030000000000004000000000a1020000000000000000000000510000000000000050000000108100000000000a100000000004110100000000000020000000108101
  | 8, 3 => 0xe10300000000000020000000000003000000000000000000000000070000000000000000000000a100000000000e10000000000000030000000000002000000000e1030000000000004000000000000300000000000030000000000003000000000000000000000000000000000000000000000000e10300000000000040000000000002000000000e10300000000000000000000012103000000010c1000000000000004000000000000200000000c81000000000000001000000010c10200000000000080000000000000
  | 8, 4 => 0xe103000000000000300000000000030000000000004000000000000200000000000030000000000003000000000a10000000000000040000000000003000000000e103000000000000300000000000000000000000000000000010c1040000000012104000000000a10000000000411010000000000000000000000000300000000000040000000000008000000010c103000000000e101000000010c100
  | 9, 0 => 0x30000000000003000000000000000000000000000000000000000000000000000300000000000000000000000003
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_5 roots_5 8 s ws hint
  | 1 => checkCutEntry dom_6 roots_6 8 s ws hint
  | 2 => checkCutEntry dom_7 roots_7 8 s ws hint
  | 3 => checkCutEntry dom_12 roots_12 8 s ws hint
  | 4 => checkCutEntry dom_13 roots_13 8 s ws hint
  | 5 => checkCutEntry dom_15 roots_15 6 s ws hint
  | 6 => checkCutEntry dom_16 roots_16 6 s ws hint
  | 7 => checkCutEntry dom_17 roots_17 6 s ws hint
  | 8 => checkCutEntry dom_20 roots_20 6 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_21 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_21 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_21 == dom_21) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_21 goalM u ys) : RunD dom_21 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_21 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
theorem z5_40 : ∀ i, 40 ≤ i → i < 42 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 40 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 42 → Z 5 i = true := range_split z5_0 (range_split z5_8 (range_split z5_16 (range_split z5_24 (range_split z5_32 (z5_40)))))
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
theorem z6_160 : ∀ i, 160 ≤ i → i < 162 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 160 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 162 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (range_split z6_64 (range_split z6_72 (range_split z6_80 (range_split z6_88 (range_split z6_96 (range_split z6_104 (range_split z6_112 (range_split z6_120 (range_split z6_128 (range_split z6_136 (range_split z6_144 (range_split z6_152 (z6_160))))))))))))))))))))
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
theorem z7_232 : ∀ i, 232 ≤ i → i < 239 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 232 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 239 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (range_split z7_136 (range_split z7_144 (range_split z7_152 (range_split z7_160 (range_split z7_168 (range_split z7_176 (range_split z7_184 (range_split z7_192 (range_split z7_200 (range_split z7_208 (range_split z7_216 (range_split z7_224 (z7_232)))))))))))))))))))))))))))))
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_32 : ∀ i, 32 ≤ i → i < 40 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_40 : ∀ i, 40 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_48 : ∀ i, 48 ≤ i → i < 56 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_56 : ∀ i, 56 ≤ i → i < 60 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 56 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 60 → Z 8 i = true := range_split z8_0 (range_split z8_8 (range_split z8_16 (range_split z8_24 (range_split z8_32 (range_split z8_40 (range_split z8_48 (z8_56)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_0 : ∀ i, 0 ≤ i → i < 8 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_8 : ∀ i, 8 ≤ i → i < 9 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 8 = true)
theorem z9 : ∀ i, 0 ≤ i → i < 9 → Z 9 i = true := range_split z9_0 (z9_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z10_0 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := z10_0
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, Z s i = true := by
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
  · exact fun i hi => z10 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_21 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD dom_21 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_21 roots_21 goal_21 11 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_21 goal_21 := by
    have h0 : isConstB dom_21 goal_21 = false := by decide +kernel
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

end S_21

theorem low_21 : Lower dom_21 roots_21 goal_21 11 := S_21.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_21_bits : ∀ r : Fin 64, roots_21.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_21_lt : ∀ r : Fin 64, dom_21.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_21 T)
    (hlow : Lower dom_21 roots_21 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_21, Avail mask256 roots_21 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_21 hfan 0 roots_21 roots_21 rfl hsup0
  set out := (execN C.gates roots_21).getD C.output 0
  have hout : out &&& dom_21 = T &&& dom_21 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_21_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_21 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_21_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_21).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_21)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_21.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_21 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_21).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_21 &&& mask256 = dom_21 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_21 = T &&& dom_21 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_21, hd63, hout]
  have hnc_m : ¬ IsConst dom_21 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_21 roots_21 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_21, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_21 roots_21 0 roots_21 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4276682240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_21.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 11 ≤ t :=
  lower_to_circuit6 fG goal_21 11 hT6 (by unfold IsConst; decide) low_21

def wit : Circuit := ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.and, [9, 5]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [12, 11]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [14, 4]⟩, ⟨GateOp.and, [13, 15]⟩], 16⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 11 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_12316_aux

theorem PEqualNP.Outside.L_meta_12316 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_12316_aux.wit, PEqualNP.Outside.L_meta_12316_aux.wmono, le_trans PEqualNP.Outside.L_meta_12316_aux.wsize (PEqualNP.Outside.L_meta_12316_aux.lower s hs), PEqualNP.Outside.L_meta_12316_aux.weval⟩
