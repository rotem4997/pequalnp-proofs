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

namespace PEqualNP.Outside.L_meta_12112_aux

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

def dom_0 : Nat := 0x4444444400000000
def goal_0 : Nat := 0x4440400000000000
def roots_0 : List Nat := [0x4040404000000000, 0x4400440000000000, 0x4444000000000000]

namespace S_0
def pairsG : List (Nat × Nat) := [(38, 46), (38, 54), (42, 46), (42, 58), (50, 54), (50, 58)]
def r1sG : List Nat := [38, 38, 42, 42, 50, 50]
def r2sG : List Nat := [46, 54, 46, 58, 54, 58]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xd585f17f
  | 3, 0 => 0xd585f17f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x444400000000000044004400000000004040404000000000
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
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

def dom_1 : Nat := 0x5050505000000000
def goal_1 : Nat := 0x5040400000000000
def roots_1 : List Nat := [0x4040404000000000, 0x5000500000000000, 0x5050000000000000]

theorem low_1 : Lower dom_1 roots_1 goal_1 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_2 : Nat := 0x5555000000000000
def goal_2 : Nat := 0x5440000000000000
def roots_2 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]

theorem low_2 : Lower dom_2 roots_2 goal_2 4 :=
  lower_iso [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1

def dom_3 : Nat := 0x5555555500000000
def goal_3 : Nat := 0x5440400000000000
def roots_3 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]

namespace S_3
def pairsG : List (Nat × Nat) := [(38, 46), (38, 54), (42, 46), (42, 58), (44, 46), (44, 60), (50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [38, 38, 42, 42, 44, 44, 50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [46, 54, 46, 58, 46, 60, 54, 58, 54, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_3.map (· &&& dom_3)
def goalM : Nat := goal_3 &&& dom_3
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x37d88c65
  | 4, 0 => 0x27d1549508d5bfca0684d88004965e93
  | 5, 0 => 0x5568db7e3ef7d626217f3ab8
  | 6, 0 => 0x217f3ab8
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x50500000000000005000500000000000444444440000000040400000000000001515151500000000111111110000000005050505000000000000555500000000
  | 0, 1 => 0x5555000000000000550055000000000055000000000000005050505000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x97654
  | 4, 0, 0 => 0xba214ba8535ba8545a98755
  | 5, 0, 0 => 0xba86550a85040ba854
  | 6, 0, 0 => 0xba854
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3000300cf000ffcf30ccc03f
  | 0, 1 => 0xfc0c3cc00333
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xb62a355df142ea8a20488015
  | 0, 1 => 0xfeaebdea8b77
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 12 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
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
  | 2, 0 => 0x6091bba
  | 3, 0 => 0x8df69e96217f3ab80abb01d7007a81f4
  | 4, 0 => 0x72f55c1f5568db7e4fabacef487848c33ef7d6263c3431b2217f3ab806cb9bc3
  | 5, 0 => 0x72f55c1f487848c3
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x0
  | 3, 0 => 0x40000000000000001
  | 4, 0 => 0x1000004000000000080000100000000000
  | 5, 0 => 0x0
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 4 s ws hint
  | 1 => checkCutEntry dom_1 roots_1 4 s ws hint
  | 2 => checkCutEntry dom_2 roots_2 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_3 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_3 == dom_3) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_3 goalM u ys) : RunD dom_3 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_3 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_3 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_3 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_3 roots_3 goal_3 7 := by
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

theorem low_3 : Lower dom_3 roots_3 goal_3 7 := S_3.noCircuit

def dom_4 : Nat := 0x3333333300000000
def goal_4 : Nat := 0x3220200000000000
def roots_4 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]

theorem low_4 : Lower dom_4 roots_4 goal_4 7 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3

def dom_5 : Nat := 0xf0f0f0f00000000
def goal_5 : Nat := 0xe08080000000000
def roots_5 : List Nat := [0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000]

theorem low_5 : Lower dom_5 roots_5 goal_5 7 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4

def dom_6 : Nat := 0x5500550000000000
def goal_6 : Nat := 0x5400400000000000
def roots_6 : List Nat := [0x4400440000000000, 0x5000500000000000, 0x5500000000000000]

theorem low_6 : Lower dom_6 roots_6 goal_6 4 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2

def dom_7 : Nat := 0x3300330000000000
def goal_7 : Nat := 0x3200200000000000
def roots_7 : List Nat := [0x2200220000000000, 0x3000300000000000, 0x3300000000000000]

theorem low_7 : Lower dom_7 roots_7 goal_7 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6

def dom_8 : Nat := 0xff0000000000
def goal_8 : Nat := 0xe80000000000
def roots_8 : List Nat := [0xaa0000000000, 0xcc0000000000, 0xf00000000000]

theorem low_8 : Lower dom_8 roots_8 goal_8 4 :=
  lower_iso [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7

def dom_9 : Nat := 0xff00ff0000000000
def goal_9 : Nat := 0xfe00e80000000000
def roots_9 : List Nat := [0xaa00aa0000000000, 0xcc00cc0000000000, 0xf000f00000000000, 0xff00000000000000]

namespace S_9
def pairsG : List (Nat × Nat) := [(41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [41, 41, 41, 42, 42, 42, 44, 44, 44, 56, 56, 56]
def r2sG : List Nat := [43, 45, 57, 43, 46, 58, 45, 46, 60, 57, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_9.map (· &&& dom_9)
def goalM : Nat := goal_9 &&& dom_9
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x8de3595f
  | 4, 0 => 0x306029ce2a8775cb0ab50bda0637b8c8
  | 5, 0 => 0x5f9d9d5d1605d2a20435f488
  | 6, 0 => 0x5f9d9d5d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfc00fc0000000000f000f00000000000ee00ee0000000000cc00cc0000000000aa00aa000000000055005500000000000000ff00000000000000330000000000
  | 0, 1 => 0xff00fa0000000000ff00f00000000000ff00cc0000000000ff00aa0000000000ff00000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa9654
  | 4, 0, 0 => 0xc86435b87435064214864305
  | 5, 0, 0 => 0x86434a86435086424
  | 6, 0, 0 => 0x86434
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1f81c003f038007ff81ff1c7
  | 0, 1 => 0xfc7fc0e38e07e00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xdfb9d26ff4b924fdb00db042
  | 0, 1 => 0xfffff6fbdf6ff24
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 13 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 13 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 13 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 13 then wireAt i else 0
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
  | 2, 0 => 0x6ff599b
  | 3, 0 => 0x5f9d9d5d1445e4d80e01a05007662f1c
  | 4, 0 => 0x73bc8b8e5f9d9d5d410e677532f384d11f0c9e891ca2a8651605d2a20435f488
  | 5, 0 => 0x73bc8b8e32f384d1
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x1
  | 3, 0 => 0x400001
  | 4, 0 => 0x200000400000
  | 5, 0 => 0x0
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_6 roots_6 4 s ws hint
  | 1 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 2 => checkCutEntry dom_8 roots_8 4 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_9 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
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
  scr dom_9 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_9 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_9 roots_9 goal_9 7 := by
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

theorem low_9 : Lower dom_9 roots_9 goal_9 7 := S_9.noCircuit

def dom_10 : Nat := 0xffff000000000000
def goal_10 : Nat := 0xfee8000000000000
def roots_10 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]

theorem low_10 : Lower dom_10 roots_10 goal_10 7 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9

def dom_11 : Nat := 0x2222222200000000
def goal_11 : Nat := 0x2220200000000000
def roots_11 : List Nat := [0x2020202000000000, 0x2200220000000000, 0x2222000000000000]

theorem low_11 : Lower dom_11 roots_11 goal_11 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0

def dom_12 : Nat := 0xaaaaaaaa00000000
def goal_12 : Nat := 0xaaa8a80000000000
def roots_12 : List Nat := [0x8888888800000000, 0xa0a0a0a000000000, 0xaa00aa0000000000, 0xaaaa000000000000]

theorem low_12 : Lower dom_12 roots_12 goal_12 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x8888888800000000, 41, 43)] (by decide +kernel) (by decide +kernel) low_11

def dom_13 : Nat := 0xcccccccc00000000
def goal_13 : Nat := 0xccc8c80000000000
def roots_13 : List Nat := [0x8888888800000000, 0xc0c0c0c000000000, 0xcc00cc0000000000, 0xcccc000000000000]

theorem low_13 : Lower dom_13 roots_13 goal_13 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12

def dom_14 : Nat := 0xf0f0f0f000000000
def goal_14 : Nat := 0xf0e0e00000000000
def roots_14 : List Nat := [0xa0a0a0a000000000, 0xc0c0c0c000000000, 0xf000f00000000000, 0xf0f0000000000000]

theorem low_14 : Lower dom_14 roots_14 goal_14 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13

def dom_15 : Nat := 0xff000000000000
def goal_15 : Nat := 0xe8000000000000
def roots_15 : List Nat := [0xaa000000000000, 0xcc000000000000, 0xf0000000000000]

theorem low_15 : Lower dom_15 roots_15 goal_15 4 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8

def dom_16 : Nat := 0xff00ff00000000
def goal_16 : Nat := 0xe8000000000000
def roots_16 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]

theorem low_16 : Lower dom_16 roots_16 goal_16 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000000000, 35, 51)] (by decide +kernel) (by decide +kernel) low_15

def dom_17 : Nat := 0xffff00000000
def goal_17 : Nat := 0xe80000000000
def roots_17 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]

theorem low_17 : Lower dom_17 roots_17 goal_17 5 :=
  lower_iso [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16

def dom_18 : Nat := 0xffffffff00000000
def goal_18 : Nat := 0xfee8e80000000000
def roots_18 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]

namespace S_18
def pairsG : List (Nat × Nat) := [(35, 43), (35, 51), (37, 45), (37, 53), (38, 46), (38, 54), (39, 47), (39, 55), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (49, 51), (49, 53), (49, 57), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [35, 35, 37, 37, 38, 38, 39, 39, 41, 41, 41, 42, 42, 42, 44, 44, 44, 49, 49, 49, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [43, 51, 45, 53, 46, 54, 47, 55, 43, 45, 57, 43, 46, 58, 45, 46, 60, 51, 53, 57, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x1fffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_18.map (· &&& dom_18)
def goalM : Nat := goal_18 &&& dom_18
def NN : Nat → Nat
  | 5 => 11
  | 6 => 30
  | 7 => 15
  | 8 => 5
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xba21efada27474d18c6a13d082d8c7387e0deb884f2add684ceed08b272ddd642525296c1ce37a80144f6d7f
  | 6, 0 => 0xeb3cd251bbdecaa7a9c050029470a9f88c75cfe67ba284766fcf02146da756715ac36ba153f9e76649b5579a4733f71f4026727a3cf1ebab2f1357842d52862f28d71a2c2731420a26afad252262b0be1faa7bc51e537da918ea334317201853145943500c98d0c70857869e0488d079029e966e025ffba9
  | 7, 0 => 0xa209b34a9679e0108a38227884bf332e5cc73d0639b6c7fa3135523426f346c024cbd9b921207d740ca2a6980c640bd30854d8be062d6bb7030e6323
  | 8, 0 => 0xbe37fa2f8ec343583bd8c2aa1f3caa08009e3c06
  | 9, 0 => 0xbe37fa2f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f0000000005ff05ff00000000030303030000000000ffffff0000000000ff00ff0000000000fcfcfc0000000000555555000000000000ffff00000000
  | 0, 1 => 0xfa00fa0000000000f0f0f0f000000000eeeeeeee00000000eeee000000000000cccccccc00000000aaaaaaaa0000000055555555000000003333333300000000
  | 0, 2 => 0xfeaafeaa00000000feaaaaaa00000000fe00fe0000000000fcfcfcfc00000000fca8a8a800000000fc00000000000000fafafafa00000000fafa000000000000
  | 0, 3 => 0xffeeeeee00000000ffcccccc00000000ffaaaaaa00000000ff05050500000000ff00ff0000000000ff00000000000000fefefefe00000000fefe000000000000
  | 0, 4 => 0xffff000000000000fff0f0f000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x1538b280500e2480c0502151134356903ce2ca685e75b38d685b38b282685c6ce2ca685b59438b685b4ce2ca685b69444d601b2481c05
  | 6, 0, 0 => 0x85b40f38b29c085138d2c360216ce2c911806cf38b280685b38d2ca11c085138a203685e6d138b29c00216c9207585b69438d29e16d750e2ca70216ce2c9158001b2881c050006d838b296181b6912ca701b38b285018044e2ca0c06
  | 6, 0, 1 => 0x85b69938b29c00216d444d502179b38b25a179d6ce2ca700038b24301616d448e2ca785b44e2ca19e16da38b285702164e2ca0da17db68e2ca76da38d30b29c085b3ce288685b68e2ca05c085b68e2486
  | 7, 0, 0 => 0x85e6ce2ca600084e2c90d4085b64e2ca600038b283014085b44e34b685b45038b29c085b3ce2ca60216da38b25a16da38d2ca70216ce2ca118085b38b285602144e2ca0d800216cb24750216cd2ca1da179b68e2ca7
  | 8, 0, 0 => 0x216ce2ca502138b283585b44e2ca685b68e2ca60216cb2875
  | 9, 0, 0 => 0x216ce2ca5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 40
  | 6 => 46
  | 7 => 46
  | 8 => 40
  | 9 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe3f1f81fff8e3ff81c0e003ffffff1ff007f8fc7e3fc7e3f060001ffff
  | 0, 1 => 0xe3800e0703f00fc7ffe07e00000381c7980381f3ffe3f061f8fc70c
  | 0, 2 => 0x7ffe780381f3c003fe003f1f8ff00000678000000071f8ffe38e0000
  | 0, 3 => 0xe3f1ffff1c0e3cf81c0f9fc703800e00ff80700000007fffffe3fe0000
  | 0, 4 => 0x3ffc0001f81c0fc
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x62d1681a7d882a881008001b6dbff0db005506db6ffc2412060000db55
  | 0, 1 => 0xb04efaace974bf1bfdfffedfe24aa4b95cf992793f3f6c3606168d460c
  | 0, 2 => 0xf6fffeffb7dbf3fc93feabbf7fbffd6bb5e7e9048002f7fbfff7bf04aa
  | 0, 3 => 0xffffffffdeef7cfdbedf9fe492400f24ffaaf9249003ffffffffff24aa
  | 0, 4 => 0x3ffe4955fedf6fc
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 29 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 29 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 34 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 34 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 34 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 34 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 20
  | 5 => 90
  | 6 => 240
  | 7 => 62
  | 8 => 6
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xc62c05adbe37fa2fbbdecaa7931d9bbb81bea9ef75594e2a630bec675aa324ff4f8473d84ad62b212fbc7f372cb5bfca1cf63ef70ec26afc0abbccdb0a508e270857869e06daf7fc01e17b5f0099a2eb
  | 5, 0 => 0x453d1efe43db727042117ce33ed52e3c3dd6ddcf3d4207373afce0b738f7e84538e8efc73707ab7836b8a2c7365b56a433ac96dd3395236f313552342edc22ac2e02026129503fe228bc788d2883d810276875a02542093d252aafb0252473592514be5721efec8a215e16aa21207d74211e8b4b1f6322c71d5826a51b2093801b0950cc19e3ce0218a23b3d184439cf17901bf116dd164e1641c089150c3ef4147f040b14549e511175dd8e10b7511e0f26f2fc0f1a9f9e0de6b64f0dd51b0b0ca2a6980b0cf6f70a792db50a49771009c37d2f0947bd550854d8be07c5bc5d06ddb54b068c41ae065925a3053f542804c0e097028cb2af0191714600f78174
  | 5, 1 => 0xece81f09d2caae12d03ad330be37fa2fb159e859ae1c0baba209b34aa0dcb18f9679e0108a38227887def2f084bf332e796eaad76b6cf28f6addde04699d56bb657e7d9661a173c55ffa8a495cc73d065789078a52a5575051480b605032f2204e1f40a24974c94e
  | 6, 0 => 0x9ff740609f10bd809c9da980965dd36093a647408da21f508a25ff4089d53ff08568d59083a01c5081ba09a08092a2707d8eaf307a309fe07998486075cce280748049506e70f9d0662749a06502fd3061e7e5305fad78805dd958d05c6981c05927736055759740530bd460509f9f104f2368f04dfcf2f046ef2a104461200040b6b7e03e9007003cc752003b655dd03a0ecaa0323c98a030e632302f432fe029c4ceb027017af026ec85e02692d5d025fde66023a6f2002341d6d022fd7f601fe84f301f29d9801eb5c9a01c09b5d0183c7bc013d51ec0120fbfd00fff5f600efce6a00ecd4c6009e3c06008f1c860080868000481dee0045591d003a8162
  | 6, 1 => 0x2170c276216d156221497c9620c5663c2042bf881f9166ce1f3caa081eae4c4e1e8314351e72c63b1e4ff05e1d1aaf581ce2aa2a1bee67311bd179c11bba91421a9efd7a1a7a122a1a04c57219c9c34c19b29625197604f918195c7c17ab5c8b179039eb1764b84e175a3fe4171c6d4a167c5bcf15e55be6153d4b4715328dd8150984de141aa88b135e702a135dbe78133e749e1331d8c1131a18a0123c44e81231d64911e5f645113527d810f66fd01088f9d3105d35cd1002dc290ff7638a0f4364520ef413c60ee017130e32f4250ddd8bba0dda7f9c0d77cf810ca5baa20c9a5ea10c427d260c359d8e0bf1479f0bbb14f40b93fc150b6cc53e0a33df00
  | 6, 2 => 0x4b1cd485499f04034861c35b47cc5c68461f92514584eadf43ef791b40a1a2fa3d39c4643d34c4533bd8c2aa3aa6769e39ceb81b39b6c7fa38ac29c738aada7637c0d51a3633f52435864be5356b9add34f7890734c17b303485ec763437e2703361253f32ddd92b32c6a6fc31a22caa3177742f30d919492ffacb962e3fb9582e2f75df2d635d392d4389e12c3366f62b81eca82b76ae442b6226d42b2bbdc22accd8272a4fced52a40ea7a29ebce2329a28cce2991134529795e01295026c628c7654f282418d8279aa7052750450a272e2c16267394fa25bbc15a249dfbe223ee9a9b23e9c81823cca99c23729338236e4de82365540f22c14378219e86b4
  | 6, 3 => 0xe7a7b673e736f196be37fa2fb8085835b33719dfb137a1f9adbaea369446f44e925731ce91eebf30902628208fe795698ec343588b53b3128928a06185432b03841e682f82252d4d7d70cb1d7c75637c7c0bbeec72c5e1f17294fc737166f7b66e49e513699d56bb69891f236969ce7c6773ab526397053061a53038608724f56003ea3b5f58f1df5ee859a15cddf9e25c2c40ee5b8cf6c65b059c21536d901f52f5d47652527a65514b956f50e596905032f2204f244d7a4f047e0a4d6f0fd6
  | 7, 0 => 0xee476d15be37fa2fb82bd7ebb0753b338ec343588b01ad9d8928a06182252d4d658fd7e663faa34d61b331c45a75b10a598894834d407a0e4167f25b40a2202e3bd8c2aa3adc933337d380e63485ec7631a48ecd2e1603ae2c0dce5c2c07b1f427b583fd25020e8a23ba810b2324783e1f8422301f4b03c71f3caa081d6280541cf2b0081bb7b1301a9ad4001a89ccf817ab5c8b153d4b47153899de15328dd814988863133e749e1179eb0c111707970ddd8bba0c63ee900b93fc150b87d7e60a1a57be08b692ae08846f4a08742150081ba09a07d8eaf3068f25a7048b280d043aaae703cb1e61023a6f200183c7bc00fff5f6009e3c06
  | 8, 0 => 0xb0753b3363faa34d15328dd80b87d7e6048b280d00fff5f6
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x51101320c0000000000000000010440000000000070000032040000000c8101304c5014c0c000008510332084310c00000008510351490300c0000000c810000000000004000004110500000014414000000e101000d0104800000000000621441204c0c0000000009
  | 5, 0 => 0x12481104c0c0000000001000903008000002449203000c110480c003404120100000320404d4414813030000e00880000000000010009010480400000000060009010480400000c8102000d01048000003802203000121048000000000000000900148000000005106000d010480800000411060000001840000000411050000021440c00240412020000003840000038062000000000000c0000041103000000000200000005100
  | 5, 1 => 0x8431080400000c810200000000024000000a10000090104800000000000600012200800003444120300000000010000000000900000000018d4414813030009010480000000000040000021040000000051050000000002000404c42010000032040000000000080000010440c00018022000000000002000048c1203000d010480400008062030000e02880000048c8200000000144140000085103000c83108040024041200
  | 5, 2 => 0x2000000000050010520480c000000000000000000000851048130300101320800000000000400000028400000004110000000104400000380a200000c131480c00048c82000000000001400414c8201000003204088510481304000003204040000000000001053208000004885203000003204080034085203000000000080000000005
  | 6, 0 => 0x411000000000001800000c01010000031040000000021000000032040400008062000000021040400000801000000030040000000c410000000038400000000a1010010520480c00028022000000001840800000411040001210480c00000811030000003840400414c82000000031040400000000010000010440400000c91030000001840000000061000000000000800240412000000912480c0000002102
  | 6, 1 => 0x3840c00008062030000010440c00340412010000e008804000180a2030000020040800000c81020000000001400414c820100000320400000000000300000014400004048c2010000023040000000021010000a00880400000000050000031040000000000060000003840c0000000001000000000080000006103000002104040000005101000002104080004841202000000000200000000005000003204040003806203
  | 6, 2 => 0x14404000000a1000000003840c000000e103000000084000000000008000d0104804000000000100000018404000000610100000000018002404120000000300400000000000000000028400003408120400000018400000000a10200000104400000000a10200000310400000008510300012320800000000e1010000020040000000c81000000002840c0000002103000d010480000000c810000000104408000008c100
  | 6, 3 => 0x10440000404c8201000002304080000006100000d010480000000051010000032040000000c81010000000840000038062040000020040000000811040000e02880400000021020000010441000000c5104000123208080000000004000000184000000002100000d010480c000000e10100101320804000000a1010000003840c000000210000000014400000000e103000123208080000085104000000084000000000000
  | 6, 4 => 0x2400000021000010132080400000000060000000001c000000610000000028400000000e10400090104808000008c1000000021441000000411000001210480400000000040000021040400000000060000010440400028062000000000001c00000000000000000002400000c81010000003840c000380a20300000104404000008c1010000010440c0000081103000000084100000006101000002304040000000008
  | 6, 5 => 0x202880c00000000050000032040400000c51040000001840400000c51030000000001c00000000070000010440000000c81020000000000000048852030000000000800000c4100000d010481000000411040000e028800000000000300000104400000000e1030000a00880400000000080000003840c00000000020000001840c00000411010001220481000000811030000000001400104812040010520481000000c8100
  | 6, 6 => 0x14000000e1030000001840400414812030001210481000000411010000031440c000000e10300000000000000000000600000320400000000210300012320800000000e103000001044080000000000000d010480c00008062010000000001400008062010000e028808000000a1000000001840400000000090001201480000000c810100000000024000004110200000000020000000e1030004120480c0000000006
  | 6, 7 => 0x3840c00000000050000000000000000c81010000000001400000000080000001840000000c5103000003204080000041100000000000140004841201000000284000000000003000000084000000005100
  | 7, 0 => 0xc00000000030000000840400000000040000020441000000021000000021440c00000000050000000001000000000000000032040800000021010000000000c000000000100000000008000000000000000320400000000000100000000000000000210300000000000000000e1040000000000c00000000050000000000400000000000000000000c00000000000000001840c000000e101000000000040000000002
  | 7, 1 => 0x3840c00000000000000000840c00000000030000000000c00000000000000010440400000000080000032040000000000040000000000c000000000100000320408000000000300000000000000004110000000000000000000000100000104400000000e10400000008400000008110300000000008000008110400000028400000000e101000000384000000000001000000000040000000004
  | 8, 0 => 0xc0000000004000000000000000000001000000000000000000003
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_3 roots_3 7 s ws hint
  | 1 => checkCutEntry dom_4 roots_4 7 s ws hint
  | 2 => checkCutEntry dom_5 roots_5 7 s ws hint
  | 3 => checkCutEntry dom_9 roots_9 7 s ws hint
  | 4 => checkCutEntry dom_10 roots_10 7 s ws hint
  | 5 => checkCutEntry dom_12 roots_12 5 s ws hint
  | 6 => checkCutEntry dom_13 roots_13 5 s ws hint
  | 7 => checkCutEntry dom_14 roots_14 5 s ws hint
  | 8 => checkCutEntry dom_16 roots_16 5 s ws hint
  | 9 => checkCutEntry dom_17 roots_17 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_18 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_14 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_17 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_18 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 11 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 8 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 11 → Z 5 i = true := range_split z5_0 (z5_8)
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
theorem z6_24 : ∀ i, 24 ≤ i → i < 30 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 24 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 30 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (z6_24)))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_8 : ∀ i, 8 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 8 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := range_split z7_0 (z7_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 5 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 5 0 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 5 → Z 8 i = true := z8_0
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
  scr dom_18 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_18 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_18 roots_18 goal_18 10 := by
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

theorem low_18 : Lower dom_18 roots_18 goal_18 10 := S_18.noCircuit

def dom_19 : Nat := 0xff000000ff0000
def goal_19 : Nat := 0xe8000000800000
def roots_19 : List Nat := [0xaa000000aa0000, 0xcc000000cc0000, 0xf0000000f00000, 0xff000000000000]

theorem low_19 : Lower dom_19 roots_19 goal_19 7 :=
  lower_iso [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5

def dom_20 : Nat := 0xffff0000
def goal_20 : Nat := 0xfe800000
def roots_20 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]

namespace S_20
def pairsG : List (Nat × Nat) := [(17, 25), (18, 26), (19, 23), (19, 27), (20, 28), (21, 23), (21, 29), (22, 23), (22, 30), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [17, 18, 19, 19, 20, 21, 21, 22, 22, 24, 24, 24]
def r2sG : List Nat := [25, 26, 23, 27, 28, 23, 29, 23, 30, 25, 26, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_20.map (· &&& dom_20)
def goalM : Nat := goal_20 &&& dom_20
def NN : Nat → Nat
  | 3 => 5
  | 4 => 9
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe9e6f74a63b431c25050658d3679b58d12d657c9
  | 4, 0 => 0xe9e6f74accb54ee97394dfb55db483be5b3a80872afaa02716881d271475ee7f0a1afd34
  | 5, 0 => 0xe9e6f74a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccc000000000000aaaa000000000000aa00000000000000a0a0000000000000888800000000000055550000000000000f0f00000000000000ff0000
  | 0, 1 => 0xfff0000000000000ff00000000000000fafa000000000000f0f0000000000000f0c0000000000000f000000000000000eecc0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xdb764e9764dc744da764db864
  | 4, 0, 0 => 0xdb7640d7614dcb7650b7604db7625db7655db7635db7605edb765
  | 5, 0, 0 => 0xdb764
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x18e06d00006000cf92e0f1ff
  | 0, 1 => 0xff0e001fd1f018000018e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x5ae2ed2490e40acd1260b0a4
  | 0, 1 => 0xffff5bbfd9f49f49507ef
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_20 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_20 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
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
  scr dom_20 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_20 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_20 roots_20 goal_20 6 := by
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

theorem low_20 : Lower dom_20 roots_20 goal_20 6 := S_20.noCircuit

def dom_21 : Nat := 0x5555000055550000
def goal_21 : Nat := 0x5440000054000000
def roots_21 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]

theorem low_21 : Lower dom_21 roots_21 goal_21 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 22, 54)] (by decide +kernel) (by decide +kernel) low_2

def dom_22 : Nat := 0xaa000000aa0000
def goal_22 : Nat := 0xa8000000800000
def roots_22 : List Nat := [0x88000000880000, 0xa0000000a00000, 0xaa000000000000]

theorem low_22 : Lower dom_22 roots_22 goal_22 4 :=
  lower_iso [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11

def dom_23 : Nat := 0xaaaa0000aaaa0000
def goal_23 : Nat := 0xaaa80000aa800000
def roots_23 : List Nat := [0x8888000088880000, 0xa0a00000a0a00000, 0xaa000000aa000000, 0xaaaa000000000000]

theorem low_23 : Lower dom_23 roots_23 goal_23 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa000000, 17, 25)] (by decide +kernel) (by decide +kernel) low_22

def dom_24 : Nat := 0x3333000033330000
def goal_24 : Nat := 0x3220000032000000
def roots_24 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]

theorem low_24 : Lower dom_24 roots_24 goal_24 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21

def dom_25 : Nat := 0xcccc0000cccc0000
def goal_25 : Nat := 0xccc80000cc800000
def roots_25 : List Nat := [0x8888000088880000, 0xc0c00000c0c00000, 0xcc000000cc000000, 0xcccc000000000000]

theorem low_25 : Lower dom_25 roots_25 goal_25 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23

def dom_26 : Nat := 0xf0f00000f0f0000
def goal_26 : Nat := 0xe0800000e000000
def roots_26 : List Nat := [0xa0a00000a0a0000, 0xc0c00000c0c0000, 0xf0000000f000000, 0xf0f000000000000]

theorem low_26 : Lower dom_26 roots_26 goal_26 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24

def dom_27 : Nat := 0xf0f00000f0f00000
def goal_27 : Nat := 0xf0e00000f0800000
def roots_27 : List Nat := [0xa0a00000a0a00000, 0xc0c00000c0c00000, 0xf0000000f0000000, 0xf0f0000000000000]

theorem low_27 : Lower dom_27 roots_27 goal_27 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25

def dom_28 : Nat := 0xffff0000ffff0000
def goal_28 : Nat := 0xfee80000fe800000
def roots_28 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

namespace S_28
def pairsG : List (Nat × Nat) := [(17, 25), (18, 26), (19, 23), (19, 27), (19, 51), (20, 28), (21, 23), (21, 29), (21, 53), (22, 23), (22, 30), (22, 54), (24, 25), (24, 26), (24, 28), (49, 51), (49, 53), (49, 57), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [17, 18, 19, 19, 19, 20, 21, 21, 21, 22, 22, 22, 24, 24, 24, 49, 49, 49, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [25, 26, 23, 27, 51, 28, 23, 29, 53, 23, 30, 54, 25, 26, 28, 51, 53, 57, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_28.map (· &&& dom_28)
def goalM : Nat := goal_28 &&& dom_28
def NN : Nat → Nat
  | 5 => 3
  | 6 => 8
  | 7 => 4
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x48f9079a164f92e208082259
  | 6, 0 => 0xcc3c5ec7a663525d980173f74666e6311dd6ec8d1d0e1ddb0fd654cf0f8f7c04
  | 7, 0 => 0x6d9aee5f642f2ee556f046b248a8d629
  | 8, 0 => 0xe704062d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xeeee0000eeee0000cccc0000cccc0000c0c00000c0c00000aaaa0000aaaa0000a0a00000a0a00000555500005555000033330000333300000f0f00000f0f0000
  | 0, 1 => 0xffff000000000000ff000000ff000000fcfc0000fcfc0000f0f00000f0f00000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xba21050ba9525ba95426
  | 6, 0, 0 => 0xba821500ba9545ba8643170ba843160ba862160ba76406ba876407ba864217
  | 7, 0, 0 => 0xba86546ba986460ba8625ba86426
  | 8, 0, 0 => 0xba8645
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 28
  | 6 => 32
  | 7 => 28
  | 8 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3f1fbe070387800070000381dd0000381ff1f88bf1f8f0f1ff01f
  | 0, 1 => 0xfff0001c01c0007e07ff0e00fe0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x6ff7fbe972b97824072212793dd0420789b61b08ad1a8d0b16b01b
  | 0, 1 => 0xfff1221e49d2af7ef7ff4e94fe4
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 27 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 27 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 12 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
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
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 1 zs)
def CN : Nat → Nat
  | 4 => 2
  | 5 => 45
  | 6 => 120
  | 7 => 12
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xe704062da663525d
  | 5, 0 => 0xe704062dd987db39c3a495bdb3aececfae9ca3329dcb89539a083c7a98b95db67f78a79877395b2d6d9aee5f69e6fe92642f2ee556f046b25092d060507fbd1348a8d62943fa576a438f4f2d3bcc5b1038592adc3131b8fd2af0473b26d9a8131efae3671a9f702a1a4a53a019bf032e1883a6e4180c9a161765e85812ebebd2107c1c2c102c3eb70b67da9f0ad4d10a0a0ca55a0a01a69709e66b4b080d5e27050b8cd204611b8f03dca6b103be83af036a9ef1
  | 6, 0 => 0x40110d1f3eac3c7a3da367913d6d6c693c4dc0463bc700d13afee1823acf7f503aca2955394c64ea38592adc36f2f6d436a29505369a81113305a01732bf9e1832bbad0331fcdd0f2f8bbf102ec1fca82d5980dc2ceab1722cbf734b2c82b8cc2aa4429a29193bac286b022327b2db1a2784345826e85d3a233e63f2230cd34d1efae3671d7c9dc01b6933bb1ae9028a1ad1cb231873dac816fcfa81158b6da11223e2f810d20f14106146c1103db58d0ec4daa00e5edbe50b91da940ac6eb2f097e55fa07a1968c078c37560743fd1805d1d91b046ba51303e3fa680233a6e101f6450401c633f201b1114f01aa35bb015b2bb5013f098f011b110700ecabd0
  | 6, 1 => 0xe704062daa87b262a59f2d1ca3c4b190a1d93b6997e2288997a5ab5d96d8d2a4949a53368e77f82a8d704d538a6de2518829d67f87184d938652e2ad850c38b083c704be7ebe17057c3ed0607ae66ad17a33ec5577cd507d75d43f34717f2ed2717aab576e0babe36c687fba6985dff465032555643bc3246337be49613fd87c5ff0f9b85f2997875c2f6a155b9765db57d4190257b1b64e56853a3e55f4529b549d601e538c9fa250e226fe50ccf2874f8b34814e587da84ac5c0754a9530cf4946520b48a8d62947f3d8f346d3b65c4662f51c4574f72141070ea141031d8c
  | 7, 0 => 0xf44f829fef3d5702e704062dde6c3d23daa8f04ad95a11865594250e24ae12b1222234c217936dcc07e10ff80192ee4d
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x21484200
  | 5, 0 => 0x21000000000310440200000021002148420121484201000000040000000400000006000000031044020000000003104402010000000310440200204802010000a10221484201214842000000000300000006000000040000a102104402012048020001802200000000030000000400000003000000031044020010440200
  | 5, 1 => 0x18022000180220121484200214842002148420121484200214842011044020010440200000841000000000600085100
  | 6, 0 => 0x3000000060000000300000000000411000000000100002101000021000008110100000005000401010000000400080100000000050000610100084101000401000004110000000000000021000000000400081100000481000000a101000000030008510100000008000081000008510100040100000000040000a101
  | 6, 1 => 0x210100006100000801000000000300002100000000060000210100000003000000050000210000000004000811000000000300041100000000010000000300002100000000020008010100080101000841010008110100000001000000030000610100041100000061000000000600000003000000050000000500009101
  | 6, 2 => 0x8510000000004000851000000210100084101000021000000210000084100000841010000210000002101000851010008510000000007000851010000210000000004000000000000210000000003000411010000210100009100000021000000210100002100000021010000610100006100000801010000000300002100
  | 6, 3 => 0x4000021000004010000085100000061010000a100000811000000210000048101000401000000a100000841000000a10000002100000491010000210000085100000061010008410000002101000021010008410000002100
  | 7, 0 => 0x10000000000000001000000010000000000000000000000000000000100000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 8 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_19 roots_19 7 s ws hint
  | 1 => checkCutEntry dom_10 roots_10 7 s ws hint
  | 2 => checkCutEntry dom_20 roots_20 6 s ws hint
  | 3 => checkCutEntry dom_21 roots_21 5 s ws hint
  | 4 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 5 => checkCutEntry dom_24 roots_24 5 s ws hint
  | 6 => checkCutEntry dom_25 roots_25 5 s ws hint
  | 7 => checkCutEntry dom_26 roots_26 5 s ws hint
  | 8 => checkCutEntry dom_27 roots_27 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 1 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 1 ys) ys = true) : ¬ RunD dom_28 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_24 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_26 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_28 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_28 == dom_28) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 1 zs symsG zs (hk 1 zs)
theorem ori_ok {u ys} (h : RunD dom_28 goalM u ys) : RunD dom_28 goalM u (ori ys) :=
  pickMin_runD 1 ys h symsG ys (hk 1 ys) symsG_ok h

def Z (s : Nat) := bar dom_28 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 1 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := z6_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := z7_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := z8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
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
def RootG (s : Nat) : Bool :=
  scr dom_28 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_28 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_28 roots_28 goal_28 9 := by
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

theorem low_28 : Lower dom_28 roots_28 goal_28 9 := S_28.noCircuit

def dom_29 : Nat := 0x55005500
def goal_29 : Nat := 0x54004000
def roots_29 : List Nat := [0x44004400, 0x50005000, 0x55000000]

namespace S_29
def pairsG : List (Nat × Nat) := [(10, 14), (10, 26), (12, 14), (12, 28), (24, 26), (24, 28)]
def r1sG : List Nat := [10, 10, 12, 12, 24, 24]
def r2sG : List Nat := [14, 26, 14, 28, 26, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_29.map (· &&& dom_29)
def goalM : Nat := goal_29 &&& dom_29
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xe916f6c9
  | 3, 0 => 0xe916f6c9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5500000000000000500050000000000044004400
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_29 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_29 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_29 == dom_29) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_29 goalM u ys) : RunD dom_29 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_29 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_29 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_29 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_29 roots_29 goal_29 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_29 goal_29 := by
    have h0 : isConstB dom_29 goal_29 = false := by decide +kernel
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

end S_29

theorem low_29 : Lower dom_29 roots_29 goal_29 4 := S_29.noCircuit

def dom_30 : Nat := 0x33003300
def goal_30 : Nat := 0x32002000
def roots_30 : List Nat := [0x22002200, 0x30003000, 0x33000000]

theorem low_30 : Lower dom_30 roots_30 goal_30 4 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29

def dom_31 : Nat := 0xf000f00
def goal_31 : Nat := 0xe000800
def roots_31 : List Nat := [0xa000a00, 0xc000c00, 0xf000000]

theorem low_31 : Lower dom_31 roots_31 goal_31 4 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30

def dom_32 : Nat := 0xff00ff00
def goal_32 : Nat := 0xfe00e800
def roots_32 : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]

namespace S_32
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (12, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [9, 9, 9, 10, 10, 10, 12, 12, 12, 24, 24, 24]
def r2sG : List Nat := [11, 13, 25, 11, 14, 26, 13, 14, 28, 25, 26, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_32.map (· &&& dom_32)
def goalM : Nat := goal_32 &&& dom_32
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x14443de7
  | 4, 0 => 0x6a2be5a8505d8d6d0b1c75d70289835f
  | 5, 0 => 0x8299b27f5d5bb24528a66142
  | 6, 0 => 0x8299b27f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000f000f00000000000ee00ee0000000000cc00cc0000000000aa00aa000000000033003300000000000f000f000000000000003300
  | 0, 1 => 0xff00ee0000000000ff00cc0000000000ff00aa00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x98654
  | 4, 0, 0 => 0x73214a76435764305986435
  | 5, 0, 0 => 0x76434074314765435
  | 6, 0, 0 => 0x76434
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe001c003f038007fc7e3f1c7
  | 0, 1 => 0xe3fe38e07
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf249d26ff4b924fb4662d042
  | 0, 1 => 0xffffbdf6f
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 12 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 12 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 11 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 11 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 11 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 11 then wireAt i else 0
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
  | 2, 0 => 0x1ce97366
  | 3, 0 => 0xada99f5a8299b27f108e74cf01eed52c
  | 4, 0 => 0x8299b27f5d5bb2452ca9e11e28a66142170f4d9c0f534c000e21469b032235bb
  | 5, 0 => 0xe21469b032235bb
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 2, 0 => 0x1
  | 3, 0 => 0x80000000000400001
  | 4, 0 => 0x2000000000000000000000000000400001
  | 5, 0 => 0x400001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_29 roots_29 4 s ws hint
  | 1 => checkCutEntry dom_30 roots_30 4 s ws hint
  | 2 => checkCutEntry dom_31 roots_31 4 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_32 == dom_32) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_32 goalM u ys) : RunD dom_32 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_32 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_32 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_32 roots_32 goal_32 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_32 goal_32 := by
    have h0 : isConstB dom_32 goal_32 = false := by decide +kernel
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

end S_32

theorem low_32 : Lower dom_32 roots_32 goal_32 7 := S_32.noCircuit

def dom_33 : Nat := 0xaaaaaaaa
def goal_33 : Nat := 0xaa80a800
def roots_33 : List Nat := [0x88888888, 0xa0a0a0a0, 0xaa00aa00, 0xaaaa0000]

theorem low_33 : Lower dom_33 roots_33 goal_33 6 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20

def dom_34 : Nat := 0xcccccccc
def goal_34 : Nat := 0xcc80c800
def roots_34 : List Nat := [0x88888888, 0xc0c0c0c0, 0xcc00cc00, 0xcccc0000]

theorem low_34 : Lower dom_34 roots_34 goal_34 6 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20

def dom_35 : Nat := 0xf0f0f0f0
def goal_35 : Nat := 0xf080e000
def roots_35 : List Nat := [0xa0a0a0a0, 0xc0c0c0c0, 0xf000f000, 0xf0f00000]

theorem low_35 : Lower dom_35 roots_35 goal_35 6 :=
  lower_iso [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20

def dom_36 : Nat := 0x55555555
def goal_36 : Nat := 0x54004000
def roots_36 : List Nat := [0x44444444, 0x50505050, 0x55005500, 0x55550000]

theorem low_36 : Lower dom_36 roots_36 goal_36 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x55005500, 6, 14)] (by decide +kernel) (by decide +kernel) low_29

def dom_37 : Nat := 0x33333333
def goal_37 : Nat := 0x32002000
def roots_37 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]

theorem low_37 : Lower dom_37 roots_37 goal_37 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_36

def dom_38 : Nat := 0xffffffff
def goal_38 : Nat := 0xfe80e800
def roots_38 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

namespace S_38
def pairsG : List (Nat × Nat) := [(3, 11), (5, 13), (6, 14), (7, 15), (7, 23), (9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (12, 28), (17, 25), (18, 26), (19, 23), (19, 27), (20, 28), (21, 23), (21, 29), (22, 23), (22, 30), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [3, 5, 6, 7, 7, 9, 9, 9, 10, 10, 10, 12, 12, 12, 17, 18, 19, 19, 20, 21, 21, 22, 22, 24, 24, 24]
def r2sG : List Nat := [11, 13, 14, 15, 23, 11, 13, 25, 11, 14, 26, 13, 14, 28, 25, 26, 23, 27, 28, 23, 29, 23, 30, 25, 26, 28]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_38.map (· &&& dom_38)
def goalM : Nat := goal_38 &&& dom_38
def NN : Nat → Nat
  | 5 => 2
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x2de50cfb1d85073f
  | 6, 0 => 0x27b9bfe120bc0fdd03732ac5
  | 7, 0 => 0x1e29e5df14e17f6b
  | 8, 0 => 0x1f16380d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccccccc00000000cccc000000000000aaaaaaaa00000000aaaa000000000000a0a0a0a000000000555555550000000033333333000000000000ffff
  | 0, 1 => 0xffff000000000000ff00ff0000000000f0f0f0f000000000eaeac0c0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xba987560a92105
  | 6, 0, 0 => 0xa95105ba9765370ba95416
  | 7, 0, 0 => 0xba976560ba9725
  | 8, 0, 0 => 0xba9755
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 28
  | 6 => 32
  | 7 => 28
  | 8 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x18e1c7463800006d03ec1b4000060006be4bf04e71e388003fff
  | 0, 1 => 0xfff0003803fe01f0e0787b401c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x5ae5cf56b84102ed27ecbb40900e4216b44b604a51a308001b6f
  | 0, 1 => 0xfff9243d6ffef9f4e978fb529c
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 12 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
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
  | 4 => 1
  | 5 => 8
  | 6 => 38
  | 7 => 7
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x1f16380d
  | 5, 0 => 0xa254e4fa474b5a80429af6de1f16380d1e29e5df1ae126f514e17f6b033350e5
  | 6, 0 => 0x9bbcfe5f62446dd55b4f406c5b18a81b564c935647e1d63d472e25f73fae359034868e872fe39c9c2515df9721c99be51f436d281f16380d1e3bac671b578f6c1b2ce85219ef57cd199f5f93162a946a15fb06b41463a74f1288ee2a117fcf9b105d54730e8cab400e7383530c6da9dc0afc43060aa4161f0974d4bb08211c8608088c3707c232ef045f366803558ff102ee6cc5001d64ce
  | 7, 0 => 0xea902df2ceef2316564c935634b0cb8f1f16380d0d59fc0a090d6eb4
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x500000001000c410100000000000c4100028022000000210000002101
  | 6, 0 => 0x2000c010000084100000000050000a100000000010000000200000000000061000000210000006103000c81000000000300000001000000010000e10200000000000000010000a100000c010000000001000c010100040100000000060000a100000c4100000c01020008410400084100000c0102000c01000000e102
  | 6, 1 => 0x801000000a100000c0100000000050000a10000000006
  | 7, 0 => 0x300000000000000000000000100000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_32 roots_32 7 s ws hint
  | 1 => checkCutEntry dom_33 roots_33 6 s ws hint
  | 2 => checkCutEntry dom_34 roots_34 6 s ws hint
  | 3 => checkCutEntry dom_35 roots_35 6 s ws hint
  | 4 => checkCutEntry dom_20 roots_20 6 s ws hint
  | 5 => checkCutEntry dom_36 roots_36 5 s ws hint
  | 6 => checkCutEntry dom_37 roots_37 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_38 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_33 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_34 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_35 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_20 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_36 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_37 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_38 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_38 == dom_38) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_38 goalM u ys) : RunD dom_38 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_38 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
theorem z6_0 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := z6_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := z7_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := z8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
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
def RootG (s : Nat) : Bool :=
  scr dom_38 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_38 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_38 roots_38 goal_38 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_38 goal_38 := by
    have h0 : isConstB dom_38 goal_38 = false := by decide +kernel
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

end S_38

theorem low_38 : Lower dom_38 roots_38 goal_38 9 := S_38.noCircuit

def dom_39 : Nat := 0x5555555555555555
def goal_39 : Nat := 0x5440400054004000
def roots_39 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

theorem low_39 : Lower dom_39 roots_39 goal_39 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555555500000000, 22, 54)] (by decide +kernel) (by decide +kernel) low_3

def dom_40 : Nat := 0x2222222222222222
def goal_40 : Nat := 0x2220200022002000
def roots_40 : List Nat := [0x2020202020202020, 0x2200220022002200, 0x2222000022220000, 0x2222222200000000]

theorem low_40 : Lower dom_40 roots_40 goal_40 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_21

def dom_41 : Nat := 0xa0a0a0a0a0a0a0a
def goal_41 : Nat := 0xa0808000a000800
def roots_41 : List Nat := [0x808080808080808, 0xa000a000a000a00, 0xa0a00000a0a0000, 0xa0a0a0a00000000]

theorem low_41 : Lower dom_41 roots_41 goal_41 5 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40

def dom_42 : Nat := 0xaa00aa00aa00aa
def goal_42 : Nat := 0xa8000000800000
def roots_42 : List Nat := [0x88008800880088, 0xa000a000a000a0, 0xaa000000aa0000, 0xaa00aa00000000]

theorem low_42 : Lower dom_42 roots_42 goal_42 5 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_16

def dom_43 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_43 : Nat := 0xaaa8a800aa80a800
def roots_43 : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]

namespace S_43
def pairsG : List (Nat × Nat) := [(3, 11), (5, 13), (7, 15), (7, 23), (9, 11), (9, 13), (9, 25), (17, 25), (19, 23), (19, 27), (19, 51), (21, 23), (21, 29), (21, 53), (35, 43), (35, 51), (37, 45), (37, 53), (39, 47), (39, 55), (41, 43), (41, 45), (41, 57), (49, 51), (49, 53), (49, 57)]
def r1sG : List Nat := [3, 5, 7, 7, 9, 9, 9, 17, 19, 19, 19, 21, 21, 21, 35, 35, 37, 37, 39, 39, 41, 41, 41, 49, 49, 49]
def r2sG : List Nat := [11, 13, 15, 23, 11, 13, 25, 25, 23, 27, 51, 23, 29, 53, 43, 51, 45, 53, 47, 55, 43, 45, 57, 51, 53, 57]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_43.map (· &&& dom_43)
def goalM : Nat := goal_43 &&& dom_43
def NN : Nat → Nat
  | 4 => 2
  | 5 => 14
  | 6 => 6
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x66b2192036102e96
  | 5, 0 => 0xd50be031c6d7b408b3d718eba1eafae09130875c84234c076d77f70d454d87e036a3511227a6bb441bd3cf650c58d0d4057b4093050176d2
  | 6, 0 => 0xdac949decef65dffab3dcdb05b1a3bce43411736209a85a7
  | 7, 0 => 0x5e605c4a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0a0a0a0a0a0a0a0888888888888888822222222222222220a0a0a0a0a0a0a0a020202020202020200aa00aa00aa00aa00220022002200220000aaaa0000aaaa
  | 0, 1 => 0xaaa80000aaa80000aaa0aaa0aaa0aaa0aaa00000aaa00000aa88aa88aa88aa88aa00aa00aa00aa00a8a8a8a8a8a8a8a8a8a8a8a8a800a800a8a80000a8a80000
  | 0, 2 => 0xaaaaaaaaaa00aa00aaaaaaaa00000000aaaa0000aaaa0000aaaa0000aa000000aaa8aaa8aaa8aaa8
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x24b49ccb37ace65
  | 5, 0, 0 => 0x9ca0b399a725a0e6604ce610167259cc1604d6620167259cc360524b31167272d4669c9ab399a925a8e66051673014128ace6504e4620941392ca45
  | 6, 0, 0 => 0x9c96a39981359cc050524b39967262ce6604e4730941392cc45
  | 7, 0, 0 => 0x1392ce65
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 29
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3ce0380cc70dfcce3cbf0c7f1fc003c38fff8fe0ce2087fc07f
  | 0, 1 => 0xfc007f387e000e0007cc77d1c001c00fff0f03f0000003f00
  | 0, 2 => 0x3ffc070fff0003803f80e0000007fff7f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x4bce4b89ccf1dd8cc38ad0c6d190003018aad084088000354037
  | 0, 1 => 0xf2aff237f7bffd28ef22fddfff9d54bddbfff3f6ffd8dd8abf08
  | 0, 2 => 0x3fff6f7fff9003cabfc8f2adb03ffffff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 26 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 26 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 21 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 21 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 21 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 21 then wireAt i else 0
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
  | 3 => 1
  | 4 => 15
  | 5 => 48
  | 6 => 19
  | _ => 0
def CH : Nat → Nat → Nat
  | 3, 0 => 0xe3d89ae6
  | 4, 0 => 0xfdcde88fb4bf5c95ad4379ecab3dcdb0a4cd3d0a79a2af3c7894c91471d3db635e605c4a4e51bdca4d29f8b04b130e4a3ab909f024497273136a2647
  | 5, 0 => 0xf792a286ecd2225de589b82be005d0a5c7eb9b56b59af58aac8c50aba990eda9a34b6ba89b42cd0c98783ad792f463fb901e889c8cd719ee88d9eb1d83f16c41767f41016a9fc85465e53f73642dcbac5e605c4a5cb37c4357efcba44d85b6df4d23283244dd87b244a37cc2445488ea4068d2853dedd4ef3dd6f78f37bcedfd3449786832ead51d316322c52e061fc229a1cf9b1dc256ee1afbc70c19bbb7e1138caa3f0644876a063ec742034b68f402db91f40121d32500a8096400a71648
  | 6, 0 => 0xfe98e010f7c60b5ce128ae5cd0ba3a9ecde6f350b55aeff39f43274498ac46c58fde8305758192a35e605c4a5cb37c434f85b93229a1cf9b1dc256ee1c4118391161fe3608bc17b400e1cd8e
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 3, 0 => 0x400c5201
  | 4, 0 => 0x500000000000c5101000000010000000300081104000000003408520000000003000c8103420c52010000000000000002
  | 5, 0 => 0xc9104000c510100085100000c5102000000000000a10000000001000411000004110000000003000000030004110000000003000051000000000500000005000c510100000001000c5101000c51010000e1000000210000000002000c910400000004000000010000000500000000000000010000a1000000210000000005
  | 5, 1 => 0xa100000000010000000300085104000000000000a10000000000000000030000000400000004000c910400006100000000030000e1000000000100085100
  | 6, 0 => 0x40000000100000000000000000000000000000002000000030000000000000004000000000000000300000002000000040000000100000000000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_33 roots_33 6 s ws hint
  | 1 => checkCutEntry dom_40 roots_40 5 s ws hint
  | 2 => checkCutEntry dom_41 roots_41 5 s ws hint
  | 3 => checkCutEntry dom_42 roots_42 5 s ws hint
  | 4 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 5 => checkCutEntry dom_12 roots_12 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_43 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_33 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_40 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_41 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_42 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_12 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_43 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_43 == dom_43) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_43 goalM u ys) : RunD dom_43 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_43 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
theorem z5_8 : ∀ i, 8 ≤ i → i < 14 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 8 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 14 → Z 5 i = true := range_split z5_0 (z5_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 6 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 0 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 6 → Z 6 i = true := z6_0
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
  scr dom_43 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_43 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_43 roots_43 goal_43 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_43 goal_43 := by
    have h0 : isConstB dom_43 goal_43 = false := by decide +kernel
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

end S_43

theorem low_43 : Lower dom_43 roots_43 goal_43 8 := S_43.noCircuit

def dom_44 : Nat := 0x3333333333333333
def goal_44 : Nat := 0x3220200032002000
def roots_44 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]

theorem low_44 : Lower dom_44 roots_44 goal_44 8 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39

def dom_45 : Nat := 0xcccccccccccccccc
def goal_45 : Nat := 0xccc8c800cc80c800
def roots_45 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]

theorem low_45 : Lower dom_45 roots_45 goal_45 8 :=
  lower_iso [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43

def dom_46 : Nat := 0xf0f0f0f0f0f0f0f
def goal_46 : Nat := 0xe0808000e000800
def roots_46 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]

theorem low_46 : Lower dom_46 roots_46 goal_46 8 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_44

def dom_47 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_47 : Nat := 0xf0e0e000f080e000
def roots_47 : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]

theorem low_47 : Lower dom_47 roots_47 goal_47 8 :=
  lower_iso [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45

def dom_48 : Nat := 0xff00ff00ff00ff
def goal_48 : Nat := 0xe8000000800000
def roots_48 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]

theorem low_48 : Lower dom_48 roots_48 goal_48 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff0000, 7, 23)] (by decide +kernel) (by decide +kernel) low_19

def dom_49 : Nat := 0xffff
def goal_49 : Nat := 0xe800
def roots_49 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

theorem low_49 : Lower dom_49 roots_49 goal_49 5 :=
  lower_iso [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_37

def dom_50 : Nat := 0xffffffffffffffff
def goal_50 : Nat := 0xfee8e800fe80e800
def roots_50 : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

namespace S_50
def pairsG : List (Nat × Nat) := [(3, 11), (5, 13), (6, 14), (7, 15), (7, 23), (9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (12, 28), (17, 25), (18, 26), (19, 23), (19, 27), (19, 51), (20, 28), (21, 23), (21, 29), (21, 53), (22, 23), (22, 30), (22, 54), (24, 25), (24, 26), (24, 28), (35, 43), (35, 51), (37, 45), (37, 53), (38, 46), (38, 54), (39, 47), (39, 55), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (49, 51), (49, 53), (49, 57), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [3, 5, 6, 7, 7, 9, 9, 9, 10, 10, 10, 12, 12, 12, 17, 18, 19, 19, 19, 20, 21, 21, 21, 22, 22, 22, 24, 24, 24, 35, 35, 37, 37, 38, 38, 39, 39, 41, 41, 41, 42, 42, 42, 44, 44, 44, 49, 49, 49, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [11, 13, 14, 15, 23, 11, 13, 25, 11, 14, 26, 13, 14, 28, 25, 26, 23, 27, 51, 28, 23, 29, 53, 23, 30, 54, 25, 26, 28, 43, 51, 45, 53, 46, 54, 47, 55, 43, 45, 57, 43, 46, 58, 45, 46, 60, 51, 53, 57, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3ffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_50.map (· &&& dom_50)
def goalM : Nat := goal_50 &&& dom_50
def NN : Nat → Nat
  | 2 => 1
  | 3 => 2
  | 4 => 5
  | 5 => 15
  | 6 => 66
  | 7 => 142
  | 8 => 135
  | 9 => 55
  | 10 => 12
  | 11 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x8d226f10
  | 3, 0 => 0x8b30509b106373b8
  | 4, 0 => 0x4fddf72446d0392c4397c8a32c109d9d19f8ce00
  | 5, 0 => 0x6f15dc165e8887eb53fea15050edb0c53c59855b2cde607b2999c479271792d71c7062971c197fb0153a16820e76718d0b20184f0a07e2ee0436cc8f
  | 6, 0 => 0xaf635f38aed6d184ae0b36e8ac60903aaae1fd15a72dd29b96d3c1f49075d4ed8eb727da893370a88519ab5e818508cc7cf0128b772c08fa6dd4c46a6b96281a6ab59110662a881c6519e0fc6218b51b618933b15deb2e0b55caf4b255323f715325371252d3b80b50cfd3964e9c2aab4e80cd004e74a0624c5dd91241fa0a65417f07b83f6e79283f09bbe03cb6607834611c3230c0902d2d71d2a02d4634112b3eefbd2a5a14ac290d6b402755f3c626637af123d841be228a5d192211b6a72161d63b1fea34281e5b2b561e02c5a91d5da4591b585c5816259eb913c672e310833dc21079d7e20f5bedd60c555e5509881bd6073f8bb8047871020083c8db
  | 6, 1 => 0xcd9696f9b10e05e6
  | 7, 0 => 0x3494badd3295b93f3124ce0530f4f2c02f635ed12f61fd3e2e9ebd8c2de3c4072ddd34cc2bab2f992b32cb7b28bd3d0e28897075268e5108266c4ff725f259af25363552238b820a236d5448231558ef2302abfa2230c4ff211c88cd1efcc0321e19b9cf1d5adde71c9f93801c005fea1b75a31c1b5666c019441ad5193f596018fd90ec1809acf917709a7e172716e716f97e3916adeef2166f9eb5142a5450108192020fae703d0f84075a0d4dd6010ac2abd80900f93307e2750a07aacc6007a4e281071e3eac067389510660c025061859ac05e1695b05810d1c04d1c770040a5c2303e4a4da03bff91b02ee86dc01cef872013b0f8e012d094600c7081f
  | 7, 1 => 0x9da3cc01960d74478e5ca8f1858da13983bcd23d834ae0fd81997033807ea0927ee583167eb965fa7a6696b479f8bc247763c7b67302284172d536c86eb7f9026d7cb67e6c4657b36af71a59698bf0f065c81f7361e02eba61ca67005a5e143d59d707dd5801773c572d178e571a870b5353f9b652fac21252f6d1c452e1ce9350ff2b2c50183afb4ffcca9d4dfc5c2e4d156bfd4cf9fb9f4ac4837a45b40a3045640e6d44900f80447dfcb5436302be434ce739425360d3423e36684235ba2e4184d86d414cda5f3f5091d53ee4112f3acb45dc3a3eb8283a1dd436398348203953cc0938fd1471385956c33849ed0037c876de379789db3777030d35477bce
  | 7, 2 => 0xec0c51aae4133eb5e1c40961dec13a63d98e7cc4d041a975bda628c6bc3aff5db8aade0fb77a5587b2077d9dacd819a0abb62907a5a9d07f
  | 8, 0 => 0x28b9f83a28b95572282e06e528263dc82616f985258735bc249fa8ed219cd9ef21367429211c770b207f8d1d1f9d1eaa1f52d15f1e0e25f51cbc32921ca3ecd51b0b56f717e1bcc015d8995815b2180b1549a13b147c82a61246d1311112dea910df70b00f5126ba0f3ded470f27c4520e7961bd0e47552b0e12afb30ddca1b20c4e57bc0b7a942e0b44862d0a2f584f0a2e92260a2d96460a10929909f74c3909f6a97109f28ac409c585720973c895094d59ab08e0b0eb0812288507544d84071b9a1d070dc39b06efbbc6062713660619dfa806180995055a1c1003edf0f9032d0c3f02ec685a02574d1201a7fa9d00b463a30090255e002a3d4100078767
  | 8, 1 => 0xa4348a8da367abb2a131bb8f9bec9b199a9acdfb97fd4cb2873e36d9805ab07f7832f0487785a42f7482d5316ea207256b02382668612678655e577a602b99db5fce71e95e6b01b65dd6cb515cefdb205cdca4b35cd46ac25ac136f2579c239f56bbf64c5563562352cb3a9e50b89d45508b985b5011b35a4f2b00f84e610a134e247a844bc8ee8e4b5e3b1549edf18d491c06c648c61f9047ebbf8e47db1c1147a2e601450f495c446f2a0044652ab3435f45b34112bc07410704733e17729e3e11bec13e0cfd4c3b0a2e4e3492c5453374411c3365f12d32c9f9d431f5f1443173356d30e7aefa306393822df428f22d60c4842a43297828f0424728d8000f
  | 8, 2 => 0xe472e052c062a745ba4cff06b56961ffab3e3eecab36d69da84437c5
  | 9, 0 => 0xf6f0e39ac979a565b10c2ab2a4d4ecd7850a906d845d44547693aa237538c69d6e31842f5efb1e4f5e4ba7e15b38aa3858a08eb357495bd154468cd34ddea498499ff207469d2309437388d2416a656a40db6d4d3d3b33a73c713cc239d9213d396e6dc437fac1db36d6523f34fddded317749122c21f1702a4f3d2e2692f6d4239027d6234cf11e2289b830204a22201f563e2d1db710d51c28c6df1b1ef55016e832be16ca2ae915b8511012feb38b1231bc351004ac640c4c0fe20af3e8430a8396b309a176d608c57b070737cead0631e9ad0492c531025b429a
  | 10, 0 => 0xbd3f3ec9b63cf2b9b33a23bb6420fbf65677922c4948dce746b0c162455e4ff544d262003024914303c883bf0041eee4
  | 11, 0 => 0xc31492de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55ffff0055ffff0033ffff0033ffff0032fafa0032fafa00135f5f00135f5f0000ffff0000ffff000055ff55ff55ff000033ff33ff33ff00000fff0fff0fff
  | 0, 1 => 0x3570357035703570303ffff0303ffff030303ff03ff03ff0302ffaa0302ffaa010533ff010533ff00ff00ff00ff00ff00ff00ff000000000077777700777777
  | 0, 2 => 0x111111ff11ff11ff0f0f0f0f0f0f0f0f077707770777077707077777070777770537053705370537050f55ff050f55ff0505ffff0505ffff050505ff05ff05ff
  | 0, 3 => 0xa0a0a0a0a0a0a0a0888888888888888855555555555555553333333333333333153f153f153f153f15153f3f15153f3f111f111f111f111f1111ffff1111ffff
  | 0, 4 => 0xaaaaaaaaaaaaaaaaaaaaa000a000a000aaaa880088008800aaaa0000aaaa0000aaa8aa00aaa8aa00aa808080aa808080aa00aa00aa00aa00a888a000a888a000
  | 0, 5 => 0xe0a0c000e0a0c000ccccccccccccccccccccc000c000c000cccc0000cccc0000cc808080cc808080cc00cc00cc00cc00c8c8c800c800c800c0c0c0c0c0c0c0c0
  | 0, 6 => 0xec00a000ec00a000eaeac0c0eaeac0c0eac0eac0eac0eac0ea00c000ea00c000e8e8e8c0e8c0e8c0e8e8e8a0e8a0e8a0e8e8e888e888e888e0e0e000e000e000
  | 0, 7 => 0xeeee000000000000eee0eee0eee0eee0eee00000eee00000eeccaa00eeccaa00eeaacc00eeaacc00ececa0a0ececa0a0ececa0a000000000eca0eca0eca0eca0
  | 0, 8 => 0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0808080f0808080f000f000f000f000eeeeeeeeeeeeeeeeeeeeee00ee00ee00eeeee000e000e000eeee0000eeee0000
  | 0, 9 => 0xfac8fac8fac8fac8fac80000fac80000faaaf000faaaf000f8f88888f8f88888f8f8888800000000f888f888f888f888f8880000f8880000f8008800f8008800
  | 0, 10 => 0xfce8e8e8fce8e8e8fca8fca8fca8fca8fafafafafafafafafafafa00fa00fa00fafac800c800c800fafa0000fafa0000faf0aa00faf0aa00fae8e8e8fae8e8e8
  | 0, 11 => 0xfeeefaaafeeefaaafeeef000feeef000feeef000f000f000feeef00000000000fcfcfcfcfcfcfcfcfcfcfc00fc00fc00fcfc0000fcfc0000fcfc000000000000
  | 0, 12 => 0xfefeccccfefeccccfefeaaaafefeaaaafefe0000fef00000fefe0000fecc0000fefe0000feaa0000fefcaa00fefcaa00fefafcf0fefafcf0fefacc00fefacc00
  | 0, 13 => 0xffa0a0a0ffa0a0a0ff888888ff888888ff00ff00ff00ff00ff000000ff000000fefefef0fef0fef0fefefeccfeccfeccfefefeaafeaafeaafefef0f0fefef0f0
  | 0, 14 => 0xffecececffecececffeaffc0ffeaffc0ffeaeaeaffeaeaeaffccffccffccffccffcc0000ffcc0000ffc0c0c0ffc0c0c0ffaaffaaffaaffaaffaa0000ffaa0000
  | 0, 15 => 0xfff8ff88ff00ff00fff8f8f8fff8f8f8fff88888fff88888fff0fff0fff0fff0fff00000fff00000ffeeff00ff00ff00ffeeaaaaffeeaaaaffecffa0ff00ff00
  | 1, 0 => 0xffffeca0eca0eca0ffffcc00cc00cc00ffffaa00aa00aa00ffff0000ffff0000ffff000000000000fffcff00ff00ff00fffcf0f0fffcf0f0fffaff00fffaff00
  | 1, 1 => 0xffffffff00000000ffffff00ff00ff00fffffcccfcccfcccfffff000f000f000ffffeecceecceeccffffeeaaeeaaeeaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x6d63333
  | 3, 0, 0 => 0x6d64291f4846d6b314
  | 4, 0, 0 => 0x8d846d57225846d6b301e56d65302e275846d54322e56d64542e1f5
  | 5, 0, 0 => 0x847847372e27600846d28270d58d844f4e2a1f6846d695a28276846d542e1f1c6846d4742301e66d635a472e2768d845628210f6008d84441e195846d6a4729276008d5628210358d84776d552b6846d47421e17600846d5a281d58d846f6d502e6
  | 6, 0, 0 => 0x8786846d472e2778d846d4a4947437008d551f1c0a03684836d472e271578b8a846d472d277008483551f1c0a60084551f1c0a0968d846d4f4e2e1f7008d6d4f2e1f0368d8474472a27117846d54472e29277008d84472a27136846d6258472e277008d846d47430868c846d5b28271d78d84443e3d2e277
  | 6, 0, 1 => 0x846d5e5c472e277846d5a472e271d78d846d5b35271b7846d4739372e2778d846d5f472e20700846d47271c0268d846e6d474308700471d1c0a090368d846d472e27057008d846d47431568d846d552e1f0678d846d472e270b78d846d4f2e1f1378d84443e2e2719700552e1f0a0903600008d845628215
  | 6, 0, 2 => 0x84826d66472e277008d74552a1f0360088846d472e256846d472e2d27267846d47422e271778d846f6d552e1c78d846d472e270c7008d846d28270f6846d4b472e27147008d846e6d431660086846d552e1f686846d53472e2778d847e6d452e27700846d47412e276008a846d471d1c6008c846d5b281d6
  | 6, 0, 3 => 0x8d1d1c160a036008d7c441d1c0360084836d5b352760084831d1c160a6846d6a54472e27700841d1c160a09600846d472e271060000846d542e1f58d846d472e270478d84726d5b27227008c846d1d1c166008d4f472a2703600846d5a472e1d68d84776f6d552e7846d5d47402e277847f6d4c472e277
  | 6, 0, 4 => 0x8d847647342e277008d6d5b3527036
  | 7, 0, 0 => 0x8d6d5b28270a037008d847c44402e277008d844746431e0a7008d846d47271c0778d847c442e27241c88d736d47462e271d88d846d61473b2e278008d47271d1c0a03700008d84742a1d1660086846d472e2716700008d846d55382e68d84766d47362e27800848347271d1c0a7008d71472e28210378d846d472e2a271188d846d472e271f068
  | 7, 0, 1 => 0x84836d1d1c16600008c846d471d1c68d847d7b6d472e2780000846d47422e276008d846d472e27197008d846d472e27127008a846d472e2d277008d846d59472e237008c846d432e27167008d847147211c1678d846d472e271d06800008c846d552e1f6008d846d472e2708700472e271d0a090378d84726d472e271d8008d84402e27160a7
  | 7, 0, 2 => 0x8d8447431e160a70084836d47352e2778d846d4a49472e2788d84806d67472e278008d846d6c1d1c167008d84473a2e270a7008d6d4744431e0378d8481796d472e2780084836d4744431e700008d846d4f2e1f6846d4744403f2e27800008d6d1d1c16036008985846d472e277000047271c0a09036008d847447462a1d7008d74472a2716037
  | 7, 0, 3 => 0x8483552e1f0a60084432e27160a0978d846d473b2f2e2788d846e6d472e27088008d846d3b2e27167000084552e1f0a096000085846d47271c6008d6d6c402e27167008d846d472e271578d846d47362e271a800008d84551f1c0a68d846d4d472e271c80086846d472e271f7008d6d47352e27037008d846d5b281d0a7008d746d552e1f037
  | 7, 0, 4 => 0x8d8427241c160a7008d6d4f472e2703700008483471d1c0a68d846d47362e270a8008d432e27160a037008d7c44432e27037000084471d1c0a096008d847d6d472e2770000846d472e270168d846d51472e271288d846d6052472e278008c846d2e271c167008483432e27160a700008d552e1f0a03600846d5958472e1d7008d846d47271c117
  | 7, 0, 5 => 0x8d6d431e16036008d6d552e1f1c037008d6d471d1c16037000084836d431e1660084836d552e1f1c70084836d471d1c167008d6d271c160a03700842e2724160a097008d84726d472e1d78d846d4f4e472e2788c846d47432e27168008d736d47462e1d78d847c442e271d1c800008d471d1c0a036008d846d5e472e2778d8475726d472e278
  | 7, 0, 6 => 0x8a846d472e270078c846d472e271c1688d846d472e270e0a8008d846d1d1c160a700472e271e0a090378d6d6c47402e2716800008d7147211c03600842e271c160a0978d846d55472e27068008d846d6c431e1678d846d4f472e271388d846d6c552e1f1c80055472e270a090378d6d52472e2c270a8008d7c6d471d1c0378d846d4a472e27158
  | 7, 0, 7 => 0x8d846d552e1f1c0a800847a6d47402e27700008d844f472a276008447402e270a097008d846d472e271478d846d4c48472e2780086846d55472e277846d47403f2e27168008d84706d5b28277008d84271d1c160a7008d6d27211c160378c846d472e28271d80084836d27211c16700008d8474552a1f6008447403f2e270a7008d84736d2e1d167
  | 7, 0, 8 => 0x846d4c4b472e2778d846d472e2718168008d472e281d0a037008483472e281d0a70084472e281d0a0978d84746d472e27118008d84472e270e0a700008d841d1c160a600846d68473f2e277008c846d472e281d700008d846f6d552e68d846f6d472e2b2788d846d5b2827240a8008d52472e2c270a7
  | 8, 0, 0 => 0x84472e271f0a09700000084836d271c1660084836d472e2a27168008d7c6d472e271c0380000008c846d47271c6008d8479736d472e27800008d6d47442e1d03700008d6d6c52472e277008d6d472e271c1603800008d8447271f1c0a7000084836d47442e1d700008d84736d472e1d7008d716d472e2827038008d846d4746271d1c80084836d472e271c168008d84472e2c27160a8
  | 8, 0, 1 => 0x8483472e271f0a700008d84715b472e2170084836d5b472e271d88d846d6c472e271c169008d846d6659472e2788d846d4746432e270a90000008d6d271c16036008d846d47462e2a1d8008d8447462e271e0a8008d6d472e2a271603800008d846d473c2e27700008d84472e1d160a7008d846d5547271c0a800008d6d472e1d0a037008d846d2e2724160a800008d847447462a277
  | 8, 0, 2 => 0x8483472e271d0a78d846d6c472e28271d9000084472e271d0a097008d6d55472e270a0388d846d6c5b472e271d900008d846d5b28270a700008d6d52472e2c27700008d846d6c271c167008d6d472e28271d03800008d472e271f0a037008d84706d472e27168008d84716d47271c168008d84736d55472e278008d6d5b472e271d03800008d8471472e282170084836d472e28271d8
  | 8, 0, 3 => 0x8d846d472e2a1d168008d84472e271e160a80000008447271c0a096008d6d472e271e0a03800008d8474472a271670000846d5958472e277008d6d47442e271e0380084836d47442e271e88d846d472e2827240a9008d8455472e271c0a800008d846d59472e1d700008d846d472e27077008d846d47271d1c16800008d472e271d0a037008d846d2e271c160a800008d846d4c472e277
  | 8, 0, 4 => 0x8d846d47461d1c700008d6d47271c16037000084836d47271c167000000472e270a0903600008d84726d472e27700008d846d47352e27700008d84746d552e1f78d846d47462e271c0a900008d736d47462e2778d84716d472e2c271690000008d47271c0a03600008d846d4744431e7000000848347271c0a600008d846d472e270e78d846d47432e27160a90000008d846d1d1c166
  | 8, 0, 5 => 0x8d846d4f472e27700008d6d5b472e1d037000084836d472e281d7000084472e2c270a097008d84746d2e2724168000084836d5b472e1d7008d846d47402e270a800000085846d472e27600008d84432e27160a7008d846d6c47271c1680000008d84552e1f0a6008d846d4744402e2788d846d47442e27241c98d846d472e2c271d16900008d7c6d47271c03700008c846d55472e277
  | 8, 0, 6 => 0x8d847c6d471d1c78d846d472e28271d0a90000008d846d431e16600008d846d552e1f1c7008d844746432e270a800008d846d471d1c16700008d842e2724160a700008d846d271c160a7008d746d55472e27038008d846d6c472e281d8008d846d6c5b472e1d88d846d472e271c160a900008c846d472e271e7008d84806d52472e2780000008d84471d1c0a600008d6d472e281d037
  | 8, 0, 7 => 0x8d6d552e1f036008d84472e271c160a800000084836d552e1f6008d846d472e281d0a800008d8447402e270a7008d6d472e27160a03800008d846d27211c1678d846d472e27211c1690000008d74472a27036008d6d4744432e270380084836d4744432e2780000008d847147211c600008d846d5b282724700008d55472e270a0370000848355472e270a700008455472e270a097
  | 8, 0, 8 => 0x8d846d472e271d1c16900008c846d472e271678d84746d472e271d169008d84736d472e271f8008d847c6d47402e27800008d846d6c552e1f7008d846d47402e27168
  | 9, 0, 0 => 0x8d846d5b472e271d800008d846d271c1668d846d472e2a27168008d846d472e1d0a78d847c6d472e271c8008d846d47442e1d78d846d472e271c1688d846d472e2c270a88d84716d5b472e2788d84746d472e271f88d84716d47462e2788d846d47442e2c278008d846d47402e2778d846d472e27241c8008d846d2e271d167008d84472e271c0a7
  | 9, 0, 1 => 0x8d6d5b472e270370084836d472e28277008d746d472e270370084836d5b472e2778d846d472e271e0a88d846d47442e271e8008d846d4746271c7008d846d6c2e27167008d6d472e27210370084836d472e2721700008d6d2e27160368d846d55472e270a8000084836d2e2716600008c846d472e2768d846d472e28271d8008d84472e271f0a7
  | 9, 0, 2 => 0x8d8455472e270a7008d84706d472e277008d84472e2c270a78d846d6c472e27168008d846d472e281d7008d846d5b472e1d7008d6d472e27160370084836d472e27167008d847c6d47271c700008d472e270a03600008483472e270a68d846d6c472e28278000084472e270a0968d846d6c5b472e27800008d8447271c0a6008d6d472e2827037
  | 9, 0, 3 => 0x8d6d472e270a0378d846d4746432e27800008d846d552e1f68d846d472e27160a800008d8474472a2768d846d4744432e2788d846d47462e271e8
  | 10, 0, 0 => 0x8d846d6c472e277008d6d472e270360084836d472e2768d846d472e27167008d84472e270a68d846d472e282778d846d5b472e2778d846d47462e2778d84746d472e277008d846d2e271668d846d472e270a78d846d47442e277
  | 11, 0, 0 => 0x8d846d472e276
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 28
  | 3 => 36
  | 4 => 44
  | 5 => 52
  | 6 => 60
  | 7 => 68
  | 8 => 76
  | 9 => 68
  | 10 => 60
  | 11 => 52
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 64 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1f8ffff8e22fffc71ffffe0787fff1c7e3ff81e1e3fc71ffe660087fe5000ffff8000fffc003f1fffffff1f000e3ffffffe3fc0007ffffffc7ff
  | 0, 1 => 0xfff03987e23039381fffffc007fffe0703ffffff03ff81fff9fc007ffbe38e3fff002e3fc7fc01fe3ffc01f1ff007f800000007fffe783f8ffe6
  | 0, 2 => 0xfc0e07fffffe07f8fc7e07c07c7e1fff1f9e7fe31f9b8fffe79c00ffe6fff1c0671e31c0b8fff1ffc07ff1fe38fffff002ffff8e071fffffc71f
  | 0, 3 => 0x6601c0006800001860070019ff8fc187e22fc13f1f8e19c7878e2ffffc07f1fffc0ffe3fe1fc08bfe3fffe001f03fe007f03ffffc083fff
  | 0, 4 => 0x703e781dd03ec01c0000000000000700000000000001c00000774000000038001dc03800000180000001800003800000038000000000070000
  | 0, 5 => 0x1c000000e071e6387871d0380000000000000e0000038780000000060000000600007000000070000000000000000000001e0380001c
  | 0, 6 => 0x1c01e03f7401c00003f80e0003f00000000000000000000780e0000700000198070001a0000061801c006400000000000000
  | 0, 7 => 0x3f0000000000000007ff83f007fe00000000fc000000e00e0038780e00071c0001dd1c000e001983f7801a0380066000000000007198070071a
  | 0, 8 => 0x1c0e07e0fe0e07870000003f800000000060000000600038000000380003f1fff8fdf1ffc0fc7e0000007e003f0000000000000fc00003f7c000
  | 0, 9 => 0xe3f98e1ce3f400000003870000007e00001dde00070001863ff00191c0006180000000003818600738190000000001c000000000000000000
  | 0, 10 => 0x7f8fdc007c003f19e0773f1b1c7e3ff8ffde3fc71f8e0000038e01c700000000000071c00003ff40001c003800fe0038000001fe3f7001f
  | 0, 11 => 0x3fe3e78fdfe3ec0ff80003f7f80003fe0000000e0000ff800000000001f8fc7f8ffefc7c7e3f0000003f001f800000ffe00007e000000000000
  | 0, 12 => 0x1ff1c798fff1c747fc0f9e3ffc0fb1ff00000fe000007fc000038780001ff000001dd00007e00e003ff80e01c7fc7e0ffdfc7871c70003ff4700
  | 0, 13 => 0xe00006671c0006b8000187c070019e00ff807000ff838000001c0000001fffffe0fe0fff87ffffe6387bffd1ffffe781ddffec7ff81f83fff81e
  | 0, 14 => 0xe381c7fffde1c7f81fffe1ff77ffce0703ffffdd03ff8e3ffe7f87bffde3800007e1e000380001e1f80001ce07ffe7f1ddffef81c0001c774000
  | 0, 15 => 0xfc0ffe1f000ff83f0381fffff381ffc00061fffc0067f03fff9ff83ffefc000007fe000038fffe01c003fe0e3f03e7ffdf03ef8e3ff99c003fe0
  | 1, 0 => 0xfff1c6601c01c6bffc70000000700fff038000000383ffc0001fffc000fff000000000003fe3fe01c003fe0ff8e07e7ffee07bf1ffe01fff7fe0
  | 1, 1 => 0xfffffff80000003ffffe01c003fe0ffffc798e1efc77fff80000003800fff1ff98e1e1ff7ffc7f9e07747fb
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x906dba88006dbc109b6ba0401b6f0426dae81006dbc001322200013250006daa80006dbc0012021999b614000210252e5a3480001202c93c5b1
  | 0, 1 => 0x294021018010200811beaa4005bef204020012450240811beaa4005bef00021020000210836c01542d500100db005509100000349a4782401a46
  | 0, 2 => 0x9008000426480418b45a06c06c5a16f6121439031201891ec28c00dec64621004210210010a5602480496044207daaa0027dbd08040008918410
  | 0, 3 => 0x42216603c4216802413860970139db0d8186c22d812d1a8c1946868c2d6b900561329003482d60b808ad63909800140308002403b6ab0083b6f
  | 0, 4 => 0x24f27e793dd27ec93c8d9c064084a24f06e5811804a493c09144f7409024f27e793dd27ec81009804b3409820427a2908927ac024858c0b7085a
  | 0, 5 => 0x42486c07c448712e573e6b97973d4b958790c1048312e44144b9784104201060264e106108172a2902972d0994cf98c184cb424121e0391121c
  | 0, 6 => 0x4203122248a3128b7d29f47f7529c2946ffa9ecd6ffc81128a0522528c0db6dff8fdc6dfc36db7fe3f71b7f0db6dff8fdc6dfc349a5f83601a4e
  | 0, 7 => 0x6ff125509100001bd9fffaff3dfff6f612543fcf1241af4dfcefb7cdfb66f5eedb7df5ef53ecc5dcbf78c5a4fb317709100001189f7ba9f39f7f
  | 0, 8 => 0x9d2e97e4fe4e97a74a01513f92010900806046e48062403a4a91283a4e6ff7fffbfdf7ffdbfdfffef66dfef6ff7b7f0d906939bfc4954ff7c490
  | 0, 9 => 0xb9deffbdefdeffee7609457bf6090b4feb6f57fdeb7a76e13d73ff21399db84f589100002427b7af1bf3b7f909804146fc8042402128312a2129
  | 0, 10 => 0xdfbfdffeffefdff5aff7bf9ffbf7fbdfefffdffdeffef7fbfff76e7befbdfcefd8d184cb6f7e09557ff6090bd6a7f6dfeda7eef7fbfff7ff7bff
  | 0, 11 => 0xffffffffffffffffffedfdffffedeffffb7f4db0e93bfffedfc2440000dfbfdffeffefdff7eff7ffb6ebf6fdfb90556ffe90437ee41542440000
  | 0, 12 => 0xfffdefdffffdef7ffedfdffffedfbfff92557fff9243ffe4955fffe490fff92557fff9243ffedfdffffedfbffffffffffffffffff7bf7ffff7bd
  | 0, 13 => 0xf66b36677efb36bcb65b87dbfe5b9f24ffaaf4abffbfc924801d2ae480fffffffffffffffffffffffffffffffffffffffffffffffedfdffffede
  | 0, 14 => 0xffffffffffffffffffffffffffffffffffffffffffffef7ffeffbffffffbd92517eff9243ed369e1fbbf69cf6fffeff7ffffffdbe4915dffe490
  | 0, 15 => 0xffffffffdbbffbffffffffffffffffff96f5ffff96e7fdbfffbffbffffff692547fef9243ffffffff6effeffffb7f7ffffb7efffffffff6effef
  | 1, 0 => 0xfffffffafde7dfffff7bf6b46972dfffb7f7999927afffe4955fffe490fff925509100003ffffffff6effefffffb7f7ffffb7bffffffffffffff
  | 1, 1 => 0xfffffff89100003ffffffff6effeffffffffeffefdfffffedfd36c3a4efffffffbfdf7fffffffffeff7dfff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 58 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 58 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 142 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 142 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 142 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 142 then wireAt i else 0
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
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 5 zs)
def CN : Nat → Nat
  | 4 => 7
  | 5 => 124
  | 6 => 867
  | 7 => 3040
  | 8 => 2879
  | 9 => 352
  | 10 => 13
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x9075d4ed40a96fbe382c63012fd068682211b6a707a8c8ab002d42d5
  | 5, 0 => 0x380d0f4a378b3138371705303712605635b1529e35245bee3471093232ab7a4c325f6ad431ff2ed531c452f8308dd8632d4a5abc2bd153962bcf2a6e2a8fe856284dbc5928373ca327c661bb23d8d43b23c35db12308efc62239f7c321f3b2ab209679902080063b1f96c32b1f3c441f1d7cf91e1d5adde71b263c431a27515a198e768c1850225e172716e716fe224f16c1a88e145fb340130ec79e12cc488612683c4e123747841233a40f11e42780107be3a90eda08c50da1540f0d97b5dd0d4dd6010d18bf4c0c7169730c2ecaed0bf1487a0b409da30b0fc6210abd5d4f0686ed2305ecbda305a8134e044f44c203bff91b0349a8a50171ec6600c21606
  | 5, 1 => 0xc31492dec25e1129c20a5784ba508cdab2077d9dab14929ea9e0bab1a911b707a5af18229b6745369665ef1a934d095590a821df8e5ca8f18aa080d889164c03839e34c881f820d17f13e5e17d04b84a7c26da707930ad6378a6a7b475f80f7075179d717302284172e3a26c711139fd6c50f44a6c306f4667f878ba67a3adc460259c9c5b4e4f51564f59f255c8cb7853ff054b53e2835a51fd15ae51ea38784e74a0624cbef7384bdae77e4b86a20d48c47c5044c5a2ee431f03e04307b89c42bd7d844201a14f3d5d0c3e3d588b623c61dd583c3661fc3b5dfe3b3b3760283952a29338d3a9cf38b1378438726548
  | 6, 0 => 0x5aa5a86058cb6ee056611b805129ffb0506913d0504500c04ec71d704e60d4404c0165f04a21383044fe52d04262632041e7f620401abb103ee340f03edf0f903e4a4da03d273b403bfe23203aa6b3403959fa003937e2503790289036239850359fd500344a92703109cb602d474eb029fb6b102991c5d02959bad02958a01027c1aaa0268328502466a29023b6dee0239eb9b0237a38a022ae2f40228d7d102107ffd0209e4a90206221302042b4e01f4b86c01f3626b01f1975501db05fc01da082a01d0666c0183218601781f4d0157d1370128b09101212a670106fcd900cdd936009a06d400946069008cdfb0007fc56a007635dc005aaf260041eee4
  | 6, 1 => 0xbbdb2890bb9af460bb60a8f0ba615e90b7b7e5f0b7a942e0b6c08c80b320cd40b2617390afb165d0ae3fde70a5791940a4f76c20a3f1eea0a30cefb0a27b6100a19edd30a10929909da04d909d0d50d09c58572096f22e80960d2f90934cd4708ff668108efdd6008e3c2e008bf7f5208a7a0a8089ce3e9086707fb082b08610819c946081946cf0819217507ff917407f217d107e7c12807bd5e990796c0130781c741077881ec076cec0e076ba5fc076b4f9f0765fae207544d8407365274071f0f16071a11ea070dc39b06d9de5f06d37fcf069dcb5b068cdd5b06789ffd06631f2d06518c4e0640bd7f062e91bf0619dfa805f0f79005c89a8205b3209a
  | 6, 2 => 0x11bbcdbd11ad4ab1119a2568115e59161151c2d211444b97114240c9113cdd0f111db36a10e0731810c57ed010bcb73a10a6c00310a6660810a07c8c1078aab1104e5bc9103995ce101e2dee0ff58a1a0f9f7b390f8614810f44ce170f4203910f1e5b300f1213540f06b5790f02a4070efddabd0efb797f0ef18c230eb4ca5d0ead630d0e958d830e8db8ed0e6dc71d0e5218be0e4f0e290e43c8cf0e3fc45c0e192be20e12afb30e028b370dc280750dc01f140d806ec40d7f960a0d72d7820d5002d60d3088b90cf6a3cf0cd3a40b0c43f3e40c43853e0c3671ce0c25f0c70c1334280c0cae520c063a360bf903600bf713100bc4d76d0bc45a7e0bc2d3d1
  | 6, 3 => 0x19871ed0197ace77196bf71d18e3790418c9fa3718c7107d18b9e321189d700f189614c8187f69091864260d184d21561839ba5118360f7a18321aef17ec50ed17e2d36017ad063d17a9dacf17a3a0f8178589d2171f93d916dd3d2916777664165eb02b16578922162dfc05160510a115d1622415c0287b15b3b52c15a0f3201599adee1546727b1535fcb615313a3d152f380d1521f43315095b4514df50c614d7638014cf387b147c82a6142a545013f1760113d9a70813cad34d13bc6975139ea0c3135a1d09134e3a331349c0371333573e13101b4912d6120812bbc2101246d131121db7b412071938120063d511fa0a6c11e8f96811df7c0911ce29ad
  | 6, 4 => 0x21d119fb21c71d6721c3688b219ace62218557f021616d7121573f642124291c2110f36220d0be7520bc25e220bae23b20a1523a20a0121d207f962d2072545320596743202f91ad201f769920176d84201172f11ff30c541fec912f1faaa30a1f9d1eaa1f39dc271f36efc61edcb6821ed2f2761ec3ba101e994ede1e8c96851e8a15ae1e87bf701e755c121e6023731e4ed4e91e1765ff1e151c291dfe6af31da9742d1da68feb1d90ab401d77117e1d559f991d5109251d45ca5e1cb19bee1ca3ecd51c7f12c11c6d910b1c529a511c3e9fe41c2fc60c1c1e4a181b8cfa261b873abc1b0da94c1ae3ef4e1a83e21e1a33175b19eebdb619bb8aaa19b76e1a
  | 6, 5 => 0x299f24af2916e4382900e8ea28e5dbd928d8000f28c9050828b7ff4328b4e39b288c70ef284b4ea8282e06e52814e741280badc727e1f4ab27d9e15927bd1ab82783ee2f27739e78274465a7271a7ad626c9eb74268d5b40268b65c82677aa8726678ea22616f9852613121a25eaff9625ea212925dff70125de6a0a25d4eebc25bd756f25b2fe79258735bc2550424e2549fd66252c034d2512c0bf25103ebc24fe74d424db066c248826ee246451bc245e77502432d98624264313241c5b1f240e839b240241da23cee88823c35db12395b66a232a09e62313596222f3bf2c22f115ac22e5c71e22b31b472298c79a2265e3b7225e7fb02258a9ef2253f56a
  | 6, 6 => 0x3365f12d32e35ee932c9f9d432a813e23278f1b03263c74532537282321466e631fe321f31be0c6731a7a6103173356d316ec9f8316adbe931282c88310ed37430f7a96c30d55f4330b179ed309c7d2430833b33306c8a42306393823029ba6c301b38262fddbdfc2f87cde42f76c22c2f6912092f605e512f436c1b2f3843572efd92792efa55f32ee303912ed592d72ed527ce2e7c5efd2e79e1412df428f22da2ed6e2d8883ec2d60c4842d1dd1dd2d09bbe32cbd20942c7c2be42c55cc932c53dd762c2114a52c1480502baadbe22b94167e2b2b52032b0576ad2a9a30852a5efe232a4329782a2a10d42a09c4a529b3405429a8d8fd29a3325129a035e8
  | 6, 7 => 0x3e39334a3e2292ad3e17729e3de7cef33dd1d4683dab7c8f3da3d0e33da210e83ce16c713cc6e7d23cb84d793c581ab33c47ff503c43f8f63c1d7e7e3bcf65983b9fbbe83b7d55f13b2e1efd3b24af0c3aa101e53a3f7a783a3832133a07019739e501e639857ef539834820398113133973324a394280e239288a6539156f6e3909a22c38b7c7033850752a384cfde438414a8c384130c137e7c24d37bb414936c611e7368bb46b365fc900364d5fe536321c113614fe2f3611341e35ebf0cf35e84b5835e60e5235a4df18356e44463544cd423538b8c8350bc0fa34d078ba34cf1ea63492c54533f9a3c333e5aa0c33c7584933c54cbf33bdfc783374411c
  | 6, 8 => 0x485c711548443a61482bfeef48166b0f47e2ae5e47db1c1147c728c1475baf344748220a4714bf79464860064638735745ffb57945d3dfcf45ac999f45a310a14598d40b456a7ceb4564de354545c0ae453d866644dc268c44d950f544c55e15448f7737447d6ed9446f2a0043af55e2438bca224389cd45434f9464433186ee42f158a742b13510429af4fc429698cb4285e96f42520b55423e36684224a6674223cfff41ce377041ca0b8a41b5293a41a4c1f14183078641774dbd4145804641408af14124bc09411c446f410f4a3b4104ead240fa395940967e60408e8add40693d2240549879401729bb3fd860d83f9b11da3f4bd3243eba80483e7424f8
  | 6, 9 => 0x58a6f4d156ff858756afd252564dc50755f50b6455aeaca45584c56b556971aa552d9c5b54f37edf54db6eb654a270d854a01211545472ed53aa02a453719ce852b546ba5248c74051ea387851dc107251a60aea5148a5595111f2b8508b985b4ffcd3d64feeecbb4fcf02bd4fa96b3c4f96a1554f3eeb2a4f2b00f84e6d3b3b4e4695bb4e247a844e01c6e24ddb2bdc4dad12634d473f954d156bfd4c8993384c43ae8f4bf8cd804ba970f04b3a94bf4b3169424b20acde4af8e4794ade2bb84a796a024a5a63c54a5813294a4833f64a09d33149dbd29749bc3b3349b4ab4849886128494cfab0493b9751492a9cb048c99e8f48c6b929487f1d21486f4b19
  | 6, 10 => 0x6bdf70dc6b0238266abe33946ab7e6926a8ddb9d69f10c0c69e0add869d765f6696f5a6c68ec9f0468e6994b68e265de68df364c6883cc6c68801c4e67a474326778eda5671b65c9670b402e670007aa66ba32fd667e11696600a95565e52f2564f054f264e36751649b93b063f511d16327b91e6296740d624b917b623aade0620a209a61b26a376138c97d611b3c2560f377f160e756b060640d766003eef8600335025fbae4775f9351ce5ef0d6ce5e9d0f395e0ecec85dd6cb515dd47f545d2d25c75cefdb205c6435075c5912665c5239825bfc8dbb5b1d13985b0f6cc65aef45615adac6ac5ad797475ad692ce5a8f70855a27905959393ad958e4e327
  | 6, 11 => 0x89b44f9089164c0388391e3b87b4acd585f6f73b85a2759d8548c22484ac1ff78309667e82e9421f82af78d78228ccec81fc679481fc18ec81a98318819211fe805c2628803981c0802de8797f824bdd7f5ed56d7e8239ce7e69ad167e1220297cd2e2387cc1c5307caa5baf7c5566047c5440c57c475a617b856a027af7ba6b7a90c27579db05eb7912e84278ed61d87832f048779e867c76e9219d76e2b43a75f0da15755363bb754d82da74d72c1a74ca657b746c738a7459d89373e2631a73a2dc2c7320d9e372a0dc2a71c3be34714c651f70ce7d60705980046f0feb0e6f0b13f36ea207256e415fc66db9afcc6d7cb67e6d26a2b16c2b0f5c6beceda5
  | 6, 12 => 0xb1322830b0bddd35b05c3a8aafde02c6ae90f528ae8dbd34ad930e40ad0562afac322988abd40286ab36d69daaf53ee7a873061da75cfecfa52fdd78a4348a8da397fe76a314f4f1a2b05815a25879a9a22d0e7aa131bb8fa0f83f62a0b0d54fa09bff8da07f9158a01225f39fe615479f9dc1659f18ad099ed8667b9e7a28649cbeaa309c21ccb59bfefdf09b426c579af348ce99142ab29821f4b3981c45e0960eecf79444cf3f93c627a093ae92a6935648ff921d4bbe91e7a61f9145b59b908b88cc8fdcd78a8fb3f2008f275dcb8f0ba5238ee78eec8ecc8ceb8e3075f08e1c08138cdbdc2c8cc2f2f38c770db88c4c752a8a5984678a35d4418a1c14bb
  | 6, 13 => 0xf9157840f59b6543ee5cc6c8d4c2bab6d3683cb9d1dc7b37d043b53ccf6f68b9cc8aa089c8e06df2c8af2762c6deea98c6d345c4c37f2375c31492dec062a745bf203ec0beb6a459be73be48bd3910a5bd135840bc5209e3bbc71a8cbb34eb56ba924b74ba4f9b13b9c302e1b8e46a21b81051f6b72489c3b5d220aab44460d6b3af8ed9b268b929b1ee1ae9
  | 7, 0 => 0x181cde90178b0340176348a017281340170768e016cdd33016cb1a8016b707c016739d301657c6301563beb01526bfb01449074013c332c01386f86013087b8012f1c440128fb4b011c638b0116982601146a38010ee67a010d51d9010a883f01090c5801079533010336d70100315b00fac25400f6537500f4e21000ecc73200eb0f6500ddc7fa00d101bc00cda97700ca653a00c7ac2100b9f7eb00b647c700ab244e00ab1eba00aa5a2f007927c50076ee1b0075bb2400700cd0006efad50068e00f005ab39d005a48790052dece0051563e00448b93003e69050033fd8200312ef0002b40d0002a3d41001db6a2001bbdc3000885c7000633c5000164f0
  | 7, 1 => 0x33f83dd0335ff520334c74e0330cb5d031955ab0318b681030dd6a90307514d0303bb3e02ef588402ed3c6302e6005d02ccc32802c78fd402be952302b72d2502b1898602a8c1f302a8789c02a423740292d045027fb9d8027d3237027ca6ae02751e4e0274be7502721ec4026288eb026084cb025b429a025a997f0259ee750253245502362815021fa5e6021dedcf0213d84d020eefc20201a8b001ffc78601fe4b5e01f5c65501f4f69401ef211001ee758c01ed6e2a01e4d95c01e2c99f01deddac01dd3b9001db05fc01d9f65601d42feb01b8004a01b5b49201b4bc8801af5a2b01aa528101a790c9019eff8c018d860a0187b6830184daef018338be
  | 7, 2 => 0x4cbeb7f04c0165f04bf572104bf239404be42a104b563ad04aa5fc704a2138304a1ce8a049ebba904953edf0492c53104905508048d2fa8048c019104862125047e717b047c77f20478c320047629fd04694c3d0467da0e0462fea0045f675c0456a829044d7279044cd80d0446bb65043e26e9043b3e84043356b60432e4e20424ecce0422f56104194114040d573d040bdb5603ff2a6103fe19d003fa96e103f638bc03f58e7b03f0315d03efc11603dfcde203d9723303cbe2b503c8a75103c116d003bcc6e903b6b16703a93d89039c53350396ca0303923d250390338803884f2b037a250803678e50036478c10354ae60034a885b034532d80343ff4d
  | 7, 3 => 0x66ef1830669a86e0665b0f00657f0b106539939064d643c06493e9106471a4f0641f0ae063ea7500631e9ad062e29f60624e25f06202a5c061defd6061b857f061a5aba0611c88e0610604305f6b49c05ebb72205dde1ed05d8a67605c8e6e205b8b4dd05b8b17e05b4d3ec05b2775305aa108205a65dbc0595e2310590ddc5058c575305886e57057b709e056b7331056a083d055f3e69055d43b4055d284a055912c705529518053f5732053ed57405344eb0052e720c05262850051f6045051f5340051b96e9051a19e404fb348104f98baf04f8955304f8757e04f36a9104f1dbbf04f1c75c04eef8be04e9084604dee57d04ddb7d304d5c7d004cc8e34
  | 7, 4 => 0x81fd1480819217508080e37080710cf07efbd3d07e543b507e32a1607dc2ba407d9364707d4251b07d2750107cb7fd607c72db507c3205307b3196007b08dea07a61a4a079fa3b8079ce1c6079049800787e9e30787c7ad07840601077fa696077990290777638f077655f1076ee8be076d503b076c1f2e075ccb980755563e074dfedc0749fc7e07432e98074302520737cead0726ca0507256fba071ff00f071cf59b071c2933070d739706fc3e3206f5b62306f493f706efbbc606eeef0406e1e89106deac0106da611606d3700706c6303106ba596d06b99b3d06b72f5806b3ac7106acb81006ab8d7c0699715b0695a3db0692ddc7068e880006747ee1
  | 7, 5 => 0x9883d15098199c9097db53e097acc210977c29d097417b00973c89509706997096d6964096c900b096adac00967883a096677e70961b3560953142d0950822f094db7a30946f0a10945e9ca09412176093c8e890935a83009340dca092e72b3091778120916340709026fb308f8b9b408f4644508e0b0eb08dd847c08db872208d083d408c8b0a608c57b0708c5262f08b80a5008a9e41308a1e4ff0898d4700891a610088aecb60880e3f30879c2280878bba2086b441908674aa10863a2310861bcc1085efa1008595b5708591c460851e409084a644908440bda084365560839a5b30836e9c00834403b08343581082f285c082954a808262d58082130f1
  | 7, 6 => 0xb5356550b4cfd040b47de120b44862d0b431de20b3d98c70b361f4d0b1d09ae0b1b638e0b143d470b0fa34d0afe75410af3e8430aeb3da60ae9bcb20adb98540ad8e9bf0ac44cd30abfe7920abf12f90ab7641d0ab51b150ab30be80aa645980aa5b1ea0a9fb0c40a9fa12f0a944d620a8f107e0a8bd31a0a890a7e0a8396b30a6ebc0e0a57ae160a5767e80a5426610a3be6ce0a3ac57a0a333cdf0a2fc7290a2005680a0d29780a04dfb30a03258109fe650a09f9cc6e09f1be0209f091bc09dc0a3009da5aa609d18c9009bece3f09b9891509b4e0fe09aec34b09adaa4f09acddc409a9b8fa09a176d6099ca3f80998662e098fab02098f7e03098dd1a8
  | 7, 7 => 0xc924d010c923a040c88bb850c874aea0c8304550c76e62b0c75181c0c69c7ab0c619bb00c5d42b50c5d02790c5b66b90c5a8fb20c5535bb0c4e0c1d0c4c88890c4c0fe20c4a8c630c489b0d0c47bde40c429f720c4031360c3b22810c32979d0c2ac0c80c255bfe0c1f76990c1e42f20c1889950c17bc4d0c1620d80c14536a0c0f39cd0c0ad7930c01f4e10bfb93630bfb482e0bfab7490bf733430bf3526a0bf0c68e0be2aeac0bde56200bde2b5a0bd974b20bced9050bcabd720bca1e310bc4adfd0bc1459f0bbaecf50bb0b7140ba41a9a0ba2ce2c0b9c41950b8a7b3d0b8a45b60b82b1940b7ee99e0b7d309f0b7ca7810b62e8320b62855e0b5b85b2
  | 7, 8 => 0xe36df1e0e36c3090e33b6d20e240bb40e212afd0e1e328c0e19fab70e173f860e1124ab0e0c0ded0dff46450ddca1b20dd87e6a0dbbb4bd0db51bc00db095f20da6f4600d98ab770d8c50c40d82fa950d82f3980d7fc6f00d7c932f0d7c8b6e0d6ee10b0d6345e30d5f1fa80d5e7bf70d5ad3110d58216b0d56f55f0d553e2b0d4d8b020d4a0ed60d495cd10d40e2170d3dd8a90d3c619d0d3558260d3520020d2fcef60d1d80930d15ad0d0d0f11280d0704110d04ac890cfd2ca80cfac3cf0cf955700cf6cdd00cf255a70cef98860cea3e8d0cdd29a40ccf84340cc97db20cbc90b70cb69dc20caef0280cad402a0c9b8fe20c9a75dc0c9716440c9699db
  | 7, 9 => 0xfc2af870fbf190e0fb96cc00fb45ed40fa67fe60f9fb5560f990a130f98a9650f93d29a0f914fbe0f86ded80f7b183e0f765a590f6c96a90f694f900f63c6430f54552b0f507ab40f5020360f4b6a0b0f4300340f3ded470f399d1f0f375bfc0f33f00b0f30aacb0f2936090f1f666f0f1b58930f142fe50f0da4640f04006e0f02bd7f0ee41f350ee35c280edbea020ed7c3c80ed502960ecc58910ecae8be0ec9377a0ebe642b0ebbec300eaabe3b0ea72e910ea40b810ea37e290e9d6bcb0e9cd5530e9a27460e98f2db0e8cfee00e87e44c0e87b7850e84942d0e7ee82e0e77bb060e56bdd30e551a710e536e0d0e52cbe00e4051c20e3fc45c0e38ee4b
  | 7, 10 => 0x11a54888119ef0a2119e12ce1197a6d2117519fc1162b37f1157f5151153c70711523438114b72b0114ac43011484e801123bfbf111e23b81113ea731111e2e71108fea91106caf31102f0cd10ed70fa10e9559d10dbc34310dab3d810d5702c10d2a7fd10cefa6b10c8d58610c425bc10bfa2a610b81f3910afee3e10ad6e8a10a791a810a51dfa1098f5bd108b94d3107aa7de10716f63106586a7105af71c104dfdaa1049d0f1104332471041f70b103c8bee10394b921035b1eb103140d210247fc110201418101fed9f101a78131013d5a31004ac641002e80d10026b160ff564850fed0d8b0fe0da4b0fdb43200fd8b2750fcc4cb00fcb97460fc75bb0
  | 7, 11 => 0x134870cc1347d8f61341e87e133ca8a81330d94313294c4b13292d8a1324cbb71323061313124eb513018eef1300a10612fef0aa12feb38b12f79c2712e0a23012d9e79012d9b1ff12cddea612c57e8512c3144c12bc939112b7797212af490d12abaee4129d3b6a129a869b1288ef821288701b1285a68c12858f7112712b50126b272c1269f43512697719126961b51267a165126282a61258df8d1249119512480bf8124383fa123f56a31237bd39123291191231bc35122d2112122cb874122913c11223cad3121f8394121e96ff121212ad1211d6e5120b920211ffc52211fc831811dd3a3511cd337b11ca437511c4f26a11be872611b6a57711ac2fd3
  | 7, 12 => 0x14f31bbc14f2137614ef385914ecfa6714da6cd714d0027914cebf3c14c91a8014c560e914c457f614c1562414bdc1fd14b941ee14a8178614a3729a149bb18e1498b1c4148d7db814810050147c82a61477816a1463c54f14639338145ff72c1457b7ef1455186b14550336144c3e131449b4aa144613711440620314400bb6143c479114350f0614336f95143083c2142b0d5914239cac14205196141cf31b1408be7e140580ef13ff534813fe205113f9ff8113f9f95613f6630913ddce9013d5af3713d34f0a13c797b813b2bd3c13b03d8813affbb213a7ecf8138e4fe0138a4c5913852261136e27d9136715f0136444e7135d35d013595257135937e1
  | 7, 13 => 0x16729858166f56b6166e0b18166b8e2c165b81571659511f1656ce43164cb8a516484134164108a8163ccd0e163c8a62163bc56216325fd4162d2d4d16167da31608f24b15f59bae15e63c8215e08c5115ddbe4a15dc80fd15d9901415d8995815cd0a7c15cb66b315c8f4c815bee48915b8511015a5a92815a50f5815a0d7d4159e07cc159bf8c7158d8fbd15880c7d1584811a15816ab515742e931573fa4e157112e11570977f156c1988156a5dd5156051d4155e56a3155149cd15451b041542cb89153ea820153a311d15391c801527538815207ec1151fbfbb151904e21516b1f31514efa6151006cf15020fba1501cc7014f86e6c14f7187a14f692b2
  | 7, 14 => 0x182a2286182917361822e5261819c6e218109bd4180f68dd17e3e02a17e2d8b517e280a517de4a8817d24ca217d1211c17ca128b17bd69dd17ba9fd817b69ac717b4e9f617aaace617a802a517a31013179950b81797cdbc178ff4cd178873bc177e64b51775098b176c4588175c3664174db10a174331011742dab4174056b4173e7344173b676217364eb81733489b172f31b9172ddc57171d9c471716fa421716d32e1714c4ae170f8f30170d72f0170af39c16fbe8de16f913d416eb775716e832be16e7c56516de776516dd3d2916dcc0d616d9465916ce98c016cb1b9616ca2ae916c06c7016a5c0c4169e30fa16963bd6168c82601678b1801675ea15
  | 7, 15 => 0x19e7dfb919d2f76719c7ca9519bef87619bba5ad19b73b4819ab443019aafe5a1999829719948d56198830c1197f50d619738f11196f73e7196e6a9e1962b1251961b45a195cd60a195721801954640b194e86d3194669b3194164381934f6d219294b12191754dc1910fc0b190b676e1909b1da190961f6190897d718fb583b18f6f86418f65f5718f5ce0018e7c2b518e0cae718dad5db18d9d5a418d5e14e18c418d118be87b118b58fa518b50b2118af959718a6f20018a04bb1189a4abd189614c8188e8fc9188dd8cf187db60e186d593e186a9ea61863e27f186051c3185a83a01856a0c018501b3f1843c2d01836d6e81836050c1835671f18339bcb
  | 7, 16 => 0x1bb552c31bb1a5b01b9feb5c1b9ac0a21b9857701b9325fa1b88d95a1b8764a01b85133b1b848c3b1b80c94c1b75120e1b6d2da81b68bece1b5988331b5824d31b4ff2fd1b413e6a1b32cfd21b2df5da1b2886051b25f4541b1ef5501b1d36741b1bc53c1b1764811b15da7f1b0b56f71b06cff71b0698461afc4b911af017dc1ae627e11ad3f01a1ac5302b1ac4cdd51abff9af1ab66b6e1ab289981aa136271aa0dfce1a97bf391a8f1e251a8cb13a1a7eb9171a7c33f41a79c4e11a75e30b1a68ba551a5b9e671a4466411a40bc341a3e66a01a37e2971a2992a81a2734811a1728441a1468681a10fa2d1a10da5519fcfad219f7159519f4bfaf19f4b5d4
  | 7, 17 => 0x1e31a5f81e260da31e1f80251e0e25f51e01fce51deb0f7b1de5f5b81db9eb821db710d51db531771d9dd1481d9a45891d927d571d88e5331d6b89531d5109251d47c9081d449b921d4380051d358b861d24ffc31d2419ca1d0e8e9d1d0a3ef01d040a981cfdee971cfc36241cf9e4931ceb33df1ce342011ce2a98c1cdf3eea1cc25ebf1c982c8a1c965bd51c8e43961c83d7d31c7d2ba11c750de61c7130e31c6facb41c6d910b1c69d2f61c5d99891c5139371c4396a21c3f2af81c3807ea1c2d86db1c2c1a101c28c6df1c2810211c27492c1c2399091c1a4a971c0f5d9b1c0ebc2a1c07a03a1c0518301bff604b1bf734771bde83671bd57ae21bc3a234
  | 7, 18 => 0x2001b0f21ff944741ff707111ff6b7f21ff1bc291ff0b12b1fe181411fddaa641fdcbbbf1fdacced1fdaad9c1fd2e6391fcee2221fcbddc71fc93be01fc903471fc5d3a91fc0de151fb1e1a71fae15ae1fa7b2a71fa26d841f9cf5c41f9803bc1f8e35151f86acb51f858f9c1f73ffe11f56e3f71f563e2d1f4cbec81f49ab3c1f4665a01f3bd3c61f322be71f29f90e1f2961041f2663651f24f71c1f154c131f0d9fe31f0d33531f0cff161eec82771ee02d071ed8a1d11ed36f4a1ed321261eb7cf231e9935df1e93c0391e936de21e8d354c1e8a23361e770aca1e6023731e5ef94d1e5127bb1e4693721e4526c41e4183d81e3e250d1e3c1f951e382f76
  | 7, 19 => 0x225830252257bd62224236bb223b190b223041ea222def53222cbddc2223f79c2211f5d121e2fc0521e29bf821dfbae121d974e721d7f89521d58d6021d4d62721d3871f21c949e821c3688b21b7290121a815c8219d3151218b2297218ade7a218ac96d2178a9af217852b8216519de216217452145fe9f2140f40b213bb39321398268212d3f9b212b8c3c212608162124662320fc642520dffcdf20d4c0e520c4b58c20bae23b20b3472f20ac46d220a9e66620a105f12095cb35208a55122089245f207e6485206bd434205eff0b205e9938205319d4204a2220204a128a2042906b202ce9d9202a67d32029c4592026285b20237b64200e8af3200dde7f
  | 7, 20 => 0x249f09222483d854247f7c67247e4e94247c3504246e6b59246dd5632465f0b72448cd9d2442d4a8243fbdfc243e025b2439d2a424369e822424725a2410b304240f7f0c240e085624061743240098d923fd4b6e23fc461723db4a4623d5f2e023b2cf5c23af7b5c23adc14223a4a6a823a49f5a239fe2f3239f466f2399d1f923948a2c239027d6238203222380fec82378c12a236422852362500d235035b7234cf11e23135962230eff0a230d339222f3bf2c22ef8ab122ee215922ed700a22e4a06a22dd4b6122d82dc822cd032822c99e5722c4485722af256a229d3bdb2299029d22919f0522911463228cad772289b830227a86a7226a14f5225cc0b4
  | 7, 21 => 0x26bc859626b8f1b426a59f7a26a279e7269ca0f7269c72312692f6d4268bfb24267435cc2667bff0264c955e26436296263ae08d262ead032616f9852615b7d62610029025e1fbd225dc52b125d091ba25cfd22625cef80c25bf1abf25bb63c125bb50b425b6236425b2fe7925a00ad9259e2056257d55a5257b27ee25773064256be1962563f3e725624f4c25617080255a8c60255888b025539d48254688ab25411e912540c4ea253c29c8253b5a1d25317a04252f8cda252c034d25236eca2516262a2506f5112503aaab25034a6e24ff325624f9cc4924f8247724e3062624d4a2db24cbf47b24c6701524c2a0f724bd5f5424aefa2724a9a79e24a845f8
  | 7, 22 => 0x28a14bbf2890bc89288e81fb28744b3a2871cfda2863438c283453622830af4028303c79281ed4dd2814e741281164b028099ca22805a76427ffa70427fc12d727fc0f6c27f99cdc27f7007627f0a43527ee2da227e7ab6327e771dc27dd0d4d27d9d06e27d8c03527d4454d27d1ec0827c7052127c6086f27c2ae3427b3f43427b0dc5b27ab903f27a06ca32792e089278b6cae278222ee2781afcf278144ce277d5d0e277b86ec2777928527739e782770c9fa2769265927641000275e185a275a961c271aad0a2711c371270dc221270d1a7a2708de5d26fedefa26fbcd0e26f8e83526f8880926f8641c26f6d9e026e09be426d31dce26cf967f26caf483
  | 7, 23 => 0x2b8029b02b7b0ce62b725e432b71bd762b59ba772b526bcc2b5116522b4bad1a2b3dd7b22b092c042b0876622b0864962b05a8092af2db5d2ae8186f2acd83942ac785c72ac061742abaa5982ab6c3322ab3ab592ab12a1e2a8fda612a87d4d32a7952482a59fe0e2a5913982a4f3d2e2a38ab672a20aa0229ff600329facaa729f7857e29f06d6929d978cf29bb870629a5dda629a035e8299bea08299614d0298eca22297dd818297d2c5529731009296f470229690a9429466640294370a3293f469229361e992901bcc928d9cc4628d1c70a28d0332028c916df28c7bf5e28c5d28028c557ca28c32ac428b6630b28b2b75128b1c18528a821bb28a174f5
  | 7, 24 => 0x2e5224ac2e4e2bff2e42eefd2e374f9e2e34041f2e328e292e2b3e642e273ea82e1403d22e0ac1df2e08576e2df1c4012de893872de760902de701c82dc78abb2dc30e432dbf40422dbf0f9a2dbe12562dab61a92da017a02d9eed072d995f5a2d96613f2d940b932d909d182d7af9032d6c52262d4565b92d4484912d3fd0082d39e34a2d124ea02d0d5a562cff64e32cf4a5bf2cec54952ce4766f2ce38b612ce11caa2cd709172c9908342c94ef232c941f962c7651932c4632b42c368df82c21f1702c117c4c2c05333e2bed07722beb44db2bdb36382bce71872bbed8762bbba2572bb7415f2bb594162bb243972bafa9e12bace0ba2b9de1582b89c7df
  | 7, 25 => 0x30f6f4ad30f5a48e30f2d7b830f0c30a30ea694030e0d81430c4a3bf30b8c8c430b1e6aa30b1930830ae30a73092c18a307f7c15306cacd130512333304eb358303ab396303781fd3032fdd73023f071301f60923008e7f7300429793001272c2ffc9b392fda2ec92fd994602fd696742fc9af522fc8e0e52fc263f52fb57b312fac4bce2f85b6e32f639e902f5a4d5b2f5367a12f5300862f4ef89d2f257cb02f0aa3912efcd6082eeb0e4f2edbac842edab2082ed8b4322ed438182ecca9572eb917522eb592612eb310f42eb1faf92eae62292eaa12e12ea7f11c2ea2dd2c2e94e5222e881ac12e76b4312e7177492e66877c2e64cb282e6484d12e5615c4
  | 7, 26 => 0x3340ac5e331833a2330bb6f532fcbd3732de92cc32d435f032cc7e5032c8f9f632c6b59b32bc5d1132bb33f232b7ba84329b8dba32979cfe329507fd328dc30032859886326e7233326776613261ab013256369f3254f5ca32524e7f3251b4ea324d96b632490d64323dcbcc323d2904323222823228e6313221dc90321cf36a3216925332166b403204aab83203880632031cef31e7351f31e6007731e12d3831dfbe8331d0997631c43af031bf3a9a31b1cf7531a96b6631a394a03177491231606940315fc713315e50df315b8c3231482d5f313fd279313bdc94313a1e9c311ed58b311bb1c6311a4ce5310f399431086c56310805a23100686330fc3254
  | 7, 27 => 0x364da0b63641bdf63618315536162a6c35ff4eb535ff08ec35fe136335f06eaa35e450a735d9a64335d7edfd35d770af35afae363596337935946cab359322bc35808ede35788f793574bc803571e0863548a8613544cd423533a93f352c07a9352ab1713527e924352757243524ab8e35234b27351ba6d7350c51ff350739ba34fddded34f072d234e81bff34e6c2a634e2d47334d22a1d34cd6c6f34c904a934c801ec34c3194634bba9d93493eef9348abb90345f3c3d345b1237345a05c13441696f343bb025343325bd340993173407e1c03402c66733f7e7f233a9f4f433a7060933a1c8b73395e7723389edcb3388bad4335ebd8b334524d233423eb4
  | 7, 28 => 0x392293033919fa2038fef94038f79f3438f1646638ef447838ed878438e2e36c38d244bb38c7fb3d38b49ec138ae6bf738aa75793886fb363881badc386dbf8e386b13623860c788385e5a7b385c648738421e89382efe5038210ab7381cdd123811506b37fac1db37ee894637e9339c37e627e037de47c837dc389537d3b73e37c8412537c6470937be78d737bc63ce37b937b937b3c5e137a5a83c379a340037994ae73795a47f378c417d3767e741375c61b737494ff23740e28f374035e8373f43bd373be92a372be3fc371b28eb37127c223710423037064e1636ebc33736e604a736d6523f36a52ca6367e195e3666df7c3666ddbb365b60ec36556bff
  | 7, 29 => 0x3bb13af53bad9a843ba5ee023b9053ef3b7c235f3b65380b3b5d7c543b58a1c53b3df6fc3b3938d53b31474b3b1aa95f3b12d6583b12b5c13b0b62553b0a2e4e3b037bec3afb2b893afadfa03ae155fd3ae117a03ad300ae3ad2347e3ad22fd43ac74bad3ac4d86c3ac3eac33abf6bbe3ab1761f3a9fb7d83a9f45a73a9d02fe3a857f183a650cf23a521afe3a51e9943a4d51e73a4c1ef03a498e5c3a3f7a783a3004c53a1fa06d3a1d1fba3a154b203a07019739f6c19039ed33ad39e3721a39d9213d39d7339339d0f47939c48b5639c0c43339a8e525399360bc39934baf399165aa39900f10398b19003988bc24396e6dc43965e9d939622ed13925bbfa
  | 7, 30 => 0x3ea613a83ea5d4243e99d5eb3e9784353e892e963e869af03e7d236f3e697b633e656a353e4a0b613e432e9f3e3b6d573e2422053e1a94783e179ccd3e0cfd4c3dfb8cdc3de3e69e3dbfa3163dbe46d93daee7df3d9d57263d75829e3d74cdbe3d61e55d3d6123083d5728b93d3e78403d3b33a73d3952813d33de0b3d3315623d2d18503d258e1c3d1651683d137ebd3d0433333cf1bb8f3cef77c53ce42b063cc42e973cbb76ba3cb2977e3ca9f1d13ca927de3c9f76bc3c8c05aa3c8996c33c76fb5a3c713cc23c5e148c3c49db1e3c3f68ec3c37ee5e3c1c12583c0421073bf842933bee7f6b3be97d503bcb00723bca4dfc3bc152093bbbeb293bb76dbf
  | 7, 31 => 0x42f866bb42f632d442f0d9a842e1a57e42d0a56542c8c34442b9b9cf42ac645c42998d1b429194c4428ef6dd427fbe86427f1af9426b973042581296423c2f0f422076674205c7fc41eed4d941b76e4941b727b841b69d0641a0f8e5419ded07418f1b6d4176f4a4416bf81a416a656a41591a304142474e4137cc814128f74b4126f103412578c0411e1606411cb3814106ce394103326b40fd224f40db6d4d40cd1dfb40c598b040afb85240a02624407deaa34079c065406ab6d740693d22406563f2405ea62740388d6e40374437401c7362400c1dce4005613d3ffe5f943fdbfada3f7c4bfb3f556bea3f4f62653f31a8ff3f0f6b853ee627653eca734a
  | 7, 32 => 0x4694fc3a463d096c4635a280462da2a7462b7d76462a8adb46066b594600b88c45eb0f3a45e4747c45d2f7e245cc00f045ac30ab4599c620458d81b74555be7e454d2f9545439dca452c9daf452c65a645240d2d451ab6874517da0b450fb83644f6b8eb44e6301d449ebf4c449d1d8344926a5b447cb4b94471271d446ff426445743b244486a2d4447c9944444bf334433053a4430f9e2441b0abe44139dbd44083260440701b14403a3f643fe061e43ec1fd243e09f6143b3f83643a324f5439c107143995f8f439361f1438bca224376d445437388d2436bb96b436af8aa435d088743539e7b434f8b9e4335f61a432ba9e54328a9f74326c62a43225239
  | 7, 33 => 0x4ab2d3a24a9f478f4a955a544a7b71084a78fb204a7573d84a552a2c4a3407f14a210cdb4a15464b4a12e8ff49ec1e8849e8bf6a49b2b25e49a9c5a7499ff207499bdd3d498a015149868c7d4977121b4955ace3494905a649307b8e4925eaae4923be3b491edd7149045de949020b9748fc095048e49fee48cb2dbb48c71e25488fc626488b1e724884da99487c1e9d486e442a484f266f484ea6d54842623e483ea007481d858547f2f5ea47ebbf8e47d42ebc47d311b647c1b47c47b6148047af1f464799348047829f99477f83b7477803dc476f8f31474a989247469676474120f44721927846d786d246cdd08946c9cb5246c4e27146bcd27f469d2309
  | 7, 34 => 0x4f149b054f13cf344f0b58d64f034c0e4ef708f84ef3b53d4ee3e86c4edd3f224ed055904eaa48c84e9001574e6f17734e6000ca4e58a84d4e4def144e2ec6ef4e1a060a4dfe91284df918184df5a5224de996cd4ddea4984ddd06714ddbbc004ddb75814dd947034dcf970d4da8dad64da4a01a4d83abb24d8003424d3b78f24cf7bdbd4cdddb394ccc05a94cb13e734c8cd04f4c8a7bb94c81130b4c7cd1c74c3519fa4c2aaf444c27cf124c1ab77b4c16763f4c0e8bc94bfbb7134be0a8b54bdced374bd507704bc35c1e4bb3854f4ba78eb14b9295244b7eed9b4b724d3c4b5530754b51c1c14b49b1624b49adc84b4577b44ae6c7cf4ad57a154ab64446
  | 7, 35 => 0x53719d8b5341066d53136392530caf1952f8c2b952f5c7f652f39a0052f330f752ee716e52ce030752a02868529b1cfd528139ab526af1005257ed4d524fa47e524121da523dee8b52166486520544805202aaca51e83efb51dc35d651d7037651cd0c8851cd0b3451b6e92451b4ad8b5198e84351969e9e517662f15171e671515b774b5157489a514857ef5147c08e50e9133650d9820650d3ec2350d278d850ae0eac508c7c62508b0f48507a7ace506a25ac505ea834503e47f0503c03d15035752a50257149501e0e26500903f44ff53f994ff402c64fe0e50b4fd7a26d4fb1269e4fa0bd084f7ce3ae4f69c6674f3e52dc4f2e7db74f2058754f182fef
  | 7, 36 => 0x59100c1758ea9de758c1754f58c1383258b3d90d58a08eb35886b755587343eb58598c44582c58925824dad257fcfd1b57f7409557ea400357e4177357e0f71d57c3fca057a0ea2c579c239f5799b2315761f8df57495bd1573f6b3d57352d045734b208572cec48570a33b15707667656fe6eb356d68e7356cdb1cc56c0680b56b49c3356a4d325565af908564d997f563f79c1563d6f60561686fd55ca1900558e1a0a555dca4d555772b35545df72553e3dd1552a60015525b117551e0ced5505044c54e2701654de281f54d51c52548dcd6a5489b60f5463f88e54468cd3544393a95436c4f053fc5ef653f738db53eed5df53e75df953c5a69353b7e048
  | 7, 37 => 0x5e1fadf25e0b332f5e09479d5dfa3e495dc49dc25dbec4ef5db173595dad83ae5d8aeb1a5d852dd45d5f16315d37651c5d3437da5d0f7e045d0f26065cefdb205cd46ac25cca7ab05cc4f33e5cb62f555c8f14e05c85a9125c5cb8bc5c4f839b5c4ec73d5c42a0835c374b825c3661ed5c3232ba5c2213765c19de7d5c1973755c06eba95c0212175bfae38e5bf2a50f5be51bb65bc4e16f5bbd2b635ba2b8185b9c675c5b899fcd5b87d7615b38aa385b27c9035b1ee1f95b020c6d5ae751b25ae089085abbf5f15a8480735a7cdcf15a5c94005a16acdd5a13cc775a0d5a3d59e4425459ce0e5659b36057599cdde1597789b059560d8c591f3f8f591164ae
  | 7, 38 => 0x62eb303d62e6e51b62e6aa0162d9bfed62a61bbb629eb36c6295fe0d6295bb43628f1ee86282bf446271d89662716a03626cde73625120b6623feea6623aade06226cdeb6225e55861e7185c61bd4c0f61bbf49161ab3dc361a56c9461867d61618590876151e690613c3abb6130069c6117d9556113703b60fa0dfe60ec893760e4e35d60d9839160c7ab9660c0381060b052ac606fac826034c002601629b7600895cc60072fd85ff7af945fcfae925fac14945f9ca9065f8878105f647a395f4f50195f4245615f2fd2825f23165a5f16f7755f10bc0a5efb1e4f5ec798025e96a4d25e8c6ecb5e823cd75e7382915e68acd65e4ba7e15e2efdb45e2a9801
  | 7, 39 => 0x689ddac26891150a682f3745682b93666824badb68216e28680c7d8c67b96dda67b40b3f679f27b6679668406793242a677f4ecb677c41556770857e6767b3b46761d98b675bb58a67566ac8673c8c25673240d56728900866e12cb066c5420266b743f166af780f66ad052d669c50826682896a66810ea5665ea9f46659d0ab66583e546647c0ab6646f12d66139f1366055c15660482fc65b27e4a65925095658ebadb655bd3486530307d652ce41165096fbf65003de664eb133b64e2107364da35e164ce6bba64c110ff64ab60646481d6396436e787641a76366418c16663e19cab63d64f0263813ccc637979fc633881f1630eb59762f9563262f94b92
  | 7, 40 => 0x6ef3c8276edc95486ec7feaf6ec6eb626eba2a606ea819d36e7a523b6e49bc9a6e32c7486e31842f6e2c6cbf6dffa9e16db91b606db099a26d9b11756d97c3066d6a9f8c6d622f366d5a8a646d450ec46d26a2b16d0794ea6cff1d7d6cd13ece6c9cf9d36c9a71536c678b3a6c5a0cc76c4f567c6c432b446c38e5c86c3482156c2f274f6c1c13d56c0fe9e36c03d67c6bc483d96ba1671d6b9096dd6b5bc7e56b2ab4b86b0f4c8a6afb7fda6afadd126af4150f6af096fa6ab8a24e6ab535cf6aaed1d76a62e9bc69faaec669f7eaf669e0add869d6fbc7697cf991693f2d6a69381fd96932c9f169283168690b614269085e5969051a4368ff633c68b986e0
  | 7, 41 => 0x75b85f8f75888476755d7d0e754d6d0a7538c69d7536736e7534373475217a3b74ddfb1a74c1d5157485e43a7481009a7478ae16745ff2bb742fee7473f66d6273e58c1873bc1ee0737deab572e1037572c4580e72bdbd6a72b542a27282dabe726afbb372517bf1724a9e0c723d438272390b01723655f372308abc7224aa91721764c172161bb071ce876f718ad4ce717df7117171ed5171608c5a71221e0371213aac7105141470f96b7470f2487870c1c5d370b7a4d470aaa0c9709f8fe67092878a7057d918703e7c9970351601701d271d7002bb117001ec7b6ff2aae96faebde16fa0ef7c6f9d40516f3522e06f2bfba96f1145a46ef804916ef50dca
  | 7, 42 => 0x7e9a49f87e7926847e0d41ce7dcf8fe67db3061f7d69b4057d5e260b7d5b2d217d50d0bf7d0d4b2c7cf359cd7cf205777cec55e87cdaef257cce1de27cc96b257cbffc9f7c85ff127c38bf7e7c29d8f57bfa9b067be9f9c57be7961e7b95b2b57b9230e27b8bb0ed7b82758a7b52e9a37af7d8d27aab21447a941a107a69f6de7a67ab117a2830fc7a25936579ff165a79c69c2779342dc97912e90178fdbcc278d0fa0178bb2e8d78b103877861a414783ba27178263ed1781db0c277fa3bd177d3623577cdbe867775f42a77699719775f5f8e772a7e8877255fef770a6d9c76f5947276c7ff1a7693aa237633cb2e75ed097375d9b4af75d55e7675be5666
  | 7, 43 => 0x8ac05ed88ab116258a75d0d28a48bbd88a2bb1848a02d776897faa3e888f0cf28881aae0888111bf887326b288391e3b87e1e926877b0727873b3d7e87093f088708b6f086f170f686b75ad18620fa70862032d485525ed78548e9a8850a906d850111f184d5459a84cc7395845d4454844688b3838eefa0836577328351634182f68c1982e0b473825392f28238f9798210308e81ff298281db8f5581cc4ed281c42b4e817cde5a816d032b813afb7d811f9e4880be6e8c80aa842b80858a34807db775806e4eaf80559cbe804e0bf5800c40117fef24e67fe6ad4c7f9298787f6c57f37f5909637f4ef73b7f423b027f3f2ded7f3316bb7ee033dd7ecb637f
  | 7, 44 => 0x990e2e6f98ac1ecc9869c8a298661240981d35b498185e2e97dec7c197699bf897513cc9971652fa96f99feb95ea652595e432ac9569c6af94fa7db494e4ba07947537c994663625945a1b6a93ae92a693809c1992e84bf992e172c992d90c16924871d69241e9ec91d5ae8391a6df7b919447e39167ca989111bfa090a6eff19088bf8f906e0b179044dca29026b29e8fc7c0158f58364b8ef789208ee1121c8eda74ba8ed86b658eb9bc8f8e626d4f8e540d8c8e17b8798dc32dd68dc1e4c58db58e5a8daf9b418da77f838d972ad68d420da48d10d8e68d08d4e68cc6bb088c54e6028c423a458bb027c28b590d228b55e7e88b36a24a8af12cf68ade0cbd
  | 7, 45 => 0xa8908e48a85e52bba84437c5a7ed37f2a7d1b202a75bf0d7a73a03b0a73136e8a7193460a6cd0577a6aff01da699c416a6038655a5e95c1aa58ef2dca4d4ecd7a4b075f7a4a8f2e8a454ad9ea41cee98a41b2503a3b263e9a39fbcefa2b696c9a275faffa23d6bb6a2249c8ba21437eea19c0f99a1648e9aa12fc5f7a11892f69ffba73c9f64f42f9f18ad099f05974f9ed8667b9eb94cf79e84b69b9e5f36789e306c279db618a69da877a49d9a6de69d78e41f9d6f93899d1c89469d01a0159ceb6db29c29a5259c22b7959bfefdf09bb7d4049b63cfc99b5c677a9b433ee19b426c579b303d659a8234a59a19ba4899f02f619971995799422290992ca48a
  | 7, 46 => 0xc2ecea5ac1572840c062a745c04a628dc023bc24c0172003bf3c8655bdb6d372bd4a6e87bcfd5554bc7090c5bbbe3450bb68954dbafe9aacba96104dba8d5330ba0760faba057935b97adbebb93197d7b9225be6b8c1a53eb8b7b82db7b4eff3b77d7a27b69905dab66869a5b5990a02b4f6738cb4b32ec3b49bb21eb46c78a3b458e8eab41bce1db38b0720b376ba03b35d13ccb2f25be1b2a83a81b2a6be01b2823254b1918a6db10c2ab2b0c3b1c5b0343c41afec9516af905b78af05ae1baede0e52aeb168d9ae55df30ade08af3ad6fff64ac75618aac709943ac634e97ac322988abf00fd1ab8c12e4aa95cf31aa1513eda9358f82a927f862a8ed40d3
  | 7, 47 => 0xfb10d886f9d9e8f0f6f0e39ae74357afe66aebb3e2117c35e1e3b6d8e03fdcdedfe7482cdca7e18fdbc0d764db3e1b5fd9eb6fbad8dfb5a8d7445fccd6d28d7ad5f671d3d244ea21d1fe6b8ed15bf8c9cfd582a3cc293b2acbe5c373cb943a4dc979a565c94f9800c8bed944c77a9705c64cc902c60f6d9cc554d9c4c31492de
  | 8, 0 => 0x17ca9f3017c8482017a8834017902c5016a53d6016736ca01627a98016131870159ba2d0156ed00014c1e47014a9bfa01439833013a6bbe013a67fc0138703b012912c4011b8e8f01122ad3010a883f0107ced6010336d700fd830700e9e4ae00d20dd100cb03fe00c77bed00ba92d900b8bf2000b4ec9700ab244e00a24f6000922fac008b0b0b0087d38b0087c4a1008170180079a9c80075f6a400702b6f006e8ba9006e1b7e0064664800615920005f7517005e57df005c959800583ea70045337d0044f7da0041eee40036146b00337457003149fd00239b2f001fc80d001c0e8400192c920018f923000d063400097cdc000733190005e92500043769
  | 8, 1 => 0x308306703018e8e0300c31102fdda1602f6529402f026f202e620eb02e0352802d94d2f02d346e602cb110f02c3a6d202b84a3502b58e4c02b33fb402ac2b9a02abe43d02a5dfbf028920080288ad160286df780281f26b02805ede027be594027931f302744277027029db026b95d90265163a0261bdb7025b429a02521820024c7a400246dc26024427ff02227175021bfd440208b111020376d201f8b9b001efa86301e3c9c201e381b901e296cb01d7b9a701cf895a01c71bd701c2a45701bb7f2101b9d6d301b81fa701af7c2a01a5f539019f57cf019ce36d019ad84e0194837d0193d28e019217d1018fcc44018ef4a7018501e2017f8327017e5a88
  | 8, 2 => 0x4ae429e04a4382104a2236a04a14502049fff89049db3b90492c5310492a906048b93aa04843f21048097a2047ab250046c21d804694c3d045de8ca045abfdc045050db044f120e044de5b7044cf32e044bf811044aea5304497b1d04495e09044937700444b3b5044127b4043d530e0438ef480434fef2042aabc7041b3da7040d573d03ecb3ac03ebce1303eb94ae03e7f46003e268b303de2e7a03dcd90903d90c8003cc22c103cbc85803c883bf03ba1c1f03a870f4039e445d03983f2c03959e8c0394e0840386050a0385b5c60372d23e036f8cd10351ee6d033c20e6033a6ae5033911f00330b25a03301b920330057c032444680319086e0313004a
  | 8, 3 => 0x6377fd706355e3a0631e9ad062d31e9062cddd706275ff7061e30b7061d8f39061b1376061314f1060bc18b0601d6e105ffc6ce05e57d0005e4e75605dde1ed05cfc16205cd4e0d05cc3dfc05c916ff05c6cd7605c6c4d005c37af405bb26dc05b96a8405b26cfd05ac5a3f05ab60e005a0277c059ecd0a059dbb1a059725220584a8fc057d687d05708e4a056b2a900561835c05605bb00555019b054b75d305483cbf054681670544471f053f7e25053f6468053a30930528bf6f0527ddac051e942e051a3f4604fbaa0604f8757e04f5a1ee04f2c0d704e1ddcc04dda23104dd9aa304d990d604d72a0104d4fa5d04cbeb7f04beb66d04b8570c04b2e30a
  | 8, 4 => 0x7faa5cf07f972d807f3445a07e64bd607e3a01907dbe4f307d1996007d0cdab07d00ff807c852d507c5934707bdc65807b9153707b453c207a99e1b079a06b007919c7b078f3d26078ecab607859ad1077fa696077e4cfa076ee63f075c925307540d360735b934072d2742071ff00f071c5aa60719e48907147f9906fd85d706ed909d06e821ea06dc31f806db012906d835a106d313a706d1c0b606cf900c06c9b5ee06c30f6d06b5620706a8377d06a7147806a7016b069d57a306916aaf06916a43068f0a28068dd4f7068ca200068c355f0686db5e06803be00676bbcd06759247066fe08e0663afc0065a5cc40657857506513930064a3e27064637bb
  | 8, 5 => 0x9a88a1f09925c59099146c2099118c5098ea881098a67b909886bbc0986e47609863c8609858a91096df6f4096ca42e096c11db096b5e44096abb7c0967340e09416419093ea4d309326c980924bd850923a57609228165091febc50917abed091702a60913fde5090b86a40902a63e0900e73b08fcaabc08f9988308e73ae108e4e54308da82a608d90f5308cddff008bb750008b64c3c08afa2cf08a7f1e808a66166089ce3e9088eefb8088a3bd8088572860879514608780ea80877ec150863f44a0859573808564872085498f0084f79ee084cf0ff0842e4a90841afbc08329bd8082f40a7082e14e20814466d0812b1b8080ae341080a563207fd7428
  | 8, 6 => 0xb4a4dd50b491ade0b3c3c0c0b2b496b0b2b37460b24c8910b20c9e80b1ee0fe0b0fa34d0b0d5bc10b0213be0afe6dcd0af3a1fb0af0f8750adecebd0ade1c540adb0a1e0ad4e05f0ad43e970ac9f3d30ac5e4f40abe5c5b0ab113330aae5ae90aa7e7380aa13f940a940a820a918e5d0a8cf8340a7eaa340a7d95770a7cc1f40a5517ab0a4e177f0a4578560a3c3e270a36f49b0a2d37040a2a53b60a2960890a18c3fb0a12f0220a0cc7ac0a081b2d0a06d0150a044ace0a037a5a09fb66d409f78cfe09f4d7ca09f3580f09f214c009f091bc09e9c2ed09de86f309dbf5a609d85e4009bdf62109bde56309ba964509b1390809afa25109ae6f5a09aa0647
  | 8, 7 => 0xcbb99db0cb2cf210cb0ff4b0caa65db0ca714cb0ca702e90c9c94560c9bcd420c88598f0c7f41780c7dcab70c7864140c7639d00c726cfe0c6293c20c5fc9780c5c68200c5a8fb60c4d5f5c0c4c0fe20c4998ac0c497f7f0c468adf0c41ca350c3e031c0c3635c00c2b40030c22bac30c197f740c1941e60c12a2070c10d0b30c01f4e10beecd100bedcc7e0beb5b2b0be7dbba0be6c2510bdf2b9c0bdccc540bca881d0bc8e4920bc841ca0bc685760bc564260bc3ad190bba9cea0ba47a630ba3a2290b9c41950b8966080b880a710b8409030b8007b30b7e4b5f0b7dd25a0b78618f0b68f1bc0b64fade0b5dc26c0b58b76e0b582e3b0b52c8c70b4af09d
  | 8, 8 => 0xe5f02050e5262200e4888220e3ea0e40e3d1c880e3c16970e3087870e2c69ee0e2313920e21818d0e1877b70e1823380e1666e40e1246f00e11e3a10e0fefb10e0bcf1c0e06eaa10e017a1b0deaff9c0de43a600de318e80de1d92b0de136630ddc10760dda10380dcd50840dcad5810da667b70d9ed2810d9ce1340d9b98230d9a2f430d99111f0d98fc4c0d949d340d7c8b6e0d7325a30d6264e80d592bc10d4a6fa80d41628f0d31e36b0d295f760d286e630d26b5970d1e237c0d1916010d12cb220cfd6d510cfd2ca80cf4e3be0cf089840cf00bfd0ced33300cec91eb0cdc1a120cd750450cd5fccd0cc801d20cc331780cc0d6990cbfaea90cbf8de9
  | 8, 9 => 0x104476cf103e46e5103cf08b103c31781036ee061024fecf10222880101cbf8e100e078810086b821004ac64100334d410032eb70ffd2ef90ff774780ff62ce60fe2fcfb0fdedabc0fdbd4130fd97c970fd44b310fc7d6d10fc497f70fc458390fc31d320fc17c160fbf56820fbb5ad00fb945570fb7880b0fa37c320f8f9e620f7746df0f71f0060f51c5fe0f28b4320f25ee4c0f25abb20f2531520f1fc1f10f1d14370f0b69dc0ef218bd0eed64640ee8d4370ee52d350ed8303d0ed4e83b0ecd6da40ec67c170ec3ac550ebd46800ebc79810eb69fd20eb5fa150eb575d00eb138a00e9a13bd0e984b940e9520e50e85b4500e7975c40e6f1ca00e6eaa72
  | 8, 10 => 0x11d2da4611d0357811c7031c11c3020b11bad95111b7dd7611b00eef11abe52e11ab3fc711a45c1711a44d4211a17c94119a8ec911991504118c9c0c118975211181ffec11796eaf1167f52d1165d291116068661157e9571156d938114ce88e114ae5b11142b383114259031141a8f6113f0123113bba8711347f3611301c751120c147110eb4f8110dc7fb110af6db1106652810f76b9c10f4d6d410ef257410eca4c710e8f9c310e4f76210e37b7b10d93f1610d8ef3210d6ca8610c3da4310b8784610b0e4c910acae7410aaf85810a962e0109fbc5e109d2f78109879551094670e1090f4911083a1951079edf0106412581062f106105c570a105c5488
  | 8, 11 => 0x13944795138fd94b138e7c60138aa59f13849d5113811860137f31501378a75d1377746613742696137281fb136ce4be136aa8f61354942b13499146134836d4133fbf891332dcc91328ec95132506d31324cbb71319f3001316477513100066130f6505130f1731130722d61303ffae12feb38b12fc1d2c12f325a412d39ad412d2682912af6d8712af490d12a08707128bd15d128b9b18128666cc12826586127e9e081272fc641270342a126961b51265702f1257a59912491195123ab3ea1237f46e123412ee122cb874122b8330122714a1122257721221cb79121ff573121fbee0121fb3b61207e52711e93b1f11e3f5a411dd562e11dd555311da8937
  | 8, 12 => 0x15b384b015b129101597e292158cdc201585c0a215816ab515800ea8157ed2791575d25b157425de15709ae2154ad43215490d82153d033515330c51152af0f21529081d1520aefb150bffbd15060f6414f822f614f6dee314f6060c14f47c0d14f2ef6014f2829e14e6b52f14e5823814def26314d3274814d2cf6f14c9d21a14c8c0c614c6fd4f14bac11b14b3853214ad719914a6dfdf14a66e1c14a5d888149afae414945cd6148d38cd147571b31459139b1446c16d144333a2143998191431174c14190dd1140c58fe13fe8e6213fe1e4213f8f18913f79d5d13f69b5213edc1c613ec19f413d3d60c13cb17b013c603d113a767b8139a99de1399c385
  | 8, 13 => 0x17a0133b179ed4ec179dac81179007cb177da2ea177750e9176395b2175ab5b31752f0131747bf5e1746e75a17459df517411cb6171f7e9f171cca691714254616e46ec616df95f916d6052f16ca2ae916c95e2716c8b35916c06c7016bc86ed16b887b116aa36b616a55cb1169639c7168ce23c1684d50716847de916843f0c16820289167c6dc616779a1f167770e11666ebe51665892e1664e4861662fb1e165372ca1650fec616452fb51643986d163cc564163c42341635abc716257b4b16202213160f8feb160f89ac160c421b160bacd11606ceac15f6285415f27dd215e4e24115db577515d9901415d7344b15c8c82715c4531315b8511015b529bb
  | 8, 14 => 0x19bba89419ba739719b4c9c919b175eb19975aae1995dfe9198de728198b80a81986b1e01980ea1819801580197c8a4b1971ab941969ed261966012c195721801951199d194e86d3193f36dc193d78361939646719384c8b19359db7192dcf4019279bfe192594f9190bbc5718fcfc2318f93d6218f3b79f18f284a818d7ddaa18d2576e18c54e1b18bdaad418b7b08118b5f64518995df3188acf5e18883887187f0177187da8611875df981854314b1844a5131843fcff183aea8d18353e0f182bd71b182692ba181d72d61819c6e2181158e3180f68dd180eaf5e180da32c17ee7e7f17d43cd217d1b55e17c043a217b7872717b6f0e917b3a3e217ace424
  | 8, 15 => 0x1b9144271b8aa02d1b88d95a1b823fae1b76904b1b66726d1b616aa81b584a391b53e2e51b5036d21b4ae68c1b3676ee1b363f6c1b33390b1b2ddea01b2137e11b1ef5501b1d8d051b18f6c01b17c3c91b1764811b108e701b0980141b0556321afb73401afb3d991af688871af5d2b11af0f2011ae3ef4e1ad9234d1ad8e4641ac9e48f1ac9486e1ac39fab1ab63d0c1aabb5ff1aa35f441aa1dae81a9354e21a932e001a9215951a8b82561a8a76e71a7f08fe1a7c33f41a74ce0b1a6b3c0c1a6a783f1a6167121a4712191a4530601a420b991a3568b81a2e95841a1bd6c81a0e2c6d1a0bfd8c19f7c18619e11c4d19dea43619d9383b19c5c6c519c44953
  | 8, 16 => 0x1dd33fe71dccb38d1dc860161dbad3c11db918f31db710d51daaa6361d9bc5e11d99f3ba1d93fa751d779d091d713ed21d6d83141d63de8b1d634f3d1d613f171d559f991d4be7371d490f881d4414e41d37f7d71d3297411d2b07b31d0f800a1d0604b31cfa90841cf6fb0c1cf1c8ad1cf01c301ce3b5941cd13cf31ccb5b2d1cbe507a1cb4641b1cb0266f1c9251321c910ce51c86e6e01c7ba36d1c7364041c6bb2bb1c47824d1c3ea29b1c222d071c1aa0591c1591a41c0921ad1c00d62e1bf366371bf2f8b81bf159241bedbec61bec8bcf1be686521be2d7111bdac6261bcb35b11bca0d781bc364811bc17f681bbb94581bb9fa921bb990bc1b9e10b8
  | 8, 17 => 0x1f8d5f6e1f8ac05a1f8838501f7ddbf01f77edff1f75b5f01f6e838e1f6e41bd1f6bbee11f6a511b1f50ff5f1f4db70c1f4d3b441f4a514b1f43f8931f43dad81f43beb31f41db3f1f4107a41f3e35661f32deeb1f2e232b1f189f051f0947281efee3b11ef28e161eed6d5e1ee735831ee692bb1ee1fe0a1ee08d791ecb9cac1ec02df21ebe63561eb703251eb6236b1eb5eff21eb4da5a1e9a332c1e98d34e1e9686511e94fbb31e87ab511e8689d91e86532b1e84a7541e755c121e6dbd9b1e64be151e5f793f1e51c3661e4cef1c1e47784c1e433a0b1e3046931e2702491e1289f41dfaa1261df7418c1df28f881dedcf571de6be4c1de302111ddf1bb5
  | 8, 18 => 0x21a7a29e219f618d219998762198f64921972d712197289c2194b1e12190ebfb21806a5f217fb7ab2161bd572157891c214f891f2140a6dc213bb39321326ab1212ea1d6212de8c7212ca35b2123399f211a5b842118ea4e21188a292114b5c5210823e721028b5120ff22d820f8174d20ed877a20e9e41820e9deeb20e80d2920d7bd6e20d19fa620cce72a20b5a62f20abe65520a7cfad209df5af209cc2b8208cfc59208a5d612089c7d82087ddad204dfe7b204c43be203e777820320f3f2030f27c2027e109201c662e2013bab5200987312000169b1fff583e1ffb1c3c1ff497ab1ff460fd1ff0b12b1fcf3c4c1fcd517e1fc46b481fa7acf51f9ab471
  | 8, 19 => 0x241e9492241ad126241a7ad9241727012411eeef240f8164240c64e8240ae8c023fcdc9423e774a723dff01223d4545a23c1597923a3b46a238e6b4b238a22792381b117236f421d236422852360ca84234fb6ec2349ae632340a953233ac38f2334de3d23232bb123115535230da954230c271e23075fb622fd753622f3072222db102922da7a9422b4212222af256a22a63ad0228cad772289b830228766952286ae5f22842b7a228112dd22775a912274480c225614f52249009e2241fdfa22386480223297ff222ce612222badc82219c5c62201c084220184b421fbbdf121ef4f8821ec8fcb21e385d721d6f23b21cee32a21c5ebbb21c4221121b14967
  | 8, 20 => 0x2701a44e26f6e3bb26cd6b6226c8619726ab3f9026a4ce3c26a2a72c2692bbf9268ffdfa267bc13826508858264c9d5b263a9cf826313d66261d3a2d25f9031e25ea966f25e863ce25e7a8c725e3616e25cf957925ce988925c0af6625bf62da25bc8646259960fe2592f5272583e1db257a4fdd2578bd062569ad6c2561ba83254688ab2537f1e82537de42252553e325236eca251e596f25126da125107205250911c42501c2ab24f98d9c24f9153424e956af24e6572124e4fcaf24e459e724de923f24dae00624ceff9d249f46b7249e13c0249c1fd02497781824935327248c573a247620b124610474245e52492457c2132451f0a5244df6f0243e025b
  | 8, 21 => 0x2975c85f29607d1c29361e992929ee0a2906acc72902548a28fe480e28f9a09c28ee85f328e8a3dd28e7191828cac72e28c0232028b81723289aebd1289a16c1287b8ee528724e5228711b5b286bbf712867ab8b28568593285642c9284b44b22848d5e3284540db28405ef3283e51a228292f66282822e128219df2281eccf52807d6102806f874280595ff280101dd2800b7e927e4253427e2eabc27e2943427dc2a7927d9ca5027c5523f27b90ae827ab903f27a041bf279f0ec82776adc427761c882765125e275a9111275a59e72756593c274e8fce274d83302738de932735a43527343b552734241d271ea9ee271697802714ec4327066c0f2703f5fd
  | 8, 22 => 0x2c3a93192c257a442c1e05c52c13b3f92c0562fe2bed70972beb44db2bea496e2bc4ce552bbe93b92bbe3c9b2bbacc472bb366862bb35c992ba38bee2ba1f4fd2b9bf9522b99f9782b7cce4c2b7bb5282b697f972b68493c2b4eaaef2b4e356a2b49cc642b4377da2b3b10152b2d004f2b1da5372b0f0d152af869692af3ad842af0e54a2aea4a572ae5dd3f2ae2671c2ae0015b2ade94932a87d1352a8542b62a8215272a453d742a42365e2a37fe472a3590b32a3545ab2a2558482a18c5452a18b1152a019a6429feb21a29f03f5129e3c6dd29d8a63529d327d929d184b829d0fa1829c5d20929adcde829a27794299614d02991aa6b29826dcc297c8178
  | 8, 23 => 0x2fdc18562fcc2b4c2fc8e0e52fc5c17e2fc3ac992fc300cd2fc1cdd62faaee7e2fa64e2d2f8588422f6e0b812f59945c2f584b4b2f4d90c22f361fa02f2889d82f2552022f24dc7d2f12b9302f00f2e62ef1c4752edfe9812ec5e0d52ec1bade2eba9c2a2eadde6d2e769b2a2e67a46f2e65b2a12e614ed92e5cdd212e5c7efe2e570bb32e514e2b2e36125d2e2ee1232e2b96de2e1894302e12fa812dfb86f22df8020d2de9f1492ddea70c2dd510492dce96282dbb4b382da48ee22d9eed072d7236402d676bde2d53f2802d369e072d365e062d3517a42d0e32a82d09bbe32ceb34132ce695db2cd0d2002caa865e2ca0a36c2c96cd9f2c8f81db2c49551f
  | 8, 24 => 0x338831c033683f5c3356043b33423eb43341ea943327dfd5331b02bb32fb56fb32e7a2b532c4be2d32b7ba8432afed9632a7724b328dc3b13277aafe3274ab1032689c293257fc433254f5ca3245c0db32424cd132423b763238b28132322c85322b3d6d3218650f32072cff3204df5831fb748031fafa0d31d8831731bfe7fc31a546c731a394a03179ee82316a034f3159d15b313e7f7231238405311f9c1c311b70a2310805a23100fe2a30e4612a30d023d730b019f8308be265308a6f81307c6429306c1e2d306a3adc306a171f30676179305a591d305583ee305123333046230f3040f4c2302786b53024914330224719300c8ae12ffe8b8c2ffd0730
  | 8, 25 => 0x36cb84d036c47f5136c0118536bb0b07369be8ad3689a3ca3680fa1736666a47365b60ec36478f6436417ca2360c21523608f3cf35fdb5d535e18e5f35d94ad135cdb51535c3284c35b16c6b35a9672f359ae2403587cad83580d036357ff527357fc1e0356b6b27355acb41354fc3f3354487f9352f52a5351ba90535084f653505f83134fddded34cfeb0e34cb4d7f34c83c4534bb43f334b302d234b1709334b1574a34a98c2d34a57d9334957f5234798581347903fd347866bf3459eb8a3454a95a343bb0253427f6003427c44e341e3fa0340eda1d3403cd2833f903b533e8e1eb33e1b62133c8b5d233bc990e33b7280e339919af33913f9033909cc8
  | 8, 26 => 0x39b304da398b8079398abd3d396accba395cc66339548953394a5e623941b9073934c083391ddfc6390edca5390b0e813906d2023901d83938fb182b38d4624138bb6fc9389e803c3896789b3893427c3882c425387a2a873865714c3849fe6838495d9b3845a223383f6d07383b8b9d3816aa6e37f367c237ef0c5737ee5ce137e92c8237e0168737dd482e37dc153737d01ebe37cfaa3437cf745437b43bbf37b3694f379b33c837955794378b4b7e377f9890377e62293777514e376c86ec376743db3765df9237626c2837538478374eb08137486f1f37461ba937388b9937273121371eecca371d7ac8370ed6f136fe584a36f3449136f2f6f936e56f35
  | 8, 27 => 0x3d2570a23cf2c99a3ce5a51d3ca96b683ca8dc1a3ca0810a3c7cf7373c6db7373c5d34af3c45a02c3c2942713c20a57b3c0f1c6b3c0c2b863bc521233bc30ce43bc1fdfa3b971a0b3b9003393b82f6443b808fe33b6fc15d3b65380b3b602d363b5cb0243b4e54563b36e6013b29d7ce3b17f31f3b139b2c3b10ea4c3aeee37e3aed76363aeb90183ad6c6153a9aae683a9a2fd33a9666773a95c3af3a95b27b3a778ae13a6babb83a67c5b93a65534c3a58504b3a5299283a50303d3a4d89983a3b815d3a3801c13a3324c63a2e78df3a291e6e3a0de1363a005f9c39fad53539f528b739ed64f839ed5bde39e80a8d39e114af39c6b39739c582e439ba61b9
  | 8, 28 => 0x4048baf64046035f402f70f5400878db400324b33ffe5f943fe3571a3fdb964f3fd70a5c3fc519fa3fbb0e7e3fa41e753f92d4173f889ea03f8510353f6563253f59de623f5283f73f360d173f336d103f2dd6c43f156bf13f14c9293f13b1343f1007a73f0923923ef744043eebddb43ecc8f123ec413b63ebd7adc3eb4d2253e91d7833e832a363e6c598e3e5f4fee3e453b073e3c26493e3c133c3e3aab843e3092dd3e2cc2603e29403b3e0435753df8f97b3de9cf423dd643a13dd4219c3dce94d23dcdd0e03dc4606c3dba36723db50dba3db18af23db00ea43da670fa3da4f4d23d8e4f2a3d7a1da53d6c8f263d65173d3d52ff3b3d3c427d3d3b0f86
  | 8, 29 => 0x44a9192744a373cc44a000cc449de72e449d88694489ee594481059d4475c9a34463e1a2444da20f44340db9441882b443f282a743e8c42e43be73ac43bbc13543bbad8e43aa0f8443400a86433d10e9431bb1fa431289364306549e42f866bb42f2a2c542e31cbf42d152ee42b51a9142918a4e4282dbf3422805d9420e4e54420c91a5420c5a644207e54741ff894941fc4bb341e1129041da6b0541c812f741b7493441b727b841b6f21941b2f23a41b173e8419fa2114194a68141698c7f4164aa974147b459413a4dd1412e6e36410ccee44105faa540f06a5a40dd568c40c46c8540a24f1240a0782140977aa44096f4a140945908405e1706404caa72
  | 8, 30 => 0x488cbbc8486cc6af48616a594856da40483f2d794836d3aa482144494809508347fe148947ea767d47d70f8d47b7415247b457bd47a129ad479b8ae84795930447936a38478a610d4776e5cc4774a323476eecae474f6bfc4742d8ba472989b9472557484724f20c4723bf1546ff6cc846fad09646f95bed46eceb4546de083b46b41f0046b405fb46b0c16246684875463aaf7e461c2d1945ed4cce45d9a36c45d7e1d545d6305c45cdc12a45c65fc645c14e1545bebfca45b25d2045a9e4e045830ef9455e4ff5455cd319454b05f545240d2d4521548c4510d6894505fd6844f47d3744f2e12f44eea21c44e9ee3344e6c12244d2620044c131c944b76b6b
  | 8, 31 => 0x4c5f1f294c5618de4c553a6c4c3d9c8a4c2cd99b4c1f71e74c125d814c0d00554bff3ebd4bf792774bebda464beb7e8a4bbd1bd24bae03514b6392a24b60ae344b5530754b54c3944b3da0b24b3934a04b3787944b3774874b1e37f24afb991f4afa66284ae325e14abb86c34aad9dcd4a9f478f4a9b0a3c4a7e6d3c4a646c9a4a6332144a4c6de34a3985824a367e5d4a2c8a214a26c7c54a25f7e74a24c4384a227c924a16703b49eb2f4549d39efe49c0950149c0298c4991755d49658823495fcd90495ef970495d0cdf49545605494e9b7f494c21804948dce74915f2e54915c50c4909a3d4490063fa48f2575d48e5dcab48d9c79e4896f291488f0de4
  | 8, 32 => 0x50c2e11150b075c2507bce47507a607a50388629502c0f915013acaf4fd6cff04fb83a1a4fb5fb6f4fae027b4faa0fe54fa158434f9a97dd4f56bb1e4f460e524f2ccd2f4f20af2c4f1f729b4f13cf344f020dbb4eee4d884ee372144ed62e874ed5b80f4eae3f0b4ea51bda4e7138be4e6f17734e5c4edd4e579e784e48b0844e43983f4e2cd1574e14ce8c4e01b8d84dfe91284dd947034dd5bc374dcd012e4db003c54d9281ad4d90c5184d83bd1a4d77c6494d6b8c254d44bdec4d3325c14d32086a4d1dd6a74d19d5394d1706e04d15d3e94d1403fb4d13520c4d1020544d09dd704d01e0504ce1e28e4cbe32f34c9c59e74c8de7444c843e4f4c7e63c5
  | 8, 33 => 0x552350e4551e0ced54ef3da954c582045486bf6b546dd8355468e30c5468710354468cd3542be2d354281132542238b7540136f153fb059153c74eee53be947553b9274e53a7687253a16b7753967ef7533a44415324ac9b5323c4515322501b530d52fe5305b1db52f9de8752ed943952e282c452e0586a52d5862752bc14a152b0029652a948f5529ee68c529e72c4525a2da95251778f524e447c524750f852422b6a522ba2fd52237e2a5212924452104369520ea34051ec6eab51e1ff2651cf887151c2a5d951b78e20519ab9005198e84351775440517407bc5171e671516e4a0c516e25a6511cb671510863995102c56350f46a6250d6196150caaf88
  | 8, 34 => 0x5a4b354a59e4499859cf631359bac44f596470745938bf5259361217592e32345925ca3a591037a05900c9a958ff6f3758fe2d5e58e0ea6d58c44cc758b4d26e58af780358aed53b589b88a5589a55ae58882db35878256c586a354958669b2458568dc05852591a584dc929584c5156582c617758081da557eaca9957c8510257bdc42c579e4187576c168457506455574ba3c857495bd1572ad6e0571a3987571631fb571429b7570ba81656fdd48f56ebb79956d64e8f56c0bd28569e43e2568d80f5568d55ba568165cc5677922c5640cd015634cf33560459cb559ebe4a559da62a559786b055871829555f2d35554eebc55541581f5529c4bc55279eb8
  | 8, 35 => 0x6022746f6018a69260172c1e600a2f0e5ff8c6645ff545755fdd24465fd1a9695fc4201d5fa5a9eb5f9dd4b55f9ca1be5f781fdb5f73af7e5f4e93115f44358a5f3b6ebb5f18c1ff5f0e76a75ed20e9e5eca9d125ebfdf205ebb609e5e823cd75e57150c5e4c16bb5e4ba7e15e3f16115e3718de5e3317705e2f16205e2d59cc5e281d685e00209f5ded9a615db1222b5da08ff25d9a15475d8b9ce75d70925c5d15e8155cb870b25c839a335c63976d5c63486b5c5eb0be5c3cc9a65c34babe5c3291595c2ac0a45c061ddc5bf189b95be8faec5b9b57955b7ad23b5b6abd135b59a8985b471ee15b1e68855b0e3d165aa252c75aa138ef5a8d42c55a803a69
  | 8, 36 => 0x65919e8965693820655bd348653f34e8652e5de36510c2d064f8472764c3724564b8974264b28d6d6495a531648de8f764669a74646425326449fafa6445cb016430af386420fbf6641eb1cc63f5020763d8830963d221bb63c13ccd63c052da63b5739563b0222c639808306391c9396387fd9f636786b36366dc74635fe932635f85926359d94b633dda60633706ce62f03f2962e0c24662c6ef1b62b676d8628aab276276e53e6262b36062602ba2623d9f516228a99c61b8a00d61b5c49661a341c261959201618c85766184828f61710dc16170abaa616b5e616159e40a6147bde26141e50f60bd83dc6081ba1560657e6b60640d76605c13f7603424da
  | 8, 37 => 0x6bdc813a6bcc89716bb351716b9cc6dc6b9bd11b6b8da2576b82d2926b75da0e6b41a3056b0fae626aa3c7f26a9665146a88fdf66a860e7d6a68f01b6a2cb15769f533aa69f11c0069f0339569e03c4169c8dae769bc09fe69add71e698dcf7a698a57b8697d3ae9697c2c936952462c6935547469132e7568ed852368ebd3d168babb3e68b4f2be68addb4668aa9e94688ad35968740781685c301a6844311f682cbc96680b44d067d1afb867cc5fdc67cbcee167b96dda6769cf886761d98b6756648f66d973ba66c60be966b93b0066b2f12a66b112f266a820ef66a6abca666a3d406668b27b66506280664337226641bc83662cade76620a43266139f13
  | 8, 38 => 0x722b39f37220877b71fa9d6071f293e5715ed8cd714171fa710e87ac7106bdd17105141470f2487870e8e4dc70cb26f770c6457870be560e7062efd1702e80b770204d3f6ffaf5a46fd8cd5e6fc997ca6fc6aa116fb88f316f70e7416f6372886f5040666f3f75e06f358df36f2fd0f76f25b4376f235bb76efd857d6ed3ba086eb0d8ff6ea5be566ea1af776e66ded16e51bd3a6e2986b56e1aa91f6e02ef1e6e027d156dd7d4c46d97d8356d74d5716d6504406d526db16d3985546d1a4a796cedc9dc6cbd44c76ca450b26c949d0f6c93ea996c8fad2f6c87b8576c6018356c480ff56c46691b6c2ff8856c29f2be6c26f03e6c1722946bf8348d6be9df9c
  | 8, 39 => 0x79c5a5ed79a85e7d79631737794f9c9e7941ca66793aa0b17937e0c7791acb697908ee6b79049769790460bb78eb0ccf78e78a0878db76a178b56d5978aeb2bc788976d1787ea3e6780cf52f77f1211e77e6ecaf77cd12d877403ab07707b03a76a4f686769b998d7637d1b37626df83760a6a167601c86b75f8bcd075f7507775d6d5b875be566675b448a4759eebdf758363c275825990755d55d37530214a752284bd75217a3b7504c92575013ff474ffce5974e9f1b174e050a9749bd1687487290674698089743b79217425b81e740af7a473fe195c73a227887352aad273309ada732fde7972f4f16372a79310728fee67724c47b9723594b7722d6246
  | 8, 40 => 0x83fd001483ebbb5f83d2927283ca7f0f83c67a1783b70e2b837fee22831638a582f6fc2d82cf608682cc9d3282aaa9be8272bb0682250d2f820e139381eaa1d281c53d2b8199d1b881666bee813afb7d811ce9a980e1823480a1c6c9809d4b5d807d52a8806a59a5805347127ff9cc137f18a6847ef8638c7ed273b47e9957db7e87f03f7e6274f37e1a1aab7e188e047deebd2a7de207e37ddfd7137dccec057daa9a0d7da777d67da742967d8f0fc87d55cdf37d4ceef07cf44be17ce454187cde532d7cc7bf827c627cba7c3624b57bfa3c847ba3ad6c7b9d94607b5dcdc87b4297bd7b215cbf7af7d8d27abc99ef7a8e45157a8940fa7a5437da79f9dea9
  | 8, 41 => 0x91e3ffd990fe5c9f90ab3386909946c99098ddaf90679dcf904ac1f4903730df90287b188fc7c0158fc0eb958f8ed75c8f4125498f0c431c8ef4be148eefbf098ee94a8f8eca2d5c8e87597f8e4a9d7d8e4628788e44a3508e1ce1438e0d14f08da330488cc6c50b8c6603f98c57a3848c3c93a88c19db278c18c9988bc468e88bc205418b7021d88b4d8ea98ad530288a84b9f38a7e82c18a75d0d28a2ea6fd89eeb5f189e53b5789a10b4a891dc19288eb1c66887fd7c38875ee28882ad6ad881f35b987fda1a487f81fe587b148c1876f25cd8731e44786cd4e0d86280db0860e552b85cf20288558d6af851eadc3850c5ee3850bfa7084c71a3b841911bc
  | 8, 42 => 0xa649397ca5b6fad2a51e21c3a4d4ecd7a4896595a46f3c3aa43734b2a3e91ea4a3ce3fc9a3bc80bba32847aea2615c3fa2579dc6a20f9fefa1c4e9d6a1bc5a2ca1814e9ea12fc5f7a1140d4fa10074d29eff98c29ecf23349eb1473a9dfd69f29dd9be4d9d52f3999d46a7e79c5124049c351c529bb8b2419b7b36f49ab527c99a9984ea9a7b8e4699e2af58997e899b98f9d92298c7a26d9820076597eb361c97d810c79770befe974c2607971a0e8896e3261396a1a8d095fa3fe89569c6af953ab04c94fa7db494f1aa4b94bb68d1947537c9946df00094663625946082559428512793bcf82493a20ddf93685009932bd26492e063489202bcb291f78d12
  | 8, 43 => 0xbbc9cde1bb982356baf5a8ffbacbc7a1bac9d209ba7b6e49ba3a40feba20a602ba12ccacb99f3642b8e2b8f8b8c7aff6b8c1a53eb8145925b700b49fb65397d1b63cf2b9b6238d2fb5dd64a6b5682e6db49bb21eb470d95eb33a23bbb2f1190fb2b93d7bb21c7031b12b81dfb03525f0b0067fdfb0043147af4d9b24aeebd813aee07230aecd7615ae9489c6ae58c069ae2cb64aae07661cadf62d4ead439e10ad3c19f1acf1f771acbd2fb2ac807a52ac0c75d0ab7f540eab1a2421ab172dedaa6cd299aa5ca3c8aa21f1f9a9f4296ba9c71f56a9a17604a961cc27a8d63e1da8d43e42a8c735e6a8362696a8175523a803d674a7fdfa32a7f2cd51a73a03b0
  | 8, 44 => 0xff5f94d3fc7dbec2fc508471fb7dc2eaf6f0e39af4597140f3ee149ceebb56fde6d75f94e1e3b6d8e13667ecdf831e18ded60bb3d9eb6fbad6273825d4ab386dd427ce1cd4157a5bd3394254d22857aed1352aa9cffe2b47cffb180fcfa70688ced6dc33cd3d5382ccd7c477cc0bc9a8cbb7fcd8ca7d2032ca43ddb9ca224434c9b8219cc933c8a4c885e425c835b3f5c824d813c7f2cc7bc78f5f16c76c8933c5113535c4fac40dc3e2cd87c3a45150c37ad422c31492dec2ed83b9c2da7012c1d26a24c0780524c00f9513bec51cd4beaba3f2be625fdebdf877fdbdc2ad60bd4a6e87bd3f3ec9bca20540bc5c9bc1bc3dbdbabc33723ebc2c4956
  | 9, 0 => 0xefa119a0e00b2e90de037560ddf6efb0d8820ae0d3710940c63290c0c61f6150c5c2f730c4534a30c3734f80be869060b74113a0b7381ec0b730f2f0b1637620b11f3680b0f84a80af51b3a0ad4e05f0ab931300aa13f940a333cdf0a2ad3080a018bd30986c2fa09606981093232db0920c11f091588e108dd847c08bb750008a065240855b2f30855630f08276c350825d6bd07d8cae707c4fc7807702c630736859c06e28a1d0639ba5d058842f90545b72a04a32974046c7fda045270aa044c74e303c883bf03a815410395f3510395b5c303594031026cb456018f63ff016fcbec0158698301267a24010ed03601035853010336d700e3a7eb00b0b9b6
  | 9, 1 => 0x254b0a0525037740248b44072467a7f023f46a8e230d4bec22f1bdc922de6ed122ddd858217e0e4120d091ae20545d1320175fae1fcdc9341f633b3d1f032bfb1f0323551e9aa2301e9160201e82dfec1e643c311e6023731e19f9281cabeb561c3a389b1b9e1c3c1b88d8c51b2028471b1fe03e1af017dc1acc2ac91abab90d1a5a4c351a4ac5c81a03da7219c4321019b8f616195ff9b4192dd7e618fa5ae817fc68b617b2aa431785fb0e1709d34b1701f3db166648a6166038d615d9901415d44ae1158cdc2015271a13148bf3e713174ea612f52f5e12f377911286536011b6160e10e4f76210c453d10f9613a30f8fea5a0f5fbbce0f28bcd80efa16c7
  | 9, 2 => 0x3efd0deb3df73c413d41db013ce42b063ca0810a3bae9ee63b56244b3b28ee5039e42e3239da543439be360038aae2133886afd03854fd8a377f98903719d683370f9e6c36856e0d3583e0d235435f963522e4d734f7f2dd34323136342c5fc833f903b533e814843371c73d3274ab10325b82003201aca031719c9430f34f6e301263b42fd2f3c62f4be8312f049e502ebc6d2d2e6f6ad62d9542e42d7595d42d7462dd2d259ea02d23e3e32cd6f8632ccc37d02b96037b2b7549ec2b4443ac2aff60902acee1b12aa453b229d230a929a035e8295e87052915db1c28a69926280101dd27f8d806279b3fd0277aff6927797b0d27186efb2628b9c225fd351e
  | 9, 3 => 0x68cf8c8e66a7eaaa657328ca6571f5d3649ff1276420fbf663d574b46375e40761a9253461401128606e1f1c60372f1b5f0c900b5ee643655e231fa75cc10bae5c1dae775bd9ade05b04717c5a76ac565a432c4a5a0136e858cf329c56983526552e7a65547a6fef53746046530879d65293706051e2546a51a1bb6050b3afd350a23e17508fe2fd50705e515003f5084fa8f3134f957da14f35807c4f344d854f1dece44e91feef4e6c46a64de1dc184dd3689e4d68be4d4b9bb3db4b9124504b52ecc24a2a9f604861b08748583008470fa1e646ae94c5455a644a448b097443a324f542430b4c4192e41840f5dfc540dca04440b27b0d405a8cd83f88fbe0
  | 9, 4 => 0xb0679ea4aea99257ae9c89fbae07661cad64cfa6a9720424a6628396a4485f23a39cb00fa0fff14c9fb8036d9ecf2d37993da41e97d810c7975c5a1894be9ea4934840428fd7f8128ef315a78e4127aa8a2ea6fd8a02a3fd87e21cdb8765e53a873edb9a858652e183df505f837c96ab82fe7fa8828202337f0ffd167f0d34dc7e414df47e378f7b7e2675d37d0620dc795ed2f4793aa901791564c6788af196788976d17865427c76c7d3ba76a07b0c759fa6f075045cbb74a71b98733a585572693eae723d282e7097f2ff703e7c997028161e6f9353466f528efe6e1985346de098e56daa36ba6da4cf886c3e06906a633d0c69e48f5d69132e75690c5ae3
  | 9, 5 => 0xfdf32faaf6cba7aff3ee149cf3aeffb9f0f6539aeebb56fde6f1388ce51ba498e19e40a6da912b48da14f3a7d9eb6fbad7dea3b7d4ca6ca0d4161ba5d0527447cc0de161cb834417cb3a0003cad01822cac02059c8a16e06c870d1d1c7a1722ec6fedbb8c31492dec2cc19f1be6bb6c3bb30608eb994cfd7b7f1c446b6b15b14
  | 10, 0 => 0xf6cba7afce4625e6ccd42fcdc31492de94167bbf7a7c6fad75fd6a33737f8acf604c006b5868c475568903e846b1f45937d700b5
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x7610d204804000000036081200c0a1c30485300845010000061149430c161c3048530084500001d84348120100400000005250c206
  | 5, 0 => 0x26041100c161c3244132040500000006510d104c021c3048530084500870c9104c81014000000000104402000000026041100c0c0060580454c8401001d84348521100400000002148420a000000008120082800000000010c103870c5204c4201400007610d214844010000061149430c1c007610d104404010000043481200c0000001845250c305001d4464c420500400000981044030300000000d41048080000118534803040000061149430c0c0000118350413030000060149430c0e1c3048530084500870c9104c810140000000005148020400081654c4201000007610d21484400001d843041101024000018021484303
  | 5, 1 => 0x870c1214c0211404002059531080401870c5204c4201400000018420480305000006550c210c18000009810440303001d843481201004000010c10440303000006550c200c18002751835041408000000014943081000000003404120a00119214c02110061c3048530084500001d8434852110040060580454c84010000060149430c0c0000118350413070000061081200c0c00000002048020a00000000000000000010595320404010000043145200c100000000000000000000061149430c14006704132440401000000004110082000000005250c204870c5204c420140000670813148040000000460d4104c14000010c21484309
  | 5, 2 => 0x26041100c1c00001845250c303001d5430852110080000118350413050000046055200c0400001183504130900000001413208121c30485300845010000000085210810007610d204804010000036081200c08000000000000002000006550c210c10007550c214844000000000000000000000000045004205001d843485211004000010c10440309001d843081201024007610d1044040100000460d4104c24000010c50484304870c9104c81014040000000000000000000061081200c14000000045041200000190614931100400000d51044030100000460d5100c121c30485300845010000034485210c28000019443481301
  | 5, 3 => 0x21c32441320405000000000115300804000000021484204001d54308120100000750c13008540100081654c4201008000011835041305870c1214c0211400007511930085401000000009543081000001845250c3050000061149430c1400750c531081400001d843481201004000011835041305001d84348120100400001805250c30300000000c130080000000000000000b000006550c210c1000000000010c1040000036085210c0800001842048030300000460d4104c0c0031481310804000000065500210c00000018021484303
  | 6, 0 => 0x2000000000000000b000000014931080400000d945081301000006510d214c040000000430022030000000081200810000019543084304000006550c200c0c0000000204802080000000000320400000000000000008000000480e028c00000019443081309000000000e008810000000e0180a300000000004110082800000000000000b0001e650c520500000000003508520500000460d4104c18000018021484303000006550c200c18000000020480200000000000000002000000001540920100000001494308100000000204802060000006915320c00000010d204803010000000141320810000000000000007
  | 6, 1 => 0x1400000000000e1000019c214c12110000000000514c8206000000014032080800000001044020300000000d410481c00000000000000000000654c8014c04000000e2148430000000600d5214c04000019532440301000000004110081800001953108130100000000d0104828000010c4508130000000464c4028c000000181454c4301000000008521080c00750c932041401000c5204c42010000000000000000050000043041100c1400000004304020300000464c0018c0400750c9320414000000020480018c0800000000000e10200000000d410480c00304c00180a4000000000000104410000000000000001
  | 6, 2 => 0x812008100000000104402050000000041100820000000010440208000000010c0348100000000510812030000000081200804000019542040302000000010c200818000010d20480301000006550c210c0c00000d94508530100000001142048000000000000c01050000031508310c00000019543084304000000001210482800001180548430100000000060288000000114154813010000006949300c040000180354493010000000006028828000000045041202000000000003441800000002048020a000000000000002c000004132040302000000010d0188000000000430842030000000000000004000010c10440304
  | 6, 3 => 0x19c104c91010000000000514c82040000000145200818000001210440300000000014520081000000c1300853000000000000000024000010d0080630100000000d02048280000000350412030000016081200c24000000003802206000006510d104c0400000d52148430100085654c02110040000000000c0103000000000000001000000120180a300000000000000001c0000000430022030000065504300c0000000d521484301000000014520081800000000000000800000214c0210c04000000051081203000000004110080c00000002148420300118104c91010000000000350852070001210440029000000000043002209
  | 6, 4 => 0x184100004881200064000000000000000018000001a450813000000000145320818000480e0180a400000000000010040c00000120380a300000006510d204c0400000c130084300001d4314c420500000048c93200640000012314c400900000000002048020a00081654c4201000000011835085309000000000023441000000004508120100000000d42048240000000038022030000035481200c0400000001044020500000460d4104c1800000020180a301000000008120080c00001845250c3070000000145320818000019543084304000000000000002000000005250c2050000000145320818000000000806200
  | 6, 5 => 0x1203885211000000001a504c43010000006915320c04000000002802206000006510d104c0400750c932041400000000000021040c00000000000000b0000006514214c08000010c10440307000c5204c4201000000000000000005000c1214c021100000001802148430700041654c8101004000010c204803090000000000000018003148131080400000000000000002c0000000454c4201000000000000841800000004504120100000654c4200c040000000450c520200000000d410480c00000000010c104000000014943082000001953108030100012304c002900000001944348530100081654c420100400000000000a100
  | 6, 6 => 0x14031080800000005250c2060000006914214c08000000050085203000000014032080800000593000a301000000014943081000675143108140000041654c8101000000010c104403070000003885210c000000000350412030000003802028c080000000000021040000000806028c0800000000000000700000654c4204c0400000005250c203000006550c200c0c0000012304c03020000065508100c0800000d94508530000000000d42148100000000504842040000045104204c000010595320404000000000081200824000000010440204001d4314c4205000000010c10440307000000000000001400000d510440301
  | 6, 7 => 0x14943080c00000d51044030100000000004304100000000000811060000000141320810000799540084400000006550c200c20000001a25440301001d4304c0215000000010d20480300000c9104c8101000001059532040401000000000000002c00001954308030600000000000000100000000000c410200000000001004000000000000061040001e56504321000000001a514c83010000016081200c2400000000010c105000000014943080c006708530484400000006550c200c1c0000000454c0200000000000043041c007550c104404000000043481200c0400000000010c1030000000000320408000000025041203
  | 6, 8 => 0x10c20080c00000000010c10600000000d41048240000000000000010000000002028828000011835041303000000014131081000000d9450853010000061149430c1400000000548420100000000411008200000000000c010300000000d4104814000000000000001000000000000002c0000000450042030000065508100c00007550c104404000000003841100c0000000004500a20600000000d420480c003048530084400000000010c0188140000000000000070001e56500311000000000010440201000000000043040c000019543084303000000000000001400000000008510400000314c4028c0400000411000a302
  | 6, 9 => 0x1d4314c420500400001193000630100041654c810100000710d945081400000000010c028818000010c1044030400000000d42148100000000000c110600012038060290000030485300844010000003802028c00000000010440207000000004110081c00000000008110000000001494308140000000000000050000045095104c0400000120080a302000c5204c420100400000000590c2050000061081200c0c0000000104402060000062515300c000000194434053010000006914304c00000000003802205000000000000001000000000004110600000000852108100000000504c82020000000095310810000000005484201
  | 6, 10 => 0x464c0018c0400000413244030100000001142148000000000430842090000000041100824000000000000004000000014943081000000000000e1020000026545300c040000058504c8301000000000e02881800324413204040100000000d42048100000000000000000000045095104c04000799543084400000000014132081000000000000000700000610d4204c24000000000000000000000000043040c00000005250c2040000000081200814000019532440301000000004110082400000d5214843010000026041100c140000189454c43000000060115310c000000189450c5302000006510d104c00000000000006100
  | 6, 11 => 0x6550c200c0c00000005250c204000000014532081000000005250c2040000000806028c0000001181548030100000001412108100000118350413080019c204c5201004000000000002108000000000e01880000000c93200530100000000000000180000000430842070000000000310408000000e204803010000000145320810000000000000007001d543041101000006708131480400001d543081201000000000051480204000000000000001c0000000104402090000065500210c0000000c53100a30000000464c8104c04003148131080400000000000000002c00000000000e1020000026041100c1400001845250c303
  | 6, 12 => 0x41100814000000000806208000000000002842000000d945081302000c9450c810500000000002148420a00000000000000040000041320403000000000115310804000011803806301000000000e01880000000005250c205000000000043040c00000c0214843090000006915310c0400001183504130300000000000000200000000000000040000061149430c1c000000000080103001d4314c42050000000000314c4202000000000000000400000411000a300000000000021040c000001a4508530000000000000000240000118350413030000020480018c0000001953244030100000000d4104814000000000000001
  | 6, 13 => 0x654c0210c0000000001044020700000204c5200c000021595300844000000003802018c04000019532041301001d4304c0215000000000051480204000c9104c810100000000003504120200000000000084180000114420c53000000000000000018000000000000004000000000000000c0000000000000020000004806028c000000000204802060000061149430c1c0000000350852020000e21484009000000019543080305000000480e018c0000001953148030100000001494308100000000000c010b000006550c210c100000000500852030000060085210c1c00000000000000b00000000002144280000159410c8302
  | 6, 14 => 0x6550c210c10000000000000000000000010c10080c0067085304844010000003841100c0800000000008510400041654c810100000000004308020900000304c0214c04000000051081205000000014021480c00460853048440000000000d420480c000001a454c43010000010440028c0800304853008440000000001494308100000184454c8301001d54308120100000000004500a2030000003914204c0000000005250c2030000043041100c10000000021484204000000014943080c00000000480e20000000000c13008000000114420413020000000081200814000000020480209000006510d104c04000019543084300
  | 6, 15 => 0x324c8008c04000000000000009000000010d2048000000000350412040000000000000010000000000006104000000000e02880c00000020180a302000000000000002c000000000000005000006550c200c14000000050484204000000001203880800000000380a20a0000003885210c0400000000000000200000460d4104c1000000002500520500000000d4104814000799542040400000000010c02880c00000000000000100000001142048040000000000000080000065500210c0800000005348020400000000d421480c00324413204040000000460d4104c240000000104402040000000016320808007550c10440400
  | 6, 16 => 0x1c83651410500000000000000a100001d54308120100000000005250c203000000004110080c00105953204040000000000d410481c000000035041207000000009410480c000000045004205000000000000000000000d9450813000000000041100810002159530084400000006550c200c1c00750c5310814000000061115300c0400000411000a30100000204c5200c0400000d5104403010000043481200c040000000350812030000000081200800000000043002203000000001632081c00000020180a3010000006914324c0800038020180a400000000000000001400324c80080640000000000d510080400000000000000a
  | 6, 17 => 0x60149430c0c00000000000a10400000000852108100046085304844000000020480018c080000000454c02000000000000008428007550c2048040000000464c4028c040000000000000020000043481200c04000000000000001000000008120080800000000000610a000000000000002c0000195430843060000006945300c04000000020480209001d4304c02150000000000510812030019c214c12110000000000510812030000000149430810003151431081400000000014943080c0000184454c03010000003881200c0000000001044020400000104c9100c0400000005250c203000000000a008818000019443441301
  | 6, 18 => 0x1d4314c42050000000194314813000000043081200c24000000010440204000000000003840000750c5310814000000020480018c0000001954308430400000000812008280032441320404010000000000018410000000000000001000006550c210c0c000001a3548030100000600d5124c040000194434413010000000145200810000010d21484301000000009410481400001954308030600000654c4200c04000019542040300000122148400900000670413244040100000214c1210c0400000005250c20400000000d410480c00000005250c2040000010440028c080000189300063010000000000000004000000021484204
  | 6, 19 => 0xd420481400000000080620a00000000164308240000000104402030000021500210c0800001843540930100000000000000180075518304844000000035485210c040000000454c0200000120380602900000000000008110a00000000411008240000194430413090000000000000014003244132040400000000009410480c0000000350812050000000000000008000000050484204000000004110081c0000000214842090019c204c520100400000004344020000000000d410481c00000000010c107000004600e018c04000011835041309000000010c10480c007550c204804000000003802018c00000011931080301
  | 6, 20 => 0x460d4104c14006708131480401000000000000002000000005250c20400000000d410481000000000010c104000000000043040c00000005250c203000000000000002c0000000214842040000035441100c0400001842048030300000001153008040000058204803090000010440028c0000000d94508530100000204c4200c040000081200063000000003841100c08000000000806203000000000000001400000003504120400085654c021100000000000380220200000000000000000000085210023010000026041100c1c0000000510c020200000204c4200c08000010d204803010000003881200c0800000000000a10a
  | 6, 21 => 0x460d4104c1400000002148420100000000d42048240000000350812090000000000000008000000010440204000000000000000400000000000000b001d543081201000000011805484301000000000000001400079953204040000000000003244000067514310814000000000000000004007551831480400000000004110082800079953108040000000600d4214c2400000005250c20400000000d410481c006704132440400000000014d21081000000000000a100001d543081201000000010d008063010000000141310804000000e008063020000000081200828000011815480301000006550c200c20000000000000003
  | 6, 22 => 0x411008100010595320404010000043441100c0400000003544020400000048c5310c0000079954308040000000650c9104c04000010d20480300000c9104c810100000000411000a30100085654c021100000038411000a400001c03651421500000000812000630100000000d1100828000001a254403010000e008060290000000000454c82010000010440028c080000195310803020001e65504201000002159530084400000000010c21082400000000008010300000214c1210c0400000c13000630000000000004304240000000350812090000006915320c0000000005250c206000000001610080c000011931080301
  | 6, 23 => 0x19c214c121100000000000000000a00000654c5200c04000000035041205000000009410480c0000000104402070000000000008428000019443481301001d543081201000000000e20480302000000004110080c00000001044020300000001153008040000000514c82040000043041100c0c00000000000a10800000001494308140000000350812030000000114204800000799430485400000000000e00880800000000008110a00081654c420100000001183504130500000000411008180031481310804000000035481200c04000010d214843010000000081200810000000e0080a3010000043485210c0400000000000000a
  | 6, 24 => 0x4110081400000005050c2030000003881200c000000194434413000000000000028410002059531080400000000014121081000750c5310814000000043041100c1400000002048020a001d4324c810500400000000000000300000464c0214c04006708131480400000000000000001400001181548030100000654c8104c040000000000000000000003881200c0000000122048030200000000812008280021595300844000000003885210c04000000000000008000000000a00881400048020180a40000000000d010482800000003448020a000006550c210c180000195430803030000043041100c24000019543080300
  | 6, 25 => 0x4110081c00000002048020a00000068d5200c04000000000000000000000000e028810003048530084401000000008120081400000d945049301001d54308120100000000000080620a0000043081200c0000750c13008540100012038812010000000012038063020000035481200c04000001220480300000000000000000c000000003802206001c43651420500000000000000000b0000035481200c040000000204802000019c204c520100000000002048020a000000014d210810000000000000007000000010c0088180000000000000000001200806029000006708131480400000000008521081000000000000000a
  | 6, 26 => 0x19c204c520100000048020180a400000000000000002c0067081314804000000000000300408000000021484204000000014532081800000000000000300000000000000280000000514c820600000304c0214c04000000000000000000000010d0288000000000000000040000026041100c1c00000005250c2060000035481200c0400001954308030200000000d5100810007550c20480400000120388120100000670813148040000000000d12108280000000514c82040000043041100c0c00000002148420900000000d410480c000000021484202000000000043040c0000000454c820100000000d0204828000000010440204
  | 6, 27 => 0x510812030000000806028c00006708131480400
  | 7, 0 => 0x20480018c040000000320c0209000000000001840c000000025041205000000000010440400000000000610400000000004304180000000524c1201000000000e008800000000020480203000000000e00880800000c5420c43000000056500320c000000000000c0107000000000000002c00000004508120100000001140148040000114420413000000045104024c000000000524c42010000000000000018000000043406201000000000030041000000002148420000000650c9104c00000000032402201000000000a0188000000000000c8105000000010c01880c0000000000021050000000000204418000000043040205
  | 7, 1 => 0x380a008c040000081310803000000000000028420000000030006201000000010c0188180000000200062000000006914204c00000000000002104000000010c01881400000120380630000000324c8008c000000012314023000000043085210c000000000000c8102000000000602880400000000010c105000000000031041400000c130085300000000000030040c00000004300a20900000000d420481c00000002048020200000650c5204c0000000000010c106000000000043042000000000180a20100000000000000140000000514c82010000000002028824000000000002106000000000021040c000008131080300
  | 7, 2 => 0x324c8018c040000000304c0201000000000000002c00000000000000a0000003802018c00000000000041104000000000e02880800001040080a300000000000202880000000004300220600000000c831080c000000021484203000000000000002800000000000610300000048c8018c00000000e0280230000000000000000000000000104402080000000006028808000000010440203000000000a00881400000004340a20100000000001044140000000038852010000000000000024000000021484201000000000043041800000000010c104000000010c00880c0000000350412090000000000028418000000000081108
  | 7, 3 => 0x200404000000005841201000000014943081400000122140230000000000d4214810000000043002208000000000030041c0000000000c0109000000004110080400000000180a200000000000000002000000000380a20600000000c00188240000000524c520100000000002044100000000450c520200000000d420481c00000000000610400000048c5310c0000000c5400c43000000000000038400000000000002107000000000600880c000000e104403000000045108314c0000000001040a2010000045100214c0000000000010c1040000000000028414000000003806200000000014943081000000000000e102
  | 7, 4 => 0x31040c000000000000006000000000000001800000000000e1060000000000038420000001203884300000000000e00880800000000000a10a00000304c0018c0000000000000e102000000014530080400000002504120700000460c5028c0000000000000000300000204c5200c0000000005250c20300000304c0210c0000000000000e106000000000000841000000000180a201000000000a00881400000000000000b000000000000001000001954108030000000000000084140000000430842030000000000310414000000000080103000000000000840c00000000000e105000000000030041800000005250c203
  | 7, 5 => 0x32040c00000000000000600000001080088080000000524c12010000000006028808000000001802204000000000003841800000002148420a00000000000384100000000000c4103000000000000000000000000080a200000000000e00880c000011431481300000000000001842800000000008010500000048c0028c00000000003802201000000001632480400001954308430000000000090188040000195300843000000003885210c00000000000006107000000010c018810000011832406300000000000e210804000001a450c530000000450c1214c0000000000180a201000000000003841400000c932006300
  | 7, 6 => 0x650c5204c000000000000c8104000000080a018c0000000000280220700000000d421482400000000388520100000000d421482400000000004010a00000000c831081c00000000080a200000000000000841000000004100220000000000000284240000114420c5300000000001632082400000000000e10400000000d0214828000000043080203000000000020041c00000000000610300000204c5200c00000000003802206000000000000841c00000003408520a000000000002841400000000000000b00000000003204180000000000c8104000000000000841c0000000000c8108000000000001840c00000000000e102
  | 7, 7 => 0x84200000000000021060000003802028c0000000000000e1020000000000430424000000031081201000000000e0088080000000310c0207000000000000002c00000120080a30000000001000188000000114410c930000000000000000240000000214842030000000085210810000000003802208000000000012440400000002140220200000001140288180000000000061060000006914204c0000000000380220000000000d420481c000001221002300000000380a008c000000000058c52010000006914324c00000000000002106000000004110080c0000195420403000000046085008c00000000010440202
  | 7, 8 => 0xa01881400000000000e104000000000000841800000002148420300000001141048000000000058c92010000043081200c0000000000000000500000000c93208080000000214842050000000000008424000000020480205000000000021442400000812000630000000000c402880000000000010c104000000000202880400000000010c109000000000021040c0000000454c4201000000010c00881400000000080620600000000d421480c00000000004010500000000152108040000000028062030000003914214c000000000000021050000010440028c00000000e00806300000000000e0288080000000450c1202
  | 7, 9 => 0x2c000000010440208000000000032040c00000005250c2030000065500210c00000000000806203000000000a01880c000000000806202000000008120080c000000000040103000000010c0188100000000350852050000003841100c0000000000000000b0000000000000010000008131080301000000000000840800000000000a103000000000043041c000000000000004000000000021442800001943244130100000654c4020c040000012214843000000036514204c00000001a450413000000000000104428000000035005204000000010c104814000000000000001000000000a0188080000000000c0107
  | 7, 10 => 0xc1028804000000e0080a3000000000104320800000000003806200000000001630080c00000002100220200000324c8008c0400000000280620300000000d421480c0000000000000040000000000000004000000032040201000000008521081c000000002802204000000010c018824000000010440207000000004110080c00000000000a10200000000000000140000000000c0106000000008120080000000002148420500000000060288080000000104402010000021500210c00000000043002209000000010c1048200000000514c820100000000c13008040000000214842060000000000200410000000000040103
  | 7, 11 => 0xd42048240000000000411030000000012008800000000035081209000000000a00880c0000000430842030000003802028c000000000000061030000003841100c0000000000000000b0000021484008c0000001943240530000000000d4204814000000005484201000000008521081400000000000a10800000000c80188080000000000c4106000000010c2108140000000000c01080000000041100808000019430485300000000000000002c000000e0080a30100000000812008040000159420c03000000043002028c00000000010440203000000000043040c000001203802300000000000000000c00000000010c103
  | 7, 12 => 0xc402880400000c5400c430000000314c4204c0400000000010c1050000000114204800000000030406201000000000000000c00000000000610a0000000000210428000008120006301000000000e0088080000000320c4207000000000a0188040000000000841050000000000038410000000032402201000000001621480400000004300220700000000002104100000000000061080000000000000010000011442041300000000000021040c00000003508120900000048c4028c0000000000000610300000001083048000000000350852030000000000008418000004132440300000000010c01881c000000000084109
  | 7, 13 => 0x1840c000000050085203000000000a018814000000021402200000000000e01880400000005250c207000000010c008824000000000000000000000010c008810000000002806203000000000032041800000000010c10900000000c121480000000004348020100000304c0028c0400000c00180a3000000000000028400000000000000006000000000e0188040000000000c81060000065508100c00000000000002108000000000000002000000003508120300000314c4200c0000000000000e1070000032500320c00000000035041206000000000003840800000000004110100000000d420481c000000031480200
  | 7, 14 => 0x324404000000035408201000000000001841000000c1300063000000000049008804000001203802300000000000003840c000000035041204000000000043040c000000035085207000000000003840c000001a450c130000000304c0018c0000000c932040300000000000600880800000005250c2030000003914104c0000000000380a20200000654c4020c0000000000140a201000000000032041000000000000610300000000001004200000000000411080000000000310424000000000040108000000000020042400000004500a2080000000114104804000011832406300000000004110081c000000020480203
  | 7, 15 => 0xe01881c000008120006300000000014943080c00000004348520000000324c8018c0000000c53100a300000000000000002c0000000314c420100000314c4008c0000000002148420100000460c1018c00000000e1000a3000000045108304c00000000043006209000000000e028808000000000000004000000000e410800000000035081208000000000043040c000000043080205000000008521080c000000043002209000000000001840400000000280220200000460c9100c00000001220006300000000011402881800000000010c103000000010c018824000001a450c530000000324c8018c00000000035081203
  | 7, 16 => 0x21441000000000000e10500000000d41048100000000504c8201000000000003840000000004340a201000000000002840c000000e42002300000000000a00881000000c9400c8300000000010c20080c000019431481300000000480e018c000000000204802030000045104324c00000010c20480300000006550c100c00000000010440201000000014943080c000000000084105000000010c0088140000000038022070000032504320c0000000002544020100000000d420481000000000010c103000000000020040c000019543080300000000011431480000000004500a204000000000000002c00000c10180a300
  | 7, 17 => 0x430410000000000002105000000000e00880400000000000a10a00000000d4204818000000003802204000000000a0188200000000000c4105000000000001842800000005250c204000000000000841800000002100220000000000d421482400000000000e1040000021484008c00000001a450c1300000000011402880c00001181040a300000000000043040c000000035480201000000000001842000000003140a2010000000149430818000000003881200000000000e018804000010c4508130000000000002104140000195430803000000020480018c0000000000000a1040000000000038414000000045041202
  | 7, 18 => 0x284200000000000c0105000000000e1048040000159400c83000000000002028800000000000002101000000000e0288000000195310803000000000000008410000000043002205000000000043041400000003240520100000000852108240000000300c42030000003881200c00000000043406201000000000021440c000000000006102000000000001841000000000080620a0000000114104800000000050085205000000000020440c00000004344120100000000d520480400000000000a105000000008521081400000000000000300000000002004180000000038022010000000012028808000000003802209
  | 7, 19 => 0x16304804000000035085203000000000003840c00000000008410700000001141048000000000214842050000000041100814000000e0080a301000000010c00880c00000000180a201000000014943080c0000159410c830000000000852108180000000314c4201000000008521080400000004308420600000000d421481000000001044020200000000d420482400000000000e103000000000e00882400001183040a300000000000000002c00000000380220100000001142048000000195310803010000000012100800000000043484200000000000e01882400000000000a1050000000000104424000000e0180a300
  | 7, 20 => 0x11430080c00000002140220100000000c9104804000000000040105000000001521080400000120180a30000000304c0018c000000012304c0300000000014132080400000d945041300000000000000841000000003100a2010000000000300424000000021484201000000000002841c00000000000210600000000d0214828000008530484300000000000010040c0000000000411060000000000300410000000002806200000000000a01881800000005250c208000000000032041c00000000380220500000001453208040000000054852010000020480018c000000000254402010000000149430810000000001802204
  | 7, 21 => 0x10c00880c00000c53100a30000000001140388040000000104402040000000000008404000000000006104000000000a018818000000000000005000000010c02881800000004340620000000650c9104c0000000000000e108000000000032040c00000005250c2040000031508310c00000000043408201000000000030040c00000000000e10600000001141248040000000000000040000020504200c000000000214842080000045104304c0000000814108030000000204c4200c04000000021402202000000014943080c00000000000e1070000010440028c00000000003880201000000010c02882000000000010c104
  | 7, 22 => 0x65504200c000000000000041050000000000028410000000000041101000000000020441000000005250c205000000000a0188040000159410c0300000000000a008804000000003806205000000000602880400000000000000b00000000c1300804000000032002200000000000e0188040000000000c11010000003900028c0000000852100230000000000d421481000000000000a102000000000000840c00000000280220300000000d4104814000000003802201000000000000840400000000380a204000000010c02881000000004308420400000000c810480400000000010c1060000000000008420000000035085207
  | 7, 23 => 0x10c214824000000035085205000000000030041000000000004010300000001494308180000000450412010000036514214c000000000000c010300000000c800880400000003504120300000000003204280000000000c410100000000d420480c000000032406200000000480e008c000000000000c810300000324c8018c0400000004300a20300000000411008040000000058c12010000000012304808000000003881201000000000001841000000000388120000000000c130080400000c130006301000000014943081c00000000000610500000000d521480400000005250c2030000000000310424000000043002204
  | 7, 24 => 0x2802018c000000000058c42030000000149430814000001210440300000000010c01881c00001953204030100000204c4200c000000000104402070000006914104c000000000430402030000030504300c0000000002048020500000000120188080000000504c92010000000145304804000000000085102000000014420480c000000000806201000000014943080c00000000380a208000000000003841000000000004010400000000850088040000000000c9101000000000e0288080000159410c0300000000000a0088100000000210022020000003881018c0000000000000a10a0000004881200c0000000000380a200
  | 7, 25 => 0x10c10481c000000005484201000000000201880c00000005250c20300000000d421481400000000380a204000000014943080c000000031002201000000000021040c00000000000a10900000000000384180000000350812060000000095104804000000003802203000000004110080400000000080a2010000040006028c0000000000000a104000000000000840c000000e21484300000000000020440800000000000a104000000010c10081c00000020180a3000000020480018c00000000035041207000000000e02881800000000000a105000000008521080000000000000000b000000000000002800000000010c105
  | 7, 26 => 0x314c4204c0000000000000a104000000004110081000000000280220500000000d42048140000000454c420000000000000084140000000038022040000003881200c0000000411000a300000000010c10081c0000012314c4300000000000001842000000003504120300000000d510080400000000000a10400000000c910480400000411000a30000000304c0214c000000000504c4201000000010c018814000008530084300000000009410481c000000000006102000000000e0188080000000048062000000004881200c0000000000000410500000000002044180000000000000070000000145300804000000000000004
  | 7, 27 => 0x184100000000514c920100000000d421480c0000000304c0201000000000000002000000004308020300000000c40288040000000324c8200000000000001842400000004500a203000000014943080c00000000000a10a00000324c8008c00000000e450813000000000000028410000011832406300000000000043040c00000003548520100000048c5028c00000000043084209000000000032041000000000380a203000000000000001c00000000380220000000314c4028c000000000000841030000000149430814000000005849201000000000e0088000000114400853000000056508300c00000019532040300
  | 7, 28 => 0x11402881400000004500e2010000032402018c0000000000480a200000000000000841800000000380620700000000812008100000000104402070000010440028c0000000004200620200000000d420480c0000000204802020000000085210810000000010440201000000000032040c000000a0080630000000000060288000000000504c82010000060514324c0000000005250c2030000006914214c0000000000380a20000000000951008040000000314c420100000000c402880000000003140a20100000001413208040000081310803000000000081200814000000003802204000000000000002c000000000084102
  | 7, 29 => 0xe018814000000042006200000000000030041400001943244130000000650c1214c0000001943048530000000000c430081400000c932040300000000000031041000000414204030000000304c0210c00000000043006203000000000000002400000000000a1030000000149300804000010c0080630000000460c5008c00000000002806207000000000a01880000000000000000a0000000095100804000000020480201000000480e008c0000000003240620100000001453248040000000058c02030000000000038404000000000080106000000000001841000000000000e10a000000000003841400000123000a300
  | 7, 30 => 0x4881200c000000000058c9201000000000a00880c0000012324c83000000000085210814000000000006106000000004110080c000000031480201000000000000001000000004348020100000324c8104c040000159420c0300000000011421480400000000008410700000000c13008040000000000811060000000081200818000000000041104000000000e214808000000010440200000000010c200814000004132440300000000010c0188140000012304c030000000654c8100c00000001a45049300000000000020040000000121040a30000000000003104180000000008062000000000149430810000000000000004
  | 7, 31 => 0x1840c0000000028062030000000016304804000000000002104000000010c10481400000001040a201000000000000840c00000000000a103000000005520480400000000380a204000006550c100c00000000000006109000000000000840c000008521002301000000008521080400000c5310023000000045104324c0000000000080a2020000056504320c0000000001044020300000654c8100c00000000021484203000000000002840c000000021484203000000010c018810000000030006201000000000000001c00000004500a2030000021484008c00000000e214843000000003885210c0000000123040a300
  | 7, 32 => 0x31040c0000000038062030000000081200810000000035081209000000000003840800000000000e108000000000032041000000000180a209000000008101880800000c53100230000000000d4104814000000000002108000000000e028820000019543040300000000008521081000000000000e10a0000000016214804000010c204803000000003885008c000000000324c820000000000852108040000000000c81050000000000200414000000000006103000000000a00880c000000e214843000000056500320c00000004132440300000000000030041000000000000a10a0000045108104c0000000c5400c4300
  | 7, 33 => 0x30040c00000002148420300000000d421481400000005250c2070000000002028800000000e0080a30000000000c101880400000000004110300000000d421480c0000000214842030000000114104808000000e0180a3000000020480018c0000000120380a300000000000e204808000019530084300000000008120080c00000000000000b0000043041100c0000000000000e10400000000000184280000000038842020000000085008800000008131080300000000000000001c00000000380a2000000000114214808000000003802200000000000000842800000c932002300000000010c018808000000000000006
  | 7, 34 => 0x43114104c000000195430403000000000115300804000000003881202000000000000841c000000045009201000000000602882400000004300a205000000000001840c000000010440209000000000000002800000000380a2020000062514314c00000000043002203000000008120081000000000000a1060000000000200424000000003806204000000000e20080000000002148420900000000d421481c0000000450c5200000000000000001000000000080a2010000000000008420000004132040300000000000021440c00000002148420500000000812008100000000000c410200000304c0028c000000000000c8106
  | 7, 35 => 0xd4104810000011830406300000000000010040c000001203802300000000010d200804000008540084300000000000030041c00000005250c203000000008400880000000000080620500000000d410481c0000000000000090000000000300410000000020480204000000001621480400000000000000100000001140288100000118038063010000000081200824000000035480201000000011402880c000000000080109000000000002841800000005250c203000000000a01880c000000035440201000000008120080400000000380a20a0000003885210c000000000039082020000000000000028000008540084300
  | 7, 36 => 0xe00880c00000c53100a30000000314c4028c04000000020480203000000010c018814000019431481300000000000e0288040000195430803000000003806028c0000000000000210400000304c0018c000000000000000040000000000430418000000000006102000000010c00881000000000380a2010000001802028c0000000c13000a3000000000006028828000000e21484300000000010c210810000000035041208000000480e018c00000000000000001000000000020440c00000003000a20100000000c93208040000000000c810500000000d421480c00000004300a2030000003885210c00000000e45041300
  | 7, 37 => 0x8420000010c204803000000000140214814000000000806206000000010c2008100000000038402000000003806028c040000000104402090000000085210808000000032402201000000010d02880400000000380a204000000010d008804000001200806300000000000002842800000120388130000000000d42048180000000514c02010000000114214804000000e214843010000006914324c0000000000000a103000000000a0188200000000304062010000003841100c000000114420c5300000000000001841000000000380a205000000000602880000000000010d100000000011402881800000c932006300
  | 7, 38 => 0x30040c00000000000000b000000000002840c00000000000000b00000000000284200000000304c0201000000000030041c0000000504c82010000004802028c00000000010440207000000000032041000000c80080630000000000d4214824000001202802300000000000e00880800000000000610a000000000e01880400000000000a10600000000852108240000000018022030000045104324c00000000020480209000000000002840000000853048430100000000c831080c000000e00806300000000000000001800000000000a10300000000d01048280000000304c020100000460c1214c000000159420c0300
  | 7, 39 => 0x2c00000004300a203000000005520080400000000000e1090000000000320410000000000002104000000010c008814000008120006301000000000000841400000000000e1060000065500210c00000000000002103000000000003841800000005250c20400000304c0018c0000000002048020200000000d410481c000000000806202000000004110081c000000001802204000000011431080c0000000000c1101000000008521081000000c1300063000000003885210c00000001a4508530000000000852108280000000000851000000000000300418000000043002203000000000e02880c0000000000c4104
  | 7, 40 => 0xd41048200000000000c0100000000000202880800000005250c206000000000002842000000000000210400000000d410481c0000012028023000000000012028800000000020480205000000000021041400000000010c103000000000000002800000002048020a000000001200880800000004300220300000000003104100000000430022050000032504320c0000000000010c109000000014931082400000c9410c83000000043114204c0000000000010c104000000000000002c000000000806203000000000020041c000000000081105000000000e20480000000004300a2040000021500210c00000000000040104
  | 7, 41 => 0x320410000000010440201000000000e0188040000194324053000000065508100c00000000043402201000000001621480400000000000a109000000000e00880c00000002048020300000314c4200c000000000000401070000045104304c000000000000c0104000000000010041c00001180380a301000000000000001800000c130084301000000000e420800000000000041106000000000020042800000000000e101000000000010040c0000000450812000000004802018c00000000035081205000000000e02880400000000000000b000000000003840800000004340a20100000204c4200c00000000035484201
  | 7, 42 => 0x314c4028c000000000214022000000000002028804000008540084300000000000e02880c0000000038852000000000000038414000019532040300000000010c01880c00000000380a205000000010d12480400000000390820200000324c8008c040000000038022050000000000000010000000003840200000000014943081800000000000210a00000000001044200000000000c0106000000000000840000000005250c203000000000002842800000000000a10000000304c0210c04000000004885202000000000030040800000c531002301000000014943081c0000114420c1300000000004110081c000000000000004
  | 7, 43 => 0x14021481400000005250c206000000000e01880800000002048020100000000d52108040000000000c4104000000001230080000000000010c10400000000001004240000000018022030000000081200804000001203806300000000000000840c00000003100a20100000314c4028c0000000005250c207000000000003840c00000000000000b000000001632080c00000000004910100000000000384240000000430062080000000000028410000000043080209000000010d10480400000c1410c0300000000004110082000000000000e104000000000031040800000000380a204000000000021040c000000e20480301
  | 7, 44 => 0x4304100000000000061030000043114204c00000000031402201000000480e028c0000000003540920100000324c8100c0000000000180a201000000004110081000000004340220100000000d4204818000000000000007000000000000002400000c5310813000000000012210808000000000000008000000000e01880400000000000a104000000014943081000000005250c206000000000000840000000000000a10300000048c9320c0000000003200220200000000d50148040000195430803000000000000000010000000000006105000000000043040c000000e0180a300000000000001841c000005945081300
  | 7, 45 => 0xd4104814000011830484300000000000010041000000c40080a3000000000002028800000008120006300000000008101880400000000000e103000000004110082800000001044020900000000852108180000000000000070000000000018418000000043006204000000001632480400000000000a103000000008400880000000853008430000000000000000140000000038842000000045100324c0000001943048530100000324c8100c040000000000c9100000000480e028c00000000000000006000000010d1208040000012204803000000000006028808000000000006101000000000031041400000000010c103
  | 7, 46 => 0x10d0288000000000430022020000000000314404000000000000009000000014943081400000000000000100000000000000080000000000411050000000000038410000000035041203000000000002841400000000080a2010000000000038420000000002806205000000000000001000000000380a201000000000a01880c000000032440201000000000002840c00000000380a201000000000e0188200000000028022030000000114038804000000003841201000000000201881c000000000002106000000000e018800000000000006107000000000031440400000003508520400000048c5028c00000000002806206
  | 7, 47 => 0x214c1210c04000000000006101000000480e028c000000012304c03000000000002018810000000000084102000000000000002800000004304120300000650c1214c00000000020480204000000000e0188100000000028022040000004841028c0000000004308020600000000411008040000000000c8107000006550c100c0000000000000000a0000003881200c0400000000000e1030000000000038410000000000084103000000004110080400000000000000b000000000a00881000000002048020300000000c430080c00000004300a200000000000021041000000004500a206000000000021041c000000000040109
  | 7, 48 => 0x3104280000000000c8103000000000a00881800000004500a2030000000081200824000000000002103000000000000841000000000180a201000000000000000c0000000104402030000000000324404000000002806207000000014943080c000000000002102000000014943080c000001a450c930000000001080188000000000000021050000065504200c0000000005250c2040000000000000014000001a450c93000000003802018c0000000000000e106000000001202880000000000380a201000000000000840400000000180a2020000046041028c00000000025041203000000000031440400000004500e201
  | 7, 49 => 0x20504200c000000000320412090000032504320c00000000000806201000000008120080c000000002806201000000000000001000000003040a201000000000e40080800000004508520100000000c93208040000081200063000000003806028c0000000000280620600000000812008100000000000c81070000004806028c0000000000000a104000000000001841800000000480e200000000010c0088180000000450c0207000006550c210c0000000c1410c03000000000000024404000001220406300000000000021042400000000480e200000000000000000c0000000000c81090000056500320c0000000001000a202
  | 7, 50 => 0x1632480400000000000a109000000000001841c00000000000000b000000010c02881800000003504120500000000d510480400000000000a1030000010440028c000000000000c810300000000c9320804000000020480204000000000043040c00000411000a3000000043081200c0000000000000a105000000000030040c0000000104402080000046081018c0000000000000e10200000000c130080400000122048030000000000c831081c000000021484203000000000e028804000000000006104000000000e008814000019540048300000000000a01881800000000180a201000000000020040c000000000006105
  | 7, 51 => 0x3840c000000021484205000000000e20080800000000000000400000000020188040000000000021030000045100214c0000000004508520100000450c4204c0000000004500a205000000000e008818000000000806204000000000a01881400000005250c208000000000e420800000000000081106000000000201881800000002140220100000000d421480c00000004300620400000000d420480c000000043002204000000000002840c000000043006203000000010c0188200000000000c4107000000000001842400000c53100a300000000010c01880c00000000000e1040000056500320c00000000043005204
  | 7, 52 => 0x11402882000000002140220200000104c9100c000000085210023010000000000300410000000005484201000000000000001c0000000434802010000000114028810000000000081100000000000002842800001000180a3000000056508310c000000000000c4103000000000e214800000000032040200000000000002840c00000000000a106000000000201880400000000080620500000104c8100c040000000434812010000000041100810000000000806201000000000002840800000c5310803000000006914104c0000000c1420c030000000000020188040000114410813000000000000310410000000021484205
  | 7, 53 => 0x204414000000002806201000000000e00881000000c53100230000000000d41048240000000000c4107000000000e01880c0000000154802010000000016214804000000000006103000000000e008810000000000002105000000008500880400000020180a3000000000000028404000001200806300000000000e00880800000003100a209000000011402880c00000c130085300000000000e02881800000000000a104000000000000002c00000005250c203000000010c01081000000003108020200000048c4008c00000001203840300000000000e200804000000002806201000000010c0088140000159400c8300
  | 7, 54 => 0xe10080000000120380630000000000001044180000000310802010000000000008404000000000000003000000000001840c0000000430022050000004881200c00000000043084203000000010c01881000000001044020300000000c810480400000c531081300000000000e028808000000e450853000000056500320c0000000000388420000000048c5310c0000000020180a3010000000000310410000001a4508530000000000c5310804000000000080104000000008521080400000000000a10700000000d421480c0000114420c130000000000d420481c0000000314c4201000000000e400808000000000041101
  | 7, 55 => 0x450c0214c0000000000080620100000000004344040000000450812010000000000008424000008521002301000000000e028808000000003806201000000000e018804000000010440207000000010c2008100000000028062020000000000210410000010c45041300000000000e008808000008120006300000000008120080c000011431081300000000001621480400000000180a202000000008120080c0000000450812020000000084008804000000045085202000000000021042400000000480e200000000000010040c00000000380220500000000c831080c000000010440203000000000e018804000008120006300
  | 7, 56 => 0x2c00000000380a206000000000e018810000000000084107000000008521080c000004132040300000000000602880400000004300a203000000000201881000000c5420c43000000000012320808000000000000006000000014943080c00000004300a2080000004841100c0000000c5310813010000043114204c0000000000004110a00000000d410481c00000000008110a000000010c0288100000000000000090000045108104c0000000000180a200000000010d10480400000000008510000000000000184100000000000c0109000000000000002c000000043485201000000000031040c00000000008510a
  | 7, 57 => 0x1632081c00000000000a103000000010d210804000000000006103000000011402880c00000000180a2010000000000210428000000000041105000000480e018c0000000000380a201000000000043041000000000010c104000000000000840c00000000008110100000000d421482400000000380a20a00000000000000140000000320c020900000000c001880800000001000a201000000010d204804000000e2148430000000000020188140000012314c4300000000000e1048040000000048c520000000000c900880400000000004010400000650c9104c0400000000000000b00000460c5028c00000000000002104
  | 7, 58 => 0x20441000000c9320063000000000000300404000001202806300000000480e028c0000000000380a2080000000114028810000000000000001000000000002840c00000004500e20100000304c0120c0400000000380a20400000000000000200000000000c51010000000000430424000000000000004000000001221480000000000010c104000000010d01880400000005008520300000048c9320c000000000350412030000000000018420000008120006300000000000001840c000010c00806300000000000043040c0000012204803000000000000210400000001200806300000000000031040c000004132040301
  | 7, 59 => 0x38410000000015081209000000000e0288080000000000000000000000000008428000000031480201000000000030041c0000000000c410400000000d410481800000000080a20000000000000000180000000350412070000000012038808000001a4508530000000000c531080400000000180a2000000000115300804000000045085200000000000030040c00000000008010a000000010c02882400000003404120a00000000411008140000000300842020000045108104c0000000000180a20100000000120188000000000038492010000000000100414000000031081202000000000003842000000000380a203
  | 7, 60 => 0x20504200c00000019530084300000000011403880400000000280620400000324c8100c000000000000c5101000000014943080c000000000000003000000010d2108040000000430062070000000000300414000019543080300000000001632082400000000000a103000000000e008804000008131480300000000000003841400000000488420000000000d410480c00000000008110100000000001044040000000104402010000000000204410000008540084300000000008521080400000002140220100000000002004140000081200063010000043081200c0000000000080a20a00000304c0124c0000000000000e104
  | 7, 61 => 0x30006028c0000000003548420100000000812008240000195300843010000000006028804000000021002201000000000e028814000000001802203000000010c10080c00000000008110a0000043041100c00000000002802205000000010c02880c00000005250c205000000480e214c0000000120180a30000000204c5200c0400000000380a2090000003806028c04000000000000000000000011402881c00000000010c104000000000001841000000000000e1030000004806028c000000000350412040000000000028428000000e00806300000000000e018800000008131080300000006550c210c0000000c932006301
  | 7, 62 => 0xe02880c00000120380a3000000000041100810000000000084103000000000021040c00000c5310813000000000015124804000000043085200000000008120080400000005250c203000000480e210c0000000000000e10400000324c8018c04000000000002106000000011403880400000000000000800000000000384100000000310812010000000041100820000000035481201000000008120080c00000120180a300000000011530080000000000000610400000000c400880800000004300a204000000000032440800000004500520200000304c0214c0400000004300a20900000304c0028c040000000000c4108
  | 7, 63 => 0x214410000000030406201000000000000002c00000004300a207000000000000840c00000000380a200000000000032041000000004340a20100000000000384100000000000c81060000000006028824000000043041203000000000e028810000000000006106000000000031041000000000480a20200000000000284280000000454c0201000004600e028c04000000035081209000000000e124804000019541080300000000000030041c00000004308020300000314c4204c000000000000401050000004881200c0000000000000e10000000000001044040000000430812090000000000028428000019543080300
  | 7, 64 => 0x11402880c00000000010c108000000010c00881400000000004010000000000852108140000189450c130000000000000084140000114400c5300000000000a008814000000000806206000000000000001800000000380a202000000011402881000000c531080300000000010d100804000000000000006000000380a018c000000000058c5201000000008500880800000001044020a000000011420480000000004308420000000000000084140000000000c8109000000011402881800000000180a2000000000000320428000019541080300000000004110081000000001044020400000000d4104814000000e42006300
  | 7, 65 => 0xa0188100000000104402010000065504200c00000000002802201000000008400880800000000000a102000000000021040c000019543080300000000004110080c00000000380a2070000000149430810000000000085104000000000000002c0000000000000030000000000028410000000000040103000000000043041000000004300620300000000000000040000000000811050000000000300410000000030406201000000010c10080c00000000000610a000000000a00881000000001044020400000000000184200000000504c420100000000d510080400000000010c1060000043114104c000000000000c8106
  | 7, 66 => 0x10c028818000000000084104000000000000840c00000000010c1030000043081200c0000000001508120900000000c531080400000001044020300000000c932080000000003040620100000000d4204814000000e4504130000000324c8008c0000000000000000b000000000602882800000413244030000000000000384100000000018022040000003806028c0000000000000e106000000000010442800000c50080a300000000000e00881400000000000000b000000000000002800000000380a201000000014943080c00000004300620900000048c9320c0000000004500e201000000004110080c00000000000e100
  | 7, 67 => 0x8001880400000120180a300000000000202880400000000000a1030000000041100814000000000049101000000000600880400000000480a200000000000023441000000813108030000000000003144040000000000c810300000214c1210c0000000004500a205000000001202880000000000480e200000000000043041400000004300a203000000000e2008080000000008062060000000002018824000000043481200000000000010442000000004500a204000000010c01881400000004300a20400000000000384200000000028062040000003881200c00000000002802203000000000e02880000000000000e106
  | 7, 68 => 0x149430814000000e20480300000000000001842000000005250c203000000000e02880c00000020180a300000000010c10080c00000000000210300000104c9100c0000000000000a1040000004802018c0000000002048020a000000004110082400000004308420900000304c0214c00000000000040103000000008521080000000000000000300000000c8310814000000000000004000000001630480400000000380a206000000000003840c00000000000a104000000000002840c00000004500e2010000003885210c0000000120080a30000000304c0018c0000000000380a201000000000010040c000000043440201
  | 7, 69 => 0x31041400000000380a2000000006914324c00000000002806204000000011421480800000000380a2090000020504200c00000008540084300000000000e018818000000035041204000000480e018c0000000000010c10500000000c831081400000004300a2040000000000038408000000e20480300000000000e01880800000000000a1030000000000314428000001a45085300000000000e028804000000032406200000000000000002400000000380a2010000056500320c000000195420403000000000141320804000000000000004000000004110080c000000043406201000000004110081c00000000010c105
  | 7, 70 => 0xe028810000000050085207000000000002841800000000008410300000314c4204c0400000120388530000000000d42048140000000058c82030000000081200808000000003802204000000000043041c00000000000000800000000003204180000000454c0201000000000003841400001953108030000000000d40148140000000000c810500000000000000140000000000041030000065508100c0000000000080620a00000000c420480400000000380a2020000000000018404000000e204803010000000006028804000000000084101000000010c01881000000000000e1090000021500210c00000000000000007
  | 7, 71 => 0x480e210c0000000000000e107000000000032040c0000000454c0201000000000021040c000000000002105000000010d01880400000000080a2020000006914304c0000000120180a300000000000000002c000000035041203000000000032040c000008530484300000000008120080c0000000450c1200000000000e01881000000003508520300000000000284100000000038062020000003914104c0000000000380620100000000000184180000000058c9201000000004110081400000000000a10400000048c5310c000000000350412060000000000028418000000043002203000000000001440400000000000e105
  | 7, 72 => 0x314c4204c00000000043002203000000000000002c000000005849201000000000000001800000000380220200000000c80188240000185450c1300000000010d018804000000000006103000000000000841400000000008010a00000000c53108040000000000000000000045108314c0000000000000610300000654c0210c00000000a00806301000000010c01881800000002148420400000000d421481000000004300620300000000d520080400000000000a100000000000000002c000000035041209000000000002840c0000114420c5300000000010c01480c00000120380a3000000000000028428000000e00806300
  | 7, 73 => 0x300418000000e0080630000000001143248000000000000041030000000000310414000000021402200000000000e204804000000000081105000000000000000400000004500e201000000000001840c000000043002204000000010c21080c00000000008110100000650c5204c00000000003806206000000000021442800000000000a1050000003806028c00000000e00806300000000000000001800000000480a200000000000003840800000000080a20a000000001631080c0000000204802020000045104324c00000000005881201000000011532080000000000080620a0000000080018804000001203806300
  | 7, 74 => 0x852108040000000430062040000016514204c00000000035484201000004600e018c04000000003806202000000010d1008000000000350412090000004881200c0000000000010c106000000480e028c000000000210022000000000085210804000000000085103000000000a01880c00000001044020100000214c0210c0400000000010c1030000006914124c000000000204062000000003802018c040000000430412030000021484008c00000000000806203000000000000002c00000c53100a301000000010c0088100000000000c810300000000004344040000194314813010000000000200414000000043041205
  | 7, 75 => 0x43081200c00000010c45041300000006550c100c00000000005885201000000004110081c00000000000e103000000000030040400000000010c1090000000081200804000000e10440301000000000003840400000000004010500000000d410481c00000000000000b00000000552008040000081200063000000000806028c000000000058c0209000000000002840c0000000038022040000000806028c04000000043006204000000000000002c0000000000811010000000000214410000000000000003000000000000002800000000000210400000000c021480800000005250c20600000000002104100000000000c0103
  | 7, 76 => 0x3881200c000000000350412030000003885210c0400000000488520000000000000384240000000350812030000004881200c0000000000000e109000000000001842400000000000a10400000000000284180000195410803000000046041028c0000000000380a201000000000e01881000000000000000b0000000000038410000000003806201000000000031041800000000010c10500000654c4200c00000011832441300000000000e41080000000000000610a000000000000841800000000000e10600000000001044200000000514c8201000000000010442000000004300a200000000000000002c000000021484201
  | 7, 77 => 0x45100214c000000000524c120100000000d410480c00000004500a20300000450c9104c00000010c204803000000021484008c000000000300c8209000000000000001400000000000210800000000000184040000000214842050000000095100804000000000000000000000000020441800000000000000300000650c9104c0000000000000e10500000000003204100000000000021030000000114104804000004132040301000000000001841c000000042040202000000000e018808000001203806300000000004002880800000000010c106000000000e0188040000000028022030000000114214808000000020480202
  | 7, 78 => 0x4802018c0000000000000e1050000000000008418000000000006106000000000201881c000000000006106000000008120080c0000000000061040000000000320418000000032005201000000000e100808000000021484201000000001630480400000000008010a000000000000842400000005250c20300000000d410482400000000000a105000000000032040c00000000000210400000304c0018c0000000000000e109000000014943080c0000000200062010000000000028404000000021484201000000000000002c000000043441201000000000a00880c000000035081205000000000010441000000020180a301
  | 7, 79 => 0x10d100804000001945085300000000000000000c0000000350812040000000000000024000008120006301000000010c02880c000001a450c5300000000000031041000000c5310803000000010440028c000000185450c13000000000149304804000000000040108000000001631081c00000004500a20300000000c12148040000000320c02030000003881200c0400000000000a1040000000081200824000000000006109000000014943081000000000008010a00000654c0210c00000008120006300000000008120080400000000010c1030000003881200c0000000813148030100000000003104200000000000c0109
  | 7, 80 => 0x41100814000011432041300000000000003842000000000000e10300000204c5200c0400000000010d10100000000d51008040000000454c4201000000000001842400000000380a20300000000c4008804000000003840201000000004110081c00000120080630000000000d421480c000000010440204000000000043040c0000000000401070000020504200c000000000000021020000000000000004000000000084105000000008120080c00000003508520400000000c831081c000001210440300000000000032041400000004500e2010000010440028c040000000514c1201000000000201882400000000000a104
  | 7, 81 => 0x806028c00000000000080109000000010d0288040000000038402010000000081018808000000010440209000000000001841000000120380a30000000000000184200000000450c120000000000000000100000000000801050000000085008804000000000006104000000001521480400000000080620600000000850088080000000000c81030000043002018c00000001a4508130000000001494308180000000104402050000000141320804000011831480300000000000020041400000004300a203000000011410480800000000000a103000000000032041800000000000e1030000000041100814000000000084103
  | 7, 82 => 0x210410000000000084104000000010d20480400000000000e10a0000056504320c00000000000006104000000010c200818000008530084300000000000e02880c00000000390820000000000000084280000012038063000000000000000010000001a450c9300000000000021441000000002048020300000000c5310800000000000085104000000000000000c000010c104403000000000085008804000000021002202000000014132080400000003408120a000000010d018800000000e21402300000000000e02880c000000043406201000000000202880400000000584120100000000c420080400000000000000a
  | 7, 83 => 0x10c00880c0000000304c02010000003881200c00000000003802205000000000e204800000001220480300000000000002842800000000480e2000000000149430810000008540084300000000000032040c00000000000000b0000000000000014000000020480203000000000001840c00000000080620200000001153008040000000000000030000000081200824000000025441201000000000031041000000001044020300000000840088040000000058c1201000000000000841800000000000a103000000010c008814000000e104403000000003884008c0000000000000000900000000d02048280000000000c8106
  | 7, 84 => 0x324c8104c000000000300c4203000000000003841800000004500e201000000010c01880c000011442041300000000011401480800000000000210a000000014943081000000000380220300000654c4200c0000000c1300063000000043114104c00000000e20480301000000010c10080c000010c2048030000000314c4200c0400000c932040300000000000000000c0000000000811010000000000100418000000035041203000000001203880800000000004110700000000c52048040000041320403000000000000100404000000021484201000000000000001000000002048020100000000d4104818000001a45085300
  | 7, 85 => 0x460c5200c0000000000000610400000000163248040000000204802000000000000038428000000e2048030100000654c8100c0400000411000a300000000000003841800000000008110a000000000e104804000000010440203000000000043040c0000000104402040000000000104404000000003806203000000000030041c0000000000841070000043081200c00000008530484300000000000032040800000000010c10300000000c021480400000000000a101000000011530080400000004500e201000000014530480400000000380220200000000c502880400000000000a1030000036514214c00000000043080206
  | 7, 86 => 0x100000041324403000000003881200c00000000000000004000000000000002c00000000000000000000650c5204c040000000000c010500000000852108040000000350412070000000000038410000000000080106000000000000840000000000000e10100000000d421482400000000000000b00000000d410481c00000000000a104000000000030041400000004304020600000000c520080400000000000e1030000010440028c00000001a450c93000000003802018c0000000004500a2080000000149430810000001203802300000000000e2148080000000000c41000000000006008818000000043081209
  | 7, 87 => 0xe10480400000004340220100000000c520480400000000008110400000314c4204c00000000003881202000000000000002800000000010c10900000000c1210804000000010440204000000001610480400000000000000600000001141048080000000314c4201000000000e21480800001144108130000000000000184280000000000c810300000204c5200c0000000000000000700000000d410481c000000021484201000000000030040c0000000314c420000000000d51008040000000450412000000003841100c00000000032041200000000000a00881800000c1300853000000000000038404000000043002203
  | 7, 88 => 0x28420000000043406201000000000e018814000000020480205000000000e02880000000000000e10a0000003881200c00000001203802300000000004110080c000000015081209000000000010040c000019531080300000000000000000c000000000006104000000000e10480400000000480e20200000001140388040000081200063000000000000310410000010c45041300000000010c01881400000005250c20500000000411008100000000204802010000021484008c0000000002544120100000104c8100c000000000310812020000000114300814000000000080103000000010d204804000000e21484300
  | 7, 89 => 0x2c0000000104402030000000041028804000000035484201000000008120080c0000000000061010000000000028420000000020480200000000000030041000000000000210400000000000000100000081200063010000045104204c00000019540084300000000000e02880000000000480e20000000000c52048040000000038492010000000081200804000000000000003000000000030041400000000000e10100000654c4200c00000000000002105000000008120080c0000000000000060000043114104c000000000430402090000043081200c0000000c9320403000000000000214410000008120006301
  | 7, 90 => 0x6914324c000000000028062040000000041100818000001a4508530000000000852108100000000214842010000000149430810000000020480201000000000201880c00000000000000b000000000002841400000020180a300000000000002840c000000000040105000000000e0288280000000058c820700000000d520480400000000000000b000000000002842400000002048020200000000d410481c000000032441201000000008120080400000003504120900000001494308100000000000c4102000000000602880400000000000a10a000000000000002800000000480e2000000043114204c00000001a450c9300
  | 7, 91 => 0x120288000000000008062050000046041028c000000000214842010000000149430810000001203841300000000000003840c000010c4504130000000324c8100c0000000000000000300000001494308140000000000851030000003884008c0000000001044020500000000c520080400000000380a2000000000006028804000000e2048030000000650c9104c000000118214023000000000081200808000000000000007000000000001840c0000041320403000000000012038808000000030084209000000000000002400000120380a300000000014943080c00000000008510a0000000012038800000000035041207
  | 7, 92 => 0x43114204c0000000000000a100000000010d028804000000e214843010000006914324c000000000000c81040000043114104c0000000000000a106000004600e018c0400000413204030000000000812008000000000204802090000003841100c04000000000002106000000000010440c0000000038852010000006914324c000000000104402030000000000204428000001a45085300000000010c20080c00000020180a3000000000000300408000000020480201000000008120082400000000000e1040000000000038428000000000806206000000010d0188040000118304853000000003881200c0000000000010c104
  | 7, 93 => 0x28410000000010440209000000010d028800000000021402202000000000043041400000005250c2050000004884008c000000000000c0102000000000020040c00000000010c10500000000c12148040000085304843000000000000028410000011830485300000000000020441000000004340a2010000000000204410000000e204803010000000081200800000000e204803000000010440028c040000012314c4300000000008120082800000000380620100000000000284140000000204802090000000081200804000000e204803000000043081200c000000081200063000000000081018804000000042041202
  | 7, 94 => 0x14943080c00000020180a300000000001203880000000004500e201000000000002840c000000000000000000000001203880000000020180a30000000204c5200c040000000000000060000000806028c0000000000010c10900000000003204140000000000c810600000000001004100000000000c810600000000000184100000099450413000000004884008c00000000003806201000000000000840c000011803806301000000000e02880c00000004340a200000000000010440400000000000e103000000004110080c000001a45085300000000000043040c00000020180a300000000010d204804000000000000000
  | 8, 0 => 0x1840c0000000000c4101000000000021441400000000000210600000000c002880400000000000a10400000000000000180000000000000040000000000000018000000041080200000000000032040c0000000000000030000000000204408000000003884200000000000001840400000000000a10100000000c80088000000000410c9200000000000032040000000000000a101000000000e0088000000000000c0103000000000000840c0000000000c4101000000000002840c000000000006104000000000002840400000000000a107000000000003840c0000000000000040000000000008414000000000002106
  | 8, 1 => 0xc00000000000a10300000000c00288000000000039002000000000000000010000000000040107000000000010440400000000010c102000000000031040400000003148120000000000003004240000000000c8103000000000e0288000000000000851030000000104008800000000000084107000000000003841c00000003200220000000000c901880000000000010c1060000000012038800000000000049101000000000010440c00000000000000a000000000001441800000003148120000000000c9018800000000032002201000000000001840c00000000000a1070000000000008424000000030485200
  | 8, 2 => 0xa01880000000000000a101000000000000002000000000000e1070000000000008404000000000084103000000000032040c00000004100a200000000000032041c0000000008062000000000000018404000000000002106000000000002841c00000000000a1030000000108310800000000000041103000000010002880000000004508120000000000002144040000000000c110100000000003044040000000000c010300000001002148000000000000c8103000000000000002800000003100220000000000840088000000000304062010000000000210420000000000081107000000000002840400000000000610a
  | 8, 3 => 0x3204200000000000c410a00000000c001880000000002000620100000000000384040000000000c8101000000000000840400000000000e1090000000000310404000000000006104000000000032040c000000000000007000000000003841800000000380a2010000000000028414000000000000005000000000002840400000000000210500000000001004100000000000411080000000000000010000000000080106000000010c00880000000002040620000000000c810080000000000388020100000000060288000000000000c01030000000006028800000000000002103000000000e0188000000000000c8107
  | 8, 4 => 0x3841800000000000e10a000000000001840800000000000610200000000003104180000000400062000000000000028404000000000081101000000000a0088040000000000c1101000000000e00880000000000000e1000000000000008424000000031480200000000000030040400000000000a105000000000010040c00000000000e10100000000003104040000000450c1200000000000000840400000003040620000000000c021480400000000000610500000000c12108000000000000c4101000000000043040c0000000000c9101000000000000841000000000000610a00000000000184040000000000c9101
  | 8, 5 => 0x200424000000000002107000000000e00880000000000000a107000000000021441c0000000410c1200000000000a008800000000000000001000000000030041c000000000002105000000000000841c000000000002105000000000010440c000000000006108000000000032040c000000000040103000000000000840c00000000010c103000000000002841400000000380a20100000000c93208000000000000c4101000000000021441c00000000008010800000000000284040000000000c8109000000000e008804000000030406200000000000000840c0000000400842000000000000018418000000000002109
  | 8, 6 => 0x1040088000000000000c0103000000000001840c0000000000c1101000000000031040c000000000040108000000000000840c0000000000c81050000000000420400000000032406200000000000000001400000000480920000000000000000180000000000081010000000000010408000000000006109000000000021442400000004000a200000000000a01880000000000000210700000000123048000000000410c9200000000000001841400000003100a20000000000800188000000000000000040000000000200418000000000080103000000000032040c0000000000c810700000000c0028800000000000002104
  | 8, 7 => 0x1000000003000620000000001000188000000000000000050000000000008410000000000002105000000000e1248040000000048c420000000000002104180000000430402000000000104200800000000000084106000000000e100800000000000084103000000000000841000000000000210a00000000c5028800000000000085104000000000e2048000000000000c8109000000010c018800000000000006107000000000002840c00000000000a1060000000000000004000000000081101000000000001840c0000000200062000000000012038800000000003802200000000000032041000000000000a106
  | 8, 8 => 0x2840c000000003806200000000000020041c000000000000005000000000032440400000003240220100000000003204100000000000021030000000000008424000000000002103000000000002840c000000000000009000000000002841c000000000041107000000000e10480400000000000610700000000002144140000000000c5101000000010c2008000000000000c8107000000000002840400000000004010100000000c402880000000000000e1010000000000204414000000043002200000000001220080000000004300620000000000000184100000000310812000000000000028410000000000006100
  | 8, 9 => 0xc810480000000000008410600000000000284180000000000000090000000000010414000000000085105000000000021040c000000000080104000000000032042400000003000a200000000000001840c00000000000a103000000010800880000000000480a200000000000000840c00000000008510800000000410288000000000000c010100000000c52048040000000000c010900000000852108040000000000c4101000000000030041400000000000000300000000c500880000000000000000500000000c50088000000000000000030000000000008414000000021484200000000000001840c000000000006104
  | 8, 10 => 0x30040c0000000000c5101000000000000000c00000000000000b000000001200880000000000384820100000000003144040000000314c4200000000000021440c0000000000000080000000000038418000000000084105000000000000000c000000000080107000000000e0088000000000000c01070000000000214414000000000002105000000000000840800000000388520000000000122048000000000000c010a0000000000000018000000030006200000000000020440000000000000a10500000000c00288040000000400c9200000000000a018804000000000009101000000000001840c000000000084104
  | 8, 11 => 0x2840000000000000210100000000c502880000000000080a200000000000004840000000000000000100000000000284180000000000c4108000000000032440400000000010c103000000000000841c000000000000005000000000002840c00000000000210500000000000284140000000000c010400000000c420480000000000008010500000000490088000000000000c8107000000000031440400000000000a10600000000004304140000000000021030000000000000028000000000040102000000008500880000000000390820000000000003004140000000048c52000000000000000014000000000002107
  | 8, 12 => 0xe12480000000000008110400000000000000140000000038082000000000108008800000000000000005000000001231480000000000380a200000000004002880000000000008510500000001142048000000000000401010000000000018428000000000006101000000000002841000000000008010400000000002144100000000000491010000000104008800000000000002101000000000000842000000000010c109000000000031040400000004100a200000000000000840c00000000000a10500000000000184180000000000c810600000000c9008800000000003908200000000000002841c00000004100a200
  | 8, 13 => 0xe10080000000000000a10500000000060088040000000000021030000000000028418000000004840200000000000032041400000000000a1090000000000320418000000000006101000000000e214800000000000080103000000000202880000000000000a10100000000000284140000000000000050000000012214800000000000000005000000000e104800000000003806200000000000020441c00000000000000400000000003104080000000048c92000000000100310800000000000000003000000000000001c000000000084105000000000e2048000000000000c41080000000085008800000000000000004
  | 8, 14 => 0x1841000000001040a200000000000e0088040000000000841030000000108010800000000000040107000000000001840c0000000000c41070000000048008800000000000080104000000000002840c000000000040101000000000001841400000000010c103000000000002841400000000000000b00000000840088000000000000401080000000085008800000000003802200000000000002841000000000000a106000000000021440400000000008510300000000002004100000000450c1200000000000a00880000000000000000400000000c001880400000000000a10300000000c1018800000000031002200
  | 8, 15 => 0x1840000000000000a1030000000000028404000000000080104000000000000001000000000000210300000000c9018800000000040006200000000000003840c000000032402201000000000002840c00000000000e101000000000010041800000000000a103000000000e00880400000000008010100000000000084240000000000851090000000100314800000000003904200000000000a01880000000000000e101000000000002841c0000000430092000000000100320800000000000080103000000010021480000000000000e1050000000000320404000000000104100000000000e42080000000000000a105
  | 8, 16 => 0xe21080000000000000210100000000000284140000000000c0105000000000020442400000000488420000000000c8018800000000000041106000000000001840c000000000081103000000000021040c00000000000610900000000c90088040000000000c0104000000000001840400000000000210100000000c91008000000000000061040000000000310420000000000002101000000000e1008000000000410c0200000000000e12080000000000000e109000000000002841c000000000005105000000010432480000000000180a20000000000000084040000000200062000000000000100408000000000085107
  | 8, 17 => 0xc900880000000000080a2000000000012008800000000003806200000000000e018800000000000080104000000000000840c0000000000401030000000000018410000000021002200000000000003841c00000000000a1050000000000210404000000000006104000000000000002000000000380a200000000010420480000000000000610600000000003004200000000000c9101000000000e10480000000000000e10a000000000000841400000000000a10500000000120188000000000000801070000000000100404000000003885201000000000000001c00000004308520000000000001044040000000000c4104
  | 8, 18 => 0x10441400000000000a103000000010c20480000000000010c107000000000001840c000000000002101000000000000000c0000000000411030000000000310410000000000080105000000000000001800000000008110100000000c910480000000000000610500000000c402880400000000480a200000000000000840400000000000e10300000000002044040000000000c010300000000c801880000000004300a2000000000108008800000000000006101000000001202880000000000000000500000000c002880400000000000000400000000000000040000000000c0105000000000020040c000000000000005
  | 8, 19 => 0x21440c0000000000c41050000000000430414000000000006103000000010c21080000000000008010100000000000000140000000304c020100000000c00188000000000214022000000000006028800000000000006107000000000031040c000000003884200000000000021441000000000000610300000000000084240000000304062000000000000100414000000000006102000000001230480000000000000a104000000000e40080000000000080a201000000000031440400000000008410300000000060288040000000000051010000000000000014000000000081101000000000030040c000000030006200
  | 8, 20 => 0x32040800000000000a1030000000000210414000000000000005000000000002840c0000000450412000000000000028424000000000000003000000000032042000000000380620000000000000000180000000000000080000000104008800000000003904200000000000e210800000000040048200000000000002840c000000031481201000000010c0288000000000000c4107000000000030040400000000000a101000000000e02480000000000000e101000000000000001800000000010c100000000000000840c000000000040101000000000000840c000000003884201000000000030040c0000000000c5100
  | 8, 21 => 0x31040400000000000210600000000004304140000000048062000000000002018804000000000040103000000000000841c0000000000c1101000000001232480000000000008010700000000000284140000000000851010000000000028414000000000081105000000000003842400000000000a1030000000000000018000000000000004000000000000840c00000000000000600000000120288000000000000c81090000000081018800000000020006200000000000001841800000000000610500000000122008000000000000061050000000000008404000000040085200000000010c0288000000000000c4103
  | 8, 22 => 0x20441c00000000004110400000000002044280000000210022000000000000100414000000004806200000000000001841c000000000006106000000000043440400000000000a105000000000e20480000000000004110100000000c50088000000000000c410500000000002004140000000000851000000000000000028000000000006102000000000030440400000000000e107000000010c1008000000000420c02000000000000018428000000000085103000000000020440c00000000000a107000000000001840400000003140a201000000000e4108000000000430852000000000000210414000000000002101
  | 8, 23 => 0x300418000000000006107000000000002840c0000000000c810300000000800188040000000000c410000000000000084200000000410c12000000000000204414000000000085100000000000002840400000000000610300000001143148000000000000841030000000012028800000000002802200000000000003841400000000010c10400000000000184100000000000c8105000000000030040c0000000000801010000000002028800000000032006201000000000000000000000003100a200000000000010041400000000010c10500000000c90188000000000038812000000000000008420000000000040102
  | 8, 24 => 0x104008800000000000081104000000000e41080000000003048520000000001002108000000000000c810300000000123008000000000000c4104000000000000000c00000000000a105000000000043040c000000043084200000000000002840c00000001040a20100000000c520080000000000008410100000000000184100000000000c8106000000000001840c000000031481200000000000001440c00000000484120000000000000384040000000000c0104000000000001441400000003040a2000000000100210800000000042040200000000010801880000000000010c10500000000060088000000000000c9101
  | 8, 25 => 0x10c028800000000000085108000000008400880000000000488120000000000c800880400000000010c105000000000000840c00000000008110300000000c40088040000000000c01020000000000008404000000043002200000000000001840c00000003000a200000000000000840c00000000000a109000000000043041400000000480220000000000003204080000000000c510100000000c0028800000000000002104000000000020040c00000004200620000000000c42008000000000000851060000000104200800000000000004105000000000002842000000000000a104000000000021040000000000000e105
  | 8, 26 => 0x2840000000003148120000000000c1028800000000000000004000000000021440c00000000180a20000000000002004040000000039042000000000000200424000000000040101000000000002841c0000000048c92000000000000104414000000001802200000000000003841000000003048520100000000c50288000000000000811050000000000028418000000000084100000000000e41080000000000000e10500000000000284140000000000c41030000000000304404000000000006104000000000032440400000004300a200000000000032040c0000000450c9200000000000e008800000000031480201
  | 8, 27 => 0x10041c000000042006200000000000001840400000000000e10300000000000384040000000000000070000000000104404000000000006104000000000020040400000000004110500000000c80188000000000000c0100000000000002841c0000000000811040000000012320800000000000006105000000000012440400000000000a106000000000001841c00000003100a20000000000000000100000000000841070000000000028428000000000000009000000000030040400000000000e1050000000000014410000000000004103000000000001841800000003100a20100000000c40288000000000000c4107
  | 8, 28 => 0xe008800000000043006200000000000001840c0000000000c8102000000000000000c000000000081103000000000000000400000000000610500000000c531080400000001040a2000000000000310414000000000084103000000010c2008000000000000c410600000000002104140000000000021030000000000038414000000000040101000000000000841000000000004110800000000000084240000000000811060000000000104420000000020406201000000000000000400000000000a10700000000c810480400000000004110900000000123048000000000000061070000000012100800000000000006104
  | 8, 29 => 0x3840400000000000000a000000000000841c000000032005200000000000e02880000000003140a201000000010c018800000000000002103000000000003840400000000010d1010000000000104404000000000048101000000000001840c000000000006107000000000020440c0000000000c4107000000001231080000000000008410300000000000284200000000000041040000000000300424000000000002104000000000001841c0000000000c81070000000000000010000000004880200000000000021040c000000020006200000000000e00880000000001000a20000000000000184140000000000c0106
  | 8, 30 => 0x43040c0000000000c010100000000121008000000000000c0106000000000001840800000000480e2000000000012038800000000000000004000000000002840c000000000084105000000010831080000000000000e10100000000001004040000000000c8103000000000002840400000000380a20100000000002044040000000000851050000000000028424000000003802200000000000032041400000004200620000000000000000140000000000061030000000000214414000000002802201000000000043041c000000000085107000000000e01880000000000000a107000000000000000400000000180a200
  | 8, 31 => 0x3104100000000000061050000000000018428000000000085105000000000000841400000000390820000000001081008000000000038412010000000114204800000000003802200000000000032041c00000000380a200000000000602880400000000000210600000000c40088000000000048c8200000000008500880000000000000a10600000001003208000000000000c01070000000000028408000000000002109000000010831480000000000008110400000000c52048000000000430412000000000000028414000000000002104000000000000841c00000000010c106000000000e214804000000000000009
  | 8, 32 => 0xc9018800000000000081109000000000020040c00000000000a103000000000000000c00000000000e1050000000000018424000000000081103000000000021440c000000000006101000000000010441c00000000008010500000000000084240000000000061010000000000300424000000000040100000000004102880400000000000610900000000c80088000000000324402000000000000214414000000002806200000000000002840c00000000000a103000000000000000c000000000041109000000000001841c00000000000a10500000000004304180000000420c4200000000000001840c000000000040103
  | 8, 33 => 0x1842000000000000e10300000000000000280000000000c01010000000000020408000000021002200000000010420480000000000000000700000000004304180000000324402000000000000028404000000003884201000000000021040400000000000210900000000c8008804000000000006104000000000000001800000000000e10100000000060288000000000000c410300000000003204100000000304c020000000000c402880000000004100a20000000000c900880400000000000e107000000000001842800000000010c107000000000020040c0000000000411040000000041100804000000042041200
  | 8, 34 => 0x31040c00000000000e106000000000032041c00000000000a104000000010c10080000000000000a1040000000000200410000000000002105000000000010440c00000000000210100000000c910480000000000000e10a00000000c10188000000000000851050000000000000028000000000006103000000000002841c000000000000009000000000001440c000000020406200000000000000000400000000380620100000000c901880400000000380220000000000c102880000000000000a1020000000012214800000000003900200000000000000840c00000000000e106000000000032041c000000000000007
  | 8, 35 => 0x104028800000000032040200000000000021440c000000032406201000000000e00880000000000000210100000000000184040000000000021030000000000018414000000000041102000000000e2108000000000000061050000000041028804000000000006101000000000001841400000000000210300000000000000180000000000851070000000000310408000000000084106000000000001840c0000000000c8105000000000001840400000000000610500000000000184100000000000c010000000000c9104804000000000080103000000000002840c00000000000210100000000c90188000000000000c8102
  | 8, 36 => 0x2104140000000000061020000000000028410000000003880200000000000003840000000000180a200000000001201880000000000000e106000000000020440c00000000000a10800000000c40288000000000000000040000000012310800000000004884200000000000000840c00000000010c10500000000812008000000000430802000000000000018414000000021484201000000010432480000000003140a2010000000012008800000000000084107000000000003841c0000000200062000000000000100424000000003802200000000000002841400000000000000800000000000284180000000000c1102
  | 8, 37 => 0x28410000000000041107000000000010440c000000000000006000000000030040400000000000610300000000c81048000000000000801060000000000028408000000000002103000000000002840c00000000000a10500000000000084040000000000c0102000000000031041000000000000a106000000000010040c000000020406201000000000002841800000000000000700000001143048000000000000c410300000000000084080000000000c0101000000004110080000000000390020000000000003104140000000000c81050000000000320414000000003802201000000000001040c000000032006200
  | 8, 38 => 0x310404000000000041103000000000002840c0000000000c8104000000000032041c000000000081105000000000e2048000000000410c9200000000000000001800000000000210400000000004304240000000000c4105000000000003842400000000388120100000000003204040000000314c42000000000000028424000000000040105000000000021440c0000000000401010000000006028804000000042006200000000000003840000000003100a201000000000001840c000000000006100000000000030040c00000000000210100000000c42008000000000430402000000000000008414000000000084103
  | 8, 39 => 0x32040400000000000000a000000000000001400000000080a2000000000000310404000000000000009000000010402880000000000000a100000000000032041c000000000084107000000000010040c00000000008010a000000000e028800000000041002200000000000e0288040000000420c520000000000000284240000000000c510100000000000084100000000000401090000000000304404000000003908200000000000001840400000000000a1010000000000038414000000032041200000000000e100800000000020406200000000000021441c00000000000a109000000000000841c000000000000001
  | 8, 40 => 0x10041c0000000304c0200000000000002840c00000000010c10700000000001004280000000000c810500000000c4204800000000000002109000000000010440c000000000006105000000010c214800000000000006101000000000021440c0000000048c420000000000c40088000000000038402000000000085008800000000000008101000000000032040c0000000450c92000000000000000020000000003885200000000000e200800000000042006200000000000000001c000000000002108000000000030042000000000000a105000000000043041000000000000610100000000c1210804000000000040107
  | 8, 41 => 0x10c0088000000000000c81070000000000000014000000000041103000000000003840400000003140a200000000000a00880000000000000a109000000000000000c00000000280220000000000850088040000000000061010000000000008414000000000006105000000000020041c00000000000000400000000000184140000000038802000000000108104800000000000000003000000000003840400000002048020000000000003204180000000324c8200000000000002841c0000000450c1200000000000032041000000000000e109000000000020440c00000000000a105000000000010441c000000004880200
  | 8, 42 => 0x1004100000000000401010000000000000010000000004840200000000000031040c00000000000a1060000000000320404000000004802200000000000020441400000000010d101000000000e02880000000003040a200000000000001840c0000000430062000000000000320418000000021002200000000001201880000000000000a1010000000000038410000000003880201000000000002842000000004308420000000000000000280000000430852000000000108104800000000003884200000000000021442000000000000a107000000000e2048000000000000c11010000000104324800000000000080103
  | 8, 43 => 0xc90088000000000000401030000000000100420000000000041102000000000000841000000001040a200000000000021040c0000000028022000000000000028404000000021002201000000000000840400000001000a201000000000020440c0000000038062000000000000000014000000000002101000000000032041c00000000380a200000000000002841c0000000048412000000000000200408000000032006200000000000002842400000000480a200000000010831080000000000080a200000000000e028800000000000006105000000000000840000000000000e107000000000e20480000000003040a201
  | 8, 44 => 0x810188000000000450412000000000000018410000000000000003000000000e4208000000000000c0109000000000043440000000000000000900000000c901880000000000000a104000000001203880000000000000e1080000000000214404000000000081109000000000003840000000000000a109000000000002841c0000000410c02000000000000214404000000000040103000000000043041400000000000610500000000c420480000000000000a10a000000010c21080000000000000a1030000000012028800000000021402200000000000010441400000000004110800000000c4020800000000042040200
  | 8, 45 => 0x840088000000000420c1200000000000000840c0000000000c01010000000000000014000000000000001000000000010040c00000000004110900000000c91008040000000000c410100000001083108000000000000c0106000000000020042400000000004010a00000000000084040000000000401090000000100028800000000000085105000000008101880000000000000a1010000000000038404000000000000004000000000e01880000000000000a103000000000002840c000000000084105000000000e0288040000000000c0108000000010c00880000000004300a200000000000e204800000000000000005
  | 8, 46 => 0x1840400000000001210000000000c5200800000000000085106000000000001840c00000000000a1030000000000100404000000042040200000000000e210804000000000081102000000000002841400000004000a200000000000000840400000000388120100000000c9010800000000000084109000000000001840400000000010c10700000001083048000000000000041030000000000048408000000000040101000000000021440000000000000000a000000000030040c00000000000e105000000000001840c00000000000a104000000000e2048000000000000841010000000002028800000000003881200
  | 8, 47 => 0x2842400000000008010400000000000384100000000000021020000000000200424000000032006200000000000021041400000000000a100000000000021040000000000000a103000000010c104800000000000085104000000000021441000000004300a2000000000000210410000000000040109000000010001880000000000000000300000000000000240000000000061050000000000314404000000000080103000000000001841c0000000000c010100000000000000180000000000021040000000000038404000000000084104000000000e01880400000003008420000000000003204100000000410c9200
  | 8, 48 => 0xe028804000000000085102000000000201880000000000000a1050000000000000010000000030484200000000000002840c0000000048c520000000000004304240000000000c0104000000000021440400000000000a100000000000021440400000004300a20000000000c400880000000000080620000000001043208000000000000c4109000000000003841c000000000000004000000000020440c0000000000c5100000000000000001c0000000001081020000000012100800000000000084105000000000010440800000000000a100000000000030041400000000000e10a000000000e410800000000003904200
  | 8, 49 => 0x204410000000000084101000000001220080000000000004110100000000001004140000000000c0103000000000e018800000000000000004000000000000000c0000000000851050000000000008414000000000000003000000000000002400000001000a20000000000000000100000000450c1200000000000043041000000000010c105000000000002841000000000000510300000000c4204800000000045085200000000000010042000000000000a103000000000000001400000000000a105000000000000841400000000008110300000000000000180000000000851050000000000204408000000000006108
  | 8, 50 => 0x104408000000003840200000000000032040400000003204020100000000c80148000000000048c8200000000010032080000000000380a200000000000002841c00000002048020000000000000184040000000314812000000000000028410000000021002201000000000020441400000000000a1060000000000028404000000000084102000000000000001c000000000081103000000000003842400000004300a20000000000002144040000000048c820000000000003204140000000000c410a000000000043042400000000000a1070000000006028800000000000084101000000000000841400000000000a105
  | 8, 51 => 0x3842400000000000a107000000000000001c00000000000000300000000002104040000000000411070000000114038804000000000000004000000000031040c00000000010c104000000010032080000000000008510500000000000084100000000000061060000000108018800000000043080200000000000002440400000003148120000000000000284240000000000061080000000000100400000000032440200000000000002840400000000010c10300000000c502880000000000000e10400000000000384140000000000c410700000000002004040000000039082000000000000028424000000000000003
  | 8, 52 => 0x21041000000000000610400000000410288000000000000061060000000000028428000000003885200000000000002841400000000000610300000000120388000000000314802010000000000200418000000000000004000000001203880000000000008510300000000000184040000000000c8107000000000000840c0000000000061090000000114304800000000000006101000000000032440400000004304020000000000c81048000000000000061050000000000100418000000000084102000000000002841400000000004010900000000c11248040000000000401030000000000008404000000000006107
  | 8, 53 => 0x21040c0000000000c0101000000000e100800000000003802200000000000010041c000000000000004000000000003841000000000388520000000000c121480000000000380a201000000000001840c00000000000610500000001043208000000000000c4101000000000e4208000000000000c11010000000000320424000000003880200000000000000001800000000000a100000000000003840c000000031081201000000011402480000000000380a20000000000c130080000000000000a10100000000c40088000000000000c910100000000000184140000000314c4200000000010c204800000000004880200
  | 8, 54 => 0x840c000000000000008000000008101880400000000180a2000000000000124404000000031002200000000000e10080000000000000e1000000000000204404000000020406200000000000e21080000000000000a103000000010c20080000000000000e100000000000043041400000000388520000000000003104140000000048062000000000000320410000000032002200000000000e02880000000000000a105000000000e018804000000000084105000000000030040400000000000e106000000000031040c0000000048c4200000000000020440400000000000000a0000000000038404000000000006104
  | 8, 55 => 0x2841c0000000420c1200000000000e21080000000000004010900000000c810080400000000000000400000000000184040000000000c81040000000000038404000000000002103000000000010440c00000004000a200000000000a01880400000000004010500000000c8104800000000000000006000000000001840c0000000000411090000000000008404000000000040104000000000004840000000000000a1040000000000200428000000000040109000000000020041400000000000210500000000c81008000000000000c41070000000000028420000000000004103000000000001840c000000000041101
  | 8, 56 => 0x430418000000000108100000000000040040000000000004110300000000c12148000000000038802000000000108104800000000031480201000000000031041c000000000080103000000000040040000000000000610a000000000001840400000000000e101000000000003840400000003000a200000000000000000c000000000000009000000010c204800000000000040103000000000e008800000000000081104000000000002841c00000004100a2000000000000028400000000000000001000000000e420800000000003840200000000010400880000000000000e10500000000c0210800000000000080105
  | 8, 57 => 0x100310800000000002806200000000000e1008040000000000000040000000000038404000000000006104000000000000841000000000000610300000000000184200000000000c410500000000001004040000000000061030000000000008410000000000006109000000000032040c00000000080620000000000002144040000000000c8109000000000021040c0000000450c12000000000000028418000000031002200000000000e100800000000021002200000000000e20080400000003240620100000000c1210800000000000080109000000000e214800000000004806200000000000e1008000000000000c8101
  | 8, 58 => 0x2840c00000000380a200000000000021440400000000000e1000000000000008414000000045085200000000000e028800000000003806200000000000002842000000000000a10800000000c121080000000004108120000000000002144240000000204802000000000000038418000000021002200000000000e2108000000000000c4100000000010c01880000000000000000100000000000084100000000000000050000000000018414000000030484200000000000a0188000000000204062000000000104324800000000000006101000000000003840400000000000a10600000000001004080000000000c8104
  | 8, 59 => 0x10c028800000000000002105000000000021040400000000000a106000000000021040c000000000084103000000000020042000000003000a201000000000032040800000000000e1020000000000214414000000010440200000000000010041400000000004010500000000c901880000000000180a201000000000010042000000000000a10300000000c901880000000000008410900000000850088000000000000000030000000000200404000000000085104000000000a0188040000000000c41030000000012028800000000000085104000000000041040800000000010c10000000000000104100000000000c8107
  | 8, 60 => 0x2104140000000124022000000000000214400000000000085109000000000e20480000000000080620100000000000184040000000048812000000000000008408000000000100100000000000021040c000000043006200000000000402880000000000000a105000000000020041000000000380620000000000c800880000000000010810000000000120288000000000314022010000000000300410000000020406200000000000030040400000000000210300000000c5310800000000000085105000000000002840800000003108120000000000000184280000000000c51000000000000100414000000000000001
  | 8, 61 => 0x2840c00000000380620100000000002044040000000048c92000000000040028800000000000006103000000000020441c000000000006109000000000001840400000000000e1020000000000204408000000000005105000000004102880400000000000a10100000000000184000000000420402000000000000000004000000021402200000000000000002000000000000a10300000000000284040000000000041060000000000314404000000002806200000000000001841000000000380a200000000000002842000000000480a200000000000e0188000000000400842000000000000028410000000000002103
  | 8, 62 => 0x10c1008000000000000000030000000006028800000000041081200000000000030040400000000000210100000000060288040000000000c010900000000840088000000000410c8200000000000e42080000000004300a20000000000122048000000000000401010000000000028420000000000000003000000008500880000000000008510100000000c801880000000000000a1030000000000000014000000012002200000000000021040000000000000000900000000c81008000000000038022000000000000210424000000032441200000000011430480000000000000a1030000000000320418000000000000004
  | 8, 63 => 0x10c0288000000000000c8102000000000010040400000000008510900000000800188000000000000061030000000041100804000000000085101000000000043040c00000000000e104000000000000001000000000010c103000000000031041c000000000040104000000000000840c00000000010d101000000000002840c00000000000a105000000000e21480000000003244020000000000002004240000000000c4106000000000031041800000004000a2000000000000300420000000000006107000000000002842400000000000a105000000000602880400000004308520000000000000284000000000400c8200
  | 8, 64 => 0x8120080000000000480e200000000011430480000000004300a200000000000002840c0000000000c4103000000000e21080000000000010810000000001080188000000000000c0107000000004102880000000000390820000000000000000100000000048062000000000000100414000000043084200000000000001841c0000000420022000000000000310410000000042041200000000000031041800000000000610200000000c021080400000000000a1030000000000038404000000000084109000000004002880000000001000a200000000000e1008000000000000811040000000000028414000000000049101
  | 8, 65 => 0x10c204800000000000084102000000000020440c000000000041105000000010c100800000000000006107000000000003840400000000000210400000000c9100800000000000006103000000000002841c00000000388520100000000002044100000000000c010100000000000284100000000048c4200000000000003840400000000000e101000000000021440000000000000a102000000000003840c00000000000e1030000000100320800000000003885200000000000021042400000000000a102000000000021040400000000000a101000000000043041400000000008510a000000000003840400000000000e101
  | 8, 66 => 0x21440c0000000000811020000000000000000000000000081102000000000010440c000000000000001000000000031040c000000000006106000000000e21080400000000000a1010000000000038404000000000041103000000000020440c00000000480e2000000000000430410000000021002200000000000000000c00000000000a10300000000002104000000000000c0102000000000002841800000001040a200000000000002840400000000000e105000000000e2108000000000210022010000000000204424000000021002200000000000020040c00000000008410a000000000002841400000000180a200
  | 8, 67 => 0xe200804000000000006103000000000003841000000000010c103000000000000001000000004300620000000000c42048000000000048062000000000000028400000000000002101000000000e400800000000000002105000000000002840400000000010c1050000000114204800000000000084101000000000020442800000000380620100000000c93208000000000048c020000000000000284200000000000c5101000000000002842400000000008510100000000004344040000000000061050000000000320410000000020406201000000000e0088000000000000c0103000000000020440400000000000a107
  | 8, 68 => 0xe0288000000000324062000000000000204404000000000006103000000000021440c00000000480a200000000000000002000000000000e1000000000000204404000000003908200000000000002840000000000000e105000000010c018800000000030084200000000000020041c00000000480a2000000000000320424000000000084103000000000002840000000000000e100000000000e20480400000000000a109000000000032040c000000000000006000000000000002c00000000010c1080000000000028410000000032041200000000000002840c00000000008510600000000c8100800000000000000004
  | 8, 69 => 0x1004080000000048c020000000000c1028800000000000080107000000000002840c000000000081101000000000031040c000000032040200000000000003840400000003240620100000000120188000000000008062000000000000018414000000000006103000000000020441800000000000210600000000c4008800000000003840200000000001220480000000000000e108000000000002841c0000000000c81090000000000028418000000003885200000000000000000c00000003108020000000000121008000000000000021070000000000018404000000000000002000000000000841800000000000e103
  | 8, 70 => 0x31040c0000000000c81050000000081018800000000003885200000000010c0288000000000300842010000000012214800000000000040101000000000000001400000003148120000000000004304240000000000021010000000108018800000000003908200000000000e028800000000004840200000000000030440400000000000210300000000000000240000000000c810400000000002104240000000000000090000000000214408000000043006200000000000000000400000000000a103000000000000840c00000000000e100000000000002841800000003140a200000000000000840c000000000006100
  | 8, 71 => 0xe018804000000000000007000000000e01880000000000010c10900000000c91048000000000000c810900000000003104040000000000021010000000000324404000000000041102000000010c2048000000000000c81080000000000028404000000004881200000000000e018800000000000084101000000000032042000000000000610400000000c8018800000000000084104000000000032040c00000000000a1050000000081018800000000000041108000000000030440400000000000000a000000010c02880000000000010c103000000000e00880000000000000a1040000000000028418000000000085101
  | 8, 72 => 0x1c0000000000801030000000000204404000000043040200000000000020040c0000000000491010000000000324404000000000000002000000000010440c00000000000a1040000000000310410000000021402200000000000010440c0000000000c410300000000c81008000000000000c510000000000003004100000000000021080000000000214424000000003841200000000000000840c000000000000009000000000010041c0000000000c1101000000000010041c00000000000e103000000000043042400000000000a107000000000000001c00000000010c1060000000000104410000000000049101
  | 8, 73 => 0x12204800000000020006200000000000021041800000000384020000000000c81008040000000000000080000000084008800000000000000009000000000001841800000000000a10100000001000288000000000430852000000000000100414000000000006103000000000010440c0000000048c8200000000000010440c00000000000a10000000000003004140000000204802000000000000028424000000021402201000000000002841000000000000e109000000000002840c00000000010c103000000000e018800000000003904200000000000e41080000000000000a1030000000000038418000000000041101
  | 8, 74 => 0xe410800000000003840201000000000e028800000000000081103000000000043040c00000002048020000000000003044040000000000c8103000000001232080000000004300a200000000000021040c00000000480e200000000000001841000000000000000b000000000e41080000000000004110400000000000384080000000000c51010000000000430410000000000040101000000000003840c000000042041200000000000010041800000000000e101000000008400880400000000000210100000000000184080000000000c8102000000000020440c00000000000a105000000000021440c000000000006106
  | 8, 75 => 0x1841000000000000a10a0000000012038800000000000084103000000000010441400000000000e103000000000e2148000000000000c110000000000000384080000000048402000000000000430414000000000000003000000000010440c000000000041107000000000001840400000000000e1010000000000028404000000000041103000000000003842000000000004010100000000000384100000000000401010000000000028424000000000002104000000000010040400000000000a10100000000c502880000000003244020000000000000000080000000450812000000000000000004000000000041105
  | 8, 76 => 0x201880000000000000610100000000001004040000000000c41010000000000214404000000003806200000000000031040c0000000310812000000000012018800000000003884200000000000021440000000004500e201000000000010440400000000480e200000000000003840400000000380a201000000000000002400000000000000a000000000020040c000000020406201000000010c20480000000000000a10000000000c0210800000000000006104000000000020041400000000380a2000000000000434404000000000081101000000000000001000000000004110500000000000384040000000420c5200
  | 8, 77 => 0x10042400000000010c10900000000840088040000000000c010900000000002144040000000028062000000000000000024000000030084200000000000032042400000000380620100000000000084100000000000c8104000000010c01880000000000004010100000000002044040000000048c1200000000000e21080400000000000e101000000000002840c0000000000c8106000000000000002400000000000e101000000000201880400000000008110900000000000000140000000410c0200000000000031040400000000000000000000000c420080000000000000a1030000000000000014000000032441200
  | 8, 78 => 0xe02880000000000000000b000000000021040000000000000000600000000002044100000000000c8101000000000031041400000000000000a000000000002842400000004500e201000000010c01880000000000000e10200000000000284080000000000c0107000000000e018804000000000002103000000000020040c00000003108020100000000c9018800000000003908200000000000021440c00000003008420000000000004304180000000000000030000000000300410000000000806200000000000000000800000000000e101000000000032040c0000000000061010000000012204800000000000081103
  | 8, 79 => 0xe2048000000000314802000000000000304404000000000002103000000000002842800000000000e101000000010c204800000000000000003000000000003840400000000000e108000000008101880000000000000a1020000000000000020000000000000003000000000000000400000000000e109000000001231480000000000000e10100000000001004140000000450c1200000000000002840c000000000000004000000000021040c0000000048c820000000000000384180000000000061000000000000038404000000000012100000000004110080000000000010c108000000000e420800000000003841200
  | 8, 80 => 0x10442400000000000000a000000000043041400000000000e101000000010430480000000000004010300000000123208000000000000c5101000000000032041c000000003881200000000000032041800000000390820000000000c402880400000000010c108000000000002841000000000008110a000000000020040400000000000a107000000010810480000000000000210300000001141048000000000000c41050000000000028404000000000002100000000000010441400000000380a20000000000000184180000000000c010800000000120388000000000000000030000000000038404000000000004104
  | 8, 81 => 0x3840800000000000000a000000000002840c00000000010c109000000000002840c000000000002105000000000000001c00000003140a2000000000000028410000000045081200000000000030042800000000000a1020000000000200428000000000002105000000008120080000000000008010000000000001004040000000000c8108000000001203880000000000008010600000000000384140000000420412000000000000210410000000021402200000000000000840c00000000388120100000001081008000000000000c81050000000000204404000000003881200000000000010041400000000004110a
  | 8, 82 => 0x10440c00000000000a101000000000e200800000000045041200000000001232480000000000000a105000000000020441000000000480e2000000000000214414000000000085107000000000001840c0000000000811010000000000434400000000000000003000000000010042800000000000a108000000000032041400000000000a101000000000010040c0000000320412010000000000000020000000000085100000000000003842400000000000a101000000000002840c0000000000c810500000000000084080000000000411080000000114314800000000021402200000000000602880000000000000a105
  | 8, 83 => 0x11430480000000000488120000000000c520480400000000000000100000000000384040000000000021030000000000028404000000000041106000000000010041800000000000a1090000000000048400000000032041201000000000031040400000000000e101000000000043040c000000021002201000000010c2048000000000314c4200000000000e018804000000000002103000000000010442400000000000000400000000c810480000000000004010300000000003004140000000000000030000000012204800000000021402201000000000010440c0000000038022000000000000210410000000000000003
  | 8, 84 => 0x38408000000042041200000000010c01880000000000000e102000000000032040c00000003140a200000000000e204804000000000000003000000001202880000000000000e107000000000e2048000000000000c010600000000000184280000000000411080000000000000018000000000040103000000000002841000000000000a10a000000000003840800000000380a200000000000020442800000000010c107000000000002842000000000008510a00000000120388000000000000021030000000006028800000000043081200000000000000840c000000004806200000000000002840400000000000e103
  | 8, 85 => 0x38400000000000000003000000000000000800000000380a2000000000000028414000000045041200000000000043040c000000000041107000000008001880000000000008110300000000003204100000000000c810500000000003144040000000000c4107000000000004840000000000000e100000000000010042400000000001210200000000000000280000000304842010000000000028424000000000080101000000000003840800000000000000300000000c13008040000000000c810400000000c50288000000000000811040000000000214410000000003802200000000004002880400000000000a104
  | 8, 86 => 0x21440400000000000a103000000000e02880000000000480e200000000010420080000000000000e100000000000002840c00000000380a200000000000602880000000000000a103000000001231480000000000000a10900000001002108000000000210022010000000000038414000000003885200000000000e02880000000000180a201000000000002842800000000000a10a000000000002841000000000000e101000000000e0288000000000048c5200000000000020040400000000010c100000000000002841000000000010c105000000000010440c00000000000a103000000000001840400000000000e103
  | 8, 87 => 0x384040000000048c52000000000000430410000000020480200000000001203880000000000480e200000000010c0288000000000450412000000000000314404000000000041101000000011432480000000000000000400000000c531080400000003204120100000001140388040000000039082000000000000048400000000000080102000000000020040400000000000a10000000000000084100000000000c4104000000000000000000000000480e20000000000000000280000000000c8105000000008400880400000000000a102000000000e02880400000000000a105000000000003840800000000380a200
  | 8, 88 => 0x28408000000000000005000000000002840c00000000380a20000000000c420480000000000480a2000000000012038800000000003806201000000000602880000000000004110900000000003204100000000000c8105000000000010440400000000000e103000000000000000000000000180a200000000000000840800000000000a103000000000043040c00000004300a2000000000000214400000000000012100000000001203880000000000000e104000000000010040c0000000000801030000000000430400000000000041101000000000031040c000000020480201000000000003840400000000000a101
  | 8, 89 => 0x480e200000000000003840400000000000e101000000001203880000000000480e200000000000003840800000000000e100000000000003840000000000480e2000000000000038424000000003806201000000000002840c0000000210022000000000000314404000000000000003000000000010440400000000000000a000000001203880000000004204120000000000003244040000000000c41040000000000000014000000021002200000000000e2048040000000000061040000000012038800000000000000005000000001202880000000000000e101000000000032040c000000000080101
  | 9, 0 => 0xc0000000000021000000000000038400000000000000007000000000000000c000000000000003000000000000001c000000000000003000000000000000800000000000e100000000000000000c000000000081100000000000000840000000000000000400000000003004000000000000c9100000000000001840000000000000e10000000000002104000000000000c810100000000000000000000000000000070000000000018404000000000000008000000000000840000000000000a100000000000002840000000000000210100000000000000200000000000000080000000000000010000000000084100
  | 9, 1 => 0x1c000000000000007000000000002440400000000000e10000000000000384000000000001001000000000000200400000000000000007000000000000000c000000000002100000000000003840000000000004010000000000000000240000000000c810100000000000000100000000000c9101000000000031040000000000000000700000000003044000000000000000050000000000400400000000000000003000000000000000c000000000000009000000000032040000000000000000500000000000384000000000000c4101000000000000002400000000000000a0000000000000020000000000002101
  | 9, 2 => 0x841000000000000324400000000000000009000000000031040400000000000000300000000004304000000000000000050000000000100400000000000085100000000000032440000000000000a1000000000000314400000000000000000000000000042040000000000000000a0000000000314400000000000081101000000000020440000000000000a10000000000000000080000000000c41000000000000018404000000000000008000000000040040000000000000000600000000000000280000000000c11010000000000000018000000000000001000000000000000800000000000e101
  | 9, 3 => 0x840400000000000000500000000001004000000000000000030000000000320400000000000000004000000000041040000000000000000500000000004104000000000000c010000000000001044000000000000401010000000000000014000000000000007000000000001840000000000010c100000000000000001c000000000006100000000000000000c0000000000c9100000000000000002400000000000000100000000002004000000000000c1100000000000020040400000000000000300000000000284000000000000021000000000000000004000000000000007000000000030440400000000000000a
  | 9, 4 => 0x1c00000000000e1010000000000000024000000000000001000000000000000c000000000000003000000000000002400000000000610000000000000000180000000000c41000000000000210400000000000002100000000000000001c00000000000000600000000004104000000000000000010000000000048400000000000085100000000000000000c000000000000007000000000000000400000000000000500000000000000080000000000c410000000000001004040000000000c8100000000000010040000000000000e10000000000000384000000000000121000000000000310400000000000080100
  | 9, 5 => 0x240000000000c5100000000000000001c00000000000000a00000000000000100000000000801000000000000028404000000000000000000000000002840000000000001210000000000000000140000000000000010000000000000004000000000000001000000000003840400000000000e100000000000000002000000000000a1000000000000000004000000000041100000000000002840000000000000000a000000000000001000000000000610100000000003204040000000000000020000000000420400000000000000004000000000000002400000000010c100000000000000000c000000000000007
  | 9, 6 => 0x2400000000000000100000000002144000000000000c51010000000000028400000000000040101000000000041040000000000000000500000000004204000000000000c5100000000000000001800000000000000100000000000184040000000000000010000000000018400000000000012100000000000000000400000000000000500000000004004000000000000000000000000000018400000000000000001000000000000000c00000000000e1000000000000000024000000000000004000000000032040000000000000000900000000004304000000000000121000000000000410400000000000000001
  | 9, 7 => 0x4104000000000000121000000000000204400000000000000008000000000000000c00000000000a100000000000000001400000000000a1000000000000038404000000000006100000000000030040000000000000e100000000000000000400000000000e10000000000000000280000000000061000000000000310400000000000000003000000000003840000000000010c100000000000001840000000000000000400000000000000100000000000811000000000000324400000000000084101000000000004840000000000008410000000000004304000000000000851010000000000000004000000000000001
  | 9, 8 => 0x14000000000000005000000000000000c0000000000c11000000000000038404000000000000009000000000000000400000000000e1000000000000314404000000000000003000000000000002000000000000000400000000004204000000000000c810000000000004304000000000000411010000000000204400000000000012100000000000000002400000000000000600000000004304000000000000000010000000000028404000000000000003000000000002840000000000010c100000000000004840000000000000000300000000002144000000000000000010000000000000010000000000040100
  | 9, 9 => 0x4000000000000003000000000000000000000000000000200000000000000040000000000000000000000000000004000000000000007000000000043040000000000000e1000000000000018400000000000000003000000000020440000000000000a10100000000003244000000000000811000000000000000004000000000000000000000000020440400000000010c100000000000003840400000000010c100000000000000000400000000000e10000000000000484000000000000000090000000000320400000000000000006000000000000000000000000000e1010000000000000014000000000081100
  | 9, 10 => 0x24000000000012100000000000000002800000000000e1000000000000000004000000000000009000000000000000400000000000000100000000000000080000000000000010000000000038400000000000000006000000000000000800000000000e1000000000000000024000000000000003000000000003840400000000000000000000000000384000000000000000040000000000000028000000000000009000000000000000400000000000e1000000000000430400000000000000000000000000000002400000000000000100000000000384000000000000c5100000000000000001400000000000e100
  | 10, 0 => 0x1000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_18 roots_18 10 s ws hint
  | 1 => checkCutEntry dom_28 roots_28 9 s ws hint
  | 2 => checkCutEntry dom_38 roots_38 9 s ws hint
  | 3 => checkCutEntry dom_39 roots_39 8 s ws hint
  | 4 => checkCutEntry dom_43 roots_43 8 s ws hint
  | 5 => checkCutEntry dom_44 roots_44 8 s ws hint
  | 6 => checkCutEntry dom_45 roots_45 8 s ws hint
  | 7 => checkCutEntry dom_46 roots_46 8 s ws hint
  | 8 => checkCutEntry dom_47 roots_47 8 s ws hint
  | 9 => checkCutEntry dom_48 roots_48 8 s ws hint
  | 10 => checkCutEntry dom_32 roots_32 7 s ws hint
  | 11 => checkCutEntry dom_49 roots_49 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 62 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 5 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 5 ys) ys = true) : ¬ RunD dom_50 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_18 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_28 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_38 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_44 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_46 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_48 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_49 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_50 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_50 == dom_50) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 5 zs symsG zs (hk 5 zs)
theorem ori_ok {u ys} (h : RunD dom_50 goalM u ys) : RunD dom_50 goalM u (ori ys) :=
  pickMin_runD 5 ys h symsG ys (hk 5 ys) symsG_ok h

def Z (s : Nat) := bar dom_50 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 5 pool6G cutHitH s
theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)
theorem z3 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_8 : ∀ i, 8 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 8 = true)
theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := range_split z5_0 (z5_8)
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
theorem z6_64 : ∀ i, 64 ≤ i → i < 66 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 2 64 = true)
theorem z6 : ∀ i, 0 ≤ i → i < 66 → Z 6 i = true := range_split z6_0 (range_split z6_8 (range_split z6_16 (range_split z6_24 (range_split z6_32 (range_split z6_40 (range_split z6_48 (range_split z6_56 (z6_64))))))))
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
theorem z7_136 : ∀ i, 136 ≤ i → i < 142 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 136 = true)
theorem z7 : ∀ i, 0 ≤ i → i < 142 → Z 7 i = true := range_split z7_0 (range_split z7_8 (range_split z7_16 (range_split z7_24 (range_split z7_32 (range_split z7_40 (range_split z7_48 (range_split z7_56 (range_split z7_64 (range_split z7_72 (range_split z7_80 (range_split z7_88 (range_split z7_96 (range_split z7_104 (range_split z7_112 (range_split z7_120 (range_split z7_128 (z7_136)))))))))))))))))
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
theorem z8_56 : ∀ i, 56 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 56 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_64 : ∀ i, 64 ≤ i → i < 72 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_72 : ∀ i, 72 ≤ i → i < 80 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_80 : ∀ i, 80 ≤ i → i < 88 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_88 : ∀ i, 88 ≤ i → i < 96 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 88 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_96 : ∀ i, 96 ≤ i → i < 104 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_104 : ∀ i, 104 ≤ i → i < 112 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 104 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_112 : ∀ i, 112 ≤ i → i < 120 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_120 : ∀ i, 120 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 8 120 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_128 : ∀ i, 128 ≤ i → i < 135 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 7 128 = true)
theorem z8 : ∀ i, 0 ≤ i → i < 135 → Z 8 i = true := range_split z8_0 (range_split z8_8 (range_split z8_16 (range_split z8_24 (range_split z8_32 (range_split z8_40 (range_split z8_48 (range_split z8_56 (range_split z8_64 (range_split z8_72 (range_split z8_80 (range_split z8_88 (range_split z8_96 (range_split z8_104 (range_split z8_112 (range_split z8_120 (z8_128))))))))))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_0 : ∀ i, 0 ≤ i → i < 8 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_8 : ∀ i, 8 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 8 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_16 : ∀ i, 16 ≤ i → i < 24 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_24 : ∀ i, 24 ≤ i → i < 32 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_32 : ∀ i, 32 ≤ i → i < 40 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_40 : ∀ i, 40 ≤ i → i < 48 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 8 40 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z9_48 : ∀ i, 48 ≤ i → i < 55 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 48 = true)
theorem z9 : ∀ i, 0 ≤ i → i < 55 → Z 9 i = true := range_split z9_0 (range_split z9_8 (range_split z9_16 (range_split z9_24 (range_split z9_32 (range_split z9_40 (z9_48))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z10_0 : ∀ i, 0 ≤ i → i < 8 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z10_8 : ∀ i, 8 ≤ i → i < 12 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 8 = true)
theorem z10 : ∀ i, 0 ≤ i → i < 12 → Z 10 i = true := range_split z10_0 (z10_8)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z11_0 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := z11_0
theorem checked (s : Nat) (hs : s ≤ 11) : ∀ i < NN s, Z s i = true := by
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
  · exact fun i hi => z11 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_50 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 7 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : RunD dom_50 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_50 roots_50 goal_50 12 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_50 goal_50 := by
    have h0 : isConstB dom_50 goal_50 = false := by decide +kernel
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

end S_50

theorem low_50 : Lower dom_50 roots_50 goal_50 12 := S_50.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_50_bits : ∀ r : Fin 64, roots_50.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_50_lt : ∀ r : Fin 64, dom_50.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_50 T)
    (hlow : Lower dom_50 roots_50 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_50, Avail mask256 roots_50 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_50 hfan 0 roots_50 roots_50 rfl hsup0
  set out := (execN C.gates roots_50).getD C.output 0
  have hout : out &&& dom_50 = T &&& dom_50 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_50_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_50 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_50_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_50).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_50)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_50.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_50 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_50).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_50 &&& mask256 = dom_50 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_50 = T &&& dom_50 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_50, hd63, hout]
  have hnc_m : ¬ IsConst dom_50 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_50 roots_50 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_50, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_50 roots_50 0 roots_50 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4276676608 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_50.testBit r.val = fG (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 12 ≤ t :=
  lower_to_circuit6 fG goal_50 12 hT6 (by unfold IsConst; decide) low_50

def wit : Circuit := ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [6, 1]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [8, 4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [3, 14]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [11, 16]⟩], 17⟩
theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 12 := by decide
set_option maxRecDepth 40000 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_12112_aux

theorem PEqualNP.Outside.L_meta_12112 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676608 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676608 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_12112_aux.wit, PEqualNP.Outside.L_meta_12112_aux.wmono, le_trans PEqualNP.Outside.L_meta_12112_aux.wsize (PEqualNP.Outside.L_meta_12112_aux.lower s hs), PEqualNP.Outside.L_meta_12112_aux.weval⟩
