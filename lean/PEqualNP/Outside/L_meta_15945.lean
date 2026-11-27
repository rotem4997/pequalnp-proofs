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

-- The live-wire and cofactor lemmas are adapted from V_meta_9945__k9 and
-- L_meta_13671 (PR 17967, Apache-2.0). The tables below certify this truth table.

namespace PEqualNP.Outside.L_meta_15945_aux

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

section LiveRun
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
end LiveRun

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

def scr (_ _ _ : Nat) (_ _ : List Nat) : Bool := false
theorem scr_no {dm y s : Nat} (pool : List Nat) {zs : List Nat}
    (_ : RunD dm y s zs) : scr dm y s pool zs = false := rfl

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
  let v := ((w ^^^ (w >>> 32) ^^^ seed) * 0xbf58476d1ce4e5b9) &&& 0xffffffffffffffff
  let z := ((v ^^^ (v >>> 29)) * 0x94d049bb133111eb) &&& 0xffffffffffffffff
  (z ^^^ (z >>> 31)) &&& 4294967295

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

def limbWord (xs : List Nat) : Nat := xs.foldl (fun z v => (z <<< 64) ||| v) 0

-- Each cofactor fixes one input and pins inputs that have become irrelevant.
def dom_0 : Nat := 0x5555555555555555
def roots_0 : List Nat := [0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]
def goal_0 : Nat := 0x4444444044404040
namespace Cert0

def xsM : List Nat := roots_0.map (· &&& dom_0)
def goalM : Nat := goal_0 &&& dom_0

def pairsG : List (Nat × Nat) := [(0,6),(2,6),(2,14),(2,22),(2,26),(2,38),(2,42),(2,50),(4,6),(4,14),(4,22),(4,38),(8,14),(8,26),(8,42),(10,6),(10,14),(10,26),(10,30),(10,42),(10,46),(10,50),(10,58),(12,6),(12,14),(12,30),(12,46),(16,22),(16,26),(16,50),(18,6),(18,22),(18,26),(18,30),(18,42),(18,50),(18,54),(18,58),(20,6),(20,22),(20,30),(20,54),(24,26),(24,30),(24,58),(28,14),(28,22),(28,26),(28,30),(28,62),(32,38),(32,42),(32,50),(34,6),(34,26),(34,38),(34,42),(34,46),(34,50),(34,54),(34,58),(36,6),(36,38),(36,46),(36,54),(40,42),(40,46),(40,58),(44,14),(44,38),(44,42),(44,46),(44,62),(48,50),(48,54),(48,58),(52,22),(52,38),(52,50),(52,54),(52,62),(56,26),(56,42),(56,50),(56,58),(56,62),(60,6),(60,26),(60,30),(60,42),(60,46),(60,50),(60,54),(60,58),(60,62)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

def wireAtBlock0 (i : Nat) : Nat := (if i < 8 then [0x4040404040404040,0x4400440044004400,0x4444000044440000,0x4444444400000000,0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5550555055505550].getD (i % 8) 0 else [0x5555000055550000,0x5555505055555050,0x5555555500000000,0x5555555550505050].getD (i % 8) 0)

def wireAt (i : Nat) : Nat := wireAtBlock0 i

def p1AtBlock0 (i : Nat) : Nat := (if i < 8 then [0,0x7f8000,0x3fc0000000,0x1fe0000000000000,0x1fe0003fc07f80fe,(limbWord [0x7fc1f1f1,0xe003e3c007800f00]),(limbWord [0x7ffe01fe,0x3fc0007fff000]),(limbWord [0x7ffff1ff,0xe003ffc007ffff00])].getD (i % 8) 0 else [(limbWord [0x7ffffe00,0x3fffff8000000]),(limbWord [0x7ffffff1,0xe003ffffff800f00]),(limbWord [0x7fffffff,0xfffc000000000000]),(limbWord [0x7fffffff,0xffffe3c007800f00])].getD (i % 8) 0)

def p1At (i : Nat) : Nat := p1AtBlock0 i

def p2AtBlock0 (i : Nat) : Nat := (if i < 8 then [(limbWord [0x5561b5b5,0xeaa76bd2cf959f2f]),(limbWord [0x67b709de,0x934bbd27175f7254]),(limbWord [0x79bbdf09,0x1c53dfbbba662498]),(limbWord [0x7e3defef,0xdf9e123c247848e0]),(limbWord [0x7fffffff,0xffffffffffffffff]),(limbWord [0x5561b5b5,0xeaa76bd2cf959f2f]),(limbWord [0x67b709de,0x934bbd27175f7254]),(limbWord [0x77f7bdff,0xfbeffff7dfdfff7f])].getD (i % 8) 0 else [(limbWord [0x79bbdf09,0x1c53dfbbba662498]),(limbWord [0x7dfbffbd,0xfef7fffbfff7bfbf]),(limbWord [0x7e3defef,0xdf9e123c247848e0]),(limbWord [0x7f7dffff,0xffbf7bfeeffddfef])].getD (i % 8) 0)

def p2At (i : Nat) : Nat := p2AtBlock0 i

def wireSAt (i : Nat) := if i < 12 then wireAt i else 0

def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 12 then (wireAt i,p1At i,p2At i) else (0,0,0)

def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_0 : ∀ i, 0 ≤ i → i < 8 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_8 : ∀ i, 8 ≤ i → i < 12 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 4 8 = true)

theorem wireD_all : ∀ i, 0 ≤ i → i < 12 → wireDOK i = true := (range_split wireD_all_0 wireD_all_8)

theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := wireD_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]

def stateWordDataBlock0 (i : Nat) : Nat := (if i < 8 then [759364,755524,694084,0xa86405,0xb86545,0xa96545,0xa87545,0xa86545].getD (i % 8) 0 else [0x865435,0xa85415,0xa65425,0xa86545].getD (i % 8) 0)

def stateWordData (i : Nat) : Nat := stateWordDataBlock0 i

def stateWord (s i : Nat) : Nat := stateWordData ([0,0,0,0,3,11].getD s 0 + i)

def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n+1, ids => wireDAt (ids % 16) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, ids => wireSAt (ids % 16) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) := let p := stateWord s j; stateWiresD (p % 16) (p >>> 4)
def SS (s j : Nat) := let p := stateWord s j; stateWiresS (p % 16) (p >>> 4)

theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAtDataBlock0 (i : Nat) : Nat := (if i < 8 then [0x6e950527,0x8723290b,0xca55f30f,0x19ff2c7c,0x1ec3b967,0x61f6836b,0x7a84a74f,0xa4ae85ae].getD (i % 8) 0 else [0xdbf53722,0xf39a1c98,0xf5c1bb41,0xa4ae85ae].getD (i % 8) 0)

def htAtData (i : Nat) : Nat := htAtDataBlock0 i

def htAt (s i : Nat) : Nat := htAtData ([0,0,0,0,3,11].getD s 0 + i)

def NN (s : Nat) := [0,0,0,3,8,1].getD s 0
def idxH (s h : Nat) := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (ws : List Nat) := idxH s (hk 0 ws)

def cutHitH (_ _ : Nat) (_ : List Nat) : Bool := false
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_0 goalM u ys := by contradiction

def cutHit (s : Nat) (ws : List Nat) := cutHitH s (hk 0 ws) ws
def ori (xs : List Nat) := xs
theorem ori_ok {u ys} (h : RunD dom_0 goalM u ys) : RunD dom_0 goalM u (ori ys) := h
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_0 goalM u ys := cutHitH_sound h
def pool6G : List Nat := []

def Z (s : Nat) := bar dom_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s

theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)

theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := z3_0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_6 : ∀ i, 6 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 6 = true)

theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := (range_split z4_0 z4_6)

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
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

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

end Cert0
theorem low_0 : Lower dom_0 roots_0 goal_0 6 := Cert0.noCircuit

def dom_1 : Nat := 0xaaaaaaaaaaaaaaaa
def roots_1 : List Nat := [0x8888888888888888,0xa0a0a0a0a0a0a0a0,0xaa00aa00aa00aa00,0xaaaa0000aaaa0000,0xaaaaaaaa00000000]
def goal_1 : Nat := 0xaaaaaaa0aaaaaa80
namespace Cert1

def xsM : List Nat := roots_1.map (· &&& dom_1)
def goalM : Nat := goal_1 &&& dom_1

def pairsG : List (Nat × Nat) := [(1,7),(1,9),(1,11),(1,13),(1,17),(1,19),(1,21),(1,25),(1,37),(1,41),(1,49),(3,7),(3,9),(3,11),(3,15),(3,17),(3,19),(3,23),(3,27),(3,39),(3,43),(3,51),(5,7),(5,9),(5,13),(5,15),(5,17),(5,21),(5,23),(5,29),(5,37),(5,39),(5,45),(5,53),(33,9),(33,17),(33,37),(33,39),(33,41),(33,43),(33,45),(33,49),(33,51),(33,53),(33,57),(35,7),(35,9),(35,11),(35,17),(35,19),(35,37),(35,39),(35,41),(35,43),(35,47),(35,49),(35,51),(35,55),(35,59)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_1 goalM s xsM) : False := by
  have hl := run_len h
  change 5 ≤ s + 1 at hl
  omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

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

end Cert1
theorem low_1 : Lower dom_1 roots_1 goal_1 4 := Cert1.noCircuit

def dom_2 : Nat := 0x3333333333333333
def roots_2 : List Nat := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]
def goal_2 : Nat := 0x2222222022222200
namespace Cert2

def xsM : List Nat := roots_2.map (· &&& dom_2)
def goalM : Nat := goal_2 &&& dom_2

def pairsG : List (Nat × Nat) := [(0,9),(0,17),(1,9),(1,13),(1,17),(1,21),(1,25),(1,37),(1,41),(1,49),(4,13),(4,21),(4,37),(5,9),(5,13),(5,17),(5,21),(5,29),(5,37),(5,45),(5,53),(8,9),(8,13),(8,25),(8,41),(12,9),(12,13),(12,29),(12,45),(16,17),(16,21),(16,25),(16,49),(20,17),(20,21),(20,29),(20,53),(24,9),(24,17),(24,25),(24,29),(24,57),(28,13),(28,21),(28,25),(28,29),(28,61),(32,37),(32,41),(32,49),(33,9),(33,17),(33,37),(33,41),(33,45),(33,49),(33,53),(33,57),(36,37),(36,45),(36,53),(40,9),(40,41),(40,45),(40,57),(44,13),(44,37),(44,41),(44,45),(44,61),(48,17),(48,49),(48,53),(48,57),(52,21),(52,37),(52,49),(52,53),(52,61),(56,25),(56,41),(56,49),(56,57),(56,61),(60,9),(60,17),(60,29),(60,37),(60,45),(60,53),(60,57),(60,61)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_2 goalM s xsM) : False := by
  have hl := run_len h
  change 5 ≤ s + 1 at hl
  omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noCircuit : Lower dom_2 roots_2 goal_2 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_2 goal_2 := by
    have h0 : isConstB dom_2 goal_2 = false := by decide +kernel
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

end Cert2
theorem low_2 : Lower dom_2 roots_2 goal_2 4 := Cert2.noCircuit

def dom_3 : Nat := 0xcccccccccccccccc
def roots_3 : List Nat := [0x8888888888888888,0xc0c0c0c0c0c0c0c0,0xcc00cc00cc00cc00,0xcccc0000cccc0000,0xcccccccc00000000]
def goal_3 : Nat := 0xccccccc0ccc8c8c0
namespace Cert3

def xsM : List Nat := roots_3.map (· &&& dom_3)
def goalM : Nat := goal_3 &&& dom_3

def pairsG : List (Nat × Nat) := [(2,6),(2,7),(2,11),(2,14),(2,19),(2,22),(2,26),(2,38),(2,42),(2,50),(3,6),(3,7),(3,11),(3,15),(3,19),(3,23),(3,27),(3,39),(3,43),(3,51),(10,6),(10,11),(10,14),(10,15),(10,19),(10,26),(10,27),(10,30),(10,42),(10,43),(10,46),(10,50),(10,58),(18,6),(18,11),(18,19),(18,22),(18,23),(18,26),(18,27),(18,30),(18,42),(18,50),(18,51),(18,54),(18,58),(34,6),(34,38),(34,39),(34,42),(34,43),(34,46),(34,50),(34,51),(34,54),(34,58),(35,6),(35,7),(35,11),(35,19),(35,26),(35,38),(35,39),(35,42),(35,43),(35,47),(35,50),(35,51),(35,55),(35,59)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

def wireAtBlock0 (i : Nat) : Nat := (if i < 8 then [0x8888888888888888,0xc0c0c0c0c0c0c0c0,0xc8c8c8c8c8c8c8c8,0xcc00cc00cc00cc00,0xccc0ccc0ccc0ccc0,0xcccc0000cccc0000,0xccccc0c0ccccc0c0,0xcccccccc00000000].getD (i % 8) 0 else [0xcccccccc88888888,0xccccccccc0c0c0c0,0xccccccccc8c8c8c8].getD (i % 8) 0)

def wireAt (i : Nat) : Nat := wireAtBlock0 i

def p1AtBlock0 (i : Nat) : Nat := (if i < 8 then [(limbWord [0x3f,0xff000000000ffc00]),0,(limbWord [0x3f,0xff000000000ffc00]),0x1fff00000,0x1fff00000,0x3ffe00000000,0x3ffe00000000,(limbWord [0x3f,0xffffc00000000000])].getD (i % 8) 0 else [(limbWord [0x3f,0xffffc000000ffc00]),(limbWord [0x3f,0xffffc00000000000]),(limbWord [0x3f,0xffffc000000ffc00])].getD (i % 8) 0)

def p1At (i : Nat) : Nat := p1AtBlock0 i

def p2AtBlock0 (i : Nat) : Nat := (if i < 8 then [(limbWord [0x3b,0x4e2508ac25aff816]),(limbWord [0x12,0x6349d13248d2acab]),(limbWord [0x3b,0x6f6dd9be6dfffcbf]),(limbWord [0x23,0x948e23c57ee5314c]),(limbWord [0x33,0xf7cff3f77ef7bdef]),(limbWord [0x3c,0x18f03df98f09c270]),(limbWord [0x3e,0x7bf9fdfbcfdbeefb]),(limbWord [0x3f,0xe0ffbe01f00e0380])].getD (i % 8) 0 else [(limbWord [0x3f,0xeeffbeadf5affb96]),(limbWord [0x3f,0xe3ffff33f8deafab]),(limbWord [0x3f,0xefffffbffdffffbf])].getD (i % 8) 0)

def p2At (i : Nat) : Nat := p2AtBlock0 i

def wireSAt (i : Nat) := if i < 11 then wireAt i else 0

def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 11 then (wireAt i,p1At i,p2At i) else (0,0,0)

def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_0 : ∀ i, 0 ≤ i → i < 8 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_8 : ∀ i, 8 ≤ i → i < 11 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 3 8 = true)

theorem wireD_all : ∀ i, 0 ≤ i → i < 11 → wireDOK i = true := (range_split wireD_all_0 wireD_all_8)

theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 11 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := wireD_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]

def stateWordDataBlock0 (i : Nat) : Nat := (if i < 16 then (if i < 8 then [42547,42307,34371,484356,676628,549652,545812,615172].getD (i % 8) 0 else [611332,484132,480292,545556,0x753215,0x875315,0x763105,0x754105].getD (i % 8) 0) else [0x853105,0x953105,545556,0x753105,0x753105].getD (i % 8) 0)

def stateWordData (i : Nat) : Nat := stateWordDataBlock0 i

def stateWord (s i : Nat) : Nat := stateWordData ([0,0,0,3,12,20].getD s 0 + i)

def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n+1, ids => wireDAt (ids % 16) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, ids => wireSAt (ids % 16) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) := let p := stateWord s j; stateWiresD (p % 16) (p >>> 4)
def SS (s j : Nat) := let p := stateWord s j; stateWiresS (p % 16) (p >>> 4)

theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAtDataBlock0 (i : Nat) : Nat := (if i < 16 then (if i < 8 then [0x16001e37,0x2137500f,0x2943e65a,0x310e8277,0x4e1cb641,0x56294c8c,0x61607e64,0xa64b71aa].getD (i % 8) 0 else [0xb182a382,0xcc557793,0xd78ca96b,0xf5f5d635,0x4720f9d,0x366b13a9,0x5df3e8a9,0x692b1a81].getD (i % 8) 0) else [0x8ccd33e4,0xde6809b4,0xf5f5d635,0xfdc07252,0xfdc07252].getD (i % 8) 0)

def htAtData (i : Nat) : Nat := htAtDataBlock0 i

def htAt (s i : Nat) : Nat := htAtData ([0,0,0,3,12,20].getD s 0 + i)

def NN (s : Nat) := [0,0,3,9,8,1].getD s 0
def idxH (s h : Nat) := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (ws : List Nat) := idxH s (hk 0 ws)

def cutHitH (_ _ : Nat) (_ : List Nat) : Bool := false
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_3 goalM u ys := by contradiction

def cutHit (s : Nat) (ws : List Nat) := cutHitH s (hk 0 ws) ws
def ori (xs : List Nat) := xs
theorem ori_ok {u ys} (h : RunD dom_3 goalM u ys) : RunD dom_3 goalM u (ori ys) := h
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_3 goalM u ys := cutHitH_sound h
def pool6G : List Nat := []

def Z (s : Nat) := bar dom_3 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s

theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z2_0 : ∀ i, 0 ≤ i → i < 3 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 3 0 = true)

theorem z2 : ∀ i, 0 ≤ i → i < 3 → Z 2 i = true := z2_0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 6 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 6 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_6 : ∀ i, 6 ≤ i → i < 9 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 6 = true)

theorem z3 : ∀ i, 0 ≤ i → i < 9 → Z 3 i = true := (range_split z3_0 z3_6)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_6 : ∀ i, 6 ≤ i → i < 8 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 6 = true)

theorem z4 : ∀ i, 0 ≤ i → i < 8 → Z 4 i = true := (range_split z4_0 z4_6)

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
  scr dom_3 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_3 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noCircuit : Lower dom_3 roots_3 goal_3 6 := by
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

end Cert3
theorem low_3 : Lower dom_3 roots_3 goal_3 6 := Cert3.noCircuit

def dom_4 : Nat := 0xf0f0f0f0f0f0f0f
def roots_4 : List Nat := [0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]
def goal_4 : Nat := 0xe0e0e000e0a0a00
namespace Cert4

def xsM : List Nat := roots_4.map (· &&& dom_4)
def goalM : Nat := goal_4 &&& dom_4

def pairsG : List (Nat × Nat) := [(0,9),(0,17),(1,9),(1,11),(1,17),(1,19),(1,25),(1,41),(1,49),(2,11),(2,19),(2,26),(2,42),(2,50),(3,9),(3,11),(3,17),(3,19),(3,27),(3,43),(3,51),(8,9),(8,11),(8,25),(8,26),(8,41),(8,42),(10,9),(10,11),(10,17),(10,26),(10,27),(10,42),(10,43),(10,50),(10,58),(16,17),(16,19),(16,25),(16,26),(16,49),(16,50),(18,9),(18,17),(18,19),(18,26),(18,27),(18,42),(18,50),(18,51),(18,58),(24,9),(24,17),(24,25),(24,26),(24,27),(24,57),(24,58),(32,41),(32,42),(32,49),(32,50),(33,9),(33,17),(33,41),(33,43),(33,49),(33,51),(33,57),(34,42),(34,43),(34,50),(34,51),(34,58),(35,9),(35,11),(35,17),(35,19),(35,26),(35,41),(35,42),(35,43),(35,49),(35,50),(35,51),(35,59),(40,9),(40,41),(40,42),(40,43),(40,57),(40,58),(48,17),(48,49),(48,50),(48,51),(48,57),(48,58),(56,9),(56,17),(56,25),(56,26),(56,41),(56,42),(56,49),(56,50),(56,57),(56,58),(56,59)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

def wireAtBlock0 (i : Nat) : Nat := (if i < 8 then [0xa0a0a0a0a0a0a0a,0xc0c0c0c00000000,0xc0c0c0c0c0c0c0c,0xe0e0e0e0a0a0a0a,0xe0e0e0e0e0e0e0e,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000].getD (i % 8) 0 else [0xf0f0f0f0a0a0a0a].getD (i % 8) 0)

def wireAt (i : Nat) : Nat := wireAtBlock0 i

def p1AtBlock0 (i : Nat) : Nat := (if i < 8 then [(limbWord [0x3ffc1f,0xc0000000001fc1fc]),(limbWord [0x3fffe0,0x0]),(limbWord [0x3fffe0,0x7fc0ff81ffe00]),(limbWord [0x3fffff,0xc0000000001fc1fc]),(limbWord [0x3fffff,0xc007fc0ff81ffffc]),(limbWord [0x1ffc0fc00000,0x3f8000fffe00000]),(limbWord [0x1ffff0000000,0x3fffff000000000]),(limbWord [0x1fffffffffff,0xfc00000000000000])].getD (i % 8) 0 else [(limbWord [0x1fffffffffff,0xfc000000001fc1fc])].getD (i % 8) 0)

def p1At (i : Nat) : Nat := p1AtBlock0 i

def p2AtBlock0 (i : Nat) : Nat := (if i < 8 then [(limbWord [0x155db6f6bd5f,0xd5ba5d72baffc7ff]),(limbWord [0x1a82cb3b03ea,0x2a07820f04183000]),(limbWord [0x1aa2cb3b6bea,0x2ac7f2afd55ebe28]),(limbWord [0x1fdfffffbfff,0xffbfdf7fbefff7ff]),(limbWord [0x1fffffffffff,0xffffffffffffffff]),(limbWord [0x1cf70fe3ce73,0x4fece4cbdfecdacd]),(limbWord [0x1f3bfc3c739c,0xb3f77bfce1972d72]),(limbWord [0x1fc3efbf83ff,0x3f07830f06183180])].getD (i % 8) 0 else [(limbWord [0x1fdfffffbfff,0xffbfdf7fbefff7ff])].getD (i % 8) 0)

def p2At (i : Nat) : Nat := p2AtBlock0 i

def wireSAt (i : Nat) := if i < 9 then wireAt i else 0

def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 9 then (wireAt i,p1At i,p2At i) else (0,0,0)

def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_0 : ∀ i, 0 ≤ i → i < 8 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_8 : ∀ i, 8 ≤ i → i < 9 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 1 8 = true)

theorem wireD_all : ∀ i, 0 ≤ i → i < 9 → wireDOK i = true := (range_split wireD_all_0 wireD_all_8)

theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 9 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := wireD_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]

def stateWordDataBlock0 (i : Nat) : Nat := [550212,414500,0x865205,0x652105,0x765405,0x765205,0x765205].getD (i % 8) 0

def stateWordData (i : Nat) : Nat := stateWordDataBlock0 i

def stateWord (s i : Nat) : Nat := stateWordData ([0,0,0,0,2,6].getD s 0 + i)

def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n+1, ids => wireDAt (ids % 16) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, ids => wireSAt (ids % 16) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) := let p := stateWord s j; stateWiresD (p % 16) (p >>> 4)
def SS (s j : Nat) := let p := stateWord s j; stateWiresS (p % 16) (p >>> 4)

theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAtDataBlock0 (i : Nat) : Nat := [0x45261773,0x5871d099,0xd7fcbac,0x2ccc0175,0xd7ff152d,0xe1e63793,0xe1e63793].getD (i % 8) 0

def htAtData (i : Nat) : Nat := htAtDataBlock0 i

def htAt (s i : Nat) : Nat := htAtData ([0,0,0,0,2,6].getD s 0 + i)

def NN (s : Nat) := [0,0,0,2,4,1].getD s 0
def idxH (s h : Nat) := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (ws : List Nat) := idxH s (hk 0 ws)

def cutHitH (_ _ : Nat) (_ : List Nat) : Bool := false
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_4 goalM u ys := by contradiction

def cutHit (s : Nat) (ws : List Nat) := cutHitH s (hk 0 ws) ws
def ori (xs : List Nat) := xs
theorem ori_ok {u ys} (h : RunD dom_4 goalM u ys) : RunD dom_4 goalM u (ori ys) := h
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_4 goalM u ys := cutHitH_sound h
def pool6G : List Nat := []

def Z (s : Nat) := bar dom_4 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s

theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z3_0 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)

theorem z3 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := z3_0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)

theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := z4_0

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
  scr dom_4 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_4 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noCircuit : Lower dom_4 roots_4 goal_4 6 := by
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

end Cert4
theorem low_4 : Lower dom_4 roots_4 goal_4 6 := Cert4.noCircuit

def dom_5 : Nat := 0xf0f0f0f0f0f0f0f0
def roots_5 : List Nat := [0xa0a0a0a0a0a0a0a0,0xc0c0c0c0c0c0c0c0,0xf000f000f000f000,0xf0f00000f0f00000,0xf0f0f0f000000000]
def goal_5 : Nat := 0xe0e0e0e0e0e0e0c0
namespace Cert5

def xsM : List Nat := roots_5.map (· &&& dom_5)
def goalM : Nat := goal_5 &&& dom_5

def pairsG : List (Nat × Nat) := [(4,6),(4,7),(4,13),(4,14),(4,21),(4,22),(4,37),(4,38),(5,6),(5,7),(5,13),(5,15),(5,21),(5,23),(5,29),(5,37),(5,39),(5,45),(5,53),(12,6),(12,13),(12,14),(12,15),(12,29),(12,30),(12,45),(12,46),(20,6),(20,21),(20,22),(20,23),(20,29),(20,30),(20,53),(20,54),(28,13),(28,14),(28,21),(28,22),(28,29),(28,30),(28,31),(28,61),(28,62),(36,6),(36,37),(36,38),(36,39),(36,45),(36,46),(36,53),(36,54),(44,13),(44,14),(44,37),(44,38),(44,45),(44,46),(44,47),(44,61),(44,62),(52,21),(52,22),(52,37),(52,38),(52,53),(52,54),(52,55),(52,61),(52,62),(60,6),(60,13),(60,21),(60,29),(60,30),(60,37),(60,45),(60,46),(60,53),(60,54),(60,61),(60,62),(60,63)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_5 goalM s xsM) : False := by
  have hl := run_len h
  change 5 ≤ s + 1 at hl
  omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noCircuit : Lower dom_5 roots_5 goal_5 4 := by
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

end Cert5
theorem low_5 : Lower dom_5 roots_5 goal_5 4 := Cert5.noCircuit

def dom_6 : Nat := 0xff00ff00ff00ff
def roots_6 : List Nat := [0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]
def goal_6 : Nat := 0xee00e000ea00c0
namespace Cert6

def xsM : List Nat := roots_6.map (· &&& dom_6)
def goalM : Nat := goal_6 &&& dom_6

def pairsG : List (Nat × Nat) := [(0,6),(0,17),(1,7),(1,17),(1,19),(1,21),(1,37),(1,49),(2,6),(2,7),(2,19),(2,22),(2,38),(2,50),(3,6),(3,7),(3,17),(3,19),(3,23),(3,39),(3,51),(4,6),(4,7),(4,21),(4,22),(4,37),(4,38),(5,6),(5,7),(5,17),(5,21),(5,23),(5,37),(5,39),(5,50),(5,53),(16,17),(16,19),(16,21),(16,22),(16,49),(16,50),(18,6),(18,17),(18,19),(18,22),(18,23),(18,37),(18,50),(18,51),(18,54),(20,6),(20,17),(20,21),(20,22),(20,23),(20,53),(20,54),(32,37),(32,38),(32,49),(32,50),(33,17),(33,37),(33,39),(33,49),(33,51),(33,53),(34,6),(34,38),(34,39),(34,50),(34,51),(34,54),(35,6),(35,7),(35,17),(35,19),(35,37),(35,38),(35,39),(35,49),(35,50),(35,51),(35,55),(36,6),(36,37),(36,38),(36,39),(36,53),(36,54),(48,17),(48,49),(48,50),(48,51),(48,53),(48,54),(52,6),(52,17),(52,21),(52,22),(52,37),(52,38),(52,49),(52,50),(52,53),(52,54),(52,55)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

def wireAtBlock0 (i : Nat) : Nat := (if i < 32 then (if i < 16 then (if i < 8 then [0xff00ff,0xff000000ff,0xf000f000f000f,0x33003300330033,0x55005500550055,0x88008800880088,0xa000a000a000a0,0xaa000000aa0000].getD (i % 8) 0 else [0xaa00a000aa00a0,0xaa00aa00000000,0xaa00aa00aa0000,0xaa00aa00aa00aa,0xc000c000c000c0,0xcc000000cc0000,0xcc00c000cc00c0,0xcc00cc00000000].getD (i % 8) 0) else (if i < 24 then [0xcc00cc00c000c0,0xcc00cc00cc00cc,0xe000e000e000e0,0xea00ea00ea00ea,0xee000000ee0000,0xee00cc00ee00cc,0xee00ee00000000,0xee00ee00aa00aa].getD (i % 8) 0 else [0xee00ee00cc00cc,0xee00ee00ee00ee,0xf0000000f00000,0xf000f000000000,0xf000f000c000c0,0xf000f000f000f0,0xfa00f000fa00f0,0xfa00fa00fa00fa].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [0xfc00fc00000000,0xfc00fc00fc00fc,0xff000000000000,0xff000000aa0000,0xff000000ff0000,0xff00aa00000000,0xff00aa00ff00aa,0xff00c000ff00c0].getD (i % 8) 0 else [0xff00cc00ff00cc,0xff00f000000000,0xff00f000f000f0,0xff00f000ff0000,0xff00f000ff00f0,0xff00ff00000000,0xff00ff00880088,0xff00ff00aa0000].getD (i % 8) 0) else [0xff00ff00aa00aa,0xff00ff00c000c0,0xff00ff00cc00cc,0xff00ff00f00000,0xff00ff00f000f0,0xff00ff00ff0000].getD (i % 8) 0))

def wireAt (i : Nat) : Nat := wireAtBlock0 i

def p1AtBlock0 (i : Nat) : Nat := (if i < 32 then (if i < 16 then (if i < 8 then [0x3ffffffffffffff,(limbWord [0x7ffffff,0xfc00000fffffffff]),(limbWord [0x1f81fffff,0xfc07fff0001fffff]),(limbWord [0xfffffe0000f,0xfff803ffffe000ff]),(limbWord [0xfffffe003f0,0x3ffffff007e03f03]),(limbWord [0x1ffc00,0x1fc000]),0xff8000000,0].getD (i % 8) 0 else [0xff8000000,(limbWord [0x1ffc0f,0xc000000000000000]),(limbWord [0x1ffc0f,0xc000000000000000]),(limbWord [0x1ffc0f,0xc000000ff81fc0fc]),0,0x7fc0000000000,0x7fc0000000000,(limbWord [0x1ffff0,0x0])].getD (i % 8) 0) else (if i < 24 then [(limbWord [0x1ffff0,0x0]),(limbWord [0x1ffff0,0x7fc00001fff00]),0xff8000000,(limbWord [0x1ffc0f,0xc000000ff81fc0fc]),0x7fc0000000000,(limbWord [0x1ffff0,0x7fc00001fff00]),(limbWord [0x1fffff,0xc000000000000000]),(limbWord [0x1fffff,0xc000000ff81fc0fc])].getD (i % 8) 0 else [(limbWord [0x1fffff,0xc007fc00001fff00]),(limbWord [0x1fffff,0xc007fc0ff81ffffc]),(limbWord [0xffe00000000,0x3f8000000000000]),(limbWord [0xffe07e00000,0x0]),(limbWord [0xffe07e00000,0x0]),(limbWord [0xffe07e00000,0x3f8000fffe00000]),(limbWord [0xffe07e00000,0x3f8000fffe00000]),(limbWord [0xffe07fffc0f,0xc3f8000fffffc0fc])].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [(limbWord [0xffe07fffff0,0x0]),(limbWord [0xffe07fffff0,0x3fffc0fffffff00]),(limbWord [0xffff8000000,0x0]),(limbWord [0xffff8000000,0x0]),(limbWord [0xffff8000000,0x3fffff000000000]),(limbWord [0xffff81ffc0f,0xc000000000000000]),(limbWord [0xffff81ffc0f,0xc3fffffff81fc0fc]),(limbWord [0xffff8000000,0x3fffff000000000])].getD (i % 8) 0 else [(limbWord [0xffff81ffff0,0x3fffff0001fff00]),(limbWord [0xfffffe00000,0x0]),(limbWord [0xfffffe00000,0x3f8000fffe00000]),(limbWord [0xfffffe00000,0x3fffff000000000]),(limbWord [0xfffffe00000,0x3ffffffffe00000]),(limbWord [0xfffffffffff,0xfc00000000000000]),(limbWord [0xfffffffffff,0xfc000000001fc000]),(limbWord [0xfffffffffff,0xfc00000000000000])].getD (i % 8) 0) else [(limbWord [0xfffffffffff,0xfc00000ff81fc0fc]),(limbWord [0xfffffffffff,0xfc00000000000000]),(limbWord [0xfffffffffff,0xfc07fc00001fff00]),(limbWord [0xfffffffffff,0xfff8000000000000]),(limbWord [0xfffffffffff,0xfff8000fffe00000]),(limbWord [0xfffffffffff,0xfffffff000000000])].getD (i % 8) 0))

def p1At (i : Nat) : Nat := p1AtBlock0 i

def p2AtBlock0 (i : Nat) : Nat := (if i < 32 then (if i < 16 then (if i < 8 then [(limbWord [0x1e08203c10,0x40f87cf0f9e7cf3f]),(limbWord [0x6201e1cc71,0x8c0884031e68d345]),(limbWord [0x184780e3186,0x70131b342013249a]),(limbWord [0x2ac9a42500a,0xd5308959628100ea]),(limbWord [0x55324a486b0,0x2a4d26840d207901]),(limbWord [0x80041192945,0x825022905e8614]),(limbWord [0xa2883514849,0x85a0c04bd2cc8264]),(limbWord [0xa8cda1a310e,0x51b25978e09704ba])].getD (i % 8) 0 else [(limbWord [0xaacdb5b794f,0xd5b2d97bf2df86fe]),(limbWord [0xaa0d35b414f,0x9502810b021800c0]),(limbWord [0xaacdb5b714f,0xd5b2d97be29f04fa]),(limbWord [0xaacdb5b794f,0xd5b2d97bf2df86fe]),(limbWord [0xc5305b18e71,0xacc64829d6cdb05]),(limbWord [0xd11641c2384,0x22c772a481162c10]),(limbWord [0xd5365bdaff5,0x2acf76a69d7eff15]),(limbWord [0xd41659d83e5,0x2a07020604183000])].getD (i % 8) 0) else (if i < 24 then [(limbWord [0xd5365bd8ff5,0x2acf66869d7cfb05]),(limbWord [0xd5365bdaff5,0x2acf76a69d7eff15]),(limbWord [0xe7b87f1ce79,0x8fece4cbdfecdb65]),(limbWord [0xeffdffbff7f,0xdffefdfbffffdfff]),(limbWord [0xf9dfe1e338e,0x73f77bfce1972cba]),(limbWord [0xfdfffbfbfff,0x7bff7ffefdffffbf]),(limbWord [0xfe1f7dfc3ef,0xbf07830f061830c0]),(limbWord [0xfedffdffbef,0xffb7db7ff6dfb6fe])].getD (i % 8) 0 else [(limbWord [0xff3f7ffefff,0xbfcff7af9f7effd5]),(limbWord [0xfffffffffff,0xffffffffffffffff]),(limbWord [0xe1986100208,0x3e460c8c1840820]),(limbWord [0xe6187d1c269,0x8f04800b06081040]),(limbWord [0xe7387f1ce79,0x8fcce48b9f6cdb45]),(limbWord [0xe7b87f1ce79,0x8fece4cbdfecdb65]),(limbWord [0xeffdffbff7f,0xdffefdfbffffdfff]),(limbWord [0xeffdffbff7f,0xdffefdfbffffdfff])].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [(limbWord [0xf61e7ddc3ed,0xaf07820f06183040]),(limbWord [0xf7be7fdeffd,0xafeff6efdffeff75]),(limbWord [0xf81f61e038e,0x3307030c00102080]),(limbWord [0xf8dfe1e338e,0x73b75b7ce09724ba]),(limbWord [0xf9dfe1e338e,0x73f77bfce1972cba]),(limbWord [0xfa1f75f43cf,0xb707830f021820c0]),(limbWord [0xfbdff5f7bcf,0xf7f7fbfff3dfaefe]),(limbWord [0xfdfffbfbfff,0x7bff7ffefdffffbf])].getD (i % 8) 0 else [(limbWord [0xfdfffbfbfff,0x7bff7ffefdffffbf]),(limbWord [0xfe1f7dfc3ef,0xbf07830f061830c0]),(limbWord [0xffbf7ffcfff,0xbfefe7cfdffcfbe5]),(limbWord [0xffdffdff3ef,0xfff7fbffe79f3cfa]),(limbWord [0xfffffffffff,0xffffffffffffffff]),(limbWord [0xfe1f7dfc3ef,0xbf07830f061830c0]),(limbWord [0xfe1f7dfebef,0xbf87d32f965eb6d4]),(limbWord [0xfedffdff3ef,0xffb7db7fe69f34fa])].getD (i % 8) 0) else [(limbWord [0xfedffdffbef,0xffb7db7ff6dfb6fe]),(limbWord [0xff3f7ffcfff,0xbfcfe78f9f7cfbc5]),(limbWord [0xff3f7ffefff,0xbfcff7af9f7effd5]),(limbWord [0xff9f7dfc3ef,0xbfe7e3cfc79c38e0]),(limbWord [0xffbf7ffcfff,0xbfefe7cfdffcfbe5]),(limbWord [0xffdffdff3ef,0xfff7fbffe79f3cfa])].getD (i % 8) 0))

def p2At (i : Nat) : Nat := p2AtBlock0 i

def wireSAt (i : Nat) := if i < 54 then wireAt i else 0

def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 54 then (wireAt i,p1At i,p2At i) else (0,0,0)

def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_0 : ∀ i, 0 ≤ i → i < 8 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_8 : ∀ i, 8 ≤ i → i < 16 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 8 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_16 : ∀ i, 16 ≤ i → i < 24 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 16 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_24 : ∀ i, 24 ≤ i → i < 32 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 24 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_32 : ∀ i, 32 ≤ i → i < 40 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 32 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_40 : ∀ i, 40 ≤ i → i < 48 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 40 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_48 : ∀ i, 48 ≤ i → i < 54 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 6 48 = true)

theorem wireD_all : ∀ i, 0 ≤ i → i < 54 → wireDOK i = true := (range_split (range_split (range_split wireD_all_0 wireD_all_8) (range_split wireD_all_16 wireD_all_24)) (range_split (range_split wireD_all_32 wireD_all_40) wireD_all_48))

theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 54 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := wireD_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]

def stateWordDataBlock0 (i : Nat) : Nat := (if i < 32 then (if i < 16 then (if i < 8 then [0x2d91d54b5,0x2d91d5d15,0x2dadd44b5,0x3191d44b5,0x2daa444b5,0x2475644b5,0x2d91d4485,0x2e91d44b5].getD (i % 8) 0 else [0x2f91d44b5,0x2d91244b5,0x2d91d40b5,0x2d8dd44b5,0x2d91d60b5,0x2d75444b5,0x2d91d4d15,0x2d91d44a5].getD (i % 8) 0) else (if i < 24 then [0x2d91c44b5,0x2d9dd44b5,0x2d91e44b5,0x3391d44b5,0x2d91d44b5,0x2591d44b5,0x2481d44b5,0x2991d44b5].getD (i % 8) 0 else [0x2d91d38b5,0xb647512c76,0xb647512c96,0x247512c05,0xb6475a44b6,0xb6475130b6,0xb6489d44b6,0xc2d91d44b6].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [0xb647512c16,0xb6475b44b6,0xb647513cb6,0x2d91d2c35,0xb6891d44b6,0xb647512c66,0xb647512c26,0x2d7512c15].getD (i % 8) 0 else [0xd6d91d44b6,0xd2d91d44b6,0xb647512c56,0x2d9112c25,0xb6c91d44b6,0xb647512c46,0x2d91d44b5,0xb647512c36].getD (i % 8) 0) else (if i < 56 then [0xb6485d44b6,0x2d91d4445,0xb6475134b6,0xb6691d44b6,0xcad91d44b6,0xb647dd44b6,0xb647512c06,0xb6475944b6].getD (i % 8) 0 else [0x2d91d44b5].getD (i % 8) 0)))

def stateWordData (i : Nat) : Nat := stateWordDataBlock0 i

def stateWord (s i : Nat) : Nat := stateWordData ([0,0,0,0,0,25,56].getD s 0 + i)

def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n+1, ids => wireDAt (ids % 64) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, ids => wireSAt (ids % 64) :: stateWiresS n (ids >>> 6)
def SD (s j : Nat) := let p := stateWord s j; stateWiresD (p % 16) (p >>> 4)
def SS (s j : Nat) := let p := stateWord s j; stateWiresS (p % 16) (p >>> 4)

theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAtDataBlock0 (i : Nat) : Nat := (if i < 32 then (if i < 16 then (if i < 8 then [0x72ae9d5,0xba04ca4,0x1363375b,0x329e8a69,0x437cb3df,0x4daa6b06,0x52fc3e0c,0x539dac85].getD (i % 8) 0 else [0x6829cb1b,0x6b217175,0x6dfa56b0,0x7c80a5f6,0x8d065f2c,0x8f964c40,0x929b731e,0x9484ddac].getD (i % 8) 0) else (if i < 24 then [0x98f5986c,0x9adb4166,0xab9efaf6,0xc06ea9f8,0xc75334ec,0xd683da85,0xd893a010,0xe43ec351].getD (i % 8) 0 else [0xeb159592,0x1520e48,0x6a64ae4,0x8db3cce,0xd86c48f,0x17c57fcb,0x1d4412d1,0x1e416e5d].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [0x2ef5abdb,0x40936f62,0x45a7a6cb,0x470e136e,0x49cfa8c9,0x5e9140de,0x5ee35caf,0x69f765d1].getD (i % 8) 0 else [0x6d4dd0a1,0x7a4eef81,0x891d4fac,0x9b7b9e1c,0xa2b49de6,0xa37d19b2,0xc75334ec,0xd2c9a9f6].getD (i % 8) 0) else (if i < 56 then [0xd5230868,0xde3bf0d6,0xdf7ac0f1,0xe3968bc6,0xe5b7a4f3,0xf09c0829,0xf6cbadb9,0xffd02c18].getD (i % 8) 0 else [0xc75334ec].getD (i % 8) 0)))

def htAtData (i : Nat) : Nat := htAtDataBlock0 i

def htAt (s i : Nat) : Nat := htAtData ([0,0,0,0,0,25,56].getD s 0 + i)

def NN (s : Nat) := [0,0,0,0,25,31,1].getD s 0
def idxH (s h : Nat) := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (ws : List Nat) := idxH s (hk 0 ws)

def cutHitH (_ _ : Nat) (_ : List Nat) : Bool := false
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_6 goalM u ys := by contradiction

def cutHit (s : Nat) (ws : List Nat) := cutHitH s (hk 0 ws) ws
def ori (xs : List Nat) := xs
theorem ori_ok {u ys} (h : RunD dom_6 goalM u ys) : RunD dom_6 goalM u (ori ys) := h
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_6 goalM u ys := cutHitH_sound h
def pool6G : List Nat := []

def Z (s : Nat) := bar dom_6 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s

theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_6 : ∀ i, 6 ≤ i → i < 12 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 6 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_12 : ∀ i, 12 ≤ i → i < 18 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 12 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_18 : ∀ i, 18 ≤ i → i < 24 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 18 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_24 : ∀ i, 24 ≤ i → i < 25 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 24 = true)

theorem z4 : ∀ i, 0 ≤ i → i < 25 → Z 4 i = true := (range_split (range_split (range_split z4_0 z4_6) (range_split z4_12 z4_18)) z4_24)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_6 : ∀ i, 6 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 6 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_12 : ∀ i, 12 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 12 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_18 : ∀ i, 18 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 18 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_24 : ∀ i, 24 ≤ i → i < 30 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 24 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_30 : ∀ i, 30 ≤ i → i < 31 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 30 = true)

theorem z5 : ∀ i, 0 ≤ i → i < 31 → Z 5 i = true := (range_split (range_split (range_split z5_0 z5_6) (range_split z5_12 z5_18)) (range_split z5_24 z5_30))

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

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

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

end Cert6
theorem low_6 : Lower dom_6 roots_6 goal_6 7 := Cert6.noCircuit

def dom_7 : Nat := 0xff00ff00ff00ff00
def roots_7 : List Nat := [0xaa00aa00aa00aa00,0xcc00cc00cc00cc00,0xf000f000f000f000,0xff000000ff000000,0xff00ff0000000000]
def goal_7 : Nat := 0xee00ee00ee00ea00
namespace Cert7

def xsM : List Nat := roots_7.map (· &&& dom_7)
def goalM : Nat := goal_7 &&& dom_7

def pairsG : List (Nat × Nat) := [(8,9),(8,11),(8,13),(8,14),(8,25),(8,26),(8,41),(8,42),(10,9),(10,11),(10,14),(10,15),(10,26),(10,27),(10,30),(10,42),(10,43),(10,46),(10,58),(12,9),(12,13),(12,14),(12,15),(12,29),(12,30),(12,45),(12,46),(24,9),(24,25),(24,26),(24,27),(24,29),(24,30),(24,57),(24,58),(28,13),(28,14),(28,25),(28,26),(28,29),(28,30),(28,31),(28,61),(28,62),(40,9),(40,41),(40,42),(40,43),(40,45),(40,46),(40,57),(40,58),(44,13),(44,14),(44,41),(44,42),(44,45),(44,46),(44,47),(44,61),(44,62),(56,25),(56,26),(56,41),(56,42),(56,57),(56,58),(56,59),(56,61),(56,62),(60,9),(60,14),(60,26),(60,29),(60,30),(60,42),(60,45),(60,46),(60,57),(60,58),(60,61),(60,62),(60,63)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_7 goalM s xsM) : False := by
  have hl := run_len h
  change 5 ≤ s + 1 at hl
  omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

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

end Cert7
theorem low_7 : Lower dom_7 roots_7 goal_7 4 := Cert7.noCircuit

def dom_8 : Nat := 0xffff0000ffff
def roots_8 : List Nat := [0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]
def goal_8 : Nat := 0xeee00000eac0
namespace Cert8

def xsM : List Nat := roots_8.map (· &&& dom_8)
def goalM : Nat := goal_8 &&& dom_8

def pairsG : List (Nat × Nat) := [(0,6),(0,9),(1,7),(1,9),(1,11),(1,13),(1,37),(1,41),(2,6),(2,7),(2,11),(2,14),(2,38),(2,42),(3,6),(3,7),(3,9),(3,11),(3,15),(3,39),(3,43),(4,6),(4,7),(4,13),(4,14),(4,37),(4,38),(5,6),(5,7),(5,9),(5,13),(5,15),(5,37),(5,39),(5,42),(5,45),(8,9),(8,11),(8,13),(8,14),(8,41),(8,42),(10,6),(10,9),(10,11),(10,14),(10,15),(10,37),(10,42),(10,43),(10,46),(12,6),(12,9),(12,13),(12,14),(12,15),(12,45),(12,46),(32,37),(32,38),(32,41),(32,42),(33,9),(33,37),(33,39),(33,41),(33,43),(33,45),(34,6),(34,38),(34,39),(34,42),(34,43),(34,46),(35,6),(35,7),(35,9),(35,11),(35,37),(35,38),(35,39),(35,41),(35,42),(35,43),(35,47),(36,6),(36,37),(36,38),(36,39),(36,45),(36,46),(40,9),(40,41),(40,42),(40,43),(40,45),(40,46),(44,6),(44,9),(44,13),(44,14),(44,37),(44,38),(44,41),(44,42),(44,45),(44,46),(44,47)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

def wireAtBlock0 (i : Nat) : Nat := (if i < 32 then (if i < 16 then (if i < 8 then [65535,0xff000000ff,0xf0f00000f0f,0x333300003333,0x555500005555,0x888800008888,0xa0a00000a0a0,0xaa000000aa00].getD (i % 8) 0 else [0xaaa00000aaa0,0xaaaa00000000,0xaaaa0000aa00,0xaaaa0000aaaa,0xc0c00000c0c0,0xcc000000cc00,0xccc00000ccc0,0xcccc00000000].getD (i % 8) 0) else (if i < 24 then [0xcccc0000c0c0,0xcccc0000cccc,0xe0e00000e0e0,0xeaea0000eaea,0xee000000ee00,0xeecc0000eecc,0xeeee00000000,0xeeee0000aaaa].getD (i % 8) 0 else [0xeeee0000cccc,0xeeee0000eeee,0xf0000000f000,0xf0f000000000,0xf0f00000c0c0,0xf0f00000f0f0,0xfaf00000faf0,0xfafa0000fafa].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [0xfcfc00000000,0xfcfc0000fcfc,0xff0000000000,0xff000000aa00,0xff000000ff00,0xffaa00000000,0xffaa0000ffaa,0xffc00000ffc0].getD (i % 8) 0 else [0xffcc0000ffcc,0xfff000000000,0xfff00000f0f0,0xfff00000ff00,0xfff00000fff0,0xffff00000000,0xffff00008888,0xffff0000aa00].getD (i % 8) 0) else [0xffff0000aaaa,0xffff0000c0c0,0xffff0000cccc,0xffff0000f000,0xffff0000f0f0,0xffff0000ff00].getD (i % 8) 0))

def wireAt (i : Nat) : Nat := wireAtBlock0 i

def p1AtBlock0 (i : Nat) : Nat := (if i < 32 then (if i < 16 then (if i < 8 then [0x3ffffffffffffff,(limbWord [0x7ffffff,0xfc00000fffffffff]),(limbWord [0x1f81fffff,0xfc07fff0001fffff]),(limbWord [0xfffffe0000f,0xfff803ffffe000ff]),(limbWord [0xfffffe003f0,0x3ffffff007e03f03]),(limbWord [0x1ffc00,0x1fc000]),0xff8000000,0].getD (i % 8) 0 else [0xff8000000,(limbWord [0x1ffc0f,0xc000000000000000]),(limbWord [0x1ffc0f,0xc000000000000000]),(limbWord [0x1ffc0f,0xc000000ff81fc0fc]),0,0x7fc0000000000,0x7fc0000000000,(limbWord [0x1ffff0,0x0])].getD (i % 8) 0) else (if i < 24 then [(limbWord [0x1ffff0,0x0]),(limbWord [0x1ffff0,0x7fc00001fff00]),0xff8000000,(limbWord [0x1ffc0f,0xc000000ff81fc0fc]),0x7fc0000000000,(limbWord [0x1ffff0,0x7fc00001fff00]),(limbWord [0x1fffff,0xc000000000000000]),(limbWord [0x1fffff,0xc000000ff81fc0fc])].getD (i % 8) 0 else [(limbWord [0x1fffff,0xc007fc00001fff00]),(limbWord [0x1fffff,0xc007fc0ff81ffffc]),(limbWord [0xffe00000000,0x3f8000000000000]),(limbWord [0xffe07e00000,0x0]),(limbWord [0xffe07e00000,0x0]),(limbWord [0xffe07e00000,0x3f8000fffe00000]),(limbWord [0xffe07e00000,0x3f8000fffe00000]),(limbWord [0xffe07fffc0f,0xc3f8000fffffc0fc])].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [(limbWord [0xffe07fffff0,0x0]),(limbWord [0xffe07fffff0,0x3fffc0fffffff00]),(limbWord [0xffff8000000,0x0]),(limbWord [0xffff8000000,0x0]),(limbWord [0xffff8000000,0x3fffff000000000]),(limbWord [0xffff81ffc0f,0xc000000000000000]),(limbWord [0xffff81ffc0f,0xc3fffffff81fc0fc]),(limbWord [0xffff8000000,0x3fffff000000000])].getD (i % 8) 0 else [(limbWord [0xffff81ffff0,0x3fffff0001fff00]),(limbWord [0xfffffe00000,0x0]),(limbWord [0xfffffe00000,0x3f8000fffe00000]),(limbWord [0xfffffe00000,0x3fffff000000000]),(limbWord [0xfffffe00000,0x3ffffffffe00000]),(limbWord [0xfffffffffff,0xfc00000000000000]),(limbWord [0xfffffffffff,0xfc000000001fc000]),(limbWord [0xfffffffffff,0xfc00000000000000])].getD (i % 8) 0) else [(limbWord [0xfffffffffff,0xfc00000ff81fc0fc]),(limbWord [0xfffffffffff,0xfc00000000000000]),(limbWord [0xfffffffffff,0xfc07fc00001fff00]),(limbWord [0xfffffffffff,0xfff8000000000000]),(limbWord [0xfffffffffff,0xfff8000fffe00000]),(limbWord [0xfffffffffff,0xfffffff000000000])].getD (i % 8) 0))

def p1At (i : Nat) : Nat := p1AtBlock0 i

def p2AtBlock0 (i : Nat) : Nat := (if i < 32 then (if i < 16 then (if i < 8 then [(limbWord [0x1e08203c10,0x40f87cf0f9e7cf3f]),(limbWord [0x6201e1cc71,0x8c0884031e68d345]),(limbWord [0x184780e3186,0x70131b342013249a]),(limbWord [0x2ac9a42500a,0xd5308959628100ea]),(limbWord [0x55324a486b0,0x2a4d26840d207901]),(limbWord [0x80041192945,0x825022905e8614]),(limbWord [0xa2883514849,0x85a0c04bd2cc8264]),(limbWord [0xa8cda1a310e,0x51b25978e09704ba])].getD (i % 8) 0 else [(limbWord [0xaacdb5b794f,0xd5b2d97bf2df86fe]),(limbWord [0xaa0d35b414f,0x9502810b021800c0]),(limbWord [0xaacdb5b714f,0xd5b2d97be29f04fa]),(limbWord [0xaacdb5b794f,0xd5b2d97bf2df86fe]),(limbWord [0xc5305b18e71,0xacc64829d6cdb05]),(limbWord [0xd11641c2384,0x22c772a481162c10]),(limbWord [0xd5365bdaff5,0x2acf76a69d7eff15]),(limbWord [0xd41659d83e5,0x2a07020604183000])].getD (i % 8) 0) else (if i < 24 then [(limbWord [0xd5365bd8ff5,0x2acf66869d7cfb05]),(limbWord [0xd5365bdaff5,0x2acf76a69d7eff15]),(limbWord [0xe7b87f1ce79,0x8fece4cbdfecdb65]),(limbWord [0xeffdffbff7f,0xdffefdfbffffdfff]),(limbWord [0xf9dfe1e338e,0x73f77bfce1972cba]),(limbWord [0xfdfffbfbfff,0x7bff7ffefdffffbf]),(limbWord [0xfe1f7dfc3ef,0xbf07830f061830c0]),(limbWord [0xfedffdffbef,0xffb7db7ff6dfb6fe])].getD (i % 8) 0 else [(limbWord [0xff3f7ffefff,0xbfcff7af9f7effd5]),(limbWord [0xfffffffffff,0xffffffffffffffff]),(limbWord [0xe1986100208,0x3e460c8c1840820]),(limbWord [0xe6187d1c269,0x8f04800b06081040]),(limbWord [0xe7387f1ce79,0x8fcce48b9f6cdb45]),(limbWord [0xe7b87f1ce79,0x8fece4cbdfecdb65]),(limbWord [0xeffdffbff7f,0xdffefdfbffffdfff]),(limbWord [0xeffdffbff7f,0xdffefdfbffffdfff])].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [(limbWord [0xf61e7ddc3ed,0xaf07820f06183040]),(limbWord [0xf7be7fdeffd,0xafeff6efdffeff75]),(limbWord [0xf81f61e038e,0x3307030c00102080]),(limbWord [0xf8dfe1e338e,0x73b75b7ce09724ba]),(limbWord [0xf9dfe1e338e,0x73f77bfce1972cba]),(limbWord [0xfa1f75f43cf,0xb707830f021820c0]),(limbWord [0xfbdff5f7bcf,0xf7f7fbfff3dfaefe]),(limbWord [0xfdfffbfbfff,0x7bff7ffefdffffbf])].getD (i % 8) 0 else [(limbWord [0xfdfffbfbfff,0x7bff7ffefdffffbf]),(limbWord [0xfe1f7dfc3ef,0xbf07830f061830c0]),(limbWord [0xffbf7ffcfff,0xbfefe7cfdffcfbe5]),(limbWord [0xffdffdff3ef,0xfff7fbffe79f3cfa]),(limbWord [0xfffffffffff,0xffffffffffffffff]),(limbWord [0xfe1f7dfc3ef,0xbf07830f061830c0]),(limbWord [0xfe1f7dfebef,0xbf87d32f965eb6d4]),(limbWord [0xfedffdff3ef,0xffb7db7fe69f34fa])].getD (i % 8) 0) else [(limbWord [0xfedffdffbef,0xffb7db7ff6dfb6fe]),(limbWord [0xff3f7ffcfff,0xbfcfe78f9f7cfbc5]),(limbWord [0xff3f7ffefff,0xbfcff7af9f7effd5]),(limbWord [0xff9f7dfc3ef,0xbfe7e3cfc79c38e0]),(limbWord [0xffbf7ffcfff,0xbfefe7cfdffcfbe5]),(limbWord [0xffdffdff3ef,0xfff7fbffe79f3cfa])].getD (i % 8) 0))

def p2At (i : Nat) : Nat := p2AtBlock0 i

def wireSAt (i : Nat) := if i < 54 then wireAt i else 0

def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 54 then (wireAt i,p1At i,p2At i) else (0,0,0)

def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_0 : ∀ i, 0 ≤ i → i < 8 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_8 : ∀ i, 8 ≤ i → i < 16 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 8 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_16 : ∀ i, 16 ≤ i → i < 24 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 16 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_24 : ∀ i, 24 ≤ i → i < 32 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 24 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_32 : ∀ i, 32 ≤ i → i < 40 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 32 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_40 : ∀ i, 40 ≤ i → i < 48 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 40 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_48 : ∀ i, 48 ≤ i → i < 54 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 6 48 = true)

theorem wireD_all : ∀ i, 0 ≤ i → i < 54 → wireDOK i = true := (range_split (range_split (range_split wireD_all_0 wireD_all_8) (range_split wireD_all_16 wireD_all_24)) (range_split (range_split wireD_all_32 wireD_all_40) wireD_all_48))

theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 54 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := wireD_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]

def stateWordDataBlock0 (i : Nat) : Nat := (if i < 32 then (if i < 16 then (if i < 8 then [0x2481d44b5,0x2d91d44a5,0x2591d44b5,0x2d91244b5,0x3191d44b5,0x2d91c44b5,0x2d91e44b5,0x2d91d4485].getD (i % 8) 0 else [0x2d91d54b5,0x2dadd44b5,0x3391d44b5,0x2d9dd44b5,0x2d91d4d15,0x2e91d44b5,0x2991d44b5,0x2d91d5d15].getD (i % 8) 0) else (if i < 24 then [0x2f91d44b5,0x2d91d44b5,0x2daa444b5,0x2d91d60b5,0x2d91d38b5,0x2d8dd44b5,0x2475644b5,0x2d75444b5].getD (i % 8) 0 else [0x2d91d40b5,0xb647512c16,0xb6489d44b6,0xb647513cb6,0x2d9112c25,0x2d91d4445,0xb647512c76,0xb6475134b6].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [0xb6475944b6,0xb647512c26,0xb647512c96,0x247512c05,0xb6485d44b6,0x2d91d2c35,0xb6891d44b6,0xd6d91d44b6].getD (i % 8) 0 else [0xb647512c36,0xb6691d44b6,0xb647512c66,0xb6475b44b6,0xb6475a44b6,0xb6475130b6,0x2d91d44b5,0x2d7512c15].getD (i % 8) 0) else (if i < 56 then [0xcad91d44b6,0xd2d91d44b6,0xb647512c46,0xb647dd44b6,0xb6c91d44b6,0xb647512c56,0xc2d91d44b6,0xb647512c06].getD (i % 8) 0 else [0x2d91d44b5].getD (i % 8) 0)))

def stateWordData (i : Nat) : Nat := stateWordDataBlock0 i

def stateWord (s i : Nat) : Nat := stateWordData ([0,0,0,0,0,25,56].getD s 0 + i)

def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n+1, ids => wireDAt (ids % 64) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, ids => wireSAt (ids % 64) :: stateWiresS n (ids >>> 6)
def SD (s j : Nat) := let p := stateWord s j; stateWiresD (p % 16) (p >>> 4)
def SS (s j : Nat) := let p := stateWord s j; stateWiresS (p % 16) (p >>> 4)

theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAtDataBlock0 (i : Nat) : Nat := (if i < 32 then (if i < 16 then (if i < 8 then [0x71729c3,0x7edf94c,0x85963fb,0x1b99fa91,0x266731f0,0x28cfb507,0x33df76f4,0x36be41c7].getD (i % 8) 0 else [0x681a8ec3,0x6d12af4a,0x6fb1298d,0x75819ad0,0x7b16993f,0x7e585c3e,0x9b16a858,0x9b2fed8d].getD (i % 8) 0) else (if i < 24 then [0xa93eb7c5,0xae9d43a7,0xba686abf,0xc506497e,0xc647435e,0xcd99b965,0xda401239,0xe669dc51].getD (i % 8) 0 else [0xfc97ab07,0x163fba96,0x25c7148e,0x2f773244,0x35bd9462,0x3a225d52,0x41d74280,0x4c830e8b].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [0x6267e58d,0x6697f7fb,0x6eb29bd1,0x6f128fa6,0x78ce80e0,0x7acd99bd,0x7ba08c70,0x82e3437c].getD (i % 8) 0 else [0x8632f164,0x8947918c,0x8c1e79d2,0x9a399d8c,0xad469050,0xae5239fe,0xae9d43a7,0xb77abc50].getD (i % 8) 0) else (if i < 56 then [0xbaf33fea,0xc672aabe,0xd028caab,0xd0ea858d,0xd7d843dc,0xdd84e761,0xe4d2e469,0xeca4ac6e].getD (i % 8) 0 else [0xae9d43a7].getD (i % 8) 0)))

def htAtData (i : Nat) : Nat := htAtDataBlock0 i

def htAt (s i : Nat) : Nat := htAtData ([0,0,0,0,0,25,56].getD s 0 + i)

def NN (s : Nat) := [0,0,0,0,25,31,1].getD s 0
def idxH (s h : Nat) := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (ws : List Nat) := idxH s (hk 0 ws)

def cutHitH (_ _ : Nat) (_ : List Nat) : Bool := false
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_8 goalM u ys := by contradiction

def cutHit (s : Nat) (ws : List Nat) := cutHitH s (hk 0 ws) ws
def ori (xs : List Nat) := xs
theorem ori_ok {u ys} (h : RunD dom_8 goalM u ys) : RunD dom_8 goalM u (ori ys) := h
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_8 goalM u ys := cutHitH_sound h
def pool6G : List Nat := []

def Z (s : Nat) := bar dom_8 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s

theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_6 : ∀ i, 6 ≤ i → i < 12 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 6 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_12 : ∀ i, 12 ≤ i → i < 18 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 12 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_18 : ∀ i, 18 ≤ i → i < 24 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 18 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_24 : ∀ i, 24 ≤ i → i < 25 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 24 = true)

theorem z4 : ∀ i, 0 ≤ i → i < 25 → Z 4 i = true := (range_split (range_split (range_split z4_0 z4_6) (range_split z4_12 z4_18)) z4_24)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_6 : ∀ i, 6 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 6 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_12 : ∀ i, 12 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 12 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_18 : ∀ i, 18 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 18 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_24 : ∀ i, 24 ≤ i → i < 30 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 24 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_30 : ∀ i, 30 ≤ i → i < 31 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 30 = true)

theorem z5 : ∀ i, 0 ≤ i → i < 31 → Z 5 i = true := (range_split (range_split (range_split z5_0 z5_6) (range_split z5_12 z5_18)) (range_split z5_24 z5_30))

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

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

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

end Cert8
theorem low_8 : Lower dom_8 roots_8 goal_8 7 := Cert8.noCircuit

def dom_9 : Nat := 0xffff0000ffff0000
def roots_9 : List Nat := [0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff000000000000]
def goal_9 : Nat := 0xeeee0000eeea0000
namespace Cert9

def xsM : List Nat := roots_9.map (· &&& dom_9)
def goalM : Nat := goal_9 &&& dom_9

def pairsG : List (Nat × Nat) := [(16,17),(16,19),(16,21),(16,22),(16,25),(16,26),(16,49),(16,50),(18,17),(18,19),(18,22),(18,23),(18,26),(18,27),(18,30),(18,50),(18,51),(18,54),(18,58),(20,17),(20,21),(20,22),(20,23),(20,29),(20,30),(20,53),(20,54),(24,17),(24,25),(24,26),(24,27),(24,29),(24,30),(24,57),(24,58),(28,21),(28,22),(28,25),(28,26),(28,29),(28,30),(28,31),(28,61),(28,62),(48,17),(48,49),(48,50),(48,51),(48,53),(48,54),(48,57),(48,58),(52,21),(52,22),(52,49),(52,50),(52,53),(52,54),(52,55),(52,61),(52,62),(56,25),(56,26),(56,49),(56,50),(56,57),(56,58),(56,59),(56,61),(56,62),(60,17),(60,22),(60,26),(60,29),(60,30),(60,50),(60,53),(60,54),(60,57),(60,58),(60,61),(60,62),(60,63)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_9 goalM s xsM) : False := by
  have hl := run_len h
  change 5 ≤ s + 1 at hl
  omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

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

end Cert9
theorem low_9 : Lower dom_9 roots_9 goal_9 4 := Cert9.noCircuit

def dom_10 : Nat := 0xffffffff
def roots_10 : List Nat := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def goal_10 : Nat := 0xeeeaeac0
namespace Cert10

def xsM : List Nat := roots_10.map (· &&& dom_10)
def goalM : Nat := goal_10 &&& dom_10

def pairsG : List (Nat × Nat) := [(0,6),(0,9),(0,17),(1,7),(1,9),(1,11),(1,13),(1,17),(1,19),(1,21),(1,25),(2,6),(2,7),(2,11),(2,14),(2,19),(2,22),(2,26),(3,6),(3,7),(3,9),(3,11),(3,15),(3,17),(3,19),(3,23),(3,26),(3,27),(4,6),(4,7),(4,13),(4,14),(4,21),(4,22),(5,6),(5,7),(5,9),(5,13),(5,15),(5,17),(5,21),(5,23),(5,26),(5,29),(8,9),(8,11),(8,13),(8,14),(8,25),(8,26),(10,6),(10,9),(10,11),(10,14),(10,15),(10,17),(10,26),(10,27),(10,30),(12,6),(12,9),(12,13),(12,14),(12,15),(12,29),(12,30),(16,17),(16,19),(16,21),(16,22),(16,25),(16,26),(18,6),(18,9),(18,17),(18,19),(18,22),(18,23),(18,26),(18,27),(18,30),(20,6),(20,17),(20,21),(20,22),(20,23),(20,29),(20,30),(24,9),(24,17),(24,25),(24,26),(24,27),(24,29),(24,30),(28,6),(28,9),(28,13),(28,14),(28,17),(28,21),(28,22),(28,25),(28,26),(28,29),(28,30),(28,31)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

def wireAtBlock0 (i : Nat) : Nat := [0xaaaaaaaa,0xc0c0c0c0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000].getD (i % 8) 0

def wireAt (i : Nat) : Nat := wireAtBlock0 i

def p1AtBlock0 (i : Nat) : Nat := [0xffc0ffc07f8,0,(limbWord [0x1ff00,0x7fc00000ffff800]),(limbWord [0x7ff80fe0003,0xf8000ffff0000000]),(limbWord [0x7ffff000003,0xfffff00000000000]),(limbWord [0x7fffffffffc,0x0])].getD (i % 8) 0

def p1At (i : Nat) : Nat := p1AtBlock0 i

def p2AtBlock0 (i : Nat) : Nat := [(limbWord [0x55b376cae5d,0xb2d97bf96bf8b7fe]),(limbWord [0x624c0b33122,0xcc64824eb24d5809]),(limbWord [0x6a4d8b3f9aa,0xcf76a64ebf6ff929]),(limbWord [0x736e0fb3133,0xec64cb6ff24d5a49]),(limbWord [0x7c77dc1c2c3,0xf77bfc70cc726472]),(limbWord [0x7f87efdfcff,0x7830f830f838784])].getD (i % 8) 0

def p2At (i : Nat) : Nat := p2AtBlock0 i

def wireSAt (i : Nat) := if i < 6 then wireAt i else 0

def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 6 then (wireAt i,p1At i,p2At i) else (0,0,0)

def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_0 : ∀ i, 0 ≤ i → i < 6 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 6 0 = true)

theorem wireD_all : ∀ i, 0 ≤ i → i < 6 → wireDOK i = true := wireD_all_0

theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := wireD_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]

def stateWordDataBlock0 (i : Nat) : Nat := [363781,362629,363781].getD (i % 8) 0

def stateWordData (i : Nat) : Nat := stateWordDataBlock0 i

def stateWord (s i : Nat) : Nat := stateWordData ([0,0,0,0,0,2].getD s 0 + i)

def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n+1, ids => wireDAt (ids % 8) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, ids => wireSAt (ids % 8) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) := let p := stateWord s j; stateWiresD (p % 16) (p >>> 4)
def SS (s j : Nat) := let p := stateWord s j; stateWiresS (p % 16) (p >>> 4)

theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAtDataBlock0 (i : Nat) : Nat := [0x7488a4f8,0xe66ccf9c,0x7488a4f8].getD (i % 8) 0

def htAtData (i : Nat) : Nat := htAtDataBlock0 i

def htAt (s i : Nat) : Nat := htAtData ([0,0,0,0,0,2].getD s 0 + i)

def NN (s : Nat) := [0,0,0,0,2,1].getD s 0
def idxH (s h : Nat) := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (ws : List Nat) := idxH s (hk 0 ws)

def cutHitH (_ _ : Nat) (_ : List Nat) : Bool := false
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_10 goalM u ys := by contradiction

def cutHit (s : Nat) (ws : List Nat) := cutHitH s (hk 0 ws) ws
def ori (xs : List Nat) := xs
theorem ori_ok {u ys} (h : RunD dom_10 goalM u ys) : RunD dom_10 goalM u (ori ys) := h
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_10 goalM u ys := cutHitH_sound h
def pool6G : List Nat := []

def Z (s : Nat) := bar dom_10 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s

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
  scr dom_10 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_10 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noCircuit : Lower dom_10 roots_10 goal_10 6 := by
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

end Cert10
theorem low_10 : Lower dom_10 roots_10 goal_10 6 := Cert10.noCircuit

def dom_11 : Nat := 0xffffffff00000000
def roots_11 : List Nat := [0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000]
def goal_11 : Nat := 0xeeeeeee000000000
namespace Cert11

def xsM : List Nat := roots_11.map (· &&& dom_11)
def goalM : Nat := goal_11 &&& dom_11

def pairsG : List (Nat × Nat) := [(32,37),(32,38),(32,41),(32,42),(32,49),(32,50),(33,37),(33,39),(33,41),(33,43),(33,45),(33,49),(33,51),(33,53),(33,57),(34,38),(34,39),(34,42),(34,43),(34,46),(34,50),(34,51),(34,54),(34,58),(35,37),(35,38),(35,39),(35,41),(35,42),(35,43),(35,47),(35,49),(35,50),(35,51),(35,55),(35,59),(36,37),(36,38),(36,39),(36,45),(36,46),(36,53),(36,54),(40,41),(40,42),(40,43),(40,45),(40,46),(40,57),(40,58),(44,37),(44,38),(44,41),(44,42),(44,45),(44,46),(44,47),(44,61),(44,62),(48,49),(48,50),(48,51),(48,53),(48,54),(48,57),(48,58),(52,37),(52,38),(52,49),(52,50),(52,53),(52,54),(52,55),(52,61),(52,62),(56,41),(56,42),(56,49),(56,50),(56,57),(56,58),(56,59),(56,61),(56,62),(60,37),(60,38),(60,41),(60,42),(60,45),(60,46),(60,49),(60,50),(60,53),(60,54),(60,57),(60,58),(60,61),(60,62),(60,63)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_11 goalM s xsM) : False := by
  have hl := run_len h
  change 5 ≤ s + 1 at hl
  omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

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

end Cert11
theorem low_11 : Lower dom_11 roots_11 goal_11 4 := Cert11.noCircuit

-- The full search excludes budgets below ten. Each surviving successor must occur
-- in the next table or be ruled out by one of the twelve cofactor bounds.
def dom_12 : Nat := 0xffffffffffffffff
def roots_12 : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def goal_12 : Nat := 0xeeeeeee0eeeaeac0
namespace Cert12

def xsM : List Nat := roots_12.map (· &&& dom_12)
def goalM : Nat := goal_12 &&& dom_12

def pairsG : List (Nat × Nat) := [(0,6),(0,9),(0,17),(1,7),(1,9),(1,11),(1,13),(1,17),(1,19),(1,21),(1,25),(1,37),(1,41),(1,49),(2,6),(2,7),(2,11),(2,14),(2,19),(2,22),(2,26),(2,38),(2,42),(2,50),(3,6),(3,7),(3,9),(3,11),(3,15),(3,17),(3,19),(3,23),(3,27),(3,39),(3,43),(3,51),(4,6),(4,7),(4,13),(4,14),(4,21),(4,22),(4,37),(4,38),(5,6),(5,7),(5,9),(5,13),(5,15),(5,17),(5,21),(5,23),(5,26),(5,29),(5,37),(5,39),(5,42),(5,45),(5,50),(5,53),(8,9),(8,11),(8,13),(8,14),(8,25),(8,26),(8,41),(8,42),(10,6),(10,9),(10,11),(10,14),(10,15),(10,17),(10,26),(10,27),(10,30),(10,37),(10,42),(10,43),(10,46),(10,50),(10,58),(12,6),(12,9),(12,13),(12,14),(12,15),(12,29),(12,30),(12,45),(12,46),(16,17),(16,19),(16,21),(16,22),(16,25),(16,26),(16,49),(16,50),(18,6),(18,9),(18,17),(18,19),(18,22),(18,23),(18,26),(18,27),(18,30),(18,37),(18,42),(18,50),(18,51),(18,54),(18,58),(20,6),(20,17),(20,21),(20,22),(20,23),(20,29),(20,30),(20,53),(20,54),(24,9),(24,17),(24,25),(24,26),(24,27),(24,29),(24,30),(24,57),(24,58),(28,13),(28,14),(28,21),(28,22),(28,25),(28,26),(28,29),(28,30),(28,31),(28,61),(28,62),(32,37),(32,38),(32,41),(32,42),(32,49),(32,50),(33,9),(33,17),(33,37),(33,39),(33,41),(33,43),(33,45),(33,49),(33,51),(33,53),(33,57),(34,6),(34,38),(34,39),(34,42),(34,43),(34,46),(34,50),(34,51),(34,54),(34,58),(35,6),(35,7),(35,9),(35,11),(35,17),(35,19),(35,26),(35,37),(35,38),(35,39),(35,41),(35,42),(35,43),(35,47),(35,49),(35,50),(35,51),(35,55),(35,59),(36,6),(36,37),(36,38),(36,39),(36,45),(36,46),(36,53),(36,54),(40,9),(40,41),(40,42),(40,43),(40,45),(40,46),(40,57),(40,58),(44,13),(44,14),(44,37),(44,38),(44,41),(44,42),(44,45),(44,46),(44,47),(44,61),(44,62),(48,17),(48,49),(48,50),(48,51),(48,53),(48,54),(48,57),(48,58),(52,21),(52,22),(52,37),(52,38),(52,49),(52,50),(52,53),(52,54),(52,55),(52,61),(52,62),(56,25),(56,26),(56,41),(56,42),(56,49),(56,50),(56,57),(56,58),(56,59),(56,61),(56,62),(60,6),(60,9),(60,17),(60,26),(60,29),(60,30),(60,37),(60,42),(60,45),(60,46),(60,50),(60,53),(60,54),(60,57),(60,58),(60,61),(60,62),(60,63)]

def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := maskP pairsG.length

def wireAtBlock0 (i : Nat) : Nat := (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then [255,3855,21845,52428,65535,983055,0x550055,0xcc00cc].getD (i % 8) 0 else [0xff00ff,0x5050505,0xc0c0c0c,0xf0f0f0f,0x3f3f3f3f,0x44444444,0x55555555,0x5f5f5f5f].getD (i % 8) 0) else (if i < 24 then [0x77777777,0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xfafafafa,0xfcfcfcfc,0xffaaffaa].getD (i % 8) 0 else [0xffccffcc,0xfff0fff0,0xffffaaaa,0xffffcccc,0xfffff0f0,0xffffff00,0xffffffff,0xf0000000f].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [0x5500000055,0xcc000000cc,0xff000000ff,0x50500000505,0xc0c00000c0c,0xf0f00000f0f,0xf0f0000ffff,0x33330000ffff].getD (i % 8) 0 else [0x3f3f00003f3f,0x444400004444,0x555500005555,0x55550000ffff,0x5f5f00005f5f,0x777700007777,0xeeee0000eeee,0xffff0000ffff].getD (i % 8) 0) else (if i < 56 then [0x5000500050005,0xc000c000c000c,0xf000f000f000f,0xf000f00ff00ff,0x33003300ff00ff,0x3f003f003f003f,0x44004400440044,0x55005500550055].getD (i % 8) 0 else [0x55005500ff00ff,0x5f005f005f005f,0x77007700770077,0xee00ee00ee00ee,0xff00ff00ff00ff,0x30303030f0f0f0f,0x404040404040404,0x505050505050505].getD (i % 8) 0))) else (if i < 96 then (if i < 80 then (if i < 72 then [0x50505050f0f0f0f,0x505050555555555,0x707070707070707,0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xe0e0e0e0e0e0e0e,0xf0a0f0a0f0a0f0a,0xf0c0f0c0f0c0f0c].getD (i % 8) 0 else [0xf0f0a0a0f0f0a0a,0xf0f0c0c0f0f0c0c,0xf0f0f000f0f0f00,0xf0f0f0f00000000,0xf0f0f0f0a0a0a0a,0xf0f0f0f0c0c0c0c,0xf0f0f0f0f000f00,0xf0f0f0f0f0f0000].getD (i % 8) 0) else (if i < 88 then [0xf0f0f0f0f0f0f0f,0x1111111155555555,0x1515151515151515,0x3333333333333333,0x333333333333ffff,0x3333333333ff33ff,0x333333333f3f3f3f,0x3333333377777777].getD (i % 8) 0 else [0x333333ff333333ff,0x33333f3f33333f3f,0x3333777733337777,0x333f333f333f333f,0x3377337733773377,0x3737373737373737,0x4444444444444444,0x5050505050505050].getD (i % 8) 0)) else (if i < 112 then (if i < 104 then [0x5454545454545454,0x5544554455445544,0x5550555055505550,0x5555444455554444,0x5555505055555050,0x5555550055555500,0x5555555500000000,0x5555555544444444].getD (i % 8) 0 else [0x5555555550505050,0x5555555555005500,0x5555555555550000,0x5555555555555555,0x8888888888888888,0xa0a0a0a0a0a0a0a0,0xaa80aa80aa80aa80,0xaaa0aaa0aa00aa00].getD (i % 8) 0) else (if i < 120 then [0xaaa0aaa0aaa0aaa0,0xaaaa8080aaaa8080,0xaaaaa0a0aaaa0000,0xaaaaa0a0aaaaa0a0,0xaaaaaa00aaaaaa00,0xaaaaaaa0aaaaaa00,0xaaaaaaa0aaaaaaa0,0xaaaaaaaa00000000].getD (i % 8) 0 else [0xaaaaaaaa80808080,0xaaaaaaaaa0a0a0a0,0xaaaaaaaaaa00aa00,0xaaaaaaaaaaaa0000,0xaaaaaaaaaaaaaa00,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaff,0xaaaaaaaaaaaaffff].getD (i % 8) 0))))

def wireAtBlock1 (i : Nat) : Nat := (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then [0xaaaaaaaaaaffaaff,0xaaaaaaaaafafafaf,0xaaaaaaaaeeeeeeee,0xaaaaaaafaaaaaaaf,0xaaaaaaeeaaaaaaee,0xaaaaaaffaaaaaaff,0xaaaaafafaaaaafaf,0xaaafaaafaaafaaaf].getD (i % 8) 0 else [0xaeaeaeaeaeaeaeae,0xb3b3b3b3b3b3b3b3,0xbbbbbbbb33333333,0xbbbbbbbbbbbbbbbb,0xc0c0c0c0c0c0c0c0,0xc8c8c8c888888888,0xc8c8c8c8c0c0c0c0,0xc8c8c8c8c8c8c8c8].getD (i % 8) 0) else (if i < 152 then [0xcc80cc80cc80cc80,0xcc88cc88cc00cc00,0xcc88cc88cc88cc88,0xccc0ccc0cc00cc00,0xccc0ccc0ccc0ccc0,0xccc8ccc8ccc8ccc8,0xcccc8080cccc8080,0xcccc8888cccc0000].getD (i % 8) 0 else [0xcccc8888cccc8888,0xccccc0c0cccc0000,0xccccc0c0ccccc0c0,0xccccc8c8ccccc8c8,0xcccccc00cccccc00,0xcccccc88cccccc88,0xccccccc0ccccccc0,0xccccccc8ccccccc8].getD (i % 8) 0)) else (if i < 176 then (if i < 168 then [0xcccccccc00000000,0xcccccccc80808080,0xcccccccc88888888,0xccccccccc0c0c0c0,0xccccccccc8c8c8c8,0xcccccccccc00cc00,0xcccccccccc88cc88,0xccccccccccc0ccc0].getD (i % 8) 0 else [0xccccccccccc8ccc8,0xcccccccccccc0000,0xcccccccccccc8888,0xccccccccccccc0c0,0xccccccccccccc8c8,0xcccccccccccccc00,0xccccccccccccccc0,0xcccccccccccccccc].getD (i % 8) 0) else (if i < 184 then [0xcececececececece,0xe0e0e0e0a0a0a0a0,0xe0e0e0e0e0e0e0e0,0xeae0eae0eae0eae0,0xeaeae0e0eaeae0e0,0xeaeaeaea00000000,0xeaeaeaeac0c0c0c0,0xeaeaeaeaeaeaeaea].getD (i % 8) 0 else [0xececececa0a0a0a0,0xeee0eee0ee00ee00,0xeee0eee0eee0eee0,0xeeeaeeeaeeeaeeea,0xeeeceeeceecceecc,0xeeeee0e0eeee0000,0xeeeee0e0eeeee0e0,0xeeeeeaeaeeeeeaea].getD (i % 8) 0))) else (if i < 224 then (if i < 208 then (if i < 200 then [0xeeeeececeeeecccc,0xeeeeee00eeeeee00,0xeeeeeeaaeeeeeeaa,0xeeeeeecceeeeeecc,0xeeeeeeee00000000,0xeeeeeeeeaa00aa00,0xeeeeeeeeaaaa0000,0xeeeeeeeeaaaaaaaa].getD (i % 8) 0 else [0xeeeeeeeecccccccc,0xeeeeeeeee0e0e0e0,0xeeeeeeeeeaeaeaea,0xeeeeeeeeee00ee00,0xeeeeeeeeeeaaeeaa,0xeeeeeeeeeecceecc,0xeeeeeeeeeeee0000,0xeeeeeeeeeeeeaaaa].getD (i % 8) 0) else (if i < 216 then [0xeeeeeeeeeeeecccc,0xeeeeeeeeeeeeeeee,0xf0a0f0a0f0a0f0a0,0xf0e0f0e0f0e0f0e0,0xf0f0a0a0f0f0a0a0,0xf0f0e0e0f0f0e0e0,0xf0f0f000f0f0f000,0xf0f0f0f000000000].getD (i % 8) 0 else [0xf0f0f0f080808080,0xf0f0f0f0a0a0a0a0,0xf0f0f0f0c0c0c0c0,0xf0f0f0f0e0e0e0e0,0xf0f0f0f0f000f000,0xf0f0f0f0f0c0f0c0,0xf0f0f0f0f0f00000,0xf0f0f0f0f0f0c0c0].getD (i % 8) 0)) else (if i < 240 then (if i < 232 then [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0ffff,0xf0f0f0f0f0fff0ff,0xf0f0f0f0f5f5f5f5,0xf0f0f0f0fcfcfcfc,0xf0f0f0fff0f0f0ff,0xf0f0f5f5f0f0f5f5,0xf0f5f0f5f0f5f0f5].getD (i % 8) 0 else [0xf3f3f3f333333333,0xf3f3f3f3f3f3f3f3,0xf4f4f4f4f4f4f4f4,0xf8f8f8f888888888,0xf8f8f8f8f8f8f8f8,0xfac8fac8fac8fac8,0xfafac8c8fafac8c8,0xfafafa00fafafa00].getD (i % 8) 0) else (if i < 248 then [0xfafafaf0fafafaf0,0xfafafafa00000000,0xfafafafaaaaaaaaa,0xfafafafac8c8c8c8,0xfafafafaf0f0f0f0,0xfafafafafa00fa00,0xfafafafafafa0000,0xfafafafafafafafa].getD (i % 8) 0 else [0xfbfbfbfbfbfbfbfb,0xfca8fca8fca8fca8,0xfcf8fcf8fcf8fcf8,0xfcfca8a8fcfca8a8,0xfcfcf8f8fcfcf8f8,0xfcfcfc00fcfcfc00,0xfcfcfcf0fcfcfcf0,0xfcfcfcfc00000000].getD (i % 8) 0))))

def wireAtBlock2 (i : Nat) : Nat := (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then [0xfcfcfcfca8a8a8a8,0xfcfcfcfcf0f0f0f0,0xfcfcfcfcf8f8f8f8,0xfcfcfcfcfc00fc00,0xfcfcfcfcfcf0fcf0,0xfcfcfcfcfcfc0000,0xfcfcfcfcfcfcf0f0,0xfcfcfcfcfcfcfcfc].getD (i % 8) 0 else [0xfefefefe00000000,0xfefefefefafafafa,0xfefefefefefefefe,0xff00ff00ff00aa00,0xff00ff00ff00ff00,0xff00ff00ff00ff55,0xff00ff00ff00ffff,0xff00ff00ff0fff0f].getD (i % 8) 0) else (if i < 280 then [0xff00ff00ff55ff55,0xff00ff00ffccffcc,0xff00ff0fff00ff0f,0xff00ff55ff00ff55,0xff05ff05ff05ff05,0xff0cff0cff0cff0c,0xff33ff33ff33ff33,0xff44ff44ff44ff44].getD (i % 8) 0 else [0xff50ff50ff50ff50,0xff88ff88ff88ff88,0xffa0ffa0ffa0ffa0,0xffaacc88ffaacc88,0xffaaf0a0ffaaf0a0,0xffaaff80ffaaff80,0xffaaffa0ffaaff00,0xffaaffaa00000000].getD (i % 8) 0)) else (if i < 304 then (if i < 296 then [0xffaaffaacc88cc88,0xffaaffaaf0a0f0a0,0xffaaffaaff00ff00,0xffaaffaaffaa0000,0xffaaffaaffaaffaa,0xffbbffbbffbbffbb,0xffc0ffc000000000,0xffc0ffc0ffc0ffc0].getD (i % 8) 0 else [0xffc8ffc8ffc8ffc8,0xffccaa88ffccaa88,0xffccf0c0ffccf0c0,0xffccff88ffccff88,0xffccffc0ffccffc0,0xffccffccaa88aa88,0xffccffccf0c0f0c0,0xffccffccff00ff00].getD (i % 8) 0) else (if i < 312 then [0xffccffccff88ff88,0xffccffccffc0ffc0,0xffccffccffcc0000,0xffccffccffccff00,0xffccffccffccffcc,0xffeaffeaffeaffea,0xffeeffee00000000,0xffeeffeeffaaffaa].getD (i % 8) 0 else [0xffeeffeeffeeffee,0xfff0aaa0fff0aaa0,0xfff0ccc0fff0ccc0,0xfff0fff000000000,0xfff0fff0aaa0aaa0,0xfff0fff0c0c0c0c0,0xfff0fff0ccc0ccc0,0xfff0fff0ff00ff00].getD (i % 8) 0))) else (if i < 352 then (if i < 336 then (if i < 328 then [0xfff0fff0ff80ff80,0xfff0fff0ffc0ffc0,0xfff0fff0fff00000,0xfff0fff0fff0ff00,0xfff0fff0fff0fff0,0xfff3fff3fff3fff3,0xfff8fff8fff8fff8,0xfffafffaffaaffaa].getD (i % 8) 0 else [0xfffafffafff0fff0,0xfffafffafffafffa,0xfffcfffc00000000,0xfffcfffcffccffcc,0xfffcfffcfff0fff0,0xfffcfffcfffcfffc,0xffff0000ffaa0000,0xffff0000ffff0000].getD (i % 8) 0) else (if i < 344 then [0xffff0000ffff0055,0xffff0000ffff00ff,0xffff0000ffff0f0f,0xffff0000ffff5555,0xffff0000ffffcccc,0xffff000fffff000f,0xffff0055ffff0055,0xffff0505ffff0505].getD (i % 8) 0 else [0xffff0c0cffff0c0c,0xffff3333ffff3333,0xffff4444ffff4444,0xffff5050ffff5050,0xffff8888ffff8888,0xffffa0a0ffffa0a0,0xffffaa80ffffaa80,0xffffaaa0ffffaa00].getD (i % 8) 0)) else (if i < 368 then (if i < 360 then [0xffffaaaa00000000,0xffffaaaacccc8888,0xffffaaaaf0f0a0a0,0xffffaaaaff00aa00,0xffffaaaaffff0000,0xffffaaaaffffaaaa,0xffffbbbbffffbbbb,0xffffc0c000000000].getD (i % 8) 0 else [0xffffc0c0ffffc0c0,0xffffc8c8ffffc8c8,0xffffcc88ffffcc88,0xffffccc0ffffccc0,0xffffccccaaaa8888,0xffffccccf0f0c0c0,0xffffccccff00cc00,0xffffccccffff0000].getD (i % 8) 0) else (if i < 376 then [0xffffccccffff8888,0xffffccccffffc0c0,0xffffccccffffcc00,0xffffccccffffcccc,0xffffeaeaffffeaea,0xffffeeee00000000,0xffffeeeeffffaaaa,0xffffeeeeffffeeee].getD (i % 8) 0 else [0xfffff0f000000000,0xfffff0f0aaaaa0a0,0xfffff0f0c0c0c0c0,0xfffff0f0ccccc0c0,0xfffff0f0ff00f000,0xfffff0f0ffff0000,0xfffff0f0ffff8080,0xfffff0f0ffffc0c0].getD (i % 8) 0))))

def wireAtBlock3 (i : Nat) : Nat := (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then [0xfffff0f0fffff000,0xfffff0f0fffff0f0,0xfffff3f3fffff3f3,0xfffff8f8fffff8f8,0xfffffafaffffaaaa,0xfffffafafffff0f0,0xfffffafafffffafa,0xfffffcfc00000000].getD (i % 8) 0 else [0xfffffcfcffffcccc,0xfffffcfcfffff0f0,0xfffffcfcfffffcfc,0xffffff0000000000,0xffffff00aaaaaa00,0xffffff00cccccc00,0xffffff00f0f0f000,0xffffff00ffffff00].getD (i % 8) 0) else (if i < 408 then [0xffffff33ffffff33,0xffffff88ffffff88,0xffffffa0ffffffa0,0xffffffaa00000000,0xffffffaaffffff00,0xffffffaaffffffaa,0xffffffc0ff00ff00,0xffffffc0ffff0000].getD (i % 8) 0 else [0xffffffc0ffffffc0,0xffffffccffffff00,0xffffffccffffffcc,0xfffffff000000000,0xfffffff0f0f0f0f0,0xfffffff0fafafaf0,0xfffffff0ff00ff00,0xfffffff0ffc0ffc0].getD (i % 8) 0)) else (if i < 432 then (if i < 424 then [0xfffffff0ffff0000,0xfffffff0ffffc0c0,0xfffffff0ffffff00,0xfffffff0fffffff0,0xfffffffafffffffa,0xffffffff00000000,0xffffffff0000000f,0xffffffff00000055].getD (i % 8) 0 else [0xffffffff000000cc,0xffffffff000000ff,0xffffffff00000f0f,0xffffffff00005555,0xffffffff000f000f,0xffffffff00550055,0xffffffff05050505,0xffffffff0a0a0a0a].getD (i % 8) 0) else (if i < 440 then [0xffffffff0c0c0c0c,0xffffffff33333333,0xffffffff44444444,0xffffffff50505050,0xffffffff88888888,0xffffffffa0a0a0a0,0xffffffffaa80aa80,0xffffffffaaaa8080].getD (i % 8) 0 else [0xffffffffaaaaaa00,0xffffffffaaaaaaaa,0xffffffffbbbbbbbb,0xffffffffc0c0c0c0,0xffffffffc8c8c8c8,0xffffffffcc88cc88,0xffffffffccc0ccc0,0xffffffffcccc8888].getD (i % 8) 0))) else (if i < 480 then (if i < 464 then (if i < 456 then [0xffffffffccccc0c0,0xffffffffcccccc00,0xffffffffcccccccc,0xffffffffeaeaeaea,0xffffffffeeeeeeee,0xfffffffff0f0f000,0xfffffffff0f0f0f0,0xfffffffff3f3f3f3].getD (i % 8) 0 else [0xfffffffff8f8f8f8,0xfffffffffac8fac8,0xfffffffffafac8c8,0xfffffffffafafa00,0xfffffffffafafafa,0xfffffffffcfcfcfc,0xffffffffff00ff00,0xffffffffff33ff33].getD (i % 8) 0) else (if i < 472 then [0xffffffffff88ff88,0xffffffffffa0ffa0,0xffffffffffaaffaa,0xffffffffffc0ffc0,0xffffffffffccffcc,0xfffffffffff0fff0,0xfffffffffffafffa,0xffffffffffff0000].getD (i % 8) 0 else [0xffffffffffff3333,0xffffffffffff8888,0xffffffffffffa0a0,0xffffffffffffaaaa,0xffffffffffffc0c0,0xffffffffffffcccc,0xfffffffffffff0f0,0xfffffffffffffafa].getD (i % 8) 0)) else [0xffffffffffffff00,0xffffffffffffffaa,0xfffffffffffffff0].getD (i % 8) 0))

def wireAt (i : Nat) : Nat := (if i < 256 then (if i < 128 then wireAtBlock0 i else wireAtBlock1 i) else (if i < 384 then wireAtBlock2 i else wireAtBlock3 i))

def p1AtBlock0 (i : Nat) : Nat := (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then [0xfffffffffffffff,(limbWord [0x7ffff,0xf000000fffffffff]),(limbWord [0xfffffff,0xf0000ff000ffc007]),(limbWord [0x7fff0,0xfffffc000]),(limbWord [0xfffffff,0xffffffffffffffff]),(limbWord [0x7fffff0000000,0xfffffffff]),(limbWord [0xffffffff0000000,0xff000ffc007]),(limbWord [0x7fff000000000,0xfffffc000])].getD (i % 8) 0 else [(limbWord [0xffffffff0000000,0xfffffffffffffff]),(limbWord [0x1f,0xf007fffff007ffff,0xf000000000ffc007]),(limbWord [0x7fff00007fff0,0xfffffc000]),(limbWord [0x1f,0xf007fffff007ffff,0xf000000fffffffff]),(limbWord [0xffff,0xffffffffffffffff,0xffffffffffffffff]),(limbWord [0x7fff00007fff0,0xffc000]),(limbWord [0xffff,0xffffffffffffffff,0xf0000ff000ffc007]),(limbWord [0xffff,0xffffffffffffffff,0xf0000fffffffffff])].getD (i % 8) 0) else (if i < 24 then [(limbWord [0xffff,0xffffffffffffffff,0xfffffff000ffffff]),0xffff00fff003ff8,(limbWord [0x7fff00007fff0,0xfffffc000]),(limbWord [0x7fff00007fff0,0xffff00ffffffff8]),(limbWord [0xffe0,0xff800000ff80000,0xffffff000000000]),(limbWord [0xffe0,0xff800000ff80000,0xfffffffff003ff8]),(limbWord [0xffe0,0xffffff00ffffff0,0xfffffffffffc000]),(limbWord [0xffff,0xf00000000fffffff,0xfffff00fff003ff8])].getD (i % 8) 0 else [(limbWord [0xffff,0xf007fff00fffffff,0xf000000fffffc000]),(limbWord [0xffff,0xfff800000fffffff,0xfffffff000000000]),(limbWord [0xffff,0xfffffffff0000000,0xffff00fff003ff8]),(limbWord [0xffff,0xfffffffff007fff0,0xfffffc000]),(limbWord [0xffff,0xfffffffffff80000,0xffffff000000000]),(limbWord [0xffff,0xffffffffffffffff,0xf000000000000000]),(limbWord [0xffff,0xffffffffffffffff,0xffffffffffffffff]),(limbWord [0x3fffffffffff0000,0x0,0xfffffffff])].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [(limbWord [0x3f,0xc00007fe003f0000,0x0,0xff000ffc007]),(limbWord [0x3ffffffe00000000,0x0,0xfffffc000]),(limbWord [0x3f,0xffffffffffff0000,0x0,0xfffffffffffffff]),(limbWord [0x3fc0,0x7fe003f0000,0x7ffff,0xf000000000ffc007]),(limbWord [0x3ffffffe00000000,0x7fff0,0xfffffc000]),(limbWord [0x3fc0,0x3fffffffffff0000,0x7ffff,0xf000000fffffffff]),(limbWord [0x3fc0,0x3fffffffffff0000,0xfffffff,0xffffffffffffffff]),(limbWord [0x1ffffff,0xc0000001ffff0000,0xfffffff,0xffffffffffffffff])].getD (i % 8) 0 else [(limbWord [0x1ffffff,0xffffffffffff0000,0xfffffff,0xffffffffffffffff]),(limbWord [0x7fe00000000,0x7fff0,0xffc000]),(limbWord [0x1ffffff,0xc00007fe003f0000,0xfffffff,0xf0000ff000ffc007]),(limbWord [0x1ffffff,0xc00007fe003f0000,0xfffffff,0xffffffffffffffff]),(limbWord [0x1ffffff,0xffffffffffff0000,0xfffffff,0xf0000fffffffffff]),(limbWord [0x1ffffff,0xc00007ffffff0000,0xfffffff,0xfffffff000ffffff]),(limbWord [0x3fffffffffc00000,0x7fff0,0xffff00ffffffff8]),(limbWord [0x1ffffff,0xffffffffffff0000,0xfffffff,0xffffffffffffffff])].getD (i % 8) 0) else (if i < 56 then [(limbWord [0x1fe000000,0x7fe003f0000,0x7fffff0000000,0xffc007]),(limbWord [0x3ffffffe00000000,0x7fff000000000,0xfffffc000]),(limbWord [0x1fe000000,0x3fffffffffff0000,0x7fffff0000000,0xfffffffff]),(limbWord [0x1fe000000,0x3fffffffffff0000,0xffffffff0000000,0xfffffffffffffff]),(limbWord [0xffffe00003f,0xc0000001ffff0000,0xffffffff0000000,0xfffffffffffffff]),(limbWord [0xffffe00003f,0xffffffffffff0000,0xffffffff0000000,0xfffffffffffffff]),(limbWord [0x7fe00000000,0x7fff000000000,0xffc000]),(limbWord [0xffffe00003f,0xc00007fe003f0000,0xffffffff0000000,0xff000ffc007])].getD (i % 8) 0 else [(limbWord [0xffffe00003f,0xc00007fe003f0000,0xffffffff0000000,0xfffffffffffffff]),(limbWord [0xffffe00003f,0xffffffffffff0000,0xffffffff0000000,0xfffffffffff]),(limbWord [0xffffe00003f,0xc00007ffffff0000,0xffffffff0000000,0xffffff000ffffff]),(limbWord [0x3fffffffffc00000,0x7fff000000000,0xffff00ffffffff8]),(limbWord [0xffffe00003f,0xffffffffffff0000,0xffffffff0000000,0xfffffffffffffff]),(limbWord [0x7ff001fe003fc0,0x1ffff001f,0xf007fffff007ffff,0xf000000fffffffff]),(limbWord [0x7fe00000000,0x7fff00007fff0,0xffc000]),(limbWord [0x7ff001fe003fc0,0x7fe003f001f,0xf007fffff007ffff,0xf000000000ffc007])].getD (i % 8) 0))) else (if i < 96 then (if i < 80 then (if i < 72 then [(limbWord [0x7ff001fe003fc0,0x7fe003f001f,0xf007fffff007ffff,0xf000000fffffffff]),(limbWord [0x7ff001fe003fc0,0x7fe003fffff,0xffffffffffffffff,0xf0000ff000ffc007]),(limbWord [0x7ff001fe003fc0,0x7ffffff001f,0xf007fffff007ffff,0xf000000000ffffff]),(limbWord [0x3ffff801ffc00000,0x0,0xfff003ff8]),(limbWord [0x3ffffffe00000000,0x7fff00007fff0,0xfffffc000]),(limbWord [0x3fffffffffc00000,0x7fff00007fff0,0xffffffff8]),(limbWord [0x7ff00000003fc0,0x3ffff801ffc0001f,0xf00000000007ffff,0xf000000fff003ff8]),(limbWord [0x7ff00000003fc0,0x3ffffffe0000001f,0xf007fff00007ffff,0xf000000fffffc000])].getD (i % 8) 0 else [(limbWord [0x7ff001fe000000,0x3ffff801ffc0001f,0xf007fffff0000000,0xfff003ff8]),(limbWord [0x7ff001fe000000,0x3ffffffe0000001f,0xf007fffff007fff0,0xfffffc000]),(limbWord [0x7ff001fe003fc0,0x1f,0xf007fffff007ffff,0xf000000000000000]),(limbWord [0x7ff001fe003fc0,0x3fffffffffff0000,0x0,0x0]),(limbWord [0x7ff001fe003fc0,0x3fffffffffff0000,0x0,0xfff003ff8]),(limbWord [0x7ff001fe003fc0,0x3fffffffffff0000,0x7fff00007fff0,0xfffffc000]),(limbWord [0x7ff001fe003fc0,0x3fffffffffff001f,0xf00000000007ffff,0xf000000000000000]),(limbWord [0x7ff001fe003fc0,0x3fffffffffff001f,0xf007fffff0000000,0x0])].getD (i % 8) 0) else (if i < 88 then [(limbWord [0x7ff001fe003fc0,0x3fffffffffff001f,0xf007fffff007ffff,0xf000000fffffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xc0000000003fffff,0xffffffffffffffff,0xf0000ff000ffc007]),(limbWord [0x1ff,0xffffffffffffffff,0xc00007fe003fffff,0xffffffffffffffff,0xf0000ff000ffc007]),(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xfff8000ffff8000f,0xfffffff000003fff]),(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xfff8000fffffffff,0xffffffffffffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xfffffffffff8000f,0xffffffffffffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xffffffffffffffff,0xffffffffffffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xffffffffffffffff,0xfffffff000ffffff])].getD (i % 8) 0 else [(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfff8000ffff8000f,0xffffffffffffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfff8000fffffffff,0xffffffffffffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xc00007ffffffffff,0xfff8000fffffffff,0xfffffff000ffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfffffffffff8000f,0xffffffffffffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xc00007ffffffffff,0xfffffffffff8000f,0xfffffff000ffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xc00007ffffffffff,0xffffffffffffffff,0xfffffff000ffffff]),(limbWord [0x7fe00000000,0x7fff00007fff0,0xffc000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00000000000ffe0,0xff800000ff80000,0xff000000000])].getD (i % 8) 0)) else (if i < 112 then (if i < 104 then [(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00007fe0000ffe0,0xffffff00ffffff0,0xff000ffc000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x7fe0000ffff,0xf007fff00fffffff,0xf000000000ffc000]),(limbWord [0x1ff,0xfffffffe01ffffff,0xc00000000000ffff,0xfff800000fffffff,0xf0000ff000000000]),(limbWord [0x1ff,0xfffffffffe000000,0x7fe0000ffff,0xfffffffff007fff0,0xffc000]),(limbWord [0x1ff,0xffffffffffffc03f,0xc00000000000ffff,0xfffffffffff80000,0xff000000000]),(limbWord [0x1ff,0xffffffffffffffc0,0xffff,0xffffffffffffffff,0xf000000000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xc00007fe003f0000,0x0,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xc00007fe003f0000,0x7fff00007fff0,0xffc000])].getD (i % 8) 0 else [(limbWord [0x1ff,0xffffffffffffffff,0xc00007fe003fffe0,0xff800000ff80000,0xff000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xc00007fe003fffff,0xf00000000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xc00007fe003fffff,0xfffffffff0000000,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xc00007fe003fffff,0xffffffffffffffff,0xf0000ff000ffc007]),(limbWord [0x3ffff80000000000,0x0,0xfff000000]),0xffff00000000000,0,0].getD (i % 8) 0) else (if i < 120 then [0xffff00000000000,0,0,0xffff00000000000,0,0,0xffff00000000000,(limbWord [0x3ffff801ffc00000,0x0,0x0])].getD (i % 8) 0 else [(limbWord [0x3ffff801ffc00000,0x0,0x0]),(limbWord [0x3ffff801ffc00000,0x0,0xffff00000000000]),(limbWord [0x3ffff801ffc00000,0x0,0x0]),(limbWord [0x3ffff801ffc00000,0x0,0x0]),(limbWord [0x3ffff801ffc00000,0x0,0x0]),(limbWord [0x3ffff801ffc00000,0x0,0xffff00fff003ff8]),(limbWord [0x3ffff801ffc00000,0x0,0xfffffffffffffff]),(limbWord [0x3ffff801ffc00000,0xfffffff,0xffffffffffffffff])].getD (i % 8) 0))))

def p1AtBlock1 (i : Nat) : Nat := (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then [(limbWord [0x3ffff801ffc00000,0xffffffff0000000,0xfffffffffffffff]),(limbWord [0x3ffff801ffc0001f,0xf007fffff007ffff,0xfffff00fffffffff]),(limbWord [0x3ffff801ffc00000,0x7fff00007fff0,0xffff00ffffffff8]),(limbWord [0x3fffffffffff0000,0x0,0xffff00fffffffff]),(limbWord [0x3fffffffffc00000,0x0,0xffff00ffffffff8]),(limbWord [0x3f,0xffffffffffff0000,0x0,0xfffffffffffffff]),(limbWord [0x3fc0,0x3fffffffffff0000,0x7ffff,0xfffff00fffffffff]),(limbWord [0x1fe000000,0x3fffffffffff0000,0x7fffff0000000,0xffff00fffffffff])].getD (i % 8) 0 else [(limbWord [0x3fffffffffc00000,0x7fff00007fff0,0xffff00ffffffff8]),(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xfff8000ffff8000f,0xfffffff000003fff]),(limbWord [0x1ff,0xffffffffffffffff,0xfffff801ffffffff,0xfff8000ffff8000f,0xfffffff000003fff]),(limbWord [0x1ff,0xffffffffffffffff,0xfffff801ffffffff,0xfff8000ffff8000f,0xffffffffff003fff]),0,(limbWord [0x3ffff80000000000,0x0,0xfff000000]),(limbWord [0x3ffff80000000000,0x0,0x0]),(limbWord [0x3ffff80000000000,0x0,0xfff000000])].getD (i % 8) 0) else (if i < 152 then [(limbWord [0x7fff0,0x0]),(limbWord [0x3ffff80000000000,0x7fff0,0x0]),(limbWord [0x3ffff80000000000,0x7fff0,0xfff000000]),(limbWord [0x7fff0,0x0]),(limbWord [0x7fff0,0x0]),(limbWord [0x3ffff80000000000,0x7fff0,0xfff000000]),(limbWord [0x7fff000000000,0x0]),(limbWord [0x3ffff80000000000,0x7fff000000000,0x0])].getD (i % 8) 0 else [(limbWord [0x3ffff80000000000,0x7fff000000000,0xfff000000]),(limbWord [0x7fff000000000,0x0]),(limbWord [0x7fff000000000,0x0]),(limbWord [0x3ffff80000000000,0x7fff000000000,0xfff000000]),(limbWord [0x7fff00007fff0,0x0]),(limbWord [0x3ffff80000000000,0x7fff00007fff0,0xfff000000]),(limbWord [0x7fff00007fff0,0x0]),(limbWord [0x3ffff80000000000,0x7fff00007fff0,0xfff000000])].getD (i % 8) 0)) else (if i < 176 then (if i < 168 then [(limbWord [0x3ffffffe00000000,0x0,0x0]),(limbWord [0x3ffffffe00000000,0x0,0x0]),(limbWord [0x3ffffffe00000000,0x0,0xfff000000]),(limbWord [0x3ffffffe00000000,0x0,0x0]),(limbWord [0x3ffffffe00000000,0x0,0xfff000000]),(limbWord [0x3ffffffe00000000,0x7fff0,0x0]),(limbWord [0x3ffffffe00000000,0x7fff0,0xfff000000]),(limbWord [0x3ffffffe00000000,0x7fff0,0x0])].getD (i % 8) 0 else [(limbWord [0x3ffffffe00000000,0x7fff0,0xfff000000]),(limbWord [0x3ffffffe00000000,0x7fff000000000,0x0]),(limbWord [0x3ffffffe00000000,0x7fff000000000,0xfff000000]),(limbWord [0x3ffffffe00000000,0x7fff000000000,0x0]),(limbWord [0x3ffffffe00000000,0x7fff000000000,0xfff000000]),(limbWord [0x3ffffffe00000000,0x7fff00007fff0,0x0]),(limbWord [0x3ffffffe00000000,0x7fff00007fff0,0x0]),(limbWord [0x3ffffffe00000000,0x7fff00007fff0,0xfffffc000])].getD (i % 8) 0) else (if i < 184 then [(limbWord [0x3fffffffffc00000,0x7fff00007fff0,0xffffffff8]),0xffff00000000000,0xffff00000000000,0xffff00000000000,0xffff00000000000,(limbWord [0x3ffff801ffc00000,0x0,0x0]),(limbWord [0x3ffff801ffc00000,0x0,0x0]),(limbWord [0x3ffff801ffc00000,0x0,0xffff00fff003ff8])].getD (i % 8) 0 else [(limbWord [0x3ffffffe00000000,0x0,0xffff00000000000]),(limbWord [0x7fff0,0x0]),(limbWord [0x7fff0,0xffff00000000000]),(limbWord [0x3ffff801ffc00000,0x7fff0,0xffff00fff003ff8]),(limbWord [0x3ffffffe00000000,0x7fff00007fff0,0xfffffc000]),(limbWord [0x7fff000000000,0x0]),(limbWord [0x7fff000000000,0xffff00000000000]),(limbWord [0x3ffff801ffc00000,0x7fff000000000,0xffff00fff003ff8])].getD (i % 8) 0))) else (if i < 224 then (if i < 208 then (if i < 200 then [(limbWord [0x3ffffffe00000000,0x7fff00007fff0,0xfffffc000]),(limbWord [0x7fff00007fff0,0x0]),(limbWord [0x3ffff801ffc00000,0x7fff00007fff0,0xffff00fff003ff8]),(limbWord [0x3ffffffe00000000,0x7fff00007fff0,0xfffffc000]),(limbWord [0x3fffffffffc00000,0x0,0x0]),(limbWord [0x3fffffffffc00000,0x0,0x0]),(limbWord [0x3fffffffffc00000,0x0,0x0]),(limbWord [0x3fffffffffc00000,0x0,0xffff00fff003ff8])].getD (i % 8) 0 else [(limbWord [0x3fffffffffc00000,0x7fff00007fff0,0xfffffc000]),(limbWord [0x3fffffffffc00000,0x0,0xffff00000000000]),(limbWord [0x3fffffffffc00000,0x0,0xffff00fff003ff8]),(limbWord [0x3fffffffffc00000,0x7fff0,0x0]),(limbWord [0x3fffffffffc00000,0x7fff0,0xffff00fff003ff8]),(limbWord [0x3fffffffffc00000,0x7fff00007fff0,0xfffffc000]),(limbWord [0x3fffffffffc00000,0x7fff000000000,0x0]),(limbWord [0x3fffffffffc00000,0x7fff000000000,0xffff00fff003ff8])].getD (i % 8) 0) else (if i < 216 then [(limbWord [0x3fffffffffc00000,0x7fff00007fff0,0xfffffc000]),(limbWord [0x3fffffffffc00000,0x7fff00007fff0,0xffff00ffffffff8]),(limbWord [0x1ff,0xff80000001ffc000,0xffe0,0xff80000,0xffff00000000000]),(limbWord [0x1ff,0xff80000001ffc000,0xffe0,0xff80000,0xffff00000000000]),(limbWord [0x1ff,0xff800ffe00000000,0xffe0,0xff8000000000000,0xffff00000000000]),(limbWord [0x1ff,0xff800ffe00000000,0xffe0,0xff8000000000000,0xffff00000000000]),(limbWord [0x1ff,0xff800ffe01ffc000,0xffe0,0xff800000ff80000,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc000000000000000,0x0,0x0])].getD (i % 8) 0 else [(limbWord [0x1ff,0xff800ffe01ffc03f,0xc000000000000000,0x0,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc000000000000000,0x0,0xffff00000000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc000000000000000,0x0,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc000000000000000,0x0,0xffff00000000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00000000000ffe0,0xff80000,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00000000000ffe0,0xff80000,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00000000000ffe0,0xff8000000000000,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00000000000ffe0,0xff8000000000000,0x0])].getD (i % 8) 0)) else (if i < 240 then (if i < 232 then [(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00000000000ffe0,0xff800000ff80000,0xffffff000000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00000000000ffe0,0xff800000fffffff,0xffffffffffffffff]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00000000000ffe0,0xffffffffff80000,0xfffffffffffffff]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00000000000ffff,0xffffffffffffffff,0xfffffff000ffc007]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00000000000ffe0,0xffffff00ffffff0,0xfffffffffffc000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xffffffffffffffe0,0xff800000ff80000,0xfffffffffffffff]),(limbWord [0x1ff,0xff800ffe01ffffff,0xc00007fe003fffe0,0xff800000fffffff,0xfffffff000ffc007]),(limbWord [0x1ff,0xff800fffffffc03f,0xc00007fe003fffe0,0xffffffffff80000,0xffffff000ffc007])].getD (i % 8) 0 else [(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xfff8000ffff8000f,0xfffffff000003fff]),(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xfff8000ffff8000f,0xfffffff000003fff]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00007fe0000ffe0,0xffffff00ffffff0,0xffffff000ffc000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffff80000000000,0x0,0xfff000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffff8000000ffe0,0xff800000ff80000,0xfffffffff000000]),(limbWord [0x1ff,0xff80000001ffc000,0x3ffff8000000ffe0,0xff80000,0xfff000000]),(limbWord [0x1ff,0xff800ffe00000000,0x3ffff8000000ffe0,0xff8000000000000,0xfff000000]),(limbWord [0x1ff,0xff800ffe01ffc000,0xffe0,0xff800000ff80000,0x0])].getD (i % 8) 0) else (if i < 248 then [(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00000000000ffe0,0xff800000ff80000,0xffffff000000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffff801ffc00000,0x0,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffff801ffc00000,0x0,0xffff00fff003ff8]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffff801ffc00000,0x0,0xfff000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffff801ffc0ffe0,0xff800000ff80000,0xffffff000000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffff801ffc0ffe0,0xff80000,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffff801ffc0ffe0,0xff8000000000000,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffff801ffc0ffe0,0xff800000ff80000,0xfffffffff003ff8])].getD (i % 8) 0 else [(limbWord [0x1ff,0xffffffffffffffff,0xfffff801ffffffff,0xfff8000ffff8000f,0xffffffffff003fff]),(limbWord [0x1ff,0xff80000001ffc000,0x3ffff8000000ffe0,0xffffff0,0xffff00fff000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffff8000000ffe0,0xff800000ffffff0,0xfffffffff000000]),(limbWord [0x1ff,0xff800ffe00000000,0x3ffff8000000ffe0,0xffffff000000000,0xffff00fff000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffff8000000ffe0,0xffffff00ff80000,0xfffffffff000000]),(limbWord [0x1ff,0xff800ffe01ffc000,0xffe0,0xffffff00ffffff0,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xc00000000000ffe0,0xffffff00ffffff0,0xffffff000000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffffffe00000000,0x0,0x0])].getD (i % 8) 0))))

def p1AtBlock2 (i : Nat) : Nat := (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then [(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffffffe00000000,0x0,0xffff00fff000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffffffe0000ffe0,0xff800000ff80000,0xffffff000000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffffffe0000ffe0,0xff800000ff80000,0xfffffffff000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffffffe0000ffe0,0xffffff0,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffffffe0000ffe0,0xff800000ffffff0,0xffffff000000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffffffe0000ffe0,0xffffff000000000,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffffffe0000ffe0,0xffffff00ff80000,0xffffff000000000]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xfffffffe0000ffe0,0xffffff00ffffff0,0xfffffffffffc000])].getD (i % 8) 0 else [(limbWord [0x1ff,0xff800ffe01ffc03f,0xffffffffffc00000,0x0,0x0]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xffffffffffc0ffe0,0xff800000ff80000,0xfffffffff003ff8]),(limbWord [0x1ff,0xff800ffe01ffc03f,0xffffffffffc0ffe0,0xffffff00ffffff0,0xffffffffffffff8]),(limbWord [0x1ff,0xfffff00001ffffc0,0xffff,0xf000000000000000,0x0]),(limbWord [0x1ff,0xfffff00001ffffc0,0xffff,0xf00000000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0xffff,0xf00000000fffffff,0xf0000ff000ffc007]),(limbWord [0x1ff,0xfffff00001ffffc0,0xffff,0xf00000000fffffff,0xffffffffffffffff]),(limbWord [0x1ff,0xfffff00001ffffc0,0xffff,0xf007ffffffffffff,0xf000000fffffffff])].getD (i % 8) 0) else (if i < 280 then [(limbWord [0x1ff,0xfffff00001ffffc0,0xffff,0xffffffffffffffff,0xf0000ff000ffc007]),(limbWord [0x1ff,0xfffff00001ffffc0,0xffff,0xf007fff00fffffff,0xf000000fffffc000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3fffffffffffffff,0xf00000000fffffff,0xf000000fffffffff]),(limbWord [0x1ff,0xfffff00001ffffff,0xc00007fe003fffff,0xf00000000fffffff,0xf0000ff000ffc007]),(limbWord [0x1ff,0xfffff001ffffffc0,0x7fe003fffff,0xf007ffffffffffff,0xf000000000ffc007]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffffffe0000ffff,0xf007fff00fffffff,0xf000000fffffc000]),(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xfff8000fffffffff,0xfffffff000003fff]),(limbWord [0x1ff,0xfffff00001ffffc0,0x7fe0000ffff,0xf007fff00fffffff,0xf000000000ffc000])].getD (i % 8) 0 else [(limbWord [0x1ff,0xfffffffe01ffffff,0xc00000000000ffff,0xfff800000fffffff,0xf0000ff000000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffff8000000ffff,0xf00000000fffffff,0xf000000fff000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0xffff,0xf00000000fffffff,0xfffff00000000000]),(limbWord [0x1ff,0xfffff00000000000,0x3ffff8000000ffff,0xf00000000007fff0,0xfff000000]),(limbWord [0x1ff,0xfffff00001ffc000,0xffff,0xf00000000ff80000,0xffff00000000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0xffff,0xf00000000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0xffff,0xf00000000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffff801ffc00000,0x0,0x0])].getD (i % 8) 0)) else (if i < 304 then (if i < 296 then [(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffff801ffc00000,0x7fff0,0xfff000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffff801ffc0ffe0,0xff80000,0xffff00000000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffff801ffc0ffff,0xf00000000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffff801ffc0ffff,0xf000000000000000,0x0]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffff801ffc0ffff,0xf00000000fffffff,0xfffff00fff003ff8]),(limbWord [0x1ff,0xffffffffffffffff,0xfffff801ffffffff,0xfff8000fffffffff,0xffffffffff003fff]),(limbWord [0x1ff,0xfffff00001ffffc0,0x0,0x0,0x0]),(limbWord [0x1ff,0xfffff00001ffffc0,0xffff,0xf00000000fffffff,0xf000000000000000])].getD (i % 8) 0 else [(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffff8000000ffff,0xf00000000fffffff,0xf000000fff000000]),(limbWord [0x1ff,0xfffff00000000000,0x3ffff8000000ffff,0xf007fff000000000,0xfff000000]),(limbWord [0x1ff,0xfffff00001ffc000,0xffff,0xf007fff00ff80000,0x0]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffff8000000ffff,0xf007fff00fffffff,0xf000000fff000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0xffff,0xf007fff00fffffff,0xf000000000000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffffffe00000000,0x0,0xfff000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffffffe0000ffe0,0xff80000,0x0]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffffffe0000ffff,0xf00000000fffffff,0xf000000000000000])].getD (i % 8) 0) else (if i < 312 then [(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffffffe0000ffff,0xf00000000fffffff,0xf000000fff000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffffffe0000ffff,0xf00000000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffffffe0000ffff,0xf007fff000000000,0x0]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffffffe0000ffff,0xf007fff00fffffff,0xf000000000000000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffffffe0000ffff,0xf007fff00fffffff,0xf000000fffffc000]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3ffff801ffc0ffff,0xf00000000fffffff,0xfffff00fff003ff8]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3fffffffffc00000,0x0,0x0]),(limbWord [0x1ff,0xfffff00001ffffc0,0x3fffffffffc0ffff,0xf00000000fffffff,0xfffff00fff003ff8])].getD (i % 8) 0 else [(limbWord [0x1ff,0xfffff00001ffffc0,0x3fffffffffc0ffff,0xf007fff00fffffff,0xfffff00ffffffff8]),(limbWord [0x1ff,0xfffffffe00000000,0xffff,0xfff8000000000000,0xffff00000000000]),(limbWord [0x1ff,0xfffffffe00000000,0xffff,0xfff800000007fff0,0x0]),(limbWord [0x1ff,0xfffffffe01ffffff,0xc000000000000000,0x0,0x0]),(limbWord [0x1ff,0xfffffffe01ffffff,0xc000000000000000,0x0,0xffff00000000000]),(limbWord [0x1ff,0xfffffffe01ffffff,0xc000000000000000,0x0,0x0]),(limbWord [0x1ff,0xfffffffe01ffffff,0xc000000000000000,0x7fff0,0x0]),(limbWord [0x1ff,0xfffffffe01ffffff,0xc00000000000ffff,0xf00000000fffffff,0xf000000000000000])].getD (i % 8) 0))) else (if i < 352 then (if i < 336 then (if i < 328 then [(limbWord [0x1ff,0xfffffffe01ffffff,0xc00000000000ffff,0xf00000000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xfffffffe01ffffff,0xc00000000000ffff,0xf00000000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xfffffffe01ffffff,0xc00000000000ffff,0xfff8000000000000,0x0]),(limbWord [0x1ff,0xfffffffe01ffffff,0xc00000000000ffff,0xfff800000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xfffffffe01ffffff,0xc00000000000ffff,0xfff800000fffffff,0xfffffff000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xfff8000fffffffff,0xfffffff000003fff]),(limbWord [0x1ff,0xfffffffe01ffffff,0xfffff8000000ffff,0xfff800000fffffff,0xffffffffff000000]),(limbWord [0x1ff,0xfffffffe01ffffff,0xfffff801ffc0ffff,0xf00000000fffffff,0xfffff00fff003ff8])].getD (i % 8) 0 else [(limbWord [0x1ff,0xfffffffe01ffffff,0xfffff801ffc0ffff,0xfff800000fffffff,0xfffffff000000000]),(limbWord [0x1ff,0xfffffffe01ffffff,0xfffff801ffc0ffff,0xfff800000fffffff,0xffffffffff003ff8]),(limbWord [0x1ff,0xfffffffe01ffffff,0xfffffffe00000000,0x0,0x0]),(limbWord [0x1ff,0xfffffffe01ffffff,0xfffffffe0000ffff,0xf007fff00fffffff,0xf000000fffffc000]),(limbWord [0x1ff,0xfffffffe01ffffff,0xfffffffe0000ffff,0xfff800000fffffff,0xfffffff000000000]),(limbWord [0x1ff,0xfffffffe01ffffff,0xfffffffe0000ffff,0xfffffff00fffffff,0xffffffffffffc000]),(limbWord [0x1ff,0xfffffffffe000000,0xffff,0xf000000000000000,0x0]),(limbWord [0x1ff,0xfffffffffe000000,0xffff,0xfffffffff0000000,0x0])].getD (i % 8) 0) else (if i < 344 then [(limbWord [0x1ff,0xfffffffffe000000,0xffff,0xfffffffff0000000,0xff000ffc007]),(limbWord [0x1ff,0xfffffffffe000000,0xffff,0xfffffffff0000000,0xfffffffffffffff]),(limbWord [0x1ff,0xfffffffffe000000,0xffff,0xfffffffff007ffff,0xf000000fffffffff]),(limbWord [0x1ff,0xfffffffffe000000,0xffff,0xffffffffffffffff,0xf0000ff000ffc007]),(limbWord [0x1ff,0xfffffffffe000000,0xffff,0xfffffffff007fff0,0xfffffc000]),(limbWord [0x1ff,0xfffffffffe000000,0x3fffffffffffffff,0xfffffffff0000000,0xfffffffff]),(limbWord [0x1ff,0xfffffffffe00003f,0xc00007fe003fffff,0xfffffffff0000000,0xff000ffc007]),(limbWord [0x1ff,0xfffffffffe003fc0,0x7fe003fffff,0xfffffffff007ffff,0xf000000000ffc007])].getD (i % 8) 0 else [(limbWord [0x1ff,0xfffffffffe000000,0x3ffffffe0000ffff,0xfffffffff007fff0,0xfffffc000]),(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xfffffffffff8000f,0xfffffff000003fff]),(limbWord [0x1ff,0xfffffffffe000000,0x7fe0000ffff,0xfffffffff007fff0,0xffc000]),(limbWord [0x1ff,0xffffffffffffc03f,0xc00000000000ffff,0xfffffffffff80000,0xff000000000]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffff8000000ffff,0xfffffffff0000000,0xfff000000]),(limbWord [0x1ff,0xfffffffffe000000,0xffff,0xfffffffff0000000,0xffff00000000000]),(limbWord [0x1ff,0xfffffffffe000000,0xffff,0xfffffffff0000000,0x0]),(limbWord [0x1ff,0xfffffffffe000000,0xffff,0xfffffffff0000000,0x0])].getD (i % 8) 0)) else (if i < 368 then (if i < 360 then [(limbWord [0x1ff,0xfffffffffe000000,0x3ffff801ffc00000,0x0,0x0]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffff801ffc00000,0x7fff000000000,0xfff000000]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffff801ffc0ffe0,0xff8000000000000,0xffff00000000000]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffff801ffc0ffff,0xf000000000000000,0x0]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffff801ffc0ffff,0xfffffffff0000000,0x0]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffff801ffc0ffff,0xfffffffff0000000,0xffff00fff003ff8]),(limbWord [0x1ff,0xffffffffffffffff,0xfffff801ffffffff,0xfffffffffff8000f,0xffffffffff003fff]),(limbWord [0x1ff,0xfffffffffe000000,0x0,0x0,0x0])].getD (i % 8) 0 else [(limbWord [0x1ff,0xfffffffffe000000,0xffff,0xfffffffff0000000,0x0]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffff8000000ffff,0xfffffffff0000000,0xfff000000]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffff8000000ffff,0xfffffffff007fff0,0xfff000000]),(limbWord [0x1ff,0xfffffffffe000000,0xffff,0xfffffffff007fff0,0x0]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffffffe00000000,0x0,0xfff000000]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffffffe0000ffe0,0xff8000000000000,0x0]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffffffe0000ffff,0xf00000000007fff0,0x0]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffffffe0000ffff,0xfffffffff0000000,0x0])].getD (i % 8) 0) else (if i < 376 then [(limbWord [0x1ff,0xfffffffffe000000,0x3ffffffe0000ffff,0xfffffffff0000000,0xfff000000]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffffffe0000ffff,0xfffffffff0000000,0x0]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffffffe0000ffff,0xfffffffff007fff0,0x0]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffffffe0000ffff,0xfffffffff007fff0,0xfffffc000]),(limbWord [0x1ff,0xfffffffffe000000,0x3ffff801ffc0ffff,0xfffffffff0000000,0xffff00fff003ff8]),(limbWord [0x1ff,0xfffffffffe000000,0x3fffffffffc00000,0x0,0x0]),(limbWord [0x1ff,0xfffffffffe000000,0x3fffffffffc0ffff,0xfffffffff0000000,0xffff00fff003ff8]),(limbWord [0x1ff,0xfffffffffe000000,0x3fffffffffc0ffff,0xfffffffff007fff0,0xffff00ffffffff8])].getD (i % 8) 0 else [(limbWord [0x1ff,0xffffffffffffc03f,0xc000000000000000,0x0,0x0]),(limbWord [0x1ff,0xffffffffffffc03f,0xc000000000000000,0x0,0xffff00000000000]),(limbWord [0x1ff,0xffffffffffffc03f,0xc000000000000000,0x0,0x0]),(limbWord [0x1ff,0xffffffffffffc03f,0xc000000000000000,0x7fff000000000,0x0]),(limbWord [0x1ff,0xffffffffffffc03f,0xc00000000000ffff,0xf00000000ff80000,0x0]),(limbWord [0x1ff,0xffffffffffffc03f,0xc00000000000ffff,0xfffffffff0000000,0x0]),(limbWord [0x1ff,0xffffffffffffc03f,0xc00000000000ffff,0xfffffffff0000000,0x0]),(limbWord [0x1ff,0xffffffffffffc03f,0xc00000000000ffff,0xfffffffff0000000,0x0])].getD (i % 8) 0))))

def p1AtBlock3 (i : Nat) : Nat := (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then [(limbWord [0x1ff,0xffffffffffffc03f,0xc00000000000ffff,0xfffffffffff80000,0x0]),(limbWord [0x1ff,0xffffffffffffc03f,0xc00000000000ffff,0xfffffffffff80000,0xffffff000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xfffffffffff8000f,0xfffffff000003fff]),(limbWord [0x1ff,0xffffffffffffc03f,0xfffff8000000ffff,0xfffffffffff80000,0xfffffffff000000]),(limbWord [0x1ff,0xffffffffffffc03f,0xfffff801ffc0ffff,0xfffffffff0000000,0xffff00fff003ff8]),(limbWord [0x1ff,0xffffffffffffc03f,0xfffff801ffc0ffff,0xfffffffffff80000,0xffffff000000000]),(limbWord [0x1ff,0xffffffffffffc03f,0xfffff801ffc0ffff,0xfffffffffff80000,0xfffffffff003ff8]),(limbWord [0x1ff,0xffffffffffffc03f,0xfffffffe00000000,0x0,0x0])].getD (i % 8) 0 else [(limbWord [0x1ff,0xffffffffffffc03f,0xfffffffe0000ffff,0xfffffffff007fff0,0xfffffc000]),(limbWord [0x1ff,0xffffffffffffc03f,0xfffffffe0000ffff,0xfffffffffff80000,0xffffff000000000]),(limbWord [0x1ff,0xffffffffffffc03f,0xfffffffe0000ffff,0xfffffffffffffff0,0xfffffffffffc000]),(limbWord [0x1ff,0xffffffffffffffc0,0x0,0x0,0x0]),(limbWord [0x1ff,0xffffffffffffffc0,0x0,0x0,0x0]),(limbWord [0x1ff,0xffffffffffffffc0,0x0,0x7fff00007fff0,0x0]),(limbWord [0x1ff,0xffffffffffffffc0,0xffe0,0xff800000ff80000,0x0]),(limbWord [0x1ff,0xffffffffffffffc0,0xffff,0xffffffffffffffff,0xf000000000000000])].getD (i % 8) 0) else (if i < 408 then [(limbWord [0x1ff,0xffffffffffffffff,0xc0000001ffffffff,0xffffffffffffffff,0xfffffff000003fff]),(limbWord [0x1ff,0xffffffffffffffc0,0x3ffff8000000ffff,0xffffffffffffffff,0xf000000fff000000]),(limbWord [0x1ff,0xffffffffffffffc0,0xffff,0xffffffffffffffff,0xfffff00000000000]),(limbWord [0x1ff,0xffffffffffffffc0,0x3ffff801ffc00000,0x0,0x0]),(limbWord [0x1ff,0xffffffffffffffc0,0x3ffff801ffc0ffff,0xffffffffffffffff,0xf000000000000000]),(limbWord [0x1ff,0xffffffffffffffc0,0x3ffff801ffc0ffff,0xffffffffffffffff,0xfffff00fff003ff8]),(limbWord [0x1ff,0xffffffffffffffc0,0xffff,0xf00000000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xffffffffffffffc0,0xffff,0xfffffffff0000000,0x0])].getD (i % 8) 0 else [(limbWord [0x1ff,0xffffffffffffffc0,0xffff,0xffffffffffffffff,0xf000000000000000]),(limbWord [0x1ff,0xffffffffffffffc0,0x3ffffffe0000ffff,0xffffffffffffffff,0xf000000000000000]),(limbWord [0x1ff,0xffffffffffffffc0,0x3ffffffe0000ffff,0xffffffffffffffff,0xf000000fffffc000]),(limbWord [0x1ff,0xffffffffffffffff,0xc000000000000000,0x0,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xc00000000000ffe0,0xff800000ff80000,0xffffff000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xc00000000000ffe0,0xff800000ff80000,0xffffff000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xc00000000000ffff,0xf00000000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xc00000000000ffff,0xf00000000fffffff,0xf000000000000000])].getD (i % 8) 0)) else (if i < 432 then (if i < 424 then [(limbWord [0x1ff,0xffffffffffffffff,0xc00000000000ffff,0xfffffffff0000000,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xc00000000000ffff,0xfffffffff0000000,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xc00000000000ffff,0xffffffffffffffff,0xf000000000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xc00000000000ffff,0xffffffffffffffff,0xfffffff000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xfffff801ffc0ffff,0xffffffffffffffff,0xffffffffff003ff8]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0xfffffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0xff000ffc007])].getD (i % 8) 0 else [(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0xfffffc000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0xfffffffffffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x7ffff,0xf000000fffffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0xfffffff,0xf0000ff000ffc007]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x7fffff0000000,0xfffffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0xffffffff0000000,0xff000ffc007]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff001f,0xf007fffff007ffff,0xf000000000ffc007]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0xfff003ff8])].getD (i % 8) 0) else (if i < 440 then [(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x7fff00007fff0,0xfffffc000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfff8000ffff8000f,0xfffffff000003fff]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x7fff00007fff0,0xffc000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffe0,0xff800000ff80000,0xff000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0xfff000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0xffff00000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0x0])].getD (i % 8) 0 else [(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0xffff00fff003ff8]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfff8000ffff8000f,0xffffffffff003fff]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0xfff000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x7fff0,0xfff000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x7fff0,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x7fff000000000,0xfff000000])].getD (i % 8) 0))) else (if i < 480 then (if i < 464 then (if i < 456 then [(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x7fff000000000,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x7fff00007fff0,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x7fff00007fff0,0xfffffc000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x0,0xffff00fff003ff8]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffff0000,0x7fff00007fff0,0xffff00ffffffff8]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffe0,0xff800000ff80000,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffe0,0xff800000ff80000,0xffffff000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfff8000ffff8000f,0xfffffff000003fff])].getD (i % 8) 0 else [(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffe0,0xff800000ff80000,0xfffffffff000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffe0,0xff80000,0xfff000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffe0,0xff8000000000000,0xfff000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffe0,0xff800000ff80000,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffe0,0xff800000ff80000,0xfffffffff003ff8]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffe0,0xffffff00ffffff0,0xfffffffffffc000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xf00000000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfff8000fffffffff,0xfffffff000003fff])].getD (i % 8) 0) else (if i < 472 then [(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xf00000000fffffff,0xf000000fff000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xf00000000fffffff,0xfffff00000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xf00000000fffffff,0xfffff00fff003ff8]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xf00000000fffffff,0xf000000000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xf007fff00fffffff,0xf000000fffffc000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfff800000fffffff,0xfffffff000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfff800000fffffff,0xffffffffff003ff8]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfffffffff0000000,0x0])].getD (i % 8) 0 else [(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfffffffffff8000f,0xfffffff000003fff]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfffffffff0000000,0xfff000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfffffffff0000000,0xffff00000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfffffffff0000000,0xffff00fff003ff8]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfffffffff0000000,0x0]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfffffffff007fff0,0xfffffc000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfffffffffff80000,0xffffff000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xfffffffffff80000,0xfffffffff003ff8])].getD (i % 8) 0)) else [(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xf000000000000000]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xfffff00fff003ff8]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xfffffff000000000])].getD (i % 8) 0))

def p1At (i : Nat) : Nat := (if i < 256 then (if i < 128 then p1AtBlock0 i else p1AtBlock1 i) else (if i < 384 then p1AtBlock2 i else p1AtBlock3 i))

def p2AtBlock0 (i : Nat) : Nat := (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then [(limbWord [0x80000000000000,0x4000180200000000,0x8001000080010,0x30300300c009]),(limbWord [0x100000000000040,0x600000400000,0x1000002000100060,0x300040000c010032]),(limbWord [0x80000000008000,0x4000080200000040,0x8001000480090,0x8000109001024001]),(limbWord [0x80000000008000,0x4000580200000040,0x8001000c801d0,0xa00130b01b03c029]),(limbWord [0x18000000000c040,0x4000780200400060,0x1008003000f801f0,0xf001f0f01f03c07b]),(limbWord [0x200000002000000,0x1800000800000,0x201000c030000200,0x2000060040184]),(limbWord [0x80000400000000,0x4000080200000100,0x48011080080010,0x121001084001]),(limbWord [0x80000400000000,0x4001180200000100,0xc80390a0080010,0x83230c30cc109])].getD (i % 8) 0 else [(limbWord [0x280000602000000,0x4001980200800180,0x20f803d0f0080210,0xe3330e30cc38d]),(limbWord [0x400200000000000,0x2000000000400,0x8000040200000402,0x10000000100000]),(limbWord [0x400200000000000,0x3400000000401,0x80000c8220000c42,0x2010000148150120]),(limbWord [0x700300002000040,0x3e00000c00601,0xf0100ce330100e63,0x301240016c1505b6]),(limbWord [0xf00300202004040,0x3e00000c00ea3,0xf1300ce371300e63,0x7036c1416c1507f6]),(limbWord [0x1480200400008000,0x4002080200001544,0x8248151282481492,0x80101290011a4001]),(limbWord [0x1480200400008000,0x4002080200001544,0x8248151282481492,0x80101290011a4001]),(limbWord [0x1780300402008040,0x4003e80200c01745,0xf2581df3b2581ef3,0xb01252916d1f45b7])].getD (i % 8) 0) else (if i < 24 then [(limbWord [0x1f8030060200c040,0x4002a80200c01fe6,0xf3781573d37816b3,0xd036d3d0251a46d7]),(limbWord [0xb00100202004040,0x1f00000c02aa3,0x71b00ae171b00b61,0x702fe161fe0587fe]),(limbWord [0x1480200400008000,0x4003580200003545,0x82c81f92a2c81dd2,0xa01932b1db1fc129]),(limbWord [0x1f8030060200c040,0x4003f80200c03fe7,0xf3f81ff3f3f81ff3,0xf03ff3f1ff1fc7ff]),(limbWord [0x188000060000c000,0x40001802000039e6,0x3e81310c3e81190,0xc02db3f0930ac249]),(limbWord [0x1b8010060200c040,0x4001f80200c03be7,0x73f81bf1f3f81bf1,0xf02ff3f1ff0fc7ff]),(limbWord [0x1c8020060000c000,0x4003580200003de7,0x83e81f92e3e81dd2,0xe03db3f1db1fc369]),(limbWord [0x1f0030020200c040,0x3f00000c03ee7,0xf3b01ee373f01fe3,0xf03fe1e1fe1787fe])].getD (i % 8) 0 else [(limbWord [0x1d8030040000c040,0x4003780200403f67,0xd3c81fb3a3f81df3,0xf039f2f1df1fc57b]),(limbWord [0x1d8030060000c040,0x4002780200403fe7,0xd3e81f33c3f81df3,0xf03df3f19f1bc67b]),(limbWord [0x1f00300602004040,0x3f00000c03fa7,0xf3f01fe3f3b01f63,0x703fe361fe1d87fe]),(limbWord [0x1e80300602008000,0x4003d80200803fc7,0xe3f81fd3f3c81fd3,0xa03f33b1fb1fc7ad]),(limbWord [0x1e8030060200c000,0x4003980200803fe7,0xe3f81fd3f3e81f93,0xc03fb3f1f31ec7cd]),(limbWord [0x1f0030060200c040,0x3e00000c03fe7,0xf3f01fe3f3f01fe3,0xf03fc3c1fc1f07f6]),(limbWord [0x1f8030060200c040,0x4003f80200c03fe7,0xf3f81ff3f3f81ff3,0xf03ff3f1ff1fc7ff]),0].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [(limbWord [0x80001000020001,0x4008080600020000,0x8001000080010,0x181001204001]),(limbWord [0x80001000020003,0x4018180e02020000,0x8001000080010,0x8038320320c009]),(limbWord [0x2080001800030003,0xc01c180e03030000,0x8201000082010,0xc03c320320c809]),(limbWord [0x4000800000080100,0x40001000080000,0x400000004008,0x100000000400000]),(limbWord [0x4000800000080300,0xc0403008080000,0x40000000c048,0x2100000408410020]),(limbWord [0x4100c000000c03c0,0xe060300c4c0000,0x100040200010c06c,0x310040040c411032]),(limbWord [0x4180c000000cc3c0,0x40e078320c4c0060,0x1008403000f8c1fc,0xf101f0f41f43d07b]),(limbWord [0xa18040080015c4c4,0xc024780215450060,0x1008203004f821f4,0xf241f4f01f03d87b])].getD (i % 8) 0 else [(limbWord [0xe100c008001d47c4,0x80e460301d4d0020,0x100060200430e06c,0x7340c4440c411872]),(limbWord [0x1,0x40808010002a8909,0x40480856000a0040,0x8401008494098,0x8100189001624001]),(limbWord [0x1,0x40808010002a8909,0x40480856000a0040,0x8401008494098,0x8100189001624001]),(limbWord [0x1,0x41808010002ac949,0x40487856004a0060,0x1008403008f941f8,0xf101f8f01f63c07b]),(limbWord [0x1,0x4180c010002e8bc9,0x40e868760c4e0040,0x100840300859c0fc,0xb10058940d635033]),(limbWord [0x1,0xe180c018003fcdcd,0xc06c2856154f0060,0x100860300c7960bc,0xd340dcd005625853]),(limbWord [0x1,0xe180c018007fcfcf,0xc1fc787e1f4f0060,0x100860300cf9e1fc,0xf3c1fcf61f63d87b]),(limbWord [0x1,0xe180c018007fcfcf,0xc1fc787e1f4f0060,0x100860300cf9e1fc,0xf3c1fcf61f63d87b])].getD (i % 8) 0) else (if i < 56 then [(limbWord [0x2,0x2004008000000,0x400008000200000,0x800800020000,0x400000000800000]),(limbWord [0x2,0x2004018000000,0xc01018040200000,0x1808820020000,0x400000840840100]),(limbWord [0x2,0x20300601e000000,0xe01818060b00000,0x201180cc30020200,0x402000860842184]),(limbWord [0x2,0x28300661e000000,0x4e01998260b00180,0x20f983dcf00a0210,0x40e3338e38ce38d]),(limbWord [0x4,0x228100ae26010010,0xc2059802a1910180,0x24f823d4f0082210,0x84e3730e30ceb8d]),(limbWord [0x6,0x220300ea3e010010,0x8e058180e1b10080,0x2431a0cc70022200,0xc46050860842b84]),(limbWord [0xa,0x82015448020021,0x44080a8600220100,0x84a8118800a0010,0x4001a1001a84001]),(limbWord [0xa,0x82015448020021,0x44080a8600220100,0x84a8118800a0010,0x4001a1001a84001])].getD (i % 8) 0 else [(limbWord [0xa,0x28201564a020021,0x44099a8600a20180,0x28fa83d8f00a0210,0x40e3b30e3acc38d]),(limbWord [0xa,0x28301745e020021,0x4e098b8660b20100,0x285b81dcb00a0210,0x4021a1861ac6185]),(limbWord [0xe,0x228301fe6e030031,0xc60c8a86a1b30180,0x2c7aa15cd00a2210,0xc461f1021a86a85]),(limbWord [0xe,0x228303fe7e030033,0xde1d9b8ee3b30180,0x2cfba3dcf00a2210,0xcce3f3ae3aceb8d]),(limbWord [0xe,0x228303fe7e030033,0xde1d9b8ee3b30180,0x2cfba3dcf00a2210,0xcce3f3ae3aceb8d]),(limbWord [0x10,0x7057020860410c0,0x223e00124d40609,0xf0100ce730100e67,0x301240016c1535b6]),(limbWord [0x22,0x440aa04108082100,0x442049000280410,0x8004c40a0006440a,0x510000000d00000]),(limbWord [0x22,0x440aa04108082100,0x442049000280410,0x8004c40a0006440a,0x510000000d00000])].getD (i % 8) 0))) else (if i < 96 then (if i < 80 then (if i < 72 then [(limbWord [0x22,0x470ab0410a082140,0x443e49000e80611,0xf014cceb30164e6b,0x351240016cd505b6]),(limbWord [0x22,0x548aa0450808a100,0x44420c9200281554,0x824cd51a824e549a,0x8510129001da4001]),(limbWord [0x32,0x470ff0618e0c31c0,0x662a49124fc0618,0xf014c46f1016462f,0x1512400024d03496]),(limbWord [0x10,0x3155020960412c0,0x2aa1e1216cd40209,0x701108e530108a65,0x3002400d6c0535b6]),(limbWord [0x22,0x441aa04118082300,0x2cc345b048280411,0x8005cc8a2006cc4a,0x2510000d48d50120]),(limbWord [0x32,0x471ff0619e0c33c0,0x2ee3e5b16cfc0619,0xf015ccef3016ce6f,0x3512400d6cd535b6]),(limbWord [0x30,0x471df021960c33c0,0x2ae3e5316cdc0619,0xf0154ce73014ce6f,0x3112400d6c5535b6]),(limbWord [0x32,0x451ef041980c33c0,0x2ce365b14c6c0619,0xd005ccab2016cc6f,0x3510400d4cd51532])].getD (i % 8) 0 else [(limbWord [0x32,0x71f70619e0432c0,0x2ea3e5a16cf40619,0xf0158cef30168e67,0x3412400d6c9535b6]),(limbWord [0x32,0x461fb0619e083300,0x2ec3c5b168b80619,0xe015cccf3006ce4b,0x2512000d68d525a4]),(limbWord [0x32,0x471ff0619e0c33c0,0x2ee3e5b16cfc0619,0xf015ccef3016ce6f,0x3512400d6cd535b6]),(limbWord [0x32,0x401fc0619c0c3380,0x2ee005b16c3c0018,0x5c00c0006c00c,0x500000c00c03000]),(limbWord [0x32,0x431fd0619e0c33c0,0x2ee1e5b16cfc0219,0x7015c8ed3016ca6d,0x3502400d6cc535b6]),(limbWord [0x32,0x441fe0619c0c3380,0x2ee345b16c3c0419,0x8005cc8e2006cc4e,0x2510000d48d53120]),(limbWord [0x32,0x451ff0619c0c33c0,0x2ee265b16c7c0619,0xd005cc2f0016cc6f,0x3510400d0cd13432]),(limbWord [0x32,0x461ff0619e0c3380,0x2ee385b16cbc0619,0xe015cccf3006ce0f,0x512000d60d43584])].getD (i % 8) 0) else (if i < 88 then [(limbWord [0x32,0x471ff0619e0c33c0,0x2ee3e5b16cfc0619,0xf015ccef3016ce6f,0x3512400d6cd535b6]),(limbWord [0x1480200400008000,0x4002080200001544,0x8248151282481492,0x80101290011a4001]),(limbWord [0x22,0x440aa04108082100,0x442049000280410,0x8004c40a0006440a,0x510000000d00000]),(limbWord [0x54,0xab2554aaa69554d4,0x8224a001b5d54aaa,0x7530206555302225,0x5a66c54024003ed6]),(limbWord [0x54,0xaba554aaa695d4d4,0xc224f803b5d54aea,0x7538207555f823f5,0xfa67f5f03f03feff]),(limbWord [0x54,0xaba554aea69554d4,0xc225b803b5d54baa,0x75f823f5f5382235,0x5a6ef770e70cffdf]),(limbWord [0x54,0xaf2574aaa69554d4,0x8227e001b5d54eab,0xf5302ce775302e67,0x7a76c5416c153ff6]),(limbWord [0x54,0xbfa574aea695d4d4,0xc226a803b5d55fee,0xf7783577d77836b7,0xda76d7d0251a7ed7])].getD (i % 8) 0 else [(limbWord [0x54,0xaba554baa69754d7,0xc23cb80fb7d74aaa,0x7538207555382235,0x5ae6fd722720fedf]),(limbWord [0x54,0xeb25d4aaa69d57d4,0x82e4e031bddd4aaa,0x753060655530e26d,0x7b66c5442c413ef6]),(limbWord [0x55,0xeba5d4baa6bfdddd,0xc26ca857b5df4aea,0x753860755d7962bd,0xdb66ddd025627ed7]),(limbWord [0x56,0xab2754eabe9554d4,0x8e25a181f5f54aaa,0x7531a0ed75322225,0x5e66c54864843fd6]),(limbWord [0x5e,0xaba755feee9754f5,0xc62caa87b5f74baa,0x7d7aa17dd53a2235,0x5e66df5025a87ed7]),(limbWord [0x76,0xef2ff4ebae9d75d4,0x8666a491b5fd4eba,0xf534e46f5536662f,0x5f76c54024d03ed6]),(limbWord [0xab,0x54caa955492aa929,0x444a0ed6002a9554,0x8a4ed51a8a4f549a,0x85101a9001fa4001]),(limbWord [0x89,0x10c0091441228829,0x40080a4600029144,0xa4a11108a491090,0x80001a90012a4001])].getD (i % 8) 0)) else (if i < 112 then (if i < 104 then [(limbWord [0xab,0x54caa955492aa929,0x444a0ed6002a9554,0x8a4ed51a8a4f549a,0x85101a9001fa4001]),(limbWord [0xab,0x54caa955492aa929,0x444a0ed6002a9554,0x8a4ed51a8a4f549a,0x85101a9001fa4001]),(limbWord [0xa9,0x54c8a915412aa929,0x404a0e56000a9554,0x8a4e55128a4d549a,0x81101a90017a4001]),(limbWord [0xab,0x54caa955492aa929,0x444a0ed6002a9554,0x8a4ed51a8a4f549a,0x85101a9001fa4001]),(limbWord [0xab,0x14ca29554922a829,0x440a0ec600229554,0x8a4e951a8a4f1492,0x84101a9001ba4001]),(limbWord [0xab,0x544aa9454928a928,0x44206d000289554,0x8a46d50a8a47548a,0x8510028000da0000]),(limbWord [0xab,0x404a8951492a2929,0x44806d4002a8010,0x806c00808074008,0x500080000e00000]),(limbWord [0xab,0x54caa955492aa929,0x444a0ed6002a9554,0x8a4ed51a8a4f549a,0x85101a9001fa4001])].getD (i % 8) 0 else [(limbWord [0xab,0x50ca8955492aa929,0x44480ed6002a9154,0xa4ed1188a4f5098,0x85001a9001ea4001]),(limbWord [0xab,0x544aa951492aa929,0x44a06d4002a9454,0x8a06d40a0a47548a,0x8510088000f20000]),(limbWord [0xab,0x544aa955492a2929,0x44a06d4002a9514,0x8a46d50a8a07540a,0x5100a0000f80000]),(limbWord [0xab,0x54caa955492aa929,0x444a0ed6002a9554,0x8a4ed51a8a4f549a,0x85101a9001fa4001]),(limbWord [0x100,0x10020010400202,0x399151284a002001,0x810a8020808940,0x2089202fda058128]),(limbWord [0x144,0xa820068a20d14416,0x91141008930168a2,0x5a0220045a02100,0x4aeda56292008a48]),(limbWord [0x150,0x8934560080d456c6,0x31b070291e446a2b,0x51800a2105b08965,0x72a9e0679e01947a]),(limbWord [0x154,0xa9345688a0d556d6,0xb1b460299f456a2b,0x5500282105b0a965,0x7ae1c4471c011c72])].getD (i % 8) 0) else (if i < 120 then [(limbWord [0x154,0xa934568aa0d556d6,0xb1b470299f456aab,0x55a02a2145b0a965,0x7aede5679e019e7a]),(limbWord [0x154,0xa3516a2b6c01012,0x3b119109e2906a8b,0x65b10ac571800b01,0x8af212bf204a78c]),(limbWord [0x154,0xaa3516aab6d11416,0xbb158109f3916a8b,0x65b12ac575002a01,0xaee050be0042f84]),(limbWord [0x154,0xaa3516aab6d15416,0xbb159109f3916aab,0x65b12ac575a02b01,0x4aefa56bf204afcc]),(limbWord [0x154,0x8b3556a2b6d456d4,0x3ba1e121fcd46aab,0x75b10ae575b08b65,0x7a2fc14dfc0537f6]),(limbWord [0x154,0xab3556aab6d556d6,0xbbb5e129ffd56aab,0x75b12ae575b0ab65,0x7aefc54ffc053ff6]),(limbWord [0x154,0xab3556aab6d556d6,0xbbb5f129ffd56aab,0x75b12ae575b0ab65,0x7aefe56ffe05bffe]),(limbWord [0x154,0xa03546a8b4d51696,0xbbb40129ff154008,0x40120040400a004,0xac0040e00003800])].getD (i % 8) 0 else [(limbWord [0x154,0xa03546a8b4d51696,0xbbb41129ff156008,0x48122040480a104,0xac9242e9200b808]),(limbWord [0x154,0xa83546aab4d55696,0xbbb41129ff1568aa,0x5a1220445a0a104,0x4aeda56e9200ba48]),(limbWord [0x154,0xa93556a8b4d556d6,0xbbb46129ff556a2b,0x5501282505b0a965,0x7ae1c44f1c013c72]),(limbWord [0x154,0xaa3556aab6d51696,0xbbb58129ff956a8b,0x65b12ac57500aa05,0xaee050fe0043f84]),(limbWord [0x154,0xab3556aab6d556d6,0xbbb5e129ffd56aab,0x75b12ae575b0ab65,0x7aefc54ffc053ff6]),(limbWord [0x154,0xab3556aab6d556d6,0xbbb5f129ffd56aab,0x75b12ae575b0ab65,0x7aefe56ffe05bffe]),(limbWord [0x154,0xabb556aab6d556d6,0xfbb5f92bffd56aab,0x75b92af575b8ab75,0x7aeff57fff05ffff]),(limbWord [0x154,0xabb556aab6d5d6d6,0xfbb5f92bffd56aeb,0x75b92af575f8abf5,0xfaeff5ffff07ffff])].getD (i % 8) 0))))

def p2AtBlock1 (i : Nat) : Nat := (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then [(limbWord [0x154,0xabb556aeb6d556d6,0xfbb5f92bffd56bab,0x75f92bf5f5b8ab75,0x7aeff77fff0dffff]),(limbWord [0x154,0xaf3576aab6d556d6,0xbbb7f129ffd56eab,0xf5b12ee775b0af67,0x7affe56ffe15bffe]),(limbWord [0x154,0xbfb576aeb6d5d6d6,0xfbb7f92bffd57fef,0xf7f93ff7f7f8bff7,0xfafff7ffff1fffff]),(limbWord [0x154,0xab3556aab6d556d6,0xbbb5f129ffd56aab,0x75b12ae575b0ab65,0x7aefe56ffe05bffe]),(limbWord [0x154,0xabb556bab6d756d7,0xfbbdf92fffd76aab,0x75b92af575b8ab75,0x7aeffd7fff25ffff]),(limbWord [0x154,0xabb556bab6d756d7,0xfbbdf92fffd76aab,0x75b92af575b8ab75,0x7aeffd7fff25ffff]),(limbWord [0x154,0xeb35d6aab6dd57d6,0xbbf5f139ffdd6aab,0x75b16ae575b0eb6d,0x7befe56ffe45bffe]),(limbWord [0x156,0xab3756eabed556d6,0xbfb5f1a9fff56aab,0x75b1aaed75b2ab65,0x7eefe56ffe85bffe])].getD (i % 8) 0 else [(limbWord [0x176,0xef3ff6ebbedd77d6,0xbff7f5b9fffd6ebb,0xf5b5eeef75b6ef6f,0x7fffe56ffed5bffe]),(limbWord [0x154,0xab2556aaa6d554d6,0x9334b009b7d56aaa,0x75b0226555b02325,0x5aefe562b600bede]),(limbWord [0x154,0xab3556aab6d556d6,0xbbb4a129ffd54aaa,0x753120655530a225,0x5ae6c54e24003ed6]),(limbWord [0x154,0xab3556aab6d556d6,0xbbb5f129ffd56aab,0x75b12ae575b0ab65,0x7aefe56ffe05bffe]),(limbWord [0x189,0x10c00b144162882b,0x51181a4e0202b144,0xaca13108ac91190,0x80893ab2932ac009]),(limbWord [0x189,0x500b1051620a2b,0x3999536c4a02a001,0x8830a8028818940,0x2089282fda258128]),(limbWord [0x189,0x10d00b1451628a2b,0x79981b6e4a02b144,0xacb13108ac99190,0x80893abe932ac009]),(limbWord [0x189,0x10d00b1451628a2b,0x79995b6e4a02b145,0xacb1b90aac999d0,0xa0893abfdb2fc129])].getD (i % 8) 0) else (if i < 152 then [(limbWord [0x1a1,0x5458aa010168ab0a,0x31d254780a08b455,0x82845e020ac5ddca,0xa19920a79a538028]),(limbWord [0x1a1,0x5458aa011168ab0a,0x39d245784a08b455,0x82055c020ac5ddca,0xa191008f18530020]),(limbWord [0x1a1,0x5458aa011168ab0a,0x39d355784a08b455,0x82855e822ac5ddca,0xa19920afda578128]),(limbWord [0x1a9,0x5458ab11416aab2b,0x31da467c0a0ab455,0x8a065c020ac5ddca,0xa191088718730020]),(limbWord [0x1a9,0x54d8ab15416aab2b,0x71da5e7e0a0ab555,0x8ace5f128acdddda,0xa1993ab79b7bc029]),(limbWord [0x1a9,0x54d8ab15516aab2b,0x79db5f7e4a0ab555,0x8acf5f92aacdddda,0xa1993abfdb7fc129]),(limbWord [0x1aa,0x145a2b4559402022,0x3d1317884220b515,0x8ac79f8aa2861d02,0x499222bd29c8108]),(limbWord [0x1aa,0x145a2b4559402222,0x3d9307a84a20b515,0x8ac79f8aa2069c02,0x498020fc09c0100])].getD (i % 8) 0 else [(limbWord [0x1aa,0x145a2b4559402222,0x3d9357a84a20b515,0x8ac79f8aa2869d42,0x2499222fda9d8128]),(limbWord [0x1ab,0x145a2b555962282b,0x3d1b07cc4222b515,0x8ac79f8aaa071c02,0x4980a0bc0bc0100]),(limbWord [0x1ab,0x14da2b555962a82b,0x7d1b1fce4222b555,0x8acf9f9aaacf1d92,0x84993abbd3bec109]),(limbWord [0x1ab,0x14da2b555962aa2b,0x7d9b5fee4a22b555,0x8acf9f9aaacf9dd2,0xa4993abfdbbfc129]),(limbWord [0x1ab,0x545aab455968ab28,0x3dc347f04828b555,0x8ac7df8aaac7ddca,0xa519028dd8df0120]),(limbWord [0x1ab,0x545aab455968ab2a,0x3dd357f84a28b555,0x8ac7df8aaac7ddca,0xa59922afdadf8128]),(limbWord [0x1ab,0x54daab55596aab2b,0x7ddb5ffe4a2ab555,0x8acfdf9aaacfddda,0xa5993abfdbffc129]),(limbWord [0x1ab,0x54daab55596aab2b,0x7ddb5ffe4a2ab555,0x8acfdf9aaacfddda,0xa5993abfdbffc129])].getD (i % 8) 0)) else (if i < 176 then (if i < 168 then [(limbWord [0x1ab,0x405a8b51596a2b2b,0x3dd807fc4a2a8010,0x807c0080807c008,0x580080e00e00000]),(limbWord [0x1ab,0x405a8b51596a2b2b,0x3dd817fc4a2aa010,0x887c2080887c108,0x589282e92e08008]),(limbWord [0x1ab,0x405a8b51596a2b2b,0x3dd957fc4a2aa011,0x887ca882887c948,0x2589282fdae58128]),(limbWord [0x1ab,0x50da8b55596aab2b,0x7dd81ffe4a2ab154,0xacfd3188acfd198,0x85893abe93eac009]),(limbWord [0x1ab,0x50da8b55596aab2b,0x7dd95ffe4a2ab155,0xacfdb98aacfd9d8,0xa5893abfdbefc129]),(limbWord [0x1ab,0x545aab51596aab2b,0x3dda47fc4a2ab455,0x8a07dc0a0ac7ddca,0xa591088f18f30020]),(limbWord [0x1ab,0x545aab51596aab2b,0x3ddb57fc4a2ab455,0x8a87de8a2ac7ddca,0xa59928afdaf78128]),(limbWord [0x1ab,0x54daab55596aab2b,0x7dda5ffe4a2ab555,0x8acfdf1a8acfddda,0xa5993abf9bfbc029])].getD (i % 8) 0 else [(limbWord [0x1ab,0x54daab55596aab2b,0x7ddb5ffe4a2ab555,0x8acfdf9aaacfddda,0xa5993abfdbffc129]),(limbWord [0x1ab,0x545aab55596a2b2b,0x3ddb07fc4a2ab515,0x8ac7df8aaa07dc0a,0x5980a0fc0fc0100]),(limbWord [0x1ab,0x545aab55596a2b2b,0x3ddb57fc4a2ab515,0x8ac7df8aaa87dd4a,0x25992a2fdafd8128]),(limbWord [0x1ab,0x54daab55596aab2b,0x7ddb1ffe4a2ab555,0x8acfdf9aaacfdd9a,0x85993abfd3fec109]),(limbWord [0x1ab,0x54daab55596aab2b,0x7ddb5ffe4a2ab555,0x8acfdf9aaacfddda,0xa5993abfdbffc129]),(limbWord [0x1ab,0x545aab55596aab2b,0x3ddb47fc4a2ab555,0x8ac7df8aaac7ddca,0xa5990a8fd8ff0120]),(limbWord [0x1ab,0x54daab55596aab2b,0x7ddb5ffe4a2ab555,0x8acfdf9aaacfddda,0xa5993abfdbffc129]),(limbWord [0x1ab,0x54daab55596aab2b,0x7ddb5ffe4a2ab555,0x8acfdf9aaacfddda,0xa5993abfdbffc129])].getD (i % 8) 0) else (if i < 184 then [(limbWord [0x1bb,0x57dffb75df6ebbeb,0x7ffbffff6efeb75d,0xfadfdfffbadfdfff,0xb59b7abffffff5bf]),(limbWord [0x1cd,0xa8600f9a61f34c3f,0x911c124c9303e8a2,0xda222004da12100,0x4aedad6292208a48]),(limbWord [0x1cd,0xb8e00f9e61f3cc3f,0xd11c1a4e9303f9e6,0xfea3310cfe93190,0xcaedbff2932aca49]),(limbWord [0x1dd,0xb9f45f9ee1f7deff,0xf1bc7a6f9f47fbef,0x5fea3b31cff9b9f5,0xfaedfff79f2bde7b]),(limbWord [0x1dd,0xbaf51fbef7f3dc3f,0xfb1d9b4ff393fbef,0x6ffb3bd5ffe93b91,0xcaefbffbf32eefcd]),(limbWord [0x1dd,0xa0754fb8f5f71ebf,0xbbbc036dff17c008,0xc0320040c01a004,0xac00c0e00203800]),(limbWord [0x1dd,0xb0f54fbcf5f79ebf,0xfbbc1b6fff17f14c,0xecb33148ec9b194,0x8ac93ebe932af809]),(limbWord [0x1dd,0xbbf55fbef7f7deff,0xfbbdfb6fffd7fbef,0x7ffb3bf5fff9bbf5,0xfaefffffff2fffff])].getD (i % 8) 0 else [(limbWord [0x1ef,0xe87a8fdb79fb6f3f,0xbddc17fcdb2be8b2,0xda7e2084da7e108,0x4fedad6e92e08a48]),(limbWord [0x1fd,0xfd7cff99e1ffffff,0xb1fe667d9f4ffe7f,0xdf067c230ff5fdef,0xfbf1ccc71c731c72]),(limbWord [0x1fd,0xfdfcff9fe1ffffff,0xf1fe7e7f9f4fffff,0xdfee7f33cffdfdff,0xfbfdfff79f7bde7b]),(limbWord [0x1fd,0xfffdffbff7ffffff,0xfbffff7fffdfffff,0xffff7ff7fffdffff,0xfbffffffff7fffff]),(limbWord [0x1ff,0xfdfeffddf9ffffff,0xfdff7fffdf6fff7f,0xdfcfffbbaffffdff,0xfff9feffdfffdd7b]),(limbWord [0x1ff,0xbe7f3ffffff33c3f,0xbf1f87cdf3b3ff9f,0xeff7bfcfff073e03,0xefe0f0be0bc2f84]),(limbWord [0x1ff,0xbeff3ffffff3fc3f,0xff1f9fcff3b3ffff,0xefffbfdfffef3f93,0xceffbffbf3beefcd]),(limbWord [0x1ff,0xbfff7ffffff7feff,0xffbfffeffff7ffff,0xffffbfffffffbff7,0xfeffffffffbfffff])].getD (i % 8) 0))) else (if i < 224 then (if i < 208 then (if i < 200 then [(limbWord [0x1ff,0xfeffbffffffbbf3f,0xffdfdffffbbbffdf,0xefffffdfffcfffdb,0xafff3fbffbffefad]),(limbWord [0x1ff,0xdf7fffe7fffcfffc,0x3fe3e7f1fcfcffff,0xfff7dfeffff7dfef,0xff3fc3cdfcdf37f6]),(limbWord [0x1ff,0xff7fffeffffdfffe,0xbff7f7f9fffdffff,0xfff7ffeffff7ffef,0xffffe7effedfbffe]),(limbWord [0x1ff,0xdffffff7fffeffff,0x7ffbfffffefeffff,0xffffdfffffffdfff,0xffbffbfffffff7ff]),(limbWord [0x1ff,0xe07fcff9fdff3fbf,0xbffc07fdff3fc018,0xc07e00c0c07e00c,0xfc00c0e00e03800]),(limbWord [0x1ff,0xe97fdff9fdff7fff,0xbffc67fdff7fea3b,0x5d07e82d0db7e96d,0x7fe1cc4f1ce13c72]),(limbWord [0x1ff,0xea7fdffbffff3fbf,0xbffd87fdffbfea9b,0x6db7eacd7d07ea0d,0xfee0d0fe0e43f84]),(limbWord [0x1ff,0xeb7fdffbffff7fff,0xbffdf7fdffffeabb,0x7db7eaed7db7eb6d,0x7fefed6ffee5bffe])].getD (i % 8) 0 else [(limbWord [0x1ff,0xf4ffeffdfdffbfbf,0xffff5fffff3ff55d,0x8ecfff9eaecffdde,0xafd93ebfdbfff929]),(limbWord [0x1ff,0xf8ffcffffdffffbf,0xfffc1fffff3ff9fe,0xfeff31ccfeff19c,0xcfedbffe93eafa49]),(limbWord [0x1ff,0xfbffdfffffffffff,0xfffdfffffffffbff,0x7ffffbfdfffffbfd,0xffefffffffefffff]),(limbWord [0x1ff,0xfd7ffff9fdffffff,0xbffe67fdff7ffe7f,0xdf07fc2f0ff7fdef,0xfff1cccf1cf33c72]),(limbWord [0x1ff,0xff7ffffbffffffff,0xbffff7fdfffffeff,0xffb7feef7ff7ffef,0xffffedeffef7bffe]),(limbWord [0x1ff,0xfdfffffdfdffffff,0xffff7fffff7fff7f,0xdfcfffbfaffffdff,0xfff9feffdffffd7b]),(limbWord [0x1ff,0xfe7fffffffff3fbf,0xbfff87fdffbfff9f,0xeff7ffcfff07fe0f,0xffe0f0fe0fc3f84]),(limbWord [0x1ff,0xff7fffffffff7fff,0xbffff7fdffffffbf,0xfff7ffefffb7ff6f,0x7fffef6ffefdbffe])].getD (i % 8) 0) else (if i < 216 then [(limbWord [0x1ff,0xfeffffffffffbfbf,0xffffdfffffbfffdf,0xefffffdfffcfffdf,0xafff3fbffbffffad]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff]),(limbWord [0x1c5,0xb8600e8a21f1cc1e,0x911410489301f8e6,0x7a032004fe13180,0xcaeda5e292028a48]),(limbWord [0x1cd,0xb8e00f9e61f3cc3f,0xd11c1a4e9303f9e6,0xfea3310cfe93190,0xcaedbff2932aca49]),(limbWord [0x1cc,0xb8600f8e61d14436,0x911412089301f9a6,0xfe23300c7a03100,0x4aeda76292088a48]),(limbWord [0x1cd,0xb8e00f9e61f3cc3f,0xd11c1a4e9303f9e6,0xfea3310cfe93190,0xcaedbff2932aca49]),(limbWord [0x1cd,0x98600f8661f0cc3c,0x110002409000f9e6,0xfe21300cfe11180,0xca2d83c0900a0240]),(limbWord [0x1cd,0xa0600f9861f30c3f,0x911c024c9303c000,0xc0220000c012000,0xac00c0200200800])].getD (i % 8) 0 else [(limbWord [0x1cd,0xa0600f9861f30c3f,0x911c124c9303e000,0xc8222000c812100,0xac92c2292208808]),(limbWord [0x1cd,0xa8600f9a61f34c3f,0x911c124c9303e8a2,0xda222004da12100,0x4aedad6292208a48]),(limbWord [0x1cd,0xb0e00f9c61f38c3f,0xd11c1a4e9303f144,0xeca33108ec93190,0x8ac93eb2932ac809]),(limbWord [0x1cd,0xb8e00f9e61f3cc3f,0xd11c1a4e9303f9e6,0xfea3310cfe93190,0xcaedbff2932aca49]),(limbWord [0x1cd,0xb8600f9861f3cc3f,0x911c024c9303f866,0xf0230000fe13180,0xcae18cc210220840]),(limbWord [0x1cd,0xb8e00f9c61f3cc3f,0xd11c1a4e9303f966,0xfca33108fe93190,0xcae9bef2932ac849]),(limbWord [0x1cd,0xb8600f9e61f30c3f,0x911c024c9303f986,0xfe23300cf013000,0xaec0f0280280a00]),(limbWord [0x1cd,0xb8e00f9e61f38c3f,0xd11c1a4e9303f9c6,0xfea3310cfc93190,0x8aed3fb2932aca09])].getD (i % 8) 0)) else (if i < 240 then (if i < 232 then [(limbWord [0x1cd,0xb8e00f9e61f3cc3f,0xd11c1a4e9303f9e6,0xfea3310cfe93190,0xcaedbff2932aca49]),(limbWord [0x1cd,0xb9e00f9e61f3cc7f,0xd11c7a4e9343f9e6,0x1fea3330cff931f0,0xfaedfff29f2bca7b]),(limbWord [0x1cd,0xbae00f9e63f3cc3f,0xd11d9a4e9383f9e6,0x2ffa33d0ffe93390,0xcaefbff2f32ecbcd]),(limbWord [0x1cd,0xbce02f9e61f3cc3f,0xd11e1a4e9303fde6,0x8fea3712cfe93592,0xcafdbff2933aca49]),(limbWord [0x1cd,0xbce02f9e61f3cc3f,0xd11f5a4e9303fde7,0x8fea3f92efe93dd2,0xeafdbff3db3fcb69]),(limbWord [0x1cd,0xb8e00f9e61f3cc3f,0xd11c1a4e9303f9e6,0xfea3310cfe93190,0xcaedbff2932aca49]),(limbWord [0x1cd,0xf8e08f9e61fbcd3f,0xd15c1a5e930bf9e6,0xfea7310cfe97198,0xcbedbff2936aca49]),(limbWord [0x1cf,0xb8e20fde69f3cc3f,0xd51c1ace9323f9e6,0xfeab318cfeb3190,0xceedbff293aaca49])].getD (i % 8) 0 else [(limbWord [0x1dd,0xab655fbae7f75cff,0x933ca24db7d7caaa,0x7d3220655d312225,0x5ae6cd4224203ed6]),(limbWord [0x1dd,0xbbe55fbee7f7dcff,0xd33cba4fb7d7fbee,0x7ffa3375dff933b5,0xdaeffff2b72afedf]),(limbWord [0x1ef,0xfceaafdf69fbed3f,0xd55e1ede932bfdf6,0x8feef71acfef759a,0xcffdbff293faca49]),(limbWord [0x1cd,0xa0700f9871f30e3f,0xb99d536cdb03e001,0xc832a802c81a940,0x2ac92c2fda258928]),(limbWord [0x1cd,0xb8f00f9e71f3ce3f,0xf99d5b6edb03f9e7,0xfeb3b90efe9b9d0,0xeaedbfffdb2fcb69]),(limbWord [0x1d9,0x99f45f14d1f6deef,0x79b97b6f5e46fb6f,0x5bcb1bb1aff999f5,0xf2a9faffdf2fd57b]),(limbWord [0x1dd,0x1af51fb6f7e29a3b,0x7b99db6fea92fbcf,0x6ffb1bd5fbc99bd1,0xa8af3bbffb2fe7ad]),(limbWord [0x1dd,0x9b755fa6f7f4defc,0x3ba1e361fcd4fbef,0x7ff31be5fff19be5,0xfa2fc3cdfc0f37f6])].getD (i % 8) 0) else (if i < 248 then [(limbWord [0x1dd,0xbbf55fbef7f7deff,0xfbbdfb6fffd7fbef,0x7ffb3bf5fff9bbf5,0xfaefffffff2fffff]),(limbWord [0x1dd,0xa0754fb8f5f71ebf,0xbbbc036dff17c008,0xc0320040c01a004,0xac00c0e00203800]),(limbWord [0x1dd,0xab755fbaf7f75eff,0xbbbdf36dffd7eaab,0x7db32ae57db1ab65,0x7aefed6ffe25bffe]),(limbWord [0x1dd,0xb0f54fbcf5f79ebf,0xfbbd5b6fff17f14d,0xecb3b94aec9b9d4,0xaac93ebfdb2ff929]),(limbWord [0x1dd,0xb8f54fbef5f7debf,0xfbbc1b6fff17f9ee,0xfeb3314cfe9b194,0xcaedbffe932afa49]),(limbWord [0x1dd,0xb9755fb8f5f7deff,0xbbbc636dff57fa6f,0x5f0338250ff1b9e5,0xfae1cccf1c233c72]),(limbWord [0x1dd,0xba755fbef7f71ebf,0xbbbd836dff97fb8f,0x6ff33bc5ff01ba05,0xaee0f0fe02c3f84]),(limbWord [0x1dd,0xbbf55fbef7f7deff,0xfbbdfb6fffd7fbef,0x7ffb3bf5fff9bbf5,0xfaefffffff2fffff])].getD (i % 8) 0 else [(limbWord [0x1dd,0xbbf55fbef7f7deff,0xfbbdfb6fffd7fbef,0x7ffb3bf5fff9bbf5,0xfaefffffff2fffff]),(limbWord [0x1e5,0xfc78ae8b31f9ef1e,0xb9d75578db09fcf7,0x87a57e826fe5fdca,0xebfda5efda578b68]),(limbWord [0x1ed,0xfcf8af9f71fbef3f,0xf9df5f7edb0bfdf7,0x8fef7f92efedfdda,0xebfdbfffdb7fcb69]),(limbWord [0x1ee,0xbc7a2fcf79d16636,0xbd9757a8db21fdb7,0x8fe7bf8ae7a6bd42,0x6efda76fda9d8b68]),(limbWord [0x1ef,0xbcfa2fdf79f3ee3f,0xfd9f5feedb23fdf7,0x8fefbf9aefefbdd2,0xeefdbfffdbbfcb69]),(limbWord [0x1ef,0xdc7aafc779f8ef3c,0x3dc347f0d828fdf7,0x8fe7df8aefe7ddca,0xef3d83cdd8df0360]),(limbWord [0x1ef,0xfcfaafdf79fbef3f,0xfddf5ffedb2bfdf7,0x8fefff9aefeffdda,0xeffdbfffdbffcb69]),(limbWord [0x1ef,0xe07a8fd979fb2f3f,0xbddc07fcdb2bc010,0xc07e0080c07e008,0xfc00c0e00e00800])].getD (i % 8) 0))))

def p2AtBlock2 (i : Nat) : Nat := (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then [(limbWord [0x1ef,0xe87a8fdb79fb6f3f,0xbddd57fcdb2be8b3,0xda7ea886da7e948,0x6fedad6fdae58b68]),(limbWord [0x1ef,0xf8fa8fdf79fbef3f,0xfddc1ffedb2bf9f6,0xfeff318cfeff198,0xcfedbffe93eaca49]),(limbWord [0x1ef,0xf8fa8fdf79fbef3f,0xfddd5ffedb2bf9f7,0xfeffb98efeff9d8,0xefedbfffdbefcb69]),(limbWord [0x1ef,0xfc7aafd979fbef3f,0xbdde47fcdb2bfc77,0x8f07fc0a0fe7fdca,0xeff18ccf18f30860]),(limbWord [0x1ef,0xfcfaafdf79fbef3f,0xfdde5ffedb2bfdf7,0x8fefff1acfeffdda,0xeffdbfff9bfbca69]),(limbWord [0x1ef,0xfc7aafdf79fb2f3f,0xbddf07fcdb2bfd97,0x8fe7ff8aef07fc0a,0xffc0f0fc0fc0b00]),(limbWord [0x1ef,0xfcfaafdf79fbef3f,0xfddf1ffedb2bfdf7,0x8fefff9aefeffd9a,0xcffdbfffd3fecb49]),(limbWord [0x1ef,0xfcfaafdf79fbef3f,0xfddf5ffedb2bfdf7,0x8fefff9aefeffdda,0xeffdbfffdbffcb69])].getD (i % 8) 0 else [(limbWord [0x1ff,0xe07fcff9fdff3fbf,0xbffc07fdff3fc018,0xc07e00c0c07e00c,0xfc00c0e00e03800]),(limbWord [0x1ff,0xfbffdfffffffffff,0xfffdfffffffffbff,0x7ffffbfdfffffbfd,0xffefffffffefffff]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff]),(limbWord [0x1f1,0xdd7cfc0181fc7fcc,0x21e264711c4cfe3f,0xd3045c230fb5dd6f,0x7331c0451c511472]),(limbWord [0x1f1,0xdd7cfc0181fcffcc,0x21e264711c4cfe7f,0xd3045c230ff5ddef,0xf331c0c51c531472]),(limbWord [0x1f1,0xddfcfc0181fcffcc,0x61e26c731c4cfe7f,0xd30c5c330ffdddff,0xf331d0d51d535473]),(limbWord [0x1f1,0xddfcfc0181fcffcc,0x61e27c731c4cfe7f,0xd30c5c330ffdddff,0xf331f0f51f53d47b]),(limbWord [0x1f1,0xdf7cfc0183fcffcc,0x21e3e4711cccfe7f,0xf3145ce33ff5dfef,0xf333c0c57c5715f6])].getD (i % 8) 0) else (if i < 280 then [(limbWord [0x1f1,0xddfcfc0581fcffcc,0x61e26c731c4cff7f,0xd34c5d338ffdddff,0xf331d2d51d5b5473]),(limbWord [0x1f1,0xddfcfc0581fcffcc,0x61e37c731c4cff7f,0xd3cc5fb3affdddff,0xf339f2f5df5fd57b]),(limbWord [0x1f1,0xdd7cfc0181fcffcc,0x21e264711c4cfe7f,0xd3045c230ff5ddef,0xf331c0c51c531472]),(limbWord [0x1f1,0xddfcfc1181feffcd,0x61ea6c771c4efe7f,0xd30c5c330ffdddff,0xf331d8d51d735473]),(limbWord [0x1f3,0xdd7efc4189fcffcc,0x25e264f11c6cfe7f,0xd304dc2b0ff7ddef,0xf731c0c51cd31472]),(limbWord [0x1f3,0xdd7efc4199fcffcc,0x2de365f15c6cfe7f,0xd305dcab2ff7ddef,0xf731c0cd5cd71572]),(limbWord [0x1f5,0xff7dfcaba7fdffdc,0xa3e6e471bdddfeff,0xf7347c675ff5ffef,0xfb77c5c53c533ef6]),(limbWord [0x1fb,0xddfefd55c9feffed,0x65ea6ef71c6eff7f,0xdb4edd3b8fffddff,0xf731dad51dfb5473])].getD (i % 8) 0 else [(limbWord [0x1f9,0xddfcfd15c1feffed,0x61ea6e771c4eff7f,0xdb4e5d338ffdddff,0xf331dad51d7b5473]),(limbWord [0x1f1,0xdd7cfe0191fcffce,0x39f375795e4cfe7f,0xd3855ea32ff5ddef,0xf3b9e0efde57957a]),(limbWord [0x1f5,0xfd7cfe8ba1fdffde,0xb1f674799f4dfeff,0xd7a47e234ff5fdef,0xfbfde5e79e539e7a]),(limbWord [0x1f5,0x5e7dbea3b7e8bb1a,0x3bd3d579ea98fedf,0xe7b55ec77bc5dfcb,0xa9bf21affa57a7ac]),(limbWord [0x1f5,0xbe7d3eabb7f1fc1e,0xbb179549f391feff,0xe7b53ec77fe53f83,0xcaffa5ebf216afcc]),(limbWord [0x1f5,0xdf7dfea3b7fcffde,0x3bf3f579fedcfeff,0xf7b55ee77ff5dfef,0xfbbfe1effe57b7fe]),(limbWord [0x1f5,0xff7dfeabb7fdffde,0xbbf7e579ffddfeff,0xf7b57ee77ff5ffef,0xfbffc5cffc573ff6]),(limbWord [0x1f5,0xe07dcea9b5fd3f9e,0xbbf40579ff1dc018,0x40560040c05e00c,0xbc0040e00403800])].getD (i % 8) 0)) else (if i < 304 then (if i < 296 then [(limbWord [0x1f5,0xf47deea9b5fdbf9e,0xbbf75579ff1df45d,0x86857e862ec5fdce,0xabd924afda57b928]),(limbWord [0x1f5,0xf87dceabb5fdff9e,0xbbf41579ff1df8fe,0x7a572044fe5f18c,0xcbeda5ee9242ba48]),(limbWord [0x1f5,0xfd7dfea9b5fdffde,0xbbf66579ff5dfe7f,0xd7057c270ff5fdef,0xfbf1c4cf1c533c72]),(limbWord [0x1f5,0xfe7dfeabb7fd3f9e,0xbbf78579ff9dfe9f,0xe7b57ec77f05fe0f,0xbfe050fe0543f84]),(limbWord [0x1f5,0xff7dfeabb7fdffde,0xbbf7f579ffddfeff,0xf7b57ee77ff5ffef,0xfbffe5effe57bffe]),(limbWord [0x1f5,0xff7dfeabb7fdffde,0xbbf7f579ffddfeff,0xf7b57ee77ff5ffef,0xfbffe5effe57bffe]),(limbWord [0x1f9,0xc07ccf11c1fe3faf,0x31f8067d1e0ec018,0x80640000c05c00c,0x380080600601000]),(limbWord [0x1f9,0xddfcff15c1feffef,0x71fa7e7f1e4eff7f,0xdbce5f338ffdddff,0xf3b9faf79f7bd47b])].getD (i % 8) 0 else [(limbWord [0x1f9,0xddfcff15d1feffef,0x79fb7f7f5e4eff7f,0xdbcf5fb3affdddff,0xf3b9faffdf7fd57b]),(limbWord [0x1fa,0x9d7e7f45d9d476e6,0x3db377a95e64ff3f,0xdbc79faba7b69d67,0x76b9e26fde9d957a]),(limbWord [0x1fb,0x9cfe3f55d9f2fc2f,0x7d1b1fcf5222ff7f,0xcbcf9f9bafef1d93,0xc6b9bafbd3bec549]),(limbWord [0x1fb,0xdd7eff45d9fcffee,0x3df377f95e6cff7f,0xdbc7dfabaff7ddef,0xf7b9e2efdedf957a]),(limbWord [0x1fb,0xddfeff55d9feffef,0x7dfb7fff5e6eff7f,0xdbcfdfbbafffddff,0xf7b9faffdfffd57b]),(limbWord [0x1fb,0xc97edf51d9fe7fef,0x3df977fd5e6eea3b,0x5987caa92db7c96d,0x77a9e86fdee5957a]),(limbWord [0x1fb,0xd8fecf55d9feffaf,0x7df81fff5e2ef97e,0xbcfd3188fefd19c,0xc7a9bafe93ead049]),(limbWord [0x1fb,0xdd7eff51d9feffef,0x3dfa67fd5e6efe7f,0xdb07dc2b0ff7ddef,0xf7b1c8cf1cf31472])].getD (i % 8) 0) else (if i < 312 then [(limbWord [0x1fb,0xdd7eff51d9feffef,0x3dfb77fd5e6efe7f,0xdb87deab2ff7ddef,0xf7b9e8efdef7957a]),(limbWord [0x1fb,0xddfeff55d9feffef,0x7dfa7fff5e6eff7f,0xdbcfdf3b8fffddff,0xf7b9faff9ffbd47b]),(limbWord [0x1fb,0xdc7eff55d9fe3faf,0x3dfb07fd5e2eff1f,0xcbc7df8baf07dc0f,0x7b80a0fc0fc1500]),(limbWord [0x1fb,0xdd7eff55d9feffef,0x3dfb67fd5e6eff7f,0xdbc7dfabaff7ddef,0xf7b9cacfdcff1572]),(limbWord [0x1fb,0xddfeff55d9feffef,0x7dfb7fff5e6eff7f,0xdbcfdfbbafffddff,0xf7b9faffdfffd57b]),(limbWord [0x1fd,0xfffdffbff7ffffff,0xfbffff7fffdfffff,0xffff7ff7fffdffff,0xfbffffffff7fffff]),(limbWord [0x1ff,0xe07fcff9fdff3fbf,0xbffc07fdff3fc018,0xc07e00c0c07e00c,0xfc00c0e00e03800]),(limbWord [0x1ff,0xff7ffffbffffffff,0xbffff7fdfffffeff,0xffb7feef7ff7ffef,0xffffedeffef7bffe])].getD (i % 8) 0 else [(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff]),(limbWord [0x1fc,0xbd7c7f8fe1d576f6,0xb1b676299f45ffbf,0xdfe63f23c7b4bd67,0x7afde7679e199e7a]),(limbWord [0x1fd,0x5cfcbf97e1eabb3b,0x71da5e7f8a0affdf,0xcfee5f13cbcddddb,0xa9bd3bb79b7bc629]),(limbWord [0x1fd,0xe07ccf99e1ff3fbf,0xb1fc067d9f0fc018,0xc0660000c05e00c,0xbc00c0600601800]),(limbWord [0x1fd,0xe97cdf9be1ff7fff,0xb1fc767d9f4feabb,0x5da66a214db5e96d,0x7beded679e619e7a]),(limbWord [0x1fd,0xf0fccf9de1ffbfbf,0xf1fc1e7f9f0ff15c,0xece73108ecdf19c,0x8bc93eb6936ad809]),(limbWord [0x1fd,0xf4fcef9de1ffbfbf,0xf1fe5e7f9f0ff55d,0x8ece7f128ecdfdde,0xabd93eb79b7bd829]),(limbWord [0x1fd,0xfd7cff99e1ffffff,0xb1fe667d9f4ffe7f,0xdf067c230ff5fdef,0xfbf1ccc71c731c72])].getD (i % 8) 0))) else (if i < 352 then (if i < 336 then (if i < 328 then [(limbWord [0x1fd,0xfd7cff99e1ffffff,0xb1fe767d9f4ffe7f,0xdf867e230ff5fdef,0xfbf9ece79e739c7a]),(limbWord [0x1fd,0xfdfcff9de1ffffff,0xf1fe7e7f9f4fff7f,0xdfce7f338ffdfdff,0xfbf9fef79f7bdc7b]),(limbWord [0x1fd,0xfc7cff9fe1ff3fbf,0xb1fe067d9f0fff9f,0xcfe67f03cf05fc0f,0xbfc0f0780781e00]),(limbWord [0x1fd,0xfd7cff9fe1ffffff,0xb1fe667d9f4fffff,0xdfe67f23cff5fdef,0xfbfdcfc79c7b1e72]),(limbWord [0x1fd,0xfdfcff9fe1ffffff,0xf1fe7e7f9f4fffff,0xdfee7f33cffdfdff,0xfbfdfff79f7bde7b]),(limbWord [0x1fd,0xfffdffbfe7ffffff,0xf3fefe7fbfdfffff,0xfffe7f77dffdffff,0xfbfffff7bf7bfeff]),(limbWord [0x1fd,0xfdfcff9ff1ffffff,0xf9ff7f7fdf4fffff,0xdfef7fb3effdfdff,0xfbfdffffdf7fdf7b]),(limbWord [0x1fd,0xff7dffbbf7ffffff,0xbbfff77dffdffeff,0xffb77ee77ff5ffef,0xfbffedeffe77bffe])].getD (i % 8) 0 else [(limbWord [0x1fd,0xfdfdffbff5ffffff,0xfbfe7f7fff5fffff,0xdfef7f37cffdfdff,0xfbfdffff9f7bfe7b]),(limbWord [0x1fd,0xfffdffbff7ffffff,0xfbffff7fffdfffff,0xffff7ff7fffdffff,0xfbffffffff7fffff]),(limbWord [0x1ff,0xe07ecfd9f9ff3fbf,0xbdfc07fddf2fc018,0xc07e0080c07e00c,0xfc00c0e00e01800]),(limbWord [0x1ff,0xfdfeffddf9ffffff,0xfdff7fffdf6fff7f,0xdfcfffbbaffffdff,0xfff9feffdfffdd7b]),(limbWord [0x1ff,0xfdfeffdff9ffffff,0xfdfe7fffdf6fffff,0xdfefff3bcffffdff,0xfffdffff9ffbde7b]),(limbWord [0x1ff,0xfdfeffdff9ffffff,0xfdff7fffdf6fffff,0xdfefffbbeffffdff,0xfffdffffdfffdf7b]),(limbWord [0x1fe,0x1e7f3fe3ff803030,0x3e038781e0b0fe9f,0xefb79ecf73061e03,0xc3e0109e0942784]),(limbWord [0x1fe,0x1e7f3fe7ff803030,0x3e038781e0b0ff9f,0xeff79fcff3061e03,0xc3e0309e09c2784])].getD (i % 8) 0) else (if i < 344 then [(limbWord [0x1fe,0x1eff3fe7ff803030,0x7e038f83e0b0ff9f,0xefff9fdff30e1e13,0xc3e1319e19c6785]),(limbWord [0x1fe,0x1eff3fe7ff803030,0x7e039f83e0b0ff9f,0xefff9fdff30e1e13,0xc3e3339e39ce78d]),(limbWord [0x1fe,0x1f7f3fe7ff803070,0x3e03e781e0f0ff9f,0xfff79feff3161e63,0x3c3e4309ec9d27b6]),(limbWord [0x1fe,0x1eff3fe7ff80b030,0x7e038f83e0b0ffdf,0xefff9fdff34e1e93,0x8c3e1399e19e6785]),(limbWord [0x1fe,0x1eff3fe7ff80b030,0x7e03df83e0b0ffdf,0xefff9fdff3ce1fd3,0xac3f33b9fb9fe7ad]),(limbWord [0x1fe,0x1e7f3fe7ff803030,0x3e038781e0b0ff9f,0xeff79fcff3061e03,0xc3e0309e09c2784]),(limbWord [0x1fe,0x1eff3ff7ff823031,0x7e0b8f87e0b2ff9f,0xefff9fdff30e1e13,0xc3e1b19e1bc6785]),(limbWord [0x1fe,0x5e7fbfe7ff883130,0x3e438791e0b8ff9f,0xeff7dfcff3065e0b,0xd3e0309e0dc2784])].getD (i % 8) 0 else [(limbWord [0x1fe,0x5e7fbfe7ff883330,0x3ec3c7b1e8b8ff9f,0xeff7dfcff306de4b,0x2d3e030de8dd27a4]),(limbWord [0x1fe,0xbf7f7fefff9574f4,0xbe27a781f5f5ffbf,0xfff7bfeff7363e27,0x5e7ec749e49c3fd6]),(limbWord [0x1ff,0x5effbff7ffaab939,0x7e4b8fd7e0baffdf,0xefffdfdffb4f5e9b,0x8d3e1b99e1fe6785]),(limbWord [0x1ff,0x1eff3ff7ffa2b839,0x7e0b8fc7e0b2ffdf,0xefff9fdffb4f1e93,0x8c3e1b99e1be6785]),(limbWord [0x1fe,0x1e7f3fe7ffc03232,0x3f93d7a9eab0ff9f,0xeff79fcff3869f43,0x2cbf232ffa9da7ac]),(limbWord [0x1fe,0xbe7f3fefffd17436,0xbf179789f3b1ffbf,0xeff7bfcff7a63f03,0x4effa76bf29cafcc]),(limbWord [0x1fe,0x9f7f7fe7ffd476f6,0x3fb3f7a9fef4ffbf,0xfff79feff7b69f67,0x7ebfe36ffe9db7fe]),(limbWord [0x1fe,0xbf7f7fefffd576f6,0xbfb7e7a9fff5ffbf,0xfff7bfeff7b6bf67,0x7effc74ffc9d3ff6])].getD (i % 8) 0)) else (if i < 368 then (if i < 360 then [(limbWord [0x1fe,0xa07f4fe9fdd536b6,0xbfb407a9ff35c018,0xc07a00c0406a004,0xec0040e00803800]),(limbWord [0x1fe,0xb47f6fedfdd536b6,0xbfb757a9ff35f51d,0x8ec7bf8ea686bd46,0x2ed9262fda9db928]),(limbWord [0x1fe,0xb87f4feffdd576b6,0xbfb417a9ff35f9be,0xfe7b30cc7a6b104,0x4eeda76e9288ba48]),(limbWord [0x1fe,0xbd7f7fe9fdd576f6,0xbfb667a9ff75fe3f,0xdf07bc2f07b6bd67,0x7ef1c44f1c913c72]),(limbWord [0x1fe,0xbe7f7fefffd536b6,0xbfb787a9ffb5ff9f,0xeff7bfcff706be07,0xefe070fe09c3f84]),(limbWord [0x1fe,0xbf7f7fefffd576f6,0xbfb7f7a9fff5ffbf,0xfff7bfeff7b6bf67,0x7effe76ffe9dbffe]),(limbWord [0x1fe,0xbf7f7fefffd576f6,0xbfb7f7a9fff5ffbf,0xfff7bfeff7b6bf67,0x7effe76ffe9dbffe]),(limbWord [0x1ff,0x7f0ff1fde2383b,0x3f1807cde232c018,0xc07800c08070000,0xc80080a00a02000])].getD (i % 8) 0 else [(limbWord [0x1ff,0x1eff3ff7ffe2b83b,0x7f1b9fcfe2b2ffdf,0xefff9fdffbcf1f93,0x8cbf3bbbf3bee78d]),(limbWord [0x1ff,0x1eff3ff7ffe2ba3b,0x7f9bdfefeab2ffdf,0xefff9fdffbcf9fd3,0xacbf3bbffbbfe7ad]),(limbWord [0x1ff,0x5e7fbfe7ffe8bb3a,0x3fd3d7f9eab8ffdf,0xeff7dfcffbc7dfcb,0xadbf23affadfa7ac]),(limbWord [0x1ff,0x5effbff7ffeabb3b,0x7fdbdfffeabaffdf,0xefffdfdffbcfdfdb,0xadbf3bbffbffe7ad]),(limbWord [0x1ff,0x4a7f9ff3ffea3b3b,0x3fd9d7fdeabaea9b,0x6db7cacd7987cb49,0x2daf292ffae5a7ac]),(limbWord [0x1ff,0x58ff8ff7fdeabb3b,0x7fd81fffea3af9de,0xfefd31ccbcfd198,0x8dad3bbe93eae209]),(limbWord [0x1ff,0x5c7fbff1fdeabb3b,0x3fda47fdea3afe5f,0xcf07dc0f0bc7ddcb,0xadb1088f18f32420]),(limbWord [0x1ff,0x5e7fbff7ffea3b3b,0x3fdb87fdeabaff9f,0xeff7dfcffb07de0b,0xdbe0b0fe0fc2784])].getD (i % 8) 0) else (if i < 376 then [(limbWord [0x1ff,0x5e7fbff7ffea3b3b,0x3fdbd7fdeabaff9f,0xeff7dfcffb87df4b,0x2dbf2b2ffafda7ac]),(limbWord [0x1ff,0x5effbff7ffeabb3b,0x7fdb9fffeabaffdf,0xefffdfdffbcfdf9b,0x8dbf3bbff3fee78d]),(limbWord [0x1ff,0x5e7fbff7ffeabb3b,0x3fdbc7fdeabaffdf,0xeff7dfcffbc7dfcb,0xadbf0b8ff8ff27a4]),(limbWord [0x1ff,0x5effbff7ffeabb3b,0x7fdbdfffeabaffdf,0xefffdfdffbcfdfdb,0xadbf3bbffbffe7ad]),(limbWord [0x1ff,0xbfff7ffffff7feff,0xffbfffeffff7ffff,0xffffbfffffffbff7,0xfeffffffffbfffff]),(limbWord [0x1ff,0xe07fcff9fdff3fbf,0xbffc07fdff3fc018,0xc07e00c0c07e00c,0xfc00c0e00e03800]),(limbWord [0x1ff,0xff7fffffffff7fff,0xbffff7fdffffffbf,0xfff7ffefffb7ff6f,0x7fffef6ffefdbffe]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff])].getD (i % 8) 0 else [(limbWord [0x1ff,0xa07f0ff9fdf33c3f,0xbf1c07cdf333c018,0xc07a00c0c072000,0xec00c0a00a02800]),(limbWord [0x1ff,0xaa7f1ffbfff37c3f,0xbf1d97cdf3b3eabb,0x6db7aacd7da72b01,0x4eefad6bf2a4afcc]),(limbWord [0x1ff,0xb0ff0ffdfdf3bc3f,0xff1c1fcff333f15c,0xecfb31c8ecf3190,0x8ec93eba93aae809]),(limbWord [0x1ff,0xb4ff2ffdfdf3bc3f,0xff1f1fcff333f55d,0x8ecfbf9eaecf3d92,0x8ed93ebbd3bee909]),(limbWord [0x1ff,0xbc7f3ff9fdf3fc3f,0xbf1e07cdf333fe7f,0xcf07bc0f0fe73d83,0xcef18ccb10b22c40]),(limbWord [0x1ff,0xbe7f3ffffff33c3f,0xbf1f87cdf3b3ff9f,0xeff7bfcfff073e03,0xefe0f0be0bc2f84]),(limbWord [0x1ff,0xbe7f3ffffff33c3f,0xbf1f97cdf3b3ff9f,0xeff7bfcfff873f03,0xeff2f2bf2bcaf8c]),(limbWord [0x1ff,0xbeff3ffffff3bc3f,0xff1f9fcff3b3ffdf,0xefffbfdfffcf3f93,0x8eff3fbbf3beef8d])].getD (i % 8) 0))))

def p2AtBlock3 (i : Nat) : Nat := (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then [(limbWord [0x1ff,0xbe7f3ffffff3fc3f,0xbf1f87cdf3b3ffff,0xeff7bfcfffe73f83,0xceff8fcbf0be2fc4]),(limbWord [0x1ff,0xbeff3ffffff3fc3f,0xff1f9fcff3b3ffff,0xefffbfdfffef3f93,0xceffbffbf3beefcd]),(limbWord [0x1ff,0xbfff7ffffff7fcff,0xff3fbfcff7f7ffff,0xffffbfffffff3fb7,0xdefffffbf7beffdf]),(limbWord [0x1ff,0xbeff3ffffff3fe3f,0xff9fdfeffbb3ffff,0xefffbfdfffefbfd3,0xeeffbffffbbfefed]),(limbWord [0x1ff,0xbf7f7ffffff77eff,0xbfbff7edfff7ffbf,0xfff7bfefffb7bf67,0x7effef6ffebdbffe]),(limbWord [0x1ff,0xbeff7ffffff7febf,0xffbf9fefffb7ffff,0xefffbfdfffefbf97,0xceffbffff3beffcd]),(limbWord [0x1ff,0xbfff7ffffff7feff,0xffbfffeffff7ffff,0xffffbfffffffbff7,0xfeffffffffbfffff]),(limbWord [0x1ff,0xe07f8ff9fdfb3f3f,0xbfdc07fdfb3bc018,0xc07e00c0c07e008,0xfc00c0e00e02800])].getD (i % 8) 0 else [(limbWord [0x1ff,0xfeffbffffffbbf3f,0xffdfdffffbbbffdf,0xefffffdfffcfffdb,0xafff3fbffbffefad]),(limbWord [0x1ff,0xfeffbffffffbff3f,0xffdf9ffffbbbffff,0xefffffdfffefff9b,0xcfffbffff3feefcd]),(limbWord [0x1ff,0xfeffbffffffbff3f,0xffdfdffffbbbffff,0xefffffdfffefffdb,0xefffbffffbffefed]),(limbWord [0x1ff,0xc07fcfe1fdfc3fbc,0x3fe007f1fc3cc018,0xc07c00c0c07c00c,0xf00000c00c03000]),(limbWord [0x1ff,0xcb7fdfe3fffc7ffc,0x3fe1e7f1fcfceabb,0x7db7caed7db7cb6d,0x7f2fc14dfcc537f6]),(limbWord [0x1ff,0xd47fefe5fdfcbfbc,0x3fe347f1fc3cf55d,0x8ec7df8eaec7ddce,0xaf19028dd8df3120]),(limbWord [0x1ff,0xd87fcfe7fdfcffbc,0x3fe007f1fc3cf9fe,0xfe7d30ccfe7d18c,0xcf2d83cc90ca3240]),(limbWord [0x1ff,0xdf7fffe7fffcfffc,0x3fe3e7f1fcfcffff,0xfff7dfeffff7dfef,0xff3fc3cdfcdf37f6])].getD (i % 8) 0) else (if i < 408 then [(limbWord [0x1ff,0xff7fffeffffdfffc,0xbfe7e7f1fdfdffff,0xfff7ffeffff7ffef,0xff7fc7cdfcdf3ff6]),(limbWord [0x1ff,0xdf7fffe7fffcfffe,0x3ff3f7f9fefcffff,0xfff7dfeffff7dfef,0xffbfe3effedfb7fe]),(limbWord [0x1ff,0xff7fffeffffdfffe,0xbff7f7f9fffdffff,0xfff7ffeffff7ffef,0xffffe7effedfbffe]),(limbWord [0x1ff,0xe07fcfe9fdfd3fbe,0xbff407f9ff3dc018,0xc07e00c0c07e00c,0xfc0040e00c03800]),(limbWord [0x1ff,0xff7fffeffffdfffe,0xbff7e7f9fffdffff,0xfff7ffeffff7ffef,0xffffc7cffcdf3ff6]),(limbWord [0x1ff,0xff7fffeffffdfffe,0xbff7f7f9fffdffff,0xfff7ffeffff7ffef,0xffffe7effedfbffe]),(limbWord [0x1ff,0xdd7ffff1fdfeffff,0x3ffa67fdfe7efe7f,0xdf07dc2f0ff7ddef,0xffb1c8cf1cf33472]),(limbWord [0x1ff,0xde7ffff7fffe3fbf,0x3ffb87fdfebeff9f,0xeff7dfcfff07de0f,0xfbe0b0fe0fc3784])].getD (i % 8) 0 else [(limbWord [0x1ff,0xdffffff7fffeffff,0x7ffbfffffefeffff,0xffffdfffffffdfff,0xffbffbfffffff7ff]),(limbWord [0x1ff,0xdf7ffff7fffeffff,0x3ffbe7fdfefeffff,0xfff7dfeffff7dfef,0xffbfcbcffcff37f6]),(limbWord [0x1ff,0xdffffff7fffeffff,0x7ffbfffffefeffff,0xffffdfffffffdfff,0xffbffbfffffff7ff]),(limbWord [0x1ff,0xe07fcff9fdff3fbf,0xbffc07fdff3fc018,0xc07e00c0c07e00c,0xfc00c0e00e03800]),(limbWord [0x1ff,0xf8ffcffffdffffbf,0xfffc1fffff3ff9fe,0xfeff31ccfeff19c,0xcfedbffe93eafa49]),(limbWord [0x1ff,0xfbffdfffffffffff,0xfffdfffffffffbff,0x7ffffbfdfffffbfd,0xffefffffffefffff]),(limbWord [0x1ff,0xfd7ffff9fdffffff,0xbffe67fdff7ffe7f,0xdf07fc2f0ff7fdef,0xfff1cccf1cf33c72]),(limbWord [0x1ff,0xfdfffffdfdffffff,0xfffe7fffff7fff7f,0xdfcfff3f8ffffdff,0xfff9feff9ffbfc7b])].getD (i % 8) 0)) else (if i < 432 then (if i < 424 then [(limbWord [0x1ff,0xfe7fffffffff3fbf,0xbfff87fdffbfff9f,0xeff7ffcfff07fe0f,0xffe0f0fe0fc3f84]),(limbWord [0x1ff,0xfeffffffffffbfbf,0xffff9fffffbfffdf,0xefffffdfffcfff9f,0x8fff3fbff3feff8d]),(limbWord [0x1ff,0xff7fffffffffffff,0xbfffe7fdffffffff,0xfff7ffeffff7ffef,0xffffcfcffcff3ff6]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff]),(limbWord [0x1ff,0xe07fcff9fdff3fbf,0xbffc07fdff3fc018,0xc07e00c0c07e00c,0xfc00c0e00e03800]),(limbWord [0x1ff,0xe07fcff9fdff3fbf,0xbffc07fdff3fc018,0xc07e00c0c07e00c,0xfc00c0e00e03800]),(limbWord [0x1ff,0xe0ffcff9fdff3fbf,0xfffc0fffff3fc018,0xc0fe01c0c0fe01c,0xfc01c1e01e07801])].getD (i % 8) 0 else [(limbWord [0x1ff,0xe0ffcff9fdff3fbf,0xfffc1fffff3fc018,0xc0fe01c0c0fe01c,0xfc03c3e03e0f809]),(limbWord [0x1ff,0xe0ffcff9fdff3fbf,0xfffc1fffff3fc018,0xc0fe01c0c0fe01c,0xfc03c3e03e0f809]),(limbWord [0x1ff,0xe17fcff9fdff3fff,0xbffc67fdff7fc018,0x1c07e02c0c17e06c,0x3fc04c0e0ce13832]),(limbWord [0x1ff,0xe0ffcff9fdffbfbf,0xfffc0fffff3fc058,0xc0fe01c0c4fe09c,0x8fc01c9e01e27801]),(limbWord [0x1ff,0xe27fcff9ffff3fbf,0xbffd87fdffbfc018,0x2c17e0cc3c07e20c,0xfc20c0e60e43984]),(limbWord [0x1ff,0xe0ffcffdfdff3fbf,0xfffc0fffff3fc118,0xc4fe11c8c0fe01c,0xfc01e1e01e87801]),(limbWord [0x1ff,0xe47feff9fdff3fbf,0xbffe07fdff3fc418,0x8c07e40e0c07e40e,0xfd00c0e00f03800]),(limbWord [0x1ff,0xe37fdff9ffff3fff,0xbffde7fdffffc219,0x7c17e8ed3c17ea6d,0x3fc24c0f6ce53db6])].getD (i % 8) 0) else (if i < 440 then [(limbWord [0x1ff,0xe47feff9fdff3fbf,0xbfff47fdff3fc419,0x8c07ec8e2c07ec4e,0x2fd00c0f48f53920]),(limbWord [0x1ff,0xeb7fdffbffff7fff,0xbffca7fdffffcaba,0x7d37e06d5d37e22d,0x5fe6cd4e24e03ed6]),(limbWord [0x1ff,0xf4ffeffdfdffbfbf,0xfffe0fffff3fd55c,0x8e4ff51e8e4ff49e,0x8fd01e9e01fa7801]),(limbWord [0x1ff,0xf0ffcffdfdffbfbf,0xfffc0fffff3fd15c,0xe4ff11c8e4ff09c,0x8fc01e9e01ea7801]),(limbWord [0x1ff,0xe07fcff9fdff3fbf,0xbffd57fdff3fe019,0xc87ea8c2c87e94c,0x2fc92c2fdae5b928]),(limbWord [0x1ff,0xe87fcffbfdff7fbf,0xbffc17fdff3fe8ba,0xda7e20c4da7e10c,0x4fedad6e92e0ba48]),(limbWord [0x1ff,0xe97fdff9fdff7fff,0xbffc77fdff7fea3b,0x5d87ea2d0db7e96d,0x7fe9ec6f9ee1bc7a]),(limbWord [0x1ff,0xea7fdffbffff3fbf,0xbffd97fdffbfea9b,0x6db7eacd7d87eb0d,0xfef2d2ff2e4bf8c])].getD (i % 8) 0 else [(limbWord [0x1ff,0xeb7fdffbffff7fff,0xbffde7fdffffeabb,0x7db7eaed7db7eb6d,0x7fefcd4ffce53ff6]),(limbWord [0x1ff,0xeb7fdffbffff7fff,0xbffdf7fdffffeabb,0x7db7eaed7db7eb6d,0x7fefed6ffee5bffe]),(limbWord [0x1ff,0xeb7fdffbffff7fff,0xbffdf7fdffffeabb,0x7db7eaed7db7eb6d,0x7fefed6ffee5bffe]),(limbWord [0x1ff,0xf0ffcffdfdffbfbf,0xfffc1fffff3ff15c,0xecff31c8ecff19c,0x8fc93ebe93eaf809]),(limbWord [0x1ff,0xf0ffcffdfdffbfbf,0xfffd5fffff3ff15d,0xecffb9caecff9dc,0xafc93ebfdbeff929]),(limbWord [0x1ff,0xf47feff9fdffbfbf,0xbfff57fdff3ff45d,0x8e87fe8e2ec7fdce,0xafd92cafdaf7b928]),(limbWord [0x1ff,0xf4ffeffdfdffbfbf,0xfffe5fffff3ff55d,0x8ecfff1e8ecffdde,0xafd93ebf9bfbf829]),(limbWord [0x1ff,0xf47feffdfdff3fbf,0xbfff57fdff3ff51d,0x8ec7ff8eae87fd4e,0x2fd92e2fdafdb928])].getD (i % 8) 0))) else (if i < 480 then (if i < 464 then (if i < 456 then [(limbWord [0x1ff,0xf4ffeffdfdffbfbf,0xffff1fffff3ff55d,0x8ecfff9eaecffd9e,0x8fd93ebfd3fef909]),(limbWord [0x1ff,0xf47feffdfdffbfbf,0xbfff47fdff3ff55d,0x8ec7ff8eaec7fdce,0xafd90e8fd8ff3920]),(limbWord [0x1ff,0xf4ffeffdfdffbfbf,0xffff5fffff3ff55d,0x8ecfff9eaecffdde,0xafd93ebfdbfff929]),(limbWord [0x1ff,0xfbffdfffffffffff,0xfffdfffffffffbff,0x7ffffbfdfffffbfd,0xffefffffffefffff]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff]),(limbWord [0x1ff,0xf87fcffffdffffbf,0xbffc07fdff3ff9fe,0xfe7f30ccfe7f18c,0xcfed8fce90ea3a40]),(limbWord [0x1ff,0xf8ffcffffdffffbf,0xfffc1fffff3ff9fe,0xfeff31ccfeff19c,0xcfedbffe93eafa49]),(limbWord [0x1ff,0xfbffdfffffffffff,0xfffcbffffffffbfe,0x7ffff37ddffff3bd,0xdfeffffeb7eafedf])].getD (i % 8) 0 else [(limbWord [0x1ff,0xf8ffcffffdffffbf,0xfffd5fffff3ff9ff,0xfeffb9cefeff9dc,0xefedbfffdbeffb69]),(limbWord [0x1ff,0xf9ffdffdfdffffff,0xfffd7fffff7ffb7f,0x5fcffbbdaffff9fd,0xffe9feffdfeffd7b]),(limbWord [0x1ff,0xfaffdfffffffbfbf,0xfffddfffffbffbdf,0x6ffffbddffcffbdd,0xafef3fbffbefffad]),(limbWord [0x1ff,0xfb7fdfffffffffff,0xbffde7fdfffffbff,0x7ff7fbedfff7fbed,0xffefcfcffcef3ff6]),(limbWord [0x1ff,0xfbffdfffffffffff,0xfffdfffffffffbff,0x7ffffbfdfffffbfd,0xffefffffffefffff]),(limbWord [0x1ff,0xfcffeffffdffffbf,0xffff5fffff3ffdff,0x8fefff9eefeffdde,0xeffdbfffdbfffb69]),(limbWord [0x1ff,0xfd7ffff9fdffffff,0xbffe67fdff7ffe7f,0xdf07fc2f0ff7fdef,0xfff1cccf1cf33c72]),(limbWord [0x1ff,0xff7ffffbffffffff,0xbffee7fdfffffeff,0xff37fc6f5ff7ffef,0xfff7cdcf3cf33ef6])].getD (i % 8) 0) else (if i < 472 then [(limbWord [0x1ff,0xfd7ffff9fdffffff,0xbfff77fdff7ffe7f,0xdf87feaf2ff7fdef,0xfff9ecefdef7bd7a]),(limbWord [0x1ff,0xfd7ffffbfdffffff,0xbffe77fdff7ffeff,0xdfa7fe2f4ff7fdef,0xfffdedef9ef3be7a]),(limbWord [0x1ff,0xff7ffffbffffffff,0xbffff7fdfffffeff,0xffb7feef7ff7ffef,0xffffedeffef7bffe]),(limbWord [0x1ff,0xfdfffffdfdffffff,0xfffe7fffff7fff7f,0xdfcfff3f8ffffdff,0xfff9feff9ffbfc7b]),(limbWord [0x1ff,0xfdfffffdfdffffff,0xffff7fffff7fff7f,0xdfcfffbfaffffdff,0xfff9feffdffffd7b]),(limbWord [0x1ff,0xfdfffffffdffffff,0xfffe7fffff7fffff,0xdfefff3fcffffdff,0xfffdffff9ffbfe7b]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff]),(limbWord [0x1ff,0xfe7fffffffff3fbf,0xbfff87fdffbfff9f,0xeff7ffcfff07fe0f,0xffe0f0fe0fc3f84])].getD (i % 8) 0 else [(limbWord [0x1ff,0xff7fffffffff7fff,0xbfffa7fdffffffbf,0xfff7ffefff37fe2f,0x5ffecf4fe4fc3fd6]),(limbWord [0x1ff,0xfe7fffffffff3fbf,0xbfffd7fdffbfff9f,0xeff7ffcfff87ff4f,0x2fff2f2ffafdbfac]),(limbWord [0x1ff,0xfe7fffffffff7fbf,0xbfff97fdffbfffbf,0xeff7ffcfffa7ff0f,0x4fffaf6ff2fcbfcc]),(limbWord [0x1ff,0xff7fffffffff7fff,0xbffff7fdffffffbf,0xfff7ffefffb7ff6f,0x7fffef6ffefdbffe]),(limbWord [0x1ff,0xfeffffffffffbfbf,0xffff9fffffbfffdf,0xefffffdfffcfff9f,0x8fff3fbff3feff8d]),(limbWord [0x1ff,0xfeffffffffffbfbf,0xffffdfffffbfffdf,0xefffffdfffcfffdf,0xafff3fbffbffffad]),(limbWord [0x1ff,0xfeffffffffffffbf,0xffff9fffffbfffff,0xefffffdfffefff9f,0xcfffbffff3feffcd]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff])].getD (i % 8) 0)) else [(limbWord [0x1ff,0xff7fffffffffffff,0xbfffe7fdffffffff,0xfff7ffeffff7ffef,0xffffcfcffcff3ff6]),(limbWord [0x1ff,0xff7fffffffffffff,0xbffff7fdffffffff,0xfff7ffeffff7ffef,0xffffefeffeffbffe]),(limbWord [0x1ff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff])].getD (i % 8) 0))

def p2At (i : Nat) : Nat := (if i < 256 then (if i < 128 then p2AtBlock0 i else p2AtBlock1 i) else (if i < 384 then p2AtBlock2 i else p2AtBlock3 i))

def wireSAt (i : Nat) := if i < 483 then wireAt i else 0

def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 483 then (wireAt i,p1At i,p2At i) else (0,0,0)

def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_0 : ∀ i, 0 ≤ i → i < 8 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_8 : ∀ i, 8 ≤ i → i < 16 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 8 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_16 : ∀ i, 16 ≤ i → i < 24 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 16 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_24 : ∀ i, 24 ≤ i → i < 32 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 24 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_32 : ∀ i, 32 ≤ i → i < 40 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 32 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_40 : ∀ i, 40 ≤ i → i < 48 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 40 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_48 : ∀ i, 48 ≤ i → i < 56 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 48 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_56 : ∀ i, 56 ≤ i → i < 64 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 56 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_64 : ∀ i, 64 ≤ i → i < 72 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 64 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_72 : ∀ i, 72 ≤ i → i < 80 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 72 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_80 : ∀ i, 80 ≤ i → i < 88 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 80 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_88 : ∀ i, 88 ≤ i → i < 96 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 88 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_96 : ∀ i, 96 ≤ i → i < 104 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 96 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_104 : ∀ i, 104 ≤ i → i < 112 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 104 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_112 : ∀ i, 112 ≤ i → i < 120 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 112 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_120 : ∀ i, 120 ≤ i → i < 128 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 120 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_128 : ∀ i, 128 ≤ i → i < 136 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 128 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_136 : ∀ i, 136 ≤ i → i < 144 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 136 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_144 : ∀ i, 144 ≤ i → i < 152 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 144 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_152 : ∀ i, 152 ≤ i → i < 160 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 152 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_160 : ∀ i, 160 ≤ i → i < 168 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 160 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_168 : ∀ i, 168 ≤ i → i < 176 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 168 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_176 : ∀ i, 176 ≤ i → i < 184 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 176 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_184 : ∀ i, 184 ≤ i → i < 192 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 184 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_192 : ∀ i, 192 ≤ i → i < 200 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 192 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_200 : ∀ i, 200 ≤ i → i < 208 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 200 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_208 : ∀ i, 208 ≤ i → i < 216 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 208 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_216 : ∀ i, 216 ≤ i → i < 224 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 216 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_224 : ∀ i, 224 ≤ i → i < 232 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 224 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_232 : ∀ i, 232 ≤ i → i < 240 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 232 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_240 : ∀ i, 240 ≤ i → i < 248 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 240 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_248 : ∀ i, 248 ≤ i → i < 256 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 248 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_256 : ∀ i, 256 ≤ i → i < 264 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 256 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_264 : ∀ i, 264 ≤ i → i < 272 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 264 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_272 : ∀ i, 272 ≤ i → i < 280 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 272 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_280 : ∀ i, 280 ≤ i → i < 288 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 280 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_288 : ∀ i, 288 ≤ i → i < 296 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 288 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_296 : ∀ i, 296 ≤ i → i < 304 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 296 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_304 : ∀ i, 304 ≤ i → i < 312 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 304 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_312 : ∀ i, 312 ≤ i → i < 320 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 312 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_320 : ∀ i, 320 ≤ i → i < 328 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 320 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_328 : ∀ i, 328 ≤ i → i < 336 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 328 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_336 : ∀ i, 336 ≤ i → i < 344 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 336 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_344 : ∀ i, 344 ≤ i → i < 352 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 344 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_352 : ∀ i, 352 ≤ i → i < 360 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 352 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_360 : ∀ i, 360 ≤ i → i < 368 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 360 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_368 : ∀ i, 368 ≤ i → i < 376 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 368 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_376 : ∀ i, 376 ≤ i → i < 384 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 376 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_384 : ∀ i, 384 ≤ i → i < 392 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 384 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_392 : ∀ i, 392 ≤ i → i < 400 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 392 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_400 : ∀ i, 400 ≤ i → i < 408 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 400 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_408 : ∀ i, 408 ≤ i → i < 416 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 408 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_416 : ∀ i, 416 ≤ i → i < 424 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 416 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_424 : ∀ i, 424 ≤ i → i < 432 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 424 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_432 : ∀ i, 432 ≤ i → i < 440 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 432 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_440 : ∀ i, 440 ≤ i → i < 448 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 440 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_448 : ∀ i, 448 ≤ i → i < 456 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 448 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_456 : ∀ i, 456 ≤ i → i < 464 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 456 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_464 : ∀ i, 464 ≤ i → i < 472 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 464 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_472 : ∀ i, 472 ≤ i → i < 480 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 8 472 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_all_480 : ∀ i, 480 ≤ i → i < 483 → wireDOK i = true := span_ok (by decide +kernel : span (wireDOK) 3 480 = true)

theorem wireD_all : ∀ i, 0 ≤ i → i < 483 → wireDOK i = true := (range_split (range_split (range_split (range_split (range_split (range_split wireD_all_0 wireD_all_8) (range_split wireD_all_16 wireD_all_24)) (range_split (range_split wireD_all_32 wireD_all_40) (range_split wireD_all_48 wireD_all_56))) (range_split (range_split (range_split wireD_all_64 wireD_all_72) (range_split wireD_all_80 wireD_all_88)) (range_split (range_split wireD_all_96 wireD_all_104) (range_split wireD_all_112 wireD_all_120)))) (range_split (range_split (range_split (range_split wireD_all_128 wireD_all_136) (range_split wireD_all_144 wireD_all_152)) (range_split (range_split wireD_all_160 wireD_all_168) (range_split wireD_all_176 wireD_all_184))) (range_split (range_split (range_split wireD_all_192 wireD_all_200) (range_split wireD_all_208 wireD_all_216)) (range_split (range_split wireD_all_224 wireD_all_232) (range_split wireD_all_240 wireD_all_248))))) (range_split (range_split (range_split (range_split (range_split wireD_all_256 wireD_all_264) (range_split wireD_all_272 wireD_all_280)) (range_split (range_split wireD_all_288 wireD_all_296) (range_split wireD_all_304 wireD_all_312))) (range_split (range_split (range_split wireD_all_320 wireD_all_328) (range_split wireD_all_336 wireD_all_344)) (range_split (range_split wireD_all_352 wireD_all_360) (range_split wireD_all_368 wireD_all_376)))) (range_split (range_split (range_split (range_split wireD_all_384 wireD_all_392) (range_split wireD_all_400 wireD_all_408)) (range_split (range_split wireD_all_416 wireD_all_424) (range_split wireD_all_432 wireD_all_440))) (range_split (range_split (range_split wireD_all_448 wireD_all_456) (range_split wireD_all_464 wireD_all_472)) wireD_all_480))))

theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 483 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := wireD_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]

def stateWordDataBlock0 (i : Nat) : Nat := (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then [0x1a5c7e054e7d5,0x19ea7b81567d5,0x1d7c0c314e7d5,0x1cea7d11567d5,0x1a5c7d11567d5,0x19ca7c315e7c5,0x1bca7d055e7d5,0x1c9a7d115e7d5].getD (i % 8) 0 else [0x1cec7b81567d5,0x1d7c7b814e7d5,0x1d7c0c3194af5,0x1bcbfc315e7d5,0x1bbd0c315e7d5,0x1ceced3d5e7d5,0x1a0863814e7d5,0x1cea7d1194af5].getD (i % 8) 0) else (if i < 24 then [0x1d7cec315e7d5,0x1cac0c315e7d5,0x1bbcfd3d5e7d5,0x39d8fa7b818eaf6,0x3697d863815e7d6,0x34b4f93b80fa5e6,0x34b688eb815e7d6,0x34b8fa7d116eaf6].getD (i % 8) 0 else [0x39dcca7d115e7d6,0x3bd9ea7b815e7d6,0x38d9ec0d3d5e7d6,0x36d4f93b815e7d6,0x34b68863818eaf6,0x29f0c7032988af6,0x3afd2c7b815e7d6,0x34b81a7c3194af6].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [0x34b7d8f3815e7d6,0x3af4f863814e7d6,0x39d4f9e3815e7d6,0x34b8f86381567d6,0x34b4f9fb815e756,0x3af81864055e7d6,0x3bdcea7d115e7d6,0x3c19ca7c315e7d6].getD (i % 8) 0 else [0x3af81862bd467d6,0x34b4f862dd66af6,0x34ba3a7c316eaf6,0x34b96b43815e7d6,0x37781a7c31a27d6,0x3b7cec7b815e7d6,0x34b98b45115e7d6,0x34b68863813c7d6].getD (i % 8) 0) else (if i < 56 then [0x34b4fa23b55e7d6,0x34b4f93b814e7d6,0x29f3f702bd447d6,0x34b98c0c9d5e7d6,0x34b4f863815e7e6,0x3637d863815e7d6,0x3bda5c7d115e7d6,0x34b4f93b818eaf6].getD (i % 8) 0 else [0x3934f863815e7d6,0x34f4f863815e7d6,0x3aba5c7e055e7d6,0x34b8f91b815e7d6,0x3af8f863818eaf6,0x34b4f702e55e7d6,0x34b4f93b813c7d6,0x3694f9fb815e7d6].getD (i % 8) 0))) else (if i < 96 then (if i < 80 then (if i < 72 then [0x39d8f702bd527d6,0x34b4f863813c766,0x39d4fa24055e7d6,0x34b8fb1b815e7d6,0x39d4fa22bd467d6,0x34b4f863818e946,0x3794f86381a27d6,0x34b0c702f55e7d6].getD (i % 8) 0 else [0x3bdcec7b815e7d6,0x34b81a7c9da27d6,0x39dc6c7e055e7d6,0x34b9793b815e7d6,0x3794fa24315e7d6,0x3afa5c0c316eaf6,0x3694fa03815e7d6,0x3694f863816eaf6].getD (i % 8) 0) else (if i < 88 then [0x3af9ec0b815e7d6,0x3afd5c0c315e7d6,0x34b9da7c315e7d6,0x38d81a7c31907d6,0x3778fc0c315e7d6,0x3774f8638194af6,0x34b4f863815c7d6,0x29f0c703295e776].getD (i % 8) 0 else [0x3774f9ec315e7d6,0x34b4f86381587d6,0x3634f9fb815e7d6,0x34b4f86b815e7d6,0x3afcec0d115e7d6,0x34b4f8632964af6,0x3794f863815e7d6,0x3778fa7d115e7d6].getD (i % 8) 0)) else (if i < 112 then (if i < 104 then [0x34b81863b95e7d6,0x3a7bba7d115e7d6,0x377b9a7c31c0d16,0x39dc6d1d3d5e7d6,0x34b4fa243194af6,0x38d81b24315e7d6,0x39d8ca7b815e7d6,0x3c14f863818eaf6].getD (i % 8) 0 else [0x3af81863818eaf6,0x39da5a7d116eaf6,0x3af4f8638194af6,0x377a3a7c315e7d6,0x34b4f863815e846,0x3774fa2431a27d6,0x29f0c7031d8aaf6,0x34b8fb45115e7d6].getD (i % 8) 0) else (if i < 120 then [0x3974f863815e7d6,0x373a5b4431c0d16,0x34b4f863815e836,0x34b50863815e7d6,0x34b8fc0c9d5e7d6,0x29f0c70311287d6,0x3b9bbc0c315e7d6,0x34b4f8638194af6].getD (i % 8) 0 else [0x29f3b863814e7d6,0x3174f863815e7c6,0x34b68a2431a27d6,0x34b4f86368fa5e6,0x39d4f8638194af6,0x34b5e93b815e7d6,0x34b7d86381807d6,0x3afc6c7d115e7d6].getD (i % 8) 0))))

def stateWordDataBlock1 (i : Nat) : Nat := (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then [0x34b8fa22bd347d6,0x39d9cc7d3d5e7d6,0x34b8fa13815e7d6,0x3afd5c7b815e7d6,0x3af79863815e7d6,0x34b81a7c314e7d6,0x373a5a7c9dc0d16,0x34b8fbe3815e7d6].getD (i % 8) 0 else [0x39d4fa23818eaf6,0x3afc6d1c315e7d6,0x39d8fb7b815e7d6,0x34b8f9cb815e7d6,0x3374f863815e766,0x3737d86381a2af6,0x3af8c863815e7d6,0x3697e863815e7d6].getD (i % 8) 0) else (if i < 152 then [0x3afbbc0c315e7d6,0x34b8fc0d255e7d6,0x34b7d863a55e7d6,0x34b4f863818e9a6,0x3c1a5c0d115e7d6,0x34b4f86381507d6,0x3afced1b815e7d6,0x38d4fa2431907d6].getD (i % 8) 0 else [0x3777aa7c315e7d6,0x3774f86381567d6,0x34b4f862dd68af6,0x34d4f863815e7d6,0x34b5f9fb815e7d6,0x3c1c6c0c315e7d6,0x34b8fc0abd287d6,0x36968863815e7d6].getD (i % 8) 0)) else (if i < 176 then (if i < 168 then [0x3794f863ddc0d16,0x38d4fa24895e7d6,0x3774f86380fa5e6,0x3794f863816eaf6,0x3af9cc7c315e7d6,0x387bba7c31c0d16,0x3af8f702bd4a7d6,0x2f14f86381567d6].getD (i % 8) 0 else [0x3954f863815e7d6,0x34b6886381567d6,0x34b4fa2431567d6,0x3c1c6a7d115e7d6,0x34b7d863815e756,0x3afccc0c315e7d6,0x39dbba7d115e7d6,0x3afa5c0c9d5e7d6].getD (i % 8) 0) else (if i < 184 then [0x3734f9fb81a2af6,0x38da0a24315e7d6,0x38d7ba7c315e7d6,0x3694f93b815e7d6,0x34b6886380fa5e6,0x37981a7c315e7d6,0x2fb0c702bd447d6,0x34b4f9fba55e7d6].getD (i % 8) 0 else [0x34b8fc35115e7d6,0x34b8fa7b814e7d6,0x3aba0863815e7d6,0x3774f863814e7d6,0x3514f863815e7d6,0x3374f863813c7d6,0x34b8f8e3815e7d6,0x3af8f97b815e7d6].getD (i % 8) 0))) else (if i < 224 then (if i < 208 then (if i < 200 then [0x38d4f9f4315e7d6,0x39da5b45115e7d6,0x34b8fc0c316eaf6,0x34b4f863813e7d6,0x29f0c70311347d6,0x39da0a23815e7d6,0x3794f863695e7d6,0x3774f863818eaf6].getD (i % 8) 0 else [0x34b4f9fb81787d6,0x39d4f86381567d6,0x36f68863815e7d6,0x29f0c7031d8caf6,(limbWord [0x6,0x969f0c702bd1a7d7]),(limbWord [0x7,0x1b4b4f8638194af7]),(limbWord [0x7,0x5e9f0c702bd467d7]),(limbWord [0x6,0x969f0c702bd2e7d7])].getD (i % 8) 0) else (if i < 216 then [(limbWord [0x6,0x971f5c863815e7d7]),(limbWord [0x6,0x969f0c753815e7d7]),(limbWord [0x6,0x971f4f863695e7d7]),(limbWord [0x6,0x969f3f702bcfa537]),(limbWord [0x7,0x3b734fa23815e7d7]),(limbWord [0x7,0x1b854fa24315e7d7]),(limbWord [0x6,0x97034f863813c7d7]),(limbWord [0x6,0x969f3f702bcfa6f7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c702bcfe7d7]),0x29f0c622bcfa506,(limbWord [0x6,0x96a94f863815e7d7]),(limbWord [0x7,0x3b1f4f702bd407d7]),(limbWord [0x6,0x97494f863815e7d7]),(limbWord [0x7,0x5b4b4f863815e7d7]),(limbWord [0x6,0x969f45863815e7d7]),(limbWord [0x7,0x3b634f863815e7d7])].getD (i % 8) 0)) else (if i < 240 then (if i < 232 then [0x34b4f3e94ca03c6,(limbWord [0x6,0x969f31863815e7d7]),(limbWord [0x6,0x969f0c7031d5e507]),(limbWord [0x6,0x97097d863815e7d7]),0x29f0c7fabcfa506,(limbWord [0x6,0x971f0c702bd307d7]),(limbWord [0x6,0x969f0c702bcfa297]),(limbWord [0x6,0x969f0c7031d5e6d7])].getD (i % 8) 0 else [(limbWord [0x6,0xf29f0c702bd1e7d7]),(limbWord [0x6,0x96cd4f863815e7d7]),(limbWord [0x6,0x969f0c723815e7d7]),0x34b0c3e94ca02f6,0x34b4f861aca6506,(limbWord [0x5,0x3e19087bb815e7d7]),(limbWord [0x6,0x96fb65863815e7d7]),(limbWord [0x6,0x96d167863815e7d7])].getD (i % 8) 0) else (if i < 248 then [(limbWord [0x6,0x97314f93b815e7d7]),(limbWord [0x7,0x5f0378863815e7d7]),(limbWord [0x6,0x969f0c702e15e7d7]),0x29ee0622bcfa3c6,(limbWord [0x6,0x97314f863815e7d7]),(limbWord [0x6,0x97034f862bd1e7d7]),(limbWord [0x6,0xd29f0c703615e7d7]),(limbWord [0x6,0x969f0c7f3815e7d7])].getD (i % 8) 0 else [(limbWord [0x7,0x3b4b8fc0b815e7d7]),0x29eff702bcfa3c6,(limbWord [0x6,0x969f44863d15e7d7]),0x218e0622bcfa2f6,(limbWord [0x6,0x969f0c702bd467d7]),0x29f0c703115e6b6,(limbWord [0x7,0x5f4b81a24315e7d7]),(limbWord [0x6,0x969f2b863815e7d7])].getD (i % 8) 0))))

def stateWordDataBlock2 (i : Nat) : Nat := (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then [(limbWord [0x6,0x969f0c702dd5e1e7]),(limbWord [0x6,0x969f0c7ab815e7d7]),0x34ae03e94c782f6,(limbWord [0x7,0x1b4b8fa7d115e7d7]),0x34b4f863818e536,0x34b4f701aca63c6,(limbWord [0x6,0x96d10c702bd407d7]),(limbWord [0x7,0x74b4f863815e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c73b815e7d7]),0x218ff702bcfa2f6,0x29f0c7fb815e6b6,(limbWord [0x6,0x96fb24863815e7d7]),(limbWord [0x6,0x969f0c702bd367d7]),(limbWord [0x6,0x969f44863dda2af7]),(limbWord [0x6,0x969f4497b815e7d7]),(limbWord [0x6,0x969f0c84b815e7d7])].getD (i % 8) 0) else (if i < 280 then [(limbWord [0x6,0xd29f44863815e7d7]),(limbWord [0x6,0x969f0c702bcfa5a7]),0x34b0c701aca62f6,(limbWord [0x6,0x969f0c702bcfa457]),(limbWord [0x7,0x1a9f44862bcfa777]),(limbWord [0x7,0x3b4b4f863814e7d7]),(limbWord [0x6,0xe74b4f863695e7d7]),(limbWord [0x7,0x3a9f0c80b815e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c702bd3c7d7]),(limbWord [0x7,0x5f4b4f8637d5e7d7]),(limbWord [0x6,0x969f0c702bd487d7]),(limbWord [0x6,0x969f0c702dd5e777]),(limbWord [0x7,0x5f1f8b863815e7d7]),(limbWord [0x6,0x969f0c702bcfa577]),(limbWord [0x6,0x969f3486380fa5e7]),(limbWord [0x7,0x3a9f0c702bd467d7])].getD (i % 8) 0)) else (if i < 304 then (if i < 296 then [(limbWord [0x6,0x96d14f86381a27d7]),(limbWord [0x7,0x574b8fa7b815e7d7]),(limbWord [0x6,0x969f0c702bcfa0b7]),(limbWord [0x6,0x96e74f86380fa5e7]),(limbWord [0x6,0x97034f86381907d7]),(limbWord [0x6,0x96f34f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa497]),(limbWord [0x6,0x97294f863815e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f29863815e7d7]),(limbWord [0x6,0x96fb34863815e7d7]),0x3af4f863818eaf6,0x34b4f6d2bcfa3c6,(limbWord [0x6,0xe6fb4f863815e7d7]),(limbWord [0x6,0xee9f0c702bcfa6b7]),(limbWord [0x6,0x4f1f4f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa477])].getD (i % 8) 0) else (if i < 312 then [0x34b4f702bcfa356,(limbWord [0x6,0x969f0c7031d62af7]),(limbWord [0x6,0x96fb73863815e7d7]),(limbWord [0x6,0x969f0c702bcfa177]),(limbWord [0x6,0x969f0c702e95e7d7]),0x34b0c6d2bcfa2f6,0x34b4f863695e6b6,(limbWord [0x6,0x969f0c702bd227d7])].getD (i % 8) 0 else [(limbWord [0x6,0x971f59863815e7d7]),(limbWord [0x6,0x969f0c702bcfa567]),(limbWord [0x6,0x96d14fa24315e7d7]),(limbWord [0x6,0x96d10c702bcfa287]),0x34b4f863814e7d6,(limbWord [0x6,0x96ed4f863815e7d7]),(limbWord [0x6,0x969f44863815e767]),(limbWord [0x6,0x969f0c702bcfa417])].getD (i % 8) 0))) else (if i < 352 then (if i < 336 then (if i < 328 then [(limbWord [0x7,0x1b4ba3a7c315e7d7]),0x34b4f862bcd6506,(limbWord [0x6,0x969f0c702bcfa2d7]),0x29f0c702dd5e1e6,(limbWord [0x6,0x969f0c702bd427d7]),(limbWord [0x6,0x971d4f863815e7d7]),(limbWord [0x6,0x971f81862bd187d7]),(limbWord [0x6,0x971f81923815e7d7])].getD (i % 8) 0 else [(limbWord [0x7,0x5f9da5c7b815e7d7]),(limbWord [0x6,0x969f0c702bcfa397]),(limbWord [0x6,0x969f0c703395e7d7]),(limbWord [0x6,0x969f0c702bcfa627]),0x34b4f9fb80fa536,(limbWord [0x6,0x97034f93c315e7d7]),(limbWord [0x6,0x969f0c702bcfa237]),0x3734f863695e7d6].getD (i % 8) 0) else (if i < 344 then [(limbWord [0x6,0x97194f863815e7d7]),(limbWord [0x6,0xff4b4f863815e7d7]),(limbWord [0x6,0x969f10863815e7d7]),(limbWord [0x7,0x5f4b81863dd5e7d7]),(limbWord [0x6,0xd29f0c702bd407d7]),(limbWord [0x6,0x6f1f4f863815e7d7]),(limbWord [0x6,0x969f30863815e7d7]),(limbWord [0x6,0xef4b81a7c315e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c70320fa507]),(limbWord [0x7,0x3b4b4f863755e7d7]),(limbWord [0x6,0x96cb4f863818eaf7]),(limbWord [0x7,0x6b4b4f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa017]),(limbWord [0x6,0x969f0c702bcfa517]),(limbWord [0x6,0x969f27702bd407d7]),(limbWord [0x6,0x969f21863815e7d7])].getD (i % 8) 0)) else (if i < 368 then (if i < 360 then [(limbWord [0x6,0x969f0c72b815e7d7]),(limbWord [0x7,0x6ec14f863815e7d7]),0x35f4f862bcfa506,(limbWord [0x6,0x969f0c7033d5e7d7]),0x29f0c3e94ca01e6,(limbWord [0x6,0x969f0c70345347d7]),(limbWord [0x6,0x96d10c702bcfa6b7]),(limbWord [0x6,0x969f0c702bcfa647])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c702bcfa197]),(limbWord [0x6,0x969f0c702bcfa1c7]),(limbWord [0x7,0x5f9d81863815e7d7]),0x39d4f863818eaf6,(limbWord [0x7,0x3b4ba3a7b815e7d7]),(limbWord [0x7,0x3b8d8fa7b815e7d7]),(limbWord [0x6,0x969f48863815e7d7]),(limbWord [0x6,0x969f0c743815e7d7])].getD (i % 8) 0) else (if i < 376 then [(limbWord [0x6,0x96d10c702bd347d7]),(limbWord [0x7,0x5f8d4fa24315e7d7]),(limbWord [0x6,0x969f24863818eaf7]),(limbWord [0x7,0x5f4b4f863816eaf7]),0x3afcec7b815e7d6,(limbWord [0x6,0x69f0c703115e7d7]),(limbWord [0x6,0x971f4fa22bd187d7]),(limbWord [0x6,0x969f44862bd347d7])].getD (i % 8) 0 else [(limbWord [0x6,0x97454f863815e7d7]),(limbWord [0x7,0x5f4b8f923815e7d7]),(limbWord [0x6,0x970364863815e7d7]),(limbWord [0x7,0x3b4b4f8d3815e7d7]),(limbWord [0x6,0x969f13863815e7d7]),(limbWord [0x7,0x5f1f0c702bd407d7]),0x34b0c702bcfa2e6,(limbWord [0x6,0x96e34f863815e7d7])].getD (i % 8) 0))))

def stateWordDataBlock3 (i : Nat) : Nat := (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then [(limbWord [0x6,0x69f0c7fb815e7d7]),0x34b4f863813c7d6,0x29ee03e94c781e6,(limbWord [0x7,0x4b4b4e863815e7d7]),(limbWord [0x6,0x969f42863815e7d7]),(limbWord [0x7,0x5fab4f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa287]),(limbWord [0x6,0xe74b4f86381a28c7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c70271187d7]),0x37781a7c315e7d6,0x218e03e94c5e1e6,(limbWord [0x6,0x969f44863b15e7d7]),0x29f0c701aca61e6,(limbWord [0x7,0x6f4b4f85b815e7d7]),(limbWord [0x7,0x5f4b4f863815e7c7]),0x34b4fa24316eaf6].getD (i % 8) 0) else (if i < 408 then [0x34b4f863816e536,(limbWord [0x6,0xef1f4f863815e7d7]),(limbWord [0x6,0x969f0c713815e7d7]),(limbWord [0x6,0x969f0c702bd147d7]),(limbWord [0x6,0x969f0c70295187d7]),(limbWord [0x6,0x96cb4f9fb815e7d7]),(limbWord [0x6,0x969f3a863815e7d7]),(limbWord [0x6,0x96db4f863815e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c77b815e7d7]),(limbWord [0x7,0x4a9f1f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa597]),(limbWord [0x6,0x969f0c702bcfa487]),(limbWord [0x6,0x97474f863813c7d7]),(limbWord [0x6,0x969f0c833815e7d7]),(limbWord [0x6,0x96f94f863815e7d7]),(limbWord [0x6,0xaf4b4f863815e7d7])].getD (i % 8) 0)) else (if i < 432 then (if i < 424 then [(limbWord [0x7,0x4f774f863815e7d7]),(limbWord [0x6,0x97035c863815e7d7]),(limbWord [0x6,0x971f81a23815e7d7]),(limbWord [0x7,0x8b4b4f863815e7d7]),(limbWord [0x6,0xb74b4f863815e7d7]),(limbWord [0x6,0x971f4f862c95e7d7]),(limbWord [0x7,0x3adf4f863815e7d7]),(limbWord [0x6,0x970373a24315e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c702bcfa077]),(limbWord [0x6,0x969f39863815e7d7]),0x29f0c6d2bcfa1e6,(limbWord [0x7,0x5f9d4fa23815e7d7]),(limbWord [0x6,0x96ab4f863815e7d7]),(limbWord [0x7,0x3b4b8fb2b815e7d7]),(limbWord [0x6,0x97474f862bd187d7]),(limbWord [0x6,0x969f0c702bcfa2b7])].getD (i % 8) 0) else (if i < 440 then [(limbWord [0x6,0x969f0c702bcfa617]),(limbWord [0x6,0x969f0c82b815e7d7]),(limbWord [0x6,0x969f2c863815e7d7]),(limbWord [0x5,0x3e18e0622bcfa507]),(limbWord [0x6,0x969f0c70281287d7]),(limbWord [0x6,0x969f15863815e7d7]),(limbWord [0x6,0x969f3f923815e7d7]),(limbWord [0x6,0x969f4486345187d7])].getD (i % 8) 0 else [0x29f0c579f4a01e6,(limbWord [0x6,0x969f0c71b815e7d7]),(limbWord [0x6,0x969f44863814e7d7]),(limbWord [0x6,0x969f0c702bcfa4e7]),(limbWord [0x5,0x3e9544863815e7d7]),(limbWord [0x6,0x969f27702bcfa6b7]),(limbWord [0x6,0x969f0c703295e7d7]),(limbWord [0x6,0x97398fa7c315e7d7])].getD (i % 8) 0))) else (if i < 480 then (if i < 464 then (if i < 456 then [(limbWord [0x6,0x969f0c702bcfa3f7]),(limbWord [0x6,0x969f37863815e7d7]),(limbWord [0x6,0x96e54f863815e7d7]),(limbWord [0x6,0x969f0c702bd127d7]),(limbWord [0x6,0x97034fa4c315e7d7]),(limbWord [0x7,0x3b4b4f863816eaf7]),(limbWord [0x6,0x971f4f702bd4a7d7]),(limbWord [0x6,0x96d94f863815e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x971b4f863815e7d7]),(limbWord [0x6,0x969f20863815e7d7]),(limbWord [0x6,0x969f0c84b818eaf7]),(limbWord [0x6,0x969f27702bcfa6e7]),(limbWord [0x6,0x969f3f9a3815e7d7]),(limbWord [0x6,0x97457d863815e7d7]),(limbWord [0x6,0xee9f0c702bcfa6c7]),(limbWord [0x7,0x7f4b4f863815e7d7])].getD (i % 8) 0) else (if i < 472 then [(limbWord [0x6,0xef734f863815e7d7]),0x34b4f8c3815e6b6,(limbWord [0x6,0x96e74f9fb815e7d7]),(limbWord [0x6,0x969f35863816eaf7]),(limbWord [0x6,0x969f0c79381a2af7]),(limbWord [0x6,0x969f46863815e7d7]),(limbWord [0x6,0x969f0c70344fa127]),(limbWord [0x7,0xf4b4f863816eaf7])].getD (i % 8) 0 else [(limbWord [0x6,0x971f68863815e7d7]),(limbWord [0x7,0x43694f863815e7d7]),(limbWord [0x6,0x969f348d3815e7d7]),(limbWord [0x7,0x334b81a7c315e7d7]),(limbWord [0x7,0x5f8da5c0c315e7d7]),(limbWord [0x6,0x969f0c702bcfa677]),(limbWord [0x6,0x969f0c773815e7d7]),(limbWord [0x7,0x3b4b4fa23dd5e7d7])].getD (i % 8) 0)) else (if i < 496 then (if i < 488 then [(limbWord [0x6,0xf34b4f863815e7d7]),(limbWord [0x6,0x969f47863815e7d7]),(limbWord [0x6,0x971f5d863815e7d7]),(limbWord [0x6,0x969f44863818eaf7]),(limbWord [0x7,0x3b4b4f863815e7c7]),(limbWord [0x6,0x969f32863815e7d7]),0x29f0c702bcd61e6,(limbWord [0x6,0xe69f0c7035da2af7])].getD (i % 8) 0 else [(limbWord [0x6,0x971f6f863815e7d7]),(limbWord [0x6,0x969f33863815e7d7]),0x3774f702bcfa3c6,(limbWord [0x6,0xe74b4f862c95e7d7]),(limbWord [0x6,0x969f0c702bcfa697]),(limbWord [0x7,0x3b738fa7b815e7d7]),(limbWord [0x6,0x96cb4f863816eaf7]),(limbWord [0x7,0x5f4b8fa23815e7d7])].getD (i % 8) 0) else (if i < 504 then [(limbWord [0x7,0x83174f863815e7d7]),(limbWord [0x7,0x1b694f863815e7d7]),(limbWord [0x6,0x969f27933815e7d7]),(limbWord [0x7,0x5f4b4f863695e7d7]),(limbWord [0x7,0x434b4f863815e7d7]),0x3770c702bcfa2f6,(limbWord [0x6,0x969f0c702bcfa337]),(limbWord [0x6,0x969f0c702bcfa217])].getD (i % 8) 0 else [0x3774f863815e6b6,(limbWord [0x6,0x1f034f863815e7d7]),(limbWord [0x6,0x971f65923815e7d7]),(limbWord [0x6,0x96ed4f863818eaf7]),(limbWord [0x6,0x969f0c74b5d5e7d7]),(limbWord [0x7,0x1ac94f863815e7d7]),0x34b4f592bcfa3c6,(limbWord [0x6,0x96e968863815e7d7])].getD (i % 8) 0))))

def stateWordDataBlock4 (i : Nat) : Nat := (if i < 576 then (if i < 544 then (if i < 528 then (if i < 520 then [(limbWord [0x6,0x969f0c702bcfa347]),(limbWord [0x6,0x970373863dd5e7d7]),(limbWord [0x6,0x96dd4f863815e7d7]),0x3674f863815e6b6,(limbWord [0x6,0x969f0c702bd267d7]),(limbWord [0x6,0x97034f863a55e7d7]),(limbWord [0x6,0x57274f863815e7d7]),0x34b0c592bcfa2f6].getD (i % 8) 0 else [0x34b4f862c95e6b6,(limbWord [0x6,0x969f24863816eaf7]),0x34b4f86381147d6,(limbWord [0x6,0x969f0c702bcfa0e7]),(limbWord [0x6,0x969f0c702bcfa607]),(limbWord [0x6,0x97034f862bd287d7]),(limbWord [0x6,0x969f44863813c7d7]),(limbWord [0x6,0x969f0c7032d5e7d7])].getD (i % 8) 0) else (if i < 536 then [(limbWord [0x7,0x5f4b4fa1b815e7d7]),(limbWord [0x7,0x1b4b4f86381567d7]),0x34b4f861f4a6506,(limbWord [0x6,0x96d10c702bcfa6c7]),(limbWord [0x6,0x96fb0c702bcfa6b7]),0x3afc6c0c315e7d6,(limbWord [0x6,0xe74b68863815e7d7]),0x3794f863815e7d6].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c7031d5e517]),(limbWord [0x6,0xb34b4f863815e7d7]),(limbWord [0x6,0x969f0c703451e7d7]),(limbWord [0x7,0x5f4ba3863815e7d7]),(limbWord [0x7,0x5f8d8f863815e7d7]),(limbWord [0x6,0x969f0c702bd1c7d7]),(limbWord [0x6,0x969f0c702bcfa037]),(limbWord [0x6,0x96ad4f863815e7d7])].getD (i % 8) 0)) else (if i < 560 then (if i < 552 then [(limbWord [0x6,0x971f4f97b815e7d7]),(limbWord [0x6,0xd31f4f863815e7d7]),(limbWord [0x6,0x969f2d863815e7d7]),(limbWord [0x6,0x6f034f863815e7d7]),(limbWord [0x6,0x971f0c702bd347d7]),0x34b4f863815e516,(limbWord [0x6,0x96a34f863815e7d7]),0x34b68702bcfa3c6].getD (i % 8) 0 else [(limbWord [0x6,0x96d10c702bcfa717]),0x34b81a7c9d5e7d6,0x34b4f702bcfa3b6,(limbWord [0x6,0x96cb4f863555e7d7]),(limbWord [0x6,0x969f0c7c3815e7d7]),(limbWord [0x6,0xee9f0c702bcfa0c7]),(limbWord [0x6,0x969f0c7bb818eaf7]),(limbWord [0x7,0x5f734f86381a2af7])].getD (i % 8) 0) else (if i < 568 then [(limbWord [0x7,0x329f0c78b815e7d7]),(limbWord [0x5,0x969f0c703115e7d7]),0x34b4f862bcfa4d6,(limbWord [0x6,0x971f4f93b815e7d7]),(limbWord [0x6,0x969f4b9fb815e7d7]),(limbWord [0x7,0x3b4b80863815e7d7]),0x34b68863815e6b6,(limbWord [0x6,0x969f44862bd1e7d7])].getD (i % 8) 0 else [(limbWord [0x7,0x73774f863815e7d7]),(limbWord [0x6,0xee9f0c702bcfa1e7]),(limbWord [0x6,0x969f449a3dd5e7d7]),(limbWord [0x6,0xd29f0c702bcfa107]),(limbWord [0x5,0x969f0c7fb815e7d7]),(limbWord [0x6,0x969f0c703055e7d7]),(limbWord [0x6,0x969f0c702bcfa057]),(limbWord [0x7,0x5e9f0c702bd4a7d7])].getD (i % 8) 0))) else (if i < 608 then (if i < 592 then (if i < 584 then [(limbWord [0x7,0x3b4b4f863695e7d7]),(limbWord [0x6,0x969f0c74abcfa6d7]),(limbWord [0x7,0x4f4b4f93b815e7d7]),0x34b4f86380d6536,(limbWord [0x7,0x23694f863815e7d7]),(limbWord [0x7,0x4f4b4f863815e7d7]),(limbWord [0x6,0x969f0c702bd2a7d7]),0x34b0c702bcfa266].getD (i % 8) 0 else [(limbWord [0x6,0x971f4f863815e767]),(limbWord [0x7,0x474b4f863815e7d7]),(limbWord [0x6,0x969f28863815e7d7]),(limbWord [0x6,0x969f0c592bcfa1e7]),(limbWord [0x6,0x969f0c702bcfa107]),(limbWord [0x6,0x969f0c702bd007d7]),(limbWord [0x6,0xee9f0c702bcfa777]),(limbWord [0x6,0x969f0c7eb815e7d7])].getD (i % 8) 0) else (if i < 600 then [(limbWord [0x5,0x3e490c703115e7d7]),(limbWord [0x6,0x969f0c702bcfa4a7]),(limbWord [0x7,0x634b4f863815e7d7]),(limbWord [0x7,0x234b4f863815e7d7]),0x3694f862bcfa506,(limbWord [0x6,0x96e94f863815e7d7]),(limbWord [0x7,0x5f4b81862bd187d7]),(limbWord [0x5,0x3e490c7fb815e7d7])].getD (i % 8) 0 else [(limbWord [0x7,0x829f0c702bd407d7]),(limbWord [0x6,0x969f4486381907d7]),(limbWord [0x7,0x5f030c702bd407d7]),(limbWord [0x7,0x574b4f863814e7d7]),(limbWord [0x6,0x971f65a23815e7d7]),(limbWord [0x6,0xa74b4f863815e7d7]),(limbWord [0x6,0x97074f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa1a7])].getD (i % 8) 0)) else (if i < 624 then (if i < 616 then [(limbWord [0x6,0x96cb4f863695e7d7]),(limbWord [0x6,0x969f0c702bcfa187]),(limbWord [0x7,0xb6b4f863815e7d7]),(limbWord [0x6,0xd29f0c702bd187d7]),(limbWord [0x6,0x969f0c702bcfa5d7]),(limbWord [0x6,0x969f0c702bcfa427]),(limbWord [0x6,0x969f0c702dd6aaf7]),(limbWord [0x6,0x971f4f863c15e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f2786381a27d7]),(limbWord [0x7,0x3b8da5a7d115e7d7]),(limbWord [0x6,0x969f0c702bcfa5c7]),(limbWord [0x6,0x969f27702bcfa6c7]),(limbWord [0x6,0x969f0c75b815e7d7]),(limbWord [0x6,0x969f0c702f95e7d7]),(limbWord [0x6,0xe74b4f93b815e7d7]),(limbWord [0x6,0x969f0c702bcfa307])].getD (i % 8) 0) else (if i < 632 then [(limbWord [0x6,0x969f0c733815e7d7]),0x3694f702bcfa3c6,(limbWord [0x6,0x969f0c702bcfa1f7]),(limbWord [0x6,0x969f0c702bcfa4f7]),(limbWord [0x6,0x969f0c702bcfa317]),(limbWord [0x7,0x3f4b4f863815e7d7]),(limbWord [0x7,0x734b68863815e7d7]),(limbWord [0x6,0xef4b4f86381a27d7])].getD (i % 8) 0 else [(limbWord [0x7,0x4b4b8fa7b815e7d7]),(limbWord [0x6,0x971f4f86381867d7]),(limbWord [0x6,0x96d10c702bcfa1e7]),(limbWord [0x6,0x970d4fa24315e7d7]),0x3690c702bcfa2f6,(limbWord [0x6,0x969f24863695e7d7]),(limbWord [0x7,0x3b734f86381a2af7]),(limbWord [0x7,0x834b81863815e7d7])].getD (i % 8) 0))))

def stateWordDataBlock5 (i : Nat) : Nat := (if i < 704 then (if i < 672 then (if i < 656 then (if i < 648 then [(limbWord [0x6,0x97454f9fb815e7d7]),(limbWord [0x6,0x969f0c702bcfa157]),(limbWord [0x6,0x969f37863818eaf7]),(limbWord [0x6,0x969f0c702bcfa3a7]),(limbWord [0x7,0x67694f863815e7d7]),(limbWord [0x6,0x970b4f863815e7d7]),0x29f0c592bcfa1e6,0x29f0c702bcfa106].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c7031d5e6b7]),(limbWord [0x6,0x969f0f863815e7d7]),(limbWord [0x6,0x96b14f863815e7d7]),(limbWord [0x6,0x969f0c702bd1e7d7]),(limbWord [0x6,0x971f7d863815e7d7]),(limbWord [0x6,0x969f0c702bcfa527]),(limbWord [0x6,0x969f0c702bd4c7d7]),(limbWord [0x7,0x1b4b81b9c315e7d7])].getD (i % 8) 0) else (if i < 664 then [0x34b27702bcfa2f6,0x34b4f93b815e6b6,0x34b4f8638194af6,(limbWord [0x6,0x969f0c702a5187d7]),(limbWord [0x6,0x96d10c702bcfa777]),(limbWord [0x6,0xef4b4fa24315e7d7]),(limbWord [0x6,0x97034f864055e7d7]),(limbWord [0x6,0x969f44913815e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f1c863815e7d7]),(limbWord [0x7,0x5e9f2f863815e7d7]),(limbWord [0x6,0x96a54f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa587]),(limbWord [0x6,0x969f0c702bcfa637]),(limbWord [0x7,0x5f738f863815e7d7]),(limbWord [0x7,0x674b4f863815e7d7]),(limbWord [0x7,0x33854f863815e7d7])].getD (i % 8) 0)) else (if i < 688 then (if i < 680 then [(limbWord [0x6,0x97034f862bd467d7]),(limbWord [0x7,0x1b4b4f863814e7d7]),(limbWord [0x6,0x969f0c702bcfa247]),(limbWord [0x5,0x3e6d24863815e7d7]),(limbWord [0x6,0x969f0c702bd107d7]),(limbWord [0x6,0x969f0c702bcfa5b7]),(limbWord [0x6,0x969f1b863815e7d7]),(limbWord [0x6,0x969f0c702bd327d7])].getD (i % 8) 0 else [(limbWord [0x5,0x3e18e06babd447d7]),0x39dc6a7d115e7d6,(limbWord [0x6,0x969f11863815e7d7]),(limbWord [0x6,0x969f448cb815e7d7]),(limbWord [0x6,0x4ecb4f863815e7d7]),(limbWord [0x7,0x5f774f863815e7d7]),(limbWord [0x6,0x971f4fa4b815e7d7]),(limbWord [0x6,0x969f0c702dd5ea07])].getD (i % 8) 0) else (if i < 696 then [0x3774f86381a27d6,0x2d10c702bcfa1e6,(limbWord [0x6,0x97034f862dd5e7d7]),(limbWord [0x5,0x3e890c703115e7d7]),(limbWord [0x6,0x97036f863815e7d7]),(limbWord [0x7,0x834b4f863815e7c7]),(limbWord [0x6,0x969f0c703095e7d7]),(limbWord [0x7,0x834b4fa23815e7d7])].getD (i % 8) 0 else [0x29f0c701f4a61e6,(limbWord [0x5,0x3e890c7fb815e7d7]),(limbWord [0x6,0x969f0c70230fa5e7]),(limbWord [0x7,0x1b8581a7c315e7d7]),(limbWord [0x6,0x969f0c7d3815e7d7]),(limbWord [0x6,0x969f0c702bd5a7d7]),(limbWord [0x7,0x5f4b4f862c95e7d7]),(limbWord [0x6,0xd29f0c702bcfa1e7])].getD (i % 8) 0))) else (if i < 736 then (if i < 720 then (if i < 712 then [(limbWord [0x6,0x96fb0c702bcfa6c7]),(limbWord [0x6,0x969f3f702bcfa6b7]),(limbWord [0x7,0x1b4b4fa24d15e7d7]),(limbWord [0x7,0x1a9f22863815e7d7]),0x3774fa24315e7d6,0x3774f86380fa536,(limbWord [0x6,0xe69f3f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa0c7])].getD (i % 8) 0 else [(limbWord [0x6,0x4e9f24863815e7d7]),(limbWord [0x6,0x969f0c702bcfa067]),0x34b4f702bcfa336,(limbWord [0x6,0x969f27702bcfa1e7]),(limbWord [0x6,0x969f0c702bd3a7d7]),(limbWord [0x7,0x171f4f863815e7d7]),(limbWord [0x6,0x969f0c702bd2c7d7]),(limbWord [0x7,0x734b4f863815e7d7])].getD (i % 8) 0) else (if i < 728 then [0x34b7d702bcfa3c6,(limbWord [0x6,0x969f0c702bd0a7d7]),(limbWord [0x6,0x969f0c702bcfa207]),(limbWord [0x6,0x969f0c7b3815e7d7]),(limbWord [0x6,0x974144863815e7d7]),(limbWord [0x6,0x96f74f863815e7d7]),(limbWord [0x6,0x969f25863815e7d7]),(limbWord [0x6,0x969f479fb815e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c7cb815e7d7]),0x34b7d863815e6b6,(limbWord [0x6,0x969f0c703255e7d7]),(limbWord [0x6,0xe31f4f863815e7d7]),(limbWord [0x6,0xfb4b4f863815e7d7]),(limbWord [0x7,0x3b4b4fa22bd187d7]),(limbWord [0x6,0x969f27702bcfa777]),(limbWord [0x7,0x3a9f44702bd407d7])].getD (i % 8) 0)) else (if i < 752 then (if i < 744 then [(limbWord [0x6,0x97034f863d15e7d7]),(limbWord [0x6,0xcb4b4f863815e7d7]),(limbWord [0x7,0x5fa54f863815e7d7]),(limbWord [0x6,0xbb4b4f863815e7d7]),(limbWord [0x6,0x8f374f863815e7d7]),(limbWord [0x6,0x969f3f702bcfa337]),(limbWord [0x6,0xf29f0c7bb815e7d7]),(limbWord [0x7,0x5e9f0c702bd447d7])].getD (i % 8) 0 else [(limbWord [0x6,0xd29f0c7035d5e7d7]),(limbWord [0x6,0x969f0c702bcfa007]),(limbWord [0x7,0x838d4f863815e7d7]),(limbWord [0x7,0x5f4b68863815e7d7]),(limbWord [0x6,0x969f0c703295ea37]),(limbWord [0x6,0x96c54f863815e7d7]),(limbWord [0x7,0x5f8d81863815e7d7]),(limbWord [0x6,0x971f4f863818eaf7])].getD (i % 8) 0) else (if i < 760 then [(limbWord [0x6,0x96fb0c702bd327d7]),(limbWord [0x6,0x97034f863dda2af7]),0x34b6886381a27d6,(limbWord [0x7,0xb4b4f86380fa5e7]),(limbWord [0x6,0x971f4f702bd287d7]),(limbWord [0x6,0x969f12863815e7d7]),(limbWord [0x6,0xd3034f863815e7d7]),(limbWord [0x7,0x5f4b5d863815e7d7])].getD (i % 8) 0 else [(limbWord [0x7,0x1b034f862bcfa777]),(limbWord [0x6,0x969f3f702bd267d7]),(limbWord [0x7,0x3b774f863815e7d7]),0x3737d863815e7d6,(limbWord [0x7,0x1f4b4f863815e7d7]),(limbWord [0x7,0x5f6b4f863815e7d7]),(limbWord [0x7,0x1a9f449dc315e7d7]),(limbWord [0x5,0x3e18f7703115e7d7])].getD (i % 8) 0))))

def stateWordDataBlock6 (i : Nat) : Nat := (if i < 832 then (if i < 800 then (if i < 784 then (if i < 776 then [0x29f0c702bcfa0c6,(limbWord [0x6,0x969f3e863815e7d7]),(limbWord [0x6,0x969f0c702bcfa137]),(limbWord [0x7,0x5f4b4f86381a07d7]),0x29f27702bcfa1e6,0x34b68a24315e7d6,(limbWord [0x6,0x969f0c702bcfa4d7]),(limbWord [0x5,0x3e18ff7bb815e7d7])].getD (i % 8) 0 else [(limbWord [0x7,0xf774f863815e7d7]),0x34b6886380fa536,(limbWord [0x6,0x969f0c70281347d7]),(limbWord [0x6,0x969f0c702bcfa0a7]),(limbWord [0x7,0x3b4b4f862c95e7d7]),(limbWord [0x6,0xd29f0c702bd447d7]),(limbWord [0x6,0x969f0c702bcfa3d7]),(limbWord [0x6,0x969f0c702bcfa277])].getD (i % 8) 0) else (if i < 792 then [(limbWord [0x6,0x969f0c702dd5e6b7]),(limbWord [0x6,0x96e14f863815e7d7]),(limbWord [0x7,0x6f9d4f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa407]),(limbWord [0x7,0x334b4fa24315e7d7]),(limbWord [0x6,0x97334f863815e7d7]),(limbWord [0x7,0x569f3b863815e7d7]),(limbWord [0x6,0xee9f0c702bcfa787])].getD (i % 8) 0 else [(limbWord [0x6,0x97034f863815e767]),(limbWord [0x6,0xeecb4f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa1b7]),(limbWord [0x6,0x97034f86381567d7]),(limbWord [0x6,0x971f86863815e7d7]),(limbWord [0x6,0x969f0c702bcfa167]),(limbWord [0x6,0x971f4f863813c7d7]),(limbWord [0x6,0x969f0c702bd447d7])].getD (i % 8) 0)) else (if i < 816 then (if i < 808 then [0x34aaf3e940782f6,0x34b4f8631d5e506,(limbWord [0x6,0x969f4c863815e7d7]),0x34b4f579aca03c6,(limbWord [0x6,0x969f3c863815e7d7]),(limbWord [0x6,0x971f4f702bd247d7]),0x34b0c579aca02f6,(limbWord [0x6,0xd29f0c702bcfa507])].getD (i % 8) 0 else [(limbWord [0x7,0x7af14f863815e7d7]),(limbWord [0x7,0x34b4f863815e7d7]),(limbWord [0x6,0x969f0c7031d5e6c7]),(limbWord [0x6,0x969f0c70345287d7]),(limbWord [0x6,0x96fb0c703455e7d7]),(limbWord [0x6,0x96cb4f862c95e7d7]),(limbWord [0x6,0x969f0c702bcfa657]),(limbWord [0x7,0x1b0378a7c315e7d7])].getD (i % 8) 0) else (if i < 824 then [(limbWord [0x6,0x969f0c703315e7d7]),(limbWord [0x6,0x971f4f9fb815e7d7]),(limbWord [0x6,0x969f0c7031d5e8c7]),(limbWord [0x6,0x969f17863815e7d7]),(limbWord [0x7,0x5f994f863815e7d7]),(limbWord [0x6,0x969f44863a55e7d7]),(limbWord [0x6,0x969f0c702bd547d7]),(limbWord [0x7,0x5f694f863815e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c702bcfa6a7]),(limbWord [0x6,0xee9f24863815e7d7]),(limbWord [0x7,0x7b4b4fa24315e7d7]),(limbWord [0x7,0x3a9f0c702bd447d7]),(limbWord [0x7,0x3a9f449db815e7d7]),(limbWord [0x6,0x971f4f8d3815e7d7]),(limbWord [0x7,0x3b4b68863815e7d7]),(limbWord [0x6,0x969f0c702bcfa687])].getD (i % 8) 0))) else (if i < 864 then (if i < 848 then (if i < 840 then [0x29f0c702bcfa136,0x34b4f7031d5e3c6,(limbWord [0x6,0x969f0c702bcfa367]),(limbWord [0x7,0x5f4b4f93b815e7d7]),(limbWord [0x6,0x96fb0c702bcfa537]),0x34b0c7031d5e2f6,0x34b4f93b81a27d6,0x34ae0579ac782f6].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c702d95e7d7]),(limbWord [0x6,0xc69f0c702bcfa777]),(limbWord [0x7,0x6f4b8f863815e7d7]),(limbWord [0x6,0x969f24862c95e7d7]),(limbWord [0x7,0x3b6b4f863815e7d7]),0x34b4f863815e526,(limbWord [0x6,0x97254f863815e7d7]),(limbWord [0x6,0x969f0c702fd5e7d7])].getD (i % 8) 0) else (if i < 856 then [(limbWord [0x6,0x973d81a7b815e7d7]),(limbWord [0x7,0x574b81a7c315e7d7]),0x34b4f862bcfa456,0x3694f86380fa536,(limbWord [0x7,0x334b4f86381a2af7]),(limbWord [0x6,0x971f81863dd5e7d7]),(limbWord [0x6,0x969f0c702bcfa2c7]),(limbWord [0x6,0x969f0c702bcfa0d7])].getD (i % 8) 0 else [(limbWord [0x6,0xeb4b4f863815e7d7]),0x29f0c702bcfa166,(limbWord [0x6,0x96c34f863815e7d7]),(limbWord [0x6,0x969f0c803815e7d7]),(limbWord [0x6,0x6e9f44863815e7d7]),(limbWord [0x6,0x969f0c702bd567d7]),(limbWord [0x6,0x969f23863815e7d7]),(limbWord [0x6,0x96d165863815e7d7])].getD (i % 8) 0)) else (if i < 880 then (if i < 872 then [(limbWord [0x6,0x969f27702bcfa357]),(limbWord [0x5,0x3e18ff702bcfa6b7]),(limbWord [0x7,0x5f4b4f86381567d7]),0x34b4f93b80fa536,(limbWord [0x6,0xc69f0c7035d5e7d7]),(limbWord [0x6,0x969f0c702bcfa357]),(limbWord [0x7,0x83734f863815e7d7]),0x34b0c702bcfa286].getD (i % 8) 0 else [(limbWord [0x7,0x5f7381863815e7d7]),(limbWord [0x7,0x334b4f863815e7d7]),(limbWord [0x6,0x969f248634d5e7d7]),(limbWord [0x6,0x969f0c702bd0e7d7]),(limbWord [0x6,0x971f4f86381907d7]),(limbWord [0x6,0x969f0e863815e7d7]),0x38d4f86381907d6,(limbWord [0x6,0x97234f863815e7d7])].getD (i % 8) 0) else (if i < 888 then [(limbWord [0x6,0x969f3f702bcfa6c7]),(limbWord [0x6,0x97214f863815e7d7]),(limbWord [0x7,0x3b4b81a7d115e7d7]),(limbWord [0x6,0x97034f863b15e7d7]),(limbWord [0x7,0x3a9f0c702bd527d7]),(limbWord [0x7,0x874b4f863815e7d7]),0x34b5b863815e6b6,(limbWord [0x7,0x5e9f0c7031d5e7d7])].getD (i % 8) 0 else [0x34b81a7c316eaf6,(limbWord [0x6,0x96d124863815e7d7]),(limbWord [0x7,0x3b8d4fa23815e7d7]),(limbWord [0x6,0xee9f0c702bd467d7]),(limbWord [0x6,0x971f4f863816eaf7]),(limbWord [0x7,0x3b994f863815e7d7]),(limbWord [0x6,0x969f0c6d2bcfa6b7]),(limbWord [0x7,0x3b694f863815e7d7])].getD (i % 8) 0))))

def stateWordDataBlock7 (i : Nat) : Nat := (if i < 960 then (if i < 928 then (if i < 912 then (if i < 904 then [(limbWord [0x6,0x969f0c702bcfa267]),(limbWord [0x6,0xab4b4f863815e7d7]),(limbWord [0x5,0x3e18e057a8cfa777]),(limbWord [0x6,0x969f0c702bd0c7d7]),0x34b3f702bcfa2f6,(limbWord [0x6,0x969f0c813815e7d7]),0x34b4f9fb815e6b6,(limbWord [0x7,0x3b1f8ba7b815e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x96c74f863815e7d7]),(limbWord [0x6,0x969f2a863815e7d7]),(limbWord [0x6,0x96d54f863815e7d7]),(limbWord [0x6,0x969f27702bd287d7]),(limbWord [0x7,0x3b4b4f93b815e7d7]),(limbWord [0x6,0x969f0c702bcfa0f7]),(limbWord [0x7,0x3b4b4f863819a7d7]),(limbWord [0x6,0x971f4fa23dd5e7d7])].getD (i % 8) 0) else (if i < 920 then [(limbWord [0x6,0x969f0c702bcfa3e7]),(limbWord [0x6,0x969f0c7db815e7d7]),0x34b4f86320fa506,(limbWord [0x6,0x969f0c702bd207d7]),(limbWord [0x6,0x971f4f863815e7c7]),0x34b4f862c0fa506,(limbWord [0x6,0x969f0c702bcfa547]),(limbWord [0x6,0x969f0c702bcfa387])].getD (i % 8) 0 else [(limbWord [0x6,0xf74b4f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa097]),(limbWord [0x6,0x97034f86345187d7]),(limbWord [0x6,0x96e75d863815e7d7]),(limbWord [0x6,0x96e94f863816eaf7]),(limbWord [0x6,0x969f3593b815e7d7]),(limbWord [0x6,0x971f4f913815e7d7]),0x29eaf3e940781e6].getD (i % 8) 0)) else (if i < 944 then (if i < 936 then [(limbWord [0x7,0x7b4b4f86381567d7]),(limbWord [0x6,0x969f35863815e7d7]),(limbWord [0x7,0x7b9d4f863815e7d7]),0x3734f9fb815e7d6,(limbWord [0x7,0xf4b4f863815e7d7]),(limbWord [0x7,0x3b8d81a7c315e7d7]),0x218af3e9405e1e6,(limbWord [0x6,0x97094f863815e7d7])].getD (i % 8) 0 else [0x29f0c579aca01e6,(limbWord [0x7,0x5f634f863815e7d7]),(limbWord [0x6,0x969f0c70b815e7d7]),(limbWord [0x6,0x971f0c702bd527d7]),(limbWord [0x6,0x969f0c702bcfa1d7]),(limbWord [0x6,0x971f4f8b3815e7d7]),(limbWord [0x6,0x96af4f863815e7d7]),(limbWord [0x6,0x96cb4f93b815e7d7])].getD (i % 8) 0) else (if i < 952 then [(limbWord [0x6,0x969f0c70345467d7]),0x34b7d86380fa536,0x34b4f70320fa3c6,(limbWord [0x6,0x973168863815e7d7]),(limbWord [0x6,0x969f0c7bb81a28f7]),(limbWord [0x6,0x971f4f8cb815e7d7]),(limbWord [0x6,0x969f0c702dd5e6c7]),(limbWord [0x6,0x969f0c76b815e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c702ed5e7d7]),(limbWord [0x6,0xe74b4f863816eaf7]),(limbWord [0x6,0x969f0c7e3815e7d7]),(limbWord [0x6,0x96d34f863815e7d7]),(limbWord [0x6,0x96fb0c702bcfa727]),0x34b0c70320fa2f6,(limbWord [0x6,0x969f0c702bcfa027]),(limbWord [0x6,0x969f44864055e7d7])].getD (i % 8) 0))) else (if i < 992 then (if i < 976 then (if i < 968 then [(limbWord [0x6,0x97034f863818eaf7]),(limbWord [0x6,0x3e9f0c703115e7d7]),(limbWord [0x7,0x3a9f0c7031d5e7d7]),0x1c0af3e8f05e1e6,(limbWord [0x6,0x97474f863dd5e7d7]),0x29ee0579ac781e6,(limbWord [0x6,0x971f64863815e7d7]),(limbWord [0x6,0x969f44862bd467d7])].getD (i % 8) 0 else [(limbWord [0x5,0xd6cb4f863815e7d7]),0x34b4f86381567d6,(limbWord [0x6,0x97034fa24d15e7d7]),(limbWord [0x6,0xe74b4f8636d5e7d7]),(limbWord [0x6,0x3e9f0c7fb815e7d7]),(limbWord [0x6,0x969f0c79b815e7d7]),0x34b4f702dd5e3c6,(limbWord [0x6,0x969f0c702bcfa467])].getD (i % 8) 0) else (if i < 984 then [(limbWord [0x6,0x969f0c702dd5e8f7]),(limbWord [0x6,0x969f0c702bd027d7]),(limbWord [0x6,0x969f0c702dd5e527]),(limbWord [0x6,0x969f27923815e7d7]),0x218e0579ac5e1e6,(limbWord [0x6,0x96a74f863815e7d7]),(limbWord [0x6,0x97054f863815e7d7]),0x34b0c702dd5e2f6].getD (i % 8) 0 else [(limbWord [0x6,0x96fb0c702bcfa267]),(limbWord [0x6,0x969f3f703455e7d7]),(limbWord [0x6,0x97134f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa4c7]),(limbWord [0x6,0x969f0c702bd047d7]),(limbWord [0x6,0x96b54f863815e7d7]),(limbWord [0x6,0x969f0c7031d5ea27]),(limbWord [0x6,0x969f2e863815e7d7])].getD (i % 8) 0)) else (if i < 1008 then (if i < 1000 then [(limbWord [0x6,0x969f14863815e7d7]),(limbWord [0x6,0x969f0c702bd4e7d7]),(limbWord [0x6,0x969f0c823815e7d7]),(limbWord [0x7,0x7b4b8f863815e7d7]),(limbWord [0x6,0x97474f863815e767]),(limbWord [0x6,0xee9f0c702bd407d7]),(limbWord [0x6,0x97117d863815e7d7]),(limbWord [0x6,0xc34b4f863815e7d7])].getD (i % 8) 0 else [(limbWord [0x7,0x1b4b8fc0c315e7d7]),(limbWord [0x7,0x5e9f0c80b815e7d7]),(limbWord [0x6,0x969f0c702bcfa557]),(limbWord [0x6,0x969f0c81b815e7d7]),(limbWord [0x6,0x96d74f863815e7d7]),(limbWord [0x6,0x969f44862dd5e7d7]),0x34b8fc0d115e7d6,(limbWord [0xd2d,0x3e490c702bd247d8])].getD (i % 8) 0) else (if i < 1016 then [(limbWord [0x7,0x1b4b0c702bcfa2f7]),(limbWord [0x6,0x969f4486380fa537]),(limbWord [0x7,0x1b4b4f863815e6b7]),(limbWord [0xd2d,0x969f34863815e7d8]),(limbWord [0xd2d,0x969f0c83b815e7d8]),(limbWord [0x6,0x96b34f863815e7d7]),(limbWord [0xd2e,0x3e9f0c702bd387d8]),(limbWord [0xd2d,0x3e18e0579f4d61e8])].getD (i % 8) 0 else [(limbWord [0x6,0x971f4f862bcfa507]),(limbWord [0x6,0x969f0c702bd167d7]),(limbWord [0xf07,0x5f4b4f863815e7d8]),(limbWord [0x6,0x969f1686380fa537]),(limbWord [0x6,0x97034f862bd187d7]),(limbWord [0xd2d,0x3e18e057a80fa508]),0x34b7d863815e7d6,(limbWord [0xd2e,0x3e9f0c702bcfa6c8])].getD (i % 8) 0))))

def stateWordDataBlock8 (i : Nat) : Nat := (if i < 1088 then (if i < 1056 then (if i < 1040 then (if i < 1032 then [(limbWord [0xdce,0x971f4f863815e7d8]),(limbWord [0xebe,0x969f0c702bcfa048]),(limbWord [0xd2d,0x3e18e057a80fa6d8]),(limbWord [0x6,0x971f65863815e7d7]),(limbWord [0xe37,0xb4b4f863815e7d8]),(limbWord [0xd2e,0x3e9f0c702bd187d8]),(limbWord [0xd2d,0xce9f24863815e7d8]),(limbWord [0xd2d,0x3e490c83b815e7d8])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c80b815e7d7]),(limbWord [0x6,0x969f0c702bd467d7]),(limbWord [0xd2d,0x3e890c702bd287d8]),(limbWord [0x6,0x969f0c702bcfa2a7]),(limbWord [0xd2d,0x3e18e0579f4d6538]),(limbWord [0xebe,0x969f0c7bb815e7d8]),(limbWord [0xd2d,0x969f0c702bcfa2a8]),(limbWord [0xe36,0x969f0c702bcfa798])].getD (i % 8) 0) else (if i < 1048 then [(limbWord [0x6,0x971f4f863815e6b7]),(limbWord [0xd2d,0x3e930c7bb815e7d8]),(limbWord [0xd2d,0x3e18e06babcfa6b8]),(limbWord [0xe76,0x969f0c702bcfa088]),(limbWord [0x6,0x969f0c70280fa537]),(limbWord [0xd2e,0x69f0c702bcfa6b8]),(limbWord [0x5,0x3e18e0579f4d61e7]),(limbWord [0x6,0x969f0c579f4d8507])].getD (i % 8) 0 else [(limbWord [0x6,0x969f44863dd5e7d7]),(limbWord [0x6,0x969f0c702bcfa0b7]),(limbWord [0x6,0x969f0c702dd5e7d7]),(limbWord [0x6,0xe74b4f862bcfa507]),(limbWord [0x6,0x969f0c7bb80fa537]),(limbWord [0xe66,0x969f0c7bb815e7d8]),(limbWord [0xd2e,0x69f0c702bd347d8]),(limbWord [0xe76,0x969f0c702bcfa7a8])].getD (i % 8) 0)) else (if i < 1072 then (if i < 1064 then [(limbWord [0xe36,0x969f0c703455e7d8]),(limbWord [0xd2d,0x969f44863815e7d8]),(limbWord [0x6,0x969f22863815e7d7]),(limbWord [0xe16,0x971f4f863815e7d8]),(limbWord [0x7,0x1b854f863815e7d7]),(limbWord [0xd2d,0x3e18e057a30fa6c8]),(limbWord [0xd2e,0x2b034f863815e7d8]),(limbWord [0x6,0x969f0c702bcfa087])].getD (i % 8) 0 else [(limbWord [0xdce,0x969f0c702bd187d8]),0x34b4f579f4a03c6,(limbWord [0x7,0x5e9f0c702bd407d7]),(limbWord [0x6,0x969f0c702bcfa447]),(limbWord [0xf07,0x3b4b4f863815e7d8]),0x34b0c579f4a02f6,(limbWord [0x6,0x969f16863815e7d7]),(limbWord [0xd2e,0x8e9f44863815e7d8])].getD (i % 8) 0) else (if i < 1080 then [0x34b4f862bcd6506,(limbWord [0xe36,0x969f0c702bcfa538]),(limbWord [0x6,0x969ee0579f4d83c7]),(limbWord [0x6,0xe74b4f702bcfa3c7]),(limbWord [0x6,0x969ee057a30fa3c7]),(limbWord [0x6,0x969f19863815e7d7]),(limbWord [0x6,0x9618e0579f4d82f7]),(limbWord [0x6,0xe74b0c702bcfa2f7])].getD (i % 8) 0 else [(limbWord [0xebe,0x969f0c703795e7d8]),(limbWord [0x6,0xe74b4f863815e6b7]),(limbWord [0x6,0x9618e057a30fa2f7]),(limbWord [0x6,0x969f0c702bd186b7]),(limbWord [0xd2d,0x3e18e0579f4d6508]),(limbWord [0xe76,0x969f0c703715e7d8]),(limbWord [0xe36,0x97034f863815e7d8]),(limbWord [0xd2e,0x3e9f0c702bcfa1e8])].getD (i % 8) 0))) else (if i < 1120 then (if i < 1104 then (if i < 1096 then [(limbWord [0xe76,0x969f0c7bb815e7d8]),(limbWord [0x7,0x1a9f0c702bcfa1e7]),(limbWord [0x7,0x834b4f863815e7d7]),(limbWord [0x6,0x969f0c7a3815e7d7]),(limbWord [0x7,0x5f4b81863815e7d7]),0x34ae0579f4782f6,0x34b4f863818eaf6,(limbWord [0xebe,0x969f0c702bcfa6b8])].getD (i % 8) 0 else [(limbWord [0x7,0xb4b4f862bcfa507]),0x34b4f702bcd63c6,(limbWord [0xd2e,0x3e9f0c703455e7d8]),(limbWord [0x6,0x969f0c702bcfa047]),(limbWord [0xd2d,0xdecb4f863815e7d8]),(limbWord [0xd2d,0xce9f44863815e7d8]),(limbWord [0x6,0x969f0c7bb81a2af7]),(limbWord [0xd2d,0x3e890c83b815e7d8])].getD (i % 8) 0) else (if i < 1112 then [0x34b0c702bcd62f6,(limbWord [0xd2e,0x3e9f0c702bcfa778]),(limbWord [0xd2d,0x969f0c702bd407d8]),(limbWord [0xe16,0xe74b4f863815e7d8]),(limbWord [0x7,0x1a9f0c702bcfa777]),(limbWord [0x6,0x969f0c7bb815e7d7]),(limbWord [0xd2d,0x969f0c7bb815e7d8]),(limbWord [0xd2e,0x3e9f0c702bcfa538])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c701f4d6537]),(limbWord [0x7,0xb4b4f702bcfa3c7]),(limbWord [0xd2e,0x3e9f0c7035d5e7d8]),(limbWord [0x7,0x3a9f0c702bd407d7]),(limbWord [0x7,0xb4b0c702bcfa2f7]),(limbWord [0x6,0x969f0c579f4a01e7]),(limbWord [0x7,0xb4b4f863815e6b7]),(limbWord [0xd2d,0x3e490c702bd407d8])].getD (i % 8) 0)) else (if i < 1136 then (if i < 1128 then [(limbWord [0xe6f,0x1b4b4f863815e7d8]),(limbWord [0x6,0x96d14f863815e7d7]),(limbWord [0xd2e,0x571f4f863815e7d8]),(limbWord [0x6,0x3e9f0c702bcfa1e7]),(limbWord [0xd2e,0x69f0c702bcfa738]),(limbWord [0x6,0x969f0c68abcfa507]),(limbWord [0x6,0x96bb4f863815e7d7]),(limbWord [0xd2d,0x3e18e0579f4d81e8])].getD (i % 8) 0 else [(limbWord [0xd2e,0x3e9f0c703595e7d8]),(limbWord [0x6,0x96df4f863815e7d7]),(limbWord [0xebf,0x1b4b4f863815e7d8]),(limbWord [0xd2d,0x3e490c7bb815e7d8]),(limbWord [0xd2d,0x3e18e057a30fa1e8]),(limbWord [0x6,0x969f0c579f4ee507]),(limbWord [0x5,0x3e18e0579f43c127]),0x34b4f9fb815e7d6].getD (i % 8) 0) else (if i < 1144 then [(limbWord [0x6,0x969f0c579f4a0437]),(limbWord [0xdce,0x969f0c703455e7d8]),(limbWord [0x6,0x969ee0579f4781e7]),(limbWord [0x7,0xb734f863815e7d7]),(limbWord [0xeaf,0x3b4b4f863815e7d8]),(limbWord [0x6,0x969f0c579f4a6507]),(limbWord [0xd2d,0x3e18e057a30fa778]),(limbWord [0xe76,0x969f0c702bcfa6b8])].getD (i % 8) 0 else [(limbWord [0x6,0x9618e0579f45e1e7]),(limbWord [0xd2d,0x3e690c7bb815e7d8]),(limbWord [0x6,0x969ee068abcfa3c7]),(limbWord [0x6,0x969f0c702bcd61e7]),(limbWord [0x7,0x1b4b4fa24315e7d7]),(limbWord [0x7,0x1b4b4f86380fa537]),(limbWord [0xe67,0x1b4b4f863815e7d8]),(limbWord [0xd2d,0xce9f0c7bb815e7d8])].getD (i % 8) 0))))

def stateWordDataBlock9 (i : Nat) : Nat := (if i < 1216 then (if i < 1184 then (if i < 1168 then (if i < 1160 then [(limbWord [0xd2d,0x3e19077bb815e7d8]),(limbWord [0xdce,0x969f0c702bcfa538]),(limbWord [0x6,0x9618e068abcfa2f7]),(limbWord [0xede,0xe74b4f863815e7d8]),(limbWord [0x6,0x969ee0579f4ee3c7]),(limbWord [0x6,0x969f0c703455e6b7]),(limbWord [0x6,0x97034f862bcfa507]),(limbWord [0xd2d,0x3e18e06babcfa6c8])].getD (i % 8) 0 else [0x29f0c579f4a01e6,(limbWord [0xd2e,0x3e9f0c702bcfa508]),(limbWord [0x6,0x9618e0579f4ee2f7]),(limbWord [0x7,0x574b4f863815e7d7]),(limbWord [0xd2e,0x3e9f0c702bcfa6d8]),(limbWord [0xd2e,0x69f0c702bcfa6c8]),(limbWord [0x6,0x969ee0579f4a63c7]),(limbWord [0xdce,0x97034f863815e7d8])].getD (i % 8) 0) else (if i < 1176 then [(limbWord [0x6,0x969f0c702bcfa3f7]),(limbWord [0x5,0x3e18e0579f4d81e7]),(limbWord [0x6,0xe69f0c702bcfa1e7]),(limbWord [0x7,0x5f8d4f863815e7d7]),(limbWord [0x5,0x3e18e057a30fa1e7]),(limbWord [0x6,0x9618e0579f4a62f7]),(limbWord [0x6,0x969f0c702bcd6537]),(limbWord [0x6,0x969ee06babcfa3c7])].getD (i % 8) 0 else [0x34b4f86381907d6,(limbWord [0x6,0x969f0c702bd347d7]),(limbWord [0xef7,0x1b4b4f863815e7d8]),(limbWord [0x6,0x97034f702bcfa3c7]),(limbWord [0x6,0x9618e06babcfa2f7]),(limbWord [0xe96,0xe74b4f863815e7d8]),(limbWord [0x6,0x969f0c7035d5e6b7]),0x29ee0579f4781e6].getD (i % 8) 0)) else (if i < 1200 then (if i < 1192 then [(limbWord [0xdce,0x969f0c702bd447d8]),(limbWord [0x6,0x969f0c702bcfa227]),(limbWord [0xe77,0x1b4b4f863815e7d8]),(limbWord [0x6,0x97034f863815e6b7]),0x218e0579f45e1e6,0x29f0c702bcd61e6,(limbWord [0x6,0x971f4f86380fa537]),(limbWord [0x7,0x3b4b4fa23815e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c763815e7d7]),0x34b4f863816eaf6,(limbWord [0x6,0x969f0c793815e7d7]),(limbWord [0xd2d,0x3e890c702bd407d8]),(limbWord [0xd2d,0x96c14f863815e7d8]),(limbWord [0x6,0xe69f0c7035d5e7d7]),(limbWord [0xd2d,0x3e18e0579f4d8508]),(limbWord [0x7,0x5f4b4f862bcfa507])].getD (i % 8) 0) else (if i < 1208 then [(limbWord [0xd2d,0x3e890c7bb815e7d8]),(limbWord [0xdce,0x969f0c702bcfa508]),(limbWord [0xd2d,0x3e18e068abcfa1e8]),(limbWord [0xe16,0x97034f863815e7d8]),(limbWord [0x7,0x1b4b4f863815e7d7]),(limbWord [0xd2d,0x3e690c702bcfa6b8]),(limbWord [0x6,0x970373863815e7d7]),(limbWord [0xe36,0x96cb4f863815e7d8])].getD (i % 8) 0 else [(limbWord [0x7,0xa9f0c702bcfa1e7]),(limbWord [0x6,0x969f0c579f4a04b7]),(limbWord [0xd2d,0xce9f0c702bcfa6b8]),(limbWord [0xd2d,0x3e1907702bcfa6b8]),(limbWord [0xebe,0x969f0c702bcfa6c8]),(limbWord [0xebe,0xe74b4f863815e7d8]),(limbWord [0xebe,0x969f0c702bd187d8]),(limbWord [0x6,0x969f0c702bcfa0e7])].getD (i % 8) 0))) else (if i < 1248 then (if i < 1232 then (if i < 1224 then [(limbWord [0x6,0x969ee0579f4a03c7]),(limbWord [0xea7,0x3b4b4f863815e7d8]),(limbWord [0x6,0x969f0c70345187d7]),(limbWord [0x6,0x969ee0579f4da3c7]),(limbWord [0xd2d,0x3e18e0579f4a61e8]),0x34b4f861f4a6506,(limbWord [0x6,0x9618e0579f4a02f7]),(limbWord [0x6,0x969f0c702bcd6507])].getD (i % 8) 0 else [(limbWord [0x7,0x5f4b4f702bcfa3c7]),(limbWord [0x7,0x3b8d4f863815e7d7]),(limbWord [0x5,0x3e18e0579f43c117]),(limbWord [0x6,0x9618e0579f4da2f7]),(limbWord [0xd2e,0x1b034f863815e7d8]),(limbWord [0xe36,0x969f24863815e7d8]),(limbWord [0x6,0x969f0c701f4d8537]),(limbWord [0xd2d,0x3e491f863815e7d8])].getD (i % 8) 0) else (if i < 1240 then [(limbWord [0x7,0x5f4b4f863815e6b7]),(limbWord [0x6,0xe74b4f86380fa537]),(limbWord [0xe66,0xe74b4f863815e7d8]),(limbWord [0x6,0x969f44862bd187d7]),(limbWord [0x6,0x969f0c70230fa537]),(limbWord [0xd2e,0x69f0c702bcfa1e8]),(limbWord [0xd2d,0x3e18e0579f4ee538]),(limbWord [0xd2e,0x3e9f0c702bcfa748])].getD (i % 8) 0 else [(limbWord [0xd2d,0x3e18e06bb455e7d8]),(limbWord [0xd2e,0x69f0c702bcfa258]),0x29f0c703115e7d6,(limbWord [0xd2e,0x69f0c703455e7d8]),0x34b4f701f4a63c6,(limbWord [0x6,0x96fb4f863815e7d7]),(limbWord [0x5,0x3e18e068abcfa1e7]),(limbWord [0xe16,0x969f0c702bcfa508])].getD (i % 8) 0)) else (if i < 1264 then (if i < 1256 then [0x29f0c7fb815e7d6,(limbWord [0xe36,0x969f34863815e7d8]),(limbWord [0xe26,0xe74b4f863815e7d8]),(limbWord [0xe16,0x969f0c702bcfa6d8]),(limbWord [0xd2e,0x69f0c702bcfa778]),(limbWord [0xd2d,0x3e18f7702bd407d8]),(limbWord [0xe36,0x96e74f863815e7d8]),0x34b0c701f4a62f6].getD (i % 8) 0 else [(limbWord [0xe36,0x969f0c83b815e7d8]),(limbWord [0x6,0x969f449a3815e7d7]),0x34b4f86380d6536,(limbWord [0xd2d,0x3e18e06babcfa538]),(limbWord [0x7,0x5f734f863815e7d7]),(limbWord [0xebf,0xb4b4f863815e7d8]),(limbWord [0xd2d,0x3e893b863815e7d8]),(limbWord [0x6,0x969f0c702bcfa127])].getD (i % 8) 0) else (if i < 1272 then [(limbWord [0x7,0x3b4b4f862bcfa507]),(limbWord [0xd2e,0x69f0c702bcfa538]),(limbWord [0xeae,0x969f44863815e7d8]),(limbWord [0x5,0x3e18e0579f4a61e7]),(limbWord [0xd2e,0x8f1f4f863815e7d8]),(limbWord [0xe76,0x969f0c702bd4a7d8]),(limbWord [0xd2d,0x3e890c702bcfa6b8]),(limbWord [0xe76,0x969f0c702bcfa6c8])].getD (i % 8) 0 else [(limbWord [0xe76,0xe74b4f863815e7d8]),(limbWord [0xe76,0x969f0c702bd187d8]),0x34b4f863695e7d6,(limbWord [0xd2d,0x3e18e0579f4a01e8]),(limbWord [0x6,0x69f0c702bcfa1e7]),(limbWord [0xd2d,0x3e18e0579f4da1e8]),(limbWord [0x6,0xe74b4f86381a2af7]),(limbWord [0x6,0x969f0c702bd387d7])].getD (i % 8) 0))))

def stateWordDataBlock10 (i : Nat) : Nat := (if i < 1344 then (if i < 1312 then (if i < 1296 then (if i < 1288 then [(limbWord [0xe36,0x969f0c702bd467d8]),0x34b4f862bcfa506,(limbWord [0x6,0x969f0c702bcd65e7]),(limbWord [0xd2d,0x3e18e068abcfa508]),(limbWord [0x6,0x96cb4f862bcfa507]),(limbWord [0x6,0x969f0c702bd4a7d7]),(limbWord [0x7,0x3b4b0c702bcfa2f7]),(limbWord [0x7,0x3b4b4f863815e6b7])].getD (i % 8) 0 else [(limbWord [0xd2e,0x6f14f863815e7d8]),(limbWord [0xd2d,0x3e18e0579f4ee508]),(limbWord [0xebe,0x969f0c703455e7d8]),(limbWord [0x6,0xe74b4f863815e7d7]),(limbWord [0xd2e,0x3e9f0c83b815e7d8]),(limbWord [0x6,0x969f0c702bcfa327]),(limbWord [0xd2d,0x3e890c702bcfa708]),(limbWord [0xdce,0x96cb4f863815e7d8])].getD (i % 8) 0) else (if i < 1304 then [(limbWord [0xd2d,0x969f0c702bd187d8]),(limbWord [0xd2d,0x3e490c703495e7d8]),(limbWord [0xd2d,0x3e18e0579f4a6508]),(limbWord [0xe36,0x969f0c702bcfa0b8]),(limbWord [0x6,0x969f0c701f4a61e7]),(limbWord [0xd2d,0x3e18e0579f4da538]),(limbWord [0xe36,0x969f44863815e7d8]),(limbWord [0x6,0x969f24862bcfa507])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c702bd1e7d7]),(limbWord [0x6,0x96cb4f702bcfa3c7]),(limbWord [0xebe,0x969f0c702bcfa538]),(limbWord [0xedf,0x5f4b4f863815e7d8]),(limbWord [0xd2d,0x969f0c703515e7d8]),(limbWord [0x7,0x3b734f863815e7d7]),(limbWord [0xe77,0xb4b4f863815e7d8]),0x34b4f863815e6b6].getD (i % 8) 0)) else (if i < 1328 then (if i < 1320 then [(limbWord [0xd2d,0x3e18e057a80fa6b8]),(limbWord [0x6,0x96cb4f863815e6b7]),(limbWord [0xd2e,0x6b1f4f863815e7d8]),(limbWord [0xd2e,0x3f174f863815e7d8]),(limbWord [0xdce,0x969f24863815e7d8]),(limbWord [0x5,0x3e18e0579f4a01e7]),(limbWord [0xd2d,0x3e490c702bd187d8]),(limbWord [0x6,0x969f0c701f4ee537])].getD (i % 8) 0 else [(limbWord [0xd2d,0x3e18f7702bcfa3f8]),(limbWord [0x5,0x3e18e0579f4da1e7]),(limbWord [0x6,0x969f34862bcfa507]),(limbWord [0x7,0x5e9f0c702bcfa1e7]),(limbWord [0x6,0x96e74f862bcfa507]),(limbWord [0x6,0x969f0c83abcfa507]),(limbWord [0xdce,0x969f34863815e7d8]),(limbWord [0x6,0x96490c702bcfa2f7])].getD (i % 8) 0) else (if i < 1336 then [(limbWord [0xebe,0x969f0c702bcfa7b8]),(limbWord [0x6,0x969f24863815e6b7]),(limbWord [0xe16,0x96cb4f863815e7d8]),(limbWord [0xdce,0x96e74f863815e7d8]),(limbWord [0x6,0x969f0c7035cfa537]),(limbWord [0xdce,0x969f0c83b815e7d8]),(limbWord [0x6,0x97034fa24315e7d7]),(limbWord [0x6,0x97034f86380fa537])].getD (i % 8) 0 else [0x29f0c701f4a61e6,(limbWord [0xe76,0x969f0c703455e7d8]),(limbWord [0x6,0x96e74f702bcfa3c7]),(limbWord [0x6,0x969f07702bcfa3c7]),(limbWord [0x6,0x969f2f863815e7d7]),(limbWord [0x6,0x96690c702bcfa2f7]),(limbWord [0x6,0x969f34863815e6b7]),(limbWord [0x6,0x961907702bcfa2f7])].getD (i % 8) 0))) else (if i < 1376 then (if i < 1360 then (if i < 1352 then [(limbWord [0x6,0x96e74f863815e6b7]),(limbWord [0x6,0x970d4f863815e7d7]),(limbWord [0x6,0x969f0c83b815e6b7]),(limbWord [0xe16,0x969f24863815e7d8]),(limbWord [0xd2e,0x1acb4f863815e7d8]),(limbWord [0xe36,0x969f0c7bb815e7d8]),(limbWord [0x6,0x969f27863815e7d7]),(limbWord [0xebe,0x969f0c702bcfa508])].getD (i % 8) 0 else [(limbWord [0xd2d,0x969f0c702bcfa1e8]),(limbWord [0xe76,0x969f0c702bcfa538]),(limbWord [0x6,0x969f0c702bcfa257]),(limbWord [0xebe,0x969f0c702bcfa6d8]),(limbWord [0xef6,0x97034f863815e7d8]),(limbWord [0x6,0xef4b4f863815e7d7]),(limbWord [0xd2d,0x969f0c703455e7d8]),(limbWord [0xe76,0x97034f863815e7d8])].getD (i % 8) 0) else (if i < 1368 then [(limbWord [0x6,0x969f44862bcfa507]),(limbWord [0xf06,0x971f4f863815e7d8]),(limbWord [0x7,0x3a9f0c702bcfa1e7]),(limbWord [0x6,0x969f0c701f4a6507]),(limbWord [0xebe,0x969f0c702bd527d8]),(limbWord [0x6,0x969f0c701f4da537]),(limbWord [0xd2d,0x3e490c702bcfa1e8]),(limbWord [0x7,0x3b4b8fa7b815e7d7])].getD (i % 8) 0 else [(limbWord [0x7,0x6f4b4f863815e7d7]),(limbWord [0xd2d,0x3e890c702bcfa6c8]),(limbWord [0xd2d,0x969f0c702bcfa538]),(limbWord [0xdce,0x969f44863815e7d8]),(limbWord [0x6,0x969f0c579f4a0447]),(limbWord [0xede,0x96cb4f863815e7d8]),(limbWord [0x7,0x5f4b4f86380fa537]),(limbWord [0xd2d,0x3e890c702bcfa328])].getD (i % 8) 0)) else (if i < 1392 then (if i < 1384 then [(limbWord [0xe97,0x3b4b4f863815e7d8]),(limbWord [0xd2e,0x3e9f0c702bd407d8]),(limbWord [0xd2d,0x3e490c703455e7d8]),(limbWord [0xd2d,0x969f0c7035d5e7d8]),(limbWord [0x6,0x97034f863dd5e7d7]),(limbWord [0xd2e,0x3e9f0c7bb815e7d8]),(limbWord [0x6,0x972b4f863815e7d7]),(limbWord [0xd2d,0x3e690c702bcfa1e8])].getD (i % 8) 0 else [0x29f0c702bcfa1e6,(limbWord [0xd2e,0x56cb4f863815e7d8]),(limbWord [0x5,0x969f0c702bcfa1e7]),(limbWord [0xd2d,0xce9f0c702bcfa1e8]),(limbWord [0xd2d,0x3e1907702bcfa1e8]),(limbWord [0x6,0x96890c702bcfa2f7]),(limbWord [0x6,0x969f44863815e6b7]),(limbWord [0xd2d,0x3e490c702bcfa538])].getD (i % 8) 0) else (if i < 1400 then [0x3774f863815e7d6,(limbWord [0xd2d,0x3e9b44863815e7d8]),(limbWord [0x7,0x4b4b4f863815e7d7]),(limbWord [0xd2d,0x3e18f778b815e7d8]),(limbWord [0xe76,0x969f0c702bcfa508]),(limbWord [0xd2e,0x8f034f863815e7d8]),(limbWord [0xd2d,0x3e7124863815e7d8]),(limbWord [0xef7,0x5f4b4f863815e7d8])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c702bd447d7]),(limbWord [0xd2d,0x3e690c702bcfa778]),(limbWord [0xd2d,0x3e490c7035d5e7d8]),(limbWord [0xeaf,0x1b4b4f863815e7d8]),(limbWord [0xd2d,0xce9f0c702bcfa778]),(limbWord [0xe76,0x969f0c702bcfa6d8]),(limbWord [0xd2d,0x3e1907702bcfa778]),(limbWord [0xe36,0x969f0c702bcfa6b8])].getD (i % 8) 0))))

def stateWordDataBlock11 (i : Nat) : Nat := (if i < 1472 then (if i < 1440 then (if i < 1424 then (if i < 1416 then [(limbWord [0xd2e,0x69f24863815e7d8]),(limbWord [0xebf,0x3b4b4f863815e7d8]),(limbWord [0xd2e,0x569f24863815e7d8]),0x34b4f862c95e7d6,(limbWord [0x6,0x969f0c57a80fa507]),(limbWord [0x5,0x3e490c702bcfa1e7]),(limbWord [0xe16,0x969f44863815e7d8]),(limbWord [0x6,0xd74b4f863815e7d7])].getD (i % 8) 0 else [(limbWord [0x6,0x971f4f923815e7d7]),(limbWord [0x6,0x969f0c74b80fa537]),(limbWord [0xd2d,0x3e18e057a80fa6c8]),(limbWord [0xd2d,0x3e690c7035d5e7d8]),(limbWord [0x6,0x969f0c7babcfa507]),(limbWord [0xe96,0x969f24863815e7d8]),(limbWord [0xd2d,0xce9f0c7035d5e7d8]),(limbWord [0xd2d,0x3e18e057a81187d8])].getD (i % 8) 0) else (if i < 1432 then [(limbWord [0xd2e,0x69f34863815e7d8]),(limbWord [0xd2d,0x969f0c702bcfa508]),(limbWord [0xeef,0x5f4b4f863815e7d8]),(limbWord [0x5,0x3e690c702bcfa1e7]),(limbWord [0xd2e,0x69f0c83b815e7d8]),(limbWord [0x7,0x3b4b4f86380fa537]),(limbWord [0xdce,0x969f0c7bb815e7d8]),(limbWord [0x6,0x969f0c702bcfa377])].getD (i % 8) 0 else [(limbWord [0x5,0xce9f0c702bcfa1e7]),(limbWord [0x5,0x3e1907702bcfa1e7]),(limbWord [0x6,0x969ee057a80fa3c7]),(limbWord [0xd2d,0x3e190a7bb815e7d8]),(limbWord [0x6,0x969f49863815e7d7]),(limbWord [0x6,0x9618e057a80fa2f7]),(limbWord [0x6,0x969f0c702bd406b7]),(limbWord [0x6,0x969ef7702bcfa3c7])].getD (i % 8) 0)) else (if i < 1456 then (if i < 1448 then [(limbWord [0x5,0x3e18e0579f43c147]),(limbWord [0xd2d,0x3e18f7702bd1e7d8]),(limbWord [0xd2d,0x3e890c702bcfa1e8]),(limbWord [0x6,0x971f81863815e7d7]),0x34b68863815e7d6,(limbWord [0x6,0x969f0c702bd527d7]),(limbWord [0xd2e,0x3e9f0c702bcfa6b8]),(limbWord [0xd2d,0x3e490c702bcfa508])].getD (i % 8) 0 else [(limbWord [0x6,0x9618f7702bcfa2f7]),(limbWord [0x6,0x969f0c7bb815e6b7]),(limbWord [0x7,0x5f9d4f863815e7d7]),(limbWord [0xd2d,0x3e890c703455e7d8]),0x34b4f86380fa536,(limbWord [0x7,0x334b4f863815e7d7]),(limbWord [0xd2d,0x3e490c702bcfa378]),(limbWord [0x6,0x96cb4f86380fa537])].getD (i % 8) 0) else (if i < 1464 then [(limbWord [0xebe,0x969f24863815e7d8]),(limbWord [0x6,0xd34b4f863815e7d7]),(limbWord [0xd2d,0x3e890c702bcfa778]),(limbWord [0xd2d,0x3e9324863815e7d8]),(limbWord [0xd2e,0x3e9f0c702bcfa228]),(limbWord [0xd2d,0x3e690c702bcfa508]),(limbWord [0x6,0x96c94f863815e7d7]),(limbWord [0xd2d,0xce9f0c702bcfa508])].getD (i % 8) 0 else [(limbWord [0xd2d,0x3e690c702bcfa6d8]),(limbWord [0xd2d,0x3e890c702bcfa538]),(limbWord [0xd2d,0xce9f0c702bcfa6d8]),(limbWord [0xe16,0x969f0c7bb815e7d8]),(limbWord [0xebe,0x969f34863815e7d8]),(limbWord [0x6,0x969f2486380fa537]),(limbWord [0x6,0x969f0c74b815e7d7]),(limbWord [0xebe,0x969f0c83b815e7d8])].getD (i % 8) 0))) else (if i < 1504 then (if i < 1488 then (if i < 1480 then [(limbWord [0x7,0x7b4b4f863815e7d7]),(limbWord [0x6,0x969f0c579f4d6507]),(limbWord [0x6,0x969f0c702bcfa5e7]),(limbWord [0x7,0x1b4b81a7c315e7d7]),(limbWord [0xd2e,0x69f44863815e7d8]),(limbWord [0x6,0xc74b4f86380fa537]),(limbWord [0x5,0x3e890c702bcfa1e7]),(limbWord [0xe36,0x971f4f863815e7d8])].getD (i % 8) 0 else [(limbWord [0x6,0x969f0c702bd287d7]),(limbWord [0xe76,0x96cb4f863815e7d8]),(limbWord [0x6,0x96b94f863815e7d7]),(limbWord [0x6,0x971f4fa23815e7d7]),(limbWord [0xdce,0x969f0c703655e7d8]),(limbWord [0x7,0x5f4b8f863815e7d7]),(limbWord [0xd2d,0x3e18e057a30fa6b8]),(limbWord [0xd2e,0x1a9f0c7bb815e7d8])].getD (i % 8) 0) else (if i < 1496 then [0x3694f863815e7d6,(limbWord [0x6,0x96b34f86380fa537]),(limbWord [0xd2d,0x3e18f7702bcfa1e8]),(limbWord [0x6,0x969f0c702bd307d7]),(limbWord [0x6,0x969f0c7031d5e7d7]),(limbWord [0x6,0x969ee0579f4d63c7]),(limbWord [0xd2d,0x969f0c702bd307d8]),(limbWord [0x6,0x969f0c7022cfa537])].getD (i % 8) 0 else [0x34b4f93b815e7d6,(limbWord [0xd2d,0x3e18f7703455e7d8]),(limbWord [0x6,0x969f0c702bcd6667]),(limbWord [0x6,0x9618e0579f4d62f7]),(limbWord [0x7,0x1b4b4f862bcfa507]),(limbWord [0x6,0x969f0c702bd247d7]),(limbWord [0xd2d,0x3e18f7702bcfa538]),(limbWord [0x6,0x97474f863815e7d7])].getD (i % 8) 0)) else (if i < 1520 then (if i < 1512 then [(limbWord [0xd2e,0x69f0c702bd407d8]),(limbWord [0xe36,0x969f0c702bcfa6c8]),(limbWord [0xebe,0x969f44863815e7d8]),(limbWord [0xe36,0xe74b4f863815e7d8]),(limbWord [0x6,0x969f3f863815e7d7]),(limbWord [0xe76,0x96e74f863815e7d8]),(limbWord [0xe16,0x969f0c702bcfa6b8]),(limbWord [0xe76,0x969f0c83b815e7d8])].getD (i % 8) 0 else [(limbWord [0xd2d,0x3e9344863815e7d8]),(limbWord [0xd2d,0x969f24863815e7d8]),(limbWord [0xd2e,0x69f0c7bb815e7d8]),(limbWord [0x6,0x969f1a863815e7d7]),(limbWord [0x6,0xc74b4f863815e7d7]),(limbWord [0xdce,0x969f0c702bcfa0e8]),(limbWord [0x6,0x969f0c702bcd65f7]),(limbWord [0x5,0x3e18f7702bcfa1e7])].getD (i % 8) 0) else (if i < 1528 then [(limbWord [0x7,0x1b4b4f702bcfa3c7]),(limbWord [0x6,0x969f34863815e7d7]),(limbWord [0x6,0x96e74f863815e7d7]),(limbWord [0x6,0x969f0c83b815e7d7]),(limbWord [0x6,0x969f44863815e7d7]),(limbWord [0x6,0x969f0c702bd407d7]),(limbWord [0x6,0x969f0c7bb815e7d7]),(limbWord [0x6,0x969f0c702bcfa6b7])].getD (i % 8) 0 else [(limbWord [0x7,0x1b4b4f863815e7d7]),(limbWord [0x6,0x971f4f863815e7d7]),0x34b4f862bcfa506,(limbWord [0x6,0x969f0c702bcfa6c7]),(limbWord [0x6,0xe74b4f863815e7d7]),(limbWord [0x6,0x969f0c702bd187d7]),0x34b4f702bcfa3c6,0x34b0c702bcfa2f6].getD (i % 8) 0))))

def stateWordDataBlock12 (i : Nat) : Nat := (if i < 1552 then (if i < 1544 then [0x34b4f863815e6b6,(limbWord [0x7,0xb4b4f863815e7d7]),(limbWord [0x6,0x969f0c702bcfa1e7]),(limbWord [0x6,0x969f0c703455e7d7]),(limbWord [0x6,0x969f0c702bcfa777]),(limbWord [0x6,0x969f0c702bcfa537]),(limbWord [0x6,0x969f0c7035d5e7d7]),(limbWord [0x6,0x97034f863815e7d7])].getD (i % 8) 0 else [0x29f0c702bcfa1e6,(limbWord [0x6,0x969f0c702bcfa507]),(limbWord [0x6,0x969f0c702bcfa6d7]),(limbWord [0x7,0x5f4b4f863815e7d7]),0x34b4f86380fa536,(limbWord [0x7,0x3b4b4f863815e7d7]),0x34b4f863815e7d6,(limbWord [0x6,0x96cb4f863815e7d7])].getD (i % 8) 0) else [(limbWord [0x6,0x969f24863815e7d7]),0x34b4f863815e7d6].getD (i % 8) 0)

def stateWordData (i : Nat) : Nat := (if i < 1024 then (if i < 512 then (if i < 256 then (if i < 128 then stateWordDataBlock0 i else stateWordDataBlock1 i) else (if i < 384 then stateWordDataBlock2 i else stateWordDataBlock3 i)) else (if i < 768 then (if i < 640 then stateWordDataBlock4 i else stateWordDataBlock5 i) else (if i < 896 then stateWordDataBlock6 i else stateWordDataBlock7 i))) else (if i < 1536 then (if i < 1280 then (if i < 1152 then stateWordDataBlock8 i else stateWordDataBlock9 i) else (if i < 1408 then stateWordDataBlock10 i else stateWordDataBlock11 i)) else stateWordDataBlock12 i))

def stateWord (s i : Nat) : Nat := stateWordData ([0,0,0,0,0,19,204,1007,1521,1553].getD s 0 + i)

def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n+1, ids => wireDAt (ids % 512) :: stateWiresD n (ids >>> 9)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, ids => wireSAt (ids % 512) :: stateWiresS n (ids >>> 9)
def SD (s j : Nat) := let p := stateWord s j; stateWiresD (p % 16) (p >>> 4)
def SS (s j : Nat) := let p := stateWord s j; stateWiresS (p % 16) (p >>> 4)

theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAtDataBlock0 (i : Nat) : Nat := (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then [0x53ab184,0x216b2bbc,0x29349c0f,0x2cd64f83,0x3f4e5863,0x50316cae,0x5d781a79,0x5e3e7b82].getD (i % 8) 0 else [0x624a2066,0x73566bed,0x96f84135,0x9a3d4cf6,0xa79b22be,0xa7b372ea,0xc0e13aa2,0xc46ba3b0].getD (i % 8) 0) else (if i < 24 then [0xde256655,0xf2647d4a,0xfc6c28b2,0xcb015e,0x42a26ce,0x5a9d32f,0x8330379,0xbc50f98].getD (i % 8) 0 else [0xbd6d15f,0xcaf6286,0xd9280ba,0xf63c214,0xf7936f4,0xfe85aa7,0x101aa9a3,0x1036662c].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [0x1054628a,0x108e7b6f,0x10d2d46a,0x11fa38c8,0x14ff07e7,0x1714f212,0x181a864d,0x18bb5226].getD (i % 8) 0 else [0x1971f10b,0x1af8f1e9,0x1c2daff4,0x1c68b934,0x1cee937c,0x1d9a6734,0x1e3d37ed,0x1e6f866c].getD (i % 8) 0) else (if i < 56 then [0x1f71f55c,0x1f7231b9,0x23652b54,0x25707ecb,0x26875318,0x29e85827,0x2a928f2d,0x2b5a7ccd].getD (i % 8) 0 else [0x30ea5be7,0x31eadd26,0x327d3eeb,0x35edc97e,0x373cf4c9,0x3818d7d6,0x3a50cc45,0x3b86c1c4].getD (i % 8) 0))) else (if i < 96 then (if i < 80 then (if i < 72 then [0x3e45abd2,0x41b553d5,0x4488548d,0x45b6b5f8,0x46e55386,0x46edb2b4,0x48b8d073,0x490d2be3].getD (i % 8) 0 else [0x4d8e5730,0x4e3955f4,0x4e717564,0x4f1e8eab,0x4fd1913e,0x50b701fb,0x51a56f7e,0x54e32bb5].getD (i % 8) 0) else (if i < 88 then [0x56749803,0x56772976,0x57638b4c,0x59018e72,0x597b252a,0x5beb1467,0x5e29f614,0x5e7dc280].getD (i % 8) 0 else [0x5eaac214,0x5ed1c491,0x6144f31d,0x61d2237f,0x61dfbbca,0x623b077c,0x6a7f33db,0x6e292425].getD (i % 8) 0)) else (if i < 112 then (if i < 104 then [0x7091dc8f,0x724618af,0x73600eaa,0x738814bb,0x741bbc12,0x7898ea9a,0x79e8e975,0x7aa9937e].getD (i % 8) 0 else [0x7b60fd1c,0x7e2a6476,0x7e522095,0x7e91c481,0x7ebf64bd,0x80d3e962,0x8314b9bf,0x8392a0c4].getD (i % 8) 0) else (if i < 120 then [0x85794b5e,0x88c98b49,0x88e6910b,0x8a4a2f62,0x8ac5e7a2,0x8b44e3be,0x8c58fac9,0x8ec95eaf].getD (i % 8) 0 else [0x8f5292e9,0x932c7616,0x963d6601,0x96b905ad,0x97178415,0x97ae457f,0x980280d9,0x999167ca].getD (i % 8) 0))))

def htAtDataBlock1 (i : Nat) : Nat := (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then [0x9c26c2de,0x9edcc006,0xa05bc552,0xa098f954,0xa1fd6dd1,0xa272c106,0xa4aad122,0xa6c8203e].getD (i % 8) 0 else [0xa8d45f97,0xa9fa0826,0xaa0ab39f,0xab6ee6cc,0xace063f0,0xae7aae8a,0xb05adce0,0xb1a7e789].getD (i % 8) 0) else (if i < 152 then [0xb31b1688,0xb3882378,0xb4ae5e6f,0xb4f841fc,0xb7c4635f,0xba8715cd,0xbc6a2c04,0xbce6e458].getD (i % 8) 0 else [0xbf7ca8be,0xc455c03a,0xc49378a5,0xc5926933,0xc75d7aa1,0xc8500784,0xca36ddb0,0xccb0bce1].getD (i % 8) 0)) else (if i < 176 then (if i < 168 then [0xcdbb0fd9,0xcf056150,0xd45f10b7,0xd53cd506,0xd54eb371,0xd73a9094,0xd7de9829,0xd86c18bc].getD (i % 8) 0 else [0xd9be5caa,0xd9bf3cd9,0xdc8667e5,0xdcfe067f,0xdda26cf1,0xde636ee4,0xe08e7903,0xe465d900].getD (i % 8) 0) else (if i < 184 then [0xe5d74980,0xe71c367f,0xe72c50c0,0xe89202ba,0xe9c88d56,0xebec3b58,0xec08905e,0xec0af965].getD (i % 8) 0 else [0xec4080fc,0xec9490e4,0xee23c809,0xee276f41,0xf06f3c17,0xf2cd7e96,0xf4122da5,0xf4201f08].getD (i % 8) 0))) else (if i < 224 then (if i < 208 then (if i < 200 then [0xf46086fa,0xf5f7f5a2,0xf717109d,0xf7fe490c,0xf94f7306,0xf98c5a5d,0xf9fade89,0xfa0fba55].getD (i % 8) 0 else [0xfd0849e0,0xff822fe8,0xff85001e,0xffddc954,0x8809cf,0x917d03,0xcbd06b,0x1a42612].getD (i % 8) 0) else (if i < 216 then [0x1d4d35c,0x2368e9d,0x32ef980,0x3521780,0x387d3db,0x394e50e,0x395718b,0x3b70dd4].getD (i % 8) 0 else [0x3dbb04a,0x44bfa8b,0x44eb0fc,0x47873e4,0x480b8ca,0x4c47257,0x5427959,0x5d625e4].getD (i % 8) 0)) else (if i < 240 then (if i < 232 then [0x5f728c5,0x6286f3b,0x638df7a,0x65e641d,0x6edb33b,0x6f0b0f7,0x79a0b8c,0x7db6898].getD (i % 8) 0 else [0x8082ed5,0x881aaa8,0x8ce3583,0x8cf2503,0x94d48f7,0x9f9f42a,0xae35bd1,0xbc3d1c3].getD (i % 8) 0) else (if i < 248 then [0xcca5e2b,0xd758503,0xe18ee68,0xe20b731,0xe5de5fb,0xf1c3c26,0xfb9cc78,0xfc8419d].getD (i % 8) 0 else [0x1091b1a4,0x10c26fe1,0x10f08023,0x10f8b36f,0x11430e85,0x1176d763,0x118fd42c,0x1194d4b9].getD (i % 8) 0))))

def htAtDataBlock2 (i : Nat) : Nat := (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then [0x11a8357d,0x11c19acb,0x12a3e1a9,0x12cf8cc1,0x12dcad45,0x1322059d,0x1326a97a,0x1329fe23].getD (i % 8) 0 else [0x1383e2cd,0x139a6c1f,0x14189013,0x148dada8,0x148ee088,0x149070ff,0x1567a238,0x15a5e4b8].getD (i % 8) 0) else (if i < 280 then [0x15bbfde6,0x15e432f4,0x15fa01db,0x164ca697,0x16f51937,0x16f8238a,0x171d238f,0x173434f2].getD (i % 8) 0 else [0x17c05204,0x17ceba42,0x17cf18c1,0x183c8346,0x1849bcd9,0x191a699b,0x1979df50,0x199133eb].getD (i % 8) 0)) else (if i < 304 then (if i < 296 then [0x19b1ef7b,0x19d71e4b,0x1a78062d,0x1abcfa94,0x1b21cab2,0x1b3b92c8,0x1bf37f3c,0x1c06a205].getD (i % 8) 0 else [0x1c19d64d,0x1c675a44,0x1c76c683,0x1c7d65e7,0x1cc8b767,0x1d164daa,0x1d18803d,0x1d2e8aaa].getD (i % 8) 0) else (if i < 312 then [0x1d333f1e,0x1da51f58,0x1daa7588,0x1e14b003,0x1e530ace,0x1f556225,0x1fd38619,0x201036b3].getD (i % 8) 0 else [0x20577564,0x2085d729,0x20cab046,0x20f98318,0x2105b989,0x21665d6e,0x218daccb,0x222b8864].getD (i % 8) 0))) else (if i < 352 then (if i < 336 then (if i < 328 then [0x23382d1d,0x235ea04f,0x23931b5a,0x2403f0e2,0x240e28a2,0x241584ec,0x24a97dd3,0x25021f58].getD (i % 8) 0 else [0x260d9aaf,0x263c3c4b,0x26548771,0x265704cd,0x27761991,0x27fdf724,0x2969cc75,0x2978def4].getD (i % 8) 0) else (if i < 344 then [0x299901d7,0x29bbe7dc,0x2a678dcf,0x2a985cbd,0x2a9ac7fe,0x2a9c7953,0x2b83cac5,0x2c593b7f].getD (i % 8) 0 else [0x2cbb8819,0x2d30ca31,0x2da68a7b,0x2df16e93,0x2e21eee1,0x2ee5b592,0x2f07ef53,0x2f56ed56].getD (i % 8) 0)) else (if i < 368 then (if i < 360 then [0x2f84c504,0x30ef02dc,0x31befafc,0x31c7c8e1,0x323bbd43,0x32461195,0x327fca49,0x32abee2b].getD (i % 8) 0 else [0x32f64846,0x342b651e,0x348b9c2f,0x353c2a03,0x35a850fb,0x35cb54c4,0x36442565,0x3686af49].getD (i % 8) 0) else (if i < 376 then [0x3697a754,0x36c9774c,0x3750dc52,0x3810e15b,0x38695614,0x38f6531d,0x39577cce,0x395ed260].getD (i % 8) 0 else [0x39d3caf1,0x3a7e0863,0x3ab926da,0x3ad753a2,0x3adc9f4f,0x3aea674f,0x3b29f4b8,0x3b86e040].getD (i % 8) 0))))

def htAtDataBlock3 (i : Nat) : Nat := (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then [0x3b980bcd,0x3be45415,0x3c1079e9,0x3c8fd648,0x3d93d4d4,0x3dd108d6,0x3e6e50c1,0x3e8e6753].getD (i % 8) 0 else [0x3eb0d9fd,0x3eb4f6e4,0x3ee87627,0x3f2c0f24,0x3f669a1b,0x3f9ec90f,0x40292e34,0x4036383d].getD (i % 8) 0) else (if i < 408 then [0x40d28382,0x40d5048a,0x4171e6ac,0x417bb88e,0x4201f637,0x423ff6c7,0x4292c033,0x42bfdf78].getD (i % 8) 0 else [0x42d9bb04,0x430a5a0c,0x436157bb,0x4369c601,0x43723f28,0x43b1e118,0x44002fc0,0x445a23b2].getD (i % 8) 0)) else (if i < 432 then (if i < 424 then [0x44f1f914,0x45f8dbaf,0x4635baff,0x46472f6e,0x46f1bd89,0x4724f79f,0x4742c321,0x47e26d40].getD (i % 8) 0 else [0x481ebcbb,0x48a6f64e,0x48c1fa65,0x49399b2a,0x493e78cc,0x49991a0c,0x49c01d2a,0x4a0829d9].getD (i % 8) 0) else (if i < 440 then [0x4a2fb0f4,0x4a31ec23,0x4a8f9ff6,0x4a901084,0x4a9b253a,0x4ad01e10,0x4bea489e,0x4c02420b].getD (i % 8) 0 else [0x4c4d149b,0x4c8f6669,0x4c9c2ce5,0x4e02edc4,0x4e514525,0x4e611022,0x4e661b36,0x4e8cd868].getD (i % 8) 0))) else (if i < 480 then (if i < 464 then (if i < 456 then [0x4f5f8298,0x4f75496d,0x5032a49a,0x50723305,0x50c032fa,0x50d644db,0x511cbd20,0x51614329].getD (i % 8) 0 else [0x51883e30,0x5230c156,0x526dafa6,0x52a47b2f,0x53c3f53a,0x53d86735,0x541f4d16,0x5490a2be].getD (i % 8) 0) else (if i < 472 then [0x54c32e99,0x54f1450c,0x5507107e,0x556784c9,0x559400e1,0x55dc7f46,0x55eeebea,0x56399bf6].getD (i % 8) 0 else [0x563e8129,0x56d32240,0x57216df2,0x57a193db,0x57c17f24,0x57e85f4b,0x57ebbbef,0x580bbf38].getD (i % 8) 0)) else (if i < 496 then (if i < 488 then [0x58237876,0x58358aca,0x586476fd,0x588477f9,0x58ee91b4,0x593f5038,0x5977f173,0x59ab54b1].getD (i % 8) 0 else [0x59bacc01,0x59c25c04,0x5a2370f1,0x5b1321ae,0x5b241fd8,0x5b7e75a2,0x5b9c60b8,0x5bb1a40a].getD (i % 8) 0) else (if i < 504 then [0x5bb65b8e,0x5beda8de,0x5c0e6685,0x5cceeade,0x5cd3d165,0x5cfb6d2f,0x5d3ddcca,0x5d694432].getD (i % 8) 0 else [0x5d799123,0x5dd5d4d7,0x5e0987c0,0x5e2e285c,0x5fdf0496,0x5ff2c9fa,0x60736406,0x60c69834].getD (i % 8) 0))))

def htAtDataBlock4 (i : Nat) : Nat := (if i < 576 then (if i < 544 then (if i < 528 then (if i < 520 then [0x60e8c912,0x60eaf5d1,0x614c76a7,0x61b3c90e,0x61d6dae6,0x625adfa1,0x62671f85,0x634b6044].getD (i % 8) 0 else [0x63c98438,0x6546b28f,0x659fba9f,0x6629c8d3,0x6753f0a1,0x676eed32,0x677ac771,0x68b3bf3a].getD (i % 8) 0) else (if i < 536 then [0x68cf1499,0x68fc28d6,0x691ba73b,0x6988c9b5,0x69f93436,0x6a1d3a89,0x6a2cab38,0x6a7f33db].getD (i % 8) 0 else [0x6bad8080,0x6bbc6637,0x6be8d141,0x6c1a4466,0x6c3d482f,0x6c5d3977,0x6c90ee41,0x6d1b70e8].getD (i % 8) 0)) else (if i < 560 then (if i < 552 then [0x6d5e43ff,0x6db29fad,0x6e2c9e54,0x6ec081a6,0x6ed2a343,0x6f48f90b,0x6f728191,0x6f8ced90].getD (i % 8) 0 else [0x6f993cd3,0x6fffb95c,0x70a4f313,0x70ebb277,0x71093d11,0x7109f73f,0x718d008a,0x71a318c7].getD (i % 8) 0) else (if i < 568 then [0x71fd9eec,0x71fdbb85,0x7201d81c,0x721fc702,0x723efdef,0x72680fb1,0x72e30dc2,0x7301920c].getD (i % 8) 0 else [0x73b2da29,0x740c4a0a,0x7455d988,0x745bc6f4,0x749f7435,0x74a1ed10,0x74ccd71e,0x7516a7ab].getD (i % 8) 0))) else (if i < 608 then (if i < 592 then (if i < 584 then [0x75944e5e,0x75972626,0x763cbb8c,0x76468413,0x76835917,0x77d0435c,0x77eedb70,0x77f73d35].getD (i % 8) 0 else [0x79844e92,0x7a1d9587,0x7a41cfe2,0x7a5c3d1f,0x7a5c7619,0x7a662a18,0x7aa097d3,0x7abda2ad].getD (i % 8) 0) else (if i < 600 then [0x7ba80d5c,0x7bef4278,0x7c72c263,0x7c84083c,0x7d2c4f6e,0x7e3b65dd,0x7e496f31,0x7e49c60c].getD (i % 8) 0 else [0x7e570604,0x7f072098,0x7f0e6fa2,0x7f27c6ca,0x7f3d2367,0x7fa9aeab,0x7fbbc330,0x7fd9c29b].getD (i % 8) 0)) else (if i < 624 then (if i < 616 then [0x805a6a3b,0x821251d9,0x824de453,0x827598eb,0x8327778b,0x83397023,0x841c9583,0x8433a81e].getD (i % 8) 0 else [0x84ca8c3f,0x8534e19f,0x85352f36,0x856a0f8e,0x85d2fcbe,0x860778a3,0x860df111,0x8644c314].getD (i % 8) 0) else (if i < 632 then [0x86b6ba1f,0x87010c14,0x87b0d5da,0x88084d3a,0x885c6c07,0x88f825c8,0x891c56c8,0x8925d09a].getD (i % 8) 0 else [0x8958ce9a,0x8966cf07,0x8975c6a9,0x8978907e,0x89d90852,0x8a04bc12,0x8a687c47,0x8a7043c4].getD (i % 8) 0))))

def htAtDataBlock5 (i : Nat) : Nat := (if i < 704 then (if i < 672 then (if i < 656 then (if i < 648 then [0x8b35022b,0x8b6508c1,0x8c3d145b,0x8c64b545,0x8c7c529d,0x8cb75834,0x8cb7f884,0x8cb8317e].getD (i % 8) 0 else [0x8cbc62e0,0x8d66d2b1,0x8d69efdc,0x8daf34a9,0x8db7eb16,0x8df1a76b,0x8e0ce32e,0x8e141838].getD (i % 8) 0) else (if i < 664 then [0x8e462fa7,0x8ec4539b,0x8ec95eaf,0x8fa3a660,0x900a1472,0x903e9165,0x90531709,0x91259d90].getD (i % 8) 0 else [0x914a3d27,0x91582e8a,0x9158fa22,0x9176656d,0x91b4a35b,0x91f0690d,0x927d01c2,0x9288bc06].getD (i % 8) 0)) else (if i < 688 then (if i < 680 then [0x92b01602,0x92cdd7dd,0x932e96bf,0x9530d284,0x95f6800b,0x96556d73,0x9688117f,0x969cfa98].getD (i % 8) 0 else [0x97393685,0x97909d04,0x97e4a5bf,0x9986764c,0x9a43f0f8,0x9a74f5e8,0x9ae202d8,0x9b59184e].getD (i % 8) 0) else (if i < 696 then [0x9b818bff,0x9bd1820e,0x9bed9ede,0x9cdba903,0x9dded454,0x9e5bfb2f,0x9f0adc6f,0x9f1e42bf].getD (i % 8) 0 else [0x9f34f85f,0x9f7d61b3,0x9f8d6960,0x9faf8f28,0xa022df09,0xa09dfdc7,0xa0c4e8fd,0xa0e9e52d].getD (i % 8) 0))) else (if i < 736 then (if i < 720 then (if i < 712 then [0xa10233a2,0xa155cf2c,0xa17efbef,0xa1b141b5,0xa29a4cca,0xa336980f,0xa35ca948,0xa3e84187].getD (i % 8) 0 else [0xa3ee42cf,0xa404b401,0xa53f9f02,0xa5570c82,0xa5b5bd98,0xa5e71feb,0xa63498a6,0xa6912471].getD (i % 8) 0) else (if i < 728 then [0xa706577d,0xa7ef1762,0xa82ec226,0xa9397043,0xa93c72bf,0xa94c8d00,0xa955b156,0xa996c204].getD (i % 8) 0 else [0xaa0ab937,0xaa5c77af,0xaa779f20,0xaac64142,0xab605a13,0xabbcd1ac,0xabeb5a4b,0xac81d21d].getD (i % 8) 0)) else (if i < 752 then (if i < 744 then [0xad0b2a3d,0xad23c93a,0xad52b925,0xadec262d,0xae9d4f43,0xae9f1404,0xaf1e2fc8,0xaf30fa9b].getD (i % 8) 0 else [0xaf5accf5,0xaf913030,0xafa9e6e4,0xafde7287,0xafe63385,0xb04f74e7,0xb0615082,0xb07b19c0].getD (i % 8) 0) else (if i < 760 then [0xb0a196dc,0xb0ab1b19,0xb0eb089e,0xb135cf42,0xb190bd10,0xb1a1098b,0xb1d6a800,0xb204685b].getD (i % 8) 0 else [0xb30fc351,0xb3381220,0xb33a5968,0xb401d08a,0xb4658fb9,0xb5827691,0xb58d8ec6,0xb5e43194].getD (i % 8) 0))))

def htAtDataBlock6 (i : Nat) : Nat := (if i < 832 then (if i < 800 then (if i < 784 then (if i < 776 then [0xb643fcec,0xb680c33a,0xb699f1c0,0xb718eab9,0xb7b2c7e7,0xb803c969,0xb845ee15,0xb885ea44].getD (i % 8) 0 else [0xb89db083,0xb8a014ae,0xb8a5b482,0xb8d07ac3,0xb98a4c7d,0xb9a78990,0xba1fe6fd,0xba69ba1c].getD (i % 8) 0) else (if i < 792 then [0xbab2391d,0xbabdb649,0xbad276b6,0xbb03a14e,0xbb86e9c1,0xbc2a9acb,0xbc952050,0xbd67524f].getD (i % 8) 0 else [0xbda856e5,0xbe007545,0xbe9ff960,0xbee527f8,0xbeec6161,0xbf2e5912,0xbf716938,0xbfa838b5].getD (i % 8) 0)) else (if i < 816 then (if i < 808 then [0xbfbbfde5,0xbff4c981,0xc0319ebe,0xc03a21d9,0xc082eccc,0xc21d50f1,0xc3121e17,0xc3706567].getD (i % 8) 0 else [0xc3b04f86,0xc3bfd78b,0xc3c5624c,0xc43b824d,0xc440707a,0xc450685a,0xc4807fda,0xc4936dba].getD (i % 8) 0) else (if i < 824 then [0xc4f87730,0xc514860c,0xc53e12fe,0xc57534bf,0xc5bd4e44,0xc6403587,0xc6ef4269,0xc752910b].getD (i % 8) 0 else [0xc76ef983,0xc7aac71c,0xc7ca9eaf,0xc7f65e1b,0xc7fdb2a4,0xc871fec4,0xc8a3d607,0xc8e7c19e].getD (i % 8) 0))) else (if i < 864 then (if i < 848 then (if i < 840 then [0xc8f5ad25,0xc9c98627,0xca93f777,0xcbbfb860,0xcbf57c8a,0xcca18265,0xcccc4e77,0xcce6dabd].getD (i % 8) 0 else [0xcd29643f,0xcd3c644f,0xcd4a7f96,0xcdfaba31,0xce47da11,0xce54eae4,0xcf008f72,0xcf902030].getD (i % 8) 0) else (if i < 856 then [0xcfb2bcfa,0xcfb54e6d,0xd008909e,0xd0143332,0xd0ad6a5e,0xd0f86b5f,0xd0ff9fd5,0xd16eb0be].getD (i % 8) 0 else [0xd17c067e,0xd18a1477,0xd1e2224d,0xd2031f6d,0xd2a5d78c,0xd3100871,0xd325d900,0xd369f1e4].getD (i % 8) 0)) else (if i < 880 then (if i < 872 then [0xd39df516,0xd3b54c9a,0xd4611103,0xd4815a87,0xd518fe4e,0xd5317ce6,0xd55d07c2,0xd5a769e4].getD (i % 8) 0 else [0xd6147160,0xd6348c5e,0xd6d127ed,0xd6e9d7ff,0xd6fdc25f,0xd711b623,0xd79486f5,0xd836a18f].getD (i % 8) 0) else (if i < 888 then [0xd85ece98,0xdaad799f,0xdb1de0c1,0xdb46b93e,0xdb7dbb54,0xdb9fcaa4,0xdba0f9d9,0xdc13830a].getD (i % 8) 0 else [0xdc50e257,0xdd1443bb,0xddd4b2fd,0xde64c43d,0xde70effd,0xde82b1c4,0xdf7042a0,0xe017f48b].getD (i % 8) 0))))

def htAtDataBlock7 (i : Nat) : Nat := (if i < 960 then (if i < 928 then (if i < 912 then (if i < 904 then [0xe0be2412,0xe0ee15e5,0xe0f77256,0xe11b2361,0xe13aeeb1,0xe15f9e5c,0xe1b912a5,0xe1d7c96e].getD (i % 8) 0 else [0xe2eec57a,0xe3743a59,0xe3b67d2d,0xe46e5de5,0xe4851be0,0xe4f6722f,0xe546afb9,0xe5a66a5a].getD (i % 8) 0) else (if i < 920 then [0xe5db34a3,0xe6440233,0xe6777220,0xe68253da,0xe6893cd6,0xe6c6f2c5,0xe72e393f,0xe795f9f1].getD (i % 8) 0 else [0xe7a8b1ea,0xe7c2f270,0xe81cec25,0xe857016f,0xe8f90708,0xe9165bce,0xe91c3f57,0xe9289625].getD (i % 8) 0)) else (if i < 944 then (if i < 936 then [0xe986121f,0xeaa9e39e,0xeac666b2,0xeb5e6b80,0xeb7bfacb,0xeba984e6,0xec009263,0xec59c7d9].getD (i % 8) 0 else [0xec7eb657,0xed10c264,0xedd9056d,0xedf5c434,0xee098406,0xeea4c504,0xeee76b37,0xef4b37bd].getD (i % 8) 0) else (if i < 952 then [0xef7cab1d,0xf0197e9b,0xf04c2ec6,0xf0e91852,0xf0eb10a7,0xf17d1813,0xf1bb3889,0xf21dd5c1].getD (i % 8) 0 else [0xf2301b58,0xf25f1a0c,0xf27b1621,0xf2fac0ee,0xf3018ba3,0xf3242b04,0xf431432e,0xf4386cef].getD (i % 8) 0))) else (if i < 992 then (if i < 976 then (if i < 968 then [0xf49f2213,0xf4d24aca,0xf4d8e68a,0xf5d54f09,0xf60f0ab6,0xf65372fd,0xf6951e87,0xf6956be8].getD (i % 8) 0 else [0xf6a01902,0xf7340a82,0xf767fb11,0xf76bb417,0xf774037a,0xf7a4e7a5,0xf7bf5c64,0xf7dda163].getD (i % 8) 0) else (if i < 984 then [0xf86cd5d4,0xf8a8b28e,0xf8af4896,0xf8f58994,0xf92b6f3b,0xfa48f55e,0xfa6fe511,0xfa9758a2].getD (i % 8) 0 else [0xfac2c056,0xfb9d0b70,0xfbae8313,0xfbd5295b,0xfc02962f,0xfc2f5339,0xfc7003a3,0xfc92e700].getD (i % 8) 0)) else (if i < 1008 then (if i < 1000 then [0xfca6e14c,0xfce1b778,0xfd36578e,0xfd3e6f92,0xfd852482,0xfdbd2cdb,0xfdce3754,0xfe1a2110].getD (i % 8) 0 else [0xfe218dc6,0xfe6ed172,0xfea60993,0xfec995e5,0xff6c77ea,0xffd2f4c4,0xfff1a506,0xf1514b].getD (i % 8) 0) else (if i < 1016 then [0x1a1d5cb,0x1ab55b3,0x21ff9bf,0x31b43de,0x4d845d4,0x591471e,0x5c9deae,0x6b8f295].getD (i % 8) 0 else [0x6ba13b6,0x78a65f2,0x8b313ac,0x9049651,0x9e34f8d,0x9e65200,0xa2ad5f3,0xa8aac81].getD (i % 8) 0))))

def htAtDataBlock8 (i : Nat) : Nat := (if i < 1088 then (if i < 1056 then (if i < 1040 then (if i < 1032 then [0xb2e8e04,0xb5aa8f7,0xb88db1e,0xba4edd3,0xbe6cc46,0xc035d33,0xe08b0f9,0xe8297ab].getD (i % 8) 0 else [0xee60f8c,0x11430e85,0x11985911,0x11b1c0b3,0x11bf3e89,0x11f23c1d,0x126a4691,0x137167e1].getD (i % 8) 0) else (if i < 1048 then [0x13e4f08e,0x13f2276a,0x1529da5d,0x15911c7d,0x168a1fcb,0x17a5b568,0x1914adfa,0x1a045c42].getD (i % 8) 0 else [0x1a1792ff,0x1a78062d,0x1a809761,0x1aa83dc5,0x1ab3de44,0x1ad3884b,0x1bbd9273,0x1bf10fcb].getD (i % 8) 0)) else (if i < 1072 then (if i < 1064 then [0x1c03f28a,0x1c7532e9,0x1d8d67fc,0x1dabc315,0x1e4287ab,0x1f4da5bf,0x1f5fb1fc,0x1f9eb27c].getD (i % 8) 0 else [0x1ff18742,0x2008801d,0x20243909,0x2033c8fd,0x2178772c,0x22e07c5b,0x2315eda9,0x234a981e].getD (i % 8) 0) else (if i < 1080 then [0x235ea04f,0x23b8fe9a,0x23d918e8,0x247cfa6b,0x2551c99a,0x25ee40b8,0x26b11526,0x2754f6a9].getD (i % 8) 0 else [0x27625bc8,0x27d31a9d,0x2829c5d8,0x28a7e9cc,0x293f72cf,0x2966652a,0x299f7579,0x2a77a975].getD (i % 8) 0))) else (if i < 1120 then (if i < 1104 then (if i < 1096 then [0x2ab79f9d,0x2b0e6e0b,0x2b860d2b,0x2b9e22c0,0x2c3d76c9,0x2cb53901,0x2cee049d,0x2d219e73].getD (i % 8) 0 else [0x2d2572d6,0x2d335cf5,0x2dc8e959,0x2e2da276,0x2e9838f8,0x2f3c4ca0,0x2f3e139c,0x2fb63352].getD (i % 8) 0) else (if i < 1112 then [0x300b5933,0x310bf73e,0x3153fd01,0x3199ed24,0x31a2bbd4,0x34c5359c,0x357dbb7a,0x357df569].getD (i % 8) 0 else [0x35e3409a,0x36fa2f7c,0x38e8913d,0x38e99c89,0x39d22bba,0x39f15936,0x3a504fae,0x3afe4ed8].getD (i % 8) 0)) else (if i < 1136 then (if i < 1128 then [0x3b2b56d5,0x3b7852e3,0x3c8f033d,0x3cd364da,0x3ce2c01e,0x3d42991a,0x3d9e48b7,0x3dc1f201].getD (i % 8) 0 else [0x3ee289db,0x3ef49dbb,0x3f1b5e84,0x3f280d51,0x3f3aa2b3,0x4085a6ff,0x40d5655a,0x418770e9].getD (i % 8) 0) else (if i < 1144 then [0x419f9066,0x41b71368,0x43c615dc,0x43f5a889,0x443ab0f1,0x44f7a52a,0x45cef07c,0x45e701f3].getD (i % 8) 0 else [0x469e121a,0x4701b9ed,0x471755c0,0x471c360e,0x4740b566,0x47dd00ab,0x47fcaab2,0x4844d531].getD (i % 8) 0))))

def htAtDataBlock9 (i : Nat) : Nat := (if i < 1216 then (if i < 1184 then (if i < 1168 then (if i < 1160 then [0x48bebbe3,0x496c1f78,0x49ef51fe,0x49ff9082,0x4a5a63a5,0x4a6d75f2,0x4ade1c09,0x4c32d9c9].getD (i % 8) 0 else [0x4c4d149b,0x4cfe29af,0x4d325fe3,0x4e4846f0,0x4ea0b2cd,0x4eaeb4d4,0x4ecc61d0,0x4f529657].getD (i % 8) 0) else (if i < 1176 then [0x4f5f8298,0x501dad66,0x50c18ee9,0x517719e9,0x51965e18,0x51a45e0e,0x52228202,0x5236fda4].getD (i % 8) 0 else [0x5370ad3c,0x540c74fd,0x54405fa0,0x54b2d8af,0x550ef9e2,0x55453671,0x558d1dd6,0x5621d141].getD (i % 8) 0)) else (if i < 1200 then (if i < 1192 then [0x572377e7,0x57c8b09e,0x57e0c204,0x5808f8e1,0x58f9cd7f,0x5977f173,0x59a1f77a,0x59b0d944].getD (i % 8) 0 else [0x59d9b1c1,0x5ae3dada,0x5b1b22e1,0x5c31ea7f,0x5cedb5b4,0x5f3276b1,0x6048723b,0x605a0514].getD (i % 8) 0) else (if i < 1208 then [0x605ba8f8,0x60ec53be,0x61002ed9,0x61cfcb68,0x61ee5803,0x62311c43,0x62900fdd,0x62a6dde1].getD (i % 8) 0 else [0x633ec3fa,0x63425a26,0x63743787,0x63ee1e39,0x642a9ddf,0x64ce7f62,0x65a34e91,0x6629c8d3].getD (i % 8) 0))) else (if i < 1248 then (if i < 1232 then (if i < 1224 then [0x664c9616,0x66a741bc,0x66afe4a8,0x67ef1f34,0x68b53ae9,0x691ba73b,0x69249254,0x69a2b648].getD (i % 8) 0 else [0x6a2ec1ba,0x6a3c7d69,0x6a5c8c6f,0x6ac71b72,0x6bd75091,0x6c512fb8,0x6cec4006,0x6d6db8cc].getD (i % 8) 0) else (if i < 1240 then [0x6d84e1ec,0x6d902189,0x6dafcb90,0x6dc8a573,0x6e64f0b8,0x6e9bb1c8,0x6f4988b2,0x6f56fc79].getD (i % 8) 0 else [0x6f7116a1,0x6fd20b79,0x714535a7,0x71ecf1ac,0x72f063e1,0x72f1bcd0,0x735bea3e,0x736988cf].getD (i % 8) 0)) else (if i < 1264 then (if i < 1256 then [0x73e6ee57,0x742adc54,0x74cd2094,0x750c11ed,0x752fff91,0x753a7310,0x756df798,0x75c8601f].getD (i % 8) 0 else [0x75e7de4a,0x75faf394,0x76468413,0x772622b1,0x772a3ac7,0x774bb473,0x77adcb06,0x77b54f52].getD (i % 8) 0) else (if i < 1272 then [0x791f6894,0x79a1fdbc,0x79deba4c,0x7b10f64e,0x7b4139e5,0x7b804fc6,0x7b8b0b4e,0x7cf0015f].getD (i % 8) 0 else [0x7d93e2e2,0x7e68b211,0x7fa1e45d,0x80356f2f,0x80f76d2d,0x81d7f84d,0x821a56e1,0x823cc98b].getD (i % 8) 0))))

def htAtDataBlock10 (i : Nat) : Nat := (if i < 1344 then (if i < 1312 then (if i < 1296 then (if i < 1288 then [0x830b2cd9,0x832cfe93,0x834afaaa,0x8386af13,0x83e58471,0x858de5c5,0x85cc2178,0x864a456c].getD (i % 8) 0 else [0x86b3a9fa,0x86c9bcf8,0x8768dab7,0x87a178e1,0x87acd519,0x87b66172,0x881e4348,0x8859febf].getD (i % 8) 0) else (if i < 1304 then [0x892ecdee,0x8acbf0bc,0x8b3bbb23,0x8c402481,0x8cd93cfa,0x8cde4441,0x8d84cb5f,0x8d8fd648].getD (i % 8) 0 else [0x8daf34a9,0x8dba4117,0x8f1de6c7,0x8fb157d1,0x8feae8c8,0x8fef9e47,0x901117f3,0x9057db6b].getD (i % 8) 0)) else (if i < 1328 then (if i < 1320 then [0x9069d566,0x91106149,0x912d70b8,0x9187e1d0,0x92045096,0x92912a94,0x92d91fc5,0x936d8ac3].getD (i % 8) 0 else [0x93fe7e85,0x9433b3b2,0x956982e4,0x96735638,0x96ac9e28,0x972684da,0x99ddfd32,0x9a3c8f2c].getD (i % 8) 0) else (if i < 1336 then [0x9a625164,0x9abab320,0x9ad733d0,0x9b211876,0x9b4a24c2,0x9b9aff28,0x9d29b488,0x9dc5ffcd].getD (i % 8) 0 else [0x9f34f85f,0xa02e3e37,0xa0815ace,0xa0fb4180,0xa1cf6ca4,0xa2163bc8,0xa2945fbc,0xa3d33dbe].getD (i % 8) 0))) else (if i < 1376 then (if i < 1360 then (if i < 1352 then [0xa3d77b00,0xa426331b,0xa45161b2,0xa48185a7,0xa4deb8f9,0xa68d53f0,0xa690efa7,0xa69e1b0d].getD (i % 8) 0 else [0xa7a31a30,0xa7e34a47,0xa820ee03,0xa840a42b,0xaa295ec2,0xaaec3402,0xaaf45a14,0xadc9c126].getD (i % 8) 0) else (if i < 1368 then [0xaec371ef,0xaf13224e,0xaf38b9b8,0xaf5fbd34,0xb05c9c6f,0xb1024652,0xb14d6c07,0xb1a77b0b].getD (i % 8) 0 else [0xb2845150,0xb2940aba,0xb2a96624,0xb337ec3d,0xb33a8de1,0xb33cd72e,0xb341e8d8,0xb34cd4ce].getD (i % 8) 0)) else (if i < 1392 then (if i < 1384 then [0xb3bc6140,0xb4288c46,0xb49eabeb,0xb61401f8,0xb6323d19,0xb8524abf,0xb901ee1a,0xb92718a3].getD (i % 8) 0 else [0xb9464fb7,0xb9ba73f8,0xb9fed595,0xba6a33e7,0xbae41a99,0xbb702ad3,0xbbee4ec7,0xbc53b7fb].getD (i % 8) 0) else (if i < 1400 then [0xbd47ef67,0xbd6bce0f,0xbdc9f73f,0xbe328cc5,0xbf637e8d,0xbf654238,0xbf83e721,0xbfa547cd].getD (i % 8) 0 else [0xbfa838b5,0xbfbb666c,0xbfbe53cf,0xc0106544,0xc0fe81b0,0xc10607ab,0xc1786862,0xc1bcb646].getD (i % 8) 0))))

def htAtDataBlock11 (i : Nat) : Nat := (if i < 1472 then (if i < 1440 then (if i < 1424 then (if i < 1416 then [0xc23a2eda,0xc345aa31,0xc364c5cf,0xc397e27c,0xc3a23c07,0xc3a9276c,0xc5b5214e,0xc5f9b4ab].getD (i % 8) 0 else [0xc617e8bf,0xc6dc80cc,0xc772d4d2,0xc798006b,0xc7cbfa80,0xc82ccef4,0xc8db1baf,0xc8eb8584].getD (i % 8) 0) else (if i < 1432 then [0xca13db76,0xca299a6a,0xca64b2a8,0xcb82d408,0xcbd0dd6c,0xcc074c58,0xcc4074ce,0xcc501e75].getD (i % 8) 0 else [0xccc5ef4c,0xcd3fd5fe,0xcd76f8ad,0xcda91c7e,0xcf532b7d,0xd04ef4eb,0xd0cd18df,0xd1a0b726].getD (i % 8) 0)) else (if i < 1456 then (if i < 1448 then [0xd1eead33,0xd24e3096,0xd28107ae,0xd29d856b,0xd2b16c06,0xd32f95ee,0xd381ad15,0xd3d3ec41].getD (i % 8) 0 else [0xd478b364,0xd4f6d758,0xd5a16596,0xd5d24792,0xd614e257,0xd6348c5e,0xd6b2f62a,0xd6cd6835].getD (i % 8) 0) else (if i < 1464 then [0xd7b617e5,0xd7c9cf25,0xd9155577,0xd9b60332,0xdb55c5c1,0xdbad98dd,0xdbcef041,0xdcf0b421].getD (i % 8) 0 else [0xdd5021fb,0xdd8753a2,0xde933d3f,0xdebda9df,0xdf8fc481,0xe077ba0c,0xe0edd824,0xe14cc677].getD (i % 8) 0))) else (if i < 1504 then (if i < 1488 then (if i < 1480 then [0xe278414c,0xe2fb5cd6,0xe31958ee,0xe35b5f80,0xe36dca81,0xe376a926,0xe4dcc313,0xe57b6d26].getD (i % 8) 0 else [0xe601e5b5,0xe6d1298e,0xe70ea516,0xe74b8466,0xe762965e,0xe8196e76,0xe844a653,0xe8c52f08].getD (i % 8) 0) else (if i < 1496 then [0xea258a8a,0xeb7fefc6,0xeb89903f,0xec2a82b1,0xec8ac124,0xecd0197c,0xece3088f,0xed790e9a].getD (i % 8) 0 else [0xee92b1df,0xeedad023,0xef042fa1,0xefa815ba,0xf4f51ce7,0xf68e7996,0xf68fdc33,0xf7b424c2].getD (i % 8) 0)) else (if i < 1520 then (if i < 1512 then [0xf84c9499,0xf8c5b5b2,0xf8e9b38c,0xf9699735,0xf985aeb1,0xf9984345,0xf9ed0c35,0xfa1229f7].getD (i % 8) 0 else [0xfae99ed9,0xfb419742,0xfc765312,0xfce32769,0xfd88007e,0xfda50805,0xfdce8d68,0xfde54ba4].getD (i % 8) 0) else (if i < 1528 then [0xfec9d98d,0x262be00,0x3a5d944,0x41fbff6,0x1bbcad0b,0x309b7723,0x34c5359c,0x4ff497f2].getD (i % 8) 0 else [0x61ee5803,0x73b34ed2,0x832cfe93,0x86fd975e,0x87a178e1,0x88764810,0x8d01bb39,0x8fd9b777].getD (i % 8) 0))))

def htAtDataBlock12 (i : Nat) : Nat := (if i < 1552 then (if i < 1544 then [0x9057db6b,0x9a1eadf2,0xa6ea9452,0xaa3bd436,0xad7ee21b,0xb1f0e046,0xb55b7c1a,0xb7d75725].getD (i % 8) 0 else [0xb9464fb7,0xc971148c,0xcb139daa,0xcd534030,0xd614e257,0xe618a3b0,0xf02639af,0xf0debf8d].getD (i % 8) 0) else [0xfa891164,0xf02639af].getD (i % 8) 0)

def htAtData (i : Nat) : Nat := (if i < 1024 then (if i < 512 then (if i < 256 then (if i < 128 then htAtDataBlock0 i else htAtDataBlock1 i) else (if i < 384 then htAtDataBlock2 i else htAtDataBlock3 i)) else (if i < 768 then (if i < 640 then htAtDataBlock4 i else htAtDataBlock5 i) else (if i < 896 then htAtDataBlock6 i else htAtDataBlock7 i))) else (if i < 1536 then (if i < 1280 then (if i < 1152 then htAtDataBlock8 i else htAtDataBlock9 i) else (if i < 1408 then htAtDataBlock10 i else htAtDataBlock11 i)) else htAtDataBlock12 i))

def htAt (s i : Nat) : Nat := htAtData ([0,0,0,0,0,19,204,1007,1521,1553].getD s 0 + i)

def NN (s : Nat) := [0,0,0,0,19,185,803,514,32,1].getD s 0
def idxH (s h : Nat) := bsr (htAt s) h 11 0 (NN s)
def idx (s : Nat) (ws : List Nat) := idxH s (hk 0 ws)

def cutWordDataBlock0 (i : Nat) : Nat := (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then [0x46f8da145405203,0xc906766254d0206,0x1474210714449200,0x24aaa90304405204,0x2866afdf00000006,0x290f6a8b00010100,0x30a0c4c245405203,0x3e77cc0b00010100].getD (i % 8) 0 else [0x4815bf0500011103,0x594e5c4605450204,0x59c98c0b00000008,0x5c0743f904405204,0x600ccd4d2540c206,0x626958304540c206,0x6742fa0614449203,0x90aaf73c05450204].getD (i % 8) 0) else (if i < 24 then [0x914a96e400000006,0x947a6e4100004100,0x9572b89a0004810a,0x9a31303900000008,0xa072ba9100000006,0xa4082c831444d203,0xabf040ef45405203,0xb040d60514449203].getD (i % 8) 0 else [0xb275380300010100,0xbe7dff994548c206,0xc49facd100000006,0xcec56ab000011103,0xd81da6a100000006,0xed0608821444d203,0xef3a7de713449200,0xf1ef74f300000006].getD (i % 8) 0)) else (if i < 48 then (if i < 40 then [0xffc6220c1444d200,0x246eb400000000,0x83a33a00000006,0xa692fb00000000,0x1d3808d00000000,0x1e40d3b00000000,0x222c32b00011103,0x28148e000004100].getD (i % 8) 0 else [0x294e40700011104,0x3d1f96500000004,0x46015e800051103,0x47f026d05450204,0x4c280d835448206,0x4e565d500000006,0x5b06a3f00004100,0x5d9b9e400000000].getD (i % 8) 0) else (if i < 56 then [0x60dc8f200011104,0x628e1ef0004d103,0x6946dbe00000000,0x6f3246300000006,0x747e37a00011103,0x75ff1c20000000a,0x7b27b8c00011103,0x7bffaa800000006].getD (i % 8) 0 else [0x7c3697900051103,0x7ca421d00000000,0x8019f8435490208,0xa2ad5f300000004,0xbc4836600050104,0xc33f09900008100,0xc58d13600010100,0xcd3224a00000000].getD (i % 8) 0))) else (if i < 96 then (if i < 80 then (if i < 72 then [0xe2612d70000000a,0xe475fd005450208,0xec11dce05450206,0xfbbb72900000004,0x12420ff213449203,0x1286ee2200000006,0x136f553000000008,0x137d1b1a4500d206].getD (i % 8) 0 else [0x14f919b600000004,0x151179a50004d100,0x1515a92e0000000a,0x1a26d5aa00000008,0x1ab8721413449203,0x1c17709500049100,0x1c76c68305450208,0x1cf84d5b0000000a].getD (i % 8) 0) else (if i < 88 then [0x1d2ce6180004d103,0x1fb5e04200051103,0x1ffd9cb435011206,0x2083cb6500005104,0x209262f400051103,0x210114304508d206,0x2105b98915091206,0x222cd10f14449203].getD (i % 8) 0 else [0x223e6b2200000008,0x225a0ac800000004,0x22bad1c900000003,0x23f1bcf400011103,0x24a2a2d500000008,0x26388cdd35490206,0x26ed557800011103,0x27392c1f00000000].getD (i % 8) 0)) else (if i < 112 then (if i < 104 then [0x28a8f8ba05450204,0x28af0c5500000000,0x2963364600049103,0x2978def400011103,0x2afd36ad00051103,0x2bf184b90008d106,0x2cee049d00011103,0x2d122a9d00051103].getD (i % 8) 0 else [0x2d31ef090000000a,0x2ee9b0ed00000000,0x2ff89ec400000000,0x303865ce35490206,0x320a04960004d103,0x32af5e1200011103,0x34d8bce20004d103,0x34dade6800000000].getD (i % 8) 0) else (if i < 120 then [0x353c2a0305450206,0x35aad86000049103,0x35ba03a000011103,0x35ed480400005104,0x35fbdf930004d103,0x372bf16300005103,0x37399f6745448206,0x373e603000000003].getD (i % 8) 0 else [0x3743091100000003,0x3841e38d00000004,0x387f68e235490208,0x3928b26300011103,0x39e2372900000008,0x39f17efd00011104,0x3a05975f00051103,0x3a13498300000008].getD (i % 8) 0))))

def cutWordDataBlock1 (i : Nat) : Nat := (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then [0x3a5b24560000000a,0x3a706af300005104,0x3a7af01300000008,0x3aa1b3c100000003,0x3b567f710004810a,0x3b6f581d0004d100,0x3be454151508d206,0x3c5b327a00011103].getD (i % 8) 0 else [0x3d6a63e800011104,0x3d89927c25005206,0x3daaca1300000006,0x3eb4f6e400000004,0x3f0d153300000006,0x4036383d00000004,0x40ab962200000008,0x40faaf4600000006].getD (i % 8) 0) else (if i < 152 then [0x418770e900000004,0x419127b00000000a,0x42f1de130000000a,0x44268e1c00049100,0x44f17345254d0206,0x45e1c4340000000a,0x464ceed100010100,0x46962c5500000000].getD (i % 8) 0 else [0x480331d700004100,0x4815bf0500011103,0x48ed4d7005448206,0x493da3d235490206,0x4af6825d00000006,0x4b144a4805448208,0x4b1d8e5745405203,0x4bdabb5000051100].getD (i % 8) 0)) else (if i < 176 then (if i < 168 then [0x4deb4a6f00049103,0x50ebc08e35448208,0x50f4706f00050104,0x5100a2ba00049103,0x5174c78015091206,0x51ce8ddd00005104,0x51dd256c00049103,0x52be5ef00004d103].getD (i % 8) 0 else [0x5370ad3c00000000,0x538f628c00000008,0x53c02de100000000,0x54a561cc00049103,0x54a6500500000004,0x565fee4d00000006,0x568afad505450204,0x575e136700000008].getD (i % 8) 0) else (if i < 184 then [0x5965fbe20000000a,0x59d5d77a00004100,0x59ff453c1444d200,0x5ae3dada00005103,0x5bb60f1b4548c206,0x5bc4defb00000000,0x5c36ce5b00000004,0x5cfbcecc00050104].getD (i % 8) 0 else [0x5d6f069500010100,0x5ddb80f500000003,0x5e74da9e00000008,0x5e830e8f00000000,0x5f00156100049103,0x5ff074e500000003,0x5ff9bfbc00000000,0x60c1cb450000000a].getD (i % 8) 0))) else (if i < 224 then (if i < 208 then (if i < 200 then [0x617f9ec800011103,0x6291086100000008,0x62b5db8b00011104,0x62fc27b300000000,0x64173a8a45404206,0x6440674300000006,0x648e89ff0000000a,0x65696b631508d206].getD (i % 8) 0 else [0x65e194d300048106,0x662868c30004d103,0x665a5c7f05450204,0x66dd31b300000000,0x6719ebc100000006,0x678b277200000000,0x67d11abe00000004,0x69aa57e300000004].getD (i % 8) 0) else (if i < 216 then [0x6b0687ed35005206,0x6bcc9a7300000008,0x6d13e1a600000006,0x6ef334cc00051103,0x6fe8e96f0508d206,0x6fffb95c00000004,0x70332c9900000003,0x70a09d3b1508d208].getD (i % 8) 0 else [0x711640aa00000008,0x714535a700010100,0x71b7bf4c0000000a,0x71cd05e900005104,0x71e959b200090108,0x725eecc300000008,0x72770ff600000004,0x732e2f7000000003].getD (i % 8) 0)) else (if i < 240 then (if i < 232 then [0x739aca7f00000000,0x739cf30f00000006,0x73e6ee5700000003,0x741502a000000003,0x741c09030000000a,0x744fc53300000006,0x745a8df20000c100,0x75222c1d00010100].getD (i % 8) 0 else [0x7555b62300000006,0x76017fa100000004,0x769f476800000000,0x78083d8a13449200,0x780bf27100011104,0x78f73ca600000008,0x7924d4ab00000000,0x7a3b766c00000003].getD (i % 8) 0) else (if i < 248 then [0x7a9842fb2540c206,0x7b32e58e0000000a,0x7b56e52100048106,0x7c75a5b000000004,0x7da5ff6335490206,0x7e10a12300000006,0x7f70725e00000000,0x7f87d5e213405203].getD (i % 8) 0 else [0x7fa1e45d00000003,0x7fcb69e41540c206,0x824aa8fc00000006,0x8297817c05450204,0x831d27b300000006,0x83a0fb9f0000000a,0x83dd850500000008,0x845cb16b0004d103].getD (i % 8) 0))))

def cutWordDataBlock2 (i : Nat) : Nat := (if i < 320 then (if i < 288 then (if i < 272 then (if i < 264 then [0x8557935d00000008,0x858ed6d400000006,0x86e93d7700051103,0x87099b0f13405203,0x877fa46005448206,0x889f976a00000004,0x8a01a6801444d203,0x8acdfacf00000003].getD (i % 8) 0 else [0x8b49d1eb0000000a,0x8ba20e1800000004,0x8d5360de00011104,0x8e23c0b100000004,0x8e4eafac00000004,0x8e5a2ab635448206,0x8e5a3c091508d208,0x8f27847500000006].getD (i % 8) 0) else (if i < 280 then [0x8f4c3afa00010100,0x8f779e5c00000000,0x8fd6da9f00000006,0x9047935d00000008,0x91890c5c25051206,0x919925d600000003,0x92f2b99912405203,0x9393695100000004].getD (i % 8) 0 else [0x943e2df81508d206,0x945869c200050104,0x9466563f00000004,0x948d0ccf00000000,0x9558007b00049103,0x9573ced20004d103,0x9624b76100000003,0x9806dfb400000006].getD (i % 8) 0)) else (if i < 304 then (if i < 296 then [0x9958db9a05450204,0x998b6b1a4500d206,0x99deb1c913449203,0x9a747ec612405203,0x9aa61e6a00000008,0x9b3addfd0000000a,0x9b5764fd00000004,0x9b818bff00051103].getD (i % 8) 0 else [0x9c4bbac84548c206,0x9d0f6f0400048108,0x9d91261200000003,0x9eb8361800000000,0x9f7b0e0800011104,0x9f7b212100000003,0xa03df74400049103,0xa083aa2e0000000a].getD (i % 8) 0) else (if i < 312 then [0xa12adc1f4540c206,0xa1cd950500000003,0xa1e5eb3405450204,0xa29a4cca00000004,0xa4be115500000006,0xa5aa7f0900011103,0xa5eaa90200000008,0xa6dfb49d05450206].getD (i % 8) 0 else [0xa70f64304508d206,0xa9c876e8254d0206,0xaa847d3c00000006,0xaa8fdc6000000008,0xaafda80500000004,0xab2a668a00000003,0xab5161fd45448206,0xab58b6290000000a].getD (i % 8) 0))) else (if i < 352 then (if i < 336 then (if i < 328 then [0xab7be10c00000003,0xabb4c7710000000a,0xad4c26c700010100,0xad785ed545448208,0xadde0b9805450208,0xafd232c00004810a,0xb02953a50000000a,0xb03b50be00004100].getD (i % 8) 0 else [0xb0eb089e0004d103,0xb1259c1745405203,0xb19b3f100000000a,0xb22e676a0000000a,0xb28f80840000000a,0xb31a749800051103,0xb401d08a00011104,0xb4054b2d00000000].getD (i % 8) 0) else (if i < 344 then [0xb4bfa35000049100,0xb4f4c06a00051103,0xb5ab86cf00011103,0xb5cd208c00010100,0xb5d604151508d206,0xb641296500000008,0xb6cef4070004d100,0xb72c493500000000].getD (i % 8) 0 else [0xb78f42e900051103,0xb803c96900000004,0xb99b64d915091208,0xbad86c1105450206,0xbbeed09600000008,0xbd47ef6700051103,0xbe2e4e6700005103,0xbfa592bb05448208].getD (i % 8) 0)) else (if i < 368 then (if i < 360 then [0xbfb6fb2d00000006,0xbfd85e0e00011103,0xc0bade9c35448206,0xc11400740000000a,0xc182275200051100,0xc1e65e4c0004d100,0xc2a66ce10000000a,0xc315fe6600010100].getD (i % 8) 0 else [0xc397e27c00004100,0xc39dd0ad00000000,0xc4784bc000000003,0xc47cdf7f00000003,0xc55af83d00000003,0xc5805ba700000004,0xc59ebf6100000006,0xc5ab4aa200000004].getD (i % 8) 0) else (if i < 376 then [0xc5bbc52c35490208,0xc664c78f00000006,0xc795c5bd00011103,0xc8b7172b0000000a,0xc8c9457f00000008,0xcaae161000005103,0xcadac86800049103,0xcaffc345254d0206].getD (i % 8) 0 else [0xcbc2f13500000004,0xcc6e503800000003,0xcccc4e7700049103,0xccf8bf880004d103,0xcd625d3c15410206,0xce4ba42b00090106,0xceae479100000004,0xced2c96700010100].getD (i % 8) 0))))

def cutWordDataBlock3 (i : Nat) : Nat := (if i < 448 then (if i < 416 then (if i < 400 then (if i < 392 then [0xcfdb4f2a04405204,0xd00356cc0000000a,0xd07484c600000000,0xd07cf28a00000004,0xd17f94e200000008,0xd1f952e000000006,0xd1fd50ac00051103,0xd2131be400000003].getD (i % 8) 0 else [0xd272dd3600000003,0xd298e3e800000006,0xd2b16c060004d103,0xd307b10200000008,0xd488d8f100090108,0xd4be9af900000006,0xd4d58ada05448206,0xd65ef2e3000d1106].getD (i % 8) 0) else (if i < 408 then [0xd6945d4700049100,0xd6bb23d200051103,0xd7769f1e14449200,0xd9ebe43800000000,0xdaf0cdc400005103,0xdc2f6a3200000008,0xdc50e25700000004,0xdcedd7b3050d1206].getD (i % 8) 0 else [0xdd656d3f00000003,0xdd9c7ec000000004,0xdec3214d35448208,0xdec92ecc00000006,0xe01a853800000004,0xe0dcf1b300000008,0xe22b188a00000004,0xe2385d1b00000000].getD (i % 8) 0)) else (if i < 432 then (if i < 424 then [0xe336a05c00000008,0xe35b779d00000006,0xe42af9b100000003,0xe6d630fd00000006,0xe720016c00051100,0xe7a79c6400048108,0xe96daf9c1444d203,0xea258a8a00000000].getD (i % 8) 0 else [0xeb176cf300000003,0xeb36e5a745005206,0xeb5e6b8000011104,0xebb3f0c000000004,0xed1eb78500051103,0xedd89e5745049206,0xee92b1df00049103,0xef24566300000006].getD (i % 8) 0) else (if i < 440 then [0xef5445b800000000,0xf02639af00000000,0xf086d5ed00000006,0xf0a9f3f80004810a,0xf25af30625051208,0xf3af938d00000006,0xf42c7b854500d208,0xf562f3c900051103].getD (i % 8) 0 else [0xf5e7932400000003,0xf5eb790200000000,0xf5f7396f00000000,0xf7340a8215091208,0xf74fbd3b00000006,0xf8709b6a0000000a,0xf91b5c980004810a,0xf931ec6200000006].getD (i % 8) 0))) else (if i < 480 then (if i < 464 then (if i < 456 then [0xf993945d25051206,0xf9e0723b00090106,0xfbab62fa4500d206,0xfc5a75d100000006,0xfcd8935314449203,0xfd44dccf2540c206,0xfda51b1300000000,0xfea1f1a600000006].getD (i % 8) 0 else [0xff9ed39c00004100,0xffa167b24540c206,0x1303f100000004,0x1d3ff40000000a,0x3673e000049103,0xc852a600000000,0xcf363000049103,0xd1976000000003].getD (i % 8) 0) else (if i < 472 then [0xef475e00004106,0x14f4a0c45404206,0x17876c500000006,0x19328e100011106,0x1cd0ceb00000006,0x1e6eb5400000004,0x20343f200000003,0x20f9f6a00000006].getD (i % 8) 0 else [0x212517400049103,0x2152d4c00000000,0x2265a9a00000006,0x23cc3e400090106,0x23e53cf0008d106,0x262be0000000003,0x267f81000048106,0x28c382600049103].getD (i % 8) 0)) else (if i < 496 then (if i < 488 then [0x2a17ae51508d206,0x2afbc6900005103,0x33952d900011103,0x3a5d94400000003,0x3c5be1600000004,0x3d31ccd00051100,0x3d3328545448208,0x3e1b25300000008].getD (i % 8) 0 else [0x40d1ff000000003,0x415d31500000008,0x41fbff600000003,0x451fb4300000006,0x478536b05450208,0x47f026d0000000a,0x4d5ee8100000000,0x4dc4f1d00005103].getD (i % 8) 0) else (if i < 504 then [0x51c6a0d00000008,0x52de82500000003,0x591471e00000003,0x59a3c9c00000000,0x5bc716100048106,0x60c2a6d0000000a,0x64eab2400011103,0x66757ea00011108].getD (i % 8) 0 else [0x671036900000003,0x684d81a0004810a,0x69dcc9c00000004,0x6bcb35400000004,0x6d035dc0000000a,0x71a8eca00000000,0x71d65d400000000,0x74abb4600000008].getD (i % 8) 0))))

def cutWordDataBlock4 (i : Nat) : Nat := (if i < 576 then (if i < 544 then (if i < 528 then (if i < 520 then [0x76152d60008a108,0x78a65f200000003,0x7e9c2ac00000000,0x8172db40000000a,0x81c935600010100,0x836de6900000004,0x84fc7bd00000004,0x853e5dc00000004].getD (i % 8) 0 else [0x8c074d90000000a,0x8ce972b00000004,0x9388e5f00000004,0x975b0dd0004d103,0x995440800000003,0x9dbf87500000003,0x9e34f8d00000004,0xa04ddbe00000003].getD (i % 8) 0) else (if i < 536 then [0xa12e83400000003,0xa1b0b1e0000000a,0xa23259a25005208,0xa2ad5f300000004,0xa34069c00000008,0xa3507df0000000a,0xa498b6b00002106,0xa4bf12800000006].getD (i % 8) 0 else [0xaa786f10000000a,0xabe4c0600000003,0xb02994800000008,0xb26bd8d0000000a,0xb5048c400000000,0xb622d890000000a,0xbb0979a45404208,0xbb3503400000004].getD (i % 8) 0)) else (if i < 560 then (if i < 552 then [0xbd5cd2400011108,0xbed1c790008d108,0xc36fcb800000003,0xce1dbae0000000a,0xce8c45100000000,0xcec76770000d106,0xd42fc040000000a,0xd52ac7200000006].getD (i % 8) 0 else [0xd8647c300000000,0xdc0ad9f00000006,0xdd38cbd00000003,0xdd8acbd1508d208,0xddaaa3b00000004,0xddd9aea00090108,0xdfcda6700000006,0xe0b815900000004].getD (i % 8) 0) else (if i < 568 then [0xe9f2cec0004c106,0xee60f8c0000000a,0xf66f9cc00011106,0xf96fc4500000008,0xfde230d00000008,0xff37bf700000004,0x100643bc00010100,0x101dbeef00000004].getD (i % 8) 0 else [0x1021512500000000,0x10432e23000d1106,0x10c955a800000000,0x10cb895300000004,0x10cd89ad00000003,0x10e796e700000000,0x110ce3d30000000a,0x110e84ec0004810a].getD (i % 8) 0))) else (if i < 608 then (if i < 592 then (if i < 584 then [0x110f6e390000000a,0x11360f7c000ce108,0x113bfb0e00000003,0x11d3855d0000000a,0x11d97f7c00000003,0x1221aeb945448206,0x123ea16100000004,0x12a53a9800090108].getD (i % 8) 0 else [0x13a447ee00000000,0x13a897ea00000000,0x13f325d500000000,0x14105df200051106,0x1426003700000000,0x148c2fae00002108,0x14abdda600000003,0x14bbf0a000011106].getD (i % 8) 0) else (if i < 600 then [0x14f9756100005103,0x1519626800000004,0x153b53d300000003,0x15a0d1d800000006,0x15ba7b9d00000004,0x1679420c00000003,0x1696c84e00000006,0x16d5455100000004].getD (i % 8) 0 else [0x173748a20000000a,0x175067f300000004,0x1769baa300000006,0x17b61f2000000008,0x17bf6d2200000004,0x17d15dce00049100,0x17f1f2be00000003,0x1871a1ce25005206].getD (i % 8) 0)) else (if i < 624 then (if i < 616 then [0x18a5efa70000000a,0x18b15fb400000006,0x1911bfb735490208,0x193caf2400048108,0x1945372e00000008,0x195ef4580000000a,0x19ce1de000000004,0x1a1792ff00009106].getD (i % 8) 0 else [0x1a29253b00000004,0x1a3beae400000008,0x1a80976100000004,0x1a8bd25200011103,0x1aa6d65600000000,0x1ad24bc600000004,0x1b215f240000000a,0x1b7de53e00000000].getD (i % 8) 0) else (if i < 632 then [0x1b860d6b000d1108,0x1b922f5b00000003,0x1b992dd505448206,0x1bbcad0b00000004,0x1c0fba8700000006,0x1c1f817c0004d100,0x1c634c7900000000,0x1c74d4e400000004].getD (i % 8) 0 else [0x1c90c3440000000a,0x1cae817100005103,0x1d0da56a00000003,0x1d5e54ad00000008,0x1d7416cf00000008,0x1e245c3a00000004,0x1e31f31900000006,0x1e4287ab00051103].getD (i % 8) 0))))

def cutWordDataBlock5 (i : Nat) : Nat := (if i < 704 then (if i < 672 then (if i < 656 then (if i < 648 then [0x1eb4776a0000000a,0x1ed1b33600000004,0x2008801d0008a106,0x20191d4500000004,0x2024390900050108,0x2033c8fd00000004,0x2055373500000006,0x20d8ed150000000a].getD (i % 8) 0 else [0x20dc445200112106,0x20ddc6b500000003,0x211162b600000004,0x2115948700000008,0x212d0fc60000000a,0x2154957535490206,0x2178ec520000000a,0x222f452100011103].getD (i % 8) 0) else (if i < 664 then [0x2244610a00000000,0x22526e0745448206,0x228fa2df00000008,0x2294f85000000004,0x2298e43a00000000,0x22cea83200049100,0x22e06e9e0000000a,0x22e07c5b0008a108].getD (i % 8) 0 else [0x2315eda900000003,0x235b4b6900000006,0x236640bf00004100,0x236a8b6f0000000a,0x242d843600005106,0x2473c23e00049100,0x24f5a50a0004d100,0x250b3bdc45448206].getD (i % 8) 0)) else (if i < 688 then (if i < 680 then [0x255d08a600000006,0x2593a36a00000008,0x25ee40b800000000,0x25fea5ca00000000,0x2612f2b40000000a,0x261f29b500000003,0x26340dae00000004,0x2658435b00000004].getD (i % 8) 0 else [0x26638bb50000000a,0x269abf160004d100,0x26b5bb2d00000006,0x2770921b00010106,0x278b2b5835448206,0x2809904a0000000a,0x28a2611c25005206,0x29389f6c0000000a].getD (i % 8) 0) else (if i < 696 then [0x295eafa200000003,0x29863dab00000000,0x299304070000000a,0x299a58a000000003,0x2a9a350800000006,0x2aab48fa0000000a,0x2afafc0a00000000,0x2b1ee89500112108].getD (i % 8) 0 else [0x2b469b4700000003,0x2b4f2fe70000000a,0x2b5ad02e00000003,0x2b860d2b000d1106,0x2b9e22c000000000,0x2ba970cf00000006,0x2bb5e30300000004,0x2bcd02dc00046106].getD (i % 8) 0))) else (if i < 736 then (if i < 720 then (if i < 712 then [0x2be2904600046106,0x2c566b4000050104,0x2c7f24c800000000,0x2cee049d0000000a,0x2d0eea2100000006,0x2d12603000000008,0x2d2424e000000000,0x2d335cf500002106].getD (i % 8) 0 else [0x2ddfb31a00000003,0x2dfc88de00000003,0x2e26202600000004,0x2e30f01600000008,0x2e5583a700000004,0x2e5e113700000000,0x2e8e18a500000008,0x2e9dde1300010100].getD (i % 8) 0) else (if i < 728 then [0x2e9fe91a0000000a,0x2ec4867700000000,0x2f100dbb00000004,0x2f3e139c00005103,0x2f4d2c1a00090106,0x2f9a4aa00000000a,0x3001baba00000006,0x300b593300002108].getD (i % 8) 0 else [0x3013b61600004100,0x309b772300000003,0x309db3bd0000000a,0x30a0c99405450208,0x30b0cda845404208,0x30ceb00305450206,0x30fa7f3300000000,0x313f96c30000000a].getD (i % 8) 0)) else (if i < 752 then (if i < 744 then [0x31a2bbd400051100,0x31fa88a200010100,0x325081a500000008,0x3267960900000004,0x326e29a805448208,0x32f39e1a0000d106,0x330fdc3e00000003,0x331627a200000006].getD (i % 8) 0 else [0x331683bf00000006,0x3331adcc00000004,0x3337ffb700112106,0x33430d0700000000,0x3373fb2900000004,0x33a01c9d00000008,0x33d19a6000005104,0x33d4a7b70000000a].getD (i % 8) 0) else (if i < 760 then [0x342eb5b700000004,0x346233d900000003,0x349c415245049206,0x34c5359c00000000,0x3511c3ef00000008,0x351df4fd35448208,0x353eef3600000006,0x354724b80008c106].getD (i % 8) 0 else [0x356000d000000004,0x3568694205450208,0x35aede4e0000000a,0x35b194ee00000003,0x35c1494f00000004,0x35d13ed500000004,0x36663f000004810a,0x367a78120000000a].getD (i % 8) 0))))

def cutWordDataBlock6 (i : Nat) : Nat := (if i < 832 then (if i < 800 then (if i < 784 then (if i < 776 then [0x369f23c800000003,0x3779daea0000000a,0x37b5a63d00000006,0x37bbeaa635448206,0x37ca63f500000006,0x389e026b00000000,0x38e99c8900050106,0x3919d58d15091208].getD (i % 8) 0 else [0x391c30c200050104,0x395466d800000004,0x397f55d300000004,0x3980b86e00000003,0x398fd05d00090108,0x39b4582f00000008,0x39b77ee400000003,0x39c3391b00000006].getD (i % 8) 0) else (if i < 792 then [0x39c7ed4d00000006,0x39d5bb2300000004,0x3a218d7500000003,0x3a59d37935490206,0x3a67deb000000004,0x3a8d365900000006,0x3aea5b2b00000004,0x3b7852e300000004].getD (i % 8) 0 else [0x3c0bab6800000008,0x3c41d0f000000008,0x3c61fcaf00000004,0x3ccfd67c00000000,0x3cfa8cc90004810a,0x3d3295930000000a,0x3d7aa3fa00112108,0x3de4b33a0000000a].getD (i % 8) 0)) else (if i < 816 then (if i < 808 then [0x3e5b4fcb0000000a,0x3e6e868900011103,0x3ef49dbb00050108,0x3eff49dc45404206,0x3f08229800000004,0x3f2a88ee00011103,0x3f96fc6600000004,0x3ffa7a3300000000].getD (i % 8) 0 else [0x4008a50000000003,0x4057375825051206,0x406da43200011103,0x4088609600000006,0x40c9ac750004d103,0x40cc165a00000003,0x40cff88600000008,0x40e78ae400011103].getD (i % 8) 0) else (if i < 824 then [0x4159249c00051100,0x416c8af400000003,0x418770e900000004,0x41f620d700000006,0x4212d77100000004,0x42ef490f00000004,0x4322b88400000008,0x4326663d0000000a].getD (i % 8) 0 else [0x4362c48c0008a106,0x436c713100048106,0x438873d900000003,0x43f5a88900011103,0x4417c41f05450206,0x44798a5a00000004,0x44d726c800000004,0x45054daa00008106].getD (i % 8) 0))) else (if i < 864 then (if i < 848 then (if i < 840 then [0x4528f2ea0000000a,0x453a35e035490208,0x45681c4f00000004,0x456f31c000000008,0x4589020900000000,0x462614e100000006,0x4698629a00000004,0x471aaab700000003].getD (i % 8) 0 else [0x4740b56600091106,0x475301d300000004,0x478a6a9e0000000a,0x47a973f500000008,0x47b8f33e45448206,0x47bc8cbe00000006,0x47c7ebe200000008,0x47d6337c00000006].getD (i % 8) 0) else (if i < 856 then [0x48cf847500010100,0x493b16ff00005104,0x4963173d0000000a,0x49f3e8cd00000000,0x49f84e9300000004,0x4a01d58e35490208,0x4a09d40f00000004,0x4a1161a200000006].getD (i % 8) 0 else [0x4a35554700000004,0x4a89ac7a00000006,0x4aa013670000000a,0x4ab41def0004d100,0x4abdb9d900000008,0x4b4bca8600005103,0x4b5ffbb400000003,0x4b60800600000008].getD (i % 8) 0)) else (if i < 880 then (if i < 872 then [0x4b713d2545049208,0x4b91419e00000004,0x4b91a71900000004,0x4c1757aa00090106,0x4c21e2c00004d103,0x4c2613f100000006,0x4c3299a200010100,0x4c56a78a0000000a].getD (i % 8) 0 else [0x4c935925000d1108,0x4cc39a1500000004,0x4d31c93400050104,0x4da568cf0008a108,0x4de913b945404208,0x4e08e65300000003,0x4e2d4b7b000ce106,0x4e4846f000091106].getD (i % 8) 0) else (if i < 888 then [0x4e4b20ca00000003,0x4e4fb15800000003,0x4e723c280000000a,0x4e7911ad05450208,0x4ec9d1e000000004,0x4ece348200000006,0x4ed28de500000000,0x4ed4525200050104].getD (i % 8) 0 else [0x4eee745300000003,0x4eef1fd100000004,0x4f0c886800000004,0x4f30092a45404206,0x4f8edacc00091106,0x4fa8d36c00000006,0x4fe7572c00000004,0x4ff497f200000000].getD (i % 8) 0))))

def cutWordDataBlock7 (i : Nat) : Nat := (if i < 960 then (if i < 928 then (if i < 912 then (if i < 904 then [0x4ff7ca9900091106,0x5006925700046106,0x5036cd3500011103,0x504eb44b00000004,0x5053d7ca00000004,0x50b6191100090108,0x50d2ec8600009106,0x5113f4d80000000a].getD (i % 8) 0 else [0x512e9c8145448208,0x517719e900091108,0x5187947300000008,0x51a9eddd00000004,0x51cebab200000000,0x51e5b11735448208,0x520e87e400049103,0x520ed00000000004].getD (i % 8) 0) else (if i < 920 then [0x521ec77100091108,0x52b95bb300000004,0x52c264e100000004,0x537938e700000008,0x539d307f00048106,0x53e9c2de00000008,0x540c74fd00048108,0x541b6dab00000006].getD (i % 8) 0 else [0x5429331a00000000,0x5434902c00049103,0x543802ff00000000,0x5515b8c000000003,0x554f1df600000004,0x5580f73000000004,0x558bffae00011103,0x559645ad00011106].getD (i % 8) 0)) else (if i < 944 then (if i < 936 then [0x5597fdc800000004,0x5605d9a500000000,0x5621d14100112106,0x5629971d0004d100,0x568c9b7b00000006,0x5720b34b0000000a,0x572c332b25051208,0x5733de4f00000003].getD (i % 8) 0 else [0x575158a215410206,0x5755dcb200000000,0x5774234200000008,0x57ae948600000003,0x57d7bac300000000,0x57e4bd6e00000000,0x57e9862400000006,0x58b1306b00090106].getD (i % 8) 0) else (if i < 952 then [0x58ecbf3a00000004,0x58f9cd7f00112108,0x594652bf00000006,0x59c2f2e700000000,0x59d596ff00000003,0x59d9b1c100000000,0x5a2b84c505448206,0x5a386d5b00050104].getD (i % 8) 0 else [0x5a6db7ef000d1106,0x5a6f402b00004100,0x5a74d1d600000003,0x5a8f485800000004,0x5abee3ef00000000,0x5ae3dada00000004,0x5b1b22e100000004,0x5be7f0dd00000003].getD (i % 8) 0))) else (if i < 992 then (if i < 976 then (if i < 968 then [0x5beb11e115410208,0x5c352fd600010108,0x5c36ce5b00000004,0x5c87cfec00000000,0x5cc4777800000004,0x5cec03f70000000a,0x5cef0aaf00000006,0x5cfbcecc0000000a].getD (i % 8) 0 else [0x5d226fdd35448206,0x5d9cebac00000000,0x5da1ee550000000a,0x5da94c2000000004,0x5dd384f100000000,0x5ddb80f500000003,0x5e6afa4e00000004,0x5e6d8cdf00009106].getD (i % 8) 0) else (if i < 984 then [0x5e8fe02600000008,0x5e969fd105448208,0x5ea2f90700000000,0x5eb5073400000000,0x5ec4864000000004,0x5ee97a4200000003,0x5ef0ac800000000a,0x5f04954535490206].getD (i % 8) 0 else [0x5f3276b100011104,0x5f4d5e3e00000000,0x5f621cea00049100,0x5fd9092700000008,0x6012a6eb00000006,0x6056208100000003,0x605778aa00004100,0x605ad03300000004].getD (i % 8) 0)) else (if i < 1008 then (if i < 1000 then [0x606e90b400000004,0x60973dcb0000000a,0x60f8337f35490208,0x6103c6d90000d108,0x611c791b00010100,0x618b32f200000003,0x61ee580300000004,0x6224411c00000004].getD (i % 8) 0 else [0x6280d11f00000003,0x6292889a00011103,0x62ad5f3c00000000,0x62f951e40000000a,0x62fc27b300000000,0x630ae11700010106,0x63127df900000004,0x634e109400000006].getD (i % 8) 0) else (if i < 1016 then [0x635e3f7f05448208,0x63b6c30c00000008,0x63f18b3c00000000,0x6439f18b00000004,0x645ea6ca00000008,0x649ab67b000d1108,0x64de82b9000d1108,0x651c5cd800005104].getD (i % 8) 0 else [0x65908d0500000003,0x659e99fe00005103,0x65a1c74800000003,0x65ad318d00000003,0x65b830ea00000004,0x65bb97560000c106,0x666aef8600000003,0x66844ae700000000].getD (i % 8) 0))))

def cutWordDataBlock8 (i : Nat) : Nat := (if i < 1088 then (if i < 1056 then (if i < 1040 then (if i < 1032 then [0x6696688d00000000,0x66e1b54200005103,0x66f04cd100000003,0x670c457a00000000,0x67379fa80000000a,0x674063aa00051103,0x676a338300000003,0x67751ca300000006].getD (i % 8) 0 else [0x6887aa4900000003,0x68b88be30008d108,0x68d9871b0000000a,0x68faddcc00000003,0x698287460000000a,0x69d958580000000a,0x6a3c7d6900091106,0x6a4cf7f3000d1108].getD (i % 8) 0) else (if i < 1048 then [0x6a9a6cbe15410206,0x6b017a6700000004,0x6b5bfc9e00000004,0x6c351da300000004,0x6c8a922e0004d103,0x6d0b79440000000a,0x6d1de44500000004,0x6d205f2b00005103].getD (i % 8) 0 else [0x6d233f9a00009108,0x6d59af9800000006,0x6d59b71300000004,0x6d6342110000000a,0x6d8a8a5d00000000,0x6d9056bf00000003,0x6da9bd1c0000000a,0x6dc8a57300000004].getD (i % 8) 0)) else (if i < 1072 then (if i < 1064 then [0x6e0c50be00000004,0x6e199ac10000d108,0x6e637a6f00005103,0x6e735ef700000000,0x6ea208b400000000,0x6ea84c7a00000008,0x6ec859a600000008,0x6edd612100005103].getD (i % 8) 0 else [0x6eec18b800000008,0x6f0e7d0d0000000a,0x6f35549335490206,0x6fbcf4ed00011104,0x705e60d50000000a,0x70b3083d00000003,0x70b4d7bb00000003,0x70dd1ebc00000004].getD (i % 8) 0) else (if i < 1080 then [0x714535a700000003,0x715b85e000051103,0x71a5d4c20008d106,0x720d9a5c05448206,0x725f6fcd00000008,0x72c69d6f00000004,0x72f063e100046106,0x7339689e00000004].getD (i % 8) 0 else [0x735762f40000000a,0x7372d56635448206,0x737947bb05450208,0x73970265000d1106,0x739c0a8800000006,0x73aa220400000006,0x73b34ed200000006,0x73b795b045404206].getD (i % 8) 0))) else (if i < 1120 then (if i < 1104 then (if i < 1096 then [0x73e6ee5700000003,0x7454af0f00046108,0x747bdfcf0000000a,0x7482d12400000008,0x74968e6145404206,0x749999a000000004,0x74a0f0b800000004,0x74f7fa9e00000003].getD (i % 8) 0 else [0x74fbba4c15410208,0x751313d000000008,0x7523aeb00000000a,0x7525e10d45005206,0x7531a2a800000000,0x7560503600000006,0x75b167770000000a,0x75c8601f00046108].getD (i % 8) 0) else (if i < 1112 then [0x7622d18000000006,0x767fbaa600048106,0x76d22fcf00000006,0x76df3fd100051100,0x76e4886100091108,0x772a3ac700011108,0x7743e9e200000004,0x775d89ee00051103].getD (i % 8) 0 else [0x7799b34e00000003,0x77b54f520000000a,0x77c799bd00050104,0x787f56dd00000004,0x78a6b77e00048108,0x78cf9ea300010100,0x7903b5b600048106,0x793712f500011104].getD (i % 8) 0)) else (if i < 1136 then (if i < 1128 then [0x794ef06d0000d108,0x799390d80000000a,0x79b844d500000006,0x79bf9a4c45005208,0x79cac1e800000000,0x79cf523200000003,0x79f0dbf600000000,0x7a973d8600000003].getD (i % 8) 0 else [0x7ab2c1cf00000004,0x7b33fcf30000000a,0x7b8010580000000a,0x7be1d03700000006,0x7bf2f44700000004,0x7bfc685d00011103,0x7c6152fc45049208,0x7c6ee7ea00000004].getD (i % 8) 0) else (if i < 1144 then [0x7ca9e0490004d103,0x7cea6cf100000000,0x7d40b16e00000006,0x7d54343200000003,0x7da9886a00000004,0x7dad7d0300000003,0x7db7b80300000004,0x7dd9aab900000004].getD (i % 8) 0 else [0x7df3865a00000006,0x7df9374c0000d106,0x7dfc0eed00091106,0x7dfd426245448206,0x7e116ff600049106,0x7e15013500000008,0x7e4a2be000000003,0x7ebd65a70000d108].getD (i % 8) 0))))

def cutWordDataBlock9 (i : Nat) : Nat := (if i < 1216 then (if i < 1184 then (if i < 1168 then (if i < 1160 then [0x7f1295fe00051103,0x7fa1e45d00000003,0x7faf431400000000,0x8023c56a0000000a,0x8069190700000004,0x8080f9e500049100,0x80a6aad200000003,0x80d6a0d50000000a].getD (i % 8) 0 else [0x80e723d100000000,0x80f08ae800004100,0x80fce83900000000,0x810b041300000004,0x8138912900049103,0x816d896900000004,0x819976c300000004,0x81a0c9bc00000000].getD (i % 8) 0) else (if i < 1176 then [0x81a96b4200000006,0x81ae3a4300009106,0x81c7c3ef05450206,0x81fcae5d0000000a,0x821a56e100011103,0x82355a2300000008,0x823762800008d108,0x827d31d200000004].getD (i % 8) 0 else [0x82bd9b9200000003,0x832cfe9300000004,0x8354a95400000003,0x835c6cfe00011104,0x8381b9f800000003,0x840ce6c900000008,0x840e407f00000006,0x844d357700004100].getD (i % 8) 0)) else (if i < 1200 then (if i < 1192 then [0x845f661c00000004,0x84c4d53c00000003,0x84d5326300000004,0x84f90cdd00000004,0x853ebbee00000003,0x8562891300000003,0x857ff39100000004,0x858de5c500050106].getD (i % 8) 0 else [0x85a5ead800000000,0x8617b55800000004,0x86193f590000000a,0x862372a800000003,0x86253b8a00000008,0x86266cd600000004,0x8644f40200050104,0x867a4e3600000004].getD (i % 8) 0) else (if i < 1208 then [0x86e2c04000000004,0x86fd975e00000000,0x872fafb50000000a,0x87668dec00000003,0x878584c705450208,0x87920b950004d106,0x87a178e100000000,0x87d3bd230000000a].getD (i % 8) 0 else [0x87e0749e00000003,0x87ec7cad000d0106,0x87fb1e920000000a,0x8812b40735490208,0x881c490225051208,0x886ef52945005206,0x8876481000000003,0x88b2fc0f0000000a].getD (i % 8) 0))) else (if i < 1248 then (if i < 1232 then (if i < 1224 then [0x88cd24e700000004,0x88e631570000000a,0x890a209100000003,0x89395ac700000008,0x8a3b9ea800000004,0x8a49607200000008,0x8a572c4600000000,0x8af7cefd00000000].getD (i % 8) 0 else [0x8b10add945049206,0x8b48fff200000004,0x8c057fae00000000,0x8c5c65e500000006,0x8c78f56d00000000,0x8c8fc4ea0000000a,0x8ca9232f00000003,0x8cc30a0400000008].getD (i % 8) 0) else (if i < 1240 then [0x8cc7068d0004d103,0x8d01bb3900000006,0x8d0e0a7c00000000,0x8d25a65d00000008,0x8d6c80f400000003,0x8dbee56f00000006,0x8dfdc37d0004c106,0x8e3a904e00000003].getD (i % 8) 0 else [0x8e4eafac00000004,0x8e5a8a4700000008,0x8ebc116000000000,0x8f30ff8500000000,0x8f3262ea00000004,0x8f5c9c8600010100,0x8faa411f00000004,0x8fc105bc00000006].getD (i % 8) 0)) else (if i < 1264 then (if i < 1256 then [0x8fd9b777000ce106,0x8fef9e4700011106,0x8ff22eae00000004,0x902a1eb400000008,0x9057db6b00000000,0x90e7a30f00000006,0x90e8ffc600000006,0x91d55ab300000003].getD (i % 8) 0 else [0x91de68ae00000003,0x91f8833d05450206,0x922d43a00004d100,0x9233590000000006,0x9239714b00000000,0x926a163800112108,0x926f59fb00051100,0x92a6c4340000000a].getD (i % 8) 0) else (if i < 1272 then [0x92d042b745005208,0x9307b00e00000004,0x930b8fff00000006,0x932183f200000003,0x9366bf0135448206,0x9393695100000004,0x941dfecd00011103,0x945869c20000000a].getD (i % 8) 0 else [0x94589e7600000008,0x947c129d0004d103,0x9487ccbd00000006,0x949bd9ca35490206,0x94b3a8cb0000000a,0x94d23e3545448208,0x94ed2f6100051100,0x9571fb6700050104].getD (i % 8) 0))))

def cutWordDataBlock10 (i : Nat) : Nat := (if i < 1344 then (if i < 1312 then (if i < 1296 then (if i < 1288 then [0x95ae187c00000000,0x96237f9c00000000,0x9661303b00090106,0x9669fbe400000006,0x9692ca4400000004,0x969c79a400000008,0x96cba3df25051206,0x970ea6be00011103].getD (i % 8) 0 else [0x9749175100000008,0x97e6ae7100000004,0x980fa92900000000,0x9835536200000004,0x9840b79700000004,0x988b262200049103,0x98b888b000000003,0x98cfcf6f000ce106].getD (i % 8) 0) else (if i < 1304 then [0x9951f4bf00000003,0x998b6b1a0000000a,0x9996db5e00049100,0x99affe4c0000000a,0x99fbf05a15410208,0x9a1eadf200000003,0x9a62897c00000004,0x9ab0a3ce00000004].getD (i % 8) 0 else [0x9ade424a00000004,0x9af049f000000008,0x9b22314a00004100,0x9b3018310000000a,0x9bb145300000000a,0x9bb5546700000000,0x9c12cf8500000003,0x9c414daf00000004].getD (i % 8) 0)) else (if i < 1328 then (if i < 1320 then [0x9c9260af00000000,0x9ce2bd5900000004,0x9ce9d81700000003,0x9cee6cbd00000004,0x9d064e2000050104,0x9d319ad700000004,0x9d788ee40000000a,0x9d8ab27b00000004].getD (i % 8) 0 else [0x9dbbb2bc00000006,0x9e14b8ae00000000,0x9e2350120004810a,0x9e280dcb00011103,0x9e71a50200000006,0x9e85467700004100,0x9eb622f10000000a,0x9ed05d4600000004].getD (i % 8) 0) else (if i < 1336 then [0x9ee850830000000a,0x9f063c8000000000,0x9f36cf9100000008,0x9f3ab57d0008a106,0x9f6c7a1600000006,0x9f82d6c700000004,0x9fb597c900000004,0x9feff9130000000a].getD (i % 8) 0 else [0x9ff1014e0008d108,0xa02bcd0800000003,0xa0c605ca45049206,0xa0f5d00200000000,0xa1303cf1000d1108,0xa13c766700000000,0xa16f1df805448208,0xa1a615250000000a].getD (i % 8) 0))) else (if i < 1376 then (if i < 1360 then (if i < 1352 then [0xa1a9498d00000000,0xa1cf6ca400050106,0xa1f34f9400000004,0xa21d755700000006,0xa23f0a9000000003,0xa249a3400000000a,0xa27ae45400000004,0xa29197ff00000000].getD (i % 8) 0 else [0xa2c0986400051103,0xa36a4fc800000008,0xa3a2ff2300000003,0xa3af2fcb00011106,0xa426331b00009108,0xa439283a00000000,0xa43b251100000000,0xa4f80a2a00000006].getD (i % 8) 0) else (if i < 1368 then [0xa5104b7a0008d106,0xa577bd2b000d1106,0xa5e0c9bb0008d106,0xa5e8f02f00051100,0xa690efa700000004,0xa691ef8900090106,0xa6ea945200112106,0xa6ff721b05448208].getD (i % 8) 0 else [0xa70f64300000000a,0xa77e32f600000000,0xa84a6c8e15410206,0xa87f3b0100000000,0xa880e04d00000006,0xa8a84c6600049103,0xa8def0cc00011103,0xa911a98200000000].getD (i % 8) 0)) else (if i < 1392 then (if i < 1384 then [0xa95a0c6c00000004,0xa9868b2400000003,0xa9fb1f3600000004,0xaa227f8300051100,0xaa3bbad400048108,0xaa3bd43600000000,0xaa6422d200000003,0xaa8d272300050106].getD (i % 8) 0 else [0xaadadd8500000000,0xaae89ff10000000a,0xaaec340200000004,0xab3857b900000004,0xab68b9880000d106,0xabd2be8000011108,0xabe76e61000ce106,0xabf0312100011103].getD (i % 8) 0) else (if i < 1400 then [0xabf124890000000a,0xabfc46e300000004,0xac61b0a800000000,0xac65925500002106,0xac83d30e00112106,0xad6df0b700000004,0xad7ee21b00000000,0xad9ed00100000004].getD (i % 8) 0 else [0xadb9329c00000006,0xadbe325900051103,0xadc58a2e00011104,0xae07c95800000004,0xae0d00950000000a,0xae93c85400004100,0xae98cb8200000000,0xaea3487200000003].getD (i % 8) 0))))

def cutWordDataBlock11 (i : Nat) : Nat := (if i < 1472 then (if i < 1440 then (if i < 1424 then (if i < 1416 then [0xaea8e7f400000008,0xaeb6e59c00009106,0xaf0628af0000000a,0xaf3ef3c500000003,0xaf4804da00048106,0xafbd9a2c05448206,0xafbefda400000006,0xb01c9be70000000a].getD (i % 8) 0 else [0xb049ffd600000003,0xb05d0f9400005103,0xb05d587600049103,0xb06ba72300000003,0xb093adeb00011104,0xb13e6f1900011104,0xb1ba731b00000003,0xb1c6362945005206].getD (i % 8) 0) else (if i < 1432 then [0xb1f0e04600000003,0xb2133c2c00000003,0xb25474d200000008,0xb255d69a00000000,0xb284515000011108,0xb2b727ce00000000,0xb2e9869e00000000,0xb33f0b7f00000000].getD (i % 8) 0 else [0xb34f8f3d00000004,0xb37084e400051103,0xb37267df00005103,0xb3830f4f00000006,0xb3c7f44a00000004,0xb3f8609600000008,0xb4234a360000000a,0xb45c2bcb00000003].getD (i % 8) 0)) else (if i < 1456 then (if i < 1448 then [0xb478dfb20000000a,0xb49c08450004d103,0xb4c49b7000000003,0xb4d993df00011108,0xb4eea65100000006,0xb50d241a00000008,0xb5210f6c00000003,0xb55b7c1a00000004].getD (i % 8) 0 else [0xb593f5f600000000,0xb5b4eb4500000000,0xb5dbd9f00000000a,0xb6265c8c00000003,0xb627430c00000000,0xb6323d1900009108,0xb643cf5500000004,0xb6a33cc500000006].getD (i % 8) 0) else (if i < 1464 then [0xb6eed75a00000004,0xb75ee52c00000008,0xb75f087405450206,0xb797d4e200000004,0xb7d7572500000004,0xb7efe2ce0008d106,0xb8227ad900000000,0xb87393db00000003].getD (i % 8) 0 else [0xb87add4300011103,0xb87b2bdc15410206,0xb8bad98200000008,0xb8dee0f400000004,0xb8f989df00009108,0xb901ee1a0000d106,0xb9464fb700112106,0xb958750700000004].getD (i % 8) 0))) else (if i < 1504 then (if i < 1488 then (if i < 1480 then [0xb9bdf88700011103,0xb9dc302600000003,0xba633a6600000003,0xba843cad00000000,0xba8c3485000d1106,0xbac8fb1c00000008,0xbaec5d5000000004,0xbc3f24f500010100].getD (i % 8) 0 else [0xbd212b7100000006,0xbd354ae300000000,0xbd47ef6700000004,0xbd47f42f00000000,0xbd709d5c00000003,0xbdc9f73f00011106,0xbe42852400000006,0xbe71363005450206].getD (i % 8) 0) else (if i < 1496 then [0xbf028c8400090108,0xbf12482400000004,0xbf58c74d00000004,0xbf767aa400000008,0xbfbe357200000000,0xbfc457280000000a,0xbfd8146d15091206,0xbfee597a05448206].getD (i % 8) 0 else [0xc01721d100000003,0xc05ba49f00000003,0xc08a1ac100000000,0xc0a5cff400000003,0xc0ef30960000000a,0xc0fab45e45448208,0xc1289acd00000004,0xc17e4bf900000000].getD (i % 8) 0)) else (if i < 1520 then (if i < 1512 then [0xc18968de00000000,0xc1afd95800000000,0xc1dab25700000008,0xc1fbd9610000000a,0xc20e284a00000006,0xc233edcf00000003,0xc294bd7a00000003,0xc2cfdcee00048108].getD (i % 8) 0 else [0xc2f84b3c00112106,0xc326b2f300000008,0xc32e82ea00000000,0xc385d09400000003,0xc397e27c00000003,0xc3b0ddfc00000004,0xc41bbef40000000a,0xc41c8a1a00000004].getD (i % 8) 0) else (if i < 1528 then [0xc440e04a00000004,0xc44b795300000008,0xc455dbfc00009108,0xc46943cf0000000a,0xc472ab0800000000,0xc4cdcb0c0000000a,0xc4fdb53800000004,0xc512ee8500000000].getD (i % 8) 0 else [0xc538cb900000000a,0xc5a4a8f000000004,0xc5ab4aa200000004,0xc5c2540c45448208,0xc5c2b5a90000000a,0xc5e5fa5600000003,0xc5f2e6bf00000003,0xc5f9b4ab00000000].getD (i % 8) 0))))

def cutWordDataBlock12 (i : Nat) : Nat := (if i < 1600 then (if i < 1568 then (if i < 1552 then (if i < 1544 then [0xc5fb182f00000006,0xc600724e00000008,0xc61d00ad35448208,0xc61ef4f945005206,0xc62d277b25051208,0xc677260100000008,0xc73d9b1000004100,0xc74aa77300000003].getD (i % 8) 0 else [0xc764629300000000,0xc7837e5f0000000a,0xc7dd8cbc00000004,0xc806ebfc00049103,0xc8295fa500000008,0xc85f272200000000,0xc873b94200011103,0xc8c0ada945049206].getD (i % 8) 0) else (if i < 1560 then [0xc929943b0008d106,0xc93a5e1500000006,0xc963388100000003,0xc971148c00000004,0xc98015da00000004,0xc9e647f200002106,0xca2ab3830000000a,0xca4efc550000000a].getD (i % 8) 0 else [0xcae028ee35490206,0xcaf8c2b80000000a,0xcb139daa00000000,0xcb3a3f3400051103,0xcb7148bf00000003,0xcbf874c000090106,0xcc12472125005208,0xcc6489b10000000a].getD (i % 8) 0)) else (if i < 1584 then (if i < 1576 then [0xcc6d588e00000006,0xcc7da9e900000008,0xccabf92e00000004,0xccc2db9600000004,0xcccd878300000008,0xccfc0d000000000a,0xcd534030000d1106,0xcd973e2d00051103].getD (i % 8) 0 else [0xce29d8e500000004,0xce4fb38000000003,0xce592f0000000004,0xceac533d00000004,0xcebf196600000006,0xcf4542ff0000000a,0xcf532b7d00009106,0xcf60185e00000004].getD (i % 8) 0) else (if i < 1592 then [0xcf8473b800051103,0xcf8c965f0000000a,0xcf8e678e00000000,0xcfd5a06100000000,0xd03b31630000000a,0xd03b954200000004,0xd05ca5820000000a,0xd085fb310000000a].getD (i % 8) 0 else [0xd08e588800000000,0xd09c385e00000008,0xd0c78efc00051103,0xd11393ea00010100,0xd14175ae00051103,0xd146de6600000000,0xd169330400090106,0xd16d85d300005104].getD (i % 8) 0))) else (if i < 1632 then (if i < 1616 then (if i < 1608 then [0xd1ba609e000ce106,0xd1dbf36900000004,0xd272dd3600000003,0xd275116f00000004,0xd2803bed00010100,0xd28d2a7800000004,0xd2b16c0600000004,0xd2e4216600091108].getD (i % 8) 0 else [0xd2ed927a00000004,0xd2ff865800000004,0xd32f95ee00050108,0xd34aebfb0000000a,0xd371533700011103,0xd3e160d90000000a,0xd3e50e0f0008d106,0xd3f2238b45005208].getD (i % 8) 0) else (if i < 1624 then [0xd41845320000000a,0xd471aee945448206,0xd47ba3af25051206,0xd48e35cd00000004,0xd48fa93400000003,0xd55406a100112106,0xd59da7ae00000006,0xd5d466cd00000003].getD (i % 8) 0 else [0xd614e25700000003,0xd65bb0e600000003,0xd66430fd00048108,0xd692176c00000004,0xd6a9e77000000003,0xd6e678e000011103,0xd6ea788200000004,0xd6ffd77900000004].getD (i % 8) 0)) else (if i < 1648 then (if i < 1640 then [0xd705054500000004,0xd717821100000003,0xd71a46ab00000008,0xd71e32aa00000000,0xd7b2ff9500000008,0xd7c9cf2500000000,0xd86295300000000a,0xd885a45300000000].getD (i % 8) 0 else [0xd886469e00000004,0xd889baa80000000a,0xd8a09dbf00000004,0xd8fcef5f00000000,0xd902b01b0000000a,0xd90728c80000000a,0xd93d3af700091106,0xd971e9c900000003].getD (i % 8) 0) else (if i < 1656 then [0xd985726700000004,0xd99f872545049208,0xd9d77f4a00000004,0xda3c0dc800000006,0xda3db22300000000,0xdac1a1fe25005206,0xdb2bd0ab00048108,0xdbe0080300091106].getD (i % 8) 0 else [0xdc4e8ed70000000a,0xdc62a3a200000000,0xdc81c98b00000008,0xdca7d96f00000004,0xdd4af5c000011104,0xdd51e16200000003,0xdd81a2cd00000003,0xddaf307e0000000a].getD (i % 8) 0))))

def cutWordDataBlock13 (i : Nat) : Nat := (if i < 1728 then (if i < 1696 then (if i < 1680 then (if i < 1672 then [0xde07bdae00000000,0xde17b3e20000d106,0xde58429a00000006,0xde9a735d0000000a,0xded2fc7700000004,0xdf09f32900000004,0xdffce80d0000000a,0xe059098f0000000a].getD (i % 8) 0 else [0xe0dd546a00000004,0xe0edd82400000003,0xe13e5b5200000004,0xe189e61400000000,0xe18ca0d400011106,0xe1b524c100090108,0xe278414c00091108,0xe30d53fb0000000a].getD (i % 8) 0) else (if i < 1688 then [0xe31958ee00000000,0xe35b5f8000091108,0xe375b0d000000004,0xe3b25f400000000a,0xe3c99b1000000003,0xe3e951d000000008,0xe44d0d4f00049103,0xe49e688a00011103].getD (i % 8) 0 else [0xe4ac62fd25051206,0xe4edf0570004d103,0xe4f3721800000003,0xe51839ee00000004,0xe554deb105448206,0xe561529200000000,0xe57ecb760008a106,0xe58bca7d0000000a].getD (i % 8) 0)) else (if i < 1712 then (if i < 1704 then [0xe5a1111a00005104,0xe5af0cab0000000a,0xe5b33c9e00000004,0xe5c0764000000004,0xe601e5b500048106,0xe618a3b000000006,0xe622ac4600091108,0xe6310b9b0004d103].getD (i % 8) 0 else [0xe642c55600000000,0xe6770d5c00050104,0xe688fa9b0004d103,0xe6aaf24d0004d103,0xe6ec277e00000000,0xe7039f2400011103,0xe70ea51600000000,0xe72ebad00000000a].getD (i % 8) 0) else (if i < 1720 then [0xe753657100000004,0xe757dc740000000a,0xe7ae971e00000000,0xe7cee0a000000003,0xe81451a600000004,0xe843210200000008,0xe8ab036900011103,0xe8aedfc100000003].getD (i % 8) 0 else [0xe8d0b36500000000,0xe8d40c5500050104,0xe8de62c300000004,0xe942344500011103,0xe960f71a000d1106,0xe985d33b00000000,0xe9db2b8835448206,0xea258a8a00000000].getD (i % 8) 0))) else (if i < 1760 then (if i < 1744 then (if i < 1736 then [0xea46ad090000000a,0xea4b202500000004,0xea77ff470000000a,0xeade106800000000,0xeae438eb00000003,0xeaebec6e00000000,0xeafc592400000004,0xeb00ad3d00000003].getD (i % 8) 0 else [0xeb29e0e8000d1106,0xeb4dc86500000000,0xeb715f5e00000006,0xeb7fe52c0000000a,0xebb2240e00005104,0xebc0bb9d00000003,0xebd9f82d00000003,0xebf55a3b00000000].getD (i % 8) 0) else (if i < 1752 then [0xec2a82b100004108,0xec6e81e400000004,0xec7a715700000006,0xec8ac1240000000a,0xec9c089000000003,0xecbab6f300000000,0xece8dfc700000004,0xecf907a500000008].getD (i % 8) 0 else [0xecfb133000000008,0xed37ac2700000003,0xeda3579805450206,0xedd84f8145404208,0xedea9fbe00000004,0xedf2402e00000004,0xee0635f045404206,0xee20f48e00000004].getD (i % 8) 0)) else (if i < 1776 then (if i < 1768 then [0xee92b1df00000004,0xeeb8ab3400011103,0xeeb8fae800048106,0xef2e55d800000004,0xef5ffca000000000,0xef6de39a00000006,0xef7fd65700000004,0xefe1ecaf0008d108].getD (i % 8) 0 else [0xf02639af00000000,0xf033aa6800011108,0xf0459c9700000000,0xf04b4a4b00000006,0xf05a59460000000a,0xf06793dc000d1106,0xf0debf8d00000000,0xf16a02b100000004].getD (i % 8) 0) else (if i < 1784 then [0xf19458a10000000a,0xf1c713dd0000000a,0xf22347080000000a,0xf235619d00000008,0xf24576d635448208,0xf251c70a00000003,0xf27195c000000006,0xf2735d4500000004].getD (i % 8) 0 else [0xf28b742100000006,0xf29fef2f45404208,0xf2bb661800000000,0xf331f6c60000000a,0xf333e93b00000004,0xf397fdcf00000006,0xf39e94fb00000008,0xf3a2280e00000003].getD (i % 8) 0))))

def cutWordDataBlock14 (i : Nat) : Nat := (if i < 1856 then (if i < 1824 then (if i < 1808 then (if i < 1800 then [0xf3a24ef800000000,0xf3d8fea600000003,0xf40c4fde00011104,0xf412df9100000000,0xf42d47670000d108,0xf431380a00000004,0xf43c791600000004,0xf488623f00000000].getD (i % 8) 0 else [0xf4b7e3a700000006,0xf4d8b17400051103,0xf54c1b5400000006,0xf586b03d00000008,0xf5a4137100000004,0xf5ee52410000000a,0xf5f7396f00000000,0xf60e1aa50000000a].getD (i % 8) 0) else (if i < 1816 then [0xf68e799600004106,0xf6c7f25500000003,0xf70d168435448208,0xf715968900000004,0xf73f608400000000,0xf7ad52e900000008,0xf7b424c20008d106,0xf7e7a31500000008].getD (i % 8) 0 else [0xf84bcb8c0000000a,0xf9c17a0400000006,0xfa89116400000000,0xfaa69abf00000006,0xfb0938d900000003,0xfb0a7af10000000a,0xfb1eebad00000003,0xfb5932aa00004100].getD (i % 8) 0)) else (if i < 1840 then (if i < 1832 then [0xfb8b915600000008,0xfbb6397e00000003,0xfbd0b2f500000004,0xfc2e798b0004c106,0xfc3239fb00000006,0xfc620edb00011103,0xfc7c244300051103,0xfca2686e0000000a].getD (i % 8) 0 else [0xfcf0688900000006,0xfd1eae930008a106,0xfd47a7d300000000,0xfd4c543000000000,0xfd5a89f000005103,0xfd69217f00000003,0xfd88007e00000003,0xfd8ae3110000000a].getD (i % 8) 0) else (if i < 1848 then [0xfda52a1f00011103,0xfda8ee670000d106,0xfdb76a910000000a,0xfdfe6bd500000000,0xfe1f10d100011103,0xfe47df6200000004,0xfe57f22e00000003,0xfee019550000000a].getD (i % 8) 0 else [0xff23389a00000000,0xff63c99300000004,0xff6b776f00000008,0xffc917e300000008,0x4fdaf40000000a,0xb74bbc00000003,0xd197600000000a,0xeed28e00000008].getD (i % 8) 0))) else (if i < 1888 then (if i < 1872 then (if i < 1864 then [0x258a16d00010106,0x262be0000000003,0x289f7100008a108,0x30376090000d108,0x340269700000000,0x3a5d94400000003,0x4094b3d00000004,0x41fbff600000003].getD (i % 8) 0 else [0x45e5f2200000008,0x48b675300000003,0x61582f700000003,0x643696600000006,0x6bcb35400000004,0x6ca9f9800046106,0x71d65d400000000,0x74ff93100000006].getD (i % 8) 0) else (if i < 1880 then [0x7589e3b00000003,0x767748200000004,0x78684aa0004d106,0x7a3b0c0000d1108,0x7d284ed00000003,0x8006b5c00000004,0x8087f0f0000d106,0x825c5f100050108].getD (i % 8) 0 else [0x82c74f30000000a,0x8cc51d400000008,0x8ce972b00000004,0x9dbf87500000004,0xa04ddbe00000003,0xa0a327900000000,0xa353b6c00090106,0xa75432900000003].getD (i % 8) 0)) else (if i < 1904 then (if i < 1896 then [0xa9ff0f70000000a,0xadd22a50004d108,0xb5048c400000000,0xb51aa430000d108,0xb8a792e00000000,0xbf512f200112106,0xc203de900000008,0xc33f09900000006].getD (i % 8) 0 else [0xc4f846a00000000,0xc9a249b00049108,0xcb116770008d106,0xcc595b500000006,0xce8c45100000000,0xd4d405e00000000,0xd6bd43f00000008,0xd9e026a0008a106].getD (i % 8) 0) else (if i < 1912 then [0xda05b9500000003,0xdc87da40000000a,0xdd9330a00000003,0xdfaccad0000000a,0xe10107900000004,0xe200f0900112106,0xe4b804200000000,0xe9f2cec00000008].getD (i % 8) 0 else [0xf4652d600005106,0xf8b31b800000004,0xfb2999700000000,0xfde230d00000008,0xffc57aa0008a108,0x108ed05c00000006,0x10a9eaed00000000,0x10c955a800000000].getD (i % 8) 0))))

def cutWordDataBlock15 (i : Nat) : Nat := (if i < 1984 then (if i < 1952 then (if i < 1936 then (if i < 1928 then [0x116e9b3500004106,0x119ee0c800008108,0x11a50d0100000003,0x11af170c00000006,0x11b146bf00000004,0x11b2d0e600000006,0x11eb3e7500112106,0x12127cb800011106].getD (i % 8) 0 else [0x1269cc9d00000008,0x128960bb00010106,0x12e74be700048106,0x12fe530a00000006,0x130e1bb100000003,0x1320960000000004,0x1366cc9a00000008,0x13a897ea00000000].getD (i % 8) 0) else (if i < 1944 then [0x13de834e00000008,0x152daa4100000004,0x1595922a00002108,0x15e25d9500000003,0x165c444700000003,0x16fb5ee600046106,0x1720c0f50008a106,0x173b246400000000].getD (i % 8) 0 else [0x179f5f8b00000003,0x1804e3de00000003,0x188bacb200000000,0x18b2b2a60000000a,0x18bd51c100000006,0x18ff14c900000003,0x198c7d8200000006,0x19ce1de000000004].getD (i % 8) 0)) else (if i < 1968 then (if i < 1960 then [0x1a34246300000000,0x1a4abb4e000ce106,0x1a65faba00090106,0x1aad4bfe00000003,0x1ac8df4200002106,0x1acf98c60004d106,0x1b497f7800049106,0x1b7d0cf400000004].getD (i % 8) 0 else [0x1bbcad0b00000006,0x1c141e740000d108,0x1ca0257500046108,0x1ce1d5c50008d106,0x1d1f961200000004,0x1dfe640500000003,0x1e4ad3de0008a106,0x1e50ce5700112106].getD (i % 8) 0) else (if i < 1976 then [0x1e78d69000000000,0x1e9cbeab00000003,0x1f47006f0000000a,0x1f49cf0b00000003,0x1f6f72020008d108,0x1f9d587100000004,0x1fdcdfe600000003,0x1fe0e4d000000000].getD (i % 8) 0 else [0x1fed5cfc00008106,0x2050654c00000004,0x211ffb2a00000003,0x2137853700000008,0x2216277700000006,0x222cff82000d1106,0x22a3aafe00091106,0x235b4b6900000006].getD (i % 8) 0))) else (if i < 2016 then (if i < 2000 then (if i < 1992 then [0x23edcb100004d108,0x243711b00008d108,0x2446f9da00112106,0x2473c23e00000006,0x248fb1c900000003,0x2530e65400000008,0x25aacd0600000004,0x25e024d000000008].getD (i % 8) 0 else [0x25fea5ca00000000,0x261f84c000000006,0x263a3eb300000008,0x2658435b00000004,0x268de1240000000a,0x269abf1600000008,0x27239a6e00000004,0x272f391a00000000].getD (i % 8) 0) else (if i < 2008 then [0x277ee6c000000000,0x27b3955400000006,0x299a58a000000003,0x2ae1fbed00000000,0x2aeea1a900046106,0x2b5ad02e00000003,0x2b7ca04c00000008,0x2ca3e6ce000d1108].getD (i % 8) 0 else [0x2cfffe980000000a,0x2ddfb31a00000003,0x2df9315c00000006,0x2e17b8d600011108,0x2e70287900000003,0x2e79a9f50000000a,0x2e7b932c0008a106,0x2f4cab2b00000003].getD (i % 8) 0)) else (if i < 2032 then (if i < 2024 then [0x301e1c4a00008106,0x309b77230000000a,0x30f60ba100000003,0x31196d4400009106,0x315b982900112106,0x325dbed0000d1106,0x326ebc5300000003,0x32e66c8d00000006].getD (i % 8) 0 else [0x33430d0700000000,0x3373fb2900000004,0x3374098800000003,0x339f700300000000,0x344e3c1a00050108,0x3468a1cd00000006,0x347c228900050106,0x34acd80d00000003].getD (i % 8) 0) else (if i < 2040 then [0x36b17ccd00000008,0x376a02ab00000008,0x37efe5f200010106,0x3826ff3b00000004,0x3833049100000003,0x3877fa9300009108,0x38834d3700000008,0x38a5e10200000004].getD (i % 8) 0 else [0x3915dbc800050108,0x3978a6d100091108,0x397f55d300000004,0x39b96b9100000004,0x39d5bb2300000004,0x3af2630200000006,0x3b1f60f700046106,0x3b3932e000000004].getD (i % 8) 0))))

def cutWordDataBlock16 (i : Nat) : Nat := (if i < 2112 then (if i < 2080 then (if i < 2064 then (if i < 2056 then [0x3b646c4800000008,0x3c28e5ef00000003,0x3c61e41d00000003,0x3cadf4fc00000008,0x3cdbbbfe00000004,0x3d3f9a4100009108,0x3d47ba1b00000004,0x3dd61bf100000000].getD (i % 8) 0 else [0x3e65d3840000000a,0x3ed408d200000003,0x3ee0fe0800000004,0x3f46c06800000000,0x3fcc7ff100090106,0x411331e500000000,0x411454820000d108,0x415f52af00000003].getD (i % 8) 0) else (if i < 2072 then [0x42485afc0008d106,0x428be29700000003,0x42d7fb7400000003,0x42e7b73100000000,0x431fbb1800000003,0x433c426300000004,0x43b7538e00112106,0x43e2518e0008a106].getD (i % 8) 0 else [0x441b16b800000003,0x44563fca00000000,0x4494fd6a00000003,0x44fa214d00000000,0x44fff90100000006,0x45b87edf0000d106,0x462614e100000006,0x4640467e00000004].getD (i % 8) 0)) else (if i < 2096 then (if i < 2088 then [0x46c2ac9c00000003,0x4792a3480000000a,0x47b2ea5900000000,0x47c536a500050106,0x4856cbdc00000000,0x486240fe00000004,0x48c83df500000003,0x48ce0d0900000004].getD (i % 8) 0 else [0x48dc392000000004,0x48ee011e0004d108,0x492b9b0b00048106,0x492e70db0000000a,0x4a311c6200000008,0x4a35554700000004,0x4a40eea700000003,0x4aab031400049108].getD (i % 8) 0) else (if i < 2104 then [0x4b23225000000006,0x4b3d9da000000008,0x4beef51e00009106,0x4c1757aa0000000a,0x4c8c48f400000000,0x4cd6bb4c0000000a,0x4d22885900000006,0x4dab8a7b00000004].getD (i % 8) 0 else [0x4db083d700000000,0x4e04f9a600000004,0x4ed28de50000000a,0x4f5b4d000000000a,0x4f62d0b600000006,0x4fe7572c00000004,0x4ff497f200000000,0x5015dd1000000004].getD (i % 8) 0))) else (if i < 2144 then (if i < 2128 then (if i < 2120 then [0x5027658600000004,0x506979cc00000006,0x5080e32c00000006,0x508f0a72000ce106,0x50a77b4300000003,0x50ad1dd000000000,0x50e0555300000008,0x50e308950000000a].getD (i % 8) 0 else [0x510d2e6600000000,0x5200014300000006,0x5226843300050108,0x5242e41500000006,0x53a75ce900002108,0x53d5435800002106,0x53e218630008a106,0x5434487900000003].getD (i % 8) 0) else (if i < 2136 then [0x547d1efa00009108,0x5530b84f00000006,0x5584a18100008106,0x5597fdc800000004,0x55e66fda00000008,0x55e93e2d0000d106,0x562bb85e00000003,0x563a3d4700000003].getD (i % 8) 0 else [0x565042ac00000004,0x570dbec700000000,0x573c7d5200000006,0x5755dcb200000000,0x5777565e0000000a,0x578ad4ed00000008,0x57ae948600000003,0x57c44407000d1106].getD (i % 8) 0)) else (if i < 2160 then (if i < 2152 then [0x5800d10a0000000a,0x586efc9700002108,0x587f98960004d106,0x58f97f4800049106,0x59d935b500000000,0x5a576fa700000000,0x5ab74d610008a108,0x5ad400ed00051106].getD (i % 8) 0 else [0x5b26e3d200000006,0x5b8a2c400000000a,0x5be9548900000003,0x5c352fd60000000a,0x5c87cfec00000000,0x5d64d6ee00000004,0x5d7eddb500000006,0x5d9cebac00000004].getD (i % 8) 0) else (if i < 2168 then [0x5e1a628e00000004,0x5e87e62c00000000,0x5ec125f900091108,0x5ee97a420000000a,0x5f24df5000112108,0x5f2bc7af00000000,0x5f53f05d0000000a,0x5f93900400000006].getD (i % 8) 0 else [0x5fa2277e00000000,0x600096de00048108,0x606e90b400000004,0x6085e62e00046106,0x618388d500000008,0x618b32f20000000a,0x61c122ed00000004,0x61eafb5900000000].getD (i % 8) 0))))

def cutWordDataBlock17 (i : Nat) : Nat := (if i < 2240 then (if i < 2208 then (if i < 2192 then (if i < 2184 then [0x6247f0290008d108,0x628edcdc00000000,0x630ae1170000000a,0x63482db10000000a,0x6363ac0b00000004,0x64433cbe0000000a,0x648c0a07000ce108,0x653733f600000000].getD (i % 8) 0 else [0x65a11cfa00091108,0x65cf036900000004,0x66cd80cf0000000a,0x66e0f68a0000000a,0x671e577400002106,0x676d3ca000000006,0x67947ca200000000,0x679f1aa900000004].getD (i % 8) 0) else (if i < 2200 then [0x679fe74d00112106,0x67e22a3900000000,0x6828d2c800050106,0x68b057e40004d106,0x692a3e9600049106,0x69a5b8d300000006,0x6a17e9af00000006,0x6a68bca800091108].getD (i % 8) 0 else [0x6add38d900000004,0x6af1273100000000,0x6b017a6700000004,0x6b2e341b00000003,0x6b3d3a550000000a,0x6b453f6600000000,0x6ba81acd00000003,0x6c067acd00000003].getD (i % 8) 0)) else (if i < 2224 then (if i < 2216 then [0x6c1fd6bd0000000a,0x6c5620db00000003,0x6c8c374b00000004,0x6cb7229400000000,0x6d06bdf800000008,0x6d6342110000000a,0x6e34351600000000,0x6ea12cd400000000].getD (i % 8) 0 else [0x6f36a9f300000003,0x6f83322c00000008,0x6fde6e9900000003,0x7089a78700000006,0x70966c5d00000006,0x709b7d5800000004,0x70b4d7bb00000003,0x717fa50200002108].getD (i % 8) 0) else (if i < 2232 then [0x71809ab500112108,0x71a8fcc000051108,0x72a6334100046106,0x72b424860000000a,0x735bacc400000003,0x73b34ed200000006,0x745a8df200000008,0x746bd4b000000008].getD (i % 8) 0 else [0x7531a2a800000000,0x7563f06e00000008,0x7584b93900000003,0x75a3e9160000000a,0x7610cf1500090106,0x769ef8230000000a,0x7726ba4100050108,0x776613c900000008].getD (i % 8) 0))) else (if i < 2272 then (if i < 2256 then (if i < 2248 then [0x7793fa3800000006,0x78584a8a00000003,0x788caa200008d106,0x7918178500091106,0x793cb1ef0000000a,0x799390d80000000a,0x79fba2b200112106,0x7a973d8600000006].getD (i % 8) 0 else [0x7af22c2400000006,0x7b4fc3640000d106,0x7b5078ba00009108,0x7c2db37700000008,0x7cdd9be000000004,0x7d0c999000000004,0x7d98f5ba0000000a,0x7dad7d0300000003].getD (i % 8) 0) else (if i < 2264 then [0x7de602c500000000,0x7e16268700000006,0x7e395f6a00000000,0x7e47c8e800000003,0x7e74e32000112108,0x7e7b92220000000a,0x7f69db2f0000000a,0x7faf431400000000].getD (i % 8) 0 else [0x800d569a00000003,0x8069190700000004,0x80c72bab00000006,0x80fce83900000000,0x810b041300000004,0x8176755e00000003,0x81c6230400000000,0x82f15c0c00000003].getD (i % 8) 0)) else (if i < 2288 then (if i < 2280 then [0x82f4253a00000006,0x8379651300000004,0x83a6f6b500000004,0x84179ad30000000a,0x8419fc1100000006,0x84fa153b00000006,0x850930e900000000,0x8529383100000000].getD (i % 8) 0 else [0x855d64c60000000a,0x8575367500050106,0x85efd32300000006,0x86dfc38a0008a108,0x86e2c04000000004,0x86fd975e00000000,0x870da9f900000004,0x8732ee6700000008].getD (i % 8) 0) else (if i < 2296 then [0x874a55a500000003,0x87b61d3c00000000,0x87bff17a00000000,0x87e0749e00000003,0x87e3a65f00000004,0x8861f06a000d1106,0x886c461600000000,0x8876481000000004].getD (i % 8) 0 else [0x890a209100000003,0x897b2f1400046108,0x899ef4ee00009106,0x8a2667870008a106,0x8aabe89c0000000a,0x8ab05c5500004108,0x8add0e5400000006,0x8ade42c400004106].getD (i % 8) 0))))

def cutWordDataBlock18 (i : Nat) : Nat := (if i < 2368 then (if i < 2336 then (if i < 2320 then (if i < 2312 then [0x8b543dd800011108,0x8b82244700011106,0x8ba763380008a108,0x8bc8f0a500000000,0x8c290d0700048108,0x8c56f37600000004,0x8c8cf16600000004,0x8cd3c1d700000003].getD (i % 8) 0 else [0x8ce5cae800090108,0x8d01bb3900000006,0x8d19fc310008d108,0x8d26cbd500000006,0x8e08932b000d1106,0x8e16dd1b00000003,0x8e3a904e00000003,0x8e90c3cd00000003].getD (i % 8) 0) else (if i < 2328 then [0x8ea656f700000004,0x8f3262ea00000004,0x8f61a5f300000008,0x8f77fc0300004108,0x8fd9b77700000008,0x901bdd8600011108,0x902a7cde00000003,0x9048e01500000004].getD (i % 8) 0 else [0x90714b6d00000003,0x907a22ec00000003,0x90923d5500000008,0x90a24f4000000000,0x90b48030000ce108,0x90d09e8500112108,0x90f0acb500048108,0x9122320200000004].getD (i % 8) 0)) else (if i < 2352 then (if i < 2344 then [0x913cb93600011106,0x91606f1300000000,0x91d55ab300000003,0x926a16380000000a,0x9288829b0000000a,0x92c4bb2000000004,0x9313f85000000003,0x931e4e3c00000008].getD (i % 8) 0 else [0x9324e48800000006,0x93ba62dd000ce106,0x940aa06200002108,0x943886d100002106,0x9476db1600000000,0x949393df00000000,0x94f5c41600000006,0x94f9797d00000000].getD (i % 8) 0) else (if i < 2360 then [0x95045da600000008,0x952369bd00091106,0x953e5be200000008,0x957c1fde000ce108,0x95a5f5c300050106,0x965bad4e00050108,0x967fdb1000002108,0x9694fca00000000a].getD (i % 8) 0 else [0x969c79a400000008,0x96ca355200046106,0x9730206a00000003,0x97370f5600000003,0x976492ee00000006,0x97677be900000003,0x9771024000000000,0x98d2401000002108].getD (i % 8) 0))) else (if i < 2400 then (if i < 2384 then (if i < 2376 then [0x992798ad00000000,0x993a1baf00000003,0x99cfb43c00009106,0x9a1eadf200000003,0x9a28780b00000006,0x9a3c792e00000000,0x9a56be150008a106,0x9a7d36f300000003].getD (i % 8) 0 else [0x9ab2cc6100000003,0x9ae0fde90000d106,0x9af71da500000003,0x9b3f0f1e00000008,0x9b82e32400000008,0x9bf5e7a500000003,0x9c6fce5700000003,0x9cb3da5b00000003].getD (i % 8) 0) else (if i < 2392 then [0x9cc8125400000000,0x9cdcfe530000000a,0x9d03a6d800000003,0x9d7c080d00000004,0x9dd172e900000003,0x9df4c38300000000,0x9dff595800051106,0x9e2756e000004106].getD (i % 8) 0 else [0x9e91b75e00000003,0x9ecb386300011106,0x9f3e3f8a00000006,0x9f49c22e00000006,0x9f7663510008d106,0x9fa0079200048106,0xa040f8e700000003,0xa0e718a600000000].getD (i % 8) 0)) else (if i < 2416 then (if i < 2408 then [0xa0fb635a0008a108,0xa13c766700000000,0xa1a9498d00000000,0xa26395770000000a,0xa299129700051108,0xa29dec7800000000,0xa2b87ebb00000003,0xa359570c00000008].getD (i % 8) 0 else [0xa3714c1c0000000a,0xa3a2ff230000000a,0xa3c950dd00000008,0xa411df0400000003,0xa439283a00000000,0xa45e788700000004,0xa4b80ba300000004,0xa4ce574400002106].getD (i % 8) 0) else (if i < 2424 then [0xa4dd8efe00000008,0xa5cee0fa00000003,0xa62db0e200000006,0xa6cdf6ab00000006,0xa6ea94520000000a,0xa7819aed00002106,0xa7db401900000004,0xa86084ad00000008].getD (i % 8) 0 else [0xa87563ab00000003,0xa8799b2100091108,0xa888a46e00004108,0xa8f0b8050000000a,0xa92c85f100011108,0xa986701f00000004,0xa9bac5be00000000,0xaa01552000000004].getD (i % 8) 0))))

def cutWordDataBlock19 (i : Nat) : Nat := (if i < 2496 then (if i < 2464 then (if i < 2448 then (if i < 2440 then [0xaa2e2dfc00000006,0xaa3bd43600000003,0xaa7ff59900000000,0xaa8b7a4400000003,0xaa9d594900112108,0xaacb3fb800112106,0xab179c7100000008,0xab34e9e900000006].getD (i % 8) 0 else [0xab4de61b0000000a,0xab6a6fe500000003,0xac5b324300000003,0xac83d30e0000000a,0xacd28d7f00000000,0xacd4e2c400000004,0xad1a660d00000000,0xad7ee21b00000000].getD (i % 8) 0) else (if i < 2456 then [0xad9e4d8700000003,0xad9f312500046108,0xadee992d00000003,0xae18343900000003,0xae1c7f9c00005106,0xae3767f900000000,0xae8cc849000ce108,0xae98cb8200000000].getD (i % 8) 0 else [0xaea0ec2800000000,0xaf64f8f700112108,0xb01c9be70000000a,0xb04f416f00000000,0xb0db8caa00000000,0xb0f7c3e800000006,0xb131a71200010108,0xb137e59e00000006].getD (i % 8) 0)) else (if i < 2480 then (if i < 2472 then [0xb1486d7400051106,0xb15f8d8100010106,0xb194128800000000,0xb1e2e87b00002108,0xb1f0e04600000003,0xb2b638db00005108,0xb2d04d4400000004,0xb2d0a5c200000004].getD (i % 8) 0 else [0xb40cbb6c00000004,0xb478dfb20000000a,0xb4ff169200002106,0xb5210f6c00000003,0xb55b7c1a00000004,0xb5a3a53d00000003,0xb5b4eb4500000000,0xb5d18bac00046106].getD (i % 8) 0) else (if i < 2488 then [0xb5f946c000010108,0xb675ac8b00000003,0xb6c8175500091106,0xb7229eb800000003,0xb7d7572500000008,0xb7e1b9d000000000,0xb88fdd0300000008,0xb8982e9500000006].getD (i % 8) 0 else [0xb8be1ced000d1108,0xb90e411100090108,0xb93c278000000004,0xba3e91f000000008,0xba633a6600000004,0xba6b44eb00046108,0xbb0c7afa00050106,0xbb3e645f00000000].getD (i % 8) 0))) else (if i < 2528 then (if i < 2512 then (if i < 2504 then [0xbb5574b800000004,0xbb8a1c1c00000008,0xbba9bb0200051108,0xbbb8028b00000004,0xbc78588700000003,0xbcc59e6700000000,0xbcf914ae00112108,0xbd26fb1d00112106].getD (i % 8) 0 else [0xbd27949700000008,0xbd354ae300000000,0xbd6b49ef00000000,0xbda2f27e000d1108,0xbdbb73cb00000003,0xbdd5e0bf00090108,0xbe1453d400112106,0xbe355a7d00000003].getD (i % 8) 0) else (if i < 2520 then [0xbea851bc00000004,0xbebaf11c00000004,0xbf028c840000000a,0xbf36397300009106,0xbf52a71500000003,0xbf92f1ce0000000a,0xc051bbca00000008,0xc093d06800000004].getD (i % 8) 0 else [0xc0a5cff400000004,0xc0b41b1000000008,0xc16593b800005106,0xc1c0b45c00112108,0xc29bfb1900000000,0xc2cbb2ec00000008,0xc31810fb00000006,0xc3f192fc00000003].getD (i % 8) 0)) else (if i < 2544 then (if i < 2536 then [0xc42d649700000003,0xc4322e6100000006,0xc45b2c3f0004d106,0xc464faf800000003,0xc4760e4000000000,0xc4a8a19d00010106,0xc4d512f100049106,0xc5707fdb00000003].getD (i % 8) 0 else [0xc5e5fa5600000004,0xc5ea668d00000003,0xc6498b2000000003,0xc6f8d6a300091106,0xc757aefb00000004,0xc75bedb500000003,0xc75d93bd00000003,0xc775b69200000006].getD (i % 8) 0) else (if i < 2552 then [0xc7b0887d00000000,0xc7bbe76c00000003,0xc816b6550000000a,0xc8690e5b00000000,0xc875a16200112108,0xc88d0e2400000006,0xc8e3219a00000000,0xc91a9fc800046106].getD (i % 8) 0 else [0xc955026100000004,0xc9550c8900000003,0xc963388100000003,0xc96e839e00000000,0xc971148c00000004,0xc9b841b10008a108,0xca2ab3830000000a,0xcb139daa00000000].getD (i % 8) 0))))

def cutWordDataBlock20 (i : Nat) : Nat := (if i < 2624 then (if i < 2592 then (if i < 2576 then (if i < 2568 then [0xcb56f6ba00000008,0xcb9c934b00000000,0xcba428ae00000000,0xcbc6e14600005108,0xcbcc238800000000,0xcc853b9c00090106,0xccdc800700000004,0xcd1543fd00000004].getD (i % 8) 0 else [0xcd23d9830008a108,0xcd51bff200000004,0xcd53403000000008,0xcd88da7c00004108,0xcde2d9fb00000003,0xce0bc60e00000008,0xce2cbbff00011108,0xcec662a100008108].getD (i % 8) 0) else (if i < 2584 then [0xcecd61c300000003,0xcef4491000000004,0xcf0116a70008d106,0xcf018b2e00048108,0xcf09ef2b00010108,0xcf60185e00000004,0xcf8e71f600000003,0xd03b95420000000a].getD (i % 8) 0 else [0xd0700f3900112106,0xd106052700000008,0xd133eb96000d1106,0xd1eb79310008a108,0xd213603200000000,0xd28d2a7800000004,0xd2ded08c00000006,0xd2e2544500000003].getD (i % 8) 0)) else (if i < 2608 then (if i < 2600 then [0xd3539a6500000008,0xd37bed5600046108,0xd380c2ad00000004,0xd38cfe57000ce108,0xd38e024f00008108,0xd3c8614400000004,0xd493ccd000000000,0xd4d5840f00000003].getD (i % 8) 0 else [0xd5324eb100000000,0xd576755f00000000,0xd5cda4d500000008,0xd65bb0e600000003,0xd6e31e8900002108,0xd6e6892a00000004,0xd71e32aa00000000,0xd7c545db00000006].getD (i % 8) 0) else (if i < 2616 then [0xd7d08b6400000000,0xd806bde50008a106,0xd8bdcd7200000006,0xd959427800000006,0xd962643500000004,0xd985726700000004,0xd9c7a74e00046108,0xd9ed0cce0004d108].getD (i % 8) 0 else [0xd9f58dbd00046106,0xda659bc900002106,0xda93eb6600000003,0xdad15cc700112108,0xdae6106800000000,0xdb30281200000008,0xdb3b870100000003,0xdbaa0ec400049108].getD (i % 8) 0))) else (if i < 2656 then (if i < 2640 then (if i < 2632 then [0xdbd756b000004106,0xdc72000600000006,0xdc7b383300011106,0xdd2174cf00000008,0xdd50076200048106,0xdd51e16200000003,0xdd5cbec800000003,0xdd6a9ad300000004].getD (i % 8) 0 else [0xde07bdae00000000,0xde76525000000003,0xde8f46fc00046108,0xdf0d23f100000004,0xdf7da15700000000,0xdfd0a1fd00000003,0xe067654200000003,0xe09ad40e0008a106].getD (i % 8) 0) else (if i < 2648 then [0xe09c5a9800000003,0xe0a9f11000051108,0xe0d2dfc500000008,0xe0df84750000000a,0xe0f1ef7600000004,0xe1df75dc00000003,0xe23d5d2c00008106,0xe244aa180000000a].getD (i % 8) 0 else [0xe3c01e0600000004,0xe47cffb2000d1106,0xe4b376c9000ce106,0xe4e0944000000003,0xe5319abd00002106,0xe618a3b000000006,0xe6cbf5a100000000,0xe75fd1c60000000a].getD (i % 8) 0)) else (if i < 2672 then (if i < 2664 then [0xe76fd72400000000,0xe7ae971e00000000,0xe7f54da100000003,0xe8377d330008a106,0xe85166a800000003,0xe8f6cb2c00000000,0xe91b840d00000008,0xe938e43d00000000].getD (i % 8) 0 else [0xe99481ec00000003,0xe99fc94e00000000,0xe9cb68a7000d1108,0xe9f94f1600000006,0xea0e689e00000003,0xeab111aa00000003,0xeafc219c00000004,0xeb8d85c600000004].getD (i % 8) 0) else (if i < 2680 then [0xebc9e75600000000,0xec0815fe00004106,0xec5f5bda00091106,0xec7a715700000006,0xec9eaaba00000004,0xeca5539700000000,0xecabf78100011106,0xecefa6cb00000003].getD (i % 8) 0 else [0xecf907a500000008,0xed37ac2700000003,0xed3ea1d900046106,0xed75d77000112108,0xed80c6b000048106,0xedf41f8f0000000a,0xee930855000d1108,0xee9eb5bd000ce106].getD (i % 8) 0))))

def cutWordDataBlock21 (i : Nat) : Nat := (if i < 2752 then (if i < 2720 then (if i < 2704 then (if i < 2696 then [0xeede4d4000000008,0xeef86d4400051106,0xf02639af00000006,0xf07b7b6500000006,0xf0b10f7000000000,0xf0b284e800002106,0xf0c7175400005108,0xf0debf8d00000008].getD (i % 8) 0 else [0xf150ca1e00050106,0xf21dde0800000000,0xf2661dba00000003,0xf2bb661800000000,0xf318f8bd00000004,0xf333e93b00000004,0xf346fbd90008d108,0xf375559800000004].getD (i % 8) 0) else (if i < 2712 then [0xf3d8fea600000008,0xf406e51500000004,0xf40a253900010108,0xf491848400000008,0xf4bf6af30000d106,0xf4e43617000ce106,0xf50787e800000004,0xf5625a0b00002106].getD (i % 8) 0 else [0xf57a889700000000,0xf5d0b98e0000000a,0xf6aa110600000004,0xf71afc9c00000003,0xf73f608400000000,0xf79fef6700046108,0xf855280100000006,0xf87c236400046108].getD (i % 8) 0)) else (if i < 2736 then (if i < 2728 then [0xf8a09e5400000008,0xf959243200000008,0xf97ea3da00000004,0xf9bb8d2b0000000a,0xf9c17a0400000006,0xf9fa780700000004,0xfa0ad77200000000,0xfa3e666400000004].getD (i % 8) 0 else [0xfa89116400000006,0xfb9caeb900000003,0xfba1a7d800000006,0xfbc453a400112106,0xfbe6bf3800090108,0xfd42633200000006,0xfdab86ba00000006,0xfe221bce00000000].getD (i % 8) 0) else (if i < 2744 then [0xfe2452a900000006,0xfe3bd65b0000d108,0xfe629a4300000008,0xfe69bcca00000006,0xfeb7ed770000000a,0xff15938800005106,0xff292c9200051106,0xffd192d500112108].getD (i % 8) 0 else [0x74ff93100000006,0x11b146bf00000008,0x36b17ccd00000008,0x44fff90100000006,0x5530b84f00000006,0x7a973d8600000006,0xb0db8caa00000006,0xc7b0887d00000008].getD (i % 8) 0))) else [0xf3d8fea600000008,0xf406e51500000006,0xf8a09e5400000008].getD (i % 8) 0)

def cutWordData (i : Nat) : Nat := (if i < 2048 then (if i < 1024 then (if i < 512 then (if i < 256 then (if i < 128 then cutWordDataBlock0 i else cutWordDataBlock1 i) else (if i < 384 then cutWordDataBlock2 i else cutWordDataBlock3 i)) else (if i < 768 then (if i < 640 then cutWordDataBlock4 i else cutWordDataBlock5 i) else (if i < 896 then cutWordDataBlock6 i else cutWordDataBlock7 i))) else (if i < 1536 then (if i < 1280 then (if i < 1152 then cutWordDataBlock8 i else cutWordDataBlock9 i) else (if i < 1408 then cutWordDataBlock10 i else cutWordDataBlock11 i)) else (if i < 1792 then (if i < 1664 then cutWordDataBlock12 i else cutWordDataBlock13 i) else (if i < 1920 then cutWordDataBlock14 i else cutWordDataBlock15 i)))) else (if i < 2560 then (if i < 2304 then (if i < 2176 then cutWordDataBlock16 i else cutWordDataBlock17 i) else (if i < 2432 then cutWordDataBlock18 i else cutWordDataBlock19 i)) else (if i < 2688 then cutWordDataBlock20 i else cutWordDataBlock21 i)))

def cutWord (s i : Nat) : Nat := cutWordData ([0,0,0,0,0,33,458,1852,2744,2755].getD s 0 + i)

def CN (s : Nat) := [0,0,0,0,33,425,1394,892,11,0].getD s 0
def chAt (s i : Nat) := cutWord s i >>> 32
def cidxH (s h : Nat) := bsr (chAt s) h 12 0 (CN s)

def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_0 roots_0 6 s ws hint
  | 1 => checkCutEntry dom_1 roots_1 4 s ws hint
  | 2 => checkCutEntry dom_2 roots_2 4 s ws hint
  | 3 => checkCutEntry dom_3 roots_3 6 s ws hint
  | 4 => checkCutEntry dom_4 roots_4 6 s ws hint
  | 5 => checkCutEntry dom_5 roots_5 4 s ws hint
  | 6 => checkCutEntry dom_6 roots_6 7 s ws hint
  | 7 => checkCutEntry dom_7 roots_7 4 s ws hint
  | 8 => checkCutEntry dom_8 roots_8 7 s ws hint
  | 9 => checkCutEntry dom_9 roots_9 4 s ws hint
  | 10 => checkCutEntry dom_10 roots_10 6 s ws hint
  | 11 => checkCutEntry dom_11 roots_11 4 s ws hint
  | _ => false

def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (cutWord s i &&& 4294967295)

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_12 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_3 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_5 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_6 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_7 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_9 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_10 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_11 _ hc
  · contradiction

def cutHit (s : Nat) (ws : List Nat) := cutHitH s (hk 0 ws) ws
def ori (xs : List Nat) := xs
theorem ori_ok {u ys} (h : RunD dom_12 goalM u ys) : RunD dom_12 goalM u (ori ys) := h
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_12 goalM u ys := cutHitH_sound h
def pool6G : List Nat := []

def Z (s : Nat) := bar dom_12 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s

theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_6 : ∀ i, 6 ≤ i → i < 12 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 6 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_12 : ∀ i, 12 ≤ i → i < 18 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 12 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z4_18 : ∀ i, 18 ≤ i → i < 19 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 18 = true)

theorem z4 : ∀ i, 0 ≤ i → i < 19 → Z 4 i = true := (range_split (range_split z4_0 z4_6) (range_split z4_12 z4_18))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_0 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_6 : ∀ i, 6 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 6 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_12 : ∀ i, 12 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 12 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_18 : ∀ i, 18 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 18 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_24 : ∀ i, 24 ≤ i → i < 30 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 24 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_30 : ∀ i, 30 ≤ i → i < 36 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 30 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_36 : ∀ i, 36 ≤ i → i < 42 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 36 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_42 : ∀ i, 42 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 42 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_48 : ∀ i, 48 ≤ i → i < 54 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 48 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_54 : ∀ i, 54 ≤ i → i < 60 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 54 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_60 : ∀ i, 60 ≤ i → i < 66 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 60 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_66 : ∀ i, 66 ≤ i → i < 72 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 66 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_72 : ∀ i, 72 ≤ i → i < 78 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 72 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_78 : ∀ i, 78 ≤ i → i < 84 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 78 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_84 : ∀ i, 84 ≤ i → i < 90 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 84 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_90 : ∀ i, 90 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 90 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_96 : ∀ i, 96 ≤ i → i < 102 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 96 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_102 : ∀ i, 102 ≤ i → i < 108 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 102 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_108 : ∀ i, 108 ≤ i → i < 114 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 108 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_114 : ∀ i, 114 ≤ i → i < 120 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 114 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_120 : ∀ i, 120 ≤ i → i < 126 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 120 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_126 : ∀ i, 126 ≤ i → i < 132 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 126 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_132 : ∀ i, 132 ≤ i → i < 138 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 132 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_138 : ∀ i, 138 ≤ i → i < 144 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 138 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_144 : ∀ i, 144 ≤ i → i < 150 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 144 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_150 : ∀ i, 150 ≤ i → i < 156 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 150 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_156 : ∀ i, 156 ≤ i → i < 162 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 156 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_162 : ∀ i, 162 ≤ i → i < 168 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 162 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_168 : ∀ i, 168 ≤ i → i < 174 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 168 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_174 : ∀ i, 174 ≤ i → i < 180 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 174 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z5_180 : ∀ i, 180 ≤ i → i < 185 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 180 = true)

theorem z5 : ∀ i, 0 ≤ i → i < 185 → Z 5 i = true := (range_split (range_split (range_split (range_split (range_split z5_0 z5_6) (range_split z5_12 z5_18)) (range_split (range_split z5_24 z5_30) (range_split z5_36 z5_42))) (range_split (range_split (range_split z5_48 z5_54) (range_split z5_60 z5_66)) (range_split (range_split z5_72 z5_78) (range_split z5_84 z5_90)))) (range_split (range_split (range_split (range_split z5_96 z5_102) (range_split z5_108 z5_114)) (range_split (range_split z5_120 z5_126) (range_split z5_132 z5_138))) (range_split (range_split (range_split z5_144 z5_150) (range_split z5_156 z5_162)) (range_split (range_split z5_168 z5_174) z5_180))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_0 : ∀ i, 0 ≤ i → i < 6 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_6 : ∀ i, 6 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 6 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_12 : ∀ i, 12 ≤ i → i < 18 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 12 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_18 : ∀ i, 18 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 18 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_24 : ∀ i, 24 ≤ i → i < 30 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 24 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_30 : ∀ i, 30 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 30 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_36 : ∀ i, 36 ≤ i → i < 42 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 36 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_42 : ∀ i, 42 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 42 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_48 : ∀ i, 48 ≤ i → i < 54 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 48 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_54 : ∀ i, 54 ≤ i → i < 60 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 54 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_60 : ∀ i, 60 ≤ i → i < 66 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 60 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_66 : ∀ i, 66 ≤ i → i < 72 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 66 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_72 : ∀ i, 72 ≤ i → i < 78 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 72 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_78 : ∀ i, 78 ≤ i → i < 84 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 78 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_84 : ∀ i, 84 ≤ i → i < 90 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 84 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_90 : ∀ i, 90 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 90 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_96 : ∀ i, 96 ≤ i → i < 102 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 96 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_102 : ∀ i, 102 ≤ i → i < 108 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 102 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_108 : ∀ i, 108 ≤ i → i < 114 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 108 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_114 : ∀ i, 114 ≤ i → i < 120 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 114 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_120 : ∀ i, 120 ≤ i → i < 126 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 120 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_126 : ∀ i, 126 ≤ i → i < 132 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 126 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_132 : ∀ i, 132 ≤ i → i < 138 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 132 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_138 : ∀ i, 138 ≤ i → i < 144 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 138 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_144 : ∀ i, 144 ≤ i → i < 150 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 144 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_150 : ∀ i, 150 ≤ i → i < 156 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 150 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_156 : ∀ i, 156 ≤ i → i < 162 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 156 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_162 : ∀ i, 162 ≤ i → i < 168 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 162 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_168 : ∀ i, 168 ≤ i → i < 174 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 168 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_174 : ∀ i, 174 ≤ i → i < 180 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 174 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_180 : ∀ i, 180 ≤ i → i < 186 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 180 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_186 : ∀ i, 186 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 186 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_192 : ∀ i, 192 ≤ i → i < 198 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 192 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_198 : ∀ i, 198 ≤ i → i < 204 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 198 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_204 : ∀ i, 204 ≤ i → i < 210 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 204 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_210 : ∀ i, 210 ≤ i → i < 216 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 210 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_216 : ∀ i, 216 ≤ i → i < 222 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 216 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_222 : ∀ i, 222 ≤ i → i < 228 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 222 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_228 : ∀ i, 228 ≤ i → i < 234 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 228 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_234 : ∀ i, 234 ≤ i → i < 240 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 234 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_240 : ∀ i, 240 ≤ i → i < 246 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 240 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_246 : ∀ i, 246 ≤ i → i < 252 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 246 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_252 : ∀ i, 252 ≤ i → i < 258 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 252 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_258 : ∀ i, 258 ≤ i → i < 264 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 258 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_264 : ∀ i, 264 ≤ i → i < 270 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 264 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_270 : ∀ i, 270 ≤ i → i < 276 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 270 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_276 : ∀ i, 276 ≤ i → i < 282 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 276 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_282 : ∀ i, 282 ≤ i → i < 288 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 282 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_288 : ∀ i, 288 ≤ i → i < 294 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 288 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_294 : ∀ i, 294 ≤ i → i < 300 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 294 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_300 : ∀ i, 300 ≤ i → i < 306 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 300 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_306 : ∀ i, 306 ≤ i → i < 312 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 306 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_312 : ∀ i, 312 ≤ i → i < 318 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 312 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_318 : ∀ i, 318 ≤ i → i < 324 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 318 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_324 : ∀ i, 324 ≤ i → i < 330 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 324 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_330 : ∀ i, 330 ≤ i → i < 336 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 330 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_336 : ∀ i, 336 ≤ i → i < 342 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 336 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_342 : ∀ i, 342 ≤ i → i < 348 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 342 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_348 : ∀ i, 348 ≤ i → i < 354 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 348 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_354 : ∀ i, 354 ≤ i → i < 360 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 354 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_360 : ∀ i, 360 ≤ i → i < 366 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 360 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_366 : ∀ i, 366 ≤ i → i < 372 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 366 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_372 : ∀ i, 372 ≤ i → i < 378 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 372 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_378 : ∀ i, 378 ≤ i → i < 384 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 378 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_384 : ∀ i, 384 ≤ i → i < 390 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 384 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_390 : ∀ i, 390 ≤ i → i < 396 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 390 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_396 : ∀ i, 396 ≤ i → i < 402 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 396 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_402 : ∀ i, 402 ≤ i → i < 408 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 402 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_408 : ∀ i, 408 ≤ i → i < 414 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 408 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_414 : ∀ i, 414 ≤ i → i < 420 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 414 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_420 : ∀ i, 420 ≤ i → i < 426 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 420 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_426 : ∀ i, 426 ≤ i → i < 432 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 426 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_432 : ∀ i, 432 ≤ i → i < 438 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 432 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_438 : ∀ i, 438 ≤ i → i < 444 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 438 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_444 : ∀ i, 444 ≤ i → i < 450 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 444 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_450 : ∀ i, 450 ≤ i → i < 456 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 450 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_456 : ∀ i, 456 ≤ i → i < 462 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 456 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_462 : ∀ i, 462 ≤ i → i < 468 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 462 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_468 : ∀ i, 468 ≤ i → i < 474 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 468 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_474 : ∀ i, 474 ≤ i → i < 480 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 474 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_480 : ∀ i, 480 ≤ i → i < 486 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 480 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_486 : ∀ i, 486 ≤ i → i < 492 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 486 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_492 : ∀ i, 492 ≤ i → i < 498 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 492 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_498 : ∀ i, 498 ≤ i → i < 504 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 498 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_504 : ∀ i, 504 ≤ i → i < 510 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 504 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_510 : ∀ i, 510 ≤ i → i < 516 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 510 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_516 : ∀ i, 516 ≤ i → i < 522 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 516 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_522 : ∀ i, 522 ≤ i → i < 528 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 522 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_528 : ∀ i, 528 ≤ i → i < 534 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 528 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_534 : ∀ i, 534 ≤ i → i < 540 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 534 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_540 : ∀ i, 540 ≤ i → i < 546 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 540 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_546 : ∀ i, 546 ≤ i → i < 552 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 546 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_552 : ∀ i, 552 ≤ i → i < 558 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 552 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_558 : ∀ i, 558 ≤ i → i < 564 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 558 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_564 : ∀ i, 564 ≤ i → i < 570 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 564 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_570 : ∀ i, 570 ≤ i → i < 576 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 570 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_576 : ∀ i, 576 ≤ i → i < 582 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 576 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_582 : ∀ i, 582 ≤ i → i < 588 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 582 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_588 : ∀ i, 588 ≤ i → i < 594 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 588 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_594 : ∀ i, 594 ≤ i → i < 600 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 594 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_600 : ∀ i, 600 ≤ i → i < 606 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 600 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_606 : ∀ i, 606 ≤ i → i < 612 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 606 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_612 : ∀ i, 612 ≤ i → i < 618 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 612 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_618 : ∀ i, 618 ≤ i → i < 624 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 618 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_624 : ∀ i, 624 ≤ i → i < 630 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 624 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_630 : ∀ i, 630 ≤ i → i < 636 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 630 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_636 : ∀ i, 636 ≤ i → i < 642 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 636 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_642 : ∀ i, 642 ≤ i → i < 648 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 642 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_648 : ∀ i, 648 ≤ i → i < 654 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 648 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_654 : ∀ i, 654 ≤ i → i < 660 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 654 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_660 : ∀ i, 660 ≤ i → i < 666 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 660 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_666 : ∀ i, 666 ≤ i → i < 672 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 666 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_672 : ∀ i, 672 ≤ i → i < 678 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 672 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_678 : ∀ i, 678 ≤ i → i < 684 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 678 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_684 : ∀ i, 684 ≤ i → i < 690 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 684 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_690 : ∀ i, 690 ≤ i → i < 696 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 690 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_696 : ∀ i, 696 ≤ i → i < 702 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 696 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_702 : ∀ i, 702 ≤ i → i < 708 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 702 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_708 : ∀ i, 708 ≤ i → i < 714 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 708 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_714 : ∀ i, 714 ≤ i → i < 720 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 714 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_720 : ∀ i, 720 ≤ i → i < 726 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 720 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_726 : ∀ i, 726 ≤ i → i < 732 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 726 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_732 : ∀ i, 732 ≤ i → i < 738 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 732 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_738 : ∀ i, 738 ≤ i → i < 744 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 738 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_744 : ∀ i, 744 ≤ i → i < 750 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 744 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_750 : ∀ i, 750 ≤ i → i < 756 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 750 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_756 : ∀ i, 756 ≤ i → i < 762 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 756 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_762 : ∀ i, 762 ≤ i → i < 768 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 762 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_768 : ∀ i, 768 ≤ i → i < 774 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 768 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_774 : ∀ i, 774 ≤ i → i < 780 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 774 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_780 : ∀ i, 780 ≤ i → i < 786 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 780 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_786 : ∀ i, 786 ≤ i → i < 792 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 786 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_792 : ∀ i, 792 ≤ i → i < 798 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 792 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z6_798 : ∀ i, 798 ≤ i → i < 803 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 5 798 = true)

theorem z6 : ∀ i, 0 ≤ i → i < 803 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split (range_split z6_0 z6_6) (range_split z6_12 z6_18)) (range_split (range_split z6_24 z6_30) (range_split z6_36 z6_42))) (range_split (range_split (range_split z6_48 z6_54) (range_split z6_60 z6_66)) (range_split (range_split z6_72 z6_78) (range_split z6_84 z6_90)))) (range_split (range_split (range_split (range_split z6_96 z6_102) (range_split z6_108 z6_114)) (range_split (range_split z6_120 z6_126) (range_split z6_132 z6_138))) (range_split (range_split (range_split z6_144 z6_150) (range_split z6_156 z6_162)) (range_split (range_split z6_168 z6_174) (range_split z6_180 z6_186))))) (range_split (range_split (range_split (range_split (range_split z6_192 z6_198) (range_split z6_204 z6_210)) (range_split (range_split z6_216 z6_222) (range_split z6_228 z6_234))) (range_split (range_split (range_split z6_240 z6_246) (range_split z6_252 z6_258)) (range_split (range_split z6_264 z6_270) (range_split z6_276 z6_282)))) (range_split (range_split (range_split (range_split z6_288 z6_294) (range_split z6_300 z6_306)) (range_split (range_split z6_312 z6_318) (range_split z6_324 z6_330))) (range_split (range_split (range_split z6_336 z6_342) (range_split z6_348 z6_354)) (range_split (range_split z6_360 z6_366) (range_split z6_372 z6_378)))))) (range_split (range_split (range_split (range_split (range_split (range_split z6_384 z6_390) (range_split z6_396 z6_402)) (range_split (range_split z6_408 z6_414) (range_split z6_420 z6_426))) (range_split (range_split (range_split z6_432 z6_438) (range_split z6_444 z6_450)) (range_split (range_split z6_456 z6_462) (range_split z6_468 z6_474)))) (range_split (range_split (range_split (range_split z6_480 z6_486) (range_split z6_492 z6_498)) (range_split (range_split z6_504 z6_510) (range_split z6_516 z6_522))) (range_split (range_split (range_split z6_528 z6_534) (range_split z6_540 z6_546)) (range_split (range_split z6_552 z6_558) (range_split z6_564 z6_570))))) (range_split (range_split (range_split (range_split (range_split z6_576 z6_582) (range_split z6_588 z6_594)) (range_split (range_split z6_600 z6_606) (range_split z6_612 z6_618))) (range_split (range_split (range_split z6_624 z6_630) (range_split z6_636 z6_642)) (range_split (range_split z6_648 z6_654) (range_split z6_660 z6_666)))) (range_split (range_split (range_split (range_split z6_672 z6_678) (range_split z6_684 z6_690)) (range_split (range_split z6_696 z6_702) (range_split z6_708 z6_714))) (range_split (range_split (range_split z6_720 z6_726) (range_split z6_732 z6_738)) (range_split (range_split z6_744 z6_750) (range_split z6_756 z6_762))))))) (range_split (range_split (range_split z6_768 z6_774) (range_split z6_780 z6_786)) (range_split z6_792 z6_798)))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_0 : ∀ i, 0 ≤ i → i < 6 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_6 : ∀ i, 6 ≤ i → i < 12 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 6 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_12 : ∀ i, 12 ≤ i → i < 18 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 12 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_18 : ∀ i, 18 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 18 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_24 : ∀ i, 24 ≤ i → i < 30 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 24 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_30 : ∀ i, 30 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 30 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_36 : ∀ i, 36 ≤ i → i < 42 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 36 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_42 : ∀ i, 42 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 42 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_48 : ∀ i, 48 ≤ i → i < 54 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 48 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_54 : ∀ i, 54 ≤ i → i < 60 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 54 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_60 : ∀ i, 60 ≤ i → i < 66 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 60 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_66 : ∀ i, 66 ≤ i → i < 72 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 66 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_72 : ∀ i, 72 ≤ i → i < 78 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 72 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_78 : ∀ i, 78 ≤ i → i < 84 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 78 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_84 : ∀ i, 84 ≤ i → i < 90 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 84 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_90 : ∀ i, 90 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 90 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_96 : ∀ i, 96 ≤ i → i < 102 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 96 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_102 : ∀ i, 102 ≤ i → i < 108 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 102 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_108 : ∀ i, 108 ≤ i → i < 114 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 108 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_114 : ∀ i, 114 ≤ i → i < 120 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 114 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_120 : ∀ i, 120 ≤ i → i < 126 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 120 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_126 : ∀ i, 126 ≤ i → i < 132 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 126 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_132 : ∀ i, 132 ≤ i → i < 138 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 132 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_138 : ∀ i, 138 ≤ i → i < 144 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 138 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_144 : ∀ i, 144 ≤ i → i < 150 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 144 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_150 : ∀ i, 150 ≤ i → i < 156 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 150 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_156 : ∀ i, 156 ≤ i → i < 162 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 156 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_162 : ∀ i, 162 ≤ i → i < 168 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 162 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_168 : ∀ i, 168 ≤ i → i < 174 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 168 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_174 : ∀ i, 174 ≤ i → i < 180 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 174 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_180 : ∀ i, 180 ≤ i → i < 186 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 180 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_186 : ∀ i, 186 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 186 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_192 : ∀ i, 192 ≤ i → i < 198 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 192 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_198 : ∀ i, 198 ≤ i → i < 204 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 198 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_204 : ∀ i, 204 ≤ i → i < 210 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 204 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_210 : ∀ i, 210 ≤ i → i < 216 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 210 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_216 : ∀ i, 216 ≤ i → i < 222 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 216 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_222 : ∀ i, 222 ≤ i → i < 228 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 222 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_228 : ∀ i, 228 ≤ i → i < 234 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 228 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_234 : ∀ i, 234 ≤ i → i < 240 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 234 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_240 : ∀ i, 240 ≤ i → i < 246 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 240 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_246 : ∀ i, 246 ≤ i → i < 252 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 246 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_252 : ∀ i, 252 ≤ i → i < 258 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 252 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_258 : ∀ i, 258 ≤ i → i < 264 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 258 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_264 : ∀ i, 264 ≤ i → i < 270 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 264 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_270 : ∀ i, 270 ≤ i → i < 276 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 270 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_276 : ∀ i, 276 ≤ i → i < 282 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 276 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_282 : ∀ i, 282 ≤ i → i < 288 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 282 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_288 : ∀ i, 288 ≤ i → i < 294 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 288 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_294 : ∀ i, 294 ≤ i → i < 300 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 294 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_300 : ∀ i, 300 ≤ i → i < 306 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 300 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_306 : ∀ i, 306 ≤ i → i < 312 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 306 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_312 : ∀ i, 312 ≤ i → i < 318 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 312 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_318 : ∀ i, 318 ≤ i → i < 324 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 318 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_324 : ∀ i, 324 ≤ i → i < 330 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 324 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_330 : ∀ i, 330 ≤ i → i < 336 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 330 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_336 : ∀ i, 336 ≤ i → i < 342 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 336 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_342 : ∀ i, 342 ≤ i → i < 348 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 342 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_348 : ∀ i, 348 ≤ i → i < 354 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 348 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_354 : ∀ i, 354 ≤ i → i < 360 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 354 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_360 : ∀ i, 360 ≤ i → i < 366 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 360 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_366 : ∀ i, 366 ≤ i → i < 372 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 366 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_372 : ∀ i, 372 ≤ i → i < 378 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 372 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_378 : ∀ i, 378 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 378 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_384 : ∀ i, 384 ≤ i → i < 390 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 384 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_390 : ∀ i, 390 ≤ i → i < 396 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 390 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_396 : ∀ i, 396 ≤ i → i < 402 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 396 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_402 : ∀ i, 402 ≤ i → i < 408 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 402 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_408 : ∀ i, 408 ≤ i → i < 414 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 408 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_414 : ∀ i, 414 ≤ i → i < 420 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 414 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_420 : ∀ i, 420 ≤ i → i < 426 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 420 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_426 : ∀ i, 426 ≤ i → i < 432 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 426 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_432 : ∀ i, 432 ≤ i → i < 438 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 432 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_438 : ∀ i, 438 ≤ i → i < 444 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 438 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_444 : ∀ i, 444 ≤ i → i < 450 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 444 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_450 : ∀ i, 450 ≤ i → i < 456 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 450 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_456 : ∀ i, 456 ≤ i → i < 462 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 456 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_462 : ∀ i, 462 ≤ i → i < 468 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 462 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_468 : ∀ i, 468 ≤ i → i < 474 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 468 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_474 : ∀ i, 474 ≤ i → i < 480 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 474 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_480 : ∀ i, 480 ≤ i → i < 486 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 480 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_486 : ∀ i, 486 ≤ i → i < 492 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 486 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_492 : ∀ i, 492 ≤ i → i < 498 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 492 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_498 : ∀ i, 498 ≤ i → i < 504 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 498 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_504 : ∀ i, 504 ≤ i → i < 510 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 504 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z7_510 : ∀ i, 510 ≤ i → i < 514 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 510 = true)

theorem z7 : ∀ i, 0 ≤ i → i < 514 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split (range_split (range_split z7_0 z7_6) (range_split z7_12 z7_18)) (range_split (range_split z7_24 z7_30) (range_split z7_36 z7_42))) (range_split (range_split (range_split z7_48 z7_54) (range_split z7_60 z7_66)) (range_split (range_split z7_72 z7_78) (range_split z7_84 z7_90)))) (range_split (range_split (range_split (range_split z7_96 z7_102) (range_split z7_108 z7_114)) (range_split (range_split z7_120 z7_126) (range_split z7_132 z7_138))) (range_split (range_split (range_split z7_144 z7_150) (range_split z7_156 z7_162)) (range_split (range_split z7_168 z7_174) (range_split z7_180 z7_186))))) (range_split (range_split (range_split (range_split (range_split z7_192 z7_198) (range_split z7_204 z7_210)) (range_split (range_split z7_216 z7_222) (range_split z7_228 z7_234))) (range_split (range_split (range_split z7_240 z7_246) (range_split z7_252 z7_258)) (range_split (range_split z7_264 z7_270) (range_split z7_276 z7_282)))) (range_split (range_split (range_split (range_split z7_288 z7_294) (range_split z7_300 z7_306)) (range_split (range_split z7_312 z7_318) (range_split z7_324 z7_330))) (range_split (range_split (range_split z7_336 z7_342) (range_split z7_348 z7_354)) (range_split (range_split z7_360 z7_366) (range_split z7_372 z7_378)))))) (range_split (range_split (range_split (range_split (range_split z7_384 z7_390) (range_split z7_396 z7_402)) (range_split (range_split z7_408 z7_414) (range_split z7_420 z7_426))) (range_split (range_split (range_split z7_432 z7_438) (range_split z7_444 z7_450)) (range_split (range_split z7_456 z7_462) (range_split z7_468 z7_474)))) (range_split (range_split (range_split z7_480 z7_486) (range_split z7_492 z7_498)) (range_split z7_504 z7_510))))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_0 : ∀ i, 0 ≤ i → i < 6 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 0 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_6 : ∀ i, 6 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 6 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_12 : ∀ i, 12 ≤ i → i < 18 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 12 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_18 : ∀ i, 18 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 18 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_24 : ∀ i, 24 ≤ i → i < 30 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 24 = true)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem z8_30 : ∀ i, 30 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 30 = true)

theorem z8 : ∀ i, 0 ≤ i → i < 32 → Z 8 i = true := (range_split (range_split (range_split z8_0 z8_6) (range_split z8_12 z8_18)) (range_split z8_24 z8_30))

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
  scr dom_12 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_12 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noCircuit : Lower dom_12 roots_12 goal_12 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_12 goal_12 := by
    have h0 : isConstB dom_12 goal_12 = false := by decide +kernel
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

end Cert12
theorem low_12 : Lower dom_12 roots_12 goal_12 10 := Cert12.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_12_bits : ∀ r : Fin 64, roots_12.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_12_lt : ∀ r : Fin 64, dom_12.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_12 T)
    (hlow : Lower dom_12 roots_12 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_12, Avail mask256 roots_12 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_12 hfan 0 roots_12 roots_12 rfl hsup0
  set out := (execN C.gates roots_12).getD C.output 0
  have hout : out &&& dom_12 = T &&& dom_12 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_12_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_12 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_12_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_12).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_12)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_12.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_12 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_12).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_12 &&& mask256 = dom_12 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_12 = T &&& dom_12 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_12, hd63, hout]
  have hnc_m : ¬ IsConst dom_12 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_12 roots_12 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_12, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_12 roots_12 0 roots_12 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def fG : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4008636128 * 2 ^ 32 + 4008372928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem hT6 : ∀ r : Fin 64, goal_12.testBit r.val = fG (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, HasCircuitSize 6 fG t → 10 ≤ t := lower_to_circuit6 fG goal_12 10 hT6 (by unfold IsConst; decide) low_12

def wit : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.and,[3,4]⟩,⟨.or,[3,4]⟩,⟨.or,[0,5]⟩,⟨.or,[1,5]⟩,⟨.or,[2,7]⟩,⟨.and,[8,9]⟩,⟨.and,[10,11]⟩,⟨.or,[12,13]⟩,⟨.and,[6,14]⟩],15⟩

theorem wmono : Monotone2 wit := by simp [wit, Monotone2]
theorem wsize : wit.size ≤ 10 := by decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = fG x := by decide +kernel

end PEqualNP.Outside.L_meta_15945_aux

theorem PEqualNP.Outside.L_meta_15945 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008636128 * 2 ^ 32 + 4008372928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008636128 * 2 ^ 32 + 4008372928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_15945_aux.wit, PEqualNP.Outside.L_meta_15945_aux.wmono, le_trans PEqualNP.Outside.L_meta_15945_aux.wsize (PEqualNP.Outside.L_meta_15945_aux.lower s hs), PEqualNP.Outside.L_meta_15945_aux.weval⟩
