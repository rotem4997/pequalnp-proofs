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

namespace PEqualNP.Outside.L_meta_12895_aux

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

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeaaaa88cc000000eeaaaa88cc000000eeaaaa88cc000000eeaaaa88cc000000
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfaaaaa00f0000000faaaaa00f0000000faaaaa00f0000000faaaaa00f0000000
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfeeaeac8fcc0c0c0feeaeac8fcc0c0c0feeaeac8fcc0c0c0feeaeac8fcc0c0c0
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_30
def pairsG : List (Nat × Nat) := [(2, 6), (4, 6), (10, 14), (10, 26), (12, 14), (12, 28), (18, 22), (18, 26), (20, 22), (20, 28), (24, 26), (24, 28)]
def r1sG : List Nat := [2, 4, 10, 10, 12, 12, 18, 18, 20, 20, 24, 24]
def r2sG : List Nat := [6, 6, 14, 26, 14, 28, 22, 26, 22, 28, 26, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := [13237493701126]
def xsM : List Nat := roots_30.map (· &&& dom_30)
def goalM : Nat := goal_30 &&& dom_30
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe65a0c41
  | 4, 0 => 0xe17a4c91
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x555500000000000000000000000000000000000000000000000000000000000055005500000000000000000000000000000000000000000000000000000000005500000000000000000000000000000000000000000000000000000000000000505050500000000000000000000000000000000000000000000000000000000044444444
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x883
  | 4, 0, 0 => 0x8c84
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 13
  | 4 => 16
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc00000000000000000000000000000000000000000000000000000000000000c3c0000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000033200000000000000000000000000000000000000000000000000000000000000cd
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfe80000000000000000000000000000000000000000000000000000000000000ebc0000000000000000000000000000000000000000000000000000000000000ea80000000000000000000000000000000000000000000000000000000000000b7700000000000000000000000000000000000000000000000000000000000005df
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 5 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 5 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 5 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 5 then wireAt i else 0
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
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_30 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_30 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_30 == dom_30) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_30 goalM u ys) : RunD dom_30 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_30 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_30 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_30 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_30 roots_30 goal_30 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_30 goal_30 := by
    have h0 : isConstB dom_30 goal_30 = false := by decide +kernel
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

end S_30

theorem low_30 : Lower dom_30 roots_30 goal_30 5 := S_30.noCircuit

namespace S_59
def pairsG : List (Nat × Nat) := [(3, 35), (9, 41), (10, 26), (11, 27), (11, 43), (17, 49), (18, 26), (19, 27), (19, 51), (24, 26), (25, 27), (25, 57), (33, 35), (33, 41), (33, 49), (34, 35), (40, 41), (42, 43), (42, 58), (48, 49), (50, 51), (50, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [3, 9, 10, 11, 11, 17, 18, 19, 19, 24, 25, 25, 33, 33, 33, 34, 40, 42, 42, 48, 50, 50, 56, 56]
def r2sG : List Nat := [35, 41, 26, 27, 43, 49, 26, 27, 51, 26, 27, 57, 35, 41, 49, 35, 41, 43, 58, 49, 51, 58, 57, 58]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [27569951417114]
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xc55bddd0
  | 5, 0 => 0xf0260ba
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f000000000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000a0a0a0a00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x6884
  | 5, 0, 0 => 0x568c5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 16
  | 5 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfff0000000000000000000000000000000000000000000000000000000000000007dbb0000000000000000000000000000000000000000000000000000000000f80fe00000000000000000000000000000000000000000000000000000000000c70e1e00000000000000000000000000000000000000000000000000000000003681dd0000000000000000000000000000000000000000000000000000000000007000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfff93300000000000000000000000000000000000000000000000000000000005bfdbb0000000000000000000000000000000000000000000000000000000000fc4fec0000000000000000000000000000000000000000000000000000000000e72ede0000000000000000000000000000000000000000000000000000000000b697dd00000000000000000000000000000000000000000000000000000000005bf933
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_59 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_59 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_59 == dom_59) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_59 goalM u ys) : RunD dom_59 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_59 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_59 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_59 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_59 roots_59 goal_59 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_59 goal_59 := by
    have h0 : isConstB dom_59 goal_59 = false := by decide +kernel
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

end S_59

theorem low_59 : Lower dom_59 roots_59 goal_59 6 := S_59.noCircuit

namespace S_61
def pairsG : List (Nat × Nat) := [(9, 41), (12, 28), (13, 29), (13, 45), (17, 49), (20, 28), (21, 29), (21, 53), (24, 28), (25, 29), (25, 57), (33, 41), (33, 49), (37, 45), (37, 53), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [9, 12, 13, 13, 17, 20, 21, 21, 24, 25, 25, 33, 33, 37, 37, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [41, 28, 29, 45, 49, 28, 29, 53, 28, 29, 57, 41, 49, 45, 53, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [40772345338929, 40738120342569, 23146202736924]
def xsM : List Nat := roots_61.map (· &&& dom_61)
def goalM : Nat := goal_61 &&& dom_61
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xb5f27f30
  | 5, 0 => 0x653667d8
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x333333330000000000000000000000000000000000000000000000000000000022222222222222220000000000000000000000000000000000000000000000003333000033330000000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000002222222200000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x6884
  | 5, 0, 0 => 0x568c5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 16
  | 5 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x7ff8000000000000000000000000000000000000000000000000000000000000007edd00000000000000000000000000000000000000000000000000000000007c07f0000000000000000000000000000000000000000000000000000000000063870f00000000000000000000000000000000000000000000000000000000001b60ee0000000000000000000000000000000000000000000000000000000000007800
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7ffc9900000000000000000000000000000000000000000000000000000000002dfedd00000000000000000000000000000000000000000000000000000000007e57f6000000000000000000000000000000000000000000000000000000000073af6f00000000000000000000000000000000000000000000000000000000005b63ee00000000000000000000000000000000000000000000000000000000002dfc99
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_61 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_61 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_61 == dom_61) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_61 goalM u ys) : RunD dom_61 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_61 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_61 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_61 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_61 roots_61 goal_61 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_61 goal_61 := by
    have h0 : isConstB dom_61 goal_61 = false := by decide +kernel
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

end S_61

theorem low_61 : Lower dom_61 roots_61 goal_61 6 := S_61.noCircuit

namespace S_63
def pairsG : List (Nat × Nat) := [(2, 6), (3, 7), (3, 35), (4, 6), (5, 7), (9, 41), (10, 14), (10, 26), (11, 15), (11, 27), (11, 43), (12, 14), (12, 28), (13, 15), (13, 29), (13, 45), (17, 49), (18, 22), (18, 26), (19, 23), (19, 27), (19, 51), (20, 22), (20, 28), (21, 23), (21, 29), (21, 53), (24, 26), (24, 28), (25, 27), (25, 29), (25, 57), (33, 35), (33, 41), (33, 49), (34, 35), (34, 38), (36, 38), (37, 39), (37, 45), (37, 53), (40, 41), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 3, 3, 4, 5, 9, 10, 10, 11, 11, 11, 12, 12, 13, 13, 13, 17, 18, 18, 19, 19, 19, 20, 20, 21, 21, 21, 24, 24, 25, 25, 25, 33, 33, 33, 34, 34, 36, 37, 37, 37, 40, 42, 42, 42, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [6, 7, 35, 6, 7, 41, 14, 26, 15, 27, 43, 14, 28, 15, 29, 45, 49, 22, 26, 23, 27, 51, 22, 28, 23, 29, 53, 26, 28, 27, 29, 57, 35, 41, 49, 35, 38, 38, 39, 45, 53, 41, 43, 46, 58, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3ffffffffffffff
def pool6G : List Nat := [23171769834006, 40772345338929, 46339143042595, 55156593994010, 61761816037148, 40729495935529, 13237510544134, 27569749231130, 61796309993244, 40729596992035, 40763721456177, 40738120342569, 20938589809946, 40763890140707, 27535255275034, 27570018525978, 14341317925382, 57222270556678, 14341318449670]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 3 => 4
  | 4 => 23
  | 5 => 204
  | 6 => 447
  | 7 => 259
  | 8 => 27
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xf57a7e97790dbc4665ec39992ab0fdf7
  | 4, 0 => 0xffefec58ec756281d953dfd4d0e5108cbde4359bbd66b08bba7ae29cb8fee8a1a39ce1c69d0ae66e80b91f1b80885ef66b4603145df1c1eb58c1cc8653c211f03680ea9b363901e23361fd0a30a2a52723ec879410476419046b5db9
  | 5, 0 => 0x329cd2e731e09f8a310d3cd13018ffd32f2dfb092d9b84832c887dd42c01854b2af2d8a92ae564872ad1e6df2a6e02f5299c20f6299c12f8273a8a0026c69d8a2694393f25022fa5228a16192230621421a9a65520fece1f20b44547208d8cd2202215df1fc2fb0c1f38433b1df344641d2198131c455e411a6942fc1a378df419edb8e61961d5231908befe175337cd15fca8f314e7ff3d14abe27d139da07213485d5e1246ed41121740db11837c64116a48a5107b452c10447f220fd9da170ef54d0a0e6188930da3e4970d3c5e220d213aee0ca3b5de0c02158d094444e908ee6f6f0861f965085aaaf808001630055faf75039cdb3d02bfdc8f01a77d22
  | 5, 1 => 0x78a232b2788b6d20779c90de7587d4b875005150708dd8336e8e34576e791c0d6cd182bc6b22dae66a7b285f6a34fbb16a0153b2689f540d680ccfb76637bd7b6267399b60fe170c609a33225fd0c71c5f1200da5c720ff35b568be6598f54bc58f1bad758c20e715873b813582e49fa57e9caf25742df16555ce24154dbf86454c91dca5019e9134c1eac9e4bead77d4a3a583f4a2eeb00470c9299466dfc5c457a831344dca9514305ad0f42fd148b42d52b494243ca9242214f4540ab4dfd40472c733cb3aca13c8b4a893c6c557c3bd15cdc3b3d986538e0e93537e29c7637ac21ad36a5528f35615b1d34f6aab9344ef8323443e9623404e17933f3041d
  | 5, 2 => 0xe8b56faee86e1529e17474c8e0b109bede765715dd872869dc1abd14db1611e9d88289b0d2b7078dd299cd05d1517646d13b44a3ca4a697ec9da89ddc9bac2b3c98e3621c77b7cdac3a5acd8c224e8aec0aa4b76c07ec6f7c05032f2befa5f19be69c748b9700e4cb7eba66eb7ce68d4b757e1f7b716a7a9b6fcca2cb604c368b434601db3b26292aeb79d4dab48449baaadd9e8a7fed1d9a6624a58a2ff17439c6fe8ca989369c8971c1ed395e9624a93931813932213318ea883948e1b05fc8d4bfea98c845f688b0828918a8fed4b8a32aca587ab3dcf8560205184fd814c805659288020623d7d6813017bf8d0037bd4afe07a9dd1b37947a07d791ea258
  | 5, 3 => 0xffdf0045fe3d5acdfd67e933f7a8d5fef5268f46f420c556f3d28c6bf35db393f2ae4899ed841224eca15582ec1b59b5
  | 6, 0 => 0x1102cabf10d6ef02108dfb000f47b66e0f124de30f1175970f0a2ca10ea9e7200dc479fe0db3fb6b0db0d3410d7b2e1b0cf7c80e0cce62560c9e03cb0c76b2fc0c4e41df0bda5acd0ae7ecdc0ad2515e0a9035760a22302e0a1eb381097f4255095e84ee094a188808a714d3088b9c37077e2f710756736a071ebcc6070b6e2706fd30e406c7045f06c0c02a06a21a96063e36ac062172b705e90f6305e3ec2605c54fb805a60b08057e0c0f0573298d0567fa5105205a4f04fa332104678a0c0451cb6b04427193040aaf0b03d3c5950382553003752fc1031706ff02ef67e50270f25002185fdf021598710184b62a01628750015ff58b0104b42a0010041b
  | 6, 1 => 0x24102f2323cf7d44233bb8cd232edee7231e979d22a6f5ce22929d1c21f40ce021d6fea521d6d258212acd6b2109b4d62090380e2075f5e61fe205301fa856201ed2190f1eba10b01e3e87891df565bf1de8e6291d59d57f1cbb86ee1cb356241bbe39af1b983d231af080381ae554351a9d40321a81704b1a72b5351a53497619ce07e619af0e9619231ca31893b97218917f9418667dc918613565185ae16017e5a7ad17d388ff178f9dc81783d36c173d883c1703f31a16cbbec0165fdb941621068e14fb3d0b14f3b30a14c279f4149b041c13ffb8f813e23a6c13b13c8e13acbc761246ed41121740db11ea99d711837c641182c6e911585ff7114d5ad8
  | 6, 2 => 0x3aa042af3a3b06ec39955ad5384d14893846846c382c378237ff233837865af6373201ad370a8bd5369e3d36369255f03676c75e3582312935389f97351210de34de6bb834d6594234c43a9434bd92e33476152a344c26a2340feda7340c055d33f3041d3376f89933121ba33311b82332a284ca329cd2e731f3adf831ebeea031e09f8a314fc4ae3121f68530b17a1b309d6e0b3020be7a2e9e136e2d7eac952cfd4cb22c05dd8b2bef778f2b7d99b12aef28452ae33e892ad1e6df2abf02a32aa184d62a410c032a1defe529e30a9d297d69db294cfc672890fa70288ecc2f27fd35f927ce4e7727c57d6d27bf8f03276eca5b246ee106246225e624387f4a
  | 6, 3 => 0x546f4794545b765953ef921253e30e5253c7b1e2530cf5c45279314d5189a4bf50fcb6f250e562b94f23ef074ea78cac4e4076434ded216a4ddc693a4da583094d69b8694cf4df914ca4ee864c7d48184c3ac3c24af4a5534ae5e5554a357f0848fcf02a48ef7a5e48a70b1f489c65b84894832747b814864731629d464aa44845d991d2456fc3ff44e3171544160fec43cfd02243a4ce57439cf8a64323f83b4249976b41f9bbd441dec60e4197cdb14090fe93404e605b3f97a7633ebf5c103d6f4a1e3cc117773c5d77393c153f903bf920853be010773bcc4b8e3bb15ba63b84cdd53b7a7d2d3b76f0d13b400bf23b3a508c3b2a790d3b1ea6523abf3c5e
  | 6, 4 => 0x758f9d5974391d8f73c49c1972c540b671c71b6c7140d8d87125b82a71239b3e70d9b548706bda136f3999c56dd851da6d3049b76cd182bc6c5e9d666c2261ac6b22dae66b0d7f656addd2ff6abafcb969fdfe6a68bc5f31689eda76684b3d27683c46a3680ccfb766a3f72366896365657f66cf654b0ab46539ae4664ca439b64127297634fc2fb628562b1621ba7bc62072f1c618341bb617923c060fe170c609a33226014a9d05ff88ac55f3052075f16df6a5e34319f5e2462915d03b9ec5cf2b5ff5c70c3ca5c6a8f0c5b7e003f5b78337f5a16683a594b8cd858bcfd235840b374580f57e75781a10f56ebd8645640bafc559b095255813fdc54e640dd
  | 6, 5 => 0xa60a17e5a55cd2cda406231da303ad69a29fc71ea1523354a0855a339f8d239f9d1625de9d0ddf0d9b910e739b773ae19b6a992f9b5bb1f19b27dcd09b233eaa9ade398d9ab48ee89aae65d29a6671909a428dde996bf05396c7f7ac945092be941485ff939fad279339040592b3968a92b0d0e5923b50209180cfe591380981909c14bf8fc706088f8431c68f3f4ae28e75ebe48e07e69c8a7a9db886eeafff86ba297384fd814c83db0476830dbfae82cc6932811da4dd8103242c7f9deae07f5d02fb7e8bb4df7e6b005c7e15d27a7cabb4257c3bbef57bd4afe07ae507237a0eec327976ef1678d9b45d78d9184b786eb1d476ecc1ec764852707603a2dd
  | 6, 6 => 0xffa4fc52fc02cecffbf9bf4dfb7def40fb091668f9433c97f7aa5287f6e7a296f6b7f630f5268f46f4679fa6f0c30fb4ed841224e4a27628e4271949e200006ce17474c8e0db6e2de00a4734dd580b4fdd3f6a77dbf814f5da8377f8da0e9f20d9c7449bd77e6381d5b62547d2b7078dd20974cbd119036fd084ae12d0534614ce822926cb11b533caa7af24c999b18cc867804dc76439aec6d99631c57abf6abf9078b3bf867976bf076360be3b6f79bdf89813bdf4a2d4bb0d12b6b813f03fb79f1767b6e9d33eb5a88bbeb514c747b03b1c5faeb79d4dae7645fbae5ffd95aa939139a9f0cc46a9044887a76d0905a76b4f4da75144eaa6768364
  | 7, 0 => 0x1eb9c8591eb180c41dbf2e791d0c61251c4478291c1160c61c02e4e51bd38e271b96e8611b6588df1ae554351a53497619b15e68196939d2186b8f5c17a485a01780280516ed244d168319a4167ebc1d1658ec56161ad83315303b88147be17a147387c814445611141f8fdd140ddc3213b478a2136b9aa4131d3b5411f546a611c9fc59108cbea2106602d20ed48efb0ecd7e060eccb7400de1f81f0dc479fe0db6ae630db3a33c0d359d660c0c577e0b8bbf6b0ae68dfb0a6e47250a4a1809093db6800801277907540f08052b8f990499b2c1046cf47e0451cc9a0402104d03a5f4b302fbbdeb02ded44202c7e1c602b75e6a01c0cf2f00f26ece00339b29
  | 7, 1 => 0x452bb7f644fa104944aae86243cfd02243a4ce574323f83b42a809fe40bc65a3404e605b400015073fd89f2f3ef2c9303e51fe3b3d7b1e3a3cedab6d3cc117773c153f903bcc4b8e3a9cdd1a3a2919be386dc675376a4f6935db23933578c84e352ef43834bd92e333c5ae8333ac494933641e9c33513a6031c32ec3315f0dca30b17a1b30a94148301873802ffd69612f474c872ee5f83b2eb1aa0b2db401b12d6782ad2ceb381e2cc710002c4612372b5379482ad2a9b42ac299d128a5bcb4288ecc2f2880e0ed280c08152572009524f1d90e24c4815c242a74e0241a19e72358f6eb22929d1c225227cd21f40ce0212e1271212bd53220bd10b4200848ee
  | 7, 2 => 0x7ad0785279fc07f679200ff077cbd182773a3b4c764d3db57319db9a71e7969571cce639716c3c1f714ddd1f6ee55b736d7b8cdc6c322cc86bf88c416afb3f0269904ec9690b0d39680ccfb7679e3ab86722ad006608c413655e0be164ca439b644d15206438425e6430b85d63d8096f621ba7bc60fe170c60a67754608a602b6014a9d06013f4555e4f53365e4e7aea5d017f515a910ab5595bb8d458bcfd23555e780a54e640dd537f76e65310cae851a4824251529dc4509f8ca3509cfade4f1c75a54e793bc74d69b8694d2885244cf4df914cae6cf64c50a0f34c1021324b550f7148a30f48487c560147c09368477294e646e757da4691d9b84621c469
  | 7, 3 => 0xedcb4794ec4ae460e9a376e3e6527f1ce4271949dabcacbbd5f72ec6d43a869fd24ac501cdc8ba32cd54eb62cd52d7cdca2c216cc867804dc3d12e09c2d474bfc060a091c016ba9bbf1a8222bd15572dbb5f66ffb8db3bf4b7f96484b749d50ab5e0fc76b03b1c5fb0049811aba7945fa9f0cc46a9536d8da888922ba77db8c7a76d0905a4234630a32013a5a304b735a039bc45a022680c9ca6bdbc9c31e4e49c26fc249bea8a5f9b773ae198a6ec6897e4107296f519d994dbd1b494acc95291869cbe8f8b65ae8f0950aa8c0dbe5a8b9a7c8c8ac1d32888c8f86086c3604984fd814c84135e9583b31a7d83490ab0824ebd76805efbd87db0481d7c3a5205
  | 7, 4 => 0xf92dd199f5b2a9a3f1dccc71
  | 8, 0 => 0xf92dd199d43a869fc0a94172b749d50ab03b1c5fa42346309437159c8ff96af68f8b65ae77cbd1827319db9a69904ec962a89ff75d017f514e31041e44efaef6448b58423ef2c9303e51fe3b3d084ce7358f846f242a74e01a534976196926bf1957081117a485a0167ebc1d
  | 9, 0 => 0x69904ec9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffaaaaaaff000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000fafafafaf0f0f0f0000000000000000000000000000000000000000000000000eeeeeecccccccccc000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000fafac8c8f0f0c0c0000000000000000000000000000000000000000000000000eeeeaaaacccc0000
  | 0, 1 => 0xff00aa00ff000000000000000000000000000000000000000000000000000000aaaa888800000000000000000000000000000000000000000000000000000000fefe0000fcfc0000000000000000000000000000000000000000000000000000c8c8c8c8c0c0c0c0000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000ffaaaa00ff000000000000000000000000000000000000000000000000000000cccccccccccccccc
  | 0, 2 => 0xcccc0000cccc000000000000000000000000000000000000000000000000000000ffff0000ffff00000000000000000000000000000000000000000000000000f0f00f0ff0f00f0f000000000000000000000000000000000000000000000000a5a5a5a50f0f0f0f000000000000000000000000000000000000000000000000fac8fac8f0c0f0c0000000000000000000000000000000000000000000000000eeeeeeeecccccccc000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000faeaeaeaf0c0c0c0
  | 0, 3 => 0xc3c3c3c3c3c3c3c3000000000000000000000000000000000000000000000000fafa0000f0f00000000000000000000000000000000000000000000000000000ccccc8c8ccccc0c0000000000000000000000000000000000000000000000000eeeecccccccccccc000000000000000000000000000000000000000000000000ffffff00ffffff000000000000000000000000000000000000000000000000009999999933333333000000000000000000000000000000000000000000000000ffffc8c8ffffc0c0000000000000000000000000000000000000000000000000aaaa55550000ffff
  | 0, 4 => 0xff00ff00ff00ff0000000000000000000000000000000000000000000000003333333333333333000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000ccc0ccc0ccc0ccc0000000000000000000000000000000000000000000000000aaaaaa8800000000000000000000000000000000000000000000000000000000aaaaaa0000000000000000000000000000000000000000000000000000000000ff0000ffff0000ff000000000000000000000000000000000000000000000000cccc3333cccc3333
  | 0, 5 => 0xffc8ffc8ffc0ffc0000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000000000000000000000000000000000001111333333333333000000000000000000000000000000000000000000000000ccccccccccccc0c000000000000000000000000000000000000000000000000055555555ffffffff000000000000000000000000000000000000000000000000050505050f0f0f0f000000000000000000000000000000000000000000000000faf0faf0f0f0f0f0
  | 0, 6 => 0xf0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000005500ff00ff00ff000000000000000000000000000000000000000000000000ffaaff00ff00ff000000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c00000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000f0c0c0c0f0c0c0c0
  | 0, 7 => 0xccc8ccc8ccc0ccc0000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000000077770000ffff00000000000000000000000000000000000000000000000000ff00ff00ffffff000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000eaeaeaeac0c0c0c0
  | 0, 8 => 0xaaaa000000000000000000000000000000000000000000000000000000000000f0f0f3f3f0f0f3f3000000000000000000000000000000000000000000000000ccffccffccffccff00000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000088888888000000000000000000000000000000000000000000000000000000001111111133333333000000000000000000000000000000000000000000000000ffaa0000ff000000000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0
  | 0, 9 => 0xff000000ff00000000000000000000000000000000000000000000000000ffaaff00ffaaff00000000000000000000000000000000000000000000000000ffff0000ffaa0000000000000000000000000000000000000000000000000000ffc0ffc0ffc0ffc0000000000000000000000000000000000000000000000000ffff8888ffff000000000000000000000000000000000000000000000000000000ff00ff00ff0000000000000000000000000000000000000000000000000000f0f0f0c0f0f0f0c0000000000000000000000000000000000000000000000000ffffaaaaffff0000
  | 0, 10 => 0xaaaaaaaa80808080000000000000000000000000000000000000000000000000050f050f0f0f0f0f000000000000000000000000000000000000000000000000ff00ff00ff00cc00000000000000000000000000000000000000000000000000ffff0000ff000000000000000000000000000000000000000000000000000000f8f8f8f8f0f0f0f0000000000000000000000000000000000000000000000000ffffffccffffffcc00000000000000000000000000000000000000000000000050505050f0f0f0f0000000000000000000000000000000000000000000000000ff00ffffff00ffff
  | 0, 11 => 0xfa00fa00f000f000000000000000000000000000000000000000000000000000ffffc0c0ffffc0c0000000000000000000000000000000000000000000000000ff00ffccff00ffcc000000000000000000000000000000000000000000000000ffff0000fff00000000000000000000000000000000000000000000000000000faaaaaaaf0000000000000000000000000000000000000000000000000000000ececececcccccccc000000000000000000000000000000000000000000000000ffff00ccffff00cc0000000000000000000000000000000000000000000000000f3f0f3f0f3f0f3f
  | 0, 12 => 0xf0f00000f0f000000000000000000000000000000000000000000000000ff00aa00ff00aa00000000000000000000000000000000000000000000000000aaaaaa00aaaaaa00000000000000000000000000000000000000000000000000eeee0000cccc0000000000000000000000000000000000000000000000000000bb33bb3333333333000000000000000000000000000000000000000000000000ffaaffaaff00ff00000000000000000000000000000000000000000000000000aa00aa0000000000000000000000000000000000000000000000000000000000fffafffafff0fff0
  | 0, 13 => 0xf0f0c0c0f0f0c0c000000000000000000000000000000000000000000000000aaff00ff00ff00ff000000000000000000000000000000000000000000000000ffccccccffcccccc000000000000000000000000000000000000000000000000f0e0f0e0f0c0f0c0000000000000000000000000000000000000000000000000ffeeccccffcccccc000000000000000000000000000000000000000000000000f0f0f0f00f0f0f0f000000000000000000000000000000000000000000000000ffff0000ffff00ff000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc
  | 0, 14 => 0xff00fa00ff00f000000000000000000000000000000000000000000000000000aaffaaff00ff00ff00000000000000000000000000000000000000000000000000aa00aa0000000000000000000000000000000000000000000000000000000000ffffff00ffffff000000000000000000000000000000000000000000000000f0f0e0e0f0f0e0e0000000000000000000000000000000000000000000000000afafafaf0f0f0f0f000000000000000000000000000000000000000000000000aaaaaa88aaaaaa88000000000000000000000000000000000000000000000000eecceecccccccccc
  | 0, 15 => 0xff00aa00ff000000000000000000000000000000000000000000000000000000ff55ff00ffffff000000000000000000000000000000000000000000000000f0faf0faf0f0f0f0000000000000000000000000000000000000000000000000ffee0000ffcc0000000000000000000000000000000000000000000000000000f0f0fffff0f0ffff0000000000000000000000000000000000000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000aaaa5555aaaa5555000000000000000000000000000000000000000000000000fefe0000fefe0000
  | 1, 0 => 0xf0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000fcccccccfccccccc0000000000000000000000000000000000000000000000000055005500ff00ff000000000000000000000000000000000000000000000000c0ffc0ffc0ffc0ff000000000000000000000000000000000000000000000000ff00ff55ff00ffff0000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000fefefefefcfcfcfc000000000000000000000000000000000000000000000000a0a0a0a000000000
  | 1, 1 => 0xfaeafaeaf0c0f0c000000000000000000000000000000000000000000000000088ff88ff00ff00ff000000000000000000000000000000000000000000000000cc88cc88cc00cc000000000000000000000000000000000000000000000000008f8f8f8f0f0f0f0f000000000000000000000000000000000000000000000000fafaf0f0f0f0f0f00000000000000000000000000000000000000000000000009999999999999999000000000000000000000000000000000000000000000000003f003f003f003f0000000000000000000000000000000000000000000000002222222200000000
  | 1, 2 => 0xfffffffff0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000e0e0e0e0c0c0c0c0000000000000000000000000000000000000000000000000151515153f3f3f3f000000000000000000000000000000000000000000000000af0faf0f0f0f0f0f000000000000000000000000000000000000000000000000070707070f0f0f0f000000000000000000000000000000000000000000000000f2f2f2f2f0f0f0f0000000000000000000000000000000000000000000000000ff88ff88ff00ff00
  | 1, 3 => 0xffffffaaffffffaa000000000000000000000000000000000000000000000000aaaaaaaaffaaffaa000000000000000000000000000000000000000000000000faaafaaaf000f00000000000000000000000000000000000000000000000000055005500ff00ff00000000000000000000000000000000000000000000000000f0fff0fff0fff0ff000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000ffeeffeeffeeffee00000000000000000000000000000000000000000000000000000000aaaaaaaa
  | 1, 4 => 0x5555555555555555000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ffaaaaaaffaaaaaa000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000f000f000f000f000
  | 1, 5 => 0xffff0000ffcc0000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000000000000cccccccc000000000000000000000000000000000000000000000000f0f0f000f0f0f0000000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000aaaaaaaaaa00aa00000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0
  | 1, 6 => 0xfffafffafffafffa0000000000000000000000000000000000000000000000003333000033330000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000ffff0000f0f0000000000000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff00aa00ff00aa
  | 1, 7 => 0xeaeaeaea00000000000000000000000000000000000000000000000000000000ffffffffeeeeeeee000000000000000000000000000000000000000000000000ffffffff0000ffff000000000000000000000000000000000000000000000000aaaaaaaaafafafaf000000000000000000000000000000000000000000000000ffff0000cccc0000000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000aaaaaaaaeeeeeeee000000000000000000000000000000000000000000000000fff0ff00fff0ff00
  | 1, 8 => 0xffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000aaffaaffaaffaaff0000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000ff55ff00ff55ff00000000000000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000ffff000000000000
  | 1, 9 => 0xfff0fff0fff0fff0000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000ffffffffffffaaaa000000000000000000000000000000000000000000000000fcfcfcfcf0f0f0f0000000000000000000000000000000000000000000000000ff00ff00ff00ffff000000000000000000000000000000000000000000000000eecceecceecceecc00000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000000000555500005555
  | 1, 10 => 0xfffffffff000f000000000000000000000000000000000000000000000000000ffffffff11111111000000000000000000000000000000000000000000000000f0a0f0a0f000f000000000000000000000000000000000000000000000000000ff00fa00ff00fa000000000000000000000000000000000000000000000000003300330033003300000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000000fafafafa000000000000000000000000000000000000000000000000ffff00ffffff00ff
  | 1, 11 => 0xfff0fff0f0f0f0f0000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000ff00ff00ff000000000000000000000000000000000000000000000000000000ffa0ffa0ffa0ffa000000000000000000000000000000000000000000000000022222222222222220000000000000000000000000000000000000000000000000000cccc0000cccc000000000000000000000000000000000000000000000000aaaaffff0000ffff00000000000000000000000000000000000000000000000055550000ffff0000
  | 1, 12 => 0x5555555555005500000000000000000000000000000000000000000000000000aaffaaff00000000000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000fe00fe00fe00fe00000000000000000000000000000000000000000000000000ffffff00ffff0000000000000000000000000000000000000000000000000000ffffffffff000000000000000000000000000000000000000000000000000000ffffffff55555555
  | 1, 13 => 0xffffffff00550055000000000000000000000000000000000000000000000000c0c0ffffc0c0ffff0000000000000000000000000000000000000000000000000000aaaa00000000000000000000000000000000000000000000000000000000000000003f3f3f3f000000000000000000000000000000000000000000000000ffffcc00ffffcc00000000000000000000000000000000000000000000000000cccc8888cccc00000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000aaaaaaaaffffffff
  | 1, 14 => 0x44444444cccccccc000000000000000000000000000000000000000000000000fcf0fcf0fcf0fcf0000000000000000000000000000000000000000000000000ecececececececec000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000ffffffff00ff00ff00000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000ffffaa00ffff0000
  | 1, 15 => 0xfffcfffcfffcfffc0000000000000000000000000000000000000000000000001111111111111111000000000000000000000000000000000000000000000000ee00ee00cc00cc00000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000ff00cc00ff00cc00000000000000000000000000000000000000000000000000fcccfcccfcccfccc000000000000000000000000000000000000000000000000ffffccccffff0000000000000000000000000000000000000000000000000000cccc8888cccc8888
  | 2, 0 => 0xeeeeaaaaeeeeaaaa000000000000000000000000000000000000000000000000ffa0ffa0ff00ff00000000000000000000000000000000000000000000000000ffeeffeeffccffcc000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000fffffafafffff0f0000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000aaaaaaaa888888880000000000000000000000000000000000000000000000000f0f0f0f00000000
  | 2, 1 => 0xf0000000f00000000000000000000000000000000000000000000000000000005555555544444444000000000000000000000000000000000000000000000000ffffffff55550000000000000000000000000000000000000000000000000000ccccc0c0ccccc0c0000000000000000000000000000000000000000000000000aaaaaaaaa0a0a0a0000000000000000000000000000000000000000000000000fffffff0fffffff0000000000000000000000000000000000000000000000000fffffffffcfcfcfc0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c
  | 2, 2 => 0xccccccccc0c0c0c0000000000000000000000000000000000000000000000000fffffffffafafafa000000000000000000000000000000000000000000000000cccccc00cccccc00000000000000000000000000000000000000000000000000000055550000ffff000000000000000000000000000000000000000000000000aaaaaaaafafafafa000000000000000000000000000000000000000000000000fc00fc00fc00fc00000000000000000000000000000000000000000000000000fff0f0f0fff0f0f0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0
  | 2, 3 => 0xfffff0f0f0f0f0f00000000000000000000000000000000000000000000000003333333300000000000000000000000000000000000000000000000000000000fffff000fffff000000000000000000000000000000000000000000000000000ff00f000ff00f000000000000000000000000000000000000000000000000000faaafaaafaaafaaa0000000000000000000000000000000000000000000000000a0a0a0a00000000000000000000000000000000000000000000000000000000ffffffaaffffff00000000000000000000000000000000000000000000000000ccccffffccccffff
  | 2, 4 => 0xfffffafafffffafa000000000000000000000000000000000000000000000000ffffff00ff00ff000000000000000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000ffffffffcccc0000000000000000000000000000000000000000000000000000fefefefefefefefe000000000000000000000000000000000000000000000000fcfcfcfccccccccc
  | 2, 5 => 0xf8f8f8f8f8f8f8f80000000000000000000000000000000000000000000000000f000f000f000f00000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000000ff88ff88ff88ff88000000000000000000000000000000000000000000000000ffccffcccccccccc000000000000000000000000000000000000000000000000ffccff00ffccff00
  | 2, 6 => 0x5050505050505050000000000000000000000000000000000000000000000000fcfcccccfcfccccc000000000000000000000000000000000000000000000000ffffffffc0c0c0c0000000000000000000000000000000000000000000000000ffffa0a0ffffa0a0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x4810106070300cc0a0401980802003
  | 4, 0, 0 => 0x38080c1c40d81c08084088080c1a402818060b40c808081240101810184010042e0b4030201616401054100b408808101440880826124088082008407818100e401034180b404818100b40500808004
  | 4, 0, 1 => 0x2818102340381810224028101022410818100b401018400b4088083e0b4010783a0b4
  | 5, 0, 0 => 0xc40406040a94003103020162750004404300402d4001117810100b5000b80406100b54002e088083e2d5000440406058b14001101018560b5000440408150a540011128080812500044100b1489d400111402016275000440c1c0589d40011078181626501014081e0402d8001112818480b5
  | 5, 0, 1 => 0x4404041f82d40002058986e345000444a061f0a9400111a81816265000f4043c058994000203020163b5000440c08058e94001901018100b5000140c08058e5400110101870085000440408150dd400110402c6e275000d40a060402d400110302016365000d40c08058d140011010cc16325
  | 5, 0, 2 => 0x1380a060402d4000a07818100b50013404060402d4004c03020163450012c0c080589d4001103020164a50004404490402d400110782016375000b84206040b540048010188e2650002804060002d4001101118100b5000440c4505911400110101886425000d482060402d4003d01100100b5
  | 5, 0, 3 => 0x4404040902140011010101626500044045b030214001101010b40850006c0a06058994005901018100b5000440408059614001103020ae27500044040805959400112a818100b5000080808058d14005401010100b500044a6080589d4005202818100b500044100b2889d4005003020164f5
  | 5, 0, 4 => 0x140c080599540048010208e3750002804063202d4001101018c60b5000080c2a130d140006058984e345001880c08308d1400113017c100b50002804040b82d4005e01010100b5001740c08058d14004101010100b500044040409031400111a820163750017004060402d400110302054275
  | 5, 0, 5 => 0xf478080589d40011010187e0b50006c0a08058dd4001101020166f5000440c083702d4366d02818100b600044046c0402d4d64101018100b600044046a040b54006901018100b5001888206041854001107818102a50004404680602d400021e0201667500044cc0605899400110101000085
  | 5, 0, 6 => 0x44ee040402d4000203020163450015004060402d40011010a84c37500044cc08058dd4001103020ec7550006c0c08059d140011011cc100b5000080c38040d140002040a86e345000440408390a540008058dc4e345000b80a06041c540011011c016375000f4043c040a94000206810100b5
  | 5, 0, 7 => 0xf4041e0402d400020202c4c3450004404400589940011010a8a2265000440e06041854000220020163450006c0a06040a940002040a8a23450017804060402d4004101018100b500044040609031400023d820167a5000b80406041e54001126018102a500044040605899400023c018100b5
  | 5, 0, 8 => 0x4404810602d400020202100345000081a060402d4001103808080850006c1e060402d4001103020167f5000440c08059f940011010201637500044040409099400113e820162750002804400b82d4007c01018100b5000440408058a540006040a84e345000080812040d140011031c016275
  | 5, 0, 9 => 0xb8220203229400110302016895000080c0b130d14001b02810100b5000440404132214002e030205a165000090e08058d14002e01054102d50004404860302d400113b818100b5000440c0830a154001103021080b500044040440099400110104c100b50004506060402d40011030f816825
  | 5, 0, 10 => 0x44040b130a54001103020168e5000444a064682d400021402016345000080a060e02d40011011c81626500044040805a314001101010542650006c0e060402d40002041c816345000080808150d140002340cc1634500010100b138d1400020304886345000440440040a9400110122c16265
  | 5, 0, 11 => 0x44040404145400110102ca22650006c0a060402d422020281024086000440404041094001101021002950004404041c021400110104886375000280417058dd400110102c4c375000940c3e058d140011010201692500044049105899400110104810295000452008058dd400110123c100b5
  | 5, 0, 12 => 0x440408390a940011011a0662a5050940a060402d800410302016275000440406150994000503020162250881c04060902182207010100c0860004404044a821400060402c4e345000440406042514001101021260b5
  | 6, 0, 0 => 0x4548060402c4ec0008a8c04060402d80011012880ca1043000220650020162760004404060402ca2c004f84404060402d8002e088080c084f30005c11030205a89600044049d0302016c00088080c0805a71800114d818100b13b00022060402d342760004532020302016c004b8440408058dd80011010185a264c30012e024b0205a346
  | 6, 0, 1 => 0x4404060402d5ac00088080cac0402d8000203020163455b0005c020302154346000b8a8020302154c00088940408058dd80002020205a0b1a3000220229818100b6000b804065482068c001704480081689d8001101019500805b0005c1b0281810a76000b94c060429468c00170441e06040b58001101100102d05b000220203280102a6
  | 6, 0, 2 => 0x4570020302016c0008adc04060402d8001101018100b5b300022020302016b560004404041e02016c000880968040402d80011598080c0805b00004060429c68b26000b8b206040b44ec00088080c0805ac58002e08818102d5830005caf01018102d6000b804060589868c00170440c085709d80097088092c2d1330005c02340cc5a346
  | 6, 0, 3 => 0x2f422020302016c0001018100b538d180011010194e265930005c110101810bc6000080a060402c68c0008aec04060402d80011030205a2a13b0005c1107818100b6002e822020302016c00088080812040b58002e088080caa133000220203254100b60004404041682c4cc00088080c085cac98004801018100b1a30005c11530194a266
  | 6, 0, 4 => 0x4404050302c4cc00088080c0b130d18001101018100b61b00022020405c163760004404680402c6ec0001018100b218d18002e08818102d6130005c114d8205ac160012022020302c4cc000004404061c0214000008808102a1ba801800202818100b6000002208058dc4ea001701810a7138d180000088080cbf0428017c1101018100b6
  | 6, 0, 5 => 0x440c080589d82c00170459606040b58001101019940805b00022060402c54276000b82206538984ec0017044cc060429d8001101018162664b0005c020302134c8600044040605a9c4cc0008b000406058998002e639980c084d30018cc0010205a3760004404040902016c00088080c0805b158001103021880b13b00022060402cc2276
  | 6, 0, 6 => 0xb86202030b44cc000d84404040402d8001101018100b6930002202040b46e986000440406040b5a2c00680440c080589d8001167809400805b0017411033385a2760033422020302016c00638080c08058d18001151018102d13b0005c02040b46e3460004404cc0302016c00171500408168dd80011480080c0805b000001101018100b5
  | 6, 0, 7 => 0x4404060436416c004b8440406040a98009708818100b13b000222501018240b6000440406040a9b0c006384404060589980011310080c0805b0005c11010b44c3760035c22020302016c00170940c3e168d1800d6088080c0816b0005c3d010f0100b6000b82225438f85ac00088080cd50402d8002e08b500c0816b00022020302c4cd36
  | 6, 0, 8 => 0xb82202042a86ec00700080c08538d1800116f8080c0805b000001101100100b50004404066f02016c00173740c08168d180011128080c0815300022cf01018100b6000444a060402c4ec0000044040815145400116e0080c0805b0005c0a0105c5a37600044040605899b6c0017008100b1b8d1800020302016346d3000220203070100b6
  | 6, 0, 9 => 0x22020202c4ca00700440406538998226d010140c0805b8005c1b02818102d60012022020402c6ec000881810e61689d800e508808080805b00022020429c6eb260039004060402c68c0017045c606040b58001101010100b13b0005c110102c4c376000b9c405030205ac00708454806040b58000001010100b1a280004060402c684f6
  | 6, 0, 10 => 0x4404045082016c0008808100b538dd8001160008100b1bb0000406040b468b26000080c08058dc68c001704498060402d8002e0101810e81a3001c8110101816266000002206040a84ea00088090e0816ac9800a601018100b1a300022020282016376000b8220203021cec00000440404090214001101018100b22300022020402c6e346
  | 6, 0, 11 => 0x80c08058d1dac001706c0a060402d8001101018102d76300090110101810476003ac22020302016c00088080c087502d800110102016431bb000140202818100b60004404060405c54c0008808d006040a980011030202e0b13b00022020302016e9600044d0060402c4ec001704410a71b89d8001167a80102d593000144801018100b6
  | 6, 0, 12 => 0x2822020302c4cc0017018102d138d18000203020660b1a30000406040b416346000080c0805bc468c00088192c080589d80011010185a26593000a802030205a0b6000440406058986ec00170450e081689d800f0088080c0805b0002202020207c0b6003bc2202030205ac00170080c08770b58002e088080ce81330007a1101010100b6
  | 6, 0, 13 => 0x22020202100a0008809ec060402d80011011a0662d5930002202033d4100b6000b82206168984ec0017044cc06040b5800110101952085930002202030b4162660004404060402ce8c00088080ca95f821800117a0080c0805b00014020305c5ab26001780406040b564c000880968060402d800c708808100b1bb001e611030205af26
  | 6, 0, 14 => 0x4404060902016c000880808060402d85c0a128140c0816b8005c110302154276000440468198b416c00088080ca90402d8001101018b40805b001f21101018100b6000440406043e016c00050080c171682d8001101018100b19300022020302016f76000b8bc06040b44ec000d8440a060402d80011128080c3e05b0005c060402c4e346
  | 6, 0, 15 => 0x2e804060402c68c00088080c08150d1800a6188080c0805b0012e11012d0100b6000440c080589c68c00240440406040a98004808818100b13b00022020302016fc60039022020402c6ec0008809f6060402d800e2088080c0805b00022026e818100b60038022020429c6ec00170440406150998001101020e42d05b00022027d018100b6
  | 6, 1, 0 => 0xc40406040b416c004b84404060440580011010201637803001741101018162660004404060002016c0001018100b130d1800117f8080c0805b0002202040b46eb260004404060402dfcc00170440408740dd8001101018100b3d30002202040b4162960004404067e82016c00188080c0816ac980011010140c08153000361101018100b6
  | 6, 1, 1 => 0x440406810b44cc0008c1404060402d8002e02818102d1cb000220203020162760031c22020302054c00240441e060402d8000008b3d400805a8000002030201634500000a8020302016a0008808102d058dd800110102016f11bb000001148018100b5000b82202198b464c00088080c0805c118010308808080805b0000406810205a346
  | 6, 1, 2 => 0x82020302016a001704404061c0218002e08808102a1bb00004060436416346000b822020342c4cc008504404060402d8002e010b44c371a300000110122c100b50042422020302016c00000440406058994001101020163784300022020341c100b6000460c020302016c000889404040402d8002e1e808782d133001ca1101018100b6
  | 6, 1, 3 => 0x44049b0302016c00088092c0816bf180011011a0080805b000001101020e40b5000b89a02030205ac00000440404040a9400110103c0c0805b0000011011a0660b5050444a020302016e000004404060910d400cf01018100b1a3000000a010182e0b5000b82202230205ac000017804060402d4002e088188a2d223000220203114100b6
  | 6, 1, 4 => 0x4342202030214ec000894004060402d8002e0d8140c2d13300022020402c4c376000440a060402cc2c00050440c080589d8000008808100b14a80022020302054376000b80404040b468c001704404a1788dd80000088080c1c05a8005c5202818102d6002e822020402c6ec00088080c088602d80011678080c0b1330005c50030205a4f6
  | 6, 1, 5 => 0x440406040a8a2c002404404040402d8002e02818102d32b00022020343c100b60004404061e02c4cc00088096806058998002e030b44c271a30005c1101022163760004404060402c72c00000440408058dd4002e088080c08873000226d01018100b6000440406040cc54c00170440404168998001101408102d1bb00022020402c6ec36
  | 6, 1, 6 => 0x2e822020302054c000004404080594540011010100c0b133000231101018100b60006c90020302016c2e0d9b40a06040b5c0011260080c0805b002061101018100b6000080c120402c68c00010100c08058d18001167808100b1bb00022020302e202660004404062002016c00088080a040402d8002e010f0102d33b000220202020180b6
  | 6, 1, 7 => 0x4404060402e28c000881c04060402d8002e1e8f0102d13b00022020302226b260006c22020302c4cc0008808085f0402d8001101018102a133000220289018100b60000022022982016a002904404060402d8001b01018100b1a3000222501018100b60004404040304810c001706c0a08168dd8002e08808102d37b00022020304816266
  | 6, 1, 8 => 0x4404120402c6ec00088080808058dd8001101018111505b00022cf01018102a6000459e060402c4ec00170080c08168d1800000101816261a28002202020201629600044040605a004cc001706c0c08169d180011011a00c0805b0005c1101011420860000022020302054a00170205a37138d1800020302016801a30002202168986eb26
  | 6, 1, 9 => 0x46422020302016c000101a3008058d18002e08808102d14b00022020302016c960000022350302016a00088080a060402d8001101018100c05b0005c11011005a2660004404060589910c000d8440408058dd8001101010103305b00022020302c8e2660004404810202016c00010194008058d18001101018111705b0022c1101018100b6
  | 6, 1, 10 => 0x6c22020302054c000006c0a060402d40011128090e0805b0007a0a01018100b6000b822061f0b504c0008808080805899800110102016471bb000220203048102a60004404040302054c00088080c0b15099800110117c0c0805b00022020302054f76000002202058986ea000012004060411d400110122c0c0805b00004060402cc2346
  | 6, 1, 11 => 0x8808100b1bc698002e088080cf17f300022020302017086088080a060902016e110101408060402dc001101018100b213000220234018162660004404061c02016c0008808100b150dd80000088080c2a132800220240818100b6000080c080b82c68c0000018100b138d14001101018100b14b000001101010100b5
  | 7, 0, 0 => 0xba3e1101018102d7000b82202032845a267000b80406040f85a347000b822025a01942087000b82202030b44d1e7000ba3a1101018102d7000b822cf030205a277000b822028e018102d7000459e02030205a0b7000b822028d818102d7000b82202030202e0b7003185c02030205a347000b8220234018100b7003945c11010185a267000b80406508205a347000005c1101018102a6
  | 7, 0, 1 => 0xb82202030214e377000b8220290018102d7000b822a60101810a7700001c01101018102d6000b83611010205a377000005c110101942f16000b87a11010185a26700001741101018100b6000b82206040b44e447000b804a4030205a347000b80406500205a347000b80405030205a9a7000b82202043385a377000b80406040b534347003945c110101810aa7004585c1101018102d7
  | 7, 0, 2 => 0x5c3d010f0102d6000b82202030205b237004885c1101018102d7000b82202030205a34700000220203408102d6000b8225401018102d7000b8901101018102d70004404061e0205ab27000b8a002030205a347000b82202032805a267000b8220290818102d70004404b4030205ab27000b814110101810a7700000220203020162660031822c001018102d7000b82202030b534267
  | 7, 0, 3 => 0xb8901101018100b7003945c11010205a377000b804068c0205a347000ba4e1101018102d7000005c1101018110b6000b822b4030205a277000b82202040b46e2770004404061e0205a0b7000ba4c1101018102d70004404b4030205a0b7000005c02040b46e34600000001101018100b5000b822020302066a77000b82202030205b257000b82202030205b247000b8220202818102d7
  | 7, 0, 4 => 0x22cf01018100b6000440406090205a0b7000440404030205a0b7000b8232801018102d7000b82202508205a377003cc5c1101018102d7000b98e1101018102d7000b82206040b44ef27000b81411010182e2d700000226201018100b6000b8bc1101018102d7000005c11010b44c376000b8220202818100b7000b82202030205ad37000b82206040b620277000b822020302016347
  | 7, 0, 5 => 0x5c1b02818102d6000b83611030205a277000b822250121c102d70006c2202030205a0b7000b87a0a01018102d7000b82202040b534377000005c1101018112b6000b98e1101018100b7000b82206043385a277000b8232a01018102d7000b8232901018102d7002e85c110101811017000b82202040f85a377000b87a11010205a377000005c1126018102d60006c2202030205ab27
  | 7, 0, 6 => 0x406040b416346000002202030b44cb26004b45c1101018102d7000b82202030205a677000b82225010185a267000b82202030214e267000440406040b44eb27000b8220296018102d7003185c116e818102d7000000406040b468b260000022020302016a560025c5c11010185a267000005c1101010102d6000b82202030205a4f7002e85c110101810a77000b84a02030205a347
  | 7, 0, 7 => 0x440406040f85ab270000022020302017106000f42202030205ab27000005c11030b44c276000005c1133018102d6000002202030b416266000b82202040b46f2e7000002202030f0100b60000022025a018100b6000b804060405c5a347000b80468030205a347000b8141101018102d7000005c110101810a76000005cc701018109a6000005c1101010100b6000005c06040b44e346
  | 7, 0, 8 => 0xb82202030214f337000b8220203020660b700000220203048100b6000b8220299018102d700000220202018100b6000b87a11030205a277000b82202032585a267004c45c1101018102d7000b822023d818102d7003185c11030205a277000b8141101018100b7000ba601101018102d7000b8220297818102d7000b82202340185a267000b822020302016377000440406508205a0b7
  | 7, 0, 9 => 0x2202040b416376000b80406040b54e347000b80405030205a347000b822bb01018102d7002e85c1101018102d7000b82202030214ee97000b822b301018102d7000002202040b46eb26000b82225010205a37700000361101018100b6000b822a301018102d7000b82206500205a277000002202030219c0b6000b8229b030205a277000b8229901018102d70025c5c11010205a377
  | 7, 0, 10 => 0x5c1101018102d6000b82206040b44ec170000000110101816265000b82202030b44cc97000b82202030b54e267000b82206043105a277000b82202028185a26700001ca1101018100b6000b822025a01810a77000b82202030b44c347000b82202030205ac37000b82202340205a377000002202030201627600000000203020163450000022020302016806002f85c1101018102d7
  | 7, 0, 11 => 0x5c110101810ae6000b80406040b4684f7000005c1101100102d6000b822cf01018102d7000b82225030205a277000005c11012d011106000005c1101018100b600000220203021d0b260025c2202030205a0b7000002202030207c0b60000022020302016476000b82202030b44cd37000b82202030205ad27000b822020302016267000b822cf01280102d7003345c1101018102d7
  | 7, 0, 12 => 0xb82202030205a747000b822025a018102d7000b822020328410a7700000220203020162a6000b80406040cc5a347000b82202030b44c377003945c110101810a77000b8140202818102d70000000110102016375000b82202040b54e377000b80406040b46e347003905c11010185a267000b82202028205a37717044da0202818102d8000440468030205ab27003905c02030205a347
  | 7, 0, 13 => 0x1101018102a5000b8361101018102d70025c5c11012d0102d7000b82206040b44e347003905c11010205a377000b822027d818102d7000b8220203048102d7000b8220202018102d7000440405030205ab27000b82202030b41626700000222501018100b60025c5c1101018110b7000b82202030205a327000b8361102818102d7000b80406040b416347000b822027b018102d7
  | 7, 0, 14 => 0x5c11011a0662d617028222501018102d8000005c110101952086000005c0a010182e2d6000b8220203114102d7000b82202040b416377000ba141101018102d7000005c11010185a266000b82202040b46f087000005c02030205a3460031c2202030205a0b7000b82202040b46f00700000220234018100b6000b80406040b44c347000b822ff01018102d7000b82202030205afe7
  | 7, 0, 15 => 0x22020302016376000b8a41101018102d7000b8231101018102d700001c81101018100b600000001101010100b5000440406040b564ad7000b82202030205a397000005c11010205a376000b8226d01018102d7000b8225001018102d70000022020302016436000b82202040b44c3770000022020302016a7600000220202818100b6000b8220203284100b7000002202030214eb26
  | 7, 1, 0 => 0xb8220234018102d700000220203020660b6000b83611010185a267
  | 8, 0, 0 => 0xb82202030205ac2e088080c0816899d742e088080c0816b8b82202030205a0b7170440406040cc5ae2e088080c0816bc5c5c0a088080c0816b8005c110101810a76170440406040b46eee4170440406040b5c5cc7088080c0816b800001101018100b5170440406040b54ee2e08b000406040b5c5c11010140c0816b8b82202030205a347
  | 8, 0, 1 => 0x2e08808d006040b5c002e08808102d1bb0b82202030207c2d7000b82202030b44cc00170080c08168d185c1b088080c0816b8b82202030205b1071704404061e0205ae2e088096806040b5c5c11678080c0816b8005c1101018100b6
  | 9, 0, 0 => 0x5c1101018102d6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 31
  | 4 => 40
  | 5 => 58
  | 6 => 67
  | 7 => 76
  | 8 => 67
  | 9 => 58
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 9 0) :: stateWires n (ids >>> 9)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x38001c7f80000000000000000000000000000000000000000000000000000000070e1e007c0f81800000000000000000000000000000000000000000000000003800000f80000000000000000000000000000000000000000000000000000000070e1e707c0f818000000000000000000000000000000000000000000000000000e1c18003e07c70000000000000000000000000000000000000000000000000380fe00f800ffe00000000000000000000000000000000000000000000000000070000007c00000000000000000000000000000000000000000000000000000000e01c7003e0000
  | 0, 1 => 0x3800000f80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007e000007fe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c70000000000000000000000000000000000000000000000000000000003ff1c18ffff07c700000000000000000000000000000000000000000000000003800000f8000000000000000000000000000000000000000000000000000000000e1c18003e07c7
  | 0, 2 => 0xe0000003e0000000000000000000000000000000000000000000000000000007ffe0007ffffe000000000000000000000000000000000000000000000000000701e1f07c007e7000000000000000000000000000000000000000000000000038f1fd8f83f07e70000000000000000000000000000000000000000000000000000e0000000f800000000000000000000000000000000000000000000000000000e1ddf003e07c700000000000000000000000000000000000000000000000003ff0000ffff0000000000000000000000000000000000000000000000000000000001c700000000
  | 0, 3 => 0x3810207f80100200000000000000000000000000000000000000000000000000070000007c00000000000000000000000000000000000000000000000000000000e0000003e0000000000000000000000000000000000000000000000000000000e1c18003e07c700000000000000000000000000000000000000000000000003fffe00ffffffe000000000000000000000000000000000000000000000000003f1e220ffc1f83800000000000000000000000000000000000000000000000003ff0000ffff00000000000000000000000000000000000000000000000000000000fe380000ffff
  | 0, 4 => 0x7f01ff07ff001f00000000000000000000000000000000000000000000000003f1e3e7ffc1f838000000000000000000000000000000000000000000000000038efe18f83effe700000000000000000000000000000000000000000000000000001c00000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000038001fff800001f000000000000000000000000000000000000000000000000000ee3e7003ef838
  | 0, 5 => 0x380fe00f800ffe000000000000000000000000000000000000000000000000003ffffff00000000000000000000000000000000000000000000000000000000000001c7e739e73600000000000000000000000000000000000000000000000003f1e3e7ffc1f838000000000000000000000000000000000000000000000000000e1c18003e000000000000000000000000000000000000000000000000000003fffe38ffffffff000000000000000000000000000000000000000000000000038f1e18f83f07e70000000000000000000000000000000000000000000000000070e1e007c0f818
  | 0, 6 => 0x38f1e1ff83f07e7000000000000000000000000000000000000000000000000007f01ff07ff001f0000000000000000000000000000000000000000000000000380fe00f800ffe00000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003810207f801002000000000000000000000000000000000000000000000000003800000ff3900000000000000000000000000000000000000000000000000000000000000000000
  | 0, 7 => 0x1c00000007c000000000000000000000000000000000000000000000000000001c00000007c000000000000000000000000000000000000000000000000003ffe1e0fffff8180000000000000000000000000000000000000000000000000070000007c000000000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000007f01ff07ffffff000000000000000000000000000000000000000000000000000001ff0000001f000000000000000000000000000000000000000000000000000001c700000000
  | 0, 8 => 0x70e3e707c0f838000000000000000000000000000000000000000000000000007f1dff07ff07df000000000000000000000000000000000000000000000000000e0018003e0007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f1e220ffc1f83800000000000000000000000000000000000000000000000003800000f80000000000000000000000000000000000000000000000000000000070000007c00000
  | 0, 9 => 0xfe000000ffe00000000000000000000000000000000000000000000000000380fe00ff39ffe000000000000000000000000000000000000000000000000003ff0000ff3900000000000000000000000000000000000000000000000000000380fe00f800ffe000000000000000000000000000000000000000000000000003ff0000ffff0000000000000000000000000000000000000000000000000000007f01ff07ff00000000000000000000000000000000000000000000000000000070e00007c0f80000000000000000000000000000000000000000000000000003ff01c7ffff0000
  | 0, 10 => 0x1c700000000000000000000000000000000000000000000000000000000038f1e1ff83f07e70000000000000000000000000000000000000000000000000380fe00f80007c000000000000000000000000000000000000000000000000003ff0000f80000000000000000000000000000000000000000000000000000000070e1e007c0f81800000000000000000000000000000000000000000000000003fffe18ffffffe70000000000000000000000000000000000000000000000000070e02007c0f8180000000000000000000000000000000000000000000000000380fffff800ffff
  | 0, 11 => 0xe0000000f80000000000000000000000000000000000000000000000000003ff0000ffff00000000000000000000000000000000000000000000000000000380fe18f800ffe700000000000000000000000000000000000000000000000003ff0000ffc00000000000000000000000000000000000000000000000000000000001c700000000000000000000000000000000000000000000000000000000000e1dd8003e07c700000000000000000000000000000000000000000000000003ff0018ffff000700000000000000000000000000000000000000000000000003ff1fffffff07ff
  | 0, 12 => 0x1e1f000007e700000000000000000000000000000000000000000000000003800000f800e72000000000000000000000000000000000000000000000000000000000e739e720000000000000000000000000000000000000000000000000000e0000003e000000000000000000000000000000000000000000000000000003f1e3e7ffc1f8380000000000000000000000000000000000000000000000000380ffc7f800ffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f0ffe7ffc0fff8
  | 0, 13 => 0x38f1c18f83f07c7000000000000000000000000000000000000000000000000007f01ff07ff001f000000000000000000000000000000000000000000000000038e1c18f83e07c70000000000000000000000000000000000000000000000000000e1c00000f800000000000000000000000000000000000000000000000000038e1c18f83e07c70000000000000000000000000000000000000000000000000070e1e0f83f07e700000000000000000000000000000000000000000000000003ff0000ffff001f000000000000000000000000000000000000000000000000007efdf807feffdf
  | 0, 14 => 0x380e000f800f800000000000000000000000000000000000000000000000000007f01ff07ff001f000000000000000000000000000000000000000000000000000001c700000000000000000000000000000000000000000000000000000000007fffff07ffffff000000000000000000000000000000000000000000000000007001c007c0e010000000000000000000000000000000000000000000000000038f1fdff83f07e700000000000000000000000000000000000000000000000000000000e739e726000000000000000000000000000000000000000000000000000e1c18003e07c7
  | 0, 15 => 0x7f01c707ff0000000000000000000000000000000000000000000000000000007fffff07ffffff0000000000000000000000000000000000000000000000000070e1e707c0f818000000000000000000000000000000000000000000000000038e0000f83e00000000000000000000000000000000000000000000000000000070ffff07c0ffff0000000000000000000000000000000000000000000000000000e1e00000f8180000000000000000000000000000000000000000000000000000fe38e73918c9000000000000000000000000000000000000000000000000007e0000e7ff0000
  | 1, 0 => 0xe0000000f800000000000000000000000000000000000000000000000000000e1c18003e07c7000000000000000000000000000000000000000000000000007f003807ff001f000000000000000000000000000000000000000000000000007f01ff07ff001f0000000000000000000000000000000000000000000000000380fe38f800ffff000000000000000000000000000000000000000000000000007101e707c10018000000000000000000000000000000000000000000000000007efdff07feffdf000000000000000000000000000000000000000000000000000001c000000000
  | 1, 1 => 0xe1c70000f800000000000000000000000000000000000000000000000000007f01ff07ff001f00000000000000000000000000000000000000000000000000001c00000007c0000000000000000000000000000000000000000000000000038f1e1ff83f07e70000000000000000000000000000000000000000000000000070e1e007c0f81800000000000000000000000000000000000000000000000003f1e22018f81f0e000000000000000000000000000000000000000000000000007f01ff07ff001f000000000000000000000000000000000000000000000000000001c700000000
  | 1, 2 => 0x3ffffff07c0f8180000000000000000000000000000000000000000000000000070e1e000000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000003fffe38ffffffff000000000000000000000000000000000000000000000000038f1e1ff83f07e7000000000000000000000000000000000000000000000000038f1e1ff83f07e70000000000000000000000000000000000000000000000000070e1e707c0f8180000000000000000000000000000000000000000000000000380fe00f800ffe0
  | 1, 3 => 0x3ffffc7fffffff6000000000000000000000000000000000000000000000000000001c7ff39fff60000000000000000000000000000000000000000000000000000e1c70000f8000000000000000000000000000000000000000000000000000380fe00f800ffe0000000000000000000000000000000000000000000000000007fe1ff07fff81f00000000000000000000000000000000000000000000000000000000e7390000000000000000000000000000000000000000000000000000038effdfff3ffff700000000000000000000000000000000000000000000000000000000e739e736
  | 1, 4 => 0x3fffe3818c618c90000000000000000000000000000000000000000000000000380ffc7ff39fff600000000000000000000000000000000000000000000000000000000e000e7200000000000000000000000000000000000000000000000000380fe0000000000000000000000000000000000000000000000000000000000038001c7ff39e7360000000000000000000000000000000000000000000000000070e1e700000000000000000000000000000000000000000000000000000000000e1ddfe73fe7f70000000000000000000000000000000000000000000000000000e0000000f800
  | 1, 5 => 0x3ff0000f83e000000000000000000000000000000000000000000000000000003fffe380000000000000000000000000000000000000000000000000000000000000000003e07c70000000000000000000000000000000000000000000000000070e00007c0f8000000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000001c7e000e720000000000000000000000000000000000000000000000000000001c7e739e736000000000000000000000000000000000000000000000000000001c00700e010
  | 1, 6 => 0x3f0ffe7fff9fffe00000000000000000000000000000000000000000000000003f10000ffc10000000000000000000000000000000000000000000000000000000f001f003f00070000000000000000000000000000000000000000000000000070e1e7e7f9ff3e00000000000000000000000000000000000000000000000003ff000007c0000000000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000007f000007ff0000000000000000000000000000000000000000000000000000007f01c707ff0016
  | 1, 7 => 0x1c70000000000000000000000000000000000000000000000000000000003ffffffe73fe7f700000000000000000000000000000000000000000000000003ffffff0000ffff000000000000000000000000000000000000000000000000000001c7ff3fe7f700000000000000000000000000000000000000000000000003ff0000003e000000000000000000000000000000000000000000000000000003ffffff003e07c7000000000000000000000000000000000000000000000000000001c7e73fe7f700000000000000000000000000000000000000000000000003f0fe00ffc0ffe0
  | 1, 8 => 0x3ff01c7ffffe73600000000000000000000000000000000000000000000000003ffffffffff00000000000000000000000000000000000000000000000000000000000007c0f818000000000000000000000000000000000000000000000000007f01ffe7ffe73f000000000000000000000000000000000000000000000000038f0000f83f0000000000000000000000000000000000000000000000000000007fffff07ff18df000000000000000000000000000000000000000000000000007001e007c0001800000000000000000000000000000000000000000000000003ff000000000000
  | 1, 9 => 0x3f0ffe0ffc0fff8000000000000000000000000000000000000000000000000000e1c180000000000000000000000000000000000000000000000000000000003ffffffffffe736000000000000000000000000000000000000000000000000007efdf807c0f8180000000000000000000000000000000000000000000000000380fe00f800ffff000000000000000000000000000000000000000000000000000e1c18e03ee7e70000000000000000000000000000000000000000000000000070e1e007c0f8180000000000000000000000000000000000000000000000000000fe38000018c9
  | 1, 10 => 0x3ffffff0000f80000000000000000000000000000000000000000000000000003ffffff18c018080000000000000000000000000000000000000000000000000000e1c00000f8000000000000000000000000000000000000000000000000000380e000f800ff200000000000000000000000000000000000000000000000000380e200f800f8200000000000000000000000000000000000000000000000000000e3e70000f83800000000000000000000000000000000000000000000000000000000e7f9ff3e00000000000000000000000000000000000000000000000003ff01ffffff001f
  | 1, 11 => 0x3f0ffe007c0f818000000000000000000000000000000000000000000000000007001c007c0e0100000000000000000000000000000000000000000000000000380fe00f80000000000000000000000000000000000000000000000000000000380ffc0ff00fff0000000000000000000000000000000000000000000000000000001c7e701e03000000000000000000000000000000000000000000000000000001c18000007c70000000000000000000000000000000000000000000000000000ffff0000ffff00000000000000000000000000000000000000000000000003ff0000ffff0000
  | 1, 12 => 0x3fffe38180018c0000000000000000000000000000000000000000000000000007f01ff0000000000000000000000000000000000000000000000000000000003fffffff800ffe000000000000000000000000000000000000000000000000003ffffffe739e7360000000000000000000000000000000000000000000000000000fc00e000ffe000000000000000000000000000000000000000000000000003fffe00ffff000000000000000000000000000000000000000000000000000003fffffff800000000000000000000000000000000000000000000000000000003ffffff18c618c9
  | 1, 13 => 0x3ffffff00c600090000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000000001c70000000000000000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000003ff1c00ffff07c0000000000000000000000000000000000000000000000000000e0000003e000000000000000000000000000000000000000000000000000003ff000018c60000000000000000000000000000000000000000000000000000000001c7ffffffff
  | 1, 14 => 0xe1c18003e07c70000000000000000000000000000000000000000000000000070fde007c0ffd8000000000000000000000000000000000000000000000000000e1dd8073ee7d700000000000000000000000000000000000000000000000003f00000ffc0000000000000000000000000000000000000000000000000000003ffffff07ff001f000000000000000000000000000000000000000000000000007f01ff00000000000000000000000000000000000000000000000000000000000000000038070600000000000000000000000000000000000000000000000003ff0000ffff0000
  | 1, 15 => 0x3fefff8fffeffff00000000000000000000000000000000000000000000000003f1e22018c0180800000000000000000000000000000000000000000000000000001c00000007c000000000000000000000000000000000000000000000000000000000f83f07e700000000000000000000000000000000000000000000000003801c00f80007c0000000000000000000000000000000000000000000000000000efc18003effc700000000000000000000000000000000000000000000000003ff1c18ffff0000000000000000000000000000000000000000000000000000000e0000003e0706
  | 2, 0 => 0xe01c7e73fe7360000000000000000000000000000000000000000000000000380ffc0f800ffe0000000000000000000000000000000000000000000000000038effdff83effe7000000000000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000003ffe1e7fffff818000000000000000000000000000000000000000000000000000e1ddf00000000000000000000000000000000000000000000000000000000000001c700380706000000000000000000000000000000000000000000000000038f1e1f00000000
  | 2, 1 => 0x3fffe38000600c100000000000000000000000000000000000000000000000003ffffff18c60000000000000000000000000000000000000000000000000000000e0000003e0000000000000000000000000000000000000000000000000000000001c70700e01000000000000000000000000000000000000000000000000003ffffe0fffffff800000000000000000000000000000000000000000000000003ffffff07feffdf000000000000000000000000000000000000000000000000000e1c18003e07c7
  | 2, 2 => 0xe1c180000000000000000000000000000000000000000000000000000000003ffffffe7f9ff3e000000000000000000000000000000000000000000000000000e1c00003e07c00000000000000000000000000000000000000000000000000000fe380000ffff000000000000000000000000000000000000000000000000000001c7e7f9ff3e0000000000000000000000000000000000000000000000000000fc000000ffc000000000000000000000000000000000000000000000000003f0e1e0ffc0f818000000000000000000000000000000000000000000000000000001c00700e010
  | 2, 3 => 0x3ffe1e007c0f81800000000000000000000000000000000000000000000000003f1e3e70000000000000000000000000000000000000000000000000000000003ffe000fffff8000000000000000000000000000000000000000000000000000380e000f800f8000000000000000000000000000000000000000000000000000000e1c7e739ff36000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000003ffffc7ffffffe0000000000000000000000000000000000000000000000000000effff003effff
  | 2, 4 => 0x3ffe1e7ffffff3e00000000000000000000000000000000000000000000000003fffe00f800ffe00000000000000000000000000000000000000000000000000000000007ff001f00000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000038f1e18180600c100000000000000000000000000000000000000000000000003ffffff003e0000000000000000000000000000000000000000000000000000007efdffe7ffffff000000000000000000000000000000000000000000000000007efdf8003e07c7
  | 2, 5 => 0x70e1e007f8ff1e00000000000000000000000000000000000000000000000003801e00f80007e000000000000000000000000000000000000000000000000003ffffffffffffe0000000000000000000000000000000000000000000000000007e000007fe0000000000000000000000000000000000000000000000000000000001c7e73900000000000000000000000000000000000000000000000000000380fe00f838ffe6000000000000000000000000000000000000000000000000038efe18003e07c7000000000000000000000000000000000000000000000000038efe00f83effe0
  | 2, 6 => 0x70e02000c01808000000000000000000000000000000000000000000000000007e1c1807fe07c700000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ff01c0ffffe010
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3dbb7cffeb5d6a40000000000000000000000000000000000000000000000000274e9f057caf95b00000000000000000000000000000000000000000000000003c89000fa94528000000000000000000000000000000000000000000000000002f7efffd7ebfd7f00000000000000000000000000000000000000000000000001bf7fffad7fafff00000000000000000000000000000000000000000000000003c8fe82fa94ffe000000000000000000000000000000000000000000000000002f7cd7dd7eb7d5f00000000000000000000000000000000000000000000000001bf37cfad7f86a4
  | 0, 1 => 0x3c8b682fa94d6a00000000000000000000000000000000000000000000000000093054d8421040400000000000000000000000000000000000000000000000003ff9104ffff528000000000000000000000000000000000000000000000000000264c79016a2d5f000000000000000000000000000000000000000000000000009327cf8421842400000000000000000000000000000000000000000000000003ffdd7dffff7fdf00000000000000000000000000000000000000000000000003dbb786feb5d6a0000000000000000000000000000000000000000000000000012e5c79297e2fdf
  | 0, 2 => 0x12e1000297e028000000000000000000000000000000000000000000000000000376f86056bad600000000000000000000000000000000000000000000000000274870b57ca5424000000000000000000000000000000000000000000000000011831c02c14828000000000000000000000000000000000000000000000000002e6eefbd3eafd7f00000000000000000000000000000000000000000000000001bf7fffad7fafff00000000000000000000000000000000000000000000000003ff9104ffff528000000000000000000000000000000000000000000000000002f7efffd7ebfd7f
  | 0, 3 => 0xa54a76814b297b00000000000000000000000000000000000000000000000002f78104d7eb5000000000000000000000000000000000000000000000000000012e5c79297e2fdf00000000000000000000000000000000000000000000000001bf5d7dad7f2fdf00000000000000000000000000000000000000000000000003ffff86ffffffe00000000000000000000000000000000000000000000000000242844952a0540400000000000000000000000000000000000000000000000003ffdd7dffff7fdf000000000000000000000000000000000000000000000000009349348421295b
  | 0, 4 => 0x37017d056b001f00000000000000000000000000000000000000000000000002d1a386d681d02000000000000000000000000000000000000000000000000003eefefbfbfeffff000000000000000000000000000000000000000000000000012c5c70295e2fdb000000000000000000000000000000000000000000000000009327cf84218424000000000000000000000000000000000000000000000000009327868421842000000000000000000000000000000000000000000000000003c89079fa94529f000000000000000000000000000000000000000000000000012e3282297e82a0
  | 0, 5 => 0x3eefefbfbfeffff00000000000000000000000000000000000000000000000003ffffff84218424000000000000000000000000000000000000000000000000009327cfe739e7360000000000000000000000000000000000000000000000000240a2825280d020000000000000000000000000000000000000000000000000012e5c79297e2fdf000000000000000000000000000000000000000000000000036cd8307bde7bdb000000000000000000000000000000000000000000000000010810002814028000000000000000000000000000000000000000000000000002f4eff2d7cafd7b
  | 0, 6 => 0x18b160fa83506a400000000000000000000000000000000000000000000000000240079014a001f00000000000000000000000000000000000000000000000003dbff86feb5ffe000000000000000000000000000000000000000000000000000006efb0000ad7f00000000000000000000000000000000000000000000000000244870014a295b000000000000000000000000000000000000000000000000008102068001002000000000000000000000000000000000000000000000000003db9104ffbd52800000000000000000000000000000000000000000000000000264c87053ca795b
  | 0, 7 => 0x12e5c79297e2fdf00000000000000000000000000000000000000000000000001085c0028142fc000000000000000000000000000000000000000000000000003fff9f4fffffbdb0000000000000000000000000000000000000000000000000274810057ca500000000000000000000000000000000000000000000000000000006ab20000a97b0000000000000000000000000000000000000000000000000037017d056b295f000000000000000000000000000000000000000000000000000000790000001f00000000000000000000000000000000000000000000000000b76fff856bad7f
  | 0, 8 => 0x930104842100000000000000000000000000000000000000000000000000000274ebf257caf97b000000000000000000000000000000000000000000000000013f5d7d2d7f2fdf00000000000000000000000000000000000000000000000000260079016a001f0000000000000000000000000000000000000000000000000002044900200404000000000000000000000000000000000000000000000000024080005280500000000000000000000000000000000000000000000000000003db9104feb552800000000000000000000000000000000000000000000000000274c97057ca795b
  | 0, 9 => 0x6e820000ad6000000000000000000000000000000000000000000000000003dbff86ffbdffe000000000000000000000000000000000000000000000000003ff9104ffbd528000000000000000000000000000000000000000000000000003ecfef2fbdefffb00000000000000000000000000000000000000000000000003ff954dffff56840000000000000000000000000000000000000000000000000037017d056b00040000000000000000000000000000000000000000000000000274e9f057caf95b00000000000000000000000000000000000000000000000003ffb7cfffffd6a4
  | 0, 10 => 0x9327cf8529a536000000000000000000000000000000000000000000000000010b100d2835028400000000000000000000000000000000000000000000000003c8fe82fa94ffe000000000000000000000000000000000000000000000000003ff9104feb552800000000000000000000000000000000000000000000000000276edf957eafd5f00000000000000000000000000000000000000000000000003ffffffffffffff0000000000000000000000000000000000000000000000000264c83053ca795b00000000000000000000000000000000000000000000000003c8fefbfa94ffff
  | 0, 11 => 0x2c0ee82d280fd6000000000000000000000000000000000000000000000000003ffd974ffff7bdb00000000000000000000000000000000000000000000000003c8fefbfa94ffff00000000000000000000000000000000000000000000000003ff9104ffff528000000000000000000000000000000000000000000000000002d3a7cfd6a1d424000000000000000000000000000000000000000000000000013e7df92d7eafdf00000000000000000000000000000000000000000000000003ff917dffff529f000000000000000000000000000000000000000000000000019b170fac3506a4
  | 0, 12 => 0x60b0000042400000000000000000000000000000000000000000000000003c8b682fa94f7a000000000000000000000000000000000000000000000000000932786e739e72000000000000000000000000000000000000000000000000001bf1104ad7f028000000000000000000000000000000000000000000000000002d1a786d681d42000000000000000000000000000000000000000000000000003dbffcffeb5ffe4000000000000000000000000000000000000000000000000008026828000842000000000000000000000000000000000000000000000000003ffffffffffffff
  | 0, 13 => 0x18b140da835068400000000000000000000000000000000000000000000000000b7017d856b001f00000000000000000000000000000000000000000000000003eedc79fbfe7fdf0000000000000000000000000000000000000000000000000274e9f057caf95b00000000000000000000000000000000000000000000000003ffdd7dffff7fdf0000000000000000000000000000000000000000000000000274e9f02c14828000000000000000000000000000000000000000000000000003ff9104ffff529b000000000000000000000000000000000000000000000000037efdf97ffeffdf
  | 0, 14 => 0x3c8fe82fa94ffe000000000000000000000000000000000000000000000000000b727ff856b843f0000000000000000000000000000000000000000000000000013014d0421000400000000000000000000000000000000000000000000000000376fff056bad7f0000000000000000000000000000000000000000000000000274e9f057caf95b000000000000000000000000000000000000000000000000019b37cfac3586a4000000000000000000000000000000000000000000000000009327cfe739e73600000000000000000000000000000000000000000000000001ae7efba97eafff
  | 0, 15 => 0x37014d056b00040000000000000000000000000000000000000000000000000037497d056b295f0000000000000000000000000000000000000000000000000277e9fd57ebf95f00000000000000000000000000000000000000000000000003ff9104ffff52800000000000000000000000000000000000000000000000000274effb57cafd7f000000000000000000000000000000000000000000000000000068f00000a95b00000000000000000000000000000000000000000000000000934934e7394a4900000000000000000000000000000000000000000000000003ff9104ffff5280
  | 1, 0 => 0x264e8f053caf95b000000000000000000000000000000000000000000000000036edc797bfe7fdf00000000000000000000000000000000000000000000000000240030014a001b0000000000000000000000000000000000000000000000000037497d056b295f00000000000000000000000000000000000000000000000003c8feb2fa94fffb000000000000000000000000000000000000000000000000001101040401000000000000000000000000000000000000000000000000000003ffffffffffffff000000000000000000000000000000000000000000000000001021c004008000
  | 1, 1 => 0x2f7efffd7ebfd7f0000000000000000000000000000000000000000000000000037057d056b041f000000000000000000000000000000000000000000000000010a5c4928342fc4000000000000000000000000000000000000000000000000018b164fa83506a400000000000000000000000000000000000000000000000002f7e9f4d7ebf95b0000000000000000000000000000000000000000000000000242844931b837160000000000000000000000000000000000000000000000000013010d042100040000000000000000000000000000000000000000000000000091238684018020
  | 1, 2 => 0x3ffffffd7ebfd7f0000000000000000000000000000000000000000000000000274e9f004008000000000000000000000000000000000000000000000000000003469f0054aa95b000000000000000000000000000000000000000000000000034890007a945280000000000000000000000000000000000000000000000000018b368fa83586a400000000000000000000000000000000000000000000000001891206a81502a000000000000000000000000000000000000000000000000002f5ebf6d7cbf97b00000000000000000000000000000000000000000000000003cafecbfab4ffe4
  | 1, 3 => 0x3ffffcffffffff6000000000000000000000000000000000000000000000000009327cfffbdfff600000000000000000000000000000000000000000000000002d3efcfd6a1fd640000000000000000000000000000000000000000000000000348d8007a947bc00000000000000000000000000000000000000000000000000277e9fd57ebf95f00000000000000000000000000000000000000000000000000930104e739420000000000000000000000000000000000000000000000000003ffffffffffffff0000000000000000000000000000000000000000000000000000000063186312
  | 1, 4 => 0x36cd83018c618c900000000000000000000000000000000000000000000000003dbffcfffbdfff600000000000000000000000000000000000000000000000000802682e210e72000000000000000000000000000000000000000000000000003c8fe828000842000000000000000000000000000000000000000000000000003dbb7cfffbdf7b600000000000000000000000000000000000000000000000002f7efff8421842400000000000000000000000000000000000000000000000001bf7fffef7fefff0000000000000000000000000000000000000000000000000240e8805280f940
  | 1, 5 => 0x3ff9104ffff5280000000000000000000000000000000000000000000000000036cd8300000000000000000000000000000000000000000000000000000000000000000295e2bdb0000000000000000000000000000000000000000000000000274e98057caf94000000000000000000000000000000000000000000000000000006efb00008424000000000000000000000000000000000000000000000000009327cfe631e72400000000000000000000000000000000000000000000000000b76fffe77bef7f000000000000000000000000000000000000000000000000003469f0474ae95b
  | 1, 6 => 0x3ffffffffffffff00000000000000000000000000000000000000000000000002d18104d68150000000000000000000000000000000000000000000000000000003000d0021000400000000000000000000000000000000000000000000000002f7effff7fbff7f00000000000000000000000000000000000000000000000003ff9104d7eb5000000000000000000000000000000000000000000000000000000000007bde7bdb00000000000000000000000000000000000000000000000000370104056b00000000000000000000000000000000000000000000000000000037014d056b0016
  | 1, 7 => 0xb76fff8421842400000000000000000000000000000000000000000000000003ffffffef7fefff00000000000000000000000000000000000000000000000003ffffff8421ad7f000000000000000000000000000000000000000000000000009327cfef3de7b600000000000000000000000000000000000000000000000003ff9104ad7f028000000000000000000000000000000000000000000000000003ffffffad7fafff000000000000000000000000000000000000000000000000009327cfef7fefff00000000000000000000000000000000000000000000000003fcff82ffdeffe0
  | 1, 8 => 0x3ffb7cffffff7b600000000000000000000000000000000000000000000000003ffffffffffd6a40000000000000000000000000000000000000000000000000000000053ca795b00000000000000000000000000000000000000000000000000b727ffe77be73f000000000000000000000000000000000000000000000000018b1004a83502800000000000000000000000000000000000000000000000000037497d056b085f00000000000000000000000000000000000000000000000000340170054a001b00000000000000000000000000000000000000000000000003ff910484210000
  | 1, 9 => 0x3fcfff2ffdefffb000000000000000000000000000000000000000000000000012e5c790020040400000000000000000000000000000000000000000000000003fffffffffff7b6000000000000000000000000000000000000000000000000037efdf957eafd5f00000000000000000000000000000000000000000000000003c8fe82fa94fffb00000000000000000000000000000000000000000000000001ae7efbeb7eefff0000000000000000000000000000000000000000000000000250a1805680d0000000000000000000000000000000000000000000000000000000483000000849
  | 1, 10 => 0x3ffffffd6a1fd6400000000000000000000000000000000000000000000000003ffffff94a194240000000000000000000000000000000000000000000000000250e9c05680f94000000000000000000000000000000000000000000000000003c8fe82fa94ffe000000000000000000000000000000000000000000000000002c0a282d280d02000000000000000000000000000000000000000000000000000002282000080200000000000000000000000000000000000000000000000000000000073da7b5b00000000000000000000000000000000000000000000000003ff917dffff529f
  | 1, 11 => 0x3fcfff2d7cafd7b0000000000000000000000000000000000000000000000000274a1c057caf11200000000000000000000000000000000000000000000000003c8fe82fa94d6a000000000000000000000000000000000000000000000000003d8ffc2ff9cfff200000000000000000000000000000000000000000000000000912386c601c02000000000000000000000000000000000000000000000000000004c7900002d5f00000000000000000000000000000000000000000000000000936fff8421ad7f000000000000000000000000000000000000000000000000036c90007bde5280
  | 1, 12 => 0x36cd830188418c000000000000000000000000000000000000000000000000000b727ff8421842400000000000000000000000000000000000000000000000003fffffffeb5ffe400000000000000000000000000000000000000000000000003ffffffe739e73600000000000000000000000000000000000000000000000003c8fe82fa94ffe000000000000000000000000000000000000000000000000003ffff86ffffd6a000000000000000000000000000000000000000000000000003fffffffeb5d6a400000000000000000000000000000000000000000000000003ffffff9ce79ced
  | 1, 13 => 0x3ffffff8463842d00000000000000000000000000000000000000000000000000246efb014aad7f000000000000000000000000000000000000000000000000000026cb00008424000000000000000000000000000000000000000000000000000000007a94528000000000000000000000000000000000000000000000000003ffdd04ffff7fc0000000000000000000000000000000000000000000000000012e1449297e0684000000000000000000000000000000000000000000000000036c900018c61080000000000000000000000000000000000000000000000000009327cfffffffff
  | 1, 14 => 0x12c5830295e2bdb000000000000000000000000000000000000000000000000037cfdf07fdeffdb000000000000000000000000000000000000000000000000013e7df96f7eefdf00000000000000000000000000000000000000000000000003fc9100ffde528000000000000000000000000000000000000000000000000003ffffff856b843f0000000000000000000000000000000000000000000000000037017d04210004000000000000000000000000000000000000000000000000000204492138271600000000000000000000000000000000000000000000000003ffb786ffffd6a0
  | 1, 15 => 0x3fefffbfffeffff000000000000000000000000000000000000000000000000024080001080100000000000000000000000000000000000000000000000000001887e82a814afe0000000000000000000000000000000000000000000000000000000002814028000000000000000000000000000000000000000000000000003c8dc00fa947fc0000000000000000000000000000000000000000000000000036efcf97bfeffdf00000000000000000000000000000000000000000000000003ffdd7dffff5684000000000000000000000000000000000000000000000000012e1449297e2796
  | 2, 0 => 0x1bf37cfef7fe7b600000000000000000000000000000000000000000000000003d8ffc2fe94ffe000000000000000000000000000000000000000000000000003ffffffffffffff000000000000000000000000000000000000000000000000000000000000295b00000000000000000000000000000000000000000000000003ffffffffffffff00000000000000000000000000000000000000000000000001bf7fff84218424000000000000000000000000000000000000000000000000009327cfa539a736000000000000000000000000000000000000000000000000018b160f80210424
  | 2, 1 => 0x240800052805000000000000000000000000000000000000000000000000000036cd830084608c900000000000000000000000000000000000000000000000003ffffff9ce794a4000000000000000000000000000000000000000000000000012e5870297e2bdb000000000000000000000000000000000000000000000000009327cfc729e53600000000000000000000000000000000000000000000000003fffff6fffffffb00000000000000000000000000000000000000000000000003ffffffffffffff000000000000000000000000000000000000000000000000010a140928340684
  | 2, 2 => 0x12e5c79016a2d5f00000000000000000000000000000000000000000000000003fffffff7fbff7f000000000000000000000000000000000000000000000000012e5c00297e2fc0000000000000000000000000000000000000000000000000000048300000295b000000000000000000000000000000000000000000000000009327cff7fbff7f0000000000000000000000000000000000000000000000000348fc807a94ffc000000000000000000000000000000000000000000000000003fcf9f0ffdefbdb000000000000000000000000000000000000000000000000001021c04708e112
  | 2, 3 => 0x3fff9f4d7ebf95b00000000000000000000000000000000000000000000000002d1a3868401802000000000000000000000000000000000000000000000000003fff984fffffbc000000000000000000000000000000000000000000000000003c8f880fa94fbc000000000000000000000000000000000000000000000000002d3efcff7b9ff760000000000000000000000000000000000000000000000000083060f8021042400000000000000000000000000000000000000000000000003ffffcfffffffe4000000000000000000000000000000000000000000000000012e7efb297eafff
  | 2, 4 => 0x3ffffffffffffff00000000000000000000000000000000000000000000000003ffff86feb5ffe000000000000000000000000000000000000000000000000000000000014a001b000000000000000000000000000000000000000000000000000000007bde5280000000000000000000000000000000000000000000000000010810000804008000000000000000000000000000000000000000000000000003ffffffad7f86a400000000000000000000000000000000000000000000000003ffffffffffffff000000000000000000000000000000000000000000000000037efdf92d7eafdf
  | 2, 5 => 0x276edf977faff5f00000000000000000000000000000000000000000000000001881602a81406a000000000000000000000000000000000000000000000000003ffffffffffffe4000000000000000000000000000000000000000000000000037e91007ffe5280000000000000000000000000000000000000000000000000009327cfe739c62400000000000000000000000000000000000000000000000003cafecbfbbcfff600000000000000000000000000000000000000000000000003eefefba97eafff00000000000000000000000000000000000000000000000003eefe82fbfeffe0
  | 2, 6 => 0x264c83010c21849000000000000000000000000000000000000000000000000037edd797ffe7fdf00000000000000000000000000000000000000000000000003ffffff856bad7f00000000000000000000000000000000000000000000000003ffb1c4fffff392
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 308 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 308 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 308 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 308 then wireAt i else 0
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
  | 4 => 1
  | 5 => 88
  | 6 => 226
  | 7 => 122
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x49a293c
  | 5, 0 => 0x916a2d81814fdce17cf1251778d9b45d77bd2ed97361b86d72c540b67140d8d871239b3e706bda136dd851da6c4738bf694f5a0669173f09684b3d27625544d162391173617923c0600073825f3052075f11e6385cf453a75b6d302656b3711b4fadc8374db258554cc5abe9462fcc5445d991d242ad843040d84d213da9a7603a3fa9e6399597b83916a9c93255e646310b29a2308fdfb22c5de5032a6cd8a12a2fe56d29e30a9d293f1abf290421da27ce4e77279a9143223d6acc20e9c7ca2001687c1f670ebe1cdb4f431a53497614d8520111585ff70ef5fe8d0d58fe950a25c20908cc06670893daa70673a80005f373ec051593a502d056d1000840e5
  | 5, 1 => 0xf32eb67beb8bdf7ceacfac1fea21ab24e93e44a6e4271949d46bd541d36ae5e7d20974cbc999b18cc84e2917c530d125c0c6217cb779b406b548e2a4ace9d848a9f31bcba76d09059d1625de9bdd449e9ab48ee8965d4689936d815f9173bf1c
  | 6, 0 => 0x2a3e329b29c4b9f8298caa2526b8bfe523a8da9420f0ba56209445351fe279271eef54901d774fe61cb196b41c82662b1c4478291bcaa5001b7852151b30be7f1b0e71a31a044d3519b9c86819371cc718a6696f185e1bcc1780280516f3a00b1658ec56163ccd4b15ead3ea146dd678145b541c136b9aa412ded9d71231f3f310affa5f0f764fbf0ed48efb0ecde01c0eccb7400e7a9d0c0d8687440cd408630c908a7a0c6f03cc0c5be1980b78a65e0a8238c00a5a9dcf0a0ee3b509c80e500825ce0e073439a60700674a06b6b95906a5dad805ecc2ee033240080330b3530328288202e576fb022760e602187aa101eda1a001992da401766d8100339b29
  | 6, 1 => 0x605ce1795f71edf25dd275755ce0e9ea5c34234d5c1f3e465b2ea5385a978b145a6eaaf158fae3a65884b1ee583e54f35745e0fb55e18e2d550c8f68549f33f151a4824250e482755017c7ca4ed591294cc65f984c58015c4bd80f244bd0eb074b83029749ee7a494830e2e947a969a6476ee9434741da75472aca85463f0093463d3ed4462755f545c2dbcc44fa10494479c384436c2fe4433fa33f4307d930430570e440bc65a33f313b653ed28ae53ea34f7a3e51fe3b3d7b1e3a3cedab6d3c73d4ee3b21acf237e92e0f36d1397b3666b6bc33c5ae8333641e9c31747fcf3110e8fa2eb1aa0b2ea6c05d2c25485b2ad006ef2ac299d12a7a47272a4abc0b
  | 6, 2 => 0xb6aa2a20b34dff88b3458a1bb2a00218b0264eefaff6cbf3aea7581aadd5ff5eab94a992ab669d79aa4ba25ea3c6bea1a1ff33179faba7f299b6e7dd987df0ac97f411f197ac05c29728bb3594fb60b694fac47c93fff13f930359e78e26e5f78d1e15d58ce6acb38c0dbe5a8beab0788b216dfb880cdd5b86100eca8268127e7d9e80da7d05f6f57ad078527acc2fde79200ff078f874f278b9448077c13929764d3db574975b2e736c3eab7319db9a71e79695716c3c1f71576297714ddd1f7026cd1d6ff14a9a6fa458616c195fe56b18346f6a1ef21b69904ec9687f3dd7686d790367a3272d6792916b64ef0a7e632c34926261245961c7e1c460a67754
  | 6, 3 => 0xf7b6ec83f5f4fc2af5b2a9a3f54beaa3ee37cb69edcb4794edc036e3eda64d6eec6f887be2fd77ace0b0c46fde3480bcdc84ac5adb9306fed9f16186d8f1ceb3d43a869fcfd29977cf6ae6fbcd54eb62cb50af2aca2c216cc3248b03c2d474bfc2024609c060a091bfaca009bf45d0d0bf3e5620bf25c260bf1a8222bd575833bd15572db749d50a
  | 7, 0 => 0x46f3f1d645d1eda144efaef6448b58424488eff6417604ab40fd5c893f1911403d084ce73c5cd0913bbd9fd83b9517d93b8c25f93661bf25358f846f35895b04313507a63092a0e22cf45da32cbbaac62aa95048292e66d928f2496d261b7d8625029ba323bebf2122f2b3902232fccd21da3c201c91f0b51b9b06e31a28899f19e4b4771983ef5b19728323196926bf19570811194d07b418b98c201804d3f117c2485d159b56a613ec0a33122bc8a90f52f7e70edcd7070e62c7b30d31a8270c11c00d0b5d6d290a5133e109c8d28f0820a78307852a5a0626d8910621f9fe05a02dba0544cdf60346c6ec02f5fddb028b04db01dd076b0122554d002f4827
  | 7, 1 => 0xff33d146fd1304b1e8f3ed30e7311744de7c5035dc5b1b28db4ac3addb27b5cbda5e734ec0a94172c08ae272bead66f1b7aa7e56b19e29acafe37ca7af99e6ccab7128a0aa6baa8baa6b1466a837e8f9a6bea662a3dc39449a79e24f967edfc894ffe11f9437159c92a935379244de83924276378ff96af68a713de38726336285a3bc0f78ba6f2e75a337076bee9c076bbf6b7e6941528868f8c50e6874221a679b211f6724e6de6640f86d62a89ff75db7a25f59bf3e13560409b254bb116252e2f8d752652dd55062e4424f85907a4f2308104e31041e4c6505a34b8b4c2a4b36c4a0479295b9
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x8c100
  | 5, 0 => 0x1001010000000100101000000000000000000000000000000000000000000000010010200000000000000000000100102000000010010100000000000000000000000000000000000000000000000000000000000100102000000000000000000000c810000000000000000000000100102000000010010200000000000000000000000000000000008c100000000001010200000001001020000000000000000000010010200000000000000000000000000000000008c1000000000000000
  | 5, 1 => 0x100102000000000000000000001001020000000000000000000010010200000000000000000000100101000000010010100000001001010000000000000000000000000000000001001010000000000000000000000000000000000000000000000100102000000010010100000000000000000000100101000000000000000000000000000000000000000000000008c1000000000000000000000000000000000001001020000000100102000000000000000000000000000000000100101
  | 5, 2 => 0x10010100000001001010000000100101000000000000000000001001010000000000000000000010010100000001001020000000000000000000000000000000000000000000000100102000000010010200000001001020000000100101000000010010100000001001010000000000000000000000000000000000000000000000100102000000010010100000000000000000000100101
  | 6, 0 => 0x1001020000000000000000000000000000000000000000000000000001000000010010100000000000010000000000001000000000000000000000000000000000000000000000010010200000000000000000000000002000000000000000000000000010000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000101020000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000
  | 6, 1 => 0x1001010000000000002000000000000100000000000020000000000001000000000000000000000000000000000000000000000000000200000000000000000000000000000000010010100000000000000000000100101000000000000000000000000000000000100101000000001010200000000000000000000100101000000000000000000000000000000000000002000000000000000000000000000000000010101000000000000100000000000020000000000002000000010010100000000000010000000100101
  | 6, 2 => 0x1001020000000100101000000000000000000001001020000000000000000000010010100000000000000000000100101000000010010100000001001020000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000001001020000000000000000000000000000000000c81000000000000000000000000000100000000000000000000000000
  | 6, 3 => 0x1001020000000000000000000000000000000000000020000000100101000000000000000000000000000000000000000000000000000000000001001010000000010102000000000000000000000000000000000000000000000000000000000000000000000000010101000000000000100000001001010000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000010010100000000000000000000000000000000010010100000000000000000000100102
  | 6, 4 => 0x2000000010010200000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000100101000000001010100000000000000000000000002000000000000200000000000000000000000000000000000000000000000000000000000000001000000000000000000001001020000000000000000000000000000000000000000000000000000000000010010200000000000000000000100102
  | 6, 5 => 0x100102000000000000000000000000000000000000000000000010010100000001001020000000000000000000000000000000001001020000000000002000000010010100000000000000000000010101000000000000000000000101020000000000000000000000000000000000000000000000100101000000000000000000000000000000000000000000000000000000000001001010000000000001000000000000000000001001020000000010101000000000000000000000000000000000000000
  | 6, 6 => 0x1001010000000100101000000010010200000001001020000000000000000000010010100000000000000000000000001000000000000100000000000010000000100101000000010010200000001001020000000000000000000000000200000000000000000000000001000000001010100000001001020000000000000000000000000200000000000000000000000002000000000000100000000000000000000000000000000000000000000001001010000000000001000000000000000000000000010000000000001
  | 6, 7 => 0x1001020000000000000
  | 7, 0 => 0x20000000000002000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000200000000000010000000000000000000000000000000000000000000000000000000000000000100000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000100000000000000000000000000000000000000100000000000000000000000002000000000000000000000000020000000000001
  | 7, 1 => 0x20000000000002000000000000100000000000010000000000001000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000200000000000010000000000001000000000000000000000000000000000000002000000000000100000000000010000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000020000000000001000000000000100000000000000000000000002
  | 7, 2 => 0x10000000000001000000000000100000000000020000000000000000000000000200000000000000000000000002000000000000000000000000000000000000001000000000000200000000000000000000000001000000000000000000000000000000000000002000000000000100000000000010000000000000000000000000200000000000020000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000
  | 7, 3 => 0x10000000000001000000000000000000000000000000000000002000000000000100000000000000000000000002000000000000100000000000010000000000000000000000000000000000000020000000000002000000000000200000000000020000000000001000000000000000000000000000000000000001000000000000200000000000000000000000001000000000000100000000000000000000000002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_30 roots_30 5 s ws hint
  | 1 => checkCutEntry dom_61 roots_61 6 s ws hint
  | 2 => checkCutEntry dom_59 roots_59 6 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_63 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_63 == dom_63) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_63 goalM u ys) : RunD dom_63 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_63 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 4 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_16 : ∀ i, 16 ≤ i → i < 23 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 7 16 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 23 → Z 4 i = true := (range_split z4_0 z4_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_48 : ∀ i, 48 ≤ i → i < 64 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_64 : ∀ i, 64 ≤ i → i < 80 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_80 : ∀ i, 80 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_96 : ∀ i, 96 ≤ i → i < 112 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_112 : ∀ i, 112 ≤ i → i < 128 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_128 : ∀ i, 128 ≤ i → i < 144 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_144 : ∀ i, 144 ≤ i → i < 160 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_160 : ∀ i, 160 ≤ i → i < 176 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_176 : ∀ i, 176 ≤ i → i < 192 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_192 : ∀ i, 192 ≤ i → i < 204 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 192 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 204 → Z 5 i = true := (range_split (range_split (range_split z5_0 (range_split z5_16 z5_32)) (range_split z5_48 (range_split z5_64 z5_80))) (range_split (range_split z5_96 (range_split z5_112 z5_128)) (range_split (range_split z5_144 z5_160) (range_split z5_176 z5_192))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_32 : ∀ i, 32 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : ∀ i, 48 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 80 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_80 : ∀ i, 80 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_96 : ∀ i, 96 ≤ i → i < 112 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_112 : ∀ i, 112 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 144 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_144 : ∀ i, 144 ≤ i → i < 160 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_160 : ∀ i, 160 ≤ i → i < 176 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_176 : ∀ i, 176 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_192 : ∀ i, 192 ≤ i → i < 208 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_208 : ∀ i, 208 ≤ i → i < 224 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_224 : ∀ i, 224 ≤ i → i < 240 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_240 : ∀ i, 240 ≤ i → i < 256 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_256 : ∀ i, 256 ≤ i → i < 272 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_272 : ∀ i, 272 ≤ i → i < 288 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_288 : ∀ i, 288 ≤ i → i < 304 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_304 : ∀ i, 304 ≤ i → i < 320 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_320 : ∀ i, 320 ≤ i → i < 336 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_336 : ∀ i, 336 ≤ i → i < 352 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_352 : ∀ i, 352 ≤ i → i < 368 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_368 : ∀ i, 368 ≤ i → i < 384 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_384 : ∀ i, 384 ≤ i → i < 400 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_400 : ∀ i, 400 ≤ i → i < 416 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_416 : ∀ i, 416 ≤ i → i < 432 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_432 : ∀ i, 432 ≤ i → i < 447 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 432 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 447 → Z 6 i = true := (range_split (range_split (range_split (range_split z6_0 (range_split z6_16 z6_32)) (range_split (range_split z6_48 z6_64) (range_split z6_80 z6_96))) (range_split (range_split z6_112 (range_split z6_128 z6_144)) (range_split (range_split z6_160 z6_176) (range_split z6_192 z6_208)))) (range_split (range_split (range_split z6_224 (range_split z6_240 z6_256)) (range_split (range_split z6_272 z6_288) (range_split z6_304 z6_320))) (range_split (range_split z6_336 (range_split z6_352 z6_368)) (range_split (range_split z6_384 z6_400) (range_split z6_416 z6_432)))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_32 : ∀ i, 32 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_64 : ∀ i, 64 ≤ i → i < 80 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_80 : ∀ i, 80 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_96 : ∀ i, 96 ≤ i → i < 112 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_112 : ∀ i, 112 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 144 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_144 : ∀ i, 144 ≤ i → i < 160 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_160 : ∀ i, 160 ≤ i → i < 176 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_176 : ∀ i, 176 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_192 : ∀ i, 192 ≤ i → i < 208 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_208 : ∀ i, 208 ≤ i → i < 224 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_224 : ∀ i, 224 ≤ i → i < 240 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_240 : ∀ i, 240 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_256 : ∀ i, 256 ≤ i → i < 259 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 3 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 259 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 (range_split z7_240 z7_256)))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 27 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 11 16 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 27 → Z 8 i = true := (range_split z8_0 z8_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
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
  scr dom_63 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_63 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_63 roots_63 goal_63 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_63 goal_63 := by
    have h0 : isConstB dom_63 goal_63 = false := by decide +kernel
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

end S_63

theorem low_63 : Lower dom_63 roots_63 goal_63 10 := S_63.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_63_bits : ∀ r : Fin 64, roots_63.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_63_lt : ∀ r : Fin 64, dom_63.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_63 T)
    (hlow : Lower dom_63 roots_63 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_63, Avail mask256 roots_63 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_63 hfan 0 roots_63 roots_63 rfl hsup0
  set out := (execN C.gates roots_63).getD C.output 0
  have hout : out &&& dom_63 = T &&& dom_63 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_63_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_63 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_63_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_63).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_63)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_63.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_63 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_63).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_63 &&& mask256 = dom_63 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_63 = T &&& dom_63 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63, hout]
  have hnc_m : ¬ IsConst dom_63 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_63 roots_63 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_63 roots_63 0 roots_63 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩], 15⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 10 := by decide

theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4240490688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4240490688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4240490688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 10 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4240490688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 10 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_12895_aux

theorem PEqualNP.Outside.L_meta_12895 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4240490688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4240490688) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_12895_aux.wit, PEqualNP.Outside.L_meta_12895_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_12895_aux.wit_sz (PEqualNP.Outside.L_meta_12895_aux.lower s hs), PEqualNP.Outside.L_meta_12895_aux.wit_ev⟩
