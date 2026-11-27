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

namespace PEqualNP.Outside.L_meta_15513_aux

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

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xeac8c888eac8c888eac8c888eac8c888eac8c888eac8c888eac8c888eac8c888
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xe8e8a8a8c8c88888e8e8a8a8c8c88888e8e8a8a8c8c88888e8e8a8a8c8c88888
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xeaa8eaa8c888c888eaa8eaa8c888c888eaa8eaa8c888c888eaa8eaa8c888c888
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xeae8eaa8eac8c888eae8eaa8eac8c888eae8eaa8eac8c888eae8eaa8eac8c888
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (5, 7), (6, 7), (6, 14), (6, 22), (9, 11), (9, 25), (10, 11), (10, 14), (12, 14), (13, 15), (13, 29), (17, 19), (17, 25), (18, 19), (18, 22), (20, 22), (21, 23), (21, 29), (24, 25), (26, 27), (26, 30), (28, 29), (28, 30)]
def r1sG : List Nat := [1, 2, 5, 6, 6, 6, 9, 9, 10, 10, 12, 13, 13, 17, 17, 18, 18, 20, 21, 21, 24, 26, 26, 28, 28]
def r2sG : List Nat := [3, 3, 7, 7, 14, 22, 11, 25, 11, 14, 14, 15, 29, 19, 25, 19, 22, 22, 23, 29, 25, 27, 30, 29, 30]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [6653375745539, 28677598216985]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x1f16380d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000aaaaaaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | _, _, _ => 0
def stateW : Nat → Nat
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
  | 0, 0 => 0x1ffe0000000000000000000000000000000000000000000000000000000000001f01fc000000000000000000000000000000000000000000000000000000000018e1c3c000000000000000000000000000000000000000000000000000000000061833a00000000000000000000000000000000000000000000000000000000000c78c5
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1fff0a00000000000000000000000000000000000000000000000000000000001f85fd00000000000000000000000000000000000000000000000000000000001cf1e3c000000000000000000000000000000000000000000000000000000000167af7f0000000000000000000000000000000000000000000000000000000000bcf9cf
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_31 == dom_31) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_31 goalM u ys) : RunD dom_31 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_31 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
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
  scr dom_31 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_31 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31 roots_31 goal_31 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_31 goal_31 := by
    have h0 : isConstB dom_31 goal_31 = false := by decide +kernel
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

end S_31

theorem low_31 : Lower dom_31 roots_31 goal_31 6 := S_31.noCircuit

namespace S_55
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (5, 7), (5, 37), (6, 7), (6, 22), (17, 19), (18, 19), (18, 22), (20, 22), (21, 23), (21, 53), (33, 35), (33, 37), (34, 35), (36, 37), (38, 39), (38, 54), (49, 51), (49, 53), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 2, 5, 5, 6, 6, 17, 18, 18, 20, 21, 21, 33, 33, 34, 36, 38, 38, 49, 49, 50, 50, 52, 52]
def r2sG : List Nat := [3, 3, 7, 37, 7, 22, 19, 19, 22, 22, 23, 53, 35, 37, 35, 37, 39, 54, 51, 53, 51, 54, 53, 54]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [55066650547715, 54040118821669, 55066600211222]
def xsM : List Nat := roots_55.map (· &&& dom_55)
def goalM : Nat := goal_55 &&& dom_55
def NN : Nat → Nat
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xa5e2e6eb
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff0000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aa00aa00aa00aa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | _, _, _ => 0
def stateW : Nat → Nat
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
  | 0, 0 => 0xfff0000000000000000000000000000000000000000000000000000000000000fc0fc00000000000000000000000000000000000000000000000000000000000c38e3c00000000000000000000000000000000000000000000000000000000003341b200000000000000000000000000000000000000000000000000000000000c3c4d
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfff8080000000000000000000000000000000000000000000000000000000000fe0fe00000000000000000000000000000000000000000000000000000000000ebaf3c0000000000000000000000000000000000000000000000000000000000b757f700000000000000000000000000000000000000000000000000000000005dfcdf
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_55 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_55 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_55 == dom_55) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_55 goalM u ys) : RunD dom_55 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_55 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
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
  scr dom_55 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_55 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_55 roots_55 goal_55 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_55 goal_55 := by
    have h0 : isConstB dom_55 goal_55 = false := by decide +kernel
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

end S_55

theorem low_55 : Lower dom_55 roots_55 goal_55 6 := S_55.noCircuit

def isoMv_47 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem low_47 : Lower dom_47 roots_47 goal_47 6 :=
  lower_iso isoMv_47 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (2, 3), (5, 7), (5, 37), (6, 7), (6, 14), (6, 22), (9, 11), (9, 25), (9, 41), (10, 11), (10, 14), (12, 14), (13, 15), (13, 29), (13, 45), (17, 19), (17, 25), (18, 19), (18, 22), (20, 22), (21, 23), (21, 29), (21, 53), (24, 25), (26, 27), (26, 30), (28, 29), (28, 30), (33, 35), (33, 37), (33, 41), (34, 35), (36, 37), (38, 39), (38, 46), (38, 54), (40, 41), (42, 43), (42, 46), (44, 45), (44, 46), (49, 51), (49, 53), (49, 57), (50, 51), (50, 54), (52, 53), (52, 54), (56, 57), (58, 59), (58, 62), (60, 61), (60, 62)]
def r1sG : List Nat := [1, 2, 5, 5, 6, 6, 6, 9, 9, 9, 10, 10, 12, 13, 13, 13, 17, 17, 18, 18, 20, 21, 21, 21, 24, 26, 26, 28, 28, 33, 33, 33, 34, 36, 38, 38, 38, 40, 42, 42, 44, 44, 49, 49, 49, 50, 50, 52, 52, 56, 58, 58, 60, 60]
def r2sG : List Nat := [3, 3, 7, 37, 7, 14, 22, 11, 25, 41, 11, 14, 14, 15, 29, 45, 19, 25, 19, 22, 22, 23, 29, 53, 25, 27, 30, 29, 30, 35, 37, 41, 35, 37, 39, 46, 54, 41, 43, 46, 45, 46, 51, 53, 57, 51, 54, 53, 54, 57, 59, 62, 61, 62]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [53932259088681, 54126186401283, 14543398241049, 42039359639062, 6709563696398, 54040252515109, 6653914526979, 23146217737753, 42039494117134, 54125816317721, 66220630278926, 41837630395150, 54125816316713, 14543767539203, 36448102585859, 41872511014403, 6688272354819]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 5 => 48
  | 6 => 676
  | 7 => 641
  | 8 => 45
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xf71c1030f1568eb8e22d262ae0802803e0645234de56981fdd1a5b1cd3bcdb79d00ae2a9cba49ca0c8373744bea363caba346190ba2417abb664526cb434601db0802a1dab23472da2ff1743a099e6d29bfc7cbd99bd0b2a9806a7b596b7fe99927f0db5925a20fe91c655dd8f4176b67852ed446a0153b268cf07606825d5e659df37c54e028a72457a831342a52997424f8c1c377c4b01340569fa337f57cb335ba3f632935a2228be08b8202215df1a077bf20d95e0800d213aee0ca3b5de
  | 6, 0 => 0x151b48d314cd083e149a449b146dd6781401a17513e889c512cb0a3211d7ef0c11a58ee01182c6e911146bc310f7dc1910ee966510d6ef02108dfb001042be7e0f886e6d0f39231c0f0a2ca10efc98350ed48efb0eccb7400ea563de0da2053a0d15d59f0cdf040e0c76b2fc0c5373540b760dc10a5a9dcf0a3edfed0a25bb570a0d2c480a077844097f425508eb11d108defe5008c07176082a1dbb081616210807ec25076a3e3a071ebcc6070b6e2706e4120e06b6b9590573298d0567fa5105495b4e0524aa2c04da3bcb043aed2d03fe10b503e8417902d338cd027b432e023e5948022760e601d045a50104b42a00f4ccb10084b00c0012918d0010041b
  | 6, 1 => 0x2f364e4c2eb2619a2e43076c2d7eac952d6ecb4f2cfd4cb22c5e54df2a410c0329bf13b4298caa25296764912866bf56281ee37b27bf8f0326b622e02608ac4425cfafe5254f9c3424313815241a1c8a23a8da9422cb4d0d22725c4621f40ce021d6d258212acd6b20a99be1204765262014b8841fa76a351f8294af1f3289d01f1339b11ec054711df565bf1de8e6291cb356241c5406471ba8fd461b8989a61af080381ae554351adda0ab19ccae5619a552161996d3a01932068f18a1f77718a1db0a18917f94185e1bcc185ae1601817360717e5a7ad1783d36c1765f31f170d28fa170095b516e53d6716d1a88d167d5873167b58e8163ab96d1576ce42
  | 6, 2 => 0x47a969a64798997147623978466a846245eb319d45d63c9845d333c344e317154421a80f43e02b9843cfd02243a6d475433fa33f4323f83b421efd334197cdb141814761417ae7e74103154f405380cd3fd129013fa021c53f0b3c833ef14cd93ec0ecb33e51fe3b3cc117773c904c443c153f903bcc4b8e3b7296e23b3a508c3ab9c1273a728eb63a60712939f45ca439b1313539aa4f6c39a731c539a6d15b39955ad5396b594f395f96ae394fcac6390d0b543899aedb38591bb53582312935389f9734d6594234bd92e334b9efcf3456a4b4340c055d33f54673334b791132db49ce329818b0324f851832008a29314fc4ae3134e2c230c5a1fa2fdad49c
  | 6, 3 => 0x5e71f8f65e656a0e5e655d4c5df3c6e45dd029f45d6eca4c5d03b9ec5ce587035c8e153c5bfa05395b3aef915b0b3ef55a85e43759cc583a5967cb1f592a4abf58dbfe4c58bcfd23586d653b57bff59157abf56d5745e0fb56b21c845678c310563267f65586900f557f5c91557784d654f6b5bf54c1720f54aaacd3549d984f53b9ba0951f4736e51eea6ae514d96cf50fcb6f250b98cc05051ca7b4f5a6fd74ed591294ecd1a174e7421054e4076434e2ee3624d8edfa44ce69ba94c3ac3c24b60c7774b3060ba4ae5bac34ac954934a974fec4a64fe6e4a4282984a19e0d6499b524549973a2e494735504926b51048ef7a5e4877acf8484290cf47ab7327
  | 6, 4 => 0x7a92b2b77a1a3cad79e9aa45797ec6d17976ef16794f6d02792e645b7891b1e478734632784a37a477c76e4b772d50a8764d3db575d6a32675564e4c74391d8f737c6a2472d87a34722f281471fe05ed71a8d4f0718e49e47111845170b28612706fc19e701c39856ef970426ee8d5556ee525036df384186d5d4dc16c55d0e46b2ac9b66a7ef1cf689eda766866d1d36821124f670627f36700302366fae65966e4cb6d66c30d4f667b89e2661766a5658297b76539ae4664ef0a7e64570b426452eb0d6412729763f43fae632c34926327452262f60e5762d8cb5d628d2c46628562b16280cd0860c081b7602bb2d36014a9d05fae7b465f3c4a0f5f16df6a
  | 6, 5 => 0x8fe727818f1475508f037d7a8e725f848e26e5f78e15b8678daa93db8d7584e38ce6acb38c0b847c8bea21d78b34a47b8b047cde8ae435ad8a8af92e8a7a9db889cec5d1893c789988d133a78880453c880cdd5b87f329e78747520087347efa8697e97e862eae4f85d6dadd85a4a1268577d88584fccbd1849fcae6847b5ba083e1371583ae4b3c8311509183083064829ee8b6828ebe06827719248232a1da81f06d12819b4b088103242c80f382ad8094d00f80420fc27fefa5537fcf8a267fc490577fa1e4517f5d02fb7e8d0d417e6b005c7e1c26677da27d9b7d6de1057d384bf87cc86c177bf891e37b901b097b725a9f7b4daf147acc2fde7a98c065
  | 6, 6 => 0xa97755a4a95a76f5a8fc3611a8cc5a0fa8255610a76b4f4da7454648a6bf7766a6768364a5c26085a570f6d1a5053c33a4c467f2a4bc745ba406231da35a4b36a3363a9ba2dee76ea2c78c72a2c0b485a2b12677a296fa28a22d274ca204a732a09d03cb9f6861d19f67cab99f6427a59f2bfd249efdaaf79ea165819e6e1c509e2dbe589c6f54319c029e899bd345fc9b5bb1f19b5a8a139b52b2589b27740c9aa6da719996536298e3b7e998b5e8a7989f410497ef9c399659f5eb9617cd3395826379953f9b7695225003942d0a49936a0d26934f2dc492f9ae42927e36f2923784189223dc8591d7069f9199b1d99180cfe59129b39190c0e84590978270
  | 6, 7 => 0xc3a85e1ec3a48965c3248b03c2d474bfc23ae89fc1fd94bec1984679c1438dfbc0aefa8cc060a091bf625b31becb0a92bcf80b4bbc9eab44bc8b9d4cbbf13299bbea8865bb9554cdbb25780fbae49c3bb853a286b8031352b7e923a8b7bc51e7b75e26bbb749d50ab6b24ed4b686bea0b62bf158b6187b80b5ed3c51b58ff299b533f09fb4081b57b3667e10b34b2de9b2a179deb2a00218b28503beb244fabcb22ac669b17c46f1b0f756bdb0f45aa7b0499080afedb434af5aa227af197be6aeb1faadae8a636eae7a07f8adce3011ad2c0b55ad245454ad1a0d32ac637b96ac207a85ac142108ac0d8531abd3209dab42051eaaf860f8aa4ba25ea9d0c5fc
  | 6, 8 => 0xdc530cc6dc270072dc240b61dbc78eb0dbbbbc27dba5c180d94e7810d8fc9c9fd83420ded825bc9ed8078597d7bf8d9ad76bb5dbd70860edd6d828a2d666a11bd51552b6d4f3c4e7d4d9d53dd43a869fd3ca8f6fd2c7f300d2b65212d29d8d76d23889ebd222218ed1c4f305d1a51e2fd1256833d06626b0d03db7cad02ede41d000bef7cfa9f353cfa8f22ecf6ae6fbce6a62a9ce3a49f5cdb5173bcd25444fcd029b64cb5c187fcad7f953ca2c216cca011952c9e6e84dc9ac6cdec955416bc949a14ac92eff1fc8c3d232c89b3aa8c8897092c85246a6c80f6476c80b3e80c7e9128dc74cba13c5d3a1b6c582ca07c576664ec4f09b0fc4ba697ec406c3f6
  | 6, 9 => 0xf62b4b74f609c098f6045146f6019973f5ece40cf524d273f4fbad49f477dc2af3ea6d26f3756ca3f35752b0f3498f0ef2ab5983f27dee33f1dfc445f115b5b9f0ffaaaeefb9afc6efa703a7ef554b37ef12d323eeb6c0aeeeb213ebee64586dedff4ae2edf3b601ed5e15c5ed2e695fec9aa4e8ec5ed828ec41d777ebed4b1aeb9e1ad9eb57b97ceb1a9bc8eafc68dfea9f9574e9c4d5cfe918fde8e7fc7670e721783ee6bd54c5e59b1a55e54da7b3e542f83be3e26edde3963e6de2d0e57ee271cd96e1d78511e1d1ec39e1c1513be0d17bb7e0b0c46fdf9bd708deb9fbbcdea4ce9ede7a6e86de3eef08dd889314dd580b4fdd03a133dc85c203dc5fc220
  | 6, 10 => 0xff99db15ff3a2dc7ff2ee50eff0d80a2fe6faf54fe6c20c9fdf4a2a0fdaefc54fd977f69fd93ab53fd82f821fd6000eefd03f230fca6220bfc7d7b9efc02cecffba0428cfb964055fb8694d5fb6b201bfad792e2fad3ffe0facfb439fac0f34cfa9321d7f9f5fb7ff9e348d9f980b498f93770f2f914bcf6f7f56088f7e9791bf794c018f760f6a9f6cf8829f6b5bc52
  | 7, 0 => 0x17c2485d1780280516ed244d169ad4dc168319a41658ec56163ab96d159b56a615303b8814c25be7147be17a14445611141f8fdd140ddc3213ec0a3313b478a2134220d912766fe611f546a611c9fc59108cbea210739a89106602d20edcd7070ed48efb0ecd7e060eccb7400e62c7b30de1f81f0db6ae630db3a33c0d359d660d31a8270c11c00d0b8bbf6b0b5d6d290a5133e10a4a180909d69a7109c8d28f093db6800801277907852a5a07540f0806e4120e06d33f7406c8af810626d891058c8cb80544cdf60499b2c1046cf47e0451cc9a043aed2d03a5f4b302fbbdeb02f5fddb02c7e1c60253480f01dd076b01c0cf2f0185e19d00f26ece002f4827
  | 7, 1 => 0x30c2219f30b17a1b30a941483092a0e22ffd69612ff00c9c2ee5f83b2ee1b4002d6782ad2cfda1512cf45da32ceb381e2cc710002c9d909e2b5379482ad82ba32ad2a9b42aa950482aa4095a2a360412292e66d928f2496d28a5bcb42880e0ed280c081526c74c0626b609292572009524f1d90e242a74e0241a19e722f2b390225227cd2232fccd21f40ce0216845b4213fea0120bd10b42039fdd7201138cd1eb180c41dad523a1d0c61251c7f660e1c1160c61c02e4e51bd38e271b9b06e31b96e8611b6588df1b22957d1ae554351a28899f19e4b47719c2d80519b15e681983ef5b19728323196939d2196926bf194d07b418bc18ae18b98c20189246be
  | 7, 2 => 0x48be36e948a30f4847f7376147c09368477294e6470ecdb246f3f1d646e757da46cd9c504621c46945d1eda14541e848452bb7f64514c0b444efaef644aae862448b58424488eff643e02b9843cfd0224323f83b42a809fe417604ab409f8ab4408d44063fe16c1f3fd89f2f3ef2c9303ecde4943eca17bc3e51fe3b3e22f7d83d7b1e3a3d32d0403d084ce73cc117773ca49d893c5cd0913c153f903bcc4b8e3ba453603b8c25f93aefec363ac6befb3a9cdd1a3a2919be3913ae5c3889bf72386dc67538495668381d549c376a4f693661bf2535db2393358f846f35895b0434f9221f34d1c21a34bd92e333ac494931c32ec331b30d7c315f0dca313507a6
  | 7, 3 => 0x63d8096f62a89ff761b3740a61356e3460c081b7608a602b6014a9d06013f4555fecffb25faaa4325ee65ec95e6214035e199a5c5db7a25f5d3edab75d017f515b8b47325b53dfd65b1760205ad310425a910ab55a0f56b158bcfd2357c463485731eb8a56c7b29456713ef9563a3637560409b255fdc57d555e780a54f23f9c54bb1162537f76e652b2351452652dd55264f3015223ea5a51f4736e5164663950c1bb7d509f8ca3509cfade50429db55015e3964f85907a4f2308104f1c75a54eb1e7524d2885244cd3f7294cae6cf64ca3de694c8d80f44c8364a34c50a0f34c1021324c034b734c02950f4b36c4a04b0d46544ae5bac349d837ae49c137dd
  | 7, 4 => 0x7b7c8fb07ac3e1087a98c0657a5ac63379fc07f6795af53878e4f5a278ba6f2e77cbd182773a3b4c770282c076b0ffbe76abcfae768e6365764d3db575a33707748bed82739f2b397278be2071e3fb2171cfa26f71cce63971a8d4f07128b497711403f87111845170f150466f36b6b86f014b916ee55b736ee525036d7b8cdc6d7263e76d5d4dc16cb455396bfb0bf96bbf6b7e6afb3f026ad542766a75398c6a498d116a2f9d676a04d46d69da458569904ec969415288690b0d3968f8c50e6874221a686021f667e36ec2679e3ab8679b211f6722ad0067108e5267103ec5664a2e4d6640f86d655e0be164bb1a686482b4d9644d15206438425e63ff7f47
  | 7, 5 => 0x93d86ffd935864a69353153f93494f8992a935379244de839242763790dec3a290c0e84590943691906c6bd9902d5b0c8f8b65ae8f0950aa8ed4acb68e6a85208d8425078cac4f718c6c5e0d8c0b847c8b9a7c8c8b3625d88b1d15ca8ae474e18ac1d3288a7a9a9d895dd9a188c8f86088ad1ada878389bf87263362868acfaf861a5c8185db428985b3ccb1859d96c6857f3777855ede98852f6aa28507f4ca84fccbd184d2c17584689b4d84135e9584013fe783b31a7d83490ab082843189824f20f6824ebd7681f06d128130b34b8128f3f380b18522809d616c8077f719804dee4d7f2d59fd7f087fb57dd7bdf57db0481d7c42909f7c3a52057b901b09
  | 7, 6 => 0xadcd0e94ad7136f2acd99b96abd3209daba7945fab7128a0aabb0592aa6baa8ba99d0106a9536d8da8fc3611a8aceb64a888922ba837e8f9a7de7870a77db8c7a6bea662a64e8b36a5ef21d7a5dd0329a5cfa42ba54349f0a4a77657a4234630a3ac4ce7a37ea8d1a304b735a258df4ea1f4e361a10a5eb9a0c6aa12a039bc459e60f45a9deb9d439cee05e09ce2885c9ca6bdbc9c31e4e49c26fc249c0a3ca09bea8a5f9bca85189b4c7f429b0e75849b0132a19a31aaa699d4553f9972845b9941b91698fd6fd7988b180e9839f57d97e4107297942172967edfc895feb81b956af0e495546bd094ea215094dbd1b494acc9529492ddb29437159c93ffe5d5
  | 7, 7 => 0xc8357a45c82a4e78c7abb727c77e7691c66c1ee5c629c73fc5ca4838c58557c3c5825014c3753fb4c2d474bfc2157f87c18ac36bc169a7a0c11b76cfc060a091c02871dec026c9e4bf75efa6bed51344bebd2cbbbead66f1be769f18be620e8cbdbc8780bd15572dbc1d1430bbc46b4fbb25780fbab4727aba47a138ba2b822dba11faf3b99fd817b9653685b8db3bf4b7f96484b7794bf6b749d50ab65b2236b5e0fc76b5c668b8b4659c05b413c523b40748eeb401a675b34b2de9b275c1e6b24f2404b19e29acb1838f47b1295a81b0b62913b0b06ff8b03b1c5fb0049811af99e6ccaf359018aeec9bcaae96a897ae08364cadf62d26adf473f8adcd7c31
  | 7, 8 => 0xe50d18f3e45de151e4386609e3963e6de2760958e1f09bdde1edd638e1df1b87e183f5d5e173acfedf9a4d5adf35f6a6df1b03fddea4ce9ede53bb01ddb2f137dd44ebefdcf66048dc851221db2c04c2db27b5cbdae1e332dabcacbbdab6ff36da067d68d99d6794d8fc9c9fd80e38fad7c3a15ed7b2eb4bd64ef1c4d6363344d5f72ec6d43a869fd35f5289d358ca24d2c7c583d271ba71d24ac501d175aa0ed111535ad0c9d227d0bc3a17d0657b73d03a22d3cff609b7cedaf033cea8ef3bce16f6e3cdef810bcdef7705cd52d7cdcbbcb7cecb78c448cad7f953caccec61ca2c216cc9d81675c9ad816cc9ac6cdec98e47ffc972257ac90dcec6c8e27018
  | 7, 9 => 0xff18459fff123350ff0a3806fee14d72febb539efdf4a2a0fda9c5a0fd76da79fd533e5bfd1304b1fc4e4806fbadfa39fb6d2ecffb34fe8ffab21684faa3a2ccfa359d84f9a8b337f92dd199f8f9194ef8ec2452f85d4df5f8037aa5f75ba0adf61649e1f56a71faf542c7dcf46969daf3caa704f3c7c120f3498f0ef1dccc71ef2e9b0fee9b0dd6ee82c328ee18b783ee12c54dedacebaced6973f8ece046c1ec663512ec58a0dbec4ae460ebed4b1aeb406b8feace13c6eac36ef1eab44034ea5d6b67ea5d0618e9e3dfc4e9a376e3e9877a69e9430aa7e8dba282e8a202a5e7baf5ffe78c552be72b167be6527f1ce604fcffe5f93c5de5f2c308e59e6d1a
  | 7, 10 => 0xffb3f673
  | 8, 0 => 0xfe971ab2f9554771f92dd199f61649e1f56a71faee12c54deab44034e5f2c308d43a869fc708d5a6c68acfd0c43bc065c0a94172c02871debc1d1430ba47a138b749d50ab40748eeb158ad0fb03b1c5fa4234630a0e187959437159c8ff96af68f8b65ae8302b3d677cbd18269904ec962a89ff75d017f514e31041e46d9577144efaef6448b58423ef2c9303e51fe3b3d084ce73ba45360358f846f242a74e0196926bf1957081117a485a0167ebc1d043aed2d
  | 9, 0 => 0x69904ec9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xeeeeeeeecccccccc000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000cccc3333cccc3333000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000c3c3c3c3c3c3c3c3000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa
  | 0, 1 => 0xf0f0f0f0c0c0c0c0000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c8000000000000000000000000000000000000000000000000faf0faf0c8c0c8c0000000000000000000000000000000000000000000000000ff0000ffff0000ff000000000000000000000000000000000000000000000000cccccccccccccccc0000000000000000000000000000000000000000000000005a5a5a5a5a5a5a5a000000000000000000000000000000000000000000000000f8f8f8f8f8f8f8f8
  | 0, 2 => 0xc0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000ff00ff00cc00cc00000000000000000000000000000000000000000000000000aaaaaaaaaa88aa88000000000000000000000000000000000000000000000000cc33cc33cc33cc33000000000000000000000000000000000000000000000000aaaaaaaaaaaa8888000000000000000000000000000000000000000000000000eecceecceecceecc000000000000000000000000000000000000000000000000aaaaaaaa88888888000000000000000000000000000000000000000000000000ff00ff00ff00cc00
  | 0, 3 => 0xaaaa5555aaaa5555000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000eaeaeaeac0c0c0c0000000000000000000000000000000000000000000000000ffffaaaaffff0000000000000000000000000000000000000000000000000000a5a5a5a5a5a5a5a5000000000000000000000000000000000000000000000000ffff0000eeee0000000000000000000000000000000000000000000000000000f0f0f0f00f0f0f0f000000000000000000000000000000000000000000000000fffcfffccccccccc
  | 0, 4 => 0xffffaaaacccc8888000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000ff00ff00ee00ee00000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000ffff00000000ffff000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000eeaaeeaacc00cc00
  | 0, 5 => 0xffff0000cccc0000000000000000000000000000000000000000000000000000f00ff00ff00ff00f000000000000000000000000000000000000000000000000f0f00f0ff0f00f0f000000000000000000000000000000000000000000000000ff88ff88ff88ff88000000000000000000000000000000000000000000000000ffffff00ffffcc00000000000000000000000000000000000000000000000000aaaaaaaa55555555000000000000000000000000000000000000000000000000ffeeaaaaffcc0000000000000000000000000000000000000000000000000000ee00ee00ee00ee00
  | 0, 6 => 0xaa55aa55aa55aa550000000000000000000000000000000000000000000000003c3c3c3c3c3c3c3c000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0000000000000000000000000000000000000000000000000ff00ff0000ff00ff000000000000000000000000000000000000000000000000aa88aa88aa88aa88000000000000000000000000000000000000000000000000ffaaffaacc88cc88000000000000000000000000000000000000000000000000aa00aa00aa00aa000000000000000000000000000000000000000000000000009999999999999999
  | 0, 7 => 0xcccccccc33333333000000000000000000000000000000000000000000000000e0e0e0e0c0c0c0c0000000000000000000000000000000000000000000000000aaaaaaaaaa888888000000000000000000000000000000000000000000000000fa00fa00fa00fa00000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000006666666666666666000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000ffffaaaaffff8888
  | 0, 8 => 0xfafafafafafafafa00000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000fffffffff0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e00000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000ffffff00ffff0000
  | 0, 9 => 0xcdcdcdcdcdcdcdcd00000000000000000000000000000000000000000000000000ff00ff00ff00ff000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000333333333333333300000000000000000000000000000000000000000000000000000000aaaaaaaa000000000000000000000000000000000000000000000000ffffffffcccccccc
  | 0, 10 => 0xffffff00ffffff00000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000000005555555555555555000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffffffffc0c0c0c0000000000000000000000000000000000000000000000000aaa8aaa8aaa8aaa8000000000000000000000000000000000000000000000000ffccff00ffccff000000000000000000000000000000000000000000000000000000ffcc0000ffcc
  | 0, 11 => 0xffff0f0fffff0000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000ffcc0000ffcc0000000000000000000000000000000000000000000000000000cccccc88cccccc88000000000000000000000000000000000000000000000000fafa0000fafa0000000000000000000000000000000000000000000000000000ffffffff88888888000000000000000000000000000000000000000000000000ffff0f0fffff0f0f0000000000000000000000000000000000000000000000000f0f00000f0f0000
  | 0, 12 => 0xf0f0f0a0f0f0f0a000000000000000000000000000000000000000000000000055555555ffffffff000000000000000000000000000000000000000000000000ffffffff55555555000000000000000000000000000000000000000000000000ffff0033ffff0033000000000000000000000000000000000000000000000000ffffffff44444444000000000000000000000000000000000000000000000000ffffffffcccc0000000000000000000000000000000000000000000000000000f0f0f0f0f0c0f0c0000000000000000000000000000000000000000000000000ffff000fffff000f
  | 0, 13 => 0xcfcfcfcfcfcfcfcf0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c000000000000000000000000000000000000000000000000ffffffffccc0ccc0000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000f0f0f0f0e0e0e0e0000000000000000000000000000000000000000000000000fefefefecccccccc000000000000000000000000000000000000000000000000faf0faf0faf0faf0000000000000000000000000000000000000000000000000faf0faf000000000
  | 0, 14 => 0xffffffffffff0000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ffff8888ffff8888000000000000000000000000000000000000000000000000ffffaaaa0000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000001f1f1f1f1f1f1f1f000000000000000000000000000000000000000000000000ffff5500ffff5500000000000000000000000000000000000000000000000000ffffffffcc00cc00
  | 0, 15 => 0xcccccccc00000000000000000000000000000000000000000000000000000000f0f0f0f050505050000000000000000000000000000000000000000000000000000055550000ffff000000000000000000000000000000000000000000000000ffeeffeecccccccc000000000000000000000000000000000000000000000000ffffffff50505050000000000000000000000000000000000000000000000000fafafafa000000000000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000ffffffffffcccccc
  | 1, 0 => 0xcc00cc00cc00cc00000000000000000000000000000000000000000000000000ffffffff11111111000000000000000000000000000000000000000000000000cccccc00cccccc000000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000ccccccccffffffff0000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000ffffffff8080808000000000000000000000000000000000000000000000000000000000fafafafa
  | 1, 1 => 0xccc8ccc8ccc8ccc8000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000ff55ff00ff55ff000000000000000000000000000000000000000000000000003f3f3f3f3f3f3f3f000000000000000000000000000000000000000000000000ff0cff0cff0cff0c000000000000000000000000000000000000000000000000ffffffff0000cccc
  | 1, 2 => 0xcc88cc88cc88cc88000000000000000000000000000000000000000000000000ffffffffffccffcc000000000000000000000000000000000000000000000000ffccff88ffccff88000000000000000000000000000000000000000000000000ffffffffccccc0c0000000000000000000000000000000000000000000000000ffffcc88ffffcc88000000000000000000000000000000000000000000000000cccccccccc00cc00000000000000000000000000000000000000000000000000ffffffffaaaaaaaa0000000000000000000000000000000000000000000000000f0f0f0f0c0c0c0c
  | 1, 3 => 0xaaaaaaaaaa000000000000000000000000000000000000000000000000000000ffffffffffffcccc000000000000000000000000000000000000000000000000ffffffff00cc00cc000000000000000000000000000000000000000000000000000000003f3f3f3f000000000000000000000000000000000000000000000000afafafaf000000000000000000000000000000000000000000000000000000003232323232323232000000000000000000000000000000000000000000000000cccccccccccc0000000000000000000000000000000000000000000000000000ffff0c0cffff0c0c
  | 1, 4 => 0x5555000055550000000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ff0fff0fff0fff0f0000000000000000000000000000000000000000000000000f000f000f000f00000000000000000000000000000000000000000000000000ffffffff00550055
  | 1, 5 => 0x33ff33ff000000000000000000000000000000000000000000000000050f050f050f050f000000000000000000000000000000000000000000000000eac0eac0eac0eac00000000000000000000000000000000000000000000000000000eeee0000eeee000000000000000000000000000000000000000000000000ffffffffcc88cc88000000000000000000000000000000000000000000000000f5f5f5f5f5f5f5f50000000000000000000000000000000000000000000000005050505050505050000000000000000000000000000000000000000000000000ffff5555ffff5555
  | 1, 6 => 0x8f8f8f8f8f8f8f8f0000000000000000000000000000000000000000000000000f0f0f0f3f3f3f3f000000000000000000000000000000000000000000000000f0f0f0f0f3f3f3f3000000000000000000000000000000000000000000000000eeeeaaaacccc0000000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000aaaa8888aaaa8888000000000000000000000000000000000000000000000000ffffeeeecccccccc000000000000000000000000000000000000000000000000f0e0f0e0f0e0f0e0
  | 1, 7 => 0xfafa0000fafa0000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000ffaaffaaff00ff00000000000000000000000000000000000000000000000000ffffffffff000000000000000000000000000000000000000000000000000000cccc8888cccc8888000000000000000000000000000000000000000000000000ecececececececec000000000000000000000000000000000000000000000000bbbbbbbb00000000000000000000000000000000000000000000000000000000000033ff000033ff
  | 1, 8 => 0xffff1111ffff1111000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000ffffffffc8c8c8c80000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000aaaaaaaa88008800000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000f3f3f3f300000000
  | 1, 9 => 0xff11ff11ff11ff1100000000000000000000000000000000000000000000000088888888aaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaa80808080000000000000000000000000000000000000000000000000f0f0f0f0fafafafa000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000fffffffffcfcfcfc000000000000000000000000000000000000000000000000ffffcc00ffffcc00000000000000000000000000000000000000000000000000ffffffff0c0c0c0c
  | 1, 10 => 0xffff00aaffff00aa000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000000ff550000ff550000000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea000000000000000000000000000000000000000000000000ffffffff55550000000000000000000000000000000000000000000000000000ffffffffdddddddd0000000000000000000000000000000000000000000000007070707070707070000000000000000000000000000000000000000000000000ffffffff0f0f0000
  | 1, 11 => 0xf0f0f0f0f0f0c0c0000000000000000000000000000000000000000000000000faf8faf8faf8faf8000000000000000000000000000000000000000000000000fafafafac8c8c8c8000000000000000000000000000000000000000000000000ffff3333ffff33330000000000000000000000000000000000000000000000003333000033330000000000000000000000000000000000000000000000000000ff05ff05ff05ff05000000000000000000000000000000000000000000000000ffffffff000f000f0000000000000000000000000000000000000000000000000000fff00000fff0
  | 1, 12 => 0xffff0000000000000000000000000000000000000000000000000000000077777777000000000000000000000000000000000000000000000000ffaaaaaaff000000000000000000000000000000000000000000000000000000aaaaffff0000ffff0000000000000000000000000000000000000000000000000707070707070707000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000f3f30000f3f3000000000000000000000000000000000000000000000000000000000f0f00000f0f
  | 1, 13 => 0x5f5f5f5f5f5f5f5f000000000000000000000000000000000000000000000000ffff333300000000000000000000000000000000000000000000000000000000f0f0e0e0f0f0e0e00000000000000000000000000000000000000000000000000077007700770077000000000000000000000000000000000000000000000000ffff0000ffcc0000000000000000000000000000000000000000000000000000ff80ff80ff80ff80000000000000000000000000000000000000000000000000ffffffff0000555500000000000000000000000000000000000000000000000000fa00fa00fa00fa
  | 1, 14 => 0x5555555577777777000000000000000000000000000000000000000000000000ffff8080ffff8080000000000000000000000000000000000000000000000000ffffff00ff00ff00000000000000000000000000000000000000000000000000ff33ff33ff33ff330000000000000000000000000000000000000000000000003300330033003300000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a800000000000000000000000000000000000000000000000000ee00ee00ee00ee00000000000000000000000000000000000000000000000000000000ffffaaaa
  | 1, 15 => 0x2222222200000000000000000000000000000000000000000000000000000000ff55ff55ff55ff550000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000ffffffff55005500000000000000000000000000000000000000000000000000ccccccccc8c8c8c80000000000000000000000000000000000000000000000000000000055555555000000000000000000000000000000000000000000000000003300ff003300ff000000000000000000000000000000000000000000000000000000ff0000ffff
  | 2, 0 => 0x2222222222222222000000000000000000000000000000000000000000000000ffff0505ffff050500000000000000000000000000000000000000000000000000000000222222220000000000000000000000000000000000000000000000000000777700007777000000000000000000000000000000000000000000000000faf00000faf00000000000000000000000000000000000000000000000000000ffffffff05050505000000000000000000000000000000000000000000000000afafafafafafafaf0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a
  | 2, 1 => 0xfcfcfcfccccccccc000000000000000000000000000000000000000000000000ffffffffeeeeeeee000000000000000000000000000000000000000000000000ccccc8c8ccccc8c80000000000000000000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000000000dddddddddddddddd0000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000ff33ff3300000000000000000000000000000000000000000000000000000000bbbbbbbbbbbbbbbb
  | 2, 2 => 0xfff0fff0ccc0ccc0000000000000000000000000000000000000000000000000f3f3f3f3f3f3f3f30000000000000000000000000000000000000000000000003030303030303030000000000000000000000000000000000000000000000000ffffffffcccc88880000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000ffff3333ffff0000000000000000000000000000000000000000000000000000cccccccceeeeeeee000000000000000000000000000000000000000000000000af0faf0faf0faf0f
  | 2, 3 => 0x37373737373737370000000000000000000000000000000000000000000000001111111133333333000000000000000000000000000000000000000000000000000000003333ffff000000000000000000000000000000000000000000000000cccccccc888888880000000000000000000000000000000000000000000000000000333300003333000000000000000000000000000000000000000000000000ffccccccffcccccc000000000000000000000000000000000000000000000000f3f0f3f0f3f0f3f0000000000000000000000000000000000000000000000000aaaaaaaa88880000
  | 2, 4 => 0xccccccccc0c0c0c00000000000000000000000000000000000000000000000001111111111111111000000000000000000000000000000000000000000000000ffffffff3333333300000000000000000000000000000000000000000000000000000000ffaaffaa000000000000000000000000000000000000000000000000777777777777777700000000000000000000000000000000000000000000000000000000fff0fff0000000000000000000000000000000000000000000000000ffffffffcccccc00000000000000000000000000000000000000000000000000f1f1f1f1f1f1f1f1
  | 2, 5 => 0xfaaafaaafaaafaaa000000000000000000000000000000000000000000000000aaaaaa00aaaaaa000000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e00000000000000000000000000000000000000000000000000000000eeeeeeee0000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000ffffffff0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000f300f300f300f300
  | 2, 6 => 0xfffffafafffffafa000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000fefefefefefefefe00000000000000000000000000000000000000000000000000cc00cc00cc00cc000000000000000000000000000000000000000000000000fafafafaaaaaaaaa000000000000000000000000000000000000000000000000fffffffffafafafa000000000000000000000000000000000000000000000000fffff0f0f0f0f0f0000000000000000000000000000000000000000000000000fffff000fffff000
  | 2, 7 => 0xaaaa0000aaaa000000000000000000000000000000000000000000000000fffffffff0f00000000000000000000000000000000000000000000000000000eeaaeeaaeeaaeeaa0000000000000000000000000000000000000000000000000000cccc0000cccc000000000000000000000000000000000000000000000000ffccffcccccccccc000000000000000000000000000000000000000000000000fafafafaf0f0f0f000000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000ffffc0c0ffffc0c0
  | 2, 8 => 0xfafaaaaafafaaaaa000000000000000000000000000000000000000000000000ffccffccff00ff00000000000000000000000000000000000000000000000000ffffa0a0ffffa0a0000000000000000000000000000000000000000000000000ffffffffaaaa0000000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000ffffaa00ffffaa00000000000000000000000000000000000000000000000000ccc0ccc0ccc0ccc0000000000000000000000000000000000000000000000000ffaaffaaaaaaaaaa
  | 2, 9 => 0xf0f0f000f0f0f0000000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000ffaaaaaaffaaaaaa000000000000000000000000000000000000000000000000ffffffaaffffffaa000000000000000000000000000000000000000000000000ffeeffeeffeeffee000000000000000000000000000000000000000000000000ffffffffa0a0a0a0000000000000000000000000000000000000000000000000eeeeeeeeaaaaaaaa000000000000000000000000000000000000000000000000fcfcccccfcfccccc
  | 2, 10 => 0xffffffffffffaaaa000000000000000000000000000000000000000000000000fcfcfcfcf0f0f0f000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000fff0ff00fff0ff00000000000000000000000000000000000000000000000000fffafffafffafffa00000000000000000000000000000000000000000000000000000000cccccccc
  | 2, 11 => 0xfff0fff0ff00ff00000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0a0000000000000000000000000000000000000000000000000aaaaa0a0aaaaa0a00000000000000000000000000000000000000000000000000000ff000000ff00000000000000000000000000000000000000000000000000fff0fff0f0f0f0f0000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000ffa0ffa0ffa0ffa0000000000000000000000000000000000000000000000000fffffffff000f000
  | 2, 12 => 0xffff0000000000000000000000000000000000000000000000000000fcccfcccfcccfccc000000000000000000000000000000000000000000000000f0f0f0f0f000f000000000000000000000000000000000000000000000000000aaaaaaaaaa00aa00000000000000000000000000000000000000000000000000ffffccccffff0000000000000000000000000000000000000000000000000000ffffaaaaaaaaaaaa000000000000000000000000000000000000000000000000fffffffffff0fff0000000000000000000000000000000000000000000000000fcf0fcf0fcf0fcf0
  | 2, 13 => 0xf0a0f0a0f0a0f0a0000000000000000000000000000000000000000000000000fffffffffffff0f0000000000000000000000000000000000000000000000000fffffff0fffffff0000000000000000000000000000000000000000000000000eeeeaaaaeeeeaaaa000000000000000000000000000000000000000000000000ffffffffffaaffaa000000000000000000000000000000000000000000000000fffcfffcfffcfffc0000000000000000000000000000000000000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000ffffffffaa00aa00
  | 2, 14 => 0xf0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000fffff0f0ffff0000000000000000000000000000000000000000000000000000fafaf0f0fafaf0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0000000000000000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000fffffcfcfffffcfc000000000000000000000000000000000000000000000000ffffeeeeffffeeee000000000000000000000000000000000000000000000000ccccc0c0ccccc0c0
  | 2, 15 => 0xfcfcf0f0fcfcf0f00000000000000000000000000000000000000000000000008080808080808080000000000000000000000000000000000000000000000000ffffffccffffffcc000000000000000000000000000000000000000000000000fff0f0f0fff0f0f0000000000000000000000000000000000000000000000000ffaaff00ffaaff00000000000000000000000000000000000000000000000000eeeecccceeeecccc000000000000000000000000000000000000000000000000ffc0ffc0ffc0ffc000000000000000000000000000000000000000000000000000ff000000ff0000
  | 3, 0 => 0xffffcccccccccccc000000000000000000000000000000000000000000000000aaaaaaaaa0a0a0a0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x200c040a0da868040605045406020c82800a030c0082e005018580c0a0aa81006060a001406020782826a030101824115018401e0a00280c1c0206801406020602800a0405818140050200c040a04a80c040803801408020301400a040180802005
  | 5, 0, 1 => 0x178080c0a09a810062e05001408021682800a03160180e005158081e0a00280c0406050a9452020302800a03030a014115138080c0a13280c4a060504541c241182800a220101814005018840c2000281004060507d406020f07400a1c0103c14005
  | 5, 0, 2 => 0x200c504220a900040f0500140602030fc00a1c010f814005018080c0a1ea810063c068ed408030101874a02030e4141151c0081e0a0028100606050dd40803010006ca04018081a355018d00c0a00280c0406038cd406320302862a04018080c305
  | 6, 0, 0 => 0x14c06020782800c000200c04060514980048019440c0a0030009003010181400600010040605000a0c000200c040627801800040191c143b273000080203134724160000c1c020500098c00018088e0a258ed8000203028001121b000060203000944962400c04060500066e000200c8e3c050ed800030103c14002330008a022202800436
  | 6, 0, 1 => 0x10be020500098c0001018bc39050018000203028aa43233000ba0203028004660000c04060004494c000200c04062e001800040111cb60a1db000080307828004e60012006020303400c00018081e0a0012d8004501808880025300008020f05c004360016806020302800c0002164040a00161800042b9580c0a2ab00008540302862436
  | 6, 0, 2 => 0x7004060512caac000200c04670500180003030280066273000b40316018140060019406020302800c000200c04062690580004018081017003000086401018140060018c06020302800c000210004060515580004019500c31253000900316018140060018806020300094c000200c04610500180004300080c0a003000060e010282e006
  | 6, 0, 3 => 0x10e20203028aac002400c2006050018007001018140021b0000803011bc006e6001b406020302800c000201872280500180004019b0040d0030009003011ac140060000c046a0302800c000201814552710d80003011a4d00a00300090030111c143b600010ba06050009cc0001018144b2a90d8000301018aa4a233000ba0203028004b6
  | 6, 0, 4 => 0xc040603828aac000200c0c552513980065018080c0a25b0000802030284c796001e006020302800c00018080c4b2a929800773b0081400263000087501018004a60000c04060512c66c003a00c0c0a0013980004018b00c4d20b000083801018140060000c0400251cc98c000200c040a001c980048018081e0a00300090030101814136
  | 6, 0, 5 => 0x120ba020302800c004080c0406050018000301028004c24b000060203028008060012006063f8009cc000200c047e0500180070018080c00253000080301108004160000cf406050009cc000200814002610d8000203028004b3eb000067c01018140060000c42020301c00c0002070040a001318007b018080c0a003000067a1e01814006
  | 6, 0, 6 => 0xc040a0004498c0002008100a0010d8000401a2c0c0a2ab000060e03028004e60001006020f00114c000200d1206050018008801018140021b000080301000944c60001042064380086c004300c04060500180004018840c85003000047a2d818140060019406020302908c00240080c0a2a90d8005301808880a00300006020320c00826
  | 6, 0, 7 => 0x1006020680076c004a00c04060500180004498080c0a003000060205154984660012006020324800c00488080c0a2590d80004018081000253000ca0203028aa4360012006020500120c000200c04064780180004019501431263000c40301028004c60000c041e0301c00c0002238048d0013180048018080c5525300008030123014006
  | 6, 0, 8 => 0xcd823050008cc0001808144b2a931800020302800432330000898010181400600010ea020500098c004880c04062592980004018840c97003000063201018140060000c040605154e6c0002008840a0010d80003011a414002330000802030e4145560019406020315494c004b00c2c060500180003010189a0a08b00008034a81814006
  | 6, 0, 9 => 0xc0406050444cc00020f00c0a0010d800030101814004fb000a60203028004360027806020782800c004e80c0c0a0013980003011a4140025b000080301108004a60000c04060500138c0001808149b00131800773b0181400273000080301018009a60012006020326400c003800c040a0013180003030009473273000080305154984e6
  | 6, 0, 10 => 0x10063c0300094c000200c0c0a18a9180053018080c00253001460203028004360000c0c0a0013892c000200d440a002858000301019060a2ab0000803288181455600010ea020402800c000200c0406051558000403028004e21b000066c11828004b6000080c0a0012c86c00018080c0025119800040e018140027300140030101814006
  | 6, 0, 11 => 0x1006025502952c00022a004060529d80003518080c0025300008031601814556001140644050009cc000200c4287001318000301018145541300006020f05c00466002994a060500086c00018080c07050018000401818004a273000900301028aa4c60000ca806050c48cc00018080c002592980004018080c0d2ab0011c020323400466
  | 6, 0, 12 => 0x120066c1182800c005300d4a06001298004801018140021b00008030102800ae60000ca8060512c62c04018080cad05001c0062018181400273000a603010782e006000111c06468009cc00240700406050018000401018140056300008022d818004a60023804064680096c002400c046905001800ab018080c0a003000060605000224e6
  | 6, 0, 13 => 0x1006025a82800c002400c0406001298000301019680a00300008b30101814b260024406020512c98c005880c04060500180004018081e0a2ab0000606051549c4660000ca8a30302862c000200c04b0050018000301018140057b000ca0301028aa4c6001d40406050008cc002d0080c0a0010d80004018782e0027300006020f05c004b6
  | 6, 0, 14 => 0x3848020302800c0001808140026119800040101814005c3000908e010191a0060012006020304800c00018080c0a3315580003030289655273000ee04288181400600010ea06050009cc003a8080c0a0012d8006501018140021b00008020313482436000100602050016ec0001838044705001800040180814005b3000b40301018004a6
  | 6, 0, 15 => 0x10063c0500098c00599d00406050998001c5e8080c0a003000a60301028004c60000c04061002800c005e00c0406051558000203178140021b000900207828004360019406020300094c000223804065d80180003012d414004130009003010782e0060001006025d05c00c00018080cb90012980048019500c0a18b000085d0101814556
  | 6, 1, 0 => 0xd46020500098c00018080c5e0012980048018081e0025300006023d018145560000c0408050008cc006200c0406050018000352818140061b00006020302800c2600010ac060500182c00018098006001298000401828004c27300008020302800bf60000c040a0012c98c00018840c870011980074018080c0a2ab00008030105c00be6
  | 6, 1, 1 => 0x100608050009cc0001808100a0012d8000401000944c21b000700203028001160029806a50500098c00018840c870012d8005a3a8080c0a00300190030101814006000100c280500086c006200c04060680180004638080c0a00300008022d828004c6001200606051549cc000231804c50012980048018080c7f2ab00090750101814006
  | 6, 1, 2 => 0xc04060380082c004880c0c0a25939800480d0080c0a003000086c1208c1400600010062c0302800c002d00c040a001318000301018140041300194030103c140060000c0442050008cc003280c0c0a2a93980004648080c002530000875010189a4160012006020500098c000200c0c280012980004018080c0d003000060e0101814556
  | 6, 1, 3 => 0xc0406050019ac000200c0447068ed8000401809980a003000ca0301028004c60001006022690498c002400c04080500180027018080c0a003000082401018004a6000100642050009cc00018f00c0a001198000301108140025b0000803011ac140060001006022382876c002400c42064380180077018081e0a00300006022202800cb6
  | 6, 1, 4 => 0xc043e0500096c00018f00c0a0012d800d3018080c0a2ab0009003010181415600010ae560300094c006900c0406051558000401808140068b000902b01018140060034006020500098c000200d9e06050018005a01808100a00300008030103c140060000c30020302800c00018080c0a0033980004018080c0a09b0000606050009c466
  | 6, 1, 5 => 0x1006020413482c0002070040605155800030103c140041300008b30101814d66001200602032e800c000200c0469051558000203000944323300008d501018145560000c0c0a0012c9cc003b9d804060515580003011781400263000080301350143b60000c04062a928e6c00018094a0f05001800022d8181400233000a60303028004e6
  | 6, 1, 6 => 0x80c002592886c000e0080c07050018000301018144b593000380203000964a60000c04060515492c000216c0c0a00139800022d818140025b001b20301018140060012006022102800c0001a8c0c0a0013980004200080c00253000085b1e0181400600010066c11828aac00020080c0a2a90d800040101814006c300008d703028004e6
  | 6, 1, 7 => 0xc040605044aac000200c040a00241800040101814003eb00090031e0181400600114060222028aac000200c04de0500180003013740c0a003000080344828004c600011b80203001b6c000200c04062a9298000464808140026300008b3010184c4a60001006da0302800c000200c500a00131800020301c140021b0000806001289c436
  | 6, 1, 8 => 0x1048020500098c00018082c0f0500180004018083c172ab0000803010781a006001680606050009cc00018080c4d20919800040188c1400713000c40301018145560000c047a0303400c0002009c2060012980004470080c8d2ab00006020301c004a60001004c505001c0c000200c044d211058004801818140027300090030137c14006
  | 6, 1, 9 => 0x1d8040605001cec00018080c0a00399800c601314140023300006e5010181400600010ae560500098c003280c0c0a0013980004018189a412730000602239e8143b60000c04062692c82c000200c0444068018000203029c80025b00006022f108140060012004060012886c000200c040a0038d8006501808fc0a2ab00090022d81814006
  | 6, 1, 10 => 0x121d6020302800c0001818bc0a0013980004200081400263000900307828004e6001c0060203028aac000200c50420500180048018081e7f00300008032a018143360029838020302800c000200dd4060500180002050009843233000089801028004c60011406020782800c007480c0406050018000401818140074300008750101814556
  | 6, 1, 11 => 0x12006020313482c006900c040605001800040180814552630000803013b4140060001166020509898c0002028004c2710d80004018181400763000040a0012c984360000c0400251308cc00648080c0a001198001c01028004b26300090030118414006000080c0a001cc86c0001818500a00119800046331414002730018c0262828004b6
  | 6, 1, 12 => 0x1006f403001e6c00018080e0a001318000401800944c27300006020012c944c60001006020b801e4c004e80c040605001800c901018140025b00008030302800f160016806020313482c0001818500a0012d80091018080c0a08b000060203000947360000c040605001e0c00020080c390012980004018088e0a77b001dc0301018004a6
  | 6, 1, 13 => 0x15cac06050008cc00020080c0d0010d8000401808100a2ab00006020302800496000100602033ec00c00018080c0a25be9800040181814007cb00008020302800f86001218c026282800c00240e0040605001800030101814007bb0000406418280043600011ec020302800c000200c42064395580024010181400233000eef50101814006
  | 6, 1, 14 => 0x12192020302800c00018080c4d2f1058000301018140008b0009003030a0140060001058060500086c00018080c830012980004019440c0025300004060500086826000104806050009cc000200c0406001298002401018140025b00090031281814006002785e020302800c000200dfc06053f5800fc018080c0a2ab00090020500098436
  | 6, 1, 15 => 0x40806020302800c0001809980a0012580004018081501803000060203028aa46600010040f0500086c00598080c0a131198006501808fc0a0030000c0a001388646600010060221028aac000200c041e0b80180004018b00c0025300006020300094826000100447050ec86c002400c040025131800572b018140025b00006020300094ff6
  | 6, 2, 0 => 0x1006020780094c000101814003310d800030102800732630000c0a0012c9c43600010063c03028aac0001818004a2711980004018088e0a793000a60301018145560001004390500098c000e0181400259398000301018140082b00090240101814006000100606268a082c00020080c0a0041180004011a6060a00300008030111c764a6
  | 6, 2, 1 => 0x1006020342e14c0001818004b2513980003848080c0025300008030101a110760000d460203028aac00018080e3e0500180004830080c0a003000060207828001160000c0c5e1402800c002415cac06050018000401818145527300006020302896556000116606050989cc0002238040642801800043a8080c0a00300166020302896266
  | 6, 2, 2 => 0x8f4060500086c0001809060a0013180004019441400263000080301028004c60001006020343400c00241000406050018000401018aa4a21b000060203028010c60029806a503028aac0002174040600129800043a8b00c0a003001900301028004c6001d004060500086c00018180e0a001398000301018006625300008022d81814556
  | 6, 2, 3 => 0x10062c0500098c000200c040a8800180003011e80c00253001100301018140060000c040a0013104c002d00c04060515580004471440c0a00300090030101814556001d006020300094c00242cc04060509980004018081a0026300008030143c2e006001200c0a0013886c008700c0406050458004801018fe0021b001780301018004a6
  | 6, 2, 4 => 0x1006020403400c003180c040605155800038b8080c0a00300004061c82800466000100602238286ac000200c05160045580004010e4840a003000066c0708c140060001006020402800c002400c0c00251398000e01018140021b002280301018140060001006064380226c005e2cc0406050018011201018004a39b00006020344414006
  | 6, 2, 5 => 0x1004064680236c000215e3406050018000301018bc0a2ab00090030103c145560000c0c0a001cc9cc0002018720a0013980002030e4140025b000091201018004a60001192210302800c000200c580805001800040180a3200253000060e01018004a60000c1400261388cc000200c04060505580065018080c0a2ab00006020302801186
  | 6, 2, 6 => 0x100602030023ec00018080c0a004798000401028aa4c21b00090030102800b6600010ba020500098c000200c04066a105800032881814002330009003012d4140060000c0406050023ac003d80c04060515580003010183a0a003000060205000cc4c60000c1400259309cc002400c04068e00180004630098a0a2ab00008030110814006
  | 6, 2, 7 => 0xc5806050008cc00019440c0a0012d80004109740c8700300008c901018145560001006026f82800c003a00c040a001318000401818500a2ab000080234828004360001006021f02800c009080c040605001800bc018081400263000a60301018140060001006029002800c0001018004a3990d80003010181a002330000803011f814556
  | 6, 2, 8 => 0x12006023f80098c000200c040626c8d800030111c143b23300006020302801226001dcec020300094c000101814002192580004018181a00273000060203028223160000c04060680096c0001808f40a00131800046b8080c0a0030009002030e41400600010063c0303400c00021b0460a0010d800030320c1400273000080301154944c6
  | 6, 2, 9 => 0x10066c1180094c0001809980a001198000401018004a21b000080301028772b60000c0c0a0013904c009500c040a004a58000316018140025b000080394018004a60000c04063f80104c000207004060012980048018080d270030000803010188326600494060203000e6c00018080c0a004918000401808d200253000900305000984e6
  | 6, 2, 10 => 0x10480203028aac0002008b606068018000401808140096b000060203028012c6
  | 7, 0, 0 => 0x10425d01018140070001006fe01018140070001006020300094737000126003010181400700010066c03028004e700000900301018140060000cd80203028004b7000100602978181400700010060203028012e7001dc0802030280043700010ae0303028003170001006020302800fa700298080301018004a70001006212a01814007000100406268280043700494080301018004a7
  | 7, 0, 1 => 0x1006020302a4e0070001006020302800497000100602051fc004c700010060299818140070024408030101814557004c808030101814007001dc080301018004a70001006020302800d67000126203010181400700010060203134004a70000c040605000624670001004060521c0043700000b4030101814006000118c0203028004370001006020505c003b7000100602030290a007
  | 7, 0, 2 => 0x10ae8e010181400700120066c0101814007000100602030004c4a700010060203028aa4c70001006028781814007001dc08b3010181400700010065401018145570000c0406050009631700000ca03010181400600010ae0301028004c7000000803010189a4160001006020321c004a7000118c0301018004a7000100606050009d3470001004a503028004370001004061182800437
  | 7, 0, 3 => 0x100602034d8140070000008c6013141400600010060203028012b70001006023481814007001880803010181400700000060203178140060000090030103c1400600010060203028010a7000103803010181400700010060252818004a70000c040662828004670001006020308c004a70001006029a818140070000c044703028004670001006020302800117000111c030101814557
  | 7, 0, 4 => 0x11ea0301018140070000c044703028004b7002789003010181400700000080205000984360001006020302a0200700010060203028011570001006471e01814007000100602030282e55700010066c0308c14007000100602030292e0070001006020302800c3700010060203028005570001006020302882557000100602030281a0070000c040605000764670001166020302800267
  | 7, 0, 5 => 0x1270030101814007001140602031101400700000080301000944c60001004472d818140070000008c9010181400600010060605000764e7000000803030a0140060000c040605000963b700298080301028004c70012006020302800317000126e03010181400700010060662828004e700010064703028004e700010060205000984e70000c040662828004b700010060203028aa467
  | 7, 0, 6 => 0x118c0301028004c700010060203028aa847001200602033141400700120060223818140070001006020f0182e00700010060203028010770015c060203028004670000c040603828004b70000c053a03028004b7001dc080301028004c7001c008030101814007000100651010181400700010060226828004c70001166030101814007000100606050009d3970001006020302896557
  | 7, 0, 7 => 0x4f8080301018140070000008572b0181400600010ae0303028004e700010060203028012370015c060203028004b700010ea030101814007000100602050004c4c700120060203028003b7000100606051fc004e7000100602034f41400700010060203028013c700010062c010181400700010073b010181400700114080203028004370001006020521c004c70000008240101814006
  | 7, 0, 8 => 0x10062101018004a70001284030101814007000000840010181400600010060203028aa4a70001006020302a820070000c0406050009c4670024408030101814007000100740010181400700010066c0111c1400700010060203028013f7000000406050008646600114080301018004a7001200803010181455700010060252828004c7000104202030280043700010060211828004c7
  | 7, 0, 9 => 0x8b301018142660000c040605000964e700010060203028004c7000000806050009c4360001006022690814007001940803010181455700000040605000964360000006020300094466000100654010181400700120060203028fe007005100803010181400700000380203028004b60050c080301018140070001006020302800e0700010d82401018140070029806020302800467
  | 7, 0, 10 => 0x10060203028004170001006028b018140070000006020301c1400600000080303000944e600000060203000964a60001006020500098a170001150030101814557001dc0602030280046700298080303028004e700298060203028004b700010041e0302800437000111c03010181400700120ae0301018140070000c0406268280046700000080301018145560001006020302924007
  | 7, 0, 11 => 0xc0406050004c467001dc080303028004e7001dc060203028004b7000128a030101814007000100602040181400700010060203234004a7000100602031bc140070001006020f018004a700010060626828004e70000c040626828004b700010b20301028004c700010040622028004370000c04060521c00467002cce8030101814007000100602030282e0070031806020302800467
  | 7, 0, 12 => 0x29890030101814007000100602a401814007000100602a381814007000118c0303028004e700010062c030280041700010066c01018145570000c04060521c004b700010060203110004a70014c0803010181400700120060203028004e700318060203028004b700010060203028006e70000c04061182800467000009002030280043600010074601018140070001006020302932007
  | 7, 0, 13 => 0x100602031081400700010074d01018140070001298030101814007004a8080301028004c70000c040611828004b7003289003010181400700000900301018004a600010060223828003b7000100606050004c4e700010074b010181400700114080301028004c700528080301018140070000c040605000962670001006025501814557000100602035241400700010060203028aaa97
  | 7, 0, 14 => 0x1007520101814007001200602030290e0070001007510101814007001218c03010181400700010060203028aaa770001006020302800e27000000602050009846600010060203028625570000c04060500094737001dc90030101814007000100602030280100700010060203028015070001006020353c1400700010040605000874e700010062101028004c70012006020313414007
  | 7, 0, 15 => 0x1006020f028004c700010060203028004a700120060252818140070012006020308c1400700000080305000984e6004380803010181400700000060205000964c600010040605000aa4370001006a201028004c7001680803010181400700120060203028002670200c04060505c0031800000060203028007360001006f40101814007000000802030e4140060012008030101814007
  | 7, 1, 0 => 0x111c02030291a007000100602030481400700010060203028015470001006020300095157001940803010181400700010060203000aa4a700010067601018004a70000c04062697814007000100602030280033700010060203028015370001006022b018004a7000100602033141455700120060203028008270001006022381814557000100602030009443700010060205234004c7
  | 7, 1, 1 => 0x25890030101814007000000803010181a00600011500301018140070001166022b018140070001006020f0282e0070055c08030101814007000116602030280043700114060203028004670000006020320c14006000000803288181400600010ae031081814007000100602ab01814007000000803010181400600010060222028004c7000100606050009d5570001006020302876557
  | 7, 1, 2 => 0x1006020305c0041700010040605000873c700114080303028004e700011660301018004a70001006bd010181400700114060203028004b70000008031601814006000100602220282e00700560080301018140070000006020302800826000100606268a0140070000c420203028004670012008030103c140070001006020300094f3700000900301028004c600010060203028011b7
  | 7, 1, 3 => 0x10040605000873f70001006025501814007000000606050009c4660001006020302800a9700010040605000875c700010075b010181400700010ae030101814557000100602035681400700010066c010181400700010062103028004e700010075901018140070012006020b0181400700010060203000950770000c420203028004b70000008030111c143b600010060203028fe557
  | 7, 1, 4 => 0x10a80203028004370001006022b028004c700000060605000964e60001006020302801347000100602050009843700010060203028015d700114900301018140070027808030101814007000118c0203314140070001006020342c145570012006020303c140070000c040605234004670000c041e0302800467001dc0802033141400700244080203028004370000008030103c14006
  | 7, 1, 5 => 0x10060203028aa4e700010060605234004e700010061e03028004e7000111c02030280043700010060203028aafd700120062101018140070000c040605234004b70000c041e03028004b700000080203028aa43600010060205404004c700000085d010181400600010060205000aa4c700010067601028004c7000100406050009843700244080301018004a70000006020302800666
  | 7, 1, 6 => 0x1004060500086467000111c0301018004a70001006210308c1400700000080301018aa4a60001004060505c00437000100406050008243700010060622028004e700010075f010181400700010060203000944c700000e803010181400600010065401018004a70029808030101814557000017803010181400600011920301018140070001006020357814007000100621030290e007
  | 7, 1, 7 => 0x12006020f01814007000100602238181a007000100602032e814007000111cb301018140070001006020305c004a700010060203000824a70001006028b018004a7001dc0803010181455700000900303028004e60000c0406050008c497001dc0857010181400700000900301018fe0060001006022381814007000100602031341455700011660301028004c70000006023d01814006
  | 7, 1, 8 => 0x12006020311014007000100602030284c55700010ae02030280026700010060203029760070001006020302800be700000060e01018140060001006020302a1000700012c4030101814007000100602030290e5570058408030101814007000118c0301018145570001004060500096437000100602b001814007000100602030009446700010060203028003b7001200602030291a007
  | 7, 1, 9 => 0x10800301018140070000c040605000aa4670000c0406050008d677000100602b3018140070001006020301c140070001006029d018140070000c04560302800467000100602035941400700010060203000964a700010060252818145570001006020308c1455700010060203028016470000c040605000864670001006020335014007000100654030280031700012c6030101814007
  | 7, 1, 10 => 0x100602030280169700010065401028004c700010060605000aa4e700010067603028004e70000cd80e01018140070000c0406050009655700010ea02030280041700010ae03010181400700120080203028004370000c045603028004b7000100606050009c4370000c04060500096437005a00803010181400700070060203028004b70001006020302800cb700244080301028004c7
  | 7, 1, 11 => 0x803011a4140060001006020302800e7700000ee760101814006000000602030009473600010060205000992970001006f401018004a700120080301018004a70001006020342c14007000111c0301028004c7000100406050009443700000080301028aa4c6002cc0602030280046700010076a010181400700010060203028008a70001006020300094db70001006020302801267
  | 7, 1, 12 => 0x12006022b0181400700010060237828004c7000100602050009846700120060203028004370000008033608c1400600011660303028004e70000008020302800436002cc060203028004b70001006020505c004c700010060205000824c700000081c01018140060012006020302800117005ac08030101814007000100406268e41400700011b8030101814007001dd4c030101814007
  | 7, 1, 13 => 0x244060203028004670001006020402800417000008a03011101400600010060205000964c700012da030101814007003280803010181400700000080301018004a60001006020f11c1400700010060205000986e7000100602035b0140070000c04473d0181400700120060203028005570029808030101814007001200676010181400700000060203028004960049408030101814007
  | 7, 1, 14 => 0x118c0301018140070000ca8020302800467000100621010181455700121660301018140070000008032a01814316001940602030280055700010d80203028004370001006020302800a4700000c403010181400600000088e010191a006001dc0803010181400700010060223910140070000006020302800116001140803010181455700010060203134140070001006020313414417
  | 7, 1, 15 => 0x1006020302800ef700010065403028004e700120080301028004c70000ca80203028004b700012e20301018140070001006020302ae0007000100602035bc1400700010066c01018004a7005b808030101814007002380602030280046700000060203028aa46600244080303028004e70000c0406050009846700244060203028004b70001006020500099007000000803010782e006
  | 7, 2, 0 => 0x100602030291a5570001006020f0181455700000e003010181400600010060205000944c70000ca8a30101814007000111c0303028004e700000080303028aa4e600238060203028004b7000000602030289655600010060203028008270001004060500062437000000875010181400600010060605000984e70000c04060505c004670000c040605000824670000c040605000964c7
  | 7, 2, 1 => 0x1006020302800c1700000080301028004c6000100606050009c467000100602031101455700258080301018140070000c0406050008d73700010071a01018140070001006060505c004e700010060605000824e70000c04060505c004b700010060203000624a70000c04060500096417001212203010181400700012e403010181400700010060205000985870014c0602030282e007
  | 7, 2, 2 => 0x10060223818004a7000100602ba818140070001006020302801557000000803108190e00600010b203010181400700010040605000764370000c0406050008d50700010060605000964e70001006fe0101814557001211c03010181400700000900301018145560001006020302800b27000100602035d01400700120060203028004c700120065401018140070001004470302800437
  | 7, 2, 3 => 0x100606050009d7870001006020303c1400700010060203420004a700000ca03010181455600010066c01028004c700010060203000764a7000100602035dc1400700168060203028004170012006020302800467002f008030101814007001200602030282e007001200602030280041700010060223818143b7000000803010201400600012ec03010181400700010060203314004a7
  | 7, 2, 4 => 0x10066c010282e00700010060203028ab0a7000100602031340041700010077c010181400700120080303028004e700010077b010181400700120060203028004b7000100602035e814007004a808030101814007000100406051fc004370000c0406050009446700001220301018144b600010077901018140070001006020302800f270011408030101814007001dc0802030291a007
  | 7, 2, 5 => 0x10060605000944e7000100602031fc004a70000c040605000964a70001006760101814557000000602030280046600010060205000624c7000100406050008769700010060203028011370001006022b0181455700010060203028017e700012fa030101814007000000803011081400600010060203028aa43700010ae0203028004370000c0406050008d5370001006210101814007
  | 7, 2, 6 => 0x10060223828004c70000006a301018140060001006020f0181400700120062f01018140070001166030101814557001dc06020311014007000100406050009c437000100602030280180700000080303028004e600000060203028004b60001006a20101814007000100606050009d547000100602bf818140070000008031e0181400600000a603010181400600010ae0301018004a7
  | 7, 2, 7 => 0x111c02033141400700010060203000944e7000100602030280079700010060205000764c7000100602030280035700000080203000944360000d7a0203028004b7000014c03528181400600120060203028004a70001006020302a380070000cd802030280046700011b80301018004a70000008022d818140060043890030101814007002980802030280043700010060262828004c7
  | 7, 2, 8 => 0x1302030101814007
  | 8, 0, 0 => 0x2401006020302800e04018080c0a0012dc08030101814002338100602030282e0070200c04060500082e044700c040605001c0004018080c0a2ab010060203028004c70200ca8020302800e910200c040605001c08b3018080c0a003810060203028005570200cec020302800e0401808ac0605001c080301018140021b80090030101814006
  | 8, 0, 1 => 0x231806020302800e770200c040605001c0803010189a0a003800080301018004a65301006020302800e04018080c0a00139c000401018140021b010ae0301018140070200c0406051fc00e04018080c0a000edc0803010198a0a003810060223818140070200c04060500062e04019b0040605001c0004018080c0a003010060203028004a7
  | 8, 0, 2 => 0x10060203110140070200c04060523400e04018083c0605001c0004018181400273000060203028004b60000c0406050008cc0401884040605001c8a04018080c0a003800080301028004c60200c04a50302800e04018080c2305001c08030101814001338100602030290e007
  | 9, 0, 0 => 0x8030101814006
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 49
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
  | 0, 0 => 0xc7cdde60c0c720000000000000000000000000000000000000000000000000031831e18f0f07c000000000000000000000000000000000000000000000000000c6322e60cf38d000000000000000000000000000000000000000000000000003fffffe0000000000000000000000000000000000000000000000000000000003ffc001fff0000000000000000000000000000000000000000000000000000003e03e01f00ff8000000000000000000000000000000000000000000000000000021c3ce10303f100000000000000000000000000000000000000000000000000001c00e0e3e38d
  | 0, 1 => 0x31831e00000070000000000000000000000000000000000000000000000000003f83fe000000000000000000000000000000000000000000000000000000000000001c000000700000000000000000000000000000000000000000000000000031831e00000070000000000000000000000000000000000000000000000000003e001fff00007f000000000000000000000000000000000000000000000000000c60dd060c0c7200000000000000000000000000000000000000000000000000319f1ef81313f10000000000000000000000000000000000000000000000000031831e18f0f07c
  | 0, 2 => 0x1c00000070000000000000000000000000000000000000000000000000003e03e006000c0000000000000000000000000000000000000000000000000000001c00e000e380000000000000000000000000000000000000000000000000000d9cc2e6f30c0d00000000000000000000000000000000000000000000000000001c00e0e30000000000000000000000000000000000000000000000000000000c60dd060ceff200000000000000000000000000000000000000000000000000001c00e0000000000000000000000000000000000000000000000000000000003e03e01f000c00
  | 0, 3 => 0x1fff00e31c72000000000000000000000000000000000000000000000000003de3df1efcfc7e00000000000000000000000000000000000000000000000000001c1ce0000070000000000000000000000000000000000000000000000000003ffc00ffff0000000000000000000000000000000000000000000000000000000e60e107ecec0e000000000000000000000000000000000000000000000000003ffc0006ef00000000000000000000000000000000000000000000000000000031831e070f0f83000000000000000000000000000000000000000000000000003fe3ff060c0c72
  | 0, 4 => 0x3ffc00e60c000000000000000000000000000000000000000000000000000000001c0000e30000000000000000000000000000000000000000000000000000003e03e00600ef80000000000000000000000000000000000000000000000000003f80001ff00000000000000000000000000000000000000000000000000000003003001800f000000000000000000000000000000000000000000000000000003ffc000000ffff000000000000000000000000000000000000000000000000003e63fd1f0cfff2000000000000000000000000000000000000000000000000000c1cc0e6000c00
  | 0, 5 => 0x3ffc00060c000000000000000000000000000000000000000000000000000000307f01f80ff003000000000000000000000000000000000000000000000000003180e1f8f00f83000000000000000000000000000000000000000000000000003e03e01f00ff80000000000000000000000000000000000000000000000000003fffe01fff0c0000000000000000000000000000000000000000000000000000001c00ff1c1c72000000000000000000000000000000000000000000000000003e7c00ff0c0000000000000000000000000000000000000000000000000000000c00c00600ef80
  | 0, 6 => 0x1e01f001ce3f2000000000000000000000000000000000000000000000000003de3c31efcfc0e0000000000000000000000000000000000000000000000000000000000e0e38c000000000000000000000000000000000000000000000000003e03e000ff007f000000000000000000000000000000000000000000000000000000000000e380000000000000000000000000000000000000000000000000003e1fe0e6000c00000000000000000000000000000000000000000000000000000000000000e3800000000000000000000000000000000000000000000000000033832219101000
  | 0, 7 => 0xc60dd19f3f38d0000000000000000000000000000000000000000000000000000001c0000007000000000000000000000000000000000000000000000000000001c00e0000000000000000000000000000000000000000000000000000000003003001800f3800000000000000000000000000000000000000000000000000000000000e0e00c000000000000000000000000000000000000000000000000000c7cdde6efefff000000000000000000000000000000000000000000000000000c7c0006ef0000000000000000000000000000000000000000000000000000003ffc00ffff0000
  | 0, 8 => 0x319f1ef8f3f3fd000000000000000000000000000000000000000000000000000000001fffffff000000000000000000000000000000000000000000000000003ffffff8f0f07c0000000000000000000000000000000000000000000000000031831e00000000000000000000000000000000000000000000000000000000000003ffe000ffff0000000000000000000000000000000000000000000000000000001c00e0e07c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffe01fff0000
  | 0, 9 => 0xe60fd070c0c720000000000000000000000000000000000000000000000000001fc1fe0ff007f000000000000000000000000000000000000000000000000000c7cdde6efefff000000000000000000000000000000000000000000000000000e7ce1e70f0f8300000000000000000000000000000000000000000000000000001c00e000000000000000000000000000000000000000000000000000000000339f22f9f3f38d0000000000000000000000000000000000000000000000000000000000e3e38d000000000000000000000000000000000000000000000000003fffffe60c0c72
  | 0, 10 => 0x3fffe01fffff80000000000000000000000000000000000000000000000000003e00001f000000000000000000000000000000000000000000000000000000003fe3ff1f1c1c72000000000000000000000000000000000000000000000000003e1fe0ffe3ff8d000000000000000000000000000000000000000000000000003fffffe00000700000000000000000000000000000000000000000000000000000000000e0e38c000000000000000000000000000000000000000000000000003e63e01f0cff80000000000000000000000000000000000000000000000000000003fd0000fff2
  | 0, 11 => 0x3ffce1ffff0000000000000000000000000000000000000000000000000000000c7cdde0000000000000000000000000000000000000000000000000000000003e60001f0c0000000000000000000000000000000000000000000000000000000c60c0060c0c0000000000000000000000000000000000000000000000000000319c0018f30000000000000000000000000000000000000000000000000000003fffffe0000000000000000000000000000000000000000000000000000000003ffce1ffff0f83000000000000000000000000000000000000000000000000000e7c00070f0000
  | 0, 12 => 0x31830018f0f00c000000000000000000000000000000000000000000000000003fe3ff1fffffff000000000000000000000000000000000000000000000000003fffffff1c1c72000000000000000000000000000000000000000000000000003ffc02ffff000d000000000000000000000000000000000000000000000000003fffffe60c0c72000000000000000000000000000000000000000000000000003fffffe60c00000000000000000000000000000000000000000000000000000031831e1800f070000000000000000000000000000000000000000000000000003ffc01ffff0003
  | 0, 13 => 0xe7cfde70f0ff3000000000000000000000000000000000000000000000000000c60c1060c0c02000000000000000000000000000000000000000000000000003fffffe6000c70000000000000000000000000000000000000000000000000003f83fe1ff0fffc0000000000000000000000000000000000000000000000000031831e00e0e07c000000000000000000000000000000000000000000000000003dffdfe60c0c720000000000000000000000000000000000000000000000000031831e18f0f3fc0000000000000000000000000000000000000000000000000031831e00000000
  | 0, 14 => 0x3fffffffff0000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003ffc001fff0000000000000000000000000000000000000000000000000000003ffc00e000000000000000000000000000000000000000000000000000000000339f22e0000000000000000000000000000000000000000000000000000000003fffe3ff1f1f83000000000000000000000000000000000000000000000000003fffe01fff1c00000000000000000000000000000000000000000000000000003fffffe6000c00
  | 0, 15 => 0xc60dd000000000000000000000000000000000000000000000000000000000031831e18101070000000000000000000000000000000000000000000000000000003ff0000ffff000000000000000000000000000000000000000000000000003e7ffde60c0c72000000000000000000000000000000000000000000000000003ffffff810107000000000000000000000000000000000000000000000000000319f1ee0000000000000000000000000000000000000000000000000000000000003ff00001c72000000000000000000000000000000000000000000000000003fffffff0c0c72
  | 1, 0 => 0xc00c006000c00000000000000000000000000000000000000000000000000003ffffff9101000000000000000000000000000000000000000000000000000000c60c0060c0c00000000000000000000000000000000000000000000000000003fe3ff00000000000000000000000000000000000000000000000000000000000c60dd1fffffff0000000000000000000000000000000000000000000000000000000019f3f38d000000000000000000000000000000000000000000000000003fffffe00000000000000000000000000000000000000000000000000000000000000018f3f3fd
  | 1, 1 => 0xc00dc06000c70000000000000000000000000000000000000000000000000003ffcdd1fff0c72000000000000000000000000000000000000000000000000000c6000060c00000000000000000000000000000000000000000000000000000031831e18f0f000000000000000000000000000000000000000000000000000003fe3e01f1cff80000000000000000000000000000000000000000000000000003fffe3ffffff8f000000000000000000000000000000000000000000000000003e63e11f0cff82000000000000000000000000000000000000000000000000003fffffe0000c72
  | 1, 2 => 0xc00c006000c00000000000000000000000000000000000000000000000000003fffffff0cfff2000000000000000000000000000000000000000000000000003e63e01f0cff80000000000000000000000000000000000000000000000000003fffffe60c0070000000000000000000000000000000000000000000000000003ffcc01fff0c00000000000000000000000000000000000000000000000000000c60dd06000c00000000000000000000000000000000000000000000000000003fffffe0e3e38d000000000000000000000000000000000000000000000000000e7ce1e60c0c02
  | 1, 3 => 0x1c00e0000000000000000000000000000000000000000000000000000000003fffffffff0c72000000000000000000000000000000000000000000000000003fffffe00c0072000000000000000000000000000000000000000000000000000000001fffff8f000000000000000000000000000000000000000000000000000e7ce1e000000000000000000000000000000000000000000000000000000000319f02f8f3f38d000000000000000000000000000000000000000000000000000c60dd060c0000000000000000000000000000000000000000000000000000003ffcc11fff0c02
  | 1, 4 => 0x3fe0001f1c0000000000000000000000000000000000000000000000000000003fffffff00ff80000000000000000000000000000000000000000000000000003e03e0000000000000000000000000000000000000000000000000000000000001e01f001c0072000000000000000000000000000000000000000000000000003e1fe0e0000000000000000000000000000000000000000000000000000000003e7fe1ff0fff83000000000000000000000000000000000000000000000000000e00e007000f80000000000000000000000000000000000000000000000000003fffffe01c0072
  | 1, 5 => 0x19fff3ff000000000000000000000000000000000000000000000000000e7ce1e70f0c030000000000000000000000000000000000000000000000000000001c0000e3f0000000000000000000000000000000000000000000000000000000dde000efff000000000000000000000000000000000000000000000000003fffffe6000c00000000000000000000000000000000000000000000000000003fe3ff1ffcfc7e0000000000000000000000000000000000000000000000000031831e18101070000000000000000000000000000000000000000000000000003fffff1fff1c72
  | 1, 6 => 0xe7ce1e70f0f83000000000000000000000000000000000000000000000000000e7ce1ffffff8f0000000000000000000000000000000000000000000000000031831e19f3f3fd000000000000000000000000000000000000000000000000000c7c00e60c0000000000000000000000000000000000000000000000000000003ffc00ffffe38d00000000000000000000000000000000000000000000000000001c0000e30000000000000000000000000000000000000000000000000000003ffcdde60c0c720000000000000000000000000000000000000000000000000030031c18e0f07c
  | 1, 7 => 0x31ee000f3fd00000000000000000000000000000000000000000000000000021c20e1030381000000000000000000000000000000000000000000000000003e1fe0ff00ff80000000000000000000000000000000000000000000000000003fffffff000000000000000000000000000000000000000000000000000000000c6000060c0000000000000000000000000000000000000000000000000000000c60dd06ecec7e00000000000000000000000000000000000000000000000000339f22e00000000000000000000000000000000000000000000000000000000000033fe000f3ff
  | 1, 8 => 0x3fff221fff1000000000000000000000000000000000000000000000000000003fff1e1ffff07c0000000000000000000000000000000000000000000000000031800018f00000000000000000000000000000000000000000000000000000003fffffe00000700000000000000000000000000000000000000000000000000000000000ff007f00000000000000000000000000000000000000000000000000001c00e00000000000000000000000000000000000000000000000000000000000001fe000007f00000000000000000000000000000000000000000000000000339f3ee0000000
  | 1, 9 => 0x3f83e21f10ff800000000000000000000000000000000000000000000000000000000000e3e38d00000000000000000000000000000000000000000000000000001c00e00000000000000000000000000000000000000000000000000000000031831e18f3f3fd00000000000000000000000000000000000000000000000000000000070f0f83000000000000000000000000000000000000000000000000003ffffffefcfc7e000000000000000000000000000000000000000000000000003ffcc01fff0c00000000000000000000000000000000000000000000000000003fffffe60c0c02
  | 1, 10 => 0x3ffc00ffff000d00000000000000000000000000000000000000000000000000001c00e0e30000000000000000000000000000000000000000000000000000003fe0001f1c000000000000000000000000000000000000000000000000000000001c1ce0e3e3fd000000000000000000000000000000000000000000000000003fffffff1c0000000000000000000000000000000000000000000000000000003fffffff1c1c720000000000000000000000000000000000000000000000000031831e18f0f07c000000000000000000000000000000000000000000000000003fffffe70f0000
  | 1, 11 => 0x31831e18f000700000000000000000000000000000000000000000000000000031831e18f0f3fc00000000000000000000000000000000000000000000000000319f1ee0000070000000000000000000000000000000000000000000000000003fff22fffff38d00000000000000000000000000000000000000000000000000339c0019f30000000000000000000000000000000000000000000000000000003e63e11f0cff82000000000000000000000000000000000000000000000000003fffffe00f0003000000000000000000000000000000000000000000000000000003fe0000fffc
  | 1, 12 => 0xffff000000000000000000000000000000000000000000000000000000001fffffff000000000000000000000000000000000000000000000000003e1c00ff00000000000000000000000000000000000000000000000000000000001fffe000ffff000000000000000000000000000000000000000000000000000e7ce1e70f0f8300000000000000000000000000000000000000000000000000007c01e00f000300000000000000000000000000000000000000000000000000339c0019f30000000000000000000000000000000000000000000000000000000000e1e0000f83
  | 1, 13 => 0x3fffffff1f1ff3000000000000000000000000000000000000000000000000003fff22e00000000000000000000000000000000000000000000000000000000031801c18f0e07c0000000000000000000000000000000000000000000000000001fc1fe0ff007f000000000000000000000000000000000000000000000000003ffc001f0c0000000000000000000000000000000000000000000000000000003e03e01f00ff80000000000000000000000000000000000000000000000000003fffffe0001c7200000000000000000000000000000000000000000000000000019c1ee0f3007d
  | 1, 14 => 0x3fe3ff1fffffff000000000000000000000000000000000000000000000000003ffc001fff0000000000000000000000000000000000000000000000000000003fffe01f00ff80000000000000000000000000000000000000000000000000003f9fe2fff3ff8d000000000000000000000000000000000000000000000000003203201900f3800000000000000000000000000000000000000000000000000000000000e0e00c00000000000000000000000000000000000000000000000000007c1de0ef007f000000000000000000000000000000000000000000000000000000001fffe38d
  | 1, 15 => 0x1c00e0000000000000000000000000000000000000000000000000000000003fe3ff1f1cfff2000000000000000000000000000000000000000000000000003e03e01f001c00000000000000000000000000000000000000000000000000003fffffff001c00000000000000000000000000000000000000000000000000000c60dd00000070000000000000000000000000000000000000000000000000000000001f1c1c7200000000000000000000000000000000000000000000000000019c1fe0f3007f0000000000000000000000000000000000000000000000000000001fe000ffff
  | 2, 0 => 0x1c00e0e3e38d000000000000000000000000000000000000000000000000003ffce11fff0c020000000000000000000000000000000000000000000000000000000000e3e38d000000000000000000000000000000000000000000000000000003ffe000ffff0000000000000000000000000000000000000000000000000031800018f00000000000000000000000000000000000000000000000000000003fffffe70c0c02000000000000000000000000000000000000000000000000000e7ce1e7efef8f00000000000000000000000000000000000000000000000000001c00e0030381
  | 2, 1 => 0x3de3df060c0c72000000000000000000000000000000000000000000000000003fffffe6efefff000000000000000000000000000000000000000000000000000c601c060c00700000000000000000000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000000000003fe3ff1f1c1c72000000000000000000000000000000000000000000000000000c60dd060c0c72000000000000000000000000000000000000000000000000003f9fe2e000000000000000000000000000000000000000000000000000000000339f22f9f3f38d
  | 2, 2 => 0x3f83fe06000c7000000000000000000000000000000000000000000000000000339f3ef9f3f3fd0000000000000000000000000000000000000000000000000031830218f0f00c000000000000000000000000000000000000000000000000003fffffe60c000000000000000000000000000000000000000000000000000000019c02e0f3000d000000000000000000000000000000000000000000000000003fff22ffff0000000000000000000000000000000000000000000000000000000c60dd06efefff000000000000000000000000000000000000000000000000000e7ce1e70fef83
  | 2, 3 => 0x3fffe3ffffff8f0000000000000000000000000000000000000000000000000033832219f3f38d0000000000000000000000000000000000000000000000000000000019f3ffff000000000000000000000000000000000000000000000000000c60dd0000000000000000000000000000000000000000000000000000000000000322e000f38d000000000000000000000000000000000000000000000000003e60dd1f0c0c720000000000000000000000000000000000000000000000000033833e19f0f3fc00000000000000000000000000000000000000000000000000001c00e0000000
  | 2, 4 => 0xc60dd000000700000000000000000000000000000000000000000000000000033832219101000000000000000000000000000000000000000000000000000003ffffff9f3f38d000000000000000000000000000000000000000000000000000000001fe3ff8d000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000000000001ff0fffc000000000000000000000000000000000000000000000000003fffffe60c0c000000000000000000000000000000000000000000000000000033833e19f0f07c
  | 2, 5 => 0x301f00f8e3f38d00000000000000000000000000000000000000000000000000001c0000e3e380000000000000000000000000000000000000000000000000000c7cc1e60f0f830000000000000000000000000000000000000000000000000000000006efefff000000000000000000000000000000000000000000000000000e60e1070c0c02000000000000000000000000000000000000000000000000003fffffe70f0f83000000000000000000000000000000000000000000000000000e7ce1e0000000000000000000000000000000000000000000000000000000003203201900f380
  | 2, 6 => 0x3fff1efffff3fd0000000000000000000000000000000000000000000000000030031c1800f070000000000000000000000000000000000000000000000000003dffdffeffffff0000000000000000000000000000000000000000000000000000601d000c007200000000000000000000000000000000000000000000000000319f1ee0e3e38d000000000000000000000000000000000000000000000000003ffffff8f3f3fd000000000000000000000000000000000000000000000000003fff1e18f0f07c000000000000000000000000000000000000000000000000003fff001ffff000
  | 2, 7 => 0xe000e38d000000000000000000000000000000000000000000000000003ffffff8f00000000000000000000000000000000000000000000000000000000c1cc0e6e3ef8d000000000000000000000000000000000000000000000000000000dd00000c72000000000000000000000000000000000000000000000000003e63fd060c0c7200000000000000000000000000000000000000000000000000319f1ef8f0f07c0000000000000000000000000000000000000000000000000001fc1fe0000000000000000000000000000000000000000000000000000000003ffc1c1fff0070
  | 2, 8 => 0x319c00f8f3e38d000000000000000000000000000000000000000000000000003e63fd1f00ff80000000000000000000000000000000000000000000000000003ffc001fffe00c000000000000000000000000000000000000000000000000003fffffe0e30000000000000000000000000000000000000000000000000000003fffffffffff80000000000000000000000000000000000000000000000000003ffc001fffe380000000000000000000000000000000000000000000000000000c00dc06000c70000000000000000000000000000000000000000000000000003e1fe0e0e3e38d
  | 2, 9 => 0x31830018f0f000000000000000000000000000000000000000000000000000000003ffe0000000000000000000000000000000000000000000000000000000003e1c00ffe3e38d000000000000000000000000000000000000000000000000003fffe0ffffff8d000000000000000000000000000000000000000000000000003e7ffdffefffff000000000000000000000000000000000000000000000000003fffffe0e0e00c000000000000000000000000000000000000000000000000000c7cdde0e3e38d000000000000000000000000000000000000000000000000003de0dd1efc0c72
  | 2, 10 => 0x3fffffffffe38d000000000000000000000000000000000000000000000000003de3df18f0f07c0000000000000000000000000000000000000000000000000001801e00f0007c00000000000000000000000000000000000000000000000000001c00e0e3000d0000000000000000000000000000000000000000000000000000000018f0f07c000000000000000000000000000000000000000000000000003f83e01ff0ff80000000000000000000000000000000000000000000000000003f9ffefff3fffd00000000000000000000000000000000000000000000000000000000060c0c72
  | 2, 11 => 0x3f83fe1f00ff800000000000000000000000000000000000000000000000000031831e00e0e00c00000000000000000000000000000000000000000000000000001c0000e3e00c000000000000000000000000000000000000000000000000000003e00000ff80000000000000000000000000000000000000000000000000003f83fe18f0f07c0000000000000000000000000000000000000000000000000031800018f0e00c000000000000000000000000000000000000000000000000003e03e01fe0ff8c000000000000000000000000000000000000000000000000003ffffff800f000
  | 2, 12 => 0x1fff0000000000000000000000000000000000000000000000000000003c63dd1e0cfc720000000000000000000000000000000000000000000000000031831e1800f00000000000000000000000000000000000000000000000000000001c00e000e380000000000000000000000000000000000000000000000000003ffcdd1fff0000000000000000000000000000000000000000000000000000003ffc00e0e3e38d000000000000000000000000000000000000000000000000003ffffffff0fffc000000000000000000000000000000000000000000000000003d83de1ef0fc7c
  | 2, 13 => 0x30030018e0f00c000000000000000000000000000000000000000000000000003ffffffffff07c000000000000000000000000000000000000000000000000003ffffe1ffffffc000000000000000000000000000000000000000000000000000c7c00e6efe38d000000000000000000000000000000000000000000000000003fffffffe3ff8d000000000000000000000000000000000000000000000000003fe3ff1ffcfffe0000000000000000000000000000000000000000000000000000031e0000f07c000000000000000000000000000000000000000000000000003fffffe000e380
  | 2, 14 => 0x31801c18f00070000000000000000000000000000000000000000000000000003fff1e1fff000000000000000000000000000000000000000000000000000000319f1e18f3f07c0000000000000000000000000000000000000000000000000031831e18f00000000000000000000000000000000000000000000000000000000000001f00ff80000000000000000000000000000000000000000000000000003fffdf1ffffc7e000000000000000000000000000000000000000000000000003ffcddffffefff000000000000000000000000000000000000000000000000000c601c060c0070
  | 2, 15 => 0x3de31e1efcf07c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffd1ffffff2000000000000000000000000000000000000000000000000003f831e1ff0f07c000000000000000000000000000000000000000000000000003e1fe01fe3ff80000000000000000000000000000000000000000000000000000c7cdd06ef0c72000000000000000000000000000000000000000000000000003e03fc1f00fff00000000000000000000000000000000000000000000000000001fc0000ff0000
  | 3, 0 => 0x3ffcdd060c0c7200000000000000000000000000000000000000000000000000001c00e0e0e00c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ffffff6bdbeff0000000000000000000000000000000000000000000000000039cb9e5cf8f87c000000000000000000000000000000000000000000000000002d6532d63d8248000000000000000000000000000000000000000000000000003fffffe0808208000000000000000000000000000000000000000000000000003ffc101fff4140000000000000000000000000000000000000000000000000003e13e89f42ffa0000000000000000000000000000000000000000000000000002b52bc953a3b740000000000000000000000000000000000000000000000000016bd67ebe7e79f
  | 0, 1 => 0x39cb9e54b8b87c000000000000000000000000000000000000000000000000003fdbfec0808208000000000000000000000000000000000000000000000000002d66dd363d3cf7000000000000000000000000000000000000000000000000003fdbfed6b8befc000000000000000000000000000000000000000000000000003e10077f42411f000000000000000000000000000000000000000000000000002d66dd363d3cf7000000000000000000000000000000000000000000000000002f76f9b71f1fe3000000000000000000000000000000000000000000000000003defdf7efdfcff
  | 0, 2 => 0x29429c14383874000000000000000000000000000000000000000000000000003e13e89600bea00000000000000000000000000000000000000000000000000016bd67ebe7e79f000000000000000000000000000000000000000000000000002c8aca56803ca80000000000000000000000000000000000000000000000000016bd67ebe7e79f000000000000000000000000000000000000000000000000003f77fdbf7ffff70000000000000000000000000000000000000000000000000016bd67e2a5a69f000000000000000000000000000000000000000000000000003e13e89f42ffa0
  | 0, 3 => 0x16be880be75920000000000000000000000000000000000000000000000000003defdf7efdfcff000000000000000000000000000000000000000000000000003ffffff4b8ba7c000000000000000000000000000000000000000000000000003ffd77ffffc3480000000000000000000000000000000000000000000000000010890648e0e01c000000000000000000000000000000000000000000000000003ffc101fff41400000000000000000000000000000000000000000000000000039cb9e4387858b000000000000000000000000000000000000000000000000003ffffff6bdbeff
  | 0, 4 => 0x3ffd77f6bda6df0000000000000000000000000000000000000000000000000016bc000be74100000000000000000000000000000000000000000000000000003e13e89f42ffa0000000000000000000000000000000000000000000000000003fd8101ffa4140000000000000000000000000000000000000000000000000003803881c40f820000000000000000000000000000000000000000000000000003ffc1000803cb7000000000000000000000000000000000000000000000000003f77fdbf7ffff7000000000000000000000000000000000000000000000000003ebfeff680bea8
  | 0, 5 => 0x3ffc1016bd0040000000000000000000000000000000000000000000000000003827893c45f8230000000000000000000000000000000000000000000000000039c871bcf846c3000000000000000000000000000000000000000000000000003e37edbf67ffb7000000000000000000000000000000000000000000000000003ffff89fffffe00000000000000000000000000000000000000000000000000016bd67f4989a68000000000000000000000000000000000000000000000000003ffd77ffffc348000000000000000000000000000000000000000000000000003e13e89f42ffa0
  | 0, 6 => 0x1751708b5ae7c00000000000000000000000000000000000000000000000000014ad436ac5c48b00000000000000000000000000000000000000000000000000169966cbe2e79c000000000000000000000000000000000000000000000000003e13e8803d825700000000000000000000000000000000000000000000000000163565ab67e797000000000000000000000000000000000000000000000000003ebfeff6a5bebf000000000000000000000000000000000000000000000000001611608b42e7800000000000000000000000000000000000000000000000000004244522252497
  | 0, 7 => 0x2d66dd294241000000000000000000000000000000000000000000000000000039cb9e54b8b87c0000000000000000000000000000000000000000000000000016bd67ebe7e79f000000000000000000000000000000000000000000000000003e13e89f42ffa00000000000000000000000000000000000000000000000000010890648e0e01c000000000000000000000000000000000000000000000000003bdbbadddadb68000000000000000000000000000000000000000000000000003ffc101fff4140000000000000000000000000000000000000000000000000003ffd77ffffe7df
  | 0, 8 => 0x3fffffffffffff000000000000000000000000000000000000000000000000000000001f7f7df7000000000000000000000000000000000000000000000000003ffffffcf8fa7c0000000000000000000000000000000000000000000000000039cb9e40808008000000000000000000000000000000000000000000000000000003efe000bebf0000000000000000000000000000000000000000000000000039cb9e5cf8f87c0000000000000000000000000000000000000000000000000004244522252497000000000000000000000000000000000000000000000000003ffff89fffc340
  | 0, 9 => 0x2d66dd363d3cf70000000000000000000000000000000000000000000000000001ec1760bd005f000000000000000000000000000000000000000000000000003fffffffffffff00000000000000000000000000000000000000000000000000063461a30707830000000000000000000000000000000000000000000000000016bd67e080820800000000000000000000000000000000000000000000000000129922c9c2c308000000000000000000000000000000000000000000000000000000000b676597000000000000000000000000000000000000000000000000003ffffff6bdbeff
  | 0, 10 => 0x3ffff89fffffe0000000000000000000000000000000000000000000000000003e10001f4241000000000000000000000000000000000000000000000000000029429814181860000000000000000000000000000000000000000000000000003ebfefffe7ffbf000000000000000000000000000000000000000000000000003ffffff4b8ba7c0000000000000000000000000000000000000000000000000016bd67ebe7e79f000000000000000000000000000000000000000000000000003f77f89f7fffe0000000000000000000000000000000000000000000000000000003eda000beb7
  | 0, 11 => 0x3ffc71bfff4340000000000000000000000000000000000000000000000000003fffffe0808208000000000000000000000000000000000000000000000000003f74101f7f4140000000000000000000000000000000000000000000000000002d66dd363d3cf7000000000000000000000000000000000000000000000000003ffc101fff4140000000000000000000000000000000000000000000000000003fffffe2a5a69f000000000000000000000000000000000000000000000000003ffc71bfff47c30000000000000000000000000000000000000000000000000006340003070100
  | 0, 12 => 0x39cb9e5cf8f87c000000000000000000000000000000000000000000000000002942981f7f7df7000000000000000000000000000000000000000000000000003ffffff4989a68000000000000000000000000000000000000000000000000003ffc125fff4148000000000000000000000000000000000000000000000000003ffffff4989a68000000000000000000000000000000000000000000000000003ffffff6bd82480000000000000000000000000000000000000000000000000039cb9e5cf8f87c000000000000000000000000000000000000000000000000003ffc113fff4143
  | 0, 13 => 0x2f76fdb73f3ff70000000000000000000000000000000000000000000000000004244122050483000000000000000000000000000000000000000000000000003ffffff6b8befc000000000000000000000000000000000000000000000000003fdbfedffafffc0000000000000000000000000000000000000000000000000039cb9e5cf8f87c000000000000000000000000000000000000000000000000003ffffff6bdbeff000000000000000000000000000000000000000000000000003fdbfedffafffc000000000000000000000000000000000000000000000000003fdbfec0808208
  | 0, 14 => 0x3fffffffffc348000000000000000000000000000000000000000000000000003ffc1000800000000000000000000000000000000000000000000000000000003ffc553fff65d7000000000000000000000000000000000000000000000000003ffd77e080820800000000000000000000000000000000000000000000000000129922c080820800000000000000000000000000000000000000000000000000063461a3070783000000000000000000000000000000000000000000000000003ffe981fff5960000000000000000000000000000000000000000000000000003ffffff680bea8
  | 0, 15 => 0x2d66dd200000000000000000000000000000000000000000000000000000000039cb9e549898680000000000000000000000000000000000000000000000000000028800003cb7000000000000000000000000000000000000000000000000003ffffff6bdbeff000000000000000000000000000000000000000000000000003ffffff4989a68000000000000000000000000000000000000000000000000003fffffe08082080000000000000000000000000000000000000000000000000000028800001820000000000000000000000000000000000000000000000000003fffffffffffff
  | 1, 0 => 0x2c02c816003ca0000000000000000000000000000000000000000000000000003fffffe0808208000000000000000000000000000000000000000000000000002d66d8163d3ce00000000000000000000000000000000000000000000000000029429800000000000000000000000000000000000000000000000000000000002d66dd3f7f7df70000000000000000000000000000000000000000000000000000000009424100000000000000000000000000000000000000000000000000003fffffe0a0a21c000000000000000000000000000000000000000000000000000000001f7f7df7
  | 1, 1 => 0x2d66dd363d3cf7000000000000000000000000000000000000000000000000003ffedd3fff7df7000000000000000000000000000000000000000000000000002d6410163d00400000000000000000000000000000000000000000000000000039cb9e5cf8f868000000000000000000000000000000000000000000000000003f53f89f5affe00000000000000000000000000000000000000000000000000016bd63ebc7c78b000000000000000000000000000000000000000000000000003e37e9bf47ffa3000000000000000000000000000000000000000000000000003fffffe080bebf
  | 1, 2 => 0x2c26cd36253cb7000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003f77fdbf7ffff7000000000000000000000000000000000000000000000000003ffffff6bdba7c000000000000000000000000000000000000000000000000003ffedd3fff7df7000000000000000000000000000000000000000000000000002d66dd36003ca0000000000000000000000000000000000000000000000000003fffffebe7e79f00000000000000000000000000000000000000000000000000063461a2050683
  | 1, 3 => 0x16bd67ebc2c308000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003fffffe0bd825f000000000000000000000000000000000000000000000000000000000b4745830000000000000000000000000000000000000000000000000016bd67e080820800000000000000000000000000000000000000000000000000129922c9c2c308000000000000000000000000000000000000000000000000002d66dd363d0040000000000000000000000000000000000000000000000000003ffc513fff45c3
  | 1, 4 => 0x29401014180040000000000000000000000000000000000000000000000000003fffffffc2ffa8000000000000000000000000000000000000000000000000003e13e8800082000000000000000000000000000000000000000000000000000001401000180040000000000000000000000000000000000000000000000000003ebfefe0808208000000000000000000000000000000000000000000000000003e37e9bf47ffa30000000000000000000000000000000000000000000000000006106083020780000000000000000000000000000000000000000000000000003fffffe0988248
  | 1, 5 => 0x97f41570000000000000000000000000000000000000000000000000000240120050003000000000000000000000000000000000000000000000000003f53fc9f7afff4000000000000000000000000000000000000000000000000000003efe000bebf000000000000000000000000000000000000000000000000003ffffff6a5bebf0000000000000000000000000000000000000000000000000039cb9e5cf8f87c0000000000000000000000000000000000000000000000000029429814181860000000000000000000000000000000000000000000000000003ffe981fff5960
  | 1, 6 => 0x63465a327279700000000000000000000000000000000000000000000000000063461ab4747830000000000000000000000000000000000000000000000000039cb9e5dfaf97c000000000000000000000000000000000000000000000000003ffd77f6bd8248000000000000000000000000000000000000000000000000003ffd77ffffe7df0000000000000000000000000000000000000000000000000016bc452be76597000000000000000000000000000000000000000000000000003ffffff6bdbeff0000000000000000000000000000000000000000000000000039cb9e5cf8f87c
  | 1, 7 => 0x3efe000bebf0000000000000000000000000000000000000000000000000002102081020300000000000000000000000000000000000000000000000000003ebfefffc2ffa8000000000000000000000000000000000000000000000000003fffffffc2c308000000000000000000000000000000000000000000000000002d6455363d24d7000000000000000000000000000000000000000000000000003defdf7efdfcff0000000000000000000000000000000000000000000000000016bd67e080820800000000000000000000000000000000000000000000000000000127e000821f
  | 1, 8 => 0x3ffc101fff4140000000000000000000000000000000000000000000000000003fff9e5ffff97c0000000000000000000000000000000000000000000000000039c8101cf84040000000000000000000000000000000000000000000000000003ffffff6bdbeff00000000000000000000000000000000000000000000000000000000003d00570000000000000000000000000000000000000000000000000016bd67e280a688000000000000000000000000000000000000000000000000000000076000001f000000000000000000000000000000000000000000000000003bdbbec0808208
  | 1, 9 => 0x3e13e89f42ffa0000000000000000000000000000000000000000000000000000424452b6765970000000000000000000000000000000000000000000000000016bd67e0a0a21c0000000000000000000000000000000000000000000000000039cb9e5ffffdff0000000000000000000000000000000000000000000000000000000003070583000000000000000000000000000000000000000000000000003ffffffefdfeff000000000000000000000000000000000000000000000000003ffed81fff7de0000000000000000000000000000000000000000000000000003fffffe285868b
  | 1, 10 => 0x3ffc177fff415f0000000000000000000000000000000000000000000000000016bd67ebe7c308000000000000000000000000000000000000000000000000003f50101f5a4140000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffffff4988248000000000000000000000000000000000000000000000000003ffffff6bdbeff0000000000000000000000000000000000000000000000000039cb9a5cd8d868000000000000000000000000000000000000000000000000003fffffe3878308
  | 1, 11 => 0x39cb9e5cf8f87c000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003ffffff6bdbeff000000000000000000000000000000000000000000000000003ffd32dfffc3480000000000000000000000000000000000000000000000000012980009c24100000000000000000000000000000000000000000000000000003e13e89f42ffa0000000000000000000000000000000000000000000000000003fffffe085820b000000000000000000000000000000000000000000000000000003eec000bebc
  | 1, 12 => 0x3cb7000000000000000000000000000000000000000000000000000000001d5a5960000000000000000000000000000000000000000000000000003ebd67ffc2c3080000000000000000000000000000000000000000000000000016bfefe080bebf00000000000000000000000000000000000000000000000000021020810203000000000000000000000000000000000000000000000000000000240120050003000000000000000000000000000000000000000000000000003bd8101dfa414000000000000000000000000000000000000000000000000000000061a0000683
  | 1, 13 => 0x2f76f9b71f1fe3000000000000000000000000000000000000000000000000003ffd32c08082080000000000000000000000000000000000000000000000000039cb9e5cf8f87c0000000000000000000000000000000000000000000000000001c81240980048000000000000000000000000000000000000000000000000003ffc101fff4140000000000000000000000000000000000000000000000000003e13ec9f62ffb4000000000000000000000000000000000000000000000000003fffffe0809a280000000000000000000000000000000000000000000000000001ec1760bd005f
  | 1, 14 => 0x2942981d5a5960000000000000000000000000000000000000000000000000003ffc141fff6154000000000000000000000000000000000000000000000000003ffff89fc2ffa0000000000000000000000000000000000000000000000000003e9beadfc2ffa8000000000000000000000000000000000000000000000000001211208942c3000000000000000000000000000000000000000000000000000014ad476ae5e49f0000000000000000000000000000000000000000000000000001ec1760bd005f000000000000000000000000000000000000000000000000000000001f7f65d7
  | 1, 15 => 0x129922c0808208000000000000000000000000000000000000000000000000003f53f89f5affe00000000000000000000000000000000000000000000000000028028814001820000000000000000000000000000000000000000000000000003ffffff4809a28000000000000000000000000000000000000000000000000002d66dd363d3cf70000000000000000000000000000000000000000000000000000000014181860000000000000000000000000000000000000000000000000000088076080001f0000000000000000000000000000000000000000000000000000000760003cbf
  | 2, 0 => 0x129922c9c2c308000000000000000000000000000000000000000000000000003ffc101fff41400000000000000000000000000000000000000000000000000000000009424100000000000000000000000000000000000000000000000000000003aac0009a28000000000000000000000000000000000000000000000000003fd8101ffa4140000000000000000000000000000000000000000000000000003fffffe08082080000000000000000000000000000000000000000000000000016bd67ebe7e79f00000000000000000000000000000000000000000000000000063461a3070783
  | 2, 1 => 0x3defdf76bdbcff000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000002d66dd363d3cf700000000000000000000000000000000000000000000000000000000003d3cf7000000000000000000000000000000000000000000000000002d66dd363d3cf70000000000000000000000000000000000000000000000000029429814181860000000000000000000000000000000000000000000000000003e9beac08082080000000000000000000000000000000000000000000000000016bd67ebe7e79f
  | 2, 2 => 0x3fdbfed6b8befc000000000000000000000000000000000000000000000000003bdbbeddfafb7c0000000000000000000000000000000000000000000000000010890248c0c008000000000000000000000000000000000000000000000000003ffffff6bda6df0000000000000000000000000000000000000000000000000000880240800008000000000000000000000000000000000000000000000000003ffd32dfffc348000000000000000000000000000000000000000000000000002d66dd3f7f7df700000000000000000000000000000000000000000000000000163561ab47e783
  | 2, 3 => 0x129922c9c2c30800000000000000000000000000000000000000000000000000000000094241000000000000000000000000000000000000000000000000000000000009427db7000000000000000000000000000000000000000000000000002d66dd2225249700000000000000000000000000000000000000000000000000000122c0008208000000000000000000000000000000000000000000000000003f76dd3f7f7df7000000000000000000000000000000000000000000000000003bdbbeddfafb7c0000000000000000000000000000000000000000000000000016bd67e2a58208
  | 2, 4 => 0x2d66dd343838740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffe9c2c308000000000000000000000000000000000000000000000000000000001f677db7000000000000000000000000000000000000000000000000003bdbbadddadb68000000000000000000000000000000000000000000000000000000001f7a7df4000000000000000000000000000000000000000000000000003ffffff6bdbee80000000000000000000000000000000000000000000000000039cb9e5cf8f87c
  | 2, 5 => 0x3ebfefffe7ffbf0000000000000000000000000000000000000000000000000016bd608be7e78000000000000000000000000000000000000000000000000000063461a3070783000000000000000000000000000000000000000000000000000000001f7f7df70000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffe387878b00000000000000000000000000000000000000000000000000063461a0000200000000000000000000000000000000000000000000000000003a13a89d42fb20
  | 2, 6 => 0x3fffffffffffff0000000000000000000000000000000000000000000000000039439c1c78f874000000000000000000000000000000000000000000000000003fffffffffffff00000000000000000000000000000000000000000000000000016415203d0057000000000000000000000000000000000000000000000000003fffffebe7e79f000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003fff9e5cf8f87c000000000000000000000000000000000000000000000000003fff981ffff960
  | 2, 7 => 0x167e000a69f000000000000000000000000000000000000000000000000003ffffffcf8c248000000000000000000000000000000000000000000000000003ebfefffe7ffbf000000000000000000000000000000000000000000000000000002cd20003cb7000000000000000000000000000000000000000000000000003f77fdb63dbef7000000000000000000000000000000000000000000000000003ffffffcf8fa7c0000000000000000000000000000000000000000000000000001ec1760800008000000000000000000000000000000000000000000000000003ffe9c1fff7974
  | 2, 8 => 0x3ffd77ffffe7df000000000000000000000000000000000000000000000000003f77fdbf42ffa0000000000000000000000000000000000000000000000000003ffd165fffe15c000000000000000000000000000000000000000000000000003fffffebe7c308000000000000000000000000000000000000000000000000003fffffffffffe8000000000000000000000000000000000000000000000000003ffd709fffe7c0000000000000000000000000000000000000000000000000002d42dc16383cf4000000000000000000000000000000000000000000000000003ebfefebe7e79f
  | 2, 9 => 0x39cb981cf8f860000000000000000000000000000000000000000000000000000003efe0008208000000000000000000000000000000000000000000000000003ebd67ffe7e79f000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003fffffe8e0e21c000000000000000000000000000000000000000000000000003fffffebe7e79f000000000000000000000000000000000000000000000000003deedd3efd7cf7
  | 2, 10 => 0x3fffffffffe7df000000000000000000000000000000000000000000000000003defdf7cf8f87c0000000000000000000000000000000000000000000000000001c81640b8005c0000000000000000000000000000000000000000000000000000ac0760a5001f000000000000000000000000000000000000000000000000000000001c787874000000000000000000000000000000000000000000000000003fdbf89ffaffe0000000000000000000000000000000000000000000000000003fffffffffffff00000000000000000000000000000000000000000000000000000000163d3cf7
  | 2, 11 => 0x3fdbfedfc2ffa80000000000000000000000000000000000000000000000000039cb9e48e0e01c0000000000000000000000000000000000000000000000000016bd064be7e11c000000000000000000000000000000000000000000000000000003e88000bea0000000000000000000000000000000000000000000000000003fdbfedcf8fa7c0000000000000000000000000000000000000000000000000039c9165cf8e05c000000000000000000000000000000000000000000000000003e9beedfe2ffbc000000000000000000000000000000000000000000000000003ffffffcc0fa28
  | 2, 12 => 0x1f7f4140000000000000000000000000000000000000000000000000003d67dd3e7dfcf70000000000000000000000000000000000000000000000000039cb9e5cc0f8280000000000000000000000000000000000000000000000000016bd67ebc2e788000000000000000000000000000000000000000000000000003ffedd3fff4140000000000000000000000000000000000000000000000000003ffd77ebe7e79f000000000000000000000000000000000000000000000000003ffffffffafffc000000000000000000000000000000000000000000000000003dcbde5ef8fcfc
  | 2, 13 => 0x388b8e5ce0f83c000000000000000000000000000000000000000000000000003ffffffffffb7c000000000000000000000000000000000000000000000000003ffffedffffffc000000000000000000000000000000000000000000000000003ffd77ffffe7df000000000000000000000000000000000000000000000000003fffffffe7ffbf000000000000000000000000000000000000000000000000003fffffffffffff0000000000000000000000000000000000000000000000000000038e4000b83c000000000000000000000000000000000000000000000000003fffffebc2e788
  | 2, 14 => 0x39ca9c1cf87874000000000000000000000000000000000000000000000000003fff9e5fffc148000000000000000000000000000000000000000000000000003fff9e5ffff97c0000000000000000000000000000000000000000000000000039cb9e5cf8c048000000000000000000000000000000000000000000000000000000001f427da0000000000000000000000000000000000000000000000000003fffdf7ffffdff000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000002d669c163d3874
  | 2, 15 => 0x3def9e5efdf87c0000000000000000000000000000000000000000000000000000000400202014000000000000000000000000000000000000000000000000003ffffdbffffff7000000000000000000000000000000000000000000000000003fdb9e5ffaf97c000000000000000000000000000000000000000000000000003ebfe89fe7ffa0000000000000000000000000000000000000000000000000003ffedd3fff7df7000000000000000000000000000000000000000000000000003f53fc9f7afff40000000000000000000000000000000000000000000000000001ec1000bd0040
  | 3, 0 => 0x3ffedd36bd3cf70000000000000000000000000000000000000000000000000016bd67e8e0e21c
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 386 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 386 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 386 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 386 then wireAt i else 0
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
  | 6 => 219
  | 7 => 175
  | _ => 0
def CH : Nat → Nat → Nat
  | 6, 0 => 0x48d2974946f8474e46c1b2c845701e22446a564444290d3c424e8253417c5d4240fb2d0a3f8b2cfe3f313b653ebf5c103da13db43d7b1e3a3d3209773ac6befb3a5309ac381d549c380480eb371fff3136287075344e166f336f124e30b17a1b2c05dd8b2baecc1d2ad82ba32a4abc0b29cdbc9d253f8be5223769d3213fea0120f0ba562039fdd71fe205301fbbaa661e8569621db48e521d7550671bdc203c1b30be7f1a3d0b5f19b9c868178028051658ec56153315f214c746c713b13c8e1274662d126c23b311418fe4105e17d50d8687440d0994b80ce919930c5be1980c12d1f9088b9c3706a5dad805ecc2ee0467551603b92f860330b35302f9ec86
  | 6, 1 => 0xa99d6bb8a70aed3fa62bfff7a24d3e86a1745b989dccd3d09d1ecbc39c79378499357d9197f220639794217292db9ffa902d5b0c8ecc3bc28e6a85208a7a9a9d88d6051288b703e688ad1ada861497468507e9eb84689b4d8341e6cc8284318981ef6bed807da9b37f6febe07de26d157a2269da79265e9d78b944807751c4e176c3c0467603a2dd745d8e61744fee3073fbe2cc736c3eab6ff442ca6fa458616e37ac586c5e9d666a498d116a2f9d6769f194fb69904ec9684ea6b866c490a26624a08364f83f645e976f455e199a5c5d3edab75cfc72835c173fbb5a75721d5a2cc3f458d7e684506d52fe4fce462c4f852c6d4ccd68b54b83029749ee7a49
  | 6, 2 => 0xde3480bcdcf7b9f8dcc9e4eedb2c04c2d78489b0d6e094d3d454066cd45296d2cfd6e79ecfd29977cfba4a1ccf57e870cf17ab5ecf171212cec12179cdef7705cd4d4423ccd7abf8cc03e04ccb7a0fdfc8b74ff0c89d7b8fc7e07e8ac6fa342cc6d23c35c4a34fb4c463bb14c4374b3ac3f777cdbebd2cbbbdbc8780bdb4a5cbbd15572dbce92dbfbcd4bababc9fcb20bc2067d6bbf07120bb3f33fab9720104b9653685b95247afb92f5c87b6f1867ab574c2ceb25bf2acb22e73c4b2003480b0da6afdb0b62913b03b1c5fb0167aacafa67aadaf81c9c5aeec9bcaae651889adcd0e94adc5e519ad81abe0ad70f268ad209d4facd99b96ab94a992aa939139
  | 6, 3 => 0xffe602bdfd76da79fb6d2ecff9a8b337f9963cc4f943fd5ff75143c9f61649e1f5f4fc2af56a71faf3c7c120f36d449cf1d10e6ff1582cd2ef8bcdfbef6b2279ef502352ee12c54dec6f887bebb11d6beb2cd58fe8197b1de6527f1ce64c55b1e59a4bdce4db98e8e458c67c
  | 7, 0 => 0x5a24f22f59bf3e13595bb8d458871ddb563d6c9d55e7a0d6538ed0be5310cae852e2f8d7526f455b51529dc450d632f74e31041e4def43ed4d8180284d2f3c8a4cfebf194c6505a34b8b4c2a4b550f7147e56217479295b946d95771443331984125de8a40fd5c89400015073f1911403c05e1c63bbd9fd83b9517d9375c328c36c151b13578c84e33513a602cbbaac62563fe19250869ae25029ba324c4815c24bad1af23bebf212358f6eb21da3c20212bd5321ed943511dbf2e791c91f0b519570811186b8f5c17a485a0167ebc1d161ad833147387c8131d3b54122bc8a90f88aeee0f52f7e70ae68dfb05a02dba0402104d03490f6b0346c6ec0122554d
  | 7, 1 => 0xc09467eac08ae272c088584abfb0bb14bb5f66ffb8b93da7b7aa7e56b6e02c80b158ad0fb14a7c74b0bd8805b0316723afe37ca7af0a244eac584a90aa7319c3a86c13e6a6ea9da8a5312b42a42a80b8a3dc3944a3bebdf8a0e18795a07a6a93a022680c9de491ff9dd97e9597941ecf96f519d9966e67f09595db7994ffe11f938d511f91ffdd0791869cbe911bcb618ff96af68a713de385cf5b4385a3bc0f84613cd4831991368302b3d67dc3c7c379ff8fe97858dcaa6f1f7e7a6c96dad26bf88c416bee9c076986998d6724e6de6608c41364f109006430b85d62125aeb61b0ce8d603fd0126001d5a75eec2d245e4f53365e4e7aea5bcd8fcd5ab5abb1
  | 7, 2 => 0xff33d146fee73185fe971ab2fcd4c3e5fba0a51cf9f4960ff9554771f303c3f4f29bf981f071128bf05ab396efb5a3deeee8ad45eeca28f2edbd194fec01c0ebebf3dd49eaac3b0be8f3ed30e7311744e3412cc1e010dfbade7c5035dccedae9dc5b1b28dc06615adb7c6105db4ac3adda5e734ed982c8fbd916e5cfd7fdd228d7ca020fd71460e3d6a4388cd2b37aa2cdc8ba32ca94fea2c87c4895c73f73a1c708d5a6c68acfd0c4cca2acc43bc065c3827a75c3101f35c0a94172
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 6, 0 => 0x1000000000000100000000000000000000000000000000000000000000000000010000000000001000000000000000000000000020000000000002000000000000200000000000000000000000001000000000000000000000000010000000000001000000000000100000000000020000000000000000000000000100000000000020000000000002000000000000000000000000000000000000002000000000000000000000000000000000000002000000000000200000000000000000000000001
  | 6, 1 => 0x20000000000002000000000000000000000000000000000000002000000000000100000000000000000000000001000000000000200000000000010000000000002000000000000100000000000000000000000002000000000000200000000000000000000000001000000000000100000000000010000000000000000000000000100000000000020000000000000000000000000100000000000010000000000000000000000000200000000000000000000000001000000000000200000000000020000000000001
  | 6, 2 => 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000200000000000000000000000001000000000000200000000000020000000000002000000000000000000000000020000000000000000000000000200000000000010000000000000000000000000100000000000010000000000001000000000000200000000000010000000000001000000000000000000000000000000000000000
  | 6, 3 => 0x20000000000000000000000000000000000000010000000000002000000000000100000000000010000000000000000000000000100000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000002000000000000100000000000010000000000001000000000000200000000000020000000000002000000000000000000000000000000000000002000000000000100000000000010000000000001000000000000200000000000000000000000002
  | 6, 4 => 0x20000000000001000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000001000000000000100000000000020000000000000000000000000200000000000020000000000002000000000000100000000000020000000000001000000000000100000000000000000000000000000000000000100000000000010000000000001000000000000100000000000020000000000000000000000000200000000000000000000000001
  | 6, 5 => 0x2000000000000000000000000010000000000002000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000200000000000020000000000002000000000000000000000000010000000000000000000000000000000000000010000000000002000000000000000000000000020000000000000000000000000100000000000020000000000001000000000000200000000000000000000000000000000000000100000000000020000000000002
  | 6, 6 => 0x10000000000002000000000000000000000000000000000000000000000000000200000000000010000000000000000000000000000000000000010000000000002000000000000200000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000200000000000000000000000002
  | 7, 0 => 0x10000000000002000000000000100000000000000000000000000000000000000100000000000000000000000001000000000000100000000000010000000000002000000000000200000000000010000000000001000000000000200000000000000000000000002000000000000200000000000010000000000002000000000000200000000000020000000000002000000000000000000000000010000000000000000000000000200000000000000000000000001000000000000000000000000010000000000000
  | 7, 1 => 0x20000000000000000000000000200000000000020000000000000000000000000000000000000010000000000001000000000000000000000000000000000000001000000000000200000000000000000000000001000000000000200000000000010000000000000000000000000000000000000000000000000002000000000000100000000000000000000000000000000000000000000000000020000000000000000000000000200000000000000000000000000000000000000000000000000020000000000002
  | 7, 2 => 0x2000000000000100000000000020000000000002000000000000000000000000020000000000002000000000000200000000000000000000000001000000000000200000000000010000000000001000000000000000000000000010000000000001000000000000000000000000020000000000000000000000000100000000000000000000000002000000000000100000000000020000000000002000000000000200000000000010000000000002000000000000200000000000000000000000002
  | 7, 3 => 0x20000000000002000000000000000000000000000000000000001000000000000100000000000020000000000000000000000000100000000000010000000000001000000000000200000000000000000000000001000000000000000000000000010000000000000000000000000200000000000000000000000001000000000000100000000000020000000000000000000000000200000000000010000000000001000000000000000000000000000000000000002000000000000100000000000010000000000000
  | 7, 4 => 0x10000000000001000000000000200000000000000000000000000000000000000000000000000010000000000001000000000000100000000000010000000000001000000000000100000000000000000000000000000000000000100000000000010000000000001000000000000200000000000020000000000002000000000000000000000000020000000000001000000000000000000000000010000000000001000000000000100000000000010000000000002000000000000200000000000000000000000001
  | 7, 5 => 0x100000000000010000000000000000000000000100000000000020000000000002000000000000200000000000010000000000002000000000000000000000000000000000000001000000000000000000000000010000000000002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_31 roots_31 6 s ws hint
  | 1 => checkCutEntry dom_55 roots_55 6 s ws hint
  | 2 => checkCutEntry dom_47 roots_47 6 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_63 goalM u ys) : RunD dom_63 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_63 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 32 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 48 → Z 5 i = true := (range_split z5_0 (range_split z5_16 z5_32))
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
private theorem z6_432 : ∀ i, 432 ≤ i → i < 448 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_448 : ∀ i, 448 ≤ i → i < 464 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_464 : ∀ i, 464 ≤ i → i < 480 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_480 : ∀ i, 480 ≤ i → i < 496 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_496 : ∀ i, 496 ≤ i → i < 512 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_512 : ∀ i, 512 ≤ i → i < 528 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_528 : ∀ i, 528 ≤ i → i < 544 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_544 : ∀ i, 544 ≤ i → i < 560 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_560 : ∀ i, 560 ≤ i → i < 576 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_576 : ∀ i, 576 ≤ i → i < 592 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_592 : ∀ i, 592 ≤ i → i < 608 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_608 : ∀ i, 608 ≤ i → i < 624 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_624 : ∀ i, 624 ≤ i → i < 640 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_640 : ∀ i, 640 ≤ i → i < 656 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 640 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_656 : ∀ i, 656 ≤ i → i < 672 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 656 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_672 : ∀ i, 672 ≤ i → i < 676 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 672 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 676 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 (range_split z6_48 z6_64))) (range_split (range_split z6_80 z6_96) (range_split z6_112 (range_split z6_128 z6_144)))) (range_split (range_split (range_split z6_160 z6_176) (range_split z6_192 (range_split z6_208 z6_224))) (range_split (range_split z6_240 (range_split z6_256 z6_272)) (range_split z6_288 (range_split z6_304 z6_320))))) (range_split (range_split (range_split (range_split z6_336 z6_352) (range_split z6_368 (range_split z6_384 z6_400))) (range_split (range_split z6_416 (range_split z6_432 z6_448)) (range_split z6_464 (range_split z6_480 z6_496)))) (range_split (range_split (range_split z6_512 z6_528) (range_split z6_544 (range_split z6_560 z6_576))) (range_split (range_split z6_592 (range_split z6_608 z6_624)) (range_split z6_640 (range_split z6_656 z6_672))))))
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
private theorem z7_256 : ∀ i, 256 ≤ i → i < 272 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_272 : ∀ i, 272 ≤ i → i < 288 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_288 : ∀ i, 288 ≤ i → i < 304 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_304 : ∀ i, 304 ≤ i → i < 320 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_320 : ∀ i, 320 ≤ i → i < 336 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_336 : ∀ i, 336 ≤ i → i < 352 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_352 : ∀ i, 352 ≤ i → i < 368 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_368 : ∀ i, 368 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_384 : ∀ i, 384 ≤ i → i < 400 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_400 : ∀ i, 400 ≤ i → i < 416 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_416 : ∀ i, 416 ≤ i → i < 432 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_432 : ∀ i, 432 ≤ i → i < 448 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_448 : ∀ i, 448 ≤ i → i < 464 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_464 : ∀ i, 464 ≤ i → i < 480 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_480 : ∀ i, 480 ≤ i → i < 496 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_496 : ∀ i, 496 ≤ i → i < 512 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_512 : ∀ i, 512 ≤ i → i < 528 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 512 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_528 : ∀ i, 528 ≤ i → i < 544 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 528 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_544 : ∀ i, 544 ≤ i → i < 560 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 544 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_560 : ∀ i, 560 ≤ i → i < 576 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 560 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_576 : ∀ i, 576 ≤ i → i < 592 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 576 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_592 : ∀ i, 592 ≤ i → i < 608 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 592 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_608 : ∀ i, 608 ≤ i → i < 624 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 608 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_624 : ∀ i, 624 ≤ i → i < 640 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 624 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_640 : ∀ i, 640 ≤ i → i < 641 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 640 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 641 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 (range_split z7_48 z7_64))) (range_split (range_split z7_80 z7_96) (range_split z7_112 (range_split z7_128 z7_144)))) (range_split (range_split (range_split z7_160 z7_176) (range_split z7_192 (range_split z7_208 z7_224))) (range_split (range_split z7_240 z7_256) (range_split z7_272 (range_split z7_288 z7_304))))) (range_split (range_split (range_split (range_split z7_320 z7_336) (range_split z7_352 (range_split z7_368 z7_384))) (range_split (range_split z7_400 z7_416) (range_split z7_432 (range_split z7_448 z7_464)))) (range_split (range_split (range_split z7_480 z7_496) (range_split z7_512 (range_split z7_528 z7_544))) (range_split (range_split z7_560 (range_split z7_576 z7_592)) (range_split z7_608 (range_split z7_624 z7_640))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_32 : ∀ i, 32 ≤ i → i < 45 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 13 32 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 45 → Z 8 i = true := (range_split z8_0 (range_split z8_16 z8_32))
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 14]⟩], 15⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 10 := by decide

theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (3941132968 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (3941132968 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132968 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 10 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (3941132968 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 10 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_15513_aux

theorem PEqualNP.Outside.L_meta_15513 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132968 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132968 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_15513_aux.wit, PEqualNP.Outside.L_meta_15513_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_15513_aux.wit_sz (PEqualNP.Outside.L_meta_15513_aux.lower s hs), PEqualNP.Outside.L_meta_15513_aux.wit_ev⟩
