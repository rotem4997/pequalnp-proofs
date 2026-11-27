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

namespace PEqualNP.Outside.L_meta_16205_aux

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
      simp only [binD, andD, Nat.testBit_and, Nat.zero_testBit] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · cases op
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, andD, Nat.testBit_and] at *
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
  cases b <;> simp [kept, List.countP_cons] <;> omega

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
        Or.inr ⟨negD d a, List.mem_cons_self, by rw [negD_and_sub hd hsub a]; simp [negD]⟩
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
        rw [orD_and_sub hsub]; simp [orD]
      · simp only [z1, z0, ite_true, Bool.not_true, Bool.false_eq_true, binD, ite_false]
        rw [andD_and_sub hsub]; simp [andD]
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

theorem mask_idemp (d w : Nat) : (w &&& d) &&& d = w &&& d := by
  simp [Nat.and_self]

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
    have hstep : ∃ p1 bank1, p1 ≤ p + 1 ∧ NatReach mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g], Avail mask256 bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, andD mask256 a mask256 &&& mask256 = a &&& mask256 := fun a => by
        simp [andD]
      have hor_0 : ∀ a, orD mask256 a 0 &&& mask256 = a &&& mask256 := fun a => by
        simp [orD]
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


def dom_141 : Nat := 0x5050000
def goal_141 : Nat := 0x4000000
def roots_141 : List Nat := [xs256.getD 1 0, xs256.getD 3 0]
def L_141 : Nat := 1
namespace S_141
def pairsG : List (Nat × Nat) := [(24, 26), (18, 26)]
def r1sG : List Nat := [24, 18]
def r2sG : List Nat := [26, 26]
def mpG : Nat := 0x3
def pool6G : List Nat := []
def xsM : List Nat := roots_141.map (· &&& dom_141)
def goalM : Nat := goal_141 &&& dom_141
def NN : Nat → Nat
  | _ => 0
def HT : Nat → Nat → Nat
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def stateW : Nat → Nat
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 1 0) :: stateWires n (ids >>> 1)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 0 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 0 → wireDOK i = true := by omega
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 0 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    omega
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 0 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 1 0) :: stateWiresD n (ids >>> 1)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 1 0) :: stateWiresS n (ids >>> 1)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 1 0 (NN s)
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
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_141 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_141 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_141 goalM u ys) : RunD dom_141 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_141 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem checked (s : Nat) (hs : s ≤ 0) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_141 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 0 1 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 0) (h : RunD dom_141 goalM s xsM) : False := by
  have hmin : 1 ≤ s := by
    have hl := run_len h; change 2 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_141 roots_141 goal_141 1 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_141 goal_141 := by
    have h0 : isConstB dom_141 goal_141 = false := by decide +kernel
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
end S_141
theorem low_141 : Lower dom_141 roots_141 goal_141 1 := S_141.noCircuit
def dom_263 : Nat := 0x3300000000
def goal_263 : Nat := 0x2000000000
def roots_263 : List Nat := [xs256.getD 0 0, xs256.getD 2 0]
def L_263 : Nat := 1
namespace S_263
def pairsG : List (Nat × Nat) := [(36, 37), (33, 37)]
def r1sG : List Nat := [36, 33]
def r2sG : List Nat := [37, 37]
def mpG : Nat := 0x3
def pool6G : List Nat := []
def xsM : List Nat := roots_263.map (· &&& dom_263)
def goalM : Nat := goal_263 &&& dom_263
def NN : Nat → Nat
  | _ => 0
def HT : Nat → Nat → Nat
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def stateW : Nat → Nat
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 1 0) :: stateWires n (ids >>> 1)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 0 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 0 → wireDOK i = true := by omega
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 0 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    omega
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 0 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 1 0) :: stateWiresD n (ids >>> 1)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 1 0) :: stateWiresS n (ids >>> 1)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 1 0 (NN s)
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
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_263 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_263 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_263 goalM u ys) : RunD dom_263 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_263 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem checked (s : Nat) (hs : s ≤ 0) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_263 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 0 1 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 0) (h : RunD dom_263 goalM s xsM) : False := by
  have hmin : 1 ≤ s := by
    have hl := run_len h; change 2 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_263 roots_263 goal_263 1 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_263 goal_263 := by
    have h0 : isConstB dom_263 goal_263 = false := by decide +kernel
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
end S_263
theorem low_263 : Lower dom_263 roots_263 goal_263 1 := S_263.noCircuit
def dom_380 : Nat := 0x303000000000000
def goal_380 : Nat := 0x200000000000000
def roots_380 : List Nat := [xs256.getD 0 0, xs256.getD 3 0]
def L_380 : Nat := 1
namespace S_380
def pairsG : List (Nat × Nat) := [(56, 57), (49, 57)]
def r1sG : List Nat := [56, 49]
def r2sG : List Nat := [57, 57]
def mpG : Nat := 0x3
def pool6G : List Nat := []
def xsM : List Nat := roots_380.map (· &&& dom_380)
def goalM : Nat := goal_380 &&& dom_380
def NN : Nat → Nat
  | _ => 0
def HT : Nat → Nat → Nat
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def stateW : Nat → Nat
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 1 0) :: stateWires n (ids >>> 1)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 0 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 0 → wireDOK i = true := by omega
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 0 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    omega
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 0 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 1 0) :: stateWiresD n (ids >>> 1)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 1 0) :: stateWiresS n (ids >>> 1)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 1 0 (NN s)
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
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_380 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_380 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_380 goalM u ys) : RunD dom_380 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_380 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
theorem checked (s : Nat) (hs : s ≤ 0) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_380 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 0 1 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 0) (h : RunD dom_380 goalM s xsM) : False := by
  have hmin : 1 ≤ s := by
    have hl := run_len h; change 2 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_380 roots_380 goal_380 1 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_380 goal_380 := by
    have h0 : isConstB dom_380 goal_380 = false := by decide +kernel
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
end S_380
theorem low_380 : Lower dom_380 roots_380 goal_380 1 := S_380.noCircuit
def dom_237 : Nat := 0x44444444
def goal_237 : Nat := 0x44404000
def roots_237 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]
def L_237 : Nat := 4
namespace S_237
def pairsG : List (Nat × Nat) := [(10, 14), (6, 14), (6, 22), (10, 26), (18, 22), (18, 26)]
def r1sG : List Nat := [10, 6, 6, 10, 18, 18]
def r2sG : List Nat := [14, 14, 22, 26, 22, 26]
def mpG : Nat := 0x3f
def pool6G : List Nat := [11072729126414, 19817282016782, 6640323139094]
def xsM : List Nat := roots_237.map (· &&& dom_237)
def goalM : Nat := goal_237 &&& dom_237
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x38233cb0
  | 3, 0 => 0x38233cb0
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x4444000000000000000000000000000000000000000000000000000000000000440044000000000000000000000000000000000000000000000000000000000040404040
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x243
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 10
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3000000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000006
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c000000000000000000000000000000000000000000000000000000000000002b0000000000000000000000000000000000000000000000000000000000000017
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_237 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_237 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_237 goalM u ys) : RunD dom_237 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_237 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → (Z 2) i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → (Z 2) i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_237 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_237 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_237 roots_237 goal_237 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_237 goal_237 := by
    have h0 : isConstB dom_237 goal_237 = false := by decide +kernel
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
end S_237
theorem low_237 : Lower dom_237 roots_237 goal_237 4 := S_237.noCircuit
def dom_296 : Nat := 0xff0000000000
def goal_296 : Nat := 0xe80000000000
def roots_296 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0]
def L_296 : Nat := 4
namespace S_296
def pairsG : List (Nat × Nat) := [(42, 43), (41, 43), (41, 45), (42, 46), (44, 45), (44, 46)]
def r1sG : List Nat := [42, 41, 41, 42, 44, 44]
def r2sG : List Nat := [43, 43, 45, 46, 45, 46]
def mpG : Nat := 0x3f
def pool6G : List Nat := [46356323184171, 48555279395627]
def xsM : List Nat := roots_296.map (· &&& dom_296)
def goalM : Nat := goal_296 &&& dom_296
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x47cc91f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000000000000000000000000000000000000000000000000000cc00000000000000000000000000000000000000000000000000000000000000aa0000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3000000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000006
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c000000000000000000000000000000000000000000000000000000000000002b0000000000000000000000000000000000000000000000000000000000000017
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_296 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_296 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_296 goalM u ys) : RunD dom_296 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_296 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_296 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_296 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_296 roots_296 goal_296 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_296 goal_296 := by
    have h0 : isConstB dom_296 goal_296 = false := by decide +kernel
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
end S_296
theorem low_296 : Lower dom_296 roots_296 goal_296 4 := S_296.noCircuit
def dom_320 : Nat := 0xcccc00000000
def goal_320 : Nat := 0xc88000000000
def roots_320 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0]
def L_320 : Nat := 4
namespace S_320
def pairsG : List (Nat × Nat) := [(38, 39), (35, 39), (35, 43), (38, 46), (42, 43), (42, 46)]
def r1sG : List Nat := [38, 35, 35, 38, 42, 42]
def r2sG : List Nat := [39, 39, 43, 46, 43, 46]
def mpG : Nat := 0x3f
def pool6G : List Nat := [41928060513063, 46330401992238, 41945240839982, 41962420512558]
def xsM : List Nat := roots_320.map (· &&& dom_320)
def goalM : Nat := goal_320 &&& dom_320
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xcee0398e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc00000000000000000000000000000000000000000000000000000000000000c0c0000000000000000000000000000000000000000000000000000000000000888800000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3000000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000006
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c000000000000000000000000000000000000000000000000000000000000002b0000000000000000000000000000000000000000000000000000000000000017
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_320 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_320 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_320 goalM u ys) : RunD dom_320 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_320 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_320 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_320 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_320 roots_320 goal_320 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_320 goal_320 := by
    have h0 : isConstB dom_320 goal_320 = false := by decide +kernel
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
end S_320
theorem low_320 : Lower dom_320 roots_320 goal_320 4 := S_320.noCircuit
def dom_440 : Nat := 0xf000f0000000000
def goal_440 : Nat := 0xe00080000000000
def roots_440 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0]
def L_440 : Nat := 4
namespace S_440
def pairsG : List (Nat × Nat) := [(42, 43), (41, 43), (41, 57), (42, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [42, 41, 41, 42, 56, 56]
def r2sG : List Nat := [43, 43, 57, 58, 57, 58]
def mpG : Nat := 0x3f
def pool6G : List Nat := [46352230398507, 61745141528890]
def xsM : List Nat := roots_440.map (· &&& dom_440)
def goalM : Nat := goal_440 &&& dom_440
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xd5fecd4d
  | 3, 0 => 0xd5fecd4d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000000000000000000000000000000000000000000000000000c000c00000000000000000000000000000000000000000000000000000000000a000a0000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x243
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 10
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3000000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000006
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c000000000000000000000000000000000000000000000000000000000000002b0000000000000000000000000000000000000000000000000000000000000017
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_440 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_440 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_440 goalM u ys) : RunD dom_440 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_440 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → (Z 2) i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → (Z 2) i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_440 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_440 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_440 roots_440 goal_440 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_440 goal_440 := by
    have h0 : isConstB dom_440 goal_440 = false := by decide +kernel
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
end S_440
theorem low_440 : Lower dom_440 roots_440 goal_440 4 := S_440.noCircuit
def dom_480 : Nat := 0x4444444400000000
def goal_480 : Nat := 0x4440400000000000
def roots_480 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]
def L_480 : Nat := 4
namespace S_480
def pairsG : List (Nat × Nat) := [(42, 46), (38, 46), (38, 54), (42, 58), (50, 54), (50, 58)]
def r1sG : List Nat := [42, 38, 38, 42, 50, 50]
def r2sG : List Nat := [46, 46, 54, 58, 54, 58]
def mpG : Nat := 0x3f
def pool6G : List Nat := [41997032634934, 41996830780990]
def xsM : List Nat := roots_480.map (· &&& dom_480)
def goalM : Nat := goal_480 &&& dom_480
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xd585f17f
  | 3, 0 => 0xd585f17f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x444400000000000000000000000000000000000000000000000000000000000044004400000000000000000000000000000000000000000000000000000000004040404000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x243
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 10
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3000000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000006
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c000000000000000000000000000000000000000000000000000000000000002b0000000000000000000000000000000000000000000000000000000000000017
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_480 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_480 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_480 goalM u ys) : RunD dom_480 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_480 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → (Z 2) i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → (Z 2) i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_480 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_480 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_480 roots_480 goal_480 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_480 goal_480 := by
    have h0 : isConstB dom_480 goal_480 = false := by decide +kernel
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
end S_480
theorem low_480 : Lower dom_480 roots_480 goal_480 4 := S_480.noCircuit
def dom_623 : Nat := 0x303000003030000
def goal_623 : Nat := 0x200000000000000
def roots_623 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]
def L_623 : Nat := 2
theorem low_623 : Lower dom_623 roots_623 goal_623 2 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000000000000, 25, 57)] (by decide +kernel) (by decide +kernel) low_380
def dom_682 : Nat := 0xa000a000a000a00
def goal_682 : Nat := 0xa00080008000000
def roots_682 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]
def L_682 : Nat := 4
namespace S_682
def pairsG : List (Nat × Nat) := [(25, 27), (11, 27), (11, 43), (25, 57), (41, 43), (41, 57)]
def r1sG : List Nat := [25, 11, 11, 25, 41, 41]
def r2sG : List Nat := [27, 27, 43, 57, 43, 57]
def mpG : Nat := 0x3f
def pool6G : List Nat := [27535458638619, 27595353168697]
def xsM : List Nat := roots_682.map (· &&& dom_682)
def goalM : Nat := goal_682 &&& dom_682
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x2494040d
  | 3, 0 => 0x2494040d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa000a00000000000000000000000000000000000000000000000000000000000a0000000a0000000000000000000000000000000000000000000000000000000800080008000800
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 2, 0, 0 => 0x243
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 2 => 10
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3000000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000006
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c000000000000000000000000000000000000000000000000000000000000002b0000000000000000000000000000000000000000000000000000000000000017
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_682 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_682 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_682 goalM u ys) : RunD dom_682 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_682 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2_0 : ∀ i, 0 ≤ i → i < 1 → (Z 2) i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → (Z 2) i = true := z2_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_682 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_682 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_682 roots_682 goal_682 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_682 goal_682 := by
    have h0 : isConstB dom_682 goal_682 = false := by decide +kernel
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
end S_682
theorem low_682 : Lower dom_682 roots_682 goal_682 4 := S_682.noCircuit
def dom_161 : Nat := 0xffff0000
def goal_161 : Nat := 0xece00000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]
def L_161 : Nat := 4
namespace S_161
def pairsG : List (Nat × Nat) := [(20, 21), (20, 22), (17, 21), (18, 26), (18, 22), (19, 23), (19, 27), (24, 26), (25, 27), (25, 29), (28, 29), (28, 30)]
def r1sG : List Nat := [20, 20, 17, 18, 18, 19, 19, 24, 25, 25, 28, 28]
def r2sG : List Nat := [21, 22, 21, 26, 22, 23, 27, 26, 27, 29, 29, 30]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_161.map (· &&& dom_161)
def goalM : Nat := goal_161 &&& dom_161
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe9e6f74a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c0300000000000000000000000000000000000000000000000000000000000000780000000000000000000000000000000000000000000000000000000000000364
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc80000000000000000000000000000000000000000000000000000000000000e3700000000000000000000000000000000000000000000000000000000000009fa0000000000000000000000000000000000000000000000000000000000000765
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_161 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_161 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_161 goalM u ys) : RunD dom_161 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_161 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_161 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_161 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_161 roots_161 goal_161 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_161 goal_161 := by
    have h0 : isConstB dom_161 goal_161 = false := by decide +kernel
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
end S_161
theorem low_161 : Lower dom_161 roots_161 goal_161 4 := S_161.noCircuit
def dom_215 : Nat := 0xff00ff00
def goal_215 : Nat := 0xec00e000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]
def L_215 : Nat := 4
namespace S_215
def pairsG : List (Nat × Nat) := [(12, 13), (12, 14), (9, 13), (10, 26), (10, 14), (11, 15), (11, 27), (24, 26), (25, 27), (25, 29), (28, 29), (28, 30)]
def r1sG : List Nat := [12, 12, 9, 10, 10, 11, 11, 24, 25, 25, 28, 28]
def r2sG : List Nat := [13, 14, 13, 26, 14, 15, 27, 26, 27, 29, 29, 30]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_215.map (· &&& dom_215)
def goalM : Nat := goal_215 &&& dom_215
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x8299b27f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aa00aa00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c0300000000000000000000000000000000000000000000000000000000000000780000000000000000000000000000000000000000000000000000000000000364
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc80000000000000000000000000000000000000000000000000000000000000e3700000000000000000000000000000000000000000000000000000000000009fa0000000000000000000000000000000000000000000000000000000000000765
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_215 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_215 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_215 goalM u ys) : RunD dom_215 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_215 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := z3_0
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_215 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_215 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_215 roots_215 goal_215 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_215 goal_215 := by
    have h0 : isConstB dom_215 goal_215 = false := by decide +kernel
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
end S_215
theorem low_215 : Lower dom_215 roots_215 goal_215 4 := S_215.noCircuit
def dom_239 : Nat := 0xcccccccc
def goal_239 : Nat := 0xccc0c080
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]
def L_239 : Nat := 5
theorem low_239 : Lower dom_239 roots_239 goal_239 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x88888888, 6, 7)] (by decide +kernel) (by decide +kernel) low_237
def dom_240 : Nat := 0x55555555
def goal_240 : Nat := 0x44404000
def roots_240 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]
def L_240 : Nat := 5
theorem low_240 : Lower dom_240 roots_240 goal_240 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x44444444, 12, 14)] (by decide +kernel) (by decide +kernel) low_237
def dom_323 : Nat := 0xffff00000000
def goal_323 : Nat := 0xe8a000000000
def roots_323 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]
def L_323 : Nat := 5
theorem low_323 : Lower dom_323 roots_323 goal_323 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff0000000000, 35, 43)] (by decide +kernel) (by decide +kernel) low_296
def dom_431 : Nat := 0xff00ff00000000
def goal_431 : Nat := 0xe000a000000000
def roots_431 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]
def L_431 : Nat := 3
theorem low_431 : Lower dom_431 roots_431 goal_431 3 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00000000, 52, 54), (0xff000000000000, 38, 54)] (by decide +kernel) (by decide +kernel) low_263
def dom_458 : Nat := 0xff00ff0000000000
def goal_458 : Nat := 0xee00e80000000000
def roots_458 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]
def L_458 : Nat := 5
theorem low_458 : Lower dom_458 roots_458 goal_458 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00000000000000, 41, 57)] (by decide +kernel) (by decide +kernel) low_296
def dom_467 : Nat := 0xf0f0f0f00000000
def goal_467 : Nat := 0xe00080000000000
def roots_467 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]
def L_467 : Nat := 5
theorem low_467 : Lower dom_467 roots_467 goal_467 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f0000000000, 35, 43)] (by decide +kernel) (by decide +kernel) low_440
def dom_482 : Nat := 0xcccccccc00000000
def goal_482 : Nat := 0xccc0c88000000000
def roots_482 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]
def L_482 : Nat := 5
theorem low_482 : Lower dom_482 roots_482 goal_482 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc000000000000, 38, 54)] (by decide +kernel) (by decide +kernel) low_320
def dom_483 : Nat := 0x5555555500000000
def goal_483 : Nat := 0x4440400000000000
def roots_483 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]
def L_483 : Nat := 5
theorem low_483 : Lower dom_483 roots_483 goal_483 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x4444444400000000, 44, 46)] (by decide +kernel) (by decide +kernel) low_480
def dom_539 : Nat := 0xff000000ff00
def goal_539 : Nat := 0xe8000000e000
def roots_539 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]
def L_539 : Nat := 5
theorem low_539 : Lower dom_539 roots_539 goal_539 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff0000000000, 11, 43)] (by decide +kernel) (by decide +kernel) low_296
def dom_563 : Nat := 0xcccc0000cccc
def goal_563 : Nat := 0xc8800000c080
def roots_563 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]
def L_563 : Nat := 5
theorem low_563 : Lower dom_563 roots_563 goal_563 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc00000000, 11, 43)] (by decide +kernel) (by decide +kernel) low_320
def dom_629 : Nat := 0xf0f00000f0f0000
def goal_629 : Nat := 0xe0000000c000000
def roots_629 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]
def L_629 : Nat := 3
theorem low_629 : Lower dom_629 roots_629 goal_629 3 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a00000a0a0000, 56, 57), (0xf0f000000000000, 25, 57)] (by decide +kernel) (by decide +kernel) low_141
def dom_683 : Nat := 0xf000f000f000f00
def goal_683 : Nat := 0xe0008000c000000
def roots_683 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]
def L_683 : Nat := 5
theorem low_683 : Lower dom_683 roots_683 goal_683 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f0000000000, 11, 43)] (by decide +kernel) (by decide +kernel) low_440
def dom_700 : Nat := 0xaa00aa00aa00aa00
def goal_700 : Nat := 0xaa00a800a800a000
def roots_700 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]
def L_700 : Nat := 5
theorem low_700 : Lower dom_700 roots_700 goal_700 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a000a000a000, 9, 13)] (by decide +kernel) (by decide +kernel) low_682
def dom_704 : Nat := 0x303030303030303
def goal_704 : Nat := 0x200000000000000
def roots_704 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def L_704 : Nat := 3
theorem low_704 : Lower dom_704 roots_704 goal_704 3 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303000003030000, 41, 57), (0x303030300000000, 25, 57)] (by decide +kernel) (by decide +kernel) low_380
def dom_709 : Nat := 0xa0a0a0a0a0a0a0a
def goal_709 : Nat := 0xa00080008000000
def roots_709 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def L_709 : Nat := 5
theorem low_709 : Lower dom_709 roots_709 goal_709 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a000a000a00, 19, 27)] (by decide +kernel) (by decide +kernel) low_682
def dom_242 : Nat := 0xffffffff
def goal_242 : Nat := 0xece0e0a0
def roots_242 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]
def L_242 : Nat := 7
namespace S_242
def pairsG : List (Nat × Nat) := [(4, 5), (12, 14), (1, 5), (6, 14), (6, 22), (3, 7), (6, 7), (9, 13), (10, 14), (10, 26), (11, 15), (11, 27), (12, 13), (17, 21), (18, 22), (18, 26), (19, 23), (19, 27), (20, 21), (20, 22), (24, 26), (25, 27), (25, 29), (28, 29), (28, 30)]
def r1sG : List Nat := [4, 12, 1, 6, 6, 3, 6, 9, 10, 10, 11, 11, 12, 17, 18, 18, 19, 19, 20, 20, 24, 25, 25, 28, 28]
def r2sG : List Nat := [5, 14, 5, 14, 22, 7, 7, 13, 14, 26, 15, 27, 13, 21, 22, 26, 23, 27, 21, 22, 26, 27, 29, 29, 30]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [13207327805191, 20934092066326, 30786646121230, 3341654103319, 6700452351246, 18760518272781, 27608117349645, 4411084184346]
def xsM : List Nat := roots_242.map (· &&& dom_242)
def goalM : Nat := goal_242 &&& dom_242
def NN : Nat → Nat
  | 4 => 1
  | 5 => 7
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa3a4acb0
  | 5, 0 => 0xea902df2e269044ad5d7a2ceb41bdfa3599be9b2569c8b90564c9356
  | 6, 0 => 0x1f16380d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff00000000000000000000000000000000000000000000000000000000aaaaaaaa000000000000000000000000000000000000000000000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000afafafaf
  | 0, 1 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000f000000000000000000000000000000000000000000000000000000000000000ffff
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x432105
  | 5, 0, 0 => 0x421675432a16643b21660321685043165543291664321656
  | 6, 0, 0 => 0x432165
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 4 0) :: stateWires n (ids >>> 4)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfe07d0000000000000000000000000000000000000000000000000000000000632ca4000000000000000000000000000000000000000000000000000000000073efa40000000000000000000000000000000000000000000000000000000001ffe0000000000000000000000000000000000000000000000000000000000001f01f8200000000000000000000000000000000000000000000000000000000018c105b000000000000000000000000000000000000000000000000000000000003cf78000000000000000000000000000000000000000000000000000000000073efa4
  | 0, 1 => 0x1f0000000000000000000000000000000000000000000000000000000000000018c000000000000000000000000000000000000000000000000000000000000018010020000000000000000000000000000000000000000000000000000000000001fff
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xd60750000000000000000000000000000000000000000000000000000000000e73ce50000000000000000000000000000000000000000000000000000000000328a000000000000000000000000000000000000000000000000000000000001ffea100000000000000000000000000000000000000000000000000000000001f29f8a0000000000000000000000000000000000000000000000000000000001cd75ff00000000000000000000000000000000000000000000000000000000013bcf7a0000000000000000000000000000000000000000000000000000000000f7bee5
  | 0, 1 => 0x1f28a000000000000000000000000000000000000000000000000000000000001cd60100000000000000000000000000000000000000000000000000000000001c0158a00000000000000000000000000000000000000000000000000000000000015ef
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 14
  | 5 => 27
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xce52c4fabf55ea1ab9aca26ca9d456f1a91a4bfda690455c5f84236f4e744b384aa0e6ac3ac89b312e3f09211f16380d142c985d07b7eebd
  | 5, 0 => 0xe39fa026ceef2316c3e14ac6b98e8086b96ea3a2b762f0afaacb8ff0a78f08149dcd98c6974979bd92b4184b8fd54a877f5dffb97f26f0c76f4ea54c62f7203634b0cb8f2c356191258c480e21a8620b202fbf561f16380d1e29e5df14e17f6b0d59fc0a09e2bbbd090d6eb4
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x1000000000000000000000061030000000006102000000000000000000000000000000000000001000000000e102000000000a103000000000a10200000000000010000000000002000000000e1030000000000001
  | 5, 0 => 0x200000000000010000000000002000000000000300000000000020000000000003000000000000100000000000000000000000002000000000000200000000000020000000000003000000000000200000000000030000000000002000000000000000000000000030000000000003000000000000200000000000030000000000002000000000000200000000000020000000000003000000000000200000000000030000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_161 roots_161 L_161 s ws hint
  | 1 => checkCutEntry dom_215 roots_215 L_215 s ws hint
  | 2 => checkCutEntry dom_239 roots_239 L_239 s ws hint
  | 3 => checkCutEntry dom_240 roots_240 L_240 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_242 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_161 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_215 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_239 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_240 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_242 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_242 goalM u ys) : RunD dom_242 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_242 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → (Z 4) i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → (Z 4) i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 7 → (Z 5) i = true := span_ok (by decide +kernel : span (Z 5) 7 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 7 → (Z 5) i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → (Z 6) i = true := z6_0
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
  scr dom_242 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_242 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_242 roots_242 goal_242 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_242 goal_242 := by
    have h0 : isConstB dom_242 goal_242 = false := by decide +kernel
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
end S_242
theorem low_242 : Lower dom_242 roots_242 goal_242 7 := S_242.noCircuit
def dom_485 : Nat := 0xffffffff00000000
def goal_485 : Nat := 0xeee0e8a000000000
def roots_485 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]
def L_485 : Nat := 8
namespace S_485
def pairsG : List (Nat × Nat) := [(36, 37), (41, 43), (33, 37), (35, 43), (38, 54), (35, 39), (38, 39), (38, 46), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (49, 53), (49, 57), (50, 54), (50, 58), (51, 55), (51, 59), (52, 53), (52, 54), (56, 57), (56, 58), (60, 61), (60, 62)]
def r1sG : List Nat := [36, 41, 33, 35, 38, 35, 38, 38, 41, 41, 42, 42, 42, 44, 44, 49, 49, 50, 50, 51, 51, 52, 52, 56, 56, 60, 60]
def r2sG : List Nat := [37, 43, 37, 43, 54, 39, 39, 46, 45, 57, 43, 46, 58, 45, 46, 53, 57, 54, 58, 55, 59, 53, 54, 57, 58, 61, 62]
def mpG : Nat := 0x7ffffff
def pool6G : List Nat := [48529661371694, 61744989157695, 66181724974653, 54031363550009, 54091559942439, 56213273198394, 44170135414069]
def xsM : List Nat := roots_485.map (· &&& dom_485)
def goalM : Nat := goal_485 &&& dom_485
def NN : Nat → Nat
  | 4 => 2
  | 5 => 14
  | 6 => 10
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xca3d7c493181ffc3
  | 5, 0 => 0xf69a2bdcbbea86bda4c1e8439cfa0b859679e0108160e3c17d2d85b37bacb04e43946bb94297b7b231d4b280198d1d17169ce0f10854d8be
  | 6, 0 => 0xd4369f1ac5ee96e7be37fa2fb433ea058ec3435879aa470957ee72523bd8c2aa37e8d827009e3c06
  | 7, 0 => 0xbe37fa2f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f00000000000000000000000000000000000000000000000000000000ff00fa0000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000ccccc8c800000000000000000000000000000000000000000000000000000000aaaaaaaa00000000
  | 0, 1 => 0xfffffafa000000000000000000000000000000000000000000000000000000000505050500000000000000000000000000000000000000000000000000000000fafafafa000000000000000000000000000000000000000000000000000000003333333300000000000000000000000000000000000000000000000000000000fffff0f0000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000005555555500000000
  | 0, 2 => 0xcc00cc000000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000033ff33ff00000000000000000000000000000000000000000000000000000000ffffaaaa000000000000000000000000000000000000000000000000000000000000555500000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x831040a4308a05
  | 5, 0, 0 => 0xca03a94031150a5010406255e4188a0601045425564188a8620c4504d8831141265c4622818831140e61b4450298831141060106061d404195075
  | 6, 0, 0 => 0x1062031404188a85010622814031140a501045025564188a0620c45a01883688a0689062281804194075
  | 7, 0, 0 => 0x4188a05
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 29
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 5 0) :: stateWires n (ids >>> 5)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x19f9f2e000000000000000000000000000000000000000000000000000000000780630200000000000000000000000000000000000000000000000000000000001e1cf80000000000000000000000000000000000000000000000000000000007ff80000000000000000000000000000000000000000000000000000000000007807f0200000000000000000000000000000000000000000000000000000000066060d100000000000000000000000000000000000000000000000000000000001e00f8000000000000000000000000000000000000000000000000000000000019832e
  | 0, 1 => 0x7ffe3ff0000000000000000000000000000000000000000000000000000000001861c00000000000000000000000000000000000000000000000000000000000679e3ff0000000000000000000000000000000000000000000000000000000007e1e3070000000000000000000000000000000000000000000000000000000007ffe0d10000000000000000000000000000000000000000000000000000000000007fff00000000000000000000000000000000000000000000000000000000007f80fd0000000000000000000000000000000000000000000000000000000007e67cd1
  | 0, 2 => 0x1c000000000000000000000000000000000000000000000000000000000000001f2e0000000000000000000000000000000000000000000000000000000007ffe3ff0000000000000000000000000000000000000000000000000000000007ff832e0000000000000000000000000000000000000000000000000000000000007cd1
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x195160a0000000000000000000000000000000000000000000000000000000007957f8a00000000000000000000000000000000000000000000000000000000055e5cfa0000000000000000000000000000000000000000000000000000000007ff92100000000000000000000000000000000000000000000000000000000007957f8a00000000000000000000000000000000000000000000000000000000066ae9f500000000000000000000000000000000000000000000000000000000055e5cfa0000000000000000000000000000000000000000000000000000000002b9a76f
  | 0, 1 => 0x7ffffff00000000000000000000000000000000000000000000000000000000010410000000000000000000000000000000000000000000000000000000000006fbefff0000000000000000000000000000000000000000000000000000000002a1a3050000000000000000000000000000000000000000000000000000000007fffbf50000000000000000000000000000000000000000000000000000000000006def00000000000000000000000000000000000000000000000000000000006a80750000000000000000000000000000000000000000000000000000000005465890
  | 0, 2 => 0x5145c8a000000000000000000000000000000000000000000000000000000000000040a0000000000000000000000000000000000000000000000000000000002eba3750000000000000000000000000000000000000000000000000000000007ffb77f0000000000000000000000000000000000000000000000000000000000004880
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
  | 4 => 9
  | 5 => 167
  | 6 => 21
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xfe805f20dc204223d341b27bc5ee96e7be37fa2fb719226cb433ea056ef4d6380f436452
  | 5, 0 => 0x69fc827b67358bf163faa34d6365354d61a2ebdf5fa50f0a5e4eb7945b7a9b4e5b0103e758d7528357ee725257a2552755275d2a4dea62284cb8fbb44c5761014c4466bb4a359032455c4e6245025efc438f5f62436637cd3f9f74df3d3de73c3bd8c2aa3afe4ed23adc933337e8d82736bcbb6c353b4ef33485ec76313552342f061eb42de4c7fd2dbe91352879bb7b26f346c0262c69372627820a25020e8a23ba810b20e7a6e21f4b03c71f3caa081d6280541cf2b0081bb7b1301a89ccf8187c0be7153c135015328dd8133e749e0b87d7e60a62315908b692ae08846f4a06e18ae8062d6bb705ecae70048b280d03cb1e610183c7bc00fff5f6009e3c06
  | 5, 1 => 0xbfed88b2be37fa2fbc20cec5bc15ff7fbc1088e0bbaad95dbb4a7542ba32d5aeb9c319b6b82bd7ebb6a84430b61d8631b433ea05b4141862b393d88ab2771baab0753b33ae66e979aa8f4c3caa42b67ba98fc860a8e9d731a716f0c1a660e524a54359cda08b3c129d8b3b339d6bddf89d5ba4a79d12e0979be856d19a54b42997f35ff795a507ef945273099350484592cc950e9249d672916b5e0b903cc33f8fa8ebf48ec343588dd615a88ba0f7c58b01ad9d8a38227889cc150984bf332e83bbcd04814050427ef232a27c9aa77f7b1a956579f9483879eb2fb879aa470978510e2977a152a771399c1b6fa636df6ded173d6bb140056b6ddfed6ae986db
  | 5, 2 => 0xff9167ddfa8717e3fa7bfd33f8500e8ff79a9562f6fbe5ccf3f266edf2de5bacf2db7d0af15e293df14dca8cf0cd2b50ee476d15edf84320ed25249fecf58e13ec3bca35e9a78c85e926ceb8e5c75c79e237ba0bdfa37c5bdf1cb288de5f2465dbed3bd2da0d8518d834293cd5167136d4369f1ad129852fd124f02bcba5b974ca328ef0c9cf5bb7c9927d75c673e01ec5ee96e7c3c729e0c08df127
  | 6, 0 => 0xec3bca35e9a78c85c3c729e0b393d88ab0753b33ae66e979aa8f4c3ca716f0c195a507ef903cc33f71399c1b63faa34d45025efc2f061eb42dbe91351f3caa08153c135015328dd80b87d7e6048b280d00fff5f6
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0xe10500000000021020000000000008000000000000800000000000020000000000005000000000000200000000000050000000002105
  | 5, 0 => 0x50000000000002000000000000400000000000040000000002102000000000000700000000000040000000000001000000000000000000000000020000000000002000000000000200000000000040000000000006000000000000200000000000060000000000008000000000000200000000000020000000000006000000000000700000000000060000000000006000000000000500000000000020000000006107000000000000400000000000050000000000008000000000000100000000000040000000000005
  | 5, 1 => 0x60000000000001000000000000200000000000040000000000003000000000000600000000000050000000000000000000000610400000000000060000000000004000000000a10200000000000050000000000000000000000210400000000000020000000000007000000000000000000000000070000000000004000000000000800000000000030000000000008000000000000400000000000050000000000000000000000000200000000000020000000000006000000000000100000000000000000000000003
  | 5, 2 => 0x21020000000000005000000000a10700000000000020000000000001000000000000700000000000030000000000002000000000000100000000000040000000000002000000000e10500000000000080000000000007000000000000700000000000000000000000000000000000000400000000000000000000000003000000000a10800000000000010000000000000000000000000200000000000060000000000000000000000000700000000000020000000000007000000000210200000000000000000000000004
  | 5, 3 => 0x50000000000002000000000000000000000000020000000000005000000000000800000000021050000000000003000000000000100000000021040000000000002000000000000600000000000020000000000006000000000000400000000000080000000000002000000000000200000000000080000000000002000000000000000000000000080000000000004000000000a1020000000000002000000000e108000000000000500000000000050000000002105000000000000000000000000020000000000003
  | 5, 4 => 0x40000000000003000000000000600000000000060000000006107000000000000200000000000080000000000005000000000610800000000000040000000000005000000000000200000000000000000000000000000000000000100000000000020000000000008000000000000600000000000080000000000007000000000000300000000000070000000000003000000000000800000000000000000000000001000000000000400000000061050000000000001000000000000800000000000070000000000006
  | 5, 5 => 0x3000000000e10500000000000020000000000005000000000000200000000000000000000002104
  | 6, 0 => 0x400000000000070000000000007000000000000500000000000040000000000007000000000000800000000000040000000000005000000000000200000000000080000000000002000000000000400000000000050000000000008000000000000200000000000020000000000002000000000000700000000000050000000000004
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_296 roots_296 L_296 s ws hint
  | 1 => checkCutEntry dom_320 roots_320 L_320 s ws hint
  | 2 => checkCutEntry dom_323 roots_323 L_323 s ws hint
  | 3 => checkCutEntry dom_440 roots_440 L_440 s ws hint
  | 4 => checkCutEntry dom_458 roots_458 L_458 s ws hint
  | 5 => checkCutEntry dom_467 roots_467 L_467 s ws hint
  | 6 => checkCutEntry dom_480 roots_480 L_480 s ws hint
  | 7 => checkCutEntry dom_482 roots_482 L_482 s ws hint
  | 8 => checkCutEntry dom_483 roots_483 L_483 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_485 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_296 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_320 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_323 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_440 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_458 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_467 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_480 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_482 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_483 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_485 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_485 goalM u ys) : RunD dom_485 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_485 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 2 → (Z 4) i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → (Z 4) i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → (Z 5) i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_12 : ∀ i, 12 ≤ i → i < 14 → (Z 5) i = true := span_ok (by decide +kernel : span (Z 5) 2 12 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 14 → (Z 5) i = true := (range_split z5_0 z5_12)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 10 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 10 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 10 → (Z 6) i = true := z6_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 1 → (Z 7) i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → (Z 7) i = true := z7_0
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
  scr dom_485 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_485 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_485 roots_485 goal_485 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_485 goal_485 := by
    have h0 : isConstB dom_485 goal_485 = false := by decide +kernel
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
end S_485
theorem low_485 : Lower dom_485 roots_485 goal_485 8 := S_485.noCircuit
def dom_566 : Nat := 0xffff0000ffff
def goal_566 : Nat := 0xe8a00000e0a0
def roots_566 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]
def L_566 : Nat := 6
theorem low_566 : Lower dom_566 roots_566 goal_566 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff00, 6, 14), (0xffff00000000, 11, 43)] (by decide +kernel) (by decide +kernel) low_296
def dom_647 : Nat := 0xffff0000ffff0000
def goal_647 : Nat := 0xeee00000ece00000
def roots_647 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]
def L_647 : Nat := 5
theorem low_647 : Lower dom_647 roots_647 goal_647 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffff000000000000, 25, 57)] (by decide +kernel) (by decide +kernel) low_161
def dom_701 : Nat := 0xff00ff00ff00ff00
def goal_701 : Nat := 0xee00e800ec00e000
def roots_701 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]
def L_701 : Nat := 7
namespace S_701
def pairsG : List (Nat × Nat) := [(12, 13), (12, 14), (9, 13), (10, 26), (11, 43), (10, 14), (11, 15), (11, 27), (24, 26), (25, 27), (25, 29), (25, 57), (28, 29), (28, 30), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (56, 57), (56, 58), (60, 61), (60, 62)]
def r1sG : List Nat := [12, 12, 9, 10, 11, 10, 11, 11, 24, 25, 25, 25, 28, 28, 41, 41, 41, 42, 42, 42, 44, 44, 56, 56, 60, 60]
def r2sG : List Nat := [13, 14, 13, 26, 43, 14, 15, 27, 26, 27, 29, 57, 29, 30, 43, 45, 57, 43, 46, 58, 45, 46, 57, 58, 61, 62]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [46421017041465, 9943538022942, 66147734724139]
def xsM : List Nat := roots_701.map (· &&& dom_701)
def goalM : Nat := goal_701 &&& dom_701
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x90ae1cda39952a31
  | 6, 0 => 0xd9129671
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc00cc00cc00cc00000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000aa00aa00aa00aa000000000000000000000000000000000000000000000000003300330033003300
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8d521846885
  | 6, 0, 0 => 0x46a95
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe00f80000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003c03f000000000000000000000000000000000000000000000000000000000003303003000000000000000000000000000000000000000000000000000000000001ced40000000000000000000000000000000000000000000000000000000003f1ff07
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2ae63fa0000000000000000000000000000000000000000000000000000000003ffc8100000000000000000000000000000000000000000000000000000000003c93f88000000000000000000000000000000000000000000000000000000000334b467000000000000000000000000000000000000000000000000000000000153ded50000000000000000000000000000000000000000000000000000000001519c05
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 3
  | 5 => 32
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xd9129671c07b98784ba33a5a
  | 5, 0 => 0xf4bf4b31eb20a69aea8598c9d9129671ce6e74ccc570211ebd718b95a2d38208738457f572c90e946eb618ee6e69792d6c570b8d5ff904b85f37eb865e4c709a5b8408934dfe97dd4bdd62d04b88a9024afea8ad48992d77478019d03a17464a203fcfad1e8c6bf619f5616b135e80ec0fa4afb40ede84b00d66d9a706cd6aa0
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x61000000000002103
  | 5, 0 => 0x10000000000003000000000000200000000000000000000000000000000000000200000000000000000000000001000000000000100000000000000000000000001000000000000100000000000000000000000000000000000000300000000000020000000000000000000000000100000000000020000000000000000000000000300000000000000000000000002000000000000000000000000030000000000002000000000000200000000000010000000000001000000000000000000000000000000000000003
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_458 roots_458 L_458 s ws hint
  | 1 => checkCutEntry dom_539 roots_539 L_539 s ws hint
  | 2 => checkCutEntry dom_683 roots_683 L_683 s ws hint
  | 3 => checkCutEntry dom_700 roots_700 L_700 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_701 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_458 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_539 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_683 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_700 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_701 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_701 goalM u ys) : RunD dom_701 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_701 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 2 → (Z 5) i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 2 → (Z 5) i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → (Z 6) i = true := z6_0
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
  scr dom_701 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_701 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_701 roots_701 goal_701 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_701 goal_701 := by
    have h0 : isConstB dom_701 goal_701 = false := by decide +kernel
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
end S_701
theorem low_701 : Lower dom_701 roots_701 goal_701 7 := S_701.noCircuit
def dom_710 : Nat := 0xf0f0f0f0f0f0f0f
def goal_710 : Nat := 0xe0008000c000000
def roots_710 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def L_710 : Nat := 6
theorem low_710 : Lower dom_710 roots_710 goal_710 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f00, 18, 26), (0xf0f0f0f00000000, 11, 43)] (by decide +kernel) (by decide +kernel) low_440
def dom_725 : Nat := 0xcccccccccccccccc
def goal_725 : Nat := 0xccc0c880ccc0c080
def roots_725 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def L_725 : Nat := 7
namespace S_725
def pairsG : List (Nat × Nat) := [(6, 7), (3, 7), (6, 14), (6, 22), (11, 43), (10, 14), (10, 26), (11, 15), (11, 27), (18, 22), (18, 26), (19, 23), (19, 27), (35, 39), (35, 43), (38, 39), (38, 46), (38, 54), (42, 43), (42, 46), (42, 58), (50, 54), (50, 58), (51, 55), (51, 59)]
def r1sG : List Nat := [6, 3, 6, 6, 11, 10, 10, 11, 11, 18, 18, 19, 19, 35, 35, 38, 38, 38, 42, 42, 42, 50, 50, 51, 51]
def r2sG : List Nat := [7, 7, 14, 22, 43, 14, 26, 15, 27, 22, 26, 23, 27, 39, 43, 39, 46, 54, 43, 46, 58, 54, 58, 55, 59]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [46343019501319, 19834749194030, 6640070231862, 11072613329671, 41790335555342, 56226259283719, 55139497807418, 20006530923066, 3518421146382]
def xsM : List Nat := roots_725.map (· &&& dom_725)
def goalM : Nat := goal_725 &&& dom_725
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 6
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe672a5c8
  | 4, 0 => 0xe1ad77a84c198842275312fb
  | 5, 0 => 0xec29f245dad0a36db630039aa15afe1f9510ff9c47545a22
  | 6, 0 => 0xd4898dc3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccc0000cccc0000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000c888c888c888c888000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000ccccc000ccccc000000000000000000000000000000000000000000000000000ccc0ccc0ccc0ccc00000000000000000000000000000000000000000000000008888888888888888
  | 0, 1 => 0xcc00cc00cc00cc0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c000000000000000000000000000000000000000000000000c000c000c000c000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x32104
  | 4, 0, 0 => 0x371805326405376545
  | 5, 0, 0 => 0x37640a603760953764096371640603740a53764806
  | 6, 0, 0 => 0x376405
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 4 0) :: stateWires n (ids >>> 4)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1e01e0000000000000000000000000000000000000000000000000000000000001c01f00000000000000000000000000000000000000000000000000000000001807992000000000000000000000000000000000000000000000000000000000003800d0000000000000000000000000000000000000000000000000000000001ffe0000000000000000000000000000000000000000000000000000000000001e01e0000000000000000000000000000000000000000000000000000000000001f81fd0000000000000000000000000000000000000000000000000000000001807992
  | 0, 1 => 0x1e3fe0f0000000000000000000000000000000000000000000000000000000001fc7ff20000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1f21f4800000000000000000000000000000000000000000000000000000000015d55f400000000000000000000000000000000000000000000000000000000018df9b70000000000000000000000000000000000000000000000000000000000abaaaf0000000000000000000000000000000000000000000000000000000001ffe0100000000000000000000000000000000000000000000000000000000001fb1fec0000000000000000000000000000000000000000000000000000000001ffffff000000000000000000000000000000000000000000000000000000000184f993
  | 0, 1 => 0xa2aa0b000000000000000000000000000000000000000000000000000000000154555000000000000000000000000000000000000000000000000000000000000900a4
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 10
  | 5 => 30
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xf7763ef3f1c1761bd4898dc3cd2ecae8c7075548a9061c5f9e09b9f433dc19eb10c168bc0161202e
  | 5, 0 => 0xd4898dc3c1337531b4ba76d7a91c36d2a5998c2797ed9c9d89e23c65878b2faf846bc21d83b557a8809495a07d693e0b782ae7217120178b6e4005e66a2d1040680c43ab6699e4165d95387b5aaee2d85751dfd55039f6e34557b24840d9ae5536eecd1a312306392b8da6e428382afe0828a3f503333477
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0xa1000000000000000000000000000000000000000020000000000002000000000000000000000000010000000000003000000000a100000000000a102
  | 5, 0 => 0x10000000000003000000000000000000000000000000000000001000000000000100000000000010000000000002000000000000000000000000030000000000000000000000000300000000000000000000000003000000000000300000000000010000000000001000000000000000000000000000000000000002000000000000000000000000030000000000000000000000000300000000000030000000000003
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 6 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_239 roots_239 L_239 s ws hint
  | 1 => checkCutEntry dom_480 roots_480 L_480 s ws hint
  | 2 => checkCutEntry dom_482 roots_482 L_482 s ws hint
  | 3 => checkCutEntry dom_563 roots_563 L_563 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_725 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_239 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_480 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_482 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_563 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_725 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_725 goalM u ys) : RunD dom_725 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_725 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → (Z 3) i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → (Z 4) i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → (Z 4) i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 6 → (Z 5) i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 6 → (Z 5) i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → (Z 6) i = true := z6_0
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
  scr dom_725 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_725 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_725 roots_725 goal_725 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_725 goal_725 := by
    have h0 : isConstB dom_725 goal_725 = false := by decide +kernel
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
end S_725
theorem low_725 : Lower dom_725 roots_725 goal_725 7 := S_725.noCircuit
def dom_727 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_727 : Nat := 0xaaa0a8a0a8a0a0a0
def roots_727 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def L_727 : Nat := 6
theorem low_727 : Lower dom_727 roots_727 goal_727 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a0a0a0a0a0, 1, 5), (0xaa00aa00aa00aa00, 19, 27)] (by decide +kernel) (by decide +kernel) low_682
def dom_728 : Nat := 0xffffffffffffffff
def goal_728 : Nat := 0xeee0e8a0ece0e0a0
def roots_728 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def L_728 : Nat := 10
namespace S_728
def pairsG : List (Nat × Nat) := [(4, 5), (12, 14), (1, 5), (6, 14), (6, 22), (11, 43), (3, 7), (6, 7), (9, 13), (10, 14), (10, 26), (11, 15), (11, 27), (12, 13), (17, 21), (18, 22), (18, 26), (19, 23), (19, 27), (20, 21), (20, 22), (24, 26), (25, 27), (25, 29), (25, 57), (28, 29), (28, 30), (33, 37), (35, 39), (35, 43), (36, 37), (38, 39), (38, 46), (38, 54), (41, 43), (41, 45), (41, 57), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (49, 53), (49, 57), (50, 54), (50, 58), (51, 55), (51, 59)]
def r1sG : List Nat := [4, 12, 1, 6, 6, 11, 3, 6, 9, 10, 10, 11, 11, 12, 17, 18, 18, 19, 19, 20, 20, 24, 25, 25, 25, 28, 28, 33, 35, 35, 36, 38, 38, 38, 41, 41, 41, 42, 42, 42, 44, 44, 49, 49, 50, 50, 51, 51]
def r2sG : List Nat := [5, 14, 5, 14, 22, 43, 7, 7, 13, 14, 26, 15, 27, 13, 21, 22, 26, 23, 27, 21, 22, 26, 27, 29, 57, 29, 30, 37, 39, 43, 37, 39, 46, 54, 43, 45, 57, 43, 46, 58, 45, 46, 53, 57, 54, 58, 55, 59]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := [44152735337787, 52828973645338, 52884201082133, 48520987741485, 11219260226061, 39720431719941, 41962687839006, 82611942935, 41863365922575, 26629368585742, 66159695437614, 48426396618523, 46317129577791, 8977087141399, 27527036739098, 27706870410010, 45256275201550, 13271654275638, 9904498030110, 20976789566749, 36460030276918, 9015305902853, 2414075062046]
def xsM : List Nat := roots_728.map (· &&& dom_728)
def goalM : Nat := goal_728 &&& dom_728
def NN : Nat → Nat
  | 3 => 2
  | 4 => 7
  | 5 => 24
  | 6 => 116
  | 7 => 102
  | 8 => 23
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe650416d0080f41a
  | 4, 0 => 0xff8e6966e20d6a63c29dfdc6a86d4b197bc8d8d96008cc3919bf1c13
  | 5, 0 => 0xfb4b925cf47c5779eec57511dd19b093dbdc25bfd71b981bd3e4c6c4c1dac15ec1ab7312bc98de84bb538086b646c18ca42a740fa2ff17439b2b281974a158dd70d7f85d5359f735463042e542432a0528d26f9821c3b6ed0b0e616000f556f4
  | 6, 0 => 0x8ba4dddf8a7a9db88a7535398a16205689cec5d189aec08a87e29fff8277261f7fa4ca357edde7257d6e825a788c2ff5771a8ec07583edf974c30ad371fe46de71e3eefb717d774a70e541f06e4de9556cd73001689eda7663aa72a860b0f6125f66e6445e74deda5dadfbca5c4539315aef23a75a4238f356803d4a5454029e52afc25752267abf5203ea7051eea6ae51bb968e50c3a0934d71a1d848fae8683c73557f39ae918a35354d8630d3ff152a2d2ac7280c0df326a60199233bab091f9748ee1e69adb71acb72991a337eed18917f941673e5761293ecd81182c6e910d6ef020eeac9300dba7f720d03172405a7c76302f2e5b202a6975900bd6281
  | 6, 1 => 0xffcf6f8ffd224669f6b5bc52f5c605cbf22dc195f1e87d9df07c42f8f059c014efd9a278efa703a7ebe2db01e37cbfd9e2a5fae3db94eee6db5796e8db18e957d3304b68d2b65212d16ca0becfa9f353cadbbbf8c89b3aa8c88c5676c7c57366c6af14d6be6b7a3abd689c08bcf80b4bbc7607b4bc6af28fb60a28a2ae7a07f8adce3011a76b4f4da6bf7766a57e47e7a4d35194a09a887c9fd89fc89dd376b29c5e759b9aeb76b19a9a447299bc1b50998bcfd1938c4828932e323991e192369180cfe59124d9018e1d627c8bc200e8
  | 7, 0 => 0x9839f57d956af0e494ea215094acc9528c0b847c8b9a7c8c8b3625d88ac1d328878389bf852f6aa284fccbd183b31a7d824ebd7681f06d128128f3f37b7c8fb0764d3db571e3fb216ad5427663ff7f4760c081b76014a9d06013f4555a9a336252e1023b4cae6cf64c8364a34c02950f4b36c4a04a1cb69d47c09368477294e644fa104943cfd022436b52c04323f83b4303f2f4412582f03d7b1e3a3cc117773c79d3023c153f903a2919be2ff00c9c2ee5f83b2b5379482ad2a9b4225227cd21f40ce0209463141f505e561cc1ea541ae5543518bc18ae1780280517416487144456110de1f81f0d359d660a18d2fd07540f0806d33f74046cf47e0402104d
  | 7, 1 => 0xfdf4a2a0f3caa704f303c3f4ed6973f8ec663512ebc5bbfbeb406b8fe9f6ba3be9a9cac8e9a376e3e17cf3aade9c7c68dd44ebefdcf66048dae1e332daaf4034d8ec7b58d749a837d6363344d111535acedaf033ce16f6e3cccd458fcad7f953ca2c216cc9ad816cc6579413c629c73fc4da6697bbfbc9c3b5e0fc76b4ed1118af359018a8fc3611a37ea8d1a258df4e9e2954c09b237b57
  | 8, 0 => 0xf9554771f61649e1f56a71fad43a869fc68acfd0c43bc065c0a94172c02871deb749d50ab03b1c5f9437159c8ff96af68f8b65ae8302b3d66e42438244efaef6448b58423e51fe3b3d084ce7242a74e0196926bf17a485a0167ebc1d
  | 9, 0 => 0x69904ec9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfafafafaf0f0f0f0000000000000000000000000000000000000000000000000fffffafafffff0f0000000000000000000000000000000000000000000000000ff00fa00ff00f000000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000fafa0000f0f00000000000000000000000000000000000000000000000000000ccccc8c8ccccc0c0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0
  | 0, 1 => 0xff00f000ff00f0000000000000000000000000000000000000000000000000003333333333333333000000000000000000000000000000000000000000000000050505050f0f0f0f000000000000000000000000000000000000000000000000ee00ea00cc00c000000000000000000000000000000000000000000000000000fe00fa00fc00f000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000ffff0000ffff0000
  | 0, 2 => 0xeeeeeaeaccccc0c0000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000111155553333ffff000000000000000000000000000000000000000000000000fefefafafcfcf0f00000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000eeeeaaaacccc00000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000ff00ff0000000000
  | 0, 3 => 0xf0f00f0ff0f00f0f000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000cc00c000cc00c000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000fcf0fcf0fcf0fcf0000000000000000000000000000000000000000000000000ccccc0c0ccccc0c0000000000000000000000000000000000000000000000000fff0fff0f0f0f0f000000000000000000000000000000000000000000000000033ff33ff33ff33ff
  | 0, 4 => 0xaaaaaaaa0000000000000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000fcfcf0f0fcfcf0f0000000000000000000000000000000000000000000000000ffffcc00ffffcc0000000000000000000000000000000000000000000000000000ff00ff00ff00ff000000000000000000000000000000000000000000000000555555555555555500000000000000000000000000000000000000000000000000ff0fff00ff0fff
  | 0, 5 => 0xf8f8f8f8f8f8f8f8000000000000000000000000000000000000000000000000f0f0fafaf0f0fafa0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c000000000000000000000000000000000000000000000000ffff8888ffff8888000000000000000000000000000000000000000000000000ffff0c0cffff0c0c000000000000000000000000000000000000000000000000fffff000fffff000000000000000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000000f0f0f0f00000000
  | 0, 6 => 0x5050f0f05050f0f000000000000000000000000000000000000000000000000373737373737373700000000000000000000000000000000000000000000000000005f5f00005f5f0000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000ff008800ff0088000000000000000000000000000000000000000000000000000707070707070707000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c8000000000000000000000000000000000000000000000000fafafafafafafafa
  | 0, 7 => 0xf0f00000f0f00000000000000000000000000000000000000000000000000000ccccc000ccccc00000000000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000003030f0f03030f0f000000000000000000000000000000000000000000000000030f030f030f030f000000000000000000000000000000000000000000000000f3fff3fff3fff3ff000000000000000000000000000000000000000000000000c8c8c8c8c0c0c0c00000000000000000000000000000000000000000000000003333777733337777
  | 0, 8 => 0xaaaa0000aaaa000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000000000000000000000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000aaa0aaa0a0a0a0a0000000000000000000000000000000000000000000000000000f0f0f000f0f0f00000000000000000000000000000000000000000000000033333f3f33333f3f
  | 0, 9 => 0xeeeeaaaaeeeeaaaa000000000000000000000000000000000000000000000000ffffc0c0ffffc0c0000000000000000000000000000000000000000000000000cccc8888cccc8888000000000000000000000000000000000000000000000000fafaf0f0fafaf0f0000000000000000000000000000000000000000000000000ffffa0a0ffffa0a0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000aa00aa00aa00aa000000000000000000000000000000000000000000000000000000f0f00000f0f0
  | 0, 10 => 0xfff0f0f0fff0f0f0000000000000000000000000000000000000000000000000aaaaa0a0aaaaa0a0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa08200406080804
  | 4, 0, 0 => 0x1410a0825430304100288061c0805101438400a2050c0825440b14104a8304280895
  | 5, 0, 0 => 0x101438a0825840324104916104051a3c25841014104a060c201870801801c067c2095104078a12398403145c2096000c384004d440328282096100c50412558b0314482096100c5091c35818a08246936382079b082584030e082006
  | 5, 0, 1 => 0xc0c10a082584030e1000d6106450412618e08066cd096100c38a022584030e10013610405043a258008061000d5
  | 6, 0, 0 => 0xc80412449b1c100c5041301ce08062820976e2018704282097007040a4239131c100c5041305cb0806405091ce00e0a08851136000c5044e849b1c100c5044299c4030e282091ae20184129c893738ac40308248b80380c50412d58003202848e26c7040314104b27
  | 6, 0, 1 => 0x38205043425139c542018a1239c4031410d094ee0040314482096382018f14247380202821e124d8008203c50412c7040374282097002080a0824c31c0628209304dc410362821e12e704030868491700004030e1002a310405043c25c008064048e22c7040360100137
  | 6, 0, 2 => 0x382018a34784b9c2c0c209224dce08062823e12e00419062848e6382018a08250380380c48e224d8e0314112894ce584101410f097380c50462249b9c100d2041245ce08061049822e7118806282217380c52912389b9c100c50412e1c01c06282097ac70b0308944917
  | 6, 0, 3 => 0xc5044e009b00382848e444d8e08062821d12e0018714104936000c5094e389b000640504424d8e08062848e4ce70b08066c2097100d20a08253b8806282094e61ce08062820978e70b0806247117100c5044e849b960628225129dc0082010f0922c701843c248937
  | 6, 0, 4 => 0x382018412453380100c48e22a18e081e2821e12e0000806282425382018a0825b39c100c5043485ce2c100c20922e58403142538e7000c20922a09b08202821e1261c18a08784a726e7018a0825693700701bf08253300100c38a12398e035e2820926e701ae14104937
  | 6, 0, 5 => 0x100c80a08684b8014104a7444d8e08069050442e704031411098738205041289339c2c0c5044a85c308061c50412e00e036010013638b040a0825138010645043c258e0806282096ee00e0812388a2600201894e388b003810491444d8003082539126c715031411f097
  | 6, 0, 6 => 0x388c40308248b880628227004dc4030e2823912e2018714104937100c225129c8b80380c221224d801c540c5091cc7040366282097100c2251245439c2c0c504424dce03362820926e00403141048d6100c38a08944b80380c5211c4d8e03142471126e0040a129c7226
  | 6, 0, 7 => 0x100c20922a09b9c100c5256225c01c100d08e22c7040314684b47
  | 7, 0, 0 => 0xe080624711600004190628209638201b01411289838584031410d0980000e03082489360070403141188970000e1606fc209638584031410f098007040314a448e70070b08062848e7007018a5210493700004101410f096007018a087849370070b031410493700715080628209700704031e282097
  | 7, 0, 1 => 0x403141138060000e081424722600004030e2820960000403142538e6000040320282216382018a082401380000e44062824660000e0a0825113638201b014104938000018a08253936007040314104a670071608062820970070403082631170070403087849170070b0806104917007270806282097
  | 7, 0, 2 => 0xe0806c020060072208062848e70072203141049370070403089449170000e0808248a26000040308253916007018a0825093738584031e282098000040308248a860070b0814104a27002018a08784a77005840314104a77007040314104ad7382018a0878498800725880628209700704035e282097
  | 7, 0, 3 => 0x704031412689700704031410f2170070b08062822170070403362820970000e08062908e6007018a09284937007018a0825a137007040314247117007118806282097002018a08944a770000e0314110936007018a08248937007040386104917000040a08253a26007040308248937007018a08249c77
  | 7, 0, 4 => 0x382018a089449180000e0814110a26000040314113a16007018a08264937382018a0825093800704031410d0970058403202820970000403202848e6007040308248ad700001901410493600704030825a1170000e080611091600201c314104a77002018a082539370000e2a06282096385840314104b48
  | 7, 0, 5 => 0x7040314110937382018a082489380070b03141128970070451062820970000e4b06282096388c4031410f0980070403602848e7007040398282097007018a082401370000e08062a7846000040320104916385840314104d0800701b014104937007040a0825a227007040308248c57007040314112a17
  | 7, 0, 6 => 0xe0314247136007040348282097007040314104987007018a08249c87007040386282217382019b1410f098
  | 8, 0, 0 => 0x385840314104b80382018a1239801c062820926c7040314104807382018a7e104b9c100d80a0825ce08062820992e0040320282096382018a09284b9c100c50412d1c01c100c50442c7040314104917391040314104b9c100c5041285ce08070c50412e7040314104937
  | 8, 0, 1 => 0x1c100c5044a25c01c102820944c0040314104a76007040308248b1c100c5290825ce0806282098ce704031410f097
  | 9, 0, 0 => 0xe0806282096
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
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 7 0) :: stateWires n (ids >>> 7)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xcf1ffe18209b0000000000000000000000000000000000000000000000000000ff1fffffe09b0000000000000000000000000000000000000000000000000000031c07e020020000000000000000000000000000000000000000000000000000f0e3b0079ef8000000000000000000000000000000000000000000000000000003fc07e03f220000000000000000000000000000000000000000000000000000cc00061800000000000000000000000000000000000000000000000000000000f003b00780980000000000000000000000000000000000000000000000000000000000000000
  | 0, 1 => 0x30007e0200200000000000000000000000000000000000000000000000000000f1c4ff86107000000000000000000000000000000000000000000000000000030e001e7df640000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000031c0600200200000000000000000000000000000000000000000000000000000303c618209b0000000000000000000000000000000000000000000000000000cc1c39c659640000000000000000000000000000000000000000000000000000fc0007ffc000
  | 0, 2 => 0xfc1fb80780980000000000000000000000000000000000000000000000000000ff03c7ffe09b000000000000000000000000000000000000000000000000000003e3c7f87fff0000000000000000000000000000000000000000000000000000ff1ffe1fa09b000000000000000000000000000000000000000000000000000003fff8003fff0000000000000000000000000000000000000000000000000000fc1c380780000000000000000000000000000000000000000000000000000000fcfc39e7df64000000000000000000000000000000000000000000000000000003fc00000000
  | 0, 3 => 0xfc3e181f64000000000000000000000000000000000000000000000000000000e000001e2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffff8000000000000000000000000000000000000000000000000000000000003e3c6183ebb0000000000000000000000000000000000000000000000000000f00380078098000000000000000000000000000000000000000000000000000003ffc618209b0000000000000000000000000000000000000000000000000000ff1fffffe1df
  | 0, 4 => 0xcc1c38000000000000000000000000000000000000000000000000000000000000fc38001f640000000000000000000000000000000000000000000000000000f000000780000000000000000000000000000000000000000000000000000000f303c61fa09b0000000000000000000000000000000000000000000000000000fce007ffde200000000000000000000000000000000000000000000000000000fc03f81fc0dd000000000000000000000000000000000000000000000000000033e3c639a69b0000000000000000000000000000000000000000000000000000fcfff81fdffd
  | 0, 5 => 0xc303f61e38fb0000000000000000000000000000000000000000000000000000031ffe1839ff0000000000000000000000000000000000000000000000000000f0e030079e600000000000000000000000000000000000000000000000000000fc0037ffd8600000000000000000000000000000000000000000000000000000fce037ffde600000000000000000000000000000000000000000000000000000ff0007ffe00200000000000000000000000000000000000000000000000000000300060020020000000000000000000000000000000000000000000000000000fcfc38000000
  | 0, 6 => 0x30fc38219f6400000000000000000000000000000000000000000000000000003ffc4ff9e707000000000000000000000000000000000000000000000000000003fff8003fff0000000000000000000000000000000000000000000000000000c000300618600000000000000000000000000000000000000000000000000000000007e0182000000000000000000000000000000000000000000000000000003cfc09e1c7040000000000000000000000000000000000000000000000000000c003b00618f80000000000000000000000000000000000000000000000000000cf1fffde79ff
  | 0, 7 => 0x61800000000000000000000000000000000000000000000000000000000f00000078000000000000000000000000000000000000000000000000000000000fff8001ffd00000000000000000000000000000000000000000000000000000cfc39e05f640000000000000000000000000000000000000000000000000000fc1c39e7c1440000000000000000000000000000000000000000000000000000ff1fffffe1df0000000000000000000000000000000000000000000000000000c003b000009800000000000000000000000000000000000000000000000000000fffcff8679f
  | 0, 8 => 0x1c380019640000000000000000000000000000000000000000000000000000cc0001c640000000000000000000000000000000000000000000000000000000fc0001e7c0000000000000000000000000000000000000000000000000000000fc1c3fffd9640000000000000000000000000000000000000000000000000000000007e000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000fcfc3807df6400000000000000000000000000000000000000000000000000000ffc7ff87f67
  | 0, 9 => 0xfc1c39c7d9640000000000000000000000000000000000000000000000000000fc0387ffc0980000000000000000000000000000000000000000000000000000f000300798600000000000000000000000000000000000000000000000000000cf03c7de609b0000000000000000000000000000000000000000000000000000fc0007ffc00000000000000000000000000000000000000000000000000000000003800000980000000000000000000000000000000000000000000000000000001c01c0192000000000000000000000000000000000000000000000000000000303c000209b
  | 0, 10 => 0x303c7f8209b0000000000000000000000000000000000000000000000000000cc0001c64000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xdf7fff9aebff0000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000abfd27e53f2a0000000000000000000000000000000000000000000000000000f2e7b4779efa0000000000000000000000000000000000000000000000000000abfd27e53f2a0000000000000000000000000000000000000000000000000000dc12079ac0100000000000000000000000000000000000000000000000000000f2e7b4779efa00000000000000000000000000000000000000000000000000004508da8a69c5
  | 0, 1 => 0xabd907e53f0a00000000000000000000000000000000000000000000000000000d184b88610500000000000000000000000000000000000000000000000000002080006514000000000000000000000000000000000000000000000000000000abfd25651e2a0000000000000000000000000000000000000000000000000000abfd27e53f2a0000000000000000000000000000000000000000000000000000574bde9aebdf0000000000000000000000000000000000000000000000000000cd3cfbce79e50000000000000000000000000000000000000000000000000000fc9207ffd410
  | 0, 2 => 0xfffffd779efa0000000000000000000000000000000000000000000000000000ffdbdfffffdf0000000000000000000000000000000000000000000000000000024102886bcf0000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000036df8002bef0000000000000000000000000000000000000000000000000000fdbefd7794300000000000000000000000000000000000000000000000000000a8b4216514200000000000000000000000000000000000000000000000000000abfd21000020
  | 0, 3 => 0x5426269ac0300000000000000000000000000000000000000000000000000000a2e524651e2a0000000000000000000000000000000000000000000000000000a2c104651e0a0000000000000000000000000000000000000000000000000000fffff90000200000000000000000000000000000000000000000000000000000f7effeffffff0000000000000000000000000000000000000000000000000000f2c394779eda0000000000000000000000000000000000000000000000000000ffffff9aebff00000000000000000000000000000000000000000000000000005d1adb9ae1d5
  | 0, 4 => 0xcd3cf900002000000000000000000000000000000000000000000000000000000024200000200000000000000000000000000000000000000000000000000000f082047794100000000000000000000000000000000000000000000000000000f7cbdeffffdf0000000000000000000000000000000000000000000000000000fef727ffde3a00000000000000000000000000000000000000000000000000005402d81ac0d5000000000000000000000000000000000000000000000000000032c30431861a00000000000000000000000000000000000000000000000000005426f81ac0f5
  | 0, 5 => 0xd76ffedefbff0000000000000000000000000000000000000000000000000000576ffe9aebff0000000000000000000000000000000000000000000000000000a0a4206514200000000000000000000000000000000000000000000000000000fcb6b7ffdcf00000000000000000000000000000000000000000000000000000fcb627ffd4300000000000000000000000000000000000000000000000000000ffdb07ffff1a0000000000000000000000000000000000000000000000000000034906802b0a0000000000000000000000000000000000000000000000000000a8b421000020
  | 0, 6 => 0x20a42021042000000000000000000000000000000000000000000000000000002d984ba96505000000000000000000000000000000000000000000000000000002652000022a0000000000000000000000000000000000000000000000000000c024b04618e00000000000000000000000000000000000000000000000000000a8b427e51c2000000000000000000000000000000000000000000000000000002890012104000000000000000000000000000000000000000000000000000000d267b4569afa0000000000000000000000000000000000000000000000000000df7fffdefbff
  | 0, 7 => 0x5402069ac0100000000000000000000000000000000000000000000000000000f2c304779e1a00000000000000000000000000000000000000000000000000000024f80000e50000000000000000000000000000000000000000000000000000083421000020000000000000000000000000000000000000000000000000000008100100000000000000000000000000000000000000000000000000000000005f5bdf9aebdf0000000000000000000000000000000000000000000000000000d267b4128afa00000000000000000000000000000000000000000000000000000f594b88630f
  | 0, 8 => 0x12cf80029e50000000000000000000000000000000000000000000000000000cc1003ce50000000000000000000000000000000000000000000000000000000a890016514000000000000000000000000000000000000000000000000000000fdbefffffdf50000000000000000000000000000000000000000000000000000a89007e514000000000000000000000000000000000000000000000000000000cd3cfb8a69e5000000000000000000000000000000000000000000000000000000242000002000000000000000000000000000000000000000000000000000000d3c6b886125
  | 0, 9 => 0xfdbefffffdf50000000000000000000000000000000000000000000000000000fed397ffdeda0000000000000000000000000000000000000000000000000000f0a6b4779cf00000000000000000000000000000000000000000000000000000df5bdfdefbdf0000000000000000000000000000000000000000000000000000fd9adffffdd50000000000000000000000000000000000000000000000000000524394128ada0000000000000000000000000000000000000000000000000000893c23c4392000000000000000000000000000000000000000000000000000000349d8002bcf
  | 0, 10 => 0xffdbdfffffdf0000000000000000000000000000000000000000000000000000cd18dbce79c5
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 82 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem wireD_ok_chk_0 : ∀ i, 0 ≤ i → i < 48 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 48 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem wireD_ok_chk_48 : ∀ i, 48 ≤ i → i < 82 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 34 48 = true)
private theorem wireD_ok_chk : ∀ i, 0 ≤ i → i < 82 → wireDOK i = true := (range_split wireD_ok_chk_0 wireD_ok_chk_48)
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 82 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := wireD_ok_chk i (Nat.zero_le i) hi
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 82 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 4 => 20
  | 5 => 304
  | 6 => 2048
  | 7 => 1053
  | 8 => 23
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xffcb1ad6ef3bf3e6e4af8163c6865386c307c926aa923659a297671199a52b508058ee406c0488af5daffef75beeb90441be0657403ebce739c7663f2a2d2ac727b514c521c62d10140a922709f052a1
  | 5, 0 => 0x39aa062d37ad796c379f5ebe35f050a635adfb6134cf7a6e34a551ac338c6264314e68822f89bd162ee197fb2d986f5a2d70f9822b8b786c2b35f5912aa887a62a5971ca29aeb1b828f6610f27152a6526b05620268ec7cd24c87b53248397f1246b699423457bf52233514a20d9833a209463141ef7681d1dfb2dc51bfea7ab1bae5cf11b5287af18ec651218be9d6e17a479a21780280517435a49168abf901603466915aeb66a14c12eb1149fa44612e8e7c01264421b11376c46113504f10f27dc140d971e470c340a220a28b39b0a2478d00a18d2fd0a08d968087dae88085d6f6607a4da6b044180f70374110c03160e380315c025006f48570052fe09
  | 5, 1 => 0x708ed63d706c535970504f926c73eabf6c20c07b6bf0de9e6b0ff5c16a87b09369eba2ff69904ec9689b96dd67c80e9c679ee46f64c0222e6308816562d1b0bc627aa4146269ca9661c37a1160814b556014a9d05f7fb2015f08e9625e2b8f705c1846225b3232035af5d8b95a3d911258aadcd156dde6bc55e63f975578adb2544b4bc953eff13d5342dead52fdd98c52e1023b518ce16f4e8165a84bef20e14be7ad894ae3c8134ac1e4064a22f8474974ac9c46ca17d24656788c4628be4b45c3212d45046b6b44fa10494459c9ea43d90261436b52c04323f83b4303f2f4417a81cf40f7c7503f313b653d7b2f4d3cca49b63c153f903c00e01c3b5c06d4
  | 5, 2 => 0xa8b4ef14a8912650a6660a9fa62e9bf0a49f3430a28a65e0a219cfa8a1c82831a17e44fda0d1204aa0758ca19fa82cef9e7d26d49e2954c09cf1e9e29bbcd0b39a46123299bf3dc79960aa75995c997099293efa98997444975b82aa96f5fb2296f05b2496ebc7e0941c6f6e912ca2018ecd08e38dcd12b78d68f89f8c6373d58a2cdbc088d2564387755c3683204da2820aa7cf81f06d1281461d7080c435d37ff6e30b7f643cda7f615f297f2e06107c5cfb907bf256287ae71a677a92b22e7a1c1f65799a7b267932d6df79310cb577e6b10877bcfe3276f2fac2765a6c92764d3db574df3a837338cc527335f1197283d8ef71f5890d71c88e76714b74d0
  | 5, 3 => 0xddd4aea8db02b3ceda6c8956da67c72ed9a5bea5d95e6420d8ec7b58d8950667d8666e19d841619ed73e1affd44ea065d403a9c8d3ca8f6fd27a978ad1adc1ced1420149d1339b3bcfddbcc0cc6c32accaa044d6ca2c216cc87a3d85c6a42577c572457ac45508aec43c92dfc3fff3a6c30d9819c1aa0004c1898678c10d8157c0eb8503bfa34288bc478134bbfbc9c3bb385cb2b9f2236fb9a1b450b81bd9aeb808ac39b6b325dfb6231338b53b688ab4ed1118b48a442bb47210d2b3b5a2cdb399b234b099fba9afda98c9aea18d32adca12acadb0f589ad798a0eacf57cd9ac0ef96bab511c32ab45aaa9ab0f3eecaa354f5caa2f2600aa278b53a9795cd5
  | 5, 4 => 0xffc3c16aff8fa52eff63888bfe3677c4fda8ce6afda01cccfc681c7efb57a362fb5091d8facdf7b9f61c2815f4ec695bf4c0582cf46e81fff46b99c7f1c7b802f113d177f094cfbaf003477beec968f0ec903820ec6b87cfec4e94caeb8cfcf3e8d36d1ce81cc55be81960f4e77f3a88e75844d2e6347abfe6163fdce5c53e3ee59bd4f8e53fdc1fe47e4448e3e41e70e2d0e57ee25a607be2007c22e1fe4191e1d241a2e1cbdd01e17cf3aae0b47750ded3840fdec82bf7de7c3f2cde74a1c6
  | 6, 0 => 0x94b9571091ee93708d38c9608b4050608a584ed083591010812e9d207e60fd707780a8f0756b2e1074a9e19073e6337070b6e2706d133fa06b6b9590677b93206487f4b063ab42b0626d8910612365d05d62b2705b2eac505ab6a7705a617bc05a463870573298d0567fa510558348705555b1f0544534b0518d5c504bf18d304b1bc0e046cf47e0438fa7d0402104d03c4280903af162503a0a63e03793d110331cac60331242b02e42d5302d33fd402d338cd02b9da3102b06b5e0285f2df026aed2802599619021f2246021dfac801b60d1501189fc601185c6100f5391200e0ce0a00d64fc300c7987b00aa571900966ccb00924263005feef2001c45a1
  | 6, 1 => 0x108dfb00107f4f4a1073336b105cb296101cf31010154c531002172d0fed81c60fd4c59b0fb9a7030fb89c5c0f8d3dae0f4449ac0f250b2c0f0a2ca10ee047db0edc4daa0edabba70ecde01c0e86711a0e7871670e5ebfe10e2944270e28e0a70dda1f680dbd20e90db766cd0d8687440d7b28520d45ace30d3f58fe0d37803a0d1a20270d16ec7b0d0fc52b0ce117920cd494d50cd3e9650c8ba8530c4eb6810c3025590c2d1daa0c28117e0c23ba7d0c0603c10c0600430bb4968f0b85342d0b3f3fcc0b24a2690b077d2e0af1588d0ae213d90a83948a0a43775b0a3bf23b099deaf40993718c097f4255097b206e09691cef09684ec4096465950958e6e8
  | 6, 2 => 0x18b1b33e18720e6718666d5b185e1bcc185ae160182d023217e5a7ad17a485a0179a106d17749fbd1766891f1747ce401714a0de17104909170706f516f1fadc16e350de16a73b5f16a0d74d169fa60f169bf659167ebc1d167bf11216202697160e528215e78dfc15c683ec15c20c2115b76b33157f57571553bcd11542379b1537fcd214c11dd3149a4ea1146dd6781411bdaa140984d713e34d8013a260fd137f72bf135dacf0133bd6551324cfcd13164bbc129e49aa1264f2e012492a311238304e122ebf771200790011f47fb211e7921f11c9fc5911b565ba11a2fa93118defe21177b9f71168de3811595aa81105561310f31c5810ace4a610987933
  | 6, 3 => 0x20dc7ec920c4448120b4d99e20a0f1a92086ec832070a08e205970762051ecb820448ff32016bee31ff874121fc1b3651f4d462b1ecab2ed1ea89fbe1e665c391e6353211e2f7dc81e1c99681e1b1b781dda00381d7fa8f01d6e0d671d60bfef1d48e0fa1d0f04c81d00799c1cbc6c011c8242da1c70d8431c3932451c3444581c321cbe1c26e3261c0feb111c02e4e51bd07d241bbefd001b50f3c41b30b0d61b2c75891b04528d1ae2adb71ac426e21aaecfe71a8bc8ff1a5c8ab01a0a201f19ed676819e3796c19bab7be19b9c86819acb442196c97d4196926bf193d1fbb1930ecf0192f3fd619257c8118f64aca18da7e6718ce2c7618cdcd2718bc18ae
  | 6, 4 => 0x2808d69927f2fc1927d6774d27bf8f0327a2b1ad279df2682726a273270504e827041c86269d04852613f6fd25f197ff25c5d19325b758692579079a2575f2e525438452252abaeb25263a592525ce5d24f506d224f4abb424d5ba0324c1317424bff0952473a81e2465f4e22461748c2457de7a242a74e0241418ae23aa133923a12dde2379a87f2331768c232a54e82305e8be2304593422cf3d0a22abcb4422a39c5a227fd74d22779e7a227123322254b62c225227cd22488b2122432f9a223fc74c21f0c94721d6d25821d2836121be55de219084bb2190501221701c68215a0dca21546758214514152132c46a212bd5322126b5152118d8ca210940e4
  | 6, 5 => 0x2f3679eb2f2664432f15f2d72f14219e2ee197fb2ededa662ecfe5cd2eb2619a2ea15e5e2ea07b222e9f17e82e65c3952e648a822e4f101d2e346ced2dee4d682ddc0bb42ddbe4da2dc6d7902d9059d12d8369372d7eac952d6682232d4599c22d3ec0ff2d3c059b2d11b3fb2ceadb072cd48a3e2cafca952c35d6762bf3edcf2b8260c92b6692a32b3e9fc02b351a482b343acd2b1dc0e02aeff1232ad82ba32aafe6892aaf4fd82a88612a2a6f218f2a6bb0532a410c032a0377f129f5790b29ebfa5729c9501129a3cdc7294551f02920d6ee28e13c0c28c5433128c3a7c3289b697328997e9b2885da4d28708577286eb3dd2868c6752866bf5628437ca2
  | 6, 6 => 0x35f050a635aeb39835a264d33595bc22358231293578c84e3577243735747c4035563ca5353f3678352d90be35017f8434f20efe34ea9d8534d98ea734d6594234d1c21a34c3851934bf99d034a2015534a16be0348778123457b9423409b91133b89ba133b8069c3397ecf4337ef3c933725b2e333020a9331102a833036e7132b014893298c99332681bf4323446193228ae6731c9450831c832dd31c427d7317dda3a31747fcf314fc4ae314ce6a13147634930fab30230f28d1230ec4ec230e9925e30d17f8130986860308ead5a3081ef2a304e44793044a548302f8f99302c87ea3013e9e230056e013004a3e92ff00c9c2fb65c752f849e6d2f729edd
  | 6, 7 => 0x3e26d9273e24e9a83e1261773df9fd3c3dd6037f3d927cff3d784cdd3d35d18c3d32d0403d084ce73cf4fcd73c8a93293c83a3ee3c57fac93c4b2c0a3c2865463c1c44223c0b8a543bf8f7873bed95723be696503b58f2743b16298f3b0fb3493aaf31163aa0418d3a75749a3a6372fa3a2e61823a2919be3a1fbb533a19683d3a06c8213a0550d439f45ca439f12b3139b2b8723944bdf9389b16443895e6533872f208385fd14f3827c711381516bf38019ffe37e0382c37a9c13b37a11493376a4f6937635109375cfd243754a448374b4bd1370a73e836db17c7369cf6e636936f68368f5c033661bf2536607174364f2538362670f8361f6d3136110283
  | 6, 8 => 0x4881c4db4873125e485d290d4859eb6047ef23c547a0981e477294e64759feb746fd7f4146f5e80846db778946b17d4546a5aa93468f79f94627f96445fce37f45ee09e845d63c9845d2253d45b5059c4591ff1b458feefb457ce1024559780a44efaef6448b5842448a93e84488eff64454933643f41d3943d387b542fc4e1d4270df49422d12f34222f01b41be98b941bb1fa741ba41a041a08be94184918f41842d4541730c30414e706240fb2d0a40e06b1a40bd4a3540bc61683fc1f26b3f96f1e83f5b35893f55384c3f4bef103f313b653ef57a873ef2c9303ee9788e3ee60e733edb0e773e8136503e7774b13e51fe3b3e4848ff3e4480d63e294fff
  | 6, 9 => 0x526c4440521c351e52084b2c51fb152a51a6d579516061af515f7af4513f75ad5133c5d350f4e59f50b5442c5089060c503e3f225013ea855011dd494fe8b9594fae83b24f6674a34f5a6fd74ed160d14ea3893b4e83f48d4e4076434e38bd404e2ff7f04e022cb64df00e084d816bcf4d737d174d3963ef4cf59a004cc3be474ca53e9f4ca0b7c64c9ad3b34c7288214c3d8b974c272b804c24899f4c1de4d44bfe37d34bf953694bf1bf454bef9b8c4bd380b74bb6a0f34bafb81c4b634be14b550f714b5012d74b3b29e74b36c4a04b17c2144ae58e0c4aacdde34aac3dc34a83e25a4a50c24949f1948249a68b814953456348ef7a5e48dd5c0848b7e811
  | 6, 10 => 0x5b3983f85b275a7b5ad0256c5aca5d735ac8bc335ac80da45ab8a9c85ab513645a757c235a5fdbb45a4d2e935a106cc359f11a1459db1ce459c9a43c59a2dd63597165865945debb592cfafe59166efa58c37ad758a40ae158675125585896a658039e4a57d2593e576614095752e7795745e0fb5722e1255718f8f75711b47356fb2fd856b21c84569e151f562ecd41562c1268560409b255af346c5593c9de5587a49d55825803557f5c9155784b9c557784d655686b30553f4f795512031d550f9dbf550d9549548e179a547d8254544daeb95437853353ed427d53ce6a5e5396465d538beeb7535d66b7534c3a7b5335930252ce996352996d6752857735
  | 6, 11 => 0x64a6aa8e649f79ed649ef46b6438425e6430b85d63b72ebb63aef8ce63a425406397fc72633cbe4b6336422f62ee841462cc084362a0e515627e5bbd627b547b6245d47962387e786232122c622d0e096210567561f7222a61c7627361b0ce8d6178d6cc6117005560fd5a8260e5b79460d3573560ce7e49605cf992602ebcf16013f4555f83829a5f6459b65f48864b5f455d895f42ff6e5f31b6b85ef83f6a5e656a0e5e24e8325ddf67e95dc4fbd95d97f1e35d5851685d4fcd3f5d4631575d45a2725cff8ca15ceb768b5cddb7cd5cd503df5cbf0a655c965d485c8704475c7c04cf5c46243c5bdf984a5bd3319f5bd02ce85bbd4f985b6d297d5b4c7f21
  | 6, 12 => 0x6ac5e7666a7438dc6a5673666a4cc3046a288a666a10009a69de091c69d46eed69be6e3d69bc6b26699d812669904ec9698d1468697c5b6069716f05696e78c4696d0f21696669a5693978f969368570691f0f2068fcf56368f40b1c68ea371768d0837968cd9ffa68b1740068ae8ce6685cc15a6853fd76684bb6fd68377a7468353e5967e20fe067d44f0c67729a9d676bb23d675a94b0673f30aa673d759c67353b4c6722ad00670627f366cebc7866bc06636689636566759eef665c40e9664bccff664adcf266484c30664278a86606f81565ff6a2e65e93dc065e0a09965b9e4e5659a5792658410e7657276706564da556539ae4664c5e90e64c44499
  | 6, 13 => 0x7365dee3735b371572eb043272d7efa972bc21e472a2f37b7206812871f2bb8171ebea7c71a152de714bb5837141ec52711a767a70e8ab9670e73c24704a4f11703d5957701c39857012893a700bae0e6fd9346f6fc2e2136fb60c1d6f87372f6f67bb426f658ee36f2bae836f1b81706f172c546ed2a6bb6ebcd6bf6eb6d5ab6eac48236e991aae6e7696f56e6dbd796e4243826e2c414c6e25ed676e1219936e02eec26df0fec26dcabf0e6d60d6bf6d5716db6d00a8586cfba4ef6cfa59176c649cd26c5367486c502f716c24c4ee6be9b77a6bd746be6bd4a1b96bb6c94b6bad69396b632c766b5f9afb6b5c75836b3017626b2ab0536b1d82d66b0e7701
  | 6, 14 => 0x79870edd7976ef16795b686a7943972979245e39790cff8978f874f278ec302a78ebb70b78ea9f3678de9bf378bb489a78ba6f2e785ddb12785978f078511ff2784d1d88784058437823d24f78107f3c77fbc30d77dfd53c77d80d1677d4988577ce007a77cbd18277c708b577c0a3b577ad55bd779ba66477863a78773d6e78772c862976a8ae2676a836f7769ada327695efda7683bf937669dadc76372949762fc5e0762a3a1b762971fb75e65e8d75dd0ce375cc0e2b75c58e56757d9a14753c1a0575176c2174f8aee274cc57067480d24774653a047419a07b7404923d73d2f70573a86ee773a727dd7397502c739605b473944620738bcf2773722950
  | 6, 15 => 0x828ac9e3827719248275bc7c82686d6e8239b851819c32b2817f75818130b7408130b34b812d517a8128f3f380e61d5380d3e75480b1852280a4e2c7809566178073fb51806c43f780576af38050a21c80438d0b802e84697fca39d47f8d07b07f89bf0c7f7faaeb7f29300d7f21f4997f1dbf9e7eadfcaf7e761cb27e296a9b7dfe4a277de5e2f37dd241b97db6efa27da992dd7d97ec697d96ea5b7d8ee41b7d2dc3587ce39f5c7c9f7e7c7c9266867c8ee58e7c83f9e37b8fc70f7b8055d47b7c8fb07b725d687b5dc4677b3fd4b07b3759e07b08be407aff326e7a6bf5b27a555d6879fd2fbd79d11e9f79cdb177799f6a03799d347679973c807988b4ed
  | 6, 16 => 0x8acc513a8ac1d3288a9d0fa98a75f97c8a312c308a24d52f89dd480289c21aea8984b62e89837b27897726198952d7948928487388ef6b0288d9841188c5534e88c3770b88b545a5888e78d4888486d188650f36883cc48d880ca2e487f4d5fe87f2185f87b698fb87a82a1f87a7c0b9879dad88879b616287881d6a877ac84d8778f3be874f8de9873c288b870115af8700b22f86819cfc8669f43a866967f0862ef221861a5c8185f6bca685eb68b785dcdb4385dae8ac85ae8a63857a065e856379db854a84af85437c8084ffe3068461606984135e9583df4eb683dd9dd683bf71ac83b31a7d83afd670836650848352a486833c7e948302b3d682ca0a15
  | 6, 17 => 0x91d7069f91b813ea91aa7544919a8548916040ff915ee2109155cba09143acf29134859e911bcb6190f2ef9690ccfe8890bd7935908d554b90880b659084abc1904c7145904717af903e28129033b524901c386b8fe81a918fdc337e8fb464b68facd3798faa2cc78f912a818f8b65ae8f73c7e18f6f7fe28eb6e2ca8e7fa0178e7124918e6b60fe8e1ccec98e0fce5a8e032ec18db211478da284ba8d9ebf6c8d73f9a28cfc5fa38ccc91ff8cc26e8f8cbb13f68ca1c75b8c86d0e28c8473f68c7cbb378c6c29718c357e788bd6858c8bbf8e4a8b55b5f88b4d3e278b4bda108b3e9aea8b34a47b8b33b1068b3227778b226ac38b0df4778b02f4388aec5681
  | 6, 18 => 0x9a0375d599ddcba599bb987e99b655cd999c16099990d194995ebe0b995d02aa993863759929f7319929be40990fc09798f04ae198c6cc9598a41970985c4b769839f57d980f33cf97d4ee8097a7d927979e957997956ff49741a5ee9729e1129728c2da971329b99702333596f46af096ed6b4b96c0b12c96b1d1c0965c958996172dd4957fdd3c957a19a99563f2849556175c954d6df69549664b9539e7a3952c1b27952537b994e2b7a6949410e39475b1e39437159c9422a52f940baf2d93da0a209386a16f93676c6a93384e8a932b18c3931aebb0930fd33992faf10f92ce46f592baeec892b3968a92ad62a59296efa9927e36f292646ea391f23136
  | 6, 19 => 0xa091e7eea07a6a93a06bbb55a065d3c7a05bb1f0a0591b68a04daaf9a022680ca01e7942a010042b9ffe73fb9fbc557a9fb9dc6f9fab95ca9f8e9bd39f7c842e9f7bf9f09f67cab99f56ae149f2eb7e69f1dec7a9f1871cb9ecf60d39ea9cf699e950e899e7b41be9e6f30de9e58602e9e56811f9e469a269e2954c09e16c45c9dfb72369dcf69d79dabcbb79da41f8a9d3e8f329d1c0c8f9cebea369ca61f269c926e6c9c233c8f9c1719c19c1302f29c029e899bf4a3f29b92335e9b5bb1f19b52b2589b3cd8b89b27740c9afd8f8d9af3a5179aa960819aa7a1379a91b62d9a8445699a759f419a56ee569a43ff869a3ceae49a31aaa69a1e8be49a1ce59d
  | 6, 20 => 0xa8bd2881a898adeca85b9c23a859893fa8255610a82101fba81e9b5aa7eb83f7a7dd0816a76e8d9fa76a235fa74efc98a73eccc8a70c7473a6d49e51a6bea662a697cd48a6768364a65571c8a63d7091a63833fca61aec0fa5ef21d7a59a240ca596fabaa5903687a58b8199a54349f0a54213c6a4e58793a4c4d60ea4b7b929a4963bdfa47192b6a46a78e5a42ac53aa4234630a4232d48a40e31c1a409c4eda408a2cda406231da3cf4b20a39f3bc5a39854aaa35a4b36a32a47dca304b735a2db4979a2abd7d4a28a69a4a279624ba26ac316a261a1cea258df4ea219d787a1f49150a1c22db6a1b8547fa1607947a154c97da14a8c27a104f34fa0ca5129
  | 6, 21 => 0xaf715a7faf6a54ceaf552038af365ea7af3327ccaf331a1caf1c0d65af0aef8caed822e5aed207f3aea90596ae5db543ae4ef5bfae45eeb5ae2c4afeae273e52ae158a96ae056246adcfb474adb45f51adae2acaad9e7681ad9e1d21ad8c73d7ad8298d1ad7c2950ad1a5e2cad0806d3acf5cd26acac968aaca5b365ac9733e5ac906d29ac8bb181ac64d779abd61055abd01660abb8bae8ab9bd696ab7c776eab65e7feab1f6bdaab007fefaaeb53bdaadb85f3aab36682aaaa4cddaa687f22aa4ba25eaa48ef73aa32de0ca9faaec3a9f9f4e4a9c8f352a99951aaa9925c3da9907e58a98a32b7a9792550a9536d8da917ebcda8f1a5d6a8e68456a8d0e661
  | 6, 22 => 0xb70f3d79b7074051b6e36c7eb6df6e11b6b4852db6accce5b6501e65b63ea31cb6355c70b61f6ec1b60ea061b5ff4747b5e0fc76b5c668b8b5ba85f3b506dc05b4f4f1c8b4e35bdcb4de6d1fb492032db480a74fb4728320b3e784d1b3d8d830b390f841b3686ebfb35f22cfb33dffa7b320141eb3129c5ab2f88af3b2aa8f41b2a359d7b26acb3eb26a3914b21cccbcb1f1e989b1ea3e9eb1e1004db1b90588b1b80fbab1a60c98b18896bbb165fce9b157a81eb14c23c6b11cca9ab104e2a9b0e12fb9b0e0351cb0cbfc3fb0917dc9b0595bbcb04a1743b03b1c5fb031e5e4b0231d59b011ba9bafedb434afe6968bafd5efccafa76697afa4481fafa392a4
  | 6, 23 => 0xbe29aebcbe1d3d89be196fedbe159bfbbe14a030bdfad6fbbdf2ce8cbdad5056bd569d44bd3930fbbd2dda18bd189bfabd0264adbce6b52abcdc53d7bccfcb9bbcc3dd08bcab593dbca06b93bc8cd216bc8b9d4cbc77fd23bbf2c071bbd5d798bbca2fcdbbc7133abbc2fc4fbbbca07bbbaec883bb02fa31baeb4c1abac01b6cba92f12fba64e0c5ba506113ba042ecbb9f1aaf3b9dd9279b9b4923ab9b21282b9720104b906d2ffb8e55231b8d7c482b8ce80d4b8b4c543b88ec8b7b886036bb848ab6db82bb7feb814d973b7f848dcb7d97460b7c51bbdb7bed18eb7aef41ab7aa7e56b79bb9cdb78baa2eb749d50ab73008afb72d9c79b72bfc32b7283853
  | 6, 24 => 0xc686c8f2c673f56fc66f5291c6478a4cc63d3690c629c73fc61e01b4c61da8ffc6033cefc5cd6b88c56b8624c52e1fb3c4b7b787c4b2f914c4ad5e92c4aabbdac49270edc48f442bc478693dc476406ac4474355c43bc065c427e45fc4278cbcc4246ba5c406c3f6c37de605c35e0bd2c344729ac34137aac32e2226c32893d1c301791cc23da4f7c22b236ac1fd94bec1d9b175c1c536dbc1739970c16eae9ec14e859ac1438dfbc10593c9c0c437dac0b58cbbc0abe54bc0aa5d7fc0a94172c02871debff60ab6bfcca165bfc1787dbf8fc338bf653cc4bf2b5d91beee72e6becd8a39bec5fc52beb104f9beab9042be9f0fa5be652655be54e56bbe381453
  | 6, 25 => 0xcee27a34cedaf033cea899ebce846d20ce822d2fce6b0b63ce5f7625ce5dcc22ce5b4dccce2e5755ce2070bcce09d9eccdf4d6b0cdefb0f9cd9bd94dcd887d41cd862585cd82d068cd66305ecd52d7cdcd5027dccd4f9434cd359d45cd18a10acd0001bbcc7a28d9cc6e980bcc4309eccbf50b6acbda3838cbc67032cbb2c260cb7d4e04cb0c2dffcb03c38bcb000b6dcafc3a61caea07e8cabe2c2bca54dc08ca374c7cca011952c9ad9d05c98e47ffc9795635c92eff1fc8f98b0cc8e27018c8da031cc8d01b93c8c8ea72c87d0e7ec85246a6c8439af0c83a8abdc836f3c2c7eb7b10c7dfb52bc7c2625bc75c52b8c758fffbc6fb2141c690441dc68acfd0
  | 6, 26 => 0xd57f7a4cd57a8d8cd56e2ed0d53d1000d51e70b2d51552b6d4f26931d4ee2432d4bf08f1d4b0fdb3d4a7fe70d4979319d4756249d4468e80d43b08a9d43a869fd430d163d4130060d404f3a6d3f88ffed3f580b8d3cbe778d3c79162d3c5c492d3bf8548d39ab699d38ce4ecd34cb817d31e59f0d308d590d2f50777d2f274dfd2e8f0e3d2d200f6d2c8eb9cd2c5622dd2a7bf81d2a175c4d281ea23d2818fffd26b7512d22df939d213cfd8d204cc86d1cf1eb4d1ac10d2d1800b61d136a4a4d130e37ad1256833d0ac00cad06d3b0ad062548ed03db7cad008a737cff14dd8cfdff1facfb93b24cf9b40d6cf95ef5acf89ee0ccf5420d8cf49ee88cf0c9d9d
  | 6, 27 => 0xdf599a17dee4c313deda826fdeb87221deb1fadbde937b4ede0db03bddd031a2ddc09bfedd90d11bdd7d567fdd2cc0f5dd193586dcba6b17dc9bdeaedc8e32f7dc52b190dc240b61db96031edb79602cdb5fb3abdb3dab48db2e892bdb27b5cbdaf698d6dae827fddac5c427dabc24d6daaf4034da9544d8da951939da7ca94ada2eb777d9fde2d5d99d2432d95402cdd92ea3f0d9247009d91c549ed9095fbbd9084f52d8eb00bbd8d386a4d8c3bfbfd8bc4c27d8889027d867a425d85167f6d83420ded80e38fad808765ed7bcbfb8d769f1afd7694654d72f32a2d710e7d1d6e876c0d6a543cfd64d8f7ad61a4d78d611df38d5fede1cd5b41e40d5aa7164
  | 6, 28 => 0xe8b9410ae8a04ee5e89fb0f7e881f5cbe864106fe836ca65e818f2fae818e661e7e5d496e7c993cce7b52c4fe7750cb2e7253829e6a29096e6936f92e66b2de6e65f5618e62ee863e62b425de5f93c5de5f37bbee5f1b306e5d5979de5c458a1e59d96b3e578332ae542f83be521b1c7e513dc76e4e004dee4966ad9e46b7003e414a759e3b79e65e3963e6de38d55f2e38be53ae37f5dabe3247725e3106e12e2d452cfe29557f5e277a43ce27552aee2664f93e264e5f0e21be6e1e1f6e0a8e1edd638e1b39f56e1a85501e1389b3be1232a51e0dc783ce07f22d5e0756c61e06d864ee00a8c96dfa83d6ddf93d7ebdf86cf84df7b4d64df66fd53df6134ed
  | 6, 29 => 0xf1167821f0f73096f0cc6f54f0c046e0f0b61a27f0a7140ff099fd08f0953d99f08f4c22f02d76b9f012658feff26048efb87663ef93593cef5ce72fef57b8faef2e9b0fef16e17cef0efad1ef02a9ebeef747a2eee2b68feee0a72feeca28f2eec3e4faeeaf7c3aee82c328ee7f00b8ee73db6eee5bbf81ee556b9cee39e296ee24acd8edf34286edd2f3c1ed7dc820ed6973f8ed496387ed2e695fecf958cceccb1c68ec9aa4e8ec41d777ec309f4aec268398ebf52873ebee1786ebc722e3eb5bbcf8eb44c916eb406b8feb1d37caeafa8b81ea297667ea159ccce9c5a95ae9a9cac8e9a376e3e9942c9ce984f115e8eac2ede8ea5ac2e8daf5d2e8c459f6
  | 6, 30 => 0xf7c46fa3f7b5b8adf7a500cdf7712f20f768559bf760f6a9f75b3d8ef713d73ff6d62584f6af65a7f6a17f76f69beb92f68ec12af68e4a3df66671a5f64e5c0df644b462f61f7c20f61b6f81f61649e1f5f6dd7bf5f16f3af5b4f1e4f56a71faf560bcbef5561286f5424769f4e5306af4e0ba2bf4c930adf4c177d5f4b1393ef4ad3575f44e454bf440ca70f40c6132f4081177f3ee0630f3dc3983f3caa704f3aae1f6f3785de9f36d449cf3442ab6f30e4720f2fcd031f2a867abf27b317ef25ee065f21b68b1f1e2e744f1de31ecf1dbec25f1b2d8fef17f8997f1784439f15ce2fff1480d4bf1382f12f1350785f122744bf11de759f11cb99bf11829cb
  | 6, 31 => 0xffff0634ffdd78bdff7df0b5ff794e6aff74b158ff570128ff3d1588ff2757a7ff22015dff123350ff0a3806fea4321afe7dc54dfe6faf54fe69f639fe554becfe4b224ffe0578d7fdeaed64fdbe1e52fdaefc54fd42905ffd3824dafd32634cfcfad091fcef1659fcecae0dfccdb787fcc3aa8ffcb56f5efc30d494fc20dd5afbf3c341fba1db9dfb8f6c8dfb77b89bfb26bad0fb23d5c7fb185e60fb10699bfaef58b7facfb439fac3d065fabf7ea4fa4e962dfa33b007f9d2155ff9c44b15f97762a1f9554771f92dd199f91f3fb8f9158fc7f8d4c65cf89e2a03f87c9bbdf870fe03f85c491df82e5cddf82ca004f81aa65df8037aa5f7fbb235f7d52f2a
  | 7, 0 => 0x10af5719109989db108a8de8106602d20f970d4b0f88aeee0f52f7e70f1c517e0edcd7070ed48efb0ecd7e060eccb7400eb2ba8a0e9187990e62c7b30e532e160db6ae630db3a33c0d4c5b2b0d2e3d660d2c2e290cda57470c5bdf350c23ba7d0c041eab0bedd9ed0b8daa5b0b8bbf6b0b203b970b15b6280aeb16150ae68dfb0a9f6c030a5133e10a4a180909efeca509d69a71092808eb0907828d08cb2a3508bba70d08719fb807f8bba507f0d02407e641970790ca2a07852a5a076d9aca06c8af8105c078cc0544cdf604e56c620499b2c10426a54103a5f4b30346c6ec02fbbdeb02c7e1c601c0cf2f0193adbd01737d88011dc73700f26ece002f4827
  | 7, 1 => 0x1bd38e271b9b06e31b6588df1b54b30e1b36540e1b30b0d61ad3e37a1a6beff41a52295d1a51558f1a28899f19edd2a919b22bfc19b15e681983ef5b196926bf194d07b41917953718b98c20189246be1867ad14184d71d418097fbf18035660179ba5681773f9151742223f1703b38d16ff67ae16ed244d16c885cc169f5cd9169ad4dc168319a4167ebc1d167506e1159b56a6155b07071512820214f312d414c25be7147ef837147be17a14755aa7147387c8141f8fdd140ddc3213b478a213a260fd133606d912c7ac7e12b5374512a036a6129b1125128177ed126ac74e11f546a611c9fc59116093e1111d5c611101c9f510eee49c10dfc44d10bcd6ce
  | 7, 2 => 0x2a9cb8fe2a339e2929e93d172990644b293de185292e66d9292c0d9728dc69992880e0ed2870b3da280c081527a4a978276f815f26c74c0626b60929268e2ccc25e00859259565192572009525029ba3250036df24f1d90e24ba3ed624923197241a19e7240356ad23fc0e4423d4986c2358f6eb22f2b390226d9e5f2238b79e2222d2642209c14921da3c2021d460ea21b4474221a9023c2136416c20bd10b4201138cd1feab86f1fbe639e1f96edc61f28e87e1ed943511eb180c41eaec2be1e21c84f1e1b1b781dbf2e791da3c2791da0f8bb1d42c60e1d22f2e51d0c61251cf1298c1c91f0b51c8d2d2f1c7f660e1c567a591c1a73291c1160c61c02e4e5
  | 7, 3 => 0x3e0da1cd3e0800243da3a9703d9f9c853d9cd9ed3d32d0403d0bb5b13d084ce73d0508da3ce83b323ce7d84a3c8ae61d3c5cd0913bcc4b8e3bbd9fd83b9517d93b76d13c3b4067bb3aefec363aa5adab3a3b4fbd3a1aa6c23a1a9e3839c95bf039559c2f3860df7e3849566837fc88ca37a8b67b37a1d1e4376a4f6936209e1535a8333934d1c21a34bd92e333e83ed833ac494933740dd13354954533513a6032db8bcc32c96d1e3265f79931c32ec331b30d7c317904b9315f0dca313507a63116eaad30c2219f30b17a1b30a6803d3092a0e230797d6f30452eee300d39e92ffd69612ff1212a2d6782ad2cfda1512cf45da32ceb381e2c9d909e2aa95048
  | 7, 4 => 0x4dcff4e94d8180284d476b1d4d2f3c8a4d2885244cd3f7294c8d80f44c6505a34c50a0f34c1021324be20cd84b550f714b43cfa04b0d46544a93910d4a258bc54a0c99e049a1a3af493d4cfb48be36e948a30f4847e5621747c656fb47aec13b470ecdb246f3f1d646ce968746cd9c504621c46945d1eda1458b6160455fb1d04541e848452bb7f64514c0b444aae862440fed9243fdcee443ee7c4343cc419643a4bde9434d74414307780a42ed440f42d860fb42a809fe424b4c7341cd32dd41ba41a0417604ab414c63494125de8a411da5b740fd5c89409e34a440564819400015073fd89f2f3fd242ec3fc0243e3f9ad3953f643da43f521ef63eb72f93
  | 7, 5 => 0x5e4f53365e471a635dfdbd4f5bf8a09c5b919bb95b8b47325b8a9b545b7badac5b1760205ab5abb15a910ab55a5fb9955a44828159428c4e58bcfd235883ea5058652e3d57c46348572b3dcc56cdce4e567ab1f456713ef9564fc878564cc3ef562852a055fdc57d55e7a0d655b00d5b555e780a552f3dc75516b86d5400b90d53fc1e2653d9433553ad13b6537f76e6532b31af5310cae852d41b9452c6dafb52b2351452652dd55264f30152377d0751f0701b51bbbb755164663951529dc45111b38450c1bb7d50ba5f8b509cfade506e3a1a505960925046c44250429db55015e3964fed6a864fc5f4ae4f85907a4f1c75a54f01e97c4ef5be6c4ed13bb3
  | 7, 6 => 0x6a314b076a20792e6999900369904ec96986998d69415288690b8184690b0d3968f8c50e688b91116874221a686021f6685bd80f68273a5d67af13ba67a3692b679e3ab8679b211f675a94b067360e8c6724e6de6722ad0067108e52664b1a336608c4136601c8f4655e0be1655be55d64f1090064ede01564bb1a68644d15206438425e6430b85d63e020e463d8096f639e21dd63716914630363cc62df652162a89ff7621b7fc562125aeb620d6f8d61fe340661ede05661b0ce8d619f6a45616775856131850560f5b64260a42f0260965ffb604bbc7e603fd01260364b426001d5a75ff63ef25fecffb25faaa4325f6ce3e65eec2d245ebd6c475e621403
  | 7, 7 => 0x78d7caf178ba6f2e78a93579779b444e770282c076e1ad9c76b73a4776abcfae768e63657673e45e7663a7c67651891875b7bbb075a3370775910ad37547f2db751d0c7d74e1c74f749f06a7749a204b745985b3742c1b037414985b740279ad73f742fa73ba132f73a4843a739f2b397391a15173793d24733d13567278be2072675a3b724ff73c71801e44712a2db9711403f870821968706ffaba700149d46fef2b266f9675c96f321f156ee55b736ebd78496ea16f056e3ca8b56d97aec66d42739e6d16df326cd46e566cb455396c96dad26bfb0bf96bf88c416bf5ec266bf2d3266bbf6b7e6b58cb236afb3f026af4746f6aeac5db6a866f276a7438dc
  | 7, 8 => 0x87b4a88f87abe57287a84624877f470c868acfaf861a5c8185db428985cf5b4385b3ccb1859d96c6857f3777855c72848507f4ca84d2c17584d0ab2d841693fa84135e958402ce3784013fe783974926838f9fac836a9b7e83490ab082fc9636828431898260f229824f20f681f4635f81d2870381a2fbbd8124f5e7811ec7de81127705810644fc80b18522805efbd8805053ab804dee4d7f82a65d7f2d59fd7f1e4fa97ed5e67c7e0ce9f17dd7bdf57dcefbd27dc3c7c37c7dc63b7c40e7c27c3a52057c1b05047bdc910e7b9abeb87b84bff87b4367897ae964887ac3e1087ac297f57ab727867a98c0657a7938dc7a5ac63379ff8fe979fc07f678e4f5a2
  | 7, 9 => 0x98c8770b989ed46797b7adba97b3be8397a2ad88977c745d97181da996f519d9966e67f0964fc4fc960bbbd995cb9afe95a70165959b5dd2958aec459542aab194dbd1b494ab5faf9492ddb29477c987943d5a6794213f90941af6919406f9df93a06ffc9353153f92e1305c92bd460992a93537928a05769244de8392427637923c767591ffdd0791869cbe913e368f90dec3a290c13cd3903af60b8f95124e8f87e3d58f66a91b8f0950aa8f0252678ef8c9ee8ed4acb68e6a85208e5c135a8dbf9f568d8425078d4f66ca8cb80d3c8ca877188c90870c8c53b6888c27a7848b659dc48b1d15ca8a7a9a9d895dd9a18911bc2488f2ca4188c8f86088a3b6dc
  | 7, 10 => 0xa7420870a6ea9da8a6bea662a69e95f1a64e8b36a648124ca643b4c5a61c3eeda5ef21d7a5dd0329a54e664ba549f6c7a54349f0a50f6f2da4c92733a42a80b8a3dc3944a3d3d878a3bebdf8a3ac4ce7a312e913a304b735a2729855a26835d3a203df1fa1f4e361a1ea2ffda1a94993a185d949a184c90da10a5eb9a08ce91fa07a6a93a048e404a039bc459f9b20929f36c9de9e34edaf9df24a1a9deb9d439ddb52d89dc6e8679dc0a26d9d717a869ce2885c9c26fc249c08a19f9bed4a379bea8a5f9bca85189ba44aeb9b87d20b9b4c7f429b0132a19a8d182a9a80d3c49a31aaa69a02cdee99d4553f99ca9ecb99c2b8b8999e3acc98fd6fd798e90a55
  | 7, 11 => 0xb981579cb96ac126b940c30cb93140c9b8db3bf4b7f96484b7d2f7b7b7ba7b55b7acf0edb7aa7e56b60aa1c8b5f481dbb5c668b8b5bdd37bb5611d4db536f93db51da5ecb4659c05b41a71fab3ef6d88b3c7f7b0b399a266b3954d11b37b151bb32747c9b19f34c8b19e29acb1838f47b158ad0fb14a7c74b0bd8805b0b62913b0b06ff8b0316723b0049811afe37ca7af99e6ccaf0a244eae9fb3e9ae6ff2a8ada97aa9ad48081dacab5189aba7945fab858806ab75d046ab7128a0ab2b8525aa7319c3aa6baa8ba99d0106a96bd003a9536d8da92e1f67a91c00b9a906a98fa8fdcabba8dc75baa8d53ae9a8aceb64a86c13e6a837e8f9a7de7870a7697e48
  | 7, 12 => 0xc972257ac92fe007c90dcec6c8edb51ec8e27018c8bac5fac8357a45c7b80108c7abb727c77e7691c77d5d96c76b3ee8c753aa54c74aa3c2c6dc9e7ac6b20031c66c1ee5c6457565c613a061c5af49adc58557c3c5825014c5742e9cc55b362bc5547d17c492f2f4c3e57ed0c2d474bfc2157f87c18ac36bc1645d2cc1522335c11b76cfc0edcc81c09467eac08ae272c060a091bfa320febf75efa6bef995f1bebd2cbbbead66f1be769f18be2c3e52bdf9dc12bdbc8780bd95ab3dbd541193bd4e9e51bd15572dbc41653bbbe6ae2bbbc01f92bbaec883bb67486ebb32f41dbab4727abaa031c9ba53eca2ba322c81ba2b822db9fc0058b9c192a0b9a45e1d
  | 7, 13 => 0xd9e2caf7d99ad6ebd992242bd916e5cfd7fdd228d7fb8f7bd7ca020fd7c1c93cd7a6873cd753c3f4d71460e3d7000549d6a4388cd69e5019d58f793dd519e096d5053b33d4c65289d4b4a79ed48d31c6d45050ead428db12d4034cd6d3f12e28d3d6fe7ad3ba0645d35f5289d358ca24d2925225d277431ed24ac501d23eabb7d20f18d0d175aa0ed118e234d0c9d227d0bc3a17d0657b73cff609b7cf46f35bcee4c42bceca0d03ceb7c1d8cea8ef3bce63f497ce0e84ffcdef810bcdc8ba32cd9702facd79adfbcd52d7cdcca5cfb7cb884e68cb78c448cb694c08cb3cc489caf82cfdcaccec61cacb121ccab0ad57ca94fea2ca8c625dca1e5d15c98e47ff
  | 7, 14 => 0xea36d74aea26b1ebe9e3dfc4e9b88a37e9877a69e9430aa7e8a202a5e892c0b4e836ca65e7f44a52e7d7a280e7baf5ffe78c552be7311744e7125d9fe6c3db03e6a45857e6918e0be666e665e62388c3e604fcffe5685c65e50d18f3e4ee680be445238de4386609e3c453f9e3a3bb46e3963e6de3412cc1e286305de27df1c3e2760958e2182b15e1f09bdde1c02f6ee173acfee0b0bd65e07b3ab3e042b81de03fa7b4dffd34dddf1b03fddeae0fc1de7c5035de139a83ddf5fcc6ddc8da88ddb2f137ddae2572dccedae9dc5b1b28dbff73e2db2c04c2db27b5cbdae5b725dab6ff36da8a437ada70651bda5e734eda1ba67fda067d68da025fd3d9f67adf
  | 7, 15 => 0xfa359d84f9dd0963f98cef47f8ec2452f8437cc5f8037aa5f7fa7a3ef7d668baf7a272fef78cfa2ef77c0b91f779aaaaf6b22f67f63e7977f542c7dcf4ed8e48f4c886ecf4b6683ef46969daf4643038f452118af3c7c4c5f3498f0ef303e5cdf2dc4118f29f8f19f29bf981f2894adcf26d989ff1de1c4af1dccc71f1af9c79f179c596f13196a3f0a9d6b2f029aa86efb5a3deef6634edef2e9b0feee28738eecba126ee82c328ee18b783edbd194fedacebaceda087bded71f1d3ed070007ed03ec8becf3ebfdece124ddeccf062fecc677f9ec85e6b5ec58a0dbebf3dd49ebe13684eb7d2b56eb500845eb1c83beeacf38b1eace13c6eaa4dc92ea5d0618
  | 7, 16 => 0xff89d50dff652815ff33d146ff257e59ff123350ff0a3806fee73185fee14d72feceb7ccfe87aae0fe64aba8fe09dc14fe073c2afddfc652fddc089cfdb187fafda9c5a0fc453af5fbadfa39fba0a51cfb8cf931fb3c38d9fb25dc2ffb23d5c7fb1f7172fac83e9afabb6945fab21684faa3a2cc
  | 8, 0 => 0xfe971ab2f92dd199ee12c54deab44034e5f2c308c708d5a6bc1d1430ba47a138b40748eeb158ad0fa4234630a0e187958d2c30e477cbd18269904ec962a89ff75d017f514e31041e46d957713ef2c9303ba45360358f846f19570811
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0xa106000000000e10f00000000061060000000000010000000000e10f000005040a205000000000610f000000000e10f0000000006103000000000610d000000000001000184544813100018c54481310000000000610f000000000610f000000000000f000000000000d000000000000b000000000610f000000000e103
  | 5, 0 => 0x2117000000000000f000000000001c000000000e10f000000000a105000000000001d000000000000f000000000e10f00000000000000000000000003000000000000d00000000061170000000000011000000000610b000000000000e0000000006102000000000e11d0000000000011000000000001f00000000000080000000000003000000000001a000000000e10f000000000000a000000000000f0000000000000000000000000d000000000000f000000000001a000000000000600000000000160000000000011
  | 5, 1 => 0xd000000000000f000000000000f0000000000003000000000001c000000000e10f0000000000016000000000000f000000000000b00000000000190000000000000000000000000d000000000000d000000000001a000000000001f000000000e11c000000000000b000000000000f00000000000100000000000018000000000000d000000000e11d0000000000016000000000211f000000000e11f000000000000d000000000001700000000061110000000000005000000000000b0000000000011000000000000a
  | 5, 2 => 0xa103000000000000f0000000000008000000000000d000000000001d0000000000012000000000a103000000000e10f000000000000b000000000e11d00000000000060000000000003000000000000b000000000001000000000000080000000000014000000000a105000000000a11c000000000001f000000000e11f000000000000d00000000000050000000000003000000000000f000000000e10f000000000a105000000000001d0000054481210000000488121000000000000080000000006117000000000e11d
  | 5, 3 => 0xd0000000000008000000000a111000000000611800000000000080000000000013000000000000f000000000a105000000000000700000000000100000000000007000000000000f000000000a117000000000000a0000000000003000000000e103000000000611800000000000140000000000003000000000000b000000000001c00000000000170000000000008000000000000f00000000061060000000000000000000000000d000000000000c000000000000f000000000001c0000000000010000000000e10f
  | 5, 4 => 0x611a000000000000f0000000000000000000000001b00000000000180000000000019000000000000d000000000a1180000000000005000000000000f000000000001f000000000000d000000000000f000000000000300000000000160000000000005000000000e11d000000000000f000000000000d000000000001f000000000000d000000000211c0000000000011000000000001a000000000001d00000000000140000000000006000000000000d0000000000015000000000000a000000000e11f000000000000a
  | 5, 5 => 0x611a000000000000f00000000061030000000000011000000000000f000000000a118000000000000f0000000000017000000000000d0000000000006000000000a11700000000000030000000000007000000000001d000000000610f000000000e10f00000000000080000000000008000000000a103000000000000c000000000a1030000000000008000000000001300000000000060000000000003000000000000d000000000001100000000000020000000000000000000588121000000000000100000000000001
  | 5, 6 => 0x1a000000000e10f000000000000d0000000000003000000000000b000000000000d000000000000d00000000000180000000000011000000000000a0000000000005000000000001e0000000000011000000000001c000000000e10f000000000a1050000000006103000000000e11c000000000e11c000000000000a000000000001c00000000000070000000000006000000000000f000000000000b000000000000d000000000000f000000000000400000000000060000000000010000000000000a000000000e11d
  | 5, 7 => 0xe10f0000000000000000000000000b0000000002111000000000a11c000000000a10d0000000000018000000000000f000000000000b000000000000a000000000000d0000000000016000000000000b000000000001f00000000000160000000000011000000000a108000000000001c00000000000050000000000005000000000001a000000000001f000000000000f000000000000d0000000000018000000000000f000000000000a000000000001c0000000000008000000000e104000000000000d0000000000003
  | 5, 8 => 0x70000000006118000000000000f000000000000800000000000030000000000018000000000000e000000000000d0000000002112000000000001e0000000000018000000000001b000000000000a000000000000c000000000001d000000000e11d000000000000b00000000000080000000000006000000000000d00000000000100000000000000000000000000f0000000006118000000000e11f000000000a103000000000001d000000000000d0000000000011000000000000c000000000001f0000000000006
  | 5, 9 => 0x18000000000000d0000000000013000000000a11c0000000000006000000000001200000000000180000000000002000000000001a000000000000b0000000000007000000000000b000000000a11c000000000000a000000000000a000000000000e
  | 6, 0 => 0xf000000000001d000000000001d0000000000011000000000611a000000000e11d000000000001f000000000001d000000000a11e0000000000003000000000001c00000000000120000000000018000000000001c000000000001800000000000030000000000011000000000e11d000000000000200000000000100000000002112000000000001800000000000130000000000018000000000000d00000000000120000000000003000000000001f0000000000017000000000000f00000000000030000000000011
  | 6, 1 => 0xf0000000000011000000000001d0000000000011000000000001d000000000e10c0000000002111000000000001d000000000001d0000000000000000000000001200000000000180000000000012000000000000a000000000001d000000000001300000000000180000000000004000000000001a000000000000d0000000000006000000000611a000000000a1080000000000011000000000000700000000000190000000000011000000000e11f0000000000003000000000000f000000000001d0000000000019
  | 6, 2 => 0x160000000000012000000000001d000000000001100000000000120000000000011000000000000f000000000001000000000061110000000000008000000000001c000000000001d00000000000110000000000007000000000a10500000000000110000000000003000000000a113000000000001f0000000000012000000000001e0000000000016000000000000c00000000000110000000000008000000000000f0000004802210000000000001d000000000001d000000000611d000000000000d000000000001f
  | 6, 3 => 0xd000000000000f00000000000120000000000010000000000000700000000000030000000000017000000000001c0000000000013000000000a1110000000000007000000000a11c000000000610c000000000001a000000000e105000000000e11d00000000021080000000000013000000000000f00000000000170000000000016000000000000600000000000060000000000017000000000001f000000000000a000000000001a000000000611a000000000001c000000000000800000000000180000000000017
  | 6, 4 => 0xd00000000000180000000002112000000000001d000000000001200000000000110000000000012000000000001a00000000000180000000000000000000000000e0000000000013000000000a105000000000001a0000000000003000000000000300000000000050000000000013000000000001200000000000190000000000011000000000001c0000000000006000000000000600000000000170000000000007000000000001d000000000001f0000000000008000000000001c000000000001c0000000000012
  | 6, 5 => 0x3000000000001c000000000000d0000000000010000000000001f000000000001c000000000000d000000000001a000000000000d000000000a11c00000000000080000000006118000000000001e000000000e10f000000000001f000000000000f000000000001c0000000000007000000000001200000058c4210000000000211c00000000000130000000000017000000000001000000000000050000000002113000000000001100000000000130000000000000000000000001c00000000000070000000000013
  | 6, 6 => 0x11000000000000300000000000180000000000018000000000000d000000000000f00000000000120000000000011000000000001c000000000001d0000000000019000000000000f000000000001c000000000001d000000000000d0000000000006000000000000d0000000000003000000000001c000000000001300000000000030000042402210000000000001f000000000e10f0000000000017000000000000a0000000000011000000000611a0000000000012000000000000f0000000000003000000000001f
  | 6, 7 => 0x1f000000000001c000000000001800000000000170000000000017000000000001c000000000001c000000000000a00000000000160000000002113000000000001c00000000000060000000000011000000000001c000000000a118000000000000f000000000000200000000000030000000000003000000000000f00000000000080000000000003000000000001900000000000080000000000012000000000001800000000000030000000000007000000000000f0000000000011000000000000f000000000000f
  | 6, 8 => 0x13000000000e11d000000000001c000000000000f000000000e11d00000000061180000000000019000000000000c0000000000018000000000001300000000000110000000000011000000000001d000000000001d0000000000003000000000000d000000000001300000000000030000000000011000000000001600000000000190000000000007000000000000a00000000000170000000000013000000000001c00000000000190000000000018000000000001e000000000000f000000000a1030000000000007
  | 6, 9 => 0x1d00000000000050000000000010000000000611e000000000001c0000000000018000000000001900000000000050000000000018000000000001f000000000000f000000000001f000000000e11d0000000006118000000000001f0000000000010000000000000500000000000050000000000011000000000001a0000000000018000000000000f000000000001c000000000000f0000000000019000000000000600000000000050000000000018000000000000f0000000000013000000000001f000000000001f
  | 6, 10 => 0x3000000000001f000000000a105000000000a1050000000000016000000000001f0000000000007000000000001a00000000000120000000000018000000000611d0000000000008000000000000c0000004802210000000000001c00000000000050000000000008000000000001f00000000000170000000000018000000000a111000000000611d0000000000010000000000000c000000000a10d00000000000120000000000005000000000a103000000000001d0000000000012000000000000c0000000006103
  | 6, 11 => 0xd000000000001f000000000001e00000000000050000000012105000000000000600000000000180000000000010000000000001c0000000000013000000000001200000000000080000000000019000000000001d000000000000f0000000000011000000000001c0000000000000000000000001d000000000e105000000000001100000028022100000000000003000000000001900000000000060000000000013000000000e11d000000000001a000000000000d00000000000110000000000012000000000000f
  | 6, 12 => 0x11000000000001c000000000001e000000000000f000000000001c0000000000019000000000001100000000000110000000000007000000000000f000000000000d000000000000f000000000001300000000000030000000000011000000000000f00000000000060000000000006000000010c105000000000001200000000000110000000000013000000000001d0000000006118000000000000c000000000001900000000000180000000000019000000000000f000000000000f00000000000180000000000000
  | 6, 13 => 0x30000000000005000000000000a000000000001c0000000000017000000000001e0000000006103000000000000e000000000001f000000000000a0000000000007000000000000f000000000000100000000000030000000000019000000000001c00000000000130000000002113000000000001800000000000040000000000013000000000001d0000000006117000000000000f0000000000003000000000610f00000000000170000000000019000000000000f000000000001d0000000002113000000000e11d
  | 6, 14 => 0x400000000000170000000000008000000000000a000000000000f000000000001f00000000000180000000000018000000000001800000000000040000000000011000000000001d000000000001f000000000611d0000000000011000000000000d000000000000d00000000000120000000000012000000000a1180000000000003000000000001f000000000000d000000000001800000000000120000000000003000000000001a000000000e10f0000000000010000000000001d000000000000f0000000000011
  | 6, 15 => 0x80000000000005000000000000d00000000000170000000000013000000000001f000000000001c000000000000d0000000000019000000000001d000000000611e00000000000190000000000003000000000001c0000000000018000000000000f000000000000d0000000000008000000000001e0000000000011000000000000f00000000000000000000000009000000000001c0000000000019000000000611e0000000000013000000000000c000000000001c000000000001600000000021120000000000018
  | 6, 16 => 0x30000000000004000000000611a000000000611e000000000001c0000000000018000000000001f000000008411e00000000000120000000000011000000000e11d0000000000013000000000a11c000000000611a000000000001f000000000001d000000000e11f000000000001800000000000070000000000013000000000001d000000000000f000000000001e0000000000003000000000001f0000000000000000000480a210000000000001d000000000001f000000000001f000000000001d000000000000c
  | 6, 17 => 0x611a000000000000a000000000611d0000000000010000000000211c000000000001c000000000000f00000000000180000000000018000000000001f000000000001b0000000000019000000000000d0000000000018000000000000f000000000611a000000000001d000000000001800000000000080000000000016000000000001100000028062100000000000016000000000001c000000000001e000000000001e0000000000007000000000001e000000000000600000000000190000000000019000000000611a
  | 6, 18 => 0x1f0000000002119000000000611d00000000000040000000000011000000000001d0000000000004000000000000c000000000001f0000000006103000000000001f000000000001100000000000120000000000011000000000000d0000000000003000000000001300000000000190000000000004000000000001d0000000000011000000000001c00000000000110000000000007000000000001800000000000060000000000007000000000e11f00000000000080000000000003000000000611d0000000000018
  | 6, 19 => 0xf0000000000007000000000000b0000000000013000000000001c000000000001100000000021190000000000019000000000610d0000000000008000000000211f000000000001c000000000e10f0000000000016000000000001e0000000000018000000000000500000000000120000003802210000000000001200000000000060000000000003000000000001c000000000001d0000000000006000000000001c0000000000011000000000001d000000000e11d000000000000f000000000001c000000000211f
  | 6, 20 => 0x110000000000019000000000001800000000000120000000000016000000000001a0000000000018000000000a10f000000000e10f00000000000120000000000008000000000a1110000000000012000000000000a000000000000c000000000000f000000000001c0000000000012000000000001c000000000001d0000000000018000000000000f00000000000180000000000004000000000000f000000000000f000000000000c000000000611e00000000000190000000000004000000000000d000000000001c
  | 6, 21 => 0x1c0000000000018000000000000300000000000120000000000013000000000001a0000004881210000000000001c0000000000017000000000001700000000000110000000000018000000000000d0000000000013000000000001c00000000000190000000000012000000000e11d0000000006103000000000001c000000000001c0000000000005000000000a1130000000000017000000000000e0000000000003000000000001d000000000a103000000000000f000000000000400000000000110000000000008
  | 6, 22 => 0xe11f000000000211c000000000e10f0000000000011000000000611a000000000000400000000000080000000000008000000000001f0000000000003000000000001d0000005909210000000000e11f0000000000018000000000000a000000000a113000000000a119000000000001d0000000000019000000000000f00000000000130000000000011000000000000d0000000006118000000000a11e000000000e11f000000000001800000000000110000000000003000000000000800000000000070000000000019
  | 6, 23 => 0x211f000000000611a00000000000180000000000012000000000001d00000000000160000000000016000000000000800000000000130000000000007000000000000f0000000000003000000000000700000000000180000000000008000000000001f000000000e10f000000000211c00000000000170000000000012000000000e11f0000000000011000000000000d0000000000013000000000000f000000000000f00000000000120000000000016000000000e11d000000000000d00000000000060000000000011
  | 6, 24 => 0x1c000000000611d000000000001f000000000001d000000380621000000000000030000000000006000000000611a0000000000011000000000000d00000000000030000000000003000000000e10f000000000001f000000000000d00000000000120000000000012000000000001d00000000021130000000000005000000000000e000000000000f0000000000011000000000001f0000000000016000000000001d000000000a10d000000000001800000000000120000000000012000000000e1040000000000011
  | 6, 25 => 0x211f000000000001300000000000080000000000012000000000001c0000000000007000000000a113000000000001c000000000000f0000000006118000000000e10f000000000001000000000000070000000000011000000000001600000000000170000000000017000000000001c00000000000170000000000016000000000000d000000000001200000000000130000000000007000000000000f000000000e11d000000000a11100000000000110000000000018000000000000a000000000001c0000000000012
  | 6, 26 => 0x1800000000000110000000006118000000000001f000000000001000000000000080000000000008000000000000f0000000000018000000000000a000000000000d0000000000008000000000000f000000000001f000000000001f000000000001d000000000000800000000000180000000000003000000000001f0000000000011000000000000a000000000000d00000000000190000000000008000000000001c0000000000018000000000001d000000000001900000000000120000000000011000000000000f
  | 6, 27 => 0xa000000000000d000000000001c000000000000d0000000000003000000000000a000000000611e000000000001d0000000000008000000000001d0000000000003000000000000d000000000001d000000000210800000000000190000000000018000000000001100000000000190000000000003000000000001200000000000120000000002108000000000000800000000000110000000000000000000000000d00000000000070000000000006000000000001d000000000001d000000000000f0000000012105
  | 6, 28 => 0x18000000000001c000000000000600000000000120000000000002000000000001d0000000000019000000000001f00000000000110000000000003000000000001100000000000030000000000019000000000000f00000000000030000000000017000000000000f000000000001c0000000000011000000000000f000000000610c000000000001300000000000120000000000016000000000001d000000000e11f000000000001800000000000030000000000011000000000001e00000000000160000000000008
  | 6, 29 => 0x1c000000000001c000000000001a0000000000000000000000001c000000000611e000000000000f0000000000019000000000000f000000000000f00000000000180000000000011000000000001d000000000a10a000000000001e0000000000011000000000000800000000000190000000000007000000000000f0000000000003000000000e11d000000000001600000000000040000000000019000000000001a000000000001300000000000120000000000018000000000000f00000058c4210000000000e10f
  | 6, 30 => 0xa0000000000012000000000000c00000000021190000000000012000000000000d00000000000190000000000018000000000000f00000000000180000000006112000000000001a0000000000003000000000000a000000000000f000000000001c0000000000013000000000000c00000000000030000000000004000000000001d000000000a103000000000000400000000000110000000000011000000000a105000000000211100000000000080000000000003000000000001c0000000000008000000000001d
  | 6, 31 => 0x12000000000000700000000000110000000000000000000000000f000000000001c00000000000160000000000012000000000001a000000000000c000000000a11300000000000060000000000016000000000000f0000000000018000000000000f000000010c105000000000a113000000000001f00000000000110000000000019000000000001100000000000130000000000019000000000611a000000000000f000000000001c0000000000011000000000a1130000000000011000000000000f000000000000f
  | 6, 32 => 0x100000000000016000000000a10500000000000110000000000018000000000000800000000000050000000000011000000000001200000000000190000000000013000000000001d000000000000f000000000a111000000000001d0000000000012000000000000f000000000000800000000000110000000000011000000000000f000000000001c000000000000f0000000000006000000000001d000000000e11d000000000e10f000000000001c0000000000011000000000001c000000000001a000000000001c
  | 6, 33 => 0x19000000000611e000000000001d00000000000130000000000004000000000000f00000000000080000000000012000000000001800000000000170000000000003000000000a118000000000000f000000000000c0000000000018000000000001700000000000130000000000004000000000001c000000000000a000000000a118000000000211200000000000000000000000003000000000000f000000000001c000000000000000000000000110000000000013000000000a10800000000000030000000000008
  | 6, 34 => 0x80000000000016000000000001f0000000000002000000000611e0000000000013000000000001800000000000120000000000018000000000001d000000000000700000000000190000000000019000000000001f000000000001e000000000a113000000000e11d000000000001d0000000000011000000000000700000000000160000000000008000000000000f000000000000700000000000180000000000012000000000000a0000000000013000000000001e0000000000008000000000001a0000000002119
  | 6, 35 => 0xd00000000000060000000000019000000000000c000000000000c0000000000000000000000000f000000000000f000000000000c000000000001a0000000000011000000000000f0000000000002000000000611e00000000000110000000002108000000000a118000000000001c000000000000d00000000000180000000000018000000000e10400000000000170000000000013000000000000c000000000001d0000000000018000000000001d0000000006118000000000001300000000000030000000000016
  | 6, 36 => 0x190000000000007000000000000d00000000000110000000000004000000000000f0000000000013000000000a103000000000000d0000000000000000000000001200000000000110000000000013000000000001d0000000000003000000000001a00000000000110000000000017000000000000a0000000002111000000000a105000000000000a0000000000008000000000001c00000000000020000000000008000000000000d0000000000000000000000001e000000000000f00000000000070000000000012
  | 6, 37 => 0x1c0000000000011000000000001100000000000030000000000017000000000001900000000000180000000000011000000000001100000000000170000000000011000000000a11c000000000611e000000000610c0000000000011000000000a11e000000000001f000000000e11f0000000000005000000000001c00000000061120000000000018000005348421e000000000000f0000000000011000000000001d000000000000f0000000000003000000000000800000000000080000000000011000000000610b
  | 6, 38 => 0xa1110000000000007000000000000f000000000001c000000000000d000000000e10f000000000001900000000000050000000000000000000000000a000000000000f000000000000d0000000000008000000000000f000000000001c00000000000180000000000019000000000610f000000000001f0000000000016000000000000f0000000000018000000000000a000000000001300000000000170000000000011000000000001f000000000000f0000000000003000000000001d00000000000030000000000019
  | 6, 39 => 0x30000000000013000000000611a000000000001c0000000000013000000000001c0000000000008000000000001e000000000211c000000000001d0000000000019000000000001100000000000040000000000013000000000000d0000000000019000000000610f000000480a21000000000000040000000000011000000000000d0000000000008000000000000f000000000001800000000000100000000006111000000000e10f000000000001c000000000610c0000000000013000000000001d000000000000f
  | 6, 40 => 0x1f00000000000080000000000008000000000000d000000000001a000000000001f00000000000100000000000000000000000000400000000000110000000000003000000000000f000000000001c000000000001c000000000001800000000000110000000000018000000000001c0000000000019000000000001f000000000001c000000000001900000000000080000000000008000000000001c000000000001100000000000030000000000013000000000000b00000000000080000000000017000000000611a
  | 6, 41 => 0xe10f00000048022100000000000013000000000000a000000000001c000000000a10f00000000000100000000000019000000000000a000000000000b000000000000c000000000e11d0000000000013000000000000d000000000000c000000000001d000000000e11d00000028062100000000000008000000000611a000000000000a000000000001c0000000000019000000000000c00000000000060000000000012000000000001c000000000001f0000000000019000000000000a000000000a108000000000000d
  | 6, 42 => 0x30000000000017000000000001d000000000000d000000000a113000000000001100000000000000000000000018000000000211300000000000070000000000018000000000001300000000000130000000000019000000000a1130000000000012000000000001d0000000000006000000000000d000000000611e0000000000018000000000001300000000000080000000000019000000000001d0000000000007000000000001d000000000001200000000000010000000000011000000000001f000000000611a
  | 6, 43 => 0x30000000000012000000000000c0000000000007000000000611e000000000000300000000000110000000000012000000000001800000000000070000000000005000000000611d00000000061030000000000008000000000001c000000000001c000000000001c0000000000007000000000000000000000000080000000000017000000000000f000000000000b000000000001c000000000a113000000000000f000000000001800000000000100000000000018000000000001200000000000030000000000019
  | 6, 44 => 0x11000000000001d0000000000012000000000001c00000000000110000000000012000000000001a000000000611e000000000000f0000000000008000000000000a000000000001300000000000030000000000019000000000001c000000000001100000000000130000000000018000000000001c000000000001800000000000060000000000011000000000001300000000000030000000000003000000000001300000000000190000000000013000000000000a000000000000d000000000001c000000000e10f
  | 6, 45 => 0xa105000000000001100000000000110000000000016000000000000f000000000001c0000000000018000000000000f000000000000f00000000000180000000000012000000000a113000000000001d00000000000130000000000005000000000e105000000000001d000000000001100000000000030000000000017000000000000f000000000000f00000000000170000000000018000000000000f000000000610f0000000000016000000000001c0000000000016000000000001f00000000000180000000000003
  | 6, 46 => 0x180000000000015000000000611a000000000001c0000000000019000000000000f0000000000012000000000611a0000000000013000000000000d000000000611a000000000001f0000000000007000000000000e0000000000012000000000001c0000000000018000000000a113000000000001f00000000000080000000000018000000000001a0000000000008000000000001f000000000001d0000000000018000000000001c000000000001e000000000001d0000000000017000000000001f0000000000003
  | 6, 47 => 0x1c000000000001300000000000050000000000018000000000001f000000000001300000000000110000000000011000000000001200000000000070000000000013000000000a10f000000000001e000000000000f000000000001d000000000000c0000000000016000000000001a000000000001d00000000000130000000000019000000000000f0000000000006000000000001c000000000000f000000000001f00000000000080000000000010000000000001d000000000000c000000000000f000000000001c
  | 6, 48 => 0x611d0000000000012000000000a11c000000000000f0000000000011000000000001d000000000000d000000000e10f000000000001d0000000000006000000000e11d000000000000f0000000000019000000000000f0000000000011000000000001a000000000001d000000000001f000000000001d00000000000100000000002111000000000e11d0000000000006000000000000d000000000000e000000000000f0000000000016000000000000000000000000110000000000017000000000001a0000000000011
  | 6, 49 => 0x13000000000611d0000000000016000000000001a000000000000400000000000120000000000019000000000000f0000000000000000000000001800000000000170000000000019000000000000600000000000190000000000018000000000000b000000000001d0000000000003000000000001d00000000000190000000000003000000000001300000000000190000000000011000000000001d000000000000d0000000000010000000000000f000000000000d000000000001c00000000000180000000000011
  | 6, 50 => 0x120000000000015000000000001c0000000000019000000000001c000000000000c000000000a11c000000000000c000000000611a0000000000011000000000000c000000000001800000000000110000000012105000000000a113000000000001c000000000000f000000000001d000000000611a000000000001d0000003806210000000000000a000000000001c000000000001f0000000000019000000000000a000000000000f000000000e10f000000000001c00000000121050000000000005000000000001a
  | 6, 51 => 0x6112000000000001d00000000000180000000000013000000000001c000000000000d0000000000011000000000001300000000000130000000000011000000000001200000000000030000000000017000000000000f0000000000018000000000001c000000000001900000000000060000000000018000000000611e000000000001f000000000000300000000000110000000000012000000000000800000000000130000000000011000000000000f000000000000f000000000000800000000000030000000000007
  | 6, 52 => 0x3000000000001f0000000000002000000000000f0000000000019000000000000d000000000000f0000000000010000000000000f0000000000013000000000000f0000000006103000000000a105000000000001c000000000000a000000000000f000000000000a000000001210500000000000170000000000004000000000001c000000000000300000000061110000000000017000000000000f000000000000c0000000000017000000000001200000000000190000000000011000000000001c0000000000005
  | 6, 53 => 0xa11c000000000000c000000000000d0000000000012000000000a1130000000012105000000000001d000000000000f000000000000d00000000000180000000000003000000000001c000000000000b00000000000180000000000003000000000001d000000000001c000000000001d000000000001800000000000170000000002113000000000001f0000000000012000000000000f0000000000019000000000000f0000000000018000000000000f000000000611e0000000000003000000000001f0000000000008
  | 6, 54 => 0x1d000000000001200000000000030000000000012000000000001c00000000000180000000000000000000000001900000000000130000000000006000000000e11f000000000001700000000000110000000000017000000000001900000000000110000000000003000000000001e00000000000040000000000018000000000611100000000000030000000000008000000000001c00000000000170000000000017000000000000500000000000130000000000003000000000000c000000000e11f0000000000010
  | 6, 55 => 0x1f00000000000120000000000002000000000000f000000000001d000000000001d000000000001a0000000000011000000000001f0000000000018000000000000d0000000000019000000000001100000000000040000000000019000000000211c000000000000f00000000000030000000000010000000000000f000000000001f00000000000070000000000017000000000001d000000000001f000000000a1190000000000014000000000001c0000000000013000000000000d000000000001f0000000000011
  | 6, 56 => 0x4000000000000f000000000001f0000000000012000000000000b0000000000008000000000000d000000000000d000000000001a0000000000007000000000001d000000000e104000000008511e0000000000007000000000001a0000000000002000000000001e00000000000080000000000004000000000000a0000000000016000000000e11f00000000000110000000000012000000000e10f00000000000120000000002113000000000e1040000000000010000000000000300000000000180000000000011
  | 6, 57 => 0xb00000000000110000000000008000000000a1080000000000019000000000000500000000000160000000000013000000000001d000000000001c000000000000000000000000130000000000013000000000000d000000000001f000000000001f00000000000190000000000004000000000001f000000000001e00000000000120000000000011000000000a112000000000001d000000000001e0000000000003000000000000a000000000000f0000000000003000000000001e000000000e10f000000000e10f
  | 6, 58 => 0xf000000000211c000000000000f000000000001f00000000000130000000000006000000000a105000000000a111000000000000f0000000000017000000000001c000000000000b000000000001f000000000001d000000000e11f000000000001c000000000001c000000000000f0000000002113000000000001a0000000000017000000000000800000000000190000000000007000000000001300000000000130000000000011000000000001d00000000000110000000000003000000010c105000000000000f
  | 6, 59 => 0x12000000000001f00000000000030000000000003000000000000c000000000001d000000000000f000000000001c000000000001c000000000001200000000000070000000002111000000000001d0000000000010000000000a11e0000000000008000000000611a00000000000000000000000004000000000000b000000000000c000000000e11d000000000001c000000000001e0000000000003000000000001f00000000000030000000000011000000000001700000000000110000000000011000000000001d
  | 6, 60 => 0x170000000000003000000000001600000000000180000000006118000000000001f000000000000f0000000000013000000000000100000000000030000000000013000000000000f000000000000a000000000000d0000000000018000000000001200000000000180000000000011000000000001900000000000100000000000003000000000000d000000000001700000000000120000000000016000000000001800000000000070000000000018000000000001d000000000e11d00000000000120000000000019
  | 6, 61 => 0x16000000000611a000000000001e0000000000018000000000e11f00000000000110000000000011000000000001c000000000000f000000000000000000000000180000000002113000000000611a000000000000000000000000070000000000008000000000e11d0000000081110000000000001c000000000001a0000000000003000000000611e000000000a1190000000000010000000000001f00000000000170000000000018000000000001900000000000030000000000008000000000001d000000000001d
  | 6, 62 => 0x1800000000000180000000000004000000000000f0000000000008000000000001d000000000001d000000000e11f000000000000f000000000000f000000000001d0000000000003000000000e11d0000000000019000000000a11c0000000000004000000000001e000000000001e000000000001e0000000000011000000000001d0000000000011000000000000f00000000000110000000000019000000000a113000000000a108000000000000d000000000000d0000000000011000000000000f0000000000019
  | 6, 63 => 0x80000000000005000000000000d000000000000700000000000030000000000018000000000610300000000000080000000000018000000000611a000000000001f0000000000011000000000e11d000000000611a000000000211900000000000130000000000008000000000001c0000000000012000000000000d000000000001f000000000000f00000000000080000000000004000000000001c000000000611e000000000611e000000000000f00000000021190000000000011000000000a1130000000000008
  | 7, 0 => 0x11000000000001f00000000000100000000000012000000000000e000000000000f000000000001c000000000001f000000000001e000000000001a00000000000050000000000011000000000000f0000000000011000000000000f000000000001d000000000001d000000000001f000000000001a000000000001d000000000001e000000000001a00000000000190000000000005000000000001f0000000000008000000000000e0000000000013000000000000f000000000001a0000000000012000000000001e
  | 7, 1 => 0x18000000000001d000000000001f000000000001f0000000000012000000000001a00000000000050000000000018000000000000f00000000000100000000000018000000000001e000000000000f0000000000011000000000001e000000000001a000000000001a0000000000006000000000001f0000000000013000000000001f000000000000f000000000001d000000000001d0000000000011000000000000f000000000000f000000000a110000000000001a0000000000012000000000000f0000000000013
  | 7, 2 => 0x19000000000001000000000000130000000000013000000000001f0000000000018000000000001f000000000001f0000000000003000000000001c0000000000008000000000001d0000000000013000000000001e0000000081110000000000000d000000000001a000000000000b00000000000110000000000008000000000000d000000000001d000000000000d000000000611e0000000000012000000000001c000000000001e0000000000011000000000001a000000000001c00000000000120000000000012
  | 7, 3 => 0x1c000000000000f000000000001f0000000000011000000000001300000000000110000000000013000000000001d000000000001e000000000000c000000000001d000000000001e000000000e110000000000001c000000000001a000000000001f000000000000f000000000000b000000000000f000000000001f000000000001d0000000000010000000000000f000000000001c000000000000f000000000001f00000000000190000000000018000000000001d000000000001f0000000000013000000000001f
  | 7, 4 => 0x1d000000000001d0000000000013000000000000f000000000000f000000000001c00000000000110000000000018000000000000f000000000001e0000000000013000000000001d000000000001c000000000000d0000000000018000000000001d000000000001a00000000000040000000000013000000000001a000000000000a0000000000012000000000001d000000000001f00000000000080000000000005000000000001f0000000000011000000000001a000000000000800000000000190000000000018
  | 7, 5 => 0x1f000000000001f000000000001d0000000000003000000000001d000000000001e000000000000f00000000000190000000000005000000000000500000000000050000000000019000000000001d000000000000c00000000000100000000000012000000000001a000000000001f000000000001a0000000000005000000000001d000000000001c0000000000011000000000001d000000000001a000000000001a000000000000d000000000001d000000000001e000000000000f000000000000f0000000000003
  | 7, 6 => 0x1f000000000000f00000000121100000000000013000000000000e0000000000018000000000001f0000000000011000000000001f000000000000f0000000000011000000000000f000000000000a00000000000050000000000011000000000001d000000000001a0000000000010000000000001a000000000001e000000000000f000000000000c000000000001f000000000000f00000000000190000000000011000000000e110000000000001f0000000000012000000000001a0000000000008000000000001f
  | 7, 7 => 0x13000000000001e000000000001e0000000000019000000000001f0000000000019000000000000b000000000001d000000000000f000000000001f00000000000130000000000008000000000000f000000000611000000000000050000000000005000000000001d00000000000080000000000010000000000000f0000000000005000000000001f0000000000008000000000001d000000000001d000000000001e0000000000019000000000001e000000000001d0000000000013000000000000d000000000611e
  | 7, 8 => 0x1211000000000c4110000000000001f0000000109110000000000001f000000000000f0000000000013000000000001100000000000030000000000013000000000001f000000000001d000000000001300000000000180000000000018000000000001a0000000000018000000000000f0000000000011000000000001300000000000110000000000005000000000000f000000000001a00000000000130000000000012000000000001c00000000000130000000000013000000000001f0000000000004000000000001f
  | 7, 9 => 0x1200000000000130000000000013000000000001a000000000001e000000000001f000000000001900000000000050000000000003000000000001000000000000130000000000013000000000001d000000000000c0000000000013000000000001f000000000001e00000000000180000000000004000000000000f000000000000b000000000001a000000000001c000000000001a000000000001e000000000001e000000000000d0000000000019000000000001f000000000001d00000000000130000000000011
  | 7, 10 => 0x1900000000000120000000000013000000000001f000000000001d000000000001a000000000001f0000000000019000000000001a000000000001d000000000001c000000000001a0000000000013000000000000f000000000001f000000000001a00000000000130000000000011000000000000f000000000000c000000000001e0000000000013000000000001e0000000000010000000000000f00000000000130000000000012000000000000f000000000001f000000000001f0000000000012000000000001f
  | 7, 11 => 0x130000000000011000000000000f0000000000008000000000001d000000000001a000000000001f0000000000004000000000001a000000000001d000000000001f0000000000003000000000001f000000000000f000000000a110000000000001a000000000000d000000000000f000000000001d00000000000110000000000018000000000000f00000000000110000000000011000000000001d0000000000008000000000000500000000000030000000000018000000000001d000000000001a0000000000013
  | 7, 12 => 0x120000000000013000000000000f000000000611e0000000000005000000000001d000000000001d0000000000003000000000001e000000000001a000000000000f0000000000011000000000001d00000000021100000000000013000000000001f000000000001d00000000000190000000000011000000000001d000000000001f000000000000f0000000000010000000000001f0000000000013000000000001d000000000001d0000000000010000000000001a000000000000500000000000110000000000018
  | 7, 13 => 0x13000000000001f000000000000d00000000000100000000000013000000000001d0000000000013000000000001a000000000000f000000000001d000000000001e000000000001e0000000000012000000000000f000000000001d000000000000f000000000001e0000000000010000000000000300000000000120000000000005000000000000d0000000000012000000000001f000000000001a000000000001e000000000001200000000000130000000000005000000000000d000000000001c000000000001f
  | 7, 14 => 0x1d0000000000013000000000000f0000000000013000000000001000000000000190000000000011000000000001c0000000000013000000000001d000000000000f000000000001e000000000001a000000000000f0000000000013000000000001100000000000080000000000013000000000000f000000000000f000000000001a0000000000019000000000001a000000000000f0000000000011000000000001e000000000001d00000000000100000000000012000000000001d000000000001f0000000000013
  | 7, 15 => 0xf000000000001d00000000000130000000000018000000000001a000000000000f000000000000f000000000001e0000000000003000000000000f0000000000019000000000001100000000000080000000000004000000000001d000000000001d000000000001a000000000001f000000000001a0000000000008000000000000c000000000001f000000000001f00000000000130000000000011000000000001c000000000001c0000000000012000000000001d0000000000011000000000001d000000000000b
  | 7, 16 => 0x1f000000000001f000000000000f00000000000130000000000005000000000001d0000000000018000000000000f0000000000019000000000001300000000000050000000000008000000000000b0000000000013000000000001a000000000001e0000000000008000000000000d000000000001e0000000000000000000000000f0000000000019000000000001d000000000000f000000000001c0000000000013000000000e110000000000001e000000000001d000000000001a00000000000110000000000019
  | 7, 17 => 0x1a000000000001f000000000000f0000000000018000000000001a000000000001900000000000110000000000013000000000a11e0000000000012000000000001f000000000001d0000000000003000000000001d00000000000180000000000019000000000001c0000000000013000000000a110000000000001d00000000000130000000000012000000000000e000000000000f000000000000500000000000130000000000011000000000001d000000000000f00000000000040000000000019000000000001d
  | 7, 18 => 0x1100000000000130000000000013000000000001a000000000000f0000000000016000000000001f000000000000c00000000000130000000000018000000000001f000000000000f0000000000013000000000001c00000000000050000000000003000000000001c0000000000008000000000000d00000000000180000000000019000000000001300000000000190000000000008000000000001300000000000180000000000005000000000611a0000000000012000000000001e000000000000f000000000000d
  | 7, 19 => 0x1a000000000001a0000000000013000000000001c0000000000011000000000000c000000000000f000000000001a000000000001a000000000001f000000000001e000000000000f000000000001e00000000000130000000000012000000000001e000000001211000000000000110000000000003000000000001800000000000190000000000018000000000000f0000000000008000000000001d000000000001e0000000000008000000000001a000000000001e0000000000019000000000001e000000000001e
  | 7, 20 => 0x13000000000001a000000000001c0000000000012000000000000f000000000001d0000000000003000000000000f000000000001f0000000000018000000000000f0000000000008000000000001e0000000000008000000000001e000000008411e00000000000030000000000004000000000001e000000000001d000000000001c000000000000800000000000190000000000018000000000001f000000000001d000000000001a000000000001f000000000000f0000000000013000000000000f0000000000004
  | 7, 21 => 0x120000000000013000000000001d000000000000f00000000000180000000000013000000000001300000000000120000000000019000000000001100000000000110000000000003000000000001f00000000000110000000000000000000000001a0000000000013000000000000b0000000000013000000000001200000000000050000000000011000000000001d0000000000003000000000000f0000000000010000000000001d000000000001d000000000001c000000000000f0000000000005000000000000f
  | 7, 22 => 0x190000000000013000000000001f0000000000005000000000001d0000000000019000000000001d000000000000f000000000000f00000000000130000000000018000000000000c0000000000008000000000001d000000000001e000000000001c000000000001d000000000001e000000000611e00000000000110000000000012000000000000d0000000000013000000000001c000000000001f000000000000f000000000001a00000001011100000000000005000000000001d000000000001e0000000000013
  | 7, 23 => 0x1f000000000001d00000000000120000000000004000000000a110000000000001a000000000001d000000000001d000000000000f000000000001d000000000001a000000000001d000000000001f000000000001d00000000000130000000000013000000000001f000000000001f000000000001e000000000001300000000000120000000000012000000000001d0000000000012000000000001c0000000000013000000000001d000000000000c000000000001a000000000001a000000000001f000000000001a
  | 7, 24 => 0x1c000000000000f00000000000050000000000005000000000001e000000008411e00000000000190000000000003000000000001a000000000001f00000000000110000000000018000000000001d0000000000010000000000001a0000000000012000000000000f000000000001e0000000000013000000000001d000000000001a000000000001d000000000000f000000000001d000000000000f000000000001d000000000000f000000000001d000000000001e000000000000b000000000001e000000000001f
  | 7, 25 => 0xc000000000000f000000000000f0000000000004000000000001c000000000001d000000000001d000000000001d000000000000c000000000001f00000000000190000000000013000000000000f00000000000120000000000004000000000001d000000000001e0000000000013000000000001e000000000001e000000000611a0000000000010000000000001f000000000001a00000000000080000000000013000000000000f00000000021100000000000019000000000000c000000000001d000000000001d
  | 7, 26 => 0x1d00000000000180000000000013000000000001c000000000000d000000000000f000000000001e0000000000005000000000001a0000000000018000000000001e000000000001d0000000000011000000000001d000000000000d000000000001a000000000000f000000000001a000000000611e000000000001d000000000000f000000000a11e0000000000011000000000001a00000000000050000000000003000000000001a000000000000f0000000000005000000000001300000000000180000000000018
  | 7, 27 => 0x130000000000017000000000000f00000000000050000000000018000000000001000000000000130000000000011000000000001f0000000000018000000000001e000000000001d00000000000130000000000003000000000000f000000000001d000000000001f000000000001a000000000001e000000000001e000000000001e000000000001e000000000001f00000000000130000000012110000000000001f000000000000b0000000000004000000000000f0000000000011000000000001e0000000000013
  | 7, 28 => 0x18000000000000f000000000000d000000000001300000000000100000000000012000000000001a000000000001f0000000000013000000000001a000000000001d000000000000f000000000001d000000000001d000000000000300000000000050000000000012000000000000f000000000001d000000000001d0000000000018000000000001a000000000001d0000000006110000000000e110000000000001d00000000000110000000000005000000000001a000000000000f000000000000f000000000001d
  | 7, 29 => 0x1f000000000001d000000000001e000000000001a000000000000b000000000001a000000000001e00000000000110000000000005000000000001e000000000000f0000000000010000000000000700000000000050000000000011000000000000f0000000000019000000000001d000000000001d000000000001c000000000001a000000000001f000000000001a000000000001f00000000c4110000000000001e000000010911000000000000190000000002110000000000000500000000000130000000000008
  | 7, 30 => 0x12000000000001d0000000000018000000000001f000000000000f000000000001a000000000a11e000000000000f000000000000d0000000000003000000000000400000000000130000000000017000000000001d000000000001100000000000130000000000004000000000001d000000000001c000000000000c000000000001e000000000001d000000000001d000000000001a0000000000013000000000001f00000000000180000000000018000000000001d00000000000110000000000013000000000001f
  | 7, 31 => 0x1c000000000001d0000000000012000000000001f00000000000130000000000011000000000001e000000000a110000000000001c000000000000f00000000000100000000000007000000000000f000000000001f000000000001a0000000000008000000000001c0000000000012000000000001a000000000001f000000000000f000000000000800000000000100000000000012000000000001d00000000000120000000000013000000000000f000000000001e0000000000012000000000611a000000000000f
  | 7, 32 => 0x1c000000000000f0000000000013000000000001f000000000611a000000000001f0000000000019000000000001d00000000000130000000000013000000000001d000000000001f00000000000110000000000003000000000000c000000000001d00000000000050000000000008000000000001e000000000001d000000000000f000000000001a0000000000013000000000001d0000000000008000000000001a00000000000110000000000011000000000001d
  | 8, 0 => 0x10000000000001e0000000000010000000000001a000000000001000000000000100000000000010000000000001e0000000000010000000000001a000000000001a00000000000100000000000010000000000001a0000000000010000000000001e000000000001000000000000100000000000010000000000001e000000000001a00000000000100000000000010
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_161 roots_161 L_161 s ws hint
  | 1 => checkCutEntry dom_215 roots_215 L_215 s ws hint
  | 2 => checkCutEntry dom_237 roots_237 L_237 s ws hint
  | 3 => checkCutEntry dom_239 roots_239 L_239 s ws hint
  | 4 => checkCutEntry dom_240 roots_240 L_240 s ws hint
  | 5 => checkCutEntry dom_242 roots_242 L_242 s ws hint
  | 6 => checkCutEntry dom_296 roots_296 L_296 s ws hint
  | 7 => checkCutEntry dom_320 roots_320 L_320 s ws hint
  | 8 => checkCutEntry dom_323 roots_323 L_323 s ws hint
  | 9 => checkCutEntry dom_431 roots_431 L_431 s ws hint
  | 10 => checkCutEntry dom_440 roots_440 L_440 s ws hint
  | 11 => checkCutEntry dom_458 roots_458 L_458 s ws hint
  | 12 => checkCutEntry dom_467 roots_467 L_467 s ws hint
  | 13 => checkCutEntry dom_480 roots_480 L_480 s ws hint
  | 14 => checkCutEntry dom_482 roots_482 L_482 s ws hint
  | 15 => checkCutEntry dom_483 roots_483 L_483 s ws hint
  | 16 => checkCutEntry dom_485 roots_485 L_485 s ws hint
  | 17 => checkCutEntry dom_539 roots_539 L_539 s ws hint
  | 18 => checkCutEntry dom_563 roots_563 L_563 s ws hint
  | 19 => checkCutEntry dom_566 roots_566 L_566 s ws hint
  | 20 => checkCutEntry dom_623 roots_623 L_623 s ws hint
  | 21 => checkCutEntry dom_629 roots_629 L_629 s ws hint
  | 22 => checkCutEntry dom_647 roots_647 L_647 s ws hint
  | 23 => checkCutEntry dom_682 roots_682 L_682 s ws hint
  | 24 => checkCutEntry dom_683 roots_683 L_683 s ws hint
  | 25 => checkCutEntry dom_700 roots_700 L_700 s ws hint
  | 26 => checkCutEntry dom_701 roots_701 L_701 s ws hint
  | 27 => checkCutEntry dom_704 roots_704 L_704 s ws hint
  | 28 => checkCutEntry dom_709 roots_709 L_709 s ws hint
  | 29 => checkCutEntry dom_710 roots_710 L_710 s ws hint
  | 30 => checkCutEntry dom_725 roots_725 L_725 s ws hint
  | 31 => checkCutEntry dom_727 roots_727 L_727 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_728 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_161 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_215 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_237 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_239 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_240 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_242 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_296 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_320 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_323 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_431 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_440 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_458 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_467 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_480 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_482 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_483 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_485 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_539 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_563 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_566 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_623 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_629 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_647 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_682 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_683 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_700 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_701 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_704 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_709 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_710 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_725 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_727 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_728 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_728 goalM u ys) : RunD dom_728 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_728 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 2 → (Z 3) i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 2 → (Z 3) i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 7 → (Z 4) i = true := span_ok (by decide +kernel : span (Z 4) 7 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 7 → (Z 4) i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → (Z 5) i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_12 : ∀ i, 12 ≤ i → i < 24 → (Z 5) i = true := span_ok (by decide +kernel : span (Z 5) 12 12 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 24 → (Z 5) i = true := (range_split z5_0 z5_12)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 12 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_12 : ∀ i, 12 ≤ i → i < 24 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 12 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_24 : ∀ i, 24 ≤ i → i < 36 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 12 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_36 : ∀ i, 36 ≤ i → i < 48 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 12 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : ∀ i, 48 ≤ i → i < 60 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 12 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_60 : ∀ i, 60 ≤ i → i < 72 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 12 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_72 : ∀ i, 72 ≤ i → i < 84 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 12 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_84 : ∀ i, 84 ≤ i → i < 96 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 12 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_96 : ∀ i, 96 ≤ i → i < 108 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 12 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_108 : ∀ i, 108 ≤ i → i < 116 → (Z 6) i = true := span_ok (by decide +kernel : span (Z 6) 8 108 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 116 → (Z 6) i = true := (range_split z6_0 (range_split z6_12 (range_split z6_24 (range_split z6_36 (range_split z6_48 (range_split z6_60 (range_split z6_72 (range_split z6_84 (range_split z6_96 z6_108)))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 12 → (Z 7) i = true := span_ok (by decide +kernel : span (Z 7) 12 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_12 : ∀ i, 12 ≤ i → i < 24 → (Z 7) i = true := span_ok (by decide +kernel : span (Z 7) 12 12 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : ∀ i, 24 ≤ i → i < 36 → (Z 7) i = true := span_ok (by decide +kernel : span (Z 7) 12 24 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_36 : ∀ i, 36 ≤ i → i < 48 → (Z 7) i = true := span_ok (by decide +kernel : span (Z 7) 12 36 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 60 → (Z 7) i = true := span_ok (by decide +kernel : span (Z 7) 12 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_60 : ∀ i, 60 ≤ i → i < 72 → (Z 7) i = true := span_ok (by decide +kernel : span (Z 7) 12 60 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_72 : ∀ i, 72 ≤ i → i < 84 → (Z 7) i = true := span_ok (by decide +kernel : span (Z 7) 12 72 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_84 : ∀ i, 84 ≤ i → i < 96 → (Z 7) i = true := span_ok (by decide +kernel : span (Z 7) 12 84 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_96 : ∀ i, 96 ≤ i → i < 102 → (Z 7) i = true := span_ok (by decide +kernel : span (Z 7) 6 96 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 102 → (Z 7) i = true := (range_split z7_0 (range_split z7_12 (range_split z7_24 (range_split z7_36 (range_split z7_48 (range_split z7_60 (range_split z7_72 (range_split z7_84 z7_96))))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 12 → (Z 8) i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_12 : ∀ i, 12 ≤ i → i < 23 → (Z 8) i = true := span_ok (by decide +kernel : span (Z 8) 11 12 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 23 → (Z 8) i = true := (range_split z8_0 z8_12)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 1 → (Z 9) i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → (Z 9) i = true := z9_0
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
  scr dom_728 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD dom_728 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_728 roots_728 goal_728 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_728 goal_728 := by
    have h0 : isConstB dom_728 goal_728 = false := by decide +kernel
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
end S_728
theorem low_728 : Lower dom_728 roots_728 goal_728 10 := S_728.noCircuit
def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_728_bits : ∀ r : Fin 64, roots_728.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_728_lt : ∀ r : Fin 64, dom_728.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_728 T)
    (hlow : Lower dom_728 roots_728 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_728, Avail mask256 roots_728 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_728 hfan 0 roots_728 roots_728 rfl hsup0
  set out := (execN C.gates roots_728).getD C.output 0
  have hout : out &&& dom_728 = T &&& dom_728 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_728_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_728 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_728_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_728).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_728)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_728.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_728 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_728).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_728 &&& mask256 = dom_728 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_728 = T &&& dom_728 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_728, hd63, hout]
  have hnc_m : ¬ IsConst dom_728 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_728 roots_728 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_728, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_728 roots_728 0 roots_728 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega


def targetFn : (Fin 6 → Bool) → Bool := fun x : Fin 6 → Bool => Nat.testBit (4007717024 * 2 ^ 32 + 3974160544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 14]⟩], 15⟩
theorem witMono : PEqualNP.MetaComplexity.Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem witEval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = targetFn x := by decide +kernel
theorem witSize : wit.size = 10 := rfl
theorem hT6 : ∀ r : Fin 64, goal_728.testBit r.val = targetFn (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 targetFn t → 10 ≤ t :=
  lower_to_circuit6 targetFn goal_728 10 hT6 (by unfold IsConst; decide) low_728
end PEqualNP.Outside.L_meta_16205_aux

open PEqualNP.Outside.L_meta_16205_aux in
theorem PEqualNP.Outside.L_meta_16205 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717024 * 2 ^ 32 + 3974160544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717024 * 2 ^ 32 + 3974160544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨wit, witMono, by have hl := lower s hs; have hz := witSize; omega, witEval⟩
