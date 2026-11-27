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

namespace PEqualNP.Outside.L_meta_12809_aux

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

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xe888888088808880e888888088808880e888888088808880e888888088808880
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_63
def pairsG : List (Nat × Nat) := [(3, 7), (3, 11), (5, 7), (6, 7), (9, 11), (10, 11), (13, 15), (14, 15), (19, 23), (19, 27), (19, 51), (21, 23), (22, 23), (25, 27), (26, 27), (29, 31), (29, 61), (30, 31), (30, 62), (35, 39), (35, 43), (35, 51), (37, 39), (38, 39), (41, 43), (42, 43), (45, 47), (45, 61), (46, 47), (46, 62), (49, 51), (50, 51), (53, 55), (53, 61), (54, 55), (54, 62), (57, 59), (57, 61), (58, 59), (58, 62), (60, 61), (60, 62)]
def r1sG : List Nat := [3, 3, 5, 6, 9, 10, 13, 14, 19, 19, 19, 21, 22, 25, 26, 29, 29, 30, 30, 35, 35, 35, 37, 38, 41, 42, 45, 45, 46, 46, 49, 50, 53, 53, 54, 54, 57, 57, 58, 58, 60, 60]
def r2sG : List Nat := [7, 11, 7, 7, 11, 11, 15, 15, 23, 27, 51, 23, 23, 27, 27, 31, 61, 31, 62, 39, 43, 51, 39, 39, 43, 43, 47, 61, 47, 62, 51, 51, 55, 61, 55, 62, 59, 61, 59, 62, 61, 62]
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := [21016168182539, 21020547101447, 50771819117831, 62900116592445, 38715611024179, 66220766071614, 21118844733235, 66199240967997, 62866026858301, 58398992436029, 21123156543283, 66203519092542, 66099868796734, 66216487947069, 59602271878451, 3355329770247, 21016168179467, 38715611023155, 21016235281159, 21020479981323, 66215830292285, 66198650423101, 62797038946109, 64003922134846, 66095573829437, 66220125259582, 58467980348221]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 3 => 1
  | 4 => 60
  | 5 => 359
  | 6 => 665
  | 7 => 311
  | 8 => 23
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x5edd39b
  | 4, 0 => 0xfaa7350be4c1184eceae6125cbf184b8bd1f4e2ab398c03badb969fb9ed1392797c9f6f189cb7319844512cb7a1258d179da04ee716393df6b99e3b96af50737687626c4663cf0fc651dc74164cec92a63873c0d51f5ab0a51ee4110517ebd7d504f5d9747f242db3efb8f983ef707463df6faeb392963f5385f57e8370429e3365ef5a332fb60103289a670319923892ee48cd42ccd94a02c785ca029cfae08293ab4ef260be16423f41cb2226937b01f9297ae1e378dd01d71c7d21c3888fd19c093eb194f856f181b4e5f15a5a3d6154505da1353572111bb567e11a0e8a80fd9ff800c50502409b9a32203ff4dc6
  | 5, 0 => 0x12aedc881220ba6a1204b2ed11ccb39b11bb567e1145f7fe1134901710ec99810fe809f70f24eb560ed350d10e7391840e64ab280e5043ca0e47c5880dfae9110d705f300d534c1d0d3ac95e0d22cc280c7d68810c3d1f240b8c9cac0b2249f90a4833a80a4324ea0a3038aa09b9e4fc09a3f06a08f9a4ce08a962ad08a003e0081e512d0774fbbe06bae55606450e1905b1b8b405936098055ce66d0556078a054891ef0513af4e05137fcd04fce84204bd4b320395f7f90363bbce0361363c0337d55a03212d5d02f244d602981025021861f701db102701dab67e01c5ab4b01ab15a201635eb400a4805e007cd476006091b30057a0580046b25a000559de
  | 5, 1 => 0x2a99360e2a7824bf2a72183027aa2d902757e39d25fce28825e44e9f25e29e3525a96f76253c7a892484e05c248059c2247c3a5b2461742923d05e6223a0ad62236aca32234d0270234ab6fd22d369fe22aa62f8224e653820cca5462080a39c1f7fe3e71f53d3691e8b82e01e5af5441e3eb2e31dafc3b31cf00d9c1cddf3bf1c5d27d21c5ac3671c28af8e1b88dcfe1b565f6d1b037fbf1aaf7bc719fece8319c0f4d11953569a1951043b18cdaeae18a90caa18513222184df1b01809cf1f17e17a9617a232b6174beebc170a3c5c16d8acb01668af7115b1f5cf154505da14f6a7ca14cdedb6148da95514262f99139cb2d51397f4e11365ef6b12e39cd6
  | 5, 2 => 0x452b81f9436ef8c0433edd3042d579ee42c260a442c06dde42bde9c9422b74c541bd1d3e40b6d91240a41b50408bfeea3faefc4c3ebea1fb3d89c89c3d50ebad3d11f6e93c80b75f3c700c1c3bc8dd5e3bb920683b6a63823b5bc9873ac8bdcf3a71c9473a20965238cd392338b8d5e1387c38bc3775eb6d370429e33626d2e1358cc6033527af5f3451ccbe33d3ded733a45eb433720c633311326232b153c1327decf93254a61f323de1ff3239ae073201706d3140b15530fc2d0730d89a27308751512efb99702e9663ac2e775a852e6c5e922e35c5b02e24777a2e117fd72d5051d02c705a442bda491a2bcc43f52b8a10072acb12cd2ac16eff2aac1654
  | 5, 3 => 0x69e9f08b69af879a69697bab69401d6d692fd07d680b5c8f66eabf11667b39c8663cf0fc65cfe06064644194640f09946390efa6615edc8b6146207c60235d455eee48cd5ded8dd65dab40105c5f36c65b7680b059a1086558cc880857ec4f6e57db28c05724b82156f4306c56e2cfa356a68342550ba0345422079253ae37c0527bcfbb51fca04c51b8d50b5177c949515740df50f4b4604ff4e9b94fd0aa7c4f7691164f3008454ef60d994ee7cdd04eac38834e2010d34e1be3034da542274cb329de4c2967db4bec1fe64b89ae064b3714294af11f1649627409494409c148defba348a9e38a482d66fe4728239846ebe8b7461173c945be547645964472
  | 5, 4 => 0xa2bc32efa2bc19279f92cc759e7d56909e7620179e31a5e99d5112cd9d35d2a19b131a509a9c7c1898e3d4ea95361f9d92cac4c491e8f7f291adff3d8ff7d1db8f1967a78c14f5d38bdc310389ecf1ae89ec6df889c95ae38979998388b5d470887cddca87b75d9c8632d5a185f71c318481679e83910ea3824c57427d55c5f97c83a3f07c77fbe37c69194a7c36d76c7bf64e177ba687fe7b6656ba7aad330c781d031f77911c5a776dc60376fabe85768db43a7577ab3974cea1a273f4647a73c077677364b668732eed6770c010e97002141b6f9f88136e9ad6d76e7a42a76db6c1556c6f90d26bd2420b6bacde976ae66ae06acb5a966a6f7d536a205364
  | 5, 5 => 0xfdb1d824f44fdf7ff43c8121ed186622e9a02480e0028c83deae138bde88764cde12a3ecdb881855db4dc9dedaceddf5d91d6ff2d668d93dd5e2c384d563d79bceae6125c2d15d0ac123b9fbbcd6f7dabcaf94abbcadac1cba88e302ba6be8b4b9c8a2d4b82cf7fab4735fa3b45d9c7ab2c25278b2c1f1a0b1a905c5adf7620eab428b96aaf2a919a93f7f8aa78367dda6df5301a5d7853ca39cac43
  | 6, 0 => 0x7ca473b07b30a1107750516074b083a073d1f77072fdee70714721506d2122c06c3b88006c1158506b145b80666a81306450e1905d95a3c05d8c8cc05d7dbca05b1b8b405a1a02c059ba72f058f12e905894db3058925520588c8840572fd2904eb973d04c8037f04bd0c40042e129c0421d99b0416becf03c3830403b968f3033bf95e03390c9c0300443b02b9431802b2f26e02a39ba3028ab1770289093f0256d3aa023d9882022a64a702221e4f0209febc01f4cf2d01ddbaba01cf722601cad53701bc6d7101ba2cda0184f269017c03e30155d4ba014345790114c34d00f9ecac00b3d3a6007ecfe6006091b3005b15560048c28a001ab72000188ce6
  | 6, 1 => 0x11b9f326118e409511855c7b1129746d11283b241101235d10f1df1910d7dc3b108f084b101d9be00f87be240f8607800f580fab0f32dd910f24eb560f049ef50ef8e9660eaad6810e88f3790e6842d50e64ab280e5dfb780e3e29630e3dc2ca0e315ce00e0a487d0dc629f60da531e40d9324240d61d59e0d336c450d029c5c0ceb24ee0cc1ecfd0c915ea10c911a280c619c510c320ce60c284bd40bf479e70bbf7f160bace6f70b9fd0280b5e71440b5259ce0b3ab1930b27d9370b2387570b02d2a70ad843a20abe7fb40aacf85c0a8099210a46f97609e7339d093ec958090a547008f9a4ce08d4accd08c2704f087681f90868a080081db2930808d813
  | 6, 2 => 0x1c11ed331bfba1ca1be304ac1ba415431b91ef281b88dcfe1b7339e01b70195b1b6de8931b5344b21b0c02e11ae902d11acbcffd1ab829b41ab66b211a9bd5781a6411f11a541e8a1a4dd02c1a424978196d944c1948602e18f619b4187ad58f1815ff90180d672a180bf87117d199c017b0f9321799397717756584172f6a7a170cf7ac16cfc91c16add6a716a8b88d168a4359167ddc4e167355a21644c07f160fb2ea1608e1fd15dcee021580524015496be21517df681514c1ae14bb083914b92f5f14a76c121446ffbb143fff9814384d77140baa3e13e10bcc138490c31365ef6b134ce271131ec54912aff485125db833121f680d11e9b49b11e9570a
  | 6, 3 => 0x2764515a27556afe274196012739a6f32738855e2725b03626c9d23426611f0626440bf3262cb3b926138bfe25a90ed6258bd55524ec9f74247c3a5b2438e03e24351f32241a57b623fe402923ed99ff23c0ac8a2294b040222070782218decb21bee2802190c3b62166a824210f110320d8eeed206a6f2f20618403205feb5c205f7506200af9e31ff49c8d1fb418921faba52c1f8998871f2c5d711f24bd041f1841d71eb615ab1eac56f61ea2788a1e7f42021e49a9241e3951c51dde50e71dc7b6451da454901d76fecb1d2eb7181d2559541ce11e0b1cd3fa621cb082861cadfe4a1c5df1c11c547ba41c4c16371c414c1c1c39478a1c38c5e31c20602f
  | 6, 4 => 0x31c7941031c34df93199cc80315048b0313eb1863122743a30c9372d30900882308c59bc305e14f23051389a303cae92303a81a430012b502fc96c862fc4bf852fb567752f69df6a2f2d607d2ebc379a2ea2b5a52e9ff0d82e9f411e2e35c5b02df73e062defd2882dbead8c2d8d3d522d7172bd2d2ac42e2d16ef6f2cfa37c12cdd0f7c2cdd085c2c56af412c34d88e2bdf8d6e2bd45cac2bc891372b117a402b0b13fa2af572c32aac16542a7fbee72a57a5ce2a254fed2a12d5c42a08619a29dd595729c8b07a29a3ee1d2961d54d296061ff287d9ca1287b4037284cb81e2836cc352815ab2c27fcc1e627e0c82127d2f5e627c4aa7e27c410a727b1530c
  | 6, 5 => 0x4063ddc440119fd73fd9b1b93fa4d7023f6a770e3ee324c23eb82e3d3e9a2f4c3e6658373e5a072c3d733a693c916d383c90451b3c6079633c554e053c3dc2463b22fcdf3ab979343a9fe6c03a88f1ca3a0d104639bd651c397902d739716372392526923918d40d390e4dff39079890388b621a387c38bc3870a3bd386653f63844d55c37930c03376e270336b7527036a86d7336a521e4368d7a9435e80e9c35d065b935ceb39535914cc53544386834471f4334398f58340a477833ee865833e7e6b333cca16b33a44bf5337b589532ef8e5932dc791732d9cf0232d3d1e632b1b4a732653e1b324c56c0324416703241c41132037827320320a931d10409
  | 6, 6 => 0x519fd75651710c8a516cf89250f4b46050b0a09a50720bf0504aa8e95035d1cc5018152a4ff4e9b94fd6dd734fc67bf04f984ce74f3008454f17860a4f12affe4e5746b14de1a1a34d9f17f64d9d33444d099f2c4caf430a4c61ac554c442b364ba3472b4b8577db4b6c7c7d4b2ea1d54ae0400e4ac537ad4a945e904a681a0a4a3c980749ececdd4978112748f3efe348cde93a48aca91448a9e38a482d66fe475d1e684728239847023fad46e6871546e200e6468a0b834666783546501adf45611a1a452958364510f12844bd03cb447acfdd4423349743bbd2a3438a122e435f9ffb42f9b961425f7b26423e603641b975d341370a8b410c188940fb71db
  | 6, 7 => 0x68c16a5268690594686750ec6782a6326710d0a9669601fd6679494b66466c1c65c44378656d9ae9651a27b1644fe68e6434957263c43aac637bc8af619aa360611e26d461145be8608433a360593d1e5fff957d5fb7118d5f989dc35f18c74d5ee6e06c5ee3b6a35ebba0685df7cafa5ddebb5a5c5df84f5c110d6a5be5ecce5aa1857c5a3d9da15a0333f359a798e859581168589fbc2258268a95580dcbb357af61d15793a55e56e2cfa356dc12e456a607105697785c567954a955d854755563e75854a9e03e5474a0b3545b23585429b2e25412131b53f1705b53ccd0cd53b97da5539d26a55362891d535fc450535a722952349c93522c7b2351a995b7
  | 6, 8 => 0x878b96ad876fda3a8767577085b6bdc7856050a8849d9e6d8405e7be83bc1a6c833bf92c82a0477082909bf48204d3e080fc1c658064302e80503df5803535357fa4b7377f54a2197eed2a5c7e9ae1647e589f2c7dd412bf7dd0f2d27d55016a7c81af7c7c204efc7aaab1377a5496bd7a36e052771a120876de4dac7582840074d7e8a27490092272f2767b7282a47972557d8471ec356971c972a471c161a871153b4b70cbe89670631aa3701577f76fd38f796f9f88136f2502c86ec2106c6e9ad6d76db0b6f26dab37716ca281246c6644956b6c8f916aed60226aa994e16a4800b56a32bf046a0ed6dc69e5743669c91d3669c0f0c5695537b368ede175
  | 6, 9 => 0xc3e368efc35e18c0c171b1c1c16007d7c07427b3c0463d45bdf31266bc8d6c19bc43f8dcbbacd8fdb9f0341ab9c8a2d4b82cf7fab4f49c6db45d9c7aaecdc3e0ae07934fadb0479bad0983e2acc0721fac5de458ab428b96aad9b7c8aa76913fa962bd86a8c54099a610ef9ba39cac43a2dd2dcea2bc1927a26a5959a1a5a780a1803036a16d9da0a0a81d72a03f4f7f9f2395779ee7dc079defce909d029a6e9c3aa1269b0a54f997b249f396557e2795e497fb95d50ec394e70ded949db779939df2e29381e3e49356040193364bff9034c8f58ff7d1db8db4dc618cfe41508cb1373d8c1fad3d8c0ae9cc89ec6df88958254e88b44c9e87ea008f87b75d9c
  | 6, 10 => 0xfd389549fad0ddddf7a1f9bfea719b50e0a6f220de88764cdbc21ce0db2881fcdb1c106edaceddf5da52c61bd91d6ff2d5a05481d4e7bfc1d2fc8c9ed2c766c7d233290cd11db7d0d09a805ccd4315cacbb3124ec97fa4e6c5b1439fc47e3127c417ea21
  | 7, 0 => 0x14970abc13fbe9a813c19db3137421cd135da5e11358c9d4132603861280cdab1194a2e3115b7e701129746d110a7b0210c409401092b99510525497100c404f0fa5577e0f7502090efdc70d0ee916120e64ab280e5278880de3a1660d50ac880c915ea10c4842230c284bd40c095b5b0be881c10b34e5f00abb2fb70a7b331e09cdaf3e09b00b89099654760983f2f7097ac802093523ce08f9a4ce08cd61800877ec1907ea2df907adf39f07750516072a3742070a5de60706e3ce068b89c50673128c0626add00610c14605d7dbca056864e80560a131054f7abc050541f102a39ba30211d02401fb1b4d01f747e3014fe3b100f9ecac005e47fc0022acaf
  | 7, 1 => 0x27f55ecb27b1530c27556afe272ce78225b2acd32571ba9b25525c27248c1393242b71692414472d23c9037822ff012722ddff69227e86ad227d9fcb22207078220989fe21fb144621c56ca32166a8242159605620f997e920d8eeed20bbbd8920a3c9e71fa2058e1f63f61d1f1e1eed1ec988a21ea2788a1e8c67051e7fd2bf1e7a0d891e63bcff1e49a9241dd844901d76fecb1d1ed2721bf104111baa02ee1ba3b2441b945b791b7b714d1b79c9151b1b247d1ae902d11ac031fc1abb950d1aad2d471a6cc3b91a4dd02c194bd52c1939826019094cbc18cbf15d1837058d182711de17cc2c1016b352a01682db831613608d15ce6ef2153ae11114dd5e4e
  | 7, 2 => 0x4ac537ad4a945e90492b417a48a6274b47acf7704790b0ae46e7fddc468a0b834666783545f8be5b442334974294adf3425ccc6a40d187f7403255d73f0428283e99ceac3d29a0143d25df083b96de8d3a5767fa39c9aec3395243d9395034dc38a9965c3844d55c381d1d4738157cda36cf10bd368d7a943667bea13616192a35c4ba3835a1425c353cd60d35320bf2352a0760352985b93482aefe340a477833a8e98a333e900232dc791732653e1b31d10409319b41cd30d1ebeb30a1b908309008822f7b032f2f6e9c242f6415782f4696d72f241a4d2d982be82d37bf912c7550992c56af412c34d88e2b2ad3792ada16e02876c7562815ab2c27ff285d
  | 7, 3 => 0x82b9dd0c8083c11c807366087e5c15517e3e30727cb4fa8278f0555378895d9977d7a04277ac603e76cf7b30769b294275d13ab0754eb82574a561e172ee0719710447766fd38f796fccd2ba6f8e98726f6a147f6ec5caa06e1a7c1b6d1a72b86c8de67b6c5afc416c5084266b255c6969e5743669a16070695537b3692691a267fa326e673a496865fa5f0265c443786408632c63851e665fd4821e5f57380b5e01b0fe5d13f46d5c505fd15c19630b5c110d6a5a350b29589596d8574ac70256a6071055460ddb5379b1a0520993e351ff0dd5517c21f0516cf89251359532504ffde54fa812464f7e3a6a4cfb074e4ce2b44a4cdf462e4bcd38ed4b55fdf1
  | 7, 4 => 0xf34385f1ebed4c74ebb8269de0a6f220dea20375de88764cdc4ed896da627197da52c61bd534b8b2d2e0f3f0d11db7d0c5b1439fc5b131f5c3675115c35e18c0c1b6006fbc8d6c19bbacd8fdba966756ba70f00cb9c8a2d4aed557d1aec5ce99ac5de458aa901e68a6a59c37a5ef0126a2dd2dcea1a5a780a0a81d72a0609a10a0581746a03f4f7f9ea77d9d9c2cb9029954f004974dbe8196c4d29596557e2794366dc5937c99c2933c9f69900ad1de8adcf53f8aba327a8ab2217e8a05fb21878b96ad876fda3a86f41ea1869bf7478557046b8405e7be833bf92c
  | 8, 0 => 0xf34385f1dea20375ba9667569c2cb90263851e665f57380b5d13f46d5c110d6a513595324f7e3a6a4cfb074e4bcd38ed4b55fdf14ac537ad3a5767fa38a9965c3667bea127556afe1b945b79182711de1129746d0e64ab2800f9ecac
  | 9, 0 => 0x27556afe
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x7777777777777777000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000aa88aa88aa88aa88000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000ccccccc0ccc0ccc0000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa
  | 0, 1 => 0xaaaa88888888888800000000000000000000000000000000000000000000000000ff00ff00ff00ff000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c8000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000000000ffffffffffff000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000ee00ee00ee00ee00
  | 0, 2 => 0xec00ec00ec00ec00000000000000000000000000000000000000000000000000aa888888aa888888000000000000000000000000000000000000000000000000fffffff0fff0fff0000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000c8c88888c8c88888000000000000000000000000000000000000000000000000e0e0c0c0e0e0c0c00000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000cccc000000000000
  | 0, 3 => 0xcccc888888888888000000000000000000000000000000000000000000000000ffcc000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000f0f0c0c0c0c0c0c0000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000003333777777777777000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000aaaaaaa0aaa0aaa0
  | 0, 4 => 0x1f1f1f1f1f1f1f1f000000000000000000000000000000000000000000000000ee00aa00aa00aa00000000000000000000000000000000000000000000000000aa00aa00aa00aa000000000000000000000000000000000000000000000000003377337733773377000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a80000000000000000000000000000000000000000000000005555ffffffffffff000000000000000000000000000000000000000000000000f0f0a0a0a0a0a0a0
  | 0, 5 => 0xeaea0000000000000000000000000000000000000000000000000000000000001111ffffffffffff000000000000000000000000000000000000000000000000e0e0a0a0e0e0a0a0000000000000000000000000000000000000000000000000cc88888888888888000000000000000000000000000000000000000000000000f00ff00ff00ff00f000000000000000000000000000000000000000000000000eeaa000000000000000000000000000000000000000000000000000000000000eeee000000000000000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0
  | 0, 6 => 0xa888a888a888a888000000000000000000000000000000000000000000000000e0a0e0a0e0a0e0a0000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a00000000000000000000000000000000000000000000000000ff00ff00ff00ff0000000000000000000000000000000000000000000000000cc33cc33cc33cc33000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000000000cc88cc88cc88cc8800000000000000000000000000000000000000000000000055ff55ff55ff55ff
  | 0, 7 => 0xf0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000009999999999999999000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000ff00cc00cc00cc000000000000000000000000000000000000000000000000000f0ff0f0f0f0f0f0000000000000000000000000000000000000000000000000aa88888888888888000000000000000000000000000000000000000000000000c888c888c888c888000000000000000000000000000000000000000000000000f0f00f0f0f0f0f0f
  | 0, 8 => 0xeaeaeaeaeaeaeaea0000000000000000000000000000000000000000000000006666666666666666000000000000000000000000000000000000000000000000fcfc000000000000000000000000000000000000000000000000000000000000fc00fc00fc00fc000000000000000000000000000000000000000000000000003333cccccccccccc00000000000000000000000000000000000000000000000055aa55aa55aa55aa000000000000000000000000000000000000000000000000aaaa5555555555550000000000000000000000000000000000000000000000003737373737373737
  | 0, 9 => 0xcccccccccc88cc88000000000000000000000000000000000000000000000000eeaaeeaaeeaaeeaa000000000000000000000000000000000000000000000000fafafafaaaaaaaaa000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000cccccccc88888888000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000ff00ff00ff55ff55000000000000000000000000000000000000000000000000aaaa8888aaaa8888
  | 0, 10 => 0xeeaaeeaa00000000000000000000000000000000000000000000000000000000ccccccccdddddddd000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000fafa0000000000000000000000000000000000000000000000000000000000000000eeeeeeeeeeee000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ee00aa00ee00aa00000000000000000000000000000000000000000000000000f800f800f800f800
  | 0, 11 => 0xf5f0f5f0f5f0f5f000000000000000000000000000000000000000000000000ffff000088000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ccccccc0ccccccc00000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0a0000000000000000000000000000000000000000000000000303ffffffffffff0000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000ffff0f0000000000
  | 0, 12 => 0xf0f0f0f0a0a0a0a00000000000000000000000000000000000000000000000005555555555555555000000000000000000000000000000000000000000000000ff88ff88ff88ff88000000000000000000000000000000000000000000000000ecec0000ecec0000000000000000000000000000000000000000000000000000ff55ff55ff55ff550000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000ff00fa00ff00fa00000000000000000000000000000000000000000000000000e0e0e0e0c0c0c0c0
  | 0, 13 => 0xff33ff33ff33ff000000000000000000000000000000000000000000000000cc88cc8888888888000000000000000000000000000000000000000000000000ffffaaaaaaaaaaaa000000000000000000000000000000000000000000000000cccc8888cccc8888000000000000000000000000000000000000000000000000aaaa0000aaaa000000000000000000000000000000000000000000000000000000fc00fc00fc00fc000000000000000000000000000000000000000000000000ccccccccc8c8c8c8000000000000000000000000000000000000000000000000ff88ff00ff00ff00
  | 0, 14 => 0xaaaaaaaa88888888000000000000000000000000000000000000000000000000f0f000f0f0f000f0000000000000000000000000000000000000000000000000fa00fa00fa00fa00000000000000000000000000000000000000000000000000ff00ff00ff00cc000000000000000000000000000000000000000000000000003333333322222222000000000000000000000000000000000000000000000000ff00ff00aa00aa00000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000000f000f000f000f
  | 0, 15 => 0xcccccccc00000000000000000000000000000000000000000000000000000000ecececececececec00000000000000000000000000000000000000000000000033cc33cc33cc33cc0000000000000000000000000000000000000000000000003333333333333333000000000000000000000000000000000000000000000000ff00ff33ff33ff33000000000000000000000000000000000000000000000000ccccffffffffffff0000000000000000000000000000000000000000000000000000cccccccccccc000000000000000000000000000000000000000000000000ff00ff00cc00cc00
  | 1, 0 => 0xff00aa00aa00aa00000000000000000000000000000000000000000000000000eeeeeeeecccccccc000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000aaaaa0a0a0a0a0a0000000000000000000000000000000000000000000000000aaaaaaa0aaaaaaa0000000000000000000000000000000000000000000000000aa88aa888888888800000000000000000000000000000000000000000000000000ff00cc00cc00cc000000000000000000000000000000000000000000000000ffa0ffa0ffa0ffa0
  | 1, 1 => 0xffff0000ffff000000000000000000000000000000000000000000000000fffff0f0f0f0f0f0000000000000000000000000000000000000000000000000ffff0f000f000f00000000000000000000000000000000000000000000000000cdcdcdcdcdcdcdcd000000000000000000000000000000000000000000000000ccffccffccffccff00000000000000000000000000000000000000000000000000cc00cc00cc00cc000000000000000000000000000000000000000000000000ffaaffaaffaaffaa0000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c
  | 1, 2 => 0xf0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000ffccffccffccffcc00000000000000000000000000000000000000000000000033ff33ff33ff33ff000000000000000000000000000000000000000000000000ffffff00ff00ff00000000000000000000000000000000000000000000000000ffffc0c0c0c0c0c0000000000000000000000000000000000000000000000000ffff5555555555550000000000000000000000000000000000000000000000005555000000000000
  | 1, 3 => 0xffffcccccccccccc0000000000000000000000000000000000000000000000003333ffffffffffff000000000000000000000000000000000000000000000000ff00fc00fc00fc000000000000000000000000000000000000000000000000005757575757575757000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000faf0faf0faf0faf0000000000000000000000000000000000000000000000000f0f0f0a0f0f0f0a0000000000000000000000000000000000000000000000000ffccffcc00000000
  | 1, 4 => 0xc0c0c0c0c0c0c0c000000000000000000000000000000000000000000000000ff11ff11ff11ff11000000000000000000000000000000000000000000000000f0f0f0f000f000f00000000000000000000000000000000000000000000000005555777755557777000000000000000000000000000000000000000000000000f0f0f0f0c0c0c0c0000000000000000000000000000000000000000000000000ff0f000000000000000000000000000000000000000000000000000000000000ff00ff00ff33ff33000000000000000000000000000000000000000000000000c8c8c8c888888888
  | 1, 5 => 0xffffaa00aa00aa00000000000000000000000000000000000000000000000000a8a8a8a888888888000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000fff0fff0fff0fff00000000000000000000000000000000000000000000000000fff0fff0fff0fff000000000000000000000000000000000000000000000000ffff0055000000000000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e000000000000000000000000000000000000000000000000cfcfcfcfcfcfcfcf
  | 1, 6 => 0xf0c0f0c0f0c0f0c000000000000000000000000000000000000000000000000fcccfcccfcccfccc000000000000000000000000000000000000000000000000eeee0000eeee000000000000000000000000000000000000000000000000000033333333cccccccc000000000000000000000000000000000000000000000000ffff00000f000000000000000000000000000000000000000000000000000000fafa0000fafa0000000000000000000000000000000000000000000000000000ffaaff00ff00ff00000000000000000000000000000000000000000000000000fcfcfcfc00000000
  | 1, 7 => 0x5555555577777777000000000000000000000000000000000000000000000000eeee0000aaaa0000000000000000000000000000000000000000000000000000000000ff00ff00ff000000000000000000000000000000000000000000000000ffee000000000000000000000000000000000000000000000000000000000000aaaaaa88aa88aa88000000000000000000000000000000000000000000000000f0f0f0f0e0e0e0e0000000000000000000000000000000000000000000000000f0fff0f0f0f0f0f0000000000000000000000000000000000000000000000000cccc3333cccc3333
  | 1, 8 => 0xf0f0f0f080808080000000000000000000000000000000000000000000000000ff05ff05ff05ff050000000000000000000000000000000000000000000000001111111111111111000000000000000000000000000000000000000000000000f8f0f8f0f8f0f8f0000000000000000000000000000000000000000000000000ffff0055005500550000000000000000000000000000000000000000000000000f0f0f0f5f5f5f5f000000000000000000000000000000000000000000000000f0f0ffffffffffff0000000000000000000000000000000000000000000000000000f0f0f0f0f0f0
  | 1, 9 => 0xf8f8f8f8f8f8f8f8000000000000000000000000000000000000000000000000f0f000f000f000f0000000000000000000000000000000000000000000000000ff00fff0ff00fff0000000000000000000000000000000000000000000000000aaaaaa00aa00aa000000000000000000000000000000000000000000000000000000fafafafafafa000000000000000000000000000000000000000000000000ffff880088008800000000000000000000000000000000000000000000000000f0f0fff0fff0fff00000000000000000000000000000000000000000000000000f3f0f3f0f3f0f3f
  | 1, 10 => 0xffff00000000ffff000000000000000000000000000000000000000000000000f0e0f0e0f0e0f0e0000000000000000000000000000000000000000000000000fa00fa00aa00aa00000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000ffff00ff00ff00ff00000000000000000000000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000ccc0ccc0ccc0ccc0000000000000000000000000000000000000000000000000cccccc88cc88cc88
  | 1, 11 => 0xf0fffffffffffff00000000000000000000000000000000000000000000000033332222222222220000000000000000000000000000000000000000000000003232323232323232000000000000000000000000000000000000000000000000fa00aa00aa00aa00000000000000000000000000000000000000000000000000f0f0e0e0e0e0e0e0000000000000000000000000000000000000000000000000ff00ff0000ff00ff0000000000000000000000000000000000000000000000003322332233223322000000000000000000000000000000000000000000000000ffaaaaaaaaaaaaaa
  | 1, 12 => 0xfaaafaaafaaafaaa000000000000000000000000000000000000000000000000aaaaaaaaaaaa8888000000000000000000000000000000000000000000000000ffff8888888888880000000000000000000000000000000000000000000000003333ffff3333ffff000000000000000000000000000000000000000000000000ff33ff33ff33ff330000000000000000000000000000000000000000000000003300330033003300000000000000000000000000000000000000000000000000ff0fff0fff0fff0f0000000000000000000000000000000000000000000000000f000f000f000f00
  | 1, 13 => 0xeeeecccccccccccc000000000000000000000000000000000000000000000000ffff111100000000000000000000000000000000000000000000000000000000cccccc00cc00cc000000000000000000000000000000000000000000000000001111ffff1111ffff000000000000000000000000000000000000000000000000f0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000000f0f0f0ff0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0a0a0000000000000000000000000000000000000000000000000fccc000000000000
  | 1, 14 => 0xffffffff000000000000000000000000000000000000000000000000f000ff00ff00ff00000000000000000000000000000000000000000000000000ccc8ccc8ccc8ccc8000000000000000000000000000000000000000000000000bbbbbbbbbbbbbbbb00000000000000000000000000000000000000000000000022222222222222220000000000000000000000000000000000000000000000000000555555555555000000000000000000000000000000000000000000000000ff88000000000000000000000000000000000000000000000000000000000000f0f0808080808080
  | 1, 15 => 0xeecceecceecceecc000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000ffff1111111111110000000000000000000000000000000000000000000000000000ffffffff0000000000000000000000000000000000000000000000000000aaaabbbbbbbbbbbb000000000000000000000000000000000000000000000000eeeeaaaaaaaaaaaa000000000000000000000000000000000000000000000000fffa000000000000
  | 2, 0 => 0xff00ff00ff000000000000000000000000000000000000000000000000000000ff00f000ff00f00000000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000000ffffeeeeffffeeee000000000000000000000000000000000000000000000000ffff0000cccc0000000000000000000000000000000000000000000000000000ff00ffffff00ffff0000000000000000000000000000000000000000000000000000ff000000ff00000000000000000000000000000000000000000000000000fcfc0000fcfc0000
  | 2, 1 => 0xfafafafa00000000000000000000000000000000000000000000000000000000fffffffff0f0f0f000000000000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000ffff0f0fffff0f0f000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000eeeeaaaa000000000000000000000000000000000000000000000000000000003333000033330000000000000000000000000000000000000000000000000000ffff333300000000
  | 2, 2 => 0xffff0000ff000000000000000000000000000000000000000000000000000000fffff0f0ffff0000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000ff00aa00ff00aa000000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000ffffffff00550055000000000000000000000000000000000000000000000000ffff0000fffff0f0
  | 2, 3 => 0xf0f0f000f000f000000000000000000000000000000000000000000000000000ffff000088880000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000aa00000000000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000ffff00ffffff00ff000000000000000000000000000000000000000000000000fffff000f000f000000000000000000000000000000000000000000000000000fffffffffffff0f0
  | 2, 4 => 0xffffffff88888888000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ffffff00ffffff00000000000000000000000000000000000000000000000000ff00cc00ff00cc0000000000000000000000000000000000000000000000000000000000aaaaaaaa000000000000000000000000000000000000000000000000ff00ee00ff00ee000000000000000000000000000000000000000000000000000000000000ff00ff
  | 2, 5 => 0xfffff0f0000000000000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000f0f0f0c0f0f0f0c0000000000000000000000000000000000000000000000000fcfcf0f0fcfcf0f0000000000000000000000000000000000000000000000000fcfcfcfccccccccc000000000000000000000000000000000000000000000000aaaaaaaaa8a8a8a8000000000000000000000000000000000000000000000000f3f3f3f3f3f3f3f3000000000000000000000000000000000000000000000000ffff0000f0f00000
  | 2, 6 => 0xffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffffffff0000f0f0000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000ffff0000ffff00ff000000000000000000000000000000000000000000000000f0fff0ff00000000000000000000000000000000000000000000000000000000ffffffffcccc00000000000000000000000000000000000000000000000000000000ffaa0000ffaa000000000000000000000000000000000000000000000000f0f0fff0f0f0fff0
  | 2, 7 => 0xf0f0f5f5f0f0f5f5000000000000000000000000000000000000000000000000ffff0000ffffcccc00000000000000000000000000000000000000000000000011111111ffffffff000000000000000000000000000000000000000000000000ffeeffeeffeeffee00000000000000000000000000000000000000000000000055555555000000000000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000eeeeaaaaeeeeaaaa000000000000000000000000000000000000000000000000ee00ee00cc00cc00
  | 2, 8 => 0xfffff0f0fffff0f0000000000000000000000000000000000000000000000000ffffffffffffaaaa0000000000000000000000000000000000000000000000000000ffff3333ffff000000000000000000000000000000000000000000000000fc00fc00cc00cc00000000000000000000000000000000000000000000000000ff0f0000ff0f0000000000000000000000000000000000000000000000000000ffffffff00ff00ff00000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0
  | 2, 9 => 0xcc00000000000000000000000000000000000000000000000000000000000000ffffaa0000000000000000000000000000000000000000000000000000000000ffccffccff00ff00000000000000000000000000000000000000000000000000ffff0000ffffffff000000000000000000000000000000000000000000000000ffff1111ffff11110000000000000000000000000000000000000000000000008888000088880000000000000000000000000000000000000000000000000000ffffffff00f000f0000000000000000000000000000000000000000000000000fcf0fcf0fcf0fcf0
  | 2, 10 => 0xffffffff3333333300000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000f0fff0fff0fff0ff000000000000000000000000000000000000000000000000ffff0f0f00000000000000000000000000000000000000000000000000000000aaffaaffaaffaaff000000000000000000000000000000000000000000000000ffffffff0f000f00000000000000000000000000000000000000000000000000fffffff0fffffff0
  | 2, 11 => 0xccccc0c0ccccc0c0000000000000000000000000000000000000000000000000f0f0f0f0fff0fff0000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000000ffff3333333333330000000000000000000000000000000000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000ffffaaaa000000000000000000000000000000000000000000000000fcfccccc0000000000000000000000000000000000000000000000000000000000f000f000f000f0
  | 2, 12 => 0xffaa0000ffaa00000000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000fefe0000fefe00000000000000000000000000000000000000000000000000003f3f3f3f3f3f3f3f0000000000000000000000000000000000000000000000008888000000000000000000000000000000000000000000000000000000000000f0f0fffff0f0ffff0000000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000f0f0f0fffffffff
  | 2, 13 => 0xffffffffc0c0c0c0000000000000000000000000000000000000000000000000ffffffffa0a0a0a0000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000faaa0000faaa0000000000000000000000000000000000000000000000000000ffcc0000ffcc0000000000000000000000000000000000000000000000000000ffff0f0f0f0f0f0f000000000000000000000000000000000000000000000000eeeecccceeeecccc000000000000000000000000000000000000000000000000ffaaffaa00000000
  | 2, 14 => 0xffffffff00005555000000000000000000000000000000000000000000000000ccccc0c0c0c0c0c0000000000000000000000000000000000000000000000000ffcccccccccccccc00000000000000000000000000000000000000000000000000330033ffffffff000000000000000000000000000000000000000000000000ffff5555ffff5555000000000000000000000000000000000000000000000000cccccc00cccccc00000000000000000000000000000000000000000000000000ecececec00000000000000000000000000000000000000000000000000000000ffff0000f0000000
  | 2, 15 => 0xf0f0f0f0f0f000000000000000000000000000000000000000000000000ffffffff0000ffff000000000000000000000000000000000000000000000000ffff8080ffff8080000000000000000000000000000000000000000000000000ffffffaaffffffaa00000000000000000000000000000000000000000000000000000000ffffff00000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000ffffcc00ffffcc00000000000000000000000000000000000000000000000000fafaaaaaaaaaaaaa
  | 3, 0 => 0xeeee0000eeee0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000088008800880088000000000000000000000000000000000000000000000000000505ffff0505ffff000000000000000000000000000000000000000000000000ffaaff00ffaaff00000000000000000000000000000000000000000000000000000000ffffffffff0000000000000000000000000000000000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000fff0fff0ff00ff00
  | 3, 1 => 0xff880000ff880000000000000000000000000000000000000000000000000000a000a000a000a000000000000000000000000000000000000000000000000000fcfc0000f0f00000000000000000000000000000000000000000000000000000afafafafafafafaf000000000000000000000000000000000000000000000000ffffffcc00000000000000000000000000000000000000000000000000000000f5f5f5f5f5f5f5f5000000000000000000000000000000000000000000000000ffff0000eeee0000000000000000000000000000000000000000000000000000fafaf0f000000000
  | 3, 2 => 0x3030303030303030000000000000000000000000000000000000000000000000aa00aa0000000000000000000000000000000000000000000000000000000000fffc0000fffc000000000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000fff0ff00ff00ff00000000000000000000000000000000000000000000000000fffafffafffafffa000000000000000000000000000000000000000000000000fcfcccccfcfccccc000000000000000000000000000000000000000000000000ffffffccffffffcc
  | 3, 3 => 0xffffeeeeeeeeeeee000000000000000000000000000000000000000000000000ccccffffccccffff0000000000000000000000000000000000000000000000000000cccc0000cccc000000000000000000000000000000000000000000000000dddddddddddddddd0000000000000000000000000000000000000000000000000000fcfc0000fcfc000000000000000000000000000000000000000000000000ffffffff0000cccc000000000000000000000000000000000000000000000000ff00ffffffffffff000000000000000000000000000000000000000000000000aaaaaaaaffffffff
  | 3, 4 => 0xfffffff000000000000000000000000000000000000000000000000000000000fff000000000000000000000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000333333333333000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000fffffafafafafafa0000000000000000000000000000000000000000000000005555ffff5555ffff
  | 3, 5 => 0xc0c0c0c000000000000000000000000000000000000000000000000000000000aaaaaa00aaaaaa00000000000000000000000000000000000000000000000000ccccccccffffffff000000000000000000000000000000000000000000000000fff0fff0f0f0f0f0000000000000000000000000000000000000000000000000ffccccccffcccccc00000000000000000000000000000000000000000000000000ff00ffffffffff000000000000000000000000000000000000000000000000ffffffccffccffcc000000000000000000000000000000000000000000000000fffffffff000f000
  | 3, 6 => 0xaaaa0000aaaa000000000000000000000000000000000000000000000000ffffffff55555555000000000000000000000000000000000000000000000000eeeeeeeeaaaaaaaa000000000000000000000000000000000000000000000000ffaaffaaff00ff00000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000ffffaa00ffffaa00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x802003
  | 4, 0, 0 => 0xe8242818406870200f406824361a40306428184030242e11403024081640a8082800403034260b40302408034030342411403034180b4048401e0e404810060a406830160a403024100740301408034
  | 4, 0, 1 => 0x68245207406824222e4030345a11403034501140302458254030ac280040682454114068a0220a4068a4501140303422274030244c114030244a2440308c440e4068243e214068803e1b40f02408034
  | 4, 0, 2 => 0x3034123e4068f4020041e0702000406850003b406824203a406824200f403034720b4068e0280040303446374030346c114190d4282540305000344030246600419024622540302462304068245e114
  | 4, 0, 3 => 0x30205011403034124640682452114229104600403030160e40682400434030d46225403024284240682428414030341640403020223f4048a4220e4
  | 5, 0, 0 => 0x1301a092b8454000606824ac005000181a55140454005404850000e50003412140014d40006220504600500148980928845400062802428005000181a092780140006068249c11500018781c0a0014000606934280b5001301a092592940006248242800500034121424029400060691c280b5
  | 5, 0, 1 => 0x18ca090a0954005206824c811500018c6090a1894000d048a428005000181a090a121400063082428005000781a14000fd4005226034c0115000181a140017d4005e068242800500148ba092e00140006068243e4a5000181a140016d4000d04850005a500018120400165400580682428005
  | 5, 0, 2 => 0x180a1402001400060c85000705000181214001bd4000606824dc005001b41a090f86d40052069b0d63f5000181214001a940c090105008006000181a09348014001e0681428005000181a09238454000d04850440a5000181a09118894000d04850000a500018d0090a001400060699c28665
  | 5, 0, 3 => 0x1489809001f5400060699c007c5000181a092a81d400063d82428005000000c0d0602d0000d049e80079500018f0090a1dd400063b050000e50014898750602d40006068242822500018e8090a001400060682400735000181a090a0014000d22850003f500018e4670a0014000d3888c000a5
  | 5, 0, 4 => 0x2141a09259294000d1e850008450001888090a199400060682428835000181a280004540052260240882500018124b000394000003024080340001812140020540006400642800500130f0093f9dd40006069c446225001480c0d14045400522602050115000181a711180140006069f846005
  | 5, 0, 5 => 0x2387a14000394004c0682452115002341a14000fd4001e0682428005000181a09460014006d04850360e50003412290a0454000614050000e500018128b0022940006068240024500019120918895400061e02428665000181a1400221400064382428665000181a09430454005226010063f5
  | 5, 0, 6 => 0x181a990a00140006448d428255001313005020014005206a5d2c4850014898090401d400061e024007c5000188809001f1400060494428005000192a0900251400930e82428665002481a3d0a00140091068242890500148ba090a20d40052048c44a8f50014898050200d40006048104a115
  | 5, 0, 7 => 0x181a09019f1400a206850003f50001942090a00140006068254000500034a8090a1994009f06824009e5000193a090a001400060682458005000181a090a2714000d22824282250003536540a02d4006d06880281b5000348a090a001400064d0642800500034124b2523d400060682418665
  | 5, 0, 8 => 0x191209129f14004c030246225500148980d0982d4004c06ab450115000195814002ad400522602408035002a81a090a001400060685000a95000181214188954000606aa000a7500078121402001400065302428005000181aa50a001400060682428a4500130f0a33f8014005226034180b5
  | 5, 0, 9 => 0x1878090a03d4005206ac8180b5000192e1400039400b10e824280050013160441180140052068243e6b500034ce140002940052260242e115000187814000fd4008d06824280050001810280a001400af0e82428005000190e14000fd4004c06824feae5000188814000fd4000d2a024007c5
  | 5, 0, 10 => 0x197214000394004c06824fe82500150ea090a001400520682570005000181a14002dd400065b024080050014812b5088394000606850063f5000181a09259994004c0682400b45002cc1a14000fd400063a82418005000181a670a001400320682462005000000c0d14045000060682428185
  | 5, 0, 11 => 0xc81a090a1995261d0485000116000f01214000294005206824200f50021c12140002940052260244a2450003412100d845400522608c440e50011012140002940006448504a3f5002881a090a0014000606ae828005000181a050a00d40006068a028665001301a095681d4000606830003f5
  | 5, 0, 12 => 0x3582140030140006389104600500148982b0a0014000d04850060a5001301a093fafd4008e0680828005001481a095f0454006d06824367c5000741214002f5400061e02428005000190e090a001400062202428005002f01a090a0014000d04840000f500148980d0889d400060682428bb5
  | 5, 0, 13 => 0x181ac70a001400064a82408665000198c090a00140089048504a0a50001812170a00140006068242803500148980d14045400060682422c55000181ac40a001400930e824280050030c1a090a0014000d0487c001b5000c81a09001f14000604954220e5001481a0c05a3d400060685000c25
  | 5, 0, 14 => 0x74121400331400063c02428005000181a23000894000606b24280050003412140032d4000606824001a5003281a090a0014005226024623050001958190a1994000606824d86b50003592140002940006448242825500018121f00039400060685000c85000181a4b000fd4005204a58900e5
  | 5, 0, 15 => 0x34c12140034940c0d04b4400116000181a0968001400522602466005000345014000294000606b3c460050003440140006d4000d148a028005000001a090803d0000667050000e5000181a140009d4000604898280050001812663e0394000666824280050001812140200d40006068803e005
  | 5, 1, 0 => 0x1828661f83940052068a0228f5000181a09003654000d04850002e5003601a090a06d4006d06824281b5000181a280a0014000d04ab56a1150035c1a090a0014000606b582800500019aa090a001400064a810003f500148980d1b045400065635028005001489814000d14000d048a828005
  | 5, 1, 1 => 0x3941a0908001400522603446375001481a092439140006048c4000e5032b0321400045800067182400e25000181a090f999400067085000e05002381a140037d4000606824200f5000181a0900379400060682400dd500034122f0a001400066e02428005000181adb0a0014004c6d02428005
  | 5, 1, 2 => 0x1481a0908bb14000606bac28005001301a14003a940c0d0485198116000181214330394000d04ab452115000181ae90a0014000d7402428005000181ae70a02d400065606428005000186a1400039400060682428e650002428660702940015068f428005002b03214000294000d0e05020005
  | 5, 1, 3 => 0x148980d059014000606824aa115000181af00a0014000d04bbc200050682404140006d80014000fc1c0a5000341255088294005226020223f5003b81a090a0014000d04954521150303404140002d80c0d04bb40011600148980d048f940006068255a115000181ab90a00140052068256a115
  | 5, 1, 4 => 0x181ace0a0014000604850000e5000181a09331f140006068d4007c5000242800070294000606825e8f350003412663e0294000914850000e50003412140dbc940006068243e005000181a350a199400f106824280050001832146880140006068247200500034121f00029400060a0007e0e5
  | 5, 1, 5 => 0x181a090a199400f806824280050003412b508bdd4000604bd828005000181a350a0014000d04850cc0a50003412290a199400097b050000a5000346a1400029400000682452114000181a091404540006048c4002550001958020a0014000606825ea00500019b0090a0954000604850440e5
  | 5, 1, 6 => 0x522603412465000540c190a001400fc0682428005000341214003ed400060682428fa5000181a09148454000606825f2115
  | 6, 0, 0 => 0x181a090a00128c00030360c090a001800522603412223e30000c0d0485001056004100c0d0485000c002940c1a09001f18005281024280080b000a40d228242800600148980d04800f8c002903600090a199800522603412ff08b000004c06824964a5003f80c090a0001cc0003024282300039800fd0682428960030000c950682428036
  | 6, 0, 1 => 0x4401a090a001eec0026035370f0a02d8010e0303412143330000c0d04850010d60001936750485000c00030341214000458010c03034121400300216060682428666001301a098505000c0029034126c001ad8000606824280084b002104c06824007c60013012140003814c002903564090a199800060682428963330000c0d8382428006
  | 6, 0, 2 => 0xc0d0485090a008c8181a090a001801180303412140030000c0d0485000f360045c0c0d0485000c00368181a090a1298000d0e82428100030022c0606824280060045499140485000c00291301a140044d8005206850cc3f47b0000c0d04850cc7c6000181a14000fc14c008903412142523d801112603412140030013e060682420006
  | 6, 0, 3 => 0x14899210485000c00030341214004818004c0302428000730000c0d4d850003f6001301a092a845eec0003034131f0a001800528f03412140030000c0d048523a006000181a090a00238c00470181b1b0a001800060682428667bb002340604850000e6000001a091485000a00260181a09331f180006068242800723000980d04ab428006
  | 6, 0, 4 => 0x14a500d0a0007ec00938181a090a0018011226034ce142530000c0d1e850003f600148980d0600016c0003034121400279800fe0348c12140030024d2504850008f6004900c5d0485000c0000034121400029400064483412310030000c0d918242800600148980d0a1207ec00030341214059998004c0a0007e0e7bb0000c0d0485001226
  | 6, 0, 5 => 0x13266090a0001cc00990181a090a00180052261d41214003000a40d0485001316000181a090200022c00291301b300a0018012f260341214003000a40d0a0007f2e600148980d9685000c0029036591b0a0018000606cac12140030000c0d04a58007c600148980d0485254c0003034287f000fd8004c8a02428007bb0000c0d9482428006
  | 6, 0, 6 => 0x1301b2b049fc00c00294501214001ad80006068267214003000a40904050008f6000000c0d0485000a002913013380a00180015030341214003000a40d001f07e8f60049c980d049fc00c002913012040000d800522603412141bb0026e0604850000e6004d8980d0485000c00924d4ba090a0018005206824620047b000a5340682428006
  | 6, 0, 7 => 0x14899400a0001cc00728181a090a001800528183428001fb000a44c06850003f60024c0c090a0001cc002601a46090a0018004c030344014003000a44c06cfc28006004f81a090a001eec00260341214004f5800060485008000730000d3c0682428006001300c0d04850eec00030341214334ed800000303412141128000c0d04850013a6
  | 6, 0, 8 => 0x14a8f1b0a0001cc00a30181a090a00180006068242825333000a40d51850008f600148980d048501ec00260181a1c0a00180052068242800a2b0000cac0486428006000000c0d3888c00a002913288090a0018000d04ad428007bb000a5430682428006001301a093f80274c00a1130121400505800522603428221fb0000c0d04800167c6
  | 6, 0, 9 => 0x14964750485000c00291301a092e0018014c0682428667bb000a54b068242800600019120d04850ccc000303690090a00180006068242800a530000c0d04be42800600148980d0285000c00260181a14330fd80149260341214003000a44ca4064280060014898090a00c1cc06068247a1400045c005203034ce140030000c0d04a5c28006
  | 6, 0, 10 => 0x1481b000a0007ec00291301a092704580006068242800053000980d04ab42811600148980d2685016c002913092090a00180052260348e1405b000a48506824007c6001481a9b0a02d1ec008a9301214000398000d4d8242800053000a44c04830000e60001a9a0d0485000c000303412290a00180006068241014003000a40d1a850008f6
  | 6, 0, 11 => 0x148980d0495800c0006824287f000298005226034aa2808b000989804850000e6000181a090a54800c00000781a090a001401512603428001fb000a55006c6c2800600034123d0a00014c00030341214a78018014e260341214003000a40d04850cc8f60014898440a08c00c00890181a090a19980052261401214003000a44c068249e006
  | 6, 0, 12 => 0x181a0900094f8c00260341214005698000606a6c1214003000980dac824280060001812140003ab0c00ab9301a0900559800060682428310030021c0606850003f6001301a09331f1eec008b8341214003dd800522602408002cb0000c0d0485000626000181a090a002aac00858181a14000fd8000606d501214003002a64c06850003f6
  | 6, 0, 13 => 0x181a090a002bac00032241a09001f18015c0303412003e30009806048202800600148986304850c4c00260181a003e0fd8013703034121435b0000c0d04bfc28006000181a14000feb6c00030343a090a1998980d04b502800253800a44c0682428486001300c0d048c400c00260242800073dd800522603428002fb0000c0d0a000f83f6
  | 6, 0, 14 => 0x181aa80a0007ec00871301a14005818005206c6c295f003002ae060682428006001480c440485000c00291301a0911889800520682428009730000c0d0a000163f6003f4980d0485090c00291301a670a1998000606824287f003000a44c3282428256000181a091e85000c0026036bc14003dd8000606850003f7bb00224063902428006
  | 6, 0, 15 => 0x148980d04800e6c00291301a090a00180006068242800383000980d51850fe0060014898723385000c00470181a190a0018004c068242866053000a44c02850080060014898190a000e0c002603412143bbdd8005226034126e0030000c0db102428006001300c0d5185000c000682428000558580000069141214002802240606824007c6
  | 6, 1, 0 => 0x14898760a0001cc00b459c1a090a00180006068242866b33000980606a6c280b6001481b650485000c00841301a090a0018004c030346a140030000cac068f428006000181a1d04800f8c00291301a090a089800060682428006fb0000c0d0485001646000181a090a002c6c00290356a280a00180052261d01214003000a5030682428006
  | 6, 1, 1 => 0x14ad60d0a0007ec00030781a090a0018005226034e22300300098060682428666000181a094585000c00291301a7e1180180052498741214003000a44c0699c007c6005a80c0d0a0007ec00291301a092a81d80000291301a0c05a8011c0d0e82428006000181a090a002c2c0029130f0090a1dd8005206826d296003000a49f068252c006
  | 6, 1, 2 => 0x5300c0d0485000c000302428001f8398016f0303412140030000c800682428006001489809258001cc00034941214000398000d04850007c05300000522602408035000181a14000947ec00b71301b6d0a00180052262003214003000a4060682428036004381a090a00014c0029036d8090a0018005226034e223113002160d04850000a6
  | 6, 1, 3 => 0x181a14001287ec00295ac1a050a00180052260342800443000a40d800242822600148980d04a1822c00068242800053dd8000606824280001b000a40d8002428006004d4980d04850ccc00a603428001fbdd80115030341214003000a44c220242866600019120d0a0007ec00291d412140023d8005226034500008b0026f1506824286b6
  | 6, 1, 4 => 0x19300d0485000c0029034a8090a0018004c06826e214003000a40644824282560014898280a0001cc00870181a090a0018000d04850000b0530013e0604850000e60014898094580114c00858181a090a00180153260341214003000a44c0682400246001489889048c44ac00295c01a090a0018000d04850000a603000a40d5902428006
  | 6, 1, 5 => 0x181a090a00016c00262c0121400039800060682428006030000c8904850002560001aea0d0485000c00260341214005d1800060682428007bb00126060682428666000181a450485000c002913012041284580052069c600230030000c0d04850015b600148980d04a3000c00b98181a090a199800060682428003e30000c0d04852e4006
  | 6, 1, 6 => 0x148ba090a5c800c00bc8181a090a0018000606de012140030000c0d2a8a028006004d4980d04800f8c00291308809001f180052a38363614333000a44c0494428006005dc980d0485000c000302428000722980006069d412140030000c0d04852ec006000181a09001f1c4c00000181a670a001400522625412004a30000c0d0e850003f6
  | 6, 1, 7 => 0x361eb20485000c004f9301a09080018012f069741214003002f80606824280060027c0c0d0e05000c00030741214000958000d048500025053000a44c06824289c60027c1a090a04000c00a38181214000398004c068242800bdb000a44c068241866600448980d0492c94c00260354614003dd80006068242800bd3000a44c448d428256
  | 6, 1, 8 => 0x148980d540014ec008903412140002980150030341214003000a44c530242800600148980d5285000c000303412140009580052260341214523000a57d0682428006000181b1b0a00016c002951c1b1b001f18000d8795012140030000c0d26824280060002428000723deec00b50181a090a001800980f0341214003001120d04850000a6
  | 6, 1, 9 => 0x4d4980d0a0007ec00291308814000fd800522622412253e3000980606824280f6002bc0c0d0485000c00368181a090f80180000030f01214002800000643824280050014898ac0a00156c000001888090a0014005226034280054b000a4060682496006001301ab00a08c00c00a60341214003dd80006448341214003002b8060682428006
  | 6, 1, 10 => 0x1b000d0485000c007e83412140023d8000606824295f0030000c0d04850017f60001958090a0001cc00030341214058458004c06824284b253001fc060682428486005f898090a0001cc002903412141123d8005226450126c003000a44c040a02800600238980db685000c002903412140023d801120303412140030000cb10682428006
  | 6, 1, 11 => 0x1481a090a00308c00068242800054b98005226034ce140030000006068242803500018131b0a0001cc002960cba090a0018004c068242800c130000c0d0a0007f81600018e2090a0001cc0000148980d140454000606ac01214003000a40d3888c008f60024c0c0d0a0007ec000024c3a090a00140006068242800b030000c0d0488028006
  | 6, 1, 12 => 0x4bc1a098d85000c00291301a14002dd8000604850080012b000a44c5b02408006000181a090a1987ec002603710090a0018004c068245214003000a40d048500187600148980d0a00c7ec000303428001fe198005226034124b3330000c0d92824286660014ad6090a01000c000303412140061580006068243814003000a44c3a82418006
  | 6, 1, 13 => 0x1481b8d0485000c0003034298c000fd9260606824280008b800a44c448504a3f6000361e090a0011ec00291301a050a00d8018b2603412140030000c0d04850cc90600148980d14050ccc004f8181a090a1998000003224121412a8000c0d04850012e6001301a090a00014c06068247a1400095c000606e281214333000a5890682428006
  | 6, 1, 14 => 0x14898870485000c004f8181a09001f180093030741214003001260d04850000a6000181b1b0a08c00c0026034127f2504580006c90341214003000a44c06e4446006000181a090a001c4c000307412140200180190030341214003000a58f0682428006000181a090a0031cc00030341214250458004c030341214003000a40d049556a116
  | 6, 1, 15 => 0x148980d048458ac00296541a090a001800522603588140030000c0d4d824280b60014898092a8441cc00291301a14003098000d04850cc8f7bb0001a9b2a024280060024c0c0d0485000c002903636140065180052261c48823003000a406560642800600132d00d048c400c000303432140002d80006c98341214003000a44c1e02428006
  | 6, 2, 0 => 0xc0d1405000a00068242800973dd800060682429980030000c0d04800f9976000181a090a00156c00291301ac70a00180052262541204333000a44c63024280060014898090b85000c00260341214243dd80006068242800cb3000a44c0682428036000181a090a0030cc000302428003303980052a38363614003000a4850699c28006
  | 6, 2, 1 => 0x181a7104850ccc00036641a090a0018005204ad42800073000a40d04850019b600668980d0485000c000303412140001d800065603412143330000c0d04850015860001812190a0001cc002913158190a1998017e260341214333000a44c06824d86b6001489889048504ac00001b41a090a06d401990682428000530000c090a000360e6
  | 6, 2, 2 => 0x1481a09cf0033ac00290181a092a8458000606824200008b0001a090a0007e0a6000181a7104800f8c0003034139c0a1998000d928242800053000a44c0685000276001489809331f01cc0006c001214003dd80c0d0486428000db8001a090a040001b60014898090a01006c00030356c090a00180052261e012140030000c0d0485000cc6
  | 6, 2, 3 => 0x148980d1405000c004f8181a090a0018000606824280062b0000c092a850000e600148980d6b05000c00291312a04000fd800060682428001fb000a44c5635028006000181b250485000c522603412d100045c000606824aa0008b0013e0d04850000a600148980d6788c00c00030343214118018019f030341214003000a4060a0007e0e6
  | 6, 2, 4 => 0x14898e10a001c0c000303412140d99980006068242800d23000a44c04820001160068c98093f8001cc00001481a095a845400060682428004530000da20682428006001489814330fc1cc00291301a09003658011226024284a073000000604850cc0e5006840c0d0485000c00294dc1a090a6818000606824280048300000065606428005
  | 6, 2, 5 => 0x181a090a000eec00291301ae70a02d80052262b03214003002fc4c06824280060014898350a0001cc00291301a090a3998004c068242866d2b0000c0d04800367c6002b01a090a00014c00bf0341214004b980052068256a143330001a090a0011ef76032b01a090a00022e000303412190a1998a44c56064280008b801260d0e82428006
  | 6, 2, 6 => 0x181214000441cc0003034139c0a001800891903412140030000cac06c6c28006001489809001f01cc00000181a090f801400522603412ad08b0000c0d049542866600034127a0a00014c000303412d40a0018000d04ab56a1400300000060a0007e0e50014898090a1981cc00000181a092a8454005226035d2140030000cac0682428006
  | 6, 2, 7 => 0x148980d1a850ccc000303412140006d800060682428d10030001a09568a4280060014898190a34400c00068243214000298000d04850001b053000a44c0a0007e0e600019c20d0a0007ec00291301a092a84580c0d04864280008b800000604850000e5000000c0d04998f8a00d19301a093f9998000004850000e0528000c0d049e828006
  | 6, 2, 8 => 0xc0d1a85000a000303412550a00180000068242866052800a44c06825ea0060003412550a00014c00d40181a090a001800060682428113330001a092a8a42800600148980d04998f8c00d39301a090a00180006d30341214003000a44c06825e8f36000181a095685000c000303412190a0018000d048f428000db000a4ac0c850008f6
  | 6, 2, 9 => 0x1a090a000220a6000181a090105000c00031941a090a00180006068242866053002244c06824284a6000000c0d04850cca00291301a0914045801a90303412140030000c0d04850000f6
  | 7, 0, 0 => 0x14899ac068242800700131580d0485000f770014899ab068242800700000980d04ab42800600148980d0a000223f700148980d04850cc6270014a184c06850003f700148980d8a02428007000000c0d0485000116001481a090c850008f700148980d0a0007e0e7291301a090c8512c00800148980d048500141700000a44c06824007c600148980d04851e800700148980d0485001aa7
  | 7, 0, 1 => 0x1301a098d85000f7700148980d0485001ae700148980d04800f9567001301a09d685000f770014a480d04850008f7001301a710485000f7700000000d04850000a500148980606824286670014898090a0004a0e700148980d048500022700148980d049542811700000980604850000e6001489863068242866700149fa4c06824280070014a6e4c06824d800700148980d4d82428667
  | 7, 0, 2 => 0x1301a090a000d6f7700438a40606824280070042ca406068242800700448a44c04850000e70000000060682428005001480c0d048512c00700438980d04db428007001481a098d850006b700000a44c3a824280060014898090a000940e7000025e4c0682428006001300c0d048500066700148980d0a08c000b7001300c95068242800700148988904850000e700148980d04850fe667
  | 7, 0, 3 => 0x1491c4c068242800700148980d049fc007c700148980d0485001b170014a6e4c8a02428007001300c0d048642800700148980d048a028007001480c0d0485000f7700148980d8782428007001301a09b685000f77005f8980d04850008f700000a44c06850003f6001300c0d04850001b70014b604c0682428007001489865068242800700148980d048535e00700148980d4d824007c7
  | 7, 0, 4 => 0x148980d83024280070014a084c0682428007000000c0d04850000a600149fc4c04850000e70014898090a08c000e70014898950682428037006d0a44c068242800700148980d04ecc2800700148980d04850000e70014899b20682428007001481a092a850008f70055ca44c06824007c700148980d0488c001170014a040d04850008f700148980d04ad428007001480c0d04850000b7
  | 7, 0, 5 => 0x148991706824280070014a2c4c06824280070000098090a0001cf760068ca40d04850008f7000000c0d4d8242800600148980d04850cc7c700438a44c068242866700148980d04850010d700148989b3a8242800700148980d04850001170014a184c06824280070042ca44c068242866700148980d048500109700000a40d04850cc8f600148980d838242800700148980d0485000947
  | 7, 0, 6 => 0x1312a0d0485000f770014a484c2e824280070014898890682462007000000c0d04850fe00600148980d048501666700148980d0485001227000000c0d048f428006001480c0d048500025700148980d048500120700148980d04850ccf77001312a980682428007004926a4c068242800700148980d0485000e4700000a44c068242848600460a44c068242800700148980d0485000f37
  | 7, 0, 7 => 0x148980d04850013a700000a503068242800600000a44c068242800600448a4060682428007004c8a44c068242800700438a44c06824007c700148980d0481000117001480c0d04850004a700148980d0a1fc003f700148980d94824280070049ca44c0682428007001480c890682428007001301a090a000ccf77001301a71580242800700148980606850003f700000a40d04850012e6
  | 7, 0, 8 => 0xa40d8002428006001489889068242866700148980da40242800700148980d04850014a70014a480d04c6c280070068c9806068242800700518a44c068242800700148980d048504a6670014898ac048642800700000a44c069c4460060000098060682428666001480c0d0e8242800700148980d04800167c700148993c068242800700000a44c0682428226001300c0d0495428007
  | 7, 0, 9 => 0x148980d048506200700438a44c06850003f700148980d048500062700148980d04850015570042ca44c06850003f700148980daa0242800700148980d04852a4007000000c0d04850007c600448a44c068242866700148980d04850000a7000021c060682428006000021606068242800600000a40d590242800600490980d0485000f770068c980d04850fe00700148994d0682428007
  | 7, 0, 10 => 0x148980db10242800700448a44c06824007c700148980d54050003f7001481a090a0001c8f700148980d04850fe00700148980d048f42800700148980d0a0007ef7700148980d04850015d70014898060682428007000000c0d04850000b60014a6e4c06824286b700148980d04bfc2800700148980d0a000f83f7000000c0d0485000f7600148980d4d824280070014898090a0001d587
  | 7, 0, 11 => 0xa40d04850008f6000022406068242800600148988906850003f70014a984c0682428007001489880068242800700148992504850000e700148980d0a0004a3f700002980d0485000f76000000c8906824280060068c980d0485000f77000000c0d048500025600148980d04850cd667001492606068242800700148980d048500164700148980d0485000707001481a090a000228f7
  | 7, 0, 12 => 0x980d04850000a600148980d04850017a700148980d2a8a0280070014898090a0001c8a700148980d3a8242800700148980d04800f8e2700000a44c0699c2800600148980d04850000b7001300c0d0485000117001489889048500025700148980d0485000f7700148980d04850007c7001300c0d04850000e700148980d04852e400700438a44c06824280070042ca44c0682428007
  | 7, 0, 13 => 0x1300c0d04850000a7001301a090a001ef0d70014898ac04850000e70000126060682428006001493e06068242800700448a44c0682428007001480c0d928242800700148988906824280070014aa04c068242800700148980d048500025700148980d8d850000b7001480c0d04850008f70000098060682428006001481a090a0011fb570014af84c06824280070014a8e4c04850000e7
  | 7, 0, 14 => 0x3f9fa4c068242800700000a44c448242825600148980d04850012e70014a8e06068242800700148980dc5024286670042ca40d04850008f7001481a090a258008f700148980d04850cc3f700148980d0a0007f867001480c0d2e8242800700148980d928242866700148980d048500185700000a44c06824280360014898098d850000e700000a54706c6c2800600148980d0a0007f817
  | 7, 0, 15 => 0x148980d0485001867001481a090a0004a8f700148980d4d824280b7001481a5d048512c007001480cac068242800700148980d0c850000b700148980d8d85046007001489992068242800700148980d0485000e270014b204c068242800700148980d04850018e700148980d04800f83f700148980d92824007c700148980d0485094117001481a090a000168f7001481a090a0011ef77
  | 7, 1, 0 => 0x1a090a0011ef7600530980d0485000f77001481a092aad428007001481a090a0011f2e700148980d5b0242800700148980d04850000770014898ac068242866700148980d04850015870014898090c850000e700000a44c068a028006000013e060682428006291301a090a0004a0b800148980d048533000700148980d0485000ab7000000c0d04850003f6000000c0d9282428006
  | 7, 1, 1 => 0x148980d048642866700000a44c04800f80e6291301a090c9542800800148980d04850008a70014899a2068242800700000a44c04850cc0e6000000cac068242800600000a44c5606428006001493e4c068242800700148980d0485000c5700002fc4c06824280060014898092a850000e700148980d928242800700148980d0c85046007001301a090a1fc004a700148980d04e7028667
  | 7, 1, 2 => 0x148980d04851a2007000000c0d04954280060014898e106850003f7291301a090c8500011800000a44c06824cc7c6000000c0d04864280060014898ac06c6c2800700148980d0495428667000000c0d04850001b600148980d04b502800700000a44c0a0007e0e600000a44c06824aa1160014898ac068242800700148980d048500077700000000604850000e529131580d0485000118
  | 7, 1, 3 => 0x148980d0495428007006a0a44c068242800700148980d048502266700002244c06824284a600148980d0486428007000000006068242866500148980d04850001b7
  | 8, 0, 0 => 0x1300c0d0485000c522603412140002dca44c0682428007bb948980d04850007c787148980d0485000f0b291301a090a001c005206824280047b148980d04850fe007291300c0d0485000e522603536090a001c0052260341214003148980d0485000117291301a090a0001ce00291301a14000fd80000030341214002800a44c06824007c6
  | 8, 0, 1 => 0x522603412550a001ca44c06824321400394898ac0682428007291301b250485000f12291301a090a001ca44c448341214003948980d0485000257
  | 9, 0, 0 => 0xa44c0682428006
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
  | 0, 0 => 0x3ffffc7f8fc000000000000000000000000000000000000000000000000000003ffc00000000000000000000000000000000000000000000000000000000000030c3c8790c8000000000000000000000000000000000000000000000000000000c0320640a0000000000000000000000000000000000000000000000000000000300d39a7530000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000000ccb28650a8000000000000000000000000000000000000000000000000000000334d79af57
  | 0, 1 => 0x33403807030000000000000000000000000000000000000000000000000000000fc0f81f0f000000000000000000000000000000000000000000000000000003f03f07e0f00000000000000000000000000000000000000000000000000000000c30be178b000000000000000000000000000000000000000000000000000000030c418844000000000000000000000000000000000000000000000000000000003fffffff0000000000000000000000000000000000000000000000000000030f3cc798cc000000000000000000000000000000000000000000000000000000f03f07e0f0
  | 0, 2 => 0xc03e07c0e0000000000000000000000000000000000000000000000000000000300039a703000000000000000000000000000000000000000000000000000003ffffc7f8fc000000000000000000000000000000000000000000000000000000ccb2be57ab0000000000000000000000000000000000000000000000000000000c003e17030000000000000000000000000000000000000000000000000000000f308798880000000000000000000000000000000000000000000000000000000000380703000000000000000000000000000000000000000000000000000000cc80000000
  | 0, 3 => 0xcc80380703000000000000000000000000000000000000000000000000000003fc80000000000000000000000000000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000030f308610880000000000000000000000000000000000000000000000000000003340000000000000000000000000000000000000000000000000000000000003337fc7f8fc000000000000000000000000000000000000000000000000000003003c0780c0000000000000000000000000000000000000000000000000000000334d41a854
  | 0, 4 => 0x3f0c3386733000000000000000000000000000000000000000000000000000000f00d01a050000000000000000000000000000000000000000000000000000000300d01a0500000000000000000000000000000000000000000000000000000033fcdc1b85c0000000000000000000000000000000000000000000000000000000c30861088000000000000000000000000000000000000000000000000000000030c798f47000000000000000000000000000000000000000000000000000003ccbfffffff0000000000000000000000000000000000000000000000000000030f0c418844
  | 0, 5 => 0x3f40000000000000000000000000000000000000000000000000000000000003003fffffff0000000000000000000000000000000000000000000000000000000f0c479844000000000000000000000000000000000000000000000000000000c00038070300000000000000000000000000000000000000000000000000000300fc3f87c3000000000000000000000000000000000000000000000000000000f340000000000000000000000000000000000000000000000000000000000000ffc00000000000000000000000000000000000000000000000000000000000000f3cc798cc
  | 0, 6 => 0xc398743000000000000000000000000000000000000000000000000000000033c4788c4000000000000000000000000000000000000000000000000000003033c4788c4000000000000000000000000000000000000000000000000000000ff03c0783c000000000000000000000000000000000000000000000000000000c3724648a4000000000000000000000000000000000000000000000000000003f340000000000000000000000000000000000000000000000000000000000000c0323e47a3000000000000000000000000000000000000000000000000000003cff2fe5faf
  | 0, 7 => 0xf0c338673300000000000000000000000000000000000000000000000000000300003807030000000000000000000000000000000000000000000000000000030f00000000000000000000000000000000000000000000000000000000000003f0320640a0000000000000000000000000000000000000000000000000000000f0fcc798cc000000000000000000000000000000000000000000000000000000300038070300000000000000000000000000000000000000000000000000000000303e07830000000000000000000000000000000000000000000000000000030f03386733
  | 0, 8 => 0x3f7dffbfdf000000000000000000000000000000000000000000000000000000ffffc7f8fc000000000000000000000000000000000000000000000000000003cf80000000000000000000000000000000000000000000000000000000000003c03e07c0e00000000000000000000000000000000000000000000000000000033372be57ab000000000000000000000000000000000000000000000000000003c3727e4fa700000000000000000000000000000000000000000000000000000033728650a8000000000000000000000000000000000000000000000000000003f3cf41e874
  | 0, 9 => 0xccb2be47a3000000000000000000000000000000000000000000000000000000f37f7feff70000000000000000000000000000000000000000000000000000033f7df9af57000000000000000000000000000000000000000000000000000003ffc007ff00000000000000000000000000000000000000000000000000000000ccb2b80703000000000000000000000000000000000000000000000000000000334d780000000000000000000000000000000000000000000000000000000003f03f07f0f8000000000000000000000000000000000000000000000000000000334039af03
  | 0, 10 => 0xf37f780000000000000000000000000000000000000000000000000000000000ccb2be57ab000000000000000000000000000000000000000000000000000000ffffffffff0000000000000000000000000000000000000000000000000000033f40000000000000000000000000000000000000000000000000000000000000003fffffff000000000000000000000000000000000000000000000000000003fffff80000000000000000000000000000000000000000000000000000000000f00d07e050000000000000000000000000000000000000000000000000000003003c0780c0
  | 0, 11 => 0xfcc3b8773b000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003f00007e000000000000000000000000000000000000000000000000000000000ccb28657a8000000000000000000000000000000000000000000000000000000f0c3382713000000000000000000000000000000000000000000000000000000307fffffff0000000000000000000000000000000000000000000000000000000340400804000000000000000000000000000000000000000000000000000003ffc3000000
  | 0, 12 => 0x30f3cc18844000000000000000000000000000000000000000000000000000003ccb28650a8000000000000000000000000000000000000000000000000000003f03f3fe7f3000000000000000000000000000000000000000000000000000000cf8007df00000000000000000000000000000000000000000000000000000003fcbf87f0f8000000000000000000000000000000000000000000000000000003c0320640a0000000000000000000000000000000000000000000000000000003f03d07e0d00000000000000000000000000000000000000000000000000000000f3cc61088
  | 0, 13 => 0xfcdf9bf5f000000000000000000000000000000000000000000000000000000c032380703000000000000000000000000000000000000000000000000000003ffcd79af57000000000000000000000000000000000000000000000000000000cc803e5703000000000000000000000000000000000000000000000000000000334001af000000000000000000000000000000000000000000000000000000000f80f81f0f000000000000000000000000000000000000000000000000000000ccb2be178b000000000000000000000000000000000000000000000000000003f03f07e0f0
  | 0, 14 => 0x334d7807030000000000000000000000000000000000000000000000000000030f00c7980c000000000000000000000000000000000000000000000000000003303d07a0d0000000000000000000000000000000000000000000000000000003f03f07e0a0000000000000000000000000000000000000000000000000000003334d41a854000000000000000000000000000000000000000000000000000003f03f01a050000000000000000000000000000000000000000000000000000003cfbeffdfef00000000000000000000000000000000000000000000000000000000c0380703
  | 0, 15 => 0xccb2b80000000000000000000000000000000000000000000000000000000000cfbeffdfef0000000000000000000000000000000000000000000000000000033c8db9b75b000000000000000000000000000000000000000000000000000003334d41a854000000000000000000000000000000000000000000000000000003f03f47e8f4000000000000000000000000000000000000000000000000000000ccbfffffff0000000000000000000000000000000000000000000000000000000032be57ab000000000000000000000000000000000000000000000000000003f03f0640a0
  | 1, 0 => 0x3f00d01a050000000000000000000000000000000000000000000000000000000fffffe57ab000000000000000000000000000000000000000000000000000003ffc001af00000000000000000000000000000000000000000000000000000000334c418844000000000000000000000000000000000000000000000000000000334d41af54000000000000000000000000000000000000000000000000000000300d3807030000000000000000000000000000000000000000000000000000000fc0b8170b000000000000000000000000000000000000000000000000000003f33f47e8f4
  | 1, 1 => 0x3ff800ff000000000000000000000000000000000000000000000000000003fffcc798cc000000000000000000000000000000000000000000000000000003ffc3006030000000000000000000000000000000000000000000000000000000ccb2be57ab000000000000000000000000000000000000000000000000000000cff2fe5faf0000000000000000000000000000000000000000000000000000000c80b8170b000000000000000000000000000000000000000000000000000003f37f7feff7000000000000000000000000000000000000000000000000000000f0c2386723
  | 1, 2 => 0x30f30879888000000000000000000000000000000000000000000000000000000cc80065700000000000000000000000000000000000000000000000000000003fcbfbff7fb0000000000000000000000000000000000000000000000000000033fcdf9bf5f000000000000000000000000000000000000000000000000000003ffff07e0f0000000000000000000000000000000000000000000000000000003fff0861088000000000000000000000000000000000000000000000000000003fff28650a8000000000000000000000000000000000000000000000000000003cc80000000
  | 1, 3 => 0x3fff2be57ab000000000000000000000000000000000000000000000000000003337fffffff000000000000000000000000000000000000000000000000000003f03e07c0e0000000000000000000000000000000000000000000000000000003fcf38670b80000000000000000000000000000000000000000000000000000033f7dffbfdf0000000000000000000000000000000000000000000000000000033f3dc7b8dc0000000000000000000000000000000000000000000000000000030f3c4798c4000000000000000000000000000000000000000000000000000003fcbfb80000
  | 1, 4 => 0xc082384723000000000000000000000000000000000000000000000000000003f03f07e0f00000000000000000000000000000000000000000000000000000030f3cc0180c000000000000000000000000000000000000000000000000000003ccbfc650fc0000000000000000000000000000000000000000000000000000030f3cc61088000000000000000000000000000000000000000000000000000003f0c0000000000000000000000000000000000000000000000000000000000003f03f07e8f40000000000000000000000000000000000000000000000000000000c30b80703
  | 1, 5 => 0x3ffcd01a050000000000000000000000000000000000000000000000000000000030c780703000000000000000000000000000000000000000000000000000000fffff80000000000000000000000000000000000000000000000000000000003ff3fc7f8fc000000000000000000000000000000000000000000000000000000ffc3f87f3f000000000000000000000000000000000000000000000000000003ffc0800000000000000000000000000000000000000000000000000000000000f0c3386733000000000000000000000000000000000000000000000000000000fcf3be77bb
  | 1, 6 => 0xf083386733000000000000000000000000000000000000000000000000000003ccbebfd7eb000000000000000000000000000000000000000000000000000000ffc007ff00000000000000000000000000000000000000000000000000000003334d4657ab000000000000000000000000000000000000000000000000000003ffc00060000000000000000000000000000000000000000000000000000000033f4007bf00000000000000000000000000000000000000000000000000000003f37f07e0f0000000000000000000000000000000000000000000000000000003cfbef80000
  | 1, 7 => 0x3ccb287f8fc000000000000000000000000000000000000000000000000000000ffc001af000000000000000000000000000000000000000000000000000000000000f81f0f000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000000334d39a7530000000000000000000000000000000000000000000000000000030f3cc798cc0000000000000000000000000000000000000000000000000000030ffcc798cc000000000000000000000000000000000000000000000000000000cc8d465754
  | 1, 8 => 0x30f3cc00000000000000000000000000000000000000000000000000000000003f0bf07e0f000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000030f3cc798cc000000000000000000000000000000000000000000000000000003ffc0801008000000000000000000000000000000000000000000000000000000f0c33e77bb0000000000000000000000000000000000000000000000000000030f3fffffff000000000000000000000000000000000000000000000000000000003cc798cc
  | 1, 9 => 0x30f3cff9fcf0000000000000000000000000000000000000000000000000000030f00c0180c000000000000000000000000000000000000000000000000000003f03fc7e0fc000000000000000000000000000000000000000000000000000000334d01a050000000000000000000000000000000000000000000000000000000003dffbfdf000000000000000000000000000000000000000000000000000003ffc00000000000000000000000000000000000000000000000000000000000030f3fc7f8fc000000000000000000000000000000000000000000000000000000f3c3786f37
  | 1, 10 => 0x3ffc00000ff0000000000000000000000000000000000000000000000000000030f3cc798cc000000000000000000000000000000000000000000000000000003303d01a050000000000000000000000000000000000000000000000000000003003c000000000000000000000000000000000000000000000000000000000003ffc0f81f0f0000000000000000000000000000000000000000000000000000000fc0000000000000000000000000000000000000000000000000000000000000cc328650a8000000000000000000000000000000000000000000000000000000ccb23e47a3
  | 1, 11 => 0xf0ffffffff000000000000000000000000000000000000000000000000000003334d41a854000000000000000000000000000000000000000000000000000003334d41a854000000000000000000000000000000000000000000000000000003300d01a0500000000000000000000000000000000000000000000000000000030f3cc798cc000000000000000000000000000000000000000000000000000003f03f001f0f000000000000000000000000000000000000000000000000000003334d41a854000000000000000000000000000000000000000000000000000003f34d79af57
  | 1, 12 => 0x3337d7fafd7000000000000000000000000000000000000000000000000000000334d79af03000000000000000000000000000000000000000000000000000003ffc0380703000000000000000000000000000000000000000000000000000003337ff9a8ff000000000000000000000000000000000000000000000000000003f37f47e8f4000000000000000000000000000000000000000000000000000003300d01a050000000000000000000000000000000000000000000000000000003f0ff3fe7f3000000000000000000000000000000000000000000000000000000f003006030
  | 1, 13 => 0xfff2be57ab000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000000ccb20640a0000000000000000000000000000000000000000000000000000003003ff800ff000000000000000000000000000000000000000000000000000003030c418844000000000000000000000000000000000000000000000000000000f0c33f98cc0000000000000000000000000000000000000000000000000000030f3cc79844000000000000000000000000000000000000000000000000000003cc80000000
  | 1, 14 => 0x7ffff000000000000000000000000000000000000000000000000000003003f07e0f0000000000000000000000000000000000000000000000000000000cc32be57ab000000000000000000000000000000000000000000000000000003334d79af57000000000000000000000000000000000000000000000000000000334d41a85400000000000000000000000000000000000000000000000000000000328650a8000000000000000000000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000030f00000000
  | 1, 15 => 0xfcbfbff7fb000000000000000000000000000000000000000000000000000003fff2bfffab000000000000000000000000000000000000000000000000000003fff2b80000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000000003fffff00000000000000000000000000000000000000000000000000000000334d79af57000000000000000000000000000000000000000000000000000000ffcd79af57000000000000000000000000000000000000000000000000000003ff40000000
  | 2, 0 => 0x3f03f07e000000000000000000000000000000000000000000000000000000003f03c07e0c00000000000000000000000000000000000000000000000000000000fc0001f00000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffc0065700000000000000000000000000000000000000000000000000000003f03fffe0ff000000000000000000000000000000000000000000000000000000003f0000f0000000000000000000000000000000000000000000000000000003cf8007df00
  | 2, 1 => 0x33f7df80000000000000000000000000000000000000000000000000000000003ffffff98cc000000000000000000000000000000000000000000000000000000000007e0f0000000000000000000000000000000000000000000000000000003ffc33fff33000000000000000000000000000000000000000000000000000003ffffffff00000000000000000000000000000000000000000000000000000000ffcd780000000000000000000000000000000000000000000000000000000003334001a800000000000000000000000000000000000000000000000000000003ffcd400000
  | 2, 2 => 0x3ffc007e000000000000000000000000000000000000000000000000000000003fffcc7ff00000000000000000000000000000000000000000000000000000003ffcd780000000000000000000000000000000000000000000000000000000003f00d07e050000000000000000000000000000000000000000000000000000000f0c1386713000000000000000000000000000000000000000000000000000003fffff9af57000000000000000000000000000000000000000000000000000003fffff81008000000000000000000000000000000000000000000000000000003ffc007ffcc
  | 2, 3 => 0x30f3c0780c0000000000000000000000000000000000000000000000000000003ffc0000700000000000000000000000000000000000000000000000000000000c00006400000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000030f00079800000000000000000000000000000000000000000000000000000003ffc0ffff0f000000000000000000000000000000000000000000000000000003fffc0780c0000000000000000000000000000000000000000000000000000003ffffffffcc
  | 2, 4 => 0x3fffff80703000000000000000000000000000000000000000000000000000003ffffffe0f0000000000000000000000000000000000000000000000000000003f03f000000000000000000000000000000000000000000000000000000000003ffff07fff0000000000000000000000000000000000000000000000000000003f03207e0a0000000000000000000000000000000000000000000000000000000000001af57000000000000000000000000000000000000000000000000000003f03f07e0f00000000000000000000000000000000000000000000000000000000000001f0f
  | 2, 5 => 0x3fffcc00000000000000000000000000000000000000000000000000000000000003ff800000000000000000000000000000000000000000000000000000000030f3c8798c8000000000000000000000000000000000000000000000000000003cfbcc7dfcc000000000000000000000000000000000000000000000000000003cfbefe57ab000000000000000000000000000000000000000000000000000000334d798f470000000000000000000000000000000000000000000000000000033f7dc7b8dc000000000000000000000000000000000000000000000000000003ffc0079800
  | 2, 6 => 0x3ffcd7fff57000000000000000000000000000000000000000000000000000003fffff800cc000000000000000000000000000000000000000000000000000003ffff000000000000000000000000000000000000000000000000000000000003ffc007ff0f0000000000000000000000000000000000000000000000000000030ffcf80000000000000000000000000000000000000000000000000000000003fffffe5700000000000000000000000000000000000000000000000000000000003f7800f70000000000000000000000000000000000000000000000000000030f3fc798fc
  | 2, 7 => 0x30f3ec798ec000000000000000000000000000000000000000000000000000003ffc007ffab000000000000000000000000000000000000000000000000000003000007ffff000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ccb2800000000000000000000000000000000000000000000000000000000000000001a854000000000000000000000000000000000000000000000000000000ffcd7fff57000000000000000000000000000000000000000000000000000000f03f0640a0
  | 2, 8 => 0x3fffcc7ffcc000000000000000000000000000000000000000000000000000003ffffffff57000000000000000000000000000000000000000000000000000000003ff9a8ff000000000000000000000000000000000000000000000000000003c03e0640a0000000000000000000000000000000000000000000000000000003f0c007e700000000000000000000000000000000000000000000000000000003fffff81f0f0000000000000000000000000000000000000000000000000000000fc0f800000000000000000000000000000000000000000000000000000000030f0c479844
  | 2, 9 => 0xc000000000000000000000000000000000000000000000000000000000000003ffcd000000000000000000000000000000000000000000000000000000000003fcbfbfe0f0000000000000000000000000000000000000000000000000000003ffc007ffff000000000000000000000000000000000000000000000000000003ffc007ff000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000003fffff8180c000000000000000000000000000000000000000000000000000003cf3ec7d8ec
  | 2, 10 => 0x3fffff9a854000000000000000000000000000000000000000000000000000003334d4000000000000000000000000000000000000000000000000000000000000c808010080000000000000000000000000000000000000000000000000000030ffcff9fcf000000000000000000000000000000000000000000000000000003ffc33800000000000000000000000000000000000000000000000000000000003fcdf9bf5f000000000000000000000000000000000000000000000000000003fffff86030000000000000000000000000000000000000000000000000000003ffffc7fffc
  | 2, 11 => 0xccb08657880000000000000000000000000000000000000000000000000000030f3cc7f8fc000000000000000000000000000000000000000000000000000000334d79af00000000000000000000000000000000000000000000000000000003ffcd41a854000000000000000000000000000000000000000000000000000000f0c0000000000000000000000000000000000000000000000000000000000000000007ff57000000000000000000000000000000000000000000000000000003cfb2b800000000000000000000000000000000000000000000000000000000000f00c0180c
  | 2, 12 => 0x3f34007ef00000000000000000000000000000000000000000000000000000000ccb28650a8000000000000000000000000000000000000000000000000000003ffc007ff00000000000000000000000000000000000000000000000000000003f3cf79ef7700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030f3fff98ff000000000000000000000000000000000000000000000000000000000d79af57000000000000000000000000000000000000000000000000000000f0c33fffff
  | 2, 13 => 0x3fffffe1088000000000000000000000000000000000000000000000000000003fffff988440000000000000000000000000000000000000000000000000000030f3cc00000000000000000000000000000000000000000000000000000000003334007af00000000000000000000000000000000000000000000000000000003fc8007f700000000000000000000000000000000000000000000000000000003ffc3386733000000000000000000000000000000000000000000000000000000fff2bfffab000000000000000000000000000000000000000000000000000003f37f780000
  | 2, 14 => 0x3fffff800a8000000000000000000000000000000000000000000000000000000ccb0861088000000000000000000000000000000000000000000000000000003fcb2be57ab000000000000000000000000000000000000000000000000000000034047ffff000000000000000000000000000000000000000000000000000003fff287ffa8000000000000000000000000000000000000000000000000000000ccb20657a0000000000000000000000000000000000000000000000000000000cfbef80000000000000000000000000000000000000000000000000000000003ffc0078000
  | 2, 15 => 0x3386733000000000000000000000000000000000000000000000000000003fffff800ff000000000000000000000000000000000000000000000000000003ffc007ff00000000000000000000000000000000000000000000000000000003ffff7ffff7000000000000000000000000000000000000000000000000000000000007fff000000000000000000000000000000000000000000000000000000000000000ff000000000000000000000000000000000000000000000000000003fff207ffa00000000000000000000000000000000000000000000000000000033f4d79af57
  | 3, 0 => 0x3ff800ff00000000000000000000000000000000000000000000000000000030413827130000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0bff840ff000000000000000000000000000000000000000000000000000003f37f07eff00000000000000000000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000000000000000f0c0006700000000000000000000000000000000000000000000000000000003ff3fc7e0f0
  | 3, 1 => 0x3f00007e700000000000000000000000000000000000000000000000000000000000c018040000000000000000000000000000000000000000000000000000003cf80079800000000000000000000000000000000000000000000000000000000f3cf79ef77000000000000000000000000000000000000000000000000000003ffffb80000000000000000000000000000000000000000000000000000000003cfbec7d8ec000000000000000000000000000000000000000000000000000003ffc007ff000000000000000000000000000000000000000000000000000000033f7cc00000
  | 3, 2 => 0x3030c418844000000000000000000000000000000000000000000000000000000300d000000000000000000000000000000000000000000000000000000000003ff8007ff000000000000000000000000000000000000000000000000000000000003380033000000000000000000000000000000000000000000000000000003ff3f07e0f0000000000000000000000000000000000000000000000000000003ff7fffffff000000000000000000000000000000000000000000000000000003cfb2bfdfab000000000000000000000000000000000000000000000000000003ffffbffffb
  | 3, 3 => 0x3ffffffffff000000000000000000000000000000000000000000000000000000ccbffe57ff0000000000000000000000000000000000000000000000000000000032b800ab000000000000000000000000000000000000000000000000000003ccb2be57ab000000000000000000000000000000000000000000000000000000003ef800ef000000000000000000000000000000000000000000000000000003fffff800ab000000000000000000000000000000000000000000000000000003f03fffffff000000000000000000000000000000000000000000000000000000334d7fffff
  | 3, 4 => 0x3ffffc00000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000000000007ff00000000000000000000000000000000000000000000000000000000000d41a854000000000000000000000000000000000000000000000000000003fffffe57ab000000000000000000000000000000000000000000000000000003ff0007f800000000000000000000000000000000000000000000000000000003fffdffbfdf000000000000000000000000000000000000000000000000000003ccbffe50ff
  | 3, 5 => 0xc30800000000000000000000000000000000000000000000000000000000000334d01af50000000000000000000000000000000000000000000000000000000ccb2bfffff000000000000000000000000000000000000000000000000000003ff3fc798cc000000000000000000000000000000000000000000000000000003fcb2bff7ab0000000000000000000000000000000000000000000000000000000fc0ffffff000000000000000000000000000000000000000000000000000003ffffbff7fb000000000000000000000000000000000000000000000000000003ffffff80c0
  | 3, 6 => 0xd780057000000000000000000000000000000000000000000000000000003fffffe50a8000000000000000000000000000000000000000000000000000000fffff9af57000000000000000000000000000000000000000000000000000003f37f7fe0f0000000000000000000000000000000000000000000000000000000300001a000000000000000000000000000000000000000000000000000000003ffcd07ff50
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3aa28050000000000000000000000000000000000000000000000000000000003ffe8250400000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000002d83716e2f200000000000000000000000000000000000000000000000000000177dffbffff000000000000000000000000000000000000000000000000000003aa28050000000000000000000000000000000000000000000000000000000002ddf7feffff00000000000000000000000000000000000000000000000000000177dffbffff
  | 0, 1 => 0x177dffbffff00000000000000000000000000000000000000000000000000000005c0e81d0d000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000002ddf7feffff000000000000000000000000000000000000000000000000000001271ccb99cd0000000000000000000000000000000000000000000000000000000017dafbff000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000003fa3f17e2f2
  | 0, 2 => 0x3fa3f17e2f200000000000000000000000000000000000000000000000000000177dffbffff000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000002ddf7feffff000000000000000000000000000000000000000000000000000002ddf7feffff000000000000000000000000000000000000000000000000000003af3ccf99cd00000000000000000000000000000000000000000000000000000055d7faffff000000000000000000000000000000000000000000000000000002dde0240400
  | 0, 3 => 0x2ddf7feffff000000000000000000000000000000000000000000000000000003ffe8250400000000000000000000000000000000000000000000000000000003fa28050000000000000000000000000000000000000000000000000000000003af3ccf99cd00000000000000000000000000000000000000000000000000000177c82104000000000000000000000000000000000000000000000000000000012208010000000000000000000000000000000000000000000000000000000003aa3c0780c000000000000000000000000000000000000000000000000000000177dffbffff
  | 0, 4 => 0x50c3306632000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000001721f13e2f200000000000000000000000000000000000000000000000000000122080100000000000000000000000000000000000000000000000000000000028d34ce99cd00000000000000000000000000000000000000000000000000000177dffbffff0000000000000000000000000000000000000000000000000000028837defbff000000000000000000000000000000000000000000000000000003af3ccf99cd
  | 0, 5 => 0x3ffe82504000000000000000000000000000000000000000000000000000000000017dafbff000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000002ddf7feffff000000000000000000000000000000000000000000000000000003aafc2784c0000000000000000000000000000000000000000000000000000003ffe8250400000000000000000000000000000000000000000000000000000003ffe8250400000000000000000000000000000000000000000000000000000003af3ccf99cd
  | 0, 6 => 0x177dffbffff000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000003af3ccf99cd0000000000000000000000000000000000000000000000000000005503d87b3f000000000000000000000000000000000000000000000000000002d83716e2f2000000000000000000000000000000000000000000000000000003ffe8250400000000000000000000000000000000000000000000000000000002ddf7feffff0000000000000000000000000000000000000000000000000000028de0ec1d0d
  | 0, 7 => 0x50c330663200000000000000000000000000000000000000000000000000000055d7faffff000000000000000000000000000000000000000000000000000003af28050000000000000000000000000000000000000000000000000000000003fa3f17e2f200000000000000000000000000000000000000000000000000000050d4ea9dcd00000000000000000000000000000000000000000000000000000177dffbffff000000000000000000000000000000000000000000000000000002ddf7feffff000000000000000000000000000000000000000000000000000003af2b156232
  | 0, 8 => 0x3ffffffffff000000000000000000000000000000000000000000000000000003aa28050000000000000000000000000000000000000000000000000000000003ffe8250400000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000001221fdbfbff0000000000000000000000000000000000000000000000000000028de0ec1d0d00000000000000000000000000000000000000000000000000000177c82104000000000000000000000000000000000000000000000000000000012208010000
  | 0, 9 => 0x2ddf7feffff000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffe827ff00000000000000000000000000000000000000000000000000000002ddf7feffff00000000000000000000000000000000000000000000000000000177dff90400000000000000000000000000000000000000000000000000000003fa3f17e2f200000000000000000000000000000000000000000000000000000177dffbffff
  | 0, 10 => 0x3fffffd0400000000000000000000000000000000000000000000000000000002ddf7feffff000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffe82504000000000000000000000000000000000000000000000000000000000017dafbff000000000000000000000000000000000000000000000000000003fffffd0400000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000003fa3f17e2f2
  | 0, 11 => 0x50c3306632000000000000000000000000000000000000000000000000000003ffe827e600000000000000000000000000000000000000000000000000000003fa2807e200000000000000000000000000000000000000000000000000000002ddf7feffff00000000000000000000000000000000000000000000000000000050c33066320000000000000000000000000000000000000000000000000000000017dafbff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffeb350400
  | 0, 12 => 0x3af3ccf99cd0000000000000000000000000000000000000000000000000000028820040000000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffe827ff00000000000000000000000000000000000000000000000000000003fa3f17e2f20000000000000000000000000000000000000000000000000000028820040000000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000003af3ccf99cd
  | 0, 13 => 0x5c0e81d0d000000000000000000000000000000000000000000000000000002ddf7feffff000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000002ddf7feffff00000000000000000000000000000000000000000000000000000177c823ff0000000000000000000000000000000000000000000000000000000005c0e81d0d000000000000000000000000000000000000000000000000000002ddf7feffff000000000000000000000000000000000000000000000000000003ffff37e6f2
  | 0, 14 => 0x177dffbffff000000000000000000000000000000000000000000000000000003af28cf990d000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000003fa3f17e2f20000000000000000000000000000000000000000000000000000012208010000000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000003ffffffffff00000000000000000000000000000000000000000000000000000000c0200400
  | 0, 15 => 0x2ddf7fc0400000000000000000000000000000000000000000000000000000003ffffffffff00000000000000000000000000000000000000000000000000000127c8e91d0d0000000000000000000000000000000000000000000000000000012208010000000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000002ddf7feffff0000000000000000000000000000000000000000000000000000000017dafbff000000000000000000000000000000000000000000000000000003fa3f17e2f2
  | 1, 0 => 0x3fa3f17e2f2000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffe827ff0000000000000000000000000000000000000000000000000000000177dceb9dcd00000000000000000000000000000000000000000000000000000177dffbffff00000000000000000000000000000000000000000000000000000177dffbffff00000000000000000000000000000000000000000000000000000005c0e81d0d000000000000000000000000000000000000000000000000000003ff3fdffbff
  | 1, 1 => 0x17d800ff000000000000000000000000000000000000000000000000000003fffcef9dcd000000000000000000000000000000000000000000000000000003ffeb356632000000000000000000000000000000000000000000000000000002ddf7feffff000000000000000000000000000000000000000000000000000002ddf7feffff00000000000000000000000000000000000000000000000000000005c0e81d0d000000000000000000000000000000000000000000000000000003ffffffffff00000000000000000000000000000000000000000000000000000050c3306632
  | 1, 2 => 0x3af3ccf99cd000000000000000000000000000000000000000000000000000002dde026ff00000000000000000000000000000000000000000000000000000003ffffffffff00000000000000000000000000000000000000000000000000000127c8e91d0d000000000000000000000000000000000000000000000000000003ffff37e6f2000000000000000000000000000000000000000000000000000003fffcef9dcd000000000000000000000000000000000000000000000000000003ffe82504000000000000000000000000000000000000000000000000000000028820040000
  | 1, 3 => 0x3ffffffffff000000000000000000000000000000000000000000000000000001221fdbfbff000000000000000000000000000000000000000000000000000003fa3f17e2f20000000000000000000000000000000000000000000000000000028820040000000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ff3fdffbff000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000003fffffd0400
  | 1, 4 => 0x50c3306632000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000003af3ccd190d0000000000000000000000000000000000000000000000000000028820040000000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000003fae8250400000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000002ddf7feffff
  | 1, 5 => 0x3ffff37e6f200000000000000000000000000000000000000000000000000000177dffbffff000000000000000000000000000000000000000000000000000003fffffd0400000000000000000000000000000000000000000000000000000003ff3fdffbff00000000000000000000000000000000000000000000000000000055c3f87f3f000000000000000000000000000000000000000000000000000003ffe825040000000000000000000000000000000000000000000000000000000050c3306632000000000000000000000000000000000000000000000000000002ddf7feffff
  | 1, 6 => 0x50c3306632000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffe827ff00000000000000000000000000000000000000000000000000000001220803fbff000000000000000000000000000000000000000000000000000003ffe8256600000000000000000000000000000000000000000000000000000003ffe827ff00000000000000000000000000000000000000000000000000000003ffff37e6f2000000000000000000000000000000000000000000000000000003fffffd0400
  | 1, 7 => 0x28820040000000000000000000000000000000000000000000000000000000003ffe827ff000000000000000000000000000000000000000000000000000000000000c8190d000000000000000000000000000000000000000000000000000003ffe825040000000000000000000000000000000000000000000000000000000177dffbffff000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000003affcef9dcd000000000000000000000000000000000000000000000000000002dde026ff00
  | 1, 8 => 0x3af3ccf99cd000000000000000000000000000000000000000000000000000003fa3f17e2f20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ff3fdffbff000000000000000000000000000000000000000000000000000003ffe825040000000000000000000000000000000000000000000000000000000050c3306632000000000000000000000000000000000000000000000000000003af3fdffbff0000000000000000000000000000000000000000000000000000000014ca99cd
  | 1, 9 => 0x3ffffffffff000000000000000000000000000000000000000000000000000003af28cd190d000000000000000000000000000000000000000000000000000003fa3fdfe2ff00000000000000000000000000000000000000000000000000000177df33e6f20000000000000000000000000000000000000000000000000000000017dafbff000000000000000000000000000000000000000000000000000003ffff37e6f2000000000000000000000000000000000000000000000000000003af3fdffbff00000000000000000000000000000000000000000000000000000050c3306632
  | 1, 10 => 0x3ffe82504ff000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000003aa3c050000000000000000000000000000000000000000000000000000000003ffe8ed1d0d00000000000000000000000000000000000000000000000000000005c0200400000000000000000000000000000000000000000000000000000002dd37defbff000000000000000000000000000000000000000000000000000002ddf7feffff
  | 1, 11 => 0x50d7faffff00000000000000000000000000000000000000000000000000000122080100000000000000000000000000000000000000000000000000000000012208010000000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000003fa3f15190d0000000000000000000000000000000000000000000000000000012208010000000000000000000000000000000000000000000000000000000003ffffffffff
  | 1, 12 => 0x3ffffffffff00000000000000000000000000000000000000000000000000000177dffbffff000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000001221fd900ff000000000000000000000000000000000000000000000000000003fa3f17e2f20000000000000000000000000000000000000000000000000000012208010000000000000000000000000000000000000000000000000000000003faff37e6f20000000000000000000000000000000000000000000000000000005003106232
  | 1, 13 => 0x3ffffffffff000000000000000000000000000000000000000000000000000003ffe8250400000000000000000000000000000000000000000000000000000002ddf736e6f20000000000000000000000000000000000000000000000000000000017d800ff000000000000000000000000000000000000000000000000000003af3ccf99cd00000000000000000000000000000000000000000000000000000050c3329dcd000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000003ffe8250400
  | 1, 14 => 0x2fbff000000000000000000000000000000000000000000000000000003aa3f17e2f2000000000000000000000000000000000000000000000000000002ddf7feffff00000000000000000000000000000000000000000000000000000177dffbffff00000000000000000000000000000000000000000000000000000122080100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffe8250400000000000000000000000000000000000000000000000000000003af3ccf99cd
  | 1, 15 => 0x3ffffffffff000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003fffffd0400000000000000000000000000000000000000000000000000000003ffe82504000000000000000000000000000000000000000000000000000000000017dafb0000000000000000000000000000000000000000000000000000000177dffbffff000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffe8250400
  | 2, 0 => 0x3fa3f17e200000000000000000000000000000000000000000000000000000003fa3c07e2c000000000000000000000000000000000000000000000000000000005c0201d00000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffe827ff00000000000000000000000000000000000000000000000000000003fa3fdfe2ff00000000000000000000000000000000000000000000000000000000171000f2000000000000000000000000000000000000000000000000000003ffe827ff00
  | 2, 1 => 0x3fffffd0400000000000000000000000000000000000000000000000000000003ffffff9dcd000000000000000000000000000000000000000000000000000000000002e2f2000000000000000000000000000000000000000000000000000003ffeb37ff32000000000000000000000000000000000000000000000000000003ffffffff00000000000000000000000000000000000000000000000000000003fffffd04000000000000000000000000000000000000000000000000000000012208010000000000000000000000000000000000000000000000000000000003ffe8250400
  | 2, 2 => 0x3ffe827e600000000000000000000000000000000000000000000000000000003fffcefff00000000000000000000000000000000000000000000000000000003fffffd0400000000000000000000000000000000000000000000000000000003fa3f17e2f200000000000000000000000000000000000000000000000000000050c3306632000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003fffffd0400000000000000000000000000000000000000000000000000000003ffe827ffcd
  | 2, 3 => 0x3af3c0780c0000000000000000000000000000000000000000000000000000003ffe827ff00000000000000000000000000000000000000000000000000000002d82006e2000000000000000000000000000000000000000000000000000000017208010000000000000000000000000000000000000000000000000000000003af28079900000000000000000000000000000000000000000000000000000003ffe8efff0d000000000000000000000000000000000000000000000000000003fffc2784c0000000000000000000000000000000000000000000000000000003ffffffffcd
  | 2, 4 => 0x3ffffffffff000000000000000000000000000000000000000000000000000003ffffffe6f2000000000000000000000000000000000000000000000000000003fa3f150000000000000000000000000000000000000000000000000000000003ffff37fff2000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000000000002fbff000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000000000000190d
  | 2, 5 => 0x3fffced04000000000000000000000000000000000000000000000000000000000017d80000000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000003fffcefffcd000000000000000000000000000000000000000000000000000003ffffffffff00000000000000000000000000000000000000000000000000000177dffbffff000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000003ffe8279d00
  | 2, 6 => 0x3ffffffffff000000000000000000000000000000000000000000000000000003fffffd04cd000000000000000000000000000000000000000000000000000003ffff350400000000000000000000000000000000000000000000000000000003ffe827ff0d000000000000000000000000000000000000000000000000000003affced0400000000000000000000000000000000000000000000000000000003ffffffff000000000000000000000000000000000000000000000000000000000017d800ff000000000000000000000000000000000000000000000000000003af3fdf99ff
  | 2, 7 => 0x3af3ccf99cd000000000000000000000000000000000000000000000000000003ffe827ffff000000000000000000000000000000000000000000000000000000000002fbff000000000000000000000000000000000000000000000000000003ffffffffff00000000000000000000000000000000000000000000000000000288200400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003fa3f17e2f2
  | 2, 8 => 0x3fffcefffcd000000000000000000000000000000000000000000000000000003ffffffffff0000000000000000000000000000000000000000000000000000000017d800ff000000000000000000000000000000000000000000000000000003fa3f17e2f2000000000000000000000000000000000000000000000000000003fae827e600000000000000000000000000000000000000000000000000000003fffffd1d0d00000000000000000000000000000000000000000000000000000005c0e80400000000000000000000000000000000000000000000000000000003af3ccf99cd
  | 2, 9 => 0x2d820040000000000000000000000000000000000000000000000000000000003ffff350400000000000000000000000000000000000000000000000000000003ffffffe6f2000000000000000000000000000000000000000000000000000003ffe827ffff000000000000000000000000000000000000000000000000000003ffe827ff0000000000000000000000000000000000000000000000000000000055c022ff00000000000000000000000000000000000000000000000000000003fffffd1d0d000000000000000000000000000000000000000000000000000003ff3fdffbff
  | 2, 10 => 0x3fffffd040000000000000000000000000000000000000000000000000000000122080100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003affcef9dcd000000000000000000000000000000000000000000000000000003ffeb35040000000000000000000000000000000000000000000000000000000177dffbffff000000000000000000000000000000000000000000000000000003fffffd6632000000000000000000000000000000000000000000000000000003ffffffffff
  | 2, 11 => 0x2ddf4eeffcd000000000000000000000000000000000000000000000000000003af3ccffbff00000000000000000000000000000000000000000000000000000177dffbff00000000000000000000000000000000000000000000000000000003ffe825040000000000000000000000000000000000000000000000000000000050c0200400000000000000000000000000000000000000000000000000000000000002fbff000000000000000000000000000000000000000000000000000003fffffd04000000000000000000000000000000000000000000000000000000000500c8190d
  | 2, 12 => 0x3ffe827ff000000000000000000000000000000000000000000000000000000028820040000000000000000000000000000000000000000000000000000000003ffe827ff0000000000000000000000000000000000000000000000000000000172cb31663200000000000000000000000000000000000000000000000000000055c0200400000000000000000000000000000000000000000000000000000003af3fdf99ff0000000000000000000000000000000000000000000000000000000017dafbff00000000000000000000000000000000000000000000000000000050c332ffff
  | 2, 13 => 0x3ffffff9dcd000000000000000000000000000000000000000000000000000003ffffff9dcd000000000000000000000000000000000000000000000000000003af3ccd0000000000000000000000000000000000000000000000000000000003ffe827ff00000000000000000000000000000000000000000000000000000003ffe827ff00000000000000000000000000000000000000000000000000000003ffeb356632000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003fffffd0400
  | 2, 14 => 0x3fffffd0400000000000000000000000000000000000000000000000000000002ddf4ee9dcd000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000000000002fbff000000000000000000000000000000000000000000000000000003ffe827ff00000000000000000000000000000000000000000000000000000002ddf736fff2000000000000000000000000000000000000000000000000000003fffffd0400000000000000000000000000000000000000000000000000000003ffe8278400
  | 2, 15 => 0x3106232000000000000000000000000000000000000000000000000000003fffffd04ff000000000000000000000000000000000000000000000000000003fffcefffcd000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000000000002fbf200000000000000000000000000000000000000000000000000000000000000ff000000000000000000000000000000000000000000000000000003ffff37fff2000000000000000000000000000000000000000000000000000003ffffffffff
  | 3, 0 => 0x17d800ff00000000000000000000000000000000000000000000000000000050c3306632000000000000000000000000000000000000000000000000000000501712e2f20000000000000000000000000000000000000000000000000000000017d800ff000000000000000000000000000000000000000000000000000003ffff37fff20000000000000000000000000000000000000000000000000000000000cafbff00000000000000000000000000000000000000000000000000000050c0206600000000000000000000000000000000000000000000000000000003ff3fdfe2f2
  | 3, 1 => 0x3ffe827ff00000000000000000000000000000000000000000000000000000001221c0380c0000000000000000000000000000000000000000000000000000003ffe8279d0000000000000000000000000000000000000000000000000000000177dffbffff000000000000000000000000000000000000000000000000000003fffffd0400000000000000000000000000000000000000000000000000000003af3ccf99cd000000000000000000000000000000000000000000000000000003ffe827ff00000000000000000000000000000000000000000000000000000003fffced0400
  | 3, 2 => 0x12208010000000000000000000000000000000000000000000000000000000001721f110000000000000000000000000000000000000000000000000000000003ffe827ff000000000000000000000000000000000000000000000000000000000003100032000000000000000000000000000000000000000000000000000003ff3f17e2f2000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffffffffff
  | 3, 3 => 0x3ffffffffff000000000000000000000000000000000000000000000000000002ddf7feffff0000000000000000000000000000000000000000000000000000000017d800ff000000000000000000000000000000000000000000000000000002ddf7feffff0000000000000000000000000000000000000000000000000000000017d800ff000000000000000000000000000000000000000000000000000003fffffd04ff000000000000000000000000000000000000000000000000000003fa3fdffbff00000000000000000000000000000000000000000000000000000177dffbffff
  | 3, 4 => 0x3fffffd0400000000000000000000000000000000000000000000000000000003ff28050000000000000000000000000000000000000000000000000000000000000002fb000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ff2807fb00000000000000000000000000000000000000000000000000000003ffffffffff0000000000000000000000000000000000000000000000000000028837dc00ff
  | 3, 5 => 0x28d34cc000000000000000000000000000000000000000000000000000000000177df33fff2000000000000000000000000000000000000000000000000000002ddf7feffff000000000000000000000000000000000000000000000000000003ff3fdf99cd000000000000000000000000000000000000000000000000000003ffffffffff00000000000000000000000000000000000000000000000000000005c0eaffff000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffffff84c0
  | 3, 6 => 0x17d800ff000000000000000000000000000000000000000000000000000003fffffd0400000000000000000000000000000000000000000000000000000003ffffffffff000000000000000000000000000000000000000000000000000003ffffffe6f2000000000000000000000000000000000000000000000000000001720803e200000000000000000000000000000000000000000000000000000003ffff37fff2
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 438 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 438 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 438 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 438 then wireAt i else 0
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
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 2000006 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 2000006 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 2000006 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 2000006 ys) ys = true) : ¬ RunD dom_63 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_63 == dom_63) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 2000006 zs symsG zs (hk 2000006 zs)
theorem ori_ok {u ys} (h : RunD dom_63 goalM u ys) : RunD dom_63 goalM u (ori ys) :=
  pickMin_runD 2000006 ys h symsG ys (hk 2000006 ys) symsG_ok h

def Z (s : Nat) := bar dom_63 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 2000006 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_16 : ∀ i, 16 ≤ i → i < 32 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_32 : ∀ i, 32 ≤ i → i < 48 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_48 : ∀ i, 48 ≤ i → i < 60 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 48 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 60 → Z 4 i = true := (range_split (range_split z4_0 z4_16) (range_split z4_32 z4_48))
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
private theorem z5_192 : ∀ i, 192 ≤ i → i < 208 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_208 : ∀ i, 208 ≤ i → i < 224 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_224 : ∀ i, 224 ≤ i → i < 240 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_240 : ∀ i, 240 ≤ i → i < 256 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_256 : ∀ i, 256 ≤ i → i < 272 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_272 : ∀ i, 272 ≤ i → i < 288 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_288 : ∀ i, 288 ≤ i → i < 304 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_304 : ∀ i, 304 ≤ i → i < 320 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_320 : ∀ i, 320 ≤ i → i < 336 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_336 : ∀ i, 336 ≤ i → i < 352 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_352 : ∀ i, 352 ≤ i → i < 359 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 352 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 359 → Z 5 i = true := (range_split (range_split (range_split (range_split z5_0 z5_16) (range_split z5_32 (range_split z5_48 z5_64))) (range_split (range_split z5_80 (range_split z5_96 z5_112)) (range_split z5_128 (range_split z5_144 z5_160)))) (range_split (range_split (range_split z5_176 (range_split z5_192 z5_208)) (range_split z5_224 (range_split z5_240 z5_256))) (range_split (range_split z5_272 (range_split z5_288 z5_304)) (range_split z5_320 (range_split z5_336 z5_352)))))
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
private theorem z6_656 : ∀ i, 656 ≤ i → i < 665 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 656 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 665 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 (range_split z6_48 z6_64))) (range_split (range_split z6_80 z6_96) (range_split z6_112 (range_split z6_128 z6_144)))) (range_split (range_split (range_split z6_160 z6_176) (range_split z6_192 (range_split z6_208 z6_224))) (range_split (range_split z6_240 (range_split z6_256 z6_272)) (range_split z6_288 (range_split z6_304 z6_320))))) (range_split (range_split (range_split (range_split z6_336 z6_352) (range_split z6_368 (range_split z6_384 z6_400))) (range_split (range_split z6_416 z6_432) (range_split z6_448 (range_split z6_464 z6_480)))) (range_split (range_split (range_split z6_496 z6_512) (range_split z6_528 (range_split z6_544 z6_560))) (range_split (range_split z6_576 (range_split z6_592 z6_608)) (range_split z6_624 (range_split z6_640 z6_656))))))
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
private theorem z7_304 : ∀ i, 304 ≤ i → i < 311 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 7 304 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 311 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 (range_split z7_48 z7_64))) (range_split (range_split z7_80 z7_96) (range_split z7_112 (range_split z7_128 z7_144)))) (range_split (range_split (range_split z7_160 z7_176) (range_split z7_192 (range_split z7_208 z7_224))) (range_split (range_split z7_240 z7_256) (range_split z7_272 (range_split z7_288 z7_304)))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 23 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 7 16 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 23 → Z 8 i = true := (range_split z8_0 z8_16)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 14]⟩], 15⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 10 := by decide

theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (3901261952 * 2 ^ 32 + 2290124928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (3901261952 * 2 ^ 32 + 2290124928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3901261952 * 2 ^ 32 + 2290124928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 10 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (3901261952 * 2 ^ 32 + 2290124928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 10 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_12809_aux

theorem PEqualNP.Outside.L_meta_12809 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3901261952 * 2 ^ 32 + 2290124928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3901261952 * 2 ^ 32 + 2290124928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_12809_aux.wit, PEqualNP.Outside.L_meta_12809_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_12809_aux.wit_sz (PEqualNP.Outside.L_meta_12809_aux.lower s hs), PEqualNP.Outside.L_meta_12809_aux.wit_ev⟩
