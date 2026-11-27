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

namespace PEqualNP.Outside.L_meta_12829_aux

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
def goal_31 : Nat := 0xe8000000e8000000e8000000e8000000e8000000e8000000e8000000e8000000
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xaa88888888000000aa88888888000000aa88888888000000aa88888888000000
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xaaa0a0a0a0000000aaa0a0a0a0000000aaa0a0a0a0000000aaa0a0a0a0000000
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xeaa8a8a8e8000000eaa8a8a8e8000000eaa8a8a8e8000000eaa8a8a8e8000000
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_31
def pairsG : List (Nat × Nat) := [(11, 27), (13, 29), (14, 30), (15, 31), (19, 27), (21, 29), (22, 30), (23, 31), (25, 27), (25, 29), (26, 27), (26, 30), (28, 29), (28, 30)]
def r1sG : List Nat := [11, 13, 14, 15, 19, 21, 22, 23, 25, 25, 26, 26, 28, 28]
def r2sG : List Nat := [27, 29, 30, 31, 27, 29, 30, 31, 27, 29, 27, 30, 29, 30]
def mpG : Nat := 0x3fff
def pool6G : List Nat := [28695148240155]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x429d6d17
  | 5, 0 => 0x1f16380d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000aaaaaaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x6884
  | 5, 0, 0 => 0x58885
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
  | 0, 0 => 0x3ff00000000000000000000000000000000000000000000000000000000000003f0f0000000000000000000000000000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000030ee0000000000000000000000000000000000000000000000000000000000000cdd00000000000000000000000000000000000000000000000000000000000003bb
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3fff0000000000000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000003aee0000000000000000000000000000000000000000000000000000000000002ddd00000000000000000000000000000000000000000000000000000000000017bb
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_31 == dom_31) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_31 goalM u ys) : RunD dom_31 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_31 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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

namespace S_59
def pairsG : List (Nat × Nat) := [(3, 35), (11, 27), (11, 43), (19, 27), (19, 51), (25, 27), (25, 57), (26, 27), (33, 35), (34, 35), (41, 43), (41, 57), (42, 43), (49, 51), (49, 57), (50, 51), (56, 57), (58, 59)]
def r1sG : List Nat := [3, 11, 11, 19, 19, 25, 25, 26, 33, 34, 41, 41, 42, 49, 49, 50, 56, 58]
def r2sG : List Nat := [35, 27, 43, 27, 51, 27, 57, 27, 35, 35, 43, 57, 43, 51, 57, 51, 57, 59]
def mpG : Nat := 0x3ffff
def pool6G : List Nat := [45127644551971]
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xe051932
  | 5, 0 => 0xf0260ba
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f00000f0f00000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x6884
  | 5, 0, 0 => 0x3b085
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
  | 0, 0 => 0x3e0f80000000000000000000000000000000000000000000000000000000000031ce6000000000000000000000000000000000000000000000000000000000003ff0000000000000000000000000000000000000000000000000000000000000300e0000000000000000000000000000000000000000000000000000000000002929f0000000000000000000000000000000000000000000000000000000000006d7f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3e8fa0000000000000000000000000000000000000000000000000000000000035cee000000000000000000000000000000000000000000000000000000000003ff5500000000000000000000000000000000000000000000000000000000000348ea000000000000000000000000000000000000000000000000000000000002b7bf000000000000000000000000000000000000000000000000000000000003ffff
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
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

def isoMv_61 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_61 : Lower dom_61 roots_61 goal_61 6 :=
  lower_iso isoMv_61 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59

namespace S_63
def pairsG : List (Nat × Nat) := [(3, 35), (5, 37), (7, 39), (11, 27), (11, 43), (13, 29), (13, 45), (14, 30), (15, 31), (15, 47), (19, 27), (19, 51), (21, 29), (21, 53), (22, 30), (23, 31), (23, 55), (25, 27), (25, 29), (25, 57), (26, 27), (26, 30), (28, 29), (28, 30), (33, 35), (33, 37), (34, 35), (36, 37), (38, 39), (41, 43), (41, 45), (41, 57), (42, 43), (44, 45), (46, 47), (46, 62), (49, 51), (49, 53), (49, 57), (50, 51), (52, 53), (54, 55), (54, 62), (56, 57), (58, 59), (58, 62), (60, 61), (60, 62)]
def r1sG : List Nat := [3, 5, 7, 11, 11, 13, 13, 14, 15, 15, 19, 19, 21, 21, 22, 23, 23, 25, 25, 25, 26, 26, 28, 28, 33, 33, 34, 36, 38, 41, 41, 41, 42, 44, 46, 46, 49, 49, 49, 50, 52, 54, 54, 56, 58, 58, 60, 60]
def r2sG : List Nat := [35, 37, 39, 27, 43, 29, 45, 30, 31, 47, 27, 51, 29, 53, 30, 31, 55, 27, 29, 57, 27, 30, 29, 30, 35, 37, 35, 37, 39, 43, 45, 57, 43, 45, 47, 62, 51, 53, 57, 51, 53, 55, 62, 57, 59, 62, 61, 62]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := [27737907404059, 45144824421669, 53983831597881, 66220496069406, 66035895903517, 27552906814235, 45278522056229, 45278555945251, 45187604489017, 45127644551971, 27746463783709, 63836872647451, 45329858569017, 45187604357945, 27552906814749, 66220227107614, 45145378069283, 53983831728953, 45145411624229, 54109008702755]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 3 => 5
  | 4 => 37
  | 5 => 337
  | 6 => 694
  | 7 => 341
  | 8 => 28
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xae8a22a00f7b6a330d6aa4da0c185e19026570e9
  | 4, 0 => 0xfdc727f3fdacb753f389c546f23bbe98ea7d39edc14e84b8b3e5126c9d0d85119ab2ad6c9931e9c993c0ee807f9573b47f8a2a2e794eed166fc52cbc6ebb5a156a1cedd35ca7aa2d5b55636c58dab83e585180a956467eff52f3cad952ad834a49d3246047e1dca540c29408331931053289af9531a04beb2bbce70b264b3f1524c36e3c092ba6400587900a01e3c43b00f423d5
  | 5, 0 => 0x1ab519e21899b86717a004ee16d3f79316ab53c7165cf3ef1631a87a162cf7fa15e54e0815d8317d15c3c18e15b0ac75159b45de1576a520155f67921544da04153d02491518792114d5401f149b11461240051a121c3a63108b8a0b107c71be0f5330560f04417e0e145e410e0d68af0de7d6990d9158170d8430840d30cc650d213aee0ca3b5de0beb36e60a2cb4c50a2600ba09a0fe5c095df6610951df97094b62fb0912ca5208f9643708ea75770841c757075a63c907093d2d06f3c1a406a870980698056c060cfabc0605230105b3b17b0547786b054381ac0455a23603bb8493018ceefd011b3b88010c1dae00c7517a00993710005ca16e0018fe40
  | 5, 1 => 0x39d36a8639ba3f4039acc16137ecdb2c37e42bcb37d0390937443c1c3729877435beb1983582462c355a8dfa35284ef23521f51434c050cd349030253420ed1034053dc333c52b4c33b83bd53304b74f3248972b30562d283028f74d2ee6ee1d2de1b2802c696c5f2b8bdee22b645d1c2b34f6dd2ace9a7b2a6d8d952a4657642952ef832918f669286457e927b5a7f7277e79b02756de8127350e5c27161fbe26e39cd625c2dc4125bac1402580ac6124d3bdbe247dd024241f6edb234a6af5224bebcd21b083ee20fd535520bb3e34202215df1fdd61af1fc5b8981f8bf0291f4d8c0d1ec5b8031e0bed1d1d0859221cc9375f1bd3245e1ba21b801af8b90b
  | 5, 2 => 0x69d5bb3f695818d96839f0cf655ad64e64e2e0e864c254c96495b982648096b061aad709602a52d45ff3b96e5e0764505def06025ccbebb55c8ef2e25b0f7efa5af8969459df37c55868ab935838558d56ba5557564adc495520b94053ce63d852f5dd0f51556fd650c57f25503692094fd398b54fadc8374f62a8aa4e2b0ded4d6da1fd4d3d2e774cdc2c694c8580eb4ba4cd744b9e3062499443444950036d48bd4d1c471a0127471174ec4614b69e457a831344c24944449e0eb4444d20c743d808f542693a26423c969741c024ee40fdd0fc40472c733ff4b1fb3fd961d43fc2547a3f3bd8783f2e36033cdf60253cc8cf463b71a1f13a5c63fc3a35f98c
  | 5, 3 => 0x927bcf85925794f591b2de17912e35f18f694bdd8f669c5b8f4176b68dc247a88dbab4a58d92e8158cd255398bbd18f98b9bb48d8b914ae588f47c92889102ba8765c6cd85a2f0e18566d58b84f088cf8343f03d82ec5e8482d873288256365881f8a5e58169247580bfe24a7f398d6e7e6df8307ddfc3857d8dde997c1ef8387c10fd197aa0f93879a31a497901b78e78fdbc6678f95c1f7884234f78411ace783f515677a8cfb37400738f73cd98ca73a2e31c72abb1637169ccd370caeaac70247258700099d26fcb29176e65b8fc6e47276b6de131746d3037af6c7732dc6c4b366f6bef7e7c6bd61afa6b3b58946b3302896b1b0b0e6a0153b269ffd8c5
  | 5, 4 => 0xdee7bc32dd786d7fdc68c52bd8c8f7add782d93ed3c4fb9bd1bc323fd1714b00d09c6c75d07831e5cfb22c26cec72f81cc4c8453cae03226c944bfc8c9208538c912d05bc85a7f79c71bb9dec6d0eb9ac66596eec4c28815c3f97584c32089dbc09a3948be8025d2be22ba5cbdddf899bdba2013bafd2c94b9bb78f2b5a82bdcaf827893ae8240cbaca2ec6fac882e07aa4b26daa8fd8e1ea817bd91a8053271a7fed1d9a7bef26aa64396b3a4ec4fb7a473db98a382d075a230d02c9f6389839f3a67fb9d1c2eeb9ced77399c668d2a9c10f3a49bdd69509b62c2e699bd0b2a99a4098a994dccbb9928fef1969da615969d17a0954ea561948c59b5948480a3
  | 5, 5 => 0xff48eca9fbdabd03fb8052e0fa848bb3f4831056f19a073fefb5790deef3a935ecc2ca25eba51355ea068976e685b98fe51519a7e3d414e6e12d67dce00b8f5adf65ce46
  | 6, 0 => 0x92abfff090ca4c608eb11d108ac7f4d08a714d3088b9c37083137aa07fe25ca07eef28307c7e419075214f3071ebcc6070b6e2706e8fa1e06a21a9606974e47068dc3d406533b14063e36ac061ec7a905e9292305b7cf9e05a7632d05a41c4f0573298d0567fa510548a319052c1ca10524aa2c05205a4f050765bb04e59b660478b5ba045a056d04547ac4041907b603fe10b503e841790390b6ab033a0399031c97500303e9e102db71a002d338cd02be7c8f02ba592d0253d81a02316af2022760e602187aa1020bcdff0207ae4701a662a4019e8ae9018ceefd0184b62a016803c5014d19630135cd9e0104b42a00ae069d0084b00c0010041b0004ac72
  | 6, 1 => 0x170d28fa1708ce88170095b516cbbec0169df71915ec0d8c15a29c4115572c4b14c5e0891411bdaa13ff8d6813e889c513e23a6c13b4674d13b13c8e12d5559812bd260c12a8906c12865704126c23b3125d8f2e1231effa120d6b6211fcb88511bd9e8d119628b51182c6e910ee966510d6ef0210a19280108f73d2108dfb001080f77b10447bb51042be7e0fd73e9b0f90e7c10f1265740f0a2ca10ed48efb0dcca35d0dc576640dbee7360db727de0db0d3410d53e0f30d3fb90d0d062b040d022f3c0ce919930cbf98d00c76b2fc0c01601d0bbb8de80aa50bd80a9320a80a65f1e00a51fbae0a41a4680a3edfed0a3e7c080a0ee3b50a077844097f4255
  | 6, 2 => 0x21f924cf21f40ce021d6d25821c73131218e150a2178553b213afd3d212acd6b2121119d2039fdd72014b8841fe698911fe1492a1fd97b401fd971c81fc7531a1fb537381f5260d61f4a28031ed2190f1e9e501c1e68e75a1e14d0a91de8e6291de7b9e61dc0fec81da9ff4c1d815c911d7550671d226a7c1cef07261cbb8ef71c1999991c0b1db81bdc203c1b9784951b8989a61b02c6a81af8b90b1af080381ae554351a81704b1a49943a1a3d0b5f19f7a8a219b9c86819af0e96193a835c191a7492191504cd1899b86718917f9418667dc9185e1bcc185ae16017f9b8d517e5a7ad179c2862178f9dc81783d36c17744cf81772a8cc175007131746a36f
  | 6, 3 => 0x314fc4ae3123d1e430c2e3c530b17a1b30b16133306a6d2f3020be7a2fe980262f4894ad2f208b1c2ee713392eb1aa0b2ea2d3992e9e1f372e83174c2e80e4e22e6f67852e2316352df8a9bb2df2d40c2dc731122d9892a42d5f599c2d54ddfd2d089e7e2cfd4cb22c05dd8b2be4e1ff2b66d5862b42fd002b148d062aef28452ae868082ae33e892ad82ba32a9abfe92a79d12e2a72c5ea2a410c03297c39cb294cfc67291eddde28c018cf2898708b2878be4a2858b903283a5cab27bf8f03279ca96f278f668c26bfde9126aab89b2697822c267565b7260e4a0125eb7b9e258ba3c2254f9c342472445d242252ba23fdbfd12399ecf5228dce74228cec06
  | 6, 4 => 0x3e51fe3b3de6e0fa3d7b1e3a3d3b09133cd136d53cc117773c92cbfc3c904c443c153f903bffcf783bcc4b8e3bc3c4033bb15ba63b9858393b3a508c3aae250c3a966a373a728eb639ff6add39f3fa0039c1856939a6d15b395f96ae394fcac638e67e7b38650d423835c84a37a5ab2f3749397d37014dae369255f03666b6bc362b34f13628707535f5cbe435e35c66353b1f4f35389f97352437813516c61635149d4134bd92e334abc1a934903025346cac5b3459aef9344e166f34173658340c055d340becb23403849233c5ae8333bde23333b0f4e3339aa85e3385f82632a284ca32998b1f329818b032008a2931d17ddb31be316231762d40316263f9
  | 6, 5 => 0x4df7db8b4d49a27a4d19165d4ceed47c4cad02654c8580eb4c7d48184c70991f4c3ac3c24bd170314b5ff9ff4b3b9adc4b014a6c4afba34b4af4a5534af042774a974fec49b49b7f49473550491db07c482f817747ed9aea47a969a647989971477980054771079a476239784742a665471174ec46a02ede463a036a456314394547719244e3171544c2494444b44fa8449e0eb44487986f4479c38444077fe143d808f543a4ce57437897f0436e606b433fa33f4323f83b42c3905b426f306142549ca3421efd3341814761417c5d4241794a5040f3cff040d70c92409f53bf40957cd93fd961d43fd129013fcc33923fa0d0453f426cc83eff18133ebf5c10
  | 6, 6 => 0x64902155648c06136412729763e8e7d06371ca5a632c34926327452262d8cb5d628562b1621e5cc161c7aebf617feb5d6175ec1e6130f73c603fdd455f3c4a0f5f16df6a5ed8f8ec5e71f8f65dd275755d9e8de65d5806125d4a6e025cf3af5e5cf2b5ff5c8e153c5c70547a5c6222725ac6b0145a7db4f65a56ee1d59efc1ef599395ba590705f9584aebb9578562665745e0fb56ba55575600596555d4f3af559c02b1559b0952557f5c915570a40354a14f27549f33f15439eb12540cc15553ddd8b052fa52d052b7fb2a52b7de0e50befcef50a15f1c509686335003739f4fd63c634f8a3cb44f62a8aa4ed591294ece75b34e8eef6e4e85f1fc4e18f756
  | 6, 7 => 0x79ae0f5b7976ef16796e7aac79695e7b796125a878b54dc1787b7f05784a37a477c76e4b77a0836a776db15b76eb3a0376824124767213af763ffe9e7603a2dd75d13e927569d66d7556053274391d8f73bf4b2f72e0b30772b3d5a2729330ea728770487280f6f372066a1f71c71b6c715da11470ec153c706fc19e703bd372702472587000bd14700099d26ff228d76fcf60ac6f2dc9df6e1229c06e01e0e96d89a1566cd020406c455e756be7ce026bce56ea6ba140276b3302896adf20d36a7ef1cf6a5cbad96a41252269d31fda69849433689eda7668949545684ea6b867d08ebb674ae0a66694b153667b89e26624a0836610fce664ef0a7e64b2bd55
  | 6, 8 => 0x9b62c2e69b27740c9b0979a598dcea6c989ff3f89819f35697eba1149708cd8896df67cc96d84bf496bc370a9669b5ff95fbb0b79522500394135e45934f2dc492b50c7c92378418922d5e4591d301e19180cfe5912e35f19105869590800e378fbee73e8f8431c68e6b3b568e4f031a8c0b847c8b7565708ad5b1988a7a9db889cec5d18972fedf88b2df66880cdd5b86c3d16f862eae4f85bc058485b1d12f857a583d8577d88584fccbd18498e7e783fd562083e9d4988277192481f8a5e5819b4b08817f34c481280c0b8103242c80c29efb80a2987a7fa1e4517f5d02fb7edd58257e6b005c7e23f3707d9e80da7bb3936c7b585cdd7aa0f9387a1a3cad
  | 6, 9 => 0xc1438dfbc007efffbfdf6e4bbdba2013bc8b9d4cbc816ce9bc449060bbbb672abba988a8ba7793f7b8c40a61b80fdac9b7f25385b792a617b7378433b5807d58b533f09fb4ece3b3b4cf5a43b49a3c00b3b8f888b3667e10b34b2de9b2a00218b2295fe2b152b547b0b8a8cbb03b1c5fb03a9b5bafd73875af80e77bae8240cbadce3011ad2c0b55acdfed75ac927f2dab42051eaafd3858aae1ae72aa9b5389aa939139aa4c844da9eef3daa8293acea7f3bccaa6768364a672e862a63f9253a61d0192a5f75aaaa5db3b9fa54a4c99a4f9c347a4dcb8cea3114d8fa297472da296fa28a1be6f73a0adc3c8a09c101d9e5830449d44baad9d1af28d9b6b0af2
  | 6, 10 => 0xff9e1ca2fc02cecffbdabd03f9dc041af6b5bc52f61e82b4f4831056f429550af2d6801bf284576df2578dfeefc4761aef82c92ee8857962e85bc3b8e7e3f807e3963e6de35b6f70e2c86a22e275d4c1e1d78511e12d67dce00daad1df4068ffdcd0d1a0d9f03bcfd8bb100ad89e551dd4ec5e95d4a3daded3758bc5d2e91d17d24b31b6d10549abd03db7cacfb22c26cc6fa00acae03226ca2c216cc8eb047cc89b3aa8c85a7f79c82bc7c7c802f5cdc72b1105c71bb9dec5627f99c517f35dc484c5f5c47189c5c3eb310fc2d474bfc21db85ac15ff605
  | 7, 0 => 0x168319a4167ebc1d1658ec56161ad83315303b8814c25be7147be17a147387c814445611141f8fdd140ddc3213ec0a3313b478a2131d3b5412865704126595bb11f546a611c9fc59108cbea2106602d20feca8e60f90e7c10edcd7070ed48efb0ecd7e060eccb7400de1f81f0db6ae630db3a33c0c3afa680c28dbba0c11c00d0c0c577e0b8bbf6b0b5d6d290ae68dfb0a6e47250a5133e10a4a180909c8d28f09508fc6093db6800879d88b0801277907f908f707852a5a07540f0806533b14058c8cb80544cdf60499b2c1046cf47e045a056d0451cc9a0402104d03edab4903a5f4b302fbbdeb02f5fddb02c7e1c60218385101dd076b01c0cf2f00f26ece
  | 7, 1 => 0x3123d1e430b17a1b30a94148306a6d2f2ffd69612fda20902f1086872eb1aa0b2e7627092dc35a212d6fbb802d6782ad2ceb381e2c9d909e2b42fd002ad82ba32ad2a9b42aa950482944441728f2496d28a5bcb428615818280c0815264ce74e24f1d90e24c4815c242a74e0241a19e72358f6eb22f2b390225227cd21f40ce0212bd53220c5498720bd10b42039fdd7201138cd1ed943511e14d0a91dbf2e791d0c61251c879ee11c1999991c0b1db81c02e4e51bd38e271b9b06e31b96e8611b6588df1ae554351a1b5c1a19c2d80519b15e68196939d2196926bf194d07b418b98c20189246be186b8f5c17a485a01780280516fc488916ed244d169ad4dc
  | 7, 2 => 0x5164663950c1bb7d509cfade50429db54f85907a4f1c75a54d2885244c1021324b550f7149d837ae48a30f48477294e646e757da4667b1cb46514a8f4514c0b444aae86243d808f543a4ce574323f83b42a809fe417604ab4125de8a4102d7c740fe68b240957cd9400015073fe16c1f3fd89f2f3ef2c9303e51fe3b3de6e0fa3d7b1e3a3d3b09133d32d0403cc117773ca49d893c5cd0913c153f903bcc4b8e3aefec363a9cdd1a3a2919be39ab2b1a3889bf723849566837c1829f375d2beb375c328c35e35c6635db2393358f846f35895b043578c84e352ef43834d1c21a34bd92e333c5ae8333ac494933513a60333c765831c49cd931c32ec3315f0dca
  | 7, 3 => 0x8a7a9a9d88c8f860861a5c8185cf5b4385bc058485a3bc0f8507f4ca84fccbd18458706783b31a7d83490ab08302b3d682843189824f20f681f8a5e58077f7197db3707d7db0481d7c3a52057b7c8fb07ac3e1087aa0f93879ff8fe979fc07f678e4f5a276abcfae75a337077280f6f371e3fb2171cce639700099d26e01e0e96d5d4dc16b0a84206afb3f026ad542766a75398c69904ec96986998d679e3ab8679b211f6722ad0067103ec5664a2e4d6608c413655e0be164bb1a68644d152062125aeb61b0ce8d61279f2a6013f4555ed8f8ec5e4f53365d017f515c6222725a910ab5595bb8d457c463485723328d53970991538ed0be537f76e652b23514
  | 7, 4 => 0xcae03226ca2c216cc99680d2c972257ac8e27018c2d474bfc21db85ac18ac36bc169a7a0c060a091bf74c458bead66f1be620e8cba11faf3b7f96484b7794bf6b749d50ab70d940eb40748eeb34b2de9b0b8a8cbb03b1c5fb0049811afd73875af359018aeeee7d9acd99b96a8aceb64a888922ba7420870a6ea9da8a5f75aaaa54349f0a4e7f955a4234630a3dc3944a37ea8d1a32c9765a304b735a10a5eb9a0c6aa129e86591b9deb9d439d44baad9cee05e09c31e4e49c26fc249bea8a5f9bca85189a31aaa697e4107296f519d996ae0ced94dbd1b49492ddb291869cbe90943691902d5b0c8f8b65ae8d8425078c8c40a78c0b847c8b9a7c8c8ac1d328
  | 7, 5 => 0xf92dd199f61e82b4f56a71faee12c54dec663512e6527f1ce5f93c5de3963e6de173acfee00daad1dea4ce9eddce86eedabf3809dabcacbbd5f72ec6d3678b5cd24ac501d17de2e1d0c9d227cdef810bcdc8ba32
  | 8, 0 => 0xf92dd199f61e82b4f56a71faee12c54db749d50ab40748eeb03b1c5fa4234630a0e187958ff96af68f8b65ae8302b3d669904ec95d017f515c6222724e31041e46d9577144efaef6448b58423ef2c9303e51fe3b3d084ce7358f846f242a74e0196926bf1957081117a485a0167ebc1d
  | 9, 0 => 0x69904ec9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xfa000000fa000000000000000000000000000000000000000000000000000000ecececececececec000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000e8e8e8e8e8e8e8e8000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000eeaaaaaacc000000000000000000000000000000000000000000000000000000aa888888aa888888
  | 0, 1 => 0xcccccccccccccccc000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000cc888888cc000000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ea000000ea000000000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8
  | 0, 2 => 0xf0a0a0a0f0a0a0a0000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000eaea0000eaea0000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c8000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000fff0f0f0fff0f0f0000000000000000000000000000000000000000000000000faaaaaaaf0000000
  | 0, 3 => 0xaaa0a0a0aaa0a0a0000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea00000000000000000000000000000000000000000000000055aaaaaa55aaaaaa0000000000000000000000000000000000000000000000009999999999999999000000000000000000000000000000000000000000000000ffaaaaaa00000000000000000000000000000000000000000000000000000000ff000000cc000000000000000000000000000000000000000000000000000000aaaaaaaaaa000000000000000000000000000000000000000000000000000000aaaaaaaa55555555
  | 0, 4 => 0xaaaaaaaaa8000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0000000000000000000000000000000000000000000000000000000cccccccc33333333000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e00000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000cc333333cc333333000000000000000000000000000000000000000000000000f0000000f0000000
  | 0, 5 => 0xc0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000ff00000000ffffff000000000000000000000000000000000000000000000000f8f8f8f8f8f8f8f8000000000000000000000000000000000000000000000000ee00ee00ee00ee00000000000000000000000000000000000000000000000000c3c3c3c3c3c3c3c3000000000000000000000000000000000000000000000000ee000000ee000000000000000000000000000000000000000000000000000000ffff0000ffff0000
  | 0, 6 => 0xf0f0f000f0f0f000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000ffaaffaa0000000000000000000000000000000000000000000000000000000000ffffff00ffffff000000000000000000000000000000000000000000000000cccccccccc000000000000000000000000000000000000000000000000000000cc888888cc888888000000000000000000000000000000000000000000000000aa555555aa555555
  | 0, 7 => 0xffccccccffcccccc000000000000000000000000000000000000000000000000cc000000cc0000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000ffffffaa00000000000000000000000000000000000000000000000000000000cccc8888cccc8888000000000000000000000000000000000000000000000000f0f0f0f0e0e0e0e0000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000000000000000000000000000000000003333333333333333
  | 0, 8 => 0xaaaaaaaaaaaa8888000000000000000000000000000000000000000000000000fafa0000fafa0000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000aaaa8888aaaa8888000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000ff555555ff5555550000000000000000000000000000000000000000000000005500000055000000000000000000000000000000000000000000000000000000ffffffff55555555
  | 0, 9 => 0xec000000ec000000000000000000000000000000000000000000000000000000fa00fa00fa00fa00000000000000000000000000000000000000000000000000ffffffffcc0000000000000000000000000000000000000000000000000000005555555555555555000000000000000000000000000000000000000000000000aaffffff00000000000000000000000000000000000000000000000000000000ffffffff88000000000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000000aaaaaaaaaaaaaa00
  | 0, 10 => 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000ff000000fc000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000f0f0f0f0f000f000000000000000000000000000000000000000000000000000aaaaaaaaaaaaffff000000000000000000000000000000000000000000000000cccc3333cccc3333000000000000000000000000000000000000000000000000ffffffff55550000000000000000000000000000000000000000000000000000aaaaaaaaa8a8a8a8
  | 0, 11 => 0xf0f0fcfcf0f0fcfc000000000000000000000000000000000000000000000000332233223322332200000000000000000000000000000000000000000000000000000000aaaaaaaa000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000000000cc000000ffffffff0000000000000000000000000000000000000000000000005555555555000000000000000000000000000000000000000000000000000000000000000fffffff
  | 0, 12 => 0xaaffaaffaaffaaff000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000aaaaaaaaaa00aa00000000000000000000000000000000000000000000000000ffffffffff000000000000000000000000000000000000000000000000000000f0a0f0a0f000f000000000000000000000000000000000000000000000000000ff000000ee000000000000000000000000000000000000000000000000000000ffaaaaaaffaaaaaa00000000000000000000000000000000000000000000000000000000ffffffff
  | 0, 13 => 0xc8888888c8888888000000000000000000000000000000000000000000000000f0f0f0f0f0f000000000000000000000000000000000000000000000000000000707070707070707000000000000000000000000000000000000000000000000fffffffff00000000000000000000000000000000000000000000000000000000f0f0f0f0fff0fff000000000000000000000000000000000000000000000000ff0000ffff0000ff000000000000000000000000000000000000000000000000fffffffff0f0f0f0000000000000000000000000000000000000000000000000aaa8a8a8aaa8a8a8
  | 0, 14 => 0xccccccccccccffff000000000000000000000000000000000000000000000000ff050505ff050505000000000000000000000000000000000000000000000000aaffffffaaffffff00000000000000000000000000000000000000000000000000aaaaaa00aaaaaa000000000000000000000000000000000000000000000000ff00ff00aa00aa00000000000000000000000000000000000000000000000000ff110000ff110000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000ffffffff55000000
  | 0, 15 => 0xeeaaaaaaeeaaaaaa000000000000000000000000000000000000000000000000ffaaaaaaff000000000000000000000000000000000000000000000000000000cccccccccccc0000000000000000000000000000000000000000000000000000aaffaaff00000000000000000000000000000000000000000000000000000000ffffffff00555555000000000000000000000000000000000000000000000000f0f0f0f0f0ffffff000000000000000000000000000000000000000000000000ffffffff00005555000000000000000000000000000000000000000000000000fffffcfc00000000
  | 1, 0 => 0xf0f0f0f0f00000000000000000000000000000000000000000000000000000000000000ffffaaaa000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a0000000000000000000000000000000000000000000000000f0f0e0e0f0f0e0e0000000000000000000000000000000000000000000000000ccccccccccc0ccc0000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000b3b3b3b3b3b3b3b300000000000000000000000000000000000000000000000000000000ffaaaaaa
  | 1, 1 => 0xfffcfcfc0000000000000000000000000000000000000000000000000000000000eeeeee00eeeeee000000000000000000000000000000000000000000000000f0f0f0f00f0f0f0f000000000000000000000000000000000000000000000000aaaaaa00aaaaaa000000000000000000000000000000000000000000000000000000000055555555000000000000000000000000000000000000000000000000ececccccececcccc00000000000000000000000000000000000000000000000033337777333377770000000000000000000000000000000000000000000000000055555500555555
  | 1, 2 => 0xfc000000fc000000000000000000000000000000000000000000000000000000ccfcfcfcccfcfcfc000000000000000000000000000000000000000000000000f0f0a0a0f0f00000000000000000000000000000000000000000000000000000eeeeaaaa00000000000000000000000000000000000000000000000000000000ffffffff05050505000000000000000000000000000000000000000000000000ffff0000ff00000000000000000000000000000000000000000000000000000055555555ffffffff000000000000000000000000000000000000000000000000ff00ff0000000000
  | 1, 3 => 0xfefefefe000000000000000000000000000000000000000000000000000000005555555555ff55ff000000000000000000000000000000000000000000000000ccccddddccccdddd00000000000000000000000000000000000000000000000005ffffff05ffffff000000000000000000000000000000000000000000000000f0f0f0f0f0f0a0a0000000000000000000000000000000000000000000000000dddddddddddddddd0000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000a5a5a5a5a5a5a5a5
  | 1, 4 => 0xffffffffcccccccc00000000000000000000000000000000000000000000000000555555ffffffff000000000000000000000000000000000000000000000000f0f0f0f0f0a0a0a0000000000000000000000000000000000000000000000000aaaaaaaaa0000000000000000000000000000000000000000000000000000000ccddddddccdddddd000000000000000000000000000000000000000000000000aaaa5555aaaa55550000000000000000000000000000000000000000000000000f0f0f0f0f000f00000000000000000000000000000000000000000000000000fffafafa00000000
  | 1, 5 => 0xeaeaeaea00000000000000000000000000000000000000000000000000000000c8c88888c8c88888000000000000000000000000000000000000000000000000ffffffffaaaa000000000000000000000000000000000000000000000000000005050505ffffffff000000000000000000000000000000000000000000000000ffffffff00ffffff00000000000000000000000000000000000000000000000000ffffff00000000000000000000000000000000000000000000000000000000ffffeeee00000000000000000000000000000000000000000000000000000000ffffffff44444444
  | 1, 6 => 0xcccccccc000000000000000000000000000000000000000000000000000000003377777733777777000000000000000000000000000000000000000000000000cccccccccccccc00000000000000000000000000000000000000000000000000f8f0f0f0f8f0f0f0000000000000000000000000000000000000000000000000f1f1f1f1f1f1f1f1000000000000000000000000000000000000000000000000ff00aa00ff00aa000000000000000000000000000000000000000000000000003737373737373737000000000000000000000000000000000000000000000000eecccccceecccccc
  | 1, 7 => 0x55ffffff55ffffff000000000000000000000000000000000000000000000000ffff00000000ffff000000000000000000000000000000000000000000000000f0f0f0f0f0c0c0c0000000000000000000000000000000000000000000000000f0e0e0e0f0e0e0e00000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e00000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000055555555555500000000000000000000000000000000000000000000000000001111111111111111
  | 1, 8 => 0x5555ffffffff000000000000000000000000000000000000000000000000fe000000fe00000000000000000000000000000000000000000000000000000055ff55ff55ff55ff000000000000000000000000000000000000000000000000f0fffffff0ffffff00000000000000000000000000000000000000000000000000f0f0f000f0f0f0000000000000000000000000000000000000000000000000eeeeeeeecccccccc000000000000000000000000000000000000000000000000cccccc88cccccc88000000000000000000000000000000000000000000000000aaa8aaa8aaa8aaa8
  | 1, 9 => 0xffffffffaaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaaaaa0a0a000000000000000000000000000000000000000000000000055aa55aa55aa55aa00000000000000000000000000000000000000000000000033222222332222220000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000ff00aa00ff0000000000000000000000000000000000000000000000000000005555555555ffffff00000000000000000000000000000000000000000000000000ffff0000ffff00
  | 1, 10 => 0xff000000aa0000000000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000fffffffffc000000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000eeaaaaaa000000000000000000000000000000000000000000000000000000000f0f0f0f0fffffff000000000000000000000000000000000000000000000000ffffffffaa0000000000000000000000000000000000000000000000000000005555000055550000
  | 1, 11 => 0xffa0ffa0ffa0ffa00000000000000000000000000000000000000000000000002222222222222222000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000ff005500ff0055000000000000000000000000000000000000000000000000000f0f0f0f0f0f000000000000000000000000000000000000000000000000000000ff00ff00ff00ff0000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000aaaaaaaaaaffffff
  | 1, 12 => 0xccffffffccffffff000000000000000000000000000000000000000000000000ffff00ffffff00ff000000000000000000000000000000000000000000000000ffffff00ffffff00000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffc0c0c0ffc0c0c0000000000000000000000000000000000000000000000000fff0fff0fff0fff00000000000000000000000000000000000000000000000000000ffcc0000ffcc000000000000000000000000000000000000000000000000cdcdcdcdcdcdcdcd
  | 1, 13 => 0xff00aa00ff00aa000000000000000000000000000000000000000000000000ffff0000ffcc000000000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000000f5f5f5f5f5f5f5f50000000000000000000000000000000000000000000000005050505050505050000000000000000000000000000000000000000000000000ff00fff0ff00fff0000000000000000000000000000000000000000000000000f0f0f0f0f0f0ffff000000000000000000000000000000000000000000000000fff0fff0f0f0f0f0
  | 1, 14 => 0xffffffffffffcccc000000000000000000000000000000000000000000000000fffc0000fffc0000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000ffff000fffff000f000000000000000000000000000000000000000000000000ffcc0000ffcc0000
  | 1, 15 => 0xccc0c0c0ccc0c0c0000000000000000000000000000000000000000000000000ff00ffffff00ffff00000000000000000000000000000000000000000000000005ff05ff05ff05ff000000000000000000000000000000000000000000000000ffff0000aaaa00000000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000000cc00cc00cc00cc000000000000000000000000000000000000000000000000aaaaa0a0aaaaa0a0
  | 2, 0 => 0xfff0fff0ff00ff00000000000000000000000000000000000000000000000000cccccccccc00cc00000000000000000000000000000000000000000000000000aa88aa88aa88aa88000000000000000000000000000000000000000000000000ffffcc00ffffcc0000000000000000000000000000000000000000000000000000ff55ff00ff55ff000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0a0000000000000000000000000000000000000000000000000f0fff0fff0fff0ff00000000000000000000000000000000000000000000000000f000f000f000f0
  | 2, 1 => 0xffff00ffffff00000000000000000000000000000000000000000000000000005555ffff5555ffff000000000000000000000000000000000000000000000000ff00ff00ff00ffff000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000fffcfcfcfffcfcfc0000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000ff00ff00ff000000
  | 2, 2 => 0x33000000330000000000000000000000000000000000000000000000000000000033333300333333000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000ff00f000ff00f000000000000000000000000000000000000000000000000000ff00ee00ff00ee00000000000000000000000000000000000000000000000000ff00ff00ee00ee00000000000000000000000000000000000000000000000000aaaaffffaaaaffff000000000000000000000000000000000000000000000000000fffff000fffff
  | 2, 3 => 0xfcccccccfccccccc000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000ffffaaaaaaaaaaaa000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000fcf0fcf0fcf0fcf0000000000000000000000000000000000000000000000000ffffffff1111111100000000000000000000000000000000000000000000000000cccccc00cccccc00000000000000000000000000000000000000000000000000000000fafafafa
  | 2, 4 => 0xffffffffaa00aa00000000000000000000000000000000000000000000000000ffffaaaaffff0000000000000000000000000000000000000000000000000000fe00fe00fe00fe00000000000000000000000000000000000000000000000000ffffff00ffff000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000fafafafaf0f0f0f0000000000000000000000000000000000000000000000000ff008800ff00880000000000000000000000000000000000000000000000000000ff00ff00000000
  | 2, 5 => 0xfafaf0f0fafaf0f000000000000000000000000000000000000000000000000013131313131313130000000000000000000000000000000000000000000000005555555555005500000000000000000000000000000000000000000000000000ff00cc00ff00cc0000000000000000000000000000000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000ff00ffaaff00ffaa000000000000000000000000000000000000000000000000fffafafafffafafa000000000000000000000000000000000000000000000000faaaaaaafaaaaaaa
  | 2, 6 => 0xffccffcc000000000000000000000000000000000000000000000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0000000000000000000000000000000000000000000000000a000a000a000a000000000000000000000000000000000000000000000000000ea00ea00ea00ea00000000000000000000000000000000000000000000000000fffcfffcfffcfffc000000000000000000000000000000000000000000000000ff000000f00000000000000000000000000000000000000000000000000000003333000033330000
  | 2, 7 => 0xaa00aa00aa00aa000000000000000000000000000000000000000000000000ee00aa00ee00aa00000000000000000000000000000000000000000000000000ffffffff00ff00ff000000000000000000000000000000000000000000000000ffffffff00550055000000000000000000000000000000000000000000000000ffffffffffaaffaa000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000003232323232323232
  | 2, 8 => 0xccffccffccffccff000000000000000000000000000000000000000000000000ffff5555ffff5555000000000000000000000000000000000000000000000000ffaa0000ff000000000000000000000000000000000000000000000000000000fffffff0fffffff0000000000000000000000000000000000000000000000000fffffffffcfcfcfc00000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c000000000000000000000000000000000000000000000000eeeeaaaaeeeeaaaa
  | 2, 9 => 0xffffeeeeffffeeee000000000000000000000000000000000000000000000000ccccc0c0ccccc0c0000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000f0f5f0f5f0f5f0f50000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000ffffffffffaaaaaa0000000000000000000000000000000000000000000000000000eeee0000eeee000000000000000000000000000000000000000000000000fff00000ff000000
  | 2, 10 => 0xfafaaaaafafaaaaa0000000000000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000000ff00ff00ffffff0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000cc88cc88cc88cc88000000000000000000000000000000000000000000000000aaaaaaaaaaaaa0a0000000000000000000000000000000000000000000000000fff0f0f0ff000000
  | 2, 11 => 0xccccfcfcccccfcfc0000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a000000000000000000000000000000000000000000000000555555555555ffff000000000000000000000000000000000000000000000000ff00ff00cc00cc00000000000000000000000000000000000000000000000000eecc0000eecc000000000000000000000000000000000000000000000000000000000000cccccccc000000000000000000000000000000000000000000000000ff55ff55ff55ff55000000000000000000000000000000000000000000000000ffff1111ffff1111
  | 2, 12 => 0xfc00fc00fc00fc0000000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000008800000088000000000000000000000000000000000000000000000000000000ffaaff00ffaaff00000000000000000000000000000000000000000000000000ffc0ffc0ffc0ffc0000000000000000000000000000000000000000000000000ffff0000ffaa0000000000000000000000000000000000000000000000000000f0f0f0f0c0c0c0c000000000000000000000000000000000000000000000000000ff00ff00ff0000
  | 2, 13 => 0xfcfcfcfccccccccc000000000000000000000000000000000000000000000000fffffffffff0f0f0000000000000000000000000000000000000000000000000fafafafaaaaaaaaa000000000000000000000000000000000000000000000000fffffffffafafafa000000000000000000000000000000000000000000000000cccccc00cccccc0000000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000aaaaaaaaa0a0a0a0000000000000000000000000000000000000000000000000ffaaffaaff00ff00
  | 2, 14 => 0xff00c000ff00c000000000000000000000000000000000000000000000000000ffcccccccccccccc0000000000000000000000000000000000000000000000000000aaaa0000aaaa000000000000000000000000000000000000000000000000ffff0055ffff0055000000000000000000000000000000000000000000000000ffa0a0a0ffa0a0a00000000000000000000000000000000000000000000000003030303030303030000000000000000000000000000000000000000000000000ffffffffcccc0000000000000000000000000000000000000000000000000000fefefefefefefefe
  | 2, 15 => 0xffaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000ffffffaaffffffaa000000000000000000000000000000000000000000000000ffffffffa0a0a0a0000000000000000000000000000000000000000000000000ffcccccc00000000000000000000000000000000000000000000000000000000ffffffffc0c0c0c0000000000000000000000000000000000000000000000000ffff0000fcfc0000000000000000000000000000000000000000000000000000ffffffffffffff00
  | 3, 0 => 0xfffffafafffffafa000000000000000000000000000000000000000000000000ffffff00ff00ff000000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000faf0faf0faf0faf0000000000000000000000000000000000000000000000000aaaaaaaa88888888000000000000000000000000000000000000000000000000fffff0f0f0f0f0f0000000000000000000000000000000000000000000000000fffff000fffff000000000000000000000000000000000000000000000000000faaafaaafaaafaaa
  | 3, 1 => 0xffccffccff00ff00000000000000000000000000000000000000000000000000ffffaa00ffffaa00000000000000000000000000000000000000000000000000ffaaffaaaaaaaaaa000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000ff88ff88ff88ff88000000000000000000000000000000000000000000000000ffffc0c0ffffc0c00000000000000000000000000000000000000000000000003300330033003300000000000000000000000000000000000000000000000000ccccffffccccffff
  | 3, 2 => 0xffffffff0000ffff000000000000000000000000000000000000000000000000ffffffffffffaaaa000000000000000000000000000000000000000000000000ffff0000f0f00000000000000000000000000000000000000000000000000000fcfcccccfcfccccc000000000000000000000000000000000000000000000000f0f0fffff0f0ffff
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x2c1203305024106070300cc0a0401980802003
  | 4, 0, 0 => 0x1003c061f40282c3c0340a01c1e124080081e0c4050081e1d405014041c4010241e0340d85c1e0c40501c261240d0081e194028081e1840b83c060c40b02c2a0340285026124088401e0e401034060c4
  | 4, 0, 1 => 0x28b05c034050143c084168081e0e4140b05603405014540e4010a4062240501c1e0841405808034028081e274130941e19402808480e4050582a0840501c0c0e405014080e40288c0622405008420e4
  | 4, 0, 2 => 0x502c120e413094640e40505c620c4050081e304028bc06084
  | 5, 0, 0 => 0x280a43098494000a210081e415001000a0f070f54000a028b8443d5000287e3e070f54003c028081e0e500014043b0700d400051183c1c035000280a3a07839400050103c06395000280429070e14000a1003c1c375000146c0f070d540028010ac062250001404060700d400340103c1c335
  | 5, 0, 1 => 0x282c02290394000a14058540e5001440a02079314000a028081e505050140406278398001b0103c1c33500028504e030394004d028081e4c5000081e4b070cd4004a028081e0e5000280a02248e14000a0383c1c125000280a02079214000a028081e47500058284607849400160111406445
  | 5, 0, 2 => 0x28042e110cd4000a028081c5e5000280a25070e1400050103c985d5001700a0207925400260103c1c5b5000280a2c17039400050103cb40e50006c0a02078e54000a028081e59500014040f07161400050100cae38500028ac0207839400052a83c1c3d5000280a54070e14000a028081e535
  | 5, 0, 3 => 0x1a40a36079314000a0280898385000280a02079a1400050103cce035001904c02078654000a3303c1c335000280a54079954000a1400856085001904c02070e1400283183c0657500028c40207839400610103c18605000280a25078654000a0297c1e0e500014040f01911400400103c1c335
  | 5, 0, 4 => 0x280a0f071ad4000a0282c5e4c500014cc0f071814000a0282c260e500028d4020783940005010b844605000280a661d8394003f010f81c60500014c60f0700d400050a008260e500028520f070f5400610103c060c500008aa0f070cd4000a038081e4c500014040f01905400050a0081e0e5
  | 5, 0, 5 => 0x1cc0a020780d4000a390081e0e5000281c381e8cd40005218501e12500028043e070014000a140583c08500014042e01889400710b00876395000fc043e0700d40070028081e0e5000280a02378394000a02808624c5001702c6e079254000a0283c1c6d5001b0040f070cd400050103c06085
  | 5, 0, 6 => 0x280a0240839400050103c1c80500028047f0783140005070e07a60500028fc02078314000a029b8fa0e500014040f3e039400050100c18385001ec0a02078394000a029e81e0e5001e40a020783940078028081e0e5000280a023b839400610d8081e0c500028ec02078394000a0103cea745
  | 5, 0, 7 => 0x28040f062214000a028bc1c08500028a80f070cd4000a0283c1c87500008520f07181400050103c1c865000280a85070e140051028081e0e5000285223078394000a0285c1c385000280a84078394000a02809060e500028040f248cd400280b0b05c035001340a02078394000a0b20846225
  | 5, 0, 8 => 0x280a02070e14000a0285c620e5000081c381998140005010041e0e5000284a0f070cd400050103c068c5000280a2c07931400050103c1c5d500014040f24981400021483c1c03500014040f01a2d4000a02809140e5000280a02170214000a028081c895000141c031c0f5400020780cae335
  | 5, 0, 9 => 0x14040f2ba454000a0288c1e4c5000144c02078654000a028081e65500014a80f0700d400051283c1c605000081c031c0cd40090028081e1950023c0a0207839400050103c92035000280e02078394000a0103c1c8e5000a02c8d078394000a0103c98335000280a0207865400052a03c1c605
  | 5, 0, 10 => 0xd00a02079314000a140581e985000282c0b0a8394140505a5c5e0e600014040f019314000a012581c335001903402078394000a2181c1e125000144a0f0700d4000a02a541e0e50001404940783940093028081e0e500014040d0700d40092480081e65500014040f261814000a02808764c5
  | 5, 0, 11 => 0x2800a0207839400054f8081e0e5001a40a02078654000a028081e9e5000280a024e83940071028081c385000280a13070f54001b028081e4c5000282e0f070cd400022a8a41e0e500028040f072714000a02a6c1e0e5000a02c2f01821400050103922385000280a024d265400020780c18335
  | 5, 0, 12 => 0x1000a02079314000a0103c1c335000287e021f131400a8028081e4c500014040f062454000a0581c1e0e50029c0a0219039400050103c1ca65000142e0f07181400284283c06575000280aa507839400050103c1ca45000280a2c078394000a02809460e5000282c0207a894000a0283c1ca15
  | 5, 0, 13 => 0x5014040f01821800050103c1c605000d00a85078394000a012c07c0e50001404af07839400280b05026125000280a0257039400ad028081e03500014040f072b140005011541e4c5000282e0f070314000a0104c1c335000142e0f0700d400ab0103c1caa5002a40a020783940a0b0103c060c6
  | 5, 0, 14 => 0x29c0ab7070f5400050a03c1c3d500014040f3a80d4000a028081cb65000280a4c1c0f54000a028096a0e500028c217078314000a010241e0e500014040f0700d4001b0285c1e0e5000280ab4078394000a02acc1e0e50001404130718140071590081e395000280a02072c541405058807c0e6
  | 5, 0, 15 => 0x28044c1c0cd4000a0280832385000280a0207b014000a308081e0c500014040f258394000a308081ebf5002f82c02078394000a02af41e0e50005804150780d4000501038705d5000280abc078394000a0283c1cbb500014040f072e94000a028081eb95000081e0e488cd4000a0280844b85
  | 5, 1, 0 => 0x1340a0f070f5400050113070605001904c02079314000a6203c1cc3500014040f018014000a028941e4c5001000a0207839400280b0081e185002a00a020783940a0b013081c036001904c2507839400a7012dc1c335001c40a02078e54000a02809820e5000280a54079314005c0b1b8fa0e5
  | 5, 1, 1 => 0x280a02073314000a02838703d5001000a0207b2d4000a0b1987639500328040f018e54000a028081ec95000280a2307089400021003c060c500028040f07321400050103c1cc75000298c020783940040028081e035000140403260e14000a02894640e5000280a0b0f039400050103c06c55
  | 5, 1, 2 => 0x280a0f07349400050103870605000280a25078394000a058bc1c335000a02c0b0f00d400d1028081e035000280a0206839400050103c06d050033c0a02018e14000a0103c32335001f8040f0183140040028089838500028040e1c0cd4000a028081ece5000081e0e199754000a140081ecd5
  | 5, 1, 3 => 0x28c202060e14001b028081c385000280a024b03940005058bc1c03500014041e0780d400050134c1e0e505014040f0602180005058bc1c605000081e03260cd400050103c3203500014040e018e14000a14058080e5000a02c23018894000a028081e4c5000081e4c19981400050103c32605
  | 5, 1, 4 => 0x81e0e018cd4000a028081ed85001c00a020793140002078386660500015ae020780d400051603c1c6050006c0a0207831400cf0103c06335000280a2f07359400400103c98335003540a02078394000a1603c1c33500014040f48931400050103c060c500350040f0195d400050103c06bf5
  | 5, 1, 5 => 0x2079d406335
  | 6, 0, 0 => 0xa02c430780c24c0014058040f1ca4580011028081e0e01b00014280b03c1cdb60010050050103c1cc00050a00a021708980000028081e031ca80050020780c72da6000280a970103c1cc00050a07e021f039800690b0146c0f073000501601038705d6050140420078f81ce00050a0864e07849800690b0d81e0e6cb00014160103c98336
  | 6, 0, 1 => 0x28500b010ac1cc00053880a02078398000a0b1981e0e1cb0001402170a41e0e6000282c0207839c2c00050a02c02700398000a6f814040f07300014050103870de6003740a020783806c00360280a02078398000005014860f09280014282183c24da60002850053303c1cc00050a1b802079318000a0b01c040f07300014050103d6e4c6
  | 6, 0, 2 => 0x29c8050103caec0005398040f073698000a49058040f32b00014280b3a41e0e600029d0050103c1cc0005009ce0f070cd800e60b0081e0e01b0001402078f81c33600029ca050103c98c0005390040f2bb658000a02808cc0f07300014050103c184c60002850160103d80c00050a19402078398000a010d81e0e19b00014e3028081e0e6
  | 6, 0, 3 => 0xa00a022a83c1cc00050a02c7d070f5800f00b0081e0e303000c8a7028081e0e600028500207839dec00053b82c02078398000a0b014162f07300014280b1501e4c600028500f070f5dac00050580a02079958000a02bb0040f073000d2280b0d81c386000282c0b17839b2c0005014040f073ad8000a0b0081e656cb00014ea0103c1cd96
  | 6, 0, 4 => 0x1f80a020783806c00053d82c02078398501605809840e01b800142872008ae386000282c05010c41cc0005014049a0793180016028081e4c303000143f02809ea0e600014040f22838c0c00053d00af307839800f205014a80f07300014f10b0081e0e600014160207838c0c00388a02c02078e58001601155040f0730002c0207931b2606
  | 6, 0, 5 => 0x1b050050103c1cc00028081e3e07181800f00b0081e0e01b0019e0a028081c386000280a0207838aec0000014040f07245400280103c1c916d300080280b0081e0e6003e814050103c92c00388a02c021d8398000a028081e0e7cb0001405078387ad960002850160119470c00050090429078398000a028081e0e7c3001ee0a028081e0e6
  | 6, 0, 6 => 0x280a0207bfc1cc0005014040f263698000a143f8040f07300014280103c1cfd6000280a0207839a0c00053f00a02078398000a028081e4c7db0002c050103c064c600014040f2283806c000282c040f0700d8000a0103c98da6cb00014f00103c1cda600058040f01931b2c00050141e0e260f58000a2e0141e0e1eb00050160113070606
  | 6, 0, 7 => 0xa02c020780e0ac00001c40a020783940071140081e0e6d300050020799c06da6002ac14050103c1cc00053900a02070e18000a14058161e073001e40a028081e4c6000285005070e07ac00054100a0207839800d105014040f0730001402410ac1e0e60002850020783a06c00050140502078398000a144041e0e80300050160103c06c56
  | 6, 0, 8 => 0x280a020780caec000542c0a02078398000005014044c1c280014280113070da60002850b20103c98c00200a02c020780d8000a0b0081e398530001402078f81c0c6000a02c020193070c00028081e3e0700d8000a84ac8040f1cb001f45c0b03c1c3d6000285108011f41cc000541c0a02078398000a028081c381eb0005016014181c606
  | 6, 0, 9 => 0x280a430103c1cc00050580a0f070f58000a14448040f0730001405010b81e4c60002850161183844c00051080a02078398000002850040f07280050140103c1cda6000282c0f070f5b2c00052482c0f070f5800280b0081f1101b00014160103c1d1060002a1e0207839b4c00054242c0207c398000a14434040f073000150c028081c386
  | 6, 0, 10 => 0x280a020783832c00000280a02830394000a1400a0c0e6d300014d40b0081c386000a02c028303806c00051840a020795d8000a028081e0e19b00050160103c1d186000280a020783a2ec0005014040f074598000a8a814040f07300014288a0081e4c60002851130103c1cc00028081e0e301758000a0103c1c336cb00000a7028096e0e5
  | 6, 0, 11 => 0x280a0207bd498c00050a02c0e1c0f58000a6e809ea0e6cb000500207839da606000280b1c0103c1cc00053d00a02079318000a02c6c040f07300234280b0081e0e6000280a02070e0c0c00050a0042b078398004014058040f65b000140521808260e6000280a020303c1cc00050081e0e19c658000a0103c1c4c19b000145c0103c1c336
  | 6, 0, 12 => 0x280a0207838cac00028081e0e6c9818000a028083c0f073001e4284800a0c0e6000a00a020780caec00050580a2c078398000a14014a80f073001f45c840081e0e6000280a02078e498c0005058580f073658000a028081e0e6b300014050103c1d206000285002070e066c00050163e02078398000a140463c0f073000151d028081e0e6
  | 6, 0, 13 => 0x2850023e839b4c00320a12002078398000a8a858040f07300015090103c1c33600014040f07130c0c00054200a0207839800400b0081e4c6cb0000a0207838c12360002a100207839b2c00140081e0e01bb58000a02c88040f0730001405011501e0e6000280a020700c70c00052400a02079318000a14484040f073000150c0b1141c3d6
  | 6, 0, 14 => 0x19050260103c1cc00678580a020780d8000a14370040f07300014fe0103c98d9600028c2050103870c0093014040f0700d8000a140144a0f07300014050103c1c356000280a020783a1cc0067858040f01b658000a14494040f0730001405130081e4c6001002c050103c98c0005058040f070cd8000a0282c042e0730001524028081e0e6
  | 6, 0, 15 => 0x10050160113070c00050a00a02079318000a144a8040f07300014e5028081e0e60002a52050103c1cc0005014040f07031800280103cf80e6d30001405010941e0e600029a80207838aec0005016500207839800050103c1c036cb00014280b0081e496000280a02078397ec0014014040e1c1818012705014040f07300015260b0081e396
  | 6, 1, 0 => 0x33c50160100c70c0005014040f072e18000a84814043b07300050160103c06576000282c051183c1cc00050a02c02074b98000a1f814040f2630001416010ec1cd960002850160103e5ac00050a25802070e18000a0b08c1e0e6cb0001416012081e4c600014040f0700c98c00050a02c85079318000a0282c04f50730000a0207838c12b6
  | 6, 1, 1 => 0x2a1805078387ac00050a005330783980028028081c031c30002c050103c1c606004240a0207838c0c001438a3c0f0718180016013cc1e031cb0001532028081e0e6000280b310103c1cc000b0081e0e6c9818000a0b014043b073000004d028081e0e5000280a02070e260c0049058040f071818000a0b4bde60f07300014280b1b81e496
  | 6, 1, 2 => 0x4ec14050103c1cc0005138040f073658000a028081e0e9d300014050103c060c600028040f070ce72c00050a02c23070e1800fa2e0081e0e6d300014280b0081d3860002a6e050103c1cc00054325802228398000a0283c1c3d9b300014288f03c1d3560029c14050103870c0005014040f074d1800280b0081e0368300050fc0b0081e036
  | 6, 1, 3 => 0x2850160103c98c0005014040f073698000a84858040f1cb0002c050103c1c036000280a025803c1cc00050081e0e6d36580109028081e0e01b00050e28f03c1c03600058040f0700db2c0067828040f070cd800280b0081c38303000140507838443d6002482c020783806c00050149c02078398013c14058040f073000146102808620e6
  | 6, 1, 4 => 0x280a02a003c1cc00050a02c02099318000a14138040e1c300014280103ccf3f6000d02c050103c1cc000290c2802078398000a02b5c040f0730001428014f81e0e6003c814050103c1cc0000014040f07175400280103c1cda2eb0001405010801e4c6000280a020793082c00051840a020783180064050144a0f0730027a280103c1d206
  | 6, 1, 5 => 0x3c920050103c1cc0014058162f0718180000050081e4c19a80014050103c1cc360000014050103c32a00055100a0207839800280b0081e65303002860a028081e0e60000014050103870a00050a16402078398000a0103c1c3d19b00014050103c1d426000a1c8020795cc0c0014058040e018e18006405014040f2630001405078387b416
  | 6, 1, 6 => 0xa1c8020780caec00a50280a02078398000a0b0081e0ea4b000143f028087c0e60002a90160103c1cc00050140547078398000a14059d80f75b00015460b0081ed06000280a02078383ec0014014040f01831800281a058040e1c3000d20a028081e4c60000014070103c1ca0067814040f07181801450b0081e0e01b000150c0103c1c336
  | 6, 1, 7 => 0x33c0a020783806c00050081e0e199818000a028081e0ea6b000000a0282c5e0e5000285016a603c1cc00000280a02079954000a140081e656d300014610b0081e0c6000a02c0b1783806c0014058040f3280d8000a0103c5e0e19b00080050103c1c4c60006c2c050103c1cc00050081e0e110cd800280b0083c0f01b00014050103c1d4b6
  | 6, 1, 8 => 0x3c850900103ccac000553c0a02078398000a028081f4e0730024e280b0081e036000001405010c41ca00140592a0f0700d8000a028082e0f07300218050103c1c6060002850021583844c00050a2580f070f580000028081e4c30280050e41a0081e57600028040f070cce8c00053982c02079318000a0103cea0e19b0000a02078387a606
  | 6, 1, 9 => 0x28040f0736a72c0005014040f072a9800e41a014040f07300014280b0ec1c3d6000a02c0207a4498c0000014040f01931400050103c5e0e3030001550028081e0e600014040f07088c0c006a058040f07181800400b0081e0e6cb0000a0207838063d600028040f0700c66c0014058040f01831800a7050141e0e1eb00014e60103870da6
  | 6, 1, 10 => 0x28501617839acc00050fc0a02078398000a141381e0e1eb00014280b0081f51600029a80207839b4c00028081e2f0700d8000a028081c571c30000a020783806226003502c020783806c00200a02c02070e18000a14058a9060730001428028081e0e6000a0040f070ccc0c00050141602079318000a7f014040f07300014610103c1c336
  | 6, 1, 11 => 0x1840a0207838c0c0005014040f07559800280b008aa0e1c300014280103c1d5560029c14020783866c0014058280207931800280b0b01e0e30300050900103c1d546000280a020783aa6c00140081e0e018cd8000a14014dc0f07300014280b216a40e6000280a021483c1cc001a3502c02078398000a143f8040e1c3000e2280b0081e4c6
  | 6, 1, 12 => 0xa02c2c0783806c0a0282c040f0700dc000a02809e60e1c30001405218081c386000280b2f0103c1cc00050581c381eb658000aae014040f07300014160156c1e0e6000a00a020780c72c00028081e0e305698000aac814040f26300015580b0081e0e6000282d570103c72c0005014040f33839800a71405804b72630001405620081e0e6
  | 6, 1, 13 => 0x80050103c98a000501416021f03980000050081e0e19a80014160157c1cd9600028e2050103c1cc00050a02c0f07579800a7028081e0e303000c80a028081e0e60002850160103ebac00051842c02078e58000a308081e0e063000c2050103c1c036000280a02070e066c0005014040e1c45d8000005014580f07280014050103c1c416
  | 6, 1, 14 => 0x2ac8050103c1cc0053814040f0700d80028028081e0e48b00050161b03c1c356000280a140103c1cc000033c0a020780d4006448014040f0730001563028081e0e6000280a020783810c00348280a02078398000a140081e4c76b00015620b0081e0e6000a02c021d838c0c0005014056107839800280b08c1e0e30300014280103c1d606
  | 6, 1, 15 => 0x18436050103c1cc00050a02c2e110f58000a028081e0eb33000000a02808760e50002850021d839b4c0014058043b0700d8000005014460f072800504e0103c1c606000a02c230783806c0005014040f075958000a950081e0e6cb00014050103c98996000282c050103c92c0005014042e070898006402898040f07300014fe0103c1d396
  | 6, 2, 0 => 0x3e8b8160103c98c001405804032b8e18000a3f014040f07300050162a83c1c3d6000a2d0020780caec00050a02c020794d80028270081e0e01b000a2280b0081e4c60002850050113070c00053940a02070e18000a028081c0c1c300014280b0081e5060002850160103c90c0005016ce020783980000028081e0e30280014280b10c26126
  | 6, 2, 1 => 0x58040e018e1b2c00050081e0e2b8cd8000a028081e0e44300050160103c985d6000280a43078387ac00140d0040f073698000a0282c040f073000505c0b0081e4960002a12050103c98c00050a1c51e079318000a0b0081e4c6cb00014920b0081e4c6000285016160b81cc0005014040f075a5800160103870d930300000050103c1c035
  | 6, 2, 2 => 0x280a0207dac1cc0014058280209839800e60103c1c036d30001559028081e0e6000282cf30783ad4c0000028c202078314140505a5c040f073801560a0103c1c3360000036050103c1ca0005014040f072318000a028081e0e45b001e40a028081c3860002850160113070c00052c80a0207839800e60103c1cda3030001402070e1b4d96
  | 6, 2, 3 => 0x80050103c1ca001405886140784980000050fc043e072802dc0a028081e0e6000280a0207838bac00050141eb7070f58000a02db4040f07300050fe0103c1c6060033c14050103c98c00b60280a0207839800280b0081e0304300014027983c1c3360002886020783866c00050a02c0b17931800050103c1c573030005016010b844606
  | 6, 2, 4 => 0xa00a0207838bac0005014040f071318000a028081e2226300014050103c260e6000280a020783a46c00050144c02070e18017105014040f0730000a02078386660600028502b1183c1cc00054980a02078398000a02dc0040f0730000a430103c1c606000280a02079307ac00050a0040f073b58000a02dbc040f0730000a020783806576
  | 6, 2, 5 => 0xa02c0e018e07ac00050a02c2f070218000a028081e0e95b000143f028081c386000a02c02078390cc00055cc0a02078398000a14014040f0cb000a2280b0081e0e600029ca020783866c00050081e0e060cd800050103c1c0319b00014050103c986060001486020783806c00140581c381e9818000a028081e0eb9300014050103c5e4c6
  | 6, 2, 6 => 0x3940a0207838c0c00028081e0e061818000a30814040f2630000b220103c1c036000a02c020780d18c00050a02c2c07931800280b0081e0e2eb00050160103c068b60002850e44283caec009e8280a02078398000a84814040f07300014160103c1cd96000285016010b810c00052482c02078398000a028081e03263000000a02838703d5
  | 6, 2, 7 => 0x81e0e6d364c0c0a0282c040f07031c000a028081e0e9cb000000a0103870335003940a020783806c00320280a0207865800050103c1c03063000c80a028081c38600058040f018e5b2c0079028040f070cd8000a02808400e1c300014280b0081e196000280a0207838b6c00055d02c02078398000a028081e4c65b00014050103c1cde6
  | 6, 2, 8 => 0xa02c020780c98c00200280a0207931800020783806da6cb0000005010387060500000c8260103c1ca00055e42c02078398017805014040f073000000a028941e0e50002851770103c1cc0079014040f071818000a6a0590a0f0730001576028081e0e60002822050103870c0014058040f26181800cf05014040f07300014050103c1d756
  | 6, 2, 9 => 0x28c2050103c1cc00055f40a02078398017c05014040f073000157b028081e0e6000287e020783866c00bd0280a02078398000a028081e0e3a300014050103cea0e6000280a0b0103870c00050081e0e19aa9800710b014040f07300014260103c1c336000a02c020724470c0000014040e018e1400f2028081e0e01b000000a028081e4c5
  | 6, 2, 10 => 0x40f070ccc0a00200280a02078398000a028081e4c19b000c8050103c1c6060002afe050103c1cc00051080a0207931814280b0081e03043800141b028081e0e60002afc050103c1cc0032028040f070cd8004014058040f2630007e050103c1c606000280a020783ab4c0005014040f0732d800a814058040f26300000050103c060c5
  | 6, 2, 11 => 0xa058081e0e19b00014280b00844b8600000040f0700c66a0032014040f0700d8000a1405898381eb000000a028081e0e5
  | 7, 0, 0 => 0x29baf00b0081e0e70002851590b0081e0e700028501601038714270002b02280b0081e0e70000014e2028081e0e60002850e20103c1cda70002850168a0081e0e7003e81416028081e0e7000a1c4160103c1c037000285016c00081e0e70002850160103c1c8c7003e814160103c1cd97000282c05010b81e0e70002850160103c1c8b7003c814280b0081c387000282c021703c1cd97
  | 7, 0, 1 => 0x282c050103c1c39700028501607adc1c3d7000285016b68081e0e7000282c020783872d97003c814280b0081e6570033c14280b0081e4c7005b014280b0081e0e70002850160103c1c4970002850050103c1cd970002b04280b0081e0e7000282c050103dea0e7000285016010b81c38700029e816028081e0e7000a02c0207838ae607000282c0207bd41cd970000014e60103c1cda6
  | 7, 0, 2 => 0x28501601038723870002850160103c983d7000285016b78081e0e70002850e40b0081e4c70000014280b1981e0e60000014050103c1c576000a02c0207838065770000080280b0081e0e600029ca280b03c1c3d70000014280b0085c22600029e8280b0081c38700028500207839b4f97000282c900103c1cd970002850050103c1c4c700028505c028081e0e70002850160103c1c5d7
  | 7, 0, 3 => 0x5c414280b0081e0e70002850160103c1cd97000005016011541e0e60002850920b0081e0e70002a4c280b0081e0e7000285016480081c387000a02c027983c1c60700029fc160103c1cd97000285016014781c387000285016b80081e0e7000a02c430103c1c6070002850160103c1d8370002a18280b0081e4c7003e8505c0b0081e0e70000014287f0081e0e6000282c05130081e0e7
  | 7, 0, 4 => 0xa02c430103c1c037000001416078387ad96000287e16028081e0e7000285043270081e0e70002850160103c5e4c70002850160103c1d5470002850160103c1c4c70002850160103c444c7000a02c0207838246070002a12160103c1c3970002850160103c1d237000285016028081e0e70000014f40b3cc1e0e60002a1228028081e0e70002850160103c1d857000285016c20081e0e7
  | 7, 0, 5 => 0x2850160103c1d8970000014050103c1c1260002850020783824da7000001428010ac1e0e6000a02c02078380612700028500207bd41c5770000014050103c1c336000282c02c403c1cd970002b0e280b0081e0e7000001405013cc1e0e6000001405218081e0e60000014160283c1c3d6000285016078387ada7000a02c027983c1c0370002850160103c986070002b0c280b0081e0e7
  | 7, 0, 6 => 0x29e8280b03c1c3d70002850160103c98cb7001901416028081e0e70002850160103c1cde70039450160103c1c6070033c1428028081e0e7000a02d220103c1c037000282c05010801e0e70002850161703c1c3d7004f414280b0081e0e70002a12280b0081e0e700028500207839b52070002a18280b0088a0e70002850160103c064c70002b14280b0081e0e70000014280b038703d6
  | 7, 0, 7 => 0x1428028081e4c60000014e5028081e0e600029ca280103c1cda70000014050103c1c0c60039450160103c1c0370002850050103c1c3d70002850e40b2141e0e70000014280b0081e4960002850e4028081e0e7001a41416028081e0e70000014050103d6e0e600028500207adc1cda700028518b0b0081e0e7001a414160103c1cd970000014160103c1c3360000015150b0081e0e6
  | 7, 0, 8 => 0x2850d40b0081e0e7000002c050103c1c606000a02c0207839b46070033c14280b0081e0e700028518d0b0081e0e7000285016c60081e0e7003e81428840081e0e70002850160103c1d757000002c0207839b26060000050160103c06576001a414280b0081c3870002850160103c1d3970000014280b1501e0e60002a1828028081e0e70029c14280b0081e4c700029ba160103c1cd97
  | 7, 0, 9 => 0x15090b0081e396000002c050103c1c036000a02c020783806da700000140207839b4d960002850161708c1e0e70010014280b0081e4c7000002c020783806d960000050160103870606002b414280b0081e0e7005e014280b0081e0e70002850160103c1d6a70002850050103c1c607003c850160103c1c6070002b1c280b0081e0e70002850050103c5e0e70002850050103c1c227
  | 7, 0, 10 => 0x3d050160103c1c60700000000a028081c385000001428590081e0e60000050160103806386000285016078387b5670002a8c280b0081e4c7000282c050103c8a0e70002850050103c1c037000282c05058081e0e700001e40a028081e0e6000282c02079141cd97003c850160103c1c037000282c0b0103c1cd970002a18280b0081e0e70000014280b0081e4c60000014050103c1cda6
  | 7, 0, 11 => 0x2850162183c1c1270002850020783872da7001a414280b03c1c3d7005f014280b0081e0e7000285016760081e4c70002850160103c98eb7000285016c88081e0e7005e814280b0081e0e7000285016c80081e0e700028518f0b0081e0e7003e814280103c1cda7000285016160081e0e7000285016058081c387000282c05010d81e0e7000285061028081e0e700424e2280b0081e0e7
  | 7, 0, 12 => 0x2850160103c1cc57000285016230081e0e700028b816028081e0e7000282c020783898d9700000143f028081e0e6000282c050103c1cd970029c14280b0081e0e7000001428028081e0e60002850160103c98d070002851920b0081e0e70002850160103cae4c7000001405130081e0e6000001490028081e0e60002850900103c1cda70002850610b0081e0e70002afa280b0081e0e7
  | 7, 0, 13 => 0x14280b008260e6000001405010801e0e60064c14280b0081e0e70002a12160103c1cd97001a450160103c1c6070000014280b0081e0e60002850160103e220e700028501601038717270010014280b0081e0e70002850160103898387000a02c02171541e0e70002850160103c1d0570002850020799c1cda7000285016028081c387000285016013cc1e4c7000285016218081e4c7
  | 7, 0, 14 => 0x3c814280b1501e0e7000a02c0b0103c1c6070033c14160103c1cd97000282c0207839b3757000285016760081e0e70000000050103c1c6050002850e40b0081e577000282c0207839b339700029ca280b0081e4c70002850160103870de70002850160103d6e4c700000d20a028081e0e60002a12280b0081c387001a450160103c1c03700000000a0103c1c33500000c80a028081e0e6
  | 7, 0, 15 => 0xe2280b0081e0e6003c814280b0081e4c70002850160103c98da70002850160103c1cd07000001405058081e0e60002850fc0b0081e0e7000a02c0b0103c1c0370000014160103c98d960002850050103c1c337000282c02078387ad970033c14280b0081c3870002850160103c1c5770000050160103c1c91600029c8160103c1cd970000000050103c1c035003dc14280b0081e0e7
  | 7, 1, 0 => 0x285016480081e4c7000285016010781e0e70002850160103c1cd6700029ca28028081e0e70002850050103c1c0c7000282c020783806d9700028501601038706070002850160103c1c337000a02c0207838c05d7000014e280b0096e0e6000285016218081e0e7000282c0207839b26070002850160103c065770000014280b00898386000282c02078bc1cd9700028501601038703d7
  | 7, 1, 1 => 0xa02c0207838064c700028501605809ea0e700029ca280b0081e0e70002850160103c1c0c7000a02c050103c1c03700029c8d40b0081e0e700028500207839b4d970049850160103c1c0370002850160103c1c357000285016058085c0e7000a02c0207838986070000014280103c1ced6000a02c0207838c1237000285016910081e0e7000a02c050103c1c6070002850160103806387
  | 7, 1, 2 => 0x14280b0081c3860002850050103c1c397003c814280b0081e0e70000050160103c1c5d6000001509028081e0e60000014160103c1cd960042450160103c1c0370000014920b0081e0e600028501607838443d7003e81428028081e0e700001f45c0b0081e0e60042450160103c1c6070002851320b0081e0e7050a02c05058081e0e80065014160103c1cd970000014050103c1c4c6
  | 7, 1, 3 => 0xa028081e4c50000050160103c064c60000014050103c1c3d6000a02c02078bc1c607000a02c0207838063d70000050160103c98606000019e0a028081e0e6000a02c02078387a6070033c50160103c1c0370000014280b02c5e0e60002850fe0103c1cd970010050160103c1c4c70002850160103c1d4b70033c50160103c1c6070002a88280b0081e0e70050c14280b0081e0e7
  | 7, 1, 4 => 0x19e280b0081e0360002850160103c1c0870000080280b0081e4c60019014280b0081e0e7000001461028081e0e60000014280b0b01e0e6050a02c0b0103c1c0380000014050103c1c036000a02c0207838c15a70002850160103c1d5370000014050103c1c60600028503f0b0081e0e70000014050103c5e0e6000a02c02078bc1c037000285016058081e4c70002850fe0b0081e0e7
  | 7, 1, 5 => 0x285016058081e0e700000000a028081e0e50000050160103c1c0360000050160103c1c606000285016028081e4c7
  | 8, 0, 0 => 0x2850160103c1cca7050a02c0207839c000a14014040f07302850160103c1c037050a02c0207838c0e0a14058040f17839c14280b0081e0e11382a18280b0081e0e70002850160103c98c0a14058040f070f5d9e0a14058040f07382a12280b0081e0e7050a02c020783898e0a141702c0207839c14280b014040f07382850160103c1cd97
  | 8, 0, 1 => 0x50a02c0b0103c1ce00000280a0207839400280b0081e0e01b00050160103c1c6060002850160103870cf2050a02c0207839c000a0b0081e0e6cb029ca280b0081e0e7050a02c0207adc1ce0a1405804f307839c14280b10c040f07382850160103c1c577
  | 9, 0, 0 => 0x14280b0081e0e6
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
  | 0, 0 => 0xc00000ce00000000000000000000000000000000000000000000000000000000368d1431ffff0000000000000000000000000000000000000000000000000000f80000fe00000000000000000000000000000000000000000000000000000000060c1001ffff00000000000000000000000000000000000000000000000000000070e30000000000000000000000000000000000000000000000000000000000c70e18c1f3e600000000000000000000000000000000000000000000000000003070e330000000000000000000000000000000000000000000000000000000000000000f8f1d
  | 0, 1 => 0x368d1431cf9d00000000000000000000000000000000000000000000000000000070e30fbf7f000000000000000000000000000000000000000000000000000030000030000000000000000000000000000000000000000000000000000000000000000e00000000000000000000000000000000000000000000000000000000f78f1cf1ffff0000000000000000000000000000000000000000000000000000ffffff00000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001bf7f
  | 0, 2 => 0xc00000c1b3660000000000000000000000000000000000000000000000000000f80fe0fe03f800000000000000000000000000000000000000000000000000000670000ffc000000000000000000000000000000000000000000000000000000c77efb0000000000000000000000000000000000000000000000000000000000060c1001cf9d000000000000000000000000000000000000000000000000000000000001b3660000000000000000000000000000000000000000000000000000ff0e18fff3e60000000000000000000000000000000000000000000000000000c070e3c00000
  | 0, 3 => 0xfb3660000000000000000000000000000000000000000000000000000067cf30fffff0000000000000000000000000000000000000000000000000000f870e3f1bf7f0000000000000000000000000000000000000000000000000000c90208c18f1d0000000000000000000000000000000000000000000000000000f870e30000000000000000000000000000000000000000000000000000000000f8000030000000000000000000000000000000000000000000000000000000000070e30e000000000000000000000000000000000000000000000000000000000070e3f04080
  | 0, 4 => 0x70e30000000000000000000000000000000000000000000000000000000000f800000000000000000000000000000000000000000000000000000000000000c70e18c000000000000000000000000000000000000000000000000000000000368d14ce30620000000000000000000000000000000000000000000000000000060c1001f3e60000000000000000000000000000000000000000000000000000000000018f1d00000000000000000000000000000000000000000000000000003172eb3030620000000000000000000000000000000000000000000000000000c00000c00000
  | 0, 5 => 0x60c1001c384000000000000000000000000000000000000000000000000000036fdf73fffff0000000000000000000000000000000000000000000000000000f8000001ffff0000000000000000000000000000000000000000000000000000c70e18c1ffff0000000000000000000000000000000000000000000000000000300de03e03f800000000000000000000000000000000000000000000000000000e7cf30fc38400000000000000000000000000000000000000000000000000003000003e00000000000000000000000000000000000000000000000000000000fff000fffc00
  | 0, 6 => 0xf1e7000c190000000000000000000000000000000000000000000000000000c70e1800000000000000000000000000000000000000000000000000000000000000003e0c190000000000000000000000000000000000000000000000000000f87fe3000000000000000000000000000000000000000000000000000000000007ffff01ffff0000000000000000000000000000000000000000000000000000368d143000000000000000000000000000000000000000000000000000000000300000318f1d0000000000000000000000000000000000000000000000000000078f1c0e4080
  | 0, 7 => 0xfe8d14ffcf9d0000000000000000000000000000000000000000000000000000300000300000000000000000000000000000000000000000000000000000000038f1e73e0c190000000000000000000000000000000000000000000000000000ffffe3000000000000000000000000000000000000000000000000000000000036800031cf1d0000000000000000000000000000000000000000000000000000c70e1801f3e600000000000000000000000000000000000000000000000000000070000fbc000000000000000000000000000000000000000000000000000000c972ebce3062
  | 0, 8 => 0x70e30fbf1d0000000000000000000000000000000000000000000000000000c77000cffc00000000000000000000000000000000000000000000000000000036800031cc0000000000000000000000000000000000000000000000000000000070000fbf1d0000000000000000000000000000000000000000000000000000c77efbcfffff0000000000000000000000000000000000000000000000000000ff8f1cfe40800000000000000000000000000000000000000000000000000000f80000f000000000000000000000000000000000000000000000000000000000fffffff04080
  | 0, 9 => 0x3000003000000000000000000000000000000000000000000000000000000000c00ee0ce03f80000000000000000000000000000000000000000000000000000ffffff3000000000000000000000000000000000000000000000000000000000ff8f1cf04080000000000000000000000000000000000000000000000000000007ffff0000000000000000000000000000000000000000000000000000000000ffffff00000000000000000000000000000000000000000000000000000000000070e30fbc0000000000000000000000000000000000000000000000000000000070e30fbf78
  | 0, 10 => 0xe00e03780000000000000000000000000000000000000000000000000000f80000f00000000000000000000000000000000000000000000000000000000036fdf70000000000000000000000000000000000000000000000000000000000c70e18c003e000000000000000000000000000000000000000000000000000000070e30fbfff00000000000000000000000000000000000000000000000000003682eb31cc620000000000000000000000000000000000000000000000000000fffffff0400000000000000000000000000000000000000000000000000000000070e301bf7f
  | 0, 11 => 0xc70f1cc1f3ff0000000000000000000000000000000000000000000000000000c872e3ce306200000000000000000000000000000000000000000000000000000000000fbf7f0000000000000000000000000000000000000000000000000000fff000000000000000000000000000000000000000000000000000000000000000000001ffff0000000000000000000000000000000000000000000000000000300000ffffff0000000000000000000000000000000000000000000000000000ff8f1cf0000000000000000000000000000000000000000000000000000000000000003fffff
  | 0, 12 => 0x7f0ff0fff7f0000000000000000000000000000000000000000000000000000c70000c1f36600000000000000000000000000000000000000000000000000000070e30e03780000000000000000000000000000000000000000000000000000fffffffe00000000000000000000000000000000000000000000000000000000c00e00c003e00000000000000000000000000000000000000000000000000000f800003e00000000000000000000000000000000000000000000000000000000f870e3ffbf7f0000000000000000000000000000000000000000000000000000000000ffffff
  | 0, 13 => 0x18f1d0000000000000000000000000000000000000000000000000000c70e18c1f000000000000000000000000000000000000000000000000000000038f1e73e00000000000000000000000000000000000000000000000000000000ffffffc00000000000000000000000000000000000000000000000000000000038f1e73ffc1f0000000000000000000000000000000000000000000000000000f8001ffe00070000000000000000000000000000000000000000000000000000ffffffc1f3e600000000000000000000000000000000000000000000000000000000000fbf7f
  | 0, 14 => 0x368d1431cfff0000000000000000000000000000000000000000000000000000f88104fe0000000000000000000000000000000000000000000000000000000007ffff0fffff00000000000000000000000000000000000000000000000000000070e301bf7f0000000000000000000000000000000000000000000000000000f80fe00e03780000000000000000000000000000000000000000000000000000f90000fe00000000000000000000000000000000000000000000000000000000fff0e30000000000000000000000000000000000000000000000000000000000fffffff00000
  | 0, 15 => 0x3070e33fbf7f0000000000000000000000000000000000000000000000000000f870e3fe00000000000000000000000000000000000000000000000000000000368d1431cc00000000000000000000000000000000000000000000000000000007f0ff0000000000000000000000000000000000000000000000000000000000ffffff0040800000000000000000000000000000000000000000000000000000c70e18c1ffff0000000000000000000000000000000000000000000000000000ffffff0000800000000000000000000000000000000000000000000000000000ffff1c000000
  | 1, 0 => 0x38f1e73e00000000000000000000000000000000000000000000000000000000000000ffff7f0000000000000000000000000000000000000000000000000000c00e00c1b3e60000000000000000000000000000000000000000000000000000c70c10c1f3e60000000000000000000000000000000000000000000000000000368d1431c39c000000000000000000000000000000000000000000000000000036f0003ffc000000000000000000000000000000000000000000000000000000c972ebcfb3660000000000000000000000000000000000000000000000000000000000ffbf7f
  | 1, 1 => 0xff8f1c000000000000000000000000000000000000000000000000000000000006fdf701ffff0000000000000000000000000000000000000000000000000000c70e183e0c1900000000000000000000000000000000000000000000000000000070e00fbf780000000000000000000000000000000000000000000000000000000000f040800000000000000000000000000000000000000000000000000000368d1431ff9d0000000000000000000000000000000000000000000000000000c97fffce30e20000000000000000000000000000000000000000000000000000078f1c004080
  | 1, 2 => 0xf00000f000000000000000000000000000000000000000000000000000000000378f1c31ffff0000000000000000000000000000000000000000000000000000c70000c1f000000000000000000000000000000000000000000000000000000036f0e30000000000000000000000000000000000000000000000000000000000ffffff3000000000000000000000000000000000000000000000000000000000fff000fe00000000000000000000000000000000000000000000000000000000ff8f1cffffff0000000000000000000000000000000000000000000000000000f80fe0000000
  | 1, 3 => 0xf7ffff0000000000000000000000000000000000000000000000000000000000ff8f1cf1fc870000000000000000000000000000000000000000000000000000368f1c31cf9d00000000000000000000000000000000000000000000000000003fffff31ffff0000000000000000000000000000000000000000000000000000c70e18c1f3660000000000000000000000000000000000000000000000000000ff8f1cf1cf9d0000000000000000000000000000000000000000000000000000368d14304080000000000000000000000000000000000000000000000000000038810431b366
  | 1, 4 => 0xffffff31cf9d0000000000000000000000000000000000000000000000000000078f1cffffff0000000000000000000000000000000000000000000000000000c70e18c1b36600000000000000000000000000000000000000000000000000000070e30000000000000000000000000000000000000000000000000000000000378f1c31cf9d0000000000000000000000000000000000000000000000000000007f1c0fbc80000000000000000000000000000000000000000000000000000038f1e73e00180000000000000000000000000000000000000000000000000000ff7efb000000
  | 1, 5 => 0x67cf3000000000000000000000000000000000000000000000000000000000006000001cf1d0000000000000000000000000000000000000000000000000000ffffff0fbc000000000000000000000000000000000000000000000000000000388104ffffff0000000000000000000000000000000000000000000000000000ffffff01ffff000000000000000000000000000000000000000000000000000007ffff0000000000000000000000000000000000000000000000000000000000fffdf70000000000000000000000000000000000000000000000000000000000ffffff304080
  | 1, 6 => 0x368d140000000000000000000000000000000000000000000000000000000000cfffffce70e20000000000000000000000000000000000000000000000000000368d1431cf980000000000000000000000000000000000000000000000000000c70e18c1f3e60000000000000000000000000000000000000000000000000000cf0e18c1f3e60000000000000000000000000000000000000000000000000000f800e0fe03780000000000000000000000000000000000000000000000000000f9f3effe30620000000000000000000000000000000000000000000000000000368d143fcf9d
  | 1, 7 => 0xfffffff1ffff0000000000000000000000000000000000000000000000000000fff0000003ff0000000000000000000000000000000000000000000000000000c70e18c1c3840000000000000000000000000000000000000000000000000000c60c10c1f3e6000000000000000000000000000000000000000000000000000030f1e73e0c1900000000000000000000000000000000000000000000000000000000003fffff0000000000000000000000000000000000000000000000000000ff8f1cf040000000000000000000000000000000000000000000000000000000c90208c00000
  | 1, 8 => 0xf1cffffff0000000000000000000000000000000000000000000000000000f00000fe00000000000000000000000000000000000000000000000000000000ffff1ff1fc870000000000000000000000000000000000000000000000000000c7ffffc1ffff0000000000000000000000000000000000000000000000000000070e1801f3e6000000000000000000000000000000000000000000000000000036fdf731cf9d0000000000000000000000000000000000000000000000000000368d0031cf9d00000000000000000000000000000000000000000000000000000000e00fbf7f
  | 1, 9 => 0xffffff0fbf7f00000000000000000000000000000000000000000000000000000070e30fb3660000000000000000000000000000000000000000000000000000f87f03f1bc870000000000000000000000000000000000000000000000000000c870e3ce30620000000000000000000000000000000000000000000000000000ff8f1c0000000000000000000000000000000000000000000000000000000000f800e0fe00000000000000000000000000000000000000000000000000000000ff8f1cf1ffff000000000000000000000000000000000000000000000000000007ffe001fff8
  | 1, 10 => 0xf800000e000000000000000000000000000000000000000000000000000000000870e30e00000000000000000000000000000000000000000000000000000000fffffff000000000000000000000000000000000000000000000000000000000f87000ffbc0000000000000000000000000000000000000000000000000000003070e3000000000000000000000000000000000000000000000000000000000038f1e73fffff0000000000000000000000000000000000000000000000000000ffffff0e00000000000000000000000000000000000000000000000000000000ff8000f04000
  | 1, 11 => 0xf80fe0ffb3fe00000000000000000000000000000000000000000000000000000070e30e30620000000000000000000000000000000000000000000000000000fe8ff4ffcffd0000000000000000000000000000000000000000000000000000f80f00fe0080000000000000000000000000000000000000000000000000000038f1e73e0c00000000000000000000000000000000000000000000000000000007f01f01fc070000000000000000000000000000000000000000000000000000000fff0003ff00000000000000000000000000000000000000000000000000000070e30fffff
  | 1, 12 => 0x37ffff31ffff0000000000000000000000000000000000000000000000000000fff01ffffc070000000000000000000000000000000000000000000000000000ffffe0fffff80000000000000000000000000000000000000000000000000000f87fe3ffbfff0000000000000000000000000000000000000000000000000000fe0c10ffc3840000000000000000000000000000000000000000000000000000ff0ff8fff3fe0000000000000000000000000000000000000000000000000000000ff40003fd00000000000000000000000000000000000000000000000000003e8d1431cf9d
  | 1, 13 => 0x7f00301fc070000000000000000000000000000000000000000000000000000fff000ffcc00000000000000000000000000000000000000000000000000000007f00001fc000000000000000000000000000000000000000000000000000000ff8f1cf1f3e60000000000000000000000000000000000000000000000000000c70e18c040800000000000000000000000000000000000000000000000000000f80ff8fe03fe0000000000000000000000000000000000000000000000000000c70e18c1f3ff0000000000000000000000000000000000000000000000000000ff0ff8c1f3e6
  | 1, 14 => 0xffffffffff9d0000000000000000000000000000000000000000000000000000ff8000fffc000000000000000000000000000000000000000000000000000000300d003003980000000000000000000000000000000000000000000000000000fffe18ffffe60000000000000000000000000000000000000000000000000000c70000c1f0000000000000000000000000000000000000000000000000000000fffffffe03f80000000000000000000000000000000000000000000000000000fff007fffc010000000000000000000000000000000000000000000000000000fe8000ffcc00
  | 1, 15 => 0x360c1031c3840000000000000000000000000000000000000000000000000000f80ffffe03ff00000000000000000000000000000000000000000000000000003ff11f31fc070000000000000000000000000000000000000000000000000000fff0000fbc000000000000000000000000000000000000000000000000000000f80f00f000800000000000000000000000000000000000000000000000000000fffffffffc00000000000000000000000000000000000000000000000000000006801401cc0500000000000000000000000000000000000000000000000000000070000fbf66
  | 2, 0 => 0xff0ff8fe03f80000000000000000000000000000000000000000000000000000368d1430039800000000000000000000000000000000000000000000000000000000e00f8f7d0000000000000000000000000000000000000000000000000000fffd00ffff98000000000000000000000000000000000000000000000000000007ff1f01fc870000000000000000000000000000000000000000000000000000c70e1801b3660000000000000000000000000000000000000000000000000000c7fe1fc1ffe7000000000000000000000000000000000000000000000000000007001801f006
  | 2, 1 => 0xfff01ffffc000000000000000000000000000000000000000000000000000000ff8ffff043ff0000000000000000000000000000000000000000000000000000f80fe0fe03ff0000000000000000000000000000000000000000000000000000fffd14ffff9d0000000000000000000000000000000000000000000000000000ff8f1cffffff0000000000000000000000000000000000000000000000000000000f1c0000800000000000000000000000000000000000000000000000000000fff0e3ffff7f0000000000000000000000000000000000000000000000000000f80fe0fe0000
  | 2, 2 => 0xc80000ce000000000000000000000000000000000000000000000000000000000172eb0030620000000000000000000000000000000000000000000000000000ff0000fff0000000000000000000000000000000000000000000000000000000f80e00fe03e00000000000000000000000000000000000000000000000000000f80de0fe03f80000000000000000000000000000000000000000000000000000f80fe03e03f80000000000000000000000000000000000000000000000000000007fff0fbfff000000000000000000000000000000000000000000000000000000ffff000fff
  | 2, 3 => 0xf68d14f1cf9d0000000000000000000000000000000000000000000000000000c00e00c003e00000000000000000000000000000000000000000000000000000fff0e30fbf7f0000000000000000000000000000000000000000000000000000f78f1c0000000000000000000000000000000000000000000000000000000000f70f18f1f3fe0000000000000000000000000000000000000000000000000000ffffffc000000000000000000000000000000000000000000000000000000000068d1401cf9d0000000000000000000000000000000000000000000000000000000000cfffff
  | 2, 4 => 0xffffff0e03780000000000000000000000000000000000000000000000000000fff0e3fffc000000000000000000000000000000000000000000000000000000f00fe0fe03f80000000000000000000000000000000000000000000000000000ffffe0fffc000000000000000000000000000000000000000000000000000000000000fffc000000000000000000000000000000000000000000000000000000c77efbc1f3e60000000000000000000000000000000000000000000000000000f80000fe0318000000000000000000000000000000000000000000000000000007f01f000000
  | 2, 5 => 0xc77e18cfffe60000000000000000000000000000000000000000000000000000c972ebce00000000000000000000000000000000000000000000000000000000ff8f1cf000800000000000000000000000000000000000000000000000000000f80d00fe03980000000000000000000000000000000000000000000000000000000000fe00000000000000000000000000000000000000000000000000000000f80fe3fe03ff0000000000000000000000000000000000000000000000000000ff7efbffffff0000000000000000000000000000000000000000000000000000c070e3cfbf7f
  | 2, 6 => 0xfe8ff4000000000000000000000000000000000000000000000000000000000038f1e700000000000000000000000000000000000000000000000000000000000000e00fb37e00000000000000000000000000000000000000000000000000000000000003600000000000000000000000000000000000000000000000000000000ce00e03f80000000000000000000000000000000000000000000000000000ff8ffcffffff0000000000000000000000000000000000000000000000000000f80000c000000000000000000000000000000000000000000000000000000000c97000ce3000
  | 2, 7 => 0x700301bc0700000000000000000000000000000000000000000000000000003000e03e03780000000000000000000000000000000000000000000000000000ffffff01fc070000000000000000000000000000000000000000000000000000ffffff0040000000000000000000000000000000000000000000000000000000ffffffffbfff00000000000000000000000000000000000000000000000000000000000003ff0000000000000000000000000000000000000000000000000000000fe00003f80000000000000000000000000000000000000000000000000000c172ebce3062
  | 2, 8 => 0x37fd1f31ff9f0000000000000000000000000000000000000000000000000000ffff1cfffc800000000000000000000000000000000000000000000000000000f87000fe00000000000000000000000000000000000000000000000000000000fffff8fffffe0000000000000000000000000000000000000000000000000000fffffff1ffff0000000000000000000000000000000000000000000000000000c972eb0000000000000000000000000000000000000000000000000000000000308104300c19000000000000000000000000000000000000000000000000000036f0e33fff7f
  | 2, 9 => 0xfffdf7ffffff0000000000000000000000000000000000000000000000000000368c1031cf8400000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000c78e1cc1f3e6000000000000000000000000000000000000000000000000000007801c0040000000000000000000000000000000000000000000000000000000ffffffffbf7f0000000000000000000000000000000000000000000000000000000df70003ff0000000000000000000000000000000000000000000000000000ff0000fe0000
  | 2, 10 => 0xc770e3cfff7f00000000000000000000000000000000000000000000000000003801e03e0018000000000000000000000000000000000000000000000000000007f01f01ffff000000000000000000000000000000000000000000000000000000000001fc07000000000000000000000000000000000000000000000000000000001f0000070000000000000000000000000000000000000000000000000000300d00318f9d00000000000000000000000000000000000000000000000000000070e30fbf660000000000000000000000000000000000000000000000000000ff0e18fe0000
  | 2, 11 => 0x368f1c31cfff000000000000000000000000000000000000000000000000000038f0e33e0c190000000000000000000000000000000000000000000000000000ff8f1cf043ff0000000000000000000000000000000000000000000000000000f80fe030039800000000000000000000000000000000000000000000000000003680003fcc00000000000000000000000000000000000000000000000000000000000031cf9d0000000000000000000000000000000000000000000000000000ff8ffcfe43f80000000000000000000000000000000000000000000000000000fff208fffc00
  | 2, 12 => 0xf00f00f003f8000000000000000000000000000000000000000000000000000001700b00300200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f87fe0ffbff80000000000000000000000000000000000000000000000000000fe0ff0ffc3fc0000000000000000000000000000000000000000000000000000fff000ffbc000000000000000000000000000000000000000000000000000000c70e1801c384000000000000000000000000000000000000000000000000000007f01f01fc00
  | 2, 13 => 0xf78f1c31cf9d0000000000000000000000000000000000000000000000000000fffffffff3e60000000000000000000000000000000000000000000000000000c77efb0fbf7f0000000000000000000000000000000000000000000000000000ffffffcfffff0000000000000000000000000000000000000000000000000000368d0031cf9800000000000000000000000000000000000000000000000000000001e700001900000000000000000000000000000000000000000000000000000070e301b3660000000000000000000000000000000000000000000000000000f87fe3fe03f8
  | 2, 14 => 0xf80c00fe03800000000000000000000000000000000000000000000000000000fe8d1431cf9d00000000000000000000000000000000000000000000000000000000e300037f0000000000000000000000000000000000000000000000000000fff01cfffc000000000000000000000000000000000000000000000000000000f80000ffb3660000000000000000000000000000000000000000000000000000c10208c030620000000000000000000000000000000000000000000000000000ffffff31cc000000000000000000000000000000000000000000000000000000f7ffffffffff
  | 2, 15 => 0xf870e30fbf7f0000000000000000000000000000000000000000000000000000ffffe00000000000000000000000000000000000000000000000000000000000ffffe3ffffff0000000000000000000000000000000000000000000000000000ffffff01b3660000000000000000000000000000000000000000000000000000fe8d140000000000000000000000000000000000000000000000000000000000ffffff01c3840000000000000000000000000000000000000000000000000000fff000f1fc000000000000000000000000000000000000000000000000000000fffffffffff8
  | 3, 0 => 0xfffefbffffff0000000000000000000000000000000000000000000000000000ffffe0fe03f800000000000000000000000000000000000000000000000000003881043000000000000000000000000000000000000000000000000000000000c70ef8cff3fe00000000000000000000000000000000000000000000000000000070e3018f1d0000000000000000000000000000000000000000000000000000fffe18c1f3e60000000000000000000000000000000000000000000000000000fffe00ffffe00000000000000000000000000000000000000000000000000000c07ee3cfbfff
  | 3, 1 => 0xfe8ff4fe03f80000000000000000000000000000000000000000000000000000fff0e0ffff780000000000000000000000000000000000000000000000000000f87fe30fbf7f0000000000000000000000000000000000000000000000000000f78000f1fc000000000000000000000000000000000000000000000000000000f80fe0ff8ffd0000000000000000000000000000000000000000000000000000fffc10ffff840000000000000000000000000000000000000000000000000000c802e0ce00600000000000000000000000000000000000000000000000000000368fff31cfff
  | 3, 2 => 0xffffff0003ff0000000000000000000000000000000000000000000000000000ffffffffff7f0000000000000000000000000000000000000000000000000000fff000c1f0000000000000000000000000000000000000000000000000000000f78d14f1ff9d0000000000000000000000000000000000000000000000000000c70fffc1f3ff
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc4880fed5a80000000000000000000000000000000000000000000000000000f7bf7ff7ffff0000000000000000000000000000000000000000000000000000fc4880fed5a80000000000000000000000000000000000000000000000000000f7bf7ff7ffff00000000000000000000000000000000000000000000000000005bf7ff092a570000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000ffffffbbefdf00000000000000000000000000000000000000000000000000005ad5b55f9f3d
  | 0, 1 => 0xb69d35b3cf9d00000000000000000000000000000000000000000000000000005bf7ff5fbf7f0000000000000000000000000000000000000000000000000000b69d35b3cf9d00000000000000000000000000000000000000000000000000005840805e95280000000000000000000000000000000000000000000000000000f7bf7ff7ffff0000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000fc4880fed5a8000000000000000000000000000000000000000000000000000053b77f57bf7f
  | 0, 2 => 0xe72e5ae5f3e60000000000000000000000000000000000000000000000000000fc4fe0fed7f80000000000000000000000000000000000000000000000000000fff880fffda80000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000b69d35b3cf9d000000000000000000000000000000000000000000000000000043265a45b3660000000000000000000000000000000000000000000000000000ff6edafff7ee0000000000000000000000000000000000000000000000000000ffffffedfbf7
  | 0, 3 => 0x5b66da5fb76e0000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000a7bf7fa16ad70000000000000000000000000000000000000000000000000000129535138f1d0000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000fc4880bac58800000000000000000000000000000000000000000000000000005bf7ff5fbf7f00000000000000000000000000000000000000000000000000005bf7ffa96ad7
  | 0, 4 => 0x5bf7ff5fbf7f0000000000000000000000000000000000000000000000000000fc48800800000000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000b69d35451a350000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000129535138f1d0000000000000000000000000000000000000000000000000000b52a4ab2e5ca0000000000000000000000000000000000000000000000000000e40800e4d1a0
  | 0, 5 => 0xa60c10a1c3840000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000fc48800800000000000000000000000000000000000000000000000000000000f7bf7ff7ffff0000000000000000000000000000000000000000000000000000fc4fe0fed7f80000000000000000000000000000000000000000000000000000ae4c90a9c3840000000000000000000000000000000000000000000000000000fc4880fed5a80000000000000000000000000000000000000000000000000000fff880fffda8
  | 0, 6 => 0x91250008110000000000000000000000000000000000000000000000000000e72e5a01224600000000000000000000000000000000000000000000000000000000001204080000000000000000000000000000000000000000000000000000ffffff092a57000000000000000000000000000000000000000000000000000003b77f012a570000000000000000000000000000000000000000000000000000b69d35b3cf9d0000000000000000000000000000000000000000000000000000b69d35b3cf9d00000000000000000000000000000000000000000000000000005840805e9528
  | 0, 7 => 0xfeddb5ffdfbd0000000000000000000000000000000000000000000000000000b40800b2c588000000000000000000000000000000000000000000000000000018d1a51a0c190000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000b69d35b3cf9d0000000000000000000000000000000000000000000000000000e72e5ae5f3e600000000000000000000000000000000000000000000000000005bf0805fbd2800000000000000000000000000000000000000000000000000004962ca4c3062
  | 0, 8 => 0x5bf7ff5fbf7f0000000000000000000000000000000000000000000000000000fff880fffda80000000000000000000000000000000000000000000000000000b69800b3cd8800000000000000000000000000000000000000000000000000005bf5b55fbf3d0000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000fc4880fed5a80000000000000000000000000000000000000000000000000000a40800a040800000000000000000000000000000000000000000000000000000ffffffa96ad7
  | 0, 9 => 0xf40800f6d5a80000000000000000000000000000000000000000000000000000fc4fe0fed7f80000000000000000000000000000000000000000000000000000ffffffbbefdf0000000000000000000000000000000000000000000000000000a40800a0408000000000000000000000000000000000000000000000000000005bf7ff092a570000000000000000000000000000000000000000000000000000ffffff1baf5f00000000000000000000000000000000000000000000000000005bf7ff5fbf7f00000000000000000000000000000000000000000000000000005bf7ff5fbf7f
  | 0, 10 => 0x5847e05e97780000000000000000000000000000000000000000000000000000fc4880fed5a80000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000e72e5ae5f3e600000000000000000000000000000000000000000000000000005bf7ff5fbf7f0000000000000000000000000000000000000000000000000000b69a4ab3cdca0000000000000000000000000000000000000000000000000000ffffffa96ad700000000000000000000000000000000000000000000000000005bf7ff5fbf7f
  | 0, 11 => 0xe72f7fe5f3f700000000000000000000000000000000000000000000000000004962ca4c306200000000000000000000000000000000000000000000000000000000005695280000000000000000000000000000000000000000000000000000fff88009280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b40800f6d5a80000000000000000000000000000000000000000000000000000a40800a040800000000000000000000000000000000000000000000000000000000000120408
  | 0, 12 => 0x5bf7ff5fbf7f0000000000000000000000000000000000000000000000000000e72e5ae5f3e600000000000000000000000000000000000000000000000000005bf7ff5fbf7f0000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000fc4880fed5a80000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000000000f6d5a8
  | 0, 13 => 0xb69d35b3cf9d0000000000000000000000000000000000000000000000000000e72e5ae5f3e600000000000000000000000000000000000000000000000000000840800800000000000000000000000000000000000000000000000000000000ffffffedfbf7000000000000000000000000000000000000000000000000000018d1a51a0c190000000000000000000000000000000000000000000000000000fc489ffed5af0000000000000000000000000000000000000000000000000000ffffffedfbf700000000000000000000000000000000000000000000000000005bf7ff5fbf7f
  | 0, 14 => 0xb69d35b3cf9d0000000000000000000000000000000000000000000000000000fc4880fed5a800000000000000000000000000000000000000000000000000005bf7ff5fbf7f000000000000000000000000000000000000000000000000000003b77f012a570000000000000000000000000000000000000000000000000000fc4fe05e97780000000000000000000000000000000000000000000000000000fc4880fed5a80000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000ffffffa96ad7
  | 0, 15 => 0xffffffffffff0000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000b69d35b3cf9d00000000000000000000000000000000000000000000000000005bf7ff092a570000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000ffffff092a57
  | 1, 0 => 0x18d1a51a0c190000000000000000000000000000000000000000000000000000000000f6d5a80000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000b69d35b3cf9d0000000000000000000000000000000000000000000000000000fff880fffda800000000000000000000000000000000000000000000000000004b66da4db3660000000000000000000000000000000000000000000000000000000000f6d5a8
  | 1, 1 => 0xffffff092a57000000000000000000000000000000000000000000000000000003b77f012a570000000000000000000000000000000000000000000000000000e72e5a13264e00000000000000000000000000000000000000000000000000005bf7e05fbf780000000000000000000000000000000000000000000000000000000000a040800000000000000000000000000000000000000000000000000000f7bd35f7ffbd00000000000000000000000000000000000000000000000000004962ca4c30620000000000000000000000000000000000000000000000000000000000000000
  | 1, 2 => 0xf40800f6d5a80000000000000000000000000000000000000000000000000000b7bf7fb3efdf0000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000fff880fffda80000000000000000000000000000000000000000000000000000a40800f6d5a80000000000000000000000000000000000000000000000000000fc4fe0080250
  | 1, 3 => 0xffffff092a570000000000000000000000000000000000000000000000000000a40800a040800000000000000000000000000000000000000000000000000000b69d35b3cf9d000000000000000000000000000000000000000000000000000003b77f012a570000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000b69d35b3cf9d0000000000000000000000000000000000000000000000000000a40800a04080000000000000000000000000000000000000000000000000000043265a45b366
  | 1, 4 => 0xffffffbbefdf0000000000000000000000000000000000000000000000000000000000f6d5a80000000000000000000000000000000000000000000000000000e72e5ae5f3e600000000000000000000000000000000000000000000000000005bf7ff4dbb770000000000000000000000000000000000000000000000000000b69d35b3cf9d00000000000000000000000000000000000000000000000000005bf0805fbd28000000000000000000000000000000000000000000000000000018d1a51a0c190000000000000000000000000000000000000000000000000000ffffff092a57
  | 1, 5 => 0xffffff092a570000000000000000000000000000000000000000000000000000b69d35b3cf9d0000000000000000000000000000000000000000000000000000ffffff5fbf7f0000000000000000000000000000000000000000000000000000000000f6d5a80000000000000000000000000000000000000000000000000000ffffff092a57000000000000000000000000000000000000000000000000000003b77f012a570000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000ffffffa96ad7
  | 1, 6 => 0xb69d35010a1500000000000000000000000000000000000000000000000000004962ca4c30620000000000000000000000000000000000000000000000000000b69d35b3cf9d0000000000000000000000000000000000000000000000000000f72e5af7f7ee0000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000fc4fe0fed7f800000000000000000000000000000000000000000000000000004962ca4c30620000000000000000000000000000000000000000000000000000feddb5ffdfbd
  | 1, 7 => 0xa7bf7fa16ad70000000000000000000000000000000000000000000000000000fff8800928000000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000e72e5ae5f3e6000000000000000000000000000000000000000000000000000018d1a51a0c190000000000000000000000000000000000000000000000000000000000f6d5a80000000000000000000000000000000000000000000000000000a40800a040800000000000000000000000000000000000000000000000000000000000000000
  | 1, 8 => 0xf6d5a80000000000000000000000000000000000000000000000000000fc4880fed5a80000000000000000000000000000000000000000000000000000a7b81fa168870000000000000000000000000000000000000000000000000000e7bf7fe5fbf7000000000000000000000000000000000000000000000000000003265a0122460000000000000000000000000000000000000000000000000000ffffffbbefdf0000000000000000000000000000000000000000000000000000b69d35b3cf9d00000000000000000000000000000000000000000000000000005bf7ff5fbf7f
  | 1, 9 => 0xffffff5fbf7f00000000000000000000000000000000000000000000000000005bf7ff5fbf7f0000000000000000000000000000000000000000000000000000a7b81fa1688700000000000000000000000000000000000000000000000000004962ca4c30620000000000000000000000000000000000000000000000000000a408000000000000000000000000000000000000000000000000000000000000fc4fe0fed7f80000000000000000000000000000000000000000000000000000a40800a04080000000000000000000000000000000000000000000000000000003b760012a50
  | 1, 10 => 0xfc48805e952800000000000000000000000000000000000000000000000000000840800800000000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000fff880fffda80000000000000000000000000000000000000000000000000000ffffff092a57000000000000000000000000000000000000000000000000000018d1a51a0c190000000000000000000000000000000000000000000000000000ffffff5fbf7f0000000000000000000000000000000000000000000000000000a40800a04080
  | 1, 11 => 0xff6ffafff7fe00000000000000000000000000000000000000000000000000004962ca4c30620000000000000000000000000000000000000000000000000000fedff5ffdffd0000000000000000000000000000000000000000000000000000fc4880fed5a8000000000000000000000000000000000000000000000000000018d1a51a0c19000000000000000000000000000000000000000000000000000003b01f012807000000000000000000000000000000000000000000000000000000077f00025700000000000000000000000000000000000000000000000000005bf7ff5fbf7f
  | 1, 12 => 0xb7bf7fb3efdf0000000000000000000000000000000000000000000000000000fff89ffffdaf0000000000000000000000000000000000000000000000000000ffffe0fffff80000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000fe4c90ffd7ac0000000000000000000000000000000000000000000000000000ff6ffafff7fe00000000000000000000000000000000000000000000000000000007750002550000000000000000000000000000000000000000000000000000b69d35b3cf9d
  | 1, 13 => 0x3b01f0128070000000000000000000000000000000000000000000000000000fff880fffda8000000000000000000000000000000000000000000000000000003b0000128000000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000a40800a040800000000000000000000000000000000000000000000000000000fc4ffafed7fe0000000000000000000000000000000000000000000000000000e72e5ae5f3e60000000000000000000000000000000000000000000000000000ff6ffaedf3f6
  | 1, 14 => 0xffffffffffff0000000000000000000000000000000000000000000000000000fff880fffda80000000000000000000000000000000000000000000000000000b40d20b2c7980000000000000000000000000000000000000000000000000000fffedaffffee0000000000000000000000000000000000000000000000000000e72800e5f1a00000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000fff885fffda90000000000000000000000000000000000000000000000000000fed880ffdda8
  | 1, 15 => 0xb60c10b3c78c0000000000000000000000000000000000000000000000000000fc4ffffed7ff000000000000000000000000000000000000000000000000000003b01f0128070000000000000000000000000000000000000000000000000000fff8805fbd280000000000000000000000000000000000000000000000000000a40800a040800000000000000000000000000000000000000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000002901501080500000000000000000000000000000000000000000000000000005bf6da5fbf6e
  | 2, 0 => 0xff6ffafff7fe0000000000000000000000000000000000000000000000000000b69d35b3cf9d00000000000000000000000000000000000000000000000000005ad7f55f9f7d0000000000000000000000000000000000000000000000000000fffda0ffffb8000000000000000000000000000000000000000000000000000003b01f0128070000000000000000000000000000000000000000000000000000e72e5a45b3660000000000000000000000000000000000000000000000000000e7be5fe5fbe7000000000000000000000000000000000000000000000000000003201a012006
  | 2, 1 => 0xfff89ffffdaf0000000000000000000000000000000000000000000000000000a40f7fa042d70000000000000000000000000000000000000000000000000000fc4fe0fed7f80000000000000000000000000000000000000000000000000000fffdb5ffffbd0000000000000000000000000000000000000000000000000000ffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000fc4fe0fed7f8
  | 2, 2 => 0x4840804c1020000000000000000000000000000000000000000000000000000001224a0020420000000000000000000000000000000000000000000000000000ff6880fff5a80000000000000000000000000000000000000000000000000000fc4ec0fed7e80000000000000000000000000000000000000000000000000000fc4fe0fed7f80000000000000000000000000000000000000000000000000000fc4fe0fed7f800000000000000000000000000000000000000000000000000005bf7ff5fbf7f000000000000000000000000000000000000000000000000000000977f000a57
  | 2, 3 => 0xf69d35f7dfbd0000000000000000000000000000000000000000000000000000e40e40e4d3e00000000000000000000000000000000000000000000000000000ffffff5fbf7f0000000000000000000000000000000000000000000000000000f7bf7f012a570000000000000000000000000000000000000000000000000000f72f7af7f7fe0000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000029535010a150000000000000000000000000000000000000000000000000000000000f6d5a8
  | 2, 4 => 0xffffff5fbf7f0000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000fc4fe0fed7f80000000000000000000000000000000000000000000000000000ffffe0fffff80000000000000000000000000000000000000000000000000000000000f6d5a80000000000000000000000000000000000000000000000000000ffffffedfbf70000000000000000000000000000000000000000000000000000fc4da0fed7b8000000000000000000000000000000000000000000000000000003b01f012807
  | 2, 5 => 0xfffedaffffee00000000000000000000000000000000000000000000000000000840800800000000000000000000000000000000000000000000000000000000a40800a040800000000000000000000000000000000000000000000000000000fc4da0fed7b80000000000000000000000000000000000000000000000000000000000f6d5a80000000000000000000000000000000000000000000000000000fc4ffffed7ff0000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000ffffffffffff
  | 2, 6 => 0xfedff5090a55000000000000000000000000000000000000000000000000000018d1a508081100000000000000000000000000000000000000000000000000005b67fa5fb77e00000000000000000000000000000000000000000000000000004006404493600000000000000000000000000000000000000000000000000000fc4fe0fed7f80000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000fc4880ecd1a000000000000000000000000000000000000000000000000000004960804c3020
  | 2, 7 => 0x3b01f0128070000000000000000000000000000000000000000000000000000fc4fe0fed7f80000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000ffffff092a570000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000076000025000000000000000000000000000000000000000000000000000004962ca4c3062
  | 2, 8 => 0xb7bd3fb3ef9f0000000000000000000000000000000000000000000000000000fff880fffda80000000000000000000000000000000000000000000000000000fff880fffda80000000000000000000000000000000000000000000000000000fffffafffffe0000000000000000000000000000000000000000000000000000ffffffffffff00000000000000000000000000000000000000000000000000004962ca0820420000000000000000000000000000000000000000000000000000109125120c190000000000000000000000000000000000000000000000000000ffffffffffff
  | 2, 9 => 0xffffffffffff0000000000000000000000000000000000000000000000000000b69c10b3cf8c00000000000000000000000000000000000000000000000000005bf0800928000000000000000000000000000000000000000000000000000000e72e5ae5f3e600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000000077f0002570000000000000000000000000000000000000000000000000000ff6880fff5a8
  | 2, 10 => 0xffffffffffff00000000000000000000000000000000000000000000000000001841a01a0418000000000000000000000000000000000000000000000000000003b01f0128070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f0000070000000000000000000000000000000000000000000000000000b69d35b3cf9d00000000000000000000000000000000000000000000000000005bf7ff5fbf7f0000000000000000000000000000000000000000000000000000ff6edafff7ee
  | 2, 11 => 0xb69f7fb3cfdf000000000000000000000000000000000000000000000000000018d1a51a0c190000000000000000000000000000000000000000000000000000a40800a040800000000000000000000000000000000000000000000000000000fc4fe0bac7d80000000000000000000000000000000000000000000000000000fed880ffdda80000000000000000000000000000000000000000000000000000000000b2c5880000000000000000000000000000000000000000000000000000fc4fe0fed7f80000000000000000000000000000000000000000000000000000fff880fffda8
  | 2, 12 => 0xf40f60f6d7f8000000000000000000000000000000000000000000000000000001200a00200200000000000000000000000000000000000000000000000000001000001285080000000000000000000000000000000000000000000000000000ffffe0fffff80000000000000000000000000000000000000000000000000000fe4ff0ffd7fc0000000000000000000000000000000000000000000000000000fff880fffda80000000000000000000000000000000000000000000000000000e72e5aa1e3c6000000000000000000000000000000000000000000000000000003b01f012807
  | 2, 13 => 0xf7bf7fb3efdf0000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000ffffff5fbf7f0000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000b69d20b3cf98000000000000000000000000000000000000000000000000000000012500001100000000000000000000000000000000000000000000000000005bf7ff4dbb770000000000000000000000000000000000000000000000000000ffffffffffff
  | 2, 14 => 0xfc4c80fed7a80000000000000000000000000000000000000000000000000000feddb5bbcf9d000000000000000000000000000000000000000000000000000000077f0002570000000000000000000000000000000000000000000000000000fff880fffda80000000000000000000000000000000000000000000000000000ff6edafff7ee000000000000000000000000000000000000000000000000000041224a4430620000000000000000000000000000000000000000000000000000ffffffbbefdf0000000000000000000000000000000000000000000000000000ffffffffffff
  | 2, 15 => 0xffffff5fbf7f0000000000000000000000000000000000000000000000000000ffffe0092a500000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000ffffff4dbb770000000000000000000000000000000000000000000000000000feddb5090a150000000000000000000000000000000000000000000000000000ffffffa9ebd70000000000000000000000000000000000000000000000000000fff880fffda80000000000000000000000000000000000000000000000000000ffffffffffff
  | 3, 0 => 0xffffffffffff0000000000000000000000000000000000000000000000000000ffffe0fffff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff6ffafff7fe00000000000000000000000000000000000000000000000000005bf7ff1baf5f0000000000000000000000000000000000000000000000000000fffedaedfbe60000000000000000000000000000000000000000000000000000fffec0ffffe80000000000000000000000000000000000000000000000000000ffffffffffff
  | 3, 1 => 0xfedff5ffdffd0000000000000000000000000000000000000000000000000000ffffe0fffff80000000000000000000000000000000000000000000000000000ffffff5fbf7f0000000000000000000000000000000000000000000000000000f7b800f7fda80000000000000000000000000000000000000000000000000000fedff5ffdffd0000000000000000000000000000000000000000000000000000fffc90ffffac00000000000000000000000000000000000000000000000000004842c04c10600000000000000000000000000000000000000000000000000000b69f7fb3cfdf
  | 3, 2 => 0xffffff092a570000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000fff880edf9a00000000000000000000000000000000000000000000000000000f7bd35f7ffbd0000000000000000000000000000000000000000000000000000e72f7fe5f3f7
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 405 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 405 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 405 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 405 then wireAt i else 0
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
  | 5 => 54
  | 6 => 150
  | 7 => 79
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xfffa7296ff2cfcd0f61e82b4df3b481ddb51f2e9d67cae34cbe5fc69c82bc7c7c3ae331cc0829e04ba9184aeb8ec88cab3def7fcb0370e7fad7eee41a31a88ab9b3397c99b0979a590c2c9078fbee73e885a8424882e767779695e7b787b7f0572e0b30772da899c718f744f6f0001816d3ef85a5c60cd6258d6fd025577ba1950befcef4fb2beee4ceed47c4962eea548ae9bc1487ea50b36d9d6493399212a1f5260d61cbb8ef71708ce8816ed2a4515e2632314e78f9310f746bc106f6b000f1265740e10eb440d81b69809073ca5039fcaa202db71a0
  | 6, 0 => 0x3f03f5d13d0975633c71b0923a8d85f33a82a7e337ff5c8b371fff313662c45234fa47d134c61ce4338dc01b333c765831bf5f2d306a6d2f2d6fbb802ce384ab2c9221e72c5e54df2c25485b2a67b280298caa252608ac4423a8da94230d13b320f259eb20f0ba5620d3d93220c549871f3769221f2959291ed3126e1ed0aa221d62fcac1d5b5dc81c879ee11b30be7f17b47310179512581780280516ff71ce167b58e81658ec5614f20446146dd67811d5e93b1160f5600feca8e60fa7c5210eccb7400ea563de0d8687440c5be1980a5a9dcf0a4b7ec008e5298e08c0717607a854b606e534f106b6b95906a5dad805ecc2ee0434951c0330b353011a216d
  | 6, 1 => 0xc23ce783c060a091bcd4bababc2067d6bbf07120b749d50ab5bc9ac4b04cf30caec130b8ad209d4facd99b96aa4ba25ea70aed3f9ed62931942d0a49902d5b0c8cbd7c128a7a9a9d8a5ef65a8731d6b783e137158284318980f382ad7cff46767b76e1307b2941c178e6d4c678b94480772d50a8760a1d227582211b736c3eab6ff442ca6fa458616d5d4dc16b0a84206a5146a369904ec968e94f1367d8f79866eca73966cfa9b564f83f645f41ae8d5b3a8c005add672f5a2cc3f457cc0cc35723328d550a7c8054f6b5bf54c3ae3054306802539709914f9e53204f465b0a4d229bd54d168c354c3eeeff49ee7a4946c1b2c846b9b618462e0c024438b241
  | 6, 2 => 0xfba0428cf61e82b4f56a71faf3b31ac9ee12c54dec6f887be6527f1ce2fd55bedea4ce9edcc9e4eedba5a911dabf3809d98cf304d8f3398ed5b4bbf6d3c8d18ed3678b5cd17de2e1d11723e1cba7452bc99680d2c3248b03
  | 7, 0 => 0x9244de83924276378ff96af68726336284d2c1756f1f7e7a6bee9c07694152886724e6de5db7a25f5bcd8fcd5ab5abb1563a363755e7a0d652e2f8d7526f455b4e31041e4cfebf194c9baf514c6505a34b8b4c2a479295b946d9577145d1eda144efaef6448b58424488eff64433319840fd5c893f1911403e22f7d83d084ce73c05e1c63bbd9fd83092a0e22cf45da32cbbaac6292e66d928f185fd2563fe1925029ba323bebf212232fccd21da3c201c91f0b51a28899f19e4b4771983ef5b197283231957081118bc18ae17c2485d159b56a6129b1125122bc8a90f52f7e70e62c7b30d31a82706c8af810626d89105a02dba0346c6ec0122554d002f4827
  | 7, 1 => 0xec58a0dbde7c5035dc5b1b28db4ac3adda5e734ed2b37aa2ca94fea2c87c4895c08ae272ba2b822db275c1e6a837e8f9a0e1879594ffe11f92a93537
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x8c10100000000c8102000000010c100000000010c10000000000c810100000000c810100000000c8101000000010c10000000000c810200000000c810100000000c810100000000c810200000000c8101000000010c100000000010c10000000000c810200000000c8102000000010c10000000000c810100000000c810100000000d010000000000c810100000000c810200000000c810200000000c810100000000c8101000000010c10000000000c810100000000c810200000000c8102000000008c10100000000c8102
  | 5, 1 => 0x10c100000000010c10000000000c810200000000c8102000000010c100000000010c100000000010c100000000010c100000000010c10000000000c8101000000010c10000000000c810100000000c810200000000c8101000000010c100000000010c10000000000c810100000000c810100000000c8102000000010c10000000000c810200000000c8101
  | 6, 0 => 0x100000000c8101000000008c102000000000000000000000c810100000000000010000000000002000000010c1000000000000002000000000000000000000c81020000000000002000000008c10100000000c81020000000000002000000010c10000000000000010000000000001000000000000100000000000000000000000002000000000000100000000c8102000000000000100000000c810200000000000020000000000002000000000000000000000000000000000000002000000000000000000000c8101
  | 6, 1 => 0xc810100000000c8102000000010c1000000000000002000000008c10100000000c81010000000000000000000010c100000000010c10000000000c81010000000000001000000000000200000000d0100000000010c10000000000c810100000000c810200000000000010000000000001000000010c10000000000d010000000000000010000000000002000000000000100000000c8101000000010c1000000000000000000000000000100000000c810200000000c810100000000c810200000000c810100000000c8101
  | 6, 2 => 0x1000000008c1020000000000002000000000000100000000c8101000000010c10000000000c810100000000000020000000000000000000010c1000000000000002000000010c1000000000000000000000000000100000000d0100000000010c100000000000000200000000c81020000000000000000000010c100000000010c100000000010c100000000008c101000000010c10000000000d01000000000000000000000000000000000000c810100000000c8101000000008c102
  | 6, 3 => 0x10c1000000000000001000000000000000000000000000000000000002000000000000100000000c8102000000010c10000000000c8102000000000000000000000000000000000000002000000000000000000000000000000000000001000000000000100000000c810100000000000000000000000001000000008c102000000000000100000000000000000000000002000000010c10000000000c810100000000c810100000000c81020000000000000000000000000200000000c8102000000010c1000000000000000
  | 6, 4 => 0x100000000c81020000000000000000000010c100000000000000000000000000000000000000000000000010c10000000000000010000000000000000000010c100000000010c100000000010c10000000000d010000000000c8102000000010c100000000010c10000000000c810100000000c8101000000010c10000000000c81020000000000002
  | 7, 0 => 0x100000000000010000000000000000000000000200000000000010000000000000000000000000000000000000000000000000002000000000000100000000000010000000000002000000000000200000000000020000000000001000000000000000000000000010000000000002000000000000100000000000020000000000000000000000000000000000000010000000000001000000000000200000000000010000000000000000000000000100000000000020000000000001
  | 7, 1 => 0x10000000000001000000000000200000000000020000000000002000000000000000000000000000000000000002000000000000000000000000010000000000000000000000000200000000000010000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000200000000000010000000000001000000000000100000000000000000000000000000000000000000000000000010000000000002
  | 7, 2 => 0x100000000000020000000000001000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000100000000000010000000000001000000000000100000000000000000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_31 roots_31 6 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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
private theorem z3 : ∀ i, 0 ≤ i → i < 5 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_16 : ∀ i, 16 ≤ i → i < 32 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_32 : ∀ i, 32 ≤ i → i < 37 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 32 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 37 → Z 4 i = true := (range_split z4_0 (range_split z4_16 z4_32))
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
private theorem z5_336 : ∀ i, 336 ≤ i → i < 337 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 336 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 337 → Z 5 i = true := (range_split (range_split (range_split (range_split z5_0 z5_16) (range_split z5_32 (range_split z5_48 z5_64))) (range_split (range_split z5_80 (range_split z5_96 z5_112)) (range_split z5_128 (range_split z5_144 z5_160)))) (range_split (range_split (range_split z5_176 z5_192) (range_split z5_208 (range_split z5_224 z5_240))) (range_split (range_split z5_256 (range_split z5_272 z5_288)) (range_split z5_304 (range_split z5_320 z5_336)))))
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
private theorem z6_672 : ∀ i, 672 ≤ i → i < 688 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 672 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_688 : ∀ i, 688 ≤ i → i < 694 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 688 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 694 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 (range_split z6_48 z6_64))) (range_split (range_split z6_80 (range_split z6_96 z6_112)) (range_split z6_128 (range_split z6_144 z6_160)))) (range_split (range_split (range_split z6_176 z6_192) (range_split z6_208 (range_split z6_224 z6_240))) (range_split (range_split z6_256 (range_split z6_272 z6_288)) (range_split z6_304 (range_split z6_320 z6_336))))) (range_split (range_split (range_split (range_split z6_352 z6_368) (range_split z6_384 (range_split z6_400 z6_416))) (range_split (range_split z6_432 (range_split z6_448 z6_464)) (range_split z6_480 (range_split z6_496 z6_512)))) (range_split (range_split (range_split z6_528 z6_544) (range_split z6_560 (range_split z6_576 z6_592))) (range_split (range_split z6_608 (range_split z6_624 z6_640)) (range_split z6_656 (range_split z6_672 z6_688))))))
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
private theorem z7_336 : ∀ i, 336 ≤ i → i < 341 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 336 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 341 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 (range_split z7_48 z7_64))) (range_split (range_split z7_80 (range_split z7_96 z7_112)) (range_split z7_128 (range_split z7_144 z7_160)))) (range_split (range_split (range_split z7_176 z7_192) (range_split z7_208 (range_split z7_224 z7_240))) (range_split (range_split z7_256 (range_split z7_272 z7_288)) (range_split z7_304 (range_split z7_320 z7_336)))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 28 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 16 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 28 → Z 8 i = true := (range_split z8_0 z8_16)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 14]⟩], 15⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 10 := by decide

theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (3936921768 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (3936921768 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936921768 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 10 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (3936921768 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 10 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_12829_aux

theorem PEqualNP.Outside.L_meta_12829 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936921768 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936921768 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_12829_aux.wit, PEqualNP.Outside.L_meta_12829_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_12829_aux.wit_sz (PEqualNP.Outside.L_meta_12829_aux.lower s hs), PEqualNP.Outside.L_meta_12829_aux.wit_ev⟩
