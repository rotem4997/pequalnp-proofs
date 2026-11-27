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

namespace PEqualNP.Outside.L_meta_12893_aux

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

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfaaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00faaaaa00
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeaaaa88aaaaaa00eeaaaa88aaaaaa00eeaaaa88aaaaaa00eeaaaa88aaaaaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcc0c0c0f0000000fcc0c0c0f0000000fcc0c0c0f0000000fcc0c0c0f0000000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfeeaeac8faaaaa00feeaeac8faaaaa00feeaeac8faaaaa00feeaeac8faaaaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_29
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (5, 13), (5, 21), (8, 9), (12, 13), (12, 28), (16, 17), (20, 21), (20, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [1, 1, 5, 5, 8, 12, 12, 16, 20, 20, 24, 24]
def r2sG : List Nat := [9, 17, 13, 21, 9, 13, 28, 17, 21, 28, 25, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := [13215951753481, 22011910555921]
def xsM : List Nat := roots_29.map (· &&& dom_29)
def goalM : Nat := goal_29 &&& dom_29
def NN : Nat → Nat
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x86580566
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000000000000000000000000000000000000000000000000000000000003300330000000000000000000000000000000000000000000000000000000000303030300000000000000000000000000000000000000000000000000000000022222222
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c70000000000000000000000000000000000000000000000000000000000000036c000000000000000000000000000000000000000000000000000000000000000f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfca0000000000000000000000000000000000000000000000000000000000000e750000000000000000000000000000000000000000000000000000000000000b6c00000000000000000000000000000000000000000000000000000000000005bf
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_29 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_29 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_29 == dom_29) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_29 goalM u ys) : RunD dom_29 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_29 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
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
  scr dom_29 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_29 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_29 roots_29 goal_29 5 := by
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

theorem low_29 : Lower dom_29 roots_29 goal_29 5 := S_29.noCircuit

namespace S_59
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (3, 11), (3, 19), (3, 35), (8, 9), (10, 11), (16, 17), (18, 19), (24, 25), (26, 27), (26, 58), (33, 35), (33, 41), (33, 49), (34, 35), (40, 41), (42, 43), (42, 58), (48, 49), (50, 51), (50, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 1, 3, 3, 3, 8, 10, 16, 18, 24, 26, 26, 33, 33, 33, 34, 40, 42, 42, 48, 50, 50, 56, 56]
def r2sG : List Nat := [9, 17, 11, 19, 35, 9, 11, 17, 19, 25, 27, 58, 35, 41, 49, 35, 41, 43, 58, 49, 51, 58, 57, 58]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [3411046699273]
def xsM : List Nat := roots_59.map (· &&& dom_59)
def goalM : Nat := goal_59 &&& dom_59
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xaa77fe47
  | 5, 0 => 0xf0260ba
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f000000000000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x6884
  | 5, 0, 0 => 0x56a05
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
  | 0, 0 => 0xfff0000000000000000000000000000000000000000000000000000000000000368d5c0000000000000000000000000000000000000000000000000000000000f80f800000000000000000000000000000000000000000000000000000000000c70e600000000000000000000000000000000000000000000000000000000000368000000000000000000000000000000000000000000000000000000000000000701f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfff8100000000000000000000000000000000000000000000000000000000000b69d5c0000000000000000000000000000000000000000000000000000000000fc4f8a0000000000000000000000000000000000000000000000000000000000e72e650000000000000000000000000000000000000000000000000000000000b6981000000000000000000000000000000000000000000000000000000000005bf7ff
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

namespace S_62
def pairsG : List (Nat × Nat) := [(6, 38), (12, 28), (14, 30), (14, 46), (20, 28), (22, 30), (22, 54), (24, 28), (26, 30), (26, 58), (34, 38), (36, 38), (42, 46), (42, 58), (44, 46), (44, 60), (50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [6, 12, 14, 14, 20, 22, 22, 24, 26, 26, 34, 36, 42, 42, 44, 44, 50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [38, 28, 30, 46, 28, 30, 54, 28, 30, 58, 38, 38, 46, 58, 46, 60, 54, 58, 54, 60, 58, 60]
def mpG : Nat := 0x3fffff
def pool6G : List Nat := [28648140318236, 28682634274332]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x688655d3
  | 4, 0 => 0x1ded6f73
  | 5, 0 => 0xc99170a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5555000055550000000000000000000000000000000000000000000000000000550055005500550000000000000000000000000000000000000000000000000055555555000000000000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000550000005500000000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000004444444400000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x883
  | 4, 0, 0 => 0x88b4
  | 5, 0, 0 => 0x4d4b5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 13
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
  | 0, 0 => 0x3f03f0000000000000000000000000000000000000000000000000000000000030f38e00000000000000000000000000000000000000000000000000000000003ffc00000000000000000000000000000000000000000000000000000000000003376d000000000000000000000000000000000000000000000000000000000030038000000000000000000000000000000000000000000000000000000000000cc87f0000000000000000000000000000000000000000000000000000000000033400
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3fa3f600000000000000000000000000000000000000000000000000000000003af3be00000000000000000000000000000000000000000000000000000000003ffe490000000000000000000000000000000000000000000000000000000000177f6d00000000000000000000000000000000000000000000000000000000003aa3b600000000000000000000000000000000000000000000000000000000002dddff0000000000000000000000000000000000000000000000000000000000177e49
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 7 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 7 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 7 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 7 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_62 == dom_62) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_62 goalM u ys) : RunD dom_62 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_62 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
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
  scr dom_62 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_62 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_62 roots_62 goal_62 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_62 goal_62 := by
    have h0 : isConstB dom_62 goal_62 = false := by decide +kernel
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

end S_62

theorem low_62 : Lower dom_62 roots_62 goal_62 6 := S_62.noCircuit

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (3, 11), (3, 19), (3, 35), (5, 13), (5, 21), (6, 38), (7, 15), (7, 23), (7, 39), (8, 9), (10, 11), (12, 13), (12, 28), (14, 15), (14, 30), (14, 46), (16, 17), (18, 19), (20, 21), (20, 28), (22, 23), (22, 30), (22, 54), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (33, 35), (33, 41), (33, 49), (34, 35), (34, 38), (36, 38), (37, 39), (37, 45), (37, 53), (40, 41), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 3, 3, 3, 5, 5, 6, 7, 7, 7, 8, 10, 12, 12, 14, 14, 14, 16, 18, 20, 20, 22, 22, 22, 24, 24, 26, 26, 26, 33, 33, 33, 34, 34, 36, 37, 37, 37, 40, 42, 42, 42, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [9, 17, 11, 19, 35, 13, 21, 38, 15, 23, 39, 9, 11, 13, 28, 15, 30, 46, 17, 19, 21, 28, 23, 30, 54, 25, 28, 27, 30, 58, 35, 41, 49, 35, 38, 38, 39, 45, 53, 41, 43, 46, 58, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffffffffffff
def pool6G : List Nat := [28648140320284, 48538299666697, 57355936603174, 46209790511907, 55087622134842, 55156088572218, 46240057924646, 3410440752401, 28618209759497, 24220029035281, 28682634274332, 24219557300497, 46339142846755, 28617738031369, 28682634274321, 46291277254970, 15424070230793, 46209924731171, 55005884057891, 46209993153574, 13215985439497, 28648140318217, 48559843580966, 46210395804427]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 3 => 4
  | 4 => 28
  | 5 => 235
  | 6 => 506
  | 7 => 285
  | 8 => 28
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xd0cdc5d371dc4aa15220252a39a46f60
  | 4, 0 => 0xfcfbff64db2aad94d62af2fed36a2febcfc1b3c2cbe7edbdc591f13fc16c54dab0d0dba6a924cfe6a4c6359a9d2d2f6d8fc622888d0b13808a5ca5d585b1b83b81ce6f357009fd115de3e530534df19a4428cdd03eb06ee63940f04634362df12373d643128a61780c2b5621064ce56c
  | 5, 0 => 0x328dc4c231e92a7e316e1dca31434e0d30dad80f302783802f525f702f000fff2d1a43cf2bfba36f2b316ca82a8cd2642a2f377c2949f4402942259c2918bfc728cb2b66284400ab27f6075627a3b7e526e18e732699205722d2df622131d7c8210aa673202215df1f6db3321f38cd661c6367571c5f09e318fac23318e0c323189ae7b9183801af1587aec6152e0a2914307aae13fd577213eec94813a675f912939bc5127942bb109d8095103b31880f7548c50f52dc2d0f4897ff0d5bbbfd0d213aee0ca3b5de0c9da4810c92712e09c42bfc095de0bd089686c30766625a062fcd3c053192650505cb3104c6c26b04a50c2004446e8903b5baae014dcdd4
  | 5, 1 => 0x64650be463f945bf63dd55d663776f9a610bd5fa6029a375602558ae5fa58fc95f31b9465db949325c9a46cd5c93404c5acf501f59e97b2159df37c5593487ff587b77ef5620165b556d880a543401f453ba57545338b815530de0eb524b943950a12c225073fb7e504d4efb500d12e44ea2937a4e112ff04dd7e8284d5268a64d3725ea4c436aeb4b9259844b86bd1b4b2001bb4abb798349e45de847ea6d9e47a36988470e162746dd184944d95aaa44aea2a444384562433af14a42b914004276f6233ff02e263e9d06223e49c5a53c23ccfe3bd2f08e3b2a018539747ce6389f05483893d60c37092aa2361d64a635ff148834769be933fdfaaf33334d36
  | 5, 2 => 0xab0fd97aa92f7e98a8fd1a4da85f605fa7fed1d9a7f0a0d1a75475bba64a1efda3f52c25a3e60cd1a2ff1743a1a56fdea09448b79fb8471c9e5474ab9c1855a09aa9530a9a01405599bd0b2a95b13e6c92c001569256e3c19235244f921403bc91b78d7d9126e36490ca69a18f9cca078ed127688dd419f48d925c3d8b63a93c8ab98d398835508f8822917a860a470685fc2d8d84a4139a83a4fa097efcc6c27df5304e7cde492d7cb250437c93da2e7a3ee8da7947569e7555f829754da807729f9eb371dc527b719a59df717dd9f66fecf3326fdbca3b6eeea65f6ea658e86db961ae6d7ee5676a0153b26992f1fd68c17aba6781b0c86629d48265eefd3b
  | 5, 3 => 0xfdce71eafaa70a68f97d6cfdf7803f20f095e072f06f2423f047fa88ece2e9feebc6ca83e37bc926e14b39c0dfdb36a6ddbf6cf4dc2811ccda972b08d9e5bc3ad5a1ebd1d4ab7a5bd1d46bc7d18f4102ce878daccb1b77f4c8b4c739c4f49b3ec4acaba0c2b00d81c0d677c6bf84ffa6bdf418e2b9484e84b828a78cb76c725eb6cc4c12b65fb6a7b60ce932b55d9dddb4601447b2daf942b26c3194b1e47b86aedf6f27ad158600ab660281
  | 6, 0 => 0xcaea4b60c8b4e210c76b2fc0b3a14b50b3452190b29ade30aef7d190accc1e50a403c9e09d0144709b03469098a0e81097f425509620eff09230a8109154506090ca4c6090119c608a714d3089a0a2807fe25ca07fdb1f807b059160766625a074650a506de02a206d7e875068b2e440684a5df061ec7a905fcd06d05f3a13e05a60b08058bb6e50576a0bc0573298d0567fa510548460e0531926505127dcf04f2c66004a185c90478bc3504446e89043d2f150435b54103ac249f039fbae70321e57202d338cd023fab940207ae470206cbee0142d29e011b5cc600fd20bf00f495ed00d21ef400cc52f700b732f500ae9518007eb388001b07df0010041b
  | 6, 1 => 0x1dd816c61d88e1d31d7550671cdca4e31ccf529e1cb356241c6ee6621c6ab5321c05c4e21bcdde601b4bbe1f1ae554351aac0c6d1aa585c61a16c326197a8b1819264f9419251818191e9ec318fac233186d774618667dc9185ae160184b91ca1838f4ae17f42600178f9dc8178c8c4b1783d36c16dc805f15a1e513156a170714a7d9651483a138146ef72f13e23a6c13b13c8e131b9fca12b7be2111d0aa5911a82bf01182c6e9117f96bc11755fbb112c6c61110c69a710fafe6d10ef39b010bf090910be6719108dfb0010886d1610223c030fc3d6d10fb0eddc0f3c20c30ee18a610ed4dee30ea83cc00e49ffdb0e0dbeed0da1bf290d658d7d0cf2a6ea
  | 6, 2 => 0x2fe2e0532f4bf5882eb569e02eab2a932e70df342dddf23f2d7eac952d61793f2d2193672cfd4cb22cf97cf32c18000d2c05dd8b2ba5a8442b4593e42b2f56602ae8680829d53e96298c1c58296764912942259c28d427a828b9c5e4285367de2849052c27ab8edf2795459526f682bf26805eaa2675e93626135ace25e8b0c725999f732556479b254f9c34246f06e02426ef9222f43aa022e8246722a81639222f74ff21f604ad21f40ce021d6d25821bc88db212acd6b20f4e66f20d8c76720954fb32090380e200c227c1fe205301fbf3ceb1f9210cd1f7f06ec1f76c01b1f4a28031f1fb9041f002dd71ed2190f1eae35bc1e6c474a1df9ef811de01bef
  | 6, 3 => 0x41f959c1417c5d42415b734940e28a1e40617921405c9bd03f7c34683f4b285f3f3d9bc83f3833393f36085d3ebf5c103e8948e43e1269b63de0be6f3d7d0f9c3d75f3c43d4d31363cc117773cafee803ca896f23c4221bc3c2d8a3e3c1e40083bc2caa43b7aa2a33b7a7d2d3aa5591d3a7feac33a6b113b3a5309ac3a3164063a11cbe43798d039377da855374897ec373283c9372dec08362799a63621d99635f3bd8135dd39db35959eff358231293548db4e353a4a5935389f973508e32634eea3f034bd92e3341e4a893408359e3376f89932a1d489328bae7a324f8518323613c132130d4031e72f59316e1dca316ad0293139302930b17a1b30631aa2
  | 6, 4 => 0x602cf47e60297d0c5fc96c595f46862c5f16df6a5f0948945e8bb1c25e7f55035e6a7b7b5e5c21de5d9e8de65d915def5d03b9ec5bef837e5bce5bc35b45a6f85a4c1c605a3371dd59e97b2159611b6959245b2e5837cd81581db4c957aab698578794ff5756509b5710933d556d880a54f9d62354791a4054351c9f5209fae551dd5c7f51c5c2db50fcb6f250eb0a34504bfaff50383ce04f2ec0a04f2d25f44ec6e29e4ec2c41c4e112ff04d5aaba94d1090324b976b174b6936264ad0615b4ac954934aac03c04a19000849aa97d84938d519485c1743481d4670479f638346e0545d461b7ae344f5d81444b8dba6441e71a943a4ce57423cb56b422a1c6e
  | 6, 5 => 0x83cb685e83c8d69983a07057836e797082e41c9182e10d7782771924825b8c1e824ee3cb82485160819b4b088103242c8052974e7fda48b17fb95caf7e80eb2c7e6b005c7dd02c097d1d703d7d0413697c894c787b8a6f167aec6f237a9e70a176bb8fd37603a2dd75d13e92747725a7732bf0c272411d3c723ff342721dd9db71c7d0b2717dd9f670f57a3e70cb784070a6f9f56fecf3326fceca7b6e3726e26db546b16d686cfc6d54f5796cd020406c8c6b616a06ec3368bf569668bb602a689eda76688044f96824fdda681ddbe967fd9dd56725c473667d161b6668521364ef0a7e64650be463edfd5a63e0f03863dd55d663444f3b62d8cb5d628562b1
  | 6, 6 => 0xad2b6ba4ace648fbac10d15dabe64ae9ab52f45caaf7ad3daa939139a9791970a8fc3611a7f0a0d1a76b4f4da75475bba6e386d1a6768364a55d764ba406231da09448b7a08bf8959f2467fc9ea8900c9e6365479e011e319d7f6dca9d0621409cbc2a849b5bb1f19ac821149a9c282a99357d9199349fce98d7870b97ef9c3997e6f6239778f0db96689a0695ce12259588eb7e94dcaa48947c728893b63be6933fd0109180cfe5917b2ef18f875d3c8f8431c68e26e5f78dbce6708cff4b7e8cbec0d68c0b847c8a7a9db8899d1ab4892fe56d88a7607c884ccd3487e6ed1d8771bcb786ab52a1861c72c985de10cf8577d88584fccbd1847e797f83ed9738
  | 6, 7 => 0xfdaefc54fad792e2f9ee6814f8f99c2bf6d63872f447528af050ec42eddecab8ecf91ba1eb25403feb0d46f0eac35034eaa527b1e83107c0e4869f12e2616bd3e24bfe7be14b39c0df6952c0df41d99dded3701adc2811ccda41df7cd74f21ebd70814ffd64bef60d2355385d056097bcd32d22ccb0fec2dcab79fa6c5e7a398c4b27879c406c3f6c2b74169c2008871bf84ffa6be3b4e52bcf2e36dbc3e4c92bb9e85e0baa0f4b0ba680446b8fb36feb828a78cb8003918b7beecdcb792a617b73f3a50b6def638b57afcb1b57a9931b2a00218b0ed9442b03b1c5faf1ec88dae1f5e05ad86a1ee
  | 7, 0 => 0x1bebd8d51b9b06e31b96e8611b92f38f1b7dd38d1ae554351a2ecfee19b15e68196939d2191e9ec318b98c20186b8f5c1844b0bd17b1544817a485a01780280516ed244d169ad4dc167ebc1d1658ec56161ad83315303b88147387c814445611141a2b17140ddc3213b478a2131d3b5411c9fc59118cffeb106602d20ef521b50ecd7e060eccb7400de1f81f0db6ae630d8a4f090d359d660c0c577e0b8bbf6b0b8161930b5d6d290ae68dfb0a5133e10a4a1809093db6800801277907852a5a0766625a07540f080548460e046cf47e0451cc9a0406a80e0402104d03be3f6102fbbdeb02c7e1c602b51b88021cff9301dd076b01c0cf2f00f8abef00f26ece
  | 7, 1 => 0x3d7b1e3a3d4b1aee3d4337b83cc117773c394efb3c2d8a3e3bcc4b8e3aefec363a9cdd1a3a2919be386dc67538495668375c328c3672a2a735db2393358f846f3578c84e34f9221f34bd92e333ac494933641e9c33513a60333c765831c32ec331c2f66d315f0dca30c2219f30b17a1b30a94148301873803015b40f2ee5f83b2e00a7792dadaeb82d6782ad2cfda1512c9d909e2c81232c2b5379482ad2a9b42aa950482942259c28a5bcb4273fec7026bd9f662564f23a24f1d90e24c4815c242a74e0225227cd2214890021f40ce020bd10b42029837b1ede1f2a1eb180c41de01bef1dbf2e791db36f6a1d7d6fd81d0c61251cdca4e31c1160c61c02e4e5
  | 7, 2 => 0x717dd9f67134998b703428a26ee55b736e85fdac6d686cfc6bf88c416ad5427669da458569904ec96986998d690b0d3968bb602a679e3ab86722ad006608c413655e0be164bb1a68644d15206430b85d61b0ce8d615096cd608a602b602cf47e6013f4555e4f53365e0ed8325a910ab559e97b215756509b537f76e65310cae852b2351451529dc450c1bb7d509f8ca3509cfade50429db54fbdcc704f2308104f1c75a54ef5be6c4d26bb934cae6cf64c95027a4c8d80f44b550f714ad0615b49d837ae49aa97d84864ec2d481af57147c09368477294e646e757da4541e84843a4ce574389e25842a809fe400015073ef2c9303eca17bc3e51fe3b3d9f9c85
  | 7, 3 => 0xb749d50ab62e8f91b1838f47b15ac357b03b1c5faf359018ae1f5e05acd99b96aba7945faaf7ad3da8fc3611a55b949ea45e67e1a4234630a3ac4ce7a396f37fa32c9765a32013a5a304b7359d0621409cbc2a849c33cacc98d247e097e4107296f519d9956af0e495546bd091869cbe902d5b0c8f8b65ae8ed4acb68d8425078c0b847c8b3625d88ac1d328861a5c8185cf5b4385a3bc0f85203f7884fccbd184135e9583b31a7d824f20f6824ee3cb824ebd768077f7197dd6920f7d0413697b7c8fb07a05332c79ff8fe979fc07f678e4f5a277cbd18277b733fd7774f1d576abcfae76a6ae13764d3db575a33707747725a774289a0071e530e771e3fb21
  | 7, 4 => 0xfb7f4ed8fa359d84ec663512eac35034e9a376e3e64eaf5de5f2c308e157c57dd74f21ebd5f72ec6d4d1d63dd4b5a9d7d43a869fd41a74ead24ac501cdc8ba32cbd6d1cbc7abb727c77768a6c762f157c32546b1c2b74169c11b76cfbe620e8cbaf4e799bab4727ab9653685b7f96484b7794bf6
  | 8, 0 => 0xe5f2c308d43a869fb749d50ab03b1c5fa4234630a0e187959cbc2a849437159c8ff96af68f8b65ae8302b3d677cbd18269904ec95d017f51481af57146d9577144efaef6448b58423ef2c9303e51fe3b3d084ce7358f846f26bd9f66242a74e0196926bf1957081117a485a0167ebc1d
  | 9, 0 => 0x69904ec9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffaaaa00ffaaaa00000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000eeeeeeccaaaaaa00000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000fac8fac8fa00fa00000000000000000000000000000000000000000000000000eeaaeeaaaaaaaaaa
  | 0, 1 => 0xeaeaeaeaaaaaaaaa000000000000000000000000000000000000000000000000fa00fa00fa00fa00000000000000000000000000000000000000000000000000ccc8ccc800000000000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000faeaeaeafaaaaaaa000000000000000000000000000000000000000000000000ffaaaaaaffaaaaaa000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0
  | 0, 2 => 0xffffffff00000000000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000fefe0000fafa0000000000000000000000000000000000000000000000000000c8c8c8c800000000000000000000000000000000000000000000000000000000ffffc8c8ffff0000000000000000000000000000000000000000000000000000eeeeeeeeaaaaaaaa000000000000000000000000000000000000000000000000aaaaaa00aaaaaa00000000000000000000000000000000000000000000000000ffffff00ffffff00
  | 0, 3 => 0xaaaa5555aaaa5555000000000000000000000000000000000000000000000000a5a5a5a5a5a5a5a5000000000000000000000000000000000000000000000000aaaaaa88aaaaaa00000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000aa88aa88aa00aa00000000000000000000000000000000000000000000000000ff0000ffff0000ff000000000000000000000000000000000000000000000000fafac8c8fafa0000000000000000000000000000000000000000000000000000cccc000000000000
  | 0, 4 => 0xffff0000ffff00000000000000000000000000000000000000000000000000f0f00f0ff0f00f0f000000000000000000000000000000000000000000000000ffccffccff00ff00000000000000000000000000000000000000000000000000cccc33330000ffff000000000000000000000000000000000000000000000000f0c0c0c0f0000000000000000000000000000000000000000000000000000000ffc0c0c0ff000000000000000000000000000000000000000000000000000000eecceeccaa00aa000000000000000000000000000000000000000000000000009999999955555555
  | 0, 5 => 0xffffaa00ffffaa00000000000000000000000000000000000000000000000000cccccccc880088000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000f0f0f0f0f0f0a0a0000000000000000000000000000000000000000000000000fafac8c8fafac8c8000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000d5d5d5d555555555000000000000000000000000000000000000000000000000c3c3c3c30f0f0f0f
  | 0, 6 => 0xc3c3c3c3c3c3c3c3000000000000000000000000000000000000000000000000aaaaaaaaa0a0a0a0000000000000000000000000000000000000000000000000f0c0f0c0f000f000000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000ffccccccff000000000000000000000000000000000000000000000000000000555555555555555500000000000000000000000000000000000000000000000033333333ffffffff0000000000000000000000000000000000000000000000000000ffff0000ffff
  | 0, 7 => 0xffffccccffff000000000000000000000000000000000000000000000000000000ff00ff00ff00ff0000000000000000000000000000000000000000000000000f0f0f0f0f000f00000000000000000000000000000000000000000000000000ff00fa00ff00fa00000000000000000000000000000000000000000000000000f0f0fafaf0f0fafa000000000000000000000000000000000000000000000000af0faf0faf0faf0f000000000000000000000000000000000000000000000000aaaa8888aaaa0000000000000000000000000000000000000000000000000000cccc3333cccc3333
  | 0, 8 => 0xfff0fff0fff0fff0000000000000000000000000000000000000000000000000fffffafa00000000000000000000000000000000000000000000000000000000fafa0000fafa0000000000000000000000000000000000000000000000000000c0ffc0ff00ff00ff000000000000000000000000000000000000000000000000eecceecc00000000000000000000000000000000000000000000000000000000eeeeaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0000000000000000000000000000000000000000000000000fafafafafa00fa00
  | 0, 9 => 0xaaaaffffaaaaffff0000000000000000000000000000000000000000000000000000aaaa0000aaaa000000000000000000000000000000000000000000000000f0f3f0f3f0f3f0f3000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000f0c0f0c0f000f00000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000fe00fe00fe00fe00000000000000000000000000000000000000000000000000eeeeccccaaaa0000
  | 0, 10 => 0xff00ff55ff00ff55000000000000000000000000000000000000000000000000afafafafafafafaf000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f0f0f0f0f0f0c0c0000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000ff88ff88ff00ff000000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000faf0faf0faf0faf0
  | 0, 11 => 0xf0f0f0f0f000f000000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ff00ee00ff00aa000000000000000000000000000000000000000000000000000077007700ff00ff000000000000000000000000000000000000000000000000ff00aa00ff00aa00000000000000000000000000000000000000000000000000f0f0c0c0f0f00000000000000000000000000000000000000000000000000000ececececa0a0a0a0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0
  | 0, 12 => 0xaa00ffffaa00ffff0000000000000000000000000000000000000000000000008f8f8f8f0f0f0f0f000000000000000000000000000000000000000000000000fcfcfcfcf0f0f0f0000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000f2f2f2f2fafafafa000000000000000000000000000000000000000000000000fefefefefafafafa000000000000000000000000000000000000000000000000fafaf8f8fafaf8f800000000000000000000000000000000000000000000000000ff00aa00ff00aa
  | 0, 13 => 0xaaaa0000aaaa000000000000000000000000000000000000000000000000000088ff88ff00ff00ff000000000000000000000000000000000000000000000000ffffc0c0ffff000000000000000000000000000000000000000000000000000000003f3f0000ffff00000000000000000000000000000000000000000000000000ff55ff00ff55ff000000000000000000000000000000000000000000000000f0fff0fff0fff0ff00000000000000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000ffeeccccffaa0000
  | 0, 14 => 0xfefe0000fefe0000000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c800000000000000000000000000000000000000000000000022222222aaaaaaaa000000000000000000000000000000000000000000000000faeafaeafaeafaea000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000f0f0f0c0f0f0f0000000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000ffffaaaaffffaaaa
  | 0, 15 => 0xccccc8c8000000000000000000000000000000000000000000000000000000005050505050505050000000000000000000000000000000000000000000000000ffc0ffc0ff00ff00000000000000000000000000000000000000000000000000f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000f8f8f8f8f8f8f8f8000000000000000000000000000000000000000000000000e0e0e0e0a0a0a0a0000000000000000000000000000000000000000000000000070707070f0f0f0f000000000000000000000000000000000000000000000000ff00ee00ff00ee00
  | 1, 0 => 0xa8a8a8a8a0a0a0a00000000000000000000000000000000000000000000000001515151555555555000000000000000000000000000000000000000000000000fcccccccf0000000000000000000000000000000000000000000000000000000fffffafafffffafa0000000000000000000000000000000000000000000000000f0f3f3f0f0fffff000000000000000000000000000000000000000000000000f0f0f0f0f00000000000000000000000000000000000000000000000000000008888888800000000000000000000000000000000000000000000000000000000f8f8f8f8f0f0f0f0
  | 1, 1 => 0xff000000ff000000000000000000000000000000000000000000000000111133335555ffff000000000000000000000000000000000000000000000000ff00ffccff00ff00000000000000000000000000000000000000000000000000faeafaeafaaafaaa0000000000000000000000000000000000000000000000008f8f8f8f8f8f8f8f0000000000000000000000000000000000000000000000000033003300ff00ff0000000000000000000000000000000000000000000000000f0f3f3f0f0f3f3f000000000000000000000000000000000000000000000000050f050f050f050f
  | 1, 2 => 0xff00ffffff00ffff0000000000000000000000000000000000000000000000000000ff000000ff00000000000000000000000000000000000000000000000000ffaaff00ffaaff00000000000000000000000000000000000000000000000000fafaf0f0fafaf0f0000000000000000000000000000000000000000000000000ffaaff88ffaaff00000000000000000000000000000000000000000000000000ee00ee00aa00aa00000000000000000000000000000000000000000000000000eeccccccaa000000000000000000000000000000000000000000000000000000aaaaaaaa55555555
  | 1, 3 => 0xf0f00000f0f000000000000000000000000000000000000000000000000ccccffff0000ffff0000000000000000000000000000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000f0e0f0e0f0a0f0a0000000000000000000000000000000000000000000000000fafafaf0fafafaf0000000000000000000000000000000000000000000000000aaaaaaaaaaaaaa00000000000000000000000000000000000000000000000000f0f0f0f0fafafafa0000000000000000000000000000000000000000000000001111111155555555
  | 1, 4 => 0xffffffccffffff00000000000000000000000000000000000000000000000000faf8faf8faf0faf000000000000000000000000000000000000000000000000000ffffff00ffffff000000000000000000000000000000000000000000000000faf0f0f0faf0f0f0000000000000000000000000000000000000000000000000030303030f0f0f0f000000000000000000000000000000000000000000000000000055ff000055ff0000000000000000000000000000000000000000000000000707070707070707000000000000000000000000000000000000000000000000f0f3f0f3f0fff0ff
  | 1, 5 => 0xfffffcfcfffffcfc0000000000000000000000000000000000000000000000000f0f0f0f0f0f00000000000000000000000000000000000000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc0000000000000000000000000000000000000000000000003333333333333333000000000000000000000000000000000000000000000000fffffffff0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000faaaaaaafaaaaaaa
  | 1, 6 => 0xffffffffffccffcc000000000000000000000000000000000000000000000000000033330000ffff000000000000000000000000000000000000000000000000ffccccccffcccccc000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000fefefefefefefefe0000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000eecceecceecceecc
  | 1, 7 => 0xffff000000000000000000000000000000000000000000000000000000000000cccccccccccc0000000000000000000000000000000000000000000000000000fafafafafafa0000000000000000000000000000000000000000000000000000ccccccccffffffff00000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000f0f0f0f0f0f0ffff000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000cccccccccc00cc00
  | 1, 8 => 0xcccccccceeeeeeee000000000000000000000000000000000000000000000000ffffffffaaaa0000000000000000000000000000000000000000000000000000cccccccc88880000000000000000000000000000000000000000000000000000aaffaaffaaffaaff000000000000000000000000000000000000000000000000aaaa8888aaaa88880000000000000000000000000000000000000000000000000f000f000f000f00000000000000000000000000000000000000000000000000f0f0f0f0f0f00000000000000000000000000000000000000000000000000000ccccffffccccffff
  | 1, 9 => 0xf0000000f0000000000000000000000000000000000000000000000000000000fffff0f0ffff0000000000000000000000000000000000000000000000000000fffffcfcfffff0f0000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000cccccccc88888888000000000000000000000000000000000000000000000000ee00ee00ee00ee00
  | 1, 10 => 0xffeeffeeffaaffaa00000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000000ffff8888ffff0000000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000ffffffff33333333000000000000000000000000000000000000000000000000fcccfcccf000f000000000000000000000000000000000000000000000000000fc00fc00f000f0000000000000000000000000000000000000000000000000003333333333330000
  | 1, 11 => 0xffcc0000ffcc00000000000000000000000000000000000000000000000000004444444444444444000000000000000000000000000000000000000000000000fff0f0f0fff0f0f0000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000eeeecccceeeecccc000000000000000000000000000000000000000000000000ccffccff00ff00ff000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8
  | 1, 12 => 0xffffffff30303030000000000000000000000000000000000000000000000000ffffffff111111110000000000000000000000000000000000000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000cc00cc00cc00cc000000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000ffffffccffffffcc000000000000000000000000000000000000000000000000ccccccccc0c0c0c0000000000000000000000000000000000000000000000000ffccffccffccffcc
  | 1, 13 => 0x111133331111333300000000000000000000000000000000000000000000000030303030f0f0f0f000000000000000000000000000000000000000000000000000aa00aa00aa00aa000000000000000000000000000000000000000000000000fcfcf0f0fcfcf0f0000000000000000000000000000000000000000000000000ccccccccffffcccc000000000000000000000000000000000000000000000000333333333030303000000000000000000000000000000000000000000000000033003300ff00ff00000000000000000000000000000000000000000000000000fc00fc00fc00fc00
  | 1, 14 => 0xff00f000ff00f000000000000000000000000000000000000000000000000000faaafaaafaaafaaa0000000000000000000000000000000000000000000000000000000055555555000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000fffafffa00000000000000000000000000000000000000000000000000000000aaaaaaaa00000000
  | 1, 15 => 0xcc00cc00cc00cc000000000000000000000000000000000000000000000000eeeeeeee0000000000000000000000000000000000000000000000000000000000000000aaaaaaaa000000000000000000000000000000000000000000000000ffffffff00ff00ff00000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000fafafafaaaaaaaaa000000000000000000000000000000000000000000000000fffffffffafafafa000000000000000000000000000000000000000000000000fffff000fffff000
  | 2, 0 => 0xcccccccc0000cccc000000000000000000000000000000000000000000000000eeee0000aaaa00000000000000000000000000000000000000000000000000004444444400000000000000000000000000000000000000000000000000000000ffffff00ff00ff00000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000ffffaaaaffff000000000000000000000000000000000000000000000000000000000000cccccccc
  | 2, 1 => 0xff00ff00000000000000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000eeaaeeaaeeaaeeaa0000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000ffffffff030303030000000000000000000000000000000000000000000000000c0c0c0c00000000000000000000000000000000000000000000000000000000ccccccccccffccff000000000000000000000000000000000000000000000000ff00ff00fa00fa00
  | 2, 2 => 0xffffffffa0a0a0a0000000000000000000000000000000000000000000000000f0f0fffff0f0ffff000000000000000000000000000000000000000000000000ffcc0000ff000000000000000000000000000000000000000000000000000000ffffa0a0ffffa0a0000000000000000000000000000000000000000000000000fcf0fcf0f0f0f0f00000000000000000000000000000000000000000000000003333333322222222000000000000000000000000000000000000000000000000ccccccccc8c8c8c8000000000000000000000000000000000000000000000000fffffffff0f00000
  | 2, 3 => 0x33330000ffff000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000fffa0000fffa0000000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000ffffffaaffffffaa000000000000000000000000000000000000000000000000ffeeffeeffeeffee
  | 2, 4 => 0xf2f2f2f2f2f2f2f20000000000000000000000000000000000000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000ffffcc00ffff0000000000000000000000000000000000000000000000000000ffff0055ffff0055000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000ffffffff33330000000000000000000000000000000000000000000000000000ffffffffeeeeeeee
  | 2, 5 => 0x5555555500000000000000000000000000000000000000000000000000000000ffffc0c0ffffc0c0000000000000000000000000000000000000000000000000fffafffafffafffa000000000000000000000000000000000000000000000000ffff0000ff0000000000000000000000000000000000000000000000000000003333333300000000000000000000000000000000000000000000000000000000fffff0f0f0f0f0f0000000000000000000000000000000000000000000000000fffffff0fffffff0000000000000000000000000000000000000000000000000fffffffffcfcfcfc
  | 2, 6 => 0xfafafafa00000000000000000000000000000000000000000000000000000000fffffffffff0fff0000000000000000000000000000000000000000000000000ffffffffffffcccc00000000000000000000000000000000000000000000000022222222222222220000000000000000000000000000000000000000000000003300330033003300000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000fafafafaf0f0f0f0
  | 2, 7 => 0x55005500550055
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x48200660702018c0a0401980802003
  | 4, 0, 0 => 0x1c1006062000040b0307900005040183a8000e0200c1b40004012040320000a08018310000205864248000d0200c0c40002c32180620002e07020590000b0a850188000982c0812400024100608a0400a08078194000207034188000102c14064
  | 4, 0, 1 => 0x8162806200010060609d0000b130181880001094080040002c10240620400a2303031400020581006810110200c0c500008120810a000040b04081000050201822800058200c1f4
  | 5, 0, 0 => 0x5c16081c031400170102c6e0c5000081604030d94000b1a81818305000081208030d142033028200c0c6000081604078194000205818182d50002c1032188c14002f058200c0c500008162e060b5400020588c0c0c500008162c030314001c058200c0c50005c162b15031400020582052065
  | 5, 0, 1 => 0x11816450b03140002058100c115000081006220314000b0410c18305000fc16082103140002058100c415000081635060c540002059000c0c5000fc1018060f94040b0281024066000081606060f5400021e0100c0c500008163b030314000205818740c5000081608090e5400021282c08125
  | 5, 0, 2 => 0x2ca606060c14005204018183050002c0c0c288c14000b280181830500008102e060f94000b040189e4e50002c0c32168c140002059340c0c5000400a0403031400170d0202c0c500128164c030c94000205818184b50012816450303140002248100c0c50000816082403140002238d40c0c5
  | 5, 0, 3 => 0x81656060c54000223954183150002c100c188c14000205810b20650000816062c145400020594c1831500008160c18945400020594018315000100c0c1f0c1400022b8200c0c50002c0c56060c1400472a81818305000081632188b5400250e0200c0c5000081006060f940002059500c0c5
  | 5, 0, 4 => 0x81665320c9400022f02068315000081663060c54000205988280c50000816610303140002040181860500008165f030c947e25028200c0c6000400a08030c94005e040186830500008ba08030314000204018185c50000808062c0f94000202030623e500008b604030314000b2d01818305
  | 5, 0, 5 => 0x81672030314000229018182d500008b608030c94000b04018de71500040b60803031400702d8200c6f5000081006061b94006d059680c0c50002c1006061b14000204018186b500008d406061a54d01c058200c0c6000200c321f0c14000b0401818675000fc16040c031400020581818665
  | 5, 0, 6 => 0x2cf606060c14000b1d8181830500008160c188b54000205810f4065000081606061e54002f0582018315000087808030314001c058201831500008f0080303140017059dcec0c5000081604031d54000202820420c50005c2009020594000b030305a3050000816740303140002128d4e60c5
  | 5, 0, 7 => 0x8160409019400020581084065000400a08030314000b0a8100c0c50004c1604030314000205810241450002c0c323f0c14000b041201830500008920803031400023e8100c0c50005c0e080b031400022f018682d5000fc16080c0c940002058100c0c50005c040b0b07940002059f00c0c5
  | 5, 0, 8 => 0x816060620d400022f0200c1150005c0a040b04540002058200c325000200c0c1f0c14002f05818182d5000701606060b54000229818183e5000081682030314000228018183e50005c16080b07d4000b040490230500008120b0201940002058c8fc3150002d0006060c14000205810fe0c5
  | 5, 0, 9 => 0x81619030314000205a300c0c50000816060622d40002041cc188a5080081608078198006d04018183e5000081648060b54000205818188950000816060622140002058100c875000081604190c540002058200c8650000816850403140084059140c0c50002c0806190c1400023e8200c325
  | 5, 0, 10 => 0x81635030c94000205821220c50000816080b2414000504018188f500008160c3f0c54000205820188e501014080e030318000b0403c0c305000bc1006060f9404090582024066000701006060f940002058100c7e5000084a73060b54008d0401818305000081612408b54000b03030fc305
  | 5, 0, 11 => 0x2c0812030c1400970401818965002540a080303140422058200c0c60005c10160609d400020581018315000081694030314000b0a8200c0c5000092608030314000b04084183050005c16260b0314000212821240c50002c0806060c140010048200c0c5000081604189d54000b060c45a305
  | 5, 0, 12 => 0x81608190c540008060c47c3050000816062b0c94000b040186430500008169c030314000205818ac51500008169b03031400020581864515001c01608030e54000b32990183050102c0a2303031800020581024315000400a08060c540002058200c9a500008169903031400020582102985
  | 5, 0, 13 => 0x816a603031400100401818a55000081606190b540006060b47c3050000816a403031400020599018a35080141006320318000b0401818a25010241604040198001002818182d500008160606285400950e0200c0c50000816a0030314000b26018189f5000141006060454000b04278189d5
  | 5, 0, 14 => 0x2058200c1d50000816a8040194040b028201e0660000816042c0c5400020598c0c0c50029c0a080303140017048202c1150000816040326140002058480c51500008160801831400020581818515
  | 6, 0, 0 => 0x2bc040b0401818c000b80808162c0f9800170102c08062c30002e020585818ae6000081606060b55ac000102c1006150c98000205ab010061930002e0202031563e6000092e0b0401818c000b808b6040b0318000205858183116b0002e0205810183160005c04940b0307cc000102c0c0c558b5800170102d2806063001540b5485818306
  | 6, 0, 1 => 0x5c04b40b0307cc000102c1006062d9800025a82c10060630002e10028202c3260005cbc080b0d060c000102c081603031800001782c10060628002e0205ad00c0c60000816080303146c00010200cb3060f98000205ac80806063000001c058200c0c5000081006062c47cc000102c100c1a0c58001705821600c183000040b040000c0c6
  | 6, 0, 2 => 0x5c040b5f0305ac000b80816bd0b03180017010202c0c303000040b040842c0c60005c040b2f85864c000102c0a040303180002059940c0c16b000000205818182d500008160403030a2c000102d780c16aed80002058100c0c1830000408030307cbb60000816085481864c000b80816ba0b031800b90102c10b80630016e02058200c0c6
  | 6, 0, 3 => 0x816080331018c00012541016030318001701178103455b000040b0401818c36000081608031cc64c000102c10060630980002058218206063000040b04018189860000816086001818c00058209806060c1800025f82c0806063000042504018183e60002c1016190c176c00058101006060c180002058200c0c47b000040b02018ec0c6
  | 6, 0, 4 => 0x9960b0205818c000102c0808060c5800020582064ab5db001940205ad02c0c60000816940401818c000102c08120b01980002058200c0c34b0002005040580c0c60005c040b0232418c00010202406060f980002058219006063000040b0431c18bb60002c10060616060c0063008160862831800840102c080606300016084f01818306
  | 6, 0, 5 => 0x816d20401818c00380081604030318003f0581410060630002e0204058186b60005c046a0b030d2c000102da20803031800170102c100c6830000002059ec0c0c50000816086781818c000b8202c321f0c1800ce0102c10060630019a02058200c0c60000816082603062c000b82c10160619d8000205b3010161930002e0b0401864306
  | 6, 0, 6 => 0x351b20b0405818c000102c100606361800aa0102c1006063000000205820900c500009ae0b0401818c000b808b6080b0c980017058202c6f38b0002e020582064316000081006060f9acc000b840b6080b031800173816c101637b00000d5058200c0c5003517e0b0b0305ac006980816040b031800022382c0c0c16b000040b04030b0316
  | 6, 0, 7 => 0x9be0b0401818c000102c10061937980017011e01016063000040b040580c32600009ba0b0401818c006e0081006060f9800024a82c10060630007e02059680c0c6001c016080b018dec000102c10db03031800080b018183e1830002e0b0b0305a3060005c040b3a05818c001f8081608060c58000205821b406063000000205818647e5
  | 6, 0, 8 => 0x2c1006060c1cac000b809c0537203180002058200c0c71b0002e021e0202c0c60005c5e0b0403156c000102c0a08030c9800000102d0006062801c402058200c0c60005c04085c0307cc000802c0a0803031800170102c08e10630002e1c0582018ab60005c040b1a81818c000102c1006190c180010058200c0c18300004e0058200c0c6
  | 6, 0, 9 => 0x5c040b04031d4c00080081608060c580017059ec2c0c183000040b0403062e96000000425041cc18a000b82c7616060c1800000102c101240a80004080b030623e600008b6080b01818c000102dd00803031800170102c18ab16b0002ee004390183060039c040b0403156c007300816080b0318003f3802c1006063000040b03030682d6
  | 6, 0, 10 => 0x5c04085f0307cc000b8081608063bd80002328200c0c1f30002e022f058682d6000000408030307ca006302c1016060c180002042f0183e5db00004cb058202c326000081608060c5dcc000b80816b0060b58000204018183e76b000040b760200c0c60000816080781818c000b8081608648c98000205821d60c5db0017202058100c0c6
  | 6, 0, 11 => 0x318040b0403156c007980816040303180002058206a060630000002058100c3250034c040b0405864c007902c1006060c18000205858642d5db000040b02018182d600009e20b0205818c005c82c1016780c18001705858647e183000e002058200c3260005c04490405818c00081c0160803031800021282c10120630001608030307c306
  | 6, 0, 12 => 0x5c040b030c85ac00058202c0c182ed8000b043d00c0c1830002e02058c8fcab60000816530b03176c000102c2c0c28aed800020582018311f3000040b2805818bb600008160803030e2c000102cb6080303180002058200c0c20b000000b0403062305001c0045b0401818c000b808160409059800170801410160630081605040480c0c7
  | 6, 0, 13 => 0x5c040b03030a2c007c00816080303180002238200c0c1f30007e0205818182d60000816040303176c000102dee08030318000205bd81006063000040b04018181160035016080303060c000102c2c56062ed800170102416040b30002e020b0c85a3e6000081604032cc18c00790081608060c580002239542c0c5db000040b0401818f56
  | 6, 0, 14 => 0x3e4040b0401818c000b80816062b0318001704058183e1830002e2f05858182d60005c04472a81818c000000816086283140017058200c0c183000040b04018183960005c380b0b0305ac000102c10f4060c5800170114c2c0c1f30002e020b030a23e60002c10067203060c00058200c18060c180017011402c0c1f30000425058100c0c6
  | 6, 0, 15 => 0x40040b030305ac000b8081016623b58004a0102c100c18b0000408030307cff60002c10550303060c007980816087f031800020581024060630000416030305a3e600008160803031fac00058141006061bd80017010100c0c1f3001f8020405818fb60000816fa0401818c00058200c0c378c18001701058ac0c1f30017202058200c326
  | 6, 1, 0 => 0x5c040b0b03110c0000128164c0303140002058200c0c28b000040b04018183060005c040b020c956c008080816080303182002058200c640638012e0b0401818306003cc040b0401864c000ba1016450b03180002058200c3216b000000205818187e50002c1016060c200c000b808b6080b031800021982c10060630002e0b0205864306
  | 6, 1, 1 => 0x3c8040b030305ac00010941608030c9800b90102c2cf016b000160860018183060000816082401818c00420081608030318000205818182d1f3000040b041640c0c6000081608030c976c00820081608030318000005818182d182801b802058100c0c60000816080303206c000102c100606409800000102c100f032800040b028200c0c6
  | 6, 1, 2 => 0x5c05080205818c000102cca0403031800000102c0806062800040b022f018bb6000fc0408030307cc000b82c2c0c3f0c18000205bd00c0c16b000040b5a0580c0c60005c16088383060c003800816080303180002058202406193000000205830622d50000816088301818c000102c1006194158000b04018c80c183000040b021140c0c6
  | 6, 1, 3 => 0x5c040b030305ac000102c110d03031800aa058200c0c1830002e0205830fcab60005c040b5983218c1701014080e0b031c0017178202c0c1f3000040b03390182d60000816060c0305ac000b82c10bc060c1800170e0202c0c1f30021602058202c0c60002c10fe0b03060c000102c0c0c16c29800023e82c10060630002e0205822120c6
  | 6, 1, 4 => 0x5c160c558b460c000102cc40403031800022382c0806063000040b0b0305b006000081608030309cc00550081608060c580002058200c0c4b300000020597c0c0c500370040b0401864c0000008160409019401100102c10060630014e02058200c0c60000020050401818a000138016530303180002878202c0c8730002e0504058188f6
  | 6, 1, 5 => 0x816650401864c00000081608030c9400020582178325db0081605020200c0c700000e00b04018dea00000200c0c1f0c1400170102c0911063000040b040181875600000040b3299018a000b82c0816060c180002058200c0c4fb0002e09058202c6f60005c20090405818c006a2fc16040b0318000b0401818311830017202058200c0c6
  | 6, 1, 6 => 0x5c20050403156c006a8081608030318000b04018e60c1830000425058200c0c60000a2a0b0401818c00058200c0c18275801140102c1006063000040b3d8200c0c60000817130401818c000ba5c101606259800174a81410160630002e020581018ab60002c10061503060c000b8081606191f9800170102c100c893000040b041e80c0c6
  | 6, 1, 7 => 0xa300b0401818c00550081606060b5800170102c2c5628b0022e02058200c0c60002d98080b03060c000b8081616191458000b0403156305db0002e0205af0182d60000816080901818c000102c1006191f9800d45f82c1016193000040b7f058182d60000816042601818c00250081006060f9800022382c1006193000040b8b0200c0c6
  | 6, 1, 8 => 0x81606060c45ac000b8081608192ad8001704031563e183000040b04018191d60000816088e01818c000bc6c16040b0318000205a001006063000040b044680c0c60005c040b0201864c0001024160803031800170102c2c561930023202058200c0c60005c04472a85864c000b82c1016190c180002350200c0c1f3000040803030de3e6
  | 6, 1, 9 => 0x816082601864c000102c0808030c98000b0401818811830024202058202c0c60005d2a1c0405818c000102c8a0803031800100102c08060630024002058200c0c60002c1006060c860c000b82c98160627d8000b028200c0c183000040b04018191f60005c0a080b03022c005500816a90b0c980002058200c328f3000040b02018280c6
  | 6, 1, 10 => 0x16040303060a0000008fa0803031400022382caa060630002e0b0405818a260b808120b020202ce003802c1006060c1800170102c0c0c3f3000040b328200c0c600000040b0401818a000b8400a16060b580002058200c0c43b000040b04030643160005c04470705818c00010200cc4060f98000205814100c18b0002e020585818a16
  | 6, 1, 11 => 0x8bc0b0401868c3f01094160803031c00100102c1006193000040b044880c0c60000816620401818c000111c16080303180017080202c0c52b0000002058100c5850005c040b0b0c85ac00000081604060c5400170b0305a3e183000000205a500c0c50000816cc0b0305ac000102c18ab16aed800700102c100c18b0002e4a26058183e6
  | 6, 1, 12 => 0x81606062045ac000102c10060647980000058200c321828024802058200c0c600008165f0b03176c000bc8c16080b0318000205818183216b0001608030305a3060017816080303060c000102c0a06060b580002058202cf07ab000040b02018300c60005c16080b03060c000b80816b23b031800170102c2c0c28b000040b04018187e6
  | 6, 1, 13 => 0x816080b0ca00c000102c1012060c580002058101012033000040b04018190c60000816040319018c000000816350303140002058200c0c52b0002e0205810b0ab60000816040401818c00380081606060b5800000102c103218a800040b04030622d6001287e0b0401818c000102c100c189d58040b028200c64063800040b0205819006
  | 6, 1, 14 => 0x816650403062c00000081608060c5401280102c10060630002e0205c9c18ab600000040b0315818a000102c0c0c588b580002058200c6419300000020581818515000084a0b041cc18c000102c0806060c58000205818182d933000000205818642d500008160803031dcc000800816080303180002058200c0c92b0015402058100c0c6
  | 6, 1, 15 => 0x170102c2c5828b001b80205818182d60005c0816060f860c000102c080c55aed80002058200c3218b000040b030305b1d6010cc16050401818e000b8400a040b03180002058480c0c16b0025202058200c0c6
  | 7, 0, 0 => 0x205818182d50005c16080b3901830700000040b020580c0c60005df002058202c0c70005c044704058183e70005c040b0205818bb70005c040b7b8202c0c70005c0447058200c0c70005c040b7b0202c0c7003502e0b0405818307001c0040b040580c0c70005c040b02059660c70005c040b0405818f57003c82e020582018ab7000019402058202c0c60005c16087a05818307
  | 7, 0, 1 => 0x5c200205858182d7000002e0205821e8b160005c94020582018ab70005c04080b0307cff700000040b04018c80c60005c16082a858183070005c160504058186f70005c040b0b018182d7000002e0205820192b60005c040b7d0202c0c70005c16080b030de307002e42e02058202c327003e42e02058202c0c70005e5402058202c0c70005c040b043d018ab70000816080b03068bb7
  | 7, 0, 2 => 0x5c040b04058185170005c040b280202c0c70005c040b040581830700000040b043f82c0c60005c052c058202c0c70005e0202058202c0c70005d2e0b04058183070005c040b0415418ab7002e4040b040580c0c70000816040405818bb70005de602058202c3270035004bf058202c0c70005c040b04058642d7000002e0205858187e60005c045e058202c3270005c040b0401818347
  | 7, 0, 3 => 0x5c040b041300c0c70005c040b0405864bb70005e0802058202c0c70000816080b018182d70005c040b020200c0c7000002e0b0b0305a306003702e02058102c0c70005c040b04059663270005c040b04058190e7000015402058200c0c60000816080b030b0bb70005c040b04058190270005c052d058102c0c7000002e0205821780c60005c040b028202c0c7000002e4a059302c0c6
  | 7, 0, 4 => 0x5ce002058202c0c70005e5c02058202c0c700000040b0401818316000002e0205831562d60005c04080b030b03e70005c040b04018185870005c040b021142c0c7003c82e0205858182d70000004e0058200c0c60005c16086005818307002e42e0205821920c7003cc040b040580c0c70005d0802058202c0c700000040b040580c3260005c040404058183e70005c040b0b0305a3e7
  | 7, 0, 5 => 0x2e024a8202c0c6000081608090580c0c70005c04080b018183e70005c040b044342c0c7002a82e0b040581830700000040b04018540c60005c040b0b390182d70005c940205858182d70005c040b04058652f700000000204018183e500040040b0405818bb7003c97202058202c0c7000002e02058102c0c60005c7e02058200c0c70005c040b7a058182d7003f02e02058202c0c7
  | 7, 0, 6 => 0x5c040b988202c0c70005c0447058102c0c70000016080b03060bb6002a82e020582018ab7000002e0205cc02c0c60005c040b0405818967000002e020597c2c0c6003702e02058202c32700000040b042a40c0c60005dc00b0405818307004402e02058202c0c7000002e10028202c0c60005c200204058183e70005c04e00594c2c0c70005c2002058200c0c70005c040b0b030de2d7
  | 7, 0, 7 => 0x2e70058202c6f60005c040b04018183e7000002e0205821b60c6000002e080b0307c30600000040b660202c0c6000002e0b040181830600000040b0403156bb6003182e02058202c0c7004c82e02058202c0c70005c040b04058189f70005c04e00582018ab70005c5e02058202c0c70005c041c058202c0c700000040b04018e60c60000816080b0307cbb7002e42e02058202c0c7
  | 7, 0, 8 => 0x5c0425058202c0c700000040b0401818306000081665040580c0c700000040b040580c0c60005e2802058202c0c70005c040b3d8202c0c70005c040b5602018ab70005c16085485818307000002e022d8202c0c6000002e0205820183160005c040b0b0305ac270005c16080b0a8183070005de602058202c0c70000816087a05818bb7000002e02058202c3260b8081605020202c0c8
  | 7, 0, 9 => 0x5e3202058202c0c70005c046a04058183e70005c04080b030de3e70005c0518058202c0c7002a82e0205858182d70045c2e02058202c0c700000040b04018188160005c040b040482c0c70005c040b04058647e70b8081605040580c0c80005c040b021302c0c70005c940204058183e700000040b04018183260005c0447058202c3270005c040b8b0202c0c700000040b028200c0c6
  | 7, 0, 10 => 0x5c040b0282018ab70005c040b041302c3270005c040b020202c3270005c040b0405818ad70005c040b228202c0c70005c2002058102c0c7004802e02058202c0c7000002e0205818182d60005c16080b030643070005c160504058183070005c040b020580c0c70005c040b04058651e7000000002058100c0c500000e002058200c0c60005c0409058202c0c70005c04082a858183e7
  | 7, 0, 11 => 0x2058200c325003c82e02058102c0c700000040b04018182d60005c040b04031573370005c040b02058183e7000002e0b02058183060005c0447059542c0c70005ce00b04058183070005c040b328202c0c7000002e02058202c0c60005c040b040589e0c70005c04080b0307c697000017202058200c0c60005c040b04031570370005c040b0403064ab70005c04080b310183e7
  | 7, 0, 12 => 0x5c16080b030604e700000040b0401818bb60005c045e058202c3470005c16080b030609670005c2002058202c3270005c0447058202c0c700000040b0401818b160005c040b023d02c0c70005c040b04031573470005c04e0058200c0c7000002e02058102c5860005c040b040580c327000002e020581018ab6000002e0205a502c0c6002a82e02058200c0c70005ce0020582018ab7
  | 7, 0, 13 => 0x2e020582064ab60005c16080b031623070005c040b04031562d70005c040b04058643e70005c040b04058191e70005c04d9058202c0c70005c040b560200c0c7000002e0b04058643060005c040b0b030642d70005c16080b0305a3070005cbc0b040581830700000040b040480c0c60005c040b02858182d7004d42e02058202c0c70005c040b02059c80c7000000425058200c0c6
  | 7, 0, 14 => 0x5cbc1c058202c0c7002a82e02058102c0c70005c04080b0307c30700000040b328200c0c6000000002058200c0c500000040b042f018bb60000816087a0580c0c70005c040b04058190c70005c2002028202c0c70005c040b04059c8327004d82e02058202c0c70005c040b0405818a5700001b802058200c0c60005c040b020202c0c70005ce00205858182d70005c16080b03060bb7
  | 7, 0, 15 => 0x2e020582018ab600000040b04018183460005c040b0b0305abb7000002e0205858ac0c6000002e0b04058183060005c040b0b031622d7000002e02058581851600001a8bf058202c0c60005c040b0b0305b267000000447058200c0c6000002e0205858642d60005c040b04018183270005c040b024dc2c0c70005c2002058202c0c7003702e0b04058183070005c040b028200c0c7
  | 7, 1, 0 => 0x5c040b02058185170005c04b5058202c0c70005c0497058202c0c70000816ac660202c0c7003702e0205858182d7003e42e02058102c0c700000040b040181858600000040b041300c0c600000040b020200c0c60005c040b0b0305b1d70005c040b04058193870005c20022f0202c0c7002a82e02058202c32700001540205aa42c0c60005e5202058202c0c7004a02e02058202c0c7
  | 7, 1, 1 => 0x2e02058102c3260005c040b02058182d70005c040b028202c32700000000205820183150005c04dd058202c0c7000002e0205858647e6002a82e02058202c0c70005ce002058102c0c7000002002058200c0c60005c040b04058188f70005c040b028102c0c700009c0cb058202c0c7000002e0205858182d6
  | 8, 0, 0 => 0x5c040b0405818cdc0b80816080b031c0002058202c0606305c040b0405818bb70b80816080b2cc18e170102c1016062c5c2ef30102c10160638002e02058202c3260b80816080b0305aeb90b80816080b031c00170102c081606305ce002058202c0c70b80816080b03064e17012fc16080b031c2e0205814101606385c040b0405818307
  | 8, 0, 1 => 0x5505c040b0405818e000b8081616060b5800170102c100c55b0002e0b04058183060b840040b0405818e170102c101603031c00000102c100606285c040b04058185870b80816082605818e170102c08080b031c2e02058202c0c1a385c0447058202c0c7
  | 9, 0, 0 => 0x2e02058202c0c6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 31
  | 4 => 49
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
  | 0, 0 => 0xe000003e000000000000000000000000000000000000000000000000000000000387060000000000000000000000000000000000000000000000000000000000e000003e000000000000000000000000000000000000000000000000000000001c3879c1f3e7ff000000000000000000000000000000000000000000000000000387060000000000000000000000000000000000000000000000000000000000ffc0003ffc0000000000000000000000000000000000000000000000000000000038000003e00000000000000000000000000000000000000000000000000000000771c000077f
  | 0, 1 => 0x71c000077f000000000000000000000000000000000000000000000000000038000003e000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000071c000077f00000000000000000000000000000000000000000000000000e03f803e03f80000000000000000000000000000000000000000000000000000000071c000077f00000000000000000000000000000000000000000000000000e00071fe00077f000000000000000000000000000000000000000000000000001c387801f3e7e0
  | 0, 2 => 0xffffffc00000000000000000000000000000000000000000000000000000000003870639cb979c000000000000000000000000000000000000000000000000001f800001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffc0003ffc000000000000000000000000000000000000000000000000000000038777c000077f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff803ffff800
  | 0, 3 => 0x3f8e0003f88000000000000000000000000000000000000000000000000000e3c7f63e0c1f60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e000003e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e0007ffe0007ff000000000000000000000000000000000000000000000000001c000001f000000000000000000000000000000000000000000000000000000003800000000000
  | 0, 4 => 0x1fff8001fff800000000000000000000000000000000000000000000000000001c0787c1f0181f00000000000000000000000000000000000000000000000000e3bf863e03f8000000000000000000000000000000000000000000000000000003b8f9c003ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e000003e000000000000000000000000000000000000000000000000000000000387060000000000000000000000000000000000000000000000000000000000fc78883ffff880
  | 0, 5 => 0xffc0003ffc0000000000000000000000000000000000000000000000000000000387060000000000000000000000000000000000000000000000000000000000e3c787fe0c181f000000000000000000000000000000000000000000000000001c387801f00760000000000000000000000000000000000000000000000000001c000001f3879c0000000000000000000000000000000000000000000000000003800039c8000000000000000000000000000000000000000000000000000000ffff8e3ffff88000000000000000000000000000000000000000000000000000e04081fe0c181f
  | 0, 6 => 0xe04081c7c78f8300000000000000000000000000000000000000000000000000000071c0000760000000000000000000000000000000000000000000000000000038000003e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e387063e00000000000000000000000000000000000000000000000000000000ffff8e3ffff88000000000000000000000000000000000000000000000000000fc78f9ffffffff00000000000000000000000000000000000000000000000000003fffc003ffff
  | 0, 7 => 0xffc7063ffc0000000000000000000000000000000000000000000000000000001fc07fc1fc07ff00000000000000000000000000000000000000000000000000e3c787fe00180000000000000000000000000000000000000000000000000000e038003e03e000000000000000000000000000000000000000000000000000001c3879c1f3e7ff00000000000000000000000000000000000000000000000000e3c787fe0c181f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003b8f9f9c86863
  | 0, 8 => 0xfc3ff83ff3ffe000000000000000000000000000000000000000000000000000fff879c0000000000000000000000000000000000000000000000000000000001c000001f00000000000000000000000000000000000000000000000000000001fc07fc1fc07ff000000000000000000000000000000000000000000000000000387060000000000000000000000000000000000000000000000000000000000038071c000077f0000000000000000000000000000000000000000000000000000007000000760000000000000000000000000000000000000000000000000001c3879c003e000
  | 0, 9 => 0x3fffc003ffff00000000000000000000000000000000000000000000000000000071c000077f000000000000000000000000000000000000000000000000001c7879c1f7e7e3000000000000000000000000000000000000000000000000001c000001f0000000000000000000000000000000000000000000000000000000e387863e00180000000000000000000000000000000000000000000000000000fff8783fffe7e000000000000000000000000000000000000000000000000000003f003803f0000000000000000000000000000000000000000000000000000003870600000000
  | 0, 10 => 0xe03f8e3e03f88000000000000000000000000000000000000000000000000000e3c7f7fe0c1f7f000000000000000000000000000000000000000000000000000038000003e000000000000000000000000000000000000000000000000000001c387801f387800000000000000000000000000000000000000000000000000000380001c3e78000000000000000000000000000000000000000000000000000e03f803e03f80000000000000000000000000000000000000000000000000000e3c7863e0c1800000000000000000000000000000000000000000000000000001c387801f3e7e0
  | 0, 11 => 0x1c38780003e00000000000000000000000000000000000000000000000000000e03ff1fe03ff7f00000000000000000000000000000000000000000000000000e007003e000000000000000000000000000000000000000000000000000000001fc07fc1fc07ff00000000000000000000000000000000000000000000000000e000003e000000000000000000000000000000000000000000000000000000001c000001f0000000000000000000000000000000000000000000000000000000038776000007600000000000000000000000000000000000000000000000000000007000000760
  | 0, 12 => 0x3fffc003ffff00000000000000000000000000000000000000000000000000e3c787fe0c181f000000000000000000000000000000000000000000000000001fbf7e01f3e7e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c3879c1f3e7ff000000000000000000000000000000000000000000000000001fbf7fc1f3e7ff000000000000000000000000000000000000000000000000001c387801f3e7fc000000000000000000000000000000000000000000000000001fc071c1fc077f
  | 0, 13 => 0x1fc07fc1fc07ff00000000000000000000000000000000000000000000000000ffc0003ffc000000000000000000000000000000000000000000000000000000003fffc003ffff000000000000000000000000000000000000000000000000001fffffc1ffffff000000000000000000000000000000000000000000000000001ff87fc1ffe7ff000000000000000000000000000000000000000000000000001c007801f007e000000000000000000000000000000000000000000000000000e387063e000000
  | 0, 14 => 0x1f800039f800000000000000000000000000000000000000000000000000000000000001c3879c00000000000000000000000000000000000000000000000000000071c000077f00000000000000000000000000000000000000000000000000003871c1c3e7ff0000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000001c380001f3e00000000000000000000000000000000000000000000000000000003f8e0003f88000000000000000000000000000000000000000000000000000ffc071fffc077f
  | 0, 15 => 0x3800000000000000000000000000000000000000000000000000000000000001c380801f3e08000000000000000000000000000000000000000000000000000e03f803e03f800000000000000000000000000000000000000000000000000001c387801f3e000000000000000000000000000000000000000000000000000001c387801f3e7fc000000000000000000000000000000000000000000000000000000700000076000000000000000000000000000000000000000000000000000e3c787fe0c181f00000000000000000000000000000000000000000000000000e007003e039000
  | 1, 0 => 0x700000076000000000000000000000000000000000000000000000000000ffff8e3ffff880000000000000000000000000000000000000000000000000000387060000000000000000000000000000000000000000000000000000000000fff879ffffe7ff00000000000000000000000000000000000000000000000000e3fffffe0fffff000000000000000000000000000000000000000000000000001c3878000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c387801f3e7e0
  | 1, 1 => 0x7fc00007ff00000000000000000000000000000000000000000000000000fc78f9ffffffff00000000000000000000000000000000000000000000000000e03f863e03f80000000000000000000000000000000000000000000000000000003871c003e77f00000000000000000000000000000000000000000000000000e3c787fe0c1f1f000000000000000000000000000000000000000000000000001c4079c1fc07ff00000000000000000000000000000000000000000000000000e3fffffe0c787f00000000000000000000000000000000000000000000000000e3c787fe0c181f
  | 1, 2 => 0xe03ffffe03ffff00000000000000000000000000000000000000000000000000003f800003f80000000000000000000000000000000000000000000000000000e03f803e03f800000000000000000000000000000000000000000000000000001c387801f3e7e000000000000000000000000000000000000000000000000000e03f803e03f8000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000387060000000000000000000000000000000000000000000000000000000000000071fffff880
  | 1, 3 => 0x787c000181f0000000000000000000000000000000000000000000000000003bfffc003ffff0000000000000000000000000000000000000000000000000000070600000000000000000000000000000000000000000000000000000000000038700003e760000000000000000000000000000000000000000000000000001c387801f3e7e000000000000000000000000000000000000000000000000000000071c0000000000000000000000000000000000000000000000000000000001c387801f3e7ff00000000000000000000000000000000000000000000000000fc78883ffff880
  | 1, 4 => 0xffff863ffff800000000000000000000000000000000000000000000000000001c387801f3e7e0000000000000000000000000000000000000000000000000001fffffc1ffffff000000000000000000000000000000000000000000000000001c387801f3e7e000000000000000000000000000000000000000000000000000e04081fe0c181f00000000000000000000000000000000000000000000000000003fffc003ffff00000000000000000000000000000000000000000000000000e3c787fe0c1803000000000000000000000000000000000000000000000000001c7879c1ffe7ff
  | 1, 5 => 0xffff7e3ffff7fc00000000000000000000000000000000000000000000000000e3c787fe0c000000000000000000000000000000000000000000000000000000e3c0003e0c0000000000000000000000000000000000000000000000000000001fbf7e39fbf7fc00000000000000000000000000000000000000000000000000fc78f9c634686300000000000000000000000000000000000000000000000000ffffffc1f3e7e0000000000000000000000000000000000000000000000000001c38780000000000000000000000000000000000000000000000000000000000000071c000077f
  | 1, 6 => 0xffffffffcbff9c000000000000000000000000000000000000000000000000000038f9c003ffff00000000000000000000000000000000000000000000000000e387063fcb979c000000000000000000000000000000000000000000000000001c000001f387800000000000000000000000000000000000000000000000000000000001c38780000000000000000000000000000000000000000000000000001fbf7ff9fbf7ff000000000000000000000000000000000000000000000000000000000000071c0000000000000000000000000000000000000000000000000003870639cb979c
  | 1, 7 => 0xffc000000000000000000000000000000000000000000000000000000000000003870639c80000000000000000000000000000000000000000000000000000001c3879c1f00000000000000000000000000000000000000000000000000000000387063fffffff000000000000000000000000000000000000000000000000000000003fffffff000000000000000000000000000000000000000000000000001c387801f3ffff00000000000000000000000000000000000000000000000000ffffffc000077f0000000000000000000000000000000000000000000000000003870638039000
  | 1, 8 => 0x3870639cb97ff00000000000000000000000000000000000000000000000000ffffffc00000000000000000000000000000000000000000000000000000000003870600000000000000000000000000000000000000000000000000000000001fc07fc1fc07ff000000000000000000000000000000000000000000000000000000000000071c00000000000000000000000000000000000000000000000000e007803e001800000000000000000000000000000000000000000000000000001c387801f000000000000000000000000000000000000000000000000000000003bffff9cbffff
  | 1, 9 => 0xfff8783ffc000000000000000000000000000000000000000000000000000000ffff7e3fffe7e0000000000000000000000000000000000000000000000000001fbf7e0000000000000000000000000000000000000000000000000000000000e3bf860000000000000000000000000000000000000000000000000000000000ffc70600000000000000000000000000000000000000000000000000000000000387060000071c0000000000000000000000000000000000000000000000000000070038039000
  | 1, 10 => 0xe3bff7fe03ff7f000000000000000000000000000000000000000000000000001fc00001fc000000000000000000000000000000000000000000000000000000ffc0003ffc000000000000000000000000000000000000000000000000000000fffffffffc000000000000000000000000000000000000000000000000000000ffffffc63468630000000000000000000000000000000000000000000000000003bf060003e00000000000000000000000000000000000000000000000000000003f000003e00000000000000000000000000000000000000000000000000000fc78f9c6340000
  | 1, 11 => 0xe380003fc800000000000000000000000000000000000000000000000000000003870639cb908000000000000000000000000000000000000000000000000000fc38783ff3e7e000000000000000000000000000000000000000000000000000fffffff9cb979c0000000000000000000000000000000000000000000000000003870639cb979c000000000000000000000000000000000000000000000000001fc77fc1fc07ff00000000000000000000000000000000000000000000000000ffc00000000000000000000000000000000000000000000000000000000000000000700000077c
  | 1, 12 => 0xffffffc030606000000000000000000000000000000000000000000000000000ffffffc6346800000000000000000000000000000000000000000000000000000038780003e7e00000000000000000000000000000000000000000000000000000070038039000000000000000000000000000000000000000000000000000001c4079c034006300000000000000000000000000000000000000000000000000ffff863fffff9c0000000000000000000000000000000000000000000000000003870601c3878000000000000000000000000000000000000000000000000000e3bf863fcbff9c
  | 1, 13 => 0xfc78f9c6346863000000000000000000000000000000000000000000000000001c387801f3e7e000000000000000000000000000000000000000000000000000000071c000077f000000000000000000000000000000000000000000000000001fb87839fbe7e0000000000000000000000000000000000000000000000000000387063fff979c00000000000000000000000000000000000000000000000000fc78f9c030606000000000000000000000000000000000000000000000000000e038803e03f80000000000000000000000000000000000000000000000000000003f003803f000
  | 1, 14 => 0xe038003e03e00000000000000000000000000000000000000000000000000000003871c003e77f000000000000000000000000000000000000000000000000000000003ffff88000000000000000000000000000000000000000000000000000038777f9cb97ff00000000000000000000000000000000000000000000000000ffc7063fff979c00000000000000000000000000000000000000000000000000fffffffe03f80000000000000000000000000000000000000000000000000000fc3ff9c000000000000000000000000000000000000000000000000000000000000071c0000000
  | 1, 15 => 0x3800601c8079c00000000000000000000000000000000000000000000000000038777c0000000000000000000000000000000000000000000000000000000000000000000077f00000000000000000000000000000000000000000000000000ffffffc1fc07ff000000000000000000000000000000000000000000000000001fc07fc0000000000000000000000000000000000000000000000000000000001c3879c000077f00000000000000000000000000000000000000000000000000ffffffc1f3e7ff00000000000000000000000000000000000000000000000000fff8003fffe000
  | 2, 0 => 0x387060003979c0000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000000387060000000000000000000000000000000000000000000000000000000000ffff803e03f800000000000000000000000000000000000000000000000000001c387800306060000000000000000000000000000000000000000000000000000000003ffc000000000000000000000000000000000000000000000000000000ffc071fffc00000000000000000000000000000000000000000000000000000000000039cb979c
  | 2, 1 => 0xe03f80000000000000000000000000000000000000000000000000000000000000000001fc07ff00000000000000000000000000000000000000000000000000000771f803977f00000000000000000000000000000000000000000000000000e04081c604080300000000000000000000000000000000000000000000000000ffffffc604080300000000000000000000000000000000000000000000000000038706000000000000000000000000000000000000000000000000000000000003870639ff97ff00000000000000000000000000000000000000000000000000e03f800003e000
  | 2, 2 => 0xffffffc0000760000000000000000000000000000000000000000000000000001c3fffc1f3ffff00000000000000000000000000000000000000000000000000e380003e00000000000000000000000000000000000000000000000000000000ffc0703ffc0760000000000000000000000000000000000000000000000000001c3f7801f3e7e000000000000000000000000000000000000000000000000000fc78f9c00000630000000000000000000000000000000000000000000000000003870601c3879c00000000000000000000000000000000000000000000000000ffffffc1f00000
  | 2, 3 => 0xfc40003ffc000000000000000000000000000000000000000000000000000000ffc0003ffc000000000000000000000000000000000000000000000000000000000001c000001f000000000000000000000000000000000000000000000000001c380001f3e00000000000000000000000000000000000000000000000000000fc00003ff000000000000000000000000000000000000000000000000000000000007001c387e000000000000000000000000000000000000000000000000000fffff1ffffff7f00000000000000000000000000000000000000000000000000e3bff7ffcbffff
  | 2, 4 => 0x1c3879c1f3e7e300000000000000000000000000000000000000000000000000e3c787c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffc7003ffc000000000000000000000000000000000000000000000000000000ffc00e3ffc0080000000000000000000000000000000000000000000000000001c007001f0076000000000000000000000000000000000000000000000000000ffffffc634000000000000000000000000000000000000000000000000000000fffffff9cb97ff
  | 2, 5 => 0xffff8e0000000000000000000000000000000000000000000000000000000000ffc0003fff878000000000000000000000000000000000000000000000000000fc3ff9fff3ffff00000000000000000000000000000000000000000000000000ffc0003e00000000000000000000000000000000000000000000000000000000fc78f9c000000000000000000000000000000000000000000000000000000000fff87801f3e7e000000000000000000000000000000000000000000000000000fffff83fffffe000000000000000000000000000000000000000000000000000fffffff9fbf7fc
  | 2, 6 => 0x1c3879c000000000000000000000000000000000000000000000000000000000fffffffff3ffe000000000000000000000000000000000000000000000000000ffffffffff979c00000000000000000000000000000000000000000000000000000071c000006300000000000000000000000000000000000000000000000000e038800600680000000000000000000000000000000000000000000000000000fffffffffff800000000000000000000000000000000000000000000000000001f800039f80000000000000000000000000000000000000000000000000000001c3879c1f3e7e0
  | 2, 7 => 0x1fc00e01fc0080
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf6ede1befdfb6f000000000000000000000000000000000000000000000000004b971e6102049000000000000000000000000000000000000000000000000000f224003ea1400000000000000000000000000000000000000000000000000000bdfbffdfffffff000000000000000000000000000000000000000000000000006fdfffeb5ebfff00000000000000000000000000000000000000000000000000ffe4413ffd424a00000000000000000000000000000000000000000000000000b9bbbedfa3fdb50000000000000000000000000000000000000000000000000066dff3ea5ebf7f
  | 0, 1 => 0x2ddbffcb5ebfff00000000000000000000000000000000000000000000000000b03ba09ea3f925000000000000000000000000000000000000000000000000004b971e610204900000000000000000000000000000000000000000000000000024c9f3ca5cbf7f00000000000000000000000000000000000000000000000000f23fa0bea3f92500000000000000000000000000000000000000000000000000bdfbffdfffffff00000000000000000000000000000000000000000000000000f6edf3fefdff7f000000000000000000000000000000000000000000000000009d3a7c15f3e7e0
  | 0, 2 => 0xffffffe1020490000000000000000000000000000000000000000000000000004b971e79cb979c00000000000000000000000000000000000000000000000000ffe4413ffd424a0000000000000000000000000000000000000000000000000009931e4102049000000000000000000000000000000000000000000000000000fff75f7fff46da000000000000000000000000000000000000000000000000006fdfffeb5ebfff0000000000000000000000000000000000000000000000000024c9e18a5cbb6f00000000000000000000000000000000000000000000000000ffffe1bffffb6f
  | 0, 3 => 0x24d24d0a5e02ca00000000000000000000000000000000000000000000000000460c702050a7600000000000000000000000000000000000000000000000000024c9f3ca5cbf7f00000000000000000000000000000000000000000000000000f6e4413efd424a000000000000000000000000000000000000000000000000002089b2ca00bd3500000000000000000000000000000000000000000000000000f2241e7ea1449000000000000000000000000000000000000000000000000000bdf35f5fff46da000000000000000000000000000000000000000000000000004b840021000000
  | 0, 4 => 0xddbe1815ebb6f000000000000000000000000000000000000000000000000009d21c2d5f15a5500000000000000000000000000000000000000000000000000fbbfbeffa3fdb5000000000000000000000000000000000000000000000000004b8ca0a100b9250000000000000000000000000000000000000000000000000099321c15a3448000000000000000000000000000000000000000000000000000fb361c3fa34480000000000000000000000000000000000000000000000000006b9fbeeb02bdb50000000000000000000000000000000000000000000000000090a11254a14410
  | 0, 5 => 0xffede1bffdfb6f000000000000000000000000000000000000000000000000004b971e690295940000000000000000000000000000000000000000000000000062c583ea0c181f000000000000000000000000000000000000000000000000009d3a7c15f3e7e000000000000000000000000000000000000000000000000000bdf35f5fffd7de000000000000000000000000000000000000000000000000004b840039c9020800000000000000000000000000000000000000000000000000db361c35a344800000000000000000000000000000000000000000000000000029529d8b0e1c8f
  | 0, 6 => 0x29529d93c78f830000000000000000000000000000000000000000000000000024c9f3c050a77000000000000000000000000000000000000000000000000000993a3c15a3e5a0000000000000000000000000000000000000000000000000002009a08a00b92500000000000000000000000000000000000000000000000000fbb71e7fa3449000000000000000000000000000000000000000000000000000db360c35a3408000000000000000000000000000000000000000000000000000b468e19efdfb6f00000000000000000000000000000000000000000000000000001bbec002bdb5
  | 0, 7 => 0xfff75f7fff46da000000000000000000000000000000000000000000000000000dc05f415c06da0000000000000000000000000000000000000000000000000062c583ea00181500000000000000000000000000000000000000000000000000f23fa0bea3f925000000000000000000000000000000000000000000000000009d3bfed5f3fff50000000000000000000000000000000000000000000000000062cda3ea0cb93f0000000000000000000000000000000000000000000000000024c1534a5c065a000000000000000000000000000000000000000000000000004b8ca0b9c92a29
  | 0, 8 => 0xff3ffcbff3ffe500000000000000000000000000000000000000000000000000ffffffe102049000000000000000000000000000000000000000000000000000bde0411ffd424a000000000000000000000000000000000000000000000000000dd25f415e06da000000000000000000000000000000000000000000000000006b9fbee1020490000000000000000000000000000000000000000000000000006fcdf3eb5cbf7f000000000000000000000000000000000000000000000000002409f08a50bf6500000000000000000000000000000000000000000000000000bdfbffdfa3fdb5
  | 0, 9 => 0x24dbffca5ebfff000000000000000000000000000000000000000000000000000009b2c000bd35000000000000000000000000000000000000000000000000009d7a7d15f7e7e2000000000000000000000000000000000000000000000000009d204015f1424000000000000000000000000000000000000000000000000000628582ea00181500000000000000000000000000000000000000000000000000fffe7d3fffe7ea00000000000000000000000000000000000000000000000000f23fa0bea3f925000000000000000000000000000000000000000000000000006fd75f6b5e06da
  | 0, 10 => 0xf23facbea3f9a50000000000000000000000000000000000000000000000000066cdf3ea5cbf7f00000000000000000000000000000000000000000000000000903a2014a3e120000000000000000000000000000000000000000000000000009d3a7c15f3c7c000000000000000000000000000000000000000000000000000993a3c15e3e7a000000000000000000000000000000000000000000000000000f2bfb2fea3fd35000000000000000000000000000000000000000000000000004204002000000000000000000000000000000000000000000000000000000000bd3bfc9ff3ffe5
  | 0, 11 => 0x9d3a7c15a3e5a000000000000000000000000000000000000000000000000000f6fff3feffff7f00000000000000000000000000000000000000000000000000f23fa0bea3f925000000000000000000000000000000000000000000000000000d404d015c02ca00000000000000000000000000000000000000000000000000f22da0bea1f925000000000000000000000000000000000000000000000000009d325c15f346c0000000000000000000000000000000000000000000000000004f9f7e6152a7f0000000000000000000000000000000000000000000000000000408700050a760
  | 0, 12 => 0x201bbeca02bdb50000000000000000000000000000000000000000000000000062c593ea0c1c1f00000000000000000000000000000000000000000000000000dfbf7e75f3e7f00000000000000000000000000000000000000000000000000009121c0102048000000000000000000000000000000000000000000000000000bd7afd9fffffef00000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000bdfb7f5ffff7fe000000000000000000000000000000000000000000000000000dc053415c065a
  | 0, 13 => 0x24c0410a5c024a000000000000000000000000000000000000000000000000000dc15f415c06da00000000000000000000000000000000000000000000000000fff65d3fff46ca000000000000000000000000000000000000000000000000000009a2c000b935000000000000000000000000000000000000000000000000000dd25f415e06da000000000000000000000000000000000000000000000000009dfa7f55ffe7fa000000000000000000000000000000000000000000000000000d005c015006c000000000000000000000000000000000000000000000000000fff75f7fff46da
  | 0, 14 => 0xffe4413ffd424a0000000000000000000000000000000000000000000000000009931e59cb979c000000000000000000000000000000000000000000000000002448e18a5cbb6f00000000000000000000000000000000000000000000000000bdfbffdfffffff0000000000000000000000000000000000000000000000000042170020020000000000000000000000000000000000000000000000000000009d3a7c15f3e7e00000000000000000000000000000000000000000000000000000120c0002008000000000000000000000000000000000000000000000000000ffedf3fffdff7f
  | 0, 15 => 0x4b971e610204900000000000000000000000000000000000000000000000000099320c15a3408000000000000000000000000000000000000000000000000000fb3fbcbfa3fda5000000000000000000000000000000000000000000000000009d3a7c15f3e7e0000000000000000000000000000000000000000000000000009dbb7e5dfbf7fc000000000000000000000000000000000000000000000000000d1a7c0152a7e000000000000000000000000000000000000000000000000000624481aa0c180f00000000000000000000000000000000000000000000000000f23fa0bea3f925
  | 1, 0 => 0x489724050a77000000000000000000000000000000000000000000000000000d2240034a1400000000000000000000000000000000000000000000000000000dbb71e75a3449000000000000000000000000000000000000000000000000000ffffffffffffff0000000000000000000000000000000000000000000000000062cda3ea0cb93f000000000000000000000000000000000000000000000000009d3a7c15a344800000000000000000000000000000000000000000000000000000811240000410000000000000000000000000000000000000000000000000009dbb7e55f3e7f0
  | 1, 1 => 0x1e40000490000000000000000000000000000000000000000000000000009028a094a1f92500000000000000000000000000000000000000000000000000f23fbefea3fdb500000000000000000000000000000000000000000000000000bdfbffdfffffff0000000000000000000000000000000000000000000000000062c593ea4c9f1f00000000000000000000000000000000000000000000000000044041005c024a0000000000000000000000000000000000000000000000000062cda3ea0c383f0000000000000000000000000000000000000000000000000042c403600c001a
  | 1, 2 => 0xf23fbefea3fdb500000000000000000000000000000000000000000000000000001ba08002b92500000000000000000000000000000000000000000000000000f6ffe1befffb6f00000000000000000000000000000000000000000000000000bdfa7d1fffe7ea00000000000000000000000000000000000000000000000000f6fff3feffff7f00000000000000000000000000000000000000000000000000621fa0aa02b925000000000000000000000000000000000000000000000000006b971e6b0204900000000000000000000000000000000000000000000000000024c9f3d4a14410
  | 1, 3 => 0x182c0001815000000000000000000000000000000000000000000000000004b9fbee102bdb50000000000000000000000000000000000000000000000000000131e40020490000000000000000000000000000000000000000000000000009d3a7c15f3e7e000000000000000000000000000000000000000000000000000bdfbfd9fffffef0000000000000000000000000000000000000000000000000024c9f3ca5cbf7f000000000000000000000000000000000000000000000000009d3a7c1fffffef0000000000000000000000000000000000000000000000000090200014a14000
  | 1, 4 => 0xffffffffffffff00000000000000000000000000000000000000000000000000bdbbfedff3fff5000000000000000000000000000000000000000000000000000ddbffc15ebfff00000000000000000000000000000000000000000000000000bd3a7c1ff3e7e0000000000000000000000000000000000000000000000000002040818a0c180f0000000000000000000000000000000000000000000000000000121e4002049000000000000000000000000000000000000000000000000000624481a2040803000000000000000000000000000000000000000000000000009d7a7d15ffe7ea
  | 1, 5 => 0xffff7f7ffff7fe0000000000000000000000000000000000000000000000000062c583ea0c001a0000000000000000000000000000000000000000000000000062c4012a0c000a00000000000000000000000000000000000000000000000000dfbf7e7dfbf7fc00000000000000000000000000000000000000000000000000b468e18634686300000000000000000000000000000000000000000000000000fffffff5f3e7f0000000000000000000000000000000000000000000000000009d3a7c0102048000000000000000000000000000000000000000000000000000b4e9f3defdff7f
  | 1, 6 => 0xffffffffebffbd000000000000000000000000000000000000000000000000000008a08000b92500000000000000000000000000000000000000000000000000fbb71e7febd79c000000000000000000000000000000000000000000000000009d325c15f3c7c00000000000000000000000000000000000000000000000000009121c11c3878000000000000000000000000000000000000000000000000000ffffffffffffff000000000000000000000000000000000000000000000000000081124848971c000000000000000000000000000000000000000000000000006b9fbefbcbbfbd
  | 1, 7 => 0xffe44121000000000000000000000000000000000000000000000000000000004b971e79cb069800000000000000000000000000000000000000000000000000bdfbffdfff46da000000000000000000000000000000000000000000000000004b971e7fffffff000000000000000000000000000000000000000000000000000000001efdfb6f000000000000000000000000000000000000000000000000009d3a7c15f3ffe500000000000000000000000000000000000000000000000000ffffffeb5ebfff000000000000000000000000000000000000000000000000004b971e79839594
  | 1, 8 => 0x4b971e7bdfbfff00000000000000000000000000000000000000000000000000ffffffeb5e06da000000000000000000000000000000000000000000000000004b971e694a0698000000000000000000000000000000000000000000000000002dc9ffcb5cbfff0000000000000000000000000000000000000000000000000024c1534a5c975e00000000000000000000000000000000000000000000000000620580aa001805000000000000000000000000000000000000000000000000009d3a7c15f346c0000000000000000000000000000000000000000000000000004b9fbef9cbbfbd
  | 1, 9 => 0x90200014a1400000000000000000000000000000000000000000000000000000fffe7d3fff46ca00000000000000000000000000000000000000000000000000ffff7f7fffe7fa00000000000000000000000000000000000000000000000000dfbf7e6102049000000000000000000000000000000000000000000000000000fbbfbee102049000000000000000000000000000000000000000000000000000fff75f61020490000000000000000000000000000000000000000000000000004b971e694a979c00000000000000000000000000000000000000000000000000621fa0ba83b925
  | 1, 10 => 0xffffffffffffff000000000000000000000000000000000000000000000000000dc041015c024a00000000000000000000000000000000000000000000000000ffe5537ffd465a00000000000000000000000000000000000000000000000000ffffffffff46da00000000000000000000000000000000000000000000000000ffffffe7366cf300000000000000000000000000000000000000000000000000dbbf3e75a3e5b000000000000000000000000000000000000000000000000000d23f2034a3e12000000000000000000000000000000000000000000000000000b468e186344042
  | 1, 11 => 0xfba4003fe94208000000000000000000000000000000000000000000000000004b160c3183008000000000000000000000000000000000000000000000000000ff3e7c3ff3e7e000000000000000000000000000000000000000000000000000fffffff9cb979c000000000000000000000000000000000000000000000000006fd75f7bdf97de000000000000000000000000000000000000000000000000004fd75f615e06da00000000000000000000000000000000000000000000000000ffe4412b5c024a000000000000000000000000000000000000000000000000000489724858b77c
  | 1, 12 => 0xffffffe53264f000000000000000000000000000000000000000000000000000ffffffe522449000000000000000000000000000000000000000000000000000001a3c0002a5a00000000000000000000000000000000000000000000000000042170038839104000000000000000000000000000000000000000000000000000440410014004200000000000000000000000000000000000000000000000000ffffffffffffff000000000000000000000000000000000000000000000000004b971e71c3879000000000000000000000000000000000000000000000000000fbbfbeffebffbd
  | 1, 13 => 0x9028a0842068210000000000000000000000000000000000000000000000000094286014f1e3600000000000000000000000000000000000000000000000000004c053405c065a00000000000000000000000000000000000000000000000000dfbe7c3dfbe7e8000000000000000000000000000000000000000000000000004b971e7fffd7de00000000000000000000000000000000000000000000000000b468e18430606000000000000000000000000000000000000000000000000000b028a09ea1f92500000000000000000000000000000000000000000000000000d23f203ca3f124
  | 1, 14 => 0xf23e203ea3e12000000000000000000000000000000000000000000000000000b4fbf3deffff7f0000000000000000000000000000000000000000000000000000000014a14000000000000000000000000000000000000000000000000000006fdffffbdfbfff00000000000000000000000000000000000000000000000000fff75f7fffd7de00000000000000000000000000000000000000000000000000ffffffffa3fdb500000000000000000000000000000000000000000000000000ffffffe10204900000000000000000000000000000000000000000000000000024c9f3c0000410
  | 1, 15 => 0x9801e41480698000000000000000000000000000000000000000000000000006fdfffe1020490000000000000000000000000000000000000000000000000000000000a5cbb6f00000000000000000000000000000000000000000000000000ffffffe15e06da000000000000000000000000000000000000000000000000000dc05f4100049000000000000000000000000000000000000000000000000000bdfbffcb5ebfff00000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000fffe613fffe36a
  | 2, 0 => 0x4b971e61029594000000000000000000000000000000000000000000000000006fc4412b5c024a000000000000000000000000000000000000000000000000004b160c2102008000000000000000000000000000000000000000000000000000ffffe1bfa3f9250000000000000000000000000000000000000000000000000094286004306060000000000000000000000000000000000000000000000000000000001efd424a00000000000000000000000000000000000000000000000000ffedf3fffd465a0000000000000000000000000000000000000000000000000000000018c9930c
  | 2, 1 => 0xf23fa0a002000000000000000000000000000000000000000000000000000000000000005c024a0000000000000000000000000000000000000000000000000066dff3fadfbf7f000000000000000000000000000000000000000000000000002040818204080300000000000000000000000000000000000000000000000000ffffffe3060c930000000000000000000000000000000000000000000000000042850260000010000000000000000000000000000000000000000000000000004b971e79df97de00000000000000000000000000000000000000000000000000f23fa0bea3f925
  | 2, 2 => 0xffffffe152a7f0000000000000000000000000000000000000000000000000009d3bfed5f3fff500000000000000000000000000000000000000000000000000fba4003fa1400000000000000000000000000000000000000000000000000000ffec713ffde76a00000000000000000000000000000000000000000000000000df3f7c35f3e7e000000000000000000000000000000000000000000000000000b468e182142863000000000000000000000000000000000000000000000000004b971e79cb979c00000000000000000000000000000000000000000000000000fffffff5f346d0
  | 2, 3 => 0xb460411efd424a00000000000000000000000000000000000000000000000000db240035a140000000000000000000000000000000000000000000000000000020c183ca0c181f000000000000000000000000000000000000000000000000009d3a6015f3e36000000000000000000000000000000000000000000000000000ffe4413ffd424a000000000000000000000000000000000000000000000000000d1a7c11d3a7e000000000000000000000000000000000000000000000000000fffff3ffffff7f00000000000000000000000000000000000000000000000000ffffffffffffff
  | 2, 4 => 0xbd7afd97f7efe30000000000000000000000000000000000000000000000000062c583e0000010000000000000000000000000000000000000000000000000002000000a00000000000000000000000000000000000000000000000000000000fff7413fff424a00000000000000000000000000000000000000000000000000ffe44d3ffd42ca000000000000000000000000000000000000000000000000009d287015f1e76000000000000000000000000000000000000000000000000000ffffffe73644d200000000000000000000000000000000000000000000000000fffffffbdfbfff
  | 2, 5 => 0xdb360c2102008000000000000000000000000000000000000000000000000000fff65d3fffc7ca00000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000ffe4413fa1400000000000000000000000000000000000000000000000000000b468e18000000000000000000000000000000000000000000000000000000000fffe7d35f3e7e000000000000000000000000000000000000000000000000000fffffdbfffffef00000000000000000000000000000000000000000000000000fffffffdfbf7fc
  | 2, 6 => 0xbdfbffc102049000000000000000000000000000000000000000000000000000fffffffff3fff500000000000000000000000000000000000000000000000000ffffffffffd7de000000000000000000000000000000000000000000000000002448e18214286300000000000000000000000000000000000000000000000000b028a08620682100000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000dfa4403df9424800000000000000000000000000000000000000000000000000bdfbffd5f3e7f0
  | 2, 7 => 0x9000c01000080
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 313 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 313 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 313 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 313 then wireAt i else 0
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
  | 5 => 83
  | 6 => 240
  | 7 => 127
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x448a9881
  | 5, 0 => 0x9cbc2a849bba8efa99705bd694b8b3548fdab39085bb727783e3493f7c8685b47c16252d7ad545617ac4752c725d1720718514c270a6f9f56db546b16d862c9c6d51488c67c52cf867a393a866685213627470685fd7d0095ba47f81521b304b4ce5a4234b6936264aac03c046253e3244b8dba63c4221bc3b51a9c939e295143677d6813625c84135ee32a6351752a531fceead2ffcf2892fa058c52f6a8d732eab2a932dd44a922d857a4529fa97af271420462426ef9222e824671f7f06ec1e59d3d11c6252531c4c3b1c1c0333ce1c0231261a688fd8197a8b18178c8c4b11d0aa59115ebcc61103d12e0b36306b09a6ad6409048c0b08fe9133039e226b
  | 5, 1 => 0xf65066bef440b65eeac35034e4869f12e2e5669ae0157504dd777e19d54000ecc5e7a398bc8ab796b65ae287b6136dfcb2681d2da9791970a8c1ac9ea5ab00cfa2fc52d8a08bf8959ec683b2
  | 6, 0 => 0x25efb12c247f7be223a8da9423868f512214890020d5dedc20d3d9322031019e2014b8841f847c961eef54901ea3f7721ae6d1ba1a5cf2ff19b9c8681960c3881914119e17b15448179512581789bd0c178028051746a36f166d087c1658ec56162c9eb5162179a015459a96146dd6781246dfb81204e72a11eec544118cffeb115a1d1a112e072910dcc7690ffab6a40f97bb250f86f6e30f323d150eccb7400e769f680e5391860d8a4f090d8687440d3259230ceb1d0d0c5be1980c42c18a0b8161930a5a9dcf09c253170825ce0e071ebcc606b6b959065ba1da05eb79380434951c02f9ec8602c256eb01ffe75701eb76ea01b709c801766d8100f8abef
  | 6, 1 => 0x4bbe22794b6f522c4b30afac4b2d2a5448ea497248c73261481af57147a969a6479899714717e5ee45f7656045f52ae24557a4644389e258427ed3a241dc42dd41c769554197cdb1405d83e23f313b653f26a70a3eb076c03e51fe3b3d7b1e3a3d4337b83c394efb3bcc4b8e3a8d85f33952b44c38cc09753870a9b138132deb371fff313672a2a7365be243356e6b0234e4849a34dfa180344e3108341b2bc1340c055d338dc01b33641e9c333c7658325fad01320d292d31c2f66d316c6b9a310d147d308b8d4b303ee06c2f4894ad2e00a7792dcf7e872c81232c2c5e54df2bf0eb492baf016a298caa252749ceb726bd9f6626aab89b262f9faf2608ac44
  | 6, 2 => 0x9c24a0c99ac6fcda977621a4953e36a6949ad501942d0a499309a0c392bbc7dd8f3307478de1876c8b8016b28af03f0389f2d53c85910990849041f483e13715837590b282b16c3582572dd28232c4c07fca1c1d7fb76ace7bea7d587bb3936c7baeb68b7a05332c78fdc95c783486df77b733fd77b4cbb1764d3db57429384474289a0073a633cf736c3eab735be02e7244ecfb7150c563714ed393703428a26f88ac4c6f31bd816df032966c39e43b6acc82b869904ec966ecb4b864f83f64641272976327452262c7ad3b5c70ee4c5b9174b95b78285e5a395d3358814a3c54f6b5bf509b8e214fbdcc704d54655a4cafcb164c95027a4c78e36f4bd0eb07
  | 6, 3 => 0xfdff4cebfd03f230fc3eb1b8fb7f4ed8fb615600f6981e4af491b39cf1454ba8e854bc93e64eaf5de5a19da1e50c25f4de3480bcd6830cf9d43a869fd280a8d8cfd1fae1c9aabb83c8a7e1a1c8903703c80f6476c80c58dcc762f157c5be59adc32546b1c3248b03bd2f7546bc375aabbb9554cdb9653685b7fe9d30b749d50ab62e8f91b2a179deb15ac357adefbcc3acd99b96aa4ba25ea8d3998ba890f89aa70aed3fa5067f7da42a7979a3a81e18a37fcfb99dc4f2209c6d2e439c33cacc
  | 7, 0 => 0x4c86d5c94c50a0f346f3f1d646d9577145d1eda144efaef6448b58424488eff644333198417604ab4133469f40fd5c89403004733f1911403e22f7d83d084ce73cd4cbae3c5cd0913c05e1c63b9517d93b8c25f934d1c21a313507a63092a0e22cbbaac62563fe1925029ba3237a559e2315feea2232fccd21da3c201c91f0b51a28899f19e4b4771983ef5b19728323196926bf19570811194d07b418bc18ae189246be1804d3f117c2485d168319a4159b56a614c25be713ec0a33122bc8a9108cbea20f52f7e70e62c7b30d31a8270c11c00d09c8d28f0626d89105a02dba0544cdf60499b2c10346c6ec02f5fddb028b04db01b8a8df0122554d002f4827
  | 7, 1 => 0xfee14d72eee8ad45e5f93c5de45de151df1b03fdde7c5035db27b5cbda5e734ed696775cd0e21cd5ca94fea2c9d81675c8357a45c73f73a1c169a7a0c165d7e1c08ae272b7aa7e56b275c1e6afe37ca7aabb0592a8845e94a6bea662a3dc3944a0e187959bea8a5f967edfc89492ddb29437159c9244de83924276378ff96af688ac191584d2c175831991368302b3d680b185227adb1b247ac3e1087a5ac63378ba6f2e6f1f7e7a6941528868f8c50e679b211f6650e12d62125aeb5faaa4325e4e7aea5d017f515ab5abb157c4634856713ef9563a3637560409b254bb116252fb438552c780f052652dd5516466394f85907a4cfebf194c9baf51
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x4008c200
  | 5, 0 => 0x2000000010010000000001001000000000100100000000010010000000000000020000000000002000000010410100000001001000000000100100000000010010000000000000020000000100100000000000000200000001001000000000000002000000010010000000001041010000000000002000000010010000000001001000000000100100000000010010000000000000020000000000002000000008c100000000001010000000001041010000000000002000000010410100000001041010000000000002
  | 5, 1 => 0x20000000100100000000000000200000001041010000000100100000000000000200000000000020000000000002000000010010000000001001000000000100100000000010410100000001041010000000100100000000010410100000000000020000000100100000000010010000000000000020000000104101000002310020000000000000020000000000002000000010410100000001001000000000000002000000010410100000000000020000000104101000000010010000000001001000000000104101
  | 5, 2 => 0x104101000000010010000000000000020000000104101000000000000200000001001000000000100100000000010410100000001041010000000104101000000010010000000001041010000000100100000000010010000000000000020000000100100000000000000200000000000020000000100100
  | 6, 0 => 0x1041010000000000000000000000000200000001041010000000000002000000010410100000000000020000000000000000000001010000000001041010000000050101000000000000200000001001000000000100100000000000000200000000101000000000000002000000000000100000001001000000000000000000000000000200000000000010000000000000000000000000200000000000010000000000000000000000000000000001001000000000000000000000010410100000000000020000000000002
  | 6, 1 => 0x501010000000100100000000000000100000000000020000000000002000000010410100000000000020000000100100000000000000000000001041010000000000001000000010010000000000501010000000000002000000000000000000000000020000000000002000000000000200000000000020000000000002000000000000100000000000020000000000002000000000000200000000000020000000000002000000000000200000000000010000000104101000000000000000000000000020000000000000
  | 6, 2 => 0x2000000000000200000000000020000000000002000000010010000000000000020000000050101000000010410100000000000020000000000002000000000000000000000000010000000000002000000010410100000000501010000000000002000000000000200000000000000000000000002000000008c100000000000000000000001041010000000000002000000000000200000000000020000000000001000000000000200000000000020000000000000000000000000200000000000020000000000001
  | 6, 3 => 0x1001000000000100100000000001010000000000000020000000000000000000000000200000000000020000000000000000000000000000000000000020000000000002000000001010000000000000020000000000002000000000000200000000000020000000000002000000000000200000000000020000000000001000000010010000000000000000000000000000000000000000000000000000000000000000002000000000000200000000000010000000000002000000000000200000001001000000000000002
  | 6, 4 => 0x100100000000000000000000001001000000000000002000000000000200000000000020000000104101000000001010000000000000020000000000002000000005010100000000000010000000000000000000000000200000000000020000000000002000000000000200000000000000000000000001000000000000200000000000020000000000002000000000000200000000000010000000000002000000010010000000001041010000000104101000000010010000000001001000000000000001
  | 6, 5 => 0x1001000000000010100000000000000200000001001000000000100100000000000000200000000000020000000000001000000000000000000001001000000000104101000000010010000000000000020000000050101000000010010000000000000000000000000002000000010010000000000000000000000000002000000000000200000000000020000000000000000000000000000000000000020000000000002000000010410100000001041010000000100100000000000000200000000000000000000000002
  | 6, 6 => 0x20000000000002000000010410100000001001000000000000000000000000000200000001001000000000000002000000010410100000000000010000000000002000000010410100000000000020000000000001000000010410100000000000020000000100100000000000000200000000000010000000100100000000000000200000000000000000000104101000000000000200000000000020000000000002000000000000200000000000020000000000000000000000000200000000501010000000000002
  | 6, 7 => 0x100100000000000000200000000000010000000000000000000010010000000000000020000000100100000000000000200000000000020000000000000000000000000200000000000000000000000002000000010410100000000000010000000100100
  | 7, 0 => 0x10000000000001000000000000100000000000020000000000000000000000000200000000000000000000000002000000000000000000000000000000000000001000000000000200000000000020000000000002000000000000000000000000020000000000002000000000000200000000000020000000000002000000000000000000000000000000000000002000000000000200000000000000000000000002000000000000200000000000000000000000001000000000000000000000000010000000000002
  | 7, 1 => 0x20000000000002000000000000100000000000020000000000001000000000000100000000000000000000000002000000000000200000000000000000000000002000000000000200000000000000000000000002000000000000200000000000010000000000000000000000000000000000000020000000000001000000000000200000000000000000000000001000000000000000000000000020000000000002000000000000200000000000020000000000002000000000000100000000000020000000000000
  | 7, 2 => 0x10000000000000000000000000100000000000020000000000000000000000000000000000000020000000000000000000000000100000000000010000000000002000000000000100000000000000000000000000000000000000200000000000000000000000002000000000000200000000000020000000000000000000000000000000000000000000000000002000000000000100000000000010000000000002000000000000200000000000010000000000000000000000000000000000000020000000000002
  | 7, 3 => 0x1000000000000200000000000000000000000001000000000000100000000000010000000000001000000000000100000000000000000000000002000000000000200000000000020000000000000000000000000000000000000000000000000000000000000000000000000000010000000000002000000000000000000000000020000000000002000000000000100000000000000000000000002000000000000200000000000020000000000002000000000000000000000000020000000000002
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_62 roots_62 6 s ws hint
  | 1 => checkCutEntry dom_59 roots_59 6 s ws hint
  | 2 => checkCutEntry dom_29 roots_29 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
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
private theorem z4_16 : ∀ i, 16 ≤ i → i < 28 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 12 16 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 28 → Z 4 i = true := (range_split z4_0 z4_16)
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
private theorem z5_224 : ∀ i, 224 ≤ i → i < 235 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 11 224 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 235 → Z 5 i = true := (range_split (range_split (range_split z5_0 (range_split z5_16 z5_32)) (range_split (range_split z5_48 z5_64) (range_split z5_80 z5_96))) (range_split (range_split (range_split z5_112 z5_128) (range_split z5_144 z5_160)) (range_split (range_split z5_176 z5_192) (range_split z5_208 z5_224))))
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
private theorem z6_496 : ∀ i, 496 ≤ i → i < 506 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 10 496 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 506 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112))) (range_split (range_split (range_split z6_128 z6_144) (range_split z6_160 z6_176)) (range_split (range_split z6_192 z6_208) (range_split z6_224 z6_240)))) (range_split (range_split (range_split (range_split z6_256 z6_272) (range_split z6_288 z6_304)) (range_split (range_split z6_320 z6_336) (range_split z6_352 z6_368))) (range_split (range_split (range_split z6_384 z6_400) (range_split z6_416 z6_432)) (range_split (range_split z6_448 z6_464) (range_split z6_480 z6_496)))))
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
private theorem z7_272 : ∀ i, 272 ≤ i → i < 285 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 13 272 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 285 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 (range_split z7_112 z7_128)))) (range_split (range_split (range_split z7_144 z7_160) (range_split z7_176 z7_192)) (range_split (range_split z7_208 z7_224) (range_split z7_240 (range_split z7_256 z7_272)))))
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩], 15⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 10 := by decide

theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4205488640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4205488640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4205488640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 10 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4205488640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 10 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_12893_aux

theorem PEqualNP.Outside.L_meta_12893 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4205488640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4205488640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_12893_aux.wit, PEqualNP.Outside.L_meta_12893_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_12893_aux.wit_sz (PEqualNP.Outside.L_meta_12893_aux.lower s hs), PEqualNP.Outside.L_meta_12893_aux.wit_ev⟩
