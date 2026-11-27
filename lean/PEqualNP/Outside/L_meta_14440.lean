import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14440_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def mask256 : Nat := 2 ^ 256 - 1

def negD (d w : Nat) : Nat := (w ^^^ mask256) &&& d
def andD (d a b : Nat) : Nat := (a &&& b) &&& d
def orD (d a b : Nat) : Nat := (a ||| b) &&& d
def opD (d : Nat) (op : Nat) (a b : Nat) : Nat :=
  if op == 0 then andD d a b
  else if op == 1 then orD d a b
  else if op == 2 then andD d a (negD d b)
  else andD d (negD d a) b

def allowedB (u : Bool) (op : Nat) : Bool :=
  decide (op < 2) || (u && decide (op < 4))

def flipOp (op : Nat) : Nat :=
  if op == 2 then 3 else if op == 3 then 2 else op

def nrmD (u : Bool) (d w : Nat) : Nat :=
  if u && w.testBit 0 then negD d w else w &&& d

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunD (u : Bool) (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a b r} (op : Nat) (ka kb : Bool),
      allowedB u op = true →
      opD d op a b ≠ 0 →
      opD d op a b ≠ d →
      opD d op a b ∉ (a :: b :: r) →
      P s (opD d op a b :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {u : Bool} {d y : Nat}

theorem Run.done : RunD u d y 0 [y] := fun _ dn _ _ => dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD u d y s xs) :
    RunD u d y s zs := fun P dn q b => q p (h P dn q b)
theorem Run.two {s a b r} (op : Nat) (ka kb : Bool)
    (hop : allowedB u op = true)
    (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
    (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))) :
    RunD u d y (s + 1) (a :: b :: r) := fun P dn q v => v op ka kb hop h0 hd hm (h P dn q v)

theorem Run.fold {P : ∀ t ws, RunD u d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD u d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (two : ∀ {s a b r} (op : Nat) (ka kb : Bool)
      (hop : allowedB u op = true)
      (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
      (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two op ka kb hop h0 hd hm h))
    {t ws} (h : RunD u d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunD u d y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun op ka kb hop h0 hd hm ⟨h', ih⟩ => ⟨Run.two op ka kb hop h0 hd hm h', two op ka kb hop h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end

theorem allowed_cases {u : Bool} {op : Nat} (h : allowedB u op = true) :
    op = 0 ∨ op = 1 ∨ (u = true ∧ op = 2) ∨ (u = true ∧ op = 3) := by
  simp only [allowedB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨hu, h⟩
  · omega
  · have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨hu, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu, rfl⟩))

theorem opD_comm {u : Bool} (d : Nat) {op : Nat} (hop : allowedB u op = true) (a b : Nat) :
    opD d op a b = opD d (flipOp op) b a := by
  rcases allowed_cases hop with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp [opD, flipOp, andD, orD, Nat.and_comm, Nat.or_comm]

theorem flipOp_allowed {u : Bool} {op : Nat} (hop : allowedB u op = true) :
    allowedB u (flipOp op) = true := by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [allowedB, flipOp]

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

theorem run_len {u d y s xs} (h : RunD u d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | two _ ka kb _ _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

theorem zero_done {u d y t ws} (h : RunD u d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | two => simp

def IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def isConstB (d w : Nat) : Bool := (w &&& d == 0) || (w &&& d == d)

theorem isConstB_iff (d w : Nat) : isConstB d w = true ↔ IsConst d w := by
  simp [isConstB, IsConst]

def Avail (u : Bool) (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  IsConst d w ∨ (∃ v ∈ bank, (v &&& d) = (w &&& d)) ∨ (u = true ∧ ∃ v ∈ bank, (v &&& d) = negD d w)

def availB (u : Bool) (d : Nat) (bank : List Nat) (w : Nat) : Bool :=
  let m := w &&& d
  m == 0 || m == d || bank.any (fun v => (v &&& d) == m) ||
    (u && bank.any (fun v => (v &&& d) == negD d w))

theorem availB_iff (u : Bool) (d : Nat) (bank : List Nat) (w : Nat) :
    availB u d bank w = true ↔ Avail u d bank w := by
  simp [availB, Avail, IsConst, or_assoc]

def NatReach (u : Bool) (d : Nat) (roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
    ∃ b a c op, allowedB u op = true ∧ bank = opD d op a c :: b ∧
      NatReach u d roots p b ∧ Avail u d b a ∧ Avail u d b c

def Lower (u : Bool) (d : Nat) (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, NatReach u d roots p bank → Avail u d bank T → L ≤ p

theorem avail_mono {d : Nat} {bank : List Nat} {w : Nat} (h : Avail false d bank w) :
    Avail true d bank w := by
  rcases h with h | h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · contradiction

theorem reach_up {d : Nat} {roots : List Nat} {p bank} (h : NatReach false d roots p bank) :
    NatReach true d roots p bank := by
  induction p generalizing bank with
  | zero => exact h
  | succ p ih =>
    obtain ⟨b, a, c, op, hop, rfl, hrb, ha, hc⟩ := h
    have hop' : allowedB true op = true := by
      rcases allowed_cases hop with rfl | rfl | ⟨hc, _⟩ | ⟨hc, _⟩ <;> first | decide | contradiction
    exact ⟨b, a, c, op, hop', rfl, ih hrb, avail_mono ha, avail_mono hc⟩

theorem lower_down {d : Nat} {roots : List Nat} {T L : Nat} (h : Lower true d roots T L) :
    Lower false d roots T L := fun p bank hr ha => h p bank (reach_up hr) (avail_mono ha)

theorem mask256_bit (i : Nat) : mask256.testBit i = decide (i < 256) := by
  rw [mask256, Nat.testBit_two_pow_sub_one]

theorem opD_and_sub {d d1 : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d) (op a b : Nat) :
    opD d1 op a b &&& d = opD d op a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  have h2 := congrArg (fun v => v.testBit i) hsub
  unfold opD
  split_ifs <;> simp only [andD, orD, negD, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at * <;>
    cases hi : d.testBit i <;> simp_all

theorem negD_invol {d : Nat} (hd : d &&& mask256 = d) (a : Nat) :
    negD d (negD d a) = a &&& d := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  simp only [negD, Nat.testBit_and, Nat.testBit_xor] at *
  cases hi : d.testBit i <;> cases ha : a.testBit i <;> simp_all

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

theorem opD_mask_self (d op a b : Nat) : opD d op a b &&& d = opD d op a b := by
  apply Nat.eq_of_testBit_eq; intro i
  unfold opD; split_ifs <;> simp only [andD, orD, negD, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases d.testBit i <;> simp

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

theorem avail_cons {u : Bool} {d : Nat} {bank : List Nat} (z w : Nat) (h : Avail u d bank w) :
    Avail u d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩ | ⟨hu, v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨v, List.mem_cons_of_mem _ hv, he⟩)
  · exact Or.inr (Or.inr ⟨hu, v, List.mem_cons_of_mem _ hv, he⟩)

theorem avail_of_eq {u : Bool} {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Avail u d bank v) : Avail u d bank w := by
  rcases h with (h0 | h1) | ⟨x, hx, hxe⟩ | ⟨hu, x, hx, hxe⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr (Or.inl ⟨x, hx, hxe.trans he⟩)
  · exact Or.inr (Or.inr ⟨hu, x, hx, hxe.trans (by rw [← negD_mask, he, negD_mask])⟩)

theorem avail_neg {d : Nat} (hd : d &&& mask256 = d) {bank : List Nat} {w : Nat}
    (h : Avail true d bank w) : Avail true d bank (negD d w) := by
  rcases h with hc | ⟨v, hv, he⟩ | ⟨_, v, hv, he⟩
  · exact Or.inl (negD_const hd hc)
  · refine Or.inr (Or.inr ⟨rfl, v, hv, ?_⟩)
    rw [negD_invol hd, he]
  · refine Or.inr (Or.inl ⟨v, hv, ?_⟩)
    rw [he]; simp [negD, Nat.and_assoc, Nat.and_self]

theorem opD_const_left {u : Bool} {d : Nat} (hd : d &&& mask256 = d) {op : Nat}
    (hop : allowedB u op = true) {a b : Nat} (hc : IsConst d a) :
    (opD d op a b &&& d = 0) ∨ (opD d op a b &&& d = d) ∨
      (opD d op a b &&& d = b &&& d) ∨ (u = true ∧ opD d op a b &&& d = negD d b) := by
  rcases allowed_cases hop with rfl | rfl | ⟨hu, rfl⟩ | ⟨hu, rfl⟩
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [opD, andD, Nat.testBit_and, Nat.zero_testBit, beq_self_eq_true, ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [opD, andD, Nat.testBit_and, beq_self_eq_true, ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [opD, orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, beq_self_eq_true, ite_true, ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [opD, orD, Nat.testBit_and, Nat.testBit_or, beq_self_eq_true, ite_true, ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [opD, andD, negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, beq_self_eq_true, ite_true, ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; right; refine ⟨hu, ?_⟩
      apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      have hdi := congrArg (fun v => v.testBit i) hd
      simp only [opD, andD, negD, Nat.testBit_and, Nat.testBit_xor, beq_self_eq_true, ite_true, ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      have hdi := congrArg (fun v => v.testBit i) hd
      simp only [opD, andD, negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, beq_self_eq_true, ite_true, ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      have hdi := congrArg (fun v => v.testBit i) hd
      simp only [opD, andD, negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, beq_self_eq_true, ite_true, ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all

theorem countP_kept_ge {α : Type} (p : α → Bool) (b : Bool) (a : α) (xs : List α) :
    xs.countP p ≤ (kept b a xs).countP p := by
  cases b <;> simp [kept, List.countP_cons] <;> split <;> omega

theorem contraction {u : Bool} {d d1 T : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD u d1 T s ws) {roots p bank}
    (hp : NatReach u d roots p bank) (hs : ∀ w ∈ ws, Avail u d bank w) :
    ∃ q next, NatReach u d roots q next ∧ Avail u d next T ∧
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
  | @two s a b r op ka kb hop _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    have hb := hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1 := opD d1 op a b
    set z0 := opD d op a b
    have hz_eq : z1 &&& d = z0 &&& d := by
      rw [opD_and_sub hd hsub, opD_mask_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail u d bank z1 := by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨rfl, hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
          · exact avail_of_eq (by rw [hn]; simp [negD, Nat.and_assoc, Nat.and_self]) (avail_neg hd hb)
        · dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨rfl, hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
          · exact avail_of_eq (by rw [hn]; simp [negD, Nat.and_assoc, Nat.and_self]) (avail_neg hd ha)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail u d bank w := by
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
          rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨_, hn⟩
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1, hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b := by simp only [isConstB, hz_eq.trans he]
            simp [ha1, hzb]
          · have hzb : isConstB d z1 = isConstB d b := by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff, isConstB_iff]
              have hnm : negD d b &&& d = negD d b := by simp [negD, Nat.and_assoc, Nat.and_self]
              constructor
              · intro hz; have hnb : IsConst d (negD d b) := by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq.symm.trans h1)))
                have h2 := negD_const hd hnb
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc, Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc, Nat.and_self] using e)]
              · intro hb'; have hnb := negD_const hd hb'
                rcases hnb with h0 | h1
                · exact Or.inl (hz_eq.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq.trans (hn.trans (hnm.symm.trans h1)))
            simp [ha1, hzb]
        · have hb1 : isConstB d b = true := (isConstB_iff _ _).2 hcb
          have hz_eq' : z1 &&& d = opD d (flipOp op) b a &&& d := by rw [hz_eq]; dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨_, hn⟩
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1, hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a := by simp only [isConstB, hz_eq'.trans he]
            simp [hb1, hza]
          · have hza : isConstB d z1 = isConstB d a := by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff, isConstB_iff]
              have hnm : negD d a &&& d = negD d a := by simp [negD, Nat.and_assoc, Nat.and_self]
              constructor
              · intro hz; have hna : IsConst d (negD d a) := by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h1)))
                have h2 := negD_const hd hna
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc, Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc, Nat.and_self] using e)]
              · intro ha'; have hna := negD_const hd ha'
                rcases hna with h0 | h1
                · exact Or.inl (hz_eq'.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq'.trans (hn.trans (hnm.symm.trans h1)))
            simp [hb1, hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hna : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false := by
        cases h : isConstB d b with | false => rfl | true => exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach' : NatReach u d roots (p + 1) (z0 :: bank) := ⟨bank, a, b, op, hop, rfl, hp, ha, hb⟩
      have hz_av : Avail u d (z0 :: bank) z1 := Or.inr (Or.inl ⟨z0, List.mem_cons_self, hz_eq.symm⟩)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail u d (z0 :: bank) w := by
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

-- Normalization lemmas for backward extraction
theorem nrmD_mask (u : Bool) (d w : Nat) : nrmD u d w &&& d = nrmD u d w := by
  unfold nrmD; split <;> simp [negD, Nat.and_assoc, Nat.and_self]

theorem nrmD_of_bit0_false (u : Bool) (d w : Nat) (hw : w.testBit 0 = false) :
    nrmD u d w = w &&& d := by
  simp [nrmD, hw]

theorem nrmD_and_d {d : Nat} (hd0 : d.testBit 0 = true) (u : Bool) (w : Nat) :
    nrmD u d (w &&& d) = nrmD u d w := by
  unfold nrmD
  rw [Nat.testBit_and, hd0, Bool.and_true, negD_mask, Nat.and_assoc, Nat.and_self]

theorem nrmD_neg {d : Nat} (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true) (w : Nat) :
    nrmD true d (negD d w) = nrmD true d w := by
  have hm0 : mask256.testBit 0 = true := by decide
  unfold nrmD
  have hnb : (negD d w).testBit 0 = !w.testBit 0 := by
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, hd0, hm0, Bool.and_true, Bool.xor_true]
  rw [hnb]
  cases hw : w.testBit 0
  · simp [negD_invol hd]
  · simp [negD, Nat.and_assoc, Nat.and_self]

theorem nrmD_const_iff {d : Nat} (hd : d &&& mask256 = d) (u : Bool) (w : Nat) :
    (nrmD u d w ≠ 0 ∧ nrmD u d w ≠ d) ↔ ¬ IsConst d w := by
  unfold nrmD
  have hnm : negD d w &&& d = negD d w := by simp [negD, Nat.and_assoc, Nat.and_self]
  split
  · constructor
    · rintro ⟨h0, h1⟩ hc
      rcases negD_const hd hc with hn0 | hn1
      · exact h0 (hnm.symm.trans hn0)
      · exact h1 (hnm.symm.trans hn1)
    · intro hnc; refine ⟨fun h0 => ?_, fun h1 => ?_⟩
      · have := negD_const hd (a := negD d w) (Or.inl (hnm.trans h0))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc, Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc, Nat.and_self] using e)])
      · have := negD_const hd (a := negD d w) (Or.inr (hnm.trans h1))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc, Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc, Nat.and_self] using e)])
  · simp [IsConst, not_or]

theorem opD_bit {d : Nat} (hd : d &&& mask256 = d) (op a b i : Nat) (hdi : d.testBit i = true) :
    (opD d op a b).testBit i =
      if op == 0 then a.testBit i && b.testBit i
      else if op == 1 then a.testBit i || b.testBit i
      else if op == 2 then a.testBit i && !(b.testBit i)
      else !(a.testBit i) && b.testBit i := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hdi] at this; exact this
  unfold opD; split_ifs <;>
    simp only [andD, orD, negD, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hdi, hmi, Bool.and_true, Bool.xor_true]

theorem nrmD_bit {d : Nat} (hd : d &&& mask256 = d) (w i : Nat) (hdi : d.testBit i = true) :
    (nrmD true d w).testBit i = if w.testBit 0 then !(w.testBit i) else w.testBit i := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hdi] at this; exact this
  unfold nrmD
  cases hw0 : w.testBit 0 <;>
    simp only [hw0, Bool.true_and, Bool.and_false, Bool.false_eq_true, ite_true, ite_false,
      negD, Nat.testBit_and, Nat.testBit_xor, hdi, hmi, Bool.and_true, Bool.xor_true]

theorem nrmD_opD {d : Nat} (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true)
    (u : Bool) (op : Nat) (hop : allowedB u op = true) (a b : Nat) :
    ∃ op', allowedB u op' = true ∧
      nrmD u d (opD d op a b) = opD d op' (nrmD u d a) (nrmD u d b) := by
  cases u with
  | false =>
    rcases allowed_cases hop with rfl | rfl | ⟨h, _⟩ | ⟨h, _⟩
    · exact ⟨0, rfl, by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD, opD, andD, Bool.false_and, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true, Nat.testBit_and]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1, rfl, by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD, opD, orD, Bool.false_and, Bool.false_eq_true, ite_false]
        simp only [show (1 == 0) = false from rfl, show (1 == 1) = true from rfl, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · contradiction
    · contradiction
  | true =>
    have h4 : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by
      rcases allowed_cases hop with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    have hbit : ∀ (e : Nat),
        (∀ i, d.testBit i = true →
          (nrmD true d (opD d op a b)).testBit i =
          (opD d e (nrmD true d a) (nrmD true d b)).testBit i) →
        nrmD true d (opD d op a b) = opD d e (nrmD true d a) (nrmD true d b) := by
      intro e h; apply Nat.eq_of_testBit_eq; intro i
      by_cases hdi : d.testBit i = true
      · exact h i hdi
      · have hf : d.testBit i = false := Bool.eq_false_iff.2 hdi
        have h1 := congrArg (fun v => v.testBit i) (nrmD_mask true d (opD d op a b))
        have h2 := congrArg (fun v => v.testBit i) (opD_mask_self d e (nrmD true d a) (nrmD true d b))
        simp only [Nat.testBit_and, hf, Bool.and_false] at h1 h2; exact h1.symm.trans h2
    rcases h4 with rfl | rfl | rfl | rfl <;>
      cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0
    · exact ⟨0, by decide, hbit 0 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2, by decide, hbit 2 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3, by decide, hbit 3 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1, by decide, hbit 1 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1, by decide, hbit 1 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3, by decide, hbit 3 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2, by decide, hbit 2 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0, by decide, hbit 0 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2, by decide, hbit 2 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0, by decide, hbit 0 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1, by decide, hbit 1 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3, by decide, hbit 3 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3, by decide, hbit 3 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1, by decide, hbit 1 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0, by decide, hbit 0 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2, by decide, hbit 2 fun i hdi => by rw [nrmD_bit hd _ i hdi, opD_bit hd _ _ _ 0 hd0, opD_bit hd _ _ _ i hdi, opD_bit hd _ _ _ i hdi, nrmD_bit hd a i hdi, nrmD_bit hd b i hdi, ha0, hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩

theorem avail_nrm_mem {u : Bool} {d : Nat} (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true)
    {b : List Nat} {w : Nat} (h : Avail u d b w) (hnc : ¬ IsConst d w) :
    nrmD u d w ∈ b.map (nrmD u d) := by
  rcases h with hc | ⟨v, hv, he⟩ | ⟨rfl, v, hv, he⟩
  · exact absurd hc hnc
  · refine List.mem_map.2 ⟨v, hv, ?_⟩
    rw [← nrmD_and_d hd0, he, nrmD_and_d hd0]
  · refine List.mem_map.2 ⟨v, hv, ?_⟩
    rw [← nrmD_and_d hd0, he, nrmD_neg hd hd0]

theorem pull_two {u : Bool} {d Y k ws} (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true)
    (hnd : ws.Nodup) (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD u d Y k ws)
    {b : List Nat} {a c : Nat} (op : Nat) (hop : allowedB u op = true)
    (ha : Avail u d b a) (hc : Avail u d b c)
    (hsub : ∀ w ∈ ws, w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (nrmD u d)) ∧ RunD u d Y k' ws' := by
  set z := nrmD u d (opD d op a c)
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (nrmD u d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      obtain ⟨op', hop', hez⟩ := nrmD_opD hd hd0 u op hop a c
      have ha_nc : ¬ IsConst d a := by
        intro hca
        have hznc : ¬ IsConst d (opD d op a c) := (nrmD_const_iff hd u _).1 hzp
        rcases opD_const_left hd hop hca with e0 | e1 | ec | ⟨rfl, en⟩
        · exact hznc (Or.inl e0)
        · exact hznc (Or.inr e1)
        · have hcn : ¬ IsConst d c := fun hcc => hznc (by rcases hcc with e | e <;> [exact Or.inl (ec.trans e); exact Or.inr (ec.trans e)])
          have hz_eq : z = nrmD u d c := by dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c), ec, nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
        · have hcn : ¬ IsConst d c := fun hcc => hznc (by
            rcases negD_const hd hcc with e | e
            · exact Or.inl (en.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using e))
            · exact Or.inr (en.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using e)))
          have hz_eq : z = nrmD true d c := by dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c), en, nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
      have hc_nc : ¬ IsConst d c := by
        intro hcc
        have hznc : ¬ IsConst d (opD d op a c) := (nrmD_const_iff hd u _).1 hzp
        have hcm : opD d op a c = opD d (flipOp op) c a := opD_comm d hop a c
        rcases opD_const_left hd (flipOp_allowed hop) hcc with e0 | e1 | ea | ⟨rfl, en⟩
        · exact hznc (Or.inl (hcm.symm ▸ e0))
        · exact hznc (Or.inr (hcm.symm ▸ e1))
        · have hz_eq : z = nrmD u d a := by
            dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c), hcm, ea, nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
        · have hz_eq : z = nrmD true d a := by
            dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c), hcm, en, nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
      set a' := nrmD u d a
      set c' := nrmD u d c
      have ha'_mem : a' ∈ b.map (nrmD u d) := avail_nrm_mem hd hd0 ha ha_nc
      have hc'_mem : c' ∈ b.map (nrmD u d) := avail_nrm_mem hd hd0 hc hc_nc
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := (nrmD_const_iff hd u a).2 ha_nc
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d := (nrmD_const_iff hd u c).2 hc_nc
      have hne_ac : a' ≠ c' := by
        intro heq
        have hz_eq : opD d op' a' a' = a' ∨ opD d op' a' a' = 0 := by
          rcases allowed_cases hop' with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm := congrArg (fun v => v.testBit i) (nrmD_mask u d a)
            change (a' &&& d).testBit i = a'.testBit i at hm
            simp only [opD, andD, Nat.testBit_and] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm := congrArg (fun v => v.testBit i) (nrmD_mask u d a)
            change (a' &&& d).testBit i = a'.testBit i at hm
            simp only [opD, orD, Nat.testBit_and, Nat.testBit_or] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi := congrArg (fun v => v.testBit i) hd
            simp only [opD, andD, negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi := congrArg (fun v => v.testBit i) hd
            simp only [opD, andD, negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
        have hez' : z = opD d op' a' a' := by
          have : z = opD d op' a' c' := hez
          rw [← heq] at this; exact this
        rcases hz_eq with e | e
        · exact hzb ((hez'.trans e).symm ▸ ha'_mem)
        · exact hzp.1 (hez'.trans e)
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (nrmD u d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have h1 : RunD u d Y k (opD d op' a' c' :: rest) := by
        rw [← hez]; exact Run.perm hp1 h
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
      have hne0 : opD d op' a' c' ≠ 0 := fun h0 => hzp.1 (hez.trans h0)
      have hned : opD d op' a' c' ≠ d := fun h1 => hzp.2 (hez.trans h1)
      have hnm : opD d op' a' c' ∉ (a' :: c' :: tail) := by
        rw [← hez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (by simpa [z, e] using ha'_mem)
        · exact hzb (by simpa [z, e] using hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD u d Y (k + 1) (a' :: c' :: tail) := Run.two op' ka kb hop' hne0 hned hnm h2
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

theorem reach_to_run_aux {u : Bool} {d : Nat} {roots : List Nat} {p bank}
    (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true)
    (hr : NatReach u d roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (nrmD u d)) → RunD u d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ roots.map (nrmD u d)) ∧ RunD u d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    obtain ⟨b, a, c, op, hop, rfl, hrb, ha, hc⟩ := hr
    have hsub' : ∀ w ∈ ws, w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d) := by
      intro w hw; simpa [List.map_cons] using hsub w hw
    obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_two hd hd0 hnd hprop hrun op hop ha hc hsub'
    obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
    exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem reach_to_run {u : Bool} {d : Nat} {roots : List Nat} {T : Nat} {p bank}
    (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r => !r.testBit 0) = true)
    (hnc : ¬ IsConst d T) (hr : NatReach u d roots p bank) (ha : Avail u d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ roots.map (· &&& d)) ∧ RunD u d (T &&& d) s ws := by
  have hTmem : T &&& d ∈ bank.map (nrmD u d) := by
    have := avail_nrm_mem hd hd0 ha hnc
    rwa [nrmD_of_bit0_false u d T hT0] at this
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (nrmD u d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact hTmem
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := reach_to_run_aux hd hd0 hr (List.nodup_singleton _) hprop hsub Run.done
  have hrmap : roots.map (nrmD u d) = roots.map (· &&& d) := by
    apply List.map_congr_left
    intro r hr_m
    have h0 := List.all_eq_true.1 hR0 r hr_m
    simp only [Bool.not_eq_true'] at h0
    exact nrmD_of_bit0_false u d r h0
  rw [hrmap] at hsub'
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

-- Bit separation lemmas
theorem runD_bits {u d y s ws} (hd : d &&& mask256 = d) (h : RunD u d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : mask256.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
        simp [opD, andD, orD, negD, ha, hb, hi, hj, hmi, hmj]
    · rw [mem_kept, mem_kept] at hr
      rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

theorem runD_bits_le_mono {d y s ws} (h : RunD false d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨h, _⟩ | ⟨h, _⟩
      · simp only [opD, andD, beq_self_eq_true, ite_true, Nat.testBit_and, hi, hj, Bool.and_true]; grind
      · simp only [opD, orD, beq_self_eq_true, ite_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true]; grind
      · contradiction
      · contradiction
    · rw [mem_kept, mem_kept] at hr
      rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

theorem lower_base {u : Bool} {d : Nat} {roots : List Nat} {T : Nat} (h : availB u d roots T = false) :
    Lower u d roots T 1 := by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht := (availB_iff u d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p => omega

-- moveBits & lower_iso
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

theorem applyMoves_opD (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2 : Nat} (hd : applyMoves ms d2 = d1) (op a b : Nat) :
    applyMoves ms (opD d2 op a b) = opD d1 op (applyMoves ms a) (applyMoves ms b) := by
  obtain ⟨hand, hor, hxor, _, h256⟩ := applyMoves_hom ms hok
  unfold opD; split_ifs <;> simp only [andD, orD, negD, hand, hor, hxor, h256, hd]

theorem applyMoves_runD {u d Y s} (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD u d Y s ws) :
    RunD u d Y s (ws.map (applyMoves ms)) := by
  obtain ⟨_, _, _, h0, _⟩ := applyMoves_hom ms hok
  have hinj := applyMoves_inj ms hok
  rw [← hY]
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map _) ih
  | @two s a b r op ka kb hop hne0 hned hnm _ ih =>
    have eop := applyMoves_opD ms hok hd op a b
    have e1 : (opD d op a b :: kept ka a (kept kb b r)).map (applyMoves ms) =
        opD d op (applyMoves ms a) (applyMoves ms b) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))) := by
      simp [kept_map, eop]
    rw [e1] at ih
    refine Run.two op ka kb hop ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop, ← List.map_cons, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)

theorem reach_map_moves {u : Bool} (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2 : Nat} (hd1 : d1 &&& mask256 = d1) (hd : applyMoves ms d2 = d1)
    {roots1 roots2 : List Nat} (hroots : ∀ r ∈ roots2, Avail u d1 roots1 (applyMoves ms r)) :
    ∀ {p bank}, NatReach u d2 roots2 p bank →
      ∃ bank', NatReach u d1 roots1 p bank' ∧ ∀ v ∈ bank, Avail u d1 bank' (applyMoves ms v) := by
  obtain ⟨hand, _, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hav : ∀ {b b' w}, (∀ v ∈ b, Avail u d1 b' (applyMoves ms v)) →
      Avail u d2 b w → Avail u d1 b' (applyMoves ms w) := by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v, hv, he⟩ | ⟨rfl, v, hv, he⟩
    · exact Or.inl (Or.inl (by rw [← hd, ← hand, hz, h0]))
    · exact Or.inl (Or.inr (by rw [← hd, ← hand, h1]))
    · have hve : applyMoves ms v &&& d1 = applyMoves ms w &&& d1 := by rw [← hd, ← hand, ← hand, he]
      exact avail_of_eq hve (hbb v hv)
    · have hve : applyMoves ms v &&& d1 = negD d1 (applyMoves ms w) &&& d1 := by
        rw [← hd, ← hand, he]; simp only [negD, hand, hxor, h256, hd, Nat.and_assoc, Nat.and_self]
      have hneg := avail_neg hd1 (avail_of_eq hve (hbb v hv))
      exact avail_of_eq (by rw [negD_invol hd1, Nat.and_assoc, Nat.and_self]) hneg
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1, rfl, hroots⟩
  | succ p ih =>
    intro bank hr
    obtain ⟨b, a, c, op, hop, rfl, hrb, ha, hc⟩ := hr
    obtain ⟨b', hrb', hbb⟩ := ih hrb
    have ha' := hav hbb ha; have hc' := hav hbb hc
    refine ⟨opD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
      ⟨b', applyMoves ms a, applyMoves ms c, op, hop, rfl, hrb', ha', hc'⟩, ?_⟩
    intro v hv; rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr (Or.inl ⟨opD d1 op (applyMoves ms a) (applyMoves ms c), List.mem_cons_self, by
        rw [applyMoves_opD ms hok hd]⟩)
    · exact avail_cons _ _ (hbb v hv)

theorem lower_iso {u : Bool} {d1 d2 T1 T2 L : Nat} {roots1 roots2 : List Nat}
    (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd1 : d1 &&& mask256 = d1) (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r => availB u d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower u d1 roots1 T1 L) : Lower u d2 roots2 T2 L := by
  obtain ⟨hand, _, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2, Avail u d1 roots1 (applyMoves ms r) := fun r hr =>
    (availB_iff u _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank', hrb', hbb⟩ := reach_map_moves ms hok hd1 hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v, hv, he⟩ | ⟨rfl, v, hv, he⟩
  · exact Or.inl (Or.inl (by rw [← hT, ← hd, ← hand, hz, h0]))
  · exact Or.inl (Or.inr (by rw [← hT, ← hd, ← hand, ho]))
  · have hve : applyMoves ms v &&& d1 = T1 &&& d1 := by rw [← hT, ← hd, ← hand, ← hand, he]
    exact avail_of_eq hve (hbb v hv)
  · have hve : applyMoves ms v &&& d1 = negD d1 T1 &&& d1 := by
      rw [← hT, ← hd, ← hand, he]; simp only [negD, hand, hxor, h256, hd, Nat.and_assoc, Nat.and_self]
    have hneg := avail_neg hd1 (avail_of_eq hve (hbb v hv))
    exact avail_of_eq (by rw [negD_invol hd1, Nat.and_assoc, Nat.and_self]) hneg

-- lower_slice
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

theorem lower_slice {u : Bool} {d dSub T TSub L : Nat} {roots rootsSub : List Nat}
    (hd : d &&& mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r => !r.testBit 0) = true)
    (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB u dSub rootsSub) = true)
    (singles : List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e => isConstB dSub e.1 && essOK d (T &&& d) (roots.map (· &&& d)) e.1 e.2) = true)
    (hprior : Lower u dSub rootsSub TSub L) :
    Lower u d roots T (L + singles.length) := by
  have hnc' : ¬ IsConst d T := fun h => by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T &&& d) := by
    intro h
    have e : (T &&& d) &&& dSub = TSub &&& dSub := by
      rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hws_av : ∀ w ∈ ws, Avail u dSub rootsSub w := by
    intro w hw
    obtain ⟨r, hr_m, rfl⟩ := List.mem_map.1 (hws_sub w hw)
    have hav := (availB_iff u _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub]) hav
  obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hncSub' hrun (p := 0) (bank := rootsSub) rfl hws_av
  have hTSub_av : Avail u dSub next TSub := avail_of_eq (by
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

-- poolCut (52-bit compact hint)
def runChoices (u : Bool) (d : Nat) (pool : List Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some pool
  | p + 1, bits =>
    let code := bits &&& 1023
    let op := code &&& 3
    let ia := (code >>> 2) &&& 15
    let ib := (code >>> 6) &&& 15
    if allowedB u op && ia < pool.length && ib < pool.length then
      let a := pool.getD ia 0
      let b := pool.getD ib 0
      runChoices u d (pool ++ [opD d op a b]) p (bits >>> 10)
    else none

theorem getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem runChoices_sound {u : Bool} {d : Nat} {roots : List Nat} :
    ∀ (p bits q : Nat) (bank pool result : List Nat),
      NatReach u d roots q bank →
      (∀ v ∈ pool, Avail u d bank v) →
      runChoices u d pool p bits = some result →
      ∃ bank', NatReach u d roots (q + p) bank' ∧ ∀ v ∈ result, Avail u d bank' v
  | 0, _, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices, Option.some.injEq] at hok; subst hok; exact ⟨bank, hr, hsup⟩
  | p + 1, bits, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices] at hok
    split at hok
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨hop, hia⟩, hib⟩ := hcond
      set code := bits &&& 1023
      set op := code &&& 3
      set ia := (code >>> 2) &&& 15
      set ib := (code >>> 6) &&& 15
      set a := pool.getD ia 0
      set b := pool.getD ib 0
      set w := opD d op a b
      have ha : Avail u d bank a := hsup a (getD_mem hia)
      have hb : Avail u d bank b := hsup b (getD_mem hib)
      have hr1 : NatReach u d roots (q + 1) (w :: bank) := ⟨bank, a, b, op, hop, rfl, hr, ha, hb⟩
      have hsup1 : ∀ v ∈ pool ++ [w], Avail u d (w :: bank) v := by
        intro v hv; rcases List.mem_append.1 hv with hv | hv
        · exact avail_cons _ _ (hsup v hv)
        · rw [List.mem_singleton.1 hv]; exact Or.inr (Or.inl ⟨w, List.mem_cons_self, rfl⟩)
      obtain ⟨bank', hrb', hsb'⟩ := runChoices_sound p (bits >>> 10) (q + 1) (w :: bank) (pool ++ [w]) result hr1 hsup1 hok
      exact ⟨bank', by simpa [Nat.add_assoc, Nat.add_comm 1] using hrb', hsb'⟩
    · contradiction

def checkCutEntry (u : Bool) (dSub : Nat) (rootsSub : List Nat) (LSub s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  let p := (hint >>> 8) &&& 15
  decide (s + p < LSub + ws.countP (isConstB dSub)) &&
  match runChoices u dSub rootsSub p (hint >>> 12) with
  | none => false
  | some pool => ws.all (availB u dSub pool)

theorem checkCutEntry_sound {u : Bool} {d dSub T TSub LSub s : Nat} {rootsSub ws : List Nat}
    (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower u dSub rootsSub TSub LSub) (hint : Nat)
    (hchk : checkCutEntry u dSub rootsSub LSub s ws hint = true) :
    ¬ RunD u d (T &&& d) s ws := by
  intro hrun
  simp only [checkCutEntry, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hineq, hmatch⟩ := hchk
  cases hrc : runChoices u dSub rootsSub ((hint >>> 8) &&& 15) (hint >>> 12) with
  | none => rw [hrc] at hmatch; contradiction
  | some pool =>
    rw [hrc] at hmatch
    have hsup0 : ∀ v ∈ rootsSub, Avail u dSub rootsSub v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
    obtain ⟨bank, hrb, hsb⟩ := runChoices_sound _ _ 0 rootsSub rootsSub pool rfl hsup0 hrc
    simp only [Nat.zero_add] at hrb
    have hws_av : ∀ w ∈ ws, Avail u dSub bank w := by
      intro w hw
      have hav := (availB_iff u _ _ _).1 (List.all_eq_true.1 hmatch w hw)
      rcases hav with hc | ⟨v, hv, he⟩ | ⟨rfl, v, hv, he⟩
      · exact Or.inl hc
      · exact avail_of_eq he (hsb v hv)
      · have hneg := avail_neg hdSub (hsb v hv)
        have he' : negD dSub v &&& dSub = w &&& dSub := by
          rw [← negD_mask, he, negD_invol hdSub, Nat.and_assoc, Nat.and_self]
        exact avail_of_eq he' hneg
    have hnc' : ¬ IsConst dSub (T &&& d) := by
      intro h; have e : (T &&& d) &&& dSub = TSub &&& dSub := by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
      rcases h with h0 | h1
      · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
      · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
    obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hnc' hrun hrb hws_av
    have hL := hprior q next hq (avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht)
    omega

-- covers, eval6, hw256, hk, bsr, bar, bar_all
def coversP (u : Bool) (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  if !u then
    pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem coversP_ok {u : Bool} {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD u d (T &&& d) s ws) : coversP u pairs ws = true := by
  cases u with
  | false =>
    simp only [coversP, Bool.not_false, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u1, v1⟩ hm
    have hp := List.all_eq_true.1 hpairs (u1, v1) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := runD_bits_le_mono h v1 u1 hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u1 <;> cases hv : w.testBit v1 <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  | true =>
    simp only [coversP, Bool.not_true, Bool.false_eq_true, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u1, v1⟩ hm
    have hp := List.all_eq_true.1 hpairs (u1, v1) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def unorientedCov (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem unorientedCov_ok {u : Bool} {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD u d (T &&& d) s ws) : unorientedCov pairs ws = true := by
  simp only [unorientedCov, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro ⟨u1, v1⟩ hm
  have hp := List.all_eq_true.1 hpairs (u1, v1) hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  by_contra! hall
  have heq := runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2, hp.2] at heq; contradiction

-- Fast bitmask-decorated covers
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

def opP (mp op : Nat) (pa pb : Nat) : Nat :=
  if op == 0 then pa &&& pb
  else if op == 1 then pa ||| pb
  else if op == 2 then pa &&& (pb ^^^ mp)
  else (pa ^^^ mp) &&& pb

theorem projBit_opD {dm : Nat} (hd : dm &&& mask256 = dm) {rs : List Nat}
    (hrs : ∀ r ∈ rs, dm.testBit r = true) (op a b : Nat) :
    projBit rs (opD dm op a b) = opP (maskP rs.length) op (projBit rs a) (projBit rs b) := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < rs.length
  · have hdr := hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true := by
      have := congrArg (fun v => v.testBit rs[i]) hd; simp [Nat.testBit_and, hdr] at this; exact this
    unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit, hi, dite_true, andD, orD, negD, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
        maskP, Nat.testBit_two_pow_sub_one, decide_true, hdr, hmr, Bool.and_true, Bool.xor_true] <;>
      (cases a.testBit rs[i] <;> cases b.testBit rs[i] <;> rfl)
  · unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit, hi, dite_false, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
        maskP, Nat.testBit_two_pow_sub_one, decide_false, Bool.false_and, Bool.and_false, Bool.false_or, Bool.xor_false]

theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs : List α) (acc i : Nat) :
    (xs.foldl (fun a x => a ||| g x) acc).testBit i = (acc.testBit i || xs.any (fun x => (g x).testBit i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.any_cons, Bool.or_assoc]

def colB (mp : Nat) (oriented : Bool) (p : Nat × Nat) : Nat :=
  if oriented then (p.1 ^^^ mp) &&& p.2 else p.1 ^^^ p.2

def coversD (u : Bool) (mp : Nat) (dws : List (Nat × Nat × Nat)) : Bool :=
  dws.foldl (fun acc d => acc ||| colB mp (!u) d.2) 0 == mp

theorem coversD_eq (u : Bool) (pairs : List (Nat × Nat)) (ws : List Nat) :
    coversD u (maskP pairs.length) (ws.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) =
      coversP u pairs ws := by
  set r1s := pairs.map Prod.fst
  set r2s := pairs.map Prod.snd
  set mp := maskP pairs.length
  have hr1 : r1s.length = pairs.length := List.length_map _
  have hr2 : r2s.length = pairs.length := List.length_map _
  unfold coversD coversP
  cases u with
  | false =>
    simp only [Bool.not_false, colB, ite_true]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq, List.all_eq_true]
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
  | true =>
    simp only [Bool.not_true, colB, Bool.false_eq_true, ite_false]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq, List.all_eq_true]
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

theorem score_bound {d y s ws} (h : RunD false d y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b, v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | two op ka kb hop _ _ _ h ih =>
    have hh := run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    rcases allowed_cases hop with rfl | rfl | ⟨hc, _⟩ | ⟨hc, _⟩
    · simp only [opD, beq_self_eq_true, ite_true, kept, Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc, ← hand]; exact ih'
    · simp only [opD, beq_self_eq_true, ite_true, ite_false, kept, Bool.false_eq_true, List.map_cons, List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc, ← hor]; exact ih'
    · contradiction
    · contradiction

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {dm y s ws} (h : RunD false dm y s ws) (hl : ws.length = s + 1)
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

theorem scoreCheck_no {dm y s ws} (h : RunD false dm y s ws) (code : Nat) :
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

def scr (u : Bool) (dm y s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  !u && zs.length == s + 1 && pool.any (scoreCheck dm y s zs)

theorem scr_no {u : Bool} {dm y s : Nat} (pool : List Nat) {zs : List Nat}
    (h : RunD u dm y s zs) : scr u dm y s pool zs = false := by
  cases u with
  | true => simp [scr]
  | false =>
    unfold scr; simp only [Bool.not_false, Bool.true_and]
    rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
    intro x _; rw [scoreCheck_no h x]; simp

def opsOf (u : Bool) : List Nat := if u then [0, 1, 2, 3] else [0, 1]

theorem mem_opsOf {u : Bool} {op : Nat} (hop : allowedB u op = true) : op ∈ opsOf u := by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases u <;> decide
  · cases u <;> decide
  · decide
  · decide

def nextD (u : Bool) (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        (opsOf u).any fun op =>
          let w := opD dm op a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem nextD_two_sorted {u : Bool} {dm y a b rest} {op : Nat} {ka kb : Bool} {s ws}
    (hop : allowedB u op = true) (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD u dm y s ys → f ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (opD dm op a b) = false := by
    cases h : ws.contains (opD dm op a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (opD dm op a b != 0) = true := bne_iff_ne.2 h0
  have hdb : (opD dm op a b != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨op, mem_opsOf hop, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem nextD_two {u : Bool} {dm y a b rest} {op : Nat} {ka kb : Bool} {s ws}
    (hop : allowedB u op = true) (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD u dm y s ys → f ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hop hab p h0 hd hnm h f hf
  · have he : opD dm op a b = opD dm (flipOp op) b a := opD_comm dm hop a b
    have hnm' : opD dm (flipOp op) b a ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (op := flipOp op) (ka := kb) (kb := ka) (flipOp_allowed hop) hba
      ((List.Perm.swap _ _ _).trans p) (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _

theorem nextD_complete {u : Bool} {dm y t ws} (h : RunD u dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, RunD u dm y s ys → f ys = true) →
      nextD u dm (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | two op ka kb hop h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_two hop p h0 hd hnm h f hf

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

-- Decorated fast O(1) incremental cover check!
def nextD_decor (u : Bool) (dm mp : Nat) (slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  dws.any fun da =>
    let a := da.1
    let ra := dws.erase da
    ra.any fun db =>
      let b := db.1
      a ≤ b && (let r := ra.erase db
        (opsOf u).any fun op =>
          let w := opD dm op a b
          w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
            let dw := (w, opP mp op da.2.1 db.2.1, opP mp op da.2.2 db.2.2)
            (f (dw :: r) || (slack ≥ 1 && (f (dw :: da :: r) || f (dw :: db :: r))) ||
              (slack ≥ 2 && f (dw :: da :: db :: r))))

theorem nextD_decor_gen (u : Bool) (dm mp : Nat) (dec : Nat → Nat × Nat × Nat)
    (hfst : ∀ w, (dec w).1 = w)
    (hop : ∀ op a b, (opD dm op a b, opP mp op (dec a).2.1 (dec b).2.1, opP mp op (dec a).2.2 (dec b).2.2) = dec (opD dm op a b))
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    nextD_decor u dm mp slack (ws.map dec) g = nextD u dm slack ws (fun zs => g (zs.map dec)) := by
  have hinj : Function.Injective dec := fun x y h => by rw [← hfst x, ← hfst y, h]
  have herase : ∀ (l : List Nat) x, (l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x => erase_map_inj dec hinj l x
  have hcont : ∀ (l : List Nat) w, (l.map dec).any (fun x => x.1 == w) = l.contains w := by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map, Function.comp_def, hfst, herase, hcont, hop, List.map_cons]

theorem nextD_decor_eq (u : Bool) {dm : Nat} (hd : dm &&& mask256 = dm)
    (pairs : List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true)
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    let dec := fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)
    nextD_decor u dm (maskP pairs.length) slack (ws.map dec) g =
      nextD u dm slack ws (fun zs => g (zs.map dec)) := by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro op a b
    simp only [dec, projBit_opD hd hr1, projBit_opD hd hr2, List.length_map]

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

theorem cov3_coversD (u : Bool) (mp : Nat) (dw : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    ((cov3 mp (!u) rest).1 ||| colB mp (!u) dw.2 == mp) = coversD u mp (dw :: rest) := by
  have e : ((cov3 mp (!u) rest).1 ||| colB mp (!u) dw.2) =
      (dw :: rest).foldl (fun acc x => acc ||| colB mp (!u) x.2) 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1, _, _⟩ := cov3_bit mp (!u) rest i
    rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, Nat.testBit_or, h1, List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw => (colB mp (!u) dw.2).testBit i)) =
        rest.any (fun x => (colB mp (!u) x.2).testBit i) := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.succ_le_iff, List.countP_pos_iff, List.any_eq_true]
    rw [hp, Bool.or_comm]
  unfold coversD; exact congrArg (· == mp) e

def nextD_cov (u : Bool) (dm mp slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  let ori := !u
  let cov := cov3 mp ori dws
  dws.any fun da =>
    let a := da.1
    let ca := colB mp ori da.2
    let ra := dws.erase da
    ra.any fun db =>
      let b := db.1
      a ≤ b &&
        (let cb := colB mp ori db.2
         let base0 := takeTwo cov ca cb
         let base1a := takeOne cov cb
         let base1b := takeOne cov ca
         let r := ra.erase db
         (opsOf u).any fun op =>
           let pz := (opP mp op da.2.1 db.2.1, opP mp op da.2.2 db.2.2)
           let cz := colB mp ori pz
           let ok0 := (base0 ||| cz) == mp
           let ok1a := slack ≥ 1 && ((base1a ||| cz) == mp)
           let ok1b := slack ≥ 1 && ((base1b ||| cz) == mp)
           let ok2 := slack ≥ 2 && ((cov.1 ||| cz) == mp)
           (ok0 || ok1a || ok1b || ok2) &&
           (let w := opD dm op a b
            w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
              let dw := (w, pz)
              ((ok0 && f (dw :: r)) || (ok1a && f (dw :: da :: r)) ||
               (ok1b && f (dw :: db :: r)) || (ok2 && f (dw :: da :: db :: r)))))

theorem nextD_cov_eq (u : Bool) (dm mp slack : Nat) (dws : List (Nat × Nat × Nat))
    (g : List (Nat × Nat × Nat) → Bool) :
    nextD_cov u dm mp slack dws g =
      nextD_decor u dm mp slack dws (fun dzs => coversD u mp dzs && g dzs) := by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨da, hda, db, hdb, hab, op, hop, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    refine ⟨da, hda, db, hdb, hab, op, hop, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
    set pz := (opP mp op da.2.1 db.2.1, opP mp op da.2.2 db.2.2)
    set dw := (opD dm op da.1 db.1, pz)
    set ra := dws.erase da
    set r := ra.erase db
    have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2 := cov3_perm mp (!u) hp
    have hca := cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2) ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: r) := by rw [hc2, takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2) ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: da :: r) := by rw [hca, takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2) ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: db :: r) := by rw [hc2, takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1 ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: da :: db :: r) := by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with ((⟨hu0, hf0⟩ | ⟨⟨hsl1, hu1a⟩, hf1a⟩) | ⟨⟨hsl1, hu1b⟩, hf1b⟩) | ⟨⟨hsl2, hu2⟩, hf2⟩
    · left; left; exact ⟨hcov0 ▸ hu0, hf0⟩
    · left; right; exact ⟨hsl1, Or.inl ⟨hcov1a ▸ hu1a, hf1a⟩⟩
    · left; right; exact ⟨hsl1, Or.inr ⟨hcov1b ▸ hu1b, hf1b⟩⟩
    · right; exact ⟨hsl2, hcov2 ▸ hu2, hf2⟩
  · rintro ⟨da, hda, db, hdb, hab, op, hop, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    refine ⟨da, hda, db, hdb, hab, op, hop, ?_⟩
    set pz := (opP mp op da.2.1 db.2.1, opP mp op da.2.2 db.2.2)
    set dw := (opD dm op da.1 db.1, pz)
    set ra := dws.erase da
    set r := ra.erase db
    have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2 := cov3_perm mp (!u) hp
    have hca := cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2) ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: r) := by rw [hc2, takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2) ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: da :: r) := by rw [hca, takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2) ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: db :: r) := by rw [hc2, takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1 ||| colB mp (!u) pz == mp) =
        coversD u mp (dw :: da :: db :: r) := by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with (⟨hc0, hg0⟩ | ⟨hsl1, ⟨hc1a, hg1a⟩ | ⟨hc1b, hg1b⟩⟩) | ⟨hsl2, hc2', hg2⟩
    · have u0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2) ||| colB mp (!u) pz == mp) = true := hcov0.symm ▸ hc0
      exact ⟨Or.inl (Or.inl (Or.inl u0)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inl ⟨u0, hg0⟩))⟩
    · have u1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2) ||| colB mp (!u) pz == mp) = true := hcov1a.symm ▸ hc1a
      exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1, u1a⟩)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inr ⟨⟨hsl1, u1a⟩, hg1a⟩))⟩
    · have u1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2) ||| colB mp (!u) pz == mp) = true := hcov1b.symm ▸ hc1b
      exact ⟨Or.inl (Or.inr ⟨hsl1, u1b⟩), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inr ⟨⟨hsl1, u1b⟩, hg1b⟩)⟩
    · have u2 : ((cov3 mp (!u) dws).1 ||| colB mp (!u) pz == mp) = true := hcov2.symm ▸ hc2'
      exact ⟨Or.inr ⟨hsl2, u2⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, u2⟩, hg2⟩⟩

def bar (u : Bool) (dm Y : Nat) (mp : Nat)
    (SD : Nat → Nat → List (Nat × Nat × Nat)) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (htAt idxH : Nat → Nat → Nat)
    (ori : List Nat → List Nat) (seed : Nat) (pool : List Nat) (cutHitH : Nat → Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Y])
  | s + 1, i =>
    let dws := SD (s + 1) i
    !(nextD_cov u dm mp (s + 2 - dws.length) dws fun dzs =>
        let zs := dzs.map Prod.fst
        !(scr u dm Y s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))

theorem bar_all {u : Bool} {dm T : Nat} {pairs : List (Nat × Nat)} {r1s r2s mp SD S N htAt idxH ori seed pool cutHitH cap}
    (hd : dm &&& mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j, SD s j = (S s j).map (fun w => (w, projBit r1s w, projBit r2s w)))
    (hpairs : pairs.all (fun p => dm.testBit p.1 && dm.testBit p.2 && !(T &&& dm).testBit p.1 && (T &&& dm).testBit p.2) = true)
    (hr : ∀ {v ys}, RunD u dm (T &&& dm) v ys → RunD u dm (T &&& dm) v (ori ys))
    (hcut : ∀ {v ys}, cutHitH v (hk seed ys) ys = true → ¬ RunD u dm (T &&& dm) v ys)
    (hc : ∀ s ≤ cap, ∀ i < N s, bar u dm (T &&& dm) mp SD S N htAt idxH ori seed pool cutHitH s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RunD u dm (T &&& dm) s (S s i) := by
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
        coversP u pairs zs && !(scr u dm (T &&& dm) s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz))
      have hF (zs) (hz : RunD u dm (T &&& dm) s zs) : F zs = true := by
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
      rw [hSD, List.length_map, nextD_cov_eq, nextD_decor_eq u hd pairs hr1 hr2] at hb
      have hFeq : (fun zs => coversD u (maskP pairs.length) (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) &&
          (let zs' := (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr u dm (T &&& dm) s pool zs') &&
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

theorem pickMin_runD {u : Bool} {dm Y v} (seed : Nat) (orig : List Nat) (h0 : RunD u dm Y v orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all moveOK256 && (applyMoves ms dm == dm) && (applyMoves ms Y == Y)) = true →
      RunD u dm Y v best →
      RunD u dm Y v (pickMin seed orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb

-- Bridge: directSplit!
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

def isNotGate (g : Gate) : Bool := match g.op with | .not => true | _ => false

theorem execN_reach (u : Bool) (gs : List Gate) (roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hmono : u = false → ∀ g ∈ gs, isNotGate g = false) :
    ∀ (p : Nat) (w bank : List Nat), NatReach u mask256 roots p bank →
      (∀ v ∈ w, Avail u mask256 bank v) →
      ∃ p' bank', p' ≤ p + gs.countP (fun g => !isNotGate g) ∧ NatReach u mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w, Avail u mask256 bank' v := by
  have hm256 : mask256 &&& mask256 = mask256 := Nat.and_self _
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by simp, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, Avail u mask256 bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hstep : ∃ p1 bank1, p1 ≤ p + (if !isNotGate g then 1 else 0) ∧ NatReach u mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g], Avail u mask256 bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, andD mask256 a mask256 &&& mask256 = a &&& mask256 := fun a => by
        simp [andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, orD mask256 a 0 &&& mask256 = a &&& mask256 := fun a => by
        simp [orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, Avail u mask256 (z :: bank) v) := fun z v hv => avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · have hn : (!isNotGate g) = true := by simp [isNotGate, h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, opD mask256 0 (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            ⟨bank, _, _, 0, by simp [allowedB], rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr (Or.inl ⟨_, List.mem_cons_self, by simp [opD, andD, Nat.and_assoc, Nat.and_self]⟩)
        · rw [hgi] at hlen; simp at hlen
      · have hn : (!isNotGate g) = true := by simp [isNotGate, h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, opD mask256 1 (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            ⟨bank, _, _, 1, by simp [allowedB], rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr (Or.inl ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [opD, orD]; cases mask256.testBit r <;> simp⟩)
        · rw [hgi] at hlen; simp at hlen
      · cases u with
        | false =>
          have hbad := hmono rfl g List.mem_cons_self
          simp [isNotGate, h] at hbad
        | true =>
          have hn : (!isNotGate g) = false := by simp [isNotGate, h]
          rw [hn]; simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
          rcases hgi : g.inputs with _ | ⟨i, l⟩
          · exact ⟨p, bank, le_rfl, hr, fun v hv => by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
          · exact ⟨p, bank, le_rfl, hr, fun v hv => by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi]
                exact avail_neg hm256 (hav_gd i)⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      (fun hu g' hg' => hmono hu g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    rw [List.countP_cons]
    cases hb : !isNotGate g <;> simp only [hb, ite_true, Bool.false_eq_true, ite_false] at hp1 ⊢ <;>
      exact ⟨p2, bank2, by omega, hr2, hsup2⟩

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

theorem countP_not_lt {gs : List Gate} {g : Gate} (hg : g ∈ gs) (hn : isNotGate g = true) :
    gs.countP (fun x => !isNotGate x) + 1 ≤ gs.length := by
  induction gs with
  | nil => simp at hg
  | cons x xs ih =>
    rw [List.countP_cons, List.length_cons]
    rcases List.mem_cons.1 hg with rfl | hxs
    · simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false]
      have := List.countP_le_length (p := fun y => !isNotGate y) (l := xs); omega
    · have := ih hxs; cases hb : !isNotGate x <;> simp only [hb, ite_true, Bool.false_eq_true, ite_false] <;> omega

theorem directSplit_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 256, T.testBit r.val = f (pt8 r.val))
    (hS : Lower true mask256 xs256 T (lb - 1))
    (hM : Lower false mask256 xs256 T lb) :
    ∀ t : ℕ, HasCircuitSize 8 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
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
  by_cases hhas : ∃ g ∈ C.gates, isNotGate g = true
  · obtain ⟨g, hg, hgn⟩ := hhas
    have hsup0 : ∀ v ∈ xs256, Avail true mask256 xs256 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
    obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach true C.gates xs256 hfan (fun h => Bool.noConfusion h) 0 xs256 xs256 rfl hsup0
    have hav_out : Avail true mask256 bank ((execN C.gates xs256).getD C.output 0) := by
      by_cases hi : C.output < (execN C.gates xs256).length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hL := hS p bank hr (avail_of_eq hout hav_out)
    have hlt := countP_not_lt hg hgn
    have : C.gates.length ≤ t := hsz
    omega
  · push_neg at hhas
    have hmono : ∀ g ∈ C.gates, isNotGate g = false := fun g hg => Bool.eq_false_iff.2 (hhas g hg)
    have hsup0 : ∀ v ∈ xs256, Avail false mask256 xs256 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
    obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach false C.gates xs256 hfan (fun _ => hmono) 0 xs256 xs256 rfl hsup0
    have hav_out : Avail false mask256 bank ((execN C.gates xs256).getD C.output 0) := by
      by_cases hi : C.output < (execN C.gates xs256).length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hL := hM p bank hr (avail_of_eq hout hav_out)
    have hle := List.countP_le_length (p := fun y => !isNotGate y) (l := C.gates)
    have : C.gates.length ≤ t := hsz
    omega

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xeeeeeeeeeeeeeeeeaaaa0000aaaa0000eeeeeeeeeeeeeeeeaaaa0000aaaa0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfafafafafafafafaaaaa0000aaaa0000fafafafafafafafaaaaa0000aaaa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfefefefefefefefeaaaa0000aaaa0000fefefefefefefefeaaaa0000aaaa0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffaaffaaffaaffaaaaaa0000aaaa0000ffaaffaaffaaffaaaaaa0000aaaa0000
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffeeffeeffeeffeeaaaa0000aaaa0000ffeeffeeffeeffeeaaaa0000aaaa0000
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffafffafffafffaaaaa0000aaaa0000fffafffafffafffaaaaa0000aaaa0000
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xeeeeeeeeeeeeeeeecccccccc00000000eeeeeeeeeeeeeeeecccccccc00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_101 : Nat := 0x33000000330000003300000033
def goal_101 : Nat := 0xfafafafafafafafaf0f0f0f000000000fafafafafafafafaf0f0f0f000000000
def roots_101 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_106 : Nat := 0x505000005050000050500000505
def goal_106 : Nat := 0xffccffccffccffcccccccccc00000000ffccffccffccffcccccccccc00000000
def roots_106 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffeeffeecccccccc00000000ffeeffeeffeeffeecccccccc00000000
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfff0fff0fff0fff0f0f0f0f000000000fff0fff0fff0fff0f0f0f0f000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafffafffaf0f0f0f000000000fffafffafffafffaf0f0f0f000000000
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xeeeeeeeeeeeeeeeeeeeeccccaaaa0000eeeeeeeeeeeeeeeeeeeeccccaaaa0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfafafafafafafafafafaf0f0aaaa0000fafafafafafafafafafaf0f0aaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffeeffeeffeeffeeeeeeccccaaaa0000ffeeffeeffeeffeeeeeeccccaaaa0000
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffafffafffafffafafaf0f0aaaa0000fffafffafffafffafafaf0f0aaaa0000
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffccccffffccccffffccccffffccccaaaa0000aaaa0000aaaa0000aaaa0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffff00ffffff00ffffff00ffffff00aaaa0000aaaa0000aaaa0000aaaa0000
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xffffffffff00ff00ffffffffff00ff00f0f0f0f000000000f0f0f0f000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffffff0000ffffffffffff0000aaaa0000aaaa0000aaaa0000aaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_180 : Nat := 0x1100110011001100000000000000000011001100110011
def goal_180 : Nat := 0xffffffffffff0000ffffffffffff0000f0f0f0f000000000f0f0f0f000000000
def roots_180 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xffffffffffff0000ffffffffffff0000fafaf0f0aaaa0000fafaf0f0aaaa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffffff00ffffffffffffff00aaaa0000aaaa0000aaaa0000aaaa0000
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_188 : Nat := 0x111111111111111100000000000000001111111111111111
def goal_188 : Nat := 0xffffffffffffff00ffffffffffffff00f0f0f0f000000000f0f0f0f000000000
def roots_188 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xffffffffffffff00ffffffffffffff00fafaf0f0aaaa0000fafaf0f0aaaa0000
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeecccccccccccccccceeeeeeeeeeeeeeee0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfff0fff0fff0fff0ff00ff00ff00ff00fff0fff0fff0fff00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffaff00ff00ff00ff00fffafffafffafffa0000000000000000
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffff0000ffff0000aaaaaaaaaaaaaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccffffccccffffcccccccccccccccccccc0000000000000000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffccccffffcccceeeeeeeeeeeeeeeeaaaa0000aaaa0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_213 : Nat := 0x330033000000000033003300000000003300330000000000330033
def goal_213 : Nat := 0xfffffafafffffafaffff0000ffff0000fafafafafafafafaaaaa0000aaaa0000
def roots_213 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefeffffccccffffccccfefefefefefefefeaaaa0000aaaa0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffff00ffffff00ffaaffaaffaaffaaaaaa0000aaaa0000
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_220 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def goal_220 : Nat := 0xfffffff0fffffff0ffffff00ffffff00fff0fff0fff0fff00000000000000000
def roots_220 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffaffffff00ffffff00fffafffafffafffaaaaa0000aaaa0000
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafaffffffff00000000fafafafafafafafaf0f0f0f000000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffff00ff00ffaaffaaffaaffaa0000000000000000
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0ffffffffff00ff00fff0fff0fff0fff0f0f0f0f000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffaffffffffff00ff00fffafffafffafffaf0f0f0f000000000
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffffff0000aaaaaaaaaaaaaaaaaaaa0000aaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0ffffffffffff0000f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafaffffffffffff0000fafafafafafafafafafaf0f0aaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffffffff00ff00ff00ff00ff000000000000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffffff00ffaaffaaffaaffaaaaaa0000aaaa0000
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffffffffffff0ffffffffffffff00fff0fff0fff0fff0f0f0f0f000000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffaffffffffffffff00fffafffafffafffafafaf0f0aaaa0000
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffeffffffffffffffccfffefffefffefffefefefcfcaaaa0000
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_83
def pairsG : List (Nat × Nat) := [(1, 17), (1, 65), (2, 66), (3, 19), (3, 67), (16, 17), (18, 19), (18, 82), (64, 65), (64, 66), (80, 81), (80, 82)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 16, 18, 18, 64, 64, 80, 80]
def r2sG : List Nat := [17, 65, 66, 19, 67, 17, 19, 82, 65, 66, 81, 82]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_83.map (· &&& dom_83)
def goalM : Nat := goal_83 &&& dom_83
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x677bce70
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000000000000000f00000000000000000000000000000000000000000000000c000c00000000000c000c0000000000000000000000000000000000000000000a000a00000000000a000a0000000000000000000000000000000000000000000f000f0000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xce00dc01bf00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xce9adc57bf96
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
def CN0 : Nat → Nat
  | _ => 0
def CH0 : Nat → Nat → Nat
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 1 0 (CN0 s)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_83 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_83 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_83 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_83 == dom_83) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_83 goalM v ys) : RunD true dom_83 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_83 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_83 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_83 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_83 roots_83 goal_83 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_83 goal_83 := by
    have h0 : isConstB dom_83 goal_83 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_83

theorem lowS_83 : Lower true dom_83 roots_83 goal_83 4 := S_83.noCircuit

def isoMvS_85 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_85 : Lower true dom_85 roots_85 goal_85 4 :=
  lower_iso isoMvS_85 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_89 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_89 : Lower true dom_89 roots_89 goal_89 4 :=
  lower_iso isoMvS_89 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_99 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_99 : Lower true dom_99 roots_99 goal_99 4 :=
  lower_iso isoMvS_99 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_101 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_101 : Lower true dom_101 roots_101 goal_101 4 :=
  lower_iso isoMvS_101 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_106 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_106 : Lower true dom_106 roots_106 goal_106 4 :=
  lower_iso isoMvS_106 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_108 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_108 : Lower true dom_108 roots_108 goal_108 4 :=
  lower_iso isoMvS_108 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_147 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_147 : Lower true dom_147 roots_147 goal_147 4 :=
  lower_iso isoMvS_147 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_153 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_153 : Lower true dom_153 roots_153 goal_153 4 :=
  lower_iso isoMvS_153 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_172 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_172 : Lower true dom_172 roots_172 goal_172 4 :=
  lower_iso isoMvS_172 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_177 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_177 : Lower true dom_177 roots_177 goal_177 4 :=
  lower_iso isoMvS_177 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_180 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_180 : Lower true dom_180 roots_180 goal_180 4 :=
  lower_iso isoMvS_180 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_195 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_195 : Lower true dom_195 roots_195 goal_195 4 :=
  lower_iso isoMvS_195 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_204 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_204 : Lower true dom_204 roots_204 goal_204 4 :=
  lower_iso isoMvS_204 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_209 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_209 : Lower true dom_209 roots_209 goal_209 4 :=
  lower_iso isoMvS_209 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_210 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_210 : Lower true dom_210 roots_210 goal_210 4 :=
  lower_iso isoMvS_210 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

theorem lowS_87 : Lower true dom_87 roots_87 goal_87 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc0000000000cc00cc, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_85

theorem lowS_115 : Lower true dom_115 roots_115 goal_115 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f0000000f0000000f0000, 1, 17)] (by decide +kernel) (by decide +kernel) lowS_99

namespace S_211
def pairsG : List (Nat × Nat) := [(1, 17), (1, 65), (2, 66), (2, 130), (3, 19), (3, 67), (3, 131), (16, 17), (16, 144), (18, 19), (18, 82), (18, 146), (64, 65), (64, 66), (80, 81), (80, 82), (80, 208), (128, 130), (128, 144), (129, 131), (129, 145), (129, 193), (192, 193), (192, 194), (192, 208)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 16, 16, 18, 18, 18, 64, 64, 80, 80, 80, 128, 128, 129, 129, 129, 192, 192, 192]
def r2sG : List Nat := [17, 65, 66, 130, 19, 67, 131, 17, 144, 19, 82, 146, 65, 66, 81, 82, 208, 130, 144, 131, 145, 193, 193, 194, 208]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_211.map (· &&& dom_211)
def goalM : Nat := goal_211 &&& dom_211
def NN : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x434d2eaa
  | 5, 0 => 0x746c246736ce6f9203b74642
  | 6, 0 => 0x746c2467
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f00000000000a000a00000000000f000f00000000000a000a00000000000f000f00000000000f000000000000000f000f00000000000f000000000000000f000f00000000000f000f000000000000000000000000000000000000000000000000000000000000000000000000000f000c00000000000f000c00000000000f000000000000000f000000000000000f000000000000000f000000000000000c000c00000000000c000c00000000000c000c00000000000c000c00000000000a000a00000000000a000a00000000000a000a00000000000a000a00000000000f000f000000000000000000000000000f000f0000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x46885
  | 5, 0, 0 => 0x344556b915b34456
  | 6, 0, 0 => 0x34455
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 19
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfcf839f07fe03fc000001cffc00e7c000039f07000e7c1f000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfcfb7bfd7fedffe129000e6b58ae7c8a2ab9f0f0a5e7e1f426
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 25 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 25 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 8 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 4 => 4
  | 5 => 6
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0x746c246759ccb85d0c3c09ab0427d0ec
  | 5, 0 => 0x40d489493cfa798339cb6c2f1930887606df5c4505d38d30
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x2010002
  | 5, 0 => 0x20301010003
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 4 0 (CN0 s)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_195 roots_195 4 s ws hint
  | 1 => checkCutEntry true dom_209 roots_209 4 s ws hint
  | 2 => checkCutEntry true dom_210 roots_210 4 s ws hint
  | 3 => checkCutEntry true dom_147 roots_147 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_211 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_195 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_209 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_210 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_211 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_211 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xcccccccccccccccccccccccccccccccc, 126)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xffffffffffffffff0000000000000000, 64), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_211 == dom_211) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_211 goalM v ys) : RunD true dom_211 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_211 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
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
  scr true dom_211 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_211 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_211 roots_211 goal_211 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_211 goal_211 := by
    have h0 : isConstB dom_211 goal_211 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_211

theorem lowS_211 : Lower true dom_211 roots_211 goal_211 7 := S_211.noCircuit

def isoMvS_91 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_91 : Lower true dom_91 roots_91 goal_91 5 :=
  lower_iso isoMvS_91 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_93 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem lowS_93 : Lower true dom_93 roots_93 goal_93 5 :=
  lower_iso isoMvS_93 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_107 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_107 : Lower true dom_107 roots_107 goal_107 5 :=
  lower_iso isoMvS_107 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_109 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_109 : Lower true dom_109 roots_109 goal_109 5 :=
  lower_iso isoMvS_109 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_117 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_117 : Lower true dom_117 roots_117 goal_117 5 :=
  lower_iso isoMvS_117 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_181 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_181 : Lower true dom_181 roots_181 goal_181 5 :=
  lower_iso isoMvS_181 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_185 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_185 : Lower true dom_185 roots_185 goal_185 5 :=
  lower_iso isoMvS_185 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_188 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_188 : Lower true dom_188 roots_188 goal_188 5 :=
  lower_iso isoMvS_188 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_205 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_205 : Lower true dom_205 roots_205 goal_205 5 :=
  lower_iso isoMvS_205 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_213 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]
theorem lowS_213 : Lower true dom_213 roots_213 goal_213 5 :=
  lower_iso isoMvS_213 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_217 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_217 : Lower true dom_217 roots_217 goal_217 7 :=
  lower_iso isoMvS_217 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_211

def isoMvS_220 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_220 : Lower true dom_220 roots_220 goal_220 5 :=
  lower_iso isoMvS_220 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_229 : List (Nat × Nat) := [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_229 : Lower true dom_229 roots_229 goal_229 5 :=
  lower_iso isoMvS_229 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_233 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_233 : Lower true dom_233 roots_233 goal_233 5 :=
  lower_iso isoMvS_233 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_236 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_236 : Lower true dom_236 roots_236 goal_236 7 :=
  lower_iso isoMvS_236 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_211

def isoMvS_241 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_241 : Lower true dom_241 roots_241 goal_241 5 :=
  lower_iso isoMvS_241 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_244 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_244 : Lower true dom_244 roots_244 goal_244 5 :=
  lower_iso isoMvS_244 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_248 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_248 : Lower true dom_248 roots_248 goal_248 5 :=
  lower_iso isoMvS_248 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

namespace S_123
def pairsG : List (Nat × Nat) := [(1, 17), (1, 65), (2, 34), (2, 66), (3, 19), (3, 35), (3, 67), (8, 72), (9, 25), (9, 73), (10, 42), (10, 74), (11, 27), (11, 43), (11, 75), (16, 17), (18, 19), (18, 50), (18, 82), (24, 25), (24, 88), (26, 27), (26, 58), (26, 90), (32, 34), (33, 35), (33, 49), (33, 97), (40, 42), (40, 104), (41, 43), (41, 57), (41, 105), (48, 49), (48, 50), (56, 57), (56, 58), (56, 120), (64, 65), (64, 66), (64, 72), (80, 81), (80, 82), (80, 88), (96, 97), (96, 98), (96, 104), (112, 113), (112, 114), (112, 120)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 8, 9, 9, 10, 10, 11, 11, 11, 16, 18, 18, 18, 24, 24, 26, 26, 26, 32, 33, 33, 33, 40, 40, 41, 41, 41, 48, 48, 56, 56, 56, 64, 64, 64, 80, 80, 80, 96, 96, 96, 112, 112, 112]
def r2sG : List Nat := [17, 65, 34, 66, 19, 35, 67, 72, 25, 73, 42, 74, 27, 43, 75, 17, 19, 50, 82, 25, 88, 27, 58, 90, 34, 35, 49, 97, 42, 104, 43, 57, 105, 49, 50, 57, 58, 120, 65, 66, 72, 81, 82, 88, 97, 98, 104, 113, 114, 120]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_123.map (· &&& dom_123)
def goalM : Nat := goal_123 &&& dom_123
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xf40360d26145fd4c
  | 6, 0 => 0x60d528e8
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f00000f0f00000f0f00000f0f000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f00000f0f0000000000000000000000000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000000000000000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xbd119ac6886
  | 6, 0, 0 => 0x2f6886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe38f803fe0003ffc000000000fc0fffc000003fffe00ff8000000e7c3e1fe00000000e77c7c000073801cdcfffc000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xe38fa13fe4445b6c00804004afc0fffd089093ffffacffdbdb924e7c3e1fe01249453e77c7c2492f38a7cdcfffe128944aca
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 50 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 50 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 8 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 4 => 1
  | 5 => 7
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0x9ec20800
  | 5, 0 => 0x918fd2837d052e5860d528e83ec86bce336a90d12da938d518d2c191
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x4010202020003
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 4 0 (CN0 s)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_106 roots_106 4 s ws hint
  | 1 => checkCutEntry true dom_91 roots_91 5 s ws hint
  | 2 => checkCutEntry true dom_115 roots_115 5 s ws hint
  | 3 => checkCutEntry true dom_107 roots_107 5 s ws hint
  | 4 => checkCutEntry true dom_89 roots_89 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_123 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_106 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_107 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_89 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_123 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_123 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_123 == dom_123) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_123 goalM v ys) : RunD true dom_123 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_123 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
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
  scr true dom_123 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_123 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_123 roots_123 goal_123 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_123 goal_123 := by
    have h0 : isConstB dom_123 goal_123 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_123

theorem lowS_123 : Lower true dom_123 roots_123 goal_123 7 := S_123.noCircuit

theorem lowS_215 : Lower true dom_215 roots_215 goal_215 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000f000f00000000000f000f00000000000f000f0, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_211

namespace S_245
def pairsG : List (Nat × Nat) := [(1, 17), (1, 65), (4, 36), (4, 68), (5, 21), (5, 37), (5, 69), (16, 17), (16, 144), (20, 21), (20, 52), (20, 84), (20, 148), (32, 36), (32, 160), (33, 37), (33, 49), (33, 97), (33, 161), (48, 49), (48, 52), (48, 176), (64, 65), (64, 68), (80, 81), (80, 84), (80, 208), (96, 97), (96, 100), (96, 224), (112, 113), (112, 116), (112, 240), (128, 144), (128, 160), (129, 145), (129, 161), (129, 193), (132, 148), (132, 164), (132, 196), (133, 149), (133, 165), (133, 197), (192, 193), (192, 196), (192, 208), (192, 224)]
def r1sG : List Nat := [1, 1, 4, 4, 5, 5, 5, 16, 16, 20, 20, 20, 20, 32, 32, 33, 33, 33, 33, 48, 48, 48, 64, 64, 80, 80, 80, 96, 96, 96, 112, 112, 112, 128, 128, 129, 129, 129, 132, 132, 132, 133, 133, 133, 192, 192, 192, 192]
def r2sG : List Nat := [17, 65, 36, 68, 21, 37, 69, 17, 144, 21, 52, 84, 148, 36, 160, 37, 49, 97, 161, 49, 52, 176, 65, 68, 81, 84, 208, 97, 100, 224, 113, 116, 240, 144, 160, 145, 161, 193, 148, 164, 196, 149, 165, 197, 193, 196, 208, 224]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_245.map (· &&& dom_245)
def goalM : Nat := goal_245 &&& dom_245
def NN : Nat → Nat
  | 5 => 1
  | 6 => 3
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xabe1c78
  | 6, 0 => 0xa31c25224a7f33ad17aabe66
  | 7, 0 => 0xa31c2522
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x320032003200320032003200320032003200320032003200320032003200320022002200220022002200220022002200220022002200220022002200220022003300330000000000330033000000000033003300000000003300330000000000330000003300000033000000330000003300000033000000330000003300000030003000300030003000300030003000300030003000300030003000300030001100110011001100110000001100000011001100110011001100000011000000330033003300330000000000000000003300330033003300000000000000000033003300330033003300330033003300000000000000000000000000000000
  | 0, 1 => 0x33003000330030003300300033003000330030003300300033003000330030
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x5432106
  | 6, 0, 0 => 0x54361065843610754736107
  | 7, 0, 0 => 0x5436106
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 28
  | 6 => 32
  | 7 => 28
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xff800079e7f0e38000780730001f83fe0000001c7381f800fc000001e7cf001fff81f80f001ffc00000fffe00000000
  | 0, 1 => 0xfc1c7381ffc
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ff8dbdfbeff1e38494f82f38495f83fe424424bc7391f912fc09290be7ce143b6b01d08f921ffc2084affff24245100
  | 0, 1 => 0x6fcbd7b9bffd
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 48 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 48 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 9 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 9 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 9 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 9 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 5 => 4
  | 6 => 9
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0xa31c25223edefc3118ed9c7601bcf292
  | 6, 0 => 0x5e13b4364e81419f35f166742173784f1c191e110ec17b810ca6277603da2a1400d42d07
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x1000002
  | 6, 0 => 0x20003040205030304
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 5 0 (CN0 s)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_213 roots_213 5 s ws hint
  | 1 => checkCutEntry true dom_244 roots_244 5 s ws hint
  | 2 => checkCutEntry true dom_181 roots_181 5 s ws hint
  | 3 => checkCutEntry true dom_241 roots_241 5 s ws hint
  | 4 => checkCutEntry true dom_229 roots_229 5 s ws hint
  | 5 => checkCutEntry true dom_209 roots_209 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_245 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_213 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_244 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_181 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_241 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_229 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_209 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_245 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_245 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124)], [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffffffffffff0000000000000000, 64), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xffffffffffffffff0000000000000000, 64), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xffffffff00000000ffffffff00000000, 96), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_245 == dom_245) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_245 goalM v ys) : RunD true dom_245 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_245 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
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
  scr true dom_245 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_245 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_245 roots_245 goal_245 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_245 goal_245 := by
    have h0 : isConstB dom_245 goal_245 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_245

theorem lowS_245 : Lower true dom_245 roots_245 goal_245 8 := S_245.noCircuit

def isoMvS_125 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_125 : Lower true dom_125 roots_125 goal_125 7 :=
  lower_iso isoMvS_125 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_123

def isoMvS_189 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_189 : Lower true dom_189 roots_189 goal_189 7 :=
  lower_iso isoMvS_189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_123

def isoMvS_221 : List (Nat × Nat) := [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem lowS_221 : Lower true dom_221 roots_221 goal_221 8 :=
  lower_iso isoMvS_221 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215

def isoMvS_237 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_237 : Lower true dom_237 roots_237 goal_237 8 :=
  lower_iso isoMvS_237 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215

def isoMvS_249 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]
theorem lowS_249 : Lower true dom_249 roots_249 goal_249 8 :=
  lower_iso isoMvS_249 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215

def isoMvS_252 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_252 : Lower true dom_252 roots_252 goal_252 8 :=
  lower_iso isoMvS_252 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215

namespace S_253
def pairsG : List (Nat × Nat) := [(1, 17), (1, 65), (4, 36), (4, 68), (5, 21), (5, 37), (5, 69), (8, 72), (8, 136), (9, 25), (9, 73), (9, 137), (12, 44), (12, 76), (12, 140), (13, 29), (13, 45), (13, 77), (13, 141), (16, 17), (16, 144), (20, 21), (20, 52), (20, 84), (20, 148), (24, 25), (24, 88), (24, 152), (28, 29), (28, 60), (28, 92), (28, 156), (32, 36), (32, 160), (33, 37), (33, 49), (33, 97), (33, 161), (40, 44), (40, 104), (40, 168), (41, 45), (41, 57), (41, 105), (41, 169), (48, 49), (48, 52), (48, 176), (56, 57), (56, 60), (56, 120), (56, 184), (64, 65), (64, 68), (64, 72), (80, 81), (80, 84), (80, 88), (80, 208), (96, 97), (96, 100), (96, 104), (96, 224), (112, 113), (112, 116), (112, 120), (112, 240), (128, 136), (128, 144), (128, 160), (129, 137), (129, 145), (129, 161), (129, 193), (132, 140), (132, 148), (132, 164), (132, 196), (133, 141), (133, 149), (133, 165), (133, 197), (192, 193), (192, 196), (192, 200), (192, 208), (192, 224)]
def r1sG : List Nat := [1, 1, 4, 4, 5, 5, 5, 8, 8, 9, 9, 9, 12, 12, 12, 13, 13, 13, 13, 16, 16, 20, 20, 20, 20, 24, 24, 24, 28, 28, 28, 28, 32, 32, 33, 33, 33, 33, 40, 40, 40, 41, 41, 41, 41, 48, 48, 48, 56, 56, 56, 56, 64, 64, 64, 80, 80, 80, 80, 96, 96, 96, 96, 112, 112, 112, 112, 128, 128, 128, 129, 129, 129, 129, 132, 132, 132, 132, 133, 133, 133, 133, 192, 192, 192, 192, 192]
def r2sG : List Nat := [17, 65, 36, 68, 21, 37, 69, 72, 136, 25, 73, 137, 44, 76, 140, 29, 45, 77, 141, 17, 144, 21, 52, 84, 148, 25, 88, 152, 29, 60, 92, 156, 36, 160, 37, 49, 97, 161, 44, 104, 168, 45, 57, 105, 169, 49, 52, 176, 57, 60, 120, 184, 65, 68, 72, 81, 84, 88, 208, 97, 100, 104, 224, 113, 116, 120, 240, 136, 144, 160, 137, 145, 161, 193, 140, 148, 164, 196, 141, 149, 165, 197, 193, 196, 200, 208, 224]
def mpG : Nat := 0x7fffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_253.map (· &&& dom_253)
def goalM : Nat := goal_253 &&& dom_253
def NN : Nat → Nat
  | 5 => 6
  | 6 => 113
  | 7 => 344
  | 8 => 149
  | 9 => 13
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x5bc46620497e3c093eb9614c3cac2c7c10f49a0904dfae4a
  | 6, 0 => 0x4632007345e2b8f243aca7de4041390e401f61093eb9614c3d8f8a753a1946fa36fde7bd365685f335a29eda34a520d834889d69335091293254d56c31cc77d43186b6d73144f4502f7d7c052ce1686e2b75156729f064dd294a2e9a28fdeb24215f12c12063bf621eab3ca21df9fa5b1df8ac991da1cdfa1c91d5ea1aa675f71a9e21b21a667e5916f03e5516485ad415d1b77615782bbe1448d169134ef9b9134024fa12af4ea9128525a4127e41c3125242c911fab205119eb8330fd612b90f78a8500f517d680ddca19a0dd0fa9b0d9ee2a80cb1acf00812ede806a84bcb061ead9d057f506103f99e4100cbde9700cbd44e00b3574f007da93b002a4426
  | 6, 1 => 0xe27f1392dec6dccedc4830d7dc3d4348da6bdb15d2b7b1f1ce33bd9caf674f4aaf423c75a5b6400fa4c91173a12e9d26a059788f9c5f1f54982ddefa982a98668efafe998ba205038ab66ba789bfdc0088983452879560ac85630d05836c749d81745f0b802df3f47c6f636b7b01ea44735ac6116e1447c06e00997664dbb151641c9b4063d6a671618431c9609f1b1e606c32635f62c3325f4ba62e595315135661ed8e55b201e55569f35e52af25f44e438c2b4e3ebef049e9d22b489f441148626b50
  | 7, 0 => 0xed661ae0e63d5560d7f72380d14420f0cbea4460c60c6750c4504be0c3048e00bfe27e40b00a3fb0a919a120a3d439d09f0324009e7e78109b8a3bd096840380900213108fa366108de54dd08d64e1e087f5c8b086e8e850793f646078bbc15074d5a2306abc6bb0647c8a6061f703805f5eacd05f58a4105bcf527059b06a705812aad052cc4fd05235d1c0521adcb05207ec005186760048c7df7042fdb1e041da0fb03de576a03a74f70038c8ae8034c5882030df47102cbaf88029968d1025a87cf02535294022ec55101f05de601b8777b019af5200196eeed019368620181d6dd0148a83d0128a6490106ec6400cbde97009a567d0030c9120000502e
  | 7, 1 => 0x2138acfa20cc55ed209751ae202883911efcd3681e4c0ce41e2515101e1bae101df84a481dbcc37f1dbb91941db9277c1d63e9241d5631771c8c0bbb1c3667731c2a145a1c0978e71bd1bfc31ac41fdb1ac241051a8929d219b2eae219749f85194f8cb01922d529191b115e189809991886017f181b415317f75460179520ff17936f0a16af7e2a16955dfd162efa2715f6a92515f69c6d159e1e5c1594c3451568120d153d381314e65d3214cb065d1488c4cb146b42f1144fb0da144a7ff61405843e132cde971307a1b111fd18ad11b8727511b7eec4112e4af011279ec4112412b0111b894410c37bd5109799ac10446291102866cc0f5853750f186cec
  | 7, 2 => 0x37f1596637e719fd37dab3303724bc2236b68b8d365685f3362bb7823576dc3c357157fd3496e4c434501672344a448a33f86dce33f43f4a3393be06336fe34a3308457532b2811f3262ab7d31f2589d316e547a313b84f930be0c1d307123073056a4032fec77882fe5d80d2f1441e22e82efec2e742f022d7c3eb02cd57afe2c3d1d172c349af32bb05a9b2b97d6692ae4e6b82a7159c929ff3c4b2996a1ce295943fd28a96045282ce3b227c29c23277b399a2758555d265e7cc22655006225be5a5925bdfa42259775cc25204c8d24f194f0248a52cd2452160b243cbd7924035e9c235feb0023500335221356c321f0baa821b5df88215fc0482142b50d
  | 7, 3 => 0x58e6294d58d81a375823b77d58004de357dc0a4b576b6acd57038cdb570178b255fd058655f0b0745569f35e54474ed253f4c28153d603fe530fbe9053070e035110b9024f4a5d234e5216074dddc5844d623dcd4d4b36244cad41c44c42f5354b2374ff4ad57ca44a7e1df94a5ac7cf4a5199ef49baf0ff49b228e5499ad97c4934aaee489bd8de485225cf47d1659d47cb135446a6aaeb466714544655811245daac2144916afb448311ec43dfb0e542c9f1ec422e898941fc8f4f41a35207418272a9415c078741358210400baf23400a27413e4628fd3d841c123c4302623c1b1e243adbe7cc3ab2a654395f343938e28956386bebca38671404381bcc94
  | 7, 4 => 0x9168eb5790f496df90a1a55a8c33c2eb8c2aea158bf06e1d8b6c62fc8afa330289ceb39388ee1832869866ce85aeab7184de150e846324778455681f83f57aaa83bfe9fc83bc9e6c80e1e9a7802df3f47e83f7d67de61b937d2e76fe7c864dc37c6874a67c24c5187b7c2d567b45ba5079b165c776cc127a761b82f075c62a97758a7118750cb3da74293a2b7400e5e273eca442735e16f472a19a326edc88ac6eccc4886d79e1316cee1f286cd5422c6b7b117c68c3103a6864a6fd6862872267d4bde866057c6164bd638663b7adba628fef0a614bef896007583d5fb4a90c5f8211555f03bd0f5d83c8555d453c3d5cd6953f5cb6b3505ca7e2255c98451a
  | 7, 5 => 0xecdcb08deba8bd56e222e95fd203f6cbd1ac8526c7c1d05ec4ff2c22c40e34acbd7cef7eb8ed2341b8c8106cb21f293fadf2bb37aa09bdfca9dedd74a8c6b187a55f8538a46ce7409babcce899920dc298f405a4973210e996c2df1993aeaa8f
  | 8, 0 => 0x2657cb68264d24cf2505cfee24c82d6424956abd24872beb245355b8233ff8f12286e9db2216ef3421c8c1cc2008449f1ee5b5691e7b96601e4cf9f01cc216e61b43a20b1b27a7581b0371b4181d80ae17d7a613179520ff16fb7aaf165f547214d709f514481034124946f712258dc111fbb2611109622b108aac5010110c8f100ec2c40f639f2c0e7a377b0e49ab4d0d638bf00d1229900c5582bd0c010edb0bc0583b0b9722e60a80bebc0a497cdb0a356fdf0a254d49077d0fd4074c298b06abcc3805dc2884054c29ad053dcefb0468003503fc23b603096a8c02cccd5e02651ff3025f0b3c01f7b60901b8777b00fd63a30082c63600298a9600203b63
  | 8, 1 => 0x77c16e63766848df71c0c9dc6a641bce6773eb15662ac45d6369ec4f62f526e761abedf7617070c65d1d7c905c82419d5c56ab545c31987f5a6e02195a0ee93a53ecbc7e53adf97253964e6b538e6af552609d2652278ffd51b86d7d515c434a51545c804ff8ae414f94d04b4dcc31834b818ac248f2e89a48c123d848927cd247f5fb9c47de51a7472f3cf246eeeb9a463bfbe94412941943286c7d4232c56e414727d43ea63e943ea559363d25ee753cda9f983cd362a63b68c4973b3e71963581511b3304cba932c0bcf23152337230f41d2b3006b80c2e63bb152de121ef2da5bed02cecb1f32b56bc922ae7352d2a159c6929b248fe29883c6027b5e7ad
  | 8, 2 => 0xeba8bd56daf1cbd6ce4e6ecbbfb49c23adf2bb37a878f281a46089329db5f6a39cf670d299c7dfdf8ba14efd89378ce18834da6f873b32ae809460427fa4f3837f86fc597efd29f37e4b8f8d78c106df78a38faf
  | 9, 0 => 0xc949d068b0eef66e90986cac569b1b91515c434a250c500223f5ebd81f5155a01ea0a935196d63b513a6412b10b91f0c0c726c39
  | 10, 0 => 0x13a6412b
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x330033003300330033003300330033003300330033003300330000003300000000000000000000333333333333333333333333333333330000000000000000333333333333333333333333000000003333333333333333333333330000000033330000333300003333000033330000333300003333000033330000333300003300330033003300330033003300330033003300330033003300330033003300333333333333303033333333333330303030303030303030303030303030303022222222222222222222222222222222222222222222222222222222222222223333333333333333333333333333333333333333333333330000000000000000
  | 0, 1 => 0x33003300330033003300330033003300330033003300330000000000000000003333333333333333333333333333333300000000000000000000000000000000333333333333333333330000333300003333333333333333333300003333000033333333333333003333333333333300330033003300330033003300330033000033003300330033003300330033003300330033003300330000000000000000030303030303030303030303030303030303030303030303030303030000000033333333000000003333333300000000333333330000000033333333000000003030303030303030303030303030303030303030303030303030303030303030
  | 0, 2 => 0x11111111111111111111101011111010111111111111111111111010111110100000333300003333000033330000333300003333000033330000332200003322003300330033003300330033003300330033003300330033333300003333000033333333333333333300330033003300333333333333333333003300330033003333333333333333333333333333333330303030303030303030303030303030333033303330333000000000000000003330333033303330000000000000000000003333000033330000333300003333000033330000333300002222000022223333333333333333000000000000000033333333333333330000000000000000
  | 0, 3 => 0x33333333333333333333333333333333333300003333000033330000333300003333333333330000333333333333000000000000000000000000000000000000303030303030303030300000303000003030303030303030303030303030303011111111111111111111000011110000111111111111111111110000111100003333000033330000333300003333000033330303333303033333000033330000000000003333333300000000333333330000000030303030000000003030303000000000333033330000000033303333000000003330333000000000333033300000333300003333000033330000333300003333000033330000000000000000
  | 0, 4 => 0x330033003300330033003300330033000300030003000300030003000000003300330033003300333333333333333333333333333333333300330033003300333333333232323233333333000000003333333332323232333333330000000033333232333332323333000033330000333332323333323233330000333300003333333333333333333333333333333322222222222222222222222222222222003300330033003300330033000000330033003300330033003300330000000000000000323332330000000032333233000000003232323200000000323232320000333300003333000033330000333300002222000022220000222200002222
  | 0, 5 => 0x10101010101010101010000010100000303030303030303030303030303030300303030303030303030303030303030303030303010101010303030300000000333333333333333333333333333333333322332233223322000000000000000000330033003300330033003300330033000000000000000000000000000000000000000033333333000000003333333300000000333233320000000033323332030303030003000303030303000300030303030300030003030303030000000033323332333233320000000000000000333233323332333200000000000000000303030303030303030303030000000003030303030303030303030300000000
  | 0, 6 => 0x330033003300330030003300300033003300330033003300300030003000303322332233223322332233223322332233223322332233223322332233223322333333333333333333333333333333330033003300330033003300330000000000000000303330330000000030333033000000003033303300000000303030300000000030303333000000003030333300000000303030300000000030303030000033330000333300003333000033330000333300003333000033330000222200003333000033330000333300003333000032320000323200003232000032323333000033330000333300003333000033333333333333333333000033330000
  | 0, 7 => 0x33333333333333332222222222222222333333333333333322222222222222223322332233223322000000000000000033223322332233220000000000000000333311113333110033331111333311003333111133331100333311113333110000000000303033330000000030303333000000003030333000000000303033303333332233333322333300003333000033333322333333223333000033330000000000003333333300000000333333330000000030333033000000003030303011110011111100111111001111110000111100111111001111110011111100000000000000000000323232323232323200000000000000003232323232323232
  | 0, 8 => 0x333333330000000033333333000000003333333300000000303030300000000000000000333333333333333333333333333333333333000033330000000000003333333300000000333333330000000031313131000000003030303000000000000000000303030303030303030303030303030300000000000000001111111111111111111111111111111111111111111111111111111111110000030303030303030303030303010101010303030303030303030303030000000033330000333300003333000033330000000000000000000033330000333300003333303033333030333330303333303033333030333330303333303033333030
  | 0, 9 => 0x33333333333333333333333333333333003300330033003300300030003000303333333311111111333333330000000033333333111111113333333300000000222222223333333322222222333333332222222222222222222222222222222203030303030303030000000000000000030303030303030303030303030300001111111111111111111111111111000011111111111111111111111111110000030303030303030303030303030300000303030303030303030303030303000033333333222222223333333322222222333333332222222233333333222222223300330033003300330033003300330033003300330033003000300030003000
  | 0, 10 => 0x330033003300330033003300330033003300330033003300300030003000300000000000000000003300330033003300330033003300330000000000000000333233323332333233003300330033003332333233323332330033003300330000000000333333330000000033333333000000000000000000000000333033303333333333333333000000000000000033003300330033000000000000000000003300330033003300000033000000330033003300330033000000000000000000000000000000000000000000000000333333333333333333333333333333003232323232323232323233333232333330303030303030303030303030303030
  | 0, 11 => 0x333333333333330033333333333333003333333333333333000000000000000000000000000000000000000000000000030303030101010103030303010101010303030301010101030303030000000003030303030303030000000000000000030303030303030303030303020202023333333333333300333333333333330033330000333300003333000033330000003300330033003300000000000000000033003300330033000000000000000003030303030303030303030303020302030303030303030303030303030203023333333332323232333333333232323230303030303030303030303030303030
  | 0, 12 => 0x30033000300330000003300000033000300030003000300000000000000000000333300003333000033330000333311113333111133330000222200002222003300330033003300330033003300330033003300330033003300330022002200330033003300330033003300330033000300030003000300030000000300003333333333333333330033003300330033003300330033003300330033003300111100111111001111110010111100101111001111110011111100101111001000003333000022330000333300002233000033330000222200003333000022223300330033003300330033003300330033003300330033002200220022002200
  | 0, 13 => 0x333233323332333233323332333233323333000033330000333333333333333333333333333333333333000033330000333333333333333333333333333333333333333333333333333300003333000033333330333333303333333033333330303030303030303030303030303030300033003300330033003300330033003300220022002200220022002200220022333333333333333333333333333333330033003300330033000000000000000033333333333333003333333333333300333333330000000033333333000000003333333333333333333300003333000000000000000000000000000000000000
  | 0, 14 => 0x33333333333333333333333333333333333333333333333333333333000000000303030303030303333333333333333303030303030303030303030300000000000000003030333300000000303033330000000030303232000000003030323211111111111111111111111111111111111111111111111111110000111100000000333300003333000022330000223300003333000033330000222200002222333333332222222233333333222222220000000000000000000000000000000000330033003300330033003300330033003300330033003300330033003300003300330033003300000000003300330033003300330033000000000030003000
  | 0, 15 => 0x33333030333330300000000000000000333330303333303000000000000000003333333333330000333333333333000033333333333333333333333333330000003300330033003300000000003300330033003300330033000000000033000000000000000000003333333333333333333333333333333333003300330033003232323232323232323232323232323232323232323232323232323232323232333333333333333333333333333333333333333333333333330033003300330011111111111111111111111100000000111111111111111111111111000000000000000033333333000000003333333300000000222222220000000022222222
  | 1, 0 => 0x22222222222222222020202020202020222222222222222222222222222222223333330033333300333333003333330033333300333333003333330033333300333333333333333333333333333333330033003300330033003300000033000000000000333333330000000033333333000000003333333300000000222222223300330033003300330033003300330033003300330033003300000033000000333333333333003333333333333300333333333333330000333333333333000033333333333333333333333333333333030303030303030303030000030300002233223322332233223322332233223322332233222222222233223322222222
  | 1, 1 => 0x30303030303030303333333333333333303030303030303030303030303030303330333033303330333033303330333033303330333033303330333033303330000000000000000033333333333333330000000000000000303030303030303033333333330033003333333333003300333333333300330033333333330033000303030301010101030303030000000003030303010101010303030300000000330033003300330033003300330033003333333033333330333333303333333033333333333333333333333333333333333333333333000033333333333300003333333333333333303030303030303033333333333333333030303030303030
  | 1, 2 => 0x33333333333333330000000000000000333333333333333333333030333330300000000000000000000000000000000033333333330033003333333333003300333333333333333333333333330033003333333333333333333333333300330003030303030303030303030303000300030303030303030303030303030003000000333300003333000000000000000000003333000033330000000000000000333333333333333333333333333333330303030303030303000000000000000000330033003300330033003300330033000300030003000300000000000000000033003300330033003300330033003300320032003200320032003200320032
  | 1, 3 => 0x33333333000000003333333300000000333333331111111133333333000000000000000000003333000000000000333300000000000000000000000000000000333133313331333133313331333133313330333033303330333033303330333000000000333333330000000033333333000000003333333300000000333300003333333333333333333333333333333322222222333333332222222222222222000000003333333300000000000000000000000033333333000000000000000000000000000000000000000033333333000000000000000000000000000000000000333300003333000033000000330000003333000033330000330000003300
  | 1, 4 => 0x33333333003300333333333300330033333333330033000033333333003300003033303330333033303330333033303330303030303030303030303030303030333330303333303033333333333333333333303033333030333330303333303003330333033303330033003300330033030303030303030300000000000000002222222222222222333333333333333322222222222222222222222222222222330033003333333333003300330033003300330033333333330033003300330033333333333333330000000033333300333333333333333300000000333333000033003000330030003300300033003000330030003300300033003000330030
  | 1, 5 => 0x33333333000000003333333300000000333333333333330033333333333333003030303030303030303030303030303033333330333333303333333033333330333333333333333333333333333333330000000033333333000000000000000033333333330033003333333333003300000000000000000000000000000000000000000000000000333333333333333300000000000000002222222222222222111111111111111100000000000000001111111111111111000000000000000011111111111111111111110011111100111111111111111111111100111111003333333333333333333333333333333311111111111111110000000000000000
  | 1, 6 => 0x33333333333333333333333333333333333333332222222233333333222222222222222222222222222222222222222233333333333333333333333322222222333333330033003333333333000000003333333300330033333333330000000033003300330033003300330033003300333333333333333333003300330033003333333333333333333333333333333333003300330033003300330033003300333333333333333333333333333300003333333333333333333333333333000033333333000033333333333300000000333333330000333333333333000000003333333333330000333333333333000033333333333300003333333333330000
  | 1, 7 => 0x33003300330033003300330033003300333233323332333233323332333233323332333233323332333233323332333233323332333233323332333233323332000000003333333300000000003300330000000033333333000000000000000033333333000000003333333300000000333333333333333333333333330033003333333333333300333333333333330033333333333333003333333333333300223322332233223322332233223322332222222222222222222222222222222233333333333333330303030303030303333333333333333300000000000000001111111111111111111111111111111111101110111011101110111011101110
  | 1, 8 => 0x33333333333333333333303033333030333330303333303033333030333330303333333333333333000000003333333333333333333333330000000000000000333333333333333300330033003300333333333333333333000000000000000033333300333333003333330033333300333333333333333333333300333333002222222233333333222222223333333322222222333333332222222222222222000000003333333300000000333333330000000033333333000000003300330013131313131313130303030303030303111111111111111100000000000000000000003300000033000000330000003300000033000000330000000000000000
  | 1, 9 => 0x33333333000000003333333300000000333333330303030333333333000000003300330033003300330033003300330011001100110011000000000000000000303030303030303030303030303030303333333333333333303030303030303000000000333333330000000033333333000000003300330000000000330033003333333333333333330033003333333333333333333333333300330033003300111111111100110011111111110011001111111111001100111111111100110033333333333333333333000033330000333300003333000033330000333300003333333333333333333333333333333300000000000000003330333033303330
  | 1, 10 => 0x3300330000000000330033000000000033003300000000000000000000000000000000000000000000000033333333333333330000000000000000333300333333003333330033333300003333003333330033333300333333000033333333111111113333333311001100333333331111111133333333110011003333333311111111333333331111000033333333111111113333333311110000003300330033003300330033003300330033003300330033003300330000000000003333000033330000333300003333000000000000333300000000000000003333333333333333333333333333333300000000000033330000000000000000
  | 1, 11 => 0x33333333333333333333333333333333333333333333333330303030303030300000000033333333000000003333333300000000323232320000000032323232333333333333333311111111111111113333333333333333111111110000000033333333333333333333333333333333333333331111111133333333000000003333333333333333333333333333333300000000000000003333333333330000333333333300330033333333330033003333333333333333333333333300330033333333000000003333333300000000333333333333333333333333000000003131313131313131313131313131313131313131313131313030303030303030
  | 1, 12 => 0x3333000033330000333300003333000033330000000000003333000000003333000033333333333300003333333333330000333300003333000033330000232323232323232323232323222222222323232323232323232323232222222200000000000000003333333333333333000000000000000032323232323232323333333300330033333333330033003333333333003300333333333300000000333300003333000033330000333300003030000030300000333300003333000033003300330033003300330033003300330033003300330033003300000000003333333333333333003300300033003033333333333333330033003000330030
  | 1, 13 => 0x33333333333333333333333333223322333333333333333333333333332233223333333322222222333333333333333333333333222222223333333322222222000000000000000033333333333333330000000000000000333333333333000030303030303030303033303330333033303030303030303030303030303030300000333300003333000033330000333300000000000000000000000000000000333333333333333333333333333333333322332233223322332233223322332200000000000000003332333233323332000000000000000033323332333233323311331133113311331133003311330033113311331133113311330033113300
  | 1, 14 => 0x33333333333333333333333333333333333033303330333033303330333033303333333333333333333333333333333323232323232323232222222222222222003300330033003300330033003300330030003000300030003000300030003033333333333333330000000000000000333333333333333333333333333300003333333322332233333333332233223333333333222222223333333322222222303033333030333330303030303030303030333330303333303030303030303033033303330333033303330333033303330333033303330333003300330033003333333333333333111111111100110033333333333333331111111111001100
  | 1, 15 => 0x33113311331133113311331133003300331133113311331133113311330033003333333333333333333330303333303033333333333333333333303033333030333333333333333323232323232323233333333333333333222222222222222230303030303030303030303030303030333333333333333332323232323232323333333333333333333333333333333333333333333333333333333333330000333333333333333333333333333333333333333300000000333333330000000033330000333300003333000033330000333300003333333333330000333300001111111111111111111111111111111100000000000000000000000000000000
  | 2, 0 => 0x33333333333333333333333333333300333333333333333333333333333333000000000011111111000000000000000000000000111111110000000000000000333333333333333303030303030303033333333333333333020202020202020233033303330333033300330033003300330333033303330333003300330033000000333300003333000033330000333300003333000022220000333300002222000033330000333300003333000033330000332200003322000033220000332222222222222222222222333322223333000000000000000000000000000000003333333333333333333333333333333332323232323232323232323232323232
  | 2, 1 => 0x33333333333333333333333333333333333333333333333333333030333330300303030303030303030303030303030303030303030303030000000000000000000033330000333300003333000000000000333300003333000033330000000033333300333333003333330033333300000000000000000000000000000000000000333300003300000033330000330000003333000033000000333300003300333300003333333333330000333300003333000033333333333300003333000003020302030203020302030203020302030203020302030203020302030203020000000000000000333333333333333300000000000000000000000000000000
  | 2, 2 => 0x330033003300330033003300330033001100110011001100000000000000003333333333333333333333333333000033333333333300003333333333330000222222222222222233333333333333332222222222222222333333332222222233330000333300003333333333333300333300003333000033333333333333000000000000000000333333333300330000000000000000003333333333003300333333330033003333333333003300333333333300000000333333330000000033333333333300003333333333333333333333333333000033333333333300003300330033003300333333333333330033003300330033003333333333333300
  | 2, 3 => 0x33333333333333330000333300003333333333333333333300000000000000000033003300330033002200220022002200330033003300330022002200220022333333333333333333333333333333333300333333003333330033003300330000330033003300330033003300330033000000000033003300000000000000000303030303030303030303000303030003030303030303030303030003030300003300330033003300330033000000000033003300330033003300330000000000000000000000003333330033333300000000000000000033333300333333003311331133113311331133113311331133103310331033103310331033103310
  | 2, 4 => 0x30303030303030300000000000000000303030303030303030303030303030303300330033003300330033003300330033333333333333333333330033333300323232323232323200000000000000003232323232323232000000000000000000003333000033330000333300003333000003030000030300000000000000003333333333333333333333333333333300320032003200320032003200320032222222222222222200000000000000002222222222222222222222222222222233333333333300003333333333333333000000000000000000000000000000003333333333333333003300330033003333333333333333330033003300000000
  | 2, 5 => 0x33333333333333333333333333333333111111111111111111001100110011002222222222222222333333333333333322222222222222223232323232323232111111111111111111111111111111111111111111111111000000000000000000330033003300330033003300330033003300330022002200330033002200220000000000000000333333333333333300000000000000003333333322222222333333333333333333333333333333330303030303030303030303030000000033333333332233223333333333223322333333333322332233333333332233223333333333333333333333333333333333333333003300333333333300000000
  | 2, 6 => 0x333333003333330033003300330033000033330000333300000000000000000303030303030303000300030003000303030303030303030000000000000000003200320032003200320032003200320032003200320032003200320032003200000000333333330000000000003333000000003333333300000000000000001111111133333333000000003333333311111111111111110000000000000000232323232323232322222222222222222323232323232323222222222222222203030303030303030303030303030303000000000000000000000000000000000000333300003333000003030000030300003333000033330000000000000000
  | 2, 7 => 0x333333333333333333333300333333000000000011111111000000001111111100000000111111110000000000000000313131313131313131313131313131313030303030303030303030303030303003030303030303030000000000000000030303030303030300000000000000000000000000000000333333333322332200000000000000003333333333223322000000000000333300000000000033330000000000003333000000000000000033333333000000003333333333333333333333330000000033333333000000003333333333333333003200320032003233333333333333330032003200320032
  | 2, 8 => 0x33333333333333333333330033333300333333333333333333333300333333002233223322332233223322332233223322332233223322332222222222222222003300330033000000330033003300000033003300330000003300330033000000000000000000003333333333333333000000000000000033330000333300003030303030303030333333303333333030303030303030303333333033333330313131313131313131313131313131313130313031303130313031303130313033333333003300333333333300330033333333330022002233333333002200220000333300003333000033330000333300003030000030300000303000003030
  | 2, 9 => 0x30333033303330333030303030303030303330333033303330303030303030303333333333333333333333333333333322332233223322332222222222222222003300330033003300330033003300330033000000330000003300000033000033333333331133113333333333003300333333333311331133333333330033000303333303033333030303030303030300003333000033330000000000000000333333333333333333333333333333333333333333333333333333333300330000330033003300330032003200320032003300330033003300320032003200323333333333333333333333333333333300003333000033330000330000003300
  | 2, 10 => 0x111111111111111100000000000000000000000000000000333333333333330000000000000000003333333333333300330033003300330033323332333233323300330033003300333233323332333233333333333300333333333333330000333333333333003333333333333300003333333333333333000033330000333333333333333333330000333300000000333333333333333333323332333233323333333333333333333233323332333200000000303330330000000030333033000000003030303000000000303030303333333333333333333333330000000033333333000000003333333300000000
  | 2, 11 => 0x3030303030303030303030303030303020202020202020202020202020202020000000000000000030303030303030300000000000000000000000000000000333303033333030333330303333303033333000033330000333300003333000000000000333333000000000033333300000000003333330000000000333333000303030003030300030303000303030003030300030303000303030003030300333303033333030333330000333300003333030333330303333300003333000000003333000033330000333300003333000033000000330000003300000033000000000033333333000000003333333300000000333300000000000033330000
  | 2, 12 => 0x33003333330033333300333333003333330033003300330033003300330033003333333333333333333333332222222233333333333333333333333322222222000000000000000033333333222222220000000000000000333333332222222201010101010101010000000000000000010101010101010100000000000000000000000011111111000000001111111100000000000000000000000000000000000033330000333300003030000030300000333300003333000030300000303000000000000000003330333033303330000000000000000033303330333033303333333333333333111111111111111133333333333333330000000000000000
  | 2, 13 => 0x33333330333333303333333033333330333333303333333033333330333333300000000000000000000000000000000032323232323232323232323232323232000000000033003300000000000000000000000000330033000000000000000000000000000000000033003300330033000000000000000000000000000000003333333333333333333333333333333333333300333333003333330033333300000000000000000000000000000000003322332233223322332233223322332200330033002200220033003300220022003300330022002200330033002200220000000000000000000000000000000033333333333333333300330033003300
  | 2, 14 => 0x3333333300000000333333330000000000000000000000000000000033003300330033003333333333333333330033003300330033003300330033000101010101010101010101010101010100000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x48340602008018120d06020020060481010010302d8120401804140660481010010381980a040180802006
  | 6, 0, 0 => 0x48104c03040040ce250200c102308039c1224018204610073824080800888200e70200c1001108401ce0904004401007839c0a1f0182002100f382408030e870200e70d80c10010d0401ce0401820021908039c12040182002060c382408030405c200e70480c10010b0401ce0902054100108039c12040a04c02120738241001088401e0e7
  | 6, 0, 1 => 0x481010011b8401ce09020d8280811801c1204040046a101638241a0304004001e70200c10011a0401ce0d01820023308039c120304004641007380c100118868200e7048c01001038401ce090200c5e1c08039c1204018045c100738240808008405a2c70200c1001158401ce0902004541005839c12040184c022907382408011409c200e7
  | 6, 0, 2 => 0x2481408030408c00e0404120024708039c12460200c1001003810060800914200e70481006080081888e090200c104308039c1204018048410073904060800868200e7049000803040040ce09020207e3e070b1c0a3d0182002100738100608008f0200e7048ec0608118401ce0401820023a08039c12040182072100738240838040041e0e7
  | 6, 0, 3 => 0x4810020a0802c1ce050200cb00108039c1204008a0200b07381010012b91c200e704810060800800ace000481010010302d812042a8204610073810060800950200e70481010010014c16e0902020021029039ca2090200c1001083824080328070200e70481010012784058e4e0200c104d08039c1204018049810073824080325928200e7
  | 6, 0, 4 => 0x481010010819c1ce0902020380708039c120304004cc10073824080800994200e7048101001320401ce090218c10010002dc120401820c410073824060800984200e7048200260100401ce5f04810060800841c0803040048e002f3824080300974200e70481006012e0401ce3001820021a08039c125b04004205a073824080300964200e7
  | 6, 0, 5 => 0x2810060811840e4e090200c382808039c120404004d6002d38240808009c4200e702020021a380401ce09021bc1001080b1c126e0200c1001033824da040182002067048101001038401ce090202002000302dc1204040040e002f38240803040040c56704834066c008401ce0902020026b081a9cd20d01820021007382408080080016687
  | 6, 0, 6 => 0x481010011483858e090200c10010302dc12041300c1001003824080800800165670481010013e8401ce09021f0060800801c1204019ec1001033824087a01820020670200c10793c0401ce000481010010303d8ee040182002100f38240803009d8200e70182002203a8401ce0401820381a08039c123001820e8100738240608009cc200e7
  | 6, 0, 7 => 0x240808008000c0f7
  | 7, 0, 0 => 0x48111c0346804200e846138080304004200e800024080300a2c200e704a28080304004200e844824080304004200e80481006880421c200e804a18080800840d40e804810060800a14200e804810060800a10200e804834088304004200e841024080304004200e804810060800a04200e80002408030405c200e704810060840004200e804810061300840fe0e83f024600304004200e8
  | 7, 0, 1 => 0x4810060800a70200e80481006084d804200e804810060800801342c804a38060800880200e8048100601140401c998000240803041d0200e704810060800a60000e804a5c080304004200e84b02408030408c021084a824080300a50200e824824080304134200e8048100613040040093804810068847804200e804810100108249220e804810060800a40200e804900080347804200e8
  | 7, 0, 2 => 0x481006081180420ad8048101001081681cac8000240803042ad540e7048340803042a4200e80481006130400420a8853824080304004200e804900080353004200e804a94080347804200e804810060800841480e80481028030428c200e804811440304004000e804810060800a84200e804810061300a80200e84f810060811804200e8028100608008401c9e8048113a0304004200e8
  | 7, 0, 3 => 0x240808008001e5e7048c0061304004200e80481010010802c300e80481168b304004200e80200cf61300868200e8048111c03098040010859024080304070200e8582c4080304004200e802824080347804200e804a181a0304070200e8048340808008001e0e8581dc080304004200e857824080304004200e804810067b0408c001080480c102310041540e804ab8080304004200e8
  | 7, 0, 4 => 0x48117c0309804200e84601408b304004200e8048100608008417a0e85e024080304004200e804811660800800200b85d82408b304004200e859024080304004000e80481006085d041540e804810060800ae4b40e80483408030405c200e80487c0803041d0200e804810060800ae0200e85b824060800880200e85b024080304004200e8582d4080304004200e8049001a0309804200e8
  | 7, 0, 5 => 0x48106c03042e8200e804811900304004200e804b1c080304004200e804810060800b19260e8048340803040058a0e8028240803008a0000e804810260800840160e85802408030428c200e8048340803041d0200e804b10080304004200e804810060861804200e804810060800b08200e804810067b46804200e804810060800841820e804810060800841800e80002408bf04004200e7
  | 7, 0, 6 => 0x4810100169000200e804810060800841a20e804810280309820020085802408030400420d0867810061304004200e802824080800800160e8048101001082a19c0e804810067b04004005e804810f40304004005e804810067b66804200e802810060800b30200e804810100100040162c804811960304004200e802810060800b28200e804901920304004200e85b824080304004200e8
  | 7, 0, 7 => 0x4810060800b74200e86e024080304004200e80282408030408c020086d824080304004200e804810f608008401e0e86d364080304004200e80481006d804004200e80481010010802dae0e846024060800880200e80481006080081c200e80480c100110041ac0e804b54080304004200e804810060826841540e804a18080800800b40e86a024080304004200e869824080304070200e8
  | 7, 0, 8 => 0x2810060826804200e8048117ce901820020e804811d00304070200e804834060800b9c200e80481010010003d260e858025cc0304004200e8048340808008401e0e80481006e5008a0200e8048111c036f804200e80481006e404004200e871824080304004200e804b88061304004200e804811c20800800200e804810060800b80200e804811be0824004200e800010060800b78200e7
  | 7, 0, 9 => 0x200cf60800b78200e804810100135840b40e804810063804005ac0e804811100800840160e804900080800840160e879824080304004200e8048117c0344004200e804900080379004200e804811e20304004200e804810060800bc0200e877824080304004200e877024080304004200e876824080304004200e804810280376004200e8048100601140401ceb804ba8060800880200e8
  | 7, 0, 10 => 0x24824080347804200e80481006080e000200e804bf808030405c200e846014083604004200e80481006087e804200e80481006fc04004200e87d824080304004200e87d025f20304004200e804810060800b15260e8048100601140401cf8804a1808f704004200e80481006087b004200e8048106c0800bd4200e8048102803040058c0e87a024080304004200e83b824080800b48200e8
  | 7, 0, 11 => 0x4810280304070200e804810067b04005ad0882f8250c04018200210804834080304004002c883824080304004200e800024080800840a40e7048100608118420c0e804810060800c14200e8460240836040fc200e804812080309804200e824824060800c0c200e804acc060800c08200e80481006080e0401d0180200e000800b78200e804811fe0304004200e8248140803008a0200e8
  | 7, 0, 12 => 0x5d824080800840b40e80481006880428c200e804810061300800210e889024083604004200e888824080304004200e888024080304004200e80480c100108800200e804c3c080304004200e8048100608008021c5e804900080309804210880481028030400400f8804810060800c34000e8048340608008401d0c802810060800c2c200e804c28080304004000e8048101001848401c2c8
  | 7, 0, 13 => 0x4810060800c68000e8048102803040058a0e804811be08008401e0e804c64088e04004200e804812300304004200e800024080800b14b40e7048100608008422e0e804810060800800165e86ca18080304004200e88b024080304004200e88a824080304004200e88a024080304004200e80481006df04004005e80044c120404004b40e7000247a0304004200e70481010010803e1c0e8
  | 7, 0, 14 => 0x89024080800840b40e804850060800880200e804810060800842480e804810060800c8c200e85a824080304004000e804810068804488200e8580240803040042121804810060800c80200e804810060800c7cb40e80481010018f0401c2c8048123a0304004200e804811ee0304004210880200c102300b78200e804810067b098fc200e804810060800842380e804810060800c6c200e8
  | 7, 0, 15 => 0x4810060800cb0200e80481006df008421c0e895824080304004200e804810063804004000e804a1a140304004200e8048100601950a0200e894814080304004200e8048101001081a8160e802824080304488200e894024080304004200e80017c12040182002107048106c0393804200e804c98080304004200e8048100608118424a0e8048d8060800c08200e8580241a0304005ac0e8
  | 7, 1, 0 => 0x24080800800b42c704a183e0800840b40e804810060800842680e80481026080095c200e804810060800842660e804810061399004200e8048101001000401731804810067b440fc200e804810060800842600e8048100601140401c2c804810060800cbc200e804810060800ae5260e804810072e04004200e804811660800840160e804810061304070200e80481006081f8425a0e8
  | 7, 1, 1 => 0x4810280304005720e846364080304004200e800024080300a50200e70480c260800880200e804810073d00842780e89d824080304004200e804810068804070200e804810060800842740e802ce4080304004200e87d024060800c0c200e83f024080304004200e8048106c1404004000e804810060800ce0200e8048100608008426e0e8048100608008426c0e80481006081fcd4200e8
  | 7, 1, 2 => 0x49b4600304004200e802810060800d14200e858026880304004200e80002408080081c200e704d0c080304004200e804810074204004200e8a0824080304004200e804834060800d00200e804cfc080304004200e8048117c0304004520e8048106c0800840160e804811d2033d820020e80481110080095c200e8048106c030408c21088048100608008427c0e8580141a0304004200e8
  | 7, 1, 3 => 0x4810060800842960e8049000808008401e0e804810067b47804200e8048100613008421c0e80200dbe080091c200e8a5024080304004200e804900080304004005e8049b4080800840160e80200c103f00868200e80200c260800b78200e804810060800d24200e8048100700040042108804810060800d20200e804d1c080304004000e804810114600840160e824814080304004000e8
  | 7, 1, 4 => 0xaa024080304004200e804810f60800840160e804810f40800840160e804810060800d4c200e800024080800840160e704812a40304004200e804900080304005ad08800024080800800165e700010060800d44200e7000001204018200206658540080304004200e804810067ba7804200e80481006080080127318048100608a7004200e8048111c0800d34200e8a6024080304004200e8
  | 7, 1, 5 => 0xab024080304004200e804810100100040160e80002408030400400067049b4080304070200e804810067b04004520e804811d20304004200e8000240863018200200704812aa0304004200e8
  | 8, 0, 0 => 0x4810067b04004200e844be8121f0200c10010803a400090681006080e0401d00004810060800d70200e800024080304006b61007412412040a00c10010803a40009ad0100608008401d0b0048100608008401c5e900024080304006b21007400012040182003580803a0008c028100608008401d00044824080304004200e8049b41a0401820021007480176090200c10010803a012040182046010855c1d209022cc060800800200e9
  | 8, 0, 1 => 0x24080304006be1007402408034402002100757a4000004810060800800bce090200d1008008401ceb9448243e04018200210074801b2090200c10010803a000000480c1001100401ce09068100608008401d0890002409440182002100743e812040182002106b03a5f409068100608008401d200048101001081681c2c8000241a04018200200074000135d0200c10010803a012860200c1001083581d20004a1808b304004200e8
  | 8, 0, 2 => 0x4810060811804205a074ac01204018200210070b241204018204601082681d2090f8111c0304004200e904810068804004200e7c48016e090200c10010803a00a090200c100108039d720004810060899004200e800024080304006c4100742c012045980c10010803a40009025840608008401d0bb46024080304004200e900024080304006c01007400012040182046105503a0000902050060800b581d00089024080304004200e8
  | 8, 0, 3 => 0x2408038002002100740001204018211a010803a000094307c0608008401d000b2824080304004200e80002408030400400930740001204470200210070b201204018207e01000401d2fa04810060811804200e904810067b04004216407492412040182002100758e412040182002109e039d720004811440304004200e8048106c0304004001007480012043d00c10010803a000090200c10014c0401d009068111c0304004200e9
  | 8, 0, 4 => 0x48111c030408c0210074d980a090200c10010803a400090200c10018f0401d0090200e007b04004200e9460243e0401820021007482408033d82002106b03a4126d0200c1001000401d209200100608008401c5e90002408ea01820021007400000090200c10016b421c12040182002109e039f12000481006cd04004200e8048116603098200210074a540a090200c10010803a400090200c1001082a01d12924824080304004200e9
  | 8, 0, 5 => 0x2408036f82002100744a412041b00c10010803a400090200c1001b48401d0090200d1008008401c2c904900080304004200e164ac012040182002102d03a40009025a00608008401d00058014080304004200e800024080304004210e074024081401820021007422400090259c0608008401d0fa04810280304004200e900024081401820020007400012040182174010803a012040182002104983a632b204834080304004200e9
  | 8, 0, 6 => 0x1412040182002d60740240814018200210074c6512b0048100608008401d209022cc060800842780e95dac01204018200210074800130a0200c10010803a000090202002000803c1d00004810060800800200e8000250c0447020021007423012040182002104983a40009b58100608008401d00004812d40304004200e800024080304004200b07400012040182003400803a00a09022cc0608008401d2777d024080304004200e9
  | 8, 0, 7 => 0x259204018200210074000136f0200c10010803a000090200c7008008401d00004810076e04004200e80002408630182002100742301204018200210b683a400006c8100608008401ce0004810060800c68200e8048340803040040010074824087a0a00c10010803a400090200c1001628401d009020500608008401d6c904810067b040040010074824087a0182002000803a412040182002109e0385936624824080304004200e9
  | 8, 0, 8 => 0x58024081401820021007482408030982046010803a40049028100608008401d0090f810068804004200e904811eeb30182002100748241a040184c10010803a412040182002000802c1d20004810060800cd4200e804a18080304004213c0748268e860200c10010803a6cc090200c103f008401d20004810067b44004200e804810060800800210e0748001204018200200080b2012040182002102d039f1209200100608008401d089
  | 8, 0, 9 => 0x4810100100040160e800024097101820021007402480040182002000803a41204019ec10010803ae120000024080800840160e7
  | 9, 0, 0 => 0x48100608008401c2c8048100608008401c5e804900080304004200e804810280304004200e804810060800800200e804810060800841ac0e804834080304004200e80487c080304004200e804810067b04004200e8048100608008401d72800024080304004200e7048100608008401d318048111c0304004200e8
  | 10, 0, 0 => 0x24080304004200e7
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 58
  | 6 => 67
  | 7 => 76
  | 8 => 85
  | 9 => 76
  | 10 => 67
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffffffffe1c00003f000000fffffffc0000000000003e0003ffffffff80000000000007878fe000fff80000000000001e3f81fc0fff000ff00000000003c79fc1f01e1e000000f1e0003c739fffffffff0000000000000
  | 0, 1 => 0x1ffffe00000000000000003e0003fffff0007ffc0000000000000f1fc0fe07ff80ffffffffe0000000000001f00ffffffffffc0000000000003fc07ffff8000000003fc0000000000f1e7f07c
  | 0, 2 => 0xf8780fffffc001fff0e019ffffe1e1c07ff0001fffcfffffffffff0007ffc00007c0007ffff1fc0fe07ff80fffff000000001e3cfe0f80000000000000000000003ffffc3c380f1e0003c739fc0007fff0000000000000
  | 0, 3 => 0xffffff0f1fc001fff000000000000000000000000000000000000000078f3f83e7c0007ffffe000fff8000000000fffffc001fff00001ffffe000000003c79fc1f3ffffc000000007ff3fffe7ffff87870000000000000
  | 0, 4 => 0xffffffffe1c07e000000000ffffffffc7f03f81ffe0000003fc07ffff80000000000007878fe000fff80000fffff000003c78000f1ce7ffffffffc380fc00000003ffffc0000000078f3ff3ffffff800001e3c00078e73
  | 0, 5 => 0x1e3cfe0f9f00ffffffffffc00000003ffffc00000000000000007ffff80000000000000000fffff000000001ffcffffff00ffffffffffc000000000000000000000000000007c0007ffffffff00000000
  | 0, 6 => 0xffffffffe0000003c000f80f0f00003c7ff3f81fffcfffffffff8701f800000007ffff807f00000f1e7f07cfffff000000001e3cfe0f9ffffe1e1c07ffc001e39cfffffc00000f1e0003ff3f800007ffffe000fff80000
  | 0, 7 => 0xff878fffe03c78000f1ce6000000000000000000000000003ffc7f0e1fffc38c07ffff800000000f1e7fffc00000f0f1fc001fff00001ffffe01fc00003c79fc1f3e0003fffff001fffc000003ffc000001e3cf1e7fe7f
  | 0, 8 => 0xfffff00fe00001e3cfe0f80fffffffff8003ffe00003ffffc03f8000078f3f83e0003fffff0000000000000f8787fffffc387fff00001f000fffffffffc00000000000000007f0007ffc000003fc07878fe000fffff07c
  | 0, 9 => 0xffffffffe0000003c000f9f0001ffffffffc00000003ffffc00000f1e0003c739fc0007ffffffff0e180000f8000fffffc387fff00001f0001ffffffffc386000001e1e3fc07ffff8003c73980000000000000f007f000
  | 0, 10 => 0xffffffffe0000003c000f80fffffffc00000000000000000000078fe07f03ffc07ffff800000000ffe7fffcf800000000000000000001ffffffffc000000000000000003ffffffffffffffc003fff800000000f1e7f07c
  | 0, 11 => 0xfff1fffffffffff01f000000000000000000003e001fffffffff800000007c0007ffffffff00000e0300000f0f1fc001fff00001f0001fffc0000000000003e01e3ffffffff870007c183ffc000000000f1e7f07c
  | 0, 12 => 0xffffffffe0000000000001ffffffffc078f0001e39cfffffffff8701f80000039fffffffff0e00000180000f80000001e3f81fc0fff01f0f01fffff8003ffe00033ffffc3c000fff8003c73980000000001e0000078e00
  | 0, 13 => 0x1e3ff9ffcffffe0fffffffff8003ffe00003ffffffffff0007ffc000003fc0000000000f1e7f07cfffff000000078000000e7ffffffffc000000000000000003fc07ffff800000007c00000000000000000000
  | 0, 14 => 0xfffffffffffffe00000001fffffffffffffc00000003ffffc0000000078f3ff3ffc3c3fffffe000fff80000fffff0f0e03c78000f1ce60f0f000000000000000003ffffffff8701f80fc000000000000000000f007f000
  | 0, 15 => 0xf0f0000000000000000001fffffffffffe00003ffffffff8000000fc000003ffffffff1fc0fe07ff8007ff8000003c79e3cffcfffffffffffc7f03f81ffe03e0003fffff0e1800000007ffff80000000000078e73
  | 1, 0 => 0x7800000003c78000f1ce600001e1e3fff03fffffe03ffffffff8700000fc00007ffff807f0000000078e73000000001e0001fc000001fffffffe3fffffffe00003ffffffffff000070c00007ffffff800fe3f00078e73
  | 1, 1 => 0x7fff000000001e3cfe0f80ff000003c7f03ff9ffff01fffc0000000078f3f83e000007f80ffffffe07ff80f8000ffffffffe0000000000001e1e3fff03fffffff3fffffffc7fffffffc00007ffc07fff00000f1e7f07c
  | 1, 2 => 0xf8000fffffc001ffffe0f800001fe03ffffff81ffe03e0003ffffffffff03ffc07c0007ffffffff0e000f80f80000f0e0000000000001ffffffffc0000000000003ffffffff80000000000007ffff80000003c01e0007f
  | 1, 3 => 0xffffffffe00000001ffffe00000000000000003ffe1c00078fe07ff3fffe7ffff807f00000fff80000fffff00fe03c78000f1ce7f000001fc00000000000001fffc00000000000000007c000078701fc00007ff80
  | 1, 4 => 0xffffffff1ffffe03f00001ffffe000000003c79fc1f01ffffc3c7f0007ffff83e7ffffffff000000000000007fff000003c78000f1ce7f000001ffc7f03f81ffe03e0003fff800007fffffc003fc078780e00001f8007c
  | 1, 5 => 0xfff1fffffffffff000ff01e1e3fff03fffffff3ffffc03f8000000000000000000000000000000000007fff000003c78000f1ce7f0001fffc0000000000003e0003fffff0e07ffc38c07ffffffff0000000000000
  | 1, 6 => 0xfffffff01ffffe000f1ce60f0f1ffffffffc001e39cfe0003ffffffff80000000000007ffff1fc0fe07ff80fffff0001e3f81fc0fff01f0001fffffffffffe00003e0003fc3fffff80000000000007ff8ffffffff80000
  | 1, 7 => 0x1e3ff9ffcffffe0fff00003c7ff3ff9fffffffffc03f8000000000000000007fffffffffe07ff8000000fff1fffffffffff01ffffe0000078f0001e39cfe01fffff80000000000007c3c38000f01c0ffe0718c
  | 1, 8 => 0xfff80f0f1fc001ffffe0f9ffffffffc0000000000003ffffffff8000000000000000007ffffffc0ffffff80fffff00fe03c78000f1ce7ffffe01fc00003f81ffe03e01fffff80000000000007ffff87870000000000000
  | 1, 9 => 0xffffffffe0000000000000000000000000000001fe03fff8000078f3f83e7ffff800000000fe07ff80fffffffffe3f81fc0fff0000001fe03f870ff801c603e0003c3c7f0007ffc00007ffff8000f1fc0ffe7fffc
  | 1, 10 => 0xfffff00fe000000000000000001fffc0000000000003e0003fffff01ffffc00007c0007fffffffffe007180f8000ffffffffffff00001ffffffffc380fc00000003ffffc00380000000000007ffff80070000000000000
  | 1, 11 => 0xffffffffe00001e3cfe0f9ffffe000000003c79ff9ffe1e1ffffff0e1800000007fffffffffffff00000000fffff0001ffffffff0000000001ffffffffff81ffe0000003ffffffff800000007ffc3ffff00000f1e7f07c
  | 1, 12 => 0xfffff0f0003ffe00000001fffffe1e3f8003ffe00003fe1e3ffffffff8003c73983fff800001e3cf1e7fe7ffffffffffffffe00000000000000003f8003ffe000000000000078fe0000000007ffc07fff0e00001f8007c
  | 1, 13 => 0xff878ffffffffffc0fffe60fffffe03ffffc001e39cc1fffc0007fffffffc000003fff800000000f1e7f07cfffff00000000000000001ffffe0003c7ff3f81fffcc1ffe000078ffe7ff3fffffc0007ffffffc0ffffff80
  | 1, 14 => 0xfffff0001e3f81ffcffff9ffffffffc078f0001e39cfffffc0000000000f0003e7c0007fffffffffff80000fffffff01ffffe000f1ce7fff001e1c00003c79fc1f3e01ffffff8fe07f03ffc07c0007ffffe1c3fe007180
  | 1, 15 => 0xf8000fffffff87fc0fff01fff01fffff8003ffffc1f3fe1fffff80f1e0003c73983fc07fff01e3cf1e7fe7ffffffffffffffffff00001ffffffe03ffffc0000000000003c3fff0007ffc00007c3c380000000000000000
  | 2, 0 => 0xf8000fffffffffffffff01f000001fc0000000000003e01fffff80f1e00000701fc0007ffff1fc0fe07ff80fffff0f0003ffe000f1ce7ffffe000007ff0001fffcc1fffc00000000000000007ffff800001e3cf1e7fe7f
  | 2, 1 => 0xffffffffffc001ffffe0f9f00fffffc0000000000003e00003c380fff800000000000000000000000000000000000f0003ffe000fff01f0001e1fff8003ffe00000001e000078ffe070007c183fff80000000000000000
  | 2, 2 => 0xffffffffe0000000000001f0001ffe3fffffffe000001fffc0007ffff8003c739800007878fffffffffff80000000001ffffffc0fff01ffffffe03ffffc000000001ffffffc7fffffffc0000000000000fffffffffff80
  | 2, 3 => 0xffffffffe0000000000001ff0f1fffc000f0000001cfffffc3c3f8fe07f03ffc07ffff807f0000000000000f8000fffffff801c301f01f0001fffc380fc00000000000000007ffe07fffffc07c3c38000f1fc0ffe7ff8c
  | 2, 4 => 0x1e3cfe0f800001fffffff03fffffe000000000000000000000007ffff87870000000000000fffff00000007803c000fe000000000078f0001e39cc1fffc00000000000000007ffffffff0e03f00000000
  | 2, 5 => 0xfffffffffe0381fc00e3000fffe0000078f3c79ff9ffe1e1ffff80000000000007ffffff800e03f0000007307fff0001ffffe000f1ce7fffffffffffffc000000001e1e3fc07ffffff03fff9ffffffffffffff00000000
  | 2, 6 => 0xfffff0f0e0000000000001f00fffffc00000000000001ffe00000001e00f0003ffffff807f0000000000000ffffffffe0000000000001ff0f1fffc078f0001e39cfe01fc00000000000000007c03f87870000000000000
  | 2, 7 => 0xfffffff81ffffff01f0f0e01fc0000000000003ffe1c0000000078f3f83e7c0007fff0000000000000078780001ffffffc0fffe7ffffe001c00000000000001fffffc07ffff800000007fffc7fff0003c01e0007f
  | 2, 8 => 0xf8000fffffff81ffffff01ffffffffc078f0001e39cc00003ffc0701f80fc000003fff8000fe000fff8000007f800001fff81fffffff9fff0e0003c0703ff9fc7f3ffffffc07ffff80000039fffff8000000000007f07c
  | 2, 9 => 0xfff80fffe00001e3cfe0f9ffffffffc078f0001e39cffffffc3c0700000fc00007c0007fffffffffe07ff80f807f0f0e0000000000001fffffffffffffff81ffe03fffe3fff8001e00f0003ffffff878701fc00007ff80
  | 2, 10 => 0xfffe0000000000000000000003ffffffffffe001ffe000078ffe7ff3fffffc0007fffffffffff80000ffffffffe03ffe00000001ffff1ffffc7ff3ff9fffffffffc0000000078f3f83e7c0007f80fffff00000000
  | 2, 11 => 0xf807f000003c7800001c06000fe00000000000000003e01ffc3c7f0007ffc000000000007800000ffffff8000000f0f1fff801c301f01f0001fffff8003ffe00003ffffc00000fe00003ffc07ffff807800000fff80000
  | 2, 12 => 0xfffff0001e3f81fc0fff01ff0f1ffffffffc001e39cc1e1e00007ffff8003c739fc0007fff0000000000000f878700000000000000001fff001e1c00000001fc1f01fe0000078fe07ff3fffe7c3c3ffff0000000000000
  | 2, 13 => 0x7f80f0f1fff81fffffff8000000000078f3c79ff9ffe000003f800000000000003fff80000000000000000ffffff0f1fff81ffffff00000000003c7ff3f81fffcc1e1e3fc00701f80000039800007ffff1fc0fe07ff80
  | 2, 14 => 0x1ffffe000000000000000001fffc00078fe07f03ffc07c00380000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xdf776bbb61c07403f000b60777eeeff266cb3659b72bf9993ffffffffb2619a77208897878fe408fff88211208894449e3f81fc0fff01aff6d554ab4d9fe7dfc1f03e1e044489f1e0917c739fffffffffc99b2cd966dca
  | 0, 1 => 0x20889444983301980cdb01fffff11022448a24512403f554bfffff64c7ffd536df1ddfe664f9fe2ff17ff80df776bbb61006403200095d00ffbbb76f6e83040360a08893fc07ffff902088120bfc0111224245f1e7f07c
  | 0, 2 => 0xf0782eeedd8183dba0e1197ddda1e1c06fd8001df7ab7dddaeed9f21d19fc412dfe664fffff1fd0fe87ffcafffffaaa55a6cff3eff2f868800ccd90220112089322fbbb43c380ddb0003b6f57e2207fff40890448224ca
  | 0, 3 => 0xffffff8f1fea55fff996238666d11022448a244000005540088912122f8f1d83e782817776ec080edd0208841112f5fbfd931fff10d26fbbb601480000366dba560f772401b000006fd377ec5f7768787019b200066dca
  | 0, 4 => 0xdf776999214074022000044777eeeffe7fcbfe5fff2a79993fcdfffffb0619a372eaa979fbfec18fffaa65bfffff999337e7d367f9ee7bccc9776c380fc030001b97776802d8000069df772ddf776848101b3600074d62
  | 0, 5 => 0x1050022244848be3c760f9d00ffbb936f6e830402603fffff776e4cd9668b36e16fbbb444008022011000007dddb00fe00001bf7ddfb7900edbb276f6e800400008f1101ddfa044822411265740326eeddbdba04000482
  | 0, 6 => 0xdf764bbb60806e03c000fc5f1f2aab7cfff3f8bfffcfffffeeedc789fc4ea24b72eee9005b00000d1b6e05a3ddc9002400001a34dd2b17ddda1e1c06fdc001df7bafbbb42c180dbb8003beb7208897bfffec98fffaa6db
  | 0, 7 => 0xffc78fffea7d78ad5f5df658080aab5022411008930b84e5ffbe7f2e5fffc79ca9eee4801600000d1a6edd86d152f5fbfd931fff54da6fbbb6016c0000366dba56b41c1bab976001f6e8000601ddc00003766db36dda35
  | 0, 8 => 0x7dddb00fe00001bb6ddbb40777eeeffff6ebfffbbf6df776c03b000006edb74ec0001faaadc99b20c100d82f0787eeedd8387dba0e319d00cfbbb76f6e8304016090444a0205f2045dbc4108abfc9797afe64dfffff27d
  | 0, 9 => 0xfffffbbb71a26f13e892fde4c49ffdbffffd9304c2b1ff7ec46489f1e4d9fe7b9f40206eed52c9806080683f0706eeedd8387dba06119d00edbbb76f6e838601a0e3e9f3fc4fffff9937cf3b90444a224e1bc0fc07fd80
  | 0, 10 => 0xdf776bbb61806e03e000fc0666c666c200c806400128f3325ddff8fe87f43ffe53eeed8040000009b34cb10fc440ccc88110088044901bccc9776c000c80200012800001ddfbb76ebb75db7f8fffe911225367f1e7f97c
  | 0, 11 => 0x7778eddbaedd76d6bf8881110000000000000038009f7726dedd060800c0740206eed52c9806080683e3bbff8f1fea55fff99623b8881776c000400200012ba01f7776ededd070407c1cfffe5512ad367f1e7f87c
  | 0, 12 => 0xde664999200064000000057dddadedd06ed9121db7ab7dddaeed8701f80fc003fefbbb4cc90a03a01180003fccc9ccc9e3f81fc0fff01a0e05d5cbb0007b74000327b9b03c080dfb80038e3310444a224d1f80de07ef80
  | 0, 13 => 0x777eeddbaedd76dfe8777fefffff6ebfffbbf6fffffffffffedd7fff77edbbfcdd152ad345f9f7f97cdf77699921407c027000e7fffff776e244ca2651252b8eefffe07ffffd4aaac927eaa944408800089100000
  | 0, 14 => 0xffffffffffffffdbaefbddd77ffbbb76f6ea34513608f77240098000068d376ad783c3f776ec182edd06188bee6c0f0e0356c000e59d51f4f9100224488001020037dddaeed8701f80fc003f90444a22440880dc06ed80
  | 0, 15 => 0x54400f2f480000890440918666dfffffffffffeedbff7554aeed8000800dc002d81ddfbbbff9ff2ff97ffca1fff833366fcfbe7dffcfffffffffffe7fcbfe5fff2bc1813bbb760e1b26018463eeed8049000009b3ecf53
  | 1, 0 => 0xf840111225c38245f0ce6c3337e9f3fff23fffffe47ffffeeedc789d44fe24adbeeed807f00000dfbeefdb208894449e3b01fc0ddf01beeedffe3fffffffe648d7fffff776ededd478e27c1effbf5dc91fe3f137f8e77
  | 1, 1 => 0x17fbf22255a6cff3eff2f86ff12ccdbd7f17ff9ffff00eefc000569b3dcbaec9a51556ffa4ffffffe47ffa4e0024ddc9b7b740800010041112ecfbdff37fbbffff7fffffffc7fffffffeed9afffe07fff64ad5f5e7f4fe
  | 1, 2 => 0xfc440fffeeddbaedd76dfe00000ee91dbb75d90eda93fbbb7ffffffffff63fff774036eeeddbdba0e000f82bc4400f0e0112000044995fffffbbb7266ca3451360b7ddda66484019008800016fbbb5ddb0e03f01f8007f
  | 1, 3 => 0x82224ff6dffffec98261587999200000000000112403dfe3fbbb7efe3fffbfffe3eeed807f00000dfbeefdbfffff99ff37e7dbf7fdff6f888001fc00001120893280666c00000000448a24805e664878701bd000077dca
  | 1, 4 => 0xdf776ffb1ffffe43f2206bbffed5548b099fc7dfc1f15feffcbd7fbb7fffffdbeffbbb6eed488b2051004820fbff111337e7d367f9ee6f999289ffc7f03fa1fff2bf776ffffa04486fdf77edabb89595a0e00d01f8007d
  | 1, 5 => 0x82224ff79ffffeedd76d6a2ff00ecf9dbb37dfbfdbf7ffffe23fc489166cb36e551556c400891228804490003bbf000136e5d367b9663e0801ddd90020112008223c160fbbb760e076e838c47fffff776c91a2cd946988
  | 1, 6 => 0xfffffff93fffff76ffbeee1f0f0eefddfbf5dbbefbff79993fedfffff9060883710444bbbff1fd0fe87ffcafffffccc9f3fc5fe2fff01feeedfffffffffffeedbfef9993fc3fffff90219a776199b7ff8ffffffff99235
  | 1, 7 => 0x20889777feffbbfddffffe7fff2eeffdfff7ffbffffdf554803f8000022c91265411127fbffffff76c3b6eee3bbffff9fffffffffff6bbfefd33246f8f84cfe39cff11fffffe4cd9264916e5783c3f776ec1c3edd0718c
  | 1, 8 => 0xfffd2faf5fcc9bffffe4fbfbbb7fffd022433659b72bfdddbfffa445922c9126530ccdfbfffffd8ffffffdb7fdfb11fe27c79bf7fdff6fbbb601fc000037e5bbf2be11ffbbb648d1264814c44f3320583000320000004a
  | 1, 9 => 0x82224ff5bffffe4882294c411128893046033011a6005fe01ddfb256afaf3fa7f3eeed806400000df16ef80fdddbffffe3fa1ff2fff954050bdc93b070fb101c613f554be3c7f2047ffc4108fffffc440bd767bb75db34
  | 1, 10 => 0x5d55200b6000000320009400000eefd022411208932b7dddbefdff21ffffc413ff9352fff6fffffecc171acf2726ffedfffffdba26159beeed776c380fc074001bafbbb420380891000336e57ffffc4478912289166dca
  | 1, 11 => 0xfffffffffdb7effbeffbfcfbbb6016c000036efbbd6ff1f1fffff64e9f6e93ae77fffffff6fffffedd579acfffff88817eedf76fbb66b4555bfeffffffffb1fffba08893fdffffffb2619a777bfc3f776ec3c7fdf7f1fc
  | 1, 12 => 0xbeeed0f00037ee000ab248fbbb7e1e3f9023fff32c47be1f3776edfdf0b17c77981ddf8000bf76fbb7ddb35df776ffb7ffffe43a220dc822254142f9023efe208448222511278fe07603bec07fba97fff4e89d45fa24ff
  | 1, 13 => 0xffefdffffffffffddfffff1f7fffe27ffffeedff7ddc0eefc0005fbb7ddbeed9a8bfdb11122c267f1f7f07cbeeed08000224400089201fffffbbb7efffbfcffffcc0eee40005bbb6ddb6ed9af86c5f776fdfc0ffd7ff88
  | 1, 14 => 0xfffffeeedfbfcfffeffff9fffffbbb76fefa7cff3fcf7dddaaa90601380f8003e7e2207fff76edd76ebb6ffdff7eff93ffffe66ff3cef7ff805e5c92b57c79fd3fba23ff776fcff97f0bffc17e362ffffec9d3ecc275ce
  | 1, 15 => 0xf0e8deeedfbf87fd8fff19fffa5fffffbb77ffffdbffff1fffffedfdf2f5fd7fd8bfc03bbf76eddf7eff6fffffffffffffffffffffffffffffff03ffffea55564910444bc3fff2047ffd536df83c3c4408810289104100
  | 2, 0 => 0xfffffffffffffffffffffee080001d80000112008223f11fffffededd274d17e5f4464eeedf1fd0fe07ff82beeed0f02037ee000ebacd7ddda1a1406fd8001df7883ebf400000891000224807ffffdddbbff7ffbffff7f
  | 2, 1 => 0xffffffffffffffffffffffd00ffbbb7266c83040360af99903c380dfb80019a7730ccdc0408910089144900a2aad0f08037ee000efb48faaa5e1fff9023ffea9b6ca01e5556e9edc070407c181ddf80008912289144900
  | 2, 2 => 0xdf776aaa41004403200011feeedffe3fffffffe648d43effc444dffbfddbfefbba1ddff878ff76ffffddb3502aad00017eedf748bb649beeedff03ffffc854440930eeffffc7fffffffeed9a91ddfa224fffefff7fffb5
  | 2, 3 => 0xfeeedfffe83364890cdb95be8e1776c080f002a001effffff3f3fcff97f8bffe56fbbb445b080220190004ae805bdddbb7b301c301f07bccc9776c380fc030001b80666c0005fba45dbeed88f87c7f776fdfc3ffd7ff8c
  | 2, 4 => 0x1440022244848ae1c760f841112eeffdff63fbbfff6c71100ccd80408204112255f7768685019b200044d82fffffbbb71e27f13f892fe1808022244b87048ae19cf0eefe22044891448a24807fbbb7fff4e8bf45d224ee
  | 2, 5 => 0xfffffeeedd23c5db28f3101f7fe2226ffdfeedff7ddfc1e1fbbb640c166c830c46fbbb5dc90e03f0178007703bbf00017eedf76fbb66bfffffbbb76f6ea3451360abebf7fd6fffffff37fffbfffffffdbfffffa9d5596e
  | 2, 6 => 0xff7768f8e1116402244995d00edbbb5222c8104012087ddc0ccd8301e80f4003fbe664807f0000044866dcafdddbeeec801019b28d311df0f1bbb54faf058be3bcfa01fe22044891040804805e2368787019b200022dca
  | 2, 7 => 0x777eeddb0edd76db6e0b0601d80000336418623dfe1eaa9561a3fcfbf8be740206eed408900400048203abd00017eedf74dbb66a79992001c000000019b72a0eefffc07ffffd4aaac927fbb87fff468bd45ea24ff
  | 2, 8 => 0xfdddbfffffffb1ffffffb7bfefd776c6f8f84efe39ef0ccdaeec0701f80fc001a81ddf8000bf52abb7ccb1117f9b22257ee9bf7fff6fbeff0fdddbb0f1ff7dfc7f37dddbfe4fffff90bc883bdf7768502013670007796c
  | 2, 9 => 0xdffc0bbb6484abe3cfe0fdfffff776e6fcfa6eff3def7dddae2c0701500fc0008f9756fff6ffffffec7ffacfc47f8f8f1336410245b95ffffffffffffffff5fffbb7ddc2eed8301e80f4003ffffffc7c789bf289177dca
  | 2, 10 => 0x666c80100890041100777e0002fddbeedf76cd48eee51127bff6ffb7ffdaefbbb7ffbffffffff9927ffeeedfffe837ee890efbddffff3ffffdfff7ffbffffd777480290000068db702c7f3327fc0fffff20411024
  | 2, 11 => 0xe807f999337a7414301e060007e00022448820402403a45ffe3c7fa957ffc4588b0ccd807c00000dfbeef916001bd4d9b7b101c301f03d22a5fbf7fb263ffe21a4efbbb430200df10003bec03eeed807800000dfbccb11
  | 2, 12 => 0xbeeed4c49e3fc5fc0fff01ffcf9ffffffffddbbefbfc0e8f00005fbb79936cd1af00006664400800400008070583008000001122082017dd801e1c02b54001dd3b80ee240005aba2ddb2ed9a7e3e3ffffc8992cd9265ca
  | 2, 13 => 0x77f9bf6fdfff9bfffffffa00000666cdb975cbaed9fd7110002d80000004000250199b00000802201100000ffffffcf9fffd5ffffff2200000aab5cbb71d8aedbce3c9d2ec48701f8034003b800003bbf70ed07683b6ca
  | 2, 14 => 0xfbbb6010000002245124008eefd1127cff17f8bffc070003c4408810208100100
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 87 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 87 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 371 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 371 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 371 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 371 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 5 => 8
  | 6 => 223
  | 7 => 1041
  | 8 => 509
  | 9 => 16
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0x86cd3da075015e9e73f7b3883486cc9b192c443a18911a6d095d2bf60417d867
  | 6, 0 => 0x15daf6c4156fa56f1538324714e09bd1144a7ff61406c0e514026b5e13a6412b139b064b12b65bd012a95373121445a411db7376114026e210ad67e610a0bea51099bfdf104c3e600ffd54110fcab9760fc97b4a0e7a377b0e4eb5d70de365b50db05da30da727d50da52d6b0d8b49a60d5d7cd10d136b7d0cdae46a0cbd88870cafbf720b2cf8260ad19f830a765fbd0a5debc709e11c6909c481aa08e590ff08dc8c11080a290d07a2e4d5079f979e074a0b4e07427ca2072e069606fdb4f706c70ba7068fb2b00651b84105b58679050b474f03d0efad03c8201003aba9dc031faa92030260bb0287cc48018d966f0151201600ee64a900a5bbe20053c882
  | 6, 1 => 0x371a4ba036440d393630bbd734de90bf34d7477d3252f66831d76274318a14c530c03bf030702906306be9372f97f96f2eec4f282ebbbf092e927ddd2e0a432d2d61817e2b1e28142a8e21a429e0a4cc28d89d4a28bf6f472889ffa627f18564279870402791858c276822aa262ad3ef259fe65624dbcc4623ed74d623d6afd12391d28c2381d3c222c5457122c4d7cd225f32f91f03cb2f1ed01a181e402ee81e04dfcd1df647a11d29358c1c5f20961c2af0461c2522131c1cde0a1bdce54b1b29000e1b218ee21b0c968f1a47a0b119f2afd7199d55b91970b99e190d959118dd8b4518ca23b5186fcad217d34330179607181785bf33176112f116d2cee8
  | 6, 2 => 0x71f6595f71db7a9d70017a196c1827f76922282a645683f66453606764355030615810e1612ac0346056c6905ef2b3675e28c9365d3686f55d02c0535c49e26a5c26ab435b9e563a5b4f9b775a6fa0fa58a81ded57d6b6a3565e694e564396e254674964539c0388513922e65022290f4f2c82e94f2a76d74d988c364d4b04b94c55e32e4b7b45694b11713b49c4b16c48167d0747e5d2cc47aaa09c475c0b2946ce286f4612ccad4611674845d925a745af3ef24503a99443e02cc5420f980841b59c834182546f40f1b7a140512654402001863d7faf1b3d6cf8ce3cfa4c733c8690c33b0f21a93a3247533a12207d39a470803997a0483969ab5937c2ccb7
  | 6, 3 => 0xe41910ade267ebabdef2b139d70b3f3ccd9e2c3ac67630f2adb04d9caa9a2e59a7cf7ad9a4a5ddd4a28dcbbea16d6aa5a0c0b0099dfaad799519fc7e9424035b90049ceb8fbeeadd8da758b08557d2ad820b7a5b81fc28987edde8c37bee28127b35db467b13d5f077ffc7d077cabe217613ee0c738582d07377b075
  | 7, 0 => 0x4dd1f9104d5b56704cc554304a5b5950490e1cc04805e300462f7e50441c53e043ae4910411a6c503ed355803eb575903d0efad03d008de03cccfd403c6da7403bf801f03b68cff0383818d03751d4b036905e303363eaf0327d7260326612803124efe02f85a2402f447be02e2d83002dc3e2e02d47ac302beb6ab02bb730002a58c40027d2118026a5c57021e44fe021835a201d5f7aa01bfb49d01b8de0001a16e110198a5c6018670770181ba6201812fb7016cee740130281f012e74ff012d7705012022850115dfaf010bf92b0104054400e0de9c00d3b8fc00beb3a400b9467500b2a19200580419004b6cd1004576730034b9950034b41b001c8039
  | 7, 1 => 0x8ee044608c342c308bea10508be045608841d2f085b31c2084effb0082e78bb08268a5508259db4081630830810128208009d5408001d4b07e8e0fb07c50ec307b9860c07ad705107a18d1507801f39077d401c0748e79507466289073a481c0736b7d407332f0607273c3f071f5251071ac97606f4982d06e0c67006db9c4406cbdb7b06c10d6c06bf143206b772dc06a28ffc06825c4c067681af065ec9e80650cb56064bf35f063fdb60063f504406104de30602011b060184f305fa6f9105f324fd05f0498f05c6ddf205c2d3b505c0ff5405b19388057e8ddc0579cd090573dd4205726081056d16b305673bf805536e2105510a710543366605047fce
  | 7, 2 => 0xe4bd2f70e4ac9430e2bd7760e1a84f10e0d023b0e05ca000e00a98b0e00a82c0de245920d685f7d0d2a27840d14c7470d0f40f10d078c3c0cf59ab80cea78060cd146e50ccec7790cce966c0c8ca8d60c8c50950c88fa160c6b0f2c0c5c6e570c5416370c3387060c25c8970c1c64a20c1720bc0c06321b0bea1d2f0bc0583b0bbf3e670b8e24840b704f320b68ec6c0b53b0020b4f49300b3c550b0b1e573a0b1d786f0ac2c12b0ab78d4a0a6da4a10a1a6fa50a0ff83c09ef5edf09e553ce09ddae440980296409797a3d095c0f8109552c3f09532cf80941339109398ebf092ec6ff092bb89109142cd8091335750910517708fca55e08f635ee08ee7ba3
  | 7, 3 => 0x14026b5e13fc657713a6412b13a07bc5137784d713446c6b1339a8e912ffab3612fc66c612ce0bb412bf8dc812beca3812b65bd0129af558129abcc6124946f71213da2f1210b041120ce17c11feff8111e331b111dd784d11c3331611b8170411a1b5351174d289114026e211235f26111cfc6a111775421101f01710ed4e7910cf21df10b91f0c10a7794810a3c7981091f50f108aac50107a6f7d105a65dc104f0bc4103c15951038539c1021b40b1018f781100bfbab0fd9c7970fd1dd9f0fc7fbcf0fc59ef90fb9ed060f5d71c50f23a19e0f160c3b0eebe9f00eebd4200ee034780ec0faa00eb9c1a70eb436fc0e7a377b0e778d910e73d6420e53408d
  | 7, 4 => 0x1a63a54a1a5d151b1a4739f01a2e54fc1a254bf01a0bfcd719f6d78f19a1d066198d6737196d63b5195fee88194ec2cf1913e1d718fadec718f8461a18dde019188064cc185b3633185825ea184df6f01824ec90181e112b1808763218082d24180377cf1800a58f17cc7b181793afb0178c81d11745fbdd1714b40917123a3316f8d02f16a7a710169e662c168c06681681914a1669a55a16183ba215cd8d4015bcff09158d28211577476115258a491508bdef14ed757b14ebcf7d14dc081414db763714b6bac014b1dbf31498119a1496c976148569f5148547111470758e146e41091467c1da1455fa24144339fe144002b1141cf52014185d5014111422
  | 7, 5 => 0x1fd3bc1d1fcb5cfa1fc096401fad7fd31f95994a1f67f42a1f57400e1f5155a01f31e8121f104c941f05b36a1f03cb2f1ef21c8c1ec9e2281e977a6f1e91ad3b1e90fd0b1e5a02401e39e20a1e308c6a1e2e858a1e2a97471e289b341e16ce931ddeea931dd83d1b1dc446181d9085981d62df641d3b2cd71d3606de1d2d44191d20bde31d115f591cfd83ac1cf3a0b41ce4b7a61ce409021cbce9c01cbb9bb41cbabd491c75aa3a1c5f9f7c1c5710ea1c4aae221c27188c1c12aa401c0d17a61bd6c3e31bc608881b8e26e81b7b31971b61fd431b58dc941b56be731b33899c1b2f91141b19059f1b168e571b06ab891adb0fb91acbb7c41aa0b9b51a6f4018
  | 7, 6 => 0x25e93df725e4c2b325dd983e259ed8b92565b0ab2557537c254eeba7254e1b822546561325393d50251182c6250c500224f28e9124ede2cc24e82a3424c82d6424c135e5246e910b246c6cb824686c5924619e97245d8d63243649cc2424e6b62401743e23f5ebd823bbb3fa23aa2ec723678e11234ead782328a6c922efc00522ddd6aa22c4f1482292a58c2281c5fb226a212b225f731922475f12221d87a1220a8514220330e721ebd54c21b9af3e218c5ae32183f1e2217de33f21637bd4215e1304215d65022159c79621469f4c2146351d211c0f7a20f78c5d20e3ef30209204a9207bb655207aadf6206ac845206467b8202fe39f1fea13461fe18ea6
  | 7, 7 => 0x2e02cc2a2dfeeef02de057bf2dc652bd2d8c29f62d6b7abb2d5a47e52d1033072cd25f2c2cbc37812ca43d2d2ca3a92d2c74cf192c72891a2c3d74f92c2f21562c29114c2c250cff2c18381e2bd8dc9e2bb9dd1b2ba7c7aa2b9870932b972bb22b9483ef2b88d0972b6b57792b624f7a2b3519a22b1c78302af2a2f62ada9d3a2aca5def2aa9f6202a85df082a6191022a3940012a3053dd2a17ae7729ba765429ae52e529a22366295622d82904e91f28f1d2a628cab14a28791acc2826532328261114281c419f27d4927127d111bc27cecb6827522df027090b2127011649270059e32698a52d26589a58264d24cf2641c9a9262592212605f42625f199ec
  | 7, 8 => 0x36c0bd3536ade367367cf9563669bad1363151ca362cf92d36255b9035b9bcdc35a13c2f358e53b93546392f34ed23f234ea1fd534cf2dd034cd88f434c0fdc3348fe1e73473ea93346b3569345aba4a33e9704633d2f596332d934f332279ba331c23e632f3dc4e32d3d7ff32ac42ca32a48fdb3283c6e3324c734c320b6ad13209e8113208058531fc3f2831fac1ed31ed39bf31c29df931b0ff22312c2a4230f35e6e30ced06530ae2c673098980a304cd6a63022e07130124c912ff9d2c12fd6ddbe2fa1ab582f9f2dc92f6baacd2f13bdc82f0a6adb2efb8abd2ed63d502ed04e032ecd62062ec684342e7f7b552e7080c72e6ddd082e658dc02e4b5f35
  | 7, 9 => 0x3dc8a7fe3dadfb563d64258c3d3c5ca03d01f2d83d01af4e3cf0982c3ce060cc3cdec5f43cc92c993c91fa383c3d53483c1142013c0255fc3be4dbae3bdf6af33b4fde723b4acc8d3b3564903af5a8263acb94fb3ac780d93a7b05183a1e9ec33a12207d3a08bf693a02f67039eec83639e6bfee39d5d8ff39cd082239c00e3c39b658ba395b97ad39492c8d393af3d63932600538dacd0338c2f63938a938cf38a75fe7385941c03857246838228c88381fedae37f9957437f64e5837f349d037b8c33237b62a4337a8c3bc378ebb71377c62ef377416c7376e325a3760d64a374694fa3735e39e373487c2371f718d371370f6371363d83705f4db36fd7e25
  | 7, 10 => 0x482aafd04802a27647ab24614796fe764792a534473fa58a46fd3fd846f90ad546c9304446c32c1446116748458f47844566ca834524288a44fd31a444ee261044a94cad449c2b88447dc911442da5f54423b77c43fb640543f2757b4374435c434d99d9433b6d16432b2e9f43286c7d430617df42da3d2e42cbcb8942a56cb742888457426add3042511d6d42326815420844634202a9004201314c41efae9f41de1a0941b837f641b59c83415436894122be844120ebbd40f1b7a140b53b454097b92340854ee4404b224e401d42e0401098aa400054763fa5eabb3f2950ca3eea801d3ed388333eb29d083ea5b7bf3e66ec973e4d9ac73e4b1ab53deaecf6
  | 7, 11 => 0x52960ea2526e011f526a6b5c5259c57a52526b91524fa724520289ee51d8ca7851c88516518bc8e0517e808b5172ce47516f11e15143079850fcca9350a6992f509a835b507b6f825042b29c4f9d5f414f94d04b4f83f67c4ed3939c4eb031e74e9687c64e91d28a4e8698894e750fc94e425a774e2270ba4dcc31834dbb97614d3906b54ceedc9b4cbaac244c8e98024c3790c04c31f6814c1cb1404c149f584c0ef6074befabc04be69b4b4bbde7614b750f524af1210e4af111264ae9c39c4a909cd14a6b3fdb4a499b3d4a29a99849dbffac49d8452149cb6919498c968c497fe698496d23c04965560c49571aa6494bdc6a48af297e48ad7e944857a852
  | 7, 12 => 0x5df8fcf95d4883a15d42e74f5d3b940f5d04f54f5d02c0535cf574575c6f39f55c5e1d495c36175d5c2d78395c1d005e5bfb62225bbdef845b70bd835b595bca5b57d4d45b4bfbad5b38e6795b35f98a5b0950515afb5ddb5af66b805ae85b165ad940cf5ad53fce5aa13cb75a8352725a6fa0fa59d4ca8c59a508ba5982a51e5965dea95959948c59229dc35906e90e581ab3f157fd16c557cde98c5779c2065764fd9c5730dfc15711ca74570a1c2656f745c4569b1b91564f831c561206ba55dedadf558de87e5544cb2a552692505511e860550dfe6054f01e0a54a01c0454495b175417ae2153f2ab4853ecbc7e53db99da53bfe3e95365bee452d3431a
  | 7, 13 => 0x6f6692196ed794ec6e6c254d6e0303566db260536c35fc8a6c3210346c2112b86bef6df46b803c9a6b47a83a6b14acf76aea9c676ac172bd6a7aabef6a641bce6a2cd9e86a11108469dd817b69dd3d8069ced10769b59f6c69abe5846938219c686bf131683d4afc683b4b7b682c7b7066ae78d0665e0e49664cbf2c663d7c8d65f0b59365c3b295657a81156577d4fd65480fc0651c629264f52eb36480eec4647d437f645360676445d97a6369ec4f62c0cc506285b5626251711e6247e165621e370d61fb8faa619b05cf61962c776172b8016130069760909e32608c7fb06085d490607f888d604e57745f863ea75f8064be5f6eeac35f1fcd375e980468
  | 7, 14 => 0x88ad02e187b4a8a68785c7aa84dcaa9e84106cdc84081ceb83de2a77839f8f6482f20d1782c3cbc2826ab59a81c988148182b3c48167702c803b063c80182c7f7f88aac77f6b9ea27f62b3947f1fec807eb530d07ea7722e7e9b4f517e962ad27e76d7fb7e3bf3b97dda4c0b7dd9e4537d79d54a7d461b897cb05d177c9d28dc7c8db1687c1f65ef7ad7260e799e83ff787776b277f8411577b0002276c8409c7695068976687e64765def607655cf9b7645f6247591fd5b7519d7c373b0dd4e73710cff7362ddb7729564b37285ee6b7267c8dc71cd914771cc03c671c6e78471c25b8271c0c9dc7105590a70a6a31d700fff156fe19b786fe18c596f880707
  | 7, 15 => 0xb84a23e4b7081cdeb6cd2691b6c023e2b6398991b5935732b438f3f3b342e515b1913ae9b0eef66eb0e0d8a6b067597ab03a5eb2add535b0ab5f514eab159141a83bb879a5d92f17a5906667a5405d43a3910e73a2efb3bba1a1b6aca16d6aa5a018b2e09fe084409eb7584e9e5afe569dde191a9d7fca739d0f97379cb16db199e3bcad976e8da997513d45945a46b8940dcade940a3da49408916193bd526593a55c0a933eb6de921f854a91b844bd91987cfd916f77189161150c914ab61a8fdfd1dc8ec0f79c8e4742e18cadfd3c8c780a438bfaaced8b2ff4408adff5238a9bdf4b8a637a6189ff2e53893ff9d28938a18388feac5c88edf53988b2a65b
  | 7, 16 => 0xf28503c1e5c5bf9ee3a887f0e1075b47daad8879da0e0f27d7801596d4d06fc7d0e2804ece9dd03fcb41c794c971c68fc949d068c4126081bf8eaa26bef7096dbd126d2c
  | 8, 0 => 0x853e10208309f6407eb18e107d223aa07b9c888075c78a30754c5b507382b2a0718ce6206ffd28706ddbcb50676bbd8066a98690666abaa06432ed4063fdb6006360a5c062ecb30062acd0405f0498f05ec442905e020ba05cbed7005b9fe1805b7cf6005b6a31405b0c60005af866605ade8440573888f055f13aa054f242d052b7c19051538c704cbe24c04bca05804805e300473f0b9046b80d0043ae49103d784b403d2c7e603d1f679039acc000397545d037d07cd03617f75035a9ba90327d72602879a75028467d602759e0202524e7801ddee0601c2157201a88ee401988a3a019408a8017886b801621b830111690701087a8a0028b4b60008ea4d
  | 8, 1 => 0x13a6412b13a07bc512f11e5b12ec0f4312e5204012d287d612c10bcd12bac99e12b85ffe12b43cb01299c1011269037b12398ec31220ad2311eaefd511d9dfa511ca9260117ae463114cf9241129333a10b91f0c10a7874d1045d6770fac387b0f914cf20f46d8050f412fdb0ec99b180eb6737b0e4b720d0e3d87de0e3c97a80e0a1fb10ddcda3a0d96bb9c0d685f7d0d65f5750d542bb90d4528580d29fcc40d1ff8530d1773050cf5ccf80cea78060ce5af780cc5f64b0cafbf720c9785770c726c390c5416370c3eaace0c12e3380be89c190bdf58d50b5feaf40b5805e80af6d1f10ab18d9d0a6fc0a809da69af097474f6096e30d709186b0108fca55e
  | 8, 2 => 0x1e89027f1e7838671e186dc01e1533c41df647a11db8bd6a1d9c0b7b1d9084d71d636b851d57ec461d4f30951d4bc8d71d3606de1d34af361d2d44191cea6c751ce462b41ca4325d1ca041de1c9dfda41c6ae2bc1c6433811c4434291bdce54b1bb387161b82fc621b7ddef91b55a3a21b0c80081acf5bf51ac5143e1ac066cf1aba95f21a06949719da87f119d1baed19b88d7c198d6737196d63b518bb95ed18adb9b4189a59931879e523183662a6182329ec17a246f1178c81d1176cd443176b6cb01724b66217070f5716ef574016ada0cf16a07f32168f860d164b66d416136fe9161220e1150a23a61508bdef14b20b921443d3621414ca1214026b5e
  | 8, 3 => 0x2c3e03112ba5c0202ba2406b2ba22ad22b215d702b102b402b10117c2ada9d3a2ad3728c29f611de29ba765429ae52e529a2236629922dff296e878029489b9c29477a7f29067a0e28a0b071288aece1288aa14c281da4be27090b2126b50147269e84d3268d9527262592212611a39125e6a08225baced9257a7d52254e1b822518782a250c500224d7c32424c0491024bc133124b8538b24a585a424a270222467cbbf24248db0240235e123f5ebd823bbb3fa23979837239703632348e2a523167aba22b0046f2297707f226f8e0e226e4e74221f2de3220330e721ca888c214961732130e4841fe18ea61f5155a01f25e5df1eb77ede1ea289ed1ea0a935
  | 8, 4 => 0x3d4296293cd07d193c4d44043c36897b3bdf6af33ba94f7c3b7f1abe3b467dcf3b44eaf13aa941993a61b87839fde13539e6bfee39c230593997a0483967664d391da7a6390bdb6338c21a2438a75fe738408dd537fb7b3737f64e58377ebe32377b402437585ebe372211c436c8e92c360d1c4c3529978f34e9673834cf2dd0349c8b7033d51f18339c7a5e331678d032d648793236597c3234db8b3205901d31b05b0a3129192e31238ee830ff320330f1d18d30de70bb3098980a3075dba4305d18e62fee4c012faa8ef12efb8abd2ef536722ef053e22ed56a5e2e9411a02e3bf70f2e39ac712ded455e2de52c3e2dae455c2d89748f2d3645e72ccbbae6
  | 8, 5 => 0x585e094957c231f45771b51c569b1b9155a758915595492755269250550dfe605487fcd254674964544ea4b154157d715239703151e1b2a95162343a50e296b250bccd6850ab9a9250a428d95022290f4ed6cf904ea591634e922f704e8baece4d7d1bed4d2143344d0f5b8b4cd882134cb2d6724c8266af4c42eddb4c31f6814c0eeaff4a00fb2b498c968c496d23c049504ec04934b5c647af8e1747939306475e33e4475a2b114749950f46f3caf0465a58a346481f5845b135c445494c90453cc5c4441cbc1542a6bd45427c489741de1a0941b6e3184109c609400a317b3f6a8f073f262ca43ef0f7ea3eac64823e4991d73e2d72c13e0598403df974d1
  | 8, 6 => 0x778a71ac76a85cb4755e83d8751c80377519d7c374b5e70f746d61797464461d73092c7e7253e4fb7231140a707e8025700fff156ff8def56fd9d85b6fb3ab5d6f69fec86f6692196ec8ffb66e8413ad6de8ab456db260536c9e3dbf6c44e0276c122c056be814b56be685826b5eb50b6b4b3aa56abdd71769ec654a69c82efe69381a4d68d3c4f8680cb72368012a686773c99466ba49f1669285ab664cbf2c65f0b59364536067639ba28962520a236217e40961502cba6103bd00607fde665fdab2cd5fb2ee875e9804685e21decb5df27eb95d9971a95d4426aa5cb1945b5bbdef845ba5ba235b3fe4c059d4ca8c599feff759264ab2590d2ebc58651b44
  | 8, 7 => 0xeee32c0beea4f88de3aaef49db586ef7dacbcc29da3fe02cda0e0f27cea586bfce9dd03fcd2f078ccb41c794c949d068c4e2306cc24be342be4b82d6b87ac592b5b84399b1913ae9b0eef66eabba903aa7d84c66a6f98c8ca6aa8a9ba2ee23e8a0599d569f76802e9db61b669bf485b598fa1971979ac8049433098d932f42799269d14a914d868b90986cac8fa536b28e4742e18db76dfc8c64df0b89ae940c893ff9d28938a18388edf539861d46e3855baa568463300b84415f7c8364055682ca5d287f62b3947eb5aaac7e78688d7c948ad47b1db37f7b13d5f07ace7b5e7a7d09997a60595b79db58d6799e83ff77d62f41
  | 9, 0 => 0xa0599d568938a18388edf5395bbdef8455269250550dfe6041de1a0929a2236629067a0e220330e71fe18ea61ac066cf1269037b0cea7806063fdb60062ecb30
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x90b080a0c0902
  | 6, 0 => 0x1c0e0707050e0e04050c10050507060d0d070d05100d0f050d0104010e14050f07070510170e08070101010f04020f07120f0c120f0f060f110f081c0718130f040e090216180504040e091507011604050501050f0d0f190d05101806020d0301050305051d0e051a0d190f0d060d05101303070d05040304040e18140d0f0f
  | 6, 1 => 0xf0d0d0f0d09040e0f0e120f01070c0d01010e0f0102170f0d0e04041207041a01040d0717010e0f0e050e0401050409070d040f090f10070f1801050e0604110705050e01021c0201040c010501070d07050f010d17191b1005050e050705
  | 7, 0 => 0x204031801120d120107040d0f04050705040c0905011e0704010e03131e0f011c0d070f0f0f120604070503050118200f01180e0107010f0d160117030712040f030712010f010407040d04050d0f000f05010d200e04100e05011b010507050f080d050e1d070101070e0e070f0c0f0f010d010f0701070d0d1505011a0d0e
  | 7, 1 => 0x51804050f0d0701050e0f1e0e1a181701100e00040f04041d1d0105010e090505010f0d140d050c190107160f041d0e0f05071d0f131e0d0f0e07070d0d160014040d080f03050f0e070f06120d0d050007051001060f12050f0d0d0d090e1c030f010703091d01130f0d0d082007130f1e05091811020f020e0f171604010d
  | 7, 2 => 0x1d04091d051b0f071c0f050e070d0601101b05161b0e0d0d011705070d0d0105110c1b0e12130d01040d010d06081f04090d1c01070e0f051800040407010f0d0f1d040e0f0701010f0e09020f020e010c04070f0f0e070e0f0507010d010c0e080d1f16100d051b0405170d040d100d0e091a030e0f171e120d0e0d0d0f050f
  | 7, 3 => 0x901070f04060e040f0f0c190e0405170d0d150d060c021e020d040f0e010904050d04050503020707010f070f0e0106070d0e20000d04050d110d100e070105050e05070d08070e01041e0d12010d190e06100e0d0d05060907050e050d18160305010304070d050e01012004030c0d04040f0f0f0e04070f1b0d0f010f0e05
  | 7, 4 => 0xd040f0d090504030d02050118200504050f070d070d040605140f01010f050d0d061d0505040d050e011011040505050913040c010e0f09050d200418050705010f1b12010e04011a040f012004030f18050f0e18030304051b0f121d0007010e04051618010d0e1a020f070e060f1a05050f070f090e0d0107041b0407200c
  | 7, 5 => 0x7070805030d05040d1515040d070d06010f050e1d0d050f0f07011601071401040e1c0418050f05010103040d0705010d0805011c0105040404040d010f030106151d010d0f1f05060104100d04050d20040e0d150f010f0e0503090703010e0d0e06150d040d0d010d0d0e0619050f0c1a010d0d0d0f05170d1f07020e0d18
  | 7, 6 => 0xf0f051c0f010f070e0101040f0e06160e0c17070e0d0d09070704111b0e01070d0f04120e0e0f0412010e0d050c0e0d150e1f0f0e0f0d1001140d050e050105120e010d050506010f1e010408011f0d0f13030d0f1804050e040404040e030e01110d1a070f0f050f040e0f05050f1e010d05040f050e0f0703050d0c14200d
  | 7, 7 => 0x20d0105120e1105050d0d0d0e0f0f050e0f07011b0f050f160d05040d07050d0d1a010d0d01050f11020d01070d0d12110f01020f030112040d0c04010707040f0f150d200c1d0d01161905010d05050f0d050d070d20050d010d101e040d0e0f04160e190d090107070f0e200f0d0d00040d0f0d16070417161a160f0f0d07
  | 7, 8 => 0x20f09050f0d0d04110d050d0501020e04
  | 8, 0 => 0x40507050e030f0e010503040603070704010304010e0d040e03010e0101010d1c050707071f0d0e020d0d050304010f0105050506030501040501040e0501040e050e04050f0e0f0f0f010707070f050e0401010707050620050d050103050f060d0e0d0f0704070504050d0e0e0e0d04040d03050f07060f070f0f03041808
  | 8, 1 => 0xe12060f060e07040f050707011a0103050e0f1606040401040d070304040f0e0f0d0e0f0e05051106050107050d040405040501010f01010104050703050504060d0105010d0d0d04070707010105070d0d04010e0f040701070d140701040401040401050f0e1f050f0d0406060d011c030f060304070604060d0405180e05
  | 8, 2 => 0x5030f05040d04050d0707060105010e060e07010f07200619141501070405050e070404030504040e05040d0f0f0d0d0f071c0f01050f08070d01060e01030304010d040407030f050e0e0e0103050f18050e0e030005050f011e040e050d040104050d0d00051d0d0607031e07070d040f0d0e0e030f0d06010f0e0704110e
  | 8, 3 => 0x50d050d070d0d050d0505050305090303050d05050501060703050d0d0d011605010105010f0e01040107090e0d0f0407050f1a0c050e0d0f01040e06070516060d0f0301071a01030f040d04050f0f05060f070f040d0d070e05070e0701010d04050f010d01031709040406050f05030e0d0d07010f1d0e06010105
  | 9, 0 => 0x7010701010501050e07050704050703
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 12 0 (CN0 s)
def CN : Nat → Nat
  | 5 => 22
  | 6 => 175
  | 7 => 887
  | 8 => 389
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xbc35d9fca4c91173a46ce7409ee36b5c90d9e5b083ef6132839336ff7fa95a536feff1bf5f6477ce3eaa161f37d4d5633629989c3530561f21616b4b1e8a60eb153e23b41522956c10cd385008bd7d3106ec1b5602c5891d
  | 6, 0 => 0x1c5970591bf0ad5d1ac3bf271a21ae7819ff479819b49b4e1919e4f818d26d1218a529ae1856cd1f17c661ab17b27d2c166aac2f161a8a3f154f1366154d39e514640b91138e3950135bd5691312860312aaadb7125ad46211ded939113e28f111027b6310eb396f0ed661ae0e42efc80ddff0ad0d596d930d4f0b800d4c4bd40d0be9a50ca711eb0c88fa160c6853f70c5582bd0c2202d60bc4b42d0bb2a5420b3253850adf59cc0a2a25f509a75124097ba5c408fba92607d5c6920783b5c2074dc8dc0729790d065c510b0621c7ec06212181051928b60477f48e042611f4038b081002c2207202b2e13502658d27008378dd007fca1f0061dfc90032d439
  | 6, 1 => 0x5200bb095168704c4f6e96504f3b3fb44f2380764e5f9d254be69b4b4aa8293549a41a3448f3e93e475ec74b46a6aaeb466d917b4439eb824257e0fe4211c6b640e55d98408e9a2f4048819a403cc8c43faf6c933eb62a163e8e55353d6c3ed23cf8c8873bce5cc53bb126c43b90730d3b77c9073a3ba16e3897959738738c8136d9994734e7d7c5344d9a2733b3f87f2fc23ef22f51538e2d6bb5f42c853b7f2c2e96992c29114c2b92bb832a03b17427571d8426da9e3d265640122652ec4025f6303a241ebe5823fe563e23a692742326aed12321a5e722ac35d1222c85152192cab3212af528206819a320533a2e1e5ce8151e5271d41de1c6931c7c3439
  | 6, 2 => 0xdc02168fdbf5b4c4c6758b58c55b5655adf2bb37ad22de3cacc6b409a963ed37a8c6b187a32fa990a1f6fbab9f087f0f9db11e1b9235279b8702bccc8438bb417a1c90ee7975c5b676ab1b0c706067867038f6726ddd88276dadba2c6ce1a9506bcfe5c96ac70bab67d4bde864af8a9a5faa4f9e5c086da95ad2d7055a692c8e58dadb7f57da8ae0579b22d256fc3c31569dd784566da35c5634629a54c3739754c14cee54b4ed4d52c93ccc52bc690b52b26a9d52b17daf52526b91
  | 7, 0 => 0x44b8250041bdd4e041a1b160404366b03b81d8f03b440a503ab09bf0391e1da038bf119037dd9b80364a3f203596ebc032b417d032565760318a7780312a9f10311f5ff030fd96503096a8c02ebe3ef02cb551002c9ce8602bf9d9602a75300029d633c0278bfdb027269ca0267b82f02651ff3025f0b3c025bcdb40247f9fe024282a5023ca12f022a4d6c0205d85001cd6bf201b0b74c01836ce50175a50201723763016dbad5014b7327013b3ded0137cc7b0113d1b0010abce80102c18000f17e5200da65d800c729c600b5422100a7937500a1ed1f00a1541c009188620085c6ca0082c63600670773006517a7005472c3004aa09a003d2f9f002ae2ae
  | 7, 1 => 0xa0c6f480a0ad8a10a059e1609fcd44b09ef1b9b09d609b309c451f409985ef70968609e095895ea09173c9609139e4509068c7808f31d9c08b690de087c9222087be133087a5067083b96bd08199a410814f44d080d769b0804202907ffeeff07be6e560764b3a7071b01190718ce6206ffdb18069af4c8068fa949068b0da7067cb21c06628dd706499ed606192a9906048c0305ec115305e7a82b0599b9980599b8bb0594d10b058db9d70588a5180587d2d6057b4706057955ee057310b1056e177305638d730555833a054c29ad054ae83a0547d7f2053dcf91053dcefb05373d7a051ea98a04cf78e604970ec4048de7760485200b0468003504650a2d
  | 7, 2 => 0xf8626cf0f7e2f180f473d4c0f39aa850f2d09ac0f22ce230f1e20a30e9efcad0e42acde0e3551d50e2b932c0e182d620e06c57e0dfad96e0dea08180de57ce50ddcda3a0dc239a50da674f60d9532e50d85994f0d8102970d65f5750d6294510d3cf9cb0d29fcc40d1229900cf5ccf80cd01e600cb442e80c8eb2b60c8a0cb40c83fefe0c70d7070c4cd92b0c4a3e6b0c48de650c2417fb0c0309640bce9aae0bae48190baa75d00b6a0b300b5c45fb0b50e9930b461a510b184e670b18450d0acc921e0ac938b30ac5028c0abebdb60ab1d7ee0aa16c1d0a77c1300a63090b0a5cb7e30a55db5d0a4caedd0a356fdf0a254d490a1ffb1e0a11fa3c0a0e1cd5
  | 7, 3 => 0x1719bfd717070f5716e807a716cc151c16cb6f011690b320166f219c165f54721646ab3915ed81e615bd626d15945d1f1578ff2e1558ad45153bc076150de56f150c34e414d709f514a9105914a65f5313fc983213f6539913f20c3c13e11d6713d0555113c52fb413c45b4b13936430138d9a141377c1a313725ebe134bf7581317588012ea840412e009e012c5ecbb128b7c3f125a997b121ca54711fbb26111e32e1611e2367111e11ed111d18d4611af34d0115d58a7115a932511004b6f10f546e310e3e25910a48cc810986500107e570f10384e3f102b7b9e101cf08310110c8f100ec2c40feed3600fe59f970fc43c7a0fc40cc30fc390490f98e401
  | 7, 4 => 0x1e7b96601e603f2c1e4cf9f01e33112c1e15ce491de243341d9e53a41d8619011d55fa561d448ee71d3184341d2ef3581d26ad1a1d25f8d81cef6b2d1cdf4dc91cd727371ca0e6d11c9cc88b1c8eacae1c8a9dee1c4ad2891c00263f1bf8d38a1be0a8591bc8711a1bc711271b32238e1b303f8d1b297e5e1b21e9191b20bd031b0c43cb1ae50ad11ac3fce81a84bb831a7af0631a2a9b6b1a14a31f19f8a30519f6efa419f6dba419b88d7c197e19b2190d7b8c190d17fb18d5af0d18d3b94e18c3a3421890d038187ba691186c21d7184274a41837ee6c18326c5f17e5ebef17e22ba217cb381f1783e29b178159bb1756dc6f174feac7173c23a2171e9d62
  | 7, 5 => 0x25b3047e258282fd25687a35254910442525663024fbbe3824956abd2485d5bf247619b624632dcb245b293f2448c3b62428a48323c4e6f423a7d752239cceec23851b8f234edd05233a6f45231b4af62318df132317b6d922894302226d71792261b51c221ecbb221ecf2df21df48bb21cf527621bd4b1921b72ddd21b5bba021908de9210ddaf720e5433c20dfd20420b9d4bd209522ba2093e61e207080c1205f5a7520577d33204e7381203aee7b203845e8202dd8022012c4902008449f2002a1fa2001b4601fe8b6e01fac248b1fa7832d1f93fd5b1f864c281f753bf81f6a65c61f0cde7c1f019e2b1edab0621ed7c0931ed62c311ed420bf1ea7e1e0
  | 7, 6 => 0x2c0c1b892be529ee2bdeae5f2bc47c1b2bb8df812baf74432b6869a72b1c733e2b1b43872b112e1c2af10a272ae7352d2ae020ea2aa3f75c2a915d002a8cac372a8b0fc72a85f6752a64263f2a49fa3b2a07be4829ae739529aa09e029a15c1629883c60295f595d2952a65729480a492947c2242946b0bc293437882930f8f6292a91032926292e291123e029067a0e28e50d3728e4ba1428a0b071289b83b9287971bf28726756285d6adf28405f1227f6def327df97fb27bf692827bd370927b471a32780c09f277fcfaa2760431c27444bc7273c581e2726a93f26fa589326e9ee112685993f26648e742657cb6826579f142630e8ce25e90bd225dff219
  | 7, 7 => 0x34aa14c434a89406347f04ed3455981d3452f0d0342bb8343406d79733d7b6d533c9cca6339920153388c109337ce6fe337abc8d3378ae0d32f6cd8232f5c56232f4600032c0bcf232a378bd32a266f03276859632180a1931ff381231dcd286318fdf0d318b391b317e0d9f30ff0e3f30bc54d330a7d1de309b291c307dbe41307978ba30607234304e2763304b6ce6303b86cf302e5d442ffc151a2fee4c012fcec9f52fc6234e2faa09cd2f89f2232f831add2f5c56782f5908e32f44ef3e2f1516e62f0eb1152ef7a9132eb946f02ea791cd2e45f24e2dfa793d2da5bed02d93b68d2d674aac2d44bbe72d42f4222d36c8632cc9df802c79d2462c3eaa15
  | 7, 8 => 0x408f4e334076b5b04025a8fd4000e4ce3fc82b863f9fa7733f3b5d423f3327113f262ca43f064e1f3eeeb0b13ea559363e0283f93d714ff43d36c9cb3d0ad4423d0224c23cda9f983cd6e6773cd362a63cc1bf293cc028ed3c726c673c6045fd3c3b95263c2b43253c1f854a3bf0b7cd3bd61a173b49a1af3ad0e1473aa617623a89c9453a845f833a7ce63e39cd2b243998930c398918123982fda9394bf6cc38992ed3389805713877e4113876379d38384c07382d4c123801b41837c6359f376c010c374a72d5372f1d5b36b36143369b574f36643c35364c5208361ba8dc361389fd35ca8af53598de1435434fb63538718f351b6ec434da6ab134d04bdb
  | 7, 9 => 0x4a65c1914a5e5b674a417d8a4a2d567c4a21330d49e74af549e5faec49dc887549dbea9549d4199c49b6087c490b957949032d5048f2e89a48b6b5ea48a3dd9e47fbd2d647f5fb9c475e5a5f4743bb5b472f3cf24716e42b47052c8346c4203946a8e31546546fca46338bf84624a35245f507df45f3717245ba27cc45adae404586af0245838d9a45701e5f45494c9044e7a53044c895f944920852446cf57d4445eb79441cbc15438afd50435c3219431a002a42e8942e42d1cb7642add1c2428e61f94267d10f425a6df841f4e32641ed547841b6e31841b2654d41a41a8f4183299941690178414727d44143ce6f40feca1940f768b940b9108340b70205
  | 7, 10 => 0x5a459ba95a0d3f4759e16c7059bfe9a658a6accf585e0949581ee68a57b283c35753270a5710d5325686831656450b5e5603868455a6d55655a0215a5487fcd25486b559546f5d3a5446c2ef54157d7153710b97533f89b45325373953168cd552b2d3665277d55d52671e7d525dc465525516fd52278ffd51fb7fa051ea7bf351b86d7d519d8391515c434a50b5ad554ffa88a04fd778c24fd528c04fa8be444fa499d84f9ac0c24f1baaa74f0dedfc4f07c2794e6814bd4e1bff604dc01fe14dbd3ff24daddb814d7a1d6b4cd9df434cc4df294c5e836a4c5bca0e4c22df784bddb4f54b8828cc4b818ac24b6334c04b3b707a4b0eade64afdaf1f4a8776be
  | 7, 11 => 0x6cf58b6c6c7b30626c6f55b36c44e0276c3ac1d86bafcf226a8b977169cf500d69c9ebdb69a05ce4696fb6686860d11367b7de2c6755951366a3043e6666c244664cdfc665cd583b65bde0f4658e41a06423143c63d3a66a63bf06a363964a746304c4196304a88562f526e762ea6c2262ea54b762ae05ec62a6852a6295a993622cae9f6213964a61c0b4fd616740be60abd602607b2a7e606724055fc6dce25fc4d7275fba9e125f4ca6635f33cff15f17dfc65ed1bfb15ebe26ba5e9af2895e474a8e5e4720e55e3daa385df0e4b65d2633f95d1d7c905cc36d865c40b9ac5c04156d5bcd3d845bca15325bac49c05b1168535a9d81855a8d13aa5a6354c4
  | 7, 12 => 0x8ded43c38d7c46b78c64df0b8bd053ef8b8058ee8b78136d88b06f908834da6f86b09e57865e7e5b840c97d383c1eb898302a1e6811720d1803d3e987fd963917f9da9867f53e7e67f16c2697f00be877ebd8a7f7eb5aaac7ea7b9c07e4eef8e7e4b8f8d7df2533d7d082cb87c96d1a07c7200ed7b9be6257b813f017a9392d279a70c5a78efd8e678cb8373775530af774da26776c85787766848df76677d4775ea4f3d758b686374b5e70f745a8933744c2c3173b8417573b24f6e73ac080072b5fc69724d06a27231c51f71dcf70071a0ea0b719a932870f1ba4e70c93b036ffe74dc6f2f44266f2d34416e8413ad6e6d03186d3b65746d3a695b6d3860c8
  | 7, 13 => 0xf18bc3afe4357a76de7ee599daf1cbd6da6a395ad855eb2ed1ddefb4c8560f9dc615bde4bf4b3c00bc96a8a4bad0ae08b7a42a41b7546d9bb510b451b34dd206afa3cc33ad0116fcacb57d87ac653139a78db3a9a736f212a6832053a4b8cd18a45bb3e0a3d9fbf1a29ea784a27f124ba2346601a20537fca1bdae47a130fa16a0599d56a02318169f788c2e9ec81d129e1d29039ba0204599ca4626997af4109940fc36979963a497621c6995fdde3a9305144b92385a189216f324918090a190efc26290ad44d6900a83248f7e97338f0ddc2a8ec339ba8e51f1df
  | 8, 0 => 0x9e6b3db094b01a2092ceca8091ef7a90910b2e208fbbbe208f7c9b3088e03cb0882d01507f06f0d07ecb1a90794f60c079062c307691309071d881a07188d230704fa2506f2e5e806c68b0506acf76b0693106b06882c50066c618a0649e12f0636f073062ec06305f8a27e05f207af0576b4520529e81d04dba38504ac62190467fc14043beb340429916803ea8a6903b266ef03a5944e03764fb1037261df0370352c0352b9410341a9110317a30b02f491a402cb89d2029ede2a02869daa026f0685026e6a9a026b6a7e026a11ed0231b1e601b0a8f801709a24014b39b3011b4dbc00dd55bb0091ace5006833c000517c8e00507fc400370d4d00182465
  | 8, 1 => 0x14d52c7713b9135a13a40e0c13a1b003139966ee138c91dd138219b01339590913124718130623a912eb0e9712d3f71312c6e4ec12b19a901261a17511c4e97311b6fc0e11ad4669119b37e411617ec1113a436a111f6613111f2872107899d1106c7662106ace9910435b03102cf64a1004b69e0ffb2d760fcf577c0fc4eb390f8f8c170f7be15c0f678c280e7a832b0e66b6f40e62d7bc0e557ebc0e4a4eea0e3d7c490da4a5cb0d27664d0d01d94d0ce185680cb4be130c9d55070c59c1e50c06fdea0bfc44960bf5edba0bc6d6fd0b7739e00b3d59a30b3a65130ad764ea0aca218d0aafd4370a81e79d0a342af70a12a0430a0e53ea09ff27cc09fd55e7
  | 8, 2 => 0x26abebcf268156c62636aa7c25b0819425a8b130255cb3472510209224f6fec72466516d244ed9db244bb7d8240964d92361cdda23387002231383832309a4712303617922db915d22b8ae2821f3404721d2a51c216d1388215bdb50206c9607202c65b01f482cb11f3b9e631f0fdda11edce3901e7d1c231e5086dd1d9addba1d4f6d0f1d4eaa0f1d3a22b31cfeb2321cf46c871cbb558c1c8b3c901c7001d51c57e5f01c4bc2811c2ba0391a9c9e991a1226ea19d1357519d1055a19bae7df18c21dd918aad6d718958c7b1886727418302605181d7dc917e4e01017d344b017d192bb17a5ea371794da07176ab824176194dd1732a091171d959f16fd416f
  | 8, 3 => 0x3c2663e63c2445ca3b98d1443b08323d3b07dd883a6c88e53a4c6b823a3245493820cfd13801fd6837fc999c37a3046a379a1d91379752223780d33e376da5483737bd8a36427b6e3622220836183237360ea7443594e8593583b0213400e21833c07d7533a5f87233693fbe335cad6b335c4a073347a81d32f1691e32bcd9d531553a8c31479d7d30d06f5c307dc8b1305826662f4ec0422f0a7f3f2e81a52e2e1509a42e08e6352df60b2c2d8e2d522d85b18b2d6a61052d5b4cea2cb0a4542c632e5a2c2675a62bdd42b129e93d0c29b4654d29b1e6e8296a05fc294761a3293b6c852868eced280510ce273829d92723248b26e5e70c26ccb26926c1222b
  | 8, 4 => 0x61d1074e615c2c9b5fb933065d9790c55c5f6ff65c4fb8125c4e82055b67963f5b2f5e175ad520ea598a34535966d327587668ee56c213a25687550856776758565804fc55fd2c93555ddde154987000548b40bb53b61f99534428e052a0ce48522dc4b65229e3dc52155ef050ba504650960ec150741311501f059a4fca49f14e5f6ff74dab248d4d9f011e4cba9f254aa2bcb74aa07a25497f617e48b2b0d547bfce684669cfc8459b82f944f8493f44d7f04144c2eaf344642fd243e4cd4f4304346e4248c268415a990c40da63693eea215c3edc30c03e9184763e2eaf563e075f003da252993d5e83253d31b5533d1921633ce6500f3cbac1e13c67d8ec
  | 8, 5 => 0xb1fc64e1b1bfac2dafb1b8beaa332d49a6ebd550a663a2d59a54041097a18d98966d796592dc946f927b09828f5b2efc89dca387897c0b608813b2a287290715868b4ac984a22d4e837c10b8826bc9f4819f6fe780f3a48c80ee8e7480d00d9f809cc15e7f941c287ee819547d2475287b7ffa567b18428e7b0ae4967a7cd6d279d2351e79956d127963b87e773129bf76f7dabf76e119cd765cb5c2765265e474bff1be71f0652371bf6596716560827143c48670f9183c702a7cd96dda2e556d23fe5b6c63177e6aecfeeb6a0dfbfd69fcc3c56940de41677c713767582585673c40e066b022e766740d3765763cfd65246d9b63f71d12638864f9635cec56
  | 8, 6 => 0xef473d08e98ba31ec80c92b8c6eea3a2c19f8122
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x76d15450c15db4551430576d15450c15db4551430576d15450c15db4551430576d15450c159f5411530176d15450c1000154902060004d13080c005300520356cd0434c199d4595230476d15450c15db5455030776d51540c15db455143050009124080c002545020376d15450c05db45514305
  | 6, 0 => 0x584548040062c55204000d123480400269512070018f0548380006d162010014b04480c0026951207000d504881800168d12050018b05480400564d22070001945881c00451152050005a34481c00455142010001b54c804000000f10f00187544805db4551430400115450811db455143050001954c81c0061cd12050005a344814000004b1060005434480c00564d220e0000024840ddb455143040000021443c0006516201
  | 6, 1 => 0x18f05483800464162040009604480c0025d0e20376d15450c05db54550307001973248140050c8d2030014743480c0063c552050014f1048180062cd52040001945881000000511030018734481c0063c5520700015348818003655220400058454804002615120e0018334483997344d03060005634480ddb455143010018f15481400000111060011445481400000c310d76d51540c1c00000851060018354481c0050c8d203
  | 6, 2 => 0x18734481c00510d1206000194588380061d152010001931881000000d110376d15450c0400455142050000024041800455142050018f0548040063c1520e0014b04480ddb5455030e0005a4548100065c8d2070011654880400165162050001b458810000004c1060018f15481c00455142050011545081400065162070001a34481c0063c1520e0000004440c0005cd2206000002584340016115201000194588140061d1520e
  | 6, 3 => 0x1874048380060cd120e0018845481c00545502070018734481c00065532040001205481c000010d1030018f054838000651620400096044818000009610d0005443480c000000710676d15450c14000009410d000d043480c0040d51207001832448140006d1620e000564348180016915204000594588140045514205001832448040064c41204000954388180056cd22070000024441800000051030005a4548100060d09201
  | 6, 4 => 0x18f15481400001151050005a4548100016951204000da15481400158d120300000134418005495320776d15450c0400169152010001b458838000011510500054434819db4551430576d15450c1400545502050005634480c000009610f0001945881000365522040018342481c00464162040000024441800169152040009854481ddb4551430176d15450c1400065162010010354481c00451512070001a2448140005481207
  | 6, 5 => 0x9610d00115450814000009610d001154508140062d5120e00115450814004551420500000244418000009610d76d15450c10000004d10300193104815db5455030500190104810000001510d
  | 7, 0 => 0x5a454810001651620e00000254438000009210500000144418000010d1030000034441800000c51040000024c40c000011510f0000021441c00000d610e0018324481400545502070000053c40400344d02030000015840400365522050018f05481000000121050000040c41c000004210100000450410000010710700000344410000008d10e0000012440400000151050000013440c0063c1520e0000025843400000d510e
  | 7, 1 => 0x44438000010c1060000034443800000151010000045841000000d110e00000044438000010d1030005a45481000000511050000025841400001031070000025441c000011710e0000012443c000000d1030000043441800000961010000024440400000d71040009954881000001071030000034843800001161010000041c438000009610e0000005441000000d51070000052441c00000d610700183244804000008d10d
  | 7, 2 => 0x34841800000c310d0000014841400000971010000035441400000d1107000002484380062c152050000005441400000411010000043440c000000d103000004144180006516204000003584100060cd120400000454404000011510500000458410000010310700000458438000000d10300000158410000008d10e00019458804000651620500000344438002615120700000450404005491620100000214404000010f106
  | 7, 3 => 0x18734481400000961070005a454810000014110e0000035441c00134552010000003440c000010f1030000003c43c00265522040000034441800000d51070009954881400000911030000003840c000010710e00000434418000005210300000344418000014b10500059458838000010d1030000013c41800165162070015154081400265522050000045041000000d61050000004440400000d2103000002544040000151107
  | 7, 4 => 0x34440c0063c152040000013840c00000911050000054441c000651620e0000012840c00065162010018734481400000d11030018f0548380061cd12070000012441800000d510400000314410000014b1040000013440c000001610e0005a23480400000171040000021c40c00165162070005514883800000431040018334483800001171010000031c4100000151107000002544040021495204000001544040000013105
  | 7, 5 => 0x54841c0000049107001833448100000056101000d9548810000008f1030000024841400001151050000010c410000010e1060000001c414000008d10300000158414000004110300019458804000008510f0000010c41000001521040000045841000258812070000004843800001071010000024c40400001161050011545081000000d11050000045c438000015210700000244414000009610d000000444140000116104
  | 7, 6 => 0x1444180063c152040000041c438000008e10e0000005c41400165162070000003c43c0000115104000002384180000097107000003544380060cd120e0000003840c000015210e0005945881400000161010000015441400000d11060000023441800000061060000041c438003655220e0000054841c000009110d0000035441400000151010009a45481c00001531050018f154804000001110500000144404000005510d
  | 7, 7 => 0x23841800001141010000034441000000d11010000015443400000911050000010c41000000121040000021c404000009310e00000354438005455020700000044418002645220e0000024441c00000d21030000054441400000511070000021441c002550e20600000144418000001110600000424438000008d10e0000041c40c00000c910e0000054843800268d52040000034440c00001151050000014440c0000117104
  | 7, 8 => 0x4840400000951070005a45480400000431030000003840c0002411207000005444100062c1520100000148418000010710e0000014441000000c21050000045443c00000151010000003840c0063c55207000002584040062c152050000045c43800000111040000052c41400000d21050000043841800000d21050000003c40c00000511030018f154814000004910300000054414000014b104000000544040000051101
  | 7, 9 => 0x454414001651620500000248414000001510d0000054840400001511050000045c404000011510500000344418000010110e0000014c418000001710e0000035443c00000951010000010440c00001151040015154081c000008f10300000218404000004f1030000054841c00265522010000054841c00000d51050005634481800000d110500119058810000000d1050000014441000001031070000023843800000d510e
  | 7, 10 => 0x148410000004d10600000044414000009510700000434418000001610e00000048410000015210e0000034c438000005510e0000005c410000011510500000244434000008d1060000054441c00000d21050000015841c000010d1030000001c41400001031070000005443400369512010015245881c003490e2030000013841800000c91050000054443800000cb105000004544140045514201000002444180061cd1207
  | 7, 11 => 0x1945881c00000521010000025043400000d51050000040c41c00000131060000054441c00000111030011545081400065162050000034441400000151040009a54483800269512070000040c41c00000421030005a45480400000cb1050009a54481c00000561050000043440c001651620500189134810000010d1030000045c438000010710e00000344418000015110e0000030c43400234d5204000594588380063c1520e
  | 7, 12 => 0x18f054838003655220e0000054841c00000d31040000023441800000d21030000054c414003144120100000154410000001510100115450810000008e1060000024441800000121050000025841c00000d310600000344414001681120e0000015440400001511040018f124810000005110400000454410000009210e0000023440c0064c412050005a32481000000151040000031c41800549162050000054440400000d1104
  | 7, 13 => 0x25840400000d210e000d954880400001511040018734481c00459522040000013841800000571010000021c418000008f1060000025843c000011710100000058404000009610d00000450414000011510400000148410000009610d00000340418000004d10300000214404000014b1040000025441400000951010000045441000000d510500049154810000015310e000d12348040000011101001833448100000011104
  | 7, 14 => 0x248418002695120e0000003441800269512070000043441800001031070000053c404000011610e0009954881000000111060000040c41c000008110f0000004440c000015210100000158410000001510e0018b13480400054812070000024440c00000951070000023440c0000091101000d925881000000551040000023443400000521070000035443c00001171070001945883800000961050000013440c000145120e
  | 7, 15 => 0x24440400000d61070000025843c001548520e0011654881c000014b1040015245881c000014f1010000053c40400000551050000040c4180000011101000d9548810000000d1030000004440400000921070000025441400000111050000025840400000111050018334481000000511050000015840400000411060000010c40c00000c71040000054441400000cb1030000514483800000151010000035c4380000091101
  | 7, 16 => 0x54404000010710e0000003841800000921070000042c404000651620700000354410000010310e0000034c40c000008d1060000014c404000005110600000348414000011610100000244404000015310100000158414000000d106001832448140045514204000001044140060c9120500000324414000000d1030018734481c00000511040000025841c000014110e0000012c40c0005441207000001544140000016104
  | 7, 17 => 0xd954881000000d71040018f15481c000004f1060000030441400000c510400000058410000008e10600000540414000009210500000454410000014b1050015245883800000d1104000004544140065c8d2070011654881400001511050000041441800001471040000035441000000d210e0000054c41c00001521010005845481000001511050000035841c00000171050000054441c00549162070018f0548040026915207
  | 7, 18 => 0x5440400000551050000041c438000015010e0000014440400000431040000010441400001511050000010c41400000971050018f15481c000014b10400000104410004595220500000054438001651620e0000023440c00000111030000035441c00000491010015934881c00000561010000045041000000d110e0000021840c000011510500000544404000008d1070000034441800365522070000023840c0006516201
  | 7, 19 => 0x454404000001110e00183344838000009610500000124414000009110500000054414000009510e0000053c40400000111060000041c40c00000521070000045441000001451070000005443400000d51050000053c40400001511010000024441800001011060000030441400455142050000005440400000491060000041c434000015210e00000048418000651620e0000001440c00000551070018f154814000008d103
  | 7, 20 => 0x45441400000d31030000054441000001151010011545080400000d710e0000024c404000015210100000144404000009110300000124404000005510d0000014841800000931010000045840400001161010018b05481400000171050000024441400000111030000015443400000d210600000108404000004e10600000454414000008d10e000004544140000115105000002584340000153101000005484140000097105
  | 7, 21 => 0x24c40c00000561040000005441400000921030000035441c00000531010000003840c000009610d0000013840c000010e1030000045c43c000014b104000d954881c00165162050000054441c00000d210500000454410000015110e0000023c418000005510e0000054841000000c310d0000005843800000561010000024841c00000071050000043840c00000d51070000031440c00000d2107000001584040065c8d20e
  | 7, 22 => 0xd954881000000511050018f15481400365522010005925881000000491060000054c414000651620e0000053c404000001110300000328434000010d1060000014441800000911070018b05481400000d51070000024c418001691520100000158414000004d1060000003c4180000151105000d954881400000511030000034843800000951010015154083800001151010000041c418000004d10300000258434000001510e
  | 7, 23 => 0x5a454838000005310f0009132480400001501070000023443800000d11070000054841400000d610700000454414000009610d0000024441c00000911060000025c404000011410500000540438000010710e0000025043400001521070001945881400001151050000034c4180000114101000d9548838000009610f000000544380000055104000003444140050c8d206000004544140000091103000000544140000012106
  | 7, 24 => 0x248438000008d1050000010441400001031070000054441400000161040000021441400169152010000034441000000951050000050c438000009610d0000054841400001161050000004440c00000931050000015841000000d310e0018f05481000000d110e0000020443800000cb1050000014441000365522010000024441800000c91050009954880400000851010011654880400001171010000014441400000d510e
  | 7, 25 => 0x15441000001151040000034441c0000055101000000444100065cc920500152458814000004110500000158410000011610100115450804005455020700000104404000010b10300000058410006244d20400000454404000010f1040000031841000165162050000035441400001161050000045441400000531030000045441400001511050000015841c000001210100000450410000008d1060000042440c000014b101
  | 7, 26 => 0x15443400000c91050000034441800000851060011654880400549162070000005443400000551010000013441000000971010000042c40c00000921050000023c418000009610d0000040440c000009610d00000144414000010e1030000025440400000111060000025843c0060cd1207000d9548838000010e1030000012440c00000d510f0000031841000244962040018f05481000000151050000052c410000009510e
  | 7, 27 => 0x10c1060000045441400455142050000054c414000009410d0000054441400000111060000034440c004551420500000258434000015110500000154410000004110600000344418000009110700000540438000014f1010000014841c0016915204001154508140045952201000005444140000049101
  | 8, 0 => 0x54410000004d10e00000054404000005510100000058438000001610700000124404000001110e0000034441c00000561070000004840c000011610700000324414000011610700000358410000009610700000304414000004d1040000015441000000511040000054841000001151010000032441400000d51070000024441000000121040000024841c000009110e0000034841c0000056104000002544040000091104
  | 8, 1 => 0x34443800000561040000035440400000c11010000045840400000121010000045441400000d51070000025441000000d210500000458414000009210e0000035440400000d11010000014441c00000521050000015441400000921040000014841c000000510e0000014441c00001141040000035441400000d610e00000258404000004d101000003444100000152101000001484140000015101000002444040000049104
  | 8, 2 => 0x344404000001610400000104404000004d10400000248410000011510e00000248414000005210e0000014841c00000961010000024441000001141040000032440400000151050000015440400000551040000035841c00000561010000024840c000011610500000234438000005510400000304404000009510e0000015840400000d510e000001544040000055105000001584140000116107000000144380000056105
  | 8, 3 => 0x44404000005110e0000014441c000009110e00000204410000008510700000158438000005610400000358438000004d10e0000045041c00000511010000035841400000d61050000004441c00000561050000025843800001161050000045041400000561010000010441c000001110400000358404000009610400000204410000015210e0000054041c00000d51050000005841c00000961040000034441c0000016101
  | 8, 4 => 0x244414000009510100000244414000005110500000158414000008d10e0000005841c00000961050000025841400000491050000004841400000521070000014841c00000d110400000454404000009610400000154414000009510500000254414000011610e0000035841000000491040000001441400000561070000012440c00001521070000043840c00000d61010000015443800000161010000004441000000d1101
  | 8, 5 => 0x14441000001141010000054041c00000d11050000035841400000561040000004843800000121010000025441c00000491010000014841400000c11050000025843800000561070000034441000001521010000030441c000001210100000244410000009110100000214438000011510400000544414000005210100000348404000001610e000002484040000051101000003404180000055104000005484140000015101
  | 8, 6 => 0x244404000015210500000044404000005210500000144418000001510700000044438000011510400000258414000008510500000044438000005610e0000024440400000121010000014443800000951010000023441c00001521070000025441c00001161010000034843800000411050000034841c00000411010000014841000000d510100000044414000005210e0000014841c0000016107000003584040000150107
  | 8, 7 => 0x354438000005210400000354414000015210500000148410000015210e0000014840400000d51040000021443800000961010000015440400000161050000024841400000491010000014440400000d110500000148418000001610e0000054843800000491040000005441400000c910400000324414000000510e00000144410000008d1070000054841c000015010e0000034841400001501070000010441c0000096107
  | 8, 8 => 0x45041400000d610e00000314438000000d1050000020441c000015110500000158410000005510500000058410000008d10100000354410000000510e0000025443800000951070000035440400000d11030000035441000000d510100000344404000005210e0000012441000000561010000025841c00000491010000030440400001141070000054043800001161010000045841400000d2105000005444380000052101
  | 8, 9 => 0x14843800000111040000054441c000015110500000254414000004d1040000005840400000d21070000013441000000d610500000054438000008d1070000054441c00000411010000013441000000811070000025441000000961070000014441000000511010000003441800000d210e0000054840400000d21050000024440400000491040000005443800000161040000004841c00000d61040000045441000000d5104
  | 8, 10 => 0x45843800001151040000045040400000d51010000012441000000d510700000358404000011610100000214414000009110e0000032441400000561050000045840400001161070000025840400000111030000054840400000d110e0000005440400000d11040000034441400000951040000024841c00001151050000034841c000005510e0000054841400000911010000045841c00000911040000020441c00000d6104
  | 8, 11 => 0x23441c00001521070000045041000001501050000032441400000d110e0000054841c00000d51050000035840400001151010000015441000000811040000012441400000c11010000010441c00000921040000015841c00000911050000004441400000551070000025441400001141050000054041400001521050000010441c00001511010000024841c00000d6101000002344140000016101000003484100000011104
  | 8, 12 => 0x11510500000450414000005610400000454404000005210e
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_233 roots_233 5 s ws hint
  | 1 => checkCutEntry true dom_249 roots_249 8 s ws hint
  | 2 => checkCutEntry true dom_117 roots_117 5 s ws hint
  | 3 => checkCutEntry true dom_236 roots_236 7 s ws hint
  | 4 => checkCutEntry true dom_252 roots_252 8 s ws hint
  | 5 => checkCutEntry true dom_245 roots_245 8 s ws hint
  | 6 => checkCutEntry true dom_217 roots_217 7 s ws hint
  | 7 => checkCutEntry true dom_237 roots_237 8 s ws hint
  | 8 => checkCutEntry true dom_229 roots_229 5 s ws hint
  | 9 => checkCutEntry true dom_181 roots_181 5 s ws hint
  | 10 => checkCutEntry true dom_204 roots_204 4 s ws hint
  | 11 => checkCutEntry true dom_209 roots_209 4 s ws hint
  | 12 => checkCutEntry true dom_172 roots_172 4 s ws hint
  | 13 => checkCutEntry true dom_189 roots_189 7 s ws hint
  | 14 => checkCutEntry true dom_221 roots_221 8 s ws hint
  | 15 => checkCutEntry true dom_125 roots_125 7 s ws hint
  | 16 => checkCutEntry true dom_89 roots_89 4 s ws hint
  | 17 => checkCutEntry true dom_205 roots_205 5 s ws hint
  | 18 => checkCutEntry true dom_153 roots_153 4 s ws hint
  | 19 => checkCutEntry true dom_185 roots_185 5 s ws hint
  | 20 => checkCutEntry true dom_244 roots_244 5 s ws hint
  | 21 => checkCutEntry true dom_213 roots_213 5 s ws hint
  | 22 => checkCutEntry true dom_248 roots_248 5 s ws hint
  | 23 => checkCutEntry true dom_241 roots_241 5 s ws hint
  | 24 => checkCutEntry true dom_108 roots_108 4 s ws hint
  | 25 => checkCutEntry true dom_220 roots_220 5 s ws hint
  | 26 => checkCutEntry true dom_180 roots_180 4 s ws hint
  | 27 => checkCutEntry true dom_93 roots_93 5 s ws hint
  | 28 => checkCutEntry true dom_109 roots_109 5 s ws hint
  | 29 => checkCutEntry true dom_101 roots_101 4 s ws hint
  | 30 => checkCutEntry true dom_177 roots_177 4 s ws hint
  | 31 => checkCutEntry true dom_85 roots_85 4 s ws hint
  | 32 => checkCutEntry true dom_188 roots_188 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_253 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_233 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_249 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_117 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_236 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_252 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_245 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_217 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_237 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_229 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_181 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_204 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_209 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_172 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_189 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_221 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_125 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_89 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_205 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_153 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_185 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_244 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_213 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_248 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_241 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_108 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_220 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_180 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_93 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_109 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_101 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_177 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_85 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_188 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_253 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_253 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xffffffffffffffff0000000000000000, 64), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xffffffffffffffff0000000000000000, 64), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_253 == dom_253) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_253 goalM v ys) : RunD true dom_253 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_253 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 6 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 6 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 113 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 113 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_256 : ∀ i, 256 ≤ i → i < 344 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 88 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 344 → Z 7 i = true := (range_split z7_0 (range_split z7_128 z7_256))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 128 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 149 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 21 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 149 → Z 8 i = true := (range_split z8_0 z8_128)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 13 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 13 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
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
  scr true dom_253 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_253 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_253 roots_253 goal_253 11 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_253 goal_253 := by
    have h0 : isConstB dom_253 goal_253 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hnc hr ha
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
    rw [proper_failG zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction

end S_253

theorem lowS_253 : Lower true dom_253 roots_253 goal_253 11 := S_253.noCircuit

theorem lowS_255 : Lower true dom_255 roots_255 goal_255 12 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_253

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 13 ≤ gates.length := by
  obtain ⟨g, hg, hgn⟩ := hhas
  have hout : (execN gates xs256).getD o 0 &&& mask256 = goal_255 &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit gates xs256 r hlt (fun g' hg' => (hfan g' hg').1)
      have h2 := congrArg (fun l => l.getD o false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN gates xs256).map (·.testBit r)).getD o false =
          ((execN gates xs256).getD o 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN gates xs256)[o]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt8 r)).trans (goal_eq_f ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hsup0 : ∀ v ∈ xs256, Avail true mask256 xs256 v := fun v hv => Or.inr (Or.inl ⟨v, hv, rfl⟩)
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach true gates xs256 hfan (fun h => Bool.noConfusion h) 0 xs256 xs256 rfl hsup0
  have hav_out : Avail true mask256 bank ((execN gates xs256).getD o 0) := by
    by_cases hi : o < (execN gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := lowS_255 p bank hr (avail_of_eq hout hav_out)
  have hlt := countP_not_lt hg hgn
  omega

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [8, 9] }, { op := GateOp.or, inputs := [1, 3] }, { op := GateOp.or, inputs := [11, 4] }, { op := GateOp.or, inputs := [12, 5] }, { op := GateOp.and, inputs := [7, 13] }, { op := GateOp.or, inputs := [4, 6] }, { op := GateOp.and, inputs := [0, 15] }, { op := GateOp.and, inputs := [3, 6] }, { op := GateOp.or, inputs := [10, 14] }, { op := GateOp.or, inputs := [18, 16] }, { op := GateOp.or, inputs := [19, 17] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 20⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  decide +kernel

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfan _h1not hev
  by_cases hhas : ∃ g ∈ gates, isNotGate g = true
  · have hfan' : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨h1, h2⟩ := hfan g hg
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 | h1 <;> simp [h1]
    have hlb : 13 ≤ gates.length := lb_with_not gates o hfan' hev hhas
    refine ⟨witGates, 20, wit_mono, ?_, wit_eval⟩
    have hlen : witGates.length = 13 := rfl
    omega
  · push_neg at hhas
    refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; have := hhas g hg; simp [isNotGate, h1] at this

end PEqualNP.Outside.L_meta_14440_aux

theorem PEqualNP.Outside.L_meta_14440 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_14440_aux.main
