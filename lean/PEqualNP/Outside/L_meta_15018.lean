import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15018_aux

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

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcfcfccccc0000fcfcfcfccccc0000fcfcfcfccccc0000fcfcfcfccccc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefeeeee0000fefefefeeeee0000fefefefeeeee0000fefefefeeeee0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_85 : Nat := 0x3300330000000000330033
def goal_85 : Nat := 0xfafafafafafafafaaaaa0000aaaa0000fafafafafafafafaaaaa0000aaaa0000
def roots_85 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfefefafafefefafaeeee0000eeee0000fefefafafefefafaeeee0000eeee0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_99 : Nat := 0xf0000000f0000000f0000000f
def goal_99 : Nat := 0xeeeeeeeeaaaaaaaaeeeeeeee00000000eeeeeeeeaaaaaaaaeeeeeeee00000000
def roots_99 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfcfcfcfcf0f0f0f0fcfcfcfc00000000fcfcfcfcf0f0f0f0fcfcfcfc00000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefafafafafefefefe00000000fefefefefafafafafefefefe00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_105 : Nat := 0x303000003030000030300000303
def goal_105 : Nat := 0xffaaffaaffaaffaaaaaaaaaa00000000ffaaffaaffaaffaaaaaaaaaa00000000
def roots_105 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_107 : Nat := 0xf0f00000f0f00000f0f00000f0f
def goal_107 : Nat := 0xffeeffeeffaaffaaeeeeeeee00000000ffeeffeeffaaffaaeeeeeeee00000000
def roots_107 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_108 : Nat := 0x1111000011110000111100001111
def goal_108 : Nat := 0xfff0fff0fff0fff0f0f0f0f000000000fff0fff0fff0fff0f0f0f0f000000000
def roots_108 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_109 : Nat := 0x3333000033330000333300003333
def goal_109 : Nat := 0xfffafffafffafffafafafafa00000000fffafffafffafffafafafafa00000000
def roots_109 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfff0fff0fcfcfcfc00000000fffcfffcfff0fff0fcfcfcfc00000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffafffafefefefe00000000fffefffefffafffafefefefe00000000
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_162 : Nat := 0x50000000500000000000000000000000500000005
def goal_162 : Nat := 0xffffffffccccccccffffffffcccccccccccccccc00000000cccccccc00000000
def roots_162 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee00000000eeeeeeee00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaafafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xffffffffccccccccffffffffccccccccfcfcfcfc00000000fcfcfcfc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeefefefefe00000000fefefefe00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaaaaaaaaa00000000aaaaaaaa00000000
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeeeeeeeee00000000eeeeeeee00000000
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xffffffffff00ff00ffffffffff00ff00f0f0f0f000000000f0f0f0f000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xffffffffffaaffaaffffffffffaaffaafafafafa00000000fafafafa00000000
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xffffffffffccffccffffffffffccffccfcfcfcfc00000000fcfcfcfc00000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xffffffffffeeffeeffffffffffeeffeefefefefe00000000fefefefe00000000
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_197 : Nat := 0x33000000000000003300000000000000330000000000000033
def goal_197 : Nat := 0xfafafafafafafafaaaaaaaaaaaaaaaaafafafafafafafafa0000000000000000
def roots_197 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefeeeeeeeeeeeeeeeeefafafafafafafafa0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffaaffaaffaaffaa0000000000000000
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfff0fff0fff0fff0ff00ff00ff00ff00fff0fff0fff0fff00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_205 : Nat := 0x3333000000000000333300000000000033330000000000003333
def goal_205 : Nat := 0xfffafffafffafffaffaaffaaffaaffaafffafffafffafffa0000000000000000
def roots_205 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcffccffccffccffccfff0fff0fff0fff00000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffeffeeffeeffeeffeefffafffafffafffa0000000000000000
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_225 : Nat := 0x300000003000000030000000300000003000000030000000300000003
def goal_225 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000
def roots_225 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeaaaaaaaaeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0ffffffff00000000f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafaffffffffaaaaaaaafafafafafafafafafafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcffffffffccccccccfcfcfcfcf0f0f0f0fcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefeffffffffeeeeeeeefefefefefafafafafefefefe00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_232 : Nat := 0x10100000101000001010000010100000101000001010000010100000101
def goal_232 : Nat := 0xffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff000000000000000000
def roots_232 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaffaaffaaaaaaaaaa00000000
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffffccffccffccffccff00ff00cccccccc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeffaaffaaeeeeeeee00000000
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0ffffffffff00ff00fff0fff0fff0fff0f0f0f0f000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffaffffffffffaaffaafffafffafffafffafafafafa00000000
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcffffffffffccffccfffcfffcfff0fff0fcfcfcfc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffeffffffffffeeffeefffefffefffafffafefefefe00000000
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffefffeffffffffffeeffeefffefffefffefffafefefefeeeee0000
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_161
def pairsG : List (Nat × Nat) := [(1, 33), (1, 129), (32, 33), (32, 160), (128, 129), (128, 160)]
def r1sG : List Nat := [1, 1, 32, 32, 128, 128]
def r2sG : List Nat := [33, 129, 33, 160, 129, 160]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_161.map (· &&& dom_161)
def goalM : Nat := goal_161 &&& dom_161
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xa88ed650
  | 3, 0 => 0xa88ed650
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3000000000000000000000000000000030000000000000000000000000000000200000002000000000000000000000002000000020000000000000000000000030000000300000000000000000000000000000000
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
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xc0f0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2d5fa
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
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_161 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_161 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_161 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffff00000000ffffffff00000000, 96), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffff00000000ffffffff00000000, 96), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_161 == dom_161) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_161 goalM v ys) : RunD true dom_161 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_161 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i, 0 ≤ i → i < 1 → Z 2 i = true := span_ok (by decide +kernel : span (Z 2) 1 0 = true)
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
  scr true dom_161 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_161 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_161 roots_161 goal_161 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_161 goal_161 := by
    have h0 : isConstB dom_161 goal_161 = false := by decide +kernel
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

end S_161

theorem lowS_161 : Lower true dom_161 roots_161 goal_161 4 := S_161.noCircuit

def isoMvS_162 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_162 : Lower true dom_162 roots_162 goal_162 4 :=
  lower_iso isoMvS_162 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_161

namespace S_53
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (4, 36), (5, 21), (5, 37), (16, 17), (20, 21), (20, 52), (32, 33), (32, 36), (48, 49), (48, 52)]
def r1sG : List Nat := [1, 1, 4, 5, 5, 16, 20, 20, 32, 32, 48, 48]
def r2sG : List Nat := [17, 33, 36, 21, 37, 17, 21, 52, 33, 36, 49, 52]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_53.map (· &&& dom_53)
def goalM : Nat := goal_53 &&& dom_53
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x531db19e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33003300000000000000000000000000000000000000000000000000000000003300000033000000000000000000000000000000000000000000000000000000300030003000300000000000000000000000000000000000000000000000000022002200220022
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf00ce00dc01b
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf96ce9adc57b
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
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_53 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_53 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_53 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_53 == dom_53) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_53 goalM v ys) : RunD true dom_53 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_53 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_53 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_53 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_53 roots_53 goal_53 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_53 goal_53 := by
    have h0 : isConstB dom_53 goal_53 = false := by decide +kernel
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

end S_53

theorem lowS_53 : Lower true dom_53 roots_53 goal_53 4 := S_53.noCircuit

theorem lowS_163 : Lower true dom_163 roots_163 goal_163 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0000000a00000000000000000000000a0000000a, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_162

theorem lowS_165 : Lower true dom_165 roots_165 goal_165 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x300000003000000000000000000000003000000030, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_161

def isoMvS_54 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_54 : Lower true dom_54 roots_54 goal_54 4 :=
  lower_iso isoMvS_54 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_85 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32)]
theorem lowS_85 : Lower true dom_85 roots_85 goal_85 4 :=
  lower_iso isoMvS_85 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_99 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_99 : Lower true dom_99 roots_99 goal_99 4 :=
  lower_iso isoMvS_99 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_102 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_102 : Lower true dom_102 roots_102 goal_102 4 :=
  lower_iso isoMvS_102 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_105 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_105 : Lower true dom_105 roots_105 goal_105 4 :=
  lower_iso isoMvS_105 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_108 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_108 : Lower true dom_108 roots_108 goal_108 4 :=
  lower_iso isoMvS_108 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_166 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_166 : Lower true dom_166 roots_166 goal_166 5 :=
  lower_iso isoMvS_166 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_165

def isoMvS_169 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_169 : Lower true dom_169 roots_169 goal_169 5 :=
  lower_iso isoMvS_169 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_165

def isoMvS_172 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_172 : Lower true dom_172 roots_172 goal_172 4 :=
  lower_iso isoMvS_172 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_195 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_195 : Lower true dom_195 roots_195 goal_195 4 :=
  lower_iso isoMvS_195 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_197 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)]
theorem lowS_197 : Lower true dom_197 roots_197 goal_197 4 :=
  lower_iso isoMvS_197 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_204 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_204 : Lower true dom_204 roots_204 goal_204 4 :=
  lower_iso isoMvS_204 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_225 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_225 : Lower true dom_225 roots_225 goal_225 5 :=
  lower_iso isoMvS_225 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_165

def isoMvS_228 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_228 : Lower true dom_228 roots_228 goal_228 4 :=
  lower_iso isoMvS_228 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_232 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_232 : Lower true dom_232 roots_232 goal_232 4 :=
  lower_iso isoMvS_232 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

theorem lowS_55 : Lower true dom_55 roots_55 goal_55 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa00aa00aa, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_54

theorem lowS_87 : Lower true dom_87 roots_87 goal_87 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc0000000000cc00cc, 16, 18)] (by decide +kernel) (by decide +kernel) lowS_85

theorem lowS_167 : Lower true dom_167 roots_167 goal_167 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa000000aa0000000000000000000000aa000000aa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_166

theorem lowS_173 : Lower true dom_173 roots_173 goal_173 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30300000303000000000000000000000303000003030, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_169

namespace S_227
def pairsG : List (Nat × Nat) := [(1, 33), (1, 65), (1, 129), (2, 34), (2, 130), (3, 35), (3, 67), (3, 131), (32, 33), (32, 34), (32, 160), (64, 65), (66, 67), (66, 98), (66, 194), (96, 97), (96, 98), (96, 224), (128, 129), (128, 130), (128, 160), (192, 193), (192, 194), (192, 224)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 32, 32, 32, 64, 66, 66, 66, 96, 96, 96, 128, 128, 128, 192, 192, 192]
def r2sG : List Nat := [33, 65, 129, 34, 130, 35, 67, 131, 33, 34, 160, 65, 67, 98, 194, 97, 98, 224, 129, 130, 160, 193, 194, 224]
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_227.map (· &&& dom_227)
def goalM : Nat := goal_227 &&& dom_227
def NN : Nat → Nat
  | 4 => 3
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x93a230df4b2c333b49cf8990
  | 5, 0 => 0xcecf14f047887c2e
  | 6, 0 => 0xd453940d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3000000030000000300000003000000030000000000000003000000000000000f0000000f00000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000f0000000f0000000f000000000000000f0000000f0000000f0000000f0000000f0000000f0000000f000000000000000f000000000000000f000000000000000f000000000000000f000000000000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000a0000000a0000000a0000000a0000000a0000000a0000000a0000000a0000000f0000000f0000000f0000000f00000000000000000000000000000000
  | 0, 1 => 0xf0000000f0000000f000000000000000f0000000f0000000f000000000000000f0000000f0000000f0000000f0000000f000000000000000f00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x317605532105432105
  | 5, 0, 0 => 0x9321058321606
  | 6, 0, 0 => 0x321605
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xff8700e3f80003ff00ffff000387000070f80000e7fc0000
  | 0, 1 => 0xe3ff00ff8700
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xb68505e3f84201bb6bffffff93a7294972f82499e7fe4494
  | 0, 1 => 0xf3ff6bffe7bd
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 24 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 24 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 10 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 10 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 10 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 10 then wireAt i else 0
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
  | 3 => 1
  | 4 => 11
  | 5 => 32
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 3, 0 => 0x329ca04
  | 4, 0 => 0xebf6a50ad453940d9da6630f5fe57aec5d2e3d9457ab7737388395952f7106fb14144d0511e7b9fc0f7212b4
  | 5, 0 => 0xd453940dcfff9ba9c6266eadc26b56f1c1c33291bac8c352ba412bc8aafeb602a40bbbbf99b2dbd5956d64d59011177c8e3786117ad91fbc75d8e23a717b9a95701775346d0f42085ffe66875e23b1604c6fede934fb3256310c78c02f7106fb2bda558529cad8112064c2f21a1c63e1199f69db19194cd4176c39190b2c8a8c
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 3, 0 => 0x0
  | 4, 0 => 0x302030200000003000001
  | 5, 0 => 0x201030302030200030202020203000002030203040302030202000002030002
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 7 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 1
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xb4bcacab
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x85102
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_162 roots_162 4 s ws hint
  | 1 => checkCutEntry true dom_195 roots_195 4 s ws hint
  | 2 => checkCutEntry true dom_225 roots_225 5 s ws hint
  | 3 => checkCutEntry true dom_163 roots_163 5 s ws hint
  | 4 => checkCutEntry true dom_99 roots_99 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_227 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_162 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_195 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_225 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_163 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_99 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_227 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_227 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_227 == dom_227) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_227 goalM v ys) : RunD true dom_227 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_227 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
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
  scr true dom_227 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_227 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_227 roots_227 goal_227 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_227 goal_227 := by
    have h0 : isConstB dom_227 goal_227 = false := by decide +kernel
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

end S_227

theorem lowS_227 : Lower true dom_227 roots_227 goal_227 7 := S_227.noCircuit

theorem lowS_229 : Lower true dom_229 roots_229 goal_229 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3000000030000000300000003000000030000000300000003000000030, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_225

namespace S_230
def pairsG : List (Nat × Nat) := [(2, 34), (2, 130), (4, 36), (4, 68), (6, 38), (6, 70), (6, 134), (32, 34), (32, 36), (32, 160), (64, 68), (66, 70), (66, 98), (66, 194), (96, 98), (96, 100), (96, 224), (128, 130), (128, 160), (132, 134), (132, 164), (132, 196), (192, 194), (192, 196), (192, 224)]
def r1sG : List Nat := [2, 2, 4, 4, 6, 6, 6, 32, 32, 32, 64, 66, 66, 66, 96, 96, 96, 128, 128, 132, 132, 132, 192, 192, 192]
def r2sG : List Nat := [34, 130, 36, 68, 38, 70, 134, 34, 36, 160, 68, 70, 98, 194, 98, 100, 224, 130, 160, 134, 164, 196, 194, 196, 224]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_230.map (· &&& dom_230)
def goalM : Nat := goal_230 &&& dom_230
def NN : Nat → Nat
  | 4 => 3
  | 5 => 4
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa4a8677414267388056dae2d
  | 5, 0 => 0xc1f948d8bbbb96dd935a7b7e0244ad5d
  | 6, 0 => 0xd481a3b2
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5000000050000000500000000000000050000000500000005000000000000000000000000000000000000000000000055000000440000005500000044000000550000005500000000000000000000005500000055000000000000000000000055000000550000000000000000000000550000005500000055000000000000005500000000000000550000000000000055000000000000005500000000000000500000005000000050000000500000005000000050000000500000005000000044000000440000004400000044000000440000004400000044000000440000005500000055000000550000005500000000000000000000000000000000
  | 0, 1 => 0x5500000055000000550000005500000044000000440000004400000044000000550000004400000055000000440000005500000044000000550000004400000011000000000000001100000000000000110000000000000011000000000000005500000055000000550000000000000055000000550000005500000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x831705632155432105
  | 5, 0, 0 => 0x32b15060832105a3215063219506
  | 6, 0, 0 => 0x321505
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe0ffc0007efcf83f801c1ff8000e1c00e001f00070e7fe0000
  | 0, 1 => 0xff1c39807efcc038701c1ff80
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xa2b94080366d7c3f851e1fdbd8ae9caae235f094f1e7ff2242
  | 0, 1 => 0xffbd79d7fefde2b0609f5ffbd
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 25 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 25 (i % 8)
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
def CN0 : Nat → Nat
  | 3 => 2
  | 4 => 14
  | 5 => 28
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 3, 0 => 0xbe84b04e37135549
  | 4, 0 => 0xd481a3b2c9b514b5be84b04eb3a61915a8ecc2367888c5e9738ac7866e968b7260f3f5254e8359c02d1c520d22509dff14c907a7079f4e77
  | 5, 0 => 0xd481a3b2d240fdc8d098b9d6cc93c723c7e1d224bee9b59ab06c465692b11b138f82fc568c4b089279e4b9ac71a9aa3a6cb1d3e06b77422b6983b523642213e260f3f5255e51c10555be951751acce3a3d2a88993d0a49bd321909ca313a88651f4745f615efde48132d4c0a0650e42f
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 3, 0 => 0x0
  | 4, 0 => 0x200000100000200020103000201
  | 5, 0 => 0x2030002000202020202000002020002020201010201020100020003
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 6 0 (CN0 s)
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
  | 0 => checkCutEntry true dom_162 roots_162 4 s ws hint
  | 1 => checkCutEntry true dom_228 roots_228 4 s ws hint
  | 2 => checkCutEntry true dom_166 roots_166 5 s ws hint
  | 3 => checkCutEntry true dom_102 roots_102 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_230 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_162 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_228 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_166 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_102 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_230 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_230 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccccccccccccccccccc, 126)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_230 == dom_230) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_230 goalM v ys) : RunD true dom_230 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_230 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 4 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 4 0 = true)
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
  scr true dom_230 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_230 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_230 roots_230 goal_230 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_230 goal_230 := by
    have h0 : isConstB dom_230 goal_230 = false := by decide +kernel
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

end S_230

theorem lowS_230 : Lower true dom_230 roots_230 goal_230 7 := S_230.noCircuit

namespace S_236
def pairsG : List (Nat × Nat) := [(4, 36), (4, 68), (8, 72), (8, 136), (12, 44), (12, 76), (12, 140), (32, 36), (32, 160), (40, 44), (40, 104), (40, 168), (64, 68), (64, 72), (96, 100), (96, 104), (96, 224), (128, 136), (128, 160), (132, 140), (132, 164), (132, 196), (192, 196), (192, 200), (192, 224)]
def r1sG : List Nat := [4, 4, 8, 8, 12, 12, 12, 32, 32, 40, 40, 40, 64, 64, 96, 96, 96, 128, 128, 132, 132, 132, 192, 192, 192]
def r2sG : List Nat := [36, 68, 72, 136, 44, 76, 140, 36, 160, 44, 104, 168, 68, 72, 100, 104, 224, 136, 160, 140, 164, 196, 196, 200, 224]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_236.map (· &&& dom_236)
def goalM : Nat := goal_236 &&& dom_236
def NN : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x1c1d73f9
  | 5, 0 => 0x9e4525c15f296ce527f06f9b
  | 6, 0 => 0x9e4525c1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x1111000011110000110000001100000011110000111100001100000011000000111100001111000011110000000000001111000011110000111100000000000010100000101000001010000010100000101000001010000010100000101000001111000000000000111100000000000011110000000000001111000000000000110000001100000011000000110000001100000011000000110000001100000001010000010100000101000000000000010100000101000001010000000000001111000011110000000000000000000011110000111100000000000000000000111100001111000011110000111100000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x46885
  | 5, 0, 0 => 0x474859dd21b47486
  | 6, 0, 0 => 0x47485
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 19
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe0ff3e707fe007000e601cf8000073e707fe0383e001fe0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf5ff3f7d7fedcf0a5e715cf9145573e616b413c3e84dff0948
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
  | 4, 0 => 0x9e4525c167b598d35009ea1a0b336cf7
  | 5, 0 => 0x660285614ee92ee9356554252e4f0c261781b055130bb224
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x1010200
  | 5, 0 => 0x10102030004
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
  | 0 => checkCutEntry true dom_204 roots_204 4 s ws hint
  | 1 => checkCutEntry true dom_232 roots_232 4 s ws hint
  | 2 => checkCutEntry true dom_172 roots_172 4 s ws hint
  | 3 => checkCutEntry true dom_228 roots_228 4 s ws hint
  | 4 => checkCutEntry true dom_108 roots_108 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_236 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_204 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_232 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_172 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_228 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_108 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_236 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_236 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xffffffffffffffff0000000000000000, 64), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124)], [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124)], [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_236 == dom_236) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_236 goalM v ys) : RunD true dom_236 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_236 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_236 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_236 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_236 roots_236 goal_236 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_236 goal_236 := by
    have h0 : isConstB dom_236 goal_236 = false := by decide +kernel
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

end S_236

theorem lowS_236 : Lower true dom_236 roots_236 goal_236 7 := S_236.noCircuit

def isoMvS_103 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_103 : Lower true dom_103 roots_103 goal_103 5 :=
  lower_iso isoMvS_103 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_107 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_107 : Lower true dom_107 roots_107 goal_107 5 :=
  lower_iso isoMvS_107 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_109 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem lowS_109 : Lower true dom_109 roots_109 goal_109 5 :=
  lower_iso isoMvS_109 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_110 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_110 : Lower true dom_110 roots_110 goal_110 5 :=
  lower_iso isoMvS_110 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_171 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_171 : Lower true dom_171 roots_171 goal_171 6 :=
  lower_iso isoMvS_171 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_167

def isoMvS_174 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_174 : Lower true dom_174 roots_174 goal_174 6 :=
  lower_iso isoMvS_174 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_173

def isoMvS_199 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem lowS_199 : Lower true dom_199 roots_199 goal_199 5 :=
  lower_iso isoMvS_199 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_203 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_203 : Lower true dom_203 roots_203 goal_203 5 :=
  lower_iso isoMvS_203 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_205 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem lowS_205 : Lower true dom_205 roots_205 goal_205 5 :=
  lower_iso isoMvS_205 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_206 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_206 : Lower true dom_206 roots_206 goal_206 5 :=
  lower_iso isoMvS_206 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_233 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_233 : Lower true dom_233 roots_233 goal_233 6 :=
  lower_iso isoMvS_233 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_229

def isoMvS_234 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_234 : Lower true dom_234 roots_234 goal_234 7 :=
  lower_iso isoMvS_234 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_230

theorem lowS_111 : Lower true dom_111 roots_111 goal_111 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa0000aaaa0000aaaa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_110

theorem lowS_175 : Lower true dom_175 roots_175 goal_175 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa00000000000000000000aaaa0000aaaa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_174

namespace S_231
def pairsG : List (Nat × Nat) := [(1, 33), (1, 65), (1, 129), (2, 34), (2, 130), (3, 35), (3, 67), (3, 131), (4, 36), (4, 68), (5, 37), (5, 69), (5, 133), (6, 38), (6, 70), (6, 134), (7, 39), (7, 71), (7, 135), (32, 33), (32, 34), (32, 36), (32, 160), (64, 65), (64, 68), (66, 67), (66, 70), (66, 98), (66, 194), (96, 97), (96, 98), (96, 100), (96, 224), (128, 129), (128, 130), (128, 160), (132, 133), (132, 134), (132, 164), (132, 196), (192, 193), (192, 194), (192, 196), (192, 224)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 32, 32, 32, 32, 64, 64, 66, 66, 66, 66, 96, 96, 96, 96, 128, 128, 128, 132, 132, 132, 132, 192, 192, 192, 192]
def r2sG : List Nat := [33, 65, 129, 34, 130, 35, 67, 131, 36, 68, 37, 69, 133, 38, 70, 134, 39, 71, 135, 33, 34, 36, 160, 65, 68, 67, 70, 98, 194, 97, 98, 100, 224, 129, 130, 160, 133, 134, 164, 196, 193, 194, 196, 224]
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_231.map (· &&& dom_231)
def goalM : Nat := goal_231 &&& dom_231
def NN : Nat → Nat
  | 4 => 5
  | 5 => 31
  | 6 => 53
  | 7 => 14
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xdf27b5dda8bd80ffa634a87e8171ed413c31dbea
  | 5, 0 => 0xfed9c1e1f9689b97f3a86093e07cb34dd771514cd34c1997c6c16f59c32a09faba345734ac997506aa8e55f2a58a2a64a17c66609d192ef39b23b0b47cdde8a87b1ef88962498db8568ae991474f5687440bb99b43fcf6613dac347b3bec1fe13b3e8a523b08682d371ab67a2d880182289be359072a93ab06da2124
  | 6, 0 => 0xfdf261e8fceb5699fc0b86fcf3968965e7cd7883e74ea6f0e7491918d87d2f2cd82f5b45d4a0e02fce217f7fcd4af2bccb042fb1c8c776e4c5eb0a6cc3d6acbdc2e7a16bc0ebab41bf559593b9f171deb840e302ada2d601a89e5f54a7e89290a6a8e115a257edf5996a8bf29394040791a09a9a883588ba8657a7448127b6f26985bee86345cba86200e4bb5e39beb14b83059347f48a7d44ba6c4039ef72ea34749b99331a3d6d2ac5975421971ca61e0e41c31a7fc6ad19f2a3d41658d2fd159b62050dac14c70c3c73ce072a93ab04edcbf8
  | 7, 0 => 0xd7ebfbd2cf8e6038c90e5d9cc8c776e4b0a7ec87af9fdd4b91e3752b877aea086b432cc35573cc96252597bc21971ca61e5cfe690e172dc2
  | 8, 0 => 0xa26a090d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000ff00000000000000ff00000000000000ff00000000000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000aa000000aa000000aa000000aa000000aa000000aa000000aa000000aa000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000ff000000aa000000ff000000aa000000aa000000aa000000aa000000aa0000003300000033000000330000003300000033000000000000003300000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000
  | 0, 1 => 0xff000000ff000000ff000000ff000000330000000000000033000000000000003300000033000000330000003300000000000000000000000000000000000000ff000000ff000000ff00000000000000ff000000ff000000ff000000000000003300000033000000330000003300000033000000330000003300000000000000ff000000ff000000ff000000ff0000000000000000000000000000000000000000000000ff00000000000000ff000000ff00000000000000ff000000000000000000000033000000000000003300000033000000000000003300000000000000000000000000000000000000ff000000ff000000ff000000ff00000000
  | 0, 2 => 0xff00000033000000ff00000033000000ff00000000000000ff0000000000000033000000000000003300000000000000330000000000000033000000000000000f0000000f0000000f0000000f0000000f0000000f0000000f00000000000000ff000000ff0000000000000000000000ff000000ff000000ff000000000000000f0000000f00000000000000000000000f0000000f0000000f00000000000000ee000000ee000000ee000000ee000000ee000000aa000000ee000000aa000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000000000ff000000ff000000ff0000000000000000000000000000000000000000
  | 0, 3 => 0xff000000cc000000ff000000cc000000ff000000cc000000ff000000cc000000ff000000ff000000ff000000ff000000cc000000cc000000cc000000cc000000550000005500000055000000550000005500000055000000550000000000000000000000000000000000000000000000ff000000ff000000ff000000000000000000000000000000ff000000ff00000000000000000000000000000000000000ff000000ff0000003300000000000000ff000000ff00000033000000000000000f0000000f00000003000000000000000f0000000f0000000300000000000000ff000000cc000000ff000000cc000000cc000000cc000000cc000000cc
  | 0, 4 => 0xff00000000000000ff00000000000000cc00000000000000cc000000f0000000f0000000ff000000ff000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000ff000000f0000000f0000000f0000000f0000000ff00000000000000ff000000000000000000000000000000000000000000000000000000ff000000000000000000000000000000ff00000000000000000000000f0000000f0000000f0000000c0000000f0000000f0000000f0000000c00000000000000ff00000000000000ff00000000000000ff0000000000000000000000ff00000000000000ff000000ff000000ff00000000000000ff00000000
  | 0, 5 => 0xff000000ff0000000000000000000000ff00000000000000cc000000cc000000cc000000cc000000cc00000000000000cc00000000000000ff000000ff000000ff000000ff000000ff000000cc000000ff000000cc000000ff000000ff00000000000000ff000000ff000000ff000000000000000000000000000000ff00000000000000ff00000000000000000000000000000000000000ff000000f0000000ff000000f0000000f0000000f0000000f0000000f0000000cc000000ff000000cc000000ff000000cc000000cc000000cc000000cc000000000000000000000000000000ff00000000000000000000000000000000
  | 0, 6 => 0xff000000000000000000000000000000ff00000000000000ff000000ff000000ff000000cc000000ff000000ff000000ff000000cc000000ff000000ff000000ff000000ff0000000000000000000000ff0000000000000033000000330000003300000000000000330000003300000033000000000000000f0000000f0000000f000000000000000f0000000f0000000f00000000000000ff000000ff000000ff00000000000000ff000000ff0000000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000000000000000000000000000000000000000000000000000ff00000000000000ff00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x40c52405283141014a0c524052070c615440c20405
  | 5, 0, 0 => 0x7c40de14061c319d00b634718554b67070c615b61c615a64b60040d8140500a0c614055c315600b61c615500b65071854cb61070d200b64470c615063470c504b61c314f00e61c314100b63470c530b6
  | 5, 0, 1 => 0x7070c616863431859cb634798614b61c314c00b60040c6080534794614b6103141024610a0c614061c31418cb634718588b61c615300b610315600e63470c674b634318584b63600c614b6
  | 6, 0, 0 => 0x3441c31852dcd1c31852ce73470c614ba1cd1c378614b70141c31852d841c318500e71070c61402dc70de18502b71070de18501d41c318500b71031855802dc01ea18500b635c1c31852dc70e918500b70070c50402d870c616700b7
  | 6, 0, 1 => 0x300c6140ad870c614084b71ef0c61402de01c318500b77c70de1402dc70c614f00b74470c61402dcd1c31852db71070ee1402dc41c314100b71c31850402dc01c360500b6b470c61402dc010318502461c3185b002dcd1c31852eb7
  | 6, 0, 2 => 0x7070c61402dc0347185ccb60070c61722d870c61632eb71070c61632dcd1c617300b70079861402d870c55802ce700d1c31852d8d1c31852d070070c615a2d971c318500b7007185cc02d870c617200b744d1c31852dcd1c3185c4b7
  | 6, 0, 3 => 0x1f10318500b70070c60802db63470c614b71f50c61402dcd1c3185d0b7
  | 7, 0, 0 => 0x1f70c61402dc7c0318500b71c31855802dc03470c614b67c70c61402dcd1c318500b71c3185c402dc70c61402e471c318500b6dc01c31858cb61c318500badc41c318500b71c318500b39c70de18500b7
  | 8, 0, 0 => 0x1c318500b6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 34
  | 5 => 40
  | 6 => 46
  | 7 => 46
  | 8 => 40
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1e07800000001e07e0f800000071ce7fffe07800000f00007ff0000000071ce7fffe0780000f01ff800000
  | 0, 1 => 0xfffe0780000ffe00000000f01fff80000fffe1f80000ffe00000000fffe0780000fffe07800000fffff80000
  | 0, 2 => 0xfffe0780000001e0780000f0ffff80000f01fff80000f01fff8000000000071ce7ffffff80000f0000000000
  | 0, 3 => 0x1fe7fe0f8ffe1e07e0f8ffffff80000001fff800000fe00000000f01fff80000f01fff800000001e07e0f8
  | 0, 4 => 0xffe1e07e0f80fe0007ff000fe0007ff0000000000000f001f800000f01fff800f8ffe1f8000000ffe0780000
  | 0, 5 => 0xfe0078000000000000000ffffe7fe0f8fffff800000ffe000000000f00007ff00ffe1e07e0f80fe00000000
  | 0, 6 => 0x780000f01ffffe0f8ffe00780000f01e1f80000f01fff80000f01ff800000fffff800000001e0780000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x849e87925292245e17e0f8112228f1ce7ffff87db5bd4f08527ff0095b22cf1ce7ddba0681505f81ff824a42
  | 0, 1 => 0xfffb06c9595ddb00401004fc9fffb6f6bddba1e81f07fff104490947b6f83db5bd592a0281505036efbfffff
  | 0, 2 => 0xddbe879352d849a0680501b0f7ad800fff81ffbb6f6bb017a98006b3367a9fbcffffffffffffffc910400000
  | 0, 3 => 0xa6dfe7fe5f9fff5e57f0fceeddd70e318000efbb6f6b07e00449094fc9ffea4f43b097ac80043a6d5e57e0f8
  | 0, 4 => 0x7b61606d0d44fe8567ff944f68527ff948490040000078017824a42b0d7ad800fb7b61786dad687fe87db5bd
  | 0, 5 => 0x7e007db5bd2245815a0b8ffffe7ff5fdfb7ff86dad67b610049094cf98567ff007b65e17f0fc03600049094
  | 0, 6 => 0x4800792529fedffffeffbfff107db5bddc9a1e80f03b097ad8006bfc9ffc24a42fffffc6dad6000e8392529
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 44 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 44 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 56 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 56 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 56 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 56 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN0 : Nat → Nat
  | 4 => 11
  | 5 => 68
  | 6 => 227
  | 7 => 53
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0xf9815c50aa9b62757b7230424a8404ed482d081545eea49e440bb99b3e0fbd603ad328aa1b72b5db15a20aca
  | 5, 0 => 0xe76c993fe563ba63d87d2f2cd5323db3d40043d8cd77c453c952d1b8c8a5258ec89f50cfc6b88510bf71ddd2be08dce2bc823247bc1238aab91493e0b6d03449b6494c7caff51a22a26a090d98140ada96b6840a8fe32cbf8b7ccb90885e5292797cd2e97803962475ee57d371214d8c6ffe0a3a6da70d626b68a9eb69e5c7fa6985bee864c777db6200e4bb60ac998a5573cc96554feb9b4a35cbfa451640ed3e530a613bf8cfdc3943e083356a279e331a3d6d2f65e2f8291c9a96290dd75c259276062348c4702203faf01fde7d751c8f8271150aa84412e672ac1236efcf11e3c06f0e316faf0ce26a9a0953ef840908752106e2bfa106b4287501f11f28
  | 5, 1 => 0xfdca2b78fc3c0f5ef82d0f8cf6d56503
  | 6, 0 => 0x541c43e3533abbd7505373ee4e969fe34e0a2f434dde5b264bc3c7724a070cae474be3f344ed38b444d98fda43c21ea541c46fd3408657123feb878a3eb2b5d93ca533b03c4c32fd3a84ad913872ba68375dc5bc36c3c37e33c8394032e9f07232970bce30c7029c307d0e502e54126a2e244a5a2c5cc4ee2b63add629f60617289a9ebe26f465fc25beacd8252597bc240807b321b614ab206750af1f4488e21e9ebbe81e5cfe691e4cf04c1d5b8e2f1d3537dd1b44580919b6a01019164e79181afc52179f69031392051311f6ee34100cffd70ee5394b0e6b992e0e172dc20b0b5ca20a1fa07909087521083578ec0820d8f006b4287503a974c60149b64d
  | 6, 1 => 0x9e1db1969de8bd399c20b0179939d41797f9caed9771fe099708d2de96c3e52d966ceeba9624167295c719839589737d93e382f393406e8e92e1c2e591e3752b91d3aef091bb63768f5fcd478f11cd958eb811f08af5bf5b8a7c01f48984a4bb877aea0886d491e986cc4f2083b9fff58305986882bca2fb829823c18043fe9c800aaf1f7fb5b1a57e336c537e17fc607c182125799c3cdf795be31a77907d8d76bc2e12764d3bdc74618a4473e4327a72700d1d71fd696c702e860b6d6035916b432cc369e5f62d68b14432671c650365481bf1641c122863b1b01062a9a0d4617539d76132cab4603e9498603449815d4f1dcf59132123573c59d95573cc96
  | 6, 2 => 0xd703873dd6d4c106d5ae1925d4c55f69d40e2590d3fd0647d166c1f2d11bc92dd08f18bfcf8e6038cf7447c0ce975ff8cb011b2acaaf9408caa5e724c9dc6925c9163f15c90e5d9cc6927956c450168fc1700aacc120f14bbfd29120bf595db3bed6b321be90321ebd8e1027bb2de16cb95ecc33b9423e0bb8afd920b82833b1b7f606a6b78e8cdfb6a256f7b54b9f24b3fc327bb248482ab1773087b165ecb2b0a7ec87b0306c77af9fdd4baf815e72aeda88daae33b8a5add857dfad6855c7ac095c7eabe9a57aaaaf1324aa90b4f5a97b830aa86a0879a7347fc3a6ccbdb7a6aaf787a6a4e074a48acd3ea3590df3a31378bca26a090da2674cb79f8d9c95
  | 6, 3 => 0xfe56bdc3fe4969a9faac4300f9907d1ff786f16cf7238746f7104ca5f5ebce0ff55504f4f2f43820f2f1c9a0ef6bcb73ec5da0c9ec205dc8ea7b014ce9c5bd72e5cd069ee4cf729fe4713ff4e382e22fe2ae6779e27b6ddfe1fc3794df857439ddebfab6ddba004fdda3eebbdbf6f923db75bee0da8a01c9d80c4ed9d7ebfbd2d73d2436d71b3453d7055a5e
  | 7, 0 => 0xee6e928ce9c5bd72e61db972e45c7366e27b6ddfde133ea9d8fd0873d24904acd18c530dc79f5611c21c5344bcf89f86b7c686b4b78e8cdfb3584fcfb0bdc67cafbddc46af815e72ad9a6d74a59827caa26a090d9a834487998bf218937a182177fa4c4677c6ef217449568972cf49476c605ce1670a06e3601adcb95df36186561e35fe54aee0254eff90d64e7413d94c78bdfc4b5fcefc3c4c32fd3a43d76d395fc133353f4a5f31c3a9fb2ad3f3f729f60617259683f9234ae2cf2025d4401d3537dd1b6701fc1935560513b764700a1fa079
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x303030304040503030101
  | 5, 0 => 0x105050205010505050500050308010305070108080502050105050505000505030404050505050506050807050507080507050505050505050501010805050501050001
  | 6, 0 => 0x702010101050602010802000500060602020505000600050506060601050506060500070506060201070008080100010600010603050706010205060506000606000605010002020606010106010601010605060806010106060608060505060203000806050806020106000100050602060801080102010506010007000008
  | 6, 1 => 0x505010606060502010505000605010007010301010505060006050101000601070302050708070707020105060200010201060106050707060101000506070601080806010000060102010606010102050506030706060102000602020207020208
  | 7, 0 => 0x201020201000200020200000206020700010202020002000000020202020202000001000001060200000202060202020106000206
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 9 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 9
  | 5 => 88
  | 6 => 243
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xedabba89c7383487c729714d9dfc042787b0a6c685fe23f485ef60ba595974080ec3eb3f
  | 5, 0 => 0xc6614dbdc3760974c2ff53a8b646b859ad7fb65aab782941a5b49520a3f34f149e6103fb926435708f0eb2098efe14268a570e9785cbbb1a851ea29280cd7d628054b645775d626276cdedd2750ca7c673f56eca7373abaf72136a636e9b21e76e8f3681674a18e6651023b064c05ff15ba9aa185a030618594f126a52d74a3c51523f244f48a4d04bf3f1d04929afc4491cfe044876bb14470327a937ca9e9b34e0c267343df08c30cf50ed30c7029c302de15d2d11964c2afcc97d2af7dfac1d32d2da1c30df911a6f99851325bfd612bb0ea01105bd0810fea32110e75c5f0f552e2c0e8354900c7b27490ab9e13d09f24079078a5d2205c91716049f5ba6
  | 5, 1 => 0xff729eadfce502ccfca596bff5d763faf1568666ef95405aedd9acd3ecb239d4ec5ace4aebf97a46eafbe89be7491918e6bc4b0be52d5fa7e2a77063de23f48bd9332a64d68794f5d64828e8d2ae5eb8d19cdf6fcd77d812ca8afeb2c8c776e4
  | 6, 0 => 0x4c489abd4c3ad8884bf3f1d049a850a64929afc448ef94bc4683dbaa4683421744833b944392a5b43f92c3dc3daa5bbf3a8215633a14d247382da85d36f39a4d359b4cd134b248143427e7b133d4677333b97c1032e2d02432cc583730c87fba3002162b2e50de332d11964c2b040fcf27531a1226477dd425d90cd0252bf4482373ab6921bbeea11f6a206a1d3e42321b9fac371b2b281a1a8662e91a13ca6c19de662b159ef12e150ff01714cc006313e9fcb31342109d1324a04211d4d3971180ca9110fd250f10232b490cc20e010c7b27490c2a74750b12edf40b00c7f50ab9e13d0aa764f409c6487f0927f98708d8dbb607b8a3ae0470ac8000016f25
  | 6, 1 => 0x8ea2d1bb8d6774ba8cd21af58c06cbfc88df3852883e766f86784a90852c9841849616968450cf5d84406a8a80b1ef74809faa6a7fe43e657e54abb17ddf71d67c7ba3d57b0c4dfc78514f8976cc4471766e9dd475d67a8d755cfead752616cd74d181b072d62bd371bd3cd37002630f6f4d02936e11023a6b2383fc6ad04a3d68d94821674a18e667180215661549ff654acd0b638986ff628b21fb6286cee96210aece6142e0d960a430fd60a14544604f68c25fbd2f0a5f873e6b5e278c7c5b9cb8365b1876be5ac830195a1ed074584e34b2582117d2565d1377554edc3752badb2451cade27513161ce5009981b4ff5ad284e227f4d4d8d08104c95b5a1
  | 6, 2 => 0xd03efb66d02d12b8cfa37206cd77d812cc59b143cc3f198ecbf595a1cb2e9a6dca5dff91c9b67bcac96d5461c6046a2ec4fc5af2c4122559c27e1deec0e0b25ec019bea8bfe95fefbcab7587b9d785f8b85ee1fdb536c47fb5157fc7b4503e79b32f88ccaef6dd28ae392d81ada64254ad761638ad35971cac32df06a85212a8a73ff2d2a4c39792a1897955a1785615a0296323a02307159e57ba1d9e245cf89e2299149e1610a99d9f4b809d27f3409cd767af9ccf80fb9aeb82829aa6c460992cb71e99277cfb98edb0fc985ad743976636ef958531689507240094819cd792c035b492bdcab8923e864491effbe99143a8ae911d02328fe1ae338efe1426
  | 6, 3 => 0xff828185ff5a764afe65a68dfd60f514fb5e80cafad72b77fa804cb4fa6c5c04f8a67283f805d9d5f7e9c0e4f600dfddf45b9cecf3538db0f29a56e0f19247a4f0fe47f9ee6fa7afee0a52aaedfcc3e8ed4d9af6ed487979ec6984bcea7bd794e879c11be8490de8e69cacf6e5143cc6e4eadddfe4cd6d84e3560d5dde6adb43de23f48bddddb780dcca79e2dc9c5d00daea0a63d9b5bda6d942ff8cd8a04782d654a658d61b4a1dd5decc49d5972590d43ec166d439498ad3f7db4bd3d5df84d32f97c9d2d3276ed0405bc8
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x910549030224415240c099524c9230205491240c019524c9230224415240c099524c9230265493248c089105490302
  | 5, 0 => 0x9124080800000cb10600095238808002548e2000014324480800534932020014d20c808005349320200147234808000549020200093248808002548e20200000234404000008d100001472348080015490202001512348080035490202000d524080800054902020008d348800005448d2000005534880800154902020008d3448000051c8d20200095238808002548e2020000023440000534832020014d20c8080051c8d202
  | 5, 1 => 0x23440000054902000009324880800534932020000023440000054902020009124080800244902020015123480000154d220200000234404002548e200001432448080051c8d2020000032c418005488d2000000024441800244902020014d24c80800534932020000032c418002449020200055240808000008d10000000234404002548e202000002344040054c8d200000d52408080053493200000552408080024490200
  | 5, 2 => 0x1452348000051c8d202001472348080053487200000932488080024c92202000d52408080005490202000912408080051c8d202000553488080051c8d20200143244808002449020200055348808002548e2020014d20c8080051c8d202001472348080050c912020014d24c808002548e2020000032c418000008d101
  | 6, 0 => 0x44408000008d1020000023840800000921020000023c408000005210000000248400000008e1020000023c408000009110000000344408000008d1020000023440000000931020000023840800000901020000024c408000008e10200000234404000008310200000234408000008d1000000034840800000831020000023440800000901020000023c400000008e10000000234404000008e10000000234400000008f102
  | 6, 1 => 0x344400000008310200000234408000008d10200000234400000008d10000000238400000008d10200000348408000008d1010000023440000000d110200000248408000008d1020000020c408000009110200000244408000009210000000348400000008110200000048408000008e10100000234408000008e10200000234400000008e10000000234400000008e10000000238408000009110200000238408000008e100
  | 6, 2 => 0x248408000008d10200000248408000009210000000244408000009110200000238404000009110000000048408000008110200000238408000008d10200000048408000008d10000000144400000005110000000234400000008f1020000034440000000911000000023c400000008d1020000021440000000d21000000024c40800000111020000023440800000111020000023c408000008d10200000238400000008e102
  | 6, 3 => 0x238400000008d10200000234408000008e1020000023c40000000911020000023440800000d110000000238408000008d10200000248408000009110200000348408000008110200000344408000008e10100000234400000008d1000000024040000000901020000023c408000008d10000000234404000008e10000000234400000008d10000000234404000008e10000000234400000009310200000344408000008e102
  | 6, 4 => 0x344408000009110200000048408000008e10200000048408000009310200000234400000008d1000000023c400000009010000000240400000009310000000240408000008e10100000214400000008d10200000234408000008e10200000240408000008d10100000238408000008e1010000024c408000005210000000238400000008d1020000021c40000000d210000000044408000008e10000000044408000008d100
  | 6, 5 => 0x238404000008310200000234400000008d10200000048408000008e10000000234408000009010200000348408000008d10200000240408000008110200000234408000005210000000234404000008d10000000244408000008d10200000044408000008d1000000034440000000d210000000234400000008d1020000023440800000d21020000034440800000851000000021440000000d2102000003484000000092102
  | 6, 6 => 0x234408000008e1020000023c408000008e10000000244400000008d10000000238400000008e10200000238408000009310200000238408000008d1000000020c408000008d1020000023840800000931000000023c40800000d110000000234408000005210000000238408000008e10200000234400000008d10100000344408000009310200000248408000008d10200000344408000008e1020000034440000000d1102
  | 6, 7 => 0x8e10000000234408000009210200000234408000008d1020000024440800000d210200000238408000008d1000000021c400000008d1020000023440000000811020000023440800000811020000023440800000d1102000003484080000092100
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_227 roots_227 7 s ws hint
  | 1 => checkCutEntry true dom_229 roots_229 6 s ws hint
  | 2 => checkCutEntry true dom_230 roots_230 7 s ws hint
  | 3 => checkCutEntry true dom_197 roots_197 4 s ws hint
  | 4 => checkCutEntry true dom_102 roots_102 4 s ws hint
  | 5 => checkCutEntry true dom_199 roots_199 5 s ws hint
  | 6 => checkCutEntry true dom_167 roots_167 6 s ws hint
  | 7 => checkCutEntry true dom_165 roots_165 5 s ws hint
  | 8 => checkCutEntry true dom_103 roots_103 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_231 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_227 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_229 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_230 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_197 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_102 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_199 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_167 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_165 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_231 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_231 goalM v ys := cutHitH_sound h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_231 goalM v ys) : RunD true dom_231 goalM v (ori ys) := h
def Z (s : Nat) := bar true dom_231 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 31 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 31 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 53 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 53 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
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
  scr true dom_231 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_231 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_231 roots_231 goal_231 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_231 goal_231 := by
    have h0 : isConstB dom_231 goal_231 = false := by decide +kernel
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

end S_231

theorem lowS_231 : Lower true dom_231 roots_231 goal_231 9 := S_231.noCircuit

namespace S_237
def pairsG : List (Nat × Nat) := [(1, 33), (1, 65), (1, 129), (4, 36), (4, 68), (5, 37), (5, 69), (5, 133), (8, 72), (8, 136), (9, 41), (9, 73), (9, 137), (12, 44), (12, 76), (12, 140), (13, 45), (13, 77), (13, 141), (32, 33), (32, 36), (32, 160), (40, 41), (40, 44), (40, 104), (40, 168), (64, 65), (64, 68), (64, 72), (96, 97), (96, 100), (96, 104), (96, 224), (128, 129), (128, 136), (128, 160), (132, 133), (132, 140), (132, 164), (132, 196), (192, 193), (192, 196), (192, 200), (192, 224)]
def r1sG : List Nat := [1, 1, 1, 4, 4, 5, 5, 5, 8, 8, 9, 9, 9, 12, 12, 12, 13, 13, 13, 32, 32, 32, 40, 40, 40, 40, 64, 64, 64, 96, 96, 96, 96, 128, 128, 128, 132, 132, 132, 132, 192, 192, 192, 192]
def r2sG : List Nat := [33, 65, 129, 36, 68, 37, 69, 133, 72, 136, 41, 73, 137, 44, 76, 140, 45, 77, 141, 33, 36, 160, 41, 44, 104, 168, 65, 68, 72, 97, 100, 104, 224, 129, 136, 160, 133, 140, 164, 196, 193, 196, 200, 224]
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_237.map (· &&& dom_237)
def goalM : Nat := goal_237 &&& dom_237
def NN : Nat → Nat
  | 4 => 5
  | 5 => 13
  | 6 => 29
  | 7 => 9
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xbe69743795168c8951d911033ab2ea530f6024d9
  | 5, 0 => 0xf54b06fee90b4a26d331ad3785bb0c52841ae0e978f04a9571ce9a9b6ec1b1d65781625332e675d12b8436501dde3a5b068ab1b1
  | 6, 0 => 0xd9f263f1ccee7336b417e3d9b0c83142a5d6b686a4947ffda10f01d6968a72a989b0f7b07e0411486e48120f6321333762cd7ea05ccf3e01586f07af547cb2f4529b6fe247d7a4e347380b863b5c9544381dd915312c87a02e17d28a2db299ec268e94f81e4b0f5d158a1dcc11dbb96c00c453b3
  | 7, 0 => 0xb0c831428dc3092671ee4ae34ed480654154eb0433ee8d6513f494b3125afa10082e3278
  | 8, 0 => 0xd2e18b09
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33330000000000003333000033330000333300003333000000000000222200002222000022220000222200002222000022220000222200002222000033330000333300000000000000000000333300003333000000000000000000003333000033330000333300000000000033330000333300003333000000000000330000003300000033000000330000003300000033000000330000003300000030300000303000003030000030300000303000003030000030300000303000003333000022220000333300002222000022220000222200002222000022220000333300003333000033330000333300003333000033330000000000000000
  | 0, 1 => 0x3333000033000000333300003300000033000000330000003300000033000000333300000000000033330000000000000000000000000000000000000000000033330000000000003333000000000000333300000000000033330000000000001111000011110000111100001111000011110000111100001111000000000000333300003333000033330000333300000000000000000000000000000000000033330000303000003333000030300000303000003030000030300000303000003333000033330000333300003333000033330000333300003333000000000000000000000000000033330000333300000000000000000000333300000000
  | 0, 2 => 0x3333000000330000333300000033000033330000000000003333000000000000333300000000000033330000333300003333000000000000333300000000000000000000333300000000000033330000333300000000000033330000000000000303000003030000030300000303000003030000030300000303000000000000030300000303000000000000000000000303000003030000030300000000000033330000333300003333000033330000333300000000000033330000000000000000000000000000000000000000000033330000333300003333000000000000000000003333000000000000333300000000000000000000000000000000
  | 0, 3 => 0x33000000330000003300000033000000330000003300000000000000000000003300000000000000330000000000000033000000000000003300000000000033330000333300003333000000000000333300003333000000000000000000000000000033330000000000003333000000000000333300000000000000000000330000003333000033000000333300003300000033000000330000003300000033330000333300000000000000000000333300003333000033330000000000000000000000000000333300000000000000000000000000003333000000000000330000003300000033330000330000003300000033000000333300003300
  | 0, 4 => 0x3333000033330000333300003333000033330000330000003333000033000000333300003333000033330000333300000033000000000000003300000000000000000000000000000000000000000000333300003030000033330000303000000303000003030000030300000000000003030000030300000303000000000000333300003333000033330000333300003300000033000000330000003300000033330000330000003333000033000000333300003300000033330000330000000303000003030000030300000303000003030000000000000303000000000000000000000000000000000000000000003333000000000000333300000000
  | 0, 5 => 0x330000003300000033000000330000000000000000000000000000000000000303000003030000030300000303000000000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000033330000303000003333000030300000333300003030000033330000303000003333000033330000333300003333000030300000303000003030000030300000333300003333000000330000000000003333000033330000003300000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x40ca180524308115480c204551c308615440c20405
  | 5, 0, 0 => 0x150c2185510308600e64950c2185634319414b634319314b60120c20455443086150624308614e610308114b610f08614b620308614e634308c14b610328614b6
  | 6, 0, 0 => 0x8920c21852dcd0c21a114b73600c218015c048308614e600d08615f2d8434308600b74830867852dc034308674b610308614b39cd0c218570b735b0c21852dda34308614b764308614b41c060d08614b65cd0c21852dd634308614b7
  | 6, 0, 1 => 0x343086a0b624d0c21852dc034308114b648d0c21852de734308614b73430869852de534308614b710d0c69052dcd20308614b788d8c21852dc0803086150600d0ca1852d8d0c219d14b7
  | 7, 0, 0 => 0x1234308614b734308614b39cd80308614b734308614bb5cd0c21852ec734308614badea34308614b710d0c21852dcd0e908614b7
  | 8, 0, 0 => 0x34308614b6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 34
  | 5 => 40
  | 6 => 46
  | 7 => 46
  | 8 => 40
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffffff8000000000071ce7f01fc000000f01fff8000000003c7ff000f00007e0f800000071ce7ffffc000000
  | 0, 1 => 0x3c7ff0000000000000001e3f80000ffffff80000ffe000000000f00007e0f8ffffff800000fe03f80000
  | 0, 2 => 0xfffe3f800000ffe3f80000fffe3f80000f0ffff80000f01fff80000fffe3f80000001fff80000ffe00000000
  | 0, 3 => 0xffffc000000001e0380000f01fc000000ffe1c000000ffe03c7ff00f01fff8000000003f8000000003ffff00
  | 0, 4 => 0xfffe3ffff00fffe0380000001e3ffe0f8f01fff80000ffe03c7ff00001e3ffff00f0fe3f80000001e3f80000
  | 0, 5 => 0xffe00000000f0e000000000fe000000000f1e3ffe0f8ffe0007e0f8f01fc380000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7b6fddfffff112244f1ce7f81fd024952fc9fffb6d7b42493c7ff002f04897e0f895b266f1ce7fffff26dbd6
  | 0, 1 => 0xc6d93e7ff0084902200000849e3f92429eeddbb0e318fff02249284af94ab7e0f8fffffffffff07e02fdb6ad
  | 0, 2 => 0xbdbe3f924ad87fe3fdb6ad7b6e1ddb6add0fb7681f07d01b5480d03fffe3fdb6ad000fddb6d7b7b600049284
  | 0, 3 => 0xbdb6c2000d684960380029fc9ff2249527b61c06dbd67b693c7ff84f81fddb6d7b04802f9242946c93ffff29
  | 0, 4 => 0xffff3ffffadfff623c92ad000e9db6479d09b7680d03fff93e7ff84c6df3ffff29d0fa3681605000e1d92429
  | 0, 5 => 0xbdb00200084d0f0220120407e02249284af9ebffe4f9fff4ab7f2fcfc9fd3a497b
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 44 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 44 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 46 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 46 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 46 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 46 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 4 => 2
  | 5 => 36
  | 6 => 172
  | 7 => 28
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0x45b94c4f38a47754
  | 5, 0 => 0xefe860deddff5cf9d7eae247d2e18b09c4098a80b7d7bdeeb61d98abb02c851bae432aaca30dd0d1a2979253982697459279c6a48b74b25280e0e59375029dd973cc1098738baac36d3269b4632133375e4673d5529b6fe24c819b92472fe6a33b2b617c381dd915340f49f133d1c8b23381ac10225182631d8cd22415003b221397fa7f0f36dc300ab30da703f4147a
  | 6, 0 => 0x2b564f802b0ffa222b0e91d32a85e9012a20475e29c1d2fe296725c62830b0cc275e647d271d3c6b2664d51a262cc0df262080a825cc86f025639e70247764552423579923e3531523255b4a22873405217aca9a2158d7de207e4a4b1f386c411ec1c5b61e02b1541df557a21d91e91b1bd77e1c1ad519d118964771185838dd13f494b3132df52612655544125afa1010f5c860109f46c9106107f70f326a660e48d00e0ce9e02a0cc80f4f0c9be6f20b4fe9360a7ea0840a58029c0a50ea8009bf0bcc09ba8188082e327807d571f9061015e1057967b404a2097c045d3d6202af8d3a020aa13d01915e3a016e16b80167b6d801148b480096b880005eec48
  | 6, 1 => 0x76eee7d576802746736cb79272db710d727ef90871ee4ae371d1bc9271a6ba71702e7c056ef961f66daf1b3f6d59c6b16cc8a9e26a569f4c6941d97c6932331768cb9edb687b68c7625bd21a61136ee95ec0b8475eacfcc35cc090555c8037925bbe34ad58e90c0558371f47576b26ee5753e0c3572523de55f445f4543878b350fa06004ed480654da397594d97996d4c3473cd4a6b3e1e49f6125e499ec43f4883e66445c6afef45064eca44ba36c64395cdc543098b5e4154eb043fa6f9c13e5afd2038d9cddd38acfae836654b5b35ccb5e4350f59a6345521a133ee8d6532e3cebd31c1384931b04a3f3162e8763114266130efcde42fde50bc2c8edd2e
  | 6, 2 => 0xf2ff5732f14531efed7cdfcee482ee61dff7bea2dbc1cd94d9bea2bdd98283ced5bcdb28d3a30bb8d38afab8d3017378d2e18b09cf99bed2ce603f35ccaf558bcb65e69cc271888dbe6206cfb83939c8b7fd6f42b743d11cb607d378b5e9870fb44a0226b43181f1b096bbe2ad4717c8a748afa2a68a8a2ba42ed1e2a30dd0d1a157afcb9c0a394e9b070a1b9ade219099fc25e396d3de308dc309268d5ddbd48b471efe8572ca68852ee94c80bb956e
  | 7, 0 => 0xeedecc1ee76681fee07f5f67d41253d3d2e18b09cc20f956af03c3969b7e8a3b82edd51f7f188a46768027467358a43465b6cc5b5eacfcc35cd08fa553c264cb4d595c774bde83f838d9cddd345521a131b04a3f31193857281899561d91e91b151bf490151429640d31711d067c3a4b
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x20307010202020205050303020400050003010204020203020202020604030204020306
  | 6, 0 => 0x8060605070203070402060206040504030606040106090a0104010602040304090604050105070406010706070405040504050a0101040406030509010701040302040503050b020609090206010704020705060206040501020b050606020a0506090406050601060a06030608020a060a0505010409090305050202060204
  | 6, 1 => 0x2020607060503010a040906010301040502090102040a020104010306010905050405040606020406040204
  | 7, 0 => 0x10101070101010105010601050601010104040405060a0501060101
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 9 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 2
  | 5 => 26
  | 6 => 65
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x7f3a0b9a02e8db5c
  | 5, 0 => 0xf83716abdc8a747ed7f10420d5032d74d414e6d8c20cddb19faa8cc383a4dc9f828392377be5e66d73936eb4662fa5e663e1688d603944405e57ad9f55757941543851c04788d71345bbad733994f72635c31f6534138f1b2327f22a1bba394c14915f1001ab8a06
  | 6, 0 => 0xbdab2b7b9e983c059c49feac9bc5a9559b60dd84946b746d942c5de0932178399271f44b92484a98921d37148adb7a3085c3218d8374e434835ada2277b68ee47568518b7486d3a772d3a1397238964e6f5829cd60736c865c8cd4e3547236cd516a88e84dddabc64c1e159d4b8f6e6d47a8176c45e301d3418c61c340b6c9d83ab735de34783e1b32dea37831303b3630b581ca2ee1fddd28965cb324e049c922e69daf21926911217ddbd32143d7e52094cc891ff8ce6e1c4393741bfde4581a09890017b20dc215cc06d613189d64114e6232102ac6b80ed60aa00c1529210bfcf6570935696808cd3b1a08422b6f0723b3f6061be31000fe0acc00a494b4
  | 6, 1 => 0xbe6605a0
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x65d09420c059724490301
  | 5, 0 => 0x10a248804004250820100091240804002449020100147344804003550820100015240804000549020100091240804002490a20100055420804003544a201000d51288040024490201001433248040051cd12010001534880400154ca201000d524080400054d22010000031c4100050cc9201000553288040015508201000d50488040035412201
  | 6, 0 => 0x42440400000091010000032440400000ca1010000042440400000ca1010000012440400000ca10100000244404000000910100000144404000004e1040000032840400000c910100000344404000001210100000128404000010810100000044404000009010100000344414000009010100000244404000001110100000028404000009110100000248404000008d10400000128404000005110100000344404000004a101
  | 6, 1 => 0x24040400000c91010000032440400000d11010000024040400000111010000004440400000921010000042840400000c91010000004440400000d110100000128404000004a10100000328404000000a10100000028404000009210100000328404000009210100000148404000000a1010000032440400000d21010000024840400000511010000002840400000511010000024840400000c9106000003484040000092101
  | 6, 2 => 0x91101
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 8 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_204 roots_204 4 s ws hint
  | 1 => checkCutEntry true dom_236 roots_236 7 s ws hint
  | 2 => checkCutEntry true dom_205 roots_205 5 s ws hint
  | 3 => checkCutEntry true dom_109 roots_109 5 s ws hint
  | 4 => checkCutEntry true dom_173 roots_173 6 s ws hint
  | 5 => checkCutEntry true dom_233 roots_233 6 s ws hint
  | 6 => checkCutEntry true dom_229 roots_229 6 s ws hint
  | 7 => checkCutEntry true dom_169 roots_169 5 s ws hint
  | 8 => checkCutEntry true dom_105 roots_105 4 s ws hint
  | 9 => checkCutEntry true dom_165 roots_165 5 s ws hint
  | 10 => checkCutEntry true dom_225 roots_225 5 s ws hint
  | 11 => checkCutEntry true dom_197 roots_197 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_237 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_204 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_236 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_205 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_109 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_173 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_233 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_229 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_169 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_105 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_165 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_225 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_197 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_237 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_237 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_237 == dom_237) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_237 goalM v ys) : RunD true dom_237 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_237 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 13 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 13 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 29 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 29 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
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
  scr true dom_237 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_237 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_237 roots_237 goal_237 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_237 goal_237 := by
    have h0 : isConstB dom_237 goal_237 = false := by decide +kernel
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

end S_237

theorem lowS_237 : Lower true dom_237 roots_237 goal_237 9 := S_237.noCircuit

namespace S_238
def pairsG : List (Nat × Nat) := [(2, 34), (2, 130), (4, 36), (4, 68), (6, 38), (6, 70), (6, 134), (8, 72), (8, 136), (10, 42), (10, 74), (10, 138), (12, 44), (12, 76), (12, 140), (14, 46), (14, 78), (14, 142), (32, 34), (32, 36), (32, 160), (40, 42), (40, 44), (40, 104), (40, 168), (64, 68), (64, 72), (66, 70), (66, 74), (66, 98), (66, 194), (96, 98), (96, 100), (96, 104), (96, 224), (128, 130), (128, 136), (128, 160), (132, 134), (132, 140), (132, 164), (132, 196), (192, 194), (192, 196), (192, 200), (192, 224)]
def r1sG : List Nat := [2, 2, 4, 4, 6, 6, 6, 8, 8, 10, 10, 10, 12, 12, 12, 14, 14, 14, 32, 32, 32, 40, 40, 40, 40, 64, 64, 66, 66, 66, 66, 96, 96, 96, 96, 128, 128, 128, 132, 132, 132, 132, 192, 192, 192, 192]
def r2sG : List Nat := [34, 130, 36, 68, 38, 70, 134, 72, 136, 42, 74, 138, 44, 76, 140, 46, 78, 142, 34, 36, 160, 42, 44, 104, 168, 68, 72, 70, 74, 98, 194, 98, 100, 104, 224, 130, 136, 160, 134, 140, 164, 196, 194, 196, 200, 224]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_238.map (· &&& dom_238)
def goalM : Nat := goal_238 &&& dom_238
def NN : Nat → Nat
  | 4 => 3
  | 5 => 8
  | 6 => 18
  | 7 => 5
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xffa25987cd0307bb687775cb
  | 5, 0 => 0xffe54020f2674c91bed55c57accf1baaa90ca1c97b0c33ac41b409100a6694d4
  | 6, 0 => 0xff981cbde8f20aa4d9da294acae38874b7a0def099048e0a8a5be36482c3ecd97c00021f69793c3e68eae288683fa49957142c1741f6efa941b4091032d473150650cbc800b07b8d
  | 7, 0 => 0x8ba63d2f4f957c914c9fd74241f6efa90edce612
  | 8, 0 => 0xe70be0
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5555000055550000555500005555000000000000000000000000000000000000111100001111000011110000111100001111000000000000111100000000000000000000555500000000000055550000555500000000000055550000000000005555000055550000555500005555000055550000000000005555000000000000550000005500000055000000550000005500000055000000550000005500000050500000505000005050000050500000505000005050000050500000505000000000000011110000000000001111000011110000000000001111000000000000555500005555000000000000000000005555000055550000000000000000
  | 0, 1 => 0x5050000050500000555500005555000050500000505000005050000050500000555500004444000055550000444400004444000044440000444400004444000011110000111100001111000011110000111100001111000011110000000000005555000000000000555500000000000000000000000000000000000000000000050500000505000000000000000000000505000005050000050500000000000055550000000000005555000000000000555500000000000055550000000000004444000044440000444400004444000044440000444400004444000044440000005500000055000000550000005500000055000000550000005500000000
  | 0, 2 => 0x555500005555000000000000000000005555000000000000555500005500000055550000550000005500000055000000550000005500000055550000555500005555000000000000555500005555000000000000000000005555000055550000555500000000000055550000555500005555000000000000050500000505000005050000000000000505000005050000050500000000000000000000000000000000000000000000555500005555000055550000000000005555000055550000555500005555000000000000000000005555000000000000555500005555000000000000555500005555000055550000000000000000
  | 0, 3 => 0x555500000000000000000000000000005555000000000000000000000000000000000000000000005555000000000000555500000000000000000000555500000000000055550000000000000000000000000000000000005555000055550000555500005555000055550000555500000000000000000000555500005555000055550000555500005555000055550000555500000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x14623014a31040a4188205
  | 5, 0, 0 => 0x21462481804189c050146248154313407620c460319434ac07650c4601d9424a0076
  | 6, 0, 0 => 0x28624d4ed850c4901dd57189203b814313807602ac2480ec450c4601dc0a1a6603b28624d4077a2869980ee020c49031a4a189203b914312407702862300eca88c4901dd43126003b81437a4076
  | 6, 0, 1 => 0x1b18920d35143127277
  | 7, 0, 0 => 0x28624e407756c62480eeae0c4901dc8a189203ba862480ec7
  | 8, 0, 0 => 0x143124076
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 29
  | 5 => 34
  | 6 => 39
  | 7 => 39
  | 8 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffe000000003fff81fc0000fffe07f00003fff81fc00000000078ffe003c00003f07cfffe07f00003c07fe000000
  | 0, 1 => 0xfe0000fc1f000078038e73fffe1ff0000000000000000f01ffff0000000781fc00000001e00e39cfffffe1c0000
  | 0, 2 => 0xfe007f0000000001e3ff80f01ff8000003c07fffc0000f01ffff00000007fffc0000ffe007f00003ffffe000000
  | 0, 3 => 0x1fc0000001e07f00003ff800000000fffff8000003ffffffc0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfff10449250bbb701d851047b6f83bb6d5ffffe1fedb574248578ffe00bc10a4bf07c6a4c03214413e07fe8124a8
  | 0, 1 => 0x2fe42d6fe5fa56cf9378e73eedc1f61c63212401100000d01bd2901a06127a1fc92151123e09e39cef6dea1c007f
  | 0, 2 => 0x7e005fb6d5f1b615f3ff80fc9ffe4492a3f27fffdb6bdd09bd6d01a04003beedb6bdfff105fb6d5fedffe836dea
  | 0, 3 => 0x120017c9215000e83b24855ed840024942fffffe4db7abfffffffffff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 46 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 46 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 29 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 29 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 29 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 29 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 5 => 19
  | 6 => 68
  | 7 => 30
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0xd9da294ad64847accccb368980ccfbdb72245135683fa4996485c44d5b561abf594d4f714b7362074597b5594132c2032eb17e8c2721baca0d83cd0803d6f2cf030b901c00e70be0005d26c3
  | 6, 0 => 0xe0a348c7e02994e7d8051cbed7d00a9bd64847acd16fca13cf25a779c3fd0ed5c1cf0d27b05da3d7af586cecabef1a98a9eba4b7a9a8d195a6fa683ca3e9e5b09f5d6bec9e92bae29be3bfad9bb2f7639851bd9690857b5a8ba63d2f83118fcb82b19e6881af6796809ab37d7d93458378b61842780587e076381bc76eaf45c26897ee77667e1f9d650313895c3b63035a24b75e54a8d86b4f957c914c9fd74248de60074629760042ed0ecd422f72083ef77fe03e4341383491ed4a2ca115cc2c4049d32b520a572997543f25c5891e16bc7659163e6fcc0fde3df80fbe58f80edce61208d6362408c40a5e05fbe4930514879c03d6f2cf011964ae00e70be0
  | 6, 1 => 0xf25626fded2ef5c4e856782be7d0037c
  | 7, 0 => 0xfe8d7f36fa267a2dc1a12213ba608fe5aff1d364ad1e0b1da64bcbe08f57195c882f851e76381bc77038a03d69213935652eada162f729dc5a24b75e531ae4665266d01940f91fb12124407a20390a441ce44cf51c45fa3d14c0f90e13a44e450c17704706b570520424b6c504152a9d00e70be00070add9
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x1000101010104020102010101000102010001
  | 6, 0 => 0x100000100030502000001050000030201010102030205030103030302020000050203010501040303040103050203000303000302030201040301030103030500020500
  | 7, 0 => 0x2050500020005030205020003050002000000050500050005020000
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 3
  | 5 => 7
  | 6 => 53
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xe2a3718da69edf1194369823
  | 5, 0 => 0xed8ecef86122c04454878e7d45136ad93da0e065078a181605eb539b
  | 6, 0 => 0xff3548f8fb24cff6ebb0ac52e9494f72e90602bedcbe6849b447ef29b210c5d7a966b5f9a63fbc68a0d922109ac5d69796a937fa942c10718e96241e8abc3f218a9255ba75ad98436e7ac6ea5e7e71f85e61443758d3c4b458cd235f577247a25649be56534e966c4f9fdac3463732813edec24f3cdb8b773bf14bd931ccd5a93123e8582b683e4e26546fdc263e092a1eecef881c4cd3c81b0d59d117582b751543141011cd44f911a3ec2f10d9c5450ec46ca00e1cc5b20de41ff60c2dc699079f5e6406e4838904e3d52004acbac6033b385d
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x2409120056c90244c015b24091300
  | 5, 0 => 0x240912000008d34480800240912000009024480000240912000000024840c0042109202
  | 6, 0 => 0x32441400000d11050000032440000000c91020000042840000000911000000034840800000ca1050000024440000000921020000034440000000d21020000024841400000c91050000034441400000c910200000328408000009210500000244400000010a1020000024041400001091020000042840800000d11000000034441400000ca10200000244414000010a1050000024041400000ca100000004284000000109102
  | 6, 1 => 0xd11020000024040000000901000000032840800000911000000034440800000911000000024441400000ca1050000024840000000ca1000000032441400000c91050000024040000000d11020000032840800000c91000000024840000001081020000032840800000d1105
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_236 roots_236 7 s ws hint
  | 1 => checkCutEntry true dom_206 roots_206 5 s ws hint
  | 2 => checkCutEntry true dom_230 roots_230 7 s ws hint
  | 3 => checkCutEntry true dom_174 roots_174 6 s ws hint
  | 4 => checkCutEntry true dom_110 roots_110 5 s ws hint
  | 5 => checkCutEntry true dom_234 roots_234 7 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_238 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_236 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_206 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_230 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_174 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_110 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_234 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_238 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_238 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_238 == dom_238) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_238 goalM v ys) : RunD true dom_238 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_238 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 18 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 18 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 5 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
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
  scr true dom_238 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_238 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_238 roots_238 goal_238 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_238 goal_238 := by
    have h0 : isConstB dom_238 goal_238 = false := by decide +kernel
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

end S_238

theorem lowS_238 : Lower true dom_238 roots_238 goal_238 9 := S_238.noCircuit

def isoMvS_207 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_207 : Lower true dom_207 roots_207 goal_207 6 :=
  lower_iso isoMvS_207 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_111

def isoMvS_235 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_235 : Lower true dom_235 roots_235 goal_235 9 :=
  lower_iso isoMvS_235 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_231

namespace S_239
def pairsG : List (Nat × Nat) := [(1, 33), (1, 65), (1, 129), (2, 34), (2, 130), (3, 35), (3, 67), (3, 131), (4, 36), (4, 68), (5, 37), (5, 69), (5, 133), (6, 38), (6, 70), (6, 134), (7, 39), (7, 71), (7, 135), (8, 72), (8, 136), (9, 41), (9, 73), (9, 137), (10, 42), (10, 74), (10, 138), (11, 43), (11, 75), (11, 139), (12, 44), (12, 76), (12, 140), (13, 45), (13, 77), (13, 141), (14, 46), (14, 78), (14, 142), (15, 47), (15, 79), (15, 143), (32, 33), (32, 34), (32, 36), (32, 160), (40, 41), (40, 42), (40, 44), (40, 104), (40, 168), (64, 65), (64, 68), (64, 72), (66, 67), (66, 70), (66, 74), (66, 98), (66, 194), (96, 97), (96, 98), (96, 100), (96, 104), (96, 224), (128, 129), (128, 130), (128, 136), (128, 160), (132, 133), (132, 134), (132, 140), (132, 164), (132, 196), (192, 193), (192, 194), (192, 196), (192, 200), (192, 224)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 8, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 12, 12, 12, 13, 13, 13, 14, 14, 14, 15, 15, 15, 32, 32, 32, 32, 40, 40, 40, 40, 40, 64, 64, 64, 66, 66, 66, 66, 66, 96, 96, 96, 96, 96, 128, 128, 128, 128, 132, 132, 132, 132, 132, 192, 192, 192, 192, 192]
def r2sG : List Nat := [33, 65, 129, 34, 130, 35, 67, 131, 36, 68, 37, 69, 133, 38, 70, 134, 39, 71, 135, 72, 136, 41, 73, 137, 42, 74, 138, 43, 75, 139, 44, 76, 140, 45, 77, 141, 46, 78, 142, 47, 79, 143, 33, 34, 36, 160, 41, 42, 44, 104, 168, 65, 68, 72, 67, 70, 74, 98, 194, 97, 98, 100, 104, 224, 129, 130, 136, 160, 133, 134, 140, 164, 196, 193, 194, 196, 200, 224]
def mpG : Nat := 0x3fffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_239.map (· &&& dom_239)
def goalM : Nat := goal_239 &&& dom_239
def NN : Nat → Nat
  | 4 => 5
  | 5 => 78
  | 6 => 188
  | 7 => 217
  | 8 => 81
  | 9 => 7
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x8e92d5f1821b3fa44915d6e426d7d38a0425b5c2
  | 5, 0 => 0xb8019cfba8f77bd4a82c9037a0c632a89bdb5b078e8bf82488378ae186987da78555b3fe854a34ec848b7ded80cf9cc38058d5a87dd271eb75ac9e17710632267005ba4f6ebf02226c09dce76b322a8d69c7adc4612737505e08ab9657ff8cbc5678461654099881534ec35d519e34814d6191b84a6c689c4827e03a46e5080d468a6fa146023f8a45805451431f72cd3dd05e843d852d203ce57b1a3c603bb73b49b14a36e8a0f32fd877292c8caf752a642dad286358ff27b91fb325bce90e226b066a1db123191c1fb92919594d0317b64ec4174ea434152941071118bbe90fe7929e0ac2ed7309489d3d075a2770070e99980703ffbb0688910d00151571
  | 5, 1 => 0xfb7aa7d5fb57fc5ff8e730ddec7086aee851e001e17744d8df5465e1d29e64aacf8c06aecdaa46e8cbb095bbc930a070c2292027c0200de0
  | 6, 0 => 0x3e67d44c3d8f8fa43d671aca3bf307253a00ba433933572337aaef2937198fdb36dcc73d35468b2834df3e8f34c186ad344ebf0d332eafb32e9d69132db2e1fd2d5c4bc42d281a432cd70c6129a6ec2628b6ef4628acc555289fe37a26f2a51326e63f8e23d3fe3223026c3722e07ba3220ac51721c2ef511ffcbd4c1e32c2c91e1df91c1d4133641d2e87611cbe33871cb56c471be114c81aa5c3b71a0e2e5618a0c841186d9532181b456e16d2790e154ab74c14eea44a1486f3651480c9371388fd1c122415ee10a0ff5c0fa302590e27f3c30dc0cbc90dbb48380d910f9a0b371ed90a46d5aa0697c8bd068e402e056e2df6041ab86a0376f77102a46fef
  | 6, 1 => 0x8f282f178ecdce1e8be01a59881f481286f60d5986cdde9286ca3a0782d2ad9b825be6808141014f81089a7e7a0716e577ce5ef6770f4e5175f5b0757325b7fd72f22140721673ed71fa7a206f93a70a6e92ed886e18f46e6e0dae256bfa853d6a594e0b6a54b4e06583cff1628cbe8860b250a8607c8af95f62ed1d5ed1079b5c139e5e5be6a00c5ba8fb375b58e8c658e852b75867af245464c04450df258d503d34934fd443494e060c9f4c9f773b4c92a0184c457bd54c0076374b7201e74a9316c64887c2e747c4e1f246b5fc8346405df44603f03544c6256e44be0e00437ad2cf4358e23b4354d3b8424776f341b6af9c3fd557613f32a6d23e6e29ec
  | 6, 2 => 0xfe0324ddfb9a6cfdfb11bf3df96c7040f77ad065f6876e7af40fe964f40e8ccdee88e0f9ebf1787fead7daa3e99b5adee8c39ce5e7709cbce6f5ca72e6b5c301e4676464e30d610cdf5465e1deee2b0cdeb663ccdce75758dbbfd068d9d17654d9d11873d6c1c20ad6b32785d1d6c508cfcb368bceb198afcd3ed258cac31ce4c7be13ffc4973e5cc37fb1dfc022b18bbc276665bb4769d0b8a4ccf5b5a428efb57384fab096de8aa605c962a5321da5a2061a44a139efc4a0ee598a9f47c4d59c09c1749bf8e9859bf464d19bdb5b079ba0822b98a360e197da84a797473469964150a5933a1cab919dd3529184997a
  | 7, 0 => 0x2ab09d182a8d49152a0a7bba29e75c6529db4f6f29aa27cd295812ee28e52195286e3eeb2669def825bd5bd224e0978124c58fb72422d7c223fd1fb623dedef623abf1db2330f79f230f070b2259f0392247450521c4facf21945d8b2189002f21670f9b20bfa1f41ffea51e1eb87d1f1d495f1a1d4133641b90a4881a73e4741993c7ba1971d726194e53c718e16c331836fab9182169f417f72da61614d6d215f2e63e14eea44a14899e7b12ba92e112432f4d11398f171101d84f101081770f5499e80de79e3d0d6e09400d6d42d60c4738e00bf6fe050b65aa410a2a071a09fad242090f2a2c0868131d086099f3068da53d04bd9dab00f2cc1300e025bc
  | 7, 1 => 0x70e065226eaa35aa6d2332a76b7405d16a8d3e4868adba6963e9def863c7240a63b2f110628d4497612944205e9ff28d5e3fc5aa5d5672245c683fbc5ad2695a5a630f825931b4a75867af2457dbbdfe578125cb55faa09b54fcac8a52a7f8a85205581551e3678150e64db04f1bfd5f4ec010834dde18b24cf259924c5d70b64c2918df4bcb206e4a00b21448de7fce47c4e1f2473304ed443fa602435136604063822f40438fde4003f58a3f8f15ce3f6807bd3e221a233e18344f3b37a6683a5989ab3a37991739bdbba439b4f6d339a2c3a938bcef973691687635807bfc352f88d6304c280b30208bbf2ebf99502dd4bee52d281a432ca19ad72c1ffb27
  | 7, 2 => 0xc729f82fc6105a53c4596a96c390cff4c022b18bbb75f538bac9f8dfba0c3e02b9cdfdc8b8a15017b7ff6a83b77b1d8fb4c4dafeb4243165b3204436b02bfed7ae59d46babbe3a7aab7392a4a81540eaa5ea55a4a5303182a3f831e6a3c3e65ba383828ea37776f0a36be74fa2919c82a056016a9fea816e9e21a5a99b9e66ba9731425f96b108c8968e9bb0967c9a0c95cb3d1e93dafd8e92dd3b8b921384af9167d1618f4d50b08b3369928aa4e8158a777b278a5468058a40e45489ad70ad874a933682246b69801bcb207fad356b7facc05a7cb393b67c667bea78f4917e78d2a0ea7744af3c772fc2f37320aca87318524872febc14721f1996717f6b28
  | 7, 3 => 0xfbadef83f4367158f1bee887ecf4dc3eea515b37e08ae47be005def5deee2b0cde116d59ddc4fdfedda3ae00dce832a0dc239cb0db3deb6eda2a8694d8c4d2e2d4de350ecfcb368bcfb49388ce3985d7cc4bc4ddcc36a112c98493bdc8e44687c7d144f6
  | 8, 0 => 0x9731425f9636ad618e8244e2874a933683a85c83830e1b8582d492fa80438d297ab7b4fe7a3fb51577e76b2f71fac3886cdc625669c6f6fd680e3c6b67b4ec0d65fc317b655cfaa76107365e608362fe5ef52b6e5dd6b1da5b07ca45554286315271464151a014ca4fe14f3a4c2918df48de7fce46505fa044b2b8a444511b3643f54c54415d1e5a3245c543321e9ed1306a611a2fd7cab02ca19ad72ad05a552aae69c12a9ddc2729db4f6f2933c04128e52195259a94ca23999b3d1c96cbd11b90a4881614d6d215f2e63e110d547a1101d84f0f5499e80bbeda990a9ab5b00a16e2500888aac0086099f307edb7b6061349d605c25f5801b05fc100d44241
  | 8, 1 => 0xfbdc7aebecf4dc3ee720f768dda3ae00c31557eebac9f8dfb38e5194b348976bb1cbec36ae59d46babecc5e2aaed1338aa44ce72a8cce399a3c3e65ba1ecb2be9ed0a515
  | 9, 0 => 0x9ed0a515830e1b85680e3c6b65fc317b3d6cb3d92ca19ad714783cbe
  | 10, 0 => 0x8a152192
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000ffff0000aaaa0000ffff0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ffff0000fafa0000ffff0000fafa0000fafa0000fafa0000fafa0000fafa00000000000011110000000000001111000011110000000000001111000000000000ffff0000ffff00000000000000000000ffff0000ffff0000000000000000
  | 0, 1 => 0xffff0000ffff00000000000000000000ffff000000000000ffff000000000000ffff00000000000000000000ffff00000000000000000000ffff0000cccc0000ffff0000cccc0000cccc0000cccc0000cccc0000cccc0000ffff00000000000000000000ffff000000000000ffff0000ffff000000000000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000ffff0000ffaa0000ffff0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa000033330000333300003333000033330000333300000000000033330000000000000000000000000000ffff0000ffff000000000000ffff0000ffff00000000
  | 0, 2 => 0xffff000000000000ffff000000000000ffff000000000000ffff0000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000000000000000000000000000ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff0000ffff00000000000000000000ffff000000000000000000000000000000000000ffff000000000000ffff0000ffff000000000000ffff0000000000000000000033330000000000003333000033330000000000003333000000000000ffff0000ffff0000ffff000000000000ffff0000ffff0000000000000000
  | 0, 3 => 0xffff000000000000ffff000000000000000000000000000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff000000000000ffff000000000000ffff000000000000ffff000000000000000000000000000011110000111100001111000011110000111100005555000011110000000000000000000000000000000000000000000000000000ffff0000000000000000000011110000111100001111000011110000111100001111000011110000000000000505000005050000050500000505000005050000050500000505000000000000ffff0000ffff0000ffff0000ffff00000000000000000000000000000000
  | 0, 4 => 0xffff0000aaaa0000ffff0000aaaa0000eeee0000aaaa0000eeee0000aaaa0000ffff0000f0f00000ffff0000f0f00000f0f00000f0f00000f0f00000f0f00000ffff000000000000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000000000000000ffff000000000000ffff0000000000000000000000000000ffff0000ff000000ffff0000ff000000ff000000ff000000ff000000ff0000005555000055550000000000005555000055550000555500005555000000000000ffff00000000000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff000000000000ffff0000000000000000
  | 0, 5 => 0x55550000000000005555000055550000000000005555000000000000f0f00000f0f00000f0f00000ffff0000f0f00000f0f00000f0f00000f0f0000000000000ffff00000000000000000000ffff0000ffff00000000000000000000005500000055000055550000005500000055000000550000555500000000000000000000ffff000000000000ffff0000ffff0000ffff0000ffff000000000000ffff0000cccc0000cccc0000cccc0000cccc0000ffff0000cccc0000cccc00000f0f00000f0f00000f0f0000000000000f0f00000f0f00000f0f00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff00000000
  | 0, 6 => 0xff000000ff000000ff000000ff000000ff000000ff00000000000000000000ffff0000cccc0000ffff0000ffff0000cccc000000000000ffff000000000000ffff0000f0f00000f0f00000ffff0000f0f00000f0f00000f0f00000f0f0000000550000005500000055000000550000005500000055000000550000000000003333000033330000333300003333000033330000333300003333000000000000ffff0000ffff0000ffff0000aaaa0000ffff0000ffff0000aaaa0000aaaa0000000000000000000000000000ffff00000000000000000000ffff000000000000ffff000000000000000000000000000000000000ffff0000000000000000
  | 0, 7 => 0x55550000000000000000000055550000555500000000000000000000ffff0000eeee0000ffff0000eeee0000eeee0000eeee0000eeee0000eeee0000ffff0000bbbb0000ffff0000bbbb0000bbbb0000aaaa0000bbbb0000aaaa00000f0f00000f0f000000000000000000000f0f00000f0f00000f0f00000000000055550000555500005555000055550000555500005555000055550000000000000000000033330000000000003333000033330000333300003333000000000000333300003333000000000000333300003333000033330000333300000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000
  | 0, 8 => 0xf0f00000f0f00000f0f00000ffff00000f0f00000f0f00000f0f00000000000000000000555500000000000055550000555500005555000055550000000000000505000005050000050500005555000005050000050500000505000000000000cccc0000cccc0000cccc0000cccc0000cccc0000ffff0000cccc0000cccc0000000000000000000000000000ffff0000ffff0000ffff0000ffff000000000000ffff0000000000000000000000000000ffff0000000000000000000000000000ffff0000ffff000000000000ffff0000ffff0000ffff0000ffff00000000000000000000ffff00000000000000000000ffff000000000000000000000000
  | 0, 9 => 0xffff0000ffff000000ff000000000000ffff0000ffff00000000000000000000000000000000000000000000ffff000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000ffff000033330000ffff00000000000000ff000000ff00000000000000ff000000ff000000ff000000ff000000000000ffff0000cccc0000ffff0000cccc0000cccc0000ffff0000cccc0000cccc0000cccc0000cccc00003333000033330000cccc0000ffff00003333000000000000ffff0000ffff000000000000000000000000000000000000ffff00000000000000000000ffff000000000000ffff000000000000ffff0000000000000000
  | 0, 10 => 0xffff0000cccc0000ffff0000cccc00000000000000000000000000000000000000000000000000000000000000000000ffff000000000000ffff00000000000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff0000ffff000000000000ffff0000ffff000000000000f0f00000f0f00000f0ff0000f0ff0000f0f00000f0f00000f0f00000f0f0
  | 0, 11 => 0x333300003333000000000000000000003333000000000000000000000000000000ff000000ff0000003300000033000000ff000000ff0000003300000000000000ff000000ff0000ffff000000ff000000ff000000ff0000ffff0000000000005555000055550000111100001111000055550000555500001111000000000000555500000055000055550000005500005555000000550000555500000000000000ff000000ff000000ff000000ff0000000f0000000f0000000f000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff0000ffff00000000
  | 0, 12 => 0xff000000ff000000ff000000ff000000ff000000ff0000ffff000000000000ffff000000000000ffff0000ffff0000ffff000000000000ffff00000000000000000000ffff000000000000ffff000000000000ffff0000ffff0000000000000000000000000000ffff0000000000000000000000000000ffff000000000000ff00000000000000ff00000000000000ff00000000000000ffff0000000000000000000000ff00000000000000ff00000000000000ff00000000000000000000ff000000ff000000ffff0000ff000000ff000000ff000000ffff0000ff000000ffff0000ffff00003333000033330000ffff0000ffff0000333300000000
  | 0, 13 => 0xffff0000ffff0000000000000000000000000000000000000000000000000000ffff0000ffff0000ffff0000cccc0000ffff0000ffff0000cccc0000cccc0000000000000f0f00000f0f000000000000000000000f0f00000f0f000000000000ffff00000000000000000000ffff00000000000000000000000000000000000000000000ffff0000ffff0000ffff000000000000ffff0000ffff0000000000000000000000000000333300003333000000000000000000003333000000000000cccc0000cccc00000000000000000000cccc0000ffff00000000000000000000ffff0000ffff0000ffff0000ffff00000000000000000000ffff00000000
  | 0, 14 => 0xf0f00000f0f00000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0000000000000000000000000000000000000ffff0000ffff00000000000000000000ffff0000ffff0000ffff0000ffff000033330000333300000000000000000000ffff0000000000000000000000000000ffff0000ffff00000000000000000000000000000000000000000000000000000000000000000000ffff00000000000000000000ffff0000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000ffff0000ffff000000000000ffff0000ffff0000ffff0000000000000000000000000000000000000000
  | 0, 15 => 0xf0f000000000000000000000f0f00000f0f00000f0f000000000000ffff0000000000000000000000000000ffff000000000000ffff0000000000003333000000330000333300000033000033330000003300003333000000000000000000000000000000000000000000003333000000000000333300000000000000000000333300000000000033330000000000000000000000000000000000000000000033330000000000000000000033330000333300000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000ffff0000ff000000ffff0000f0f00000ffff0000ffff0000f0f00000f0f00000f0f00000f0f0
  | 1, 0 => 0xff000000ff00000000000000ff000000ff000000ff00000000000000000000ffff000000000000ffff0000000000000000000000000000ffff000000000000ffff000000ff0000ffff000000ff0000ffff000000ff0000ffff00000000000000ff00000000000000ff00000000000000ff000000000000000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000f0000000f000003333000033330000333300003333000033330000ffff00003333000000000000ffff00000000000000000000ffff0000ffff000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000
  | 1, 1 => 0xffff0000f0f00000ffff0000ffff0000ffff0000f0f00000ffff0000f0f00000ffff0000ffff0000ffff0000ffff000000000000ffff00000000000000000000ffff0000ffff0000ffff00000000000000000000ffff0000000000000000000000ff000000ff00000000000000ff000000000000000000000000000000000000ffff0000ffff000000000000ffff0000ffff00000000000000000000000000000000000000000000ffff0000ffff0000ffff000000000000ffff0000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000ff0000000000000000000000ff000000ff0000000000000000
  | 1, 2 => 0xf0f00000000000000000000000000000f0f000000000000f0f00000f0f00000ffff0000f0f00000f0f00000f0f00000f0f00000f0f00000ffff0000ffff000000000000ffff000000000000000000000000000000000000aaaa0000aaaa0000ffff0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000000000000000000000ff000000ff000000000000000000000000000000000000ffff0000ffff0000ffff0000ff000000ffff0000ffff0000ff000000ff000000cccc0000cccc0000ffff0000cccc0000cccc0000cccc0000cccc0000cccc0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f00000f0f0
  | 1, 3 => 0xffff0000ffff0000ffff000000000000ffff000000000000ffff0000000000000000000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000ff000000ffff0000ff000000ff000000ff000000ffff0000ff000000ffff000000000000ffff0000ffff0000ffff000000000000000000000000000000000000ffff00000000000000000000ffff0000ffff0000ffff000000000000ffff000000000000ffff000000000000ffff0000ffff0000ffff000000000000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000000000000000ffff0000ffff000000000000ffff0000ffff0000ffff0000000000000000
  | 1, 4 => 0xffff0000000000000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x803070d0b50c0307060b5040a02090050803070605504030201005
  | 5, 0, 0 => 0x250307060b24612030705110060423070b110061203070622006210307060b206080307060b1f61e0307060b1d61703071c001860f03070d0b1b60403070501006040302050900617031a19001861703060b1615614030706051361203070b111060f0307060b0e6
  | 5, 0, 1 => 0x2803070b331860403020632006310307060b3061203060b16006040a07062f00628032e060b186040307051100604030705092d61707062c001862b0307060b1361203072a0b0061203060b290062803070b0918604030727090061203260b090060403070b11106
  | 5, 0, 2 => 0x4030605290061403070d0b1361707060b3815604032605090061203060b3c006280307063b1860403070b3a0061203070b390061203070b112d60403260b0910604070d0b3800604070d0b003763603070d0b0060423260b09006280335060b1861706193400186
  | 5, 0, 3 => 0x1203070b330061203070b091060f030706051b604030706460061203070b090061703064500186120307440b0060403060516006430307060b4261203260b11006410307060b4060403073e003f6000403023e0050403070d3b0060403070b112d60403073d05006
  | 5, 0, 4 => 0x4030705330064d03070d0b0061203070b092d604030705091061207060b4c0060403074b0b0060403070509006120307063b0061703070b4a186490307060b48604030744050061703060b4700600040a02060051203070509006
  | 6, 0, 0 => 0x42307060b5900758120307060b0070403070b09005775603060b3c005571203070b11001f70403070d0b0054753280307060b187520307063b421870403070605002d751280307060b1872b040307060b007040307063b001f71750060b00371870403070509001871707060b4f37187280307060b184e7
  | 6, 0, 1 => 0x1703070b09101871707060b3800187000403070d0b2d6170307095c0018700170a073e001861707065b0037187041703260b090070f0307060b48187000403070b1100600122307060b00600170a02060018617060b295a001875203060b291d18700120307060b00604120307060b2d71723070b0900187
  | 6, 0, 2 => 0x403070b11001f71703070b33001870403070b092d1f71203070b110055700612807060b1861707060b103718717030b0929001876117060b29001871703070b605f18717070b095e001870403070d0b10007040326060b1000700120307060b10614280307060b187175d07060b001871203070b1100187
  | 6, 0, 3 => 0x41203070b09007120307060b001370403070b1100187176707060b00187170307060b151d7001203070605006616607060b00187650307060b001876403070b095418717030705090018717060b2938001876307060b006218704030706055900717060b290037187120f0307060b00717030d0b2900187
  | 6, 0, 4 => 0x280307060b186c7526b0307060b187170307063b001871703070b6a691871707060b591537704280307060b18717030b33290018700042307060b106041203070d0b00704120326060b007120307060b001b728680307060b1875603070b090055717070605003718717030b091600187140403070d0b007
  | 6, 0, 5 => 0x1707060b38596f70004230706050060403260b09001f717030b33160018752720307060b18700040307060500628710307060b18752120307060b007140307060b427071703070b09596f70403076e0d0b0070403070632050075203060b296d1875607060b0037557000403260d0b00617060b163800187
  | 6, 0, 6 => 0x403070d0b002d7040f0307060500700120307060b2d6171203070b090071703070b110018766170377060b7671703070b092d1871703070b33596f7001707060b153761703070d0b00757000403070605106120307060b00547120307060b007470403060b29001f71703063b2900187730307060b486f7
  | 6, 0, 7 => 0x5207060b1d37187172803060b2918741120307060b0070403070d0b007a7000403073e050060403070605001b7791707060b596f70403070605003f70004030206050061703063b19001870403070605001371703070b1100557120307060b100070403060b16001f71703063b160018704170378060b007
  | 6, 0, 8 => 0x12310307060b007177e0307060b157001203070d0b0065603070b11005570403070d0b59007041203070b11007170302063200187001203070b09006530307060b004870f0307060b1b1f71703073b1a0018717070b7d00371876117070b090018714120307060b0070403070b7c007b7120307060b00307
  | 6, 0, 9 => 0x403070b09001f71703073b0900187000403070d0b106520307060b81187120307060b002d704120307060b10700042326060b006000403070d0b006040307440b001f7040307060510007280307060b188071703060b7f001870004030706052d61203070b09001f70403070605005471723060b2900187
  | 6, 0, 10 => 0x403070d0b00137611777060b001871777060b8300187120307060b00407000403070d050065207060b38421870004030705090061703060b3c00187040307060b000e70403070b09101f7041203070605007040f03070d0b0071703070b82001871703073e003f18714040307060500717560307060b157
  | 6, 0, 11 => 0x4030706052f0070403070d0b1100717080307060b187001203070b11006140307060b131f70403070b09110070403070509001f7040307060b102d70403070d0b001b70403070b33001f71703073b33001878507060b0084187
  | 7, 0, 0 => 0x611707060b001870012560307060b00758170307060b5918817120307060b0018866170307060b59188531703060b29001880017030706052d18752170307060b59708175603070b09001881703070b335900188560307060b005455814170307060b00188560307060b007455804170377060b0018804860307060b001881703060b2900184e8
  | 7, 0, 1 => 0x1723070d0b0018700172326060b00187172307060b008818817120307060b00558520307060b59481881707060b008718558172307060b0076188001703070d0b0018700170326060b001870000120307060b006175607060b0037188176403070b0900188521703060b297618817030706051000188001703070b09001870403070b090018558
  | 7, 0, 2 => 0x170307063b5900188001703070d0b1018700170326060b10187170307060b008b1888a170307060b001881707060b003762188170307060b1076188001703070d0b0055700170326060b0055717680307060b54188141703060b290018800170a07060500187176407060b0037188001707060b3800187001707060b003718704170307060b76898
  | 7, 0, 3 => 0x170f03070b0900188177e0377060b00188170307060b591d6f8170f0307060b59188170307060b004818800120307060b001f704170307060b008e817680307060b00188170307060b008d1881703070b0900187b81703070b0900181f8611707060b00188c8040307060b59001f80017032e060b00187170307060b5900708791707060b5900188
  | 7, 0, 4 => 0x1703070d05001870017032606050018704170307060b1018800120307060b001871703070b09001318817030706050076188141703060b1600188851707060b003718800616407060b541871707060b0037181f804172307060b0018853170307060b004e8041703070b097c008001703070b330018704170307060b0018800041703070605007
  | 7, 0, 5 => 0x52170307060b591881707060b003718558170307060b102d18800040307060b001f700170307063b0018714170307060b596f8041703060b290018817039077060b00188172307060b002d188177e0307060b768988f170377060b00188611707060b00185581703070b09001b18812560307060b00558170377060b5900188521703060b2942188
  | 7, 0, 6 => 0x1707060b59376f7521707060b380018800000403070605006640307060b0048188521707060b003718800040307060b101f717922307060b0018800170307910b00187521703070d0b0018852170326060b0018804170307060500188560307060b004818868640307060b541881453170307060b008521703070b090018800042307060b001f7
  | 7, 0, 7 => 0x17560307060b7689817730307060b596f8000403070605001f704170307060b596f81707060b593718938170307060b59486f817640377060b00188521703060b29591881703070d0b0054188040f0307060b001f81703070605002d1881703070b09005418866170377060b0018804560307060b0055800042307060b00187041703060b1600188
  | 7, 0, 8 => 0x58170307060b00188170307060b5900958520307060b42185581707060b593718898001703070694001871707060b001d37188170f0307060b1b1881703070d0b1000188170326060b1000188040307060b001b1f80017280307060b187001703070d0b2d187170307060b591018800170326060b2d1875304170307060b008040307060b00131f8
  | 7, 0, 9 => 0x170307060b10187560307060b590055852170307060b99188040307060b00541f8140307060b001d18800041703070d0b0071707060b003784188520307060b00481881703070b600900188141703070b09001880417120307060b008170307060b98541881703060b29970018800170396060b001871703070605590018804170307060b2d188
  | 7, 0, 10 => 0x170307060500187040307060b10001f8141703070b33001889a560307060b0018800040307060b2d1f70028640307060b1871703076e0d0b00188170f0307060b00188041703070b09001f80000280307060b186176403060b290018817030706320500188170326060b007618804170307440b0018852170377060b00188170f0307060b54188
  | 7, 0, 11 => 0x14040307060b001f814170307063b001881703070b0900421881703070b09006918800000403070d0b0060017030706051018700560307060b00557040307060b001d18800170307060500557041703070d0b0018858560307060b005580004120307060b00700170307060b5915766640307060b001885217280307060b1889b170307060b00188
  | 7, 0, 12 => 0x170307060b599c188521703060b2900188001703073e0500187581703060b3c0018814170307060b131881703070b09005f1881703070605003f188000403070d0b001f7000403070b09001f7041703070b330018800170307060b5970714170f0307060b18804120307060b001f852172307060b001881703070d0b002d1881703070b096a00188
  | 7, 0, 13 => 0x40307060b002d1f8521703060b1600188176307060b0037188170307060b100018804170307063b00188009d1707060b0018717680307060b59008001703060b3c001871703070d0b007a188
  | 8, 0, 0 => 0x1707060b003718700001703070d0b001870000170326060b001870061176407060b0018800001703070b09001870000611707060b0018717730307060b590018904170307060b001889904170307060b00186f904170307060b59001890014170307060b00188170307060b005418559170307060b007418559170307060b590048189170307060b1000181f9000417560307060b008
  | 8, 0, 1 => 0x170307060b59001889904170307060b00181f900179e0307060b001880017860307060b00188177e0307060b00188990017730307060b001880004170307060b00188001703070d0b00181f800170326060b00181f81768640307060b0018900170307060b0048188170307060b0076181f90017680307060b001880417560307060b001890052170307060b421880004170307060b001f8
  | 8, 0, 2 => 0x170307060b5900188009f170307060b0018817560307060b001889917560307060b00186f917560307060b590018900170307060b595418804170307060b001b18904170307060b001318900177e0307060b00188170307060b002d181f90000520307060b421870052170307060b591880000040307060b001f704170f0307060b00189170307060b0076185591452170307060b00189
  | 8, 0, 3 => 0x170307060b10187170307060b5900185590017560307060b005580058170307060b001880017640307060b541880017560307060b00188009a170307060b001885817560307060b00189170307060b5900181f904170307060b00541890000170307060b76897005217640307060b18800170307060b001870817640307060b001889900170307060b001889817640307060b5900189
  | 8, 0, 4 => 0x170307060b10001880000170307060b2d18700521703060b290018800170307060500181f80000560307060b0055700041703070b090018817560307060b001855900170307060b0018a08000017030706050018700170307060b10181f81404170307060b0018900170307060b001f55852170307060b001870900170f0307060b0018852170307060b590018900170307060b00181f8
  | 8, 0, 5 => 0x170307060b2d181f8
  | 9, 0, 0 => 0x170307060b00181f817560307060b00188170307060b0018898170307060b5900188170307060b004218804170307060b00188170307060b0076188
  | 10, 0, 0 => 0x170307060b00187
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 44
  | 5 => 52
  | 6 => 60
  | 7 => 68
  | 8 => 76
  | 9 => 68
  | 10 => 60
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x7c000000fff001ffc0000007c003f03f07e0f8000000000e38e39c739fffff807fc00000000000000001f0fffffe000001f0000003fff8e7ffe7ffffe01ff00000000003e00fff8000000000000
  | 0, 1 => 0x7fc001ff0000000000000007f800000000000000001f000fc0fc1f83e01ff07fffc0000000000000000000e38e39c739c0000007c3ffffff1ce7ffffe01ff000000000001ff07fffc0000000000
  | 0, 2 => 0x3e01ff00000000003e0ffffffc000000000007ffffe0000000000003ffffffffc0000000000f803e000000000000003ffff807fc0000000000ffffe01ff00000000003e00fff8000000000000
  | 0, 3 => 0x1fffffffc00000000000003e000000000000003ffffffffc000000000000001fe0000000000003ffff83ffc0000000000f83ffffff00000000003fff0000000000000000
  | 0, 4 => 0xe38e39c739c1f0000003ffc007ff0007fffffff00000000000000f8000000000000000000001f0fffffe00003ffffffffc00000000000000001ff000000000001ff07f8000000000000
  | 0, 5 => 0xffffe01ff000000000001ff000003ffc007ff00f803ffe0000000000003ffffffffc0000000000fffffffff0000000000000007f803f03f07e0f8f803fffff00000000003e0007fffc0000000000
  | 0, 6 => 0xffffffe00000000000001ff0007fc000000000007fc00000fff001ffc03ffffff83c0000000000ffffe0fff00000000003e00fff8038e38e71ce707fc001ff0000000000000007f8000000000000
  | 0, 7 => 0xf803ffe000000000000000007c003fe3fe7fcffffffe01ffe38e39c739fe00fffffc0000000000fffffffff00000000003ffff83ffc0000000000ffffe0fff00000000003ffffff83c0000000000
  | 0, 8 => 0x7fffffff00000000003ffffffffc0000000000fffffffff0000000000000007f803f03f07e0f807fffffff00000000000000f800000000000000fffffffff00000000003e00f800000000000000
  | 0, 9 => 0xf803ffe00000000000001ff0000000000000000ffffe0fff00000000003ffffff83c000000000000001fe00fc0fc1f83e01ff07fffc0000000000f800001ff00000000003fff07f8000000000000
  | 0, 10 => 0xf807fc0000000000fffc0000000000000003e0007f80000000000000003fffff00000000003e00fffffc0000000000fffc1ffff000000000001ff000003ffc007ff00
  | 0, 11 => 0xf803e000000000000003ffffff83c0000000000fffffffff00000000003ffffffffc0000000000fffffffff00000000003ffffff83c0000000000ffffffe0000000000003e00fffffc0000000000
  | 0, 12 => 0xfffffffff000000000001fff807fc0000000000fffc1ffff000000000000000007fc00000000000000001ff00000000003fff07f80000000000000000001fffffffe00003ffffffffc0000000000
  | 0, 13 => 0xf8000000000000000003e00fff803f03f07e0f8f8001ffff000000000001ff0000000000000000fffc1ffff000000000001ff0007fc000000000000001fe0000000000003fff0007fc0000000000
  | 0, 14 => 0x7fc00000fff001ffc00000fff8000000000000ffffe0e0000000000000000fff80000000000000000001ff00000000003e0007fffc000000000000001ffff00000000003e000000000000000000
  | 0, 15 => 0xf803fffff00000000000000f807fc0000000000ffffe0fff00000000000000f807fc0000000000fffc0000000000000003e00f8380000000000000000001fffffffe000001ff000003ffc007ff00
  | 1, 0 => 0xffffffe00000000000000000007fc0000000000fffffffff00000000000000f800000000000000ffffffe00000001ffc03ffffffffc000000000007ffe000000000000003e000000000000000000
  | 1, 1 => 0x7ffe01fffff001ffc03fff07f8000000000000f8001fe0000000000003fff0000000000000000ffffe0000000000000001fff807fc000000000007fc0000000000000003e00fff8000000000000
  | 1, 2 => 0x1ff000000000001f0000003ffc007ff00fffc00000000000000000000000038e38e71ce707fc0000000000000003e00ffffc3fffff8000000001f000fc0fc1f83e3ffffff803ffc007ff00
  | 1, 3 => 0xf803e01ff00000000000000f807fc00000000000000001fffffffe000001fff800000000000000f803fffff00000000000000fffffc0000000000ffffe000000000000003ffffff8000000000000
  | 1, 4 => 0x0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x27c082444fff001ffc0042217c08bf03f07e0f88a6621319e38e39c739fffffe07fedb6db5b5bd4111049f0fffffe00002bf9a8dd77fff8e7ffe76511800c400500400403f00fffa0124924a4a42
  | 0, 1 => 0x3fc0017fb6db6d6d6f608881fc2124924a4a4292aa5f12afc0fc1f83e207781f9dfffffffffff084421211e38e39c739f2ddc96fe7ffffff1ce7ef77a01dd02d02c054140ff01fdffffffffffff
  | 0, 2 => 0x8223e81ff249248494a760fdf6eec003ff800ff03fdeff88db6db7b6b5bffffffffffffffffffffc03f808000000000001f777e03dedb6db5b5bd6d55a00d502d02c05417f88fffe2124924a4a42
  | 0, 3 => 0x822200108000000000000ff7bffffffffffffff8223e8188000000000039cce1b73021c2184300000007e004924929290b9cce0373001c0180300d03b5c9aa0001c600063fff8404224924949094
  | 0, 4 => 0x8a666933be78e79cf3be9f8a09533ffc007ff0083ffeffffffffffffffc0887a06200000000000c333049f8fffffe00003d66f7b39871c718e318800200077249248494a407701f8036db6dedad6
  | 0, 5 => 0x7599d80e6145144284609f7209113ffe497ff947c01ffe804924929290adaab695b8104100e3187dddffef7ffffffffffe42297f88bf4bf4feafad8237dbbb0006da001adf8805fdfdb6db6b6f6b
  | 0, 6 => 0xbeeefb608000001b6b5a4ff9605fedb6db5b5bda7de82444fff925ffe52daab69038000000e318ef77a0fdd03f03e07c1ff99fffe67aebaef5ee701dc00077b6db6d6d6f600081f80124924a4a42
  | 0, 7 => 0x7401dec80082082108026bb9fcceffe3fe7fcffef77a13dde3de3dc779f600df6acc001b68006bf7bbdedee1c71c638c61b55683b540fc0f81f07ed57a0ed503f03e07c1efbbbed83c000007ffff
  | 0, 8 => 0x27dd6dab3924fff243fdd6677b39871c718e318d1bb5c9aa1041c62006042217f88bf4bf4feafa01ddefef7ffffffffffe000fa02000000000000fddfffef7ffffffffffdf007e02000000000000
  | 0, 9 => 0xfe23ffe88492492929080770000024924949094fffff8fffb7fb7f6fefef33bed81c000007ffff92aa5ff2afd2fd3fabe84dd17fd752fd2fa5f47fc0210077249248494a5f7705f8036db6dedad6
  | 0, 10 => 0x92aa10108900901202400007a03dc92492125297ddc1000092492524251f0005f80124924a4a420001efef76db6dadbdaff88fffffdb6db6b6f6bfffe17f7fffffffffffc9fb209133ffc007ff94
  | 0, 11 => 0xec03a008000000000002f99bed8340000025f47beeefb77f249249fffffdccf7b73021c2184300b6abda5ee04104038c62fbb9e482c00000490fffffffff88db6db7b6b5bf00fffbddb6db6b6f6b
  | 0, 12 => 0xbeeefb67f249249ffffe0fffa07fedb6db5b5bd7ddc17e77ffffffffffc0880005fc92492125290001001f7249248494a4f3304d800000006dad64331049fffffffe494a7fddffff752fd2fa5f47
  | 0, 13 => 0xfc021000000000000003faafffeabf4bf4feafa582015b3b0006da001ae07780000249249490947ffc17f7fffffffffffc0dd0005740b40b0150510005fe004924929290bfff8405fedb6db5b5bd
  | 0, 14 => 0x27fc8254cfff925ffe500007bfa0124924a4a42ffffb0f8893693726a5a000fbfa0124924a4a42000000077249248494a5f0005f9ddb6db6b6f6b000007e776db6dadbdaff888404200000000000
  | 0, 15 => 0x58017dab30006da001ae000fa03dc9249212529ae67a07dd00900807c1c00068035402402005016d540000002402404011b00683a000480480a024111049f7fffffe494a69ffa09533ffe497ff94
  | 1, 0 => 0xbccefb600000001b6b5a0888005fc9249212529beeffb7ff249249ffffe088ba00200000000000beeefb60c000001fff5bbdde9ff752fd2fa5f4781dfe808092492524251f880404200000000000
  | 1, 1 => 0xa7ffea5fffffb6dffef7fff85fc236db6dedad6fe2217f084924929290af338400000000049094fddff8080924925242500ff7a07fedb6db5b5bd03fc0010892492524250f003ed8000000024a42
  | 1, 2 => 0x200013b000248000a49f8209533ffc007ff00fdde1000092492524250299084c678e38e71ce702ec0000800000124253fccffffe3fffffa4a4212a85f12afc0fc1f83e3fffffff33fff6dfffd6
  | 1, 3 => 0xfe23f81ff249248494a40887a07fc9249212529c333049fffffffe494a60fffa062249249490947c01ffef76db6dadbdae088fbfffdb6db6b6f6bfffff818892492524253f77fffa036db6dedad6
  | 1, 4 => 0x880004200000000000
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 78 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 78 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 161 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 161 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 161 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 161 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 4 => 2
  | 5 => 28
  | 6 => 168
  | 7 => 366
  | 8 => 104
  | 9 => 48
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0x967c64fd12365a99
  | 5, 0 => 0xf2ba8f34e401e32fbc434135b0ea44b5a7d19f67a37776f09a7b930395e16c2a94122e268f78074d8b89ae5986f60d59825be68067c1b55863278e7f54a41c84541121ab41f61a372c291138282995a42740f27525d22dae238f6ecb18d3924a14eea44a12d3d2050e5b9bc00745e7cb
  | 6, 0 => 0x3ed475aa3cfc86eb3ca56eee3c040df83bcdd52c3bc41e9a39f40876393c1bf4380ac41436c8a66436c6489a3660c9fd3559e19d34e8271031ea0ae431c81a50309ae7262f52d7a12ea520fc2e8330682d80fc5b2d2918b52ce5b9da2c1ffb272bd49dec2a6fa9d82a2ca67c26afc8c72507f11724e600832189002f21670f9b20fa82a21fb8c23a1eb87d1f1cd30da11b79400e190e8de5190dffcd18765a03180aa86e16d9d39e16a75edc160d816b159b080c131f2e361235667c0fe096400de79e3d0bbf416b092db6ed091846fb090bc659086732c007bd55a806dc69fc045c317003f8729403e7206f03c52fdb0228e09000ec4ee200d3ba9e009495b9
  | 6, 1 => 0x9737fde29731425f97176a0393dafd8e8a8206f58a152192892bd0fd86b5fda3821b367f80acf295801e79c87e94d6057e1ac0a27a3f5374789c7a5e78068fdf77e76b2f74260213741b9d49737a43d270c6c8c070a2238f706c650e702238fa6984608968c5f74c644dc107639575c06340e64160bbf9ba5f7847075f58b7d75f2f71655e6866685d380d125c683fbc5aae595c59a8eb245979918356cf09375614328355faa09b54e741cc5360402252f2351e52ab82ee5160a9174ff7ce0c4fe14f3a4deedaa64adf966448de7fce48acb47b484fb4fb48335810479b1a0c45cdb30845abc274444c16af43f92b0f41f4d9ea41ccd21a400971353f0727ea
  | 6, 2 => 0xfdc3c4aef922e7e7ea04536de7d97c2fe773b8cee720f768e32493fde1fa55dbe17bd3a0dce832a0d83b3562d4de350ed271a481d1374c29ce3985d7cc667d74cbfc01f1ca2f087dc8463691c6ea1e95bef19c82be46520dbac9f8dfb9cdfdc8b9741592b91bab7eb8e59cc5b832fa73b5a9dd0db4c4dafeb2f4490caa9641cba7161fd5a5ea55a4a0f71e5b9fab89239e1bcc649c7ea3db9c2c1e089bb190dc
  | 7, 0 => 0x19387f4f190e8de518da528f1850f753184b863517cd916417aba0d0178e5e02175b734e1710f1de160d816b1604b21415fe7cef15e8e50515c8658a14d2066b14783cbe14387754141ef898131f2e361300c5ee12e0923811e50b8711c0d28311bde515119f985111986fd211581a7a112eb4d5110d547a10dd99df1078beb0104fa1290f64b1cc0f0dd0c50eecc94c0eebe0310ed7c20c0d5b74550d57e7fb0d4507190ca6db800c52bd1d0c520a730b5b63b509ff13ce0970ca5508e7d4d9084d93db0821a6df0813f4b207f19ca50750a4480607fd0705de673005b3aa5f054dd63304d80dcf0448f401040f346901c9619701b5ae9d019487ee00d44241
  | 7, 1 => 0x3916b94438d982f637ec7b2237e2b7ba37ca8a8e370b648c364483b23622931e3603d98335c9137835c7c8de3547343834caab3134bf11a6344397e23415973f337400a23245c543321e9ed13210fcc630ab6d172fd7cab02e4f4b3d2e2d5aa92e00e8592dda6a132dab84302c4ac0252c130ed62bd599b02b7cdd7b2a87553a29f91f3029b2ec9e2971cb3828bf2eb627a7f68426d79aa726b4bc8226afc8c72696ac02267c0a0c2653c747252e7c5124101d6b23999b3d231178ab2238988e21ee273820c8f1ea20212dc42015bcb91ff0e86e1fe2e1241f6bea6a1eab266b1de19bde1dca90dd1ce143d41c96cbd11b1f4f691affe8b01a7c155019f6f1de
  | 7, 2 => 0x5759e4ff56dffcef56cf09375679858b5604b33c55b2b99e5584a456555cb2a853d60d2953ce7b1853a47165534aa7b852714641522b30e4519a09cc4fef17b14fe14f3a4fca03f84f5cccb74f150d2e4f0480b64ef31c9a4eb16c954e707a564c815ae94c00049e4ada24f04ab6b7e84a88d4a649654dea48da492d485c2caf480a14b847f7b26547bb245e479b1a0c462d6224460999d94501cf9c44fc40eb44d872f744d4e318449eda4843f84047433614a542d0e81241fd3b9a41d779c1413a011a40eba4c140db7eaa3feb71103f85e2f93f494f963f1c5cec3ec2933f3dcba1763da9b0e23d6cb3d93d65de153d5aa5753cf3eb7d3ce491473c4a0bed
  | 7, 3 => 0x82d492fa8071b4d07f5639357e4a36cf7dc0302b7a5ec34c7a02827879f8832379a2a1a779a025c17976a87978e87d8577e76b2f774a1e63770c770d762de1f475e959e175c0356f752a5d3874ebc8d3748af25d7411c9b973d557107348fcc371fac38871dddc41712b05097123c33f7118303d70a6dc9770954a727063f54d6e218b266cdc62566cb1c2b26b0959f369ef72b9680e3c6b67d323ab66caa91c65fc317b655cfaa76555517165202fd664db388d649cd2bd63b74d356340e6416273d93e625dee4261b166b261a26a35612b767660cc0ecd5fc005475f6247d35eeb8c215e6866685e41aeff5df888dc5dd6b1da59e5e4845809db61577868dd
  | 7, 4 => 0xb1c5e182aa908d4baa44ce72aa20c2d6a9e292d0a969f897a89e63b9a89da835a8968111a821e715a7638afea752ce5ea74308cca66fc4e2a64d9a9da600d5f6a4b033cca416ef55a3c7fa2ca3264d6fa17be3a3a0d1bbaba056e5469f9e35d39f3655739f1f82fd9f17c9fb9ed0a5159d5eb3eb9c33c6d69ab5c72799fc7bf4991fc5df98c313b893747dc1923a227791ef40e4909bd5ba902a3c52900c78c88f4ccd0c8f2a74a78ec7f5268e8244e28ca2eeb28c52ef448bd885848bd720698bad9f4d8b58a27b8a8206f58a152192889461ba880738ca87dc302b87ba3f9787a1a8038769455284945bb683a85c838389e55d836ec870834fd0c1830e1b85
  | 7, 5 => 0xfff6b317f788c7b2f449e2fef1a3b623ee606ce0ee1f1ff7ea9ceae4e720f768e43bc0e8e2b2f550e2a5f2b9e213b0ace17bf671d8b162c7d78d9556d6109f0fd4374317d40670d7d39b64a7d281f217d1c2e2cbd164f824d03178bbcf857c62ce89814bcdf8b526cb73e210c96c6919c852ed36c64db549c2f47615c278f5b3bee80d03bd579776bc05b554b87b5100b847ef9ab760ef3fb62c397fb56255e4b53b9e7bb531c917b5174306b2b60cecb20b32a9b1cbec36
  | 8, 0 => 0x612b767661265a2e5fc005475f6247d35eeb8c215e6866685e452f5f5df888dc5759e4ff5604b33c53d60d295228375c5068be014fca03f84b48d7e64ab6b7e8480a14b847bb245e4501cf9c44d872f7437178f442d242203feb71103f494f963f256e6b3d6cb3d93ce491473665adcc35c9137835473438319085422dab8430298d89ee2971cb38267c0a0c265a0d46252e7c512439730720bd315b1fe2e1241eab266b1d1966191ce143d41b65ceb21ae1fb52197c96771953c3c2190e8de516b1baca1630f75014d2066b14783cbe13a3bd1310dd99df0fbb0cbc0d37ae260c52bd1d08f66eee07f19ca506196b3e05b3aa5f04b519610448f40101c96197
  | 8, 1 => 0xea9ceae4e43bc0e8e29507dfd96bf662d8b162c7d40670d7d1c2e2cbcb73e210c82998b2c6876fb9c278f5b3b87b5100b6313a81b62c397fb56255e4b53a5743b5288349b2b60cecb1807712a600d5f69f17c9fb9bf1c6009b9d035b97c99f0891ef40e48fc5070f8b0ace178a8288e78a15219287a1a8038560058684c6d6178389e55d836ec8707ea282e17cc9bfee78272ab0770c770d63fa21b4621656fc
  | 9, 0 => 0xf036095ce6280471e1a8333dc88c8747c7434ed4b4c4c71daa18b71b9efe9e908af8a2658a152192853ca3f97aa2f3387346bec16b6855ef5e80882e56e1e69352beaf2c5252e89e511a1dbb4a5404034a264ec547f8011e41bd218a3e0b18323b162b4034698f4f344c8cae33feb2e92e42b47d28349d0f1db1f7b81b1cf7861a9e35c119bb665619b434861752148815c8776712b831c31214519810361bf00adc43f40a1fb0a3085b619208558a9d07bb54b4071370820514a8c9041244d9
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x1010101070801010101010101010101010101010101010006010107
  | 6, 0 => 0x606010604020606010a060606060b0708060a060a060a060a01010a080606060604070a0108060801060a0601070606080606060106030806060e010a07060b06060608060901060a01060a010c0606060e06060f06090601060103060606060a0601090b0301060c0606050a02010606060a0a0a0a0a0106060a0a010d0a0a
  | 6, 1 => 0x70601060108060601010606060a0a0a06060606060106060a06060606080401060606060a010a01
  | 7, 0 => 0x608060406060606050208080208020201080804020606060408020302060a0808060302020a080304040a080608080406040606080402080a030306030a0a0a06030606060606080a03050608030308080104020804080208050a05080604060a020602060608030902080308050a0606040504060303080508030404040306
  | 7, 1 => 0x80608050506030a060804060802030802030a03080503060608020a08080603060a030a0a0803030808050c0206020808050608030205020404040308040205030a0803050605080308080806030806080503060306030a0806050806050603040c05080a0a0208020405040a04020608060608020208080606080104060803
  | 7, 2 => 0x40202010204050802020a0204030206020306030306060606070306040a040206040808050602040408060806060808060403040507060a06060a06080205040c030a06060a06020406080a0608040a06080205060806080a060a0a03080a080402060806060303060804040a06
  | 8, 0 => 0x50203080303030308060208080204040808040204040206020a0804020308060404020a030303080303050204040203030503060805050804050202080808020808080602080602060304080803080408020308080a08030308080808040808080a040808030304
  | 9, 0 => 0x50203020404020202020202030205050402040302050204030203020204050505020204040205020204030205040404
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 10 0 (CN0 s)
def CN : Nat → Nat
  | 5 => 179
  | 6 => 786
  | 7 => 1579
  | 8 => 686
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0x414cbcac41367c793fdc2f333f6c3d793f4c55363ee2dba63dd40a973dcdcbc43a21176039d714c7385e944e37771079371ac847369d4cb9347cec0b30815a3f305f69ab3039e4e22fab6a2c2f5216632f3025cf2dd9e0942cbaf3fa2c81839429bef98a293289ae270f53e826ed63542583882d2555c7cb24c13028247e6b382235f59621fc55652027094f1e06dc2d1dbd367c1d28c6261be40b7719ff7b53191152d618a0c84118886ef516280d0b155b89ad15453f011442df62130d11f412d1634f11c0d9291127efb11103e0000e86e0f60d869bf90bea0fc40b2697ab0879f316086d543008340dc408121d3003a41ee903210f4103019d9502dfad01
  | 5, 1 => 0x89c6c9d089507951841e09228146d69e7f41cb6c7d8a322d7c3458847bf161df7ab40c4c7928919377cabbc67706731b7701e8557578724a751fadcc74baf09f73ed0248714a74af706e11606fcd7b4d6f6df5da6d6943366b335474681520ee67ad44ca66304b6865cfd2bf639836c162b15a8062127e9d613534225d0000835b7fb44b5ae35f405a0a60c359f4399258d4948758be49db56af2b56552760d45430fab85427b6a1535fccb6533ddc2251d0de855139b95f511e33bb4f1c1dde4e56869d4cf4a0cf4c44b2a44ae9ec914ab5fa4d492cbe2f48f7f6bd486a4fb84866e1af464dbef64643abe945e901c944f9fbe144b7e02e44b4bdb8437d027f
  | 5, 2 => 0xf9e93465f96c7040f65e09edf5f94cc0f5ed65f2ec8ea4ceec325f52ec1d4a4ce941e920e93e1381e8dd2bf3e67e3a9ae5a88df0e45ec4c9d9402e5ad56612c2d40dbe2bd2217095cd79e736cbf4566ec9a8d3f2c849f1f5c7f272f4c749e299c6385802bfbd3056bed835a1b91c3735b83cd826b7019be1b65aa4ecb325a57bae249d23accde66eaac2b6b9a948dd99a91599f4a6288fe0a461a1a3a408f111a3e8109da3e45c53a3dd3f7ea1c0938ea161834ea0e704239df8b0ee9ad9a19a97d2f6b58f13b3228ef04522
  | 6, 0 => 0xfcc70350f2e11a10e6368150e484b280e1fb4e20e109da40e083ba90da37e7c0d53a3d30c5da5c40c4cca330c352c5a0c1ab5bd0c01ea020bbc998c0baced500b945fb50b85547d0b06692a0ac0694d0a5d79d00a1400d009985eba0968b8d20962ee2508ff3f9f08a3e483086e60b10801db0e07fd99af07e5a1c3078feb130743758d06721ef6065eb7510651d113058abafb0580188c057c75f00567ba1b0527bc7f04a44e7c0479c513044ca0d90405df8903c670c80360ffb102e71397029f1a400147af8c013b8aad0139eac10132955400fd40c200f54cfb00df4a8500d35c6700c63f9100c40e0c00b4dc000095d2a700733ffd00433c4c00134911
  | 6, 1 => 0x1bfd89eb1bc18e1d1b90a4881b5d55de1b5abd451a9b91ef1a6601be1a5934201a534bc81a4950e11a01dba919da075819c8bb0119b5a4e4198e619a19790b4c18ea29f918a69195186d09bb182008ca180bedc61802e6e117e00e6d17ba0fa717b5c33617ad077c1798aadf178058131746d6b8172c4eff17276744171ca10716d9807416d81f09164a8eb0163bf19e163722ab160c22ae15d6d62c15d2251d15b3fddf15af559d14bc5aee14af1d82139d8c6c136827a613492d41132b008912f356e3127b2abb1262cef5122d23c711f04d19118617c7116c19281141179c11152ec41101d84f10e950aa10e90e44107562631050fde9101626b110020f0b
  | 6, 2 => 0x29aa27cd29a46a342984a36828cbe35d288b3409281395dc27fd520e27d4271b27191c6a2708b46b26e6c3d726c4410026952e68264ffe132645da7d26439955262aaeb22619bc7425fd05c525ac72912588b820253474252465b52b243e99522438c1d42434941023c6d0b72382060123766105236c0c7d2353437822e47e7c22d83df92235f596222b189921b7dffb219f8b9b217d9b0721297a3b211daa122119544a21113cbe20b0b58c20aa7add2075c5e020223ad61fd4e7311fd452901fb478361f8fa7d01f6cab4d1f34f6131e76fe271e3c173c1dae18c71d749a371d523cbd1d31c4a41ce84d6b1cdd3cea1cc8c39c1c8c25ee1c7e0dbf1c1826c8
  | 6, 3 => 0x37144d163702d84836f1791936cf888536c6c5b736b9034c36b4b0143684693c3669a683364e555d35a3d66a3565fe60355798a234f239d334f0adf4348b4908343df95c340062cc33e6f9c3331dbbb432e72c3932b997a431de7a9631cf7faa31c1a5653182802c30da58ae30bb849230ac9910306b55413052ffdd304cc9e23001f0422f3253a12f2accc52f0e09902e81faf02e41ce6f2e0e282c2dd90fe92daa3f6d2d72c58f2d6a370c2d49e16f2d44ea6b2d3e19b32d03d2a22cd315c02cbaf3fa2c4b166e2c1a87212c0b50022b8822382b7b606b2b76a6f62b7049c12b512be02abd39612a972c9e2a56aaf32a4de5712a059deb29f14cb329d82148
  | 6, 4 => 0x44814473443d18e644265d6343be475142d42096424e4222424af2044218d67d4212fb7541994c534196f26d4176777d416b937641683e274162a716414ffcb941377526411ad3b64105bc3741016f1740eaf33d40c7f1bd403bd89c40090e2e4005b2173fde5f6a3fdd710d3fd71b6f3f9e49d53f87677d3f4fc5243f1ab3563f16732f3eddc6323ecf513a3e68f18b3e66ea733e631a963e4dd3f23dcdcbc43dc8e4ad3dadb7ab3d9c17ed3d78901f3d67eb2f3d5340be3d18f03c3cf7e04c3cd57ec33c2428383be24eea3b77d09b3b6153e03b5ed54a3b5ce91539eacd7139ddf76139bae381390676ee38fa2798386a821638040084377da3d1375082c4
  | 6, 5 => 0x51dc72ef51c15602514f199d50ed347c50d94f3e50cd342350ca1a9b50abc5ba50920b1a50665fbc504e349d4feca4874fd3e6fb4fc8f64f4fc1c47f4fb3e1034f7900db4f34f74a4f19c2d94f0d6a8f4e7f74044e0507174dcbe4ad4db4d24b4d6108474d52786b4d4662924c5d70b64c3ab0054c10503e4beb72074ba245c34b9cbe144aeb73074ad4e43d4aba34584aa1c29c4a437a974a18a7ee4a17e88f49c36532495dc46d494b653149351a854831c7554821e19147ce958447ab361347a7bc7547a509db479d779f473f5c6846d4460846d1428246c258b8468634044643abe945e0bfa845daf04045aaff3c4597c7654580135744b4bdb84499c49e
  | 6, 6 => 0x62eba7a162b15a80625c0dac622f816c62097c4e61e7575061e306c46164aee6615a567c5fb761a95fa643625efec5735ef78bca5edff38f5ed3c81f5eae6c555e4f81245e422d085e26330b5e0442775d5a96565d3a53705d32f22a5d06253b5cee33b15cbe51c15c7383005c10b1845ba8b07a5b28aa845b1ede7f5add3ed85a630f825970413b58f26de958aba4f4588bf1985772d54c576d6d9057240b15571e34205702535556dc96085683fe3755fe881355ec30e955c13fba556957f354e0974a549ec2b153edb20c53bf87b15367b61c536609ff52f7110d52eed3cd529a2c155298bf8d52894f47526098cd523dfb5352321077521cd18c51f19930
  | 6, 7 => 0x75766d9c7509388b74f597bb74ef399e742876dd7407791873807d0c7342f88173151c5a72d2b72a726718c271d3a2a671d08c2571bda74871bad9497189a1a17155a249714a007e7101caa571018729706e11606ffae2486f9ab7bd6f1543a06f0fb1ad6edfb24a6d8c14456d723c496d2332a76c81b5f56c7aa13b6c3a3ee56b8487356b1b9e306b09fe726a7c73196a771f486a5a1ca76a01291369e5a10969896286697b10416966df44692c595668c3889668840fd9687f20b668335c4067333caf663ded4265e75ab165b543696588f291658233c164f5a24464d6a5aa64b46b5864b38a36643ef135639d14fb639cfc64639836c1638ae57f6388a423
  | 6, 8 => 0x8ca618748c9934eb8c3bc55a8bce62658bc13e508bbd6bd88ab194988a7475d28a6bbc498a4a4d5c8a31f11f8a2928f089573bc788d7bc63880c135487b31ef886518ef286472dcf86361bcd85c0ba0985972750855f971e85443baa852994e3850e0f3f84b877668491bcfb83d9fc4f83cda67f83c517fc83b4e376839c443a833238d2831bbdf7831754af82ad1941826e12168211b88881e181e0806193fc804d14f38033debe7f2d6ed77ea5d5d17e0948b87e0591177c3458847bd4a72a7bd404447b0f8c147ae602f07ae23f147a3d9a7a78e9d76578a4993c78281add7823172e77cab18377bde87b776cde037701e85576192e967606719375f13125
  | 6, 9 => 0xa511a1f2a50e4325a494e90ea48db73ea45af7c3a2e6c616a2d0f9d6a29eb6aca258fe69a22b9740a18b28a8a175e5e8a11b9221a1038f60a0a1fa1fa04767789ffb44a29f24ac539e9ef9579e5c74ff9df34e269d68c8cd9cedd4509c13e09c9c023df89bdb27109a0be4f399bfae4398eef84898a6106797f7aa1997aa32f99716e4c3968aae6e95b0ead39595dc669584585a94f9335b94f91c1a94c7bb4094bc8711948e182794541028941bb7e3940618d593ca791f93c62fde93b08f2592f20bb592cb1f5d929081a4920c059a91ecf33a90efdc0790cb83458f3b5e4e8f1d3db58eebc7918da9f7f08d992e878d6935c08d6774f88cd483388cd3c1b5
  | 6, 10 => 0xc8506aadc849f1f5c82b0162c7d78252c7530729c6bafae1c66036a7c644b103c5e5a3f7c5d52090c5bfa094c417a924c37b0c79c35b687dc1c0412ec08065aabf431207bf260f66bed835a1be8896eebd9f6a11bc91c687bc218696bb743c3ebac201ccba8a1a03ba30ff72b99d6557b97c5869b95cebe2b91c3735b8ef7876b8a37fc7b80de4a6b7d12f94b77b1d8fb68269edb63226e7b612cc85b5ed576cb5ec6babb4bb3cb3b40958eeb36b1e1fb30e1fc7b216b20eb2153128b17eb5fab0b08331b03bcd26affac0cfaca74619abf81b4dab4396b1aaf1c3d9a9664920a9544ebaa9300169a92e4e43a78809f9a786a2e0a776f44aa664b27ba5303182
  | 6, 11 => 0xeaffadbae9c50ed9e95a0ae6e941e920e8dd2bf3e8d20b94e7d0c0d9e68ef200e5a4a21ae50b4fede41b04f9e3a92059e392357ce23367b7e19bb4ade08597b7e066df2ae05a4509df429e98df191a2dddeffcd5ddced0eadd9aa728dd9831e4dd58eac9dd057578dc0e65efda8fef9dda3241acda2ac447d9be7204d95d1bc1d8723e35d794c2bdd6442a37d565fe14d533f0b3d3d71baed393b924d37c5774d2d183d6d264d26bd2267dcbd2016d91d1e88c72d1d46004d0b30dfbd059576dcfd02267cfb1f5afcf7559b9cea58da9ce1b592ece188bbdce0c6919cdd7bab8cdaafbf9cd15c69ccc96a442caf7b2a2c9929e70c93ed49fc9058d3ac88266bb
  | 6, 12 => 0xffe431f2fe9a1740fdfd6ca3fd98af76fc209b35fbe24e78fa283386f8f0c3c0f88685acf7e84906f2d54a83f2c81125f0b42098ef047a68edc74813ed0c12b9ec39c978eba12215
  | 7, 0 => 0x6a2a8780680b7e4066e6176065eb75106597593062df26d062ddf40061c9a640615e42505f25ff305ece61605d72a660549efc505287a6505157d3e04e2bc5404c61c6504c241b704709323045927730400f31b03e555df03d745da03ca53bd03c670c803bffdeb03a1d133039ac1040397b7210371e91d033be9c2033096880315a805030cabcc02dfd7d902d75f4f02c4c4d20296d8b0027bf6e502690aef02248af9020444c501fca9f701f3db3401ee389001e38c79019dbc59018fa9f50173c6e10161b89500f653ce00f4dfad00e3e92000e258e800b6af9f008a7b6000867fc60074218d005a57e100509fe3002a2392001c548c000eb2e20003f940
  | 7, 1 => 0xc04f1cc0c02f35f0bda527a0bd47b850bc9bcbd0bc64dfb0bb99a0f0bb12bb60ba55a7e0b99d9dc0b9097fe0b8441550b77a32b0b708d8d0b6948650b3a459c0b35402e0af696cf0acc97c40a92616a0a7c1c4f0a665a6b0a29c4660a21cd7809f5bd0d09f1e26c09ea588209ca7b5009c956e109c462cf09a1542a098a8d920978699009663a140942352b092f15e3092dbbfe091d623f08f58d5808efad0108ebe40a08e6c83608cd7f560899b0b308992f9d089399b10887fa030881a17208707f5e08400c7c0801db0e07fcce6907c0433107a793ba0792bc0b078daff30783222b07814ac3077b23880764635307248cf107199d2f071435ad06c15f5a
  | 7, 2 => 0x10020f0b0ff27c6d0feda3670fe5c2d20fe37bf70fd6ae7b0fa461c60fa173c40f9eb29c0f8f8a9e0f8f216d0f8e82ee0f67aa090f675c7c0f5664d60f4ae1c60f468bfe0f44c5180f2f4dc90f068ae80f067b5e0ee19dbd0ec6d3070e8ff1c10e6f2a9b0e5b34dc0e4761490e03811e0e0009ed0de5164c0dd86ce20dc42ec60daa8c150d9ea18b0d6b8d940d594c810d4252ec0d20885b0d2030510d1857410d16c0810cfe85a20cdc50960cd0b0410cba923d0caed3400c748f340c688f820c6284250c626e870c58127d0c5642b70c4f01d00c4b6cb40c49d8b00c44bd340c3edbe40c3d620b0c3bcf560c2f47420c2c9bb20c1e762e0c1ab5bd0c0aab1e
  | 7, 3 => 0x15896f0e1588b6ad1577825f1571ab6a156de4c0151d07171515f790150dbd7214d7758114d452e114b623371496a6d6147abc351477a76b1470ec5514388ffd14333ccf142f914f1419896b13f75bbc13df304113caccf1139d8c6c1398a02a1342f30f13380f5513322e141319cb6e13167fa1130ec65b12ef1e67128f1b45128799df1285fe681274f857125d0a8a120bbca41209a821120787d811f7cdc211eed68211ee1e0c11daccda11d2654211c6daeb11bff8af11b8a3c9119c2af2118bf5df11880d681163a71811333bb2112e65a61128d494112828b1111c46da111a68a51115058e1109f54110e90e4410d2a992109e84c210381abb10224e0a
  | 7, 4 => 0x1bb050041b9e41eb1b7668061b6d77e71b35a40c1afe2a2e1ad105701ac8eacb1ac748771ac2fa821ab896861aa5f2fd1a7974121a784a131a01152919d9245e19ae2bab19955721195179b319463b52190bf42b190833ff190395a018f004b318eb621418924d57187a83921835331c182fa2611820303317f87ca617f864c117f7771e17d5809517b26675178e63ae177f27151754add8173bd1701725551317206e2c171ca10716e710d616e64b6316dcdbbe16d6671116d6136016c5f3ad16bcab2716b826ef1647a393163bd262163722ab1628567316271b061623433b1610f84a1606e6ac15fb824d15f33ad015d29b5515d1228015ab44cf15a1959f
  | 7, 5 => 0x21affbbf21ab53f92155bfb3214c4b97211e4f1920f1276b20eb21fa20eae0a920e20e1d20bd315b207a9e37202c1110202a4c942026178c200bb1b91ff96cbd1fef5e4f1fd452901fc1a53b1f84cb891f44d87c1f3072651efb93011edfcd4a1edb68851ec209081eb54b2e1eb17bad1ea83cd41e9be86e1e34f9681e1d26a91e0881c11df7cbe31dc49ef51dbf7a931db9b12c1db4ea5d1d73f8831d6e6bda1d523cbd1d49e66a1d452c701d3a573e1d33256e1d31c4a41d1dd2701cfca3921cdd3cea1cd875bb1cc1e7181cbaf5ac1cb2b3f41cae143b1cad20281c80efcd1c74255b1c41810c1c3a14371c2475f21c14fe1a1c0aa11f1be8aaa71be454df
  | 7, 6 => 0x29e4e0b929d00e8d29c940f529c64f5c29b550e429a403072971d68a2936208f2921e16c28cae0e42874438d2856f7b228391853282149852818e6e027f392d827d5ef6e27d4271b27ba568e273dcddf273bae702723f2c1271d35f6270e4cf027047de2270225e526d7872326d0555326c52607268d6c2726249710261cf14c26125f1e25fc96df25eb554d2550cde925149d73251397eb2505932324fa6f6b24f19f7324bb1df1248d5d3a24791dba246e35552458a7fd2457bce924381ed2242ff50a241f0c48240ab10423e8c070239d2140239b5d15236ba07b22ff874122e4983422ceb81622c26be822b48b2e227a4f1f223bd8ec21d0fc8621c4e700
  | 7, 7 => 0x2fc42a212fb61abc2fa733282f8babf02f6ca68e2f6800f72f582f712f32905c2f0874562ef01fb32e64637c2e3650802e346bef2e30798b2def60c92dca11682d9643a22d91edda2d8e738d2d6682922d515da52d22cdf62d16f2142d0e803a2cfd63542cfd22272cf7acdc2cc27a192cbe24512ca869f82ca0146b2c9a3d762c364f7e2c1647e92c098d462c08628f2c00078d2bdd61cf2bd8248a2bd24bf12bb38df72bb1a1a12ba294592b7826212b58235b2b3317cf2b0a481c2afe53d02afad0972afa60922af2a62e2aef97b72adc633c2adab2002ad05a552ace18852aae69c12a6eeb722a6b3d902a5155c12a31b42b2a23e2ef2a1bce2e29fd64a1
  | 7, 8 => 0x377da3d136f19d3836c66faf369c8b023682aeaa368009ef3659047136110ade35fd3cf835f67bc735dc5e5535ca4abb35bbc3433567b0083550bddc35269a753519aaf334f17fc734cf260934c71c2634b3e99034960ac9348f1498346fc8e334506a40344131563434fc63340032c033eb403133e2221c336c6c8c3318d85d330d5c113307a39a32d4446432d4193932bb02b132b1138032afd7cd326c3bf8323ba38a321b835932177f3d32115e3132101cfd320dc04032008b3631de9aa231c96f6831c1a56531b2e6903171ff9e315dc7033159718131523fb13134248d30b732e23065c8d0302466f3300f4fbf300d542d2fe87f142fe36a512fcd8f6c
  | 7, 9 => 0x3e309bf43e1a15373e02b9333dfa2fcf3dd3f7693dc31d4a3dc2e6203d85878e3d01c8a23ccc2fa33c8ca9b83c6181413c4f0ca13c3c29f73c2fda9a3beb20f73be2f3903bd1f5753bce00353b96c7613b943a113b81f0d33b5ed54a3b5ca8713b390ea73b2af2803ae83d273ad487f03ac190493a5675b93a4f76513a3c83313a38c66b3a2ca9763a0d2a403a04cf333a043f733a02f48d39af4bf2397c6c32396c5174392f2fa3391038df390ee51e390a61ea3904c47d389320b138702c01386cb75b386bd639385e99ab383b05223826b361380c7c4437f8986237f3f9fb37ef408637ece69437e8803737e7968737db9a5d37d2e49137c847cf3780abfd
  | 7, 10 => 0x43e21de843cea2bb438ce6a6438458c34333da47432edb5642fe380042f4550742f2ada942e4afd342e4768742c928e54253772e42534399423c1308423826ac422beebf4218d67d4209fe2b41f8172d41f6aa9141d97c184185b01c4168ad7b4125f6ad411ad3b640f7e67440f6f5f340f1d30140eaf33d40e48e3940d36de840cef4a240c7f1bd40c08ee540a28bc9407924af407097d64025323b401a676f3ffd5ee53fe0ad9d3fd9f30a3fd2a83a3fb9872b3fb6f20b3fa8772c3fa66bdf3f9e5ce33f9655443f843b393f61aa5f3f1ab3563ef644ae3eec67583ee9f7f93ee2e89a3ecf513a3eb409133e951c283e88cda33e862b453e5837bb3e451c95
  | 7, 11 => 0x4b9cbe144b8c34e04b555e9c4b530d0e4b2738ff4b08d1a14ae7abbc4a703da34a690bd34a56f9094a4264a84a324d6349def67949c200a149aeaeee49a5179f49343b73490aad1649098acd48f21b9d48ba366c48ade3be489dd178487590974838b86c482282c14806ebd547f7750a47f1794647c66ea647a8c0ba472dcc8c4727f5974719f965470594f046a645df46870aa54684554b467d4eb4467d28e8466aa9fe465007ec46404a134622bc0d45f9141a45e5db7c45e4d73645e0bfa845e0289d45daf04045c596884575dc964542ea6a453d91dd453c127244f69faf44e88c4244ae705a44ad6f92448973ef446eb089440afd144406023543e713c3
  | 7, 12 => 0x518a9cbd51621af0514e426c5124a86750eb760750e6bc9250c4d00d509f33635097b871508af2505079b15050738996506ac90c504eb68f5044f68050401996502fd6e450270d28501a58cd4ff84b2e4fc123204fb206a34fac297b4f8e0daf4f793e044f4a98c94f2176484f0faf794f0886ea4f0820494ef4d1be4ed942574eaffd514ea8b3064e7b67604e78aaf34e72615d4e66cf054e56ba5f4e21caa14e06fa484ddb40a64dcbff9d4dad77b24d98b9f24d8ffbb94d7ca5904d754aff4d5a85314d4b54cb4d41df324d33af444cf657e64ce068284c82c72a4c794fe84c5ce53f4c3927544c269d334c1778fc4c00010d4bee9bf54bea97d94bb08d88
  | 7, 13 => 0x593359b2592db1e35926214d5906576058e9745c58d6dfd158cf765758befc2158bed1ca58b8b2c458913f875848e9465802dee757f645bd57c09ea657897c3b577024d0576f34615761605b57426f9256e7724256e75ac156d45a0056c581ae5689b8ff566c36e556691fed563da014560c4f6d55f97f2155d65739558fb6e35535f6ec551421eb550abf045504dc3754fc3e6e549ae261548c3c87546a4bf3542e5fc954119e2653d2929253a6be3a538ad4bd5378844a535fb4ab532113805312b3ba52ee454852deb0ca52dc601652bef60c52b4366b5283450f52798c495273e83e5212c07c5211bc1851f366ab51f103e551d1761751bb42e651ae184f
  | 7, 14 => 0x61e4b83f61e0ccd361c8dacd61c8776e61bdf3a86194c692617779c4611e1aaf60f11a2e60c532a3609d5661601d50a5600c2e9b5fe6a49c5fdacff95f9de41e5f6f096b5f46c4fa5f379fa75f32cd355efedba65efe94765ef78bca5e7173a55e6085f85e363e885defbef65dc7fccc5d7cce755d770f905d7188175d65ddab5cf2b4265cb8682d5c9d90805c67b4455c64443d5c4b7abd5c369ee25c268fca5bf0a4565bb57d8d5b898ee55b8023d05b723dd35b05f8665af327945a9673c35a76a5fe5a60d77b5a447e3d5a4029775a080a3d59f4741b59ef628059e5721659d6b8b959c4013959a168dd5970a0bb595b2cb5594d87755941c868593a9f8c
  | 7, 15 => 0x6c4f8a8c6c3cb3f76c1f66b66c07acee6ba623266b9ca8fb6b885ed06b677cc76b566f206b2877a56b14a9a96ad157516ab3f05b6a73ddfe6a5cba576a43e21369bb25cf69ba9ddd693b5288691699cf68fba93468e2155768d12a4868aa301b6894e9fa684186a968335b996820836467fbc7cb67c51853678804b6672b867966db75f166d2bcb2668f603c668aec286678bf15666916de66311cc765b145c6658f2be265616073651e669c650163fb64fd727b64f77d1964d6a5aa64ca343264c72a8a64b46b5864b38a36649350e1646169cc641f465863dc53ae63d8116a636c8081630fb3eb62e40f5f62a04a0a626a7d09624fcb0b6231a9f361ff7916
  | 7, 16 => 0x76c73c2c76bce61a769ca024768155ba7650ef46763a9cc875ea8b5475950979758323ef755ed09475034cf474f597bb74ed3f60747159627452acd374415a9c742bb4207409897e73db20f1738e25597347c0857323e9eb73151c5a730eed9672fe421d72f7e30172d44d3d72d11de372b4c9b57271f8d77205c91d71e52ac271de7eab71ac2e3471590b1e712fbd407111b15070e4b28270c543dd708db7367044f9d970013db36ffe5f0c6fe4e4c36fbe67cb6f9158166f3140f46f20276e6f0fb1ad6ee6f76c6ebfef7f6e98b6dc6e7ff1be6e51557d6e46bb8f6e005b556da7e87d6d85f7e96d68b76d6d5283106d151f776d0ec64e6cf01b176c7def2a
  | 7, 17 => 0x804d14f380037d5c7fc95fcc7f850fbd7f2874367f2679bb7eaa0fdc7e7d59507e4d1d197e4ce9a97e4725d67e3ff1ed7dda40127dcd2aaf7d82c94c7d535d877d1e95237d146ecb7cfc030b7cfad9b27cbcd5817ca74b687c71ad697c56d5367c396d3a7c35be9c7c2f091f7bef324d7be90bf87b27cd107b1d5b897b08db507adb26127ac11e067abdcd8e7a8087487a2ae71b79e8963a79b9bd3879b8f5fe79ad86d179a51f167984b8b579812f65797d9463796feedb78caec0278acd86b78a4993c789241ad788476bc7882efab786ffbab782dd78c78281add78172b3177e7db2f77df0cfa77a387677799bc84776fc04e7722c0197703620576d4c2a6
  | 7, 18 => 0x8b98c5138b690a768b5823a78b4e8a538b0ac25c8af322b58acbed0c8a95bb498a90635a8a7d6e4f8a54211f89ee639789775272893d45c688d9518088a26ab0888b932487bf1405878d3f578755e58387345586870f73ca870951c28701491c86f53c9f86b98a8986b92dee8648f70a862662a6860cad1085f879a385dc1f4885d7365585d21043858d4d99856a6fcc854e8322854072e585002ed784e2552284d9973e8439cde5842209bf841b179a83c652fd839b4ceb837386798368dc5f8348345383463bf483303efa830f5bf382c53b07823da36c823d3bb582017eb881ec156581e6f0c481d140eb81cef508814253ef810ca40680c61e808062df8e
  | 7, 19 => 0x95b4518d9561c6609508987694e57b9094a7e33b9439263e9431e2dc9413c29e9401f91e93c2bb2193a00def93340b7c932d71fe932babe8932a18c892cfcf13927c49f3926aa3ef9258c4c69230f3199213496891fd15e291db720091cee9e191756525916aa69791537927914344dd9125539891226f29910a88bf90f26d7590c576fa90a903df90a6062a90813a8d906f7b549048f106902eebe8901bbc4a90171f208fcc84338fad08c88f7ee17a8f355f7b8eec4cdf8eb4dee28e9e0d268e1519f38e00273f8dd2daff8da3d2f88d9ad9e88d6fad7c8d2964298ce39e608cce95d68c52e8d88c4b9b668c3fff4b8c0aa3ee8bf97c8e8bd864608bbfdf13
  | 7, 20 => 0xa3f72c5ea37f2521a34e6080a30ca0e0a3051f24a2027585a17a1b2aa0d6af88a0a81d13a0a0eb43a0719179a05c6fdca00a0dd69fea8c0b9fd7aa909ef3acdc9eb12c119e97fc889e4284319e1406d89e0fb43f9d9d5b5a9d758a929d6c5a999d6aebc59c918cde9c8467209c36c4fb9c2b0f189c1d2d3c9c13e09c9b9d24839b16ee089a7346e499d52f5399d10d9399b7b51499b064ab99a51eed9908762a9901085598e0f59a9893677f988685c59858e8289814c332980afbc497f7aa1997eb00b897caf19d97c494a6979dc5869797706c978b719a975a064696de6d9596db832596c5b7e596ba08a0968f54f5965ec99595daa2ae95cf965495c940b6
  | 7, 21 => 0xb1abe51eb18831c6b15eceb5b0cf641fb0426e3cb026a961afc482aeafadea14af6eeb14af1d8defaf061bf3aeff6798ae3c5ceaae386a37ae25f391ad78f6cead067012acf1b94fac987a7cac8e2cdeac1abf5dac19b8b7ac0680a6abecc5e2abd4d9ffab648a75ab57ca85ab05337eaaf1c3d9aabe1864aa7e15eaaa536b14aa1cb10eaa1a4a27a9a1e824a983bd1ea96cfce9a9664920a965d8d8a962da62a959db63a829e8b8a7ce9836a732249ba7057467a7056e9aa6e73c9fa695cbeba65538c3a60f7782a5f3bfb4a5c9ebe6a5c60c42a5bb1b96a5b3e9c6a539dc02a5271c91a50e9fe1a503d6f4a4f162ada4d1416fa4b6e8bba42b573ca3fb960e
  | 7, 22 => 0xc5dccebec5071d01c4f7ceefc4d98d7ec4839c38c4688effc3485a4cc33e26c2c31557eec2dba315c2b49b40c2a5543ac2a41831c1e0e7eac12939eec1260c4bc069448fc055a396c04c41eebf8d47f7beff516cbed4ccfabec3ec4dbd47174bbcb00c0fbc46ac11bc39b883bc12d872bbf761f7bbad79b2bb9b072abb93f592bb56460cbb39436bbb045eb2baf6e5d1bac5e3f3bac10c5abaa6909fba4dec11ba31167cb95cebe2b8a37fc7b89b4d61b860f8aab7c9d7d3b73978bdb734d7e8b6b20735b5f17b46b5ec6babb5e34ee3b5aba77bb53ae765b4f4ab4ab479b2abb434524fb40958eeb3fa59a0b38e5194b31cf6c3b2ec9e66b28fb9acb24a2b4a
  | 7, 23 => 0xdfb629eedf6806c4de469bbcddd6ee1ddd91bc96dd855a80dd4ca59fdcb3dec9dc083028dbbe6473dba4dd83db1bba2adacd8e68d953e351d90979f6d8c60faed892409fd87d92c2d81224e9d803ddcfd68b2c2ed65be65fd65b8d42d64c31bcd61b72c4d6024998d5dfc1a0d5b973a7d5a8a814d4f59f14d491d5a3d45f6fa1d3f7b65ed3dbd777d3d0fe11d2267dcbd0ddafd4d0cf2dc2d059576dcf951680cee4b7dbcdbcd6cacd5f034acbea771dcbc529b4cb25055bcb06c047cae7bd02ca1a9c24c98e9099c972a253c944fe86c92be6cbc8e90edfc8a9d847c80b9367c7c2b16cc72090b9c6bafae1c66036a7c65779d6c644b103c61ab9fcc5e9355b
  | 7, 24 => 0xffc372bdfd522a29fbdc7aebfb3b40c4fb013a45f9415e94f7f82621f7dd5b74f77d4deff659870ef612aa36f516d19af344253ef32a7b9df2c81125f2a751f0f11465c9f0ac9abef056abcaef047a68eec4540aede1202fed0c12b9ec1d2bd9eba3101aeb8801adeb7bad3deaeb4161ea803d6eea7a6d11e9f83e1ce804783be7ee500ae6e2014ee6bda88ce5799e6ae574e56be56d3eebe24879cfe17c58f2e095bb33e06a6369e027cdba
  | 8, 0 => 0xb1df8290b163c970b1205000b0d4b8b0a90019e0a8841100a3978da0a29c4660a141c240a0e452f09f1e26c09ea5882099cb94a0995da080992941909740f460942352b092f15e308ebdead08c8ae2c0779553e075b182706cd635b062db7e8061641730601ae9305f96c9105caff6b05b6a7f505aa7ae505a9e488057f11dc05759931054885d005060e6404f18cdf04b154f3047d088a0471b002041e2cf8041bacf803e761a103d53de7039a59980333d0170318aa96029b4c9e02657c720262e15b02248af9020c220801e432ae01545b85014e8490010d017300f4dfad00e3e92000b4b6f500b44ea7008fff660068e2f9004d7f25003673a1000c6a75
  | 8, 1 => 0x162aa18515d33806156de4c0155bbd91155a37d614e1691214d452e114b623371470ec5513d1c59f13cd0c2a13c22e5113972fb41391cba913393c921319cb6e12b4604912ad2e79128799df127cef571262aa281245a787123d98611215b35511f7cdc211eed68211e2af2311ded6c811db089c11d81a7511c1d42711a11e9c11951fc3118eb4e51179e58d1173fa621173c2a51111f33610c07e5d10509f38104b0e7b10339c9710224e0a0fe5c2d20f9fbf250f6ba9b80f2c94e70ee7d6580ec1715a0e66deb30e61444a0e5151fb0df4cf340dbbfd1a0d599ec80cd0b0410c9dfbda0c9a77370c94fe860c3d620b0c3bcf560c12c5610bb7fbf60bb12bb6
  | 8, 2 => 0x25fb41b525f11bf7256d489724f19f7324451a40242ff50a2412116d23f74b8223df11072347564222faea7522da108a22b9e0d222b95fb7221adb5f221a7937221885b421c4e700212d970220f94bab20708542204104a91ffeeaf61fb63c631f6ab24a1f3269031f1e0c121efb93011edb34261ebfe8361e9372b11da431731d98b4801d2f6c7d1d29c8021d16e5151d110e201cdab30c1cd5b2181cad20281c76d8371c56f0531c41810c1c04330b1bcef4051b805fab1b7420e81b6cef181a79741219f2281b1993c72e190acf1a18cdc85c18924112188b72b91877049917f7771e17a9a13e1751b3fb16fd3b2916cc41f416aaf1ab16628057163bd262
  | 8, 3 => 0x319cc757313da4cc30f0e74e30e7602130b7ca05304c03772fe87f142fd87b092fd2ff572fc830172fbd1d122f59b9442f464d7b2f1338942eb834f52ea5bf152e9015e72e76e9d92e6fb8092dfa857f2da5cc0e2d851baa2d6289422d4586a12d1418262d012da42cf7acdc2ceba5b52cb2faa12c270d0d2c268a9f2c0d980b2be8e3ce2bb79f2f2aa64d702a83faea2a6b88d22a26536c29ed57a129b90c4a29a343a629a2800c2961b9bc29604055293af57d2921e16c28e179072879daef284d1edc281f699e2818e6e02814487c27ddccb127c94b7c27c91d3e279b963e279b93eb273bae7026cfd51b269e5108263b13ec26125f1e260d5eae26032f91
  | 8, 4 => 0x43dbf92a43b17c6043abd5f7434cfdf6431f48b842fe380042f2ada9422344d0418b17d541052a0c40f0fb11407097d6403daee24002c61c3fc3d2c43e993eb03e5034ac3dda1b2e3dd4239a3d0b2c273cf020923ccee5d23cacdae73c79a3073ba715303b16bfda3ae83d273aba76283ab61b7d3a6e5ca83a6798173a3c833139c67fdb3895dd783894364038900f6238900683384953fd37f5d09a37db9a5d37649f1437307c3e37041225366726e1362249e135bbc343359b983235689464354f24af34f0fada34e35ba134db016c347bd24734572e0c34506a4034126f4433da5cd433c61eaf338478b9332b49713318d85d32c8f67c326d7b3b31fa1528
  | 8, 5 => 0x565b088d563549b055a4b5c955759d9954b18ac0540ba330537b0f46534295cb52ee454852d2d84d52c69bb552b2c307529137ab525630d751ff62e651ecd7b651b05f17513fd99a50ec46de50bc063a5056cc9750270d28501d5d0a4f91fe874f4958474f2dceaa4f02994f4efdad2f4ee6a2d24eaffd514ea8b3064e098c504e04d2db4dec739e4d754aff4cd497e24ca530604c269d334c1bd34d4c0cbe954bdf09574bb7a91f4ba94c914b57736c4ad8b1a74a77b67e4a1b15014a1317ae49f5e23c496170c8492512d24908103148dd9d6848ba366c471c437546ccc537469e93d5465adaf64526328644f69faf44ad6f92444be2d544460be0443e562c
  | 8, 6 => 0x68f1bd3e681c596467fbc7cb67f4ef79677a32af6759809467524ec4672bf768670e6c2166dfb24e667969e265d5a13e658f1ba4653edbdd64f02ec664a40b35648c11da64614fe2644fd5086400e41463f0d2fb636691a56335bed2630b6b7e62be466a6215936261745d82613f97826123b3e260564c015fb7254b5fb26bd65f0f87865ee1d2485e84390f5e3024765ddf4a5c5da22deb5d7049625d3ae4ae5cc3ebe45cb384a15c67b4455c4637f25c268fca5be149005b659e895ae9889059b2233259a278fb593359b2589c0e11589aa125587a5e325816190857eecf2957bdcae15779822157514062570d78c9568eb704568a03215678a50d5667f0a9
  | 8, 7 => 0x81e5a10481ca49d1819ccd278023d9727f2679bb7f10a91d7ef385507e4d1d197e359dec7d6839f67d146ecb7cf7b9697c73e6097c2f091f7be4198e7be0cebb7a9e9e2e7a9ae11b7a8e7fe97a60caab79b9bd3879124ad4781c7b3e77f7106a77f5a0447706ac837692ea1c75ea8b5475d2b74d759e6bf674ff795374ed49fd73c32c5d73a70fa4739bed2b734733ba733c0bb172b40c5f719565c070c543dd6f4f52116f0b3da26ecf570a6e46bb8f6e4594186db17ea06d6310226d5283106d32cd476d2110816d0ec64e6c3fb8b46c2226f46c0e34cc6b9c61eb6b50a7266b213f206b19008c6abbcd8b69e681ec69cfc81969be3dd0692d95fb691699cf
  | 8, 8 => 0xa0b75922a05cc96a9fd7aa909fb425e89f7ff7e49f6615859f39a5649d758a929d3878bf9d1bf7b99ba2d1d59b8cf2dc99f8277c99cb52d1997f96b8996d0743984568e098178427980afbc497508279965ec99595961b5c94ffc58493879db79329125592d267d692c282a192bde1f692b8a5c9921e6fe090abd70690a903df90813a8d8f9cc3b98f5e76bb8f5b3bc88eb4dee28e4369e18e3352f88e1519f38ae83ad78acbed0c8a14041f88cf84f388b47db688b4457e88a26ab08811d1f488024244873cb76c871c627986c83a2d862662a685ffc704858d4d9984e2552284d9973e84c11e018434ac8283f19c58828d64848273978f8207a98d81eaa6ec
  | 8, 9 => 0xc56be3dfc4211f4ac3a3e20bc3074ba4c185813ac06707a6c03c48c7bfa14e16bed43a9ebe8ba237be33d63bbdb07a5cbd2056a8bcab5e40bc40adcbbc1d67b5bbd21f56bb93f592babc5979baa6909fb9de8dcdb86c3b10b854f0acb851082ab7aa6b92b769d720b73978bdb4a0caddb3fa59a0b3ba2213b2f0833eb2bdc3c0b05d1a06b03272b0afbbfda4af66b423aec9db50adbdc110acc67f47acac29e8ac9f477cac580bdeac1ea26cabceae70a99fe9c7a983bd1ea81512e4a69ebe1ea685a220a5f726eba5916729a53c69ada452b6b9a41e8182a38d9ba3a3813aa7a364f6ada34e6080a311b10ea22cb62aa214c59ca1dac154a1548403a10a3254
  | 8, 10 => 0xfbcb0e74fae387f4f9e65e44f68545aaf54b2871f00d6466ede1202fec1d2bd9ea847a63e8d55ecde764ec3ce4ca2126e4499acfe30dc3a2dd480acadc947b43dbfed257dbf30088db57e3ffd97ca466d81224e9d7347936d6d905f3d68b2c2ed5b973a7d4b71f2fd48969f1d3d0fe11d33b7713d0cf2dc2d098af7dcf621422cf391a76ce2f2435cd0bc6cdcb25055bcae7bd02cac11654caa9a6cfc98e9099c9804aa0c7ec5405c6f90f8bc65838b5c60fc40ac5709d54
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x5341d56cd640270ddb5354c40228419354d440368d5026915402284195354c40468cd01690d40276d1b354d4402000195354c3034654d2654c404001db354d43043454d0654c40576d1b354d4402745db354d4404001db354d430468d5026915402615d945d1640218419354d440471ddb5354c40300019354d430274459354d440568d502691540276c19354d440468d1436d15403165db354d440274419354d4404615d945d16402164195354c40326419354d4403001db354d430471c195354c403065db5354c402165db354d4402
  | 5, 1 => 0x265db5354c40468cd01690d40271c19354d4405001d3354d43040019f3410d305165db354d440200019354d4304001db354d430418419354d440546419354d440486dd1354d4404464d5164d4402615d945d16402849db354d4404615d945d164020654d2654c402534592654c402264195354c40474819354d4404534194654c402464d5164d440235499164d44023541d36d4e40468cd05650d40268d503651540580ddb354d4402065db5354c402165db354d440280ddb354d44020011b354d4304184195354c40370ddb354d4402
  | 5, 2 => 0x80ddb5354c402615d945d16402001d2354d430481ddb354d440574419354d440400019354d430418419354d4404615d945d16402845db5354c403000d5164d4304534194654c402464d5164d4402465db354d4402065db354d440270ddb354d440253515164d440368cd01690d4020651b354d44020654d2654c402465db354d4404165db354d440274419354d4402839d945d16403001155354c30378c19354d440276d1b354d44045341d56cd64020651b354d4404165db354d440280ddb354d440278cdb6554e402065db354d4402
  | 5, 3 => 0x651b354d4404464195354c403465db5354c40276c19354d44040651b5354c40235419464d4402000195354c303284195354c40578c195354c40281ddb354d4405764d543d0e404464d5164d440278d5b634d640268d503651540386cd5164d440416419354d44040654d2654c402464d5164d44023541d36d4e40235419464d4402001db354d430435499164d4402464d5164d440200019354d430435499164d44020654d2654c402745db354d44050019f3410d3053541d36d4e402065db354d4404001db354d4304065db5354c403
  | 5, 4 => 0x465db354d4402065db354d4404001db354d430470ddb354d440280ddb354d4402465db354d44020651b354d440278cdb6554e40278cdb6554e402001d1354d4304845db354d4404064d5164d44020019f5411530378c19354d440200059354d4302184195354c40374419354d4405001db354d430428419354d440300019354d4302001d1354d4304675513594e40368cd05650d40474c19354d440476d1b354d4402001db354d43047459d538d6405745db354d440276d1b354d440435499164d440418419354d440480ddb354d4402
  | 5, 5 => 0x70ddb354d4402001db354d430476d19354d440446419354d4404001db354d430400019354d430476dd2354d4404001d1354d4302001db354d4304845db354d44023541d36d4e40478c19354d4402001db354d430278c19354d44040651b5354c403000d5464d430476d1b5354c402064d5164d44020651b354d4402
  | 6, 0 => 0x1d943d0e3020011b354d43050005d56d143020014d2654c302001d943d0e3020014d2654c304001db354d430200000164d4202001db354d430400019354d43020000054115203001502691530200019164d43020005e4650e302001db354d4305001d943d0e304000195354c303001155610d302000595354c303001502691530200019354d4302001d945d1630500019354d4302001db5354c304000d5164d43020019d3594e303001db354d43040005d0654c3030014d2654c3020014d0654c304001d945d16304001db54514303
  | 6, 1 => 0x15d1690d302001db3450c302001db354d4304001db354d430400019354d43020015026915302001db354d4304000d5064d4304001d945d16305000d5064d430400019164d43020019d3594e3040005d56d143020019d43d0e305001d943d0e305000d01690d302001db354d4303000005354c203001db5354c303001d945d163030019d43d0e302000595354c303001d943d0e3050014d0654c303000000014f1080014c5350d305001d945d1630200019354d43020009e465163020011b5354c302001c35650d305001192654c302
  | 6, 2 => 0x1152690d303001db5451430200019354d4305001d943d0e3030009d56cd6302001db54514305001515690d305001db354d430200000354d42040001946cd43020019d45d16302000d5064d43020005e4650e3020019d45d1630500019354d430400000354d4202001db354d43050019d538d6303001d943d0e304001c336515304001db354d4302001db5354c3040015026915302001d943d0e3040011b164d430200000648d5204000d5164d43030000043d152030005d468d4302001c936d17302001db354d4302000003410d205
  | 6, 3 => 0x18b365153040005d0654c30300000365152030019d43d0e302001db354d43050014d2654c3040011b2654c302001c736515302001d945d1630500019354d43020009d4694c302000d5164d43020015036515305001cb5650d302001db5354c302001d945d16305001d945d16302000195354c303001db5354c302001db354d4302001db3450c302001db354d4305001d943d0e305001d945d16304000d5164d4303001cb644d63020009a5310d303001db354d430200019354d43020011b164d43020009d064d4303000db6554e304
  | 6, 4 => 0x1db354d4302000195354c302001d945d163050019d43d0e302000595354c303000d5264d4303001d945d163020019d43d0e3050019d43d0e30200019354d43040014d2654c30400059354d4305001d943d0e304001d2354d43040010d644d63030011d36d4e3020014e2654c3020005a5310d304000195354c304001d161d4d3030019d43d0e30400000354d4204001cb5650d304001d943d0e3040011d56cd6302000db6554e3040011b164d4302001d7634d63020019d538d6302001db5354c3030014d0654c302001c3644d5304
  | 6, 5 => 0x1db354d43020019d45d16303001d943d0e302001155610d30200000354d420500019164d430200000001491080005e4650e302001c3365153050014d0654c302000d5164d4302000195354c303001d160cd5302001195354c303000d5064d430400059354d43050011d35115303001c564cd630200000164d4202000195354c303000592654c3020014d0654c305001d126516303001d943d0e30200119354d43040010c5350d3040011b354d4304001d943d0e3040001d468d43020001946cd4302001192654c302001db354d4302
  | 6, 6 => 0x1d945d163020011b0654c303001d943d0e30400000354d42040005d468d4302001db354d43050000045d16205001c3354d43020010d361153050010d361153020019d45d16302000595354c3030005d064d430400019354d4304001d943d0e30400019354d430500019354d4304000195354c303001d943d0e3020011b5354c302001d945d16305001d943d0e305001d943d0e3050009d0654c304001d943d0e302001875650d302000000654c2020019d3594e30400119354d4304000002654c2020019d538d6304001db5354c302
  | 6, 7 => 0x1d943d0e3050009d4694c302000195354c302000d5164d43020019d538d6304001db354d4305001db354d430200059355163040014d0654c30200019354d4304001db3450c30500059354d4305001db354d4304001db354d4302001d945d16302000d5164d43050005d468d4302001c76454e3020019d538d6303001d943d0e302000d5164d4303000d536d17304001c35354c302000d5164d43020009d56cd63020010f644d6303001db354d43020014d2654c3040009a5450d3030019d538d6302001c7354d4305001155610d302
  | 6, 8 => 0xd5164d4302001192654c3020001d36d4e3040014d1654c303001c7365153020014d0654c3020018b5650d303001db354d43040014d1654c3050019d538d6302001db5354c302000195354c303001db545143020001d35115303000d460cd5302001d945d1630200000000c110600019354d4305001d943d0e3050014e2654c30200019354d43040011d36d4e3020000000095108001d945d163040010c56d0d305000005354c202001db354d430500059354d4305001db545143040000064d0d2050009d56cd6302001db3450c305
  | 6, 9 => 0x19164d430200019354d43040014d0654c302001db54514303001d943d0e303000192654c30400059354d4305000db6554e3020019d538d6303000195354c3030019d43d0e30400019354d430400000000d6108001d945d16305001d943d0e304001c736515302001d945d163030011d36d4e302001db354d4302001c76454e302001d7634d6302001c36554e302001db354d430400019164d4302001d945d16302001db3450c30400019354d430400019354d4304001db354d43040019d43d0e304000595354c3030009d36d0c302
  | 6, 10 => 0x5e4650e302001c556d0f302001d943d0e304001db5354c302000d5264d43030015b064d430400000064d42050011b354d4302001513594e303001d943d0e302001d1354d430400000354d4204001c336515304000595354c30500000000d610800119354d43050009a35115302001d943d0e302000005310d205001cb365153030015026915302001db5354c303000d66454e3050009d0654c305000195354c3020005e4650e3020001d36d4e30200019354d43020014d2654c302001db354d4302001db354d4302001192654c302
  | 6, 11 => 0x19354d430400019354d4304000d6064d4302001db545143050005d064d4305001db354d43020009954d0e305000d5164d4305001db54514304001db354d4304000d05650d3040014d0654c3030011b354d4302000d5064d430200019354d43020019d538d6304001db354d430500119354d4302001d943d0e302000d5064d43030014d0654c30300059354d4305001d943d0e3020010d2654c305001d943d0e302001db354d43020019d45d163050014d2654c3020014d45d163040011b354d430400119064d43040019d45d16303
  | 6, 12 => 0x14f108001db354d4302001db54514302001db3450c30200000354d4204001c556d0f302001d943d0e304001d945d16303001d945d163020014e2654c302001155610d302001d945d16305001db354d4302001c35354c302001db354d430200000354d4202001cb36515303001d945d163030014d0654c305000d5164d430500019354d4302001db354d430200019464d4302000595354c303001db54514302000d5164d4304001db354d4304001c75350e30300019164d4302001d945d16302001db354d43040015036515302
  | 6, 13 => 0x1db354d430200019354d4302001db354d4302001c736515302001d3269153050014d2654c3040019161cd5305001db354d4302001d943d0e3050019d45d16302001d945d16304001d945d16302001cf6554e302001db5354c30300019354d4305001db545143020000065cd5204000005354c204000590654c30300019264d43030005d468d4302001db354d4302001155610d3030009a45915305001c3365153020014e2654c302001c736515302000d5164d4304001db354d4302001db5354c303001d5648d5304000d5164d4302
  | 6, 14 => 0xd5464d43040014e0654c302000d5064d4302001d943d0e30400019354d4302000595354c303001cb5650d302001d945d16305001db3450c303001db354d43020019d45d16305001d943d0e3050005d064d43040019d45d163020014d2654c3020014d2654c302001db54514303000003410d2050001d468d4305001db354d4303001db3450c30200150365153030009943d0e3020009d36d0c302000db6554e302001cf6554e302000005354c2030019d538d6302001db54514302001db3450c3050019d3594e303001d943d0e302
  | 6, 15 => 0x1db354d43050001d468d430200000354d42020019d3594e3020011b354d4304001d943d0e3040014d2654c3020011b2654c302001c3634d6302000d5164d4302001155610d302001db354d430400119354d4302001db354d430400019354d4305000d461cd5305001d943d0e304001db5354c302000d5264d4303001db354d430200019354d43020019d538d6302001db354d4304001db354d4302001c36554e302001c936d17302000d5064d4302001d943d0e30400000354d4202001db354d43030019d45d163050001d468d4304
  | 6, 16 => 0x1d945d16302001c76454e30200019354d4304000d5064d43040001d468d430200119354d4302001d945d16305000595354c3030005d36d4e302000195354c302001d943d0e302000d5164d4302001c73651530500059354d4305000195354c303001db5354c302001d945d16303001db354d430500019354d4302000d5164d43040011b354d4304000d5164d4302000db6554e3020001d56cd6302001155610d30200019354d4302001c964d4e30200019354d4302001db5354c3020009d064d43030005a5350d30400000354d4204
  | 6, 17 => 0x10d36115303001c7644d5304001d943d0e305001db354d4304000d6164d4302001db5354c3020009943d0e302001c936d1730200000350d52040014d0654c303001db354d43050015026915302001db354d4305001c76454e3020000000095108001db354d4303000592654c3020019d45d16302001c564cd630200119354d4302000006450e203001db3450c303000194654c30200019354d4302001c3354d4302001c936d17302001d945d16302001db354d43040010d361153020019d45d1630200019354d4304000d6064d4302
  | 6, 18 => 0x1db354d43050019d538d630200019354d430400019354d4304001c76454e302001db354d430400000354d4204001db354d4304001d945d1630300059354d4305001d3354d4304001db5354c303000595354c303001d945d1630200000064d4204001d943d0e304000d5064d4305001db354d4304001db5354c302001c964d4e302001db354d4304000195354c30300000354d4202001c35650d302000d66554e304001db5354c304000000654c202000dd2691530500119164d4302000595354c303001db5354c3020019d45d16304
  | 6, 19 => 0xd5264d430300115164d4303001db354d4302001db354d4302001d943d0e3020001946cd4302001db354d4305001db54514303000195354c303001db354d430400019354d43020014d0654c302001d945d163020000000095108001db5354c3040019d538d6302001c7355153030011b354d4302001d943d0e302000005454c2030019d538d63030014e0654c302001db5354c3050005d36d4e302000005354c2040011b064d43040019160cd5302001d1354d4305001d945d16302001c3365153050009d36d0c3020019d3594e303
  | 6, 20 => 0x1d36d4e302001195354c3020019d538d6302001db354d430200119354d4305001c33651530200000354d4202001d945d163020009d36d0c3020001d4694c3020005d36d4e30200000354d4202001db5354c3040005945d163020019d538d6302001db354d430400019354d4302000595354c303000d5064d4303001c33651530200000354d420400000354d42040015b634d630200000354d4205000595354c30300119164d4302000d5064d4303000d6164d4302001db354d43040005945d1630200000354d42020019d43d0e302
  | 6, 21 => 0x1c564cd630200000354d42040014d2654c305001db3450c305000d5064d4304000db6554e3040001d36d4e302001c36554e302000dd26915304001db5451430300019464d4302000d6064d4302001d943d0e30200099164d43020011b354d4302001156454e303001db354d4302001db5354c303001db354d430200019354d430500099164d4302001db3450c302001c736515303000d546cd43040019d538d6305001db354d4302001d945d1630200019354d430500000354d42040000045d16205001db354d430200019354d4305
  | 6, 22 => 0x19354d4304000195354c30300019354d4304000d5064d43040001946d4c30200119354d4304001db354d430200019464d4302001db354d4305000195354c3040001d56cd63030011b354d4302001d1354d4302000d6064d4302001db354d4304000004550d205001db354d4304001db354d43020009d4390d305001d943d0e3030011e2690d30300019354d4302001c564cd6302001db354d430200019354d4305001d945d16302001db354d4302001db54514304000d01690d3020018b4390d303001c3354d4302001db54514302
  | 6, 23 => 0x19354d4304001db354d4304001db354d4305001db354d430400019354d4304001db5354c30300019354d4302001d943d0e30300019354d43040014d2654c302000195354c3040019d3594e304001db354d4302001db5354c3030015b064d43050000000092108000195354c305001db354d4304001190654c3030009943d0e30200019354d4304001155610d3030015b064d4303001db354d43040011b164d430200000354d420400019354d430200019354d4305000195354c303001c336515302001db354d43020009943d0e302
  | 6, 24 => 0x119354d430200019354d4302001db354d430400019354d430400119354d4304001c3354d430200119354d4302001d1354d430400019354d4302001db354d4304001db354d4304000db6554e30200019354d4302000db6554e304001d945d16302000db6554e30200019354d4302001c3354d4302
  | 7, 0 => 0x3594e2020000046cd4202000003594e205000002654c20500000644d620400000365152030000036d16205000000011510300000465162050000034915202000002654c205000005690d2020000064d4d20300000164d4204000006454e2030000060cd52020000045d162040000036115203000001651620400000000d51040000056cd6202000003450c2030000043d0e2030000045d1620200000354d42020000046cd42050000064cd620200000165162040000045d1620500000165162040000063514205000006550c205
  | 7, 1 => 0x64d420200000164d4202000002654c20500000165162020000000115103000001654c203000005650e20300000464d42040000054514205000006454e20500000064d42030000064d4d2020000045915202000004390d202000003450c20200000468d420500000545142020000000115103000004591520200000361152040000056d0f20200000648d5204000003450c2040000043d4c202000001690d20200000354d420400000354d42020000045d1620400000545142030000054514205000005690d2030000061cd5205
  | 7, 2 => 0x538d6202000003594e20300000634d62030000036d4c2020000043d0e202000005354c2030000036517202000005354c202000006590c202000005490d2020000036515204000006550c204000001690d202000002654c20400000001151030000064cd52050000045d16205000005490d20200000269152020000043d0e20200000349152020000061cd5203000005650f2020000045d162020000043d0e20300000269152040000054d0d205000004390d2030000046cd42020000061d4d2030000043d0e20200000354d4205
  | 7, 3 => 0xd41020000043d0e202000000014c103000002654c202000002691520400000000d510400000545142050000036d4c202000002691520500000464d4205000003594e2030000045d162050000036517202000002654c2040000046cd4205000002654c205000002691520200000354d420500000530d6205000002654c204000002650e202000005490d2030000046516202000002650e20500000464d42030000056cd420500000634d620300000468d42020000043d0e2020000036d172050000056d0f2030000063514202
  | 7, 4 => 0x26915204000002654c204000006454e202000002650e205000000010d1050000064d4e2030000043d0e205000003594e204000004654c203000002654c2050000061cd52050000056cd420300000164d4203000003491520200000464d42050000026516203000006550c2020000056d0e20300000530d6202000002650e20200000165162020000043d0e202000005450d205000003651620200000164d4204000006554e2050000056d142020000026516203000001654c2030000026915202000001651620200000264d4203
  | 7, 5 => 0x3450c205000003450c202000006454e2020000046516202000005354c204000000654c2030000064d4e2040000043d0e202000004390d20300000064d42050000060cd5202000006391420300000164d42040000036d17203000003594e2020000063514205000006351420200000634d6202000002654c2020000061cd5205000006454e20500000064d420500000365162020000026915202000006554e202000002654c202000005354c2050000060cd5202000004654c20200000165162020000043d0e205000003450c205
  | 7, 6 => 0x56cd4204000002650e202000006550c202000003594e2030000045d162030000026516203000004554e2030000056d142020000036d0c202000003594e202000003450c20200000354d420200000634d6202000003550c2040000061d4d2030000060cd52020000046cd420200000354d42040000043d0e2040000054514202000004654c204000001651620400000264d4203000005354c20200000164d4202000003450c205000005610d2020000034915203000003514e203000001690d204000002650e2020000036d0c202
  | 7, 7 => 0x6550c2020000000095108000004654c203000004654c2020000036d4c202000001690d204000002651620300000464d4204000004654c2050000046516202000000014c103000005650e20400000064d4205000002690d2030000036d0c20200000459152040000060cd520200000464d420400000164d42050000045d16204000004694c20200000354d4204000001690d202000005650d203000006454e2050000046cd420200000265162030000036d4c20300000064d42020000036d1620300000545142040000036915202
  | 7, 8 => 0x36d4e20500000264d42030000046cd420200000354d4202000001690d202000005650f20500000464d420400000538d6202000002654c20400000354d42040000046cd4202000003450c204000003594e20200000164d42020000043d0e202000005610d20200000354d42040000026915202000001690d2020000036d4c202000002654c202000004390d2020000016516204000005354c2030000043d0e2050000045d16204000005650d202000003450c2030000045d16204000005354c202000005354c2050000060d4d202
  | 7, 9 => 0x1690d204000002650e205000002654c20500000644d620200000361152050000036115202000002654c2040000036d162040000034d152030000063914204000006454e2030000056d0e205000004650e203000006454e20200000464d4204000001651620200000545142030000026915205000003651620200000064d420200000464d42020000064cd62020000046d4c203000005490d20200000644d620200000269152020000043d0e2050000043d0e20500000165162040000036d1720300000464d420400000464d4202
  | 7, 10 => 0x345152030000045915202000000654c203000003450c2040000043d0e20400000354d42040000054514202000005450d203000004654c20200000354d420500000064d4204000002654c202000002654c20200000354d42040000016516202000001651620200000538d62020000036d16204000005354c20300000464d4202000001690d204000003450c2050000036d4e20400000164d42050000026915202000004650e2050000026915204000006550c2050000045d162020000063914202000004390d205000004390d202
  | 7, 11 => 0x538d62020000046cd4205000002650e2050000043d0e20300000064d4203000006550c2040000045d16205000003594e20500000538d62020000056d142020000054514203000002654c20400000530d620300000165162040000054514202000002690d203000005650e20500000464d42020000045d162040000046cd42020000045d16204000004654c2050000036d0c20200000639142020000043d0e20400000269152020000054514205000001690d204000002650e202000002654c2050000000116105000002654c205
  | 7, 12 => 0x56cd420500000369152050000060d4d2020000045d1620200000464d420400000464d4205000005354c20200000545142020000056cd62020000036d162020000036d1620400000000d110800000464d42040000043d0e2050000061cd5205000001690d202000004650e203000005690d20200000064d420200000164d420200000064d42050000045d1620200000530d62050000046cd4202000004654c2040000045d1620200000064d42050000043d0e203000001690d2020000045d162020000045d162020000056cd4202
  | 7, 13 => 0x64d4d202000003491520300000464d4204000003450c203000003594e204000002654c204000005450d20300000165162040000036d4c2040000046cd42040000054514204000000654c204000004654c20500000530d6204000004650e2020000046cd42020000043d0e202000001690d20200000464d420500000269152020000036d4c202000006590c20300000464d42040000045d162030000056d0e202000003651720200000464d420200000464d420200000354d4204000005310d205000003514e202000005450d205
  | 7, 14 => 0x64d42040000000092108000005650f203000003450c202000000654c2050000045d1620400000354d4204000005690d204000002654c204000005650f2030000046cd4202000006454e20200000064d42040000036d172050000026516203000000654c2020000054514202000005690d205000002654c2020000043d0e20400000164d4202000001651620400000064d420200000464d420500000164d42020000016516202000005490d2020000036516202000005354c2020000043d0e2030000036517204000004654c203
  | 7, 15 => 0x6351420400000349152030000045915205000006454e2050000046cd420200000164d4205000002650e202000003594e2050000054514205000001690d20400000064d42040000043d0e203000005690d2020000043d0e202000005354c20300000351152030000043d0e2050000043d0e202000003594e203000001690d20400000634d620200000269152050000056d0e20200000644d5204000005354c202000005610d2050000036d4c20200000365172050000036517202000005690d204000000654c203000000014c102
  | 7, 16 => 0x634d6202000003651720400000365152050000045d16202000000010d105000005490d20500000538d6202000002651620300000634d6204000004390d205000002690d203000003594e203000005354c203000004654c20200000064d420200000164d4202000003450c203000002654c202000005650f2020000054514205000006590c204000001690d202000001690d202000006454e2020000043d0e20200000530d6202000000654c203000001651620400000365162020000036d4c20500000545142050000054514202
  | 7, 17 => 0x2654c2020000064d4d2020000056d0e2050000000116105000006550c202000005650e202000000654c2050000043d0e2020000043d0e20200000164d42020000045d162040000045d162050000036d0c205000001690d204000004654c204000006590c2020000061cd5205000002654c204000005354c20400000538d620400000354d420400000538d6204000003450c2050000056d0f2040000046516205000006550c202000005650f202000003450c2020000045d1620500000064d4204000002650e2050000056d14205
  | 7, 18 => 0x3450c20400000164d4205000000654c204000005450d204000002650e20400000345152030000060d4d2020000043d0e20400000354d420200000464d420200000538d620300000468d420500000538d6202000006550c2020000043d0e20200000538d6205000005354c20200000538d620200000165162020000043d4c205000003651520200000164d42050000045d162020000043d0e2050000043d0e205000004694c202000002654c2020000046cd420300000465162030000054514204000003594e2040000000092108
  | 7, 19 => 0x634d6203000001690d204000001690d20400000354d42030000045915205000001690d20400000064d4202000003594e2030000036915202000003450c2020000043d0e203000003551620400000000d510400000064d42050000045915203000005310d20300000354d4204000003450c204000002690d20300000064d42040000026915202000002650e20200000464d420200000538d6205000006590c20200000365172040000046516204000003594e204000005650f2040000045d16205000003551520400000634d6202
  | 7, 20 => 0x64cd52020000060cd52020000045d1620300000164d42040000043d0e2050000056cd42020000045d16202000003450c204000005650e20200000639142020000036515204000001690d2040000036d17202000001690d20200000269152050000000095108000001690d2040000043d0e20200000354d4203000000654c205000002650e202000005354c2030000045d16204000003651720200000064d420500000064d42040000046cd4203000000014c1030000036d17203000005451420400000165162020000046cd4202
  | 7, 21 => 0x5310d20400000538d62030000043d0e20500000165162020000046cd4202000003454e2050000036d4e2020000043d0e2020000056cd420200000545142040000061d4d20300000538d6205000004390d20400000354d4204000003651520200000354d420400000064d420200000354d420200000164d420200000354d420400000064d4205000006454e20200000464d4202000004654c203000000654c20300000464d42020000043d0e205000005451420500000064d420400000538d62020000064cd5204000002650e202
  | 7, 22 => 0x545142020000026915205000003594e20200000064d4202000003450c20300000164d420200000538d6204000002654c20200000361152020000016516202000002691520400000538d6202000003450c203000005451420400000644d6203000001690d20200000354d420200000064d42020000045d1620400000001151030000064cd6202000005450d205000002654c2020000036d4e204000006590c2050000045915205000004650e2050000036915204000003450c2020000056d0e20500000354d42020000054514204
  | 7, 23 => 0x1690d2020000061cd52050000064cd6202000003594e20500000464d4204000003450c202000005450d205000003594e202000003594e2020000036d172040000026915202000003514e202000002650e20500000354d42020000054514202000003450c2030000046d4c2020000064d4e205000002651620300000545142040000036d4e202000005354c2020000046d4c203000002654c204000002690d2030000045d16203000003594e204000001654c2030000064cd520200000639142030000046cd42050000054514203
  | 7, 24 => 0x46516202000004650e202000003651620400000064d420200000530d6202000003594e20500000164d420200000165162040000046d4c2020000043d0e204000002650e2020000064cd52020000043d4c20300000164d420400000464d42050000036d4c20400000464d420500000361152020000046cd420500000545142020000060cd52020000060cd5202000002650e204000000654c204000005354c202000002654c202000004650e2020000045d162020000043d0e204000004390d205000002690d2030000034915203
  | 7, 25 => 0x5451420200000345152050000061d4d2030000056d0e20200000545142050000054514205000003450c20200000164d4205000003594e204000003651620400000644d6205000005451420300000530d6204000003450c20400000459152020000064d4e20500000634d6204000004650e20300000464d4202000006550c2050000054514202000005450d204000002654c205000001690d2020000060cd520200000354d4205000003450c205000005650d2020000054514202000004654c202000002654c20400000464d4202
  | 7, 26 => 0x36d1620500000464d420500000000921080000064cd6205000005490d202000005451420400000064d420200000164d420200000530d6202000003651520200000164d42050000056d0e20200000064d42040000026915202000003450c20200000164d4204000003450c2020000056d142030000046cd420500000064d42050000016516202000002690d203000005690d20300000000d1108000005451420400000464d42040000060cd520200000064d420200000464d420400000164d420200000164d42040000045915205
  | 7, 27 => 0x4650e202000005650e205000000014d104000004390d20500000538d62040000026516203000005490d2030000026915205000002691520400000354d4202000000654c2030000026516203000003651520500000464d420500000365172040000000092108000004654c2030000026915202000006554e204000004654c20200000064d4202000001690d20200000354d420200000164d4202000006554e202000005690d2020000016516202000002654c2040000046cd420400000468d420200000464d42020000043d4c204
  | 7, 28 => 0xd1108000005490d2020000056d0f202000006554e2020000046cd4205000000010d105000006454e2040000036d0c204000002654c20200000468d42020000046cd42050000036d17205000002654c2040000046cd42020000061d4d20300000064d420200000464d4205000002654c2050000043d0e20200000545142040000026915202000004591520500000545142050000046cd420300000538d6204000005450d20200000369152020000054514205000001690d2020000060cd520200000365152050000045d16202
  | 7, 29 => 0x36d17202000005650e203000006590c2020000061cd5203000003450c2040000036d16202000000014c1030000046d4c2040000043d0e2030000064cd520500000538d620500000365172030000036d16202000003451520200000464d42040000064d4e202000004654c202000006590c202000001690d20400000165162020000060cd5202000006554e203000003594e202000006351420500000064d4202000004654c2040000046d4c202000005354c20200000000d410500000634d6204000006590c2040000054514202
  | 7, 30 => 0x164d42030000054514204000002650e202000005650d203000002650e20200000365152040000016516204000003594e2020000064cd62020000046d4c202000003594e20200000538d62030000046cd42040000054514204000002650e20200000354d42020000046d4c20500000354d4202000003594e202000006454e20300000365152020000046cd420400000269152020000045d16204000003651620300000349152050000064d4e203000005650d203000002654c20400000064d420400000354d4205000002654c205
  | 7, 31 => 0x5650f20500000064d42050000045d1620200000464d420400000000d410400000464d42050000036517202000002650e20200000365152020000060cd5202000004654c20300000464d42040000043d0e205000005650d202000001690d204000005650e203000002654c20200000644d620300000064d42040000036d0c2030000046cd420200000354d42020000060cd5202000002654c2050000061cd52030000045915202000003594e2020000045d16204000006554e204000002690d2030000056d0f2020000046cd4204
  | 7, 32 => 0x2654c20200000349152040000036115202000004694c203000002690d203000001690d2020000036d4c204000002654c20400000545142040000043d0e202000006454e202000003450c2020000054514202000001690d2040000056d0e2020000046d4c2050000060cd52020000034915203000003594e204000000654c203000000010d10500000634d6204000004650e205000005350e20300000164d420300000264d420300000349152050000036d0c20300000545142020000036d4e2040000036d162040000054514202
  | 7, 33 => 0x46cd42020000064d4e20300000164d4205000005610d2050000054514202000002650e202000006554e2040000036d172040000046cd4204000000654c2040000046cd420500000354d42020000056d0e2020000064cd52020000045915202000003450c20500000354d42040000034915204000003611520200000354d4204000003651520400000354d42040000060d4d2020000045d16202000005451420300000635142020000046d4c20400000545142020000026915202000003594e20200000164d42020000064cd6202
  | 7, 34 => 0x538d6202000005354c2030000046cd4205000000011610500000464d4204000005451420300000465162020000046cd4204000003450c2040000036115204000002654c2040000064d4e204000003691520500000354d42020000045d16202000003594e20500000354d42020000045915203000004654c20200000530d6204000003594e2050000043d0e202000000654c2020000064cd52040000060d4d202000002650e2050000026915202000002650e20500000264d42030000061cd520500000064d42040000045915202
  | 7, 35 => 0x164d42020000043d0e204000003450c205000003651620200000000921080000056d14202000005354c20200000000d41050000056d1420200000464d420200000464d4202000002650e204000001690d202000002654c20400000644d5205000006590c202000005354c2050000046516202000005690d202000000654c2020000043d0e2050000054514203000005610d203000005650f20200000538d620400000164d42050000046516204000003451520200000365172050000060cd5202000002691520400000538d6203
  | 7, 36 => 0x54514204000001690d20200000465162030000061cd520500000464d42050000046d4c20400000000d41040000036d0c205000006554e204000000014c103000003651520400000269152050000061cd5203000002690d203000003594e20400000354d4205000005490d20200000000d610800000064d4204000006590c20200000064d4205000006590c204000000654c2030000043d0e2040000064cd52040000056d0f204000001690d20200000538d620400000354d42020000064d4d203000005490d202000004654c203
  | 7, 37 => 0x2654c20500000464d420200000164d42050000046cd42020000045d1620500000000d110800000634d6203000002654c202000003450c20500000164d4205000002650e20400000354d4202000006554e202000003450c20200000164d4203000006554e202000002690d20300000464d4202000001690d20200000354d4202000000010e103000005650e20300000640d52040000043d0e203000006554e20200000538d620500000164d42020000000116105000004650e20500000354d420400000468d42040000036915202
  | 7, 38 => 0x2654c2020000036d4c20200000464d42040000036d4e20500000365172020000036d172030000061d4d203000002650e202000003594e2020000000116105000000014c10200000644d6202000003594e20500000164d420500000634d6202000001690d2020000056d1420400000000d5104000005490d202000001690d204000000010e1030000064cd620200000354d4205000000654c20200000648d5204000002650e20400000545142040000046d4c203000001690d20400000468d420200000264d4203000003450c202
  | 7, 39 => 0x54514205000002650e20200000164d4202000006454e202000005650e20500000264d42030000036d172020000026516203000006554e2020000056d0f2020000026915205000006554e2020000043d0e2030000064cd62020000061cd5205000005354c203000005354c20300000464d420500000464d4202000005490d20400000351152020000043d0e2040000054514202000002654c2020000046cd4202000003651520200000064d42040000043d0e202000005451420200000464d42020000046cd420200000164d4204
  | 7, 40 => 0x46cd4204000005354c2040000056d0f202000002691520200000000d1108000002650e20200000354d42030000036d152030000061d4d205000002650e2040000036517203000005690d202000002690d20300000464d42020000036d4e202000002650e2020000045d16202000002690d203000005451420300000165162020000054514202000000654c203000003651520300000464d420200000354d4202000005451420400000164d42020000061cd52050000036d0c205000006590c20300000064d420400000064d4204
  | 7, 41 => 0x164d420500000530d6202000004650e2030000045d1620400000354d42020000046cd420400000538d620400000635142030000060cd52020000060cd520200000354d4203000002650e2050000046cd4202000005610d2020000046516202000002650e2020000064cd6205000006590c205000005690d202000001654c205000001651620200000464d420500000465162040000046cd420500000354d4202000002650e20400000365162020000036d17203000001651620200000538d620200000164d420200000064d4202
  | 7, 42 => 0x3450c202000002690d20300000468d42040000056d142050000054d0e20300000354d4205000002650e2040000056d0d20500000064d4202000003451520200000064d42040000046d4c202000003450c2020000036915202000002654c2050000043d0e20300000639142050000046cd420200000000d6108000001690d2020000046cd420200000064d420200000064d4202000005354c20200000464d420200000545142020000046cd420500000354d4202000003691520300000545142020000060cd520200000538d6203
  | 7, 43 => 0x2654c205000005650e2020000064d4d20200000164d4202000004654c20300000000d6108000005354c202000002650e205000006454e2040000046cd4204000005650e20200000354d4205000005450d20200000635142050000046d4c204000003491520500000545142020000043d0e20200000269152050000036515202000004654c20200000269152050000043d4d20400000464d42020000034915203000002650e204000003594e202000006590c203000005354c202000003450c20200000354d4204000005450d203
  | 7, 44 => 0x60cd52020000061d4d2030000046d4c203000002650e202000005490d2050000046cd42040000036d4e2020000036517204000000014c1030000045d1620500000064d420200000468d4204000005451420300000354d42040000036d4c20300000464d4202000002650e204000003594e202000002650e202000006351420400000644d5202000002650e2020000046cd4204000005690d205000000014c10400000164d420200000465162030000060cd520200000464d42020000045d16202000001690d2040000036515202
  | 7, 45 => 0x354d42040000043d0e20300000000d51040000043d0e202000004594e205000005451420500000464d4202000001651620400000000d4102000005354c2040000045d16204000003651620400000538d620200000464d42040000060d4d202000006454e20200000064d4202000000010e103000001654c203000005451420300000545142030000045d16204000006454e20400000354d4205000003651720200000545142030000043d0e205000005650e2020000046cd4204000003594e20200000355152030000036d0c202
  | 7, 46 => 0x164d42050000046cd42020000056d14205000000654c203000005354c205000006554e202000005450d20500000464d42020000061cd520500000064d420200000064d4202000005490d2030000060cd5202000006554e20200000354d420500000000d41020000046cd4204000004650e204000002654c202000005690d204000006554e20400000354d42040000060cd5202000005354c20300000464d4202000001690d20200000354d420400000064d4202000001690d2020000060cd520200000530d62020000054514202
  | 7, 47 => 0x43d0e202000002650e2040000061d4d2030000064cd6202000001690d2020000043d0e205000003651520400000644d52040000036d17202000006454e20300000634d620300000064d4202000003594e2020000046cd420500000064d420400000634d62050000036d1620200000354d4202000006554e20200000464d4202000006554e20200000530d620200000365162050000036d1720200000354d4204000003450c202000002654c202000006554e20400000464d42020000026516203000005354c20400000464d4204
  | 7, 48 => 0x46cd420200000464d42020000045d1620500000354d420200000464d4202000003651520200000000d1108000003451520200000354d420400000464d42030000036d0c20200000354d4202000004651620200000064d420400000064d4204000002650e20200000000d410400000164d42050000043d0e205000001654c2030000046cd420200000538d6203000000654c20300000000d4102000003594e204000006454e2030000061cd52050000046cd420200000349152040000046cd4204000003450c205000006550c202
  | 7, 49 => 0x464d420200000464d42050000046cd420200000464d42040000034515202000003594e202000003594e20400000468d420200000064d42020000060cd52020000034515202
  | 8, 0 => 0x114104000000010f105000000011710200000000d41050000000117104000000010d102000000010c104000000011610400000001151040000000115104000000014e1020000000114104000000010d104000000014e10400000000d610200000000d6105000000010f10400000001151050000000115104000000010d102000000014e103000000014e10200000000d510500000000d5104000000014c102000000010d105000000014e105000000010d1050000000117104000000014c103000000010e105000000014e104
  | 8, 1 => 0x11710300000000d6103000000014e105000000014e105000000011710300000000d5104000000010c1050000000115102000000010e103000000010e10200000000d6105000000014d103000000010f104000000010f1030000000115102000000010e105000000014d103000000014e10200000000d6103000000014d102000000010f102000000014c105000000010e1040000000116104000000010c104000000010e1030000000116104000000010e104000000014c102000000010c1020000000114104000000010d104
  | 8, 2 => 0xd4103000000010f1020000000117102000000011410200000000d61020000000116105000000014d1020000000115102000000014e1040000000115103000000010e102000000011510200000001171020000000116104000000010f1040000000114104000000014e104000000014e1020000000114102000000010d102000000014d10200000000d4104000000011510400000000d610300000000d6104000000014e104000000010e10200000000d51050000000116102000000014e1030000000114102000000014e102
  | 8, 3 => 0x10f102000000014d103000000014e1020000000117102000000010e104000000010f1040000000115102000000014c103000000010e102000000010e105000000010e1050000000116102000000014e105000000010f10200000000d4105000000014e103000000014e102000000014e10200000000d6104000000011710500000001161020000000116103000000010f105000000010f1020000000116102000000010e10200000000d61030000000114102000000010e102000000010c10500000001141030000000114103
  | 8, 4 => 0x10d10300000000d5102000000010d102000000014c103000000014c10200000000d5104000000010e10500000000d4104000000014c105000000010e105000000010d105000000011610400000000d41040000000114104000000010e102000000010e102000000010d1030000000115104000000010c102000000010e104000000014c104000000014d104000000011410300000000d510400000000d41050000000117102000000010c1030000000115103000000010d103000000014e10500000000d6102000000014e102
  | 8, 5 => 0xd510400000001161050000000114105000000014c102000000010c103000000010d1030000000116105000000010f103000000011510500000000d5103000000011610200000000d61050000000117102000000014d103000000014e104000000010c105000000010d10200000000d6102000000014e104000000014e10400000000d6105000000010d102000000010f1020000000116102000000010e1050000000114102000000014e104000000010e10200000000d4104000000010c10200000001141020000000115102
  | 8, 6 => 0x117102000000011710400000000d5105000000014c104000000014e1040000000116105000000010e104000000010e10400000000d510200000001141050000000117102000000011510400000000d6104000000014e104000000014e105000000010f10300000001161030000000116102000000010d1020000000115105000000010e104000000011410300000000d510200000001141020000000117105000000014e102000000014c105000000010c103000000011510300000000d610500000001151020000000116104
  | 8, 7 => 0x14c1030000000115102000000010f102000000011610300000001161040000000116102000000014e105000000014c10500000000d51020000000114102000000011510300000000d4105000000010f103000000011610400000000d61050000000115104000000010d10500000000d410200000000d4102000000010c102000000010c10400000000d5102000000014e102000000014e10300000000d61030000000115104000000014e102000000010d10200000000d4105000000010f103000000010d10500000000d4104
  | 8, 8 => 0x10f10200000000d6103000000010c102000000011710500000000d6102000000011610300000000d61050000000115103000000010f102000000010c103000000014e1040000000117104000000010e102000000010e105000000010f105000000011410400000000d6104000000010d104000000010f1050000000116105000000011710200000001141050000000115105000000010c1030000000115104000000010f102000000010c103000000010e1040000000116105000000011510500000000d4105000000010c102
  | 8, 9 => 0xd61040000000114102000000010d105000000014e103000000014e10200000000d410200000000d61020000000115102000000014d102000000010d104000000014e10500000000d6102000000010f105000000010d104000000010e104000000010f102000000010c102000000010c104000000010f10500000000d6103000000014c104000000010e103000000010c1050000000116105000000011510500000000d610200000001151040000000117103000000014e102000000010c1020000000115105000000014d102
  | 8, 10 => 0x10d10500000000d6105000000014e104000000011510300000000d5102000000010d102000000010f105000000010e103000000010e102000000014e104000000011410200000000d610500000000d6105000000010f1030000000115102000000014e10400000000d6102000000011610200000000d4102000000014c103000000011410200000000d41020000000115105000000010d102000000010f1040000000117103000000014e10500000000d4104000000010d105000000010d103000000010d1020000000117102
  | 8, 11 => 0x10f1050000000115104000000010d1020000000115103000000010f104000000010e1020000000114104000000010d1040000000116103000000010e10400000000d4104000000010f104000000010c103000000010c10200000000d61020000000115104000000010f1040000000116103000000014e10400000001141030000000117102000000010d10300000000d6104000000010d104000000010c10400000001151030000000117105000000014e10500000001161030000000115102000000010d102000000010d105
  | 8, 12 => 0x14c103000000014c102000000014d1030000000114103000000010e1040000000114103000000010c1020000000114105000000011710200000000d410500000000d51020000000116102000000010e104000000010e1040000000117104000000011410300000000d4104000000010d105000000010d1020000000116102000000010e105000000010f102000000011510400000000d5104000000010f104000000014e10500000000d5104000000010d105000000010d105000000011510200000000d4102000000010c102
  | 8, 13 => 0x116102000000010c10400000000d5104000000010e10200000000d4104000000010f102000000010f10200000000d5105000000014c10200000001151020000000114103000000014c10400000001141050000000117103000000010f10400000000d61020000000114102000000014e102000000010f1030000000115105000000010d104000000010f10400000001161020000000114105000000010c104000000010d1040000000115103000000010f1040000000115102000000010f102000000010f105000000010f105
  | 8, 14 => 0x10f10400000000d4104000000014e102000000014e10400000000d4105000000014c103000000010f103000000014e104000000010c103000000010e1030000000117102000000010d10500000000d610400000000d5102000000010d104000000010e103000000010c102000000010e10200000000d4104000000014e103000000010f1040000000116104000000011710200000000d6103000000010f10300000000d51020000000114102000000014e10300000000d5104000000014e1040000000115102000000010e103
  | 8, 15 => 0x10e10300000000d4104000000010f102000000014c1020000000116102000000010f10400000001171030000000116102000000014e10200000000d51030000000115102000000011610200000001141020000000115104000000010c102000000010f10200000000d5102000000010c10400000000d610300000000d6102000000011510200000001141020000000117105000000010c10500000000d6105000000010d103000000014d10300000000d5104000000010f104000000010f104000000010e10300000000d5102
  | 8, 16 => 0xd410500000000d610200000000d4102000000010f102000000014d102000000010d102000000010c1030000000116104000000014e102000000014d1030000000115105000000010e10200000000d5102000000010f10300000000d51020000000116102000000014c103000000011710300000000d610500000000d5102000000010d10500000001151020000000115103000000010e10500000000d5104000000010f10500000000d5103000000014e10200000000d6102000000010e103000000010f102000000010f103
  | 8, 17 => 0x10e102000000010f104000000011510200000000d4102000000010c10200000000d5103000000010c10300000001151040000000117105000000010d10300000000d610200000000d510400000000d4102000000010f105000000010c102000000011410300000000d4104000000010e10500000000d41020000000114102000000010e105000000010f105000000010c103000000014d102000000010c105000000010d10500000000d51050000000116104000000011710200000001171050000000115104000000014e102
  | 8, 18 => 0x10d104000000014e1030000000116103000000010c10400000000d5105000000014e10400000000d410200000000d5104000000010f104000000010c104000000010f105000000014d10300000000d510400000001161050000000117105000000014d1040000000116102000000010c105000000010f1040000000116104000000010c1020000000117102000000010c10500000000d6103000000010c104000000010d103000000014e102000000010d10200000001141050000000115102000000011710400000000d5105
  | 8, 19 => 0x10c1050000000116102000000010f104000000010d102000000014e102000000010f102000000014e104000000011610300000000d4102000000010f103000000010c102000000010e1030000000115102000000010d10300000000d5102000000010d103000000010f102000000010e10200000000d410200000000d410200000000d5104000000010c104000000014d1040000000114103000000010f105000000010c104000000014e103000000014d1050000000115103000000014c102000000010d102000000010c102
  | 8, 20 => 0xd4102000000010e10300000000d41040000000114105000000010c104000000010c10400000000d510200000000d4102000000014d10300000000d510200000000d5104000000011710300000001171020000000116105000000010d10300000000d5102000000011610500000000d410200000000d61020000000116105000000010c10200000000d510200000000d4102000000014d104000000010c104000000010d10400000000d4104000000010f104000000010c104000000010e105000000010c102000000010c105
  | 8, 21 => 0x10f10500000000d4102000000014d103000000011510500000000d5104000000010c104000000010e102000000011510200000000d5105000000011610200000000d5102000000010c10400000000d51020000000116104
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_204 roots_204 4 s ws hint
  | 1 => checkCutEntry true dom_206 roots_206 5 s ws hint
  | 2 => checkCutEntry true dom_238 roots_238 9 s ws hint
  | 3 => checkCutEntry true dom_231 roots_231 9 s ws hint
  | 4 => checkCutEntry true dom_237 roots_237 9 s ws hint
  | 5 => checkCutEntry true dom_235 roots_235 9 s ws hint
  | 6 => checkCutEntry true dom_207 roots_207 6 s ws hint
  | 7 => checkCutEntry true dom_205 roots_205 5 s ws hint
  | 8 => checkCutEntry true dom_175 roots_175 7 s ws hint
  | 9 => checkCutEntry true dom_203 roots_203 5 s ws hint
  | 10 => checkCutEntry true dom_111 roots_111 6 s ws hint
  | 11 => checkCutEntry true dom_167 roots_167 6 s ws hint
  | 12 => checkCutEntry true dom_199 roots_199 5 s ws hint
  | 13 => checkCutEntry true dom_107 roots_107 5 s ws hint
  | 14 => checkCutEntry true dom_171 roots_171 6 s ws hint
  | 15 => checkCutEntry true dom_173 roots_173 6 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_239 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_204 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_206 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_238 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_231 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_237 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_235 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_207 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_205 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_175 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_111 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_167 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_199 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_107 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_171 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_173 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_239 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_239 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_239 == dom_239) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_239 goalM v ys) : RunD true dom_239 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_239 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 78 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 78 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 128 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 188 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 60 128 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 188 → Z 6 i = true := (range_split z6_0 z6_128)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 128 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 217 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 89 128 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 217 → Z 7 i = true := (range_split z7_0 z7_128)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 81 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 81 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 7 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 7 0 = true)
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
  scr true dom_239 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_239 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_239 roots_239 goal_239 11 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_239 goal_239 := by
    have h0 : isConstB dom_239 goal_239 = false := by decide +kernel
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

end S_239

theorem lowS_239 : Lower true dom_239 roots_239 goal_239 11 := S_239.noCircuit

theorem lowS_255 : Lower true dom_255 roots_255 goal_255 12 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 1, 17)] (by decide +kernel) (by decide +kernel) lowS_239

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.or, inputs := [9, 7] }, { op := GateOp.and, inputs := [8, 10] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [12, 3] }, { op := GateOp.and, inputs := [6, 13] }, { op := GateOp.or, inputs := [2, 7] }, { op := GateOp.and, inputs := [5, 15] }, { op := GateOp.and, inputs := [3, 7] }, { op := GateOp.or, inputs := [11, 14] }, { op := GateOp.or, inputs := [18, 16] }, { op := GateOp.or, inputs := [19, 17] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 20⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  decide +kernel

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_15018_aux

theorem PEqualNP.Outside.L_meta_15018 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_15018_aux.main
