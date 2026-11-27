import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14306_aux

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

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000fafafafaaaaa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefafaeeee0000fefefafaeeee0000fefefafaeeee0000fefefafaeeee0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfcfcfcfcfcfcfcfccccc0000cccc0000fcfcfcfcfcfcfcfccccc0000cccc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfefefcfcfefefcfceeee0000eeee0000fefefcfcfefefcfceeee0000eeee0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffccffccffccffcccccc0000cccc0000ffccffccffccffcccccc0000cccc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffeeffccffeeffcceeee0000eeee0000ffeeffccffeeffcceeee0000eeee0000
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_94 : Nat := 0x555555550000000055555555
def goal_94 : Nat := 0xfffcfffcfffcfffccccc0000cccc0000fffcfffcfffcfffccccc0000cccc0000
def roots_94 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffefffcfffefffceeee0000eeee0000fffefffcfffefffceeee0000eeee0000
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_102 : Nat := 0x55000000550000005500000055
def goal_102 : Nat := 0xfcfcfcfcfcfcfcfcf0f0f0f000000000fcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_102 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_103 : Nat := 0xff000000ff000000ff000000ff
def goal_103 : Nat := 0xfefefefefcfcfcfcfafafafa00000000fefefefefcfcfcfcfafafafa00000000
def roots_103 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_110 : Nat := 0x5555000055550000555500005555
def goal_110 : Nat := 0xfffcfffcfffcfffcf0f0f0f000000000fffcfffcfffcfffcf0f0f0f000000000
def roots_110 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_111 : Nat := 0xffff0000ffff0000ffff0000ffff
def goal_111 : Nat := 0xfffefffefffcfffcfafafafa00000000fffefffefffcfffcfafafafa00000000
def roots_111 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xeeeeeeeeeeeecccceeeeaaaaeeee0000eeeeeeeeeeeecccceeeeaaaaeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfafafafafafaf0f0fafafafaaaaa0000fafafafafafaf0f0fafafafaaaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfcfcfcfcfcfcfcfcfcfcf0f0cccc0000fcfcfcfcfcfcfcfcfcfcf0f0cccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfefefefefefefcfcfefefafaeeee0000fefefefefefefcfcfefefafaeeee0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffeeffeeffeeffcceeeeaaaaeeee0000ffeeffeeffeeffcceeeeaaaaeeee0000
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffcfffcfffcfffcfcfcf0f0cccc0000fffcfffcfffcfffcfcfcf0f0cccc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffefffefffefffcfefefafaeeee0000fffefffefffefffcfefefafaeeee0000
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffccffccffccffccffccffccffccffcccccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeeeee0000eeee0000eeee0000eeee0000
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def goal_161 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeaaaaaaaa00000000aaaaaaaa00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaafafafafa00000000fafafafa00000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeefafafafa00000000fafafafa00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaaaaaaaaa00000000aaaaaaaa00000000
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeaaaaaaaa00000000aaaaaaaa00000000
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xffffffffff00ff00ffffffffff00ff00f0f0f0f000000000f0f0f0f000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xffffffffffaaffaaffffffffffaaffaafafafafa00000000fafafafa00000000
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xffffffffffccffccffffffffffccffccf0f0f0f000000000f0f0f0f000000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xffffffffffeeffeeffffffffffeeffeefafafafa00000000fafafafa00000000
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffccccccccffffffffcccccccccccc0000cccc0000cccc0000cccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaafafafafaaaaa0000fafafafaaaaa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffaaffaaffffffffffaaffaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffccffccffffffffffccffcccccc0000cccc0000cccc0000cccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffeeffeeffffffffffeeffeeeeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xffffffffffaaffaaffffffffffaaffaafafafafaaaaa0000fafafafaaaaa0000
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xffffffffffccffccffffffffffccffccfcfcf0f0cccc0000fcfcf0f0cccc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xffffffffffeeffeeffffffffffeeffeefefefafaeeee0000fefefafaeeee0000
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeecccccccccccccccc0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_198 : Nat := 0x55000000000000005500000000000000550000000000000055
def goal_198 : Nat := 0xfcfcfcfcfcfcfcfcccccccccccccccccfcfcfcfcfcfcfcfc0000000000000000
def roots_198 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_199 : Nat := 0xff00000000000000ff00000000000000ff00000000000000ff
def goal_199 : Nat := 0xfefefefefefefefeeeeeeeeeeeeeeeeefcfcfcfcfcfcfcfc0000000000000000
def roots_199 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffccffccffccffcc0000000000000000
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_204 : Nat := 0x1111000000000000111100000000000011110000000000001111
def goal_204 : Nat := 0xfff0fff0fff0fff0ff00ff00ff00ff00fff0fff0fff0fff00000000000000000
def roots_204 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_206 : Nat := 0x5555000000000000555500000000000055550000000000005555
def goal_206 : Nat := 0xfffcfffcfffcfffcffccffccffccffccfffcfffcfffcfffc0000000000000000
def roots_206 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_207 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def goal_207 : Nat := 0xfffefffefffefffeffeeffeeffeeffeefffcfffcfffcfffc0000000000000000
def roots_207 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeecccceeeecccceeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfcfcfcfcfcfcfcfcccccccccccccccccfcfcfcfcfcfcfcfccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfefefefefefefefeeeeeeeeeeeeeeeeefefefcfcfefefcfceeee0000eeee0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaff00ffaaff00aaaa0000aaaa0000
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffccffccffccffccffccffccffccffccffccffccffccffcccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffccffeeffcceeee0000eeee0000
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffafffafffafffaffaaffaaffaaffaafffafff0fffafff0aaaa0000aaaa0000
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffcfffcfffcfffcffccffccffccffccfffcfffcfffcfffccccc0000cccc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffefffefffefffeffeeffeeffeeffeefffefffcfffefffceeee0000eeee0000
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_226 : Nat := 0x500000005000000050000000500000005000000050000000500000005
def goal_226 : Nat := 0xffffffffccccccccffffffffcccccccccccccccccccccccc0000000000000000
def roots_226 : List Nat := [xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeccccccccaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_228 : Nat := 0x1100000011000000110000001100000011000000110000001100000011
def goal_228 : Nat := 0xfffffffff0f0f0f0ffffffff00000000f0f0f0f0f0f0f0f0f0f0f0f000000000
def roots_228 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_229 : Nat := 0x3300000033000000330000003300000033000000330000003300000033
def goal_229 : Nat := 0xfffffffffafafafaffffffffaaaaaaaafafafafaf0f0f0f0fafafafa00000000
def roots_229 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcffffffffccccccccfcfcfcfcfcfcfcfcf0f0f0f000000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefeffffffffeeeeeeeefefefefefcfcfcfcfafafafa00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaff00ff00aaaaaaaa00000000
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffffccffccffccffccffccffcc0000000000000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeffccffccaaaaaaaa00000000
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_236 : Nat := 0x111100001111000011110000111100001111000011110000111100001111
def goal_236 : Nat := 0xfffffffffff0fff0ffffffffff00ff00fff0fff0fff0fff0f0f0f0f000000000
def roots_236 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffaffffffffffaaffaafffafffafff0fff0fafafafa00000000
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcffffffffffccffccfffcfffcfffcfffcf0f0f0f000000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffeffffffffffeeffeefffefffefffcfffcfafafafa00000000
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeecccceeeeaaaaeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffafafafaffffffffaaaaaaaafafafafafafaf0f0fafafafaaaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffcfcfcfcffffffffccccccccfcfcfcfcfcfcfcfcfcfcf0f0cccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffefefefeffffffffeeeeeeeefefefefefefefcfcfefefafaeeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaffaaff00aaaaaaaaaaaa0000
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffccffccffffffffffccffccffccffccffccffcccccc0000cccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeffeeffcceeeeaaaaeeee0000
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffafffaffffffffffaaffaafffafffafffafff0fafafafaaaaa0000
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffcfffcffffffffffccffccfffcfffcfffcfffcfcfcf0f0cccc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffefffeffffffffffeeffeefffefffefffefffcfefefafaeeee0000
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

namespace S_51
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (2, 18), (3, 19), (3, 35), (16, 17), (16, 18), (32, 33), (34, 35), (34, 50), (48, 49), (48, 50)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 16, 16, 32, 34, 34, 48, 48]
def r2sG : List Nat := [17, 33, 18, 19, 35, 17, 18, 33, 35, 50, 49, 50]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_51.map (· &&& dom_51)
def goalM : Nat := goal_51 &&& dom_51
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x29c5ac2a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f00000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000a000a000a000a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf80c6031c01b
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf92e6db5c5bb
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
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_51 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_51 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_51 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_51 == dom_51) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_51 goalM v ys) : RunD true dom_51 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_51 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_51 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_51 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_51 roots_51 goal_51 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_51 goal_51 := by
    have h0 : isConstB dom_51 goal_51 = false := by decide +kernel
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

end S_51

theorem lowS_51 : Lower true dom_51 roots_51 goal_51 4 := S_51.noCircuit

theorem lowS_163 : Lower true dom_163 roots_163 goal_163 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0000000c00000000000000000000000c0000000c, 128, 130)] (by decide +kernel) (by decide +kernel) lowS_161

def isoMvS_53 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_53 : Lower true dom_53 roots_53 goal_53 4 :=
  lower_iso isoMvS_53 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_86 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_86 : Lower true dom_86 roots_86 goal_86 4 :=
  lower_iso isoMvS_86 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_90 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_90 : Lower true dom_90 roots_90 goal_90 4 :=
  lower_iso isoMvS_90 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_102 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_102 : Lower true dom_102 roots_102 goal_102 4 :=
  lower_iso isoMvS_102 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_153 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_153 : Lower true dom_153 roots_153 goal_153 4 :=
  lower_iso isoMvS_153 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_154 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_154 : Lower true dom_154 roots_154 goal_154 4 :=
  lower_iso isoMvS_154 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_165 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_165 : Lower true dom_165 roots_165 goal_165 5 :=
  lower_iso isoMvS_165 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_163

def isoMvS_169 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_169 : Lower true dom_169 roots_169 goal_169 5 :=
  lower_iso isoMvS_169 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_163

def isoMvS_172 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_172 : Lower true dom_172 roots_172 goal_172 4 :=
  lower_iso isoMvS_172 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_177 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]
theorem lowS_177 : Lower true dom_177 roots_177 goal_177 5 :=
  lower_iso isoMvS_177 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_163

def isoMvS_178 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_178 : Lower true dom_178 roots_178 goal_178 4 :=
  lower_iso isoMvS_178 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_195 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_195 : Lower true dom_195 roots_195 goal_195 4 :=
  lower_iso isoMvS_195 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_198 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_198 : Lower true dom_198 roots_198 goal_198 4 :=
  lower_iso isoMvS_198 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_204 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_204 : Lower true dom_204 roots_204 goal_204 4 :=
  lower_iso isoMvS_204 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_226 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_226 : Lower true dom_226 roots_226 goal_226 4 :=
  lower_iso isoMvS_226 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_228 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_228 : Lower true dom_228 roots_228 goal_228 4 :=
  lower_iso isoMvS_228 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

theorem lowS_55 : Lower true dom_55 roots_55 goal_55 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc, 16, 18)] (by decide +kernel) (by decide +kernel) lowS_53

theorem lowS_94 : Lower true dom_94 roots_94 goal_94 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x505050500000000050505050, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_90

theorem lowS_155 : Lower true dom_155 roots_155 goal_155 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a0000000000000000000000000a0a0a0a, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_154

theorem lowS_167 : Lower true dom_167 roots_167 goal_167 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc000000cc0000000000000000000000cc000000cc, 128, 130)] (by decide +kernel) (by decide +kernel) lowS_165

theorem lowS_171 : Lower true dom_171 roots_171 goal_171 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c000000000000000000000c0c00000c0c, 128, 130)] (by decide +kernel) (by decide +kernel) lowS_169

theorem lowS_179 : Lower true dom_179 roots_179 goal_179 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c000c000c0000000000000000000c000c000c000c, 16, 18)] (by decide +kernel) (by decide +kernel) lowS_177

namespace S_227
def pairsG : List (Nat × Nat) := [(1, 33), (1, 129), (2, 66), (2, 130), (3, 35), (3, 67), (3, 131), (32, 33), (32, 160), (34, 35), (34, 98), (34, 162), (64, 66), (65, 67), (65, 97), (65, 193), (96, 97), (96, 98), (96, 224), (128, 129), (128, 130), (128, 160), (192, 193), (192, 194), (192, 224)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 32, 32, 34, 34, 34, 64, 65, 65, 65, 96, 96, 96, 128, 128, 128, 192, 192, 192]
def r2sG : List Nat := [33, 129, 66, 130, 35, 67, 131, 33, 160, 35, 98, 162, 66, 67, 97, 193, 97, 98, 224, 129, 130, 160, 193, 194, 224]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_227.map (· &&& dom_227)
def goalM : Nat := goal_227 &&& dom_227
def NN : Nat → Nat
  | 4 => 3
  | 5 => 4
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xb94a154d22428fc121eb7330
  | 5, 0 => 0xd2281af15acbf82b4c6fede92064c2f2
  | 6, 0 => 0xd453940d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x300000003000000030000000300000003000000030000000000000000000000000000000f000000000000000f000000000000000a000000000000000a0000000f0000000f00000000000000000000000f0000000f00000000000000000000000f000000000000000f000000000000000f000000000000000f000000000000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000a0000000a0000000a0000000a0000000a0000000a0000000a0000000a0000000f0000000f000000000000000f0000000f0000000f00000000000000000000000f0000000f0000000f0000000f00000000000000000000000000000000
  | 0, 1 => 0xf0000000a0000000f0000000a0000000f0000000a0000000f0000000a000000000000000f000000000000000f000000000000000000000000000000000000000f0000000f0000000f0000000f0000000a0000000a0000000a0000000a0000000f0000000f0000000f0000000f0000000f0000000f0000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x428705326505432105
  | 5, 0, 0 => 0x432805b43250643250a64392506
  | 6, 0, 0 => 0x432505
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfff8007e381cf8fe000070f8000073e00381cfffe001f80000
  | 0, 1 => 0x3f7f9fe00003f1c0e7fff000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xb6e08136281ab8fe849274f91491f3e1278bcfbfe8ddfc894a
  | 0, 1 => 0xb7f7f9b62012bfbd7f7fffd6e
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
  | 3, 0 => 0x3cb0b6133412e8f3
  | 4, 0 => 0xe68f47c3dce9651dd453940dcd57dbd4bba21373b37c030ba28826349da6630f523c68c43cb0b6132f7106fb16c095cb136b67060f7212b4
  | 5, 0 => 0xed2eadebe9635a09db7b11c7d453940dcccb3bd5c3d986e9c1c33291bac8c352b3f45bbbaafeb602956d64d59011177c8e3786117e3225bd7bcae0017ad91fbc75d8e23a717b9a95701775345ffe66875e23b16055355eb6310c78c02f7106fb2bda5585199f69db19194cd40b2c8a8c
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 3, 0 => 0x0
  | 4, 0 => 0x10003000201000001010202
  | 5, 0 => 0x10101030101010003010000010001030203010101000101030100
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
  | 0 => checkCutEntry true dom_161 roots_161 4 s ws hint
  | 1 => checkCutEntry true dom_163 roots_163 5 s ws hint
  | 2 => checkCutEntry true dom_195 roots_195 4 s ws hint
  | 3 => checkCutEntry true dom_226 roots_226 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_227 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_161 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_163 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_195 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_226 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_227 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_227 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
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

namespace S_230
def pairsG : List (Nat × Nat) := [(2, 66), (2, 130), (4, 36), (4, 68), (6, 38), (6, 70), (6, 134), (32, 36), (32, 160), (34, 38), (34, 98), (34, 162), (64, 66), (64, 68), (96, 98), (96, 100), (96, 224), (128, 130), (128, 160), (132, 134), (132, 164), (132, 196), (192, 194), (192, 196), (192, 224)]
def r1sG : List Nat := [2, 2, 4, 4, 6, 6, 6, 32, 32, 34, 34, 34, 64, 64, 96, 96, 96, 128, 128, 132, 132, 132, 192, 192, 192]
def r2sG : List Nat := [66, 130, 36, 68, 38, 70, 134, 36, 160, 38, 98, 162, 66, 68, 98, 100, 224, 130, 160, 134, 164, 196, 194, 196, 224]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_230.map (· &&& dom_230)
def goalM : Nat := goal_230 &&& dom_230
def NN : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x14267388
  | 5, 0 => 0xd481a3b28c4b0892132d4c0a
  | 6, 0 => 0xd481a3b2
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55000000550000005000000050000000550000005500000050000000500000005400000054000000540000005400000054000000540000005400000054000000550000005500000055000000550000000000000000000000000000000000000000000000000000000000000000000000550000004400000055000000440000005500000000000000550000000000000055000000000000005500000000000000500000005000000050000000500000005000000050000000500000005000000044000000440000004400000044000000440000004400000044000000440000005500000055000000000000000000000055000000550000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x46885
  | 5, 0, 0 => 0x344557d1159e4456
  | 6, 0, 0 => 0x34455
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 19
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfcf83e0e039fffc000001cff300e7c00e001f0001ce7c1f000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfcfb7ebebfbfffe128400d6b58ae7ca2e28bf094bce7e1f429
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
  | 4, 0 => 0xd481a3b23c1bfccf2d1c520d079f4e77
  | 5, 0 => 0x41397cc03d0a49bd15efde48150423270650e42f0244ad5d
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x1020001
  | 5, 0 => 0x10101010003
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
  | 0 => checkCutEntry true dom_102 roots_102 4 s ws hint
  | 1 => checkCutEntry true dom_228 roots_228 4 s ws hint
  | 2 => checkCutEntry true dom_226 roots_226 4 s ws hint
  | 3 => checkCutEntry true dom_198 roots_198 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_230 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_102 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_228 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_226 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_198 _ hc
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xffffffff00000000ffffffff00000000, 96), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xcccccccccccccccccccccccccccccccc, 126)], [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
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

def isoMvS_87 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_87 : Lower true dom_87 roots_87 goal_87 5 :=
  lower_iso isoMvS_87 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_91 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_91 : Lower true dom_91 roots_91 goal_91 5 :=
  lower_iso isoMvS_91 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_103 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_103 : Lower true dom_103 roots_103 goal_103 5 :=
  lower_iso isoMvS_103 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_110 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_110 : Lower true dom_110 roots_110 goal_110 5 :=
  lower_iso isoMvS_110 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_94

def isoMvS_115 : List (Nat × Nat) := [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_115 : Lower true dom_115 roots_115 goal_115 5 :=
  lower_iso isoMvS_115 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_117 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_117 : Lower true dom_117 roots_117 goal_117 5 :=
  lower_iso isoMvS_117 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_118 : List (Nat × Nat) := [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_118 : Lower true dom_118 roots_118 goal_118 5 :=
  lower_iso isoMvS_118 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_173 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem lowS_173 : Lower true dom_173 roots_173 goal_173 6 :=
  lower_iso isoMvS_173 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_167

def isoMvS_174 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_174 : Lower true dom_174 roots_174 goal_174 5 :=
  lower_iso isoMvS_174 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_94

def isoMvS_181 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_181 : Lower true dom_181 roots_181 goal_181 6 :=
  lower_iso isoMvS_181 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_167

def isoMvS_185 : List (Nat × Nat) := [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_185 : Lower true dom_185 roots_185 goal_185 6 :=
  lower_iso isoMvS_185 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_167

def isoMvS_186 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem lowS_186 : Lower true dom_186 roots_186 goal_186 5 :=
  lower_iso isoMvS_186 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_94

def isoMvS_199 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_199 : Lower true dom_199 roots_199 goal_199 5 :=
  lower_iso isoMvS_199 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_203 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_203 : Lower true dom_203 roots_203 goal_203 5 :=
  lower_iso isoMvS_203 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155

def isoMvS_206 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_206 : Lower true dom_206 roots_206 goal_206 5 :=
  lower_iso isoMvS_206 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155

def isoMvS_211 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_211 : Lower true dom_211 roots_211 goal_211 5 :=
  lower_iso isoMvS_211 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155

def isoMvS_214 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]
theorem lowS_214 : Lower true dom_214 roots_214 goal_214 5 :=
  lower_iso isoMvS_214 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_94

def isoMvS_217 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_217 : Lower true dom_217 roots_217 goal_217 5 :=
  lower_iso isoMvS_217 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_218 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccccccccccccccccccccccccccc, 126), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_218 : Lower true dom_218 roots_218 goal_218 5 :=
  lower_iso isoMvS_218 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155

def isoMvS_229 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_229 : Lower true dom_229 roots_229 goal_229 7 :=
  lower_iso isoMvS_229 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_227

def isoMvS_233 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_233 : Lower true dom_233 roots_233 goal_233 7 :=
  lower_iso isoMvS_233 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_227

def isoMvS_234 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_234 : Lower true dom_234 roots_234 goal_234 5 :=
  lower_iso isoMvS_234 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155

def isoMvS_236 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem lowS_236 : Lower true dom_236 roots_236 goal_236 7 :=
  lower_iso isoMvS_236 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_230

theorem lowS_95 : Lower true dom_95 roots_95 goal_95 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaa00000000aaaaaaaa, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_94

namespace S_119
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (2, 18), (2, 66), (3, 19), (3, 35), (3, 67), (4, 36), (4, 68), (5, 21), (5, 37), (5, 69), (6, 22), (6, 38), (6, 70), (7, 23), (7, 39), (7, 71), (16, 17), (16, 18), (20, 21), (20, 22), (20, 52), (20, 84), (32, 33), (32, 36), (34, 35), (34, 38), (34, 50), (34, 98), (48, 49), (48, 50), (48, 52), (64, 66), (64, 68), (65, 67), (65, 69), (65, 81), (65, 97), (80, 81), (80, 82), (80, 84), (96, 97), (96, 98), (96, 100), (112, 113), (112, 114), (112, 116)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 16, 16, 20, 20, 20, 20, 32, 32, 34, 34, 34, 34, 48, 48, 48, 64, 64, 65, 65, 65, 65, 80, 80, 80, 96, 96, 96, 112, 112, 112]
def r2sG : List Nat := [17, 33, 18, 66, 19, 35, 67, 36, 68, 21, 37, 69, 22, 38, 70, 23, 39, 71, 17, 18, 21, 22, 52, 84, 33, 36, 35, 38, 50, 98, 49, 50, 52, 66, 68, 67, 69, 81, 97, 81, 82, 84, 97, 98, 100, 113, 114, 116]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_119.map (· &&& dom_119)
def goalM : Nat := goal_119 &&& dom_119
def NN : Nat → Nat
  | 5 => 1
  | 6 => 3
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x42c86ebe
  | 6, 0 => 0x66c2c4d15b2202470c0f5fe5
  | 7, 0 => 0x66c2c4d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff00cc00cc00ff00ff00cc00cc0000000000000000000000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000000ff00ff0000000000ff00ff000000000000000000000000000000000000000000ff000000ff000000ff000000ff00000000000000000000000000000000000000cc00cc00cc00cc00cc00cc00cc00cc0000000000000000000000000000000000aa00aa00aa00aa00aa00aa00aa00aa00000000000000000000000000000000000f000f000f000f000f000f000000000000000000000000000000000000000000ff00ff00ff00ff0000000000000000
  | 0, 1 => 0xff00ff00ff00ff00ff000000ff0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x5432106
  | 6, 0, 0 => 0x54632065846320775463207
  | 7, 0, 0 => 0x5463206
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 28
  | 6 => 32
  | 7 => 28
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc01ff03f07c000000f3ff80fc01ff000000e381c0fc000000003c03f07c007800038e73ffffff000000fffe00000000
  | 0, 1 => 0xffffc0fc0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfd4bff6bf4fe92150af3ff80fc41ff4124a2e3a1d0fc9215490abc2bf07c24f845178e736deaf500006afffe20824948
  | 0, 1 => 0xfffff0fedb5d
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
  | 5, 0 => 0x66c2c4d15fce0b35135bf4211001225c
  | 6, 0 => 0x6502e0db538c39cc2e09f1da284b994b15eddc0214543f8410828d5d0f9c58b10e7a6fca
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x1020003
  | 6, 0 => 0x30403010305040306
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
  | 0 => checkCutEntry true dom_103 roots_103 5 s ws hint
  | 1 => checkCutEntry true dom_118 roots_118 5 s ws hint
  | 2 => checkCutEntry true dom_117 roots_117 5 s ws hint
  | 3 => checkCutEntry true dom_115 roots_115 5 s ws hint
  | 4 => checkCutEntry true dom_55 roots_55 5 s ws hint
  | 5 => checkCutEntry true dom_86 roots_86 4 s ws hint
  | 6 => checkCutEntry true dom_87 roots_87 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_119 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_118 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_117 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_86 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_119 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_119 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_119 == dom_119) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_119 goalM v ys) : RunD true dom_119 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_119 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_119 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_119 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_119 roots_119 goal_119 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_119 goal_119 := by
    have h0 : isConstB dom_119 goal_119 = false := by decide +kernel
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

end S_119

theorem lowS_119 : Lower true dom_119 roots_119 goal_119 8 := S_119.noCircuit

namespace S_123
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (2, 18), (2, 66), (3, 19), (3, 35), (3, 67), (8, 72), (9, 25), (9, 41), (9, 73), (10, 26), (10, 74), (11, 27), (11, 43), (11, 75), (16, 17), (16, 18), (24, 25), (24, 26), (24, 88), (32, 33), (34, 35), (34, 50), (34, 98), (40, 41), (40, 104), (42, 43), (42, 58), (42, 106), (48, 49), (48, 50), (56, 57), (56, 58), (56, 120), (64, 66), (64, 72), (65, 67), (65, 73), (65, 81), (65, 97), (80, 81), (80, 82), (80, 88), (96, 97), (96, 98), (96, 104), (112, 113), (112, 114), (112, 120)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 8, 9, 9, 9, 10, 10, 11, 11, 11, 16, 16, 24, 24, 24, 32, 34, 34, 34, 40, 40, 42, 42, 42, 48, 48, 56, 56, 56, 64, 64, 65, 65, 65, 65, 80, 80, 80, 96, 96, 96, 112, 112, 112]
def r2sG : List Nat := [17, 33, 18, 66, 19, 35, 67, 72, 25, 41, 73, 26, 74, 27, 43, 75, 17, 18, 25, 26, 88, 33, 35, 50, 98, 41, 104, 43, 58, 106, 49, 50, 57, 58, 120, 66, 72, 67, 73, 81, 97, 81, 82, 88, 97, 98, 104, 113, 114, 120]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_123.map (· &&& dom_123)
def goalM : Nat := goal_123 &&& dom_123
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x1fb28662
  | 6, 0 => 0x60d528e8
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000000000000f0f0f0f0f0f00000f0f0f0f0f0f0000000000000000000000000000000000000f0f00000f0f00000f0f00000f0f0000000000000000000000000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000000000000000000000000000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x2c6886
  | 6, 0, 0 => 0x346886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3f007ffe00000ff81ffffc00038e07c01f00000001cf873fe00000039c0f87c0078000039dcffff800000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3f107ffe04222ffe1ffffdacdf8e87d09f29159215cf873fe01242ab9caf87c24f8529979dcffffc251094c8
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 50 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 50 (i % 8)
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
def CN0 : Nat → Nat
  | 4 => 1
  | 5 => 4
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0x4b9919ff
  | 5, 0 => 0x60d528e855fd015f132f680e0ae2444c
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x1010200
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
  | 0 => checkCutEntry true dom_90 roots_90 4 s ws hint
  | 1 => checkCutEntry true dom_115 roots_115 5 s ws hint
  | 2 => checkCutEntry true dom_91 roots_91 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_123 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_90 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91 _ hc
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

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
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

namespace S_126
def pairsG : List (Nat × Nat) := [(2, 18), (2, 66), (4, 36), (4, 68), (6, 22), (6, 38), (6, 70), (8, 72), (10, 26), (10, 74), (12, 44), (12, 76), (14, 30), (14, 46), (14, 78), (16, 18), (20, 22), (20, 52), (20, 84), (24, 26), (24, 88), (28, 30), (28, 60), (28, 92), (32, 36), (34, 38), (34, 50), (34, 98), (40, 44), (40, 104), (42, 46), (42, 58), (42, 106), (48, 50), (48, 52), (56, 58), (56, 60), (56, 120), (64, 66), (64, 68), (64, 72), (80, 82), (80, 84), (80, 88), (96, 98), (96, 100), (96, 104), (112, 114), (112, 116), (112, 120)]
def r1sG : List Nat := [2, 2, 4, 4, 6, 6, 6, 8, 10, 10, 12, 12, 14, 14, 14, 16, 20, 20, 20, 24, 24, 28, 28, 28, 32, 34, 34, 34, 40, 40, 42, 42, 42, 48, 48, 56, 56, 56, 64, 64, 64, 80, 80, 80, 96, 96, 96, 112, 112, 112]
def r2sG : List Nat := [18, 66, 36, 68, 22, 38, 70, 72, 26, 74, 44, 76, 30, 46, 78, 18, 22, 52, 84, 26, 88, 30, 60, 92, 36, 38, 50, 98, 44, 104, 46, 58, 106, 50, 52, 58, 60, 120, 66, 68, 72, 82, 84, 88, 98, 100, 104, 114, 116, 120]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_126.map (· &&& dom_126)
def goalM : Nat := goal_126 &&& dom_126
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xcfcc128c129a2baa
  | 6, 0 => 0x14e06d24
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x555500005555000055550000555500000000000000000000000000000000000000550055005500550000000000000000000000000000000000000000000000005555555500000000555555550000000000000000000000000000000000000000555555555555555555550000555500000000000000000000000000000000000055005500550055005500550055005500000000000000000000000000000000005050505050505050505050505050505000000000000000000000000000000000444444444444444444444444444444440000000000000000000000000000000055555555555555550000000000000000
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
  | 4, 0 => 0x1520e1e2
  | 5, 0 => 0xbf535937ae51a388425782903f8d61283960d27e37a8047f14e06d24
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x20001010201
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
  | 0 => checkCutEntry true dom_90 roots_90 4 s ws hint
  | 1 => checkCutEntry true dom_118 roots_118 5 s ws hint
  | 2 => checkCutEntry true dom_94 roots_94 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_126 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_90 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_118 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_94 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_126 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_126 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_126 == dom_126) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_126 goalM v ys) : RunD true dom_126 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_126 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_126 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_126 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_126 roots_126 goal_126 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_126 goal_126 := by
    have h0 : isConstB dom_126 goal_126 = false := by decide +kernel
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

end S_126

theorem lowS_126 : Lower true dom_126 roots_126 goal_126 7 := S_126.noCircuit

theorem lowS_175 : Lower true dom_175 roots_175 goal_175 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc00000000000000000000cccc0000cccc, 128, 130)] (by decide +kernel) (by decide +kernel) lowS_173

namespace S_187
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 129), (2, 18), (2, 130), (3, 19), (3, 35), (3, 131), (8, 136), (9, 25), (9, 41), (9, 137), (10, 26), (10, 138), (11, 27), (11, 43), (11, 139), (16, 17), (16, 18), (24, 25), (24, 26), (24, 152), (32, 33), (32, 160), (34, 35), (34, 50), (34, 162), (40, 41), (40, 168), (42, 43), (42, 58), (42, 170), (48, 49), (48, 50), (48, 176), (56, 57), (56, 58), (56, 184), (128, 129), (128, 130), (128, 136), (128, 160), (144, 145), (144, 146), (144, 152), (144, 176)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 8, 9, 9, 9, 10, 10, 11, 11, 11, 16, 16, 24, 24, 24, 32, 32, 34, 34, 34, 40, 40, 42, 42, 42, 48, 48, 48, 56, 56, 56, 128, 128, 128, 128, 144, 144, 144, 144]
def r2sG : List Nat := [17, 33, 129, 18, 130, 19, 35, 131, 136, 25, 41, 137, 26, 138, 27, 43, 139, 17, 18, 25, 26, 152, 33, 160, 35, 50, 162, 41, 168, 43, 58, 170, 49, 50, 176, 57, 58, 184, 129, 130, 136, 160, 145, 146, 152, 176]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_187.map (· &&& dom_187)
def goalM : Nat := goal_187 &&& dom_187
def NN : Nat → Nat
  | 3 => 1
  | 4 => 5
  | 5 => 17
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x52aed028
  | 4, 0 => 0xfd00545a5bf99e7f4a66c5e12d67a07a10a69370
  | 5, 0 => 0xf2041c70efdc2368d43c6e9dcc12b1d7c74e37a7b63c2bbfb20345baa45bc8a972c672ee53b1943836b26ed13134d20423b040dd2059458912bcac8006b11b76010e6a18
  | 6, 0 => 0xfab6fd4cda57e514901740526663ad912c1c92f417b622b315b97920
  | 7, 0 => 0xd9be079b
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f00000f0f000000000000000000000f0f00000f0f000000000000000000000e0e0e0e0e0e0e0e00000000000000000e0e0e0e0e0e0e0e00000000000000000a0f0a0f0a0f0a0f00000000000000000a0a0a0a0a0a0a0a00000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000000000000f000f000f000f0000000000000000000f000f000f000f0000000000000000000e0e0e0e0e0e0e0e00000000000000000e0e00000e0e000000000000000000000f0f0f0f0f0f0f0f00000000000000000a0a0a0a0a0a0a0a
  | 0, 1 => 0xf0e0f0e0f0e0f0e00000000000000000f0e0f0e0f0e0f0e00000000000000000f0f0f0f000f000f00000000000000000f0f0f0f000000000000000000000000000f000f000f000f0000000000000000000f000f000000000000000000000000000000000a0f0a0f0000000000000000000000000a0a0a0a00000000000000000a0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f00000f0f000000000000000000000f0a0f0a0f0a0f0a00000000000000000f0a0f0a0f0a0f0a00000000000000000c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c
  | 0, 2 => 0x303030303030303000000000000000003030000030300000000000000000000000f000f000f000f0000000000000000000f0000000f00000000000000000000000f000f000f000f0000000000000000000a000a000a000a000000000000000000000e0e00000e0e000000000000000000000e0e00000e0e0000000000000000000000000f0f0f0f0000000000000000000000000a0a0a0a0000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f0f000f0000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x188204
  | 4, 0, 0 => 0x742d8451882b228d4230146a4a00a3398a45
  | 5, 0, 0 => 0x1a90bb1186742ea4688d48591867415646188cba118e242e64619ccb249a303a16461a84659186a4a164619de659186711804670ce859186742da4619d2801186a1200b6
  | 5, 0, 1 => 0x6a12ee46
  | 6, 0, 0 => 0x19d285918671200b2382233a164600ce85924d019c48591c03388cb23006a121646
  | 7, 0, 0 => 0x67121646
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 24
  | 4 => 29
  | 5 => 34
  | 6 => 39
  | 7 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf0fc00f80000000e701feffff0000073b9ffc00000000000ffff000000038f839ff00000000000003fc00001cee7
  | 0, 1 => 0xe3fce7fffffffffc00000ff1c1f000003fc00001cee7000000073b9ffff003e000000e3e0e7ff9c000e701f0f8
  | 0, 2 => 0xfffc00f80003fc700060000ff000000039c000e701feffff0000073b9ffc00000000000ffffe7fc03fffffc00000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf0fd08f948a4cdbef5ffeffbb34b72f3bdffe494a1299488ffff021109138f839ff00336f187deaf7fedbdebeff7
  | 0, 1 => 0x77effdfffffeeffffc084d6bb1c1f000358cc0000b4ab51124a52f3b9ffffd6bf7bbd55e7e5efff9c892e715f0f8
  | 0, 2 => 0xddb442a82c16ec7068600bdbb14170803dc0c0ad41acd6770000adaed6ec404800094ccffffe7fd0bfffffe1add6
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 46 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 46 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 24 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 24 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 24 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 24 then wireAt i else 0
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
  | 4 => 7
  | 5 => 32
  | 6 => 66
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0xdc8657b0b96432da96bd420b947e10ed54c7ea1f3b31d204046c0ad8
  | 5, 0 => 0xfe8e18affb14f633faaa5dbdf7d4f555f2f82e2de8c21335e3261376d9be079bce0f5b6ac2af0131aefbe66aa25f1f168a213d298a1021a488b594bc7809ecb5778f7c1d6dc78be96c7e64e25390644d38af18643042772929b84b862544c31c22644ad721f16a8f1f32785913cbd16c0ff753940b6f8e560413be2d0323d852
  | 6, 0 => 0xe6f7db40e5cd3820e3261376d9be079bd4fcc823d45e712fd37dbbe5d0db0a4ace6b5595c69ef7cbc2825605be6e9202bd8c7360bc68dcd3bb647d72b8ccb3ceb83067d1b3fc01cdb15201f4b12b155baefbe66aaac59102a6e7d84c9c7c41bd9c6b17f79ba472c49938967b967149e4926907608f5b36fd8be900ef8a213d2988b594bc82c1be6680da4a7471756c526e7bfb076e088cf76530cb386522964264cebfbe635edf375f9040dd57d64a6a54ffd7f0548724744ef821e5495c44d3482b8afa436641aa3b1c03e53a92f0ea3080c7db2d2bb20b2c17300e298259042596428d1fa8b2121e75cfb91d97b1bf0a380884041ad0890323d85202a6e796
  | 6, 1 => 0xfab9e168f87bf355
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x1050100040003
  | 5, 0 => 0x102080708010106040502000101060108000406080005000007000108070401
  | 6, 0 => 0x10001060106010206010108020201010604060108070206060701020601060602010602080606020606020106060807060101010206020106020601060206060100
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 1
  | 5 => 36
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x35347a5c
  | 5, 0 => 0xf7fbe1eef42bd956f33cb6ececf40182e5d49d86db3059ebd4e22464cff4dc1bc8195841c61caeaec4b10641b760e8c0ae271b87abc31f34a9ae8a6da4552e27a12c3cbd9ee966749ba9b7ea7e8ccf6e772aa7d565551f2152cdb5124c083110411bf36a3f1f49d73f0ecd733ba18c603b074636211e2e8e1f2184fb1d64b6fe155b3ab2151462cc092c35ff0119af6f
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x25441202
  | 5, 0 => 0x4110700041102000521060008110200041101000911010009110600041102000411020009210200041106000c510600091106000c5106000c510800091106000c9102000c910200091106000911060004110100091101000c510600092102000411010004110100091101000411060005210600052106000c910200091101
  | 5, 1 => 0xc5108000911060004110600041102
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_51 roots_51 4 s ws hint
  | 1 => checkCutEntry true dom_179 roots_179 6 s ws hint
  | 2 => checkCutEntry true dom_171 roots_171 6 s ws hint
  | 3 => checkCutEntry true dom_177 roots_177 5 s ws hint
  | 4 => checkCutEntry true dom_154 roots_154 4 s ws hint
  | 5 => checkCutEntry true dom_178 roots_178 4 s ws hint
  | 6 => checkCutEntry true dom_185 roots_185 6 s ws hint
  | 7 => checkCutEntry true dom_155 roots_155 5 s ws hint
  | 8 => checkCutEntry true dom_186 roots_186 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_187 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_179 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_171 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_177 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_154 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_178 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_185 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_186 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_187 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_187 goalM v ys := cutHitH_sound h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_187 goalM v ys) : RunD true dom_187 goalM v (ori ys) := h
def Z (s : Nat) := bar true dom_187 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 17 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 17 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
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
  scr true dom_187 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_187 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_187 roots_187 goal_187 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_187 goal_187 := by
    have h0 : isConstB dom_187 goal_187 = false := by decide +kernel
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

end S_187

theorem lowS_187 : Lower true dom_187 roots_187 goal_187 8 := S_187.noCircuit

namespace S_189
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 129), (4, 36), (5, 21), (5, 37), (5, 133), (8, 136), (9, 25), (9, 41), (9, 137), (12, 44), (12, 140), (13, 29), (13, 45), (13, 141), (16, 17), (20, 21), (20, 52), (24, 25), (24, 152), (28, 29), (28, 60), (28, 156), (32, 33), (32, 36), (32, 160), (40, 41), (40, 44), (40, 168), (48, 49), (48, 52), (48, 176), (56, 57), (56, 60), (56, 184), (128, 129), (128, 136), (128, 160), (132, 133), (132, 140), (132, 164), (144, 145), (144, 152), (144, 176), (148, 149), (148, 156), (148, 180)]
def r1sG : List Nat := [1, 1, 1, 4, 5, 5, 5, 8, 9, 9, 9, 12, 12, 13, 13, 13, 16, 20, 20, 24, 24, 28, 28, 28, 32, 32, 32, 40, 40, 40, 48, 48, 48, 56, 56, 56, 128, 128, 128, 132, 132, 132, 144, 144, 144, 148, 148, 148]
def r2sG : List Nat := [17, 33, 129, 36, 21, 37, 133, 136, 25, 41, 137, 44, 140, 29, 45, 141, 17, 21, 52, 25, 152, 29, 60, 156, 33, 36, 160, 41, 44, 168, 49, 52, 176, 57, 60, 184, 129, 136, 160, 133, 140, 164, 145, 152, 176, 149, 156, 180]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_189.map (· &&& dom_189)
def goalM : Nat := goal_189 &&& dom_189
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 10
  | 6 => 3
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x6bf2d70b
  | 4, 0 => 0xdc04155471a3dca82a713860
  | 5, 0 => 0x9a9842cd8cb2f112534affcf3c2843f32f2a0475252730d91925251f0b41463309db0600049bbf1b
  | 6, 0 => 0x433bdfd11e763e041d6371c9
  | 7, 0 => 0xd5451cb
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3333333300000000000000000000000033333333000000000000000000000000332233223322332200000000000000003322000033220000000000000000000030303030303030300000000000000000303030303030303000000000000000003333333333333333000000000000000000000000000000000000000000000000333333333333333300000000000000003333333300000000000000000000000033330000333300000000000000000000333300003333000000000000000000003333333333003300000000000000000030303030300030000000000000000000222222222222222200000000000000002222222222222222
  | 0, 1 => 0x303030303030303000000000000000003030303000000000000000000000000330033003300330000000000000000003300330033003300000000000000000000000000333333330000000000000000000000003333000000000000000000003333333333003300000000000000000033333333330033000000000000000000003322330033223300000000000000000000222200002222000000000000000033333333333333330000000000000000333300003333000000000000000000003322332233223322000000000000000033223322332233220000000000000000333333333333333300000000000000002222222222222222
  | 0, 2 => 0x303030300000000000000000000000003030303000000000000000000000000003300330033003300000000000000000000000000000000000000000000000033333333333333330000000000000000323232323232323200000000000000003333333333333333000000000000000003030303000000000000000000000000323232323232323200000000000000003232323232323232000000000000000000003232000032320000000000000000000032320000323200000000000000003333333333330000000000000000000033333333333300000000000000000000333333332222222200000000000000003333333322222222
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x188204
  | 4, 0, 0 => 0x1ca05914ea4950a7314045
  | 5, 0, 0 => 0x89dd30118e205c96689ca02598e2754046389c0a118ee9824468c1c50118e2701e463b8a0691987514046
  | 6, 0, 0 => 0x388a0259a07138a0238227714046
  | 7, 0, 0 => 0xe2714046
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 24
  | 4 => 29
  | 5 => 34
  | 6 => 39
  | 7 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfff000000000e00f80000e38000e6f878fff000000000ffffff000000fc0fc0ff0000000000e0f80000000000e777
  | 0, 1 => 0x1c7fff000000000e38f8ff80fff000ff0000000ffff8ff80fff00000e777ffffc0ff0000000e38f8fff7fff00000e777
  | 0, 2 => 0xfff000000fff000000000fff000e6ff7fffffff000000e38000e6ff7f03800000ff7ffc0fffff0000000fff00e777
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x924fff444a2a6dbe60fbb5d5e38492e6f878fff9249094c4ffffffd4deeefc0fc0ff2111db6db6f4fca82492492be777
  | 0, 1 => 0x1c7b6d100686492e38f8ff806db000bbb5d5db6ffffcffaab6d10d00c666ffffe4ffb5d56dbe79fbfff7fffb6dbbf7f7
  | 0, 2 => 0x104b6d000202b6d104000044fffffffffffffffb6d9096c6e796dbefff7f03901b00de6efe4fffff6b3bb6dfff6fef7f
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 48 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 48 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 24 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 24 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 24 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 24 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 4 => 4
  | 5 => 14
  | 6 => 16
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0x31f610582f2378df279ae7231f4315be
  | 5, 0 => 0x9262f3c66b462f9d66da830a591d34334d6a2c94402ea05035ff7aa52fda93262f2cd5840fcdba460d5451cb075ec06d073eb7d402d4884f
  | 6, 0 => 0x8b7522bb649a96075aa42f824d6a2c943614c4b22f2cd58428a99b5d1d69c49a133b77d712d0c89710128d310d5451cb0bf7579707140615056e68db03ef6a45
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x10302
  | 5, 0 => 0x4000404000100030103030103
  | 6, 0 => 0x30004030304040403030303030503
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 6 0 (CN0 s)
def CN : Nat → Nat
  | 5 => 11
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0x31a94df12fa46df929ab31ed2973feea23aa8825236211e71ef152b21e5fb89717ace72212aa8dd2054b9a78
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x411052044148d1032344144e10410440c8210314840c4110314840c41105
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 5 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_153 roots_153 4 s ws hint
  | 1 => checkCutEntry true dom_172 roots_172 4 s ws hint
  | 2 => checkCutEntry true dom_53 roots_53 4 s ws hint
  | 3 => checkCutEntry true dom_185 roots_185 6 s ws hint
  | 4 => checkCutEntry true dom_181 roots_181 6 s ws hint
  | 5 => checkCutEntry true dom_173 roots_173 6 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_189 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_153 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_172 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_185 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_181 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_173 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_189 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_189 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffff00000000ffffffff00000000, 96), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffff00000000ffffffff00000000, 96), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_189 == dom_189) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_189 goalM v ys) : RunD true dom_189 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_189 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
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
  scr true dom_189 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_189 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_189 roots_189 goal_189 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_189 goal_189 := by
    have h0 : isConstB dom_189 goal_189 = false := by decide +kernel
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

end S_189

theorem lowS_189 : Lower true dom_189 roots_189 goal_189 8 := S_189.noCircuit

theorem lowS_207 : Lower true dom_207 roots_207 goal_207 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000aaaa000000000000aaaa000000000000aaaa, 128, 129)] (by decide +kernel) (by decide +kernel) lowS_206

theorem lowS_215 : Lower true dom_215 roots_215 goal_215 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_214

namespace S_219
def pairsG : List (Nat × Nat) := [(1, 17), (1, 129), (2, 18), (2, 66), (2, 130), (3, 19), (3, 67), (3, 131), (8, 72), (8, 136), (9, 25), (9, 73), (9, 137), (10, 26), (10, 74), (10, 138), (11, 27), (11, 75), (11, 139), (16, 17), (16, 18), (24, 25), (24, 26), (24, 88), (24, 152), (64, 66), (64, 72), (65, 67), (65, 73), (65, 81), (65, 193), (80, 81), (80, 82), (80, 88), (128, 129), (128, 130), (128, 136), (144, 145), (144, 146), (144, 152), (192, 193), (192, 194), (192, 200), (208, 209), (208, 210), (208, 216)]
def r1sG : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 8, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 16, 16, 24, 24, 24, 24, 64, 64, 65, 65, 65, 65, 80, 80, 80, 128, 128, 128, 144, 144, 144, 192, 192, 192, 208, 208, 208]
def r2sG : List Nat := [17, 129, 18, 66, 130, 19, 67, 131, 72, 136, 25, 73, 137, 26, 74, 138, 27, 75, 139, 17, 18, 25, 26, 88, 152, 66, 72, 67, 73, 81, 193, 81, 82, 88, 129, 130, 136, 145, 146, 152, 193, 194, 200, 209, 210, 216]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_219.map (· &&& dom_219)
def goalM : Nat := goal_219 &&& dom_219
def NN : Nat → Nat
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0x8e86f0dd
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x2c6886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe38e07e0000000001e7ff000000001f83f000078071ce3fc0ff8000003ffc00000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xe38e87e4909649215e7ff004924295f83f0924f82f1ce3fc0ffa092523ffc41049292
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 46 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 46 (i % 8)
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
def CN0 : Nat → Nat
  | 5 => 3
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0x8e86f0dd3e96773d0273a5df
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x1
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 3 0 (CN0 s)
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
  | 0 => checkCutEntry true dom_218 roots_218 5 s ws hint
  | 1 => checkCutEntry true dom_217 roots_217 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_219 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_218 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_217 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_219 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_219 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_219 == dom_219) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_219 goalM v ys) : RunD true dom_219 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_219 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
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
  scr true dom_219 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_219 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_219 roots_219 goal_219 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_219 goal_219 := by
    have h0 : isConstB dom_219 goal_219 = false := by decide +kernel
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

end S_219

theorem lowS_219 : Lower true dom_219 roots_219 goal_219 7 := S_219.noCircuit

namespace S_222
def pairsG : List (Nat × Nat) := [(2, 18), (2, 66), (2, 130), (4, 68), (6, 22), (6, 70), (6, 134), (8, 72), (8, 136), (10, 26), (10, 74), (10, 138), (12, 76), (12, 140), (14, 30), (14, 78), (14, 142), (16, 18), (20, 22), (20, 84), (24, 26), (24, 88), (24, 152), (28, 30), (28, 92), (28, 156), (64, 66), (64, 68), (64, 72), (80, 82), (80, 84), (80, 88), (128, 130), (128, 136), (132, 134), (132, 140), (132, 196), (144, 146), (144, 152), (148, 150), (148, 156), (148, 212), (192, 194), (192, 196), (192, 200), (208, 210), (208, 212), (208, 216)]
def r1sG : List Nat := [2, 2, 2, 4, 6, 6, 6, 8, 8, 10, 10, 10, 12, 12, 14, 14, 14, 16, 20, 20, 24, 24, 24, 28, 28, 28, 64, 64, 64, 80, 80, 80, 128, 128, 132, 132, 132, 144, 144, 148, 148, 148, 192, 192, 192, 208, 208, 208]
def r2sG : List Nat := [18, 66, 130, 68, 22, 70, 134, 72, 136, 26, 74, 138, 76, 140, 30, 78, 142, 18, 22, 84, 26, 88, 152, 30, 92, 156, 66, 68, 72, 82, 84, 88, 130, 136, 134, 140, 196, 146, 152, 150, 156, 212, 194, 196, 200, 210, 212, 216]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_222.map (· &&& dom_222)
def goalM : Nat := goal_222 &&& dom_222
def NN : Nat → Nat
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xb37739a1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5555000000000000555500000000000055550000000000005555000000000000550055000000000055005500000000005500550000000000550055000000000050505050000000005050505000000000505050500000000050505050000000004444444400000000444444440000000044444444000000004444444400000000555555550000000000000000000000005555555500000000000000000000000055555555000000005555555500000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x2c6886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe3e0e3fe0000000003f1ff80039c038df07800000001ce77fc00fc000000ffff00000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xe3e0e3fe4211914a93f1ff804b9c4b8df07824a52497ce77fe10fd2894aaffff02412944
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 48 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 48 (i % 8)
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
def CN0 : Nat → Nat
  | 5 => 9
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0xb37739a1b153d72e926b807484b4c8726b81e3f45d3045b839fff2c40b839d1a0b0d580f
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x300050104030102
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
  | 0 => checkCutEntry true dom_218 roots_218 5 s ws hint
  | 1 => checkCutEntry true dom_154 roots_154 4 s ws hint
  | 2 => checkCutEntry true dom_204 roots_204 4 s ws hint
  | 3 => checkCutEntry true dom_206 roots_206 5 s ws hint
  | 4 => checkCutEntry true dom_214 roots_214 5 s ws hint
  | 5 => checkCutEntry true dom_94 roots_94 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_222 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_218 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_154 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_204 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_206 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_214 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_94 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_222 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_222 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_222 == dom_222) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_222 goalM v ys) : RunD true dom_222 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_222 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
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
  scr true dom_222 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_222 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_222 roots_222 goal_222 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_222 goal_222 := by
    have h0 : isConstB dom_222 goal_222 = false := by decide +kernel
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

end S_222

theorem lowS_222 : Lower true dom_222 roots_222 goal_222 7 := S_222.noCircuit

namespace S_231
def pairsG : List (Nat × Nat) := [(1, 33), (1, 129), (2, 66), (2, 130), (3, 35), (3, 67), (3, 131), (4, 36), (4, 68), (5, 37), (5, 69), (5, 133), (6, 38), (6, 70), (6, 134), (7, 39), (7, 71), (7, 135), (32, 33), (32, 36), (32, 160), (34, 35), (34, 38), (34, 98), (34, 162), (64, 66), (64, 68), (65, 67), (65, 69), (65, 97), (65, 193), (96, 97), (96, 98), (96, 100), (96, 224), (128, 129), (128, 130), (128, 160), (132, 133), (132, 134), (132, 164), (132, 196), (192, 193), (192, 194), (192, 196), (192, 224)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 32, 32, 32, 34, 34, 34, 34, 64, 64, 65, 65, 65, 65, 96, 96, 96, 96, 128, 128, 128, 132, 132, 132, 132, 192, 192, 192, 192]
def r2sG : List Nat := [33, 129, 66, 130, 35, 67, 131, 36, 68, 37, 69, 133, 38, 70, 134, 39, 71, 135, 33, 36, 160, 35, 38, 98, 162, 66, 68, 67, 69, 97, 193, 97, 98, 100, 224, 129, 130, 160, 133, 134, 164, 196, 193, 194, 196, 224]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_231.map (· &&& dom_231)
def goalM : Nat := goal_231 &&& dom_231
def NN : Nat → Nat
  | 4 => 3
  | 5 => 8
  | 6 => 18
  | 7 => 5
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xeb5c1d5b244f2aba14e7e6c5
  | 5, 0 => 0xd771514cc32a09fa986351167b1ef8897354f97143fcf6613bec1fe132ebd51f
  | 6, 0 => 0xfceb5699f2820d0ad87d2f2cbf559593b840e302ada2d601a89e5f54a7e89290a6a8e115939404077354f9716200e4bb2916557521971ca619f2a3d4188fc193159b6205041ad919
  | 7, 0 => 0x91e3752b877aea086b432cc3252597bc21971ca6
  | 8, 0 => 0xa26a090d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000ff0000000000000000000000000000000000000000000000ff000000ff000000ff000000ff000000ff00000000000000ff00000000000000000000005500000000000000550000005500000000000000550000000000000000000000ff00000000000000ff000000ff00000000000000ff00000000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc0000005500000055000000550000005500000055000000000000005500000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000
  | 0, 1 => 0xcc000000cc000000ff000000cc000000cc000000cc000000ff000000cc000000ff000000aa000000ff000000aa000000aa000000aa000000aa000000aa00000033000000330000000000000033000000330000003300000000000000000000005500000055000000550000005500000055000000550000005500000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000aa000000aa000000aa000000aa000000aa000000aa000000aa000000aa0000000f0000000f0000000f0000000f0000000f0000000f0000000f00000000000000ff000000ff000000ff000000ff00000000000000000000000000000000
  | 0, 2 => 0xff00000000000000ff00000000000000ff00000000000000000000000000000000000000ff000000ff0000000000000000000000ff00000000000000ff00000000000000ff000000ff000000ff00000000000000ff00000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff00000000000000ff000000ff0000000000000000000000ff000000ff000000ff00000000000000ff000000ff000000ff000000ff000000ff000000ff00000000000000000000003300000033000000330000003300000033000000330000000000000000000000ff000000f0000000ff000000f0000000f0000000f0000000f0000000f0
  | 0, 3 => 0xff000000ff00000000000000000000000000000000000000ff000000ff000000ff00000000000000ff000000ff0000000000000000000000ff000000ff000000ff00000000000000ff000000ff000000ff0000000000000000000000000000000000000000000000ff00000000000000ff0000000000000000000000ff00000000000000ff00000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x10622814c31140a4188205
  | 5, 0, 0 => 0x18627014c418940658d406a196313008658c41021804189405589490218c3104076
  | 6, 0, 0 => 0x2c6256d0cb1895b021f4b1895243832312818658c4a05d0ebb0c4a021eab1894043d16312808702c620810c030c4a01d80b1a8114319631280879ac625010eb1aa408a1c0b809404301eb1a8086
  | 6, 0, 1 => 0xb189c0431963104087
  | 7, 0, 0 => 0x2c6254808758c4a020eeb18940471d6312808c39963128087
  | 8, 0, 0 => 0x163128086
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
  | 0, 0 => 0x3fff81fc0000fffe07f00003fff81fc00000f00000ffe0000001e3f07cfffe07f00003c07fe000000
  | 0, 1 => 0x7ffc1f000078038e73fffff8000003fff87fc0000001e07f0000000078038e73f0fffff00003ff800000000
  | 0, 2 => 0xffe1f80000003f801fc00000ffe07f00003ffffffc0000f01ffff00003ffffe000000fffff80000003c00003ff80
  | 0, 3 => 0x3f800000000f01ff8000003c07fffc0000001e07f00003ff800000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x849004400003fffe1fedadb6a4c03214221edbe0eedadb4f08512ffe008910be3f07ceedc07614223e07fe812524
  | 0, 1 => 0x26c42fffcbf656cf9378e73d93bd000340bbb707d8718c849e87f24a44448f8278e73b0f7aed001ffffc4112484a
  | 0, 2 => 0x7b61780db5b81f8017edadb87fe87fb6b6fffffffffffff81ffbb6ded7fffff936d6eddbbd040340b3e6155bff80
  | 0, 3 => 0x1f80112484afc9ffe449493f27fffdb7b5000e83b24a45ed84002484a
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
  | 5, 0 => 0xf9821c30f6d56503d87d2f2cbc823247a26a090d98140ada71214d8c6200e4bb2ae56a36291c9a96290dd75c259276062203faf012e672ac0e316faf0ce26a9a0953ef8406e2bfa106b42875
  | 6, 0 => 0xd11bc92dcf7447c0be90321ebd8e1027ac095c7ea7347fc3a6ccbdb7a6a4e074a48acd3ea26a090d9c20b01793e382f392e1c2e591e3752b91d3aef091bb63768eb811f08af5bf5b8a7c01f48984a4bb877aea0882bca2fb800aaf1f77907d8d74618a4473e4327a72700d1d71fd696c702e860b6b432cc369e5f62d671c6503617539d76132cab4591321235691f5784e969fe34bc3c772474be3f3408657123feb878a3ca533b0399ccbde33c8394032e9f07232970bce307d0e502e244a5a2c5cc4ee2b63add629f60617252597bc206750af1f4488e21e9ebbe81d5b8e2f1b44580919b6a010179f6903139205130e6b992e0a1fa07906b4287503a974c6
  | 6, 1 => 0xf9821c30f786f16ce1fc3794dda3eebb
  | 7, 0 => 0xc90e5d9cc79f5611c21c5344bcf89f86b3584fcfa59827caa26a090d77fa4c4677c6ef217449568972cf4947670a06e3601adcb95df36186561e35fe4eff90d64c78bdfc4b5fcefc395fc13331c3a9fb2ad3f3f729f606172025d4401e5cfe691d3537dd1b6701fc1935560513b764700e172dc20a1fa079
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x101000101010201010101020101010103
  | 6, 0 => 0x4010400040301040003000000020104040000030403010101040003050502030403040200040201000402040201020204040401010405050400030301040500040303
  | 7, 0 => 0x20002030000000203000000000003020302030000040002020202000204
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 3
  | 5 => 7
  | 6 => 53
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x9b1509844e7de38320c6b7fb
  | 5, 0 => 0xec5ace4ab918f7de7373abaf52d74a3c51523f24467edd880f552e2c
  | 6, 0 => 0xd0405bc8cfa37206c450168fc019bea8ae392d81ac32df06a02307159e245cf89d9f4b8098edb0fc8f5fcd478c13e83d8bfb228d883e766f852c984184406a8a7e54abb178af2fc976cc447175d67a8d755cfead7471a77171bd3cd36e11023a661549ff6286cee95ac830195a1ed074584e34b2554edc374ff5ad284c489abd48ef94bc3daa5bbf359b4cd13427e7b13002162b26f465fc26477dd4240807b321b614ab1d3e42321a8662e91658d2fd159ef12e13e9fcb311d4d3970c3c73ce0b0b5ca209c6487f0820d8f00149b64d00016f25
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x19724490300000912408019724490300
  | 5, 0 => 0x244902000009124080000244902000010942080c00244902000000014841000434c9203
  | 6, 0 => 0x34840800000c91020000042840000000921030000024440c00000d11030000042440c00000ca1030000034840c00000ca1000000034440c00000c91030000034440000000911000000034840c00000c91030000042840800001091000000034440800000901020000024840000000921030000042440800001091030000032440c00000901000000024840800000ca1020000032840c00000d21020000024840800000ca100
  | 6, 1 => 0xd11000000032440c000010a1020000042440000000d11000000034840c000010a1000000032440c00001081030000024040000000901020000032840800000c91020000024440000000d11030000024840000000d11000000024440000000901000000032440c00000c9102
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_230 roots_230 7 s ws hint
  | 1 => checkCutEntry true dom_199 roots_199 5 s ws hint
  | 2 => checkCutEntry true dom_229 roots_229 7 s ws hint
  | 3 => checkCutEntry true dom_227 roots_227 7 s ws hint
  | 4 => checkCutEntry true dom_167 roots_167 6 s ws hint
  | 5 => checkCutEntry true dom_103 roots_103 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_231 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_230 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_199 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_229 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_227 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_167 _ hc
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

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_231 == dom_231) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_231 goalM v ys) : RunD true dom_231 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_231 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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

theorem lowS_235 : Lower true dom_235 roots_235 goal_235 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_233

theorem lowS_238 : Lower true dom_238 roots_238 goal_238 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x444400004444000044440000444400004444000044440000444400004444, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_236

theorem lowS_243 : Lower true dom_243 roots_243 goal_243 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000, 1, 17)] (by decide +kernel) (by decide +kernel) lowS_227

theorem lowS_245 : Lower true dom_245 roots_245 goal_245 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x33000000330000003300000033000000330000003300000033000000330000, 1, 17)] (by decide +kernel) (by decide +kernel) lowS_229

theorem lowS_246 : Lower true dom_246 roots_246 goal_246 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x55000000550000005500000055000000550000005500000055000000550000, 2, 18)] (by decide +kernel) (by decide +kernel) lowS_230

def isoMvS_111 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_111 : Lower true dom_111 roots_111 goal_111 6 :=
  lower_iso isoMvS_111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_95

def isoMvS_190 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem lowS_190 : Lower true dom_190 roots_190 goal_190 7 :=
  lower_iso isoMvS_190 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_126

def isoMvS_221 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_221 : Lower true dom_221 roots_221 goal_221 7 :=
  lower_iso isoMvS_221 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_123

def isoMvS_237 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem lowS_237 : Lower true dom_237 roots_237 goal_237 9 :=
  lower_iso isoMvS_237 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_231

def isoMvS_249 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_249 : Lower true dom_249 roots_249 goal_249 8 :=
  lower_iso isoMvS_249 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_245

def isoMvS_250 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem lowS_250 : Lower true dom_250 roots_250 goal_250 7 :=
  lower_iso isoMvS_250 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_222

theorem lowS_127 : Lower true dom_127 roots_127 goal_127 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00ff00ff00ff00ff00ff00ff00ff00, 64, 72)] (by decide +kernel) (by decide +kernel) lowS_119

theorem lowS_191 : Lower true dom_191 roots_191 goal_191 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 16, 18)] (by decide +kernel) (by decide +kernel) lowS_189

namespace S_223
def pairsG : List (Nat × Nat) := [(1, 17), (1, 129), (2, 18), (2, 66), (2, 130), (3, 19), (3, 67), (3, 131), (4, 68), (5, 21), (5, 69), (5, 133), (6, 22), (6, 70), (6, 134), (7, 23), (7, 71), (7, 135), (8, 72), (8, 136), (9, 25), (9, 73), (9, 137), (10, 26), (10, 74), (10, 138), (11, 27), (11, 75), (11, 139), (12, 76), (12, 140), (13, 29), (13, 77), (13, 141), (14, 30), (14, 78), (14, 142), (15, 31), (15, 79), (15, 143), (16, 17), (16, 18), (20, 21), (20, 22), (20, 84), (24, 25), (24, 26), (24, 88), (24, 152), (28, 29), (28, 30), (28, 92), (28, 156), (64, 66), (64, 68), (64, 72), (65, 67), (65, 69), (65, 73), (65, 81), (65, 193), (80, 81), (80, 82), (80, 84), (80, 88), (128, 129), (128, 130), (128, 136), (132, 133), (132, 134), (132, 140), (132, 196), (144, 145), (144, 146), (144, 152), (148, 149), (148, 150), (148, 156), (148, 212), (192, 193), (192, 194), (192, 196), (192, 200), (208, 209), (208, 210), (208, 212), (208, 216)]
def r1sG : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 8, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 12, 12, 13, 13, 13, 14, 14, 14, 15, 15, 15, 16, 16, 20, 20, 20, 24, 24, 24, 24, 28, 28, 28, 28, 64, 64, 64, 65, 65, 65, 65, 65, 80, 80, 80, 80, 128, 128, 128, 132, 132, 132, 132, 144, 144, 144, 148, 148, 148, 148, 192, 192, 192, 192, 208, 208, 208, 208]
def r2sG : List Nat := [17, 129, 18, 66, 130, 19, 67, 131, 68, 21, 69, 133, 22, 70, 134, 23, 71, 135, 72, 136, 25, 73, 137, 26, 74, 138, 27, 75, 139, 76, 140, 29, 77, 141, 30, 78, 142, 31, 79, 143, 17, 18, 21, 22, 84, 25, 26, 88, 152, 29, 30, 92, 156, 66, 68, 72, 67, 69, 73, 81, 193, 81, 82, 84, 88, 129, 130, 136, 133, 134, 140, 196, 145, 146, 152, 149, 150, 156, 212, 193, 194, 196, 200, 209, 210, 212, 216]
def mpG : Nat := 0x7fffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_223.map (· &&& dom_223)
def goalM : Nat := goal_223 &&& dom_223
def NN : Nat → Nat
  | 6 => 11
  | 7 => 8
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xfe9ff2a7dbc779d8ab9797f4a7a5a53191dda1aa8fbe9565711907323416c25a2735c96d17704d9b0fd9c492
  | 7, 0 => 0xcbb5eba9c2002883bcf1d6b659c39cc04c5ba33b35ac44ed2cf52e49249d9544
  | 8, 0 => 0x159fc3d7
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000ffffffff00000000ffffffff00000000ffff000000000000ffff000000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000ffffffff000000000000000000000000ffffffff0000000000000000000000000f0f0f0f0000000000000000000000000f0f0f0f000000000000000000000000ffffffff00000000ffffffff00000000000000000000000000000000
  | 0, 1 => 0x5555555500000000555555550000000055550000000000005555000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000000ff00ff0000000000ff00ff0000000000ff00ff00000000000000000000000000000000000000000000000000000000ffff000000000000ffff0000000000000f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f0000000000fff0fff000000000fff0fff000000000fff0fff000000000fff0fff000000000ffffffff00000000ff00ff0000000000ffffffff00000000ff00ff0000000000ffff000000000000ffff000000000000ffff000000000000ffff0000
  | 0, 2 => 0xffffffff00000000ffff000000000000ffffffff00000000ffff0000000000000f0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f000000000000ff0fff0f00000000ff00ff0000000000ff0fff0f00000000ff00ff0000000000ffffffff00000000ffffffff00000000ffffffff0000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x829072101d05711e203a22520c407315c41c04e62b88f101d0e20c4d03b0a4188207414835880e852483101d0520c470398a4188207
  | 7, 0, 0 => 0x18ae20c4070214520c407320ae20c408020a4188207424ae20c4089a0ae20c408030ae20c407415c41c0408
  | 8, 0, 0 => 0x20ae20c407
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 39
  | 7 => 44
  | 8 => 39
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xff0e1fffc0000000000001ffffff807ffc000000000000000000ff07ffffe0000000000000000fc1f83f0fc0000003e0001c738e71dc7fe0007ff80000000000003fc000fff00000000000007ffffe0000000000000000
  | 0, 1 => 0xffffffc03ffe000000000001e3c0007873ff800ffc03ffffffff0000000000000000001e01fff0000000000ff0003ffc3c0003ff8000001e3c0007ff3fffffffc03fc000fffff07ffffe0000787f01e01fff0000000000
  | 0, 2 => 0xfffe03fffffe0000000001fe1c07ff878c0000000003fc000fffff07ffffe00007fffffffe0000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xbb0e1efb43000036d801b5ffffffe07ffedb5b6b6ade21224824ff07ffffe000011122441244afc1f83f0fc1112247e044bc738e71dc7ff0207ffa24124a4949522ec000bed04000049200247ffffe10110092524a4892
  | 0, 1 => 0xeeeddb803bb4288510a02889e3c2097873ff800ffc01deddb7db008000001b6ed000001e80eff2484909225bb0812fb43c0003ff8009199f3e61b7ff3fffffffc03ff264fffff87ffffe92a4787f01e81fff2484909225
  | 0, 2 => 0xffff03fffffedb5b6b6edb761c05f6878c0036d001b6ed224bedff07ffffe00247ffffffff990db7b6f6dda
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 87 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 87 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 20 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 20 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 20 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 20 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 5 => 3
  | 6 => 24
  | 7 => 89
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0xef23e438d0e847de18b877ed
  | 6, 0 => 0xed5b187fea95d338e640bf6ae49b9a55d95592f5cbb5eba9c8fa21a7ab440db1aaf54a7ea67400dca139294390859258842e87687d5e0252781650556c1bd44b6af166c16763ba0b5026612e3fc684e62cf52e49222e246c159fc3d70ef3b95a
  | 7, 0 => 0xb9e97082b772a8e7b7477579b3c80e63a933c583a8792eeba6679fa4a246353c9e73bd209be3e39b9664a366953a66aa93e603d793e02ce292a3c527929fd987909f4b0e8dda59228beba96d8b26ed4885ee40f282d129c5825f34607f12cd447e88d1777e2a36e97d5e02527ced48e47c338ca777edde1e756dbaae71419b386da88b0468cd1b5165689368633dde155e72e4365622cdf1548f11945457683f4e70d1424c152df24b15255d4a4ef6ca4753fe3a45da3fbd3f9cc85d3e906a5c3c9055bd35bf89ba329f36ec31aea9682fe775a224b88c682420a854226a1e761e3119561b66e661159fc3d714bf73211280f24d106773490f51fcb70c6f0ce2
  | 7, 1 => 0xfb435aadf3fc8a08f3ee0f7ef348fe33ee1ffb75ecc94296ecba8eadec3fab1deacffa68e7e956d4e6a1d35be49b9a55e31753ade0166637dd82b23cd860e269d6c31c6fd513f9ead1d8fb7fce41a1f5cbf17c04c3f2c155c3b3faaebc7c00a5ba4f7bff
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x20001
  | 6, 0 => 0x40906010208040801010601030107040804000106010306
  | 7, 0 => 0x501050304030306060804010501030303030505020304010503030508050405030506010504030805050106030305010501010103030503030301010903030505010509050108010103050507050105090605030104030303
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 5 => 1
  | 6 => 39
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0x2af02972
  | 6, 0 => 0xfbf104c7ea8b788de97d746ce5fd9d74d111799fc6f502aec0576590bef997c0bdbd0a16b5a746d9b159827fa7e81985a7a3bf599e6ef64e9ab1c2279a2694379589023a94b36cc49388f719924ccf198f771ccf6d7deb596be47c065c7dc77652c804505047e0e0473ce0143f6733963a44af3a38e7519733742a243316d24a3249b4792f318e712b813ed82893f1531298c51f0aa5396608f650df
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x35515201
  | 6, 0 => 0x52105000d7105000d5105000d51050011510100085105000d5105000d5101000d7105000d5104000d7101000d710300085103000d5103000c9108000d7105000d51050008510500085103000d710500052105000d5103000d5105000d510100085105000d510300085105000d510400085103000d7105000d5105000d5103
  | 6, 1 => 0xd71010005210500052105000d5105000851050005210500052103
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_211 roots_211 5 s ws hint
  | 1 => checkCutEntry true dom_219 roots_219 7 s ws hint
  | 2 => checkCutEntry true dom_199 roots_199 5 s ws hint
  | 3 => checkCutEntry true dom_222 roots_222 7 s ws hint
  | 4 => checkCutEntry true dom_215 roots_215 6 s ws hint
  | 5 => checkCutEntry true dom_221 roots_221 7 s ws hint
  | 6 => checkCutEntry true dom_207 roots_207 6 s ws hint
  | 7 => checkCutEntry true dom_87 roots_87 5 s ws hint
  | 8 => checkCutEntry true dom_95 roots_95 6 s ws hint
  | 9 => checkCutEntry true dom_155 roots_155 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_223 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_211 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_219 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_199 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_222 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_221 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_207 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_95 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_223 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_223 goalM v ys := cutHitH_sound h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_223 goalM v ys) : RunD true dom_223 goalM v (ori ys) := h
def Z (s : Nat) := bar true dom_223 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 11 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 11 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 8 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 8 0 = true)
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
  scr true dom_223 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_223 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_223 roots_223 goal_223 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_223 goal_223 := by
    have h0 : isConstB dom_223 goal_223 = false := by decide +kernel
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

end S_223

theorem lowS_223 : Lower true dom_223 roots_223 goal_223 9 := S_223.noCircuit

theorem lowS_239 : Lower true dom_239 roots_239 goal_239 10 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_237

theorem lowS_247 : Lower true dom_247 roots_247 goal_247 10 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 1, 17)] (by decide +kernel) (by decide +kernel) lowS_231

namespace S_251
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 129), (2, 18), (2, 66), (2, 130), (3, 19), (3, 35), (3, 67), (3, 131), (8, 72), (8, 136), (9, 25), (9, 41), (9, 73), (9, 137), (10, 26), (10, 74), (10, 138), (11, 27), (11, 43), (11, 75), (11, 139), (16, 17), (16, 18), (24, 25), (24, 26), (24, 88), (24, 152), (32, 33), (32, 160), (34, 35), (34, 50), (34, 98), (34, 162), (40, 41), (40, 104), (40, 168), (42, 43), (42, 58), (42, 106), (42, 170), (48, 49), (48, 50), (48, 176), (56, 57), (56, 58), (56, 120), (56, 184), (64, 66), (64, 72), (65, 67), (65, 73), (65, 81), (65, 97), (65, 193), (80, 81), (80, 82), (80, 88), (96, 97), (96, 98), (96, 104), (96, 224), (112, 113), (112, 114), (112, 120), (112, 240), (128, 129), (128, 130), (128, 136), (128, 160), (144, 145), (144, 146), (144, 152), (144, 176), (192, 193), (192, 194), (192, 200), (192, 224), (208, 209), (208, 210), (208, 216), (208, 240)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 8, 8, 9, 9, 9, 9, 10, 10, 10, 11, 11, 11, 11, 16, 16, 24, 24, 24, 24, 32, 32, 34, 34, 34, 34, 40, 40, 40, 42, 42, 42, 42, 48, 48, 48, 56, 56, 56, 56, 64, 64, 65, 65, 65, 65, 65, 80, 80, 80, 96, 96, 96, 96, 112, 112, 112, 112, 128, 128, 128, 128, 144, 144, 144, 144, 192, 192, 192, 192, 208, 208, 208, 208]
def r2sG : List Nat := [17, 33, 129, 18, 66, 130, 19, 35, 67, 131, 72, 136, 25, 41, 73, 137, 26, 74, 138, 27, 43, 75, 139, 17, 18, 25, 26, 88, 152, 33, 160, 35, 50, 98, 162, 41, 104, 168, 43, 58, 106, 170, 49, 50, 176, 57, 58, 120, 184, 66, 72, 67, 73, 81, 97, 193, 81, 82, 88, 97, 98, 104, 224, 113, 114, 120, 240, 129, 130, 136, 160, 145, 146, 152, 176, 193, 194, 200, 224, 209, 210, 216, 240]
def mpG : Nat := 0x7ffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_251.map (· &&& dom_251)
def goalM : Nat := goal_251 &&& dom_251
def NN : Nat → Nat
  | 6 => 6
  | 7 => 9
  | 8 => 5
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xca644c6868a589555136a9903d8f8089301f60b52cc3de15
  | 7, 0 => 0xc581285ac46ff58bc00bb483be77ff7ba86d79c79d61b1e33c8fcfe4148037ed0a111ac6
  | 8, 0 => 0xf9581f93d61bca3ad16353bea7e13b90229b4bcf
  | 9, 0 => 0xabbcdebd
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f00000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c05050505050505050505050505050505050505050505000005050505050500000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
  | 0, 1 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0505050505050505050505050505050505050000050500000505000005050000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a000f000f000f000f000f000f000f000f000f000f000f000f000a000a000a000a000000000f0f0f0f000000000f0f0f0f000000000f0f0a0a000000000f0f0a0a0f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000f000f000f000f000f000f000f000f000f000f000f000f000f000f00000000
  | 0, 2 => 0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a000f000f000f000f000f000f000f000f000f000f000f000f00000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0000
  | 0, 3 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0xc520dee0ba8834b4e073286961c0e520d2b081cca1a5070398a4188207
  | 7, 0, 0 => 0x18a41bd217028834d8207a99441a4e08314834d020834ca41a42080194349e407314834b8208328838a4e08818a41a4208
  | 8, 0, 0 => 0x19441a4e07328837a4208c19441a4208018a41a4207b99441a4208
  | 9, 0, 0 => 0x19441a4207
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 39
  | 7 => 44
  | 8 => 44
  | 9 => 39
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffffffffc0000000000000001fe007ffff80000003ffffc380fe000fc00000000000001e3f81e7ffc00000000000078f00fe07f1ffffffc07fffffe000003fc03ffff0000000000007fff80000000000000000
  | 0, 1 => 0xffff001f0000000f1e78fffffe1c07f0007e000003fffc03ff0000003c79e3ffffffffe0000000003c7ffff00ff000003ff1e78fe1e1e1c07f0007e0000000000007c0000003c79e3ffffffffe1c07e0000000
  | 0, 2 => 0xff1f3ffffc0f1e78ffffe003e0000001e3cf1ffffffffffffff00000007fff8070000001f800000fffff0ff3f8003ff1e78fffffffff8000000000003ffffffff0000003c79e3fffffff01ffffff800000
  | 0, 3 => 0x7fffff801ffffe0000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfffffffff266cb0cd9e691111fe107ffff8040820bffffe3d0ff52afe6cd36a22222415e3f81e7ffc00222222414978f0afe07f1dddddd8076edd741420a3fc03ffff4089041122887fffc4081122450448a24
  | 0, 1 => 0xffff993f26cd9e5f9f7cfddddd18076a95741420a1dddc03df00000d776fbaddddddbea1406e08003f7777700f7000003fdbb6dbe1e1e1c87f2047e244124444444fc1224517c79e3ddddddbea1c07e00003b6
  | 0, 2 => 0x9999ff3f3ffffc5f1e78eeeee006e000004bb36d97fffffffffffffc3b77db3bbb807a000001fcd9a6dfffff9ff3fddbfffbf7df777776fa8401900000cd3ffffffffdbbf7d7f7ffbfffffffe1ffffffddbaef
  | 0, 3 => 0x7fffff8c1fffff054aaa6
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 83 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 83 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 25 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 25 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 25 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 25 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 6 => 14
  | 7 => 88
  | 8 => 86
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 6, 0 => 0xf26d8109de343f28d1707340cabe9324c288e327ac942526abbcdebd63d014346142c45c5c7c87175c65f24f3ed7b0042c5bd9fb153ca2a7
  | 7, 0 => 0xbd2ec706b04dcbe9ad4ec11dabbcdebda6848e2f9e4bf7549d77a54c97b490a897491da69512dabf9047e9028c9cb6518c7365a1856f065a7fe15d5b79a930dc746ab6147285a337709d2c5370368ca56d01e5fb689cabf767a4872e66f9e70d633e333a60bc2da8605f10375eed28e65de10d3c5d4b42f05c63ea72568d74a5568b7ab455bfa9165414e2c74c85770d49ce75f2477799e945e45f3844fb4707439bf6bc411809663a89c7e636dcf80926d09ab523b70b1023604fcf1fd056571efe94941ebfa8a21c8a230118d7764415eb80ee110702710f5751950e8634880e5fc1200e0698350bb7dac608ba47170864e5a007b81c58030822e9029852e2
  | 7, 1 => 0xfeea3637fb0e930afab46615f9e2b538f751c7bdf6e11dcdf57c7c66ef7931a4ef034088eecee108eeb8992ce815a99be2ba32f1e20b1520e14dc6e3dd67b5c3dc18039fd8a9376cd5a74e82d240270dd0a8b710cd87b091c7f26bf9c0dc0f8e
  | 8, 0 => 0xabbcdebdaadc8e07a8cfbc9ea6848e2fa0fb88aba0c6db67a05c9e0c9f0c20289dda0f419c83c21a9525be3e8a19a4ee83f612cb802845597dc861b17c350e0679a930dc7889a3be77b1674877154aca76d1d597726209a8708f98056d01e5fb67f6166566f9e70d6501e33e633e333a61e6787e5e3c72f85e215d435dc8ed625d4b42f05bce2ce95aaddd1554e5b66d52991b8b5258a476505a2e484fb535a94e38e023477799e94434157041f75a383d24dd0f3ce1106e3c45f2ec37a37dae37a0f94835493a6f33bc0ec331fd7fed2d3f5285291d4264255b937f1ca474d91b6c377a1580c55c1332f4c20fce210108f233cf070ade8d02e103ea0156149f
  | 8, 1 => 0xfeea3637fd21f23efd1464f1f8115048f42a0a63f0f7849debb3b334e6840e11e27eefa6e0742161de709ac9dc32f7d0d11f6982c6acc047c55db4cfc516bcc3c1b8c0f8c1899e57c101cb3ec0fd5904ba19ce79ae03e0a3
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 6, 0 => 0x9090807020900060902060c0b0a
  | 7, 0 => 0x108010406030803090903040308060100010408010800080909040003050200030801080e0301030603010903010601050308030d060905040501080503010308030008090808050809080505030600060604050d000906
  | 8, 0 => 0x806000600050500040006000600000600040504000400060003040405050000000404060004030605000404040100010405040004060600050305060001040804040500060606000406000500000504060305000600
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 6 => 37
  | 7 => 203
  | _ => 0
def CH : Nat → Nat → Nat
  | 6, 0 => 0xfc0a1f28fa386afef927382ff79fd779f31161bdedd80842ebdf51d5e9e68e42e419c093e0bdd1c1c118cc43c094525ebd07ae76bab468ebb6818563b6480bb7b536d8e8b3c33ef3afdd8ef999860eb6978abe7692e9b5168db591118b4eedf67bf14a0875fe59be6c77c8fd59c6aed150a5999e4ef016164e80551d4d1a74e336dcf809307d678621c44e77120b36610747c58a
  | 7, 0 => 0x5e0ad5515d6961d75a45ba1659e5dfb657f289bc57741be957528e7356d239e854a61f63510a1340507c44c04f2402c14ef155754eee98c04ebd785e4c7e8b1b4c1891814c0c59ea4bd9927c4aafa5c74a5d3cf645ac911e41c54b39405872433e1bb70b394939e239056d41367724dd341f4ee7301a307c2e0f62372c0bdb9f2a17584d29ce38a62963af5826f9063c25419f372209127521c44e771ee602de1d0f39f318c8d1ac1790944d168b71731448011d13622f2c12f8f5a512b1fd9911a5222f0f5401ce0f24df2d0e9899da0decbdf30c5619150bf27dd40ad30cde093f37da07b50f4f061a9662051690a204c7cae4032f3b600308ee0e001489c2
  | 7, 1 => 0x9df56f1e9d50767f9ceb383a9c80fadf9c2184dc9be98fd69bd420f99b6c98289b307cfb99fe6c1498a81eed98351abe9650664f914a1b118f929b0e8d9d1eb78acb8af089e133c288e4a83b889b570d87aa2e6d863e01c1860bc4ee853ebe84853c3a1e82f1b7f182e47b4581dc8a7d81574f998083b484801a6f9e7f98c0c37ea6517a7d126add7b8e3c507b68da2c7b1126c579ecbe8479adbcd378596ad975cd8daf73d5c41b7339a79d72f6d45572f6326a72b1509c7298896e727073ad716788fa6e86667b6be00f076a6150b16a50461a692642ce68daa39f67c5a2f2641a7338631e43e0631c063261403b7e6126401160ce35985f62900d5e35e397
  | 7, 2 => 0xf3f88927f04e6736eee022c6ee96c981ee621c3ded1be170eb755017ea1f02f0e9abfec1e8d36afae7d81007e6390fc3e2a86ae4e1a31d8ae1455ea1dea34c79dcf4c73ddc987e34dbeb603ddafe956ada1ca04cd85754a3d7b4e5c4d429b002d19153a1d0c52d53ce7fdbe3ce2824cfcb9855f0cb63a287c9d04edcc7d73182c74471b2c6e4f717c6e2ad97c624e494c4b08ba0c2d11d1ac22a371bc18211a2bffd4a7ebe2ad8dbbddd1dcbbd262811bd21b5d7ba9d26d1b591573bb49527e3af81b954ac56bc36ac491cf4abd7b3ceab642e38ab5c4495aae683c6aa283d76a9696dbfa8256056a4f41971a4d7d2cca4c8c210a4022ed5a2a8eb02a280f743
  | 7, 3 => 0xfe600a54fe1b6a16fd7a7172fc79f3b5fb9f2179f938c1c4f877ceddf8028909f66afd74f5b80ab5f41fcf05
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 6, 0 => 0x96105054952043651520400115103000951031691520000102108000d5101065152040011510105495200368152000011510400095103000961080549520000115104169152000549520046815205368152060549520405495200054952002691520616915200000d51010009510300095103001151040010210800096105
  | 6, 1 => 0x9610505495200368152000009510316915200
  | 7, 0 => 0xd5105001151000009510000115100000d51050009510300115104000951040011510000095100000d5105000c110600115100000c1100001151000011510600095104001151000011510400115104000d5106000c11060009510300015100000d510500115100000d5100000d5105000d51000009510000115104000d5104
  | 7, 1 => 0x9510400115103000951040001510600095100000c1106000c1100000d5105001151000009510300115106000d51060011510000015106000d5105000951000011510000115103000d5101001151000009510400115106001151000009510400095104000d5105000951000009510000115100001151040011510000115106
  | 7, 2 => 0x1151040001510400115106000151060011510100095100000c11000009510400095103000d510500095100001151000009510400095100000d51000011510500115106000951040010110500015100000d5105000d5101000d51040011510400095100000d510100115104000151000009510400115106000d5105000c1104
  | 7, 3 => 0x1151000011510100095104000d5105000d5104000151000011510400115106000d510500095100000951000009510000115104000951000011510400015105001011050011510600115105000951000001510600095104001151000011510600115106000d510600115100000d510000115104000d51010009510400115106
  | 7, 4 => 0x1151030001510500015100001151060011510000095100000d510000095100001151040011510400095100000d5105000951040011510100115100001151010011510400015105000151060011510000115106000951040011510600095104001151000001510000095100000d510100095103000151040009510300115103
  | 7, 5 => 0x11510600095100001151040011510400115104000d5105001151000011510000115100000c1100000d51050011510300095100001151040009510400095104000d510500095100000d510400115100001011050009510000115104000c11060011510400115101000c110400095104000951000011510000115104000d5100
  | 7, 6 => 0x951000011510500095100000151040011510400095100001151060001510400115100000c110600115103
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_249 roots_249 8 s ws hint
  | 1 => checkCutEntry true dom_219 roots_219 7 s ws hint
  | 2 => checkCutEntry true dom_91 roots_91 5 s ws hint
  | 3 => checkCutEntry true dom_250 roots_250 7 s ws hint
  | 4 => checkCutEntry true dom_243 roots_243 8 s ws hint
  | 5 => checkCutEntry true dom_187 roots_187 8 s ws hint
  | 6 => checkCutEntry true dom_235 roots_235 8 s ws hint
  | 7 => checkCutEntry true dom_234 roots_234 5 s ws hint
  | 8 => checkCutEntry true dom_123 roots_123 7 s ws hint
  | 9 => checkCutEntry true dom_90 roots_90 4 s ws hint
  | 10 => checkCutEntry true dom_203 roots_203 5 s ws hint
  | 11 => checkCutEntry true dom_186 roots_186 5 s ws hint
  | 12 => checkCutEntry true dom_155 roots_155 5 s ws hint
  | 13 => checkCutEntry true dom_51 roots_51 4 s ws hint
  | 14 => checkCutEntry true dom_218 roots_218 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_251 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_249 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_219 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_250 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_243 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_187 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_235 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_234 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_123 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_90 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_186 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_218 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_251 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_251 goalM v ys := cutHitH_sound h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_251 goalM v ys) : RunD true dom_251 goalM v (ori ys) := h
def Z (s : Nat) := bar true dom_251 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 6 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 6 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 5 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 5 0 = true)
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
  scr true dom_251 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_251 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_251 roots_251 goal_251 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_251 goal_251 := by
    have h0 : isConstB dom_251 goal_251 = false := by decide +kernel
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

end S_251

theorem lowS_251 : Lower true dom_251 roots_251 goal_251 10 := S_251.noCircuit

theorem lowS_253 : Lower true dom_253 roots_253 goal_253 10 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000033330000333300003333000033330000333300003333000033330000, 1, 17)] (by decide +kernel) (by decide +kernel) lowS_237

namespace S_254
def pairsG : List (Nat × Nat) := [(2, 18), (2, 66), (2, 130), (4, 36), (4, 68), (6, 22), (6, 38), (6, 70), (6, 134), (8, 72), (8, 136), (10, 26), (10, 74), (10, 138), (12, 44), (12, 76), (12, 140), (14, 30), (14, 46), (14, 78), (14, 142), (16, 18), (20, 22), (20, 52), (20, 84), (24, 26), (24, 88), (24, 152), (28, 30), (28, 60), (28, 92), (28, 156), (32, 36), (32, 160), (34, 38), (34, 50), (34, 98), (34, 162), (40, 44), (40, 104), (40, 168), (42, 46), (42, 58), (42, 106), (42, 170), (48, 50), (48, 52), (48, 176), (56, 58), (56, 60), (56, 120), (56, 184), (64, 66), (64, 68), (64, 72), (80, 82), (80, 84), (80, 88), (96, 98), (96, 100), (96, 104), (96, 224), (112, 114), (112, 116), (112, 120), (112, 240), (128, 130), (128, 136), (128, 160), (132, 134), (132, 140), (132, 164), (132, 196), (144, 146), (144, 152), (144, 176), (148, 150), (148, 156), (148, 180), (148, 212), (192, 194), (192, 196), (192, 200), (192, 224), (208, 210), (208, 212), (208, 216), (208, 240)]
def r1sG : List Nat := [2, 2, 2, 4, 4, 6, 6, 6, 6, 8, 8, 10, 10, 10, 12, 12, 12, 14, 14, 14, 14, 16, 20, 20, 20, 24, 24, 24, 28, 28, 28, 28, 32, 32, 34, 34, 34, 34, 40, 40, 40, 42, 42, 42, 42, 48, 48, 48, 56, 56, 56, 56, 64, 64, 64, 80, 80, 80, 96, 96, 96, 96, 112, 112, 112, 112, 128, 128, 128, 132, 132, 132, 132, 144, 144, 144, 148, 148, 148, 148, 192, 192, 192, 192, 208, 208, 208, 208]
def r2sG : List Nat := [18, 66, 130, 36, 68, 22, 38, 70, 134, 72, 136, 26, 74, 138, 44, 76, 140, 30, 46, 78, 142, 18, 22, 52, 84, 26, 88, 152, 30, 60, 92, 156, 36, 160, 38, 50, 98, 162, 44, 104, 168, 46, 58, 106, 170, 50, 52, 176, 58, 60, 120, 184, 66, 68, 72, 82, 84, 88, 98, 100, 104, 224, 114, 116, 120, 240, 130, 136, 160, 134, 140, 164, 196, 146, 152, 176, 150, 156, 180, 212, 194, 196, 200, 224, 210, 212, 216, 240]
def mpG : Nat := 0xffffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_254.map (· &&& dom_254)
def goalM : Nat := goal_254 &&& dom_254
def NN : Nat → Nat
  | 6 => 11
  | 7 => 14
  | 8 => 5
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xea40c9fdcffb392572190b086104c86f5b53455f3bd561382bcc35bd232d2466188a47b60d620bd30c0b8164
  | 7, 0 => 0xc5874b63b3f14526b13a8212a5a6dd9aa22457bd9bcdccdb8eec001482f6b55c798b18a86cf3105c615f6be4549755d532ed5ec712ab2594
  | 8, 0 => 0xe8fb7100ba49dbce74a159eb4a7a4f0b285923f9
  | 9, 0 => 0xe411b243
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5050505050505050505050505050000050505050505050505050505050500005555555555555555555500005555000055555555555555555555000055550000550055005500550055005500550055005500550055005500550055005500550050505050505050505050505050505050505050505050505050505050505050504444444444444444444444444444444444444444444444444444444444444444000000005555555500000000555555550000000050505050000000005050505055555555555555550000000000000000555555555555555500000000000000005555555555555555555555555555555500000000000000000000000000000000
  | 0, 1 => 0x5050505050505050505050505050505050505050505050505050505000000001111111111111111111111111111111111111111111111111111000011110000555555555555555555555555555555555555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500000055005500550055005500550055005500550055005500550055005500000000555555555555555555555555555555555555555555555555555500005555000000550055005500550055005500550055005500550055005500550000005500005555555500000000555555550000000055555555000000005555555500000000
  | 0, 2 => 0x555555555555555555550000555500005555555555555555505050505050505055555555555555555050505050505050555555555555555555555555555500005555555555555555555555555555000000000000555555550000000055555555000000005555555500000000000000000505050505050505050505050000000005050505050505050505050500000000555505055555050555550505555505055555050555550505555500005555000055550055555500555555005555550055555500555555005555550000555500000055005500550055005500550055005500550055005500550000000000000000
  | 0, 3 => 0x555555555050505055555555505050505555555550505050555555555050505055555555555555555555555500000000555555555555555555555555000000005555555555555555555555555555555555555555555500005555555555550000555555555555555555555555555555555555555555555555000000000000000055555555555555555555555555555555505050505050505050505050505050505555555555555555555555555555555555555555555555555050505050505050
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x851061801d0a291c103a24520c207444830c00e86146f081d06291c103a1a41a4207430835840e851069081d0628ce10398a4188207
  | 7, 0, 0 => 0xe218520f408da1a520c20843083d06008428a41e8208429a520c208418b920c208430b820c208022e520c207434b620c208021841860070214520c207aa0c520c208430a4186808021851cc207
  | 8, 0, 0 => 0x430b620c208ea18520c208021a520c207e218520c208430a41e8208
  | 9, 0, 0 => 0x218520c207
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 39
  | 7 => 44
  | 8 => 44
  | 9 => 39
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xff0e03ffffffff0e200000fffe03ffffe000ffe00000000000000f1fc0fe1ffe0000f1e000000000f1dfc1f800000000001e3c001e39e7fffffc00000000f1dfc1f8ff0003fff0000000000000fffffc0000000000000000
  | 0, 1 => 0xff0e1fffffffff00000000ffffffffffe000ffe00000ffffffc38fe000ffe00000f0fe03c38fe000ffe00000fffffffff0e03f00000000ffffffffffe000ffe00000fffffffff0e00001e00000000003fc0fffff00000000
  | 0, 2 => 0x3ffffe000ffe00000fff1e3fff00000f1dfc1f8fffe03ffffffffffe00000fffffc03f0000000000000ff0003ffffffff00000000fffe1fffffe000ffe00000ffffffffffe000ffe00000fffffffff0000000000000
  | 0, 3 => 0xf1e3fc0ffffff1dfc1f8ff0003ffffffff00000000ffffffff8fffffffe00000fffffffff0000000000000fffffc00000000f1dfc1f8fffffffff00000f1dfc1f8
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xdd0e1376ddbdba0e201a03ffff03ffffec98ffea9ab3442449124f1fc0fe1ffe0022f1e089224245f1dfc1f811122444913e3c127e39e777b76c01200000d95ba5b4ff8103fff4089045089292fffffe2008912288112504
  | 0, 1 => 0xdd0e1f76ddbdba0c003606eeeddbbb6ec182ed818610ffffffe38ff52afff32d25f0fe03c38fe408ffe20821bbdbb6edb0e03f018001defffffffffffdbafffbbfb7bbdbb6edb0e03a01e001b7884893fc0fffff20844048
  | 0, 2 => 0x1dff76c9877ea9ab3fff1e3fff64ad5f5dfd3faffff93ffffffffffeedafb77b76c03f00000cd19b796dd081376ddbdba04001202fdfe1ff7dffdbaffe23e27fbffb7efbfe43affe209b7bbdbb6edb0803201000196
  | 0, 3 => 0xaaf9f3fd2ffffff1dfc1f8ffc993ffffffff658cd2daffffffff8ffffffff76d6dfffffffffc99b2cd19b796fffffea92ad367f9dfe5fcfffffffffedbf7fddff7fe
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 88 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 88 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 30 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 30 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 30 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 30 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 5 => 2
  | 6 => 23
  | 7 => 118
  | 8 => 52
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0x648b6d2b179b7f58
  | 6, 0 => 0xf2db7923f27c39bae411b243ab5c2a498d3b3e0772f05993715b1cd36055c07e58606b31501b7a8c4539388e4237ff8d4216136b3dbfa1d73b49a3213809e9ce359b92392ac5ac062668c56124bc134124739682179b7f5808216204
  | 7, 0 => 0x4fa74af44cd840594c333f9c4ad983764a99f79e4a91fe42464c7369441ccdee428410183fb389a43f4d9cee3e5d02f93c02ad863bdbadcb3bbefbc43a4cdf17382f23d636f7cdec353d770e3478c96d33d603ac33a230bf323788be3182e16830f80da02ff8865d2c64f2012b3eeb7f24b2a8172311e96f22dd5a8421fb517521dfcd2d20c6b4c020a759191d08677b1c53db411c4b1ee819d9618b19a29a69194660a6165579b011d445e3118105ad105c15170fea26a20f35b0280ed00cdf0eb9e51c0d770f790d1607760b24adc909b3976f094fee3f084e1c6f048a0dc50485143d0414f44202cf9dfd01dd217800f35354007c0bab0050bebd00473f7f
  | 7, 1 => 0xf39b0590f27c39baefeea583e708514fe411b243d1a956a4d0690450d00e2383cc4a3006cb1cc072c30a8ef5af84fc5bada26bc3acbf899aa892d60da6cfec659fc75df39ebe367e945735d09354edb792164aab9115bd46901cba208ee04e3a8cf7d7fe8b4679f989b4f4638864fbd486aafa678629986a8097d02f7fcc6d6f7e1216917d4ae2237a6fbe5d793f93257913c25c7907bc4778bf71b97394d9c172de9b6c6f70731c6b26c63967bd9842617215ea5fca34925e8a95065de56c35582529dd56e0f16055cae63053e4761752685ec3501b7a8c
  | 8, 0 => 0xf312a16df0082887eb2bd7e7e5c1c5cfe411b243df3934aad04f4be2cf66bfe1c83095c9bc4898b1bb3b3102a75f4549987bf6f58d41201786b9bf387fcc6d6f76b7ea947673bbb27630300973fa661d714d79d06a9dfbf964d8d4a5617215ea5fca34925cc3a367520cc69b4c2153ad4b5f37504af7b5234988497746d0a4a944bdf3b943dfa91a42b8d96b41be95b93fb389a43950b75036f7cdec35723b072f03f0792991d0a928862509276ebe2a2592036824d69e1c2497b16219d9618b15ef81d611b24bec0f35b0280cf8e798
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x100
  | 6, 0 => 0xb02020900060008000804030c030a000b020806000003
  | 7, 0 => 0x2050a020303070b00030308080803080200070704000202040b00000b0007040000050b07030000080707070505020500000503080000000d050804000007080000020005040303000805020007000702000203040504040c090707080b0e0d050400080000000004030c0500030b0400070a0800
  | 8, 0 => 0x2000808020802020200080802050204020707000000080505080208000802000202020207080308000202020008030702000808
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 5 => 3
  | 6 => 43
  | 7 => 108
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xcec65b2aa07cdd719fb9074b
  | 6, 0 => 0xe5a50180d8fcd8a5c7156a46c41e5e4abcaf95e8b7e54e92b3734758ac9ed7329bfbd7739254ea328b5d16b88688223e82f6b55c78d0039c756a17fa6fc9f35b6d3c5f24615f6be45f42985f5d9d63ca5be2f10e58da874f561af21052ae44b24e079d954bfa5dc1451e7d2a41a29bb2408c7d5d4014a4033dcf23793760fa0e3456dc103325f6382e60adab2136db661e71431d169d3d9e15c9b0960f658a0f0e2c3e7a0e1e54ef061235fc
  | 7, 0 => 0x5fdfcc485c3d741f5b752061595b8f6358c53a1a56db92b053d12fba537d21de4f80dac14d85560c4cd6097f4c982f514bba63664b601ecd496a84ba415e4610406f38513f3f73f23b34a84f3762787d36fd7a9636c4e6da36c3ab7033edaf3632fbccf232b02b2b31d764e92f93adf32de5d56d2d078ace2be0bb1f2b57dc4b2a02418a290b9e9d28db6b58270a57ab263c507425dad0362521960c23f28ca4201fafa01e251a0a1dd0c7bf1d08ce3419350d2018f25f59174966e01564dd8d141f6ee513910e821194b01510969fde0f49e25b0dbf93160d4ba7c807708f0a0747923c0703635a06bfd7b106348cac053c1a040301433f02bfdd6001da560b
  | 7, 1 => 0xfe4358a4f7eb9f71e093f5c1ddc9e90cdcc368abd5cfc86cd57312c9d0fc92accfcbc12acf9e85a7c8e1074fc408dd02bf8665a1be953835b7fe65d2b371f356b34eda5ba8455ee3a10b151d9e57a0c99d65b5b2956c8d419462ec428e7e9b358c3fff668b18165f87f2a09083a24915790d65d8734b622f72791065700b8f9d6f2dcfda6ed0e3926eb420806b6f742167582d6d67102fd96587c18d62dfc8b661ad6224609ecb886008c9165ff66789
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x51cd1200158d1200158d1200
  | 6, 0 => 0x158d1200000d51040009610550c8d20026515202000d5105000d51040010d10050c8d200000d1100000d710400096105000d110363c552080010f100000d1100644952020010f100000d510361cd120865c91202001511030011510726515202000d1100000d5105000d710526515202000d1103001151072691520800151103
  | 6, 1 => 0x269152082691520861cd1202000d110026915208158d12000005310400091107000d3100158d120061cd1208
  | 7, 0 => 0x951020009510200091107000551020010d100000d5108000d5108000d1102000d110300151107000d51050008110000115102000d11030009510200011100000511080008d1000011510800091102000d1102000d11030009110200095102000951020009510700095107000111000008110000091107000511080000d100
  | 7, 1 => 0x91102000d5103000c5108000d51050000d100000911020005510800151108000d110200091107000d11000000d1000000d10000091102000d11030010d100000111000008110000091102000d51050009110200051102001151020000d100000c510800091102000951020009110700091102000911020009110200055108
  | 7, 2 => 0xd510200081100000951020000d100000c5102000d51040011510800091107000511020008d10000115108000d110300091107000d11000011510400095102000c5102000d110000151102000c51080009510700115108000c5102000d110800151102000551020009110200115103000511080008d1000009110200095102
  | 7, 3 => 0x95102000c5108000911020005510800115102000d110000091102000d1108001151020005110200051102000d5104
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 8 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_236 roots_236 7 s ws hint
  | 1 => checkCutEntry true dom_230 roots_230 7 s ws hint
  | 2 => checkCutEntry true dom_246 roots_246 8 s ws hint
  | 3 => checkCutEntry true dom_222 roots_222 7 s ws hint
  | 4 => checkCutEntry true dom_126 roots_126 7 s ws hint
  | 5 => checkCutEntry true dom_190 roots_190 7 s ws hint
  | 6 => checkCutEntry true dom_206 roots_206 5 s ws hint
  | 7 => checkCutEntry true dom_250 roots_250 7 s ws hint
  | 8 => checkCutEntry true dom_238 roots_238 8 s ws hint
  | 9 => checkCutEntry true dom_174 roots_174 5 s ws hint
  | 10 => checkCutEntry true dom_186 roots_186 5 s ws hint
  | 11 => checkCutEntry true dom_154 roots_154 4 s ws hint
  | 12 => checkCutEntry true dom_110 roots_110 5 s ws hint
  | 13 => checkCutEntry true dom_90 roots_90 4 s ws hint
  | 14 => checkCutEntry true dom_218 roots_218 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_254 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_236 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_230 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_246 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_222 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_126 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_190 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_206 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_250 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_238 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_174 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_186 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_154 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_110 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_90 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_218 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_254 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_254 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffffffffffff0000000000000000, 64), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_254 == dom_254) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_254 goalM v ys) : RunD true dom_254 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_254 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 11 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 11 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 14 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 14 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 5 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 5 0 = true)
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
  scr true dom_254 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_254 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_254 roots_254 goal_254 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_254 goal_254 := by
    have h0 : isConstB dom_254 goal_254 = false := by decide +kernel
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

end S_254

theorem lowS_254 : Lower true dom_254 roots_254 goal_254 10 := S_254.noCircuit

namespace S_255
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 129), (2, 18), (2, 66), (2, 130), (3, 19), (3, 35), (3, 67), (3, 131), (4, 36), (4, 68), (5, 21), (5, 37), (5, 69), (5, 133), (6, 22), (6, 38), (6, 70), (6, 134), (7, 23), (7, 39), (7, 71), (7, 135), (8, 72), (8, 136), (9, 25), (9, 41), (9, 73), (9, 137), (10, 26), (10, 74), (10, 138), (11, 27), (11, 43), (11, 75), (11, 139), (12, 44), (12, 76), (12, 140), (13, 29), (13, 45), (13, 77), (13, 141), (14, 30), (14, 46), (14, 78), (14, 142), (15, 31), (15, 47), (15, 79), (15, 143), (16, 17), (16, 18), (20, 21), (20, 22), (20, 52), (20, 84), (24, 25), (24, 26), (24, 88), (24, 152), (28, 29), (28, 30), (28, 60), (28, 92), (28, 156), (32, 33), (32, 36), (32, 160), (34, 35), (34, 38), (34, 50), (34, 98), (34, 162), (40, 41), (40, 44), (40, 104), (40, 168), (42, 43), (42, 46), (42, 58), (42, 106), (42, 170), (48, 49), (48, 50), (48, 52), (48, 176), (56, 57), (56, 58), (56, 60), (56, 120), (56, 184), (64, 66), (64, 68), (64, 72), (65, 67), (65, 69), (65, 73), (65, 81), (65, 97), (65, 193), (80, 81), (80, 82), (80, 84), (80, 88), (96, 97), (96, 98), (96, 100), (96, 104), (96, 224), (112, 113), (112, 114), (112, 116), (112, 120), (112, 240), (128, 129), (128, 130), (128, 136), (128, 160), (132, 133), (132, 134), (132, 140), (132, 164), (132, 196), (144, 145), (144, 146), (144, 152), (144, 176), (148, 149), (148, 150), (148, 156), (148, 180), (148, 212), (192, 193), (192, 194), (192, 196), (192, 200), (192, 224), (208, 209), (208, 210), (208, 212), (208, 216), (208, 240)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 9, 9, 9, 9, 10, 10, 10, 11, 11, 11, 11, 12, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 16, 16, 20, 20, 20, 20, 24, 24, 24, 24, 28, 28, 28, 28, 28, 32, 32, 32, 34, 34, 34, 34, 34, 40, 40, 40, 40, 42, 42, 42, 42, 42, 48, 48, 48, 48, 56, 56, 56, 56, 56, 64, 64, 64, 65, 65, 65, 65, 65, 65, 80, 80, 80, 80, 96, 96, 96, 96, 96, 112, 112, 112, 112, 112, 128, 128, 128, 128, 132, 132, 132, 132, 132, 144, 144, 144, 144, 148, 148, 148, 148, 148, 192, 192, 192, 192, 192, 208, 208, 208, 208, 208]
def r2sG : List Nat := [17, 33, 129, 18, 66, 130, 19, 35, 67, 131, 36, 68, 21, 37, 69, 133, 22, 38, 70, 134, 23, 39, 71, 135, 72, 136, 25, 41, 73, 137, 26, 74, 138, 27, 43, 75, 139, 44, 76, 140, 29, 45, 77, 141, 30, 46, 78, 142, 31, 47, 79, 143, 17, 18, 21, 22, 52, 84, 25, 26, 88, 152, 29, 30, 60, 92, 156, 33, 36, 160, 35, 38, 50, 98, 162, 41, 44, 104, 168, 43, 46, 58, 106, 170, 49, 50, 52, 176, 57, 58, 60, 120, 184, 66, 68, 72, 67, 69, 73, 81, 97, 193, 81, 82, 84, 88, 97, 98, 100, 104, 224, 113, 114, 116, 120, 240, 129, 130, 136, 160, 133, 134, 140, 164, 196, 145, 146, 152, 176, 149, 150, 156, 180, 212, 193, 194, 196, 200, 224, 209, 210, 212, 216, 240]
def mpG : Nat := 0xffffffffffffffffffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_255.map (· &&& dom_255)
def goalM : Nat := goal_255 &&& dom_255
def NN : Nat → Nat
  | 7 => 16
  | 8 => 35
  | 9 => 17
  | 10 => 4
  | 11 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 7, 0 => 0xf2390382de841c75c9166a93c6474135b401ab20a8ade91fa46da7258ab7d64477aa1232556f67ba533189914666287e41c50edb3a6d508537dad3bb22f4b815
  | 8, 0 => 0xfef9ad76fea4e0bdfd899579f715a97df4e70b0aebe6df90e954edbad837bac1d82a0458d7e5e53ad6e99e60cc7f7a77c2018433b4317bbaa8445983a7fc7d9ba4041789a211c10f8392ccb970ec327667dfe8e8678326aa5d8a74d35416bf3352eec5cc512e1a84408895233ff37f21396972d23799bf0b3619528928a74f2a1ca24d670a6d310e07df098e
  | 9, 0 => 0xfc79882ef47d7b6eef734366db29e05ad29dd023c283664bc0a10e50bdae36807082a2da66102e74572f07c653ad2f97493863102e6b228a23a46f861c38bdcb0831c878
  | 10, 0 => 0xcb236c0ea36829b1194efb710297ddda
  | 11, 0 => 0x1f6d511d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | 0, 1 => 0xffffffffffffffffffffffffffff000000000000000000000000000000000000ffffffffffff0000ffffffffffff00005555555555555555555555555555555555555555555500005555555555550000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000
  | 0, 2 => 0xf0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000ff00ff00ff00ff00ff00ff00ff00ff000f000f000f000f000f000f00000000333333333333333333333333333333333333333333333333333333333333000000ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000ff000033333333333333333333333333333333333333333333333333330000333300000033003300330033003300330033003300330033003300330033000000330000
  | 0, 3 => 0xffffffffffffffff0000000000000000ffff0000ffff0000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff000000000000000000000000000000000000555555555555000055555555555500005555555555555555555555555555555555555555555555555555555555550000ffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff0000
  | 0, 4 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000ffff0000ffff0000ffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff000000000000ffffffff00000000ffffffff00000000ffff000000000000ffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffff0000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000
  | 0, 5 => 0xffffffffffffffff0000000000000000ffffffff0000000000000000000000000000000000000000ffffffffffffffffffffffff0000000000000000ffffffff00000000ffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffffffffffffffffffff00000000ffffffffffff0000ffffffffffffffff00000000ffffffffffffffffffffffff00000000ffff0000ffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f00000000ffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 7, 0, 0 => 0x1ca24c14d6c181ca24c15a04081ca24c14464181ca30445804081c61445c158081c614454158081c614454204081c61440d404081ca24c11304081ca30511204081ca30445004083c7289305101838728930534181ca30510b04081ca24510804081c61440c20408
  | 8, 0, 0 => 0x7189144541021c1ca24c14d04091e528930444102401ca24c14d040880718914454102401c630510204081e524c14490102631c6245103040980718c14489602611ca24c144040900728930444102201c630510204097077c9305101025e1c624511504091ca24c144741025c3872893051019
  | 8, 0, 1 => 0x1ca24c144a81024718914456204091c62451290c102401ca24510304088071891440e202681c630510158091e528c144601024718c1440a204098072891440c102631c6245115040970794930510102631c6305101580900728c14460102231c630510204099c728930510102472893051260409
  | 8, 0, 2 => 0x2b1ca24c144040978718c14408102403872893051018
  | 9, 0, 0 => 0x8c7189305122040a0001c6245103040800718c14488158090201c62451030409007b8624c1440409007289305124040900729f24c14404090231c624c144040902d1c624c14404090001c630510158088e01c624c144040a00794a24c1440409007189305101b00901c1ca24c14404098de1c624c144040a0201c624c1448809
  | 9, 0, 1 => 0x201ca24c1440409
  | 10, 0, 0 => 0x7871893051010247189305122040900728930510102201c624c1440409
  | 11, 0, 0 => 0x1c624c1440408
  | _, _, _ => 0
def stateW : Nat → Nat
  | 7 => 52
  | 8 => 58
  | 9 => 64
  | 10 => 58
  | 11 => 52
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffc001ffffff80000000000000000f83fe00f83c01ff00007fff0000000000000000000000000000f87c0000ff01fc0ff03f800000000003f00000000000f0f1e3cf0f3c7ffc0000ffffffffffff80000000000000000ffffffffffffe0f007f80000000000000000ffc0000fffffe00000000000000000000000fffffff00000000000000000000000000000
  | 0, 1 => 0xffffffffffffffff00000000000000000000fffc01ffffffffff0000000000000ffffffffffc01ffffffffff0000000000000003e1f00000000000007c3cfffe000fffc00ffffffffffffe0f007f803f0000000000000ffffffff83c01ff00007fff00000000000000000000000001f0ff807fc0fffffff000000ffc1e0fffffffffffff83c30000000000000
  | 0, 2 => 0xffc1e0fffffffffffff80000000000000000ffffffffffffe00000000000000000000000ffc1e0fffffffffffff80000000000000000ffffffffffffe0f007f80000000000000000fffffffffffffff0783ffff0000000000000ffffffffffffe000000003f0000000000000fffffffffffffff00007fff0000000000000ffffffffffffe0f0000003f0000000000000
  | 0, 3 => 0x3ffff000001ff00007fff0000000000000fffffffffc001ffffff80000000000000000fffffff003ffe0000007fff0000000000000ffffffffffc01ffffffffff00000000000000000000fffc01ffffffffff0000000000000ffffffffffc0fffffffffff0000000000000fffffff07c3fe00ffff80000000000000000ffffffffffffe0f0000003f0000000000000
  | 0, 4 => 0xfffffffffffffffffffffff0000000000000000000007c3fe00ffff80000000000000000fffffffffffffff00007fff0000000000000fffffff003c000000007fff0000000000000fffffffffffffffffff80000000000000000ffffffffffffe00000000000000000000000003ffff000001ffffffffff0000000000000ffc0000ffffffffffff80000000000000000
  | 0, 5 => 0x3ffff000001ffffff800000000000000000000000ffffffffffff80000000000000000fffffff003ffe00000000000000000000000003ffffffc001ffffffffff0000000000000ffffffffffffe0000007fff0000000000000fffffffffffffffffff80000000000000000fffffffffffffffffff80000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x8411088ffc101ffffff90102222408222482f83fe00f83c81ff20107fff1110244111049108442210881222f87c088aff01fc0ff03f808422110847f01108848445f0f1e3cf0f3c7dec1008deefdbbbeef681000000c99000192bdf77bbbddfb60f007f80300000000eeefb6ffe0100fffffe80422021204444891444910fffffff84020108844242008889122888224
  | 0, 1 => 0x7bfdfef77bbdbdff7776edd777ddb00000007bfd80f77bbdbdff333264c3334cbf7bddeef7b801eef77b7bba0b0a1420b0428213e1f02110244411097c3cfffe000fffc00bdf77bbbddfb60f007f803f0000000ffffffffffffffc3e81ffa4527fff999936699926d4208844422049f0ff807fc0fffffff000000dec1e0fdeefdbbbeef683c30001fff0003ff
  | 0, 2 => 0x9cc160bdecf93bbeef6800000004080003b6bdf77bbbddfb608006200200000000cccb34dec1e0fdeefdbbbeef683000001dbb0003b6bdf77bb9ccf920b0076800000000008883b6ef7bbddef77eddd0783f77500fe03f00fc07bde6733bddfb6000020002f0000000dddb7def7bbddef77eddd0602777500dc03700d805ad73399ad57a40d00020035000000000d805
  | 0, 3 => 0x1feff0000017fa4525edf999936699926dfffffffffc301ffffffd210aaab52aaaa6a67beef77003efe0000006fefddddbf7dddb7dfffffffffff81ffffffffffbbbb76ebbb6ef000000073b800e6733939ba0302040030408f7bddeef7b80feef77b7bba0f0e1c30f0c38fffffff87c37f08dfefc200eeefdbbeeefb6bdf77bbbddfb60f0072003f0000000dddb7d
  | 0, 4 => 0xffffffffffffffffffffffffffffffffffff000000003c17e005bad80006666c99666d92fffffffffffffffe6727fffddddbf7dddb7d7beef77003e800000006fef999936699926dffffffffffffffffffff330eeefdbbeeefb6fffffffffffff88c6626320cccd9b3cccb34001feff0000017fbddfdedfbbbb76ebbb6effff1188ffffffffffffb1306666c99666d92
  | 0, 5 => 0x1feff0000017fbddfd210aaab52aaaa6a600000007bfdfef77bbdb1306666c99666d927beef77003efe0000006320cccd9b3cccb34841feffffc101ffffffdedfbbbb76ebbb6efffeef77fffffe8042206fefddddbf7dddb7dfffffffdeefdbbbeef6c3008889dbb8883b6bdf77bbffdfb7ffffff90302222408eeefb6
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 144 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 144 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 47 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 47 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 47 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 47 then wireAt i else 0
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
  | 7 => 10
  | 8 => 91
  | 9 => 96
  | 10 => 113
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 7, 0 => 0xfa9a294adbe2be23d5aa71aecc05d77cc86088e7a3807c606756a0405d1239be1f6d511d0e1a2308
  | 8, 0 => 0xba64b203b850fbd8b7ddfd77b5d6a5b6af0b1556a7fb1282a651a4d9a2d417ce9df619b097c9c31a976d48b99537ca128e1504c58d5a75798c1c4e3a8bb51aaa8a7898f28359de9e833f2ff182d0fe927f929b2f7aa4f92f7833e3416f36b0296eecb8e56cee1ad7662cd93361ab53ea5c0c8db054e2b2a3527b6902521906f54d1ae01e476fa00b473e11b846d9579c426403a441e6f7d941b1d28a413a8b133fddd2dc3bcaa43a361620bd343963ef2fdfbe6d2cbb554d2a37eab7233bfa9f21e050f020b503571f6d511d1da2926f1c1dfac11b09043c0f60c6a70f3751c70e4db3960e1a23080c17388b0746f4fe0403906303e10b5703cc464101c32f09
  | 8, 1 => 0xfe397708fd0b8383fa225125f75c5f2cf750ceb8f24552e5edb18b86ece409cbeb988e6eeb67d459ea1b0b0ee695e5dce04c56c3ddfaa7d2dcfd8208dbe2be23d5aa71aed53ef539d5266f1bd2f251d8ce4891b0cc05d77ccb787009ca6175f1c5a3edf4c1eec261bc05b5d9
  | 9, 0 => 0xaf972648af29c7ecae4df8cbace6bcecac3bc4b1a98fdd4ea37187a29d8f3ec09d49d40597a7e668958d0bcd9292c065924c00cd8cba6a0b8c2cc1a6883b176587dbe3eb8692b66e85b0f0db834ed69f7833e341750b0e9174ecd1bc7317525d6e39813c6909558d666f4b85661accf465a074b461a6784e60c5b44a5edf0c6d5e805f3a5ccfcf0f55e2bb385545f83f54e2b2a353f004e5527b6902518814b64f1e44a24c5d1356493abb31473e11b83f371a6d3cca190639e564f235a5f5bf32a3a9f22de67cfc2ddad6bb2d8ab5e227fea69c1f6d511d1f2e50ca1f172e521b92fbcf19e43489191f89fd0e4db3960e1a2308097af5f503e10b5700cd1f2c
  | 9, 1 => 0xfe3183f3fc2c2a7afa8479a1f7ed88bbf49d87aef34dbfb2f1b6e41af1784053eb4b8cbfe836d235e70b9814e695e5dce27472f1e090a9b5e0076644df399415daafb44bd6764196d5aa71aecacc1c0aca539acdc9c07299c958ad60c86088e7c59effaec5051662c429297cc41d0945ba03ce87b9ffcdd1b265fb1eb246bc31
  | 10, 0 => 0xa8219417a537aa92a1ed8704a11054179d24802d9b4efb7999fba56c998e0a2996771fec950d0fcc90e08e6289cdb3478225b50280de14227d6b3a457947c50776e3cf357667409975d8da117530eafc711baf256f847ff062552b8f6080f9fa5ccfcf0f5c5449ff5c0c8db059cb79fc527b690248bc19ea4433a3a640d73a273e0a25a03d00ae463c2c192b38dd38fa37ccc8093709f1263575c9ce3152270e2c2c4fd02bba0d512b947a6c2901cdd6269fe8cd244273a01f6d511d1ee53b201da2926f1bb8b71b1737fe4215d15dda1236b6d810a93c2a0e4db3960d17918c0af82e250ac4f0c905f2eeb103e10b57030b82f4024a802601aca8ac00b1f0b4
  | 10, 1 => 0xfc2996a1f9999b28f6b19054f3259d20f0f38f97ee4ccd72ee3bf4f4e9d94aa5e8a7c67be695e5dce27472f1d8c448a3d736708ed6c89b86d575d99fd55502efd457dbf1d159d23fcfa48b3ecfa2954ece7d68dace28912fcbaf4de1c9158e5ec7a6811fc53ff79ac52151b2c510e825bfcfd872bfabba69bec9ac88beb365c7bdd6512bbda81d4fbd2514a5bcfc20a8ba64b203b84e0c67b7614604b3c975d4b24eb633b1430605b076404daf47401faf38c163a98fdd4ea974856fa93e40ffa8428216
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 7, 0 => 0x504040701080c0b0a07
  | 8, 0 => 0x407070603070a0403040106020d0604040e060a01070204050a000606010a0205010e0705090f040100010a0d020701030605030e0e060909060206040903090a0d070a0a0d010e01020601050a06070d04070607020101060402
  | 9, 0 => 0x6010a0401060306060a0606090a090104030402070606010903040206040e040603060a09090306030706060609070709090107060306060f04090609090207060102030903060203030d090909010609020909010a0606010a0a0607090606
  | 10, 0 => 0x20704010407070a0a06090a040a04070a04040a02040a020202070a02070101070101020607070701020a070a0304070a020401040a0207040a0a0702070a040a02020a010a0a0204010a09020304010a020402020a02070a070a020202010a02060a07020a01060a0204070902010a07
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 6 => 1
  | 7 => 103
  | 8 => 686
  | 9 => 552
  | _ => 0
def CH : Nat → Nat → Nat
  | 6, 0 => 0x6edfd472
  | 7, 0 => 0x9fe99b359fcfb9199ba2fef5994b39ea98667b3098650577905143be8f9fe5ce8c9052f48c8260728bcd7c1184dc96c77f59b8147e9b0e457b1a92a9796b3fd5783a2e0f6e6f55996acddcca68bb5c6e653ee07d653698166220bcb5615c4b6a572f07c6570e0b114d5c21814cd070204b75c44f421e4a2c419b97b74198e547415b73493ed46e593e3d8f213cca6e183ba21f9b34e6c5f7329f8f25304f81b72ef5da862d619f7c2cd5c158272953071ffc4a331ecd016e1d20d2671caf74be1c2d94641ac9d064194efb7116fa0f2c16df49e514458c8913b40da60f42ace50ce825c40c9f0df10c9c02490c9a8c900b4171060832a13f07fbcd5c03c78e25
  | 7, 1 => 0xff874c2bfcf053acfce51f02fc466d9bfb81466df37d46edf2d251bfef734366eccddcd2eb7d5139e6ab4c81e596bcd3e2e78ee0d96c1f2fd5a19f0dd0a906f1cde8c313cd25ec30c66bb315c3fc932dbfeb5a3bb273163ab181e4e2b13c37feae4eb068adfd8a20ac99ad36ac4cb62eabe8b06caa6711d4a86e466ba83e0fd0a52c6164a4a1b1e5a1a096a1a17c78aea10b4871a053b604a048585c
  | 8, 0 => 0x15204631143995ef13b40da612a8a24f1296d7e7126db8481247f564124247201234c7221169128110dd2c70109fa0c01085ff4c10004e150f5889350f42ace50e8a522f0e1017e90d16b9980d06a08f0cd00b4f0c62e08a0c19929a0b85a51e0ad17cab0a571ebe0a01289109b5e5c2097af5f508e32b4308deefa0083844df082f5dea0807c58207fbcd5c07d2ba52079886ab07756dfc076641e707644bf7076131c1075e7faa07299a29070fe36f068d9d5b062eadbf0629796c05ea47d804b76ac20421e1ee035231d002e522b7029b98e1028dd2b302546a5e02155176021372cc0200171e01a904a1019b635101581957012f0a1e00d7450700216367
  | 8, 1 => 0x2d0961862cf80fe02cd5c1582ccfc5bf2c5a3c482c127ff92c0f69ff2bde59052b65df572b63c4a92aec18472ae753c92a54084b2a3ae3a02a1ea9a02a03e45929fcef8a28cf10c82896328f284cccde2795cb46277936f7274d051226bfc36b260e841b260367c225fdab9d25e8ad81258c36642536173324a0f90223cc9acd23a46f86230b2db922815b4b224df33221fca5ca219c207a217ef7d32117857520697d241fbecd5b1f92ba971e579c851e4ed70d1d77578b1d1b29391d017c281c81e42e1b5383e41aeea3ed1acc9db11a3dacd81a36299a199820fa190ffb1e18c20c33188c5e4c184ffae817843cc31744040116f9558215b968db1589afb7
  | 8, 2 => 0x4536dd45451100da44f2c405444f5eec434e8ff8431d44a642b9e4ce4238e3b7420500f3416d7d9a413cac9e4121a16e411fbc0c40de2da140625bc83ffa5bcc3f8a72393f70931c3e6510a73db4a55a3d5e7ca53c82b8ac3c60de7c3ba2c2003acd399d3a5994833a44ec6b3a0c36cf398fe0dc396e5f5539669314391c15e63881048d3854d87b37ed90d037d964c937c66f513707a55236abc35a3655143f365422c035d54466353af49734875112343f22d133eb4d4a331617af32b9e7fe326e7fd3325b1dd832481cc73246304a321ab82331dc616d315b51d13155370c30cba6933086ec43301281c12fe5bf5c2e6b228a2e4d7b4c2dcc38692d5e4dff
  | 8, 3 => 0x5f050c8d5e89a1515e619f765d86688f5d1a69df5ce49d425c042a495be8164a5aa75e9e5a1634bb59ebaf6d59d3a59059a54a42592147af589ee6ac57678593570841a656bfe428567d530a56769a5c55ee380455dbe02e556449185552c5b054939f89537a6dc45354c8e852ece44d51a5eb3251622995514990f85110b21a50e4066b5000b0104ff49e774fc4658c4f0903094ef9b4eb4e86dff14e7f7a7f4d9314834d712c8e4c5d13564b52383b4a7e49314a2a8a6c49f86d81499a85664989cc4c4975fffa496bb30449386310486af2d347b52adf47530f9646e9c17e46d1f94346a873e4466d32e2460f6a3f45efae3e45decc5a4594466a458b6d79
  | 8, 4 => 0x75cbdc4975ca2dfa75bc7674753d9cdb73edcfd47397ced7736e1bfa730a05f57301a9e971f3794d71e62ac371cbdc7671abe04171a71b9b71937e087116466070aa1b97709eefa37082a2da6ffc2dca6fe9610d6fcb66496fb29bc66fb1260d6f8e7eb26ece7c106ecba7cf6e7a53ce6e6526356e4bcbc56e48fda16dceb9e06cf8fcb16cbfc3f66cbe4e3d6bcda07c6b54edc26b1261256a65609b6a644d2e6a1d16916993fc7269647e716913ddb768c9e2e667543039672543246712fd7e66102e74659c8d646576eca76552a4c6651302156407df6863ee0679637bc3fa6356311563404ab662099ebe60c3847f5ff1d8c85fdd96b75f2f74c55f229c23
  | 8, 5 => 0x8d0212f18cb936ae8c5262a38c02505d8b6fd8838b5c811a8b3b8d4d8a6eaf678a6aa44c8a3d1fab8a05c01a89b122658949cb5f88e8c13d87fc5e668798d9148767384d87186f65861ced448617bb3184cc2ed8841372d483f63ec683453e5282867dcb8254a87c82414a5b820b986e81ade7e0819fa2e080d8b3fa807dd093807c3296807306537fb798397ef028787e0a433d7daaec077d410e0e7d3080f37bf55a4f7bd5d4567b860ab17b83a6937b7edaa77af5a94c7aacf7bb7a738f737a0f22d279aa80ad7995cf97797a77b87944a9f2794433487898f0d0788d10ed785b328a7848745f7827866077c8054077bbf26d7786314f76dd8482762ce29e
  | 8, 6 => 0xa372ac66a37187a2a334cabca2420bd9a236f0a3a1ebf81ba1a096a1a17f34f6a15fc488a048585c9feaef249fdbb2c79fc9a0f19faa7d879fa887979fa5e6059f8619e29ee5901b9ea5a36b9e835b239e2e83789e2104779db8c97e9d41d1069bb5402a9b85182e9b76c36b9b76797c9b295e5799682ef7993abb5a991b80a7989c7b1f983e55cd97ac73689738d28b96afebf7967b3569964f80349545e9e3954480de952743fb9516da6e9516858694e509e5949185b8941600a89411ea7893ce44599254bebb918d30a5918990bc90300aea90266821901f4e6f8f0a515d8ecf9ed18eb958108e6859338e50e56f8e473b808e01f2948dae0f988d2b06ee
  | 8, 7 => 0xbdd24957bdae3680bd72a784bc671912bc65109fbb5c2a42b9e76babb9df3ceeb8d936a7b8adb8c4b89fcacbb83cc47eb741e035b69bd825b63f6575b5871c1ab4d245cdb43f707cb41d3d7ab3e17825b31ff7d6b27a653ab154ea78b11a0306b115e57eb1097bb0b0e9b5dcb0969bfeaff599eaaf306439aea585deae28f742ae1831d6ade520ccad9a90baad20f65dacf2a1a5ace02137accc9f41aca1c7a6ac9091c9ab8b15a4ab899febab5e264faa4ccce6a98fdd4ea8dd65cea8ca3aeca8b4f641a83016bba7ec56c8a7463699a73c62d7a6ddb074a6ce8dcfa69aa70da5a7ed87a57bcbe8a561c2bca534e3a9a4720cc6a45dce3aa4541100a3b2169d
  | 8, 8 => 0xd3e6fda0d350c18ad311753dd2b5fcfcd2b48743d29e4429d29dd023d250726fd2048e56d1bd5c15d1b29af5d189fe40d14fc0d2d115b8b2d0958117d05de9bad031bffbd00b06aecf388de3cf3061b1cf00a749cebd8960ce38d695ce2fc90bcccec675cc2f88eaca54770ec9b063b6c96e24cec8a2450bc87e619ac81d50e9c7f37b04c7a3fbdac6b7829dc6043094c6022379c58d1ce8c51a0d6cc50cfff4c4a379f7c3ec3aeac353b1fbc348211ec3401856c32b8f69c283664bc215aa33c1ea247ec1bcd663c1b7734fc1b60901c17784ecc0f981e0c0a10e50c07b173fc05045fcbffcce0ebfe7efcdbf337efabf11a48fbf0d4ae0befaded0be6ee909
  | 8, 9 => 0xef344313ef22fcadeeeb2d69eedeb87aee462fc2edef1a63eda884b8ed2f6a06ecc4bb7aec644d36ec02c6eeebbea964eb98ee18eb5357f2eb265a19ea2bfe07ea106cdce9f6b8aee9222b2fe904bcaee837f6f6e73df08be708f6c8e6fa780ce6eb7e95e620e60de60e81a1e5d75023e54e07b7e4906ec2e4587c54e3fd7b5ae3d480f5e30fe708e27472f1e23ca921e2187c89e1f1d8d0e15193f7e1252598e10d5d87e0fff7a8e0dd8c77e0af2e73e04a86a4e0257086e00438bfdfe34ac0dec1d733de53a5dfdd882401dd7b3a47dd1d83d5dcb30a4bdc7d39addb29e05adafe206edacae312da725409d9af3dadd9620c8fd50b8aaed4e636d6d4124cd6
  | 8, 10 => 0xffe5e43dffcc6111ff6837c8ff458b01fef358bdfe07260efdc2b5abfda55941fd01ae43fcedfcd1fce3085bfbeae025fbe04661fbbfff9afb9fdc55fb9a6cb5fa713922fa13193df9f0e2c2f907c01ff849f086f8487acdf7918f1bf76d7112f6de9a63f6c3e0fef6a5db16f68b6331f6751c70f656733cf5e43e51f569d3f8f5038de9f4e6cb4ef44865e9f404e070f3a63600f3336c20f29d2a0ef22668acf1cf330ff1b6e41af144afc5f0bfc72bf069a712f00fc310
  | 9, 0 => 0x218ef5022134b25d211f58c120e705ed20819321202b3b031f56a5e81f49d40d1df67e001d88e2bd1d17ab2e1cd1e8e01cd1ca161c07c5b71b3a9ae11af754c61a71f8801a347de31907e86018c6e57418a0568b17843cc3168d98f91650a440159a616f14db66f614bf707e147cb3cb12bc92881247f5641217f33111568fa51119a896101f7e3d0fb3082e0f56dc8d0ee49a0e0ebf07290e0b46800dc88bdb0c3714eb0c35eff90c2c5a930c18612c0b8cd94f0a95275e09ca758a09abc96f0885ea00082f5dea080a64f007c2a8a1076d005d06f93be006208d9605f82401058194ed04d9d87904d8ecb6020fc7dd01fe9c0d016612d90098cd94008f8ece
  | 9, 1 => 0x42c4851c42ae3e5b429dc43e422d3add41d129bf41a2f5e3411fed3940f6f93c40c32abd3ffa5bcc3f7ed6bc3e885f1d3e754a293e6b2bf53e5f8a973cf606b93c96a9533c48e4fb3b5c1e98390d47f53851e57237ebcff437e2dc9737c44e6836e2589a36498ec73612712b360dc37f3583ce38353dde99347118e1334218b3333399f732e367cf32bee34e31ae725d30eb9b7a2f5774222eed66742ddbcff32d6f5e032d453d232d3919932c942f132c3d5aaa2c1c6cab2be6a6a72b74955c29eaf07929c2c5322932832629215536275e30632735db21260dfa2425e85f9825a510a0250b2cab24fddff824fa0fe62401c6e42299ea262292eba2221d5b8a
  | 9, 2 => 0x5afd5b105aeedc545ac3741a5a13e74a5a0e5bf259a54a425991cd565970b233594fdb83590366ce58a79f37589cd7dd585b77b95852b48558359b4e570a9e965635f45355ee38045554aad3552aa060552758b554f45bf054463be253f89d0753d9580253d7af0853ad2450539f63d2539d6de252af0cad5278416e522369c350edc5834fb8db124faa26754f56b8bc4ec6f49e4e5604884e4e73614da3a1f54d7165424d1066f24cc66f084ba159b3493ad02e491c2a46490bc0b948da9b1e486c9d15484a089f482a080c4824021047d283ba4705166a46f41ce345b1c05d45adbf94457fb84c4544251a4513c61e43f0410743cab10643ab86b743a692fd
  | 9, 3 => 0x79deac2079a1aca978379c89776568d2772075b475e9bbf5751e6a8e74ee682b74cba94f740b1b1f735c9c1073296f5b72e47dbd72c5259c7247a6067236cd8870f6128b70e20d1c70d76ca370c7031670c579896fd324366fba84656e379cd86dd423396dafe5536cf840046ca29f0f6b85f3636b61d55a6afd59796a90be706a7fc7796a6980b8698c6c1c69662a44695e384069007aa268db2f9668bb061968b23b996807ea486679635c66266e52655041bf64a7f6fd6408a0df6404275863b4c2d3631760f562101dda6095c7025f7f90c55eaa8cdf5e04d1245dfcd7225d23533c5cf920f65cbf21375c7251c45c36d5e35c2c5b3e5b5dd2605b314922
  | 9, 4 => 0x9530a5cd94a414be946d92c2945de16c93a0cd0a936fb47d9271ccdc92634e2092488c2a91126a2090a6c3ab9058ca408ef306b98eeeba208ebfc95d8eaaa5258e2a8de28e0402058c9f122c8c68cdbc8b6d0ed38b4c20d48aefaf068a1a73b989edc74588eec86e8862374f883a53768739282787065b88864558ba85e5cd6d85d5ede585a78140851813c184acc948847a6394843ae0d48429168783af5d9b82ec8b7f827eb677812bf490810b1de0804f0cea80246f35800df6e27f4f399a7e7f52357e7988367d9473bc7d2632297d0fed307cb896e67c7db9d37c5b86d17c075f567bd5d4567b5aa62f7b58b03f7ad273257abfbe767aac68e87a3383cb
  | 9, 5 => 0xb142f058b0272864afb74167afb4e5e5af8f5300aed9da9eaec19de5ae009b17adab2028ad62c39dacfca66aac680ba5ac401b1bab801868ab24b059aad10ddcaa9ac161aa57eaa1a91a6bb7a86a8457a84bde6fa83d4c34a83b74e2a7dfb192a5c43bb1a54fb619a416c92ea3b2169da3562fc3a31feb53a2fa652fa2e013b4a2d64726a267ab45a2242c6aa2033e6ba1f43945a1ddf284a19d6b03a100dde8a0d2aa0ca04fa162a026ad659fb38faf9f1954e69edbb8119ddf0d1d9d2a5a8e9ca9aa889b7899249b32d6d69ad8d3239a8bd2c19a02e86399f20fe599cc366e97062a8196f4029196b76b1c96afebf79669d8c696318f6c958f6596957942f0
  | 9, 6 => 0xcf5783f3ce398645cd03d762ccb6f27ecbd25338cb615ef2cb5b0a16cb3b7c93cad9e238ca9b5611ca8a2a41c9a89828c9863592c91b1d02c85f132ec82e7c3ac80a3b83c76ed20cc590f835c4d5a4eec4d212bbc3bb3672c2f738b2c2ee1933c204fe34c1f9ca62c1882b73c18778cbc0fb86dac026f1bfbf21a1eebf02fc06bef29279bdecd1c9bde03d86bcd8118ebc5f571bbbeed560bbc7a09dbb04c9baba60fd4bb9f32843b9b182c6b98d64bdb970a262b8cdac7db8a0665cb87f8facb7b7fb7fb78268aeb6ddcafcb6ae4916b67b0bbab54cffa2b4845efcb4465c57b33f4c09b2cf17fbb2cd220bb22fb6bbb1ae3ef2b1a909a2b1a7f597b1531dec
  | 9, 7 => 0xead539ebe9c04091e9bd412ae91d7b6ee8b6c937e82e77c6e81d9f48e7e2341ce7af9b67e6500423e6360fb1e5750ce3e4d73569e4c02d85e49353ebe47bd28ee3dc7d71e3baf4f9e382e2fae2c00c17e28970cfe24de714e1c88c1ce12be4bfe11e2bd0e0caa7a3e0779030e04f2293df54235eddc65290dd0841ffdcc427e5dca277cbdc561d45db181578da38e486da2fb27cd9dc1d11d99c97edd8ab0c71d872fb96d7e26ac1d7c8146bd7702842d74a955dd6f3bcddd65029ddd5cc77d4d582ed4ad578e023d4e170d7d4b7e8c7d44e1eb7d41e1c54d3b4c18dd3519150d30fc602d2a5f2f7d25603bed1775a2fd16681b1d1181ae2d0aa45dacff88e91
  | 9, 8 => 0xffd49905fee343d8febd888cfde2d0cafdc2b5abfd429d9bfd1ff9e7fced2d48fc2ebbd5fb8e5300fb546106fadea7c9fa939b08fa628afffa62192df9d3b2a5f92bc390f8fbea97f8c88d80f850cb18f5614395f51687b9f47234dbf422b806f3e022fdf3d3c8e7f37f5884f37b457cf144afc5f0c9e10ff0933aa8f04a53b3f0421e49efe9be97ee41b119ee22bae2edef7d86ec8d5518ec0f28fcec02c2dc
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 6, 0 => 0x36947200
  | 7, 0 => 0x80d1d364c080052d1920671cd9454c080072d95206001db46481a0b754d930286d1d364c28000014710082dd5364c0a0b47559304001cb4548060b4755930481d1d564c080073d952060014b5648180073d1920980dd5364c28000014f10086d1d364c29c73651530a001cb56480dd7474d930a0011556481c00474d920a000de56481a1b474d930a001c346480603474d9302475d5364c0a1b474d930a000d945481c9e47559307
  | 7, 1 => 0x784d9454c291d754d930a001c346481a0b47559302001cb454805c73651530283d1d564c05e13651530482dd5364c2800754d920282dd5364c080037959206001cb56482400564da203001c76548061b474d9302865cb454c100057519209001cb56480c0072d5920380dd5364c29c7365153020015d4648240073d592090011d5648100073d9520182dd5364c080073d592034549e564c1c00474d920a82dd9454c1e1b474d9302
  | 7, 2 => 0x1d945481e0747559302001cf6548040071d95201001d5464818003795920680d1d364c0a0b754d930a001db464819c73651530a71cd9454c080072d5920681dd5364c1207754d930480d1d364c0a0b47559302784d9454c0a0b4755930186d1d364c2a1b474d9302001c7464825d972d153040000051c4000073d59206479d5364c080052d5920686d1d364c0800754d9204784d9454c1c0070d192014849e564c1c00754d9202
  | 7, 3 => 0x20b4755930786d1d364c0a0b754d93028551e364c121b474d930286d1d364c280075519206
  | 8, 0 => 0x46441800478d9202000d945481c0071d1520a0011556480800474d920200000564410002795920a0011d3648080047959207000005644240071d152020011e3648100075d19202001155648080000159104001d7364808000011a101001d536481000000da1030009e56480800279592020000046442400279592070000056440c0075d192060000046441800474d920a001c745482800001971010009e564808004795920a
  | 8, 1 => 0x1db4548080072d152010011556481c00474d9202001d73648080072d152010000046441800474d9202001d74648100075cd9202001c74548280075cd92040009e5648280072d152010000046441800474d920a0009e5648280071d152020009e56481c0072d152040000052c42400001191090009e56482800475592070009e56482800474d920a000d94548100047559204000005644180071d152020009e56480800474d920a
  | 8, 2 => 0x46441800474d92020000052c41800754d92020011e36481c00474d92020000056441000365152070009e5648280072d152040011d5648080037959206001db4548040071d1520a0011d56481c0075cd920a0009e56481c0075cd920a001d53648280076d152020000046441800000da1090011d3648280000119106001cb4548100037959201001cb45480400001191060000052c42400365152070011556481000478d9202
  | 8, 3 => 0x1d53648080047559204001cb4548040045559207001c7454828000014b109001db4548100072d15204001d53648280072d15201001cb45480400379592010000046442400000da103000d94548280000159103001d7364808003651520a0000065c418000015a103001d736481000754d92070000065c41800475592040009e56481c002795920a0009e56481c0071d15202001cb4548100075d1920a000003684240036515207
  | 8, 4 => 0x11e56481000001591090000045441c004555920a001db45482800754d920a000004644240075d192070011d36481c0075d192040011e36481c004555920a000004644240027959202000de56480400474d920a000de5648180071d15202001d736481c002795920a001d546481800000da1090009e56481c0000151103001c74548080072d152040009e56480800478d92070000056441800474d920a001d53648280000119109
  | 8, 5 => 0x1cb4548040072d592030000052c41800478d92070009e56481c000014b1060009e564808004755920a001d74648040047559204000003684240071d1520a000004644240075d19206001d73648100000115101001c74548280076d1520a001d74648080027959207001c745482800478d92020000065441800000da1090009e56480800000da1090011e5648040037959201001d7364808002795920a000005644180075d19201
  | 8, 6 => 0x1c745482800475592070015d4648240036515202000d945481c0027959207001155648100071d152020009e5648080072d152040000046840400001591060009e56481c000015b1060009e56482800365152040011556481c0047559207001d73648280000119109000de5648040057519209000d94548280071d15202001d53648280037959201001c74548080037959206001cb4548100071d1520a0011556480400478d9202
  | 8, 7 => 0x1d536480800365152070009e5648080075d19207001155648080075d19202000de56480400754d9207000d94548080071d15202001cb56480c0071d152020000056441000001591060011d36482800001191060011d364828002795920a001d536481c00478d9202000004644240071d1520a000de56481800455592040009e56481c002795920a0000045441c00478d92020009e56482800365152020011d36482800000da103
  | 8, 8 => 0x4644180000197101001d73648080047959201001c745480800479592040000036842400001591030011e3648280072d152040009e564828002795920a0009e564808000015a109000004644040075cd92020000056440c00000da109001db454808000015b106001c74548280076d152020009e56481c002795920a0009e56480800474d92040011e36482800279592020000056440c0047559204001d945481c000014b106
  | 8, 9 => 0x9e5648080071d15202001d53648280072d152040009e5648080076d152040000052c4240000159106001cb4548100072d152010000045441c0075d19207001db45481c0037959201001d74648080072d15204001d536480800279592020000056442400001191060011d56480800365152040000046840400478d92020009e56482800001191060009e56480800475592020011d3648100075cd92020011e5648280047559202
  | 8, 10 => 0x1c74548280000159106000d945482800001591090011d56481000474d9204000004644180036515207000de5648040000119109001cb45481000455592040011d36481c00474d9207001d736481c00474d92070015e46482400279592020000052c4240072d152040011e56482800001151070009e56482800474d9202000d94548080071d1520a001c74548080075cd9204001d546481c0045559207001d53648280027959207
  | 8, 11 => 0x1c745480800001951010009e56482800754d9204001155648280047959202000de56480400455592040000052c41800000da103001cb4548100076d152010009e56480800455592070000056441000755192040000045441c0037959201001db4548280000159104001d536480800455592020011e56481c0071d15202001d736481c0072d152010015e46482400000da109001c74548080072d15201000004644240000159104
  | 8, 12 => 0x11e36480800474d9207001c7454808002795920a0000046441800754d92040000052c4180071d15202001d73648080000115107001c74548280071d1520a0009e56480800379592010009e56482800754d920a0000036842400001591030009e56480800365152070011e3648080047559202001d53648100027959202001cb4548040072d152010011d5648280075cd92070011e56481c0000119109001cb4548040072d15201
  | 8, 13 => 0x1db45480400001971010011556481c0075cd920a0011e3648100071d15202001d53648100075cd9202001cb45481000754d92020009e5648080075cd920a0009e5648080072d15204001c745482800365152020011d3648080000197106000004644180071d15202001cb45481000754d92020011d5648040045559207001c745482800754d9207001d746481c002795920a0000052c41800000da109001d74648280071d15202
  | 8, 14 => 0x9e56481c00475592010009e5648280036515202000de564804002795920a0011d36481c0071d1520a001d73648100000115101000d945480800455592020011e56480800001971060009e5648280071d1520a00000464424004755920100000564418002795920a001cb45481000754d920a001c74548280027959207001d74648100072d15204000d945481000478d920a0011e3648080071d1520a001c74548280000119109
  | 8, 15 => 0x1d536481c0000119109000de564804000015b1090000056c40c004755920a0009e56481c0071d1520a001155648080071d1520a0009e5648280071d1520a00115564808000014b1060000056c42400754d9202001cb45480400279592020009e56481c0036515204001d5364810000014b1090009e56481c0045559204001db454808002795920a001db4548280071d1520a000de56481800765152070009e5648080027959202
  | 8, 16 => 0x1cb4548100047959202001cb45481000474d920200000564418004795920a001d536480800474d920a001cb454804000014b1060000052c418000011b103001d73648280072d15201000005644240000152103001d74648080072d59203001cb45481000478d920a0011e36481c0072d15204000004644180075d192020000045441c00279592070000046440c0047959201001d546481800765152040009e5648080045559204
  | 8, 17 => 0x52c41800478d9207001c745480800001191010011d364808004755920a001c74548280072d15201001c74548080027959207001c745482800754d9204000005644100000159106001c74548080075cd9207001d53648080075d192040000052c42400478d9204000de56481800474d92040009e564828003651520a0009e5648280071d15202000de56481800001191090011e56481c002795920700115564828000015b103
  | 8, 18 => 0x11d56481000754d92040000056c4180071d1520a000d94548280076d15202000003684240045559207000d94548280027959207001c74548080072d15201000d94548080072d152040009e5648280027959202000de564804000014b106000004644180047959202001c745482800754d92020009e56481c002795920a001c74548080072d15204000d94548280037959201001db45481000000da1030009e56482800474d920a
  | 8, 19 => 0x52c4180027959207001c74548080075cd92070011e3648280075cd920a0000052c41800001191060009e5648080047559202001155648080071d1520a001cb4548040075cd920a000d945481c0036515207000de5648040076d15204001c745480800279592020009e56482800001151070009e56481c002795920a0000036840c0047559207000de5648040071d15202001cb56480c00754d920a0000056441000000da109
  | 8, 20 => 0x11d3648080071d15202000d94548080076d152070000045441c0071d152020000065440400754d92020009e56480800279592070011556481c0000119106001c74548080037959201000de56480400754d92020011556481c00379592010011d56481c0037959201001cb45480400478d920a001c745482800474d9202001d53648080037959206000d945481000001971060000045441c00478d9204001d536481c0027959207
  | 8, 21 => 0x1d746480400478d920a0009e56480800478d920a001c745482800279592020000046441800279592020009e5648080075cd92040009e56481c0000159104000d94548080071d1520a
  | 9, 0 => 0x36441c00001151040000036440800001151070000045442800001151020000046440800001591020000046441000001591070000045440800000d910a0000056441c00001191070000045440800001591010000046440400001191060000046442800001591090000045440400000d910a0000056441c00001191020000046440800000d9102000005644280000115102000004544080000159104000005644240000115102
  | 9, 1 => 0x46442800001151020000056442800001191010000036440800001151040000045440800001591020000056441c00001591040000045441c000015910700000464428000011510200000464428000011510a0000056442800001151020000056442800000d91020000045441c00001191060000056441800000d910a00000364428000015910700000464410000011510a0000056441c0000119106000004544280000159109
  | 9, 2 => 0x56442800001151040000036440800000d910a0000036440800000d91070000045442800001191070000056441000000d91070000056441c000011910a0000056442800001591020000045441000001151010000045441c00001191010000056441000001191040000045440400001151070000036441c00001591010000056441000001591040000046442800000d9102000004544280000119102000003644100000119102
  | 9, 3 => 0x564404000015910100000364410000011910a0000056441c00001591010000056440400001591020000046442800001151010000045442800001151010000046441000001591070000056441800001151020000046441c00001591070000056441c00001151020000045441c00000d91020000046441c00001591070000036441000001591010000046442800000d9102000004644080000159102000005644280000159107
  | 9, 4 => 0x46441000001151040000056442800001591010000056440800001591040000056441c000011910100000454428000015910200000464410000015910200000564408000015910700000564428000011910a0000046441000001151010000046441c00001591040000045441c0000119102000003644280000119107000005644100000115102000004644100000119107000004544080000159102000004544100000159107
  | 9, 5 => 0x46441c000011910a0000056442800000d910a0000045440800001591040000045440800001591040000056441c000011510a00000564410000011910a00000454404000015910a0000056440c000015910a0000036442800001191090000056441000001191040000045441c000011910700000454428000011910a0000036441c000011910200000364408000015910400000564428000011510a000005644080000159104
  | 9, 6 => 0x46440400001191010000046441c00000d910a00000464404000011510a0000046440400001591070000046440800001591020000045441c00001191070000045441c00001151070000045442800001191070000056442800001191070000036440800001151040000046441c000015910400000464404000011910400000564408000011910200000564428000011510a00000364408000011910a000004544040000159104
  | 9, 7 => 0x464410000011510a00000454428000011910a0000056440400001151040000056442800001591040000046440800001151070000046440800000d910a0000036441000000d91040000056441c00001591070000046440800000d91040000046441c000011910a0000036440800001191020000036442800000d910200000564428000011910100000454408000015910a000004644080000119107000003644280000159106
  | 9, 8 => 0x454428000015910a0000045440400001591070000046442800001151040000046440800000d910200000464410000011910a0000046441000001191070000045442800001591020000046442800001591010000056442800001151020000056441c00001151070000046441000001151040000056440800001591070000036441c000011910900000464410000011910a0000045441c00000d910a000005644100000119102
  | 9, 9 => 0x364408000015910100000454408000011910a0000045442800000d91040000045441c000011510a00000564418000015910a0000036440800000d910a0000056440800000d910a0000056441000001151040000056442400001191040000045441000001151070000045442800001151020000046440400000d91070000056441c00001151020000045441000000d910200000564408000015910200000564404000011910a
  | 9, 10 => 0x45441c00001191040000036442800000d910200000454404000011510100000564418000011510700000454404000011510100000454408000015910a0000036441000001191010000056442800001151040000046441000001151070000056441c00000d910a0000045441c00001191070000046441c00001591020000036442800001151070000056441c000011910600000454408000015910a000004644280000115101
  | 9, 11 => 0x36441c000015910700000464428000015910a00000564408000011510a0000046440800001191010000036441c000011910a0000056440800001191070000045440800001151040000036440800001151020000056440800000d910a0000036442800001151020000045441c00001591010000045442800001191020000045440800001191070000046441c00001191090000036441000000d9107000004544080000159102
  | 9, 12 => 0x364428000011910a00000564404000015910200000464404000011510a00000564428000015910200000454410000011510a0000036440800000d91070000056441c000011910a0000045441000001151070000036441c000011510a00000364408000011910200000464410000015910a0000045441000001191060000045440800001151040000045442800000d9107000004644080000119107000004544080000115104
  | 9, 13 => 0x36441000000d910a00000454428000015910400000454428000011510a0000036441c00000d910400000564408000011910200000464408000015910400000364410000011910200000364408000015910100000364410000011910a00000364428000011910a00000564428000011510a0000036440800001191070000056440800001191010000036440800001191020000056441000001591020000036440800000d9107
  | 9, 14 => 0x564410000011910900000454410000011910a00000464428000011510400000464408000011910400000464408000011910700000454404000011910a00000464408000015910400000454404000011910a0000056440800001191010000056440c00001191020000045442800001151040000046440400001591010000056442800000d910a0000046440800001151070000045441c00000d9104000003644280000119101
  | 9, 15 => 0x36441000001191020000056441000001151070000046441000000d91070000036441c00001191020000056442800001591020000045440800001151010000045442800001591070000046440800001591040000045441c00000d910a00000464428000011910200000364428000011910400000464428000011910700000564408000015910100000464418000015910a000004544080000159102000004644280000115107
  | 9, 16 => 0x56441800000d910a0000056440400001591020000036441c000011510700000564408000015910a00000564404000011510200000464428000015910200000454428000015910a0000046441000001191040000046441c00001151010000056442800000d91070000045441c000011910700000364410000011510700000454428000011910100000564428000011510200000454410000011910a000003644280000159102
  | 9, 17 => 0x36441c000011510a0000045440400000d910a00000464424000015910a0000036440800000d9102
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_175 roots_175 7 s ws hint
  | 1 => checkCutEntry true dom_239 roots_239 10 s ws hint
  | 2 => checkCutEntry true dom_253 roots_253 10 s ws hint
  | 3 => checkCutEntry true dom_127 roots_127 9 s ws hint
  | 4 => checkCutEntry true dom_247 roots_247 10 s ws hint
  | 5 => checkCutEntry true dom_111 roots_111 6 s ws hint
  | 6 => checkCutEntry true dom_223 roots_223 9 s ws hint
  | 7 => checkCutEntry true dom_251 roots_251 10 s ws hint
  | 8 => checkCutEntry true dom_123 roots_123 7 s ws hint
  | 9 => checkCutEntry true dom_191 roots_191 9 s ws hint
  | 10 => checkCutEntry true dom_254 roots_254 10 s ws hint
  | 11 => checkCutEntry true dom_207 roots_207 6 s ws hint
  | 12 => checkCutEntry true dom_215 roots_215 6 s ws hint
  | 13 => checkCutEntry true dom_155 roots_155 5 s ws hint
  | 14 => checkCutEntry true dom_55 roots_55 5 s ws hint
  | 15 => checkCutEntry true dom_95 roots_95 6 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_255 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_175 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_239 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_253 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_127 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_247 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_111 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_223 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_251 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_123 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_191 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_254 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_207 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_95 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_255 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_255 goalM v ys := cutHitH_sound h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_255 goalM v ys) : RunD true dom_255 goalM v (ori ys) := h
def Z (s : Nat) := bar true dom_255 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 35 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 35 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 17 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 17 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 4 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
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
  scr true dom_255 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 7 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : RunD true dom_255 goalM s xsM) : False := by
  have hmin : 7 ≤ s := by
    have hl := run_len h; change 8 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_255 roots_255 goal_255 12 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_255 goal_255 := by
    have h0 : isConstB dom_255 goal_255 = false := by decide +kernel
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

end S_255

theorem lowS_255 : Lower true dom_255 roots_255 goal_255 12 := S_255.noCircuit

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [4, 7] }, { op := GateOp.and, inputs := [8, 9] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [11, 7] }, { op := GateOp.and, inputs := [5, 12] }, { op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [14, 3] }, { op := GateOp.and, inputs := [6, 15] }, { op := GateOp.and, inputs := [3, 7] }, { op := GateOp.or, inputs := [10, 13] }, { op := GateOp.or, inputs := [18, 16] }, { op := GateOp.or, inputs := [19, 17] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 20⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  decide +kernel

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_14306_aux

theorem PEqualNP.Outside.L_meta_14306 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_14306_aux.main
