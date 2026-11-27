import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14248_aux

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

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffaaffaaffaaffaaaaaa0000aaaa0000ffaaffaaffaaffaaaaaa0000aaaa0000
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffeeffaaffeeffaaeeee0000eeee0000ffeeffaaffeeffaaeeee0000eeee0000
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_93 : Nat := 0x333333330000000033333333
def goal_93 : Nat := 0xfffafffafffafffaaaaa0000aaaa0000fffafffafffafffaaaaa0000aaaa0000
def roots_93 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffefffafffefffaeeee0000eeee0000fffefffafffefffaeeee0000eeee0000
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

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

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xeeeeeeeeeeeeaaaaeeeeeeeeeeee0000eeeeeeeeeeeeaaaaeeeeeeeeeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_117 : Nat := 0x330033003300330033003300330033
def goal_117 : Nat := 0xfafafafafafafafafafafafaaaaa0000fafafafafafafafafafafafaaaaa0000
def roots_117 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfcfcfcfcfcfcf0f0fcfcfcfccccc0000fcfcfcfcfcfcf0f0fcfcfcfccccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfefefefefefefafafefefefeeeee0000fefefefefefefafafefefefeeeee0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffaaffaaffaaffaaaaaaaaaaaaaa0000ffaaffaaffaaffaaaaaaaaaaaaaa0000
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffeeffeeffeeffaaeeeeeeeeeeee0000ffeeffeeffeeffaaeeeeeeeeeeee0000
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_125 : Nat := 0x33333333333333333333333333333333
def goal_125 : Nat := 0xfffafffafffafffafafafafaaaaa0000fffafffafffafffafafafafaaaaa0000
def roots_125 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_126 : Nat := 0x55555555555555555555555555555555
def goal_126 : Nat := 0xfffcfffcfffcfff0fcfcfcfccccc0000fffcfffcfffcfff0fcfcfcfccccc0000
def roots_126 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffefffefffefffafefefefeeeee0000fffefffefffefffafefefefeeeee0000
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_146 : Nat := 0x5000500000000000000000000000000050005
def goal_146 : Nat := 0xffffccccffffccccffffccccffffcccccccc0000cccc0000cccc0000cccc0000
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xffffccccffffccccffffccccffffcccceeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffffff00ffffff00ffffff00ffffff00aaaa0000aaaa0000aaaa0000aaaa0000
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffffffccffffffccffffffccffffffcccccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffffffccffffffccffffffccffffffcceeee0000eeee0000eeee0000eeee0000
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_166 : Nat := 0x550000005500000000000000000000005500000055
def goal_166 : Nat := 0xfcfcfcfcccccccccfcfcfcfcccccccccfcfcfcfc00000000fcfcfcfc00000000
def roots_166 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffeeffeeffccffccffeeffeeffccffcceeeeeeee00000000eeeeeeee00000000
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffefffeffccffccfffefffeffccffccfefefefe00000000fefefefe00000000
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffccccffffccccffffccccffffcccccccccccccccc0000cccccccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffcfcffffccccfffffcfcffffccccfcfcfcfccccc0000fcfcfcfccccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffefeffffccccfffffefeffffccccfefefefeeeee0000fefefefeeeee0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffaffffff00fffffffaffffff00fafafafaaaaa0000fafafafaaaaa0000
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffcffffffccfffffffcffffffccfcfcfcfccccc0000fcfcfcfccccc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffeffffffccfffffffeffffffccfefefefeeeee0000fefefefeeeee0000
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaff00ff00ff00ff00ffaaffaaffaaffaa0000000000000000
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffccffccffccffccffaaffaaffaaffaa0000000000000000
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaffff0000ffff0000aaaaaaaaaaaaaaaaaaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeffffccccffffcccceeeeaaaaeeeeaaaaeeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefeffffccccffffccccfefefafafefefafaeeee0000eeee0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ffffff00ffffff00ff00ff00ff00ff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffffff00ffffff00ffaaffaaffaaffaaaaaa0000aaaa0000
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffffffccffffffccffccff00ffccff00cccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffffffccffffffccffeeffaaffeeffaaeeee0000eeee0000
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_221 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def goal_221 : Nat := 0xfffffffafffffffaffffff00ffffff00fffafffafffafffaaaaa0000aaaa0000
def roots_221 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_222 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def goal_222 : Nat := 0xfffffffcfffffffcffffffccffffffccfffcfff0fffcfff0cccc0000cccc0000
def roots_222 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffeffffffccffffffccfffefffafffefffaeeee0000eeee0000
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeecccccccceeeeeeeeaaaaaaaaeeeeeeee00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcccccccccfcfcfcfcf0f0f0f0fcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfefefefefefefefefefefefeccccccccfefefefefafafafafefefefe00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffaaffaaffaaffaaffaaffaaff00ff00ffaaffaaffaaffaaaaaaaaaa00000000
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffccffccffccffccffccffccffccffccffccffccff00ff00cccccccc00000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffeeffeeffeeffeeffeeffeeffccffccffeeffeeffaaffaaeeeeeeee00000000
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffafffafffafffafffafffaff00ff00fffafffafffafffafafafafa00000000
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffcfffcfffcfffcfffcfffcffccffccfffcfffcfff0fff0fcfcfcfc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffefffefffefffefffefffeffccffccfffefffefffafffafefefefe00000000
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffeeeeffffeeeeffffeeeeffffcccceeeeeeeeeeeeaaaaeeeeeeeeeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffafafffffafafffffafaffff0000fafafafafafafafafafafafaaaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffcfcfffffcfcfffffcfcffffccccfcfcfcfcfcfcf0f0fcfcfcfccccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffefefffffefefffffefeffffccccfefefefefefefafafefefefeeeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffaaffffffaaffffffaaffffff00ffaaffaaffaaffaaaaaaaaaaaaaa0000
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffccffffffccffffffccffffffccffccffccffccff00cccccccccccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffeeffffffeeffffffeeffffffccffeeffeeffeeffaaeeeeeeeeeeee0000
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_252 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def goal_252 : Nat := 0xfffffff0fffffff0fffffff0ffffff00fff0fff0fff0fff0f0f0f0f000000000
def roots_252 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffafffffffafffffffaffffff00fffafffafffafffafafafafaaaaa0000
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffcfffffffcfffffffcffffffccfffcfffcfffcfff0fcfcfcfccccc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffefffffffefffffffeffffffccfffefffefffefffafefefefeeeee0000
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_146
def pairsG : List (Nat × Nat) := [(2, 18), (2, 130), (16, 18), (16, 144), (128, 130), (128, 144)]
def r1sG : List Nat := [2, 2, 16, 16, 128, 128]
def r2sG : List Nat := [18, 130, 18, 144, 130, 144]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_146.map (· &&& dom_146)
def goalM : Nat := goal_146 &&& dom_146
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0x2a71c470
  | 3, 0 => 0x2a71c470
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x500000000000000000000000000000005000000000000000000000000000000040004000000000000000000000000000400040000000000000000000000000005000500000000000000000000000000000000
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
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_146 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_146 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_146 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff0000ffff0000ffff0000, 112)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccccccccccccccccccccccccccc, 126)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xcccccccccccccccccccccccccccccccc, 126)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_146 == dom_146) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_146 goalM v ys) : RunD true dom_146 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_146 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_146 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_146 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_146 roots_146 goal_146 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_146 goal_146 := by
    have h0 : isConstB dom_146 goal_146 = false := by decide +kernel
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

end S_146

theorem lowS_146 : Lower true dom_146 roots_146 goal_146 4 := S_146.noCircuit

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

theorem lowS_147 : Lower true dom_147 roots_147 goal_147 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a000000000000000000000000000a000a, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_146

def isoMvS_54 : List (Nat × Nat) := [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_54 : Lower true dom_54 roots_54 goal_54 4 :=
  lower_iso isoMvS_54 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_85 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32)]
theorem lowS_85 : Lower true dom_85 roots_85 goal_85 4 :=
  lower_iso isoMvS_85 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_89 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_89 : Lower true dom_89 roots_89 goal_89 4 :=
  lower_iso isoMvS_89 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_105 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_105 : Lower true dom_105 roots_105 goal_105 4 :=
  lower_iso isoMvS_105 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_108 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_108 : Lower true dom_108 roots_108 goal_108 4 :=
  lower_iso isoMvS_108 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_153 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_153 : Lower true dom_153 roots_153 goal_153 4 :=
  lower_iso isoMvS_153 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_154 : List (Nat × Nat) := [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_154 : Lower true dom_154 roots_154 goal_154 5 :=
  lower_iso isoMvS_154 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

def isoMvS_166 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_166 : Lower true dom_166 roots_166 goal_166 4 :=
  lower_iso isoMvS_166 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_178 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_178 : Lower true dom_178 roots_178 goal_178 5 :=
  lower_iso isoMvS_178 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147

def isoMvS_201 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_201 : Lower true dom_201 roots_201 goal_201 4 :=
  lower_iso isoMvS_201 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_209 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_209 : Lower true dom_209 roots_209 goal_209 4 :=
  lower_iso isoMvS_209 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

def isoMvS_216 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_216 : Lower true dom_216 roots_216 goal_216 4 :=
  lower_iso isoMvS_216 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53

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

theorem lowS_93 : Lower true dom_93 roots_93 goal_93 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x303030300000000030303030, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_89

theorem lowS_155 : Lower true dom_155 roots_155 goal_155 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a0000000000000000000000000a0a0a0a, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_154

namespace S_182
def pairsG : List (Nat × Nat) := [(2, 18), (2, 34), (2, 130), (4, 36), (6, 22), (6, 38), (6, 134), (16, 18), (16, 144), (20, 22), (20, 52), (20, 148), (32, 34), (32, 36), (48, 50), (48, 52), (48, 176), (128, 130), (128, 144), (132, 134), (132, 148), (132, 164), (160, 162), (160, 164), (160, 176)]
def r1sG : List Nat := [2, 2, 2, 4, 6, 6, 6, 16, 16, 20, 20, 20, 32, 32, 48, 48, 48, 128, 128, 132, 132, 132, 160, 160, 160]
def r2sG : List Nat := [18, 34, 130, 36, 22, 38, 134, 18, 144, 22, 52, 148, 34, 36, 50, 52, 176, 130, 144, 134, 148, 164, 162, 164, 176]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_182.map (· &&& dom_182)
def goalM : Nat := goal_182 &&& dom_182
def NN : Nat → Nat
  | 4 => 3
  | 5 => 4
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x98406a416ceecda82209817d
  | 5, 0 => 0xd5ccd2947b1d315a70c7df1d53ea4760
  | 6, 0 => 0xe65584c
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x540054000000000000000000000000005400540000000000000000005500000055000000000000000000000055000000550000000000000000000000500054005000540000000000000000005000540050005400000000000000000055005500000000000000000000000000550055000000000000000000000000005000500050005000000000000000000050005000500050000000000000000000440044004400440000000000000000004400440044004400000000000000000000005500000055000000000000000000000044000000440000000000000000005500550055005500000000000000000000000000000000
  | 0, 1 => 0x5500550055005500000000000000000055000000550000000000000000000000000044000000440000000000000000000000440000004400000000000000000055005500550055000000000000000000440044004400440000000000000000005400540054005400000000000000000054005400540054
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x682705465205432105
  | 5, 0, 0 => 0x4b632064632a0646392060468205
  | 6, 0, 0 => 0x463205
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1c073f8073e00701cffc1f0001c073c00001dffc00effe0000
  | 0, 1 => 0xffe7c000001dffc00ee380e7f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xd056ac573e45f57cfde1f42a5c573c1294bddd420cdff0944
  | 0, 1 => 0xffe7ea928419bfeb7eefafeff
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
  | 3, 0 => 0x9b8e71b145526449
  | 4, 0 => 0xba1df298a370353d9f71ff429b8e71b1949bc0d5891c68346f24ea722c7987522a9bc7a6205aa5fc120b5bdd0e65584c0a88b2e906f0c180
  | 5, 0 => 0xefef6097e11b1923de58436edc54071ebbf711ba9eb0db969ca4f003891c6834840961a9770e3d33731448856c454b726bfcbe645ce65047500432174f0fd5e74b793cac470a73ab3ec1535637fdd2663711e95625f70ae9233ecfb31872787516471bd80e65584c06df0d1b011e27ce
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 3, 0 => 0x0
  | 4, 0 => 0x200010000020001000201020003
  | 5, 0 => 0x30200000200020201020000030202020102010000020202020202
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
  | 0 => checkCutEntry true dom_146 roots_146 4 s ws hint
  | 1 => checkCutEntry true dom_54 roots_54 4 s ws hint
  | 2 => checkCutEntry true dom_178 roots_178 5 s ws hint
  | 3 => checkCutEntry true dom_166 roots_166 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_182 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_146 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_54 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_178 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_166 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_182 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_182 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff0000ffff0000ffff0000, 112)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_182 == dom_182) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_182 goalM v ys) : RunD true dom_182 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_182 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_182 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_182 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_182 roots_182 goal_182 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_182 goal_182 := by
    have h0 : isConstB dom_182 goal_182 = false := by decide +kernel
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

end S_182

theorem lowS_182 : Lower true dom_182 roots_182 goal_182 7 := S_182.noCircuit

namespace S_217
def pairsG : List (Nat × Nat) := [(1, 17), (1, 65), (8, 72), (8, 136), (9, 25), (9, 73), (9, 137), (16, 17), (16, 144), (24, 25), (24, 88), (24, 152), (64, 65), (64, 72), (80, 81), (80, 88), (80, 208), (128, 136), (128, 144), (129, 137), (129, 145), (129, 193), (192, 193), (192, 200), (192, 208)]
def r1sG : List Nat := [1, 1, 8, 8, 9, 9, 9, 16, 16, 24, 24, 24, 64, 64, 80, 80, 80, 128, 128, 129, 129, 129, 192, 192, 192]
def r2sG : List Nat := [17, 65, 72, 136, 25, 73, 137, 17, 144, 25, 88, 152, 65, 72, 81, 88, 208, 136, 144, 137, 145, 193, 193, 200, 208]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_217.map (· &&& dom_217)
def goalM : Nat := goal_217 &&& dom_217
def NN : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x1bf6c01a
  | 5, 0 => 0xfcbd6b6a4c086f17493d8b40
  | 6, 0 => 0xfcbd6b6a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x30303030000000003000300000000000303030300000000030003000000000003030300000000000303030000000000030303000000000003030300000000000202020200000000020202020000000002020202000000000202020200000000030300000000000003030000000000000303000000000000030300000000000003000300000000000300030000000000030003000000000003000300000000000101010100000000010100000000000001010101000000000101000000000000030303030000000000000000000000000303030300000000000000000000000003030303000000000303030300000000000000000000000000000000
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
  | 0, 0 => 0xe0ff3e0073ff07000e601cf8000073e707fe0383e001fe0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf5ff3f67fbff4f0a5e715cf9145573e616b413c3e84dff0948
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
  | 4, 0 => 0xfcbd6b6a38780d291b42ffd21410a0da
  | 5, 0 => 0x3d7e7a882cdca0582634b2e117f7433605ef8bcb01c8962f
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x1000002
  | 5, 0 => 0x20003030002
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
  | 0 => checkCutEntry true dom_201 roots_201 4 s ws hint
  | 1 => checkCutEntry true dom_216 roots_216 4 s ws hint
  | 2 => checkCutEntry true dom_153 roots_153 4 s ws hint
  | 3 => checkCutEntry true dom_209 roots_209 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_217 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_201 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_216 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_153 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_209 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_217 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_217 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xffffffffffffffff0000000000000000, 64), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_217 == dom_217) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_217 goalM v ys) : RunD true dom_217 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_217 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_217 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_217 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_217 roots_217 goal_217 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_217 goal_217 := by
    have h0 : isConstB dom_217 goal_217 = false := by decide +kernel
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

end S_217

theorem lowS_217 : Lower true dom_217 roots_217 goal_217 7 := S_217.noCircuit

def isoMvS_91 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem lowS_91 : Lower true dom_91 roots_91 goal_91 5 :=
  lower_iso isoMvS_91 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

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

def isoMvS_115 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_115 : Lower true dom_115 roots_115 goal_115 5 :=
  lower_iso isoMvS_115 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_117 : List (Nat × Nat) := [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_117 : Lower true dom_117 roots_117 goal_117 5 :=
  lower_iso isoMvS_117 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_118 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_118 : Lower true dom_118 roots_118 goal_118 5 :=
  lower_iso isoMvS_118 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_121 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]
theorem lowS_121 : Lower true dom_121 roots_121 goal_121 5 :=
  lower_iso isoMvS_121 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_93

def isoMvS_171 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_171 : Lower true dom_171 roots_171 goal_171 5 :=
  lower_iso isoMvS_171 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_203 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_203 : Lower true dom_203 roots_203 goal_203 5 :=
  lower_iso isoMvS_203 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_211 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_211 : Lower true dom_211 roots_211 goal_211 7 :=
  lower_iso isoMvS_211 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_182

def isoMvS_218 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]
theorem lowS_218 : Lower true dom_218 roots_218 goal_218 7 :=
  lower_iso isoMvS_218 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_182

def isoMvS_227 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_227 : Lower true dom_227 roots_227 goal_227 5 :=
  lower_iso isoMvS_227 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_230 : List (Nat × Nat) := [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_230 : Lower true dom_230 roots_230 goal_230 5 :=
  lower_iso isoMvS_230 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_233 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_233 : Lower true dom_233 roots_233 goal_233 5 :=
  lower_iso isoMvS_233 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_234 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_234 : Lower true dom_234 roots_234 goal_234 5 :=
  lower_iso isoMvS_234 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

theorem lowS_95 : Lower true dom_95 roots_95 goal_95 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccccccc00000000cccccccc, 16, 18)] (by decide +kernel) (by decide +kernel) lowS_93

theorem lowS_111 : Lower true dom_111 roots_111 goal_111 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa0000aaaa0000aaaa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_110

namespace S_119
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 65), (2, 18), (2, 34), (3, 19), (3, 35), (3, 67), (4, 36), (4, 68), (5, 21), (5, 37), (5, 69), (6, 22), (6, 38), (6, 70), (7, 23), (7, 39), (7, 71), (16, 17), (16, 18), (20, 21), (20, 22), (20, 52), (20, 84), (32, 33), (32, 34), (32, 36), (48, 49), (48, 50), (48, 52), (64, 65), (64, 68), (66, 67), (66, 70), (66, 82), (66, 98), (80, 81), (80, 82), (80, 84), (96, 97), (96, 98), (96, 100), (112, 113), (112, 114), (112, 116)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 16, 16, 20, 20, 20, 20, 32, 32, 32, 48, 48, 48, 64, 64, 66, 66, 66, 66, 80, 80, 80, 96, 96, 96, 112, 112, 112]
def r2sG : List Nat := [17, 33, 65, 18, 34, 19, 35, 67, 36, 68, 21, 37, 69, 22, 38, 70, 23, 39, 71, 17, 18, 21, 22, 52, 84, 33, 34, 36, 49, 50, 52, 65, 68, 67, 70, 82, 98, 81, 82, 84, 97, 98, 100, 113, 114, 116]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_119.map (· &&& dom_119)
def goalM : Nat := goal_119 &&& dom_119
def NN : Nat → Nat
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0x66c2c4d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff0000000000ff00ff000000000000000000000000000000000000000000ff000000ff000000ff000000ff00000000000000000000000000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000000cc00cc00cc00cc00cc00cc00cc00cc0000000000000000000000000000000000aa00aa00aa00aa00aa00aa00aa00aa0000000000000000000000000000000000ff00ff00ff00ff0000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x2c6886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc01f80000038e071f800000000079ffc0001e0007e0f80000001c739ffff80000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc41fa09254b8e871f924299215279ffc0125e2457e0f8248a48bc739ffff81049284
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
  | 5, 0 => 0x66c2c4d1486e8e240ce1612a
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
  | 0 => checkCutEntry true dom_118 roots_118 5 s ws hint
  | 1 => checkCutEntry true dom_87 roots_87 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_119 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_118 _ hc
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

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
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
  scr true dom_119 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_119 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_119 roots_119 goal_119 7 := by
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

theorem lowS_119 : Lower true dom_119 roots_119 goal_119 7 := S_119.noCircuit

theorem lowS_123 : Lower true dom_123 roots_123 goal_123 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 16, 18)] (by decide +kernel) (by decide +kernel) lowS_121

namespace S_125
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 65), (4, 36), (4, 68), (5, 21), (5, 37), (5, 69), (8, 72), (9, 25), (9, 41), (9, 73), (12, 44), (12, 76), (13, 29), (13, 45), (13, 77), (16, 17), (20, 21), (20, 52), (20, 84), (24, 25), (24, 88), (28, 29), (28, 60), (28, 92), (32, 33), (32, 36), (40, 41), (40, 44), (40, 104), (48, 49), (48, 52), (56, 57), (56, 60), (56, 120), (64, 65), (64, 68), (64, 72), (80, 81), (80, 84), (80, 88), (96, 97), (96, 100), (96, 104), (112, 113), (112, 116), (112, 120)]
def r1sG : List Nat := [1, 1, 1, 4, 4, 5, 5, 5, 8, 9, 9, 9, 12, 12, 13, 13, 13, 16, 20, 20, 20, 24, 24, 28, 28, 28, 32, 32, 40, 40, 40, 48, 48, 56, 56, 56, 64, 64, 64, 80, 80, 80, 96, 96, 96, 112, 112, 112]
def r2sG : List Nat := [17, 33, 65, 36, 68, 21, 37, 69, 72, 25, 41, 73, 44, 76, 29, 45, 77, 17, 21, 52, 84, 25, 88, 29, 60, 92, 33, 36, 41, 44, 104, 49, 52, 57, 60, 120, 65, 68, 72, 81, 84, 88, 97, 100, 104, 113, 116, 120]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_125.map (· &&& dom_125)
def goalM : Nat := goal_125 &&& dom_125
def NN : Nat → Nat
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xc3e03a50
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3333333300000000333333330000000000000000000000000000000000000000333300003333000033330000333300000000000000000000000000000000000033003300330033003300330033003300000000000000000000000000000000003030303030303030303030303030303000000000000000000000000000000000222222222222222222222222222222220000000000000000000000000000000033333333333333330000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x2c6886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc0ffc000000e38f83fe0000000e73e1ff000000039df0f800000001cee7fff000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc0ffd08944ae38f83fe4221924e73e1ff0049252b9df0f8249294a7cee7fff842512994
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
  | 5, 0 => 0xc3e03a5098823a3f63ae4264412189e830eefc7727f21dca27c1818b259014470437be2d
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x10000010204020103
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
  | 0 => checkCutEntry true dom_53 roots_53 4 s ws hint
  | 1 => checkCutEntry true dom_121 roots_121 5 s ws hint
  | 2 => checkCutEntry true dom_109 roots_109 5 s ws hint
  | 3 => checkCutEntry true dom_117 roots_117 5 s ws hint
  | 4 => checkCutEntry true dom_108 roots_108 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_125 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_121 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_109 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_117 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_108 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_125 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_125 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_125 == dom_125) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_125 goalM v ys) : RunD true dom_125 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_125 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_125 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_125 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_125 roots_125 goal_125 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_125 goal_125 := by
    have h0 : isConstB dom_125 goal_125 = false := by decide +kernel
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

end S_125

theorem lowS_125 : Lower true dom_125 roots_125 goal_125 7 := S_125.noCircuit

namespace S_126
def pairsG : List (Nat × Nat) := [(2, 18), (2, 34), (4, 36), (4, 68), (6, 22), (6, 38), (6, 70), (8, 72), (10, 26), (10, 42), (10, 74), (12, 44), (12, 76), (14, 30), (14, 46), (14, 78), (16, 18), (20, 22), (20, 52), (20, 84), (24, 26), (24, 88), (28, 30), (28, 60), (28, 92), (32, 34), (32, 36), (40, 42), (40, 44), (40, 104), (48, 50), (48, 52), (56, 58), (56, 60), (56, 120), (64, 68), (64, 72), (66, 70), (66, 74), (66, 82), (66, 98), (80, 82), (80, 84), (80, 88), (96, 98), (96, 100), (96, 104), (112, 114), (112, 116), (112, 120)]
def r1sG : List Nat := [2, 2, 4, 4, 6, 6, 6, 8, 10, 10, 10, 12, 12, 14, 14, 14, 16, 20, 20, 20, 24, 24, 28, 28, 28, 32, 32, 40, 40, 40, 48, 48, 56, 56, 56, 64, 64, 66, 66, 66, 66, 80, 80, 80, 96, 96, 96, 112, 112, 112]
def r2sG : List Nat := [18, 34, 36, 68, 22, 38, 70, 72, 26, 42, 74, 44, 76, 30, 46, 78, 18, 22, 52, 84, 26, 88, 30, 60, 92, 34, 36, 42, 44, 104, 50, 52, 58, 60, 120, 68, 72, 70, 74, 82, 98, 82, 84, 88, 98, 100, 104, 114, 116, 120]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_126.map (· &&& dom_126)
def goalM : Nat := goal_126 &&& dom_126
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x42578290
  | 6, 0 => 0x14e06d24
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55005500550055005500550055005500000000000000000000000000000000005555555500000000555555550000000000000000000000000000000000000000555500005555000055550000555500000000000000000000000000000000000055505550555055505550555055505550000000000000000000000000000000005050505050505050505050505050505000000000000000000000000000000000444444444444444444444444444444440000000000000000000000000000000055555555555555550000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x2c6886
  | 6, 0, 0 => 0x2cc886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x739f0ff80fc01ff80000038e07c1ff00000001ce7fbfff0000001cef87c0078000039dcffff800000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2485739f0ff80fc41ffa11289b8e87c1ff2111db1fef7fbfff1242a95cef87c24f85294f9dcffffc212894c8
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
  | 4, 0 => 0x6fcfa086
  | 5, 0 => 0xc94e48d28dd139883960d27e14e06d24
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x1020202
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
  | 0 => checkCutEntry true dom_54 roots_54 4 s ws hint
  | 1 => checkCutEntry true dom_108 roots_108 4 s ws hint
  | 2 => checkCutEntry true dom_118 roots_118 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_126 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_54 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_108 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_118 _ hc
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

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
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

theorem lowS_183 : Lower true dom_183 roots_183 goal_183 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa00aa00aa000000000000000000aa00aa00aa00aa, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_182

theorem lowS_190 : Lower true dom_190 roots_190 goal_190 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x550055005500550000000000000000005500550055005500, 128, 136)] (by decide +kernel) (by decide +kernel) lowS_182

theorem lowS_215 : Lower true dom_215 roots_215 goal_215 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f00000000000f000f00000000000f000f00000000000f000f0, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_211

namespace S_219
def pairsG : List (Nat × Nat) := [(1, 17), (1, 65), (2, 18), (2, 130), (3, 19), (3, 67), (3, 131), (8, 72), (8, 136), (9, 25), (9, 73), (9, 137), (10, 26), (10, 74), (10, 138), (11, 27), (11, 75), (11, 139), (16, 17), (16, 18), (16, 144), (24, 25), (24, 26), (24, 88), (24, 152), (64, 65), (64, 72), (66, 67), (66, 74), (66, 82), (66, 194), (80, 81), (80, 82), (80, 88), (80, 208), (128, 130), (128, 136), (128, 144), (129, 131), (129, 137), (129, 145), (129, 193), (192, 193), (192, 194), (192, 200), (192, 208)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 8, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 16, 16, 16, 24, 24, 24, 24, 64, 64, 66, 66, 66, 66, 80, 80, 80, 80, 128, 128, 128, 129, 129, 129, 129, 192, 192, 192, 192]
def r2sG : List Nat := [17, 65, 18, 130, 19, 67, 131, 72, 136, 25, 73, 137, 26, 74, 138, 27, 75, 139, 17, 18, 144, 25, 26, 88, 152, 65, 72, 67, 74, 82, 194, 81, 82, 88, 208, 130, 136, 144, 131, 137, 145, 193, 193, 194, 200, 208]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_219.map (· &&& dom_219)
def goalM : Nat := goal_219 &&& dom_219
def NN : Nat → Nat
  | 4 => 3
  | 5 => 8
  | 6 => 18
  | 7 => 5
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x6079f4c429dc856c1c2f5dd0
  | 5, 0 => 0xabfbddffa9dd5f3991b3c3af7c79c2c23a8338a6251cdafb1832d0260e861710
  | 6, 0 => 0xfcdc61cadf70ba42d3d8b4b2caf69e4cc0742324b9f3c800a9dd5f39a82a79e3a51db4c897ec346d8a6bad0d76397b7f71d2db1a6e2002e24483213f2a6e662a2267702d0a9f9fd3
  | 7, 0 => 0xda3f8392cf74078ea51db4c840b1ea313892a4a3
  | 8, 0 => 0x8e86f0dd
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f000000000000030303030000000003030303000000000303000000000000030300000000000000000f0f0000000000000f0f000000000f0f0000000000000f0f0000000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a0000000000000303000000000000030300000000030300000000000003030000000000000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000
  | 0, 1 => 0xf0f0f0f0000000000000000000000000f0f0f0f000000000f0f000000000000050505050000000005050505000000000505050500000000050500000000000003030303000000000303030300000000030303030000000003030000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f000000000000000f000f000000000000000f00000000000f000f0000000000000000000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000000000000f0f0c0c000000000f0f0c0c000000000c0c0c0c000000000c0c0c0c000000000f0f0000000000000f0f000000000000000000000000000000000000
  | 0, 2 => 0xf0f0f0f0000000000000000000000000f0f0000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000000000000f0f0000000000000f0f0f0f000000000f0f0000000000000f0f0000000000000f0f0f0f000000000f0f0000000000000f0f0f0f0000000000000000000000000f0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f0000000000000f0f0f00000000000f0f0f00000000000f000f00000000000f000f000000000000000f0f0000000000000f0f0000000000000f0f00000000000000000000000005050505000000000505000000000000050505050000000005050000
  | 0, 3 => 0xf0f00000000000000000000000000000f0f000000000000000000000000000000000000000000000f0f0000000000000f0f00000000000000000f0f0000000000000f0f00000000000000000000000000000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f000f00000000000f0f0f00000000000f000f00000000000f0f0f00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x18620814831140a4188205
  | 5, 0, 0 => 0x60cee0299831140a660c4d0299871016a6018691014c419c40630c4502180419c405
  | 6, 0, 0 => 0xcb0671014e060ce2a298cc188a053830c3880a6030622814ccb8ce2029ccc19c4053cd8338aca7ab0671014e060d2202998338a8053cd833c00a7032471014cc19c408a9c0c19e00533d833880a7
  | 6, 0, 1 => 0x619c404303633881a6
  | 7, 0, 0 => 0x4d833880a760ce202b4e660ce2029d9c19c4053b067101487
  | 8, 0, 0 => 0x1833880a6
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
  | 0, 0 => 0x1e00fc1f3fff81fc0000fffe07f00003fff81fc00000000078ffe003c000038e73fffe07f00003c07fe000000
  | 0, 1 => 0xf01ffff00003c3ffffc0000fffe1ff0000000781fc0000fffff8000003ff8000000000001e00fc1f000000000000
  | 0, 2 => 0xfe007f00003ffffe0000000ffe07f00003c07fe000000f01ffff0000000001e3ff80ffe1f8000003c07fffc0000
  | 0, 3 => 0x1fc0000001e07f00003ff800000000fffffff0000000001ffff80
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2125e12fc1f3fffe1fedb5ddeda06d02c05edbe0eedb5d4248578ffe007c08a278e735a4a02902c07e07fe8124a2
  | 0, 1 => 0xf81ffbb6dadf83f75d8718cdeda1ed03e0e127a1fc9215b937a80001abffc41124948a5b5e56fc1f212401100000
  | 0, 2 => 0x7e005fb6d77fffff936dea87fe87fb6d77f27ff9124a2fc9ffff6dadf1b615f3ff807b61780db7ab82775d83084
  | 0, 3 => 0x120017c9215000e83b24855ed840024948fffffffffffd1b215ffff95
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
  | 5, 0 => 0xfcdc61cae48eec6ccaf69e4cb891cad6a7ad2b6da68128cd963058bc8e86f0dd73c24d2c63f93ab65bfa35e04f732dc14ab74c5d3e43da2339a2e7f0394c0f3938e582142755eb8014356e68
  | 6, 0 => 0xd3a5e111d3a373cfcfee6936cf74078ebc1c3addb43a16c6b202a742a81b3d63a0cf44269b9dd4f7960c35a795ee23cf90e05f2c8e86f0dd8b846e83866d8f3680c46fbc7ad10fcf79fa1cfc79c8ebb876caa60476710b9975b4efe0751c81b37502521273c24d2c7221907f707348ce6f2784e76e89fc9e6d90fc646d1c98746c1ec1546ace5aaf67c20e645f4a005c5d3dd43458f72793507e56b05009b944478110ea445fba0940b1ea313d37c71338e582143892a4a3384ff44234a814b9329e11bc30fc00e52eb2b0142e2874772c27bbd82955d01c27a0ac8a265263da247838ec20452f451c5dcdbc1a63a4ea19f5e56b16ff643416a3d86e08b51e48
  | 6, 1 => 0xf51eb9bcf31dd2f6db578ab5da3f8392
  | 7, 0 => 0xc51d0557c417d903bc1c3addb3d39094ad7fd1679ebedcb89e518f098e86f0dd87ab034c759f3d396ded075658f7279356b2e4125197d96b4424203f3f2dfc92395e26af30832f4d2f617a971dd4337a1b6794cc0fb653450d16529e0bbb1efe09c8c1320860f9a9062a61ef04c5e011029a68770084c352
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x3030303030003010103040403030303000101
  | 6, 0 => 0x30205010204020305020505050500010503020403020202000403010500020102000302040105020504010002000003050304010200020002030003010201020202
  | 7, 0 => 0x102010001050101010502000000010100050000050000010101010101
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 3
  | 5 => 7
  | 6 => 53
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xe4f3203db8e4a84769318682
  | 5, 0 => 0xf6bc704edb720961a73af30141fb51fe316efe07274f079614a4ef0c
  | 6, 0 => 0xd7bcfb0cc993ce60c0cf68b7bc292abd9d0b80d39b4a6b2498508e3197b9113e95c84f8693d23c168cdb01e4866d24a083e214fe80fe3da87f489d857db194d77bdc25117723230d70265e8169f95b3e695dda11661696e163054a6f5fc178e1525c274e508992c14f7c45ff4a9dcf7b43f0fc3a3ef76e43354b481b3272b327305a29882df8c9372cedbbc9244c89d3244495b222dfe77020477cb51ebaaba31dd212b81785f81e17284c3a166547481468a4351199abc810b0bc6e09ce495e09a499ef08e1433206a34ab90297690300d3d1cf
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x2449020065c91240c019724490300
  | 5, 0 => 0x244902000009124080000244902000010942081400324d12010009124080000000c3102
  | 6, 0 => 0x24440000000901000000032840400000c910000000344404000009110000000248400000010a10500000344414000010910000000240400000010a1010000032840400000921010000032841400000d21010000042041400000911000000034440000000c91050000034440400000901000000034440000000d21000000024840000000c9101000003284140000092101000003444140000092105000002444040000108105
  | 6, 1 => 0x911000000024440400000c91050000024440400000c91050000024440400000ca1050000032840000000d11010000032841400000ca1010000042840000000d11050000042840000000d11050000042041400000c91010000032840400000c910100000324400000010a105
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_217 roots_217 7 s ws hint
  | 1 => checkCutEntry true dom_218 roots_218 7 s ws hint
  | 2 => checkCutEntry true dom_155 roots_155 6 s ws hint
  | 3 => checkCutEntry true dom_203 roots_203 5 s ws hint
  | 4 => checkCutEntry true dom_91 roots_91 5 s ws hint
  | 5 => checkCutEntry true dom_211 roots_211 7 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_219 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_217 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_218 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_211 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_219 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_219 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff0000ffff0000ffff0000, 112), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_219 == dom_219) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_219 goalM v ys) : RunD true dom_219 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_219 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_219 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_219 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_219 roots_219 goal_219 9 := by
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

theorem lowS_219 : Lower true dom_219 roots_219 goal_219 9 := S_219.noCircuit

theorem lowS_221 : Lower true dom_221 roots_221 goal_221 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x30303030000000003030303000000000303030300000000030303030, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_217

namespace S_235
def pairsG : List (Nat × Nat) := [(1, 33), (1, 65), (2, 34), (2, 130), (3, 35), (3, 67), (3, 131), (8, 72), (8, 136), (9, 41), (9, 73), (9, 137), (10, 42), (10, 74), (10, 138), (11, 43), (11, 75), (11, 139), (32, 33), (32, 34), (40, 41), (40, 42), (40, 104), (40, 168), (64, 65), (64, 72), (66, 67), (66, 74), (66, 98), (66, 194), (96, 97), (96, 98), (96, 104), (128, 130), (128, 136), (129, 131), (129, 137), (129, 161), (129, 193), (160, 161), (160, 162), (160, 168), (192, 193), (192, 194), (192, 200), (224, 225), (224, 226), (224, 232)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 8, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 32, 32, 40, 40, 40, 40, 64, 64, 66, 66, 66, 66, 96, 96, 96, 128, 128, 129, 129, 129, 129, 160, 160, 160, 192, 192, 192, 224, 224, 224]
def r2sG : List Nat := [33, 65, 34, 130, 35, 67, 131, 72, 136, 41, 73, 137, 42, 74, 138, 43, 75, 139, 33, 34, 41, 42, 104, 168, 65, 72, 67, 74, 98, 194, 97, 98, 104, 130, 136, 131, 137, 161, 193, 161, 162, 168, 193, 194, 200, 225, 226, 232]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_235.map (· &&& dom_235)
def goalM : Nat := goal_235 &&& dom_235
def NN : Nat → Nat
  | 5 => 1
  | 6 => 3
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x209554b4
  | 6, 0 => 0x9a70f0b13da2aab412805a18
  | 7, 0 => 0x9a70f0b1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000000000000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a0000000000000e0e0000000000000e0e0000000000000e0e0000000000000e0e00000f0f00000f0f000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f00000f0f00000f0f00000000000000000000000000000000
  | 0, 1 => 0xf0f00000f0f00000f0f00000f0f00000a0a00000a0a00000a0a00000a0a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x5432106
  | 6, 0, 0 => 0x75431067548310775436107
  | 7, 0, 0 => 0x7543106
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 28
  | 6 => 32
  | 7 => 28
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe381c0fc0000ffffff000000000000f3ff8000003c03f07c007800038e7300783c03fe7ffc01ff000000fffe00000000
  | 0, 1 => 0xfffe00038e73
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xe3a1d0fc9215ffffffc36dea92150af3ff80490abc2bf07c24f845178e730c5a2d036c6afc41ff4124a2fffe20824948
  | 0, 1 => 0xfffe6597cf7b
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
  | 6 => 10
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0x9a70f0b105bb7a8703599def000f937c
  | 6, 0 => 0x4a36f9e03b4b7a6b34c63ba12853463d182cbbe4113c3da90c6ec32608e450ac0402e57e02ab1e06
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x100
  | 6, 0 => 0x40502000300060302
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
  | 0 => checkCutEntry true dom_234 roots_234 5 s ws hint
  | 1 => checkCutEntry true dom_171 roots_171 5 s ws hint
  | 2 => checkCutEntry true dom_203 roots_203 5 s ws hint
  | 3 => checkCutEntry true dom_233 roots_233 5 s ws hint
  | 4 => checkCutEntry true dom_227 roots_227 5 s ws hint
  | 5 => checkCutEntry true dom_105 roots_105 4 s ws hint
  | 6 => checkCutEntry true dom_107 roots_107 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_235 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_234 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_171 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_233 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_227 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_105 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_107 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_235 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_235 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xffffffffffffffff0000000000000000, 64), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xffffffff00000000ffffffff00000000, 96), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_235 == dom_235) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_235 goalM v ys) : RunD true dom_235 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_235 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_235 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_235 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_235 roots_235 goal_235 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_235 goal_235 := by
    have h0 : isConstB dom_235 goal_235 = false := by decide +kernel
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

end S_235

theorem lowS_235 : Lower true dom_235 roots_235 goal_235 8 := S_235.noCircuit

def isoMvS_175 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_175 : Lower true dom_175 roots_175 goal_175 6 :=
  lower_iso isoMvS_175 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_95

def isoMvS_189 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_189 : Lower true dom_189 roots_189 goal_189 7 :=
  lower_iso isoMvS_189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_126

def isoMvS_222 : List (Nat × Nat) := [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_222 : Lower true dom_222 roots_222 goal_222 8 :=
  lower_iso isoMvS_222 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215

def isoMvS_231 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_231 : Lower true dom_231 roots_231 goal_231 6 :=
  lower_iso isoMvS_231 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_123

def isoMvS_237 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_237 : Lower true dom_237 roots_237 goal_237 6 :=
  lower_iso isoMvS_237 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_123

def isoMvS_238 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_238 : Lower true dom_238 roots_238 goal_238 8 :=
  lower_iso isoMvS_238 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_235

def isoMvS_243 : List (Nat × Nat) := [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_243 : Lower true dom_243 roots_243 goal_243 8 :=
  lower_iso isoMvS_243 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_183

def isoMvS_245 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_245 : Lower true dom_245 roots_245 goal_245 6 :=
  lower_iso isoMvS_245 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_123

def isoMvS_246 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_246 : Lower true dom_246 roots_246 goal_246 8 :=
  lower_iso isoMvS_246 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215

def isoMvS_249 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]
theorem lowS_249 : Lower true dom_249 roots_249 goal_249 8 :=
  lower_iso isoMvS_249 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_221

def isoMvS_250 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccccccccccccccccccccccccccccccc, 126)]
theorem lowS_250 : Lower true dom_250 roots_250 goal_250 8 :=
  lower_iso isoMvS_250 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_190

def isoMvS_252 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcccccccccccccccccccccccccccccccc, 126)]
theorem lowS_252 : Lower true dom_252 roots_252 goal_252 7 :=
  lower_iso isoMvS_252 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_126

namespace S_127
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 65), (2, 18), (2, 34), (3, 19), (3, 35), (3, 67), (4, 36), (4, 68), (5, 21), (5, 37), (5, 69), (6, 22), (6, 38), (6, 70), (7, 23), (7, 39), (7, 71), (8, 72), (9, 25), (9, 41), (9, 73), (10, 26), (10, 42), (10, 74), (11, 27), (11, 43), (11, 75), (12, 44), (12, 76), (13, 29), (13, 45), (13, 77), (14, 30), (14, 46), (14, 78), (15, 31), (15, 47), (15, 79), (16, 17), (16, 18), (20, 21), (20, 22), (20, 52), (20, 84), (24, 25), (24, 26), (24, 88), (28, 29), (28, 30), (28, 60), (28, 92), (32, 33), (32, 34), (32, 36), (40, 41), (40, 42), (40, 44), (40, 104), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60), (56, 120), (64, 65), (64, 68), (64, 72), (66, 67), (66, 70), (66, 74), (66, 82), (66, 98), (80, 81), (80, 82), (80, 84), (80, 88), (96, 97), (96, 98), (96, 100), (96, 104), (112, 113), (112, 114), (112, 116), (112, 120)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 12, 12, 13, 13, 13, 14, 14, 14, 15, 15, 15, 16, 16, 20, 20, 20, 20, 24, 24, 24, 28, 28, 28, 28, 32, 32, 32, 40, 40, 40, 40, 48, 48, 48, 56, 56, 56, 56, 64, 64, 64, 66, 66, 66, 66, 66, 80, 80, 80, 80, 96, 96, 96, 96, 112, 112, 112, 112]
def r2sG : List Nat := [17, 33, 65, 18, 34, 19, 35, 67, 36, 68, 21, 37, 69, 22, 38, 70, 23, 39, 71, 72, 25, 41, 73, 26, 42, 74, 27, 43, 75, 44, 76, 29, 45, 77, 30, 46, 78, 31, 47, 79, 17, 18, 21, 22, 52, 84, 25, 26, 88, 29, 30, 60, 92, 33, 34, 36, 41, 42, 44, 104, 49, 50, 52, 57, 58, 60, 120, 65, 68, 72, 67, 70, 74, 82, 98, 81, 82, 84, 88, 97, 98, 100, 104, 113, 114, 116, 120]
def mpG : Nat := 0x7fffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_127.map (· &&& dom_127)
def goalM : Nat := goal_127 &&& dom_127
def NN : Nat → Nat
  | 6 => 11
  | 7 => 8
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xff0e5f39f32c58feedece767eab89a10de78014bd275bea496c898823eb8575f18842fcd15e1007b098f4acd
  | 7, 0 => 0xb8c3dad5aa83b7fa9909e7358c28a32f899501197be7163e0ebf39420a79ceff
  | 8, 0 => 0x63e0daa3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f0f0f0f0f0f0f0f0f0000000000000000000000000000000000000000ffffffff00000000ffffffff0000000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa000000000000000000000000000000003333333333330000333333333333000000000000000000000000000000000000ffffffffffffffff0000000000000000
  | 0, 1 => 0xffff000000000000ffff00000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff000000ff000000000000000000000000000000000000fff0fff0fff0fff0fff0fff0fff0fff000000000000000000000000000000000fffffffffffffffff0f0f0f0f0f0f0f000000000000000000000000000000000ffffffffffff0000ffffffffffff000000000000000000000000000000000000ffffffffffffffffffffffff0000000000000000000000000000000000000000cccccccccccccccccccccccccccccccc
  | 0, 2 => 0xffffffffffffffffffff0000ffff00000000000000000000000000000000000000ff00ff00ff00ff00f000f000f000f000000000000000000000000000000000f0fff0fff0fff0fff0f0f0f0f0f0f0f00000000000000000000000000000000000ff00ff00ff00ff00ff00ff00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x628d02901cc588d0203a8c34080e7314681400e61a04f039cc51a04d0398ac5a0407518831040ea49068101cc5220470398a4188207
  | 7, 0, 0 => 0x18a34080e7498a41a0408028c41a0407018ac1a040701883409e07518a41a04083148b1a040834ca41a0408
  | 8, 0, 0 => 0x18a41a0407
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 39
  | 7 => 44
  | 8 => 39
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffffffffc0000000000001fe001fff80000000000003c3c03f80fff80000000000000078f1fc0fffff80000000000003c79ffc00ffe000000000000038e71dc739fffc03ffffff80000000007ffff80000000000000000
  | 0, 1 => 0xf000003ffe0000000001ffffe00000000000000003ffffc38001f80000000000000078f1ffcffffffff00fffff0003c79ffc00ffe01ffe01ffffffc0000000003ffffffff00000000000000007c0000000fc1f87e0f8
  | 0, 2 => 0xffffffe03ffe0000000001ffffe00000f000001ffc03ffffc000f1e7ff003ff807ffff870e0000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xbbbedb76c2000036d001adfe101fffa04124a489254bc3d03f80fff9242489214c441278f1fc0fffff80000444124893c79ffc00ffe002221224489178e71dc739f774036eddba80d0180681fffffc08112092524c9284
  | 0, 1 => 0xf400002fde4909224852eefb600000800000124a11ddf6c38001f800002db56e661b7cf9ffcffffffff00fffffc993e79ffe49fff09fff81ffffffdb6b6cdb5efffffffffc986dbdb76deb1117c122448afc1f87e0f8
  | 0, 2 => 0xfffffff03fff6dadbb6d5aeefb610200f000001ffe11ddf6d224f1e7ff003ffc23bbed870e030000006dbd6
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
  | 5, 0 => 0x87e1fdaf604e588d0c57e932
  | 6, 0 => 0xdf7e4a35da72a7f5d64c5e49cf671b28c4236df1c3a682a9c151afc1b64fb53cb1dcc9a5b12b8a76ac004ad6ab8d39dc9e57715f9909e735899501197c35fc2563e0daa354b8002b497ded2634fd8f9430f8a7682d8fa4172aa7e49a18b5850e
  | 7, 0 => 0xbca76cc7bc10e3c2bb73ec4eb6c6f64cb64fb53cb5416367b2f317faae13f666ac004ad6aa179779a54897d8a4a39454a31aba409ea809f79e6b373499a889eb99563c2995beaa369222e770878bfb7785e9baae85096e757b9511f57546e97a6c7230226aa615616992b6f768cac95763e0daa360e283725d9313835cd9d4965c4f4d0e4d8b8bdc475dbbe84328eb0141063c873f2081f13ef803273e8e344a3dd5d1c13c1a0eb136c21e23343d60ba31cd2cc231caa44b2efa42272eaf12402a92cbe4227957f720e76f151f233dd11f1de2f319d9378515d5932113753dcd12859ef011f2fca40ff450c10f3fa59009362f25089092cb0542e9eb00e34df1
  | 7, 1 => 0xfbb07c3ff98822def96a209ff6ba45b7f1b3c92ff11ca230f09436ceee43f5cfe4dbbbecdf995cf2dec9a6b6ddcd7784d7acba53d54d50f2d2cc32a8d292fa8ed0a04b2cccaea0ebcbc2a3a1cb56f0a8ca247a61c56e85b2c2f82f95c1162fb5be137c31
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x10200
  | 6, 0 => 0x50506040101090100040101040605080304070105010602
  | 7, 0 => 0x808030109030807030305080301080304040305050805070306030103010303080108080303080403070303080801030805030401030303060300040803080301030101080301080101040801060603030101030801080103
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 5 => 1
  | 6 => 39
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0x9d9c7e2c
  | 6, 0 => 0xfff482dffd60e0c9f9a49b8bf9869486f139f054eb78c1cee458ac4ee1c50a38e1295768dc03dbb2d9cca0e6d1b4714ccceb5ce0cadff629ca57bacab55e33bbb15f08b7abd64994a72742338ee7e6e8638b499c4e4d20d1451d5d533ea0c2ff3d6b662d361d55a635a87737336efd852f9c06592e932d312c8fba8524c76e1f21b1e92b1f1e47151a04c87e10f3e3f40df319ee0cd5c6e50a8fe262
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x43515201
  | 6, 0 => 0x10e1030010d1010010e1010010d1030010e10100085103000961030010e1030010d1040010d1080010d103000c91060010d10800085103000961030010d1030010d10400085103000851080010e1030010d108001151010010d103000961030010d103000851030010e1030010d10300096103000851080010d1030010e103
  | 6, 1 => 0x851030010e10300096103000961030010d1030010d10100085103
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_107 roots_107 5 s ws hint
  | 1 => checkCutEntry true dom_119 roots_119 7 s ws hint
  | 2 => checkCutEntry true dom_115 roots_115 5 s ws hint
  | 3 => checkCutEntry true dom_126 roots_126 7 s ws hint
  | 4 => checkCutEntry true dom_123 roots_123 6 s ws hint
  | 5 => checkCutEntry true dom_111 roots_111 6 s ws hint
  | 6 => checkCutEntry true dom_95 roots_95 6 s ws hint
  | 7 => checkCutEntry true dom_55 roots_55 5 s ws hint
  | 8 => checkCutEntry true dom_125 roots_125 7 s ws hint
  | 9 => checkCutEntry true dom_91 roots_91 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_127 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_107 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_119 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_126 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_123 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_111 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_95 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_125 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 32 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_127 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_127 goalM v ys := cutHitH_sound h

def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {v ys} (h : RunD true dom_127 goalM v ys) : RunD true dom_127 goalM v (ori ys) := h
def Z (s : Nat) := bar true dom_127 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_127 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_127 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_127 roots_127 goal_127 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_127 goal_127 := by
    have h0 : isConstB dom_127 goal_127 = false := by decide +kernel
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

end S_127

theorem lowS_127 : Lower true dom_127 roots_127 goal_127 9 := S_127.noCircuit

theorem lowS_191 : Lower true dom_191 roots_191 goal_191 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_190

theorem lowS_223 : Lower true dom_223 roots_223 goal_223 10 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_219

theorem lowS_239 : Lower true dom_239 roots_239 goal_239 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 32, 33)] (by decide +kernel) (by decide +kernel) lowS_238

namespace S_247
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 65), (2, 18), (2, 34), (2, 130), (3, 19), (3, 35), (3, 67), (3, 131), (4, 36), (4, 68), (5, 21), (5, 37), (5, 69), (6, 22), (6, 38), (6, 70), (6, 134), (7, 23), (7, 39), (7, 71), (7, 135), (16, 17), (16, 18), (16, 144), (20, 21), (20, 22), (20, 52), (20, 84), (20, 148), (32, 33), (32, 34), (32, 36), (48, 49), (48, 50), (48, 52), (48, 176), (64, 65), (64, 68), (66, 67), (66, 70), (66, 82), (66, 98), (66, 194), (80, 81), (80, 82), (80, 84), (80, 208), (96, 97), (96, 98), (96, 100), (112, 113), (112, 114), (112, 116), (112, 240), (128, 130), (128, 144), (129, 131), (129, 145), (129, 161), (129, 193), (132, 134), (132, 148), (132, 164), (132, 196), (133, 135), (133, 149), (133, 165), (133, 197), (160, 161), (160, 162), (160, 164), (160, 176), (192, 193), (192, 194), (192, 196), (192, 208), (224, 225), (224, 226), (224, 228), (224, 240)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 16, 16, 16, 20, 20, 20, 20, 20, 32, 32, 32, 48, 48, 48, 48, 64, 64, 66, 66, 66, 66, 66, 80, 80, 80, 80, 96, 96, 96, 112, 112, 112, 112, 128, 128, 129, 129, 129, 129, 132, 132, 132, 132, 133, 133, 133, 133, 160, 160, 160, 160, 192, 192, 192, 192, 224, 224, 224, 224]
def r2sG : List Nat := [17, 33, 65, 18, 34, 130, 19, 35, 67, 131, 36, 68, 21, 37, 69, 22, 38, 70, 134, 23, 39, 71, 135, 17, 18, 144, 21, 22, 52, 84, 148, 33, 34, 36, 49, 50, 52, 176, 65, 68, 67, 70, 82, 98, 194, 81, 82, 84, 208, 97, 98, 100, 113, 114, 116, 240, 130, 144, 131, 145, 161, 193, 134, 148, 164, 196, 135, 149, 165, 197, 161, 162, 164, 176, 193, 194, 196, 208, 225, 226, 228, 240]
def mpG : Nat := 0x3ffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_247.map (· &&& dom_247)
def goalM : Nat := goal_247 &&& dom_247
def NN : Nat → Nat
  | 5 => 3
  | 6 => 8
  | 7 => 16
  | 8 => 5
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xd5c3ab2d5c8ff3692ec5b3be
  | 6, 0 => 0xe14f1c7dde2507e867188bde667c58b357b566414bd3550235c7155e2811eb29
  | 7, 0 => 0xf856f518cdc51016c818c844c4fd2e2bafe7ce6a98b583395a4b15af590eb8d453e29f433e28721935c7155e2c2cb56a1eebb87b1388470308c9ea8e0075fe88
  | 8, 0 => 0xfffe3a9cb0c0ade73e28721925d3e27a054ce95e
  | 9, 0 => 0xabd6bf33
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa003300cc003300cc003300cc003300cc003300cc003300cc003300cc003300cc00000000000000000000000000000000003300cc003300cc003300cc003300cc00ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000
  | 0, 1 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff000000ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc00cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000ff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc0000000000000000000000000000000000ff000000ff000000ff000000ff00000000000000000000000000000000000000cc00cc00cc00cc00cc00cc00cc00cc
  | 0, 2 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00cc00ff00cc00ff00cc00ff00cc00ff00ff00cc000000ff00ff00cc000000ff00ff00cc000000ff00ff00cc000000ff00cc00ff00cc00ff00cc00ff00cc000000000000000000000000000000000033000000330000003300000033000000330000003300000033000000330000000000cc000000cc000000cc000000cc000000cc000000cc000000cc000000cc00fc00f000fc00f000fc00f000fc00f000fc00f000fc00f000fc00f000fc00f000ff00ff00ff00ff00ff00ff00ff00ff00cc000000cc000000cc000000cc000000cc00cc00cc00cc00cc00cc00cc00cc00ff00cc00ff00cc00ff00cc00ff00cc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xa720c406298830818a4188206
  | 6, 0, 0 => 0x14c488c0c531062031cb0591030394cf238607298e468c0e0290620318a7591430394c9220607
  | 7, 0, 0 => 0x2dd6450c0c8014c468c0c7298eb2286080596450c0c729d6450c0c82bd647286082ad245206082996450c15801483a4c0c72996450c0c8014eb2286070157250c0c72996440c0c8015645446072996470c0c82c16450c0c8
  | 8, 0, 0 => 0x2ac8a68c0c82ad2450c0c82996450c0c82ac8a1cc0c82bd6450c0c8
  | 9, 0, 0 => 0x156450c0c7
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 34
  | 6 => 39
  | 7 => 44
  | 8 => 44
  | 9 => 39
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3c7fcf1fffe0fe0000000f1ff3c7fff83f8f0f0003f800fe00000000003fc00000007c7ffc00000f0f000000001e1cf1c000000f1ff3c7fff83f80000003c7fcf1fffe0fe3fc0000ffffc000000000
  | 0, 1 => 0xfffffffc780f1fe000003ffffff001f00007f83f8000000000000000000003ffffff000000000000000000003c780f1fe000000000000001f00007f83f80000003c780f1fe000000000000001f00007f83f8
  | 0, 2 => 0xfffffffc7fcf1fffe0fe3c3c000fe003f80000000000000000000000000000000000f1e03c7f8000000000000007c0001fe0fe0003fc00000007c7ffc00ffffffc00000000000000000000f1ff3c7fff83f8
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1d3bc74f6ee4766aa8ccff5ff3d7fff93f9f0f4443f820fe40449249113fc04882927c7ffc00111f0f048851213e1cf1eaa8ccfd5bb3576f713b1000000152ac54d2cc4647fc2220ffffc020224904
  | 0, 1 => 0xfffffffc7d0f1ff3249a7ffffffa55f294b7f83f8000000081102024220123ffffff81102042440220888222bc790f1fe224124888445245f09097f83f80000001c39070f6224124000000244f09093b81d8
  | 0, 2 => 0xfffffffd7fcf5fffe4fe7c3d110fe4c3f9919a4daaaa333e0440810910088222088ad1a034768010012221114106c0401dc0ec1113fc068c69a7d7ffc48ffffffe8550a12d3209a088844574ff1d3dff93f9
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 82 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 82 (i % 8)
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
  | 5 => 5
  | 6 => 23
  | 7 => 77
  | 8 => 43
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0xe14f1c7dc834287f66b99bbd3a010faa00a6b4f1
  | 6, 0 => 0xe8ab56d1cdc51016c6bd05eeabd6bf339ffad06b915e7e638c422e9278752ab47671d1876b02b77c6a81ba5a5b6fd5894b27d1e64a9d8fd84a03f1a83e6cef37357697e632d3424731c95d7a2436f6ef1dac4a551388470301661e02
  | 7, 0 => 0xa003f8399e3e8c0a96ca79b595ab063393db00388da9000f8428618c8167026c7ee1204a79bafd7a7643809973c590647076bd096ff5cca16df84a056d69aa8a6d5f93ad67afc26c62ea79e261e1c6e75ad0ecc3586c46fc559687bf548380a45055bb7e49b2509346f86d5143a7f968430d1414423d94d240ddbefa40cfbf8f3713837136829266339f48882d4101862cb798f52c1bc6e52ac22df92a2e12602827bbbf27c9b48f27c16c8f25d3e27a24e10bbd24d3b822241dd2fe22d9c49e1fa1f8e91e9b39e11c7a0a0a1c6ab42f1ac2bc8f1924a9941783e3e816b7f754138c569f1332fa3c129858f810acea880c614a130b04b638069728dc054ce95e
  | 7, 1 => 0xfffe3a9ce86e6bb8e5138c75cea439b0c6bd05eec4c8fd6abe7b5918b8ee1498b0c0ade7abd6bf33aa1184d4a8aafc0da5c0d5f8
  | 8, 0 => 0xddb95d6bd2172daac787e5cfc0c03c31b9311668b4103e05af96d756abd6bf33a11bdee7a0ee3d9b9f79c3309df3efb797b894d4868418da7948b06f744b81437306a372727bea1e70a9787b6eb7552a6e9266a86b1aa29b6489b61a5fd703e34e7ecc2848d9328148d83bb83e7e25903a7596c234aab87c33daa8ae2c5d297b2520867f21d84215215de8a41f594ffd1f2b5da41e9b39e11c6ab42f114d5667112dd7480b9176870983a2a9
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x304010101
  | 6, 0 => 0x103040003040308030304010803040803030703030303
  | 7, 0 => 0x302040404020303040000030403040305060106060406090600040600000303090005050400040205000404040303030000040202050404030405040205040604080301020505000306040304
  | 8, 0 => 0x2050000000000000006060602050506000606020000050200000605060206060206000606040400000200
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 5 => 4
  | 6 => 17
  | 7 => 58
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xa092ffe552d0162a46a634920b17386a
  | 6, 0 => 0xd2cc2a6b8fe69ae88d08f37e8441119360d5f5b75adf606b4cb07edc4ba50fd43cc3d68633297692331c282b20628ff21a85082b1942a730132682ab0fa8473c02baba9a
  | 7, 0 => 0xbf421e04bc435a5eb3a3f62ba2cfd9d09d211f089d1897d29cdba3ec9a0d45999325566592741d7b8ec5c36f8b2afa8f859414fd83478aed81ebeb3a8140370a7cc64d9c78a3f5827107ccae70dd36617004914f6aa401736a4746896094eefe54cc8522509ae6af4f3587714dfe8df04de6769e47899c9f452533413b8f8ffb34d8f81c34b0db962f4110422f1516b42ee868272d8665cb26a1ee0321bb091821a403eb1d03f65d1ca13b81181584551617c5fc1499e25b108ebfce1032afc90c49aa86098ec718094f744c08c695ec08af2c0f080ef9ad06fafbc403c7717d021fef05021daed2
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x2595020c019f310c530202595020c019f02009300
  | 6, 0 => 0x654082000004812481800020092000018d02080000644c4202000c7318808001304d202001911308140065cc52020018913080800020092000018502080000654c4202001973148080002c0a2000018913080800604c4202
  | 7, 0 => 0x13040800000551060000005c40000000551020000031440800000551020000005c400000004e1020000013840800000571020000005c40000000811000000031840800000491060000031440800000551060000015441400000c61020000025c40000000971060000020040000000d510200000354408000004e1050000031840800000c41050000013840800000c410500000310408000000a100000001544080000081100
  | 7, 1 => 0x2040000000551020000035c40800000971060000005c40000000861060000015440800000971000000013440800000491060000005c40000000821000000020840000000d51020000013840800000571060000013040800000151000000015441400000d71050000025c40000000951000000031041400000c6105000003184140000081100
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_246 roots_246 8 s ws hint
  | 1 => checkCutEntry true dom_117 roots_117 5 s ws hint
  | 2 => checkCutEntry true dom_215 roots_215 8 s ws hint
  | 3 => checkCutEntry true dom_245 roots_245 6 s ws hint
  | 4 => checkCutEntry true dom_119 roots_119 7 s ws hint
  | 5 => checkCutEntry true dom_183 roots_183 8 s ws hint
  | 6 => checkCutEntry true dom_243 roots_243 8 s ws hint
  | 7 => checkCutEntry true dom_230 roots_230 5 s ws hint
  | 8 => checkCutEntry true dom_231 roots_231 6 s ws hint
  | 9 => checkCutEntry true dom_103 roots_103 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_247 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_246 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_117 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_245 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_119 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_183 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_243 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_230 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_231 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_103 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_247 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_247 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_247 == dom_247) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_247 goalM v ys) : RunD true dom_247 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_247 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 8 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
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
  scr true dom_247 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_247 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_247 roots_247 goal_247 10 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_247 goal_247 := by
    have h0 : isConstB dom_247 goal_247 = false := by decide +kernel
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

end S_247

theorem lowS_247 : Lower true dom_247 roots_247 goal_247 10 := S_247.noCircuit

theorem lowS_251 : Lower true dom_251 roots_251 goal_251 10 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 1, 33)] (by decide +kernel) (by decide +kernel) lowS_219

theorem lowS_253 : Lower true dom_253 roots_253 goal_253 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3030303030303030303030303030303030303030303030303030303030303030, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_249

namespace S_254
def pairsG : List (Nat × Nat) := [(2, 18), (2, 34), (2, 130), (4, 36), (4, 68), (6, 22), (6, 38), (6, 70), (6, 134), (8, 72), (8, 136), (10, 26), (10, 42), (10, 74), (10, 138), (12, 44), (12, 76), (12, 140), (14, 30), (14, 46), (14, 78), (14, 142), (16, 18), (16, 144), (20, 22), (20, 52), (20, 84), (20, 148), (24, 26), (24, 88), (24, 152), (28, 30), (28, 60), (28, 92), (28, 156), (32, 34), (32, 36), (40, 42), (40, 44), (40, 104), (40, 168), (48, 50), (48, 52), (48, 176), (56, 58), (56, 60), (56, 120), (56, 184), (64, 68), (64, 72), (66, 70), (66, 74), (66, 82), (66, 98), (66, 194), (80, 82), (80, 84), (80, 88), (80, 208), (96, 98), (96, 100), (96, 104), (112, 114), (112, 116), (112, 120), (112, 240), (128, 130), (128, 136), (128, 144), (132, 134), (132, 140), (132, 148), (132, 164), (132, 196), (160, 162), (160, 164), (160, 168), (160, 176), (192, 194), (192, 196), (192, 200), (192, 208), (224, 226), (224, 228), (224, 232), (224, 240)]
def r1sG : List Nat := [2, 2, 2, 4, 4, 6, 6, 6, 6, 8, 8, 10, 10, 10, 10, 12, 12, 12, 14, 14, 14, 14, 16, 16, 20, 20, 20, 20, 24, 24, 24, 28, 28, 28, 28, 32, 32, 40, 40, 40, 40, 48, 48, 48, 56, 56, 56, 56, 64, 64, 66, 66, 66, 66, 66, 80, 80, 80, 80, 96, 96, 96, 112, 112, 112, 112, 128, 128, 128, 132, 132, 132, 132, 132, 160, 160, 160, 160, 192, 192, 192, 192, 224, 224, 224, 224]
def r2sG : List Nat := [18, 34, 130, 36, 68, 22, 38, 70, 134, 72, 136, 26, 42, 74, 138, 44, 76, 140, 30, 46, 78, 142, 18, 144, 22, 52, 84, 148, 26, 88, 152, 30, 60, 92, 156, 34, 36, 42, 44, 104, 168, 50, 52, 176, 58, 60, 120, 184, 68, 72, 70, 74, 82, 98, 194, 82, 84, 88, 208, 98, 100, 104, 114, 116, 120, 240, 130, 136, 144, 134, 140, 148, 164, 196, 162, 164, 168, 176, 194, 196, 200, 208, 226, 228, 232, 240]
def mpG : Nat := 0x3fffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_254.map (· &&& dom_254)
def goalM : Nat := goal_254 &&& dom_254
def NN : Nat → Nat
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 7, 0 => 0xc24c7b8e
  | 8, 0 => 0xbc4898b1
  | 9, 0 => 0xe411b243
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55555555555555555555555555555555444444444444444444444444444444445555555500000000555555550000000055555555000000005555555500000000550055005500550055005500550055005500550055005500550055005500550050505050505050505050505050505050505050505050505050505050505050504444444444444444444444444444444444444444444444444444444444444444000055550000555500005555000055550000444400004444000044440000444455555555555555550000000000000000555555555555555500000000000000005555555555555555555555555555555500000000000000000000000000000000
  | 0, 1 => 0x5555000055550000555500005555000055550000555500005555000055550000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 7, 0, 0 => 0x65432107
  | 8, 0, 0 => 0x685473108
  | 9, 0, 0 => 0x68543107
  | _, _, _ => 0
def stateW : Nat → Nat
  | 7 => 32
  | 8 => 36
  | 9 => 32
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfffff001f0000000f1e79fc3c03f800fff8000000000000000003c79fc0fff800003e0000000078f3f81f800000001f0000000f1e79fffffc007c0000003c79e7ff000ffffc000000000003ffffc0000000000000000
  | 0, 1 => 0x3c780fe07ffc00000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfffff933f26cb367f9f79fc3d03f820fff90208904a444124882bc79fc0fff80088be0910524578f3f81f811109123f048a245f1e79dddf6c086c0128003a75c6ff080ffffd020890448a43ffffe0440890448a24504
  | 0, 1 => 0x222093c790fe07ffc40821
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 86 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 86 (i % 8)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN0 : Nat → Nat
  | 6 => 1
  | 7 => 13
  | 8 => 45
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 6, 0 => 0xe411b243
  | 7, 0 => 0xed55dd8de411b243ce6d1f69ad430ebba78616cc9a8361fc6a9dfbf95690c6d3449efc7e3124e95222e2cd6a1e37db38011164f6
  | 8, 0 => 0xf312a16df0082887e8fb7100e411b243cbadcc77bf6af459ba49dbceb2a5eb27a75f4549a3181db29017b1718d41201786b9bf387fcc6d6f7d6ed8287673bbb273b0c5376db3b0fc6a9dfbf964d8d4a5630b5de862383d19617215ea520cc69b4dd598e24c2153ad4af7b5234988497743dfa91a42b8d96b41be95b93fb389a436f7cdec35723b072991d0a928862509285923f9276ebe2a2592036824d69e1c2497b16219d9618b15ef81d611b24bec0cf8e798
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 6, 0 => 0x0
  | 7, 0 => 0x3000301050601040001010302
  | 8, 0 => 0x40200000203000003000505040003000304070301040004000303040400000002030404050400030200040503
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 7 0 (CN0 s)
def CN : Nat → Nat
  | 7 => 11
  | _ => 0
def CH : Nat → Nat → Nat
  | 7, 0 => 0xf66ec1a6b1f468709ab86ad080e4918c7281bfbf55a9c92c4858ed8e406f385124b044270766edba04032745
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 7, 0 => 0x1510305440c1510250440815103504411411035044001510305441015105
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 5 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_250 roots_250 8 s ws hint
  | 1 => checkCutEntry true dom_252 roots_252 7 s ws hint
  | 2 => checkCutEntry true dom_222 roots_222 8 s ws hint
  | 3 => checkCutEntry true dom_238 roots_238 8 s ws hint
  | 4 => checkCutEntry true dom_246 roots_246 8 s ws hint
  | 5 => checkCutEntry true dom_190 roots_190 8 s ws hint
  | 6 => checkCutEntry true dom_108 roots_108 4 s ws hint
  | 7 => checkCutEntry true dom_126 roots_126 7 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_254 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_250 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_252 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_222 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_238 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_246 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_190 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_108 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_126 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_254 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_254 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccccccccccccccccccccccccccccccc, 126)]]
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
private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
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
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 65), (2, 18), (2, 34), (2, 130), (3, 19), (3, 35), (3, 67), (3, 131), (4, 36), (4, 68), (5, 21), (5, 37), (5, 69), (6, 22), (6, 38), (6, 70), (6, 134), (7, 23), (7, 39), (7, 71), (7, 135), (8, 72), (8, 136), (9, 25), (9, 41), (9, 73), (9, 137), (10, 26), (10, 42), (10, 74), (10, 138), (11, 27), (11, 43), (11, 75), (11, 139), (12, 44), (12, 76), (12, 140), (13, 29), (13, 45), (13, 77), (13, 141), (14, 30), (14, 46), (14, 78), (14, 142), (15, 31), (15, 47), (15, 79), (15, 143), (16, 17), (16, 18), (16, 144), (20, 21), (20, 22), (20, 52), (20, 84), (20, 148), (24, 25), (24, 26), (24, 88), (24, 152), (28, 29), (28, 30), (28, 60), (28, 92), (28, 156), (32, 33), (32, 34), (32, 36), (40, 41), (40, 42), (40, 44), (40, 104), (40, 168), (48, 49), (48, 50), (48, 52), (48, 176), (56, 57), (56, 58), (56, 60), (56, 120), (56, 184), (64, 65), (64, 68), (64, 72), (66, 67), (66, 70), (66, 74), (66, 82), (66, 98), (66, 194), (80, 81), (80, 82), (80, 84), (80, 88), (80, 208), (96, 97), (96, 98), (96, 100), (96, 104), (112, 113), (112, 114), (112, 116), (112, 120), (112, 240), (128, 130), (128, 136), (128, 144), (129, 131), (129, 137), (129, 145), (129, 161), (129, 193), (132, 134), (132, 140), (132, 148), (132, 164), (132, 196), (133, 135), (133, 141), (133, 149), (133, 165), (133, 197), (160, 161), (160, 162), (160, 164), (160, 168), (160, 176), (192, 193), (192, 194), (192, 196), (192, 200), (192, 208), (224, 225), (224, 226), (224, 228), (224, 232), (224, 240)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 11, 11, 12, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 16, 16, 16, 20, 20, 20, 20, 20, 24, 24, 24, 24, 28, 28, 28, 28, 28, 32, 32, 32, 40, 40, 40, 40, 40, 48, 48, 48, 48, 56, 56, 56, 56, 56, 64, 64, 64, 66, 66, 66, 66, 66, 66, 80, 80, 80, 80, 80, 96, 96, 96, 96, 112, 112, 112, 112, 112, 128, 128, 128, 129, 129, 129, 129, 129, 132, 132, 132, 132, 132, 133, 133, 133, 133, 133, 160, 160, 160, 160, 160, 192, 192, 192, 192, 192, 224, 224, 224, 224, 224]
def r2sG : List Nat := [17, 33, 65, 18, 34, 130, 19, 35, 67, 131, 36, 68, 21, 37, 69, 22, 38, 70, 134, 23, 39, 71, 135, 72, 136, 25, 41, 73, 137, 26, 42, 74, 138, 27, 43, 75, 139, 44, 76, 140, 29, 45, 77, 141, 30, 46, 78, 142, 31, 47, 79, 143, 17, 18, 144, 21, 22, 52, 84, 148, 25, 26, 88, 152, 29, 30, 60, 92, 156, 33, 34, 36, 41, 42, 44, 104, 168, 49, 50, 52, 176, 57, 58, 60, 120, 184, 65, 68, 72, 67, 70, 74, 82, 98, 194, 81, 82, 84, 88, 208, 97, 98, 100, 104, 113, 114, 116, 120, 240, 130, 136, 144, 131, 137, 145, 161, 193, 134, 140, 148, 164, 196, 135, 141, 149, 165, 197, 161, 162, 164, 168, 176, 193, 194, 196, 200, 208, 225, 226, 228, 232, 240]
def mpG : Nat := 0x3fffffffffffffffffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_255.map (· &&& dom_255)
def goalM : Nat := goal_255 &&& dom_255
def NN : Nat → Nat
  | 7 => 2
  | 8 => 27
  | 9 => 28
  | 10 => 6
  | 11 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 7, 0 => 0x259698901a9e731a
  | 8, 0 => 0xfc74c8e8ed77fe00e98924ffe7d0afb4df49284bdec1d733de043ae6d7c1e1e0ae1ad347a1b9159d952522248aea848487186f657e30c15d76c8714375e5babf6c273239648841cc61429b2d60c3847f4d772eb247f7c26f4225973d383bd18d3556e6683215abdb309b092e
  | 9, 0 => 0xfb546106eeb31427e0a69623db29e05ad3519150d1d6eea3cad9e238c95f3f8bc6064579c3cc8c2cb98a270dacfca66aa78771a2a29aaafe9959edfe991fb43f8f8b378681e1b9ae682e73866807ea48649c53055d23533c572f07c64f56b8bc2fbcfbca2b18659222e3782a120b6d6d
  | 10, 0 => 0xc53ff79abec9ac88a36829b1a1ed87043709f1262901cdd6
  | 11, 0 => 0x1f6d511d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00ff00ccffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | 0, 1 => 0xffffffffffffffffffffccccffffccccffffffffffffffff3333333333333333ffffffffffffffff3333000033330000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff003333333333333333333300003333000033333333333333333333000033330000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff003300330033003300ff00ff00ff00ff0033000000330000
  | 0, 2 => 0xffff3333ffff3333ffff3333ffff3333ffff3333ffff3333ffff0000ffff0000ffffffffffffffffffffffffffffffffffffffffffffffffccccccccccccccccff00ff00ff00ff00ffffffccffffffccff00ff00ff00ff00ffffffccffffffcc333333333333333333333333333333333333333333333333000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000ffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc
  | 0, 3 => 0xffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff0000ffff0000ffffffffffffffff0000000000000000ffffffffffffffffffffccccffffcccc00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00ccffffffffffffffffffffccccffffccccffffffffffffffffffffccccffffccccffffffffffffffffffffffffffffffffffffffffffffffffffffccccffffccccffffffffffffffffffffffffffffffff33333333333333333333000033330000ffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc
  | 0, 4 => 0xffffccccffffcccc0000000000000000ffffccccffffcccc0000000000000000ffffffffffffffff0000000000000000ffff0000ffff0000ffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc3333333333333333333333333333333333330000333300003333000033330000333333333333333333333333333333333333333333333333333300003333000000000000000000000000000000000000ffffffffffffffffffff0000ffff000000000000000000000000000000000000ffffccccffffccccffffccccffffccccccccccccccccccccccccccccccccccccffffffffffffffffffffccccffffcccc
  | 0, 5 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 7, 0, 0 => 0x1c61440c804081c61440c20408
  | 8, 0, 0 => 0x1db18d1440c102476461440c14c091c634510368102476463456040c091d718d1440c102472863455840c090075461440c1020728634510350091d218510305302474461440c9040900749134540306073c634510304091c6345103381024718d1440cc2c091c61440c92c102472861440c90409
  | 8, 0, 1 => 0x718d1440e304091e218d15810302478463451032c191e018d1440c102472861440cb4c091df18510305302476461440c904091de18d1440c102401c61440c9040800718510374102077063451032c09
  | 9, 0, 0 => 0x72863451032c090074463454040c1900784634510304091dc486345103040a00770634510304090074863454030409007946345103040900718d15610304091d118d158103040a00718d1440c150090001c61440c14c08007646345103040900718d1440cc040900718d1440e4040900749134510304091dc286345103040a
  | 9, 0, 1 => 0x718d1440c1a0091d9446345103040a0079c634510304090071851032c14c091d918d1440cb040a1d9286345103040a00718d1581032c090072863456040c0900788634510304090071a634510304091ca18d150103040a1d218d1440cb040a
  | 10, 0, 0 => 0x1c63456040c1024744634510304091c63451032c1024728634510304091c63454040c102474863451030409
  | 11, 0, 0 => 0x1c63451030408
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
  | 0, 0 => 0xf83e00007fc000ffff80000000000000000000000001f0f803fe01ffff00000000000000001ff8000000000007c3e3fff8001fff000000000000007e000000000ff01fe07f83f80001f07c000000000000003c3c7879e1cf1ffffffffffffffc1e0000ff00000007f83f8ffc000007fffff0000000000000000000003fffffffe000000000000000000000000000
  | 0, 1 => 0x7fffffff807fffffc07f81fe0fe3fffffffffffffffe01ffff000000000000000000000000000f87c7fc03ffffffe000003ff000001fff81ffe01ffff0000000000000ffffffffffffff0000000000000000000003ff000001fffffffe01ffff0000000000000ffffffffffffff0780003fc0000000000003fffffffffffffc1e0000ff0000000000000
  | 0, 2 => 0xfffffffffffe07ff807fffc0000000000003fffffffffffffc00000000ff01fe07f83f800000000000000fffc7ffffffffffffe0fe3fffffffffff81c000000000000000000000ffffffffffffff000000000000000000000000000001f0ffe3fe01ffffff01fe07f83f8fffffffffc3e00ff807fffc0000000000003fffffffe0007e000000000ff01fe07f83f8
  | 0, 3 => 0xffffffffffffffff807fffc0000000000003ff000001fffffffe01ffffff01fe07f83f8ffffffffffffff0000000000000001fe0fe3ff000001fffffffe01ffffff01fe07f83f8ffffffffffffffff807fffffc07f81fe0fe3fffffffffff81ffe01ffff0000000000000ffffffffffffffff807fffc0000000000003ff000001fffffc00000000ff01fe07f83f8
  | 0, 4 => 0xff807fffffc07f81fe0fe000fffffe000003fe01ffff0000000000000fffffffffc3ff8ff807fffffc07f81fe0fe3fffffffff0f803fe01ffff0000000000000fffffffffffe07ff807fffc000000000000000000001fffffffe01ffff0000000000000000000007c3ff8ff807fffffc07f81fe0fe000000001fffffffe01ffffff01fe07f83f8
  | 0, 5 => 0x3fffffffe0f07fc000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf83e84207fc080ffff90080888911044924a10810849f0f903fe01ffff11102220890492109ff8011081222127c3e3fff8001fff000421042122217e044242212ff01fe07f83f80843f07c044209088484427c3c7879e1cf1ef7bf7bdb77bf6c1e0400ff00000007fdbfdffc108407fffff4020211011112222892413ffffffff008402110108848889111440220
  | 0, 1 => 0x3fdeff7ba93ddeddd53baaef6777ffefbdedffffffbb81dded44dc89ba2590542102109221024f87c7fc03ffffffe000003bd852949dde81fba81dded005400a805805ffffffffffffffc460633133336667992c93ff852949fffffffe81ffff5554aaaaad94dbdefdef6ddefdb0780003fc0000001bb6db6f7af39c977bf6c1a0000ed0000000225905
  | 0, 2 => 0xef7bef7b7f7e47ffe07fffc47708ee236137ffffffffffffff55a5aed6ffcdff9ffcbfc4234739fa21024fffd7fefffffffff764be7bdefbdeddde81f11818cc400cc019804804bdefdef6ddefdb0400003100000001992c9252914a5bf2ffe3fe25ffffff11fe27f93f9fffffffffc3f40ffc07fffe6664ccd3249a7ffffffff2297e255252a96ff89ff17f83f8
  | 0, 3 => 0xbdefdef6fdffdbff807fffc4440889bb6db7ff042101fffffdeea4f77b7754eeabbd9ddbdefdef6ddefdb0501003580000001ff2ff3ff956b5bfffffffea5ffffff55feaffdbfdffffffffffffffffe97ffffff77fefff6ff7ffffffffddec1fbb81dded88dd11bc45a25ffffffffffffffffe07ffff7776eefbb6db7ff146313fffffd44a4a652ff45fe8ffcbfc
  | 0, 4 => 0x245296800000bf895eefeec45d89764be400fbdefe000002ff017bbf99993334c9269fffffffffcbff8ffc97fffffe67fcdfe4fe7bdefbdedd0e803bb01dded0098013001001ef7bef7b777a07eee0777b4037006e01601400000000ff7bfdee80f77b5554aaaaad94d000000003c9ef87b893ddeddc43b88ee476442104212ff7ffdeea4f77bff55feaffdbfd
  | 0, 5 => 0x1ef7ef7b60f06fc01800000cccd999e64b24
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 142 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 142 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 41 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 41 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 41 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 41 then wireAt i else 0
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
  | 7 => 23
  | 8 => 274
  | 9 => 229
  | 10 => 109
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 7, 0 => 0xfcfabaaee0a8b164d5aa71aeceb067e4cdd8668fc90c115bbd0e7e91bb6194a6aa4d5379a7beec4d9ef712a97de2a88c780ca4c86ceb83066a447a356357064d4a1e8d74412e8044408a10bb3521c9331f6d511d1786bf0905787220
  | 8, 0 => 0x3360f813331617af319a32ce30d35ff430bb7e992d978ca32b947a6c29aa48f42925707f28fd16d0269fe8cd25c186d2250a432f244273a0243252e323aef9ea231fd1d422c6198d21e64c70205786301f6d511d1ecc12d01e627add1e14ed861d0f1db41c843c1b1b75c6761af236071a54c46b1a06f5da18e53ac517b167201787682d171c010416bdf66c14fd550214d54445118738aa10c40fb5103290c21001f4830e41d9000d125ebe0cd9e9a00c64a6980c0a10cf0b66835a0b02f3e90af82e250ad5c06e0ac2df6709e62b78096ed2a0094009af081e6cca06d1e76b055e1920051e1441030c527d030b82f403005694029b98e1024a8026004956f6
  | 8, 1 => 0x72da683e72c034957229a798700bd10a6fe899776fd1d86e6ee674066d0fd08d6cbd2ed46c9239c76c4e911b6904737868e5b4c56785fff86689985f66644bc8657da0bb652362396393ac1f635380286234b37d6227a82962190972619fef7860e4cbea6080f9fa5c9ba8b65c9b7e5f5c7b6b735c0c8db05ba22ad55a15627957d05a6a54e9a0765297b4635207434551eeff064fb6e1464beeb55c4a1cf6a849e6ff8c49d3302647e2c09947a67ae546fc834d46a873e44433a3a6438acf4742c2b8c2425d289f40e3097d3e04ace33d25fafe3c2230c83bead2073be9561b3b4b99f33909d4c438dd38fa38390dcf36c2f1e336acb38e35c1f6f034f2a7e5
  | 8, 2 => 0xb2442eb1b121816aae4f6ed4ac8c922eaa4533f0a8219417a7beec4da6d57a45a6a609d1a42e3395a1105417a03bdcae9feaef249fc9a0f19f9bf8ed9d40fd8c9b62d68a995ec4cb99453c879889fbcc9721912296dfbf10964d4a61963da41b953f7cda94e509e5946f3b1b917a0a939091edc88f0a515d8e58a9228c3e92ce8c1ea5498bd59f378aab226789d038cc89afc8e389521d5286f07a3d85c3178e85b0f0db85377159840d36e683b5018281426e6681048cce8090404b807a5379807412727efa081e7e3c10537ba34d1a7a9617cd7a94c45279a8285378f9cd3d780bf019774d796576e3cf3576930320755505d57530eafc746a2171735400aa
  | 8, 3 => 0xf39972dff39347f7f27274c4f23dd491f17ebf55f03960baef95bdabef890b42eea60092eaaec46eea53aec8e92e3cb4e91d9084e793458be7013836e693bae2e50622c7e4c5de14e434ff8de2d15ff7e23d2abfe11e2e02dee92e2adecf4bc1de34b148ddf3d074dcd6a9ebd79c4852d72a7686d708d786d5d82450d5d0a69dd5aa71aed2638e96d1f505a0d15272aed14224d0cfc1b6cbcf472c71cd45837ecd28c99ecb87b06ecafe2540c802b4fcc6682d65c52ffa3bc303b3bbc2240b85c16b5139bfcdd14cbeb7e142be7a10f7bd584adbbd2514a5bbd9639cba4ff55cba3d190cba28b09cb9b262f9b51cd3cab5115d25b4bcd0e3b301bc1fb24eb633
  | 8, 4 => 0xff55b039fcbb6548fc2996a1fb8f89aafb594968fadee4f9fa50d067f8d2ca58f7c688f5f6f875d0f64579fdf55eaf1ff54b8be5f51834d2f4fd0e26f4cfcb84f486f9dcf40d700f
  | 9, 0 => 0x42c4851c4271b5b34149e26f409e6ddf3fdceec43fa54a8c3e3c88d63e154dfa39e8e89639e564f238dd38fa355dde033528f72534ceec1a34cd8a0032a3a9f23269e6ac30d35ff4303465862ddad6bb2dd6f0592d8ab5e22c7e4a192c1c6cab2c1013352a7d3b7b2861bb912804a21c25e85f982294ce2e21260baf1f6d511d1ddf700b1cb675b21cae37701c6ef9ec1c39e7161b0391791aa822fd19e4348918664b10148d4667148caade13c636aa13b24def0ffb22c30dda90c50c9fffad0bdefcdf0a70e74309e62b78089ecb92078acef107787420072f7abd05e1336c05be135a04e81c7f030b82f4024a802601df342d0147f87001017fef005308ca
  | 9, 1 => 0x862b6dce85b0f0db84cab60d83b5018282e70a7a81f42a0280784bee7ffbbd527fcb138f7fa48a517f7fd4a57f4f399a7ec567b57ea9cc887c7db9d37b8033fc7b0317267acad59a7902d3697864bef47833e341770d3dc8770062c876e3cf35766c42f4766740997530eafc75239e7373ad327b71c2f03f6ddb39fe69a06ce0666f4b8566644bc864f4a8d86328e797623465ae61a6784e60d50e525f709dbf5f0800915df9c1815c9b7e5f5c8170105bd043af59f7adae527cea9052366fcc51ab119e518814b65079d9034f6283cb4df43a944dc8205f4bb433124a1cf6a8493ad02e48ec38b948867b6047c02d81477def8247015f294433a3a643311a75
  | 9, 2 => 0xd054d06ecf472c71ced47453cc728f4acacc1c0aca74c0fdca539acdc9a4bc39c85e2941c82e7c3ac6cabe6ac6b9915ec6b3d98dc429297cc39ecf0bc1445c96c12c7d57bfbe3420bd2514a5bbe332ecbb7d41aabb04c9babaf7e834b996971eb630ad6bb23d31b1b1b610d0b0cad4a2af29c7ecacaa4413ac3bc4b1ac306087ac20ad48ab8203bdab20a6f2aaa4460da9d06c49a98fdd4ea8de2971a8219417a6c2a987a2ee6ab7a2dc6b39a1fc3d1ea1a6db91a10c1f33a0f728cf9cce41a39ca2a3839c6ba00d9b85f20c96c51957953f7cda9292c06590595f1e9038c9658fae460e8e806f3e8e58a9228e03e0a28adf63fa88a245678847196e883b1765
  | 9, 3 => 0xff8429a3fd666bf6fc92b301fc2996a1fadea7c9fa8479a1f9b7c88bf964051cf92bc390f7b120e3f60b40f5f3e9acd1f20e2071f18c0ac4ef6ce923ed4b7c76ec02c2dcea86b8a1ea3b12dce6a0fc6ce693bae2e38fff11e27472f1e185681ee11e2bd0e0076644deafdf77de8cc397dcdc97a3dc73e58fdaafb44bda810c3bd6664c91d5aa71aed27d118ad16720e9d0f191dd
  | 10, 0 => 0xa93e40ffa8428216a8219417a537aa92a11054179d24802d99fba56c998e0a2996771fec950d0fcc90e08e6289cdb3478225b50280de14227d6b3a457947c50776e3cf357667409975d8da117530eafc711baf256f847ff062552b8f6080f9fa5c5449ff5c0c8db059cb79fc527b690248bc19ea4433a3a640d73a273e0a25a03d00ae463c2c192b38dd38fa37ccc8093575c9ce3152270e2c2c4fd02bba0d512b947a6c27efcc96269fe8cd244273a021426c551f6d511d1ee53b201da2926f1bb8b71b1737fe4215d15dda1236b6d810a93c2a0e4db3960d17918c0af82e250ac4f0c905f2eeb103e10b57030b82f40297ddda024a802601aca8ac00b1f0b4
  | 10, 1 => 0xfc2996a1f9999b28f6b19054f3259d20f0f38f97ee4ccd72ee3bf4f4e9d94aa5e8a7c67be695e5dce27472f1d8c448a3d736708ed6c89b86d575d99fd55502efd457dbf1d159d23fcfa48b3ecfa2954ece28912fcbaf4de1cb236c0ec9158e5ec7a6811fc52151b2c510e825bfcfd872bfabba69beb365c7bdd6512bbda81d4fbd2514a5bcfc20a8ba64b203b84e0c67b7614604b3c975d4b24eb633b1430605b076404daf47401faf38c163a98fdd4ea974856f
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 7, 0 => 0x50200000201050504010502020200070001030004
  | 8, 0 => 0x1020002060e05060601060d0b00060208000401030a040505020800050400040408010203040f04010903030609021004080202030008060000000604040304000903040508000b0008000d00020400030c0106030100030d05000f0f1000020e080501020c0a030205010205060305001001040800060206010500010c0203
  | 8, 1 => 0x10c00000602080e0a030c0505050904080d0200050f03030809060503050500050d02010408000204040b0d0306030f08010006050200020008030e050503020a0a0d020b000502010602030c0c05020002060200050105020908080b0900080a0803020a020609020600000b0506010a090800000f0400010a00060e020005
  | 8, 2 => 0xa01000306000800000204080108080d0603
  | 9, 0 => 0x5020200020400000b0b00090202040304040502060b050000000203001002080402040e0804050b0504000201080a04020000040002000404010f040102020001000200050200010402000a000206040004000402040501040002010400060302000003000400030602000001030a000200040310010203000b000204020108
  | 9, 1 => 0x101030004030104040202030006050b0c0a0d06040204080904000400060500010508000000000000000e080502010802020502020100020206010808020f0000010a04020202050604040000020d0400020103060401020002060a080000000003060408
  | 10, 0 => 0x2080506050808030306040305030508030505030503060606080308080608060205060808080208030803010508030105050308050303080508030503040003040303050503040806050103060508000308030803000300020303050603080603060603000508060006020308
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 10 0 (CN0 s)
def CN : Nat → Nat
  | 7 => 29
  | 8 => 522
  | 9 => 789
  | _ => 0
def CH : Nat → Nat → Nat
  | 7, 0 => 0xf779eba3dfe66c26d0b4f89cd04bb275bc8858e5b69d4ec0b2f0db19afefee7faa9c1ee7aa3b9116a38e30d5a1e631808bfb7aac7af3a6566d0abd4568686cc6665d5d04572f07c651d5513e507a3de84fed79e349ccdda73e939e141bcb6cfc1b6b4c4a11948ca408b34886089208d40712411e
  | 8, 0 => 0x217ef7d320697d241e60d0f31e579c851e3765711c84d4601c81e42e1c5d30171a36299a17a15ad916d2ee1616758b2e16357c7a1603eea215c5868c15302c7c14065dba13f1967c13cc8e9313b24def13ab984113098de6120cfa0511d4013111aa0a8011861852112ef9b1112b6746108b86ba1085ff4c0f3c2e200ee6bd3b0e8a522f0e4671110e261b2e0d93c3a80d16b9980c19929a0be3340e0ba23e680ad17cab0a9eefdb09a97ac108deefa008cf01cc0872c00a08184eaa0778742007774d83076641e707644bf706b476a00685673a05ea47d805cc30830593d94d0518032204eaa7d603d6dc7f02e522b7028dd2b30215517600d7450700276c9a
  | 8, 1 => 0x413cac9e410f78463ff37f213fdf3bb13f6a96313e63fe2b3e37f1a03db4a55a3ba2c2003ad7e6493acd399d3a5994833a0c36cf396e5f5538b6def8386ca608383f7743376f5374368e3a0035c964653485ff2533eb4d4a33ea8e15339ae10b3390d019337ca3ab326e7fd33246304a3231605131dc616d31db097831b829af3196ff5131921702315b51d12fbcfbca2e40f8982ced80ca2cc106f92bb9c4e12b7f0a9f2b65f3a32b1865922ae753c92ad92f9e2a3f22342a3ae3a029c4589128f98278286c48de28608f892804a21c26c5d13f260e841b25fdab9d25b70a16259a5a7f24f4eddd24db72c424b8936224a0f902237e6054227ce15d21e229e6
  | 8, 2 => 0x65a5ceb5659c8d6463ee0679637bc3fa635631156334f16361264e365fb1833f5f709dbf5ef86e745e619f765dcb8c0f5dc492335dc43e5a5d23533c5c50e9625c042a495b35bf0759cb7f3159a54a42590422fe57d934355762dab057489ab456f2212656bfe42855dcdb115564491854ec6a71549e7970537a6dc45306f99a51a5eb32512bd3f45088999c4f8a08b04f56b8bc4f0508794ef9b4eb4e3e58f74de3f33d4d9314834d8a65cc4d16c9274d0e37c64cf04eef4a7e49314a7b53a349f86d8148943852486af2d3474c9388471b47b847159afc4680b174467b56e6466e4204460f6a3f4513bcd14500b4394439458842b9e4ce428a73e6427c0013
  | 8, 3 => 0x8204d0e281bcecb681b602a681243000811702c980cb4d67807dd093807acec280424a09803d746f7fa1d46b7ec2fce17d96abd67d2aec747cfbda2e7c7db9d37c6ffb6b7bf55a4f7bdacc207bc364027b14912e7b0317267acad59a7aa1d4c97a3508417898f0d077cc1991776e8c5e7725192b767d9031762ce29e75f02e1a75ec1fe175cbdc497502ed8474632fa873fafeb473edcfd473983ffa73274e2172dc6aa4722dc30b71a71b9b70b0eeff709eefa3708eddab708a65c16fbbc1266f8e7eb26ecba7cf6e8798676bed87026a65609b6a038ebe69dd058069647e716913ddb7682e73866807ea4867d40ac466eb8aba66550271662cd93365dce47c
  | 8, 4 => 0xa22e975ca1dc6977a1a36dda9ff4de0f9f1bd59b9e33ab429df2e2ef9d7bb4379d34fb449d29e53f9ca2a3839c998b159c7840429c6ba00d9bfca1079b76797c9b6570ac9b2f38159b2f09369a8bdfc49a83aa8399682ef79961e76f9959edfe98f9bc1f980db2ff97f45b619789a0a1977cba849738d28b9533a751949963ac9481e2a1941600a893ce44599220a60991e6af8d918d30a5916052be9037cd6b902668218f8b37868ddc90d48c5262a38c1b46fb8bbf487d8b3b8d4d8af885e48accbfff8a6435278a549ef48a3d1fab8949cb5f88a4d3778831a85987fc5e6687543b868617bb3185cb993e83f8516a83b6d4e683afc38582d17654820b986e
  | 8, 5 => 0xbf337efabe0a0f69bd72a784bb8a0aabbad221e1baa7eac2b9e76babb9bc2645b8d936a7b89fcacbb809420cb7f4725db7d686e8b7aea218b700f66fb6033f14b5de5b30b5d52201b4dd9d95b4a5f4eab43f707cb42b4489b41d3d7ab3be7d76b2d07219b2aee775b28c8c43b24204bcb154ea78b1097bb0b009ed1baff599eaaf6db791aea585deae28f742ae19682eae1831d6ad9a90baacf2a1a5acaa4413ac20ad48aba0ae57ab1d2677aa906272aa2c826ca9d06c49a98fdd4ea95c8cdaa8dd65cea8606185a84e2693a8445983a83016bba7463699a72f1199a6b9da40a69aa70da587916ea4a1de8ea4896475a46fc636a4292f66a3cd3f58a2d417ce
  | 8, 6 => 0xd9dc3f6bd9cc4046d9c682a8d9af3dadd97221a9d859e5d6d82a0458d7a853ecd72f0df3d6ea8707d6c57ef8d52c9314d50c39c2d4e636d6d469f128d4316b64d419d2a5d35c5db1d1e1bb04d1bd5c15d14fc0d2d0162f78cf00a749ce8de9dece88c0f2ce38d695ce3468f9ce1ab68ccda2f3a4ccd1890fcccec675ccaefd70cc4f07a5cc228640cb5bfeeccb345ac3ca54770eca510146c982547dc96676cac9624e05c95e6e02c8a2450bc7fa3715c7ebd41dc7db60b1c7a3fbdac75737cbc6078b0cc6064579c5e571ebc5a1a764c52d1d75c4541b7ac4293237c3cc8c2cc355a0ddc3361f80c31c3e02c30b5555c1ecf203bffcce0ebfbdb5b3bf4437a0
  | 8, 7 => 0xfb546106f9cc330cf9acd059f87f03aaf7918f1bf76d7112f68b6331f687fcbef6751c70f60b40f5f569d3f8f55a9e25f5360b5af4e6cb4ef4147c21f3917377f38cf4adf304f0e3f22668acf171ad9ef1051f8bf014fd13f00fc310efb0d89cef22fcadee428f65eddc891beda1a351ed727386ed646037ed50074aed4b7c76ec331089eb58a5e0ea86b8a1ea106cdce929119ce904bcaee8779993e837f6f6e708f6c8e6fa780ce6eb7e95e69e633be60e81a1e4e22387e4587c54e3fd7b5ae3ac5bd3e27bb15be27472f1e1fb7010e15193f7e0fff7a8e0a69623e00438bfdfe8365fdfe34ac0df3eee67ddbd8121dcfefb92dc7d39addb7e8c33db29e05a
  | 8, 8 => 0xff864176ff6837c8fe316649fe07260efd666bf6fd297c3efd01ae43fce3085bfca4ab3afbeae025
  | 9, 0 => 0x1a3db8e31a347de319e7202f194948b51907e86018f755d318a42072185f2ed4184e90bd183fd6b317e2304f178d45b316ee55a216ac0e45168d98f9165cbe3316402aa015c39c041557266d1535357c14db66f614596d82142f530a1360c44912bc928811363b3110780a900f876b6a0f40d7940ee0db5b0e57abde0e4e305d0dc88bdb0d7588100c4de92e0c35eff90c2c5a930b864cda0b4125650ac23d290a466d6d09abc96f097af5f508d6309e08902fa00831c8780827d20c0653a07706208d9605e96d7b05d894fd04d8ecb604a69b1d04a5eae9035e4a09034c4544032e17e10226f07c01b186fa01ace8920175eaae016612d900460d0d00446684
  | 9, 1 => 0x3184494f303ce9cd2fa059c42f9524d02ed49e4b2e6b228a2db5048d2d6f5e032d6dfde32d3919932cf6a4042c3d5aaa2bfe144b2bf4bb562bbe76e62b52c3de2ad6e90e2ac2b7fd2ab1e1622aa1c9fe2a09966129d356e129c2c53229a264fb29328326292a0eb228b1414e2879b7d92845dc3327f85b7f27b7e07927370f2826b0ba9f25ea539f25a510a0254d33d4250b2cab24b43195239089fe238c551a233de0c2226190d221c1e8f12182106d2150856d211f58c1211d64a920cc7afb203a6f8d1fa4b6141f65da931f1a6b841ecc1ac61df67e001d8f8eba1d88e2bd1cc795b01c7bdb531c483f481c0e40101bcb33911bab808e1b7dab601a71f880
  | 9, 2 => 0x42500e59422bf05041d129bf41a2f5e3416144c241339bae411fed3940f6f93c40e16c48406caf82405687124053843a402853363fce4be93f8c6c9f3f7c568f3f79d2333f60b0a63f0a46873e92c34e3e6b2bf53e5f8a973ce4e7ea3c80db983c73d95e3c6cc4323c49c6693c48e4fb3c2a9d0e3bdf13a93b5c1e983b4aace93b1223573ae6a3c73adfb6493ace424e39ea358939e17beb395800d738ea659438df0c5e37c44e6836b334df3681db29364c67783649abbb36498ec7362174c235d37b5735c0cc89354e8a0a353f3278353dde99347118e134696b3733c33bec336392cf33555724334218b3333399f732f6763432df5ca531c7760631b8f74a
  | 9, 3 => 0x5325d13f52d50655525096a35224c125522369c35222cb355186d5925185889f50a8c716509f61705076ec8a50281e7a4fe36a304fd29bb84faa26754f6968124f472bec4f1e44a24f10e77c4ec6f49e4ea39b8a4e951cce4e5604884e4e73614e2f83c84e1528934da3a1f54d1269d74d1066f24c24f2204ba159b34b95c4454b0a510f4a6bb6e04a26b70649716b7d496b1ddb492cc7b4491c2a46490bc0b948eec71748d0e0da489a9c6a486ffffd484a089f4824021047a18799479edd81479ea25947911e0c46e2fa9446952aff463cc30145c095e445adbf9444da9a6d449405fd4493440d43cab10643c8efd943a692fd4356ad5a42f726aa42ae3e5b
  | 9, 4 => 0x646d439064059e0563b4c2d363a8f7a8637ac3cc635ff6b562f7bb2262cec72560ca8eb16058b9f36037588060323cf65f2c33dd5f0815d45eaa8cdf5e20b2e45e0fc1325db100c95d33ec815d32ac965d0478ba5cbf21375c587c135c0fe5bb5c0353e85b447e8a5b3149225ac3741a59c10d6e59bc9b3359b6a67559a54a42599c1c515970b233594fdb835948d16d5911f28658a79f375873da305852b4855831a17158215cb057f60f8657e75df757d538d657aa67d25715ac82570a9e9656d811d856bda16f5648e6ca5617170f55a6c5a95554aad35519e69c550b67e0549d4e4f541c84105409643b53da082653c8b93453b17361539f63d2539d6de2
  | 9, 5 => 0x781d9a03772c78bc772075b476d610cd76a4a09a7692cbf97624f6f175a5d307757731bb75753bcb755481de74ee682b74d2350a74c307cc74b15e5a740c40ab73fb37ac73f0ea0873b4375c73a92db973a3c7e17373c57e7247a6067236cd887181f45e71681a0570f6128b70e3a59370d5bb2d70d2649e70cd035970bc2adb70b62daa7082a2da6f00e6a96efef0b96ee834db6dd423396d84ec9a6d79279c6ca29f0f6c59808c6be9a8486bc005256b27fc626b0ba94c6af3f82f6ae38ea26a90be706a7fc7796a18090b6a1576b369161bc368bb06196871e9c967800a396702dc8a661bbf6765e8c6b865a27eef65a10a69657e60e664860c44647dad1d
  | 9, 6 => 0x8fabf1228f97c7738ef306b98ebfc95d8e7a6cf88da928dd8d98505f8d78640c8d757a1a8d4526b08ccd8b058c688c598c4cc4ef8bba31bb8a7290db89edc7458935a61088b84f2e88732498880421e687fbff0a87dbe3eb87211ff987065b8886ffb6fe8692b66e8661413e864558ba85f2414785a78140858bb8db851813c18514b0b584acc948842cde938332269b82dc41c081d0ce5c818ed0ea813d0ce980246f357fe6a1dd7f6d56ca7e96ef207e7f52357e15d8e77d9473bc7d09170b7c9b42037c5b86d17c2302187c19d10f7b48801c7b27a96c7b0da9637ab02bde7aac68e87a2a826e79f1cb987931c63b7918fca978e37b487871ae5b7820a40e
  | 9, 7 => 0xa54f4a1ca53d44e9a3c2a23ca3a64196a3902225a35d81e1a33d66c2a32286e2a2e013b4a267de5fa2424e49a1f43945a19d6b03a16a5350a1657107a1090417a06a1c84a03ee570a022c856a00e4c1fa00b9ca59fb38faf9f6c41a59f07f3f09ec8752f9ea18c859e38ed029ddf0d1d9c8436d19b32d6d69af1fe6b9a750b1b99cc366e99c2550b99b8342998f8439d98f5f69398c01cd198add190987ab42b9858f851985193c196c6361496b76b1c96318f6c960debbf953f8fa09507da4e94b6ecbf94a414be9473e0b3941f73ef940e9b71936230009329721192aa496c9281f88b927b58aa92488c2a9189da1391126a2090e4651090cde97d904feb02
  | 9, 8 => 0xb69459adb67be2a7b54cffa2b52db945b4c12036b4b523abb4205a13b3d25cf5b33f4c09b3245a07b3090228b2ea3809b2d2bdb8b265fb1eb25a87bfb214b77ab1d6fecfb1bf0403b1984575b1931243b12aaa32b0979746b0447092b0272864b0059795afb4e5e5af8f5300aefe8000aef46a84aecc274baeac85b7aea8d71bae71720fae3a4338ae14b053ae13bff5adaa0f01ad4b1a9daca9afd5aca81a1eac73ecf7ac70e7f2abeaa52aabc5952eabb3d9e9aaa4d0d0aa9ac161aa70027daa548990aa214c34a9b3b1d4a9201eb4a87d2e6ba86a8457a83d4c34a81d26a3a77f8f0fa77f4f29a7222f14a6b8fce6a6849731a625af47a6001cc6a556d020
  | 9, 9 => 0xc964552bc9403722c91f209dc8dfa60ec847e280c812e056c80d9cb9c76acde4c74c2801c73c9a08c71512d2c6e3e028c6d5616cc6bf63fcc6909d61c5fc4438c511be63c4d212bbc4b7e19dc3f92ebcc3bd4d51c37538ecc357700ec32b13d7c204fe34c1fa081ac1e28920c18b5d98c1112578c0fb86dac0f5c2bdc0dae108c09ec7c0c08a5b87c026f1bfbfdf221fbf80e42dbeac4f12be41968bbde03d86bd5df28dbd0aa4bfbcfeeddabcd8118ebcd44a9bbbf377adbbcb5557bbc7a09dbba40457bb5d6ee1bb5380bcbb351767bb151286bad782beba4cfdf0ba0abd06b970a262b8dbbcd8b8cd3e1cb8ca7702b8acf420b8095d55b7f5ffb5b7c2a67b
  | 9, 10 => 0xded47fe6ddec58aaddc65290dd9f6e86dd66810bdcbdf1bbdcad882edca277cbdc5d09b1dc4bafe3db887496db816211db48704bdaee4ef8daa0307dd93907f7d9371207d872fb96d8399465d7bd0de8d76c787bd7485a72d7292374d724cd8bd6f3bcddd6764196d65005d0d582ed4ad572f134d544bd58d543ca9ad4fb9ee9d4d22539d4c1b4aed4b7e8c7d498c0b1d30fc602d2bfee3ad2aa0b17d201520cd1fef64dd1ece558d1c264dad18cb3ced1795fc2d13afdd8d10d4b23d0ae8279d05f3b23cfeaac70cefde60dceb5ce6bcea564decdc27313ccb6f27ecb88ab3bcb6615ddcb3c4fd1cb1668bccaf0d5d7caca3e86ca151a1dc9eb563cc9a89828
  | 9, 11 => 0xf84e0f7ff7e14a2bf7d071adf7a4378bf7a3d45af51687b9f47d7b6ef4108598f39be50cf37f5884f36dc75ef3529a85f23c4334f22d7ea8f204b5d7f1d7c46df060e8acf0357925f02a6295f00f9b9feed31097ee8ec067ee653b8fed1279a8ecf1a2f8ecc70e6cec6ecdfaec08efaaebf47bfaea19b193ea064a23e9bd412ae95f04e3e8f67248e8187555e7ca7599e7af9b67e7412b47e73f3557e6a9e0a4e6500423e5c53138e4d56176e4c02d85e4b49b95e47bd28ee3dccc1de34bedeae3012fe1e2d354c3e2c00c17e2ad9f1fe258c55ce1febfa8e0caed47e0b22e67e05d183fe04f2293e0339592dfe4d854df432128df1bb446df0a5658dee97fa8
  | 9, 12 => 0xffeb702cffdd5565ff9e2079ff8e9861ff0e9b03fe3285e5fd429d9bfcba19d9fc2ebbd5fbc7faeefbb0a56afb68e91bfa880c50fa62192dfa1112faf9d3b2a5f95646b4f9540919f927d567f8e77680f8590ff8
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 7, 0 => 0x20975cc13030000036440059314d9305000de5648080073d1920482cdd564c0c594151930682cdd564c0c00369192012881d564c0ca207559303000de56480819304d93030000016440a0975cc1303000003644020975cc1303000dd56481459314d9305064c1364c0c5941519306064c1364c0c003795920286cc5564c160975cc1303001cf5648080027959200064c1364c0c0073d95202
  | 8, 0 => 0x9e56480c00704d9203001c746481800165192060009e5648200027959203001db35481400000db1000009e56480c0031459205001d736481400279592000009e56480c00001191040000035c400000005a104000c136480c00001591050009e56480c00000d9100001c335480c0000159105000d505480c0037559205001d7464818000005b102000de56480c00379592060009e5648000027959208000de56481800714d9208
  | 8, 1 => 0x5644140027959203001c336480c00379592060000015440800001591020009e564820000011b1040000036841000714d92050000041c41000374552050000046c4100071d19206001db31481400175592080001e56480c0035559203001db35481400000d91000005d56481400000d91000001e56480c0037415203001c336480c00000d91000005556481400075592030011d5648180027959203000d51548140037959205
  | 8, 2 => 0x56c4080070cd52030009e56482000000d5100001d74148180070cd9203000c53648140037559205000dd56481400304d92030000036440000379592060010546481800764d5205000003684040035559205000de56480c00001191040000041440400000591020005936481400279592080009e5648200071cd52080000056c40800000d51000005d56481400304d9203000003684100076cc5205000dd05480c0035559205
  | 8, 3 => 0xde56481800000d5100000de5648180017559206000001644100076cc1203000005644000027959208000de56481800000d91000009e5648000037959206000de5648080027959203000005644080047455206001c335480c0000105104001c74648180035415203000001684100037959202000dd56480c0070cd9203001d73148140000119104000de56481800279592030005e56481400000da104001db4548180017559205
  | 8, 4 => 0x9e56480c0037559203000c136480c0075cd92030000046440400155592050009e56482000164d9205001155648180037959206000d515481400155592050005e56482000375592030009e5648200075d052060009e56480c0075cc5208000de5648180071cd9205001d53648140047959206001d73648140015559208000dd05480c0037959206001155648180035455208000001684100027959200000d55648200030419203
  | 8, 5 => 0x1e56480c00000da1040009e56482000279592030009e56480000064d9203001c536482000279592030000016441000079592030009e5648000005559203000d55648140000119104000005644000035415203000de56480800000d91000000056440000001591050009e56480c0037559203000005644000017959205001db35481400279592030005556481800379592060000056440000000d51000009e56480c0075cc5205
  | 8, 6 => 0x1c73648200037959206000d51548140000107104000dd1548200027959208001d730480c0076d05206000001644080017559208000de56480800704d92030009e5648000071cd52050001d56480c00454552060009e56480c00000da101001db35480c00714d92050000036841000704d92030001d56480c00279592030009e56480c0000105101000005644000035559203001151548180037455208000de5648180015559208
  | 8, 7 => 0x5644000005559203000003544000041459206000555648140075cd9208000005644140035559208000d505480c0071cd9208001c735482000164d92050000036440000000db100000dd56480c0000159100000d556481400000da101000dd56480c0000105101000de56481400000d51000000056440800414592060000056440800279592030000036440000001591000000016440400155592050009e5648200000187102
  | 8, 8 => 0x1c73548140027959203000003684100037559205000d55648200027959208000dd05480c00175592050005d56481800000d5100001054648180027959203000d556480c0031459205000de5648080071d192060000056440800304192030000016c40800379592060009e5648000075cd92080001e56480c0000159105001db3548200000159105000003644000000107101000c106480c00355592050005e56482000000da104
  | 8, 9 => 0x1db3548140076cc1203000dd5648200075cd92050000046c4100075cc1203000555648200007559203001db3148140000119101000001544080037559205000d51548200000187102001c74548180027959203000003544000000197102001db30480c00179592060000016440800000da104001db30480c0000105101001db3148200037415203000555648180075cc1203000de5648200027959203000dd5648140000105104
  | 8, 10 => 0x1556480c00000da1040009e5648000075d192060009e56482000279592030000036841000000551020000036c40000314d92050001936480c0016519206000de56480c000015b1020000065c40800355592030009e56480c0075cd92030000065440800379592060011d5648180027959203000dd05480c0071cd92080009e56482000354552050005556481800354152030001936480c0071d15206000555648200037959206
  | 8, 11 => 0x11e5648180070cd9203000de56480800000d51000000036440000000551020009e56482000000d71000005556481800279592030000015c40800355592080000056440000155592050000056c408000005a1010005556481400304d9203000001644080071519206000003684100075cc52080009e5648200035455208000005644080075cd92050000036841000355592030009e5648200027959203000d556480c0037959206
  | 8, 12 => 0x1d736480c00715192060011d1548180035415203000de56481800000d510b00000354400000011b101000004144040075cd92030009e56482000000d51000000065c4080076cd52030005e56481800000d7100000dd1548140000119101000c106480c0075cd9203001db3548200000159102000001644080000119104000003644000017959206001db45481800000d91000005e56481800279592080009e56480c0000059102
  | 8, 13 => 0x3644000035455208000c136480c00000da104001c7364814000011a104000de5648180037559205000d556480c0076d05206000003644000035559203001d730480c0027959203000004684100000105104000d505480c0005559203000d505480c0027959208000005644140047959206000de5648180000159102001db35480c00279592030000035440000175592060010516481800175592060009e56480c0005559203
  | 8, 14 => 0x5d5648140076cc5205000001644040037959202001d730480c00279592080005936481400279592030009e56482000279592030000036840400064d9203000de56480800000591020000056441400000da1040009e56480c0075cc12030000056c4080070cd9203000003684100027959208000004144100027959203000de56480c00000da101000c55648140075cc52050009e56480c0027959208000003644000027959203
  | 8, 15 => 0x5644080041459206001db31482000055592030009e5648200027959208000003684040037559208000de56481800000d9100000de56481800001191010000046840400379592020011e5648180000159102001c335480c0000145102000de5648180075cd9203000de56482000079592030009e56482000001051010009e56482000000db100000d55648140076cd5203000001644080035559205001c136480c0000185102
  | 8, 16 => 0xde56480c0037959206001c736482000279592000000046841000379592030000036841000279592080000065c4080000159105
  | 9, 0 => 0x56441400001051060000035441400001591080000041441800000191030000030440c00000591060000031442000001591020000056441800000551080000016441400001591060000015441400000551050000056442000000591080000016442000001591030000036441400000d51080000035440c00001051010000031442000000151030000036441400000151030000006440c0000159105000003144140000019103
  | 9, 1 => 0x41441800000591060000016440800000191030000056440c00000d51030000036440c00000d91050000016442000000d91050000041441800000d51030000005440c00000c11030000056441800000d91050000046441000000d91000000005440c00000d91030000056442000000c51050000006440c00000d51080000056442000000591080000036440c00000c51080000006440c00000d91030000035440c0000059105
  | 9, 2 => 0x5440c00000591060000056441400000c11030000056441400000191030000035441400001191010000015441400000591050000041441800000d91080000046441000001591030000030440c00000c51080000036440c00000d51030000041441800000151030000016440800001591080000016442000001591050000036441400000d51080000035441400000d51050000030440c0000015103000001644180000159103
  | 9, 3 => 0x30440c00000d91080000015441400000d91080000016442000001591060000036440000001591050000016441800001591080000016441400001591030000015441400000d51050000035442000000551060000030440c00000d51030000030440c00001191010000015441800000191030000046441800000d51030000056441400000d91050000036441400000c5105000001644180000055108000003544140000105106
  | 9, 4 => 0x15440800000c11030000005440c00000d51080000016441400000d51080000036442000000d91050000006440c00001591080000015442000000591050000016441800000d51080000056440800000d91000000036440c00000c51080000030440c00000591060000056442000001591030000036440c00000d51080000036442000000191030000056442000001591030000035440c00000c51050000035442000000d5103
  | 9, 5 => 0x35442000000d51080000056442000001591060000030440c00001151060000056440800001591050000015442000000d91050000035442000000d91030000045441800000551080000006440c00000d51050000045441800000551050000031442000000551080000056442000001591060000045441800000d91030000031441400000591060000005440c00001591080000046441800000591020000056442000000d5103
  | 9, 6 => 0x15441400000c11030000045441800000c51050000015441400001191040000056442000001591030000006440c00000d91050000036442000000591040000045441800001591050000035442000000d91030000041441800000d51030000015441400000c51050000005440c00000c51080000056441400000551060000036441400000591050000056442000000591080000056442000000191030000005440c0000159106
  | 9, 7 => 0x36442000000d51000000031441400000d51050000056441400000d51030000016441400000591040000035441400000d91080000015441800000c11030000016442000000d91030000056440c00000191030000015441400001591060000015442000001591000000036442000000d91030000056441400001591080000035440c00000151030000045441800000591080000056441800000d5105000005644180000115106
  | 9, 8 => 0x15442000001591050000056442000000d51030000015441800001591050000006440c00001591030000005440c00000551020000035441400000551050000035442000000d91080000015442000001591030000035440c00000d91080000005440c00000551050000016441800001591050000015442000000151030000016441400001051060000016441800000d5105000001644200000105104000005644140000159103
  | 9, 9 => 0x36440c00000d51080000056440c00000551080000015441800000c51080000015440800000551050000015442000000591050000015441800000d91030000036442000000d91080000056441400000551080000046441800001051060000015442000000d91080000046441800001591030000036441400001051060000015440800000d51030000056441400001591030000046441800000c1103000003544140000159105
  | 9, 10 => 0x36441400001591060000036441400000d91030000015441800001591030000036441400000551060000056440c00000d51030000031441400001051060000035440c00000d91030000015442000000151030000056441800001191060000016441800000c51050000045441800001591080000046441800000591080000046441800001191060000030440c00000551080000041441000000551080000015441800000d9108
  | 9, 11 => 0x16441400000551050000056441800000d51050000016441400000d91050000036440c00001151060000015441400000151030000041441800001591050000036441400001051060000036442000001151060000015441400000191030000036440c00000591040000035440c00000d51050000056442000001591080000005440c00000591080000015441800000551050000036442000000d51080000035442000000d5108
  | 9, 12 => 0x30440c00001591080000035440c00000d51080000030440c00001191040000035442000000591080000056440800001191010000030440c00000151030000056440c00000d51050000056442000000551050000005440c00001591080000005440c00000d51080000015441400000551080000006440c00000c11030000056441400000151030000016441400000d51050000030440c00000d91050000016441400000d9103
  | 9, 13 => 0x5440c00000d51030000056440000001591050000005440c00000d91080000036442000000d51000000006440c00000d51050000016441000000551060000035442000000c51080000030440c00001591080000036440c00000191030000035442000000d91030000056440c00001591060000006440c0000159100000003144140000159106000004544180000159102000004644180000159103000003544000000115106
  | 9, 14 => 0x56441800000591080000035442000000551060000036442000000551080000031442000000191030000015442000001151060000015441400001591080000056440c00000d91050000015441400000591050000035440c00001591060000030440c00000551080000015442000000c51050000045441800000191030000046441800000d51030000056441800000d91030000056440c00000191030000045441800000d9105
  | 9, 15 => 0x36442000001591030000035440c00001151060000031442000000d91030000046441800000c51050000056441400000d91000000031442000001191060000056441800000591050000035441400000d91030000005440c00000591060000045441800000d91080000030440c00001591030000015442000000551060000035441400000c11030000035440c00001591030000015441400001591080000036441400000c5108
  | 9, 16 => 0x5440c00000d51030000035440000000191030000046441800000591010000006440c00000d51030000036440c00001051040000056440c00000551080000005440c00000c51050000056440000000d51030000036440000000d91050000015441800000d51000000016442000000551060000056440800000551020000005440c00000151030000035440c00000c1103000001544200000055108000004144040000059101
  | 9, 17 => 0x36442000000551060000056440c00001191060000006440c00000c51050000015441800000d51030000015441800001051010000031441400000151030000031442000001591060000035442000000551050000030440c00000c51050000016442000000d91030000016441400000551050000015441400001591080000046441800001591030000056440000000d51050000016441800000c5105000003544200000055108
  | 9, 18 => 0x36440c00001151060000056442000000191030000035441400000d51080000036441400001591020000031442000000551080000046441800001591000000016441400000c11030000036440c00001591030000015441800000d51000000031441400000591050000036440c00000c51080000035440c00000c11030000056442000000c51080000030440c00000d5103000001644140000015103000003544200000119106
  | 9, 19 => 0x31442000000c51080000046441800000591080000041441800000191030000036441400000c51080000036440c00001051060000005440c00000591080000006440c00001191060000031441400000d91000000041441800001591030000015441400001051060000016440800000551060000035440c00000c5108000005644180000115106000003144200000015103000001644140000159105000003144200000059108
  | 9, 20 => 0x36442000000591020000041441800000591050000056440c00000d91080000041441800000591060000015442000000c51080000016442000000151030000036442000001051060000056440c00000d91030000031442000000591080000016442000000c51080000030440c00000151030000056441400000d91080000016442000000d51050000036440c00000d9100000004544180000055102000001644080000159105
  | 9, 21 => 0x35440c00000c11030000056442000000151030000046441800000591080000006440c00001591050000036441400000d51080000036442000000c51080000015442000000c51050000015441800000c51050000030440c00000591060000036440000000c51050000016442000000591080000036440c00000151030000056441400001591060000016441800001591000000016442000000591060000030440c0000115106
  | 9, 22 => 0x16442000000591050000036441400000d51050000056440c00000591050000006440c00000151030000056441400000591050000035441400001591080000035442000001591050000015441800000191030000035441400000551050000016441800000591050000030440c00000551080000031441400000591060000030440c00001591030000036440c00000c11030000016441800000d51000000031441400000c5108
  | 9, 23 => 0x15441800000c51080000031442000000191030000035440c00001591030000056441800000591060000035440c00001591030000030440c00000d51080000030440c00000d91030000035440c00001191060000006440c00001051060000041441800000591060000016441400000551050000006440c00000591050000016442000000d51030000036440c00001051040000006440c0000059108000001644040000159105
  | 9, 24 => 0xd51050000036441400000551080000036440c00000d51080000016441800001591030000041441800001591060000035440c00000d91030000046441000000c51050000056440000000591040000056440c00000d51050000036442000000d91080000035440000000d5103
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_253 roots_253 9 s ws hint
  | 1 => checkCutEntry true dom_127 roots_127 9 s ws hint
  | 2 => checkCutEntry true dom_239 roots_239 9 s ws hint
  | 3 => checkCutEntry true dom_254 roots_254 10 s ws hint
  | 4 => checkCutEntry true dom_191 roots_191 9 s ws hint
  | 5 => checkCutEntry true dom_247 roots_247 10 s ws hint
  | 6 => checkCutEntry true dom_223 roots_223 10 s ws hint
  | 7 => checkCutEntry true dom_231 roots_231 6 s ws hint
  | 8 => checkCutEntry true dom_251 roots_251 10 s ws hint
  | 9 => checkCutEntry true dom_55 roots_55 5 s ws hint
  | 10 => checkCutEntry true dom_189 roots_189 7 s ws hint
  | 11 => checkCutEntry true dom_125 roots_125 7 s ws hint
  | 12 => checkCutEntry true dom_53 roots_53 4 s ws hint
  | 13 => checkCutEntry true dom_237 roots_237 6 s ws hint
  | 14 => checkCutEntry true dom_111 roots_111 6 s ws hint
  | 15 => checkCutEntry true dom_175 roots_175 6 s ws hint
  | 16 => checkCutEntry true dom_109 roots_109 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_255 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_253 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_127 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_239 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_254 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_191 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_247 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_223 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_231 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_251 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_189 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_125 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_237 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_111 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_175 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_109 _ hc
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
private theorem z7 : ∀ i, 0 ≤ i → i < 2 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 27 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 27 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 28 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 28 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 6 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 6 0 = true)
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

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [4, 5] }, { op := GateOp.and, inputs := [8, 9] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [11, 3] }, { op := GateOp.and, inputs := [6, 12] }, { op := GateOp.or, inputs := [1, 3] }, { op := GateOp.or, inputs := [14, 4] }, { op := GateOp.and, inputs := [7, 15] }, { op := GateOp.and, inputs := [2, 5] }, { op := GateOp.or, inputs := [10, 13] }, { op := GateOp.or, inputs := [18, 16] }, { op := GateOp.or, inputs := [19, 17] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 20⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  decide +kernel

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_14248_aux

theorem PEqualNP.Outside.L_meta_14248 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_14248_aux.main
