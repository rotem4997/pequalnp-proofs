import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14338_aux

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

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffccccffffcccceeee0000eeee0000ffffccccffffcccceeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_90 : Nat := 0x50505050000000005050505
def goal_90 : Nat := 0xffffffccffffffcccccc0000cccc0000ffffffccffffffcccccc0000cccc0000
def roots_90 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffffccffffffcceeee0000eeee0000ffffffccffffffcceeee0000eeee0000
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_113 : Nat := 0x30003000300030003000300030003
def goal_113 : Nat := 0xffffaaaaffff0000aaaaaaaaaaaa0000ffffaaaaffff0000aaaaaaaaaaaa0000
def roots_113 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_115 : Nat := 0xf000f000f000f000f000f000f000f
def goal_115 : Nat := 0xffffeeeeffffcccceeeeaaaaeeee0000ffffeeeeffffcccceeeeaaaaeeee0000
def roots_115 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_121 : Nat := 0x3030303030303030303030303030303
def goal_121 : Nat := 0xffffffaaffffff00aaaaaaaaaaaa0000ffffffaaffffff00aaaaaaaaaaaa0000
def roots_121 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffffeeffffffcceeeeaaaaeeee0000ffffffeeffffffcceeeeaaaaeeee0000
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_154 : Nat := 0x505050500000000000000000000000005050505
def goal_154 : Nat := 0xffccffccffccffccffccffccffccffcccccc0000cccc0000cccc0000cccc0000
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeeeee0000eeee0000eeee0000eeee0000
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaaaaaaaaa00000000aaaaaaaa00000000
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def goal_171 : Nat := 0xffffffffffeeffeeffffffffffeeffeeaaaaaaaa00000000aaaaaaaa00000000
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xffffffffff00ff00ffffffffff00ff00f0f0f0f000000000f0f0f0f000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_174 : Nat := 0x55550000555500000000000000000000555500005555
def goal_174 : Nat := 0xffffffffffccffccffffffffffccffccf0f0f0f000000000f0f0f0f000000000
def roots_174 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffccccccccffffffffcccccccccccc0000cccc0000cccc0000cccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def goal_185 : Nat := 0xffffffffffaaffaaffffffffffaaffaaaaaaaaaaaaaa0000aaaaaaaaaaaa0000
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def goal_186 : Nat := 0xffffffffffccffccffffffffffccffcccccc0000cccc0000cccc0000cccc0000
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffeeffeeffffffffffeeffeeeeeeaaaaeeee0000eeeeaaaaeeee0000
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_195 : Nat := 0xf000000000000000f000000000000000f000000000000000f
def goal_195 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeecccccccccccccccc0000000000000000
def roots_195 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_201 : Nat := 0x303000000000000030300000000000003030000000000000303
def goal_201 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaff00ff00ff00ff000000000000000000
def roots_201 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffccffccffccffcc0000000000000000
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaaaaaaffff0000ffff0000aaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_210 : Nat := 0x50005000000000005000500000000000500050000000000050005
def goal_210 : Nat := 0xffffccccffffccccccccccccccccccccffffccccffffcccccccc0000cccc0000
def roots_210 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeeeeeeeeeeeeeeeeeffffccccffffcccceeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_216 : Nat := 0x1010101000000000101010100000000010101010000000001010101
def goal_216 : Nat := 0xffffff00ffffff00ff00ff00ff00ff00ffffff00ffffff000000000000000000
def roots_216 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffaaffaaffaaffaaffffff00ffffff00aaaa0000aaaa0000
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffccffccffccffccffffffccffffffcccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffeeffeeffeeffeeffffffccffffffcceeee0000eeee0000
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_227 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def goal_227 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeeeccccccccaaaaaaaa00000000
def roots_227 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_233 : Nat := 0x30300000303000003030000030300000303000003030000030300000303
def goal_233 : Nat := 0xffffffffffaaffaaffffffffffaaffaaffaaffaaff00ff00aaaaaaaa00000000
def roots_233 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_234 : Nat := 0x50500000505000005050000050500000505000005050000050500000505
def goal_234 : Nat := 0xffffffffffccffccffffffffffccffccffccffccffccffcc0000000000000000
def roots_234 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_235 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def goal_235 : Nat := 0xffffffffffeeffeeffffffffffeeffeeffeeffeeffccffccaaaaaaaa00000000
def roots_235 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_241 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def goal_241 : Nat := 0xffffffffffffaaaaffffffffaaaaaaaaffffaaaaffff0000aaaaaaaaaaaa0000
def roots_241 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffccccccccffffccccffffcccccccc0000cccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffeeeeeeeeffffeeeeffffcccceeeeaaaaeeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_248 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def goal_248 : Nat := 0xffffffffffffff00ffffffffff00ff00ffffff00ffffff000000000000000000
def roots_248 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_249 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def goal_249 : Nat := 0xffffffffffffffaaffffffffffaaffaaffffffaaffffff00aaaaaaaaaaaa0000
def roots_249 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_250 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def goal_250 : Nat := 0xffffffffffffffccffffffffffccffccffffffccffffffcccccc0000cccc0000
def roots_250 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffeeffeeffffffeeffffffcceeeeaaaaeeee0000
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xffffffffffffffeeffffffffffeeffeefffffffeffffffccfefefafaeeee0000
def roots_255 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

namespace S_82
def pairsG : List (Nat × Nat) := [(2, 18), (2, 66), (16, 18), (16, 80), (64, 66), (64, 80)]
def r1sG : List Nat := [2, 2, 16, 16, 64, 64]
def r2sG : List Nat := [18, 66, 18, 80, 66, 80]
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_82.map (· &&& dom_82)
def goalM : Nat := goal_82 &&& dom_82
def NN : Nat → Nat
  | 2 => 1
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 2, 0 => 0xc29e8a40
  | 3, 0 => 0xc29e8a40
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x50000000000000005000000000000000000000000000000000000000000000004000400000000000400040000000000000000000000000000000000000000000500050000000000000000
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
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_82 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_82 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_82 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_82 == dom_82) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_82 goalM v ys) : RunD true dom_82 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_82 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_82 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_82 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_82 roots_82 goal_82 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_82 goal_82 := by
    have h0 : isConstB dom_82 goal_82 = false := by decide +kernel
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

end S_82

theorem lowS_82 : Lower true dom_82 roots_82 goal_82 4 := S_82.noCircuit

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

theorem lowS_83 : Lower true dom_83 roots_83 goal_83 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a00000000000a000a, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_82

def isoMvS_53 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_53 : Lower true dom_53 roots_53 goal_53 4 :=
  lower_iso isoMvS_53 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_90 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_90 : Lower true dom_90 roots_90 goal_90 5 :=
  lower_iso isoMvS_90 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_113 : List (Nat × Nat) := [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_113 : Lower true dom_113 roots_113 goal_113 4 :=
  lower_iso isoMvS_113 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_153 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_153 : Lower true dom_153 roots_153 goal_153 4 :=
  lower_iso isoMvS_153 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_154 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_154 : Lower true dom_154 roots_154 goal_154 4 :=
  lower_iso isoMvS_154 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_169 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_169 : Lower true dom_169 roots_169 goal_169 5 :=
  lower_iso isoMvS_169 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_172 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_172 : Lower true dom_172 roots_172 goal_172 4 :=
  lower_iso isoMvS_172 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_177 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_177 : Lower true dom_177 roots_177 goal_177 5 :=
  lower_iso isoMvS_177 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_178 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_178 : Lower true dom_178 roots_178 goal_178 4 :=
  lower_iso isoMvS_178 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_195 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_195 : Lower true dom_195 roots_195 goal_195 4 :=
  lower_iso isoMvS_195 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_201 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_201 : Lower true dom_201 roots_201 goal_201 4 :=
  lower_iso isoMvS_201 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_209 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_209 : Lower true dom_209 roots_209 goal_209 4 :=
  lower_iso isoMvS_209 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

def isoMvS_210 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_210 : Lower true dom_210 roots_210 goal_210 5 :=
  lower_iso isoMvS_210 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_216 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_216 : Lower true dom_216 roots_216 goal_216 4 :=
  lower_iso isoMvS_216 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51

theorem lowS_55 : Lower true dom_55 roots_55 goal_55 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc, 16, 18)] (by decide +kernel) (by decide +kernel) lowS_53

theorem lowS_91 : Lower true dom_91 roots_91 goal_91 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a000000000a0a0a0a, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_90

namespace S_115
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (2, 18), (2, 66), (3, 19), (3, 35), (3, 67), (16, 17), (16, 18), (16, 80), (32, 33), (34, 35), (34, 50), (34, 98), (48, 49), (48, 50), (48, 112), (64, 66), (64, 80), (65, 67), (65, 81), (65, 97), (96, 97), (96, 98), (96, 112)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 16, 16, 16, 32, 34, 34, 34, 48, 48, 48, 64, 64, 65, 65, 65, 96, 96, 96]
def r2sG : List Nat := [17, 33, 18, 66, 19, 35, 67, 17, 18, 80, 33, 35, 50, 98, 49, 50, 112, 66, 80, 67, 81, 97, 97, 98, 112]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_115.map (· &&& dom_115)
def goalM : Nat := goal_115 &&& dom_115
def NN : Nat → Nat
  | 4 => 3
  | 5 => 4
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xd9a4f89fd770f556cf74566d
  | 5, 0 => 0x55e531f641f609c8374d38350ab470f3
  | 6, 0 => 0x3e6b0387
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5000500050000000500050005000000000000000000000000000000000000000f000f00000000000f000f000f000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f00000000000f000f00000000000000000000000000000000000000000000000000000000000f000c000f000c00000000000000000000000000000000000f0000000f0000000f0000000f000000000000000000000000000000000000000c000c000c000c000c000c000c000c00000000000000000000000000000000000a000a000a000a000a000a000a000a
  | 0, 1 => 0xf0000000f000000000000000000000000000000000000000f000f000f000f000c000c000c000c00000000000000000000000000000000000f000c000f000c000f000c000f000c00000000000000000000000000000000000f000f000f0000000f000f000f0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x821755621055432105
  | 5, 0, 0 => 0x82105542b105642a10564921056
  | 6, 0, 0 => 0x421055
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe0ffc0707fe03fc0001c1fc0000fdfe0070e000070f8380073
  | 0, 1 => 0xe1c07f8e1f003f7f9c1ff80
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xc2d982787f6dffe4491e1fc22006cdac574e551572f8784cf3
  | 0, 1 => 0x68caffeedf33ff7fbf5ffb7
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
  | 3, 0 => 0xda66c15848c6d7f2
  | 4, 0 => 0xe6bd00edda66c158bef4e2cdb0f287fa9e915c288f79697d5dcdb84459aa018c483405f840cc1e7c3e6b038717160a1413f3d36d10e7a415
  | 5, 0 => 0xf8e1371be339ab53dff051b4c7828123c2b7c988c126c7adb55bb9f99348d653801f665a7e1048567d1469807b74727d77f8159c776933756f5b383369a72e864bcd8d254592814144f3e1c03e6b03873de8bd833d4ca4723b9941463928edba2fe7c3d2299750e91941ecbb17160a14
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 3, 0 => 0x0
  | 4, 0 => 0x200000300020001000101010002
  | 5, 0 => 0x3010000010101000100020101010200000200010100010101000101
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
  | 0 => checkCutEntry true dom_82 roots_82 4 s ws hint
  | 1 => checkCutEntry true dom_83 roots_83 5 s ws hint
  | 2 => checkCutEntry true dom_51 roots_51 4 s ws hint
  | 3 => checkCutEntry true dom_113 roots_113 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_115 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_82 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_113 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_115 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_115 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_115 == dom_115) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_115 goalM v ys) : RunD true dom_115 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_115 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_115 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_115 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_115 roots_115 goal_115 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_115 goal_115 := by
    have h0 : isConstB dom_115 goal_115 = false := by decide +kernel
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

end S_115

theorem lowS_115 : Lower true dom_115 roots_115 goal_115 7 := S_115.noCircuit

theorem lowS_155 : Lower true dom_155 roots_155 goal_155 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa0a0a0a0000000000000000000000000a0a0a0a, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_154

theorem lowS_171 : Lower true dom_171 roots_171 goal_171 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c000000000000000000000c0c00000c0c, 128, 130)] (by decide +kernel) (by decide +kernel) lowS_169

theorem lowS_174 : Lower true dom_174 roots_174 goal_174 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x44440000444400000000000000000000444400004444, 128, 130)] (by decide +kernel) (by decide +kernel) lowS_172

theorem lowS_179 : Lower true dom_179 roots_179 goal_179 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc000c000c000c0000000000000000000c000c000c000c, 16, 18)] (by decide +kernel) (by decide +kernel) lowS_177

namespace S_217
def pairsG : List (Nat × Nat) := [(1, 17), (1, 129), (8, 72), (8, 136), (9, 25), (9, 73), (9, 137), (16, 17), (16, 80), (24, 25), (24, 88), (24, 152), (64, 72), (64, 80), (65, 73), (65, 81), (65, 193), (128, 129), (128, 136), (144, 145), (144, 152), (144, 208), (192, 193), (192, 200), (192, 208)]
def r1sG : List Nat := [1, 1, 8, 8, 9, 9, 9, 16, 16, 24, 24, 24, 64, 64, 65, 65, 65, 128, 128, 144, 144, 144, 192, 192, 192]
def r2sG : List Nat := [17, 129, 72, 136, 25, 73, 137, 17, 80, 25, 88, 152, 72, 80, 73, 81, 193, 129, 136, 145, 152, 208, 193, 200, 208]
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
  | 4, 0 => 0x344189f1
  | 5, 0 => 0xfcbd6b6a4c086f17493d8b40
  | 6, 0 => 0xfcbd6b6a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x30303030000000003000300000000000303030300000000030003000000000003030300000000000303030000000000030303000000000003030300000000000303000000000000030300000000000003030000000000000303000000000000030003000000000003000300000000000300030000000000030003000000000002020202000000000202020200000000020202020000000002020202000000000000030300000000000002020000000000000303000000000000020200000000030303030000000000000000000000000303030300000000000000000000000003030303000000000303030300000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x46885
  | 5, 0, 0 => 0x58c85be321b58c86
  | 6, 0, 0 => 0x58c85
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 19
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe0ff3e0e03ff0701f00000e7c00e039f07c1cf83e001fe0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfaffbe6f3fff6715f22945e7c25e179b0d419bc3ea49ff084a
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
  | 4, 0 => 0xfcbd6b6a75c2413838780d291b42ffd2
  | 5, 0 => 0x5580acc72cbc3e942634b2e109d39f0305ef8bcb01c8962f
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x1010000
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

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xffffffffffffffff0000000000000000, 64), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
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

def isoMvS_121 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_121 : Lower true dom_121 roots_121 goal_121 5 :=
  lower_iso isoMvS_121 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_185 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)]
theorem lowS_185 : Lower true dom_185 roots_185 goal_185 6 :=
  lower_iso isoMvS_185 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_186 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]
theorem lowS_186 : Lower true dom_186 roots_186 goal_186 5 :=
  lower_iso isoMvS_186 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_174

def isoMvS_203 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_203 : Lower true dom_203 roots_203 goal_203 5 :=
  lower_iso isoMvS_203 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155

def isoMvS_211 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_211 : Lower true dom_211 roots_211 goal_211 6 :=
  lower_iso isoMvS_211 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_179

def isoMvS_218 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_218 : Lower true dom_218 roots_218 goal_218 6 :=
  lower_iso isoMvS_218 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_179

def isoMvS_227 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_227 : Lower true dom_227 roots_227 goal_227 7 :=
  lower_iso isoMvS_227 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_233 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_233 : Lower true dom_233 roots_233 goal_233 7 :=
  lower_iso isoMvS_233 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_234 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_234 : Lower true dom_234 roots_234 goal_234 5 :=
  lower_iso isoMvS_234 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155

def isoMvS_241 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_241 : Lower true dom_241 roots_241 goal_241 7 :=
  lower_iso isoMvS_241 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_242 : List (Nat × Nat) := [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_242 : Lower true dom_242 roots_242 goal_242 7 :=
  lower_iso isoMvS_242 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115

def isoMvS_248 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_248 : Lower true dom_248 roots_248 goal_248 5 :=
  lower_iso isoMvS_248 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

theorem lowS_123 : Lower true dom_123 roots_123 goal_123 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000f000f000f000f000f000f00, 64, 72)] (by decide +kernel) (by decide +kernel) lowS_115

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
  | 4, 0 => 0x3020301000104
  | 5, 0 => 0x305080708030306000205010303060308010006080102010107010308070003
  | 6, 0 => 0x30103060306030506030308050503030600060308070506060703050603060605030605080606050606050306060807060303030506050306050603060506060301
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
  | 4, 0 => 0x25441205
  | 5, 0 => 0x4110700041105000521060008110500041103000911030009110600041105000411050009210500041106000c510600091106000c5106000c510800091106000c9105000c910500091106000911060004110300091103000c510600092105000411030004110300091103000411060005210600052106000c910500091103
  | 5, 1 => 0xc5108000911060004110600041105
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_154 roots_154 4 s ws hint
  | 1 => checkCutEntry true dom_51 roots_51 4 s ws hint
  | 2 => checkCutEntry true dom_178 roots_178 4 s ws hint
  | 3 => checkCutEntry true dom_179 roots_179 6 s ws hint
  | 4 => checkCutEntry true dom_177 roots_177 5 s ws hint
  | 5 => checkCutEntry true dom_171 roots_171 6 s ws hint
  | 6 => checkCutEntry true dom_185 roots_185 6 s ws hint
  | 7 => checkCutEntry true dom_155 roots_155 5 s ws hint
  | 8 => checkCutEntry true dom_186 roots_186 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_187 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_154 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_178 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_179 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_177 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_171 _ hc
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

namespace S_219
def pairsG : List (Nat × Nat) := [(1, 17), (1, 129), (2, 18), (2, 66), (2, 130), (3, 19), (3, 67), (3, 131), (8, 72), (8, 136), (9, 25), (9, 73), (9, 137), (10, 26), (10, 74), (10, 138), (11, 27), (11, 75), (11, 139), (16, 17), (16, 18), (16, 80), (24, 25), (24, 26), (24, 88), (24, 152), (64, 66), (64, 72), (64, 80), (65, 67), (65, 73), (65, 81), (65, 193), (128, 129), (128, 130), (128, 136), (144, 145), (144, 146), (144, 152), (144, 208), (192, 193), (192, 194), (192, 200), (192, 208)]
def r1sG : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 8, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 16, 16, 16, 24, 24, 24, 24, 64, 64, 64, 65, 65, 65, 65, 128, 128, 128, 144, 144, 144, 144, 192, 192, 192, 192]
def r2sG : List Nat := [17, 129, 18, 66, 130, 19, 67, 131, 72, 136, 25, 73, 137, 26, 74, 138, 27, 75, 139, 17, 18, 80, 25, 26, 88, 152, 66, 72, 80, 67, 73, 81, 193, 129, 130, 136, 145, 146, 152, 208, 193, 194, 200, 208]
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_219.map (· &&& dom_219)
def goalM : Nat := goal_219 &&& dom_219
def NN : Nat → Nat
  | 4 => 5
  | 5 => 13
  | 6 => 29
  | 7 => 9
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x8ee524928649542982a1db977185bad72abd7a6d
  | 5, 0 => 0xd9a7e5a2abfbddff954bf37291b3c3af7af0b5d57a5da0dc71c1d0736673bd465cfe37212fc3d7cb29d4e8442560785707066176
  | 6, 0 => 0xef8f4cd5eefcd423da3f8392d3d8b4b2d3934f7ecb3ce449c84b4819c7a4e568bce8e778b6794af7aaca69fe9cc0bf3698b479fa8f0d6aaa8cdb01e480c46fbc7bdc251170265e816c2837694fa57b08422a2b9d2d5fd5772a847d012a6e662a29dd89771f46450b1d2f1f9f0a9f9fd305a66495
  | 7, 0 => 0xeb845937db07c91fda3f8392c417d903a51db4c856c2ff5440b1ea310fb65345029a6877
  | 8, 0 => 0x8e86f0dd
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f0f0c0c000000000c0c0c0c000000000f0f0c0c000000000c0c0c0c000000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000000000000f0f0f00000000000f000f00000000000f0f0f00000000000f000f00000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0000000000000000
  | 0, 1 => 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0a0a000000000a0a0a0a000000000f0f0a0a000000000a0a0a0a000000000f0f0f0f000000000f0f0000000000000f0f0f0f000000000f0f00000000000000000f0f000000000f0f00000000000000000f0f000000000f0f0000000000000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f000000000000000000000000000000000000000000000f0f0f0f000000000f0f00000000000000000f0f000000000f0f0f0f0000000000000f0f000000000f0f0000
  | 0, 2 => 0xf0f0f0f0000000000000000000000000f0f0f0f000000000f0f0000000000000a0a0a0a000000000a0a0a0a000000000f0f0f0f000000000a0a0a0a000000000505050500000000050505050000000005050505000000000505000000000000030303030000000003030303000000000303030300000000030300000000000005050505000000000505050500000000000000000000000005050000000000000f0f00000000000000000000000000000f0f000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000f0f00000000000000000f0f00000000000000000000000000000f0f0000000000000000
  | 0, 3 => 0xf0f000f000000000f0f0000000000000f0f000f000000000f0f0000000000000f0f0f0f000000000f0f0f0f000000000f0f0000000000000000000000000000000f000000000000000f000000000000000f000000000000000f000000000000000f000f00000000000f000f00000000000f000f00000000000000000000000000000f0f0000000000000f0f0000000000000f0f0000000000000000000000000f0f0505000000000f0f0000000000000f0f0505000000000f0f000000000000000000000000000000000000000000000f0f0000000000000f0f00000000000005050505000000000505000000000000050505050000000005050000
  | 0, 4 => 0xf0f00000000000000000000000000000f0f0000000000000f0f0f0f000000000f0f0f0f0000000000000000000000000f0f0000000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0f0f000000000f0f0f0f000000000505050500000000000000000000000000000f0f0000000000000f000000000000000f0f0000000000000f00000000000a0a0a0a000000000f0f0a0a000000000a0a0a0a000000000f0f0a0a000000000f0f0f0f000000000f0f0a0a000000000f0f0f0f000000000f0f0a0a000000000f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0a
  | 0, 5 => 0xf0f0f0f00000000000000000000000005050000000000000505000000000000050500000000000005050000000000000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f000000000005050505000000000000000000000000050505050000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xa18504752461411d48182047510614101440c20405
  | 5, 0, 0 => 0xc18204753c60952c7600d18504753c60542c763c60932c76286081487624608148763c30810076106081012644608140763c608e007634c18204761061412c76
  | 6, 0, 0 => 0x3c20402dc1de23c60812c7700d1820521da13c60812c7734f1828011dc03c608e2c767cf18204b1dcf18204b787734608174b1dc03c204b70763c60812db1dda3c60812c776460812d01dcf1820582c775cf18204b1dc03c60962c76
  | 6, 0, 1 => 0x3c61412c7600f18204b798d3c60812c7728f18204b1dc418204b407724f18204b1dc09c608140763e618204b1de53c60a02c7710f1820402dc03c60812e463c60818cb1dcf1820404877
  | 7, 0, 0 => 0xf18204bb0773c60812d21dcd3c60812c773c6081acb1dc43c60812c77a8f18204b1dcf9c60812c773e918204b1dcf18204ba077
  | 8, 0, 0 => 0x3c60812c76
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
  | 0, 0 => 0xffe0000000000003c7ff000000007e0fcffe03f8000000003c7ff000000007e0fc001e0071ce3ffffc000000
  | 0, 1 => 0xf003f80000001e0071ce3ff1fff80000ff1fff80000f01fc000000ffffff80000001fff80000ffffff80000
  | 0, 2 => 0xf01fff80000001fc071ce3ffe1ff80000ffffff80000ffe03f80000000000000000fe03f80000f01fc000000
  | 0, 3 => 0xff1fff80000ffe000000000f000380000ffffc000000f0ffc000000ff01ff8000000003f80000ff01ff80000
  | 0, 4 => 0xf003f80000ffe03f800000f1e3ff1ce3ffe1c000000f01fc07ff000f1e3ff1ce3ff1ffff1ce3f01fc071ce3
  | 0, 5 => 0x1fc0000000f003f800000f003ffff00f01ffc7ff00f001c000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfff020492924484bc7ff00aa4b5b7e0fcfff93fdb6b7cc8dbe7ff002242497e0fc113e04f1ce3fffff26dbda
  | 0, 1 => 0x8f093f92425993f16f1ce3ff1fffb6d6d7716edb6d6df81fd224948fffffffffff000fdfb6d6d77f6edfffff
  | 0, 2 => 0xf81fdfb6d6d113fd6f5debeec1fb0e31cddbdb681f03eec0290a2148809120000007e02ddb6b77016c024948
  | 0, 3 => 0xbf1b7f9246dfff932492928b090380025bb7b42000da70f6c06dbdaef09ff9652d00091f92425ee01fb0610c
  | 0, 4 => 0x7002d92425fff02ddb6b79f3f3ff3ce7fff1f24d39a7096c06db48173e2df3ce7ff3ffff7deff93fd6f5deb
  | 0, 5 => 0xfd2249488e013b02004cf8dbffff25fc9ffe7ff48e801d204108
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 44 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 44 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 45 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 45 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 45 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 45 then wireAt i else 0
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
  | 4, 0 => 0xcf9506a9345be8f3
  | 5, 0 => 0xeefcd423e1cccbb4e13a5302a68128cda37c411a8e86f0dd8b1d9c1580c46fbc7c1f51b076485a0773eb774e722a46d17114b0696c2837695ee837f75e65b6485bd25675573036f152b957034ce6e3203c83e2653c283040333218ab311e39cf3089cc2829d8600c2755eb802628bde425e598e423a514f21f2e35f9129a96c411048d500bf1169909a9281b073d2fa2
  | 6, 0 => 0x3c1025173b7dac653b4dfc063892a4a3384ff44236f5fc2e35fe746d35c4f9e435ae0352334b54ec329e11bc3221298d30fc00e5305a29882ed7d1a22e2874772c27bbd82bbeb81e28e0978427a0ac8a2741e33125f727742315b748214fcec420fa28bb2033eca21fee59a61f2e35f91c5dcdbc1bf312d01a63a4ea1a62b06819f6110d19f5e56b19db171617e9723917c03eea17667e1b16ff643416a3d86e15c3e0d710f1822710eed7400fb653450f18531f0e7a2af50bce65dc0ae10f9109ce495e09c8c1320903cf4c08e1433208c4c89008b51e480779031b06a34ab905cf139004c5e011029a68770297690300d3d1cf0084c352006e1407006a128c
  | 6, 1 => 0x9ab81cb59aacbb0095ee23cf95c84f86926493ce925ade188e86f0dd89aaa9c5895375a9881a914388192f5583e214fe8314895a8281cc7c816b342680d30b798028f2477fecc7f27ed7318a7ad93d497ad10fcf7ab4776479673aad76710b99751c81b3707348ce6f2784e76e89fc9e6e3a13f56c8823da6b9717916ace5aaf6a52bdc26908005a67c20e6466efe6db62a3ccef61c0d6515f7e857f5f4a005c5e3f188f5e37f20b5b889e4a56c2ff5453e638a5528af78050e93c08507e56b04e27f8a34d29c44e4b3fcb734a5c61f449b7e82d46c1485c4640dd424495d0c243f0fc3a43c10617432a325d42802b9d40b1ea313e31d34d3d37c7133c2e4cbc
  | 6, 2 => 0xeb845937e64f011cdb07c91fd9dc66abd29fe0a9d2825086d23416ced2048904d0cbb737cd0c3a1acc6da034cb5809ccc993ce60c68c0f9ec660ca4ac5d77ed1c417d903c37680f4c297a54cc13fe1b8c12db0abc0471952bec5af07bce86210b9533834b8a90fabb7915d9eb76fd0d8b5385bd6b43a16c6b06875edb001b027af735f12abdbfd63a81b3d63a51db4c8a425064ba1b5ef0ea1b0693d9fe50b8e9faf9c219f9c02469e5064ec9b9dd4f7
  | 7, 0 => 0xee81ece6c0de76dab76fd0d8b3d390949ebedcb88e86f0dd87ab034c7a7ea2c8759f3d395cde10445197d96b4424203f3f2dfc923e96773d395e26af3892a4a330832f4d1dd4337a1bf312d01b6794cc0d16529e0bbb1efe09c8c1320860f9a9062a61ef04c5e0110273a5df0084c352
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x101
  | 5, 0 => 0x20202000400040205020302020205020201020504050405060107020503070502020705
  | 6, 0 => 0x8070306060500040507090807030607050704040407020204000507080200040405040a0502090705070203000609030007000703070905020007070202000702020704030703060a0004060706040005030705020008000205050707030403070702030000050405080303040708020b070008090500040707070604070600
  | 6, 1 => 0x4040209070303040700020204030708070400040406030407020304070209040400050403090407070a0403
  | 7, 0 => 0x3000407070000000900000006000004000003000000070704070007
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 9 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 2
  | 5 => 26
  | 6 => 65
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x89b76c024d949aa4
  | 5, 0 => 0xc8d00414b76a8ca8a7236f689f0c5a837f20d2b9785ace796d22b8c868b094c26462cc6862e989255ad9f05e51852b1a3d7d4a523c37fd1b38c8347f30d3f61c2c8dc36428ed8f3524f46de21eb71f001e736a51146f70b40ed82c9f0cca571806df895c05b76945
  | 6, 0 => 0xc2ba8accbea625cbbe85c407b49e9f33ad66ef22abc8847da7760fbba0e030b59b93df9797c0a3b593921ba290d6786c8b174f7f8a4f09f288bc37f3866d24a085c496728447e34b7b3e30e37949e22a76871d797644ea8374275f6371bdb1de69f95b3e66fc938864bd5f5763a0fcf3627c6c1c5f710e39571545f9557fa341552d3b28525c274e4ef47e214e2c38944bd612894825ca3a47fa43ee478d7c4340f39aa33f36bd9c3a29dbe43a22192539df039d38048e05354b481b3438de993008efdf2b4744a82afd058d2362fc6a220668ef20477cb51ebaaba319bc8fd8190a69ca166547480e1b11690e12b6420d51e74706d285b4052caac000f6cb74
  | 6, 1 => 0xc9a66b97
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x5648e328c01593288e300
  | 5, 0 => 0x55320800001549320000055320800005448c2000008c23480000238ca20000143244800005444a2000008c23480000544c820000151038800002308d2000008c234800003288e20000015230800002308d20000151128800001549320000015230800005440e2000001534c8000050c912000000030c4100051cd1200001432448000015493200
  | 6, 0 => 0x244400000008d1000000032040000000c910000000238400000001110400000244400000000910000000038410000000d10000000234400000004e10000000024400000000a10000000244400000008e1000000023840000000091000000002440000000491000000023840000000911000000034440000000d11070000024440000000d110000000034400000004d1000000032840000000491000000034441c000000e100
  | 6, 1 => 0x128400000008c1000000012840000000ca10000000128400000008c1000000002840000000931000000034c400000008c10000000238400000004a10000000230400000008d1000000023840000000931000000024c40000000911000000034c400000000910000000038400000004e1000000002840000000911000000023440000000d11000000024c40000000d31000000012440000000d310000000138400000008d100
  | 6, 2 => 0xd100
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 8 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_217 roots_217 7 s ws hint
  | 1 => checkCutEntry true dom_201 roots_201 4 s ws hint
  | 2 => checkCutEntry true dom_203 roots_203 5 s ws hint
  | 3 => checkCutEntry true dom_211 roots_211 6 s ws hint
  | 4 => checkCutEntry true dom_91 roots_91 6 s ws hint
  | 5 => checkCutEntry true dom_155 roots_155 5 s ws hint
  | 6 => checkCutEntry true dom_90 roots_90 5 s ws hint
  | 7 => checkCutEntry true dom_218 roots_218 6 s ws hint
  | 8 => checkCutEntry true dom_83 roots_83 5 s ws hint
  | 9 => checkCutEntry true dom_210 roots_210 5 s ws hint
  | 10 => checkCutEntry true dom_154 roots_154 4 s ws hint
  | 11 => checkCutEntry true dom_195 roots_195 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_219 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_217 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_201 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_211 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_90 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_218 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_210 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_154 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_195 _ hc
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

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
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

theorem lowS_235 : Lower true dom_235 roots_235 goal_235 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c, 64, 66)] (by decide +kernel) (by decide +kernel) lowS_233

namespace S_243
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 129), (2, 18), (2, 66), (2, 130), (3, 19), (3, 35), (3, 67), (3, 131), (16, 17), (16, 18), (16, 80), (32, 33), (32, 160), (34, 35), (34, 50), (34, 98), (34, 162), (48, 49), (48, 50), (48, 112), (48, 176), (64, 66), (64, 80), (65, 67), (65, 81), (65, 97), (65, 193), (96, 97), (96, 98), (96, 112), (96, 224), (128, 129), (128, 130), (128, 160), (144, 145), (144, 146), (144, 176), (144, 208), (192, 193), (192, 194), (192, 208), (192, 224)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 16, 16, 16, 32, 32, 34, 34, 34, 34, 48, 48, 48, 48, 64, 64, 65, 65, 65, 65, 96, 96, 96, 96, 128, 128, 128, 144, 144, 144, 144, 192, 192, 192, 192]
def r2sG : List Nat := [17, 33, 129, 18, 66, 130, 19, 35, 67, 131, 17, 18, 80, 33, 160, 35, 50, 98, 162, 49, 50, 112, 176, 66, 80, 67, 81, 97, 193, 97, 98, 112, 224, 129, 130, 160, 145, 146, 176, 208, 193, 194, 208, 224]
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_243.map (· &&& dom_243)
def goalM : Nat := goal_243 &&& dom_243
def NN : Nat → Nat
  | 7 => 1
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 7, 0 => 0x84a90dbb
  | 8, 0 => 0x11aa738
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f000f000f000f000f00000000000f000f000f000f000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000f000f000f000f0000000000000000000f000f000f000f0000000000000000000f000f000f000f000f000f000f000f00000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 7, 0, 0 => 0x1ac6887
  | 8, 0, 0 => 0x2c6886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 7 => 25
  | 8 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf01ffffe000001e07fe0000f000781c00000000783f80001e0003c7f01ff800000ffe00000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc9fffff192849e87fe0824f085791c4922442978bf81123e08a7c7f81ffa21110fff10444224
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 44 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 44 (i % 8)
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
  | 5 => 1
  | 6 => 7
  | 7 => 20
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0x11aa738
  | 6, 0 => 0xe0e31d33a788481e4334ee7d3c1b864638c91a7e10e41b47011aa738
  | 7, 0 => 0xef0ed875ac8fc1b36b778ad267b9ed684d6051843d2be80238c91a7e366e74b2346a4a502915b47b246381f7232d8ade149f7086147d712e0e547add0d29d7bd070157f60558c3510495b03d011aa738
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x0
  | 6, 0 => 0x1010102010400
  | 7, 0 => 0x103020000030502000000040000000300000200
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 6 0 (CN0 s)
def CN : Nat → Nat
  | 6 => 4
  | _ => 0
def CH : Nat → Nat → Nat
  | 6, 0 => 0x5cfdafcc24fb82d9088e845d01535bdf
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 6, 0 => 0x32440cd1104234400c9102
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_242 roots_242 7 s ws hint
  | 1 => checkCutEntry true dom_211 roots_211 6 s ws hint
  | 2 => checkCutEntry true dom_227 roots_227 7 s ws hint
  | 3 => checkCutEntry true dom_241 roots_241 7 s ws hint
  | 4 => checkCutEntry true dom_115 roots_115 7 s ws hint
  | 5 => checkCutEntry true dom_179 roots_179 6 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_243 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_242 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_211 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_227 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_241 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_115 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_179 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_243 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_243 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_243 == dom_243) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_243 goalM v ys) : RunD true dom_243 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_243 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_243 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_243 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_243 roots_243 goal_243 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_243 goal_243 := by
    have h0 : isConstB dom_243 goal_243 = false := by decide +kernel
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

end S_243

theorem lowS_243 : Lower true dom_243 roots_243 goal_243 9 := S_243.noCircuit

namespace S_249
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 129), (8, 72), (8, 136), (9, 25), (9, 41), (9, 73), (9, 137), (16, 17), (16, 80), (24, 25), (24, 88), (24, 152), (32, 33), (32, 160), (40, 41), (40, 104), (40, 168), (48, 49), (48, 112), (48, 176), (56, 57), (56, 120), (56, 184), (64, 72), (64, 80), (65, 73), (65, 81), (65, 97), (65, 193), (96, 97), (96, 104), (96, 112), (96, 224), (128, 129), (128, 136), (128, 160), (144, 145), (144, 152), (144, 176), (144, 208), (192, 193), (192, 200), (192, 208), (192, 224)]
def r1sG : List Nat := [1, 1, 1, 8, 8, 9, 9, 9, 9, 16, 16, 24, 24, 24, 32, 32, 40, 40, 40, 48, 48, 48, 56, 56, 56, 64, 64, 65, 65, 65, 65, 96, 96, 96, 96, 128, 128, 128, 144, 144, 144, 144, 192, 192, 192, 192]
def r2sG : List Nat := [17, 33, 129, 72, 136, 25, 41, 73, 137, 17, 80, 25, 88, 152, 33, 160, 41, 104, 168, 49, 112, 176, 57, 120, 184, 72, 80, 73, 81, 97, 193, 97, 104, 112, 224, 129, 136, 160, 145, 152, 176, 208, 193, 200, 208, 224]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_249.map (· &&& dom_249)
def goalM : Nat := goal_249 &&& dom_249
def NN : Nat → Nat
  | 4 => 3
  | 5 => 8
  | 6 => 18
  | 7 => 5
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xfd91b515e04909a41858b50e
  | 5, 0 => 0xc243057dbeab8716b2aa85b1acdeadf09aa8f4879791c42b8be4f2a9642708fa
  | 6, 0 => 0xf0ec86b1d53f13e5b5f30152a1ac1a338be4f2a9884d7442876cb4667843302277a5184a718ffe58525eeda74cfec4aa404246fa286e62d627f9466024d3718524cecfa11e6fb060
  | 7, 0 => 0xceae85e0c7d390824cfec4aa38c25eed293d391f
  | 8, 0 => 0x50964311
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3030303030303030303030303030303000000000000000000000000000000000000000003030303000000000303030300000000020202020000000002020202010101010101010101010101010101010202020202020202020202020202020203030000030300000303000003030000030300000303000003030000030300000300030003000300030003000300030003000300030003000300030003000300030303030303030303030303030303030202020202020202020202020202020200000000010101010000000001010101000000000202020200000000020202020303030303030303000000000000000003030303030303030000000000000000
  | 0, 1 => 0x1010101010101010101010101010101010101010101010100000000000000000000000003030303000000000303030300000000030303030000000002020202020202020202020202020202020202020000000000000000000000000000000003030303020202020303030302020202030303030000000003030303000000000003000300030003000300030003000300030003000300030002000200020002030303030000000003030303000000000303030300000000030303030000000002020202020202020202020202020202020202020202020202020202020202020003000300030003000100010001000100030003000300030000000000000000
  | 0, 2 => 0x20202020202020202020202020202020101010101010101010101010101010100000000000000000000000000000000030303030303030303030303030303030000000000000000020202020202020203030303030303030202020202020202030303030303030302020202020202020000030300000303000002020000020200000303000003030000020200000202000000000000000003030303030303030000000000000000020202020202020203030000030300000303030303030303030300000303000003030000030300000303030303030303020202020202020203030303030303030000000000000000
  | 0, 3 => 0x303030303030303000000000000000000000000000000000303030303030303030303030303030303030303030303030000000000000000030203020302030203020302030203020300030003000300030003000300030003030303030303030303030303030303030303030303030302020202020202020303030303030303000000000000000003030303030303030202020202020202
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x10653014832840a4188205
  | 5, 0, 0 => 0x2883281544188a0620d2e01d8831180d6030831015444ac07620d2601d944481076
  | 6, 0, 0 => 0x51069800ee05134901d8041a4c03b106249807751079480eea20f0901dc0a20ee0b301441880d651069a80eea20c4901dc0a1a6603b28744cc07751069900ee05446901d80a20d303b2883481e77
  | 6, 0, 1 => 0xc20d203b2883a27677
  | 7, 0, 0 => 0x2883480fc75106901daea20c4901dd441d1203ba8834dc077
  | 8, 0, 0 => 0x1441a4076
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
  | 0, 0 => 0xffe000000003ff8780001e7ffe1e000079c3c001f83e000000071ce7e3ff8780001e7ffe1e000079fc07fe000000
  | 0, 1 => 0xfffe18000003ff87e0001e700000000000000781ffc000fffff800001c00781ffc0000001e000079fffffe000000
  | 0, 2 => 0x1e000079fff800000000ffe00000079fc07fe0001e7f01ff800079c3f8000001e70fe007e0f803c07fe000000
  | 0, 3 => 0x3f800000000fffff800000000001c739f8fffff800079fc07fe0001e7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfff104928451ed858002bb5eed2e5b7abcd3c215f83e2122442f1ce7e3ffcf96debf76a406000aac7e07fe921488
  | 0, 1 => 0xeedc1edad061ed85e003fbd11210000041256fe1ffc146ddbbd0e3181e127a1ffc0421123e1252f9f726f4308400
  | 0, 2 => 0x2e1252b8fbb40124a010fff105b7addfe4ffedb5fefb037a80d07381f8016deb774fe857f2fcd7e4ffe92158c
  | 0, 3 => 0x1f80124a114fffffedad670cd94bc739fcffffffffffffe07fedb5eeb
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
  | 5, 0 => 0xc2a5d57ab06a80359e4826d597bbd268928517d17ab9bab973fa46dd718ffe586356f86b50964311487b65ea45c88ae83e47b21c398052ee2df2d6e424cecfa124b9da5f11e641f80824ce99
  | 6, 0 => 0xceae85e0cd5d5e7cc7d39082c7338222bc52e0c0b813f655b072c1e19c0c1d1298a6236b928517d191bd8e4791adfb7e871836f7812343607a386ebb77bb96e174b7f62b723bf6ba6ea2dc396a2a0daf6829d42267d8f16365e1d48c619398ee6119eeee5e81902d59bfff7254a33d6e547c83b754023c19509643114ae150ae49fd3a6d49382806492a8b4846042ebe44f0a4cd44337aae3a396c29391b119338c25eed367aecb93484156a2db8a5242d70667e2d2c6b15293d391f2892dcd7232e53a221f3dca418e967a418aa1f3e1766d5ef1681be551568fc591511017e14ae34220f0e05540f037adf0e0a34070b4108300b18a62d0824ce99016af3b4
  | 6, 1 => 0xeae43123daf24377da2ab9edd0fd4ce3
  | 7, 0 => 0xff416496f2928181bd36c8eaaaf98a9c872c578b857de7ed7af30bff76ede31b6cb095d663f90d075cf70ec85c130b89547c83b7509643114accdc204a55f75b4a49ca9b4503752f4158021b34bdc8232dbe3b5427afbcf721a294982019bfc41eed62781e4a7c1d1df74f9618aa1f3e030ef7c601373467
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x2020005000202020503050201020302020201
  | 6, 0 => 0x400000204040201040404020000000204010301050105030200050104040400040003020404040500030400040004010203020204000204030101030301020403020103
  | 7, 0 => 0x103010003000000030303040303010103030301030303000003040003
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 3
  | 5 => 7
  | 6 => 53
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x483750262288b81b0431da3d
  | 5, 0 => 0xe316202dd884e93bb37ed318b2b7498e774504cc271723cf2264aefb
  | 6, 0 => 0xf050ea75ef97abd4e6d2ac53dfe71780d7a31a9dd4521e4fd02a639dcd8896f6cbda0ae8b7a7fc6eb335f80a8eed996a8433bd417e7b390f78a841257453dfa7630ab8195eb0066c5a16e1f1535041bb52309d604e9f36b64b1626e24835282245de062c454bc4f14178cef04131c724400f07fa3da2c27f39af1c543959b257347c1b053444ef05333061412be5b27b281a76c323a90c8322b5c1841e4306301c51670e142f793a10b1aae30ac858be08fadbb808b84eef07d2b08a0594505b04ff645b04ea503203d040b303c65a7f01180d87
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x15b04011300000100448015b04011300
  | 5, 0 => 0x4011200000001484100004011200000100448000004011200000d130480c0004011203
  | 6, 0 => 0x30440400000121010000040840400000d21030000034840400000c21000000030840c00000d21010000040840000000d21000000004040000001011000000040040400000d21010000004840400000d21010000034440000000121030000004440000000d21030000034440400000121000000040440c00000101000000034440c00000c11010000034440000000d21030000030440c00000c21010000040440c0000012101
  | 6, 1 => 0xc11010000034440400000d11010000004440c00000d11010000004440000000c11000000004040000000d11030000004040c00000c11030000004440000000111000000040840000000101030000040840000000121010000034440c00000c11000000004440c00000d1103
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_217 roots_217 7 s ws hint
  | 1 => checkCutEntry true dom_233 roots_233 7 s ws hint
  | 2 => checkCutEntry true dom_248 roots_248 5 s ws hint
  | 3 => checkCutEntry true dom_241 roots_241 7 s ws hint
  | 4 => checkCutEntry true dom_185 roots_185 6 s ws hint
  | 5 => checkCutEntry true dom_121 roots_121 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_249 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_217 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_233 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_248 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_241 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_185 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_121 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_249 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_249 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_249 == dom_249) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_249 goalM v ys) : RunD true dom_249 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_249 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_249 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_249 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_249 roots_249 goal_249 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_249 goal_249 := by
    have h0 : isConstB dom_249 goal_249 = false := by decide +kernel
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

end S_249

theorem lowS_249 : Lower true dom_249 roots_249 goal_249 9 := S_249.noCircuit

theorem lowS_250 : Lower true dom_250 roots_250 goal_250 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500050005000500050005000500050005000500050005000500050005000500, 64, 72)] (by decide +kernel) (by decide +kernel) lowS_242

namespace S_251
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (1, 129), (2, 18), (2, 66), (2, 130), (3, 19), (3, 35), (3, 67), (3, 131), (8, 72), (8, 136), (9, 25), (9, 41), (9, 73), (9, 137), (10, 26), (10, 74), (10, 138), (11, 27), (11, 43), (11, 75), (11, 139), (16, 17), (16, 18), (16, 80), (24, 25), (24, 26), (24, 88), (24, 152), (32, 33), (32, 160), (34, 35), (34, 50), (34, 98), (34, 162), (40, 41), (40, 104), (40, 168), (42, 43), (42, 58), (42, 106), (42, 170), (48, 49), (48, 50), (48, 112), (48, 176), (56, 57), (56, 58), (56, 120), (56, 184), (64, 66), (64, 72), (64, 80), (65, 67), (65, 73), (65, 81), (65, 97), (65, 193), (96, 97), (96, 98), (96, 104), (96, 112), (96, 224), (128, 129), (128, 130), (128, 136), (128, 160), (144, 145), (144, 146), (144, 152), (144, 176), (144, 208), (192, 193), (192, 194), (192, 200), (192, 208), (192, 224)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 8, 8, 9, 9, 9, 9, 10, 10, 10, 11, 11, 11, 11, 16, 16, 16, 24, 24, 24, 24, 32, 32, 34, 34, 34, 34, 40, 40, 40, 42, 42, 42, 42, 48, 48, 48, 48, 56, 56, 56, 56, 64, 64, 64, 65, 65, 65, 65, 65, 96, 96, 96, 96, 96, 128, 128, 128, 128, 144, 144, 144, 144, 144, 192, 192, 192, 192, 192]
def r2sG : List Nat := [17, 33, 129, 18, 66, 130, 19, 35, 67, 131, 72, 136, 25, 41, 73, 137, 26, 74, 138, 27, 43, 75, 139, 17, 18, 80, 25, 26, 88, 152, 33, 160, 35, 50, 98, 162, 41, 104, 168, 43, 58, 106, 170, 49, 50, 112, 176, 57, 58, 120, 184, 66, 72, 80, 67, 73, 81, 97, 193, 97, 98, 104, 112, 224, 129, 130, 136, 160, 145, 146, 152, 176, 208, 193, 194, 200, 208, 224]
def mpG : Nat := 0x3fffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_251.map (· &&& dom_251)
def goalM : Nat := goal_251 &&& dom_251
def NN : Nat → Nat
  | 6 => 15
  | 7 => 58
  | 8 => 34
  | 9 => 6
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xe0ec5758c3af880bbf13dacfae3082bd917d4a6a89b0c00388b8a9937350557272e8d27c709aacef61a343d44682e21444bcbea42a2f78980e0f6cd0
  | 7, 0 => 0xf8163700f6eaaa25f377325bedba2cd6eb37a082e99cf72fe862c26ae1096e41daaedd4ed607123dd1fc8dcad1b20460c7abc4e6c6b3f0ffc5c60400bc1b5e27b19369d7b12c4102ac7246d1a1dc12789fc63b7b9d8234fd99f3a54c9503670c91e849af8468d7b681354ecf804bfe3a6ff049936ea696846c3207096aee89676016b4bc4f76605b4bcf3f4041f761ed416b23b63fbaaead36e0a3fb363260d9330500ce300d2dd72fbe6acc2ec9b03522c0b7611fa5f5bb1ec381141b0a487f19a6f93715d5090c14b21f7812f537260f8045e10e5989ea0cb49d94097b047a039b68ba00032bcf
  | 8, 0 => 0xf27781b6ef30ebb4eda1159eeb7f97d8e8d5effbe279b87cdfff0a1fdb593504c9a1a72dc6e4f717c46ff58bbf26e9acbac9a4caba343882ac491cf48ac01de57b68da2c5e552b995c39174c584cf5694fc6710d4459301a4315b278406b731136cd96e0339a0df93289be242e21dcc02df2fb7a2780ddbb254cc15823cc482421423ce50d1adb07
  | 9, 0 => 0xfd21f23ed61bca3a9f0c20285dc8ed623d24dd0f31fd7fed
  | 10, 0 => 0xabbcdebd
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3030303030303030101010101010101030303030303030301010000010100000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000f0f0f0f000000000f0f0f0f0000000000000f0f0000000000000a0a0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
  | 0, 1 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000303030303030303030303030303030303030303030303030303000003030000000f000f000f000f000f000f000f000f000f000f000f000f000f0000000f0000000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0a0a03030303030303030303030303030303030303030303030303030202030302020f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
  | 0, 2 => 0xf000f000f000f000f000f000f000f000f000f000f000f000f000a000f000a000f000f000f000f000f000f000f000f0000000f0000000f0000000a0000000a000000000a0f0a0f000000000a0f0a0f000000000a0f0a0f000000000a0a0a0a0303000303030003030300030303000303030003030300030303000003030000000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000000f000f000f000f000f000f000f000f000f000f000f000f000a000a000a000a000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a
  | 0, 3 => 0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f0000000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0a00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f000000000000000000000000000000000505050505050505000000000000000005050000050500000a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0a0a0a0a0a0a0a00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f00000f0f00000003000300030003000300030003000300030003000300030003000000030000000f000f000f000f0005000500050005000f000f000f000f0005000000050000
  | 0, 4 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f00000f0f00000a0a00000a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a000000000f0f0f0f000000000f0f0f0f000000000f0f0a0a000000000f0f0a0a00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0a0a0f0f0a0a05050505050505050505050505050505050500000505000005050000050500000f0f0f0f0f0f0f0f05050505050505050f0f0f0f0f0f0f0f05050000050500000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0000
  | 0, 5 => 0xf0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0a0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a00000000000000000f0f0a0a0f0f0a0a00000000000000000f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00000f0f000005050505050505050505050505050505050505050505050500000000000000000a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0a0a0a0a0a0a
  | 0, 6 => 0xf0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f0f0a0a0f0f0a0a0f0f05050f0f05050f0f05050f0f05050f0f05050f0f05050f0f00000f0f0000050505050505050505050505050505050505050505050505050500000505000000000f0f00000f0f00000a0a00000a0a00000f0f00000f0f00000a0a00000a0a00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000a0a00000a0a0f0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f0f0f0f0f0a0a0f0f0a0a
  | 0, 7 => 0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a000000000000000000000000000000000f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x818331904072060cc05301c61034414c0720610360101c81840d7040720610358101c61035414c072060d405301c610349104072103c510e35c818330b040718510328101c81850c904072061431c101c61440c20407
  | 7, 0, 0 => 0x2103c510e040820610e0cd4c082061440e204080081850cc04072061210d204080061440d1040722018510e0c087c61440de04082103c5103341820614330d0408206144383740818510344d04082061440dc040820611b0c14c080081840d2040720f19a1440cd8
  | 7, 0, 1 => 0x21018510e340820f18512b8c182201840cb040822a1840c14c0820f1851210c182061210c14c0820f1851030698206144a0304082061440e704089861440e504080061440e50407224185103040821018512304081851210d104082103c5123040820f18510e0cd8
  | 7, 0, 2 => 0x2201840c14c0820f1850cc04084061440e504082061440f3040820f1440f204082061440f104082301851030408226185123040818510e0d104082201850cc040820f1840cb040822f185103040822e185103040820610e0d2040822d185103040822c1851033408
  | 7, 0, 3 => 0x236185103040820610348d04083c61440e504080081840cb0407235185103040822019a1440c0820f1840cd05382061032cd040823418510304082101840c14c08
  | 8, 0, 0 => 0x8dc61440c10208185121383040900020610305301c020f18510334180081840cd05302002061440e30408008b061440c1020021018510e04082264061440c102402103c510304080088061440c102087c6144ac3040921018510334102402061440c1740822018510334102402066851030408
  | 8, 0, 1 => 0x23718510e0c10240206144e4304080087c61443830208dd018510304092203c61440c102402381851030408008185103c810200206144843040800018510378101c83c6685103040900818510306902081851210cd04090089861440c1020020614438334080083c6144ac3060898f1851030409
  | 8, 0, 2 => 0x20f1851038c102483c61443830409
  | 9, 0, 0 => 0x21f1851030408206144ac304082061440cd040820f185103040820614438304082101851030408
  | 10, 0, 0 => 0x81851030407
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 46
  | 7 => 52
  | 8 => 58
  | 9 => 52
  | 10 => 46
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xffffffffe000fe0000001f00007f8003f8000000000001e1fc0f1fff0000000000078f007f03f800001f00000001e3cf1ffff07f800000078f3c7f803ffe0000000000003fff0000000000000000
  | 0, 1 => 0xfffc001fe000fe000003e00fff800000078f3c7ffffffe0000000000003ffffffff8003f800000ffffffe1e0000e000003fff07f800003ff8f3c7ffffffffe000fe03c01c000f807ffffc0000000
  | 0, 2 => 0xffffffe1e0000e000f1fffffff80000000003c7fffc1fe0000001e3cf1fffffffff8003f800000ffffffe0000000000003ffffff80000000003c7fffc1fe0000001e3cf1c1f007c7f8003ff8f3c7
  | 0, 3 => 0xffc3ffffe000fe000003fff07c000000078f3c7f83fffe00000000000001ff0007f8003f800000ffffffe0000001e3cf1c1ff0007f8003f800000ffffffe1e0000e000003ffffff8780003800000
  | 0, 4 => 0xffffffe0000001e3cf1ffff07c7f8003ff8f3c7fffc1f000000ffe3cf1c1ff0007f8003ff8f3c7fffc001fe000fe000003ffffffff8003f800000ffffffe0000001e3cf1fffffffff8003f800000
  | 0, 5 => 0x3ffffe000ffe3cf1c1ff07c7f8003ff8f3c7f803ffffe000ffe3cf1c1f00007f8003ff8f3c7fffc1f00000001e3cf1fffffffff8003f800000ffffe0e0000000000003e0ffff800000078f3c7
  | 0, 6 => 0xffc3ffffe000ffe3cf1fffffffff8003ff8f3c7fffc001fe000ffe3cf1fffff83ff8003f800000ffffe0ffe000fe000003e00fff800000078f3c7f83fffe0000001e3cf1c1f0fffff8003ff8f3c7
  | 0, 7 => 0x3ffe0000001e3cf1c00007c7f8003ff8f3c7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xef33bed98182c80130011f04127f9023f8910492110825e1fc0f1fff0004221049178f097f03f808443f02224513e3cf1df7704d800002066cf34fc03ffe8889048891443fff84044448a0448a24
  | 0, 1 => 0xffff149ff52aff3669b7f11fffaaab556faf7d7fffffff999b2c99b3cd3bddefb6e860b680dc05deef7da1e03a0e000df5f7705f800003fefdf7def77bedba1c3da03f01e088fa07ffffc0102082
  | 0, 2 => 0xdeef7da1e03f0e000fff7bb9e48400dc00003b65ccc17a000001ba34dd73d9cf26e800b6801005deef7da1803208000cd37bbdf68680dc28003f77ddc17e00000dbbb7dd53f14fe7f9937ff9f3cf
  | 0, 3 => 0xffc3ffffec98fead5565f7705c0000024ecdb65b83efb6019b2019b3cd00ee0005554aa9050828deef7fa3a2771be3cfdc0ff0005dd4aadcd9a6dce673c81a0020a0000177aadf68700e83000138
  | 0, 4 => 0xfffefb711bf781dbbedbfffcfe7fddbfffdfbef7ddc17800000ffb76db40ff0005dddbedddbaeff7bb009dd52aec1420a3feeffff776ebb274d38fffffffbbbf7dbfbffdffffffffff6ebfefdf7d
  | 0, 5 => 0x1efeeeedd7eedd76c2ff0fc5dddbedfdfbeffc03ffeeeedd7eedd76c0f10005d9936dd9b2cffffe3f13336793f3ef9f7fbdf6ff90ebf89137df7bbc0f999b2c81830c2e1fbfd88efdc4fefff7
  | 0, 6 => 0xffc7ffffeeddffefdf7fffffffffffffffffffffffe1017776fb776ebbfdfef13fff6ebf8f1c79f7bbc0fdddbaec1c30e2e01bed802b54072e796b83efb601bf701dbbed91f07bfffbb77fbb75db
  | 0, 7 => 0x1efeaaad55ae9d74c0004be3b9935fb971cb
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 78 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 78 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 58 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 58 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 58 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 58 then wireAt i else 0
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
  | 5 => 2
  | 6 => 41
  | 7 => 248
  | 8 => 215
  | 9 => 81
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 5, 0 => 0xf49f837bc5b07bdc
  | 6, 0 => 0xfff239e7f4a4efe7db9a6cbdd64b1dbcd4290da1d384a6f4d37d5a5fd26f88b7c7643099c737650cc6648654c28ec628c0827bc0b4def7abb4120463b3c34158b3b93226abbcdebda1d876259dea0afc8ca3b2577a24496f74cd354c6d1928156b69d33869c7ee6568e0c69e667234ba617289845a19293143d22d05418f782c3ce9fb8e3bd3cf94298e9207283e33a521acac8d1efe19e10ee1464101cc723f00463ef5
  | 7, 0 => 0x477799e946264cde4619746145ce28e745b888fa453dc2044447b33b43ea5fc14384a26c4308ccff4195ceda40e1889f400764193e0a76b53d36b5723cdd61373c45f2ec399fd57937a37dae3701f3a2346bb0d7332cefdd315a3e6f301c9c402bbb61d62a8d911529fd22b0291d426427fe3f38267f6a7b25e4b5a225a9d0be249b3fbc2456c584230548e121cad3fb21acac8d1ff0a4f71f47881e1efa92771e3bbbf81d7f3acb1d3e23fd1c3845981a28201b19b7c60618f6c5871827facf18160b4d101c40ed0ee146410ccdb1960c648c670a0173ac0759a4c50680e7af064a3f1905a5764b059ae8e7047d91f603a2f63c0357df5a02e103ea01b0e8b0
  | 7, 1 => 0x7ff5d0297fea96b97b41f31a7a62904579a930dc797b687e7927865878fd549b7855114677b1674875f47e31756d4e3b754351a5737892c87335c24071a883887122f6f470550bc06fc7da696e2be9476dc966df6d6725d26d1d970f6d1928156ab26a416aa326f968b2e25d667234ba65adb3dc63fc47e3638e0a75620adcf561f6459d607ecf906041957c5f661a995ed3371a5ea4dddd5e587b3b5c2065585a59a68b59dfe70459d48bc7560a3c89559f91aa54e5b66d54bc2bff52b1f35c5258a476521132f651a3cc28516a6db35140d18350ff345450d306995062198d4ef1c8304e7d01494e5dc7ac4d553a244baa58434b12f593488c0ac747add032
  | 7, 2 => 0xc760ad22c6648654c6445207c5cecbe2c516bcc3c4c79a71c4362deabeb1cebdbdc3d84dbc6a583cbb502ee7b9663d8ab8f0d918b87a98b6b7e1b50db7b04a80b6293391b563edffb4def7abb3ea1c06b3b93226b3acd112b2753141b2731805aefa89a2ade061b1adcd5223ac70825babbcdebdab1ee675a8a4653da80fbd2aa7324312a6d53b28a6a21847a65d4851a45db17ea3124788a12e75cba05c9e0c9b9724979a88f80899fa968b99932525989dceed980ab9f39702e73996d1cef69623974294248329941bf0fa9401dd8b919d2dbb8dc409e38aa080f98a342340891ae73088d8f412875825128451ccaa84193f3e8367bc938285ccb38154dba0
  | 7, 3 => 0xff57c6e3fdc51f40fcf1e46ffa54a75dfa340bdef9f1fd0cf9e8b17ff9a502bdf86411e4f6fdfa0ef69ff073f63da500f4a6318cf31e6744f1f66110f08d66c2f053b5d6f01ab30fefc91ee9ec3faf36ebb3b334ea6fa5daea2516d1ea023574e9b4952ce6047e13e41f48d4e394a81ce38be420e0d06a6adee89193de709ac9db367444d9f00569d9c90bb7d9a08436d7647ba5d67b54b3d66ae35cd4d68154d4d03b18d430d79dd4290da1d2fd3371d26f88b7d11f6982cfb82494cf267488cdee7162cbf92a2acb17b380c97c1dddc94847eac8b357a0c7d5da74c775a599
  | 8, 0 => 0x5269c99051182ecd4fa443774eee98c04e7d01494dd157524d553a244b575df348220590479c40ab477799e9400764193c45f2ec3ac6db543a89c7e63a52c80a38708418386a4fbf33c7da81323453fe31c49c5e30741e7a2f9534572dd8c5dd2d75e5ef2d3fef672cc3537c2ab9d070291d42642708dbce269d3f3c25e4b5a2240d42b222d635a422c1a60b22847d03218442ca1efe19e11c6c83cf1ba5a7081a2a621c18d77644171b898f167bd04416129eb115eb80ee13f70c1213a3c9261332f4c21266debf119043ab1113ba540e9d0c140e5fc1200b112f2e0919659a08f233cf08cf86460668e689047d91f60464b31b0343773602e103ea0003b50b
  | 8, 1 => 0x997395f2989dceed97491da696d1cef694812d279449023c9047e9028e89f0908e67b3f58dab066d8d6354948c109bc98921a51a8908912f8827d8df845f57b18362936e832b78278329ec7d802845597f580efb7f44a1ea7d1bb1867ce7962a7cd07c6e7a8255e579a930dc794d843d78e6af6e78484a26775435f57722cb6876b8833a768cf3c9746ab614737786c4730dd9e37285a33771f4546471d68566709d2c536fd8991b6e7b18df6e2be9476bdc43166b00a8b36783c88c66a4de69664edb306508dca764b13bf9649808436199d6345e41aa005c5c6b6a5b09a57f5a57475059e5dfb657600ab2568b7ab4567ebb1554c09588541799b2537c2de1
  | 8, 2 => 0xe4098e92e3befd99e38be420e2ba32f1e20b1520e0d06a6adcf08da0dc36dfa6dc18039fdb26579dd8df983bd8a9376cd89945a6d767b0f1d6b5a7b3d6a80871d4e5cbb3d4ce5550d4290da1d339f348d1dfb6afd18d58dad11f6982cdb83b19cabb8989ca7aca77c96b0ba5c9167ac9c54ca81ec53f0367c516bcc3c3657e3fc286941cc13b1996c101cb3ebde41edebd0e3810bb8bedadbb6d317dba8540b6b9499d3ab88da96bb88004b4b56dad38b4510ca9af5de394af2e00e3aefa89a2aec98a27ae18e635ad9e2acdac56bc36abbcdebdab4680b6a8b375f9a8a4653da6fb9f45a65d4851a4081c59a3bdb7f7a10d5c44a10956f8a05c9e0c9a5a3221
  | 8, 3 => 0xffe9d20cfe711914fe09b762fc41753afb813026f983a88ef4a6318cf143e294f07133a9ef827687ef7931a4ef75a840eecee108ee520191edd60625ed504140ecc4a9dbeb60b6bbe9af8c53e815a99be70f032fe64db4bfe52101ce
  | 9, 0 => 0xc1899e57c101cb3ec0fd5904ba19ce79ae03e0a3abbcdebdaadc8e07a8cfbc9ea6848e2fa0fb88aba0c6db67a05c9e0c9dda0f419c83c21a9525be3e8a19a4ee83f612cb802845597dc861b17c350e0679a930dc7889a3be77b1674877154aca76d1d597726209a8708f98056d01e5fb67f6166566f9e70d6501e33e61e6787e5e3c72f85e215d435bce2ce95aaddd1554e5b66d52991b8b5258a476505a2e484fb535a94e38e023477799e94434157041f75a383ce1106e3c45f2ec37a37dae37a0f94835493a6f33bc0ec32d3f5285291d4264255b937f229b4bcf1ca474d91b6c377a1580c55c1332f4c20fce210108f233cf070ade8d02e103ea0156149f
  | 9, 1 => 0xfeea3637fd1464f1f8115048f42a0a63f0f7849debb3b334e6840e11e27eefa6e0742161de709ac9dc32f7d0d16353bed11f6982c6acc047c55db4cfc516bcc3c1b8c0f8
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x1
  | 6, 0 => 0x60d07010609010708070804020600000507020c0b050906090102050305020908060a060305080205
  | 7, 0 => 0x30707010502080503030c0707020003060409030206020608070c0508050707060705080a080806050305090c05030602070c090401000603020603020c0902050a0403050709080507010805050208020602050906090805090905050305030908020c030a0c090506090701020102090508070c0a030a030605050a020508
  | 7, 1 => 0x4020405040c000a0605070503020206060a030805020503080709020203070503030a060706030505050607070207010205020607080a08030805060508000400060c0504020202000206090502080209080c040709050802080602050706050008000c050c050506070c06080705060402090508050507
  | 8, 0 => 0x205050508050803060207050502090802020802040505000203050c0705020203070203090505050805080303030509090405020103050003090206050907050309040c02020305020505050209070707090202050309090805070305020505030906020705030306030a020503080402030308090205030305020502060509
  | 8, 1 => 0x50502030209030c030305050c0202050909020608050602090205090302070705050802050c0c0503060506020205050909030302050502020302010206050803020603050209050a040c070708050602050206040503
  | 9, 0 => 0x80708070805070607050708020707020706090607060708070806060507070706060307060508030706060608070806060706070805080207080609060607090208070607030708070806020803070507
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 9 0 (CN0 s)
def CN : Nat → Nat
  | 5 => 1
  | 6 => 53
  | 7 => 631
  | 8 => 593
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0x84ae6f28
  | 6, 0 => 0xfe908366fe6338dbfa8af784f2fbb9a6ecdc25cae14047c2dc6691d7cc07d188cb47aa62c8a4d20cc5b63eddc307ac31bcb720c7baf05ce5b6e9aa6db4ac5edab454d4ebb2ead891a76171aa9f7acaa89deea04b9af1f2cc95491108905f31668f59436c8d6107c77daa5efb7c1a2cfc78f30ecc76791b077622665a6d03405a690629e766bfd03e610de1a860d51c5e4fc6710d4fc18b234812249f4376776341fe9bb53362d5bc323207132c76c06928c80ea927db132d276fa27b1cfca11c146cd6d0106c33680bd12bdc057cf5e302619db0
  | 7, 0 => 0x1c93360e1c05e27d1c05932c1bbaf9981b941ab81b4d80a31b1edd1a1adb67e71ac2158a1aa9501a1a5598d31a1fc23d1a092b6d19632c961921f65118d77644187e435f179d4d05167a05fd1667dbca15e48f2915c77bbf14b1450f14932b811420275213d3535313a3c9261332f4c2124da421124d5b4c11ddc153110b784b101077a80fae60a30f5177e80f3c79400f3419760e8aa7680e8a33610e79f9f20d1adb070bffa8b50b03795d0ada849f09b2bd70099676b20989f5d5091f84a208f233cf07c427f8068d4b7006367159059f5e8c0466ca020413c0d502f45c26024b3c50024605480235fb65023087ac01d27fb200e51447009df82700255477
  | 7, 1 => 0x35201377350d440134c24a32341f4672336991a631b6be88316ce6e43132566e30d1f5673085f6dd2fc961362edac09e2ed57aac2e85e3942e33dc2a2df2fb7a2d13d3612be60b902b9e8fd12b8caabd2aff1d712ac827b12ac452ce2a8adde32a0e4aed2a095e9b29d5e4fc29ba193f29ac53f9288137cf28240abd27951a0527947a3d27337ecd2595eb1e24b40d48249787fe2491327c2460f1562431d7a923cc482422d635a422af25582281949d225f7acf2206dce821cdc7fe21a6056121a54a9d203ea0562036da7c20319f851fbdf55b1fb021011f9df3d31f8a58181eedff121ee8c01d1eb9ded71ea70f611e75bbee1e46daa81db2c32c1d8d329f
  | 7, 2 => 0x4cfffaa94cd94eee4ca527844c76b0444c6f25914c2df7ee4bc1c98a4b5a4cbc4b56450f4ad53da34ab096bb4aaf0c934a8e207f4a66daa1497996f74949b35f491c70fc48d973d348bafdc3482bd0c947a4540a4783628445f2695345816c534548c5a64540f53e4466305c443deeb143fd779c4315b2784208abff41d21dab41d05932414b2de541369fc841231d2e40f11283406b73113f9a0d853f7d6a9e3f248d863ed5978b3ece4a9b3e93ba463e0eaa4d3d63beef3d3c72e63cde02f03ca7613d3c13669d3bd2410e3ac3c6283a45f870392f508e391c8020389db5ab37f69de1376d8e383715146836cd96e036a7ca8e361b375035bf796735578ba7
  | 7, 3 => 0x664edb3065c540cb659018f16584fce76526840a651f08dc650b5d8e62dce4e462d91f6462c4590562aa3e1e627bd6f86251740060acb05360686980602ab0b75f95264f5f234a805e37e9515e24716a5e2360c95ce72c3e5c973bbb5c39174c5ab61bdd5aaa71065a69aed15a504a155a041e9a59f5922659e5dfb659773f8858838ac856fffc685699a384565f2a5e560fd98555d7f3dd559b706d5594273c557c9dc2555d200154f909ba54c6187154c0958854a5a574534437905218d2cc520d72f35209685b51d8f72051aa15da516542e55109ae0b508de3815056947c4fa443774f57176d4eee98c04ee620574e3f5b1d4dfc513d4da8e7f64d727048
  | 7, 4 => 0x7b8701427b300b607b13fd137ac903397a998f4c7a7b54517a5a66547a255c8a79964c0c791072be78f30ecc787094f97800bc9576ef89c676d630ed76d4741176b8833a76a4091c767c043075de363b756ce60e7528fbd27522b5b5748143b7746ab61473fa613f730b1bdc73073cf27280f10d7216e29071e8bcb271e50a0971a7da66717a452b6fc0e5606f22ec9c6eb1d26a6ddb97ba6d98cd3b6cffe8cf6cc55efe6c4250376c2fbd896c1cee136bdc43166b84d9846b480cd76b0bbb446ab652976a54f17d69ba265f69563a6e69204f136876a8bd68684c776851509d68009fe96781271067000c1166eb065066ccccd8667da648666b9c626665ee07
  | 7, 5 => 0x991212f198db5c2798c56252983f165198339cb396a58393967b787f95c82a7a95b11b849514a619950116ed94e824d49447c9e0938c08d79371ff2e9347211792f62bc992ac92069276387b925c47aa90f059f090647e168fcc909e8fbd45848f84ec658f6f6cc98f59436c8f34ecfc8dd809428d912d928d58aa1d8cb2bcb38b063d238a8da0618a7b10f58a5e2b838a53e1a289cdc12889a370898975a9c08942aed38866d8188841406f880e0f0686ca9164866839648633462e85ea8f3c847b975c82aad71e827a2d19824585ad80a644f68048211880413472803c8a20802845597eaad5587e8c54ea7e3609817db4fa0c7d6757b67cd20b717bcc36fe
  | 7, 6 => 0xb4901b0ab44f5eb6b41d1b02b3d7b351b32c4cc9b2fe3d66b2a69e64b26a1fcdb245bcf6b1559dbdb14d5d74b11e4760b02ea4e2b0201cd0aea3b597ae773845ae0cb324add8d50cada185aaad87894bacfbc61fac56bc36ac491cf4ab908827ab81b15bab1470ddaa9e7fa8a9c5d262a93ef88ba85532dba82e3916a7cb5c4ea7835567a70cf453a6ea963aa6bd9d01a57620e7a55fa6efa43e3de2a3ca609da37ec52da37ad254a2f3c887a286e2fba27aab64a1c703a7a1be1fbda1a50d54a194c31aa17eb701a12b848ea126faa0a11df741a1164d02a04944939ffdbe4f9d7646c39d46510d9d1000519cce6e049ca929999c1ae29899ec8ef699d4a1a1
  | 7, 7 => 0xca7aca77ca20c362c9a1a72dc96525cfc8b7e1a4c8795ea9c84e57afc80d3350c7784f0cc6f0c48bc6e4f717c6dfc7f4c6b6f771c6a4de1fc5beca22c56067c3c4ef76cbc4a0d7a4c49c2f84c407ba4ac2c43ca8c1f20824c182d36cc13b1996c101cb3ec0de3617c0c7993cc0ae0729bf776089bf75c9cabf49a9d3bf37a4fdbe07f83bbd528692bd1d9939bcfc33abbced3d2dbcd1f026bc6632d6bbf1e103bbb77022bba3dd15bb6604debb2ddd05bac9a4caba688a8ab9ae9f79b97b4fddb979f235b9464e04b936180cb92d9467b90fb4dab8cbedf3b8940ab4b8805904b870da20b7bf36f6b7abda74b73c8712b68d260fb629cf7fb6033e0eb536d8e8
  | 7, 8 => 0xe9d28050e8cbf039e83da7c0e763af4de75d8890e6d19c01e6651958e6522bcee56dd264e528722ce4e00851e3dfd565e34c5c5ae3296f2fe29c57c3e2935012e27ea9cce23df3f6e1843b6fe12e6f5fe1005f98e0eaa2bee04f853cdff38f72df5fd715df4b20e5dedb0660de45ad51de10cb9dddc9d391dd35ed71dc9114e1dc7a1668dc467b35dc28c65cdbad0ffedbaa8b98db593504db4de7f4dafeee48da6bd7c6da3cb525d9b4e20cd99cd358d95f189dd952ccbfd915ce84d55aac57d5444092d4ec0303d4ce5550d3de1816d3b8bb32d3b5c1c5d320b344d2cce547d20fda90d17f783fd148e4d5cf7a5270cefecc6dcec619bdcd26d4b4cc201861
  | 7, 9 => 0xffd7bf39ff3724dffeb76f65fe911e7cfe859561fe812667fe58e9d1fde1be64fdceeeeefd6eba35fc9b5c7cfbf9ca23fb9c39bbfb813026fb78ab36fb320674fb04f3eef9a84f50f927382ff8f921cef8ef48bdf8ea86a3f818793af7c4979ff7c0f771f723b197f6a720c5f6a2addbf66236c6f5811a6cf4e60e9ef463c098f43455b2f40585a6f3efa25cf3bec7f9f2281740f1dc6788f1dae9a2f10ea292efb2fa13ef80e76eef5125fbeecee108ee4eeb5ded932082ed432092ed2f5f82ecdbe086ecc4a9dbeca7d411eb812c39eb7f97d8eb7c5c76eb1b6276
  | 8, 0 => 0x1e640e3d1daccc011c8a23011b81a3401b665f6e1b56701a1a02250a1905f5b218aad4ea1811d3c8170df1e316c2c85015ea8d3a155e111d13f28723131dd47913116f7d12eeb1d81274951812626c8510e2f98e105a461e1048819d1045cc66102d6be80ff3b6440f3060030ebb78e50decbdf30dda3b8e0d9d0c580d79a3870cdddb230cb9ebba0c0cf9b40bf1620b0b7ee1fa0ad30cde0aaeb0bb0a36b3fb09f1a21008d006c708bc3447087d491c0839d3e907f9e8a606f1c5120691e34d0682362d0676ef1c04e5479604a52a30040902e103ca07fa03950dd1031d626c030822e902f2a2ab0275af3602663ced023bad8101f7965701c1444e0044eec8
  | 8, 1 => 0x37ec8c8137e92192378356db366b66563602217035469ba3353b2ad2344481d333e4032733c5561b33511f4c326386fd322ed9b931d934e2318721e63169ca0a311d2f37310b10a4303051d92fd5ae4a2fd470562f420d932f105dce2e411cab2debc06c2d980b512cc52f5f2bbfc5832bb53f812bb5001c2bb107772af2bf192af03ab32a95b26329bd75ed294921b4293af0172921596f28dde43c2899026e28987bda2773506e274dfd74273c29db270b502e27077c9726d09ab5268dbc902550f8eb246e184d245a520f241ab07122c8673f22c4634a229ba6aa22703bc52261748620c5275a208e93f02037f7ec1fcfb2471f0df4a01ebaaa581e88f5e0
  | 8, 2 => 0x5320bf4a5307975052f19ca952d2ea0c52bb28205268acb152655756518bb4635173128251709eae5168c88c512f8632504f49b84fe61de64fba7efc4f1d6e544e8fd0bf4e7978724e1ccc904dfd1e804cfa374c4ced61774b9e55ff4b81cccb497663c948da84f348b525794834f7d847f9622847ca3f8747426c6e473dfa344731cce34703605645e85cf645cb22f745a7e5e1458f1de44582493b4409a39243a96fb3433661c143047714425c981e41add2ad4188218e412098bd4118096640d6d12a405a6fa9404a6c6b3fdfb0d93f6bdef53e92c5733e8308df3e4d19483d91e03f3d18c6b53c448c593c25b3933c0466e43a37baf03a2d0c7e38beac9d
  | 8, 3 => 0x717ff3aa7117a31c6f844f716e9300ed6e09885a6d9eddf86d9af6226d4fa45f6cf872476cd14afb6cc4af416cb3f4d86c5645b56c25dd1e6be00f076bd8e5296a648c356a6150b16a21170268bf90d6673ffbeb66e5d8dd66b4c29165bfb51865b14b1364e8b36363ded9706383068a6347b50162cb5210628767d4627399006202692b61ffe4c56143f66761403b7e6133348260512766600fef485fa825ec5e1afa405d56758c5d0700065ce89cac5c63ea725be2c8c95b4557d05adbcb435abf849e5ab073e25a60cfcb5a4928785959389d58909cd4586ff20e585124a95814be9957a3f4ee579e3e0256c5b321559730285535b9e954a88ab75446176b
  | 8, 4 => 0x8f60cebb8f5fff568f32d4ff8e7c63438e4623ef8e3f06758d4b7fbd8ce92e788c76fa3a8c4563fb8bed10588a7c514489794e9a89060cc9889b5e75888048c08874ffa98796b5cf87571e1f86c2d5ef86ae4df0862d1866859208b5852ad76785212244850cc892840fd6a1836f626383550621825f82ef818007c280ea663180b295ff7ea4a6667ea466067e51f1787d68e6597d126add7cf807087cb78ff37c4ca22c7bf8abe57b357d657ab919c57a6aab937a14212679e7f4cc78b8ceec7897cba077ec0c637769c37477455436773825cd76c0a70076792de87526fbeb745fb14d74005f5073e6edf873c4cf9d7395acfc730967a9727073ad71dc1fb3
  | 8, 5 => 0xa64ac9eea6361908a625a909a57cad33a5706647a49af314a4796dcfa4022ed5a3fe2f0ca3039342a2e88f3ba2e51609a2d82603a27bb8a6a21052c5a1bf41c9a1acd8aaa1743647a153220ea1361f53a130c114a11a492aa0345c619ff3e54c9f9df3a49ec9a1919e2bcf729dc1ac039dbfc1d99cc0f5259c1efe099be98fd69bc1668c9afc17d09aee83829a37ad4299d3cf9a99ac89bc98dcad6a98901cb69872dcdf98236d0d9760d178972d1073960ec231959928f194c03c2e9494235b948afe4b944aca1694161cd293e8fa9993abdf77935c6db992dc790f92be12f192803006925501e2916c779a9158d28a912950ac907ca96e905234898fd30385
  | 8, 6 => 0xc253a2a8c1f4ab86c1da2fa6bff8cc98bf84a9bbbf41a80bbea750d7be66f97cbde19a78bdadfb2abd2ec706bd21f131bb89db9fbafe4274baa6d47fbaa2ee69b9fcaff3b9fc01b2b95b29e6b916ed32b8acf63ab865fe2eb85efa8eb6c391d1b666f6bfb63e2b4cb5080263b4ed128fb4d8dfc2b478906bb44c9a6fb447bc26b419670db4034a21b37ff3b5b3622344b34b8bffb303f4acb2ec411cb0f644dcafa18679af8670c4af37e7c2af207396af14ca53ae54fe48ae0c732bad690fe4ad33406aacd435ccac12f096abbc9e19ab9c34afaabe4c1eaa8730d6aa4de3e2aa1d5eeda8dbecffa8bceea3a8274d2ea8256056a700eadaa6e8c3aea693f983
  | 8, 7 => 0xe0ee7e45dfa0de75df4b612adf02f49fdcab825adb7eb86fdb295109d9d34f7cd95dc566d8d9bcbbd862cc20d7f0c447d767a224d69acf78d5f5d6d9d5ce3111d59c13c2d55b264cd53b7984d4cdb4b0d4a75a74d4798153d3c362ccd395db54d35f588ad32ea81bd2844bd3d203c7fcd1bfdc34d0e379accf82393bcf2d7532ceb0837ece611a52ce490ec0cdadf13ecd9a2187cd78461fccad06d1cb5a7428cb25c6e4cb0e445dca74b6a0ca4bc2efc9eeb73fc9ad5da7c90b7c00c908f79ac87a5e4bc8494e53c838fabec837fb68c836e918c78cd401c7784f0cc6e2ad97c6b138c1c5240d15c4b29529c46eaaedc46d166dc3c71d29c321b19ec2c33a88
  | 8, 8 => 0xf8a2aad8f861e55ff860b2c6f8028909f7e9a1b0f7cb4589f7757172f6d03935f669e190f6402415f6304555f5b80ab5f4a5560af40368ddf34e76d0f342872bf2a49011f2609c2cf23977a2f22beee8f1cc9216f1c1b18df1c05a7ff10babc4f063a65cefbca04cefa4714aef895b95ef3f22c2ef26bf84ef034088eeed1f13ee36b795ede8d59bed3a883ded362b3bec5ed6afec17ac75ec15db67ebe889d4eb6091b3eb5c4481eb42846eeb3f527ae9ad07ede892235ae87ff67ae82719aee7794bcee7554914e68ad1bfe5e640a8e5c81d68e47d1428e478b9f6e461fe73e446c608e41b7db2e40119dde3c0a2c8e2c0ff14e20ece19e1c22c9ae11d33fb
  | 8, 9 => 0xffe31731ff68f424feca44eefe7d50abfe69e44dfdf20878fd55ebfafd480d59fd1276c7fc79f3b5fc41a188fbc23f3bfb7e54fffa5a1ff8fa34d01ff9b9d4a7f95e14b7
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x4515202
  | 6, 0 => 0x18754480800454112022745a454c1c004555320217995044c1c1d26915308000d530480c0064d512022645a454c1cde6548130771d91254c1c0062d5120227995044c2000354c1203000da054808002651520637995044c1dc72651530637819454c19c7644953070009a454808de654813070018735480dc7644953060011a05480c5e654113070009a454809c7644953070009a05480cde6541130700115044809c764495306
  | 6, 1 => 0x169152050005a4548140062cd52030009a4548080061d512020009a454808de654113060005a454815c3654c13080009605482400258d52030005a45481400369412020018b5448080036915205000da25481400454112020649a454c2000269152020005a4548140004551202
  | 7, 0 => 0x19720481c00054952070009a4548080026915207000112448180064cd52080000005442400000931050000035440c00169152070009a45482000001151020019325481c00044c12080019325481c00001171050000045c41400000951050001525481c00000c11030000035440c00000d61050019125481c00269152080000025840c0016915207000da05481c0006515208000002584240016915207001912048180000095105
  | 7, 1 => 0x9a4548200064c952060000035440c00000961030000035841400001151050005a45481c00001151060000025840c0065481206001153548200000115102000da05481c0064495207000da05481c00001171050000025441400000151080009a4548200060cd52080011504481c00368152070018335482000269152070009a45481c0026811206000003544240000097105000002544140000115105001970448180026915208
  | 7, 2 => 0x19320481c00269152080000024441400001151020001a4548200065cc12080001120481c0000096103000005444080000115102000da05480800000931050001525481800644812070009a45482000000c11090011a05480c00001151060019704481c00354c1203000da05481c00044812070000045441400000951050000025441400254812070019125481c00001511020009520481c00644952070005a4548140004491207
  | 7, 3 => 0x11525481c00001151020001130482000000911050005a45481c00454112060005a45481c0060c952070019325481c00001151020011525481c00001511020000030440c0016915207000da05481800000d51030000024841400368152020000035440c00054d52080000054440800269152070005a45481c00644952070001534482000654112080000035440c00000d61050000035440c0000015108000000544080000141102
  | 7, 4 => 0x35841400044912070001525481c0064cc12080011525481c00000951050001124481c00644d52080019325481800654112080000030440c0000016109000da05481c0064c812060019120481800644952060005a45481400000d61050000054c40800000d51030005a45481c00169152070000004440800001151060000035440c00654812070019125481800000c11030000030442400454112080001a4548180036815207
  | 7, 5 => 0x19120481c00169152070019530482000000d5103000da05481800001151050000025441400269152070000045441800368152070000035841400000151090009a4548200026915202000d530480c0000011102001150448080036815206000112448180036815207000da4548200026915207000da05481c00454d52080000025c41400001151020005a45481400269152080009a45480800169152070009a4548180064c95207
  | 7, 6 => 0x9a45481c00000911050019704481c00265152060019704482000000d61050009a45481800368152070019320481800000161090000040842400268112070000054c40800644952070011525481800001151050000045441800654112070009520481c00644952070001535482000454952060011504481c0036815202000002444140065cc12080000005440800269152080011a05480c0036815207000004544140005495207
  | 7, 7 => 0x54c40800000951050019325481c00000131020000045440800000c21030000025840c00000d51030009520481c00001151050019125481c00054d52080000004440800454112060001945481800000d61050018325481c00000171020000045441800454112080005a45481c00368152060000025840c00000111020000035c42400368152060011520481800069152080019125481c0016915205000000544080000115106
  | 7, 8 => 0x19125481c00644812070001a4548200036815202000000544200065411206000003584140064c952060011525481800001151020001525481c0000015102000000444080064c812070011504481800368152020005a45481c00000971050011525481800000961030009a45480800001151060000005442000044812070000035440c00269152070019325481c00644952060005a45481c0065c81207001950448200006915207
  | 7, 9 => 0x11504481c00000111020011504481c0025481206000da05481800001171050000035440c00000961090001a45481c00454952070000054440800604d52080001525481c00368152070011504481c0036815206000004544140065c112070000040842400654812060009a45482000269152020018325481c00368152070000025c4140004491207001150448180045495207000000544080065481207000000444080060cd5208
  | 7, 10 => 0x19704482000169152070019325481800044812070001525481800001151050018335482000044d1208000da05481800001531020019504481800454952070005a45481c00644952070005a45481c00000d51030019125481c00644952060005a45481400654c12080000005c4080045411206000112048180016915207000002484140045495207000002544140000153102000da0548180016915207000113048200065c81206
  | 7, 11 => 0x19130482000468152030005a45481c00654112070005a45481c0000095105000da05481c00454952060000025840c00000151080009a4548200036815206000d53048200000096103000da04482000001151020000025441400354c12080019704481800000d61050019120481c0046815203000112448180016915205000da0548180026811207000004544080060c952060019125481800454d52080009a04481c0065411207
  | 7, 12 => 0x45c41400044812070005a4548140065c812070005a45481c00169152070011525481800454952070000030442400001151020009a45482000169152070005a45481400054952060000025840c00644c12080009520481c00269152080000025840c0065c812070005a45481c00368152060019504482000069152060019530482000268112070019520481c0045495207000da05481800269152080001535480c0026811206
  | 7, 13 => 0x1970448180026915208001973048200026915208001150448180065411208000002584240016915207001970448180065cc12080019704481c00454112060000024441400054952070001124481c00454112070019320481c00368152070000054440800000951050000025840c0000015103000003044240006915207000da45482000169152070019720481800268112070000054440800054d5208000994548180000115102
  | 7, 14 => 0x45441400000d51030000025441400368152060018335482000368112080000005840c00069152080000050c4080065c81207000952048180000096103000004544140026811207000da0548180045411208000da0548180025481207001950448180065481207000003584140000153102001152548180060cd52080000004440800001021090019504481c0026915202000da05481c0000115102000000544240036815207
  | 7, 15 => 0x5840c00269152080000004440800169152070009a45480800169152050000035440c00654112080000045441800654c1208000000544240000096109000da05481800269152080009945481c0064cd52080011504480800054d52080000035440c00001151020009a4548080064c81207000da05481c00000951050000054c40800044812060019704482000169152070011504481c00269152080000035840c0000015108
  | 7, 16 => 0x5a45481c0065c112070000024c41400269152020009a45482000000c11090001525481800000c3109000da05481c00368152060000040842400044912070019530482000169152070000004440800001151020019320481c00044912070000024441400054952070000035440c00000151030001130482000368152070000005c40c00269152080005a45481c00000911050019125481800468152030000025840c0065c81207
  | 7, 17 => 0xda05480800454952070000045441800254812070019120481c0064481207000153548200060c952060001124481c00000111020019504481800454d52080000025842400044d12080009a45482000654112070000004c40800268112070011504481c00000961030019520481c00169152070000025842400054d5208000da05481c00000111020000025441400354c1208000da05481c00000d6105000004544080060c95207
  | 7, 18 => 0x25441400044912060000035841400001151020009a45482000269152020019530482000368152070005a45481c00169152070000005c40c00254812070009a4548200000015109000d530482000269152020019135482000654812070001a45481c0006515206000da05481c00000c1103000004544080065411206001933048200004481207000002544140065c112080000025842400000151090019704481c00000c1103
  | 7, 19 => 0x16915207000da05481c0026915208000da05481800000111020019504481800268112070019325481c00001531020019325481c0064c812070011504482000654112070000024c41400000d6103000da05481800000921050000025441400368152070000025c4140016915205000004544140000091105
  | 8, 0 => 0x5441800000d51080000024441800000911070000024441c00000151070000034442000000811060000004442000001151060000004440800000111070000004441800000c11080000025441400000151070000045440800000151070000020441800000d51080000020441c00000111060000045442000001151080000005442000000111070000020441800000951070000025441c0000011106000003544200000095106
  | 8, 1 => 0x30442000000111060000005442000000111060000020441c00000151080000025441c00000d51080000045441c00000911070000025441800000911070000045442000000111060000025441800000911070000004441800000911060000005441800000911060000005441c00000811060000025441c00001151080000025441800001151070000004441c0000115108000003544200000095107000000444180000115106
  | 8, 2 => 0x45442000000d51080000035440c00000151080000004441c00000951070000025441800000951070000045441c00000151070000020441800000811060000045441800000811060000005442000000111070000004441c00000951060000045441800000811070000034442000000811070000025441800000151080000005441800001151080000045441c00000d51030000004441800000d5108000004544080000015107
  | 8, 3 => 0x4442000000911070000045441800000d51080000025441800001151060000030442400000811060000024441800000d51080000005440c00000111060000004441800000911070000020441c00000151070000030442000001151060000045441c00000911050000025441c00000111070000020441c00000951060000004441c00000911070000030442000001151070000025441400000151070000020441c0000115102
  | 8, 4 => 0x25441c00000151070000045442000000151080000045440800000911070000020441800000911070000045441c00000151030000045442000000d11080000020441800001151060000045440800000151080000024441c00000811070000005440c00000151060000004441800001151080000025441c0000011108000000544080000091105000000444200000095106000004544180000011107000000544200000015102
  | 8, 5 => 0x4441c00000951060000004441800000951060000024441c00000951050000004441800001151070000024441800001151060000035442400000151080000034442000000951070000005441c00001151070000025441c00000911070000025441c00001151080000005442000000811070000020441c00000111070000034442000000d11080000045441800001151050000020441c0000081106000003044240000081106
  | 8, 6 => 0x5440800000151080000025441800000151070000034442000001151080000025441800000151070000005441800000911070000024441800000d51080000005442000000151090000045441c00000951070000035442000000951050000025441c00001151080000024441800000d51080000024441c00001151060000004441c00000c11080000005441c00000111070000024441c0000115106000002444180000091105
  | 8, 7 => 0x20441c00001151070000045441800000151060000024441c00000111070000004441c00000c11080000045441400000d11080000020441c00000951060000005441800000951070000004442000001151080000045441c00000151070000045441800000811060000005441c00000911060000020441c0000115108000004544180000015107000004544180000011106000000444180000011108000000444080000081107
  | 8, 8 => 0x45441c00000811060000024441c00000c11080000045441800000151060000005442000000151020000035440c00000c11080000030442000000151070000020441c00000151080000004442000000951070000005441800000111070000025441c00001151060000030442000000911070000045442000000151090000035442000000d1108000000444180000095107000002544180000095106000004544200000011107
  | 8, 9 => 0x5441800001151070000030440c00000111070000024441c00000951070000020441c00000111020000025441c00000151060000045441400001151070000004442000000d11080000005441c00000151060000045441c00000811070000045441800000151080000024441c00000151070000004441c00000c11080000024441800000151080000025441800000d51080000020441c00000111080000025441c0000015106
  | 8, 10 => 0x20441800000151080000005441800000c11080000045442000001151020000035442400000951070000004441c00000c11080000005442000000951060000030442000000911060000005441c00001151060000025441800001151060000045441800000111070000045441400000911060000035440c00000111070000025441c00000151070000024441400000151080000045441c0000095105000000444200000115107
  | 8, 11 => 0x24441400000951070000035442400000911070000020441c00000111020000004441800000151060000034442000000d51080000005442000000811070000024441800000111080000005440c00000911070000030442000000151070000045441800000111080000005441800000d11080000045442000001151020000024441800000151020000045442000000d11080000025441400000151060000045441c0000015107
  | 8, 12 => 0x30442400000111080000020441c00000951070000024441800000811070000004441c00000d51080000024441c00000911060000025441800000951070000004441800000151060000004441c00001151070000024441c00000111080000034442000001151060000020441c00000911060000005440c00000c11030000035442000000c11080000045441800000151070000005441c00000d5108000000444180000015106
  | 8, 13 => 0x35442000000911060000035442000000d51080000005441c00000811060000004441c00000d11080000030442000000951060000005442000000811070000020441c00000d51030000005442000000111070000020441800001151070000024441c00000951070000045441c00001151020000034442000000111070000024441800000951070000045441c0000095105000004544180000015106000004544180000095107
  | 8, 14 => 0x25441c00000151060000004441c00000151090000024441800000d51080000045441c00000151060000005441800000911050000020441800000911070000034442000000911050000004440800000111080000024441c00000111070000005441c00000811060000024441800000951060000045441800000151070000004441c00000111060000045442000001151020000045441800000911060000020441c0000115107
  | 8, 15 => 0x30442000000111060000025441c00001151050000004442000000911060000035440c00001151070000045441c00000c11080000005441800000951050000025441c00000811070000030442000001151060000004441800000911060000005442000000951060000035442000000811060000045441c00000c11030000004441800000151070000005441c00000951060000045441400000151080000045441c0000091107
  | 8, 16 => 0x20441c00000911070000030442000000111070000025441c00000151070000004442000000151060000045442000000151060000020441800000811070000035442000000911070000004442000000811060000045441c00000951070000024441c00000d11080000025441800000811070000005441c00000811060000045442000000111060000004442000000111020000045441c00000811070000004441c0000011108
  | 8, 17 => 0x20441800000111080000024441800000151060000034442000000811070000034442000000811060000004441800000951060000045441400000c11080000045441c00000951060000004441800000c11080000024441c00000911060000045442000000911060000045441c00000911050000045441400000151070000045441c00000151070000004441c00000111060000024441c00000d1108000000544200000095107
  | 8, 18 => 0x111080000024441800000c11080000045441c00000111080000030440c00000811070000004442000000811060000005441800000d11080000005442000000151020000045441c00000911070000024441c0000011107
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 11 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_186 roots_186 5 s ws hint
  | 1 => checkCutEntry true dom_234 roots_234 5 s ws hint
  | 2 => checkCutEntry true dom_235 roots_235 8 s ws hint
  | 3 => checkCutEntry true dom_187 roots_187 8 s ws hint
  | 4 => checkCutEntry true dom_171 roots_171 6 s ws hint
  | 5 => checkCutEntry true dom_250 roots_250 8 s ws hint
  | 6 => checkCutEntry true dom_243 roots_243 9 s ws hint
  | 7 => checkCutEntry true dom_249 roots_249 9 s ws hint
  | 8 => checkCutEntry true dom_219 roots_219 9 s ws hint
  | 9 => checkCutEntry true dom_123 roots_123 8 s ws hint
  | 10 => checkCutEntry true dom_51 roots_51 4 s ws hint
  | 11 => checkCutEntry true dom_227 roots_227 7 s ws hint
  | 12 => checkCutEntry true dom_90 roots_90 5 s ws hint
  | 13 => checkCutEntry true dom_242 roots_242 7 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_251 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_186 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_234 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_235 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_187 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_171 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_250 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_243 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_249 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_219 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_123 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_51 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_227 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_90 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_242 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

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
private theorem z6 : ∀ i, 0 ≤ i → i < 15 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 15 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 58 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 58 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 34 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 34 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 6 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 6 0 = true)
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
  scr true dom_251 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_251 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_251 roots_251 goal_251 11 := by
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

theorem lowS_251 : Lower true dom_251 roots_251 goal_251 11 := S_251.noCircuit

theorem lowS_255 : Lower true dom_255 roots_255 goal_255 12 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_251

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [4, 7] }, { op := GateOp.and, inputs := [8, 9] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [11, 7] }, { op := GateOp.and, inputs := [5, 12] }, { op := GateOp.or, inputs := [1, 3] }, { op := GateOp.or, inputs := [14, 4] }, { op := GateOp.and, inputs := [6, 15] }, { op := GateOp.and, inputs := [3, 7] }, { op := GateOp.or, inputs := [10, 13] }, { op := GateOp.or, inputs := [18, 16] }, { op := GateOp.or, inputs := [19, 17] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 20⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  decide +kernel

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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

end PEqualNP.Outside.L_meta_14338_aux

theorem PEqualNP.Outside.L_meta_14338 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_14338_aux.main
