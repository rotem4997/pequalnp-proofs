import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14700_aux

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

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xeeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfcfcfccccc0000fcfcfcfccccc0000fcfcfcfccccc0000fcfcfcfccccc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefcfceeee0000fefefcfceeee0000fefefcfceeee0000fefefcfceeee0000
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeeeeecceeeeaa00eeeeeecceeeeaa00eeeeeecceeeeaa00eeeeeecceeeeaa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfefefefceeeeaa00fefefefceeeeaa00fefefefceeeeaa00fefefefceeeeaa00
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_82 : Nat := 0x500050000000000050005
def goal_82 : Nat := 0xffffccccffffcccccccc0000cccc0000ffffccccffffcccccccc0000cccc0000
def roots_82 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_83 : Nat := 0xf000f00000000000f000f
def goal_83 : Nat := 0xffffccccffffcccceeee0000eeee0000ffffccccffffcccceeee0000eeee0000
def roots_83 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_86 : Nat := 0x5500550000000000550055
def goal_86 : Nat := 0xfffffcfcfffffcfccccc0000cccc0000fffffcfcfffffcfccccc0000cccc0000
def roots_86 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_87 : Nat := 0xff00ff0000000000ff00ff
def goal_87 : Nat := 0xfffffcfcfffffcfceeee0000eeee0000fffffcfcfffffcfceeee0000eeee0000
def roots_87 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_89 : Nat := 0x30303030000000003030303
def goal_89 : Nat := 0xffffaa00ffffaa00aaaaaa00aaaaaa00ffffaa00ffffaa00aaaaaa00aaaaaa00
def roots_89 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_91 : Nat := 0xf0f0f0f000000000f0f0f0f
def goal_91 : Nat := 0xffffeeccffffeecceeeeaa00eeeeaa00ffffeeccffffeecceeeeaa00eeeeaa00
def roots_91 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_95 : Nat := 0xffffffff00000000ffffffff
def goal_95 : Nat := 0xfffffefcfffffefceeeeaa00eeeeaa00fffffefcfffffefceeeeaa00eeeeaa00
def roots_95 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0]

def dom_114 : Nat := 0x50005000500050005000500050005
def goal_114 : Nat := 0xffffccccffffcccccccccccccccc0000ffffccccffffcccccccccccccccc0000
def roots_114 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_118 : Nat := 0x550055005500550055005500550055
def goal_118 : Nat := 0xfffffcfcfffffcfcfcfcfcfccccc0000fffffcfcfffffcfcfcfcfcfccccc0000
def roots_118 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_119 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def goal_119 : Nat := 0xfffffcfcfffffcfcfefefcfceeee0000fffffcfcfffffcfcfefefcfceeee0000
def roots_119 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_123 : Nat := 0xffffeeccffffeecceeeeeecceeeeaa00ffffeeccffffeecceeeeeecceeeeaa00
def roots_123 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_127 : Nat := 0xffffffffffffffffffffffffffffffff
def goal_127 : Nat := 0xfffffefcfffffefcfefefefceeeeaa00fffffefcfffffefcfefefefceeeeaa00
def roots_127 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0]

def dom_137 : Nat := 0x30300000000000000000000000000000303
def goal_137 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_141 : Nat := 0x333300000000000000000000000000003333
def goal_141 : Nat := 0xfffafffafffafffafffafffafffafffaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_141 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 7 0]

def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def goal_147 : Nat := 0xeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeee0000eeee0000eeee0000eeee0000
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_151 : Nat := 0xff00ff00000000000000000000000000ff00ff
def goal_151 : Nat := 0xfefefafafefefafafefefafafefefafaeeee0000eeee0000eeee0000eeee0000
def roots_151 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_153 : Nat := 0x303030300000000000000000000000003030303
def goal_153 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def goal_155 : Nat := 0xffeeffaaffeeffaaffeeffaaffeeffaaeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_159 : Nat := 0xffffffff000000000000000000000000ffffffff
def goal_159 : Nat := 0xfffefffafffefffafffefffafffefffaeeeeaa00eeeeaa00eeeeaa00eeeeaa00
def roots_159 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]

def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def goal_163 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaacccccccc00000000cccccccc00000000
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_164 : Nat := 0x110000001100000000000000000000001100000011
def goal_164 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f000000000f0f0f0f000000000
def roots_164 : List Nat := [xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_165 : Nat := 0x330000003300000000000000000000003300000033
def goal_165 : Nat := 0xfffffffffafafafafffffffffafafafaf0f0f0f000000000f0f0f0f000000000
def roots_165 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_167 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def goal_167 : Nat := 0xfffffffffafafafafffffffffafafafafcfcfcfc00000000fcfcfcfc00000000
def roots_167 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def goal_169 : Nat := 0xffffffffffaaffaaffffffffffaaffaaaa00aa00aa00aa00aa00aa00aa00aa00
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_172 : Nat := 0x11110000111100000000000000000000111100001111
def goal_172 : Nat := 0xfffffffffff0fff0fffffffffff0fff0f0f0f0f000000000f0f0f0f000000000
def roots_172 : List Nat := [xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_173 : Nat := 0x33330000333300000000000000000000333300003333
def goal_173 : Nat := 0xfffffffffffafffafffffffffffafffafaf0faf0aa00aa00faf0faf0aa00aa00
def roots_173 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_175 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def goal_175 : Nat := 0xfffffffffffafffafffffffffffafffafefcfefcaa00aa00fefcfefcaa00aa00
def roots_175 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def goal_177 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaaaaa0000aaaa0000aaaa0000aaaa0000
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def goal_178 : Nat := 0xffffffffcccc0000ffffffffcccc0000cccccccccccc0000cccccccccccc0000
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def goal_179 : Nat := 0xffffffffeeeeaaaaffffffffeeeeaaaaeeeecccceeee0000eeeecccceeee0000
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_181 : Nat := 0x3300330033003300000000000000000033003300330033
def goal_181 : Nat := 0xfffffffffafafafafffffffffafafafafafaf0f0aaaa0000fafaf0f0aaaa0000
def roots_181 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_182 : Nat := 0x5500550055005500000000000000000055005500550055
def goal_182 : Nat := 0xfffffffffcfcf0f0fffffffffcfcf0f0fcfcfcfccccc0000fcfcfcfccccc0000
def roots_182 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_183 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def goal_183 : Nat := 0xfffffffffefefafafffffffffefefafafefefcfceeee0000fefefcfceeee0000
def roots_183 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def goal_187 : Nat := 0xffffffffffeeffaaffffffffffeeffaaeeeeeecceeeeaa00eeeeeecceeeeaa00
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_189 : Nat := 0x333333333333333300000000000000003333333333333333
def goal_189 : Nat := 0xfffffffffffafffafffffffffffafffafafafaf0aaaaaa00fafafaf0aaaaaa00
def roots_189 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_190 : Nat := 0x555555555555555500000000000000005555555555555555
def goal_190 : Nat := 0xfffffffffffcfff0fffffffffffcfff0fcfcfcfccccc0000fcfcfcfccccc0000
def roots_190 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_191 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def goal_191 : Nat := 0xfffffffffffefffafffffffffffefffafefefefceeeeaa00fefefefceeeeaa00
def roots_191 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]

def dom_203 : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
def goal_203 : Nat := 0xffeeffeeffeeffeeffaaffaaffaaffaaeecceecceecceeccaa00aa00aa00aa00
def roots_203 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_209 : Nat := 0x30003000000000003000300000000000300030000000000030003
def goal_209 : Nat := 0xffffaaaaffffaaaaaaaaaaaaaaaaaaaaffff0000ffff0000aaaa0000aaaa0000
def roots_209 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_211 : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
def goal_211 : Nat := 0xffffeeeeffffeeeeeeeeaaaaeeeeaaaaffffccccffffcccceeee0000eeee0000
def roots_211 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_214 : Nat := 0x550055000000000055005500000000005500550000000000550055
def goal_214 : Nat := 0xfffffcfcfffffcfcfcfcf0f0fcfcf0f0fffffcfcfffffcfccccc0000cccc0000
def roots_214 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_215 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def goal_215 : Nat := 0xfffffefefffffefefefefafafefefafafffffcfcfffffcfceeee0000eeee0000
def roots_215 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_217 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def goal_217 : Nat := 0xffffffaaffffffaaffaaffaaffaaffaaffffaa00ffffaa00aaaaaa00aaaaaa00
def roots_217 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_218 : Nat := 0x5050505000000000505050500000000050505050000000005050505
def goal_218 : Nat := 0xffffffccffffffccffccff00ffccff00ffffccccffffcccccccc0000cccc0000
def roots_218 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_219 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def goal_219 : Nat := 0xffffffeeffffffeeffeeffaaffeeffaaffffeeccffffeecceeeeaa00eeeeaa00
def roots_219 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_223 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def goal_223 : Nat := 0xfffffffefffffffefffefffafffefffafffffefcfffffefceeeeaa00eeeeaa00
def roots_223 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_230 : Nat := 0x5500000055000000550000005500000055000000550000005500000055
def goal_230 : Nat := 0xfffffffffcfcfcfcfffffffff0f0f0f0fcfcfcfcfcfcfcfcfcfcfcfc00000000
def roots_230 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_231 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def goal_231 : Nat := 0xfffffffffefefefefffffffffafafafafcfcfcfcfcfcfcfcfcfcfcfc00000000
def roots_231 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_237 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def goal_237 : Nat := 0xfffffffffffafffafffffffffffafffafaf0faf0faf0faf0faf0faf0aa00aa00
def roots_237 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_238 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def goal_238 : Nat := 0xfffffffffffcfffcfffffffffff0fff0fcfcfcfcfcfcfcfcfcfcfcfc00000000
def roots_238 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_239 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def goal_239 : Nat := 0xfffffffffffefffefffffffffffafffafefcfefcfefcfefcfefcfefcaa00aa00
def roots_239 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_242 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def goal_242 : Nat := 0xffffffffffffccccffffffffcccc0000ffffccccffffcccccccccccccccc0000
def roots_242 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_243 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def goal_243 : Nat := 0xffffffffffffeeeeffffffffeeeeaaaaffffccccffffcccceeeecccceeee0000
def roots_243 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_244 : Nat := 0x11001100110011001100110011001100110011001100110011001100110011
def goal_244 : Nat := 0xfffffffffffff0f0fffffffff0f0f0f0fffff0f0fffff0f0f0f0f0f000000000
def roots_244 : List Nat := [xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_245 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def goal_245 : Nat := 0xfffffffffffffafafffffffffafafafafffff0f0fffff0f0fafaf0f0aaaa0000
def roots_245 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_246 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def goal_246 : Nat := 0xfffffffffffffcfcfffffffffcfcf0f0fffffcfcfffffcfcfcfcfcfccccc0000
def roots_246 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_247 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def goal_247 : Nat := 0xfffffffffffffefefffffffffefefafafffffcfcfffffcfcfefefcfceeee0000
def roots_247 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_251 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def goal_251 : Nat := 0xffffffffffffffeeffffffffffeeffaaffffeeccffffeecceeeeeecceeeeaa00
def roots_251 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_253 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def goal_253 : Nat := 0xfffffffffffffffafffffffffffafffafffffaf0fffffaf0fafafaf0aaaaaa00
def roots_253 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_254 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def goal_254 : Nat := 0xfffffffffffffffcfffffffffffcfff0fffffcfcfffffcfcfcfcfcfccccc0000
def roots_254 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 6 0, xs256.getD 7 0]

def dom_255 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def goal_255 : Nat := 0xfffffffffffffffefffffffffffefffafffffefcfffffefcfefefefceeeeaa00
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

def isoMvS_137 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_137 : Lower true dom_137 roots_137 goal_137 4 :=
  lower_iso isoMvS_137 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_82

def isoMvS_164 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_164 : Lower true dom_164 roots_164 goal_164 4 :=
  lower_iso isoMvS_164 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_82

namespace S_27
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (2, 18), (3, 11), (3, 19), (8, 9), (10, 11), (10, 26), (16, 17), (16, 18), (24, 25), (24, 26)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 8, 10, 10, 16, 16, 24, 24]
def r2sG : List Nat := [9, 17, 18, 11, 19, 9, 11, 26, 17, 18, 25, 26]
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_27.map (· &&& dom_27)
def goalM : Nat := goal_27 &&& dom_27
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x9d277db1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000a0a0a0a
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
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_27 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_27 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_27 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_27 == dom_27) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_27 goalM v ys) : RunD true dom_27 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_27 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 1 3 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_27 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_27 roots_27 goal_27 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_27 goal_27 := by
    have h0 : isConstB dom_27 goal_27 = false := by decide +kernel
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

end S_27

theorem lowS_27 : Lower true dom_27 roots_27 goal_27 4 := S_27.noCircuit

theorem lowS_83 : Lower true dom_83 roots_83 goal_83 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xa000a00000000000a000a, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_82

def isoMvS_54 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_54 : Lower true dom_54 roots_54 goal_54 4 :=
  lower_iso isoMvS_54 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27

def isoMvS_86 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_86 : Lower true dom_86 roots_86 goal_86 5 :=
  lower_iso isoMvS_86 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_89 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_89 : Lower true dom_89 roots_89 goal_89 4 :=
  lower_iso isoMvS_89 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27

def isoMvS_114 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_114 : Lower true dom_114 roots_114 goal_114 5 :=
  lower_iso isoMvS_114 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_141 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_141 : Lower true dom_141 roots_141 goal_141 5 :=
  lower_iso isoMvS_141 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_147 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem lowS_147 : Lower true dom_147 roots_147 goal_147 4 :=
  lower_iso isoMvS_147 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27

def isoMvS_153 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_153 : Lower true dom_153 roots_153 goal_153 5 :=
  lower_iso isoMvS_153 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_163 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_163 : Lower true dom_163 roots_163 goal_163 4 :=
  lower_iso isoMvS_163 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27

def isoMvS_165 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_165 : Lower true dom_165 roots_165 goal_165 5 :=
  lower_iso isoMvS_165 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_169 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_169 : Lower true dom_169 roots_169 goal_169 5 :=
  lower_iso isoMvS_169 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_172 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_172 : Lower true dom_172 roots_172 goal_172 5 :=
  lower_iso isoMvS_172 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83

def isoMvS_177 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_177 : Lower true dom_177 roots_177 goal_177 4 :=
  lower_iso isoMvS_177 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27

def isoMvS_178 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_178 : Lower true dom_178 roots_178 goal_178 4 :=
  lower_iso isoMvS_178 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27

def isoMvS_209 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_209 : Lower true dom_209 roots_209 goal_209 4 :=
  lower_iso isoMvS_209 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27

theorem lowS_55 : Lower true dom_55 roots_55 goal_55 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa00aa00aa, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_54

theorem lowS_87 : Lower true dom_87 roots_87 goal_87 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa0000000000aa00aa, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_86

namespace S_91
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (2, 18), (2, 66), (3, 11), (3, 19), (3, 67), (8, 9), (10, 11), (10, 26), (10, 74), (16, 17), (16, 18), (16, 80), (24, 25), (24, 26), (24, 88), (64, 66), (64, 80), (65, 67), (65, 73), (65, 81), (72, 73), (72, 74), (72, 88)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 8, 10, 10, 10, 16, 16, 16, 24, 24, 24, 64, 64, 65, 65, 65, 72, 72, 72]
def r2sG : List Nat := [9, 17, 18, 66, 11, 19, 67, 9, 11, 26, 74, 17, 18, 80, 25, 26, 88, 66, 80, 67, 73, 81, 73, 74, 88]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_91.map (· &&& dom_91)
def goalM : Nat := goal_91 &&& dom_91
def NN : Nat → Nat
  | 4 => 3
  | 5 => 4
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x7355b34551d95ca413e15b69
  | 5, 0 => 0xad39e6e6a517bddc50918ce616a51756
  | 6, 0 => 0x7083f37a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5050500000000000505050000000000000000000000000000000000000000000f030f00000000000f030f0000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000000000000000000f0f0c0c00000000000000000000000000000000000000000f0f0000000000000f0f000000000000000000000000000000000000000000000f000f00000000000f000f0000000000000000000000000000000000000000000c0c0c0c000000000c0c0c0c00000000000000000000000000000000000000000a0a0a0a000000000a0a0a0a
  | 0, 1 => 0xf0f0f0f000000000f0f000000000000000000000000000000000000000000000f0f0f0f000000000c0c0c0c000000000000000000000000000000000000000000000000000000000f0f000000000000000000000000000000000000000000000f0f0f00000000000f0f0f00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x831755361055432105
  | 5, 0, 0 => 0xb321056083105532a10563921056
  | 6, 0, 0 => 0x321055
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 28
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe0ffc0707fe03fc000001ff7c00fc007071e00000ef8380073
  | 0, 1 => 0xfffc007f81df003f001c1ff80
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xc2db027d7be4ffe489000db3692fd137471e45152ef87849f3
  | 0, 1 => 0xffff377feddf001b44df5ffb7
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
  | 3, 0 => 0xf230765254404406
  | 4, 0 => 0xf2307652ec9707c9e6683d14e0fce173d5dcdfd0cf58f6d8ba51fad69a65508886bf3cbd7083f37a577a9a0649d635053c64dd8802d43be6
  | 5, 0 => 0xe774a9ecbb6ab7a5ba51fad6b8926fbb8779ade382cc46c3778c241b7083f37a6a1793e0637edeb8614ad6c85d9072e8586e0e36531df3554b5adcae414702f93f3ad6d12bacd5d12aa75ee71a4cf6df188d6bc4141e2c2a102577140e24be750512b9e5034cd1610230ef3f01eb5c43
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 3, 0 => 0x0
  | 4, 0 => 0x3000101020302000300000003
  | 5, 0 => 0x3030303000300030003030001030300030000030300020103020003
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
  | 1 => checkCutEntry true dom_27 roots_27 4 s ws hint
  | 2 => checkCutEntry true dom_89 roots_89 4 s ws hint
  | 3 => checkCutEntry true dom_83 roots_83 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_91 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_82 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_89 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_91 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_91 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_91 == dom_91) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_91 goalM v ys) : RunD true dom_91 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_91 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_91 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_91 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_91 roots_91 goal_91 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_91 goal_91 := by
    have h0 : isConstB dom_91 goal_91 = false := by decide +kernel
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

end S_91

theorem lowS_91 : Lower true dom_91 roots_91 goal_91 7 := S_91.noCircuit

theorem lowS_118 : Lower true dom_118 roots_118 goal_118 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x500050005000500050005000500050, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_114

namespace S_173
def pairsG : List (Nat × Nat) := [(1, 9), (1, 129), (4, 36), (4, 132), (5, 13), (5, 37), (5, 133), (8, 9), (8, 136), (12, 13), (12, 44), (12, 140), (32, 36), (32, 160), (33, 37), (33, 41), (33, 161), (40, 41), (40, 44), (40, 168), (128, 129), (128, 132), (128, 136), (128, 160)]
def r1sG : List Nat := [1, 1, 4, 4, 5, 5, 5, 8, 8, 12, 12, 12, 32, 32, 33, 33, 33, 40, 40, 40, 128, 128, 128, 128]
def r2sG : List Nat := [9, 129, 36, 132, 13, 37, 133, 9, 136, 13, 44, 140, 36, 160, 37, 41, 161, 41, 44, 168, 129, 132, 136, 160]
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_173.map (· &&& dom_173)
def goalM : Nat := goal_173 &&& dom_173
def NN : Nat → Nat
  | 3 => 1
  | 4 => 4
  | 5 => 10
  | 6 => 4
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x8148d325
  | 4, 0 => 0x46e128243446680a2c0cdf4321a53524
  | 5, 0 => 0x6e5c8f516b9189d142ab77713fbb45682ceec65d229d783a1a749d1c1557acdc08c1e6af08664403
  | 6, 0 => 0x5b030d2f274d32f11588e06111d279d6
  | 7, 0 => 0x5b030d2f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x333300000000000000000000000000003333000000000000000000000000000030300000303000000000000000000000303000003030000000000000000000001100000011110000000000000000000011000000110000000000000000000000333300003333000000000000000000000000000000000000000000000000000033330000333300000000000000000000333300000000000000000000000000003300000033000000000000000000000033000000330000000000000000000000333300003232000000000000000000003030000030300000000000000000000022220000222200000000000000000000222200002222
  | 0, 1 => 0x3333000000000000000000000000000033000000000000000000000033300000333000000000000000000000333000003330000000000000000000003333000033330000000000000000000030300000303000000000000000000000333300003333000000000000000000003300000033000000000000000000000000330000003300000000000000000000000000000000000000000000000000003333000033000000000000000000000000000000000000000000000000000000333300003330000000000000000000003030000030300000000000000000000011110000111100000000000000000000111000001110
  | 0, 2 => 0x111100001111000000000000000000000000000000000000000000000000000033330000333300000000000000000000333300003300000000000000000000003333000022220000000000000000000000000000000000000000000000000000313100003131000000000000000000003030000030300000000000000000000001010000010100000000000000000000000000000000000000000000000000000000000033330000000000000000000000000000303000000000000000000000003300000033000000000000000000000022000000220000000000000000000000000000000000000000000000000000333000003330
  | 0, 3 => 0x33330000330000000000000000000000333300003300
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x188204
  | 4, 0, 0 => 0x188c0529c490114e23208a7118a45
  | 5, 0, 0 => 0xb1c460118e230095638a860118e2300936134c09118073022453c0460118e2301e463b84d0118ec3008b6
  | 6, 0, 0 => 0x1c46011707118046388c025d867118046
  | 7, 0, 0 => 0x7118045
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 24
  | 4 => 29
  | 5 => 34
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xff000000e7cfe0f80f00000fff0000e0f80000e7c01c073
  | 0, 1 => 0xf00f800e0ffcf00e7cfe0f80f00000000000000e7cfe0f8c
  | 0, 2 => 0xf00000ffff80000000f00e7cf00000f00e7cf1c0730e0ffc
  | 0, 3 => 0xfff80
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x8ff424245e7c6c0d08f9294afffd6e4e8f91bd7e7e13c2f3
  | 0, 1 => 0x700bdb6edffdfd7f7effafdbb1204ac92900ed7f7cec3d0c
  | 0, 2 => 0xe82908ffffff992042ec7f7cc82100700b5ab1606a06d6b5
  | 0, 3 => 0xcfffb5
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 24 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 24 (i % 8)
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
  | 4 => 11
  | 5 => 50
  | 6 => 7
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0x648981165b030d2f5afb7dd542ed1bbb37696e6a3170a23c20708a581cd061f60efee4940d3a351104a22949
  | 5, 0 => 0x951031617df7af196f0d26076e47376d6bb382a7694ee71c648981165dffc3795d52ac255b030d2f5471aeef4e7d82024deda3cf4a6f1b02498fd960498ca8e448b6398c424904a53d9f371e3b7d65b22a447008297931f1274d32f122ea3b3b2117add81cd061f61a7615711a32ade81a157b9619301ad71588e0611444e0de12d45cd811d279d6114580570ed3ba550d3a35110c14b4980b10ddb7071a4d0a070f06bc06839b31067827f905c70ac105b48a380259849102571193020f9e3901dd67470147be46
  | 6, 0 => 0x4e7d82024a6f1b023d9f371e297931f12117add8070f06bc067827f9
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x301020200000103010001
  | 5, 0 => 0x4050002040301000104030300000503030301050403050103010202000101050001050004020403030402010204030403
  | 6, 0 => 0x3000304010305
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 7 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 1
  | 5 => 3
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x4977f5f7
  | 5, 0 => 0x240eeaef23b1e97b04d0b01a
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0xc7101
  | 5, 0 => 0x51011244104e100
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 3 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_141 roots_141 5 s ws hint
  | 1 => checkCutEntry true dom_172 roots_172 5 s ws hint
  | 2 => checkCutEntry true dom_164 roots_164 4 s ws hint
  | 3 => checkCutEntry true dom_165 roots_165 5 s ws hint
  | 4 => checkCutEntry true dom_169 roots_169 5 s ws hint
  | 5 => checkCutEntry true dom_137 roots_137 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_173 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_141 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_172 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_164 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_165 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_169 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_137 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_173 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_173 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_173 == dom_173) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_173 goalM v ys) : RunD true dom_173 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_173 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 4 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 10 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 10 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 4 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 4 0 = true)
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
  scr true dom_173 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_173 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_173 roots_173 goal_173 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_173 goal_173 := by
    have h0 : isConstB dom_173 goal_173 = false := by decide +kernel
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

end S_173

theorem lowS_173 : Lower true dom_173 roots_173 goal_173 8 := S_173.noCircuit

namespace S_179
def pairsG : List (Nat × Nat) := [(1, 17), (1, 129), (2, 18), (2, 34), (3, 19), (3, 35), (3, 131), (16, 17), (16, 18), (32, 34), (32, 160), (33, 35), (33, 49), (33, 161), (48, 49), (48, 50), (48, 176), (128, 129), (128, 160), (130, 131), (130, 146), (130, 162), (144, 145), (144, 146), (144, 176)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 16, 16, 32, 32, 33, 33, 33, 48, 48, 48, 128, 128, 130, 130, 130, 144, 144, 144]
def r2sG : List Nat := [17, 129, 18, 34, 19, 35, 131, 17, 18, 34, 160, 35, 49, 161, 49, 50, 176, 129, 160, 131, 146, 162, 145, 146, 176]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_179.map (· &&& dom_179)
def goalM : Nat := goal_179 &&& dom_179
def NN : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x2138728b
  | 5, 0 => 0xdd81d4378741933c13adeec6
  | 6, 0 => 0xdd81d437
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000a000f000a0000000000000000000f000a000f000a0000000000000000000f000f000a000a0000000000000000000f000f000a000a0000000000000000000f000f000000000000000000000000000f000f000000000000000000000000000f0000000f00000000000000000000000f0000000f00000000000000000000000c000c000c000c0000000000000000000c000c000c000c0000000000000000000a000a000a000a0000000000000000000a000a000a000a000000000000000000000000000f000f000000000000000000000000000c000c0000000000000000000f000f000f000f00000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x46885
  | 5, 0, 0 => 0x58d05be341b58d06
  | 6, 0, 0 => 0x58d05
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 19
  | 5 => 22
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe0fcf9807f9cc03fc01c1c1801c003e000e1cffc00f9fe0000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xedfcfbdbffbee4bfc51d1d1955c45be129e3cdb402adff2442
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
  | 5 => 7
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0xdd81d43771fa42241ef5fb0906c789e8
  | 5, 0 => 0x58965053480ff99c405d3dd538bf240a2c6b74e4219ac4031a8b432d
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x20102
  | 5, 0 => 0x3020001020001
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
  | 0 => checkCutEntry true dom_178 roots_178 4 s ws hint
  | 1 => checkCutEntry true dom_147 roots_147 4 s ws hint
  | 2 => checkCutEntry true dom_177 roots_177 4 s ws hint
  | 3 => checkCutEntry true dom_163 roots_163 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_179 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_178 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_177 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_163 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_179 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_179 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff0000ffff0000ffff0000ffff0000, 112), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xffffffff00000000ffffffff00000000, 96), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xcccccccccccccccccccccccccccccccc, 126), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_179 == dom_179) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_179 goalM v ys) : RunD true dom_179 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_179 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_179 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_179 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_179 roots_179 goal_179 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_179 goal_179 := by
    have h0 : isConstB dom_179 goal_179 = false := by decide +kernel
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

end S_179

theorem lowS_179 : Lower true dom_179 roots_179 goal_179 7 := S_179.noCircuit

theorem lowS_203 : Lower true dom_203 roots_203 goal_203 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0000000000000c0c0000000000000c0c0000000000000c0c, 64, 66), (0xf0f00000000000000000000000000000f0f0000000000000000, 2, 66)] (by decide +kernel) (by decide +kernel) lowS_137

def isoMvS_59 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_59 : Lower true dom_59 roots_59 goal_59 5 :=
  lower_iso isoMvS_59 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_151 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]
theorem lowS_151 : Lower true dom_151 roots_151 goal_151 5 :=
  lower_iso isoMvS_151 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55

def isoMvS_155 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_155 : Lower true dom_155 roots_155 goal_155 7 :=
  lower_iso isoMvS_155 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_167 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_167 : Lower true dom_167 roots_167 goal_167 6 :=
  lower_iso isoMvS_167 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_87

def isoMvS_181 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_181 : Lower true dom_181 roots_181 goal_181 7 :=
  lower_iso isoMvS_181 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_182 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_182 : Lower true dom_182 roots_182 goal_182 7 :=
  lower_iso isoMvS_182 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_211 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem lowS_211 : Lower true dom_211 roots_211 goal_211 7 :=
  lower_iso isoMvS_211 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_214 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_214 : Lower true dom_214 roots_214 goal_214 7 :=
  lower_iso isoMvS_214 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_217 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffffffff00000000ffffffff00000000, 96), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_217 : Lower true dom_217 roots_217 goal_217 7 :=
  lower_iso isoMvS_217 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_218 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_218 : Lower true dom_218 roots_218 goal_218 6 :=
  lower_iso isoMvS_218 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203

def isoMvS_230 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_230 : Lower true dom_230 roots_230 goal_230 6 :=
  lower_iso isoMvS_230 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_118

def isoMvS_242 : List (Nat × Nat) := [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_242 : Lower true dom_242 roots_242 goal_242 7 :=
  lower_iso isoMvS_242 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

def isoMvS_244 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem lowS_244 : Lower true dom_244 roots_244 goal_244 7 :=
  lower_iso isoMvS_244 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (2, 18), (2, 34), (3, 11), (3, 19), (3, 35), (4, 36), (5, 13), (5, 21), (5, 37), (6, 22), (6, 38), (7, 15), (7, 23), (7, 39), (8, 9), (10, 11), (10, 26), (10, 42), (12, 13), (12, 44), (14, 15), (14, 30), (14, 46), (16, 17), (16, 18), (20, 21), (20, 22), (20, 52), (24, 25), (24, 26), (28, 29), (28, 30), (28, 60), (32, 34), (32, 36), (33, 35), (33, 37), (33, 41), (33, 49), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 4, 5, 5, 5, 6, 6, 7, 7, 7, 8, 10, 10, 10, 12, 12, 14, 14, 14, 16, 16, 20, 20, 20, 24, 24, 28, 28, 28, 32, 32, 33, 33, 33, 33, 40, 40, 40, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [9, 17, 18, 34, 11, 19, 35, 36, 13, 21, 37, 22, 38, 15, 23, 39, 9, 11, 26, 42, 13, 44, 15, 30, 46, 17, 18, 21, 22, 52, 25, 26, 29, 30, 60, 34, 36, 35, 37, 41, 49, 41, 42, 44, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x90600b51
  | 6, 0 => 0x69904ec9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x2c6886
  | 6, 0, 0 => 0x2c7886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x739f0ff80fffe000000003f007fe000000e381f07fc0000000739fefffc00000073be1f001e00000e773
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2485739f0ff80ffff084a25323f107fe844a26e3a1f07fc84476c7fbdfefffc490aa573be1f093e14a53e773
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
  | 4, 0 => 0x6c9c7229
  | 5, 0 => 0xaca10b9495c9546a780ed73269904ec9
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x0
  | 5, 0 => 0x10201
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
  | 1 => checkCutEntry true dom_59 roots_59 5 s ws hint
  | 2 => checkCutEntry true dom_55 roots_55 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_63 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_54 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 12 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_63 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_63 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_63 == dom_63) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_63 goalM v ys) : RunD true dom_63 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_63 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_63 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_63 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_63 roots_63 goal_63 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_63 goal_63 := by
    have h0 : isConstB dom_63 goal_63 = false := by decide +kernel
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

end S_63

theorem lowS_63 : Lower true dom_63 roots_63 goal_63 7 := S_63.noCircuit

theorem lowS_95 : Lower true dom_95 roots_95 goal_95 8 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f000000000f0f0f0f0, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_91

theorem lowS_119 : Lower true dom_119 roots_119 goal_119 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaa00aa00aa00aa00aa00aa00aa00aa, 16, 17)] (by decide +kernel) (by decide +kernel) lowS_118

theorem lowS_175 : Lower true dom_175 roots_175 goal_175 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc00000000000000000000cccc0000cccc, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_173

namespace S_183
def pairsG : List (Nat × Nat) := [(1, 17), (1, 129), (2, 18), (2, 34), (3, 19), (3, 35), (3, 131), (4, 36), (4, 132), (5, 21), (5, 37), (5, 133), (6, 22), (6, 38), (6, 134), (7, 23), (7, 39), (7, 135), (16, 17), (16, 18), (20, 21), (20, 22), (20, 52), (20, 148), (32, 34), (32, 36), (32, 160), (33, 35), (33, 37), (33, 49), (33, 161), (48, 49), (48, 50), (48, 52), (48, 176), (128, 129), (128, 132), (128, 160), (130, 131), (130, 134), (130, 146), (130, 162), (144, 145), (144, 146), (144, 148), (144, 176)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 16, 16, 20, 20, 20, 20, 32, 32, 32, 33, 33, 33, 33, 48, 48, 48, 48, 128, 128, 128, 130, 130, 130, 130, 144, 144, 144, 144]
def r2sG : List Nat := [17, 129, 18, 34, 19, 35, 131, 36, 132, 21, 37, 133, 22, 38, 134, 23, 39, 135, 17, 18, 21, 22, 52, 148, 34, 36, 160, 35, 37, 49, 161, 49, 50, 52, 176, 129, 132, 160, 131, 134, 146, 162, 145, 146, 148, 176]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_183.map (· &&& dom_183)
def goalM : Nat := goal_183 &&& dom_183
def NN : Nat → Nat
  | 4 => 3
  | 5 => 8
  | 6 => 18
  | 7 => 5
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xed21cdae8980383873db29b8
  | 5, 0 => 0xa9ff4b379670f44b7e6ecb547934f69e316662e6290259d2103657e10bec9244
  | 6, 0 => 0xba553ea1a10495e79e4010599341de4a7e6ecb547b1128587955ef436605fc9e57aefc2d465a7960432f03e43a09f5332bbea29f2a957f8e26f1f42620488300202702c404a967be
  | 7, 0 => 0xed4c8586a10495e7504bec4248cdc98341dd59d4
  | 8, 0 => 0x1ac9f97d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff00ff00ff00000000000000000000000000000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00000000000000000000000000000000000f000f0000000000000000000f000f0000000000000000000000000000000000ff00ff000000000000000000ff00ff00000000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000cc00cc00cc00cc000000000000000000cc00cc00cc00cc000000000000000000aa00aa00aa00aa000000000000000000aa00aa00aa00aa0000000000000000000f000f000f000f0000000000000000000f000f00000000
  | 0, 1 => 0xff000000ff0000000000000000000000ff00000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00ff00f000f0000000000000000000f000f000f000f000000000000000000055000000550055000000000000000000550000005500000000000000000000005500550055005500000000000000000055005500550000000000000000000000f000f000f000f0000000000000000000f000f000f000f0000000000000000000ff00ff00000000000000000000000000ff00ff000000000000000000000000000f000f000f000f0000000000000000000f000f000f0000
  | 0, 2 => 0xff00ff00000000000000000000000000ff0000000000000000000000ff00ff00cc00cc000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000ff00ff00ff00ff0000000000000000000000ff00000000000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff0000000000000000000000ff000000ff0000000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff0000000000000000000000ff000000ff0000
  | 0, 3 => 0xff000000000000000000000000000000ff00000000000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff0000000000000000000000ff00ff00ff00ff000000000000000000ff000000ff00000000000000000000005500550055005500000000000000000055000000550000000000000000000000aa00ff00aa00aa000000000000000000aa00ff00aa00aa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x1862095483104aa4188205
  | 5, 0, 0 => 0x30c410398c41a841648c4101d8061b441548d4261d9235096760106a105523105076
  | 6, 0, 0 => 0xda74a104ee048d42c9d809188203b012350b07648d420dcee048d5609d8151a841a300c35082e648d420ccef248d4209dc09828413b45235082774c06a104ee91a84179dc091b4413b1923104077
  | 6, 0, 1 => 0x13a1a8593b9923508277
  | 7, 0, 0 => 0x246a104ee73246a104ee91a841e1dd351a8413ba743508277
  | 8, 0, 0 => 0x123508276
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
  | 0, 0 => 0xffe000000003fffff000000fffffc000003fffff000000f01e03f000003c00003f07c0001e00e39cffffff000000
  | 0, 1 => 0xfe1fc00000000000000000000003cffe03fff80fc0000fffe1ff0000000000f3ff80001ffc000003fffff0c0000
  | 0, 2 => 0xffe003f000003c00003f07c001ffc000003ff800000000ffe1fc000003ffffffc0000f01ffff00003c0780fc0000
  | 0, 3 => 0x7f000000f01ffff00003fff80fc0000fffe03f000000007f038e73
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfff11209250bfffffc36dea3526a40001a9ddbbbc36deaf41e83f24854bc1092bf07c1123e05e39cef6ded00006a
  | 0, 1 => 0xbe17c0db7aa22444000000cad95bcffe0399700e85104eedc1fa1c63109212f3ff80889ffd0492a2f6ded0c007f
  | 0, 2 => 0x776002fb6d5ebe54d2bf07c000eed0492a1dd800824942fff17e0db7abffffffffffff41eeff6daf7f27e4fc9215
  | 0, 3 => 0x2205f0124a8fc9ffff6daf7fffe4fedb57eedc13a14410668ff17aefb
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
  | 5, 0 => 0xef2cf17de2b8e3ea94f31e1f91967c8190c816dc8ec2ecc2838a28c9574f2282515e1ec34bb782a746a6e7da465a79603e3a27e72bbea29f1ecea7cc1de39d771ac9f97d08da61ca064a3321
  | 6, 0 => 0xd5ab2145ce159ec7c182bb9ebbafd00cb7fe2b099bb5961e9b7fb52b993fd9b6966345428b9725b785733133838a28c9821b30647fdc69e57d4e81eb7848f8c96cd332f2690e958e66237f14653796f964610986636237aa606ae8805e2cf70e5d95aad85be86f845b3a6ca4556b6cc9504bec4248cdc98346274cd24558f0b241dd59d439cc7d7a388888a737ba23022f1516e62a546dad29bb55b826ee7d362520ed6923f44a191de39d771ca4c4a41bb8fe631ac9f97d13cc6a9c126bfb49122900581199c4870f832c030e51bfb50e2709f30a339f6009f4a98209c0c88f09a233f0095170c5088bd3d80771be050527fb0902dbf26401e4952b019674b1
  | 6, 1 => 0xfe412ea8f2a98ecded4c8586d7669abe
  | 7, 0 => 0xd1fa1330ce5a8fc7c698efd9aefb600aa6c9d5afa222f7759ed0d38a857331338453fbd16d160bf160b4a3f45e0e488947f0c6cd3fadd66439645a94361f430f361a396233995424326a5dff2eed78792bb8403f281dccb626d92a0220b11f891ac9f97d1a0fe42f191d19760f7747770ae7073609c0c88f
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x20402020200020202030202020201010102
  | 6, 0 => 0x202020505050500010002000004050005010503010105050005050001020501050204050504020205000001030101000101030500040304010105050204010205000202
  | 7, 0 => 0x10101000101010504000001000401040001040401000404010001000105
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 3
  | 5 => 7
  | 6 => 53
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0x78f6872d726ce7ca55ba86a7
  | 5, 0 => 0xc7461601af1aa8ac949f15717a4653fc0dd250d007d3ce2d025bba75
  | 6, 0 => 0xcc2cee8ec44b676fbb5cac45b660d0c1aec5da53a94dc69ba31f3eb59d0511d898c3b22693179d9d8f4d09878b502efe88327da8881af6c4862b0cfb836b4d12810b296e7c9111207ae18efa7a528ea4790d1fda78615f9572b3e9cb6e3822276ac044bb5a058f375113c1054e96f0f64bf88298490a3da045eff2ff44f6fdce44c57be243768a873b9121973b575647399c761336c7160635ea50d92a936d8c25e02cca1c185203197d4f2214e0575411abb9090d0da2e30be67e8009c4c533071e70dd051a8fa30460d730013f28c200b971fb
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x197344d0300564d2438c0000344d0200
  | 5, 0 => 0x344d0200000d134080000344d0201000c924480400000c7105000d134080000344d0200
  | 6, 0 => 0x238404000010e1000000034040000000d210400000244410000008e10400000348410000008d10100000438400000009110000000244404000010c1040000034440400000d01010000024440000000911040000024440400000d21000000034840000000911010000024841000000d110000000434404000009110100000344400000008e10400000344400000008d10000000244410000010e1040000023840000000d1100
  | 6, 1 => 0xd110100000248410000008d1040000034840400000d010000000340400000008d1040000034440000000d11040000023840400000d210400000234410000010e10100000234404000008e10000000238410000008e10400000238404000010c10400000244410000008d100
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_179 roots_179 7 s ws hint
  | 1 => checkCutEntry true dom_182 roots_182 7 s ws hint
  | 2 => checkCutEntry true dom_151 roots_151 5 s ws hint
  | 3 => checkCutEntry true dom_55 roots_55 5 s ws hint
  | 4 => checkCutEntry true dom_181 roots_181 7 s ws hint
  | 5 => checkCutEntry true dom_167 roots_167 6 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_183 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_179 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_182 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_151 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_181 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_167 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_183 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_183 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_183 == dom_183) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_183 goalM v ys) : RunD true dom_183 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_183 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_183 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_183 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_183 roots_183 goal_183 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_183 goal_183 := by
    have h0 : isConstB dom_183 goal_183 = false := by decide +kernel
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

end S_183

theorem lowS_183 : Lower true dom_183 roots_183 goal_183 9 := S_183.noCircuit

namespace S_219
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (1, 129), (2, 18), (2, 66), (3, 11), (3, 19), (3, 67), (3, 131), (8, 9), (8, 136), (10, 11), (10, 26), (10, 74), (10, 138), (16, 17), (16, 18), (16, 80), (24, 25), (24, 26), (24, 88), (24, 152), (64, 66), (64, 80), (65, 67), (65, 73), (65, 81), (65, 193), (72, 73), (72, 74), (72, 88), (72, 200), (128, 129), (128, 136), (130, 131), (130, 138), (130, 146), (130, 194), (144, 145), (144, 146), (144, 152), (144, 208), (192, 193), (192, 194), (192, 200), (192, 208)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 3, 8, 8, 10, 10, 10, 10, 16, 16, 16, 24, 24, 24, 24, 64, 64, 65, 65, 65, 65, 72, 72, 72, 72, 128, 128, 130, 130, 130, 130, 144, 144, 144, 144, 192, 192, 192, 192]
def r2sG : List Nat := [9, 17, 129, 18, 66, 11, 19, 67, 131, 9, 136, 11, 26, 74, 138, 17, 18, 80, 25, 26, 88, 152, 66, 80, 67, 73, 81, 193, 73, 74, 88, 200, 129, 136, 131, 138, 146, 194, 145, 146, 152, 208, 193, 194, 200, 208]
def mpG : Nat := 0x3fffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_219.map (· &&& dom_219)
def goalM : Nat := goal_219 &&& dom_219
def NN : Nat → Nat
  | 4 => 1
  | 5 => 18
  | 6 => 74
  | 7 => 51
  | 8 => 10
  | 9 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x89049fc9
  | 5, 0 => 0x968570356440affd5047e64b3edf557a3b1296f3333adf9a1cd857d41b2aa3d11a84460515c8364a0d84b49d09f8e03a09cb19500517bfd204a7feea03d71d56026fc30300e7453f
  | 6, 0 => 0x5b4cdb485a488f8e577f2b6f51bd846a4b05ec3044c03f8842a453d442664157414fb92239e056da3556dda232f56f4a30095c8b2ed8a0e92eccc0932a46623c299b5df52940972f28da01b727fb4666264af005251e99a324693a752468e29e241a1285232f653d20f6f7851ffdf8eb1f5bfd9a1c099ab0191f28f31847f1731696597f168a680c15bf489614a7d5d3149333d8145764cd133ee65912a9eb07110cb02c10c182070f5a25b50f24e7d00d931f920c960bf30bfd28220b28ad720b214c160a9b4e83090878b4079a8f1d06d9b3d106043d5a0585b743056c51c504e2c61503ac9368034c8c520243c16501a738ce011fb19c00738df500697906
  | 6, 1 => 0xd8f6dfea8f1a72198db07d578d01547b8840bd6b709214816b80ee266ad2d97d6871267465e04c91
  | 7, 0 => 0xd60407c5ad45052aa952ff8ea27711fd8ce5e7e07aed7f2d6e3a13f56d59c33f69adfc6a5e26dd1c56eeba654fefa0d64fe711c34ec7ac834ade29264640dd424409de5a43298da442802b9d420dd94240bb1b283c2e4cbc39df039d3303160c31ea0ae12ee433c22c207cb12b4744a82afd058d2ab87a93264591ed2149652c1dbb46d717add2f8179b7ba9166547480fe945c60e1b11690cffeec60bce65dc0a14810908e1433208da65b40825242f0784100e075b064804ec7fd60481e15802e5df900297690300a8227d
  | 8, 0 => 0xe384d8318e86f0dd7aed7f2d6ded075656c2ff5430832f4d1dd4337a0fb6534509c8c1320084c352
  | 9, 0 => 0x8e86f0dd
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a00000000000f000f00000000000f000f00000000000f000f00000000000e000e000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f0f0a0a000000000f000f00000000000f000f00000000000f000f00000000000f000f00000000000e0e0e0e000000000e0e0e0e000000000e0e0000000000000e0e0000000000000f0f0f0f000000000f0f0f0f000000000c0c0c0c000000000c0c0c0c000000000f0f0f0f0000000000000000000000000f0f0f0f0000000000000000
  | 0, 1 => 0xf0f0f0f000000000f0f0f0f000000000f0f0000000000000f0f0000000000000f0c0f0c000000000f0c0f0c000000000f0c0f0c000000000f0c0f0c000000000c0c0c0c000000000c0c0000000000000c0c0c0c000000000c0c000000000000000f000f00000000000f000f00000000000a000a00000000000a000a00000000000000000000000000000000000000000f0b0f0a000000000f0b0f0a0000000000000f0f0000000000000c0e0000000000000f0f0000000000000c0e000000000f0f0000000000000f0f0000000000000f0f0000000000000f0f0000000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c
  | 0, 2 => 0x3030303000000000202020200000000030303030000000002020202000000000f0f0f0f000000000f0f0f0f0000000000000000000000000f0f000000000000000f000f00000000000f000f000000000000000e000000000000000e00000000000f000f00000000000f000f00000000000f000e00000000000f000e000000000f000f00000000000f000f00000000000a000a00000000000a000a0000000000050505050000000005050505000000000505000000000000050500000000000005050505000000000505050500000000050505050000000005050500000000000f0f0f00000000000f0f0f00000000000f0f0f00000000000f0f0f00
  | 0, 3 => 0xf0f0f0f000000000a0a0a0a000000000f0f0f0f000000000a0a0a0a000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000000000000000000000000000000000000f0f0a0a0000000000000000000000000f0f0a0a0000000000000f0f0000000000000a0a0000000000000f0f0000000000000a0a0000000000000000000000000f0f0c0c0000000000000000000000000f0f0c0c0000000000000000000000000f0f0e0e0000000000000000000000000f0f0e0e000000000c0c0c0c000000000e0e0e0e000000000c0c0c0c000000000e0e0e0e0000000000000000000000000e0e0e0e0000000000000000000000000e0e0e0e
  | 0, 4 => 0xf0f00000000000000000000000000000f0f0a0a000000000f0f0f0f0000000000000000000000000f0f0f0f000000000f0c0f0c000000000d0d0d0d000000000d0d0d0d000000000d0d0c0c000000000d0d0c0c0000000000000c0c0000000000000e0e0000000000000c0c0000000000000e0e000000000f0f0f0f00000000000f000a000000000f0f0f0f00000000000f000a0000000005050505000000000505050500000000010100000000000001010000000000000f0f0f0f000000000f000f00000000000f0f0f0f000000000f000f00000000000f0f0f0f000000000a0a0a0a000000000f0f0000000000000a0a0000
  | 0, 5 => 0xe0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e0e000000000e0e0e00000000000e0e0e00000000000e0e0e00000000000e0e0e00000000000f0f0f0f000000000e0e0e0e000000000f0f0f0f000000000e0e0e0e0000000000000f0f0000000000000e0e0000000000000f0f0000000000000e0e00000000000000000000000000000000000000000f0f0f0a000000000f0f0f0a0000000000000000000000000f0f0f0f0000000000000000000000000e0e0e0e00000000000f000f00000000000f000f00000000000f000f00000000000a000a000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000e0e0e0e
  | 0, 6 => 0xf0f0a0a000000000f0f0a0a000000000000000000000000000000000000000000000000000000000f0f0f000000000005040504000000000504050400000000050405040000000005040504000000000f0f0f0f000000000f0f0f0f000000000a0a0a0a000000000a0a0a0a000000000f0f0c0c0000000000000000000000000f0f0c0c0000000000000000000000000f0f0f0f000000000f0f0f0f000000000e0e0e0e000000000e0e0e0e00000000000f000f00000000000f000f00000000000e000e00000000000e000e00000000030b000a00000000030b000a00000000030b000a00000000030b000a
  | 0, 7 => 0xe000000000000000e000000000000000e000000000000000e000000000f0f0f0f000000000f0f0f0f000000000f0f0c0c000000000f0f0c0c000000000f0f0f0f000000000f0f0f0f000000000f000f00000000000f000f0000000000000000000000000000000000000000000f0f0f0f000000000f0c0f0c000000000303030300000000030303030000000003030202000000000303020200000000050505040000000005050504000000000505050400000000050505040000000000000000000000000f0f0f0f0000000000000000000000000c0c0c0c000000000f0f0f0f000000000f0f0f0f000000000f0f0a0a000000000f0f0a0a
  | 0, 8 => 0xf0f0f0f000000000f0f0f0f000000000f0f0f00000000000f0f0f0000000000000000000000000000000000000000000f0f0f00000000000f0f0f00000000000f0f0f0f000000000f0f0f0f0000000000000000000000000f0f0f000000000005050a0a0000000005050a0a0000000005050a0a0000000005050a0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0a000000000f0a0f0a00000000000000000000000000000000000000000f000f00000000000f0f0f0000000000000a000a00000000000a000a00000000000a000a00000000000a000a000000000f0f0504000000000f0f0504000000000f0f0504000000000f0f0504
  | 0, 9 => 0xf0f000f000000000f0f000a000000000f0f000f000000000f0f000a0000000000000000000000000f0f0f0f0000000000000000000000000f0f000000000000000000000000000000000000000000000e0e0e0e000000000e0e0e0e0000000000000000000000000f0f0f0f0000000000000000000000000f0f0c0c0000000005050500000000000505050000000000050505000000000005050500000000000f0f0f0f000000000c0c0c0c000000000f0f0f0f000000000e0e0e0e000000000f0f0f0e000000000f0f0f0e000000000f0f0f0e000000000f0f0f0e000000000d0d0d0d000000000d0c0d0c000000000d0d0d0d000000000d0c0d0c
  | 0, 10 => 0xf0f0f0a000000000f0f0f0a000000000f0f0f0a000000000f0f0f0a000000000a0a0a0a000000000f0f0f0f000000000a0a0a0a000000000e0e0e0e000000000f0f0f0f000000000f0f0f0f000000000303030300000000020202020000000005050505000000000505050500000000050505000000000005050500000000000f0f0f0f0000000002020202000000000f0f0f0f00000000020202020000000003030000000000000303000000000000030300000000000003030000000000000f0f0f0f000000000f0a0f0a000000000f0f0f0f000000000f0a0f0a00000000000f000f00000000000a000a00000000000f000f00000000000a000a
  | 0, 11 => 0xf0a0f0a000000000f0a0f0a000000000f0f0f0a000000000f0f0f0a000000000f000f00000000000f000f00000000000f0f0f00000000000f0f0f00000000000f0f0c0c000000000f0f0c0c000000000f0f0e0e000000000f0f0e0e000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0c0f0c0000000000000f0f0000000000000f0f0000000000000f0c0000000000000f0c000000000f0a0f0a000000000f0a0f0a000000000000000000000000000000000000000000000000000000000f0f0f0c0000000000000000000000000f0f0f0c00000000000000000000000000000000000000000f0f0f0f000000000e0e0e0e
  | 0, 12 => 0xf0f0c0c000000000f0f0c0c000000000f0f0c0c000000000f0f0c0c000000000f0f000a000000000f0f000a000000000f0f000a000000000f0f000a000000000f0f0f0f000000000f0f0f0f000000000f0c0f0c000000000f0c0f0c00000000000e000e00000000000e000e00000000000e000e00000000000e000e00000000000f000f00000000000f000f00000000000f000a00000000000f000a0000000000030002000000000003000200000000000300020000000000030002000000000f0f0e0e000000000f0f0e0e000000000f0f0e0e000000000f0f0e0e0000000000000e0e0000000000000e0e0000000000000e0e0000000000000e0e
  | 0, 13 => 0x2020202000000000202020200000000020202020000000002020202000000000f0f0f0c000000000f0f0f0c000000000f0f0f0c000000000f0f0f0c0000000003030202000000000303020200000000030302020000000003030202000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000c0c0c0c000000000f0f0f0f00000000000a000a000000000f0f0f0f00000000000a000a000000000f0f0f0f000000000f0f0f0f00000000000f000000000000000f000000000000000f000f00000000000f000f00000000000f000f00000000000000000000000000000000000000000a0a0a0a0000000000000000000000000a0a0a0a
  | 0, 14 => 0xa0a0000000000000a0a0000000000000a0a0000000000000a0a0000000000000f0f0f0f000000000c0c0c0c000000000f0f0f0f000000000c0c0c0c000000000f0f0f0f0000000000000a0a000000000f0f0f0f0000000000000a0a000000000e0e0c0c000000000e0e0c0c000000000e0e0c0c000000000e0e0c0c00000000050500000000000005050000000000000505000000000000050500000000000000000a0a0000000000000a0a0000000000000a0a0000000000000a0a000000000f0f0000000000000f0f0a0a000000000f0f0000000000000f0f0a0a00000000000000000000000000000000000000000f0a0f0a000000000f0a0f0a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x406080805
  | 5, 0, 0 => 0x80c4200015820f0620f9e63a0c40738158d89101c605634241990e158483301cb8561258407260184880e540056122039400158789104c9006120c4110015880f1c043806123438c0015848b06203806062038a001584880e180056
  | 5, 0, 1 => 0x120c1010e01848e420439e6
  | 6, 0, 0 => 0x120c4340ecc2b8964203b10015c483101d8000ae4048e5e1c0057120d7080e002b835a203ac0015d584120c40700e241aa101c00571220f8752002b8906a04070015d38906203800ae25303101c0057120d2880e002b8906643a40015c483101d1800ae241880e880057
  | 6, 0, 1 => 0x120c68782002bc0120c4070015c483101df800aef84835e1c00571e241886848039b12f41880e15c4bc06203800ae241880eec0057203d0880e002b8906203ba0015c2091c0d7800ae241af021cf007120c4393e1c2bb86e241880e01db0906203800ae404880ed40057
  | 6, 0, 2 => 0x9e241880e002b8f13381880e79c4839a0440700e0c41f0eb000579824181101c2b892c0c4340e01c80406225800ae241ca101c005792241880e002b8907204070015e3c6120c40700f14483101c0057001018888002b1b130c1880e15c02b120c40700d08483101c0057
  | 6, 0, 3 => 0x82418896002b80b2241880e15821d120c41f0ae241d8101c0057120d7872e002bd756241880e01c483ac203800ae402035e20005712390880e782b897a0c4076615c483101ea800ae00003111000550024188a8002b000824188a61584880f486000ae268880f400057
  | 6, 0, 4 => 0x789101f1800ae241880f880057c20c407c0002b8906bcf970015efde12203800af74483101c005713701880e002b8906203db0015c0101220380b4c74483107c3857
  | 7, 0, 0 => 0x241ec101c005712f41880f48005800241880e5c005700241880fac005700241880fa800577c24181101c005800241880e03485712841af101c005800241af11a0005700241880f9000570002f09101c0056ce26183101c00580198483101c00571394181101c0058003c48310d03807120d7880f900058
  | 7, 0, 1 => 0x1284181101c0058120c407a50400580000188e7c800560184483101c0057c2241af101c005820241880f2c005801c4483101c005700004f00620380600241880fb40057001048311bc0057dc40483101c0058c210483101c005800241880ed4005700247035e1c005708241880fb40058130c1880f480058
  | 7, 0, 2 => 0x120d6af101c005812f41f6101c00580010483101c00570040783101c0057203c483101c005800241880f2c0057120fb08681c00580024703021c005700241880fd4005720241af101c00580000483e81c0056120c41f0e5c00580026883101c00570040203101c00572010483101c005800241883fc80057
  | 7, 0, 3 => 0x20311dc00560824181101c005800241ad101c0057
  | 8, 0, 0 => 0x483101fb800ae00483101c005608241880e002b897a0c4070015c80906203800ae241880f480057ce241880e002b89420c4070015c483101f4000ae241880fc80057
  | 9, 0, 0 => 0x483101c0056
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 39
  | 5 => 46
  | 6 => 53
  | 7 => 60
  | 8 => 53
  | 9 => 46
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3c00079ffff0fc001fffffc000000003c00f3f81e70003c0f1f80003c00000000fffc0001e7e3c00ffc00000
  | 0, 1 => 0xfffc00fe000003cf03c7ff8000000000003fff0f0001e70003fcffff9fc3cffc079ff0f0000fe000003c000079f8
  | 0, 2 => 0xf003ff00001ffff003f8000fffc3c0007fffff0f0381ff000000000003fff003f8000ffffc3fff8003c0f03ffe00
  | 0, 3 => 0xf003ff00079ffffffc000000f0000fe079fc00ffc001e70ff000ffe7e03fc003ff9ff00f00001e7fc03c000079ff
  | 0, 4 => 0xf0000fe079fc00fffc7ff8fffc00ffe7e003c000079ffff03ff0e079ffff003f8000f003fff1f803c0000000000
  | 0, 5 => 0xf03c01e7fc00000007800f0f3ff01e7ffc3cffc079ff0003fcffff9c3ff000079fffffc3f00079ffffffc079ff
  | 0, 6 => 0x3cfe079c000003ffe0000f3c0f1f863fff0f0001e7000000000003fff0f0079fffffc3c0007fc3c00f3f81e7
  | 0, 7 => 0xf03c0007fffff003ff9f8ffffc0f1f800000fffc7ff8ff0c3cfe001c3fcf03ffe180ffc0001e7e3fff0f3f81e7
  | 0, 8 => 0xffffc0fff800000f03ffe00fffc00fff8003c00f3f81e70003fcf1ff9c000f03ffe0000003c00079c3fcf03ffe18
  | 0, 9 => 0xff003ffe079c3ff003f800000003c01e7fc3ff003ff9f80f03c0fff803c3cffc079ff0ff3fcffffffc3cf0fc7ff8
  | 0, 10 => 0xf03fcffff9c3ff0f0079ffffffff00001fffff03ffe00f003ff00001c3c0003f8000f003fff1ff9fc000fc001e7
  | 0, 11 => 0x3fcffff9c000f03ffe000ff03cffe7ffffffffc7ff8f0ffc001ffe0000000000000ff000ffffe0000ffc079ff
  | 0, 12 => 0xff000ffe7e03c00f3f81e7ffffc0f1ffe003c0f0001fffffc3c0e079c3c00f0380070ff03cffe7fc03c0f0079ff
  | 0, 13 => 0x3c00001c3fcf03ffff80f003cfe001ffffffc079f8f003ff00079ffff00038000fffc3f000000000000001e7
  | 0, 14 => 0x3c3cffc079f8f003ff00079c03c000079f80f0000fe00000000f0001e70f0000fe079c000ff3c7fe7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x11147c122f9eef50dc381defffe208114127d55fbf9bef442bc8f1f884cfd0c0dd14efffea5a5f7f3e20ffd22090
  | 0, 1 => 0xffff32ff55399bef37d7ff922c08524c362ef50d0081c60001de7aeb8dc2dbb4069b48f4112fe41288bc214979f8
  | 0, 2 => 0xd9077a5a081ffff882dd54ebbd425000652ef50dc381de442a48913887bbac0bb5408eeeb83edd0633daf6bffe6b
  | 0, 3 => 0xf997ff5aafdfffffff26594075400b66dbdc25bb402bb5077000b765a81dd002ddb6f23f48537effc0dd000ddb6f
  | 0, 4 => 0x74000b669afe20ffdf3af9eefb87edf7e082d21406bb5fbd7ff4e877bbbac0b24400fcabfff9fac7e65cc968146
  | 0, 5 => 0x33f4fd37effc0d8360dfa6bfbf7ff7feffdc2dbb406bb50001de7eebac1df002ddf6fbbd4370a075bfffffffffff
  | 0, 6 => 0x15e7e6bac000000d9a6b66eb81e5d063fff9f24cfe7a88197488243fffbf6dffffbbd43506077a7454db681c6
  | 0, 7 => 0x309425000653fffedfffdfeffffe8f1fc9400077df3af9dd0f7ada181fbbae0fb7418077c00a575b3fffdfbfdfef
  | 0, 8 => 0xfffffafffdbc000769fba6bfffe20b77dbe7955bbb1bad553ffcf3ff9c000721dba6b11143402071bbfae4fff45a
  | 0, 9 => 0xbfd537fe47781df002dd54e0000dd36ebec1df002ddd6ece6b82edd023ebcffdffbfbffffffffffffbbee1fb7df8
  | 0, 10 => 0xdf7ffeffffbc5df1f2ddfefffff7adb1c1fbbae0bb7408f987ff5a8a5e34044b68002fdbffffbffdee650dc281d6
  | 0, 11 => 0x553ffeffffbd10af6bffe6baff1dfffefeffffffff7ffd70beed01bed554f88204504077800b77dac00077dfbafb
  | 0, 12 => 0xaff197ffe7ea7d54dbf91ceffffedf5fff4cf50d4181debbd4360e073a6410c828006bff5ffffeffcc2d3b406bb5
  | 0, 13 => 0x11047812081fbfef7fffffb9d057ada081fffffffb7dfcf997ff4a875bfff8ca3c54ebbd43708065004500048b67
  | 0, 14 => 0x1001012010bebcffdb79f8f897ff48aed48fc254df9fa8e4102ec40204051b000ba58f5512fe6dbc000771cbae3
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 46 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 46 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 120 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 120 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 120 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 120 then wireAt i else 0
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
def CN0 : Nat → Nat
  | 4 => 4
  | 5 => 58
  | 6 => 415
  | 7 => 278
  | 8 => 8
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 4, 0 => 0x476be5bf2b68f9091f7dfccd1954a62b
  | 5, 0 => 0xd60407c5a4e4a9489fe50b8e9158ab6f8e86f0dd87f3569e7ea4e3b67467f00f65ace598654cf547631d02df55b8057a50785ef64e933ed04d20801c48d44cf74239808e3bef5a91369d4d99363da39c346fef46345cd24c33fb19d3311e39cf2a870efc2a7ccc9527b4a5fb2442ab06227a8d27204aa37e19d5f53617e9723917cdee0212c2f7fe12a5e719129a96c4125b85c3114403b01120066d0e9b3e2b0e70f9450cb4b5870c8891f10c7514ff0b5006830ab296d909060e990878022e0819d50507ea01b3071ef09605d8c7f6056eaec205679628049f8cd20388ae58032305220086f878
  | 6, 0 => 0x6d77b4906c5e8c106a34ab906808cc6062a61ef05d51ed6059a672c0590ed280590a288058fca2d056eaec2050a0ac404d3c4ad04c5e01104aa8aa0049dcec8048dc62c047db26b0470d78d0459a117042aa8df04120b660406ddd103ed8e1d03cd9dcc03b5e7d30357fb890345093f031f6e4102f0d65002be03af02a6bb40029a6877027c4cb2027ad5d9027141060242819d02394281020aa64a01a51e5a01700030016c536f01395fef012a55940126c3f90124cc5c0117732e0111b4c6010b5f97010aa70400f2a5d700e9bf1600e0fa4900d3d1cf00aaee07009b5b4f0084c352007f18b7006e1407006a30cc006238210053f1d4002cdc780008e9db
  | 6, 1 => 0xecdfe7d0e95ece30e0e60da0df8fbfa0dca584b0d9c51b10d79345a0d58c3570d55a8960d52a2fa0d3d67830d16529e0d0a772b0cf2f9bb0ceedc4a0cc65ff90cbb63600c7514ff0c3d43330c33c92f0c05562e0bf5d4a70bbb1efe0bb2a3580b94c4490b7944c20b69bf760b66277f0b443e0e0b2b2e400b109c8c0b0a16760aa4adb30a782f620a0e544e09fab44109c8c13209a9281b09999cdc095da143093684980934fc36092ca99d08d709c608b1f4d408afba9a0896b19e08935038088ea1390878d8c90860f9a9085b8dc2085abf59084ed34d07b15afe079ec1a8075a68ab075213f1073cc471072884b70725acc30721f61c071f066706e29c29
  | 6, 2 => 0x1ba69df11b9463351b8fd7e31b6794cc1aeac7da1acb36f31aa42cc91a98b1ca1a62b0681a20dc1719f5e56b1980d8961977296f19508a0918f3301618a16a35189b0fad18870b01184f36d2184ae67017caf8711792f2231776888a176ee61c17667e1b17382ae81703bafa16575cd41606c17014e269d514d3e8e7148324011476e90914671aa913932adc136a3e6f134bbab212e99b3612e7bdaf12d3b6de12c71f8212be5f2f129d6940129a96c412808e2711dffd80119c81e6112e33911114bd4410eed74010987e5e1095d1d5108ee653106be2ba105c964e1009395d0fbca4610fb3c4f90fb3528f0fa16fac0f6ca8000f611f340f497ca20ee11b77
  | 6, 3 => 0x2dbee79a2da03ef42d8258992d4096bf2cefb90d2cedbbc92c5c610d2be5e9412bd13d732b7523692b074bb72ad10bfd2a9ee0d72a870efc2a3e1dc829e45dd429a0505b296ba282293587b92855370327b5823126b4b13526b25dc52670bb9d2643a16a263a35222635fbbb25b527ea25847fba256960e5254ebe6e25448f202534973a24886aca246ca6c72455345d23cb522c2373822c2328fdfe22fb8e7e22d6440a229adfc3228e3234227a8d27221d9af221cef0772149652c2100f4f520dacc6e20906d872035e4e120319b2c1f63a6301e99fc821dd5af7c1d2f1f9f1d02a1f91c9fd8841c6f3d081c5af3391c2905551bf8f5f91bf5477b1bbd8a0e
  | 6, 4 => 0x4424203f439471eb4362131242ee112e429e2e9642802b9d414ca4ff413c576940f8efbc3fdcd3d23fd0b5453f468e913e608c833d54ed533d0f3ccf3cea88443c9aaab73c4adc563bb9ef033b337ea33b2e3ad33b15b1143af574e63ae8362c399dbd423917fbe73908a1df38d26ea03894aed83885ee24384e511437a6a8a336e0a99436030ba035b701ed35a7964635a77dbe3558f57e34d2254d34a814b93467d73b336f791c336d9fcd333e2eb532fc12a1328d4f173252cacb3238d28a3162fb48311e39cf30fc00e530f62ac430d0dab930832f4d303c7d2b2fc70aa32f9662112f61467a2f53ecee2eb68c852e40d8d42e3c35452e2874772e1c4dea
  | 6, 5 => 0x71f8779b7043f8686f0f5ff96efa39666e85d2b96e82c17e6c4c806d6bc2215e6b9717916b23623c6afce6ac6a643df869f37a8e69de6f9969adfc6a6886577067e7e0546356f61b61f26b6c6129027f5c6186665aef55bf5ad676da58526f9356c2ff5456a4b917557c113d553b14985435840253fd9547524645d0520315cc51fa4e45509a48fe50785ef650368459503237b54fd652764fc220de4fab88a64f980e404ec7ac834eb59d664e87f1f54e4c03d34dc632a94d20801c4cd64c584cd06fd94c5ded1f4c402f664c152dae4b1f36c54b0f9cde4a2b98c5483634c547ebbef247b3b4ce46cad12e467da03d464ee6434546806345308c9544797dd9
  | 6, 6 => 0xe384d831da8429e5d60407c5d0cbb737b5b6b7e1b56a1e3e9ffc931b9af1de6c8f69c6cb8e86f0dd8c62d7af8a686006899a981c87f3569e8628943885cfbbcd84c26bcc844b5978837a7b6d7ea4e3b67dc493007d5675f37a38880e783e374677c8f62575f7e7a77524b93774d5c7897459e4ee7359a5ac72f1b777
  | 7, 0 => 0xf6c06ef0ec791100e87ed020e7a2af50d76ca110d55a8960d16529e0c97098f0bbb1efe0b7944c20b2220e70ae10f910ab296d90a9f9fd30a7d39c10a67d87c0a3ac1ca09cbe56509c8c13209a6a271095a480c094150fa091feece08edf8a808c4c89008b51e48086716c70860f9a907d4cd9207b54616076a0b0907676e4006cf822306a34ab9065e6da4063a650d062a61ef061d0bc7061391c305cf13900577a74f04c5e0110409006c03973a420347ca610328638d03240d630320b77902ecd3a1029a6877027db8bb01e01d1401cb8d8b01bfc29b019a3526018a19e401567d2f012a9b940108963000f0ee8b00daf0c000d3d1cf0084c352006a128c
  | 7, 1 => 0x1dd4337a1d37daa11d2f1f9f1ce9bd9d1cc125da1c5dcdbc1bf8be811bd454091b9cf1ac1b6794cc1b3bbfdc1b00255c1a661e1b1a62b0681a00ad0d19f6110d19f5e56b19db171619b98a501915c05718f1fc2f187edf5617f8bb1c17e9723917cae0dc1766808a17667e1b17382b3417382ae816f845e916f576fe16a3d86e1679c6f3166154361657da3215dc5e2e15af932a14fa8bfb14ec38f514b9cd3314b0b35e148ba73b13c03d901338c90d1327f20d131e780912d3b6de129049251242cc1b1237dfcf1208bf1011ec7235119c81e610eed74010d5980c10cf3f3a10c5c53610bcaf2d10ab2312108ee6530fd06bb80fc98adf0fb653450f6d4ed1
  | 7, 2 => 0x3a6075563a29dbe439d5fca039b43ff23939e7ee37a6a8a336f5fc2e36906927362915cd3615ab7835c4d960355e27d234be2b4234a814b9347bef64346af7653438de99329e11bc326248c131bdc10630fc00e530832f4d307a2c2b305714763025383a2f44e7842f3d6ae62ed7d1a22e2874772cedbbc92c0f33282bbeb81e2b7e997c2abe51cc2a8a4e082a40b28e2961fcb728c1a1bc27dcae3927a0ac8a27362e4b26dafcc826c05bd426740082264648ee25c4b4ff256e99d6232b64362328305220dacc6e20a528862076730b2047efee20477cb51fee3f201fbd8eab1f9147671f7da3dc1f2c96e31eb87ccf1eb31d2e1e94130b1df00cd01decb326
  | 7, 3 => 0x75abc49c74ac334472e36deb6f2784e76ded07566dab1d5d6cd036726b9717916b7485a36b6e7976695dda11671119c5631d00c95f5fcdd15d61b0295c08c2615afe3d7d5aef55bf5a5395a659ee557059a8d14b5922bc6e58e4235b58526f9356c2ff54561ace09558153e7557fa341549e38fb546a47f4525c274e52170059520315cc51fa4e4550e2aa874f7c0fd74f65e86d4c3d56074c2d87d74b0e57954ad48fef4a4270d348e1117b48cefbe548c3f08a480185f146c1485c455828dd4495d0c24424203f43f0fc3a432866b24310ab8442d85056420460404188f7ce405ed5ac3f6dd89b3f5d80343f59a9583ec8713b3dd888023d47db0f3af574e6
  | 7, 4 => 0xe384d831dfead9cbd0cbb737cfeb6681c90f87b6befb9f0db6b1f1c8b5b6b7e1b07e6753aa16a72c9fe50b8e9e92ccd19aacbb00995a7c439901b53093921ba28e86f0dd85d729148516b9647b9827047b29bd1976490176
  | 8, 0 => 0x4424203f1b6794cc0d16529e0bbb1efe0860f9a9062a61ef04c5e011029a6877
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 4, 0 => 0x2010305
  | 5, 0 => 0xb0a0802000b040a0a020702090a040a0a010a010a0a08080b020b04000a0b090b0b09080206000a020a0b0b0408040102060c0a070a0a0c0b06
  | 6, 0 => 0xa0208040a02020909000b000a050b07070b0a04080600070b0700020a020b0c0206000a080b0a020a0804040b060b0208070702000b0a0004070b0807040b0b0a080702070702020202070b0a080904070a0b0404040a0200070208090b000b080d0508080a070209090907020a04080200040a020704070b0a0807020a020a
  | 6, 1 => 0x408040a0d070b0802090a02040b0b080b0204040b080a02020b000b08020b02020a090b000a0a080b0b08000b02020800040a0b0c04020a0b02040a04020a0d0002090004020b0409090b0a000202070b0209070a020a0900040408020402050b070409010705000b0d0708020009020a09000a000b020a0a0d08070208020a
  | 6, 2 => 0x40a080b020a02020004040b000b02040b0a020a0b0b0c0009040b04040900080b0a09060704080a090b04020a020409020a04020b020d0b0b080b0107020a0b00090c020a0b09020a04010b0b00020a040b07010b0a0c02000b02000407070002000a0b0205000402020b080b0b020a00080b090a00090b0208020a0a02000b
  | 6, 3 => 0xb0b0b0b04020b0a04000b020a0b0b000b02040404040a0b0a0c040a0b0c04
  | 7, 0 => 0xb0a04070b0802040008010b090b0b0b04070b000907090800000004000a08090a04020b04000b0b000902000a0004020a08040909080a040b0b00040a09040a09090b0109000a00070804080a08070a000807090b0004080809070800020709070000070909080b080b0402080a000b080a08070902000800020a0a070b00
  | 7, 1 => 0x7070809070200070d040200000b020d0b020c000c02000907080a02000a0a080b07000b0a09070d02090b0d04080a0800040b04040d080800080b08090b0c000a0a0004000b09090b040c0704000a08070b070b000b0b00000407000700090208090b0b0808080b040802020b04020700080b0b0709000a0a02000407070b
  | 7, 2 => 0xb020b0b0c0d0c04040b080008000b0800090a0d000b
  | 8, 0 => 0x7070808
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 10 0 (CN0 s)
def CN : Nat → Nat
  | 4 => 3
  | 5 => 41
  | 6 => 262
  | 7 => 136
  | _ => 0
def CH : Nat → Nat → Nat
  | 4, 0 => 0xc716e98410dc74e40cb4b587
  | 5, 0 => 0xbdd60915b184d10b698b83c45eadc67956ed02935461d6824f6077824e3412174c7a947648ae8424470acff842c00d763b9661593a6d8cbf35929fc530bcb8da30b58cec2fcf6cd32d6128e1287922b32253682b2030258b1f8d857f1e7fb84c18da06aa1820d75b1572c177154387ea1541cd571428656913a7405f117d5be9100595fe0d6d51ce0bd464d10a2c00e404be3dd90388c5fa014c8eb100540bbb0009349c
  | 6, 0 => 0xa856c230a32490809ea937a09ea768b09afa619099fdc1109982f8e0975048108e1433208dce5d608c844c908c4c89008bea0cb088afca4086a53c30825242f08199e7b0812527807a9f8c1079cdeed07858bad0784100e077f092307661c4f075b064807556ac5074493dc070a679406f79843069e83720653845b064d19e60610cc6205ccdf660593980e0565b54005586d9c0521e6a4050bab3c04c99ba30481e1580473f335045000890425067f04208162041fc0fd040ba22c03c1389502eea5a8029b3a060278cefd02129c2c01f4dc8b018ce7b50176c274015711040100095700e3f9bd00d3fb7b00c8e4b900853a33004aaa99000bc05a0005073c
  | 6, 1 => 0x1a2ba2c019b12612196c7dee1937e3391931f42d189c0a6b187fac0e17553a401725a47416f39fb816d93e0a167fead01665474815bffc2715b2a458159e76bc14883bee141acd8913aeb5411338c90d132074651242cc1b118e00c411502f8b114fd6fd1103608f10f1822710e9dcab10d5767f10ab2312106281ef104ff240104e54530fedb4970fe146c40f8b4eb30f855acd0ebd93650e4da0c30e1b11690db27b0b0d8e5bbb0d7ffa020d59e3330d5522c70d0f3ce20cffeec60cf96eb20cf845d90cb60cb20c9a1c3f0c964e8e0c7a6ada0c7318d10c2bc5720be907f50bce65dc0b90e1720b721d050b4a3ea60aea89950ae3adbd0ae10f910a8b36b2
  | 6, 2 => 0x3b232a683ada110b3ab3318a39df039d39d857e739461b78375205a4373a00353719beeb3717b47936b9a19535efb95333529e3c3265c6fb30851a1a30447f742ee5fabd2ee433c22ee387152ed942d92e1560c32dcd702f2d956bcd2caa42e62ca7a5ff2b4744a82afd058d2ad75aa72aac09ea29f1bc47288492be2764639326b28d8c269a85fe26270f8825e546ec2473c3ca246e87ec23afdc6023909384226ecb5f2258243222538f2320e9003f20b1b3cd20477cb51fe0e8c41fa99b3d1f8bc5731f792c1a1f52533c1eca58aa1e8341b41e1a47011e19e8bf1df1ca331d84c81f1cdc03fd1cbc52091b8d367e1b29a4721a75ce011a661e1b1a58fb7b
  | 6, 3 => 0x8c4b99de8c1b78ba87f20c9587543c71811e64057aed7f2d79fcd9c87561b9887469cc3f7376979172c4613670daba4b6e3a13f56b6e79766b2668616afd39bf6a82367a696db872695dda1166f0574b657be54d62f3150962e4abb462acc228615df61b5e924aaf5da90c065c32a2955b7cd1d75828c4135765994a5563ed855493698654838f435129c767505f78c94fefa0d64f7d5c464c7a94764bf8eae84b9a43c04b00b86949f14e714804b9aa4678c2bc4640dd424581b25145618ff84409de5a4403486943f0fc3a43a1f4aa432188db42cead55426db18542477a403eeece1c3e4157f63de97da23dce4a1e3c9524943c58688c3b42aa093b2965ce
  | 6, 4 => 0xbdd60915afa98e02a952ff8ea83590029fb95abe9f32385d
  | 7, 0 => 0x1bf30ad91bc808e71b6841971b5ca3fc1b2c9a431a1aecab19935f5e196fdf151965fad618c4cccf175d068617280b76161d4a0c159076d21517253f14fdcbec123daf7e111a22311098b145104f617e1006a1cd0f456bc20f0909980ec5eed70e65b6100e5c3c0c0e5bd5e30e5038010d5f4f1c0d0637910cd7e8440c6db82c0c602eb60c371f4b0ad41bfa0ac094550a91675d09b94c0b09afd20709264d4208dddd6608d177e80859a12007ce231c0759efc7055831cf0518b0d10504efb4050188df04e689e70412361103ce5d6503c2d2bf039bb2bd02da7cb202a95004027fe128023ee520021b1d220207e01e01850c1800ceb31a009eb920009b4881
  | 7, 1 => 0x5f5653cd5e06f6b75d9659485ce7776d57fda5e15705e140542995d853cc109a5313d2fe518d97a74ef89abe4eaa99cd4e5a5b214e4a98cd4b957d9c4b697d7a49b7235e48976adf46bd137545f83e82445d671343f65ca04319726242a73ac44051ecd33ef680d03df1e1cf3bcfb2e63a56c8373a4bc54738b025c7382b509d3509485c3298aacf31fe58b7308aae8f2fef9bcb2dc013122d47ca4e2ca99c1c2c287e6e2b9f80a72b3c6c9b2b363f242a67290b287f1d9b2759da3325ea42742523427924f932f32471eee2240d36f322c315b82251e2e921b408bd21665e91214aeabc21296ef92115415d1faaf0ff1dd0c2ac1d5434741d35e1021c22471c
  | 7, 2 => 0xbd4a6f9398f3f44c9375fbcf91e7ab148d65674170657c20647a9c49621439f2
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 4, 0 => 0x3040f2000004d0348000031041204
  | 5, 0 => 0x6540b028c00004241120965483208c24004241120965c0d030c2000325092070004c3048100052cc1207000960348000054005200000960348000000080107001500148019530cc2307001472348240023013200000d4214824005448f2090014934c81c004340d2000004131482000424112090015331481d970240830000109044824003104120400000400424003048d200001533048259530cc23070000d4348000051cd1207
  | 5, 1 => 0x4249320965483208c019503c0e30800141424824001588d209000413148200023409207000d504c8000000091109
  | 6, 0 => 0x30842000000c31070000034442000000c11000015120082400454cb208000004244240002c0a20000000204424000000b1070000020442400000511070000004441c00534132000000032441c000000b10700147234824000008f1000005524c80000000071080011501c81c000000d1000005503c8240051c8d2090014503081c0052c112080000024440000000c5109000c130081c00000c110000005144820000000e107
  | 6, 1 => 0xc330881c00534082000000042c41c000000e1070000042442400000c31070000001441c00000c110700000434424000010d1000000043442000000c310900000304424000000d1000000040c41c00000051080000023c424000010710b0000001c420005448020000153024820000000710000000034400000010f1000000032441c00000cb1070014d020824000000b108000000244000030cc22080015103081c0054c05209
  | 6, 2 => 0x1044200053c052080000003440000001051000000031c42000000491070000012c42400000c11000000d03082000000c11070000023442400000c71080000003442000000c71070000003442400001091090000020442400000811000000d03082000000051070000041c41c00000811090000001c420003240e2070000024442400000c11000000042441c000000a1090000042442400000c11000000042442400000c1100
  | 6, 3 => 0x1512008000051c1120000000144424005140c2080014520080000001091090000002842400000811090000024c42400000081000000032441c00000d31070000043440000000491080000042442400454cb2080000031c42000000911090000014442400000131090014734481c00001011000008120082400000911090000001441c0000091109000003444240051cd12070000032441c00000821000005504c81c0020480209
  | 6, 4 => 0x14723482400001011080000023440000524c02070014d0208000000005100000000144200015493200000090208000000109109000c330881c000008f1000000042442400000911000000030441c00544802000000003440000000071080000030842000000d11090000034c41c000000d1090000003441c000008d10700000034420000000d1000000014440000014512080000012c40000000c7108000002084000000081109
  | 6, 5 => 0x32442000000911090000002842400000091000000023c4240053408209000c330881c000000910000145308820000008f1000000010c42400000811090000004440000000911090000003c40000000cb10700000244424000000d108000003444200053c052080000023c40000001051080000004c42000000491070000024c42400000091000000002440000000911090000021440000534082000000d2088000000041108
  | 6, 6 => 0x8120080000000931090000030c41c00000051080000003c4200054c05200000002444240020c822090000024442400001071000000002440000000c91070000012c424000000d1090011521c80000000cb1070000002442400000051080000024c424000000d1080005524c80000000d31070014704480000544872090015320482400104c52080014930081c000004d1000000004c40000000131090000031c4200000005108
  | 6, 7 => 0x3442000000131090000004440000001031000000014c42c00000811090000030440000054c720800000024424000008f1000000f03882000000071080000023441c00000911080000013442400000081000000013c41000000411080000032c41c000008d10000000104420003048d2000000902080000000cb107000003044000051408209000c330881c00000c11000000001442000000131090014d0208000051cc9208
  | 6, 8 => 0x24442400000c1107000003044000000093109000004244240024481209
  | 7, 0 => 0x21440000000111070000013440000000051090000014441c00000491070000032c41c00000511070000023c40000000801090000020442400000091000000004440000000d110900000244424000000e1070000031c41c000000f1000000004c42400000071080000023c400000001310900000344424000008f1090000001440000000111000000034442000000051080000001441c00000c91070000004c4240000093109
  | 7, 1 => 0x1c40000000811090000003c42400000d11080000034441c000000c1080000003c424000000d1090000030841c000008d1000000032c420000004d1090000024c42400000c510900000014424000000b10800000028424000000c1080000003842000000821090000004c400000010d1000000034c41c00000911090000021442000000cb1080000023c400000008d1000000041442000000931000000004440000000c0107
  | 7, 2 => 0x34400000008210000000244400000000910000000020400000000a1090000032c420000008f10000000028424000000710000000014400000000a1000000004c42000000d31080000014441c00000811090000014441c00000c11070000030041c00000091000000021442400000911000000032c41c000001310800000234424000000e1070000003842000000091070000020042400000d11090000032c4200000085100
  | 7, 3 => 0x21c400000008f1000000030841c000008f1000000002440000000cb1080000003440000000131090000032c41c00000821000000004442400000821090000031442400000511090000020042400000c51080000003c40000000091000000031441c000009110900000314424000000910700000024400000000a1000000004c42000000931090000003841c000008f10000000038420000001110000000014400000000e108
  | 7, 4 => 0x134424000000d1000000003440000000c5108000002084000000008100000000444240000080100
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 10 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_217 roots_217 7 s ws hint
  | 1 => checkCutEntry true dom_209 roots_209 4 s ws hint
  | 2 => checkCutEntry true dom_82 roots_82 4 s ws hint
  | 3 => checkCutEntry true dom_27 roots_27 4 s ws hint
  | 4 => checkCutEntry true dom_203 roots_203 6 s ws hint
  | 5 => checkCutEntry true dom_89 roots_89 4 s ws hint
  | 6 => checkCutEntry true dom_147 roots_147 4 s ws hint
  | 7 => checkCutEntry true dom_91 roots_91 7 s ws hint
  | 8 => checkCutEntry true dom_155 roots_155 7 s ws hint
  | 9 => checkCutEntry true dom_211 roots_211 7 s ws hint
  | 10 => checkCutEntry true dom_137 roots_137 4 s ws hint
  | 11 => checkCutEntry true dom_218 roots_218 6 s ws hint
  | 12 => checkCutEntry true dom_153 roots_153 5 s ws hint
  | 13 => checkCutEntry true dom_83 roots_83 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_219 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_217 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_209 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_82 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_203 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_89 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_147 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_91 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_155 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_211 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_137 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_218 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_153 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_83 _ hc
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

def symsG : List (List (Nat × Nat)) := [[(0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xffffffffffffffff0000000000000000, 64), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xffffffffffffffff0000000000000000, 64), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xcccccccccccccccccccccccccccccccc, 126), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xffffffffffffffff0000000000000000, 64), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]]
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
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 18 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 18 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 74 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 74 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 51 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 51 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 10 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 10 0 = true)
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
  scr true dom_219 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : RunD true dom_219 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_219 roots_219 goal_219 10 := by
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

theorem lowS_219 : Lower true dom_219 roots_219 goal_219 10 := S_219.noCircuit

namespace S_246
def pairsG : List (Nat × Nat) := [(2, 18), (2, 34), (2, 66), (4, 36), (4, 68), (4, 132), (6, 22), (6, 38), (6, 70), (6, 134), (16, 18), (16, 80), (20, 22), (20, 52), (20, 84), (20, 148), (32, 34), (32, 36), (32, 160), (48, 50), (48, 52), (48, 112), (48, 176), (64, 66), (64, 68), (64, 80), (96, 98), (96, 100), (96, 112), (96, 224), (128, 132), (128, 160), (130, 134), (130, 146), (130, 162), (130, 194), (144, 146), (144, 148), (144, 176), (144, 208), (192, 194), (192, 196), (192, 208), (192, 224)]
def r1sG : List Nat := [2, 2, 2, 4, 4, 4, 6, 6, 6, 6, 16, 16, 20, 20, 20, 20, 32, 32, 32, 48, 48, 48, 48, 64, 64, 64, 96, 96, 96, 96, 128, 128, 130, 130, 130, 130, 144, 144, 144, 144, 192, 192, 192, 192]
def r2sG : List Nat := [18, 34, 66, 36, 68, 132, 22, 38, 70, 134, 18, 80, 22, 52, 84, 148, 34, 36, 160, 50, 52, 112, 176, 66, 68, 80, 98, 100, 112, 224, 132, 160, 134, 146, 162, 194, 146, 148, 176, 208, 194, 196, 208, 224]
def mpG : Nat := 0xfffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_246.map (· &&& dom_246)
def goalM : Nat := goal_246 &&& dom_246
def NN : Nat → Nat
  | 7 => 1
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 7, 0 => 0x62e152c9
  | 8, 0 => 0x4548ae56
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55005500000000005500550000000000550055000000000055005500000000005500550055005500550055005500550055000000550000005500000055000000550000005500000055000000550000005500000055000000550000005500000050005000500050005000500050005000500050005000500050005000500050004400440044004400440044004400440044004400440044004400440044004400550055005500550000000000000000005500550055005500000000000000000055005500550055005500550055005500000000000000000000000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 7, 0, 0 => 0x1ac6887
  | 8, 0, 0 => 0x346886
  | _, _, _ => 0
def stateW : Nat → Nat
  | 7 => 25
  | 8 => 22
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3c7f0000fffc078fc000f00078fc000000000f3f800f000003c7f003f800000fffc0000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x844bc7f208affff27cfe614f21278fc412214912f3f811f048917c7f883fa04914fffe0448220
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
  | 5, 0 => 0x4548ae56
  | 6, 0 => 0xeba141fbd7a90bf24548ae56448bb7b81c1d7eb81727fbd21661cb57
  | 7, 0 => 0xb3f79237a70250e197fbe2ed7898516e63fb71794548ae56387a9ebc3212235128f9f8b91cc5c51e1c28e77e17b992c51727fbd2105ec0560af0ab300a9a028407a582ce05f4797b05741adc02f98202
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 5, 0 => 0x0
  | 6, 0 => 0x2020000020201
  | 7, 0 => 0x1010102000103040000010504000001040400
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 6 0 (CN0 s)
def CN : Nat → Nat
  | 6 => 4
  | _ => 0
def CH : Nat → Nat → Nat
  | 6, 0 => 0x51bc831b33c88d65119ed0690cb0289e
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 6, 0 => 0x4144045110041440491103
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_244 roots_244 7 s ws hint
  | 1 => checkCutEntry true dom_242 roots_242 7 s ws hint
  | 2 => checkCutEntry true dom_230 roots_230 6 s ws hint
  | 3 => checkCutEntry true dom_182 roots_182 7 s ws hint
  | 4 => checkCutEntry true dom_214 roots_214 7 s ws hint
  | 5 => checkCutEntry true dom_118 roots_118 6 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_246 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_244 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_242 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_230 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_182 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_214 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_118 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 22 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_246 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_246 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_246 == dom_246) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_246 goalM v ys) : RunD true dom_246 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_246 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr true dom_246 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD true dom_246 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_246 roots_246 goal_246 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_246 goal_246 := by
    have h0 : isConstB dom_246 goal_246 = false := by decide +kernel
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

end S_246

theorem lowS_246 : Lower true dom_246 roots_246 goal_246 9 := S_246.noCircuit

def isoMvS_123 : List (Nat × Nat) := [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]
theorem lowS_123 : Lower true dom_123 roots_123 goal_123 8 :=
  lower_iso isoMvS_123 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_95

def isoMvS_159 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)]
theorem lowS_159 : Lower true dom_159 roots_159 goal_159 8 :=
  lower_iso isoMvS_159 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_95

def isoMvS_187 : List (Nat × Nat) := [(0xffffffff00000000ffffffff00000000, 96), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)]
theorem lowS_187 : Lower true dom_187 roots_187 goal_187 9 :=
  lower_iso isoMvS_187 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_183

def isoMvS_189 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_189 : Lower true dom_189 roots_189 goal_189 9 :=
  lower_iso isoMvS_189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_175

def isoMvS_190 : List (Nat × Nat) := [(0xffffffffffffffff0000000000000000, 64), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]
theorem lowS_190 : Lower true dom_190 roots_190 goal_190 8 :=
  lower_iso isoMvS_190 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_95

def isoMvS_215 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_215 : Lower true dom_215 roots_215 goal_215 9 :=
  lower_iso isoMvS_215 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_183

def isoMvS_231 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem lowS_231 : Lower true dom_231 roots_231 goal_231 7 :=
  lower_iso isoMvS_231 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_119

def isoMvS_237 : List (Nat × Nat) := [(0xffff0000ffff00000000000000000000ffff0000ffff0000, 48), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]
theorem lowS_237 : Lower true dom_237 roots_237 goal_237 9 :=
  lower_iso isoMvS_237 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_175

def isoMvS_238 : List (Nat × Nat) := [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]
theorem lowS_238 : Lower true dom_238 roots_238 goal_238 7 :=
  lower_iso isoMvS_238 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_119

def isoMvS_243 : List (Nat × Nat) := [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]
theorem lowS_243 : Lower true dom_243 roots_243 goal_243 9 :=
  lower_iso isoMvS_243 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_183

def isoMvS_245 : List (Nat × Nat) := [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem lowS_245 : Lower true dom_245 roots_245 goal_245 9 :=
  lower_iso isoMvS_245 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_183

theorem lowS_127 : Lower true dom_127 roots_127 goal_127 9 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 32, 36)] (by decide +kernel) (by decide +kernel) lowS_123

namespace S_191
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (1, 129), (2, 18), (2, 34), (3, 11), (3, 19), (3, 35), (3, 131), (4, 36), (4, 132), (5, 13), (5, 21), (5, 37), (5, 133), (6, 22), (6, 38), (6, 134), (7, 15), (7, 23), (7, 39), (7, 135), (8, 9), (8, 136), (10, 11), (10, 26), (10, 42), (10, 138), (12, 13), (12, 44), (12, 140), (14, 15), (14, 30), (14, 46), (14, 142), (16, 17), (16, 18), (20, 21), (20, 22), (20, 52), (20, 148), (24, 25), (24, 26), (24, 152), (28, 29), (28, 30), (28, 60), (28, 156), (32, 34), (32, 36), (32, 160), (33, 35), (33, 37), (33, 41), (33, 49), (33, 161), (40, 41), (40, 42), (40, 44), (40, 168), (48, 49), (48, 50), (48, 52), (48, 176), (56, 57), (56, 58), (56, 60), (56, 184), (128, 129), (128, 132), (128, 136), (128, 160), (130, 131), (130, 134), (130, 138), (130, 146), (130, 162), (144, 145), (144, 146), (144, 148), (144, 152), (144, 176)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 8, 8, 10, 10, 10, 10, 12, 12, 12, 14, 14, 14, 14, 16, 16, 20, 20, 20, 20, 24, 24, 24, 28, 28, 28, 28, 32, 32, 32, 33, 33, 33, 33, 33, 40, 40, 40, 40, 48, 48, 48, 48, 56, 56, 56, 56, 128, 128, 128, 128, 130, 130, 130, 130, 130, 144, 144, 144, 144, 144]
def r2sG : List Nat := [9, 17, 129, 18, 34, 11, 19, 35, 131, 36, 132, 13, 21, 37, 133, 22, 38, 134, 15, 23, 39, 135, 9, 136, 11, 26, 42, 138, 13, 44, 140, 15, 30, 46, 142, 17, 18, 21, 22, 52, 148, 25, 26, 152, 29, 30, 60, 156, 34, 36, 160, 35, 37, 41, 49, 161, 41, 42, 44, 168, 49, 50, 52, 176, 57, 58, 60, 184, 129, 132, 136, 160, 131, 134, 138, 146, 162, 145, 146, 148, 152, 176]
def mpG : Nat := 0x3ffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_191.map (· &&& dom_191)
def goalM : Nat := goal_191 &&& dom_191
def NN : Nat → Nat
  | 6 => 7
  | 7 => 20
  | 8 => 13
  | 9 => 3
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xe28b40c8d05bd3585b2d9ea1506c43dd4c711e874055a50d164badf4
  | 7, 0 => 0xfdacd7388fc693d9806d5c787f9391547b729d6079f759836d98f6246636ef333964e1b734346f7931a2f1da2db89df229d730db27a91b88279d10071b7b96e8172436000d3a8814094d04610798fac1
  | 8, 0 => 0xbbd02dc3b657e28ab3bde6d8a95938f7806d5c787d364e976dfdd6ef41d37d4c3d2f3f902a09fa5b204714971c4b66050da52aba
  | 9, 0 => 0x75d447a660742600064323c9
  | 10, 0 => 0xb46e26d2
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff00ff00ff000000000000000000ff00ff00aa00aa0000000000000000ffffffff000000000000000000000000ffffffff000000000000000000000000ffff0000ffff00000000000000000000ffff0000ffff00000000000000000000cccccccccccccccc0000000000000000cccccccccccccccc0000000000000000aaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa00000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0a0a0a0a000000000000000000ff00ff00ff00ff000000000000000000aa00aa00aa00aa0000000000000000ffffffffffffffff00000000000000000000000000000000
  | 0, 1 => 0xffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaa0000000000000000ffffffffffffaaaa0000000000000000ffff0000ffff00000000000000000000ffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa000000000000000000000000555555550000000000000000ffffffffaaaaaaaa0000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000000000000000af00af00af00af000000000000000000af00af00aa00aa
  | 0, 2 => 0x55555555000000000000000000000000000000000000000000000000ffffffff555555550000000000000000ffffffff000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffaaaaaaaa00000000000000000f0f0f0f0505050500000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000ffffffffaaaaaaaa0000000000000000ffffffffffffffff0000000000000000ffffffff000000000000000000000000ffffffffffaaffaa0000000000000000ff00ff00ff00ff00
  | 0, 3 => 0x555555555555555500000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000aaaaaaaa0000000000000000aaaaaaaaffffffff0000000000000000aaaaaaaaaaaaaaaa0000000000000000ffffffff00ff00ff0000000000000000ffffffff00aa00aa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0xf3160a235cc520d2103bcce5a88d7618ab5106e629069401cc520c470398a4188207
  | 7, 0, 0 => 0x798aa234208c18aa20c208a18ab20c408018ab20c407798ab511b58918ab510778898aa20ce087d8ab510608a18ab510758a18ab20d208798ab20c408018ab20e607798b05106087c8c55a88d8898ab20c408898aa20c208
  | 7, 0, 1 => 0xa48c55a8838799cb510608918ab5106087c4ab511a08
  | 8, 0, 0 => 0xa18ab510608018aa23461043cc55a88305e6262ad4468c120918ab510608a3cc55a88304bcc55a8830565f23156a20c1203156a20f40803e255a8830400062ac83481c062ad44c8c1143156a234609
  | 9, 0, 0 => 0x798ab5106083156a20c1b83156a234608
  | 10, 0, 0 => 0x18ab510607
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 39
  | 7 => 44
  | 8 => 49
  | 9 => 44
  | 10 => 39
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfffc3c3fc000000f1e79c000fffff000000000000f803fc003ffe0000000001f00000000078f3f81f80000003e0000000f1e79fffffffff0000000001e7fffc003e0000000f1e79ffff00000000000000000
  | 0, 1 => 0x3ffffc000000f1e79fe00ff000fff800000000fffc003e0000000f1e79fffffffff0000003c79e70003c3c03f81fff00000000000000f1e7f03ffe00ffffffffc000000000003fff0f0ff0000003c79e7
  | 0, 2 => 0xfffc00000000000000003ffffffff000000000000000000000000000000003ffffffff0000003c79e7ffffffffc000000000000000fffff0000003c79e7ffffffffc000000000000000f0f00fe07ffc00000
  | 0, 3 => 0xfffc00000000000000003fff000000000003c79e7fffc003e0000000f1e79fffffffff0000003c79e7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xbeec3c37c06a000eddf5a108fffff408224112290fa03fc103ffe4082241285f02220924578f3f81f80844447e048a245f1e79f7ddbbbed0a080dc001f7beec2437004a000e9d71bfff88884890448a24504
  | 0, 1 => 0x8c67ffffd4aaad5f5efdff99ff8c4fff90228d14efffe667f26cb367f9f79dce67777bdbaefddf3ef34113c3c83f81fff10208482244412f1e7f03ffe00df76eefb42000320006527990b0dd0028003871d6
  | 0, 2 => 0x739800002241122081003deefffffc9866c9326908c6622210000000810413ffffffffdbaefdff7ff7d732eefb42000320002400007777b52aab55d3af3fffffffff2619b2cd9e5335df8fa4fe07ffe44925
  | 0, 3 => 0xf7ba22012241122081001ef7000009b2cd9ee5d677bdc447e26cb367f9f79efbbfffff41aa243b77d6
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 82 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 82 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 28 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 28 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 28 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 28 then wireAt i else 0
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
  | 6 => 12
  | 7 => 62
  | 8 => 67
  | 9 => 43
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 6, 0 => 0xe8901e26ca2a288eb46e26d2902b868c8e07031f85cf893f77fec0e33fcf7d4839ed01d3314c36b32c34739828137fa4
  | 7, 0 => 0xf3efd031cb1b1663c4d68596c2404fadbcfb9395b46e26d2b0bc7690ad1e3b51accf6dceac97b61ba33830f4a079badca06931b39da0d4be9c87e26f94db91dd9335052c9002c5a18d6525d086ff587085cf893f80ed9b227d00c07877fec0e37153c8786a9d94c560742600605ec91c5de99f395d13c87658ecb99856ef981655b0e40855381f9654a00a2c47f0dcba47e15cfd43676f0d3e9c101b36df98f4366a6ff433875a733300dbdc314c36b3309f179529755671260fdaad25c1b00f1c527af21b83f4a61aacf44616da15c71255c5c90fc083e10e631be50dfe72300d0a8d9f064323c904cd8fe1041868a102214d14009645bc
  | 8, 0 => 0xca2a288ec9283728c7667c61c32f3d16bb3ae94fb90a8b07b555f105b46e26d2b11ed076b114875eb04ace24ac97b61ba1180e409ff5cf5f9f8c2cbf9e5dc5329c87e26f98cd1bf6933a4cbd8c0fae7c8974431e82b2613b8051c54f7986b299667b5d496272bf3a60792eaf607426005f0076da5d4d02165cdc735c5779e97256ef9816562578fc555bbfc254a00a2c50eb702a4a5b54ab48173dc5461dde4845c4cd283f3fe8863b8b4e843aed6c8436f7a03e32bdb8fd314c36b331185d1e309f179529cdcefd2717732a26f1fb2d262841f321da46d418ea5cd417d1d44711b751840dfe72300d34b8f60738dec5064323c90408e242038a3b2e02e8aa92
  | 8, 1 => 0xf257c604d5e867e9cb1b1663
  | 9, 0 => 0xfab0b1adf3efd031d04eb118c949b92eb46e26d2a4fbf8789fbb593b9e9dba719e8acd829d9fa147926741ab8fc768e88a726c7c81e0180e7bcf7a6d76863dd375a76bd872766a926b152c9068017e3363b04a245fa384b05ea591ee5caa31d858cd61e1579def3b431c211c430cfe6135f09a9a34b9e8e7309f17952ca8bc1d2a40528f1d50b5781d3bed1a1ab1c6901428de260dfe72300d34b8f60a85b57c0a2337980854cd9d035dbc4d
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 6, 0 => 0x6010405040700030401
  | 7, 0 => 0x30906060402050403030000020608060603050300040306000404050000010000060402040506090603000009080009030800090602050002050403
  | 8, 0 => 0x4080000050005000000060302020406000604020505080800060502030600000905080002020000030006000000040004030000020002020002030002020400060402
  | 9, 0 => 0x3000506060808050306080803050603060506030603050808060603060302030605030805020205060605
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 8 0 (CN0 s)
def CN : Nat → Nat
  | 5 => 1
  | 6 => 19
  | 7 => 195
  | 8 => 269
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xa4c224c5
  | 6, 0 => 0xe41c74c1e2a6ee8a9cf14ae3888a50617f379fba7e2d11c37bf2f0ef637c22a85bbd2835503c589f379851a02cf67194220a93ce204714971e30e5b212304e8e11346ae20b6aec8d0b3712f8
  | 7, 0 => 0x25e9066725d856ad25bc2a9925a63e2b225e53ac21ffcf29216e191920f7ddf01f346d471c4b66051b7a661e1b73e5d51b29eb511ad5cfb31a292c8f18f2d47816f00ed21691b87315fb9a9c15f7a9c515c6111715380872149fbf56131e00dc128abdfd116a2d1410d4e63d10a7ab54108ded701088e4c1106c59e70fe1b0800fb843710fb4fdeb0ead43aa0e8131cd0e783b4f0d34b8f60d2e81970cf0fc050cbef0990c4568830b9447000a76a8360a63bb470a2e71320997364c09788f0c08fc120708e220a208d5bce10852379a0813c7c007b2adfc074c7edd0708713906d3f23d0648cd6705e24b4e053c60de04a609bb0201347c00f23cbe006bdada
  | 7, 1 => 0x687c96386767f10966127bba651cc30c64d9a0ca6498e3b762d6058c61e31ed65fc8bdf65d7541d95be94f905b14a8355922a4e2567d791550da37a050adb80f4f0a05424e7f8a154cbc8cc74c8e08964bf802da4b5b603148fda3b2481fcd3e47b285ba477d989d473e73a14735aa1345689d4042dcfe7341b9376740618bf8401487323fdc27a93f9a0e173d2f3f903c88b7463c279edd3c246d3d3a872b3d39fea21d39f5d96039b31c2438ae3da4387a640f3742a25e36cc789036910ba235a74d7a359f024a354b83de3522a6f334377ea0342f76ce32950ad031f4d6cf306684102e0d12aa2caa829e2be4392e2b6ae60d2b1141c3281b5195269afc94
  | 7, 2 => 0xe123589fe0b3d656e011148adfeabaccdd1ab7dcd1e3fe09d18c2f7fcd50abdbcac68551c5e2c87cc40ac53ac253b7d7be1330f1bd4977b7bbd02dc3ba37f659b7d8b33bb784d076b657e28aaea1e7dbaaa3ac1aa9e91350a940b84ba8fd475da81554f1a4863235a3ea8679a33628a8a250cf75a0a2a9f69df9f0e19ceed7df9af84fae9a83012e9902af6e96682a6996295e349619405492cae8f2919c9fb98ff66d548fd8eadf8d3190308a1b322189e695ab877980088477ac91832133aa7f0edf827bef1e1779c7d214793dea3678c1b5c9773d3868765ea341742dbb62723a57396f8548f26f36aa126eef95826b8140be6b27f9e26a6abfae69ccbc2c
  | 7, 3 => 0xf257c604e90669fee4cea7a8
  | 8, 0 => 0x1e7c69c01e4294301e1052ac1cb8aa111ca4e7a81bb6892e1ba35cac1b88104a1b1eb6251a3382b5199c53011904100f18fd769e18d9ad1a18bd810618a794981867714517daa820172b30ac171b2bbe170d9b33158c7fc01565b4191556915e14077d61139b1fd112c69f2e12346fd511e8ea3211da1a1f11a5d5ab10c940811059b888102e77c00fb649520ea3143a0e2b41be0d64fc710c2afde40bd2f0ed0ba983de0b1793610aab911c08c7678408b03106083a2d9708158c8007fbde5b07037be406dd014206cfb2af06ccb22b065f7c93065921ed04d3610f048241f004731f35046a961903a3ee6902e306ed02b999de01d423d801bba71c01767550
  | 8, 1 => 0x40f7007a406e03043ffcbe503fb1242f3f8f5f033ece3ee03e6d40d93d359b413c987a403bcd68163b47b4c23aa8c33c3869f3ad37fae55337ec5ea737490a4f370d8cac36786baa365061eb35f9dd2135de54e035a45c91357d56d933dc8b66335cddef32dd7e16329b6484327a83d9321684bc31f4120c3116aad430ef24eb30c8f39a3073be063004739e2de6173c2d8881aa2cc87c7e2cb472912c7b4d642bae84252ba5ae8e2b16f4de29e7823829c37c6f29679f0727d5799b2783d406273d434f25c8766925166af823d8e00e228c3d01228230432223ae0f21c9971a21b75f1621ad6b06213312932109a58420ca9220204e6efb200bb2c21ee58f9b
  | 8, 2 => 0x6662194c665c001b65e6dbdb65e2eb046511d2af62ba5c1d623241d9622ce0926210fbe561cee25361217a0f6003db455ff0ee565f5878fe5f37f16d5f05c21b5ee84e275d6c161b5cbbff795c5ab2735a29ca945a19b271593cf69258e75346579a3a245532b9445513e54f54ac2187542e60865429ab0b53cd627f52b78d87514e4305512d89bc5101f7a64f850ee74eae43364e547f444d705d054c85aea44c23fb4f4bd88d504bd045964bc158694b922bed4b4daad44ada63f24ad5affc4aa3b99f4a90ccb049a5a075499288d4488de19d487f490347db12674646706b45be593644bffd8f448047d34371510b434638e241fa1cfd41b9376741a0e2b0
  | 8, 3 => 0xc79894e3c4c3dd21c3e5e711c0520248bf88284abc634410bc16d281b73ef354b68bb4aab44ab4a8b39cdbcdb30274e8b1a1eeb6af63bb7bad394cc6aa6a8e1ca9c48a08a6b6b0db9da502879da253429b71ca259b2f837499e22666978788a2974e88bd94f11e13923818b191b4d1ec8fe522828df9a61b8d9c21c18c9f93ea8aafda028a2ff1d8864294de85d6b0c584c2f46c849df62683f6001383352a4382da414c81eb0b567f3211ba7ea149e87e7db9147c54b0467c154f867bbc21c17b57791e75f27c8675d45ee3754fb85c7502fca17204ec38713300c97107992d70e74d6e6f353c446e8bb3a26e28a0f76ce474e36cc928816c504ed26a7406f5
  | 8, 4 => 0xf29a75d6ee0edcf1ea1624b9da9e609ad7cffe15d577ffb8d4889e33d32c128cd0237ebdcbebd650cb4a4602c9baee71c85e90db
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x1d945d16300
  | 6, 0 => 0x36514200000da0548080016915200001174588000063c15202001144548000061d152004649a054c0c9a0551530500187454801cb464153050000030841000368152020001945480d1d268153030018f054808001651420072c19454c0c0062d15200
  | 7, 0 => 0x9a05480c00001161000010105481400269152050011a0548140000117100000114548140016915206000da05482000001151000009a45482000269152050000045440c00368152080010105482000169152060000005441400368152080000045440000169152060000045840000268152060000025840000169152060010105481400169152060019704481400464152030009a4548140046416203001190588200026815203
  | 7, 1 => 0x25840000268152060009a05481800000961000001145480c00269152080001a45481400000151020010105482000001161000009a45481400464152030009a05481800268152030011905480c00464162060001145481800651012030009a05480c00000961000000025840000464162080001945880c00045152030009a45481400000151020009a45482000000961020009a0548180000096100001940448200026815206
  | 7, 2 => 0xda05480800368152080000025840000000151020005a4548000026915205000da0548200026815203000004544000026915208000da0548200006515203000004544000065c112050000030841000464152060005a45481800464162030001145481400169152060009a45481400468152050010105481400000151050009a05481800000961020001945481400268152060010105481400069152050009a4548140026815203
  | 7, 3 => 0x19740481800268152060000030841000268152030009a45481400268152030000025840000001151030005a45480000169152060001a45482000368152080009a05480c0006515203000da05480800000961020011a05480c00001151030011905480c00268152060005a45481800065162030000005441400001171000001145480c00269152080011905880c00654112050009a0548180036815208000000544140026915208
  | 7, 4 => 0x9a05481800404152060000045440000368152080000045c40000169152060000025840800368152080000045440c00268152060001945481400065152080000005440800001151000009a45481400055152030000045440000065162030009a05480c00169152060019740480c00000151050009a45481400169152060011905880c00404152030009a45481400065162050000030841000069152080009a05480c0006516203
  | 7, 5 => 0x45840000000961000019740480c00045152060001a4548140046815208000004544000026815203000da05482000000161020009a4548200000114100000da05480800368152020000005440800268152060011905881800069152060009a0548180026815206000000544140026915205000da05482000368152020009a05480c00268152060000025840800368152080000045c40000045152080009a4548200065d01206
  | 7, 6 => 0x1161000010105480c0026815203
  | 8, 0 => 0x45841400001161060000005841800000161020000045441800001151060000005440c00000161060000005840c00001151030000005841400001151000000005842000001161060000045440c00000151080000045840c00000151030000005442000001151030000045442000000151030000005842000001011060000040440c00001161080000005841800001151060000045440c0000011105000004544140000015105
  | 8, 1 => 0x5841400000111050000004442000001011060000045840c00000161050000005441800000151030000005441800000111080000045440c00001011060000005441400001151060000045441800001151000000045841800001151060000045840c00000161060000005440c00001151050000045841800001161030000005840c0000116108000004544140000116105000000584140000116103000000544140000115103
  | 8, 2 => 0x5841800000161060000045441400000161050000045440c00000151060000045442000001011060000040441800000151030000045842000001161060000045842000001011030000005841800001151060000005441800001151000000040441800001011030000005840c0000015108000000544140000016106000004544180000016106000004044180000011103000000584180000101103000000444140000115106
  | 8, 3 => 0x5440c00000111050000045840c00000151030000045441800000161080000005842000001011060000045841800000161080000005841400001151050000045441800001161000000004440c0000116103000004044180000016103000004544140000116106000004544200000016108000004544200000011105000000544200000115108000004544000000016108000004584180000015106000000444140000116105
  | 8, 4 => 0x5841800001011080000005842000001151030000005841400000111050000005441400000151030000045440c0000011103000004584140000016108000000584180000016103000000444200000015105000000584140000016103000000584180000015105000000584080000016106000004584000000015106000004544140000116105000000444200000015106000000444140000116105000000544140000115103
  | 8, 5 => 0x40442000000161030000005440c00000161050000045842000001011060000005440c00000161080000045842000001161000000040442000000111050000040440c00001151050000045841400001011060000040440c00001151030000045840c00000151050000005441800000151080000045442000000151050000045440c00000151050000005840c0000016108000004044200000116105000000444200000115105
  | 8, 6 => 0x40441800001151060000045841800000161030000005841800001151080000005442000001151060000045441800001161050000005840c00001151060000005440c00000161050000005441800000111030000045840c00000151030000005841800000161060000004442000001161080000045442000000111050000045841400000161050000045440c0000101103000004544180000115103000004544200000101103
  | 8, 7 => 0x5441800001011050000045841800001151030000005440c00000161030000040440c00001151050000005841400000161080000004442000001011060000005441800000161050000045441800000151030000005842000000161030000045441400000161060000045841400001151060000005840c00001151060000004442000000151060000045440c0000011105000000544140000115106000000544140000116103
  | 8, 8 => 0x151020000004440c00000161050000045841800001151030000040440c00001151080000005840c0000016103000000444140000116105000004044180000115105
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 10 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_190 roots_190 8 s ws hint
  | 1 => checkCutEntry true dom_54 roots_54 4 s ws hint
  | 2 => checkCutEntry true dom_159 roots_159 8 s ws hint
  | 3 => checkCutEntry true dom_187 roots_187 9 s ws hint
  | 4 => checkCutEntry true dom_63 roots_63 7 s ws hint
  | 5 => checkCutEntry true dom_183 roots_183 9 s ws hint
  | 6 => checkCutEntry true dom_189 roots_189 9 s ws hint
  | 7 => checkCutEntry true dom_151 roots_151 5 s ws hint
  | 8 => checkCutEntry true dom_175 roots_175 9 s ws hint
  | 9 => checkCutEntry true dom_27 roots_27 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_191 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_190 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_54 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_159 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_187 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_63 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_183 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_189 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_151 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_175 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 42 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_191 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_191 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_191 == dom_191) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_191 goalM v ys) : RunD true dom_191 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_191 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 20 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 20 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 13 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 13 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 3 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 3 0 = true)
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
  scr true dom_191 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_191 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_191 roots_191 goal_191 11 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_191 goal_191 := by
    have h0 : isConstB dom_191 goal_191 = false := by decide +kernel
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

end S_191

theorem lowS_191 : Lower true dom_191 roots_191 goal_191 11 := S_191.noCircuit

theorem lowS_223 : Lower true dom_223 roots_223 goal_223 11 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 64, 68)] (by decide +kernel) (by decide +kernel) lowS_219

theorem lowS_239 : Lower true dom_239 roots_239 goal_239 10 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 32, 34)] (by decide +kernel) (by decide +kernel) lowS_237

namespace S_247
def pairsG : List (Nat × Nat) := [(1, 17), (1, 129), (2, 18), (2, 34), (2, 66), (3, 19), (3, 35), (3, 67), (3, 131), (4, 36), (4, 68), (4, 132), (5, 21), (5, 37), (5, 69), (5, 133), (6, 22), (6, 38), (6, 70), (6, 134), (7, 23), (7, 39), (7, 71), (7, 135), (16, 17), (16, 18), (16, 80), (20, 21), (20, 22), (20, 52), (20, 84), (20, 148), (32, 34), (32, 36), (32, 160), (33, 35), (33, 37), (33, 49), (33, 161), (48, 49), (48, 50), (48, 52), (48, 112), (48, 176), (64, 66), (64, 68), (64, 80), (65, 67), (65, 69), (65, 81), (65, 193), (96, 98), (96, 100), (96, 112), (96, 224), (97, 99), (97, 101), (97, 113), (97, 225), (128, 129), (128, 132), (128, 160), (130, 131), (130, 134), (130, 146), (130, 162), (130, 194), (144, 145), (144, 146), (144, 148), (144, 176), (144, 208), (192, 193), (192, 194), (192, 196), (192, 208), (192, 224)]
def r1sG : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 16, 16, 16, 20, 20, 20, 20, 20, 32, 32, 32, 33, 33, 33, 33, 48, 48, 48, 48, 48, 64, 64, 64, 65, 65, 65, 65, 96, 96, 96, 96, 97, 97, 97, 97, 128, 128, 128, 130, 130, 130, 130, 130, 144, 144, 144, 144, 144, 192, 192, 192, 192, 192]
def r2sG : List Nat := [17, 129, 18, 34, 66, 19, 35, 67, 131, 36, 68, 132, 21, 37, 69, 133, 22, 38, 70, 134, 23, 39, 71, 135, 17, 18, 80, 21, 22, 52, 84, 148, 34, 36, 160, 35, 37, 49, 161, 49, 50, 52, 112, 176, 66, 68, 80, 67, 69, 81, 193, 98, 100, 112, 224, 99, 101, 113, 225, 129, 132, 160, 131, 134, 146, 162, 194, 145, 146, 148, 176, 208, 193, 194, 196, 208, 224]
def mpG : Nat := 0x1fffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_247.map (· &&& dom_247)
def goalM : Nat := goal_247 &&& dom_247
def NN : Nat → Nat
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | 9 => 3
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 6, 0 => 0xd8782e6974c7452d1b511b02
  | 7, 0 => 0xeb62b6fedbc52337540c370244d8e129
  | 8, 0 => 0xdbc52337353b4d6227c16c8f241dd2fe054ce95e
  | 9, 0 => 0xc66b64d91e9b39e1054ce95e
  | 10, 0 => 0xabd6bf33
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x550000005500000055000000550055000000550000005500000055000000ff00ff00ff00ff00ff00ff00ff00ff00ff000000ff000000ff000000ff000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000000000ff000000ff000000ff000000ff00ff000000ff000000ff000000ff000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc005500550055005500550055005500550055000000550000005500000055000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000
  | 0, 1 => 0xff000000ff000000ff000000ff0000000000ff000000ff000000ff000000ff0000000000000000000000000000000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000ff000000ff000000ff000000ff00000000000000000000000000000000000000aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 0x563217075643210705432106
  | 7, 0, 0 => 0x54328065b3210a75632109756432807
  | 8, 0, 0 => 0x5b3210a756b3210a805d3280c705632809756b3280a8
  | 9, 0, 0 => 0x5b3280a985b3280ac856b3280a8
  | 10, 0, 0 => 0x5b3280a7
  | _, _, _ => 0
def stateW : Nat → Nat
  | 6 => 32
  | 7 => 32
  | 8 => 36
  | 9 => 36
  | 10 => 32
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf83fc0007c07f8000007fffe0003e03fc0000000000ff01ffe00000001f07f8000f80ff000000000000000007c7fff00001f0000000003fc07f3ffff0001f01fe000001f0007fff00000000000
  | 0, 1 => 0x1f01fe000001f07f80000000000000007c000007c07f8000007fffe0000000000000001f000000000000000000000787807800f0f1e3
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xb03583023823b0484027ffff9993f93fe66649e0844ff01ffe40444491706fe6647e47f999927210488891097c7fff00085f022244244bfc07f3def60c09e09ec121009f8407fff40044444490
  | 0, 1 => 0x4448f40fe22204b706fc4400440088890247c811127d07f888812fffff1102112022224091f200001001000000001084f8780f809f0f1e3
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 77 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 77 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 14 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 14 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 14 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 14 then wireAt i else 0
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
  | 6 => 1
  | 7 => 13
  | 8 => 26
  | 9 => 26
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 6, 0 => 0xabd6bf33
  | 7, 0 => 0xff250721abd6bf339e3e8c0a7076bd09631120605f6d86cf5e2731ac241dd2fe1e9b39e1138c569f1332fa3c117ac6b205f75ca4
  | 8, 0 => 0xff250721c66b64d9abeef3b6abd6bf33a1e2259b9e3e8c0a90161f067076bd096d69aa8a56af295449b2509343a7f968430d14143db0a2ab392fdf87348d688b3362bc3d238528951fe18f041e9b39e1138c569f1332fa3c12c16498117ac6b20a36d81204328fbc
  | 9, 0 => 0xaf96d756abd6bf33a0ee3d9b9f79c33097b894d476c3ed9b727bea1e6e9266a8617a4e7048d9328148d83bb844e5307a3e28721934aab87c33daa8ae2c5d297b28dac08325d3e27a21d84215215de8a41f594ffd1f2b5da41c6ab42f114d56670b9176870983a2a9
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 6, 0 => 0x0
  | 7, 0 => 0x500050506050501010005
  | 8, 0 => 0x5000006060500000105010004050301050506010104000500
  | 9, 0 => 0x30204000200030003000303020204030200020203000400
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 6 0 (CN0 s)
def CN : Nat → Nat
  | 5 => 3
  | 6 => 39
  | 7 => 106
  | 8 => 147
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xb4b7a7b9ac8c930d5106be7d
  | 6, 0 => 0xec169f55df05bafbc121523eb002b4d4aa7ce8a8a889ca658a63540b89c1da7d8785f1ca6be92146695f7b70616439e05eb7556f582a547f54f672ef52bef2075106be7d4de454c54b1d6e52490f9a743eb0feec35e5c0a82ecd5833241dd2fe23cecb572269665a1c91bc211bae40f318870e291863559112761755124987c008fb5b710837c5440713dd9a05f75ca40495204d02759366003e495a
  | 7, 0 => 0x511e71914f19c1a84e899de54c59183346658dd944967ad54372932b43215e4042d0962141b6777140f2e14440cfbf8f3fcef99a3f5f0c8a3d503c4d3c88bbc13b7fda8b353b4d622ffaeb612fec9ea02f136b252c5751d02b8184b22845591c283bf07b27ddeb212798dc0326918956265cc5162601889925b0a8972436078122edefc520912b8a203995fd1f2fc46c1eba872c1cd8eaf71beea5951b64708c1a15318d19de9d131935516617c0d6fb16b83ba1163b038215f7f2f5152de21211d4ea881032afc90fc5ad940fa3ef760da7c16f0d795d9a0cee4f480ce1c7860cd24d8a0c10ad2c08e97a62064fe88d04feda0d02d8838e02ac4efc020591ae
  | 7, 1 => 0xf659c8dde8bdd0d4e1c68a52dc957528d8d75dc6cf682734ce2cf00ec96f63a6c81e592ac200cf82ada470b3a6b2519f9f7a20099dc2ef719b160b009a1f55e09772716f9168b27490161f068e70e23e89c1da7d857797e483478aed7c79a3877c60abe4776c1aec70be23936f8bbc056b2c0dc46af0f0dd6788743364991c805ec81beb5d5b14045c4b8d7f5b24825a5974f24b5971a07858c9248756e3b68f55c2467e51c6a619
  | 8, 0 => 0x2c248cc82b9731b72abdd12e28f80a3227c9b48f26c230c926757d302647d75826261c2d2578510c24433eb12418484f24154c5822e58dd1225b52042221f7a42154a2e320fe0ffa20e23bc71ec735621e7f52ad1d6b56a81b76280c1aff808e1a92e0421a36665c1a287bba1983d10f1637451b155afa541499e25b13e0599513b2b84912d63c4512643ec3123e3dde121743fd1134d41611028c11107b653b1032afc90e6d915d0e2b5ce60d8668300c623d9c0adfd79f0a7d0f8209f1180909d6060e090d018108c7f26307c8f1f0067dbcc805bd92330573a048055fed3c04e82950041d062503ac1adc03331a4c0227d78901cd622e00803ae50075fe88
  | 8, 1 => 0x9a8e2f3d94226352915893418d108fc48411d11583478aed7ee307037e58afee7e55f1357db60caf7c0ef4167b4e6c4078a187cf77f0922675bfc1037593672f6f8bbc056ca924676af0f0dd6973a4ce66643d24665b31ee65f6ee4664c0f297644e615d63c40a48636dd8275f79d6205a446f7d597464c758bd17bf589b314c584548515368badc507dd819504f74444f3f5e224e6f4e544dc22a6c4d0ce16b49c15c2448b78a9347f702c8474d8ca446f1cf2146658dd9436f662943681444431260cd40cfbf8f406888203f5f85763c6ce7bb3c5398ba3a4c607d39c0034a3994a73038c4976236ff59d5359873533384b6df3376cc3d324d87f12e924de2
  | 8, 2 => 0xec3a78e2e51e27fce156e156d8d75dc6d03a17c6ca898256ca2b7cfcc9ece734c96f63a6c81e592ac683995cbb9dad2fbb82e341baf0789bba120752ba0e68d6b24d3a7aa605cd9b9ef7344d
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x19f2509530067c94254c019f25095300
  | 6, 0 => 0x942548019f2509530067c94254c099f2509530067d48524c099f52149302000942548019f2509530367cd4354c059f25095300000942548019f5314d30467d48524c019f250953000000050c4159f350d530467c94254c019f2509530067c94254c019f5214930267cd4354c119f5314d30467c94254c019f350d530167d48524c099f2509530067d48524c0d9f5214930067c94254c019f5214930267cd4354c059f25095303
  | 6, 1 => 0x19f2509530067c94254c099f2509530067c94254c019f2509530067c94254c019f25095300
  | 7, 0 => 0x9425480c0000095100000005244000060cd52040014b5288080025c962030014b52880c0025c96202001485248080025c962030009425480c00250952020014f53880400250952030014b52880000521492020018325480c005654e2040014b5288080025c96200001835348100060d492020014c5348100060c95202000d73588100060cd5204001835348100025c962030014c5348100060cd52010009425480c0060cd5201
  | 7, 1 => 0x942548000060d492020000030c4180060c95203001595288000052d4a2030014b5288000060cd52010009425480000250952000014852480c0026496203001485248000025c96203001485248080060d49202001835348100000095100000972588000060d492030000025440000250952000014b5288000060c95203000942548000052149200001485248080025c962030000030c4180052d4a2020009425480c0025095200
  | 7, 2 => 0x30c4180000095100001835348100052d4a2020014b5288080052149202001485248080060c95203001595288000060d4d2040009425480000000c31060015953881000250952000014b52880c00250952000018325480c005654e204000d73588100000095100000d43548100060c95203000972588000052d4a200001832548080025095200001835248080052149202001833548100025c962000018352480c0060d49202
  | 7, 3 => 0x50c4140025095200000002544000025095200000992588000060c952020000030c4180026496200001595288000025095200
  | 8, 0 => 0x25840c00000951030000025440c000009610200000354410000009610300000530410000014e10400000534410000014a10000000250400000009510000000524408000014810000000358410000009610000000350410000014910000000524408000014810200000258400000014e10400000358404000014a1030000052840c000009510300000358410000014e10400000534404000009510300000534404000014a103
  | 8, 1 => 0x25840c000014c1040000052840c00000951030000025840c000014a10200000254408000014a1000000053041000000961000000052840800001481000000052840800000951000000025840000001491030000052840c000014910000000258408000009410000000524408000009610300000358404000014e1040000052040c00001491000000025440c000014a102000005284000000094100000005284080000096100
  | 8, 2 => 0x530410000014a1000000035841000000961020000025040c00001481020000052840c00000951000000052440000000d510400000528400000009610000000250408000014910000000350410000014a1030000052840c00000951030000052040c000014a1020000052040800000951000000025840000001481020000052840c000014a1020000025040c00000d51040000025840000000961030000025440000000d6104
  | 8, 3 => 0x25840c000009610000000250400000014810200000258400000014d1040000025040000001481020000035841000000961000000025040c000014910200000524408000014a10000000538404000014a1020000053441000000d510100000254400000014a1030000052840c00000961000000025840c000014e1040000025040000001481020000025040000000941000000025840800001491030000052040c0000095100
  | 8, 4 => 0x961000000025040000000961000000025440000000951000000025040000001481000000025440000000951000000052440000000941000000025840000000941030000025440c000009610000000250408000014c10400000528400000014a100
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 9 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_246 roots_246 9 s ws hint
  | 1 => checkCutEntry true dom_183 roots_183 9 s ws hint
  | 2 => checkCutEntry true dom_243 roots_243 9 s ws hint
  | 3 => checkCutEntry true dom_245 roots_245 9 s ws hint
  | 4 => checkCutEntry true dom_215 roots_215 9 s ws hint
  | 5 => checkCutEntry true dom_231 roots_231 7 s ws hint
  | 6 => checkCutEntry true dom_119 roots_119 7 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_247 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_246 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_183 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_243 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_245 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_215 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_231 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_119 _ hc
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

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0xffffffff000000000000000000000000ffffffff00000000, 32), (0xffff0000ffff0000ffff0000ffff0000, 112), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xffff0000ffff0000ffff0000ffff0000, 112), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 3 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 4 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 5 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 3 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 3 0 = true)
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
  scr true dom_247 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 6 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_247 goalM s xsM) : False := by
  have hmin : 6 ≤ s := by
    have hl := run_len h; change 7 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_247 roots_247 goal_247 11 := by
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

theorem lowS_247 : Lower true dom_247 roots_247 goal_247 11 := S_247.noCircuit

theorem lowS_254 : Lower true dom_254 roots_254 goal_254 10 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5500550055005500550055005500550055005500550055005500550055005500, 128, 136)] (by decide +kernel) (by decide +kernel) lowS_246

def isoMvS_251 : List (Nat × Nat) := [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]
theorem lowS_251 : Lower true dom_251 roots_251 goal_251 11 :=
  lower_iso isoMvS_251 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_223

def isoMvS_253 : List (Nat × Nat) := [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]
theorem lowS_253 : Lower true dom_253 roots_253 goal_253 11 :=
  lower_iso isoMvS_253 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_191

namespace S_255
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (1, 129), (2, 18), (2, 34), (2, 66), (3, 11), (3, 19), (3, 35), (3, 67), (3, 131), (4, 36), (4, 68), (4, 132), (5, 13), (5, 21), (5, 37), (5, 69), (5, 133), (6, 22), (6, 38), (6, 70), (6, 134), (7, 15), (7, 23), (7, 39), (7, 71), (7, 135), (8, 9), (8, 136), (10, 11), (10, 26), (10, 42), (10, 74), (10, 138), (12, 13), (12, 44), (12, 76), (12, 140), (14, 15), (14, 30), (14, 46), (14, 78), (14, 142), (16, 17), (16, 18), (16, 80), (20, 21), (20, 22), (20, 52), (20, 84), (20, 148), (24, 25), (24, 26), (24, 88), (24, 152), (28, 29), (28, 30), (28, 60), (28, 92), (28, 156), (32, 34), (32, 36), (32, 160), (33, 35), (33, 37), (33, 41), (33, 49), (33, 161), (40, 41), (40, 42), (40, 44), (40, 168), (48, 49), (48, 50), (48, 52), (48, 112), (48, 176), (56, 57), (56, 58), (56, 60), (56, 120), (56, 184), (64, 66), (64, 68), (64, 80), (65, 67), (65, 69), (65, 73), (65, 81), (65, 193), (72, 73), (72, 74), (72, 76), (72, 88), (72, 200), (96, 98), (96, 100), (96, 112), (96, 224), (97, 99), (97, 101), (97, 105), (97, 113), (97, 225), (104, 105), (104, 106), (104, 108), (104, 120), (104, 232), (128, 129), (128, 132), (128, 136), (128, 160), (130, 131), (130, 134), (130, 138), (130, 146), (130, 162), (130, 194), (144, 145), (144, 146), (144, 148), (144, 152), (144, 176), (144, 208), (192, 193), (192, 194), (192, 196), (192, 200), (192, 208), (192, 224)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 7, 8, 8, 10, 10, 10, 10, 10, 12, 12, 12, 12, 14, 14, 14, 14, 14, 16, 16, 16, 20, 20, 20, 20, 20, 24, 24, 24, 24, 28, 28, 28, 28, 28, 32, 32, 32, 33, 33, 33, 33, 33, 40, 40, 40, 40, 48, 48, 48, 48, 48, 56, 56, 56, 56, 56, 64, 64, 64, 65, 65, 65, 65, 65, 72, 72, 72, 72, 72, 96, 96, 96, 96, 97, 97, 97, 97, 97, 104, 104, 104, 104, 104, 128, 128, 128, 128, 130, 130, 130, 130, 130, 130, 144, 144, 144, 144, 144, 144, 192, 192, 192, 192, 192, 192]
def r2sG : List Nat := [9, 17, 129, 18, 34, 66, 11, 19, 35, 67, 131, 36, 68, 132, 13, 21, 37, 69, 133, 22, 38, 70, 134, 15, 23, 39, 71, 135, 9, 136, 11, 26, 42, 74, 138, 13, 44, 76, 140, 15, 30, 46, 78, 142, 17, 18, 80, 21, 22, 52, 84, 148, 25, 26, 88, 152, 29, 30, 60, 92, 156, 34, 36, 160, 35, 37, 41, 49, 161, 41, 42, 44, 168, 49, 50, 52, 112, 176, 57, 58, 60, 120, 184, 66, 68, 80, 67, 69, 73, 81, 193, 73, 74, 76, 88, 200, 98, 100, 112, 224, 99, 101, 105, 113, 225, 105, 106, 108, 120, 232, 129, 132, 136, 160, 131, 134, 138, 146, 162, 194, 145, 146, 148, 152, 176, 208, 193, 194, 196, 200, 208, 224]
def mpG : Nat := 0xfffffffffffffffffffffffffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_255.map (· &&& dom_255)
def goalM : Nat := goal_255 &&& dom_255
def NN : Nat → Nat
  | 8 => 6
  | 9 => 21
  | 10 => 18
  | 11 => 5
  | 12 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 8, 0 => 0xe1e42d81b58487d3911f38e78b608839765fdf6d051074e7
  | 9, 0 => 0xfd4b934dd73a5413d00bc0d8c68e8e22bf5ffae7994ebbad9220287270e44b626fd40dd365eae98d5def37e24b6ebee749c2ce9945b00e3942943b5e37ddf8a8321f47fa30af656d2e8f940c1d9c4a7b180aecc7
  | 10, 0 => 0xff8e9861f22d7ea8ec6ecdfada1f5461b2194970a35d81e19189da13874f1a1b78ae915c71d8c51860323cf65b4be0f6539e41ad32b3be242b33d162203a6f8d06cbe66304125499
  | 11, 0 => 0xbec9ac8880de14224433a3a637ccc8093152270e
  | 12, 0 => 0x1f6d511d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa555555555555555555555555555555555555000055550000555500005555000000ff00ff00ff00ff00ff00ff00ff00ff00ff00aa00ff00aa00ff00aa00ff00aaffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | 0, 1 => 0xaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0055005500550055005500550055005500550000005500000055000000550000ffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff000000ff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aaffffffffffffffffffffffffffffffffffffaaaaffffaaaaffffaaaaffffaaaaffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 0, 2 => 0x555500005555000055550000555500000000000000000000000000000000555555555555555555555555555555550000000000000000000000000000000000000000000000000000000000000000ffffaaaaffffaaaaffffaaaaffffaaaa0000ffff0000ffff0000ffff0000ffff000000000000000000000000000000000000ffff0000ffff0000ffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaaffff5555ffff5555ffff5555ffff5555ffff0000ffff0000ffff0000ffff0000ffff00ffffff00ffffff00ffffff00ffffff00aaffff00aaffff00aaffff00aaff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 8, 0, 0 => 0x1073148268412861cc5188209424e628d4104a16731483506509398a3104128398a4188209
  | 9, 0, 0 => 0x424f031483082909398a470820a0218b818a308240861cc570820942cf03148308280041cc570820802127315ca08250961e0628c20a021673148e50650961cc570820a02127818a308240859e0629061902127315c208240889cc572820902187818af08240859cc5728209
  | 9, 0, 1 => 0x859cc570820942567818a308290959cc570820a020f031483082408398a4708209
  | 10, 0, 0 => 0x2167818a4706408398a4728209430f0315c105e80859e062b836942567818ae082808a9e062b820900107315ca0820083c0c5238349020f0315c30824083c0c574c209424f03148e08280891e062b82090218b818ae08250b3c0c523820a020f0315ee08250961e062b820a
  | 10, 0, 1 => 0x42cf0315c308280849e062b8209
  | 11, 0, 0 => 0x859e062b820941e06291c104a0f0315c1052507818ae082d2861e062b8209
  | 12, 0, 0 => 0x41e062b8208
  | _, _, _ => 0
def stateW : Nat → Nat
  | 8 => 49
  | 9 => 54
  | 10 => 54
  | 11 => 49
  | 12 => 44
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3f0000000007fe001ffff00000000000000000000000000001f0f8ff80ffff800000fc00000000000000000f87cff807f8fffffc1f007c0001f000000000f87c7c7fffffc0000007fe001ffff00000000000fffffc1f007c03e1f000ff0000f87c7c7fc0003ffffff800000000000000000000fffffc000000000000000000000000000
  | 0, 1 => 0xfc0ffc1f007c0001f000000000f87c7c70000001f007c0001f000000000f87c7c7fffffc00000003e00000ff0000000000003f0001f007c7fe1f1ffff0000f87c7c7fffffc0000007fe001ffff00000000000fffffc1f007c0001f000000000f87c7c7fffffc1f007c7fe1f1ffff0000f87c7c7000003fff0007ffffe000000000000000
  | 0, 2 => 0xfc0ffc000000000000000000000000000fffffc0000000000000000000000000000000001f007c7fe1f1ffff0000f87c7c7fc0ffc000000000000000000000000000fc0ffc1f007c0001f000000000f87c7c7fffffc0000007fe001ffff00000000000fffffc1f007c7fe1f1ffff0000f87c7c7000003e00f807c1e01ff00ffff0000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x43f2010844227fe081ffff1008108808a104088822209108825f0f8ff80ffff800082fc04111048844122212f87cff807f8fffffe3f88fc4633f919898cc7fc7e7c7fbefbb00cc027bd009eef6944a0482008df7eec1bc06e03e1b800ff0000f4fa78efe0803ffffffa10000844442204221220fffffe108840421109088084428442404
  | 0, 1 => 0xbc1dfe3f88fc0433f811098cc7fc7e7c70410443f00fc0423f011090885f87c7c7db6ea800c00203c00800f60000048200847f2453f44fe7fe3f1ffff188df8fc7cfffffff18cc627ff189ffff944a94ca48edf7eec1b806c0221b800890000f47a786ffffff3fccfe7ff3f9ffff9ccffcfe7cf810423fff0007ffffe402021102110910
  | 0, 2 => 0xb80dba008800001008000084420402000fbefba0088004210090880844204020000000012f44be3de2f0f77f188d78bc3cbbc0dfe108840001108000084428442404bc0dfe3788dc00137800008cc7ec76745fbffbb08cc227ff089ffff944a148a08adffeed1bc46e7fe1b9ffff1008f4fa78e208113e40f907c1e41ff00ffff0804041
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 132 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 132 (i % 8)
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
  | 7 => 4
  | 8 => 47
  | 9 => 146
  | 10 => 117
  | 11 => 66
  | _ => 0
def CH0 : Nat → Nat → Nat
  | 7, 0 => 0x54c2ea1e3a0390a41f6d511d1f4a6ecf
  | 8, 0 => 0xfb81a9dffaa4b58df1f8974fec39e6a1e672f966e306efe6e1d29da9dc13ecfbd999f4cfd7393dd5d6818367d5196c74d387d868cedc65f2ce41d76accff941bc88326bcc713442fbe94c52fb22ced28ac5a225aab18c879a4fa72cda3d56bb5a2b5e1d49e2919359ade054a9933f28893af720f6bf420135cf26ce45c5724d25baa907857a79e3f51b271e638904df323aa4a562159ecdc1fcfce611f6d511d16d29179165de63b124cdbd00d667fd007e2b8ac075379fb0637ec95
  | 9, 0 => 0x6afe825c6405194763c9bdb962a21fad61c88ad75f49f8cd5cfa3c6c5baa90785aa5e7765a0f47a65a066ae35722c0d357038105552d8b4a518810ab4bf48b444a6a2c174a141b5e44195e1640d73a273e08c39f3d8574a03d35e1c438287c0437ccc8093732e0c9340b911d329f85282f8236642bba0d5127edb8d526fb669126ab75862643a613263ac9502623dde02416eb7623aa4a56238a0e0722a9235320b20b0d2061419d1f6d511d1c862ed01c6ef9ec19f9c70c15fde43a142ea4b8124cdbd012290224102a354c0e11006b0e002f6f0d614da90c73a24709b9d30d075379fb07136a0a04b8f5b8042786950267ebd4024a80260102cf4500ad90b7
  | 9, 1 => 0xd347c877cfa2954ece9c4a41cb1a0557c7b605d0c5a0017ec4b31adbc2323eacc1d0a02abf8aaf02bdf08486bd276e96ba2abc1eb69e4e4fb4f43b8db48d2135b48bb9ccb38b0023b24eb633b1ff5f96b076404db04d68bbaf1395e1acdf81ecaba4c06ea6dc136ca5b99db4a5a2a705a0f728cf9f8610ff9b2b89379b1ee3d59b10c1e39a76335b9a552ff19a161dd393159a60900057118f23ca2b8e4f775e8cdaa2208c7e96ec89ddc537892bebf288d91ec688bdb68d88915d6a87b46918874f1a1b858afe2882d2acbc80de142280c018397ea9f32c7e2487c97ddfbcf1797bafcc71d7057270cdd9e16fcfb0eb6edf125d6eb4a5006bba6f6c6bb248a1
  | 9, 2 => 0xfbc5f2f6f71165d5f2dfd3f3ee102f2eea02206fe8bfdd20e62f70dbe4190a4ee054a3badfc197fadcb8b753dc5e93b9da455ed8d6ffa06dd6c89b86d4ce38bcd44a9aead387d868
  | 10, 0 => 0x92c2ea1391e58d909038c9658e58a9228d2ad056865353fd81f42a028196219880de14227902d3697864bef4770062c875f885b770cdd9e17033f03c6efef0b96eb4a5006ddb39fe6205bf155ff3503c5c931a925baa90785936b11357a79e3f561879975535006552bc101851ab119e514b20b04dca80054b1335104a29484649b19dfa4433a3a64419843d3e154dfa3d9ee34238395e8b37ccc8093428d4a03113585330c43ebe2bba0d512b9238ec2ad3c4a628c778ff2710d2af2693451b266f7bf224b802602149e8481f6d511d1ddf700b1d6632681c6ef9ec1a94d38418664b1016d29179142f561713be6b1611e70352046dbcf8038c34a3024a8026
  | 10, 1 => 0xfc1c35ebf71165d5f468e7d7f413a099f345311cef281272ea375ffae8ad7177e8020c3ae72b85cae672f966e5a4be47e38fff11e306efe6e1876b3fde1b61bfd7292374d71508bcd6c89b86d36347bdd0ae8279cfa2954ec9843fa2c8d5b739c4fac608c4338c24c25b163ec047ff06bec9ac88bcbca3fbbb5c70dfbaaa0f78b893ea6bb24eb633b22ced28b076404daf1395e1ad415f01ac306087a5a466aba3496729a247fd2ca1a6db91a0f728cfa034737f9e66fcc29e2919359b25d36c993d8b0e9933f00c9824322b968d5d57950a15a6
  | 11, 0 => 0xd6c89b86d575d99fcfa48b3ecfa2954ecbaf4de1cb236c0ec53ff79ac510e825bfabba69bdd6512bbd2514a5bcfc20a8ba64b203b84e0c67b24eb633b076404daf47401fa93e40ffa8219417a537aa92a11054179d24802d99fba56c998e0a2996771fec950d0fcc90e08e6289cdb3478225b5027d6b3a457947c5077530eafc6f847ff06080f9fa5c5449ff48bc19ea40d73a273d00ae4638dd38fa3709f1263575c9ce2c2c4fd02bba0d512901cdd6269fe8cd244273a01f6d511d1ee53b201da2926f1737fe4215d15dda1236b6d810a93c2a0e4db3960d17918c0af82e250ac4f0c905f2eeb103e10b57030b82f40297ddda024a802601aca8ac00b1f0b4
  | 11, 1 => 0xee4ccd72e9d94aa5
  | _, _ => 0
def CV0 : Nat → Nat → Nat
  | 7, 0 => 0x5050104
  | 8, 0 => 0x5000505030305050c0507050300050005050503040000050703050005000504060300000604050103050305000305
  | 9, 0 => 0x303030505000500060309080b05000508070807030703050806090303070006000507070005070608070b00030a05000003050308070103050308090308070307010b0808000306030008090a05010a060306030607060003070b09010305010000080507060a07090a010b030a05070306080807030a070303060903080307
  | 9, 1 => 0x70800060500000708030308080003060003
  | 10, 0 => 0x80803080307030306080a080303030708030108030803070803030805030807080303030308070803080307010709030003010303030a01030b0908030608060908060808080a0b07060303080a030806080706030803070303030b03060307090708060b060801080b03010b03080903030608
  | 11, 0 => 0xa0603060608060b01060a0a09010b0a08030a0a0106060a0a060a010a010a060a0909060106030601010a0a0301010901010b0a01010b0b0601060a0b010b080b0a
  | _, _ => 0
def ch0At (s i : Nat) : Nat := fld (CH0 s (i / 64)) 32 (i % 64)
def cidx0H (s h : Nat) : Nat := bsr (ch0At s) h 9 0 (CN0 s)
def CN : Nat → Nat
  | 7 => 13
  | 8 => 379
  | 9 => 1427
  | 10 => 421
  | _ => 0
def CH : Nat → Nat → Nat
  | 7, 0 => 0xf27532c7f0aed3ede431ed31d7b5d94da15b0a787e2ec31278ae915c73884cd7695ac4565def37e22cc918a72188d6ab12c8babb
  | 8, 0 => 0x1da59d381d636df51d4526b41d0dcc6b1c9d48841c7e85e51c7915861a78369d18f8427718b19941180430be1789ac851788ab18177df4cf17462f681662fb7315ebc724154a824b144cc44114064a8b13d6e9b413d03a92136bfc5d12d9c2b61191acc7108ad2d60efb425d0ef300940e4799dd0e2672030e247c130db894080d6bb9450d4e30160ce3a59b0cd7b7500c6b7cb70bf4fdbd0b6b195709b9d30d09a552d308b71fc10843a59f083064c00806266707d3b7cf0797752307831f1706cbe663062867e405b512600571a0c605414ac1051f59d503c1de5f03a338770311ac8802cbcd7d02c1f069028024be026a2ab2024e72f10166da3700e8f55f
  | 8, 1 => 0x3cd9db143c4950c23c1af1e13c01e6d33b721b7d3aab7d663a99125b3918005038763f773845dccf381b81ed37ddf8a8359fd3f8358f2047340c99ab33c0a92e338cd46a3315464b327c1030321f47fa31e541b031a783e53161bab83152270e30af656d3020583e300f4c242fce855e2f12df5f2e6abe032da005ec2cdaf3ef2cceb4372cc918a72c8908b62b4a2c502b33d1622afe1a222af0b4bf28b946bf28ac0d552877ed82285b316a2804103027e1553e27dd8a802773aaf62736ebc52729ad40267172b12517cca124f4e02b2426a50c23cbdbbf22c57fe1228f35b82188d6ab20f659b620aadf572000a43b1ff5d8d81fd9b8e11f85fbf91ed9d261
  | 8, 2 => 0x637939106361bc4862fb134c62c45a65625906b8621f73ec60faf93c60f0550b60c82b5360323cf65e7b76195d68c6d45d34e7fa5c6156d05b8bc0655afec86d5af0e0b15916ba4957d97c2456e831d5561d0ef455ecb8e255b9e507557820bb5554783e54b549d85416f9545311c7a9524051db523434b45231db5151d68bf050b89d9d50aae8e9506aa1534ecbf3254d7aca4e4ccf9a5b4cc857d64c4633334c25be484bfc5fb64b9978514b6ebee74af5890c4a1e36f8497a14ea48cb7511463b9fc245b00e3942efa3bd42a96d5a428c48b54262f21c4202b81e418d69b94119c49f40ec586840cc66eb40b765e3402e8f71400dca343fdfa37a3d4e8f32
  | 8, 3 => 0x91f815ba90d5667f8fd9c2468fc4955e8eaa053f8e7932938dd89f818c7e96ec89a6d34488ab2f0b884e235f86fe1cc48608f075851b0d5b84ed1ab3847511a1846e55988304057182b58a6b82634b5180de14227f84e6527f7c098f7f5920ec7e61fb027dbae73d7c9734bf7b87dc557b3f9a4779ab6e4e793acf9378ae915c78a2e48177fc368f7720b04a764eaece75b03a2b758bd7eb741b380372e433d371a78b4f6fd40dd36f87e4da6e5c87556e2899f76cf38e2e6c9313166af3b0a46aae36956a74a11c6a3bf41669b5b827695ac4566844abf7683c4ac7683a23c8678901b56787b1506783b49b66bd21c265b4e2866521cf9265152be064c58cd8
  | 8, 4 => 0xc4d6cacdc4b31adbc36f0178c306a5c1c13978f2c0a79bc7c07610c7bf5ffae7bec9ac88bd1b537dbc509b66b9737d35b7c9abccb7893f18b784ba2eb765620db73123d0b724cb46b6e6a5b9b5c71d71b49ab7c5b48f8c5db48d2135b4651f00b400293db3b2d1c1b21a3313b1f5c97db1a9373bb16ae96cb05aabddb0123394af4fc0a6ae0666b5ad368bc5ac5d20c3aa18fec5a9f3c161a943d0fba897f8fba6c63519a5af2fefa36246bca3555b9da2b6e005a15b0a78a0fc5af6a087a5da9f298ae59f02e0bf9eb423bb9d74e3e59c06dcc09ad630c499cdc7bb998b826e97568e399706d62096fb9ab09629850496014e609476855593b6e72a93945780
  | 8, 5 => 0xfd4b934dfc9ec220fb2c6daafa38690ef9c49c5ef92bf63df8e698c8f7d10270f66a77e1f4490436f3762252f22d7ea8f0d09cf8f0aed3edefa00542eef82712edc926e4ec6ecdfaec3916baebc345c6eab2474ce97a09a4e7c027c4e7aad138e6a37adce1df68a6e0905a5ae054a3badf923adcdf790f94deb65a44dcaafffadb356a41dacbe028da1f5461da015878d9a7ba31d973e530d80ff0eed6a618f0d50f441cd1a5ff33cf627527cebab02ace8998c6ce731bffccda8fe7cc257412cb1a0557cb1845b1cacb875bc975307bc852cb70c7add2b7c71c7a3dc6f829a0c5d100e0c5ccecc9c4fbafab
  | 9, 0 => 0x70c3c450701fbe706cbe663069bd9a9068fc3850689a495066c0a270643d0660634e9cf0623c05a0615e5c60604e37305ea58e905e63d8b05e45ac605deb5d705d5d3fe05759b3e0573ebaf05601b6d054948be0506492b050127b504f41e3704db4b8a04ce44e604ba1bfd04917805047e3fde0439fc9e04125499040b6e0303ae7a00038510f80331748a032e39430326192403174c61027f813e02781099027746ab0261d94701dff99b01dd6e6a01b2b41a01a4355e01933a790183c255018261fb017f09dc017bcf57016fd3270166da370162d45601621a80015b6b09011e877300ffe18b00ef77fe0094c44b0070a642006c5d3f00650fac00078f54
  | 9, 1 => 0xe5e5e1f0e4671110e3b6dc80dfe7e130de9b5140dd8b7040dc1e0300dbde40b0dbd5e440da1238c0d781d390d745aa80d7328f10d4516a70d3862180d2d6c460d1973900d1583730ce0082f0cd025fe0c7870f90c7439ba0be857e70ba108e60b9d66850b8ff6720b831b170b8125270b49f2af0b412f4e0b0ba27d0ab980620a99ad780a8cf5940a8446440a492b7b0a2359db0a0721080a022b2309f7fd5b09da7a3709cf500209ccb9ff09ca1eb109b7808c098dea42092d960808f21d1508d4191508994a860888805e087a01a2086b6cf8084f4dd20835f75908163c7d07bfd6e307b9b8fd078dddba07844fd5076f88d707655543071c066a071a765f
  | 9, 2 => 0x1590ed2d157db2dc151cc7ca14f315b314d0bf2614a2d87c147d7d401428fa2913eb4fb713a5f242139767b2138f5f28138ae5161318a297131500671309833812d03e2312a72b5f1248d9e6121ebe18121c9e6111b96ef611afc831118f4ca6118a54ab115fc7e111564e6d11546978113520831133ac18113392c8113360dd112009fd111ed9c210f8c15910d57b8510ca532b10c6e2bc10a28643109ea97f10697717106781271060631c1041c52610366bca10244b1410035d150ffb991c0fe703a90fc7a6bb0fc0dbd10fa78b9c0f9088a00f7003a80f6794a30f64d5ff0f52b4e80f2c0c560f04cfd80eed7d080eec46b60edc10070ed203390e7b131b
  | 9, 3 => 0x1d237f921d12fc0f1ce975d11cd45f141cb7c2591c8c6a251c7915861c67ea471c5835991c0d78611bab3ed21ba027d31b9b7f231b8102591b7c47751b3c638a1b37278b1ad676461a6a04ce1a6750b01a307f311a1433db199e8eee1989347c19395bb81924cf0318ffe77b18fd409018ecfaa818eb548d18de11d118b0bc541858094b180430be17ff3fec17fb5c6717f4a60617ab6b95178d875f178cc5ad177c5c2017547fb9172ac5231729091d1727785e171a8a6117064d4316f3d13116cdb97716beae6a16be90f41668a19c166654e4165efc791651effb163ac5781619eec8160c5c8615ff13bf15fc7cd115de4ae115bd96c715b104aa15932495
  | 9, 4 => 0x25b81a2925b7da7e258a2295257d23df257b39fd2568bae6253d4f31253b968d2506dda3250084db24e7599324dde9a6248656542464ac4d245f438c242ccb552424a443240dd815240b4e3b23efa93123c5463a238aae7123395eca22fe7e8722e8c54422e84c05227475b522572d862256ce9d22467b0122367d422216e647220e09492197de1f2194209d2114b0f120f95dd92094052a20746bda205dfe93203bce40202fd565202b470220216a05201a72231ff9e0031ff98f541fe505601f7ce5df1f430f021f2e1d3b1f2b5d4f1e8137d91e68866c1e6291f11e60d0f31e5878381e5302ca1e4c9d8d1e3e9b2c1e1ac1dc1e0b5dd01dfd371d1debd630
  | 9, 5 => 0x2e42f3862e0c0e812e0881632d991c302d8276d72d64b6332d4f59842d33b9d32d2e71c32d21c0982d031ab02cf2b1232cd21f702cb7db392c9b26772c8ba7872c5106412c32b2da2baede132b9238ec2b7fdd252b66330d2b2fbc9e2af502a72aabbb652a9e367e2a7e6b492a7094882a67cbca2a3683342a2b5d4b2a03f6a129e9cb97296cb2542955c6dc29182a802917cae1290e0a8d2903d3c128e5cb7d28e3d58d28c778ff28ac0d55284d5dd32835cf6d28357a312830270127f52df027e9517627caa7fe27c076ea278d83672762943626f92a8b26ccf6d926c34fec26952ec5267514af2664fead265b53c925ddb7c825cebbb825cbc89225beb93a
  | 9, 6 => 0x37b9a6983788e0a73786543c37845e4c37767c2d375ca1fe3758e84236dee5d7362c1e1f360a5a2d35bfaca7358f204735894577357bffa735782b01353336c9350b31dd34c5eca0348fd1f33477c193346cef4d342ec60733f9c84b33ea88f9339116df3370f2bb3353208a33412785333770e33328f2273305350c32f40f8a32f26a8132b3be243293022b3290202d326669123259c560324bbc8f322ba8273210c1dd320f33b1320588e231de654531b87b703195d27930f7575c30d10caf30b7680c30a77048301aaf303009dbc52fe2ee402fd386732fc693902f89c4a52f1829a32f14778a2f11b94b2f073bf22f042cf92eccbb3b2e96432e2e6abe03
  | 9, 7 => 0x4244ad7b423267d941e9403241e906ba41c681ef4174d28b413c4a13412a0f4241213064411545694104200440ec516c40dbef5940b8416d40a611a1409b6789409785914053843a3fbf9b303f95eb953f90ceea3f72bcd73f4801403f183d0d3f007a583eea12cd3eaa64843ea07fda3e8156193e766db33e54e2c73e290fff3dcf56be3d8b38853d6e513e3d57a29d3d36cbed3d05f5903cee827a3cd7b8463c85fccd3c5a8ed93c483add3c4830253c44bea03c3e3d2b3bb5b3303b43340e3b1aaa5b3b133a763ac927633a822ed73a5e87013a41d3983a2e8c3a39ed76b539e655d43976e6f5396d273d393b9b3d383007f0380a6d3d3808267a37f2d015
  | 9, 8 => 0x4a59a2f44a58b7364a563bef4a505e2d4a2c436f49ef432e49c0905349a3fcc049604ef14930285e4917b6ba49118276490118e948f6216548c72e8b48bc36d5487b97b8480f264047f1188747df8f4047bcbcf0478e0db14751fe2446f3314846f007ce46d6bdfe46a380a2464941e446386ed7463410434604504645e4f8254591111b456b86f645572ee44515f91f44ff027044a5f73044a3b93f4498f2a344989415448179bc44477c294433a3a6442e6455441abd1c4401dfa543e54c1243d06ecd43b2df454393484e438e076c435f0392435cc9b34356261c4320bedf431a8ae4430f6bff42d0716b42c8952142aa763c42a4e574428fde7642719485
  | 9, 9 => 0x577a10ad575fcb1d56fb75eb56e3153656cf3024567db84d565662c0564c7f52562e967055d7d6b05576f6ef54e5e28d54b4578d54ada8b054829a2f547739c854400d6d541da72e539e41ad5392c612537840dc533dabbe53168e1b52fba2b152dadb675218c1f351bb13a3518f5ba85129233050898f795069b7b050471b4d502b67d04fd29bb84fd1dff14fbf13104fbdcf624f9f7ea54f80f2334f2731df4f129f6f4f09a7644ef5a6df4e9af9ab4e51974f4e3a48664e1546b14ddc7d654dcdd6ee4d05bf224c6defb04c66dd5f4c23a6014c07f2924bc300f44bbd19fe4ba3a8d34b9291a64b89dca24b24ec7f4b1335104aaf94c04a7f5bc64a6cb722
  | 9, 10 => 0x63f0444363c85cac63bb432b63a0bbed63789cc963776bfe6320c68062f8f6f062f01af462d79d3c62d3975b627e78a6621f73ec620e8ca961a6c5a6617b6426617852596118d6ad60b9279160a65a4d60323cf6602103795f8305875ea45be45e52c5a15e42647b5e1a2cf55e03b6d95de20b3f5dbbd9655daefd375d7750a15d63a2205d3a46425d33e5c55d3064c45d224b965cc211985c9f8a485c909ae65c8f80425c8de0d25c77aee85c4cc3335c0286f15bee9ebf5b8bc0655b5a25ff5b4be0f65b1d39015abeb2e559871789594533b359375a5e592b36e9591511935913818858d8f2d458d558955864bea9584d89c557fcea1b57db3ae657d68371
  | 9, 11 => 0x6dec547d6de600f76de4654c6dc97b696db22bf66d30b6e76d00b9776cffab556cf13ba96cbbd2f76c7ef92a6c4e37b46c085a596bf8bd3b6bf509496be87cf66be2ef746bc2d4556b77f7176b71da9c6b460d2f6b2843916b1bb68e6aed4bf26ae45fb66a8d51a06a87b10b6a2c49246a25fd0a69f9436369eac4a769c6b9af69a3723d69844a4869762d27694d8ae269374d77692a7c0268bac96d683ca96868275049681aca44680adfa967d2ec1567cd3d5767989d2a678ef3d56764d4a6673a1bc866fd2249668f8706666be0a96658d1cb6629df1166175e22660674106598499a65831d0f65075f7964e05daf64c9cf8b64a22ad3646e93ae64396e64
  | 9, 12 => 0x786e1fd87849cb11783f23a877f7d81d77d717e977cedcff77ab4e49774b864e7723765b7721c7af7702a10e76ade79b765d441f763fbddc763ab5a7762f7c947624f6f1761daf6c75ebb00375ae0ca4755c12bc755ad889752310f47516b54774f95a8a74e3c05b74adb48f742a942773d081a273c7670173b7565a73ab57e27399c5297378a9fd73000fab72f4a10a72e880ff72e433d372d9f72372bddc0672a6b9c772a423e2723cfe367239276f721712e771ec9d9b71d8c518716a8751715459a7712c488d70e946c070793e817013d1b86fe4adb86fd1a6636fb734166f9ab7066f118b316efef0b96eef03e16ed652ce6e6102d96e11d0f46df8a5ac
  | 9, 13 => 0x845357058450c2ea8403339083c791a283bd9b0983366dd882caecf782c6e30d827d791b82634b5182430e1582076daa81f8eeee81cc919c81b486dc819c2600816a5259815a3ab28125cc6780ec9f6f8045d8ca80368e5c801c72c98012337f80018c8c7ff1fade7fe1290c7fd354f67f85d3c47f5033107f19c7407ef08e127eda39d37e8e8c5f7e8c7a367e81c7dd7e4482e27e25814c7dd5b5327dd3bea77dcae1697dc59a1f7d83b3df7d77bd2a7cb5ca007c6ba5127c48bcfc7c3a3e407bfe6e8a7be917fe7b6d41d17b4b00357b0196997ae1c1a27a5dbdad7a187fd679e7537879d70e1579d20229798c0de778df3e1f78a2e4817891b3e27890acb9
  | 9, 14 => 0x901ba495900706338fe542308fdb81088fbc4e338f80295d8f445d348ee85ee98eb5218d8e81b1cb8e419b538dec35478dbcbfcc8dbaaa478da082388d6c8a998d6a3d038d3c3f378d24df8e8ceae9a98cad37468ca494678c963fd88c8e320e8c243c9e8be1578d8b6bd7058b3388378b0e39f28ad7ce088a93674d8a568e828a5498928a383c048a2691828a22045389fd9d85898105c389762390896ea39a893b6b0388775803886ee95d87e13dc987d13c1b87ab8c55879308c587662ee086fbb3b886c61c8485d56f52857a6a2c856d900f854f8944851b0d5b850ee3be850e454c84fb4d9084f88f7f84ed1ab384c953ae84a9fb8d849aa9c384831573
  | 9, 15 => 0x9bff49aa9bd5bbe99b82e4d09b2a0e0c9b282f069b278de59ae7a9fa9addea429a814e269a1f29679a187a669a0c898b99f3592699b2ad2c99ad4b79997f9187997b30429933f00c98b0cabe98ae5ee898a19b4b98490e0e9832d9d89824e8eb9800252597e17f3d97d4d59397d115b096fdf32996a5d565969756a9968cb9b79626e79c96170b3b95c6d34c9594338c956c220995312282951b662894e70e5194e1b5c094248129940e18ce93c0e0d9939bd64f9342ae2292736ce3926be7f4924cfc8492417477923de45a9222ce8f9219d442921265029189da13917a9eca9174b144910e08489107c25090ce090990b1a74c909cd64590967eb6904b3165
  | 9, 16 => 0xa7506a75a7312f59a70a4fafa6afd566a6889cbaa62841cea60f2b8ba5a466aba5548a6ea53a190ca534e671a517aac2a48b4de9a483a9eba45ab5eea426fb69a3ca1863a3b694aba383e200a36a8885a35d81e1a30d7cd9a2dd2cc4a277567ca264b8c9a262c2d9a2567fcca253dd9ca242b3d4a23da031a1f6dacea1c34749a1bd763ea1a7c499a145e5d3a13c5506a12113c2a0e8bebaa0d39011a0a3bb6ba05f2ab0a034737f9fae91079faca1ad9fa6ec859f8f9ca19f1de2fe9e6f7b6c9e636cdd9e1bd4e69de399999d74e3e59d4a0eb49d2676359d1935d89d14204e9cc063ba9ca6081b9ca4122b9c94bc419c5f89d39c567bd49c446d2d9c37b095
  | 9, 17 => 0xb456c11eb44b9e6cb41be571b40cefd7b3e8145cb3e15053b3ca829cb37ae086b30de327b2f6f7a4b2ec6df5b2820154b24bf515b2194970b1a9373bb198c033b192c5bab1855d8fb1747292b15b0b92b11e1e7db10f7ad5b0fe2ad7b0ea78c8b0db8f4ab0c77bc1b0bc234cb09de2e8b07423a4b06aed34b0496bc9afaa3e15aec3f56aaebfbdfaaea025d7ae7640a4ae1814fbae160473addeb2b5adb754f1adb2f5f6acefe007acd47730acbda914aca17212ac9e8ce0ac812fb3ac7fe6f8ac6f7d6bac156ca4abfaf3c4ab630fc9a9ce3d52a9bd8cf3a988c911a8fed0b6a8eb0072a8b90325a8537cd3a836072aa832a464a815307aa7a07460a75a677d
  | 9, 18 => 0xc3394ddcc306a5c1c2eaa0dbc2b915dbc29f6437c28dad26c25a02e8c1eff3ebc1a2fffbc10cfafdc0d05cb9c04b1e06bfd6ed3dbf2efb85bec9ac88be30261ebe2730ccbe0444dbbdf50c74bd1b537dbcfc836abcf78d85bcd46ee5bccd1dfabcbca3fbbcb39835bc997830bc84ae06bc3cc092bbd570f1bbcb5557bb68011ebb4e4a4fbb46ff54bae41e8eba6057b6ba0cb0e0b9c7bf42b9a86721b998bd25b9562277b949ca1eb93326f1b929aacdb87e1799b864ebd2b7c54ea1b7032084b7012a94b6eb7062b6dac782b6a3eee8b62eece4b5f5d6d5b5c71d71b5958a3eb54257d2b52654e0b504c144b4e9261db4b7be70b4b46f82b4713310b45dbc00
  | 9, 19 => 0xd64c622ed5db289cd5ab62b8d586e582d56c9a02d5170d31d50aadb1d394119fd3918b0dd346e980d31106ecd2f22770d285e441d23e9ce6d2399d1dd210198fd1ea0186d1a57a3bd137dfebd11cbe32d10677dfd0fdb53ed0d7686ad0879788cfd6ae40cfd1c5decf4bfd03cf1d94fbcee62010ce722b3bce55d08bcdab1f0acd2c08b0cce8ba1cccbf1e3bccb522f7ccac4aaecc59c8b3cbb33902cb94796ecb723aaecac994bcca0f1a20c99cd170c9843fa2c8ffb6dac8c5c02fc8971fddc862c2f8c84ae071c823d46ac7c994d0c79c5ef7c69b1805c64291f1c62b3248c5aa3169c595233ac4c76aebc49c4666c43612fdc4148cacc3bcad54c3b3bd22
  | 9, 20 => 0xe54d0343e51cd0d8e4f6e463e4e92fafe49d3fc6e4712abee451018be4226dbae40023f0e364ed07e2eaf845e2e90255e28f1bcbe230db3ee1d53ff0e1bc14a8e13c59e4e1163a6be0f95f58e0447ac3e03aa67ce0339592dfd7bf17df3833b5df049c90def5bae8def476e4de6ffb1bde252890ddb85bb0dd851e54dd12b3fadceee3f0dc6250fbdc130358dc0aa2e6dbb6ea44db6b0b83db691593dadb09acda73966eda543e4dda52f602da1f5461da190e69d9d581f9d98c13eed8afa2dfd88664a1d87125cdd86ec0a1d857552cd85224ddd7f9ab02d7c66da6d775ce26d766c8a8d76648eed75c7308d72dea83d7292374d6e9ec53d6e7b420d6ce0be5
  | 9, 21 => 0xfaf0938cfaa83c61fa134db7f961b4f9f95372a6f9211bc0f8bb8a2ef7f63805f7d75975f76a5974f75694b9f7296114f702a12bf66a77e1f64341dcf5fde03ff5b2be2bf59fcaeaf4a63c2cf47626d2f37bc812f374b0b4f313a20cf2cf4a68f29fe77af27ecb4df256c36bf22d7ea8f223860ff1a98c6af16b3e8cf143f07df13b2c26f0a77c1bf09f9d96f00c2bf8ef7bc762ef2f2777ee2d460cedef78d7ed914767ecf54c60ec6ecdfaec54d026ec042a52ebca4b1beb25cff8ea0f088dea032cd8e9edd64ce9a9156ce992bf04e985a3b1e97076c9e93a7076e8e67ff0e8bc46a6e7ef8bece7a0ff45e67e898de6727b7ae66c1095e5fc966be54da022
  | 9, 22 => 0xfff5051fff8e9861fee5a6eafebad1b9fe7a3adcfe53a3ebfe2d66dcfdf3feedfd1fb7acfcf3042dfcd3ac0cfc62c170fc5697d7fc1c35ebfba9b4fafb893d6bfb716ed9fb237031fb06ebe3
  | 10, 0 => 0x16402aa0163c9a2815c5e14815b9e2201595128f15710a94153a38d91535357c14f058e5148d466714890d8d147cb3cb13bf793813b24def13917e9d13131ffb1302477d12b3c90a11f9121411f5db2210b8032410a984680fac3fee0f70dcc10f1107400ef8e3890ee0db5b0e9f9d2e0e19dbaf0e0e6c920d7a78f10d6e19040c896ac80b85140c0b7e71190b5c38650ae548740aaf04040a8ae67e09b3451b0992571c0953068308966645078acef1073ac57a06ac445e06a86d97069b6be0065be3c3050a731104d8ecb604a69b1d0391a3090380d159035e4a09031afb1102d865880281171c0238c19101b186fa01073d670057c31e0031a3630020cae5
  | 10, 1 => 0x2db5048d2d2010e62c942f132c79a9752b6d39512b1865922ab9413a2a962dc42a86516329c2c532292a0eb2291cd4332908b31629071af028b1414e28a75de02804a21c27d1d57d27b633cb275e306326b0ba9f26ad2a82269214b72681ab2a2672fb3525770878241b8cc92357a511232467b5228e121b222cbe7f21a8eb1f2182106d2150856d211c7d6e20efe92a20328987202428cc1f4714301efc677d1e95d7aa1e6ce3ad1e5fedb11e52659d1cdd04161cc795b01ca9c6ba1c4082431c1ad27d1bd575081b77e2dd1b6af9e01af754c61aa9f7121a0c1f9819becf6c191774d118d2090918a42072185f2ed4183fd6b317ebefa917d7c4a2165cbe33
  | 10, 2 => 0x4b4a0daa4ac20eeb4a18898049cc3c9a497e54e94923b5aa4908c62948eec71748d0e0da489a9c6a487c35ff477def82475a9fbf461dac3b449405fd448bc6bc43e535f643ab8da943333b9242c4851c422c84f1416144c24149e26f406caf824053843a3eff5fb93ecef2de3e1125c13ca1ea8c3c80db983bfe50cb3ba075813b2987893ae6a3c73a97b0633a350ba839a95f34395800d738ea65943884bebe38781b0c3744b20c36fd096136e69ca436c5c5f43627499135d37b5735c89ef6356f8eb33480890734696b373314061f32ca954431dde41531154e4330ca1111303ce9cd2fbe80ae2f9954342f97752e2f9524d02f8b43522e9c11142e30d4c6
  | 10, 3 => 0x746e1f8c74088fc273a779dd7373e2b87265cfeb6fbe769b6f00e6a96e8854916e391ff06d84ec9a6d826c736c68f12a6c35b3ce6b0ba94c6a7fc7796871e9c9672d492a661bbf67659d8cb06551ce5c649c5305647dad1d647c45f9646d439063bb432b6328e797620cf46b61c700cf611b90d65f0815d45e7d23275d32ac965c8170105c587c135bd043af5ba918d65b0a5e2d5aa0efdb5a3c1c5759c10d6e58ef272957aa67d256a91e3e55602532549660255325d13f5264529c513cafe650f2a259509f617050805fda50281e7a4fd29bb84fbd90774fa7cd034f6968124f56b8bc4ee584374ea39b8a4e951cce4dd540ba4dc8205f4d0e5d7a4b663b56
  | 10, 4 => 0xaa214c34a9ecf904a940054ea928ea73a8723348a85bf5dda6f1e5bda6ec078ba5f99ad3a5adf24da56be57aa4eb20bea33d66c2a2c56453a2318ccea22d2a339e0e17909d435f3d9c6ba00d9bb289389af1fe6b9abed8409a852bee99f73d85991c450d98f5f693983829ee95cab13194fa42c5944ad279940a8af39231cbcb91a73bf3904feb028f5010368da928dd8d9d12d58d9061e88b2c9af88935a6108810abd287e3f6dc8715c0ed8654e40885b336a585474c8384e3e85181d0ce5c816955e1811a9c887e21df827b6f70c77b0da96378e37b4878e070e678a8c1477852c728772f15a37624f6f1752f2e1b74d2350a74b68ece74b3c0eb74b15e5a
  | 10, 5 => 0xd0f542f5d0ad8353cfbb271cce049388cce7e6a0cc60e79dcc4987f4cb88ab3bcb1668bccaae2d1fca32e258ca323803c9fdfd1bc91f209dc89e0c2fc80d9cb9c7a6b70bc7332b9bc6bf63fcc5fc4438c5d6a6a0c39ecf0bc376821ac1f1bcffc1ead2b6c19db7ebc12c1610c0810b03be5911bfbe545cb2bdc50d04bd97217ebd1b537dbbcb5557bb3d7275bb2316f0ba7c11acba09aef8ba066a08b96fcb03b7c2a67bb792c83eb71c8083b6f81e54b6c673aeb6abe019b6a5c36ab69459adb5a6e0ebb583f719b2f52a08b2bbe3b5b1ed8115b1931243af09561eaed696d8ae9405d0adaa0f01ac73ecf7ab9a0b4bab72e01aab3cff9faa548990aa2cdcef
  | 10, 6 => 0xffdd5565ff8afcb6fbbe2096fb8eee0ffafecd2efa3c2c28f46addc7f40dce83f075a06aedd5508bea064a23e9d73aaee804022ae7f84c32e75aaf90e40ec4cde29ca3b4e228f892e189612fe0339592df2b048cdedbfd4add9f6e86dd9423d2dd705f11dd145ef0d80b3155d724cd8bd6f5be16d6a1ae01d635c817d53c92d6d40d92a8d3d9e86ad2c428efd23e9ce6d190905a
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 7, 0 => 0x961000000072cd92030002237419306000000014b1000020337419306000223741930690cdd278194010000000095102001c3704d930670e0b704d9401000003649a2030000072cd9203000000014b100
  | 8, 0 => 0x103107000d927819301002033641930600000764c1206002033641930600000764c1206000003741920600000000d91030020f7650130b001c3704d93060020b764c130a000e12781930a0000072cd920300000378192080020b764c1301000003741920600021768c13010020b764c1301000003741920600000378192080020f7051930b00121378193090020b764c13010020b764c130a001193781930900203364193060000037419206000c170cd9301000d92781930a0020f7051930900000378192080020b764c1301
  | 8, 1 => 0x20b764c130a0020f7650130b000000014b10000119378193090000072cd92030001970cd930a00000000d9103002033641930a00000000d91030020f4741930b00000000da103000e1278193010001970d1930b00000001011070020f7650130b0020b764c130a00000374192060000072cd920300000000d9103001c3704d93060020b764c130a00000764c12060011d3781930b0020f7650130b0020f4741930900000704d920600000364192060001970cd93060001970cd930600000764c12060000072cd92030020b704d930a
  | 8, 2 => 0x20b764c130a000003649a203000003649a203000003649a203000c170cd9301000c170cd93060000072cd92030000073d012070000036419206000d92781930a00000764c120600021769013090000006583208000003649a20300021768c130a00000000d91030020f765013090000073c192080020f7650130b0000073c192080020b764c130a00000000d9103000003649a2030000072cd92030000072cd92030020f7650130900000764c1206001193781930b00000001831080020b764c13010000006583208000e127819301
  | 8, 3 => 0xd91030020f76501309001c3704d93060020b764c130a00000378192080020b764c1301000dd27819301000003649a2030020b764c130100000364192060020b764c130a00000000d9103000003781920800000764c12060020b764c1301001c3704d9306001213781930b000e12781930a00121378193090020336419301000e12781930a0020f7650130b000000014b10000021768c13010020b764c13010020b764c1301000d92781930a0000073d01207000c170cd930100000374192060000070c19208001193781930b
  | 8, 4 => 0x20b764c130100000764c1206000003649a203000dd278193010020f705193090020f7650130b0020b764c1301000003749a2030000073c1920800000764c120600000764c1206000003649a2030020b764c130a00000000d91030020b764c130100203364193060020f7650130b000d9278193010000072cd92030020f765013090001970cd930a0020f7650130b0020b3741930a0020b764c13010020f7650130b00000374192060000073c192080001970cd93060020f7650130b00000764c1206000d927819301000003649a203
  | 8, 5 => 0x21768c13060001970cd930600000000c21070020f76501309000003781920800000000d91030011d3781930b0000037419206000e12781930a00203364193010020b764c130a0011d37819309001213781930b0000073d812080000037819208000000741a2080000072cd92030020b764c1301001c3704d93060020f7051930b000d92781930a0020f765013090020b764c130a00000000d91030000072cd9203000c170cd93010020b3741930a00000000d91030020f474193090020b704d93010020f7650130b0012137819309
  | 8, 6 => 0xd91030001970cd930600000378192080000072cd9203000003649a2030020b764c1301002033741930600000000d9103001193781930b0020b764c130100000378192080001970cd93060012137819309000d9278193010000000096100000003649a2030020b764c130a000003649a2030000072cd92030000072cd9203001c3704d93060020f7051930b002033641930a00119378193090020b764c1301000dd278193010020b764c1301000003649a203000dd2781930a0020b764c130100000764c1206000000014b100
  | 8, 7 => 0x21768c130a0000060d81208002033641930600000000d91030020b764c130100000001831080020f7051930900021768c13010000073d8120800000374192060020b3741930a0020b374193010001970cd930a000003741920600000000d9103000003649a20300000000da103001193781930b0000073c1920800000000d91030020336419301000000009610000000378192080000072cd9203000003749a203001c3704d93060000073d012070000072cd920300203764c13060020b764c130a000dd2781930a0000037419206
  | 8, 8 => 0x73c192080020f765013090000073c192080000073d8120800000378192080000073c1920800021768c1301001193781930900021768c130600000374192060020336419306000003649a203002033641930600203364193060000060c192080020b3741930a000003741920600000764c12060000072cd920300000378192080001970cd93060020b764c13010000073c1920800000000da10300000000c2107000003741920600203364193060000072cd9203000003641920600000364192060020b3741930a0000037819208
  | 8, 9 => 0x20f7650130900000378192080000072cd920300000704d920600000378192080020b764c130a0020f705193090000072cd92030001970cd930100000374192060000060c19208000003649a2030020b764c130a000000658320800000704d920600000704d92060020f7650130b0000072cd92030000073d8120800000000d9103000000010110700000000d91030000037819208000000018310800000000da1030020f76501309000003649a203000003741920600000000d910300000001031070000073c1920800000000c2107
  | 8, 10 => 0xd910300000764c12060000072cd92030000073d012070000073d012070011937819309000c170cd9306000003741920600000378192080020f4741930900000704d920600000764c12060000072cd92030020b764c130100000378192080020b764c130a0020b704d930a00000000d910300021768c13060020b704d9301000003649a2030000037819208000003649a20300203374193060000037419206000d92781930a000000014b10000000378192080000037819208000000014b100000c170cd930100000000c2107
  | 8, 11 => 0x72cd9203000003649a20300000764c1206000003649a20300021768c13060000073c192080020f7650130b002033641930600000764c12060000072cd9203000000014b10000203374193010000073c192080000072cd9203000000014b1000000072cd92030020b764c130a0001970cd93010001970cd93060000072cd92030000073d81208000d92781930a0020b764c130a0020b704d930a0020b764c13010000072cd92030000000096100
  | 9, 0 => 0x64da201000003781920100000768c120600000278192010000070d1920b000000751a209000002781920a00000364c1206000003641920a00000064da20a0000070cd920a0000076cc120a00000064da20a00000064da20a000003741a20a000003781920b000003741a20a00000000da10300000000d91030000076cc120600000378192080000027819201000003641920a00000068d92060000037819201000003781920a00000378192060000070cd92010000070cd920a000007690120b000003641920a0000037819209
  | 9, 1 => 0x76cc1201000004781920b00000000da103000002781920100000064da20a0000036419206000004741a20b00000074da20100000064da20a00000704d920a00000068d920a0000070cd920100000278192010000070cd920a000000691920900000364192010000070cd920600000064da20a00000000d910300000364c120a00000765012090000076cc120a000000751a20b0000037819201000000001910600000000d9103000004741a2090000070d19209000002781920a000003741a20600000764c12010000036419201
  | 9, 2 => 0x3641920a00000000d9103000002781920100000000d91030000070d1920900000378192060000036419206000003741a2060000070cd92010000076d0120900000064da20a00000764c1201000000009a103000004650120900000364192010000076cc120600000068d92060000070d1920b000002781920a000002781920a0000070cd920100000764c120600000764c120a000000010110700000074da20a000007650120b00000378192060000070d1920b00000764c1201000004641920b0000076901209000007690120b
  | 9, 3 => 0x4650120b00000764c120100000000d910300000074da20100000764c120a00000000d9103000003741a20a00000068d920100000704d92060000000019108000007051920b000004741920b000004650120b00000068d92060000037819206000003781920b0000076cc12060000000019108000003741a20a000000651a20b00000364c120a0000070cd92060000070d1920b000000751a20900000764c12010000037819208000003781920600000000da1030000076d012090000046419209000003641920100000064da20a
  | 9, 4 => 0x76cc120a000000651a20b0000076901209000000010110700000764c120100000000d9103000002781920a00000464192090000070cd920600000000d910300000074da20100000064da20a000004781920b0000076d0120b0000076cc12010000070cd920a000002781920a00000000d910300000764c1206000004650120b000000651a209000003741a20100000064da20100000764c120a00000364c1206000007051920900000364c12010000070cd920600000764c1201000003741a20600000364c1201000004781920b
  | 9, 5 => 0x1a10800000364192010000070d1920b000004741a20b00000068d920a000004781920b000002781920100000068d920a0000037819208000003781920b00000000d9103000007051920b00000074da20a00000000da10300000378192060000027819201000003641920600000000da10300000068d92010000070cd9206000002781920a00000364c120a000004641920b000002781920a00000068d92010000070cd92060000076cc120600000378192060000000019108000000751a209000003781920a00000000d9103
  | 9, 6 => 0xdb10300000000da10300000000d91030000070cd9206000003781920b00000064da20100000000d910300000064da20a00000064da20600000768c120100000364192060000076cc120a000004741a20b0000076cc120a00000278192010000000181108000003641920a00000364c12010000037819209000007690120b00000378192090000000183108000003741a2010000070cd92060000070cd920a000007650120900000765012090000000019108000004741a20b0000036419206000000009a1030000070cd9206
  | 9, 7 => 0x183108000003741a20a000003741920600000074da20a000002781920a000003741920a00000000d910300000064da206000004641920900000069192090000076cc120a00000000da103000004741920b00000064da20100000764c1206000003741920100000705192090000036419201000003641920100000068d920a000000001b108000004650120b000007650120b0000070d1920b000003741a20a0000076cc12010000076cc120600000068d9201000002781920a00000000da10300000364c120600000000da103
  | 9, 8 => 0xda10300000364c1201000004741a20b00000068d920a000000651a20900000064da2060000000019106000003741a20600000074da2010000076cc120a00000764c120100000064da201000000001a108000004781920900000764c120a0000000101107000004641920b0000076cc120a00000764c120600000000da103000002781920100000074da201000002781920a0000070cd920100000764c120a00000478192090000036419206000003741a20100000064da206000003741a20600000364c120100000068d920a
  | 9, 9 => 0x76cc120a00000378192060000076901209000003741a201000000651a20900000074da2010000046419209000007650120b0000076d0120900000068d920600000000d91030000076cc12010000047819209000003781920b00000074da206000004650120b000000001a10800000764c12060000037419206000004741a20b00000064da20600000074da2010000070d1920900000364c120a00000364c120100000764c1201000004781920b00000068d920100000278192010000076d0120b000003641920a0000070519209
  | 9, 10 => 0x68d92010000070d1920900000364192010000070cd920a000003741a201000004641920900000068d920a0000000019106000000009a103000000001a1080000036419206000000001910800000000da10300000000d9103000004641920b000003741920a0000076901209000003781920900000064da20a0000076cc120a0000076cc120a000003641920a0000036419201000000651a20b0000076d0120b00000768c120a000002781920a00000364c1201000000691920900000064da20100000378192090000076cc1206
  | 9, 11 => 0x704d920a000000001910800000000da103000003781920b000003641920600000068d920600000000db10300000000d910300000068d920a0000076cc12010000076cc120a0000076cc1206000003781920600000704d920a000000651a20b00000764c12010000037819209000000691920b000000651a20b00000074da201000003781920800000074da201000000651a20b00000000d910300000364c12010000070cd9206000003741a20a000000001910600000000d91030000037819209000003781920a0000037819201
  | 9, 12 => 0xd910300000000d91030000070cd9201000003781920600000364c120100000364c12060000036419206000003741a201000003741a20600000068d920a000003781920b00000764c120a0000070cd920600000278192010000076cc12010000070cd92060000037819201000003641920a00000074da206000000009a1030000037819209000007690120900000374192060000070cd9206000004641920b00000764c12010000070cd920a000003641920a000004781920b0000076501209000002781920a0000037419206
  | 9, 13 => 0x68d920a000004741a2090000076cc120600000000db1030000070cd9206000000009a103000007690120900000364c120100000278192010000076cc1206000002781920100000764c1206000004650120b00000068d920a000003781920a00000068d920100000364c120a000003741920a00000768c120a00000364c120600000069192090000036419206000002781920a0000070d1920b0000076cc1206000003781920b00000074da20a00000764c120600000068d920a00000068d920a0000076d0120b00000000da103
  | 9, 14 => 0x19108000004781920b00000000d91030000076cc12060000076cc120a0000070cd92060000070cd9201000002781920a00000464192090000070cd9206000003741a201000000009a10300000064da20600000068d920a000003781920900000768c12060000037819201000000651a209000004741920b00000464192090000070cd920a000003741a20100000064da20a0000037419206000003741a20100000064da201000003781920b0000076cc1206000004641920b00000764c1206000003781920100000364c120a
  | 9, 15 => 0x7650120900000464192090000076d01209000003781920900000068d920a000000001910800000364c120a00000074da20100000764c120600000069192090000070d1920900000068d9201000007650120b00000064da20a0000076d0120b0000000181108000003781920600000000d9103000004781920b000000009a1030000000183108000003741a20a000007690120b00000068d920a00000000d9103000003781920100000000db1030000046419209000000751a209000004781920b000000691920b0000000019108
  | 9, 16 => 0x651a20b0000070cd9206000003741a2060000070d1920900000000d91030000070d1920b00000364c1201000000001910800000000d910300000000c2107000003641920600000000da10300000000191080000070d19209000003641920600000364192010000070cd920100000074da20100000000d9103000000001910800000064da2060000070d1920b000000009a103000003741a20a0000000019106000000018310800000364c1201000003741920100000000da1030000070cd920a00000765012090000070d1920b
  | 9, 17 => 0x4781920b0000076d0120b0000076d01209000003741a201000004781920b00000764c120600000704d920600000764c1201000000001910800000068d9201000000010110700000068d920a00000068d9206000003781920600000364c1206000003741a20a00000364192010000036419201000007650120900000074da2060000006919209000002781920a000004741a20b000007650120b00000364c120a00000378192010000037819206000003641920a0000070cd9206000003741920600000364192060000036419206
  | 9, 18 => 0x764c120600000000d9103000000651a20900000278192010000070d1920900000068d92060000037419206000003641920a0000070d1920b0000076cc120a000004641920900000765012090000076cc1201000003741920100000378192010000070cd9206000003741920100000068d920100000764c1206000003781920b000003741a20100000764c120a00000704d92060000070cd920100000704d9206000002781920a0000070cd92060000000181108000003741a201000000691920b00000074da2060000036419206
  | 9, 19 => 0x1a108000003741a2060000037419201000000751a2090000036419201000003781920b0000036419206000000651a20b0000076cc120a000003781920900000064da20100000764c120a0000070519209000002781920a00000364c12060000070cd9201000000001910600000000d910300000000d910300000000d91030000070cd920a00000000d9103000003781920a0000070cd9201000002781920a00000068d92060000076cc120600000768c1201000002781920a0000076d0120900000000da103000003741a206
  | 9, 20 => 0x64da201000003641920a00000000d910300000064da206000003781920b000002781920a00000378192090000047819209000000751a20900000764c120100000364192060000027819201000003741a20600000364c120100000378192080000036419201000000001910800000465012090000070cd920a000007051920b00000068d920a00000000da1030000070d1920b0000076501209000007650120b00000000d91030000076cc1206000004781920b00000000da1030000070cd920a0000037419206000002781920a
  | 9, 21 => 0x2781920a0000037819206000000001910800000764c120a000003641920a0000076cc120600000074da20600000704d920a00000768c120600000378192080000027819201000003781920100000000d9103000003641920100000764c120a0000076cc120a000003781920900000704d9201000000651a20b00000074da20a00000000d9103000004781920900000064da206000000018310800000764c120600000074da201000003781920900000768c1206000003641920a000000751a20b000000009a10300000068d9206
  | 9, 22 => 0x64da20a00000074da20a0000070cd920600000764c120100000764c120a000004741920b0000070d1920900000000da103000004641920900000364c1201000003781920a0000076d0120900000764c120100000000da103000003781920b0000070cd9201000000001a108000003641920a000003641920600000768c120a0000000019106000000651a209000003641920600000000da103000004741920900000074da2010000070d19209000003781920100000074da20600000064da20100000064da2060000027819201
  | 9, 23 => 0xd91030000047419209000003741920a00000068d920600000704d92060000000019108000003781920800000378192090000070cd920a00000764c120a00000000d910300000764c120600000064da20100000000d9103000002781920100000068d920600000000db1030000076d0120b00000278192010000037819206000004741a20b000000009a10300000068d92060000076cc120100000000d9103000003741a20a0000070d1920b00000000db103000003641920a000002781920a000002781920a0000070cd9201
  | 9, 24 => 0x3741920600000000d9103000002781920a0000000101107000003781920100000000d91030000076cc12010000076d012090000076cc120600000000d910300000068d920a000003641920600000000d91030000036419206000000001910800000000d9103000003781920a00000074da2010000000101107000002781920a000000009a10300000764c120a000000651a20b0000037419201000003741a201000003641920a00000000d91030000046419209000002781920a00000764c1206000003641920600000000d9103
  | 9, 25 => 0x764c120a000000001b10800000074da20a00000764c120600000378192090000070cd92010000037419206000003741a20100000064da206000000009a1030000000183108000000651a209000000751a20b000003641920a0000070cd920a0000076d0120b00000000d910300000000d9103000003781920b00000074da206000003781920800000704d92010000036419201000003781920b0000076cc120600000068d920600000765012090000070cd920600000764c1206000003741a20600000000d910300000000da103
  | 9, 26 => 0x1031070000076901209000004741a20b000004781920b000003641920100000000da10300000074da20a000003741a20a0000070cd92060000070cd9206000003781920900000000d910300000000da10300000074da201000003641920a000003641920a00000764c120a00000704d920a00000064da2010000046501209000000001a10800000764c1201000002781920a0000076cc12010000037819206000004641920b00000074da201000004641920b000003781920600000000d910300000000d9103000003741a206
  | 9, 27 => 0x768c120600000000db10300000764c1201000002781920100000000da10300000000d9103000004741a20900000364c120600000074da20600000000d9103000002781920100000764c120a00000764c120a0000076501209000007650120900000000d9103000003741920a00000074da20a000003641920a00000074da20600000764c1206000004650120900000364c120100000000da10300000000d910300000278192010000027819201000002781920a00000068d920600000000191080000076cc120a0000000181108
  | 9, 28 => 0x9a10300000000da1030000046419209000003641920600000364192010000070cd9206000003781920b00000074da20a0000037819209000004741a20900000074da20600000064da20a000000691920b000000001910800000000da103000004641920b00000068d9201000003741a201000003781920b00000000da103000002781920a000003641920a0000037419206000000001910800000364c120a000000009a103000000018310800000000d910300000364c120600000364c1206000003781920600000074da20a
  | 9, 29 => 0x70d19209000002781920a0000076501209000003741920600000764c120100000074da2010000076cc120a00000068d920100000068d92060000076cc120100000768c120600000364c120a00000068d920a00000465012090000076cc120600000704d9206000000001910800000764c1206000007650120b000007650120b000003641920a00000000d910300000074da206000003741a20a0000076d0120900000000191060000076cc120a000004641920b00000764c120a000003641920a000000009a1030000000019106
  | 9, 30 => 0x68d9201000003641920100000704d920600000364c1201000003741a20a00000000db10300000364c120600000704d9201000003781920b00000000d91030000076cc120a000004641920b00000000db10300000000da10300000074da20100000764c120a0000070cd92010000036419201000000691920b000003641920a000004650120b000003641920600000000d9103000000009a1030000070cd9206000000009a10300000068d92060000046419209000003741a20600000074da20a00000764c120a0000027819201
  | 9, 31 => 0x364c120a00000764c120100000074da20a000003641920600000068d920a00000064da20600000064da201000003781920b0000076d0120900000364c1201000000009a103000003741a201000003741920600000378192080000000019108000007051920b00000374192060000076cc12010000036419206000000001910800000074da201000000751a20b0000037819201000004641920b00000764c120100000764c120a00000000da10300000764c1206000003641920600000074da20a00000074da20a0000070519209
  | 9, 32 => 0x278192010000070d192090000070cd92060000070cd920a00000768c120a00000764c120600000364c120100000768c120600000000d9103000000001a10800000000db10300000074da20a000003781920600000364c120a00000000d910300000764c1206000000010110700000000da103000007650120b00000000c2107000000001910600000378192090000070cd9201000003741a20100000000da103000003641920600000000d910300000064da2060000037819206000000691920b00000000d910300000064da20a
  | 9, 33 => 0x37819206000004641920b00000074da20a00000000d9103000003641920600000000191080000070cd9206000000001910800000364c1206000000001a10800000074da20a0000076cc12060000000019106000000751a20900000074da201000003741a20a00000000d910300000064da2060000070519209000000001910600000000d9103000002781920a000003641920a000003641920600000764c120600000000d9103000003641920a00000364c120100000074da20600000364c120a00000704d920a000000751a20b
  | 9, 34 => 0x691920900000064da2010000000183108000002781920a00000000d910300000064da206000003741920600000000da103000000691920b000004741920b000003741a20600000000d910300000068d920600000074da20100000000da10300000074da20a00000074da206000000001b1080000000101107000004781920900000768c1201000003741a20a00000000d9103000002781920a00000364c120a00000000db103000003741a20100000764c1206000000691920900000764c120a00000064da20a00000768c1206
  | 9, 35 => 0x3741a206000002781920a0000070cd920a000003641920100000364c120100000000d910300000068d920a000000001a10800000074da20600000768c120600000064da206000000751a20b0000076cc1206000000010110700000000d91030000027819201000000018310800000704d920600000364c120a00000074da2060000076cc1206000004781920900000364c1206000000751a20b00000000d910300000464192090000070cd92060000076cc120600000074da201000003741a20a0000070d1920900000000d9103
  | 9, 36 => 0x3641920a000002781920a00000074da206000004781920b0000070cd920a0000070cd92060000070cd920600000064da2060000070cd920a000003781920600000000191080000000183108000003741a20600000764c120a0000070cd920600000074da20600000000da1030000076cc120a000003641920600000000d910300000000d91030000070d1920900000000d9103000002781920100000000d9103000003781920a00000364c120a00000764c1206000003741a20100000068d920600000064da20a00000364c1206
  | 9, 37 => 0x1910800000704d92060000070cd920a0000070d1920900000064da206000003741a20a00000000d9103000000651a20900000000d910300000764c120a00000764c1206000003741a20600000064da20600000000d910300000000d91030000070cd920600000000da103000003781920a000003641920600000000191060000037819208000000010110700000074da2060000047819209000000001910800000074da20a00000764c1206000003741a20a00000000d910300000000d910300000000d9103000003741a201
  | 9, 38 => 0x76cc12060000027819201000003781920a000000001910600000068d920600000764c120a00000064da20a000003741a20a00000364c120a0000036419206000003781920800000364c120a00000000d9103000003781920b000003781920900000364192060000076cc120600000764c1201000000001a1080000000019106000000651a209000003641920a00000364c1206000004650120b0000027819201000000001a10800000000d9103000003781920a0000076cc120100000364c120a00000000d910300000764c1206
  | 9, 39 => 0x764c1206000003741920600000074da20a000000001a1080000037819206000003741a206000000018110800000000db103000003741a206000000691920900000064da206000003741a20a000004650120b00000000191080000070cd920600000000d9103000002781920a0000070cd920a00000074da206000003741a20a00000364c12010000070cd920a00000364c1206000007650120900000064da206000003741920600000000191080000070cd92010000070cd9206000003781920900000764c1206000004741a20b
  | 9, 40 => 0x378192060000070cd920600000000da10300000364c12060000070cd920600000364c120600000000d91030000000103107000003641920600000364192060000070cd9206000002781920100000364192060000000019108000000001910800000000db103000003741a201000003641920600000000da103000003741a20600000074da2060000036419201000003641920600000364c120600000704d92060000076d01209000003781920b00000000d910300000000d9103000004650120b0000076501209000003641920a
  | 9, 41 => 0x76cc1206000003781920a00000764c120100000764c120600000064da20600000068d920600000000da10300000000d910300000378192010000046419209000003741a20600000000d910300000000d910300000000191080000070cd920600000000d910300000364c12060000037819206000000018310800000068d920100000764c120600000000d910300000764c120600000364192010000036419206000003741a20600000378192090000000019108000000009a10300000764c120100000764c12060000076d01209
  | 9, 42 => 0xd9103000003641920600000001811080000070cd920a000000001a10800000000d9103000000001910800000364c1206000000651a209000000018310800000000d910300000000da103000000009a10300000704d9206000003781920a00000000d91030000070cd920a0000070cd920a000000001910800000000d9103000003641920600000000d910300000068d92060000070cd9201000003741a20600000000191080000070cd92060000070d1920900000704d9201000000009a1030000070cd920600000364c1206
  | 9, 43 => 0x68d9206000000018110800000364c120a00000074da20600000764c1206000000691920900000000d910300000768c120600000064da20600000000c210700000064da20600000000d9103000007650120900000764c1206000004781920b0000000101107000003641920600000364c120600000000d910300000074da20600000064da20600000069192090000000183108000000001910600000000da103000000009a10300000074da20100000000d910300000074da206000003641920a00000364c120a0000046419209
  | 9, 44 => 0x764c120600000000d910300000000c2107000000001910600000000d910300000000d9103000003741920600000000d9103000003741a20600000068d920600000068d9206000003641920600000000d9103000000010110700000064da20a000000009a10300000704d920600000378192080000036419206
  | 10, 0 => 0xda10a000000001a10b00000000c110a000000011a10b0000000019106000000001910a000000011910b000000001910b0000000019101000000001a10600000000c110600000000d9101000000011a109000000001a10a0000000019106000000001a10a0000000019106000000010110b000000001910900000000d9106000000010110b000000001910a0000000019109000000001910600000000c11060000000019106000000001a10600000000d9101000000001a109000000001a10600000000c110a00000000c110a
  | 10, 1 => 0xd9101000000001a10b000000010110b00000000da106000000001910a00000000c1106000000001910a000000011910900000000c11010000000119109000000001a101000000010110b000000001910800000000d9101000000010110b00000000da10a00000000da10a0000000019101000000001a10a00000000c1101000000001910a000000001910a0000000101109000000001a108000000001a1060000000119109000000011910900000000da106000000001910100000000c110100000000c1106000000011a109
  | 10, 2 => 0xd910a0000000119109000000001910a00000000da101000000010110b000000001910b000000001910a00000000c11060000000019109000000001910100000000da10a000000001a10a00000000c110100000000d910600000000c1106000000001a10b0000000019108000000001910b00000000da106000000001a101000000001a10b000000001a108000000001a10b000000001910a000000001910a000000001910a00000000d910a00000000d910600000000d9106000000011a10b00000000c110a00000000d9106
  | 10, 3 => 0xd91010000000019106000000001910b00000000c1101000000001910600000000d910100000000da10a000000001a1010000000019101000000011910b00000000d910100000000c110a000000001a10b00000000c110100000000d9106000000011a10b00000000da10100000000da10100000000c1101000000011a10b0000000019101000000001a10b000000001910a0000000019106000000011a10b000000001a10600000000c1101000000001a101000000001a106000000010110b000000011a109000000011a109
  | 10, 4 => 0xc110a00000000c110100000000da101000000001910b000000001a10800000000d910a00000000d910600000000c110100000000c1106000000001a10100000000da1010000000019106000000001910a000000010110900000000d910a000000001910b000000011a10b000000001910900000000d9101000000011a10b000000001910600000000da106000000001910600000000c110100000000d910a00000000da1010000000019106000000001a10a00000000d910a00000000da106000000001a10b000000001a101
  | 10, 5 => 0x1910600000000c11010000000019109000000001910a00000000da106000000001a106000000011a10900000000c110100000000d910600000000d910a000000001910100000000d910100000000c110a000000001a10100000000d9106000000001a10a000000001910900000000da101000000001a1090000000119109000000011a10b000000001a101000000011910900000000d910600000000d9103000000001a101000000001a10b00000000c110a000000001a10900000000d910a00000000da10a000000001910b
  | 10, 6 => 0x11910900000000d910100000000da101000000001a10b000000001910a00000000c110600000000da10a000000011910b000000011a10b00000000d910a00000000da101000000001a106000000001910b00000000d910a0000000019106000000001a10100000000da10a00000000d910100000000da10300000000c110100000000d9103000000001910a000000011a10b000000001a101000000011910900000000c110600000000d910a00000000d910a000000001a10a00000000da10100000000c110a00000000da101
  | 10, 7 => 0x11a10b000000001a10b0000000019101000000001910600000000c1106000000001910b00000000d9106000000001910600000000c110100000000d910600000000da1060000000019101000000001910600000000d9106000000011910b00000000d91010000000019106000000011910b00000000da103000000001910b00000000d910100000000d910a000000001910100000000d91060000000019108000000011910900000000c110100000000da106000000001a10600000000d910a000000001a10100000000d910a
  | 10, 8 => 0x1a10a00000000d910600000000c110600000000d910a000000001910a000000001a10900000000c110a00000000d91060000000019101000000001a10900000001011090000000101109000000001910900000000da106000000001a1060000000119109000000010110900000000da101000000001a10600000000da101000000001910100000000d9106000000001a106000000001910a000000001a10b00000000c110600000000d9103000000001910900000000d9106000000011a10b000000001a10100000000d910a
  | 10, 9 => 0xd91060000000019101000000001a10a00000000d910a00000000c110100000000c110a00000000c110100000000da10a000000001a10100000000c110a00000000da1060000000019106000000011910b00000000c110a00000000da106000000001a10100000000da10a000000001a10600000000da10100000000c110100000000d9106000000011a109000000001a10a000000011a10900000000da10100000000d910a000000010110b000000001a10600000000da106000000011a10900000000c110a00000000da106
  | 10, 10 => 0x1910600000000d910300000000da10a00000000c110a00000000c1106000000001a10600000000c1101000000001a106000000011910b00000000c110a00000000c110600000000da106000000001a10100000000da103000000001910a00000000d910a00000000da10a000000001a10a00000000c11060000000019106000000001a10600000000d910100000000c110a000000001a10a00000000da101000000011910b00000000d9106000000001910600000000c1106000000001910a00000000d91010000000019106
  | 10, 11 => 0x19109000000001a10a00000000c110a00000000da10a00000000da10100000000c1106000000010110b00000000d910a00000000d9103000000001a10800000000c110a00000000da10600000000da106000000011910b000000001910600000000d9106000000001a10a0000000019106000000011910b00000000d910100000000da1060000000119109000000001910a000000001910600000000da10a000000001a10a00000000c110a000000001a101000000001a10100000000da1060000000019101000000001a106
  | 10, 12 => 0xda10600000000da10600000000c110600000000da106000000001a10600000000da10100000000da106000000001a106000000001a10600000000c1106000000001a10600000000da10a00000000c110600000000c110600000000d9103000000011a10b0000000019106000000001a10100000000c1106000000001a10600000000da10a000000001a10a00000000c110100000000c11060000000019109000000001a10a00000000da10300000000da10a00000000da103000000001a10b000000001910800000000c110a
  | 10, 13 => 0xd9106000000001a10600000000c110600000000da1030000000019106
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry true dom_238 roots_238 7 s ws hint
  | 1 => checkCutEntry true dom_253 roots_253 11 s ws hint
  | 2 => checkCutEntry true dom_246 roots_246 9 s ws hint
  | 3 => checkCutEntry true dom_254 roots_254 10 s ws hint
  | 4 => checkCutEntry true dom_230 roots_230 6 s ws hint
  | 5 => checkCutEntry true dom_118 roots_118 6 s ws hint
  | 6 => checkCutEntry true dom_247 roots_247 11 s ws hint
  | 7 => checkCutEntry true dom_127 roots_127 9 s ws hint
  | 8 => checkCutEntry true dom_239 roots_239 10 s ws hint
  | 9 => checkCutEntry true dom_191 roots_191 11 s ws hint
  | 10 => checkCutEntry true dom_251 roots_251 11 s ws hint
  | 11 => checkCutEntry true dom_223 roots_223 11 s ws hint
  | 12 => checkCutEntry true dom_231 roots_231 7 s ws hint
  | _ => false
theorem checkCutByIdx_sound {v ys hint} (hc : checkCutByIdx v ys hint = true) : ¬ RunD true dom_255 goalM v ys := by
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_238 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_253 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_246 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_254 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_230 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_118 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_247 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_127 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_239 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_191 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_251 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_223 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_231 _ hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (let i0 := cidx0H s h; decide (i0 < CN0 s) && (ch0At s i0 == h) && checkCutByIdx s ws (fld (CV0 s (i0 / 128)) 8 (i0 % 128))) ||
  (let i := cidxH s h; decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32)))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {v ys} (h : cutHitH v (hk 0 ys) ys = true) : ¬ RunD true dom_255 goalM v ys := by
  unfold cutHitH at h
  rw [Bool.or_eq_true] at h
  rcases h with h0 | h1
  · simp only [Bool.and_eq_true] at h0; exact checkCutByIdx_sound h0.2
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2

theorem cutHit_sound {v ys} (h : cutHit v ys = true) : ¬ RunD true dom_255 goalM v ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_255 == dom_255) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_255 goalM v ys) : RunD true dom_255 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar true dom_255 goalM mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
private theorem z5 : ∀ i, 0 ≤ i → i < 0 → Z 5 i = true := by omega
private theorem z6 : ∀ i, 0 ≤ i → i < 0 → Z 6 i = true := by omega
private theorem z7 : ∀ i, 0 ≤ i → i < 0 → Z 7 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 6 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 6 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 21 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 21 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 18 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 18 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11 : ∀ i, 0 ≤ i → i < 5 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 5 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z12 : ∀ i, 0 ≤ i → i < 1 → Z 12 i = true := span_ok (by decide +kernel : span (Z 12) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 12) : ∀ i < NN s, Z s i = true := by
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
  · exact fun i hi => z12 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr true dom_255 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 7 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 12) (h : RunD true dom_255 goalM s xsM) : False := by
  have hmin : 7 ≤ s := by
    have hl := run_len h; change 8 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower true dom_255 roots_255 goal_255 13 := by
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

theorem lowS_255 : Lower true dom_255 roots_255 goal_255 13 := S_255.noCircuit

theorem goal_eq_f : ∀ r : Fin 256, goal_255.testBit r.val = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) (pt8 r.val) := by
  decide +kernel

theorem lb_with_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x)
    (hhas : ∃ g ∈ gates, isNotGate g = true) : 14 ≤ gates.length := by
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

def witGates : List PEqualNP.CircuitLowerBounds.Gate := [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [8, 9] }, { op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [11, 3] }, { op := GateOp.or, inputs := [12, 5] }, { op := GateOp.and, inputs := [7, 13] }, { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [15, 6] }, { op := GateOp.and, inputs := [4, 16] }, { op := GateOp.and, inputs := [0, 3] }, { op := GateOp.or, inputs := [10, 14] }, { op := GateOp.or, inputs := [19, 17] }, { op := GateOp.or, inputs := [20, 18] }]

theorem wit_mono : ∀ g ∈ witGates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_eval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨witGates, 21⟩ (List.ofFn x) = (fun x : Fin 8 → Bool => decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) x := by
  decide +kernel

theorem main : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfan _h1not hev
  by_cases hhas : ∃ g ∈ gates, isNotGate g = true
  · have hfan' : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨h1, h2⟩ := hfan g hg
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 | h1 <;> simp [h1]
    have hlb : 14 ≤ gates.length := lb_with_not gates o hfan' hev hhas
    refine ⟨witGates, 21, wit_mono, ?_, wit_eval⟩
    have hlen : witGates.length = 14 := rfl
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

end PEqualNP.Outside.L_meta_14700_aux

theorem PEqualNP.Outside.L_meta_14700 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := PEqualNP.Outside.L_meta_14700_aux.main
