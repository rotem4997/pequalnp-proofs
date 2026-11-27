import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_7227

abbrev Ref := ℕ × Bool

def read (v : List Bool) (r : Ref) : Bool := v.getD r.1 false != r.2

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def push (v : List Bool) (g : BinaryGate) := v ++ [g.op (v.getD g.left false) (v.getD g.right false)]

def good (S : Finset ℕ) (g : BinaryGate) : Prop :=
  ∃ (a : Bool) (b : Bool), (a = true → g.left ∈ S) ∧ (b = true → g.right ∈ S) ∧
    Monotone fun (p : Bool × Bool) => g.op (p.1 != a) (p.2 != b)

lemma good_mono {S S' : Finset ℕ} (h : S ⊆ S') {g : BinaryGate} : good S g → good S' g := by
  rintro ⟨a, b, ha, hb, m⟩
  exact ⟨a, b, fun e => h (ha e), fun e => h (hb e), m⟩

lemma mono2 (f : Bool → Bool → Bool)
    (h : ∀ a1 a2 b1 b2 : Bool, a1 ≤ b1 → a2 ≤ b2 → f a1 a2 ≤ f b1 b2) :
    Monotone fun p : Bool × Bool => f p.1 p.2 := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ hab
  rw [Prod.mk_le_mk] at hab
  exact h a1 a2 b1 b2 hab.1 hab.2

def cost (g : Gate) : ℕ := by
  letI := lineDegreeGateOpDecEq
  exact if g.op = GateOp.not then 1 else 0

lemma read_push (v : List Bool) (r : Ref) (h : r.1 < v.length) (g : BinaryGate) :
    read (push v g) r = read v r := by
  unfold read push
  rw [List.getD_append _ _ _ _ h]

lemma flip2 (x a : Bool) : ((x != a) != a) = x := by
  cases x <;> cases a <;> rfl

lemma gadget (g : Gate) (basis : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (rho : ℕ → Ref) (m : ℕ) (hz : 10 < m) (bound : ∀ i, (rho i).1 < m) (S : Finset ℕ)
    (pol : ∀ i, (rho i).2 = true → (rho i).1 ∈ S) :
    ∃ (add : List BinaryGate) (r : Ref) (S' : Finset ℕ), S ⊆ S' ∧ S'.card ≤ S.card + cost g ∧
      (∀ (j : ℕ) (q : BinaryGate), add[j]? = some q → q.left < m + j ∧ q.right < m + j ∧ good S' q) ∧
      (r.2 = true → r.1 ∈ S') ∧
      add.length + cost g ≤ 1 ∧ r.1 < m + add.length ∧
      ∀ (u v : List Bool), v.length = m → v.getD 10 false = false →
        (∀ i, read v (rho i) = u.getD i false) →
        (∀ p : Ref, p.1 < m → read (add.foldl push v) p = read v p) ∧
          read (add.foldl push v) r = g.op.eval (g.inputs.map fun i => u.getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨ops, len⟩ := basis
  change op = .and ∨ op = .or ∨ op = .not at ops
  change ins.length ≤ 2 at len
  have emit (a b : Ref) (ha : a.1 < m) (hb : b.1 < m) (sa : a.2 = true → a.1 ∈ S)
      (sb : b.2 = true → b.1 ∈ S) (f : Bool → Bool → Bool)
      (mono : Monotone fun p : Bool × Bool => f p.1 p.2) (non : op ≠ .not)
      (sem : ∀ (u v : List Bool), v.getD 10 false = false →
        (∀ i, read v (rho i) = u.getD i false) →
        f (read v a) (read v b) = op.eval (ins.map fun i => u.getD i false)) :
      ∃ (add : List BinaryGate) (r : Ref) (S' : Finset ℕ), S ⊆ S' ∧ S'.card ≤ S.card + cost ⟨op, ins⟩ ∧
        (∀ (j : ℕ) (q : BinaryGate), add[j]? = some q → q.left < m + j ∧ q.right < m + j ∧ good S' q) ∧
        (r.2 = true → r.1 ∈ S') ∧
        add.length + cost ⟨op, ins⟩ ≤ 1 ∧ r.1 < m + add.length ∧
        ∀ (u v : List Bool), v.length = m → v.getD 10 false = false →
          (∀ i, read v (rho i) = u.getD i false) →
          (∀ p : Ref, p.1 < m → read (add.foldl push v) p = read v p) ∧
            read (add.foldl push v) r = op.eval (ins.map fun i => u.getD i false) := by
    let q : BinaryGate := ⟨fun x y => f (x != a.2) (y != b.2), a.1, b.1⟩
    refine ⟨[q], (m, false), S, Finset.Subset.refl _, by omega, ?_, by simp, by simp [cost, non],
      by simp, ?_⟩
    · intro j q' hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        refine ⟨by simp [q]; omega, by simp [q]; omega, a.2, b.2, sa, sb, ?_⟩
        have e : (fun p : Bool × Bool => q.op (p.1 != a.2) (p.2 != b.2)) = fun p => f p.1 p.2 := by
          funext p
          show f ((p.1 != a.2) != a.2) ((p.2 != b.2) != b.2) = _
          rw [flip2, flip2]
        rw [e]
        exact mono
      | succ j => simp at hj
    · intro u v lv z h
      refine ⟨fun p hp => read_push v p (lv ▸ hp) q, ?_⟩
      change (((v ++ [_]).getD m false) != false) = _
      rw [List.getD_append_right _ _ _ _ (Nat.le_of_eq lv), lv, Nat.sub_self]
      change (f (v.getD a.1 false != a.2) (v.getD b.1 false != b.2) != false) = _
      rw [Bool.bne_false]
      exact sem u v z h
  have z10 : ((10 : ℕ), false).2 = true → ((10 : ℕ), false).1 ∈ S := by simp
  rcases ops with hop | hop | hop
  · subst op
    cases ins with
    | nil => exact emit (10,false) (10,false) hz hz z10 z10 (fun _ _ => true)
                    (mono2 (fun _ _ => true) (by decide)) (by intro e; cases e) (by intro u v z h; simp [GateOp.eval])
    | cons i is =>
      cases is with
      | nil => exact emit (rho i) (10,false) (bound i) hz (pol i) z10 (fun x _ => x)
                    (mono2 (fun x _ => x) (by decide)) (by intro e; cases e) (by intro u v z h; simp [h, GateOp.eval])
      | cons j js =>
        cases js with
        | nil => exact emit (rho i) (rho j) (bound i) (bound j) (pol i) (pol j) (fun x y => x && y)
                    (mono2 _ (by decide)) (by intro e; cases e) (by intro u v z h; simp [h, GateOp.eval])
        | cons k ks => simp at len
  · subst op
    cases ins with
    | nil => exact emit (10,false) (10,false) hz hz z10 z10 (fun _ _ => false)
                    (mono2 (fun _ _ => false) (by decide)) (by intro e; cases e) (by intro u v z h; simp [GateOp.eval])
    | cons i is =>
      cases is with
      | nil => exact emit (rho i) (10,false) (bound i) hz (pol i) z10 (fun x _ => x)
                    (mono2 (fun x _ => x) (by decide)) (by intro e; cases e) (by intro u v z h; simp [h, GateOp.eval])
      | cons j js =>
        cases js with
        | nil => exact emit (rho i) (rho j) (bound i) (bound j) (pol i) (pol j) (fun x y => x || y)
                    (mono2 _ (by decide)) (by intro e; cases e) (by intro u v z h; simp [h, GateOp.eval])
        | cons k ks => simp at len
  · subst op
    cases ins with
    | nil =>
      refine ⟨[], (10,true), insert 10 S, Finset.subset_insert _ _, ?_, by simp, by simp,
        by simp [cost], by simpa using hz, ?_⟩
      · have := Finset.card_insert_le 10 S
        simp only [cost, if_true]
        omega
      · intro u v lv z h
        exact ⟨fun _ _ => rfl, by change (v.getD 10 false != true) = true; rw [z]; rfl⟩
    | cons i tail =>
      refine ⟨[], ((rho i).1, !(rho i).2), insert (rho i).1 S, Finset.subset_insert _ _, ?_,
        by simp, by simp, by simp [cost], by simpa using bound i, ?_⟩
      · have := Finset.card_insert_le (rho i).1 S
        simp only [cost, if_true]
        omega
      intro u v lv z h
      refine ⟨fun _ _ => rfl, ?_⟩
      change (v.getD (rho i).1 false != !(rho i).2) = !(u.getD i false)
      rw [← h i]
      unfold read
      cases v.getD (rho i).1 false <;> cases (rho i).2 <;> decide

lemma runLength (gs : List BinaryGate) (v : List Bool) :
    (gs.foldl push v).length = v.length + gs.length := by
  induction gs generalizing v with
  | nil => simp
  | cons g t ih =>
    rw [List.foldl_cons, ih]
    simp [push,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

lemma oldLength (gs : List Gate) (u : List Bool) :
    (gs.foldl step u).length = u.length + gs.length := by
  induction gs generalizing u with
  | nil => simp
  | cons g t ih =>
    rw [List.foldl_cons, ih]
    simp [step,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

lemma preserved (gs : List BinaryGate) (v : List Bool) (i : Nat) (hi : i < v.length) :
    (gs.foldl push v).getD i false = v.getD i false := by
  induction gs generalizing v with
  | nil => rfl
  | cons q qs ih =>
    rw [List.foldl_cons, ih (push v q) (by simp [push]; omega)]
    exact List.getD_append _ _ _ _ hi

def count (gs : List Gate) := (gs.map cost).sum

lemma translate (gs : List Gate) (basis : FanInTwo (Circuit.mk gs 0)) :
    ∃ (bs : List BinaryGate) (rho : ℕ → Ref) (S : Finset ℕ),
      (∀ (j : ℕ) (q : BinaryGate), bs[j]? = some q → q.left < 11 + j ∧ q.right < 11 + j ∧ good S q) ∧
      (∀ i, (rho i).2 = true → (rho i).1 ∈ S) ∧ S.card ≤ count gs ∧
      bs.length + count gs ≤ gs.length ∧
      (∀ i, (rho i).1 < 11 + bs.length) ∧
      ∀ x : List Bool, x.length = 10 → ∀ i,
        read (bs.foldl push (x ++ [false])) (rho i) = (gs.foldl step x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], fun i => (min i 10,false), ∅, by simp, by simp, by simp, by simp [count],
      by intro i; simp, ?_⟩
    intro x len i
    change ((x ++ [false]).getD (min i 10) false != false) = x.getD i false
    by_cases hi : i < 10
    · rw [Nat.min_eq_left (by omega), List.getD_append _ _ _ _ (by omega)]
      simp
    · rw [Nat.min_eq_right (by omega), List.getD_append_right _ _ _ _ (by omega),
        List.getD_eq_default x false (by omega), len]
      rfl
  | append_singleton gs g ih =>
    have basis' : FanInTwo (Circuit.mk gs 0) :=
      fun q h => basis q (List.mem_append_left _ h)
    obtain ⟨bs, rho, S, wires, pol, scard, size, bounds, sim⟩ := ih basis'
    obtain ⟨add, r, S', sub, s'card, wires', rpol, cost', br, sound⟩ := gadget g
      (by simpa using basis g (by simp)) rho (11 + bs.length) (by omega) bounds S pol
    let k := 10 + gs.length
    have ceq : count (gs ++ [g]) = count gs + cost g := by
      simp [count, List.map_append, List.sum_append]
    refine ⟨bs ++ add, fun i => if i = k then r else rho i, S', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j q hj
      by_cases hjl : j < bs.length
      · rw [List.getElem?_append_left hjl] at hj
        obtain ⟨h1, h2, h3⟩ := wires j q hj
        exact ⟨h1, h2, good_mono sub h3⟩
      · rw [List.getElem?_append_right (by omega)] at hj
        obtain ⟨h1, h2, h3⟩ := wires' (j - bs.length) q hj
        exact ⟨by omega, by omega, h3⟩
    · intro i
      dsimp only
      split
      · exact rpol
      · exact fun e => sub (pol i e)
    · rw [ceq]; omega
    · simp only [List.length_append, List.length_singleton] at *
      rw [ceq]
      omega
    · intro i
      dsimp only
      split
      · simpa [Nat.add_assoc] using br
      · have h := bounds i
        simp only [List.length_append]
        omega
    · intro x len i
      let u := gs.foldl step x
      let v := bs.foldl push (x ++ [false])
      have lu : u.length = k := by simp [u,oldLength,len,k]
      have lv : v.length = 11 + bs.length := by simp [v,runLength,len]
      have z : v.getD 10 false = false := by
        rw [show v.getD 10 false = (x ++ [false]).getD 10 false from preserved _ _ _ (by simp [len])]
        rw [List.getD_append_right _ _ _ _ (by omega),len]
        rfl
      obtain ⟨stable, val⟩ := sound u v lv z (sim x len)
      rw [List.foldl_append, List.foldl_append]
      by_cases h : i = k
      · subst i
        simp only [if_pos rfl,List.foldl_cons,List.foldl_nil]
        change read (add.foldl push v) r = (u ++ [_]).getD k false
        rw [List.getD_append_right _ _ _ _ (Nat.le_of_eq lu),lu,Nat.sub_self]
        exact val
      · simp only [if_neg h,List.foldl_cons,List.foldl_nil]
        rw [stable (rho i) (bounds i), sim x len]
        change u.getD i false = (u ++ [_]).getD i false
        by_cases lo : i < u.length
        · exact (List.getD_append _ _ _ _ lo).symm
        · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simp; omega)]

lemma countEq (gs : List Gate) : count gs = PEqualNP.NotBracket.notCount ⟨gs,0⟩ := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : g.op = .not <;> simp [count,cost,PEqualNP.NotBracket.notCount,h] at * <;> omega

end PEqualNP.Outside.L_meta_7227

theorem PEqualNP.Outside.L_meta_7227 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     ∃ (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Finset ℕ) (x5 : Bool),       (∀ (x6 : Fin x3.gates.length),           have x7 : PEqualNP.MetaComplexity.BinaryGate := x3.gates.get x6;           x7.left < (11 : ℕ) + ↑x6 ∧ x7.right < (11 : ℕ) + ↑x6 ∧ ∃ (x8 : Bool) (x9 : Bool), (x8 = Bool.true → x7.left ∈ x4) ∧ (x9 = Bool.true → x7.right ∈ x4) ∧ Monotone fun (x10 : Bool × Bool) => x7.op (x10.1 != x8) (x10.2 != x9)) ∧         x3.output < (11 : ℕ) + x3.size ∧ (x5 = Bool.true → x3.output ∈ x4) ∧ x4.card ≤ PEqualNP.NotBracket.notCount x1 ∧ x3.size + PEqualNP.NotBracket.notCount x1 ≤ x1.size ∧ ∀ (x6 : List Bool), x6.length = (10 : ℕ) → (x3.eval (x6 ++ [Bool.false]) != x5) = x1.eval x6 := by
  intro C hf
  obtain ⟨bs, rho, S, wires, pol, scard, cost, bounds, sim⟩ :=
    PEqualNP.Outside.L_meta_7227.translate C.gates hf
  rw [PEqualNP.Outside.L_meta_7227.countEq] at cost scard
  refine ⟨⟨bs, (rho C.output).1⟩, S, (rho C.output).2, ?_, bounds C.output, pol C.output,
    scard, cost, fun x len => sim x len C.output⟩
  intro j
  exact wires j.1 (bs.get j) (by simp)
