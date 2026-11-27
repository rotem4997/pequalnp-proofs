import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2826

abbrev Ref := ℕ × Bool

def read (v : List Bool) (r : Ref) : Bool := v.getD r.1 false != r.2

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def push (v : List Bool) (g : BinaryGate) := v ++ [g.op (v.getD g.left false) (v.getD g.right false)]

def signed (g : BinaryGate) : Prop := ∃ a b : Bool, g.op = fun x y => x == a && y == b

def cost (g : Gate) : ℕ := by
  letI := lineDegreeGateOpDecEq
  exact if g.op = GateOp.not then 1 else 0

lemma read_push (v : List Bool) (r : Ref) (h : r.1 < v.length) (g : BinaryGate) :
    read (push v g) r = read v r := by
  unfold read push
  rw [List.getD_append _ _ _ _ h]

lemma sign_rule (x y a b isOr : Bool) :
    ((((x == (a == isOr)) && (y == (b == isOr))) != isOr)) =
      (if isOr then ((x != a) || (y != b)) else ((x != a) && (y != b))) := by
  cases x <;> cases y <;> cases a <;> cases b <;> cases isOr <;> decide

lemma gadget (g : Gate) (basis : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (rho : ℕ → Ref) (m : ℕ) (hz : 10 < m) (bound : ∀ i, (rho i).1 < m) :
    ∃ (add : List BinaryGate) (r : Ref), (∀ q ∈ add, signed q) ∧
      add.length + cost g ≤ 1 ∧ r.1 < m + add.length ∧
      ∀ (u v : List Bool), v.length = m → v.getD 10 false = false →
        (∀ i, read v (rho i) = u.getD i false) →
        (∀ p : Ref, p.1 < m → read (add.foldl push v) p = read v p) ∧
          read (add.foldl push v) r = g.op.eval (g.inputs.map fun i => u.getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨ops, len⟩ := basis
  change op = .and ∨ op = .or ∨ op = .not at ops
  change ins.length ≤ 2 at len
  have emit (a b : Ref) (ha : a.1 < m) (hb : b.1 < m) (d : Bool) (non : op ≠ .not)
      (sem : ∀ (u v : List Bool), v.getD 10 false = false →
        (∀ i, read v (rho i) = u.getD i false) →
        (if d then (read v a || read v b) else (read v a && read v b)) =
          op.eval (ins.map fun i => u.getD i false)) :
      ∃ (add : List BinaryGate) (r : Ref), (∀ q ∈ add, signed q) ∧
        add.length + cost ⟨op, ins⟩ ≤ 1 ∧ r.1 < m + add.length ∧
        ∀ (u v : List Bool), v.length = m → v.getD 10 false = false →
          (∀ i, read v (rho i) = u.getD i false) →
          (∀ p : Ref, p.1 < m → read (add.foldl push v) p = read v p) ∧
            read (add.foldl push v) r = op.eval (ins.map fun i => u.getD i false) := by
    let q : BinaryGate := ⟨fun x y => x == (a.2 == d) && y == (b.2 == d), a.1, b.1⟩
    refine ⟨[q], (m,d), ?_, by simp [cost,non], by simp, ?_⟩
    · simpa only [List.mem_singleton, forall_eq] using
        (show signed q from ⟨a.2 == d,b.2 == d,rfl⟩)
    · intro u v lv z h
      refine ⟨fun p hp => read_push v p (lv ▸ hp) q, ?_⟩
      change (((v ++ [_]).getD m false) != d) = _
      rw [List.getD_append_right _ _ _ _ (Nat.le_of_eq lv), lv, Nat.sub_self]
      exact (sign_rule _ _ _ _ d).trans (sem u v z h)
  rcases ops with hop | hop | hop
  · subst op
    cases ins with
    | nil => exact emit (10,true) (10,true) hz hz false (by intro e; cases e) (by intro u v z h; simp only [read, Prod.fst, Prod.snd, z]; simp [GateOp.eval])
    | cons i is =>
      cases is with
      | nil => exact emit (rho i) (10,true) (bound i) hz false (by intro e; cases e) (by intro u v z h; simp only [Bool.false_eq_true, if_false, h]; simp only [read, Prod.fst, Prod.snd, z]; simp [GateOp.eval])
      | cons j js =>
        cases js with
        | nil => exact emit (rho i) (rho j) (bound i) (bound j) false (by intro e; cases e) (by intro u v z h; simp [h,GateOp.eval])
        | cons k ks => simp at len
  · subst op
    cases ins with
    | nil => exact emit (10,false) (10,false) hz hz true (by intro e; cases e) (by intro u v z h; simp only [read, Prod.fst, Prod.snd, z]; simp [GateOp.eval])
    | cons i is =>
      cases is with
      | nil => exact emit (rho i) (10,false) (bound i) hz true (by intro e; cases e) (by intro u v z h; simp only [if_true,h]; simp only [read, Prod.fst, Prod.snd, z]; simp [GateOp.eval])
      | cons j js =>
        cases js with
        | nil => exact emit (rho i) (rho j) (bound i) (bound j) true (by intro e; cases e) (by intro u v z h; simp [h,GateOp.eval])
        | cons k ks => simp at len
  · subst op
    cases ins with
    | nil =>
      exact ⟨[], (10,true), by simp, by simp [cost], by simpa using hz,
        by intro u v lv z h; exact ⟨fun _ _ => rfl, by change (v.getD 10 false != true) = true; rw [z]; rfl⟩⟩
    | cons i tail =>
      refine ⟨[], ((rho i).1, !(rho i).2), by simp, by simp [cost], by simpa using bound i, ?_⟩
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
    ∃ (bs : List BinaryGate) (rho : ℕ → Ref), (∀ q ∈ bs, signed q) ∧
      bs.length + count gs ≤ gs.length ∧
      (∀ i, (rho i).1 < 11 + bs.length) ∧
      ∀ x : List Bool, x.length = 10 → ∀ i,
        read (bs.foldl push (x ++ [false])) (rho i) = (gs.foldl step x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], fun i => (min i 10,false), by simp, by simp [count], by intro i; simp, ?_⟩
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
    obtain ⟨bs, rho, sig, size, bounds, sim⟩ := ih basis'
    obtain ⟨add, r, sig', cost', br, sound⟩ := gadget g
      (by simpa using basis g (by simp)) rho (11 + bs.length) (by omega) bounds
    let k := 10 + gs.length
    refine ⟨bs ++ add, fun i => if i = k then r else rho i, ?_, ?_, ?_, ?_⟩
    · intro q h
      rcases List.mem_append.mp h with left | right
      · exact sig q left
      · exact sig' q right
    · simp only [List.length_append,List.length_singleton,count,List.map_append,List.sum_append,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at *
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

end PEqualNP.Outside.L_meta_2826

theorem PEqualNP.Outside.L_meta_2826 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → ∃ (x3 : PEqualNP.MetaComplexity.BinaryCircuit) (x4 : Bool), (∀ x5 ∈ x3.gates, ∃ (x7 : Bool) (x8 : Bool), x5.op = fun (x9 x10 : Bool) => x9 == x7 && x10 == x8) ∧ x3.size + PEqualNP.NotBracket.notCount x1 ≤ x1.size ∧ ∀ (x5 : List Bool), x5.length = (10 : ℕ) → (x3.eval (x5 ++ [Bool.false]) != x4) = x1.eval x5 := by
  intro C hf
  obtain ⟨bs, rho, gates, cost, _, sim⟩ := PEqualNP.Outside.L_meta_2826.translate C.gates hf
  refine ⟨⟨bs, (rho C.output).1⟩, (rho C.output).2, gates, ?_, fun x len => sim x len C.output⟩
  rw [PEqualNP.Outside.L_meta_2826.countEq] at cost
  exact cost
