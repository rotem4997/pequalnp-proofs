import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open scoped Classical

-- M is the number of distinct primary wires seen on the marked inputs.
-- A changing two-input gate adds at most one wire to the backward support.
-- Only populations larger than forty-four times M minus one remain.
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3686_418
  (support : ∀ (n : ℕ) (C : Circuit) (F : Finset (Fin n → Bool)) (V : Finset (Fin n)),
    Monotone2 C →
    (∀ i ∈ V, ∃ z ∈ F, circuitFun n C z ≠ circuitFun n C (Function.update z i false)) →
    V.card ≤ Fintype.card {j : Fin C.size //
      (C.wires (List.replicate n false)).getD (n+j.val) false = false ∧
      ∃ z ∈ F, gateVal n C j.val z = true} + 1)
  (dense : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
    N=q*q+q+1 →
    (∀ l, Fintype.card {p // I p l}=q+1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsMinimalMonoCircuit (N+N) C →
    (∀ s : Finset (Fin N), s.card ≤ q → C.eval (List.ofFn (Fin.addCases
      (fun p => decide (¬ ∃ l ∈ s, I p l)) (fun l => decide (l ∈ s)))) = false) →
    let pair := fun p l : Fin N => pairInput (Fin.castAdd N p) (Fin.natAdd N l)
    let D : Circuit := ⟨C.gates.map (fun g =>
      if g.op.eval [] = true ∧ g.inputs.length = 2 ∧
        (g.inputs.all fun i => decide (0 < (C.lineDegrees (N+N) (Finset.Ico N (N+N))).getD i 0)) = true
      then ⟨.or,[]⟩ else g), C.output⟩
    ∀ T : Fin N → Finset (Fin N),
    (∀ l p, p ∈ T l → I p l ∧ C.eval (List.ofFn (pair p l)) = true ∧ D.eval (List.ofFn (pair p l)) = false) →
    44 * (Fintype.card {j : Fin (N+N) // ∃ l, ∃ p ∈ T l, pair p l j = true} - 1) <
      ∑ l, (T l).card →
    ∑ l, (T l).card ≤ 44 * Fintype.card {j : Fin C.size //
      (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
      ∃ l, ∃ p ∈ T l, gateVal (N+N) C j.val (pair p l) = true}) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   x2 = (x1 * x1 + x1).succ →     (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →       (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →         PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →           have x10 : Finset (Fin x2) → Fin (x2 + x2) → Bool := fun (x10 : Finset (Fin x2)) (x11 : Fin (x2 + x2)) => Fin.addCases (fun (x12 : Fin x2) => Decidable.decide ¬∃ x13 ∈ x10, x3 x12 x13) (fun (x12 : Fin x2) => Decidable.decide (x12 ∈ x10)) x11;           (∀ (x11 : Finset (Fin x2)), x11.card ≤ x1 → x5.eval (List.ofFn (x10 x11)) = Bool.false) →             have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };             have x13 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x13 x14 : Fin x2) => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x2 x13) (Fin.natAdd x2 x14);             ∀ (x14 : Fin x2 → Finset (Fin x2)), (∀ (x15 x16 : Fin x2), x16 ∈ x14 x15 → x3 x16 x15 ∧ x5.eval (List.ofFn (x13 x16 x15)) = Bool.true ∧ x12.eval (List.ofFn (x13 x16 x15)) = Bool.false) → (22 : ℕ) * Fintype.card { x16 : Fin x2 // (x14 x16).Nonempty } < ∑ x16 : Fin x2, (x14 x16).card → ∑ x17 : Fin x2, (x14 x17).card ≤ (44 : ℕ) * Fintype.card { x17 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x17) Bool.false = Bool.false ∧ ∃ (x18 : Fin x2), ∃ x19 ∈ x14 x18, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 (↑x17) (x13 x19 x18) = Bool.true } := by
  classical
  intro q N I inst C order cols unique minimal test sound cut pair T valid many
  let F := Finset.univ.filter (fun z : Fin (N+N) → Bool => ∃ l, ∃ p ∈ T l, z = pair p l)
  have memF (z) : z ∈ F ↔ ∃ l, ∃ p ∈ T l, z = pair p l := by simp [F]
  let V := Finset.univ.filter (fun j => ∃ l, ∃ p ∈ T l, pair p l j = true)
  have accept (l p) (hp : p ∈ T l) := (valid l p hp).2.1
  by_cases thick : 44 * (V.card-1) < ∑ l, (T l).card
  · apply dense q N I C order cols unique minimal sound T valid
    rwa [Fintype.card_subtype]
  have positive : 0 < q := by
    by_contra! zero
    have each (l : Fin N) : (T l).card ≤ if (T l).Nonempty then 22 else 0 := by
      split_ifs with h
      · have inc : T l ⊆ Finset.univ.filter (fun p => I p l) :=
          fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(valid l p hp).1⟩
        have hc := Finset.card_le_card inc
        have c := cols l
        rw [Fintype.card_subtype] at c
        omega
      · simp [Finset.not_nonempty_iff_eq_empty.mp h]
    have total := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => each l)
    rw [Fintype.card_subtype] at many
    simp [Finset.sum_ite, Nat.mul_comm] at total many
    omega
  let evalGate (g : Gate) (w : List Bool) :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  let run (gates : List Gate) (w : List Bool) :=
    gates.foldl (fun s g => s ++ [evalGate g s]) w

  have push (l : List Gate) (g : Gate) (w : List Bool) :
      run (l ++ [g]) w = run l w ++ [evalGate g (run l w)] := by
    simp [run, List.foldl_append]

  have width (l : List Gate) (w : List Bool) :
      (run l w).length = w.length + l.length := by
    induction l using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton l g ih => simp [push, ih, Nat.add_assoc]

  have read_push (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    rcases lt_trichotomy i w.length with h | h | h
    · rw [List.getD_append _ _ _ _ h, ite_eq_right (ne_of_lt h)]
    · subst i
      simp
    · rw [ite_eq_right (ne_of_gt h), List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

  have run_mono (gs : List Gate)
      (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (x y : List Bool) (len : x.length=y.length)
      (le : ∀ i, x.getD i false=true → y.getD i false=true) :
      ∀ i, (run gs x).getD i false=true → (run gs y).getD i false=true := by
    induction gs using List.reverseRecOn with
    | nil => exact le
    | append_singleton gs g ih =>
      have prev := ih (fun a h => mono a (by simp [h]))
      intro i h
      rw [push,read_push,width] at h ⊢
      rw [←len]
      split_ifs at h ⊢ with eq
      · rcases mono g (by simp) with op | op
        · dsimp only [evalGate] at h ⊢
          rw [op] at h ⊢
          change (g.inputs.map (fun j => (run gs x).getD j false)).all id = true at h
          change (g.inputs.map (fun j => (run gs y).getD j false)).all id = true
          simp only [List.all_eq_true,List.mem_map] at h ⊢
          intro b hb
          obtain ⟨k,hk,rfl⟩ := hb
          apply prev
          exact h _ ⟨k,hk,rfl⟩
        · dsimp only [evalGate] at h ⊢
          rw [op] at h ⊢
          change (g.inputs.map (fun j => (run gs x).getD j false)).any id = true at h
          change (g.inputs.map (fun j => (run gs y).getD j false)).any id = true
          simp only [List.any_eq_true,List.mem_map] at h ⊢
          obtain ⟨b,⟨k,hk,rfl⟩,on⟩ := h
          exact ⟨_,⟨k,hk,rfl⟩,prev k on⟩
      · exact prev _ h

  have typed_mono {n : ℕ} (C : Circuit) (mono : Monotone2 C)
      (x y : Fin n → Bool) (le : ∀ j, x j=true → y j=true) (i : ℕ) :
      (C.wires (List.ofFn x)).getD i false=true → (C.wires (List.ofFn y)).getD i false=true := by
    apply run_mono C.gates (fun g hg => (mono g hg).1) _ _ (by simp) _ i
    intro k
    by_cases hk : k<n
    · simpa [List.getD_eq_getElem?_getD,hk] using le ⟨k,hk⟩
    · simp [List.getD_eq_getElem?_getD,hk]

  have monoEval (x y : Fin (N+N) → Bool) (le : ∀ i, x i=true → y i=true) :
      C.eval (List.ofFn x)=true → C.eval (List.ofFn y)=true :=
    typed_mono C minimal.1 x y le C.output
  have pivot : ∀ i ∈ V, ∃ z ∈ F, circuitFun (N+N) C z ≠ circuitFun (N+N) C (Function.update z i false) := by
    intro i hi
    obtain ⟨l,p,hp,hot⟩ := (Finset.mem_filter.mp hi).2
    refine ⟨pair p l,(memF _).2 ⟨l,p,hp,rfl⟩,?_⟩
    have yes := accept l p hp
    change C.eval (List.ofFn _) ≠ C.eval (List.ofFn _)
    rw [yes]
    intro bad
    have equal : i = Fin.castAdd N p ∨ i = Fin.natAdd N l := by
      exact of_decide_eq_true hot
    rcases equal with rfl | rfl
    · have no := sound {l} (by simp;omega)
      have on := monoEval (Function.update (pair p l) (Fin.castAdd N p) false) (test {l}) (by
        intro k hk
        by_cases e : k = Fin.castAdd N p
        · simp [e] at hk
        rw [Function.update_of_ne e] at hk
        have eq : k = Fin.natAdd N l := (of_decide_eq_true hk).resolve_left e
        subst k
        dsimp only [test]
        rw [Fin.addCases_right]
        simp) bad.symm
      rw [no] at on
      contradiction
    · have no := sound ∅ (by simp)
      have on := monoEval (Function.update (pair p l) (Fin.natAdd N l) false) (test ∅) (by
        intro k hk
        by_cases e : k = Fin.natAdd N l
        · simp [e] at hk
        rw [Function.update_of_ne e] at hk
        have eq : k = Fin.castAdd N p := (of_decide_eq_true hk).resolve_right e
        subst k
        dsimp only [test]
        rw [Fin.addCases_left]
        simp) bad.symm
      rw [no] at on
      contradiction
  have cap := support (N+N) C F V minimal.1 pivot
  rw [Fintype.card_subtype] at cap ⊢
  have same : (Finset.univ.filter (fun j : Fin C.size =>
    (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
      ∃ z ∈ F, gateVal (N+N) C j.val z = true)) =
    Finset.univ.filter (fun j : Fin C.size =>
    (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
      ∃ l, ∃ p ∈ T l, gateVal (N+N) C j.val (pair p l) = true) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨z,mem,hz⟩
      obtain ⟨l,p,hp,rfl⟩ := (memF z).1 mem
      exact ⟨l,p,hp,hz⟩
    · rintro ⟨l,p,hp,hz⟩
      exact ⟨_,(memF _).2 ⟨l,p,hp,rfl⟩,hz⟩
  rw [same] at cap
  omega
