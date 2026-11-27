import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6680

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One evaluation step of the root model: append the value of the next gate.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (stepWire w g).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false)
      else false := by
  unfold stepWire
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

-- Wire indices after the wire N has been removed.
def tau (N i : ℕ) : ℕ := if i < N then i else i - 1

def reGate (N : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (tau N)⟩

lemma eval_tau (N : ℕ) (op : GateOp) (inputs : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : inputs.length ≤ 2)
    (hN : N ∉ inputs.take (bif op.eval [false] then 1 else 2)) (wC wD : List Bool)
    (h : ∀ i : ℕ, i ≠ N → wD.getD (tau N i) false = wC.getD i false) :
    op.eval ((inputs.map (tau N)).map fun i => wD.getD i false) =
      op.eval (inputs.map fun i => wC.getD i false) := by
  rw [List.map_map]
  rcases hop with ho | ho | ho
  · subst ho
    have hN' : N ∉ inputs := by
      simpa [GateOp.eval, List.take_of_length_le hlen] using hN
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h i (fun hiN => hN' (hiN ▸ hi))
  · subst ho
    have hN' : N ∉ inputs := by
      simpa [GateOp.eval, List.take_of_length_le hlen] using hN
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h i (fun hiN => hN' (hiN ▸ hi))
  · subst ho
    cases inputs with
    | nil => rfl
    | cons a t =>
      have ha : a ≠ N := by
        intro haN
        apply hN
        simp [GateOp.eval, haN]
      simp only [GateOp.eval, List.map_cons, List.headD_cons, Function.comp_apply]
      rw [h a ha]

lemma erase_fold (N : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 ∧ N ∉ g.inputs.take (bif g.op.eval [false] then 1 else 2)) :
    ∀ (wC wD : List Bool) (k : ℕ), wC.length = N + 1 + k → wD.length = N + k →
      (∀ i : ℕ, i ≠ N → wD.getD (tau N i) false = wC.getD i false) →
      ∀ i : ℕ, i ≠ N → ((gs.map (reGate N)).foldl stepWire wD).getD (tau N i) false =
        (gs.foldl stepWire wC).getD i false := by
  induction gs with
  | nil =>
    intro wC wD k _ _ h i hi
    exact h i hi
  | cons g gs ih =>
    intro wC wD k hC hD h
    simp only [List.map_cons, List.foldl_cons]
    have hg := hgs g (by simp)
    apply ih (fun g' hg' => hgs g' (by simp [hg'])) (stepWire wC g) (stepWire wD (reGate N g))
      (k + 1)
    · simp [stepWire, hC]
      omega
    · simp [stepWire, hD]
      omega
    · intro i hi
      rw [step_getD, step_getD, hC, hD]
      have ht : tau N i = if i < N then i else i - 1 := rfl
      by_cases h1 : i < N + 1 + k
      · have h1' : tau N i < N + k := by
          rw [ht]
          split_ifs <;> omega
        simp only [h1, h1', if_true]
        exact h i hi
      · by_cases h2 : i = N + 1 + k
        · subst h2
          have h2' : tau N (N + 1 + k) = N + k := by
            rw [ht]
            split_ifs <;> omega
          rw [h2', if_neg (lt_irrefl _), if_pos rfl, if_neg (lt_irrefl _), if_pos rfl]
          exact eval_tau N g.op g.inputs hg.1 hg.2.1 hg.2.2 wC wD h
        · have h3 : ¬ (tau N i < N + k) ∧ ¬ (tau N i = N + k) := by
            rw [ht]
            split_ifs <;> omega
          simp only [h1, h2, h3.1, h3.2, if_false]

lemma main : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), PEqualNP.MetaComplexity.FanInTwo C → j < C.gates.length → C.output ≠ n + j → (∀ g ∈ C.gates, n + j ∉ g.inputs.take (bif g.op.eval [false] then 1 else 2)) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => C.eval (List.ofFn x)) (C.size - 1) := by
  intro n C j hC hj hout hread
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  have hpre : (C.gates.take j).length = j := by
    rw [List.length_take]
    omega
  have hmem_pre : ∀ g ∈ C.gates.take j, g ∈ C.gates := fun g hg => List.mem_of_mem_take hg
  have hmem_post : ∀ g ∈ C.gates.drop (j + 1), g ∈ C.gates := fun g hg => List.mem_of_mem_drop hg
  have hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have h := hC g hg
    exact ⟨by simpa using h.1, h.2⟩
  refine ⟨⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (reGate (n + j)), tau (n + j) C.output⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hC g (hmem_pre g hg)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      have h := hC g0 (hmem_post g0 hg0)
      refine ⟨h.1, ?_⟩
      simp only [reGate, List.length_map]
      exact h.2
  · simp only [Circuit.size, List.length_append, List.length_map, List.length_take,
      List.length_drop]
    omega
  · intro x
    show ((C.gates.take j ++ (C.gates.drop (j + 1)).map (reGate (n + j))).foldl stepWire
        (List.ofFn x)).getD (tau (n + j) C.output) false =
      (C.gates.foldl stepWire (List.ofFn x)).getD C.output false
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons]
    have hl : ((C.gates.take j).foldl stepWire (List.ofFn x)).length = n + j := by
      rw [foldl_len, hpre]
      simp
    refine erase_fold (n + j) (C.gates.drop (j + 1))
      (fun g hg => ⟨(hops g (hmem_post g hg)).1, (hops g (hmem_post g hg)).2,
        hread g (hmem_post g hg)⟩) _ _ 0 ?_ ?_ ?_ C.output hout
    · simp [stepWire, hl]
    · simp [hl]
    · intro i hi
      rw [step_getD, hl]
      have ht : tau (n + j) i = if i < n + j then i else i - 1 := rfl
      by_cases h1 : i < n + j
      · rw [ht]
        simp only [h1, if_true]
      · have h2 : ¬ (i = n + j) := hi
        simp only [h1, h2, if_false]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hl, ht, if_neg h1]; omega)]
        rfl

end PEqualNP.Outside.L_meta_6680

theorem PEqualNP.Outside.L_meta_6680 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x3 < x2.gates.length → x2.output ≠ x1 + x3 → (∀ x7 ∈ x2.gates, x1 + x3 ∉ List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs) → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x8 : Fin x1 → Bool) => x2.eval (List.ofFn x8)) (x2.size - (1 : ℕ)) := by
  exact PEqualNP.Outside.L_meta_6680.main
