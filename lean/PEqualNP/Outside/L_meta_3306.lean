import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3306
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def sw (A B : Finset ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | GateOp.and, [a, b] => if a ∈ B ∧ b ∈ A then g else ⟨GateOp.and, [b, a]⟩
  | _, _ => g

theorem sw_op (A B : Finset ℕ) (g : Gate) : (sw A B g).op = g.op := by
  unfold sw
  split
  · rename_i h1 h2
    split
    · rfl
    · exact h1.symm
  · rfl

theorem sw_or (A B : Finset ℕ) (g : Gate) (h : g.op = GateOp.or) : sw A B g = g := by
  unfold sw
  split
  · rename_i h1 h2
    rw [h] at h1
    cases h1
  · rfl

theorem sw_mem (A B : Finset ℕ) (g : Gate) (i : ℕ) : i ∈ (sw A B g).inputs ↔ i ∈ g.inputs := by
  unfold sw
  split
  · rename_i h1 h2
    split
    · rfl
    · rw [h2]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact or_comm
  · rfl

theorem sw_len (A B : Finset ℕ) (g : Gate) : (sw A B g).inputs.length = g.inputs.length := by
  unfold sw
  split
  · rename_i h1 h2
    split
    · rfl
    · rw [h2]; rfl
  · rfl

theorem sw_eval (A B : Finset ℕ) (g : Gate) (f : ℕ → Bool) :
    (sw A B g).op.eval ((sw A B g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  unfold sw
  split
  · rename_i h1 h2
    split
    · rfl
    · rw [h1, h2]
      simp [GateOp.eval, Bool.and_comm]
  · rfl

theorem sw_and (A B : Finset ℕ) (g : Gate) (a b : ℕ) (hop : g.op = GateOp.and)
    (hin : g.inputs = [a, b]) (h : a ∈ A ∧ b ∈ B ∨ a ∈ B ∧ b ∈ A) :
    ∃ c d, (sw A B g).inputs = [c, d] ∧ c ∈ B ∧ d ∈ A := by
  unfold sw
  split
  · rename_i a' b' h1 h2
    rw [hin] at h2
    simp only [List.cons.injEq, and_true] at h2
    obtain ⟨rfl, rfl⟩ := h2
    split
    · rename_i hc
      exact ⟨a, b, hin, hc⟩
    · rename_i hc
      rcases h with h | h
      · exact ⟨b, a, rfl, h.2, h.1⟩
      · exact absurd h hc
  · rename_i hne
    exact (hne a b hop hin).elim

theorem sw_wf (A B : Finset ℕ) (gs : List Gate) : ∀ U : List Bool,
    wf (gs.map (sw A B)) U = wf gs U := by
  induction gs with
  | nil => intro U; rfl
  | cons g gs ih =>
    intro U
    rw [List.map_cons, wf_cons, wf_cons, sw_eval, ih]

end PEqualNP.Outside.L_meta_3306

open PEqualNP.Outside.L_meta_3306 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3306 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  intro n C A B hC hand
  obtain ⟨hao, hrb, h2⟩ := hC
  have hga : ∀ k, PEqualNP.MetaComplexity.NestedCover.gateAt (⟨C.gates.map (sw A B), C.output⟩ : Circuit) k
      = sw A B (PEqualNP.MetaComplexity.NestedCover.gateAt C k) := by
    intro k
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    show (C.gates.map (sw A B)).getD k ⟨GateOp.or, []⟩ = sw A B (C.gates.getD k ⟨GateOp.or, []⟩)
    by_cases hk : k < C.gates.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk, List.getElem_map]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
      rfl
  refine ⟨⟨C.gates.map (sw A B), C.output⟩, ⟨?_, ?_, ?_⟩, by simp [Circuit.size], ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    rw [sw_op]
    exact hao g0 hg0
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    rw [hga j, sw_mem] at hi
    exact hrb j hj' i hi
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    rw [sw_len]
    exact h2 g0 hg0
  · funext x
    show (wf (C.gates.map (sw A B)) (List.ofFn x)).getD C.output false = (wf C.gates (List.ofFn x)).getD C.output false
    rw [sw_wf]
  · intro k
    rw [hga k, sw_op]
  · intro k hk
    rw [hga k, sw_or A B _ hk]
  · intro k hk hop
    have hk' : k < C.gates.length := by simpa using hk
    rw [hga k, sw_op] at hop
    obtain ⟨a, b, hin, hab⟩ := hand k hk' hop
    rw [hga k]
    exact sw_and A B _ a b hop hin hab
