import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3505

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def sw (X Y : Finset ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | GateOp.and, [a, b] => if a ∈ X ∧ b ∈ Y then g else ⟨GateOp.and, [b, a]⟩
  | _, _ => g

theorem sw_op (X Y : Finset ℕ) (g : Gate) : (sw X Y g).op = g.op := by
  unfold sw
  split
  · rename_i hop _
    split_ifs
    · rfl
    · exact hop.symm
  · rfl

theorem sw_len (X Y : Finset ℕ) (g : Gate) : (sw X Y g).inputs.length = g.inputs.length := by
  unfold sw
  split
  · rename_i _ hin
    split_ifs
    · rfl
    · rw [hin]; rfl
  · rfl

theorem sw_mem (X Y : Finset ℕ) (g : Gate) (i : ℕ) : i ∈ (sw X Y g).inputs ↔ i ∈ g.inputs := by
  unfold sw
  split
  · rename_i _ hin
    split_ifs
    · rfl
    · rw [hin]; simp [or_comm]
  · rfl

theorem sw_eval (X Y : Finset ℕ) (g : Gate) (v : ℕ → Bool) :
    (sw X Y g).op.eval ((sw X Y g).inputs.map v) = g.op.eval (g.inputs.map v) := by
  unfold sw
  split
  · rename_i hop hin
    split_ifs
    · rfl
    · rw [hop, hin]; simp [GateOp.eval, Bool.and_comm]
  · rfl

theorem sw_or (X Y : Finset ℕ) (g : Gate) (h : g.op = GateOp.or) : sw X Y g = g := by
  unfold sw
  split
  · rename_i hop _
    rw [h] at hop
    cases hop
  · rfl

theorem sw_and (X Y : Finset ℕ) (g : Gate) (a b : ℕ) (hop : g.op = GateOp.and)
    (hin : g.inputs = [a, b]) (hc : a ∈ X ∧ b ∈ Y ∨ a ∈ Y ∧ b ∈ X) :
    ∃ a' b', (sw X Y g).inputs = [a', b'] ∧ a' ∈ X ∧ b' ∈ Y := by
  unfold sw
  split
  · rename_i a0 b0 _ hin0
    rw [hin] at hin0
    simp only [List.cons.injEq, and_true] at hin0
    obtain ⟨rfl, rfl⟩ := hin0
    split_ifs with hXY
    · exact ⟨a, b, hin, hXY.1, hXY.2⟩
    · rcases hc with hc | hc
      · exact absurd hc hXY
      · exact ⟨b, a, rfl, hc.2, hc.1⟩
  · rename_i hne
    exact absurd hin (hne a b hop)

theorem gateAt_map (C : Circuit) (X Y : Finset ℕ) (j : ℕ) :
    gateAt ⟨C.gates.map (sw X Y), C.output⟩ j = sw X Y (gateAt C j) := by
  unfold gateAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : C.gates[j]? with
  | none => simp [sw]
  | some g => simp

theorem wires_map (C : Circuit) (X Y : Finset ℕ) (x : List Bool) :
    (⟨C.gates.map (sw X Y), C.output⟩ : Circuit).wires x = C.wires x := by
  unfold Circuit.wires
  rw [List.foldl_map]
  congr 1
  funext w g
  rw [sw_eval]

end PEqualNP.Outside.L_meta_3505

open PEqualNP.Outside.L_meta_3505
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.L_meta_3505 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x3 ∧ x12 ∈ x4 := by
  intro n C X Y hC hand
  refine ⟨⟨C.gates.map (sw X Y), C.output⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    rw [sw_op]
    exact hC.1 g0 hg0
  · intro j hj i hi
    rw [gateAt_map, sw_mem] at hi
    exact hC.2.1 j (by simpa using hj) i hi
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    rw [sw_len]
    exact hC.2.2 g0 hg0
  · simp [Circuit.size]
  · funext x
    simp only [circuitFun, Circuit.eval, wires_map]
  · intro k
    rw [gateAt_map, sw_op]
  · intro k hk
    rw [gateAt_map]
    exact sw_or X Y _ hk
  · intro k hk hop
    rw [gateAt_map] at hop ⊢
    rw [sw_op] at hop
    obtain ⟨a, b, hin, hc⟩ := hand k (by simpa using hk) hop
    exact sw_and X Y _ a b hop hin hc
