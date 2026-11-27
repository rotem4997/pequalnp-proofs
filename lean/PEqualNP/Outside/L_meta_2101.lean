import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2101

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gs : List Gate := [⟨GateOp.or, [15, 22]⟩, ⟨GateOp.or, [17, 26]⟩, ⟨GateOp.or, [18, 27]⟩, ⟨GateOp.and, [5, 28]⟩, ⟨GateOp.or, [16, 23]⟩, ⟨GateOp.or, [18, 30]⟩, ⟨GateOp.or, [19, 31]⟩, ⟨GateOp.and, [6, 32]⟩, ⟨GateOp.or, [17, 24]⟩, ⟨GateOp.or, [19, 34]⟩, ⟨GateOp.or, [20, 35]⟩, ⟨GateOp.and, [7, 36]⟩, ⟨GateOp.or, [18, 25]⟩, ⟨GateOp.or, [20, 38]⟩, ⟨GateOp.or, [21, 39]⟩, ⟨GateOp.and, [8, 40]⟩, ⟨GateOp.or, [19, 13]⟩, ⟨GateOp.or, [21, 42]⟩, ⟨GateOp.or, [22, 43]⟩, ⟨GateOp.and, [9, 44]⟩, ⟨GateOp.or, [20, 14]⟩, ⟨GateOp.or, [22, 46]⟩, ⟨GateOp.or, [23, 47]⟩, ⟨GateOp.and, [10, 48]⟩, ⟨GateOp.or, [21, 15]⟩, ⟨GateOp.or, [23, 50]⟩, ⟨GateOp.or, [24, 51]⟩, ⟨GateOp.and, [11, 52]⟩, ⟨GateOp.or, [22, 16]⟩, ⟨GateOp.or, [24, 54]⟩, ⟨GateOp.or, [25, 55]⟩, ⟨GateOp.and, [12, 56]⟩, ⟨GateOp.or, [53, 57]⟩, ⟨GateOp.or, [49, 58]⟩, ⟨GateOp.or, [45, 59]⟩, ⟨GateOp.or, [41, 60]⟩, ⟨GateOp.or, [37, 61]⟩, ⟨GateOp.or, [33, 62]⟩, ⟨GateOp.or, [29, 63]⟩]

def cc : Circuit := ⟨gs, 64⟩

def lp : List (Fin 26 × List (Fin 26)) := [(5, [18, 17, 15, 22]), (6, [19, 18, 16, 23]), (7, [20, 19, 17, 24]), (8, [21, 20, 18, 25]), (9, [22, 21, 19, 13]), (10, [23, 22, 20, 14]), (11, [24, 23, 21, 15]), (12, [25, 24, 22, 16])]

def ff (x : Fin 26 → Bool) : Bool := lp.any (fun q => x q.1 && q.2.any x)

theorem ofn (x : Fin 26 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ev (x : Fin 26 → Bool) : circuitFun 26 cc x = ff x := by
  show (cc.wires (List.ofFn x)).getD 64 false = ff x
  rw [ofn]
  simp [Circuit.wires, cc, gs, GateOp.eval, ff, lp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem key1 : ∀ p l : Fin 13, 5 ≤ (p : ℕ) → (∃ d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))), p = l + d) → ∃ q ∈ lp, q.1 = Fin.castAdd 13 p ∧ Fin.natAdd 13 l ∈ q.2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem key2 : ∀ q ∈ lp, ∀ m ∈ q.2, ∃ p l : Fin 13, q.1 = Fin.castAdd 13 p ∧ m = Fin.natAdd 13 l ∧ 5 ≤ (p : ℕ) ∧ ∃ d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))), p = l + d := by
  decide +kernel

theorem spec (x : Fin 26 → Bool) : ff x = Decidable.decide (∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (5 : ℕ) ≤ ↑x5 ∧ (∃ d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))), x5 = x6 + d) ∧ x (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) x6) = Bool.true) := by
  rw [Bool.eq_iff_iff]
  simp only [ff, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, h1, m, hm, h2⟩
    obtain ⟨p, l, e1, e2, h5, hI⟩ := key2 q hq m hm
    exact ⟨p, l, h5, hI, e1 ▸ h1, e2 ▸ h2⟩
  · rintro ⟨p, l, h5, hI, hp, hl⟩
    obtain ⟨q, hq, e1, e2⟩ := key1 p l h5 hI
    exact ⟨q, hq, e1 ▸ hp, _, e2, hl⟩

theorem mono : Monotone2 cc := by
  intro g hg
  simp only [cc, gs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
theorem rb : NestedCover.ReadsBack 26 cc := by
  unfold NestedCover.ReadsBack
  decide +kernel

theorem sz : cc.size ≤ 39 := by
  decide

theorem core : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 ∧ x1.size ≤ (39 : ℕ) ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x4 = Decidable.decide (∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (5 : ℕ) ≤ ↑x5 ∧ (∃ d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))), x5 = x6 + d) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) :=
  ⟨cc, mono, rb, sz, fun x => (ev x).trans (spec x)⟩

end PEqualNP.Outside.L_meta_2101

theorem PEqualNP.Outside.L_meta_2101 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 ∧       x1.size ≤ (39 : ℕ) ∧         have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => ∃ x5 ∈ x2, x3 = x4 + x5;         ∀ (x4 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x4 = Decidable.decide (∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (5 : ℕ) ≤ ↑x5 ∧ x3 x5 x6 ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) := by
  exact PEqualNP.Outside.L_meta_2101.core
