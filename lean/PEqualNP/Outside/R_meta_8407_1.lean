import Mathlib
import PEqualNP.Defs

-- L-meta-8407: 存在一个 Monotone2、read-back、size<=33 的电路计算给定边函数。
-- 切成两块：
--   (1) 存在满足结构约束（Monotone2、ReadsBack、输出与 size 范围内）的电路；
--   (2) 任何满足该结构约束的电路都满足功能正确性条件。
theorem PEqualNP.Outside.R_meta_8407_1
    (hWitness : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (21 : ℕ) x1 ∧ x1.output < (21 : ℕ) + x1.size ∧ x1.size ≤ (33 : ℕ))
    (hFunctional : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (PEqualNP.MetaComplexity.Monotone2 x1 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (21 : ℕ) x1 ∧ x1.output < (21 : ℕ) + x1.size ∧ x1.size ≤ (33 : ℕ)) → (∀ (x2 : Fin (21 : ℕ) → Bool), x1.eval (List.ofFn x2) = (List.flatMap (fun (x3 : ℕ) => List.map (fun (x4 : ℕ) => (Fin.ofNat (21 : ℕ) x3, Fin.ofNat (21 : ℕ) x4)) [(14 : ℕ) + x3, (7 : ℕ) + x3, (7 : ℕ) + (x3 + (1 : ℕ)) % (7 : ℕ), (7 : ℕ) + (x3 + (5 : ℕ)) % (7 : ℕ)]) (List.range (7 : ℕ))).any fun (x3 : Fin (21 : ℕ) × Fin (21 : ℕ)) => x2 x3.1 && x2 x3.2)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (21 : ℕ) x1 ∧ x1.output < (21 : ℕ) + x1.size ∧ x1.size ≤ (33 : ℕ) ∧ ∀ (x2 : Fin (21 : ℕ) → Bool), x1.eval (List.ofFn x2) = (List.flatMap (fun (x3 : ℕ) => List.map (fun (x4 : ℕ) => (Fin.ofNat (21 : ℕ) x3, Fin.ofNat (21 : ℕ) x4)) [(14 : ℕ) + x3, (7 : ℕ) + x3, (7 : ℕ) + (x3 + (1 : ℕ)) % (7 : ℕ), (7 : ℕ) + (x3 + (5 : ℕ)) % (7 : ℕ)]) (List.range (7 : ℕ))).any fun (x3 : Fin (21 : ℕ) × Fin (21 : ℕ)) => x2 x3.1 && x2 x3.2 := by
  classical
  obtain ⟨C, hstruct⟩ := hWitness
  refine ⟨C, hstruct.1, hstruct.2.1, hstruct.2.2.1, hstruct.2.2.2, ?_⟩
  exact hFunctional C hstruct
