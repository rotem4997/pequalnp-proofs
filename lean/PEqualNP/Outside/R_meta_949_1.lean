import Mathlib
import PEqualNP.Defs

-- L-meta-949: 存在一个 6 顶点图，其 AND-count 电路在 stated-function 条件上
-- 比任何 biclique cover 都省门。切成两块：
--   (1) 构造出满足 stated condition的良构电路（data-lane 穷举/搜索）；
--   (2) 结构下界：任何满足该 stated condition的电路都没有 ≤ size 的 biclique cover。
-- 结论逐字等于原 step；(1) 给出见证，(2) 把见证补成 ¬cover。
theorem PEqualNP.Outside.R_meta_949_1
    (hConstruct : ∃ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6), C.WellFormed ∧ (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true))
    (hLower : ∀ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6), C.WellFormed → (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → ¬ (∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧ (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)))) :
    ∃ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6), C.WellFormed ∧ (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧ ¬ (∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧ (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i))) := by
  classical
  obtain ⟨G, C, hwf, hpart⟩ := hConstruct
  refine ⟨G, C, hwf, hpart, ?_⟩
  exact hLower G C hwf hpart
