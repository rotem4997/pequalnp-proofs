import PEqualNP.Outside.L_meta_2672
import PEqualNP.MetaComplexity.L3557

theorem PEqualNP.Outside.L_meta_2240 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1) → PEqualNP.ReadK.AndOrFanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true)) → PEqualNP.ReadK.IsSingleRead C (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val)))) → N * q ≤ 32 * C.size + 3 * N :=
  PEqualNP.MetaComplexity.L3557 PEqualNP.Outside.L_meta_2672
