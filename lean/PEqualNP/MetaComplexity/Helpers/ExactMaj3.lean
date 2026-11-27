import PEqualNP.MetaComplexity.Helpers.TableSearch

/-!
# Majority of three inputs has circuit size exactly four

Helper for `L100`. Upper bound: the circuit AND(x0, x1), OR(x0, x1), AND(that, x2), OR of the
two. Lower bound: the truth-table search of `Helpers.TableSearch`, run to depth three from the
tables of the three inputs (`170`, `204`, `240`), never meets the table of majority (`232`).
-/

namespace PEqualNP.MetaComplexity.Helpers.ExactMaj3

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers.TableSearch

/-- Majority of three inputs. -/
def maj3 : (Fin 3 → Bool) → Bool :=
  fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

/-- The four-gate circuit. -/
def maj3Circuit : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [4, 2]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩

theorem maj3_upper : HasCircuitSize 3 maj3 4 := by
  refine ⟨maj3Circuit, ?_, by decide, ?_⟩
  · intro g hg
    simp only [maj3Circuit, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · decide

/-- The search fails at depth three. -/
theorem maj3_search : reach (2 ^ 8 - 1) (fun t => t % 2 ^ 8 == 232) 3 [170, 204, 240] = false := by
  decide +kernel

theorem maj3_lower : ¬ HasCircuitSize 3 maj3 3 := by
  apply lower_of_search 3 8 maj3 [170, 204, 240] 232 3 (by norm_num) _ maj3_search
  have key : ∀ p, p < 8 → (List.ofFn fun i : Fin 3 => p.testBit i)
      = [170, 204, 240].map (fun t : ℕ => t.testBit p) ∧
      maj3 (fun i => p.testBit i) = Nat.testBit 232 p := by decide
  exact fun p hp => ⟨_, key p hp⟩

theorem hasCircuitSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (hst : s ≤ t)
    (h : HasCircuitSize n f s) : HasCircuitSize n f t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, le_trans h2 hst, h3⟩

theorem maj3_size (s : ℕ) : HasCircuitSize 3 maj3 s ↔ 4 ≤ s := by
  constructor
  · intro h
    by_contra hs
    exact maj3_lower (hasCircuitSize_mono (by omega) h)
  · intro h
    exact hasCircuitSize_mono h maj3_upper

end PEqualNP.MetaComplexity.Helpers.ExactMaj3
