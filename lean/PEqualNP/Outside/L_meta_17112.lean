import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_17112

def gs : List Gate :=
  [⟨.or, [1,2]⟩, ⟨.or, [14,4]⟩, ⟨.and, [15,8]⟩,
   ⟨.or, [2,3]⟩, ⟨.or, [17,5]⟩, ⟨.and, [18,9]⟩,
   ⟨.or, [3,4]⟩, ⟨.or, [20,6]⟩, ⟨.and, [21,10]⟩,
   ⟨.or, [16,19]⟩, ⟨.or, [23,22]⟩]

def A : Circuit := ⟨gs, 24⟩

theorem shape : ∀ j (g : Gate), A.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ,
        g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j ∧ a ≠ 0 ∧ a ≠ 7 ∧ b ≠ 0 ∧ b ≠ 7 := by
  intro j g h
  have hj : j < 11 := by
    by_contra hc
    rw [List.getElem?_eq_none (by simp [A, gs]; omega)] at h
    cases h
  interval_cases j <;> simp [A, gs] at h <;> subst h <;> simp

theorem evalA (x : Fin 14 → Bool) : A.eval (List.ofFn x) =
    ((x 1 || x 2 || x 4) && x 8 || (x 2 || x 3 || x 5) && x 9 || (x 3 || x 4 || x 6) && x 10) := by
  simp [A, gs, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ]

theorem sem (x : Fin 14 → Bool) : A.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (1 ≤ l.val ∧ l.val ≤ 3) ∧ (p=l ∨ p=l+1 ∨ p=l+3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  rw [evalA]
  constructor
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ((⟨(h|h)|h, h'⟩ | ⟨(h|h)|h, h'⟩) | ⟨(h|h)|h, h'⟩)
    · exact ⟨1, 1, by decide, by decide, h, h'⟩
    · exact ⟨2, 1, by decide, by decide, h, h'⟩
    · exact ⟨4, 1, by decide, by decide, h, h'⟩
    · exact ⟨2, 2, by decide, by decide, h, h'⟩
    · exact ⟨3, 2, by decide, by decide, h, h'⟩
    · exact ⟨5, 2, by decide, by decide, h, h'⟩
    · exact ⟨3, 3, by decide, by decide, h, h'⟩
    · exact ⟨4, 3, by decide, by decide, h, h'⟩
    · exact ⟨6, 3, by decide, by decide, h, h'⟩
  · rintro ⟨p, l, hl, hpl, hp, hl'⟩
    fin_cases p <;> fin_cases l <;> simp_all (config := {decide := true})

end PEqualNP.Outside.L_meta_17112


theorem PEqualNP.Outside.L_meta_17112 :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size = (11 : ℕ) ∧ x1.output = (24 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2 ∧ x5 ≠ (0 : ℕ) ∧ x5 ≠ (7 : ℕ) ∧ x6 ≠ (0 : ℕ) ∧ x6 ≠ (7 : ℕ)) ∧ ∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), ((1 : ℕ) ≤ ↑x4 ∧ ↑x4 ≤ (3 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true := by
  exact ⟨PEqualNP.Outside.L_meta_17112.A, rfl, rfl,
    PEqualNP.Outside.L_meta_17112.shape,
    PEqualNP.Outside.L_meta_17112.sem⟩
