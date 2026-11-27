import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2147_631
    (completion : let inc (p w : Fin 13) : Prop := p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9
      ∀ P W : Finset (Fin 13),
        (∀ p ∈ P, ∀ w ∈ W, ¬ inc p w) →
        (∀ w : Fin 13, (P.filter (fun p => inc p w)).card ≤ 2) →
        (∀ p : Fin 13, (W.filter (fun w => inc p w)).card ≤ 2) →
        ∃ Q : Finset (Fin 13), P ⊆ Q ∧
          (∀ w ∈ W, ∀ p ∈ Q, ¬ inc p w) ∧
          (∀ v : Fin 13, v ∉ Q → ∃ w : Fin 13, (∀ p ∈ Q, ¬ inc p w) ∧ inc v w) ∧
          ¬ (∃ w : Fin 13, ∀ p ∈ Q, inc p w) ∧
          ¬ (∃ v : Fin 13, ∀ w : Fin 13, (∀ p ∈ Q, ¬ inc p w) → inc v w))
    (smallCircuit : let inc (p w : Fin 13) : Prop := p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9
      ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
        ¬ HasLineDegree 26 (Finset.Ico 13 26) C 1 →
        ¬ HasLineDegree 26 (Finset.range 13) C 1 →
        (∀ p w : Fin 13, inc p w →
          circuitFun 26 C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) →
        ∃ P W : Finset (Fin 13),
          (∀ p ∈ P, ∀ w ∈ W, ¬ inc p w) ∧
          (∀ w : Fin 13, (P.filter (fun p => inc p w)).card ≤ 2) ∧
          (∀ p : Fin 13, (W.filter (fun w => inc p w)).card ≤ 2) ∧
          ∀ x : Fin 26 → Bool,
            (∀ p ∈ P, x (Fin.castAdd 13 p) = true) →
            (∀ w ∈ W, x (Fin.natAdd 13 w) = true) → circuitFun 26 C x = true) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.Ico (13 : ℕ) ((13 : ℕ) + (13 : ℕ))) x2 (1 : ℕ) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.range (13 : ℕ)) x2 (1 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((¬∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∧ ¬∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false := by
  intro difference
  rintro ⟨C, mono, size, lines, points, yes, no⟩
  have incidence (p w : Fin 13) : (∃ d ∈ difference, p = w + d) ↔ (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) := by
    change (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d) ↔ _
    simp
  simp_rw [incidence] at yes no
  obtain ⟨P, W, disjoint, pointArc, lineArc, accepts⟩ := smallCircuit C mono size lines points yes
  obtain ⟨Q, incl, avoids, closed, noncollinear, nonconcurrent⟩ :=
    completion P W disjoint pointArc lineArc
  have zero := no Q closed ⟨noncollinear, nonconcurrent⟩
  let x := fun kk : Fin 26 => decide ((∃ pp ∈ Q, kk = Fin.castAdd 13 pp) ∨
    (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
      ∀ pp ∈ Q, ¬ (pp = ww ∨ pp = ww + 1 ∨ pp = ww + 3 ∨ pp = ww + 9)))
  have one := accepts x (fun p hp => decide_eq_true (Or.inl ⟨p, incl hp, rfl⟩))
    (fun w hw => decide_eq_true (Or.inr ⟨w, rfl, avoids w hw⟩))
  exact Bool.noConfusion (zero.symm.trans one)
