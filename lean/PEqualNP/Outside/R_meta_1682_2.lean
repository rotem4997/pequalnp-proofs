import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Split the finite incidence geometry from the circuit lower bound.
-- The circuit part seeks an accepting set of inputs with no incident pair,
-- no three collinear points and no three concurrent lines.
theorem PEqualNP.Outside.R_meta_1682_2
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
        (∀ p w : Fin 13, inc p w →
          circuitFun 26 C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) →
        ∃ P W : Finset (Fin 13),
          (∀ p ∈ P, ∀ w ∈ W, ¬ inc p w) ∧
          (∀ w : Fin 13, (P.filter (fun p => inc p w)).card ≤ 2) ∧
          (∀ p : Fin 13, (W.filter (fun w => inc p w)).card ≤ 2) ∧
          ∀ x : Fin 26 → Bool,
            (∀ p ∈ P, x (Fin.castAdd 13 p) = true) →
            (∀ w ∈ W, x (Fin.natAdd 13 w) = true) → circuitFun 26 C x = true) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  rintro ⟨C, mono, size, yes, no⟩
  have incidence (p w : Fin 13) : (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d) ↔ (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) := by simp
  simp_rw [incidence] at yes no
  obtain ⟨P, W, disjoint, pointArc, lineArc, accepts⟩ := smallCircuit C mono size yes
  obtain ⟨Q, incl, avoids, closed, noncollinear, nonconcurrent⟩ :=
    completion P W disjoint pointArc lineArc
  have zero := no Q closed ⟨noncollinear, nonconcurrent⟩
  let x := fun kk : Fin 26 => decide ((∃ pp ∈ Q, kk = Fin.castAdd 13 pp) ∨
    (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
      ∀ pp ∈ Q, ¬ (pp = ww ∨ pp = ww + 1 ∨ pp = ww + 3 ∨ pp = ww + 9)))
  have one := accepts x (fun p hp => decide_eq_true (Or.inl ⟨p, incl hp, rfl⟩))
    (fun w hw => decide_eq_true (Or.inr ⟨w, rfl, avoids w hw⟩))
  exact Bool.noConfusion (zero.symm.trans one)
