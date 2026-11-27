import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4199_1
    (coverBound :
      let R : Fin 42 × Fin 42 → Prop := fun p =>
        p.1.val < 21 ∧ 21 ≤ p.2.val ∧ (p.2.val + 21 - p.1.val) % 21 ∈ [0, 5, 7, 17, 20]
      let E : Finset (Fin 42 × Fin 42) := Finset.univ.filter R
      let andOp : Gate → Bool := fun g => GateOp.casesOn g.op true false false (fun _ => false) false
      ∀ C : Circuit, Monotone2 C →
        (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p ∈ E, x p.1 = true ∧ x p.2 = true) →
        ∃ S : Finset (Fin 42), (∀ p ∈ E, p.1 ∈ S ∨ p.2 ∈ S) ∧
          S.card ≤ C.gates.countP andOp)
    (matching :
      let R : Fin 42 × Fin 42 → Prop := fun p =>
        p.1.val < 21 ∧ 21 ≤ p.2.val ∧ (p.2.val + 21 - p.1.val) % 21 ∈ [0, 5, 7, 17, 20]
      let E : Finset (Fin 42 × Fin 42) := Finset.univ.filter R
      ∀ S : Finset (Fin 42), (∀ p ∈ E, p.1 ∈ S ∨ p.2 ∈ S) → 21 ≤ S.card) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (21 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x4.op Bool.true Bool.false Bool.false (fun (x5 : ℕ) => Bool.false) Bool.false) x1.gates := by
  classical
  intro C hMono hComp
  let R : Fin 42 × Fin 42 → Prop := fun p =>
    p.1.val < 21 ∧ 21 ≤ p.2.val ∧ (p.2.val + 21 - p.1.val) % 21 ∈ [0, 5, 7, 17, 20]
  let E : Finset (Fin 42 × Fin 42) := Finset.univ.filter R
  let andOp : Gate → Bool := fun g => GateOp.casesOn g.op true false false (fun _ => false) false
  have mem (p : Fin 42 × Fin 42) : p ∈ E ↔ R p := by simp [E]
  have hComp' : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p ∈ E, x p.1 = true ∧ x p.2 = true := by
    intro x
    rw [hComp x]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨(a, b), (mem (a, b)).2 hab, ha, hb⟩
    · rintro ⟨⟨a, b⟩, hab, ha, hb⟩
      exact ⟨a, b, (mem (a, b)).1 hab, ha, hb⟩
  obtain ⟨S, hCover, hBound⟩ := coverBound C hMono hComp'
  change S.card ≤ C.gates.countP andOp at hBound
  have h21 := matching S hCover
  change 21 ≤ C.gates.countP andOp
  omega
