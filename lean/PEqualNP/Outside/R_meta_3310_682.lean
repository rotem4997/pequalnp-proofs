import Mathlib.Data.Fintype.EquivFin
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3310_682
    (matching : ∀ (m N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      (∃ p l : Fin m → Fin N, ∀ i j, I (p i) (l j) ↔ i = j) →
      Monotone2 C →
      (∀ p l : Fin N, I p l → circuitFun (N + N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ x : Fin (N + N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ 1 →
        (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) C x = false) →
      m ≤ 2 * (C.gates.filter (fun g => !(g.op.eval [true, false]))).length + 1)
    (remaining : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) → Monotone2 C →
      (∀ p l : Fin N, I p l → circuitFun (N + N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ x : Fin (N + N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) C x = false) →
      let ors := (C.gates.filter (fun g => g.op.eval [true, false])).length
      let ands := (C.gates.filter (fun g => !(g.op.eval [true, false]))).length
      2 * q ^ 2 + 1 ≤ ors → 100 * (ors + (q + 1) / 2) < N * q →
      N * q ≤ 100 * (ors + ands)) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (200 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →               (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →                 have x13 : ℕ := (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length;                 (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ x13 → (100 : ℕ) * x13 < x2 * x1 → x2 * x1 - (100 : ℕ) * x13 ≤ (100 : ℕ) * (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => !x16.op.eval [Bool.true, Bool.false]) x5.gates).length := by
  classical
  intro q N I _ C hq order degree joins mono positive sound
  dsimp only
  intro orLower _
  let base : Fin N := ⟨0, by omega⟩
  let points := (Fintype.equivFinOfCardEq (degree base)).symm
  let p (i : Fin (q + 1)) : Fin N := (points i).val
  have onBase (i : Fin (q + 1)) : I (p i) base := (points i).property
  have pinj : Function.Injective p := fun _ _ he => points.injective (Subtype.ext he)
  obtain ⟨outside, hoff⟩ : ∃ x : Fin N, ¬ I x base := by
    by_contra! allOn
    let e : {x : Fin N // I x base} ≃ Fin N :=
      ⟨Subtype.val, fun x => ⟨x, allOn x⟩, fun _ => rfl, fun _ => rfl⟩
    have card := Fintype.card_congr e
    rw [degree, Fintype.card_fin] at card
    have hpos : 0 < q ^ 2 := pow_pos (by omega) 2
    omega
  have distinct (i) : p i ≠ outside := fun h => hoff (h ▸ onBase i)
  let l (i : Fin (q + 1)) := Classical.choose (joins (p i) outside (distinct i)).exists
  have onLine (i) : I (p i) (l i) ∧ I outside (l i) :=
    Classical.choose_spec (joins (p i) outside (distinct i)).exists
  have induced : ∀ i j, I (p i) (l j) ↔ i = j := by
    intro i j
    constructor
    · intro hij
      by_contra hne
      have unique := joins (p i) (p j) (fun he => hne (pinj he))
      have eqBase : l j = base := unique.unique ⟨hij, (onLine j).1⟩ ⟨onBase i, onBase j⟩
      exact hoff (eqBase ▸ (onLine j).2)
    · rintro rfl
      exact (onLine i).1
  have low := matching (q + 1) N I C ⟨p, l, induced⟩ mono positive
    (fun x h1 => sound x (by omega))
  let ors := (C.gates.filter (fun g => g.op.eval [true, false])).length
  let ands := (C.gates.filter (fun g => !(g.op.eval [true, false]))).length
  change q + 1 ≤ 2 * ands + 1 at low
  change N * q - 100 * ors ≤ 100 * ands
  by_cases h : 100 * (ors + (q + 1) / 2) < N * q
  · have bound := remaining q N I C hq order degree joins mono positive sound orLower h
    change N * q ≤ 100 * (ors + ands) at bound
    omega
  · omega
