import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One family starts with a four-point arc and takes every line avoiding it.
-- The other starts with four lines and takes every point avoiding them.
theorem PEqualNP.Outside.R_meta_2397_2 :
  (let I := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
    let EL := fun (P : Finset (Fin 13)) => Finset.univ.filter (fun l => ∀ p ∈ P, ¬ I p l)
    let EP := fun (L : Finset (Fin 13)) => Finset.univ.filter (fun p => ∀ l ∈ L, ¬ I p l)
    let CP := fun (P : Finset (Fin 13)) => ∀ l, (P.filter (fun p => I p l)).card ≤ 2
    let CL := fun (L : Finset (Fin 13)) => ∀ p, (L.filter (I p)).card ≤ 2
    (∀ P : Finset (Fin 13), P.card = 4 → CL (EL P)) ∧
    (∀ L : Finset (Fin 13), L.card = 4 → CP (EP L))) →
  (∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ x y : Fin n → Bool,
    (∀ i, x i = true → y i = true) → circuitFun n C x = true → circuitFun n C y = true) →
  (let I := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
    let EL := fun (P : Finset (Fin 13)) => Finset.univ.filter (fun l => ∀ p ∈ P, ¬ I p l)
    let EP := fun (L : Finset (Fin 13)) => Finset.univ.filter (fun p => ∀ l ∈ L, ¬ I p l)
    let CP := fun (P : Finset (Fin 13)) => ∀ l, (P.filter (fun p => I p l)).card ≤ 2
    let CL := fun (L : Finset (Fin 13)) => ∀ p, (L.filter (I p)).card ≤ 2
    let row := fun (P L : Finset (Fin 13)) (i : Fin 26) =>
      Fin.addCases (motive := fun _ => Bool)
        (fun p : Fin 13 => decide (p ∈ P)) (fun l : Fin 13 => decide (l ∈ L)) i
    ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
    (∀ p l : Fin 13, I p l → circuitFun 26 C
      (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
    (∃ P : Finset (Fin 13), P.card = 4 ∧ CP P ∧ circuitFun 26 C (row P (EL P)) = true) ∨
    (∃ L : Finset (Fin 13), L.card = 4 ∧ CL L ∧ circuitFun 26 C (row (EP L) L) = true)) →
  let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) → ∃ (x6 : Finset (Fin (13 : ℕ))) (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x7 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧ ∀ (x8 : Fin (26 : ℕ) → Bool), (∀ x9 ∈ x6, x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true) → (∀ x10 ∈ x7, x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x8 = Bool.true := by
  intro geometry propagate witness
  dsimp only
  intro C mono size accepts
  let I := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let EL := fun (P : Finset (Fin 13)) => Finset.univ.filter (fun l => ∀ p ∈ P, ¬ I p l)
  let EP := fun (L : Finset (Fin 13)) => Finset.univ.filter (fun p => ∀ l ∈ L, ¬ I p l)
  let CP := fun (P : Finset (Fin 13)) => ∀ l, (P.filter (fun p => I p l)).card ≤ 2
  let CL := fun (L : Finset (Fin 13)) => ∀ p, (L.filter (I p)).card ≤ 2
  let row := fun (P L : Finset (Fin 13)) (i : Fin 26) =>
      Fin.addCases (motive := fun _ => Bool)
        (fun p : Fin 13 => decide (p ∈ P)) (fun l : Fin 13 => decide (l ∈ L)) i
  obtain ⟨P, L, hp, hl, apart, yes⟩ :
      ∃ P L : Finset (Fin 13), CP P ∧ CL L ∧
        (∀ p ∈ P, ∀ l ∈ L, ¬ I p l) ∧ circuitFun 26 C (row P L) = true := by
    rcases witness C mono size accepts with ⟨P, hP, hcap, htrue⟩ | ⟨L, hL, hcap, htrue⟩
    · refine ⟨P, EL P, hcap, geometry.1 P hP, ?_, htrue⟩
      exact fun p hp l hl => (Finset.mem_filter.mp hl).2 p hp
    · refine ⟨EP L, L, geometry.2 L hL, hcap, ?_, htrue⟩
      exact fun p hp l hl => (Finset.mem_filter.mp hp).2 l hl
  refine ⟨P, L, apart, hp, hl, ?_⟩
  intro x allP allL
  refine propagate 26 C mono (row P L) x (fun i => ?_) yes
  refine Fin.addCases (m := 13) (n := 13)
    (motive := fun i => row P L i = true → x i = true) ?_ ?_ i
  · intro p h
    exact allP p (of_decide_eq_true (by simpa only [row, Fin.addCases_left] using h))
  · intro l h
    exact allL l (of_decide_eq_true (by simpa only [row, Fin.addCases_right] using h))
