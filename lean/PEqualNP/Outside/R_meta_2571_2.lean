import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2571_2 :
  (∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ x y : Fin n → Bool,
    (∀ i, x i = true → y i = true) → ∀ k,
    (C.wires (List.ofFn x)).getD k false = true → (C.wires (List.ofFn y)).getD k false = true) →
  (let I := fun (p l : Fin 25) => decide (p.val < 12 ∧ 12 ≤ l.val ∧
      (p.val + l.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧ p.val ∉ ([0, 2, 8] : List ℕ))
    let active := fun (P : Finset (Fin 25)) =>
      ∀ p ∈ P, p.val < 12 ∧ p.val ∉ ([0, 2, 8] : List ℕ)
    let row := fun (P B : Finset (Fin 25)) (i : Fin 25) =>
      decide (i.val < 12 ∧ (i ∈ P ∨ i.val ∈ ([0, 2, 8] : List ℕ))) ||
        (decide (12 ≤ i.val ∧ i ∉ B) &&
          (List.finRange 25).all (fun p => !(decide (p ∈ P)) || !(I p i)))
    ∀ (B : Finset (Fin 25)) (x : Fin 25 → Bool),
      (∀ i ∈ B, x i = false) → (¬ ∃ p l, I p l = true ∧ x p = true ∧ x l = true) →
      ∃ P, active P ∧ ∀ i, x i = true → row P B i = true) →
  (let I := fun (p l : Fin 25) => decide (p.val < 12 ∧ 12 ≤ l.val ∧
      (p.val + l.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧ p.val ∉ ([0, 2, 8] : List ℕ))
    let active := fun (P : Finset (Fin 25)) =>
      ∀ p ∈ P, p.val < 12 ∧ p.val ∉ ([0, 2, 8] : List ℕ)
    let row := fun (P B : Finset (Fin 25)) (i : Fin 25) =>
      decide (i.val < 12 ∧ (i ∈ P ∨ i.val ∈ ([0, 2, 8] : List ℕ))) ||
        (decide (12 ≤ i.val ∧ i ∉ B) &&
          (List.finRange 25).all (fun p => !(decide (p ∈ P)) || !(I p i)))
    let W := ({13, 15, 21} : Finset (Fin 25))
    ∃ (C : Circuit) (a : ℕ), Monotone2 C ∧ C.size ≤ 45 ∧ C.output < 25 + C.size ∧ a < 25 + C.size ∧
      (∀ p l, I p l = true → C.eval (List.ofFn (fun i : Fin 25 => decide (i = p ∨ i = l))) = true) ∧
      (∀ P, active P → C.eval (List.ofFn (row P ∅)) = false) ∧
      (∀ l ∈ W, (C.wires (List.ofFn (fun i : Fin 25 => decide (i = l)))).getD a false = true) ∧
      (∀ P, active P → (C.wires (List.ofFn (row P W))).getD a false = false)) →
  ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (25 : ℕ) + x1.size ∧ x2 < (25 : ℕ) + x1.size ∧ ∀ (x3 : Fin (25 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)), ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x4 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  intro monotone extendRows witness
  let I := fun (p l : Fin 25) => decide (p.val < 12 ∧ 12 ≤ l.val ∧
      (p.val + l.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧ p.val ∉ ([0, 2, 8] : List ℕ))
  let active := fun (P : Finset (Fin 25)) =>
      ∀ p ∈ P, p.val < 12 ∧ p.val ∉ ([0, 2, 8] : List ℕ)
  let row := fun (P B : Finset (Fin 25)) (i : Fin 25) =>
      decide (i.val < 12 ∧ (i ∈ P ∨ i.val ∈ ([0, 2, 8] : List ℕ))) ||
        (decide (12 ≤ i.val ∧ i ∉ B) &&
          (List.finRange 25).all (fun p => !(decide (p ∈ P)) || !(I p i)))
  let W := ({13, 15, 21} : Finset (Fin 25))
  obtain ⟨C, a, mono, size, output, aux, positive, negative, on, off⟩ := witness
  let hit := fun x : Fin 25 → Bool => ∃ p l, I p l = true ∧ x p = true ∧ x l = true
  have correct (x : Fin 25 → Bool) : C.eval (List.ofFn x) = true ↔ hit x := by
    constructor
    · intro yes
      by_contra none
      obtain ⟨P, hP, cover⟩ := extendRows ∅ x (by simp) none
      have forced : C.eval (List.ofFn (row P ∅)) = true :=
        monotone 25 C mono x (row P ∅) cover C.output yes
      exact Bool.false_ne_true ((negative P hP).symm.trans forced)
    · rintro ⟨p, l, edge, hp, hl⟩
      refine monotone 25 C mono (fun i : Fin 25 => decide (i = p ∨ i = l)) x (fun i h => ?_) C.output (positive p l edge)
      rcases of_decide_eq_true h with rfl | rfl
      · exact hp
      · exact hl
  refine ⟨C, a, mono, size, output, aux, fun x => ⟨?_, ?_⟩⟩
  · simpa only [hit, I, decide_eq_true_eq, and_assoc] using correct x
  · intro no
    have noEdge : ¬hit x := fun h => Bool.false_ne_true (no.symm.trans ((correct x).mpr h))
    have marked : (∃ l ∈ W, x l = true) ↔ (x 13 || x 15 || x 21) = true := by
      simp [W, Bool.or_eq_true, or_assoc]
    by_cases h : ∃ l ∈ W, x l = true
    · obtain ⟨l, hl, yes⟩ := h
      rw [marked.mp ⟨l, hl, yes⟩]
      refine monotone 25 C mono (fun i : Fin 25 => decide (i = l)) x (fun i hi => ?_) a (on l hl)
      exact (of_decide_eq_true hi).symm ▸ yes
    · obtain ⟨P, hP, cover⟩ := extendRows W x
        (fun l hl => Bool.eq_false_of_not_eq_true (fun yes => h ⟨l, hl, yes⟩)) noEdge
      rw [Bool.eq_false_of_not_eq_true (fun yes => h (marked.mpr yes))]
      apply Bool.eq_false_of_not_eq_true
      intro yes
      have forced := monotone 25 C mono x (row P W) cover a yes
      exact Bool.false_ne_true ((off P hP).symm.trans forced)
