import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each mask records its selected points in bits zero through twenty.
-- Removing one line from each representative gives 17 times 21 transitions.
-- The circuit must reject every collineation image of each representative.
theorem PEqualNP.Outside.R_meta_4197_1
    (step : let seeds : List ℕ := [0, 1, 3, 7, 15, 19, 23, 31, 95, 389, 1369, 1371, 5501, 6799, 54781, 503803, 2097151]
     let offsets : List (Fin 21) := [0, 1, 4, 14, 16]
     let inc := fun (i l : Fin 21) => i - l ∈ offsets
     let preserves := fun (g : Fin 21 ≃ Fin 21) =>
       ∀ l : Fin 21, ∃ k : Fin 21, ∀ i : Fin 21, inc i l ↔ inc (g i) k
     ∀ m ∈ seeds, ∀ l : Fin 21, ∃ n ∈ seeds, ∃ g : Fin 21 ≃ Fin 21,
       preserves g ∧ ∀ i : Fin 21, (m.testBit i.val && !decide (inc i l)) = n.testBit (g i).val)
    (tested : let seeds : List ℕ := [0, 1, 3, 7, 15, 19, 23, 31, 95, 389, 1369, 1371, 5501, 6799, 54781, 503803, 2097151]
     let offsets : List (Fin 21) := [0, 1, 4, 14, 16]
     let inc := fun (i l : Fin 21) => i - l ∈ offsets
     let preserves := fun (g : Fin 21 ≃ Fin 21) =>
       ∀ l : Fin 21, ∃ k : Fin 21, ∀ i : Fin 21, inc i l ↔ inc (g i) k
     ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 124 ∧
       (∀ i l : Fin 21, inc i l →
         C.eval (List.ofFn (Fin.append (fun j => decide (j = i)) (fun j => decide (j = l)))) = true) ∧
       ∀ m ∈ seeds, ∀ g : Fin 21 ≃ Fin 21, preserves g →
         let P := fun i : Fin 21 => m.testBit (g i).val
         C.eval (List.ofFn (Fin.append P (fun l => !offsets.any (fun d => P (l + d))))) = false) :
    have x1 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x1 x2 : Fin (21 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (21 : ℕ)) ∨ x1 = x2 + (4 : Fin (21 : ℕ)) ∨ x1 = x2 + (14 : Fin (21 : ℕ)) ∨ x1 = x2 + (16 : Fin (21 : ℕ)); have x2 : (Fin (21 : ℕ) → Bool) → Fin (21 : ℕ) → Bool := fun (x2 : Fin (21 : ℕ) → Bool) (x3 : Fin (21 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (21 : ℕ))) || x2 (x3 + (4 : Fin (21 : ℕ))) || x2 (x3 + (14 : Fin (21 : ℕ))) || x2 (x3 + (16 : Fin (21 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ (124 : ℕ) ∧ (∀ (x4 x5 : Fin (21 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((21 : ℕ) + (21 : ℕ))) => Fin.addCases (fun (x8 : Fin (21 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (21 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧ ∀ (x4 : Fin (21 : ℕ) → Bool), (∀ (x5 : Fin (21 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (21 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((21 : ℕ) + (21 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false := by
  let seeds : List ℕ := [0, 1, 3, 7, 15, 19, 23, 31, 95, 389, 1369, 1371, 5501, 6799, 54781, 503803, 2097151]
  let offsets : List (Fin 21) := [0, 1, 4, 14, 16]
  let inc := fun (i l : Fin 21) => i - l ∈ offsets
  let preserves := fun (g : Fin 21 ≃ Fin 21) =>
    ∀ l : Fin 21, ∃ k : Fin 21, ∀ i : Fin 21, inc i l ↔ inc (g i) k
  let orbit := fun (P : Fin 21 → Bool) =>
    ∃ m ∈ seeds, ∃ g : Fin 21 ≃ Fin 21, preserves g ∧ ∀ i, P i = m.testBit (g i).val
  obtain ⟨C, mono, size, pos, neg⟩ := tested
  have edge : ∀ i l : Fin 21, inc i l ↔
      i = l ∨ i = l + 1 ∨ i = l + 4 ∨ i = l + 14 ∨ i = l + 16 := by decide
  refine ⟨C, mono, size, fun i l h => pos i l ((edge i l).2 h), ?_⟩
  intro P complete
  have full : orbit (fun _ => true) :=
    ⟨2097151, by decide, Equiv.refl _, fun l => ⟨l, fun _ => Iff.rfl⟩, by decide⟩
  have erase (Q : Fin 21 → Bool) (hQ : orbit Q) (l : Fin 21) :
      orbit (fun i => Q i && !decide (inc i l)) := by
    obtain ⟨m, hm, g, hg, h⟩ := hQ
    obtain ⟨k, hk⟩ := hg l
    obtain ⟨n, hn, f, hf, h'⟩ := step m hm k
    refine ⟨n, hn, g.trans f, ?_, ?_⟩
    · intro j
      obtain ⟨a, ha⟩ := hg j
      obtain ⟨b, hb⟩ := hf a
      exact ⟨b, fun i => (ha i).trans (hb (g i))⟩
    · intro i
      simpa only [h i, hk i, Equiv.trans_apply] using h' (g i)
  have removes (ls : List (Fin 21)) : orbit (fun i => !(ls.any fun l => decide (inc i l))) := by
    induction ls with
    | nil => exact full
    | cons l ls ih => simpa [List.any_cons, Bool.and_comm] using erase _ ih l
  let free := fun l : Fin 21 => !offsets.any (fun d => P (l + d))
  have free_eq (l : Fin 21) : free l = !(P l || P (l + 1) || P (l + 4) ||
      P (l + 14) || P (l + 16)) := by simp [free, offsets, Bool.or_assoc]
  let emptyLines := (List.finRange 21).filter free
  have repr : (fun i => !(emptyLines.any fun l => decide (inc i l))) = P := by
    funext i
    cases hi : P i with
    | false =>
      obtain ⟨l, hil, hl⟩ := complete i hi
      simp only [Bool.not_eq_false', List.any_eq_true, decide_eq_true_eq]
      exact ⟨l, List.mem_filter.mpr ⟨List.mem_finRange l, (free_eq l).trans hl⟩, (edge i l).2 hil⟩
    | true =>
      simp only [Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq]
      intro l hl hil
      have off := (free_eq l).symm.trans (List.mem_filter.mp hl).2
      rcases (edge i l).1 hil with rfl | rfl | rfl | rfl | rfl <;> simp [hi] at off
  obtain ⟨m, hm, g, hg, hP⟩ := repr ▸ removes emptyLines
  have testedP : C.eval (List.ofFn (Fin.append P free)) = false := by
    simpa only [free, offsets, ← hP] using neg m hm g hg
  rw [funext free_eq] at testedP
  exact testedP
