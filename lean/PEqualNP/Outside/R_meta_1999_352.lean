import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1999_352
    (transfer : ∀ (P L : ℕ) (E : Finset (Fin P × Fin L)) (C : Circuit),
    let models := fun (D : Circuit) (S : Finset (Fin P × Fin L)) =>
      ∀ (x : Fin P → Bool) (y : Fin L → Bool),
        D.eval (List.ofFn x ++ List.ofFn y) =
          decide (∃ i j, (i,j) ∈ S ∧ x i = true ∧ y j = true)
    Monotone2 C → models C E →
    (E.image Prod.fst).card + (E.image Prod.snd).card ≤ 2 * (C.size+1) ∧
    ∀ (A : Finset (Fin P)) (B : Finset (Fin L)), ∃ D : Circuit,
      Monotone2 D ∧ D.size ≤ C.size ∧ models D (E.filter fun z => z.1 ∈ A ∧ z.2 ∈ B))
    (core : ∀ (P L d : ℕ) (E : Finset (Fin P × Fin L)),
    ∃ (A : Finset (Fin P)) (B : Finset (Fin L)),
      let F := E.filter fun z => z.1 ∈ A ∧ z.2 ∈ B
      E.card + d*(A.card+B.card) ≤ F.card + d*((E.image Prod.fst).card+(E.image Prod.snd).card) ∧
      ∀ X ⊆ A, ∀ Y ⊆ B, (F.filter fun z => z.1 ∈ X ∧ z.2 ∈ Y).card +
        d*((A \ X).card + (B \ Y).card) ≤ F.card)
    (dense : ∃ d k : ℕ, ∀ (P L : ℕ) (A : Finset (Fin P)) (B : Finset (Fin L))
    (F : Finset (Fin P × Fin L)),
    (∀ z ∈ F, z.1 ∈ A ∧ z.2 ∈ B) →
    (∀ a b x y, (a,x) ∈ F → (b,x) ∈ F → (a,y) ∈ F → (b,y) ∈ F → a=b ∨ x=y) →
    (∀ X ⊆ A, ∀ Y ⊆ B, (F.filter fun z => z.1 ∈ X ∧ z.2 ∈ Y).card +
      d*((A \ X).card+(B \ Y).card) ≤ F.card) →
    let models := fun (D : Circuit) (S : Finset (Fin P × Fin L)) =>
      ∀ (x : Fin P → Bool) (y : Fin L → Bool),
        D.eval (List.ofFn x ++ List.ofFn y) =
          decide (∃ i j, (i,j) ∈ S ∧ x i = true ∧ y j = true)
    ∀ D : Circuit, Monotone2 D → models D F → F.card ≤ k*(D.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x9.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) → ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card ≤ x1 * (x9.size + (1 : ℕ)) := by
  classical
  obtain ⟨d,k,price⟩ := dense
  refine ⟨k+2*d,?_⟩
  intro P L R inst _ _ noRectangle C mono correct
  let E : Finset (Fin P × Fin L) := Finset.univ.filter fun z => R z.1 z.2
  have memE (a : Fin P) (b : Fin L) : (a,b) ∈ E ↔ R a b := by simp [E]
  have count : E.card = ∑ i : Fin P, (Finset.univ.filter (R i)).card := by
    rw [Finset.card_eq_sum_ones]
    simp only [E, Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, one_mul, Prod.fst, Prod.snd]
  obtain ⟨support,restrict⟩ := transfer P L E C mono (by simpa only [memE] using correct)
  obtain ⟨A,B,hpay,hexpand⟩ := core P L d E
  let F := E.filter fun z => z.1 ∈ A ∧ z.2 ∈ B
  obtain ⟨D,hD,hs,hcorrect⟩ := restrict A B
  have bound : F.card ≤ k*(D.size+1) := price P L A B F
    (fun _ h => (Finset.mem_filter.mp h).2)
    (fun a b x y ax bx ay by' => noRectangle a b x y
      ((memE ..).mp (Finset.mem_filter.mp ax).1) ((memE ..).mp (Finset.mem_filter.mp bx).1)
      ((memE ..).mp (Finset.mem_filter.mp ay).1) ((memE ..).mp (Finset.mem_filter.mp by').1))
    hexpand D hD hcorrect
  rw [← count]
  calc
    E.card ≤ F.card + d*((E.image Prod.fst).card+(E.image Prod.snd).card) :=
      (Nat.le_add_right _ _).trans hpay
    _ ≤ k*(C.size+1) + d*(2*(C.size+1)) :=
      Nat.add_le_add (bound.trans (Nat.mul_le_mul_left _ (by omega))) (Nat.mul_le_mul_left _ support)
    _ = (k+2*d)*(C.size+1) := by ring
