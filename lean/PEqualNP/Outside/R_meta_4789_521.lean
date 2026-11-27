import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
-- Select at least one rejecting pair for each of the collinear-triple rows.
-- The first child shows these rows and the positive tests require twenty ORs.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4789_521
    (orBudget :
    let U := Fin 13
    let D : Finset U := {0,1,3,9}
    let I := fun (p l : U) => ∃ d ∈ D, p = l+d
    let A := fun (P : Finset U) (l : U) => ∀ p ∈ P, ¬I p l
    let X := Fin 26 → Bool
    let T := fun (p l : U) (i : Fin 26) => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
    let F := fun (P : Finset U) (i : Fin 26) =>
      decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l, i = Fin.natAdd 13 l ∧ A P l)
    let N := fun (P : Finset U) =>
      (∀ p ∉ P, ∃ l, A P l ∧ I p l) ∧
        ((∃ l, ∀ p ∈ P, I p l) ∨ ∃ p, ∀ l, A P l → I p l)
    ∀ C : Circuit, Monotone2 C →
    let V := fun (i : ℕ) (x : X) => (C.wires (List.ofFn x ++ [true,false])).getD i false
    let H := fun (f : X → Bool) => ∀ p l, I p l → f (T p l) = true
    let test := fun (e : ℕ × ℕ) (x : X) => V e.1 x || V e.2 x
    let covers := fun (K : Finset (ℕ × ℕ)) => ∀ P, N P → ∃ e ∈ K, ¬test e (F P) = true
    ∀ K : Finset (ℕ × ℕ), 2 ≤ K.card → C.size + 2*K.card ≤ 64 →
      (∀ e ∈ K, H (test e) ∧ ¬H (V e.1) ∧ ¬H (V e.2)) → covers K →
      20 ≤ ((Finset.range C.size).filter (fun j => (gateAt C j).op.eval [false,true])).card)
    (remaining :
    let U := Fin 13
    let D : Finset U := {0,1,3,9}
    let I := fun (p l : U) => ∃ d ∈ D, p = l+d
    let A := fun (P : Finset U) (l : U) => ∀ p ∈ P, ¬I p l
    let X := Fin 26 → Bool
    let T := fun (p l : U) (i : Fin 26) => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
    let F := fun (P : Finset U) (i : Fin 26) =>
      decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l, i = Fin.natAdd 13 l ∧ A P l)
    let N := fun (P : Finset U) =>
      (∀ p ∉ P, ∃ l, A P l ∧ I p l) ∧
        ((∃ l, ∀ p ∈ P, I p l) ∨ ∃ p, ∀ l, A P l → I p l)
    ∀ C : Circuit, Monotone2 C →
    let V := fun (i : ℕ) (x : X) => (C.wires (List.ofFn x ++ [true,false])).getD i false
    let H := fun (f : X → Bool) => ∀ p l, I p l → f (T p l) = true
    let test := fun (e : ℕ × ℕ) (x : X) => V e.1 x || V e.2 x
    let covers := fun (K : Finset (ℕ × ℕ)) => ∀ P, N P → ∃ e ∈ K, ¬test e (F P) = true
    ∀ K : Finset (ℕ × ℕ), 2 ≤ K.card → C.size + 2*K.card ≤ 64 →
      (∀ e ∈ K, H (test e) ∧ ¬H (V e.1) ∧ ¬H (V e.2)) → covers K →
      20 ≤ ((Finset.range C.size).filter (fun j => (gateAt C j).op.eval [false,true])).card →
      K.card ≤ 22 → (∀ e ∈ K, ¬covers (K.erase e)) → False) :
    let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x7 : Finset x1 → x5 := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10); ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x9 →     have x11 : ℕ → x5 → Bool := fun (x11 : ℕ) (x12 : x5) => (x9.wires (List.ofFn x12 ++ [Bool.true, Bool.false])).getD x11 Bool.false;     have x12 : (x5 → Bool) → Prop := fun (x12 : x5 → Bool) => ∀ (x13 x14 : x1), x3 x13 x14 → x12 (x6 x13 x14) = Bool.true;     have x13 : ℕ × ℕ → x5 → Bool := fun (x13 : ℕ × ℕ) (x14 : x5) => x11 x13.1 x14 || x11 x13.2 x14;     have x14 : Finset (ℕ × ℕ) → Prop := fun (x14 : Finset (ℕ × ℕ)) => ∀ (x15 : Finset x1), x8 x15 → ∃ x17 ∈ x14, ¬x13 x17 (x7 x15) = Bool.true;     ∀ (x15 : Finset (ℕ × ℕ)), (2 : ℕ) ≤ x15.card → x9.size + (2 : ℕ) * x15.card ≤ (64 : ℕ) → (∀ x18 ∈ x15, x12 (x13 x18) ∧ ¬x12 (x11 x18.1) ∧ ¬x12 (x11 x18.2)) → x14 x15 → (∀ x20 ∈ x15, ¬x14 (x15.erase x20)) → False := by
  dsimp only at orBudget remaining ⊢
  intro C mono K lower budget good covered minimal
  have many := orBudget C mono K lower budget good covered
  have count : ((Finset.range C.size).filter (fun j => (gateAt C j).op.eval [false,true])).card ≤ C.size := by
    simpa using (Finset.card_le_card (Finset.filter_subset
      (fun j => (gateAt C j).op.eval [false,true] = true) (Finset.range C.size)))
  exact remaining C mono K lower budget good covered many (by omega) minimal
