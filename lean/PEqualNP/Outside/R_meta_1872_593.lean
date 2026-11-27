import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

-- Suppress reads of the two exposed wires before applying the resulting sink case.
theorem PEqualNP.Outside.R_meta_1872_593
  (normal : ∀ (n : ℕ) (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack n C →
    ∃ D : Circuit, D.size=C.size ∧ Monotone2 D ∧ ReadsBack n D ∧
      (∀ g ∈ D.gates, a ∉ g.inputs ∧ b ∉ g.inputs) ∧
      ∀ x : List Bool, x.length=n →
        have u := (C.wires x).getD a false
        have v := (C.wires x).getD b false
        have u' := (D.wires x).getD a false
        have v' := (D.wires x).getD b false
        (u' || v') = (u || v) ∧
        (u=true → v=false → u'=true ∧ v'=false) ∧
        (v=true → u=false → v'=true ∧ u'=false))
  (lower : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → (∀ g ∈ x1.gates, x2 ∉ g.inputs ∧ x3 ∉ g.inputs) → have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10); have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8); have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ); have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false; (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∨ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∧ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Fin (13 : ℕ)) (x16 : Fin (13 : ℕ)), x15 - x16 ∈ x8 ∧ x12 x2 (x9 x15 x16) = Bool.true ∧ x12 x3 (x9 x15 x16) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x8 ∧ x12 x3 (x9 x16 x17) = Bool.true ∧ x12 x2 (x9 x16 x17) = Bool.false) → (63 : ℕ) ≤ x1.size) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10); have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8); have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ); have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false; (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∨ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∧ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Fin (13 : ℕ)) (x16 : Fin (13 : ℕ)), x15 - x16 ∈ x8 ∧ x12 x2 (x9 x15 x16) = Bool.true ∧ x12 x3 (x9 x15 x16) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x8 ∧ x12 x3 (x9 x16 x17) = Bool.true ∧ x12 x2 (x9 x16 x17) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C a b mono back ha hb
  dsimp only
  intro accept reject leftOnly rightOnly
  obtain ⟨D,hs,hm,hr,hsink,hval⟩ := normal 26 C a b mono back
  rw [← hs]
  apply lower D a b hm hr (by rwa [hs]) (by rwa [hs]) hsink
  · intro p l inc
    let x := List.ofFn (fun v : Fin 13 => decide (v=p)) ++ List.ofFn (fun v : Fin 13 => decide (v=l))
    obtain ⟨hv,_,_⟩ := hval x (by simp [x])
    change (D.wires x).getD a false=true ∨ (D.wires x).getD b false=true
    rw [← Bool.or_eq_true,hv,Bool.or_eq_true]
    exact accept p l inc
  · intro Q quad
    let x := List.ofFn (fun v : Fin 13 => decide (v∈Q)) ++
      List.ofFn (fun v : Fin 13 => decide (∀ p∈Q, p-v∉({0,1,3,9} : Finset (Fin 13))))
    obtain ⟨hv,_,_⟩ := hval x (by simp [x])
    obtain ⟨qa,qb⟩ := reject Q quad
    change (C.wires x).getD a false=false at qa
    change (C.wires x).getD b false=false at qb
    simp only [qa,qb,Bool.or_self] at hv
    exact Bool.or_eq_false_iff.mp hv
  · obtain ⟨p,l,inc,wa,wb⟩ := leftOnly
    let x := List.ofFn (fun v : Fin 13 => decide (v=p)) ++ List.ofFn (fun v : Fin 13 => decide (v=l))
    exact ⟨p,l,inc,(hval x (by simp [x])).2.1 wa wb⟩
  · obtain ⟨p,l,inc,wb,wa⟩ := rightOnly
    let x := List.ofFn (fun v : Fin 13 => decide (v=p)) ++ List.ofFn (fun v : Fin 13 => decide (v=l))
    exact ⟨p,l,inc,(hval x (by simp [x])).2.2 wb wa⟩
