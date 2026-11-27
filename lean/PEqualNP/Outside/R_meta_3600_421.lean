import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_3600_421
    (frontier : ∀ (d : ℕ) (C : Circuit), Monotone2 C → ReadsBack d C → C.output < d + C.size →
      (∀ v : Fin d, circuitFun d C (fun i => decide (i = v)) = false) →
      ∃ F : Finset ℕ, (∀ j ∈ F, j < C.size ∧ (gateAt C j).op = .and) ∧
        ∀ x : Fin d → Bool, circuitFun d C x = true ↔ ∃ j ∈ F, gateVal d C j x = true)
    (remaining : ∀ (q n : ℕ) (R : Fin n → Fin n → Prop) [DecidableRel R]
      (C : Circuit) (F : Finset ℕ),
      300 ≤ q → n = q ^ 2 + q + 1 →
      (∀ l : Fin n, Fintype.card {p : Fin n // R p l} = q + 1) →
      (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, R p l ∧ R r l) →
      Monotone2 C → n + n ≤ C.output → C.output < n + n + C.size →
      (∃ g : Gate, C.gates[C.output - (n + n)]? = some g ∧ g.op = .or) →
      (∀ (i : ℕ) (g : Gate), C.gates[i]? = some g →
        ∃ (a b : ℕ), g.inputs = [a,b] ∧ a < b ∧ b < n + n + i) →
      (∀ j ∈ F, j < C.size ∧ (gateAt C j).op = .and) →
      (∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = true ↔
        ∃ j ∈ F, gateVal (n + n) C j x = true) →
      (∀ p l : Fin n, R p l → ∃ j ∈ F,
        gateVal (n + n) C j (fun z => decide (z = Fin.castAdd n p ∨ z = Fin.natAdd n l)) = true) →
      (∀ x : Fin (n + n) → Bool,
        Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        (¬ ∃ p l : Fin n, R p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
        ∀ j ∈ F, gateVal (n + n) C j x = false) → n * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) → (∀ (x15 x16 : Fin x2), x3 x15 x16 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16)) = Bool.true) → (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x16 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n R _ C hq hn hl hmeet hmono hlo hhi hor htop haccept hsound
  have hback : ReadsBack (n + n) C := by
    intro i hi k hk
    have hgat : gateAt C i = C.gates[i] := List.getD_eq_getElem _ _ hi
    obtain ⟨a, b, hinputs, hab, hb⟩ := htop i C.gates[i] (List.getElem?_eq_getElem hi)
    rw [hgat, hinputs] at hk
    simp at hk
    rcases hk with rfl | rfl <;> omega
  have hsingle (v : Fin (n + n)) :
      circuitFun (n + n) C (fun i => decide (i = v)) = false := by
    let x : Fin (n + n) → Bool := fun i => decide (i = v)
    have hx (w : Fin (n + n)) (h : x w = true) : w = v := of_decide_eq_true h
    have hsub : Subsingleton { l : Fin n // x (Fin.natAdd n l) = true } := by
      constructor
      intro l k
      apply Subtype.ext
      apply Fin.ext
      have he := congrArg Fin.val ((hx _ l.property).trans (hx _ k.property).symm)
      simp only [Fin.val_natAdd] at he
      omega
    apply hsound x (le_trans (Fintype.card_le_one_iff_subsingleton.mpr hsub) (by omega))
    rintro ⟨p, l, _, hp, hl⟩
    have he := congrArg Fin.val ((hx _ hp).trans (hx _ hl).symm)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at he
    omega
  obtain ⟨F, hgate, hequiv⟩ := frontier (n + n) C hmono hback hhi hsingle
  apply remaining q n R C F hq hn hl hmeet hmono hlo hhi hor htop hgate hequiv
  · intro p l hp
    exact (hequiv _).mp (haccept p l hp)
  · intro x hx hfree j hj
    cases hg : gateVal (n + n) C j x
    · rfl
    · have ht := (hequiv x).mpr ⟨j, hj, hg⟩
      rw [hsound x hx hfree] at ht
      contradiction
