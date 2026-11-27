import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.HeptadCover PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_5202_73
    (hGeometry : ∀ i : Fin 26, ∃ Q : Finset (Fin 13),
      IsQuadrangle singerLines3 Q ∧
      (incidenceInput Q (missLines singerLines3 Q)).getD i.val false = true)
    (hFrontier : ∀ (n : ℕ) (C : Circuit) (w : ℕ), Monotone2 C →
      (∀ i : Fin n, ∃ y : List Bool, y.length = n ∧ y.getD i.val false = true ∧
        wireValue C y w = false) →
      ∀ x : List Bool, x.length = n →
        (wireValue C x w = true ↔ ∃ j < C.size, OrReaches n C w j ∧
          (gateAt C j).op = GateOp.and ∧ wireValue C x (n + j) = true))
    (hCount : ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack 26 C →
      a < 26 + C.size → b < 26 + C.size →
      let S := singerLines3
      let fires := fun (w : ℕ) (x : List Bool) =>
        ∃ j < C.size, OrReaches 26 C w j ∧ (gateAt C j).op = GateOp.and ∧
          wireValue C x (26 + j) = true
      let flag := fun (w : ℕ) (p l : Fin 13) => fires w (incidenceInput {p} {l})
      (∀ p l, p ∈ S l → flag a p l ∨ flag b p l) →
      (∀ Q, IsQuadrangle S Q →
        ¬ (fires a (incidenceInput Q (missLines S Q)) ∨ fires b (incidenceInput Q (missLines S Q)))) →
      (∃ p l, p ∈ S l ∧ flag a p l ∧ ¬ flag b p l) →
      (∃ p l, p ∈ S l ∧ flag b p l ∧ ¬ flag a p l) →
      (∃ J : Finset ℕ, J.card = 3 ∧ ∀ j ∈ J, j < C.size ∧ (gateAt C j).op = GateOp.and ∧
        ∃ k ∈ (gateAt C j).inputs, 26 ≤ k ∧ (gateAt C (k - 26)).op = GateOp.and) →
      63 ≤ C.size)
    : have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (x4 x6 x7).op = x5 ∧ ∃ x8 ∈ (x4 x6 x7).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x6 (x8 - (26 : ℕ))).op = x5; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → x8 < (26 : ℕ) + x7.size → x9 < (26 : ℕ) + x7.size → (∀ (x14 x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 → x3 x7 x8 (x2 {x14} {x15}) = Bool.true ∨ x3 x7 x9 (x2 {x14} {x15}) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x15 → x3 x7 x8 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false ∧ x3 x7 x9 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 ∈ x1 x17 ∧ x3 x7 x8 (x2 {x16} {x17}) = Bool.true ∧ x3 x7 x9 (x2 {x16} {x17}) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 ∈ x1 x18 ∧ x3 x7 x9 (x2 {x17} {x18}) = Bool.true ∧ x3 x7 x8 (x2 {x17} {x18}) = Bool.false) → (∃ x18 ∈ Finset.range x7.size, ∃ x19 ∈ Finset.range x7.size, ∃ x20 ∈ Finset.range x7.size, x18 ≠ x19 ∧ x18 ≠ x20 ∧ x19 ≠ x20 ∧ x6 x7 x18 ∧ x6 x7 x19 ∧ x6 x7 x20) → (63 : ℕ) ≤ x7.size := by
  dsimp only
  intro C a b hMono hBack ha hb hCover hReject hOnlyA hOnlyB hNested
  let bad := fun Q : Finset (Fin 13) => incidenceInput Q (missLines singerLines3 Q)
  let flagInput := fun p l : Fin 13 => incidenceInput {p} {l}
  let fires := fun (w : ℕ) (x : List Bool) =>
    ∃ j < C.size, OrReaches 26 C w j ∧ (gateAt C j).op = GateOp.and ∧
      wireValue C x (26 + j) = true
  have hBadLen (Q : Finset (Fin 13)) : (bad Q).length = 26 := by
    change ((List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
      (List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))).length = 26
    simp
  have hFlagLen (p l : Fin 13) : (flagInput p l).length = 26 := by
    change ((List.ofFn fun u : Fin 13 => decide (u ∈ ({p} : Finset (Fin 13)))) ++
      (List.ofFn fun v : Fin 13 => decide (v ∈ ({l} : Finset (Fin 13))))).length = 26
    simp
  have trace (w : ℕ) (reject : ∀ Q, IsQuadrangle singerLines3 Q →
        wireValue C (bad Q) w = false) :
      ∀ x : List Bool, x.length = 26 → (wireValue C x w = true ↔ fires w x) := by
    apply hFrontier 26 C w hMono
    intro i
    obtain ⟨Q, hQ, hi⟩ := hGeometry i
    exact ⟨bad Q, hBadLen Q, hi, reject Q hQ⟩
  have traceA := trace a (fun Q hQ => (hReject Q hQ).1)
  have traceB := trace b (fun Q hQ => (hReject Q hQ).2)
  apply hCount C a b hMono hBack ha hb
  · intro p l hpl
    exact (hCover p l hpl).imp ((traceA _ (hFlagLen p l)).mp) ((traceB _ (hFlagLen p l)).mp)
  · intro Q hQ h
    obtain ⟨hA, hB⟩ := hReject Q hQ
    rcases h with h | h
    · exact Bool.noConfusion ((traceA _ (hBadLen Q)).mpr h |>.symm.trans hA)
    · exact Bool.noConfusion ((traceB _ (hBadLen Q)).mpr h |>.symm.trans hB)
  · obtain ⟨p, l, hpl, hA, hB⟩ := hOnlyA
    exact ⟨p, l, hpl, (traceA _ (hFlagLen p l)).mp hA, fun h =>
      Bool.noConfusion ((traceB _ (hFlagLen p l)).mpr h |>.symm.trans hB)⟩
  · obtain ⟨p, l, hpl, hB, hA⟩ := hOnlyB
    exact ⟨p, l, hpl, (traceB _ (hFlagLen p l)).mp hB, fun h =>
      Bool.noConfusion ((traceA _ (hFlagLen p l)).mpr h |>.symm.trans hA)⟩
  · obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk, ai, aj, ak⟩ := hNested
    refine ⟨{i, j, k}, ?_, ?_⟩
    · simp [hij, hik, hjk]
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact ⟨Finset.mem_range.mp hi, ai⟩
      · exact ⟨Finset.mem_range.mp hj, aj⟩
      · exact ⟨Finset.mem_range.mp hk, ak⟩
