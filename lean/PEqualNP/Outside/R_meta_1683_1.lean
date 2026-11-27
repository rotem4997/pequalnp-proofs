import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Keep the eight ordinary point stars outside the five selected centers.
-- The smaller search has seventeen inputs and forty-four maximal rejected rows.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_1683_1 :
    (∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack 17 D ∧ D.size ≤ 23 ∧
      (let offsets : Finset (Fin 13) := {0, 1, 3, 9}
      let pick := fun k : Fin 17 =>
        Fin.ofNat 26 (if k.val < 5 then k.val else if k.val < 14 then k.val + 8 else k.val + 9)
      ∀ p w : Fin 13, p.val < 5 → (∃ d ∈ offsets, p = w + d) → circuitFun 17 D
        (fun k => decide (pick k = Fin.castAdd 13 p ∨ pick k = Fin.natAdd 13 w)) = true) ∧
      (∀ m ∈ ([31, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 8207, 8455,
        8718, 9229, 10251, 12295, 14723, 16414, 16910, 17436, 18458, 20502, 24590,
        29446, 33821, 34841, 36885, 40081, 40973, 44105, 46341, 48577, 49180, 54324,
        58892, 63268, 67610, 81946, 88210, 92682, 97154, 117784, 122032, 126536, 131040] : List ℕ), ∀ x : Fin 17 → Bool,
        (∀ k, x k = true → m.testBit k.val = true) → circuitFun 17 D x = false)) →
    (∀ P : Finset (Fin 13),
      let offsets : Finset (Fin 13) := {0, 1, 3, 9}
      let I := fun (p w : Fin 13) => ∃ d ∈ offsets, p = w + d
      let miss := fun w : Fin 13 => ∀ p ∈ P, ¬ I p w
      let pick := fun k : Fin 17 =>
        Fin.ofNat 26 (if k.val < 5 then k.val else if k.val < 14 then k.val + 8 else k.val + 9)
      (∀ v ∉ P, ∃ w, miss w ∧ I v w) →
      ((∃ w, ∀ p ∈ P, I p w) ∨ (∃ v, ∀ w, miss w → I v w)) →
      ∃ m ∈ ([31, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 8207, 8455,
        8718, 9229, 10251, 12295, 14723, 16414, 16910, 17436, 18458, 20502, 24590,
        29446, 33821, 34841, 36885, 40081, 40973, 44105, 46341, 48577, 49180, 54324,
        58892, 63268, 67610, 81946, 88210, 92682, 97154, 117784, 122032, 126536, 131040] : List ℕ), ∀ k : Fin 17,
        ((∃ p ∈ P, pick k = Fin.castAdd 13 p) ∨
          (∃ w : Fin 13, pick k = Fin.natAdd 13 w ∧ miss w)) →
        m.testBit k.val = true) →
    (∃ E : Circuit, Monotone2 E ∧ NestedCover.ReadsBack 26 E ∧ E.size ≤ 39 ∧
      (let offsets : Finset (Fin 13) := {0, 1, 3, 9}
      let I := fun (p w : Fin 13) => ∃ d ∈ offsets, p = w + d
      ∀ x : Fin 26 → Bool, circuitFun 26 E x =
        decide (∃ p w : Fin 13, 5 ≤ p.val ∧ I p w ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true))) →
    (∀ (m n : ℕ) (f : Fin m → Fin n) (D E : Circuit),
      Monotone2 D → NestedCover.ReadsBack m D → Monotone2 E → NestedCover.ReadsBack n E →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + E.size + 1 ∧
        ∀ x : Fin n → Bool, circuitFun n C x =
          (circuitFun m D (fun k => x (f k)) || circuitFun n E x)) →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false) := by
  intro patch cover remainder assemble
  obtain ⟨D, dMon, dBack, dSize, dPos, dNeg⟩ := patch
  obtain ⟨E, eMon, eBack, eSize, eSpec⟩ := remainder
  let pick : Fin 17 → Fin 26 := fun k : Fin 17 =>
        Fin.ofNat 26 (if k.val < 5 then k.val else if k.val < 14 then k.val + 8 else k.val + 9)
  let I := fun (p w : Fin 13) => ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d
  obtain ⟨C, cMon, cSize, cSpec⟩ := assemble 17 26 pick D E dMon dBack eMon eBack
  have opposite (p w : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 w := by
    intro h
    have h' := congrArg Fin.val h
    change p.val = 13 + w.val at h'
    have hp := p.isLt
    omega
  have point_inj (p q : Fin 13) (h : Fin.castAdd 13 p = Fin.castAdd 13 q) : p = q :=
    Fin.ext (congrArg (fun k : Fin 26 => k.val) h)
  have line_inj (p q : Fin 13) (h : Fin.natAdd 13 p = Fin.natAdd 13 q) : p = q := by
    apply Fin.ext
    have h' := congrArg Fin.val h
    change 13 + p.val = 13 + q.val at h'
    omega
  refine ⟨C, cMon, by omega, ?_, ?_⟩
  · intro p w hi
    let X : Fin 26 → Bool := fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)
    change circuitFun 26 C X = true
    rw [cSpec]
    by_cases hs : p.val < 5
    · have h := dPos p w hs hi
      change circuitFun 17 D (fun k => X (pick k)) = true at h
      rw [h]
      rfl
    · have hz : circuitFun 26 E X = true := by
        rw [eSpec]
        apply decide_eq_true
        exact ⟨p, w, by omega, hi, by simp [X], by simp [X]⟩
      rw [hz, Bool.or_true]
  · intro P hclosed hdeg
    let miss := fun w : Fin 13 => ∀ p ∈ P, ¬ I p w
    let X : Fin 26 → Bool := fun k => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
      (∃ w : Fin 13, k = Fin.natAdd 13 w ∧ miss w))
    change circuitFun 26 C X = false
    obtain ⟨m, hm, hz⟩ := cover P hclosed hdeg
    have hD : circuitFun 17 D (fun k => X (pick k)) = false :=
      dNeg m hm _ (fun k hk => hz k (of_decide_eq_true hk))
    have hE : circuitFun 26 E X = false := by
      rw [eSpec]
      apply decide_eq_false
      rintro ⟨p, w, _, hi, hp, hw⟩
      have hp' : p ∈ P := by
        rcases of_decide_eq_true hp with ⟨q, hq, he⟩ | ⟨v, he, _⟩
        · simpa [point_inj p q he] using hq
        · exact False.elim (opposite p v he)
      have hw' : miss w := by
        rcases of_decide_eq_true hw with ⟨q, _, he⟩ | ⟨v, he, hv⟩
        · exact False.elim (opposite q w he.symm)
        · simpa [line_inj w v he] using hv
      exact hw' p hp' hi
    rw [cSpec, hD, hE]
    rfl
