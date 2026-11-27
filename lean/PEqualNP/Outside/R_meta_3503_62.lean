import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Minimize size first, then the number of nested pairs of AND gates.
-- In the typing obligation only the two monochromatic test inputs are needed.
theorem PEqualNP.Outside.R_meta_3503_62
    (unnest : ∀ (m n : ℕ) (I : Fin m → Fin n → Prop) [DecidableRel I] (C : Circuit),
      (∀ p q l s, p ≠ q → l ≠ s → ¬ (I p l ∧ I p s ∧ I q l ∧ I q s)) →
      IsAO2 (m+n) C →
      (∀ x, circuitFun (m+n) C x = decide (∃ p l, I p l ∧
        x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true)) →
      (∀ B : Circuit, IsAO2 (m+n) B → circuitFun (m+n) B = circuitFun (m+n) C →
        C.size ≤ B.size) →
      0 < andPairs (m+n) C →
      ∃ B : Circuit, IsAO2 (m+n) B ∧ circuitFun (m+n) B = circuitFun (m+n) C ∧
        B.size ≤ C.size ∧ andPairs (m+n) B < andPairs (m+n) C)
    (typeProducts : ∀ (m n : ℕ) (C : Circuit), IsAO2 (m+n) C →
      (∀ B : Circuit, IsAO2 (m+n) B → circuitFun (m+n) B = circuitFun (m+n) C →
        C.size ≤ B.size) →
      andPairs (m+n) C = 0 →
      circuitFun (m+n) C (fun i => decide (i.val < m)) = false →
      circuitFun (m+n) C (fun i => decide (m ≤ i.val)) = false →
      ∃ S : Bool → Finset ℕ,
        (∀ t w, w ∈ S t → (w < m+n ∧ decide (m ≤ w) = t) ∨
          ∃ j < C.size, w = m+n+j ∧ (NestedCover.gateAt C j).op = GateOp.or ∧
            ∀ u ∈ (NestedCover.gateAt C j).inputs, u ∈ S t) ∧
        ∀ j < C.size, (NestedCover.gateAt C j).op = GateOp.and →
          ∃ a b t, (NestedCover.gateAt C j).inputs = [a,b] ∧ a ∈ S t ∧ b ∈ S (!t)) :
    ∀ (m n : ℕ) (I : Fin m → Fin n → Prop) [DecidableRel I] (C : Circuit),
      (∀ (p q : Fin m) (l s : Fin n),
        p ≠ q → l ≠ s → ¬ (I p l ∧ I p s ∧ I q l ∧ I q s)) →
      IsAO2 (m + n) C →
      (∀ x : Fin (m + n) → Bool, circuitFun (m + n) C x =
        decide (∃ (p : Fin m) (l : Fin n),
          I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true)) →
      ∃ (D : Circuit) (P L : Finset ℕ), IsAO2 (m + n) D ∧
        (∀ x : Fin (m + n) → Bool, circuitFun (m + n) D x =
          decide (∃ (p : Fin m) (l : Fin n),
            I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true)) ∧
        D.size ≤ C.size ∧
        (∀ w ∈ P, w < m ∨ ∃ j < D.gates.length, w = m + n + j ∧
          (NestedCover.gateAt D j).op = GateOp.or ∧
          ∀ a ∈ (NestedCover.gateAt D j).inputs, a ∈ P) ∧
        (∀ w ∈ L, m ≤ w ∧ w < m + n ∨ ∃ j < D.gates.length, w = m + n + j ∧
          (NestedCover.gateAt D j).op = GateOp.or ∧
          ∀ a ∈ (NestedCover.gateAt D j).inputs, a ∈ L) ∧
        ∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
          ∃ a b : ℕ, (NestedCover.gateAt D j).inputs = [a, b] ∧
            (a ∈ P ∧ b ∈ L ∨ a ∈ L ∧ b ∈ P) := by
  classical
  intro m n I inst C hfour hC hF
  let valid (B : Circuit) := IsAO2 (m+n) B ∧ circuitFun (m+n) B = circuitFun (m+n) C
  let sizes (k : ℕ) := ∃ B : Circuit, valid B ∧ B.size = k
  have hs : ∃ k, sizes k := ⟨C.size, C, ⟨hC, rfl⟩, rfl⟩
  obtain ⟨B, hB, hBs⟩ := Nat.find_spec hs
  let counts (k : ℕ) := ∃ D : Circuit, valid D ∧ D.size = Nat.find hs ∧ andPairs (m+n) D = k
  have hc : ∃ k, counts k := ⟨_, B, hB, hBs, rfl⟩
  obtain ⟨D, hD, hDs, hDc⟩ := Nat.find_spec hc
  have least (A : Circuit) (hA : IsAO2 (m+n) A)
      (eqA : circuitFun (m+n) A = circuitFun (m+n) D) : D.size ≤ A.size := by
    rw [hDs]
    exact Nat.find_min' hs ⟨A, ⟨hA, eqA.trans hD.2⟩, rfl⟩
  have exactD (x : Fin (m+n) → Bool) := (congrFun hD.2 x).trans (hF x)
  have zero : andPairs (m+n) D = 0 := by
    by_contra hn
    obtain ⟨A, hA, eqA, small, less⟩ := unnest m n I D hfour hD.1 exactD least
      (Nat.pos_of_ne_zero hn)
    have sz : A.size = Nat.find hs := (Nat.le_antisymm small (least A hA eqA)).trans hDs
    have bound := Nat.find_min' hc (show counts (andPairs (m+n) A) from
      ⟨A, ⟨hA, eqA.trans hD.2⟩, sz, rfl⟩)
    omega
  have leftOff : circuitFun (m+n) D (fun i => decide (i.val < m)) = false := by
    rw [exactD]
    apply decide_eq_false
    rintro ⟨p, l, _, _, hl⟩
    have bad := of_decide_eq_true hl
    change m + l.val < m at bad
    omega
  have rightOff : circuitFun (m+n) D (fun i => decide (m ≤ i.val)) = false := by
    rw [exactD]
    apply decide_eq_false
    rintro ⟨p, l, _, hp, _⟩
    have bad := of_decide_eq_true hp
    change m ≤ p.val at bad
    exact Nat.not_le_of_lt p.isLt bad
  obtain ⟨S, closed, prod⟩ := typeProducts m n D hD.1 least zero leftOff rightOff
  refine ⟨D, S false, S true, hD.1, exactD, least C hC hD.2.symm, ?_, ?_, ?_⟩
  · intro w hw
    rcases closed false w hw with ⟨_, ht⟩ | h
    · exact Or.inl (by simpa using ht)
    · exact Or.inr h
  · intro w hw
    rcases closed true w hw with ⟨hb, ht⟩ | h
    · exact Or.inl ⟨by simpa using ht, hb⟩
    · exact Or.inr h
  · intro j hj hop
    obtain ⟨a, b, t, eqn, ha, hb⟩ := prod j hj hop
    refine ⟨a, b, eqn, ?_⟩
    cases t
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
