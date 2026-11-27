import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1874_421
    (removeAlias : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b j r : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
      a < j → n ≤ j → j < n + C.size → b < n + C.size → r < j →
      (∀ x : List Bool, x.length = n →
        (((C.wires x).getD j false = true) → (C.wires x).getD r false = true) ∧
        (((C.wires x).getD a false = true) → (C.wires x).getD j false = (C.wires x).getD r false)) →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (b' : ℕ),
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧
        D.size + 1 = C.size ∧ a < n + D.size ∧ b' < n + D.size ∧
        ∀ x : List Bool, x.length = n →
          (D.wires x).getD a false = (C.wires x).getD a false ∧
          (((C.wires x).getD b false = true) → (D.wires x).getD b' false = true) ∧
          (((C.wires x).getD a false = true) →
            (D.wires x).getD b' false = (C.wires x).getD b false))
    (rigidBound : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∧ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∨ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), x11 x15 ∧ x12 x2 (x10 x15) = Bool.false ∧ x12 x3 (x10 x15) = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), x11 x16 ∧ x12 x3 (x10 x16) = Bool.false ∧ x12 x2 (x10 x16) = Bool.true) → (∀ a ∈ [x2,x3], ∀ j r, a < j → 26 ≤ j → j < 26 + x1.size → r < j → (∀ x : List Bool, x.length = 26 → (x12 j x = true → x12 r x = true) ∧ (x12 a x = true → x12 j x = x12 r x)) → False) → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∧ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∨ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), x11 x15 ∧ x12 x2 (x10 x15) = Bool.false ∧ x12 x3 (x10 x15) = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), x11 x16 ∧ x12 x3 (x10 x16) = Bool.false ∧ x12 x2 (x10 x16) = Bool.true) → (63 : ℕ) ≤ x1.size := by
  let marks : Finset (Fin 13) := {0, 1, 3, 9}
  let pos (p l : Fin 13) : List Bool :=
    (List.ofFn fun i : Fin 13 => decide (i = p)) ++
      List.ofFn fun i : Fin 13 => decide (i = l)
  let neg (S : Finset (Fin 13)) : List Bool :=
    (List.ofFn fun i : Fin 13 => decide (i ∈ S)) ++
      List.ofFn fun i : Fin 13 => decide (∀ p ∈ S, p - i ∉ marks)
  let quad (S : Finset (Fin 13)) : Prop :=
    S.card = 4 ∧ ∀ l : Fin 13, {p ∈ S | p - l ∈ marks}.card ≤ 2
  let value (C : PEqualNP.CircuitLowerBounds.Circuit) (i : ℕ) (x : List Bool) : Bool :=
    (C.wires x).getD i false
  let paired (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ) : Prop :=
    (∀ p l : Fin 13, p - l ∈ marks →
      value C a (pos p l) = true ∧ value C b (pos p l) = true) ∧
    (∀ S : Finset (Fin 13), quad S →
      value C a (neg S) = false ∨ value C b (neg S) = false) ∧
    (∃ S : Finset (Fin 13), quad S ∧ value C a (neg S) = false ∧ value C b (neg S) = true) ∧
    (∃ S : Finset (Fin 13), quad S ∧ value C b (neg S) = false ∧ value C a (neg S) = true)
  let rigid (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ) : Prop :=
    ∀ d ∈ [a, b], ∀ j r, d < j → 26 ≤ j → j < 26 + C.size → r < j →
      (∀ x : List Bool, x.length = 26 →
        (value C j x = true → value C r x = true) ∧
        (value C d x = true → value C j x = value C r x)) → False
  classical
  have posLength (p l : Fin 13) : (pos p l).length = 26 := by
    simp [pos]
  have negLength (S : Finset (Fin 13)) : (neg S).length = 26 := by
    simp [neg]
  have swapPair (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ)
      (h : paired C a b) : paired C b a := by
    rcases h with ⟨hp,hn,ha,hb⟩
    exact ⟨fun p l h => (hp p l h).symm, fun S h => (hn S h).symm, hb, ha⟩
  have transportPair (C D : PEqualNP.CircuitLowerBounds.Circuit) (a b b' : ℕ)
      (h : paired C a b)
      (hv : ∀ x : List Bool, x.length = 26 →
        value D a x = value C a x ∧
        (value C b x = true → value D b' x = true) ∧
        (value C a x = true → value D b' x = value C b x)) :
      paired D a b' := by
    rcases h with ⟨hp,hn,ha,hb⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro p l hi
      obtain ⟨h1,h2⟩ := hp p l hi
      obtain ⟨same,grow,_⟩ := hv (pos p l) (posLength p l)
      exact ⟨same.trans h1, grow h2⟩
    · intro S hq
      obtain ⟨same,_,agree⟩ := hv (neg S) (negLength S)
      rcases hn S hq with h1 | h2
      · exact Or.inl (same.trans h1)
      · cases he : value C a (neg S)
        · exact Or.inl (same.trans he)
        · exact Or.inr ((agree he).trans h2)
    · obtain ⟨S,hq,h1,h2⟩ := ha
      obtain ⟨same,grow,_⟩ := hv (neg S) (negLength S)
      exact ⟨S,hq,same.trans h1,grow h2⟩
    · obtain ⟨S,hq,h2,h1⟩ := hb
      obtain ⟨same,_,agree⟩ := hv (neg S) (negLength S)
      exact ⟨S,hq,(agree h1).trans h2,same.trans h1⟩
  have bound (s : ℕ) : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
      C.size = s → PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
      a < 26 + C.size → b < 26 + C.size → paired C a b → 63 ≤ C.size := by
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro C a b hs hm hr ha hb hpair
      by_cases hrigid : rigid C a b
      · exact rigidBound C a b hm hr ha hb hpair.1 hpair.2.1 hpair.2.2.1 hpair.2.2.2 hrigid
      · have hw :
            ∃ d ∈ [a,b], ∃ j r, d < j ∧ 26 ≤ j ∧ j < 26 + C.size ∧ r < j ∧
              ∀ x : List Bool, x.length = 26 →
                (value C j x = true → value C r x = true) ∧
                (value C d x = true → value C j x = value C r x) := by
          dsimp only [rigid] at hrigid
          push Not at hrigid
          simpa only [and_true] using hrigid
        obtain ⟨d,hd,j,r,had,hj₀,hj,hrr,hrows⟩ := hw
        have hd' : d = a ∨ d = b := by simpa using hd
        rcases hd' with hda | hdb
        · subst d
          obtain ⟨D,b',hm',hr',hsize,ha',hb',hv⟩ :=
            removeAlias 26 C a b j r hm hr had hj₀ hj hb hrr hrows
          have small : D.size < s := by omega
          have h := ih D.size small D a b' rfl hm' hr' ha' hb'
            (transportPair C D a b b' hpair hv)
          omega
        · subst d
          obtain ⟨D,a',hm',hr',hsize,hb',ha',hv⟩ :=
            removeAlias 26 C b a j r hm hr had hj₀ hj ha hrr hrows
          have small : D.size < s := by omega
          have h := ih D.size small D b a' rfl hm' hr' hb' ha'
            (transportPair C D b a a' (swapPair C a b hpair) hv)
          omega
  intro C a b hm hr ha hb _ _ _ _ _ hp hn hleft hright
  exact bound C.size C a b rfl hm hr ha hb ⟨hp,hn,hleft,hright⟩
