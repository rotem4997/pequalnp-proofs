import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6015

lemma agree_eq
    (x1 x2 : ℕ) (x3 : (Fin x2 → Bool) → ℕ → Finset ℕ)
    (a b : Fin x2 → ℕ)
    (hbase : ∀ (x4 : Fin x2 → Bool), ∀ x5 < x1, x3 x4 x5 = {x5})
    (ha : ∀ i : Fin x2, a i < x1 + i.val)
    (hb : ∀ i : Fin x2, b i < x1 + i.val)
    (hgate : ∀ i : Fin x2,
      (∀ x8, x3 x8 (x1 + i.val) = x3 x8 (a i) ∪ x3 x8 (b i)) ∨
      (∀ x8, x3 x8 (x1 + i.val) = if x8 i = Bool.true then x3 x8 (a i) else x3 x8 (b i)) ∨
      (∀ x8, x3 x8 (x1 + i.val) = ∅))
    (k : ℕ) (hk : k ≤ x2) (x8 x8' : Fin x2 → Bool)
    (hagree : ∀ j : Fin x2, j.val < k → x8 j = x8' j) :
    ∀ w < x1 + k, x3 x8 w = x3 x8' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hw1 : w < x1
    · rw [hbase x8 w hw1, hbase x8' w hw1]
    · let i : Fin x2 := ⟨w - x1, by omega⟩
      have hw_eq : w = x1 + i.val := by
        change w = x1 + (w - x1)
        omega
      have hik : i.val < k := by
        change w - x1 < k
        omega
      have hai : a i < w := by
        have := ha i
        omega
      have hbi : b i < w := by
        have := hb i
        omega
      rw [hw_eq]
      rcases hgate i with hu | hc | he
      · rw [hu x8, hu x8', ih (a i) hai (by omega), ih (b i) hbi (by omega)]
      · rw [hc x8, hc x8', hagree i hik, ih (a i) hai (by omega), ih (b i) hbi (by omega)]
      · rw [he x8, he x8']

noncomputable def canon
    (x2 : ℕ) (x3 : (Fin x2 → Bool) → ℕ → Finset ℕ)
    (a : Fin x2 → ℕ) (S : Set ℕ) (i : Fin x2) : Bool :=
  @decide (∃ x8 : Fin x2 → Bool, ∀ y ∈ x3 x8 (a i), y ∈ S) (Classical.propDecidable _)

lemma canon_sub
    (x1 x2 : ℕ) (x3 : (Fin x2 → Bool) → ℕ → Finset ℕ)
    (a b : Fin x2 → ℕ) (S : Set ℕ)
    (hbase : ∀ (x4 : Fin x2 → Bool), ∀ x5 < x1, x3 x4 x5 = {x5})
    (ha : ∀ i : Fin x2, a i < x1 + i.val)
    (hb : ∀ i : Fin x2, b i < x1 + i.val)
    (hgate : ∀ i : Fin x2,
      (∀ x8, x3 x8 (x1 + i.val) = x3 x8 (a i) ∪ x3 x8 (b i)) ∨
      (∀ x8, x3 x8 (x1 + i.val) = if x8 i = Bool.true then x3 x8 (a i) else x3 x8 (b i)) ∨
      (∀ x8, x3 x8 (x1 + i.val) = ∅)) :
    ∀ w < x1 + x2, (∃ x8 : Fin x2 → Bool, ∀ y ∈ x3 x8 w, y ∈ S) →
      ∀ y ∈ x3 (canon x2 x3 a S) w, y ∈ S := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw ⟨x8, hx8⟩
    by_cases hw1 : w < x1
    · rw [hbase (canon x2 x3 a S) w hw1]
      rw [hbase x8 w hw1] at hx8
      exact hx8
    · let i : Fin x2 := ⟨w - x1, by omega⟩
      have hw_eq : w = x1 + i.val := by
        change w = x1 + (w - x1)
        omega
      have hai : a i < w := by
        have := ha i
        omega
      have hbi : b i < w := by
        have := hb i
        omega
      rw [hw_eq] at hx8 ⊢
      rcases hgate i with hu | hc | he
      · rw [hu x8] at hx8
        rw [hu (canon x2 x3 a S)]
        have haS : ∀ y ∈ x3 (canon x2 x3 a S) (a i), y ∈ S :=
          ih (a i) hai (by omega) ⟨x8, fun y hy => hx8 y (Finset.mem_union_left _ hy)⟩
        have hbS : ∀ y ∈ x3 (canon x2 x3 a S) (b i), y ∈ S :=
          ih (b i) hbi (by omega) ⟨x8, fun y hy => hx8 y (Finset.mem_union_right _ hy)⟩
        intro y hy
        rcases Finset.mem_union.mp hy with hya | hyb
        · exact haS y hya
        · exact hbS y hyb
      · rw [hc x8] at hx8
        rw [hc (canon x2 x3 a S)]
        by_cases hA : ∃ x8' : Fin x2 → Bool, ∀ y ∈ x3 x8' (a i), y ∈ S
        · have hct : canon x2 x3 a S i = Bool.true := by
            simp only [canon, decide_eq_true_iff]
            exact hA
          simp only [hct, ite_true]
          exact ih (a i) hai (by omega) hA
        · have hcf : canon x2 x3 a S i = Bool.false := by
            simp only [canon, decide_eq_false_iff_not]
            exact hA
          simp only [hcf, Bool.false_eq_true, ite_false]
          have hx8f : x8 i ≠ Bool.true := by
            intro h
            simp only [h, ite_true] at hx8
            exact hA ⟨x8, hx8⟩
          simp only [hx8f] at hx8
          exact ih (b i) hbi (by omega) ⟨x8, hx8⟩
      · rw [he (canon x2 x3 a S)]
        intro y hy
        exact absurd hy (Finset.notMem_empty y)

end PEqualNP.Outside.L_meta_6015

theorem PEqualNP.Outside.L_meta_6015 :
    ∀ (x1 x2 : ℕ) (x3 : (Fin x2 → Bool) → ℕ → Finset ℕ),   (∀ (x4 : Fin x2 → Bool), ∀ x5 < x1, x3 x4 x5 = {x5}) →     (∀ (x5 : Fin x2), ∃ x6 < x1 + ↑x5, ∃ x7 < x1 + ↑x5, (∀ (x8 : Fin x2 → Bool), x3 x8 (x1 + ↑x5) = x3 x8 x6 ∪ x3 x8 x7) ∨ (∀ (x8 : Fin x2 → Bool), x3 x8 (x1 + ↑x5) = if x8 x5 = Bool.true then x3 x8 x6 else x3 x8 x7) ∨ ∀ (x8 : Fin x2 → Bool), x3 x8 (x1 + ↑x5) = ∅) →       have x6 : ℕ → Set (Set ℕ) := fun (x6 : ℕ) => {x7 : Set ℕ | ∃ (x8 : Fin x2 → Bool), ∀ x9 ∈ x3 x8 x6, x9 ∈ x7};       ∀ (x7 : Fin x2), ∃ x8 < x1 + ↑x7, ∃ x9 < x1 + ↑x7, x6 (x1 + ↑x7) = x6 x8 ∩ x6 x9 ∨ x6 (x1 + ↑x7) = x6 x8 ∪ x6 x9 ∨ x6 (x1 + ↑x7) = Set.univ := by
  intro x1 x2 x3 hbase hstep
  dsimp only
  intro x7
  let a : Fin x2 → ℕ := fun i => (hstep i).choose
  have ha : ∀ i : Fin x2, a i < x1 + i.val := fun i => (hstep i).choose_spec.1
  let b : Fin x2 → ℕ := fun i => (hstep i).choose_spec.2.choose
  have hb : ∀ i : Fin x2, b i < x1 + i.val := fun i => (hstep i).choose_spec.2.choose_spec.1
  have hgate : ∀ i : Fin x2,
      (∀ x8, x3 x8 (x1 + i.val) = x3 x8 (a i) ∪ x3 x8 (b i)) ∨
      (∀ x8, x3 x8 (x1 + i.val) = if x8 i = Bool.true then x3 x8 (a i) else x3 x8 (b i)) ∨
      (∀ x8, x3 x8 (x1 + i.val) = ∅) :=
    fun i => (hstep i).choose_spec.2.choose_spec.2
  refine ⟨a x7, ha x7, b x7, hb x7, ?_⟩
  rcases hgate x7 with hu | hc | he
  · left
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨x8, hx8⟩
      rw [hu x8] at hx8
      exact ⟨⟨x8, fun y hy => hx8 y (Finset.mem_union_left _ hy)⟩,
        ⟨x8, fun y hy => hx8 y (Finset.mem_union_right _ hy)⟩⟩
    · rintro ⟨hA, hB⟩
      refine ⟨PEqualNP.Outside.L_meta_6015.canon x2 x3 a S, ?_⟩
      rw [hu (PEqualNP.Outside.L_meta_6015.canon x2 x3 a S)]
      have haS := PEqualNP.Outside.L_meta_6015.canon_sub x1 x2 x3 a b S hbase ha hb hgate
        (a x7) (by have := ha x7; have := x7.isLt; omega) hA
      have hbS := PEqualNP.Outside.L_meta_6015.canon_sub x1 x2 x3 a b S hbase ha hb hgate
        (b x7) (by have := hb x7; have := x7.isLt; omega) hB
      intro y hy
      rcases Finset.mem_union.mp hy with hya | hyb
      · exact haS y hya
      · exact hbS y hyb
  · right
    left
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨x8, hx8⟩
      rw [hc x8] at hx8
      by_cases h : x8 x7 = Bool.true
      · simp only [h, ite_true] at hx8
        exact Or.inl ⟨x8, hx8⟩
      · simp only [h] at hx8
        exact Or.inr ⟨x8, hx8⟩
    · rintro (⟨x8, hx8⟩ | ⟨x8, hx8⟩)
      · let x8' : Fin x2 → Bool := fun j => if j = x7 then Bool.true else x8 j
        have hagree : ∀ j : Fin x2, j.val < x7.val → x8' j = x8 j := by
          intro j hj
          have hne : j ≠ x7 := by
            intro heq
            subst heq
            omega
          simp only [x8', hne, ite_false]
        have heq := PEqualNP.Outside.L_meta_6015.agree_eq x1 x2 x3 a b hbase ha hb hgate
          x7.val (by omega) x8' x8 hagree (a x7) (ha x7)
        refine ⟨x8', ?_⟩
        rw [hc x8']
        have htrue : x8' x7 = Bool.true := by
          simp only [x8', ite_true]
        simp only [htrue, ite_true]
        rw [heq]
        exact hx8
      · let x8' : Fin x2 → Bool := fun j => if j = x7 then Bool.false else x8 j
        have hagree : ∀ j : Fin x2, j.val < x7.val → x8' j = x8 j := by
          intro j hj
          have hne : j ≠ x7 := by
            intro heq
            subst heq
            omega
          simp only [x8', hne, ite_false]
        have heq := PEqualNP.Outside.L_meta_6015.agree_eq x1 x2 x3 a b hbase ha hb hgate
          x7.val (by omega) x8' x8 hagree (b x7) (hb x7)
        refine ⟨x8', ?_⟩
        rw [hc x8']
        have hfalse : x8' x7 = Bool.false := by
          simp only [x8', ite_true]
        simp only [hfalse, Bool.false_eq_true, ite_false]
        rw [heq]
        exact hx8
  · right
    right
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    refine ⟨fun _ => Bool.false, ?_⟩
    rw [he]
    intro y hy
    exact absurd hy (Finset.notMem_empty y)
