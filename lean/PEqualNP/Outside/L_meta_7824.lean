import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7824

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem fuelS {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) : ∀ (k : ℕ) (i : Fin C.size), (i : ℕ) < k → ∀ d e : ℕ, (i : ℕ) < d → (i : ℕ) < e → gateValFuel C U d i = gateValFuel C U e i := by
  intro k
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi d e hd he
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    have hs : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)), sideTrue U B F i (gateValFuel C U d) = sideTrue U B F i (gateValFuel C U e) := by
      intro B F
      unfold sideTrue
      congr 1
      apply propext
      refine or_congr_right (exists_congr fun j => and_congr_right fun _ => and_congr_right fun hj => ?_)
      have hj' : (j : ℕ) < (i : ℕ) := hj
      rw [ih j (by omega) d e (by omega) (by omega)]
    simp only [Nat.succ_eq_add_one, gateValFuel]
    rw [hs, hs]

theorem gv {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) && sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h : C.gateVal U i = gateValFuel C U (C.size + 1) i := fuelS C U (i + 1) i (by omega) _ _ i.isLt (by have := i.isLt; omega)
  rw [h]
  rfl

theorem side {n N : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] (S : ι → Finset (Fin n)) (A : κ → Finset (Fin n)) (V : Finset (Fin n) → Fin N → Bool)
    (hcase : ∀ g, (∀ a, V (A a) g = true) ∨ (∀ a, V (A a) g = false)) (hcov : ∀ i j, i ≠ j → ∃ a, A a ⊆ S i ∪ S j) (m : ℕ)
    (B : Finset (Fin n)) (F : Finset (Fin N)) (h : ∀ a, (∃ v ∈ B, v ∈ A a) ∨ ∃ j ∈ F, (j : ℕ) < m ∧ V (A a) j = true) :
    ∃ (Z : Finset (Fin N)) (L : Finset ι), (∀ g ∈ Z, (g : ℕ) < m ∧ ∀ a, V (A a) g = true) ∧ L.card + Z.card ≤ 1 ∧
      ∀ i, ¬((∃ v ∈ B, v ∈ S i) ∨ ∃ j ∈ F, (j : ℕ) < m ∧ V (S i) j = true) → i ∈ L ∨ ∃ g ∈ Z, V (S i) g = false := by
  classical
  by_cases hg : ∃ j ∈ F, (j : ℕ) < m ∧ ∀ a, V (A a) j = true
  · obtain ⟨j, hj, hjm, hja⟩ := hg
    refine ⟨{j}, ∅, ?_, by simp, ?_⟩
    · intro g hg
      rw [Finset.mem_singleton] at hg
      subst hg
      exact ⟨hjm, hja⟩
    · intro i hi
      right
      refine ⟨j, by simp, ?_⟩
      by_contra hv
      exact hi (Or.inr ⟨j, hj, hjm, by simpa using hv⟩)
  · have hv : ∀ a, ∃ v ∈ B, v ∈ A a := by
      intro a
      rcases h a with h | ⟨j, hj, hjm, hja⟩
      · exact h
      · exfalso
        rcases hcase j with h' | h'
        · exact hg ⟨j, hj, hjm, h'⟩
        · rw [h' a] at hja; cases hja
    refine ⟨∅, Finset.univ.filter fun i => ¬∃ v ∈ B, v ∈ S i, by simp, ?_, ?_⟩
    · rw [Finset.card_empty, Nat.add_zero, Finset.card_le_one]
      intro i hi j hj
      rw [Finset.mem_filter] at hi hj
      by_contra hij
      obtain ⟨a, ha⟩ := hcov i j hij
      obtain ⟨v, hvB, hvA⟩ := hv a
      rcases Finset.mem_union.1 (ha hvA) with h1 | h1
      · exact hi.2 ⟨v, hvB, h1⟩
      · exact hj.2 ⟨v, hvB, h1⟩
    · intro i hi
      left
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun h => hi (Or.inl h)⟩

theorem gen {n : ℕ} (C : AndCountCircuit n) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Nonempty κ] (S : ι → Finset (Fin n)) (A : κ → Finset (Fin n))
    (hcase : ∀ g, (∀ a, C.gateVal (A a) g = true) ∨ (∀ a, C.gateVal (A a) g = false)) (hcov : ∀ i j, i ≠ j → ∃ a, A a ⊆ S i ∪ S j)
    (hrej : ∀ i, C.eval (S i) = false) (hacc : ∀ a, C.eval (A a) = true) (T : Finset (Fin C.size)) (hT : ∀ g, (∀ a, C.gateVal (A a) g = true) → g ∈ T) :
    Fintype.card ι ≤ T.card + 1 := by
  classical
  have key : ∀ d m, m + d = C.size → ∃ (Z : Finset (Fin C.size)) (L : Finset ι), (∀ g ∈ Z, (g : ℕ) < m ∧ ∀ a, C.gateVal (A a) g = true) ∧
      (∀ i, i ∈ L ∨ ∃ g ∈ Z, C.gateVal (S i) g = false) ∧ L.card + Z.card + (T.filter fun g : Fin C.size => (g : ℕ) < m).card ≤ 1 + T.card := by
    intro d
    induction d with
    | zero =>
      intro m hm
      obtain ⟨Z, L, h1, h2, h3⟩ := side S A C.gateVal hcase hcov m C.outVars C.outGates (by
        intro a
        have := hacc a
        simp only [AndCountCircuit.eval, decide_eq_true_eq] at this
        rcases this with h | ⟨j, hj, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, hj, by have := j.isLt; omega, h⟩)
      refine ⟨Z, L, h1, fun i => h3 i ?_, ?_⟩
      · have := hrej i
        simp only [AndCountCircuit.eval, decide_eq_false_iff_not] at this
        rintro (h | ⟨j, hj, _, h⟩)
        · exact this (Or.inl h)
        · exact this (Or.inr ⟨j, hj, h⟩)
      · have := Finset.card_filter_le T (fun g : Fin C.size => (g : ℕ) < m)
        omega
    | succ d ih =>
      intro m hm
      obtain ⟨Z, L, h1, h2, h3⟩ := ih (m + 1) (by omega)
      let g : Fin C.size := ⟨m, by omega⟩
      by_cases hgZ : g ∈ Z
      · have hgt := (h1 g hgZ).2
        have hsides : ∀ a, (sideTrue (A a) (C.leftVars g) (C.leftGates g) g (C.gateVal (A a)) = true) ∧ (sideTrue (A a) (C.rightVars g) (C.rightGates g) g (C.gateVal (A a)) = true) := by
          intro a
          have := hgt a
          rw [gv, Bool.and_eq_true] at this
          exact this
        obtain ⟨Z1, L1, a1, a2, a3⟩ := side S A C.gateVal hcase hcov m (C.leftVars g) (C.leftGates g) (by
          intro a
          have := (hsides a).1
          simp only [sideTrue, decide_eq_true_eq] at this
          exact this)
        obtain ⟨Z2, L2, b1, b2, b3⟩ := side S A C.gateVal hcase hcov m (C.rightVars g) (C.rightGates g) (by
          intro a
          have := (hsides a).2
          simp only [sideTrue, decide_eq_true_eq] at this
          exact this)
        refine ⟨Z.erase g ∪ (Z1 ∪ Z2), L ∪ (L1 ∪ L2), ?_, ?_, ?_⟩
        · intro k hk
          rw [Finset.mem_union, Finset.mem_union, Finset.mem_erase] at hk
          rcases hk with ⟨hk1, hk2⟩ | hk | hk
          · have := h1 k hk2
            refine ⟨?_, this.2⟩
            have hne : (k : ℕ) ≠ m := fun e => hk1 (Fin.ext e)
            omega
          · exact a1 k hk
          · exact b1 k hk
        · intro i
          rcases h2 i with h | ⟨k, hk, hkv⟩
          · exact Or.inl (Finset.mem_union_left _ h)
          · by_cases hkg : k = g
            · subst hkg
              rw [gv, Bool.and_eq_false_iff] at hkv
              rcases hkv with h | h
              · rcases a3 i (by simp only [sideTrue, decide_eq_false_iff_not] at h; exact h) with h | ⟨z, hz, h⟩
                · exact Or.inl (Finset.mem_union_right _ (Finset.mem_union_left _ h))
                · exact Or.inr ⟨z, Finset.mem_union_right _ (Finset.mem_union_left _ hz), h⟩
              · rcases b3 i (by simp only [sideTrue, decide_eq_false_iff_not] at h; exact h) with h | ⟨z, hz, h⟩
                · exact Or.inl (Finset.mem_union_right _ (Finset.mem_union_right _ h))
                · exact Or.inr ⟨z, Finset.mem_union_right _ (Finset.mem_union_right _ hz), h⟩
            · exact Or.inr ⟨k, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hkg, hk⟩), hkv⟩
        · have c1 := Finset.card_union_le (Z.erase g) (Z1 ∪ Z2)
          have c2 := Finset.card_union_le Z1 Z2
          have c3 := Finset.card_union_le L (L1 ∪ L2)
          have c4 := Finset.card_union_le L1 L2
          have c5 := Finset.card_erase_of_mem hgZ
          have c6 : 0 < Z.card := Finset.card_pos.2 ⟨g, hgZ⟩
          have c7 : (T.filter fun k : Fin C.size => (k : ℕ) < m).card < (T.filter fun k : Fin C.size => (k : ℕ) < m + 1).card := by
            refine Finset.card_lt_card ⟨fun k hk => ?_, fun hsub => ?_⟩
            · rw [Finset.mem_filter] at hk ⊢
              exact ⟨hk.1, by omega⟩
            · have := hsub (Finset.mem_filter.2 ⟨hT g hgt, (by simp [g] : (g : ℕ) < m + 1)⟩)
              rw [Finset.mem_filter] at this
              have h' : (g : ℕ) = m := rfl
              omega
          omega
      · refine ⟨Z, L, ?_, h2, ?_⟩
        · intro k hk
          have := h1 k hk
          refine ⟨?_, this.2⟩
          have hne : (k : ℕ) ≠ m := by
            intro e
            apply hgZ
            have : k = g := Fin.ext e
            rw [← this]; exact hk
          omega
        · have : (T.filter fun k : Fin C.size => (k : ℕ) < m).card ≤ (T.filter fun k : Fin C.size => (k : ℕ) < m + 1).card := by
            refine Finset.card_le_card fun k hk => ?_
            rw [Finset.mem_filter] at hk ⊢
            exact ⟨hk.1, by omega⟩
          omega
  obtain ⟨Z, L, h1, h2, h3⟩ := key C.size 0 (by omega)
  have hL : L = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true]
    rcases h2 i with h | ⟨g, hg, _⟩
    · exact h
    · have := (h1 g hg).1; omega
  rw [hL, Finset.card_univ] at h3
  omega

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7824

theorem PEqualNP.Outside.L_meta_7824 : ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)) (x2 : Fin (52 : ℕ) → Finset (Fin (27 : ℕ))) (x3 : Fin (4 : ℕ) → Finset (Fin (27 : ℕ))), (∀ (x4 : Fin (52 : ℕ)), x1.eval (x2 x4) = Bool.false) → (∀ (x5 : Fin (4 : ℕ)), x1.eval (x3 x5) = Bool.true) → (∀ (x6 x7 : Fin (52 : ℕ)), x6 ≠ x7 → ∃ (x9 : Fin (4 : ℕ)), x3 x9 ⊆ x2 x6 ∪ x2 x7) → (∀ (x7 : Fin x1.size) (x8 : Fin (4 : ℕ)), x1.gateVal (x3 x8) x7 = Bool.true) → (52 : ℕ) ≤ x1.size + (1 : ℕ) := by
  intro C S A hS hA hcov hall
  have := PEqualNP.Outside.L_meta_7824.gen C S A (fun g => Or.inl fun a => hall g a) hcov hS hA Finset.univ (fun g _ => Finset.mem_univ g)
  simpa using this
