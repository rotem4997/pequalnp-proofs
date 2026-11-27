import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8097

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


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8097

theorem PEqualNP.Outside.L_meta_8097 : ∀ (x1 : ℕ) (x2 : PEqualNP.AndCount.AndCountCircuit x1) (x3 : SimpleGraph (Fin x1)), x2.Computes x3 → x2.outVars = ∅ → ∀ (x6 : Finset (Fin x1)), (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → x7 ∈ x6 ∨ x8 ∈ x6) → (∀ x8 ⊆ x6, (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → x10 ∈ x8 ∨ x11 ∈ x8) → x6 ⊆ x8) → ∃ (x9 : Finset (Fin x2.size)) (x10 : Finset (Fin x2.size)), Disjoint x9 x10 ∧ x9.biUnion x2.leftVars ∪ x10.biUnion x2.rightVars = x6 := by
  intro n C G hC hout X hcov hmin
  classical
  let I : Finset (Fin n) := Finset.univ \ X
  have hI : C.eval I = false := by
    cases h : C.eval I
    · rfl
    · obtain ⟨a, ha, b, hb, hab⟩ := (hC I).1 h
      simp only [I, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha hb
      rcases hcov a b hab with h' | h'
      · exact absurd h' ha
      · exact absurd h' hb
  let sl : Fin C.size → Bool := fun g => PEqualNP.AndCount.AndCountCircuit.sideTrue I (C.leftVars g) (C.leftGates g) g (C.gateVal I)
  let sr : Fin C.size → Bool := fun g => PEqualNP.AndCount.AndCountCircuit.sideTrue I (C.rightVars g) (C.rightGates g) g (C.gateVal I)
  let A : Finset (Fin C.size) := Finset.univ.filter fun g => sl g = false
  let B : Finset (Fin C.size) := Finset.univ.filter fun g => sl g = true ∧ sr g = false
  have hnot : ∀ (V : Finset (Fin n)) (F : Finset (Fin C.size)) (g : Fin C.size), PEqualNP.AndCount.AndCountCircuit.sideTrue I V F g (C.gateVal I) = false → ∀ x ∈ V, x ∈ X := by
    intro V F g h x hx
    simp only [PEqualNP.AndCount.AndCountCircuit.sideTrue, decide_eq_false_iff_not] at h
    by_contra hxX
    exact h (Or.inl ⟨x, hx, by simp [I, hxX]⟩)
  refine ⟨A, B, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro g h1 h2
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1] at h2; cases h2.1
  · apply Finset.Subset.antisymm
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_biUnion, A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨g, hg, hx⟩ | ⟨g, hg, hx⟩
      · exact hnot _ _ g hg x hx
      · exact hnot _ _ g hg.2 x hx
    · intro x hxX
      by_contra hx
      simp only [Finset.mem_union, Finset.mem_biUnion, A, B, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_exists, not_and] at hx
      obtain ⟨hx1, hx2⟩ := hx
      -- an edge from x to the independent set
      have hedge : ∃ b, b ∉ X ∧ G.Adj x b := by
        by_contra hcon
        push_neg at hcon
        have := hmin (X.erase x) (Finset.erase_subset _ _) (by
          intro a b hab
          rcases hcov a b hab with ha | hb
          · by_cases hax : a = x
            · subst hax
              right
              rw [Finset.mem_erase]
              refine ⟨fun e => G.loopless.irrefl a (by rw [e] at hab; exact hab), ?_⟩
              by_contra hb
              exact hcon b hb hab
            · exact Or.inl (Finset.mem_erase.2 ⟨hax, ha⟩)
          · by_cases hbx : b = x
            · subst hbx
              left
              rw [Finset.mem_erase]
              refine ⟨fun e => G.loopless.irrefl b (by rw [e] at hab; exact hab), ?_⟩
              by_contra ha
              exact hcon a ha hab.symm
            · exact Or.inr (Finset.mem_erase.2 ⟨hbx, hb⟩)) hxX
        simp at this
      obtain ⟨b, hb, hxb⟩ := hedge
      let J : Finset (Fin n) := insert x I
      have hJ : C.eval J = true := (hC J).2 ⟨x, by simp [J], b, by simp [J, I, hb], hxb⟩
      have hval : ∀ k, ∀ g : Fin C.size, (g : ℕ) < k → C.gateVal I g = false → C.gateVal J g = false := by
        intro k
        induction k with
        | zero => intro g hg; omega
        | succ k ih =>
          intro g hg h
          have hs : ∀ (V : Finset (Fin n)) (F : Finset (Fin C.size)), x ∉ V → PEqualNP.AndCount.AndCountCircuit.sideTrue I V F g (C.gateVal I) = false → PEqualNP.AndCount.AndCountCircuit.sideTrue J V F g (C.gateVal J) = false := by
            intro V F hxV h
            simp only [PEqualNP.AndCount.AndCountCircuit.sideTrue, decide_eq_false_iff_not] at h ⊢
            rintro (⟨w, hw, hwJ⟩ | ⟨j, hj, hjg, hjt⟩)
            · rcases Finset.mem_insert.1 hwJ with rfl | hwI
              · exact hxV hw
              · exact h (Or.inl ⟨w, hw, hwI⟩)
            · refine h (Or.inr ⟨j, hj, hjg, ?_⟩)
              by_contra hjI
              have hj' : (j : ℕ) < (g : ℕ) := hjg
              rw [ih j (by omega) (by simpa using hjI)] at hjt
              cases hjt
          rw [PEqualNP.Outside.L_meta_8097.gv, Bool.and_eq_false_iff] at h ⊢
          cases hl : sl g
          · exact Or.inl (hs _ _ (hx1 g hl) hl)
          · rcases h with h | h
            · rw [show PEqualNP.AndCount.AndCountCircuit.sideTrue I (C.leftVars g) (C.leftGates g) g (C.gateVal I) = sl g from rfl, hl] at h; cases h
            · exact Or.inr (hs _ _ (hx2 g ⟨hl, h⟩) h)
      simp only [PEqualNP.AndCount.AndCountCircuit.eval, hout, decide_eq_true_eq, decide_eq_false_iff_not] at hJ hI
      rcases hJ with ⟨w, hw, _⟩ | ⟨j, hj, hjt⟩
      · simp at hw
      · have : C.gateVal I j = false := by
          by_contra h
          exact hI (Or.inr ⟨j, hj, by simpa using h⟩)
        rw [hval C.size j j.isLt this] at hjt
        cases hjt
