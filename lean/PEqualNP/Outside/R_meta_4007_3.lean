import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4007_3
    (two : (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → x3.size < (22 : ℕ) → (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) → (PEqualNP.TopForm.Ustar x1 x3).card = (2 : ℕ) → (2 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card))
    (three : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → x3.size < (22 : ℕ) → (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) → (PEqualNP.TopForm.Ustar x1 x3).card = (3 : ℕ) → (4 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card)
    (mix : (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       have x5 : Finset ℕ := PEqualNP.TopForm.centreless x1 x2;       have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;       have x7 : Finset ℕ := PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2;       have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;       have x9 : ℕ := (2 : ℕ) * x5.card + x6.card + x7.card;       (2 : ℕ) ≤ x6.card → (3 : ℕ) ≤ x8.card → x7.card = (0 : ℕ) ∨ x7.card = (1 : ℕ) ∧ x5.card = (0 : ℕ) → (2 : ℕ) * x8.card ≤ x9))
    (many : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 → x3.size < (22 : ℕ) → have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3; have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3; have x13 : ℕ := (2 : ℕ) * x12.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card; (4 : ℕ) ≤ x11.card → ((2 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ∨ (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card = (1 : ℕ) ∧ (0 : ℕ) < x12.card) → (3 : ℕ) + x13 ≤ (2 : ℕ) * x11.card → (PEqualNP.TopForm.tops x1 x3 \ x12).card + x13 ≤ (4 : ℕ) + x11.card → (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ PEqualNP.TopForm.junk x1 x3, ∀ (x20 : Fin (2 : ℕ)), x16 ∈ PEqualNP.TopForm.side x3 x19 x20 ∨ x17 ∈ PEqualNP.TopForm.side x3 x19 x20) → False) :
    (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : ℕ := (2 : ℕ) * x12.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;             (3 : ℕ) + x13 ≤ (2 : ℕ) * x11.card → (PEqualNP.TopForm.tops x1 x3 \ x12).card + x13 ≤ (4 : ℕ) + x11.card → (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ PEqualNP.TopForm.junk x1 x3, ∀ (x20 : Fin (2 : ℕ)), x16 ∈ PEqualNP.TopForm.side x3 x19 x20 ∨ x17 ∈ PEqualNP.TopForm.side x3 x19 x20) → (22 : ℕ) ≤ x3.size) := by
  intro G inst C i j hG least top junkPair cone
  dsimp only
  intro budgetA budgetB sides
  by_contra! small
  have strict : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (cs : List (List ℕ)),
      (∀ k x, x ∈ cs.getD k [] → x < k) →
      ∀ k x, x ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep 11) cs).getD k [] → x < k := by
    intro gs
    induction gs with
    | nil => intro cs h; simpa using h
    | cons g gs ih =>
      intro cs h
      apply ih
      intro k x hx
      unfold PEqualNP.EdgeOwnership.coneStep at hx
      rw [List.getD_eq_getElem?_getD, List.getElem?_append] at hx
      split_ifs at hx with hk
      · rw [← List.getD_eq_getElem?_getD] at hx
        exact h k x hx
      · rcases Nat.lt_or_ge k (cs.length + 1) with hk' | hk'
        · have hkeq : k = cs.length := by omega
          subst hkeq
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.mem_flatMap,
            List.mem_filter, decide_eq_true_eq, List.mem_cons] at hx
          obtain ⟨w, ⟨_, hw1, hw2⟩, hmem⟩ := hx
          rcases hmem with rfl | hmem
          · omega
          · have := h (w - 11) x hmem
            omega
        · have hnone : ([((g.inputs.filter fun w => decide (11 ≤ w ∧ w < 11 + cs.length)).flatMap
              fun w => (w - 11) :: cs.getD (w - 11) [])] : List (List ℕ))[k - cs.length]? = none :=
            List.getElem?_eq_none (by simp; omega)
          rw [hnone] at hx
          simp at hx
  have lt : i < j := strict C.gates [] (by simp) j i cone
  have ne : i ≠ j := Nat.ne_of_lt lt
  have jcard : (PEqualNP.TopForm.junk G C).card = 2 := by
    rw [junkPair, Finset.card_pair ne]
  rcases Nat.lt_or_ge (PEqualNP.TopForm.Ustar G C).card 4 with low | high
  · have cases : (PEqualNP.TopForm.Ustar G C).card ≤ 1 ∨ (PEqualNP.TopForm.Ustar G C).card = 2 ∨
        (PEqualNP.TopForm.Ustar G C).card = 3 := by omega
    rcases cases with hu | hu | hu
    · omega
    · have := two G C hG least top small ⟨i, j, junkPair, cone⟩ hu
      omega
    · have := three G C hG least top small ⟨i, j, junkPair, cone⟩ hu
      omega
  · by_cases easy : (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card = 0 ∨ (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card = 1 ∧ (PEqualNP.TopForm.centreless G C).card = 0
    · subst hG
      have same : inst = PEqualNP.EdgeOwnership.instDecidableRelFinAdjEdgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] :=
        Subsingleton.elim _ _
      subst same
      have := mix C least top (by omega) (by omega) easy
      omega
    · apply many G C i j hG least top junkPair cone small high
      · omega
      · exact budgetA
      · exact budgetB
      · exact sides
