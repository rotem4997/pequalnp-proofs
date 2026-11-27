import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SplitCount PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5330_482
    (trace : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → ∀ (u v : Fin n) (j : ℕ),
      j < C.gates.length → gateVal n C j (pairInput u v) = true →
      gateVal n C j (pairInput u u) = false → gateVal n C j (pairInput v v) = false →
      ∃ k < C.gates.length, InConeOrSelf n C k j ∧ (gateAt C k).op = GateOp.and ∧
        ∃ b : Fin 2, wireVal n C (opnd C k b) (pairInput u u) = true ∧
          wireVal n C (opnd C k (1 - b)) (pairInput v v) = true)
    (shared : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      let pairOnly := fun (j : ℕ) (u v : Fin n) =>
        gateVal n C j (pairInput u v) = true ∧
        gateVal n C j (pairInput u u) = false ∧ gateVal n C j (pairInput v v) = false
      let joins := fun (j : ℕ) (u v : Fin n) => (gateAt C j).op = GateOp.and ∧
        ∃ b : Fin 2, wireVal n C (opnd C j b) (pairInput u u) = true ∧
          wireVal n C (opnd C j (1 - b)) (pairInput v v) = true
      ∀ S : Finset (Sym2 (Fin n)),
        (∀ e ∈ S, e ∈ Ustar G C ∧ (∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C,
          g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
          pairOnly g u v ∧ pairOnly h u v ∧ ∃ j ∈ Finset.range C.gates.length, InConeOrSelf n C j g ∧ InConeOrSelf n C j h ∧ joins j u v)) →
        S.card ≤ c * (C.size + 1))
    (separate : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      let pairOnly := fun (j : ℕ) (u v : Fin n) =>
        gateVal n C j (pairInput u v) = true ∧
        gateVal n C j (pairInput u u) = false ∧ gateVal n C j (pairInput v v) = false
      let joins := fun (j : ℕ) (u v : Fin n) => (gateAt C j).op = GateOp.and ∧
        ∃ b : Fin 2, wireVal n C (opnd C j b) (pairInput u u) = true ∧
          wireVal n C (opnd C j (1 - b)) (pairInput v v) = true
      ∀ S : Finset (Sym2 (Fin n)),
        (∀ e ∈ S, e ∈ Ustar G C ∧ (∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C,
          g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
          pairOnly g u v ∧ pairOnly h u v ∧ ∃ j ∈ Finset.range C.gates.length, ∃ k ∈ Finset.range C.gates.length,
            j ≠ k ∧ InConeOrSelf n C j g ∧ InConeOrSelf n C k h ∧
            joins j u v ∧ joins k u v)) →
        S.card ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ x13 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.false}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨a, ha⟩ := shared
  obtain ⟨b, hb⟩ := separate
  refine ⟨a + b, ?_⟩
  intro n G dec C hG hL hT
  classical
  let pairOnly := fun (j : ℕ) (u v : Fin n) =>
    gateVal n C j (pairInput u v) = true ∧
    gateVal n C j (pairInput u u) = false ∧ gateVal n C j (pairInput v v) = false
  let joins := fun (j : ℕ) (u v : Fin n) => (gateAt C j).op = GateOp.and ∧
    ∃ b : Fin 2, wireVal n C (opnd C j b) (pairInput u u) = true ∧
      wireVal n C (opnd C j (1 - b)) (pairInput v v) = true
  let A := (Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C,
          g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
          pairOnly g u v ∧ pairOnly h u v ∧ ∃ j ∈ Finset.range C.gates.length, InConeOrSelf n C j g ∧ InConeOrSelf n C j h ∧ joins j u v)
  let B := (Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
        ∃ a ∈ tops G C, ∃ g ∈ junk G C, ∃ h ∈ junk G C,
          g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
          pairOnly g u v ∧ pairOnly h u v ∧ ∃ j ∈ Finset.range C.gates.length, ∃ k ∈ Finset.range C.gates.length,
            j ≠ k ∧ InConeOrSelf n C j g ∧ InConeOrSelf n C k h ∧
            joins j u v ∧ joins k u v)
  have hA : A.card ≤ a * (C.size + 1) := ha n G C hG hL hT A (fun _ he => Finset.mem_filter.mp he)
  have hB : B.card ≤ b * (C.size + 1) := hb n G C hG hL hT B (fun _ he => Finset.mem_filter.mp he)
  calc
    _ ≤ (A ∪ B).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨hU, u, v, heq, t, ht, g, hg, h, hh, hne, hLeft, hRight,
        hPg, hPh, hUg, hVg, hUh, hVh⟩ := Finset.mem_filter.mp he
      have hglt : g < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hg).1
      have hhlt : h < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
      obtain ⟨i, hi, hig, hiop, hiwire⟩ := trace n C hL.1 u v g hglt hPg hUg hVg
      obtain ⟨j, hj, hjh, hjop, hjwire⟩ := trace n C hL.1 u v h hhlt hPh hUh hVh
      apply Finset.mem_union.mpr
      by_cases hij : i = j
      · subst j
        exact Or.inl (Finset.mem_filter.mpr ⟨hU, u, v, heq, t, ht, g, hg, h, hh,
          hne, hLeft, hRight, ⟨hPg, hUg, hVg⟩, ⟨hPh, hUh, hVh⟩, i, Finset.mem_range.mpr hi, hig, hjh, hiop, hiwire⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hU, u, v, heq, t, ht, g, hg, h, hh,
          hne, hLeft, hRight, ⟨hPg, hUg, hVg⟩, ⟨hPh, hUh, hVh⟩, i, Finset.mem_range.mpr hi, j, Finset.mem_range.mpr hj, hij, hig, hjh,
          ⟨hiop, hiwire⟩, ⟨hjop, hjwire⟩⟩)
    _ ≤ A.card + B.card := Finset.card_union_le A B
    _ ≤ a * (C.size + 1) + b * (C.size + 1) := Nat.add_le_add hA hB
    _ = (a + b) * (C.size + 1) := (Nat.add_mul _ _ _).symm
