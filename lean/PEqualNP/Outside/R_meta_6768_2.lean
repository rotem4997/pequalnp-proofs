import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo

-- A gate that reads a low wire w is invisible in that wire once w is false: an AND gate
-- then returns w itself and an OR gate returns its other operand, which ReadsBack keeps
-- below the output wire.
-- Reader contiguity plus two readers whose second one is not the last gate yields three
-- ordered readers of the same wire.
-- The structural core of the step locates two ordered readers of one of the four low wires.
theorem PEqualNP.Outside.R_meta_6768_2
    (hInvis : ∀ (n : ℕ) (C : Circuit) (w : Fin n) (j : ℕ),
      AndOrOnly C → ReadsBack n C → (∀ g ∈ C.gates, g.inputs.length = 2) →
      j < C.size → (w : ℕ) ∈ (gateAt C j).inputs →
      ∃ w' < n + j, ∀ (x : Fin n → Bool), x w = false →
        wval C x (n + j) = wval C x w')
    (hRun : ∀ (n : ℕ) (C : Circuit) (w : Fin n),
      ((∀ j < C.size, (w : ℕ) ∈ (gateAt C j).inputs → (gateAt C j).op = GateOp.or) ∧
        ∀ (i j k : ℕ), i < j → j < k → k < C.size →
          (w : ℕ) ∈ (gateAt C i).inputs → (w : ℕ) ∈ (gateAt C j).inputs →
          (w : ℕ) ∉ (gateAt C k).inputs) →
      ∀ (a b : ℕ), a < b → b + 1 < C.size → (w : ℕ) ∈ (gateAt C a).inputs →
        (w : ℕ) ∈ (gateAt C b).inputs →
      ∃ (i j k : ℕ), i < j ∧ j < k ∧ k < C.size ∧
        (w : ℕ) ∈ (gateAt C i).inputs ∧ (w : ℕ) ∈ (gateAt C j).inputs ∧
        (w : ℕ) ∈ (gateAt C k).inputs)
    (hCore : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : Circuit),
      G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
      IsLeastAO G D → TopForm G D → 2 ≤ (junk G D).card → D.size ≤ 21 →
      2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
        < 2 * (Ustar G D).card →
      ∃ (x9 : Fin 11), (x9 : ℕ) < 4 ∧ ∃ (a b : ℕ), a < b ∧ b + 1 < D.size ∧
        (x9 : ℕ) ∈ (gateAt D a).inputs ∧ (x9 : ℕ) ∈ (gateAt D b).inputs)
    : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             (∀ (x8 : Fin (11 : ℕ)), ↑x8 < (4 : ℕ) → (∀ x10 < x2.size, ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x10 x11 x12 : ℕ), x10 < x11 → x11 < x12 → x12 < x2.size → ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs → ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).inputs → ↑x8 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x12).inputs) →               ∃ (x9 : Fin (11 : ℕ)),                 ↑x9 < (4 : ℕ) ∧                   have x10 : ℕ → Prop := fun (x10 : ℕ) => ∃ x11 < (11 : ℕ) + x10, ∀ (x12 : Fin (11 : ℕ) → Bool), x12 x9 = Bool.false → PEqualNP.ReadTwo.wval x2 x12 ((11 : ℕ) + x10) = PEqualNP.ReadTwo.wval x2 x12 x11;                   ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x13 < x2.size ∧ x10 x11 ∧ x10 x12 ∧ x10 x13 := by
  intro x1 x2 hLeast hTop hJunk hSize hCount hCont
  dsimp only
  obtain ⟨x9, hx9, a, b, hab, hb1, ha, hb⟩ :=
    hCore (edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) x2 rfl hLeast hTop hJunk hSize hCount
  have hAO : AndOrOnly x2 := hLeast.1.1
  have hRB : ReadsBack 11 x2 := hLeast.1.2.1
  have hLen : ∀ g ∈ x2.gates, g.inputs.length = 2 := hLeast.1.2.2
  have hC' : (∀ j < x2.size, (x9 : ℕ) ∈ (gateAt x2 j).inputs → (gateAt x2 j).op = GateOp.or) ∧
      ∀ (i j k : ℕ), i < j → j < k → k < x2.size →
        (x9 : ℕ) ∈ (gateAt x2 i).inputs → (x9 : ℕ) ∈ (gateAt x2 j).inputs →
        (x9 : ℕ) ∉ (gateAt x2 k).inputs := hCont x9 hx9
  obtain ⟨i, j, k, hij, hjk, hk, hi, hj, hk' ⟩ := hRun 11 x2 x9 hC' a b hab hb1 ha hb
  have key : ∀ (g : ℕ), g < x2.size → (x9 : ℕ) ∈ (gateAt x2 g).inputs →
      ∃ w' < 11 + g, ∀ (x : Fin 11 → Bool), x x9 = false →
        wval x2 x (11 + g) = wval x2 x w' :=
    fun g hg hin => hInvis 11 x2 x9 g hAO hRB hLen hg hin
  obtain ⟨w1, hw1, hv1⟩ := key i (by omega) hi
  obtain ⟨w2, hw2, hv2⟩ := key j (by omega) hj
  obtain ⟨w3, hw3, hv3⟩ := key k (by omega) hk'
  exact ⟨x9, hx9, i, j, k, hij, hjk, hk,
    ⟨w1, hw1, hv1⟩, ⟨w2, hw2, hv2⟩, ⟨w3, hw3, hv3⟩⟩
