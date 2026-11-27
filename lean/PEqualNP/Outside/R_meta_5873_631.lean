import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.R_meta_5873_631
  (lowExceptions : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ C : Circuit, IsLeastAO G C → TopForm G C →
    let Z := centreless G C
    let J := junk G C
    let R := orN G C \ lam G C
    let U := Ustar G C
    let B := 2 * Z.card + J.card + R.card
    2 ≤ J.card → 3 ≤ U.card → (R.card = 0 ∨ (R.card = 1 ∧ Z.card = 0)) →
      2 * U.card ≤ B)
  (remaining : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ C : Circuit, IsLeastAO G C → TopForm G C →
    let Z := centreless G C
    let J := junk G C
    let R := orN G C \ lam G C
    let U := Ustar G C
    let B := 2 * Z.card + J.card + R.card
    2 ≤ J.card → 4 ≤ B → U.card ≤ B → B < 2 * U.card →
    0 < R.card → (0 < Z.card ∨ 2 ≤ R.card) → 22 ≤ C.size) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           (4 : ℕ) ≤ x7 → x8.card ≤ x7 → x7 < (2 : ℕ) * x8.card → ∃ (x12 : Finset (Fin (11 : ℕ))) (x13 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x12 ∧ x1.IsVertexCover ↑(x12 ∪ x13) ∧ x13.card ≤ x7 - x8.card) := by
  dsimp only at lowExceptions remaining ⊢
  intro C short least top dirty large lo hi
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let U := Ustar G C
  let R := orN G C \ lam G C
  let Z := centreless G C
  let B := 2 * Z.card + (junk G C).card + R.card
  change 4 ≤ B at large
  change U.card ≤ B at lo
  change B < 2 * U.card at hi
  by_cases easy : R.card = 0 ∨ (R.card = 1 ∧ Z.card = 0)
  · have many : 3 ≤ U.card := by omega
    have enough : 2 * U.card ≤ B := lowExceptions C least top dirty many easy
    omega
  · have someR : 0 < R.card := by omega
    have larger : 0 < Z.card ∨ 2 ≤ R.card := by
      by_cases h : 0 < Z.card
      · exact Or.inl h
      · exact Or.inr (by omega)
    have enough := remaining C least top dirty large lo hi someR larger
    omega
