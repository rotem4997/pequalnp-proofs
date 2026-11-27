import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2264_428
  (coverAndSmall : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (p q : ℕ),
    let U := Ustar G C
    let Z := centreless G C
    let T := (tops G C \ Z).card
    let R := (orN G C \ lam G C).card
    G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
    IsAO2 11 C →
    TopForm G C → junk G C = {p,q} → ¬ InCone 11 C p q → ¬ InCone 11 C q p →
    (∀ a ∈ tops G C, InCone 11 C p a → ¬ InCone 11 C q a) →
    (∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ tops G C, ∃ (b : Fin 2) (j : ℕ),
      (j=p ∨ j=q) ∧ gateVal 11 C a (pairInput u v) = true ∧
      OrReaches 11 C (opnd C a b) j ∧ gateVal 11 C j (pairInput u v) = true) →
    (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges (U : Set _)) K → K.card ≤ T) →
    ((17 + T + 2 * Z.card + R ≤ C.size + U.card → U.card ≤ 2 → 22 ≤ C.size) ∧
      (3 ≤ U.card → 8 ≤ T + U.card)))
  (large : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (p q : ℕ),
    let U := Ustar G C
    let Z := centreless G C
    let T := (tops G C \ Z).card
    let R := (orN G C \ lam G C).card
    G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
    IsLeastAO G C → p < q →
    TopForm G C → junk G C = {p,q} → ¬ InCone 11 C p q → ¬ InCone 11 C q p →
    (∀ a ∈ tops G C, InCone 11 C p a → ¬ InCone 11 C q a) →
    (∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ tops G C, ∃ (b : Fin 2) (j : ℕ),
      (j=p ∨ j=q) ∧ gateVal 11 C a (pairInput u v) = true ∧
      OrReaches 11 C (opnd C a b) j ∧ gateVal 11 C j (pairInput u v) = true) →
    (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges (U : Set _)) K → K.card ≤ T) →
    17 + T + 2 * Z.card + R ≤ C.size + U.card → 3 ≤ U.card → 8 ≤ T + U.card → 22 ≤ C.size) : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∀ x21 ∈ x9, x12 x4 x21 → ¬x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  intro G inst C p q graph least top T Z U cone stars trace count cover hpq junk noPQ noQP apart
  have profile := coverAndSmall G C p q graph least.1 top junk noPQ noQP apart trace cover
  by_cases h : (Ustar G C).card ≤ 2
  · exact profile.1 count h
  · have many : 3 ≤ (Ustar G C).card := by omega
    exact large G C p q graph least hpq top junk noPQ noQP apart trace cover count many (profile.2 many)
