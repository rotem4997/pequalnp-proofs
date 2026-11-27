import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4133_487
    (budget :
      let es := ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map
        (fun k => (k / 11, k % 11))
      let G := edgeGraph 11 es
      let code := fun (U : Finset (Sym2 (Fin 11))) => BitVec.ofNat 16 (tableIndex fun i : Fin 16 =>
        let e := es.getD i.val (0,0)
        decide (s(Fin.ofNat 11 e.1, Fin.ofNat 11 e.2) ∈ U))
      let rare := ([36608,44800,44864,44992,48960,52992,53120,53184,57216,61184,
        61248,61312,61376,65280,65344,65408,65472] : List ℕ).map (BitVec.ofNat 16)
      let cost : BitVec 16 → ℕ := fun m => ite (m = 65472) 0
        (ite (m ∈ ([36608,44800,52992,61184] : List (BitVec 16))) 2 1)
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        code U ∈ rare → cost (code U) + B ≤ U.card + 3)
    (remaining :
      let es := ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map
        (fun k => (k / 11, k % 11))
      let G := edgeGraph 11 es
      let code := fun (U : Finset (Sym2 (Fin 11))) => BitVec.ofNat 16 (tableIndex fun i : Fin 16 =>
        let e := es.getD i.val (0,0)
        decide (s(Fin.ofNat 11 e.1, Fin.ofNat 11 e.2) ∈ U))
      let rare := ([36608,44800,44864,44992,48960,52992,53120,53184,57216,61184,
        61248,61312,61376,65280,65344,65408,65472] : List ℕ).map (BitVec.ofNat 16)
      let cost : BitVec 16 → ℕ := fun m => ite (m = 65472) 0
        (ite (m ∈ ([36608,44800,52992,61184] : List (BitVec 16))) 2 1)
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        U.card ≤ B → cost (code U) + B ≤ U.card + 3 → code U ∉ rare) :
  have x1 : List (ℕ × ℕ) := [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) x1; have x3 : Finset (Sym2 (Fin (11 : ℕ))) → BitVec (16 : ℕ) := fun (x3 : Finset (Sym2 (Fin (11 : ℕ)))) =>   BitVec.ofNat (16 : ℕ)     (PEqualNP.MetaComplexity.tableIndex fun (x4 : Fin (16 : ℕ)) =>       have x5 : ℕ × ℕ := x1.getD ↑x4 ((0 : ℕ), (0 : ℕ));       Decidable.decide (s(Fin.ofNat (11 : ℕ) x5.1, Fin.ofNat (11 : ℕ) x5.2) ∈ x3)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x4.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x2 x4 →       PEqualNP.TopForm.TopForm x2 x4 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card →           have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x2 x4;           have x10 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card;           x9.card ≤ x10 → x10 < (2 : ℕ) * x9.card → x3 x9 ∉ [(36608 : BitVec (16 : ℕ)), (44800 : BitVec (16 : ℕ)), (44864 : BitVec (16 : ℕ)), (44992 : BitVec (16 : ℕ)), (48960 : BitVec (16 : ℕ)), (52992 : BitVec (16 : ℕ)), (53120 : BitVec (16 : ℕ)), (53184 : BitVec (16 : ℕ)), (57216 : BitVec (16 : ℕ)), (61184 : BitVec (16 : ℕ)), (61248 : BitVec (16 : ℕ)), (61312 : BitVec (16 : ℕ)), (61376 : BitVec (16 : ℕ)), (65280 : BitVec (16 : ℕ)), (65344 : BitVec (16 : ℕ)), (65408 : BitVec (16 : ℕ)), (65472 : BitVec (16 : ℕ))] := by
  dsimp only
  intro C hsize hleast htop hjunk hlower _hupper hrare
  exact remaining C hsize hleast htop hjunk hlower (budget C hsize hleast htop hrare) hrare
