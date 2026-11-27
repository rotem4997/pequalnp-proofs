import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_4835_391
    (rich : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ (C : Circuit) (v : Fin 11), IsLeastAO G C → v.val < 4 →
      (let Reads := (fun j : ℕ => j < C.size ∧ v.val ∈ (gateAt C j).inputs);
      (∃ i j k : ℕ, i < j ∧ j < k ∧ Reads i ∧ Reads j ∧ Reads k) ∨
        (∃ a b : ℕ, a ≠ b ∧ Reads a ∧ Reads b ∧ (gateAt C a).op = GateOp.and)) →
      let rep := (fun j : ℕ => ∃ k < 11 + j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11 + j) = wval C x k);
          ∃ i j k : ℕ, i < j ∧ j < k ∧ k < C.size ∧ rep i ∧ rep j ∧ rep k)
    (sparse : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 21 →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        (∀ v : Fin 11, v.val < 4 → ¬ (let Reads := (fun j : ℕ => j < C.size ∧ v.val ∈ (gateAt C j).inputs);
      (∃ i j k : ℕ, i < j ∧ j < k ∧ Reads i ∧ Reads j ∧ Reads k) ∨
        (∃ a b : ℕ, a ≠ b ∧ Reads a ∧ Reads b ∧ (gateAt C a).op = GateOp.and))) →
        ∃ v : Fin 11, v.val < 4 ∧
          (let rep := (fun j : ℕ => ∃ k < 11 + j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11 + j) = wval C x k);
          ∃ i j k : ℕ, i < j ∧ j < k ∧ k < C.size ∧ rep i ∧ rep j ∧ rep k)) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             ∃ (x8 : Fin (11 : ℕ)),               ↑x8 < (4 : ℕ) ∧                 have x9 : ℕ → Prop := fun (x9 : ℕ) => ∃ x10 < (11 : ℕ) + x9, ∀ (x11 : Fin (11 : ℕ) → Bool), x11 x8 = Bool.false → PEqualNP.ReadTwo.wval x2 x11 ((11 : ℕ) + x9) = PEqualNP.ReadTwo.wval x2 x11 x10;                 ∃ (x10 : ℕ) (x11 : ℕ) (x12 : ℕ), x10 < x11 ∧ x11 < x12 ∧ x12 < x2.size ∧ x9 x10 ∧ x9 x11 ∧ x9 x12 := by
  dsimp only
  intro C hLeast hTop hJunk hSize hCharge
  let richAt := fun v : Fin 11 => let Reads := (fun j : ℕ => j < C.size ∧ v.val ∈ (gateAt C j).inputs);
      (∃ i j k : ℕ, i < j ∧ j < k ∧ Reads i ∧ Reads j ∧ Reads k) ∨
        (∃ a b : ℕ, a ≠ b ∧ Reads a ∧ Reads b ∧ (gateAt C a).op = GateOp.and)
  by_cases someRich : ∃ v : Fin 11, v.val < 4 ∧ richAt v
  · obtain ⟨v, hv, h⟩ := someRich
    exact ⟨v, hv, rich C v hLeast hv h⟩
  · exact sparse C hLeast hTop hJunk hSize hCharge (fun v hv h => someRich ⟨v, hv, h⟩)
