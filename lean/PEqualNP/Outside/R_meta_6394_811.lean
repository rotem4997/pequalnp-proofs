import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_6394_811
    (normalizeAccount : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C →
      ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ D.size = C.size ∧
        (junk G D).card = (junk G C).card ∧
        G.edgeFinset.card + (tops G D \ centreless G D).card +
          2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card ≤
            D.size + (Ustar G D).card + 1)
    (mixedCharge : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
      G = SimpleGraph.fromRel (fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧
        (u.val + 26 - v.val) % 13 ∈ ([0,1,3,9] : List ℕ)) →
      IsLeastAO G C → TopForm G C → C.size ≤ 64 → junk G C ≠ ∅ →
      ∃ K : Finset (Fin 26), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
        (∃ p : Fin 13, Fin.castAdd 13 p ∈ K) ∧ (∃ l : Fin 13, Fin.natAdd 13 l ∈ K) ∧
        K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
          2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 ≠ ∅ → ∃ (x7 : Finset (Fin (26 : ℕ))), (∀ (x8 x9 : Fin (26 : ℕ)), x1.Adj x8 x9 → x8 ∈ x7 ∨ x9 ∈ x7) ∧ (∃ (x8 : Fin (13 : ℕ)), Fin.castAdd (13 : ℕ) x8 ∈ x7) ∧ (∃ (x8 : Fin (13 : ℕ)), Fin.natAdd (13 : ℕ) x8 ∈ x7) ∧ (52 : ℕ) + x7.card ≤ x3.size + (1 : ℕ) := by
  intro G inst C graph least dirty
  let G0 := SimpleGraph.fromRel (fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧
    (u.val + 26 - v.val) % 13 ∈ ([0,1,3,9] : List ℕ))
  let dec0 : DecidableRel G0.Adj := inferInstance
  have geometry : ∀ u v : Fin 26, G0.Adj u v ↔ ∃ p l : Fin 13,
      (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧
      ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨
        (v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)) := by decide
  have same : G = G0 := SimpleGraph.ext (funext fun u => funext fun v =>
    propext ((graph u v).trans (geometry u v).symm))
  subst G
  have instanceSame : inst = dec0 := Subsingleton.elim _ _
  subst inst
  have squareFree : NoFourCycle G0 := by decide
  have edgeCount : G0.edgeFinset.card = 52 := by decide
  have hasEdge : G0.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  by_cases small : C.size ≤ 64
  · obtain ⟨D, leastD, formD, sizeD, junkD, budgetD⟩ :=
      normalizeAccount 26 G0 C squareFree hasEdge least
    have dirtyD : junk G0 D ≠ ∅ := by
      intro empty
      have positive := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr dirty)
      have zero : (junk G0 D).card = 0 := congrArg Finset.card empty
      omega
    obtain ⟨K, cover, point, line, charge⟩ :=
      mixedCharge G0 D rfl leastD formD (by omega) dirtyD
    refine ⟨K, cover, point, line, ?_⟩
    omega
  · let points := (Finset.univ : Finset (Fin 13)).image (Fin.castAdd 13)
    let K := insert (Fin.natAdd 13 (0 : Fin 13)) points
    have point (p : Fin 13) : Fin.castAdd 13 p ∈ K :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)
    refine ⟨K, ?_, ⟨0, point 0⟩, ⟨0, Finset.mem_insert_self ..⟩, ?_⟩
    · intro u v adjacent
      obtain ⟨p, l, _, orientation⟩ := (geometry u v).mp adjacent
      rcases orientation with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl (point p)
      · exact Or.inr (point p)
    · have card : K.card = 14 := by decide
      omega
