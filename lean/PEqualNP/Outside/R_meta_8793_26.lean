import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

-- The four indices represent a repeated input, two points, an incidence and a nonincidence.
-- A translation and duality center the first input. Two permutations fixing it cover the second.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_8793_26
    (transport : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (σ : G ≃g G) (C : Circuit),
      IsLeastAO G C → TopForm G C →
      ∃ D : Circuit, D.size = C.size ∧ IsLeastAO G D ∧ TopForm G D ∧ junk G D = junk G C ∧
        ∀ a b : Fin 26, (gateAt C 0).inputs = [a.val, b.val] →
          (gateAt D 0).inputs = [(σ a).val, (σ b).val])
    (normalized : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
      (G = SimpleGraph.fromRel fun a b : Fin 26 =>
        a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ [0, 1, 3, 9]) →
      IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      (∃ b ∈ ([0, 1, 13, 15] : List ℕ), (gateAt C 0).inputs = [0, b]) →
      64 ≤ C.size) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card → (64 : ℕ) ≤ x3.size := by
  have orbits (G : SimpleGraph (Fin 26))
      (hG : G = SimpleGraph.fromRel fun a b : Fin 26 =>
        a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ [0, 1, 3, 9]) :
      ∀ a b : Fin 26, ∃ e : G ≃g G, e a = 0 ∧ (e b).val ∈ ([0, 1, 13, 15] : List ℕ) := by
    let plane : SimpleGraph (Fin 26) := SimpleGraph.fromRel fun a b : Fin 26 =>
      a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ [0, 1, 3, 9]
    let checked (f g : Fin 26 → Fin 26)
        (cert : (∀ v, g (f v) = v) ∧ (∀ v, f (g v) = v) ∧
          ∀ x y, plane.Adj (f x) (f y) ↔ plane.Adj x y) : plane ≃g plane :=
      { toEquiv := ⟨f, g, cert.1, cert.2.1⟩, map_rel_iff' := cert.2.2 _ _ }
    let affine (m t : ℕ) (v : Fin 26) : Fin 26 :=
      if v.val < 13 then ⟨(m * v.val + t) % 13, by omega⟩
      else ⟨13 + (m * v.val + (13 - t)) % 13, by omega⟩
    let shift := checked (affine 1 12) (affine 1 1) (by decide +kernel)
    let dual := checked (· + 13) (· + 13) (by decide +kernel)
    let triple := checked (affine 3 0) (affine 9 0) (by decide +kernel)
    let table : List (Fin 26) :=
      [0, 2, 7, 8, 6, 10, 1, 11, 4, 12, 9, 3, 5, 14, 22, 24, 13, 17, 23, 18, 15, 25, 16, 21, 19, 20]
    let turn (v : Fin 26) := table.getD v.val 0
    let eight := checked turn (turn^[7]) (by decide +kernel)
    let power (g : plane ≃g plane) (k : ℕ) : plane ≃g plane :=
      Nat.rec (motive := fun _ => plane ≃g plane) SimpleGraph.Iso.refl (fun _ r => r.trans g) k
    let center (a : Fin 26) : plane ≃g plane :=
      (if a.val < 13 then SimpleGraph.Iso.refl else dual).trans (power shift (a.val % 13))
    have center_zero : ∀ a : Fin 26, center a a = 0 := by decide +kernel
    let stabilizer (i : Fin 3) (j : Fin 8) : plane ≃g plane :=
      (power triple i.val).trans (power eight j.val)
    have cover : ∀ v : Fin 26, ∃ i : Fin 3, ∃ j : Fin 8,
        stabilizer i j 0 = 0 ∧ (stabilizer i j v).val ∈ ([0, 1, 13, 15] : List ℕ) := by
      decide +kernel
    subst G
    intro a b
    obtain ⟨i, j, fixed, chosen⟩ := cover (center a b)
    refine ⟨(center a).trans (stabilizer i j), ?_, chosen⟩
    change stabilizer i j (center a a) = 0
    rwa [center_zero a]

  intro G _ C same least top many
  have inRange : junk G C ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
  have nonempty : 0 < C.gates.length := by
    have h := Finset.card_le_card inRange
    rw [Finset.card_range] at h
    omega
  have firstMem : gateAt C 0 ∈ C.gates := by
    change C.gates.getD 0 ⟨GateOp.or, []⟩ ∈ C.gates
    rw [List.getD_eq_getElem _ _ nonempty]
    exact List.getElem_mem ..
  obtain ⟨i, j, pair⟩ := List.length_eq_two.mp (least.1.2.2 _ firstMem)
  have hi : i < 26 := by simpa using least.1.2.1 0 nonempty i (by simp [pair])
  have hj : j < 26 := by simpa using least.1.2.1 0 nonempty j (by simp [pair])
  let a : Fin 26 := ⟨i, hi⟩
  let b : Fin 26 := ⟨j, hj⟩
  obtain ⟨σ, ha, hb⟩ := orbits G same a b
  obtain ⟨D, size, leastD, topD, junkD, firstD⟩ := transport G σ C least top
  have mapped := firstD a b pair
  rw [ha] at mapped
  rw [← size]
  exact normalized G D same leastD topD (junkD ▸ many) ⟨(σ b).val, hb, mapped⟩
