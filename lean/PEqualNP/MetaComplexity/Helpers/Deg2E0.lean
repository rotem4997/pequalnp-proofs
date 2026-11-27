import PEqualNP.MetaComplexity.Helpers.Deg2Forms

/-!
# The E0 count D2-10 (helper for L-meta-649, package P2)

Card `card10_e0` of the degree-two card plan, statement exactly as there.

Proof (paper: the paper text of the cards, section 1). For `w ∈ W` the
root `R w` is false at the test input `z_{w}` (soundness). A pair `(p, w)` of `E0` whose root has
at most one alive point is charged to `w`. Otherwise the walk of E1 (`Forms.walk_two`, from the
path lemma D2-05) goes from `R w` to a gate `g` of the form with two alive points, false at
`z_{w}`, and a kid `c` with alive set `{p}`; `w` is the unique line of `g` (no rectangle) and `p`
is one of at most two kid points of `g`: two charges per gate.

Everything here is conjecture until the checker accepts it.
-/

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.MetaComplexity.Deg2.Forms

variable {N : ℕ}

/-- In a sound partial form, a root `R w` is false at the test input `z_{w}`. -/
theorem e0_root_false {I : Fin N → Fin N → Prop} {D : Dag N} {W : Finset (Fin N)}
    {R : Fin N → ℕ} (hs : Dag.SoundPartialForm I D W R) {w : Fin N} (hw : w ∈ W) :
    D.val (testInput I {w}) (R w) = false := by
  by_contra hf
  rw [Bool.not_eq_false] at hf
  obtain ⟨p, l, hpl, hp, hl⟩ :=
    hs.2.2 _ ⟨w, hw, (testInput_natAdd I {w} w).2 (Finset.mem_singleton_self w), hf⟩
  rw [testInput_natAdd, Finset.mem_singleton] at hl
  subst hl
  exact (testInput_castAdd I {l} p).1 hp l (Finset.mem_singleton_self l) hpl

/-- D2-10 (E0). -/
theorem card10_e0 (I : Fin N → Fin N → Prop) (hI : NoRect I) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) (hs : Dag.SoundPartialForm I D W R) :
    (D.e0Set W R).card ≤ 2 * (D.rootCone W R).card + W.card := by
  classical
  let T : ℕ → Finset (Fin N × Fin N) := fun g =>
    (Finset.univ.filter (fun q : Fin N => ∃ c, D.Kid g c ∧ D.alive c = {q})) ×ˢ
      (Finset.univ.filter (fun w : Fin N =>
        D.val (testInput I {w}) g = false ∧ 2 ≤ (D.alive g).card))
  have hT : ∀ g, (T g).card ≤ 2 := by
    intro g
    rw [Finset.card_product]
    have h1 := kid_points_card D g
    have h2 : (Finset.univ.filter (fun w : Fin N =>
        D.val (testInput I {w}) g = false ∧ 2 ≤ (D.alive g).card)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      exact line_unique I hI D ha.2.2 ha.2.1 hb.2.1
    calc _ ≤ 2 * 1 := Nat.mul_le_mul h1 h2
      _ = 2 := rfl
  let U : Fin N → Finset (Fin N × Fin N) := fun w =>
    if (D.alive (R w)).card ≤ 1 then D.alive (R w) ×ˢ {w} else ∅
  have hU : ∀ w, (U w).card ≤ 1 := by
    intro w
    simp only [U]
    split_ifs with h
    · rw [Finset.card_product, Finset.card_singleton, mul_one]; exact h
    · simp
  have hsub : D.e0Set W R ⊆ (D.rootCone W R).biUnion T ∪ W.biUnion U := by
    intro e he
    unfold Dag.e0Set at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, hw, hp⟩ := he
    by_cases h2 : 2 ≤ (D.alive (R e.2)).card
    · obtain ⟨g, c, hr, hk, hg2, hc, hg0⟩ :=
        walk_two D e.1 _ (R e.2) hp (e0_root_false hs hw) h2
      obtain ⟨hgN, hgs⟩ := kid_gate hk
      apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      refine ⟨g, mem_rootCone hw hr hgN hgs, ?_⟩
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, c, hk, hc⟩, Finset.mem_univ _, hg0, hg2⟩
    · apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨e.2, hw, ?_⟩
      have h1 : (D.alive (R e.2)).card ≤ 1 := by omega
      simp only [U, h1, ↓reduceIte]
      rw [Finset.mem_product, Finset.mem_singleton]
      exact ⟨mem_alive.2 hp, rfl⟩
  calc (D.e0Set W R).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ((D.rootCone W R).biUnion T).card + (W.biUnion U).card := Finset.card_union_le _ _
    _ ≤ (∑ g ∈ D.rootCone W R, (T g).card) + ∑ w ∈ W, (U w).card :=
        Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
    _ ≤ (∑ _g ∈ D.rootCone W R, 2) + ∑ _w ∈ W, 1 :=
        Nat.add_le_add (Finset.sum_le_sum (fun g _ => hT g)) (Finset.sum_le_sum (fun w _ => hU w))
    _ = 2 * (D.rootCone W R).card + W.card := by
        rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_comm, mul_one]

end PEqualNP.MetaComplexity.Deg2
