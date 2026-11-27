import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.LowMerge

-- Index a test by a quadrangle and one of its three missing lines. Delete that
-- line: the remaining four points and two lines give eight singleton pairs.
-- Each nonincident pair lies in 24 quadrangles and survives two deletions in each.
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_6210_421
    (footprints :
      let S := singerLines3
      ∃ T : Finset (Finset (Fin 13) × Fin 13), T.card = 702 ∧
        (∀ t ∈ T, t.1 ∈ quadrangles S ∧ t.2 ∈ missLines S t.1) ∧
        ∀ e : Fin 13 × Fin 13, e.1 ∉ S e.2 →
        (T.filter fun t => e.1 ∈ t.1 ∧ e.2 ∈ (missLines S t.1).erase t.2).card ≤ 48)
    -- Accounting on actual wires. Pair-clean tests need not make the wire false:
    -- the circuit may first fire on an input larger than a singleton pair.
    (account : ∀ (C : Circuit) (a b : ℕ),
      Monotone2 C → ReadsBack 26 C → a < 26 + C.size → b < 26 + C.size →
      let S := singerLines3
      let V := fun w Q => wireVal C (incidenceInput Q (missLines S Q)) w
      (∀ w ∈ [a, b], RightOnIncidentPairs S ⟨C.gates, w⟩) →
      (∀ Q, IsQuadrangle S Q → V a Q = false ∨ V b Q = false) →
      (∀ w ∈ [a, b], ∃ Q, IsQuadrangle S Q ∧ V w Q = true) →
      ∀ F : Finset (Finset (Fin 13) × Fin 13), 126 ≤ F.card →
      (∀ t ∈ F, t.1 ∈ quadrangles S ∧ t.2 ∈ missLines S t.1 ∧
        ∀ p ∈ t.1, ∀ l ∈ (missLines S t.1).erase t.2,
          wireVal C (incidenceInput {p} {l}) a = false) → 63 ≤ C.size) :
    ∀ (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack 26 C →
      a < 26 + C.size → b < 26 + C.size →
      let V := fun (w : ℕ) (Q : Finset (Fin 13)) =>
        wireVal C (incidenceInput Q (missLines singerLines3 Q)) w
      let E := fun (w : ℕ) => Finset.univ.filter (fun e : Fin 13 × Fin 13 =>
        e.1 ∉ singerLines3 e.2 ∧ wireVal C (incidenceInput {e.1} {e.2}) w = true)
      (E a).card ≤ 12 →
      RightOnIncidentPairs singerLines3 ⟨C.gates, a⟩ →
      RightOnIncidentPairs singerLines3 ⟨C.gates, b⟩ →
      (∀ Q, IsQuadrangle singerLines3 Q → V a Q = false ∨ V b Q = false) →
      (∃ Q, IsQuadrangle singerLines3 Q ∧ V a Q = false ∧ V b Q = true) →
      (∃ Q, IsQuadrangle singerLines3 Q ∧ V b Q = false ∧ V a Q = true) → 63 ≤ C.size := by
  intro C a b hm hr ha hb V E sparse ra rb safe wb wa
  obtain ⟨T, hT, testSpec, footprint⟩ := footprints
  let hits := fun (e : Fin 13 × Fin 13) =>
    T.filter fun t => e.1 ∈ t.1 ∧ e.2 ∈ (missLines singerLines3 t.1).erase t.2
  let covered := (E a).biUnion hits
  have bound (e) (he : e ∈ E a) : (hits e).card ≤ 48 :=
    footprint e (Finset.mem_filter.mp he).2.1
  have hc : covered.card ≤ 576 := calc
    covered.card ≤ ∑ e ∈ E a, (hits e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ E a, 48 := Finset.sum_le_sum bound
    _ = (E a).card * 48 := by simp
    _ ≤ 576 := by omega
  refine account C a b hm hr ha hb ?_ ?_ ?_ (T \ covered) ?_ ?_
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ra
    · exact rb
  · exact safe
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · obtain ⟨Q, hQ, _, h⟩ := wa
      exact ⟨Q, hQ, h⟩
    · obtain ⟨Q, hQ, _, h⟩ := wb
      exact ⟨Q, hQ, h⟩
  · have := Finset.le_card_sdiff covered T
    omega
  · intro t ht
    have hboth : t ∈ T ∧ t ∉ covered := Finset.mem_sdiff.mp ht
    obtain ⟨htT, outside⟩ := hboth
    refine ⟨(testSpec t htT).1, (testSpec t htT).2, ?_⟩
    intro p hp l hl
    apply Bool.eq_false_iff.mpr
    intro yes
    have hl' : l ∈ missLines singerLines3 t.1 := Finset.mem_of_mem_erase hl
    have disj : Disjoint (singerLines3 l) t.1 := (Finset.mem_filter.mp hl').2
    have he : (p, l) ∈ E a :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.disjoint_right.mp disj hp, yes⟩
    exact outside (Finset.mem_biUnion.mpr ⟨(p, l), he, Finset.mem_filter.mpr ⟨htT, hp, hl⟩⟩)
