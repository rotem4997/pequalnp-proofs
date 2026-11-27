import Mathlib
import PEqualNP.Defs

-- Points and lines with q + 1 points on every line and a unique line through two
-- distinct points: on a line l of T, every other line of T meets l in at most one
-- point, so at least q + 2 - T.card points of l lie on no other line of T.
namespace PEqualNP.Outside.L_meta_4763

theorem private_count {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hcard : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (huniq : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (T : Finset (Fin N)) (l : Fin N) (hl : l ∈ T)
    [instS : Fintype {p : Fin N // I p l ∧ ∀ k ∈ T.erase l, ¬ I p k}] :
    q + 2 ≤ T.card + Fintype.card {p : Fin N // I p l ∧ ∀ k ∈ T.erase l, ¬ I p k} := by
  have hpriv : Fintype.card {p : Fin N // I p l ∧ ∀ k ∈ T.erase l, ¬ I p k}
      = (Finset.univ.filter (fun p : Fin N => I p l ∧ ∀ k ∈ T.erase l, ¬ I p k)).card :=
    Fintype.card_of_subtype _ (fun x => by
      rw [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩)
  rw [hpriv]
  have h1 : (Finset.univ.filter (fun p : Fin N => I p l)).card = q + 1 := by
    rw [← hcard l]
    exact (Fintype.card_of_subtype _ (fun x => by
      rw [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩)).symm
  have h2 : Finset.univ.filter (fun p : Fin N => I p l)
      ⊆ Finset.univ.filter (fun p : Fin N => I p l ∧ ∀ k ∈ T.erase l, ¬ I p k)
        ∪ (T.erase l).biUnion
          (fun k => Finset.univ.filter (fun p : Fin N => I p l ∧ I p k)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_union]
    by_cases hp' : ∀ k ∈ T.erase l, ¬ I p k
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2, hp'⟩)
    · right
      by_contra hno
      apply hp'
      intro k hk hpk
      apply hno
      rw [Finset.mem_biUnion]
      exact ⟨k, hk, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2, hpk⟩⟩
  have h3 : ∀ k ∈ T.erase l,
      (Finset.univ.filter (fun p : Fin N => I p l ∧ I p k)).card ≤ 1 := by
    intro k hk
    have hkl : k ≠ l := Finset.ne_of_mem_erase hk
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    obtain ⟨l0, _, hl0⟩ := huniq a b hab
    have e1 : l = l0 := hl0 l ⟨ha.2.1, hb.2.1⟩
    have e2 : k = l0 := hl0 k ⟨ha.2.2, hb.2.2⟩
    exact hkl (e2.trans e1.symm)
  have h4 := Finset.card_le_card h2
  have h5 := Finset.card_union_le
    (Finset.univ.filter (fun p : Fin N => I p l ∧ ∀ k ∈ T.erase l, ¬ I p k))
    ((T.erase l).biUnion (fun k => Finset.univ.filter (fun p : Fin N => I p l ∧ I p k)))
  have h6 := Finset.card_biUnion_le_card_mul (T.erase l)
    (fun k => Finset.univ.filter (fun p : Fin N => I p l ∧ I p k)) 1 h3
  have h7 : (T.erase l).card + 1 = T.card := Finset.card_erase_add_one hl
  omega

end PEqualNP.Outside.L_meta_4763

theorem PEqualNP.Outside.L_meta_4763 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), ∀ x8 ∈ x7, x1 + (2 : ℕ) ≤ x7.card + Fintype.card { x10 : Fin x2 // x3 x10 x8 ∧ ∀ x11 ∈ x7.erase x8, ¬x3 x10 x11 } := by
  intro q N I instI hcard huniq T l hl
  exact PEqualNP.Outside.L_meta_4763.private_count I hcard huniq T l hl
