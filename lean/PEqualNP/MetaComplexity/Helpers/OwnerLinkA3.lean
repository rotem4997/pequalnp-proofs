import Mathlib
import PEqualNP.MetaComplexity.Helpers.OwnerLinkA2

/-!
# The owner link, clause (a), step A3: vertex heads, and `gOwnA` (conjecture until checked)

The vertex heads `vtxF E (REN φ)` have no repeats (`vtx_nodup`) and are exactly the numbers of
the vertices of `cvcCover φ` (`vtx_mem`). With `heads_perm`, the `innerF` lemmas and
`placedEdges` this gives clause (a) of G-OWN (`gOwnA`).
-/

namespace PEqualNP.MetaComplexity.Helpers.OwnerLink

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

/-- Every vertex head of item `(i, j)` is `2(E+1) + q` or `2q + 1` with `q = off i + j < E`. -/
theorem vtxI_cases (φ : CNF) (E : ℕ) (hI : itemsF φ ≤ E) (i j : ℕ) (hi : i < φ.length)
    (hj : j ≤ wF φ i) (x : ℕ) (hx : x ∈ vtxI E (REN φ) i j) :
    (x = 2 * (E + 1) + (offF φ i + j) ∨ x = 2 * (offF φ i + j) + 1) ∧ offF φ i + j + 1 ≤ E := by
  have hb := off_add_le φ i hi
  refine ⟨?_, by omega⟩
  unfold vtxI at hx
  simp only [List.mem_append] at hx
  rcases hx with hx | hx
  · split_ifs at hx
    · simp only [List.mem_singleton] at hx; subst hx; left; rw [ren_posF]; omega
    · simp at hx
  · split_ifs at hx with hc
    · simp only [List.mem_singleton] at hx; subst hx; right; rw [hc.2, ren_off]
    · simp at hx

theorem vtxI_nodup (φ : CNF) (E : ℕ) (hI : itemsF φ ≤ E) (i j : ℕ) (hi : i < φ.length)
    (hj : j ≤ wF φ i) : (vtxI E (REN φ) i j).Nodup := by
  have hb := off_add_le φ i hi
  unfold vtxI
  split_ifs with h1 h2 h2 <;> simp
  rw [ren_posF, h2.2, ren_off]; omega

theorem vtx_lt (φ : CNF) (E : ℕ) (hI : itemsF φ ≤ E) (x : ℕ) (hx : x ∈ vtxF E (REN φ)) :
    x < 3 * (E + 1) := by
  simp only [vtxF, List.mem_append, List.mem_flatMap, List.mem_range, ren_length, ren_wF,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ⟨i, hi, j, hj, hx⟩ | rfl | rfl
  · have := vtxI_cases φ E hI i j hi (by omega) x hx; omega
  · omega
  · omega

theorem vtx_nodup (φ : CNF) (E : ℕ) (hI : itemsF φ ≤ E) : (vtxF E (REN φ)).Nodup := by
  have hc := vtxI_cases φ E hI
  unfold vtxF
  simp only [ren_length, ren_wF]
  rw [List.nodup_append]
  refine ⟨?_, by simp; omega, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [List.mem_range] at hi
      rw [List.nodup_flatMap]
      refine ⟨fun j hj => vtxI_nodup φ E hI i j hi (by simp at hj; omega), ?_⟩
      refine (List.nodup_range).imp_of_mem ?_
      intro j j' hj hj' hne x hx hx'
      simp only [List.mem_range] at hj hj'
      have a := hc i j hi (by omega) x hx
      have b := hc i j' hi (by omega) x hx'
      omega
    · refine (List.nodup_range).imp_of_mem ?_
      intro i i' hi hi' hne x hx hx'
      simp only [List.mem_range] at hi hi'
      simp only [List.mem_flatMap, List.mem_range] at hx hx'
      obtain ⟨j, hj, hx⟩ := hx
      obtain ⟨j', hj', hx'⟩ := hx'
      have a := hc i j hi (by omega) x hx
      have b := hc i' j' hi' (by omega) x hx'
      have := item_inj φ i i' j j' hi hi' (by omega) (by omega) (by omega)
      exact hne this.1
  · intro x hx y hx' hxy
    subst hxy
    simp only [List.mem_flatMap, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, hx⟩ := hx
    have a := hc i j hi (by omega) x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    omega

section
variable {φ : CNF} {E : ℕ} {num : Vertex → ℕ} (hI : itemsF φ ≤ E)
  (h1 : ∀ z ∈ vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * eF φ z + (if b then 1 else 0))
  (h2 : ∀ b : Bool, num (Sum.inl (fresh φ, b)) = 2 * E + (if b then 1 else 0))
  (h3 : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
    num (Sum.inr (i, j)) = 2 * (E + 1) + offF φ i + j)
  (h4 : num (Sum.inr (φ.length, 0)) = 3 * E + 2)
include h1 h2 h3 h4

/-- The vertex heads are exactly the numbers of the cover vertices. -/
theorem vtx_mem (x : ℕ) : x ∈ vtxF E (REN φ) ↔ ∃ w ∈ cvcCover φ, num w = x := by
  constructor
  · intro hx
    simp only [vtxF, List.mem_append, List.mem_flatMap, List.mem_range, ren_length, ren_wF,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ⟨i, hi, j, hj, hx⟩ | rfl | rfl
    · unfold vtxI at hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · split_ifs at hx with hc
        · simp only [List.mem_singleton] at hx; subst hx
          refine ⟨Sum.inr (i, j), ?_, ?_⟩
          · rw [cover_inr, cvc_length, cvc_length_lt φ i hi, clauseAt_cvc_lt φ i hi,
              findIdx_eval_append]
            rw [ren_fF] at hc
            exact ⟨by omega, by omega, hc⟩
          · rw [h3 i j hi (by unfold wF at hj; omega), ren_posF]
        · simp at hx
      · split_ifs at hx with hc
        · simp only [List.mem_singleton] at hx; subst hx
          rw [ren_wF] at hc
          have hz := lit_mem_vars φ i j hi hc.1
          refine ⟨Sum.inl ((litF φ i j).1, true), ?_, ?_⟩
          · rw [cover_inl, vars_cvc]; exact ⟨Or.inl hz, rfl⟩
          · rw [h1 _ hz true, ren_lit φ i j hi hc.1]; simp
        · simp at hx
    · refine ⟨Sum.inl (fresh φ, true), ?_, ?_⟩
      · rw [cover_inl, vars_cvc]; exact ⟨Or.inr rfl, rfl⟩
      · rw [h2 true]; simp
    · refine ⟨Sum.inr (φ.length, 0), ?_, h4⟩
      rw [cover_inr, cvc_length, clauseAt_cvc_eq]
      refine ⟨by omega, by simp, ?_⟩
      simp [List.findIdx_cons, Literal.eval]
  · rintro ⟨w, hw, rfl⟩
    simp only [vtxF, List.mem_append, List.mem_flatMap, List.mem_range, ren_length, ren_wF,
      List.mem_cons, List.not_mem_nil, or_false]
    rcases w with ⟨z, b⟩ | ⟨i, j⟩
    · rw [cover_inl, vars_cvc] at hw
      obtain ⟨hz | rfl, hb⟩ := hw <;> simp only at hb <;> subst hb
      · obtain ⟨i, j, hi, hj, hz', he⟩ := eF_spec φ z hz
        left
        refine ⟨i, hi, j, by omega, ?_⟩
        unfold vtxI
        rw [List.mem_append]; right
        have hl := ren_lit φ i j hi hj
        rw [if_pos ⟨by rw [ren_wF]; exact hj, by rw [hl, ren_off]; simp [hz', he]⟩, hl, hz',
          h1 z hz true]
        simp
      · right; left; rw [h2 true]; simp
    · rw [cover_inr, cvc_length] at hw
      obtain ⟨hi, hj, hne⟩ := hw
      rcases Nat.lt_or_ge i φ.length with hi' | hi'
      · rw [cvc_length_lt φ i hi'] at hj
        rw [clauseAt_cvc_lt φ i hi', findIdx_eval_append] at hne
        left
        refine ⟨i, hi', j, by omega, ?_⟩
        unfold vtxI
        rw [List.mem_append]; left
        rw [if_pos (by rw [ren_fF]; exact hne), h3 i j hi' (by unfold wF at hj; omega),
          ren_posF]
        simp
      · have : i = φ.length := by omega
        subst this
        rw [clauseAt_cvc_eq] at hj
        simp at hj; subst hj
        right; right; exact h4

end

/-- Clause (a) of G-OWN (conjecture until checked). -/
theorem gOwnA : GOwnA := by
  intro φ E k off e hk hE hoff he num h1 h2 h3 h4 H hH T hT S hS F hF ol hol
  have hI : itemsF φ ≤ E := hE ▸ items_le_encode φ
  have hoffF : ∀ i, off i = offF φ i := fun i => hoff i
  have heF : ∀ z, e z = eF φ z := fun z => he z
  have h1' : ∀ z ∈ vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * eF φ z + (if b then 1 else 0) := by
    intro z hz b; rw [h1 z hz b, heF]
  have h3' : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      num (Sum.inr (i, j)) = 2 * (E + 1) + offF φ i + j := by
    intro i j hi hj; rw [h3 i j hi hj, hoffF]
  obtain ⟨pN, pB, pA, pT⟩ := placedEdges φ E k off e hk hE hoff he num h1 h2 h3 h4 H hH T hT
  have hp := heads_perm E k (REN φ)
  rw [← OWN_eq, ← hol] at hp
  have thr : ∀ x, x ∈ (callsF E (REN φ)).flatMap (hdF E k) → 3 * (E + 1) ≤ x := by
    intro x hx
    simp only [List.mem_flatMap, hdF, innerF_heads] at hx
    obtain ⟨c, -, i, -, rfl, -⟩ := hx
    omega
  refine ⟨?_, ?_⟩
  · rw [hp.nodup_iff, List.nodup_append]
    refine ⟨?_, vtx_nodup φ E hI, ?_⟩
    · rw [List.nodup_flatMap]
      refine ⟨fun c _ => innerF_heads_nodup _ _ _ _ _, ?_⟩
      have pw := List.pairwise_map.mp pN
      refine pw.imp_of_mem ?_
      intro a b ha hb hne x hx hx'
      exact innerF_heads_disjoint (pB a ha).2 (pB b hb).2 hne x hx hx'
    · intro x hx y hx' hxy
      subst hxy
      have := thr x hx
      have := vtx_lt φ E hI x hx'
      omega
  · intro j
    rw [hF, hp.mem_iff, List.mem_append, or_comm]
    apply or_congr
    · simp only [List.mem_flatMap, hdF, innerF_heads]
      constructor
      · rintro ⟨u, v, i, huv, hadj, hj, hpar⟩
        obtain ⟨t, ht⟩ := (pA u v huv).mp hadj
        have ht' := pT _ ht u rfl
        refine ⟨_, ht, i.val, i.isLt, hj, ?_⟩
        rw [hpar, ht']
      · rintro ⟨c, hc, i, hi, hj, hpar⟩
        have hb := pB c hc
        refine ⟨⟨c.1, by omega⟩, ⟨c.2.1, by omega⟩, ⟨i, hi⟩, ?_, ?_, hj, ?_⟩
        · show c.1 < c.2.1; exact hb.1
        · rw [pA _ _ (show (⟨c.1, _⟩ : Fin (3 * (E + 1))) < ⟨c.2.1, _⟩ from hb.1)]
          exact ⟨c.2.2, hc⟩
        · rw [hpar, pT c hc _ rfl]
    · rw [vtx_mem h1' h2 h3' h4]
      constructor
      · rintro ⟨u, hu, hj⟩
        obtain ⟨w, hw, hn⟩ := (hT u).mp hu
        exact ⟨w, hw, by rw [hn, hj]⟩
      · rintro ⟨w, hw, hn⟩
        have hlt : j.val < 3 * (E + 1) :=
          vtx_lt φ E hI _ ((vtx_mem h1' h2 h3' h4 _).mpr ⟨w, hw, hn⟩)
        exact ⟨⟨j.val, hlt⟩, (hT _).mpr ⟨w, hw, hn⟩, rfl⟩

end PEqualNP.MetaComplexity.Helpers.OwnerLink
