import Mathlib
import PEqualNP.MetaComplexity.Helpers.OwnerLinkP1

/-!
# The owner link, step P2: the call pairs have no repeats (conjecture until checked)

First conjunct of `PlacedEdges`. Every call of item `(i, j)` carries the item index
`offF i + j` in a decodable place (`keyF`), the two closing calls carry `E`, and item indices
are injective (`item_inj`).
-/

namespace PEqualNP.MetaComplexity.Helpers.OwnerLink

open PEqualNP.Search

/-- The calls of item `(i, j)`. -/
def blkF (E : ℕ) (ψ : CNF) (i j : ℕ) : List (ℕ × ℕ × Bool) :=
  (if j < wF ψ i then
      [(2 * (litF ψ i j).1 + (if (litF ψ i j).2 then 1 else 0), posF E ψ i j, (litF ψ i j).2)]
    else [(2 * E + 1, posF E ψ i j, true)]) ++
  ((List.range (wF ψ i + 1)).filter (fun l : ℕ => decide (j < l))).map
      (fun l : ℕ => (posF E ψ i j, posF E ψ i l, decide (j ≠ fF ψ i))) ++
  (if j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j then
      [(2 * (litF ψ i j).1, 2 * (litF ψ i j).1 + 1, false)] else [])

theorem callsF_eq (E : ℕ) (ψ : CNF) : callsF E ψ =
    (List.range ψ.length).flatMap (fun i : ℕ =>
      (List.range (wF ψ i + 1)).flatMap (fun j : ℕ => blkF E ψ i j)) ++
    [(2 * E, 2 * E + 1, false), (2 * E, 3 * E + 2, false)] := rfl

/-- The decoding of the item index from a call pair. -/
def keyF (E u v : ℕ) : ℕ :=
  if v < 2 * E + 2 then u / 2 else if u < 2 * E + 2 then v - (2 * E + 2) else u - (2 * E + 2)

theorem keyF_lo {E u v : ℕ} (hv : 2 * E + 2 ≤ v) (hu : u < 2 * E + 2) :
    keyF E u v = v - (2 * E + 2) := by
  unfold keyF; rw [if_neg (by omega), if_pos hu]

theorem keyF_hi {E u v : ℕ} (hv : 2 * E + 2 ≤ v) (hu : 2 * E + 2 ≤ u) :
    keyF E u v = u - (2 * E + 2) := by
  unfold keyF; rw [if_neg (by omega), if_neg (by omega)]

theorem keyF_lit {E u v : ℕ} (hv : v < 2 * E + 2) : keyF E u v = u / 2 := by
  unfold keyF; rw [if_pos hv]

section
variable (E : ℕ) (ψ : CNF) (hpos : ∀ i, i < ψ.length → offF ψ i + wF ψ i < E)
  (hvar : ∀ i j, (litF ψ i j).1 ≤ E)
include hpos hvar

theorem blk_key (i j : ℕ) (hi : i < ψ.length) (hj : j ≤ wF ψ i) :
    ∀ c ∈ blkF E ψ i j, keyF E c.1 c.2.1 = offF ψ i + j := by
  have hp := hpos i hi
  have hv := hvar i j
  have hb : (if (litF ψ i j).2 then 1 else 0) ≤ 1 := by split <;> omega
  intro c hc
  simp only [blkF, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq] at hc
  rcases hc with (hc | ⟨l, ⟨hl, hjl⟩, rfl⟩) | hc
  · by_cases hjw : j < wF ψ i
    · rw [if_pos hjw, List.mem_singleton] at hc; subst hc
      simp only [posF]
      rw [keyF_lo (by omega) (by omega)]; omega
    · rw [if_neg hjw, List.mem_singleton] at hc; subst hc
      simp only [posF]
      rw [keyF_lo (by omega) (by omega)]; omega
  · simp only [posF]
    rw [keyF_hi (by omega) (by omega)]; omega
  · by_cases h : j < wF ψ i ∧ (litF ψ i j).1 = offF ψ i + j
    · rw [if_pos h, List.mem_singleton] at hc; subst hc
      simp only
      rw [keyF_lit (by omega)]; omega
    · rw [if_neg h] at hc; simp at hc

theorem blk_nodup (i j : ℕ) (hi : i < ψ.length) (hj : j ≤ wF ψ i) :
    ((blkF E ψ i j).map (fun c : ℕ × ℕ × Bool => (c.1, c.2.1))).Nodup := by
  have hp := hpos i hi
  have hv := hvar i j
  unfold blkF
  simp only [List.map_append, List.map_map]
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · split_ifs <;> simp
  · refine List.Nodup.map ?_ ((List.nodup_range).filter _)
    intro a b h
    simp only [Function.comp_apply, Prod.mk.injEq, posF] at h
    omega
  · intro x hx y hy hxy
    subst hxy
    simp only [List.mem_map, List.mem_filter, List.mem_range, Function.comp_apply] at hy
    obtain ⟨l, -, rfl⟩ := hy
    split_ifs at hx <;> simp only [List.mem_map, List.mem_singleton, Prod.mk.injEq] at hx <;>
      obtain ⟨c, rfl, h⟩ := hx <;> simp only [Prod.mk.injEq, posF] at h <;> omega
  · split_ifs <;> simp
  · intro x hx y hy hxy
    subst hxy
    split_ifs at hy with h
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
      subst hy
      simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        Function.comp_apply] at hx
      rcases hx with hx | ⟨l, -, hx⟩
      · split_ifs at hx <;> simp only [List.mem_map, List.mem_singleton] at hx <;>
          obtain ⟨c, rfl, h'⟩ := hx <;> simp only [Prod.mk.injEq, posF] at h' <;> omega
      · simp only [Prod.mk.injEq, posF] at hx; omega
    · simp at hy

theorem calls_nodup_gen :
    ((callsF E ψ).map (fun c : ℕ × ℕ × Bool => (c.1, c.2.1))).Nodup := by
  rw [callsF_eq, List.map_append, List.nodup_append]
  have hkey : ∀ c ∈ (List.range ψ.length).flatMap (fun i : ℕ =>
      (List.range (wF ψ i + 1)).flatMap (fun j : ℕ => blkF E ψ i j)),
      ∃ i j, i < ψ.length ∧ j ≤ wF ψ i ∧ keyF E c.1 c.2.1 = offF ψ i + j := by
    intro c hc
    simp only [List.mem_flatMap, List.mem_range] at hc
    obtain ⟨i, hi, j, hj, hc⟩ := hc
    exact ⟨i, j, hi, by omega, blk_key E ψ hpos hvar i j hi (by omega) c hc⟩
  refine ⟨?_, by simp; omega, ?_⟩
  · rw [List.map_flatMap, List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [List.mem_range] at hi
      rw [List.map_flatMap, List.nodup_flatMap]
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [List.mem_range] at hj
        exact blk_nodup E ψ hpos hvar i j hi (by omega)
      · refine List.Nodup.pairwise_of_forall_ne List.nodup_range ?_
        intro j hj j' hj' hne x hx hy
        rw [List.mem_range] at hj hj'
        simp only [List.mem_map] at hx hy
        obtain ⟨c, hc, rfl⟩ := hx
        obtain ⟨c', hc', h⟩ := hy
        have h1 := blk_key E ψ hpos hvar i j hi (by omega) c hc
        have h2 := blk_key E ψ hpos hvar i j' hi (by omega) c' hc'
        simp only [Prod.mk.injEq] at h
        rw [h.1, h.2] at h2
        exact hne (by omega)
    · refine List.Nodup.pairwise_of_forall_ne List.nodup_range ?_
      intro i hi i' hi' hne x hx hy
      rw [List.mem_range] at hi hi'
      simp only [List.mem_map, List.mem_flatMap, List.mem_range] at hx hy
      obtain ⟨c, ⟨j, hj, hc⟩, rfl⟩ := hx
      obtain ⟨c', ⟨j', hj', hc'⟩, h⟩ := hy
      have h1 := blk_key E ψ hpos hvar i j hi (by omega) c hc
      have h2 := blk_key E ψ hpos hvar i' j' hi' (by omega) c' hc'
      simp only [Prod.mk.injEq] at h
      rw [h.1, h.2] at h2
      exact hne (item_inj ψ i i' j j' hi hi' (by omega) (by omega) (by omega)).1
  · intro x hx y hy hxy
    subst hxy
    simp only [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨i, j, hi, hj, hk⟩ := hkey c hc
    have := hpos i hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hy
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [keyF, h1, h2] at hk <;> split_ifs at hk <;>
      omega

end

/-- First conjunct of `PlacedEdges`, for `REN φ` with `itemsF φ ≤ E`. -/
theorem calls_nodup (φ : CNF) (E : ℕ) (hE : itemsF φ ≤ E) :
    ((callsF E (REN φ)).map (fun c : ℕ × ℕ × Bool => (c.1, c.2.1))).Nodup := by
  refine calls_nodup_gen E (REN φ) ?_ (fun i j => (ren_var_le φ i j).trans hE)
  intro i hi
  rw [ren_length] at hi
  have := off_add_le φ i hi
  have hw : wF (REN φ) i = wF φ i := ren_getD_length φ i
  rw [ren_off, hw]; omega

end PEqualNP.MetaComplexity.Helpers.OwnerLink
