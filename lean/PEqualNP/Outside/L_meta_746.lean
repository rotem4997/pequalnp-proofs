import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_746

theorem isAcyclic_of_order {n : ℕ} (H : SimpleGraph (Fin n)) (ord : Fin n → ℕ)
    (hinj : Function.Injective ord)
    (hord : ∀ v u1 u2 : Fin n, H.Adj u1 v → H.Adj u2 v → ord u1 < ord v → ord u2 < ord v → u1 = u2) :
    H.IsAcyclic := by
  intro v c hc
  let S : Finset (Fin n) := c.support.toFinset
  have hS : S.Nonempty := ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image S ord hS
  have hm_supp : m ∈ c.support := List.mem_toFinset.mp hmS
  let c' := c.rotate m hm_supp
  have hc' : c'.IsCycle := hc.rotate hm_supp
  have hlen3 : 3 ≤ c'.length := hc'.three_le_length
  have hsupp_sub : ∀ w ∈ c'.support, w ∈ S := by
    intro w hw
    apply List.mem_toFinset.mpr
    by_cases hwm : w = m
    · exact hwm ▸ hm_supp
    · obtain ⟨n1, hn1⟩ := c.support_rotate m hm_supp
      have hw_tail : w ∈ c'.support.tail := by
        cases hc'eq : c' with
        | nil => rw [hc'eq] at hw; simp at hw; exact (hwm hw).elim
        | cons _ p =>
          rw [hc'eq] at hw
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons, List.tail_cons] at hw ⊢
          exact hw.resolve_left hwm
      have hw_rot : w ∈ c.support.tail := by
        rw [← hn1]; exact List.mem_rotate.mpr hw_tail
      exact List.mem_of_mem_tail hw_rot
  cases hc'eq : c' with
  | nil => rw [hc'eq] at hlen3; simp at hlen3
  | cons h1 p1 =>
    rename_i u1
    have hu1_ne : u1 ≠ m := h1.ne.symm
    have hu1_S : u1 ∈ S := hsupp_sub u1 (by rw [hc'eq]; simp)
    have hlt1 : ord u1 < ord m := by
      have hle := hmax u1 hu1_S
      have hne : ord u1 ≠ ord m := fun e => hu1_ne (hinj e)
      omega
    cases hrev : c'.reverse with
    | nil =>
      have : c'.reverse.length = c'.length := SimpleGraph.Walk.length_reverse c'
      rw [hrev] at this; simp at this; omega
    | cons h2 p2 =>
      rename_i u2
      have hu2_ne : u2 ≠ m := h2.ne.symm
      have hu2_S : u2 ∈ S := by
        apply hsupp_sub u2
        have : u2 ∈ c'.reverse.support := by rw [hrev]; simp
        simpa [SimpleGraph.Walk.support_reverse] using this
      have hlt2 : ord u2 < ord m := by
        have hle := hmax u2 hu2_S
        have hne : ord u2 ≠ ord m := fun e => hu2_ne (hinj e)
        omega
      have hu12 : u1 = u2 := hord m u1 u2 h1.symm h2.symm hlt1 hlt2
      have hedg_nodup : c'.edges.Nodup := hc'.edges_nodup
      have hfirst : c'.edges.head? = some s(m, u1) := by rw [hc'eq]; rfl
      have hlast : c'.edges.getLast? = some s(u2, m) := by
        have hr : c'.reverse.edges = c'.edges.reverse := SimpleGraph.Walk.edges_reverse c'
        have hh : c'.reverse.edges.head? = some s(m, u2) := by rw [hrev]; rfl
        rw [hr, List.head?_reverse] at hh
        simpa [Sym2.eq_swap] using hh
      have hlen_e : 3 ≤ c'.edges.length := by simpa [SimpleGraph.Walk.length_edges] using hlen3
      cases he : c'.edges with
      | nil => rw [he] at hlen_e; simp at hlen_e
      | cons e0 es =>
        rw [he] at hedg_nodup hfirst hlast hlen_e
        simp only [List.head?_cons, Option.some.injEq] at hfirst
        cases hes : es with
        | nil => rw [hes] at hlen_e; simp at hlen_e
        | cons e1 es' =>
          rw [hes] at hedg_nodup hlast
          have hmem_last : s(u2, m) ∈ e1 :: es' := by
            have hne_nil : (e1 :: es') ≠ [] := List.cons_ne_nil _ _
            have hgl : (e0 :: e1 :: es').getLast? = (e1 :: es').getLast? := by simp
            rw [hgl] at hlast
            exact List.mem_of_getLast? hlast
          have hnot_mem : e0 ∉ e1 :: es' := (List.nodup_cons.mp hedg_nodup).1
          rw [hfirst, hu12, Sym2.eq_swap] at hnot_mem
          exact hnot_mem hmem_last

abbrev L : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3)]

/-- The graph of the statement. -/
def G : SimpleGraph (Fin 4) where
  Adj a b := (a.val, b.val) ∈ L ∨ (b.val, a.val) ∈ L
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable ((a.val, b.val) ∈ L ∨ (b.val, a.val) ∈ L))

theorem acyc : G.IsAcyclic :=
  isAcyclic_of_order G (fun v => v.val) (fun _ _ h => Fin.ext h) (by decide)

theorem cardE : G.edgeFinset.card = 3 := by decide

theorem cover : ∀ i j : Fin 4, G.Adj i j → i ∈ ({0} : Finset (Fin 4)) ∨ j ∈ ({0} : Finset (Fin 4)) := by
  decide

theorem low : ∀ T : Finset (Fin 4), (∀ i j : Fin 4, G.Adj i j → i ∈ T ∨ j ∈ T) → 1 ≤ T.card := by
  intro T hT
  have h1 := hT 0 1 (by decide)
  rcases h1 with h1 | h1 <;> exact Finset.card_pos.mpr ⟨_, h1⟩

theorem fn : (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3))
    = (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · intro h
    rcases h with ((h | h) | h)
    · exact ⟨0, 1, by decide, h.1, h.2⟩
    · exact ⟨0, 2, by decide, h.1, h.2⟩
    · exact ⟨0, 3, by decide, h.1, h.2⟩
  · rintro ⟨i, j, hm, hi, hj⟩
    rcases hm with hm | hm
    · simp only [L, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain rfl : i = 0 := Fin.ext h1
        obtain rfl : j = 1 := Fin.ext h2
        simp [hi, hj]
      · obtain rfl : i = 0 := Fin.ext h1
        obtain rfl : j = 2 := Fin.ext h2
        simp [hi, hj]
      · obtain rfl : i = 0 := Fin.ext h1
        obtain rfl : j = 3 := Fin.ext h2
        simp [hi, hj]
    · simp only [L, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain rfl : j = 0 := Fin.ext h1
        obtain rfl : i = 1 := Fin.ext h2
        simp [hi, hj]
      · obtain rfl : j = 0 := Fin.ext h1
        obtain rfl : i = 2 := Fin.ext h2
        simp [hi, hj]
      · obtain rfl : j = 0 := Fin.ext h1
        obtain rfl : i = 3 := Fin.ext h2
        simp [hi, hj]

end PEqualNP.Outside.L_meta_746

theorem PEqualNP.Outside.L_meta_746 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) s ↔ 3 ≤ s := by
  intro s
  rw [PEqualNP.Outside.L_meta_746.fn]
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 4 1 s PEqualNP.Outside.L_meta_746.G PEqualNP.Outside.L_meta_746.acyc ⟨0, 1, by decide⟩ PEqualNP.Outside.L_meta_746.low h
    rw [PEqualNP.Outside.L_meta_746.cardE] at this
    omega
  · intro hs
    have h := PEqualNP.MetaComplexity.L105 4 PEqualNP.Outside.L_meta_746.G ({0} : Finset (Fin 4)) ⟨0, 1, by decide⟩ PEqualNP.Outside.L_meta_746.cover
    rw [PEqualNP.Outside.L_meta_746.cardE] at h
    obtain ⟨C, hf, hsz, hev⟩ := h
    have hc : ({0} : Finset (Fin 4)).card = 1 := by decide
    rw [hc] at hsz
    exact ⟨C, hf, by omega, hev⟩
