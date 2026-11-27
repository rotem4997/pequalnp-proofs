import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- A cut of the order-3 plane bound by the number of junk AND gates (AND gates not below the
-- function) of a least top-form circuit.
-- normal: the checked normal form L_meta_4181. one: the checked L_meta_8725 (never exactly one
-- junk AND). zero: no junk AND at all. many: two or more junk ANDs, the open part.
-- The plane is written as: point a (wire a < 13) lies on line b - 13 (wire b >= 13) exactly
-- when (a + b) % 13 is 0, 1, 3 or 9; this is the edge list of the step.
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_972_5
    (normal : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → Monotone2 C → circuitFun n C = NestedCover.graphFun G ∅ →
      ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ D.size ≤ C.size)
    (one : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (colour : Fin n → Bool), (∀ u v : Fin n, G.Adj u v → colour u ≠ colour v) →
      NoFourCycle G → IsLeastAO G C → (junk G C).card ≠ 1)
    (zero : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      IsLeastAO G C → TopForm G C → junk G C = ∅ → 64 ≤ C.size)
    (many : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → 64 ≤ C.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 64 ≤ C.size := by
  intro C mono computes
  have table : ∀ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ↔
      (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) := by
    decide +kernel
  have four : ∀ a w1 : Fin 26,
      ((a.val < 13 ∧ 13 ≤ w1.val ∧ (a.val + w1.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
        (w1.val < 13 ∧ 13 ≤ a.val ∧ (w1.val + a.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) →
      ∀ b : Fin 26, a ≠ b →
      ((b.val < 13 ∧ 13 ≤ w1.val ∧ (b.val + w1.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
        (w1.val < 13 ∧ 13 ≤ b.val ∧ (w1.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) →
      ∀ w2 : Fin 26,
      ((a.val < 13 ∧ 13 ≤ w2.val ∧ (a.val + w2.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
        (w2.val < 13 ∧ 13 ≤ a.val ∧ (w2.val + a.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) →
      ((b.val < 13 ∧ 13 ≤ w2.val ∧ (b.val + w2.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
        (w2.val < 13 ∧ 13 ≤ b.val ∧ (w2.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) →
      w1 = w2 := by
    decide +kernel
  have key : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
      G = SimpleGraph.fromRel (fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) → 64 ≤ C.size := by
    intro G _ hG
    have adj : ∀ u v : Fin 26, G.Adj u v ↔
        ((u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
          (v.val < 13 ∧ 13 ≤ u.val ∧ (v.val + u.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) := by
      intro u v
      rw [hG, SimpleGraph.fromRel_adj]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rintro rfl
        rcases h with h | h <;> omega
    have hfun : circuitFun 26 C = NestedCover.graphFun G ∅ := by
      funext x
      have hx := computes x
      unfold circuitFun NestedCover.graphFun
      rw [Bool.eq_iff_iff, hx]
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_true_eq]
      constructor
      · rintro ⟨u, v, he, hu, hv⟩
        exact ⟨u, v, (adj u v).2 (Or.inl ((table u v).1 he)), hu, hv⟩
      · rintro ⟨u, v, h, hu, hv⟩
        rcases (adj u v).1 h with h | h
        · exact ⟨u, v, (table u v).2 h, hu, hv⟩
        · exact ⟨v, u, (table v u).2 h, hv, hu⟩
    have hne : G.edgeFinset.Nonempty := by
      refine ⟨s((0 : Fin 26), (13 : Fin 26)), ?_⟩
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact (adj 0 13).2 (Or.inl (by decide))
    obtain ⟨D, hleast, htop, hsize⟩ := normal 26 G C hne mono hfun
    have hcol : ∀ u v : Fin 26, G.Adj u v →
        (fun w : Fin 26 => decide (w.val < 13)) u ≠ (fun w : Fin 26 => decide (w.val < 13)) v := by
      intro u v h
      rcases (adj u v).1 h with h | h
      · simp only [ne_eq, decide_eq_decide]
        omega
      · simp only [ne_eq, decide_eq_decide]
        omega
    have hno : NoFourCycle G := by
      intro a b hab
      rw [Finset.card_le_one]
      intro w1 h1 w2 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact four a w1 ((adj a w1).1 h1.1) b hab ((adj b w1).1 h1.2) w2 ((adj a w2).1 h2.1)
        ((adj b w2).1 h2.2)
    have hone := one 26 G D (fun w : Fin 26 => decide (w.val < 13)) hcol hno hleast
    have hD : 64 ≤ D.size := by
      rcases Nat.lt_or_ge (junk G D).card 2 with hlt | hge
      · have h0 : (junk G D).card = 0 := by omega
        exact zero G D hG hleast htop (Finset.card_eq_zero.1 h0)
      · exact many G D hG hleast htop hge
    omega
  exact key _ rfl
