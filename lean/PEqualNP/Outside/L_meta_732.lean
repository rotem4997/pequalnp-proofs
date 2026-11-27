import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_732

abbrev L1 : List (ℕ × ℕ) := [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4), (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)]

abbrev L2 : List (ℕ × ℕ) := [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7), (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]

abbrev Ep (u v : Fin 8) : Prop := (u.val, v.val) ∈ L1 ∨ (v.val, u.val) ∈ L1

abbrev Dp (u v : Fin 8) : Prop := (u.val, v.val) ∈ L2

theorem orient : ∀ u v : Fin 8, Ep u v ↔ (Dp u v ∨ Dp v u) := by decide

theorem asym : ∀ u v : Fin 8, Dp u v → ¬ Dp v u := by decide

abbrev P (K : Fin 8 → Bool) : Prop :=
  (∀ u v : Fin 8, K u = true → K v = true → ¬ Ep u v) →
    ∃ a b : Fin 8, Ep a b ∧ K a = false ∧ K b = false ∧
      ∀ k : Fin 8, K k = true → ¬ Dp a k ∧ ¬ Dp b k

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
instance decP (K : Fin 8 → Bool) : Decidable (P K) := by
  unfold P
  infer_instance

def allB (p : Bool → Bool) : Bool := p false && p true

theorem allB_spec {p : Bool → Bool} (h : allB p = true) (b : Bool) : p b = true := by
  simp only [allB, Bool.and_eq_true] at h
  cases b
  · exact h.1
  · exact h.2

def chk : Bool :=
  allB fun b0 => allB fun b1 => allB fun b2 => allB fun b3 => allB fun b4 => allB fun b5 =>
    allB fun b6 => allB fun b7 => decide (P ![b0, b1, b2, b3, b4, b5, b6, b7])

theorem chk_true : chk = true := by decide +kernel

theorem vec8 (K : Fin 8 → Bool) : K = ![K 0, K 1, K 2, K 3, K 4, K 5, K 6, K 7] := by
  funext i
  fin_cases i <;> rfl

theorem key (K : Fin 8 → Bool) : P K := by
  rw [vec8 K]
  exact of_decide_eq_true (allB_spec (allB_spec (allB_spec (allB_spec (allB_spec (allB_spec
    (allB_spec (allB_spec chk_true (K 0)) (K 1)) (K 2)) (K 3)) (K 4)) (K 5)) (K 6)) (K 7))

end PEqualNP.Outside.L_meta_732

theorem PEqualNP.Outside.L_meta_732 : ∀ (E D : Fin 8 → Fin 8 → Prop),
  (∀ u v, E u v ↔ ((u.val, v.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
      (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)] ∨
    (v.val, u.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
      (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)])) →
  (∀ u v, D u v ↔ (u.val, v.val) ∈ [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
      (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]) →
  (∀ u v, E u v ↔ (D u v ∨ D v u)) ∧ (∀ u v, D u v → ¬ D v u) ∧
  ∀ W K : Set (Fin 8),
    (∀ u ∈ W, ∀ v ∈ W, ¬ E u v) → Disjoint K W → (∀ u ∈ K, ∀ v ∈ K, ¬ E u v) →
    ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ D v k := by
  intro E D hE hD
  have hE' : ∀ u v, E u v ↔ PEqualNP.Outside.L_meta_732.Ep u v := hE
  have hD' : ∀ u v, D u v ↔ PEqualNP.Outside.L_meta_732.Dp u v := hD
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    rw [hE', hD', hD']
    exact PEqualNP.Outside.L_meta_732.orient u v
  · intro u v
    rw [hD', hD']
    exact PEqualNP.Outside.L_meta_732.asym u v
  · intro W K hW _ hK
    classical
    obtain ⟨a, b, hab, ha, hb, hk⟩ :=
      PEqualNP.Outside.L_meta_732.key (fun i => decide (i ∈ K)) (by
        intro u v hu hv
        rw [← hE']
        exact hK u (of_decide_eq_true hu) v (of_decide_eq_true hv))
    have haK : a ∉ K := of_decide_eq_false ha
    have hbK : b ∉ K := of_decide_eq_false hb
    by_cases haW : a ∈ W
    · have hbW : b ∉ W := fun h => hW a haW b h ((hE' a b).mpr hab)
      refine ⟨b, hbW, hbK, ?_⟩
      intro k hk'
      rw [hD']
      exact (hk k (decide_eq_true hk')).2
    · refine ⟨a, haW, haK, ?_⟩
      intro k hk'
      rw [hD']
      exact (hk k (decide_eq_true hk')).1
