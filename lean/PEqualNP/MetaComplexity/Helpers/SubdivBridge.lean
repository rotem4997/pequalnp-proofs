import Mathlib
import PEqualNP.MetaComplexity.Helpers.SubdivDefs

/-!
# Bridge: the inline subdivision of the filed rows L-meta-281 .. 291 is `Subdiv.subdiv`

The filed rows (L-meta-281, 285, 286, 288, 289, 290, 291) state the 2k-fold subdivision inline as
`SimpleGraph.fromRel` of a relation `FRel` (written out below verbatim): `x` is the thread index
`m + 2k (u m + v) + i` of a live slot and `y` is its neighbour towards `u` (only for `i = 0`) or
towards `v`. L-meta-281 states the label as a triple sum. Proved here, for `k ≥ 1`:

* `graph_eq`: `SimpleGraph.fromRel (FRel k H) = subdiv k H` (same type `Fin (nS m k)`,
  `nS m k = m + 2 * k * m * m`, literally the filed vertex type);
* `pos_eq`: the filed triple sum equals `pos k H`.

At `k = 0` the two graphs differ (`FRel` has no thread index, so no edge; `subdiv 0 H` is `H`);
every filed row assumes `1 ≤ k`.
-/

namespace PEqualNP.MetaComplexity.Subdiv.Bridge

open PEqualNP.MetaComplexity.Subdiv

/-- The relation of the filed rows, verbatim. -/
def FRel {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) (x y : Fin (m + 2 * k * m * m)) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
    x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
    ((i.val = 0 ∧ y.val = u.val) ∨
      (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
      (i.val + 1 = 2 * k ∧ y.val = v.val))

theorem frel_to {m k : ℕ} {H : SimpleGraph (Fin m)} {x y : Fin (nS m k)} (h : FRel k H x y) :
    SubRel k H x y ∨ SubRel k H y x := by
  obtain ⟨u, v, huv, hadj, i, hx, h⟩ := h
  have hi := i.2
  rcases h with ⟨hi0, hy⟩ | ⟨hlt, hy⟩ | ⟨heq, hy⟩
  · refine Or.inr ⟨u, v, huv, hadj, ⟨0, by omega⟩, ?_, ?_⟩
    · show y.val = (if (0 : ℕ) = 0 then u.val else _)
      rw [if_pos rfl]; exact hy
    · show x.val = (if (0 : ℕ) = 2 * k then v.val else m + 2 * k * (u.val * m + v.val) + 0)
      rw [if_neg (by omega)]; omega
  · refine Or.inl ⟨u, v, huv, hadj, ⟨i.val + 1, by omega⟩, ?_, ?_⟩
    · show x.val = (if i.val + 1 = 0 then u.val else
        m + 2 * k * (u.val * m + v.val) + (i.val + 1) - 1)
      rw [if_neg (by omega)]; omega
    · show y.val = (if i.val + 1 = 2 * k then v.val else
        m + 2 * k * (u.val * m + v.val) + (i.val + 1))
      rw [if_neg (by omega)]; omega
  · refine Or.inl ⟨u, v, huv, hadj, ⟨i.val + 1, by omega⟩, ?_, ?_⟩
    · show x.val = (if i.val + 1 = 0 then u.val else
        m + 2 * k * (u.val * m + v.val) + (i.val + 1) - 1)
      rw [if_neg (by omega)]; omega
    · show y.val = (if i.val + 1 = 2 * k then v.val else
        m + 2 * k * (u.val * m + v.val) + (i.val + 1))
      rw [if_pos heq]; exact hy

theorem subrel_to {m k : ℕ} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k) {x y : Fin (nS m k)}
    (h : SubRel k H x y) : FRel k H x y ∨ FRel k H y x := by
  obtain ⟨u, v, huv, hadj, p, hx, hy⟩ := h
  have hp := p.2
  by_cases hp0 : p.val = 0
  · rw [if_pos hp0] at hx
    rw [if_neg (by omega)] at hy
    refine Or.inr ⟨u, v, huv, hadj, ⟨0, by omega⟩, ?_, Or.inl ⟨rfl, hx⟩⟩
    show y.val = m + 2 * k * (u.val * m + v.val) + 0
    omega
  · rw [if_neg hp0] at hx
    refine Or.inl ⟨u, v, huv, hadj, ⟨p.val - 1, by omega⟩, ?_, ?_⟩
    · show x.val = m + 2 * k * (u.val * m + v.val) + (p.val - 1)
      omega
    · by_cases hp2 : p.val = 2 * k
      · rw [if_pos hp2] at hy
        exact Or.inr (Or.inr ⟨by show p.val - 1 + 1 = 2 * k; omega, hy⟩)
      · rw [if_neg hp2] at hy
        exact Or.inr (Or.inl ⟨by show p.val - 1 + 1 < 2 * k; omega,
          by show y.val = m + 2 * k * (u.val * m + v.val) + (p.val - 1) + 1; omega⟩)

/-- The filed inline graph is `subdiv k H` (`k ≥ 1`). -/
theorem graph_eq {m k : ℕ} (H : SimpleGraph (Fin m)) (hk : 1 ≤ k) :
    SimpleGraph.fromRel (FRel k H) = subdiv k H := by
  ext x y
  show x ≠ y ∧ (FRel k H x y ∨ FRel k H y x) ↔ x ≠ y ∧ (SubRel k H x y ∨ SubRel k H y x)
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, frel_to h⟩
    · exact ⟨hne, (frel_to h).symm⟩
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, subrel_to hk h⟩
    · exact ⟨hne, (subrel_to hk h).symm⟩

/-- The filed triple-sum label is `pos k H`. -/
theorem pos_eq {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (j : Fin (nS m k)) :
    (∑ u : Fin m, ∑ v : Fin m, ∑ i : Fin (2 * k),
      if u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val then i.val + 1 else 0)
      = pos k H j := by
  unfold pos
  split_ifs with h
  · obtain ⟨u0, v0, i0, huv, hadj, hj⟩ := h
    have hu : ∀ u : Fin m, u ≠ u0 → (∑ v : Fin m, ∑ i : Fin (2 * k),
        if u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val
        then i.val + 1 else 0) = 0 := by
      intro u hne
      refine Finset.sum_eq_zero (fun v _ => Finset.sum_eq_zero (fun i _ => if_neg ?_))
      rintro ⟨-, -, h'⟩
      exact hne (thr_inj i.2 i0.2 (h'.symm.trans hj)).1
    have hv : ∀ v : Fin m, v ≠ v0 → (∑ i : Fin (2 * k),
        if u0 < v ∧ H.Adj u0 v ∧ j.val = m + 2 * k * (u0.val * m + v.val) + i.val
        then i.val + 1 else 0) = 0 := by
      intro v hne
      refine Finset.sum_eq_zero (fun i _ => if_neg ?_)
      rintro ⟨-, -, h'⟩
      exact hne (thr_inj i.2 i0.2 (h'.symm.trans hj)).2.1
    have hi : ∀ i : Fin (2 * k), i ≠ i0 →
        (if u0 < v0 ∧ H.Adj u0 v0 ∧ j.val = m + 2 * k * (u0.val * m + v0.val) + i.val
          then i.val + 1 else 0) = 0 := by
      intro i hne
      refine if_neg ?_
      rintro ⟨-, -, h'⟩
      exact hne (Fin.ext (thr_inj i.2 i0.2 (h'.symm.trans hj)).2.2)
    rw [Finset.sum_eq_single u0 (fun u _ hne => hu u hne) (fun h => absurd (Finset.mem_univ _) h),
      Finset.sum_eq_single v0 (fun v _ hne => hv v hne) (fun h => absurd (Finset.mem_univ _) h),
      Finset.sum_eq_single i0 (fun i _ hne => hi i hne) (fun h => absurd (Finset.mem_univ _) h),
      if_pos ⟨huv, hadj, hj⟩]
    have e : j.val - m = i0.val + 2 * k * (u0.val * m + v0.val) := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i0.2]
  · refine Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ =>
      Finset.sum_eq_zero (fun i _ => if_neg ?_)))
    rintro ⟨huv, hadj, hj⟩
    exact h ⟨u, v, i, huv, hadj, hj⟩

end PEqualNP.MetaComplexity.Subdiv.Bridge
