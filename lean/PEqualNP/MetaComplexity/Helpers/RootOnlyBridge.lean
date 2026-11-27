import Mathlib
import PEqualNP.Defs

/-!
# Root-only forms of walks, cycles and degrees

The definitions root imports only `Mathlib.Combinatorics.SimpleGraph.Basic` from the graph part
of the library, so `SimpleGraph.Walk`, `Walk.IsCycle`, `SimpleGraph.degree` and
`SimpleGraph.edgeFinset` do not exist under it. A recorded statement that needs them is written
with inline forms instead:

* a cycle of length `L` is a map `c : ℕ → V` with `3 ≤ L`, injective below `L`, and
  `G.Adj (c i) (c ((i + 1) % L))` for every `i < L`;
* a walk of length `L` from `u` to `v` is a map `w : ℕ → V` with `w 0 = u`, `w L = v` and
  `G.Adj (w i) (w (i + 1))` for every `i < L`;
* "degree at least three" is "three pairwise distinct neighbours";
* the number of edges is `G.edgeSet.ncard`.

This file proves each inline form equivalent to the library notion, and from them that the
root-only texts of rows L-meta-113 and L-meta-115 are equivalent to the filed texts.
-/

namespace PEqualNP.MetaComplexity.RootOnly

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The walk read off a map: `w 0 - w 1 - .. - w L`. -/
def walkOf (G : SimpleGraph V) :
    (w : ℕ → V) → (L : ℕ) → (∀ i : ℕ, i < L → G.Adj (w i) (w (i + 1))) → G.Walk (w 0) (w L)
  | _, 0, _ => Walk.nil
  | w, L + 1, h =>
      Walk.cons (h 0 (Nat.succ_pos L))
        (walkOf G (fun i => w (i + 1)) L (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)))

theorem length_walkOf (w : ℕ → V) (L : ℕ) (h : ∀ i : ℕ, i < L → G.Adj (w i) (w (i + 1))) :
    (walkOf G w L h).length = L := by
  induction L generalizing w with
  | zero => rfl
  | succ L ih => simp [walkOf, ih]

theorem getVert_walkOf (w : ℕ → V) (L : ℕ) (h : ∀ i : ℕ, i < L → G.Adj (w i) (w (i + 1))) :
    ∀ i : ℕ, i ≤ L → (walkOf G w L h).getVert i = w i := by
  induction L generalizing w with
  | zero => intro i hi; simp [walkOf, Nat.le_zero.mp hi]
  | succ L ih =>
    intro i hi
    cases i with
    | zero => simp [walkOf]
    | succ i =>
      simp only [walkOf, Walk.getVert_cons_succ]
      exact ih (fun j => w (j + 1)) _ i (by omega)

/-- Walks as maps. -/
theorem walk_iff (u v : V) (L : ℕ) :
    (∃ p : G.Walk u v, p.length = L) ↔
      ∃ w : ℕ → V, w 0 = u ∧ w L = v ∧ ∀ i : ℕ, i < L → G.Adj (w i) (w (i + 1)) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.getVert, p.getVert_zero, p.getVert_length, fun i hi => p.adj_getVert_succ hi⟩
  · rintro ⟨w, h0, hL, h⟩
    exact ⟨(walkOf G w L h).copy h0 hL, by simp [length_walkOf]⟩

/-- Cycles as maps. -/
theorem cycle_iff (L : ℕ) :
    (∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = L) ↔
      ∃ c : ℕ → V, 3 ≤ L ∧ (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) ∧
        ∀ i : ℕ, i < L → G.Adj (c i) (c ((i + 1) % L)) := by
  constructor
  · rintro ⟨v, p, hp, rfl⟩
    have h3 := hp.three_le_length
    refine ⟨p.getVert, h3, fun i j hi hj hij => hp.getVert_injOn' (by simp; omega)
      (by simp; omega) hij, fun i hi => ?_⟩
    have ha := p.adj_getVert_succ hi
    by_cases hlast : i + 1 = p.length
    · rw [hlast, Nat.mod_self, p.getVert_zero]
      rw [hlast, p.getVert_length] at ha
      exact ha
    · rw [Nat.mod_eq_of_lt (by omega)]
      exact ha
  · rintro ⟨c, h3, hinj, hadj⟩
    let w : ℕ → V := fun i => c (i % L)
    have hw : ∀ i : ℕ, i < L → G.Adj (w i) (w (i + 1)) := by
      intro i hi
      simp only [w, Nat.mod_eq_of_lt hi]
      exact hadj i hi
    have h0 : w 0 = c 0 := by simp [w]
    have hL : w L = c 0 := by simp [w]
    refine ⟨c 0, (walkOf G w L hw).copy h0 hL, ?_, by simp [length_walkOf]⟩
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, by simp [length_walkOf]; omega⟩
    rw [← Walk.IsPath.getVert_injOn_iff]
    intro i hi j hj hij
    simp only [Set.mem_ofPred_eq, Walk.length_tail, Walk.length_copy, length_walkOf] at hi hj
    simp only [Walk.getVert_tail, Walk.getVert_copy] at hij
    rw [getVert_walkOf w L hw _ (by omega), getVert_walkOf w L hw _ (by omega)] at hij
    simp only [w] at hij
    have := hinj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hij
    rcases Nat.lt_or_ge (i + 1) L with hi' | hi' <;>
      rcases Nat.lt_or_ge (j + 1) L with hj' | hj'
    · rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at this; omega
    · rw [Nat.mod_eq_of_lt hi', show j + 1 = L by omega, Nat.mod_self] at this; omega
    · rw [Nat.mod_eq_of_lt hj', show i + 1 = L by omega, Nat.mod_self] at this; omega
    · omega

/-- Degree at least three as three distinct neighbours. -/
theorem degree_iff [Fintype V] [DecidableRel G.Adj] (v : V) :
    3 ≤ G.degree v ↔
      ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj v a ∧ G.Adj v b ∧ G.Adj v c := by
  rw [← card_neighborFinset_eq_degree, show (3 ≤ _) ↔ 2 < _ from Iff.rfl, Finset.two_lt_card_iff]
  simp only [mem_neighborFinset]
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩; exact ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩
  · rintro ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩; exact ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩

theorem edge_card_eq [Fintype V] [DecidableRel G.Adj] : G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]

/-- The girth hypothesis, inline and library forms. -/
theorem cycleHyp_iff (K : ℕ) :
    (∀ (L : ℕ) (c : ℕ → V), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) →
        (∀ i : ℕ, i < L → G.Adj (c i) (c ((i + 1) % L))) → K ≤ L) ↔
      (∀ (v : V) (p : G.Walk v v), p.IsCycle → K ≤ p.length) := by
  constructor
  · intro h v p hp
    obtain ⟨c, h3, hi, ha⟩ := (cycle_iff p.length).mp ⟨v, p, hp, rfl⟩
    exact h _ c h3 hi ha
  · intro h L c h3 hi ha
    obtain ⟨v, p, hp, rfl⟩ := (cycle_iff L).mpr ⟨c, h3, hi, ha⟩
    exact h v p hp

/-- The distance hypothesis between distinct vertices of degree at least three. -/
theorem distHyp_iff [Fintype V] [DecidableRel G.Adj] (K : ℕ) :
    (∀ (u v : V), u ≠ v →
        (∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj u a ∧ G.Adj u b ∧ G.Adj u c) →
        (∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj v a ∧ G.Adj v b ∧ G.Adj v c) →
        ∀ (L : ℕ) (w : ℕ → V), w 0 = u → w L = v → (∀ i : ℕ, i < L → G.Adj (w i) (w (i + 1))) →
          K ≤ L) ↔
      (∀ (u v : V), u ≠ v → 3 ≤ G.degree u → 3 ≤ G.degree v → ∀ p : G.Walk u v,
          K ≤ p.length) := by
  simp only [degree_iff]
  constructor
  · intro h u v huv hu hv p
    obtain ⟨w, h0, hL, ha⟩ := (walk_iff u v p.length).mp ⟨p, rfl⟩
    exact h u v huv hu hv _ w h0 hL ha
  · intro h u v huv hu hv L w h0 hL ha
    obtain ⟨p, rfl⟩ := (walk_iff u v L).mpr ⟨w, h0, hL, ha⟩
    exact h u v huv hu hv p

theorem L113_iff :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (L : ℕ) (c : ℕ → Fin n), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) → (∀ i : ℕ, i < L → G.Adj (c i) (c ((i + 1) % L))) → 9 ≤ L) → (∀ (u v : Fin n), u ≠ v → (∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj u a ∧ G.Adj u b ∧ G.Adj u c) → (∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj v a ∧ G.Adj v b ∧ G.Adj v c) → ∀ (L : ℕ) (w : ℕ → Fin n), w 0 = u → w L = v → (∀ i : ℕ, i < L → G.Adj (w i) (w (i + 1))) → 9 ≤ L) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size ≤ C.size) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 9 ≤ p.length) → (∀ (u v : Fin n), u ≠ v → 3 ≤ G.degree u → 3 ≤ G.degree v → ∀ p : G.Walk u v, 9 ≤ p.length) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size ≤ C.size) := by
  refine forall_congr' fun n => forall_congr' fun G => forall_congr' fun _ => ?_
  rw [cycleHyp_iff, distHyp_iff]

theorem L115_iff :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (L : ℕ) (c : ℕ → Fin n), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) → (∀ i : ℕ, i < L → G.Adj (c i) (c ((i + 1) % L))) → 9 ≤ L) → (∀ (u v : Fin n), u ≠ v → (∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj u a ∧ G.Adj u b ∧ G.Adj u c) → (∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj v a ∧ G.Adj v b ∧ G.Adj v c) → ∀ (L : ℕ) (w : ℕ → Fin n), w 0 = u → w L = v → (∀ i : ℕ, i < L → G.Adj (w i) (w (i + 1))) → 7 ≤ L) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∃ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) ∧ G.edgeSet.ncard + T.card ≤ D.size + 1) ↔
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 9 ≤ p.length) → (∀ (u v : Fin n), u ≠ v → 3 ≤ G.degree u → 3 ≤ G.degree v → ∀ p : G.Walk u v, 7 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∃ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) ∧ G.edgeFinset.card + T.card ≤ D.size + 1) := by
  refine forall_congr' fun n => forall_congr' fun G => forall_congr' fun _ => ?_
  rw [cycleHyp_iff, distHyp_iff, edge_card_eq]

end PEqualNP.MetaComplexity.RootOnly
