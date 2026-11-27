import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves
open PEqualNP.MetaComplexity.NestedCover

-- The cofactor drops the five incident edges. The two cubic stars restore
-- these edges with five internal gates and two OR gates.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4859_28
  (cofactor : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (D : Circuit) (m : ℕ) (f g : Fin m ↪ Fin n),
    Odd m →
    (∀ i, G.Adj (f i) (g i) ∧ g i ∉ Set.range f) →
    (∀ i j, G.Adj (f i) (f j) ↔ (i.val + 1) % m = j.val ∨ (j.val + 1) % m = i.val) →
    (∀ v, (G.neighborSet v).ncard = if v ∈ A then 0 else 3) →
    7 ≤ G.egirth → IsMinimalCircuit n D → circuitFun n D = graphFun G A →
    ∃ i j : Fin m, G.Adj (f i) (f j) ∧ ∃ B : Circuit,
      FanInTwo B ∧ B.size + 7 ≤ D.size ∧ B.output < n + B.size ∧
      ∀ x : Fin n → Bool, circuitFun n B x =
        graphFun G A (Function.update (Function.update x (f i) false) (f j) false))
  (restore : ∀ (n : ℕ) (B : Circuit) (u v a b c d : Fin n), FanInTwo B → B.output < n + B.size →
    ∃ C : ℕ → Circuit, FanInTwo (C 0) ∧ (C 0).size = B.size + 7 ∧
      (∀ x : Fin n → Bool, circuitFun n (C 0) x =
        ((circuitFun n B x || (x u && ((x v || x a) || x b))) || (x v && (x c || x d)))) ∧
      ∀ i < 7, ∃ m p : ℕ, m < (C i).size ∧ (p < n + m ∨ n + (C i).size ≤ p) ∧
        C (i + 1) = eraseGate n (C i) m p ∧
        ((∀ x : Fin n → Bool,
          let w := (C i).wires (List.ofFn (Function.update (Function.update x u false) v false))
          w.getD (n + m) false = w.getD p false) ∨
          ((C i).output ≠ n + m ∧ ∀ g ∈ (C i).gates.drop (m + 1), n + m ∉ g.inputs))) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 x8 : Fin x6 ↪ Fin x1),   Odd x6 →     (∀ (x10 : Fin x6), x2.Adj (x7 x10) (x8 x10) ∧ x8 x10 ∉ Set.range ⇑x7) →       (∀ (x11 x12 : Fin x6), x2.Adj (x7 x11) (x7 x12) ↔ (↑x11 + (1 : ℕ)) % x6 = ↑x12 ∨ (↑x12 + (1 : ℕ)) % x6 = ↑x11) →         (∀ (x12 : Fin x1), (x2.neighborSet x12).ncard = if x12 ∈ x4 then (0 : ℕ) else (3 : ℕ)) →           (7 : ℕ∞) ≤ x2.egirth →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →                 ∃ (x16 : Fin x6) (x17 : Fin x6),                   x2.Adj (x7 x16) (x7 x17) ∧                     ∃ (x18 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo (x18 (0 : ℕ)) ∧                         (x18 (0 : ℕ)).size ≤ x5.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 (x18 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x5 ∧                             ∀ x19 < (7 : ℕ),                               ∃ (x21 : ℕ) (x22 : ℕ),                                 x21 < (x18 x19).size ∧                                   (x22 < x1 + x21 ∨ x1 + (x18 x19).size ≤ x22) ∧                                     x18 (x19 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x18 x19) x21 x22 ∧                                       ((∀ (x23 : Fin x1 → Bool),                                           have x24 : List Bool := (x18 x19).wires (List.ofFn (Function.update (Function.update x23 (x7 x16) Bool.false) (x7 x17) Bool.false));                                           x24.getD (x1 + x21) Bool.false = x24.getD x22 Bool.false) ∨                                         (x18 x19).output ≠ x1 + x21 ∧ ∀ x23 ∈ List.drop (x21 + (1 : ℕ)) (x18 x19).gates, x1 + x21 ∉ x23.inputs) := by
  intro n G dec A D m f g odd spokes cycle degree girth minimal computes
  obtain ⟨i, j, edge, B, fan, bound, output, specB⟩ :=
    cofactor n G A D m f g odd spokes cycle degree girth minimal computes
  let u := f i
  let v := f j
  have uv : G.Adj u v := edge
  have nonIso {z w : Fin n} (h : G.Adj z w) : z ∉ A := by
    intro hz
    have zero : (G.neighborSet z).ncard = 0 := by simpa only [hz, ite_true] using degree z
    have empty : G.neighborSet z = ∅ := (Set.ncard_eq_zero (s := G.neighborSet z)).mp zero
    have : w ∈ G.neighborSet z := h
    rw [empty] at this
    exact (Set.notMem_empty w) this
  have neighbors (z w : Fin n) (h : G.Adj z w) :
      ∃ a b : Fin n, ∀ k, G.Adj z k ↔ k = w ∨ k = a ∨ k = b := by
    have three : (G.neighborSet z).ncard = 3 := by
      simpa only [nonIso h, ite_false] using degree z
    have two : (G.neighborSet z \ {w}).ncard = 2 := by
      rw [Set.ncard_sdiff_singleton_of_mem (show w ∈ G.neighborSet z from h), three]
    obtain ⟨a, b, _, rest⟩ := Set.ncard_eq_two.mp two
    refine ⟨a, b, ?_⟩
    intro k
    by_cases hk : k = w
    · subst k
      simp [h]
    · have same : k ∈ G.neighborSet z \ {w} ↔ G.Adj z k := by simp [hk]
      rw [← same, rest]
      simp [hk]
  obtain ⟨a, b, nbrU⟩ := neighbors u v uv
  obtain ⟨c, d, nbrV⟩ := neighbors v u uv.symm
  obtain ⟨C, hC, hSize, hEval, chain⟩ := restore n B u v a b c d fan output
  have split (x : Fin n → Bool) :
      ((circuitFun n B x || (x u && ((x v || x a) || x b))) || (x v && (x c || x d))) =
        graphFun G A x := by
    let y := Function.update (Function.update x u false) v false
    have yu : y u = false := by
      exact (Function.update_of_ne uv.ne _ _).trans (Function.update_self _ _ _)
    have yv : y v = false := Function.update_self _ _ _
    have other {q : Fin n} (hu : q ≠ u) (hv : q ≠ v) : y q = x q := by
      exact (Function.update_of_ne hv _ _).trans (Function.update_of_ne hu _ _)
    have ytrue {q : Fin n} (hq : y q = true) : x q = true := by
      have hu : q ≠ u := fun h => by subst q; simp [yu] at hq
      have hv : q ≠ v := fun h => by subst q; simp [yv] at hq
      exact (other hu hv).symm.trans hq
    have free {q : Fin n} (hq : q ∈ A) : y q = x q :=
      other (fun h => nonIso uv (h ▸ hq)) (fun h => nonIso uv.symm (h ▸ hq))
    have incidentU {q : Fin n} (h : G.Adj u q) (hq : x q = true) :
        (x v = true ∨ x a = true) ∨ x b = true := by
      rcases (nbrU q).mp h with rfl | rfl | rfl
      · exact Or.inl (Or.inl hq)
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq
    have incidentV {q : Fin n} (hqU : q ≠ u) (h : G.Adj v q) (hq : x q = true) :
        x c = true ∨ x d = true := by
      rcases (nbrV q).mp h with ht | rfl | rfl
      · exact False.elim (hqU ht)
      · exact Or.inl hq
      · exact Or.inr hq
    rw [show circuitFun n B x = graphFun G A y from specB x]
    apply Bool.eq_iff_iff.mpr
    change (((decide (∃ q ∈ A, y q = true) ||
      decide (∃ q r, G.Adj q r ∧ y q = true ∧ y r = true)) ||
      (x u && ((x v || x a) || x b))) || (x v && (x c || x d))) = true ↔
      (decide (∃ q ∈ A, x q = true) ||
        decide (∃ q r, G.Adj q r ∧ x q = true ∧ x r = true)) = true
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (((hA | edgeY) | starU) | starV)
      · obtain ⟨q, hq, val⟩ := hA
        exact Or.inl ⟨q, hq, ytrue val⟩
      · obtain ⟨q, r, adj, hq, hr⟩ := edgeY
        exact Or.inr ⟨q, r, adj, ytrue hq, ytrue hr⟩
      · obtain ⟨hu, (hv | ha) | hb⟩ := starU
        · exact Or.inr ⟨u, v, uv, hu, hv⟩
        · exact Or.inr ⟨u, a, (nbrU a).mpr (Or.inr (Or.inl rfl)), hu, ha⟩
        · exact Or.inr ⟨u, b, (nbrU b).mpr (Or.inr (Or.inr rfl)), hu, hb⟩
      · obtain ⟨hv, hc | hd⟩ := starV
        · exact Or.inr ⟨v, c, (nbrV c).mpr (Or.inr (Or.inl rfl)), hv, hc⟩
        · exact Or.inr ⟨v, d, (nbrV d).mpr (Or.inr (Or.inr rfl)), hv, hd⟩
    · rintro (hA | edgeX)
      · obtain ⟨q, hq, val⟩ := hA
        exact Or.inl (Or.inl (Or.inl ⟨q, hq, (free hq).trans val⟩))
      · obtain ⟨q, r, adj, hq, hr⟩ := edgeX
        by_cases huq : q = u
        · subst q
          exact Or.inl (Or.inr ⟨hq, incidentU adj hr⟩)
        by_cases hur : r = u
        · subst r
          exact Or.inl (Or.inr ⟨hr, incidentU adj.symm hq⟩)
        by_cases hvq : q = v
        · subst q
          exact Or.inr ⟨hq, incidentV hur adj hr⟩
        by_cases hvr : r = v
        · subst r
          exact Or.inr ⟨hr, incidentV huq adj.symm hq⟩
        exact Or.inl (Or.inl (Or.inr ⟨q, r, adj,
          (other huq hvq).trans hq, (other hur hvr).trans hr⟩))
  refine ⟨i, j, edge, C, hC, hSize.le.trans bound, ?_, chain⟩
  funext x
  exact (hEval x).trans ((split x).trans (congrFun computes x).symm)
