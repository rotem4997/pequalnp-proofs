import Mathlib
import PEqualNP.Defs.MetaComplexityMinimal
import PEqualNP.Defs.Search

/-!
# Logic rows of the last-gate reduction

Proofs of rows L-meta-352, L-meta-376 and L-meta-388. Each is conditional: the circuit lower
bound and the cover upper bound come in as hypotheses, so the proofs are logic over the root
definitions of `SAT`, `HasCircuitSize`, `IsMinimalCircuit`, `NearMinimal`, `LgpYes` and `LgpNo`.
-/

namespace PEqualNP.MetaComplexity.Helpers.LogicRows

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

/-- Glue: a map correct on CNF codes and sending non-codes to YES sends the complement of SAT
to YES and SAT to NO. -/
theorem glue : ∀ r : List Bool → ℕ × PEqualNP.CircuitLowerBounds.Circuit, Function.Injective PEqualNP.Search.encodeCNF → (∀ φ : PEqualNP.Search.CNF, (¬ PEqualNP.Search.Satisfiable φ → PEqualNP.MetaComplexity.LgpYes (r (PEqualNP.Search.encodeCNF φ)).1 (r (PEqualNP.Search.encodeCNF φ)).2) ∧ (PEqualNP.Search.Satisfiable φ → PEqualNP.MetaComplexity.LgpNo (r (PEqualNP.Search.encodeCNF φ)).1 (r (PEqualNP.Search.encodeCNF φ)).2)) → (∀ x : List Bool, x ∉ Set.range PEqualNP.Search.encodeCNF → PEqualNP.MetaComplexity.LgpYes (r x).1 (r x).2) → ∀ x : List Bool, (x ∉ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpYes (r x).1 (r x).2) ∧ (x ∈ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpNo (r x).1 (r x).2) := by
  intro r _ hcode hnon x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · by_cases hr : x ∈ Set.range PEqualNP.Search.encodeCNF
    · obtain ⟨φ, rfl⟩ := hr
      exact (hcode φ).1 (fun hs => hx ⟨φ, rfl, hs⟩)
    · exact hnon x hr
  · obtain ⟨φ, rfl, hs⟩ := hx
    exact (hcode φ).2 hs

/-- The lower-bound hypothesis, with no extra inputs, applied to a fan-in-two circuit computing
the same function as `C`, where `C` computes the edge function. -/
theorem lower_apply
    (hLow : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s → A.card + G.edgeSet.ncard + k ≤ s + 1)
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hcyc : ∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length)
    (hdist : ∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length)
    (hedge : ∃ i j : Fin n, G.Adj i j)
    (hFun : PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)))
    (D : Circuit) (hD : FanInTwo D) (hDf : circuitFun n D = circuitFun n C)
    (k : ℕ) (hk : ∀ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) → k ≤ S.card) :
    G.edgeSet.ncard + k ≤ D.size + 1 := by
  have h := hLow n k D.size G ∅ hcyc hdist (by simp) (Or.inr hedge) hk ⟨D, hD, le_rfl, fun x => ?_⟩
  · simpa using h
  · have hx := congrFun hDf x
    rw [hFun] at hx
    simp only [circuitFun] at hx
    rw [hx]
    simp

/-- A minimal circuit for the edge function of size `|E| + |T| - 1` forces `T` to be a minimum
cover, given the cover upper bound. -/
theorem min_imp_le (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (T : Finset (Fin n))
    (hUp : ∀ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) → ∃ s : ℕ, s + 1 = G.edgeSet.ncard + S.card ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s)
    (hFun : PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)))
    (hSize : C.size + 1 = G.edgeSet.ncard + T.card)
    (hMin : IsMinimalCircuit n C) :
    ∀ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) → T.card ≤ S.card := by
  intro S hS
  obtain ⟨s, hs, D, hD, hDs, hDe⟩ := hUp S hS
  have hDf : circuitFun n D = circuitFun n C := by
    rw [hFun]; funext x; exact hDe x
  have := hMin.2 D hD hDf
  omega

/-- Row L-meta-376. -/
theorem row376 : (∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s → A.card + G.edgeSet.ncard + k ≤ s + 1) → ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (T : Finset (Fin n)), (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∃ i j : Fin n, G.Adj i j) → (∀ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) → ∃ s : ℕ, s + 1 = G.edgeSet.ncard + S.card ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size + 1 = G.edgeSet.ncard + T.card → (PEqualNP.MetaComplexity.IsMinimalCircuit n C ↔ ∀ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) → T.card ≤ S.card) := by
  intro hLow n G _ C T hcyc hdist hedge hUp _ hFan hFun hSize
  refine ⟨min_imp_le n G C T hUp hFun hSize, fun hle => ⟨hFan, fun D hD hDf => ?_⟩⟩
  have := lower_apply hLow n G C hcyc hdist hedge hFun D hD hDf T.card hle
  omega

/-- Row L-meta-388. -/
theorem row388 : (∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s → A.card + G.edgeSet.ncard + k ≤ s + 1) → ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (T : Finset (Fin n)), (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∃ i j : Fin n, G.Adj i j) → (∀ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) → ∃ s : ℕ, s + 1 = G.edgeSet.ncard + S.card ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → (∀ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) → T.card ≤ S.card + 1) → (∃ S : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ S ∨ j ∈ S) ∧ S.card < T.card) → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size + 1 = G.edgeSet.ncard + T.card → PEqualNP.MetaComplexity.LgpNo n C := by
  intro hLow n G _ C T hcyc hdist hedge hUp _ hNear hSmaller hFan hFun hSize
  obtain ⟨S₀, hS₀, hlt⟩ := hSmaller
  refine ⟨⟨hFan, fun D hD hDf => ?_⟩, fun hMin => ?_⟩
  · have := lower_apply hLow n G C hcyc hdist hedge hFun D hD hDf (T.card - 1)
      (fun S hS => by have := hNear S hS; omega)
    omega
  · have := min_imp_le n G C T hUp hFun hSize hMin S₀ hS₀
    omega

end PEqualNP.MetaComplexity.Helpers.LogicRows
