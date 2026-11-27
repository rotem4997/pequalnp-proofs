import Mathlib
import PEqualNP.Library.Helpers.PeelableSanity

/-- The class form of the lower bound for the edge function with extra OR-variables on every
peelable graph, against circuits over AND, OR and NOT with every gate counted. -/
theorem PEqualNP.MetaComplexity.L532 : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), PEqualNP.Library.Peel.Peelable G → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s → A.card + G.edgeSet.ncard + k ≤ s + 1 := by
  intro n k s G A hP hinv _ hk hC
  have hb := PEqualNP.Library.Peel.Scratch.a1_peelable n G A hP hinv s hC
  obtain ⟨T, hT, hTc⟩ := PEqualNP.MetaComplexity.Loc.tau_attained G
  have := hk T hT
  unfold PEqualNP.MetaComplexity.Loc.Phi1 at hb
  omega
