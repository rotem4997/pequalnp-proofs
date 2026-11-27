import Mathlib
import PEqualNP.MetaComplexity.L204
import PEqualNP.MetaComplexity.Helpers.L559Up

/-- The conditional exact-additivity row: from the statement of the outside row on the least
size of (edge function with extra variables) OR g, the least size of the OR is the least size of
the edge function with extra variables plus the least size of g plus one. -/
theorem PEqualNP.MetaComplexity.L559 : (∀ (n k c t s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool), (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ y y' : Fin k → Bool, g y ≠ g y') → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize k g r ↔ c ≤ r) → (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) → (PEqualNP.MetaComplexity.HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool => decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) || g (fun j : Fin k => x (Fin.natAdd n j))) s ↔ A.card + G.edgeFinset.card + t + c ≤ s)) → (∀ (n k c d s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (g : (Fin k → Bool) → Bool), (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) → (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) → (∃ y y' : Fin k → Bool, g y ≠ g y') → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize k g r ↔ c ≤ r) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) r ↔ d ≤ r) → (PEqualNP.MetaComplexity.HasCircuitSize (n + k) (fun x : Fin (n + k) → Bool => decide ((∃ a ∈ A, x (Fin.castAdd k a) = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x (Fin.castAdd k u) = true ∧ x (Fin.castAdd k v) = true) || g (fun j : Fin k => x (Fin.natAdd n j))) s ↔ d + c + 1 ≤ s)) := by
  intro H n k c d s G _ A g hcyc hhub hA hne hg hc hd
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℕ, (∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧
      S.card = t) ∧ (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) →
      t ≤ S.card) := by
    classical
    have hex : ∃ m : ℕ, ∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧
        S.card = m := ⟨_, Finset.univ, fun u _ _ => Or.inl (Finset.mem_univ u), rfl⟩
    exact ⟨Nat.find hex, Nat.find_spec hex, fun S hS => Nat.find_min' hex ⟨S, hS, rfl⟩⟩
  have hH := H n k c t s G A g hcyc hhub hA hne hg hc ht1 ht2
  -- lower half: the checked L-meta-204 at a circuit of size d
  have hFd := (hd d).2 le_rfl
  have hFd' : PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool =>
      @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
        (Classical.propDecidable _)) d := by
    convert hFd using 3
  have hlow := PEqualNP.MetaComplexity.L204 n t d G A hcyc hhub
    (fun i j hij hi => hA i hi j hij) hne ht2 hFd'
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] at hlow
  -- upper half: the OR of A and the cover circuit
  obtain ⟨S0, hS0, hS0c⟩ := ht1
  obtain ⟨s0, hs0, hb⟩ :=
    PEqualNP.MetaComplexity.Helpers.L559Up.fp_bld_graph n G A S0 hne hS0
  have hup := (hd s0).1 (PEqualNP.MetaComplexity.Helpers.L559Up.bld_hasCircuitSize hb)
  rw [hH]
  omega
