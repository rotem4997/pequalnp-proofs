import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2636_751
    (upper : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 x5 : Finset (Fin x1)) (x6 : Fin x1), (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → x5 ⊆ x4ᶜ → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∈ x5 ∨ x11 ∈ x5) → x6 ∈ x5 → ∃ (x12 : ℕ), x12 + (5 : ℕ) ≤ x4.card + x2.edgeFinset.card + x5.card ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x13 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (Function.update x13 x6 Bool.false)) x12)
    (lower : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v : Fin n, G.Adj u v → u ∉ A) → (∃ u v : Fin n, G.Adj u v) →
      ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (PEqualNP.MetaComplexity.NestedCover.graphFun G A) s →
      ∃ T : Finset (Fin n), T ⊆ Aᶜ ∧ (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        A.card + G.edgeFinset.card + T.card ≤ s + 1) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x3) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → (∀ (x9 : Fin x1 → Bool), x4 x9 = Bool.true ↔ (∃ x10 ∈ x3, x9 x10 = Bool.true) ∨ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x10 → ∃ x12 ∉ x3, ∃ (x13 : ℕ), x13 + (4 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x14 : Fin x1 → Bool) => x4 (Function.update x14 x12 Bool.false)) x13 := by
  classical
  intro n G A f deg girth iso edges spec s has
  have eq : f = PEqualNP.MetaComplexity.NestedCover.graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (f x = true) ↔
      (decide (∃ a ∈ A, x a = true) || decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) = true
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using spec x
  subst eq
  obtain ⟨T, sub, cover, budget⟩ := lower n G A deg girth iso edges s has
  obtain ⟨u, v, e⟩ := edges
  have hz : ∃ z, z ∈ T := by
    rcases cover u v e with h | h
    · exact ⟨u, h⟩
    · exact ⟨v, h⟩
  obtain ⟨z, zT⟩ := hz
  obtain ⟨t, ht, build⟩ := upper n G A T z deg iso sub cover zT
  exact ⟨z, Finset.mem_compl.mp (sub zT), t, by omega, build⟩
