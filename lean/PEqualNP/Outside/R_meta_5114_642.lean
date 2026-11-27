import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5114_642
    (elim : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (p : Fin n) (s : ℕ),
      (∃ x, f (Function.update x p (!x p)) ≠ f x) →
      (∃ x y, f (Function.update x p false) ≠ f (Function.update y p false)) →
      PEqualNP.MetaComplexity.HasCircuitSize n f s →
      ∃ t, t + 1 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n
        (fun x => f (Function.update x p false)) t)
    (core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool),
      G.Colorable 2 →
      (∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∃ u v, G.Adj u v) →
      (∀ x, f x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      ∀ s, PEqualNP.MetaComplexity.HasCircuitSize n f s →
        G.edgeSet.ncard + G.support.ncard / 2 ≤ s + 1) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → x3.card + x2.edgeSet.ncard + (Finset.univ \ x3).card / (2 : ℕ) ≤ x11 + (1 : ℕ) := by
  classical
  intro n G A f color degree girth isolated edge spec s small
  have strip : ∀ (B : Finset (Fin n)) (h : (Fin n → Bool) → Bool) (r : ℕ),
      (∀ u v, G.Adj u v → u ∉ B) →
      (∀ x, h x = true ↔ (∃ a ∈ B, x a = true) ∨
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      PEqualNP.MetaComplexity.HasCircuitSize n h r →
      ∃ (t : ℕ) (g : (Fin n → Bool) → Bool), t + B.card ≤ r ∧
        PEqualNP.MetaComplexity.HasCircuitSize n g t ∧
        (∀ x, g x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
    intro B
    induction B using Finset.induction_on with
    | empty =>
      intro h r _ hspec hsmall
      exact ⟨r, h, by simp, hsmall, by simpa using hspec⟩
    | @insert a B ha ih =>
      intro h r hiso hspec hsmall
      have hzero : h (fun _ => false) = false := by
        have hn : ¬ h (fun _ => false) = true := by
          rw [hspec]
          simp
        cases he : h (fun _ => false) <;> simp_all
      have hdep : ∃ x, h (Function.update x a (!x a)) ≠ h x := by
        refine ⟨fun _ => false, ?_⟩
        have ht : h (Function.update (fun _ => false) a true) = true :=
          (hspec _).mpr (Or.inl ⟨a, by simp, by simp⟩)
        simpa [hzero, ht]
      have hnc : ∃ x y, h (Function.update x a false) ≠
          h (Function.update y a false) := by
        obtain ⟨u, v, huv⟩ := edge
        have hua : u ≠ a := fun e => hiso u v huv (by simp [e])
        have hva : v ≠ a := fun e => hiso v u huv.symm (by simp [e])
        refine ⟨fun _ => false, fun _ => true, ?_⟩
        have hz : Function.update (fun _ : Fin n => false) a false = (fun _ => false) := by
          funext i
          by_cases hi : i = a <;> simp [hi, Function.update_of_ne]
        have ht : h (Function.update (fun _ => true) a false) = true :=
          (hspec _).mpr (Or.inr ⟨u, v, huv, by simp [Function.update_of_ne hua],
            by simp [Function.update_of_ne hva]⟩)
        rw [hz, hzero, ht]
        decide
      obtain ⟨r', hr', hsmall'⟩ := elim n h a r hdep hnc hsmall
      have hiso' : ∀ u v, G.Adj u v → u ∉ B :=
        fun u v huv hu => hiso u v huv (Finset.mem_insert_of_mem hu)
      have hspec' : ∀ x, h (Function.update x a false) = true ↔
          (∃ b ∈ B, x b = true) ∨ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
        intro x
        rw [hspec]
        apply or_congr
        · constructor
          · rintro ⟨b, hb, hx⟩
            have hba : b ≠ a := by rintro rfl; simp at hx
            exact ⟨b, (Finset.mem_insert.mp hb).resolve_left hba,
              by simpa [Function.update_of_ne hba] using hx⟩
          · rintro ⟨b, hb, hx⟩
            have hba : b ≠ a := fun e => ha (e ▸ hb)
            exact ⟨b, Finset.mem_insert_of_mem hb, by simpa [Function.update_of_ne hba] using hx⟩
        · constructor
          · rintro ⟨u, v, huv, hu, hv⟩
            have hua : u ≠ a := fun e => hiso u v huv (by simp [e])
            have hva : v ≠ a := fun e => hiso v u huv.symm (by simp [e])
            exact ⟨u, v, huv, by simpa [Function.update_of_ne hua] using hu,
              by simpa [Function.update_of_ne hva] using hv⟩
          · rintro ⟨u, v, huv, hu, hv⟩
            have hua : u ≠ a := fun e => hiso u v huv (by simp [e])
            have hva : v ≠ a := fun e => hiso v u huv.symm (by simp [e])
            exact ⟨u, v, huv, by simpa [Function.update_of_ne hua] using hu,
              by simpa [Function.update_of_ne hva] using hv⟩
      obtain ⟨t, g, ht, hg, hgspec⟩ := ih _ r' hiso' hspec' hsmall'
      refine ⟨t, g, ?_, hg, hgspec⟩
      rw [Finset.card_insert_of_notMem ha]
      omega
  obtain ⟨t, g, ht, hg, hgspec⟩ := strip A f s isolated spec small
  have hdegree : ∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3 := by
    intro v
    by_cases hv : v ∈ A
    · left
      have hempty : G.neighborSet v = ∅ := by
        ext w
        simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
        exact fun h => isolated v w h hv
      simp [hempty]
    · exact Or.inr (degree v hv)
  have support : G.support = (↑(Finset.univ \ A) : Set (Fin n)) := by
    ext v
    simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and,
      SimpleGraph.mem_support]
    constructor
    · rintro ⟨w, h⟩
      exact isolated v w h
    · intro hv
      have hd : 0 < G.degree v := by
        rw [← G.ncard_neighborSet, degree v hv]
        decide
      exact (G.degree_pos_iff_exists_adj v).mp hd
  have hc := core n G g color hdegree girth edge hgspec t hg
  rw [support, Set.ncard_coe_finset] at hc
  omega
