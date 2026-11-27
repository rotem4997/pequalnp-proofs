import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4123_835
(first : ∀ (n m : ℕ) (H : SimpleGraph (Fin n)) (_z : Fin n) (f : (Fin n → Bool) → Bool),
  (∀ u (w : H.Walk u u), w.IsCycle → 5 ≤ w.length) → (∀ x, f x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true) →
  (∃ (D : Finset (Fin n)) (h : (Fin n → Bool) → Bool) (k : ℕ)
    (A B : Fin k → (Fin n → Bool) → Bool) (p : Fin k → ℕ) (b : Fin k → Bool)
    (F : Fin k → Finset (Fin n)),
    IsLiteralPartition n h k A B p b ∧
    (∀ x, h x = f x ∨ h x = true ∧ ∃ u ∈ D, ∃ w ∈ D, u ≠ w ∧ x u = true ∧ x w = true) ∧
    (∀ j, b j = false → ∃ v ∈ D, p j = v.val) ∧
    (∀ u ∈ D, ∀ v ∈ D, u ≠ v → ∀ w : H.Walk u v, 3 < w.length) ∧
    (∀ j, b j = true → ∀ v ∈ D, v ∉ F j → ∀ a c, H.Adj a c →
      let x := fun i : Fin n => i == a || i == c
      A j (Function.update x v true) = A j x) ∧
    (∑ j : {j : Fin k // b j = true}, (1 + (F j.val).card)) ≤ m) → ∃ (R S : Fin m → Fin n → Fin n → Prop) (label : Fin m → Fin n),
    ∀ a b c d, H.Adj a b → c = d ∨ H.Adj c d →
      (∃! j, R j a b ∧ S j c d) ∧
      ∀ j, R j a b → S j c d → (label j = a ∨ label j = b) ∧
        ¬ ((H.Adj c (label j) ∨ H.Adj d (label j)) ∧ label j ≠ c ∧ label j ≠ d))
(remaining : ∀ (n t : ℕ) (G H : SimpleGraph (Fin n)) (z : Fin n) (f : (Fin n → Bool) → Bool),
  (∀ u, (G.neighborSet u).ncard = 0 ∨ (G.neighborSet u).ncard = 3) →
  (G.neighborSet z).ncard = 3 → (∀ u (w : G.Walk u u), w.IsCycle → 7 ≤ w.length) →
  H = G.deleteEdges (G.incidenceSet z) → (∀ x, f x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true) →
  HasCircuitSize n f t → ∃ (D : Finset (Fin n)) (h : (Fin n → Bool) → Bool) (k : ℕ)
    (A B : Fin k → (Fin n → Bool) → Bool) (p : Fin k → ℕ) (b : Fin k → Bool)
    (F : Fin k → Finset (Fin n)),
    IsLiteralPartition n h k A B p b ∧
    (∀ x, h x = f x ∨ h x = true ∧ ∃ u ∈ D, ∃ w ∈ D, u ≠ w ∧ x u = true ∧ x w = true) ∧
    (∀ j, b j = false → ∃ v ∈ D, p j = v.val) ∧
    (∀ u ∈ D, ∀ v ∈ D, u ≠ v → ∀ w : H.Walk u v, 3 < w.length) ∧
    (∀ j, b j = true → ∀ v ∈ D, v ∉ F j → ∀ a c, H.Adj a c →
      let x := fun i : Fin n => i == a || i == c
      A j (Function.update x v true) = A j x) ∧
    (∑ j : {j : Fin k // b j = true}, (1 + (F j.val).card)) ≤ t + 1) :
∀ (x1 x2 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) (x5 : Fin x1) (x6 : (Fin x1 → Bool) → Bool), (∀ (x7 : Fin x1), (x3.neighborSet x7).ncard = (0 : ℕ) ∨ (x3.neighborSet x7).ncard = (3 : ℕ)) → (x3.neighborSet x5).ncard = (3 : ℕ) → (∀ (x9 : Fin x1) (x10 : x3.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → x4 = x3.deleteEdges (x3.incidenceSet x5) → (∀ (x11 : Fin x1 → Bool), x6 x11 = Bool.true ↔ ∃ (x12 : Fin x1) (x13 : Fin x1), x4.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x2 → ∃ (x13 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x14 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop) (x15 : Fin (x2 + (1 : ℕ)) → Fin x1), ∀ (x16 x17 x18 x19 : Fin x1), x4.Adj x16 x17 → x18 = x19 ∨ x4.Adj x18 x19 → (∃! x22 : Fin (x2 + (1 : ℕ)), x13 x22 x16 x17 ∧ x14 x22 x18 x19) ∧ ∀ (x22 : Fin (x2 + (1 : ℕ))), x13 x22 x16 x17 → x14 x22 x18 x19 → (x15 x22 = x16 ∨ x15 x22 = x17) ∧ ¬((x4.Adj x18 (x15 x22) ∨ x4.Adj x19 (x15 x22)) ∧ x15 x22 ≠ x18 ∧ x15 x22 ≠ x19) := by
  intro n t G H z f deg dz girth deleted spec size
  classical
  have sub : H ≤ G := deleted ▸ SimpleGraph.deleteEdges_le _
  have girthH : ∀ u (w : H.Walk u u), w.IsCycle → 5 ≤ w.length := by
    intro u w cycle
    have lower := girth u (w.mapLe sub) (cycle.mapLe sub)
    rw [SimpleGraph.Walk.length_mapLe] at lower
    omega
  exact first n (t+1) H z f girthH spec (remaining n t G H z f deg dz girth deleted spec size)
