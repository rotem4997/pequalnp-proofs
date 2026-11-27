import PEqualNP.Defs

-- Flip only switches whose target results lie in the target cover.
-- Ordered by gate index, the intermediate flips stay inside the union of the two covers.
theorem PEqualNP.Outside.R_meta_3769_1
    (prefixes : ∀ (m s o : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ),
      o < m+s → (∀ z v, v < m → D z v = {v}) →
      (∀ j : Fin s, ∃ a < m+j.val, ∃ b < m+j.val,
        (∀ z, D z (m+j.val) = D z a ∪ D z b) ∨
        (∀ z, D z (m+j.val) = if z j = true then D z a else D z b) ∨
        ∀ z, D z (m+j.val) = ∅) →
      ∀ (z : Fin s → Bool) (k : ℕ),
        let h := fun j : Fin s =>
          if j.val < k ∧ D z (m+j.val) ⊆ D z o then z j else false
        D h o ⊆ D (fun _ => false) o ∪ D z o ∧ (s ≤ k → D h o = D z o))
    (count : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : (Fin x9 → Bool) → ℕ → Finset ℕ), x10 < x2 + x2 + x9 → (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) → (∀ (x14 : Fin x9 → Bool), ∀ x15 < x2 + x2, x11 x14 x15 = {x15}) → (∀ (x15 : Fin x9), ∃ x16 < x2 + x2 + ↑x15, ∃ x17 < x2 + x2 + ↑x15, (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = x11 x18 x16 ∪ x11 x18 x17) ∨ (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = if x18 x15 = Bool.true then x11 x18 x16 else x11 x18 x17) ∨ ∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = ∅) → (∀ (x16 : Fin x9 → Bool) (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x11 x16 x10 ∨ x2 + ↑x18 ∈ x11 x16 x10) → (∀ (x17 : Fin x2), ↑x17 ∉ x11 (fun (x18 : Fin x9) => Bool.false) x10 ∧ x2 + ↑x17 ∈ x11 (fun (x18 : Fin x9) => Bool.false) x10) → (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∃ (x20 : Fin x9 → Bool), ∀ (x21 : Fin x2), (↑x21 ∈ x11 x20 x10 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ (x2 + ↑x21 ∈ x11 x20 x10 ↔ x21 ∉ x18)) → (∀ (z : Fin x9 → Bool) (k : ℕ),
        let h := fun j : Fin x9 =>
          if j.val < k ∧ x11 z (x2+x2+j.val) ⊆ x11 z x10 then z j else false
        x11 h x10 ⊆ x11 (fun _ => false) x10 ∪ x11 z x10 ∧
          (x9 ≤ k → x11 h x10 = x11 z x10)) → x2 * x1 ≤ (100 : ℕ) * x9) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : (Fin x9 → Bool) → ℕ → Finset ℕ), x10 < x2 + x2 + x9 → (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) → (∀ (x14 : Fin x9 → Bool), ∀ x15 < x2 + x2, x11 x14 x15 = {x15}) → (∀ (x15 : Fin x9), ∃ x16 < x2 + x2 + ↑x15, ∃ x17 < x2 + x2 + ↑x15, (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = x11 x18 x16 ∪ x11 x18 x17) ∨ (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = if x18 x15 = Bool.true then x11 x18 x16 else x11 x18 x17) ∨ ∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = ∅) → (∀ (x16 : Fin x9 → Bool) (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x11 x16 x10 ∨ x2 + ↑x18 ∈ x11 x16 x10) → (∀ (x17 : Fin x2), ↑x17 ∉ x11 (fun (x18 : Fin x9) => Bool.false) x10 ∧ x2 + ↑x17 ∈ x11 (fun (x18 : Fin x9) => Bool.false) x10) → (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∃ (x20 : Fin x9 → Bool), ∀ (x21 : Fin x2), (↑x21 ∈ x11 x20 x10 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ (x2 + ↑x21 ∈ x11 x20 x10 ↔ x21 ∉ x18)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q N I decI qmin size incid unique s o D bound sparse inputs gates safe base realize
  exact count q N I qmin size incid unique s o D bound sparse inputs gates safe base realize
    (prefixes (N+N) s o D bound inputs gates)
