import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3769_427
    (hoverlap :
      ∀ (n : ℕ) (inc : Fin n → Fin n → Prop) [DecidableRel inc],
        (∀ a b : Fin n, a ≠ b → ∃! l : Fin n, inc a l ∧ inc b l) →
        ∀ (l : Fin n) (S : Finset (Fin n)), l ∉ S → Fintype.card {p : Fin n // inc p l ∧ ∃ m ∈ S, inc p m} ≤ S.card)
    (hcircuit :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
        ∀ (x9 x10 : ℕ) (x11 : (Fin x9 → Bool) → ℕ → Finset ℕ), x10 < x2 + x2 + x9 → (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) →
        (∀ (x14 : Fin x9 → Bool), ∀ x15 < x2 + x2, x11 x14 x15 = {x15}) →
        (∀ (x15 : Fin x9), ∃ x16 < x2 + x2 + ↑x15, ∃ x17 < x2 + x2 + ↑x15,
          (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = x11 x18 x16 ∪ x11 x18 x17) ∨
          (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = if x18 x15 = Bool.true then x11 x18 x16 else x11 x18 x17) ∨
          ∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = ∅) →
        (∀ (x16 : Fin x9 → Bool) (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x11 x16 x10 ∨ x2 + ↑x18 ∈ x11 x16 x10) →
        (∀ (x17 : Fin x2), ↑x17 ∉ x11 (fun (x18 : Fin x9) => Bool.false) x10 ∧ x2 + ↑x17 ∈ x11 (fun (x18 : Fin x9) => Bool.false) x10) →
        (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∃ (x20 : Fin x9 → Bool),
          (∀ p : Fin x2, x2 + ↑p ∈ x11 x20 x10 ↔ p ∉ x18) ∧
          (∀ p : Fin x2, ↑p ∈ x11 x20 x10 → ∃ m ∈ x18, x3 p m) ∧
          (∀ l : Fin x2, l ∉ x18 → Fintype.card {p : Fin x2 // x3 p l ∧ ↑p ∈ x11 x20 x10} ≤ x18.card)) →
        x2 * x1 ≤ (100 : ℕ) * x9) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
        ∀ (x9 x10 : ℕ) (x11 : (Fin x9 → Bool) → ℕ → Finset ℕ), x10 < x2 + x2 + x9 → (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) →
        (∀ (x14 : Fin x9 → Bool), ∀ x15 < x2 + x2, x11 x14 x15 = {x15}) →
        (∀ (x15 : Fin x9), ∃ x16 < x2 + x2 + ↑x15, ∃ x17 < x2 + x2 + ↑x15,
          (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = x11 x18 x16 ∪ x11 x18 x17) ∨
          (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = if x18 x15 = Bool.true then x11 x18 x16 else x11 x18 x17) ∨
          ∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = ∅) →
        (∀ (x16 : Fin x9 → Bool) (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x11 x16 x10 ∨ x2 + ↑x18 ∈ x11 x16 x10) →
        (∀ (x17 : Fin x2), ↑x17 ∉ x11 (fun (x18 : Fin x9) => Bool.false) x10 ∧ x2 + ↑x17 ∈ x11 (fun (x18 : Fin x9) => Bool.false) x10) →
        (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∃ (x20 : Fin x9 → Bool),
          ∀ (x21 : Fin x2), (↑x21 ∈ x11 x20 x10 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ (x2 + ↑x21 ∈ x11 x20 x10 ↔ x21 ∉ x18)) →
        x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q n inc inst hq hn hline hpair g o A ho hg hin hgate hsound hzero hreal
  apply hcircuit q n inc hq hn hline g o A ho hg hin hgate hsound hzero
  intro S hS
  obtain ⟨b, hb⟩ := hreal S hS
  refine ⟨b, fun p => (hb p).2, fun p => (hb p).1.mp, ?_⟩
  intro l hl
  let f : {p : Fin n // inc p l ∧ ↑p ∈ A b o} →
      {p : Fin n // inc p l ∧ ∃ m ∈ S, inc p m} :=
    fun p => ⟨p.val, p.property.1, (hb p.val).1.mp p.property.2⟩
  have hf : Function.Injective f := by
    intro p r e
    exact Subtype.ext (congrArg (fun z : {p : Fin n // inc p l ∧ ∃ m ∈ S, inc p m} => z.val) e)
  exact (Fintype.card_le_of_injective f hf).trans (hoverlap n inc hpair l S hl)
