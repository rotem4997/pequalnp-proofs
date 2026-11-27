import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4974_1
    (outUnion : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
      (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
      ∀ (x9 x10 : ℕ) (x11 : (Fin x9 → Bool) → ℕ → Finset ℕ),
        x2 + x2 ≤ x10 → x10 < x2 + x2 + x9 → (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) →
        (∃ a < x10, ∃ b < x10, ∀ (c : Fin x9 → Bool), x11 c x10 = x11 c a ∪ x11 c b) →
        (∀ (x14 : Fin x9 → Bool), ∀ x15 < x2 + x2, x11 x14 x15 = {x15}) →
        (∀ (x15 : Fin x9), ∃ x16 < x2 + x2 + ↑x15, ∃ x17 < x2 + x2 + ↑x15,
          (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = x11 x18 x16 ∪ x11 x18 x17) ∨
          (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = if x18 x15 = Bool.true then x11 x18 x16 else x11 x18 x17) ∨
          ∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = ∅) →
        (∀ (x16 : Fin x9 → Bool) (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x11 x16 x10 ∨ x2 + ↑x18 ∈ x11 x16 x10) →
        (∀ (x17 : Fin x2), ↑x17 ∉ x11 (fun _ => Bool.false) x10 ∧ x2 + ↑x17 ∈ x11 (fun _ => Bool.false) x10) →
        (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∃ (x20 : Fin x9 → Bool), ∀ (x21 : Fin x2),
          (↑x21 ∈ x11 x20 x10 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ (x2 + ↑x21 ∈ x11 x20 x10 ↔ x21 ∉ x18)) →
        (∀ (x19 : Fin x9 → Bool) (x20 : ℕ),
          have x21 : Fin x9 → Bool := fun x21 => if ↑x21 < x20 ∧ x11 x19 (x2 + x2 + ↑x21) ⊆ x11 x19 x10 then x19 x21 else Bool.false;
          x11 x21 x10 ⊆ x11 (fun _ => Bool.false) x10 ∪ x11 x19 x10 ∧ (x9 ≤ x20 → x11 x21 x10 = x11 x19 x10)) →
        x2 * x1 ≤ (100 : ℕ) * x9)
    (outSwitch : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
      (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
      ∀ (x9 x10 : ℕ) (x11 : (Fin x9 → Bool) → ℕ → Finset ℕ),
        x10 < x2 + x2 + x9 → (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) →
        (∃ (j : Fin x9), x10 = x2 + x2 + ↑j ∧ ∃ a < x10, ∃ b < x10,
          ∀ (c : Fin x9 → Bool), x11 c x10 = if c j = Bool.true then x11 c a else x11 c b) →
        (∀ (x14 : Fin x9 → Bool), ∀ x15 < x2 + x2, x11 x14 x15 = {x15}) →
        (∀ (x15 : Fin x9), ∃ x16 < x2 + x2 + ↑x15, ∃ x17 < x2 + x2 + ↑x15,
          (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = x11 x18 x16 ∪ x11 x18 x17) ∨
          (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = if x18 x15 = Bool.true then x11 x18 x16 else x11 x18 x17) ∨
          ∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = ∅) →
        (∀ (x16 : Fin x9 → Bool) (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x11 x16 x10 ∨ x2 + ↑x18 ∈ x11 x16 x10) →
        (∀ (x17 : Fin x2), ↑x17 ∉ x11 (fun _ => Bool.false) x10 ∧ x2 + ↑x17 ∈ x11 (fun _ => Bool.false) x10) →
        (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∃ (x20 : Fin x9 → Bool), ∀ (x21 : Fin x2),
          (↑x21 ∈ x11 x20 x10 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ (x2 + ↑x21 ∈ x11 x20 x10 ↔ x21 ∉ x18)) →
        (∀ (x19 : Fin x9 → Bool) (x20 : ℕ),
          have x21 : Fin x9 → Bool := fun x21 => if ↑x21 < x20 ∧ x11 x19 (x2 + x2 + ↑x21) ⊆ x11 x19 x10 then x19 x21 else Bool.false;
          x11 x21 x10 ⊆ x11 (fun _ => Bool.false) x10 ∪ x11 x19 x10 ∧ (x9 ≤ x20 → x11 x21 x10 = x11 x19 x10)) →
        x2 * x1 ≤ (100 : ℕ) * x9) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (300 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : (Fin x9 → Bool) → ℕ → Finset ℕ),             x10 < x2 + x2 + x9 →               (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) →                 (∀ (x14 : Fin x9 → Bool), ∀ x15 < x2 + x2, x11 x14 x15 = {x15}) →                   (∀ (x15 : Fin x9), ∃ x16 < x2 + x2 + ↑x15, ∃ x17 < x2 + x2 + ↑x15, (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = x11 x18 x16 ∪ x11 x18 x17) ∨ (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = if x18 x15 = Bool.true then x11 x18 x16 else x11 x18 x17) ∨ ∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = ∅) →                     (∀ (x16 : Fin x9 → Bool) (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x11 x16 x10 ∨ x2 + ↑x18 ∈ x11 x16 x10) →                       (∀ (x17 : Fin x2), ↑x17 ∉ x11 (fun (x18 : Fin x9) => Bool.false) x10 ∧ x2 + ↑x17 ∈ x11 (fun (x18 : Fin x9) => Bool.false) x10) →                         (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∃ (x20 : Fin x9 → Bool), ∀ (x21 : Fin x2), (↑x21 ∈ x11 x20 x10 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ (x2 + ↑x21 ∈ x11 x20 x10 ↔ x21 ∉ x18)) →                           (∀ (x19 : Fin x9 → Bool) (x20 : ℕ),                               have x21 : Fin x9 → Bool := fun (x21 : Fin x9) => if ↑x21 < x20 ∧ x11 x19 (x2 + x2 + ↑x21) ⊆ x11 x19 x10 then x19 x21 else Bool.false;                               x11 x21 x10 ⊆ x11 (fun (x22 : Fin x9) => Bool.false) x10 ∪ x11 x19 x10 ∧ (x9 ≤ x20 → x11 x21 x10 = x11 x19 x10)) →                             x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q N I inst hq hN hreg huniq m out F hout h3N hbase hgates hcov h0 hreal hprune
  have hN2 : 2 ≤ N := by omega
  have hout_ge : N + N ≤ out := by
    by_contra hlt
    have hout_lt : out < N + N := by omega
    have hsing := hbase (fun _ => false) out hout_lt
    have h00 := (h0 ⟨0, by omega⟩).2
    have h01 := (h0 ⟨1, by omega⟩).2
    rw [hsing, Finset.mem_singleton] at h00 h01
    simp at h00 h01
    omega
  let j : Fin m := ⟨out - (N + N), by omega⟩
  have hj_eq : N + N + j.val = out := by dsimp [j]; omega
  obtain ⟨a, ha, b, hb, hrule⟩ := hgates j
  rw [hj_eq] at ha hb hrule
  rcases hrule with hunion | hswitch | hdead
  · exact outUnion q N I hq hN hreg huniq m out F hout_ge hout h3N ⟨a, ha, b, hb, hunion⟩ hbase hgates hcov h0 hreal hprune
  · exact outSwitch q N I hq hN hreg huniq m out F hout h3N ⟨j, hj_eq.symm, a, ha, b, hb, hswitch⟩ hbase hgates hcov h0 hreal hprune
  · exfalso
    have h00 := (h0 ⟨0, by omega⟩).2
    rw [hdead (fun _ => false)] at h00
    exact Finset.notMem_empty _ h00
