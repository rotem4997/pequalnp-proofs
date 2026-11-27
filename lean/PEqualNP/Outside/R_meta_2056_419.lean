import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Take line zero as the line at infinity. The first problem has nine affine points and
-- twelve affine lines as inputs. The second restores the four deleted point stars.
-- Each star needs three binary OR gates, one AND, and one OR into the accumulated result.
theorem PEqualNP.Outside.R_meta_2056_419
    (small : ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 43 ∧ D.output < 21 + D.size ∧
    let ix : List (Fin 26) := [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
    let bits := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
      if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
    let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
    ∀ s t : Finset (Fin 13), D.eval (ix.map (bits s t)) = true ↔
      ∃ p ∈ s, p.val ∉ ([0, 1, 3, 9] : List ℕ) ∧ ∃ l ∈ t, near p l)
    (extend : ∀ D : Circuit, Monotone2 D → D.output < 21 + D.size →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 20 ∧
      let ix : List (Fin 26) := [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
      let bits := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
      if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      ∀ s t : Finset (Fin 13), C.eval (List.ofFn (bits s t)) = true ↔
        D.eval (ix.map (bits s t)) = true ∨
          ∃ p ∈ s, p.val ∈ ([0, 1, 3, 9] : List ℕ) ∧ ∃ l ∈ t, near p l) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := by
  obtain ⟨D, hd, h43, hout, affine⟩ := small
  obtain ⟨C, hc, h20, assembled⟩ := extend D hd hout
  refine ⟨C, hc, by omega, ?_⟩
  let ix : List (Fin 26) := [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
  let bits := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
      if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l : Fin 13 => ∀ p ∈ s, ¬near p l
  let read := fun s t => C.eval (List.ofFn (bits s t))
  change ∀ s t, D.eval (ix.map (bits s t)) = true ↔
    ∃ p ∈ s, p.val ∉ ([0, 1, 3, 9] : List ℕ) ∧ ∃ l ∈ t, near p l at affine
  change ∀ s t, read s t = true ↔ D.eval (ix.map (bits s t)) = true ∨
    ∃ p ∈ s, p.val ∈ ([0, 1, 3, 9] : List ℕ) ∧ ∃ l ∈ t, near p l at assembled
  have allEdges (s t) : read s t = true ↔ ∃ p ∈ s, ∃ l ∈ t, near p l := by
    rw [assembled, affine]
    constructor
    · rintro (⟨p, hp, _, witness⟩ | ⟨p, hp, _, witness⟩) <;> exact ⟨p, hp, witness⟩
    · rintro ⟨p, hp, witness⟩
      by_cases hin : p.val ∈ ([0, 1, 3, 9] : List ℕ)
      · exact Or.inr ⟨p, hp, hin, witness⟩
      · exact Or.inl ⟨p, hp, hin, witness⟩
  change (∀ p l : Fin 13, near p l → read {p} {l} = true) ∧
    ∀ s : Finset (Fin 13), s.card ≤ 3 → read s (off s) = false ∧ read (off s) s = false
  constructor
  · intro p l h
    exact (allEdges _ _).mpr ⟨p, by simp, l, by simp, h⟩
  · intro s _
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p, hp, l, hl, incident⟩ := (allEdges _ _).mp h
      exact (Finset.mem_filter.mp hl).2 p hp incident
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p, hp, l, hl, incident⟩ := (allEdges _ _).mp h
      apply (Finset.mem_filter.mp hp).2 l hl
      simpa [near, Nat.add_comm] using incident
