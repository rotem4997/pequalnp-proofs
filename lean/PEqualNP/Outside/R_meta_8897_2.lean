import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover

theorem PEqualNP.Outside.R_meta_8897_2
    (hRelabel : ∀ C : Circuit, Monotone2 C →
      ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧
        D.lineDeg 26 (Finset.Ico 13 26) = C.lineDeg 26 (Finset.range 13) ∧
        ∀ X Y : Finset (Fin 13), D.eval (incidenceInput X Y) =
          C.eval (incidenceInput (Y.image (fun v => -v)) (X.image (fun v => -v))))
    (hLine : ∀ C : Circuit, Monotone2 C → ComputesIncidence singerLines3 C →
      HasLineDegree 26 (Finset.Ico 13 26) C 2 → 64 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (2 : ℕ) → (64 : ℕ) ≤ x1.size := by
  intro C hMono hInc hEither
  rcases hEither with hLineDegree | hPointDegree
  · exact hLine C hMono hInc hLineDegree
  obtain ⟨D, hD, hsize, hdeg, heval⟩ := hRelabel C hMono
  have hPolarity : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ -l ∈ singerLines3 (-p) := by
    decide
  have hCorrect : ComputesIncidence singerLines3 D := by
    intro X Y
    rw [heval X Y, hInc]
    unfold incidenceFun
    rw [decide_eq_decide]
    constructor
    · rintro ⟨v, hv, w, hw, hadj⟩
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨p, hp, l, hl, (hPolarity p l).mpr hadj⟩
    · rintro ⟨p, hp, l, hl, hadj⟩
      exact ⟨-l, Finset.mem_image.mpr ⟨l, hl, rfl⟩,
        -p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, (hPolarity p l).mp hadj⟩
  have hLineDegree : HasLineDegree 26 (Finset.Ico 13 26) D 2 := by
    change D.lineDeg 26 (Finset.Ico 13 26) ≤ 2
    rw [hdeg]
    exact hPointDegree
  simpa only [hsize] using hLine D hD hCorrect hLineDegree
