import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.HeptadCover

theorem PEqualNP.Outside.R_meta_18223_1
  (rowZero : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x3 (0 : Fin (26 : ℕ)) = Bool.false → (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧ x3 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true)) → (59 : ℕ) ≤ x1.size)
  (transport : 
  let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13, p ∈ singerLines3 l ∧
    x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  ∀ (v : Fin 26) (C : Circuit), IsAO2 26 C →
    ∃ (σ : Fin 26 → Fin 26) (D : Circuit), Function.Bijective σ ∧ σ v = 0 ∧
      IsAO2 26 D ∧ D.size = C.size ∧
      (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ))) ∧
      ∀ x : Fin 26 → Bool, F (x ∘ σ) ↔ F x) :
  have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.singerLines3 x3 ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 : Fin (26 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → (∀ (x5 : Fin (26 : ℕ) → Bool), x5 x2 = Bool.false → (x3.eval (List.ofFn x5) = Bool.true ↔ x1 x5)) → (59 : ℕ) ≤ x3.size := by
  dsimp only
  intro v C model correct
  obtain ⟨σ,D,_,zero,good,size,eval,invar⟩ := transport v C model
  rw [← size]
  apply rowZero D good
  intro x hx
  rw [eval]
  exact (correct (x ∘ σ) (by simpa only [Function.comp_apply,zero] using hx)).trans (invar x)
