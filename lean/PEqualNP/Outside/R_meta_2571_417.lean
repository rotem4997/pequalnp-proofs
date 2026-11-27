import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The point inputs may participate in the first 28 gates. Each point wire only
-- has to reject independent assignments on which its own point is selected.
theorem PEqualNP.Outside.R_meta_2571_417
  (hbank : let I := fun p l : Fin 25 => p.val < 12 ∧ 12 ≤ l.val ∧
      (p.val+l.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧ p.val ∉ ([0,2,8] : List ℕ)
    ∃ (B : Circuit) (w : Fin 25 → ℕ) (q : ℕ), Monotone2 B ∧ B.size ≤ 28 ∧
      (∀ i, w i < 25+B.size) ∧ q < 25+B.size ∧
      (∃ p l, I p l ∧ (B.wires (List.ofFn (fun j : Fin 25 => decide (j=l)))).getD (w p) false = false) ∧
      ∀ x : Fin 25 → Bool,
      let v := fun a => (B.wires (List.ofFn x)).getD a false
      (∀ p l, I p l → x p = true → x l = true → v (w p) = true) ∧
      ((¬ ∃ p l, I p l ∧ x p = true ∧ x l = true) →
        (∀ p, p.val < 12 → p.val ∉ ([0,2,8] : List ℕ) → x p = true → v (w p) = false) ∧
        v q = (x 13 || x 15 || x 21)))
  (finish : ∀ (n k : ℕ) (B : Circuit) (p : Fin (k+1) → Fin n) (w : Fin (k+1) → ℕ),
      Monotone2 B → (∀ i, w i < n+B.size) →
      ∃ D : Circuit, Monotone2 D ∧ D.size = B.size+2*k+1 ∧ D.output < n+D.size ∧
      (∀ (x : Fin n → Bool) (a : ℕ), a < n+B.size →
        (D.wires (List.ofFn x)).getD a false = (B.wires (List.ofFn x)).getD a false) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ ∃ i, x (p i) = true ∧
        (B.wires (List.ofFn x)).getD (w i) false = true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (25 : ℕ) + x1.size ∧ x2 < (25 : ℕ) + x1.size ∧ ∀ (x3 : Fin (25 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)), ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x4 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  let I := fun p l : Fin 25 => p.val < 12 ∧ 12 ≤ l.val ∧
    (p.val+l.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧ p.val ∉ ([0,2,8] : List ℕ)
  let points : Fin 9 → Fin 25 := ![1,3,4,5,6,7,9,10,11]
  have listed : ∀ a : Fin 25, (a.val < 12 ∧ a.val ∉ ([0,2,8] : List ℕ)) ↔
      ∃ i, points i = a := by decide
  obtain ⟨B,w,q,mB,sB,bw,bq,_,bank⟩ := hbank
  obtain ⟨D,mD,sD,oD,keep,out⟩ := finish 25 8 B points (fun i => w (points i)) mB (fun i => bw _)
  refine ⟨D,q,mD,by omega,oD,by omega,?_⟩
  intro x
  let F := ∃ p l, I p l ∧ x p = true ∧ x l = true
  have eqF : D.eval (List.ofFn x) = true ↔ F := by
    constructor
    · intro hd
      obtain ⟨i,hp,hv⟩ := (out x).mp hd
      by_contra hf
      obtain ⟨lo,exc⟩ := (listed _).mpr ⟨i,rfl⟩
      have bad := ((bank x).2 hf).1 (points i) lo exc hp
      exact Bool.false_ne_true (bad.symm.trans hv)
    · rintro ⟨p,l,h,hp,hl⟩
      obtain ⟨i,eq⟩ := (listed p).mp ⟨h.1,h.2.2.2⟩
      apply (out x).mpr
      exact ⟨i,eq.symm ▸ hp,eq.symm ▸ (bank x).1 p l h hp hl⟩
  constructor
  · simpa only [F,I,and_assoc] using eqF
  · intro hd
    have hf : ¬ F := fun h => Bool.false_ne_true (hd.symm.trans (eqF.mpr h))
    exact (keep x q bq).trans (((bank x).2 hf).2)
