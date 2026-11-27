import Mathlib
import PEqualNP.Defs

-- The three points on the missing point's first line account for twelve incidences.
-- The extension adds these twelve incidences and joins the auxiliary flag.
theorem PEqualNP.Outside.R_meta_2215_317
    (hnine : ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (q : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 45 ∧
      C.output < 25 + C.size ∧ q < 25 + C.size ∧ ∀ x : Fin 25 → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ i j : Fin 25,
        i.val < 12 ∧ 12 ≤ j.val ∧ (i.val + j.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧
        i.val ∉ ([0,2,8] : List ℕ) ∧ x i = true ∧ x j = true) ∧
      (C.eval (List.ofFn x) = false → (C.wires (List.ofFn x)).getD q false =
        (x 13 || x 15 || x 21)))
    (hextend : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (q : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C → C.output < 25 + C.size → q < 25 + C.size →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (r : ℕ),
      PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ C.size + 16 ∧
      D.output < 25 + D.size ∧ r < 25 + D.size ∧ ∀ x : Fin 25 → Bool,
      (D.eval (List.ofFn x) = true ↔ C.eval (List.ofFn x) = true ∨ ∃ i j : Fin 25,
        i.val < 12 ∧ 12 ≤ j.val ∧ (i.val + j.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧
        i.val ∈ ([0,2,8] : List ℕ) ∧ x i = true ∧ x j = true) ∧
      ((D.wires (List.ofFn x)).getD r false =
        ((C.wires (List.ofFn x)).getD q false || x 12))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  classical
  obtain ⟨C,q,hmono,hsize,ho,hq,hC⟩ := hnine
  obtain ⟨D,r,hmonD,hsizeD,hoD,hr,hD⟩ := hextend C q hmono ho hq
  refine ⟨D,r,hmonD,by omega,hoD,hr,?_⟩
  intro x
  dsimp only
  obtain ⟨cval,caux⟩ := hC x
  obtain ⟨dval,daux⟩ := hD x
  constructor
  · rw [dval,cval]
    constructor
    · rintro (⟨i,j,hi,hj,hd,_,hx,hy⟩ | ⟨i,j,hi,hj,hd,_,hx,hy⟩)
      all_goals exact ⟨i,j,⟨hi,hj,hd⟩,hx,hy⟩
    · rintro ⟨i,j,⟨hi,hj,hd⟩,hx,hy⟩
      by_cases h : i.val ∈ ([0,2,8] : List ℕ)
      · exact Or.inr ⟨i,j,hi,hj,hd,h,hx,hy⟩
      · exact Or.inl ⟨i,j,hi,hj,hd,h,hx,hy⟩
  · intro rej
    have cfalse : C.eval (List.ofFn x) = false := by
      cases hc : C.eval (List.ofFn x) with
      | false => rfl
      | true =>
        have yes := dval.mpr (Or.inl hc)
        rw [rej] at yes
        contradiction
    rw [daux,caux cfalse]
    ac_rfl
