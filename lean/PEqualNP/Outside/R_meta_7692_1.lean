import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_7692_1
    (residual : ∃ (C : Circuit) (u : ℕ), C.size ≤ 22 ∧ TopForm.IsAO2 14 C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧ u < 14 + C.size ∧ u ≠ 2 ∧
      ∀ x : Fin 14 → Bool, BlindGate.wireValue C 14 x u = true ↔
        ∃ p l : Fin 7, p ≠ 2 ∧ (p = l ∨ p = l+1 ∨ p = l+3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
    (appendOr : ∀ (n : ℕ) (C : Circuit) (a b : ℕ), TopForm.IsAO2 n C →
      (∀ g ∈ C.gates, g.inputs.Nodup) → a < n + C.size → b < n + C.size → a ≠ b →
      ∃ D : Circuit, D.size = C.size+1 ∧ TopForm.IsAO2 n D ∧
        (∀ g ∈ D.gates, g.inputs.Nodup) ∧ ∀ x : Fin n → Bool,
        (∀ i < n + C.size, BlindGate.wireValue D n x i = BlindGate.wireValue C n x i) ∧
        BlindGate.wireValue D n x (n+C.size) =
          (BlindGate.wireValue C n x a || BlindGate.wireValue C n x b)) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ),   x1.size ≤ (24 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧         x2 < (14 : ℕ) + x1.size ∧           x3 < (14 : ℕ) + x1.size ∧             x2 ≠ (2 : ℕ) ∧               x2 ≠ x3 ∧                 ∀ (x4 : Fin (14 : ℕ) → Bool),                   have x5 : ℕ → Bool := PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x4;                   (x5 x2 || x5 (2 : ℕ) && x5 x3) = Decidable.decide (∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x7) = Bool.true) ∧ ∀ x6 ∈ [(0 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ))], (x4 = fun (x8 : Fin (14 : ℕ)) => Decidable.decide (x8 = x6)) → x5 (2 : ℕ) = Bool.false ∧ x5 x3 = Bool.false) := by
  obtain ⟨C,u,sz,ao,nd,hu,hne,hf⟩ := residual
  obtain ⟨D,ds,da,dn,hd⟩ := appendOr 14 C 8 9 ao nd (by omega) (by omega) (by decide)
  obtain ⟨B,bs,ba,bn,hb⟩ := appendOr 14 D (14+C.size) 13 da dn (by omega) (by omega) (by omega)
  have keep (gs : List Gate) (z : List Bool) (i : ℕ) (hi : i < z.length) :
      ((Circuit.mk gs 0).wires z).getD i false = z.getD i false := by
    induction gs generalizing z with
    | nil => rfl
    | cons g gs ih =>
      let zs := z ++ [g.op.eval (g.inputs.map fun j => z.getD j false)]
      change ((Circuit.mk gs 0).wires zs).getD i false = _
      rw [ih zs (by simp [zs]; omega)]
      exact List.getD_append _ _ _ _ hi
  have raw (F : Circuit) (x : Fin 14 → Bool) (i : Fin 14) :
      BlindGate.wireValue F 14 x i.val = x i := by
    change ((Circuit.mk F.gates 0).wires (List.ofFn x)).getD i.val false = x i
    rw [keep _ _ _ (by simpa using i.isLt)]
    fin_cases i <;> rfl
  refine ⟨B,u,14+D.size,by omega,ba,bn,by omega,by omega,hne,by omega,?_⟩
  intro x
  dsimp only
  have valU := ((hb x).1 u (by omega)).trans ((hd x).1 u hu)
  have valV : BlindGate.wireValue B 14 x (14+D.size) = (x 8 || x 9 || x 13) := by
    rw [(hb x).2,(hd x).2]
    exact congrArg₂ Bool.or (congrArg₂ Bool.or (raw C x 8) (raw C x 9)) (raw D x 13)
  have val2 := raw B x (2 : Fin 14)
  change BlindGate.wireValue B 14 x 2 = x 2 at val2
  rw [valU,valV,val2]
  constructor
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    rw [hf x]
    constructor
    · rintro (⟨p,l,_,e,hp,hl⟩ | ⟨hp,h⟩)
      · exact ⟨p,l,e,hp,hl⟩
      · rcases h with (h | h) | h
        · exact ⟨2,1,by decide,hp,h⟩
        · exact ⟨2,2,by decide,hp,h⟩
        · exact ⟨2,6,by decide,hp,h⟩
    · rintro ⟨p,l,e,hp,hl⟩
      by_cases h : p = 2
      · subst p
        right
        refine ⟨hp,?_⟩
        have lines : ∀ j : Fin 7, (2 = j ∨ 2 = j+1 ∨ 2 = j+3) → j = 1 ∨ j = 2 ∨ j = 6 := by decide
        rcases lines l e with rfl | rfl | rfl
        · exact Or.inl (Or.inl hl)
        · exact Or.inl (Or.inr hl)
        · exact Or.inr hl
      · exact Or.inl ⟨p,l,h,e,hp,hl⟩
  · intro i hi hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl <;> subst x <;> decide

