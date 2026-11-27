import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7043

open PEqualNP.CircuitLowerBounds

def F (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem F_ext (gs : List Gate) : ∀ w : List Bool, ∃ t, F gs w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [F]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_⟩
    simp only [F, List.foldl_cons] at ht ⊢
    rw [ht, List.append_assoc]

theorem F_len (gs : List Gate) : ∀ w : List Bool, (F gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [F]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [F, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem F_snoc (pre : List Gate) (g : Gate) (w : List Bool) :
    F (pre ++ [g]) w = F pre w ++ [g.op.eval (g.inputs.map fun i => (F pre w).getD i false)] := by
  simp [F, List.foldl_append]

theorem getD_lt_of_true {A : List Bool} {i : ℕ} (h : A.getD i false = true) : i < A.length := by
  by_contra hn
  rw [List.getD_eq_default _ _ (by omega)] at h
  exact Bool.false_ne_true h

end PEqualNP.Outside.L_meta_7043

theorem PEqualNP.Outside.L_meta_7043 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 : Fin x1 → Bool),   PEqualNP.MetaComplexity.Monotone2 x2 →     (∀ (x7 : Fin x1), x3 x7 = Bool.true → x4 x7 = Bool.true ∨ x5 x7 = Bool.true) →       PEqualNP.MetaComplexity.circuitFun x1 x2 x3 = Bool.true →         PEqualNP.MetaComplexity.circuitFun x1 x2 x4 = Bool.false →           PEqualNP.MetaComplexity.circuitFun x1 x2 x5 = Bool.false →             have x11 : (Fin x1 → Bool) → ℕ → Bool := fun (x11 : Fin x1 → Bool) (x12 : ℕ) => (x2.wires (List.ofFn x11)).getD x12 Bool.false;             ∃ x12 ∈ x2.gates, x12.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ x13 ∈ x12.inputs, ∃ x14 ∈ x12.inputs, x11 x3 x13 = Bool.true ∧ x11 x3 x14 = Bool.true ∧ x11 x4 x13 = Bool.false ∧ x11 x5 x13 = Bool.true ∧ x11 x4 x14 = Bool.true ∧ x11 x5 x14 = Bool.false := by
  intro x1 x2 x3 x4 x5 hmono hcov h3 h4 h5
  dsimp only
  by_contra hne
  have hW : ∀ x : Fin x1 → Bool, x2.wires (List.ofFn x) = PEqualNP.Outside.L_meta_7043.F x2.gates (List.ofFn x) := fun x => rfl
  have main : ∀ pre : List PEqualNP.CircuitLowerBounds.Gate, pre <+: x2.gates →
      ∀ i, (PEqualNP.Outside.L_meta_7043.F pre (List.ofFn x3)).getD i false = true →
        (PEqualNP.Outside.L_meta_7043.F pre (List.ofFn x4)).getD i false = true ∨
        (PEqualNP.Outside.L_meta_7043.F pre (List.ofFn x5)).getD i false = true := by
    intro pre
    induction pre using List.reverseRecOn with
    | nil =>
      intro _ i hi
      have hlt := PEqualNP.Outside.L_meta_7043.getD_lt_of_true hi
      simp only [PEqualNP.Outside.L_meta_7043.F, List.foldl_nil, List.length_ofFn] at hi hlt ⊢
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true, Option.getD_some] at hi ⊢
      exact hcov ⟨i, hlt⟩ hi
    | append_singleton pre g ih =>
      intro hp i hi
      have hpre : pre <+: x2.gates := (List.prefix_append pre [g]).trans hp
      have hg : g ∈ x2.gates := hp.subset (by simp)
      obtain ⟨t, ht⟩ := hp
      have ih' := ih hpre
      have hl3 := PEqualNP.Outside.L_meta_7043.F_len pre (List.ofFn x3)
      have hl4 := PEqualNP.Outside.L_meta_7043.F_len pre (List.ofFn x4)
      have hl5 := PEqualNP.Outside.L_meta_7043.F_len pre (List.ofFn x5)
      simp only [List.length_ofFn] at hl3 hl4 hl5
      have hfull : ∀ x : Fin x1 → Bool, ∀ j, j < (PEqualNP.Outside.L_meta_7043.F pre (List.ofFn x)).length →
          (x2.wires (List.ofFn x)).getD j false = (PEqualNP.Outside.L_meta_7043.F pre (List.ofFn x)).getD j false := by
        intro x j hj
        rw [hW, ← ht, PEqualNP.Outside.L_meta_7043.F]
        rw [List.foldl_append]
        change (PEqualNP.Outside.L_meta_7043.F t (PEqualNP.Outside.L_meta_7043.F (pre ++ [g]) (List.ofFn x))).getD j false = _
        obtain ⟨s, hs⟩ := PEqualNP.Outside.L_meta_7043.F_ext t (PEqualNP.Outside.L_meta_7043.F (pre ++ [g]) (List.ofFn x))
        rw [hs, PEqualNP.Outside.L_meta_7043.F_snoc, List.append_assoc, List.getD_append _ _ _ _ hj]
      rw [PEqualNP.Outside.L_meta_7043.F_snoc] at hi ⊢
      rw [PEqualNP.Outside.L_meta_7043.F_snoc]
      set A3 := PEqualNP.Outside.L_meta_7043.F pre (List.ofFn x3) with hA3
      set A4 := PEqualNP.Outside.L_meta_7043.F pre (List.ofFn x4) with hA4
      set A5 := PEqualNP.Outside.L_meta_7043.F pre (List.ofFn x5) with hA5
      rcases lt_trichotomy i A3.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hi
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact ih' i hi
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        simp only [Nat.sub_self, hl3, hl4, hl5, List.getD_cons_zero] at hi ⊢
        have hop := (hmono g hg).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · rw [hop] at hi ⊢
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_map, List.all_eq_true,
            Function.comp_apply, id] at hi ⊢
          by_contra hno
          push_neg at hno
          simp only [ne_eq, Bool.not_eq_true] at hno
          obtain ⟨⟨a, ha, ha4⟩, ⟨b, hb, hb5⟩⟩ := hno
          have ha3 := hi a ha
          have hb3 := hi b hb
          have ha5 : A5.getD a false = true := by
            rcases ih' a ha3 with h | h
            · rw [ha4] at h; exact absurd h Bool.false_ne_true
            · exact h
          have hb4 : A4.getD b false = true := by
            rcases ih' b hb3 with h | h
            · exact h
            · rw [hb5] at h; exact absurd h Bool.false_ne_true
          have hla := PEqualNP.Outside.L_meta_7043.getD_lt_of_true ha3
          have hlb := PEqualNP.Outside.L_meta_7043.getD_lt_of_true hb3
          apply hne
          refine ⟨g, hg, hop, a, ha, b, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hfull x3 a hla]; exact ha3
          · rw [hfull x3 b hlb]; exact hb3
          · rw [hfull x4 a (show a < A4.length by omega)]; exact ha4
          · rw [hfull x5 a (show a < A5.length by omega)]; exact ha5
          · rw [hfull x4 b (show b < A4.length by omega)]; exact hb4
          · rw [hfull x5 b (show b < A5.length by omega)]; exact hb5
        · rw [hop] at hi ⊢
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true,
            Function.comp_apply, id] at hi ⊢
          obtain ⟨a, ha, ha3⟩ := hi
          rcases ih' a ha3 with h | h
          · exact Or.inl ⟨a, ha, h⟩
          · exact Or.inr ⟨a, ha, h⟩
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact absurd hi Bool.false_ne_true
  have hout := main x2.gates (List.prefix_refl _) x2.output
  rw [← hW, ← hW, ← hW] at hout
  have e3 : (x2.wires (List.ofFn x3)).getD x2.output false = true := h3
  have e4 : (x2.wires (List.ofFn x4)).getD x2.output false = false := h4
  have e5 : (x2.wires (List.ofFn x5)).getD x2.output false = false := h5
  rcases hout e3 with h | h
  · rw [e4] at h; exact Bool.false_ne_true h
  · rw [e5] at h; exact Bool.false_ne_true h
