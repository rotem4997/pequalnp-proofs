import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6848

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem fren {α : Type} (z : α) (n : ℕ) (ρ : ℕ → ℕ) (r1 : ∀ i, i < n → ρ i < n) (r2 : ∀ i, n ≤ i → ρ i = i)
    (F : Gate → List α → α) (r : Gate → Gate)
    (hF : ∀ g d d', (∀ k, d'.getD (ρ k) z = d.getD k z) → F (r g) d' = F g d) :
    ∀ (gs : List Gate) (d d' : List α), d.length = d'.length → n ≤ d.length → (∀ k, d'.getD (ρ k) z = d.getD k z) →
      ∀ k, ((gs.map r).foldl (fun d g => d ++ [F g d]) d').getD (ρ k) z = (gs.foldl (fun d g => d ++ [F g d]) d).getD k z := by
  intro gs
  induction gs with
  | nil => intro d d' _ _ h; exact h
  | cons g gs ih =>
    intro d d' hl hn h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    refine ih _ _ (by simp [hl]) (by simp; omega) fun k => ?_
    rw [hF g d d' h]
    rcases Nat.lt_trichotomy k d.length with hk | hk | hk
    · have hk' : ρ k < d'.length := by
        by_cases hkn : k < n
        · have := r1 k hkn; omega
        · rw [r2 k (by omega)]; omega
      have := h k
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this ⊢
      rw [List.getElem?_append_left hk', List.getElem?_append_left hk]; exact this
    · rw [r2 k (by omega)]
      subst hk
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hl]
      conv_rhs => rw [← hl]
      simp [hl]
    · rw [r2 k (by omega), List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6848

theorem PEqualNP.Outside.L_meta_6848 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Equiv.Perm (Fin x2)),   have x4 : ℕ → ℕ := fun (x4 : ℕ) => if x5 : x4 < x2 then ↑(x3 (⟨x4, x5⟩ : Fin x2)) else x4;   ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x5.size = x1.size ∧ (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x6]? = Option.some x7 → ∃ (x9 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x9 ∧ x7.op = x9.op ∧ x7.inputs = List.map x4 x9.inputs) ∧ List.filter (fun (x6 : ℕ) => Decidable.decide (x2 ≤ x6)) (x5.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x5.gates) = List.filter (fun (x6 : ℕ) => Decidable.decide (x2 ≤ x6)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates) ∧ (∀ (x6 : Fin x2), x5.lineDeg x2 {↑(x3 x6)} = x1.lineDeg x2 {↑x6}) ∧ (PEqualNP.MetaComplexity.SingleLevel.andDepths x5 x2).getD x5.output (0 : ℕ) = (PEqualNP.MetaComplexity.SingleLevel.andDepths x1 x2).getD x1.output (0 : ℕ) ∧ ∀ (x6 : Fin x2 → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn (x6 ∘ ⇑x3)) := by
  intro C n π ρ
  have r1 : ∀ i, i < n → ρ i < n := by intro i hi; simp only [ρ, dif_pos hi]; exact (π ⟨i, hi⟩).isLt
  have r2 : ∀ i, n ≤ i → ρ i = i := by intro i hi; simp only [ρ]; rw [dif_neg (by omega)]
  have flt : ∀ l : List ℕ, (l.map ρ).filter (fun i => decide (n ≤ i)) = l.filter (fun i => decide (n ≤ i)) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.filter_cons, List.filter_cons, ih]
      by_cases h : n ≤ a
      · rw [r2 a h]
      · have := r1 a (by omega)
        rw [if_neg (by simp; omega), if_neg (by simp; omega)]
  have mg : ∀ {α : Type} (z : α) (d d' : List α), (∀ k, d'.getD (ρ k) z = d.getD k z) → ∀ l : List ℕ, (l.map ρ).map (fun i => d'.getD i z) = l.map (fun i => d.getD i z) := by
    intro α z d d' h l
    rw [List.map_map]; exact List.map_congr_left fun k _ => h k
  refine ⟨⟨C.gates.map fun g => ⟨g.op, g.inputs.map ρ⟩, ρ C.output⟩, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_, ?_, ?_, ?_, ?_⟩
  · intro j g hg
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hg
    obtain ⟨g', h1, rfl⟩ := hg
    exact ⟨g', h1, rfl, rfl⟩
  · rw [← flt (C.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates)]
    simp only [List.map_cons, List.flatMap_map, List.map_flatMap]
  · intro i
    simp only [PEqualNP.CircuitLowerBounds.Circuit.lineDeg, PEqualNP.CircuitLowerBounds.Circuit.lineDegrees]
    refine PEqualNP.Outside.L_meta_6848.fren 0 n ρ r1 r2 (fun g d => g.lineDegree d) (fun g => ⟨g.op, g.inputs.map ρ⟩) ?_ C.gates _ _ (by simp) (by simp) ?_ C.output
    · intro g d d' h
      simp only [PEqualNP.CircuitLowerBounds.Gate.lineDegree, mg 0 d d' h]
    · intro j
      by_cases hj : j < n
      · have e : ρ j = (π ⟨j, hj⟩ : ℕ) := by simp only [ρ, dif_pos hj]
        have e2 : (ρ j = (π i : ℕ)) ↔ j = (i : ℕ) := by
          rw [e]
          constructor
          · intro h; have := π.injective (Fin.ext h); exact congrArg Fin.val this
          · intro h; subst h; rfl
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (r1 j hj), List.getElem?_range hj, Option.map_some, Option.getD_some, Finset.mem_singleton, e2]
      · rw [r2 j (by omega), List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  · simp only [PEqualNP.MetaComplexity.SingleLevel.andDepths]
    refine PEqualNP.Outside.L_meta_6848.fren 0 n ρ r1 r2 (fun g d => (g.inputs.map fun i => d.getD i 0).foldr max 0 + PEqualNP.MetaComplexity.SingleLevel.andLevel g) (fun g => ⟨g.op, g.inputs.map ρ⟩) ?_ C.gates _ _ (by simp) (by simp) ?_ C.output
    · intro g d d' h
      simp only [mg 0 d d' h]
      congr 1
      obtain ⟨op, l⟩ := g
      cases op <;> rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rfl
    · intro j
      have z : ∀ k, (List.replicate n 0).getD k 0 = 0 := by
        intro k
        by_cases hk : k < n
        · simp [List.getD_eq_getElem?_getD, hk]
        · rw [List.getD_eq_default _ _ (by simp; omega)]
      rw [z, z]
  · intro x
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
    refine PEqualNP.Outside.L_meta_6848.fren false n ρ r1 r2 (fun g d => g.op.eval (g.inputs.map fun i => d.getD i false)) (fun g => ⟨g.op, g.inputs.map ρ⟩) ?_ C.gates _ _ (by simp) (by simp) ?_ C.output
    · intro g d d' h
      simp only [mg false d d' h]
    · intro j
      by_cases hj : j < n
      · have e : ρ j = (π ⟨j, hj⟩ : ℕ) := by simp only [ρ, dif_pos hj]
        rw [e]
        simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj]
      · rw [r2 j (by omega), List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
