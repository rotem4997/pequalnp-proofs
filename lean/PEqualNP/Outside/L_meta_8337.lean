import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8337

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Le (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

theorem le_snoc {w w' : List Bool} {v v' : Bool} (h : Le w w') (hv : v = true → v' = true) :
    Le (w ++ [v]) (w' ++ [v']) := by
  obtain ⟨hl, hp⟩ := h
  refine ⟨by simp [hl], fun i hi => ?_⟩
  have hp' := hp i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append] at hi hp' ⊢
  rw [← hl]
  by_cases hlt : i < w.length
  · simp only [hlt, ite_true] at hi ⊢
    exact hp' hi
  · simp only [hlt, ite_false] at hi ⊢
    by_cases h0 : i - w.length = 0
    · simp only [h0, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact hv hi
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
      simp [hk] at hi

theorem gate_mono {w w' : List Bool} (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (h : Le w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun H i hi => h.2 i (H i hi)
  · rw [Set.mem_singleton_iff] at hg
    rw [hg]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, H⟩ => ⟨i, hi, h.2 i H⟩

theorem fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ (w w' : List Bool), Le w w' →
      Le (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
         (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (le_snoc h (gate_mono g (hgs g List.mem_cons_self) h))

theorem ofFn_le {n : ℕ} (a b : Fin n → Bool) (h : ∀ k, a k = true → b k = true) :
    Le (List.ofFn a) (List.ofFn b) := by
  refine ⟨by simp, fun i hi => ?_⟩
  simp only [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < n
  · simp only [List.getElem?_ofFn, hlt, dif_pos, Option.getD_some] at hi ⊢
    exact h _ hi
  · simp [hlt] at hi

end PEqualNP.Outside.L_meta_8337

theorem PEqualNP.Outside.L_meta_8337 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 x4 : Fin (14 : ℕ) → Bool), (∀ (x5 : Fin (14 : ℕ)), x3 x5 = Bool.true → x4 x5 = Bool.true) → ∀ (x6 : ℕ), (x1.wires (List.ofFn x3)).getD x6 Bool.false = Bool.true → (x1.wires (List.ofFn x4)).getD x6 Bool.false = Bool.true := by
  intro x1 h a b hab w hh
  have hgs : ∀ g ∈ x1.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) := by
    intro g hg
    have := (h g hg).1
    simpa [Set.mem_insert_iff] using this
  have hle := PEqualNP.Outside.L_meta_8337.fold_mono x1.gates hgs _ _
    (PEqualNP.Outside.L_meta_8337.ofFn_le a b hab)
  exact hle.2 w hh
