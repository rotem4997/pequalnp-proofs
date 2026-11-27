import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5946

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

theorem fun_mono {n : ℕ} (C : Circuit) (hC : Monotone2 C) (a b : Fin n → Bool)
    (h : ∀ k, a k = true → b k = true) :
    circuitFun n C a = true → circuitFun n C b = true := by
  unfold circuitFun Circuit.eval Circuit.wires
  exact (fold_mono C.gates (fun g hg => (hC g hg).1) _ _ (ofFn_le a b h)).2 C.output

end PEqualNP.Outside.L_meta_5946

theorem PEqualNP.Outside.L_meta_5946 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x5 x6 : Fin x1), x2 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 fun (x8 : Fin (x1 + x1)) => Decidable.decide (x8 = Fin.castAdd x1 x5 ∨ x8 = Fin.natAdd x1 x6)) = Bool.true) → (∀ (x6 : Fin (x1 + x1) → Bool), (¬∃ (x7 : Fin x1) (x8 : Fin x1), x2 x7 x8 ∧ x6 (Fin.castAdd x1 x7) = Bool.true ∧ x6 (Fin.natAdd x1 x8) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x6 = Bool.false) → ∀ (x7 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x7 = Bool.true ↔ ∃ (x8 : Fin x1), ∃ x9 ∈ Finset.univ, x2 x8 x9 ∧ x7 (Fin.castAdd x1 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true := by
  intro x1 x2 x3 hM h1 h2 x7
  constructor
  · intro h
    by_contra hne
    have := h2 x7 (fun ⟨p, l, hp⟩ => hne ⟨p, l, Finset.mem_univ _, hp⟩)
    rw [this] at h
    exact Bool.false_ne_true h
  · rintro ⟨p, l, _, hpl, ha, hb⟩
    refine PEqualNP.Outside.L_meta_5946.fun_mono x3 hM _ x7 ?_ (h1 p l hpl)
    intro k hk
    rcases of_decide_eq_true hk with rfl | rfl
    · exact ha
    · exact hb
