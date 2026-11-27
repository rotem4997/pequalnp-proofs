import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2646_aux

open PEqualNP.CircuitLowerBounds

theorem getD_le {w w' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w w') (i : ℕ) :
    w.getD i false ≤ w'.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w w' : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  rw [bool_le]
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hx x hx'
    obtain ⟨i, hi, rfl⟩ := hx'
    exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, List.Forall₂ (fun a b => a ≤ b) w w' →
      List.Forall₂ (fun a b => a ≤ b)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; simpa using h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem eval_le (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ) (x y : Fin n → Bool)
    (hxy : ∀ i, x i ≤ y i) : C.eval (List.ofFn x) ≤ C.eval (List.ofFn y) := by
  have hC' : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact hxy _
  exact getD_le (fold_le C.gates hC' _ _ h0) C.output

end PEqualNP.Outside.L_meta_2646_aux

open PEqualNP.Outside.L_meta_2646_aux in
theorem PEqualNP.Outside.L_meta_2646 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : ℕ) (x5 : Fin x1 → Bool), (∀ (x6 : Fin x1), x5 x6 = Bool.true → x4.testBit ↑x6 = Bool.true) → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x7 : Fin x1) => x4.testBit ↑x7) = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x2 x5 = Bool.false := by
  intro n C hC m x hx hf
  have h := eval_le C hC n x (fun i => m.testBit i) (fun i => bool_le.mpr (hx i))
  unfold PEqualNP.MetaComplexity.circuitFun at hf ⊢
  rw [hf] at h
  cases hv : C.eval (List.ofFn x)
  · rfl
  · rw [hv] at h; exact absurd h (by decide)
