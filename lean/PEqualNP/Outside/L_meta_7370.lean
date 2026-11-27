import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7370_aux

open PEqualNP.CircuitLowerBounds

def f (i : ℕ) : ℕ := if i < 9 then i else if i < 12 then i + 1 else i + 2

def rg (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem step (w w' : List Bool) (b : Bool) (hl : 12 ≤ w.length) (hl' : w'.length = w.length + 2)
    (h : ∀ i, w'.getD (f i) false = w.getD i false) (i : ℕ) :
    (w' ++ [b]).getD (f i) false = (w ++ [b]).getD i false := by
  have hi := h i
  simp only [List.getD_eq_getElem?_getD] at hi ⊢
  rcases lt_trichotomy i w.length with h1 | h1 | h1
  · have h2 : f i < w'.length := by unfold f; split_ifs <;> omega
    rw [List.getElem?_append_left h2, List.getElem?_append_left h1]
    exact hi
  · have h2 : f i = w'.length := by unfold f; split_ifs <;> omega
    rw [h2, h1]
    simp
  · have h2 : w'.length < f i := by unfold f; split_ifs <;> omega
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem fold (gs : List Gate) :
    ∀ w w' : List Bool, 12 ≤ w.length → w'.length = w.length + 2 →
      (∀ i, w'.getD (f i) false = w.getD i false) →
      ∀ i, ((gs.map rg).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (f i) false
        = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i
          false := by
  induction gs with
  | nil => intro w w' _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' hl hl' h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have e : (rg g).op.eval ((rg g).inputs.map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    rw [e]
    apply ih
    · simp; omega
    · simp; omega
    · exact step w w' _ hl hl' h

theorem base (x6 : Fin 26 → Bool) (i : ℕ) :
    (List.ofFn x6).getD (f i) false
      = (List.ofFn fun x8 : Fin 24 => x6 (Fin.ofNat 26 (f x8))).getD i false := by
  by_cases h : i < 24
  · have h2 : f i < 26 := by unfold f; split_ifs <;> omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using h2), List.getElem?_eq_getElem (by simpa using h)]
    simp only [List.getElem_ofFn, Option.getD_some]
    congr 1
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt h2]
  · have h2 : 26 ≤ f i := by unfold f; split_ifs <;> omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simpa using h2), List.getElem?_eq_none (by simp; omega)]

end PEqualNP.Outside.L_meta_7370_aux

open PEqualNP.Outside.L_meta_7370_aux in
theorem PEqualNP.Outside.L_meta_7370 : have x1 : ℕ → ℕ := fun (x1 : ℕ) => if x1 < (9 : ℕ) then x1 else if x1 < (12 : ℕ) then x1 + (1 : ℕ) else x1 + (2 : ℕ); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     x2.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } →       ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x5 ∧           x5.size = x2.size ∧             x5.gates.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧               ∀ (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ),                 have x8 : Fin (24 : ℕ) → Bool := fun (x8 : Fin (24 : ℕ)) => x6 (Fin.ofNat (26 : ℕ) (x1 ↑x8));                 (x5.wires (List.ofFn x6)).getD (x1 x7) Bool.false = (x2.wires (List.ofFn x8)).getD x7 Bool.false := by
  show ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 →
    x2.gates.head? = Option.some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ →
    ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧
      x5.size = x2.size ∧
      x5.gates.head? = Option.some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
      ∀ (x6 : Fin 26 → Bool) (x7 : ℕ),
        (x5.wires (List.ofFn x6)).getD (f x7) false
          = (x2.wires (List.ofFn fun x8 : Fin 24 => x6 (Fin.ofNat 26 (f x8)))).getD x7 false
  intro x2 hm hh
  refine ⟨⟨x2.gates.map rg, x2.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have := hm g0 hg0
    simpa [rg] using this
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · rw [List.head?_map, hh]
    simp [rg, f]
  · intro x6 x7
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    exact fold x2.gates _ _ (by simp) (by simp) (base x6) x7
