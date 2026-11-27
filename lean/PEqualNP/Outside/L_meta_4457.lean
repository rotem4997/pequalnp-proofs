import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4457

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma step (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) (v : Fin n)
    (h : HasCircuitSize n f s) : HasCircuitSize n (fun x => x v || f x) (s + 1) := by
  obtain ⟨C, hF, hs, he⟩ := h
  refine ⟨⟨C.gates ++ [⟨GateOp.or, [(v : ℕ), C.output]⟩], n + C.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact hF g hg
    · subst hg; simp
  · simp only [Circuit.size, List.length_append, List.length_singleton] at hs ⊢
    omega
  · intro x
    show _ = (x v || f x)
    rw [← he x]
    have hl : (C.gates.foldl stepWire (List.ofFn x)).length = n + C.gates.length := by
      rw [foldl_length]; simp
    have hv : (C.gates.foldl stepWire (List.ofFn x)).getD (v : ℕ) false = x v := by
      rw [foldl_getD_lt _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    simp only [Circuit.eval, wires_eq_foldl, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize C.gates.foldl stepWire (List.ofFn x) = w at hl hv ⊢
    rw [stepWire, List.getD_eq_getElem?_getD, ← hl, List.getElem?_append_right (le_refl _)]
    rw [List.getD_eq_getElem?_getD] at hv
    simp [GateOp.eval, hv]

lemma main (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) (h : HasCircuitSize n f s) :
    ∀ S : Finset (Fin n), HasCircuitSize n
      (fun x => decide (∃ a ∈ S, x a = true) || f x) (s + S.card) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    have e : (fun x : Fin n → Bool => decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) || f x) = f := by
      funext x; simp
    rw [e]; simpa using h
  | insert a S ha ih =>
    have h2 := step n _ _ a ih
    have e : (fun x : Fin n → Bool => x a || (decide (∃ b ∈ S, x b = true) || f x)) =
        (fun x => decide (∃ b ∈ insert a S, x b = true) || f x) := by
      funext x
      cases hxa : x a <;> simp [hxa, Finset.mem_insert]
    rw [e] at h2
    rw [Finset.card_insert_of_notMem ha, ← Nat.add_assoc]
    exact h2

end PEqualNP.Outside.L_meta_4457

theorem PEqualNP.Outside.L_meta_4457 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1)) (x3 : (Fin x1 → Bool) → Bool) (x4 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x4 → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x6 : Fin x1 → Bool) => Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true) || x3 x6) (x4 + x2.card) := by
  intro n S f s h
  exact PEqualNP.Outside.L_meta_4457.main n f s h S
