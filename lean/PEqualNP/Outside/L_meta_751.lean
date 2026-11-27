import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_751_aux

open PEqualNP.CircuitLowerBounds

theorem hget (W : List Bool) (v : Bool) (i : ℕ) (hi : i < W.length) :
    (W ++ [v]).getD i false = W.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem hout (W : List Bool) (i : ℕ) (hi : W.length ≤ i) :
    W.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem struct (G : List Gate) (x : List Bool) :
    (G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
        = x.length + G.length ∧
    (∀ i, i < x.length →
      (G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false
        = x.getD i false) ∧
    (∀ k g, G[k]? = some g →
      (G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD
          (x.length + k) false
        = g.op.eval (g.inputs.map fun i => if i < x.length + k then
            (G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD
              i false else false)) := by
  induction G using List.reverseRecOn with
  | nil => simp
  | append_singleton G g ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
      = W at h1 h2 h3
    refine ⟨by simp [h1]; omega, ?_, ?_⟩
    · intro i hi
      rw [hget _ _ _ (by omega)]
      exact h2 i hi
    · intro k e hk
      by_cases hlt : k < G.length
      · have hk2 : G[k]? = some e := by rwa [List.getElem?_append_left hlt] at hk
        rw [hget _ _ _ (by omega), h3 k e hk2]
        congr 1
        apply List.map_congr_left
        intro i _
        split_ifs with hi
        · rw [hget _ _ _ (by omega)]
        · rfl
      · obtain ⟨hl, hv⟩ := List.getElem?_eq_some_iff.1 hk
        simp only [List.length_append, List.length_singleton] at hl
        have hkeq : k = G.length := by omega
        subst hkeq
        simp at hv
        subst hv
        rw [← h1]
        have h4 : (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).getD W.length false
            = g.op.eval (g.inputs.map fun i => W.getD i false) := by
          simp [List.getD_eq_getElem?_getD]
        rw [h4]
        congr 1
        apply List.map_congr_left
        intro i _
        split_ifs with hi
        · rw [hget _ _ _ hi]
        · rw [hout _ _ (by omega)]

theorem structC (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length ∧
    (∀ i, i < x.length → (C.wires x).getD i false = x.getD i false) ∧
    (∀ k g, C.gates[k]? = some g →
      (C.wires x).getD (x.length + k) false
        = g.op.eval (g.inputs.map fun i => if i < x.length + k then
            (C.wires x).getD i false else false)) :=
  struct C.gates x

end PEqualNP.Outside.L_meta_751_aux

open PEqualNP.Outside.L_meta_751_aux in
theorem PEqualNP.Outside.L_meta_751 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (i : ℕ), (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → Relation.ReflTransGen (fun a b : ℕ => ∃ (k : ℕ) (e : PEqualNP.CircuitLowerBounds.Gate), a = n + k ∧ C.gates[k]? = some e ∧ b ∈ e.inputs ∧ b < a) i (n + j) → g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ x x' : Fin n → Bool, (∀ q : Fin n, x q = true → x' q = true) → (PEqualNP.CircuitLowerBounds.Circuit.wires C (List.ofFn x)).getD i false = true → (PEqualNP.CircuitLowerBounds.Circuit.wires C (List.ofFn x')).getD i false = true := by
  intro n C i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hc x x' hx hi
    obtain ⟨h1, h2, h3⟩ := structC C (List.ofFn x)
    obtain ⟨h1', h2', h3'⟩ := structC C (List.ofFn x')
    simp only [List.length_ofFn] at h1 h2 h3 h1' h2' h3'
    by_cases hin : i < n
    · rw [h2' i hin]
      rw [h2 i hin] at hi
      simp [List.getD_eq_getElem?_getD, hin] at hi ⊢
      exact hx ⟨i, hin⟩ hi
    · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
      by_cases hk : k < C.gates.length
      · have hg : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk
        generalize C.gates[k] = g at hg
        rw [h3 k _ hg] at hi
        rw [h3' k _ hg]
        have hop := hc k _ hg Relation.ReflTransGen.refl
        have key : ∀ b ∈ g.inputs,
            (if b < n + k then (C.wires (List.ofFn x)).getD b false else false) = true →
            (if b < n + k then (C.wires (List.ofFn x')).getD b false else false) = true := by
          intro b hb hv
          by_cases hbk : b < n + k
          · simp only [hbk, ite_true] at hv ⊢
            exact ih b hbk (fun j e he hr => hc j e he
              (Relation.ReflTransGen.head ⟨k, g, rfl, hg, hb, hbk⟩ hr)) x x' hx hv
          · simp [hbk] at hv
        rcases hop with ho | ho
        · rw [ho] at hi ⊢
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_eq_true, List.mem_map] at hi ⊢
          rintro _ ⟨b, hb, rfl⟩
          exact key b hb (hi _ ⟨b, hb, rfl⟩)
        · rw [ho] at hi ⊢
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_eq_true, List.mem_map] at hi ⊢
          obtain ⟨_, ⟨b, hb, rfl⟩, hv⟩ := hi
          exact ⟨_, ⟨b, hb, rfl⟩, key b hb hv⟩
      · rw [hout _ _ (by omega)] at hi
        cases hi
