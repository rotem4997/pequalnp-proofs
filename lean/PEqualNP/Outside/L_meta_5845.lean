import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5845
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem gate_full (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length)
    (hrb : ∀ i ∈ gates[k].inputs, i < X.length + k) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf gates X).getD i false) := by
  rw [gate_val gates X k hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (wire_take gates X k i (hrb i hi) (le_of_lt hk)).symm

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

end PEqualNP.Outside.L_meta_5845

open PEqualNP.Outside.L_meta_5845 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5845 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Type) (x4 : x3 → Fin x1 → Bool), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 < x10 ∧ x10 < x1 + x6) → ∃ (x7 : ℕ → Set x3), (∀ (x8 : Fin x1), x7 ↑x8 = {x9 : x3 | x4 x9 x8 = Bool.true}) ∧ (∀ x8 < x2.size, ∃ (x10 : ℕ) (x11 : ℕ), x10 < x11 ∧ x11 < x1 + x8 ∧ (x7 (x1 + x8) = x7 x10 ∩ x7 x11 ∨ x7 (x1 + x8) = x7 x10 ∪ x7 x11)) ∧ ∀ (x8 : x3), x8 ∈ x7 x2.output ↔ PEqualNP.MetaComplexity.circuitFun x1 x2 (x4 x8) = Bool.true := by
  intro n C X inp hm hrb
  refine ⟨fun w => {a : X | (wf C.gates (List.ofFn (inp a))).getD w false = true}, ?_, ?_, ?_⟩
  · intro i
    ext a
    simp only [Set.mem_setOf_eq]
    rw [wf_keep C.gates (List.ofFn (inp a)) i (by simp), getD_ofFn]
  · intro j hj
    have hj' : j < C.gates.length := hj
    obtain ⟨p, q, hpq, hlt, hq⟩ := hrb j C.gates[j] (List.getElem?_eq_getElem hj')
    have hop := (hm C.gates[j] (List.getElem_mem hj')).1
    have hval : ∀ a : X, (wf C.gates (List.ofFn (inp a))).getD (n + j) false
        = C.gates[j].op.eval [(wf C.gates (List.ofFn (inp a))).getD p false,
            (wf C.gates (List.ofFn (inp a))).getD q false] := by
      intro a
      have h := gate_full C.gates (List.ofFn (inp a)) j hj' (by
        intro i hi
        rw [hpq] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rw [List.length_ofFn]
        omega)
      rw [List.length_ofFn, hpq] at h
      simpa using h
    refine ⟨p, q, hlt, hq, ?_⟩
    rcases hop with h | h
    · left
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      rw [hval a, h]
      simp [GateOp.eval]
    · right
      have h' : C.gates[j].op = GateOp.or := h
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_union]
      rw [hval a, h']
      simp [GateOp.eval]
  · intro a
    exact Iff.rfl
