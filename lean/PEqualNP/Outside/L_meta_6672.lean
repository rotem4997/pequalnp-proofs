import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_6672

def wst (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def ext (n o : ℕ) : List Gate :=
  [{ op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [n, 4] }, { op := GateOp.or, inputs := [o, 8] }, { op := GateOp.or, inputs := [o, n + 1] }, { op := GateOp.and, inputs := [n + 2, n + 3] }]

theorem pref : ∀ (gs : List Gate) (w : List Bool),
    ∃ T : List Bool, List.foldl wst w gs = w ++ T ∧ T.length = gs.length
  | [], w => ⟨[], by simp, rfl⟩
  | g :: rest, w => by
    obtain ⟨T, hT, hl⟩ := pref rest (wst w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: T, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hT]
    simp [wst]

theorem gapp (W l : List Bool) (k : ℕ) :
    (W ++ l).getD k false = if k < W.length then W.getD k false else l.getD (k - W.length) false := by
  by_cases h : k < W.length
  · rw [if_pos h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_of_not_lt h)]

theorem gleft (W l : List Gate) (d : Gate) (k : ℕ) (h : k < W.length) :
    (W ++ l).getD k d = W.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gright (W l : List Gate) (d : Gate) (t : ℕ) :
    (W ++ l).getD (W.length + t) d = l.getD t d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem ext5 (W : List Bool) (n o : ℕ) (hn : n = W.length) (ho : o < n) (h8 : 8 < n) :
    List.foldl wst W (ext n o) = W ++ [W.getD 1 false || W.getD 2 false,
      (W.getD 1 false || W.getD 2 false) || W.getD 4 false,
      W.getD o false || W.getD 8 false,
      W.getD o false || ((W.getD 1 false || W.getD 2 false) || W.getD 4 false),
      (W.getD o false || W.getD 8 false) && (W.getD o false || ((W.getD 1 false || W.getD 2 false) || W.getD 4 false))] := by
  subst hn
  have h4 : 4 < W.length := by omega
  simp only [ext, List.foldl_cons, List.foldl_nil, wst, List.map_cons, List.map_nil, GateOp.eval,
    List.any_cons, List.any_nil, List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true,
    List.append_assoc, List.cons_append, List.nil_append]
  simp only [gapp]
  simp [ho, h4, h8]

theorem main (x1 : Circuit) (hA : PEqualNP.TopForm.IsAO2 14 x1) (hN : ∀ x3 ∈ x1.gates, x3.inputs.Nodup)
    (h14 : 14 ≤ x1.output) (hlt : x1.output < 14 + x1.size) :
    PEqualNP.TopForm.IsAO2 14 { gates := x1.gates ++ ext (14 + x1.size) x1.output, output := 14 + x1.size + 4 } ∧
    (∀ x8 ∈ x1.gates ++ ext (14 + x1.size) x1.output, x8.inputs.Nodup) ∧
    ∀ (x8 : Fin 14 → Bool),
      (List.foldl wst (List.ofFn x8) (x1.gates ++ ext (14 + x1.size) x1.output)).getD (14 + x1.size + 2) false = (x1.eval (List.ofFn x8) || x8 8) ∧
      (List.foldl wst (List.ofFn x8) (x1.gates ++ ext (14 + x1.size) x1.output)).getD (14 + x1.size + 3) false = (x1.eval (List.ofFn x8) || (x8 1 || x8 2 || x8 4)) ∧
      (List.foldl wst (List.ofFn x8) (x1.gates ++ ext (14 + x1.size) x1.output)).getD (14 + x1.size + 4) false = ((x1.eval (List.ofFn x8) || x8 8) && (x1.eval (List.ofFn x8) || (x8 1 || x8 2 || x8 4))) := by
  have hsz : x1.size = x1.gates.length := rfl
  obtain ⟨hAO, hRB, hF⟩ := hA
  have hAO' : ∀ g ∈ x1.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hAO
  have hRB' : ∀ j < x1.gates.length, ∀ i ∈ (x1.gates.getD j ⟨GateOp.or, []⟩).inputs, i < 14 + j := hRB
  have k1 : ∀ g ∈ x1.gates ++ ext (14 + x1.size) x1.output, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hAO' g h
    · simp only [ext, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp
  have k2 : ∀ j < (x1.gates ++ ext (14 + x1.size) x1.output).length, ∀ i ∈ ((x1.gates ++ ext (14 + x1.size) x1.output).getD j ⟨GateOp.or, []⟩).inputs, i < 14 + j := by
    intro j hj i hi
    by_cases hjs : j < x1.gates.length
    · rw [gleft _ _ _ _ hjs] at hi
      exact hRB' j hjs i hi
    · obtain ⟨t, rfl⟩ : ∃ t, j = x1.gates.length + t := ⟨j - x1.gates.length, by omega⟩
      rw [gright] at hi
      have ht : t < 5 := by
        simp only [List.length_append, ext, List.length_cons, List.length_nil] at hj
        omega
      interval_cases t <;> simp [ext] at hi <;> omega
  have k3 : ∀ g ∈ x1.gates ++ ext (14 + x1.size) x1.output, g.inputs.length = 2 := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hF g h
    · simp only [ext, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl
  have k4 : ∀ g ∈ x1.gates ++ ext (14 + x1.size) x1.output, g.inputs.Nodup := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hN g h
    · simp only [ext, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> first | (simp; done) | (simp; omega)
  refine ⟨⟨k1, k2, k3⟩, k4, ?_⟩
  intro x8
  obtain ⟨T, hT, hTl⟩ := pref x1.gates (List.ofFn x8)
  have hev : x1.eval (List.ofFn x8) = (List.foldl wst (List.ofFn x8) x1.gates).getD x1.output false := rfl
  have hWl : (List.foldl wst (List.ofFn x8) x1.gates).length = 14 + x1.size := by
    rw [hT, List.length_append, hTl, hsz]
    simp
  have v1 : (List.foldl wst (List.ofFn x8) x1.gates).getD 1 false = x8 1 := by
    rw [hT]
    simp
  have v2 : (List.foldl wst (List.ofFn x8) x1.gates).getD 2 false = x8 2 := by
    rw [hT]
    simp
  have v4 : (List.foldl wst (List.ofFn x8) x1.gates).getD 4 false = x8 4 := by
    rw [hT]
    simp
  have v8 : (List.foldl wst (List.ofFn x8) x1.gates).getD 8 false = x8 8 := by
    rw [hT]
    simp
  rw [List.foldl_append, ext5 _ _ _ hWl.symm hlt (by omega), hev, v1, v2, v4, v8]
  generalize (List.foldl wst (List.ofFn x8) x1.gates).getD x1.output false = b
  generalize hW : List.foldl wst (List.ofFn x8) x1.gates = W at hWl
  simp [hWl]

end PEqualNP.Outside.L_meta_6672

theorem PEqualNP.Outside.L_meta_6672 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →     (∀ x3 ∈ x1.gates, x3.inputs.Nodup) →       (14 : ℕ) ≤ x1.output →         x1.output < (14 : ℕ) + x1.size →           have x6 : ℕ := (14 : ℕ) + x1.size;           have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(1 : ℕ), (2 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x6, (4 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x1.output, (8 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x1.output, x6 + (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x6 + (2 : ℕ), x6 + (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate }], output := x6 + (4 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };           PEqualNP.TopForm.IsAO2 (14 : ℕ) x7 ∧ (∀ x8 ∈ x7.gates, x8.inputs.Nodup) ∧ ∀ (x8 : Fin (14 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x7 (14 : ℕ) x8 (x6 + (2 : ℕ)) = (x1.eval (List.ofFn x8) || x8 (8 : Fin (14 : ℕ))) ∧ PEqualNP.BlindGate.wireValue x7 (14 : ℕ) x8 (x6 + (3 : ℕ)) = (x1.eval (List.ofFn x8) || (x8 (1 : Fin (14 : ℕ)) || x8 (2 : Fin (14 : ℕ)) || x8 (4 : Fin (14 : ℕ)))) ∧ x7.eval (List.ofFn x8) = ((x1.eval (List.ofFn x8) || x8 (8 : Fin (14 : ℕ))) && (x1.eval (List.ofFn x8) || (x8 (1 : Fin (14 : ℕ)) || x8 (2 : Fin (14 : ℕ)) || x8 (4 : Fin (14 : ℕ))))) := by
  intro x1 hA hN h14 hlt
  exact PEqualNP.Outside.L_meta_6672.main x1 hA hN h14 hlt
