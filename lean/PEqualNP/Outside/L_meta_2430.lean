import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2430_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def rho (m N : ℕ) (σ : Fin m → Fin N) (k : ℕ) : ℕ :=
  if h : k < m then (σ ⟨k, h⟩).val else N + (k - m)

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma getD_rho {m N : ℕ} (W y T : List Bool) (σ : Fin m → Fin N) (hW : W.length = N)
    (hy : y.length = m) (hyv : ∀ k (h : k < m), y.getD k false = W.getD (σ ⟨k, h⟩) false)
    (k : ℕ) : (W ++ T).getD (rho m N σ k) false = (y ++ T).getD k false := by
  unfold rho
  split_ifs with h
  · have := (σ ⟨k, h⟩).isLt
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hyv k h]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

lemma fold_rel {m N : ℕ} (W y : List Bool) (σ : Fin m → Fin N) (hW : W.length = N)
    (hy : y.length = m) (hyv : ∀ k (h : k < m), y.getD k false = W.getD (σ ⟨k, h⟩) false)
    (gs : List Gate) : ∀ T : List Bool, ∃ R : List Bool,
      (gs.map (reGate (rho m N σ))).foldl stepW (W ++ T) = W ++ R ∧
      gs.foldl stepW (y ++ T) = y ++ R := by
  induction gs with
  | nil => intro T; exact ⟨T, rfl, rfl⟩
  | cons g gs ih =>
    intro T
    have hm : (g.inputs.map (rho m N σ)).map (fun i => (W ++ T).getD i false)
        = g.inputs.map (fun i => (y ++ T).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => getD_rho W y T σ hW hy hyv i)
    have e1 : stepW (W ++ T) (reGate (rho m N σ) g)
        = W ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (W ++ T) ++ [g.op.eval ((g.inputs.map (rho m N σ)).map fun i => (W ++ T).getD i false)] = _
      rw [hm, List.append_assoc]
    have e2 : stepW (y ++ T) g
        = y ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (y ++ T) ++ _ = _
      rw [List.append_assoc]
    obtain ⟨R, h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)])
    refine ⟨R, ?_, ?_⟩
    · rw [List.map_cons, List.foldl_cons, e1, h1]
    · rw [List.foldl_cons, e2, h2]

end PEqualNP.Outside.L_meta_2430_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2430_aux in
theorem PEqualNP.Outside.L_meta_2430 : ∀ (x1 x2 : ℕ) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x2 → Fin (x1 + x3.size)), x3.output < x1 + x3.size → PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.Monotone2 x4 → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size ≤ x3.size + x4.size + (1 : ℕ) ∧ ∀ (x10 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x9 x10 = (PEqualNP.MetaComplexity.circuitFun x1 x3 x10 || PEqualNP.MetaComplexity.circuitFun x2 x4 fun (x11 : Fin x2) => (x3.wires (List.ofFn x10)).getD (↑(x5 x11)) Bool.false) := by
  intro n m A B σ ho hA hB
  refine ⟨⟨A.gates ++ B.gates.map (reGate (rho m (n + A.size) σ)) ++
    [⟨GateOp.or, [A.output, rho m (n + A.size) σ B.output]⟩], n + A.size + B.size⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨g', hg', rfl⟩) | rfl
    · exact hA g hg
    · have := hB g' hg'
      simpa [reGate] using this
    · simp
  · simp only [Circuit.size, List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  · intro x
    have hW : (A.wires (List.ofFn x)).length = n + A.size := by
      rw [wires_eq, fold_len]; simp [Circuit.size]
    have hy : (List.ofFn fun i : Fin m => (A.wires (List.ofFn x)).getD (σ i).val false).length = m := by
      simp
    have hyv : ∀ k (h : k < m), (List.ofFn fun i : Fin m => (A.wires (List.ofFn x)).getD (σ i).val false).getD k false
        = (A.wires (List.ofFn x)).getD (σ ⟨k, h⟩) false := by
      intro k h
      simp [List.getD_eq_getElem?_getD, h]
    obtain ⟨R, h1, h2⟩ := fold_rel _ _ σ hW hy hyv B.gates []
    simp only [List.append_nil] at h1 h2
    have hR : R.length = B.size := by
      have := fold_len B.gates (List.ofFn fun i : Fin m => (A.wires (List.ofFn x)).getD (σ i).val false)
      rw [h2, List.length_append, hy] at this
      simp [Circuit.size]; omega
    have hB' : PEqualNP.MetaComplexity.circuitFun m B (fun i => (A.wires (List.ofFn x)).getD (σ i).val false)
        = (A.wires (List.ofFn x) ++ R).getD (rho m (n + A.size) σ B.output) false := by
      rw [getD_rho _ _ R σ hW hy hyv, ← h2]
      rfl
    have hA' : PEqualNP.MetaComplexity.circuitFun n A x = (A.wires (List.ofFn x) ++ R).getD A.output false := by
      rw [List.getD_append _ _ _ _ (by omega)]
      rfl
    rw [hA', hB']
    show (List.foldl stepW (List.ofFn x) (A.gates ++ B.gates.map (reGate (rho m (n + A.size) σ)) ++
      [⟨GateOp.or, [A.output, rho m (n + A.size) σ B.output]⟩])).getD (n + A.size + B.size) false = _
    rw [List.foldl_append, List.foldl_append, ← wires_eq, h1]
    simp only [List.foldl_cons, List.foldl_nil, stepW]
    rw [List.getD_append_right _ _ _ _ (by simp [hW, hR])]
    simp [hW, hR, GateOp.eval]
